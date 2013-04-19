--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Control.Applicative ((<$>))
import           Data.Monoid         (mappend)
import           Data.List           (stripPrefix)
import           Control.Monad
import           Hakyll
import           System.Process
import           System.FilePath     (takeBaseName, (</>))

compass :: Compiler (Item String)
compass =
  getResourceString >>=
  withItemBody (unixFilter "sass" ["-s", "--scss", "--compass"])

coqdoc :: Compiler (Item String)
coqdoc = do
  coqFileName <- toFilePath <$> getUnderlying
  unsafeCompiler $
    readProcess "coqc" [ coqFileName ] ""
  body <- unsafeCompiler $
          readProcess "coqdoc" [ "--no-index"
                               , "--stdout"
                               , "--body-only"
                               , "--parse-comments"
                               , "-s"
                               , coqFileName ] ""
  makeItem body

coqPath = ("theories" </>)

getCoqFileName :: Item a -> Compiler (Maybe FilePath)
getCoqFileName item = do
  let ident = itemIdentifier item
  fmap coqPath <$> getMetadataField ident "coqfile"

gitHubBlobPath = "https://github.com/arthuraa/poleiro/blob/master"

gitHubField :: Context a
gitHubField = field "github" $ \item -> do
  coqFileName <- getCoqFileName item
  case coqFileName of
    Just coqFileName -> do
      let url = gitHubBlobPath ++ "/" ++ coqFileName
      linkTemplate <- loadBody "templates/github-link.html"
      applyTemplateWith (\_ _ -> return url) linkTemplate ()
    Nothing -> return ""

coqPost :: Compiler (Item String)
coqPost = do
  ident <- getUnderlying
  route <- getRoute ident
  coqFileName <- getMetadataField ident "coqfile"
  case coqFileName of
    Just coqFileName ->
      let fullName = coqPath coqFileName
          basename = takeBaseName coqFileName in do
        postBody <- loadBody $ fromFilePath fullName
        makeItem $ flip withUrls postBody $ \url ->
          -- coqdoc apparently doesn't allow us to change the links of the
          -- generated HTML that point to itself. Therefore, we must do it
          -- by hand.
          case (stripPrefix (basename ++ ".html") url, route) of
            (Just url', Just route) -> "/" ++ route ++ url'
            _ -> url

    Nothing -> error "Couldn't find \"coqfile\" metadata field"

postProcessPost :: Item String -> Compiler (Item String)
postProcessPost =
  saveSnapshot "content" >=>
  loadAndApplyTemplate "templates/post.html" postCtx  >=>
  loadAndApplyTemplate "templates/main.html" defaultContext >=>
  relativizeUrls

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "css/*.scss" $ do
        route $ setExtension "css"
        compile $ compass

    match "images/*" $ do
        route idRoute
        compile copyFileCompiler

    match "theories/*.v" $ do
        compile coqdoc

    match "posts/*.coqpost" $ do
        route $ setExtension "html"
        compile $ coqPost >>= postProcessPost

    match "posts/*.md" $ do
        route $ setExtension "html"
        compile $ pandocCompiler >>= postProcessPost

    create ["archives.html"] $ do
      route idRoute
      compile $ do
        let archiveCtx =
              field "posts" (const archives) `mappend`
              constField "title" "Archives"  `mappend`
              defaultContext

        makeItem ""
          >>= loadAndApplyTemplate "templates/archives.html" archiveCtx
          >>= loadAndApplyTemplate "templates/main.html" archiveCtx
          >>= relativizeUrls

    create ["atom.xml"] $ do
      route idRoute
      compile $ do
          let feedCtx = postCtx `mappend` bodyField "description"
          posts <- fmap (take 10) . recentFirst =<<
              loadAllSnapshots "posts/*" "content"
          renderAtom feedConfiguration feedCtx posts

    match "index.html" $ do
        route idRoute
        compile $ do
            let indexCtx = field "posts" $ const $ recentPostList 3
                ctx = constField "title" "Main" `mappend` postCtx

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/main.html" ctx
                >>= relativizeUrls

    match "about.md" $ do
        route $ setExtension "html"
        compile $ do
          let aboutCtx = constField "title" "About" `mappend` defaultContext
          pandocCompiler
            >>= loadAndApplyTemplate "templates/main.html" aboutCtx
            >>= relativizeUrls

    match "templates/*" $ compile templateCompiler


--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    gitHubField `mappend`
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext

--------------------------------------------------------------------------------
archives :: Compiler String
archives = do
    posts   <- loadAllSnapshots "posts/*" "content" >>= recentFirst
    itemTpl <- loadBody "templates/post-item.html"
    applyTemplateList itemTpl postCtx posts

recentPostList :: Int -> Compiler String
recentPostList n = do
    posts   <- loadAllSnapshots "posts/*" "content" >>= recentFirst
    itemTpl <- loadBody "templates/post-index.html"
    applyTemplateList itemTpl postCtx $ take n posts

feedConfiguration :: FeedConfiguration
feedConfiguration = FeedConfiguration
    { feedTitle       = "Poleiro: latest posts"
    , feedDescription = "A blog about the Coq proof assistant"
    , feedAuthorName  = "Arthur Azevedo de Amorim"
    , feedAuthorEmail = ""
    , feedRoot        = "http://poleiro.info"
    }
