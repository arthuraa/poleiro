--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Control.Applicative ((<$>))
import           Data.Monoid         (mappend, mconcat)
import qualified Data.Map            as M
import           Data.Time.Format    (parseTime)
import           Data.List           (stripPrefix)
import           Data.Char           (toLower, isAlphaNum)
import           Control.Monad
import           Hakyll
import           System.Process
import           System.FilePath     (takeBaseName, (</>), takeDirectory)
import           Text.Regex

compass :: Compiler (Item String)
compass =
  getResourceString >>=
  withItemBody (unixFilter "sass" ["-s", "--scss", "--compass"])

coqdoc :: String -> Compiler (Item String)
coqdoc coqFileName = do
  route <- getUnderlying >>= getRoute
  path <- takeDirectory <$> toFilePath <$> getUnderlying
  let coqFileName' = path </> coqFileName
  unsafeCompiler $
    readProcess "coqc" [ coqFileName' ] ""
  body <- unsafeCompiler $
          readProcess "coqdoc" [ "--no-index"
                               , "--stdout"
                               , "--body-only"
                               , "--parse-comments"
                               , "-s"
                               , coqFileName' ] ""
  let basename = takeBaseName coqFileName
  makeItem $ flip withUrls body $ \url ->
    -- coqdoc apparently doesn't allow us to change the links of the
    -- generated HTML that point to itself. Therefore, we must do it
    -- by hand.
    case (stripPrefix (basename ++ ".html") url, route) of
      (Just url', Just route) -> "/" ++ route ++ url'
      _ -> url

coqPost :: Compiler (Item String)
coqPost = (trim <$> itemBody <$> getResourceBody) >>= coqdoc

postProcessPost :: Item String -> Compiler (Item String)
postProcessPost =
  saveSnapshot "content" >=>
  loadAndApplyTemplate "templates/post.html" postCtx >=>
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

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/main.html" postCtx
                >>= relativizeUrls

    match "about.md" $ do
        route $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/main.html" defaultContext
            >>= relativizeUrls

    match "templates/*" $ compile templateCompiler


--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
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
    , feedDescription = ""
    , feedAuthorName  = "Arthur Azevedo de Amorim"
    , feedAuthorEmail = ""
    , feedRoot        = "http://www.cis.upenn.edu/~aarthur/poleiro"
    }