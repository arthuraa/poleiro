--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Control.Applicative ((<$>))
import           Data.Monoid         (mappend, mconcat)
import qualified Data.Map            as M
import           Data.Time.Format    (parseTime)
import           Data.List           (stripPrefix)
import           Data.Char           (toLower, isAlphaNum)
import           Hakyll
import           System.Process
import           System.FilePath     (takeBaseName)
import           Text.Regex

makeSlug :: String -> String
makeSlug = filter (\c -> isAlphaNum c || c == '-') . map subst
  where subst '_' = '-'
        subst ' ' = '-'
        subst c = toLower c

coqPostName :: Metadata -> String
coqPostName meta =
  M.findWithDefault "" "date" meta ++ "-"
  ++ (makeSlug $ M.findWithDefault "" "title" meta)
  ++ ".html"

compass :: Compiler (Item String)
compass =
  getResourceString >>=
  withItemBody (unixFilter "sass" ["-s", "--scss", "--compass"])

coqdoc :: Compiler (Item String)
coqdoc = do
  inputFileName <- toFilePath <$> getUnderlying
  unsafeCompiler $
    readProcess "coqc" [ inputFileName ] ""
  body <- unsafeCompiler $
          readProcess "coqdoc" [ "--no-index"
                               , "--stdout"
                               , "--body-only"
                               , "--parse-comments"
                               , "-s"
                               , inputFileName ] ""
  let basename = takeBaseName inputFileName
  makeItem $ flip withUrls body $ \url ->
    -- Disable internal links for now. Still needs to find a way of
    -- inserting the new filename here...
    if isExternal url then url else ""

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "css/*.scss" $ do
        route $ setExtension "css"
        compile $ compass

    match "images/*" $ do
        route idRoute
        compile copyFileCompiler

    match "posts/*.v" $ do
        route $ metadataRoute $ constRoute . coqPostName
        compile $ coqdoc >>=
          saveSnapshot "content" >>=
          loadAndApplyTemplate "templates/post.html" postCtx >>=
          loadAndApplyTemplate "templates/main.html" defaultContext

    match "posts/*.md" $ do
        route $ setExtension "html"
        compile $ pandocCompiler >>=
          saveSnapshot "content" >>=
          loadAndApplyTemplate "templates/post.html" postCtx >>=
          loadAndApplyTemplate "templates/main.html" defaultContext

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

    match "templates/*" $ compile templateCompiler


--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext

--------------------------------------------------------------------------------
recentPostList :: Int -> Compiler String
recentPostList n = do
    posts   <- loadAllSnapshots "posts/*" "content" >>= recentFirst
    itemTpl <- loadBody "templates/post-item.html"
    list    <- applyTemplateList itemTpl postCtx $ take n posts
    return list
