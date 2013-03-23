--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Control.Applicative ((<$>))
import           Data.Monoid         (mappend, mconcat)
import qualified Data.Map            as M
import           Data.Time.Format    (parseTime)
import           Hakyll
import           System.Process

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

  makeItem body

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "posts/*.v" $ do
        route $ setExtension "html"
        compile $ coqdoc >>=
          loadAndApplyTemplate "templates/post.html" postCtx >>=
          loadAndApplyTemplate "templates/main.html" defaultContext

    match "index.html" $ do
        route idRoute
        compile $ do
            let indexCtx = field "posts" $ \_ -> postList (take 3 . recentFirst)

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/main.html" postCtx
                >>= relativizeUrls

    match "templates/*" $ compile templateCompiler


--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext


--------------------------------------------------------------------------------
postList :: ([Item String] -> [Item String]) -> Compiler String
postList sortFilter = do
    posts   <- sortFilter <$> loadAll "posts/*"
    itemTpl <- loadBody "templates/post-item.html"
    list    <- applyTemplateList itemTpl postCtx posts
    return list
