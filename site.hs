--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Control.Applicative ((<$>))
import           Data.Monoid         (mappend)
import qualified Data.Map            as M
import           Hakyll
import           System.Process
import           Text.Parsec
import           Text.Parsec.String

data Post = Post { postTitle :: String
                 , postDate :: String
                 , postBody :: Item String }

-- Looks for comments that are hidden in the beginning of Coq source
-- code and tries to find metadata there
getCoqMetadata :: String -> M.Map String String
getCoqMetadata contents =
  let binding = do
        string "(*"
        spaces
        key <- many1 letter
        char ':'
        spaces
        value <- manyTill anyChar (try $ spaces >> string "*)")
        spaces
        return (key, value)

      metadata = do
        string "(* begin hide *)"
        spaces
        bindings <- manyTill binding (try $ string "(* end hide *)")
        return $ foldl (\m (k,v) -> M.insert k v m) M.empty bindings in
  case parse metadata "" contents of
    Right metadata -> metadata
    Left _ -> M.empty

coqdoc :: Compiler Post
coqdoc = do
  inputFileName <- toFilePath <$> getUnderlying
  fileContents <- itemBody <$> getResourceBody
  let metadata = getCoqMetadata fileContents
      title = M.findWithDefault inputFileName "title" metadata
      date = M.findWithDefault "No date" "date" metadata
  unsafeCompiler $
    readProcess "coqc" [ inputFileName ] ""
  body <- unsafeCompiler $
          readProcess "coqdoc" [ "--no-index"
                               , "--stdout"
                               , "--body-only"
                               , "--parse-comments"
                               , "-s"
                               , inputFileName ] ""

  Post title date <$> makeItem body

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "posts/*.v" $ do
        route $ setExtension "html"
        compile $ do
          Post _ _ body <- coqdoc
          loadAndApplyTemplate "templates/post.html" defaultContext body

    match "index.html" $ do
        route idRoute
        compile $ do
            let indexCtx = field "posts" $ \_ -> postList (take 3 . recentFirst)

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/post.html" postCtx
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
