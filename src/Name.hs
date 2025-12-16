{-# LANGUAGE UnicodeSyntax #-}

module Name (module Name) where

data Name = Name { nameString :: String, nameIndex :: Int }
  deriving (Eq, Ord)

instance Show Name where
  show name = if nameIndex name < 0 || nameString name == "_"
              then nameString name
              else nameString name ++ show (nameIndex name)

freshOf :: String → [Name] → Name
freshOf name existing = Name name (if indices == [] then -1 else 1 + maximum indices)
  where
    indices = map nameIndex $ filter (\ nm → nameString nm == name) existing

fresh :: Name → [Name] → Name
fresh = freshOf . nameString

named :: String → Name
named s = Name s (-1)
