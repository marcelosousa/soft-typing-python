{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
-------------------------------------------------------------------------------
-- Module    :  Analysis.Lattice
-- Copyright :  (c) 2011 Marcelo Sousa, Alessandro Vermeulen, Thijs Alkemade  
-- Creates a class for Lattice and an instance of our Lattice which is P (Var x P(Types)) 

module Analysis.Lattice where

import Data.Set  (fold, member, union)
import Data.List (all, elem, nub)
import Data.Map  (Map, empty, toList, mapWithKey, lookup, unionWith)

import IPython.Typing (Environment, Context)

class (Ord state, Eq state) => Lattice state where
	bottom :: state
	(⊑) :: state -> state -> Bool
	(⊔) :: state -> state -> state

instance (Eq a, Ord a) => Lattice [a] where
	bottom = []
	a ⊑ b = all (`elem` b) a
	a ⊔ b = nub (a ++ b)
    
instance Lattice Environment where
	bottom = empty
	a ⊑ b  = if a == empty && b == empty 
		      then False
		      else all snd $ toList $ mapWithKey f a
				       where f k s = case Data.Map.lookup k b of
		     			             		  Just types -> fold (\x bool -> bool && (x `member` s)) True types
		     			             		  Nothing    -> False
	a ⊔ b  = unionWith union a b