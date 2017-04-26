{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-|
Module: Reflex.Dynamic.CollectDynGeneric
Description: Generic (generics-sop) implementation of CollectDynPure and distributeFHListOverDynPure
-}
module Reflex.Dynamic.CollectDynGeneric
  (
    distributeNPOverDyn
  , collectDynGeneric
  , collectDynNP
  ) where

import Generics.SOP ((:.:) (Comp), Code, Generic, I (I), NP, NS, Proxy (..), SListI, SListI2, SOP (..), from,
                     hcliftA, hliftA, hsequence', to, unComp, unI, unSOP)

import Generics.SOP.DMapUtilities (FunctorWrapTypeList, FunctorWrapTypeListOfLists, npReCompose,
                                   npSequenceViaDMap, nsOfnpReCompose)

import Reflex.Class (Reflex)
import Reflex.Dynamic (Dynamic, distributeDMapOverDynPure)


-- | Take a type-list indexed product of dynamics and produce a dynamic of a type-list-indexed product of values (wrapped by an Identity functor, 'I').
collectDynNP::(Reflex t, SListI xs)=>NP (Dynamic t) xs -> Dynamic t (NP I xs)
collectDynNP = npSequenceViaDMap distributeDMapOverDynPure . hliftA (Comp . fmap I)

-- | Given a pair of types a and b where a is like b except each field of each constructor is dynamic
-- (e.g., ('Dynamic' t x, 'Dynamic' t y) and (x,y) or Either ('Dynamic' t x) ('Dynamic' t y) and Either x y)
-- convert the former into a Dynamic of the latter.
collectDynGeneric::(Reflex t,Generic a, Generic b, (Code a) ~ FunctorWrapTypeListOfLists (Dynamic t) (Code b))=>a -> Dynamic t b
collectDynGeneric = fmap (to . SOP) . hsequence' . collectDynNSNP . aToNSNPI

-- | A variation on 'collectDynPureNP' which more closely mirrors the structure of (deprecated) 'Reflex.Dynamic.distributeFHlistOverDynPure'
distributeNPOverDyn::(Reflex t, SListI xs)=>NP I (FunctorWrapTypeList (Dynamic t) xs) -> Dynamic t (NP I xs)
distributeNPOverDyn = collectDynNP . hliftA (unI . unComp) . npReCompose


aToNSNPI::(Generic a, Code a ~ FunctorWrapTypeListOfLists (Dynamic t) xss, SListI2 xss) =>a -> NS (NP (I :.: Dynamic t)) xss
aToNSNPI = nsOfnpReCompose . unSOP . from

collectDynNSNP::(Reflex t,SListI2 xss)=>NS (NP (I :.: Dynamic t)) xss -> NS (Dynamic t :.: NP I) xss
collectDynNSNP =
  let slistIC = Proxy :: Proxy SListI
  in hcliftA slistIC (Comp . collectDynNP . hliftA (unI . unComp))





