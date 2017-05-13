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

{-# LANGUAGE DeriveGeneric #-}

{-|
Module: Reflex.FanGeneric
Description: Generic (generics-sop) implementation of fan and select
-}
module Reflex.FanGeneric
  (
  ) where

import Generics.SOP ((:.:) (Comp), Code, Generic, I (I), NP (..), NS (Z), Proxy (..), SListI, SListI2,
                     SOP (..), from, hcliftA, hliftA, hsequence', to, unComp, unI, unSOP)

import Generics.SOP.DMapUtilities (FunctorWrapTypeList, FunctorWrapTypeListOfLists, TypeListTag (..),
                                   makeTypeListTagNP, npReCompose, npSequenceViaDMap, npUnCompose,
                                   nsOfnpReCompose)

import Generics.SOP.Distribute (functorToNP)

import Reflex.Class (Event, EventSelector (..), Reflex, constDyn, fan, fmapMaybe, updated)
import Reflex.Dynamic (Dynamic, distributeDMapOverDynPure)

import qualified GHC.Generics as GHCG

newtype EventSelectorGeneric t xss  = EventSelectorGeneric
  {
    selectGeneric :: forall a tla. (Reflex t, SListI2 xss, SListI tla, Generic a, (Code a) ~ Constructs tla) => TypeListTag xss tla -> Event t a
  }

data UnaryHelper a = UnaryHelper { getUnary :: a } deriving (GHCG.Generic)
instance Generic a => Generic (UnaryHelper a)

selectGenericUnary::(Reflex t, SListI2 xss, SListI tla, Generic a, (Code (UnaryHelper a)) ~ Constructs tla)
  => EventSelectorGeneric t xss -> TypeListTag xss tla -> Event t a
selectGenericUnary esg  = fmap getUnary . selectGeneric esg

-- | make the product of all tags for b and then put them into a type, a, isomorphic to that product. Probably a tuple.
makeTags :: forall a b. (Generic b, Generic a, (Code a) ~ Constructs (FunctorWrapTypeList (TypeListTag (Code b)) (Code b))) => Proxy b -> a
makeTags _ =
  let tags :: NP (TypeListTag (Code b)) (Code b)
      tags = makeTypeListTagNP
  in to . SOP . Z $ npUnCompose $ hliftA (Comp . I) tags

fanGeneric :: forall t a. (Reflex t, Generic a) => Event t a -> EventSelectorGeneric t (Code a)
fanGeneric ev =
  let sListIC = Proxy :: Proxy SListI
      npOfEvents :: NP (Event t :.: NP I) (Code a)
      npOfEvents = hcliftA sListIC (Comp . fmapMaybe id . fmap unComp . unComp) $ functorToNP ev
  in EventSelectorGeneric $ \tag -> selectTypedFromNP npOfEvents tag

selectTypedFromNP :: (Functor g, Generic a, (Code a) ~ Constructs xs, SListI xs, SListI2 xss) => NP (g :.: NP I) xss -> TypeListTag xss xs -> g a
selectTypedFromNP np tag = to . SOP . Z <$> selectFromNP np tag

selectFromNP :: forall g xss xs. (Functor g, SListI2 xss, SListI xs) => NP (g :.: NP I) xss -> TypeListTag xss xs -> g (NP I xs)
selectFromNP np tag = go np tag
  where
    go :: NP (g :.: NP I) yss -> TypeListTag yss ys -> g (NP I ys)
    go Nil _ = error "Reached the end of typelist before the tag was satified."
    go (gy :* _) TLHead = unComp gy
    go (_ :* npTail) (TLTail tailTag) = go npTail tailTag

type family Constructs (xs :: [*]) ::  [[*]] where
  Constructs x = x ': '[]

-- for example
data FanExample = FEA | FEB | FEC C | FED Int Double deriving (GHCG.Generic)
instance Generic FanExample

data C = C1 Int Int | C2 Double Double deriving (GHCG.Generic)
instance Generic C


exampleFan :: Reflex t => EventSelectorGeneric t (Code FanExample)
exampleFan = fanGeneric (updated $ constDyn $ FEA)

(tagA, tagB, tagC, tagD) = makeTags (Proxy :: Proxy FanExample)

evNullaryA :: Reflex t => Event t ()
evNullaryA = selectGeneric exampleFan tagA

evNullaryB :: Reflex t => Event t ()
evNullaryB = selectGeneric exampleFan tagB

evC :: Reflex t => Event t C
evC = selectGenericUnary exampleFan tagC

evD :: Reflex t => Event t (Int, Double)
evD = selectGeneric exampleFan tagD

-- or

data DLike = DLike Int Double deriving (GHCG.Generic)
instance Generic DLike

evDLike :: Reflex t => Event t DLike
evDLike = selectGeneric exampleFan tagD






