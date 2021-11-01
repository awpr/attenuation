-- Copyright 2021 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--      http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Control.Lens.Attenuation where

import Prelude hiding (id, (.))

import Control.Category (Category(..))
import Data.Coerce (Coercible)
import Data.Semigroup (All(..))
import GHC.Exts (proxy#)
import GHC.TypeNats (Nat, KnownNat, type (<=), natVal')

import Data.Type.Attenuation
import Data.Type.Coercion (Coercion(..))
import Data.Profunctor

import Data.Fin.Int (Fin, finToInt, unsafeCoFin)

class AttProfunctor p where
  {-# MINIMAL dicoerce | lcoerce, rcoerce #-}

  dicoerce :: Attenuation c a -> Attenuation b d -> p a b -> p c d
  dicoerce ca bd = lcoerce ca . rcoerce bd

  lcoerce :: Attenuation c a -> p a b -> p c b
  lcoerce = (`dicoerce` id)

  rcoerce :: Attenuation b d -> p a b -> p a d
  rcoerce = dicoerce id

defaultDicoerce
  :: Profunctor p
  => Attenuation c a -> Attenuation b d -> p a b -> p c d
defaultDicoerce ca bd = dimap (attenuateWith ca) (attenuateWith bd)

-- An Attenuation subject to a validity condition.
--
-- The nice thing about this form is that it can continue to be a coercion
-- under the hood even when composed, unlike @a -> Maybe b@.
data Restriction a b
  = Restriction
      { rstValidate :: a -> All
      , rstCoercion :: Attenuation a b
      }

restrictWith :: Restriction a b -> a -> Maybe b
restrictWith (Restriction valid att) a
  | getAll (valid a)   = Just $ attenuateWith att a
  | otherwise          = Nothing

instance Category Restriction where
  id = Restriction mempty attenuation
  Restriction f bc . Restriction g ab =
    -- Take care: validate @g@ before using its Coercion.
    Restriction (g <> withAttenuation ab (attenuate f)) (bc . ab)

class AttProfunctor p => ProfunctorRestrict p where
  restrict :: Restriction c a -> Attenuation b d -> p a b -> p c d

instance AttProfunctor Restriction where
  dicoerce ca bd ab = Restriction mempty bd . ab . Restriction mempty ca

instance ProfunctorRestrict Restriction where
  restrict ca bd ab = Restriction mempty bd . ab . ca

type Optic p s t a b = p a b -> p s t
type Optic' p s a = Optic p s s a a

type RepEquality s t a b = forall p. AttProfunctor p => Optic p s t a b

repEq :: (Attenuable s a, Attenuable b t) => RepEquality s t a b
repEq = dicoerce attenuation attenuation

fromAttenuations :: Attenuation s a -> Attenuation b t -> RepEquality s t a b
fromAttenuations = dicoerce

fromCoercions :: Coercion s a -> Coercion b t -> RepEquality s t a b
fromCoercions sa bt = dicoerce (coer sa) (coer bt)

fromCoercible :: (Coercible s a, Coercible b t) => RepEquality s t a b
fromCoercible = dicoerce coercible coercible

instance AttProfunctor Attenuation where
  dicoerce ca bd ab = bd . ab . ca

newtype ForwardAtt r a b = ForwardAtt { getForwardAtt :: Attenuation a r }

instance AttProfunctor (ForwardAtt r) where
  dicoerce ca _ (ForwardAtt ar) = ForwardAtt (ar . ca)

forwardAtt :: Optic' (ForwardAtt a) s a -> Attenuation s a
forwardAtt l = getForwardAtt $ l (ForwardAtt attenuation)

newtype ReverseAtt r a b = ReverseAtt { getReverseAtt :: Attenuation r b }

instance AttProfunctor (ReverseAtt r) where
  dicoerce _ bd (ReverseAtt rb) = ReverseAtt (bd . rb)

instance ProfunctorRestrict (ReverseAtt r) where
  restrict _ bd (ReverseAtt rb) = ReverseAtt (bd . rb)

reverseAtt :: Optic' (ReverseAtt a) s a -> Attenuation a s
reverseAtt l = getReverseAtt $ l (ReverseAtt attenuation)




type RepSubtype s t a b = forall p. ProfunctorRestrict p => Optic p s t a b

repSub :: Attenuable b t => Restriction s a -> RepSubtype s t a b
repSub sa = restrict sa attenuation

newtype ForwardRestrict r a b
  = ForwardRestrict { getForwardRestrict :: Restriction a r }

instance AttProfunctor (ForwardRestrict r) where
  dicoerce ca _ (ForwardRestrict ar) = ForwardRestrict (ar . Restriction mempty ca)

instance ProfunctorRestrict (ForwardRestrict r) where
  restrict ca _ (ForwardRestrict ar) = ForwardRestrict (ar . ca)

forwardRst :: Optic' (ForwardRestrict a) s a -> Restriction s a
forwardRst l = getForwardRestrict $ l (ForwardRestrict id)

-- ## Examples ## --

newtype MyFin (n :: Nat) = MyFin (Fin n)
type role MyFin nominal

myFin :: RepEquality (MyFin m) (MyFin n) (Fin m) (Fin n)
myFin = repEq

finRestrict :: forall m n. KnownNat n => Restriction (Fin m) (Fin n)
finRestrict = Restriction
  (\x -> All $ finToInt x < fromIntegral (natVal' @n proxy#))
  (coer unsafeCoFin)

finLT :: (KnownNat n, p <= o) => RepSubtype (Fin m) (Fin o) (Fin n) (Fin p)
finLT = repSub finRestrict
