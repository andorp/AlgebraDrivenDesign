module Scavanger2 where

{-
This module is a sketch for the Algebra Driven Design book by Sandy Maguire.
I am experimenting, how algebraic laws of a given domain could be encoded in dependently typed programming
languages.

Currently there is no intent to make this piece of software to a working prototype.
-}

open import Level

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.List
open import Data.Bool
open import Data.Product
open import Data.Maybe

const : {a : Level} {A B : Set a} → A → B → A
const a _ = a

flip : {a : Level} {A B C : Set a} → (A → B → C) → (B → A → C)
flip f b a = f a b 

record Functor {a} (F : Set a → Set a) : Set (suc a) where
  field
    fmap : {A B : Set a} → (A → B) → F A → F B

open Functor {{...}} public

_<$>_ : ∀ {a}
          {A B : Set a}
          {F : Set a → Set a}
          {{_ : Functor F}}
      → (A → B) → F A → F B
f <$> x = fmap f x

infixl 30 _<$>_

record Applicative {a} (F : Set a → Set a) : Set (suc a) where
  field
    pure  : {A : Set a} → A → F A
    app   : {A B : Set a} → F (A → B) → F A → F B

open Applicative {{...}} public

_<*>_ : ∀ {a}
          {A B : Set a}
          {F : Set a → Set a}
          {{_ : Functor F}}
          {{_ : Applicative F}}
      → F (A → B) → F A → F B
f <*> x = app f x

infixl 30 _<*>_

liftA2 : ∀ {a}
           {A B C : Set a}
           {F : Set a → Set a}
           {{_ : Functor F}}
           {{_ : Applicative F}}
       → (A → B → C) → F A → F B → F C
liftA2 f fa fb = fmap f fa <*> fb

_<$_ : ∀ {a}
         {A B : Set a}
         {F : Set a → Set a}
         {{_ : Functor F}}
     → A → F B → F A
a <$ fb = fmap (const a) fb

_*>_ : ∀ {a}
         {A B : Set a}
         {F : Set a → Set a}
         {{_ : Functor F}}
         {{_ : Applicative F}}
     → F A → F B → F A
fa *> fb = liftA2 const fa fb

infixl 30 _*>_

record Monad {a} (F : Set a → Set a) : Set (suc a) where
  field
    join : {A : Set a} → F (F A) → F A

open Monad {{...}} public

_>>=_ : ∀ {a}
          {A B : Set a}
          {F : Set a → Set a}
          {{_ : Functor F}}
          {{_ : Monad F}}
      → F A → (A → F B) → F B
m >>= k = join (fmap k m)

record Foldable {a} (F : Set a → Set a) : Set (suc a) where
  field
    foldL : {A B : Set a} → (B → A → B) → B → F A → B

foldM : {a : Level}
        {A B : Set a}
        {T : Set a → Set a}
        {M : Set a → Set a}
        {{_ : Functor M}}
        {{_ : Applicative M}}
        {{_ : Monad M}}
        {{_ : Foldable T}}
      → (B → A → M B) → B → T A → M B
foldM f i t = {!!}

open Foldable {{...}} public

record Monoid {a} (M : Set a) : Set a where
  field
    mempty : M
    _<>_   : M → M → M

open Monoid {{...}} public

instance
  PairFunctor : {M : Set} → Functor {a = Level.zero} (_×_ M)
  PairFunctor = record { fmap = \f (m , a) → (m , f a) }

instance
  PairApplicative : {M : Set}
                    {{_ : Monoid  {a = Level.zero} M}}
                    {{_ : Functor {a = Level.zero} (_×_ M)}}
                  → Applicative {a = Level.zero} (_×_ M)
  PairApplicative = record
    { pure  = \x -> (mempty , x)
    ; app   = \(m2 , f) (m1 , x) -> (m1 <> m2 , f x)
    }

instance
  PairMonad : {M : Set}
              {{_ : Monoid      {a = Level.zero} M}}
              {{_ : Functor     {a = Level.zero} (_×_ M)}}
              {{_ : Applicative {a = Level.zero} (_×_ M)}}
            → Monad {a = Level.zero} (_×_ M)
  PairMonad = record
    { join = \(m2 , (m1 , x)) → (m1 <> m2 , x)
    }

-- A Set containing a count of its contained duplicate elements.
data Multiset : Set -> Set where


singleton : {A : Set} -> A -> Multiset A
singleton = {!!}

emptyMultiset : {A : Set} -> Multiset A
emptyMultiset = {!!}

data MonoidalMap : Set -> Set -> Set where -- TODO

emptyMonoidalMap : {K V : Set} -> MonoidalMap K V
emptyMonoidalMap = {!!}

singletonMM : {K V : Set} -> K -> V -> MonoidalMap K V
singletonMM = {!!}

-- A challange that a player can participate.
data Challenge (i : Set) (k : Set) (r : Set) : Set where


-- The location of the challenge
data Point : Set where

-- The distance from the exact location, which defines the range of the acceptable coordinates.
data Distance : Set where

-- The real world time
data Time : Set where

-- The photo we can get from the user
data Photo : Set where

-- The altitude of some clue
data Altitude : Set where

-- Different kind of inputs that we can get from the player.
data Input : Set where

-- Create a photo input
photo : Point -> Photo -> Input
photo = {!!}

-- Reward that the player can get after finising the challange
data Reward : Set where

-- The clue which gives information about the challenge.
data Clue : Set where

data String : Set where -- TODO

record ClueAlg (k : Set) : Set where
  constructor MkClueAlg
  field 
    -- A hint about the clue, which is rendered for the user
    hint : String -> k

    -- Nesting
    sub : k -> k -> k
  
    lawSubAssociative
      :  (k1 k2 k3 : k)
      -> (sub k1 (sub k1 k2))
         ≡
         (sub (sub k1 k2) k3)

    toList : k -> List String

    lawToListHint
      :  (s : String)
      -> toList (hint s) ≡ [ s ]

    lawToListSub
      :  (k1 k2 : k)
      -> toList (sub k1 k2)
         ≡
         toList k1 ++ toList k2

    noClue : k

    lawSubNoClueLeft
      :  (x : k)
      -> sub noClue x ≡ x

    lawSubNoClueRight
      : (x : k)
      -> sub x noClue ≡ x

-- Observation information that can be extracted from Clue's
data ClueState : Set where
  Seen      : ClueState
  Completed : ClueState
  Failed    : ClueState

seen : ClueState
seen = Seen

completed : ClueState
completed = Completed

failed : ClueState
failed = Failed

record HasFilter {a} (i : Set) : Set (suc a) where
  constructor MkHasFilter
  field
    CustomFilter : Set a
    filterMatches : CustomFilter -> i -> Bool

open HasFilter

-- A filter that describe some condition
data InputFilter (i : Set) : Set where

custom : {a : Level} -> {i : Set} -> (f : HasFilter {a} i) -> (CustomFilter f) -> InputFilter i
custom = {!!}

-- Check if the input matches the given input filter
matches : {i : Set} -> InputFilter i -> i -> Bool
matches = {!!}

-- A photo should be within some point
photoWithin : {i : Set} -> Point -> Distance -> InputFilter i
photoWithin = {!!}

-- A challange where the photo should be taken above the given altitude
photoAbove : {i : Set} -> Altitude -> InputFilter i
photoAbove = {!!}

record InputFilterAlg (i : Set) : Set where
  constructor MkInputFilterAlg
  field
    always    : InputFilter i
    never     : InputFilter i
    locWithin : Point -> Distance -> InputFilter i
    afterTime : Time -> InputFilter i
    andF      : InputFilter i -> InputFilter i -> InputFilter i
    orF       : InputFilter i -> InputFilter i -> InputFilter i
    notF      : InputFilter i -> InputFilter i

    lawMatchesAlways
      :  (x : i)
      -> matches always x ≡ true

    lawMatchesNever
      :  (x : i)
      -> matches never x ≡ false

    lawMatchesAndF
      :  (f1 , f2 : InputFilter i) -> (x : i)
      -> matches (andF f1 f2) x
         ≡
         matches f1 x ∧ matches f2 x

    lawMatchesOrF
      :  (f1 , f2 : InputFilter i) -> (x : i)
      -> matches (orF f1 f2) x
         ≡
         matches f1 x ∨ matches f2 x

    lawMatchesNotF
      :  (f1 : InputFilter i) -> (x : i)
      -> matches (notF f1) x
         ≡
         not (matches f1 x)

shorterOf : {A : Set} -> List A -> List A -> List A
shorterOf = {!!}

ClueMap : Set -> Set
ClueMap k = MonoidalMap (List k) ClueState

StepInfo : Set -> Set -> Set
StepInfo r k = r × (ClueMap k)

emptyStepInfo : {r k : Set} -> StepInfo r k
emptyStepInfo = {!!} -- (neutral, neutral)

-- The main API for the scavanger algebra.
record Scavanger {a} (i : Set) (k : Set) (r : Set) : Set (suc a) where
  constructor MkScavanger
  field
    clueAlg : ClueAlg k
    filterAlg : InputFilterAlg i

    -- Compuate the rewards for a challange, based on the inputs from the player
    getRewards : Challenge i k r -> List i -> r

    -- Return the challenge from a clue and the actual point of the user
    pointOfInterest
      :  k
      -> Point
      -> Distance
      -> r
      -> Challenge i k r

    gate
      :  InputFilter i
      -> Challenge i k r
      -> Challenge i k r

    -- Empty challenge, the easiest to make
    Empty : Challenge i k r

    lawGetRewardsEmpty
      :  {{_ : Monoid r}}
      -> (is : List i)
      -> getRewards Empty is
         ≡
         mempty

    -- Check if the given challenge is empty
    isEmpty : Challenge i k r -> Bool

    lawIsEmptyEmpty
      : isEmpty Empty ≡ true

    -- A challenge that can never be completed
    bottom : Challenge i k r

    lawGateBottom
      :  (c : Challenge i k r)
      -> bottom
         ≡
         gate (InputFilterAlg.never filterAlg) c

    -- Associate a clue with a challenge
    clue : List k -> Challenge i k r -> Challenge i k r

    lawGetRewardsClue
      : (x : k) -> (c : Challenge i k r)
      -> getRewards (clue [ x ] c)
         ≡
         getRewards c

    lawIsEmptyClue
      :  (x : k) -> (c : Challenge i k r)
      -> isEmpty (clue [ x ] c) ≡ false

    lawClueNoClue
      :  (c : Challenge i k r)
      -> clue [ ClueAlg.noClue clueAlg ] c
         ≡
         c

    lawClueSub
      : (c : Challenge i k r) -> (k1 k2 : k)
      -> clue [ ClueAlg.sub clueAlg k1 k2 ] c
         ≡
         clue [ k1 ] (clue [ k2 ] c)

    -- Trivial challenge that gives you a reward
    reward : r -> Challenge i k r

    lawGetRewardsReward
      : (rx : r) -> (is : List i)
      -> getRewards (reward rx) is
         ≡
         rx

    lawIsEmptyReward
      :  (rx : r)
      -> isEmpty (reward rx)
         ≡
         false

    isReward : Challenge i k r -> Bool

    lawIsReward
      :  (rx : r)
      -> isReward (reward rx)
         ≡
         true

    lasIsRewardEmpty
      : isReward Empty ≡ false

    lawPointOfInterest
      : (kx : k) -> (p : Point) -> (d : Distance) -> (rx : r)
      -> pointOfInterest kx p d rx
         ≡
         clue [ kx ] (gate (photoWithin p d) (reward rx))

    lawGetRewardsGate
      : (f : InputFilter i) -> (c : Challenge i k r) -> (ix : i) -> (is : List i)
      -> matches f ix ≡ true
      -> getRewards (gate f c) (ix ∷ is)
         ≡
         getRewards c is

    lawGetRewardsUnmatched
      :  (f : InputFilter i) -> (c : Challenge i k r) -> (ix : i) -> (is : List i)
      -> matches f ix ≡ false
      -> getRewards (gate f c) (ix ∷ is)
         ≡ -- TODO?
         getRewards (gate f c) is

    lawGetRewardsGateEmpty
      :  {{_ : Monoid r}}
      -> (f : InputFilter i) -> (c : Challenge i k r)
      -> getRewards (gate f c) []
         ≡
         mempty

    -- This challenge is complete if both of its children challenges are complete.
    both : Challenge i k r -> Challenge i k r -> Challenge i k r

    lawIsEmptyBoth
      :  (c1 c2 : Challenge i k r)
      -> isEmpty (both c1 c2) ≡ isEmpty c1 ∧ isEmpty c2

    lawBothCommutative
      :  (c1 c2 : Challenge i k r)
      -> both c1 c2 ≡ both c2 c1

    lawBothAssociative
      :  (c1 c2 c3 : Challenge i k r)
      -> both c1 (both c2 c3) ≡ both (both c1 c2) c3

    lawBothIdenpotent
      :  (c : Challenge i k r)
      -> both c c ≡ c

    lawGetRewardsBoth
      :  {{_ : Monoid r}}
      -> (c1 c2 : Challenge i k r) -> (is : List i)
      -> getRewards (both c1 c2) is
         ≡
         getRewards c1 is <> getRewards c2 is

    lawBothLeftIdentity
      :  (c : Challenge i k r)
      -> both Empty c ≡ c

    lawBothRightIdentity
      :  (c : Challenge i k r)
      -> both c Empty ≡ c

    -- Connect two challenges one after another
    andThen : Challenge i k r -> Challenge i k r -> Challenge i k r

    lawIsEmptyAndThen
      :  (c1 c2 : Challenge i k r)
      -> isEmpty (andThen c1 c2) ≡ isEmpty c1 ∧ isEmpty c2

    lawAndThenGate
      :  (f : InputFilter i) -> (c1 c2 : Challenge i k r)
      -> andThen (gate f c1) c2
         ≡
         gate f (andThen c1 c2)

    lawAndThenAssociative
      : (c1 c2 c3 : Challenge i k r)
      -> andThen c1 (andThen c2 c3)
         ≡
         andThen (andThen c1 c2) c3

    lawAndThenLeftIdentity
      :  (c : Challenge i k r)
      -> andThen Empty c ≡ c

    lawAndThenRightIdentity
      :  (c : Challenge i k r)
      -> andThen c Empty ≡ c

    completes : Challenge i k r -> List i -> Maybe (List i)

    lawCompletesEmpty
      :  (is : List i)
      -> completes Empty is ≡ just is

    lawCompletesReward
      :  (rx : r) -> (is : List i)
      -> completes (reward rx) is ≡ just is

    lawCompletesBoth
      :  {{_ : Functor Maybe}} {{_ : Applicative Maybe}}
      -> (c1 c2 : Challenge i k r) -> (is : List i)
      -> completes (both c1 c2) is
         ≡
         (shorterOf <$> (completes c1 is) <*> (completes c2 is))

    lawCompletesClue
      :  (kx : k) -> (c : Challenge i k r) -> (is : List i)
      -> completes (clue [ kx ] c) is
         ≡
         completes c is

    lawCompletesGate
      :  (f : InputFilter i) -> (c : Challenge i k r) -> (ix : i) -> (is : List i)
      -> matches f ix ≡ true
      -> completes (gate f c) (ix ∷ is) ≡ completes c is

    lawCompletesGateUnmatched
      : (f : InputFilter i) -> (c : Challenge i k r) -> (ix : i) -> (is : List i)
      -> matches f ix ≡ false
      -> completes (gate f c) (ix ∷ is) ≡ completes (gate f c) is

    lawCompletesGateEmpty
      :  (f : InputFilter i) -> (c : Challenge i k r)
      -> completes (gate f c) [] ≡ nothing

    lawCompletesAndThen
      : {{_ : Functor Maybe}} {{_ : Monad Maybe}}
      -> (c1 c2 : Challenge i k r) -> (is : List i)
      -> completes (andThen c1 c2) is
         ≡
         ((completes c1 is) >>= completes c2)

    lawGetRewardsAndThen
      :  {{_ : Monoid r}}
      -> (c1 c2 : Challenge i k r) -> (is is' : List i)
      -> completes c1 is ≡ just is'
      -> getRewards (andThen c1 c2) is
         ≡
         getRewards c1 is <> getRewards c2 is'

    lawGetRewardsAndThenIncomplete
      :  (c1 c2 : Challenge i k r) -> (is : List i)
      -> completes c1 is ≡ nothing
      -> getRewards (andThen c1 c2) is
         ≡
         getRewards c1 is

    lawBothAndThenReward
      :  (rx : r) -> (c1 c2 : Challenge i k r)
      -> both (andThen (reward rx) c1) c2
         ≡
         andThen (reward rx) (both c1 c2)

    eitherC : Challenge i k r -> Challenge i k r -> Challenge i k r

    lawIsEmpty
      :  (c1 c2 : Challenge i k r)
      -> isEmpty (eitherC c1 c2) ≡ isEmpty c1 ∧ isEmpty c2

    lawEitherCAssociative
      :  (c1 c2 c3 : Challenge i k r)
      -> eitherC c1 (eitherC c2 c3)
         ≡
         eitherC (eitherC c1 c2) c3

    lawEitherCCommutative
      :  (c1 c2 : Challenge i k r)
      -> eitherC c1 c2 ≡ eitherC c2 c1

    lawEitherC
      :  (rx : r) -> (c1 c2 : Challenge i k r)
      -> eitherC (andThen (reward rx) c1) c2
         ≡
         andThen (reward rx) (eitherC c1 c2)

    -- This has an issue in the Idris code
    lawEitherCempty
      :  (c : Challenge i k r)
      -> isReward c ≡ false
      -> eitherC Empty c ≡ Empty

--    time : Time -> Input

    step : List k -> Maybe i -> Challenge i k r -> ((StepInfo r k) × Challenge i k r)

    lawIsEmptyStep
      :  (mi : Maybe i) -> (c1 c2 : Challenge i k r) -> (m : (StepInfo r k)) -> (ks : List k)
      -> step ks mi c1 ≡ (m , c2)
      -> isEmpty c1 ≡ true
      -> isEmpty c2 ≡ true

    lawStepBoth
      :  {{_ : Monoid (StepInfo r k)}}
      -> (mi : Maybe i) -> (c1 c2 : Challenge i k r) -> (ks : List k)
      -> step ks mi (both c1 c2)
         ≡
         (both <$> (step ks mi c1)) <*> (step ks mi c2)

    lawStepEitherC
      :  {{_ : Monoid (StepInfo r k)}}
      -> (mi : Maybe i) -> (c1 , c2 : Challenge i k r) -> (ks : List k)
      -> step ks mi (eitherC c1 c2)
         ≡
         (eitherC <$> (step ks mi c1) <*> (step ks mi c2))

    lawStepEmpty
      :  {{_ : Monoid ((StepInfo r k) × Challenge i k r)}}
      -> (mi : Maybe i) -> (ks : List k)
      -> step ks mi Empty ≡ mempty

    lawStepReward
      :  {{_ : Monoid (MonoidalMap (List k) ClueState)}}
      -> (mi : Maybe i) -> (rx : r) -> (ks : List k)
      -> step ks mi (reward rx)
         ≡
         ((rx , mempty) , Empty)

    lawStepGate
      :  (ix : i) -> (f : InputFilter i) -> (c : Challenge i k r) -> (ks : List k)
      -> matches f ix ≡ true
      -> step ks (just ix) (gate f c)
         ≡
         step ks nothing c

    lawStepGateUnmatched
      :  {{_ : Monoid (StepInfo r k)}}
      -> (ix : i) -> (f : InputFilter i) -> (c : Challenge i k r) -> (ks : List k)
      -> matches f ix ≡ false
      -> step ks (just ix) (gate f c)
         ≡
         (mempty , gate f c)

    lawStepGateNothing
      :  {{_ : Monoid (StepInfo r k)}}
      -> (f : InputFilter i) -> (c : Challenge i k r) -> (ks : List k)
      -> step ks nothing (gate f c)
         ≡
         (mempty , gate f c)

    lawStepAndThenComplete
      :  {{_ : Monoid (StepInfo r k)}}
      -> (mi : Maybe i) -> (c1 c2 : Challenge i k r) -> (rx : r) -> (ks : List k)
      -> step ks mi c1 ≡ ((rx , emptyMonoidalMap) , Empty)
      -> step ks mi (andThen c1 c2)
         ≡
         join ((rx , emptyMonoidalMap) , step ks nothing c2)

    lawStepAndThenIncomplete
      :  {{_ : Monoid (StepInfo r k)}}
      -> (mi : Maybe i) -> (c1 c2 c3 : Challenge i k r) -> (m : (StepInfo r k)) -> (ks : List k)
      -> step ks mi c1 ≡ (m , c3)
      -> isEmpty c3 ≡ true
      -> step ks mi (andThen c1 c2)
         ≡
         (andThen <$> (step ks mi c1) <*> (mempty , c2))

    tellClue : ClueMap k -> (StepInfo r k × Challenge i k r)

    -- This is suspicious
    lawStepClueEmpty
      :  {{_ : Monoid (StepInfo r k)}}
      -> (mi : Maybe i) -> (kctx kx : k)
      -> step [ kctx ] mi (clue [ kx ] Empty)
         ≡
         (tellClue (singletonMM [ ClueAlg.sub clueAlg kctx kx ] completed) *> (mempty , Empty))

    lawStepClueNonEmpty
      :  {{_ : Monoid (StepInfo r k)}}
      -> (mi : Maybe i) -> (kctx kx : k) -> (c : Challenge i k r)
      -> isEmpty c ≡ false
      -> step [ kctx ] mi (clue [ kx ] c)
         ≡
         ((tellClue (singletonMM [ ClueAlg.sub clueAlg kctx kx ] seen))
          *>
          (clue <$> (mempty , [ kx ]) <*> step [ ClueAlg.sub clueAlg kctx kx ] mi c))

    runChallenge : Challenge i k r -> List i -> (StepInfo r k × Challenge i k r)

    lawRunChallenge
      :  {{_ : Foldable List}} {{_ : Monoid (StepInfo r k)}}
      -> (c : Challenge i k r) -> (is : List i) -> (ks : List k)
      -> runChallenge c is
         ≡
         foldM (flip (step ks)) c (nothing ∷ Data.List.map just is)

    lawGetRewardsRunChallenge
      :  (c : Challenge i k r) -> (is : List i)
      -> getRewards c is
         ≡
         proj₁ (proj₁ (runChallenge c is))

    lawCompletes
      :  (c : Challenge i k r) -> (is : List i)
      -> is-nothing (completes c is)
         ≡
         isEmpty (proj₂ (runChallenge c is))

    getClues : Challenge i k r -> List i -> ClueMap k

    findClues : k -> Challenge i k r -> ClueMap k
    -- Sketch of the implementation is on the page 137.

    lawStepEitherCEmpty
      :  {{_ : Monoid (StepInfo r k)}}
      -> (kctx : List k) -> (mi : Maybe i)
      -> (c1 c2 c2' : Challenge i k r) -> (z1 z2 : StepInfo r k)
      -> step kctx mi c1 ≡ (z1 , Empty)
      -> step kctx mi c2 ≡ (z2 , c2')
      -> step kctx mi (eitherC c1 c2)
         ≡
         ({- fmap soonToFailed (findClues kctx c2') *> -} (step kctx mi c2) *> (step kctx mi c1))
         -- TODO: implement soonToFailed and findClues ???

    lawStepEitherCNonEmpty
      :  {{_ : Monoid (StepInfo r k)}}
      -> (kctx : List k) -> (mi : Maybe i)
      -> (c1 c2 c1' c2' : Challenge i k r) -> (z1 z2 : StepInfo r k)
      -> step kctx mi c1 ≡ (z1 , c1')
      -> step kctx mi c2 ≡ (z2 , c2')
      -> isEmpty c1' ≡ false -> isEmpty c2' ≡ false
      -> step kctx mi (eitherC c1 c2)
         ≡
         eitherC <$> step kctx mi c1 <*> step kctx mi c2
