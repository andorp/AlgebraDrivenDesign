-- {-# OPTIONS --type-in-type #-}
module Scavanger where

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
data Challenge : Set where

-- Different kind of inputs that we can get from the player.
data Input : Set where

-- Reward that the player can get after finising the challange
data Reward : Set where

-- The clue which gives information about the challenge.
data Clue : Set where

data String : Set where -- TODO

record ClueAlg : Set where
  constructor MkClueAlg
  field 
    -- A hint about the clue, which is rendered for the user
    hint : String -> Clue

    -- Nesting
    sub : Clue -> Clue -> Clue
  
    lawSubAssociative
      :  (k1 k2 k3 : Clue)
      -> (sub k1 (sub k1 k2))
         ≡
         (sub (sub k1 k2) k3)

    toList : Clue -> List String

    lawToListHint
      :  (s : String)
      -> toList (hint s) ≡ [ s ]

    lawToListSub
      :  (k1 k2 : Clue)
      -> toList (sub k1 k2)
         ≡
         toList k1 ++ toList k2

    noClue : Clue

    lawSubNoClueLeft
      :  (k : Clue)
      -> sub noClue k ≡ k

    lawSubNoClueRight
      : (k : Clue)
      -> sub k noClue ≡ k

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

-- A filter that describe some condition
data InputFilter : Set where

-- Check if the input matches the given input filter
matches : InputFilter -> Input -> Bool
matches = {!!}


record InputFilterAlg : Set where
  constructor MkInputFilterAlg
  field
    always    : InputFilter
    never     : InputFilter
    locWithin : Point -> Distance -> InputFilter
    afterTime : Time -> InputFilter
    andF      : InputFilter -> InputFilter -> InputFilter
    orF       : InputFilter -> InputFilter -> InputFilter
    notF      : InputFilter -> InputFilter

    lawMatchesAlways
      :  (i : Input)
      -> matches always i ≡ true

    lawMatchesNever
      :  (i : Input)
      -> matches never i ≡ false

    lawMatchesAndF
      :  (f1 , f2 : InputFilter) -> (i : Input)
      -> matches (andF f1 f2) i
         ≡
         matches f1 i ∧ matches f2 i

    lawMatchesOrF
      :  (f1 , f2 : InputFilter) -> (i : Input)
      -> matches (orF f1 f2) i
         ≡
         matches f1 i ∨ matches f2 i

    lawMatchesNotF
      :  (f1 : InputFilter) -> (i : Input)
      -> matches (notF f1) i
         ≡
         not (matches f1 i)

shorterOf : {A : Set} -> List A -> List A -> List A
shorterOf = {!!}

StepInfo : Set
StepInfo = (Multiset Reward × MonoidalMap Clue ClueState)

emptyStepInfo : StepInfo
emptyStepInfo = {!!} -- (neutral, neutral)

-- The main API for the scavanger algebra.
record Scavanger {a} : Set (suc a) where
  constructor MkScavanger
  field
    clueAlg : ClueAlg
    filterAlg : InputFilterAlg

    -- Compuate the rewards for a challange, based on the inputs from the player
    getRewards : Challenge -> List Input -> Multiset Reward

    -- Return the challange from a clue and the actual point of the user
    pointOfInterest
      :  Clue
      -> Point
      -> Distance
      -> Reward
      -> Challenge

    gate
      :  InputFilter
      -> Challenge
      -> Challenge

    -- Create a photo input
    photo : Point -> Photo -> Input

    -- Check if the given point is within the distance
    within : Point -> Point -> Distance -> Bool

    -- Empty challenge, the easiest to make
    Empty : Challenge

    lawGetRewardsEmpty
      :  {{_ : Monoid (Multiset Reward)}}
      -> (is : List Input)
      -> getRewards Empty is
         ≡
         mempty

    -- Check if the given challenge is empty
    isEmpty : Challenge -> Bool

    lawIsEmptyEmpty
      : isEmpty Empty ≡ true

    -- A challenge that can never be completed
    bottom : Challenge

    lawGateBottom
      :  (c : Challenge)
      -> bottom
         ≡
         gate (InputFilterAlg.never filterAlg) c

    -- Associate a clue with a challenge
    clue : Clue -> Challenge -> Challenge

    lawGetRewardsClue
      : (k : Clue) -> (c : Challenge)
      -> getRewards (clue k c)
         ≡
         getRewards c

    lawIsEmptyClue
      :  (k : Clue) -> (c : Challenge)
      -> isEmpty (clue k c) ≡ false

    lawClueNoClue
      :  (c : Challenge)
      -> clue (ClueAlg.noClue clueAlg) c
         ≡
         c

    lawClueSub
      : (c : Challenge) -> (k1 k2 : Clue)
      -> clue (ClueAlg.sub clueAlg k1 k2) c
         ≡
         clue k1 (clue k2 c)

    -- Trivial challenge that gives you a reward
    reward : Reward -> Challenge

    lawGetRewardsReward
      : (r : Reward) -> (is : List Input)
      -> getRewards (reward r) is
         ≡
         singleton r

    lawIsEmptyReward
      :  (r :  Reward)
      -> isEmpty (reward r)
         ≡
         false

    isReward : Challenge -> Bool

    lawIsReward
      :  (r : Reward)
      -> isReward (reward r)
         ≡
         true

    lasIsRewardEmpty
      : isReward Empty ≡ false

    -- A photo should be within some point
    photoWithin
      :  Point
      -> Distance
      -> InputFilter

    lawPointOfInterest
      : (c : Clue) -> (p : Point) -> (d : Distance) -> (r : Reward)
      -> pointOfInterest c p d r
         ≡
         clue c (gate (photoWithin p d) (reward r))

    -- A challange where the photo should be taken above the given altitude
    photoAbove
      :  Altitude
      -> InputFilter

    lawGetRewardsGate
      : (f : InputFilter) -> (c : Challenge) -> (i : Input) -> (is : List Input)
      -> matches f i ≡ true
      -> getRewards (gate f c) (i ∷ is)
         ≡
         getRewards c is

    lawGetRewardsUnmatched
      :  (f : InputFilter) -> (c : Challenge) -> (i : Input) -> (is : List Input)
      -> matches f i ≡ false
      -> getRewards (gate f c) (i ∷ is)
         ≡ -- TODO?
         getRewards (gate f c) is

    lawGetRewardsGateEmpty
      :  {{_ : Monoid (Multiset Reward)}}
      -> (f : InputFilter) -> (c : Challenge)
      -> getRewards (gate f c) []
         ≡
         mempty

    -- This challenge is complete if both of its children challenges are complete.
    both : Challenge -> Challenge -> Challenge

    lawIsEmptyBoth
      :  (c1 c2 : Challenge)
      -> isEmpty (both c1 c2) ≡ isEmpty c1 ∧ isEmpty c2

    lawBothCommutative
      :  (c1 c2 : Challenge)
      -> both c1 c2 ≡ both c2 c1

    lawBothAssociative
      :  (c1 c2 c3 : Challenge)
      -> both c1 (both c2 c3) ≡ both (both c1 c2) c3

    lawBothIdenpotent
      :  (c : Challenge)
      -> both c c ≡ c

    lawGetRewardsBoth
      :  {{_ : Monoid (Multiset Reward)}}
      -> (c1 c2 : Challenge) -> (is : List Input)
      -> getRewards (both c1 c2) is
         ≡
         getRewards c1 is <> getRewards c2 is

    lawBothLeftIdentity
      :  (c : Challenge)
      -> both Empty c ≡ c

    lawBothRightIdentity
      :  (c : Challenge)
      -> both c Empty ≡ c

    -- Connect two challenges one after another
    andThen : Challenge -> Challenge -> Challenge

    lawIsEmptyAndThen
      :  (c1 c2 : Challenge)
      -> isEmpty (andThen c1 c2) ≡ isEmpty c1 ∧ isEmpty c2

    lawAndThenGate
      :  (f : InputFilter) -> (c1 c2 : Challenge)
      -> andThen (gate f c1) c2
         ≡
         gate f (andThen c1 c2)

    lawAndThenAssociative
      : (c1 c2 c3 : Challenge)
      -> andThen c1 (andThen c2 c3)
         ≡
         andThen (andThen c1 c2) c3

    lawAndThenLeftIdentity
      :  (c : Challenge)
      -> andThen Empty c ≡ c

    lawAndThenRightIdentity
      :  (c : Challenge)
      -> andThen c Empty ≡ c

    completes : Challenge -> List Input -> Maybe (List Input)

    lawCompletesEmpty
      :  (is : List Input)
      -> completes Empty is ≡ just is

    lawCompletesReward
      :  (r : Reward) -> (is : List Input)
      -> completes (reward r) is ≡ just is

    -- Needs type in type?
    lawCompletesBoth
      :  {{_ : Functor Maybe}} {{_ : Applicative Maybe}}
      -> (c1 c2 : Challenge) -> (is : List Input)
      -> completes (both c1 c2) is
         ≡
         (shorterOf <$> (completes c1 is) <*> (completes c2 is))

    lawCompletesClue
      :  (k : Clue) -> (c : Challenge) -> (is : List Input)
      -> completes (clue k c) is
         ≡
         completes c is

    lawCompletesGate
      :  (f : InputFilter) -> (c : Challenge) -> (i : Input) -> (is : List Input)
      -> matches f i ≡ true
      -> completes (gate f c) (i ∷ is) ≡ completes c is

    lawCompletesGateUnmatched
      : (f : InputFilter) -> (c : Challenge) -> (i : Input) -> (is : List Input)
      -> matches f i ≡ false
      -> completes (gate f c) (i ∷ is) ≡ completes (gate f c) is

    lawCompletesGateEmpty
      :  (f : InputFilter) -> (c : Challenge)
      -> completes (gate f c) [] ≡ nothing

    -- Needs type in type?
    lawCompletesAndThen
      : {{_ : Functor Maybe}} {{_ : Monad Maybe}}
      -> (c1 c2 : Challenge) -> (is : List Input)
      -> completes (andThen c1 c2) is
         ≡
         ((completes c1 is) >>= completes c2)

    lawGetRewardsAndThen
      :  {{_ : Monoid (Multiset Reward)}}
      -> (c1 c2 : Challenge) -> (is is' : List Input)
      -> completes c1 is ≡ just is'
      -> getRewards (andThen c1 c2) is
         ≡
         getRewards c1 is <> getRewards c2 is'

    lawGetRewardsAndThenIncomplete
      :  (c1 c2 : Challenge) -> (is : List Input)
      -> completes c1 is ≡ nothing
      -> getRewards (andThen c1 c2) is
         ≡
         getRewards c1 is

    lawBothAndThenReward
      :  (r : Reward) -> (c1 c2 : Challenge)
      -> both (andThen (reward r) c1) c2
         ≡
         andThen (reward r) (both c1 c2)

    eitherC : Challenge -> Challenge -> Challenge

    lawIsEmpty
      :  (c1 c2 : Challenge)
      -> isEmpty (eitherC c1 c2) ≡ isEmpty c1 ∧ isEmpty c2

    lawEitherCAssociative
      :  (c1 c2 c3 : Challenge)
      -> eitherC c1 (eitherC c2 c3)
         ≡
         eitherC (eitherC c1 c2) c3

    lawEitherCCommutative
      :  (c1 c2 : Challenge)
      -> eitherC c1 c2 ≡ eitherC c2 c1

    lawEitherC
      :  (r : Reward) -> (c1 c2 : Challenge)
      -> eitherC (andThen (reward r) c1) c2
         ≡
         andThen (reward r) (eitherC c1 c2)

    -- This has an issue in the Idris code
    lawEitherCempty
      :  (c : Challenge)
      -> isReward c ≡ false
      -> eitherC Empty c ≡ Empty

    time : Time -> Input

    step : Clue -> Maybe Input -> Challenge -> (StepInfo × Challenge)

    lawIsEmptyStep
      :  (i : Maybe Input) -> (c1 c2 : Challenge) -> (m : StepInfo) -> (k : Clue)
      -> step k i c1 ≡ (m , c2)
      -> isEmpty c1 ≡ true
      -> isEmpty c2 ≡ true

    lawStepBoth
      :  {{_ : Monoid StepInfo}}
      -> (i : Maybe Input) -> (c1 c2 : Challenge) -> (k : Clue)
      -> step k i (both c1 c2)
         ≡
         (both <$> (step k i c1)) <*> (step k i c2)

    lawStepEitherC
      :  {{_ : Monoid StepInfo}}
      -> (i : Maybe Input) -> (c1 , c2 : Challenge) -> (k : Clue)
      -> step k i (eitherC c1 c2)
         ≡
         (eitherC <$> (step k i c1) <*> (step k i c2))

    lawStepEmpty
      :  {{_ : Monoid (StepInfo × Challenge)}}
      -> (i : Maybe Input) -> (k : Clue)
      -> step k i Empty ≡ mempty

    lawStepReward
      :  {{_ : Monoid (MonoidalMap Clue ClueState)}}
      -> (i : Maybe Input) -> (r : Reward) -> (k : Clue)
      -> step k i (reward r)
         ≡
         ((singleton r , mempty) , Empty)

    lawStepGate
      :  (i : Input) -> (f : InputFilter) -> (c : Challenge) -> (k : Clue)
      -> matches f i ≡ true
      -> step k (just i) (gate f c)
         ≡
         step k nothing c

    lawStepGateUnmatched
      :  {{_ : Monoid StepInfo}}
      -> (i : Input) -> (f : InputFilter) -> (c : Challenge) -> (k : Clue)
      -> matches f i ≡ false
      -> step k (just i) (gate f c)
         ≡
         (mempty , gate f c)

    lawStepGateNothing
      :  {{_ : Monoid StepInfo}}
      -> (f : InputFilter) -> (c : Challenge) -> (k : Clue)
      -> step k nothing (gate f c)
         ≡
         (mempty , gate f c)

    lawStepAndThenComplete
      :  {{_ : Monoid StepInfo}}
      -> (i : Maybe Input) -> (c1 c2 : Challenge) -> (r : Reward) -> (k : Clue)
      -> step k i c1 ≡ ((singleton r , emptyMonoidalMap) , Empty)
      -> step k i (andThen c1 c2)
         ≡
         join (( singleton r , emptyMonoidalMap) , step k nothing c2)

    lawStepAndThenIncomplete
      :  {{_ : Monoid StepInfo}}
      -> (i : Maybe Input) -> (c1 c2 c3 : Challenge) -> (m : StepInfo) -> (k : Clue)
      -> step k i c1 ≡ (m , c3)
      -> isEmpty c3 ≡ true
      -> step k i (andThen c1 c2)
         ≡
         (andThen <$> (step k i c1) <*> (emptyStepInfo , c2))

    tellClue : MonoidalMap Clue ClueState -> (StepInfo × Challenge)

    lawStepClueEmpty
      :  {{_ : Monoid StepInfo}}
      -> (i : Maybe Input) -> (kctx k : Clue)
      -> step kctx i (clue k Empty)
         ≡
         (tellClue (singletonMM (ClueAlg.sub clueAlg kctx k) completed) *> (mempty , Empty))

    lawStepClueNonEmpty
      :  {{_ : Monoid StepInfo}}
      -> (i : Maybe Input) -> (kctx k : Clue) -> (c : Challenge)
      -> isEmpty c ≡ false
      -> step kctx i (clue k c)
         ≡
         ((tellClue (singletonMM (ClueAlg.sub clueAlg kctx k) seen))
          *>
          (clue <$> (mempty , k) <*> step (ClueAlg.sub clueAlg kctx k) i c))
 
    runChallenge : Challenge -> List Input -> (StepInfo × Challenge)

    lawRunChallenge
      :  {{_ : Foldable List}} {{_ : Monoid StepInfo}}
      -> (c : Challenge) -> (is : List Input) -> (k : Clue)
      -> runChallenge c is
         ≡
         foldM (flip (step k)) c (nothing ∷ Data.List.map just is)

    lawGetRewardsRunChallenge
      :  (c : Challenge) -> (is : List Input)
      -> getRewards c is
         ≡
         proj₁ (proj₁ (runChallenge c is))

    lawCompletes
      :  (c : Challenge) -> (is : List Input)
      -> is-nothing (completes c is)
         ≡
         isEmpty (proj₂ (runChallenge c is))

    getClues : Challenge -> List Input -> MonoidalMap Clue ClueState

    findClues : Clue -> Challenge -> MonoidalMap Clue ClueState

    lawStepEitherCEmpty
      :  {{_ : Monoid StepInfo}}
      -> (kctx : Clue) -> (i : Maybe Input)
      -> (c1 c2 c2' : Challenge) -> (z1 z2 : StepInfo)
      -> step kctx i c1 ≡ (z1 , Empty)
      -> step kctx i c2 ≡ (z2 , c2')
      -> step kctx i (eitherC c1 c2)
         ≡
         ({- fmap soonToFailed (findClues kctx c2') *> -} (step kctx i c2) *> (step kctx i c1))

    lawStepEitherCNonEmpty
      :  {{_ : Monoid StepInfo}}
      -> (kctx : Clue) -> (i : Maybe Input)
      -> (c1 c2 c1' c2' : Challenge) -> (z1 z2 : StepInfo)
      -> step kctx i c1 ≡ (z1 , c1')
      -> step kctx i c2 ≡ (z2 , c2')
      -> isEmpty c1' ≡ false -> isEmpty c2' ≡ false
      -> step kctx i (eitherC c1 c2)
         ≡
         eitherC <$> step kctx i c1 <*> step kctx i c2

