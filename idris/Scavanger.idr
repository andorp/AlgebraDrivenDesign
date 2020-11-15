module Scavanger

Monoid a => Applicative (Pair a) where
  pure a              = (neutral, a)
  (m2, f) <*> (m1, x) = (m1 <+> m2, f x)

Monoid a => Monad (Pair a) where
  join (m2, (m1, a)) = (m1 <+> m2, a)

Monoid a => Foldable (Pair a) where
  foldr f i (_, a) = f a i

foldM : (b -> a -> m b) -> b -> (Foldable t, Monad m) => t a -> m b
foldM f i t = ?

||| A Set containing a count of its contained duplicate elements.
data Multiset : Type -> Type where

singleton : a -> Multiset a
singleton = ?

emptyMultiset : Multiset a
emptyMultiset = ?

Eq a => Eq (Multiset a) where -- TODO
  a == b = ?

Semigroup (Multiset a) where -- TODO
  a <+> b = ?

Monoid (Multiset a) where -- TODO
  neutral = ?

data MonoidalMap : Type -> Type -> Type where -- TODO

emptyMonoidalMap : MonoidalMap k v
emptyMonoidalMap = ?

singletonMM : k -> v -> MonoidalMap k v
singletonMM = ?

(Eq k, Eq v) => Eq (MonoidalMap k v) where
  a == b = ?

Semigroup (MonoidalMap k v) where -- TODO
  a <+> b = ?

Monoid (MonoidalMap k v) where -- TODO
  neutral = ?

second : (b -> c) -> (a,b) -> (a,c)
second = ?

||| A challange that a player can participate.
data Challenge : Type where

Eq Challenge where
  a == b = ?

||| Different kind of inputs that we can get from the player.
data Input : Type where

||| Reward that the player can get after finising the challange
data Reward : Type where

||| The clue which gives information about the challenge.
data Clue : Type where

record ClueAlg where
  constructor MkClueAlg
  ||| A hint about the clue, which is rendered for the user
  hint : String -> Clue

  ||| Nesting
  sub : Clue -> Clue -> Clue

  lawSubAssociative
    :  (k1,k2,k3 : Clue)
    -> sub k1 (sub k1 k2)
       =
       sub (sub k1 k2) k3

  toList : Clue -> List String

  lawToListHint
    :  (s : String)
    -> toList (hint s) = [s]

  lawToListSub
    :  (k1, k2 : Clue)
    -> toList (sub k1 k2)
       =
       toList k1 ++ toList k2

  noClue : Clue

  lawSubNoClueLeft
    :  (k : Clue)
    -> sub noClue k = k

  lawSubNoClueRight
    : (k : Clue)
    -> sub k noClue = k

||| Observation information that can be extracted from Clue's
data ClueState : Type where
  Seen      : ClueState
  Completed : ClueState
  Failed    : ClueState

seen : ClueState
seen = Seen

completed : ClueState
completed = Completed

failed : ClueState
failed = Failed

Eq ClueState where
  Seen      == Seen      = True
  Completed == Completed = True
  Failed    == Failed    = True
  _         == _         = True

||| The location of the challenge
data Point : Type where

||| The distance from the exact location, which defines the range of the acceptable coordinates.
data Distance : Type where

||| The real world time
data Time : Type where

||| The photo we can get from the user
data Photo : Type where

||| The altitude of some clue
data Altitude : Type where

||| A filter that describe some condition
data InputFilter : Type where

||| Check if the input matches the given input filter
matches : InputFilter -> Input -> Bool
matches = ?

record InputFilterAlg where
  constructor MkInputFilterAlg
  always : InputFilter
  never : InputFilter
  locWithin : Point -> Distance -> InputFilter
  afterTime : Time -> InputFilter
  andF : InputFilter -> InputFilter -> InputFilter
  orF : InputFilter -> InputFilter -> InputFilter
  notF : InputFilter -> InputFilter

-- TODO
--  lawMatchesAlways
--    :  (i : Input)
--    -> matches always i = True
--
--  lawMatchesNever
--    :  (i : Input)
--    -> matches never i = False

  lawMatchesAndF
    :  (f1 , f2 : InputFilter) -> (i : Input)
    -> matches (andF f1 f2) i
       =
       matches f1 i && matches f2 i

  lawMatchesOrF
    :  (f1 , f2 : InputFilter) -> (i : Input)
    -> matches (orF f1 f2) i
       =
       matches f1 i || matches f2 i

  lawMatchesNotF
    :  (f1 : InputFilter) -> (i : Input)
    -> matches (notF f1) i
       =
       not (matches f1 i)

shorterOf : List a -> List a -> List a
shorterOf = ?

(Semigroup a, Semigroup b) => Semigroup (a,b) where
  (a1,b1) <+> (a2,b2) = (a1 <+> a2, b1 <+> b2)

(Monoid a, Monoid b) => Monoid (a,b) where
  neutral = (neutral, neutral)

public export
StepInfo : Type
StepInfo = (Multiset Reward, MonoidalMap Clue ClueState)

emptyStepInfo : StepInfo
emptyStepInfo = (neutral, neutral)

||| The main API for the scavanger algebra.
record Scavanger where
  constructor MkScavanger

  clueAlg : ClueAlg
  filterAlg : InputFilterAlg

  ||| Compuate the rewards for a challange, based on the inputs from the player
  getRewards : Challenge -> List Input -> Multiset Reward

  ||| Return the challange from a clue and the actual point of the user
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

  ||| Create a photo input
  photo : Point -> Photo -> Input

  ||| Check if the given point is within the distance
  within : Point -> Point -> Distance -> Bool

  ||| Empty challenge, the easiest to make
  Empty : Challenge

  lawGetRewardsEmpty
    :  (is : List Input)
    -> getRewards empty is
       =
       Prelude.neutral

  ||| Check if the given challenge is empty
  isEmpty : Challenge -> Bool
  IsEmpty : Challenge -> Bool

  lawIsEmptyEmpty
    : isEmpty Empty = True

  ||| A challenge that can never be completed
  bottom : Challenge

  lawGateBottom
    :  (c : Challenge)
    -> bottom
       =
       gate (never filterAlg) c

  ||| Associate a clue with a challenge
  clue : Clue -> Challenge -> Challenge

  lawGetRewardsClue
    : (k : Clue) -> (c : Challenge)
    -> getRewards (clue k c)
       =
       getRewards c

  lawIsEmptyClue
    :  (k : Clue) -> (c : Challenge)
    -> isEmpty (clue k c) = False

  lawClueNoClue
    :  (c : Challenge)
    -> clue (noClue clueAlg) c
       =
       c

  lawClueSub
    : (c : Challenge) -> (k1, k2 : Clue)
    -> clue (sub clueAlg k1 k2) c
       =
       clue k1 (clue k2 c)

  ||| Trivial challenge that gives you a reward
  reward : Reward -> Challenge

  lawGetRewardsReward
    : (r : Reward) -> (is : List Input)
    -> getRewards (reward r) is = singleton r

  lawIsEmptyReward
    :  (r :  Reward)
    -> isEmpty (reward r) = False

  isReward : Challenge -> Bool

  lawIsReward
    :  (r : Reward)
    -> isReward (reward r) = True

  lasIsRewardEmpty
    : isReward Empty = False

  ||| A photo should be within some point
  photoWithin
    :  Point
    -> Distance
    -> InputFilter

  lawPointOfInterest
    : (c : Clue) -> (p : Point) -> (d : Distance) -> (r : Reward)
    -> pointOfInterest c p d r
       =
       clue c (gate (photoWithin p d) (reward r))

  ||| A challange where the photo should be taken above the given altitude
  photoAbove
    :  Altitude
    -> InputFilter

  lawGetRewardsGate
    : (f : InputFilter) -> (c : Challenge) -> (i : Input) -> (is : List Input)
    -> matches f i = True
    -> getRewards (gate f c) (i :: is)
       =
       getRewards c is

  lawGetRewardsUnmatched
    :  (f : InputFilter) -> (c : Challenge) -> (i : Input) -> (is : List Input)
    -> matches f i = False
    -> getRewards (gate f c) (i :: is)
       =
       getRewards (gate f c) is

  lawGetRewardsGateEmpty
    :  (f : InputFilter) -> (c : Challenge)
    -> getRewards (gate f c) []
       =
       Prelude.neutral

  ||| This challenge is complete if both of its children challenges are complete.
  both : Challenge -> Challenge -> Challenge

  lawIsEmptyBoth
    :  (c1 , c2 : Challenge)
    -> isEmpty (both c1 c2) = isEmpty c1 && isEmpty c2

  lawBothCommutative
    :  (c1 , c2 : Challenge)
    -> both c1 c2 = both c2 c1

  lawBothAssociative
    :  (c1 , c2 , c3 : Challenge)
    -> both c1 (both c2 c3) = both (both c1 c2) c3

  lawBothIdenpotent
    :  (c : Challenge)
    -> both c c = c

  lawGetRewardsBoth
    :  (c1 , c2 : Challenge) -> (is : List Input)
    -> getRewards (both c1 c2) is
       =
       getRewards c1 is <+> getRewards c2 is

  lawBothLeftIdentity
    :  (c : Challenge)
    -> both Empty c = c

  lawBothRightIdentity
    :  (c : Challenge)
    -> both c Empty = c

  ||| Connect two challenges one after another
  andThen : Challenge -> Challenge -> Challenge

  lawIsEmptyAndThen
    :  (c1 , c2 : Challenge)
    -> isEmpty (andThen c1 c2) = isEmpty c1 && isEmpty c2

  lawAndThenGate
    :  (f : InputFilter) -> (c1 , c2 : Challenge)
    -> andThen (gate f c1) c2
       =
       gate f (andThen c1 c2)

  lawAndThenAssociative
    : (c1 , c2 , c3 : Challenge)
    -> andThen c1 (andThen c2 c3)
       =
       andThen (andThen c1 c2) c3

  lawAndThenLeftIdentity
    :  (c : Challenge)
    -> andThen Empty c = c

  lawAndThenRightIdentity
    :  (c : Challenge)
    -> andThen c Empty = c

  completes : Challenge -> List Input -> Maybe (List Input)
  Completes : Challenge -> List Input -> Maybe (List Input)

  lawCompletesEmpty
    :  (is : List Input)
    -> completes Empty is = Just is

  lawCompletesReward
    :  (r : Reward) -> (is : List Input)
    -> completes (reward r) is = Just is

  lawCompletesBoth
    :  (c1 , c2 : Challenge) -> (is : List Input)
    -> completes (both c1 c2) is
       =
       shorterOf <$> completes c1 is <*> completes c2 is

  lawCompletesClue
    :  (k : Clue) -> (c : Challenge) -> (is : List Input)
    -> completes (clue k c) is
       =
       completes c is

  lawCompletesGate
    :  (f : InputFilter) -> (c : Challenge) -> (i : Input) -> (is : List Input)
    -> matches f i = True
    -> completes (gate f c) (i :: is) = completes c is

  lawCompletesGateUnmatched
    : (f : InputFilter) -> (c : Challenge) -> (i : Input) -> (is : List Input)
    -> matches f i = False
    -> completes (gate f c) (i :: is) = completes (gate f c) is

  lawCompletesGateEmpty
    :  (f : InputFilter) -> (c : Challenge)
    -> completes (gate f c) [] = Nothing

  lawCompletesAndThen
    : (c1 , c2 : Challenge) -> (is : List Input)
    -> completes (andThen c1 c2)
       =
       completes c1 is >>= completes c2

  lawGetRewardsAndThen
    :  (c1 , c2 : Challenge) -> (is , is' : List Input)
    -> completes c1 is = Just is'
    -> getRewards (andThen c1 c2) is
       =
       getRewards c1 is <+> getRewards c2 is'

  lawGetRewardsAndThenIncomplete
    :  (c1 , c2 : Challenge) -> (is : List Input)
    -> completes c1 is = Nothing
    -> getRewards (andThen c1 c2) is
       =
       getRewards c1 is

  lawBothAndThenReward
    :  (r : Reward) -> (c1 , c2 : Challenge)
    -> both (andThen (reward r) c1) c2
       =
       andThen (reward r) (both c1 c2)

  eitherC : Challenge -> Challenge -> Challenge

  lawIsEmpty
    :  (c1 , c2 : Challenge)
    -> isEmpty (eitherC c1 c2) = isEmpty c1 && isEmpty c2

  lawEitherCAssociative
    :  (c1, c2, c3 : Challenge)
    -> eitherC c1 (eitherC c2 c3)
       =
       eitherC (eitherC c1 c2) c3

  lawEitherCCommutative
    :  (c1, c2 : Challenge)
    -> eitherC c1 c2 = eitherC c2 c1

  lawEitherC
    :  (r : Reward) -> (c1, c2 : Challenge)
    -> eitherC (andThen (reward r) c1) c2
       =
       andThen (reward r) (eitherC c1 c2)

  lawEitherCempty
    :  (c1 : Challenge)
    -> isReward c = False
    -> eitherC Empty c = Empty

  time : Time -> Input

  step : Clue -> Maybe Input -> Challenge -> (StepInfo, Challenge)
--  step : Clue -> Maybe Input -> Challenge -> ((Multiset Reward, MonoidalMap Clue ClueState), Challenge)

  lawIsEmptyStep
    :  (i : Maybe Input) -> (c1 , c2 : Challenge) -> (m : StepInfo) -> (k : Clue)
    -> step k i c1 = (m, c2)
    -> isEmpty c1 = True
    -> isEmpty c2 = True

  lawStepBoth
    :  (i : Maybe Input) -> (c1 , c2 : Challenge) -> (k : Clue)
    -> step k i (both c1 c2)
       =
       both <$> (step k i c1) <*> (step k i c2)

  lawStepEitherC
    :  (i : Maybe Input) -> (c1 , c2 : Challenge) -> (k : Clue)
    -> step k i (eitherC c1 c2)
       =
       eitherC <$> (step k i c1) <*> (step k i c2)

  lawStepEmpty
    :  (i : Maybe Input) -> (k : Clue)
    -> step k i Empty = (Prelude.neutral, Empty)

  lawStepReward
    :  (i : Maybe Input) -> (r : Reward) -> (k : Clue)
    -> step k i (reward r) = ((singleton r, Prelude.neutral), Empty)

  lawStepGate
    :  (i : Input) -> (f : InputFilter) -> (c : Challenge) -> (k : Clue)
    -> matches f i = True
    -> step k (Just i) (gate f c)
       =
       step k Nothing c

  lawStepGateUnmatched
    :  (i : Input) -> (f : InputFilter) -> (c : Challenge) -> (k : Clue)
    -> matches f i = False
    -> step k (Just i) (gate f c)
       =
       (Prelude.neutral, gate f c)

  lawStepGateNothing
    :  (f : InputFilter) -> (c : Challenge) -> (k : Clue)
    -> step k Nothing (gate f c)
       =
       (Prelude.neutral, gate f c)

  lawStepAndThenComplete
    :  (i : Maybe Input) -> (c1 , c2 : Challenge) -> (r : Reward) -> (k : Clue)
    -> step k i c1 = ((singleton r, Prelude.neutral), Empty)
    -> step k i (andThen c1 c2)
       =
       join ((singleton r, netural), step k Nothing c2)

  lawStepAndThenIncomplete
    :  (i : Maybe Input) -> (c1,c2,c3 : Challenge) -> (m : StepInfo) -> (k : Clue)
    -> step k i c1  = (m, c3)
    -> isEmpty c3 = True
    -> step k i (andThen c1 c2)
       =
       andThen <$> (step k i c1) <*> (pure c2)

  tellClue : MonoidalMap Clue ClueState -> (StepInfo, Challenge)

  lawStepClueEmpty
    :  (i : Maybe Input) -> (kctx, k : Clue)
    -> step kctx i (clue k Empty)
       =
       (tellClue (singletonMM (sub clueAlg kctx k) completed)) *>
       (pure Empty)

  lawStepClueNonEmpty
    :  (i : Maybe Input) -> (kctx, k : Clue) -> (c : Challenge)
    -> isEmpty c = False
    -> step kctx i (clue k c)
       =
       (tellClue (singletonMM (sub clueAlg kctx k) seen)) *>
       (clue k <$> (step (sub clueAlg kctx k) i c))

  runChallenge : Challenge -> List Input -> (StepInfo, Challenge)

  lawRunChallenge
    :  (c : Challenge) -> (is : List Input) -> (k : Clue)
    -> runChallenge c is
       =
       foldM (flip (step k)) c (Nothing :: map Just is)

  lawGetRewardsRunChallenge
    :  (c : Challenge) -> (is : List Input)
    -> getRewards c is
       =
       fst (fst (runChallenge c is))

  lawCompletes
    :  (c : Challenge) -> (is : List Input)
    -> Completes c is
       =
       IsEmpty (snd (runChallenge c is))

  getClues : Challenge -> List Input -> MonoidalMap Clue ClueState

  findClues : Clue -> Challenge -> MonoidalMap Clue ClueState

  seenToFailed : MonoidalMap Clue ClueState -> MonoidalMap Clue ClueState

  -- typos and missing variables leads to misterious type errors
  lawStepEitherCEmpty
    :  (kctx : Clue) -> (i : Maybe Input) -> (c1 , c2 , c2' : Challenge) -> (z1 , z2 : (Multiset Reward, MonoidalMap Clue ClueState))
 --   -> (step kctx i c1 == (z1, Empty) && step kctx i c2 == (z2, c2')) = True -- TODO: Can't find implementation
    -> step kctx i (eitherC c1 c2)
       =
       (pure (seenToFailed (findClues kctx c2'))) *>
       ((step kctx i c2) *> (step kctx i c1))
