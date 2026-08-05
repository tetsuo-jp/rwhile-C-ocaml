{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- A TIMED (cost-annotated) semantics for the R-WHILE core, and an
-- executable fuel-indexed evaluator agreeing with it.
--
-- This is the base layer of the "linear-time self-interpreter" theorem
-- (Glück & Yokoyama, *A linear-time self-interpreter of a reversible
-- imperative language*).  To speak about TIME at all we need a cost
-- model; it is fixed here to be the one the implementation measures
-- (`src/EvalRwhile.ml`: `incr eval_steps` once per `evalCom` call, i.e.
-- unit cost per EXECUTED COMMAND NODE, expressions free -- the model of
-- `./ri -steps` and `examples/measure_ri_overhead.sh`).
--
--   * values          `V`      = nil | atom n | (u . v)          (src/AbsRwhile.ml valT)
--   * store           `Store`  = list of values, `get`/`set` by index
--   * expressions     flat: operands are variables or constants
--   * commands        skip | x ^= e | c ; d | if/fi | from/loop/until
--   * cost relation   `c ⊢ s ⇒ t ∣ k`  -- k = number of command nodes executed
--   * executable      `exec : ℕ → Cmd → Store → Maybe (Store × ℕ)` (fuel)
--                     `exec-sound` lifts a COMPUTED run to a derivation, which is
--                     what makes the self-interpreter's straight-line fragments
--                     provable by `refl` in RWhileSIStep.
--
-- SCOPE.  Expressions are FLAT (operands = variable or constant), as in a
-- reversible core / three-address IL; the surface language's nested
-- expressions and pattern replacement `<=` are not modelled here (see
-- RWhileCoreExp / RWhileCRep for those layers).  All four reversible control
-- constructs are modelled exactly as in EvalRwhile.ml, including the exit
-- assertion of the conditional and the loop's reversibility assertions.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileTime where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

------------------------------------------------------------------------
-- Values (src/AbsRwhile.ml: VNil / VAtom / VCons)

infixr 6 _∙_
data V : Set where
  nil : V
  atm : ℕ → V
  _∙_ : V → V → V

-- boolean equality on values (R-WHILE's `=?`), and the truth convention
-- (false = nil, true = anything else; the canonical true is (nil.nil)).

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

eqℕ-refl : ∀ n → eqℕ n n ≡ true
eqℕ-refl zero    = refl
eqℕ-refl (suc n) = eqℕ-refl n

eqV : V → V → Bool
eqV nil     nil     = true
eqV nil     _       = false
eqV (atm _) nil     = false
eqV (atm m) (atm n) = eqℕ m n
eqV (atm _) (_ ∙ _) = false
eqV (_ ∙ _) nil     = false
eqV (_ ∙ _) (atm _) = false
eqV (a ∙ b) (c ∙ d) = if eqV a c then eqV b d else false

eqV-refl : ∀ v → eqV v v ≡ true
eqV-refl nil     = refl
eqV-refl (atm n) = eqℕ-refl n
eqV-refl (a ∙ b) rewrite eqV-refl a = eqV-refl b

-- `=?` returns the canonical booleans (nil.nil) / nil
boolV : Bool → V
boolV true  = nil ∙ nil
boolV false = nil

isTrue : V → Bool
isTrue nil = false
isTrue _   = true

isTrue-boolV : ∀ b → isTrue (boolV b) ≡ b
isTrue-boolV true  = refl
isTrue-boolV false = refl

------------------------------------------------------------------------
-- Stores.  A store is a list of values indexed by variable number;
-- reading past the end gives nil, writing past the end extends with nils.

Store : Set
Store = List V

get : Store → ℕ → V
get []       _       = nil
get (v ∷ _)  zero    = v
get (_ ∷ vs) (suc n) = get vs n

set : Store → ℕ → V → Store
set []       zero    v = v ∷ []
set []       (suc n) v = nil ∷ set [] n v
set (_ ∷ vs) zero    v = v ∷ vs
set (u ∷ vs) (suc n) v = u ∷ set vs n v

------------------------------------------------------------------------
-- Syntax.  Flat expressions: operands are variables or constants.

data Opd : Set where
  var : ℕ → Opd
  cst : V → Opd

data Exp : Set where
  opd : Opd → Exp             -- X   /  'a  /  nil
  cns : Opd → Opd → Exp       -- cons A B
  hdE : Opd → Exp             -- hd A
  tlE : Opd → Exp             -- tl A
  eqE : Opd → Opd → Exp       -- =? A B
  prE : Opd → Exp             -- pair? A   (cons test, like src/EvalRwhile.ml)

infix 4 _^=_
infixr 3 _⨾_

data Cmd : Set where
  skip : Cmd
  _^=_ : ℕ → Exp → Cmd                  -- reversible (XOR) assignment
  _⨾_  : Cmd → Cmd → Cmd
  cond : Exp → Cmd → Cmd → Exp → Cmd    -- if e then C else D fi f
  loop : Exp → Cmd → Cmd → Exp → Cmd    -- from e do D loop L until f

------------------------------------------------------------------------
-- Expression evaluation (partial: hd/tl of a non-cons is an error).

evalO : Store → Opd → V
evalO s (var x) = get s x
evalO s (cst v) = v

hdM : V → Maybe V
hdM (u ∙ _) = just u
hdM _       = nothing

tlM : V → Maybe V
tlM (_ ∙ v) = just v
tlM _       = nothing

-- the cons test of `pair? E`: (nil.nil) for a cons cell, nil otherwise
isCons : V → Bool
isCons (_ ∙ _) = true
isCons _       = false

evalE : Store → Exp → Maybe V
evalE s (opd a)   = just (evalO s a)
evalE s (cns a b) = just (evalO s a ∙ evalO s b)
evalE s (hdE a)   = hdM (evalO s a)
evalE s (tlE a)   = tlM (evalO s a)
evalE s (eqE a b) = just (boolV (eqV (evalO s a) (evalO s b)))
evalE s (prE a)   = just (boolV (isCons (evalO s a)))

-- the truth value of a test
evalT : Store → Exp → Maybe Bool
evalT s e with evalE s e
... | just v  = just (isTrue v)
... | nothing = nothing

------------------------------------------------------------------------
-- The reversible update `x ^= e` (src/EvalRwhile.ml `rupdate`), all THREE
-- cases of it, in the implementation's order:
--
--   1. the variable is nil          -> set it
--   2. the value equals the current -> clear it
--   3. the value is nil             -> identity (XOR with 0)
--   otherwise                       -> run-time error
--
-- The third case is easy to miss: the papers' (+) has only two (Gluck &
-- Yokoyama, Computer Software 33(3), 2016, Eq.(8); the R-CORE paper, IEICE
-- E100-D(5), 2017, Eq.(1)).  It was dropped here once already -- see
-- AGDA_CORRESPONDENCE.md -- and it is not decoration: `examples/ri.rwhile`
-- needs it for the disjunction idiom
-- `Flag ^= =? Tag 'l4E; Flag ^= =? Tag 'loop`, so a two-case model does not
-- cover the very self-interpreter this layer is about.
--
-- Case 3 is appended INSIDE the two non-nil clauses rather than hoisted to a
-- leading `rupd w nil = just w`.  Hoisting would stop `rupd nil v` from
-- reducing for an open `v`, and dozens of proofs downstream (RWhileSIMac,
-- RWhileSIStep, RWhileSIEval) close goals of the form
-- `rupd nil <open value> ≡ just _` by `refl`.

rupd : V → V → Maybe V
rupd nil     v = just v
rupd (atm m) v = if eqV (atm m) v then just nil
                 else if eqV v nil then just (atm m) else nothing
rupd (a ∙ b) v = if eqV (a ∙ b) v then just nil
                 else if eqV v nil then just (a ∙ b) else nothing

-- assigning nil never fails and never changes the variable (case 3)
rupd-nil : ∀ w → rupd w nil ≡ just w
rupd-nil nil     = refl
rupd-nil (atm n) = refl
rupd-nil (a ∙ b) = refl

-- assigning a variable its own current value clears it
rupd-self : ∀ v → rupd v v ≡ just nil
rupd-self nil     = refl
rupd-self (atm n) rewrite eqℕ-refl n = refl
rupd-self (a ∙ b) rewrite eqV-refl a | eqV-refl b = refl

------------------------------------------------------------------------
-- Timed big-step semantics.  `c ⊢ s ⇒ t ∣ k` : running c on s yields t and
-- executes k command nodes -- exactly `eval_steps` of src/EvalRwhile.ml.

infix 3 _⊢_⇒_∣_

data _⊢_⇒_∣_ : Cmd → Store → Store → ℕ → Set
data Rest (e : Exp) (D L : Cmd) (f : Exp) : Store → Store → ℕ → Set

data _⊢_⇒_∣_ where
  e-skip : ∀ {s} → skip ⊢ s ⇒ s ∣ 1
  e-ass  : ∀ {x e s v u}
         → evalE s e ≡ just v
         → rupd (get s x) v ≡ just u
         → (x ^= e) ⊢ s ⇒ set s x u ∣ 1
  e-seq  : ∀ {c d s t u k l}
         → c ⊢ s ⇒ t ∣ k → d ⊢ t ⇒ u ∣ l
         → (c ⨾ d) ⊢ s ⇒ u ∣ suc (k + l)
  e-then : ∀ {e c d f s t k}
         → evalT s e ≡ just true → c ⊢ s ⇒ t ∣ k → evalT t f ≡ just true
         → cond e c d f ⊢ s ⇒ t ∣ suc k
  e-else : ∀ {e c d f s t k}
         → evalT s e ≡ just false → d ⊢ s ⇒ t ∣ k → evalT t f ≡ just false
         → cond e c d f ⊢ s ⇒ t ∣ suc k
  e-loop : ∀ {e D L f s t u k n}
         → evalT s e ≡ just true → D ⊢ s ⇒ t ∣ k → Rest e D L f t u n
         → loop e D L f ⊢ s ⇒ u ∣ suc (k + n)

data Rest e D L f where
  r-exit : ∀ {w} → evalT w f ≡ just true → Rest e D L f w w 0
  r-iter : ∀ {w x y z k m n}
         → evalT w f ≡ just false
         → L ⊢ w ⇒ x ∣ k
         → evalT x e ≡ just false
         → D ⊢ x ⇒ y ∣ m
         → Rest e D L f y z n
         → Rest e D L f w z (k + m + n)

------------------------------------------------------------------------
-- An executable, fuel-indexed evaluator, and its soundness.  This is the
-- workhorse: a concrete straight-line fragment of the self-interpreter is
-- RUN by `exec` (which computes, since the code and the inspected tags are
-- concrete) and the resulting equation is lifted to a derivation.

infixl 1 _>>=M_
_>>=M_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>=M f = f a
nothing >>=M _ = nothing

bind-inv : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b}
         → (m >>=M f) ≡ just b → Σ[ a ∈ A ] (m ≡ just a) × (f a ≡ just b)
bind-inv (just a) f eq = a , refl , eq

exec  : ℕ → Cmd → Store → Maybe (Store × ℕ)
execR : ℕ → Exp → Cmd → Cmd → Exp → Store → Maybe (Store × ℕ)

exec zero    _              _ = nothing
exec (suc n) skip           s = just (s , 1)
exec (suc n) (x ^= e)       s =
  evalE s e >>=M λ v → rupd (get s x) v >>=M λ u → just (set s x u , 1)
exec (suc n) (c ⨾ d)        s =
  exec n c s >>=M λ tk → exec n d (proj₁' tk) >>=M λ ul →
  just (proj₁' ul , suc (proj₂' tk + proj₂' ul))
  where
    proj₁' : Store × ℕ → Store
    proj₁' (t , _) = t
    proj₂' : Store × ℕ → ℕ
    proj₂' (_ , k) = k
exec (suc n) (cond e c d f) s =
  evalT s e >>=M λ b →
  if b then (exec n c s >>=M λ tk → evalT (fst tk) f >>=M λ b′ →
             if b′ then just (fst tk , suc (snd tk)) else nothing)
       else (exec n d s >>=M λ tk → evalT (fst tk) f >>=M λ b′ →
             if b′ then nothing else just (fst tk , suc (snd tk)))
  where
    fst : Store × ℕ → Store
    fst (t , _) = t
    snd : Store × ℕ → ℕ
    snd (_ , k) = k
exec (suc n) (loop e D L f) s =
  evalT s e >>=M λ b →
  if b then (exec n D s >>=M λ tk → execR n e D L f (fst tk) >>=M λ um →
             just (fst um , suc (snd tk + snd um)))
       else nothing
  where
    fst : Store × ℕ → Store
    fst (t , _) = t
    snd : Store × ℕ → ℕ
    snd (_ , k) = k

execR zero    _ _ _ _ _ = nothing
execR (suc n) e D L f w =
  evalT w f >>=M λ b →
  if b then just (w , 0)
       else (exec n L w >>=M λ xk → evalT (fst xk) e >>=M λ b′ →
             if b′ then nothing
                   else (exec n D (fst xk) >>=M λ ym →
                         execR n e D L f (fst ym) >>=M λ zr →
                         just (fst zr , snd xk + snd ym + snd zr)))
  where
    fst : Store × ℕ → Store
    fst (t , _) = t
    snd : Store × ℕ → ℕ
    snd (_ , k) = k

------------------------------------------------------------------------
-- exec-sound : a computed run IS a derivation (with the same cost).

exec-sound  : ∀ n c s t k → exec n c s ≡ just (t , k) → c ⊢ s ⇒ t ∣ k
execR-sound : ∀ n e D L f w z r → execR n e D L f w ≡ just (z , r) → Rest e D L f w z r

exec-sound (suc n) skip s t k eq with eq
... | refl = e-skip
exec-sound (suc n) (x ^= e) s t k eq
  with bind-inv (evalE s e) _ eq
... | v , ev , eq₁ with bind-inv (rupd (get s x) v) _ eq₁
...   | u , ru , refl = e-ass ev ru
exec-sound (suc n) (c ⨾ d) s t k eq
  with bind-inv (exec n c s) _ eq
... | (s₁ , k₁) , ec , eq₁ with bind-inv (exec n d s₁) _ eq₁
...   | (s₂ , k₂) , ed , refl =
        e-seq (exec-sound n c s s₁ k₁ ec) (exec-sound n d s₁ s₂ k₂ ed)
exec-sound (suc n) (cond e c d f) s t k eq
  with bind-inv (evalT s e) _ eq
... | true , et , eq₁ with bind-inv (exec n c s) _ eq₁
...   | (s₁ , k₁) , ec , eq₂ with bind-inv (evalT s₁ f) _ eq₂
...     | true  , ef , refl = e-then et (exec-sound n c s s₁ k₁ ec) ef
exec-sound (suc n) (cond e c d f) s t k eq
    | false , et , eq₁ with bind-inv (exec n d s) _ eq₁
...   | (s₁ , k₁) , ed , eq₂ with bind-inv (evalT s₁ f) _ eq₂
...     | false , ef , refl = e-else et (exec-sound n d s s₁ k₁ ed) ef
exec-sound (suc n) (loop e D L f) s t k eq
  with bind-inv (evalT s e) _ eq
... | true , et , eq₁ with bind-inv (exec n D s) _ eq₁
...   | (s₁ , k₁) , ed , eq₂ with bind-inv (execR n e D L f s₁) _ eq₂
...     | (s₂ , k₂) , er , refl =
          e-loop et (exec-sound n D s s₁ k₁ ed) (execR-sound n e D L f s₁ s₂ k₂ er)

execR-sound (suc n) e D L f w z r eq
  with bind-inv (evalT w f) _ eq
... | true  , ef , refl = r-exit ef
... | false , ef , eq₁ with bind-inv (exec n L w) _ eq₁
...   | (s₁ , k₁) , el , eq₂ with bind-inv (evalT s₁ e) _ eq₂
...     | false , ee , eq₃ with bind-inv (exec n D s₁) _ eq₃
...       | (s₂ , k₂) , ed , eq₄ with bind-inv (execR n e D L f s₂) _ eq₄
...         | (s₃ , k₃) , er , refl =
              r-iter ef (exec-sound n L w s₁ k₁ el) ee
                     (exec-sound n D s₁ s₂ k₂ ed)
                     (execR-sound n e D L f s₂ s₃ k₃ er)

------------------------------------------------------------------------
-- Every executed command costs at least one step (used to turn additive
-- constants into multiplicative ones in the linear-overhead theorem).

cost-pos : ∀ {c s t k} → c ⊢ s ⇒ t ∣ k → 1 ≤ k
cost-pos e-skip         = s≤s z≤n
cost-pos (e-ass _ _)    = s≤s z≤n
cost-pos (e-seq _ _)    = s≤s z≤n
cost-pos (e-then _ _ _) = s≤s z≤n
cost-pos (e-else _ _ _) = s≤s z≤n
cost-pos (e-loop _ _ _) = s≤s z≤n
