structure Multi (w : Nat) A (B := A) where
  input : A
  work : Fin w → A
  output : B

inductive Dir where
  | left : Dir
  | stay : Dir
  | right : Dir

def Dir.movement (d : Dir) : Int :=
  match d with
  | .left => -1
  | .stay => 0
  | .right => 1

inductive Alphabet Symbol where
  | blank : Alphabet Symbol
  | symbol : Symbol → Alphabet Symbol
  deriving DecidableEq

def stays : Multi w Dir { d : Dir // d ≠ .left } :=
  { input := .stay,
    work := λ _ ↦ .stay,
    output := ⟨ .stay, by grind ⟩
  }

abbrev TransitionFunction (Symbol : Type) (w : Nat) Q q_accept q_reject :=
  Multi w (Alphabet Symbol) × { q : Q // q ≠ q_accept ∧ q ≠ q_reject }
    → Multi w (Alphabet Symbol) × Q × Multi w Dir { d : Dir // d ≠ Dir.left }

abbrev Tape Symbol := Int → Alphabet Symbol

structure Configuration Symbol (w : Nat) Q where
  multitape : Multi w (Tape Symbol)
  indices : Multi w Int
  q : Q

def Configuration.read (conf : Configuration Symbol w Q) : Multi w (Alphabet Symbol) :=
  {
    input := conf.multitape.input conf.indices.input,
    work := λ i ↦ conf.multitape.work i (conf.indices.work i),
    output := conf.multitape.output conf.indices.output
  }

def fupdate {α : Sort u} {β : α → Sort v} [DecidableEq α] (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

notation f "[" a' " ↦ " v "]" => fupdate f a' v

def Configuration.update (conf : Configuration Symbol w Q) (write : Multi w (Alphabet Symbol)) (q' : Q) (dirs : Multi w Dir { d : Dir // d ≠ Dir.left} ) : Configuration Symbol w Q :=
  { 
    multitape := {
      input := conf.multitape.input[conf.indices.input ↦ write.input],
      work := λ i ↦ (conf.multitape.work i)[ (conf.indices.work i) ↦ write.work i],
      output := conf.multitape.output[conf.indices.output ↦ write.output],
    },
    indices := {
      input := conf.indices.input + dirs.input.movement,
      work := λ i ↦ conf.indices.work i + (dirs.work i).movement,
      output := conf.indices.output + dirs.output.1.movement
    },
    q := q',
  }

class Bijection (A : Type) (B : Type) where
  forward : A → B
  backward : B → A
  left_inv : ∀ b, forward (backward b) = b
  right_inv : ∀ a, backward (forward a) = a

class NonEmptyFiniteSet (Q : Type) [DecidableEq Q] where
  cardinality : Nat
  cardinality_ne_zero : cardinality ≠ 0
  bijection : Bijection Q (Fin cardinality)

structure TM Symbol (w : Nat) Q [DecidableEq Q]  [NonEmptyFiniteSet Q] where
  q_start : Q
  q_accept : Q
  q_reject : Q
  q_accept_ne_q_reject : q_accept ≠ q_reject
  transition : TransitionFunction Symbol w Q q_accept q_reject

inductive Decision w Q where
  | decided : Bool → Decision w Q
  | continuation : Configuration Symbol w Q → Decision w Q

def TM.accepted [ DecidableEq Q ] [ NonEmptyFiniteSet Q ] (tm : TM Symbol w Q) (conf : Configuration Symbol w Q) : Prop :=
  tm.q_accept = conf.q

def TM.rejected [ DecidableEq Q ] [ NonEmptyFiniteSet Q ] (tm : TM Symbol w Q) (conf : Configuration Symbol w Q) : Prop :=
  tm.q_reject = conf.q

def TM.step [ DecidableEq Q ] [ NonEmptyFiniteSet Q ] (tm : TM Symbol w Q) (conf : Configuration Symbol  w Q) : Decision w Q :=
  if q_vs_q_accept : conf.q = tm.q_accept then
    .decided true
  else if q_vs_q_reject : conf.q = tm.q_reject then
    .decided false
  else
    let (write, q', dirs) := tm.transition (conf.read, ⟨ conf.q, ⟨ q_vs_q_accept, q_vs_q_reject ⟩ ⟩)
   .continuation (conf.update write q' dirs)

inductive reachesIn [ DecidableEq Q ] [ NonEmptyFiniteSet Q ] (tm : TM Symbol w Q)
  : Nat → Configuration Symbol w Q → Configuration Symbol w Q → Prop where
  | reached : reachesIn tm 0 conf conf
  | withStep :
      tm.step conf = .continuation conf'
      → reachesIn tm n conf' conf''
      → reachesIn tm (n + 1) conf conf''

def SymbolString Symbol n := Fin n → Symbol

def BitString n := SymbolString Bool n

def TM.initialConfiguration [ DecidableEq Q ] [ NonEmptyFiniteSet Q ] 
  (tm : TM Symbol w Q)
  (input : SymbolString Symbol n) : Configuration Symbol w Q :=
  {
    multitape := {
      input := λ i ↦ match i with
                     | .ofNat i => if i_le_n : i < n then .symbol (input ⟨ i, i_le_n ⟩) else .blank
                     | .negSucc _ => .blank
      work := λ _ _ ↦ .blank,
      output := λ _ ↦ .blank,
    },
    indices := {
      input := 0,
      work := λ _ ↦ 0,
      output := 0,
    },
    q := tm.q_start
  }

def TM.acceptsIn [ DecidableEq Q ] [ NonEmptyFiniteSet Q ] (tm : TM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) : Prop :=
  ∃ steps', steps' ≤ steps ∧ ∃ conf', reachesIn tm steps' (tm.initialConfiguration input) conf' ∧ tm.accepted conf'

def TM.rejectsIn [ DecidableEq Q ] [ NonEmptyFiniteSet Q ] (tm : TM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) : Prop :=
  ∃ steps', steps' ≤ steps ∧ ∃ conf', reachesIn tm steps' (tm.initialConfiguration input) conf' ∧ tm.rejected conf'

def TM.haltsIn [ DecidableEq Q ] [ NonEmptyFiniteSet Q ] (tm : TM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) : Prop := acceptsIn tm steps input ∨ rejectsIn tm steps input

abbrev Language Symbol := ∀ n, SymbolString Symbol n → Prop

def TM.recognizesIn [ DecidableEq Q ] [ NonEmptyFiniteSet Q ]
  (tm : TM Symbol w Q)
  (L : Language Symbol)
  (T : Nat → Nat)
  := ∀ n s, L n s ↔ tm.acceptsIn (T n) s

def TM.coRecognizesIn [ DecidableEq Q ] [ NonEmptyFiniteSet Q ]
  (tm : TM Symbol w Q)
  (L : Language Symbol)
  (T : Nat → Nat)
  := ∀ n s, ¬ L n s ↔ tm.rejectsIn (T n) s

def TM.decidesIn [ DecidableEq Q ] [ NonEmptyFiniteSet Q ]
  (tm : TM Symbol w Q)
  (L : Language Symbol)
  (T : Nat → Nat)
  := tm.recognizesIn L T ∧ tm.coRecognizesIn L T

def TM.outputsIn [ DecidableEq Q ] [ NonEmptyFiniteSet Q ] (tm : TM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) (output : SymbolString Symbol m) : Prop :=
  ∃ steps', steps' ≤ steps ∧ ∃ conf',
    reachesIn tm steps' (tm.initialConfiguration input) conf'
    ∧ tm.accepted conf'
    ∧ ∀ i : Nat, ((h : i < m) → conf'.multitape.output (.ofNat i) = .symbol (output ⟨ i, h ⟩))
                  ∧ ((h : i ≥ m) → conf'.multitape.output (.ofNat i) = .blank)

abbrev SymbolStringFunction Symbol := ∀ n, SymbolString Symbol n → (m : Nat) × SymbolString Symbol m

def SymbolStringFunction.comp (g f : SymbolStringFunction Symbol) : SymbolStringFunction Symbol :=
  λ n input ↦ g (f n input).1 (f n input).2

infixr:90 " ⊚ " => SymbolStringFunction.comp

def TM.computesIn [ DecidableEq Q ] [ NonEmptyFiniteSet Q ]
  (tm : TM Symbol w Q)
  (f : SymbolStringFunction Symbol)
  (T : Nat → Nat)
  := ∀ n input, tm.outputsIn (T n) input (f n input).2

inductive CompositionState Q Q' where
  /- First, we execute the first program, treating an extra work tape as an output tape. 
     If it rejects, we short-circuit and reject as well.
  -/
  | P0 : Q → CompositionState Q Q'
  /- Then, we rewind that work tape to the beginning, as if it is the input tape. -/
  | Rewind : CompositionState Q Q'
  /- Finally, we run the second program. If it rejects, we reject as well. If it accepts,
     we accept.
  -/
  | P1 : Q' → CompositionState Q Q'
  /- We use a shared rejection state, as we have a single rejection state in our definition of
     Turing machine.
  -/
  | Reject : CompositionState Q Q'
  deriving DecidableEq

instance [DecidableEq Q] [DecidableEq Q'] [fsQ : NonEmptyFiniteSet Q] [fsQ' : NonEmptyFiniteSet Q'] :
  NonEmptyFiniteSet (CompositionState Q Q') where
    cardinality := fsQ.cardinality + fsQ'.cardinality + 2
    cardinality_ne_zero := by omega
    bijection :=
      let fwd : CompositionState Q Q' → Fin (fsQ.cardinality + fsQ'.cardinality + 2) := fun
        | .P0 q => ⟨fsQ.bijection.forward q, by omega⟩
        | .P1 q' => ⟨fsQ.cardinality + (fsQ'.bijection.forward q'), by omega⟩
        | .Rewind => ⟨fsQ.cardinality + fsQ'.cardinality, by omega⟩
        | .Reject => ⟨fsQ.cardinality + fsQ'.cardinality + 1, by omega⟩
      let bwd : Fin (fsQ.cardinality + fsQ'.cardinality + 2) → CompositionState Q Q' := fun ⟨i, _⟩ =>
        if h : i < fsQ.cardinality then
          .P0 (fsQ.bijection.backward ⟨i, h⟩)
        else if h' : i < fsQ.cardinality + fsQ'.cardinality then
          .P1 (fsQ'.bijection.backward ⟨i - fsQ.cardinality, by omega⟩)
        else if _ : i = fsQ.cardinality + fsQ'.cardinality then
          .Rewind
        else
          .Reject
      { forward := fwd
        backward := bwd
        left_inv := by
          intro ⟨i, hi⟩
          dsimp only [bwd]
          split
          · dsimp only [fwd]; ext; simp [fsQ.bijection.left_inv]
          · split
            · dsimp only [fwd]; ext; simp [fsQ'.bijection.left_inv]; omega
            · split
              · dsimp only [fwd]; ext; simp_all
              · dsimp only [fwd]; ext; simp; omega
        right_inv := by
          intro x
          dsimp only [bwd, fwd]
          cases x with
          | P0 q =>
            simp [(fsQ.bijection.forward q).2, fsQ.bijection.right_inv]
          | P1 q' =>
            simp [show ¬ fsQ.cardinality + fsQ'.bijection.forward q' < fsQ.cardinality by omega,
                  show fsQ.cardinality + fsQ'.bijection.forward q' < fsQ.cardinality + fsQ'.cardinality by omega,
                  show fsQ.cardinality + fsQ'.bijection.forward q' - fsQ.cardinality = fsQ'.bijection.forward q' by omega,
                  fsQ'.bijection.right_inv]
          | Rewind =>
            simp [show ¬ fsQ.cardinality + fsQ'.cardinality < fsQ.cardinality by omega,
                  show ¬ fsQ.cardinality + fsQ'.cardinality < fsQ.cardinality + fsQ'.cardinality by omega]
          | Reject =>
            simp [show ¬ fsQ.cardinality + fsQ'.cardinality + 1 < fsQ.cardinality by omega,
                  show ¬ fsQ.cardinality + fsQ'.cardinality + 1 < fsQ.cardinality + fsQ'.cardinality by omega]
      }

def TM.composition
  [ Inhabited Symbol ]
  [ DecidableEq Q ] [ DecidableEq Q' ]
  [ NonEmptyFiniteSet Q ] [ NonEmptyFiniteSet Q' ]
  (tm0 : TM Symbol w Q) (tm1 : TM Symbol w' Q')
  : TM
      Symbol
      (w + w' + 2)
      (CompositionState Q Q')
  :=
  {
    q_start := .P0 tm0.q_start,
    q_accept := .P1 tm1.q_accept,
    q_reject := .Reject,
    q_accept_ne_q_reject := by grind,
    transition := λ (reads, q) ↦
      match h_q : q.1 with
      | .P0 q1 =>
        if h_acc : tm0.q_accept = q1 then
          (markCounter reads, .Rewind, stays)
        else if h_rej : tm0.q_reject = q1 then
          (reads, .Reject, stays)
        else
          let (write, q', dirs) :=
            tm0.transition (projectForTm0 reads, ⟨q1, ⟨Ne.symm h_acc, Ne.symm h_rej⟩⟩)
          (embedTm0Write reads write, .P0 q', embedTm0Dirs dirs)
      | .Rewind =>
        match reads.work counterTape with
        | .blank => (reads, .P1 tm1.q_start, moveIntermediateAndCounter .right)
        | .symbol _ => (reads, .Rewind, moveIntermediateAndCounter .left)
      | .P1 q2 =>
        if h_rej : tm1.q_reject = q2 then
          (reads, .Reject, stays)
        else
          have h_ne_acc : q2 ≠ tm1.q_accept := by
            intro h; subst h; exact q.2.1 h_q
          let (write, q', dirs) :=
            tm1.transition (projectForTm1 reads, ⟨q2, ⟨h_ne_acc, Ne.symm h_rej⟩⟩)
          (embedTm1Write reads write, .P1 q', embedTm1Dirs dirs)
      | .Reject => absurd h_q q.2.2
  }
where
  intermediateTape : Fin (w + w' + 2) := ⟨w, by omega⟩
  counterTape : Fin (w + w' + 2) := ⟨w + 1, by omega⟩
  markCounter (reads : Multi (w + w' + 2) (Alphabet Symbol))
      : Multi (w + w' + 2) (Alphabet Symbol) :=
    { reads with work := reads.work[counterTape ↦ .symbol default] }
  projectForTm0 (reads : Multi (w + w' + 2) (Alphabet Symbol))
      : Multi w (Alphabet Symbol) :=
    { input := reads.input,
      work := λ i ↦ reads.work ⟨i, by omega⟩,
      output := reads.work intermediateTape }
  projectForTm1 (reads : Multi (w + w' + 2) (Alphabet Symbol))
      : Multi w' (Alphabet Symbol) :=
    { input := reads.work intermediateTape,
      work := λ i ↦ reads.work ⟨w + 2 + i, by omega⟩,
      output := reads.output }
  embedTm0Write (reads : Multi (w + w' + 2) (Alphabet Symbol))
      (write : Multi w (Alphabet Symbol)) : Multi (w + w' + 2) (Alphabet Symbol) :=
    { input := write.input,
      work := λ i ↦
        if h : i < w then write.work ⟨i.1, h⟩
        else if i = w then write.output
        /- also mark the counter to ensure we're keeping it in sync with the output tape's
          position. -/
        else if i = w + 1 then .symbol default
        /- tm1's work tapes are inactive during tm0 -/
        else reads.work i,
      /- tm1's output tape is inactive during tm0 -/
      output := reads.output }
  embedTm0Dirs (dirs : Multi w Dir { d : Dir // d ≠ Dir.left })
      : Multi (w + w' + 2) Dir { d : Dir // d ≠ Dir.left } :=
    { input := dirs.input,
      work := λ i ↦
        if h : i < w then dirs.work ⟨i, h⟩
        else if i = w then dirs.output
        /- move the counter with the output direction to ensure it stays
           synced up. -/
        else if i = w + 1 then dirs.output
        /- tm1's work tapes are inactive during tm0 -/
        else Dir.stay,
      /- tm1's work tapes are inactive during tm0 -/
      output := ⟨Dir.stay, by grind⟩ }
  embedTm1Write (reads : Multi (w + w' + 2) (Alphabet Symbol))
      (write : Multi w' (Alphabet Symbol)) : Multi (w + w' + 2) (Alphabet Symbol) :=
    { input := reads.input,
      work := λ i ↦
        /- tm0's tapes are inactive during tm1 -/
        if h₁ : i < w then reads.work i
        else if _ : i = w then write.input
        /- the counter tape is inactive during tm1 -/
        else if _ : i = w + 1 then reads.work i
        else write.work ⟨i - (w + 2), by omega⟩,
      output := write.output }
  embedTm1Dirs (dirs : Multi w' Dir { d : Dir // d ≠ Dir.left })
      : Multi (w + w' + 2) Dir { d : Dir // d ≠ Dir.left } :=
    { input := .stay,
      work := λ i ↦
        /- tm0's work tapes are inactive during tm1 -/
        if h₁ : i < w then Dir.stay
        /- tm0's output tape is the input tape of tm1 -/
        else if _ : i = w then dirs.input
        /- the counter tape is inactive during tm1 -/
        else if _ : i = w + 1 then Dir.stay
        /- tm1's work tapes are in the latter half of the tape -/
        else dirs.work ⟨i - (w + 2), by omega⟩,
      output := dirs.output }
  moveIntermediateAndCounter (dir : Dir) : Multi (w + w' + 2) Dir { d : Dir // d ≠ Dir.left } :=
    { input := .stay,
      work := λ i ↦ if i = w ∨ i = w + 1 then dir else Dir.stay,
      output := ⟨Dir.stay, by grind⟩ }

theorem composition_correctness
  [ Inhabited Symbol ]
  [ DecidableEq Q ] [ DecidableEq Q' ]
  [ NonEmptyFiniteSet Q ] [ NonEmptyFiniteSet Q' ]
  (tm0 : TM Symbol w Q) (tm1 : TM Symbol w' Q')
  (f0 f1 : SymbolStringFunction Symbol)
  (T0 T1 : Nat → Nat)
  (hT1_mono : ∀ {a b}, a ≤ b → T1 a ≤ T1 b)
  : TM.computesIn tm0 f0 T0 ∧ TM.computesIn tm1 f1 T1
      → TM.computesIn (TM.composition tm0 tm1) (f1 ⊚ f0) (λ n ↦ 2 * T0 n + T1 (T0 n) + 3)
  := sorry
