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

class FiniteSet (Q : Type) [DecidableEq Q] where
  cardinality : Nat
  enumeration : Fin cardinality → Q
  enumeration_uniqueness : ∀ i j, enumeration i = enumeration j → i = j

structure TM Symbol (w : Nat) Q [DecidableEq Q]  [FiniteSet Q] where
  q_start : Q
  q_accept : Q
  q_reject : Q
  q_accept_ne_q_reject : q_accept ≠ q_reject
  transition : TransitionFunction Symbol w Q q_accept q_reject

inductive Decision w Q where
  | decided : Bool → Decision w Q
  | continuation : Configuration Symbol w Q -> Decision w Q

def TM.accepted [ DecidableEq Q ] [ FiniteSet Q ] (tm : TM Symbol w Q) (conf : Configuration Symbol w Q) : Prop :=
  tm.q_accept = conf.q

def TM.rejected [ DecidableEq Q ] [ FiniteSet Q ] (tm : TM Symbol w Q) (conf : Configuration Symbol w Q) : Prop :=
  tm.q_reject = conf.q

def TM.step [ DecidableEq Q ] [ FiniteSet Q ] (tm : TM Symbol w Q) (conf : Configuration Symbol  w Q) : Decision w Q :=
  if q_vs_q_accept : conf.q = tm.q_accept then
    .decided true
  else if q_vs_q_reject : conf.q = tm.q_reject then
    .decided false
  else
    let (write, q', dirs) := tm.transition (conf.read, ⟨ conf.q, ⟨ q_vs_q_accept, q_vs_q_reject ⟩ ⟩)
   .continuation (conf.update write q' dirs)

inductive reachesIn [ DecidableEq Q ] [ FiniteSet Q ] (tm : TM Symbol w Q)
  : Nat → Configuration Symbol w Q → Configuration Symbol w Q → Prop where
  | reached : reachesIn tm 0 conf conf
  | withStep :
      tm.step conf = .continuation conf'
      → reachesIn tm n conf' conf''
      → reachesIn tm (n + 1) conf conf''

def TM.initialConfiguration [ DecidableEq Q ] [ FiniteSet Q ] 
  (tm : TM Symbol w Q)
  (input : Fin n → Symbol) : Configuration Symbol w Q :=
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

def SymbolString Symbol n := Fin n → Symbol

def BitString n := SymbolString Bool n

def TM.acceptsIn [ DecidableEq Q ] [ FiniteSet Q ] (tm : TM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) : Prop :=
  ∃ conf', reachesIn tm steps (tm.initialConfiguration input) conf' ∧ tm.accepted conf'

def TM.rejectsIn [ DecidableEq Q ] [ FiniteSet Q ] (tm : TM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) : Prop :=
  ∃ conf', reachesIn tm steps (tm.initialConfiguration input) conf' ∧ tm.rejected conf'

def TM.haltsIn [ DecidableEq Q ] [ FiniteSet Q ] (tm : TM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) : Prop := acceptsIn tm steps input ∨ rejectsIn tm steps input

abbrev Language Symbol := ∀ n, SymbolString Symbol n → Prop

def TM.recognizesIn [ DecidableEq Q ] [ FiniteSet Q ]
  (tm : TM Symbol w Q)
  (L : Language Symbol)
  (T : Nat → Nat)
  := ∀ n s, L n s ↔ tm.acceptsIn (T n) s

def TM.coRecognizesIn [ DecidableEq Q ] [ FiniteSet Q ]
  (tm : TM Symbol w Q)
  (L : Language Symbol)
  (T : Nat → Nat)
  := ∀ n s, ¬ L n s ↔ tm.rejectsIn (T n) s

def TM.decidesIn [ DecidableEq Q ] [ FiniteSet Q ]
  (tm : TM Symbol w Q)
  (L : Language Symbol)
  (T : Nat → Nat)
  := tm.recognizesIn L T ∧ tm.coRecognizesIn L T

def TM.outputsIn [ DecidableEq Q ] [ FiniteSet Q ] (tm : TM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) (output : SymbolString Symbol m) : Prop :=
  ∃ conf',
    reachesIn tm steps (tm.initialConfiguration input) conf'
    ∧ tm.accepted conf'
    ∧ ∀ i : Nat, (h : i < m) → conf'.multitape.output (.ofNat i) = .symbol (output ⟨ i, h ⟩)

def TM.computesIn [ DecidableEq Q ] [ FiniteSet Q ]
  (tm : TM Symbol w Q)
  (f : ∀ n, SymbolString Symbol n → (m : Nat) × SymbolString Symbol m)
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

instance [DecidableEq Q] [DecidableEq Q'] [fsQ : FiniteSet Q] [fsQ' : FiniteSet Q'] :
  FiniteSet (CompositionState Q Q') where
    cardinality := fsQ.cardinality + fsQ'.cardinality + 1
    enumeration i :=
      if i_in_Q : i.1 < fsQ.cardinality then
        .P0 (fsQ.enumeration ⟨ i.1, by omega ⟩)
      else if i_in_Q' : i.1 < fsQ'.cardinality + fsQ.cardinality then
        .P1 (fsQ'.enumeration ⟨ i.1 - fsQ.cardinality, by omega ⟩)
      else
        .Rewind
    enumeration_uniqueness := by
      intros i j
      split
      split
      intros h
      injection h with h'
      have := fsQ.enumeration_uniqueness _ _ h'
      ext
      simp at this
      exact this
      split
      intros h
      injection h
      intros h
      grind
      split
      split
      grind
      split  
      intros h
      injection h with h'
      have := fsQ'.enumeration_uniqueness _ _ h'
      ext
      simp at this
      grind
      grind
      split
      intros h
      grind
      split
      grind
      grind

def TM.composition [ DecidableEq Q ] [ FiniteSet Q ] [ DecidableEq Q' ] [ FiniteSet Q' ]
  (tm0 : TM Symbol w Q) (tm1 : TM Symbol w' Q')
  : TM Symbol (w + w' + 1) (CompositionState Q Q') :=
  {
    q_start := .P0 tm0.q_start,
    q_accept := .P1 tm1.q_accept,
    q_reject := .Reject,
    q_accept_ne_q_reject := by grind,
    transition := λ (reads, q) ↦
      match q.1 with
      | .P0 q1 => sorry
      | .Rewind => sorry
      | .P1 q2 => sorry
      | .Reject => sorry
  }
