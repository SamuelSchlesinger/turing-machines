structure Multi (w : Nat) A where
  input : A
  work : Fin w → A
  output : A

inductive Dir where
  | left : Dir
  | stay : Dir
  | right : Dir

def Dir.movement (d : Dir) : Int :=
  match d with
  | .left => -1
  | .stay => 0
  | .right => 1

inductive Alphabet α Symbol where
  | blank : α → Alphabet α Symbol
  | symbol : Symbol → Alphabet α Symbol
  deriving DecidableEq

abbrev WriteAlphabet Symbol := Alphabet Empty Symbol

abbrev ReadAlphabet Symbol := Alphabet Unit Symbol

def WriteAlphabet.toRead (w : WriteAlphabet Symbol) : ReadAlphabet Symbol :=
  match w with
  | .blank a => nomatch a
  | .symbol x => Alphabet.symbol x

abbrev TransitionFunction (Symbol : Type) (w : Nat) Q q_accept q_reject :=
  Multi w (ReadAlphabet Symbol) × { q : Q // q ≠ q_accept ∧ q ≠ q_reject }
    → Multi w (WriteAlphabet Symbol) × Q × Multi w Dir

abbrev Tape Symbol := Int → ReadAlphabet Symbol

structure Configuration Symbol (w : Nat) Q where
  multitape : Multi w (Tape Symbol)
  indices : Multi w Int
  q : Q

def Configuration.read (conf : Configuration Symbol w Q) : Multi w (ReadAlphabet Symbol) :=
  {
    input := conf.multitape.input conf.indices.input,
    work := λ i ↦ conf.multitape.work i (conf.indices.work i),
    output := conf.multitape.output conf.indices.output
  }

def fupdate {α : Sort u} {β : α → Sort v} [DecidableEq α] (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

notation f "[" a' " ↦ " v "]" => fupdate f a' v

def Configuration.update (conf : Configuration Symbol w Q) (write : Multi w (WriteAlphabet Symbol)) (q' : Q) (dirs : Multi w Dir) : Configuration Symbol w Q :=
  { 
    multitape := {
      input := conf.multitape.input[conf.indices.input ↦ write.input.toRead],
      work := λ i ↦ (conf.multitape.work i)[ (conf.indices.work i) ↦ (write.work i).toRead],
      output := conf.multitape.output[conf.indices.output ↦ write.output.toRead],
    },
    indices := {
      input := conf.indices.input + dirs.input.movement,
      work := λ i ↦ conf.indices.work i + (dirs.work i).movement,
      output := conf.indices.output + dirs.output.movement
    },
    q := q',
  }

structure DecisionTM Symbol (w : Nat) Q where
  q_start : Q
  q_accept : Q
  q_reject : Q
  transition : TransitionFunction Symbol w Q q_accept q_reject

inductive Decision w Q where
  | decided : Bool → Decision w Q
  | continuation : Configuration Symbol w Q -> Decision w Q

def DecisionTM.accepted [ DecidableEq Q ] (tm : DecisionTM Symbol w Q) (conf : Configuration Symbol w Q) : Prop :=
  tm.q_accept = conf.q

def DecisionTM.rejected [ DecidableEq Q ] (tm : DecisionTM Symbol w Q) (conf : Configuration Symbol w Q) : Prop :=
  tm.q_reject = conf.q

def DecisionTM.step [ DecidableEq Q ] (tm : DecisionTM Symbol w Q) (conf : Configuration Symbol  w Q) : Decision w Q :=
  if q_vs_q_accept : conf.q = tm.q_accept then
    .decided true
  else if q_vs_q_reject : conf.q = tm.q_reject then
    .decided false
  else
    let (write, q', dirs) := tm.transition (conf.read, ⟨ conf.q, ⟨ q_vs_q_accept, q_vs_q_reject ⟩ ⟩)
   .continuation (conf.update write q' dirs)

inductive reachesIn [ DecidableEq Q ] (tm : DecisionTM Symbol w Q)
  : Nat → Configuration Symbol w Q → Configuration Symbol w Q → Prop where
  | reached : reachesIn tm 0 conf conf
  | withStep :
      tm.step conf = .continuation conf'
      → reachesIn tm n conf' conf''
      → reachesIn tm (n + 1) conf conf''

def initialConfiguration 
  (tm : DecisionTM Symbol w Q)
  (input : Fin n → Symbol) : Configuration Symbol w Q :=
  {
    multitape := {
      input := λ i ↦ match i with
                     | .ofNat i => if i_le_n : i < n then .symbol (input ⟨ i, i_le_n ⟩) else .blank ()
                     | .negSucc _ => .blank ()
      work := λ _ _ ↦ .blank (),
      output := λ _ ↦ .blank (),
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

def acceptsIn [ DecidableEq Q ] (tm : DecisionTM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) : Prop :=
  ∃ conf', reachesIn tm steps (initialConfiguration tm input) conf' ∧ tm.accepted conf'

def rejectsIn [ DecidableEq Q ] (tm : DecisionTM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) : Prop :=
  ∃ conf', reachesIn tm steps (initialConfiguration tm input) conf' ∧ tm.rejected conf'

def haltsIn [ DecidableEq Q ] (tm : DecisionTM Symbol w Q)
  (steps : Nat)
  (input : SymbolString Symbol n) : Prop := acceptsIn tm steps input ∨ rejectsIn tm steps input
