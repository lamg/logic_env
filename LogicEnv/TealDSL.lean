import Std.Data.HashMap
import Lean

inductive Ty where
  | uint64
  | bytes
deriving DecidableEq, Repr

abbrev Stack := List Ty

-- DSL for representing TEAL programs
inductive TealProg : Stack → Stack → Type where
  | id  : TealProg s s
  | seq : TealProg s0 s1 → TealProg s1 s2 → TealProg s0 s2
  -- stack ops
  | pushU (n : Nat) : TealProg s (Ty.uint64 :: s)
  | pushB (bs : ByteArray) : TealProg s (Ty.bytes :: s)
  | add  : TealProg (Ty.uint64 :: Ty.uint64 :: s) (Ty.uint64 :: s)
  -- TEAL booleans are uint64 (0/1)
  | eqU  : TealProg (Ty.uint64 :: Ty.uint64 :: s) (Ty.uint64 :: s)
  | dup  : TealProg (t :: s) (t :: t :: s)
  | swap : TealProg (a :: b :: s) (b :: a :: s)
  -- control (structured; compiled to labels+jumps)
  | ifElse :
    TealProg s0 (Ty.uint64 :: s0) →  -- condition producer
    TealProg s0 s1 →                 -- then-branch (assumes condition consumed)
    TealProg s0 s1 →                 -- else-branch
    TealProg s0 s1
  -- TODO extend with txn fields, scratch, app/global/local etc.

inductive Value where
  | U (n : Nat)      -- model uint64; you can wrap to 2^64
  | B (bs : ByteArray)

def byteArrayToHex (bs : ByteArray) : String :=
  bs.toList.foldl (fun acc b => acc ++ Char.toString (Char.ofUInt8 b)) ""

instance : Repr Value where
  reprPrec
    | Value.U n, _   => Std.Format.group (toString n)
    | Value.B bs, _  => Std.Format.group ("0x" ++ byteArrayToHex bs)


structure MachineState where
  stack   : List (Ty × Value)   -- value paired with its type tag
  scratch : Std.HashMap Nat (Ty × Value)
  -- TODO add global/local/app state, boxes, txn fields, …
deriving Inhabited

-- type representing the compiled instructions from TealProg
inductive Instr where
  | int (n : Nat)
  | byte (bs : ByteArray)
  | add
  | eq
  | dup
  | swap
  | bz (label : String)
  | b  (label : String)
  | label (label : String)
  -- TODO add more instructions

instance : Repr Instr where
  reprPrec
    | Instr.int n, _     => Std.Format.text s!"int {n}"
    | Instr.byte bs, _   => Std.Format.text s!"byte 0x{byteArrayToHex bs}"
    | Instr.add, _       => Std.Format.text "add"
    | Instr.eq, _        => Std.Format.text "eq"
    | Instr.dup, _       => Std.Format.text "dup"
    | Instr.swap, _      => Std.Format.text "swap"
    | Instr.bz l, _      => Std.Format.text s!"bz {l}"
    | Instr.b l, _       => Std.Format.text s!"b {l}"
    | Instr.label l, _   => Std.Format.text s!"label {l}"

abbrev Program := List Instr


def eval : TealProg s0 s1 → MachineState → Except String MachineState
  | .id, t => Except.ok t
  | .seq p q, t => do
      let t' ← eval p t
      eval q t'
  | .pushU n, t =>
      .ok { t with stack := (Ty.uint64, Value.U n) :: t.stack }
  | .pushB bs, t =>
      .ok { t with stack := (Ty.bytes, Value.B bs) :: t.stack }
  | .add, t =>
      match t.stack with
      | (Ty.uint64, Value.U n1) :: (Ty.uint64, Value.U n2) :: rest =>
          .ok { t with stack := (Ty.uint64, Value.U (n1 + n2)) :: rest }
      | _ => .error "stack underflow or type mismatch in add"
  | .eqU, t =>
      match t.stack with
      | (Ty.uint64, Value.U n1) :: (Ty.uint64, Value.U n2) :: rest =>
          let b := if n1 = n2 then 1 else 0
          .ok { t with stack := (Ty.uint64, Value.U b) :: rest }
      | _ => .error "stack underflow or type mismatch in eq"
  | .dup, t =>
    match t.stack with
    | x :: xs => .ok {t with stack := x :: x :: xs }
    | _ => .ok t
  | .swap, t =>
    match t.stack with
    | x :: y :: xs => .ok {t with stack := y :: x :: xs }
    | _ => .ok t
  | .ifElse cond thenB elseB, st =>
    match eval cond st with
    | .ok st' =>
      match st'.stack with
      | (Ty.uint64, Value.U 1) :: rest =>
        eval thenB { st' with stack := rest }
      | (Ty.uint64, Value.U 0) :: rest =>
        eval elseB { st' with stack := rest }
      | _ =>
        .error "ifElse: condition did not leave a uint64 0 or 1 on stack"
    | e => e
attribute [simp] eval

mutual
  partial def compile : TealProg s0 s1 → StateM Nat Program
  | .id        => pure []
  | .seq p q   => do
      let cp ← compile p
      let cq ← compile q
      pure (cp ++ cq)
  | .pushU n   => pure [Instr.int n]
  | .pushB bs  => pure [Instr.byte bs]
  | .add       => pure [Instr.add]
  | .eqU       => pure [Instr.eq]
  | .dup       => pure [Instr.dup]
  | .swap      => pure [Instr.swap]
  | .ifElse c t e => compileIfElse c t e

  partial def compileIfElse
    : TealProg s0 (Ty.uint64 :: s0) → TealProg s0 s1 → TealProg s0 s1 → StateM Nat Program
  | c, t, e => do
      let le ← get; modify (· + 1)
      let ld ← get; modify (· + 1)
      let cc ← compile c
      let ct ← compile t
      let ce ← compile e
      let lElse := s!"L{le}"
      let lDone := s!"L{ld}"
      pure <|
        cc ++
        [Instr.bz lElse] ++
        ct ++
        [Instr.b lDone, Instr.label lElse] ++
        ce ++
        [Instr.label lDone]
end

def Assert := MachineState → Prop

def triple (P : Assert) (p : TealProg s0 s1) (Q : Assert) : Prop :=
  ∀ t, P t → ∃ t', eval p t = .ok t' ∧ Q t'

-- Stack type is a list of Ty (Ty.uint64 or Ty.bytes)
def wellTyped (state : MachineState) (expectedStack : List Ty) : Prop :=
  (state.stack.map (fun (t, _) => t)) = expectedStack

-- A simplified TEAL interpreter
partial def runsTo : Program → MachineState → Except String MachineState
  | [], state => .ok state
  | instr :: rest, state =>
    match instr with
    | Instr.int n =>
        runsTo rest { state with stack := (Ty.uint64, Value.U n) :: state.stack }
    | Instr.byte bs =>
        runsTo rest { state with stack := (Ty.bytes, Value.B bs) :: state.stack }
    | Instr.add =>
        match state.stack with
        | (Ty.uint64, Value.U n1) :: (Ty.uint64, Value.U n2) :: stackTail =>
            let newState := { state with stack := (Ty.uint64, Value.U (n1 + n2)) :: stackTail }
            runsTo rest newState
        | _ => .error "stack underflow or type mismatch in add"
    | Instr.eq =>
        match state.stack with
        | (Ty.uint64, Value.U n1) :: (Ty.uint64, Value.U n2) :: stackTail =>
            let b := if n1 = n2 then 1 else 0
            let newState := { state with stack := (Ty.uint64, Value.U b) :: stackTail }
            runsTo rest newState
        | _ => .error "stack underflow or type mismatch in eq"
    | Instr.dup =>
        match state.stack with
        | t :: tail => runsTo rest ( { state with stack := t :: t :: tail } )
        | _ => .error "stack underflow in dup"
    | Instr.swap =>
        match state.stack with
        | a :: b :: tail => runsTo rest ( { state with stack := b :: a :: tail } )
        | _ => .error "stack underflow in swap"
    | Instr.label _ => runsTo rest state   -- labels do nothing at runtime
    | Instr.b _ => runsTo rest state       -- simplified: not resolving labels
    | Instr.bz _ => runsTo rest state      -- simplified: not resolving labels

def prog0 : TealProg [] [Ty.uint64, Ty.uint64] :=
  TealProg.seq (TealProg.pushU 2) (TealProg.pushU  3)

def testProg {out : List Ty} (prog : TealProg [] out) : List (Ty × Value) :=
  let initState : MachineState :=
    { stack := [], scratch := Std.HashMap.emptyWithCapacity }
  match eval prog initState with
  | .ok st    => st.stack
  | .error _  => []

def compileProg {inStack outStack : List Ty} (prog : TealProg inStack outStack) : Program :=
  (compile prog).run 0 |>.1

instance : Repr (List Instr) where
  reprPrec xs _ :=
    let lines := xs.map (fun i => repr i)  -- call Instr’s repr
    Std.Format.joinSep lines Std.Format.line

-- theorem compile_correct (p : Prog s0 s1)
--   : ∀ t, wellTyped s0 s1 →
--     runsTo (compile p |>.eval 0) t = Execpt.ok t' →
--     t' = eval p t

-- #eval testProg prog0
-- #eval compileProg prog0

-- Condition: compare top-of-stack PIN with 1234 and push 0/1
def pinCond : TealProg [Ty.uint64] [Ty.uint64, Ty.uint64] :=
  .seq .dup (.seq (.pushU 1234) .eqU)
  -- start:  [pin]
  -- pushU:  [1234, pin]
  -- eqU:    [pin == 1234 ? 1 : 0]

-- Branches: produce the decision bit (we leave the original pin under it)
def thenBranch : TealProg [Ty.uint64] [Ty.uint64, Ty.uint64] := .pushU 1
def elseBranch : TealProg [Ty.uint64] [Ty.uint64, Ty.uint64] := .pushU 0

-- Final program: if pin==1234 then push 1 else push 0
def pinGuard : TealProg [Ty.uint64] [Ty.uint64, Ty.uint64] :=
  .ifElse pinCond thenBranch elseBranch

open Std

def emptyState : MachineState :=
  { stack := [], scratch := HashMap.emptyWithCapacity }

def withPin (n : Nat) : MachineState :=
  { stack := [(Ty.uint64, Value.U n)], scratch := HashMap.emptyWithCapacity }


theorem pinGuard_ok :
  eval pinGuard (withPin 1234)
  =
  .ok { stack := (Ty.uint64, Value.U 1) :: (Ty.uint64, Value.U 1234) :: []
      , scratch := HashMap.emptyWithCapacity } := by
  rfl

#eval compileProg pinGuard

theorem pinGuard_bad :
  ¬ ∃ (n : Nat) (t : MachineState),
    eval pinGuard (withPin n) = .ok t ∧
    n ≠ 1234 ∧
    t.stack.head? = some (Ty.uint64, Value.U 1) := by
  sorry
