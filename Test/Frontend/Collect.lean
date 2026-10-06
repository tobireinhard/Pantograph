import Pantograph.Frontend
import Pantograph.Environment
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Collect

abbrev Test := Environment → TestT IO Unit

def runFrontend { α } (env : Environment) (source: String) (f : CompilationStep → FrontendM α) (timeout : UInt32 := 0)
  : IO (List α) := do
  let (context, state) ← do createContextStateFromFile source (env? := env)
  let m := mapCompilationSteps f
  let cancelTk? ← match timeout with
    | 0 => pure .none
    | timeout => .some <$> spawnCancelToken timeout
  m.run { cancelTk? } |>.run context |>.run' state

def test_open : Test := λ env => do
  let sketch := "
open Nat
example : ∀ (n : Nat), n + 1 = Nat.succ n := by
  intro
  apply add_one
  "
  let errors ← runFrontend env sketch λ step => step.msgs.mapM (·.toString)
  checkEq "errors" errors [[], []]

def collectTacticInvocations (env : Environment) (source : String) (withTreeInfo : Bool := false)
    : IO (List (List Protocol.InvokedTactic)) := do
  let (context, state) ← do Frontend.createContextStateFromFile source (env? := env)
  let m := show FrontendM _ from Frontend.mapCompilationSteps λ step => show FrontendM _ from do
    collectTacticsFromCompilationStep step withTreeInfo
  m.run {} |>.run context |>.run' state

private def test_collect_invocations_multiple : Test := λ env => do
  let input := "
example : ∀ (p q: Prop), p ∨ q → q ∨ p := by
  intro p q h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example : α → α := by
  intro x
  exact x
  "
  let invocations ← collectTacticInvocations env input
  checkEq "numbers" (invocations.map (·.length)) [6, 2]

/-- Goal ids link the tactics: the goals created by `constructor` are passed on,
the remaining goal is carried along by the first `exact`, and the root goal is
consumed. -/
private def test_collect_goal_ids : Test := λ env => do
  let input := "
example (p : Prop) (hp : p) : p ∧ p := by
  constructor
  exact hp
  exact hp
  "
  -- Without the flag, no goal ids are recorded
  let plain ← collectTacticInvocations env input
  checkTrue "no ids without flag" <| plain.flatten.all λ t =>
    t.goalIdsBefore?.isNone && t.goalIdsAfter?.isNone && t.parent?.isNone
      && t.parentViaBy?.isNone

  let [[t0, t1, t2]] ← collectTacticInvocations env input (withTreeInfo := true)
    | fail "Expected one compilation step with three tactic invocations"
  checkEq "tactics" [t0.tactic, t1.tactic, t2.tactic] ["constructor", "exact hp", "exact hp"]
  checkTrue "ids with flag" <| [t0, t1, t2].all λ t =>
    t.goalIdsBefore?.isSome && t.goalIdsAfter?.isSome
  let ids := λ (t : Protocol.InvokedTactic) => (t.goalIdsBefore?.getD #[], t.goalIdsAfter?.getD #[])
  let (b0, a0) := ids t0
  let (b1, a1) := ids t1
  let (b2, a2) := ids t2
  checkEq "sizes" [(b0.size, a0.size), (b1.size, a1.size), (b2.size, a2.size)]
    [(1, 2), (2, 1), (1, 0)]
  checkEq "goals of constructor are passed on" b1 a0
  checkEq "remaining goal is carried along" b2 a1
  checkEq "remaining goal was created by constructor" b2 #[a0[1]!]
  checkTrue "root goal is consumed" <| !(a0 ++ b1 ++ a1 ++ b2 ++ a2).contains b0[0]!
  -- Tactics in the same tactic sequence are siblings, not children
  checkEq "parents" [t0.parent?, t1.parent?, t2.parent?] [.none, .none, .none]

/-- The tactics of the inner `by` block of a `have` are nested under the `have`. -/
private def test_collect_parent : Test := λ env => do
  let input := "
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  have h : q := by exact hq
  exact ⟨hp, h⟩
  "
  let [ts] ← collectTacticInvocations env input (withTreeInfo := true)
    | fail "Expected one compilation step"
  let indexOf (pred : String → Bool) : Option Nat := ts.findIdx? (pred ·.tactic)
  let some iHave := indexOf (·.startsWith "have") | fail "No `have` invocation"
  let some iInner := indexOf (· == "exact hq") | fail "No inner `exact` invocation"
  let some iOuter := indexOf (·.startsWith "exact ⟨") | fail "No outer `exact` invocation"
  let parentOf (i : Nat) : Option Nat := ts[i]?.bind (·.parent?)
  checkEq "have is top level" (parentOf iHave) .none
  checkEq "outer exact is top level" (parentOf iOuter) .none
  -- Robust against duplicated `have` nodes from macro expansion
  checkTrue "inner exact is nested in have" <|
    ((parentOf iInner).bind (ts[·]?)).any (·.tactic.startsWith "have")
  checkTrue "parents precede children" <| ts.zipIdx.all λ (t, i) => t.parent?.all (· < i)
  checkEq "inner exact is inside a by block" (ts[iInner]?.bind (·.parentViaBy?)) (.some true)
  checkTrue "no by flag without parent" <| ts.all λ t => t.parent?.isSome || t.parentViaBy?.isNone

/-- Tactics in a nested `by` block (of `have` and `suffices`) are marked as such,
tactics in structured tactic syntax (`cases … with`, `case`) are not. -/
private def test_collect_parent_via_by : Test := λ env => do
  let input := "
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h
  case inl hp => exact Or.inr hp
  case inr hq => exact Or.inl hq

example (a b : Nat) (h : a = b) : b = a := by
  suffices h' : a = b by exact h'.symm
  exact h
  "
  let [casesWith, caseRename, suff] ← collectTacticInvocations env input (withTreeInfo := true)
    | fail "Expected three compilation steps"
  -- For every invocation with a parent: first word of the parent tactic, and the flag
  let nested (ts : List Protocol.InvokedTactic) : List (String × Bool) :=
    ts.filterMap λ t => do
      let i ← t.parent?
      let p ← ts[i]?
      let viaBy ← t.parentViaBy?
      return ((p.tactic.splitOn " ").head!, viaBy)
  checkEq "cases with" (nested casesWith) [("cases", false), ("cases", false)]
  checkEq "case with renaming" (nested caseRename) [("case", false), ("case", false)]
  checkEq "suffices" (nested suff) [("suffices", true)]

def collectNewConstants (env : Environment) (source: String) : IO (List (List Name)) := do
  let (context, state) ← do Frontend.createContextStateFromFile source (env? := env)
  let m := show FrontendM _ from Frontend.mapCompilationSteps λ step => do
    step.newConstants
  let result ← m.run {} |>.run context |>.run' state
  return result.map (·.toList)

def test_collect_one_constant : Test := λ env => do
  let input := "
def mystery : Nat := 123
  "
  let names ← collectNewConstants env input
  checkEq "constants" names [[`mystery]]

def test_collect_one_theorem : Test := λ env => do
  let input := "
theorem mystery [SizeOf α] (as : List α) (i : Fin as.length) : sizeOf (as.get i) < sizeOf as := by
  match as, i with
  | a::as, ⟨0, _⟩  => simp_arith [get]
  | a::as, ⟨i+1, h⟩ =>
    have ih := sizeOf_get as ⟨i, Nat.le_of_succ_le_succ h⟩
    apply Nat.lt_trans ih
    simp_arith
  "
  let names ← collectNewConstants env input
  checkEq "constants" names [[`mystery]]

def test_collect_stub : Test := λ env => do
  let input := "
theorem mystery [SizeOf α] (as : List α) (i : Fin as.length) : sizeOf (as.get i) < sizeOf as := sorry
  "
  let names ← collectNewConstants env input
  checkEq "constants" names [[`mystery]]

def checkFileConflicts (env : Environment) (src dst : String) : IO (Except String Environment):= do
  let srcState ← collectOne src
  let dstState ← collectOne dst
  ExceptT.run $ checkEnvConflicts env srcState.env dstState.env
  where
  collectOne (source : String) : IO _ := do
    let (context, state) ← do createContextStateFromFile source (env? := env)
    let m := collectEndState
    m.run { } |>.run context |>.run' state

def test_conflict_simple : Test := λ env => do
  let src := "
def x : Nat := sorry
  "
  let dst := "
def x : Nat := 123
  "
  let result? ← checkFileConflicts env src dst
  match result? with
  | .ok _ =>  checkTrue "ok" result?.isOk
  | .error e =>  fail s!"Failed with {e}"
def test_conflict_poly : Test := λ env => do
  let src := "
def mystery : List α → List α := sorry
  "
  let dst := "
def helper (li : List β) := li.reverse
def mystery (li : List α) := (helper li) ++ li
  "
  let result? ← checkFileConflicts env src dst
  match result? with
  | .ok _ =>  checkTrue "ok" result?.isOk
  | .error e =>  fail s!"Failed with {e}"

def test_conflict_auxiliary : Test := λ env => do
  let src := "
def f : Nat → Nat := sorry
  "
  let dst := "
def x : Nat := 123
def f : Nat → Nat := λ y => y + x
  "
  let result? ← checkFileConflicts env src dst
  match result? with
  | .ok _ =>  checkTrue "ok" result?.isOk
  | .error e =>  fail s!"Failed with {e}"
def test_conflict_axiom : Test := λ env => do
  let src := "
axiom α : Type
axiom ne : Nonempty α
noncomputable def f : α := sorry
  "
  let dst := "
axiom α : Type
axiom ne : Nonempty α
noncomputable def f : α := @Classical.choice α ne
  "
  let result? ← checkFileConflicts env src dst
  match result? with
  | .ok _ =>  checkTrue "ok" result?.isOk
  | .error e =>  fail s!"Failed with {e}"

/-- from `GasStationManager/SafeVerify` -/
def test_conflict_simple_def : Test := λ env => do
  let src := "
def solveAdd (a b:Int):{c:Int//a+c=b} := sorry
  "
  let dst := "
def solveAdd (a b:Int):{c:Int//a+c=b} := ⟨b-a, by omega⟩
  "
  let result? ← checkFileConflicts env src dst
  match result? with
  | .ok _ =>  checkTrue "ok" result?.isOk
  | .error e =>  fail s!"Failed with {e}"
/-- from `GasStationManager/SafeVerify` -/
def test_conflict_fake_implementation : Test := λ env => do
  let src := "
noncomputable def definitely_at_least_two : Nat := sorry
theorem definitely_at_least_two_spec : 2 ≤ definitely_at_least_two := sorry
  "
  let dst := "
@[implemented_by Nat.zero]
noncomputable def definitely_at_least_two : Nat :=
  Exists.choose (⟨3, by simp⟩ : ∃ x, 2 ≤ x)

theorem definitely_at_least_two_spec : 2 ≤ definitely_at_least_two :=
  Exists.choose_spec _
  "
  let result? ← checkFileConflicts env src dst
  match result? with
  | .ok _ =>  checkTrue "ok" result?.isOk
  | .error e =>  fail s!"Failed with {e}"

def test_conflict_fail_idempotent : Test := λ env => do
  let src := "
def x : Nat := sorry
  "
  let .error e ← checkFileConflicts env src src
    | fail "Must fail"
  checkEq "message" e "Definition value has sorry: x"
def test_conflict_fail_delete_definition : Test := λ env => do
  let src := "
def x : Nat := sorry
def y : Nat := sorry
  "
  let dst := "
def x : Nat := 123
  "
  let .error e ← checkFileConflicts env src dst
    | fail "Must fail"
  checkEq "message" e "[y] not accounted for"

def test_conflict_fail_inductive_modification : Test := λ env => do
  let src := "
inductive A where
  | a
  | b
  "
  let dst := "
inductive A where
  | a
  | b
  | c
  "
  let .error e ← checkFileConflicts env src dst
    | fail "Must fail"
  checkEq "message" e "Type clash of A.casesOn"

/-- from `GasStationManager/SafeVerify` -/
def test_conflict_fail_noncomputable : Test := λ env => do
  let src := "
axiom α : Type
axiom ne : Nonempty α
def f : α := sorry
  "
  let dst := "
axiom α : Type
axiom ne : Nonempty α
noncomputable def f : α := @Classical.choice α ne
  "
  let .error e ← checkFileConflicts env src dst
    | fail "Must fail"
  checkEq "message" e "Must not modify computability on f"

def test_conflict_fail_add_axiom : Test := λ env => do
  let src := "
theorem mystery : False := sorry
  "
  let dst := "
axiom z : False
theorem mystery : False := z
  "
  let .error e ← checkFileConflicts env src dst
    | fail "Must fail"
  checkEq "message" e "Adding axiom is not allowed: z"

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("open", test_open),
    ("collect_invocations_multiple", test_collect_invocations_multiple),
    ("collect_goal_ids", test_collect_goal_ids),
    ("collect_parent", test_collect_parent),
    ("collect_parent_via_by", test_collect_parent_via_by),
    ("collect_one_constant", test_collect_one_constant),
    ("collect_one_theorem", test_collect_one_theorem),
    ("collect_stub", test_collect_stub),
    ("conflict simple", test_conflict_simple),
    ("conflict poly", test_conflict_poly),
    ("conflict auxiliary", test_conflict_auxiliary),
    ("conflict simple def", test_conflict_simple_def),
    ("conflict axiom", test_conflict_axiom),
    ("conflict fake implementation", test_conflict_fake_implementation),
    ("conflict fail idempotent", test_conflict_fail_idempotent),
    ("conflict fail delete definition", test_conflict_fail_delete_definition),
    ("conflict fail inductive modification", test_conflict_fail_inductive_modification),
    ("conflict fail noncomputable", test_conflict_fail_noncomputable),
    ("conflict fail add axiom", test_conflict_fail_add_axiom),
  ]
  tests.map (fun (name, test) => (name, runTest $ test env))
