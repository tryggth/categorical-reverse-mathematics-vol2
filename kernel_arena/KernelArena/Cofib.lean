/-
Pure Functional Partition-Refinement (Union-Find) Solver for Cartesian Cofibrations.
Decides cofibration entailment `Ψ, ψ ⊢ φ` over `Fin (|Ψ| + 2)` (`0 = Dim0`, `1 = Dim1`).
Zero `partial`, zero `sorry`, zero `axiom`, zero `Id.run`/`for`/`Array.get!`.
-/
import KernelArena.AST

namespace KernelArena
namespace Cofib

/-- Map `Dim` into `0 .. dLen + 1` (`0 = d0`, `1 = d1`, `i + 2 = dvar i`). -/
def dimToIdx : Dim → Nat
  | .d0 => 0
  | .d1 => 1
  | .dvar i => i + 2

/-- Check that every dimension variable index is `< dLen`. -/
def dimWellScoped (dLen : Nat) : Dim → Bool
  | .d0 => true
  | .d1 => true
  | .dvar i => decide (i < dLen)

/-- Check that every atom in `Cof` is well-scoped in dimension context length `dLen`. -/
def cofWellScoped (dLen : Nat) : Cof → Bool
  | .top => true
  | .bot => true
  | .eq r1 r2 => dimWellScoped dLen r1 && dimWellScoped dLen r2
  | .and c1 c2 => cofWellScoped dLen c1 && cofWellScoped dLen c2
  | .or c1 c2 => cofWellScoped dLen c1 && cofWellScoped dLen c2

private def listGetD : List Nat → Nat → Nat
  | [], d => d
  | x :: _, 0 => x
  | _ :: xs, n + 1 => listGetD xs n

private def listSet : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

private def mkInitAux : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, k => k :: mkInitAux n (k + 1)

/-- Canonical initial partition `[0, 1, ..., n - 1]`. -/
def mkInitUF (n : Nat) : List Nat :=
  mkInitAux n 0

/-- Fuel-bounded union-find representative lookup (guaranteed exact with `fuel = dLen + 2`). -/
def findRoot : Nat → List Nat → Nat → Nat
  | 0, _, x => x
  | fuel + 1, p, x =>
    let px := listGetD p x
    if px == x then x else findRoot fuel p px

/-- Merge equivalence classes of `x` and `y`, pointing the larger root to the smaller root. -/
def unionUF (dLen : Nat) (p : List Nat) (x y : Nat) : List Nat :=
  let fuel := dLen + 2
  let rx := findRoot fuel p x
  let ry := findRoot fuel p y
  if rx == ry then p
  else if rx < ry then listSet p ry rx
  else listSet p rx ry

/-- Decide whether `x` and `y` belong to the same equivalence class in partition `p`. -/
def sameClass (dLen : Nat) (p : List Nat) (x y : Nat) : Bool :=
  let fuel := dLen + 2
  findRoot fuel p x == findRoot fuel p y

/-- A branch equating `Dim0` (0) and `Dim1` (1) is inconsistent. -/
def ufInconsistent (dLen : Nat) (p : List Nat) : Bool :=
  sameClass dLen p 0 1

private def filterConsistent (dLen : Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | b :: bs =>
    if ufInconsistent dLen b then filterConsistent dLen bs
    else b :: filterConsistent dLen bs

private def mergeEqBranches (dLen : Nat) (x y : Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | b :: bs =>
    let b' := unionUF dLen b x y
    if ufInconsistent dLen b' then mergeEqBranches dLen x y bs
    else b' :: mergeEqBranches dLen x y bs

/-- Structurally refine a list of equivalence partitions by cofibration `c`. -/
private def addCofToBranches (dLen : Nat) : Cof → List (List Nat) → List (List Nat)
  | .top, bs => filterConsistent dLen bs
  | .bot, _ => []
  | .eq r1 r2, bs =>
    if !dimWellScoped dLen r1 || !dimWellScoped dLen r2 then []
    else mergeEqBranches dLen (dimToIdx r1) (dimToIdx r2) bs
  | .and c1 c2, bs => addCofToBranches dLen c2 (addCofToBranches dLen c1 bs)
  | .or c1 c2, bs => addCofToBranches dLen c1 bs ++ addCofToBranches dLen c2 bs

/-- Expand cofibration `ψ` into consistent equivalence partitions on `Fin (dLen + 2)`. -/
def solveCofBranches (dLen : Nat) (ψ : Cof) : List (List Nat) :=
  addCofToBranches dLen ψ [mkInitUF (dLen + 2)]

/-- Evaluate whether a consistent partition `p` satisfies cofibration `φ`. -/
def satBranch (dLen : Nat) (p : List Nat) : Cof → Bool
  | .top => true
  | .bot => false
  | .eq r1 r2 =>
    dimWellScoped dLen r1 && dimWellScoped dLen r2 &&
      sameClass dLen p (dimToIdx r1) (dimToIdx r2)
  | .and c1 c2 => satBranch dLen p c1 && satBranch dLen p c2
  | .or c1 c2 => satBranch dLen p c1 || satBranch dLen p c2

private def isNilList {α : Type} : List α → Bool
  | [] => true
  | _ :: _ => false

/-- Decide whether `ψ` is inconsistent under `Ψ` (every branch equates `0` and `1`). -/
def isInconsistent (dLen : Nat) (ψ : Cof) : Bool :=
  match ψ with
  | .top => false
  | .bot => true
  | .eq r1 r2 =>
    if beqDim r1 r2 then !dimWellScoped dLen r1
    else isNilList (solveCofBranches dLen ψ)
  | .and _ _ => isNilList (solveCofBranches dLen ψ)
  | .or _ _ => isNilList (solveCofBranches dLen ψ)

/-- Decide Cartesian cofibration entailment `Ψ, ψ ⊢ φ`. -/
def entails (dLen : Nat) (ψ φ : Cof) : Bool :=
  match φ with
  | .top => true
  | .bot => isInconsistent dLen ψ
  | .eq _ _ =>
    if beqCof ψ φ && cofWellScoped dLen ψ then true
    else (solveCofBranches dLen ψ).all (fun b => satBranch dLen b φ)
  | .and _ _ =>
    if beqCof ψ φ && cofWellScoped dLen ψ then true
    else (solveCofBranches dLen ψ).all (fun b => satBranch dLen b φ)
  | .or _ _ =>
    if beqCof ψ φ && cofWellScoped dLen ψ then true
    else (solveCofBranches dLen ψ).all (fun b => satBranch dLen b φ)

/-- Decide dimension equality `Ψ, ψ ⊢ r₁ = r₂`. -/
def dimEqUnder (dLen : Nat) (ψ : Cof) (r1 r2 : Dim) : Bool :=
  if beqDim r1 r2 then dimWellScoped dLen r1
  else entails dLen ψ (.eq r1 r2)

end Cofib
end KernelArena
