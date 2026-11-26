/-
Fuel-bounded WHNF and bidirectional 2LTT typechecking for `KernelArena`.
Zero `partial`, zero `sorry`, zero `axiom`, zero `propext` (no wildcard `match`).
-/
import KernelArena.AST
import KernelArena.Arena

namespace KernelArena
namespace Check

/-- Shift free de Bruijn indices `≥ cutoff` by `d`. -/
def shift (d cutoff : Nat) : Term → Term
  | .univS l => .univS l
  | .univF l => .univF l
  | .boolS => .boolS
  | .boolF => .boolF
  | .trueF => .trueF
  | .falseF => .falseF
  | .var idx => if idx >= cutoff then .var (idx + d) else .var idx
  | .piS dom cod => .piS (shift d cutoff dom) (shift d (cutoff + 1) cod)
  | .piF dom cod => .piF (shift d cutoff dom) (shift d (cutoff + 1) cod)
  | .lamS dom body => .lamS (shift d cutoff dom) (shift d (cutoff + 1) body)
  | .lamF dom body => .lamF (shift d cutoff dom) (shift d (cutoff + 1) body)
  | .appS fn arg => .appS (shift d cutoff fn) (shift d cutoff arg)
  | .appF fn arg => .appF (shift d cutoff fn) (shift d cutoff arg)
  | .liftFtoS inner => .liftFtoS (shift d cutoff inner)
  | .innerUnivalence arg => .innerUnivalence (shift d cutoff arg)
  | .innerCoalgebraNu arg => .innerCoalgebraNu (shift d cutoff arg)
  | .outerStrictEq lhs rhs => .outerStrictEq (shift d cutoff lhs) (shift d cutoff rhs)
  | .smallnessReplacement arg => .smallnessReplacement (shift d cutoff arg)

/-- Substitute `s` for de Bruijn variable `j` and shift higher indices down by 1. -/
def subst (j : Nat) (s : Term) : Term → Term
  | .univS l => .univS l
  | .univF l => .univF l
  | .boolS => .boolS
  | .boolF => .boolF
  | .trueF => .trueF
  | .falseF => .falseF
  | .var idx =>
    if idx == j then shift j 0 s
    else if idx > j then .var (idx - 1)
    else .var idx
  | .piS dom cod => .piS (subst j s dom) (subst (j + 1) s cod)
  | .piF dom cod => .piF (subst j s dom) (subst (j + 1) s cod)
  | .lamS dom body => .lamS (subst j s dom) (subst (j + 1) s body)
  | .lamF dom body => .lamF (subst j s dom) (subst (j + 1) s body)
  | .appS fn arg => .appS (subst j s fn) (subst j s arg)
  | .appF fn arg => .appF (subst j s fn) (subst j s arg)
  | .liftFtoS inner => .liftFtoS (subst j s inner)
  | .innerUnivalence arg => .innerUnivalence (subst j s arg)
  | .innerCoalgebraNu arg => .innerCoalgebraNu (subst j s arg)
  | .outerStrictEq lhs rhs => .outerStrictEq (subst j s lhs) (subst j s rhs)
  | .smallnessReplacement arg => .smallnessReplacement (subst j s arg)

private def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

private def asLamFBody? (t : Term) : Option Term := by
  cases t with
  | lamF _ body => exact some body
  | _ => exact none

private def asLamSBody? (t : Term) : Option Term := by
  cases t with
  | lamS _ body => exact some body
  | _ => exact none

private def asUnivF? (t : Term) : Option Nat := by
  cases t with
  | univF l => exact some l
  | _ => exact none

private def asUnivS? (t : Term) : Option Nat := by
  cases t with
  | univS l => exact some l
  | _ => exact none

private def asPiF? (t : Term) : Option (Term × Term) := by
  cases t with
  | piF dom cod => exact some (dom, cod)
  | _ => exact none

private def asPiS? (t : Term) : Option (Term × Term) := by
  cases t with
  | piS dom cod => exact some (dom, cod)
  | _ => exact none

private def isValidSort (t : Term) : Bool := by
  cases t with
  | univF _ => exact true
  | univS _ => exact true
  | _ => exact false

/-- Fuel-bounded weak head normal form reduction (beta reduction for fibrant and strict apps). -/
def whnf : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, t =>
    match t with
    | .appF fn arg =>
      match whnf fuel fn with
      | none => none
      | some fn' =>
        match asLamFBody? fn' with
        | some body => whnf fuel (subst 0 arg body)
        | none => some (.appF fn' arg)
    | .appS fn arg =>
      match whnf fuel fn with
      | none => none
      | some fn' =>
        match asLamSBody? fn' with
        | some body => whnf fuel (subst 0 arg body)
        | none => some (.appS fn' arg)
    | .univS l => some (.univS l)
    | .univF l => some (.univF l)
    | .boolS => some .boolS
    | .boolF => some .boolF
    | .trueF => some .trueF
    | .falseF => some .falseF
    | .var idx => some (.var idx)
    | .piS d c => some (.piS d c)
    | .piF d c => some (.piF d c)
    | .lamS d b => some (.lamS d b)
    | .lamF d b => some (.lamF d b)
    | .liftFtoS i => some (.liftFtoS i)
    | .innerUnivalence a => some (.innerUnivalence a)
    | .innerCoalgebraNu a => some (.innerCoalgebraNu a)
    | .outerStrictEq l r => some (.outerStrictEq l r)
    | .smallnessReplacement a => some (.smallnessReplacement a)

private def eqModHead (recEq : Term → Term → Bool) (u1 u2 : Term) : Bool := by
  cases u1 with
  | univS l1 =>
    cases u2 with
    | univS l2 => exact l1 == l2
    | _ => exact false
  | univF l1 =>
    cases u2 with
    | univF l2 => exact l1 == l2
    | _ => exact false
  | boolS =>
    cases u2 with
    | boolS => exact true
    | _ => exact false
  | boolF =>
    cases u2 with
    | boolF => exact true
    | _ => exact false
  | trueF =>
    cases u2 with
    | trueF => exact true
    | _ => exact false
  | falseF =>
    cases u2 with
    | falseF => exact true
    | _ => exact false
  | var i1 =>
    cases u2 with
    | var i2 => exact i1 == i2
    | _ => exact false
  | piS d1 c1 =>
    cases u2 with
    | piS d2 c2 => exact recEq d1 d2 && recEq c1 c2
    | _ => exact false
  | piF d1 c1 =>
    cases u2 with
    | piF d2 c2 => exact recEq d1 d2 && recEq c1 c2
    | _ => exact false
  | lamS d1 b1 =>
    cases u2 with
    | lamS d2 b2 => exact recEq d1 d2 && recEq b1 b2
    | _ => exact false
  | lamF d1 b1 =>
    cases u2 with
    | lamF d2 b2 => exact recEq d1 d2 && recEq b1 b2
    | _ => exact false
  | appS f1 a1 =>
    cases u2 with
    | appS f2 a2 => exact recEq f1 f2 && recEq a1 a2
    | _ => exact false
  | appF f1 a1 =>
    cases u2 with
    | appF f2 a2 => exact recEq f1 f2 && recEq a1 a2
    | _ => exact false
  | liftFtoS x1 =>
    cases u2 with
    | liftFtoS x2 => exact recEq x1 x2
    | _ => exact false
  | innerUnivalence x1 =>
    cases u2 with
    | innerUnivalence x2 => exact recEq x1 x2
    | _ => exact false
  | innerCoalgebraNu x1 =>
    cases u2 with
    | innerCoalgebraNu x2 => exact recEq x1 x2
    | _ => exact false
  | outerStrictEq l1 r1 =>
    cases u2 with
    | outerStrictEq l2 r2 => exact recEq l1 l2 && recEq r1 r2
    | _ => exact false
  | smallnessReplacement x1 =>
    cases u2 with
    | smallnessReplacement x2 => exact recEq x1 x2
    | _ => exact false

/-- Fuel-bounded definitional equality up to WHNF. -/
def isDefEq : Nat → Term → Term → Bool
  | 0, _, _ => false
  | fuel + 1, t1, t2 =>
    match whnf fuel t1 with
    | none => false
    | some u1 =>
      match whnf fuel t2 with
      | none => false
      | some u2 => eqModHead (isDefEq fuel) u1 u2

private def extractUnivF (fuel : Nat) (tyOpt : Option Term) : Option Nat :=
  match tyOpt with
  | none => none
  | some ty =>
    match whnf fuel ty with
    | none => none
    | some wty => asUnivF? wty

private def extractUnivS (fuel : Nat) (tyOpt : Option Term) : Option Nat :=
  match tyOpt with
  | none => none
  | some ty =>
    match whnf fuel ty with
    | none => none
    | some wty => asUnivS? wty

/-- Fuel-bounded type inference enforcing 2LTT stratum separation (`F -> S` only). -/
def infer : Nat → Nat → List Term → Term → Option Term
  | 0, _, _, _ => none
  | fuel + 1, k, ctx, t =>
    match t with
    | .univS l => if l < k then some (.univS (l + 1)) else none
    | .univF l => if l < k then some (.univF (l + 1)) else none
    | .boolS => if 0 < k then some (.univS 0) else none
    | .boolF => if 0 < k then some (.univF 0) else none
    | .trueF => if 0 < k then some .boolF else none
    | .falseF => if 0 < k then some .boolF else none
    | .var idx =>
      match listGet? ctx idx with
      | some ty => some (shift (idx + 1) 0 ty)
      | none => none
    | .liftFtoS inner =>
      match extractUnivF fuel (infer fuel k ctx inner) with
      | some l => some (.univS l)
      | none => none
    | .piF dom cod =>
      match extractUnivF fuel (infer fuel k ctx dom) with
      | none => none
      | some l1 =>
        match extractUnivF fuel (infer fuel k (dom :: ctx) cod) with
        | none => none
        | some l2 => some (.univF (max l1 l2))
    | .piS dom cod =>
      match extractUnivS fuel (infer fuel k ctx dom) with
      | none => none
      | some l1 =>
        match extractUnivS fuel (infer fuel k (dom :: ctx) cod) with
        | none => none
        | some l2 => some (.univS (max l1 l2))
    | .lamF dom body =>
      match extractUnivF fuel (infer fuel k ctx dom) with
      | none => none
      | some _ =>
        match infer fuel k (dom :: ctx) body with
        | none => none
        | some bodyTy =>
          match extractUnivF fuel (infer fuel k (dom :: ctx) bodyTy) with
          | none => none
          | some _ => some (.piF dom bodyTy)
    | .lamS dom body =>
      match extractUnivS fuel (infer fuel k ctx dom) with
      | none => none
      | some _ =>
        match infer fuel k (dom :: ctx) body with
        | none => none
        | some bodyTy =>
          match extractUnivS fuel (infer fuel k (dom :: ctx) bodyTy) with
          | none => none
          | some _ => some (.piS dom bodyTy)
    | .appF fn arg =>
      match infer fuel k ctx fn with
      | none => none
      | some fnTy =>
        match whnf fuel fnTy with
        | none => none
        | some wfnTy =>
          match asPiF? wfnTy with
          | none => none
          | some (dom, cod) =>
            match infer fuel k ctx arg with
            | none => none
            | some argTy =>
              if isDefEq fuel argTy dom then some (subst 0 arg cod) else none
    | .appS fn arg =>
      match infer fuel k ctx fn with
      | none => none
      | some fnTy =>
        match whnf fuel fnTy with
        | none => none
        | some wfnTy =>
          match asPiS? wfnTy with
          | none => none
          | some (dom, cod) =>
            match infer fuel k ctx arg with
            | none => none
            | some argTy =>
              if isDefEq fuel argTy dom then some (subst 0 arg cod) else none
    | .innerUnivalence arg =>
      match extractUnivF fuel (infer fuel k ctx arg) with
      | some l => some (.univF l)
      | none => none
    | .innerCoalgebraNu arg =>
      match extractUnivF fuel (infer fuel k ctx arg) with
      | some l => some (.univF l)
      | none => none
    | .outerStrictEq lhs rhs =>
      match infer fuel k ctx lhs with
      | none => none
      | some t1 =>
        match infer fuel k ctx rhs with
        | none => none
        | some t2 =>
          if isDefEq fuel t1 t2 then
            match extractUnivS fuel (infer fuel k ctx t1) with
            | some l => some (.univS l)
            | none => none
          else none
    | .smallnessReplacement arg =>
      match extractUnivS fuel (infer fuel k ctx arg) with
      | some l => some (.univS l)
      | none => none

/-- Bidirectional check: verify `ty` is a valid type (in `UnivF` or `UnivS`) and `t : ty`. -/
def check (fuel k : Nat) (ctx : List Term) (t ty : Term) : Bool :=
  match infer fuel k ctx ty with
  | none => false
  | some sort =>
    match whnf fuel sort with
    | none => false
    | some wsort =>
      if !isValidSort wsort then false
      else
        match infer fuel k ctx t with
        | some inferred => isDefEq fuel inferred ty
        | none => false

/-- Purely boolean certificate verification (for fast kernel `rfl` in `CertChecks`).
Checks schema, topological DAG order, strata flags, arena decoding, and 2LTT typing. -/
def checkCert (fuel : Nat) (c : Cert) : Bool :=
  c.schema == "kernel-arena.2ltt.v1" &&
    Arena.checkTopoBool c.nodes c.goalTypeNode c.proofTermNode &&
    (Arena.computeStrataFlags c.nodes c.proofTermNode == c.strataFlags) &&
    match Arena.decodeArena c.nodes with
    | none => false
    | some terms =>
      match terms[c.goalTypeNode]? with
      | none => false
      | some goalTerm =>
        match terms[c.proofTermNode]? with
        | none => false
        | some proofTerm => check fuel c.universeDepthK [] proofTerm goalTerm

/-- Full CLI verification including canonical SHA-256 arena hash check and structured errors. -/
def verifyCert (fuel : Nat) (c : Cert) : Except CheckError Unit := do
  if c.schema != "kernel-arena.2ltt.v1" then
    .error (.eSchemaError s!"unsupported schema '{c.schema}', expected 'kernel-arena.2ltt.v1'")
  Arena.checkTopo c.nodes c.goalTypeNode c.proofTermNode
  Arena.verifyArenaHash c
  Arena.verifyStrataFlags c
  let some terms := Arena.decodeArena c.nodes
    | .error (.eTopoCycle "failed to decode arena nodes")
  let some goalTerm := terms[c.goalTypeNode]?
    | .error (.eTopoCycle s!"invalid goal_type_node {c.goalTypeNode}")
  let some proofTerm := terms[c.proofTermNode]?
    | .error (.eTopoCycle s!"invalid proof_term_node {c.proofTermNode}")
  if check fuel c.universeDepthK [] proofTerm goalTerm then
    .ok ()
  else
    .error (.eTypecheckFail s!"2LTT typechecking failed for '{c.declName}' with fuel={fuel}")

end Check
end KernelArena
