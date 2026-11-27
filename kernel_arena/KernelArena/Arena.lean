/-
Arena topological validation, canonical hashing, strata flag aggregation, and AST decoding.
Pure structural recursion (`List`/`Array`) so kernel `rfl` evaluates with zero axioms.
-/
import KernelArena.AST
import KernelArena.SHA256

namespace KernelArena
namespace Arena

private def flattenPairs : List (Nat × Nat) → List Nat
  | [] => []
  | (p, u) :: rest => p :: u :: flattenPairs rest

def nodeChildren : NodeOp → List Nat
  | .univS _ | .univF _ | .boolS | .boolF | .trueF | .falseF | .var _ => []
  | .piS d c | .piF d c => [d, c]
  | .lamS d b | .lamF d b => [d, b]
  | .appS f a | .appF f a => [f, a]
  | .liftFtoS i | .innerUnivalence i | .innerCoalgebraNu i | .smallnessReplacement i => [i]
  | .outerStrictEq l r => [l, r]
  | .dim0 | .dim1 | .dimVar _ | .cofTop | .cofBot => []
  | .cofEq r1 r2 | .cofAnd r1 r2 | .cofOr r1 r2 => [r1, r2]
  | .unitS | .starS => []
  | .sigmaS d c | .pairS d c => [d, c]
  | .fstS p | .sndS p => [p]
  | .eqS ty l r => [ty, l, r]
  | .reflS a => [a]
  | .uipS ty l r p q => [ty, l, r, p, q]
  | .emptyF | .unitF | .starF => []
  | .emptyElimF m s => [m, s]
  | .boolElimF m t f s => [m, t, f, s]
  | .sigmaF d c | .pairF d c => [d, c]
  | .fstF p | .sndF p => [p]
  | .pathType ty a0 a1 => [ty, a0, a1]
  | .pathLam b => [b]
  | .pathApp p a0 a1 r => [p, a0, a1, r]
  | .coe r r' ty m => [r, r', ty, m]
  | .hcom r r' ty u0 tubes => [r, r', ty, u0] ++ flattenPairs tubes
  | .vType r a b f g sec ret => [r, a, b, f, g, sec, ret]
  | .vIn r a b => [r, a, b]
  | .vProj r a b f v => [r, a, b, f, v]

private def canonPairs : List (Nat × Nat) → String
  | [] => ""
  | (p, u) :: rest => s!":{p}:{u}{canonPairs rest}"

def nodeOpCanon : NodeOp → String
  | .univS l => s!"UnivS:{l}"
  | .univF l => s!"UnivF:{l}"
  | .boolS => "BoolS"
  | .boolF => "BoolF"
  | .trueF => "TrueF"
  | .falseF => "FalseF"
  | .var idx => s!"Var:{idx}"
  | .piS d c => s!"PiS:{d}:{c}"
  | .piF d c => s!"PiF:{d}:{c}"
  | .lamS d b => s!"LamS:{d}:{b}"
  | .lamF d b => s!"LamF:{d}:{b}"
  | .appS f a => s!"AppS:{f}:{a}"
  | .appF f a => s!"AppF:{f}:{a}"
  | .liftFtoS i => s!"LiftFtoS:{i}"
  | .innerUnivalence a => s!"InnerUnivalenceV:{a}"
  | .innerCoalgebraNu a => s!"InnerCoalgebraNu:{a}"
  | .outerStrictEq l r => s!"OuterStrictEq:{l}:{r}"
  | .smallnessReplacement a => s!"SmallnessReplacement:{a}"
  | .dim0 => "Dim0"
  | .dim1 => "Dim1"
  | .dimVar idx => s!"DimVar:{idx}"
  | .cofTop => "CofTop"
  | .cofBot => "CofBot"
  | .cofEq r1 r2 => s!"CofEq:{r1}:{r2}"
  | .cofAnd c1 c2 => s!"CofAnd:{c1}:{c2}"
  | .cofOr c1 c2 => s!"CofOr:{c1}:{c2}"
  | .unitS => "UnitS"
  | .starS => "StarS"
  | .sigmaS d c => s!"SigmaS:{d}:{c}"
  | .pairS a b => s!"PairS:{a}:{b}"
  | .fstS p => s!"FstS:{p}"
  | .sndS p => s!"SndS:{p}"
  | .eqS ty l r => s!"EqS:{ty}:{l}:{r}"
  | .reflS a => s!"ReflS:{a}"
  | .uipS ty l r p q => s!"UIPS:{ty}:{l}:{r}:{p}:{q}"
  | .emptyF => "EmptyF"
  | .emptyElimF m s => s!"EmptyElimF:{m}:{s}"
  | .unitF => "UnitF"
  | .starF => "StarF"
  | .boolElimF m t f s => s!"BoolElimF:{m}:{t}:{f}:{s}"
  | .sigmaF d c => s!"SigmaF:{d}:{c}"
  | .pairF a b => s!"PairF:{a}:{b}"
  | .fstF p => s!"FstF:{p}"
  | .sndF p => s!"SndF:{p}"
  | .pathType ty a0 a1 => s!"PathType:{ty}:{a0}:{a1}"
  | .pathLam b => s!"PathLam:{b}"
  | .pathApp p a0 a1 r => s!"PathApp:{p}:{a0}:{a1}:{r}"
  | .coe r r' ty m => s!"Coe:{r}:{r'}:{ty}:{m}"
  | .hcom r r' ty u0 tubes => s!"HCom:{r}:{r'}:{ty}:{u0}{canonPairs tubes}"
  | .vType r a b f g sec ret => s!"VType:{r}:{a}:{b}:{f}:{g}:{sec}:{ret}"
  | .vIn r a b => s!"VIn:{r}:{a}:{b}"
  | .vProj r a b f v => s!"VProj:{r}:{a}:{b}:{f}:{v}"

private def checkNodesTopoAux : List ArenaNode → Nat → Bool
  | [], _ => true
  | node :: rest, idx =>
    node.id == idx &&
      (nodeChildren node.op).all (fun c => decide (c < idx)) &&
      checkNodesTopoAux rest (idx + 1)

/-- Pure boolean topological check (`node.id == idx`, `child < node.id`, valid roots). -/
def checkTopoBool (nodes : Array ArenaNode) (goalId proofId : Nat) : Bool :=
  nodes.size > 0 &&
    goalId < nodes.size &&
    proofId < nodes.size &&
    checkNodesTopoAux nodes.toList 0

private def checkNodesTopoExcept : List ArenaNode → Nat → Except CheckError Unit
  | [], _ => .ok ()
  | node :: rest, idx =>
    if node.id != idx then
      .error (.eTopoCycle s!"non-canonical node id {node.id} at slot {idx}")
    else if !(nodeChildren node.op).all (fun c => decide (c < node.id)) then
      .error (.eTopoCycle s!"topological violation at node {node.id}")
    else
      checkNodesTopoExcept rest (idx + 1)

/-- Single `O(|V|)` pass validating `node.id == idx`, `child < node.id`, and valid root indices. -/
def checkTopo (nodes : Array ArenaNode) (goalId proofId : Nat) : Except CheckError Unit :=
  if nodes.size == 0 then
    .error (.eTopoCycle "empty node arena")
  else if goalId >= nodes.size then
    .error (.eTopoCycle s!"goal_type_node {goalId} out of bounds (size={nodes.size})")
  else if proofId >= nodes.size then
    .error (.eTopoCycle s!"proof_term_node {proofId} out of bounds (size={nodes.size})")
  else
    checkNodesTopoExcept nodes.toList 0

/-- Deterministic canonical serialization hashed into `sha256_arena` (Phase 0 ABI preserved). -/
def canonicalArenaPayload (c : Cert) : String :=
  let header := [
    "KERNEL_ARENA_2LTT_V1",
    s!"decl_name={c.declName}",
    s!"universe_depth_k={c.universeDepthK}",
    s!"dim_contexts={String.intercalate "," c.dimContexts}",
    s!"goal_type_node={c.goalTypeNode}",
    s!"proof_term_node={c.proofTermNode}",
    s!"nodes={c.nodes.size}"
  ]
  let body := c.nodes.toList.map fun n => s!"{n.id}:{nodeOpCanon n.op}"
  String.intercalate "\n" (header ++ body)

def verifyArenaHash (c : Cert) : Except CheckError Unit :=
  let computed := SHA256.sha256Hex (canonicalArenaPayload c)
  if computed == c.sha256Arena then .ok ()
  else .error (.eHashMismatch s!"expected sha256_arena={computed}, got {c.sha256Arena}")

private def mergeStrataFlag (acc : StrataFlags) (op : NodeOp) : StrataFlags := by
  cases op with
  | innerUnivalence _ => exact { acc with innerUnivalenceV := true }
  | vType _ _ _ _ _ _ _ => exact { acc with innerUnivalenceV := true }
  | vIn _ _ _ => exact { acc with innerUnivalenceV := true }
  | vProj _ _ _ _ _ => exact { acc with innerUnivalenceV := true }
  | innerCoalgebraNu _ => exact { acc with innerCoalgebraNu := true }
  | outerStrictEq _ _ => exact { acc with outerStrictEq := true }
  | eqS _ _ _ => exact { acc with outerStrictEq := true }
  | reflS _ => exact { acc with outerStrictEq := true }
  | uipS _ _ _ _ _ => exact { acc with outerStrictEq := true }
  | smallnessReplacement _ => exact { acc with smallnessReplacement := true }
  | _ => exact acc

private def collectConeStrata : List ArenaNode → List Nat → StrataFlags → StrataFlags
  | [], _, acc => acc
  | node :: rest, needed, acc =>
    if needed.contains node.id then
      collectConeStrata rest (nodeChildren node.op ++ needed) (mergeStrataFlag acc node.op)
    else
      collectConeStrata rest needed acc

/-- Compute actual `StrataFlags` over the transitive dependency cone of `{goalId, proofId}`. -/
def computeStrataFlags (nodes : Array ArenaNode) (goalId proofId : Nat) : StrataFlags :=
  if goalId >= nodes.size || proofId >= nodes.size then {}
  else collectConeStrata nodes.toList.reverse [goalId, proofId] {}

def verifyStrataFlags (c : Cert) : Except CheckError Unit :=
  let actual := computeStrataFlags c.nodes c.goalTypeNode c.proofTermNode
  if actual == c.strataFlags then .ok ()
  else .error (.eStrataMismatch s!"computed strata {repr actual} != declared {repr c.strataFlags}")

private def getTerm? (decoded : Array ArenaVal) (idx : Nat) : Option Term := by
  cases decoded[idx]? with
  | some v => cases v with | term t => exact some t | _ => exact none
  | none => exact none

private def getDim? (decoded : Array ArenaVal) (idx : Nat) : Option Dim := by
  cases decoded[idx]? with
  | some v => cases v with | dim r => exact some r | _ => exact none
  | none => exact none

private def getCof? (decoded : Array ArenaVal) (idx : Nat) : Option Cof := by
  cases decoded[idx]? with
  | some v => cases v with | cof c => exact some c | _ => exact none
  | none => exact none

private def decodeTubes (decoded : Array ArenaVal) : List (Nat × Nat) → Option Tubes
  | [] => some .nil
  | (pId, uId) :: rest =>
    match getCof? decoded pId with
    | none => none
    | some p =>
      match getTerm? decoded uId with
      | none => none
      | some u =>
        match decodeTubes decoded rest with
        | none => none
        | some tb => some (.cons p u tb)

private def decT1 (d : Array ArenaVal) (a : Nat) (f : Term → Term) : Option ArenaVal :=
  match getTerm? d a with | some x => some (.term (f x)) | none => none

private def decT2 (d : Array ArenaVal) (a b : Nat) (f : Term → Term → Term) : Option ArenaVal :=
  match getTerm? d a with
  | none => none
  | some x => match getTerm? d b with | none => none | some y => some (.term (f x y))

private def decT3 (d : Array ArenaVal) (a b c : Nat) (f : Term → Term → Term → Term) : Option ArenaVal :=
  match getTerm? d a with
  | none => none
  | some x => match getTerm? d b with
    | none => none
    | some y => match getTerm? d c with | none => none | some z => some (.term (f x y z))

private def decT4 (d : Array ArenaVal) (a b c e : Nat) (f : Term → Term → Term → Term → Term) : Option ArenaVal :=
  match getTerm? d a with
  | none => none
  | some x => match getTerm? d b with
    | none => none
    | some y => match getTerm? d c with
      | none => none
      | some z => match getTerm? d e with | none => none | some w => some (.term (f x y z w))

private def optBind {α β : Type} (x : Option α) (f : α → Option β) : Option β :=
  match x with | none => none | some a => f a

private def decodeNode (d : Array ArenaVal) (op : NodeOp) : Option ArenaVal :=
  match op with
  | .univS l => some (.term (.univS l))
  | .univF l => some (.term (.univF l))
  | .boolS => some (.term .boolS)
  | .boolF => some (.term .boolF)
  | .trueF => some (.term .trueF)
  | .falseF => some (.term .falseF)
  | .var k => some (.term (.var k))
  | .piS a b => decT2 d a b .piS
  | .piF a b => decT2 d a b .piF
  | .lamS a b => decT2 d a b .lamS
  | .lamF a b => decT2 d a b .lamF
  | .appS f a => decT2 d f a .appS
  | .appF f a => decT2 d f a .appF
  | .liftFtoS i => decT1 d i .liftFtoS
  | .innerUnivalence a => decT1 d a .innerUnivalence
  | .innerCoalgebraNu a => decT1 d a .innerCoalgebraNu
  | .outerStrictEq l r => decT2 d l r .outerStrictEq
  | .smallnessReplacement a => decT1 d a .smallnessReplacement
  | .dim0 => some (.dim .d0)
  | .dim1 => some (.dim .d1)
  | .dimVar idx => some (.dim (.dvar idx))
  | .cofTop => some (.cof .top)
  | .cofBot => some (.cof .bot)
  | .cofEq r1 r2 => optBind (getDim? d r1) fun x => optBind (getDim? d r2) fun y => some (.cof (.eq x y))
  | .cofAnd c1 c2 => optBind (getCof? d c1) fun x => optBind (getCof? d c2) fun y => some (.cof (.and x y))
  | .cofOr c1 c2 => optBind (getCof? d c1) fun x => optBind (getCof? d c2) fun y => some (.cof (.or x y))
  | .unitS => some (.term .unitS)
  | .starS => some (.term .starS)
  | .sigmaS a b => decT2 d a b .sigmaS
  | .pairS a b => decT2 d a b .pairS
  | .fstS p => decT1 d p .fstS
  | .sndS p => decT1 d p .sndS
  | .eqS ty l r => decT3 d ty l r .eqS
  | .reflS a => decT1 d a .reflS
  | .uipS ty l r p q =>
    optBind (getTerm? d ty) fun t => optBind (getTerm? d l) fun x =>
    optBind (getTerm? d r) fun y => optBind (getTerm? d p) fun p' =>
    optBind (getTerm? d q) fun q' => some (.term (.uipS t x y p' q'))
  | .emptyF => some (.term .emptyF)
  | .emptyElimF m s => decT2 d m s .emptyElimF
  | .unitF => some (.term .unitF)
  | .starF => some (.term .starF)
  | .boolElimF m t f s => decT4 d m t f s .boolElimF
  | .sigmaF a b => decT2 d a b .sigmaF
  | .pairF a b => decT2 d a b .pairF
  | .fstF p => decT1 d p .fstF
  | .sndF p => decT1 d p .sndF
  | .pathType ty a0 a1 => decT3 d ty a0 a1 .pathType
  | .pathLam b => decT1 d b .pathLam
  | .pathApp p a0 a1 r =>
    optBind (getTerm? d p) fun p' => optBind (getTerm? d a0) fun x =>
    optBind (getTerm? d a1) fun y => optBind (getDim? d r) fun r' =>
    some (.term (.pathApp p' x y r'))
  | .coe r r' ty m =>
    optBind (getDim? d r) fun r1 => optBind (getDim? d r') fun r2 =>
    optBind (getTerm? d ty) fun t => optBind (getTerm? d m) fun m' =>
    some (.term (.coe r1 r2 t m'))
  | .hcom r r' ty u0 tubes =>
    optBind (getDim? d r) fun r1 => optBind (getDim? d r') fun r2 =>
    optBind (getTerm? d ty) fun t => optBind (decodeTubes d tubes) fun tb =>
    optBind (getTerm? d u0) fun u => some (.term (.hcom r1 r2 t tb u))
  | .vType r a b f g sec ret =>
    optBind (getDim? d r) fun r1 => optBind (getTerm? d a) fun a' =>
    optBind (getTerm? d b) fun b' => optBind (getTerm? d f) fun f' =>
    optBind (getTerm? d g) fun g' => optBind (getTerm? d sec) fun s' =>
    optBind (getTerm? d ret) fun rt' => some (.term (.vType r1 a' b' f' g' s' rt'))
  | .vIn r a b =>
    optBind (getDim? d r) fun r1 => optBind (getTerm? d a) fun a' =>
    optBind (getTerm? d b) fun b' => some (.term (.vIn r1 a' b'))
  | .vProj r a b f v =>
    optBind (getDim? d r) fun r1 => optBind (getTerm? d a) fun a' =>
    optBind (getTerm? d b) fun b' => optBind (getTerm? d f) fun f' =>
    optBind (getTerm? d v) fun v' => some (.term (.vProj r1 a' b' f' v'))

private def decodeArenaAux (acc : Array ArenaVal) (idx : Nat) : List ArenaNode → Option (Array ArenaVal)
  | [] => some acc
  | node :: rest =>
    if node.id != idx then none
    else
      match decodeNode acc node.op with
      | some v => decodeArenaAux (acc.push v) (idx + 1) rest
      | none => none

/-- Single-pass `O(|V|)` bottom-up arena decoding into `Term`/`Dim`/`Cof` values. -/
def decodeArena (nodes : Array ArenaNode) : Option (Array ArenaVal) :=
  decodeArenaAux #[] 0 nodes.toList

end Arena
end KernelArena
