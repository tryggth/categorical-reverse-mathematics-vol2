/-
Arena topological validation, canonical hashing, strata flag aggregation, and AST decoding.
Pure structural recursion (`List`/`Array`) so kernel `rfl` evaluates without `ForIn`/`Id.run`.
-/
import KernelArena.AST
import KernelArena.SHA256

namespace KernelArena
namespace Arena

def nodeChildren : NodeOp → List Nat
  | .univS _ => []
  | .univF _ => []
  | .boolS => []
  | .boolF => []
  | .trueF => []
  | .falseF => []
  | .var _ => []
  | .piS d c => [d, c]
  | .piF d c => [d, c]
  | .lamS d b => [d, b]
  | .lamF d b => [d, b]
  | .appS f a => [f, a]
  | .appF f a => [f, a]
  | .liftFtoS i => [i]
  | .innerUnivalence a => [a]
  | .innerCoalgebraNu a => [a]
  | .outerStrictEq l r => [l, r]
  | .smallnessReplacement a => [a]

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
  | node :: rest, idx => do
    if node.id != idx then
      .error (.eTopoCycle s!"non-canonical node id {node.id} at slot {idx}")
    for child in nodeChildren node.op do
      if child >= node.id then
        .error (.eTopoCycle s!"topological violation at node {node.id}: child {child} >= {node.id}")
    checkNodesTopoExcept rest (idx + 1)

/-- Single `O(|V|)` pass validating `node.id == idx`, `child < node.id`, and valid root indices. -/
def checkTopo (nodes : Array ArenaNode) (goalId proofId : Nat) : Except CheckError Unit := do
  if nodes.size == 0 then
    .error (.eTopoCycle "empty node arena")
  if goalId >= nodes.size then
    .error (.eTopoCycle s!"goal_type_node {goalId} out of bounds (size={nodes.size})")
  if proofId >= nodes.size then
    .error (.eTopoCycle s!"proof_term_node {proofId} out of bounds (size={nodes.size})")
  checkNodesTopoExcept nodes.toList 0

/-- Deterministic canonical serialization hashed into `sha256_arena`. -/
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
  if computed == c.sha256Arena then
    .ok ()
  else
    .error (.eHashMismatch s!"expected sha256_arena={computed}, got {c.sha256Arena}")

private def mergeStrataFlag (acc : StrataFlags) : NodeOp → StrataFlags
  | .univS _ => acc
  | .univF _ => acc
  | .boolS => acc
  | .boolF => acc
  | .trueF => acc
  | .falseF => acc
  | .var _ => acc
  | .piS _ _ => acc
  | .piF _ _ => acc
  | .lamS _ _ => acc
  | .lamF _ _ => acc
  | .appS _ _ => acc
  | .appF _ _ => acc
  | .liftFtoS _ => acc
  | .innerUnivalence _ => { acc with innerUnivalenceV := true }
  | .innerCoalgebraNu _ => { acc with innerCoalgebraNu := true }
  | .outerStrictEq _ _ => { acc with outerStrictEq := true }
  | .smallnessReplacement _ => { acc with smallnessReplacement := true }

private def collectConeStrata : List ArenaNode → List Nat → StrataFlags → StrataFlags
  | [], _, acc => acc
  | node :: rest, needed, acc =>
    if needed.contains node.id then
      collectConeStrata rest (nodeChildren node.op ++ needed) (mergeStrataFlag acc node.op)
    else
      collectConeStrata rest needed acc

/-- Compute actual `StrataFlags` over the transitive dependency cone of `rootId`.
Traverses `nodes` in reverse order; valid whenever `child_id < node.id`. -/
def computeStrataFlags (nodes : Array ArenaNode) (rootId : Nat) : StrataFlags :=
  if rootId >= nodes.size then
    {}
  else
    collectConeStrata nodes.toList.reverse [rootId] {}

def verifyStrataFlags (c : Cert) : Except CheckError Unit :=
  let actual := computeStrataFlags c.nodes c.proofTermNode
  if actual == c.strataFlags then
    .ok ()
  else
    .error (.eStrataMismatch s!"computed strata {repr actual} != declared {repr c.strataFlags}")

private def optPair {α β γ : Type} (x : Option α) (y : Option β) (f : α → β → γ) : Option γ :=
  match x with
  | none => none
  | some a =>
    match y with
    | none => none
    | some b => some (f a b)

private def optSingle {α γ : Type} (x : Option α) (f : α → γ) : Option γ :=
  match x with
  | none => none
  | some a => some (f a)

private def decodeNode (decoded : Array Term) (op : NodeOp) : Option Term :=
  match op with
  | .univS l => some (.univS l)
  | .univF l => some (.univF l)
  | .boolS => some .boolS
  | .boolF => some .boolF
  | .trueF => some .trueF
  | .falseF => some .falseF
  | .var k => some (.var k)
  | .piS d c => optPair decoded[d]? decoded[c]? .piS
  | .piF d c => optPair decoded[d]? decoded[c]? .piF
  | .lamS d b => optPair decoded[d]? decoded[b]? .lamS
  | .lamF d b => optPair decoded[d]? decoded[b]? .lamF
  | .appS f a => optPair decoded[f]? decoded[a]? .appS
  | .appF f a => optPair decoded[f]? decoded[a]? .appF
  | .liftFtoS i => optSingle decoded[i]? .liftFtoS
  | .innerUnivalence a => optSingle decoded[a]? .innerUnivalence
  | .innerCoalgebraNu a => optSingle decoded[a]? .innerCoalgebraNu
  | .outerStrictEq l r => optPair decoded[l]? decoded[r]? .outerStrictEq
  | .smallnessReplacement a => optSingle decoded[a]? .smallnessReplacement

private def decodeArenaAux (acc : Array Term) (idx : Nat) : List ArenaNode → Option (Array Term)
  | [] => some acc
  | node :: rest =>
    if node.id != idx then
      none
    else
      match decodeNode acc node.op with
      | some t => decodeArenaAux (acc.push t) (idx + 1) rest
      | none => none

/-- Single-pass `O(|V|)` bottom-up arena decoding (requires `child_id < node.id`). -/
def decodeArena (nodes : Array ArenaNode) : Option (Array Term) :=
  decodeArenaAux #[] 0 nodes.toList

end Arena
end KernelArena
