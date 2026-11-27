/-
Audit compiled `HomotopyCRM` kernel environment for axioms, Four-Color Stratum,
forbidden trust/axiom/opaque constants, and the Hidden-Edge Gate.
-/
import Lean
import HomotopyCRM

open Lean

namespace AuditEnv

structure CertStrataFlags where
  innerUnivalenceV : Bool := false
  innerCoalgebraNu : Bool := false
  outerStrictEq : Bool := false
  smallnessReplacement : Bool := false
  deriving Inhabited

structure AuditNodeSpec where
  id : String
  formalPkg : String
  stratum : String
  declNames : List String
  expectedAxioms : List String
  allowedAncestors : List String
  certStrataFlags : Option CertStrataFlags := none
  deriving Inhabited

private def parseStringList (j : Json) : Except String (List String) := do
  let arr ← j.getArr?
  let xs ← arr.mapM Json.getStr?
  return xs.toList

private def getOptBoolField (j : Json) (k : String) : Bool :=
  match j.getObjVal? k with
  | .ok v => match v.getBool? with | .ok b => b | .error _ => false
  | .error _ => false

instance : FromJson AuditNodeSpec where
  fromJson? j := do
    let id ← (← j.getObjVal? "id").getStr?
    let formalPkg ← (← j.getObjVal? "formal_pkg").getStr?
    let stratum ← (← j.getObjVal? "stratum").getStr?
    let declNames ← parseStringList (← j.getObjVal? "decl_names")
    let expectedAxioms ← parseStringList (← j.getObjVal? "expected_axioms")
    let allowedAncestors ← parseStringList (← j.getObjVal? "allowed_ancestors")
    let certStrataFlags : Option CertStrataFlags :=
      match j.getObjVal? "cert_strata_flags" with
      | .ok cf => some {
          innerUnivalenceV := getOptBoolField cf "inner_univalence_V"
          innerCoalgebraNu := getOptBoolField cf "inner_coalgebra_nu"
          outerStrictEq := getOptBoolField cf "outer_strict_eq"
          smallnessReplacement := getOptBoolField cf "smallness_replacement"
        }
      | .error _ => none
    return {
      id := id
      formalPkg := formalPkg
      stratum := stratum
      declNames := declNames
      expectedAxioms := expectedAxioms
      allowedAncestors := allowedAncestors
      certStrataFlags := certStrataFlags
    }

private def insertUniqueSorted (xs : List String) (x : String) : List String :=
  if xs.contains x then xs else (x :: xs).mergeSort (· ≤ ·)

private def mergeUniqueSorted (xs ys : List String) : List String :=
  ys.foldl insertUniqueSorted (xs.mergeSort (· ≤ ·))

private def isForbiddenAxiom (ax : String) : Bool :=
  ax == "sorryAx" || ax == "Lean.ofReduceBool" || ax == "Lean.trustCompiler"

private def isAllowedStandardAxiom (ax : String) : Bool :=
  ax == "Quot.sound" || ax == "propext" || ax == "Classical.choice"

private def assignStratum (axs : List String) : String :=
  if axs.contains "Classical.choice" then "crimson"
  else if axs.isEmpty then "emerald"
  else "amber"

private def assignKernelArenaStratum (cf : CertStrataFlags) : String :=
  if cf.innerUnivalenceV || cf.innerCoalgebraNu then "sapphire"
  else if cf.outerStrictEq || cf.smallnessReplacement then "amber"
  else "emerald"

private def findOwner? (declOwners : Array (String × String)) (constStr : String) :
    Option String := Id.run do
  let mut bestLen : Nat := 0
  let mut bestOwner : Option String := none
  for (declStr, ownerId) in declOwners do
    let matchesDecl :=
      constStr == declStr || constStr.startsWith (declStr ++ ".")
    if matchesDecl && declStr.length > bestLen then
      bestLen := declStr.length
      bestOwner := some ownerId
  return bestOwner

private def isVol2Const (s : String) : Bool :=
  s.startsWith "HomotopyCRM.Vol2."

private def collectDirectUsed (env : Environment) (ci : ConstantInfo) : NameSet := Id.run do
  let mut used := ci.getUsedConstantsAsSet
  match ci with
  | .inductInfo iv =>
    for ctor in iv.ctors do
      used := used.insert ctor
      match env.find? ctor with
      | some cci => used := used ++ cci.getUsedConstantsAsSet
      | none => pure ()
  | _ => pure ()
  return used

private def jsonStrArray (xs : List String) : Json :=
  Json.arr (xs.toArray.map Json.str)

unsafe def runAudit (manifestPath : System.FilePath) : IO UInt32 := do
  unless ← manifestPath.pathExists do
    IO.eprintln s!"audit_env error: manifest not found: {manifestPath}"
    return 1
  let raw ← IO.FS.readFile manifestPath
  let j ← match Json.parse raw with
    | .ok v => pure v
    | .error e =>
      IO.eprintln s!"audit_env JSON parse error: {e}"
      return 1
  let nodesJson ← match j.getObjVal? "nodes" >>= (·.getArr?) with
    | .ok arr => pure arr
    | .error e =>
      IO.eprintln s!"audit_env manifest missing 'nodes' array: {e}"
      return 1
  let mut specs : Array AuditNodeSpec := #[]
  for item in nodesJson do
    match fromJson? (α := AuditNodeSpec) item with
    | .ok spec => specs := specs.push spec
    | .error e =>
      IO.eprintln s!"audit_env node spec decode error: {e}"
      return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `HomotopyCRM }] {}
  let mut declOwners : Array (String × String) := #[]
  for spec in specs do
    for d in spec.declNames do
      declOwners := declOwners.push (d, spec.id)
  let mut allOk := true
  let mut nodeReports : Array Json := #[]
  let mut globalErrors : Array String := #[]
  for spec in specs do
    let mut nodeErrors : Array String := #[]
    let mut actualAxioms : List String := []
    let mut checkedDecls : Nat := 0
    for declStr in spec.declNames do
      let declName := declStr.toName
      match env.find? declName with
      | none =>
        nodeErrors := nodeErrors.push s!"MISSING_DECL: {declStr}"
      | some ci =>
        checkedDecls := checkedDecls + 1
        match ci with
        | .axiomInfo _ =>
          nodeErrors := nodeErrors.push s!"FORBIDDEN_AXIOM_DECL: {declStr}"
        | .opaqueInfo _ =>
          nodeErrors := nodeErrors.push s!"FORBIDDEN_OPAQUE_DECL: {declStr}"
        | _ => pure ()
        let hasSorry := ci.type.hasSorry || (ci.value?.map (·.hasSorry)).getD false
        if hasSorry then
          nodeErrors := nodeErrors.push s!"SORRY_IN_EXPR: {declStr}"
        let (_, st) := ((Lean.CollectAxioms.collect declName).run env).run {}
        for axName in st.axioms do
          let axStr := axName.toString
          if isForbiddenAxiom axStr then
            nodeErrors := nodeErrors.push s!"FORBIDDEN_AXIOM: {declStr} uses {axStr}"
          else if !isAllowedStandardAxiom axStr then
            nodeErrors := nodeErrors.push s!"UNEXPECTED_CUSTOM_AXIOM: {declStr} uses {axStr}"
          actualAxioms := insertUniqueSorted actualAxioms axStr
        -- Reject custom axioms/opaques anywhere inside the visited Vol II cone
        for vName in st.visited.toList do
          let vStr := vName.toString
          if isVol2Const vStr then
            match env.find? vName with
            | some (.axiomInfo _) =>
              nodeErrors := nodeErrors.push s!"TRANSITIVE_AXIOM: {declStr} -> {vStr}"
            | some (.opaqueInfo _) =>
              nodeErrors := nodeErrors.push s!"TRANSITIVE_OPAQUE: {declStr} -> {vStr}"
            | _ => pure ()
        -- Hidden-Edge Gate across direct dependencies and visited Vol2 constants
        let usedDirect := collectDirectUsed env ci
        let allVol2Refs := mergeUniqueSorted
          (usedDirect.toList.map Name.toString |>.filter isVol2Const)
          (st.visited.toList.map Name.toString |>.filter isVol2Const)
        for uStr in allVol2Refs do
          match findOwner? declOwners uStr with
          | none =>
            nodeErrors := nodeErrors.push s!"UNREGISTERED_VOL2_CONST: {declStr} uses {uStr}"
          | some ownerId =>
            if !spec.allowedAncestors.contains ownerId then
              nodeErrors := nodeErrors.push s!"HIDDEN_EDGE: {declStr} \
                (node {spec.id}) uses {uStr} owned by {ownerId} outside lean_dep cone"
    let expectedSorted := spec.expectedAxioms.foldl insertUniqueSorted []
    if actualAxioms != expectedSorted then
      nodeErrors := nodeErrors.push
        s!"AXIOM_MISMATCH: expected={expectedSorted} actual={actualAxioms}"
    let computedStratum :=
      if !actualAxioms.isEmpty then assignStratum actualAxioms
      else match spec.certStrataFlags with
        | some cf => assignKernelArenaStratum cf
        | none => assignStratum actualAxioms
    if computedStratum != spec.stratum then
      nodeErrors := nodeErrors.push
        s!"STRATUM_MISMATCH: expected={spec.stratum} computed={computedStratum}"
    if !nodeErrors.isEmpty then
      allOk := false
      for err in nodeErrors do
        globalErrors := globalErrors.push s!"[{spec.id}] {err}"
    let recJson := Json.mkObj [
      ("id", Json.str spec.id),
      ("formal_pkg", Json.str spec.formalPkg),
      ("declared_stratum", Json.str spec.stratum),
      ("computed_stratum", Json.str computedStratum),
      ("expected_axioms", jsonStrArray expectedSorted),
      ("actual_axioms", jsonStrArray actualAxioms),
      ("checked_decls", Json.num checkedDecls),
      ("passed", Json.bool nodeErrors.isEmpty),
      ("errors", jsonStrArray nodeErrors.toList)
    ]
    nodeReports := nodeReports.push recJson
  let report := Json.mkObj [
    ("ok", Json.bool allOk),
    ("audited_nodes", Json.num specs.size),
    ("nodes", Json.arr nodeReports),
    ("errors", jsonStrArray globalErrors.toList)
  ]
  IO.println (Json.pretty report)
  return if allOk then 0 else 1

end AuditEnv

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [manifestPath] => AuditEnv.runAudit manifestPath
  | _ =>
    IO.eprintln "Usage: audit_env <audit_nodes_manifest.json>"
    return 1
