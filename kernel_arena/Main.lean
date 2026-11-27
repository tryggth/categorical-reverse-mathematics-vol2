import KernelArena

open KernelArena

private def sealCert (c : Cert) : Cert :=
  let flags := Arena.computeStrataFlags c.nodes c.goalTypeNode c.proofTermNode
  let base := { c with strataFlags := flags }
  { base with sha256Arena := SHA256.sha256Hex (Arena.canonicalArenaPayload base) }

private def expectOk (label : String) (res : Except CheckError Unit) : IO Bool := do
  match res with
  | .ok () => return true
  | .error e =>
    IO.eprintln s!"SELF_TEST_FAIL [{label}] unexpected error: {e}"
    return false

private def expectCode (label expected : String) (res : Except CheckError Unit) : IO Bool := do
  match res with
  | .error e =>
    if e.code == expected then return true
    else
      IO.eprintln s!"SELF_TEST_FAIL [{label}] expected {expected}, got {e}"
      return false
  | .ok () =>
    IO.eprintln s!"SELF_TEST_FAIL [{label}] expected {expected}, got OK"
    return false

private def runSelfTest : IO UInt32 := do
  -- 1. NIST FIPS 180-4 SHA-256 test vectors
  if SHA256.sha256Hex "" != "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" then
    IO.eprintln "SELF_TEST_FAIL sha256('')"
    return 1
  if SHA256.sha256Hex "abc" != "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" then
    IO.eprintln "SELF_TEST_FAIL sha256('abc')"
    return 1

  -- 2. Cofibration Union-Find solver completeness & inconsistency checks
  let cTrans := Cof.and (.eq (.dvar 0) (.dvar 1)) (.eq (.dvar 1) .d0)
  if !Cofib.entails 2 cTrans (.eq (.dvar 0) .d0) then
    IO.eprintln "SELF_TEST_FAIL cofib transitivity (i=j & j=0 |- i=0)"
    return 1
  let cDnf := Cof.and (.or (.eq (.dvar 0) .d0) (.eq (.dvar 0) .d1)) (.eq (.dvar 0) (.dvar 1))
  if !Cofib.entails 2 cDnf (.or (.eq (.dvar 1) .d0) (.eq (.dvar 1) .d1)) then
    IO.eprintln "SELF_TEST_FAIL cofib DNF split"
    return 1
  let cIncons := Cof.and (.eq (.dvar 0) .d0) (.eq (.dvar 0) .d1)
  if !Cofib.isInconsistent 1 cIncons || !Cofib.entails 1 cIncons .bot then
    IO.eprintln "SELF_TEST_FAIL cofib inconsistency (i=0 & i=1 |- bot)"
    return 1
  if Cofib.entails 1 .top (.or (.eq (.dvar 0) .d0) (.eq (.dvar 0) .d1)) then
    IO.eprintln "SELF_TEST_FAIL Cartesian interval is non-discrete (top !|- i=0 \\/ i=1)"
    return 1

  -- 3. Phase 0 Bootstrap Identity Cert + kernel checkCert
  let validBase : Cert := {
    schema := "kernel-arena.2ltt.v1"
    declName := "TwoLTT.Bootstrap.id_boolF"
    universeDepthK := 1
    fuelHint := 64
    strataFlags := {}
    dimContexts := []
    nodes := #[
      { id := 0, op := .boolF },
      { id := 1, op := .var 0 },
      { id := 2, op := .piF 0 0 },
      { id := 3, op := .lamF 0 1 }
    ]
    goalTypeNode := 2
    proofTermNode := 3
    sha256Arena := ""
  }
  let validCert := sealCert validBase
  unless ← expectOk "valid_bootstrap" (Check.verifyCert validCert.fuelHint validCert) do return 1
  if !Check.checkCert validCert.fuelHint validCert then
    IO.eprintln "SELF_TEST_FAIL checkCert returned false on validCert"
    return 1

  -- 4. Phase 0 Negative Tests: E_TOPO_CYCLE, E_HASH_MISMATCH, E_STRATA_MISMATCH, E_TYPECHECK_FAIL
  let cyclicCert : Cert := {
    validCert with
    nodes := #[{ id := 0, op := .piF 1 0 }, { id := 1, op := .boolF }]
    goalTypeNode := 1
    proofTermNode := 1
  }
  unless ← expectCode "topo_cycle" "E_TOPO_CYCLE" (Check.verifyCert 32 cyclicCert) do return 1

  let badHashCert : Cert := {
    validCert with
    sha256Arena := "0000000000000000000000000000000000000000000000000000000000000000"
  }
  unless ← expectCode "hash_mismatch" "E_HASH_MISMATCH" (Check.verifyCert 32 badHashCert) do return 1

  let badStrataBase : Cert := {
    validBase with
    nodes := #[{ id := 0, op := .boolS }, { id := 1, op := .outerStrictEq 0 0 }]
    goalTypeNode := 0
    proofTermNode := 1
    strataFlags := { outerStrictEq := false }
  }
  let badStrataCert : Cert := {
    badStrataBase with
    sha256Arena := SHA256.sha256Hex (Arena.canonicalArenaPayload badStrataBase)
  }
  unless ← expectCode "strata_mismatch" "E_STRATA_MISMATCH" (Check.verifyCert 32 badStrataCert) do return 1

  let badTypeCert := sealCert {
    validBase with
    nodes := #[{ id := 0, op := .boolF }, { id := 1, op := .trueF }, { id := 2, op := .piF 0 0 }]
    goalTypeNode := 2
    proofTermNode := 1
  }
  unless ← expectCode "typecheck_fail" "E_TYPECHECK_FAIL" (Check.verifyCert 32 badTypeCert) do return 1

  -- 5. Rung 1 Negative Tests: E_UNIV_OOB, E_LEVEL_FIREWALL, E_PATH_BOUNDARY, E_TUBE_MISMATCH
  let oobCert := sealCert {
    validBase with
    universeDepthK := 1
    nodes := #[{ id := 0, op := .univF 2 }, { id := 1, op := .univF 1 }]
    goalTypeNode := 0
    proofTermNode := 1
  }
  unless ← expectCode "univ_oob" "E_UNIV_OOB" (Check.verifyCert 32 oobCert) do return 1

  let leakS2FCert := sealCert {
    validBase with
    nodes := #[
      { id := 0, op := .boolF },
      { id := 1, op := .liftFtoS 0 },
      { id := 2, op := .var 0 },
      { id := 3, op := .piF 1 0 },
      { id := 4, op := .lamF 1 2 }
    ]
    goalTypeNode := 3
    proofTermNode := 4
  }
  unless ← expectCode "firewall_s2f" "E_LEVEL_FIREWALL" (Check.verifyCert 32 leakS2FCert) do return 1

  let eqOnInnerCert := sealCert {
    validBase with
    nodes := #[
      { id := 0, op := .boolF },
      { id := 1, op := .trueF },
      { id := 2, op := .univS 0 },
      { id := 3, op := .eqS 0 1 1 }
    ]
    goalTypeNode := 2
    proofTermNode := 3
  }
  unless ← expectCode "firewall_eqs_inner" "E_LEVEL_FIREWALL" (Check.verifyCert 32 eqOnInnerCert) do return 1

  let badPathCert := sealCert {
    validBase with
    nodes := #[
      { id := 0, op := .boolF },
      { id := 1, op := .trueF },
      { id := 2, op := .falseF },
      { id := 3, op := .pathType 0 1 2 },
      { id := 4, op := .pathLam 1 }
    ]
    goalTypeNode := 3
    proofTermNode := 4
  }
  unless ← expectCode "path_boundary" "E_PATH_BOUNDARY" (Check.verifyCert 32 badPathCert) do return 1

  let badTubeCert := sealCert {
    validBase with
    nodes := #[
      { id := 0, op := .dim0 },
      { id := 1, op := .dim1 },
      { id := 2, op := .dimVar 0 },
      { id := 3, op := .cofEq 2 0 },
      { id := 4, op := .cofEq 2 1 },
      { id := 5, op := .boolF },
      { id := 6, op := .trueF },
      { id := 7, op := .falseF },
      { id := 8, op := .hcom 0 1 5 6 [(3, 7), (4, 6)] },
      { id := 9, op := .pathType 5 6 6 },
      { id := 10, op := .pathLam 8 }
    ]
    goalTypeNode := 9
    proofTermNode := 10
  }
  unless ← expectCode "tube_mismatch" "E_TUBE_MISMATCH" (Check.verifyCert 48 badTubeCert) do return 1

  -- 6. Positive Strict EqS/ReflS/UIPS test (sets outer_strict_eq = true)
  let uipCert := sealCert {
    validBase with
    declName := "TwoLTT.Rung1.strict_uip_test"
    nodes := #[
      { id := 0, op := .boolS },
      { id := 1, op := .var 0 },
      { id := 2, op := .eqS 0 1 1 },
      { id := 3, op := .reflS 1 },
      { id := 4, op := .eqS 2 3 3 },
      { id := 5, op := .uipS 0 1 1 3 3 },
      { id := 6, op := .piS 0 4 },
      { id := 7, op := .lamS 0 5 }
    ]
    goalTypeNode := 6
    proofTermNode := 7
  }
  if !uipCert.strataFlags.outerStrictEq then
    IO.eprintln "SELF_TEST_FAIL outerStrictEq flag not set on UIPS cert"
    return 1
  unless ← expectOk "uip_strict" (Check.verifyCert 64 uipCert) do return 1

  -- 7. Sapphire VType strata_flags detection + VType positive/mismatch checks
  let vBase : Cert := {
    validBase with
    declName := "TwoLTT.Rung1.vtype_sapphire_flag"
    universeDepthK := 2
    nodes := #[
      { id := 0, op := .dim0 },
      { id := 1, op := .boolF },
      { id := 2, op := .var 0 },
      { id := 3, op := .lamF 1 2 },
      { id := 4, op := .pathLam 2 },
      { id := 5, op := .lamF 1 4 },
      { id := 6, op := .vType 0 1 1 3 3 5 5 },
      { id := 7, op := .univF 0 }
    ]
    goalTypeNode := 7
    proofTermNode := 6
    strataFlags := { innerUnivalenceV := false }
  }
  let vBadStrata := { vBase with sha256Arena := SHA256.sha256Hex (Arena.canonicalArenaPayload vBase) }
  unless ← expectCode "vtype_strata_mismatch" "E_STRATA_MISMATCH" (Check.verifyCert 64 vBadStrata) do return 1

  let vOkCert := sealCert vBase
  if !vOkCert.strataFlags.innerUnivalenceV then
    IO.eprintln "SELF_TEST_FAIL innerUnivalenceV flag not set on VType cert"
    return 1
  unless ← expectOk "vtype_sapphire_ok" (Check.verifyCert 64 vOkCert) do return 1
  if !Check.checkCert 64 vOkCert then
    IO.eprintln "SELF_TEST_FAIL checkCert failed on vOkCert"
    return 1

  IO.println "SELF_TEST_OK sha256=PASS cofib=PASS bootstrap=PASS topo=E_TOPO_CYCLE hash=E_HASH_MISMATCH strata=E_STRATA_MISMATCH typecheck=E_TYPECHECK_FAIL oob=E_UNIV_OOB firewall=E_LEVEL_FIREWALL path=E_PATH_BOUNDARY tube=E_TUBE_MISMATCH uip=PASS sapphire=PASS"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => runSelfTest
  | ["verify", path] =>
    let fp : System.FilePath := path
    unless ← fp.pathExists do
      IO.eprintln s!"VERIFY_FAIL E_IO certificate not found: {path}"
      return 1
    let src ← IO.FS.readFile fp
    match CertParser.parseCertJson src with
    | .error e =>
      IO.eprintln s!"VERIFY_FAIL {e}"
      return 1
    | .ok cert =>
      match Check.verifyCert cert.fuelHint cert with
      | .error e =>
        IO.eprintln s!"VERIFY_FAIL {e}"
        return 1
      | .ok () =>
        IO.println s!"VERIFY_OK decl={cert.declName} depth_k={cert.universeDepthK} nodes={cert.nodes.size} sha256={cert.sha256Arena}"
        return 0
  | _ =>
    IO.eprintln "Usage: kernel-arena verify <cert.json> | kernel-arena --self-test"
    return 1
