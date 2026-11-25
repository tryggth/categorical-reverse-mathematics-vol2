import KernelArena

open KernelArena

private def runSelfTest : IO UInt32 := do
  -- 1. NIST FIPS 180-4 SHA-256 test vectors
  let emptyHash := SHA256.sha256Hex ""
  let expectedEmpty := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  if emptyHash != expectedEmpty then
    IO.eprintln s!"SELF_TEST_FAIL sha256('') = {emptyHash}"
    return 1

  let abcHash := SHA256.sha256Hex "abc"
  let expectedAbc := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  if abcHash != expectedAbc then
    IO.eprintln s!"SELF_TEST_FAIL sha256('abc') = {abcHash}"
    return 1

  -- 2. Valid 2LTT bootstrap identity certificate
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
  let validCert : Cert := {
    validBase with
    sha256Arena := SHA256.sha256Hex (Arena.canonicalArenaPayload validBase)
  }
  match Check.verifyCert validCert.fuelHint validCert with
  | .error e =>
    IO.eprintln s!"SELF_TEST_FAIL valid cert rejected: {e}"
    return 1
  | .ok () => pure ()

  if !Check.checkCert validCert.fuelHint validCert then
    IO.eprintln "SELF_TEST_FAIL checkCert returned false on validCert"
    return 1

  -- 3. E_TOPO_CYCLE check
  let cyclicCert : Cert := {
    validCert with
    nodes := #[
      { id := 0, op := .piF 1 0 },
      { id := 1, op := .boolF }
    ]
    goalTypeNode := 1
    proofTermNode := 1
  }
  match Check.verifyCert 32 cyclicCert with
  | .error (.eTopoCycle _) => pure ()
  | other =>
    IO.eprintln s!"SELF_TEST_FAIL expected E_TOPO_CYCLE, got {repr other}"
    return 1

  -- 4. E_HASH_MISMATCH check
  let badHashCert : Cert := {
    validCert with
    sha256Arena := "0000000000000000000000000000000000000000000000000000000000000000"
  }
  match Check.verifyCert 32 badHashCert with
  | .error (.eHashMismatch _) => pure ()
  | other =>
    IO.eprintln s!"SELF_TEST_FAIL expected E_HASH_MISMATCH, got {repr other}"
    return 1

  -- 5. E_STRATA_MISMATCH check
  let badStrataBase : Cert := {
    validBase with
    nodes := #[
      { id := 0, op := .boolS },
      { id := 1, op := .outerStrictEq 0 0 }
    ]
    goalTypeNode := 0
    proofTermNode := 1
    strataFlags := { outerStrictEq := false }
  }
  let badStrataCert : Cert := {
    badStrataBase with
    sha256Arena := SHA256.sha256Hex (Arena.canonicalArenaPayload badStrataBase)
  }
  match Check.verifyCert 32 badStrataCert with
  | .error (.eStrataMismatch _) => pure ()
  | other =>
    IO.eprintln s!"SELF_TEST_FAIL expected E_STRATA_MISMATCH, got {repr other}"
    return 1

  -- 6. E_TYPECHECK_FAIL checks (wrong proof type + strict->fibrant leakage)
  let badTypeBase : Cert := {
    validBase with
    nodes := #[
      { id := 0, op := .boolF },
      { id := 1, op := .trueF },
      { id := 2, op := .piF 0 0 }
    ]
    goalTypeNode := 2
    proofTermNode := 1
  }
  let badTypeCert : Cert := {
    badTypeBase with
    sha256Arena := SHA256.sha256Hex (Arena.canonicalArenaPayload badTypeBase)
  }
  match Check.verifyCert 32 badTypeCert with
  | .error (.eTypecheckFail _) => pure ()
  | other =>
    IO.eprintln s!"SELF_TEST_FAIL expected E_TYPECHECK_FAIL, got {repr other}"
    return 1

  let leakBase : Cert := {
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
  let leakCert : Cert := {
    leakBase with
    sha256Arena := SHA256.sha256Hex (Arena.canonicalArenaPayload leakBase)
  }
  match Check.verifyCert 32 leakCert with
  | .error (.eTypecheckFail _) => pure ()
  | other =>
    IO.eprintln s!"SELF_TEST_FAIL expected E_TYPECHECK_FAIL for S->F leak, got {repr other}"
    return 1

  IO.println "SELF_TEST_OK sha256=PASS valid=PASS topo=E_TOPO_CYCLE hash=E_HASH_MISMATCH strata=E_STRATA_MISMATCH typecheck=E_TYPECHECK_FAIL"
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
