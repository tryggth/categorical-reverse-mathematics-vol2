/-
Pure-Init recursive-descent JSON parser for `kernel-arena.2ltt.v1` certificates.
Zero `partial`, zero external dependencies.
-/
import KernelArena.AST

namespace KernelArena
namespace CertParser

inductive JsonVal where
  | null
  | bool (b : Bool)
  | nat (n : Nat)
  | str (s : String)
  | arr (xs : Array JsonVal)
  | obj (fields : List (String × JsonVal))
  deriving Repr, Inhabited

private def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\r' || c == '\t'

private def skipWs (chars : Array Char) (idx : Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, i => i
    | fuel + 1, i =>
      match chars[i]? with
      | some c => if isSpace c then go fuel (i + 1) else i
      | none => i
  go (chars.size - idx + 1) idx

private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def parseStringAux (chars : Array Char) : Nat → Nat → String → Except String (String × Nat)
  | 0, _, _ => .error "unterminated string (fuel exhausted)"
  | fuel + 1, i, acc =>
    match chars[i]? with
    | none => .error "unterminated JSON string"
    | some '"' => .ok (acc, i + 1)
    | some '\\' =>
      match chars[i + 1]? with
      | none => .error "unterminated escape in JSON string"
      | some '"' => parseStringAux chars fuel (i + 2) (acc.push '"')
      | some '\\' => parseStringAux chars fuel (i + 2) (acc.push '\\')
      | some '/' => parseStringAux chars fuel (i + 2) (acc.push '/')
      | some 'b' => parseStringAux chars fuel (i + 2) (acc.push '\x08')
      | some 'f' => parseStringAux chars fuel (i + 2) (acc.push '\x0c')
      | some 'n' => parseStringAux chars fuel (i + 2) (acc.push '\n')
      | some 'r' => parseStringAux chars fuel (i + 2) (acc.push '\r')
      | some 't' => parseStringAux chars fuel (i + 2) (acc.push '\t')
      | some 'u' =>
        match chars[i + 2]?, chars[i + 3]?, chars[i + 4]?, chars[i + 5]? with
        | some h1, some h2, some h3, some h4 =>
          match hexVal h1, hexVal h2, hexVal h3, hexVal h4 with
          | some d1, some d2, some d3, some d4 =>
            let code := d1 * 4096 + d2 * 256 + d3 * 16 + d4
            parseStringAux chars fuel (i + 6) (acc.push (Char.ofNat code))
          | _, _, _, _ => .error "invalid \\uXXXX escape"
        | _, _, _, _ => .error "truncated \\uXXXX escape"
      | some c => .error s!"unsupported JSON escape '\\{c}'"
    | some c => parseStringAux chars fuel (i + 1) (acc.push c)

private def parseNatAux (chars : Array Char) : Nat → Nat → Nat → Nat → Except String (Nat × Nat)
  | 0, i, acc, len => if len == 0 then .error "empty number" else .ok (acc, i)
  | fuel + 1, i, acc, len =>
    match chars[i]? with
    | some c =>
      if '0' ≤ c && c ≤ '9' then
        parseNatAux chars fuel (i + 1) (acc * 10 + (c.toNat - '0'.toNat)) (len + 1)
      else if len == 0 then
        .error s!"expected digit at index {i}, got '{c}'"
      else
        .ok (acc, i)
    | none =>
      if len == 0 then .error "unexpected EOF while parsing integer" else .ok (acc, i)

private def matchKeyword (chars : Array Char) (idx : Nat) (kw : String) : Bool :=
  let kwChars := kw.toList
  let rec go : List Char → Nat → Bool
    | [], _ => true
    | c :: cs, i =>
      match chars[i]? with
      | some c' => c == c' && go cs (i + 1)
      | none => false
  go kwChars idx

mutual
  private def parseVal (chars : Array Char) : Nat → Nat → Except String (JsonVal × Nat)
    | 0, _ => .error "JSON parser fuel exhausted"
    | fuel + 1, idx =>
      let i := skipWs chars idx
      match chars[i]? with
      | none => .error "unexpected end of JSON input"
      | some '"' => do
        let (s, next) ← parseStringAux chars (chars.size + 1) (i + 1) ""
        .ok (.str s, next)
      | some '[' => parseArray chars fuel (skipWs chars (i + 1)) #[]
      | some '{' => parseObject chars fuel (skipWs chars (i + 1)) []
      | some 't' =>
        if matchKeyword chars i "true" then .ok (.bool true, i + 4)
        else .error s!"invalid token at index {i}"
      | some 'f' =>
        if matchKeyword chars i "false" then .ok (.bool false, i + 5)
        else .error s!"invalid token at index {i}"
      | some 'n' =>
        if matchKeyword chars i "null" then .ok (.null, i + 4)
        else .error s!"invalid token at index {i}"
      | some c =>
        if '0' ≤ c && c ≤ '9' then do
          let (n, next) ← parseNatAux chars (chars.size + 1) i 0 0
          .ok (.nat n, next)
        else
          .error s!"unexpected character '{c}' at index {i}"

  private def parseArray (chars : Array Char) : Nat → Nat → Array JsonVal → Except String (JsonVal × Nat)
    | 0, _, _ => .error "JSON array parser fuel exhausted"
    | fuel + 1, i, acc =>
      match chars[i]? with
      | some ']' => .ok (.arr acc, i + 1)
      | _ => do
        let (v, next) ← parseVal chars fuel i
        let j := skipWs chars next
        match chars[j]? with
        | some ',' => parseArray chars fuel (skipWs chars (j + 1)) (acc.push v)
        | some ']' => .ok (.arr (acc.push v), j + 1)
        | some c => .error s!"expected ',' or ']' in array at {j}, got '{c}'"
        | none => .error "unterminated JSON array"

  private def parseObject (chars : Array Char) : Nat → Nat → List (String × JsonVal) → Except String (JsonVal × Nat)
    | 0, _, _ => .error "JSON object parser fuel exhausted"
    | fuel + 1, i, acc =>
      match chars[i]? with
      | some '}' => .ok (.obj acc.reverse, i + 1)
      | some '"' => do
        let (k, nextK) ← parseStringAux chars (chars.size + 1) (i + 1) ""
        let colonIdx := skipWs chars nextK
        match chars[colonIdx]? with
        | some ':' =>
          let (v, nextV) ← parseVal chars fuel (colonIdx + 1)
          let j := skipWs chars nextV
          match chars[j]? with
          | some ',' => parseObject chars fuel (skipWs chars (j + 1)) ((k, v) :: acc)
          | some '}' => .ok (.obj ((k, v) :: acc).reverse, j + 1)
          | some c => .error s!"expected ',' or '}}' in object at {j}, got '{c}'"
          | none => .error "unterminated JSON object"
        | _ => .error s!"expected ':' after object key '{k}' at {colonIdx}"
      | some c => .error s!"expected string key or '}}' at {i}, got '{c}'"
      | none => .error "unterminated JSON object"
end

def parseJson (src : String) : Except CheckError JsonVal :=
  let chars := src.toList.toArray
  let fuel := chars.size * 4 + 64
  match parseVal chars fuel 0 with
  | .error e => .error (.eParseError e)
  | .ok (v, next) =>
    let rest := skipWs chars next
    if rest == chars.size then .ok v
    else .error (.eParseError s!"trailing characters at index {rest}")

private def getField (fields : List (String × JsonVal)) (k : String) : Except CheckError JsonVal :=
  match fields.find? (fun p => p.1 == k) with
  | some (_, v) => .ok v
  | none => .error (.eParseError s!"missing required JSON field '{k}'")

private def asObj : JsonVal → Except CheckError (List (String × JsonVal))
  | .obj fs => .ok fs
  | _ => .error (.eParseError "expected JSON object")

private def asStr : JsonVal → Except CheckError String
  | .str s => .ok s
  | _ => .error (.eParseError "expected JSON string")

private def asNat : JsonVal → Except CheckError Nat
  | .nat n => .ok n
  | _ => .error (.eParseError "expected JSON non-negative integer")

private def asBool : JsonVal → Except CheckError Bool
  | .bool b => .ok b
  | _ => .error (.eParseError "expected JSON boolean")

private def asArr : JsonVal → Except CheckError (Array JsonVal)
  | .arr xs => .ok xs
  | _ => .error (.eParseError "expected JSON array")

private def parseStrataFlags (v : JsonVal) : Except CheckError StrataFlags := do
  let fs ← asObj v
  let b1 ← getField fs "inner_univalence_V" >>= asBool
  let b2 ← getField fs "inner_coalgebra_nu" >>= asBool
  let b3 ← getField fs "outer_strict_eq" >>= asBool
  let b4 ← getField fs "smallness_replacement" >>= asBool
  .ok {
    innerUnivalenceV := b1
    innerCoalgebraNu := b2
    outerStrictEq := b3
    smallnessReplacement := b4
  }

private def parseNodeOp (opStr : String) (args : Array Nat) : Except CheckError NodeOp :=
  match opStr, args.toList with
  | "UnivS", [l] => .ok (.univS l)
  | "UnivF", [l] => .ok (.univF l)
  | "BoolS", [] => .ok .boolS
  | "BoolF", [] => .ok .boolF
  | "TrueF", [] => .ok .trueF
  | "FalseF", [] => .ok .falseF
  | "Var", [idx] => .ok (.var idx)
  | "PiS", [d, c] => .ok (.piS d c)
  | "PiF", [d, c] => .ok (.piF d c)
  | "LamS", [d, b] => .ok (.lamS d b)
  | "LamF", [d, b] => .ok (.lamF d b)
  | "AppS", [f, a] => .ok (.appS f a)
  | "AppF", [f, a] => .ok (.appF f a)
  | "LiftFtoS", [i] => .ok (.liftFtoS i)
  | "InnerUnivalenceV", [a] => .ok (.innerUnivalence a)
  | "InnerCoalgebraNu", [a] => .ok (.innerCoalgebraNu a)
  | "OuterStrictEq", [l, r] => .ok (.outerStrictEq l r)
  | "SmallnessReplacement", [a] => .ok (.smallnessReplacement a)
  | _, _ => .error (.eParseError s!"unknown or malformed NodeOp '{opStr}' with {args.size} args")

private def parseNode (v : JsonVal) : Except CheckError ArenaNode := do
  let fs ← asObj v
  let id ← getField fs "id" >>= asNat
  let opStr ← getField fs "op" >>= asStr
  let args ←
    match fs.find? (fun p => p.1 == "args") with
    | some (_, av) => (← asArr av).mapM asNat
    | none => .ok #[]
  let op ← parseNodeOp opStr args
  .ok { id := id, op := op }

def parseCertJson (src : String) : Except CheckError Cert := do
  let root ← parseJson src
  let fs ← asObj root
  let schema ← getField fs "schema" >>= asStr
  let declName ← getField fs "decl_name" >>= asStr
  let universeDepthK ← getField fs "universe_depth_k" >>= asNat
  let fuelHint ← getField fs "fuel_hint" >>= asNat
  let strataFlags ← getField fs "strata_flags" >>= parseStrataFlags
  let dimCtxArr ← getField fs "dim_contexts" >>= asArr
  let dimCtxs ← dimCtxArr.toList.mapM asStr
  let nodesArr ← getField fs "nodes" >>= asArr
  let nodes ← nodesArr.mapM parseNode
  let goalTypeNode ← getField fs "goal_type_node" >>= asNat
  let proofTermNode ← getField fs "proof_term_node" >>= asNat
  let sha256Arena ← getField fs "sha256_arena" >>= asStr
  .ok {
    schema := schema
    declName := declName
    universeDepthK := universeDepthK
    fuelHint := fuelHint
    strataFlags := strataFlags
    dimContexts := dimCtxs
    nodes := nodes
    goalTypeNode := goalTypeNode
    proofTermNode := proofTermNode
    sha256Arena := sha256Arena
  }

end CertParser
end KernelArena
