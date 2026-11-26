/-
Zero-Mathlib 2LTT Kernel Arena AST & Certificate Data Types.
-/

namespace KernelArena

/-- Expected or computed 2LTT stratification flags across the proof cone. -/
structure StrataFlags where
  innerUnivalenceV : Bool := false
  innerCoalgebraNu : Bool := false
  outerStrictEq : Bool := false
  smallnessReplacement : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Phase 0 bootstrap 2LTT core arena node operations plus stratum markers. -/
inductive NodeOp where
  | univS (level : Nat)
  | univF (level : Nat)
  | boolS
  | boolF
  | trueF
  | falseF
  | var (idx : Nat)
  | piS (dom cod : Nat)
  | piF (dom cod : Nat)
  | lamS (dom body : Nat)
  | lamF (dom body : Nat)
  | appS (fn arg : Nat)
  | appF (fn arg : Nat)
  | liftFtoS (inner : Nat)
  | innerUnivalence (arg : Nat)
  | innerCoalgebraNu (arg : Nat)
  | outerStrictEq (lhs rhs : Nat)
  | smallnessReplacement (arg : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Indexed DAG node inside a flat topological arena. -/
structure ArenaNode where
  id : Nat
  op : NodeOp
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Complete `kernel-arena.2ltt.v1` certificate. -/
structure Cert where
  schema : String
  declName : String
  universeDepthK : Nat
  fuelHint : Nat
  strataFlags : StrataFlags
  dimContexts : List String
  nodes : Array ArenaNode
  goalTypeNode : Nat
  proofTermNode : Nat
  sha256Arena : String
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Structured verification error codes. -/
inductive CheckError where
  | eSchemaError (msg : String)
  | eTopoCycle (msg : String)
  | eHashMismatch (msg : String)
  | eStrataMismatch (msg : String)
  | eTypecheckFail (msg : String)
  | eParseError (msg : String)
  deriving BEq, DecidableEq, Repr

namespace CheckError

def code : CheckError → String
  | .eSchemaError _ => "E_SCHEMA_ERROR"
  | .eTopoCycle _ => "E_TOPO_CYCLE"
  | .eHashMismatch _ => "E_HASH_MISMATCH"
  | .eStrataMismatch _ => "E_STRATA_MISMATCH"
  | .eTypecheckFail _ => "E_TYPECHECK_FAIL"
  | .eParseError _ => "E_PARSE_ERROR"

def message : CheckError → String
  | .eSchemaError m => m
  | .eTopoCycle m => m
  | .eHashMismatch m => m
  | .eStrataMismatch m => m
  | .eTypecheckFail m => m
  | .eParseError m => m

instance : ToString CheckError where
  toString e := s!"{e.code}: {e.message}"

end CheckError

/-- Decoded 2LTT term tree. -/
inductive Term where
  | univS (level : Nat)
  | univF (level : Nat)
  | boolS
  | boolF
  | trueF
  | falseF
  | var (idx : Nat)
  | piS (dom cod : Term)
  | piF (dom cod : Term)
  | lamS (dom body : Term)
  | lamF (dom body : Term)
  | appS (fn arg : Term)
  | appF (fn arg : Term)
  | liftFtoS (inner : Term)
  | innerUnivalence (arg : Term)
  | innerCoalgebraNu (arg : Term)
  | outerStrictEq (lhs rhs : Term)
  | smallnessReplacement (arg : Term)
  deriving BEq, DecidableEq, Repr, Inhabited

end KernelArena
