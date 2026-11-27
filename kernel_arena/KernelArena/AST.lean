/-
Zero-Mathlib 2LTT Kernel Arena AST, Cartesian Cubical Dimensions/Cofibrations,
and Certificate Data Types (Rung 1, ABI-additive `kernel-arena.2ltt.v1`).
-/

namespace KernelArena

/-- Expected or computed 2LTT stratification flags across the proof/goal cone. -/
structure StrataFlags where
  innerUnivalenceV : Bool := false
  innerCoalgebraNu : Bool := false
  outerStrictEq : Bool := false
  smallnessReplacement : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Cartesian interval dimension expressions (`0`, `1`, or de Bruijn dimension variable). -/
inductive Dim where
  | d0
  | d1
  | dvar (idx : Nat)
  deriving Repr, Inhabited

def beqDim (a b : Dim) : Bool := by
  cases a with
  | d0 => cases b with | d0 => exact true | _ => exact false
  | d1 => cases b with | d1 => exact true | _ => exact false
  | dvar i => cases b with | dvar j => exact i == j | _ => exact false

instance : BEq Dim := ⟨beqDim⟩

/-- Cartesian cofibration lattice formulas over equality atoms `r₁ = r₂`. -/
inductive Cof where
  | top
  | bot
  | eq (r1 r2 : Dim)
  | and (c1 c2 : Cof)
  | or (c1 c2 : Cof)
  deriving Repr, Inhabited

def beqCof (a b : Cof) : Bool := by
  cases a with
  | top => cases b with | top => exact true | _ => exact false
  | bot => cases b with | bot => exact true | _ => exact false
  | eq r1 r2 => cases b with | eq s1 s2 => exact beqDim r1 s1 && beqDim r2 s2 | _ => exact false
  | and x1 y1 => cases b with | and x2 y2 => exact beqCof x1 x2 && beqCof y1 y2 | _ => exact false
  | or x1 y1 => cases b with | or x2 y2 => exact beqCof x1 x2 && beqCof y1 y2 | _ => exact false

instance : BEq Cof := ⟨beqCof⟩

/-- Arena DAG node operations (Phase 0 bootstrap + Rung 1 Cartesian cubical 2LTT). -/
inductive NodeOp where
  -- Phase 0 bootstrap opcodes (ABI preserved)
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
  -- Rung 1 dimension & cofibration opcodes
  | dim0
  | dim1
  | dimVar (idx : Nat)
  | cofTop
  | cofBot
  | cofEq (r1 r2 : Nat)
  | cofAnd (c1 c2 : Nat)
  | cofOr (c1 c2 : Nat)
  -- Rung 1 outer strict level opcodes
  | unitS
  | starS
  | sigmaS (dom cod : Nat)
  | pairS (fst snd : Nat)
  | fstS (p : Nat)
  | sndS (p : Nat)
  | eqS (ty lhs rhs : Nat)
  | reflS (a : Nat)
  | uipS (ty lhs rhs p q : Nat)
  -- Rung 1 inner fibrant data opcodes
  | emptyF
  | emptyElimF (motive scrut : Nat)
  | unitF
  | starF
  | boolElimF (motive tCase fCase scrut : Nat)
  | sigmaF (dom cod : Nat)
  | pairF (fst snd : Nat)
  | fstF (p : Nat)
  | sndF (p : Nat)
  -- Rung 1 path types, Cartesian Kan operations, & V-Univalence
  | pathType (tyLine a0 a1 : Nat)
  | pathLam (body : Nat)
  | pathApp (p a0 a1 r : Nat)
  | coe (r r' tyLine m : Nat)
  | hcom (r r' ty u0 : Nat) (tubes : List (Nat × Nat))
  | vType (r a b f g sec ret : Nat)
  | vIn (r a b : Nat)
  | vProj (r a b f v : Nat)
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
  | eUnivOob (msg : String)
  | eLevelFirewall (msg : String)
  | ePathBoundary (msg : String)
  | eTubeMismatch (msg : String)
  deriving BEq, DecidableEq, Repr

namespace CheckError

def code : CheckError → String
  | .eSchemaError _ => "E_SCHEMA_ERROR"
  | .eTopoCycle _ => "E_TOPO_CYCLE"
  | .eHashMismatch _ => "E_HASH_MISMATCH"
  | .eStrataMismatch _ => "E_STRATA_MISMATCH"
  | .eTypecheckFail _ => "E_TYPECHECK_FAIL"
  | .eParseError _ => "E_PARSE_ERROR"
  | .eUnivOob _ => "E_UNIV_OOB"
  | .eLevelFirewall _ => "E_LEVEL_FIREWALL"
  | .ePathBoundary _ => "E_PATH_BOUNDARY"
  | .eTubeMismatch _ => "E_TUBE_MISMATCH"

def message : CheckError → String
  | .eSchemaError m => m
  | .eTopoCycle m => m
  | .eHashMismatch m => m
  | .eStrataMismatch m => m
  | .eTypecheckFail m => m
  | .eParseError m => m
  | .eUnivOob m => m
  | .eLevelFirewall m => m
  | .ePathBoundary m => m
  | .eTubeMismatch m => m

instance : ToString CheckError where
  toString e := s!"{e.code}: {e.message}"

end CheckError

mutual
  /-- Decoded 2LTT term tree (Phase 0 + Rung 1 Cartesian cubical). -/
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
    | unitS
    | starS
    | sigmaS (dom cod : Term)
    | pairS (fst snd : Term)
    | fstS (p : Term)
    | sndS (p : Term)
    | eqS (ty lhs rhs : Term)
    | reflS (a : Term)
    | uipS (ty lhs rhs p q : Term)
    | emptyF
    | emptyElimF (motive scrut : Term)
    | unitF
    | starF
    | boolElimF (motive tCase fCase scrut : Term)
    | sigmaF (dom cod : Term)
    | pairF (fst snd : Term)
    | fstF (p : Term)
    | sndF (p : Term)
    | pathType (tyLine a0 a1 : Term)
    | pathLam (body : Term)
    | pathApp (p a0 a1 : Term) (r : Dim)
    | coe (r r' : Dim) (tyLine m : Term)
    | hcom (r r' : Dim) (ty : Term) (tubes : Tubes) (u0 : Term)
    | vType (r : Dim) (a b f g sec ret : Term)
    | vIn (r : Dim) (a b : Term)
    | vProj (r : Dim) (a b f v : Term)
    deriving Repr

  /-- Tube list `(φ_j, i.u_j)` for Cartesian `hcom`. -/
  inductive Tubes where
    | nil
    | cons (cof : Cof) (body : Term) (rest : Tubes)
    deriving Repr
end

instance : Inhabited Term := ⟨.boolF⟩
instance : Inhabited Tubes := ⟨.nil⟩

mutual
  def beqTerm (a b : Term) : Bool := by
    cases a with
    | univS l1 => cases b with | univS l2 => exact l1 == l2 | _ => exact false
    | univF l1 => cases b with | univF l2 => exact l1 == l2 | _ => exact false
    | boolS => cases b with | boolS => exact true | _ => exact false
    | boolF => cases b with | boolF => exact true | _ => exact false
    | trueF => cases b with | trueF => exact true | _ => exact false
    | falseF => cases b with | falseF => exact true | _ => exact false
    | var i1 => cases b with | var i2 => exact i1 == i2 | _ => exact false
    | piS d1 c1 => cases b with | piS d2 c2 => exact beqTerm d1 d2 && beqTerm c1 c2 | _ => exact false
    | piF d1 c1 => cases b with | piF d2 c2 => exact beqTerm d1 d2 && beqTerm c1 c2 | _ => exact false
    | lamS d1 b1 => cases b with | lamS d2 b2 => exact beqTerm d1 d2 && beqTerm b1 b2 | _ => exact false
    | lamF d1 b1 => cases b with | lamF d2 b2 => exact beqTerm d1 d2 && beqTerm b1 b2 | _ => exact false
    | appS f1 a1 => cases b with | appS f2 a2 => exact beqTerm f1 f2 && beqTerm a1 a2 | _ => exact false
    | appF f1 a1 => cases b with | appF f2 a2 => exact beqTerm f1 f2 && beqTerm a1 a2 | _ => exact false
    | liftFtoS x1 => cases b with | liftFtoS x2 => exact beqTerm x1 x2 | _ => exact false
    | innerUnivalence x1 => cases b with | innerUnivalence x2 => exact beqTerm x1 x2 | _ => exact false
    | innerCoalgebraNu x1 => cases b with | innerCoalgebraNu x2 => exact beqTerm x1 x2 | _ => exact false
    | outerStrictEq l1 r1 => cases b with | outerStrictEq l2 r2 => exact beqTerm l1 l2 && beqTerm r1 r2 | _ => exact false
    | smallnessReplacement x1 => cases b with | smallnessReplacement x2 => exact beqTerm x1 x2 | _ => exact false
    | unitS => cases b with | unitS => exact true | _ => exact false
    | starS => cases b with | starS => exact true | _ => exact false
    | sigmaS d1 c1 => cases b with | sigmaS d2 c2 => exact beqTerm d1 d2 && beqTerm c1 c2 | _ => exact false
    | pairS a1 b1 => cases b with | pairS a2 b2 => exact beqTerm a1 a2 && beqTerm b1 b2 | _ => exact false
    | fstS p1 => cases b with | fstS p2 => exact beqTerm p1 p2 | _ => exact false
    | sndS p1 => cases b with | sndS p2 => exact beqTerm p1 p2 | _ => exact false
    | eqS t1 l1 r1 => cases b with | eqS t2 l2 r2 => exact beqTerm t1 t2 && beqTerm l1 l2 && beqTerm r1 r2 | _ => exact false
    | reflS a1 => cases b with | reflS a2 => exact beqTerm a1 a2 | _ => exact false
    | uipS t1 l1 r1 p1 q1 => cases b with
      | uipS t2 l2 r2 p2 q2 =>
        exact beqTerm t1 t2 && beqTerm l1 l2 && beqTerm r1 r2 && beqTerm p1 p2 && beqTerm q1 q2
      | _ => exact false
    | emptyF => cases b with | emptyF => exact true | _ => exact false
    | emptyElimF m1 s1 => cases b with | emptyElimF m2 s2 => exact beqTerm m1 m2 && beqTerm s1 s2 | _ => exact false
    | unitF => cases b with | unitF => exact true | _ => exact false
    | starF => cases b with | starF => exact true | _ => exact false
    | boolElimF m1 t1 f1 s1 => cases b with
      | boolElimF m2 t2 f2 s2 => exact beqTerm m1 m2 && beqTerm t1 t2 && beqTerm f1 f2 && beqTerm s1 s2
      | _ => exact false
    | sigmaF d1 c1 => cases b with | sigmaF d2 c2 => exact beqTerm d1 d2 && beqTerm c1 c2 | _ => exact false
    | pairF a1 b1 => cases b with | pairF a2 b2 => exact beqTerm a1 a2 && beqTerm b1 b2 | _ => exact false
    | fstF p1 => cases b with | fstF p2 => exact beqTerm p1 p2 | _ => exact false
    | sndF p1 => cases b with | sndF p2 => exact beqTerm p1 p2 | _ => exact false
    | pathType t1 a01 a11 => cases b with
      | pathType t2 a02 a12 => exact beqTerm t1 t2 && beqTerm a01 a02 && beqTerm a11 a12
      | _ => exact false
    | pathLam b1 => cases b with | pathLam b2 => exact beqTerm b1 b2 | _ => exact false
    | pathApp p1 a01 a11 r1 => cases b with
      | pathApp p2 a02 a12 r2 => exact beqDim r1 r2 && beqTerm p1 p2 && beqTerm a01 a02 && beqTerm a11 a12
      | _ => exact false
    | coe r1 r1' t1 m1 => cases b with
      | coe r2 r2' t2 m2 => exact beqDim r1 r2 && beqDim r1' r2' && beqTerm t1 t2 && beqTerm m1 m2
      | _ => exact false
    | hcom r1 r1' t1 tb1 u1 => cases b with
      | hcom r2 r2' t2 tb2 u2 =>
        exact beqDim r1 r2 && beqDim r1' r2' && beqTerm t1 t2 && beqTubes tb1 tb2 && beqTerm u1 u2
      | _ => exact false
    | vType r1 a1 b1 f1 g1 s1 rt1 => cases b with
      | vType r2 a2 b2 f2 g2 s2 rt2 =>
        exact beqDim r1 r2 && beqTerm a1 a2 && beqTerm b1 b2 && beqTerm f1 f2 &&
          beqTerm g1 g2 && beqTerm s1 s2 && beqTerm rt1 rt2
      | _ => exact false
    | vIn r1 a1 b1 => cases b with
      | vIn r2 a2 b2 => exact beqDim r1 r2 && beqTerm a1 a2 && beqTerm b1 b2
      | _ => exact false
    | vProj r1 a1 b1 f1 v1 => cases b with
      | vProj r2 a2 b2 f2 v2 =>
        exact beqDim r1 r2 && beqTerm a1 a2 && beqTerm b1 b2 && beqTerm f1 f2 && beqTerm v1 v2
      | _ => exact false

  def beqTubes (a b : Tubes) : Bool := by
    cases a with
    | nil => cases b with | nil => exact true | _ => exact false
    | cons c1 b1 r1 => cases b with
      | cons c2 b2 r2 => exact beqCof c1 c2 && beqTerm b1 b2 && beqTubes r1 r2
      | _ => exact false
end

instance : BEq Term := ⟨beqTerm⟩
instance : BEq Tubes := ⟨beqTubes⟩

/-- Decoded value slot inside an arena (`Term`, `Dim`, or `Cof`). -/
inductive ArenaVal where
  | term (t : Term)
  | dim (d : Dim)
  | cof (c : Cof)
  deriving Repr, Inhabited

end KernelArena
