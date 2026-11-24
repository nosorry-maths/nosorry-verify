/-
nosorry statement/axiom checker. leanprover/comparator, when configured, runs after it as an additional check.

Usage:  lean --run Compare.lean <ChallengeModule> <SolutionModule> <Target.decl.name> [neg]
With `neg` (a disproof), the solution must contain `<Namespace>.not_<name>` whose type is `¬ <reference type>`.
Both modules must already be compiled and reachable through LEAN_PATH. They are loaded into two *separate*
environments (without running any initializer), so the solution can never shadow the reference. With Mathlib each
environment takes ~3.5 GB, so the two never live in the same process: a child process (`export` mode) loads the
reference, extracts the target and the declarations of its statement closure, and writes them to a small file in
Lean's own .olean format; it exits, then this process reads that file and imports the solution. Peak ≈ one environment.

Checks
  1. the target exists in the solution and is a theorem;
  2. its type is structurally equal to the reference type. `sorry` holes in the reference type (from `answer(sorry)`)
     match any term; the substituted terms are reported (`answers`) so a person can judge them;
  3. statement closure: every constant the reference *statement* depends on — through types, definition bodies,
     inductive types, constructors and recursors, internal/auxiliary names and other modules included — exists in the
     solution environment with an identical declaration (kind, universe parameters, type, value, inductive shape);
  4. axioms in the dependency closure of the proof, and the constants that still contain `sorry` (open lemmas).
Prints one JSON object on stdout.
-/
import Lean
open Lean

partial def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | e => e

/-- Structural equality of a reference expression `t` and a solution expression `e`, up to proof irrelevance:
    where the reference uses a theorem (`rt` maps every theorem of the reference statement closure to its type,
    auxiliary `foo._proof_N` included), the solution may use any theorem of its own environment proving the same
    proposition, whatever its name. Lean elaborates proofs inside a statement into auxiliary theorems whose numbering
    can change with the rest of the file; two proofs of one proposition are definitionally equal, so the statement is
    the same. Everything else must be identical. -/
partial def eqvE (rt : NameMap Expr) (sol : Environment) (t e : Expr) : Bool :=
  match stripMData t, stripMData e with
  | .app f a, .app g b => eqvE rt sol f g && eqvE rt sol a b
  | .lam _ ty b _, .lam _ ty' b' _ => eqvE rt sol ty ty' && eqvE rt sol b b'
  | .forallE _ ty b _, .forallE _ ty' b' _ => eqvE rt sol ty ty' && eqvE rt sol b b'
  | .letE _ ty v b _, .letE _ ty' v' b' _ => eqvE rt sol ty ty' && eqvE rt sol v v' && eqvE rt sol b b'
  | .proj s i x, .proj s' i' y => s == s' && i == i' && eqvE rt sol x y
  | .const n1 ls1, .const n2 ls2 =>
      ls1 == ls2 && match rt.find? n1 with
        | some ty1 => match sol.find? n2 with
          | some (.thmInfo v) => eqvE rt sol ty1 (stripMData v.type)
          | _ => false
        | none => n1 == n2
  | t', e' => t' == e'

/-- `t` is the reference expression (may contain sorry holes), `e` the solution expression.
    The state collects the solution terms placed in the holes. -/
partial def tmatch (rt : NameMap Expr) (sol : Environment) (t e : Expr) : StateM (Array Expr) Bool := do
  let t := stripMData t
  let e := stripMData e
  if t.isAppOf ``sorryAx then
    modify (·.push e)
    return true
  match t, e with
  | .app f a, .app g b => return (← tmatch rt sol f g) && (← tmatch rt sol a b)
  | .lam _ ty b _, .lam _ ty' b' _ => return (← tmatch rt sol ty ty') && (← tmatch rt sol b b')
  | .forallE _ ty b _, .forallE _ ty' b' _ => return (← tmatch rt sol ty ty') && (← tmatch rt sol b b')
  | .letE _ ty v b _, .letE _ ty' v' b' _ =>
      return (← tmatch rt sol ty ty') && (← tmatch rt sol v v') && (← tmatch rt sol b b')
  | .proj s i x, .proj s' i' y => return s == s' && i == i' && (← tmatch rt sol x y)
  | _, _ => return eqvE rt sol t e

/-! ### Leaving the reference environment
The reference is loaded first and its memory regions are freed before the solution is imported (with Mathlib each
environment is ~3.5 GB). Everything kept from it is first copied into fresh objects. Metadata nodes (`mdata`) carry no
logical content and are stripped on both sides, so nothing kept can point into a freed region. -/

def copyStr (s : String) : String := String.ofList s.toList

partial def copyName : Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (copyName p) (copyStr s)
  | .num p n => .num (copyName p) (n + 0)

partial def copyLevel : Level → Level
  | .zero => .zero
  | .succ l => .succ (copyLevel l)
  | .max a b => .max (copyLevel a) (copyLevel b)
  | .imax a b => .imax (copyLevel a) (copyLevel b)
  | .param n => .param (copyName n)
  | .mvar m => .mvar ⟨copyName m.name⟩

/-- Fresh copy of an expression, without `mdata`. -/
partial def copyExpr : Expr → Expr
  | .bvar i => .bvar (i + 0)
  | .fvar f => .fvar ⟨copyName f.name⟩
  | .mvar m => .mvar ⟨copyName m.name⟩
  | .sort l => .sort (copyLevel l)
  | .const n ls => .const (copyName n) (ls.map copyLevel)
  | .app f a => .app (copyExpr f) (copyExpr a)
  | .lam n t b bi => .lam (copyName n) (copyExpr t) (copyExpr b) bi
  | .forallE n t b bi => .forallE (copyName n) (copyExpr t) (copyExpr b) bi
  | .letE n t v b nd => .letE (copyName n) (copyExpr t) (copyExpr v) (copyExpr b) nd
  | .lit (.natVal n) => .lit (.natVal (n + 0))
  | .lit (.strVal s) => .lit (.strVal (copyStr s))
  | .mdata _ e => copyExpr e
  | .proj s i e => .proj (copyName s) (i + 0) (copyExpr e)

/-- `mdata` removed everywhere (applied to the solution side so both sides are compared the same way). -/
partial def stripAll (e : Expr) : Expr := e.replace fun x => match x with | .mdata _ b => some (stripAll b) | _ => none

def copyNames (ns : List Name) : List Name := ns.map copyName

def copyHints : ReducibilityHints → ReducibilityHints
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular (h + 0)

/-- Fresh copy of a declaration. Theorem bodies are dropped: proofs are irrelevant to the statement. -/
def copyCI : ConstantInfo → ConstantInfo
  | .defnInfo v => .defnInfo { v with name := copyName v.name, levelParams := copyNames v.levelParams, type := copyExpr v.type,
                                      value := copyExpr v.value, all := copyNames v.all, hints := copyHints v.hints }
  | .thmInfo v => .thmInfo { v with name := copyName v.name, levelParams := copyNames v.levelParams, type := copyExpr v.type,
                                     value := .sort .zero, all := copyNames v.all }
  | .opaqueInfo v => .opaqueInfo { v with name := copyName v.name, levelParams := copyNames v.levelParams, type := copyExpr v.type,
                                           value := copyExpr v.value, all := copyNames v.all }
  | .axiomInfo v => .axiomInfo { v with name := copyName v.name, levelParams := copyNames v.levelParams, type := copyExpr v.type }
  | .quotInfo v => .quotInfo { v with name := copyName v.name, levelParams := copyNames v.levelParams, type := copyExpr v.type }
  | .inductInfo v => .inductInfo { v with name := copyName v.name, levelParams := copyNames v.levelParams, type := copyExpr v.type,
                                           all := copyNames v.all, ctors := copyNames v.ctors }
  | .ctorInfo v => .ctorInfo { v with name := copyName v.name, levelParams := copyNames v.levelParams, type := copyExpr v.type,
                                       induct := copyName v.induct }
  | .recInfo v => .recInfo { v with name := copyName v.name, levelParams := copyNames v.levelParams, type := copyExpr v.type,
                                     all := copyNames v.all,
                                     rules := v.rules.map fun r => { r with ctor := copyName r.ctor, rhs := copyExpr r.rhs } }

/-- The solution's declaration, normalised the same way as the copied reference one (no `mdata`). -/
def normCI : ConstantInfo → ConstantInfo
  | .defnInfo v => .defnInfo { v with type := stripAll v.type, value := stripAll v.value }
  | .opaqueInfo v => .opaqueInfo { v with type := stripAll v.type, value := stripAll v.value }
  | .recInfo v => .recInfo { v with type := stripAll v.type, rules := v.rules.map fun r => { r with rhs := stripAll r.rhs } }
  | .thmInfo v => .thmInfo { v with type := stripAll v.type }
  | .axiomInfo v => .axiomInfo { v with type := stripAll v.type }
  | .quotInfo v => .quotInfo { v with type := stripAll v.type }
  | .inductInfo v => .inductInfo { v with type := stripAll v.type }
  | .ctorInfo v => .ctorInfo { v with type := stripAll v.type }

def valueOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

def sameRules (eq : Expr → Expr → Bool) : List RecursorRule → List RecursorRule → Bool
  | [], [] => true
  | r :: rs, s :: ss => r.ctor == s.ctor && r.nfields == s.nfields && eq r.rhs s.rhs && sameRules eq rs ss
  | _, _ => false

/-- Declarations are identical for the purpose of the statement, expressions compared with `eq` (structural equality
    up to proof irrelevance, see `eqvE`). Theorem bodies are irrelevant. -/
def sameDecl (eq : Expr → Expr → Bool) (a b : ConstantInfo) : Bool :=
  kindOf a == kindOf b && a.levelParams == b.levelParams && eq a.type b.type &&
  match a, b with
  | .defnInfo x, .defnInfo y => eq x.value y.value && x.safety == y.safety && x.all == y.all
  | .opaqueInfo x, .opaqueInfo y => eq x.value y.value && x.isUnsafe == y.isUnsafe
  | .inductInfo x, .inductInfo y =>
      x.numParams == y.numParams && x.numIndices == y.numIndices && x.ctors == y.ctors &&
      x.all == y.all && x.isRec == y.isRec && x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
  | .ctorInfo x, .ctorInfo y =>
      x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams && x.numFields == y.numFields && x.isUnsafe == y.isUnsafe
  | .recInfo x, .recInfo y =>
      x.numParams == y.numParams && x.numIndices == y.numIndices && x.numMotives == y.numMotives &&
      x.numMinors == y.numMinors && x.k == y.k && x.isUnsafe == y.isUnsafe && sameRules eq x.rules y.rules
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
  | .thmInfo _, .thmInfo _ => true
  | .quotInfo x, .quotInfo y => x.kind.ctorIdx == y.kind.ctorIdx
  | _, _ => false

/-- Constants the *meaning* of a statement depends on (types, definition bodies, inductive structure; not proofs). -/
partial def stmtClosure (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  let some ci := env.find? n | return
  let mut deps := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => deps := deps ++ v.value.getUsedConstants
  | .opaqueInfo v => deps := deps ++ v.value.getUsedConstants
  | .inductInfo v => deps := deps ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => deps := deps.push v.induct
  | .recInfo v =>
      deps := deps ++ v.all.toArray
      for r in v.rules do deps := deps ++ r.rhs.getUsedConstants
  | _ => pure ()
  for d in deps do stmtClosure env d

structure Closure where
  seen : NameSet := {}
  axioms : Array Name := #[]
  sorried : Array Name := #[]

/-- Full dependency closure of the proof (values included), for axioms and remaining `sorry`. -/
partial def visit (env : Environment) (n : Name) : StateM Closure Unit := do
  if (← get).seen.contains n then return
  modify fun s => { s with seen := s.seen.insert n }
  let some ci := env.find? n | return
  if let .axiomInfo _ := ci then
    modify fun s => { s with axioms := s.axioms.push n }
  let mut deps := ci.type.getUsedConstants
  if let some v := valueOf? ci then
    let used := v.getUsedConstants
    if used.contains ``sorryAx then modify fun s => { s with sorried := s.sorried.push n }
    deps := deps ++ used
  if let .inductInfo v := ci then deps := deps ++ v.ctors.toArray
  for d in deps do visit env d

/-- A natural-number literal (`n`, `OfNat.ofNat _ n _`), possibly under metadata. -/
partial def natLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .mdata _ e => natLit? e
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then natLit? e.appFn!.appArg! else none

def jsonArr (xs : Array Name) : Json := Json.arr (xs.map (fun n => Json.str n.toString))

def fail (msg : String) : IO UInt32 := do
  IO.println (Json.compress (Json.mkObj [("ok", false), ("error", msg)]))
  return 2

def stmtDeps (env : Environment) (ty : Expr) : NameSet :=
  let act : StateM NameSet Unit := do for d in ty.getUsedConstants do stmtClosure env d
  (act.run {}).2

/-- What the solution is compared against, extracted from the reference environment. -/
structure RefData where
  target : ConstantInfo
  /-- every constant of the statement closure, with its reference declaration and whether it is a `sorry` hole -/
  closure : Array (Name × ConstantInfo × Bool)
  checkedDefs : Array Name
  holes : Array Name

/-- Everything the comparison needs from the reference. Declarations are copied (fresh objects, no `mdata`). -/
def extractReference (chal : Environment) (chalMod : String) (target : Name) : Except String RefData := Id.run do
  let some cT := chal.find? target | return .error s!"target {target} not found in the reference"
  let some chalIdx := chal.getModuleIdx? chalMod.toName | return .error "reference module index missing"
  let stmt := stmtDeps chal cT.type
  let mut closure := #[]
  let mut checkedDefs := #[]
  let mut holes := #[]
  for n in stmt.toList do
    let some ci := chal.find? n | continue
    let isThmC := match ci with | .thmInfo _ => true | _ => false
    if chal.getModuleIdxFor? n == some chalIdx && !isThmC then checkedDefs := checkedDefs.push (copyName n)
    -- A definition whose body is `sorry` in the reference is a hole the solution fills (e.g. the circuit of a metric
    -- challenge): only its kind, universe parameters and type must match.
    let isHole := match valueOf? ci with | some v => v.getUsedConstants.contains ``sorryAx | none => false
    if isHole then holes := holes.push (copyName n)
    closure := closure.push (copyName n, copyCI ci, isHole)
  return .ok { target := copyCI cT, closure, checkedDefs, holes }

/-- Separates checked definitions from holes in `extraConstNames` of the exported file. -/
def sep : Name := `_nosorry_holes_follow

/-- `export` mode (child process): load the reference and write what the comparison needs. -/
def exportReference (chalMod target out : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- no loadExts: never run initializers from untrusted modules
  let chal ← importModules #[{ module := chalMod.toName }] {}
  match extractReference chal chalMod target.toName with
  | .error e => fail e
  | .ok d =>
    let cis := #[d.target] ++ d.closure.map (·.2.1)
    saveModuleData out `NosorryReference
      { isModule := false, imports := #[], constNames := cis.map (·.name), constants := cis,
        extraConstNames := d.checkedDefs ++ #[sep] ++ d.holes, entries := #[] }
    return 0

/-- Runs the `export` child and reads its result back (a small region, kept for the life of the process). -/
def loadReference (chalMod : String) (target : Name) : IO (Except String RefData) := do
  -- Sandbox defaults (/tmp is a tmpfs, `lean` is on PATH); the worker overrides them when it runs without Docker.
  let out := System.FilePath.mk ((← IO.getEnv "NOSORRY_TMP").getD "/tmp") / "nosorry-reference.olean" |>.toString
  let self := (← IO.getEnv "NOSORRY_COMPARE_SELF").getD "src/Compare.lean"
  let lean := (← IO.getEnv "NOSORRY_LEAN").getD "lean"
  let r ← IO.Process.output { cmd := lean, args := #["--run", self, "export", chalMod, target.toString, out] }
  if r.exitCode != 0 then
    -- The child reports its own errors as JSON on stdout; anything else is an infrastructure failure.
    let lastLine := ((r.stdout.splitOn "\n").filter (· ≠ "")).getLast?.getD ""
    let msg := match Json.parse lastLine with
      | .ok j => (j.getObjValAs? String "error").toOption
      | .error _ => none
    return .error (msg.getD s!"reference extraction failed (exit {r.exitCode}): {String.ofList (r.stderr.toList.take 2000)}")
  let (md, _) ← readModuleData out
  let some cT := md.constants[0]? | return .error "reference export is empty"
  let some k := md.extraConstNames.idxOf? sep | return .error "reference export is malformed"
  let checkedDefs := md.extraConstNames.extract 0 k
  let holes := md.extraConstNames.extract (k + 1) md.extraConstNames.size
  let closure := (md.constants.extract 1 md.constants.size).map fun ci => (ci.name, ci, holes.contains ci.name)
  return .ok { target := cT, closure, checkedDefs, holes }

def check (chalMod solMod target : String) (neg : Bool) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let target := target.toName
  let solTarget := if neg then Name.str target.getPrefix ("not_" ++ target.getString!) else target
  let ref ← match ← loadReference chalMod target with
    | .ok r => pure r
    | .error e => return ← fail e
  let sol ← importModules #[{ module := solMod.toName }] {}
  let cT := ref.target
  let some sT := sol.find? solTarget | fail s!"{solTarget} not found in the submission"
  let isThm := match sT with | .thmInfo _ => true | _ => false
  -- Theorems of the reference statement closure (auxiliary `_proof_N` included): compared by the proposition they
  -- prove, wherever the statement uses them (`eqvE`), not by name.
  let rt : NameMap Expr := ref.closure.foldl (init := {}) fun m (n, ci, _) =>
    match ci with | .thmInfo v => m.insert n v.type | _ => m
  let eq := eqvE rt sol
  let expected := if neg then mkApp (mkConst ``Not) cT.type else cT.type
  let (typeOk, answers) := (tmatch rt sol expected (stripAll sT.type)).run #[]
  let levelsOk := cT.levelParams == sT.levelParams
  let mut mismatch : Array Name := #[]
  for (n, ci, isHole) in ref.closure do
    -- a theorem is checked where it is used (any proof of the same proposition will do), not here by name
    if let .thmInfo _ := ci then continue
    match sol.find? n with
    | none => mismatch := mismatch.push n
    | some si =>
      let si := normCI si
      let ok := if isHole then kindOf ci == kindOf si && ci.levelParams == si.levelParams && eq ci.type si.type else sameDecl eq ci si
      unless ok do mismatch := mismatch.push n
  let (_, cl) := (visit sol solTarget).run {}
  -- Declarations of the submission itself that the proof depends on (used to credit reused lemmas).
  let solIdx := sol.getModuleIdx? solMod.toName
  let ownDecls := (cl.seen.toList.filter (fun n => solIdx.isSome && sol.getModuleIdxFor? n == solIdx)).take 500
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := cl.axioms.filter (fun a => !allowed.contains a && a != ``sorryAx)
  let hasSorry := cl.axioms.contains ``sorryAx
  let ok := isThm && typeOk && levelsOk && mismatch.isEmpty && bad.isEmpty
  IO.println <| Json.compress <| Json.mkObj [
    ("ok", ok),
    ("target", solTarget.toString),
    ("disproof", neg),
    ("is_theorem", isThm),
    ("type_matches", typeOk),
    ("levels_match", levelsOk),
    ("answer_filled", !answers.isEmpty),
    ("answer_nats", Json.arr ((answers.filterMap natLit?).map (fun n => toJson n))),
    ("holes", jsonArr ref.holes),
    ("answers", Json.arr (answers.map (fun e => Json.str (String.ofList ((toString e).toList.take 500))))),
    ("definition_mismatches", jsonArr mismatch),
    ("checked_definitions", jsonArr ref.checkedDefs),
    ("statement_closure_size", (ref.closure.size : Nat)),
    ("axioms", jsonArr cl.axioms),
    ("forbidden_axioms", jsonArr bad),
    ("has_sorry", hasSorry),
    ("open_lemmas", jsonArr cl.sorried),
    ("closure_size", (cl.seen.toList.length : Nat)),
    ("own_decls", jsonArr ownDecls.toArray)
  ]
  return (if ok then 0 else 1)

/-- `inspect` mode (statements: formalizations and lemmas): one environment only. Reports whether the target is a
theorem, whether it is stated with `sorry`, and the axioms of its closure. -/
def inspectStatement (mod target : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- no loadExts: never run initializers from untrusted modules
  let env ← importModules #[{ module := mod.toName }] {}
  let t := target.toName
  let some ci := env.find? t | fail s!"target {t} not found"
  let isThm := match ci with | .thmInfo _ => true | _ => false
  let (_, cl) := (visit env t).run {}
  IO.println <| Json.compress <| Json.mkObj [
    ("target", t.toString), ("is_theorem", isThm), ("has_sorry", cl.axioms.contains ``sorryAx),
    ("open_lemmas", jsonArr cl.sorried), ("axioms", jsonArr cl.axioms), ("closure_size", (cl.seen.toList.length : Nat))]
  return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["inspect", m, t] => inspectStatement m t
  | ["export", c, t, out] => exportReference c t out
  | [c, s, t] => check c s t false
  | [c, s, t, "neg"] => check c s t true
  | _ => fail "usage: Compare <Challenge> <Solution> <decl> [neg]"
