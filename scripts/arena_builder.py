#!/usr/bin/env python3
"""High-level DAG Certificate Builder DSL for zero-Mathlib `kernel-arena.2ltt.v1`."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
CERTS_DIR = REPO_ROOT / "certs"

LITERAL_ARG_OPS = frozenset({"UnivS", "UnivF", "Var", "DimVar"})
UNIVALENCE_OPS = frozenset({"InnerUnivalenceV", "VType", "VIn", "VProj"})
COALGEBRA_OPS = frozenset({"InnerCoalgebraNu"})
STRICT_EQ_OPS = frozenset({"OuterStrictEq", "EqS", "ReflS", "UIPS"})
REPLACEMENT_OPS = frozenset({"SmallnessReplacement"})


def node_children(node: dict[str, Any]) -> list[int]:
    op = node["op"]
    if op in LITERAL_ARG_OPS:
        return []
    return list(node.get("args", []))


def node_op_canon(node: dict[str, Any]) -> str:
    op = node["op"]
    args = node.get("args", [])
    if op == "HCom":
        r, rp, ty, u0, *rest = args
        tail = "".join(f":{x}" for x in rest)
        return f"HCom:{r}:{rp}:{ty}:{u0}{tail}"
    if not args:
        return op
    return f"{op}:{':'.join(str(a) for a in args)}"


class ArenaBuilder:
    """Hash-consed topological DAG builder for `kernel-arena.2ltt.v1` certificates."""

    def __init__(
        self,
        decl_name: str,
        universe_depth_k: int = 1,
        fuel_hint: int = 96,
        dim_contexts: list[str] | None = None,
    ) -> None:
        self.decl_name = decl_name
        self.universe_depth_k = int(universe_depth_k)
        self.fuel_hint = int(fuel_hint)
        self.dim_contexts = list(dim_contexts or [])
        self.nodes: list[dict[str, Any]] = []
        self._intern_map: dict[tuple[str, tuple[int, ...]], int] = {}

    def _intern(self, op: str, *args: int) -> int:
        int_args = tuple(int(a) for a in args)
        key = (op, int_args)
        if key in self._intern_map:
            return self._intern_map[key]
        nid = len(self.nodes)
        if op not in LITERAL_ARG_OPS:
            for child in int_args:
                if child < 0 or child >= nid:
                    raise ValueError(f"Topological violation at node {nid} ({op}): child {child} >= {nid}")
        rec: dict[str, Any] = {"id": nid, "op": op}
        if int_args:
            rec["args"] = list(int_args)
        self.nodes.append(rec)
        self._intern_map[key] = nid
        return nid

    # Phase 0 & basic combinators
    def univ_s(self, level: int) -> int: return self._intern("UnivS", level)
    def univ_f(self, level: int) -> int: return self._intern("UnivF", level)
    def bool_s(self) -> int: return self._intern("BoolS")
    def bool_f(self) -> int: return self._intern("BoolF")
    def true_f(self) -> int: return self._intern("TrueF")
    def false_f(self) -> int: return self._intern("FalseF")
    def var(self, idx: int) -> int: return self._intern("Var", idx)
    def pi_s(self, dom: int, cod: int) -> int: return self._intern("PiS", dom, cod)
    def pi_f(self, dom: int, cod: int) -> int: return self._intern("PiF", dom, cod)
    def lam_s(self, dom: int, body: int) -> int: return self._intern("LamS", dom, body)
    def lam_f(self, dom: int, body: int) -> int: return self._intern("LamF", dom, body)
    def app_s(self, fn: int, arg: int) -> int: return self._intern("AppS", fn, arg)
    def app_f(self, fn: int, arg: int) -> int: return self._intern("AppF", fn, arg)
    def lift_f_to_s(self, inner: int) -> int: return self._intern("LiftFtoS", inner)

    # Dimensions & cofibrations
    def dim0(self) -> int: return self._intern("Dim0")
    def dim1(self) -> int: return self._intern("Dim1")
    def dim_var(self, idx: int) -> int: return self._intern("DimVar", idx)
    def cof_top(self) -> int: return self._intern("CofTop")
    def cof_bot(self) -> int: return self._intern("CofBot")
    def cof_eq(self, r1: int, r2: int) -> int: return self._intern("CofEq", r1, r2)
    def cof_and(self, c1: int, c2: int) -> int: return self._intern("CofAnd", c1, c2)
    def cof_or(self, c1: int, c2: int) -> int: return self._intern("CofOr", c1, c2)

    # Outer strict level
    def unit_s(self) -> int: return self._intern("UnitS")
    def star_s(self) -> int: return self._intern("StarS")
    def sigma_s(self, dom: int, cod: int) -> int: return self._intern("SigmaS", dom, cod)
    def pair_s(self, fst: int, snd: int) -> int: return self._intern("PairS", fst, snd)
    def fst_s(self, p: int) -> int: return self._intern("FstS", p)
    def snd_s(self, p: int) -> int: return self._intern("SndS", p)
    def eq_s(self, ty: int, lhs: int, rhs: int) -> int: return self._intern("EqS", ty, lhs, rhs)
    def refl_s(self, a: int) -> int: return self._intern("ReflS", a)
    def uip_s(self, ty: int, lhs: int, rhs: int, p: int, q: int) -> int:
        return self._intern("UIPS", ty, lhs, rhs, p, q)

    # Inner fibrant data
    def empty_f(self) -> int: return self._intern("EmptyF")
    def empty_elim_f(self, motive: int, scrut: int) -> int: return self._intern("EmptyElimF", motive, scrut)
    def unit_f(self) -> int: return self._intern("UnitF")
    def star_f(self) -> int: return self._intern("StarF")
    def bool_elim_f(self, motive: int, t_case: int, f_case: int, scrut: int) -> int:
        return self._intern("BoolElimF", motive, t_case, f_case, scrut)
    def sigma_f(self, dom: int, cod: int) -> int: return self._intern("SigmaF", dom, cod)
    def pair_f(self, fst: int, snd: int) -> int: return self._intern("PairF", fst, snd)
    def fst_f(self, p: int) -> int: return self._intern("FstF", p)
    def snd_f(self, p: int) -> int: return self._intern("SndF", p)

    # Paths, Kan, & V-Univalence
    def path_type(self, ty_line: int, a0: int, a1: int) -> int:
        return self._intern("PathType", ty_line, a0, a1)
    def path_lam(self, body: int) -> int:
        return self._intern("PathLam", body)
    def path_app(self, p: int, a0: int, a1: int, r: int) -> int:
        return self._intern("PathApp", p, a0, a1, r)
    def coe(self, r: int, r_prime: int, ty_line: int, m: int) -> int:
        return self._intern("Coe", r, r_prime, ty_line, m)
    def hcom(self, r: int, r_prime: int, ty: int, u0: int, tubes: list[tuple[int, int]]) -> int:
        flat: list[int] = [r, r_prime, ty, u0]
        for phi, body in tubes:
            flat.extend((phi, body))
        return self._intern("HCom", *flat)
    def v_type(self, r: int, a: int, b: int, f: int, g: int, sec: int, ret: int) -> int:
        return self._intern("VType", r, a, b, f, g, sec, ret)
    def v_in(self, r: int, a: int, b: int) -> int:
        return self._intern("VIn", r, a, b)
    def v_proj(self, r: int, a: int, b: int, f: int, v: int) -> int:
        return self._intern("VProj", r, a, b, f, v)

    # Stratum markers
    def inner_univalence_v(self, arg: int) -> int: return self._intern("InnerUnivalenceV", arg)
    def inner_coalgebra_nu(self, arg: int) -> int: return self._intern("InnerCoalgebraNu", arg)
    def outer_strict_eq(self, lhs: int, rhs: int) -> int: return self._intern("OuterStrictEq", lhs, rhs)
    def smallness_replacement(self, arg: int) -> int: return self._intern("SmallnessReplacement", arg)

    def compute_strata_flags(self, goal_id: int, proof_id: int) -> dict[str, bool]:
        flags = {
            "inner_univalence_V": False,
            "inner_coalgebra_nu": False,
            "outer_strict_eq": False,
            "smallness_replacement": False,
        }
        needed = {goal_id, proof_id}
        for node in reversed(self.nodes):
            if node["id"] not in needed:
                continue
            op = node["op"]
            if op in UNIVALENCE_OPS:
                flags["inner_univalence_V"] = True
            elif op in COALGEBRA_OPS:
                flags["inner_coalgebra_nu"] = True
            elif op in STRICT_EQ_OPS:
                flags["outer_strict_eq"] = True
            elif op in REPLACEMENT_OPS:
                flags["smallness_replacement"] = True
            needed.update(node_children(node))
        return flags

    def canonical_payload(self, goal_id: int, proof_id: int) -> str:
        header = [
            "KERNEL_ARENA_2LTT_V1",
            f"decl_name={self.decl_name}",
            f"universe_depth_k={self.universe_depth_k}",
            f"dim_contexts={','.join(self.dim_contexts)}",
            f"goal_type_node={goal_id}",
            f"proof_term_node={proof_id}",
            f"nodes={len(self.nodes)}",
        ]
        body = [f"{n['id']}:{node_op_canon(n)}" for n in self.nodes]
        return "\n".join(header + body)

    def build(self, goal_id: int, proof_id: int) -> dict[str, Any]:
        payload = self.canonical_payload(goal_id, proof_id)
        sha = hashlib.sha256(payload.encode("utf-8")).hexdigest()
        return {
            "schema": "kernel-arena.2ltt.v1",
            "decl_name": self.decl_name,
            "universe_depth_k": self.universe_depth_k,
            "fuel_hint": self.fuel_hint,
            "strata_flags": self.compute_strata_flags(goal_id, proof_id),
            "dim_contexts": self.dim_contexts,
            "nodes": self.nodes,
            "goal_type_node": goal_id,
            "proof_term_node": proof_id,
            "sha256_arena": sha,
        }

    def write(self, path: Path, goal_id: int, proof_id: int) -> dict[str, Any]:
        cert = self.build(goal_id, proof_id)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        return cert


def build_path_sym_cert() -> dict[str, Any]:
    """Emerald Rung 1 cert: path symmetry on BoolF via Cartesian hcom."""
    b = ArenaBuilder("TwoLTT.Rung1.boolF_path_sym", universe_depth_k=1, fuel_hint=96)
    b2 = b.bool_f()
    x_var = b.var(2)
    y_var = b.var(1)
    p_var = b.var(0)
    # In context [x, y], p has type Path (_. 2^f) x y where x = var(1), y = var(0)
    p_dom = b.path_type(b2, b.var(1), b.var(0))
    goal = b.pi_f(b2, b.pi_f(b2, b.pi_f(p_dom, b.path_type(b2, y_var, x_var))))

    d0, d1 = b.dim0(), b.dim1()
    di = b.dim_var(0)
    dj = b.dim_var(0)
    tube_i0 = b.cof_eq(di, d0)
    tube_i1 = b.cof_eq(di, d1)
    u_i0 = b.path_app(p_var, x_var, y_var, dj)
    h = b.hcom(d0, d1, b2, x_var, [(tube_i0, u_i0), (tube_i1, x_var)])
    proof = b.lam_f(b2, b.lam_f(b2, b.lam_f(p_dom, b.path_lam(h))))
    return b.write(CERTS_DIR / "tcb_r1_path_sym_kan.2ltt.json", goal, proof)


def build_ua_not_holonomy_cert() -> dict[str, Any]:
    """Sapphire Rung 1 cert: ua(not) on BoolF flips false^f to true^f."""
    b = ArenaBuilder("TwoLTT.Rung1.boolF_ua_not_flips_false_to_true", universe_depth_k=2, fuel_hint=96)
    b2 = b.bool_f()
    tf, ff, v0 = b.true_f(), b.false_f(), b.var(0)
    not_f = b.lam_f(b2, b.bool_elim_f(b2, ff, tf, v0))
    not_not_v0 = b.app_f(not_f, b.app_f(not_f, v0))
    inv_motive = b.path_type(b2, not_not_v0, v0)
    not_inv = b.lam_f(b2, b.bool_elim_f(inv_motive, b.path_lam(tf), b.path_lam(ff), v0))

    di = b.dim_var(0)
    ua_not = b.path_lam(b.v_type(di, b2, b2, not_f, not_f, not_inv, not_inv))
    ua_line = b.path_app(ua_not, b2, b2, di)
    transported = b.coe(b.dim0(), b.dim1(), ua_line, ff)

    goal = b.path_type(b2, transported, tf)
    proof = b.path_lam(tf)
    return b.write(CERTS_DIR / "tcb_r1_univ_bool_ua_not_holonomy.2ltt.json", goal, proof)


def main() -> int:
    c1 = build_path_sym_cert()
    c2 = build_ua_not_holonomy_cert()
    print(
        f"ARENA_BUILDER_OK path_sym_nodes={len(c1['nodes'])} path_sym_flags={c1['strata_flags']} "
        f"ua_not_nodes={len(c2['nodes'])} ua_not_flags={c2['strata_flags']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
