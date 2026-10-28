From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary SymObj.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.
Import ListNotations. Open Scope Z_scope.

Definition pc_ws_U : Z := 0x193ac.
Definition pc_tok_U : Z := 0x193f4.
Definition pc_while_U : Z := 0x19394.
Definition pc_raw_U : Z := 0x195c8.
Definition pc_tri_U : Z := 0x19854.
Definition pc_emit_U : Z := 0x19b88.

Definition magic_U : sv := SLit 12297829382473034411.
Definition tokregs_U : list (nat * sv) :=
  [(10%nat, txt xE0); (18%nat, xb 720); (19%nat, SLit 2); (22%nat, SLit 32); (23%nat, SLit 9);
   (24%nat, pA); (25%nat, am2); (27%nat, magic_U)].
Definition tokregs0_U : list (nat * sv) :=
  [(10%nat, txt xE0); (18%nat, xb 720); (19%nat, SLit 2); (22%nat, SLit 32); (23%nat, SLit 9);
   (24%nat, SLit 0); (25%nat, SLit (-2)); (27%nat, magic_U)].
Definition nzA_U : list sprop := [SPUle (SLit 1) pA; SPUle (SLit 4096) (t_d co1)].

Definition T60z_U : sstate :=
  HS_U pc_ws_U (tokregs0_U ++ [(26%nat, txt pQ)]) [] pP (t_d co1, SLit 0, t_k co1) []
    [SPUle xP0 pP; SPUle pP pQ; SPUlt pQ xE0].
Definition T60n_U : sstate :=
  HS_U pc_ws_U (tokregs_U ++ [(26%nat, txt pQ)]) [] pP coA []
    ([SPUle xP0 pP; SPUle pP pQ; SPUlt pQ xE0; SPUle pA (SLit (2 ^ 20))] ++ nzA_U).
(* r24 is written (-1) + pA so that infer_sub binds pA by offset from the leaf's r24 (the old count). *)
Definition T50_U : sstate :=
  HS_U pc_while_U [(9%nat, SVar 13); (18%nat, xb 720); (19%nat, SLit 2); (22%nat, SLit 32); (23%nat, SLit 9);
    (24%nat, SAlu ALU_ADD (SLit (-1)) pA); (25%nat, SAlu ALU_ADD pA (SLit (-3))); (27%nat, magic_U)] [] pP coA []
    ([SPUle xP0 pP; SPUle pP xE0; SPUle pA (SLit (2 ^ 20))] ++ nzA_U).

Definition vT60_U : sv := VT pQ 0.
Definition vT50_U : sv := VT pP 1.
