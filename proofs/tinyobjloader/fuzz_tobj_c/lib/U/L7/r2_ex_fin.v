From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv RingBuf RingCfg.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import
  S_r2 r2_cuts r2_ex_base r2_ex_defs r2_ex_g r2_ex r2_ex_chk r2_ex_ret r2_ex_exits r2_ex_clip.
Import ListNotations.
Import R2C R2X R2E R2G.

(* r2_sum_ex: the ring-CFG check (r2_ex_chk.v) and one exit lemma per exit node (r2_ex_exits.v, r2_ex_clip.v,
   r2_ex_ret.v). *)
Theorem r2_sum_ex : r2_sum_ex_stmt_U.
Proof.
  apply (r2_sum_ex_gen ecutpcs_g rcuts_g rexits_g rchk_r2).
  repeat constructor.
  - apply ex_Xr0. cbn. tauto.
  - apply ex_Xr. cbn. tauto.
  - apply ex_Xrf. cbn. tauto.
  - apply ex_Xc2. cbn. tauto.
  - apply ex_Eret.
  - apply ex_Xg2. cbn. tauto.
Qed.
