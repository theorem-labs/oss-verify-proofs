From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv RingBuf RingCfg.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2_cuts r2_ex_base r2_ex_defs r2_ex_g.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Import R2C R2X R2E R2G.

(* r2's complete-side cut pcs, cut nodes and exit nodes: the base lists (r2_ex_defs.v) joined with the forced-clip
   region (r2_ex_g.v). *)
Definition ecutpcs_r2 : list Z := ecutpcs_base ++ ecutpcs_g.
Definition rcuts_r2 : list rnode := rcuts_base ++ rcuts_g.
Definition rexits_r2 : list rnode := rexits_base ++ rexits_g.

Lemma rchk_r2 : check_rcfg segsU NF VN LN LP FUEL_r2 ecutpcs_r2 rcuts_r2 rexits_r2 = true.
Proof.
  unfold check_rcfg. rewrite <- (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.cuts_edges_fast_eq segsU).
  vm_cast_no_check (@eq_refl bool true).
Qed.
