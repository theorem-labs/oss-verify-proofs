From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs hf_cuts hf_ent hf_asm hf_tailc hf_tailp hf_tok.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import hf_raw hf_tri.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import r2_ex_fin.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* handle_f on the ubsan image: entry region (hf_ent), token region (hf_tok), raw-face region (U/L11/hf_raw),
   triangulation region (U/L11/hf_tri), emit tail (hf_tailp), assembled by hf_asm. *)
Definition hf_cutsR : list edesc := tok_cuts ++ raw_cuts ++ tri_cuts ++ tail_cuts.
Definition hf_exitsR : list edesc := tok_exits ++ raw_exits ++ tri_exits ++ tail_exits.

Lemma hf_EJ : ejcert segsU NP FUEL_U (hf_cpsU (hf_cutsU hf_cutsR)) NP (hf_cutsU hf_cutsR) (hf_exitsU hf_exitsR) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma incl_cutsR : forall L, incl L hf_cutsR -> incl L (hf_cutsU hf_cutsR).
Proof. intros L H x Hx. unfold hf_cutsU. apply in_or_app. right. exact (H x Hx). Qed.

Lemma hf_XR : RegionsOK hf_cutsR hf_exitsR.
Proof.
  unfold RegionsOK, hf_exitsR.
  apply RegionOK_app; [| apply RegionOK_app; [| apply RegionOK_app]].
  - eapply RegionOK_mono; [| exact tok_exits_okT].
    apply incl_cutsR. intros x Hx. unfold hf_cutsR. apply in_or_app. left. exact Hx.
  - eapply RegionOK_mono; [| exact raw_exits_okT].
    apply incl_cutsR. intros x Hx. unfold hf_cutsR. apply in_or_app. right. apply in_or_app. left. exact Hx.
  - eapply RegionOK_mono; [| exact tri_exits_okT].
    apply incl_cutsR. intros x Hx. unfold hf_cutsR. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. left. exact Hx.
  - eapply RegionOK_mono; [| exact tail_exits_okT].
    apply incl_cutsR. intros x Hx. unfold hf_cutsR. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right. exact Hx.
Qed.

Theorem handle_f_sum_U : handle_f_sum_stmt_U.
Proof. exact (handle_f_sum_gen hf_cutsR hf_exitsR hf_EJ hf_XR). Qed.

Theorem handle_f_sum_ex_U : handle_f_sum_ex_stmt_U.
Proof.
  intros Kc FB rho0 Hvi MCX ML.
  exact (handle_f_sum_ex_gen hf_cutsR hf_exitsR hf_EJ hf_XR Kc FB rho0 Hvi MCX ML r2_sum_ex).
Qed.
