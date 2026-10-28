(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Prog ApBase ApState ApLogic ApOwner CtOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_libiface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Liba.
Variable RT : rt_sig.

Definition LIBA (Σ : rts RT) (LW : list (Z * Z)) (m : mem) : Prop :=
  exists (ls : ap_ls bptr) (OW : list block),
    LW = map blk_an OW /\ List.NoDup (map blk_id OW) /\ Forall blk_okA OW      (* [comment removed for export] *)
    /\ ap_lib_inv2 ls m OW /\ CtOwner.ct_linv ls (ls_blocks ls).   (* [comment removed for export] *)

(* [comment removed for export] *)
Theorem liba_frameA : liba_frame RT LIBA.
Proof.
  intros Σ Σ' LW m m' (ls & OW & ELW & ND & OK & (E & (Hwf & HSG & nw & HS) & IDS & DC) & LINV) AG. subst LW.
  exists ls, OW. split; [reflexivity|]. split; [exact ND|]. split; [exact OK|]. split; [| exact LINV].
  exists E. split; [split; [exact Hwf|]; split; [exact HSG|]; exists nw; eapply ap_state_libfp; [exact HS| exact AG]|].
  split; [exact IDS|].
  destruct HS as (HE & _ & _ & _ & _ & _ & (_ & _ & _ & _ & FD)).
  eapply data_cells_agree; [exact DC| | exact FD].
  intros a Ha HL. unfold wa. pose proof (AG (Z_to_bv 64 a)) as EQ. rewrite unsigned_lit in EQ by lia. apply EQ.
  destruct HL as [H|(b & Hb & Hr)]; [left; exact (LIBW_S_FP a H)| right].
  exists (blk_addr b), (blk_size b). split; [| exact Hr]. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
Qed.

Theorem liba_exitA : liba_exit RT LIBA.
Proof.
  intros Σ LW m (ls & OW & _ & _ & _ & (E & (_ & _ & nw & HS) & _) & _).
  destruct HS as (_ & HF & _). unfold ap_statics_fixed in HF.
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (b0 & S22) & S23).
  exists b0. split; [exact S22| exact S23].
Qed.

Theorem liba_posA : liba_pos RT LIBA.
Proof.
  intros Σ LW m (ls & OW & -> & _ & OK & _) p n Hin. apply in_map_iff in Hin as (b & E & Hb). unfold blk_an in E. injection E as <- <-.
  exact (proj1 (proj2 (proj1 (Forall_forall _ _) OK b Hb))).
Qed.

End Liba.
