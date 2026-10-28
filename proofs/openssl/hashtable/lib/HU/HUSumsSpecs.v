(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import MemsetLib.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HUMemcpyBase HUMemcpy HUMemsetG.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxPlanSoundSums.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation HSEGS := Ubsan.M.loaded_segments (only parsing).
#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).

(* [comment removed for export] *)
Lemma kept_ok_of_keeps : forall regs regs', keeps regs regs' -> APSX.kept_ok regs regs'.
Proof.
  intros regs regs' Hk r Hr0 Hnin. apply Hk.
  pose proof (AX2S.ridx_range r) as Hrr.
  assert (Hr : AX2.ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (APSX.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold CAP.caller_saved in Hnin. cbn [In] in Hnin.
  assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
  { exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
  destruct E as (k & Hink & Hrk). rewrite (APSX.reg_of_ridx r k Hrk).
  cbn [In] in Hink. unfold callee_kept.
  repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.

Lemma segs_wr_of_forallb : forall segs,
  forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool segs = true -> APSX.segs_wr_ok segs.
Proof.
  intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
  rewrite Hw in Hs. exact Hs.
Qed.

Lemma h0_segs_wr : APSX.segs_wr_ok HSEGS.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.

Lemma h0_copy_spec_memcpy : APSX.copy_spec HSEGS 0x2bc024.
Proof.
  intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  pose proof (u64_range dst) as Hdr.
  assert (HOK : HUMemcpyBase.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
  destruct (HUMemcpy.ref_memcpy mem0 dst src n bs (seg_rom HSEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
  exists regs'. split; [replace (Z_to_bv 64 0x2bc024) with (0x2bc024%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [apply kept_ok_of_keeps; exact Hk|].
  rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

(* [comment removed for export] *)
Lemma kept_ok_of_regs_agree : forall (clob : list reg) regs regs',
  (forall r, In r clob -> In (AX2.ridx r) CAP.caller_saved) ->
  regs_agree (fun r => In r clob) regs regs' -> APSX.kept_ok regs regs'.
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.

Lemma ms_clob_sub : forall r, In r ms_clob -> In (AX2.ridx r) CAP.caller_saved.
Proof.
  unfold ms_clob. intros r H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [in_list|]); destruct H.
Qed.

Lemma h0_fill_spec_memset : APSX.fill_spec HSEGS 0x2bc5a4 AX2.two64.
Proof.
  intros mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  destruct (HUMemsetG.memset_summary mem0 s c ret n (seg_rom HSEGS) Hn Hnw Hst Hret regs R10 R11 R12 R1) as (regs' & Hms & H10 & Hag).
  exists regs'. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply ms_clob_sub | exact Hag].
Qed.
