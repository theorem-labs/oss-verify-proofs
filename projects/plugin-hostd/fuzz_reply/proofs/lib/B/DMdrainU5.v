(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainU5.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail; file sha256 d05532a39cdd) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU5.v at commit 2e76ed2595c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (1 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the quarantine's cells at the RECYCLE cut - Recycle's call of
   DoRecycle (0x33b54) - the twin of DMdrainTB.cut_cells, which states the same at the return cut.  At this cut
   the model state is DMiface.drain_recyc's S' = set_qglobal g' (set_qthread qc0 X): the thread cache is empty
   and the global cache is the KEPT list, the part of the transferred quarantine the dequeue loop did not pop.
   Every word comes from DMdeq.ATDR (DMdeq.v:201-205): the two lock bytes and the two after them, the global
   header's four words over the kept list, the thread header's four zero words (which the loop does not touch),
   and the kept list's batch cells through DMdrainU3.kept_lcn and DMdrainP.batch_cells_of_lcn.
   rule 24: no function proved (kind: the cells of a cut of segments already walked; the lane's reuse search is
   LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFey YFgj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DMwalkIF DMdrainK DMdrainP DMdrainQ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout) (X : astate).
Variable gk : qcache.
Variable mem' : word -> option byte.
Variable inst : Z.
Let m' := mrestrict (w_H W) mem'.
Local Notation R := (qc_list gk).
Local Notation S' := (set_qglobal gk (set_qthread qc0 X)).

Hypothesis Hinst : as_inst B = inst.
Hypothesis AQ : inst + o_quar = A_QUAR.
(* DMdeq.ATDR's header words (DMdeq.v:201-203) *)
Hypothesis HMUT : forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0).
Hypothesis HC160 : val_mem tfibsegs m' (A_QUAR + 160) 8 (Z.of_nat (length R)).
Hypothesis HC168 : val_mem tfibsegs m' (A_QUAR + 168) 8 (fa ly R 0).
Hypothesis HC176 : val_mem tfibsegs m' (A_QUAR + 176) 8 (la ly R).
Hypothesis HC184 : val_mem tfibsegs m' (A_QUAR + 184) 8 (qc_bytes gk).
(* the thread cache's four header words, zero since the transfer; the loop does not write them *)
Hypothesis HT0 : val_mem tfibsegs m' (ly_T ly + t_qc) 8 0.
Hypothesis HT8 : val_mem tfibsegs m' (ly_T ly + t_qc + 8) 8 0.
Hypothesis HT16 : val_mem tfibsegs m' (ly_T ly + t_qc + 16) 8 0.
Hypothesis HT24 : val_mem tfibsegs m' (ly_T ly + t_qc + 24) 8 0.
(* the kept list, linked (DMdrainU3.kept_lcn) *)
Hypothesis HRL : lcn ly (DMdrainK.iwB B ly) m' R 0.

Theorem cut_cells_recyc : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (quar_cells S').
Proof.
assert (EQS : quar_cells S' = z1 (AInst o_q_cmutex) 0 :: z1 (AInst o_q_rmutex) 0
  :: qc_cells (AT t_qc) qc0 ++ qc_cells (AInst o_q_size) gk) by reflexivity.
rewrite EQS.
apply Forall_cons.
{ apply (DMdrainP.val_mem_cellZ B ly (w_H W) mem' (AInst o_q_cmutex) 1 0). cbn [aeval].
  intros k Hk. cbn in Hk. assert (k = 0%nat) by lia. subst k.
  rewrite Z.add_0_r. change (YO0f.le_byte 0 1 0) with 0.
  rewrite Hinst in *. unfold o_q_cmutex, o_quar in *. apply HMUT. rewrite <- AQ. unfold o_quar. lia. }
apply Forall_cons.
{ apply (DMdrainP.val_mem_cellZ B ly (w_H W) mem' (AInst o_q_rmutex) 1 0). cbn [aeval].
  intros k Hk. cbn in Hk. assert (k = 0%nat) by lia. subst k.
  rewrite Z.add_0_r. change (YO0f.le_byte 0 1 0) with 0.
  rewrite Hinst in *. unfold o_q_rmutex, o_quar in *. apply HMUT. rewrite <- AQ. unfold o_quar. lia. }
apply Forall_app. split.
- (* the thread cache is empty *)
  unfold qc_cells. cbn [qc_list qc_bytes].
  apply Forall_cons.
  { apply (DMdrainP.val_mem_cellZ B ly (w_H W) mem' (AT t_qc) 8 0). cbn [aeval].
    match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_T ly + t_qc) by lia end. exact HT0. }
  apply Forall_cons.
  { apply (DMdrainP.val_mem_cell B ly (w_H W) mem' (aoff (AT t_qc) 8) 8 (ANum 0)). cbn [aeval aoff].
    match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_T ly + t_qc + 8) by lia end. exact HT8. }
  apply Forall_cons.
  { apply (DMdrainP.val_mem_cell B ly (w_H W) mem' (aoff (AT t_qc) 16) 8 (ANum 0)). cbn [aeval aoff].
    match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_T ly + t_qc + 16) by lia end. exact HT16. }
  apply Forall_cons; [|apply Forall_nil].
  { apply (DMdrainP.val_mem_cellZ B ly (w_H W) mem' (aoff (AT t_qc) 24) 8 0). cbn [aeval aoff].
    match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_T ly + t_qc + 24) by lia end. exact HT24. }
- (* the global cache is the kept list *)
  unfold qc_cells. cbn [qc_list qc_bytes].
  apply Forall_cons.
  { apply (DMdrainP.val_mem_cellZ B ly (w_H W) mem' (AInst o_q_size) 8 _). cbn [aeval].
    match goal with |- val_mem _ _ ?a _ _ =>
      replace a with (A_QUAR + 160) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia) end.
    exact HC160. }
  apply Forall_cons.
  { apply (DMdrainP.val_mem_cell B ly (w_H W) mem' (aoff (AInst o_q_size) 8) 8 _). cbn [aeval aoff batch_exp].
    match goal with |- val_mem _ _ ?a _ ?v =>
      replace a with (A_QUAR + 168) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia);
      replace v with (fa ly R 0) by (unfold fa, addrb; destruct R; reflexivity) end.
    exact HC168. }
  apply Forall_cons.
  { apply (DMdrainP.val_mem_cell B ly (w_H W) mem' (aoff (AInst o_q_size) 16) 8 _). cbn [aeval aoff batch_exp].
    match goal with |- val_mem _ _ ?a _ ?v =>
      replace a with (A_QUAR + 176) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia);
      replace v with (la ly R) by (unfold la, addrb; destruct (rev R); reflexivity) end.
    exact HC176. }
  apply Forall_cons.
  { apply (DMdrainP.val_mem_cellZ B ly (w_H W) mem' (aoff (AInst o_q_size) 24) 8 _). cbn [aeval aoff].
    match goal with |- val_mem _ _ ?a _ _ =>
      replace a with (A_QUAR + 184) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia) end.
    exact HC184. }
  exact (DMdrainP.batch_cells_of_lcn B ly (w_H W) mem' R HRL).
Qed.
End g.
End f.
