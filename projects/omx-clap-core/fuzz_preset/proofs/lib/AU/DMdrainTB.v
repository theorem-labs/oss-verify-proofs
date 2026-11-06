(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainTB.v (commit ce1a656b52b7, file sha256 e66caf332e5f) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainTB.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 c1cc38c27015) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainTB.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): DMiface.dmem_q (DMiface.v:117-126) IN FULL at the transferred
   state DMdrainM.sxf X, from the clauses Drain's entry walk leaves (YFgj.at_RETD / YFgj.at_L0, which agree on
   every value this needs) - the frame (DMdrainT2.dmem_frame), the transferred quarantine's cells
   (DMdrainTA.GT_lcn for the batches, the header words and the mutex bytes here), the presence off the
   quarantine's header, and the two bytes after the mutex word.
   rule 24: no function proved (kind: the cut relation of segments already walked; the lane's reuse search is
   the internal file LOOKUP-B1-drain.txt, `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj YFhf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF DMdrainK DMdrainM DMdrainP DMdrainQ DMdrainT2 DMdrainT3 DMdrainT4 DMdrainT7 DMdrainT8 DMdrainTA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout) (X : astate).
Variables (regs0 : bvmap 5 word) (mem0 mem' : word -> option byte).
Variable inst : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let m0 := mrestrict (w_H W) mem0.
Let m' := mrestrict (w_H W) mem'.
Local Notation SB := (ly_space ly).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).

Hypothesis Hinst : as_inst B = inst.
Hypothesis AQ : inst + o_quar = A_QUAR.
Hypothesis HM : forall x : word, ~ YFgj.WIN ly regs0 (st_qglobal X) (bv_unsigned x) -> mem' x = mem0 x.
Hypothesis HWP : forall a, YFgj.WIN ly regs0 (st_qglobal X) a -> kHighMemBeg <= a -> apresent (w_H W) mem' a.
Hypothesis HMUT : forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0).
Hypothesis HC160 : val_mem tfibsegs m' (A_QUAR + 160) 8 (YFgj.LSZv (st_qglobal X) (st_qthread X)).
Hypothesis HC168 : val_mem tfibsegs m' (A_QUAR + 168) 8 (YFgj.LFv ly (st_qglobal X) (st_qthread X)).
Hypothesis HC176 : val_mem tfibsegs m' (A_QUAR + 176) 8 (YFgj.TLv ly (st_qthread X)).
Hypothesis HC184 : val_mem tfibsegs m' (A_QUAR + 184) 8 (YFgj.LBv (st_qglobal X) (st_qthread X)).
Hypothesis HT0 : val_mem tfibsegs m' (ly_T ly + t_qc) 8 0.
Hypothesis HT8 : val_mem tfibsegs m' (ly_T ly + t_qc + 8) 8 0.
Hypothesis HT16 : val_mem tfibsegs m' (ly_T ly + t_qc + 16) 8 0.
Hypothesis HT24 : val_mem tfibsegs m' (ly_T ly + t_qc + 24) 8 0.
Hypothesis HGT : lcn ly (iwB B ly) m' (G ++ Tq) 0.
Hypothesis HTne : Tq <> [].
Hypothesis HWF : qc_bytes (st_qthread X) = sum_bytes Tq /\ qc_bytes (st_qglobal X) = sum_bytes G.
Hypothesis HQW : qc_bytes (YFeuC.transfer_g X) = YFgj.LBv (st_qglobal X) (st_qthread X).

Local Notation S' := (sxf X).

Lemma Slist : qc_list (st_qglobal S') = G ++ Tq.
Proof. reflexivity. Qed.
Lemma Sthread : st_qthread S' = qc0.
Proof. reflexivity. Qed.

Lemma Scount : Z.of_nat (length (G ++ Tq)) = YFgj.LSZv (st_qglobal X) (st_qthread X).
Proof. unfold YFgj.LSZv, YFgj.GSZv, YFgj.TSZv. rewrite length_app. lia. Qed.

Lemma Sfirst : (match G ++ Tq with [] => 0 | b :: _ => SB + b_self b end) = YFgj.LFv ly (st_qglobal X) (st_qthread X).
Proof. unfold YFgj.LFv, YFgj.GFv, YFgj.TFv. destruct G as [|b t]; reflexivity. Qed.

Lemma Slast : (match rev (G ++ Tq) with [] => 0 | b :: _ => SB + b_self b end) = YFgj.TLv ly (st_qthread X).
Proof.
unfold YFgj.TLv. rewrite rev_app_distr. destruct (rev Tq) as [|b t] eqn:ER; [|reflexivity].
exfalso. apply HTne. rewrite <- (rev_involutive Tq), ER. reflexivity.
Qed.

Theorem cut_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (quar_cells S').
Proof.
assert (EQS : quar_cells S' = z1 (AInst o_q_cmutex) 0 :: z1 (AInst o_q_rmutex) 0
  :: qc_cells (AT t_qc) qc0 ++ qc_cells (AInst o_q_size) (mkQC (G ++ Tq) (qc_bytes (YFeuC.transfer_g X)))) by reflexivity.
rewrite EQS.
apply Forall_cons.
{ apply (val_mem_cellZ B ly (w_H W) mem' (AInst o_q_cmutex) 1 0). cbn [aeval].
  intros k Hk. cbn in Hk. assert (k = 0%nat) by lia. subst k.
  rewrite Z.add_0_r. change (YO0f.le_byte 0 1 0) with 0.
  rewrite Hinst in *. unfold o_q_cmutex, o_quar in *. apply HMUT. rewrite <- AQ. unfold o_quar. lia. }
apply Forall_cons.
{ apply (val_mem_cellZ B ly (w_H W) mem' (AInst o_q_rmutex) 1 0). cbn [aeval].
  intros k Hk. cbn in Hk. assert (k = 0%nat) by lia. subst k.
  rewrite Z.add_0_r. change (YO0f.le_byte 0 1 0) with 0.
  rewrite Hinst in *. unfold o_q_rmutex, o_quar in *. apply HMUT. rewrite <- AQ. unfold o_quar. lia. }
apply Forall_app. split.
- (* the thread cache is empty: four zero words, no batch cells *)
  unfold qc_cells. cbn [qc_list qc_bytes].
  apply Forall_cons.
  { apply (val_mem_cellZ B ly (w_H W) mem' (AT t_qc) 8 0). cbn [aeval].
    match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_T ly + t_qc) by lia end. exact HT0. }
  apply Forall_cons.
  { apply (val_mem_cell B ly (w_H W) mem' (aoff (AT t_qc) 8) 8 (ANum 0)). cbn [aeval aoff].
    match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_T ly + t_qc + 8) by lia end. exact HT8. }
  apply Forall_cons.
  { apply (val_mem_cell B ly (w_H W) mem' (aoff (AT t_qc) 16) 8 (ANum 0)). cbn [aeval aoff].
    match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_T ly + t_qc + 16) by lia end. exact HT16. }
  apply Forall_cons; [|apply Forall_nil].
  { apply (val_mem_cellZ B ly (w_H W) mem' (aoff (AT t_qc) 24) 8 0). cbn [aeval aoff].
    match goal with |- val_mem _ _ ?a _ _ => replace a with (ly_T ly + t_qc + 24) by lia end. exact HT24. }
- (* the global cache is the joined list *)
  unfold qc_cells. cbn [qc_list qc_bytes].
  apply Forall_cons.
  { apply (val_mem_cellZ B ly (w_H W) mem' (AInst o_q_size) 8 _). cbn [aeval].
    match goal with |- val_mem _ _ ?a _ ?v =>
      replace a with (A_QUAR + 160) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia);
      replace v with (YFgj.LSZv (st_qglobal X) (st_qthread X)) by (rewrite <- Scount; reflexivity) end.
    exact HC160. }
  apply Forall_cons.
  { apply (val_mem_cell B ly (w_H W) mem' (aoff (AInst o_q_size) 8) 8 _). cbn [aeval aoff batch_exp].
    match goal with |- val_mem _ _ ?a _ ?v => replace a with (A_QUAR + 168) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia);
      replace v with (YFgj.LFv ly (st_qglobal X) (st_qthread X)) by (rewrite <- Sfirst; destruct (G ++ Tq); reflexivity) end.
    exact HC168. }
  apply Forall_cons.
  { apply (val_mem_cell B ly (w_H W) mem' (aoff (AInst o_q_size) 16) 8 _). cbn [aeval aoff batch_exp].
    match goal with |- val_mem _ _ ?a _ ?v => replace a with (A_QUAR + 176) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia);
      replace v with (YFgj.TLv ly (st_qthread X)) by (rewrite <- Slast; destruct (rev (G ++ Tq)); reflexivity) end.
    exact HC176. }
  apply Forall_cons.
  { apply (val_mem_cellZ B ly (w_H W) mem' (aoff (AInst o_q_size) 24) 8 _). cbn [aeval aoff].
    match goal with |- val_mem _ _ ?a _ ?v => replace a with (A_QUAR + 184) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia) end.
    rewrite HQW. exact HC184. }
  exact (batch_cells_of_lcn B ly (w_H W) mem' (G ++ Tq) HGT).
Qed.
End g.
End f.
