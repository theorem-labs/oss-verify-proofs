(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainTB.v (commit 67deba317dfb, blob 17320c02afe8) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj AFhf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainK DMdrainM DMdrainP DMdrainQ DMdrainT2 DMdrainT3 DMdrainT4 DMdrainT7 DMdrainT8 DMdrainTA.
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
Hypothesis HM : forall x : word, ~ AFgj.WIN ly regs0 (st_qglobal X) (bv_unsigned x) -> mem' x = mem0 x.
Hypothesis HWP : forall a, AFgj.WIN ly regs0 (st_qglobal X) a -> kHighMemBeg <= a -> apresent (w_H W) mem' a.
Hypothesis HMUT : forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0).
Hypothesis HC160 : val_mem tfibsegs m' (A_QUAR + 160) 8 (AFgj.LSZv (st_qglobal X) (st_qthread X)).
Hypothesis HC168 : val_mem tfibsegs m' (A_QUAR + 168) 8 (AFgj.LFv ly (st_qglobal X) (st_qthread X)).
Hypothesis HC176 : val_mem tfibsegs m' (A_QUAR + 176) 8 (AFgj.TLv ly (st_qthread X)).
Hypothesis HC184 : val_mem tfibsegs m' (A_QUAR + 184) 8 (AFgj.LBv (st_qglobal X) (st_qthread X)).
Hypothesis HT0 : val_mem tfibsegs m' (ly_T ly + t_qc) 8 0.
Hypothesis HT8 : val_mem tfibsegs m' (ly_T ly + t_qc + 8) 8 0.
Hypothesis HT16 : val_mem tfibsegs m' (ly_T ly + t_qc + 16) 8 0.
Hypothesis HT24 : val_mem tfibsegs m' (ly_T ly + t_qc + 24) 8 0.
Hypothesis HGT : lcn ly (iwB B ly) m' (G ++ Tq) 0.
Hypothesis HTne : Tq <> [].
Hypothesis HWF : qc_bytes (st_qthread X) = sum_bytes Tq /\ qc_bytes (st_qglobal X) = sum_bytes G.
Hypothesis HQW : qc_bytes (YFeuC.transfer_g X) = AFgj.LBv (st_qglobal X) (st_qthread X).

Local Notation S' := (sxf X).

Lemma Slist : qc_list (st_qglobal S') = G ++ Tq.
Proof. reflexivity. Qed.
Lemma Sthread : st_qthread S' = qc0.
Proof. reflexivity. Qed.

Lemma Scount : Z.of_nat (length (G ++ Tq)) = AFgj.LSZv (st_qglobal X) (st_qthread X).
Proof. unfold AFgj.LSZv, AFgj.GSZv, AFgj.TSZv. rewrite length_app. lia. Qed.

Lemma Sfirst : (match G ++ Tq with [] => 0 | b :: _ => SB + b_self b end) = AFgj.LFv ly (st_qglobal X) (st_qthread X).
Proof. unfold AFgj.LFv, AFgj.GFv, AFgj.TFv. destruct G as [|b t]; reflexivity. Qed.

Lemma Slast : (match rev (G ++ Tq) with [] => 0 | b :: _ => SB + b_self b end) = AFgj.TLv ly (st_qthread X).
Proof.
unfold AFgj.TLv. rewrite rev_app_distr. destruct (rev Tq) as [|b t] eqn:ER; [|reflexivity].
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
-
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
-
  unfold qc_cells. cbn [qc_list qc_bytes].
  apply Forall_cons.
  { apply (val_mem_cellZ B ly (w_H W) mem' (AInst o_q_size) 8 _). cbn [aeval].
    match goal with |- val_mem _ _ ?a _ ?v =>
      replace a with (A_QUAR + 160) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia);
      replace v with (AFgj.LSZv (st_qglobal X) (st_qthread X)) by (rewrite <- Scount; reflexivity) end.
    exact HC160. }
  apply Forall_cons.
  { apply (val_mem_cell B ly (w_H W) mem' (aoff (AInst o_q_size) 8) 8 _). cbn [aeval aoff batch_exp].
    match goal with |- val_mem _ _ ?a _ ?v => replace a with (A_QUAR + 168) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia);
      replace v with (AFgj.LFv ly (st_qglobal X) (st_qthread X)) by (rewrite <- Sfirst; destruct (G ++ Tq); reflexivity) end.
    exact HC168. }
  apply Forall_cons.
  { apply (val_mem_cell B ly (w_H W) mem' (aoff (AInst o_q_size) 16) 8 _). cbn [aeval aoff batch_exp].
    match goal with |- val_mem _ _ ?a _ ?v => replace a with (A_QUAR + 176) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia);
      replace v with (AFgj.TLv ly (st_qthread X)) by (rewrite <- Slast; destruct (rev (G ++ Tq)); reflexivity) end.
    exact HC176. }
  apply Forall_cons.
  { apply (val_mem_cellZ B ly (w_H W) mem' (aoff (AInst o_q_size) 24) 8 _). cbn [aeval aoff].
    match goal with |- val_mem _ _ ?a _ ?v => replace a with (A_QUAR + 184) by (rewrite <- AQ, <- Hinst; unfold o_quar, o_q_size; lia) end.
    rewrite HQW. exact HC184. }
  exact (batch_cells_of_lcn B ly (w_H W) mem' (G ++ Tq) HGT).
Qed.
End g.
End f.
