(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from lib/A/DMdrainTF.v's statement of ret_arm (its premises unchanged), restated at the drain's re-hide twin (DIfaceRh.drain_leaf_g_rh over YG0dH.amreal'); the proof is one lift of DMdrainTF.ret_arm. *)
(* F1 priming row R3 (re-hide at a secondary recycle): the drain's RETURN arm at the re-hide twin.  The arm recycles
   nothing, so it re-hides nothing: its twin is DMdrainTF.ret_arm lifted (YG0dH.amreal_amreal') with the leaf's
   weakening (DIfaceRh.drain_leaf_g_rh_of).  A new file, so that DMdrainTF.v stays byte-unchanged (as DIfaceRh.v).
   rule 24: no function proved (kind: one lift of a composition already proved). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFey YFgj YFhf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DIfaceR MnEnq DMwalkIF DMdrainM.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMdrainTF DIfaceRh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section g.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
(* DMdrainTF.ret_arm's Section hypotheses, unchanged *)
Hypothesis TB : TfibSyms B.
Hypothesis QV : di_qview_t B ARX L24 QB.
Hypothesis QO : di_qowned_t ARX AOX L24 QB.
Hypothesis QS : di_stack_t ARX AOX.
Hypothesis RQX : di_requar_x_t B ARX AOX L24 QB.
Hypothesis QBB : forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29.

Theorem ret_arm_rh : forall inst ly X W regs mem md,
drain_pre_cf B ARX L24 QB inst ly X W regs mem md ->
qc_bytes (gxf X) <= kQuarantineMax ->
amreal' tfibsegs YGcfRehidePost.RZ_cf (drain_body_cf X X) W (cfg_at tfibsegs dg_drain regs mem md)
  (DIfaceRh.drain_leaf_g_rh B ARX AOX (MnEnq.acall_raw_em_x B AOX) inst ly X W regs mem md).
Proof.
intros inst ly X W regs mem md PRE HLE.
eapply amreal'_mono; [| apply amreal_amreal'; eapply DMdrainTF.ret_arm; eassumption].
intros r W' c' HL. exact (DIfaceRh.drain_leaf_g_rh_of B ARX AOX _ inst ly X W regs mem md r W' c' HL).
Qed.
End g.
End f.
Print Assumptions ret_arm_rh.
