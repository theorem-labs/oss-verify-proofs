(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B,
   PHASE 5: the table-order loop of fuzz_reply.c:646-653, fuzz_reply.asan-ubsan 0x84b78 (GT0) to check_shape_done's
   call at 0x84c84 (GCSD), gp5_t0_csd at the end of this file.  A PORT of image A's
   lib/A/W_LLVMFuzzerTestOneInput_gone_p5.v (a working branch 32b23a20c3e) gp5_inner / gp5_outer /
   gp5_t0_csd, over part a (W_LLVMFuzzerTestOneInput_gone_p5a.v: the cut points P5OH / P5IH / P5T / P5C / P5OT and the
   walks gp5_t0 / gp5_oh / gp5_ih / gp5_it / gp5_ot) and part b (W_LLVMFuzzerTestOneInput_gone_p5b.v: the calls gp5_c8 /
   gp5_c3), on the base lib/B/W_LLVMFuzzerTestOneInput_gone_base.v (a working branch 85b530db754).
   Section hypotheses (each the base's or the cut's text): GN_CNL, GN_CSHE (the kit's cnl_spec / cshe_spec per slot),
   GN_RI_step, GN_RI_end (the model's obligations), GN_HGs, GN_HGcells, GN_ROM_PIN, GN_HZS, GN_CELLS_ERRNO,
   GN_ERRNO_LOW (the instance's facts), ameter_laws, the cut's glob_wr_law (:316) and errno_law (:318).
   check_no_loss's readable-stack premise comes from the cut's STKR (base gn_stkr), not a hypothesis. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListRep RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_p5a W_LLVMFuzzerTestOneInput_gone_p5b.
(* The sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) rule 3): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section gp5.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Hypothesis HGs : GN_HGs G_fr.
Hypothesis HGcells : GN_HGcells G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
Hypothesis HZS : GN_HZS B.
Hypothesis HCE : GN_CELLS_ERRNO B.
Hypothesis RIend : GN_RI_end B MT LS RINV.
Hypothesis GWL : glob_wr_law G_fr.
Hypothesis ERRL : errno_law B.
Hypothesis HERR : GN_ERRNO_LOW B.
(* ---- the two callee texts and the loop's model obligation (A's p5 set: CNL, CSHE, RIstep, ML) ---- *)
Variable MMAX : Z.
Hypothesis CNL : GN_CNL B MT MMAX.
Hypothesis CSHE : GN_CSHE B MT.
Hypothesis RIstep : GN_RI_step B MT LS RINV MMAX.
Hypothesis ML : ameter_laws MT.
(* parts a and b at this Section's variables *)
Local Notation P5OH := (W_LLVMFuzzerTestOneInput_gone_p5a.P5OH B MT G_fr fr_FP LS RINV).
Local Notation P5IH := (W_LLVMFuzzerTestOneInput_gone_p5a.P5IH B MT G_fr fr_FP LS RINV).
Local Notation P5T := (W_LLVMFuzzerTestOneInput_gone_p5a.P5T B MT G_fr fr_FP LS RINV).
Local Notation P5OT := (W_LLVMFuzzerTestOneInput_gone_p5a.P5OT B MT G_fr fr_FP LS RINV).
Local Notation gp5_t0 := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_t0 B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG
  LS RINV RIend HERR).
Local Notation gp5_oh := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_oh B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG
  LS RINV).
Local Notation gp5_ih := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_ih B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG
  LS RINV HZS).
Local Notation gp5_it := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_it B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG
  LS RINV).
Local Notation gp5_ot := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_ot B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG
  LS RINV RIend).
Local Notation gp5_c8 := (W_LLVMFuzzerTestOneInput_gone_p5b.gp5_c8 B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG
  LS RINV HGs HGcells HROMPIN HZS GWL ERRL MMAX CNL RIstep ML).
Local Notation gp5_c3 := (W_LLVMFuzzerTestOneInput_gone_p5b.gp5_c3 B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG
  LS RINV HGs HGcells HROMPIN HZS HCE GWL ERRL CSHE ML).
(* ================================================================== the two loops *)
(* the inner loop, from 0x84888 at slot k to 0x8493c: four slots, each passed or checked *)
Lemma gp5_inner : forall n cx t m m1 i k W c, (k + n = 4)%nat ->
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> P5IH cx t m m1 i k W c ->
  SRr segs W c (P5OT cx t m m1 i).
Proof.
  induction n as [|n IH]; intros cx t m m1 i k W c Hn HB HI.
  - exfalso. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _). lia.
  - assert (AT : forall W1 c1, P5T cx t m m1 i k W1 c1 -> SRr segs W1 c1 (P5OT cx t m m1 i)).
    { intros W1 c1 HT. eapply SRr_bind; [exact (gp5_it cx t m m1 i k W1 c1 HB HT)|].
      intros W2 c2 _ [(Hlt & HI2) | (Heq & HO)].
      - exact (IH cx t m m1 i (S k) W2 c2 ltac:(lia) HB HI2).
      - apply SRr_ret. exact HO. }
    eapply SRr_bind; [exact (gp5_ih cx t m m1 i k W c HB HI)|].
    intros W1 c1 _ [HT | HC]; [exact (AT W1 c1 HT)|].
    eapply SRr_bind; [exact (gp5_c8 cx t m m1 i k W1 c1 HB HC)|].
    intros W2 c2 _ HM.
    eapply SRr_bind; [exact (gp5_c3 cx t m m1 i k W2 c2 HB HM)|].
    intros W3 c3 _ HT. exact (AT W3 c3 HT).
Qed.
(* the outer loop, from 0x84870 at entry i to 0x8494c *)
Lemma gp5_outer : forall n cx t m m1 i W c, (i + n = length (lm_es m1))%nat ->
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> P5OH cx t m m1 i W c ->
  SRr segs W c (fun W' c' => exists mc, GCSD B G_fr fr_FP LS RINV cx t m mc W' c').
Proof.
  induction n as [|n IH]; intros cx t m m1 i W c Hn HB HO.
  - exfalso. destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia.
  - eapply SRr_bind; [exact (gp5_oh cx t m m1 i W c HB HO)|].
    intros W1 c1 _ HI.
    eapply SRr_bind; [exact (gp5_inner 4 cx t m m1 i 0 W1 c1 eq_refl HB HI)|].
    intros W2 c2 _ HOT.
    eapply SRr_bind; [exact (gp5_ot cx t m m1 i W2 c2 HB HOT)|].
    intros W3 c3 _ [(Hlt & HO3) | HG3].
    + exact (IH cx t m m1 (S i) W3 c3 ltac:(lia) HB HO3).
    + apply SRr_ret. exact HG3.
Qed.

(* ================================================================== GP5 *)
Lemma gp5_t0_csd : forall cx t m m1 W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> GT0 B MT G_fr fr_FP LS RINV cx t m m1 W c ->
  SRr segs W c (fun W' c' => exists mc, GCSD B G_fr fr_FP LS RINV cx t m mc W' c').
Proof.
  intros cx t m m1 W c HB HT.
  eapply SRr_bind; [exact (gp5_t0 cx t m m1 W c HB HT)|].
  intros W1 c1 _ [(Hlt & HO) | HG1].
  - exact (gp5_outer (length (lm_es m1)) cx t m m1 0 W1 c1 eq_refl HB HO).
  - apply SRr_ret. exact HG1.
Qed.

End gp5.
