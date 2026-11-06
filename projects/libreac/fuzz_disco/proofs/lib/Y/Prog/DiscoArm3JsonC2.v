(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 666 of its 732 lines of code are new or changed and 1212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntHobsS3.v, with its module paths and module names changed; 43 of its 83 lines of code are new or changed and 692 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YCbp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0d YP0c YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntBodyStmt DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonCallee
DiscoArm3JsonC2Defs DiscoArm3JsonC2Mod DiscoArm3JsonC2V DiscoArm3JsonC2R DiscoArm3JsonC2Tk DiscoArm3JsonC2M
DiscoArm3JsonC2Cp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_jscalar_model disco_json_text disco_json_reader_model.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis DBCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis DBRT : d_body_rt_stmt B.

Lemma jc2_from_call : forall (d kb : nat) (P : jc2p) (W : world SEGS) (c : config),
  (kb < 6)%nat -> (6 - kb <= d)%nat ->
  jc2_call B MT XM_LIB RLO RHI tfib_K P kb W c ->
  SRr SEGS W c (jc2_out B MT XM_LIB RLO RHI tfib_K P).
Proof.
  induction d as [|d IH]; intros kb P W c Hkb Hd Hc; [lia|].
  eapply SRr_bind;
    [eapply (jc2_jtk B MT XM_LIB RLO RHI tfib_K LAWS MT_TRIV DROH DCRO TJTOK DBCK de_mc_ro de_mc_un);
     eassumption|].
  intros W1 c1 _ (res & HR).
  eapply SRr_bind; [exact (jc2_hopR B MT XM_LIB RLO RHI tfib_K LAWS P kb res W1 c1 Hkb HR)|].
  intros W2 c2 _ [HM | [(Hs & HC) | HO]].
  - eapply SRr_bind; [exact (jc2_hopM B MT XM_LIB RLO RHI tfib_K LAWS P kb W2 c2 HM)|].
    intros W3 c3 _ HY. exact (jc2_cp B MT XM_LIB RLO RHI tfib_K LAWS AMEMCPY DBRT P kb W3 c3 HY).
  - exact (IH (S kb) P W2 c2 Hs ltac:(lia) HC).
  - apply SRr_ret. exact HO.
Qed.

Theorem a3j_C2 : jseg_C2 B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad W c HV.
  pose (P := mkJC2 cx h i n now op W0 c0 T0 T1 buf fin ip j2 kk ks kl vk vs vl cur c2 count acc vpad).
  eapply SRr_bind; [exact (jc2_hopV B MT XM_LIB RLO RHI tfib_K LAWS P W c HV)|].
  intros W1 c1 _ HC.
  eapply SRr_mono; [exact (jc2_from_call 6 0 P W1 c1 ltac:(lia) ltac:(lia) HC)|].
  intros W2 c2' _ HO. exists j2. exact HO.
Qed.

End h.
End f.
End d.
