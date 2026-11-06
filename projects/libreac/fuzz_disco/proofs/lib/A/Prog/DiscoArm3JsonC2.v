(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 60 of its 91 lines of code are new or changed and 38 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntRec.v, with its module paths changed; 44 of its 77 lines of code are new or changed and 58 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
JtokIs DiscoEntryInv DiscoEntBodyStmt DiscoRo DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonC2Defs
DiscoArm3JsonC2V DiscoArm3JsonC2R DiscoArm3JsonC2M DiscoArm3JsonC2Tk DiscoArm3JsonC2Cp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_jscalar_model disco_json_text disco_json_reader_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
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
Hypothesis de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).

Lemma jc2_from_call : forall (d kb : nat) (P : jc2p) (W : world SEGS) (c : config),
  (kb < 6)%nat -> (6 - kb <= d)%nat ->
  jc2_call B MT XM_LIB RLO RHI tfib_K P kb W c ->
  SRr SEGS W c (jc2_out B MT XM_LIB RLO RHI tfib_K P).
Proof.
  induction d as [|d IH]; intros kb P W c Hkb Hd Hc; [lia|].
  eapply SRr_bind; [eapply jc2_jtk; eassumption|].
  intros W1 c1 _ (res & HR).
  eapply SRr_bind; [exact (jc2_hopR B MT XM_LIB RLO RHI tfib_K LAWS P kb res W1 c1 Hkb HR)|].
  intros W2 c2 _ [HM | [(Hs & HC) | HO]].
  - eapply SRr_bind; [exact (jc2_hopM B MT XM_LIB RLO RHI tfib_K LAWS P kb W2 c2 HM)|].
    intros W3 c3 _ HY. eapply jc2_cp; eassumption.
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
