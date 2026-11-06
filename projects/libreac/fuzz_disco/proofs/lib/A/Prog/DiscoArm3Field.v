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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoEntBody DiscoEntBodyCall.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacBoxName.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require
DiscoArm3FieldE0 DiscoArm3FieldPH DiscoArm3FieldPF
DiscoArm3FieldPFA DiscoArm3FieldPFXB DiscoArm3FieldPFC DiscoArm3FieldPFXD
DiscoArm3FieldMDAC DiscoArm3FieldMDA3All
DiscoArm3FieldMDB.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
Import ListNotations.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis ASNPRINTF : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi AE2k.FF_got_canary AE2k.FF_canary YImgTop.IMG_LO YImgTop.IMG_TOP
    disco_fmt_lo disco_fmt_hi snp_cr (SIGMA DS___interceptor_trampoline_snprintf).
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis TBOX : ReacBoxName.treac_box_name_spec B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis SNPRO : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis SNPUN : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis MCRO : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis DAIL : asink_img_laws SEGS B tfib_K.
Hypothesis DKCAN : ak_can_got tfib_K = AE2k.FF_got_canary /\ ak_canary tfib_K = AE2k.FF_canary.

Lemma a3_field_pfx : seg_pfx_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  pose proof (DiscoEntBody.d_body_rt B) as DBRT.
  pose proof (DiscoEntBody.d_body_tobs B MT XM_LIB RLO RHI tfib_K) as DBTOBS.
  pose proof (DiscoEntBodyCall.d_body_pcall B MT XM_LIB RLO RHI tfib_K) as DBPC.
  apply seg_pfx_of_cases. intros p Hp.
  apply seg_pfx_p_of_parts.
  - apply DiscoArm3FieldPFA.a3f_pfa; eassumption.
  - apply DiscoArm3FieldPFXB.a3f_pfxb; eassumption.
  - apply DiscoArm3FieldPFC.a3f_pfc; eassumption.
  - apply DiscoArm3FieldPFXD.a3f_pfxd; eassumption.
Qed.

Lemma a3_field_md : seg_md_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  pose proof (DiscoEntBody.d_body_rt B) as DBRT.
  pose proof (DiscoEntBodyCall.d_body_pcall B MT XM_LIB RLO RHI tfib_K) as DBPC.
  apply seg_md_of_cases. intros p Hp.
  apply seg_md_p_of_parts.
  - eapply DiscoArm3FieldMDAC.a3f_mda_of_a3; try eassumption.
    eapply DiscoArm3FieldMDA3All.md_a3_all; eassumption.
  - apply DiscoArm3FieldMDB.a3f_mdb; eassumption.
Qed.

Theorem a3_field : a3_field_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  pose proof (DiscoEntBody.d_body_rt B) as DBRT.
  pose proof (DiscoEntBodyCall.d_body_pcall B MT XM_LIB RLO RHI tfib_K) as DBPC.
  apply a3f_compose.
  - apply DiscoArm3FieldE0.a3f_e0; eassumption.
  - apply DiscoArm3FieldPH.a3f_ph; eassumption.
  - apply DiscoArm3FieldPF.a3f_pf; eassumption.
  - exact a3_field_pfx.
  - exact a3_field_md.
Qed.

End h.
End f.
End d.
