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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import StrlenDef SetShadowDef SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import StackFreeDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv TjSpec ReacDiscoTableAge DiscoRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import FindEntry CheckTable CheckSighting JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxName ReacDiscoTableObserve ReacDiscoGateShouldPush.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableInit ReacDiscoGateInit
  ReacDiscoPeerLockInit ReacHuntInit ReacHuntPin ReacHuntSilenceProven ReacHuntStep ReacHuntVerdictName ReacHuntRole
  ReacHuntHeardAnything ReacDiscoClassify ReacDiscoClassifyOnSegment ReacHuntObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition TJ_STK : Z := 16384 + 640 + 4096.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Variable SF6_ENTRY : Z.

Record dentry_env : Prop := mkDEnv {
  de_laws : AR_laws SEGS B;
  de_tl : PALib B;
  de_tlf : PALibF B;
  de_ml : model_laws (as_universe B);
  de_mtl : ameter_laws MT;
  de_mt_triv : MT = ameter_triv;
  de_smp : stack_malloc_progressP B;
  de_ffl : frame_flag_lawP SEGS B;
  de_hro : forall rd, arodata_okS SEGS B RLO RHI rd -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rd;
  de_hxl : forall n, ACC_LIB MT <= XM_LIB n;
  de_hxn : forall n, ACC_LIB MT <= XN_LIB n;
  de_dzs : dglob_zshadow B;
  de_dgc : dglob_const B;
  de_dro : disco_ro_unowned B;
  de_gm : globs_marked SEGS B disco_globs;
  de_hv : img_shadow_vis SEGS B;
  de_dcro : dimg_consts_of_ro_stmt B;
  de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a;
  de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
    ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4);
  de_snp_ro : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a;
  de_snp_un : forall a, Exists (in_zr a) snp_cr ->
    ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4);
  de_ail : asink_img_laws SEGS B tfib_K;
  de_kcan : ak_can_got tfib_K = AE2k.FF_got_canary /\ ak_canary tfib_K = AE2k.FF_canary;
  de_duniv : duniv_ok B;
  de_amalloc : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS B;
  de_afree : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS B;
  de_amemcpy : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy);
  de_amemset : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset);
  de_abcmp : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp);
  de_asm6 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 6;
  de_asfw6 : forall fq : YK11.FPState, astack_free_realizes (fx := fq) SEGS B SF6_ENTRY 6;
  de_sf6 : SIGMA DS___asan_stack_free_6 = SF6_ENTRY;
  de_assf8 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_f8) 0xf8;
  de_ass00 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_00) 0;
  de_astrlen : forall fq : YK11.FPState,
    astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA DS___interceptor_trampoline_strlen);
  de_asnprintf : forall fq : YK11.FPState,
    SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi AE2k.FF_got_canary AE2k.FF_canary
      YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi snp_cr (SIGMA DS___interceptor_trampoline_snprintf);
  de_ttinit : treac_disco_table_init_spec B;
  de_tginit : treac_disco_gate_init_spec B;
  de_tlinit : treac_disco_peer_lock_init_spec B;
  de_thinit : treac_hunt_init_spec B;
  de_thpin : treac_hunt_pin_spec B;
  de_thsil : treac_hunt_silence_proven_spec B;
  de_tage : treac_disco_table_age_spec B;
  de_tchkt : tcheck_table_spec B;
  de_ttjson : tj_specP B TJ_STK 0 dimg_tj;
  de_tjsc : tjson_scalar_spec B;
  de_tjtok : tjtok_is_spec B;
  de_tbox : treac_box_name_spec B;
  de_thstep : treac_hunt_step_spec B;
  de_tvname : treac_hunt_verdict_name_spec B;
  de_throle : treac_hunt_role_spec B;
  de_thheard : treac_hunt_heard_anything_spec B;
  de_tcls : treac_disco_classify_spec B;
  de_tclss : treac_disco_classify_on_segment_spec B;
  de_tchks : tcheck_sighting_spec B;
  de_tgpush : treac_disco_gate_should_push_spec B;
  de_tfind : tfind_entry_spec B;
  de_ttobs : treac_disco_table_observe_spec B;
  de_thobs : treac_hunt_observe_spec B }.
Definition dentry_walk_ok : Prop := dentry_env -> tLLVMFuzzerTestOneInput_walk B MT XM_LIB XN_LIB RLO RHI tfib_K.
End h.
End f.
End d.
