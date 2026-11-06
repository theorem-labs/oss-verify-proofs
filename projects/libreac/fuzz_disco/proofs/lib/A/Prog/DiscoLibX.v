(* fuzz_disco A (asan) LLVMFuzzerTestOneInput: the closing theorem disco_lib_x_all (closure-map rows A-G1 and A-G9).
   disco_lib_x_all is DiscoEntryInv.tLLVMFuzzerTestOneInput_spec (the frm0-guarded contract) at PI := PB_disco,
   B := AD2l.TfibB, MT := ameter_triv, XM_LIB = XN_LIB := fun _ => 0, RLO / RHI := disco_relro_lo / disco_relro_hi,
   tfib_K := AE2k.tfib_K, SK := AE2k.tfib_sink_head, LS := DiscoAsanTop.disco_shape, generic in rc. It is
   DiscoEntTop.d_walk_to_spec applied to DiscoEntWalk.d_entry_walk_ok and to a dentry_env record built field by field.
   disco_lib_x_all_acfn has exactly the type of S1's H_PROG_LIBX (lib/A/AD2p.v:55-59, a Theorem Labs lane landing 25
   b2ef98f0a6d): G2's ACfn.tfib_lib_contract_x_all under DiscoAsanT.H_RO_stmt rc, which the proof does not use.
   No Section hypothesis is left: de_asnprintf is dl_asnprintf (a Theorem Labs lane's FMsnprintfDiscoSnp.disco_snprintf_R,
   a Theorem Labs lane landing 24 5ed86fcc436) and de_ttjson is dl_ttjson (a Theorem Labs lane's
   TjTop.pb_reac_disco_table_json_gen TJ_STK dimg_tj, a working branch cea77c23f9c). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import StrlenDef SetShadowDef SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import StackFreeDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv TjSpec ReacDiscoTableAge DiscoRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import FindEntry CheckTable CheckSighting JtokIs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxName ReacDiscoTableObserve ReacDiscoGateShouldPush.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableInit ReacDiscoGateInit
  ReacDiscoPeerLockInit ReacHuntInit ReacHuntPin ReacHuntSilenceProven ReacHuntStep ReacHuntVerdictName ReacHuntRole
  ReacHuntHeardAnything ReacDiscoClassify ReacDiscoClassifyOnSegment ReacHuntObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryShapes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k AD2l AF0m ACej AD1u AF0w AF0q AE2s AF0s AF0u ACfn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require DiscoAsanTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YG0q YG05 YG0t.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require MemchrDef AcpySameDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require
  StackMalloc0 StackMalloc3 StackMalloc6 StackFree6S StackFree6Tbl McUnowned SetShadow Strlen Memchr AcpySame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require
  DiscoImg DiscoLaws DiscoImgFacts DiscoImgSnp DiscoDcro DiscoDuniv JsonScalarImg CtrlParseImg
  ClassifyCore ClassifyCoreWalk CtrlParse CtrlParseWalk ReacPortsParse KindOfLink1 ReacArbitrate ReacRivalKindOf
  ReacSenderKind ReacMasterOnlyCadenceNs ReacRateSnap SbDec SbDecPb ReacBoxNamePb ReacDiscoTableObserve_W
  ReacHuntObserveAll DiscoAmem DiscoEntTop DiscoEntWalk TjTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YFrm0 YFrm0Eq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require FMsnprintfDiscoSnp DiscoAsanT DiscoRoA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance DiscoImgFacts.disco_ro_below_ofl | 0.
#[local] Existing Instance YK11.fx0.
#[local] Abbreviation PI := DiscoImg.PB_disco.
#[local] Abbreviation SEGS := (@pa_segs _ disco_listing DiscoImg.PB_disco).
#[local] Abbreviation SIGMA := (@pa_sigma _ disco_listing DiscoImg.PB_disco).
#[local] Abbreviation TB := AD2l.TfibB.
#[local] Abbreviation XL0 := (fun _ : Z => 0).
#[local] Abbreviation RLO := DiscoImg.disco_relro_lo.
#[local] Abbreviation RHI := DiscoImg.disco_relro_hi.

Section d. Context {rc : YM05.RunCeil}.

Lemma dl_laws : AR_laws SEGS TB.
Proof. exact (YG0q.AR_laws_ok SEGS TB). Qed.

Lemma dl_ml : model_laws (as_universe TB).
Proof. exact (YG05.model_laws_ok (as_universe TB) ACej.Tfib_universe_ok). Qed.

Lemma dl_mtl : ameter_laws ameter_triv.
Proof. exact YCbp.ameter_triv_laws. Qed.

Lemma dl_smp : stack_malloc_progressP TB.
Proof. exact (YG05.stack_malloc_progress (as_universe TB)). Qed.

Lemma dl_asf : astack_free_law SEGS TB.
Proof. exact (YG0t.astack_free_law_ok SEGS TB). Qed.

Lemma dl_hro : forall rd, arodata_okS SEGS TB RLO RHI rd -> arodata_okP SEGS pa_relro_lo pa_relro_hi TB rd.
Proof. exact (fun rd H => H). Qed.

Lemma dl_hxl : forall n, ACC_LIB ameter_triv <= XL0 n.
Proof. intros n. unfold ACC_LIB, ACC_PRO, ACC_ITER, ameter_triv. cbn. lia. Qed.

Lemma disco_ro_hyps : d_ro_hyps (PI := PI) TB.
Proof. exact (DiscoRoA.disco_H_RO rc). Qed.

Lemma dl_dro : disco_ro_unowned TB.
Proof. exact (proj1 disco_ro_hyps). Qed.

Lemma dl_gm : globs_marked SEGS TB disco_globs.
Proof. exact (proj1 (proj2 disco_ro_hyps)). Qed.

Lemma dl_hv : img_shadow_vis SEGS TB.
Proof. exact (proj2 (proj2 disco_ro_hyps)). Qed.

Lemma dl_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Proof. intros a H. left. exact (McUnowned.mc_consts_in_rom a H). Qed.

Lemma dl_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4).
Proof. exact (McUnowned.mc_consts_unowned TB AD2l.TfibB_syms). Qed.

Lemma dl_snp_ro : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Proof. intros a H. left. exact (snp_cr_in_rom a H). Qed.

Lemma dl_snp_un : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4).
Proof. exact DiscoImgSnp.snp_cr_un_disco. Qed.

Lemma dl_ail : asink_img_laws SEGS TB AE2k.tfib_K.
Proof. pose proof dl_laws. pose proof AD2l.TfibB_syms. eapply AD1u.tfib_AIL; eassumption. Qed.

Lemma dl_kcan : ak_can_got AE2k.tfib_K = AE2k.FF_got_canary /\ ak_canary AE2k.tfib_K = AE2k.FF_canary.
Proof. split; reflexivity. Qed.

Lemma dl_amalloc : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS TB.
Proof. intros fq. exact (AF0w.tfib_amalloc_realizes (fx := fq) TB AD2l.TfibB_syms (fun t => eq_refl)). Qed.

Lemma dl_afree : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS TB.
Proof. intros fq. exact (AF0q.afree_realizes_closed (fx := fq) TB AD2l.TfibB_syms (fun t => eq_refl)). Qed.

Lemma dl_abcmp : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS TB (SIGMA DS___interceptor_trampoline_bcmp).
Proof. intros fq. exact (AE2s.bcmp_icpt_contract (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_amemcpy : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS TB OCpy (SIGMA DS___asan_memcpy).
Proof. intros fq. exact (DiscoAmem.tfibX_AMEMCPY (fx := fq)). Qed.

Lemma dl_amemset : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS TB OSet (SIGMA DS___asan_memset).
Proof. intros fq. exact (DiscoAmem.tfibX_AMEMSET (fx := fq)). Qed.

Lemma dl_asm0 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS TB 0.
Proof. intros fq. exact (StackMalloc0.stack_malloc0_contract (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_asm1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS TB 1.
Proof. intros fq. exact (AF0s.stack_malloc1_contract (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_asm2 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS TB 2.
Proof. intros fq. exact (AF0u.stack_malloc2_contract (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_asm3 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS TB 3.
Proof. intros fq. exact (StackMalloc3.stack_malloc3_contract (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_asm6 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS TB 6.
Proof. intros fq. exact (StackMalloc6.disco_stack_malloc6 fq TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_asfw6 : forall fq : YK11.FPState, astack_free_realizes (fx := fq) SEGS TB StackFree6Tbl.SF6_ENTRY 6.
Proof. intros fq. exact (StackFree6S.disco_stack_free6_shared fq TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_sf6 : SIGMA DS___asan_stack_free_6 = StackFree6Tbl.SF6_ENTRY.
Proof. vm_compute. reflexivity. Qed.

Lemma dl_assf8 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS TB (SIGMA DS___asan_set_shadow_f8) 0xf8.
Proof. intros fq. exact (SetShadow.disco_set_shadow_f8 (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_ass00 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS TB (SIGMA DS___asan_set_shadow_00) 0.
Proof. intros fq. exact (SetShadow.disco_set_shadow_00 (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_assf5 : forall fq : YK11.FPState, aset_shadow_realizes (fx := fq) SEGS TB (SIGMA DS___asan_set_shadow_f5) 0xf5.
Proof. intros fq. exact (SetShadow.disco_set_shadow_f5 (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_astrlen : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS TB MC_CONSTS_LO MC_CONSTS_HI (SIGMA DS___interceptor_trampoline_strlen).
Proof. intros fq. exact (Strlen.strlen_icpt_realizesM (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_asnprintf : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS TB (@pa_relro_lo _ disco_listing DiscoImg.PB_disco)
    (@pa_relro_hi _ disco_listing DiscoImg.PB_disco) AE2k.FF_got_canary AE2k.FF_canary YImgTop.IMG_LO YImgTop.IMG_TOP
    disco_fmt_lo disco_fmt_hi snp_cr (SIGMA DS___interceptor_trampoline_snprintf).
Proof. exact FMsnprintfDiscoSnp.disco_snprintf_R. Qed.

Lemma dl_amemchr : forall fq : YK11.FPState,
  MemchrDef.amemchr_realizesM (fx := fq) SEGS TB MC_CONSTS_LO MC_CONSTS_HI (SIGMA DS___interceptor_trampoline_memchr).
Proof. intros fq. exact (Memchr.memchr_icpt_realizesM (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

Lemma dl_amemcpyeq : forall fq : YK11.FPState,
  AcpySameDef.acpy_same_realizes (fx := fq) SEGS TB (SIGMA DS___asan_memcpy).
Proof. intros fq. exact (AcpySame.acpy_same_icpt (fx := fq) TB dl_laws AD2l.TfibB_syms). Qed.

#[local] Ltac dl_env :=
  pose proof dl_laws as LAWS; pose proof (DiscoLaws.disco_PALib : PALib (PI := PI) TB) as TL;
  pose proof (DiscoLaws.disco_PALibF : PALibF (PI := PI) TB) as TLF; pose proof dl_ml as ML; pose proof dl_smp as SMP;
  pose proof (DiscoLaws.disco_FFL : frame_flag_lawP SEGS TB) as FFL; pose proof dl_asf as ASF;
  pose proof dl_dro as DRO; pose proof dl_gm as GM; pose proof dl_hv as HV;
  pose proof dl_amemcpy as AMEMCPY; pose proof dl_amemset as AMEMSET; pose proof dl_abcmp as ABCMP;
  pose proof dl_astrlen as ASTRLEN; pose proof dl_amemchr as AMEMCHR; pose proof dl_amemcpyeq as AMEMCPYEQ;
  pose proof dl_assf5 as ASSF5; pose proof dl_asm0 as ASM0; pose proof dl_asm1 as ASM1; pose proof dl_asm2 as ASM2;
  pose proof dl_asm3 as ASM3; pose proof dl_mc_un as MCUN.

Lemma dl_kind : KindOfLink1.tkind_of_link1_spec (PI := PI) TB.
Proof. dl_env. eapply KindOfLink1.pb_kind_of_link1; eassumption. Qed.

Lemma dl_tports : ReacPortsParse.treac_ports_parse_spec (PI := PI) TB.
Proof. dl_env. eapply ReacPortsParse.pb_reac_ports_parse; eassumption. Qed.

Lemma dl_tparse : CtrlParse.treac_ctrl_parse_spec (PI := PI) TB.
Proof.
  dl_env. pose proof dl_kind as KIND. pose proof CtrlParseImg.cp_HG15_disco as HG15.
  pose proof CtrlParseImg.cp_HBC_RNG_disco as HBC_RNG.
  pose proof (CtrlParseImg.cp_HBC_VAL_disco TB dl_dro) as HBC_VAL.
  eapply CtrlParseWalk.pb_reac_ctrl_parse; eassumption.
Qed.

Lemma dl_tcore : ClassifyCore.tclassify_core_spec (PI := PI) TB.
Proof.
  dl_env. pose proof dl_tports as TPORTS. pose proof dl_tparse as TPARSE.
  eapply ClassifyCoreWalk.pb_classify_core_disco; eassumption.
Qed.

Lemma dl_trate : ReacRateSnap.treac_rate_snap_spec (PI := PI) TB.
Proof. dl_env. eapply ReacRateSnap.pb_reac_rate_snap; eassumption. Qed.

Lemma dl_tmoc : ReacMasterOnlyCadenceNs.treac_master_only_cadence_ns_spec (PI := PI) TB.
Proof. dl_env. pose proof dl_trate as TRATE. eapply ReacMasterOnlyCadenceNs.pb_reac_master_only_cadence_ns; eassumption. Qed.

Lemma dl_trival : ReacRivalKindOf.treac_rival_kind_of_spec (PI := PI) TB.
Proof. dl_env. eapply ReacRivalKindOf.pb_reac_rival_kind_of; eassumption. Qed.

Lemma dl_tsender : ReacSenderKind.treac_sender_kind_spec (PI := PI) TB.
Proof.
  dl_env. pose proof dl_tmoc as TMOC. pose proof dl_trival as TRIVAL.
  eapply ReacSenderKind.pb_reac_sender_kind; eassumption.
Qed.

Lemma dl_tarb : ReacArbitrate.treac_arbitrate_spec (PI := PI) TB.
Proof. dl_env. pose proof dl_trival as TRIVAL. eapply ReacArbitrate.pb_reac_arbitrate; eassumption. Qed.

Lemma dl_tsbdec : SbDec.tsb_dec_spec (PI := PI) TB.
Proof. dl_env. eapply SbDecPb.pb_sb_dec; eassumption. Qed.

Lemma dl_ttinit : treac_disco_table_init_spec (PI := PI) TB.
Proof. dl_env. eapply ReacDiscoTableInit.pb_reac_disco_table_init; eassumption. Qed.

Lemma dl_tginit : treac_disco_gate_init_spec (PI := PI) TB.
Proof. dl_env. eapply ReacDiscoGateInit.pb_reac_disco_gate_init; eassumption. Qed.

Lemma dl_tlinit : treac_disco_peer_lock_init_spec (PI := PI) TB.
Proof. dl_env. eapply ReacDiscoPeerLockInit.pb_reac_disco_peer_lock_init; eassumption. Qed.

Lemma dl_thinit : treac_hunt_init_spec (PI := PI) TB.
Proof.
  dl_env. pose proof dl_ttinit as TTABLEINIT. pose proof dl_tlinit as TPEERLOCKINIT.
  eapply ReacHuntInit.pb_reac_hunt_init; eassumption.
Qed.

Lemma dl_thpin : treac_hunt_pin_spec (PI := PI) TB.
Proof. dl_env. eapply ReacHuntPin.pb_reac_hunt_pin; eassumption. Qed.

Lemma dl_thsil : treac_hunt_silence_proven_spec (PI := PI) TB.
Proof. dl_env. eapply ReacHuntSilenceProven.pb_reac_hunt_silence_proven; eassumption. Qed.

Lemma dl_tage : treac_disco_table_age_spec (PI := PI) TB.
Proof. dl_env. eapply ReacDiscoTableAge.pb_reac_disco_table_age; eassumption. Qed.

Lemma dl_tchkt : tcheck_table_spec (PI := PI) TB.
Proof. dl_env. eapply CheckTable.pb_check_table; eassumption. Qed.

Lemma dl_tjsc : tjson_scalar_spec (PI := PI) TB.
Proof. dl_env. eapply JsonScalar.pb_json_scalar; eassumption. Qed.

Lemma dl_tjtok : tjtok_is_spec (PI := PI) TB.
Proof. dl_env. eapply JtokIs.pb_jtok_is; eassumption. Qed.

Lemma dl_tbox : treac_box_name_spec (PI := PI) TB.
Proof. dl_env. pose proof dl_tsbdec as HSBDEC. eapply ReacBoxNamePb.pb_reac_box_name; eassumption. Qed.

Lemma dl_thstep : treac_hunt_step_spec (PI := PI) TB.
Proof.
  dl_env. pose proof dl_tage as TAGE. pose proof dl_tarb as TARB. pose proof dl_tsender as TSENDER.
  eapply ReacHuntStep.pb_reac_hunt_step; eassumption.
Qed.

Lemma dl_tvname : treac_hunt_verdict_name_spec (PI := PI) TB.
Proof. dl_env. eapply ReacHuntVerdictName.pb_reac_hunt_verdict_name; eassumption. Qed.

Lemma dl_throle : treac_hunt_role_spec (PI := PI) TB.
Proof. dl_env. eapply ReacHuntRole.pb_reac_hunt_role; eassumption. Qed.

Lemma dl_thheard : treac_hunt_heard_anything_spec (PI := PI) TB.
Proof. dl_env. eapply ReacHuntHeardAnything.pb_reac_hunt_heard_anything; eassumption. Qed.

Lemma dl_tcls : treac_disco_classify_spec (PI := PI) TB.
Proof. dl_env. pose proof dl_tcore as TCLS. eapply ReacDiscoClassify.pb_reac_disco_classify; eassumption. Qed.

Lemma dl_tclss : treac_disco_classify_on_segment_spec (PI := PI) TB.
Proof.
  dl_env. pose proof dl_tcore as TCLS.
  eapply ReacDiscoClassifyOnSegment.pb_reac_disco_classify_on_segment; eassumption.
Qed.

Lemma dl_tchks : tcheck_sighting_spec (PI := PI) TB.
Proof. dl_env. eapply CheckSighting.pb_check_sighting; eassumption. Qed.

Lemma dl_tgpush : treac_disco_gate_should_push_spec (PI := PI) TB.
Proof. dl_env. eapply ReacDiscoGateShouldPush.pb_reac_disco_gate_should_push; eassumption. Qed.

Lemma dl_tfind : tfind_entry_spec (PI := PI) TB.
Proof. dl_env. eapply FindEntry.pb_find_entry; eassumption. Qed.

Lemma dl_ttobs : treac_disco_table_observe_spec (PI := PI) TB.
Proof. dl_env. eapply ReacDiscoTableObserve_W.pb_reac_disco_table_observe; eassumption. Qed.

Lemma dl_thobs : treac_hunt_observe_spec (PI := PI) TB.
Proof.
  dl_env. pose proof dl_tclss as TCOS. pose proof dl_ttobs as TOBS.
  eapply ReacHuntObserveAll.pb_reac_hunt_observe; eassumption.
Qed.

Lemma dl_ttjson : tj_specP (PI := PI) TB TJ_STK 0 dimg_tj.
Proof.
  dl_env. pose proof dl_asnprintf as ASNP.
  pose proof (eq_refl : SIGMA DS___interceptor_trampoline_snprintf = SIGMA DS___interceptor_trampoline_snprintf) as HSNPC.
  pose proof DiscoImgSnp.snp_consts_of_arodata_disco as SNPC. pose proof DiscoImgSnp.tj_snp_cr_disco as SNPCR.
  pose proof DiscoImgSnp.tj_snp_canary_disco as SNPCAN. pose proof DiscoImgSnp.tj_snp_gcgv_disco as SNPGCGV.
  pose proof DiscoImgSnp.tj_snp_img_disco as SNPIMG.
  eapply (TjTop.pb_reac_disco_table_json_gen TB); first [eassumption | apply Z.leb_le; vm_compute; reflexivity].
Qed.

Lemma disco_denv :
  dentry_env (PI := PI) TB ameter_triv XL0 XL0 RLO RHI AE2k.tfib_K StackFree6Tbl.SF6_ENTRY.
Proof.
  exact (mkDEnv _ _ _ _ _ _ _ _
    dl_laws DiscoLaws.disco_PALib DiscoLaws.disco_PALibF dl_ml dl_mtl eq_refl dl_smp DiscoLaws.disco_FFL dl_hro
    dl_hxl dl_hxl DiscoImgFacts.disco_dglob_zshadow DiscoImgFacts.disco_dglob_const dl_dro dl_gm dl_hv
    DiscoDcro.dimg_consts_of_ro_tfib dl_mc_ro dl_mc_un dl_snp_ro dl_snp_un dl_ail dl_kcan DiscoDuniv.de_duniv
    dl_amalloc dl_afree dl_amemcpy dl_amemset dl_abcmp dl_asm6 dl_asfw6 dl_sf6 dl_assf8 dl_ass00 dl_astrlen
    dl_asnprintf dl_ttinit dl_tginit dl_tlinit dl_thinit dl_thpin dl_thsil dl_tage dl_tchkt dl_ttjson dl_tjsc
    dl_tjtok dl_tbox dl_thstep dl_tvname dl_throle dl_thheard dl_tcls dl_tclss dl_tchks dl_tgpush dl_tfind dl_ttobs
    dl_thobs).
Qed.

Lemma dl_libk : forall pl fs K, @LIBK DiscoAsanTop.disco_shape pl fs K = K (LL 0 fs []).
Proof. reflexivity. Qed.

Lemma dl_dpre : forall regs ly S W mem md p n pl M,
  tfib_lib_pre_x (PI := PI) TB ameter_triv XL0 RLO RHI AE2k.tfib_K regs ly S W mem md p n pl M ->
  dpre_extra (PI := PI) W mem.
Proof.
  intros regs ly S W mem md p n pl M (HAFN & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  exact (DiscoDcro.dimg_consts_of_ro_tfib dl_laws disco_ro_hyps ly S W mem md (proj1 HAFN) (dl_hro _ HRO)).
Qed.

Lemma disco_entry_addr : @pa_val _ disco_listing PI A_TEXT + AF_LLVMFuzzerTestOneInput = ACfn.A_LLVMF.
Proof. vm_compute. reflexivity. Qed.

Theorem disco_lib_x_all :
  tLLVMFuzzerTestOneInput_spec (LS := DiscoAsanTop.disco_shape) (PI := PI)
    TB ameter_triv XL0 XL0 RLO RHI AE2k.tfib_K.
Proof.
  exact (DiscoEntTop.d_walk_to_spec (LS := DiscoAsanTop.disco_shape) (PI := PI)
    TB ameter_triv XL0 XL0 RLO RHI AE2k.tfib_K dl_libk dl_dpre
    (DiscoEntWalk.d_entry_walk_ok TB ameter_triv XL0 XL0 RLO RHI AE2k.tfib_K JsonScalarImg.tjson_scalar_roimg_disco
      StackFree6Tbl.SF6_ENTRY disco_denv)).
Qed.

End d.

Theorem disco_lib_x_all_acfn :
  forall rc : YM05.RunCeil,
  DiscoAsanT.H_RO_stmt rc ->
  @ACfn.tfib_lib_contract_x_all rc DiscoAsanTop.disco_shape AD2l.TfibB ameter_triv (fun _ => 0) (fun _ => 0)
    DiscoImg.disco_relro_lo DiscoImg.disco_relro_hi.
Proof.
  intros rc _ fx HF ly S W regs mem md p n pl M K HAI HPRE HK.
  pose proof (@disco_lib_x_all rc fx (proj1 (YFrm0Eq.frm0_iff _) HF) ly S W regs mem md p n pl M K HAI HPRE HK) as H.
  rewrite disco_entry_addr in H. exact H.
Qed.
