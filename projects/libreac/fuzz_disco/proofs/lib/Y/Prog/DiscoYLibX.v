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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YP0l YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YF0m YE2k YCbj YRoBelow.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require
YD2l YB1w YG0q YG05 YG0t YF0w YF0q YF0s YF0u DiscoShape YCfn DiscoYAbcmp DiscoAsanUbsanT.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require DiscoAsanTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import StrlenDef SetShadowDef SnprintfDef AcpySameDef MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import StackFreeDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require FMsnprintfDiscoSnp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require
ReacDiscoTableInit ReacDiscoGateInit ReacDiscoPeerLockInit ReacHuntInit ReacHuntPin ReacHuntSilenceProven
ReacHuntStep ReacHuntVerdictName ReacHuntRole ReacHuntHeardAnything ReacDiscoClassify ReacDiscoClassifyOnSegment
ReacHuntObserve DiscoArm3JsonCallee DiscoArm3JtokSpec ReacBoxName ReacBoxNameTop CheckSighting ReacDiscoTableObserve
ReacDiscoTableJson ReacDiscoTableAge CheckTable ReacDiscoGateShouldPush FindEntry RoleOf JtokIs
ReacArbitrate ReacSenderKind ReacRivalKindOf ReacMasterOnlyCadenceNs ReacRateSnap ReacPortsParse KindOfLink1
SbDec SbDecWalk SbCh ClassifyCore ClassifyCoreSeg ClassifyCoreWalk ClassifyCoreChk ClassifyCoreRom
CtrlParse CtrlParseWalk CtrlParseImg CtrlChecksumVerify
YEntImgCan YEntImgRo YEntImgDglob YDcro DiscoAmem DiscoYLaws DiscoYDuniv JsonScalar DiscoYEntTop DiscoYEntWalk
YEntImgSnp TjSnpInst TjWalk TjSpecLift JsonScalarImgY DiscoArm3Top DiscoYEntSeat DiscoYEntBody DiscoYEntBodyCall.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require
StackMalloc6 StackFree6Tbl StackFree6S SetShadow Strlen AcpySame Memchr StackMalloc3 StackMalloc0.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section x. Context {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PB_tfib).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PB_tfib).
#[local] Notation B := YD2l.TfibB.
#[local] Notation MT := ameter_triv.
#[local] Notation XM := (fun _ : Z => 0).
#[local] Notation RLO := YB1w.tfib_data_rel_ro_lo.
#[local] Notation RHI := YB1w.tfib_got_hi.
#[local] Notation K := YE2k.tfib_K.
#[local] Notation SF6 := Y.Rt.StackFree6Tbl.SF6_ENTRY.
#[local] Notation DENV := (@dentry_env rc tfib_sink_head PB_tfib B MT XM XM RLO RHI K SF6
  (ReacDiscoTableInit.treac_disco_table_init_spec B)
  (ReacDiscoGateInit.treac_disco_gate_init_spec B)
  (ReacDiscoPeerLockInit.treac_disco_peer_lock_init_spec B)
  (ReacHuntInit.treac_hunt_init_spec B)
  (ReacHuntPin.treac_hunt_pin_spec B)
  (ReacHuntSilenceProven.treac_hunt_silence_proven_spec B)
  (ReacHuntStep.treac_hunt_step_spec B)
  (ReacHuntVerdictName.treac_hunt_verdict_name_spec B)
  (ReacHuntRole.treac_hunt_role_spec B)
  (ReacHuntHeardAnything.treac_hunt_heard_anything_spec B)
  (ReacDiscoClassify.treac_disco_classify_spec B)
  (ReacDiscoClassifyOnSegment.treac_disco_classify_on_segment_spec B)
  (ReacHuntObserve.treac_hunt_observe_spec B)
  (DiscoArm3JsonCallee.tjson_scalar_spec B)
  (DiscoArm3JtokSpec.tjtok_is_spec B)
  (ReacBoxName.treac_box_name_spec B)
  (CheckSighting.tcheck_sighting_spec B)
  (ReacDiscoTableObserve.treac_disco_table_observe_spec B)
  (ReacDiscoTableJson.treac_disco_table_json_spec B dimg_tj)).

#[local] Notation TL := DiscoYLaws.tfib_PALib (only parsing).
#[local] Notation TLF := DiscoYLaws.tfib_PALibF (only parsing).
#[local] Notation FFL := DiscoYLaws.tfib_FFL (only parsing).

Lemma tfib_laws : AR_laws SEGS B.
Proof. exact (YG0q.AR_laws_ok _ _). Qed.

Lemma tfib_ml : model_laws (as_universe B).
Proof. exact (YG05.model_laws_ok (as_universe B) (ts_universe B YD2l.TfibB_syms)). Qed.

Lemma tfib_smp : stack_malloc_progressP B.
Proof. exact (YG05.stack_malloc_progress (as_universe B)). Qed.

Lemma tfib_hro : forall rd, arodata_okS SEGS B RLO RHI rd -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rd.
Proof. exact (fun rd H => H). Qed.

Lemma tfib_hx : forall n : Z, ACC_LIB MT <= XM n.
Proof. intros n. cbv beta. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma tfib_amalloc : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS B.
Proof. intros fq. exact (@YF0w.tfib_amalloc_realizes fq rc B YD2l.TfibB_syms (fun t => eq_refl)). Qed.

Lemma tfib_afree : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS B.
Proof. intros fq. exact (@YF0q.afree_realizes_closed fq rc B YD2l.TfibB_syms (fun t => eq_refl)). Qed.

Lemma tfib_amemcpy : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Proof. intros fq. exact (@DiscoAmem.tfibX_AMEMCPY fq rc). Qed.

Lemma tfib_amemset : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Proof. intros fq. exact (@DiscoAmem.tfibX_AMEMSET fq rc). Qed.

Lemma tfib_abcmp : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Proof. exact DiscoYAbcmp.disco_y_abcmp_tfib. Qed.

Lemma tfib_sf6 : SIGMA AS___asan_stack_free_6 = SF6.
Proof. vm_compute. reflexivity. Qed.

Lemma tfib_asm1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Proof. intros fq. exact (@YF0s.stack_malloc1_contract fq rc B tfib_laws YD2l.TfibB_syms). Qed.

Lemma tfib_asm2 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 2.
Proof. intros fq. exact (@YF0u.stack_malloc2_contract fq rc B tfib_laws YD2l.TfibB_syms). Qed.

Lemma tfib_asf : astack_free_law SEGS B.
Proof. exact (YG0t.astack_free_law_ok _ _). Qed.

Lemma tfib_duniv : duniv_ok (PI := PB_tfib) B.
Proof.
exact (DiscoYDuniv.dy_duniv_of_eqs B (YCeh.tl_code B DiscoYLaws.tfib_TfibLib) (YCeh.tl_universe B DiscoYLaws.tfib_TfibLib)).
Qed.

Lemma tfib_asm6 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 6.
Proof. intros fq. exact (Y.Rt.StackMalloc6.disco_stack_malloc6 fq B tfib_laws YD2l.TfibB_syms). Qed.

Lemma tfib_asfw6 : forall fq : YK11.FPState, astack_free_realizes (fx := fq) SEGS B SF6 6.
Proof. intros fq. exact (Y.Rt.StackFree6S.disco_stack_free6_shared fq B tfib_laws YD2l.TfibB_syms). Qed.

Lemma tfib_assf8 : forall fq : YK11.FPState,
  aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_f8) 0xf8.
Proof.
intros fq. assert (E : SIGMA AS___asan_set_shadow_f8 = Y.Rt.SetShadow.SSF8_ENTRY) by (vm_compute; reflexivity).
rewrite E. exact (@Y.Rt.SetShadow.disco_set_shadow_f8 fq rc B tfib_laws YD2l.TfibB_syms).
Qed.

Lemma tfib_ass00 : forall fq : YK11.FPState,
  aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_00) 0.
Proof.
intros fq. assert (E : SIGMA AS___asan_set_shadow_00 = Y.Rt.SetShadow.SS00_ENTRY) by (vm_compute; reflexivity).
rewrite E. exact (@Y.Rt.SetShadow.disco_set_shadow_00 fq rc B tfib_laws YD2l.TfibB_syms).
Qed.

Lemma tfib_assf5 : forall fq : YK11.FPState,
  SetShadowDef.aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_f5) 0xf5.
Proof.
intros fq. assert (E : SIGMA AS___asan_set_shadow_f5 = Y.Rt.SetShadow.SSF5_ENTRY) by (vm_compute; reflexivity).
rewrite E. exact (@Y.Rt.SetShadow.disco_set_shadow_f5 fq rc B tfib_laws YD2l.TfibB_syms).
Qed.

Lemma tfib_astrlen : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Proof.
intros fq. assert (E : SIGMA AS___interceptor_trampoline_strlen = YB1w.tfib_A___wrap_strlen) by (vm_compute; reflexivity).
rewrite E. exact (@Y.Rt.Strlen.strlen_icpt_realizesM fq rc B tfib_laws YD2l.TfibB_syms).
Qed.

Lemma tfib_amemchr : forall fq : YK11.FPState,
  amemchr_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_memchr).
Proof.
intros fq. assert (E : SIGMA AS___interceptor_trampoline_memchr = Y.Rt.Memchr.MCH_ENTRY) by (vm_compute; reflexivity).
rewrite E. exact (@Y.Rt.Memchr.memchr_icpt_realizesM fq rc B tfib_laws YD2l.TfibB_syms).
Qed.

Lemma tfib_amemcpyeq : forall fq : YK11.FPState, acpy_same_realizes (fx := fq) SEGS B (SIGMA AS___asan_memcpy).
Proof.
intros fq. assert (E : SIGMA AS___asan_memcpy = YB1w.tfib_A___asan_memcpy) by (vm_compute; reflexivity).
rewrite E. exact (@Y.Rt.AcpySame.acpy_same_icpt fq rc B tfib_laws YD2l.TfibB_syms).
Qed.

Lemma tfib_asm3 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 3.
Proof. intros fq. exact (@Y.Rt.StackMalloc3.stack_malloc3_contract fq rc B tfib_laws YD2l.TfibB_syms). Qed.

Lemma tfib_asm0 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 0.
Proof. intros fq. exact (@Y.Rt.StackMalloc0.stack_malloc0_contract fq rc B tfib_laws YD2l.TfibB_syms). Qed.

Lemma tfib_mc_rom : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_rom SEGS a.
Proof.
intros a Ha. apply snp_cr_in_rom. apply Exists_exists. exists (0x10368, 32). split.
- unfold snp_cr. cbn [In]. repeat (first [left; reflexivity | right]).
- unfold in_zr, MC_CONSTS_LO, MC_CONSTS_HI in *. cbn [fst snd]. lia.
Qed.

Lemma tfib_mc_img : forall a, ReacBoxName.MC_CONSTS_LO <= a < ReacBoxName.MC_CONSTS_HI -> in_img SEGS a.
Proof.
intros a Ha. destruct (tfib_mc_rom a Ha) as (sg & Hs & _ & Hr). exists sg. split; [exact Hs | exact Hr].
Qed.

Lemma tfib_tjsc : DiscoArm3JsonCallee.tjson_scalar_spec B.
Proof.
exact (JsonScalar.pb_json_scalar B tfib_laws TL tfib_abcmp MC_CONSTS_LO MC_CONSTS_HI tfib_astrlen tfib_amemchr tfib_mc_rom
  (proj1 (proj2 YEntImgRo.tfib_d_ro_hyps)) (proj2 (proj2 YEntImgRo.tfib_d_ro_hyps)) (proj1 YEntImgRo.tfib_d_ro_hyps)).
Qed.

Lemma tfib_ttinit : ReacDiscoTableInit.treac_disco_table_init_spec B.
Proof. exact (ReacDiscoTableInit.pb_reac_disco_table_init B tfib_laws tfib_amemset). Qed.

Lemma tfib_tginit : ReacDiscoGateInit.treac_disco_gate_init_spec B.
Proof. exact (ReacDiscoGateInit.pb_reac_disco_gate_init B tfib_laws tfib_amemset). Qed.

Lemma tfib_tlinit : ReacDiscoPeerLockInit.treac_disco_peer_lock_init_spec B.
Proof. exact (ReacDiscoPeerLockInit.pb_reac_disco_peer_lock_init B tfib_laws tfib_amemset). Qed.

Lemma tfib_thinit : ReacHuntInit.treac_hunt_init_spec B.
Proof. exact (ReacHuntInit.pb_reac_hunt_init B tfib_laws TL tfib_amemset tfib_amemcpy tfib_ttinit tfib_tlinit). Qed.

Lemma tfib_thpin : ReacHuntPin.treac_hunt_pin_spec B.
Proof. exact (ReacHuntPin.pb_reac_hunt_pin B tfib_laws TL). Qed.

Lemma tfib_thsil : ReacHuntSilenceProven.treac_hunt_silence_proven_spec B.
Proof. exact (ReacHuntSilenceProven.pb_reac_hunt_silence_proven B tfib_laws TL). Qed.

Lemma tfib_tage : ReacDiscoTableAge.treac_disco_table_age_spec B.
Proof. exact (ReacDiscoTableAge.pb_reac_disco_table_age B tfib_laws TL tfib_amemcpy tfib_amemcpyeq). Qed.

Lemma tfib_tchkt : CheckTable.tcheck_table_spec B.
Proof. exact (CheckTable.pb_check_table B tfib_laws TL tfib_abcmp). Qed.

Lemma tfib_tjtok : DiscoArm3JtokSpec.tjtok_is_spec B.
Proof. exact (JtokIs.pb_jtok_is B tfib_laws TL tfib_abcmp MC_CONSTS_LO MC_CONSTS_HI tfib_astrlen tfib_mc_rom). Qed.

Lemma tfib_tsbch : SbCh.tsb_ch_spec B.
Proof. exact (SbCh.pb_sb_ch B tfib_laws TL). Qed.

Lemma tfib_tsbdec : SbDec.tsb_dec_spec B.
Proof. exact (SbDecWalk.pb_sb_dec B tfib_laws TL tfib_ml tfib_asm0 TLF tfib_smp tfib_asf FFL tfib_tsbch). Qed.

Lemma tfib_tbox : ReacBoxName.treac_box_name_spec B.
Proof.
exact (ReacBoxNameTop.pb_reac_box_name B tfib_laws TL tfib_ml tfib_amemset tfib_amemcpy tfib_abcmp tfib_astrlen
  YEntImgRo.tfib_de_mc_un tfib_mc_img tfib_assf5 tfib_asm3 TLF tfib_smp tfib_asf FFL tfib_tsbdec tfib_tsbch
  (proj1 YEntImgRo.tfib_d_ro_hyps) (proj1 (proj2 YEntImgRo.tfib_d_ro_hyps)) (proj2 (proj2 YEntImgRo.tfib_d_ro_hyps))).
Qed.

Lemma tfib_trival : ReacRivalKindOf.treac_rival_kind_of_spec B.
Proof. exact (ReacRivalKindOf.pb_reac_rival_kind_of B tfib_laws TL). Qed.

Lemma tfib_trate : ReacRateSnap.treac_rate_snap_spec B.
Proof. exact (ReacRateSnap.pb_reac_rate_snap B tfib_laws). Qed.

Lemma tfib_tmoc : ReacMasterOnlyCadenceNs.treac_master_only_cadence_ns_spec B.
Proof. exact (ReacMasterOnlyCadenceNs.pb_reac_master_only_cadence_ns B tfib_laws TL tfib_trate). Qed.

Lemma tfib_tsender : ReacSenderKind.treac_sender_kind_spec B.
Proof. exact (ReacSenderKind.pb_reac_sender_kind B tfib_laws TL tfib_tmoc tfib_trival). Qed.

Lemma tfib_tarb : ReacArbitrate.treac_arbitrate_spec B.
Proof. exact (ReacArbitrate.pb_reac_arbitrate B tfib_laws TL tfib_amemset tfib_amemcpy tfib_abcmp tfib_trival). Qed.

Lemma tfib_thstep : ReacHuntStep.treac_hunt_step_spec B.
Proof. exact (ReacHuntStep.pb_reac_hunt_step B tfib_laws TL tfib_abcmp tfib_tage tfib_tarb tfib_tsender). Qed.

Lemma tfib_tvname : ReacHuntVerdictName.treac_hunt_verdict_name_spec B.
Proof. exact (ReacHuntVerdictName.pb_reac_hunt_verdict_name B tfib_laws TL). Qed.

Lemma tfib_throle : ReacHuntRole.treac_hunt_role_spec B.
Proof. exact (ReacHuntRole.pb_reac_hunt_role B tfib_laws TL). Qed.

Lemma tfib_thheard : ReacHuntHeardAnything.treac_hunt_heard_anything_spec B.
Proof. exact (ReacHuntHeardAnything.pb_reac_hunt_heard_anything B tfib_laws TL). Qed.

Lemma tfib_tparse : ClassifyCoreSeg.tparse_need B.
Proof.
exact (CtrlParseWalk.pb_reac_ctrl_parse B tfib_laws TL TLF tfib_ml tfib_amemset tfib_amemcpy tfib_abcmp tfib_asm1
  tfib_smp tfib_asf FFL (KindOfLink1.pb_kind_of_link1 B tfib_laws) tfib_globs
  (proj1 (proj2 YEntImgRo.tfib_d_ro_hyps)) CtrlParseImg.cp_HG15_tfib (proj2 (proj2 YEntImgRo.tfib_d_ro_hyps))
  CtrlParseImg.cp_HBC_RNG_tfib (CtrlParseImg.cp_HBC_VAL_tfib B (proj1 YEntImgRo.tfib_d_ro_hyps))).
Qed.

Lemma tfib_tchk : ClassifyCoreSeg.tchk_need B.
Proof.
exact (ClassifyCoreChk.tchk_need_of_spec B tfib_laws (CtrlChecksumVerify.pb_reac_ctrl_checksum_verify B tfib_laws TL)).
Qed.

Lemma tfib_tcore : ClassifyCore.tclassify_core_spec B.
Proof.
exact (ClassifyCoreWalk.pb_classify_core_of_needs B tfib_laws tfib_ml TL TLF tfib_abcmp tfib_amemcpy tfib_amemset
  tfib_asm2 tfib_smp tfib_asf FFL (ReacPortsParse.pb_reac_ports_parse B tfib_laws TL)
  (ClassifyCoreRom.cls_rom_tfib B (proj1 YEntImgRo.tfib_d_ro_hyps)) tfib_tparse tfib_tchk).
Qed.

Lemma tfib_tcls : ReacDiscoClassify.treac_disco_classify_spec B.
Proof. exact (ReacDiscoClassify.pb_reac_disco_classify B tfib_laws tfib_tcore). Qed.

Lemma tfib_tclss : ReacDiscoClassifyOnSegment.treac_disco_classify_on_segment_spec B.
Proof. exact (ReacDiscoClassifyOnSegment.pb_reac_disco_classify_on_segment B tfib_laws tfib_tcore). Qed.

Lemma tfib_tchks : CheckSighting.tcheck_sighting_spec B.
Proof. exact (CheckSighting.pb_check_sighting B tfib_laws TL tfib_abcmp). Qed.

Lemma tfib_tgpush : ReacDiscoGateShouldPush.treac_disco_gate_should_push_spec B.
Proof. exact (ReacDiscoGateShouldPush.pb_reac_disco_gate_should_push B tfib_laws TL tfib_amemcpy tfib_abcmp). Qed.

Lemma tfib_tfind : FindEntry.tfind_entry_spec B.
Proof. exact (FindEntry.pb_find_entry B tfib_laws TL tfib_abcmp). Qed.

Lemma tfib_trole : RoleOf.trole_of_spec B.
Proof. exact (RoleOf.pb_role_of B tfib_laws TL tfib_tfind). Qed.

Lemma tfib_ttobs : ReacDiscoTableObserve.treac_disco_table_observe_spec B.
Proof. exact (ReacDiscoTableObserve.pb_reac_disco_table_observe B tfib_laws TL tfib_amemcpy tfib_amemset tfib_abcmp). Qed.

Lemma tfib_ttjs : ReacDiscoTableJson.treac_disco_table_json_spec (SK := tfib_sink_head) (PI := PB_tfib) B dimg_tj.
Proof.
eapply TjWalk.reac_disco_table_json_ok; first
  [ exact eq_refl | exact FMsnprintfDiscoSnp.disco_snprintf_R | exact TL | exact tfib_laws | exact TLF | exact tfib_ml
  | exact tfib_asm2 | exact tfib_smp
  | exact FFL | exact tfib_asf | exact TjSnpInst.tj_snp_consts_tfib | exact YEntImgSnp.tj_snp_cr_tfib
  | exact YEntImgSnp.tj_snp_canary_tfib | exact YEntImgSnp.tj_snp_gcgv_tfib | exact YEntImgSnp.tj_snp_img_tfib
  | exact (proj1 YEntImgRo.tfib_d_ro_hyps) | exact (proj1 (proj2 YEntImgRo.tfib_d_ro_hyps))
  | exact (proj2 (proj2 YEntImgRo.tfib_d_ro_hyps)) | exact tfib_amemset | exact tfib_amemcpy | exact tfib_abcmp
  | exact tfib_astrlen | exact tfib_assf5 | exact tfib_asm3 | exact tfib_asm0 ].
Qed.

Lemma tfib_thobs : ReacHuntObserve.treac_hunt_observe_spec (SK := tfib_sink_head) (PI := PB_tfib) B.
Proof.
eapply ReacHuntObserve.pb_reac_hunt_observe; first
  [ exact tfib_laws | exact TL | exact TLF | exact tfib_ml | exact tfib_amemcpy | exact tfib_abcmp | exact tfib_asm1
  | exact tfib_smp | exact tfib_asf | exact FFL | exact tfib_tclss | exact tfib_ttobs
  | exact (proj1 YEntImgRo.tfib_d_ro_hyps) ].
Qed.

Lemma tfib_ttjpf : TjSpecLift.tj_specPF (SK := tfib_sink_head) (PI := PB_tfib) B TJ_STK 0 dimg_tj.
Proof.
eapply TjSpecLift.tj_specPF_of_spec; first
  [ exact tfib_laws | exact TL | exact tfib_ttjs | apply Z.leb_le; vm_compute; reflexivity ].
Qed.

Lemma tfib_arm3 : arm3_spec (SK := tfib_sink_head) (PI := PB_tfib) B MT XM RLO RHI K.
Proof.
eapply DiscoArm3Top.arm3_proved; first
  [ exact tfib_laws | exact TL | exact TLF | exact FFL | exact eq_refl | exact tfib_ml | exact tfib_smp | exact tfib_asf
  | exact tfib_duniv | exact (proj1 YEntImgRo.tfib_d_ro_hyps) | exact (proj1 (proj2 YEntImgRo.tfib_d_ro_hyps))
  | exact (proj2 (proj2 YEntImgRo.tfib_d_ro_hyps)) | exact YDcro.dimg_consts_of_ro_tfib | exact YEntImgCan.de_ail_tfib
  | exact YEntImgCan.de_kcan_tfib | exact YEntImgRo.tfib_de_mc_ro | exact YEntImgRo.tfib_de_mc_un
  | exact YEntImgRo.tfib_de_snp_ro | exact YEntImgRo.tfib_de_snp_un
  | exact (DiscoYEntSeat.d_seat B MT XM RLO RHI K) | exact (DiscoYEntSeat.d_facts_ok B MT XM RLO RHI K)
  | exact (DiscoYEntSeat.d_land B MT XM RLO RHI K) | exact (DiscoYEntBody.d_body_keep B)
  | exact (DiscoYEntBody.d_body_rt B) | exact (DiscoYEntBody.d_body_call_keep B MT XM RLO RHI K)
  | exact (DiscoYEntBody.d_body_tobs B MT XM RLO RHI K)
  | exact (DiscoYEntBodyCall.d_body_pcall B MT XM RLO RHI K (DiscoYEntBody.d_body_step B MT XM RLO RHI K))
  | exact (DiscoYEntBodyCall.d_body_malloc B MT XM RLO RHI K (DiscoYEntBody.d_body_step B MT XM RLO RHI K))
  | exact (DiscoYEntBodyCall.d_body_free B MT XM RLO RHI K (DiscoYEntBody.d_body_step B MT XM RLO RHI K))
  | exact tfib_amalloc | exact tfib_afree | exact tfib_asm3 | exact tfib_asm0 | exact tfib_amemcpy
  | exact tfib_amemcpyeq | exact tfib_amemset | exact tfib_assf8 | exact tfib_assf5 | exact tfib_ass00
  | exact tfib_abcmp | exact tfib_astrlen | exact FMsnprintfDiscoSnp.disco_snprintf_R | exact tfib_tage
  | exact tfib_tchkt | exact tfib_ttjpf
  | exact JsonScalarImgY.tjson_scalar_roimg_tfib | exact tfib_tjsc | exact tfib_tjtok ].
Qed.

Lemma tfib_denv : DENV.
Proof.
exact (mkDEnv B MT XM XM RLO RHI K SF6
  tfib_laws TL TLF tfib_ml ameter_triv_laws eq_refl tfib_smp FFL tfib_hro tfib_hx tfib_hx
  YEntImgDglob.tfib_dglob_zshadow YEntImgDglob.tfib_dglob_const
  (proj1 YEntImgRo.tfib_d_ro_hyps) (proj1 (proj2 YEntImgRo.tfib_d_ro_hyps)) (proj2 (proj2 YEntImgRo.tfib_d_ro_hyps))
  YEntImgRo.tfib_de_mc_ro YEntImgRo.tfib_de_mc_un YEntImgRo.tfib_de_snp_ro YEntImgRo.tfib_de_snp_un
  YEntImgCan.de_ail_tfib YEntImgCan.de_kcan_tfib tfib_duniv
  tfib_amalloc tfib_afree tfib_amemcpy tfib_amemset tfib_abcmp tfib_asm6 tfib_asfw6 tfib_sf6 tfib_assf8 tfib_ass00
  tfib_astrlen FMsnprintfDiscoSnp.disco_snprintf_R
  tfib_ttinit tfib_tginit tfib_tlinit tfib_thinit tfib_thpin tfib_thsil tfib_tage tfib_tchkt tfib_ttjs tfib_tjsc tfib_tjtok
  tfib_tbox tfib_thstep tfib_tvname tfib_throle tfib_thheard tfib_tcls tfib_tclss tfib_tchks tfib_tgpush
  tfib_tfind tfib_trole tfib_ttobs tfib_thobs).
Qed.

Lemma tfib_libk : forall pl fs (K' : lleaf -> TSet), @LIBK DiscoShape.disco_lib_shape pl fs K' = K' (LL 0 fs []).
Proof. intros pl fs K'. reflexivity. Qed.

Lemma tfib_dpre : forall regs ly S W mem md p n pl M,
  tfib_lib_pre_x (PI := PB_tfib) B MT XM RLO RHI K regs ly S W mem md p n pl M ->
  dpre_extra W mem.
Proof.
intros regs ly S W mem md p n pl M HPRE.
destruct HPRE as ((HAR & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
exact (YDcro.dimg_consts_of_ro_tfib tfib_laws YEntImgRo.tfib_d_ro_hyps ly S W mem md HAR (tfib_hro _ HRO)).
Qed.

Lemma tfib_entry_addr : @pa_val _ lib_both3_0_listing PB_tfib A_TEXT + AF_both3_LLVMFuzzerTestOneInput = YCfn.A_LLVMF.
Proof. vm_compute. reflexivity. Qed.

Theorem tfib_lib_x_all :
  @tLLVMFuzzerTestOneInput_spec rc tfib_sink_head DiscoShape.disco_lib_shape PB_tfib B MT XM XM RLO RHI K.
Proof.
exact (DiscoYEntTop.d_walk_to_spec (LS := DiscoShape.disco_lib_shape) B MT XM XM RLO RHI K tfib_libk tfib_dpre
  (DiscoYEntWalk.d_entry_walk_ok B MT XM XM RLO RHI K YDcro.dimg_consts_of_ro_tfib (fun _ _ => tfib_arm3) SF6
    tfib_denv)).
Qed.

End x.

Theorem tfib_lib_x_all_ycfn :
  forall rc : YM05.RunCeil,
  DiscoAsanUbsanT.H_RO_stmt rc ->
  @YCfn.tfib_lib_contract_x_all rc DiscoAsanTop.disco_shape YD2l.TfibB ameter_triv (fun _ => 0) (fun _ => 0)
    YB1w.tfib_data_rel_ro_lo YB1w.tfib_got_hi.
Proof.
intros rc _ fx HF ly S W regs mem md p n pl M K HAI HPRE HK.
rewrite <- tfib_entry_addr.
apply (@tfib_lib_x_all rc fx HF ly S W regs mem md p n pl M K HAI HPRE).
intros l W' c' Hle HAI' (fq' & ly' & S' & regs' & mem' & md' & k & Hc & HF' & Hpost).
apply (HK l W' c' Hle HAI').
exists fq', ly', S', regs', mem', md', k.
split; [exact Hc|]. split; [exact HF' | exact Hpost].
Qed.
