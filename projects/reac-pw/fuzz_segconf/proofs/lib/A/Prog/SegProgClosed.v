(* reac-pw/fuzz_segconf, image A: the program side, composed at the pinned image (the role of plugin-hostd/fuzz_command's
   lib/A/Prog/CmdProgClosed.v, origin/ossv/recipes 501c0d516c69): the contract `<F>_contract` (lib/A/Prog/<F>_c.v,
   contracts FINAL 6f783602b5e3) of each of the 34 program functions at image A's instance SegImg.PB_seg (segments
   tfibsegs), the sink head AE2k.tfib_sink_head and the allocator record AD2l.SegB, at every run ceiling and FP state,
   from each function's walk closure (its group's theorem, applied to its callees' closures and to the runtime rows).
   The walks state entries and call targets as listing terms under `Context {PI : PAImg seg_listing}` (the image-A owner's
   ruling): here PI := PB_seg, and the top is rewritten to SegInstA's A_LLVMFuzzerTestOneInput_A by
   SegInstPB.pb_entry_LLVMFuzzerTestOneInput.
   SKELETON, instantiated group by group as the walks land (INSTANTIATE.md section E; a walk is counted only when FINAL
   6f783602b5e3 is an ancestor of its sha and it built rc=0 on that tree):
   - instantiated: the G1 harness walk (pb_LLVMFuzzerTestOneInput, bd12cd505428), in
     lib/A/Prog/SegG1.v at PB_seg and taken here at SegB, whose callees are the closures below; the four closed walks
     of the G3 walks (trim_walk, cross_check_walk, reac_segconf_parse_walk,
     reac_segconf_parse_file_walk; G3's integration head 84490aabe1bd, FINAL an ancestor), composed in
     lib/A/Prog/SegG3.v at PB_seg with every record hypothesis discharged by the listing's lemmas and taken here at
     SegB; the six landed walks of G2 (the G2 walks)
     and the 20 counted walks of G4 + G5 (the G4 / G5 walks), composed in lib/A/Prog/SegG2.v and lib/A/Prog/SegG45.v at
     the walks' abstract instance and taken here at PB_seg / SegB, with their record facts discharged by the
     listing's and the core's lemmas;
   - still Section hypotheses, each of exactly its contract at these terms: the closures of the functions whose
     walks have not landed (only those the instantiated walks and the top consume are stated so far) and the
     runtime rows the walks take (the interceptor layer's closings, the core's intrinsic and side-stack closings).
   Builds after the core's commit 7 (AD2l; SegImg needs AB1v; the walks need the listing's stage 2).
   proves no function (kind: merge; the composition of the walk closures). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI00 YI04 YI09 YN3v
  YM05 YI16 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AE2k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AD2l SegInstPB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString RtStack RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegImg SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegRecRest SegRecRo SegRecCells SegRecImg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require LLVMFuzzerTestOneInput_c trim_c reac_segconf_parse_c
  reac_segconf_parse_file_c cross_check_c refuse_c
  reac_segconf_find_c reac_segconf_init_c reac_segconf_role_file_c reac_segconf_role_c reac_segconf_ignore_file_c reac_segconf_ignored_c reac_segconf_model_c check_absent_c check_segments_c check_role_c check_model_c check_ignore_c check_provenance_c check_refusals_c check_address_c check_knock_refused_c check_declared_c name_ok_c reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegG1 SegG3 SegG45 SegG2 reac_segconf_declared_d m_fileA m_file_memchr refuse_a.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSegCalloc RtPFSeg RtPFCmd RtAPI SegRtPC SegRtClosed
  RtSM0 RtSM1 RtSM3 RtSM5 RtSF5 RtShadowProof RtLAsanMemset RtLAsanMemcpy RtLCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AE2s AF0q AF0w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require fuzz_catalogue_row_c reac_box_catalogue_c
  reac_box_catalogue_by_token_c ieq_c m_find_c m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
Import ListNotations.
Local Open Scope Z_scope.

Section closed. Context {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Notation BASE := (@pa_val _ seg_listing PB_seg A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PB_seg s).

(* ---- the runtime rows the instantiated walks take (INSTANTIATE.md, the R- rows) ---------------------------- *)
(* Each row is the walks' text at the listing's call target SIG SS_<x> = pa_sigma of PB_seg. Where a closing has
   landed it discharges the row at B := SegB, HB := AD2l.SegB_syms (AR_laws from YG0q.AR_laws_ok): the listing's target
   and SegInstA's gotwA / guardA are the closing's pc and RtAPI's stack-protector cells, each by computation (pc_eq).
   - the interceptor layer's lib/A/Rt/SegRtClosed.v (rows 1-12, 14, 16, 17, 20; row 4 in all three forms);
   - the core's closures: RtSM1 / RtSM3 / RtSM5 (side stack classes 1 / 3 / 5), RtShadowProof (set_shadow 00 / f5 /
     f8), RtLAsanMemset / RtLAsanMemcpy (the checked intrinsics), AE2s (bcmp).
   Still hypotheses: stack_free 5 (the core's RtSF5, commit 8), malloc / free at the trivial meter (AF0w / AF0q,
   commit 8), calloc at window 18576 (the interceptor layer's row 13). *)
Local Ltac pc_eq := vm_compute; reflexivity.
Lemma r_strlen : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strlen).
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strlen) with RtAPI.PC_strlen by pc_eq.
exact (SegRtClosed.seg_strlen_closed AD2l.SegB AD2l.SegB_syms).
Qed.
(* the stack-protector cells at every allocator state of SegB: the G3 walks' SSPX and the G4 / G5 walks' dc_sspP, both from the listing's
   SegRecCells.seg_ssp at SegB (route A, the image-A owner's ruling) *)
Lemma sspx : forall ly S (W : world tfibsegs) mem md, AR tfibsegs AD2l.SegB ly S W mem md ->
  sa_ssp (aview tfibsegs (w_H W) mem) gotwA guardA.
Proof.
intros ly S W mem md HAR. eapply SegRecCells.seg_ssp;
  [exact (YG0q.AR_laws_ok _ _) | exact AD2l.SegB_syms | exact (SegRecImg.seg_img_facts_tfib _ AD2l.SegB_syms) | exact HAR].
Qed.
Lemma r_strcmp : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strcmp).
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strcmp) with RtAPI.PC_strcmp by pc_eq.
exact (SegRtClosed.seg_strcmp_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_strncmp : forall fx0 : YK11.FPState,
  @RtString.astrncmp_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strncmp).
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strncmp) with RtAPI.PC_strncmp by pc_eq.
exact (SegRtClosed.seg_strncmp_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_strstr : forall fx0 : YK11.FPState,
  @RtSeg.astrstr_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strstr) gotwA guardA.
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strstr) with SegRtPC.PC_strstr by pc_eq.
replace gotwA with RtAPI.A_SSP_GOT by pc_eq. replace guardA with RtAPI.A_SSP_GUARD by pc_eq.
exact (SegRtClosed.seg_strstr_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_isalnum : forall fx0 : YK11.FPState, @RtSeg.aisalnum_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS_isalnum).
Proof.
intros fx0. replace (SIG SS_isalnum) with SegRtPC.PC_isalnum by pc_eq.
exact (SegRtClosed.seg_isalnum_closed AD2l.SegB).
Qed.
Lemma r_strncpy : forall fx0 : YK11.FPState,
  @RtSeg.astrncpy_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strncpy).
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strncpy) with SegRtPC.PC_strncpy by pc_eq.
exact (SegRtClosed.seg_strncpy_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_strrchr : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strrchr).
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strrchr) with SegRtPC.PC_strrchr by pc_eq.
exact (SegRtClosed.seg_strrchr_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_strtol0 : forall fx0 : YK11.FPState,
  @RtSeg.astrtol0_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strtol) gotwA guardA.
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strtol) with RtAPI.PC_strtol by pc_eq.
replace gotwA with RtAPI.A_SSP_GOT by pc_eq. replace guardA with RtAPI.A_SSP_GUARD by pc_eq.
exact (SegRtClosed.seg_strtol0_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_memset : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc tfibsegs AD2l.SegB OSet (SIG SS___asan_memset).
Proof.
intros fx0. replace (SIG SS___asan_memset) with (pc_asan_memset (as_code AD2l.SegB))
  by (rewrite (ts_code AD2l.SegB AD2l.SegB_syms); pc_eq).
exact (RtLAsanMemset.cmd_asan_memset AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms).
Qed.
Lemma r_memcpy : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc tfibsegs AD2l.SegB OCpy (SIG SS___asan_memcpy).
Proof.
intros fx0. replace (SIG SS___asan_memcpy) with (pc_asan_memcpy (as_code AD2l.SegB))
  by (rewrite (ts_code AD2l.SegB AD2l.SegB_syms); pc_eq).
exact (RtLAsanMemcpy.cmd_asan_memcpy AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms).
Qed.
Lemma r_sm1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc tfibsegs AD2l.SegB 1.
Proof. intros fx0. exact (RtSM1.cmd_stack_malloc1_contract AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms). Qed.
Lemma r_bcmp : forall fx0 : YK11.FPState,
  @abcmp_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_bcmp).
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_bcmp) with 0x43a38 by pc_eq.
exact (AE2s.bcmp_icpt_contract AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms).
Qed.
(* row 4 in G2's form (RtFormat.asnprintf_realizes) *)
Lemma r_snprintf : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_snprintf) with RtAPI.PC_snprintf by pc_eq.
replace gotwA with RtAPI.A_SSP_GOT by pc_eq. replace guardA with RtAPI.A_SSP_GUARD by pc_eq.
exact (SegRtClosed.seg_rtformat_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_strchr : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strchr).
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strchr) with SegRtPC.PC_strchr by pc_eq.
exact (SegRtClosed.seg_strchr_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_strncasecmp : forall fx0 : YK11.FPState,
  @RtSeg.astrncasecmp_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strncasecmp).
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strncasecmp) with SegRtPC.PC_strncasecmp by pc_eq.
exact (SegRtClosed.seg_strncasecmp_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_strcasecmp : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strcasecmp).
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strcasecmp) with SegRtPC.PC_strcasecmp by pc_eq.
exact (SegRtClosed.seg_strcasecmp_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_strspn : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___interceptor_trampoline_strspn) gotwA guardA.
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_strspn) with RtAPI.PC_strspn by pc_eq.
replace gotwA with RtAPI.A_SSP_GOT by pc_eq. replace guardA with RtAPI.A_SSP_GUARD by pc_eq.
exact (SegRtClosed.seg_strspn_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_set_shadow_f8 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___asan_set_shadow_f8) 0xf8.
Proof.
intros fx0. replace (SIG SS___asan_set_shadow_f8) with RtShadowProof.SSF8_ENTRY by pc_eq.
exact (RtShadowProof.cmd_set_shadow_f8 AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms).
Qed.
Lemma r_set_shadow_00 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___asan_set_shadow_00) 0.
Proof.
intros fx0. replace (SIG SS___asan_set_shadow_00) with RtShadowProof.SS00_ENTRY by pc_eq.
exact (RtShadowProof.cmd_set_shadow_00 AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms).
Qed.
Lemma r_sm5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc tfibsegs AD2l.SegB 5.
Proof. intros fx0. exact (RtSM5.cmd_stack_malloc5_contract AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms). Qed.
(* stack_free 5: the core's RtSF5.cmd_stack_free5_contract (commit 8), at its entry 0x3ec38 = the listing's
   __asan_stack_free_5 target by computation *)
Lemma r_sf5 : forall fx0 : YK11.FPState,
  @RtStack.astack_free_cls_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___asan_stack_free_5) 5.
Proof.
intros fx0. replace (SIG SS___asan_stack_free_5) with 0x3ec38 by pc_eq.
exact (RtSF5.cmd_stack_free5_contract AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms).
Qed.
(* the rows the harness walk (G1, lib/A/Prog/SegG1.v) takes besides those above *)
Lemma r_sm3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc tfibsegs AD2l.SegB 3.
Proof. intros fx0. exact (RtSM3.cmd_stack_malloc3_contract AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms). Qed.
Lemma r_shf5 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc tfibsegs AD2l.SegB (SIG SS___asan_set_shadow_f5) 0xf5.
Proof.
intros fx0. replace (SIG SS___asan_set_shadow_f5) with RtShadowProof.SSF5_ENTRY by pc_eq.
exact (RtShadowProof.cmd_set_shadow_f5 AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms).
Qed.
(* malloc and free at the trivial meter: YCbp.amalloc04_rule_triv (with the image's low-segment fact SegImg.seg_segs_low)
   over AF0w.tfib_amalloc_realizes (core commit 9) and
   YCbp.afree04_rule_triv over AF0q.afree_realizes_closed, both at SegB, whose hash premise holds at SegB by eq_refl
   (nothing derived from SegBSyms) *)
(* the kit's malloc / free rules take the image's low-segment fact, the errno cell's place (api_env), the allocator
   laws and the model laws: SegImg.seg_segs_low, RtLCalloc.seg_calloc_env, YG0q.AR_laws_ok, SegRecRest.seg_model_laws *)
Local Ltac mem_premise :=
  try first [ exact SegImg.seg_segs_low | exact (RtLCalloc.seg_calloc_env AD2l.SegB AD2l.SegB_syms)
            | exact (YG0q.AR_laws_ok _ _) | exact (SegRecRest.seg_model_laws AD2l.SegB AD2l.SegB_syms) ].
Lemma r_malloc4 : forall fx0 : YK11.FPState,
  @amalloc04_rule fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB ameter_triv.
Proof.
intros fx0. apply YCbp.amalloc04_rule_triv; mem_premise.
exact (AF0w.tfib_amalloc_realizes AD2l.SegB AD2l.SegB_syms (fun t => eq_refl)).
Qed.
Lemma r_free4 : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) tfibsegs AD2l.SegB ameter_triv.
Proof.
intros fx0. apply YCbp.afree04_rule_triv; mem_premise.
exact (AF0q.afree_realizes_closed AD2l.SegB AD2l.SegB_syms (fun t => eq_refl)).
Qed.
Lemma r_memchr : forall fx0 : YK11.FPState,
  MemchrDef.amemchr_realizesM (fx := fx0) tfibsegs AD2l.SegB memchr_loA memchr_hiA
    (SIG SS___interceptor_trampoline_memchr).
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_memchr) with RtAPI.PC_memchr by pc_eq.
replace memchr_loA with SegRtClosed.memchr_lo by pc_eq. replace memchr_hiA with SegRtClosed.memchr_hi by pc_eq.
exact (SegRtClosed.seg_memchr_closed AD2l.SegB AD2l.SegB_syms).
Qed.
(* calloc at its stack window 18576: the interceptor layer's row 13 in its SegB form (RtLCalloc.seg_acalloc_closed_segB,
   at AD2l.SegB with no premise: its hash equality holds there by eq_refl); the listing's target is the closing's
   PC_calloc and 18576 its SEG_CALLOC_CSTK, each by computation *)
Lemma r_calloc4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB ameter_triv
    (SIG SS___interceptor_trampoline_calloc) 18576.
Proof.
intros fx0. pose proof (RtLCalloc.seg_acalloc_closed_segB rc fx0) as H.
match type of H with @RtSegCalloc.aseg_calloc04_rule _ _ _ _ _ _ ?pc ?cs =>
  replace (SIG SS___interceptor_trampoline_calloc) with pc by pc_eq; replace 18576 with cs by pc_eq end.
exact H.
Qed.
(* row 4 in G1's form (RtPFSeg.seg_asnprintf_realizes) at the image [CMD_IMG_LO, CMD_IMG_HI) = [0x10000, kImgEnd) and
   the image's read-only ranges CMD_SNP_CR *)
Lemma r_snprintf_seg : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc tfibsegs AD2l.SegB 0x10000 kImgEnd RtPFCmd.CMD_SNP_CR
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_snprintf) with RtAPI.PC_snprintf by pc_eq.
replace gotwA with RtAPI.A_SSP_GOT by pc_eq. replace guardA with RtAPI.A_SSP_GUARD by pc_eq.
replace 0x10000 with RtPFCmd.CMD_IMG_LO by pc_eq. replace kImgEnd with RtPFCmd.CMD_IMG_HI by pc_eq.
exact (SegRtClosed.seg_snprintf_closed AD2l.SegB AD2l.SegB_syms).
Qed.
Lemma r_snp_cr : Forall (fun r => 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kImgEnd) RtPFCmd.CMD_SNP_CR.
Proof.
assert (Hb : forallb (fun r => (0x10000 <=? fst r) && (0 <=? snd r) && (fst r + snd r <=? kImgEnd))
  RtPFCmd.CMD_SNP_CR = true) by pc_eq.
apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
(* the two rows only the refuse walk takes (the G3 walks' statement, 01:5xZ): the side stack class 0 (the core's RtSM0) and
   vsnprintf in row 5's RtPFSeg form at CMD_IMG_LO / CMD_IMG_HI / CMD_SNP_CR (SegRtClosed.seg_vsnprintf_closed; the
   listing's vsnprintf target is SegRtPC.PC_vsnprintf = 0x43a5c by computation) *)
Lemma r_sm0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc tfibsegs AD2l.SegB 0.
Proof. intros fx0. exact (RtSM0.cmd_stack_malloc0_contract AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms). Qed.
Lemma r_vsnprintf_seg : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_avsnprintf_realizes fx0 rc tfibsegs AD2l.SegB RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIG SS___interceptor_trampoline_vsnprintf) gotwA guardA.
Proof.
intros fx0. replace (SIG SS___interceptor_trampoline_vsnprintf) with SegRtPC.PC_vsnprintf by pc_eq.
replace gotwA with RtAPI.A_SSP_GOT by pc_eq. replace guardA with RtAPI.A_SSP_GUARD by pc_eq.
exact (SegRtClosed.seg_vsnprintf_closed AD2l.SegB AD2l.SegB_syms).
Qed.

(* ---- refuse: the fifth G3 walk, refuse_a.r_walk (827761a2670c; refuse.v's refuse_walk restates it under the
   same 11 hypotheses), at PI := PB_seg and B := SegB. cross_check's REFUSE (stated at SEG_RLO / SEG_RHI, which are RLO_A /
   RHI_A by definition) and reac_segconf_parse_file's REF take it. SM0 := r_sm0, SMP / ASF / FFL / TL / TLF / ML /
   OBJ := the listing's lemmas at SegB, SNP := r_snprintf, VSNP := r_vsnprintf_seg, SSPX := sspx. *)
Lemma cl_refuse : forall fx0 : YK11.FPState,
  A.Prog.refuse_c.refuse_contract (fx := fx0) tfibsegs AD2l.SegB
    (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Proof.
intros fx0. eapply (refuse_a.r_walk (fx := fx0) (PI := SegImg.PB_seg) AD2l.SegB);
  first [ exact r_sm0 | exact r_snprintf | exact r_vsnprintf_seg | exact sspx
        | exact (SegRecRest.seg_stack_malloc_progress AD2l.SegB) | exact (SegRecRest.seg_astack_free_law AD2l.SegB)
        | exact (SegRecRest.seg_frame_flag_law AD2l.SegB) | exact (SegRecRest.seg_palib AD2l.SegB AD2l.SegB_syms)
        | exact (SegRecRest.seg_palibf AD2l.SegB AD2l.SegB_syms)
        | exact (SegRecRest.seg_model_laws AD2l.SegB AD2l.SegB_syms) | exact SegRecRest.seg_val_objs_PB ].
Qed.
(* ---- G4 + G5: lib/A/Prog/SegG45.v's composition at PB_seg / SegB ------------------------------------- *)
(* the record and listing facts SegG45 takes, from the listing's and the core's lemmas *)
#[local] Instance seg_ro_below : ro_below_ofl tfibsegs RLO_A RHI_A.
Proof.
exact (SegRecRo.ROB tfibsegs AD2l.SegB (YG0q.AR_laws_ok _ _) AD2l.SegB_syms
  (SegRecImg.seg_img_facts_tfib _ AD2l.SegB_syms)).
Qed.
Create HintDb g45i.
#[local] Hint Resolve sspx r_strlen r_strcmp r_strncmp r_strstr r_isalnum r_strncpy r_strrchr r_strtol0 r_memset
  r_memcpy r_sm1 : g45i.
(* the record facts at SegB, named so they can be hints *)
Definition h_palib := SegRecRest.seg_palib AD2l.SegB AD2l.SegB_syms.
Definition h_palibf := SegRecRest.seg_palibf AD2l.SegB AD2l.SegB_syms.
Definition h_model_laws := SegRecRest.seg_model_laws AD2l.SegB AD2l.SegB_syms.
Definition h_errno_rom := AD2l.SegB_errno_rom AD2l.SegB AD2l.SegB_syms.
Definition h_sm_progress := SegRecRest.seg_stack_malloc_progress AD2l.SegB.
Definition h_asf_law := SegRecRest.seg_astack_free_law AD2l.SegB.
Definition h_ffl_law := SegRecRest.seg_frame_flag_law AD2l.SegB.
#[local] Hint Unfold reac_segconf_declared_d.dc_sspP : g45i.
#[local] Hint Resolve seg_ro_below : g45i.
#[local] Hint Resolve h_palib h_palibf h_model_laws SegRecRest.seg_sig_prog_PB SegRecRest.seg_val_objs_PB
  SegRecRest.seg_val_relro_PB h_errno_rom h_sm_progress h_asf_law h_ffl_law : g45i.
Lemma cl_reac_segconf_find : forall fx0 : YK11.FPState,
  A.Prog.reac_segconf_find_c.reac_segconf_find_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_segconf_find)
    STK_reac_segconf_find RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_find (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_segconf_init : forall fx0 : YK11.FPState,
  @A.Prog.reac_segconf_init_c.reac_segconf_init_contract fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB (BASE + AF_reac_segconf_init)
    STK_reac_segconf_init.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_init (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_segconf_role_file : forall fx0 : YK11.FPState,
  A.Prog.reac_segconf_role_file_c.reac_segconf_role_file_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_segconf_role_file)
    STK_reac_segconf_role_file RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_role_file (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_segconf_role : forall fx0 : YK11.FPState,
  A.Prog.reac_segconf_role_c.reac_segconf_role_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_segconf_role)
    STK_reac_segconf_role RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_role (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_segconf_ignore_file : forall fx0 : YK11.FPState,
  A.Prog.reac_segconf_ignore_file_c.reac_segconf_ignore_file_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_segconf_ignore_file)
    STK_reac_segconf_ignore_file RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_ignore_file (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_segconf_ignored : forall fx0 : YK11.FPState,
  A.Prog.reac_segconf_ignored_c.reac_segconf_ignored_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_segconf_ignored)
    STK_reac_segconf_ignored RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_ignored (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_segconf_model : forall fx0 : YK11.FPState,
  A.Prog.reac_segconf_model_c.reac_segconf_model_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_segconf_model)
    STK_reac_segconf_model RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_model (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_check_absent : forall fx0 : YK11.FPState,
  @A.Prog.check_absent_c.check_absent_contract fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB (BASE + AF_check_absent)
    STK_check_absent RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_absent (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_check_segments : forall fx0 : YK11.FPState,
  A.Prog.check_segments_c.check_segments_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_check_segments)
    STK_check_segments RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_segments (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_check_role : forall fx0 : YK11.FPState,
  A.Prog.check_role_c.check_role_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_check_role)
    STK_check_role.
Proof. intros fx0. eapply (SegG45.cl_check_role (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_check_model : forall fx0 : YK11.FPState,
  A.Prog.check_model_c.check_model_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_check_model)
    STK_check_model RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_model (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_check_ignore : forall fx0 : YK11.FPState,
  A.Prog.check_ignore_c.check_ignore_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_check_ignore)
    STK_check_ignore.
Proof. intros fx0. eapply (SegG45.cl_check_ignore (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_check_provenance : forall fx0 : YK11.FPState,
  A.Prog.check_provenance_c.check_provenance_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_check_provenance)
    STK_check_provenance RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_provenance (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_check_refusals : forall fx0 : YK11.FPState,
  A.Prog.check_refusals_c.check_refusals_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_check_refusals)
    STK_check_refusals.
Proof. intros fx0. eapply (SegG45.cl_check_refusals (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_check_address : forall fx0 : YK11.FPState,
  A.Prog.check_address_c.check_address_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_check_address)
    STK_check_address RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_address (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_check_knock_refused : forall fx0 : YK11.FPState,
  A.Prog.check_knock_refused_c.check_knock_refused_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_check_knock_refused)
    STK_check_knock_refused RLO_A RHI_A seg_litA_fz gotwA guardA.
Proof. intros fx0. eapply (SegG45.cl_check_knock_refused (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_check_declared : forall fx0 : YK11.FPState,
  A.Prog.check_declared_c.check_declared_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_check_declared)
    STK_check_declared RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_declared (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_name_ok : forall fx0 : YK11.FPState,
  A.Prog.name_ok_c.name_ok_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_name_ok)
    STK_name_ok RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_name_ok (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_declared_vlan_split : forall fx0 : YK11.FPState,
  A.Prog.reac_declared_vlan_split_c.reac_declared_vlan_split_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_declared_vlan_split)
    STK_reac_declared_vlan_split RLO_A RHI_A gotwA guardA.
Proof. intros fx0. eapply (SegG45.cl_reac_declared_vlan_split (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_declared_vlan_add : forall fx0 : YK11.FPState,
  A.Prog.reac_declared_vlan_add_c.reac_declared_vlan_add_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_declared_vlan_add)
    STK_reac_declared_vlan_add RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_declared_vlan_add (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_segconf_declared : forall fx0 : YK11.FPState,
  A.Prog.reac_segconf_declared_c.reac_segconf_declared_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_segconf_declared)
    STK_reac_segconf_declared RLO_A RHI_A gotwA guardA.
Proof.
intros fx0. eapply (SegG45.cl_reac_segconf_declared (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i.
all: try (unfold reac_segconf_declared_d.dc_sspP; exact sspx). all: try exact seg_ro_below.
Qed.

(* ---- G2: lib/A/Prog/SegG2.v's composition of its six landed walks at PB_seg / SegB ------------ *)
#[local] Hint Resolve r_bcmp r_snprintf : g45i.
Lemma cl_fuzz_catalogue_row : forall fx0 : YK11.FPState,
  A.Prog.fuzz_catalogue_row_c.fuzz_catalogue_row_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_fuzz_catalogue_row)
    STK_fuzz_catalogue_row RLO_A RHI_A catA.
Proof. intros fx0. eapply (SegG2.cl_fuzz_catalogue_row (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_box_catalogue : forall fx0 : YK11.FPState,
  A.Prog.reac_box_catalogue_c.reac_box_catalogue_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_box_catalogue)
    STK_reac_box_catalogue catA.
Proof. intros fx0. eapply (SegG2.cl_reac_box_catalogue (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_reac_box_catalogue_by_token : forall fx0 : YK11.FPState,
  A.Prog.reac_box_catalogue_by_token_c.reac_box_catalogue_by_token_contract (fx := fx0) tfibsegs AD2l.SegB
    (BASE + AF_reac_box_catalogue_by_token) STK_reac_box_catalogue_by_token RLO_A RHI_A catA.
Proof. intros fx0. eapply (SegG2.cl_reac_box_catalogue_by_token (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_ieq : forall fx0 : YK11.FPState,
  A.Prog.ieq_c.ieq_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_ieq) STK_ieq RLO_A RHI_A.
Proof. intros fx0. eapply (SegG2.cl_ieq (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_m_find : forall fx0 : YK11.FPState,
  @A.Prog.m_find_c.m_find_contract fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Proof. intros fx0. eapply (SegG2.cl_m_find (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
Lemma cl_m_refuse : forall fx0 : YK11.FPState,
  @A.Prog.m_refuse_c.m_refuse_contract fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A
    seg_litA_fz gotwA guardA.
Proof. intros fx0. eapply (SegG2.cl_m_refuse (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i. Qed.
(* m_file: G2's last walk, m_fileA.m_file_walk (ec9e8418c67), at PI := PB_seg and B := SegB. Its premises:
   the record facts (h_palib, h_palibf, h_model_laws, seg_val_objs_PB, seg_sig_prog_PB, sspx, the relro window
   SegImg.seg_relro_img, h_sm_progress, h_asf_law, h_ffl_law), MCROM := SegG1.g1_MCR at SegB (memchr's constant window
   is read-only, unowned and not the errno cell: the same statement as G1's MCR), the rows above (r_sm1, r_snprintf,
   r_strchr, r_strlen, r_memchr, r_bcmp, r_memcpy, r_memset) and G2's closures above (cl_m_refuse, cl_ieq, cl_m_find,
   cl_fuzz_catalogue_row) *)
#[local] Hint Resolve r_strchr r_memchr cl_m_refuse cl_ieq cl_m_find cl_fuzz_catalogue_row : g45i.
Lemma cl_m_file : forall fx0 : YK11.FPState,
  @A.Prog.m_file_c.m_file_contract fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB (BASE + AF_m_file) STK_m_file RLO_A RHI_A
    seg_litA_fz wordsA rolesA catA gotwA guardA.
Proof.
intros fx0. eapply (m_fileA.m_file_walk (fx := fx0) (PI := SegImg.PB_seg) AD2l.SegB); eauto with g45i.
all: first [ exact sspx
           | exact (SegG1.g1_MCR AD2l.SegB AD2l.SegB_syms)
           | exact (@SegG1.g1_MCR rc AD2l.SegB AD2l.SegB_syms)
           | exact (fun a Ha => SegImg.seg_relro_img a Ha)
           | idtac ].
Qed.

(* ---- G3: lib/A/Prog/SegG3.v's four closed walks (84490aabe1bd) at B := SegB ------------------ *)
(* SegG3 takes each walk at PB_seg with its record facts discharged by the listing's lemmas under HB; here HB :=
   AD2l.SegB_syms, the runtime rows are the rows above, refuse's closure is cl_refuse, and the G2 callees are G2's
   closures above *)
#[local] Hint Resolve r_strchr r_strncasecmp r_strcasecmp r_strspn r_set_shadow_f8 r_set_shadow_00 r_sm5 r_sf5
  cl_refuse cl_reac_box_catalogue cl_reac_box_catalogue_by_token : g45i.
Lemma cl_trim : forall fx0 : YK11.FPState,
  A.Prog.trim_c.trim_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_trim) STK_trim RLO_A RHI_A.
Proof. intros fx0. eapply (SegG3.cl_trim (rc := rc) AD2l.SegB AD2l.SegB_syms); eauto with g45i. Qed.
Lemma cl_cross_check : forall fx0 : YK11.FPState,
  A.Prog.cross_check_c.cross_check_contract (fx := fx0) tfibsegs AD2l.SegB
    (BASE + AF_cross_check) STK_cross_check RLO_A RHI_A seg_litA_rc gotwA guardA.
Proof. intros fx0. eapply (SegG3.cl_cross_check (rc := rc) AD2l.SegB AD2l.SegB_syms); eauto with g45i. Qed.
Lemma cl_reac_segconf_parse_file : forall fx0 : YK11.FPState,
  @A.Prog.reac_segconf_parse_file_c.reac_segconf_parse_file_contract fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Proof.
intros fx0. eapply (SegG3.cl_reac_segconf_parse_file (rc := rc) AD2l.SegB AD2l.SegB_syms); eauto with g45i.
Qed.
Lemma cl_reac_segconf_parse : forall fx0 : YK11.FPState,
  A.Prog.reac_segconf_parse_c.reac_segconf_parse_contract (fx := fx0) tfibsegs AD2l.SegB (BASE + AF_reac_segconf_parse)
    STK_reac_segconf_parse RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Proof.
intros fx0. eapply (SegG3.cl_reac_segconf_parse (rc := rc) AD2l.SegB AD2l.SegB_syms); eauto with g45i.
Qed.

(* ---- G1: lib/A/Prog/SegG1.v's harness walk (bd12cd505428) at B := SegB ----------------------- *)
(* SegG1 discharges the walk's record, listing and image facts under HB; here HB := AD2l.SegB_syms, the runtime rows
   are the rows above, the 21 callees are the groups' closures above (m_file's through cl_m_file, open) *)
Lemma cl_LLVMFuzzerTestOneInput : forall fx0 : YK11.FPState,
  @A.Prog.LLVMFuzzerTestOneInput_c.LLVMFuzzerTestOneInput_contract fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB ameter_triv
    (BASE + AF_LLVMFuzzerTestOneInput) STK_LLVMFuzzerTestOneInput emptyA RLO_A RHI_A longlA mod40A catA wordsA
    rolesA gotwA guardA seg_litA_fz seg_litA_rc.
Proof.
intros fx0.
exact (@SegG1.cl_LLVMFuzzerTestOneInput rc AD2l.SegB AD2l.SegB_syms r_sm3 r_malloc4 r_free4 r_memchr r_strrchr
  r_memcpy r_memset r_strlen r_strcmp r_calloc4 RtPFCmd.CMD_SNP_CR r_snprintf_seg r_snp_cr r_shf5 cl_reac_segconf_init
  cl_check_refusals cl_check_address cl_check_knock_refused cl_reac_segconf_declared cl_check_declared
  cl_check_segments cl_reac_segconf_role cl_check_role cl_reac_segconf_model cl_check_model cl_reac_segconf_ignored
  cl_check_ignore cl_reac_segconf_role_file cl_reac_segconf_ignore_file cl_check_provenance cl_reac_segconf_parse
  cl_m_find cl_check_absent cl_m_refuse cl_m_file cl_reac_segconf_parse_file fx0).
Qed.

(* ---- the entry, at SegInstA's A_LLVMFuzzerTestOneInput_A (SegTop.v's HLTOI) ----------------------------- *)
Theorem seg_ltoi_all : forall fx0 : YK11.FPState,
  @A.Prog.LLVMFuzzerTestOneInput_c.LLVMFuzzerTestOneInput_contract fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB ameter_triv
    A_LLVMFuzzerTestOneInput_A STK_LLVMFuzzerTestOneInput emptyA RLO_A RHI_A longlA mod40A catA wordsA rolesA gotwA
    guardA seg_litA_fz seg_litA_rc.
Proof. intros fx0. rewrite <- SegInstPB.pb_entry_LLVMFuzzerTestOneInput. exact (cl_LLVMFuzzerTestOneInput fx0). Qed.
End closed.
