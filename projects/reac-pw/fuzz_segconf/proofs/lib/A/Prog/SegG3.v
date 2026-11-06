(* reac-pw/fuzz_segconf, image A: the four closed function walks of group G3 (the G3 walks) at image A's listing instance
   PI := SegImg.PB_seg, the sink head AE2k.tfib_sink_head and an allocator record B with HB : AF0m.SegBSyms B, composed
   with each other: cross_check's closure discharges reac_segconf_parse's CC, trim's discharges reac_segconf_parse_file's
   TRIM, and reac_segconf_parse_file's discharges reac_segconf_parse's PF. Every record hypothesis of the four walks is
   discharged by one listing lemma (the G3 walks' check of 2026-10-30):
   - TL := SegRecRest.seg_palib B HB, TLF := seg_palibf B HB, ML := seg_model_laws B HB, SIGP := seg_sig_prog_PB,
     OBJ / VOBJ := seg_val_objs_PB, VRO := seg_val_relro_PB, SMP := seg_stack_malloc_progress B;
   - cross_check's RELRO := SegImg.seg_relro_img (closed: the read-only window [0xa14a0, 0xa3748) lies in tfibsegs);
   - SSPX := SegRecCells.seg_ssp under YG0q.AR_laws_ok, HB and IMG := SegRecImg.seg_img_facts_tfib B HB.
   What is left are Section hypotheses of exactly the walks' own texts: the runtime rows at the listing's call targets
   (the interceptor layer's wrapper rows, the kit's intrinsic laws, the core's shadow and side-stack rows), refuse's contract (the
   fifth G3 walk, not closed yet), and the G2 callees reac_box_catalogue / reac_box_catalogue_by_token, which
   lib/A/Prog/SegProgClosed.v discharges from lib/A/Prog/SegG2.v at the core's record SegB.
   The walks are the G3 walks at 84490aabe1bd (lib/A/Prog/trim.v, cross_check.v,
   reac_segconf_parse.v, reac_segconf_parse_file.v), merged into this close; FINAL 6f783602b5e3 is
   an ancestor (checked). This file states no contract: each lemma's statement is the contract of lib/A/Prog/<F>_c.v at
   contracts FINAL 6f783602b5e3, at SegInstA's terms, as the walk states it.
   proves no function (kind: merge; the composition of G3's walk theorems). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI00 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m AE2k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg RtString RtFormat RtStack RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegObj
  SegPaLib PaLibF SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_box_catalogue_by_token_c reac_box_catalogue_c reac_segconf_parse_file_c cross_check_c reac_segconf_parse_c
  SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegImg SegRecBase SegRecRest SegRecCells
  SegRecImg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require trim cross_check reac_segconf_parse
  reac_segconf_parse_file.
Import ListNotations.
Local Open Scope Z_scope.

Section g3. Context {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Notation PB := SegImg.PB_seg.
#[local] Notation SEGS := (@pa_segs _ seg_listing SegImg.PB_seg).
#[local] Notation BASE := (@pa_val _ seg_listing SegImg.PB_seg A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing SegImg.PB_seg s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis HB : AF0m.SegBSyms B.

(* ---- the runtime rows, at the listing's call targets (the walks' own texts) ---------------------------- *)
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
Hypothesis ANCASE : forall fx0 : YK11.FPState,
  @RtSeg.astrncasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncasecmp).
Hypothesis ASTRCASECMP : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis STRSPN : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strspn) gotwA guardA.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis ABCMP : forall fx0 : YK11.FPState,
  @abcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_bcmp).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASHF8 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_f8) 0xf8.
Hypothesis ASH00 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_00) 0.
Hypothesis ASM5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5.
Hypothesis ASF5 : forall fx0 : YK11.FPState,
  @RtStack.astack_free_cls_realizes fx0 rc SEGS B (SIG SS___asan_stack_free_5) 5.

(* ---- the callees whose closures are not G3's closed walks: refuse (G3, open) and G2's two catalogue functions *)
Hypothesis REF : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B
  (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis BT : forall fx0 : YK11.FPState, reac_box_catalogue_by_token_contract (fx := fx0) SEGS B
  (BASE + AF_reac_box_catalogue_by_token) STK_reac_box_catalogue_by_token RLO_A RHI_A catA.
Hypothesis CAT : forall fx0 : YK11.FPState, reac_box_catalogue_contract (fx := fx0) SEGS B
  (BASE + AF_reac_box_catalogue) STK_reac_box_catalogue catA.

(* ---- the record facts, each from one listing lemma ------------------------------------------------------ *)
Lemma g3_img : SegRecBase.seg_img_facts SEGS B.
Proof. exact (SegRecImg.seg_img_facts_tfib B HB). Qed.
Lemma g3_sspx : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Proof. exact (SegRecCells.seg_ssp SEGS B (YG0q.AR_laws_ok SEGS B) HB g3_img). Qed.
Lemma g3_relro : forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a.
Proof.
first [ exact SegImg.seg_relro_img
      | intros a Ha; apply SegImg.seg_relro_img; unfold SEG_RLO, SEG_RHI in Ha; exact Ha ].
Qed.

Local Ltac g3_premise :=
  first [ exact (SegRecRest.seg_palib B HB) | exact (SegRecRest.seg_palibf B HB)
        | exact (SegRecRest.seg_model_laws B HB) | exact SegRecRest.seg_sig_prog_PB
        | exact SegRecRest.seg_val_objs_PB | exact SegRecRest.seg_val_relro_PB
        | exact (SegRecRest.seg_stack_malloc_progress B) | exact g3_relro | exact g3_sspx
        | assumption ].

(* ---- the four closures ---------------------------------------------------------------------------------- *)
(* trim: trim_walk, ASTRLEN and TL *)
Lemma cl_trim : forall fx0 : YK11.FPState,
  trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Proof.
intros fx0. apply (trim.trim_walk (fx := fx0) (rc := rc) (PI := PB) B); g3_premise.
Qed.
(* cross_check: cross_check_walk, REFUSE := REF (cross_check states it at SEG_RLO / SEG_RHI, which are RLO_A / RHI_A
   by definition), TL, TLF, VOBJ, SIGP, RELRO, SSPX *)
Lemma cl_cross_check : forall fx0 : YK11.FPState,
  cross_check_contract (fx := fx0) SEGS B (BASE + AF_cross_check) STK_cross_check RLO_A RHI_A seg_litA_rc
    gotwA guardA.
Proof.
intros fx0. apply (cross_check.cross_check_walk (fx := fx0) (rc := rc) (PI := PB) B); g3_premise.
Qed.
(* reac_segconf_parse_file: reac_segconf_parse_file_walk, its 14 runtime rows, REF, TRIM := cl_trim, BT, CAT, and SMP,
   TL, TLF, ML, SIGP, OBJ, VRO, SSPX *)
Lemma cl_reac_segconf_parse_file : forall fx0 : YK11.FPState,
  reac_segconf_parse_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_parse_file)
    STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Proof.
intros fx0.
apply (reac_segconf_parse_file.reac_segconf_parse_file_walk (fx := fx0) (rc := rc) (PI := PB) B);
  first [ exact cl_trim | g3_premise ].
Qed.
(* reac_segconf_parse: reac_segconf_parse_walk, PF := cl_reac_segconf_parse_file, CC := cl_cross_check, SIGP, OBJ,
   VRO, SSPX *)
Lemma cl_reac_segconf_parse : forall fx0 : YK11.FPState,
  reac_segconf_parse_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_parse) STK_reac_segconf_parse RLO_A RHI_A
    seg_litA_rc catA gotwA guardA.
Proof.
intros fx0. apply (reac_segconf_parse.reac_segconf_parse_walk (rc := rc) (PI := PB) B);
  first [ exact cl_reac_segconf_parse_file | exact cl_cross_check | g3_premise ].
Qed.
End g3.

About cl_trim.
About cl_cross_check.
About cl_reac_segconf_parse_file.
About cl_reac_segconf_parse.
Print Assumptions cl_reac_segconf_parse.
