(* reac-pw/fuzz_segconf, image A: the six function walks of group G2 (the G2 walks) that have landed, composed with each
   other at the walks' own abstract listing instance (`Context {PI : PAImg seg_listing}`, the image-A owner's ruling) and
   allocator record B: fuzz_catalogue_row's walk discharges the callee contract reac_box_catalogue_by_token's walk takes
   (its hypothesis FCR). What is left are Section hypotheses of exactly the walks' own texts:
   - the record and listing facts TL (PALib B), VOBJS (seg_val_objs), SIGP (seg_sig_prog), which
     lib/A/Prog/SegProgClosed.v discharges at image A's instance SegImg.PB_seg and the core's record SegB
     (SegRecRest seg_palib / seg_val_objs_PB / seg_sig_prog_PB);
   - the wrapper rows at the listing's call targets: strlen (the interceptor layer's row 16; the walks name it ASTRLEN in
     fuzz_catalogue_rowA.v and reac_box_catalogue_by_tokenA.v and STRLEN in ieqA.v and m_findA.v, the same text, taken
     here once as ASTRLEN), bcmp (row 19, the kit's abcmp_realizes) and snprintf (row 4, RtFormat.asnprintf_realizes,
     which the interceptor layer's closing gives through RtPFSeg's seg_all_rtformat).
   m_file's walk (12 of 13 segments) is not composed yet.
   The walks are the G2 walks at 594d3b7864d5, merged into this close; FINAL
   6f783602b5e3 is an ancestor (checked). This file states no contract: each lemma's statement is the contract of
   lib/A/Prog/<F>_c.v at contracts FINAL 6f783602b5e3, at SegInstA's terms, as the walk states it.
   proves no function (kind: merge; the composition of G2's walk theorems). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable SegSyms SegList SegPa SegPaLib SegObj SegGlob SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
fuzz_catalogue_row_c reac_box_catalogue_c reac_box_catalogue_by_token_c ieq_c m_find_c m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require
fuzz_catalogue_rowA reac_box_catalogueA reac_box_catalogue_by_tokenA ieqA m_findA m_refuseA.
Import ListNotations.
Local Open Scope Z_scope.

Create HintDb g2.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
Section e.
Variable B : asyms.

(* ---- the record and listing facts (the walks' own texts) ---------------------------------------------- *)
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs (PI := PI).
Hypothesis SIGP : seg_sig_prog (PI := PI).

(* ---- the wrapper rows, at the listing's call targets (the walks' own texts) ---------------------------- *)
(* strlen, row 16: ASTRLEN (fuzz_catalogue_rowA, reac_box_catalogue_by_tokenA) = STRLEN (ieqA, m_findA), one text *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
(* bcmp, row 19 (the kit's abcmp_realizes) *)
Hypothesis ABCMP : forall fx0 : YK11.FPState,
  @abcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_bcmp).
(* snprintf, row 4 (RtFormat.asnprintf_realizes; the interceptor layer's closing gives it via RtPFSeg's seg_all_rtformat) *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_snprintf) SegInstA.gotwA SegInstA.guardA.

#[local] Hint Resolve YG0q.AR_laws_ok : g2.

Lemma cl_fuzz_catalogue_row : forall fx0 : YK11.FPState,
  fuzz_catalogue_row_contract (fx := fx0) SEGS B (BASE + AF_fuzz_catalogue_row) STK_fuzz_catalogue_row RLO_A RHI_A catA.
Proof. intros fx0. eapply fuzz_catalogue_rowA.fuzz_catalogue_row_walk; eauto with g2. Qed.
#[local] Hint Resolve cl_fuzz_catalogue_row : g2.
Lemma cl_reac_box_catalogue : forall fx0 : YK11.FPState,
  reac_box_catalogue_contract (fx := fx0) SEGS B (BASE + AF_reac_box_catalogue) STK_reac_box_catalogue catA.
Proof. intros fx0. eapply reac_box_catalogueA.reac_box_catalogue_walk; eauto with g2. Qed.
Lemma cl_reac_box_catalogue_by_token : forall fx0 : YK11.FPState,
  reac_box_catalogue_by_token_contract (fx := fx0) SEGS B (BASE + AF_reac_box_catalogue_by_token)
    STK_reac_box_catalogue_by_token RLO_A RHI_A catA.
Proof. intros fx0. eapply reac_box_catalogue_by_tokenA.reac_box_catalogue_by_token_walk; eauto with g2. Qed.
Lemma cl_ieq : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) STK_ieq RLO_A RHI_A.
Proof. intros fx0. eapply ieqA.ieq_walk; eauto with g2. Qed.
Lemma cl_m_find : forall fx0 : YK11.FPState,
  m_find_contract (fx := fx0) SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Proof. intros fx0. eapply m_findA.m_find_walk; eauto with g2. Qed.
Lemma cl_m_refuse : forall fx0 : YK11.FPState,
  m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A seg_litA_fz gotwA guardA.
Proof. intros fx0. eapply m_refuseA.m_refuse_walk; eauto with g2. Qed.

End e.
End f.
End d.
