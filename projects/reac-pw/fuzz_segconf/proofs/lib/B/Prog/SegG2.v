(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the nine function walks of group
   G2 on image B (reac_box_catalogue, fuzz_catalogue_row, ieq, reac_box_catalogue_by_token, m_find, strip, fold,
   m_refuse, m_file) composed with each other at the walks' own abstract listing instance
   (`Context {PI : PAImg seg_listing}`) and allocator record B. The twin of image A's lib/A/Prog/SegG2.v (commit
   6f7a1561a103), with image B's two outlined functions strip and fold and with m_file, whose image-B walk is
   complete. fuzz_catalogue_row's walk discharges the callee contract reac_box_catalogue_by_token's walk takes (FCR);
   m_file's callee contracts IEQ, M_FIND, M_REFUSE, ROW, STRIP, FOLD are discharged by those walks.
   What is left are Section hypotheses of exactly the walks' own texts:
   - the record and listing facts TL, TLF, ML, VOBJS, SIGP, IMG (seg_img_facts), SSPX (the stack-protector cell at
     every AR state), MCROM (memchr_rom_fact) and the side-stack laws SMP / ASF / FFL, which
     lib/B/Prog/SegProgClosed.v discharges at image B's instance SegImg.PB_seg where the listing has the lemma;
   - the runtime rows at the listing's call targets: strlen, bcmp, strchr, memchr, snprintf (RtPFSeg's form at
     RtPFCmd's window, as m_refuse and m_file state it), checked memset / memcpy, the class-1 side-stack frame.
   This file states no contract: each lemma's statement is the contract of lib/B/Prog/<F>_c.v at SegInstB's terms,
   as the walk states it.
   proves no function (kind: merge; the composition of G2's walk theorems). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable SegSyms SegList SegPa SegPaLib PaLibF SegObj SegGlob SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegRecBase m_file_memchr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString RtSeg RtPFSeg RtPFCmd RtAPI MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
fuzz_catalogue_row_c reac_box_catalogue_c reac_box_catalogue_by_token_c ieq_c m_find_c m_refuse_c strip_c fold_c
m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require
fuzz_catalogue_row reac_box_catalogue reac_box_catalogue_by_token ieq m_find m_refuse strip fold m_file.
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
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis VOBJS : seg_val_objs (PI := PI).
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis IMG : SegRecBase.seg_img_facts SEGS B.
(* the stack-protector cell at every AR state (m_file's text; the walks' dc_sspP unfolded) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (aview SEGS (w_H W) mem) gotwA guardA.
(* musl memchr's word-constant window: read-only, not a runtime-owned static, not the errno cell *)
Hypothesis MCROM : m_file_memchr.memchr_rom_fact SEGS B.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.

(* ---- the runtime rows, at the listing's call targets (the walks' own texts) ---------------------------- *)
(* strlen, row 16: ASTRLEN (fuzz_catalogue_row, reac_box_catalogue_by_token) = STRLEN (ieq, m_find, m_file) *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
(* bcmp, row 19 (the kit's abcmp_realizes) *)
Hypothesis ABCMP : forall fx0 : YK11.FPState,
  @abcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_bcmp).
(* strchr and memchr (m_file) *)
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B SegInstB.memchr_loA SegInstB.memchr_hiA
    (SIG SS___interceptor_trampoline_memchr).
(* snprintf, row 4, in RtPFSeg's form at RtPFCmd's window (m_refuse's SNP, m_file's ASNP) *)
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIG SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.
(* the checked memset / memcpy entries and the class-1 side-stack frame (m_file) *)
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis ASM1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.

#[local] Hint Resolve YG0q.AR_laws_ok : g2.

Lemma cl_fuzz_catalogue_row : forall fx0 : YK11.FPState,
  fuzz_catalogue_row_contract (fx := fx0) SEGS B (BASE + AF_fuzz_catalogue_row) STK_fuzz_catalogue_row RLO_A RHI_A catA.
Proof. intros fx0. eapply fuzz_catalogue_row.fuzz_catalogue_row_walkB; eauto with g2. Qed.
#[local] Hint Resolve cl_fuzz_catalogue_row : g2.
Lemma cl_reac_box_catalogue : forall fx0 : YK11.FPState,
  reac_box_catalogue_contract (fx := fx0) SEGS B (BASE + AF_reac_box_catalogue) STK_reac_box_catalogue catA.
Proof. intros fx0. eapply reac_box_catalogue.reac_box_catalogue_walkB; eauto with g2. Qed.
Lemma cl_reac_box_catalogue_by_token : forall fx0 : YK11.FPState,
  reac_box_catalogue_by_token_contract (fx := fx0) SEGS B (BASE + AF_reac_box_catalogue_by_token)
    STK_reac_box_catalogue_by_token RLO_A RHI_A catA.
Proof. intros fx0. eapply reac_box_catalogue_by_token.reac_box_catalogue_by_token_walkB; eauto with g2. Qed.
Lemma cl_ieq : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) STK_ieq RLO_A RHI_A.
Proof. intros fx0. eapply ieq.ieq_walkB; eauto with g2. Qed.
Lemma cl_m_find : forall fx0 : YK11.FPState,
  m_find_contract (fx := fx0) SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Proof. intros fx0. eapply m_find.m_find_walkB; eauto with g2. Qed.
Lemma cl_strip : forall fx0 : YK11.FPState,
  strip_contract (fx := fx0) SEGS B (BASE + AF_strip) STK_strip.
Proof. intros fx0. eapply strip.strip_walkB; eauto with g2. Qed.
Lemma cl_fold : forall fx0 : YK11.FPState,
  fold_contract (fx := fx0) SEGS B (BASE + AF_fold) STK_fold.
Proof. intros fx0. eapply fold.fold_walkB; eauto with g2. Qed.
Lemma cl_m_refuse : forall fx0 : YK11.FPState,
  m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A seg_litA_fz gotwA guardA.
Proof. intros fx0. eapply m_refuse.m_refuse_walkB; eauto with g2. Qed.
#[local] Hint Resolve cl_ieq cl_m_find cl_strip cl_m_refuse : g2.
(* m_file: its callees ieq, m_find, m_refuse, fuzz_catalogue_row, strip and fold by their walks above *)
Lemma cl_m_file : forall fx0 : YK11.FPState,
  m_file_contract (fx := fx0) SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz wordsA rolesA catA
    gotwA guardA.
Proof.
intros fx0.
exact (m_file.m_file_walkB B VOBJS SIGP TL TLF ML IMG SSPX ASM1 SMP ASF FFL AMEMSET AMEMCPY ASTRCHR ASTRLEN ABCMP
  AMEMCHR MCROM ASNP cl_ieq cl_m_find cl_m_refuse cl_fuzz_catalogue_row cl_strip cl_fold fx0).
Qed.

End e.
End f.
End d.
