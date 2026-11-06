(* m_file on fuzz_segconf.asan (image A), segment S_MF_FRONT of lib/A/Prog/m_file_m.v: from HEAD 0x860d0 to LONG
   0x86110, HDR 0x862cc, KEY 0x8633c or TAIL 0x86cf8 (MF-CUTS-A.md section 4: 113 instructions, five instrumented
   checks, the strchr and strlen wrappers). s_mf_front chains the pieces at every FP state (fr_chain of
   m_file_s_front_m.v): head and sc / sl (m_file_s_front_c.v: strchr(p, '\n'), strlen(p)), e (m_file_s_front_e.v:
   line++, the long-line test, the empty line), cl (m_file_s_front_cl.v: the comment loop), cx / sf / sm / sb
   (m_file_s_front_s.v: the forward and backward strip), st (m_file_s_front_e.v: the check of the first byte, 144(s1),
   the '[' test). Each instrumented check is a load of the shadow byte at (a >> 3) + the shadow base and a compare;
   its error path (a call of an errpath_load1 entry) is not reached, because the text left is addressable.
   The FRONT segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_m m_file_s_front_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
  m_file_s_front_c m_file_s_front_e m_file_s_front_cl m_file_s_front_s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
Section i.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis ASTRCHR : forall fx0 : YK11.FPState, @RtSeg.astrchr_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strchr).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).

Lemma s_mf_front : S_MF_FRONT B.
Proof.
intros n HT HL HH HK fx0.
apply (fr_chain (fx := fx0) B n (HT fx0) (HL fx0) (HH fx0) (HK fx0)).
- intros T H K. eapply (fr_st (fx := fx0)); eauto.
- intros ST j. eapply (fr_sb (fx := fx0)); eauto.
- intros SB ST. eapply (fr_sm (fx := fx0)); eauto.
- intros SM k. eapply (fr_sf (fx := fx0)); eauto.
- intros SF SM. eapply (fr_cx (fx := fx0)); eauto.
- intros CX i. exact (fr_cl (fx := fx0) B n CX i).
- intros LG CL ST. eapply (fr_e (fx := fx0)); eauto.
- intros E. eapply (fr_sl (fx := fx0)); eauto.
- intros E SL. eapply (fr_sc (fx := fx0)); eauto.
- intros SC. eapply (fr_head (fx := fx0)); eauto.
Qed.
End i.
End h.
End g.
About s_mf_front.
Print Assumptions s_mf_front.
