(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA (HDR 0x862cc -> HFIND 0x86abc, or a refusal to TAIL
   0x86cf8): memchr(s, ']', e - s), no ']' or close + 1 <> e refuses, the strip of [s + 1, close), be - b < 8 /
   ieq(b, 7, "segment") / b[7] not blank refuses, the strip of the name, n = 0 or n >= 16 refuses, else HFIND.
   The proof composes the point walks of m_file_s_hdra_m.v (s_mf_hdra_of_parts):
     m_file_s_hdra_11.v  HDR  0x862cc  the memchr call (MemchrDef.amemchr_realizesM, m_file_memchr.v aj_memchr_atM)
     m_file_s_hdra_8.v   RMC  0x862d8  memchr's answer: refusal (no ']' / not last) or the header strip
     m_file_s_hdra_1.v   L1   0x862fc  the header strip's forward loop
     m_file_s_hdra_2.v   BK0  0x863e4  its exit
     m_file_s_hdra_3.v   L2   0x863ec  the backward loop
     m_file_s_hdra_10.v  LEN  0x86490  be - b < 8 refusal, the ieq call (m_file_iq.v mf_ieq_call)
     m_file_s_hdra_9.v   RIEQ 0x864b4  ieq's answer, b[7]
     m_file_s_hdra_4.v   L3   0x864ec  the name strip's forward loop
     m_file_s_hdra_6.v   NB0  0x86a50  its exit
     m_file_s_hdra_5.v   L4   0x86a64  the backward loop
     m_file_s_hdra_7.v   FIN  0x86aac  the name's checks: refusal or HFIND
     m_file_s_hdra_12.v  REF1 0x86bcc  cur = NULL, m_refuse (m_file_rf.v mf_refuse_step), to TAIL
     m_file_s_hdra_13.v  REF2 0x8652c  the same from the header checks
   Shared: m_file_s_hdra_t.v (model facts), m_file_s_hdra_e.v (byte and branch facts), m_file_s_hdra_w.v (the seed
   with read-only slots, the carry across a run). The HDRA segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import ieq_c m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_memchr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_hdra_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require
m_file_s_hdra_1 m_file_s_hdra_2 m_file_s_hdra_3 m_file_s_hdra_4 m_file_s_hdra_5 m_file_s_hdra_6 m_file_s_hdra_7
m_file_s_hdra_8 m_file_s_hdra_9 m_file_s_hdra_10 m_file_s_hdra_11 m_file_s_hdra_12 m_file_s_hdra_13.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the image's static objects (the string literals' addresses) and the program symbols' addresses *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
(* the stack-protector guard and the relro window *)
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
(* the callees: memchr (row 20, the constant window form), ieq, m_refuse *)
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B SegInstA.memchr_loA SegInstA.memchr_hiA (SIGMA SS___interceptor_trampoline_memchr).
Hypothesis MCROM : m_file_memchr.memchr_rom_fact SEGS B.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState,
  m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse) SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A
    SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.

(* one point: its lemma at every FP state, from the next points' statements at every FP state *)
Ltac hda_pt L := intros; intro; eapply L; eauto.

Lemma s_mf_hdra : S_MF_HDRA B.
Proof.
apply s_mf_hdra_of_parts. unfold HDA_PARTS.
unfold HDA_REF1_F, HDA_REF2_F, HDA_L1_F, HDA_BK0_F, HDA_L2_F, HDA_LEN_F, HDA_L3_F, HDA_NB0_F, HDA_L4_F, HDA_FIN_F,
  HDA_RMC_F, HDA_RIEQ_F, MF_TAIL_F, MF_HFIND_F, MF_HDR_F.
repeat split.
- intros n HT fx0. exact (m_file_s_hdra_12.hda_ref1 (fx := fx0) B VOBJS SIGP SSP RELRO M_REFUSE n HT).
- intros n HT fx0. exact (m_file_s_hdra_13.hda_ref2 (fx := fx0) B VOBJS SIGP SSP RELRO M_REFUSE n HT).
- intros n R1 HF fx0. exact (m_file_s_hdra_7.hda_fin (fx := fx0) B VOBJS n (R1 fx0) (HF fx0)).
- intros n FN fx0. exact (m_file_s_hdra_5.hda_l4 (fx := fx0) B VOBJS n (FN fx0)).
- intros n FN L4 fx0. exact (m_file_s_hdra_6.hda_nb0 (fx := fx0) B VOBJS n (FN fx0) (L4 fx0)).
- intros n NB fx0. exact (m_file_s_hdra_4.hda_l3 (fx := fx0) B VOBJS n (NB fx0)).
- intros n R2 L3 fx0. exact (m_file_s_hdra_9.hda_rieq (fx := fx0) B VOBJS n (R2 fx0) (L3 fx0)).
- intros n R2 RI fx0. exact (m_file_s_hdra_10.hda_len (fx := fx0) B VOBJS RELRO IEQ SIGP n (R2 fx0) (RI fx0)).
- intros n LN fx0. exact (m_file_s_hdra_3.hda_l2 (fx := fx0) B VOBJS n (LN fx0)).
- intros n LN L2 fx0. exact (m_file_s_hdra_2.hda_bk0 (fx := fx0) B VOBJS n (LN fx0) (L2 fx0)).
- intros n BK fx0. exact (m_file_s_hdra_1.hda_l1 (fx := fx0) B VOBJS n (BK fx0)).
- intros n R1 BK L1 fx0. exact (m_file_s_hdra_8.hda_rmc (fx := fx0) B VOBJS n (R1 fx0) (BK fx0) (L1 fx0)).
- intros n RM fx0. exact (m_file_s_hdra_11.hda_hdr (fx := fx0) B VOBJS RELRO AMEMCHR MCROM n (RM fx0)).
Qed.
End e.
End f.
End d.
