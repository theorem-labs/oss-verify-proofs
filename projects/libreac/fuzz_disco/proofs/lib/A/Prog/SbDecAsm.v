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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec SbDecLib SbDecCut.
Import ListNotations.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis S1 : sbd_seg1_stmt B.
Hypothesis S2 : sbd_seg2_stmt B.
Hypothesis S3 : sbd_seg3_stmt B.
Hypothesis S4 : sbd_seg4_stmt B.
Hypothesis S5 : sbd_seg5_stmt B.
Lemma sbd_from5 : forall X W c, sbd_cx B X -> sbd_at5 B X W c -> SRr SEGS W c (sbd_post B X).
Proof.
intros X W c HX (-> & pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
exact (S5 X pos regs1 lyc1 Sc1 memc1 mdc1 HX Hs).
Qed.
Lemma sbd_from4 : forall X W c, sbd_cx B X -> sbd_at4 B X W c -> SRr SEGS W c (sbd_post B X).
Proof.
intros X W c HX (-> & pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S4 X pos regs1 lyc1 Sc1 memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (sbd_from5 X W2 c2 HX H2).
Qed.
Lemma sbd_from3 : forall X W c, sbd_cx B X -> sbd_at3 B X W c -> SRr SEGS W c (sbd_post B X).
Proof.
intros X W c HX (-> & pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S3 X pos regs1 lyc1 Sc1 memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (sbd_from4 X W2 c2 HX H2).
Qed.
Lemma sbd_from2 : forall X W c, sbd_cx B X -> sbd_at2 B X W c -> SRr SEGS W c (sbd_post B X).
Proof.
intros X W c HX (-> & pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S2 X pos regs1 lyc1 Sc1 memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (sbd_from3 X W2 c2 HX H2).
Qed.
Lemma sbd_from1 : forall X, sbd_cx B X ->
  SRr SEGS (si_W X) (cfg_at (fx := si_fq X) SEGS (BASE + AF_sb_dec) (si_regs X) (si_memc X) (si_mdc X))
    (sbd_post B X).
Proof.
intros X HX. eapply SRr_bind; [exact (S1 X HX)|].
intros W2 c2 _ H2. exact (sbd_from2 X W2 c2 HX H2).
Qed.
Theorem pb_sb_dec_of_segs : tsb_dec_spec B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch A v md p cap n over.
intros.
exact (sbd_from1 (SbdIn fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch A v md p cap n over)
  ltac:(unfold sbd_cx, sbm_room, sbm_acc; cbn [si_fq si_STK si_sp0 si_FP si_ly si_S si_W0 si_mem0 si_md0
    si_own si_lyc si_Sc si_W si_memc si_mdc si_k si_regs si_ch si_A si_v si_md si_p si_cap si_n si_over];
    repeat (first [split; [assumption|] | split; [unfold sbd_rec; repeat (split; [assumption|]); assumption|]]);
    assumption)).
Qed.
End h.
End f.
End d.
