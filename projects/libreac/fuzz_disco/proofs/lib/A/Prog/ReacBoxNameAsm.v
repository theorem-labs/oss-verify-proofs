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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec ReacBoxName ReacBoxNameCut.
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
Hypothesis S1 : rbn_seg1_stmt B.
Hypothesis S2 : rbn_seg2_stmt B.
Hypothesis S3 : rbn_seg3_stmt B.
Hypothesis S4 : rbn_seg4_stmt B.
Hypothesis S5 : rbn_seg5_stmt B.
Hypothesis S6 : rbn_seg6_stmt B.
Hypothesis S7 : rbn_seg7_stmt B.
Hypothesis S8 : rbn_seg8_stmt B.
Hypothesis S9 : rbn_seg9_stmt B.
Hypothesis S10 : rbn_seg10_stmt B.
Lemma rbn_from10 : forall X W c, rbn_cx B X -> rbn_at10 B X W c -> SRr SEGS W c (rbn_post B X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
exact (S10 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs).
Qed.
Lemma rbn_from9 : forall X W c, rbn_cx B X -> rbn_at9 B X W c -> SRr SEGS W c (rbn_post B X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S9 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from10 X W2 c2 HX H2).
Qed.
Lemma rbn_from8 : forall X W c, rbn_cx B X -> rbn_at8 B X W c -> SRr SEGS W c (rbn_post B X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S8 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from9 X W2 c2 HX H2).
Qed.
Lemma rbn_from7 : forall X W c, rbn_cx B X -> rbn_at7 B X W c -> SRr SEGS W c (rbn_post B X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S7 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from8 X W2 c2 HX H2).
Qed.
Lemma rbn_from6 : forall X W c, rbn_cx B X -> rbn_at6 B X W c -> SRr SEGS W c (rbn_post B X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S6 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from7 X W2 c2 HX H2).
Qed.
Lemma rbn_from5 : forall X W c, rbn_cx B X -> rbn_at5 B X W c -> SRr SEGS W c (rbn_post B X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & P & -> & Hs).
eapply SRr_bind; [exact (S5 X pos regs1 lyc1 Sc1 W memc1 mdc1 P HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from6 X W2 c2 HX H2).
Qed.
Lemma rbn_from4 : forall X W c, rbn_cx B X -> rbn_at4 B X W c -> SRr SEGS W c (rbn_post B X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & P & -> & Hs).
eapply SRr_bind; [exact (S4 X pos regs1 lyc1 Sc1 W memc1 mdc1 P HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from5 X W2 c2 HX H2).
Qed.
Lemma rbn_from3 : forall X W c, rbn_cx B X -> rbn_at3 B X W c -> SRr SEGS W c (rbn_post B X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S3 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from4 X W2 c2 HX H2).
Qed.
Lemma rbn_from2 : forall X W c, rbn_cx B X -> rbn_at2 B X W c -> SRr SEGS W c (rbn_post B X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S2 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ [H2 | H2]; [exact (rbn_from3 X W2 c2 HX H2) | exact (rbn_from10 X W2 c2 HX H2)].
Qed.
Lemma rbn_from1 : forall X, rbn_cx B X ->
  SRr SEGS (ri_W X) (cfg_at (fx := ri_fq X) SEGS (BASE + AF_reac_box_name) (ri_regs X) (ri_memc X) (ri_mdc X))
    (rbn_post B X).
Proof.
intros X HX. eapply SRr_bind; [exact (S1 X HX)|].
intros W2 c2 _ H2. exact (rbn_from2 X W2 c2 HX H2).
Qed.
Theorem pb_reac_box_name_of_segs : treac_box_name_spec B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f said i o name name_len token token_len
  display display_len sd.
intros.
exact (rbn_from1 (RbnIn fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f said i o name name_len token
  token_len display display_len sd)
  ltac:(unfold rbn_cx, rbm_args; cbn [ri_fq ri_STK ri_sp0 ri_FP ri_ly ri_S ri_W0 ri_mem0 ri_md0 ri_own ri_lyc ri_Sc
    ri_W ri_memc ri_mdc ri_k ri_regs ri_ch ri_f ri_said ri_i ri_o ri_name ri_name_len ri_token ri_token_len
    ri_display ri_display_len ri_sd]; repeat (split; [assumption|]); assumption)).
Qed.
End h.
End f.
End d.
