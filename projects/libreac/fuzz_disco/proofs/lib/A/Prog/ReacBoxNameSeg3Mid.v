(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_checksum_verify on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlChecksumVerify.v, with its module paths and numbers changed; 66 of its 271 lines of code are new or changed and 57 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/CtrlChecksumVerify.v, with its module names changed; 36 of its 67 lines of code are new or changed and 240 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition RBN_T3 : Z := 0x254.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Definition rbn3_regs (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) : Prop :=
  getr regs1 2 = w64 (rbn_A X) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
  getr regs1 8 = w64 (rbn_SP X) /\ getr regs1 9 = w64 (rbn_A X) /\ getr regs1 19 = w64 (rbn_F X pos) /\
  getr regs1 22 = w64 SHADOW_OFF /\ getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 20 = w64 P /\ getr regs1 23 = w64 (ri_token X) /\ getr regs1 24 = w64 (ri_name X) /\
  getr regs1 27 = w64 (ri_token_len X) /\ getr regs1 12 = w64 (ri_i X) /\ getr regs1 13 = w64 (ri_o X) /\
  getr regs1 14 = w64 (ri_display X) /\ getr regs1 15 = w64 (ri_name_len X) /\
  getr regs1 16 = w64 (ri_display_len X).
Definition rbn3_pk (X : rbn_in) (pos P : Z) : Prop :=
  forall lyc1 Sc1 (W1 : world SEGS) memc1 mdc1 sh,
    rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh -> rbn_stp X pos W1 memc1 P.
Definition rbn3_mid (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos P regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg X RBN_T3 regs1 memc1 mdc1 /\
    rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh false false false false) /\
    rbn3_regs X pos P regs1 /\ 4096 <= P /\ P <= 2 ^ 47 - 2 /\
    0 <= ri_i X < 2 ^ 64 /\ 0 <= ri_o X < 2 ^ 64 /\
    val_mem SEGS (mrestrict (w_H W1) memc1) (rbn_A X + 80) 8 (ri_i X) /\
    val_mem SEGS (mrestrict (w_H W1) memc1) (rbn_A X + 88) 8 (ri_o X) /\
    rbn3_pk X pos P /\ rbm_args X.
Definition rbn3_head_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 (W1 : world SEGS) memc1 mdc1,
  rbn_cx B X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P3 regs1 memc1 mdc1) (rbn3_mid X).
Definition rbn3_tail_stmt : Prop :=
  forall X (W1 : world SEGS) c1, rbn_cx B X -> rbn3_mid X W1 c1 -> SRr SEGS W1 c1 (rbn_at4 B X).
Lemma rbn_seg3_of_parts : rbn3_head_stmt -> rbn3_tail_stmt -> rbn_seg3_stmt B.
Proof.
intros HH HT X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3.
eapply SRr_bind; [exact (HH X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3)|].
intros W2 c2 _ HM. exact (HT X W2 c2 HX HM).
Qed.
End h.
End f.
End d.
