(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 167 of its 196 lines of code are new or changed and 516 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacBoxName.v, with its module paths and module names changed; 111 of its 151 lines of code are new or changed and 156 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec ReacBoxName ReacBoxNameCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Definition RBN_Q3 : Z := 0x218.
Definition RBN_T3 : Z := 0x254.
Definition RBN_U3 : Z := 0x2ac.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Definition rbn3_mem0 (X : rbn_in) : word -> option byte := mrestrict (w_H (ri_W X)) (ri_memc X).
Definition rbn3_Pok (X : rbn_in) (P : Z) : Prop :=
  (ri_said X <> 0 /\ ri_sd X <> [] /\ P = ri_said X) \/
  ((ri_said X = 0 \/ ri_sd X = []) /\
   ((ri_f X = 1 /\ 0 <= P < 2 ^ 64 /\ val_mem SEGS (rbn3_mem0 X) (VAL (A_OBJ 26)) 8 P) \/
    (ri_f X = 2 /\ 0 <= P < 2 ^ 64 /\ val_mem SEGS (rbn3_mem0 X) (VAL (A_OBJ 26) + 8) 8 P) \/
    (ri_f X = 3 /\ 0 <= P < 2 ^ 64 /\ val_mem SEGS (rbn3_mem0 X) (VAL (A_OBJ 26) + 16) 8 P) \/
    (ri_f X <> 1 /\ ri_f X <> 2 /\ ri_f X <> 3 /\ P = VAL (A_OBJ 27)))).
Definition rbn3_ion (X : rbn_in) : list (Z * nat * Z) :=
  [(rbn_A X + 40, 8%nat, ri_i X); (rbn_A X + 48, 8%nat, ri_o X); (rbn_A X + 56, 8%nat, ri_name_len X)].
Section h.
Variable B : asyms.
Definition rbn3_rel (X : rbn_in) (pos : Z) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS)
  (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 mdc1 (ri_k X) /\
  frames Sc1 = (3, pos) :: frames (ri_Sc X) /\
  Permutation (ablocks B lyc1 Sc1) (ablocks B (ri_lyc X) (ri_Sc X)) /\
  rbn_kept B X W1 memc1 (fun _ => False).
Definition rbn3_stQ (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh false false false false) /\
  rbn_rbase B X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 27 = w64 (ri_f X) /\ getr regs1 21 = w64 (ri_token X) /\ getr regs1 24 = w64 (ri_name X) /\
  getr regs1 26 = w64 (ri_token_len X) /\ getr regs1 14 = w64 (ri_display X) /\
  getr regs1 15 = w64 (ri_display_len X) /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn3_ion X) /\
  (ri_said X = 0 \/ ri_sd X = []) /\ rbm_args X.
Definition rbn3_stT (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) (P : Z) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh false false false false) /\
  rbn_rbase B X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 25 = w64 P /\ getr regs1 21 = w64 (ri_token X) /\ getr regs1 24 = w64 (ri_name X) /\
  getr regs1 26 = w64 (ri_token_len X) /\ getr regs1 14 = w64 (ri_display X) /\
  getr regs1 15 = w64 (ri_display_len X) /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn3_ion X) /\
  rbn3_Pok X P /\ rbm_args X.
Definition rbn3_stU (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) (P : Z) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true false false false) /\
  rbn_rbase B X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 20 = w64 (rbn_F X pos + 32) /\ getr regs1 21 = w64 5 /\ getr regs1 25 = w64 P /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_argc X ++ rbn_rw X pos 4 0) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X) /\
  rbn3_Pok X P /\ rbm_args X.
Definition rbn3_atQ (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg X RBN_Q3 regs1 memc1 mdc1 /\ rbn3_stQ X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn3_atT (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1 P,
    c1 = rbn_cfg X RBN_T3 regs1 memc1 mdc1 /\ rbn3_stT X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P.
Definition rbn3_atU (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1 P,
    c1 = rbn_cfg X RBN_U3 regs1 memc1 mdc1 /\ rbn3_stU X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P.
Definition rbn3_said_stmt : Prop :=
  forall X pos lyc1 Sc1 W1 memc1 mdc1, rbn_cx B X -> rbm_args X -> ri_said X <> 0 ->
  rbn3_rel X pos lyc1 Sc1 W1 memc1 mdc1 ->
  rbn_str W1 memc1 (ri_said X) (ri_sd X) /\
  (forall a, ri_said X <= a < ri_said X + Z.of_nat (length (ri_sd X)) + 1 ->
     ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512)).
Definition rbn3_tab_stmt : Prop :=
  forall X pos lyc1 Sc1 W1 memc1 mdc1, rbn_cx B X -> rbm_args X ->
  rbn3_rel X pos lyc1 Sc1 W1 memc1 mdc1 ->
  range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF (VAL (A_OBJ 26)) 24 /\
  (forall j v, 0 <= j < 3 -> val_mem SEGS (rbn3_mem0 X) (VAL (A_OBJ 26) + 8 * j) 8 v ->
     val_mem SEGS (mrestrict (w_H W1) memc1) (VAL (A_OBJ 26) + 8 * j) 8 v).
Definition rbn3_stp_stmt : Prop :=
  forall X pos P lyc1 Sc1 W1 memc1 mdc1, rbn_cx B X -> rbm_args X -> rbn3_Pok X P ->
  rbn3_rel X pos lyc1 Sc1 W1 memc1 mdc1 -> rbn_stp X pos W1 memc1 P.
Definition rbn3_h1_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx B X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_P3 regs1 memc1 mdc1) (fun W2 c2 => rbn3_atQ X W2 c2 \/ rbn3_atT X W2 c2).
Definition rbn3_h2_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx B X -> rbn3_stQ X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg X RBN_Q3 regs1 memc1 mdc1) (rbn3_atT X).
Definition rbn3_t_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P, rbn_cx B X -> rbn3_stT X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  SRr SEGS W1 (rbn_cfg X RBN_T3 regs1 memc1 mdc1) (rbn3_atU X).
Definition rbn3_u_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P, rbn_cx B X -> rbn3_stU X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  SRr SEGS W1 (rbn_cfg X RBN_U3 regs1 memc1 mdc1) (rbn_at4 B X).
Lemma rbn3_rel_of_mid : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh -> rbn3_rel X pos lyc1 Sc1 W1 memc1 mdc1.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh (HJ & Hfr & Hperm & _ & HK & _).
split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hperm | exact HK].
Qed.
Section c.
Hypothesis H1 : rbn3_h1_stmt.
Hypothesis H2 : rbn3_h2_stmt.
Hypothesis HT : rbn3_t_stmt.
Hypothesis HU : rbn3_u_stmt.
Lemma rbn3_fromT : forall X W c, rbn_cx B X -> rbn3_atT X W c -> SRr SEGS W c (rbn_at4 B X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & P & -> & Hs).
eapply SRr_bind; [exact (HT X pos regs1 lyc1 Sc1 W memc1 mdc1 P HX Hs)|].
intros W2 c2 _ (pos2 & regs2 & lyc2 & Sc2 & memc2 & mdc2 & P2 & -> & Hs2).
exact (HU X pos2 regs2 lyc2 Sc2 W2 memc2 mdc2 P2 HX Hs2).
Qed.
Theorem rbn3_seg3_of_parts : rbn_seg3_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3.
eapply SRr_bind; [exact (H1 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3)|].
intros W2 c2 _ [HQ | HTT]; [|exact (rbn3_fromT X W2 c2 HX HTT)].
destruct HQ as (pos2 & regs2 & lyc2 & Sc2 & memc2 & mdc2 & -> & HsQ).
eapply SRr_bind; [exact (H2 X pos2 regs2 lyc2 Sc2 W2 memc2 mdc2 HX HsQ)|].
intros W3 c3 _ HT3. exact (rbn3_fromT X W3 c3 HX HT3).
Qed.
End c.
End h.
End f.
End d.
