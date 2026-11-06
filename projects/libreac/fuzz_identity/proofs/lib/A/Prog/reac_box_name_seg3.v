(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACgc.v:176-178;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACjv.v:45-51, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:154-159. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC81 YC4b YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC1g YC1h YC81 YC4b YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
IdentFrame YC85 YC81 YC4b YC45 YC1h YC1g IdentCJ sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition RBN_Q1 : Z := 0x254.
Definition RBN_Q2 : Z := 0x284.
Definition RBN_Q3 : Z := 0x294.
Definition RBN_Q4 : Z := 0x2a4.
Definition RBN_Q5 : Z := 0x2c4.
Definition RBN_Q6 : Z := 0x2d0.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition rbn3_cells1 (X : rbn_in) : list (Z * nat * Z) :=
  [(rbn_A X + 80, 8%nat, ri_i X); (rbn_A X + 88, 8%nat, ri_o X)].
Definition rbn3_cells2 (X : rbn_in) (pos n : Z) : list (Z * nat * Z) :=
  [(rbn_A X + 8, 8%nat, ri_display X); (rbn_A X + 56, 8%nat, ri_display_len X);
   (rbn_A X + 64, 8%nat, ri_name_len X); (rbn_A X + 80, 8%nat, ri_i X); (rbn_A X + 88, 8%nat, ri_o X);
   (rbn_A X + 152, 8%nat, rbn_F X pos + 32); (rbn_A X + 160, 8%nat, 5); (rbn_A X + 168, 8%nat, n);
   (rbn_A X + 176, 4%nat, 0)].
Definition rbn3_cells5 (X : rbn_in) (pos : Z) : list (Z * nat * Z) :=
  (rbn_A X + 32, 8%nat, ri_token_len X) :: rbn3_cells2 X pos 4.
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Definition rbn3_src (X : rbn_in) (P : Z) : Prop :=
  (ri_said X <> 0 /\ ri_sd X <> [] /\ P = ri_said X) \/
  ((ri_said X = 0 \/ ri_sd X = []) /\ rbn_imgstr B G (ri_W X) (ri_memc X) P (rbm_stem X)).
Definition rbn3_core (X : rbn_in) (pos P : Z) (sh : list Z) (cells : list (Z * nat * Z))
  (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS) (memc1 : word -> option byte)
  (mdc1 : Model) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh /\ rbn_rbase B X pos regs1 /\
  getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\ getr regs1 20 = w64 P /\
  getr regs1 23 = w64 (ri_token X) /\ getr regs1 24 = w64 (ri_name X) /\
  getr regs1 27 = w64 (ri_token_len X) /\
  rbn_cells (mrestrict (w_H W1) memc1) cells /\ rbm_args X /\ rbn3_src X P.
Definition rbn3_s1 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn3_core X pos P (rbn_sh false false false false) (rbn3_cells1 X) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 12 = w64 (ri_i X) /\ getr regs1 13 = w64 (ri_o X) /\ getr regs1 14 = w64 (ri_display X) /\
  getr regs1 15 = w64 (ri_name_len X) /\ getr regs1 16 = w64 (ri_display_len X).
Definition rbn3_s2 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn3_core X pos P (rbn_sh true false false false) (rbn3_cells2 X pos 0) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 25 = w64 (rbn_F X pos + 32).
Definition rbn3_s3 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn3_core X pos P (rbn_sh true false false false) (rbn3_cells2 X pos 2) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 25 = w64 (rbn_F X pos + 32) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (bn_dec (ri_i X) 2).
Definition rbn3_s4 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn3_core X pos P (rbn_sh true false false false) (rbn3_cells2 X pos 4) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 25 = w64 (rbn_F X pos + 32) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X).
Definition rbn3_s5 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn3_core X pos P (rbn_sh true false false false) (rbn3_cells5 X pos) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 25 = w64 (rbn_F X pos + 32) /\ getr regs1 12 = w64 4 /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X ++ [0]).
Definition rbn3_s6 (X : rbn_in) (pos P : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn3_core X pos P (rbn_sh true true false false) (rbn3_cells5 X pos) regs1 lyc1 Sc1 W1 memc1 mdc1 /\
  getr regs1 25 = w64 (rbn_F X pos + 32) /\ getr regs1 12 = w64 4 /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X ++ [0]).
Definition rbn3_at1 (X : rbn_in) (pos : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists P regs2 lyc2 Sc2 memc2 mdc2,
    c2 = rbn_cfg RBN_Q1 regs2 memc2 mdc2 /\ rbn3_s1 X pos P regs2 lyc2 Sc2 W2 memc2 mdc2.
Definition rbn3_at2 (X : rbn_in) (pos P : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists regs2 lyc2 Sc2 memc2 mdc2,
    c2 = rbn_cfg RBN_Q2 regs2 memc2 mdc2 /\ rbn3_s2 X pos P regs2 lyc2 Sc2 W2 memc2 mdc2.
Definition rbn3_at3 (X : rbn_in) (pos P : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists regs2 lyc2 Sc2 memc2 mdc2,
    c2 = rbn_cfg RBN_Q3 regs2 memc2 mdc2 /\ rbn3_s3 X pos P regs2 lyc2 Sc2 W2 memc2 mdc2.
Definition rbn3_at4 (X : rbn_in) (pos P : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists regs2 lyc2 Sc2 memc2 mdc2,
    c2 = rbn_cfg RBN_Q4 regs2 memc2 mdc2 /\ rbn3_s4 X pos P regs2 lyc2 Sc2 W2 memc2 mdc2.
Definition rbn3_at5 (X : rbn_in) (pos P : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists regs2 lyc2 Sc2 memc2 mdc2,
    c2 = rbn_cfg RBN_Q5 regs2 memc2 mdc2 /\ rbn3_s5 X pos P regs2 lyc2 Sc2 W2 memc2 mdc2.
Definition rbn3_at6 (X : rbn_in) (pos P : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists regs2 lyc2 Sc2 memc2 mdc2,
    c2 = rbn_cfg RBN_Q6 regs2 memc2 mdc2 /\ rbn3_s6 X pos P regs2 lyc2 Sc2 W2 memc2 mdc2.
Definition rbn3_T1_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx B G X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_P3 regs1 memc1 mdc1) (rbn3_at1 X pos).
Definition rbn3_MS_stmt : Prop :=
  forall X pos P regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx B G X -> rbn3_s1 X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_Q1 regs1 memc1 mdc1) (rbn3_at2 X pos P).
Definition rbn3_D1_stmt : Prop :=
  forall X pos P regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx B G X -> rbn3_s2 X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_Q2 regs1 memc1 mdc1) (rbn3_at3 X pos P).
Definition rbn3_D2_stmt : Prop :=
  forall X pos P regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx B G X -> rbn3_s3 X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_Q3 regs1 memc1 mdc1) (rbn3_at4 X pos P).
Definition rbn3_T2_stmt : Prop :=
  forall X pos P regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx B G X -> rbn3_s4 X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_Q4 regs1 memc1 mdc1) (rbn3_at5 X pos P).
Definition rbn3_P4_stmt : Prop :=
  forall X pos P regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx B G X -> rbn3_s5 X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_Q5 regs1 memc1 mdc1) (rbn3_at6 X pos P).
Definition rbn3_T3_stmt : Prop :=
  forall X pos P regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx B G X -> rbn3_s6 X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_Q6 regs1 memc1 mdc1) (rbn_at4 B X).
Definition rbn3_geo_stmt : Prop :=
  forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  alloc_ceiling + REAC_BOX_NAME_STK <= rbn_SP X /\ rbn_SP X <= 2 ^ 47 /\ rbn_SP X mod 16 = 0 /\
  rbn_SP X - 320 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\ rbn_A X mod 32 = 0 /\
  ly_stk_lo lyc1 <= rbn_SP X - REAC_BOX_NAME_STK /\ rbn_SP X <= ly_stk_hi lyc1 /\
  (forall a, rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X -> apresent (w_H W1) memc1 a) /\
  frames Sc1 = (3, pos) :: frames (ri_Sc X) /\ Z.of_nat (length (frames Sc1)) <= 8 /\
  (forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p) /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 ->
     apresent (w_H W1) memc1 a /\ ~ in_img SEGS a /\ ~ aowned B lyc1 Sc1 a) /\
  rbn_SH X pos = SHADOW_OFF + rbn_F X pos / 8 /\
  (forall i, 0 <= i < 64 -> apresent (w_H W1) memc1 (rbn_SH X pos + i) /\ ~ aowned B lyc1 Sc1 (rbn_SH X pos + i)).
Definition rbn3_mid_upd_stmt : Prop :=
  forall X pos lyc1 Sc1 W1 memc1 mdc1 sh lyc2 Sc2 memc2 mdc2 sh2,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc2 Sc2 W1 memc2 mdc2 0 ->
  Permutation (ablocks B lyc2 Sc2) (ablocks B lyc1 Sc1) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W1) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall a, rbn_inblk B X a -> aview SEGS (w_H W1) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall a, rbn_SP X - 104 <= a < rbn_SP X -> aview SEGS (w_H W1) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall a, rbn_F X pos + 504 <= a < rbn_F X pos + 512 ->
     aview SEGS (w_H W1) memc2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_shadow_at W1 memc2 (rbn_SH X pos) sh2 ->
  rbn_mid B X pos lyc2 Sc2 W1 memc2 mdc2 (fun _ => False) sh2.
Definition rbn3_said_stmt : Prop :=
  forall X pos lyc1 Sc1 W1 memc1 mdc1 sh,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh -> rbm_args X -> ri_said X <> 0 ->
  rbn_cstr W1 memc1 (ri_said X) (ri_sd X) /\
  (forall a, ri_said X <= a < ri_said X + Z.of_nat (length (ri_sd X)) + 8 ->
     ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512)).
Definition rbn3_img_stmt : Prop :=
  forall X pos lyc1 Sc1 W1 memc1 mdc1 sh,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh -> rbm_args X ->
  (forall a, rbn_fixed B a 1 -> aview SEGS (w_H W1) memc1 a = aview SEGS (w_H (ri_W X)) (ri_memc X) a) /\
  range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF (VAL (A_OBJ 21)) 24 /\
  (forall a s, rbn_imgstr B G (ri_W X) (ri_memc X) a s ->
     rbn_cstr W1 memc1 a s /\
     (forall x, a <= x < a + Z.of_nat (length s) + 1 ->
        ~ (rbn_SP X - REAC_BOX_NAME_STK <= x < rbn_SP X) /\ ~ (rbn_F X pos <= x < rbn_F X pos + 512))).
Definition rbn3_stp_stmt : Prop :=
  forall X pos P lyc1 Sc1 W1 memc1 mdc1 sh,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh -> rbm_args X -> rbn3_src X P ->
  rbn_stp X pos W1 memc1 P.
Lemma rbn3_compose :
  rbn3_T1_stmt -> rbn3_MS_stmt -> rbn3_D1_stmt -> rbn3_D2_stmt -> rbn3_T2_stmt -> rbn3_P4_stmt -> rbn3_T3_stmt ->
  rbn_seg3_stmt B G.
Proof.
intros T1 MS D1 D2 T2 P4 T3 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3.
eapply SRr_bind; [exact (T1 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3)|].
intros W2 c2 _ (P & r2 & l2 & S2 & m2 & d2 & -> & H2).
eapply SRr_bind; [exact (MS X pos P r2 l2 S2 W2 m2 d2 HX H2)|].
intros W3 c3 _ (r3 & l3 & S3 & m3 & d3 & -> & H3').
eapply SRr_bind; [exact (D1 X pos P r3 l3 S3 W3 m3 d3 HX H3')|].
intros W4 c4 _ (r4 & l4 & S4 & m4 & d4 & -> & H4).
eapply SRr_bind; [exact (D2 X pos P r4 l4 S4 W4 m4 d4 HX H4)|].
intros W5 c5 _ (r5 & l5 & S5 & m5 & d5 & -> & H5).
eapply SRr_bind; [exact (T2 X pos P r5 l5 S5 W5 m5 d5 HX H5)|].
intros W6 c6 _ (r6 & l6 & S6 & m6 & d6 & -> & H6).
eapply SRr_bind; [exact (P4 X pos P r6 l6 S6 W6 m6 d6 HX H6)|].
intros W7 c7 _ (r7 & l7 & S7 & m7 & d7 & -> & H7).
exact (T3 X pos P r7 l7 S7 W7 m7 d7 HX H7).
Qed.
End h.
End f.
End d.
Lemma rbn3b_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn3b_stem_oth : forall f, ~ (1 <= f <= 3) -> bn_STEM f = bn_STEM 0.
Proof.
intros f Hf. unfold bn_STEM.
destruct (Z.eqb_spec f 1); [lia|]. destruct (Z.eqb_spec f 2); [lia|]. destruct (Z.eqb_spec f 3); [lia|].
reflexivity.
Qed.
Definition rbn3b_keep : list (bv 5) := [2; 3; 4; 8; 9; 12; 13; 14; 15; 16; 18; 19; 22; 23; 24; 26; 27]%bv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition rbn3e_FX (l : list (nat * afact)) : facts :=
  mkFacts ([(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SB SB 0);
            (19%nat, mkAF 4096 140737479966720 5); (18%nat, mkAF SB (SB + 17592184995840) 2)] ++ l) [] [].
Definition rbn3e_rs2 : smem :=
  [YP09.mkRegion (Some 9%nat) 8 184 32 40 [YP09.mkChunk 168 (CVal 8 (SLit 4))];
   YP09.mkRegion (Some 19%nat) 32 37 36 37 []].
Definition rbn3e_ss2 : sstate :=
  mkSS (AF_reac_box_name + RBN_Q4) (sr_set sr_atoms 25%bv (SOff 19 32)) rbn3e_rs2 None (rbn3e_FX []).
Definition rbn3e_SH2 : list shent := [mkSHE 19 37 36].
Definition rbn3e_rs3 : smem :=
  [YP09.mkRegion (Some 9%nat) 16 24 16 24 [];
   YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]].
Definition rbn3e_ss3 : sstate :=
  mkSS (AF_reac_box_name + RBN_Q6) sr_atoms rbn3e_rs3 None
    (rbn3e_FX [(20%nat, mkAF 1 (2 ^ 47 - 10) 0); (32%nat, mkAF 1 255 0)]).
Definition rbn3e_Bx : sv := SOff 22 0.
Definition rbn3e_keep2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 26; 27]%bv.
Definition rbn3e_keep3 : list (bv 5) := [2; 3; 4; 8; 9; 12; 18; 19; 20; 22; 23; 25; 26]%bv.
Ltac rbn3e_in := cbn [In rbn3e_keep2 rbn3e_keep3]; repeat (first [left; reflexivity | right]).
Lemma rbn3e_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Lemma rbn3a_rom_vis : forall (H : word -> bool) (m : word -> option byte) x,
  seg_rom SEGS (Z_to_bv 64 x) <> None -> aview SEGS H m x <> None.
Proof.
intros H m x Hr E. apply Hr. unfold aview, mbyte, mrestrict in E.
destruct (seg_rom SEGS (Z_to_bv 64 x)) as [b|]; [|reflexivity]. exfalso.
destruct (H (Z_to_bv 64 x)); [cbn in E; discriminate E|].
destruct (m (Z_to_bv 64 x)); cbn in E; discriminate E.
Qed.
Lemma rbn3a_nz : forall X, rbm_args X -> ri_name X <> 0 /\ ri_token X <> 0 /\ ri_display X <> 0.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
do 6 (apply andb_prop in HA as [HA _]).
apply andb_prop in HA as [HA Hd]. apply andb_prop in HA as [Hn Ht].
apply negb_true_iff, Z.eqb_neq in Hn. apply negb_true_iff, Z.eqb_neq in Ht.
apply negb_true_iff, Z.eqb_neq in Hd.
split; [exact Hn|]. split; [exact Ht | exact Hd].
Qed.
Lemma rbn3a_fp_cases : forall X a, rbm_args X -> inFP (rbn_FPX X) a ->
  (ri_name X <= a < ri_name X + Z.min (ri_name_len X) 24) \/
  (ri_token X <= a < ri_token X + Z.min (ri_token_len X) 24) \/
  (ri_display X <= a < ri_display X + Z.min (ri_display_len X) 48).
Proof.
intros X a HA (r & Hr & Ha).
destruct (rbn3a_nz X HA) as (N1 & N2 & N3).
unfold rbn_FPX, rbn_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
rewrite ?(proj2 (Z.eqb_neq _ _) N1), ?(proj2 (Z.eqb_neq _ _) N2), ?(proj2 (Z.eqb_neq _ _) N3) in Ha;
[left | right; left | right; right]; exact Ha.
Qed.
Lemma rbn3a_nso : forall X, rbm_args X -> 0 <= ri_name X -> 0 <= ri_token X -> 0 <= ri_display X ->
  ~ YI16.sink_open_fp (rbn_FPX X).
Proof.
intros X HA H1 H2 H3 (r & Hr & Hlo).
destruct (rbn3a_nz X HA) as (N1 & N2 & N3).
destruct (rbn3a_fp_cases X 0 HA (ex_intro _ r (conj Hr Hlo))) as [E | [E | E]]; lia.
Qed.
Lemma rbn3a_hull_cov : forall a n x, 0 <= n -> a <= x < a + n + 1 ->
  shadow_addr a / 8 * 8 <= SHADOW_OFF + x / 8 < shadow_addr (a + n) / 8 * 8 + 8.
Proof.
intros a n x Hn Hx. unfold shadow_addr.
assert (L1 : a / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (L2 : x / 8 <= (a + n) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (a + n) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n) / 8) 8 ltac:(lia)) as M2.
clear - L1 L2 D1 M1 D2 M2. lia.
Qed.
Lemma rbn3a_hull_in : forall fa nb a n y, fa mod 64 = 0 -> nb mod 64 = 0 -> 0 <= fa -> fa <= a ->
  a + n < fa + nb -> 0 <= n ->
  shadow_addr a / 8 * 8 <= y < shadow_addr (a + n) / 8 * 8 + 8 ->
  shadow_addr fa <= y < shadow_addr fa + nb / 8.
Proof.
intros fa nb a n y H1 H2 H0 H3 H4 H5 Hy.
pose proof (Z.div_mod fa 64 ltac:(lia)) as D1. rewrite H1, Z.add_0_r in D1.
pose proof (Z.div_mod nb 64 ltac:(lia)) as D2. rewrite H2, Z.add_0_r in D2.
set (f := fa / 64) in D1. set (g := nb / 64) in D2. clearbody f g. subst fa nb.
unfold shadow_addr in *.
assert (E1 : 64 * f / 8 = 8 * f) by (replace (64 * f) with (8 * f * 8) by lia; apply Z.div_mul; lia).
assert (E2 : 64 * g / 8 = 8 * g) by (replace (64 * g) with (8 * g * 8) by lia; apply Z.div_mul; lia).
rewrite E1, E2.
assert (L1 : 8 * f <= a / 8) by (apply Z.div_le_lower_bound; lia).
assert (L2 : (a + n) / 8 < 8 * f + 8 * g) by (apply Z.div_lt_upper_bound; lia).
assert (ES : SHADOW_OFF = 8 * 268431360) by reflexivity.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (SHADOW_OFF + (a + n) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n) / 8) 8 ltac:(lia)) as M4.
clear - Hy L1 L2 ES D3 M3 D4 M4. lia.
Qed.
Lemma rbn3a_cstr_kept : forall (W : world SEGS) (m m' : word -> option byte) a s,
  rbn_cstr W m a s ->
  (forall x, a <= x < a + Z.of_nat (length s) + 8 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  (forall y, shadow_addr a / 8 * 8 <= y < shadow_addr (a + Z.of_nat (length s)) / 8 * 8 + 8 ->
     aview SEGS (w_H W) m' y = aview SEGS (w_H W) m y) ->
  rbn_cstr W m' a s.
Proof.
intros W m m' a s (Hf & Hl & Ha0 & Ham & Hg & Hra & Hhv & Htl) HB HS.
split; [exact Hf|]. split; [exact Hl|]. split; [exact Ha0|]. split; [exact Ham|].
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact Hg|]. intros x Hx.
  rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HB. clear - Hx. lia. }
split.
{ intros x Hx. destruct (Hra x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
  rewrite (HS (shadow_of_addr SHADOW_OFF x)); [exact Hs|].
  exact (rbn3a_hull_cov a (Z.of_nat (length s)) x ltac:(lia) ltac:(lia)). }
split.
{ intros y Hy. rewrite (HS y); [exact (Hhv y Hy)|].
  replace (a + Z.of_nat (length s)) with (a + (Z.of_nat (length s) + 1) - 1) by lia. exact Hy. }
intros x Hx. pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M.
rewrite (HB x) by (clear - Hx M; lia). exact (Htl x Hx).
Qed.
Definition rbn3b_stk : YP09.region := YP09.mkRegion (Some 9%nat) 8 184 8 184 [].
Definition rbn3b_tbl : YP09.region := YP09.mkRegion (Some (A_OBJ 21)) 0 24 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition rbn3b_sdr (v : sv) : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 v)].
Definition rbn3b_fb : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SB SB 0);
   (A_OBJ 21, mkAF IMG_LO (IMG_TOP - 24) 3)].
Definition rbn3b_ssS (v : sv) : sstate :=
  mkSS (AF_reac_box_name + RBN_P3) sr_atoms [rbn3b_stk; rbn3b_tbl; rbn3b_sdr v] None
    (mkFacts (rbn3b_fb ++ [(20%nat, mkAF 4096 140737479966720 0); (35%nat, mkAF 1 255 0)]) [] []).
Definition rbn3b_ss0 : sstate :=
  mkSS (AF_reac_box_name + RBN_P3) (sr_set sr_atoms 20%bv (SLit 0)) [rbn3b_stk; rbn3b_tbl] None
    (mkFacts rbn3b_fb [] []).
Definition rbn3b_Bx : sv := SOff 22 0.
Definition rbn3b_SH : list shent := [mkSHE (A_OBJ 21) 0 24].
Definition rbn3b_E (regs : bvmap 5 word) (t1 t2 t3 c : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [t1; t2; t3; c])).
Lemma rbn3b_ew : forall regs t1 t2 t3 c,
  ew (rbn3b_E regs t1 t2 t3 c) 32 = Z_to_bv 64 t1 /\ ew (rbn3b_E regs t1 t2 t3 c) 33 = Z_to_bv 64 t2 /\
  ew (rbn3b_E regs t1 t2 t3 c) 34 = Z_to_bv 64 t3 /\ ew (rbn3b_E regs t1 t2 t3 c) 35 = Z_to_bv 64 c /\
  (forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (rbn3b_E regs t1 t2 t3 c) k = getr regs r) /\
  ew (rbn3b_E regs t1 t2 t3 c) (A_OBJ 21) = Z_to_bv 64 (VAL (A_OBJ 21)) /\
  ew (rbn3b_E regs t1 t2 t3 c) 259%nat = Z_to_bv 64 (VAL (A_OBJ 18)).
Proof.
intros regs t1 t2 t3 c. unfold rbn3b_E.
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)|].
split; [intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk|].
split; [apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia|].
exact (Eimg_img _ 259%nat ltac:(unfold A_TEXT, A_LIM; lia)).
Qed.
Lemma rbn3b_den35 : forall regs t1 t2 t3 c, sv_denot (rbn3b_E regs t1 t2 t3 c) (SOff 35 0) = Z_to_bv 64 c.
Proof.
intros regs t1 t2 t3 c. cbn [sv_denot].
rewrite (proj1 (proj2 (proj2 (proj2 (rbn3b_ew regs t1 t2 t3 c))))), Z.add_0_r, Z_to_bv_bv_unsigned.
reflexivity.
Qed.
Lemma rbn3b_vm_unmod : forall (m : word -> option byte) a v, val_mem SEGS m a 8 (v mod 2 ^ 64) -> val_mem SEGS m a 8 v.
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte.
assert (P : 2 ^ (8 * Z.of_nat 8) = 2 ^ 64) by reflexivity. rewrite !P.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rbn3b_cells : forall E (m : word -> option byte) A i o cs,
  region_ok SEGS E m (YP09.mkRegion (Some 9%nat) 8 184 8 184 cs) -> bv_unsigned (ew E 9) = A ->
  In (YP09.mkChunk 80 (CVal 8 (SOff 12 0))) cs -> In (YP09.mkChunk 88 (CVal 8 (SOff 13 0))) cs ->
  ew E 12 = Z_to_bv 64 i -> ew E 13 = Z_to_bv 64 o ->
  val_mem SEGS m (A + 80) 8 i /\ val_mem SEGS m (A + 88) 8 o.
Proof.
intros E m A i o cs HR HA H80 H88 E12 E13.
assert (W : forall n v, ew E n = Z_to_bv 64 v ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ (8 * Z.of_N 8) = v mod 2 ^ 64).
{ intros n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned, Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
  apply Z.mod_mod. lia. }
split.
- pose proof (field_of_region_any E m 9%nat A cs 8 184 8 184 80 8%N (SOff 12 0) HR HA H80 ltac:(cbn; lia)) as V.
  rewrite (W 12%nat i E12) in V. change (N.to_nat 8) with 8%nat in V. exact (rbn3b_vm_unmod m _ i V).
- pose proof (field_of_region_any E m 9%nat A cs 8 184 8 184 88 8%N (SOff 13 0) HR HA H88 ltac:(cbn; lia)) as V.
  rewrite (W 13%nat o E13) in V. change (N.to_nat 8) with 8%nat in V. exact (rbn3b_vm_unmod m _ o V).
Qed.
Lemma rbn3b_kept : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply (aview_eq_of SEGS). apply HF.
rewrite unsigned_lit_small by lia. intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn3b_bltu_other : forall E f, ew E 25 = Z_to_bv 64 f -> - 2 ^ 31 <= f < 2 ^ 31 -> ~ (1 <= f <= 3) ->
  branch_taken BC_LTU (sv_denot E (SLit 2)) (sv_denot E (SAluw ALU_ADD (SOff 25 0) (SLit (-1)))) = true.
Proof.
intros E f H Hf Hn. rewrite branch_ltu_U, U_SLit, U_of_S, S_SAluw, U_SOff, U_SLit, H, Z.add_0_r, Z_to_bv_unsigned.
cbn [zalu_raw]. apply Z.ltb_lt.
assert (A1 : zcanon (bv_wrap 64 f) mod 2 ^ 32 = f mod 2 ^ 32).
{ unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia.
  Z.div_mod_to_equations; lia. }
replace (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1) by reflexivity.
replace (zcanon 2) with 2 by reflexivity.
rewrite A1. unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
destruct (Z_lt_le_dec f 1); Z.div_mod_to_equations; lia.
Qed.
Lemma rbn3b_rok_stk : forall E (W : world SEGS) (m : word -> option byte) A,
  ew E 9 = Z_to_bv 64 A -> 0 <= A -> A + 184 <= 2 ^ 64 ->
  (forall o, 8 <= o < 184 -> apresent (w_H W) m (A + o)) ->
  region_ok SEGS E (mrestrict (w_H W) m) rbn3b_stk.
Proof.
intros E W m A E9 HA0 HA1 PA. unfold region_ok, rbn3b_stk.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply PA. lia.
Qed.
Lemma rbn3b_rok_tbl : forall E (W : world SEGS) (m : word -> option byte) T t1 t2 t3,
  ew E (A_OBJ 21) = Z_to_bv 64 T -> ew E 32 = Z_to_bv 64 t1 -> ew E 33 = Z_to_bv 64 t2 ->
  ew E 34 = Z_to_bv 64 t3 -> 0 <= T -> T + 24 <= 2 ^ 64 ->
  0 <= t1 < 2 ^ 64 -> 0 <= t2 < 2 ^ 64 -> 0 <= t3 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m) T 8 t1 -> val_mem SEGS (mrestrict (w_H W) m) (T + 8) 8 t2 ->
  val_mem SEGS (mrestrict (w_H W) m) (T + 16) 8 t3 ->
  region_ok SEGS E (mrestrict (w_H W) m) rbn3b_tbl.
Proof.
intros E W m T t1 t2 t3 ET E32 E33 E34 HT0 HT1 R1 R2 R3 V1 V2 V3. unfold region_ok, rbn3b_tbl.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite ET, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
- apply (chunk_ok_val SEGS E _ T 0 8 (SOff 32 0) t1);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact V1.
- apply (chunk_ok_val SEGS E _ T 8 8 (SOff 33 0) t2);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V2].
- apply (chunk_ok_val SEGS E _ T 16 8 (SOff 34 0) t3);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V3].
Qed.
Lemma rbn3b_rok_sdr : forall E (W : world SEGS) (m : word -> option byte) said v cv,
  ew E 20 = Z_to_bv 64 said -> 0 <= said -> said + 1 <= 2 ^ 64 -> sv_denot E v = Z_to_bv 64 cv -> 0 <= cv < 256 ->
  val_mem SEGS (mrestrict (w_H W) m) said 1 cv -> region_ok SEGS E (mrestrict (w_H W) m) (rbn3b_sdr v).
Proof.
intros E W m said v cv E20 HS0 HS1 Hv Hcv Vc. unfold region_ok, rbn3b_sdr.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E20, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ said 0 1 v cv); [exact Hv | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Vc.
Qed.
Lemma rbn3b_entryS : forall (W : world SEGS) (regs : bvmap 5 word) memc A said t1 t2 t3 c v cv,
  getr regs 2 = w64 A -> getr regs 9 = w64 A -> getr regs 22 = w64 SHADOW_OFF -> getr regs 20 = w64 said ->
  2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> A mod 32 = 0 ->
  (forall o, 8 <= o < 184 -> apresent (w_H W) memc (A + o)) ->
  VAL (A_OBJ 21) mod 8 = 0 -> IMG_LO <= VAL (A_OBJ 21) -> VAL (A_OBJ 21) + 24 <= IMG_TOP ->
  0 <= t1 < 2 ^ 64 -> 0 <= t2 < 2 ^ 64 -> 0 <= t3 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 21)) 8 t1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 21) + 8) 8 t2 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 21) + 16) 8 t3 ->
  4096 <= said <= 140737479966720 -> (said + 1 <= VAL (A_OBJ 21) \/ VAL (A_OBJ 21) + 24 <= said) ->
  said + 1 <= A + 8 -> 1 <= c <= 255 ->
  sv_denot (rbn3b_E regs t1 t2 t3 c) v = Z_to_bv 64 cv -> 0 <= cv < 256 ->
  val_mem SEGS (mrestrict (w_H W) memc) said 1 cv ->
  st_ok_pi SEGS VAL (rbn3b_E regs t1 t2 t3 c) (rbn3b_ssS v)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P3))) memc (seg_rom SEGS))).
Proof.
intros W regs memc A said t1 t2 t3 c v cv R2 R9 R22 R20 HA1 HA2 HA3 PA HT0 HT1 HT2 Q1 Q2 Q3 V1 V2 V3
  HS1 HS2 HS3 Hc Hv Hcv Vc.
rewrite restrict_mkst_fx.
destruct (rbn3b_ew regs t1 t2 t3 c) as (E32 & E33 & E34 & E35 & EE & ET & _).
assert (HR : regs_ok (rbn3b_E regs t1 t2 t3 c) sr_atoms regs) by (unfold rbn3b_E; apply regs_ok_Eimg_Ereg).
set (E := rbn3b_E regs t1 t2 t3 c) in *.
assert (E2 : ew E 2 = Z_to_bv 64 A) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E20 : ew E 20 = Z_to_bv 64 said) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
unfold rbn3b_ssS. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + exact (rbn3b_rok_stk E W memc A E9 ltac:(lia) ltac:(lia) PA).
  + exact (rbn3b_rok_tbl E W memc (VAL (A_OBJ 21)) t1 t2 t3 ET E32 E33 E34 ltac:(lia) ltac:(lia) Q1 Q2 Q3 V1 V2 V3).
  + exact (rbn3b_rok_sdr E W memc said v cv E20 ltac:(lia) ltac:(lia) Hv Hcv Vc).
- apply pairwise_disjoint_of_extents. unfold rbn3b_stk, rbn3b_tbl, rbn3b_sdr, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, ET, E20, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
  cbn [f_atoms]. unfold rbn3b_fb. cbn [app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E9, E22, ET, E20, E35, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, SHADOW_OFF. repeat split; lia.
Qed.
Lemma rbn3b_entry0 : forall (W : world SEGS) (regs : bvmap 5 word) memc A t1 t2 t3 c,
  getr regs 2 = w64 A -> getr regs 9 = w64 A -> getr regs 22 = w64 SHADOW_OFF -> getr regs 20 = w64 0 ->
  2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> A mod 32 = 0 ->
  (forall o, 8 <= o < 184 -> apresent (w_H W) memc (A + o)) ->
  VAL (A_OBJ 21) mod 8 = 0 -> IMG_LO <= VAL (A_OBJ 21) -> VAL (A_OBJ 21) + 24 <= IMG_TOP ->
  0 <= t1 < 2 ^ 64 -> 0 <= t2 < 2 ^ 64 -> 0 <= t3 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 21)) 8 t1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 21) + 8) 8 t2 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 21) + 16) 8 t3 ->
  st_ok_pi SEGS VAL (rbn3b_E regs t1 t2 t3 c) rbn3b_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_P3))) memc (seg_rom SEGS))).
Proof.
intros W regs memc A t1 t2 t3 c R2 R9 R22 R20 HA1 HA2 HA3 PA HT0 HT1 HT2 Q1 Q2 Q3 V1 V2 V3.
rewrite restrict_mkst_fx.
destruct (rbn3b_ew regs t1 t2 t3 c) as (E32 & E33 & E34 & E35 & EE & ET & _).
assert (HR : regs_ok (rbn3b_E regs t1 t2 t3 c) (sr_set sr_atoms 20%bv (SLit 0)) regs)
  by (apply regs_ok_pin; [unfold rbn3b_E; apply regs_ok_Eimg_Ereg | discriminate | cbn [sv_denot]; exact R20]).
set (E := rbn3b_E regs t1 t2 t3 c) in *.
assert (E2 : ew E 2 = Z_to_bv 64 A) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
unfold rbn3b_ss0. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + exact (rbn3b_rok_stk E W memc A E9 ltac:(lia) ltac:(lia) PA).
  + exact (rbn3b_rok_tbl E W memc (VAL (A_OBJ 21)) t1 t2 t3 ET E32 E33 E34 ltac:(lia) ltac:(lia) Q1 Q2 Q3 V1 V2 V3).
- apply pairwise_disjoint_of_extents. unfold rbn3b_stk, rbn3b_tbl, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, ET, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
  cbn [f_atoms]. unfold rbn3b_fb. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E9, E22, ET, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, SHADOW_OFF. repeat split; lia.
Qed.
Lemma rbn3b_shok : forall E (W : world SEGS) memc,
  img_env VAL A_LIM E -> ew E 22 = Z_to_bv 64 SHADOW_OFF ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ 21)) 24 ->
  IMG_LO <= VAL (A_OBJ 21) -> VAL (A_OBJ 21) + 24 <= IMG_TOP ->
  sh_ok SEGS rbn3b_Bx rbn3b_SH E (mrestrict (w_H W) memc).
Proof.
intros E W memc HEI E22 HRA HT1 HT2. unfold sh_ok, rbn3b_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) memc E rbn3b_Bx (A_OBJ 21) (VAL (A_OBJ 21)) 24 (VAL (A_OBJ 21)) 0 24 HRA).
- unfold rbn3b_Bx. apply U_atom; [exact E22 | unfold SHADOW_OFF; lia].
- exact (U_img_atom E HEI (A_OBJ 21) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
- lia.
- lia.
- intros x Hx. unfold SHADOW_OFF. lia.
Qed.
Ltac rbn3b_awr U9s HD1 HD2 :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  eapply awr_ok_cons_stack_off;
  [ reflexivity | cbn [ew ewset Nat.eqb]; exact U9s | cbn [YP09.r_wlo]; exact HD1 | cbn [YP09.r_whi]; exact HD2 | ];
  repeat (apply awr_ok_cons_ro; [vm_compute; congruence |]); apply awr_ok_nil.
Ltac rbn3b_win U9 :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros a (r & Hr & Hw);
  cbn [ss_mem rbn3b_ssS rbn3b_ss0 add_cond In] in Hr;
  repeat destruct Hr as [<- | Hr]; try destruct Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi rbn3b_stk rbn3b_tbl rbn3b_sdr base_val ew ewset Nat.eqb] in Hw;
  rewrite ?U9 in Hw; first [exact Hw | exfalso; clear - Hw; lia].
Ltac rbn3b_inl := cbn [In rbn3b_keep]; repeat (first [left; reflexivity | right]).
Ltac rbn3b_pin25 k R :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
    let HP := fresh "HP" in
    pose proof (st_ok_pi_pin_reg' Ex ss0 ms0 (25%bv : bv 5) k HS ltac:(cbn [ms_regs restrict mkst]; exact R) eq_refl)
      as HP;
    clear HS; rename HP into HS;
    lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ => let ss2 := eval vm_compute in ss1 in change ss1 with ss2 in HS end
  end.
Ltac rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2 obl :=
  paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_Q1);
  [ first [ rbn3b_awr U9s HD1 HD2 | obl ] .. | idtac ].
Ltac rbn3b_kfr U9 X K :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    pose proof (rbn3b_kept _ _ _ m0 m1 (fun a => rbn_A X + 8 <= a < rbn_A X + 184) HFr ltac:(rbn3b_win U9)) as K
  end;
  lazymatch goal with
  | HF : frame_of _ _ _ _, HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ => clear HF HFr HG
  end.
Lemma rbn3c_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn3c_sh_w4 : forall j, j <> 4%nat ->
  nth j (rbn_sh true false false false) 0 = nth j (rbn_sh false false false false) 0.
Proof. intros j Hj. do 5 (destruct j as [|j]; [try reflexivity; lia|]). reflexivity. Qed.
Lemma rbn3c_sh_nb : forall j, (j < 8 \/ 11 <= j)%nat ->
  nth j (rbn_sh true true false false) 0 = nth j (rbn_sh true false false false) 0.
Proof. intros j Hj. do 11 (destruct j as [|j]; [try reflexivity; lia|]). reflexivity. Qed.
Lemma rbn3c_sh_nb0 : forall j, (8 <= j < 11)%nat -> nth j (rbn_sh true true false false) 0 = 0.
Proof. intros j Hj. do 11 (destruct j as [|j]; [try reflexivity; lia|]). lia. Qed.
Lemma rbn3c_oks : forall X, rbm_args X -> bn_ok (ri_i X) = true /\ bn_ok (ri_o X) = true.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
split; [exact Hi | exact Ho].
Qed.
Lemma rbn3c_ok_rng : forall x, bn_ok x = true -> 0 <= x <= 40.
Proof.
intros x Hx. unfold bn_ok in Hx. apply orb_true_iff in Hx. destruct Hx as [Hx | Hx].
- apply Z.eqb_eq in Hx. lia.
- apply andb_prop in Hx as [Hx _]. apply andb_prop in Hx as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma rbn3c_pres : forall (regs regs2 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. specialize (HP _ Hr). rewrite !Z_to_bv_bv_unsigned in HP. exact HP. Qed.
Lemma rbn3c_csl : forall r : bv 5,
  existsb (Z.eqb (bv_unsigned r)) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true ->
  acallee_saved (bv_unsigned r).
Proof.
intros r H. apply existsb_exists in H as (x & Hx & He). apply Z.eqb_eq in He.
unfold acallee_saved. cbn [In] in Hx. lia.
Qed.
Ltac rbn3c_cs := apply rbn3c_csl; reflexivity.
Lemma rbn3c_mod16 : forall a s, a mod 32 = 0 -> s mod 16 = 0 -> (a - s) mod 16 = 0.
Proof.
intros a s Ha Hs. pose proof (Z.div_mod a 32 ltac:(lia)) as Da. rewrite Ha, Z.add_0_r in Da.
pose proof (Z.div_mod s 16 ltac:(lia)) as Ds. rewrite Hs, Z.add_0_r in Ds.
replace (a - s) with ((2 * (a / 32) - s / 16) * 16) by lia. apply Z.mod_mul. lia.
Qed.
Lemma rbn3c_kept : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn3c_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma rbn3c_cells5_rng : forall X pos a n v, In (a, n, v) (rbn3_cells5 X pos) ->
  rbn_A X + 8 <= a /\ a + Z.of_nat n <= rbn_A X + 184.
Proof.
intros X pos a n v H. unfold rbn3_cells5, rbn3_cells2 in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn3c_val_mem_zero4 : forall H (m : word -> option byte) a,
  (forall i, 0 <= i < 4 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
Lemma rbn3c_zs_vis : forall (rd : Z -> option Z) q L a n,
  q mod 8 = 0 -> L mod 8 = 0 -> 0 <= q -> 0 <= L ->
  zero_shadow rd SHADOW_OFF q L ->
  q + 64 <= a -> 0 < n -> a + n + 64 <= q + L ->
  range_addressable rd SHADOW_OFF a n /\ shadow_hull_vis rd a n.
Proof.
intros rd q L a n Hq8 HL8 Hq0 HL0 Hz Hqa Hn Hhi.
assert (Hra : range_addressable rd SHADOW_OFF q L)
  by (apply zero_shadow_range; [exact Hq8 | exact HL8 | exact Hz]).
split; [eapply range_addressable_sub; [exact Hra | lia | lia]|].
assert (Hdq : (q + 64) / 8 = q / 8 + 8)
  by (replace (q + 64) with (q + 8 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
assert (D1 : q / 8 + 8 <= a / 8) by (rewrite <- Hdq; apply Z.div_le_mono; lia).
assert (HqL : (q + L) / 8 = q / 8 + L / 8).
{ pose proof (Z.div_mod L 8 ltac:(lia)) as DL.
  replace (q + L) with (q + (L / 8) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
assert (D2 : (a + n - 1) / 8 + 8 <= q / 8 + L / 8).
{ rewrite <- HqL. replace ((a + n - 1) / 8 + 8) with ((a + n - 1 + 8 * 8) / 8)
    by (rewrite Z.div_add by lia; reflexivity).
  apply Z.div_le_mono; lia. }
intros s Hs. unfold shadow_addr in Hs.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as U1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as U2.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as V1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as V2.
replace s with (shadow_of_addr SHADOW_OFF q + (s - SHADOW_OFF - q / 8))
  by (unfold shadow_of_addr; lia).
rewrite (Hz (s - SHADOW_OFF - q / 8) ltac:(unfold SHADOW_OFF in *; lia)). discriminate.
Qed.
Definition rbn3c_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition rbn3c_stk : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 184 8 184
    [YP09.mkChunk 80 (CVal 8 (SOff 12 0)); YP09.mkChunk 88 (CVal 8 (SOff 13 0))].
Definition rbn3c_ss1 : sstate := mkSS (AF_reac_box_name + RBN_Q1) sr_atoms
  [rbn3c_stk; YP09.mkRegion (Some 18%nat) 0 64 4 5 []] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Definition rbn3c_ss5 : sstate := mkSS (AF_reac_box_name + RBN_Q5) sr_atoms
  [YP09.mkRegion (Some 18%nat) 0 64 8 11 []] None (mkFacts [] [] []).
Lemma rbn3c_entry1 : forall (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte) A SH i o,
  getr regs 9 = w64 A -> getr regs 18 = w64 SH -> getr regs 12 = w64 i -> getr regs 13 = w64 o ->
  2 ^ 46 <= A -> A + 184 <= 2 ^ 47 -> A mod 32 = 0 -> 0 <= SH -> SH + 64 <= A ->
  0 <= i < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  (forall k, 8 <= k < 184 -> apresent (w_H W) memc (A + k)) -> apresent (w_H W) memc (SH + 4) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 80) 8 i -> val_mem SEGS (mrestrict (w_H W) memc) (A + 88) 8 o ->
  st_ok_pi SEGS VAL (rbn3c_E regs) rbn3c_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_Q1))) memc (seg_rom SEGS))).
Proof.
intros regs W memc A SH i o R9 R18 R12 R13 HA0 HA1 HA32 HS0 HSA Hi Ho PA PS Mi Mo.
rewrite restrict_mkst_fx.
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (rbn3c_E regs) n = getr regs r)
  by (intros n r Hn; unfold rbn3c_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew (rbn3c_E regs) 9 = Z_to_bv 64 A) by (rewrite (EL 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew (rbn3c_E regs) 18 = Z_to_bv 64 SH) by (rewrite (EL 18%nat 18%bv eq_refl); exact R18).
assert (E12 : ew (rbn3c_E regs) 12 = Z_to_bv 64 i) by (rewrite (EL 12%nat 12%bv eq_refl); exact R12).
assert (E13 : ew (rbn3c_E regs) 13 = Z_to_bv 64 o) by (rewrite (EL 13%nat 13%bv eq_refl); exact R13).
assert (VB : forall n v, ew (rbn3c_E regs) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  base_val (rbn3c_E regs) (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
unfold rbn3c_ss1. apply pa_entry_st_ok_full.
- unfold rbn3c_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rbn3c_stk. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 9%nat A E9) by lia. split; [lia|]. split; [lia|]. split.
    * intros k Hk. apply (apresent_writable SEGS). apply PA. lia.
    * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val SEGS _ _ A 80 8 (SOff 12 0) i);
           [cbn [sv_denot]; rewrite E12, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
         change (N.to_nat 8) with 8%nat. exact Mi.
      -- apply (chunk_ok_val SEGS _ _ A 88 8 (SOff 13 0) o);
           [cbn [sv_denot]; rewrite E13, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia |].
         change (N.to_nat 8) with 8%nat. exact Mo.
  + rewrite (VB 18%nat SH E18) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros k Hk. apply (apresent_writable SEGS). replace (SH + k) with (SH + 4) by lia. exact PS.
- apply pairwise_disjoint_of_extents. unfold rbn3c_stk, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat A E9), (VB 18%nat SH E18) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, unsigned_lit_small by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma rbn3c_entry5 : forall (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte) SH,
  getr regs 18 = w64 SH -> 0 <= SH -> SH + 64 <= 2 ^ 64 ->
  (forall k, 8 <= k < 11 -> apresent (w_H W) memc (SH + k)) ->
  st_ok_pi SEGS VAL (rbn3c_E regs) rbn3c_ss5
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_Q5))) memc (seg_rom SEGS))).
Proof.
intros regs W memc SH R18 HS0 HS1 PS.
rewrite restrict_mkst_fx.
assert (E18 : ew (rbn3c_E regs) 18 = Z_to_bv 64 SH)
  by (unfold rbn3c_E; rewrite (ew_Eimg_Ereg_nat regs [] 18%nat 18%bv eq_refl); exact R18).
unfold rbn3c_ss5. apply pa_entry_st_ok_full.
- unfold rbn3c_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E18, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
  intros k Hk. apply (apresent_writable SEGS). apply PS. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [exact I|]. split; exact I.
Qed.
Ltac rbn3d_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
    change (bv_unsigned x) with v end; lia.
Definition rbn3d_rs (off : Z) : smem :=
  [YP09.mkRegion (Some 9%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SOff 32 0))]].
Definition rbn3d_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition rbn3d_ss (q off : Z) : sstate := mkSS (AF_reac_box_name + q) sr_atoms (rbn3d_rs off) None rbn3d_facts.
Definition rbn3d_E (regs : bvmap 5 word) (v : Z) : env := Eimg (Ereg regs [Z_to_bv 64 v]).
Lemma rbn3d_pres_get : forall (regs regs2 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. specialize (HP _ Hr). rewrite !Z_to_bv_bv_unsigned in HP. exact HP. Qed.
Lemma rbn3d_m16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by ring. apply Z_mod_mult.
Qed.
Lemma rbn3d_gran : forall F x, F mod 32 = 0 -> F + 32 <= x < F + 40 ->
  x / 8 = F / 8 + 4 /\ x mod 8 = x - F - 32.
Proof.
intros F x HF Hx. pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D.
assert (E1 : F / 8 = 4 * (F / 32)) by (symmetry; apply Z.div_unique with (r := 0); lia).
assert (E2 : x / 8 = 4 * (F / 32) + 4) by (symmetry; apply Z.div_unique with (r := x - F - 32); lia).
split; [lia|]. rewrite (Z.mod_eq x 8) by lia. lia.
Qed.
Lemma rbn3d_shsep : forall F, 4096 <= F -> F + 512 <= alloc_ceiling -> in_app F 512 ->
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 ->
  0 <= SHADOW_OFF + F / 8 /\ SHADOW_OFF + F / 8 + 64 <= alloc_ceiling /\
  (SHADOW_OFF + F / 8 + 64 <= F \/ F + 512 <= SHADOW_OFF + F / 8).
Proof.
intros F H1 H2 H3 H4. pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H3. unfold SHADOW_OFF. lia.
Qed.
Lemma rbn3d_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn3d_dec2 : forall v, bn_ok v = true ->
  sb_dec_c.sb_dec_D v 2 = bn_dec v 2 /\ length (bn_dec v 2) = 2%nat /\ 0 <= v <= 40.
Proof.
intros v Hv. apply bn_ok_in in Hv. vm_compute in Hv.
repeat (destruct Hv as [<- | Hv]; [split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | lia]]|]).
destruct Hv.
Qed.
Lemma rbn3d_args : forall X, rbm_args X -> bn_ok (ri_i X) = true /\ bn_ok (ri_o X) = true.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
split; assumption.
Qed.
Lemma rbn3d_entry : forall q off (A v : Z) (regs : bvmap 5 word) (W : world SEGS) memc,
  (off = 80 \/ off = 88) ->
  getr regs 9 = w64 A -> 2 ^ 46 <= A <= 2 ^ 47 -> A mod 32 = 0 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + off) 8 v -> 0 <= v < 2 ^ 64 ->
  st_ok_pi SEGS VAL (rbn3d_E regs v) (rbn3d_ss q off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + q))) memc (seg_rom SEGS))).
Proof.
intros q off A v regs W memc Hoff H9 HA HA32 Mv Hv.
assert (Hoff' : 80 <= off <= 88) by (destruct Hoff; lia).
assert (E9 : ew (rbn3d_E regs v) 9 = Z_to_bv 64 A)
  by (unfold rbn3d_E; rewrite (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew (rbn3d_E regs v) 32 = Z_to_bv 64 v)
  by (unfold rbn3d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew (rbn3d_E regs v) 9) = A) by (rewrite E9; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold rbn3d_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- destruct Hoff as [-> | ->]; vm_compute; reflexivity.
- unfold rbn3d_rs. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ A off 8 _ v);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv].
- unfold rbn3d_rs. cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold rbn3d_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
  split; [lia|]. split; [exact HA32 | lia].
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma rbn3e_kept : forall E rs H (m m' : word -> option byte) (Q : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> Q a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Q a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Q HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn3e_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma rbn3e_garr8_kept : forall H (m m' : word -> option byte) base l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H m' (base + j) = aview SEGS H m (base + j)) ->
  garr8 SEGS (mrestrict H m) base l -> garr8 SEGS (mrestrict H m') base l.
Proof.
intros H m m' base l HE HG j Hj. destruct (HG j Hj) as [V Hb]. split; [|exact Hb].
apply (val_mem_kept SEGS H H m m'); [|exact V].
intros k Hk. rewrite <- Z.add_assoc. apply HE. clear - Hj Hk. lia.
Qed.
Lemma rbn3e_stem_ne : forall X, rbm_stem X <> [].
Proof.
intros X. unfold rbm_stem, bn_stem. destruct (ri_sd X) as [|c l]; [|discriminate].
unfold bn_STEM. destruct (ri_f X =? 1); [discriminate|]. destruct (ri_f X =? 2); [discriminate|].
destruct (ri_f X =? 3); discriminate.
Qed.
Lemma rbn3e_hd : forall (W : world SEGS) (m : word -> option byte) P s,
  s <> [] -> Forall (fun c => 0 < c < 256) s -> garr8 SEGS (mrestrict (w_H W) m) P (s ++ [0]) ->
  1 <= hd 0 s <= 255 /\ (1 <= length s)%nat /\ val_mem SEGS (mrestrict (w_H W) m) P 1 (hd 0 s).
Proof.
intros W m P s Hne Hch Hg. destruct s as [|c s]; [exfalso; exact (Hne eq_refl)|].
apply Forall_inv in Hch. cbn [hd length]. split; [lia|]. split; [lia|].
destruct (Hg 0%nat ltac:(cbn [length app]; lia)) as [V _]. cbn [Z.of_nat app nth] in V.
rewrite Z.add_0_r in V. exact V.
Qed.
Lemma rbn3e_w4_len : forall X, rbm_args X -> length (rbm_w4 X) = 4%nat.
Proof.
intros X HA. unfold rbm_w4. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
exact (bn_w4_length _ _ Hi Ho).
Qed.
Lemma rbn3e_entry2 : forall (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte) (A F : Z),
  getr regs 2 = w64 A -> getr regs 9 = w64 A -> getr regs 19 = w64 F -> getr regs 22 = w64 SHADOW_OFF ->
  getr regs 18 = w64 (SHADOW_OFF + F / 8) -> getr regs 25 = w64 (F + 32) ->
  2 ^ 46 <= A <= 2 ^ 47 -> A mod 32 = 0 -> 4096 <= F <= 140737479966720 -> F mod 32 = 0 -> F + 37 <= A + 8 ->
  (F + 37 <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= F) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 168) 8 4 ->
  (forall o, 32 <= o < 40 -> apresent (w_H W) memc (A + o)) -> apresent (w_H W) memc (F + 36) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) rbn3e_ss2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_Q4))) memc (seg_rom SEGS))) /\
  sh_ok SEGS rbn3e_Bx rbn3e_SH2 (Eimg (Ereg regs [])) (mrestrict (w_H W) memc).
Proof.
intros regs W memc A F R2 R9 R19 R22 R18 R25 HA HA32 HF HF32 HFA HFS V168 PA PF.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs [])) n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U2 : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = A)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew (Eimg (Ereg regs [])) 9) = A)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew (Eimg (Ereg regs [])) 19) = F)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew (Eimg (Ereg regs [])) 22) = SHADOW_OFF)
  by (rewrite (EE 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U18 : bv_unsigned (ew (Eimg (Ereg regs [])) 18) = SHADOW_OFF + F / 8)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold rbn3e_ss2. apply pa_entry_st_ok_full.
  + intros r. destruct (decide (r = 25%bv)) as [-> | Hne].
    * rewrite sr_get_set_same by reflexivity. cbn [sv_denot]. rewrite U19, R25. reflexivity.
    * rewrite sr_get_set_other by exact Hne. exact (regs_ok_Eimg_Ereg regs [] r).
  + vm_compute. reflexivity.
  + unfold rbn3e_rs2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply PA; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS _ _ A 168 8 (SLit 4) 4); [reflexivity | cbn; lia | cbn; lia |].
      change (N.to_nat 8) with 8%nat. exact V168.
    * rewrite U19. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); replace (F + o) with (F + 36) by lia; exact PF|].
      constructor.
  + apply pairwise_disjoint_of_extents. unfold rbn3e_rs2, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. unfold rbn3e_FX. cbn [app f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U2, U9, U22, U19, U18. unfold SB, SHADOW_OFF.
    repeat split; lia.
- unfold sh_ok, rbn3e_SH2. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memc _ rbn3e_Bx 19 (F + 36) 0 F 37 36).
  + apply range_addressable_nil. lia.
  + unfold rbn3e_Bx. rewrite U_SOff, U22, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
  + rewrite U_SOff, U19, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  + lia.
  + lia.
  + intros x Hx. change (Z.min 37 36) with 36 in Hx. change (Z.max 37 36) with 37 in Hx.
    unfold SHADOW_OFF in *. lia.
Qed.
Lemma rbn3e_entry3 : forall (regs : bvmap 5 word) (W : world SEGS) (memc : word -> option byte) (A F P c : Z),
  getr regs 2 = w64 A -> getr regs 9 = w64 A -> getr regs 19 = w64 F -> getr regs 22 = w64 SHADOW_OFF ->
  getr regs 18 = w64 (SHADOW_OFF + F / 8) -> getr regs 20 = w64 P ->
  2 ^ 46 <= A <= 2 ^ 47 -> A mod 32 = 0 -> 4096 <= F <= 140737479966720 -> F mod 32 = 0 ->
  1 <= P <= 2 ^ 47 - 10 -> 1 <= c <= 255 -> (P + 1 <= A + 16 \/ A + 24 <= P) ->
  val_mem SEGS (mrestrict (w_H W) memc) P 1 c ->
  (forall o, 16 <= o < 24 -> apresent (w_H W) memc (A + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 c])) rbn3e_ss3
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_Q6))) memc (seg_rom SEGS))).
Proof.
intros regs W memc A F P c R2 R9 R19 R22 R18 R20 HA HA32 HF HF32 HP Hc HPd Vc PA.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs [Z_to_bv 64 c])) n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 c])) 32 = Z_to_bv 64 c)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U2 : bv_unsigned (ew (Eimg (Ereg regs [Z_to_bv 64 c])) 2) = A)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew (Eimg (Ereg regs [Z_to_bv 64 c])) 9) = A)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew (Eimg (Ereg regs [Z_to_bv 64 c])) 19) = F)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (Eimg (Ereg regs [Z_to_bv 64 c])) 20) = P)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew (Eimg (Ereg regs [Z_to_bv 64 c])) 22) = SHADOW_OFF)
  by (rewrite (EE 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U18 : bv_unsigned (ew (Eimg (Ereg regs [Z_to_bv 64 c])) 18) = SHADOW_OFF + F / 8)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew (Eimg (Ereg regs [Z_to_bv 64 c])) 32) = c)
  by (rewrite E32; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold rbn3e_ss3. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rbn3e_rs3. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply PA; lia | constructor].
  + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ P 0 1 (SOff 32 0) c);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. exact Vc.
- apply pairwise_disjoint_of_extents. unfold rbn3e_rs3, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. unfold rbn3e_FX. cbn [app f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite U2, U9, U22, U19, U18, U20, U32. unfold SB, SHADOW_OFF.
  repeat split; lia.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IS___asan_memset).
Hypothesis PSIG : ident_prog_sig_ok.
Hypothesis HSB : tsb_dec_spec B.
Lemma rbn3a_cx : forall X, rbn_cx B G X ->
  AR SEGS B (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X) /\
  astk_ok REAC_BOX_NAME_STK (ri_lyc X) (rbn_SP X) /\ Z.of_nat (length (frames (ri_Sc X))) <= 7 /\
  0 <= ri_name X /\ 0 <= ri_token X /\ 0 <= ri_display X /\ rbn_img B G (ri_W X) (ri_memc X) /\
  (rbm_args X ->
     rbn_said (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_said X) (ri_sd X) /\
     rbn_bufs B (ri_lyc X) (ri_Sc X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X)
       (ri_display_len X)).
Proof.
intros X HX.
destruct HX as (HPRE & HRO & R10 & F10 & R11 & F11 & R12 & F12 & R13 & F13 & R14 & F14 & R15 & F15 & R16 & F16 &
  R17 & F17 & HPR & Md & Rd & Mdl & Rdl & HIMG & HARG & HFR & HEV & HLV).
destruct HPRE as (HAR & _ & _ & _ & _ & HSTK & _).
split; [exact HAR|]. split; [exact HSTK|]. split; [exact HFR|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HIMG | exact HARG].
Qed.
Lemma rbn3a_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh -> forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM c p.
destruct HM as (_ & (_ & Hly & _) & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _).
unfold frame_addr. rewrite HF. reflexivity.
Qed.
Lemma rbn3_geo : rbn3_geo_stmt B G.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
destruct (rbn3a_cx X HX) as (HAR0 & HSTK & HLEN & _).
pose proof (rbn3a_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM) as FA.
destruct HM as (HW & HJ & _).
destruct HJ as (HAR1 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _).
destruct HSTK as (H16 & HS0 & Hc & Hlo0 & Hhi0 & H47 & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & Hspr).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
split; [clear - Hc Hlo0; lia|].
split; [clear - Hhi0 H47; lia|].
split; [exact H16|].
split.
{ unfold rbn_A. pose proof (Z.div_mod (rbn_SP X - 288) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (rbn_SP X - 288) 32 ltac:(lia)) as M1. clear - D1 M1. lia. }
split.
{ unfold rbn_A. pose proof (Z.div_mod (rbn_SP X - 288) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (rbn_SP X - 288) 32 ltac:(lia)) as M1. clear - D1 M1. lia. }
split; [unfold rbn_A; rewrite Z.mul_comm; apply Z.mod_mul; lia|].
split; [rewrite Hlo; clear - Hlo0; lia|].
split; [rewrite Hhi; exact Hhi0|].
split; [exact Hpres|].
split; [exact Hfrs|].
split; [rewrite Hfrs; cbn [length app]; clear - HLEN; lia|].
split; [exact FA|].
unfold rbn_SH, rbn_F. rewrite <- (FA 3 pos).
rewrite Hfb3 in HFceil, Happ, Hpr, Hspr.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|].
split.
{ intros a Ha. destruct (Hpr a Ha) as [Hp Hno]. split; [exact Hp|]. split; [|exact Hno].
  refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
  split; [exact Hin3|]. rewrite Hfb3. exact Ha. }
split; [reflexivity|].
intros i Hi. exact (Hspr i ltac:(change (512 / 8) with 64; lia)).
Qed.
Lemma rbn3_mid_upd : rbn3_mid_upd_stmt B G.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh lyc2 Sc2 memc2 mdc2 sh2 HX HM HJ2 Hperm2 Himg Hblk Hstk Hfl Hsh2.
destruct HM as (HW & HJ & Hperm & Hro & HK & Hfr & Hflag & Hsh).
split; [exact HW|].
split; [exact HJ2|].
split; [exact (Permutation_trans Hperm2 Hperm)|].
split.
{ intros a Ha Hno Her.
  assert (Hia : in_img SEGS a).
  { destruct Ha as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]. }
  rewrite (Himg a Hia Hno Her). exact (Hro a Ha Hno Her). }
split.
{ intros a Ha Hb Hn. rewrite (Hblk a Hb). exact (HK a Ha Hb Hn). }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memc2); [|exact (Hfr j r Hj)].
  intros k Hk. apply Hstk. clear - Hj13 Hk. lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memc2); [|exact Hflag].
  intros k Hk. apply Hfl. clear - Hk. lia. }
exact Hsh2.
Qed.
Lemma rbn3_img : rbn3_img_stmt B G.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh HX HM HA.
pose proof (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HX HM) as GEO.
destruct GEO as (G1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GF & _).
destruct (rbn3a_cx X HX) as (_ & _ & _ & HN0 & HT0 & HD0 & HIMG & _).
destruct HM as (HW & HJ & _). subst W1.
destruct HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
pose proof (rbn3a_nso X HA HN0 HT0 HD0) as HNS.
split.
{ intros a Hf. destruct (Hf a ltac:(lia)) as (Hia & Hno & Her).
  exact (Himg a Hia Hno Her (fp_spares_closed _ a HNS)). }
split.
{ destruct HIMG as (_ & _ & _ & Hzs & _). exact (ro_usable SEGS B LAWS _ _ _ _ _ _ _ HAR1 Hzs). }
intros a s (Hlo & Hhi & Hfa & Hg & (q & z & Hq & Hq1 & Hq2) & Hfx & Htl).
assert (KS : forall x, a <= x < a + Z.of_nat (length s) + 1 ->
  in_img SEGS x /\ aview SEGS (w_H (ri_W X)) memc1 x = aview SEGS (w_H (ri_W X)) (ri_memc X) x).
{ intros x Hx. destruct (Hfx x ltac:(lia)) as (Hia & Hno & Her). split; [exact Hia|].
  exact (Himg x Hia Hno Her (fp_spares_closed _ x HNS)). }
destruct (ro_read_ok_glob SEGS B G lyc1 Sc1 (ri_W X) memc1 mdc1 q z a (Z.of_nat (length s) + 1) GM Hq IV HAR1
  Hq1 Hq2 ltac:(lia) Hlo ltac:(unfold IMG_HI; lia)) as (Hra & Hhv).
split.
{ split; [exact Hfa|]. split; [lia|]. split; [lia|]. split; [left; unfold kLowMemEnd; lia|].
  split.
  { apply (garr8_frame SEGS (mrestrict (w_H (ri_W X)) (ri_memc X))); [exact Hg|]. intros x Hx.
    rewrite length_app in Hx. cbn [length] in Hx.
    apply (mbyte_of_aview SEGS). exact (proj2 (KS x ltac:(lia))). }
  split; [exact Hra|]. split; [exact Hhv|].
  intros x Hx. exact (rbn3a_rom_vis _ _ x (Htl x Hx)). }
intros x Hx. destruct (KS x Hx) as (Hia & _). pose proof (pa_segs_low x Hia) as Hlow.
split.
- intros Hs. pose proof asan_consts as (C1 & _). unfold kLowMemEnd in Hlow. clear - Hlow Hs G1 C1. lia.
- intros Hf. exact (proj1 (proj2 (GF x Hf)) Hia).
Qed.
Lemma rbn3a_nfp : forall X cid p y, rbm_args X ->
  AR SEGS B (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X) ->
  rbn_bufs B (ri_lyc X) (ri_Sc X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X)
    (ri_display_len X) ->
  In (cid, p) (frames (ri_Sc X)) ->
  (in_zr y (frame_rng (ri_lyc X) (cid, p)) \/
   in_zr y (shadow_addr (frame_addr (ri_lyc X) cid p), fs_frame_bytes cid / 8)) ->
  ~ inFP (rbn_FPX X) y.
Proof.
intros X cid p y HA HAR (B1 & B2 & B3 & _) Hin Hy Hf.
assert (K : forall q N, In (q, N) (ablocks B (ri_lyc X) (ri_Sc X)) -> q <= y < q + N -> False).
{ intros q N Hq HyN.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR Hq) as (_ & _ & _ & _ & _ & _ & HN).
  pose proof (req_size_pos N (proj1 HN)) as (_ & HrN).
  apply (block_not_frame_zone SEGS B LAWS _ _ _ _ _ q N (y - q) cid p HAR Hq Hin); [clear - HyN HrN; lia|].
  replace (q + (y - q)) with y by lia. exact Hy. }
destruct (rbn3a_fp_cases X y HA Hf) as [Hry | [Hry | Hry]].
- destruct B1 as (q & N & Hq & H1 & H2). apply (K q N Hq). clear - Hry H1 H2. lia.
- destruct B2 as (q & N & Hq & H1 & H2). apply (K q N Hq). clear - Hry H1 H2. lia.
- destruct B3 as (q & N & Hq & H1 & H2). apply (K q N Hq). clear - Hry H1 H2. lia.
Qed.
Lemma rbn3_said : rbn3_said_stmt B G.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh HX HM HA Hs0.
pose proof (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HX HM) as (G1 & _).
pose proof (rbn3a_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HM) as FA.
destruct (rbn3a_cx X HX) as (HAR0 & _ & _ & _ & _ & _ & _ & HARG).
destruct (HARG HA) as (HSD & HBUF).
destruct HSD as [(E & _) | (_ & HC & cid & p & Hin & Hp1 & Hp2)]; [exfalso; exact (Hs0 E)|].
destruct HM as (HW & HJ & _). subst W1.
destruct HJ as (HAR1 & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & Hfrm & _).
destruct (frame_facts B _ _ _ cid p (proj1 HAR0) Hin) as (_ & _ & _ & _ & HFal & _ & _ & Hoff & _ & Hfb & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR0 Hin) as (Hf4096 & Hfceil & _).
assert (Hfa64 : frame_addr (ri_lyc X) cid p mod 64 = 0).
{ unfold frame_addr. unfold page_aligned in HFal. clear - HFal Hoff. Z.div_mod_to_equations. lia. }
assert (KB : forall y, (in_zr y (frame_rng (ri_lyc X) (cid, p)) \/
    in_zr y (shadow_addr (frame_addr (ri_lyc X) cid p), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H (ri_W X)) memc1 y = aview SEGS (w_H (ri_W X)) (ri_memc X) y).
{ intros y Hy. exact (Hfrm cid p y Hin Hy (rbn3a_nfp X cid p y HA HAR0 HBUF Hin Hy)). }
split.
{ apply (rbn3a_cstr_kept (ri_W X) (ri_memc X) memc1 (ri_said X) (ri_sd X) HC).
  - intros x Hx. apply KB. left. unfold frame_rng, in_zr. cbn [fst snd]. clear - Hx Hp1 Hp2. lia.
  - intros y Hy. apply KB. right. unfold in_zr. cbn [fst snd].
    apply (rbn3a_hull_in _ _ (ri_said X) (Z.of_nat (length (ri_sd X))) y Hfa64 Hfb); [| exact Hp1 | | | exact Hy];
    clear - Hf4096 Hp1 Hp2; lia. }
destruct (in_split _ _ Hin) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
  ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !FA in Hd.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity. rewrite Hfb3 in Hd.
intros x Hx. split.
- clear - Hx Hp2 Hfceil G1. lia.
- unfold rbn_F. clear - Hx Hp1 Hp2 Hd. lia.
Qed.
Lemma rbn3_stp : rbn3_stp_stmt B G.
Proof.
intros X pos P lyc1 Sc1 W1 memc1 mdc1 sh HX HM HA [(Hs0 & Hsd & ->) | (_ & Hi)].
- destruct (rbn3_said X pos lyc1 Sc1 W1 memc1 mdc1 sh HX HM HA Hs0) as (HC & HD).
  assert (Es : rbm_stem X = ri_sd X).
  { unfold rbm_stem, bn_stem. destruct (ri_sd X) eqn:E; [exfalso; exact (Hsd eq_refl) | reflexivity]. }
  unfold rbn_stp. rewrite Es. split; [exact HC|]. intros a Ha. apply HD. clear - Ha. lia.
- destruct (rbn3_img X pos lyc1 Sc1 W1 memc1 mdc1 sh HX HM HA) as (_ & _ & HI).
  exact (HI P (rbm_stem X) Hi).
Qed.
Lemma rbn3b_said_loc : forall X, rbn_cx B G X -> rbm_args X -> ri_said X <> 0 ->
  4096 <= ri_said X /\ ri_said X + 8 <= alloc_ceiling /\ (ri_said X + 1 <= IMG_LO \/ IMG_TOP <= ri_said X).
Proof.
intros X HX HA Hs.
pose proof HX as (HPRE & HX'). pose proof HPRE as (HAR & _).
do 23 (destruct HX' as [_ HX']). destruct HX' as [Hargs _].
destruct (Hargs HA) as [Hsaid _].
destruct Hsaid as [(Hz & _) | (_ & _ & cid & p & Hin & Hlo & Hhi)]; [contradiction|].
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR Hin) as (F1 & F2 & _).
pose proof (frm_off_imgP B _ _ _ _ _ cid p HAR Hin) as F3.
clear - Hlo Hhi F1 F2 F3. split; [lia|]. split; [lia|]. destruct F3; [left | right]; lia.
Qed.
Lemma rbn3b_sd_nil : forall X, rbn_cx B G X -> rbm_args X -> (ri_said X = 0 \/ ri_sd X = []) -> ri_sd X = [].
Proof.
intros X HX HA H. pose proof HX as HX'. do 24 (destruct HX' as [_ HX']). destruct HX' as [Hargs _].
destruct (Hargs HA) as [Hsaid _].
destruct H as [H | H]; [|exact H].
destruct Hsaid as [(_ & Hn) | (Hne & _)]; [exact Hn | contradiction].
Qed.
Lemma rbn3b_src_img : forall X P, rbn_cx B G X -> rbm_args X -> (ri_said X = 0 \/ ri_sd X = []) ->
  rbn_imgstr B G (ri_W X) (ri_memc X) P (bn_STEM (ri_f X)) -> rbn3_src B G X P.
Proof.
intros X P HX HA H HI. right. split; [exact H|]. unfold rbm_stem. rewrite (rbn3b_sd_nil X HX HA H). exact HI.
Qed.
Lemma rbn3b_close : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regs2 mem2 md2,
  rbn_cx B G X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 8 <= a < rbn_A X + 184) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_cells (mrestrict (w_H W1) mem2) (rbn3_cells1 X) ->
  (forall r, In r rbn3b_keep -> getr regs2 r = getr regs1 r) ->
  getr regs2 20 = w64 P -> rbn3_src B G X P ->
  rbn3_s1 B G X pos P regs2 lyc1 Sc1 W1 mem2 md2.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regs2 mem2 md2 HX H3 HJ2 HK HC HR R20 HP.
destruct H3 as (HM & (B2 & B3 & B4 & B8 & B9 & B19 & B22) & R18 & R26 & _ & R23 & R24 & _ & R27 &
  R12 & R13 & R14 & R15 & R16 & HA).
destruct (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & _ & G4 & G5 & _ & _ & _ & _ & _ & _ & _ & G13 & G14 & _ & _ & _ & G18 & _).
pose proof HX as (HPRE & _). pose proof HPRE as (HAR0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
assert (HA46 : 2 ^ 46 <= rbn_A X) by (clear - G1 G4 C1 WS; lia).
assert (HSH : 0 <= rbn_SH X pos /\ rbn_SH X pos + 64 <= 2 ^ 46).
{ rewrite G18. unfold SHADOW_OFF.
  assert (D1 : rbn_F X pos / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
  assert (D3 : 0 <= rbn_F X pos / 8) by (apply Z.div_pos; lia).
  clear - D1 D2 D3. lia. }
assert (K : forall a, 0 <= a < rbn_A X + 8 -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha. apply HK; clear - Ha G2 G5; lia. }
assert (HMID : rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) (rbn_sh false false false false)).
{ apply (rbn3_mid_upd X pos lyc1 Sc1 W1 memc1 mdc1 (rbn_sh false false false false) lyc1 Sc1 mem2 md2
    (rbn_sh false false false false) HX HM HJ2 (Permutation_refl _)).
  - intros a Hia _ _. pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
    apply K. clear - Hlow HA46. lia.
  - intros a (q & N & Hq & Hqa). destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR0 Hq) as (_ & Hb4 & Hbc & _).
    assert (Hj : a < q + req_size N) by (clear - Hqa; unfold req_size; destruct (Z.eqb_spec N 0); lia).
    apply K. clear - Hqa Hb4 Hbc Hj G1 G4 WS. lia.
  - intros a Ha. apply HK; clear - Ha G1 G2 G5 C1 WS; lia.
  - intros a Ha. apply K. clear - Ha G13 G14 G1 G4 WS. lia.
  - pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh). intros j Hj.
    rewrite rbn3b_sh_len in Hj. rewrite K by (clear - Hj HSH HA46; lia).
    apply Hsh. rewrite rbn3b_sh_len. exact Hj. }
pose proof (HR 2%bv ltac:(rbn3b_inl)) as K2. pose proof (HR 3%bv ltac:(rbn3b_inl)) as K3.
pose proof (HR 4%bv ltac:(rbn3b_inl)) as K4. pose proof (HR 8%bv ltac:(rbn3b_inl)) as K8.
pose proof (HR 9%bv ltac:(rbn3b_inl)) as K9. pose proof (HR 12%bv ltac:(rbn3b_inl)) as K12.
pose proof (HR 13%bv ltac:(rbn3b_inl)) as K13. pose proof (HR 14%bv ltac:(rbn3b_inl)) as K14.
pose proof (HR 15%bv ltac:(rbn3b_inl)) as K15. pose proof (HR 16%bv ltac:(rbn3b_inl)) as K16.
pose proof (HR 18%bv ltac:(rbn3b_inl)) as K18. pose proof (HR 19%bv ltac:(rbn3b_inl)) as K19.
pose proof (HR 22%bv ltac:(rbn3b_inl)) as K22. pose proof (HR 23%bv ltac:(rbn3b_inl)) as K23.
pose proof (HR 24%bv ltac:(rbn3b_inl)) as K24. pose proof (HR 26%bv ltac:(rbn3b_inl)) as K26.
pose proof (HR 27%bv ltac:(rbn3b_inl)) as K27.
unfold rbn3_s1, rbn3_core.
split; [split; [exact HMID|] |].
- split.
  { unfold rbn_rbase. rewrite K2, K3, K4, K8, K9, K19, K22.
    split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B8|]. split; [exact B9|].
    split; [exact B19 | exact B22]. }
  split; [rewrite K18; exact R18|]. split; [rewrite K26; exact R26|]. split; [exact R20|].
  split; [rewrite K23; exact R23|]. split; [rewrite K24; exact R24|]. split; [rewrite K27; exact R27|].
  split; [exact HC|]. split; [exact HA | exact HP].
- rewrite K12, K13, K14, K15, K16.
  split; [exact R12|]. split; [exact R13|]. split; [exact R14|]. split; [exact R15 | exact R16].
Qed.
Lemma rbn3b_post : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B G X -> rbn_st3 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  forall P E' ss' ms' md' extra cs,
  st_ok_pi SEGS VAL E' ss' (restrict (w_H W1) ms') -> ss_resv ss' = None ->
  ss_pc ss' = AF_reac_box_name + RBN_Q1 ->
  env_agree 32 (Ereg regs1 extra) E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) rbn3b_keep = true ->
  nth_error (ss_mem ss') 0 = Some (YP09.mkRegion (Some 9%nat) 8 184 8 184 cs) ->
  In (YP09.mkChunk 80 (CVal 8 (SOff 12 0))) cs -> In (YP09.mkChunk 88 (CVal 8 (SOff 13 0))) cs ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 (ms_mem ms') md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 8 <= a < rbn_A X + 184) ->
     aview SEGS (w_H W1) (ms_mem ms') a = aview SEGS (w_H W1) memc1 a) ->
  getr (ms_regs ms') 20 = w64 P -> rbn3_src B G X P ->
  rbn3_at1 B G X pos W1 (mkCfg ms' md').
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3 P E' ss' ms' md' extra cs HS Hrv Hpc HAE Hkp Hr0 H80 H88
  HJ2 HK R20 HP.
pose proof (st_ok_pi_restrict_mkst (w_H W1) E' ss' ms' HS Hrv) as Hms.
pose proof (regs_kept_of_st_ok_pi E' ss' (restrict (w_H W1) ms') regs1 extra rbn3b_keep HS HAE Hkp) as HKr.
cbn [ms_regs restrict] in HKr.
pose proof (st_ok_pi_region_nth E' ss' (restrict (w_H W1) ms') 0 _ HS Hr0) as HR0.
cbn [ms_mem restrict] in HR0.
pose proof H3 as (HM & (_ & _ & _ & _ & B9 & _) & _ & _ & _ & _ & _ & _ & _ & R12 & R13 & _).
destruct (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (G1 & G2 & _ & G4 & G5 & _).
destruct HAE as [HAE _].
assert (EA : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E' n = getr regs1 r)
  by (intros n r Hn Hr; rewrite (HAE n Hn); exact (ew_Ereg_nat regs1 extra n r Hr)).
assert (U9 : bv_unsigned (ew E' 9) = rbn_A X).
{ rewrite (EA 9%nat 9%bv ltac:(lia) eq_refl), B9. unfold w64. apply unsigned_lit_small.
  pose proof asan_consts as (C1 & _). assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
  clear - G1 G2 G4 G5 C1 WS. lia. }
destruct (rbn3b_cells E' _ (rbn_A X) (ri_i X) (ri_o X) cs HR0 U9 H80 H88
  ltac:(rewrite (EA 12%nat 12%bv ltac:(lia) eq_refl); exact R12)
  ltac:(rewrite (EA 13%nat 13%bv ltac:(lia) eq_refl); exact R13)) as (C80 & C88).
unfold rbn3_at1. exists P, (ms_regs ms'), lyc1, Sc1, (ms_mem ms'), md'.
split.
- transitivity (mkCfg (mkst (ms_regs ms') (Z_to_bv 64 (BASE + ss_pc ss')) (ms_mem ms') (seg_rom SEGS)) md');
    [rewrite <- Hms; reflexivity|].
  rewrite Hpc. unfold rbn_cfg, cfg_at, w64. rewrite Z.add_assoc. reflexivity.
- exact (rbn3b_close X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P (ms_regs ms') (ms_mem ms') md' HX H3 HJ2 HK
    (conj C80 (conj C88 I)) HKr R20 HP).
Qed.
Ltac rbn3b_fin POST HS HAE HJ K P tacP Hsrc :=
  apply SRr_ret;
  let RF := fresh "RF20" in prreg HS (20%bv : bv 5) RF;
  eapply (POST P);
  [ exact HS | reflexivity | vm_compute; reflexivity | env_agree_chain HAE
  | vm_compute; reflexivity | reflexivity | rbn3b_inl | rbn3b_inl | exact HJ | exact K
  | rewrite RF; tacP | exact Hsrc ].
Lemma rbn3_T1 : rbn3_T1_stmt B G.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3.
pose proof H3 as (HM & HRB & R18 & R26 & R20 & R23 & R24 & R25 & R27 & R12 & R13 & R14 & R15 & R16 & HA).
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
pose proof HM as (HW1 & HJ & _).
destruct (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (G1 & G2 & _ & G4 & G5 & G6 & _ & _ & G9 & _).
destruct (rbn3_img X pos lyc1 Sc1 W1 memc1 mdc1 _ HX HM HA) as (Hfix & HRAt & _).
pose proof HX as HX'. do 3 (destruct HX' as [_ HX']). destruct HX' as [Hfr HX'].
do 19 (destruct HX' as [_ HX']). destruct HX' as [Himg _].
destruct Himg as (HT8 & HT1 & HT2 & _ & HTfix & (s1 & s2 & s3 & V1 & V2 & V3 & I1 & I2 & I3) & I0 & _).
pose proof asan_consts as (C1 & _).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
assert (HA46 : 2 ^ 46 <= rbn_A X) by (clear - G1 G4 C1 WS; lia).
assert (HA47 : rbn_A X + 184 <= 2 ^ 47) by (clear - G2 G5; lia).
assert (HD1 : - REAC_BOX_NAME_STK <= rbn_A X - rbn_SP X + 8) by (clear - G4 WS; lia).
assert (HD2 : rbn_A X - rbn_SP X + 184 <= 0) by (clear - G5; lia).
assert (PA : forall o, 8 <= o < 184 -> apresent (w_H W1) memc1 (rbn_A X + o))
  by (intros o Ho; apply G9; clear - Ho G4 G5 WS; lia).
assert (KT : forall k, 0 <= k < 24 ->
  aview SEGS (w_H W1) memc1 (VAL (A_OBJ 21) + k) = aview SEGS (w_H (ri_W X)) (ri_memc X) (VAL (A_OBJ 21) + k))
  by (intros k Hk; apply Hfix; intros x Hx; apply HTfix; clear - Hk Hx; lia).
assert (V1' : val_mem SEGS (mrestrict (w_H W1) memc1) (VAL (A_OBJ 21)) 8 s1)
  by (apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H W1) (ri_memc X) memc1);
      [intros k Hk; apply KT; clear - Hk; lia | exact V1]).
assert (V2' : val_mem SEGS (mrestrict (w_H W1) memc1) (VAL (A_OBJ 21) + 8) 8 s2)
  by (apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H W1) (ri_memc X) memc1);
      [intros k Hk; rewrite <- Z.add_assoc; apply KT; clear - Hk; lia | exact V2]).
assert (V3' : val_mem SEGS (mrestrict (w_H W1) memc1) (VAL (A_OBJ 21) + 16) 8 s3)
  by (apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H W1) (ri_memc X) memc1);
      [intros k Hk; rewrite <- Z.add_assoc; apply KT; clear - Hk; lia | exact V3]).
assert (Q1 : 0 <= s1 < 2 ^ 64) by (destruct I1 as (Ia & Ib & _); clear - Ia Ib; lia).
assert (Q2 : 0 <= s2 < 2 ^ 64) by (destruct I2 as (Ia & Ib & _); clear - Ia Ib; lia).
assert (Q3 : 0 <= s3 < 2 ^ 64) by (destruct I3 as (Ia & Ib & _); clear - Ia Ib; lia).
assert (HTr1 : IMG_LO <= VAL (A_OBJ 21)) by (clear - HT1; lia).
assert (HTr2 : VAL (A_OBJ 21) + 24 <= IMG_TOP) by (clear - HT2; lia).
clear Hfix KT V1 V2 V3.
pose proof (@paj_run_to fx _ _ _ _ _ B LAWS) as RUNTO. pose proof (@paj_run fx _ _ _ _ _ B LAWS) as RUN.
pose proof (paj_branch (fx := fx) (PI := PI)) as BR.
pose proof (rbn3b_post X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX H3) as POST.
unfold rbn_cfg, cfg_at, w64. rewrite <- Z.add_assoc.
destruct (Z.eq_dec (ri_said X) 0) as [Hs0 | Hs0].
- assert (R20' : getr regs1 20 = w64 0) by (rewrite R20, Hs0; reflexivity).
  pose proof (rbn3b_entry0 W1 regs1 memc1 (rbn_A X) s1 s2 s3 1 B2 B9 B22 R20' HA46 HA47 G6 PA HT8 HTr1 HTr2
    Q1 Q2 Q3 V1' V2' V3') as HS.
  destruct (rbn3b_ew regs1 s1 s2 s3 1) as (E32 & E33 & E34 & E35 & EE & ET & E259).
  assert (HEI : img_env VAL A_LIM (rbn3b_E regs1 s1 s2 s3 1)) by (unfold rbn3b_E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs1 (map (Z_to_bv 64) [s1; s2; s3; 1])) (rbn3b_E regs1 s1 s2 s3 1))
    by (unfold rbn3b_E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; clear - Hn; lia | reflexivity]).
  set (Eb := rbn3b_E regs1 s1 s2 s3 1) in *. clearbody Eb.
  assert (E22 : ew Eb 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact B22).
  pose proof (rbn3b_shok Eb W1 memc1 HEI E22 HRAt HTr1 HTr2) as SHOK.
  assert (U9 : bv_unsigned (ew Eb 9) = rbn_A X)
    by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; clear - HA46 HA47; lia).
  assert (U9s : bv_unsigned (ew Eb 9) = rbn_SP X + (rbn_A X - rbn_SP X)) by (rewrite U9; ring).
  assert (Hsn : ri_said X = 0 \/ ri_sd X = []) by (left; exact Hs0).
  assert (HFc : ri_f X = 1 \/ ri_f X = 2 \/ ri_f X = 3 \/ ~ (1 <= ri_f X <= 3)) by (clear - Hfr; lia).
  destruct HFc as [Hfk | [Hfk | [Hfk | HN]]].
  + rewrite Hfk in R25. rbn3b_pin25 constr:(1%Z) R25.
    rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2 ltac:(fail).
    rbn3b_kfr U9 X K1.
    assert (Hsrc : rbn3_src B G X s1) by (apply (rbn3b_src_img X _ HX HA Hsn); rewrite Hfk; exact I1).
    rbn3b_fin POST HS HAE HJ K1 s1 ltac:(rewrite E32; reflexivity) Hsrc.
  + rewrite Hfk in R25. rbn3b_pin25 constr:(2%Z) R25.
    rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2 ltac:(fail).
    rbn3b_kfr U9 X K1.
    assert (Hsrc : rbn3_src B G X s2) by (apply (rbn3b_src_img X _ HX HA Hsn); rewrite Hfk; exact I2).
    rbn3b_fin POST HS HAE HJ K1 s2 ltac:(rewrite E33; reflexivity) Hsrc.
  + rewrite Hfk in R25. rbn3b_pin25 constr:(3%Z) R25.
    rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2 ltac:(fail).
    rbn3b_kfr U9 X K1.
    assert (Hsrc : rbn3_src B G X s3) by (apply (rbn3b_src_img X _ HX HA Hsn); rewrite Hfk; exact I3).
    rbn3b_fin POST HS HAE HJ K1 s3 ltac:(rewrite E34; reflexivity) Hsrc.
  + rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2 ltac:(fail).
    rbn3b_kfr U9 X K1.
    lazymatch goal with HSq : st_ok_pi _ _ ?E1 _ _ |- _ =>
      assert (E25 : ew E1 25 = Z_to_bv 64 (ri_f X))
        by (cbn [ew ewset Nat.eqb]; rewrite (EE 25%nat 25%bv eq_refl); exact R25) end.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2 ltac:(fail).
      rbn3b_kfr U9 X K2.
      lazymatch type of K2 with forall a, _ -> _ -> aview _ _ ?m2 _ = _ =>
        assert (Kf : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 8 <= a < rbn_A X + 184) ->
          aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) memc1 a)
          by (intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)) end.
      assert (Hsrc : rbn3_src B G X (VAL (A_OBJ 18)))
        by (apply (rbn3b_src_img X _ HX HA Hsn); rewrite (rbn3b_stem_oth _ HN); exact I0).
      rbn3b_fin POST HS HAE HJ Kf (VAL (A_OBJ 18)) ltac:(rewrite E259; reflexivity) Hsrc.
    * exfalso. rewrite (rbn3b_bltu_other _ (ri_f X) E25 Hfr HN) in Hc. discriminate Hc.
- destruct (rbn3_said X pos lyc1 Sc1 W1 memc1 mdc1 _ HX HM HA Hs0) as (Hcs & _).
  destruct (rbn3b_said_loc X HX HA Hs0) as (L1 & L2 & L3).
  pose proof Hcs as (Hcf & _ & _ & _ & Hcg & Hcra & _).
  assert (HOB : ri_said X + 1 <= ri_said X + (Z.of_nat (length (ri_sd X)) + 1)) by (clear - Hs0; lia).
  assert (Hsr1 : 4096 <= ri_said X <= 140737479966720) by (clear - L1 L2 C1; lia).
  assert (Hsr2 : ri_said X + 1 <= VAL (A_OBJ 21) \/ VAL (A_OBJ 21) + 24 <= ri_said X)
    by (clear - L3 HT1 HT2; lia).
  assert (Hsr3 : ri_said X + 1 <= rbn_A X + 8) by (clear - L2 G1 G4 WS; lia).
  destruct (ri_sd X) as [|c0 sd'] eqn:Hsd; try rewrite Hsd in Hcg; try rewrite Hsd in Hcf.
  + assert (Vc : val_mem SEGS (mrestrict (w_H W1) memc1) (ri_said X) 1 0).
    { destruct (garr8_nthZ SEGS _ _ _ 0 Hcg ltac:(lia) ltac:(cbn; lia)) as (Vq & _).
      rewrite Z.add_0_r in Vq. exact Vq. }
    pose proof (rbn3b_entryS W1 regs1 memc1 (rbn_A X) (ri_said X) s1 s2 s3 1 (SLit 0) 0 B2 B9 B22 R20 HA46 HA47
      G6 PA HT8 HTr1 HTr2 Q1 Q2 Q3 V1' V2' V3' Hsr1 Hsr2 Hsr3 ltac:(clear - HA; lia) eq_refl
      ltac:(clear - HA; lia) Vc) as HS.
    destruct (rbn3b_ew regs1 s1 s2 s3 1) as (E32 & E33 & E34 & E35 & EE & ET & E259).
    assert (HEI : img_env VAL A_LIM (rbn3b_E regs1 s1 s2 s3 1)) by (unfold rbn3b_E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs1 (map (Z_to_bv 64) [s1; s2; s3; 1])) (rbn3b_E regs1 s1 s2 s3 1))
      by (unfold rbn3b_E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; clear - Hn; lia | reflexivity]).
    set (Eb := rbn3b_E regs1 s1 s2 s3 1) in *. clearbody Eb.
    assert (E22 : ew Eb 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact B22).
    pose proof (rbn3b_shok Eb W1 memc1 HEI E22 HRAt HTr1 HTr2) as SHOK.
    assert (U9 : bv_unsigned (ew Eb 9) = rbn_A X)
      by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; clear - HA46 HA47; lia).
    assert (U9s : bv_unsigned (ew Eb 9) = rbn_SP X + (rbn_A X - rbn_SP X)) by (rewrite U9; ring).
    assert (HUB : U Eb rbn3b_Bx = SHADOW_OFF)
      by (unfold rbn3b_Bx; apply U_atom; [exact E22 | unfold SHADOW_OFF; clear - HA; lia]).
    assert (HU20 : U Eb (SOff 20 0) = ri_said X)
      by (apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl); exact R20 | clear - Hsr1; lia]).
    assert (Hsn : ri_said X = 0 \/ ri_sd X = []) by (right; exact Hsd).
    assert (HFc : ri_f X = 1 \/ ri_f X = 2 \/ ri_f X = 3 \/ ~ (1 <= ri_f X <= 3)) by (clear - Hfr; lia).
    destruct HFc as [Hfk | [Hfk | [Hfk | HN]]].
    * rewrite Hfk in R25. rbn3b_pin25 constr:(1%Z) R25.
      rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2
        ltac:(rewrite HU20; eapply obl_of_range; [exact Hcra | exact HUB | apply Z.le_refl | exact HOB]).
      rbn3b_kfr U9 X K1.
      assert (Hsrc : rbn3_src B G X s1) by (apply (rbn3b_src_img X _ HX HA Hsn); rewrite Hfk; exact I1).
      rbn3b_fin POST HS HAE HJ K1 s1 ltac:(rewrite E32; reflexivity) Hsrc.
    * rewrite Hfk in R25. rbn3b_pin25 constr:(2%Z) R25.
      rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2
        ltac:(rewrite HU20; eapply obl_of_range; [exact Hcra | exact HUB | apply Z.le_refl | exact HOB]).
      rbn3b_kfr U9 X K1.
      assert (Hsrc : rbn3_src B G X s2) by (apply (rbn3b_src_img X _ HX HA Hsn); rewrite Hfk; exact I2).
      rbn3b_fin POST HS HAE HJ K1 s2 ltac:(rewrite E33; reflexivity) Hsrc.
    * rewrite Hfk in R25. rbn3b_pin25 constr:(3%Z) R25.
      rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2
        ltac:(rewrite HU20; eapply obl_of_range; [exact Hcra | exact HUB | apply Z.le_refl | exact HOB]).
      rbn3b_kfr U9 X K1.
      assert (Hsrc : rbn3_src B G X s3) by (apply (rbn3b_src_img X _ HX HA Hsn); rewrite Hfk; exact I3).
      rbn3b_fin POST HS HAE HJ K1 s3 ltac:(rewrite E34; reflexivity) Hsrc.
    * rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2
        ltac:(rewrite HU20; eapply obl_of_range; [exact Hcra | exact HUB | apply Z.le_refl | exact HOB]).
      rbn3b_kfr U9 X K1.
      lazymatch goal with HSq : st_ok_pi _ _ ?E1 _ _ |- _ =>
        assert (E25 : ew E1 25 = Z_to_bv 64 (ri_f X))
          by (cbn [ew ewset Nat.eqb]; rewrite (EE 25%nat 25%bv eq_refl); exact R25) end.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2 ltac:(fail).
         rbn3b_kfr U9 X K2.
         lazymatch type of K2 with forall a, _ -> _ -> aview _ _ ?m2 _ = _ =>
           assert (Kf : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 8 <= a < rbn_A X + 184) ->
             aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) memc1 a)
             by (intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)) end.
         assert (Hsrc : rbn3_src B G X (VAL (A_OBJ 18)))
           by (apply (rbn3b_src_img X _ HX HA Hsn); rewrite (rbn3b_stem_oth _ HN); exact I0).
         rbn3b_fin POST HS HAE HJ Kf (VAL (A_OBJ 18)) ltac:(rewrite E259; reflexivity) Hsrc.
      -- exfalso. rewrite (rbn3b_bltu_other _ (ri_f X) E25 Hfr HN) in Hc. discriminate Hc.
  + pose proof (Forall_inv Hcf) as Hc0. cbv beta in Hc0.
    assert (Vc : val_mem SEGS (mrestrict (w_H W1) memc1) (ri_said X) 1 c0).
    { destruct (garr8_nthZ SEGS _ _ _ 0 Hcg ltac:(lia) ltac:(cbn; lia)) as (Vq & _).
      rewrite Z.add_0_r in Vq. exact Vq. }
    pose proof (rbn3b_entryS W1 regs1 memc1 (rbn_A X) (ri_said X) s1 s2 s3 c0 (SOff 35 0) c0 B2 B9 B22 R20
      HA46 HA47 G6 PA HT8 HTr1 HTr2 Q1 Q2 Q3 V1' V2' V3' Hsr1 Hsr2 Hsr3 ltac:(clear - Hc0; lia)
      (rbn3b_den35 regs1 s1 s2 s3 c0) ltac:(clear - Hc0; lia) Vc) as HS.
    destruct (rbn3b_ew regs1 s1 s2 s3 c0) as (E32 & E33 & E34 & E35 & EE & ET & E259).
    assert (HEI : img_env VAL A_LIM (rbn3b_E regs1 s1 s2 s3 c0)) by (unfold rbn3b_E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs1 (map (Z_to_bv 64) [s1; s2; s3; c0])) (rbn3b_E regs1 s1 s2 s3 c0))
      by (unfold rbn3b_E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; clear - Hn; lia | reflexivity]).
    set (Eb := rbn3b_E regs1 s1 s2 s3 c0) in *. clearbody Eb.
    assert (E22 : ew Eb 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact B22).
    pose proof (rbn3b_shok Eb W1 memc1 HEI E22 HRAt HTr1 HTr2) as SHOK.
    assert (U9 : bv_unsigned (ew Eb 9) = rbn_A X)
      by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; clear - HA46 HA47; lia).
    assert (U9s : bv_unsigned (ew Eb 9) = rbn_SP X + (rbn_A X - rbn_SP X)) by (rewrite U9; ring).
    assert (HUB : U Eb rbn3b_Bx = SHADOW_OFF)
      by (unfold rbn3b_Bx; apply U_atom; [exact E22 | unfold SHADOW_OFF; clear - HA; lia]).
    assert (HU20 : U Eb (SOff 20 0) = ri_said X)
      by (apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl); exact R20 | clear - Hsr1; lia]).
    rbn3b_go RUNTO HS HJ SHOK U9s HD1 HD2
      ltac:(rewrite HU20; eapply obl_of_range; [exact Hcra | exact HUB | apply Z.le_refl | exact HOB]).
    rbn3b_kfr U9 X K1.
    assert (Hsrc : rbn3_src B G X (ri_said X))
      by (left; split; [exact Hs0 | split; [rewrite Hsd; discriminate | reflexivity]]).
    rbn3b_fin POST HS HAE HJ K1 (ri_said X) ltac:(rewrite (EE 20%nat 20%bv eq_refl); exact R20) Hsrc.
Qed.
Lemma rbn3c_stk_vis : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> ly_stk_lo ly + 64 <= a -> 0 < n -> a + n + 64 <= ly_stk_hi ly ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\
  shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros ly S W mem md a n HAR H1 Hn H2.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  (or_introl eq_refl)) as Hz. cbn [fst snd] in Hz.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as LT.
unfold page_aligned in LT. decompose [and] LT.
assert (A8 : ly_stk_lo ly mod 8 = 0).
{ match goal with H : ly_stk_lo ly mod 4096 = 0 |- _ =>
    pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as D;
    replace (ly_stk_lo ly) with (512 * (ly_stk_lo ly / 4096) * 8) by lia end.
  apply Z_mod_mult. }
assert (B8 : ly_stk_hi ly mod 8 = 0).
{ match goal with H : ly_stk_hi ly mod 4096 = 0 |- _ =>
    pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)) as D;
    replace (ly_stk_hi ly) with (512 * (ly_stk_hi ly / 4096) * 8) by lia end.
  apply Z_mod_mult. }
assert (L8 : (ly_stk_hi ly - ly_stk_lo ly) mod 8 = 0)
  by (rewrite Zminus_mod, A8, B8; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (rbn3c_zs_vis (aview SEGS (w_H W) mem) (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) a n
  A8 L8 ltac:(unfold kHighMemBeg in *; lia) ltac:(lia) Hz ltac:(lia) Hn ltac:(lia)).
Qed.
Lemma rbn3c_gm : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  alloc_ceiling + 8496 <= rbn_SP X /\ rbn_SP X <= 2 ^ 47 /\ rbn_SP X mod 16 = 0 /\
  rbn_SP X - 320 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\ rbn_A X mod 32 = 0 /\
  ly_stk_lo lyc1 <= rbn_SP X - 8496 /\ rbn_SP X <= ly_stk_hi lyc1 /\
  (forall a, rbn_SP X - 8496 <= a < rbn_SP X -> apresent (w_H W1) memc1 a) /\
  frame_addr lyc1 3 pos = rbn_F X pos /\
  (rbn_F X pos + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= rbn_F X pos) /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\
  0x7fff8000 + 512 <= rbn_SH X pos /\ rbn_SH X pos + 64 <= 0x10007fff8000 /\
  (forall i, 0 <= i < 64 -> apresent (w_H W1) memc1 (rbn_SH X pos + i)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
destruct (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _ & _ & G12 & G13 & G14 & _ & G16 & _ & G18 & G19).
pose proof asan_consts as (C1 & _).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity. rewrite WS in G1, G7, G9.
assert (HF8 : rbn_F X pos / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (HC8 : alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
assert (HF5 : 512 <= rbn_F X pos / 8) by (apply Z.div_le_lower_bound; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G16.
assert (HSH : 0x7fff8000 + 512 <= rbn_SH X pos /\ rbn_SH X pos + 64 <= 0x10007fff8000)
  by (rewrite G18; unfold SHADOW_OFF; clear - HF8 HC8 HF5; lia).
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
split; [exact G6|]. split; [exact G7|]. split; [exact G8|]. split; [exact G9|].
split; [exact (G12 3 pos)|]. split; [clear - G16; lia|]. split; [exact G13|]. split; [exact G14|].
split; [exact (proj1 HSH)|]. split; [exact (proj2 HSH)|].
intros i Hi. exact (proj1 (G19 i Hi)).
Qed.
Lemma rbn3_MS : rbn3_MS_stmt B G.
Proof.
intros X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 HX H1.
destruct H1 as ((HM & HRB & R18 & R26 & R20 & R23 & R24 & R27 & HC & HA & HSRC) & R12 & R13 & R14 & R15 & R16).
destruct (rbn3c_gm X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & SL & SH & Hpres & FA3 & Happ & HF4096 & HFceil & HSHl & HSHh & HSpr).
pose proof HM as (_ & HJ & Hperm & _ & _ & _ & _ & Hsh).
pose proof (proj1 HJ) as HAR1.
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbn3c_oks X HA) as (Hbi & Hbo).
pose proof (rbn3c_ok_rng _ Hbi) as Ri. pose proof (rbn3c_ok_rng _ Hbo) as Ro.
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rnl & _ & _ & _ & _ & _ & _ & Rdi & _ & Rdl & _).
unfold rbn3_cells1 in HC. cbn [rbn_cells] in HC. destruct HC as (Mi & Mo & _).
pose proof (rbn3c_entry1 regs1 W1 memc1 (rbn_A X) (rbn_SH X pos) (ri_i X) (ri_o X) B9 R18 R12 R13
  ltac:(clear - AR1 AR4 C1; lia) ltac:(clear - AR2 AR5; lia) AR6 ltac:(clear - HSHl; lia)
  ltac:(clear - HSHh AR1 AR4 C1; lia) ltac:(clear - Ri; lia) ltac:(clear - Ro; lia)
  (fun k Hk => Hpres (rbn_A X + k) ltac:(clear - Hk AR4 AR5; lia)) (HSpr 4 ltac:(clear; lia)) Mi Mo) as HS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
remember (rbn3c_E regs1) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold rbn3c_E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; clear - AR1 AR2 AR4 AR5 C1; lia).
assert (U18 : bv_unsigned (ew E 18) = rbn_SH X pos)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; clear - HSHl HSHh; lia).
assert (HW1 : forall a, in_wrange E (ss_mem rbn3c_ss1) a ->
  (rbn_A X + 8 <= a < rbn_A X + 184) \/ a = rbn_SH X pos + 4).
{ intros a (r & Hr & Hw). unfold rbn3c_ss1, rbn3c_stk in Hr. cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  - rewrite U9 in Hw. left. clear - Hw; lia.
  - rewrite U18 in Hw. right. clear - Hw; lia. }
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_Q1) with (BASE + (AF_reac_box_name + RBN_Q1)) by ring.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off E _ _ REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) _ _ lyc1 _ 9%nat (rbn_A X - rbn_SP X));
    [reflexivity | rewrite U9; clear; lia | cbn; clear - AR4 AR5 WS; lia | cbn; clear - AR4 AR5 WS; lia |].
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 18%nat (rbn_SH X pos)); [reflexivity | exact U18 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 3, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite FA3.
    change (fs_frame_bytes 3 / 8) with 64. change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos).
    clear - Ha; lia. }
  apply awr_ok_nil. }
pose proof (rbn3c_kept E _ (w_H W1) memc1 (ms_mem ms) _ HFr HW1) as Kr.
clear HF HFr HW1.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2.
prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4. prreg HS (22%bv : bv 5) Rs6.
prreg HS (23%bv : bv 5) Rs7. prreg HS (24%bv : bv 5) Rs8. prreg HS (25%bv : bv 5) Rs9.
prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as RA.
pose proof (st_ok_region_nth E _ _ 1 _ HS eq_refl) as RSH.
cbn [ms_mem restrict] in RA, RSH.
assert (V8 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 8) 8 (ri_display X)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 8 8 (SOff 14 0) (ri_display X) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; clear - Rdi; lia | cbn; clear; lia].
  cbn [sv_denot]. rewrite (EE 14%nat 14%bv eq_refl), R14. unfold w64.
  rewrite unsigned_lit_small, Z.add_0_r by (clear - Rdi; lia). reflexivity. }
assert (V56 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 56) 8 (ri_display_len X)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 56 8 (SOff 16 0) (ri_display_len X) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; clear - Rdl; lia | cbn; clear; lia].
  cbn [sv_denot]. rewrite (EE 16%nat 16%bv eq_refl), R16. unfold w64.
  rewrite unsigned_lit_small, Z.add_0_r by (clear - Rdl; lia). reflexivity. }
assert (V64 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 64) 8 (ri_name_len X)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 64 8 (SOff 15 0) (ri_name_len X) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; clear - Rnl; lia | cbn; clear; lia].
  cbn [sv_denot]. rewrite (EE 15%nat 15%bv eq_refl), R15. unfold w64.
  rewrite unsigned_lit_small, Z.add_0_r by (clear - Rnl; lia). reflexivity. }
assert (V80 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 80) 8 (ri_i X)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 80 8 (SOff 12 0) (ri_i X) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; clear - Ri; lia | cbn; clear; lia].
  cbn [sv_denot]. rewrite (EE 12%nat 12%bv eq_refl), R12. unfold w64.
  rewrite unsigned_lit_small, Z.add_0_r by (clear - Ri; lia). reflexivity. }
assert (V88 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 88) 8 (ri_o X)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 88 8 (SOff 13 0) (ri_o X) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; clear - Ro; lia | cbn; clear; lia].
  cbn [sv_denot]. rewrite (EE 13%nat 13%bv eq_refl), R13. unfold w64.
  rewrite unsigned_lit_small, Z.add_0_r by (clear - Ro; lia). reflexivity. }
assert (V152 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 152) 8 (rbn_F X pos + 32)).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 152 8 (SOff 19 32) (rbn_F X pos + 32) RA U9);
    [repeat (first [left; reflexivity | right]) | | cbn; clear - HF4096 HFceil C1; lia | cbn; clear; lia].
  cbn [sv_denot]. rewrite (EE 19%nat 19%bv eq_refl), B19. unfold w64.
  rewrite unsigned_lit_small by (clear - HF4096 HFceil C1; lia). reflexivity. }
assert (V160 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms)) (rbn_A X + 160) 8 5).
{ apply (field_of_region E _ 9 (rbn_A X) _ 8 184 8 184 160 8 (SLit 5) 5 RA U9);
    [repeat (first [left; reflexivity | right]) | reflexivity | cbn; clear; lia | cbn; clear; lia]. }
assert (VSH4 : aview SEGS (w_H W1) (ms_mem ms) (rbn_SH X pos + 4) = Some 5).
{ apply aview_of_val_mem1; [|clear; lia].
  exact (field_of_region E _ 18 (rbn_SH X pos) _ 0 64 4 5 4 1 (SLit 5) 5 RSH U18
    ltac:(left; reflexivity) eq_refl ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)). }
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA IS___asan_memset) AMEMSET W1 (ms_regs ms) (ms_mem ms)
    REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X) [(3, pos)]
    lyc1 Sc1 _ 0 (rbn_A X + 168) 0 16 (rbn_A X - rbn_SP X) _ HJ).
  - rewrite Ra0, U9. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - clear; lia.
  - clear - AR1 AR4 C1; lia.
  - clear - AR2 AR5; lia.
  - unfold spZ. rewrite Rsp, (EE 2%nat 2%bv eq_refl), B2. unfold w64.
    rewrite unsigned_lit_small by (clear - AR1 AR2 AR4 AR5 C1; lia). clear; lia.
  - exact (rbn3c_mod16 _ _ AR6 AR3).
  - clear - AR5; lia.
  - rewrite Hes, WS. clear - AR4; lia.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact B3.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact B4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - intros a Ha. split; [left; rewrite WS; clear - Ha AR4 AR5; lia | rewrite Hes; clear - Ha; lia].
  - right. unfold kHighMemBeg, kHighMemEnd. clear - AR1 AR2 AR4 AR5 C1; lia.
  - exact (proj1 (rbn3c_stk_vis lyc1 Sc1 W1 _ _ (rbn_A X + 168) 16 (proj1 HJ)
      ltac:(clear - SL AR4; lia) ltac:(clear; lia) ltac:(clear - SH AR5; lia))).
  - intros _. exact (proj2 (rbn3c_stk_vis lyc1 Sc1 W1 _ _ (rbn_A X + 168) 16 (proj1 HJ)
      ltac:(clear - SL AR4; lia) ltac:(clear; lia) ltac:(clear - SH AR5; lia))).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfrm & Hpres2).
apply SRr_ret.
assert (Kc : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 168 <= a < rbn_A X + 184) -> ~ (rbn_A X - 4096 <= a < rbn_A X) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a).
{ intros a Ha H1 H2. apply Hfrm; [exact Ha | clear - H1; lia | rewrite Hes; clear - H2; lia]. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 4096 <= a < rbn_A X + 184) -> a <> rbn_SH X pos + 4 ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha H1 H2. rewrite (Kc a Ha) by (clear - H1; lia). apply Kr; [exact Ha|]. clear - H1 H2; lia. }
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (rbn3c_pres _ _ r HP2 Hr)).
unfold rbn3_at2. exists regs2, lyc1, Sc1, mem2, md2.
split.
{ unfold rbn_cfg, cfg_at, w64.
  replace (BASE + AF_reac_box_name + RBN_Q2) with (BASE + 9628) by (unfold AF_reac_box_name, RBN_Q2; ring).
  reflexivity. }
unfold rbn3_s2, rbn3_core. split; [|rewrite PR, Rs9, (EE 19%nat 19%bv eq_refl), B19 by rbn3c_cs; unfold w64;
  rewrite unsigned_lit_small by (clear - HF4096 HFceil C1; lia); reflexivity].
split.
{ apply (rbn3_mid_upd X pos lyc1 Sc1 W1 memc1 mdc1 (rbn_sh false false false false) lyc1 Sc1 mem2 md2
    (rbn_sh true false false false) HX HM HJ2 (Permutation_refl _)).
  - intros a Hi _ _. pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    apply KEEP; clear - Hlow AR1 AR4 HSHl C1; lia.
  - intros a (q & N & Hin & Hr).
    assert (Hin1 : In (q, N) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR1 Hin1) as (_ & Hb4 & Hbc & Hbapp & _).
    pose proof (req_size_pos N ltac:(clear - Hr; lia)) as (Hq1 & Hq2).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
    apply KEEP; clear - Hr Hb4 Hbc Hbapp Hq1 Hq2 AR1 AR4 HSHl HSHh C1; lia.
  - intros a Ha. apply KEEP; clear - Ha AR1 AR2 AR5 HSHh C1; lia.
  - intros a Ha. apply KEEP; clear - Ha Happ HF4096 HFceil AR1 AR4 HSHl HSHh C1; lia.
  - intros j Hj. rewrite rbn3c_sh_len in Hj.
    destruct (Z.eq_dec j 4) as [-> | Hj4].
    + rewrite (Kc (rbn_SH X pos + 4)) by (clear - HSHl HSHh AR1 AR4 C1; lia). rewrite VSH4. reflexivity.
    + rewrite (KEEP (rbn_SH X pos + j)) by (clear - Hj Hj4 HSHl HSHh AR1 AR4 C1; lia).
      rewrite (Hsh j) by (rewrite rbn3c_sh_len; clear - Hj; lia).
      rewrite rbn3c_sh_w4 by (clear - Hj Hj4; lia). reflexivity. }
split.
{ split; [rewrite PR, Rsp, (EE 2%nat 2%bv eq_refl) by rbn3c_cs; exact B2|].
  split; [rewrite PR, Rgp, (EE 3%nat 3%bv eq_refl) by rbn3c_cs; exact B3|].
  split; [rewrite PR, Rtp, (EE 4%nat 4%bv eq_refl) by rbn3c_cs; exact B4|].
  split; [rewrite PR, Rs0, (EE 8%nat 8%bv eq_refl) by rbn3c_cs; exact B8|].
  split; [rewrite PR, Rs1, (EE 9%nat 9%bv eq_refl) by rbn3c_cs; exact B9|].
  split; [rewrite PR, Rs3, (EE 19%nat 19%bv eq_refl) by rbn3c_cs; exact B19|].
  rewrite PR, Rs6, (EE 22%nat 22%bv eq_refl) by rbn3c_cs; exact B22. }
split; [rewrite PR, Rs2, (EE 18%nat 18%bv eq_refl) by rbn3c_cs; exact R18|].
split; [rewrite PR, Rs10, (EE 26%nat 26%bv eq_refl) by rbn3c_cs; exact R26|].
split; [rewrite PR, Rs4, (EE 20%nat 20%bv eq_refl) by rbn3c_cs; exact R20|].
split; [rewrite PR, Rs7, (EE 23%nat 23%bv eq_refl) by rbn3c_cs; exact R23|].
split; [rewrite PR, Rs8, (EE 24%nat 24%bv eq_refl) by rbn3c_cs; exact R24|].
split; [rewrite PR, Rs11, (EE 27%nat 27%bv eq_refl) by rbn3c_cs; exact R27|].
split; [|split; [exact HA | exact HSRC]].
unfold rbn3_cells2. cbn [rbn_cells].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; clear - Hk AR1 AR2 AR4 AR5 C1; lia | exact V8]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; clear - Hk AR1 AR2 AR4 AR5 C1; lia | exact V56]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; clear - Hk AR1 AR2 AR4 AR5 C1; lia | exact V64]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; clear - Hk AR1 AR2 AR4 AR5 C1; lia | exact V80]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; clear - Hk AR1 AR2 AR4 AR5 C1; lia | exact V88]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; clear - Hk AR1 AR2 AR4 AR5 C1; lia | exact V152]|].
split; [apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms) mem2); [intros k Hk; apply Kc; clear - Hk AR1 AR2 AR4 AR5 C1; lia | exact V160]|].
split; [apply val_mem_zero8; intros i Hi; rewrite (Heff i) by (clear - Hi; lia); reflexivity|].
split; [|exact I].
apply rbn3c_val_mem_zero4. intros i Hi. replace (rbn_A X + 176 + i) with (rbn_A X + 168 + (8 + i)) by ring.
rewrite (Heff (8 + i)) by (clear - Hi; lia). reflexivity.
Qed.
Lemma rbn3_P4 : rbn3_P4_stmt B G.
Proof.
intros X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 HX H5.
destruct H5 as ((HM & HRB & R18 & R26 & R20 & R23 & R24 & R27 & HC & HA & HSRC) & R25 & R12 & HW4).
destruct (rbn3c_gm X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & SL & SH & Hpres & FA3 & Happ & HF4096 & HFceil & HSHl & HSHh & HSpr).
pose proof HM as (_ & HJ & Hperm & _ & _ & _ & _ & Hsh).
pose proof (proj1 HJ) as HAR1.
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbn3c_oks X HA) as (Hbi & Hbo).
assert (Hw4l : length (rbm_w4 X) = 4%nat) by exact (bn_w4_length _ _ Hbi Hbo).
pose proof (rbn3c_entry5 regs1 W1 memc1 (rbn_SH X pos) R18 ltac:(clear - HSHl; lia) ltac:(clear - HSHh; lia)
  (fun k Hk => HSpr k ltac:(clear - Hk; lia))) as HS.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
remember (rbn3c_E regs1) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold rbn3c_E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (U18 : bv_unsigned (ew E 18) = rbn_SH X pos)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; clear - HSHl HSHh; lia).
assert (HW5 : forall a, in_wrange E (ss_mem rbn3c_ss5) a -> rbn_SH X pos + 8 <= a < rbn_SH X pos + 11).
{ intros a (r & Hr & Hw). unfold rbn3c_ss5 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  rewrite U18 in Hw. clear - Hw; lia. }
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_reac_box_name + RBN_Q5) with (BASE + (AF_reac_box_name + RBN_Q5)) by ring.
paj_run_to_sh RUNTOP HS HJ (AF_reac_box_name + RBN_Q6).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 18%nat (rbn_SH X pos)); [reflexivity | exact U18 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 3, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite FA3.
    change (fs_frame_bytes 3 / 8) with 64. change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos).
    clear - Ha; lia. }
  apply awr_ok_nil. }
pose proof (rbn3c_kept E _ (w_H W1) memc1 (ms_mem ms) _ HFr HW5) as K.
clear HF HFr HW5.
apply SRr_ret. pmkst HS.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (18%bv : bv 5) Rs2. prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4.
prreg HS (22%bv : bv 5) Rs6. prreg HS (23%bv : bv 5) Rs7. prreg HS (24%bv : bv 5) Rs8.
prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
pose proof (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl) as RSH. cbn [ms_mem restrict] in RSH.
assert (VSH : forall j, 8 <= j < 11 -> aview SEGS (w_H W1) (ms_mem ms) (rbn_SH X pos + j) = Some 0).
{ intros j Hj. apply aview_of_val_mem1; [|clear; lia].
  apply (field_of_region E _ 18 (rbn_SH X pos) _ 0 64 8 11 j 1 (SLit 0) 0 RSH U18);
    [| reflexivity | cbn; clear; lia | cbn; clear; lia].
  cbn [In]. assert (j = 10 \/ j = 9 \/ j = 8) as Hc by (clear - Hj; lia).
  destruct Hc as [-> | [-> | ->]]; repeat (first [left; reflexivity | right]). }
exists (ms_regs ms), lyc1, Sc1, (ms_mem ms), (with_vm_backing (m_vm_lazy mdc1) mat mdc1).
split.
{ unfold rbn_cfg, cfg_at, w64.
  replace (BASE + AF_reac_box_name + RBN_Q6) with (BASE + 9704) by (unfold AF_reac_box_name, RBN_Q6; ring).
  reflexivity. }
unfold rbn3_s6, rbn3_core.
split; [split|].
{ apply (rbn3_mid_upd X pos lyc1 Sc1 W1 memc1 mdc1 (rbn_sh true false false false) lyc1 Sc1 (ms_mem ms)
    (with_vm_backing (m_vm_lazy mdc1) mat mdc1) (rbn_sh true true false false) HX HM HJ (Permutation_refl _)).
  - intros a Hi _ _. pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    apply K; clear - Hlow HSHl; lia.
  - intros a (q & N & Hin & Hr).
    assert (Hin1 : In (q, N) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR1 Hin1) as (_ & Hb4 & Hbc & Hbapp & _).
    pose proof (req_size_pos N ltac:(clear - Hr; lia)) as (Hq1 & Hq2).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
    apply K; clear - Hr Hb4 Hbc Hbapp Hq1 Hq2 HSHl HSHh C1; lia.
  - intros a Ha. apply K; clear - Ha AR1 AR2 HSHh C1; lia.
  - intros a Ha. apply K; clear - Ha Happ HF4096 HFceil HSHl HSHh C1; lia.
  - intros j Hj. rewrite rbn3c_sh_len in Hj.
    destruct (Z_lt_le_dec j 8) as [Hj1 | Hj1]; [|destruct (Z_lt_le_dec j 11) as [Hj2 | Hj2]].
    + rewrite (K (rbn_SH X pos + j)) by (clear - Hj Hj1 HSHl HSHh; lia).
      rewrite (Hsh j) by (rewrite rbn3c_sh_len; clear - Hj; lia).
      rewrite rbn3c_sh_nb by (clear - Hj Hj1; lia). reflexivity.
    + rewrite (VSH j) by (clear - Hj1 Hj2; lia). rewrite rbn3c_sh_nb0 by (clear - Hj1 Hj2; lia). reflexivity.
    + rewrite (K (rbn_SH X pos + j)) by (clear - Hj Hj2 HSHl HSHh; lia).
      rewrite (Hsh j) by (rewrite rbn3c_sh_len; clear - Hj; lia).
      rewrite rbn3c_sh_nb by (clear - Hj Hj2; lia). reflexivity. }
{ split.
  { split; [rewrite Rsp, (EE 2%nat 2%bv eq_refl); exact B2|].
    split; [rewrite Rgp, (EE 3%nat 3%bv eq_refl); exact B3|].
    split; [rewrite Rtp, (EE 4%nat 4%bv eq_refl); exact B4|].
    split; [rewrite Rs0, (EE 8%nat 8%bv eq_refl); exact B8|].
    split; [rewrite Rs1, (EE 9%nat 9%bv eq_refl); exact B9|].
    split; [rewrite Rs3, (EE 19%nat 19%bv eq_refl); exact B19|].
    rewrite Rs6, (EE 22%nat 22%bv eq_refl); exact B22. }
  split; [rewrite Rs2, (EE 18%nat 18%bv eq_refl); exact R18|].
  split; [rewrite Rs10, (EE 26%nat 26%bv eq_refl); exact R26|].
  split; [rewrite Rs4, (EE 20%nat 20%bv eq_refl); exact R20|].
  split; [rewrite Rs7, (EE 23%nat 23%bv eq_refl); exact R23|].
  split; [rewrite Rs8, (EE 24%nat 24%bv eq_refl); exact R24|].
  split; [rewrite Rs11, (EE 27%nat 27%bv eq_refl); exact R27|].
  split; [|split; [exact HA | exact HSRC]].
  apply (rbn3c_cells_kept (w_H W1) (w_H W1) memc1 (ms_mem ms)); [|exact HC].
  intros a n v k Hin Hk. pose proof (rbn3c_cells5_rng X pos a n v Hin) as Hr.
  apply K; clear - Hr Hk AR1 AR2 AR4 AR5 HSHh C1; lia. }
split; [rewrite Rs9, (EE 25%nat 25%bv eq_refl); exact R25|].
split; [rewrite Ra2, (EE 12%nat 12%bv eq_refl); exact R12|].
apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HW4|].
intros a Ha. rewrite length_app, Hw4l in Ha. cbn [length] in Ha.
apply (mbyte_of_aview SEGS). apply K; clear - Ha Happ HF4096 HFceil HSHl HSHh C1; lia.
Qed.
Definition rbn3d_atc (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (r A v : Z)
  : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model),
    c' = cfg_at SEGS A_sb_dec regsT memT mdT /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k /\
    aregs_preserved regs regsT /\
    getr regsT 1 = w64 (BASE + AF_reac_box_name + r) /\ getr regsT 10 = w64 (A + 152) /\
    getr regsT 11 = w64 v /\ getr regsT 12 = w64 2 /\
    (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) memT a = aview SEGS (w_H W) memc a).
Lemma rbn3d_run : forall q off r (A v : Z) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word),
  (q = RBN_Q2 /\ off = 80 /\ r = RBN_Q3) \/ (q = RBN_Q3 /\ off = 88 /\ r = RBN_Q4) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> 2 ^ 46 <= A <= 2 ^ 47 -> A mod 32 = 0 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + off) 8 v -> 0 <= v < 2 ^ 64 ->
  SRr SEGS W (rbn_cfg q regs memc mdc) (rbn3d_atc STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs r A v).
Proof.
intros q off r A v STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Hq HJ H9 HA HA32 Mv Hv.
pose proof (rbn3d_entry q off A v regs W memc
  ltac:(destruct Hq as [(_ & -> & _) | (_ & -> & _)]; [left | right]; reflexivity) H9 HA HA32 Mv Hv) as HS.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
assert (HAG : env_agree 32 (Ereg regs [Z_to_bv 64 v]) (rbn3d_E regs v))
  by (unfold rbn3d_E; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (rbn3d_E regs v) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rbn3d_E; apply Eimg_env).
assert (EE : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr)
  by (intros nn rr Hn; subst E; unfold rbn3d_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 v)
  by (subst E; unfold rbn3d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
clear HE.
assert (AFv : AF_reac_box_name = 8984) by reflexivity.
assert (Q3v : RBN_Q3 = 660) by reflexivity.
assert (Q4v : RBN_Q4 = 676) by reflexivity.
destruct Hq as [(-> & -> & ->) | (-> & -> & ->)].
all: unfold rbn_cfg, cfg_at, w64.
all: rewrite <- (Z.add_assoc BASE AF_reac_box_name).
all: paj_run_shc RUNP RUNC HS HJ.
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0);
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] end).
all: pose proof (aview_kept_frame (segs := SEGS) E _ (w_H W) memc (ms_mem ms) 0 HFr ltac:(lia)) as TK0.
all: assert (TK : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
  by (apply TK0; intros a _ (rr & Hr & Hw); unfold rbn3d_ss, rbn3d_rs in Hr; cbn [ss_mem In] in Hr;
      destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; clear - Hw; lia).
all: clear TK0 HF HFr HG.
all: prreg HS (10%bv : bv 5) Ra0.
all: prreg HS (11%bv : bv 5) Ra1.
all: prreg HS (12%bv : bv 5) Ra2.
all: prreg HS (1%bv : bv 5) Rra.
all: assert (HPRES : aregs_preserved regs (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok SEGS (w_H W) E _ _ regs [Z_to_bv 64 v] HS HAG); vm_compute; reflexivity).
all: apply SRr_ret.
all: pmkst HS.
all: unfold rbn3d_atc.
all: split; [reflexivity|].
all: exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
all: split; [unfold cfg_at, A_sb_dec, w64; rewrite (PSIG IS_sb_dec AF_sb_dec eq_refl); reflexivity|].
all: split; [exact HJ|].
all: split; [exact HPRES|].
all: split; [rewrite Rra; unfold w64; f_equal; clear - AFv Q3v Q4v; lia|].
all: split; [rewrite Ra0, (EE 9%nat 9%bv eq_refl), H9; unfold w64; rewrite unsigned_lit_small by (clear - HA; lia);
  reflexivity|].
all: split; [rewrite Ra1, E32; reflexivity|].
all: split; [rewrite Ra2; reflexivity|].
all: exact TK.
Qed.
Definition rbn3d_post (X : rbn_in) (pos P n v r : Z) (W1 : world SEGS) (memc1 : word -> option byte)
  : world SEGS -> config -> Prop :=
  fun W2 c2 => exists (regs2 : bvmap 5 word) lyc2 Sc2 memc2 mdc2,
    c2 = rbn_cfg r regs2 memc2 mdc2 /\
    rbn3_core B G X pos P (rbn_sh true false false false) (rbn3_cells2 X pos (n + 2)) regs2 lyc2 Sc2 W2 memc2 mdc2 /\
    getr regs2 25 = w64 (rbn_F X pos + 32) /\
    garr8 SEGS (mrestrict (w_H W2) memc2) (rbn_F X pos + 32 + n) (bn_dec v 2) /\
    (forall a, rbn_F X pos + 32 <= a < rbn_F X pos + 32 + n ->
       aview SEGS (w_H W2) memc2 a = aview SEGS (w_H W1) memc1 a).
Lemma rbn3d_call : forall X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 n v r (regsT : bvmap 5 word) memT mdT,
  rbn_cx B G X ->
  rbn3_core B G X pos P (rbn_sh true false false false) (rbn3_cells2 X pos n) regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  getr regs1 25 = w64 (rbn_F X pos + 32) ->
  0 <= n <= 2 -> bn_ok v = true -> 0 <= r < 2 ^ 20 -> r mod 2 = 0 ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memT mdT 0 ->
  aregs_preserved regs1 regsT ->
  getr regsT 1 = w64 (BASE + AF_reac_box_name + r) ->
  getr regsT 10 = w64 (rbn_A X + 152) -> getr regsT 11 = w64 v -> getr regsT 12 = w64 2 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) memT a = aview SEGS (w_H W1) memc1 a) ->
  SRr SEGS W1 (cfg_at SEGS A_sb_dec regsT memT mdT) (rbn3d_post X pos P n v r W1 memc1).
Proof.
intros X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 n v r regsT memT mdT HX Hcore R25 Hn Hv Hr Hr2 HJT HPT T1 T10 T11 T12 TK.
destruct Hcore as (HM & HRB & R18 & R26 & R20 & R23 & R24 & R27 & HC & HA & Hsrc).
pose proof (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true false false false) HX HM)
  as (G1 & G2 & _ & G4 & G5 & G6 & G7 & G8 & _ & G10 & G11 & G12 & G13 & G14 & G15 & G16 & _ & G18 & _).
pose proof HM as (_ & _ & Hperm1 & _ & _ & _ & _ & Hsh1).
pose proof HRB as (R2 & R3 & R4 & R8 & R9 & R19 & R22).
cbn [rbn_cells rbn3_cells2] in HC.
destruct HC as (C8 & C56 & C64 & C80 & C88 & C152 & C160 & C168 & C176 & _).
pose proof HJT as (HART & _ & _ & _ & _ & _ & HnevT & _ & _ & _ & _ & _ & _ & HpresT & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hnev0 & Hbb0).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as (HB0 & HB1 & _).
destruct (rbn3d_dec2 v Hv) as (HDv & HLv & Rv).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
assert (SBS : SB_DEC_STK = 4208) by reflexivity.
assert (ES : ESTACK = 4096) by reflexivity.
assert (AFv : AF_reac_box_name = 8984) by reflexivity.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite WS in G1, G7.
assert (NUM : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\ alloc_ceiling + 8496 <= rbn_SP X /\
  rbn_SP X <= 2 ^ 47 /\ rbn_SP X - 320 <= rbn_A X /\ rbn_A X + 288 <= rbn_SP X /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ 0 <= n <= 2)
  by (clear - C1 G1 G2 G4 G5 G13 G14 Hn; lia).
pose proof (rbn3d_shsep (rbn_F X pos) G13 G14 G16 C1) as SHN. rewrite <- G18 in SHN.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite G10; left; reflexivity).
assert (FA : frame_addr lyc1 3 pos = rbn_F X pos) by exact (G12 3 pos).
assert (SPT : spZ regsT = rbn_A X).
{ unfold spZ. rewrite (rbn3d_pres_get regs1 regsT _ HPT) by rbn3d_cs. rewrite R2. unfold w64.
  apply unsigned_lit_small. clear - NUM. lia. }
assert (Hacc : sb_dec_c.sb_dec_acc v 2 5 n = 2).
{ unfold sb_dec_c.sb_dec_acc, sb_dec_c.sb_dec_room. rewrite HDv, HLv.
  destruct (Z.leb_spec (n + 1) 5) as [Hl | Hl]; clear - Hn Hl; lia. }
assert (Hov : (sb_dec_c.sb_dec_room 5 n <? Z.of_nat (length (sb_dec_c.sb_dec_D v 2))) = false).
{ unfold sb_dec_c.sb_dec_room. rewrite HDv, HLv. apply Z.ltb_ge.
  destruct (Z.leb_spec (n + 1) 5) as [Hl | Hl]; clear - Hn Hl; lia. }
assert (NE : forall a, (a < rbn_A X + 168 \/ rbn_A X + 180 <= a) ->
  (a < rbn_F X pos + 32 + n \/ rbn_F X pos + 32 + n + 2 <= a) ->
  ~ tsb_dec_wr (rbn_A X + 152) (rbn_F X pos + 32) n (sb_dec_c.sb_dec_acc v 2 5 n) a).
{ intros a H1 H2. unfold tsb_dec_wr. rewrite Hacc. clear - H1 H2. lia. }
assert (VT : forall a w x, val_mem SEGS (mrestrict (w_H W1) memc1) a w x -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W1) memT) a w x).
{ intros a w x Hm H0 H1. apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 memT); [|exact Hm].
  intros kk Hk. apply TK. clear - H0 H1 Hk. lia. }
eapply SRr_mono.
{ apply (HSB REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memT mdT 0 regsT (rbn_A X + 152) v 2 (rbn_F X pos + 32) 5 n 0 HJT).
  - rewrite T1. unfold w64. rewrite <- Z.add_assoc.
    apply ret_ok_codeptr_v; [rewrite AFv; clear - Hr; lia | rewrite Zplus_mod, Hr2; reflexivity].
  - unfold raZ. rewrite T1. unfold w64. rewrite unsigned_lit_small; rewrite AFv; clear - HB0 HB1 Hr; lia.
  - rewrite (rbn3d_pres_get regs1 regsT _ HPT) by rbn3d_cs. exact R3.
  - rewrite (rbn3d_pres_get regs1 regsT _ HPT) by rbn3d_cs. exact R4.
  - rewrite SPT. apply rbn3d_m16. exact G6.
  - rewrite SPT, WS, SBS. clear - NUM. lia.
  - rewrite SPT. clear - NUM. lia.
  - exact T10.
  - exact T11.
  - exact T12.
  - clear - Rv. lia.
  - right. reflexivity.
  - rewrite Zplus_mod, (mod32_mod8 _ G6). reflexivity.
  - clear - NUM. lia.
  - clear - NUM. lia.
  - left. rewrite SPT. clear - NUM. lia.
  - unfold tsb_dec_rec_at. clear - NUM G7 G8. lia.
  - exact (VT _ _ _ C152 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia)).
  - replace (rbn_A X + 152 + 8) with (rbn_A X + 160) by ring.
    exact (VT _ _ _ C160 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia)).
  - replace (rbn_A X + 152 + 16) with (rbn_A X + 168) by ring.
    exact (VT _ _ _ C168 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia)).
  - replace (rbn_A X + 152 + 24) with (rbn_A X + 176) by ring.
    exact (VT _ _ _ C176 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia)).
  - clear - NUM. lia.
  - clear - NUM. lia.
  - clear - NUM. lia.
  - clear - NUM. lia.
  - clear - NUM. lia.
  - unfold twr_ok. intros a Ha. rewrite SPT.
    split; [left; rewrite WS; clear - NUM Ha; lia|].
    split; [apply HpresT; rewrite WS; clear - NUM Ha; lia|].
    split; [apply (al_stack _ _ LAWS lyc1 Sc1 W1 memT mdT a HART); clear - NUM G7 G8 Ha; lia|].
    rewrite ES. clear - NUM Ha. lia.
  - intros _. rewrite Hacc.
    split; [clear - NUM; lia|]. split; [clear - NUM; lia|].
    split.
    { unfold tdst_ok. intros a Ha. right. exists 3, pos. split; [exact Hin3|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite FA, Hfb3. clear - NUM Ha. lia. }
    split.
    { intros x Hx. destruct (rbn3d_gran (rbn_F X pos) x G15 ltac:(clear - Hx Hn; lia)) as (Gd & Gm).
      exists 5. split.
      - unfold shadow_of_addr. rewrite Gd.
        replace (SHADOW_OFF + (rbn_F X pos / 8 + 4)) with (rbn_SH X pos + 4) by (rewrite G18; ring).
        rewrite TK by (clear - SHN NUM; lia).
        exact (Hsh1 4 ltac:(rewrite rbn3d_sh_len; lia)).
      - right. rewrite Gm. clear - Hx Hn. lia. }
    split.
    { unfold twr_ok. intros a Ha. rewrite SPT.
      destruct (al_frames _ _ LAWS lyc1 Sc1 W1 memT mdT 3 pos HART Hin3) as (_ & _ & Hfb & _).
      rewrite FA, Hfb3 in Hfb.
      split.
      { right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
        unfold in_zr. cbn [fst snd]. rewrite FA, Hfb3. clear - NUM Ha. lia. }
      split; [exact (proj1 (Hfb a ltac:(clear - NUM Ha; lia)))|].
      split; [exact (proj2 (Hfb a ltac:(clear - NUM Ha; lia)))|].
      rewrite ES. clear - NUM Ha. lia. }
    split; [left; clear - NUM; lia|].
    left. rewrite SPT, SBS. clear - NUM. lia.
  - exact G11.
  - unfold EV_SB_DEC. unfold EV_REAC_BOX_NAME in Hnev0. clear - HnevT Hnev0. lia.
  - unfold LIVE_SB_DEC. rewrite (blocks_bytes_bsum B lyc1 Sc1), (bsum_perm _ _ Hperm1),
      <- (blocks_bytes_bsum B (ri_lyc X) (ri_Sc X)).
    unfold LIVE_REAC_BOX_NAME in Hbb0. clear - Hbb0. lia. }
intros W2 c2 _ (-> & ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hperm2 & HK2 & V0 & V8 & V16 & V24 & HD).
destruct HK2 as (K1 & K2 & K3 & K4 & _ & _).
rewrite Hacc in V16, HD. rewrite Hov in V24. rewrite HDv in HD.
change (Z.to_nat 2) with 2%nat in HD.
rewrite firstn_all2 in HD by (rewrite HLv; lia).
replace (rbn_A X + 152 + 8) with (rbn_A X + 160) in V8 by ring.
replace (rbn_A X + 152 + 16) with (rbn_A X + 168) in V16 by ring.
replace (rbn_A X + 152 + 24) with (rbn_A X + 176) in V24 by ring.
assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPT HP2).
assert (PG : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regs1 rr)
  by (intros rr Hrr; exact (rbn3d_pres_get regs1 regs2 rr HP12 Hrr)).
assert (VK : forall a w x, val_mem SEGS (mrestrict (w_H W1) memc1) a w x -> rbn_A X <= a ->
  a + Z.of_nat w <= rbn_A X + 168 -> val_mem SEGS (mrestrict (w_H W1) mem2) a w x).
{ intros a w x Hm H0 H1. apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact Hm].
  intros kk Hk. rewrite (K1 (a + kk)).
  - apply TK. clear - NUM H0 H1 Hk. lia.
  - clear - NUM H0 H1 Hk. lia.
  - rewrite SPT, SBS. clear - NUM H0 H1 Hk. lia.
  - apply NE; clear - NUM H0 H1 Hk; lia. }
unfold rbn3d_post. exists regs2, ly2, S2, mem2, md2.
split; [unfold rbn_cfg, cfg_at; rewrite T1; reflexivity|].
split.
{ split.
  { apply (rbn3_mid_upd X pos lyc1 Sc1 W1 memc1 mdc1 (rbn_sh true false false false) ly2 S2 mem2 md2
      (rbn_sh true false false false) HX HM HJ2 Hperm2).
    - intros a Hi Hns He. rewrite (K3 a Hi Hns He). apply TK.
      pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. clear - Hl. lia.
    - intros a (q0 & N & Hin & Hq).
      assert (Hin1 : In (q0, N) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm1) Hin).
      destruct (al_blocks _ _ LAWS lyc1 Sc1 W1 memT mdT q0 N HART Hin1) as (_ & Hq4 & Hqc & _).
      assert (Hrq : N <= req_size N)
        by (unfold req_size; destruct (Z.eqb_spec N 0) as [E0 | E0]; clear - E0; lia).
      replace a with (q0 + (a - q0)) by ring.
      rewrite (K2 q0 N (a - q0) Hin1 ltac:(clear - Hq Hrq; lia)).
      + apply TK. clear - Hq Hq4 Hqc Hrq NUM. lia.
      + apply NE; [left; clear - Hq Hrq Hqc NUM; lia|].
        destruct (Z_lt_le_dec (q0 + (a - q0)) (rbn_F X pos + 32 + n)) as [Hl | Hl]; [left; exact Hl|].
        destruct (Z_lt_le_dec (q0 + (a - q0)) (rbn_F X pos + 32 + n + 2)) as [Hl2 | Hl2]; [|right; exact Hl2].
        exfalso.
        apply (block_not_frame_zone SEGS B LAWS lyc1 Sc1 W1 memT mdT q0 N (a - q0) 3 pos HART Hin1 Hin3
          ltac:(clear - Hq Hrq; lia)).
        left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite FA, Hfb3. clear - Hl Hl2 NUM. lia.
    - intros a Ha. rewrite (K1 a).
      + apply TK. clear - Ha NUM. lia.
      + clear - Ha NUM. lia.
      + rewrite SPT, SBS. clear - Ha NUM. lia.
      + apply NE; clear - Ha NUM; lia.
    - intros a Ha. rewrite (K4 3 pos a Hin3).
      + apply TK. clear - Ha NUM. lia.
      + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite FA, Hfb3. clear - Ha NUM. lia.
      + apply NE; clear - Ha NUM; lia.
    - intros j Hj.
      assert (Hj' : 0 <= j < 64) by (rewrite rbn3d_sh_len in Hj; clear - Hj; lia).
      rewrite (K4 3 pos (rbn_SH X pos + j) Hin3).
      + rewrite TK by (clear - Hj' SHN NUM; lia). exact (Hsh1 j Hj).
      + right. unfold in_zr. cbn [fst snd]. rewrite FA. change (shadow_addr (rbn_F X pos)) with (rbn_SH X pos).
        rewrite Hfb3. change (512 / 8) with 64. clear - Hj'. lia.
      + apply NE; clear - Hj' SHN NUM; lia. }
  split.
  { unfold rbn_rbase.
    split; [rewrite PG by rbn3d_cs; exact R2|].
    split; [rewrite PG by rbn3d_cs; exact R3|].
    split; [rewrite PG by rbn3d_cs; exact R4|].
    split; [rewrite PG by rbn3d_cs; exact R8|].
    split; [rewrite PG by rbn3d_cs; exact R9|].
    split; [rewrite PG by rbn3d_cs; exact R19|].
    rewrite PG by rbn3d_cs; exact R22. }
  split; [rewrite PG by rbn3d_cs; exact R18|].
  split; [rewrite PG by rbn3d_cs; exact R26|].
  split; [rewrite PG by rbn3d_cs; exact R20|].
  split; [rewrite PG by rbn3d_cs; exact R23|].
  split; [rewrite PG by rbn3d_cs; exact R24|].
  split; [rewrite PG by rbn3d_cs; exact R27|].
  split.
  { cbn [rbn_cells rbn3_cells2].
    split; [exact (VK _ _ _ C8 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia))|].
    split; [exact (VK _ _ _ C56 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia))|].
    split; [exact (VK _ _ _ C64 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia))|].
    split; [exact (VK _ _ _ C80 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia))|].
    split; [exact (VK _ _ _ C88 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia))|].
    split; [exact V0|]. split; [exact V8|]. split; [exact V16|]. split; [exact V24 | exact I]. }
  split; [exact HA | exact Hsrc]. }
split; [rewrite PG by rbn3d_cs; exact R25|].
split; [exact HD|].
intros a Ha. rewrite (K4 3 pos a Hin3).
- apply TK. clear - Ha NUM. lia.
- left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite FA, Hfb3. clear - Ha NUM. lia.
- apply NE; clear - Ha NUM; lia.
Qed.
Lemma rbn3_D1 : rbn3_D1_stmt B G.
Proof.
intros X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 HX (Hcore & R25).
pose proof Hcore as (HM & HRB & _ & _ & _ & _ & _ & _ & HC & HA & _).
pose proof (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (G1 & G2 & _ & G4 & G5 & G6 & _).
pose proof HM as (_ & HJ1 & _).
pose proof HRB as (_ & _ & _ & _ & R9 & _).
cbn [rbn_cells rbn3_cells2] in HC. destruct HC as (_ & _ & _ & C80 & _).
destruct (rbn3d_args X HA) as (Hbi & _). destruct (rbn3d_dec2 _ Hbi) as (_ & _ & Ri).
pose proof asan_consts as (C1 & _).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
eapply SRr_bind.
{ apply (rbn3d_run RBN_Q2 80 RBN_Q3 (rbn_A X) (ri_i X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs1
    (or_introl (conj eq_refl (conj eq_refl eq_refl))) HJ1 R9);
    [rewrite WS in G1; clear - C1 G1 G2 G4 G5; lia | exact G6 | exact C80 | clear - Ri; lia]. }
intros W2 c2 _ (-> & regsT & memT & mdT & -> & HJT & HPT & T1 & T10 & T11 & T12 & TK).
eapply SRr_mono.
{ exact (rbn3d_call X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 0 (ri_i X) RBN_Q3 regsT memT mdT HX Hcore R25
    ltac:(lia) Hbi ltac:(unfold RBN_Q3; lia) eq_refl HJT HPT T1 T10 T11 T12 TK). }
intros W3 c3 _ (regs2 & lyc2 & Sc2 & memc2 & mdc2 & -> & Hcore2 & R25' & HD & _).
unfold rbn3_at3, rbn3_s3. exists regs2, lyc2, Sc2, memc2, mdc2.
split; [reflexivity|]. split; [exact Hcore2|]. split; [exact R25'|].
rewrite Z.add_0_r in HD. exact HD.
Qed.
Lemma rbn3_D2 : rbn3_D2_stmt B G.
Proof.
intros X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 HX (Hcore & R25 & HDi).
pose proof Hcore as (HM & HRB & _ & _ & _ & _ & _ & _ & HC & HA & _).
pose proof (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (G1 & G2 & _ & G4 & G5 & G6 & _).
pose proof HM as (_ & HJ1 & _).
pose proof HRB as (_ & _ & _ & _ & R9 & _).
cbn [rbn_cells rbn3_cells2] in HC. destruct HC as (_ & _ & _ & _ & C88 & _).
destruct (rbn3d_args X HA) as (Hbi & Hbo). destruct (rbn3d_dec2 _ Hbo) as (_ & _ & Ro).
destruct (rbn3d_dec2 _ Hbi) as (_ & HLi & _).
pose proof asan_consts as (C1 & _).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
eapply SRr_bind.
{ apply (rbn3d_run RBN_Q3 88 RBN_Q4 (rbn_A X) (ri_o X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs1
    (or_intror (conj eq_refl (conj eq_refl eq_refl))) HJ1 R9);
    [rewrite WS in G1; clear - C1 G1 G2 G4 G5; lia | exact G6 | exact C88 | clear - Ro; lia]. }
intros W2 c2 _ (-> & regsT & memT & mdT & -> & HJT & HPT & T1 & T10 & T11 & T12 & TK).
eapply SRr_mono.
{ exact (rbn3d_call X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 2 (ri_o X) RBN_Q4 regsT memT mdT HX Hcore R25
    ltac:(lia) Hbo ltac:(unfold RBN_Q4; lia) eq_refl HJT HPT T1 T10 T11 T12 TK). }
intros W3 c3 _ (regs2 & lyc2 & Sc2 & memc2 & mdc2 & -> & Hcore2 & R25' & HDo & HK).
unfold rbn3_at4, rbn3_s4. exists regs2, lyc2, Sc2, memc2, mdc2.
split; [reflexivity|]. split; [exact Hcore2|]. split; [exact R25'|].
unfold rbm_w4, bn_w4. apply garr8_app. split.
- apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HDi|].
  intros a Ha. rewrite HLi in Ha. apply (mbyte_of_aview SEGS). apply HK. clear - Ha. lia.
- rewrite HLi. change (Z.of_nat 2) with 2. exact HDo.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Let RUNTO := paj_run_to B LAWS.
Lemma rbn3e_upd : forall X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 a1 b1 c1 d1 (Wr : Z -> Prop),
  rbn_cx B G X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh a1 b1 c1 d1) ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem2 md2 0 ->
  (forall a, Wr a -> (rbn_A X + 8 <= a < rbn_A X + 184) \/ (rbn_F X pos + 32 <= a < rbn_F X pos + 40)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) (rbn_sh a1 b1 c1 d1).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 a1 b1 c1 d1 Wr HX HM HJ2 HW HK.
destruct (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HM as (_ & HJ1 & Hperm & _ & _ & _ & _ & Hsh).
pose proof (proj1 HJ1) as HAR1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite G10; left; reflexivity).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite G12; reflexivity).
assert (HN : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 8 <= a < rbn_A X + 184) ->
  ~ (rbn_F X pos + 32 <= a < rbn_F X pos + 40) -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha H1 H2. apply HK; [exact Ha|]. intros Hw. destruct (HW a Hw) as [H3 | H3]; contradiction. }
clear HK HW.
assert (HFapp : rbn_F X pos + 512 <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= rbn_F X pos)
  by (clear - G16; unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia).
apply (rbn3_mid_upd X pos lyc1 Sc1 W1 memc1 mdc1 _ lyc1 Sc1 mem2 md2 _ HX HM HJ2 (Permutation_refl _)).
- intros a Hia _ _. pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
  apply HN; [clear - Hlow; lia | clear - Hlow G1 G4 C1 WS; lia |].
  intros Hf. exact (proj1 (proj2 (G17 a ltac:(clear - Hf; lia))) Hia).
- intros a (q & N & Hin & Hr).
  assert (Hin1 : In (q, N) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR1 Hin1) as (_ & Hq4 & Hqc & _ & _ & _ & HN0).
  pose proof (req_size_pos N ltac:(clear - HN0; lia)) as (Hq1 & Hq2).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N 3 pos HAR1 Hin1 Hin3) as Hd.
  rewrite FA3 in Hd. change (fs_frame_bytes 3) with 512 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  apply HN; clear - Hr Hq4 Hqc Hq1 Hq2 Hd G1 G4 C1 WS; lia.
- intros a Ha. apply HN; clear - Ha G1 G2 G4 G5 G14 C1 WS; lia.
- intros a Ha. apply HN; clear - Ha G1 G4 G13 G14 C1 WS; lia.
- unfold rbn_shadow_at. intros j Hj. pose proof (Hsh j Hj) as Hv.
  rewrite rbn3e_sh_len in Hj. change (Z.of_nat 64) with 64 in Hj.
  rewrite (HN (rbn_SH X pos + j)); [exact Hv | | |];
  rewrite G18; clear - Hj G1 G4 G13 G14 HFapp C1 WS; unfold SHADOW_OFF in *; lia.
Qed.
Lemma rbn3e_post2 : forall X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2,
  rbn_cx B G X -> rbn3_s4 B G X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((rbn_A X + 32 <= a < rbn_A X + 40) \/ a = rbn_F X pos + 36) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  val_mem SEGS (mrestrict (w_H W1) mem2) (rbn_A X + 32) 8 (ri_token_len X) ->
  val_mem SEGS (mrestrict (w_H W1) mem2) (rbn_F X pos + 36) 1 0 ->
  (forall r : bv 5, In r rbn3e_keep2 -> getr regs2 r = getr regs1 r) ->
  getr regs2 12 = w64 4 -> getr regs2 25 = w64 (rbn_F X pos + 32) ->
  rbn3_s5 B G X pos P regs2 lyc1 Sc1 W1 mem2 md2.
Proof.
intros X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2 HX H4 HJ2 HK V32 V36 HKR R12 R25.
destruct H4 as ((HM & HRB & R18 & R26 & R20 & R23 & R24 & R27 & HC & HA & HSRC) & _ & HW4).
destruct (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
assert (HMn : rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) (rbn_sh true false false false)).
{ apply (rbn3e_upd X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 true false false false
    (fun a => (rbn_A X + 32 <= a < rbn_A X + 40) \/ a = rbn_F X pos + 36) HX HM HJ2); [|exact HK].
  intros a [Ha | Ha]; [left | right]; clear - Ha; lia. }
pose proof (rbn3e_w4_len X HA) as HL.
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
unfold rbn3_s5, rbn3_core.
split; [|split; [exact R25 | split; [exact R12|]]].
- split; [exact HMn|].
  split; [unfold rbn_rbase; rewrite !HKR by rbn3e_in; repeat split; assumption|].
  split; [rewrite HKR by rbn3e_in; exact R18|].
  split; [rewrite HKR by rbn3e_in; exact R26|].
  split; [rewrite HKR by rbn3e_in; exact R20|].
  split; [rewrite HKR by rbn3e_in; exact R23|].
  split; [rewrite HKR by rbn3e_in; exact R24|].
  split; [rewrite HKR by rbn3e_in; exact R27|].
  split; [|split; [exact HA | exact HSRC]].
  unfold rbn3_cells5. cbn [rbn_cells]. split; [exact V32|].
  apply (rbn3e_cells_kept (w_H W1) (w_H W1) memc1 mem2); [|exact HC].
  intros a n v k Hin Hk. unfold rbn3_cells2 in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; apply HK;
    clear - Hk G1 G2 G4 G5 G14 C1 WS; lia |]).
  destruct Hin.
- intros j Hj. rewrite length_app, HL in Hj. cbn in Hj.
  destruct (Nat.lt_ge_cases j 4) as [Hj4 | Hj4].
  + rewrite app_nth1 by (rewrite HL; exact Hj4). destruct (HW4 j ltac:(rewrite HL; exact Hj4)) as [V Hb].
    split; [|exact Hb].
    apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [|exact V].
    intros k Hk. apply HK; clear - Hk Hj4 G1 G4 G13 G14 C1 WS; lia.
  + assert (j = 4%nat) as -> by (clear - Hj Hj4; lia). rewrite app_nth2 by (rewrite HL; lia). rewrite HL.
    cbn [Nat.sub nth]. split; [|lia].
    replace (rbn_F X pos + 32 + Z.of_nat 4) with (rbn_F X pos + 36) by lia. exact V36.
Qed.
Lemma rbn3e_post3 : forall X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2,
  rbn_cx B G X -> rbn3_s6 B G X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 mem2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 16 <= a < rbn_A X + 24) ->
     aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  val_mem SEGS (mrestrict (w_H W1) mem2) (rbn_A X + 16) 8 (ri_name X) ->
  (forall r : bv 5, In r rbn3e_keep3 -> getr regs2 r = getr regs1 r) ->
  getr regs2 27 = w64 (rbn_F X pos + 64) -> getr regs2 24 = w64 0 -> getr regs2 30 = w64 0 ->
  getr regs2 15 = w64 (hd 0 (rbm_stem X)) -> getr regs2 13 = w64 (P + 1) -> getr regs2 10 = w64 (P + 1) ->
  getr regs2 14 = w64 23 ->
  rbn_st4 B X pos regs2 lyc1 Sc1 W1 mem2 md2 P.
Proof.
intros X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 regs2 mem2 md2 HX H6 HJ2 HK V16 HKR R27 R24 R30 R15 R13 R10 R14.
destruct H6 as ((HM & HRB & R18 & R26 & R20 & R23 & _ & _ & HC & HA & HSRC) & R25 & R12 & HW4).
destruct (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
assert (HMn : rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) (rbn_sh true true false false)).
{ apply (rbn3e_upd X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 true true false false
    (fun a => rbn_A X + 16 <= a < rbn_A X + 24) HX HM HJ2); [|exact HK].
  intros a Ha. left. clear - Ha; lia. }
pose proof (rbn3e_w4_len X HA) as HL.
cbn [rbn3_cells5 rbn3_cells2 rbn_cells] in HC.
destruct HC as (C32 & C8 & C56 & C64 & C80 & C88 & C152 & C160 & C168 & C176 & _).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
unfold rbn_st4.
split; [exact HMn|].
split; [unfold rbn_rbase; rewrite !HKR by rbn3e_in; repeat split; assumption|].
split; [rewrite HKR by rbn3e_in; exact R18|].
split; [rewrite HKR by rbn3e_in; exact R26|].
split; [rewrite HKR by rbn3e_in; exact R20|].
split; [rewrite HKR by rbn3e_in; exact R23|].
split; [rewrite HKR by rbn3e_in; exact R25|].
split; [exact R27|]. split; [exact R24|]. split; [exact R30|]. split; [exact R15|].
split; [exact R13|]. split; [exact R10|]. split; [exact R14|].
split; [rewrite HKR by rbn3e_in; exact R12|].
split.
{ cbn [rbn_locs4 rbn_cells].
  refine (conj _ (conj V16 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ I)))))))))));
  (apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2);
   [intros k Hk; apply HK; clear - Hk G1 G2 G4 G5 C1 WS; lia | assumption]). }
split.
{ apply (rbn3e_garr8_kept (w_H W1) memc1 mem2); [|exact HW4].
  intros j Hj. rewrite length_app, HL in Hj. cbn in Hj. apply HK; clear - Hj G1 G4 G13 G14 C1 WS; lia. }
split; [|exact HA].
exact (rbn3_stp X pos P lyc1 Sc1 W1 mem2 md2 _ HX HMn HA HSRC).
Qed.
Lemma rbn3_T2 : rbn3_T2_stmt B G.
Proof.
intros X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 HX H4.
pose proof H4 as ((HM & HRB & R18 & R26 & R20 & R23 & R24 & R27 & HC & HA & HSRC) & R25 & HW4).
destruct (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HM as (_ & HJ & _ & _ & _ & _ & _ & Hsh).
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rtl & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
cbn [rbn3_cells2 rbn_cells] in HC. destruct HC as (C8 & C56 & C64 & C80 & C88 & C152 & C160 & C168 & C176 & _).
rewrite G18 in R18.
assert (HA' : 2 ^ 46 <= rbn_A X <= 2 ^ 47) by (clear - G1 G2 G4 G5 C1 WS; lia).
assert (HF' : 4096 <= rbn_F X pos <= 140737479966720) by (clear - G13 G14 C1; lia).
assert (HFA : rbn_F X pos + 37 <= rbn_A X + 8) by (clear - G1 G4 G14 C1 WS; lia).
assert (HFS : rbn_F X pos + 37 <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= rbn_F X pos)
  by (clear - G16; unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia).
destruct (rbn3e_entry2 regs1 W1 memc1 (rbn_A X) (rbn_F X pos) B2 B9 B19 B22 R18 R25 HA' G6 HF' G15 HFA HFS C168
  (fun o Ho => G9 (rbn_A X + o) ltac:(clear - Ho G4 G5 WS; lia))
  (proj1 (G17 (rbn_F X pos + 36) ltac:(clear - G13; lia)))) as [HS SHOK].
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE : env_agree 32 (Ereg regs1 []) E)
  by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; clear - HA'; lia).
assert (U19 : bv_unsigned (ew E 19) = rbn_F X pos)
  by (rewrite (EE 19%nat 19%bv eq_refl), B19; unfold w64; apply unsigned_lit_small; clear - HF'; lia).
assert (U22 : U E (SOff 22 0) = SHADOW_OFF).
{ rewrite U_SOff, (EE 22%nat 22%bv eq_refl), B22. unfold w64.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
  apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
assert (U1936 : U E (SOff 19 36) = rbn_F X pos + 36)
  by (rewrite U_SOff, U19; apply zcanon_id; unfold M64; clear - HF'; lia).
assert (HW1 : forall a, in_wrange E (ss_mem rbn3e_ss2) a ->
  (rbn_A X + 32 <= a < rbn_A X + 40) \/ a = rbn_F X pos + 36).
{ intros a (r & Hr & Hw). unfold rbn3e_ss2, rbn3e_rs2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  - rewrite U9 in Hw. left. clear - Hw. lia.
  - rewrite U19 in Hw. right. clear - Hw. lia. }
assert (HRA : range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF (rbn_F X pos + 36) 1).
{ intros x Hx. exists 5. split.
  - assert (x = rbn_F X pos + 36) as -> by (clear - Hx; lia).
    unfold shadow_of_addr.
    replace (SHADOW_OFF + (rbn_F X pos + 36) / 8) with (rbn_SH X pos + 4) by (rewrite G18; clear - G15; lia).
    rewrite (Hsh 4 ltac:(rewrite rbn3e_sh_len; lia)). reflexivity.
  - right. clear - Hx G15. lia. }
unfold rbn_cfg, cfg_at, w64. rewrite <- Z.add_assoc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_Q5).
- rewrite U1936. eapply obl_of_range; [exact HRA | exact U22 | apply Z.le_refl | apply Z.le_refl].
- lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off E _ _ REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) _ _ lyc1 _ 9%nat (rbn_A X - rbn_SP X));
    [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo]; clear - G4 WS; lia | cbn [YP09.r_whi]; clear - G5; lia |].
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 19%nat (rbn_F X pos)); [reflexivity | exact U19 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 3, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite G12.
    change (fs_frame_bytes 3) with 512. unfold rbn_F in Ha. clear - Ha. lia. }
  apply awr_ok_nil.
- lazymatch goal with HS0 : st_ok_pi _ _ _ _ (restrict _ ?m2) |- _ => rename m2 into ms2 end.
  pose proof (rbn3e_kept E _ (w_H W1) memc1 (ms_mem ms2) _ HFr HW1) as K.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RA.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RF.
  cbn [ms_mem restrict] in RA, RF.
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    assert (U9' : bv_unsigned (ew E2 9) = rbn_A X) by (cbn [ew ewset Nat.eqb]; exact U9);
    assert (U19' : bv_unsigned (ew E2 19) = rbn_F X pos) by (cbn [ew ewset Nat.eqb]; exact U19);
    assert (HAE2 : env_agree 32 (Ereg regs1 []) E2)
      by (split; [intros n Hn; rewrite !ew_ewset_other by (clear - Hn; lia); exact (proj1 HAE n Hn)
                 | exact (proj2 HAE)]);
    assert (V27 : sv_denot E2 (SOff 27 0) = Z_to_bv 64 (ri_token_len X))
      by (cbn [sv_denot ew ewset Nat.eqb]; rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64;
          rewrite unsigned_lit_small by (clear - Rtl; lia); rewrite Z.add_0_r; reflexivity)
  end.
  assert (V32 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms2)) (rbn_A X + 32) 8 (ri_token_len X)).
  { exact (field_of_region _ _ 9%nat (rbn_A X) _ _ _ _ _ 32 8%N (SOff 27 0) (ri_token_len X) RA U9'
      ltac:(cbn [In]; left; reflexivity) V27 ltac:(cbn; clear - Rtl; lia) ltac:(cbn; lia)). }
  assert (V36 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms2)) (rbn_F X pos + 36) 1 0).
  { exact (field_of_region _ _ 19%nat (rbn_F X pos) _ _ _ _ _ 36 1%N (SLit 0) 0 RF U19'
      ltac:(cbn [In]; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 [] rbn3e_keep2 HS HAE2 ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  prreg HS (12%bv : bv 5) R12'. prreg HS (25%bv : bv 5) R25'. rewrite U19 in R25'.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?pcv) _ _) ?md) _ =>
    apply SRr_ret; unfold rbn3_at5; cbv beta;
    exists (ms_regs ms2), lyc1, Sc1, (ms_mem ms2), md; split;
    [unfold rbn_cfg, cfg_at, w64;
     replace (BASE + AF_reac_box_name + RBN_Q5) with pcv by (unfold AF_reac_box_name, RBN_Q5; ring); reflexivity
    | exact (rbn3e_post2 X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 (ms_regs ms2) (ms_mem ms2) md HX H4 HJ K V32 V36
        HKR R12' R25') ]
  end.
Qed.
Lemma rbn3_T3 : rbn3_T3_stmt B G.
Proof.
intros X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 HX H6.
pose proof H6 as ((HM & HRB & R18 & R26 & R20 & R23 & R24 & R27 & HC & HA & HSRC) & R25 & R12 & HW4).
destruct (rbn3_geo X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HM as (_ & HJ & _).
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rnm & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8496) by reflexivity.
pose proof (rbn3_stp X pos P lyc1 Sc1 W1 memc1 mdc1 _ HX HM HA HSRC) as (HCS & HSD).
destruct HCS as (Hch & _ & HP0 & HPam & HPg & HPra & _).
destruct (rbn3e_hd W1 memc1 P (rbm_stem X) (rbn3e_stem_ne X) Hch HPg) as (Hc1 & Hl1 & Vc).
rewrite G18 in R18.
assert (HA' : 2 ^ 46 <= rbn_A X <= 2 ^ 47) by (clear - G1 G2 G4 G5 C1 WS; lia).
assert (HF' : 4096 <= rbn_F X pos <= 140737479966720) by (clear - G13 G14 C1; lia).
assert (HP' : 1 <= P <= 2 ^ 47 - 10)
  by (clear - HP0 HPam Hl1 C4; unfold amem_range, kLowMemEnd, kHighMemBeg in HPam; lia).
assert (HPd : P + 1 <= rbn_A X + 16 \/ rbn_A X + 24 <= P).
{ destruct (HSD P ltac:(clear - Hl1; lia)) as [Hs _]. clear - Hs G1 G4 G5 WS. lia. }
pose proof (rbn3e_entry3 regs1 W1 memc1 (rbn_A X) (rbn_F X pos) P (hd 0 (rbm_stem X)) B2 B9 B19 B22 R18 R20
  HA' G6 HF' G15 HP' Hc1 HPd Vc (fun o Ho => G9 (rbn_A X + o) ltac:(clear - Ho G4 G5 WS; lia))) as HS.
assert (SHOK : sh_ok SEGS rbn3e_Bx [] (Eimg (Ereg regs1 [Z_to_bv 64 (hd 0 (rbm_stem X))]))
  (mrestrict (w_H W1) memc1)) by (unfold sh_ok; apply Forall_nil).
remember (Eimg (Ereg regs1 [Z_to_bv 64 (hd 0 (rbm_stem X))])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE : env_agree 32 (Ereg regs1 [Z_to_bv 64 (hd 0 (rbm_stem X))]) E)
  by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 (hd 0 (rbm_stem X)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = rbn_A X)
  by (rewrite (EE 9%nat 9%bv eq_refl), B9; unfold w64; apply unsigned_lit_small; clear - HA'; lia).
assert (U19 : bv_unsigned (ew E 19) = rbn_F X pos)
  by (rewrite (EE 19%nat 19%bv eq_refl), B19; unfold w64; apply unsigned_lit_small; clear - HF'; lia).
assert (U20 : bv_unsigned (ew E 20) = P)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; clear - HP'; lia).
assert (U22 : U E (SOff 22 0) = SHADOW_OFF).
{ rewrite U_SOff, (EE 22%nat 22%bv eq_refl), B22. unfold w64.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
  apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
assert (U200 : U E (SOff 20 0) = P)
  by (rewrite U_SOff, U20, Z.add_0_r; apply zcanon_id; unfold M64; clear - HP'; lia).
assert (HW3 : forall a, in_wrange E (ss_mem rbn3e_ss3) a -> rbn_A X + 16 <= a < rbn_A X + 24).
{ intros a (r & Hr & Hw). unfold rbn3e_ss3, rbn3e_rs3 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  - rewrite U9 in Hw. clear - Hw. lia.
  - clear - Hw. lia. }
assert (HRA : range_addressable (aview SEGS (w_H W1) memc1) SHADOW_OFF P 1)
  by (apply (range_addressable_sub _ _ P (Z.of_nat (length (rbm_stem X)) + 1)); [exact HPra | lia | clear - Hl1; lia]).
unfold rbn_cfg, cfg_at, w64. rewrite <- Z.add_assoc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + RBN_P4).
- rewrite U200. eapply obl_of_range; [exact HRA | exact U22 | apply Z.le_refl | apply Z.le_refl].
- lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off E _ _ REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) _ _ lyc1 _ 9%nat (rbn_A X - rbn_SP X));
    [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo]; clear - G4 WS; lia | cbn [YP09.r_whi]; clear - G5; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; apply Z.le_refl|].
  apply awr_ok_nil.
- lazymatch goal with HS0 : st_ok_pi _ _ _ _ (restrict _ ?m2) |- _ => rename m2 into ms2 end.
  pose proof (rbn3e_kept E _ (w_H W1) memc1 (ms_mem ms2) _ HFr HW3) as K.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RA.
  cbn [ms_mem restrict] in RA.
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    assert (U9' : bv_unsigned (ew E2 9) = rbn_A X) by (cbn [ew ewset Nat.eqb]; exact U9);
    assert (HAE2 : env_agree 32 (Ereg regs1 [Z_to_bv 64 (hd 0 (rbm_stem X))]) E2)
      by (split; [intros n Hn; rewrite !ew_ewset_other by (clear - Hn; lia); exact (proj1 HAE n Hn)
                 | exact (proj2 HAE)]);
    assert (V24 : sv_denot E2 (SOff 24 0) = Z_to_bv 64 (ri_name X))
      by (cbn [sv_denot ew ewset Nat.eqb]; rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64;
          rewrite unsigned_lit_small by (clear - Rnm; lia); rewrite Z.add_0_r; reflexivity)
  end.
  assert (V16 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms2)) (rbn_A X + 16) 8 (ri_name X)).
  { exact (field_of_region _ _ 9%nat (rbn_A X) _ _ _ _ _ 16 8%N (SOff 24 0) (ri_name X) RA U9'
      ltac:(cbn [In]; left; reflexivity) V24 ltac:(cbn; clear - Rnm; lia) ltac:(cbn; lia)). }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 [Z_to_bv 64 (hd 0 (rbm_stem X))] rbn3e_keep3 HS HAE2
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  prreg HS (27%bv : bv 5) R27'. prreg HS (24%bv : bv 5) R24'. prreg HS (30%bv : bv 5) R30'.
  prreg HS (15%bv : bv 5) R15'. prreg HS (13%bv : bv 5) R13'. prreg HS (10%bv : bv 5) R10'.
  prreg HS (14%bv : bv 5) R14'.
  rewrite U19 in R27'. rewrite E32 in R15'. rewrite U20 in R13', R10'.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?pcv) _ _) ?md) _ =>
    apply SRr_ret; unfold rbn_at4; cbv beta;
    exists pos, (ms_regs ms2), lyc1, Sc1, (ms_mem ms2), md, P; split;
    [unfold rbn_cfg, cfg_at, w64;
     replace (BASE + AF_reac_box_name + RBN_P4) with pcv by (unfold AF_reac_box_name, RBN_P4; ring); reflexivity
    | exact (rbn3e_post3 X pos P regs1 lyc1 Sc1 W1 memc1 mdc1 (ms_regs ms2) (ms_mem ms2) md HX H6 HJ K V16
        HKR R27' R24' R30' R15' R13' R10' R14') ]
  end.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma rbn_seg3 : rbn_seg3_stmt B G.
Proof.
exact (rbn3_compose B G rbn3_T1 rbn3_MS rbn3_D1 rbn3_D2 rbn3_T2 rbn3_P4 rbn3_T3).
Qed.
End h.
End f.
End d.
