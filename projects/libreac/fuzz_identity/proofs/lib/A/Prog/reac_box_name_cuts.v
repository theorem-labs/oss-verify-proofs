(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148, for
   libreac/fuzz_identity's ASan build (lib/A). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition RBN_P2 : Z := 0xcc.
Definition RBN_P3 : Z := 0x1f4.
Definition RBN_P4 : Z := 0x304.
Definition RBN_P5 : Z := 0x370.
Definition RBN_P6 : Z := 0x4b8.
Definition RBN_P7 : Z := 0x56c.
Definition RBN_P8 : Z := 0x650.
Definition RBN_P9 : Z := 0x7a4.
Definition RBN_P10 : Z := 0x8f8.
Definition RBN_L1 : Z := 0x304.
Definition RBN_L1X : Z := 0x370.
Definition RBN_L2 : Z := 0x3f4.
Definition RBN_L2X : Z := 0x460.
Definition RBN_L3 : Z := 0x4d8.
Definition RBN_L3X : Z := 0x568.
Definition RBN_L4 : Z := 0x5dc.
Definition RBN_L4X : Z := 0x648.
Definition RBN_L5 : Z := 0x670.
Definition RBN_L5X : Z := 0x6dc.
Definition RBN_L6 : Z := 0x718.
Definition RBN_L6X : Z := 0x788.
Definition RBN_L7 : Z := 0x7c0.
Definition RBN_L7X : Z := 0x830.
Definition rbn_lit5 : list Z := [32; 40].
Definition rbn_lit6 : list Z := [32; 105; 110; 32; 47; 32].
Definition rbn_lit7 : list Z := [32; 111; 117; 116; 41].
Definition rbn_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition rbn_sh (w4 nb tb db : bool) : list Z :=
  [241; 241; 241; 241] ++ [if w4 then 5 else 248] ++ [242; 242; 242] ++ repeat (if nb then 0 else 248) 3 ++
  [242; 242; 242; 242; 242] ++ repeat (if tb then 0 else 248) 3 ++ [242; 242; 242; 242; 242] ++
  repeat (if db then 0 else 248) 6 ++ repeat 243 6 ++ repeat 0 28.
Definition rbm_ovf (cap : Z) (l : list Z) : Z := if cap <? Z.of_nat (length l) then 1 else 0.
Definition rbn_keep_regs (regs regs2 : bvmap 5 word) (cl : list Z) : Prop :=
  forall r, 0 <= r < 32 -> ~ In r cl -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Record rbn_in : Type := RbnIn {
  ri_lyc : alayout; ri_Sc : astate; ri_W : world SEGS; ri_regs : bvmap 5 word;
  ri_memc : word -> option byte; ri_mdc : Model; ri_ch : list (Z * Z * Z);
  ri_f : Z; ri_said : Z; ri_i : Z; ri_o : Z; ri_name : Z; ri_name_len : Z; ri_token : Z; ri_token_len : Z;
  ri_display : Z; ri_display_len : Z; ri_sd : list Z }.
Definition rbn_SP (X : rbn_in) : Z := spZ (ri_regs X).
Definition rbn_A (X : rbn_in) : Z := 32 * ((rbn_SP X - 288) / 32).
Definition rbn_F (X : rbn_in) (pos : Z) : Z := frame_addr (ri_lyc X) 3 pos.
Definition rbn_FL (X : rbn_in) (pos : Z) : Z := flag_addr (ri_lyc X) 3 pos.
Definition rbn_SH (X : rbn_in) (pos : Z) : Z := shadow_addr (rbn_F X pos).
Definition rbn_FPX (X : rbn_in) : list (Z * Z) :=
  rbn_fp (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X) (ri_display_len X).
Lemma rbn_fp_in : forall name name_len token token_len display display_len a,
  inFP (rbn_fp name name_len token token_len display display_len) a ->
  (name <> 0 /\ name <= a < name + Z.min name_len 24) \/ (token <> 0 /\ token <= a < token + Z.min token_len 24) \/
  (display <> 0 /\ display <= a < display + Z.min display_len 48).
Proof.
intros n nl t tl d dl a (r & Hr & Ha). revert Ha. unfold rbn_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd];
[destruct (n =? 0) eqn:E | destruct (t =? 0) eqn:E | destruct (d =? 0) eqn:E];
rewrite ?Z.eqb_eq, ?Z.eqb_neq in E; lia.
Qed.
Lemma rbn_fp_closed : forall name name_len token token_len display display_len,
  0 <= name -> 0 <= token -> 0 <= display ->
  ~ YI16.sink_open_fp (rbn_fp name name_len token token_len display display_len).
Proof.
intros n nl t tl d dl Hn Ht Hd H0. unfold YI16.sink_open_fp in H0. apply (proj1 (in_fp_inFP _ _)) in H0.
apply rbn_fp_in in H0. lia.
Qed.
Definition rbm_stem (X : rbn_in) : list Z := bn_stem (ri_f X) (ri_sd X).
Definition rbm_w4 (X : rbn_in) : list Z := bn_w4 (ri_i X) (ri_o X).
Definition rbm_NM (X : rbn_in) : list Z := bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X).
Definition rbm_NB (X : rbn_in) : list Z := firstn 23 (rbm_NM X).
Definition rbm_TB (X : rbn_in) : list Z := firstn 23 (bn_TK (rbm_NB X)).
Definition rbm_tok (X : rbn_in) : Z := 1 - rbm_ovf 23 (bn_TK (rbm_NB X)).
Definition rbm_D9 (X : rbn_in) : list Z :=
  rbm_NB X ++ [32; 40] ++ bn_dec (ri_i X) 1 ++ [32; 105; 110; 32; 47; 32] ++ bn_dec (ri_o X) 1.
Definition rbm_acc (X : rbn_in) : bool :=
  reac_box_name_c.bn_accept (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X)
    (ri_token_len X) (ri_display X) (ri_display_len X).
Definition rbm_args (X : rbn_in) : Prop :=
  reac_box_name_c.bn_args_ok (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X)
    (ri_display_len X) (ri_i X) (ri_o X) = true.
Fixpoint rbn_cells (m : word -> option byte) (l : list (Z * nat * Z)) : Prop :=
  match l with [] => True | (a, n, v) :: t => val_mem SEGS m a n v /\ rbn_cells m t end.
Definition rbn_locs4 (X : rbn_in) (pos : Z) : list (Z * nat * Z) :=
  [(rbn_A X + 8, 8%nat, ri_display X); (rbn_A X + 16, 8%nat, ri_name X); (rbn_A X + 32, 8%nat, ri_token_len X);
   (rbn_A X + 56, 8%nat, ri_display_len X); (rbn_A X + 64, 8%nat, ri_name_len X);
   (rbn_A X + 80, 8%nat, ri_i X); (rbn_A X + 88, 8%nat, ri_o X);
   (rbn_A X + 152, 8%nat, rbn_F X pos + 32); (rbn_A X + 160, 8%nat, 5); (rbn_A X + 168, 8%nat, 4);
   (rbn_A X + 176, 4%nat, 0)].
Definition rbn_locs6 (X : rbn_in) (pos : Z) : list (Z * nat * Z) :=
  rbn_locs4 X pos ++
  [(rbn_A X + 24, 8%nat, ri_token X); (rbn_A X + 48, 8%nat, rbn_F X pos + 128); (rbn_A X + 72, 8%nat, rbn_F X pos)].
Definition rbn_rec2 (X : rbn_in) (pos : Z) (s : list Z) : list (Z * nat * Z) :=
  [(rbn_A X + 120, 8%nat, rbn_F X pos + 192); (rbn_A X + 128, 8%nat, 48);
   (rbn_A X + 136, 8%nat, Z.min (Z.of_nat (length s)) 47); (rbn_A X + 144, 4%nat, rbm_ovf 47 s)].
Definition rbn_shadow_at (W1 : world SEGS) (m : word -> option byte) (q : Z) (l : list Z) : Prop :=
  forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W1) m (q + j) = Some (nth (Z.to_nat j) l 0).
Definition rbn_lsrc (W : world SEGS) (memc : word -> option byte) (P : Z) (l : list Z) : Prop :=
  garr8 SEGS (mrestrict (w_H W) memc) P l /\ 0 <= P /\ P + Z.of_nat (length l) <= 2 ^ 63 /\
  P + Z.of_nat (length l) <= 2 ^ 47 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF P (Z.of_nat (length l)).
Definition rbn_cfg (off : Z) (regs1 : bvmap 5 word) (memc1 : word -> option byte) (mdc1 : Model) : config :=
  cfg_at SEGS (BASE + AF_reac_box_name + off) regs1 memc1 mdc1.
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Definition rbn_cx (X : rbn_in) : Prop :=
  afn_pre SEGS B REAC_BOX_NAME_STK (ri_lyc X) (ri_Sc X) (ri_W X) (ri_regs X) (ri_memc X) (ri_mdc X) (ri_ch X) /\
  arodata_okP SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI) B
    (aview SEGS (w_H (ri_W X)) (ri_memc X)) /\
  getr (ri_regs X) 10 = w64 (ri_f X) /\ - 2 ^ 31 <= ri_f X < 2 ^ 31 /\
  getr (ri_regs X) 11 = w64 (ri_said X) /\ 0 <= ri_said X < 2 ^ 64 /\
  getr (ri_regs X) 12 = w64 (ri_i X) /\ - 2 ^ 31 <= ri_i X < 2 ^ 31 /\
  getr (ri_regs X) 13 = w64 (ri_o X) /\ - 2 ^ 31 <= ri_o X < 2 ^ 31 /\
  getr (ri_regs X) 14 = w64 (ri_name X) /\ 0 <= ri_name X < 2 ^ 64 /\
  getr (ri_regs X) 15 = w64 (ri_name_len X) /\ 0 <= ri_name_len X < 2 ^ 64 /\
  getr (ri_regs X) 16 = w64 (ri_token X) /\ 0 <= ri_token X < 2 ^ 64 /\
  getr (ri_regs X) 17 = w64 (ri_token_len X) /\ 0 <= ri_token_len X < 2 ^ 64 /\
  (forall a, rbn_SP X <= a < rbn_SP X + 16 -> apresent (w_H (ri_W X)) (ri_memc X) a) /\
  val_mem SEGS (mrestrict (w_H (ri_W X)) (ri_memc X)) (rbn_SP X) 8 (ri_display X) /\
  0 <= ri_display X < 2 ^ 64 /\
  val_mem SEGS (mrestrict (w_H (ri_W X)) (ri_memc X)) (rbn_SP X + 8) 8 (ri_display_len X) /\
  0 <= ri_display_len X < 2 ^ 64 /\
  rbn_img B G (ri_W X) (ri_memc X) /\
  (rbm_args X ->
     rbn_said (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_said X) (ri_sd X) /\
     rbn_bufs B (ri_lyc X) (ri_Sc X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X)
       (ri_display_len X)) /\
  Z.of_nat (length (frames (ri_Sc X))) <= 7 /\
  st_nev (ri_Sc X) + EV_REAC_BOX_NAME <= EV_MAX /\ blocks_bytes (ri_Sc X) + LIVE_REAC_BOX_NAME <= LIVE_MAX.
Definition rbn_post (X : rbn_in) : world SEGS -> config -> Prop :=
  treac_box_name_post B (ri_regs X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X) (ri_f X) (ri_sd X)
    (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X) (ri_display X) (ri_display_len X).
Definition rbn_wr (X : rbn_in) (a : Z) : Prop :=
  rbm_acc X = true /\
  (ri_name X <= a < ri_name X + Z.of_nat (length (rbm_NM X)) + 1 \/
   ri_token X <= a < ri_token X + Z.of_nat (length (bn_TK (rbm_NM X))) + 1 \/
   ri_display X <= a < ri_display X + Z.of_nat (length (bn_DP (rbm_NM X) (ri_i X) (ri_o X))) + 1).
Definition rbn_inblk (X : rbn_in) (a : Z) : Prop :=
  exists q N, In (q, N) (ablocks B (ri_lyc X) (ri_Sc X)) /\ q <= a < q + N.
Definition rbn_kept (X : rbn_in) (W1 : world SEGS) (memc1 : word -> option byte) (Er : Z -> Prop) : Prop :=
  forall a, inFP (rbn_FPX X) a -> rbn_inblk X a -> ~ Er a ->
    aview SEGS (w_H W1) memc1 a = aview SEGS (w_H (ri_W X)) (ri_memc X) a.
Definition rbn_frame (X : rbn_in) (m : word -> option byte) : Prop :=
  forall j r, nth_error rbn_saved_regs j = Some r ->
    val_mem SEGS m (rbn_SP X - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr (ri_regs X) (Z_to_bv 5 r))).
Definition rbn_mid (X : rbn_in) (pos : Z) (lyc1 : alayout) (Sc1 : astate) (W1 : world SEGS)
  (memc1 : word -> option byte) (mdc1 : Model) (Er : Z -> Prop) (sh : list Z) : Prop :=
  W1 = ri_W X /\
  ajournal SEGS B REAC_BOX_NAME_STK (rbn_SP X) (rbn_FPX X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X)
    [(3, pos)] lyc1 Sc1 W1 memc1 mdc1 0 /\
  Permutation (ablocks B lyc1 Sc1) (ablocks B (ri_lyc X) (ri_Sc X)) /\
  arodata_okP SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI) B
    (aview SEGS (w_H W1) memc1) /\
  rbn_kept X W1 memc1 Er /\
  rbn_frame X (mrestrict (w_H W1) memc1) /\
  val_mem SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 504) 8 (rbn_FL X pos) /\
  rbn_shadow_at W1 memc1 (rbn_SH X pos) sh.
Definition rbn_rbase (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
  getr regs1 2 = w64 (rbn_A X) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
  getr regs1 8 = w64 (rbn_SP X) /\ getr regs1 9 = w64 (rbn_A X) /\ getr regs1 19 = w64 (rbn_F X pos) /\
  getr regs1 22 = w64 SHADOW_OFF.
Definition rbn_stp (X : rbn_in) (pos : Z) (W1 : world SEGS) (memc1 : word -> option byte) (P : Z) : Prop :=
  rbn_cstr W1 memc1 P (rbm_stem X) /\
  (forall a, P <= a < P + Z.of_nat (length (rbm_stem X)) + 1 ->
     ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512)).
Definition rbn_st2 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (repeat 0 64) /\
  rbn_rbase X pos regs1 /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 20 = w64 (ri_said X) /\ getr regs1 23 = w64 (ri_token X) /\ getr regs1 24 = w64 (ri_name X) /\
  getr regs1 25 = w64 (ri_f X) /\ getr regs1 27 = w64 (ri_token_len X) /\
  getr regs1 12 = w64 (ri_i X) /\ getr regs1 13 = w64 (ri_o X) /\
  getr regs1 15 = w64 (ri_name_len X) /\ getr regs1 16 = w64 (ri_display_len X).
Definition rbn_st3 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh false false false false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 20 = w64 (ri_said X) /\ getr regs1 23 = w64 (ri_token X) /\ getr regs1 24 = w64 (ri_name X) /\
  getr regs1 25 = w64 (ri_f X) /\ getr regs1 27 = w64 (ri_token_len X) /\
  getr regs1 12 = w64 (ri_i X) /\ getr regs1 13 = w64 (ri_o X) /\ getr regs1 14 = w64 (ri_display X) /\
  getr regs1 15 = w64 (ri_name_len X) /\ getr regs1 16 = w64 (ri_display_len X) /\
  rbm_args X.
Definition rbn_st4 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) (P : Z) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true false false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 20 = w64 P /\ getr regs1 23 = w64 (ri_token X) /\ getr regs1 25 = w64 (rbn_F X pos + 32) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\ getr regs1 24 = w64 0 /\ getr regs1 30 = w64 0 /\
  getr regs1 15 = w64 (hd 0 (rbm_stem X)) /\ getr regs1 13 = w64 (P + 1) /\ getr regs1 10 = w64 (P + 1) /\
  getr regs1 14 = w64 23 /\ getr regs1 12 = w64 4 /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_locs4 X pos) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X ++ [0]) /\
  rbn_stp X pos W1 memc1 P /\ rbm_args X.
Definition rbn_st5 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) (P : Z) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true false false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 20 = w64 P /\ getr regs1 23 = w64 (ri_token X) /\ getr regs1 25 = w64 (rbn_F X pos + 32) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\
  getr regs1 24 = w64 (Z.of_nat (length (firstn 23 (rbm_stem X)))) /\
  getr regs1 30 = w64 (rbm_ovf 23 (rbm_stem X)) /\ getr regs1 12 = w64 4 /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_locs4 X pos) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) /\
  rbn_stp X pos W1 memc1 P /\ rbm_args X.
Definition rbn_st6 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\ getr regs1 24 = w64 (Z.of_nat (length (rbm_NB X))) /\
  getr regs1 30 = w64 (rbm_ovf 23 (rbm_NM X)) /\ getr regs1 29 = w64 (rbn_F X pos + 128) /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_locs6 X pos) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 64) (rbm_NB X ++ [0]) /\
  rbm_args X.
Definition rbn_st7 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\ getr regs1 24 = w64 (Z.of_nat (length (rbm_NB X))) /\
  getr regs1 30 = w64 (rbm_ovf 23 (rbm_NM X)) /\ getr regs1 29 = w64 (rbn_F X pos + 128) /\
  getr regs1 26 = w64 (Z.of_nat (length (rbm_TB X))) /\ getr regs1 21 = w64 (rbm_tok X) /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_locs6 X pos) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 64) (rbm_NB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 128) (rbm_TB X) /\
  rbm_args X.
Definition rbn_st8 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true true) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\ getr regs1 24 = w64 (Z.of_nat (length (rbm_NB X))) /\
  getr regs1 25 = w64 (rbm_ovf 23 (rbm_NM X)) /\ getr regs1 20 = w64 (rbn_F X pos + 192) /\
  getr regs1 26 = w64 (Z.of_nat (length (rbm_TB X))) /\ getr regs1 21 = w64 (rbm_tok X) /\
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_locs6 X pos ++ rbn_rec2 X pos (rbm_NB X)) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 64) (rbm_NB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 128) (rbm_TB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 192) (firstn 47 (rbm_NB X)) /\
  rbm_args X.
Definition rbn_st9 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true true true) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\
  getr regs1 27 = w64 (rbn_F X pos + 64) /\ getr regs1 24 = w64 (Z.of_nat (length (rbm_NB X))) /\
  getr regs1 25 = w64 (rbm_ovf 23 (rbm_NM X)) /\ getr regs1 20 = w64 (rbn_F X pos + 192) /\
  getr regs1 26 = w64 (Z.of_nat (length (rbm_TB X))) /\ getr regs1 21 = w64 1 /\
  rbn_cells (mrestrict (w_H W1) memc1)
    (rbn_locs6 X pos ++ rbn_rec2 X pos (rbm_D9 X) ++ [(rbn_A X + 40, 8%nat, rbm_tok X)]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 64) (rbm_NB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 128) (rbm_TB X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 192) (firstn 47 (rbm_D9 X)) /\
  rbm_args X.
Definition rbn_st10 (X : rbn_in) (pos : Z) (regs1 : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (memc1 : word -> option byte) (mdc1 : Model) : Prop :=
  rbn_mid X pos lyc1 Sc1 W1 memc1 mdc1 (rbn_wr X) (rbn_sh false false false false) /\
  rbn_rbase X pos regs1 /\ getr regs1 18 = w64 (rbn_SH X pos) /\ getr regs1 26 = w64 (rbn_F X pos) /\
  getr regs1 21 = w64 (if rbm_acc X then 0 else -1) /\
  (rbm_acc X = true ->
     garr8 SEGS (mrestrict (w_H W1) memc1) (ri_name X) (rbm_NM X ++ [0]) /\
     garr8 SEGS (mrestrict (w_H W1) memc1) (ri_token X) (bn_TK (rbm_NM X) ++ [0]) /\
     garr8 SEGS (mrestrict (w_H W1) memc1) (ri_display X) (bn_DP (rbm_NM X) (ri_i X) (ri_o X) ++ [0])).
Definition rbn_at2 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg RBN_P2 regs1 memc1 mdc1 /\ rbn_st2 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at3 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg RBN_P3 regs1 memc1 mdc1 /\ rbn_st3 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at4 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1 P,
    c1 = rbn_cfg RBN_P4 regs1 memc1 mdc1 /\ rbn_st4 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P.
Definition rbn_at5 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1 P,
    c1 = rbn_cfg RBN_P5 regs1 memc1 mdc1 /\ rbn_st5 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P.
Definition rbn_at6 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg RBN_P6 regs1 memc1 mdc1 /\ rbn_st6 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at7 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg RBN_P7 regs1 memc1 mdc1 /\ rbn_st7 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at8 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg RBN_P8 regs1 memc1 mdc1 /\ rbn_st8 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at9 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg RBN_P9 regs1 memc1 mdc1 /\ rbn_st9 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_at10 (X : rbn_in) : world SEGS -> config -> Prop :=
  fun W1 c1 => exists pos regs1 lyc1 Sc1 memc1 mdc1,
    c1 = rbn_cfg RBN_P10 regs1 memc1 mdc1 /\ rbn_st10 X pos regs1 lyc1 Sc1 W1 memc1 mdc1.
Definition rbn_seg1_stmt : Prop :=
  forall X : rbn_in, rbn_cx X ->
  SRr SEGS (ri_W X) (cfg_at SEGS (BASE + AF_reac_box_name) (ri_regs X) (ri_memc X) (ri_mdc X)) (rbn_at2 X).
Definition rbn_seg2_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st2 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_P2 regs1 memc1 mdc1) (fun W2 c2 => rbn_at3 X W2 c2 \/ rbn_at10 X W2 c2).
Definition rbn_seg3_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st3 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_P3 regs1 memc1 mdc1) (rbn_at4 X).
Definition rbn_seg4_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P, rbn_cx X -> rbn_st4 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  SRr SEGS W1 (rbn_cfg RBN_P4 regs1 memc1 mdc1) (rbn_at5 X).
Definition rbn_seg5_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P, rbn_cx X -> rbn_st5 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  SRr SEGS W1 (rbn_cfg RBN_P5 regs1 memc1 mdc1) (rbn_at6 X).
Definition rbn_seg6_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st6 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_P6 regs1 memc1 mdc1) (rbn_at7 X).
Definition rbn_seg7_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st7 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_P7 regs1 memc1 mdc1) (rbn_at8 X).
Definition rbn_seg8_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st8 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_P8 regs1 memc1 mdc1) (rbn_at9 X).
Definition rbn_seg9_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st9 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_P9 regs1 memc1 mdc1) (rbn_at10 X).
Definition rbn_seg10_stmt : Prop :=
  forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1, rbn_cx X -> rbn_st10 X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  SRr SEGS W1 (rbn_cfg RBN_P10 regs1 memc1 mdc1) (rbn_post X).
Definition rbn_lbuf (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (D n : Z) : Prop :=
  0 <= D /\ D + n <= 2 ^ 63 /\ in_app D n /\ range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF D n /\
  (forall a, D <= a < D + n ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a).
Definition rbn_lpost (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (ex : Z) (cl : list Z)
  (D n0 : Z) (wr : list Z) (outs : list (Z * Z)) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = rbn_cfg ex regs2 mem2 md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
    rbn_keep_regs regs regs2 cl /\
    Forall (fun p => getr regs2 (Z_to_bv 5 (fst p)) = w64 (snd p)) outs /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + Z.of_nat (length wr)) ->
       aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
    garr8 SEGS (mrestrict (w_H W) mem2) (D + n0) wr.
Definition rbn_L1_run (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (P D n0 ov0 : Z) (s : list Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  s <> [] -> Forall (fun c => 0 < c < 256) s -> rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 24 ->
  (P + Z.of_nat (length s) + 1 <= D \/ D + 24 <= P) ->
  0 <= n0 <= 23 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 24 = w64 n0 -> getr regs 30 = w64 ov0 -> getr regs 15 = w64 (hd 0 s) ->
  getr regs 13 = w64 (P + 1) -> getr regs 10 = w64 (P + 1) -> getr regs 14 = w64 23 ->
  getr regs 27 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (rbn_cfg RBN_L1 regs memc mdc)
    (rbn_lpost STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L1X [5; 10; 11; 13; 15; 16; 17; 24; 30]
       D n0 wr [(24, nF); (30, ovF)]).
Definition rbn_L1_fits : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  n0 + Z.of_nat (length s) <= 23 ->
  rbn_L1_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    (n0 + Z.of_nat (length s)) ov0 s.
Definition rbn_L1_ovf : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  23 < n0 + Z.of_nat (length s) ->
  rbn_L1_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    23 1 (firstn (Z.to_nat (23 - n0)) s).
Definition rbn_L2_run (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (P D n0 ov0 : Z) (s : list Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  s <> [] -> Forall (fun c => 0 < c < 256) s -> rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 24 ->
  (P + Z.of_nat (length s) + 1 <= D \/ D + 24 <= P) ->
  0 <= n0 <= 23 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 24 = w64 n0 -> getr regs 30 = w64 ov0 -> getr regs 13 = w64 (hd 0 s) ->
  getr regs 21 = w64 (P + 1) -> getr regs 10 = w64 (P + 1) -> getr regs 12 = w64 23 ->
  getr regs 27 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (rbn_cfg RBN_L2 regs memc mdc)
    (rbn_lpost STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L2X [10; 11; 13; 14; 15; 16; 21; 24; 30]
       D n0 wr [(24, nF); (30, ovF)]).
Definition rbn_L2_fits : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  n0 + Z.of_nat (length s) <= 23 ->
  rbn_L2_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    (n0 + Z.of_nat (length s)) ov0 s.
Definition rbn_L2_ovf : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  23 < n0 + Z.of_nat (length s) ->
  rbn_L2_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    23 1 (firstn (Z.to_nat (23 - n0)) s).
Definition rbn_L3_run (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (N D : Z) (l : list Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  (1 <= length l)%nat -> Forall (fun c => 0 <= c < 256) l -> rbn_lsrc W memc N l ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 24 ->
  (N + Z.of_nat (length l) <= D \/ D + 24 <= N) ->
  getr regs 12 = w64 0 -> getr regs 26 = w64 0 -> getr regs 13 = w64 0 -> getr regs 14 = w64 45 ->
  getr regs 15 = w64 23 -> getr regs 16 = w64 N -> getr regs 10 = w64 N ->
  getr regs 17 = w64 (Z.of_nat (length l)) -> getr regs 29 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (rbn_cfg RBN_L3 regs memc mdc)
    (rbn_lpost STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L3X [5; 6; 7; 10; 11; 12; 13; 16; 17; 26; 28]
       D 0 wr [(26, nF); (13, ovF)]).
Definition rbn_L3_fits : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l,
  Z.of_nat (length (bn_TK l)) <= 23 ->
  rbn_L3_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l
    (Z.of_nat (length (bn_TK l))) 0 (bn_TK l).
Definition rbn_L3_ovf : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l,
  23 < Z.of_nat (length (bn_TK l)) ->
  rbn_L3_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l
    23 1 (firstn 23 (bn_TK l)).
Definition rbn_L4_run (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (P D n0 ov0 : Z) (s : list Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  s <> [] -> Forall (fun c => 0 < c < 256) s -> rbn_lsrc W memc P (s ++ [0]) ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (P + Z.of_nat (length s) + 1 <= D \/ D + 48 <= P) ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 11 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 15 = w64 (hd 0 s) ->
  getr regs 13 = w64 (P + 1) -> getr regs 10 = w64 (P + 1) -> getr regs 14 = w64 47 ->
  getr regs 20 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (rbn_cfg RBN_L4 regs memc mdc)
    (rbn_lpost STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L4X [5; 10; 11; 12; 13; 15; 16; 17]
       D n0 wr [(11, nF); (12, ovF)]).
Definition rbn_L4_fits : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  n0 + Z.of_nat (length s) <= 47 ->
  rbn_L4_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    (n0 + Z.of_nat (length s)) ov0 s.
Definition rbn_L4_ovf : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s,
  47 < n0 + Z.of_nat (length s) ->
  rbn_L4_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    47 1 (firstn (Z.to_nat (47 - n0)) s).
Definition rbn_L5_run (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (D n0 ov0 : Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  rbn_lsrc W memc (VAL (A_OBJ 22)) (rbn_lit5 ++ [0]) ->
  VAL (A_OBJ 22) mod 8 = 0 ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (VAL (A_OBJ 22) + 3 <= D \/ D + 48 <= VAL (A_OBJ 22)) ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 16 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 17 = w64 32 -> getr regs 11 = w64 1 ->
  getr regs 15 = w64 3 -> getr regs 13 = w64 47 -> getr regs 14 = w64 (VAL (A_OBJ 22)) ->
  getr regs 20 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (rbn_cfg RBN_L5 regs memc mdc)
    (rbn_lpost STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L5X [5; 6; 10; 11; 12; 16; 17]
       D n0 wr [(16, nF); (12, ovF)]).
Definition rbn_L5_fits : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0,
  n0 + 2 <= 47 ->
  rbn_L5_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 (n0 + 2) ov0 rbn_lit5.
Definition rbn_L5_ovf : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0,
  47 < n0 + 2 ->
  rbn_L5_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs D n0 ov0 47 1
    (firstn (Z.to_nat (47 - n0)) rbn_lit5).
Definition rbn_L6_run (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (A1 D n0 ov0 : Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  rbn_lsrc W memc (VAL (A_OBJ 23)) (rbn_lit6 ++ [0]) ->
  VAL (A_OBJ 23) mod 8 = 0 -> alloc_ceiling <= A1 + 120 -> A1 + 128 <= 2 ^ 47 ->
  (A1 + 128 <= VAL (A_OBJ 23) \/ VAL (A_OBJ 23) + 7 <= A1 + 120) ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (VAL (A_OBJ 23) + 7 <= D \/ D + 48 <= VAL (A_OBJ 23)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D -> (A1 + 128 <= D \/ D + 48 <= A1 + 120) ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 15 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 16 = w64 32 -> getr regs 23 = w64 1 ->
  getr regs 14 = w64 7 -> getr regs 11 = w64 48 -> getr regs 13 = w64 (VAL (A_OBJ 23)) ->
  getr regs 9 = w64 A1 -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (rbn_cfg RBN_L6 regs memc mdc)
    (rbn_lpost STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L6X [5; 10; 12; 15; 16; 17; 23]
       D n0 wr [(15, nF); (12, ovF)]).
Definition rbn_L6_fits : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0,
  n0 + 6 <= 47 ->
  rbn_L6_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 (n0 + 6) ov0 rbn_lit6.
Definition rbn_L6_ovf : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0,
  47 < n0 + 6 ->
  rbn_L6_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 47 1
    (firstn (Z.to_nat (47 - n0)) rbn_lit6).
Definition rbn_L7_run (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (A1 D n0 ov0 : Z) (nF ovF : Z) (wr : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  rbn_lsrc W memc (VAL (A_OBJ 24)) (rbn_lit7 ++ [0]) ->
  VAL (A_OBJ 24) mod 8 = 0 -> alloc_ceiling <= A1 + 120 -> A1 + 128 <= 2 ^ 47 ->
  (A1 + 128 <= VAL (A_OBJ 24) \/ VAL (A_OBJ 24) + 6 <= A1 + 120) ->
  rbn_lbuf STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (VAL (A_OBJ 24) + 6 <= D \/ D + 48 <= VAL (A_OBJ 24)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D -> (A1 + 128 <= D \/ D + 48 <= A1 + 120) ->
  0 <= n0 <= 47 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 23 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 15 = w64 32 -> getr regs 21 = w64 1 ->
  getr regs 14 = w64 6 -> getr regs 11 = w64 48 -> getr regs 13 = w64 (VAL (A_OBJ 24)) ->
  getr regs 9 = w64 A1 -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (rbn_cfg RBN_L7 regs memc mdc)
    (rbn_lpost STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L7X [5; 10; 12; 15; 16; 17; 21; 23]
       D n0 wr [(23, nF); (12, ovF)]).
Definition rbn_L7_fits : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0,
  n0 + 5 <= 47 ->
  rbn_L7_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 (n0 + 5) ov0 rbn_lit7.
Definition rbn_L7_ovf : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0,
  47 < n0 + 5 ->
  rbn_L7_run STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 47 1
    (firstn (Z.to_nat (47 - n0)) rbn_lit7).
Section c.
Hypothesis S1 : rbn_seg1_stmt.
Hypothesis S2 : rbn_seg2_stmt.
Hypothesis S3 : rbn_seg3_stmt.
Hypothesis S4 : rbn_seg4_stmt.
Hypothesis S5 : rbn_seg5_stmt.
Hypothesis S6 : rbn_seg6_stmt.
Hypothesis S7 : rbn_seg7_stmt.
Hypothesis S8 : rbn_seg8_stmt.
Hypothesis S9 : rbn_seg9_stmt.
Hypothesis S10 : rbn_seg10_stmt.
Lemma rbn_from10 : forall X W c, rbn_cx X -> rbn_at10 X W c -> SRr SEGS W c (rbn_post X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
exact (S10 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs).
Qed.
Lemma rbn_from9 : forall X W c, rbn_cx X -> rbn_at9 X W c -> SRr SEGS W c (rbn_post X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S9 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from10 X W2 c2 HX H2).
Qed.
Lemma rbn_from8 : forall X W c, rbn_cx X -> rbn_at8 X W c -> SRr SEGS W c (rbn_post X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S8 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from9 X W2 c2 HX H2).
Qed.
Lemma rbn_from7 : forall X W c, rbn_cx X -> rbn_at7 X W c -> SRr SEGS W c (rbn_post X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S7 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from8 X W2 c2 HX H2).
Qed.
Lemma rbn_from6 : forall X W c, rbn_cx X -> rbn_at6 X W c -> SRr SEGS W c (rbn_post X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S6 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from7 X W2 c2 HX H2).
Qed.
Lemma rbn_from5 : forall X W c, rbn_cx X -> rbn_at5 X W c -> SRr SEGS W c (rbn_post X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & P & -> & Hs).
eapply SRr_bind; [exact (S5 X pos regs1 lyc1 Sc1 W memc1 mdc1 P HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from6 X W2 c2 HX H2).
Qed.
Lemma rbn_from4 : forall X W c, rbn_cx X -> rbn_at4 X W c -> SRr SEGS W c (rbn_post X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & P & -> & Hs).
eapply SRr_bind; [exact (S4 X pos regs1 lyc1 Sc1 W memc1 mdc1 P HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from5 X W2 c2 HX H2).
Qed.
Lemma rbn_from3 : forall X W c, rbn_cx X -> rbn_at3 X W c -> SRr SEGS W c (rbn_post X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S3 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ H2. exact (rbn_from4 X W2 c2 HX H2).
Qed.
Lemma rbn_from2 : forall X W c, rbn_cx X -> rbn_at2 X W c -> SRr SEGS W c (rbn_post X).
Proof.
intros X W c HX (pos & regs1 & lyc1 & Sc1 & memc1 & mdc1 & -> & Hs).
eapply SRr_bind; [exact (S2 X pos regs1 lyc1 Sc1 W memc1 mdc1 HX Hs)|].
intros W2 c2 _ [H2 | H2]; [exact (rbn_from3 X W2 c2 HX H2) | exact (rbn_from10 X W2 c2 HX H2)].
Qed.
Lemma rbn_from1 : forall X, rbn_cx X ->
  SRr SEGS (ri_W X) (cfg_at SEGS (BASE + AF_reac_box_name) (ri_regs X) (ri_memc X) (ri_mdc X)) (rbn_post X).
Proof.
intros X HX. eapply SRr_bind; [exact (S1 X HX)|].
intros W2 c2 _ H2. exact (rbn_from2 X W2 c2 HX H2).
Qed.
Lemma rbn_compose_of : treac_box_name_spec B G.
Proof.
intros ly S W regs mem md ch f said i o name name_len token token_len display display_len sd.
intros HPRE HRO H10 R10 H11 R11 H12 R12 H13 R13 H14 R14 H15 R15 H16 R16 H17 R17 HPR Md Rd Mdl Rdl HIMG HARG
  HFR HEV HLV.
exact (rbn_from1 (RbnIn ly S W regs mem md ch f said i o name name_len token token_len display display_len sd)
  (conj HPRE (conj HRO (conj H10 (conj R10 (conj H11 (conj R11 (conj H12 (conj R12 (conj H13 (conj R13
  (conj H14 (conj R14 (conj H15 (conj R15 (conj H16 (conj R16 (conj H17 (conj R17 (conj HPR (conj Md (conj Rd
  (conj Mdl (conj Rdl (conj HIMG (conj HARG (conj HFR (conj HEV HLV)))))))))))))))))))))))))))).
Qed.
End c.
Theorem rbn_compose :
  rbn_seg1_stmt -> rbn_seg2_stmt -> rbn_seg3_stmt -> rbn_seg4_stmt -> rbn_seg5_stmt ->
  rbn_seg6_stmt -> rbn_seg7_stmt -> rbn_seg8_stmt -> rbn_seg9_stmt -> rbn_seg10_stmt ->
  treac_box_name_spec B G.
Proof.
intros S1 S2 S3 S4 S5 S6 S7 S8 S9 S10.
exact (rbn_compose_of S1 S2 S3 S4 S5 S6 S7 S8 S9 S10).
Qed.
End h.
End f.
End d.
