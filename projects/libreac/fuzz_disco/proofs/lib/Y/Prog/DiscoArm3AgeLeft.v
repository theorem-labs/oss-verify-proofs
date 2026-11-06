(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 501 of its 566 lines of code are new or changed and 1213 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeLeft.v, with its module paths, module names and numbers changed; 723 of its 925 lines of code are new or changed and 364 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC81 YC1h YC45 YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3 DiscoArm3TailK DiscoArm3AgeSt DiscoArm3AgeKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv disco_table_c reac_disco_table_age_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Bytes PropExec.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition LH_PC : Z := 0x9d0.
Definition PL_PC : Z := 0xa84.

Definition lf_ro (r : YP09.region) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r).

Lemma lf_submem : forall rs, submem (map lf_ro rs) rs.
Proof.
  induction rs as [|r rs IH]; cbn [map]; [constructor|].
  apply submem_keep; [|exact IH].
  unfold subregion, lf_ro. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc. exact Hc.
Qed.

Lemma zbv_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact H. Qed.
Lemma U_any : forall E x a, sv_denot E x = Z_to_bv 64 a -> U E x = a mod 2 ^ 64.
Proof. intros E x a H. unfold U. rewrite H, Z_to_bv_unsigned. reflexivity. Qed.
Lemma mod64_32 : forall a, (a mod 2 ^ 64) mod 2 ^ 32 = a mod 2 ^ 32.
Proof. intros a. Z.div_mod_to_equations. lia. Qed.
Lemma sw32_congr : forall x y, x mod 2 ^ 32 = y mod 2 ^ 32 -> bv_swrap 32 x = bv_swrap 32 y.
Proof.
intros x y H. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Zplus_mod x), (Zplus_mod y), H. reflexivity.
Qed.
Lemma sw32_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
Z.div_mod_to_equations. lia.
Qed.
Lemma sw32_id : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma sw64_id : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma dn_lit : forall E c, sv_denot E (SLit c) = Z_to_bv 64 c.
Proof. reflexivity. Qed.
Lemma dn_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma dn_add : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAlu ALU_ADD x y) = Z_to_bv 64 (a + b).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy). apply zbv_eq. unfold zcanon, M64.
rewrite Z.mod_mod by lia. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma dn_mul : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SMd M_MUL x y) = Z_to_bv 64 (a * b).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SMd. cbn [zmd_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy). apply zbv_eq. unfold zcanon, M64.
rewrite Z.mod_mod by lia. rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma dn_sltu : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAlu ALU_SLTU x y) = Z_to_bv 64 (if a mod 2 ^ 64 <? b mod 2 ^ 64 then 1 else 0).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy). apply zbv_eq. unfold zcanon, M64. apply Z.mod_mod. lia.
Qed.
Lemma dn_and : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAlu ALU_AND x y) = Z_to_bv 64 (Z.land (a mod 2 ^ 64) (b mod 2 ^ 64)).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy). apply zbv_eq. unfold zcanon, M64. apply Z.mod_mod. lia.
Qed.
Lemma dn_xor : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAlu ALU_XOR x y) = Z_to_bv 64 (Z.lxor (a mod 2 ^ 64) (b mod 2 ^ 64)).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy). apply zbv_eq. unfold zcanon, M64. apply Z.mod_mod. lia.
Qed.
Lemma dn_sext32 : forall E x a, sv_denot E x = Z_to_bv 64 a ->
  sv_denot E (SExt true 32 x) = Z_to_bv 64 (bv_swrap 32 a).
Proof.
intros E x a Hx. rewrite denot_lit_U, U_SExt. rewrite (U_any E x a Hx). apply zbv_eq. unfold zcanon, M64.
rewrite Z.mod_mod by lia. f_equal. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite mod64_32.
apply sw32_congr. apply Z.mod_mod. lia.
Qed.
Lemma dn_S : forall E v, sv_denot E v = Z_to_bv 64 (Sg E v).
Proof.
intros E v. rewrite denot_lit_U, U_of_S. apply zbv_eq. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
Lemma dn_addw : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAluw ALU_ADD x y) = Z_to_bv 64 (bv_swrap 32 (a + b)).
Proof.
intros E x y a b Hx Hy. rewrite dn_S, S_SAluw. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy), !mod64_32. f_equal. apply sw32_congr.
rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma dn_subw : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAluw ALU_SUB x y) = Z_to_bv 64 (bv_swrap 32 (a - b)).
Proof.
intros E x y a b Hx Hy. rewrite dn_S, S_SAluw. cbn [zalu_raw].
rewrite (U_any E x a Hx), (U_any E y b Hy), !mod64_32. f_equal. apply sw32_congr.
rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma dn_kx : forall E n op, ew E n = Z_to_bv 64 op -> 0 <= op < 256 ->
  sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 57)) (SLit 59)) = Z_to_bv 64 (slot_ser_defs.ser_k op).
Proof.
intros E n op Hn Hop. rewrite denot_lit_U, U_SAlu, U_SAlu, !U_SLit, (U_atom E n op Hn) by lia.
cbn [zalu_raw]. change (Z.land (zcanon 57) 63) with 57. change (Z.land (zcanon 59) 63) with 59.
unfold slot_ser_defs.ser_k. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
rewrite Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
apply zbv_eq. unfold zcanon, M64. Z.div_mod_to_equations. lia.
Qed.
Lemma ser_k_range : forall op, 0 <= slot_ser_defs.ser_k op < 32.
Proof.
intros op. unfold slot_ser_defs.ser_k. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
apply Z.mod_pos_bound. lia.
Qed.
Lemma bt_eq_s : forall u v, - 2 ^ 63 <= u < 2 ^ 63 -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_EQ (Z_to_bv 64 u) (Z_to_bv 64 v) = (u =? v).
Proof.
intros u v Hu Hv. cbn [branch_taken]. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eqb_spec u v) as [->|Hne]; [apply Z.eqb_refl|]. apply Z.eqb_neq. intros Hm. apply Hne.
Z.div_mod_to_equations. lia.
Qed.
Lemma bt_ne_s : forall u v, - 2 ^ 63 <= u < 2 ^ 63 -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_NE (Z_to_bv 64 u) (Z_to_bv 64 v) = negb (u =? v).
Proof.
intros u v Hu Hv. change (branch_taken BC_NE (Z_to_bv 64 u) (Z_to_bv 64 v)) with (negb (branch_taken BC_EQ (Z_to_bv 64 u) (Z_to_bv 64 v))).
rewrite bt_eq_s by assumption. reflexivity.
Qed.
Lemma bt_lt_s : forall u v, - 2 ^ 63 <= u < 2 ^ 63 -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 u) (Z_to_bv 64 v) = (u <? v).
Proof.
intros u v Hu Hv. cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed, !sw64_id by assumption. reflexivity.
Qed.
Lemma bt_ge_s : forall u v, - 2 ^ 63 <= u < 2 ^ 63 -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 u) (Z_to_bv 64 v) = negb (u <? v).
Proof.
intros u v Hu Hv. change (branch_taken BC_GE (Z_to_bv 64 u) (Z_to_bv 64 v)) with (negb (branch_taken BC_LT (Z_to_bv 64 u) (Z_to_bv 64 v))).
rewrite bt_lt_s by assumption. reflexivity.
Qed.
Lemma seq_rel : forall (b : bool) a, 0 <= a < 2 ^ 32 ->
  (if b then (a + 1) mod 2 ^ 32 else a) mod 2 ^ 32 = (bv_swrap 32 a + (if b then 1 else 0)) mod 2 ^ 32.
Proof.
intros b a Ha. destruct b.
- rewrite Z.mod_mod by lia. rewrite (Zplus_mod (bv_swrap 32 a)), sw32_mod, <- Zplus_mod. reflexivity.
- rewrite Z.add_0_r, sw32_mod. reflexivity.
Qed.

Lemma lf_dnF : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma lf_shal : forall E FB c q, ew E 516 = Z_to_bv 64 FB -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  ew E 529 = Z_to_bv 64 (shadow_addr FB) -> 0 <= FB -> 0 <= c -> FB + c < 2 ^ 47 -> FB mod 8 = 0 -> c = 8 * q ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 c) (SLit 3)) (SOff 32 0)) = sv_denot E (SOff 529 q).
Proof.
intros E FB c q HF H32 HSH H0 Hc H1 HFm Hq.
assert (HD : (FB + c) / 8 = FB / 8 + q) by (subst c; Z.div_mod_to_equations; lia).
assert (HB : 0 <= FB / 8 <= FB) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, HF, H32, HSH, !Z.add_0_r.
unfold shadow_addr, SHADOW_OFF in *.
rewrite !unsigned_lit_small by lia.
rewrite (zcanon_id (FB + c)) by (unfold M64; lia). rewrite (zcanon_id 2147450880) by (unfold M64; lia).
rewrite HD. f_equal. lia.
Qed.

Lemma lf_r1 : forall E l t, ew E 563 = Z_to_bv 64 l -> ew E 557 = Z_to_bv 64 t -> 0 <= l < 2 ^ 64 -> 0 <= t < 2 ^ 64 ->
  l < t -> ((l <? t) && (REAC_DISCO_STALE_NS <? t - l))%bool = false ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SOff 557 0) (SMd M_MUL (SOff 563 0) (SLit (-1)))))
    (sv_denot E (SLit 5000000001)) = true.
Proof.
intros E l t Hl Ht Rl Rt Hlt Hs.
rewrite (proj2 (Z.ltb_lt l t) Hlt) in Hs. cbn [andb] in Hs. apply Z.ltb_ge in Hs. unfold REAC_DISCO_STALE_NS in Hs.
rewrite branch_ltu_U, (U_any E _ _ (dn_add E _ _ _ _ (dn_atom E 557 t Ht) (dn_mul E _ _ _ _ (dn_atom E 563 l Hl) (dn_lit E (-1))))).
rewrite U_SLit, (zcanon_id 5000000001) by (unfold M64; lia).
replace (t + l * -1) with (t - l) by lia. rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
Qed.

Lemma lf_cnt : forall E v, ew E 545 = Z_to_bv 64 v -> 1 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff 545 (-1))) (sv_denot E (SLit 0)) = negb (v =? 1).
Proof.
intros E v H Hv. rewrite branch_ne_U, U_SOff, U_SLit, H, unsigned_lit_small by lia.
rewrite (zcanon_id (v + -1)) by (unfold M64; lia). change (zcanon 0) with 0.
destruct (Z.eqb_spec v 1); destruct (Z.eqb_spec (v + -1) 0); try reflexivity; lia.
Qed.

Lemma lf_ck_sub : forall E n0 rm, ew E 556 = Z_to_bv 64 n0 -> ew E 554 = Z_to_bv 64 rm -> 0 <= n0 - rm < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SAluw ALU_SUB (SOff 556 0) (SOff 554 0)))
    (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 554 0) (SLit (-1))) (SOff 556 0))) = true.
Proof.
intros E n0 rm H556 H554 R.
rewrite (dn_subw E _ _ _ _ (dn_atom E 556 n0 H556) (dn_atom E 554 rm H554)), sw32_id by lia.
rewrite (dn_add E _ _ _ _ (dn_mul E _ _ _ _ (dn_atom E 554 rm H554) (dn_lit E (-1))) (dn_atom E 556 n0 H556)).
replace (rm * -1 + n0) with (n0 - rm) by lia. cbn [branch_taken]. unfold bv_eqb. apply Z.eqb_refl.
Qed.

Lemma lf_ck_and : forall E n1 n0 rm, ew E 542 = Z_to_bv 64 n1 -> ew E 556 = Z_to_bv 64 n0 -> ew E 554 = Z_to_bv 64 rm ->
  0 <= n1 < 2 ^ 31 -> n1 = n0 - rm ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_XOR (SOff 542 0)
    (SAluw ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 554 0) (SLit (-1))) (SOff 556 0)) (SLit 0))) (SLit 1)) (SLit 1)))
    (sv_denot E (SLit 0)) = true.
Proof.
intros E n1 n0 rm H542 H556 H554 R Heq.
assert (HA : sv_denot E (SAluw ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 554 0) (SLit (-1))) (SOff 556 0)) (SLit 0)) =
  Z_to_bv 64 n1).
{ rewrite (dn_addw E _ _ _ _ (dn_add E _ _ _ _ (dn_mul E _ _ _ _ (dn_atom E 554 rm H554) (dn_lit E (-1)))
    (dn_atom E 556 n0 H556)) (dn_lit E 0)).
  f_equal. rewrite sw32_id by lia. lia. }
rewrite (dn_and E _ _ _ _ (dn_sltu E _ _ _ _ (dn_xor E _ _ _ _ (dn_atom E 542 n1 H542) HA) (dn_lit E 1)) (dn_lit E 1)).
rewrite Z.lxor_nilpotent. reflexivity.
Qed.

Lemma lf_ck_seq : forall E s1 s0 rm,
  ew E 563 = Z_to_bv 64 s1 -> ew E 553 = Z_to_bv 64 s0 -> ew E 554 = Z_to_bv 64 rm -> 0 <= rm < 2 ^ 64 ->
  s1 mod 2 ^ 32 = (s0 + (if 0 <? rm then 1 else 0)) mod 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff 563 0)))
    (sv_denot E (SAluw ALU_ADD (SOff 553 0) (SAlu ALU_SLTU (SLit 0) (SOff 554 0)))) = true.
Proof.
intros E s1 s0 rm H563 H553 H554 Rrm Hm.
rewrite (dn_sext32 E _ _ (dn_atom E 563 s1 H563)),
  (dn_addw E _ _ _ _ (dn_atom E 553 s0 H553) (dn_sltu E _ _ _ _ (dn_lit E 0) (dn_atom E 554 rm H554))).
rewrite Z.mod_0_l, (Z.mod_small rm) by lia. rewrite (sw32_congr s1 _ Hm).
cbn [branch_taken]. unfold bv_eqb. apply Z.eqb_refl.
Qed.

Lemma ble_cons : forall (b : byte) (bs : list byte),
  bytes_le_to_Z (b :: bs) = bv_unsigned b + 256 * bytes_le_to_Z bs.
Proof.
intros b bs. cbn [bytes_le_to_Z]. apply Bytes.lor_shiftl8_add.
- pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia.
- apply PropExec.bytes_le_to_Z_nonneg.
Qed.
Lemma ble_nth : forall (bs : list byte) j, (j < length bs)%nat ->
  Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat j) mod 256 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
rewrite ble_cons. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg bs) as Hr.
destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
- cbn [nth]. replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia.
  assert (Hd : Z.shiftr (bv_unsigned b + 256 * bytes_le_to_Z bs) (8 + 8 * Z.of_nat j)
               = Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat j)).
  { rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite <- Z.div_div by lia.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs)
      by (symmetry; Z.div_mod_to_equations; lia).
    reflexivity. }
  rewrite Hd. apply IH. cbn [length] in Hj. lia.
Qed.
Lemma lf_nth_firstn : forall {X} n (l : list X) i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros X n. induction n as [|n IH]; intros l i Hi; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.
Lemma lf_nth_skipn : forall {X} n (l : list X) i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros X n. induction n as [|n IH]; intros l i; [reflexivity|].
  destruct l as [|x l]; [destruct i; reflexivity|]. cbn. apply IH.
Qed.
Lemma lf_nth_sub : forall (X : list byte) a l j, 0 <= a -> (j < l)%nat ->
  nth_error (sub X a l) j = nth_error X (Z.to_nat a + j).
Proof. intros. unfold sub. rewrite lf_nth_firstn by lia. apply lf_nth_skipn. Qed.
Lemma u_at_byte : forall (A : list byte) (k : Z) (n j : nat), 0 <= k -> (Z.to_nat k + n <= length A)%nat -> (j < n)%nat ->
  Z_to_bv 8 (YO0f.le_byte (u_at A k n) n j) = nth (Z.to_nat k + j) A (Z_to_bv 8 0).
Proof.
intros A k n j Hk Hn Hj.
assert (LS : length (sub A k n) = n).
{ unfold sub. rewrite length_firstn, length_skipn. lia. }
pose proof (PropExec.bytes_le_to_Z_bound (sub A k n)) as Hb. rewrite LS in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg (sub A k n)) as Hb0.
rewrite (YI04.le_byte_small (u_at A k n) n j) by (unfold u_at; lia).
assert (E : nth j (sub A k n) (Z_to_bv 8 0) = nth (Z.to_nat k + j) A (Z_to_bv 8 0)).
{ pose proof (lf_nth_sub A k n j Hk ltac:(lia)) as HN.
  destruct (nth_error A (Z.to_nat k + j)) as [x|] eqn:EA.
  - rewrite (nth_error_nth _ _ (Z_to_bv 8 0) HN), (nth_error_nth _ _ (Z_to_bv 8 0) EA). reflexivity.
  - apply nth_error_None in EA. lia. }
rewrite <- E. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite <- (ble_nth (sub A k n) j ltac:(lia)). unfold u_at. reflexivity.
Qed.
Lemma u_of_n : forall T : list byte, length T = 400%nat -> 0 <= n_of T -> u_at T 384 4 = n_of T.
Proof.
intros T LT Hn. unfold n_of, s32_at in *.
assert (LS : length (sub T 384 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn; lia).
pose proof (PropExec.bytes_le_to_Z_bound (sub T 384 4)) as Hb. rewrite LS in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg (sub T 384 4)) as Hb0.
unfold u_at in *. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb.
unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *.
change (bv_modulus 32) with (2 ^ 32) in *. Z.div_mod_to_equations. lia.
Qed.
Lemma u_at_range : forall (T : list byte) k (nn : nat), 0 <= u_at T k nn < 2 ^ (8 * Z.of_nat nn).
Proof.
intros T k nn. unfold u_at. pose proof (PropExec.bytes_le_to_Z_bound (sub T k nn)) as Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg (sub T k nn)) as Hb0.
assert (LS : (length (sub T k nn) <= nn)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [exact Hb0|]. eapply Z.lt_le_trans; [exact Hb|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lf_ro_pt : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Ha).
rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma lf_vm_pt : forall (m m' : word -> option byte) a n v, (forall x, m' x = m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hpt H kk Hk. pose proof (H kk Hk) as H1. unfold mbyte in H1 |- *. rewrite Hpt. exact H1. Qed.
Lemma lf_ga_pt : forall (m m' : word -> option byte) a l, (forall x, m' x = m x) ->
  garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof. intros m m' a l Hpt H j Hj. destruct (H j Hj) as [H1 H2]. split; [exact (lf_vm_pt m m' _ _ _ Hpt H1) | exact H2]. Qed.
Lemma lf_rd_pt : forall (W : world SEGS) (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall x, rd W m' x = rd W m x.
Proof. intros W m m' H x. unfold mrestrict. rewrite H. reflexivity. Qed.

Lemma nth_map_bv : forall (A : list byte) j,
  nth j (map (fun b : byte => bv_unsigned b) A) 0 = bv_unsigned (nth j A (Z_to_bv 8 0)).
Proof.
intros A j. rewrite <- (map_nth (fun b : byte => bv_unsigned b) A (Z_to_bv 8 0) j). reflexivity.
Qed.
Lemma mbytes_of_garr8 : forall (m : word -> option byte) (p : Z) (A : list byte),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) A) ->
  forall j, (j < length A)%nat -> mbyte SEGS m (p + Z.of_nat j) = Some (nth j A (Z_to_bv 8 0)).
Proof.
intros m p A HG j Hj.
rewrite (garr8_mbyte SEGS m p _ j HG ltac:(rewrite length_map; exact Hj)).
f_equal. rewrite nth_map_bv. apply Z_to_bv_bv_unsigned.
Qed.
Lemma age_val : forall (m : word -> option byte) (A : list byte) (p k : Z) (n : nat),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) A) -> 0 <= k -> (Z.to_nat k + n <= length A)%nat ->
  val_mem SEGS m (p + k) n (u_at A k n).
Proof.
intros m A p k n HG Hk Hn j Hj.
rewrite (u_at_byte A k n j Hk Hn Hj).
replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia.
apply (mbytes_of_garr8 m p A HG). lia.
Qed.

Lemma lf_regeq : forall (fq : YK11.FPState) E ss ms ss' ms' (H H' : word -> bool) (r r' : bv 5),
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict H ms) -> st_ok_pi (fx := fq) SEGS VAL E ss' (restrict H' ms') ->
  sr_get (ss_regs ss') r' = sr_get (ss_regs ss) r -> getr (ms_regs ms') r' = getr (ms_regs ms) r.
Proof.
  intros fq E ss ms ss' ms' H H' r r' HS HS' Hr.
  rewrite (st_ok_pi_restrict_reg H' E ss' ms' r' HS'), (st_ok_pi_restrict_reg H E ss ms r HS), Hr. reflexivity.
Qed.

Lemma lf_ex : forall cx E (regs : bvmap 5 word) ex (m : nat) v, nth_error ex m = Some v ->
  ew (d_env cx E (a3_vals regs ex)) (563 + m) = v.
Proof.
intros cx E regs ex m v H.
assert (Hm : (m < length ex)%nat) by (apply nth_error_Some; rewrite H; discriminate).
replace (563 + m)%nat with (AT_X + (32 + m))%nat by (unfold AT_X; lia).
rewrite d_env_x by (unfold a3_vals; rewrite length_app, length_map, length_seq; lia).
unfold a3_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia). rewrite length_map, length_seq.
replace (32 + m - 32)%nat with m by lia. apply nth_error_nth. exact H.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBKEEP : d_body_keep_stmt B.

Definition lf_X (cx : dcx) (i n now op : Z) (T0 T1 : list byte) (removed : Z)
  : world SEGS -> (word -> option byte) -> Prop :=
  fun W m => d_sp1 cx i n now W m /\ a3_aged cx now T0 T1 removed W m /\ d_spOP cx op W m.

Definition lh_R (cx : dcx) (now : Z) (T0 T1 : list byte) (removed j : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 10 = w64 (d_obj cx OT + 40 + 48 * j) /\ getr regs 15 = w64 (d_obj cx OT + 40 + 48 * j) /\
  getr regs 12 = w64 0 /\ getr regs 13 = w64 (-384 + 48 * j) /\ getr regs 14 = w64 (n_of T1 - j) /\
  getr regs 17 = w64 (STALE_NS + 1) /\ getr regs 11 = w64 (n_of T1) /\
  getr regs 21 = w64 removed /\ getr regs 23 = w64 removed /\ a3_age_regs cx now T0 regs.

Definition pl_R (cx : dcx) (now : Z) (T0 T1 : list byte) (removed : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 10 = w64 1 /\ getr regs 11 = w64 (n_of T1) /\
  getr regs 21 = w64 removed /\ getr regs 23 = w64 removed /\ a3_age_regs cx now T0 regs.

Definition lf_lh (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (removed j : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\ 0 <= j < n_of T1 /\
    a3_st B MT XM_LIB RLO RHI tfib_K cx LH_PC (EV_HEAD i) h i n now [] (lh_R cx now T0 T1 removed j)
      (lf_X cx i n now op T0 T1 removed) W c.

Definition lf_pl (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (removed : Z)
  : world SEGS -> config -> Prop :=
  fun W c => a3_from B MT XM_LIB RLO RHI tfib_K cx h i n now op T0 W0 c0 W /\
    a3_st B MT XM_LIB RLO RHI tfib_K cx PL_PC (EV_HEAD i) h i n now [] (pl_R cx now T0 T1 removed)
      (lf_X cx i n now op T0 T1 removed) W c.

Lemma lf_sp1_pt : forall cx i n now (W : world SEGS) m m', (forall x, m' x = m x) ->
  d_sp1 cx i n now W m -> d_sp1 cx i n now W m'.
Proof.
intros cx i n now W m m' HP ((H1 & H2) & H3 & H4). pose proof (lf_rd_pt W m m' HP) as HR.
split; [split; [exact (lf_vm_pt _ _ _ _ _ HR H1) | exact (lf_vm_pt _ _ _ _ _ HR H2)]
  | split; [exact (lf_vm_pt _ _ _ _ _ HR H3) | exact (lf_vm_pt _ _ _ _ _ HR H4)]].
Qed.

Lemma lf_X_pt : forall cx i n now op T0 T1 removed (W : world SEGS) m m', (forall x, m' x = m x) ->
  lf_X cx i n now op T0 T1 removed W m -> lf_X cx i n now op T0 T1 removed W m'.
Proof.
intros cx i n now op T0 T1 removed W m m' HP (((H1 & H2) & H3 & H4) & (Hm & Hp & HG) & (H5 & H6)).
pose proof (lf_rd_pt W m m' HP) as HR.
split; [split; [split; [exact (lf_vm_pt _ _ _ _ _ HR H1) | exact (lf_vm_pt _ _ _ _ _ HR H2)]
  | split; [exact (lf_vm_pt _ _ _ _ _ HR H3) | exact (lf_vm_pt _ _ _ _ _ HR H4)]]
  | split; [split; [exact Hm | split; [exact Hp | exact (lf_ga_pt _ _ _ _ HR HG)]]
  | split; [exact (lf_vm_pt _ _ _ _ _ HR H5) | exact (lf_vm_pt _ _ _ _ _ HR H6)]]].
Qed.

Lemma lf_land : forall (fq : YK11.FPState) cx pc h i n now (R : bvmap 5 word -> Prop)
  (X : world SEGS -> (word -> option byte) -> Prop) W ly3 S3 regs mem3 k acc E ss ms md,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx -> frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  d_rL B cx regs -> d_sp0 cx i now W mem3 -> d_body B cx h n [] dsh_loop ly3 S3 W mem3 -> d_E cx E ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  ew E AT_FL = a3_flag cx -> d_land_chk dsh_loop (ss_mem ss) = true ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  (forall x, ms_mem ms x = mem3 x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r = getr regs r) ->
  R (ms_regs ms) -> X W (ms_mem ms) ->
  a3_st B MT XM_LIB RLO RHI tfib_K cx pc (EV_HEAD i) h i n now [] R X W (mkCfg ms md).
Proof.
  intros fq cx pc h i n now R X W ly3 S3 regs mem3 k acc E ss ms md
    Hfrm Hbase Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow HrL Hsp0 Hbody HE HS Hrv Hpc HFL Hchk HJ HPT RG HR HX.
  pose proof (lf_rd_pt W mem3 (ms_mem ms) HPT) as HPTR.
  apply (a3_land_keep B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBKEEP fq cx pc (EV_HEAD i) h i n n now R X W ly3 S3
    mem3 md k acc E ss ms (d_S cx) (d_S cx) Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HS Hrv Hpc HE HFL
    Hchk).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a _ _. unfold aview, mbyte. rewrite HPTR. reflexivity.
  - intros a _ (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite HPT. exact Hb.
  - intros a _ Ha. lia.
  - destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
    unfold d_rL, spZ in *.
    rewrite (RG 2%bv ltac:(cbv; tauto)), (RG 3%bv ltac:(cbv; tauto)), (RG 4%bv ltac:(cbv; tauto)),
      (RG 8%bv ltac:(cbv; tauto)), (RG 9%bv ltac:(cbv; tauto)), (RG 19%bv ltac:(cbv; tauto)),
      (RG 18%bv ltac:(cbv; tauto)), (RG 20%bv ltac:(cbv; tauto)), (RG 27%bv ltac:(cbv; tauto)).
    repeat split; assumption.
  - exact HR.
  - exact HX.
  - destruct Hsp0 as (H1 & H2). split; [exact (lf_vm_pt _ _ _ _ _ HPTR H1) | exact (lf_vm_pt _ _ _ _ _ HPTR H2)].
Qed.

Ltac lf_bvne := let Hq := fresh "Hq" in intro Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq.

Ltac lf_norm HS :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.

Ltac lf_awr := let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; exfalso; revert Ha; apply a3_nowin; vm_compute; reflexivity.

Ltac lf_pt HF :=
  let P := fresh "P" in
  pose proof (lf_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as P; clear HF;
  lazymatch type of P with forall x, ?m2 x = ?m1 x =>
    lazymatch goal with HPT : forall x, m1 x = ?m0 x |- _ =>
      let Q := fresh "Q" in
      assert (Q : forall x, m2 x = m0 x) by (intro x; rewrite P; apply HPT);
      clear P HPT; rename Q into HPT
    end
  end.

Ltac lf_after HS HJ :=
  let ms' := fresh "ms" in let mat := fresh "mat" in let HS' := fresh "HSn" in let HJ' := fresh "HJn" in
  let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
  intros ms' mat HS' HJ' HF HFr HG; cbn [ms_mem YK11.mkst] in HF, HJ';
  clear HFr HG HS HJ; rename HS' into HS; rename HJ' into HJ; lf_pt HF.

Ltac lf_run_to stop HS HJ :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch goal with HEI : img_env _ _ E |- _ =>
    let r := eval vm_compute in (sym_run_toN_pi (ptree_of_list lib_both3_0_listing) 200%N stop ss) in
    lazymatch r with
    | (?ss', ?st) =>
      eapply (SRr_run_to_pi_AJ B LAWS W 200%N stop E ss ss' st ms);
      [ exact HEI | exact HS | vm_compute; reflexivity | exact I | exact HJ | lf_awr | lf_after HS HJ ]
    end end
  end.

Ltac lf_run HS HJ :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch goal with HEI : img_env _ _ E |- _ =>
    let r := eval vm_compute in (sym_runN_pi (ptree_of_list lib_both3_0_listing) 200%N ss) in
    lazymatch r with
    | (?ss', ?st) =>
      eapply (SRr_run_pi_AJ B LAWS W 200%N E ss ss' st ms);
      [ exact HEI | exact HS | vm_compute; reflexivity | exact I | exact HJ | lf_awr | lf_after HS HJ ]
    end end
  end.

Ltac lf_run_call HS HJ :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch goal with HEI : img_env _ _ E |- _ =>
    let r := eval vm_compute in (sym_runN_pi (ptree_of_list lib_both3_0_listing) 200%N ss) in
    lazymatch r with
    | (?ss', PRS_call ?s) =>
      eapply (SRr_run_pi_AJ_call B LAWS W 200%N E ss ss' s ms);
      [ exact HEI | exact HS | vm_compute; reflexivity | exact HJ | lf_awr | lf_after HS HJ ]
    end end
  end.

Ltac lf_br HS :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_step_pi (ptree_of_list lib_both3_0_listing) ss) in
    lazymatch r with
    | PStop (SR_branch ?c ?a ?b) =>
      apply (paj_branch W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS
    end
  end.

Ltac lf_rv HS r :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_pi_restrict_reg H E ss ms r HS);
    let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
  end.

Ltac lf_same HS00 HS r :=
  lazymatch type of HS00 with st_ok_pi _ _ ?E ?ss0 (restrict ?H0 ?ms0) =>
  lazymatch type of HS with st_ok_pi _ _ E ?ss (restrict ?H ?ms) =>
    rewrite (lf_regeq _ E ss0 ms0 ss ms H0 H r r HS00 HS ltac:(vm_compute; reflexivity));
    cbn [ms_regs restrict YK11.mkst]
  end end.

Ltac lf_rg HS00 HS := let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv [In] in Hr;
  repeat (destruct Hr as [<-|Hr];
    [lazymatch goal with |- getr _ ?q = _ => lf_same HS00 HS q; reflexivity end|]); destruct Hr.

Ltac lf_dn KX :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ => apply dn_lit
  | |- sv_denot _ (SAlu ALU_SRL (SAlu ALU_SLL (SOff 564 0) (SLit 57)) (SLit 59)) = _ => exact KX
  | |- sv_denot _ (SAlu ALU_ADD _ _) = _ => eapply dn_add; [lf_dn KX | lf_dn KX]
  | |- sv_denot _ (SMd M_MUL _ _) = _ => eapply dn_mul; [lf_dn KX | lf_dn KX]
  end.

Lemma lf_add0 : forall E x, sv_denot E (SAlu ALU_ADD x (SLit 0)) = sv_denot E x.
Proof.
intros E x. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0.
rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.

Ltac lf_val :=
  lazymatch goal with
  | |- sv_denot _ (SAlu ALU_ADD _ (SLit 0)) = _ => rewrite lf_add0; lf_val
  | |- sv_denot _ (SLit _) = _ =>
      rewrite dn_lit; unfold w64; first [reflexivity | apply zbv_eq; vm_compute; reflexivity]
  | H : sv_denot ?E (SExt true 32 (SOff 563 0)) = _ |- sv_denot ?E (SExt true 32 (SOff 563 0)) = _ =>
      rewrite H; unfold w64; f_equal; lia
  | H : ew ?E 516 = _ |- sv_denot ?E (SOff 516 _) = _ =>
      rewrite (lf_dnF _ 516 _ _ H) by lia; unfold w64, d_obj; cbn [dobj_off]; f_equal; lia
  | H : ew ?E 545 = _ |- sv_denot ?E (SOff 545 _) = _ =>
      rewrite (lf_dnF _ 545 _ _ H) by lia; unfold w64; f_equal; lia
  end.

Ltac lf_reg HS00 HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    first [ lf_same HS00 HS r; assumption | lf_rv HS r; lf_val ] end.

Ltac lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns :=
  lazymatch goal with
  | Hc : branch_taken BC_GEU _ _ = ?b |- _ =>
      rewrite branch_geu_U, (U_atom _ 563 _ A563 LSR), (U_atom _ 557 _ A557 Hnow) in Hc;
      lazymatch b with
      | true => apply negb_true_iff, Z.ltb_ge in Hc
      | false => apply negb_false_iff, Z.ltb_lt in Hc
      end;
      lf_run_to PL_PC HS HJ; lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns
  | Hc : branch_taken BC_LTU _ _ = ?b |- _ =>
      lazymatch b with
      | true => clear Hc; lf_run_to PL_PC HS HJ;
          lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns
      | false =>
          lazymatch goal with Hlv : last_of _ _ < _ |- _ =>
            exfalso; rewrite (lf_r1 _ _ _ A563 A557 LSR Hnow Hlv Hns) in Hc; discriminate Hc end
      end
  | Hc : branch_taken BC_NE _ _ = ?b |- _ =>
      rewrite (lf_cnt _ _ A545 ltac:(lia)) in Hc;
      lazymatch b with
      | true =>
          apply negb_true_iff, Z.eqb_neq in Hc; lf_run_to LH_PC HS HJ;
          refine (LEAFLH _ _ _ _ _ HE HS _ _ _ HJ HPT _ _ _);
          [ reflexivity | reflexivity | vm_compute; reflexivity | lf_rg HS00 HS | lia
          | unfold lh_R, a3_age_regs; repeat match goal with |- _ /\ _ => split end; lf_reg HS00 HS ]
      | false =>
          apply negb_false_iff, Z.eqb_eq in Hc; lf_run_to PL_PC HS HJ;
          lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns
      end
  | Hc : branch_taken BC_EQ _ _ = ?b |- _ =>
      lazymatch b with
      | true =>
          clear Hc; lf_run_to PL_PC HS HJ;
          refine (LEAFPL _ _ _ _ _ HE HS _ _ _ HJ HPT _ _);
          [ reflexivity | reflexivity | vm_compute; reflexivity | lf_rg HS00 HS
          | unfold pl_R, a3_age_regs; repeat match goal with |- _ /\ _ => split end; lf_reg HS00 HS ]
      | false =>
          exfalso; rewrite branch_eq_U, (U_atom _ 552 _ A552 ltac:(lia)), (U_atom _ 554 _ A554 ltac:(lia)),
            Z.eqb_refl in Hc; discriminate Hc
      end
  | |- _ => lf_br HS; lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns
  end.

Lemma lf_e3 : forall cx h i n now op W0 c0 T0 T1 removed W c,
  lf_pl cx h i n now op W0 c0 T0 T1 removed W c ->
  SRr SEGS W c (p_mal B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1).
Proof.
intros cx h i n now op W0 c0 T0 T1 removed W c (HFROM & HST).
destruct HST as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & HB & HJ & HFR & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & (R10 & R11 & R21 & R23 & R22 & R25 & R24 & R26 & R27) & HX & Hsp0 & Hbody).
assert (Hop : 0 <= op < 256).
{ destruct HFROM as (Harm & _). destruct Harm as (fq0 & ly0 & S0 & regs0 & mem0 & md0 & k0 & acc0 & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & Hop0 & _). exact Hop0. }
pose proof HX as (Hsp1 & (Hmod & Hpost & HT1) & (H360 & H352)).
pose proof Hpost as (HlenT1 & Hrem & Hrem0 & HnT1 & Hstale & Hseq & Hok1 & _ & _).
pose proof Hok1 as (HT1n & _). unfold tbl_T1 in HT1n.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HB (conj HJ HFR)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
  as (Hal16 & HSlo & HShi & HFB0 & HFc & HFia & HFo & HFal & _).
pose proof asan_consts as (Hac & _).
assert (HnT0 : n_of T0 < 2 ^ 31).
{ unfold n_of, s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  pose proof (Z.mod_pos_bound (u_at T0 384 4 + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia. }
assert (Hs1 : 0 <= seq_of T1 < 2 ^ (8 * Z.of_nat 4)) by exact (u_at_range T1 392 4).
assert (Hs0 : 0 <= seq_of T0 < 2 ^ (8 * Z.of_nat 4)) by exact (u_at_range T0 392 4).
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hs0.
assert (SEQ : seq_of T1 mod 2 ^ 32 = (s32_at T0 392 + (if 0 <? removed then 1 else 0)) mod 2 ^ 32)
  by (rewrite Hseq; exact (seq_rel (0 <? removed) (seq_of T0) Hs0)).
assert (CH1 : forall E0, d_E cx E0 -> YP09.chunk_ok SEGS (d_env cx E0 (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op]))
  (rd W mem3) (d_A cx) (YP09.mkChunk 360 (CVal 8 (SOff 564 0)))).
{ intros E0 _. apply (chunk_ok_val SEGS _ _ (d_A cx) 360 8 _ op); [|lia|lia|exact H360].
  apply dn_atom. (apply (lf_ex cx E0 regs _ 1); reflexivity). }
assert (CH2 : forall E0, d_E cx E0 -> YP09.chunk_ok SEGS (d_env cx E0 (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op]))
  (rd W mem3) (d_FB cx) (YP09.mkChunk 2552 (CVal 4 (SOff 563 0)))).
{ intros E0 _. apply (chunk_ok_val SEGS _ _ (d_FB cx) 2552 4 _ (seq_of T1)); [|exact Hs1|lia|].
  - apply dn_atom. (apply (lf_ex cx E0 regs _ 0); reflexivity).
  - replace (d_FB cx + 2552) with (d_obj cx OT + 392) by (unfold d_obj; cbn [dobj_off]; lia).
    exact (age_val (rd W mem3) T1 (d_obj cx OT) 392 4 HT1 ltac:(lia) ltac:(rewrite HlenT1; lia)). }
destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx PL_PC h n [] dsh_loop ly3 S3 W regs mem3 md3 k
  [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op] [YP09.mkChunk 360 (CVal 8 (SOff 564 0))]
  [YP09.mkChunk 2552 (CVal 4 (SOff 563 0))] [] [] [] HC HrL Hbody
  (fun E0 HE0 => conj I (conj I (conj (Forall_cons _ _ _ (CH1 E0 HE0) (Forall_nil _))
    (conj (Forall_cons _ _ _ (CH2 E0 HE0) (Forall_nil _)) (conj (Forall_nil _) (conj I (Forall_nil _)))))))
  ltac:(vm_compute; reflexivity)) as (E & HE & HS0).
pose proof (a3_env_img cx E (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op]) HE) as HEI.
destruct (d_E_env cx E (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op]) HE) as (_ & A32 & _ & _ & A516 & A529).
assert (A563 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op])) 563 = Z_to_bv 64 (seq_of T1))
  by (apply (lf_ex cx E regs _ 0); reflexivity).
assert (A564 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op])) 564 = Z_to_bv 64 op)
  by (apply (lf_ex cx E regs _ 1); reflexivity).
assert (A542 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op])) 542 = Z_to_bv 64 (n_of T1))
  by (rewrite (a3_env_reg cx E regs _ 11%bv 542 eq_refl); exact R11).
assert (A553 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op])) 553 = Z_to_bv 64 (s32_at T0 392))
  by (rewrite (a3_env_reg cx E regs _ 22%bv 553 eq_refl); exact R22).
assert (A554 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op])) 554 = Z_to_bv 64 removed)
  by (rewrite (a3_env_reg cx E regs _ 23%bv 554 eq_refl); exact R23).
assert (A556 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op])) 556 = Z_to_bv 64 (n_of T0))
  by (rewrite (a3_env_reg cx E regs _ 25%bv 556 eq_refl); exact R25).
assert (KX := dn_kx _ 564 op A564 Hop).
assert (V24 : getr regs 24 = sv_denot (d_env cx E (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op])) (SOff 516 2160)).
{ rewrite R24, (lf_dnF _ 516 (d_FB cx) 2160 A516 ltac:(lia)). unfold w64, d_obj, dobj_off. reflexivity. }
assert (V10 : getr regs 10 = sv_denot (d_env cx E (a3_vals regs [Z_to_bv 64 (seq_of T1); Z_to_bv 64 op])) (SLit 1))
  by exact R10.
unfold ss_d in HS0.
pose proof (st_ok_pi_submem _ _ _ _ HS0 (lf_submem _) ltac:(vm_compute; reflexivity)) as HS1. clear HS0. lf_norm HS1.
pose proof (st_ok_pi_set_reg _ _ _ 24%bv _ HS1 ltac:(lf_bvne) V24) as HS2. clear HS1. lf_norm HS2.
pose proof (st_ok_pi_set_reg _ _ _ 10%bv _ HS2 ltac:(lf_bvne) V10) as HS. clear HS2. lf_norm HS.
pose proof HS as HS00.
assert (HPT : forall x, mem3 x = mem3 x) by reflexivity.
unfold cfg_at. change (w64 (BASE + PL_PC)) with (Z_to_bv 64 (BASE + PL_PC)).
lf_run HS HJ. lf_br HS.
2: { exfalso. rewrite (lf_ck_sub _ (n_of T0) removed A556 A554 ltac:(lia)) in Hc. discriminate Hc. }
clear Hc. lf_run HS HJ. lf_br HS.
2: { exfalso. rewrite (lf_ck_and _ (n_of T1) (n_of T0) removed A542 A556 A554 ltac:(lia) ltac:(lia)) in Hc.
     discriminate Hc. }
clear Hc. lf_run HS HJ. lf_br HS.
2: { exfalso. rewrite (lf_ck_seq _ (seq_of T1) (s32_at T0 392) removed A563 A553 A554 ltac:(lia) SEQ) in Hc.
     discriminate Hc. }
clear Hc. lf_run HS HJ. lf_br HS.
all: rewrite KX, (dn_lit _ 0), bt_ne_s in Hc by (pose proof (ser_k_range op); lia).
all: first [apply negb_true_iff, Z.eqb_neq in Hc | apply negb_false_iff, Z.eqb_eq in Hc].
all: lf_run_call HS HJ.
all: pose proof (a3_pcall_pi fq _ _ _ _ HS) as HSp; clear HS; rename HSp into HS.
all: apply SRr_ret; split; [exact HFROM|].
all: apply (lf_land fq cx (SIGMA AS_malloc - BASE) h i n now _ _ W ly3 S3 regs mem3 k acc _ _ _ _
  Hfrm HB HFR Hk Hnev Hmo Hacc Hi Hn Hnow HrL Hsp0 Hbody (d_E_env cx E _ HE) HS eq_refl eq_refl (d_env_fl cx E _)
  ltac:(vm_compute; reflexivity) HJ HPT ltac:(lf_rg HS00 HS)).
all: cbn beta.
all: lazymatch goal with
  | |- d_sp1 _ _ _ _ _ _ /\ _ =>
      split; [exact (lf_sp1_pt cx i n now W _ _ HPT Hsp1)|];
      split; [exists removed; split; [exact Hmod | exact Hpost]|];
      exact (lf_ga_pt _ _ _ _ (lf_rd_pt W _ _ HPT) HT1)
  | |- _ =>
      split; [lf_rv HS (1%bv : bv 5); exact (codeptr_val _ P_MAL_RA HEI)|];
      split; [lf_rv HS (10%bv : bv 5); etransitivity; [lf_dn KX|];
        unfold w64, a3_cap, slot_ser_defs.ser_cap; destruct (Z.eqb_spec (slot_ser_defs.ser_k op) 0); f_equal; lia|];
      split; [lf_rv HS (21%bv : bv 5); etransitivity; [lf_dn KX|];
        unfold w64, a3_cap, slot_ser_defs.ser_cap; destruct (Z.eqb_spec (slot_ser_defs.ser_k op) 0); f_equal; lia|];
      lf_same HS00 HS (27%bv : bv 5); exact R27
  end.
Qed.

Lemma lf_e1 : forall cx h i n now op W0 c0 T0 T1 removed W c,
  q_chk B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 removed W c ->
  SRr SEGS W c (fun W' c' => lf_lh cx h i n now op W0 c0 T0 T1 removed 0 W' c' \/
    lf_pl cx h i n now op W0 c0 T0 T1 removed W' c').
Proof.
intros cx h i n now op W0 c0 T0 T1 removed W c (HFROM & HST).
destruct HST as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & HB & HJ & HFR & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & (R21 & R23 & R22 & R25 & R24 & R26 & R27) & HX & Hsp0 & Hbody).
pose proof HX as (Hsp1 & (Hmod & Hpost & HT1) & _).
pose proof Hpost as (HlenT1 & Hrem & Hrem0 & HnT1 & Hstale & Hseq & Hok1 & _ & _).
pose proof Hok1 as (HT1n & _). unfold tbl_T1 in HT1n.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HB (conj HJ HFR)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
  as (Hal16 & HSlo & HShi & HFB0 & HFc & HFia & HFo & HFal & _).
pose proof asan_consts as (Hac & _).
assert (HnT0 : n_of T0 < 2 ^ 31).
{ unfold n_of, s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  pose proof (Z.mod_pos_bound (u_at T0 384 4 + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia. }
pose proof (u_at_range T1 384 4) as HU. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HU.
assert (CH : forall E0, d_E cx E0 -> YP09.chunk_ok SEGS (d_env cx E0 (a3_vals regs [Z_to_bv 64 (u_at T1 384 4)]))
  (rd W mem3) (d_FB cx) (YP09.mkChunk 2544 (CVal 4 (SOff 563 0)))).
{ intros E0 _. apply (chunk_ok_val SEGS _ _ (d_FB cx) 2544 4 _ (u_at T1 384 4)); [|exact HU|lia|].
  - apply dn_atom. apply (lf_ex cx E0 regs _ 0). reflexivity.
  - replace (d_FB cx + 2544) with (d_obj cx OT + 384) by (unfold d_obj; cbn [dobj_off]; lia).
    exact (age_val (rd W mem3) T1 (d_obj cx OT) 384 4 HT1 ltac:(lia) ltac:(rewrite HlenT1; lia)). }
destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx P_CHK_RA h n [] dsh_loop ly3 S3 W regs mem3 md3 k
  [Z_to_bv 64 (u_at T1 384 4)] [] [YP09.mkChunk 2544 (CVal 4 (SOff 563 0))] [] [] [] HC HrL Hbody
  (fun E0 HE0 => conj I (conj I (conj (Forall_nil _) (conj (Forall_cons _ _ _ (CH E0 HE0) (Forall_nil _))
    (conj (Forall_nil _) (conj I (Forall_nil _)))))))
  ltac:(vm_compute; reflexivity)) as (E & HE & HS0).
pose proof (a3_env_img cx E (a3_vals regs [Z_to_bv 64 (u_at T1 384 4)]) HE) as HEI.
destruct (d_E_env cx E (a3_vals regs [Z_to_bv 64 (u_at T1 384 4)]) HE) as (_ & _ & _ & _ & EF & _).
assert (A516 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (u_at T1 384 4)])) 516 = Z_to_bv 64 (d_FB cx)) by exact EF.
assert (A563 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (u_at T1 384 4)])) 563 = Z_to_bv 64 (u_at T1 384 4))
  by (apply (lf_ex cx E regs _ 0); reflexivity).
assert (A552 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (u_at T1 384 4)])) 552 = Z_to_bv 64 removed)
  by (rewrite (a3_env_reg cx E regs _ 21%bv 552 eq_refl); exact R21).
assert (A554 : ew (d_env cx E (a3_vals regs [Z_to_bv 64 (u_at T1 384 4)])) 554 = Z_to_bv 64 removed)
  by (rewrite (a3_env_reg cx E regs _ 23%bv 554 eq_refl); exact R23).
assert (TNX : sv_denot (d_env cx E (a3_vals regs [Z_to_bv 64 (u_at T1 384 4)])) (SExt true 32 (SOff 563 0)) =
  Z_to_bv 64 (n_of T1)) by (rewrite (dn_sext32 _ _ _ (dn_atom _ 563 _ A563)); reflexivity).
assert (V24 : getr regs 24 = sv_denot (d_env cx E (a3_vals regs [Z_to_bv 64 (u_at T1 384 4)])) (SOff 516 2160)).
{ rewrite R24, (lf_dnF _ 516 (d_FB cx) 2160 A516 ltac:(lia)). unfold w64, d_obj, dobj_off. reflexivity. }
unfold ss_d in HS0.
pose proof (st_ok_pi_submem _ _ _ _ HS0 (lf_submem _) ltac:(vm_compute; reflexivity)) as HS1. clear HS0. lf_norm HS1.
pose proof (st_ok_pi_set_reg _ _ _ 24%bv _ HS1 ltac:(lf_bvne) V24) as HS. clear HS1. lf_norm HS.
pose proof HS as HS00.
assert (HPT : forall x, mem3 x = mem3 x) by reflexivity.
unfold cfg_at. change (w64 (BASE + P_CHK_RA)) with (Z_to_bv 64 (BASE + P_CHK_RA)).
lf_run_to LH_PC HS HJ. lf_br HS.
- rewrite (dn_lit _ 0), TNX, bt_ge_s in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hn0.
  lf_run_to PL_PC HS HJ. lf_br HS.
  + clear Hc. lf_run_to PL_PC HS HJ.
    apply SRr_ret. right. split; [exact HFROM|].
    apply (lf_land fq cx PL_PC h i n now _ _ W ly3 S3 regs mem3 k acc _ _ _ _
      Hfrm HB HFR Hk Hnev Hmo Hacc Hi Hn Hnow HrL Hsp0 Hbody (d_E_env cx E _ HE) HS eq_refl eq_refl (d_env_fl cx E _)
      ltac:(vm_compute; reflexivity) HJ HPT ltac:(lf_rg HS00 HS)).
    * unfold pl_R, a3_age_regs. repeat match goal with |- _ /\ _ => split end; lf_reg HS00 HS.
    * exact (lf_X_pt cx i n now op T0 T1 removed W _ _ HPT HX).
  + exfalso. rewrite branch_eq_U, (U_atom _ 552 _ A552 ltac:(lia)), (U_atom _ 554 _ A554 ltac:(lia)), Z.eqb_refl in Hc.
    discriminate Hc.
- rewrite (dn_lit _ 0), TNX, bt_ge_s in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
  lf_run_to LH_PC HS HJ.
  apply SRr_ret. left. split; [exact HFROM|]. split; [lia|].
  apply (lf_land fq cx LH_PC h i n now _ _ W ly3 S3 regs mem3 k acc _ _ _ _
    Hfrm HB HFR Hk Hnev Hmo Hacc Hi Hn Hnow HrL Hsp0 Hbody (d_E_env cx E _ HE) HS eq_refl eq_refl (d_env_fl cx E _)
    ltac:(vm_compute; reflexivity) HJ HPT ltac:(lf_rg HS00 HS)).
  + unfold lh_R, a3_age_regs. repeat match goal with |- _ /\ _ => split end; lf_reg HS00 HS.
  + exact (lf_X_pt cx i n now op T0 T1 removed W _ _ HPT HX).
Qed.

Lemma lf_e2 : forall cx h i n now op W0 c0 T0 T1 removed j W c,
  lf_lh cx h i n now op W0 c0 T0 T1 removed j W c ->
  SRr SEGS W c (fun W' c' => lf_lh cx h i n now op W0 c0 T0 T1 removed (j + 1) W' c' \/
    lf_pl cx h i n now op W0 c0 T0 T1 removed W' c').
Proof.
intros cx h i n now op W0 c0 T0 T1 removed j W c (HFROM & Hj & HST).
destruct HST as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & HB & HJ & HFR & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & (R10 & R15 & R12 & R13 & R14 & R17 & R11 & R21 & R23 & R22 & R25 & R24 & R26 & R27) &
  HX & Hsp0 & Hbody).
pose proof HX as (Hsp1 & (Hmod & Hpost & HT1) & _).
pose proof Hpost as (HlenT1 & Hrem & Hrem0 & HnT1 & Hstale & Hseq & Hok1 & _ & _).
pose proof Hok1 as (HT1n & _). unfold tbl_T1 in HT1n.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HB (conj HJ HFR)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
  as (Hal16 & HSlo & HShi & HFB0 & HFc & HFia & HFo & HFal & _).
pose proof asan_consts as (Hac & _).
assert (HnT0 : n_of T0 < 2 ^ 31).
{ unfold n_of, s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  pose proof (Z.mod_pos_bound (u_at T0 384 4 + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia. }
assert (LSR : 0 <= last_of T1 j < 2 ^ 64) by exact (u_at_range T1 (48 * j + 40) 8).
pose proof (Hstale j Hj) as Hns. unfold disco_stale in Hns.
assert (HLV : val_mem SEGS (rd W mem3) (d_FB cx + (2200 + 48 * j)) 8 (last_of T1 j)).
{ replace (d_FB cx + (2200 + 48 * j)) with (d_obj cx OT + (48 * j + 40)) by (unfold d_obj; cbn [dobj_off]; lia).
  exact (age_val (rd W mem3) T1 (d_obj cx OT) (48 * j + 40) 8 HT1 ltac:(lia) ltac:(rewrite HlenT1; lia)). }
assert (CH : forall E0, d_E cx E0 -> YP09.chunk_ok SEGS (d_env cx E0 (a3_vals regs [Z_to_bv 64 (last_of T1 j)]))
  (rd W mem3) (d_FB cx) (YP09.mkChunk (2200 + 48 * j) (CVal 8 (SOff 563 0)))).
{ intros E0 _. apply (chunk_ok_val SEGS _ _ (d_FB cx) (2200 + 48 * j) 8 _ (last_of T1 j)); [|exact LSR|lia|exact HLV].
  apply dn_atom. apply (lf_ex cx E0 regs _ 0). reflexivity. }
assert (LEAFLH : forall E1 vals ss ms md, d_E cx E1 ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E1 vals) ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = LH_PC ->
  d_land_chk dsh_loop (ss_mem ss) = true ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  (forall x, ms_mem ms x = mem3 x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r = getr regs r) ->
  j + 1 < n_of T1 -> lh_R cx now T0 T1 removed (j + 1) (ms_regs ms) ->
  SRr SEGS W (mkCfg ms md) (fun W' c' => lf_lh cx h i n now op W0 c0 T0 T1 removed (j + 1) W' c' \/
    lf_pl cx h i n now op W0 c0 T0 T1 removed W' c')).
{ intros E1 vals ss ms md HE1 HS1 Hrv Hpc Hchk HJ1 HPT1 RG Hlt HR1.
  apply SRr_ret. left. split; [exact HFROM|]. split; [lia|].
  exact (lf_land fq cx LH_PC h i n now _ _ W ly3 S3 regs mem3 k acc _ ss ms md Hfrm HB HFR Hk Hnev Hmo Hacc Hi Hn Hnow HrL
    Hsp0 Hbody (d_E_env cx E1 vals HE1) HS1 Hrv Hpc (d_env_fl cx E1 vals) Hchk HJ1 HPT1 RG HR1
    (lf_X_pt cx i n now op T0 T1 removed W _ _ HPT1 HX)). }
assert (LEAFPL : forall E1 vals ss ms md, d_E cx E1 ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E1 vals) ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = PL_PC ->
  d_land_chk dsh_loop (ss_mem ss) = true ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  (forall x, ms_mem ms x = mem3 x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r = getr regs r) ->
  pl_R cx now T0 T1 removed (ms_regs ms) ->
  SRr SEGS W (mkCfg ms md) (fun W' c' => lf_lh cx h i n now op W0 c0 T0 T1 removed (j + 1) W' c' \/
    lf_pl cx h i n now op W0 c0 T0 T1 removed W' c')).
{ intros E1 vals ss ms md HE1 HS1 Hrv Hpc Hchk HJ1 HPT1 RG HR1.
  apply SRr_ret. right. split; [exact HFROM|].
  exact (lf_land fq cx PL_PC h i n now _ _ W ly3 S3 regs mem3 k acc _ ss ms md Hfrm HB HFR Hk Hnev Hmo Hacc Hi Hn Hnow HrL
    Hsp0 Hbody (d_E_env cx E1 vals HE1) HS1 Hrv Hpc (d_env_fl cx E1 vals) Hchk HJ1 HPT1 RG HR1
    (lf_X_pt cx i n now op T0 T1 removed W _ _ HPT1 HX)). }
unfold cfg_at. change (w64 (BASE + LH_PC)) with (Z_to_bv 64 (BASE + LH_PC)).
assert (Hj8 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
destruct Hj8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
all: lazymatch type of Hj with 0 <= ?J < _ =>
  destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx LH_PC h n [] dsh_loop ly3 S3 W regs mem3 md3 k
    [Z_to_bv 64 (last_of T1 J)] [] [YP09.mkChunk (2200 + 48 * J) (CVal 8 (SOff 563 0))] [] [] [] HC HrL Hbody
    (fun E0 HE0 => conj I (conj I (conj (Forall_nil _) (conj (Forall_cons _ _ _ (CH E0 HE0) (Forall_nil _))
      (conj (Forall_nil _) (conj I (Forall_nil _)))))))
    ltac:(vm_compute; reflexivity)) as (E & HE & HS0) end.
all: lazymatch type of Hj with 0 <= ?J < _ =>
  let EE := constr:(d_env cx E (a3_vals regs [Z_to_bv 64 (last_of T1 J)])) in
  pose proof (a3_env_img cx E (a3_vals regs [Z_to_bv 64 (last_of T1 J)]) HE) as HEI;
  destruct (d_E_env cx E (a3_vals regs [Z_to_bv 64 (last_of T1 J)]) HE) as (_ & E32 & _ & _ & EF & ESH);
  assert (A516 : ew EE 516 = Z_to_bv 64 (d_FB cx)) by exact EF;
  assert (A529 : ew EE 529 = Z_to_bv 64 (shadow_addr (d_FB cx))) by exact ESH;
  assert (A32 : ew EE 32 = Z_to_bv 64 SHADOW_OFF) by exact E32;
  assert (A563 : ew EE 563 = Z_to_bv 64 (last_of T1 J)) by (apply (lf_ex cx E regs _ 0); reflexivity);
  assert (A557 : ew EE 557 = Z_to_bv 64 now) by (rewrite (a3_env_reg cx E regs _ 26%bv 557 eq_refl); exact R26);
  assert (A545 : ew EE 545 = Z_to_bv 64 (n_of T1 - J)) by (rewrite (a3_env_reg cx E regs _ 14%bv 545 eq_refl); exact R14);
  assert (A552 : ew EE 552 = Z_to_bv 64 removed) by (rewrite (a3_env_reg cx E regs _ 21%bv 552 eq_refl); exact R21);
  assert (A554 : ew EE 554 = Z_to_bv 64 removed) by (rewrite (a3_env_reg cx E regs _ 23%bv 554 eq_refl); exact R23);
  assert (V24 : getr regs 24 = sv_denot EE (SOff 516 2160))
    by (rewrite R24, (lf_dnF _ 516 (d_FB cx) 2160 A516 ltac:(lia)); unfold w64, d_obj, dobj_off; reflexivity);
  assert (V10 : getr regs 10 = sv_denot EE (SOff 516 (2200 + 48 * J)))
    by (rewrite R10, (lf_dnF _ 516 (d_FB cx) _ A516 ltac:(lia)); unfold w64, d_obj; cbn [dobj_off]; f_equal; lia);
  assert (V15 : getr regs 15 = sv_denot EE (SOff 516 (2200 + 48 * J)))
    by (rewrite R15, (lf_dnF _ 516 (d_FB cx) _ A516 ltac:(lia)); unfold w64, d_obj; cbn [dobj_off]; f_equal; lia);
  assert (V12 : getr regs 12 = sv_denot EE (SLit 0)) by exact R12;
  assert (V13 : getr regs 13 = sv_denot EE (SLit (-384 + 48 * J))) by exact R13;
  assert (V17 : getr regs 17 = sv_denot EE (SLit (STALE_NS + 1))) by exact R17;
  assert (VAL : sv_denot EE (SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 (2200 + 48 * J)) (SLit 3)) (SOff 32 0)) =
    sv_denot EE (SOff 529 (275 + 6 * J)))
    by (apply (lf_shal _ (d_FB cx)); [exact A516 | exact A32 | exact A529 | lia | lia | lia | lia | lia])
  end.
all: unfold ss_d in HS0.
all: pose proof (st_ok_pi_submem _ _ _ _ HS0 (lf_submem _) ltac:(vm_compute; reflexivity)) as HS1; clear HS0.
all: lf_norm HS1.
all: pose proof (st_ok_pi_set_reg _ _ _ 24%bv _ HS1 ltac:(lf_bvne) V24) as HS2; clear HS1.
all: lf_norm HS2.
all: pose proof (st_ok_pi_set_reg _ _ _ 10%bv _ HS2 ltac:(lf_bvne) V10) as HS1; clear HS2.
all: lf_norm HS1.
all: pose proof (st_ok_pi_set_reg _ _ _ 15%bv _ HS1 ltac:(lf_bvne) V15) as HS2; clear HS1.
all: lf_norm HS2.
all: pose proof (st_ok_pi_set_reg _ _ _ 12%bv _ HS2 ltac:(lf_bvne) V12) as HS1; clear HS2.
all: lf_norm HS1.
all: pose proof (st_ok_pi_set_reg _ _ _ 13%bv _ HS1 ltac:(lf_bvne) V13) as HS2; clear HS1.
all: lf_norm HS2.
all: pose proof (st_ok_pi_set_reg _ _ _ 17%bv _ HS2 ltac:(lf_bvne) V17) as HS1; clear HS2.
all: lf_norm HS1.
all: pose proof (st_ok_pi_add_alias _ _ _ _ _ HS1 VAL) as HS; clear HS1.
all: lf_norm HS.
all: pose proof HS as HS00.
all: assert (HPT : forall x, mem3 x = mem3 x) by reflexivity.
all: lf_run_to PL_PC HS HJ.
- lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns.
- lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns.
- lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns.
- lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns.
- lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns.
- lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns.
- lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns.
- lf_go2 LEAFLH LEAFPL HE HS HJ HPT HS00 A563 A557 A545 A552 A554 LSR Hnow Hns.
Qed.

Lemma lf_loop : forall cx h i n now op W0 c0 T0 T1 removed (k : nat) j W c,
  Z.of_nat k = n_of T1 - j -> lf_lh cx h i n now op W0 c0 T0 T1 removed j W c ->
  SRr SEGS W c (lf_pl cx h i n now op W0 c0 T0 T1 removed).
Proof.
intros cx h i n now op W0 c0 T0 T1 removed k. induction k as [|k IH]; intros j W c Hk H.
- exfalso. destruct H as (_ & Hj & _). lia.
- eapply SRr_bind; [exact (lf_e2 cx h i n now op W0 c0 T0 T1 removed j W c H)|].
  intros W' c' _ [H' | H'].
  + exact (IH (j + 1) W' c' ltac:(lia) H').
  + apply SRr_ret. exact H'.
Qed.

Theorem a3_e_left : e_left_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 removed W c HQ.
eapply SRr_bind; [exact (lf_e1 cx h i n now op W0 c0 T0 T1 removed W c HQ)|].
intros W1 c1 _ [H1 | H1].
- pose proof H1 as (_ & Hj & _).
  eapply SRr_bind; [exact (lf_loop cx h i n now op W0 c0 T0 T1 removed (Z.to_nat (n_of T1 - 0)) 0 W1 c1
    ltac:(rewrite Z2Nat.id by lia; reflexivity) H1)|].
  intros W2 c2 _ H2. exact (lf_e3 cx h i n now op W0 c0 T0 T1 removed W2 c2 H2).
- exact (lf_e3 cx h i n now op W0 c0 T0 T1 removed W1 c1 H1).
Qed.

End h.
End f.
End d.
