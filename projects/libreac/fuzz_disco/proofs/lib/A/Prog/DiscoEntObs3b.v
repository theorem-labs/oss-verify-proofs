(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 678 of its 708 lines of code are new or changed and 39 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YC88 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoEntObsCuts DiscoEntObs4.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe slot_known slot_newent CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma zc_small : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma UA0 : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = zcanon v.
Proof. intros E n v H. rewrite U_SOff, H, Z.add_0_r, unsigned_lit. unfold zcanon. apply Zmod_mod. Qed.
Lemma UA32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 (SOff n 0)) = zcanon (bv_swrap 32 v).
Proof.
intros E n v H Hv. rewrite U_SExt, (UA0 E n v H), (zc_small v) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small v) by lia. reflexivity.
Qed.
Lemma UA8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff n 0)) = v.
Proof.
intros E n v H Hv. rewrite U_SExt, (UA0 E n v H), (zc_small v) by lia. change (2 ^ Z.of_N 8) with 256.
rewrite (Z.mod_small v) by lia. apply zc_small. lia.
Qed.
Lemma sw32_case : forall a, 0 <= a < 2 ^ 32 -> bv_swrap 32 a = if a <? 2 ^ 31 then a else a - 2 ^ 32.
Proof.
intros a Ha. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ (Z.of_N 32 - 1)) with 2147483648. change (2 ^ 31) with 2147483648.
change (2 ^ 32) with 4294967296 in *.
destruct (Z.ltb_spec a 2147483648); lia.
Qed.
Lemma zc_sw : forall a, 0 <= a < 2 ^ 32 -> zcanon (bv_swrap 32 a) = if a <? 2 ^ 31 then a else a + (2 ^ 64 - 2 ^ 32).
Proof.
intros a Ha. rewrite sw32_case by exact Ha. unfold zcanon, M64. destruct (Z.ltb_spec a (2 ^ 31)); lia.
Qed.
Lemma zltu_sw : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  (zcanon (bv_swrap 32 a) <? zcanon (bv_swrap 32 b)) = (a <? b).
Proof.
intros a b Ha Hb. rewrite !zc_sw by assumption.
destruct (Z.ltb_spec a (2 ^ 31)), (Z.ltb_spec b (2 ^ 31)); apply Bool.eq_iff_eq_true; rewrite !Z.ltb_lt; lia.
Qed.
Lemma fu_uat : forall (L : list byte) k n, CtrlParsed.fu L k n = u_at L (Z.of_nat k) n.
Proof. intros L k n. unfold CtrlParsed.fu, CtrlParsed.fld, u_at, sub. rewrite Nat2Z.id. reflexivity. Qed.
Lemma uat1_fb : forall (L : list byte) k, (k < length L)%nat -> u_at L (Z.of_nat k) 1 = CtrlParsed.fb L k.
Proof.
intros L k Hk. unfold u_at, sub, CtrlParsed.fb. rewrite Nat2Z.id.
destruct (nth_split L (CtrlParsed.zb 0) Hk) as (l1 & l2 & EL & Hl1). rewrite EL at 1.
rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app firstn bytes_le_to_Z].
rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.
Lemma s32_sw : forall v, 0 <= v < 2 ^ 32 -> CtrlParsed.s32 v = bv_swrap 32 v.
Proof. intros v Hv. unfold CtrlParsed.s32. rewrite sw32_case by exact Hv. reflexivity. Qed.
Lemma sight_S12 : forall Sg, disco_classify_c.sighting_ok Sg -> sighting_S1 Sg /\ sighting_S2 Sg.
Proof.
intros Sg (L & Hr & Hh).
assert (U8 : 0 <= u_at Sg 8 4 < 2 ^ 32).
{ unfold u_at. pose proof (bytes_le_to_Z_bound (sub Sg 8 4)) as B1. pose proof (bytes_le_to_Z_nonneg (sub Sg 8 4)).
  assert (length (sub Sg 8 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn; lia). rewrite H0 in B1. lia. }
assert (E8 : CtrlParsed.fu Sg 8 4 = u_at Sg 8 4) by (rewrite fu_uat; reflexivity).
rewrite E8, s32_sw in Hr by exact U8.
assert (E12 : CtrlParsed.fb Sg 12 = u_at Sg 12 1) by (rewrite <- (uat1_fb Sg 12) by lia; reflexivity).
assert (E13 : CtrlParsed.fb Sg 13 = u_at Sg 13 1) by (rewrite <- (uat1_fb Sg 13) by lia; reflexivity).
assert (E14 : CtrlParsed.fb Sg 14 = u_at Sg 14 1) by (rewrite <- (uat1_fb Sg 14) by lia; reflexivity).
rewrite E12, E13, E14 in Hh.
split.
- unfold sighting_S1, s_role, s32_at. lia.
- unfold sighting_S2, s_hd, s_din, s_dout. lia.
Qed.

Lemma u_at_range : forall (L : list byte) k n, (Z.to_nat k + n <= length L)%nat -> 0 <= u_at L k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros L k n Hl. assert (Hsub : length (sub L k n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_le_to_Z_bound (sub L k n)) as Hb1. pose proof (bytes_le_to_Z_nonneg (sub L k n)) as Hb0. rewrite Hsub in Hb1.
unfold u_at. lia.
Qed.
Lemma u_at_r1 : forall (L : list byte) k, (Z.to_nat k + 1 <= length L)%nat -> 0 <= u_at L k 1 < 256.
Proof. intros L k H. pose proof (u_at_range L k 1 H). change (2 ^ (8 * Z.of_nat 1)) with 256 in *. lia. Qed.
Lemma u_at_r4 : forall (L : list byte) k, (Z.to_nat k + 4 <= length L)%nat -> 0 <= u_at L k 4 < 2 ^ 32.
Proof. intros L k H. pose proof (u_at_range L k 4 H). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in *. lia. Qed.
Lemma u_at_r8 : forall (L : list byte) k, (Z.to_nat k + 8 <= length L)%nat -> 0 <= u_at L k 8 < 2 ^ 64.
Proof. intros L k H. pose proof (u_at_range L k 8 H). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in *. lia. Qed.
Lemma obs_fields : forall T G ow now T' ret r,
  length T = 400%nat -> length G = 24%nat -> 0 <= r < n_of T -> n_of T <= 8 -> 0 <= now -> 0 <= ow <= 1 ->
  tbl_T2 T -> tbl_T4 T -> sighting_S1 G -> sighting_S2 G ->
  find_res T (s_mac G) r -> reac_disco_table_observe_c.observe_model T G ow now T' ret ->
  length T' = 400%nat /\
  (forall j, 0 <= j < 8 -> mac_of T' j = mac_of T j) /\
  u_at T' 384 4 = u_at T 384 4 /\
  bv_swrap 32 (u_at T' (48 * r + 8) 4) = slot_known.want_role (s_role G) (role_of_e T r) /\
  u_at T' (48 * r + 12) 1 = (if s_hd G =? 0 then hd_of T r else 1) /\
  u_at T' (48 * r + 13) 1 = (if s_hd G =? 0 then din_of T r else s_din G) /\
  u_at T' (48 * r + 14) 1 = (if s_hd G =? 0 then dout_of T r else s_dout G) /\
  u_at T' (48 * r + 15) 1 = (if s_fam G =? 0 then reac_disco_table_observe_c.fam_of T r else s_fam G) /\
  u_at T' (48 * r + 16) 1 = (if s_slots G =? 0 then reac_disco_table_observe_c.slots_of T r else s_slots G) /\
  bv_swrap 32 (u_at T' (48 * r + 20) 4) =
    bv_swrap 32 (if reac_disco_table_observe_c.ch_of T r <? s_ch G then s_ch G else reac_disco_table_observe_c.ch_of T r) /\
  bv_swrap 32 (u_at T' (48 * r + 24) 4) = (if ow =? 0 then owned_of T r else 1) /\
  u_at T' (48 * r + 32) 8 = u_at T (48 * r + 32) 8 /\
  u_at T' (48 * r + 40) 8 = now mod 2 ^ 64 /\
  ret = (if slot_observe.c_any T G ow r then 1 else 0).
Proof.
intros T G ow now T' ret r LT LG Hr Hn8 Hn How T2 T4 S1 S2 FR OM.
pose proof (slot_observe.known_arm T G ow now T' ret r FR ltac:(lia) OM) as EK.
destruct (slot_observe.ok_facts T G ow now r T' ret LT LG ltac:(lia) EK)
  as (LT' & EM & E384 & E8 & E12 & E13 & E14 & E15 & E16 & E20 & E24 & E32 & E40 & E392 & Eret).
destruct (T4 r Hr) as (Hhd & _ & Hown).
unfold u_at. rewrite E384, E8, E12, E13, E14, E15, E16, E20, E24, E32, E40.
split; [exact LT'|]. split; [exact EM|]. split; [reflexivity|].
split; [exact (slot_known.role_field T G r S1 (T2 r Hr))|].
split; [exact (slot_known.hd_field T G r S2 Hhd)|].
split; [exact (slot_known.din_field T G r S2)|].
split; [exact (slot_known.dout_field T G r S2)|].
split; [exact (slot_known.fam_field T G r)|].
split; [exact (slot_known.slots_field T G r)|].
split; [exact (slot_known.ch_field T G r)|].
split; [exact (slot_known.own_field T ow r How Hown)|].
split; [reflexivity|].
split; [apply bytes_le_Z_to_le; exact Hn|].
exact Eret.
Qed.



Lemma lxor_nn : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.lxor a b.
Proof. intros. apply Z.lxor_nonneg. lia. Qed.
Lemma lor_nn : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.lor a b.
Proof. intros. apply Z.lor_nonneg. lia. Qed.
Lemma big_diff_eq : forall a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 : Z,
  0 <= a1 -> 0 <= b1 -> 0 <= a2 -> 0 <= b2 -> 0 <= a3 -> 0 <= b3 -> 0 <= a4 -> 0 <= b4 ->
  0 <= a5 -> 0 <= b5 -> 0 <= a6 -> 0 <= b6 -> 0 <= a7 -> 0 <= b7 ->
  (0 <? Z.lor (Z.lor (Z.lor (Z.lxor a1 b1) (Z.lor (Z.lxor a2 b2) (Z.lxor a3 b3)))
                     (Z.lor (Z.lor (Z.lxor a4 b4) (Z.lxor a5 b5)) (Z.lxor a6 b6))) (Z.lxor a7 b7)) =
  negb ((a1 =? b1) && (a2 =? b2) && (a3 =? b3) && (a4 =? b4) && (a5 =? b5) && (a6 =? b6) && (a7 =? b7)).
Proof.
intros a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
assert (NN : 0 <= Z.lor (Z.lor (Z.lor (Z.lxor a1 b1) (Z.lor (Z.lxor a2 b2) (Z.lxor a3 b3)))
                     (Z.lor (Z.lor (Z.lxor a4 b4) (Z.lxor a5 b5)) (Z.lxor a6 b6))) (Z.lxor a7 b7))
  by (repeat first [apply lor_nn | apply lxor_nn]; lia).
apply Bool.eq_iff_eq_true. rewrite Z.ltb_lt, Bool.negb_true_iff, <- Bool.not_true_iff_false.
rewrite !andb_true_iff, !Z.eqb_eq. split.
- intros Hc ((((((E1 & E2) & E3) & E4) & E5) & E6) & E7). subst.
  rewrite !Z.lxor_nilpotent in Hc. rewrite !Z.lor_0_l in Hc. exact (Z.lt_irrefl 0 Hc).
- intros Hc. destruct (Z.eq_dec (Z.lor (Z.lor (Z.lor (Z.lxor a1 b1) (Z.lor (Z.lxor a2 b2) (Z.lxor a3 b3)))
                     (Z.lor (Z.lor (Z.lxor a4 b4) (Z.lxor a5 b5)) (Z.lxor a6 b6))) (Z.lxor a7 b7)) 0) as [Z0|Z0]; [|lia].
  exfalso. apply Hc. rewrite !Z.lor_eq_0_iff in Z0.
  destruct Z0 as (((Z1 & (Z2 & Z3)) & ((Z4 & Z5) & Z6)) & Z7).
  apply (proj1 (Z.lxor_eq_0_iff _ _)) in Z1, Z2, Z3, Z4, Z5, Z6, Z7. repeat split; assumption.
Qed.

Lemma o9_lor_u64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
intros a b Ha Hb. assert (H0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia). split; [exact H0|].
destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hne]; [lia|].
apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 64 ltac:(lia))). rewrite Z.log2_lor by lia.
apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|Ha0]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 a 64 ltac:(lia))). lia.
- destruct (Z.eq_dec b 0) as [->|Hb0]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 b 64 ltac:(lia))). lia.
Qed.
Lemma o9_lxor_u64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lxor a b < 2 ^ 64.
Proof.
intros a b Ha Hb. assert (H0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia). split; [exact H0|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hne]; [lia|].
apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 64 ltac:(lia))).
eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|Ha0]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 a 64 ltac:(lia))). lia.
- destruct (Z.eq_dec b 0) as [->|Hb0]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 b 64 ltac:(lia))). lia.
Qed.
Lemma o9_zc_rng : forall z, 0 <= zcanon z < 2 ^ 64.
Proof. intros z. unfold zcanon, M64. apply Z.mod_pos_bound. lia. Qed.
Lemma o9_zc_lor : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> zcanon (Z.lor a b) = Z.lor a b.
Proof. intros a b Ha Hb. apply zc_small. apply o9_lor_u64; assumption. Qed.
Lemma o9_zc_lxor : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> zcanon (Z.lxor a b) = Z.lxor a b.
Proof. intros a b Ha Hb. apply zc_small. apply o9_lxor_u64; assumption. Qed.
Lemma o9_zc_b : forall b : bool, zcanon (if b then 1 else 0) = Z.b2z b.
Proof. intros [|]; reflexivity. Qed.
Lemma o9_zc_b2z : forall b : bool, zcanon (Z.b2z b) = Z.b2z b.
Proof. intros [|]; reflexivity. Qed.
Lemma o9_lor_b2z : forall a b : bool, Z.lor (Z.b2z a) (Z.b2z b) = Z.b2z (a || b).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma o9_oldv : forall a v, 0 <= a -> oldv a v = v.
Proof. intros a v Ha. unfold oldv. replace (a <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma o9_uo : forall a v, 0 <= a -> 0 <= v < 2 ^ 64 -> u64 (oldv a v) = v.
Proof. intros a v Ha Hv. rewrite o9_oldv by exact Ha. unfold u64. apply Z.mod_small. exact Hv. Qed.
Lemma o9_w64z : forall x, Z_to_bv 64 x = Z_to_bv 64 (zcanon x).
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmod_mod. reflexivity.
Qed.
Ltac o9rng := first [ assumption | apply o9_zc_rng | apply o9_lxor_u64; o9rng | apply o9_lor_u64; o9rng ].
Lemma o9_diff_U : forall E a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 c d,
  ew E 550 = Z_to_bv 64 a1 -> ew E 563 = Z_to_bv 64 b1 ->
  ew E 557 = Z_to_bv 64 a2 -> ew E 564 = Z_to_bv 64 b2 ->
  ew E 555 = Z_to_bv 64 a3 -> ew E 565 = Z_to_bv 64 b3 ->
  ew E 558 = Z_to_bv 64 a4 -> ew E 566 = Z_to_bv 64 b4 ->
  ew E 552 = Z_to_bv 64 a5 -> ew E 568 = Z_to_bv 64 b5 ->
  ew E 554 = Z_to_bv 64 a6 -> ew E 567 = Z_to_bv 64 b6 ->
  ew E 572 = Z_to_bv 64 a7 -> ew E 570 = Z_to_bv 64 b7 ->
  ew E 569 = Z_to_bv 64 c -> ew E 575 = Z_to_bv 64 d ->
  0 <= a1 < 2 ^ 64 -> 0 <= b1 < 2 ^ 64 -> 0 <= a2 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
  0 <= a3 < 2 ^ 64 -> 0 <= b3 < 2 ^ 64 -> 0 <= a4 < 2 ^ 64 -> 0 <= b4 < 2 ^ 64 ->
  0 <= a5 < 2 ^ 64 -> 0 <= b5 < 2 ^ 64 -> 0 <= a6 < 2 ^ 64 -> 0 <= b6 < 2 ^ 64 ->
  0 <= a7 < 2 ^ 64 -> 0 <= b7 < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= d < 2 ^ 64 ->
  U E (SAlu ALU_OR
         (SAlu ALU_SLTU (SLit 0)
            (SAlu ALU_OR
               (SAlu ALU_OR
                  (SAlu ALU_OR (SAlu ALU_XOR (SOff 550 0) (SOff 563 0))
                     (SAlu ALU_OR (SAlu ALU_XOR (SOff 557 0) (SOff 564 0))
                        (SAlu ALU_XOR (SOff 555 0) (SOff 565 0))))
                  (SAlu ALU_OR
                     (SAlu ALU_OR (SAlu ALU_XOR (SOff 558 0) (SOff 566 0))
                        (SAlu ALU_XOR (SOff 552 0) (SOff 568 0)))
                     (SAlu ALU_XOR (SOff 554 0) (SOff 567 0))))
               (SAlu ALU_XOR (SOff 572 0) (SOff 570 0))))
         (SAlu ALU_SLTU (SOff 569 0) (SOff 575 0))) =
  Z.b2z (negb ((a1 =? b1) && (a2 =? b2) && (a3 =? b3) && (a4 =? b4) && (a5 =? b5) && (a6 =? b6) && (a7 =? b7)) || (c <? d)).
Proof.
intros E a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 c d E1 F1 E2 F2 E3 F3 E4 F4 E5 F5 E6 F6 E7 F7 Ec Ed
  A1 B1 A2 B2 A3 B3 A4 B4 A5 B5 A6 B6 A7 B7 Rc Rd.
rewrite !U_SAlu, U_SLit.
rewrite (UA0 E 550 a1 E1), (UA0 E 563 b1 F1), (UA0 E 557 a2 E2), (UA0 E 564 b2 F2), (UA0 E 555 a3 E3), (UA0 E 565 b3 F3),
  (UA0 E 558 a4 E4), (UA0 E 566 b4 F4), (UA0 E 552 a5 E5), (UA0 E 568 b5 F5), (UA0 E 554 a6 E6), (UA0 E 567 b6 F6),
  (UA0 E 572 a7 E7), (UA0 E 570 b7 F7), (UA0 E 569 c Ec), (UA0 E 575 d Ed).
rewrite (zc_small a1 A1), (zc_small b1 B1), (zc_small a2 A2), (zc_small b2 B2), (zc_small a3 A3), (zc_small b3 B3),
  (zc_small a4 A4), (zc_small b4 B4), (zc_small a5 A5), (zc_small b5 B5), (zc_small a6 A6), (zc_small b6 B6),
  (zc_small a7 A7), (zc_small b7 B7), (zc_small c Rc), (zc_small d Rd).
change (zcanon 0) with 0. cbn [zalu_raw].
repeat first [ rewrite o9_zc_lxor by o9rng | rewrite o9_zc_lor by o9rng ].
rewrite !o9_zc_b. rewrite o9_lor_b2z, ?o9_zc_b2z.
rewrite big_diff_eq by lia. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Let DSEAT := d_seat B MT XM_LIB RLO RHI tfib_K.
Let DFACTS := d_facts_ok B MT XM_LIB RLO RHI tfib_K.
Let DLAND := d_land B MT XM_LIB RLO RHI tfib_K.
Let DBRT := d_body_rt B.
Let DBCK := d_body_call_keep B MT XM_LIB RLO RHI tfib_K.
Let DBTOBS := d_body_tobs B MT XM_LIB RLO RHI tfib_K.
Let DBREAD := d_body_read B.
Lemma ew_dx : forall cx E (regs : bvmap 5 word) (xv : list word) j, (j < length xv)%nat ->
  ew (d_env cx E (obs_vals regs ++ xv)) (AT_X + 32 + j) = nth j xv (Z_to_bv 64 0).
Proof.
intros cx E regs xv j Hj. unfold d_env, havoc. cbn [ew].
replace (AT_X + 32 + j <? AT_FL)%nat with false by (symmetry; apply Nat.ltb_ge; unfold AT_X, AT_FL; lia).
replace (AT_X + 32 + j - AT_FL)%nat with (S (32 + j)) by (unfold AT_X, AT_FL; lia). cbn [nth].
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
rewrite app_nth2 by lia. rewrite L. replace (32 + j - 32)%nat with j by lia. apply nth_indep. exact Hj.
Qed.
Lemma ew_dr : forall cx E (regs : bvmap 5 word) (xv : list word) (r : nat), (r < 32)%nat ->
  ew (d_env cx E (obs_vals regs ++ xv)) (AT_X + r) = getr regs (Z_to_bv 5 (Z.of_nat r)).
Proof.
intros cx E regs xv r Hr. unfold d_env, havoc. cbn [ew].
replace (AT_X + r <? AT_FL)%nat with false by (symmetry; apply Nat.ltb_ge; unfold AT_X, AT_FL; lia).
replace (AT_X + r - AT_FL)%nat with (S r) by (unfold AT_X, AT_FL; lia). cbn [nth].
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
rewrite app_nth1 by lia. unfold obs_vals.
rewrite (nth_indep _ _ (getr regs (Z_to_bv 5 (Z.of_nat 0)))) by (rewrite length_map, length_seq; exact Hr).
rewrite (map_nth (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0)))). rewrite seq_nth by exact Hr. reflexivity.
Qed.
Lemma chunk_okW : forall E (m : word -> option byte) base off (w : N) a v,
  ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS m (base + off) (N.to_nat w) v ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w (SOff a 0))).
Proof.
intros E m base off w a v Ha Hv Hw H. apply (chunk_ok_val SEGS E m base off w (SOff a 0) v); [| exact Hv | exact Hw | exact H].
cbn [sv_denot]. rewrite Ha, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma chunk_ok8 : forall E (m : word -> option byte) base off a v,
  ew E a = Z_to_bv 64 v -> val_mem SEGS m (base + off) 8 v ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 (SOff a 0))).
Proof.
intros E m base off a v Ha H. apply (chunk_okW E m base off 8 a (v mod 2 ^ 64)).
- rewrite Ha. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity.
- change (8 * Z.of_N 8) with 64. apply Z.mod_pos_bound. lia.
- lia.
- intros j Hj. rewrite (H j Hj). f_equal. f_equal. unfold YO0f.le_byte. change (8 * Z.of_nat (N.to_nat 8)) with 64. change (8 * Z.of_nat 8) with 64. rewrite Zmod_mod. reflexivity.
Qed.
Lemma garr8_u : forall (m : word -> option byte) p (L : list byte) k n, 0 <= k -> (Z.to_nat k + n <= length L)%nat ->
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> val_mem SEGS m (p + k) n (u_at L k n).
Proof.
intros m p L k n Hk Hl G j Hj.
assert (Hsub : length (sub L k n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
destruct (nth_error L (Z.to_nat k + j)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (garr8_mbyte SEGS m p _ (Z.to_nat k + j) G) by (rewrite length_map; lia).
f_equal. rewrite (nth_error_nth (map (fun b0 : byte => bv_unsigned b0) L) _ 0 (map_nth_error _ _ _ Hb)).
assert (Hs : nth_error (sub L k n) j = Some b).
{ unfold sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec j n); [|lia]. rewrite nth_error_skipn. exact Hb. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hs) as Hv.
pose proof (bytes_le_to_Z_bound (sub L k n)) as Hb1. pose proof (bytes_le_to_Z_nonneg (sub L k n)) as Hb0. rewrite Hsub in Hb1.
unfold u_at. rewrite le_byte_small by (split; [exact Hb0 | exact Hb1] || lia).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. rewrite Hv. rewrite Z.mod_mod by lia. reflexivity.
Qed.

#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation oc := (oc B).
#[local] Notation ob_c11 := (ob_c11 B MT XM_LIB RLO RHI tfib_K).

Definition xb (j : nat) : sv := SOff (AT_X + 32 + j) 0.
Definition sr11_x (ai : Z) (r : nat) : sv :=
  match r with 22%nat => SOff AT_F (2160 + 48 * ai) | 10%nat => SLit 0 | _ => sr_x r end.
Definition sr11 (ai : Z) : list sv := map (sr11_x ai) (seq 0 32).
Definition acs11 : list YP09.chunk :=
  [YP09.mkChunk 392 (CVal 8 (xb 0)); YP09.mkChunk 136 (CVal 8 (xb 1)); YP09.mkChunk 128 (CVal 8 (xb 2));
   YP09.mkChunk 120 (CVal 8 (xb 3)); YP09.mkChunk 112 (CVal 8 (xb 4)); YP09.mkChunk 104 (CVal 8 (xb 5));
   YP09.mkChunk 224 (CVal 8 (xb 6)); YP09.mkChunk 96 (CVal 8 (xb 7)); YP09.mkChunk 72 (CVal 8 (xb 8));
   YP09.mkChunk 88 (CVal 8 (xb 9)); YP09.mkChunk 408 (CVal 8 (xb 10)); YP09.mkChunk 64 (CVal 8 (xb 11));
   YP09.mkChunk 56 (CVal 8 (xb 12)); YP09.mkChunk 368 (CVal 8 (xb 13)); YP09.mkChunk 344 (CVal 8 (xb 14));
   YP09.mkChunk 248 (CVal 8 (xb 15)); YP09.mkChunk 336 (CVal 8 (xb 16)); YP09.mkChunk 280 (CVal 8 (xb 17))].
Definition fcs11 (ai : Z) : list YP09.chunk :=
  [YP09.mkChunk (2168 + 48 * ai) (CVal 4 (xb 18)); YP09.mkChunk (2172 + 48 * ai) (CVal 1 (xb 19));
   YP09.mkChunk (2173 + 48 * ai) (CVal 1 (xb 20)); YP09.mkChunk (2174 + 48 * ai) (CVal 1 (xb 21));
   YP09.mkChunk (2176 + 48 * ai) (CVal 1 (xb 22)); YP09.mkChunk (2175 + 48 * ai) (CVal 1 (xb 23));
   YP09.mkChunk (2180 + 48 * ai) (CVal 4 (xb 24)); YP09.mkChunk (2184 + 48 * ai) (CVal 4 (xb 25));
   YP09.mkChunk (2192 + 48 * ai) (CVal 8 (xb 26)); YP09.mkChunk (2200 + 48 * ai) (CVal 8 (xb 27))].

Lemma regs_ok11 : forall cx E regs xv ai, d_E cx E -> d_rL B cx regs ->
  getr regs 10 = w64 0 -> getr regs 22 = w64 (d_obj cx OT + 48 * ai) ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx -> 0 <= ai < 8 -> d_FB cx + 2560 < 2 ^ 64 ->
  regs_ok (d_env cx E (obs_vals regs ++ xv)) (sr11 ai) regs.
Proof.
intros cx E regs xv ai HE HL H10 H22 HA HF0 Hai HF1.
destruct HE as (HER & H32 & _ & HA60 & HF516 & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_F with 516%nat in HF516.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (change (sr_get (sr11 ai) 22%bv) with (SOff 516 (2160 + 48 * ai))).
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end).
all: cbn [sv_denot].
all: try first
  [ rewrite getr_zero; reflexivity
  | rewrite H10; reflexivity
  | unfold d_env; rewrite ew_havoc_old by (cbv; lia); rewrite HF516, H22; unfold w64, d_obj, dobj_off;
    rewrite unsigned_lit_small by lia; f_equal; lia
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew _ ?nn)) =>
      let k := eval vm_compute in (nn - AT_X)%nat in change nn with (AT_X + k)%nat;
      rewrite (ew_dr cx E rg xv k ltac:(lia)), Z_to_bv_bv_unsigned; f_equal; try (apply bv_eq; reflexivity) end ].
Qed.


Lemma fch11 : forall E (m : word -> option byte) fb (L : list byte) off k (w : N) a,
  ew E a = Z_to_bv 64 (u_at L k (N.to_nat w)) -> 0 <= k -> (Z.to_nat k + N.to_nat w <= length L)%nat -> Z.of_N w <= 8 ->
  off = 2160 + k -> garr8 SEGS m (fb + 2160) (map (fun b : byte => bv_unsigned b) L) ->
  YP09.chunk_ok SEGS E m fb (YP09.mkChunk off (CVal w (SOff a 0))).
Proof.
intros E m fb L off k w a Ha Hk Hl Hw -> G.
apply (chunk_okW E m fb (2160 + k) w a (u_at L k (N.to_nat w))); [exact Ha | | exact Hw |].
- pose proof (u_at_range L k (N.to_nat w) Hl) as R. rewrite N_nat_Z in R. exact R.
- replace (fb + (2160 + k)) with (fb + 2160 + k) by lia. rewrite <- (N_nat_Z w) in *. apply garr8_u; [exact Hk | exact Hl | exact G].
Qed.

Definition xv11 (cx : dcx) (T T' Sg : list byte) (ai ow ret nb now len fr : Z) : list word :=
  map (Z_to_bv 64)
  [u64 (oldv ai (role_of_e T ai)); u64 (oldv ai (hd_of T ai)); u64 (oldv ai (din_of T ai));
   u64 (oldv ai (dout_of T ai)); u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai));
   u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai)); u64 (oldv ai (s32_at T (48 * ai + 20)));
   u64 (oldv ai (owned_of T ai)); u64 (oldv ai (u_at T (48 * ai + 32) 8)); (if ow =? 0 then owned_of T ai else 1); ret;
   bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg else reac_disco_table_observe_c.ch_of T ai);
   bv_swrap 32 (s_ch Sg); nb; now; d_cur cx nb; len; fr;
   u_at T' (48 * ai + 8) 4; u_at T' (48 * ai + 12) 1; u_at T' (48 * ai + 13) 1; u_at T' (48 * ai + 14) 1;
   u_at T' (48 * ai + 16) 1; u_at T' (48 * ai + 15) 1; u_at T' (48 * ai + 20) 4; u_at T' (48 * ai + 24) 4;
   u_at T' (48 * ai + 32) 8; u_at T' (48 * ai + 40) 8].

Lemma ob_seat11 : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  oc cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 ->
  ob_sp24 cx T Sg ai ow ret W mem3 -> ob_r24 cx T Sg ai ow regs -> 0 <= ai < 8 ->
  regions_wf (d_kregions dsh_rec acs11 (fcs11 ai) ++ []) = true ->
  exists E, d_E cx E /\
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (obs_vals regs ++ xv11 cx T T' Sg ai ow ret nb now len fr))
    (ss_d 0x1990 (sr11 ai) dsh_rec acs11 (fcs11 ai) [] (d_facts [] []))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + 0x1990)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k Hc3 HOC Hsp24 Hr24 Hai Hwf.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl' & HT' & HTok' & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcanb & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
destruct Hsp24 as (V392 & V136 & V128 & V120 & V112 & V104 & V224 & V96 & V72 & V88 & V408 & V64 & V56).
destruct Hr24 as (R10 & R19 & R21 & R22 & R23 & R24 & R26 & R27).
set (xv := xv11 cx T T' Sg ai ow ret nb now len fr).
assert (Lxv : length xv = 28%nat) by reflexivity.
assert (EX : forall j, (j < 28)%nat -> ew (d_env cx E (obs_vals regs ++ xv)) (AT_X + 32 + j) = nth j xv (Z_to_bv 64 0))
  by (intros j Hj; apply ew_dx; rewrite Lxv; exact Hj).
exists E. split; [exact HdE|].
apply (DSEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0x1990 (sr11 ai) (obs_vals regs ++ xv) acs11 (fcs11 ai) []
  (d_facts [] []) Hc3 HdE Hregs Hflag).
- apply (regs_ok11 cx E regs xv ai HdE HrL R10 R22); unfold LLVMF_STK in *; lia.
- exact (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (obs_vals regs ++ xv) [] [] Hc3 HdE I I).
- unfold acs11.
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 0%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V392) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 1%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V136) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 2%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V128) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 3%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V120) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 4%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V112) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 5%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V104) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 6%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V224) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 7%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V96) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 8%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V72) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 9%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V88) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 10%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V408) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 11%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V64) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 12%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) V56) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 13%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) H368) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 14%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) (proj2 Hsp0)) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 15%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) H248) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 16%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) H336) |].
  apply Forall_cons; [exact (chunk_ok8 _ _ _ _ _ _ ltac:(transitivity (nth 17%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity]) H280) |].
  apply Forall_nil.
- unfold fcs11. assert (HT2 : garr8 SEGS (rd W mem3) (d_FB cx + 2160) (map (fun b : byte => bv_unsigned b) T')) by exact HT'.
  apply Forall_cons; [apply (fch11 _ _ _ T' _ (48 * ai + 8) 4); [transitivity (nth 18%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity] | lia | rewrite HTl'; lia | lia | lia | exact HT2] |].
  apply Forall_cons; [apply (fch11 _ _ _ T' _ (48 * ai + 12) 1); [transitivity (nth 19%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity] | lia | rewrite HTl'; lia | lia | lia | exact HT2] |].
  apply Forall_cons; [apply (fch11 _ _ _ T' _ (48 * ai + 13) 1); [transitivity (nth 20%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity] | lia | rewrite HTl'; lia | lia | lia | exact HT2] |].
  apply Forall_cons; [apply (fch11 _ _ _ T' _ (48 * ai + 14) 1); [transitivity (nth 21%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity] | lia | rewrite HTl'; lia | lia | lia | exact HT2] |].
  apply Forall_cons; [apply (fch11 _ _ _ T' _ (48 * ai + 16) 1); [transitivity (nth 22%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity] | lia | rewrite HTl'; lia | lia | lia | exact HT2] |].
  apply Forall_cons; [apply (fch11 _ _ _ T' _ (48 * ai + 15) 1); [transitivity (nth 23%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity] | lia | rewrite HTl'; lia | lia | lia | exact HT2] |].
  apply Forall_cons; [apply (fch11 _ _ _ T' _ (48 * ai + 20) 4); [transitivity (nth 24%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity] | lia | rewrite HTl'; lia | lia | lia | exact HT2] |].
  apply Forall_cons; [apply (fch11 _ _ _ T' _ (48 * ai + 24) 4); [transitivity (nth 25%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity] | lia | rewrite HTl'; lia | lia | lia | exact HT2] |].
  apply Forall_cons; [apply (fch11 _ _ _ T' _ (48 * ai + 32) 8); [transitivity (nth 26%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity] | lia | rewrite HTl'; lia | lia | lia | exact HT2] |].
  apply Forall_cons; [apply (fch11 _ _ _ T' _ (48 * ai + 40) 8); [transitivity (nth 27%nat xv (Z_to_bv 64 0)); [apply EX; lia | reflexivity] | lia | rewrite HTl'; lia | lia | lia | exact HT2] |].
  apply Forall_nil.
- apply Forall_nil.
- exact I.
- apply Forall_nil.
- exact Hwf.
Qed.

Ltac o9_refute :=
  exfalso;
  lazymatch goal with Hc : branch_taken BC_NE (sv_denot ?Ex ?A) (sv_denot _ _) = true |- _ =>
    rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc; apply Hc; clear Hc;
    lazymatch A with
    | SExt true 32 (SOff 581 0) =>
        lazymatch goal with EW581 : ew _ 581 = _, EW550 : ew _ 550 = _, BR : 0 <= u_at _ (48 * _ + 8) 4 < _,
          HF : bv_swrap 32 (u_at _ (48 * _ + 8) 4) = _ |- _ =>
          rewrite (UA32 Ex 581 _ EW581 BR), (UA0 Ex 550 _ EW550), HF; reflexivity end
    | SExt false 8 (SOff 582 0) =>
        lazymatch goal with EW : ew _ 582 = _, EWr : ew _ 557 = _, BR : 0 <= u_at _ (48 * _ + 12) 1 < _,
          HF : u_at _ (48 * _ + 12) 1 = _ |- _ =>
          rewrite (UA8 Ex 582 _ EW BR), (UA0 Ex 557 _ EWr), HF; symmetry; apply zc_small; assumption end
    | SExt false 8 (SOff 583 0) =>
        lazymatch goal with EW : ew _ 583 = _, EWr : ew _ 555 = _, BR : 0 <= u_at _ (48 * _ + 13) 1 < _,
          HF : u_at _ (48 * _ + 13) 1 = _ |- _ =>
          rewrite (UA8 Ex 583 _ EW BR), (UA0 Ex 555 _ EWr), HF; symmetry; apply zc_small; assumption end
    | SExt false 8 (SOff 584 0) =>
        lazymatch goal with EW : ew _ 584 = _, EWr : ew _ 558 = _, BR : 0 <= u_at _ (48 * _ + 14) 1 < _,
          HF : u_at _ (48 * _ + 14) 1 = _ |- _ =>
          rewrite (UA8 Ex 584 _ EW BR), (UA0 Ex 558 _ EWr), HF; symmetry; apply zc_small; assumption end
    | SExt false 8 (SOff 585 0) =>
        lazymatch goal with EW : ew _ 585 = _, EWr : ew _ 552 = _, BR : 0 <= u_at _ (48 * _ + 16) 1 < _,
          HF : u_at _ (48 * _ + 16) 1 = _ |- _ =>
          rewrite (UA8 Ex 585 _ EW BR), (UA0 Ex 552 _ EWr), HF; symmetry; apply zc_small; assumption end
    | SExt false 8 (SOff 586 0) =>
        lazymatch goal with EW : ew _ 586 = _, EWr : ew _ 554 = _, BR : 0 <= u_at _ (48 * _ + 15) 1 < _,
          HF : u_at _ (48 * _ + 15) 1 = _ |- _ =>
          rewrite (UA8 Ex 586 _ EW BR), (UA0 Ex 554 _ EWr), HF; symmetry; apply zc_small; assumption end
    | SExt true 32 (SOff 587 0) =>
        lazymatch goal with EW : ew _ 587 = _, EWr : ew _ 574 = _, BR : 0 <= u_at _ (48 * _ + 20) 4 < _,
          HF : bv_swrap 32 (u_at _ (48 * _ + 20) 4) = _ |- _ =>
          rewrite (UA32 Ex 587 _ EW BR), (UA0 Ex 574 _ EWr), HF; reflexivity end
    | SExt true 32 (SOff 588 0) =>
        lazymatch goal with EW : ew _ 588 = _, EWr : ew _ 572 = _, BR : 0 <= u_at _ (48 * _ + 24) 4 < _,
          HF : bv_swrap 32 (u_at _ (48 * _ + 24) 4) = _ |- _ =>
          rewrite (UA32 Ex 588 _ EW BR), (UA0 Ex 572 _ EWr), HF; reflexivity end
    | SOff 589 0 =>
        lazymatch goal with EW : ew _ 589 = _, EWr : ew _ 571 = _, HF : u_at _ (48 * _ + 32) 8 = _ |- _ =>
          rewrite (UA0 Ex 589 _ EW), (UA0 Ex 571 _ EWr), HF; reflexivity end
    | SOff 590 0 =>
        lazymatch goal with EW : ew _ 590 = _, EWr : ew _ 577 = _, HF : u_at _ (48 * _ + 40) 8 = _ |- _ =>
          rewrite (UA0 Ex 590 _ EW), (UA0 Ex 577 _ EWr), HF; unfold zcanon, M64; apply Zmod_mod end
    | SOff 573 0 =>
        lazymatch goal with EW : ew _ 573 = _, DF : U _ (SAlu ALU_OR _ _) = _ |- _ =>
          rewrite (UA0 Ex 573 _ EW), DF; reflexivity end
    end end.
Ltac o9_go RUNTO BR :=
  o4_runto RUNTO 6984;
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    let p := eval vm_compute in (ss_pc ss) in
    lazymatch p with
    | 6984 => idtac
    | _ => psrr_branch_tok RUNTO BR HS SHOK OBspan;
      [ o9_refute
      | lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end; o9_go RUNTO BR ]
    end end.
Ltac o9x XV j := etransitivity; [exact (XV j ltac:(lia)) |];
  lazymatch goal with x := xv11 _ _ _ _ _ _ _ _ _ _ _ |- _ => unfold x end; unfold xv11; cbn [nth map].

Theorem ob_s9b : ob_seg9b B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & HTl0 & HTok0 & Hfind & Hain & How & HOM & Hsp24 & Hr24).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (_ & _ & _ & HF0 & HF1 & _ & _ & HF32 & _ & _ & _).
pose proof alloc_ceiling_val as HAC.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof HTok0 as (Ht1 & Ht2 & Ht3 & Ht4). unfold tbl_T1 in Ht1.
assert (Hai8 : 0 <= ai < 8) by lia.
destruct (sight_S12 Sg) as (HSs1 & HSs2); [pose proof HSf as (_ & _ & _ & _ & _ & Hok & _); exact Hok|].
destruct (obs_fields T Sg ow now T' ret ai HTl0 HSgl Hain ltac:(lia) ltac:(lia) ltac:(lia) Ht2 Ht4 HSs1 HSs2 Hfind HOM)
  as (_ & _ & _ & HFrole & HFhd & HFdin & HFdout & HFfam & HFslots & HFch & HFown & HFfs & HFlast & HFret).
assert (Hwf : regions_wf (d_kregions dsh_rec acs11 (fcs11 ai) ++ []) = true).
{ assert (Hc : ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity. }
destruct (ob_seat11 fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k HctxD HOC Hsp24 Hr24 Hai8 Hwf)
  as (E & HdE & HS).
destruct Hr24 as (R10 & R19 & R21 & R22 & R23 & R24 & R26 & R27).
pose proof (Ht2 ai Hain) as HR2.
destruct (Ht4 ai Hain) as (BThd & _ & BTown).
assert (BR8 : 0 <= u_at T' (48 * ai + 8) 4 < 2 ^ 32) by (apply u_at_r4; rewrite HTl; lia).
assert (BR12 : 0 <= u_at T' (48 * ai + 12) 1 < 256) by (apply u_at_r1; rewrite HTl; lia).
assert (BR13 : 0 <= u_at T' (48 * ai + 13) 1 < 256) by (apply u_at_r1; rewrite HTl; lia).
assert (BR14 : 0 <= u_at T' (48 * ai + 14) 1 < 256) by (apply u_at_r1; rewrite HTl; lia).
assert (BR16 : 0 <= u_at T' (48 * ai + 16) 1 < 256) by (apply u_at_r1; rewrite HTl; lia).
assert (BR15 : 0 <= u_at T' (48 * ai + 15) 1 < 256) by (apply u_at_r1; rewrite HTl; lia).
assert (BR20 : 0 <= u_at T' (48 * ai + 20) 4 < 2 ^ 32) by (apply u_at_r4; rewrite HTl; lia).
assert (BR24 : 0 <= u_at T' (48 * ai + 24) 4 < 2 ^ 32) by (apply u_at_r4; rewrite HTl; lia).
assert (BT32 : 0 <= u_at T (48 * ai + 32) 8 < 2 ^ 64) by (apply u_at_r8; rewrite HTl0; lia).
assert (BTdin : 0 <= din_of T ai < 256) by (unfold din_of; apply u_at_r1; rewrite HTl0; lia).
assert (BTdout : 0 <= dout_of T ai < 256) by (unfold dout_of; apply u_at_r1; rewrite HTl0; lia).
assert (BTsl : 0 <= reac_disco_table_observe_c.slots_of T ai < 256)
  by (unfold reac_disco_table_observe_c.slots_of; apply u_at_r1; rewrite HTl0; lia).
assert (BTfam : 0 <= reac_disco_table_observe_c.fam_of T ai < 256)
  by (unfold reac_disco_table_observe_c.fam_of; apply u_at_r1; rewrite HTl0; lia).
assert (BTch : 0 <= reac_disco_table_observe_c.ch_of T ai < 2 ^ 32)
  by (unfold reac_disco_table_observe_c.ch_of; apply u_at_r4; rewrite HTl0; lia).
assert (BGdin : 0 <= s_din Sg < 256) by (unfold s_din; apply u_at_r1; rewrite HSgl; cbn; lia).
assert (BGdout : 0 <= s_dout Sg < 256) by (unfold s_dout; apply u_at_r1; rewrite HSgl; cbn; lia).
assert (BGsl : 0 <= s_slots Sg < 256) by (unfold s_slots; apply u_at_r1; rewrite HSgl; cbn; lia).
assert (BGfam : 0 <= s_fam Sg < 256) by (unfold s_fam; apply u_at_r1; rewrite HSgl; cbn; lia).
assert (BGch : 0 <= s_ch Sg < 2 ^ 32) by (unfold s_ch; apply u_at_r4; rewrite HSgl; cbn; lia).
assert (Ra1 : 0 <= slot_known.want_role (s_role Sg) (role_of_e T ai) < 2 ^ 64).
{ unfold slot_known.want_role. destruct HSs1 as [E1|[E1|E1]]; rewrite E1; destruct HR2 as [E2|[E2|E2]]; rewrite E2; cbn; lia. }
assert (Rb1 : 0 <= role_of_e T ai < 2 ^ 64) by lia.
assert (Ra2 : 0 <= (if s_hd Sg =? 0 then hd_of T ai else 1) < 2 ^ 64) by (destruct (s_hd Sg =? 0); lia).
assert (Rb2 : 0 <= hd_of T ai < 2 ^ 64) by lia.
assert (Ra3 : 0 <= (if s_hd Sg =? 0 then din_of T ai else s_din Sg) < 2 ^ 64) by (destruct (s_hd Sg =? 0); lia).
assert (Rb3 : 0 <= din_of T ai < 2 ^ 64) by lia.
assert (Ra4 : 0 <= (if s_hd Sg =? 0 then dout_of T ai else s_dout Sg) < 2 ^ 64) by (destruct (s_hd Sg =? 0); lia).
assert (Rb4 : 0 <= dout_of T ai < 2 ^ 64) by lia.
assert (Ra5 : 0 <= (if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg) < 2 ^ 64)
  by (destruct (s_slots Sg =? 0); lia).
assert (Rb5 : 0 <= reac_disco_table_observe_c.slots_of T ai < 2 ^ 64) by lia.
assert (Ra6 : 0 <= (if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg) < 2 ^ 64)
  by (destruct (s_fam Sg =? 0); lia).
assert (Rb6 : 0 <= reac_disco_table_observe_c.fam_of T ai < 2 ^ 64) by lia.
assert (Ra7 : 0 <= (if ow =? 0 then owned_of T ai else 1) < 2 ^ 64) by (destruct (ow =? 0); lia).
assert (Rb7 : 0 <= owned_of T ai < 2 ^ 64) by lia.
set (xv := xv11 cx T T' Sg ai ow ret nb now len fr) in HS.
set (Es := d_env cx E (obs_vals regs ++ xv)) in HS.
assert (XV : forall j, (j < 28)%nat -> ew Es (AT_X + 32 + j) = nth j xv (Z_to_bv 64 0))
  by (intros j Hj; apply ew_dx; exact Hj).
assert (EW563 : ew Es 563 = Z_to_bv 64 (role_of_e T ai)) by (o9x XV 0%nat; rewrite o9_uo by lia; reflexivity).
assert (EW564 : ew Es 564 = Z_to_bv 64 (hd_of T ai)) by (o9x XV 1%nat; rewrite o9_uo by lia; reflexivity).
assert (EW565 : ew Es 565 = Z_to_bv 64 (din_of T ai)) by (o9x XV 2%nat; rewrite o9_uo by lia; reflexivity).
assert (EW566 : ew Es 566 = Z_to_bv 64 (dout_of T ai)) by (o9x XV 3%nat; rewrite o9_uo by lia; reflexivity).
assert (EW567 : ew Es 567 = Z_to_bv 64 (reac_disco_table_observe_c.fam_of T ai)) by (o9x XV 4%nat; rewrite o9_uo by lia; reflexivity).
assert (EW568 : ew Es 568 = Z_to_bv 64 (reac_disco_table_observe_c.slots_of T ai)) by (o9x XV 5%nat; rewrite o9_uo by lia; reflexivity).
assert (EW569 : ew Es 569 = Z_to_bv 64 (zcanon (bv_swrap 32 (reac_disco_table_observe_c.ch_of T ai))))
  by (o9x XV 6%nat; rewrite o9_oldv by lia; reflexivity).
assert (EW570 : ew Es 570 = Z_to_bv 64 (owned_of T ai)) by (o9x XV 7%nat; rewrite o9_uo by lia; reflexivity).
assert (EW571 : ew Es 571 = Z_to_bv 64 (u_at T (48 * ai + 32) 8)) by (o9x XV 8%nat; rewrite o9_uo by lia; reflexivity).
assert (EW572 : ew Es 572 = Z_to_bv 64 (if ow =? 0 then owned_of T ai else 1)) by (o9x XV 9%nat; reflexivity).
assert (EW573 : ew Es 573 = Z_to_bv 64 ret) by (o9x XV 10%nat; reflexivity).
assert (EW574 : ew Es 574 = Z_to_bv 64 (bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg
  else reac_disco_table_observe_c.ch_of T ai))) by (o9x XV 11%nat; reflexivity).
assert (EW575 : ew Es 575 = Z_to_bv 64 (zcanon (bv_swrap 32 (s_ch Sg)))) by (o9x XV 12%nat; apply o9_w64z).
assert (EW576 : ew Es 576 = Z_to_bv 64 nb) by (o9x XV 13%nat; reflexivity).
assert (EW577 : ew Es 577 = Z_to_bv 64 now) by (o9x XV 14%nat; reflexivity).
assert (EW578 : ew Es 578 = Z_to_bv 64 (d_cur cx nb)) by (o9x XV 15%nat; reflexivity).
assert (EW579 : ew Es 579 = Z_to_bv 64 len) by (o9x XV 16%nat; reflexivity).
assert (EW580 : ew Es 580 = Z_to_bv 64 fr) by (o9x XV 17%nat; reflexivity).
assert (EW581 : ew Es 581 = Z_to_bv 64 (u_at T' (48 * ai + 8) 4)) by (o9x XV 18%nat; reflexivity).
assert (EW582 : ew Es 582 = Z_to_bv 64 (u_at T' (48 * ai + 12) 1)) by (o9x XV 19%nat; reflexivity).
assert (EW583 : ew Es 583 = Z_to_bv 64 (u_at T' (48 * ai + 13) 1)) by (o9x XV 20%nat; reflexivity).
assert (EW584 : ew Es 584 = Z_to_bv 64 (u_at T' (48 * ai + 14) 1)) by (o9x XV 21%nat; reflexivity).
assert (EW585 : ew Es 585 = Z_to_bv 64 (u_at T' (48 * ai + 16) 1)) by (o9x XV 22%nat; reflexivity).
assert (EW586 : ew Es 586 = Z_to_bv 64 (u_at T' (48 * ai + 15) 1)) by (o9x XV 23%nat; reflexivity).
assert (EW587 : ew Es 587 = Z_to_bv 64 (u_at T' (48 * ai + 20) 4)) by (o9x XV 24%nat; reflexivity).
assert (EW588 : ew Es 588 = Z_to_bv 64 (u_at T' (48 * ai + 24) 4)) by (o9x XV 25%nat; reflexivity).
assert (EW589 : ew Es 589 = Z_to_bv 64 (u_at T' (48 * ai + 32) 8)) by (o9x XV 26%nat; reflexivity).
assert (EW590 : ew Es 590 = Z_to_bv 64 (u_at T' (48 * ai + 40) 8)) by (o9x XV 27%nat; reflexivity).
assert (EW550 : ew Es 550 = Z_to_bv 64 (slot_known.want_role (s_role Sg) (role_of_e T ai)))
  by exact (eq_trans (ew_dr cx E regs xv 19 ltac:(lia)) R19).
assert (EW557 : ew Es 557 = Z_to_bv 64 (if s_hd Sg =? 0 then hd_of T ai else 1))
  by exact (eq_trans (ew_dr cx E regs xv 26 ltac:(lia)) R26).
assert (EW555 : ew Es 555 = Z_to_bv 64 (if s_hd Sg =? 0 then din_of T ai else s_din Sg))
  by exact (eq_trans (ew_dr cx E regs xv 24 ltac:(lia)) R24).
assert (EW558 : ew Es 558 = Z_to_bv 64 (if s_hd Sg =? 0 then dout_of T ai else s_dout Sg))
  by exact (eq_trans (ew_dr cx E regs xv 27 ltac:(lia)) R27).
assert (EW552 : ew Es 552 = Z_to_bv 64 (if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg))
  by exact (eq_trans (ew_dr cx E regs xv 21 ltac:(lia)) R21).
assert (EW554 : ew Es 554 = Z_to_bv 64 (if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg))
  by exact (eq_trans (ew_dr cx E regs xv 23 ltac:(lia)) R23).
assert (EW516 : ew Es 516 = Z_to_bv 64 (d_FB cx)).
{ unfold Es. rewrite d_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & _ & EF & _). exact EF. }
assert (DF : U Es (SAlu ALU_OR
         (SAlu ALU_SLTU (SLit 0)
            (SAlu ALU_OR
               (SAlu ALU_OR
                  (SAlu ALU_OR (SAlu ALU_XOR (SOff 550 0) (SOff 563 0))
                     (SAlu ALU_OR (SAlu ALU_XOR (SOff 557 0) (SOff 564 0))
                        (SAlu ALU_XOR (SOff 555 0) (SOff 565 0))))
                  (SAlu ALU_OR
                     (SAlu ALU_OR (SAlu ALU_XOR (SOff 558 0) (SOff 566 0))
                        (SAlu ALU_XOR (SOff 552 0) (SOff 568 0)))
                     (SAlu ALU_XOR (SOff 554 0) (SOff 567 0))))
               (SAlu ALU_XOR (SOff 572 0) (SOff 570 0))))
         (SAlu ALU_SLTU (SOff 569 0) (SOff 575 0))) = zcanon ret).
{ rewrite (o9_diff_U Es _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EW550 EW563 EW557 EW564 EW555 EW565 EW558 EW566 EW552 EW568
    EW554 EW567 EW572 EW570 EW569 EW575 Ra1 Rb1 Ra2 Rb2 Ra3 Rb3 Ra4 Rb4 Ra5 Rb5 Ra6 Rb6 Ra7 Rb7 (o9_zc_rng _) (o9_zc_rng _)).
  rewrite zltu_sw by assumption.
  rewrite HFret. unfold slot_observe.c_any.
  rewrite <- (slot_known.fr_role T Sg ai HSs1 HR2), <- (slot_known.fr_decl T Sg ai HSs2 BThd), <- (slot_known.fr_slots T Sg ai),
    <- (slot_known.fr_fam T Sg ai), <- (slot_known.fr_own T ow ai ltac:(lia) BTown).
  unfold slot_observe.c_ch.
  destruct (slot_known.want_role (s_role Sg) (role_of_e T ai) =? role_of_e T ai),
    ((if s_hd Sg =? 0 then hd_of T ai else 1) =? hd_of T ai),
    ((if s_hd Sg =? 0 then din_of T ai else s_din Sg) =? din_of T ai),
    ((if s_hd Sg =? 0 then dout_of T ai else s_dout Sg) =? dout_of T ai),
    ((if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg) =? reac_disco_table_observe_c.slots_of T ai),
    ((if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg) =? reac_disco_table_observe_c.fam_of T ai),
    ((if ow =? 0 then owned_of T ai else 1) =? owned_of T ai),
    (reac_disco_table_observe_c.ch_of T ai <? s_ch Sg); reflexivity. }
pose proof (regs_ok11 cx E regs xv ai HdE HrL R10 R22 HAr2 ltac:(lia) Hai8 ltac:(lia)) as RO1. fold Es in RO1.
assert (HEI : img_env VAL A_LIM Es).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold Es, d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] Es (rd W mem3)) by constructor.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (MP : forall x, mem3 x = mem3 x) by reflexivity.
unfold cfg_at. change (w64 (BASE + 0x1990)) with (Z_to_bv 64 (BASE + 0x1990)).
clear XV HFret.
assert (Hc : ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
all: unfold ss_d in HS; ro_base HS 516%nat; ro_base HS 529%nat; ro_base HS 60%nat.
all: o9_go RUNTO BR.
all: repeat rewrite wvb_collapse in HJ.
all: apply SRr_ret.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?ms) |- _ =>
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs ms) r = getr regs r)
    by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS), (RO1 r); cbv [In] in Hr;
        repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
  assert (RX : forall (r : bv 5) q v, sr_get (ss_regs ss) r = SOff q 0 -> ew Ex q = Z_to_bv 64 v -> getr (ms_regs ms) r = w64 v)
    by (intros r q v Hq Hv; rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS), Hq; exact (o4_sv_atom _ q v Hv));
  assert (RF : forall (r : bv 5) cc, sr_get (ss_regs ss) r = SOff 516 cc -> getr (ms_regs ms) r = w64 (d_FB cx + cc))
    by (intros r cc Hq; rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS), Hq; cbn [sv_denot]; rewrite EW516, w64_add_w; reflexivity);
  apply (o4_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h i now nb fr len n ly3 S3 W mem3 _ k acc E _ ss ms Hf0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HdE HS
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) MP
    Hi Hnow Hlen Hnb Hbody Hsp0 Hfrm);
  [ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25); unfold d_rL, spZ in *;
    rewrite (RG 2%bv), (RG 3%bv), (RG 4%bv), (RG 8%bv), (RG 9%bv), (RG 18%bv), (RG 20%bv), (RG 25%bv) by (cbv; tauto);
    repeat split; assumption
  | exact (RX 14%bv 578%nat _ ltac:(vm_compute; reflexivity) EW578)
  | exact (RX 24%bv 579%nat _ ltac:(vm_compute; reflexivity) EW579)
  | exact (RX 23%bv 576%nat _ ltac:(vm_compute; reflexivity) EW576)
  | exact (RX 27%bv 580%nat _ ltac:(vm_compute; reflexivity) EW580)
  | exact (RF 22%bv 2992 ltac:(vm_compute; reflexivity))
  | exact (RF 26%bv 2128 ltac:(vm_compute; reflexivity)) ]
end.
Qed.

End h.
End f.
End d.
