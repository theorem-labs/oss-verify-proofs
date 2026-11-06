(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D1p56.v, with its module paths and module names changed; 923 of its 968 lines of code are new or changed and 696 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition oz_a1 (T Sg : list byte) (ai : Z) : Z :=
  if (role_of_e T ai =? 1) && (s_role Sg =? 2) then 1 else s_role Sg.
Definition oz_role (T Sg : list byte) (ai : Z) : Z := if s_role Sg =? 0 then role_of_e T ai else oz_a1 T Sg ai.
Definition oz_hd (T Sg : list byte) (ai : Z) : Z := if s_hd Sg =? 0 then hd_of T ai else 1.
Definition oz_din (T Sg : list byte) (ai : Z) : Z := if s_hd Sg =? 0 then din_of T ai else s_din Sg.
Definition oz_dout (T Sg : list byte) (ai : Z) : Z := if s_hd Sg =? 0 then dout_of T ai else s_dout Sg.
Definition oz_slots (T Sg : list byte) (ai : Z) : Z :=
  if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg.
Definition oz_fam (T Sg : list byte) (ai : Z) : Z :=
  if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg.
Definition oz_ch (T Sg : list byte) (ai : Z) : Z :=
  bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg else reac_disco_table_observe_c.ch_of T ai).
Definition oz_own (T : list byte) (ai ow : Z) : Z := if ow =? 0 then u64 (owned_of T ai) else 1.

Definition oz_acs : list YP09.chunk :=
  map (fun kv => YP09.mkChunk (fst kv) (CVal 8 (SOff (snd kv) 0)))
  [(184, 563%nat); (120, 564%nat); (136, 565%nat); (376, 566%nat); (280, 567%nat); (232, 568%nat); (264, 569%nat);
   (208, 570%nat); (320, 571%nat); (200, 572%nat); (328, 573%nat); (368, 574%nat); (408, 575%nat);
   (352, 576%nat); (192, 577%nat); (104, 578%nat); (96, 579%nat); (88, 580%nat); (80, 581%nat); (296, 582%nat);
   (72, 583%nat); (48, 584%nat); (64, 585%nat); (56, 586%nat); (360, 587%nat)].
Definition oz_tcs : list YP09.chunk :=
  [YP09.mkChunk 3000 (CVal 4 (SOff 588 0)); YP09.mkChunk 3004 (CVal 1 (SOff 589 0));
   YP09.mkChunk 3005 (CVal 1 (SOff 590 0)); YP09.mkChunk 3006 (CVal 1 (SOff 591 0));
   YP09.mkChunk 3007 (CVal 1 (SOff 592 0)); YP09.mkChunk 3008 (CVal 1 (SOff 593 0));
   YP09.mkChunk 3012 (CVal 4 (SOff 594 0)); YP09.mkChunk 2544 (CVal 4 (SOff 595 0))].

Lemma oz_u_rng : forall (L : list byte) p (n : nat), 0 <= u_at L p n < 2 ^ (8 * Z.of_nat n).
Proof.
intros L p n. unfold u_at. pose proof (YK11.bytes_le_to_Z_nonneg (sub L p n)) as H0.
pose proof (YK11.bytes_le_to_Z_bound (sub L p n)) as H1.
assert (Hl : (length (sub L p n) <= n)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [exact H0|]. eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma oz_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Lemma oz_nth_le_byte : forall bs k (b : byte),
  nth_error bs k = Some b -> bv_unsigned b = (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
induction bs as [|b0 bs IHbs]; intros k b H; [destruct k; discriminate H|].
rewrite oz_ble_cons. pose proof (u8_range b0) as Hb0. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
destruct k as [|k].
- cbn in H. injection H as <-. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. lia.
- cbn [nth_error] in H. rewrite (IHbs k b H).
  replace (8 * Z.of_nat (Datatypes.S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  rewrite <- Z.div_div by lia. f_equal. f_equal. lia.
Qed.
Lemma oz_oldv : forall ai v, 0 <= ai -> oldv ai v = v.
Proof. intros ai v H. unfold oldv. destruct (Z.ltb_spec ai 0); [lia | reflexivity]. Qed.
Lemma oz_w64_u64 : forall v, Z_to_bv 64 (u64 v) = Z_to_bv 64 v.
Proof. intros v. unfold u64. exact (Z_to_bv64_canon v). Qed.

Lemma oz_swrap_s32 : forall v, 0 <= v < 2 ^ 32 -> bv_swrap 32 v = CtrlParsed.s32 v.
Proof.
intros v Hv. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, CtrlParsed.s32.
change (2 ^ Z.of_N 32) with (2 ^ 32).
destruct (Z.ltb_spec v (2 ^ 31)).
- rewrite Z.mod_small by lia. lia.
- replace (v + 2 ^ 32 / 2) with ((v - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.
Lemma oz_u4_s32 : forall (L : list byte) p, 0 <= s32_at L p -> u_at L p 4 = s32_at L p.
Proof.
intros L p H. pose proof (oz_u_rng L p 4) as Hr. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hr.
unfold s32_at, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
change (2 ^ Z.of_N 32) with (2 ^ 32) in *.
assert (E : (u_at L p 4 + 2 ^ 32 / 2) mod 2 ^ 32 - 2 ^ 32 / 2 = if u_at L p 4 <? 2 ^ 31 then u_at L p 4 else u_at L p 4 - 2 ^ 32).
{ destruct (Z.ltb_spec (u_at L p 4) (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (u_at L p 4 + 2 ^ 32 / 2) with ((u_at L p 4 - 2 ^ 31) + 1 * 2 ^ 32) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia. }
rewrite E in H |- *. destruct (Z.ltb_spec (u_at L p 4) (2 ^ 31)); lia.
Qed.
Lemma oz_keep_mac : forall T Sg ow now T' ret ai,
  length T = 400%nat -> length Sg = 24%nat -> disco_table_c.table_ok T ->
  disco_table_c.find_res T (disco_table_c.s_mac Sg) ai -> 0 <= ai ->
  reac_disco_table_observe_c.observe_model T Sg ow now T' ret ->
  disco_table_c.mac_of T' ai = disco_table_c.s_mac Sg /\ disco_table_c.n_of T' = disco_table_c.n_of T /\ length T' = 400%nat.
Proof.
intros T Sg ow now T' ret ai LT LS (T1 & _) FR Hai OM.
pose proof T1 as T1'. unfold tbl_T1 in T1'.
assert (Hr8 : 0 <= ai < 8) by (destruct FR as [[? _]|[? _]]; lia).
pose proof (slot_observe.known_arm T Sg ow now T' ret ai FR Hai OM) as E.
destruct (slot_observe.ok_facts T Sg ow now ai T' ret LT LS Hr8 E) as (LT' & EM & E384 & _).
split; [|split; [apply slot_observe.n_of_sub; exact E384 | exact LT']].
rewrite (EM ai Hr8). destruct FR as [[? _] | (_ & M & _)]; [lia | exact M].
Qed.
Lemma oz_keep_mac_bytes : forall T Sg ow now T' ret ai,
  length T = 400%nat -> length Sg = 24%nat -> disco_table_c.table_ok T ->
  disco_table_c.find_res T (disco_table_c.s_mac Sg) ai -> 0 <= ai ->
  reac_disco_table_observe_c.observe_model T Sg ow now T' ret ->
  forall j, 0 <= j < 6 -> nth (Z.to_nat (48 * ai + j)) T' (Z_to_bv 8 0) = nth (Z.to_nat j) Sg (Z_to_bv 8 0).
Proof.
intros T Sg ow now T' ret ai LT LS TO FR Hai OM j Hj.
destruct (oz_keep_mac T Sg ow now T' ret ai LT LS TO FR Hai OM) as (M & _ & LT').
assert (Hai8 : ai < 8) by (destruct TO as (T1 & _); unfold tbl_T1 in T1; destruct FR as [[? _]|[? _]]; lia).
unfold mac_of, s_mac in M.
assert (E1 : nth_error (sub T' (48 * ai) 6) (Z.to_nat j) = nth_error (sub Sg 0 6) (Z.to_nat j)) by (rewrite M; reflexivity).
rewrite !slot_observe.ne_sub in E1 by lia.
replace ((Z.to_nat j <? 6)%nat) with true in E1 by (symmetry; apply Nat.ltb_lt; lia).
replace (Z.to_nat (48 * ai) + Z.to_nat j)%nat with (Z.to_nat (48 * ai + j)) in E1 by lia.
replace (Z.to_nat 0 + Z.to_nat j)%nat with (Z.to_nat j) in E1 by lia.
assert (Ha : (Z.to_nat (48 * ai + j) < length T')%nat) by lia.
assert (Hb : (Z.to_nat j < length Sg)%nat) by lia.
rewrite (nth_error_nth' T' (Z_to_bv 8 0) Ha) in E1. rewrite (nth_error_nth' Sg (Z_to_bv 8 0) Hb) in E1.
injection E1 as E1. exact E1.
Qed.
Lemma oz_sx_ltu : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  ((bv_swrap 32 a) mod 2 ^ 64 <? (bv_swrap 32 b) mod 2 ^ 64) = (a <? b).
Proof.
intros a b Ha Hb. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32).
assert (Ea : (a + 2 ^ 32 / 2) mod 2 ^ 32 - 2 ^ 32 / 2 = if a <? 2 ^ 31 then a else a - 2 ^ 32).
{ destruct (Z.ltb_spec a (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (a + 2 ^ 32 / 2) with ((a - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. }
assert (Eb : (b + 2 ^ 32 / 2) mod 2 ^ 32 - 2 ^ 32 / 2 = if b <? 2 ^ 31 then b else b - 2 ^ 32).
{ destruct (Z.ltb_spec b (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (b + 2 ^ 32 / 2) with ((b - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. }
rewrite Ea, Eb.
destruct (Z.ltb_spec a (2 ^ 31)); destruct (Z.ltb_spec b (2 ^ 31)).
- rewrite !Z.mod_small by lia. reflexivity.
- rewrite (Z.mod_small a) by lia.
  replace (b - 2 ^ 32) with ((b - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add, Z.mod_small by lia.
  destruct (Z.ltb_spec a (b - 2 ^ 32 + 2 ^ 64)); destruct (Z.ltb_spec a b); lia.
- rewrite (Z.mod_small b) by lia.
  replace (a - 2 ^ 32) with ((a - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add, Z.mod_small by lia.
  destruct (Z.ltb_spec (a - 2 ^ 32 + 2 ^ 64) b); destruct (Z.ltb_spec a b); lia.
- replace (a - 2 ^ 32) with ((a - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
  replace (b - 2 ^ 32) with ((b - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
  rewrite !Z.mod_add, !Z.mod_small by lia.
  destruct (Z.ltb_spec (a - 2 ^ 32 + 2 ^ 64) (b - 2 ^ 32 + 2 ^ 64)); destruct (Z.ltb_spec a b); lia.
Qed.

Lemma oz_U0 : forall E, U E (SLit 0) = 0.
Proof. intros E. rewrite U_SLit. reflexivity. Qed.
Lemma oz_zx8 : forall E q v, ew E q = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff q 0)) = v.
Proof.
intros E q v H Hv. rewrite U_SExt, (U_atom E q v H ltac:(lia)). cbv iota.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Lemma oz_sx32u : forall E q v, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  U E (SExt true 32 (SOff q 0)) = (bv_swrap 32 v) mod 2 ^ 64.
Proof.
intros E q v H Hv. rewrite U_SExt, (U_atom E q v H ltac:(lia)). cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Z.mod_small by lia. unfold zcanon, M64. reflexivity.
Qed.
Lemma oz_u_mod : forall E q v, ew E q = Z_to_bv 64 v -> U E (SOff q 0) = v mod 2 ^ 64.
Proof.
intros E q v H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, zcanon, M64.
change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma oz_dn_off : forall E q v, ew E q = Z_to_bv 64 v -> sv_denot E (SOff q 0) = Z_to_bv 64 v.
Proof. intros E q v H. rewrite sv_denot_SOff0. exact H. Qed.
Lemma oz_dn_sx32 : forall E q u, ew E q = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff q 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E q u H Hu. rewrite denot_lit_U, (oz_sx32u E q u H Hu). apply Z_to_bv64_canon.
Qed.
Lemma oz_dn_zx8 : forall E q u, ew E q = Z_to_bv 64 u -> 0 <= u < 256 ->
  sv_denot E (SExt false 8 (SOff q 0)) = Z_to_bv 64 u.
Proof. intros E q u H Hu. rewrite denot_lit_U, (oz_zx8 E q u H Hu). reflexivity. Qed.
Lemma oz_dn_add0 : forall E e v, sv_denot E e = Z_to_bv 64 v -> sv_denot E (SAlu ALU_ADD e (SLit 0)) = Z_to_bv 64 v.
Proof.
intros E e v H. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. unfold U at 1. rewrite H, U_SLit.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, zcanon, M64. change (2 ^ Z.of_N 64) with (2 ^ 64).
change (0 mod 18446744073709551616) with 0. rewrite Z.add_0_r, Z.mod_mod by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma oz_vm_u64 : forall m a v, val_mem SEGS m a 8 v <-> val_mem SEGS m a 8 (u64 v).
Proof.
intros m a v. unfold val_mem, u64.
split; intros H k Hk; rewrite (H k Hk); first [unfold YO0f.le_byte | unfold YG0f.le_byte];
change (8 * Z.of_nat 8) with 64; rewrite ?Zmod_mod; reflexivity.
Qed.
Lemma oz_garr8_nth : forall (m : word -> option byte) base (L : list byte) j b,
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) L) -> nth_error L j = Some b ->
  mbyte SEGS m (base + Z.of_nat j) = Some b.
Proof.
intros m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte SEGS m base _ j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth _ j 0 (map_nth_error (fun b : byte => bv_unsigned b) j L Hj)). apply Z_to_bv_bv_unsigned.
Qed.
Lemma oz_u_val : forall (m : word -> option byte) t (L : list byte) p (n : nat),
  garr8 SEGS m t (map (fun b : byte => bv_unsigned b) L) ->
  0 <= p -> p + Z.of_nat n <= Z.of_nat (length L) ->
  val_mem SEGS m (t + p) n (u_at L p n).
Proof.
intros m t L p n GT Hp Hpn k Hk.
pose proof (oz_u_rng L p n) as Hb.
destruct (nth_error L (Z.to_nat p + k)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (t + p + Z.of_nat k) with (t + Z.of_nat (Z.to_nat p + k)) by lia.
rewrite (oz_garr8_nth m t L _ b GT Hb2). f_equal.
rewrite le_byte_small by first [exact Hk | exact Hb].
assert (Hs : nth_error (sub L p n) k = Some b).
{ unfold sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec k n); [|lia]. rewrite nth_error_skipn. exact Hb2. }
pose proof (oz_nth_le_byte _ _ _ Hs) as Hv.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. unfold u_at. rewrite <- Hv. first [reflexivity | symmetry; apply Z.mod_small; apply (u8_range b)].
Qed.
Lemma oz_obs_len : forall regs, length (obs_vals regs) = 32%nat.
Proof. intros regs. unfold obs_vals. rewrite length_map, length_seq. reflexivity. Qed.
Lemma oz_atom : forall cx E regs X j, (j < length X)%nat ->
  ew (d_env cx E (obs_vals regs ++ X)) (563 + j) = nth j X (Z_to_bv 64 0).
Proof.
intros cx E regs X j Hj. replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
rewrite oy_d_env_x by (rewrite length_app, oz_obs_len; lia).
rewrite app_nth2 by (rewrite oz_obs_len; lia). rewrite oz_obs_len. f_equal. lia.
Qed.
Lemma oz_ew_low : forall cx E regs X q, (q < 563)%nat ->
  ew (d_env cx E (obs_vals regs ++ X)) q = ew (d_env cx E (obs_vals regs)) q.
Proof.
intros cx E regs X q Hq.
destruct (Nat.ltb_spec q AT_FL) as [H1|H1]; [rewrite !oy_d_env_old by exact H1; reflexivity|].
destruct (Nat.eqb_spec q AT_FL) as [->|H2]; [rewrite !oy_d_env_fl; reflexivity|].
replace q with (AT_X + (q - AT_X))%nat by (unfold AT_X, AT_FL in *; lia).
rewrite !oy_d_env_x by (rewrite ?length_app, ?oz_obs_len; unfold AT_X, AT_FL in *; lia).
rewrite app_nth1 by (rewrite oz_obs_len; unfold AT_X, AT_FL in *; lia). reflexivity.
Qed.
Lemma oz_regs_ok : forall B cx E regs X, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (obs_vals regs ++ X)) obs_sr regs.
Proof.
intros B cx E regs X HE HL HA.
pose proof (regs_ok_obs B cx E regs HE HL HA) as R.
apply regs_ok_by_cases. intros r Hr. rewrite (R r).
cbv [all_regs In] in Hr.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ];
  (match goal with |- sv_denot _ (sr_get ?sr ?r) = _ =>
     let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end);
  first [ reflexivity | cbn [sv_denot]; rewrite oz_ew_low by lia; reflexivity ].
Qed.

Definition oz_x (cx : dcx) (h i now nb fr len : Z) (T T' Sg : list byte) (ai ow : Z) : list word :=
  [w64 (u64 h); w64 (u64 (h + 440)); w64 (u64 0); w64 (u64 (dnot (d_obj cx OG))); w64 (u64 (dnot (d_obj cx OT)));
   w64 (u64 (dnot (d_obj cx OO))); w64 (u64 (dnot (d_obj cx OUSED)));
   w64 (u64 i); w64 (u64 now); w64 (u64 (d_cur cx nb)); w64 (u64 nb); w64 (u64 fr); w64 (u64 len);
   w64 (u64 (oldv ai (role_of_e T ai))); w64 (u64 (oldv ai (hd_of T ai))); w64 (u64 (oldv ai (din_of T ai)));
   w64 (u64 (oldv ai (dout_of T ai))); w64 (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai)));
   w64 (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai))); w64 (u64 (oldv ai (s32_at T (48 * ai + 20))));
   w64 (u64 (oldv ai (owned_of T ai))); w64 (u64 (oldv ai (u_at T (48 * ai + 32) 8)));
   w64 (u64 (16 * ai)); w64 (u64 (64 * ai)); w64 (u64 ow);
   w64 (u_at Sg 8 4); w64 (u_at Sg 12 1); w64 (u_at Sg 13 1); w64 (u_at Sg 14 1); w64 (u_at Sg 15 1);
   w64 (u_at Sg 16 1); w64 (u_at Sg 20 4); w64 (u_at T' 384 4);
   w64 (oz_a1 T Sg ai); w64 (oz_role T Sg ai); w64 (oz_din T Sg ai); w64 (oz_dout T Sg ai); w64 (oz_hd T Sg ai);
   w64 (oz_slots T Sg ai); w64 (oz_fam T Sg ai); w64 (oz_ch T Sg ai); w64 (oz_own T ai ow)].

Lemma oz_pres_grow : forall (H : word -> bool) (m1 m2 : word -> option byte),
  mem_grows (mrestrict H m1) (mrestrict H m2) -> forall a, apresent H m1 a -> apresent H m2 a.
Proof.
intros H m1 m2 HG a (Hh & b & Hb). split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E2; [exists b'; reflexivity|]. exfalso. apply HG; [discriminate | reflexivity].
Qed.

Lemma oz_drop_cond : forall (fq : YK11.FPState) E pc rs sm rv ats c cs al (ms : machine_state),
  st_ok_pi (fx := fq) SEGS VAL E (mkSST pc rs [] sm rv (mkFacts ats (c :: cs) al)) ms ->
  st_ok_pi (fx := fq) SEGS VAL E (mkSST pc rs [] sm rv (mkFacts ats cs al)) ms.
Proof.
intros fq E pc rs sm rv ats c cs al ms HS.
unfold st_ok_pi, abs_ss, setpc in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
destruct HS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & Ha & Hc & Hl).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
split; [exact A6|]. split; [exact A7|]. split; [exact A8|].
split; [exact Ha|]. split; [exact (proj2 Hc) | exact Hl].
Qed.

Ltac oz_hwin UA :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi aa Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin; intros; subst; cbn [base_val] in Ha; first [ lia | rewrite UA in Ha; lia ] | ]);
  destruct Hin.

Ltac oz_awr UA :=
  cbn [ss_mem];
  repeat (first [ apply awr_ok_cons_ro; [cbn; lia|]
                | eapply awr_ok_cons_gen; [reflexivity | exact UA | intros a Ha; left; cbn [YP09.r_wlo YP09.r_whi] in Ha;
                    unfold LLVMF_STK; lia | ] ]);
  apply awr_ok_nil.

Ltac oz_keep cx0 m0 UA :=
  lazymatch goal with
  | HFr : frame_of ?E ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- _ =>
    lazymatch goal with
    | HG : mem_grows (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- _ =>
      lazymatch goal with
      | MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx0 <= a < d_A cx0 + 472) -> _ = _ |- _ =>
        lazymatch goal with
        | MPR : forall a, apresent (w_H ?W) m0 a -> apresent (w_H ?W) ?m1 a |- _ =>
          let M2 := fresh "M2" in let P2 := fresh "P2" in
          assert (M2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx0 <= a < d_A cx0 + 472) ->
            aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m0 a)
            by (let aa := fresh "aa" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
                intros aa Ha Hn;
                rewrite (kept_of_frame E rs (w_H W) m1 m2 (fun z => d_A cx0 <= z < d_A cx0 + 472) HFr
                  ltac:(oz_hwin UA) aa Ha Hn); apply MEQ; assumption);
          assert (P2 : forall a, apresent (w_H W) m0 a -> apresent (w_H W) m2 a)
            by (let aa := fresh "aa" in let Hp := fresh "Hp" in
                intros aa Hp; apply (oz_pres_grow (w_H W) m1 m2 HG); apply MPR; exact Hp);
          clear MEQ MPR HFr HG; rename M2 into MEQ; rename P2 into MPR
        end end end end.

Lemma oz_pi_of_ok : forall (fq : YK11.FPState) E (ss : sstate) (ms : machine_state) pc,
  st_ok (fx := fq) SEGS E ss ms -> ss_pc ss = BASE + pc ->
  st_ok_pi (fx := fq) SEGS VAL E (mkSST pc (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros fq E ss ms pc HS Hpc. unfold st_ok_pi, abs_ss, setpc.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
rewrite <- Hpc. destruct ss. exact HS.
Qed.

Lemma oz_pres : forall a b (r : bv 5), aregs_preserved a b -> acallee_saved (bv_unsigned r) -> getr b r = getr a r.
Proof. intros a b r H Hr. pose proof (H (bv_unsigned r) Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.

Lemma oz_aview_garr8 : forall H (m : word -> option byte) p (L : list byte) j,
  garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) L) -> (j < length L)%nat ->
  aview SEGS H m (p + Z.of_nat j) = Some (bv_unsigned (nth j L (Z_to_bv 8 0))).
Proof.
intros H m p L j HG Hj. unfold aview.
rewrite (garr8_mbyte SEGS (mrestrict H m) p _ j HG) by (rewrite length_map; exact Hj).
cbn [option_map]. f_equal. rewrite (map_nth (fun b : byte => bv_unsigned b) L (Z_to_bv 8 0)).
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma oz_aview_present : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Ltac oz_cs := unfold acallee_saved;
  repeat match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

Ltac oz_fld RA UA DEN :=
  eapply (field_of_region _ _ 60%nat _ _ _ _ _ _ _ 8%N _ _ RA);
  [ exact UA
  | cbn [In]; repeat (first [left; reflexivity | right])
  | exact DEN
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); first [ apply oy_u64_rng | lia | assumption ]
  | cbn; lia ].

Ltac oz_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Ltac oz_setreg EV r e :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
    let G := fresh "GG" in let Hr := fresh "Hrr" in
    assert (G : getr (ms_regs msx) r = sv_denot EV e);
    [ cbn [ms_regs restrict]; oz_reg HS r Hr; rewrite Hr; clear Hr
    | let HS2 := fresh "HS2" in
      pose proof (st_ok_pi_set_reg EV _ _ r e HS ltac:(discriminate) G) as HS2;
      clear HS G; rename HS2 into HS; norm_ss HS ]
  end.

Ltac oz_fin :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
    apply SRr_ret; split; [reflexivity|]; exists msx; eexists;
    split; [reflexivity | split; [exact HS | split; [assumption | split; assumption]]]
  end.

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
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis BCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).

Definition oz_J (fq : YK11.FPState) (cx : dcx) (ly3 : alayout) (S3 : astate) (k : Z)
  (m0 : word -> option byte) (E : env) (ss : sstate) (W : world SEGS) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists (ms : machine_state) (md : Model),
    c' = mkCfg ms md /\
    st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) /\
    ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
       aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) m0 a) /\
    (forall a, apresent (w_H W) m0 a -> apresent (w_H W) (ms_mem ms) a).

Ltac oz_show :=
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss _ |- _ =>
    let r := eval vm_compute in (ss_pc ss, ss_regs ss) in idtac r end.

Theorem ob_s9a1 : ob_seg9a1 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & HOT & R25 & R23 & Hai0).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (S208 & S320) & (F1 & F2 & F0 & F3) & HSgl & HSg & HSf &
  (R200 & R328 & R368 & R408) & Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof HOT as (LT & TOK & HFR & How & HSP & H360 & HOM).
pose proof HSP as (V64 & V56 & V352 & V192 & V104 & V96 & V88 & V80 & V296 & V72 & V48).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & V184 & V120 & V136 & V376 & V280 & V232 & V264).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (G16 & Glo & Ghi & GF0 & GFc & GFia & GFo & GF32 & GFpres & GSpres & GWpres & GAR & Gfin & Gefa & Gefl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as ACV.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (HOTr : 0 <= d_obj cx OT /\ d_obj cx OT + 400 <= alloc_ceiling) by (unfold d_obj, dobj_off; lia).
assert (HOSr : 0 <= d_obj cx OS /\ d_obj cx OS + 24 <= alloc_ceiling) by (unfold d_obj, dobj_off; lia).
pose proof TOK as (TT1 & TT2 & TT3 & TT4). unfold tbl_T1 in TT1.
assert (Hain : 0 <= ai < n_of T) by (destruct HFR as [(Hx & _) | (Hx & _)]; lia).
assert (Hai8 : 0 <= ai < 8) by lia.
assert (Hrole : role_of_e T ai = 0 \/ role_of_e T ai = 1 \/ role_of_e T ai = 2) by (apply TT2; lia).
assert (Hrole2 : 0 <= role_of_e T ai <= 2) by (destruct Hrole as [Hx|[Hx|Hx]]; lia).
assert (Hhd : hd_of T ai = 0 \/ hd_of T ai = 1) by (destruct (TT4 ai ltac:(lia)) as (Hx & _); exact Hx).
assert (Hown : owned_of T ai = 0 \/ owned_of T ai = 1) by (destruct (TT4 ai ltac:(lia)) as (_ & _ & Hx); exact Hx).
destruct (oz_keep_mac T Sg ow now T' ret ai LT HSgl TOK HFR ltac:(lia) HOM) as (Hmac & Hnof & HTl').
pose proof HSf as (_ & _ & _ & _ & _ & (_ & HSR & _) & _).
assert (Efu : CtrlParsed.fu Sg 8 4 = u_at Sg 8 4) by reflexivity.
rewrite Efu in HSR.
assert (HuSg1 : forall p, 0 <= u_at Sg p 1 < 256)
  by (intros p; pose proof (oz_u_rng Sg p 1) as Hx; change (2 ^ (8 * Z.of_nat 1)) with 256 in Hx; lia).
assert (HuSg4 : forall p, 0 <= u_at Sg p 4 < 2 ^ 32)
  by (intros p; pose proof (oz_u_rng Sg p 4) as Hx; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hx; lia).
assert (HuT1 : forall p, 0 <= u_at T p 1 < 256)
  by (intros p; pose proof (oz_u_rng T p 1) as Hx; change (2 ^ (8 * Z.of_nat 1)) with 256 in Hx; lia).
assert (HuT4 : forall p, 0 <= u_at T p 4 < 2 ^ 32)
  by (intros p; pose proof (oz_u_rng T p 4) as Hx; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hx; lia).
assert (HuTp4 : forall p, 0 <= u_at T' p 4 < 2 ^ 32)
  by (intros p; pose proof (oz_u_rng T' p 4) as Hx; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hx; lia).
assert (Hsr : 0 <= s_role Sg <= 2)
  by (unfold s_role, s32_at; rewrite (oz_swrap_s32 (u_at Sg 8 4) (HuSg4 8)); exact HSR).
assert (HS1 : s_role Sg = 0 \/ s_role Sg = 1 \/ s_role Sg = 2) by lia.
assert (Hu8 : u_at Sg 8 4 = s_role Sg) by (unfold s_role in *; apply oz_u4_s32; lia).
set (X := oz_x cx h i now nb fr len T T' Sg ai ow).
assert (XA : forall j, (j < 42)%nat -> ew (d_env cx E (obs_vals regs ++ X)) (563 + j) = nth j X (Z_to_bv 64 0))
  by (intros j Hj; apply oz_atom; unfold X, oz_x; cbn [length]; lia).
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ X)) (rd W mem3) (d_A cx)) oz_acs).
{ unfold oz_acs. cbn [map fst snd].
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?q 0))) =>
    let j := eval vm_compute in (q - 563)%nat in
    let v := eval cbv beta iota zeta delta [X oz_x nth] in (nth j X (Z_to_bv 64 0)) in
    lazymatch v with w64 (u64 ?z) =>
      apply (chunk_ok_val SEGS _ _ _ o 8 _ (u64 z));
      [ rewrite sv_denot_SOff0; exact (XA j ltac:(lia)) | apply oy_u64_rng | cbn; lia
      | first [ assumption | apply (proj1 (oz_vm_u64 _ _ z)); assumption ] ]
    end
  end. }
assert (HTCS : Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ X)) (rd W mem3) (d_FB cx)) oz_tcs).
{ unfold oz_tcs. repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?wd (SOff ?q 0))) =>
    let j := eval vm_compute in (q - 563)%nat in
    let v := eval cbv beta iota zeta delta [X oz_x nth] in (nth j X (Z_to_bv 64 0)) in
    lazymatch v with w64 (u_at ?L ?p ?nn) =>
      apply (chunk_ok_val SEGS _ _ _ o wd _ (u_at L p nn));
      [ rewrite sv_denot_SOff0; exact (XA j ltac:(lia)) | exact (oz_u_rng L p nn) | cbn; lia
      | lazymatch L with
        | Sg => replace (d_FB cx + o) with (d_obj cx OS + p) by (unfold d_obj, dobj_off; lia);
                exact (oz_u_val _ _ Sg p nn HSg ltac:(lia) ltac:(rewrite HSgl; cbn; lia))
        | _ => replace (d_FB cx + o) with (d_obj cx OT + p) by (unfold d_obj, dobj_off; lia);
                exact (oz_u_val _ _ L p nn HT ltac:(lia) ltac:(rewrite HTl; cbn; lia))
        end ]
    end
  end. }
pose proof (oz_regs_ok B cx E regs X HdE HrL HAr2) as HROK.
pose proof (FACTS LAWS cx ly3 S3 W mem3 md3 k E (obs_vals regs ++ X) [] [] HC HdE I I) as HFACTS.
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OB_C9 obs_sr (obs_vals regs ++ X) oz_acs oz_tcs []
  (d_facts [] []) HC HdE Hregs Hflag HROK HFACTS HACS HTCS (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (oy_d_E_env cx E (obs_vals regs ++ X) HdE) as HdE'.
pose proof (oy_d_env_fl cx E (obs_vals regs ++ X)) as HFL'.
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs ++ X))) by (destruct HdE' as (_ & _ & HI & _); exact HI).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs ++ X)) (rd W mem3)) by constructor.
assert (E556 : ew (d_env cx E (obs_vals regs ++ X)) 556 = w64 (n_of T)).
{ change 556%nat with (AT_X + 25)%nat. rewrite oy_d_env_x by (rewrite length_app, oz_obs_len; unfold X, oz_x; cbn [length]; lia).
  rewrite app_nth1 by (rewrite oz_obs_len; lia). unfold obs_vals. cbn [nth map seq].
  rewrite <- R25. f_equal; try (apply bv_eq; reflexivity). }
assert (E554 : ew (d_env cx E (obs_vals regs ++ X)) 554 = w64 ret).
{ change 554%nat with (AT_X + 23)%nat. rewrite oy_d_env_x by (rewrite length_app, oz_obs_len; unfold X, oz_x; cbn [length]; lia).
  rewrite app_nth1 by (rewrite oz_obs_len; lia). unfold obs_vals. cbn [nth map seq].
  rewrite <- R23. f_equal; try (apply bv_eq; reflexivity). }
set (Ev := d_env cx E (obs_vals regs ++ X)) in *.
assert (E563 : ew Ev 563 = w64 (u64 h)) by exact (XA 0%nat ltac:(lia)).
assert (E564 : ew Ev 564 = w64 (u64 (h + 440))) by exact (XA 1%nat ltac:(lia)).
assert (E565 : ew Ev 565 = w64 (u64 0)) by exact (XA 2%nat ltac:(lia)).
assert (E566 : ew Ev 566 = w64 (u64 (dnot (d_obj cx OG)))) by exact (XA 3%nat ltac:(lia)).
assert (E568 : ew Ev 568 = w64 (u64 (dnot (d_obj cx OO)))) by exact (XA 5%nat ltac:(lia)).
assert (E569 : ew Ev 569 = w64 (u64 (dnot (d_obj cx OUSED)))) by exact (XA 6%nat ltac:(lia)).
assert (E570 : ew Ev 570 = w64 (u64 i)) by exact (XA 7%nat ltac:(lia)).
assert (E571 : ew Ev 571 = w64 (u64 now)) by exact (XA 8%nat ltac:(lia)).
assert (E572 : ew Ev 572 = w64 (u64 (d_cur cx nb))) by exact (XA 9%nat ltac:(lia)).
assert (E573 : ew Ev 573 = w64 (u64 nb)) by exact (XA 10%nat ltac:(lia)).
assert (E574 : ew Ev 574 = w64 (u64 fr)) by exact (XA 11%nat ltac:(lia)).
assert (E575 : ew Ev 575 = w64 (u64 len)) by exact (XA 12%nat ltac:(lia)).
assert (E584 : ew Ev 584 = w64 (u64 (oldv ai (u_at T (48 * ai + 32) 8)))) by exact (XA 21%nat ltac:(lia)).
assert (E567 : ew Ev 567 = w64 (u64 (dnot (d_obj cx OT)))) by exact (XA 4%nat ltac:(lia)).
assert (E576 : ew Ev 576 = w64 (u64 (oldv ai (role_of_e T ai)))) by exact (XA 13%nat ltac:(lia)).
assert (E577 : ew Ev 577 = w64 (u64 (oldv ai (hd_of T ai)))) by exact (XA 14%nat ltac:(lia)).
assert (E578 : ew Ev 578 = w64 (u64 (oldv ai (din_of T ai)))) by exact (XA 15%nat ltac:(lia)).
assert (E579 : ew Ev 579 = w64 (u64 (oldv ai (dout_of T ai)))) by exact (XA 16%nat ltac:(lia)).
assert (E580 : ew Ev 580 = w64 (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai)))) by exact (XA 17%nat ltac:(lia)).
assert (E581 : ew Ev 581 = w64 (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai)))) by exact (XA 18%nat ltac:(lia)).
assert (E582 : ew Ev 582 = w64 (u64 (oldv ai (s32_at T (48 * ai + 20))))) by exact (XA 19%nat ltac:(lia)).
assert (E583 : ew Ev 583 = w64 (u64 (oldv ai (owned_of T ai)))) by exact (XA 20%nat ltac:(lia)).
assert (E585 : ew Ev 585 = w64 (u64 (16 * ai))) by exact (XA 22%nat ltac:(lia)).
assert (E586 : ew Ev 586 = w64 (u64 (64 * ai))) by exact (XA 23%nat ltac:(lia)).
assert (E587 : ew Ev 587 = w64 (u64 ow)) by exact (XA 24%nat ltac:(lia)).
assert (E588 : ew Ev 588 = w64 (u_at Sg 8 4)) by exact (XA 25%nat ltac:(lia)).
assert (E589 : ew Ev 589 = w64 (u_at Sg 12 1)) by exact (XA 26%nat ltac:(lia)).
assert (E590 : ew Ev 590 = w64 (u_at Sg 13 1)) by exact (XA 27%nat ltac:(lia)).
assert (E591 : ew Ev 591 = w64 (u_at Sg 14 1)) by exact (XA 28%nat ltac:(lia)).
assert (E592 : ew Ev 592 = w64 (u_at Sg 15 1)) by exact (XA 29%nat ltac:(lia)).
assert (E593 : ew Ev 593 = w64 (u_at Sg 16 1)) by exact (XA 30%nat ltac:(lia)).
assert (E594 : ew Ev 594 = w64 (u_at Sg 20 4)) by exact (XA 31%nat ltac:(lia)).
assert (E595 : ew Ev 595 = w64 (u_at T' 384 4)) by exact (XA 32%nat ltac:(lia)).
assert (E596 : ew Ev 596 = w64 (oz_a1 T Sg ai)) by exact (XA 33%nat ltac:(lia)).
assert (E597 : ew Ev 597 = w64 (oz_role T Sg ai)) by exact (XA 34%nat ltac:(lia)).
assert (E598 : ew Ev 598 = w64 (oz_din T Sg ai)) by exact (XA 35%nat ltac:(lia)).
assert (E599 : ew Ev 599 = w64 (oz_dout T Sg ai)) by exact (XA 36%nat ltac:(lia)).
assert (E600 : ew Ev 600 = w64 (oz_hd T Sg ai)) by exact (XA 37%nat ltac:(lia)).
assert (E601 : ew Ev 601 = w64 (oz_slots T Sg ai)) by exact (XA 38%nat ltac:(lia)).
assert (E602 : ew Ev 602 = w64 (oz_fam T Sg ai)) by exact (XA 39%nat ltac:(lia)).
assert (E603 : ew Ev 603 = w64 (oz_ch T Sg ai)) by exact (XA 40%nat ltac:(lia)).
assert (E604 : ew Ev 604 = w64 (oz_own T ai ow)) by exact (XA 41%nat ltac:(lia)).
clearbody Ev.
assert (UA : bv_unsigned (ew Ev 60) = d_A cx)
  by (destruct HdE' as (_ & _ & _ & E60 & _); change AT_A with 60%nat in E60; rewrite E60; apply unsigned_lit_small; lia).
assert (UA576 : U Ev (SOff 576 0) = role_of_e T ai).
{ rewrite (U_atom Ev 576 _ E576 (oy_u64_rng _)). rewrite oz_oldv by lia. apply oy_u64_small. lia. }
assert (US588 : U Ev (SExt true 32 (SOff 588 0)) = s_role Sg).
{ rewrite (oz_sx32u Ev 588 _ E588 (HuSg4 8)).
  change (bv_swrap 32 (u_at Sg 8 4)) with (s_role Sg). apply Z.mod_small. lia. }
assert (U589 : U Ev (SExt false 8 (SOff 589 0)) = s_hd Sg) by exact (oz_zx8 Ev 589 _ E589 (HuSg1 12)).
assert (U592 : U Ev (SExt false 8 (SOff 592 0)) = s_fam Sg) by exact (oz_zx8 Ev 592 _ E592 (HuSg1 15)).
assert (U593 : U Ev (SExt false 8 (SOff 593 0)) = s_slots Sg) by exact (oz_zx8 Ev 593 _ E593 (HuSg1 16)).
assert (U587 : U Ev (SOff 587 0) = ow)
  by (rewrite (U_atom Ev 587 _ E587 (oy_u64_rng _)); apply oy_u64_small; lia).
assert (U582 : U Ev (SOff 582 0) = bv_swrap 32 (reac_disco_table_observe_c.ch_of T ai) mod 2 ^ 64).
{ rewrite (oz_u_mod Ev 582 _ E582). rewrite oz_oldv by lia. unfold u64. rewrite Z.mod_mod by lia. reflexivity. }
assert (U594 : U Ev (SExt true 32 (SOff 594 0)) = bv_swrap 32 (s_ch Sg) mod 2 ^ 64)
  by exact (oz_sx32u Ev 594 _ E594 (HuSg4 20)).
assert (U595 : U Ev (SExt true 32 (SOff 595 0)) = n_of T).
{ rewrite (oz_sx32u Ev 595 _ E595 (HuTp4 384)). change (bv_swrap 32 (u_at T' 384 4)) with (n_of T').
  rewrite Hnof. apply Z.mod_small. lia. }
assert (U556 : U Ev (SOff 556 0) = n_of T) by (apply (U_atom Ev 556 _ E556); lia).
assert (U567 : U Ev (SOff 567 0) = dnot (d_obj cx OT))
  by (rewrite (U_atom Ev 567 _ E567 (oy_u64_rng _)); apply oy_u64_small; unfold dnot; lia).
assert (U585 : U Ev (SOff 585 0) = 16 * ai)
  by (rewrite (U_atom Ev 585 _ E585 (oy_u64_rng _)); apply oy_u64_small; lia).
assert (U586 : U Ev (SOff 586 0) = 64 * ai)
  by (rewrite (U_atom Ev 586 _ E586 (oy_u64_rng _)); apply oy_u64_small; lia).
assert (Hr_a1 : 0 <= oz_a1 T Sg ai <= 2)
  by (unfold oz_a1; destruct ((role_of_e T ai =? 1) && (s_role Sg =? 2)); lia).
assert (U596 : U Ev (SOff 596 0) = oz_a1 T Sg ai) by (apply (U_atom Ev 596 _ E596); lia).
assert (HhdR : 0 <= hd_of T ai < 256) by (unfold hd_of; apply HuT1).
assert (HdinR : 0 <= din_of T ai < 256) by (unfold din_of; apply HuT1).
assert (HdoutR : 0 <= dout_of T ai < 256) by (unfold dout_of; apply HuT1).
assert (HfamR : 0 <= reac_disco_table_observe_c.fam_of T ai < 256)
  by (unfold reac_disco_table_observe_c.fam_of; apply HuT1).
assert (HslotsR : 0 <= reac_disco_table_observe_c.slots_of T ai < 256)
  by (unfold reac_disco_table_observe_c.slots_of; apply HuT1).
assert (HchR : 0 <= reac_disco_table_observe_c.ch_of T ai < 2 ^ 32)
  by (unfold reac_disco_table_observe_c.ch_of; apply HuT4).
assert (HscR : 0 <= s_ch Sg < 2 ^ 32) by (unfold s_ch; apply HuSg4).
assert (U26 : U Ev (SAlu ALU_ADD (SMd M_MUL (SOff 585 0) (SLit (-1))) (SOff 586 0)) = 48 * ai).
{ rewrite U_SAlu, U_SMd, U_SLit, U585, U586.
  assert (Hc8 : ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
  repeat (destruct Hc8 as [Hz|Hc8]; [rewrite Hz; vm_compute; reflexivity|]).
  rewrite Hc8. vm_compute. reflexivity. }
clear HACS HTCS HFACTS.
unfold ss_d in HS. ro_base HS 516%nat. ro_base HS 529%nat.
pose (RUN := paj_run (fx := fq) B LAWS).
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by (intros; reflexivity).
assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem3 a) by (intros a Hp; exact Hp).
unfold cfg_at. change (w64 (BASE + OB_C9)) with (Z_to_bv 64 (BASE + OB_C9)).
paj_run_tok RUN HS HJ SHOK OBspan.
{ oz_awr UA. }
oz_keep cx mem3 UA.
eapply (SRr_bind _ _ _ (oz_J fq cx ly3 S3 k mem3 Ev _ W)).
{ psrr_branch_tok RUN BR HS SHOK OBspan.
  - rewrite branch_ne_U, !U_SAlu, U_SLit, UA576, US588 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6348.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (11%bv : bv 5) (SOff 596 0).
    { rewrite !denot_lit_U. f_equal. rewrite !U_SAlu, U_SLit, US588, U596.
      destruct Hrole as [HR|[HR|HR]]; destruct HS1 as [HQ|[HQ|HQ]];
      rewrite ?HR, ?HQ in *; unfold oz_a1; rewrite ?HR, ?HQ;
      try (vm_compute in Hc; discriminate); vm_compute; reflexivity. }
    oz_fin.
  - rewrite branch_ne_U, !U_SAlu, U_SLit, UA576, US588 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6348.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (11%bv : bv 5) (SOff 596 0).
    { rewrite !denot_lit_U. f_equal. rewrite !U_SLit, U596.
      destruct Hrole as [HR|[HR|HR]]; destruct HS1 as [HQ|[HQ|HQ]];
      rewrite ?HR, ?HQ in *; unfold oz_a1; rewrite ?HR, ?HQ;
      try (vm_compute in Hc; discriminate); vm_compute; reflexivity. }
    oz_fin. }
cbv beta. intros W1 c1 _ (HW1 & msA & mdA & Hc1 & HS1a & HJ1 & MEQ1 & MPR1). subst W1. subst c1.
clear HS HJ SHOK MEQ MPR. rename HS1a into HS. rename HJ1 into HJ. rename MEQ1 into MEQ. rename MPR1 into MPR.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ev (rd W (ms_mem msA))) by constructor.
paj_run_tok RUN HS HJ SHOK OBspan.
{ oz_awr UA. }
oz_keep cx mem3 UA.
eapply (SRr_bind _ _ _ (oz_J fq cx ly3 S3 k mem3 Ev _ W)).
{ psrr_branch_tok RUN BR HS SHOK OBspan.
  - rewrite branch_eq_U, US588, oz_U0 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6368.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (16%bv : bv 5) (SOff 597 0).
    { rewrite (oz_dn_off Ev 576 _ E576), (oz_dn_off Ev 597 _ E597). f_equal.
      unfold oz_role. rewrite Hc. rewrite oz_oldv by lia. apply oy_u64_small. lia. }
    oz_fin.
  - rewrite branch_eq_U, US588, oz_U0 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6368.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (16%bv : bv 5) (SOff 597 0).
    { rewrite (oz_dn_off Ev 596 _ E596), (oz_dn_off Ev 597 _ E597). f_equal.
      unfold oz_role. rewrite Hc. reflexivity. }
    oz_fin. }
cbv beta. intros W2 c2 _ (HW2 & msB & mdB & Hc2 & HS2a & HJ2 & MEQ2 & MPR2). subst W2. subst c2.
clear HS HJ SHOK MEQ MPR. rename HS2a into HS. rename HJ2 into HJ. rename MEQ2 into MEQ. rename MPR2 into MPR.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ev (rd W (ms_mem msB))) by constructor.
paj_run_tok RUN HS HJ SHOK OBspan.
{ oz_awr UA. }
oz_keep cx mem3 UA.
eapply (SRr_bind _ _ _ (oz_J fq cx ly3 S3 k mem3 Ev _ W)).
{ psrr_branch_tok RUN BR HS SHOK OBspan.
  - rewrite branch_eq_U, U589, oz_U0 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6404.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (21%bv : bv 5) (SOff 598 0).
    { rewrite (oz_dn_off Ev 578 _ E578), (oz_dn_off Ev 598 _ E598). f_equal.
      unfold oz_din. rewrite Hc. rewrite oz_oldv by lia. apply oy_u64_small. lia. }
    oz_setreg Ev (14%bv : bv 5) (SOff 599 0).
    { rewrite (oz_dn_off Ev 579 _ E579), (oz_dn_off Ev 599 _ E599). f_equal.
      unfold oz_dout. rewrite Hc. rewrite oz_oldv by lia. apply oy_u64_small. lia. }
    oz_setreg Ev (24%bv : bv 5) (SOff 600 0).
    { rewrite (oz_dn_off Ev 577 _ E577), (oz_dn_off Ev 600 _ E600). f_equal.
      unfold oz_hd. rewrite Hc. rewrite oz_oldv by lia. apply oy_u64_small. lia. }
    oz_fin.
  - rewrite branch_eq_U, U589, oz_U0 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6404.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (21%bv : bv 5) (SOff 598 0).
    { rewrite (oz_dn_zx8 Ev 590 _ E590 (HuSg1 13)), (oz_dn_off Ev 598 _ E598). f_equal.
      unfold oz_din. rewrite Hc. reflexivity. }
    oz_setreg Ev (14%bv : bv 5) (SOff 599 0).
    { rewrite (oz_dn_zx8 Ev 591 _ E591 (HuSg1 14)), (oz_dn_off Ev 599 _ E599). f_equal.
      unfold oz_dout. rewrite Hc. reflexivity. }
    oz_setreg Ev (24%bv : bv 5) (SOff 600 0).
    { rewrite (oz_dn_off Ev 600 _ E600). cbn [sv_denot]. f_equal.
      unfold oz_hd. rewrite Hc. reflexivity. }
    oz_fin. }
cbv beta. intros W3 c3 _ (HW3 & msC & mdC & Hc3 & HS3a & HJ3 & MEQ3 & MPR3). subst W3. subst c3.
clear HS HJ SHOK MEQ MPR. rename HS3a into HS. rename HJ3 into HJ. rename MEQ3 into MEQ. rename MPR3 into MPR.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ev (rd W (ms_mem msC))) by constructor.
paj_run_tok RUN HS HJ SHOK OBspan.
{ oz_awr UA. }
oz_keep cx mem3 UA.
eapply (SRr_bind _ _ _ (oz_J fq cx ly3 S3 k mem3 Ev _ W)).
{ psrr_branch_tok RUN BR HS SHOK OBspan.
  - rewrite branch_eq_U, U593, oz_U0 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6420.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (5%bv : bv 5) (SOff 601 0).
    { rewrite (oz_dn_off Ev 581 _ E581), (oz_dn_off Ev 601 _ E601). f_equal.
      unfold oz_slots. rewrite Hc. rewrite oz_oldv by lia. apply oy_u64_small. lia. }
    oz_fin.
  - rewrite branch_eq_U, U593, oz_U0 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6420.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (5%bv : bv 5) (SOff 601 0).
    { rewrite (oz_dn_add0 Ev _ _ (oz_dn_zx8 Ev 593 _ E593 (HuSg1 16))), (oz_dn_off Ev 601 _ E601). f_equal.
      unfold oz_slots. rewrite Hc. reflexivity. }
    oz_fin. }
cbv beta. intros W4 c4 _ (HW4 & msD & mdD & Hc4 & HS4a & HJ4 & MEQ4 & MPR4). subst W4. subst c4.
clear HS HJ SHOK MEQ MPR. rename HS4a into HS. rename HJ4 into HJ. rename MEQ4 into MEQ. rename MPR4 into MPR.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ev (rd W (ms_mem msD))) by constructor.
paj_run_tok RUN HS HJ SHOK OBspan.
{ oz_awr UA. }
oz_keep cx mem3 UA.
eapply (SRr_bind _ _ _ (oz_J fq cx ly3 S3 k mem3 Ev _ W)).
{ psrr_branch_tok RUN BR HS SHOK OBspan.
  - rewrite branch_eq_U, U592, oz_U0 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6440.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (22%bv : bv 5) (SOff 602 0).
    { rewrite (oz_dn_off Ev 580 _ E580), (oz_dn_off Ev 602 _ E602). f_equal.
      unfold oz_fam. rewrite Hc. rewrite oz_oldv by lia. apply oy_u64_small. lia. }
    oz_fin.
  - rewrite branch_eq_U, U592, oz_U0 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6440.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (22%bv : bv 5) (SOff 602 0).
    { rewrite (oz_dn_add0 Ev _ _ (oz_dn_zx8 Ev 592 _ E592 (HuSg1 15))), (oz_dn_off Ev 602 _ E602). f_equal.
      unfold oz_fam. rewrite Hc. reflexivity. }
    oz_fin. }
cbv beta. intros W5 c5 _ (HW5 & msE & mdE & Hc5 & HS5a & HJ5 & MEQ5 & MPR5). subst W5. subst c5.
clear HS HJ SHOK MEQ MPR. rename HS5a into HS. rename HJ5 into HJ. rename MEQ5 into MEQ. rename MPR5 into MPR.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ev (rd W (ms_mem msE))) by constructor.
paj_run_tok RUN HS HJ SHOK OBspan.
{ oz_awr UA. }
oz_keep cx mem3 UA.
eapply (SRr_bind _ _ _ (oz_J fq cx ly3 S3 k mem3 Ev _ W)).
{ psrr_branch_tok RUN BR HS SHOK OBspan.
  - rewrite branch_ltu_U, U582, U594 in Hc. rewrite (oz_sx_ltu _ _ HchR HscR) in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6464.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (7%bv : bv 5) (SOff 603 0).
    { rewrite (oz_dn_add0 Ev _ _ (oz_dn_sx32 Ev 594 _ E594 (HuSg4 20))), (oz_dn_off Ev 603 _ E603). f_equal.
      unfold oz_ch. rewrite Hc. reflexivity. }
    oz_fin.
  - rewrite branch_ltu_U, U582, U594 in Hc. rewrite (oz_sx_ltu _ _ HchR HscR) in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6464.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (7%bv : bv 5) (SOff 603 0).
    { rewrite (oz_dn_off Ev 582 _ E582), (oz_dn_off Ev 603 _ E603).
      rewrite oz_oldv by lia. rewrite oz_w64_u64. f_equal.
      unfold oz_ch. rewrite Hc. reflexivity. }
    oz_fin. }
cbv beta. intros W6 c6 _ (HW6 & msF & mdF & Hc6 & HS6a & HJ6 & MEQ6 & MPR6). subst W6. subst c6.
clear HS HJ SHOK MEQ MPR. rename HS6a into HS. rename HJ6 into HJ. rename MEQ6 into MEQ. rename MPR6 into MPR.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ev (rd W (ms_mem msF))) by constructor.
paj_run_tok RUN HS HJ SHOK OBspan.
{ oz_awr UA. }
oz_keep cx mem3 UA.
eapply (SRr_bind _ _ _ (oz_J fq cx ly3 S3 k mem3 Ev _ W)).
{ psrr_branch_tok RUN BR HS SHOK OBspan.
  - rewrite branch_eq_U, U587, oz_U0 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6484.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (7%bv : bv 5) (SOff 604 0).
    { rewrite (oz_dn_off Ev 583 _ E583), (oz_dn_off Ev 604 _ E604). f_equal.
      unfold oz_own. rewrite Hc. rewrite oz_oldv by lia. reflexivity. }
    oz_fin.
  - rewrite branch_eq_U, U587, oz_U0 in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6484.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    norm_ss HS. apply oz_drop_cond in HS.
    oz_setreg Ev (7%bv : bv 5) (SOff 604 0).
    { rewrite (oz_dn_off Ev 604 _ E604). cbn [sv_denot]. f_equal.
      unfold oz_own. rewrite Hc. reflexivity. }
    oz_fin. }
cbv beta. intros W7 c7 _ (HW7 & msG & mdG & Hc7 & HS7a & HJ7 & MEQ7 & MPR7). subst W7. subst c7.
clear HS HJ SHOK MEQ MPR. rename HS7a into HS. rename HJ7 into HJ. rename MEQ7 into MEQ. rename MPR7 into MPR.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ev (rd W (ms_mem msG))) by constructor.
paj_run_tok RUN HS HJ SHOK OBspan.
{ oz_awr UA. }
oz_keep cx mem3 UA.
psrr_branch_tok RUN BR HS SHOK OBspan.
- exfalso. rewrite branch_ltu_U, U567, U26 in Hc.
  apply Z.ltb_lt in Hc. unfold dnot, d_obj, dobj_off in Hc. lia.
- clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 6500.
    { oz_awr UA. }
    oz_keep cx mem3 UA.
    lazymatch goal with HSc : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into mC end.
    pose proof (st_ok_pi_region_nth Ev _ _ 1%nat _ HS eq_refl) as RA.
    cbn [ms_mem restrict] in RA.
    assert (HFLr : 0 <= flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx) < 2 ^ 64)
      by exact (oy_rdword_aview_range SEGS _ _ _ _ Hflag).
    assert (L184 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 184) 8 h)
      by (apply (proj2 (oz_vm_u64 _ _ h)); oz_fld RA UA (oz_dn_off Ev 563 _ E563)).
    assert (L120 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 120) 8 (h + 440))
      by (apply (proj2 (oz_vm_u64 _ _ (h + 440))); oz_fld RA UA (oz_dn_off Ev 564 _ E564)).
    assert (L136 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 136) 8 0)
      by (apply (proj2 (oz_vm_u64 _ _ 0)); oz_fld RA UA (oz_dn_off Ev 565 _ E565)).
    assert (L376 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 376) 8 (dnot (d_obj cx OG)))
      by (apply (proj2 (oz_vm_u64 _ _ (dnot (d_obj cx OG)))); oz_fld RA UA (oz_dn_off Ev 566 _ E566)).
    assert (L280 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 280) 8 (dnot (d_obj cx OT)))
      by (apply (proj2 (oz_vm_u64 _ _ (dnot (d_obj cx OT)))); oz_fld RA UA (oz_dn_off Ev 567 _ E567)).
    assert (L232 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 232) 8 (dnot (d_obj cx OO)))
      by (apply (proj2 (oz_vm_u64 _ _ (dnot (d_obj cx OO)))); oz_fld RA UA (oz_dn_off Ev 568 _ E568)).
    assert (L264 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 264) 8 (dnot (d_obj cx OUSED)))
      by (apply (proj2 (oz_vm_u64 _ _ (dnot (d_obj cx OUSED)))); oz_fld RA UA (oz_dn_off Ev 569 _ E569)).
    assert (L208 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 208) 8 i)
      by (apply (proj2 (oz_vm_u64 _ _ i)); oz_fld RA UA (oz_dn_off Ev 570 _ E570)).
    assert (L320 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 320) 8 now)
      by (apply (proj2 (oz_vm_u64 _ _ now)); oz_fld RA UA (oz_dn_off Ev 571 _ E571)).
    assert (L200 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 200) 8 (d_cur cx nb))
      by (apply (proj2 (oz_vm_u64 _ _ (d_cur cx nb))); oz_fld RA UA (oz_dn_off Ev 572 _ E572)).
    assert (L328 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 328) 8 nb)
      by (apply (proj2 (oz_vm_u64 _ _ nb)); oz_fld RA UA (oz_dn_off Ev 573 _ E573)).
    assert (L368 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 368) 8 fr)
      by (apply (proj2 (oz_vm_u64 _ _ fr)); oz_fld RA UA (oz_dn_off Ev 574 _ E574)).
    assert (L408 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 408) 8 len)
      by (apply (proj2 (oz_vm_u64 _ _ len)); oz_fld RA UA (oz_dn_off Ev 575 _ E575)).
    assert (P64 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 64) 8 (u64 (16 * ai)))
      by (oz_fld RA UA (oz_dn_off Ev 585 _ E585)).
    assert (P56 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 56) 8 (u64 (64 * ai)))
      by (oz_fld RA UA (oz_dn_off Ev 586 _ E586)).
    assert (P352 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 352) 8 (u64 (oldv ai (role_of_e T ai))))
      by (oz_fld RA UA (oz_dn_off Ev 576 _ E576)).
    assert (P192 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 192) 8 (u64 (oldv ai (hd_of T ai))))
      by (oz_fld RA UA (oz_dn_off Ev 577 _ E577)).
    assert (P104 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 104) 8 (u64 (oldv ai (din_of T ai))))
      by (oz_fld RA UA (oz_dn_off Ev 578 _ E578)).
    assert (P96 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 96) 8 (u64 (oldv ai (dout_of T ai))))
      by (oz_fld RA UA (oz_dn_off Ev 579 _ E579)).
    assert (P88 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 88) 8
      (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai))))
      by (oz_fld RA UA (oz_dn_off Ev 580 _ E580)).
    assert (P80 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 80) 8
      (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai))))
      by (oz_fld RA UA (oz_dn_off Ev 581 _ E581)).
    assert (P296 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 296) 8 (u64 (oldv ai (s32_at T (48 * ai + 20)))))
      by (oz_fld RA UA (oz_dn_off Ev 582 _ E582)).
    assert (P72 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 72) 8 (u64 (oldv ai (owned_of T ai))))
      by (oz_fld RA UA (oz_dn_off Ev 583 _ E583)).
    assert (P48 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 48) 8 (u64 (oldv ai (u_at T (48 * ai + 32) 8))))
      by (oz_fld RA UA (oz_dn_off Ev 584 _ E584)).
    assert (P360 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 360) 8 ow)
      by (apply (proj2 (oz_vm_u64 _ _ ow)); oz_fld RA UA (oz_dn_off Ev 587 _ E587)).
    assert (P8 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 8) 8 (oz_ch T Sg ai)).
    { apply (proj2 (oz_vm_u64 _ _ (oz_ch T Sg ai))).
      oz_fld RA UA (eq_trans (oz_dn_off Ev 603 _ E603) (eq_sym (oz_w64_u64 (oz_ch T Sg ai)))). }
    assert (P0 : val_mem SEGS (rd W (ms_mem mC)) (d_A cx + 0) 8 (bv_swrap 32 (s_ch Sg))).
    { apply (proj2 (oz_vm_u64 _ _ (bv_swrap 32 (s_ch Sg)))).
      oz_fld RA UA (eq_trans (oz_dn_sx32 Ev 594 _ E594 (HuSg4 20)) (eq_sym (oz_w64_u64 (bv_swrap 32 (s_ch Sg))))). }
    destruct (oy_land B MT XM_LIB RLO RHI tfib_K fq cx h dsh_rec ly3 S3 W _ k Ev _ mC LAWS
      (conj Hbase (conj HJ Hfrs)) HdE' HFL' HFLr HS ltac:(vm_compute; reflexivity)
      L184 L120 L136 L376 L280 L232 L264) as (FrC & ShC).
    assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs mC) r = getr regs r).
    { intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W) Ev _ mC r HS), (HROK r).
      cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
    oz_reg HS (26%bv : bv 5) Q26. oz_reg HS (16%bv : bv 5) Q16. oz_reg HS (24%bv : bv 5) Q24.
    oz_reg HS (21%bv : bv 5) Q21. oz_reg HS (14%bv : bv 5) Q14. oz_reg HS (5%bv : bv 5) Q5.
    oz_reg HS (22%bv : bv 5) Q22. oz_reg HS (7%bv : bv 5) Q7. oz_reg HS (25%bv : bv 5) Q25.
    oz_reg HS (23%bv : bv 5) Q23.
    assert (GT' : garr8 SEGS (rd W (ms_mem mC)) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T')).
    { apply (oy_garr8_keep W W mem3 (ms_mem mC)); [|exact HT].
      intros j Hj. rewrite length_map, HTl in Hj. apply MEQ; unfold d_obj, dobj_off, LLVMF_STK in *; lia. }
    assert (GS' : garr8 SEGS (rd W (ms_mem mC)) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg)).
    { apply (oy_garr8_keep W W mem3 (ms_mem mC)); [|exact HSg].
      intros j Hj. rewrite length_map, HSgl in Hj. apply MEQ; unfold d_obj, dobj_off, LLVMF_STK in *; lia. }
    assert (Hbody2 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem mC)).
    { apply (BRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem mC) (d_A cx) (d_A cx + 472)
        (fun a => d_A cx <= a < d_A cx + 472) Hbody);
      [ unfold LLVMF_STK in *; lia | lia | intros a Ha; left; exact Ha | exact MEQ
      | intros a _ Hp; apply MPR; exact Hp | exact FrC | exact ShC | lia ]. }
    assert (Hfrm2 : d_frm cx nb fr len W (ms_mem mC)).
    { split; [exact F1|]. split; [exact F2|]. split; [exact F0|].
      destruct (Z.eq_dec fr 0) as [Ez|Ez].
      - rewrite (F2 Ez). exact (garr8_nil SEGS _ _).
      - pose proof Hbody as (_ & _ & _ & _ & _ & _ & _ & Hblocks & _).
        assert (Hin : In (fr, len) (ablocks B ly3 S3)).
        { destruct Hblocks as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)). unfold dxb.
          rewrite (proj2 (Z.eqb_neq fr 0) Ez). left. reflexivity. }
        destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len GAR Hin) as (_ & Hfr4 & Hfrc & _).
        assert (Hrq : len <= req_size len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
        apply (oy_garr8_keep W W mem3 (ms_mem mC)); [|exact F3].
        intros j Hj. rewrite length_map, length_firstn in Hj. apply MEQ; unfold LLVMF_STK in *; lia. }
    pmkst HS.
    apply SRr_ret.
    apply (oy_dat B MT XM_LIB RLO RHI tfib_K cx OB_C9M kmax accmax _ fq ly3 S3 (ms_regs mC) (ms_mem mC) _ k acc W
      MT_TRIV HFRM0 (conj Hbase (conj HJ Hfrs)) Hk Hacc).
    exists T, T', ai, ow, ret.
    split.
    { split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
      split.
      { destruct HrL as (Hsp & Hgp & Htp & H8r & H9r & H19r & H18r & H20r & H27r). unfold d_rL, spZ in *.
        rewrite (RG 2%bv ltac:(cbv; tauto)), (RG 3%bv ltac:(cbv; tauto)), (RG 4%bv ltac:(cbv; tauto)),
          (RG 8%bv ltac:(cbv; tauto)), (RG 9%bv ltac:(cbv; tauto)), (RG 18%bv ltac:(cbv; tauto)),
          (RG 19%bv ltac:(cbv; tauto)), (RG 20%bv ltac:(cbv; tauto)), (RG 27%bv ltac:(cbv; tauto)).
        repeat split; assumption. }
      split; [exact (conj L208 L320)|].
      split; [exact Hfrm2|]. split; [exact HSgl|]. split; [exact GS'|]. split; [exact HSf|].
      split; [exact (conj L200 (conj L328 (conj L368 L408)))|].
      split; [exact Hlen|]. split; [exact Hnb|]. split; [exact HTl|]. split; [exact GT'|].
      split; [exact HTok | exact Hbody2]. }
    split.
    { split; [exact LT|]. split; [exact TOK|]. split; [exact HFR|]. split; [exact How|].
      split.
      { unfold ob_sp22. split; [exact P64|]. split; [exact P56|]. split; [exact P352|]. split; [exact P192|].
        split; [exact P104|]. split; [exact P96|]. split; [exact P88|]. split; [exact P80|].
        split; [exact P296|]. split; [exact P72 | exact P48]. }
      split; [exact P360 | exact HOM]. }
    split; [exact Hain|].
    split; [unfold oz_ch in P8; exact P8|].
    split; [exact P0|].
    unfold ob_r9m.
    split.
    { rewrite Q26, denot_lit_U, U26. reflexivity. }
    split; [rewrite Q16, (oz_dn_off Ev 597 _ E597); unfold oz_role, oz_a1; reflexivity|].
    split; [rewrite Q24, (oz_dn_off Ev 600 _ E600); unfold oz_hd; reflexivity|].
    split; [rewrite Q21, (oz_dn_off Ev 598 _ E598); unfold oz_din; reflexivity|].
    split; [rewrite Q14, (oz_dn_off Ev 599 _ E599); unfold oz_dout; reflexivity|].
    split; [rewrite Q5, (oz_dn_off Ev 601 _ E601); unfold oz_slots; reflexivity|].
    split; [rewrite Q22, (oz_dn_off Ev 602 _ E602); unfold oz_fam; reflexivity|].
    split; [rewrite Q7, (oz_dn_off Ev 604 _ E604); unfold oz_own; reflexivity|].
    split; [rewrite Q25, (oz_dn_off Ev 556 _ E556); reflexivity|].
    rewrite Q23, (oz_dn_off Ev 554 _ E554). reflexivity.
Qed.
End h.
End f.
End d.
