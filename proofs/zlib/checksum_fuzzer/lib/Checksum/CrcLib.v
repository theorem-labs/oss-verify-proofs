(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Export CrcAlgebra.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_nonneg : forall bs : list byte, (0 <= bytes_le_to_Z bs)%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. apply Z.shiftl_nonneg. exact IH.
Qed.

Lemma bytes_le_to_Z_bound : forall bs : list byte, (bytes_le_to_Z bs < 256 ^ Z.of_nat (length bs))%Z.
Proof.
  intros bs. rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as H. rewrite length_map in H. lia.
Qed.

Lemma Z_to_le_bytes_roundtrip : forall bs : list byte,
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
    Z.div_mod_to_equations. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8)%Z with 256%Z.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256)%Z with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le4, le_bytes_to_word.
  pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1. rewrite Hl in H1.
  change (256 ^ Z.of_nat 4)%Z with 4294967296%Z in H1.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  rewrite Z.mod_small by lia. rewrite <- Hl. apply Z_to_le_bytes_roundtrip.
Qed.

Lemma land255_mod : forall x, Z.land x 255 = (x mod 256)%Z.
Proof. intros x. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land255_range : forall x, (0 <= Z.land x 255 <= 255)%Z.
Proof. intros x. rewrite land255_mod. pose proof (Z.mod_pos_bound x 256). lia. Qed.

Lemma land31_mod : forall x, Z.land x 31 = (x mod 32)%Z.
Proof. intros x. change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land31_range : forall x, (0 <= Z.land x 31 <= 31)%Z.
Proof. intros x. rewrite land31_mod. pose proof (Z.mod_pos_bound x 32). lia. Qed.

(* [comment removed for export] *)
Definition DIV20_MAGIC : Z := 0xCCCCCCCCCCCCCCCD.
Lemma div20_magic : forall x, (0 <= x < 2^64)%Z ->
  (x * DIV20_MAGIC / 2^64 / 2^4 = x / 20)%Z.
Proof.
  intros x Hx. unfold DIV20_MAGIC.
  rewrite Z.div_div by lia. change (2^64 * 2^4)%Z with (2^68)%Z.
  remember (x / 20)%Z as q eqn:Eq. remember (x mod 20)%Z as r eqn:Er.
  assert (Hx' : (x = 20 * q + r)%Z) by (subst; apply Z.div_mod; lia).
  assert (Hr : (0 <= r < 20)%Z) by (subst r; apply Z.mod_pos_bound; lia).
  assert (Hq : (0 <= q <= 922337203685477580)%Z) by lia.
  rewrite Hx'.
  replace ((20 * q + r) * 14757395258967641293)%Z with ((4 * q + r * 14757395258967641293) + q * 2^68)%Z by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small (4 * q + r * 14757395258967641293)%Z) by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bword4 (bs : list byte) (k : Z) : word := le_bytes_to_word (firstn 4 (skipn (Z.to_nat k) bs)).
Definition bbyte (bs : list byte) (k : Z) : byte := nth (Z.to_nat k) bs (Z_to_bv 8 0).

Section WithSegs.
  Variable segs : list Segment.

  Lemma rd1_at : forall m A bs (k : Z) a,
    bytes_at segs m A bs -> (0 <= k)%Z -> (k < Z.of_nat (length bs))%Z -> a = wa (A + k) ->
    ov_read_bytes segs m a 1 = Some [bbyte bs k].
  Proof.
    intros m A bs k a Hb Hk Hk' ->.
    destruct (nth_error bs (Z.to_nat k)) as [b|] eqn:E.
    2:{ apply nth_error_None in E. lia. }
    rewrite (u8ro_read segs m A bs k b _ Hb E Hk eq_refl). unfold bbyte.
    rewrite (nth_error_nth _ _ _ E). reflexivity.
  Qed.

  Lemma rd4_at : forall m A bs (k : Z) a,
    bytes_at segs m A bs -> (0 <= k)%Z -> (k + 4 <= Z.of_nat (length bs))%Z -> a = wa (A + k) ->
    ov_read_bytes segs m a 4 = Some (le4 (bword4 bs k)).
  Proof.
    intros m A bs k a Hb Hk Hk' ->. unfold bword4.
    rewrite (bytes_at_read segs m A bs k 4 Hb Hk) by lia.
    f_equal. symmetry. apply le4_of_bytes. rewrite firstn_length, skipn_length. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ro_table_at : forall m A bs,
    mem_inv segs m -> ro_bytes_b segs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
    bytes_at segs m A bs.
  Proof.
    intros m A bs MI RO HA HB. apply ro_bytes_at; try assumption. apply ro_bytes_b_sound. exact RO.
  Qed.
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac crc_arith_prep :=
  repeat match goal with |- context [Z.shiftl ?x 2] => rewrite (Z.shiftl_mul_pow2 x 2) by lia end;
  change (2^2)%Z with 4%Z;
  repeat match goal with |- context [Z.land ?x 255] =>
    pose proof (land255_range x); let ix := fresh "ix" in set (ix := Z.land x 255) in *; clearbody ix end;
  repeat match goal with |- context [Z.land ?x 31] =>
    pose proof (land31_range x); let ix := fresh "ix" in set (ix := Z.land x 31) in *; clearbody ix end.
Ltac crc_lia := crc_arith_prep; first [lia | Z.div_mod_to_equations; lia].

Ltac solve_load_sym :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      let E := addr_expr a in
      match goal with
      | H : bytes_at segs m ?A ?bs |- _ =>
          lazymatch n with
          | 4%nat => rewrite (rd4_at segs m A bs (E - A)%Z a H) by (first [crc_lia | addr_eq_tac])
          | 1%nat => rewrite (rd1_at segs m A bs (E - A)%Z a H) by (first [crc_lia | addr_eq_tac])
          end
      end
  end; load_post.

Ltac solve_load ::= first [ solve_load_base | solve_load_image | solve_load_sym ].

Ltac gen_loads :=
  repeat match goal with
  | |- context [bword4 ?t ?k] => let w := fresh "w" in set (w := bword4 t k) in |- *; clearbody w
  | |- context [bbyte ?t ?k] => let b := fresh "b" in set (b := bbyte t k) in |- *; clearbody b
  end.

(* [comment removed for export] *)
Ltac cstep := zstep; gen_loads.

(* [comment removed for export] *)
Ltac lit_branch :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      lazymatch c with
      | context [bv_eqb (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => is_Zlit_zb a; is_Zlit_zb b; first [if_true | if_false]
      | context [bv_ltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => is_Zlit_zb a; is_Zlit_zb b; first [if_true | if_false]
      | _ => idtac
      end
  | _ => idtac
  end.
Ltac bstep := cstep; lit_branch.

(* [comment removed for export] *)
Ltac gen_lxor :=
  repeat match goal with
  | |- context [Z_to_bv 64 (Z.lxor ?x ?y)] => let w := fresh "acc" in set (w := Z_to_bv 64 (Z.lxor x y)) in |- *; clearbody w
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac unfold_swrap32 :=
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z; change (4294967296 / 2)%Z with 2147483648%Z.
(* [comment removed for export] *)
Lemma swrap32_SX : forall c, (0 <= c < 2^32)%Z -> (bv_swrap 32 c mod 18446744073709551616)%Z = SX c.
Proof.
  intros c Hc. unfold SX, HI32. unfold_swrap32. change (2^31)%Z with 2147483648%Z.
  destruct (Z.ltb_spec c 2147483648); Z.div_mod_to_equations; lia.
Qed.
Lemma srliw1_SX : forall b, (0 <= b < 2^32)%Z -> bv_swrap 32 (Z.shiftr (bv_wrap 32 (SX b)) 1) = Z.shiftr b 1.
Proof.
  intros b Hb. unfold bv_wrap. change (bv_modulus 32) with (2^32)%Z. rewrite SX_mod32 by lia.
  pose proof (shiftr1_bound 31 b ltac:(change (31+1)%Z with 32%Z; lia) ltac:(lia)).
  unfold_swrap32. change (2^31)%Z with 2147483648%Z in H.
  rewrite Z.mod_small; lia.
Qed.
Lemma addiw_m1_SX : forall m, (1 <= m <= 2^31)%Z -> bv_swrap 32 (SX m + -1) = (m - 1)%Z.
Proof.
  intros m Hm. unfold_swrap32. change (2^31)%Z with 2147483648%Z in Hm.
  unfold SX, HI32. change (2^31)%Z with 2147483648%Z. destruct (Z.ltb_spec m 2147483648); Z.div_mod_to_equations; lia.
Qed.
Lemma SX_odd : forall b, (0 <= b < 2^32)%Z -> Z.odd (SX b) = Z.odd b.
Proof. intros b Hb. rewrite <- !Z.bit0_odd. rewrite SX_testbit by lia. reflexivity. Qed.

Lemma SX_POLY : SX POLY = 18446744073402876704%Z.
Proof. reflexivity. Qed.

Lemma signmask_SX : forall b, (0 <= b < 2^32)%Z ->
  Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (SX b) 63))) 63 mod 18446744073709551616) 18446744073402876704
  = if Z.odd b then 18446744073402876704%Z else 0%Z.
Proof.
  intros b Hb. change 18446744073709551616%Z with (2^64)%Z. rewrite zb_signed.
  rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (SX_range b Hb) as R.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  rewrite <- (SX_odd b Hb).
  set (s := SX b) in *. clearbody s.
  pose proof (Zmod_odd s) as Hm2.
  destruct (Z.odd s).
  - replace (s * 2^63)%Z with (2^63 + (s / 2) * 2^64)%Z by (Z.div_mod_to_equations; lia).
    rewrite Z.mod_add by lia. vm_compute. reflexivity.
  - replace (s * 2^63)%Z with (0 + (s / 2) * 2^64)%Z by (Z.div_mod_to_equations; lia).
    rewrite Z.mod_add by lia. vm_compute. reflexivity.
Qed.

Lemma bstep_SX : forall b, (0 <= b < 2^32)%Z ->
  Z.lxor (Z.shiftr b 1) (if Z.odd b then 18446744073402876704%Z else 0%Z) = SX (cstep b).
Proof.
  intros b Hb. rewrite <- SX_POLY. unfold cstep.
  pose proof (shiftr1_bound 31 b ltac:(change (31+1)%Z with 32%Z; lia) ltac:(lia)).
  destruct (Z.odd b).
  - apply lxor_small_SX; [lia|]. pose proof POLY_range. lia.
  - rewrite !Z.lxor_0_r. symmetry. apply SX_small. lia.
Qed.

Lemma land_small_SX : forall a b, (0 <= a < 2^31)%Z -> (0 <= b < 2^32)%Z -> Z.land a (SX b) = Z.land a b.
Proof.
  intros a b Ha Hb. rewrite <- (SX_small a Ha) at 1. rewrite land_SX by lia.
  apply SX_small. pose proof (land_bound_l 31 a b Ha ltac:(lia)). lia.
Qed.
Lemma sx32_SX : forall (w : word) c, bv_unsigned w = c -> (0 <= c < 2^32)%Z -> sx32 w = Z_to_bv 64 (SX c).
Proof.
  intros w c Hw Hc. unfold sx32. rewrite Hw. apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z.
  rewrite swrap32_SX by lia. symmetry. apply Z.mod_small. apply SX_range. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition X2N_TAB : Z := 0x11954.
Definition x2n_bytes : list byte := flat_map (fun z => le4 (Z_to_bv 64 z)) x2n_tab.

Lemma flat4_chunk : forall (ws : list Z) i, (i < length ws)%nat ->
  firstn 4 (skipn (4 * i) (flat_map (fun z => le4 (Z_to_bv 64 z)) ws)) = le4 (Z_to_bv 64 (nth i ws 0%Z)).
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  cbn [flat_map nth]. destruct i as [|i].
  - rewrite Nat.mul_0_r. rewrite skipn_O.
    rewrite firstn_app. rewrite length_le4, Nat.sub_diag. rewrite firstn_O. rewrite app_nil_r.
    apply firstn_all2. rewrite length_le4; lia.
  - replace (4 * S i)%nat with (length (le4 (Z_to_bv 64 w)) + 4 * i)%nat by (rewrite length_le4; lia).
    rewrite skipn_app. rewrite Nat.add_comm, Nat.add_sub, skipn_all2 by lia. cbn [app].
    apply IH. lia.
Qed.

Lemma x2n_bytes_length : length x2n_bytes = 128%nat.
Proof. reflexivity. Qed.

Section X2N.
  Variable segs : list Segment.
  Lemma rd_x2n : forall m (k : Z) a,
    bytes_at segs m X2N_TAB x2n_bytes ->
    a = wa (X2N_TAB + Z.shiftl (Z.land k 31) 2) ->
    ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (tabz (Z.to_nat (Z.land k 31))))).
  Proof.
    intros m k a Hb ->. pose proof (land31_range k) as R.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^2)%Z with 4%Z.
    rewrite (bytes_at_read segs m X2N_TAB x2n_bytes (Z.land k 31 * 4) 4 Hb) by (try rewrite x2n_bytes_length; lia).
    f_equal. unfold x2n_bytes, tabz.
    replace (Z.to_nat (Z.land k 31 * 4)) with (4 * Z.to_nat (Z.land k 31))%nat by lia.
    apply flat4_chunk. cbn [length x2n_tab]. lia.
  Qed.

  Lemma tabz_word : forall i, (i < 32)%nat -> bv_unsigned (Z_to_bv 64 (tabz i)) = tabz i.
  Proof. intros i Hi. pose proof (tabz_range i Hi). apply unsigned_lit. lia. Qed.
End X2N.

Lemma shr1_mod64 : forall b, (0 <= b < 2^32)%Z -> (Z.shiftr b 1 mod 18446744073709551616)%Z = Z.shiftr b 1.
Proof.
  intros b Hb. pose proof (shiftr1_bound 31 b ltac:(change (31+1)%Z with 32%Z; lia) ltac:(lia)). apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_pow2_zero : forall a k, (0 <= k)%Z -> Z.land (2^k) a = 0%Z -> Z.testbit a k = false.
Proof. intros a k Hk H. pose proof (land_pow2_testbit a k Hk) as E. rewrite H in E. cbn in E. destruct (Z.testbit a k); [discriminate|reflexivity]. Qed.
(* [comment removed for export] *)

Lemma pow2k_range : forall k : nat, (k <= 31)%nat -> (0 < 2 ^ Z.of_nat k <= 2^31)%Z.
Proof. intros k Hk. split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]. Qed.

Lemma pow2k_half : forall k : nat, (1 <= k)%nat -> Z.shiftr (2 ^ Z.of_nat k) 1 = (2 ^ Z.of_nat (k - 1))%Z.
Proof.
  intros k Hk. rewrite Z.shiftr_div_pow2 by lia. rewrite <- Z.pow_sub_r by lia. f_equal. lia.
Qed.

Lemma signed_small : forall n, (0 <= n < 2^63)%Z -> bv_signed (Z_to_bv 64 n) = n.
Proof. intros n Hn. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec n (2^63)); lia. Qed.

(* [comment removed for export] *)
Lemma div20_form : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (Z.shiftr (x * 14757395258967641293) 64 mod 18446744073709551616) 4 = (x / 20)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small (x * 14757395258967641293 / 2^64)).
  2:{ split. { apply Z.div_pos; lia. } apply Z.div_lt_upper_bound; [lia|]. nia. }
  apply div20_magic. exact Hx.
Qed.

(* [comment removed for export] *)
Section CellConv.
  Variable segs : list Segment.
  Lemma rw_cells_C8_CB : forall m A (w : word) cs,
    rw_cells segs m A (C8 w :: cs) -> rw_cells segs m A (CB 8 (le8 w) :: cs).
  Proof.
    intros m A w cs [[WF BA] WR]. split; [split|].
    - cbn. split; [apply (length_le8 w) | exact (proj2 WF)].
    - exact BA.
    - exact WR.
  Qed.
End CellConv.

(* [comment removed for export] *)
Ltac notrap :=
  let K := fresh "KT" in
  if_cases K; zify_cond K; [ exfalso; revert K; crc_arith_prep; intros K; lia | try clear K ].
