(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 552 of its 576 lines of code are new or changed and 120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/diginet_sysex_encode.v, with its module names, addresses and numbers changed; 892 of its 988 lines of code are new or changed and 480 lines of the source are left out. *)
(** The walk of owed_counter_text (fuzz_codec.c:402-429; 0x150cc in the UBSan image) against its
    contract, given the contract of its callee owed_seg7: the prologue, the first loop over the text
    by fuel, the second loop over the eight digits, and the epilogue. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells owed_seg7_c owed_counter_text_c.

Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- cells ---- *)

Lemma oct_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma oct_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma oct_u32_cells : forall m A ws,
  u32arr rsegs m A ws -> rw_cells rsegs m A [CB (length (u32s ws)) (u32s ws)].
Proof.
  intros m A ws [Hb Hw]. split.
  - split. { cbn. split; [reflexivity|exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia.
    exact Hw.
Qed.

Lemma oct_cells_u8 : forall m A b, rw_cells rsegs m A [C1 b] -> u8arr rsegs m A [b].
Proof.
  intros m A b [[_ Hb] Hw]. split; [exact Hb | exact Hw].
Qed.

Lemma oct_u8_cell : forall m A b, u8arr rsegs m A [b] -> rw_cells rsegs m A [C1 b].
Proof.
  intros m A b [Hb Hw]. split; [split; [cbn; tauto | exact Hb] | exact Hw].
Qed.

Lemma oct_u8_cb : forall m A bs n, length bs = n -> u8arr rsegs m A bs -> rw_cells rsegs m A [CB n bs].
Proof. intros m A bs n <- H. apply rw_cells_of_u8arr. exact H. Qed.

(** ---- the RELRO tables after stores outside them ---- *)

Lemma relro_img_munch : forall W m m', relro_img m -> munch W m m' -> disjoint_from W RELRO_BASE RELRO_LEN ->
  relro_img m'.
Proof.
  intros W m m' HR MU Hd i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))).
  - apply HR. exact Hi.
  - eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by (unfold RELRO_BASE, RELRO_LEN in *; lia). lia.
Qed.

(** ---- bytes ---- *)

Lemma le1_b8 : forall x, 0 <= x < 256 -> le1 (Z_to_bv 64 x) = [b8 x].
Proof.
  intros x Hx. rewrite <- le1_zxb. f_equal. unfold zxb, b8. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma b8_unsigned : forall x, 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof.
  intros x Hx. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. lia.
Qed.

Lemma z8_unsigned : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. exact b8_unsigned. Qed.

(** the value of a byte b8 x loaded with lbu, x in [0, 256) *)
Ltac byte_fix :=
  cbv beta;
  repeat first [ rewrite b8_unsigned by lia | rewrite z8_unsigned by lia
               | match goal with |- context [?x mod 256] => rewrite (Z.mod_small x 256) by lia end ].

Lemma pow2_small : forall i, 0 <= i <= 6 -> 1 <= 2 ^ i <= 64.
Proof.
  intros i Hi. assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; cbn; lia.
Qed.

Lemma lor_128 : forall a b, 0 <= a < 128 -> 0 <= b < 128 -> 0 <= Z.lor a b < 128.
Proof. intros a b Ha Hb. pose proof (lor_lt_pow2 a b 7) as H. change (2 ^ 7) with 128 in H. auto. Qed.

Lemma swrap32_id : forall e, -2^31 <= e < 2^31 -> bv_swrap 32 e = e.
Proof. intros e He. apply bv_swrap_small. replace (bv_half_modulus 32) with (2^31) by reflexivity. lia. Qed.

Ltac swrap_fix := repeat match goal with |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia end.

(** wa e = a, for the address a of a load or store *)
Ltac oct_addr :=
  first [ apply wa_of_var; lia | apply wa_of_Z_to_bv; rewrite ?Z.shiftl_mul_pow2 by lia; lia
        | unfold wa; f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; lia
        | unfold wa; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia ].

Lemma bz_length : forall l, length (bz l) = length l.
Proof. intros l. unfold bz. apply length_map. Qed.

(** the store tactics' sizes, also through the digit and frame lists *)
Ltac simpl_sizes ::=
  repeat progress (rewrite ?length_app, ?bz_length, ?length_skipn, ?length_map);
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app; cbn [length].

(** an index inside an array, or the length of an array *)
Ltac len_tac :=
  first [ lia | (cbn [length]; lia)
        | (rewrite ?length_app, ?length_map, ?bz_length, ?length_skipn, ?Arr.upd_length in *; cbn [length] in *; lia) ].

Ltac arr_len l :=
  first [ lazymatch goal with _ : length l = _ |- _ => idtac end
        | let L := fresh "LEN" in assert (L : length l = 8%nat) by len_tac ].
Ltac arr_lens :=
  repeat match goal with
  | H : u8arr _ _ _ ?l |- _ => lazymatch l with [_] => fail | _ => progress (arr_len l) end
  | H : u32arr _ _ _ ?l |- _ => progress (arr_len l)
  end.

(** after the step of a byte store into the array ARR at index i of the value x *)
Ltac u8_store ARR i x :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
    lazymatch type of ARR with u8arr _ mm ?A ?l =>
      replace (write_to_mem mm a bs) with (write_to_mem mm (wa (A + i)) [b8 x])
        by (f_equal; first [ oct_addr | symmetry; rewrite le1_b8 by lia; reflexivity ]);
      let ARR' := fresh "ARRn" in
      pose proof (u8arr_write rsegs mm A l i (b8 x) ARR) as ARR';
      specialize (ARR' ltac:(len_tac));
      clear ARR; store_done; rename ARR' into ARR
    end
  end.

(** after the step of a word store into the array ARR at index i *)
Ltac u32_store ARR i :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a (le4 ?v)) _) =>
    lazymatch type of ARR with u32arr _ mm ?A ?l =>
      replace (write_to_mem mm a (le4 v)) with (write_to_mem mm (wa (A + 4 * i)) (le4 v))
        by (f_equal; oct_addr);
      let ARR' := fresh "ARRn" in
      pose proof (u32arr_write rsegs mm A l i v ARR) as ARR';
      specialize (ARR' ltac:(len_tac));
      clear ARR; store_done; rename ARR' into ARR
    end
  end.

(** ---- branch conditions: unsigned / signed tests on words held as Z_to_bv 64 e ---- *)

Lemma lxor_ones_mod : forall x,
  Z.lxor (x mod 18446744073709551616) 18446744073709551615 = 18446744073709551615 - x mod 18446744073709551616.
Proof. intros x. apply zb_lxor_ones. apply Z.mod_pos_bound. lia. Qed.

Lemma lxor_ones_w : forall w : word, Z.lxor (bv_unsigned w) 18446744073709551615 = 18446744073709551615 - bv_unsigned w.
Proof. intros w. apply zb_lxor_ones. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

Ltac oc_lia := rewrite ?Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia.
Ltac oc_base :=
  first [ reflexivity
        | apply Z.ltb_lt; oc_lia | apply Z.ltb_ge; oc_lia
        | apply Z.leb_le; oc_lia | apply Z.leb_gt; oc_lia
        | apply Z.eqb_eq; oc_lia | apply Z.eqb_neq; oc_lia ].
Ltac oc_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); oc_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); oc_rec
  | |- andb _ _ = true => apply andb_true_intro; split; oc_rec
  | |- andb _ _ = false => first [ apply andb_false_intro1; oc_rec | apply andb_false_intro2; oc_rec ]
  | |- orb _ _ = true => first [ apply orb_true_intro; left; oc_rec | apply orb_true_intro; right; oc_rec ]
  | |- orb _ _ = false => apply orb_false_intro; oc_rec
  | _ => oc_base
  end.
Ltac oc_cond :=
  rewrite ?bv_lts_zero_r, ?bv_lts_zero_l; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  rewrite ?unsigned_lit_wrap, ?lxor_ones_mod, ?lxor_ones_w; oc_rec.
Ltac oc_true :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota | symmetry; oc_cond]
  end.
Ltac oc_false :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; oc_cond]
  end.

(** ---- list facts of the two arrays and the digits ---- *)

Lemma nth_error_bz_app : forall (sv : list Z) (jk : list byte) f, 0 <= f < Z.of_nat (length sv) ->
  nth_error (bz sv ++ jk) (Z.to_nat f) = Some (b8 (nth (Z.to_nat f) sv 0)).
Proof.
  intros sv jk f Hf. rewrite nth_error_app1 by (rewrite bz_length; lia).
  unfold bz. rewrite nth_error_map. rewrite (nth_error_nth' sv 0) by lia. reflexivity.
Qed.

Lemma nth_error_mapw : forall (dot : list Z) f, 0 <= f < Z.of_nat (length dot) ->
  nth_error (map (Z_to_bv 64) dot) (Z.to_nat f) = Some (Z_to_bv 64 (nth (Z.to_nat f) dot 0)).
Proof. intros dot f Hf. rewrite nth_error_map. rewrite (nth_error_nth' dot 0) by lia. reflexivity. Qed.

Lemma upd_seg : forall (sg : list Z) (sj : list byte) i v, length sg = Z.to_nat i -> 0 <= i ->
  (Z.to_nat i < length sj)%nat ->
  upd (bz sg ++ skipn (Z.to_nat i) sj) (Z.to_nat i) (b8 v) = bz (sg ++ [v]) ++ skipn (Z.to_nat (i + 1)) sj.
Proof.
  intros sg sj i v Hl Hi Hj.
  assert (Lb : length (bz sg) = Z.to_nat i) by (rewrite bz_length; exact Hl).
  rewrite upd_firstn_skipn by (rewrite length_app, length_skipn; lia).
  replace (firstn (Z.to_nat i) (bz sg ++ skipn (Z.to_nat i) sj)) with (bz sg)
    by (rewrite firstn_app, Lb, Nat.sub_diag, firstn_O, app_nil_r; symmetry; apply firstn_all2; lia).
  replace (skipn (S (Z.to_nat i)) (bz sg ++ skipn (Z.to_nat i) sj)) with (skipn (Z.to_nat (i + 1)) sj).
  2:{ rewrite skipn_app, Lb. replace (S (Z.to_nat i) - Z.to_nat i)%nat with 1%nat by lia.
      replace (skipn (S (Z.to_nat i)) (bz sg)) with (@nil byte) by (symmetry; apply skipn_all2; lia).
      cbn [app]. rewrite skipn_skipn. f_equal. lia. }
  unfold bz. rewrite map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma upd_dot : forall (dot : list Z) i v, 0 <= i -> (Z.to_nat i < length dot)%nat ->
  upd (map (Z_to_bv 64) dot) (Z.to_nat i) (Z_to_bv 64 v) = map (Z_to_bv 64) (upd_at dot i v).
Proof.
  intros dot i v Hi Hl. rewrite upd_firstn_skipn by (rewrite length_map; lia).
  unfold upd_at. rewrite map_app, firstn_map, skipn_map. reflexivity.
Qed.

Lemma upd_sv : forall (sv : list Z) (jk : list byte) v, (0 < length jk)%nat ->
  upd (bz sv ++ jk) (length sv) (b8 v) = bz (sv ++ [v]) ++ tl jk.
Proof.
  intros sv jk v Hj. destruct jk as [|b jk]; [cbn in Hj; lia|].
  rewrite upd_firstn_skipn by (rewrite length_app, bz_length; cbn; lia).
  rewrite firstn_app, bz_length, Nat.sub_diag, firstn_O, app_nil_r.
  replace (firstn (length sv) (bz sv)) with (bz sv) by (symmetry; apply firstn_all2; rewrite bz_length; lia).
  rewrite skipn_app, bz_length.
  replace (skipn (S (length sv)) (bz sv)) with (@nil byte) by (symmetry; apply skipn_all2; rewrite bz_length; lia).
  replace (S (length sv) - length sv)%nat with 1%nat by lia. cbn [skipn app tl].
  unfold bz. rewrite map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma toN_succ : forall i, i <= 7 -> Z.to_nat (8 - i) = S (Z.to_nat (8 - (i + 1))).
Proof. intros i Hi. lia. Qed.

Lemma sx32_small : forall x, 0 <= x < 2 ^ 31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_id by lia. reflexivity. Qed.

Lemma Forall_nthZ : forall (P : Z -> Prop) (l : list Z) k, Forall P l -> (k < length l)%nat -> P (nth k l 0).
Proof. intros P l k H Hk. apply (proj1 (Forall_nth P l) H k 0 Hk). Qed.

(** ---- the text, read byte by byte ---- *)

Lemma skipn_cons_nth2 : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.

Lemma in_skipn_lt : forall {A} (l : list A) k (x : A), In x (skipn k l) -> (k < length l)%nat.
Proof.
  intros A l k x H. destruct (Nat.lt_ge_cases k (length l)) as [Hl | Hg]; [exact Hl|].
  rewrite skipn_all2 in H by lia. destruct H.
Qed.

Lemma in_skipn_next : forall (l : list byte) k,
  In (b8 0) (skipn k l) -> bv_unsigned (nth k l (b8 0)) <> 0 ->
  In (b8 0) (skipn (S k) l) /\ (S k < length l)%nat.
Proof.
  intros l k H HC.
  assert (Hk : (k < length l)%nat) by (eapply in_skipn_lt; exact H).
  rewrite (skipn_cons_nth2 l k (b8 0)) in H by exact Hk. cbn [In] in H.
  destruct H as [H | H].
  - exfalso. apply HC. rewrite H. apply b8_unsigned. lia.
  - split; [exact H|]. eapply in_skipn_lt; exact H.
Qed.

Lemma zb_nth : forall (l : list byte) k, nth k (zb l) 0 = bv_unsigned (nth k l (b8 0)).
Proof.
  intros l k. unfold zb.
  rewrite <- (map_nth bv_unsigned l (b8 0) k).
  f_equal; symmetry; apply b8_unsigned; lia.
Qed.

Lemma oct_byte : forall mm a bs (j : Z),
  bytes_at rsegs mm a bs -> 0 <= j < Z.of_nat (length bs) ->
  ov_read_bytes rsegs mm (wa (a + j)) 1 = Some [nth (Z.to_nat j) bs (b8 0)].
Proof.
  intros mm a bs j H Hj.
  rewrite (bytes_at_read rsegs mm a bs j 1 H) by lia.
  f_equal. remember (Z.to_nat j) as i eqn:Ei. assert (Hi : (i < length bs)%nat) by lia.
  clear Ei Hj H. revert i Hi. induction bs as [|x bs IHb]; intros i Hi; cbn in *; [lia|].
  destruct i as [|i]; [reflexivity|]. apply IHb. lia.
Qed.

Lemma land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof.
  intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma seqz46 : forall c, 0 <= c < 256 ->
  Z.b2z ((c + -46) mod 18446744073709551616 <? 1) = (if c =? 46 then 1 else 0).
Proof.
  intros c Hc. destruct (Z.eqb_spec c 46) as [-> | Hne]; [vm_compute; reflexivity|].
  replace ((c + -46) mod 18446744073709551616 <? 1) with false; [reflexivity|].
  symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Lemma In_firstn : forall {A} (l : list A) k x, In x (firstn k l) -> In x l.
Proof.
  induction l as [|y l IH]; intros [|k] x H; cbn in *; try tauto.
  destruct H as [H | H]; [left; exact H | right; eapply IH; exact H].
Qed.

Lemma In_skipn : forall {A} (l : list A) k x, In x (skipn k l) -> In x l.
Proof.
  induction l as [|y l IH]; intros [|k] x H; cbn in *; try tauto.
  right. eapply IH. exact H.
Qed.

Lemma Forall_upd_at : forall (P : Z -> Prop) (l : list Z) i v, Forall P l -> P v -> Forall P (upd_at l i v).
Proof.
  intros P l i v Hl Hv. unfold upd_at. apply Forall_app. split.
  - rewrite Forall_forall in Hl |- *. intros x Hx. apply Hl. eapply In_firstn; exact Hx.
  - constructor; [exact Hv|]. rewrite Forall_forall in Hl |- *. intros x Hx. apply Hl.
    eapply In_skipn; exact Hx.
Qed.

Lemma tl_length : forall {A} (l : list A), (0 < length l)%nat -> length (tl l) = (length l - 1)%nat.
Proof. intros A [|x l] H; cbn in *; lia. Qed.

(** addresses of the loads and stores also carry shifts *)
Ltac word_eq_tac ::=
  first [ exact eq_refl
        | f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; lia
        | apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; Z.div_mod_to_equations; lia ].

Ltac nth_tac := first [ assumption | reflexivity | (apply nth_error_bz_app; lia) | (apply nth_error_mapw; lia) ].

Ltac u8_read ARR i v a :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of ARR with u8arr _ mm ?A ?l =>
      let HR := fresh "HR" in
      assert (HR : ov_read_bytes rsegs mm a 1 = Some [v])
        by (apply (u8arr_read rsegs mm A l i v); [exact ARR | nth_tac | lia | symmetry; oct_addr])
    end end.
Ltac u8_sok ARR i a :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of ARR with u8arr _ mm ?A ?l =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm a 1 = true)
        by (apply (u8arr_store_ok rsegs mm A l i a); [exact ARR | len_tac | symmetry; oct_addr])
    end end.
Ltac u32_read ARR i v a :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of ARR with u32arr _ mm ?A ?l =>
      let HR := fresh "HR" in
      assert (HR : ov_read_bytes rsegs mm a 4 = Some (le4 v))
        by (apply (u32arr_read rsegs mm A l i v); [exact ARR | nth_tac | lia | symmetry; oct_addr])
    end end.
Ltac u32_sok ARR i a :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of ARR with u32arr _ mm ?A ?l =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm a 4 = true)
        by (apply (u32arr_store_ok rsegs mm A l i a); [exact ARR | len_tac | symmetry; oct_addr])
    end end.

Lemma ct1_zero_head : forall (l : list Z) n s dot,
  nth 0 l 0 = 0 -> (0 < length l)%nat -> ct1_owe l n s dot = Some (n, s, dot).
Proof.
  intros [|x l'] n s dot H Hl; cbn in H, Hl; [lia|].
  cbn [ct1_owe]. rewrite H. reflexivity.
Qed.

(** the frame after the prologue and the four sd zero: dot[8] zeroed, s[8] junk, then the saved cells *)

Lemma u32arr_zero4 : forall mm A,
  rw_cells rsegs mm A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  u32arr rsegs mm A (map (Z_to_bv 64) (repeat 0 8)).
Proof.
  intros mm A [[_ Hb] Hw]. split.
  - eapply bytes_at_ext; [exact Hb|]. vm_compute. reflexivity.
  - exact Hw.
Qed.

Lemma frame_split : forall mm A j (cs : list cell),
  rw_cells rsegs mm A (C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: CB 8 j :: cs) ->
  u32arr rsegs mm A (map (Z_to_bv 64) (repeat 0 8)) /\ u8arr rsegs mm (A + 32) j /\ length j = 8%nat /\
  rw_cells rsegs mm (A + 40) cs.
Proof.
  intros mm A j cs H.
  change (C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: CB 8 j :: cs)
    with ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ (CB 8 j :: cs)) in H.
  apply oct_split in H. destruct H as [H0 H1].
  change (CB 8 j :: cs) with ([CB 8 j] ++ cs) in H1.
  apply oct_split in H1. destruct H1 as [H1 H2].
  cbn [cells_size csize Nat.add] in H1, H2.
  assert (Lj : length j = 8%nat) by (destruct H1 as [[Hwf _] _]; cbn in Hwf; tauto).
  split; [apply u32arr_zero4; exact H0|].
  split; [apply u8arr_of_rw_cells in H1; exact H1|].
  split; [exact Lj|].
  replace (A + 40) with (A + Z.of_nat 32 + Z.of_nat 8) by lia. exact H2.
Qed.

Section OctEx.
Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo : Z) (a0t a1 a2 : word) (tb sj : list byte).
Hypothesis LO : lo + 144 <= bv_unsigned sp.
Hypothesis SP1 : bv_unsigned sp <= bv_unsigned a1.
Hypothesis SP2 : bv_unsigned sp <= bv_unsigned a2.
Hypothesis DSJ : disj (bv_unsigned a1) 8 (bv_unsigned a2) 1.
Hypothesis A1B : bv_unsigned a1 + 8 <= 2 ^ 64.
Hypothesis A2B : bv_unsigned a2 + 1 <= 2 ^ 64.
Hypothesis SP0 : bv_unsigned sp <= bv_unsigned a0t.
Hypothesis A0B : bv_unsigned a0t + Z.of_nat (length tb) <= 2 ^ 64.
Hypothesis RI : relro_img m.
Hypothesis D3 : disj lo (bv_unsigned sp - lo) RELRO_BASE RELRO_LEN.

Definition saved : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition Wfull : list ivl :=
  [(bv_unsigned sp + -144, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 8); (bv_unsigned a2, bv_unsigned a2 + 1)].

Definition post_ok (m' : word -> option byte) (rw : word) : Prop :=
  let '(rc, sg, d) := owed_counter_text_spec (zb tb) in
  rw = Z_to_bv 64 rc /\
  (rc = 0 -> rw_cells rsegs m' (bv_unsigned a1) [CB 8 (bz sg)] /\ rw_cells rsegs m' (bv_unsigned a2) [C1 (b8 d)]) /\
  (rc <> 0 -> exists sg' dv, rw_cells rsegs m' (bv_unsigned a1) [CB 8 sg'] /\ rw_cells rsegs m' (bv_unsigned a2) [C1 dv]).

Definition Qo (ms' : machine_state) : Prop :=
  exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - OWED_COUNTER_TEXT_DEPTH, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 8); (bv_unsigned a2, bv_unsigned a2 + 1)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    let '(rc, sg, d) := owed_counter_text_spec (zb tb) in
    a0' = Z_to_bv 64 rc /\
    (rc = 0 -> rw_cells rsegs m' (bv_unsigned a1) [CB 8 (bz sg)] /\ rw_cells rsegs m' (bv_unsigned a2) [C1 (b8 d)]) /\
    (rc <> 0 -> exists sg' dv, rw_cells rsegs m' (bv_unsigned a1) [CB 8 sg'] /\ rw_cells rsegs m' (bv_unsigned a2) [C1 dv]).

Lemma oct_exit : forall (ra' t0' x8 x9 a0' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 rcw : word)
    (ws : list word) (bs : list byte) (m1 : word -> option byte),
  length ws = 8%nat -> length bs = 8%nat ->
  u32arr rsegs m1 (bv_unsigned sp + -144) ws ->
  u8arr rsegs m1 (bv_unsigned sp + -112) bs ->
  rw_cells rsegs m1 (bv_unsigned sp + -104) saved ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch Wfull m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  post_ok m1 rcw ->
  evt rsegs Qo
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1 t2 x8 x9 a0' rcw a2' a3' a4' a5' a6' a7'
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15288) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' x8 x9 a0' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 rcw ws bs m1
    HL1 HL2 DOT SA FS ST MU WM HMI PO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as [Hlo _].
  assert (FR : rw_cells rsegs m1 (bv_unsigned sp + -144) ([CB 32 (u32s ws); CB 8 bs] ++ saved)).
  { apply (oct_join m1 _ [CB 32 (u32s ws); CB 8 bs]).
    - apply (oct_join m1 _ [CB 32 (u32s ws)] [CB 8 bs]).
      + pose proof (oct_u32_cells m1 _ ws DOT) as H. rewrite u32s_length, HL1 in H. exact H.
      + cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -144 + Z.of_nat 32) with (bv_unsigned sp + -112) by lia.
        apply oct_u8_cb; assumption.
    - cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) by lia.
      exact FS. }
  clear DOT SA.
  eapply stk_release in FR; [ | exact ST | lia ].
  rewrite cells_size_app in FR. cbn [saved cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -144 + Z.of_nat 144) with (bv_unsigned sp) in FR by lia.
  clear ST.
  unfold saved in FS.
  do 16 zstep.
  apply evt_done. unfold Qo.
  do 10 eexists. split; [reflexivity|].
  split.
  { eapply munch_weaken; [| exact MU]. unfold sub_fp, Wfull, OWED_COUNTER_TEXT_DEPTH. cbn [outside]. intros; lia. }
  split; [exact WM|]. split; [exact HMI|]. split; [exact FR|].
  exact PO.
Qed.

Lemma post_ok_ok : forall m1 sg d, owed_counter_text_spec (zb tb) = (0, sg, d) ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 (bz sg)] -> rw_cells rsegs m1 (bv_unsigned a2) [C1 (b8 d)] ->
  post_ok m1 (Z_to_bv 64 0).
Proof.
  intros m1 sg d E H1 H2. unfold post_ok. rewrite E. split; [reflexivity|]. split; [auto | intros C; lia].
Qed.

Lemma post_ok_err : forall m1 sg d sg' dv, owed_counter_text_spec (zb tb) = (E_RANGE, sg, d) ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sg'] -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  post_ok m1 (Z_to_bv 64 (-11)).
Proof.
  intros m1 sg d sg' dv E H1 H2. unfold post_ok. rewrite E. split; [reflexivity|].
  split; [unfold E_RANGE; intros C; lia | intros _; exists sg', dv; auto].
Qed.

(** ---- the second loop (fuzz_codec.c:418-428), 0x1520c ---- *)

Section L2.
Variables (ra' tw x24 x25 x26 x27 : word) (n : Z) (sv dot : list Z) (jk : list byte).
Hypothesis Hn : 0 <= n <= 8.
Hypothesis Hsv : length sv = Z.to_nat n.
Hypothesis Fsv : Forall (fun v => 0 <= v < 128) sv.
Hypothesis Hdot : length dot = 8%nat.
Hypothesis Fdot : Forall (fun d => 0 <= d <= 1) dot.
Hypothesis Hjk : length jk = (8 - Z.to_nat n)%nat.
Hypothesis Hsj : length sj = 8%nat.

Definition l2_ok (fuel : nat) : Prop :=
  forall (t0' a6' a7' : word) (i d : Z) (sg : list Z) (m1 : word -> option byte),
  (Z.to_nat (8 - i) <= fuel)%nat -> 0 <= i <= 7 ->
  length sg = Z.to_nat i -> Forall (fun v => 0 <= v < 128) sg -> 0 <= d < 128 ->
  ct2_go n sv dot i (Z.to_nat (8 - i)) sg d = owed_counter_text_spec (zb tb) ->
  u32arr rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -112) (bz sv ++ jk) ->
  rw_cells rsegs m1 (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  u8arr rsegs m1 (bv_unsigned a1) (bz sg ++ skipn (Z.to_nat i) sj) ->
  u8arr rsegs m1 (bv_unsigned a2) [b8 d] ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch Wfull m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qo
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1 t2 a2 a1
             (Z_to_bv 64 (8 - n)) (Z_to_bv 64 i) (Z_to_bv 64 i)
             (Z_to_bv 64 (Z.lxor (bv_unsigned a1) 18446744073709551615)) (Z_to_bv 64 7) (Z_to_bv 64 1) a6' a7'
             tw (Z_to_bv 64 (bv_unsigned sp + -144))
             (Z_to_bv 64 (Z.lxor ((bv_unsigned sp + -144) mod 18446744073709551616) 18446744073709551615))
             (Z_to_bv 64 (bv_unsigned sp + -112))
             (Z_to_bv 64 (Z.lxor ((bv_unsigned sp + -112) mod 18446744073709551616) 18446744073709551615))
             (Z_to_bv 64 8) x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1520c) fc None m1 (seg_rom rsegs)).

Ltac l2_side :=
  first [ eassumption | lia | (rewrite length_app; cbn [length]; lia)
        | (apply Forall_app; split; [assumption | constructor; [lia | constructor]]) ].

(** the end of an iteration, 0x15270: digit i is placed *)
Lemma l2_tail : forall fuel, l2_ok fuel ->
  forall (t0' a6' a7' : word) (i d : Z) (sg : list Z) (m1 : word -> option byte),
  (Z.to_nat (8 - (i + 1)) <= fuel)%nat -> 0 <= i <= 7 ->
  length sg = Z.to_nat (i + 1) -> Forall (fun v => 0 <= v < 128) sg -> 0 <= d < 128 ->
  ct2_go n sv dot (i + 1) (Z.to_nat (8 - (i + 1))) sg d = owed_counter_text_spec (zb tb) ->
  u32arr rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -112) (bz sv ++ jk) ->
  rw_cells rsegs m1 (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  u8arr rsegs m1 (bv_unsigned a1) (bz sg ++ skipn (Z.to_nat (i + 1)) sj) ->
  u8arr rsegs m1 (bv_unsigned a2) [b8 d] ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch Wfull m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qo
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1 t2 a2 a1
             (Z_to_bv 64 (8 - n)) (Z_to_bv 64 i) (Z_to_bv 64 i)
             (Z_to_bv 64 (Z.lxor (bv_unsigned a1) 18446744073709551615)) (Z_to_bv 64 7) (Z_to_bv 64 1) a6' a7'
             tw (Z_to_bv 64 (bv_unsigned sp + -144))
             (Z_to_bv 64 (Z.lxor ((bv_unsigned sp + -144) mod 18446744073709551616) 18446744073709551615))
             (Z_to_bv 64 (bv_unsigned sp + -112))
             (Z_to_bv 64 (Z.lxor ((bv_unsigned sp + -112) mod 18446744073709551616) 18446744073709551615))
             (Z_to_bv 64 8) x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15270) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel IH t0' a6' a7' i d sg m1 HF Hi Hsg Fsg Hd HCT DOT SA FS SG DT ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as [Hlo _].
  zstep. zstep. swrap_fix. zstep.
  destruct (Z.eqb_spec (i + 1) 8) as [E8 | N8].
  - oc_false. zstep. zstep.
    rewrite skipn_all2 in SG by lia. rewrite app_nil_r in SG.
    eapply oct_exit with (ws := map (Z_to_bv 64) dot) (bs := bz sv ++ jk);
      [ rewrite length_map; exact Hdot | rewrite length_app, bz_length; lia | exact DOT | exact SA | exact FS
      | exact ST | exact MU | exact WM | exact HMI | ].
    apply (post_ok_ok m1 sg d).
    + rewrite <- HCT. replace (Z.to_nat (8 - (i + 1))) with O by lia. reflexivity.
    + apply oct_u8_cb; [rewrite bz_length; lia | exact SG].
    + apply oct_u8_cell. exact DT.
  - oc_true.
    eapply (IH t0' _ _ (i + 1) d sg); l2_side.
Qed.


Lemma l2_loop : forall fuel, l2_ok fuel.
Proof.
  induction fuel as [|fuel IH]; unfold l2_ok;
    intros t0' a6' a7' i d sg m1 HF Hi Hsg Fsg Hd HCT DOT SA FS SG DT ST MU WM HMI.
  { exfalso. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
  pose proof ST as [Hlo _].
  pose proof DSJ as DSJ'. unfold disj in DSJ'.
  unfold Wfull in MU.
  arr_lens.
  rewrite (toN_succ i) in HCT by lia. cbn [ct2_go] in HCT.
  do 2 zstep. swrap_fix. zstep. oc_false.
  zstep.
  destruct (Z.ltb_spec (i - (8 - n)) 0) as [Hneg | Hpos].
  - replace (i - (8 - n) <? 0) with true in HCT by (symmetry; apply Z.ltb_lt; lia).
    replace (0 <=? i - (8 - n)) with false in HCT by (symmetry; apply Z.leb_gt; lia).
    cbn [andb] in HCT.
    oc_true. zstep. zstep. oc_false.
    u8_sok SG i (Z_to_bv 64 (bv_unsigned a1 + i)).
    zstep. zstep.
    u8_store SG i 0.
    rewrite upd_seg in SG by (rewrite ?bz_length; lia).
    arr_lens.
    zstep. oc_true.
    eapply (l2_tail fuel IH _ _ _ i d (sg ++ [0])); l2_side.
  - replace (i - (8 - n) <? 0) with false in HCT by (symmetry; apply Z.ltb_ge; lia).
    replace (0 <=? i - (8 - n)) with true in HCT by (symmetry; apply Z.leb_le; lia).
    cbn [andb] in HCT.
    remember (nth (Z.to_nat (i - (8 - n))) sv 0) as x eqn:Ex.
    assert (Rx : 0 <= x < 128)
      by (subst x; apply (Forall_nthZ (fun v => 0 <= v < 128) sv); [exact Fsv | lia]).
    assert (Hx : nth_error (bz sv ++ jk) (Z.to_nat (i - (8 - n))) = Some (b8 x))
      by (subst x; apply nth_error_bz_app; lia).
    oc_false. zstep. oc_false. zstep. oc_false. zstep.
    u8_read SA (i - (8 - n)) (b8 x) (Z_to_bv 64 (bv_unsigned sp + -112 + (i - (8 - n)))).
    zstep. byte_fix.
    zstep. oc_false. zstep.
    u8_sok SG i (Z_to_bv 64 (bv_unsigned a1 + i)).
    zstep. zstep.
    u8_store SG i x.
    rewrite upd_seg in SG by (rewrite ?bz_length; lia).
    arr_lens.
    zstep. oc_false.
    zstep. zstep. oc_false. zstep.
    u32_read DOT (i - (8 - n)) (Z_to_bv 64 (nth (Z.to_nat (i - (8 - n))) dot 0))
      (Z_to_bv 64 (bv_unsigned sp + -144 + Z.shiftl (i - (8 - n)) 2)).
    assert (Rd : 0 <= nth (Z.to_nat (i - (8 - n))) dot 0 <= 1)
      by (apply (Forall_nthZ (fun d => 0 <= d <= 1) dot); [exact Fdot | lia]).
    zstep. rewrite sx32_small by lia.
    zstep.
    destruct (Z.eq_dec (nth (Z.to_nat (i - (8 - n))) dot 0) 0) as [D0 | D1].
    + rewrite (proj2 (Z.eqb_eq _ _) D0) in HCT. cbn [negb] in HCT.
      oc_true.
      eapply (l2_tail fuel IH _ _ _ i d (sg ++ [x])); l2_side.
    + rewrite (proj2 (Z.eqb_neq _ _) D1) in HCT. cbn [negb] in HCT.
      oc_false. zstep.
      destruct (Z.eq_dec i 7) as [E7 | N7].
      * rewrite (proj2 (Z.eqb_eq _ _) E7) in HCT.
        oc_true. zstep.
        eapply oct_exit with (ws := map (Z_to_bv 64) dot) (bs := bz sv ++ jk);
          [ rewrite length_map; exact Hdot | rewrite length_app, bz_length; lia | exact DOT | exact SA | exact FS
          | exact ST | exact MU | exact WM | exact HMI | ].
        apply (post_ok_err _ (sg ++ [x]) d (bz (sg ++ [x]) ++ skipn (Z.to_nat (i + 1)) sj) (b8 d)).
        -- rewrite <- HCT. reflexivity.
        -- apply oct_u8_cb; [rewrite length_app, bz_length, length_skipn, length_app; cbn [length]; lia | exact SG].
        -- apply oct_u8_cell. exact DT.
      * rewrite (proj2 (Z.eqb_neq _ _) N7) in HCT.
        oc_false.
        u8_read DT 0 (b8 d) a2.
        zstep. byte_fix.
        zstep.
        rewrite (Z.mod_small i 32) by lia. rewrite Z.shiftl_1_l.
        assert (P2 : 1 <= 2 ^ i <= 64) by (apply pow2_small; lia).
        rewrite (swrap32_id (2 ^ i)) by lia.
        zstep.
        assert (Rl : 0 <= Z.lor d (2 ^ i) < 128) by (apply lor_128; lia).
        u8_sok DT 0 a2.
        zstep.
        u8_store DT 0 (Z.lor d (2 ^ i)).
        change (Z.to_nat 0) with O in DT. cbn [upd] in DT.
        eapply (l2_tail fuel IH _ _ _ i (Z.lor d (2 ^ i)) (sg ++ [x])); l2_side.
Qed.

(** 0x151f4: *dots = 0 and the second loop from digit 0 (fuzz_codec.c:418-419) *)
Lemma l2_setup : forall (t0' a1' a2' a3' a4' a5' a6' a7' : word) (dj : byte) (m1 : word -> option byte),
  owed_counter_text_spec (zb tb) = ct2 n sv dot ->
  u32arr rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -112) (bz sv ++ jk) ->
  rw_cells rsegs m1 (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sj] ->
  rw_cells rsegs m1 (bv_unsigned a2) [C1 dj] ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qo
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1 t2 a2 a1
             (Z_to_bv 64 (8 - n)) a1' a2' a3' a4' a5' a6' a7'
             tw (Z_to_bv 64 (bv_unsigned sp + -144))
             (Z_to_bv 64 (Z.lxor ((bv_unsigned sp + -144) mod 18446744073709551616) 18446744073709551615))
             (Z_to_bv 64 (bv_unsigned sp + -112))
             (Z_to_bv 64 (Z.lxor ((bv_unsigned sp + -112) mod 18446744073709551616) 18446744073709551615))
             (Z_to_bv 64 8) x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x151f4) fc None m1 (seg_rom rsegs)).
Proof.
  intros t0' a1' a2' a3' a4' a5' a6' a7' dj m1 HCT0 DOT SA FS SG DT ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
  pose proof ST as [Hlo _].
  pose proof DSJ as DSJ'. unfold disj in DSJ'.
  assert (MU' : munch Wfull m m1).
  { eapply munch_weaken; [| exact MU]. unfold sub_fp, Wfull. intros x Hx. cbn [outside] in *. tauto. }
  clear MU. unfold Wfull in MU'.
  apply u8arr_of_rw_cells in SG. apply oct_cells_u8 in DT.
  arr_lens.
  zstep. zstep.
  u8_sok DT 0 a2.
  zstep.
  u8_store DT 0 0.
  change (Z.to_nat 0) with O in DT. cbn [upd] in DT.
  do 3 zstep.
  eapply (l2_loop 8 t0' _ _ 0 0 []); try eassumption; try lia; try constructor.
  rewrite HCT0. reflexivity.
Qed.

End L2.

(** 0x151ec, the end of the first loop: a0 = 8 - n *)
Lemma l1_done : forall (ra' tw x25 x26 x27 t0' a0' a1' a2' a3' a4' a5' a6' a7' : word) (n : Z) (sv dot : list Z)
    (jk : list byte) (dj : byte) (m1 : word -> option byte),
  0 <= n <= 8 -> length sv = Z.to_nat n -> Forall (fun v => 0 <= v < 128) sv ->
  length dot = 8%nat -> Forall (fun d => 0 <= d <= 1) dot -> length jk = (8 - Z.to_nat n)%nat -> length sj = 8%nat ->
  owed_counter_text_spec (zb tb) = ct2 n sv dot ->
  u32arr rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -112) (bz sv ++ jk) ->
  rw_cells rsegs m1 (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sj] ->
  rw_cells rsegs m1 (bv_unsigned a2) [C1 dj] ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qo
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1 t2 a2 a1
             a0' a1' a2' a3' a4' a5' a6' a7'
             tw (Z_to_bv 64 (bv_unsigned sp + -144))
             (Z_to_bv 64 (Z.lxor ((bv_unsigned sp + -144) mod 18446744073709551616) 18446744073709551615))
             (Z_to_bv 64 (bv_unsigned sp + -112))
             (Z_to_bv 64 (Z.lxor ((bv_unsigned sp + -112) mod 18446744073709551616) 18446744073709551615))
             (Z_to_bv 64 8) (Z_to_bv 64 n) x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x151ec) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' tw x25 x26 x27 t0' a0' a1' a2' a3' a4' a5' a6' a7' n sv dot jk dj m1
    Hn Hsv Fsv Hdot Fdot Hjk Hsj HCT0 DOT SA FS SG DT ST MU WM HMI.
  zstep. zstep. swrap_fix.
  eapply l2_setup; eassumption.
Qed.

(** ---- the first loop (fuzz_codec.c:407-417), 0x15150 ---- *)

Hypothesis SEG7 : owed_seg7_contract.

Definition l1_regs (ra' t0' a0' a1' a2' a3' a4' a5' a6' a7' cur : word) (n : Z) : bvmap 5 word :=
  mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1 t2 a2 a1
      a0' a1' a2' a3' a4' a5' a6' a7'
      cur (Z_to_bv 64 (bv_unsigned sp + -144))
      (Z_to_bv 64 (Z.lxor ((bv_unsigned sp + -144) mod 18446744073709551616) 18446744073709551615))
      (Z_to_bv 64 (bv_unsigned sp + -112))
      (Z_to_bv 64 (Z.lxor ((bv_unsigned sp + -112) mod 18446744073709551616) 18446744073709551615))
      (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 46) (Z_to_bv 64 8) (Z_to_bv 64 (-1)) t3 t4 t5 t6.

Definition l1_mem (n k : Z) (sv dot : list Z) (jk : list byte) (dj : byte) (m1 : word -> option byte) : Prop :=
  0 <= n <= 8 /\ length sv = Z.to_nat n /\ Forall (fun v => 0 <= v < 128) sv /\
  length dot = 8%nat /\ Forall (fun d => 0 <= d <= 1) dot /\
  length jk = (8 - Z.to_nat n)%nat /\ length sj = 8%nat /\
  u32arr rsegs m1 (bv_unsigned sp + -144) (map (Z_to_bv 64) dot) /\
  u8arr rsegs m1 (bv_unsigned sp + -112) (bz sv ++ jk) /\
  rw_cells rsegs m1 (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sj] /\
  rw_cells rsegs m1 (bv_unsigned a2) [C1 dj] /\
  bytes_at rsegs m1 (bv_unsigned a0t) tb /\
  stk rsegs m1 lo (bv_unsigned sp + -144) /\
  munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1.

Definition l1_ok (fuel : nat) : Prop :=
  forall (ra' t0' a0' a2' a3' a4' a5' a6' a7' cur : word) (k n : Z) (sv dot : list Z) (jk : list byte)
         (dj : byte) (m1 : word -> option byte),
  (length tb - Z.to_nat k <= fuel)%nat ->
  0 <= k -> (Z.to_nat k < length tb)%nat ->
  In (b8 0) (skipn (Z.to_nat k) tb) ->
  bv_unsigned (nth (Z.to_nat k) tb (b8 0)) <> 0 ->
  bv_unsigned cur = bv_unsigned a0t + k ->
  ct1_owe (skipn (Z.to_nat k) (zb tb)) n sv dot = ct1_owe (zb tb) 0 [] (repeat 0 8) ->
  l1_mem n k sv dot jk dj m1 ->
  evt rsegs Qo
    (MS (l1_regs ra' t0' a0' (Z_to_bv 64 (bv_unsigned (nth (Z.to_nat k) tb (b8 0)))) a2' a3' a4' a5' a6' a7' cur n)
        F (Z_to_bv 64 0x15150) fc None m1 (seg_rom rsegs)).

Ltac l1_part :=
  first [ eassumption | lia | reflexivity | apply Forall_nil
        | (apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia)
        | (rewrite length_app; cbn [length]; lia)
        | (apply Forall_app; split; [eassumption | constructor; [lia | constructor]])
        | (apply Forall_upd_at; [eassumption | first [lia | eassumption]])
        | (rewrite upd_length by lia; eassumption)
        | (rewrite tl_length by lia; lia) ].

Ltac l1_mem_tac :=
  unfold l1_mem; repeat match goal with |- _ /\ _ => split end;
  try l1_part; try l1_part; l1_part.

Ltac l1_side := first [ eassumption | lia | reflexivity | l1_mem_tac ].

(** 0x151cc: the next character, then the loop or its end *)
Lemma l1_tail : forall fuel, l1_ok fuel ->
  forall (ra' t0' a0' a1' a2' a3' a4' a5' a6' a7' cur : word) (k n : Z) (sv dot : list Z) (jk : list byte)
         (dj : byte) (m1 : word -> option byte),
  (length tb - Z.to_nat (k + 1) <= fuel)%nat ->
  0 <= k -> (S (Z.to_nat k) < length tb)%nat ->
  In (b8 0) (skipn (S (Z.to_nat k)) tb) ->
  bv_unsigned cur = bv_unsigned a0t + k ->
  ct1_owe (skipn (S (Z.to_nat k)) (zb tb)) n sv dot = ct1_owe (zb tb) 0 [] (repeat 0 8) ->
  l1_mem n k sv dot jk dj m1 ->
  evt rsegs Qo
    (MS (l1_regs ra' t0' a0' a1' a2' a3' a4' a5' a6' a7' cur n)
        F (Z_to_bv 64 0x151cc) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel IH ra' t0' a0' a1' a2' a3' a4' a5' a6' a7' cur k n sv dot jk dj m1
    HF Hk0 Hklt HZk Hcur HCT MEM.
  unfold l1_regs. unfold l1_mem in MEM.
  destruct MEM as (Hn & Hsv & Fsv & Hdot & Fdot & Hjk & Hsj & DOT & SA & FS & SG & DT & TB & ST & MU & WM & HMI).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a0t) as Ra0t. unfold bv_modulus in Ra0t.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur. unfold bv_modulus in Rcur.
  pose proof ST as [Hlo _].
  assert (Hk1 : Z.to_nat (k + 1) = S (Z.to_nat k)) by lia.
  assert (HR : ov_read_bytes rsegs m1 (wa (bv_unsigned a0t + (k + 1))) 1
               = Some [nth (Z.to_nat (k + 1)) tb (b8 0)]) by (apply oct_byte; [exact TB | lia]).
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (k + 1)) tb (b8 0))) as Rc1.
  unfold bv_modulus in Rc1. change (2 ^ Z.of_N 8) with 256 in Rc1.
  zstep. cbv beta. zstep.
  zstep.
  destruct (Z.eq_dec (bv_unsigned (nth (Z.to_nat (k + 1)) tb (b8 0))) 0) as [Z0 | NZ].
  - oc_true.
    assert (Hcons : skipn (S (Z.to_nat k)) (zb tb) = 0 :: skipn (S (S (Z.to_nat k))) (zb tb)).
    { rewrite (skipn_cons_nth2 (zb tb) (S (Z.to_nat k)) 0) by (unfold zb; rewrite length_map; lia).
      rewrite zb_nth. rewrite <- Hk1, Z0. reflexivity. }
    rewrite Hcons in HCT. cbn [ct1_owe] in HCT.
    eapply (l1_done _ _ _ _ _ _ _ _ _ _ _ _ _ _ n sv dot jk dj m1); try eassumption; try lia.
    unfold owed_counter_text_spec. rewrite <- HCT. reflexivity.
  - oc_false. zstep.
    eapply (IH _ _ _ _ _ _ _ _ _ _ (k + 1) n sv dot jk dj m1);
      first [ exact HF | lia | (rewrite Hk1; assumption)
            | (rewrite unsigned_lit by lia; lia)
            | l1_mem_tac ].
Qed.

(** 0x15180: the call of owed_seg7 and the digit it adds *)
Lemma l1_call : forall fuel, l1_ok fuel ->
  forall (ra' t0' a0' a2' a3' a4' a5' a6' a7' cur : word) (k n c' dv : Z) (sv dot : list Z) (jk : list byte)
         (dj : byte) (m1 : word -> option byte),
  (length tb - Z.to_nat (k + 1) <= fuel)%nat ->
  0 <= k -> (Z.to_nat k < length tb)%nat -> (S (Z.to_nat k) < length tb)%nat ->
  In (b8 0) (skipn (S (Z.to_nat k)) tb) ->
  bv_unsigned cur = bv_unsigned a0t + k ->
  0 <= c' < 256 ->
  dv = (if bv_unsigned (nth (Z.to_nat k) tb (b8 0)) =? 46 then 1 else 0) ->
  (if (owed_seg7_spec c' <? 0) || (n =? 8) then None
   else ct1_owe (skipn (S (Z.to_nat k)) (zb tb)) (n + 1) (sv ++ [owed_seg7_spec c'])
          (upd_at dot n dv)) = ct1_owe (zb tb) 0 [] (repeat 0 8) ->
  l1_mem n k sv dot jk dj m1 ->
  evt rsegs Qo
    (MS (l1_regs ra' t0' a0' (Z_to_bv 64 c') a2' a3' a4' a5' a6' a7' cur n)
        F (Z_to_bv 64 0x15180) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel IH ra' t0' a0' a2' a3' a4' a5' a6' a7' cur k n c' dv sv dot jk dj m1
    HF Hk0 Hklt Hk1lt HZk1 Hcur Hc' Hdv HCT MEM.
  unfold l1_regs. unfold l1_mem in MEM.
  destruct MEM as (Hn & Hsv & Fsv & Hdot & Fdot & Hjk & Hsj & DOT & SA & FS & SG & DT & TB & ST & MU & WM & HMI).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
  pose proof (bv_unsigned_in_range 64 a0t) as Ra0t. unfold bv_modulus in Ra0t.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur. unfold bv_modulus in Rcur.
  pose proof ST as [Hlo _].
  pose proof DSJ as DSJ'. unfold disj in DSJ'.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) tb (b8 0))) as Rc.
  unfold bv_modulus in Rc. change (2 ^ Z.of_N 8) with 256 in Rc.
  arr_lens.
  assert (Hdvr : 0 <= dv <= 1) by (rewrite Hdv; destruct (_ =? 46); lia).
  assert (RIm : relro_img m1).
  { eapply relro_img_munch; [exact RI | exact MU |].
    cbn [disjoint_from]. unfold disj, RELRO_BASE, RELRO_LEN in *. split; [lia | exact I]. }
  assert (MUf : munch Wfull m m1).
  { eapply munch_weaken; [| exact MU]. unfold sub_fp, Wfull. cbn [outside]. tauto. }
  unfold Wfull in MUf.
  zstep. rewrite land255 by lia.
  zstep.
  unfold owed_seg7_contract, OWED_SEG7 in SEG7.
  eapply evt_cut;
    [ eapply SEG7 with (c := c');
      unfold owed_seg7_pre; repeat split; [lia | lia | exact RIm | exact HMI] | ].
  intros ms' POST. destruct POST as (t0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & ->).
  replace (ret_pc (Z_to_bv 64 86408)) with (Z_to_bv 64 86408)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  zstep. zstep.
  destruct (owed_seg7_range c') as [Vn | Vp].
  - rewrite Vn. oc_true.
    rewrite Vn in HCT. cbn [Z.ltb Z.compare orb] in HCT.
    eapply oct_exit with (ws := map (Z_to_bv 64) dot) (bs := bz sv ++ jk);
      [ rewrite length_map; exact Hdot | rewrite length_app, bz_length; lia | exact DOT | exact SA | exact FS
      | exact ST | exact MUf | exact WM | exact HMI | ].
    apply (post_ok_err _ [] 0 sj dj); [| exact SG | exact DT].
    unfold owed_counter_text_spec. rewrite <- HCT. reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _) (proj1 Vp)) in HCT. cbn [orb] in HCT.
    oc_false.
    zstep.
    destruct (Z.eq_dec n 8) as [N8 | N8].
    + rewrite N8 in HCT. cbn [Z.eqb] in HCT.
      rewrite N8. oc_true.
      eapply oct_exit with (ws := map (Z_to_bv 64) dot) (bs := bz sv ++ jk);
        [ rewrite length_map; exact Hdot | rewrite length_app, bz_length; lia | exact DOT | exact SA | exact FS
        | exact ST | exact MUf | exact WM | exact HMI | ].
      apply (post_ok_err _ [] 0 sj dj); [| exact SG | exact DT].
      unfold owed_counter_text_spec. rewrite <- HCT. reflexivity.
    + rewrite (proj2 (Z.eqb_neq _ _) N8) in HCT. cbv iota in HCT.
      oc_false.
      zstep. zstep. oc_false.
      zstep. zstep. oc_false.
      assert (HRc : ov_read_bytes rsegs m1 cur 1 = Some [nth (Z.to_nat k) tb (b8 0)]).
      { replace cur with (wa (bv_unsigned a0t + k)) by (apply wa_of_var; lia).
        apply oct_byte; [exact TB | lia]. }
      zstep. cbv beta. byte_fix.
      zstep. zstep. rewrite seqz46 by lia.
      zstep.
      u32_sok DOT n (wa (bv_unsigned sp + -144 + 4 * n)).
      zstep.
      u32_store DOT n.
      rewrite upd_dot in DOT by lia.
      rewrite <- Hdv in DOT.
      assert (LD : length (upd_at dot n dv) = 8%nat) by (rewrite upd_length by lia; exact Hdot).
      arr_lens.
      zstep. oc_false.
      zstep. zstep. swrap_fix.
      u8_sok SA n (wa (bv_unsigned sp + -112 + n)).
      zstep.
      u8_store SA n (owed_seg7_spec c').
      rewrite <- Hsv in SA. rewrite upd_sv in SA by lia.
      arr_lens.
      zstep. oc_false.
      eapply (l1_tail fuel IH _ _ _ _ _ _ _ _ _ _ cur k (n + 1) (sv ++ [owed_seg7_spec c'])
                (upd_at dot n dv) (tl jk) dj); l1_side.
Qed.

Lemma l1_loop : forall fuel, l1_ok fuel.
Proof.
  induction fuel as [|fuel IH]; unfold l1_ok;
    intros ra' t0' a0' a2' a3' a4' a5' a6' a7' cur k n sv dot jk dj m1 HF Hk0 Hklt HZk HC0 Hcur HCT MEM.
  { exfalso. lia. }
  pose proof MEM as MEM0. unfold l1_mem in MEM.
  destruct MEM as (Hn & Hsv & Fsv & Hdot & Fdot & Hjk & Hsj & DOT & SA & FS & SG & DT & TB & ST & MU & WM & HMI).
  unfold l1_regs.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
  pose proof (bv_unsigned_in_range 64 a0t) as Ra0t. unfold bv_modulus in Ra0t.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur. unfold bv_modulus in Rcur.
  pose proof ST as [Hlo _].
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) tb (b8 0))) as Rc.
  unfold bv_modulus in Rc. change (2 ^ Z.of_N 8) with 256 in Rc.
  destruct (in_skipn_next tb (Z.to_nat k) HZk HC0) as [HZk1 Hk1lt].
  arr_lens.
  assert (Hcons : skipn (Z.to_nat k) (zb tb)
                  = bv_unsigned (nth (Z.to_nat k) tb (b8 0)) :: skipn (S (Z.to_nat k)) (zb tb)).
  { rewrite (skipn_cons_nth2 (zb tb) (Z.to_nat k) 0) by (unfold zb; rewrite length_map; lia).
    rewrite zb_nth. reflexivity. }
  rewrite Hcons in HCT. cbn [ct1_owe] in HCT.
  rewrite (proj2 (Z.eqb_neq _ _) HC0) in HCT. cbv iota in HCT.
  zstep.
  destruct (Z.eq_dec (bv_unsigned (nth (Z.to_nat k) tb (b8 0))) 46) as [E46 | N46].
  - rewrite E46. oc_false.
    rewrite E46 in HCT. cbn [Z.eqb Pos.eqb] in HCT.
    zstep.
    destruct (Z.eq_dec n 0) as [N0 | Npos].
    + subst n. oc_true.
      cbn [Z.ltb Z.compare andb] in HCT. cbv iota zeta in HCT.
      zstep. oc_false.
      zstep.
      eapply (l1_call fuel IH _ _ _ _ _ _ _ _ _ cur k 0 32 1);
        first [ eassumption | lia | (rewrite E46; reflexivity) | l1_mem_tac ].
    + oc_false.
      replace (0 <? n) with true in HCT by (symmetry; apply Z.ltb_lt; lia).
      cbn [andb] in HCT.
      zstep. zstep. oc_false.
      zstep. zstep. zstep. oc_false.
      zstep.
      assert (Rd1 : 0 <= nth (Z.to_nat (n - 1)) dot 0 <= 1)
        by (apply (Forall_nthZ (fun d => 0 <= d <= 1) dot); [exact Fdot | lia]).
      u32_read DOT (n - 1) (Z_to_bv 64 (nth (Z.to_nat (n - 1)) dot 0)) (wa (bv_unsigned sp + -144 + 4 * (n - 1))).
      zstep. rewrite sx32_small by lia.
      zstep.
      destruct (Z.eq_dec (nth (Z.to_nat (n - 1)) dot 0) 0) as [D0 | D1].
      * rewrite D0. oc_true.
        rewrite D0 in HCT. cbn [Z.eqb andb] in HCT. cbv iota in HCT.
        zstep.
        u32_sok DOT (n - 1) (wa (bv_unsigned sp + -144 + 4 * (n - 1))).
        zstep.
        u32_store DOT (n - 1).
        rewrite upd_dot in DOT by lia.
        assert (LD : length (upd_at dot (n - 1) 1) = 8%nat) by (rewrite upd_length by lia; exact Hdot).
        arr_lens.
        zstep. oc_true.
        eapply (l1_tail fuel IH _ _ _ _ _ _ _ _ _ _ cur k n sv (upd_at dot (n - 1) 1) jk dj); l1_side.
      * oc_false.
        rewrite (proj2 (Z.eqb_neq _ _) D1) in HCT. cbn [andb] in HCT. cbv iota zeta in HCT.
        zstep. oc_false.
        zstep.
        eapply (l1_call fuel IH _ _ _ _ _ _ _ _ _ cur k n 32 1);
          first [ eassumption | lia | (rewrite E46; reflexivity) | l1_mem_tac ].
  - oc_true.
    rewrite (proj2 (Z.eqb_neq _ _) N46) in HCT. cbn [andb] in HCT. cbv iota zeta in HCT.
    zstep. oc_true.
    eapply (l1_call fuel IH _ _ _ _ _ _ _ _ _ cur k n (bv_unsigned (nth (Z.to_nat k) tb (b8 0))) 0);
      first [ eassumption | lia | (rewrite (proj2 (Z.eqb_neq _ _) N46); reflexivity) | l1_mem_tac ].
Qed.

(** ---- the prologue, 0x150cc ---- *)

Lemma oct_entry : forall (t0 a3 a4 a5 a6 a7 : word) (dj : byte),
  bytes_at rsegs m (bv_unsigned a0t) tb -> In (b8 0) tb ->
  rw_cells rsegs m (bv_unsigned a1) [CB 8 sj] -> rw_cells rsegs m (bv_unsigned a2) [C1 dj] ->
  length sj = 8%nat -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Qo
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0t a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x150cc) fc None m (seg_rom rsegs)).
Proof.
  intros t0 a3 a4 a5 a6 a7 dj TB TZ SG DT Hsj HMI ST.
  pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a0t) as Ra0t. unfold bv_modulus in Ra0t.
  pose proof (bytes_at_bound _ _ _ _ TB) as BTB.
  assert (TL : (0 < length tb)%nat) by (destruct tb as [|b tb']; [destruct TZ | cbn; lia]).
  pose proof (bv_unsigned_in_range 8 (nth 0 tb (b8 0))) as Rc0.
  unfold bv_modulus in Rc0. change (2 ^ Z.of_N 8) with 256 in Rc0.
  carve_frame 144%nat ST.
  do 14 zstep.
  do 7 zstep.
  apply frame_split in FR. destruct FR as (DOT & SA & Ljk & FS).
  replace (bv_unsigned sp + -144 + 32) with (bv_unsigned sp + -112) in SA by lia.
  replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) in FS by lia.
  zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HB0 : ov_read_bytes rsegs mm a0t 1 = Some [nth 0 tb (b8 0)])
      by (replace a0t with (wa (bv_unsigned a0t + 0)) by (apply wa_of_var; lia);
          apply (oct_byte mm (bv_unsigned a0t) tb 0); [assumption | lia]) end.
  zstep. cbv beta.
  do 5 zstep.
  zstep.
  destruct (Z.eq_dec (bv_unsigned (nth 0 tb (b8 0))) 0) as [Z0 | NZ].
  - oc_true.
    eapply (l2_setup _ _ _ _ _ _ 0 [] (repeat 0 8));
      first [ eassumption | lia | reflexivity | apply Forall_nil
            | (apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia)
            | (unfold owed_counter_text_spec;
               rewrite (ct1_zero_head (zb tb) 0 [] (repeat 0 8));
                 [ reflexivity
                 | rewrite zb_nth; exact Z0
                 | unfold zb; rewrite length_map; lia ]) ].
  - oc_false.
    do 4 zstep.
    eapply (l1_loop (length tb) _ _ _ _ _ _ _ _ _ a0t 0 0 [] (repeat 0 8));
      first [ eassumption | lia | reflexivity | apply Forall_nil
            | (apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia)
            | l1_mem_tac ].
Qed.

End OctEx.

Theorem owed_counter_text_holds : owed_seg7_contract -> owed_counter_text_contract.
Proof.
  intros SEG7. unfold owed_counter_text_contract, OWED_COUNTER_TEXT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo tb sj dj PRE.
  unfold owed_counter_text_pre, OWED_COUNTER_TEXT_DEPTH in PRE.
  destruct PRE as (A0 & [TB TZ] & A1 & SJ & A2 & DJ & DSJ & RI & D3 & SP0 & SP1 & SP2 & MI & ST & LO).
  assert (LSJ : length sj = 8%nat) by (destruct SJ as [[Hwf _] _]; cbn in Hwf; tauto).
  pose proof (rw_cells_bound rsegs m (bv_unsigned a1) [CB 8 sj] SJ) as B1.
  pose proof (rw_cells_bound rsegs m (bv_unsigned a2) [C1 dj] DJ) as B2.
  pose proof (bytes_at_bound _ _ _ _ TB) as B0.
  cbn [cells_size csize Nat.add] in B1, B2.
  destruct B0 as [B0a B0b]. destruct B1 as [B1a B1b]. destruct B2 as [B2a B2b].
  eapply evt_mono.
  - eapply oct_entry; first [ exact SEG7 | eassumption | lia ].
  - intros ms' HQ. exact HQ.
Qed.
