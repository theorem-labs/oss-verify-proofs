(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 552 of its 576 lines of code are new or changed and 120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/diginet_sysex_encode.v, with its module paths, addresses and numbers changed; 807 of its 897 lines of code are new or changed and 486 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text codec_cells
  owed_seg7_c owed_counter_text_c.
Import ListNotations.
Open Scope Z_scope.

(** owed_counter_text keeps dot[8] (ints) at sp'+0, s[8] (bytes) at sp'+0x20 and ra, s0..s9 at
    sp'+0x28..0x80 (sp' = sp - 0x80). Loop 1 (0x14edc..0x14f40) reads the text a byte at a time and runs
    codec_owe's ct1_owe; loop 2 (0x14f70..0x14fbc) runs DgnLib's ct2_go over i = 0..7 and writes seg[i] and
    *dots. dot is kept as a u32arr of the 8 flags, s as a u8arr whose first n bytes are the digits, seg as a
    u8arr whose first i bytes are the digits so far. The three returns meet at 0x14fc8. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* ---- memory helpers ---- *)

Lemma oct_cells_app_split : forall m A cs1 cs2,
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

Lemma oct_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma relro_img_munch : forall W m m', relro_img m -> munch W m m' -> disjoint_from W RELRO_BASE RELRO_LEN -> relro_img m'.
Proof.
  intros W m m' HR HM HD i Hi. specialize (HR i Hi). unfold mrd in *. rewrite HM; [exact HR|].
  eapply disjoint_outside; [exact HD|]. unfold RELRO_BASE, RELRO_LEN in *.
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma relro_frame : forall m m1 lo sp, relro_img m -> disj lo (sp - lo) RELRO_BASE RELRO_LEN -> lo + 128 <= sp ->
  munch [(sp + -128, sp)] m m1 -> relro_img m1.
Proof.
  intros m m1 lo sp HR HD HL HM. eapply relro_img_munch; [exact HR | exact HM |].
  cbn [disjoint_from]. unfold disj in HD. split; [lia | exact I].
Qed.

Lemma u32arr_zero4 : forall m A,
  rw_cells rsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  u32arr rsegs m A (map (Z_to_bv 64) (repeat 0 8)).
Proof.
  intros m A [[_ Hb] Hw]. split.
  - eapply bytes_at_ext; [exact Hb|]. vm_compute. reflexivity.
  - exact Hw.
Qed.

Lemma rw_cells_of_u32arr : forall m A ws,
  u32arr rsegs m A ws -> rw_cells rsegs m A [CB (4 * length ws) (u32s ws)].
Proof.
  intros m A ws [Hb Hw]. rewrite <- u32s_length. apply rw_cells_of_u8arr. split; [exact Hb|].
  rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact Hw.
Qed.

Lemma sx32_lit : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  apply bv_swrap_small. replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. lia.
Qed.

Lemma le1_b8 : forall v, 0 <= v < 256 -> le1 (Z_to_bv 64 v) = [b8 v].
Proof.
  intros v Hv. replace (Z_to_bv 64 v) with (zxb (b8 v)); [apply le1_zxb|].
  unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  replace (bv_modulus 8) with 256 by reflexivity. lia.
Qed.

(* ---- list helpers ---- *)

Lemma firstn_upd_snoc : forall (l : list byte) n b, (n < length l)%nat ->
  firstn (S n) (upd l n b) = firstn n l ++ [b].
Proof.
  induction l as [|x l IH]; intros n b Hn; cbn in Hn; [lia|].
  destruct n as [|n]; cbn; [reflexivity|]. f_equal. apply IH. lia.
Qed.

Lemma firstn_upd_other : forall (l : list byte) n j b, (n <= j)%nat ->
  firstn n (upd l j b) = firstn n l.
Proof.
  induction l as [|x l IH]; intros n j b Hn; [destruct n; reflexivity|].
  destruct n as [|n]; [reflexivity|]. destruct j as [|j]; [lia|]. cbn. f_equal. apply IH. lia.
Qed.

Lemma nth_firstn_bz : forall (sbs : list byte) (s : list Z) n j, firstn n sbs = bz s -> (j < n)%nat ->
  (n <= length sbs)%nat -> nth j sbs (Z_to_bv 8 0) = b8 (nth j s 0).
Proof.
  intros sbs s n j H Hj Hn.
  rewrite <- (firstn_skipn n sbs). rewrite app_nth1 by (rewrite length_firstn; lia). rewrite H.
  unfold bz. change (Z_to_bv 8 0) with (b8 0). apply map_nth.
Qed.

Lemma nth_error_map_lit : forall (l : list Z) j, (j < length l)%nat ->
  nth_error (map (Z_to_bv 64) l) j = Some (Z_to_bv 64 (nth j l 0)).
Proof.
  induction l as [|x l IH]; intros j Hj; cbn in Hj; [lia|].
  destruct j; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_error_byte : forall (l : list byte) j, (j < length l)%nat -> nth_error l j = Some (nth j l (Z_to_bv 8 0)).
Proof.
  induction l as [|x l IH]; intros j Hj; cbn in Hj; [lia|].
  destruct j; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma map_upd_at : forall (l : list Z) i v, (Z.to_nat i < length l)%nat -> 0 <= i ->
  map (Z_to_bv 64) (upd_at l i v) = upd (map (Z_to_bv 64) l) (Z.to_nat i) (Z_to_bv 64 v).
Proof.
  intros l i v Hi H0. unfold upd_at. rewrite upd_firstn_skipn by (rewrite length_map; lia).
  rewrite map_app, firstn_map, skipn_map. reflexivity.
Qed.

(** The frame after the prologue and the four sd zero: dot[8] zeroed, s[8] junk, then the saved cells. *)
Lemma frame_split : forall m A j (cs : list cell),
  rw_cells rsegs m A (C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: CB 8 j :: cs) ->
  u32arr rsegs m A (map (Z_to_bv 64) (repeat 0 8)) /\ u8arr rsegs m (A + 32) j /\ length j = 8%nat /\
  rw_cells rsegs m (A + 40) cs.
Proof.
  intros m A j cs H.
  change (C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0) :: CB 8 j :: cs)
    with ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ (CB 8 j :: cs)) in H.
  apply oct_cells_app_split in H. destruct H as [H0 H1].
  change (CB 8 j :: cs) with ([CB 8 j] ++ cs) in H1.
  apply oct_cells_app_split in H1. destruct H1 as [H1 H2].
  cbn [cells_size csize Nat.add] in H1, H2.
  assert (Lj : length j = 8%nat) by (destruct H1 as [[Hwf _] _]; cbn in Hwf; tauto).
  split; [apply u32arr_zero4; exact H0 |].
  split; [apply u8arr_of_rw_cells in H1; exact H1 |].
  split; [exact Lj |].
  replace (A + 40) with (A + Z.of_nat 32 + Z.of_nat 8) by lia. exact H2.
Qed.

(* ---- arithmetic of the loops ---- *)

(** addw a5, s2, a0 with s2 = n - 8 and a0 = i: the index into s of digit i. *)
Lemma from_eq : forall n i, 0 <= n <= 8 -> 0 <= i < 8 ->
  bv_swrap 32 ((n - 8) mod 18446744073709551616 + i) = i - (8 - n).
Proof.
  intros n i Hn Hi. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma shl2 : forall f, Z.shiftl f 2 = 4 * f.
Proof. intros f. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma le1_unsigned : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. intros b. exact (le1_zxb b). Qed.

Lemma b8_unsigned : forall v, 0 <= v < 256 -> bv_unsigned (b8 v) = v.
Proof.
  intros v Hv. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  replace (bv_modulus 8) with 256 by reflexivity. lia.
Qed.

(** One digit of ct2_go, by the four paths of the machine. *)
Lemma ct2_step_neg : forall n s dot i k seg d, i - (8 - n) < 0 ->
  ct2_go n s dot i (S k) seg d = ct2_go n s dot (i + 1) k (seg ++ [0]) d.
Proof.
  intros n s dot i k seg d H. cbn [ct2_go].
  replace (i - (8 - n) <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (0 <=? i - (8 - n)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Lemma ct2_step_nodot : forall n s dot i k seg d f, f = i - (8 - n) -> 0 <= f -> nth (Z.to_nat f) dot 0 = 0 ->
  ct2_go n s dot i (S k) seg d = ct2_go n s dot (i + 1) k (seg ++ [nth (Z.to_nat f) s 0]) d.
Proof.
  intros n s dot i k seg d f Ef H0 H. subst f. cbn [ct2_go].
  replace (i - (8 - n) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (0 <=? i - (8 - n)) with true by (symmetry; apply Z.leb_le; lia).
  rewrite H. reflexivity.
Qed.

Lemma ct2_step_dot7 : forall n s dot i k seg d f, f = i - (8 - n) -> 0 <= f -> nth (Z.to_nat f) dot 0 <> 0 ->
  i = 7 -> ct2_go n s dot i (S k) seg d = (E_RANGE, seg ++ [nth (Z.to_nat f) s 0], d).
Proof.
  intros n s dot i k seg d f Ef H0 H H7. subst f. cbn [ct2_go].
  replace (i - (8 - n) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (0 <=? i - (8 - n)) with true by (symmetry; apply Z.leb_le; lia).
  replace (nth (Z.to_nat (i - (8 - n))) dot 0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H).
  replace (i =? 7) with true by (symmetry; apply Z.eqb_eq; exact H7). reflexivity.
Qed.

Lemma ct2_step_dot : forall n s dot i k seg d f, f = i - (8 - n) -> 0 <= f -> nth (Z.to_nat f) dot 0 <> 0 ->
  i <> 7 -> ct2_go n s dot i (S k) seg d = ct2_go n s dot (i + 1) k (seg ++ [nth (Z.to_nat f) s 0]) (Z.lor d (2 ^ i)).
Proof.
  intros n s dot i k seg d f Ef H0 H H7. subst f. cbn [ct2_go].
  replace (i - (8 - n) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (0 <=? i - (8 - n)) with true by (symmetry; apply Z.leb_le; lia).
  replace (nth (Z.to_nat (i - (8 - n))) dot 0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H).
  replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact H7). reflexivity.
Qed.

Lemma bz_snoc : forall l v, bz (l ++ [v]) = bz l ++ [b8 v].
Proof. intros l v. unfold bz. rewrite map_app. reflexivity. Qed.

(* ---- loop 1: the text and ct1_owe ---- *)

Lemma skipn_cons_nth' : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.

Lemma zb_skipn_cons : forall tb k, (k < length tb)%nat ->
  skipn k (zb tb) = bv_unsigned (nth k tb (Z_to_bv 8 0)) :: skipn (S k) (zb tb).
Proof.
  intros tb k Hk. rewrite (skipn_cons_nth' (zb tb) k 0) by (unfold zb; rewrite length_map; lia). f_equal.
  unfold zb. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  apply (map_nth (fun b : byte => bv_unsigned b)).
Qed.

Lemma skipn_In0_len : forall (tb : list byte) k, In (b8 0) (skipn k tb) -> (k < length tb)%nat.
Proof.
  intros tb k H. destruct (Nat.lt_ge_cases k (length tb)) as [L|L]; [exact L|].
  rewrite skipn_all2 in H by lia. destruct H.
Qed.

Lemma skipn_In0_next : forall (tb : list byte) k, In (b8 0) (skipn k tb) ->
  bv_unsigned (nth k tb (Z_to_bv 8 0)) <> 0 -> In (b8 0) (skipn (S k) tb).
Proof.
  intros tb k H Hc. pose proof (skipn_In0_len tb k H) as L.
  rewrite (skipn_cons_nth' tb k (Z_to_bv 8 0) L) in H. destruct H as [E | H]; [|exact H].
  exfalso. apply Hc. rewrite E. reflexivity.
Qed.

Lemma ct1_end : forall rest n s dot, ct1_owe (0 :: rest) n s dot = Some (n, s, dot).
Proof. intros. reflexivity. Qed.

Lemma ct1_step_merge : forall c rest n s dot, c = 46 -> 0 < n -> nth (Z.to_nat (n - 1)) dot 0 = 0 ->
  ct1_owe (c :: rest) n s dot = ct1_owe rest n s (upd_at dot (n - 1) 1).
Proof.
  intros c rest n s dot Hc Hn Hd. subst c. cbn [ct1_owe].
  replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Hd. reflexivity.
Qed.

Lemma ct1_step_call : forall c rest n s dot, c <> 0 ->
  ((c =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)) = false ->
  ct1_owe (c :: rest) n s dot =
    (if (owed_seg7_spec (if c =? 46 then 32 else c) <? 0) || (n =? 8) then None
     else ct1_owe rest (n + 1) (s ++ [owed_seg7_spec (if c =? 46 then 32 else c)])
                  (upd_at dot n (if c =? 46 then 1 else 0))).
Proof.
  intros c rest n s dot H0 H. cbn [ct1_owe].
  replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). rewrite H. reflexivity.
Qed.

Lemma hnm_of : forall c n x, c <> 46 \/ n <= 0 \/ x <> 0 -> ((c =? 46) && (0 <? n) && (x =? 0)) = false.
Proof.
  intros c n x H.
  destruct (Z.eqb_spec c 46), (Z.ltb_spec 0 n), (Z.eqb_spec x 0); cbn [andb]; first [reflexivity | exfalso; lia].
Qed.

Lemma Forall_upd_at : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (upd_at l i v).
Proof.
  intros P l i v H Hv. unfold upd_at. generalize (Z.to_nat i) as j. clear i.
  induction H as [|x l Hx H IH]; intros j.
  - destruct j; cbn; (constructor; [exact Hv | constructor]).
  - destruct j as [|j]; cbn [firstn skipn app].
    + constructor; [exact Hv | exact H].
    + constructor; [exact Hx | apply IH].
Qed.

Lemma land255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof. intros c Hc. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma sw32 : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof. intros x Hx. apply bv_swrap_small. replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. lia. Qed.

(** addi a1, s9, -0x2e; seqz a1, a1: (c == '.') as an int. *)
Lemma seqz46 : forall c, 0 <= c < 256 ->
  Z.b2z ((c + -46) mod 18446744073709551616 <? 1) = (if c =? 46 then 1 else 0).
Proof.
  intros c Hc. destruct (Z.eqb_spec c 46) as [->|Hne]; [reflexivity|].
  replace ((c + -46) mod 18446744073709551616 <? 1) with false; [reflexivity|].
  symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

(** sllw a6, a4, a0 then or with lbu of *dots: the dots after digit i < 7 has a dot. *)
Lemma dots_or : forall d i, 0 <= d < 128 -> 0 <= i < 7 ->
  Z.lor (bv_unsigned (b8 d)) (bv_swrap 32 (Z.shiftl 1 (i mod 32)) mod 18446744073709551616) = Z.lor d (2 ^ i).
Proof.
  intros d i Hd Hi. rewrite b8_unsigned by lia. rewrite (Z.mod_small i 32) by lia. rewrite Z.shiftl_1_l.
  assert (H2 : 0 < 2 ^ i <= 2 ^ 6) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  change (2 ^ 6) with 64 in H2.
  rewrite bv_swrap_small by (replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity; lia).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma upd_len : forall {X} (l : list X) i x, length (upd l i x) = length l.
Proof. induction l; intros [|i] x; cbn; auto. Qed.

Lemma firstn_seg_step : forall segb segacc i v, (Z.to_nat i < length segb)%nat -> 0 <= i ->
  firstn (Z.to_nat i) segb = bz segacc -> firstn (Z.to_nat (i + 1)) (upd segb (Z.to_nat i) (b8 v)) = bz (segacc ++ [v]).
Proof.
  intros segb segacc i v H H0 H1. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_upd_snoc by lia. rewrite H1, bz_snoc. reflexivity.
Qed.

Lemma len_snoc : forall (segacc : list Z) i v, length segacc = Z.to_nat i -> 0 <= i ->
  length (segacc ++ [v]) = Z.to_nat (i + 1).
Proof. intros segacc i v H H0. rewrite length_app. cbn [length]. lia. Qed.

Lemma u8arr8 : forall m A l, u8arr rsegs m A l -> length l = 8%nat -> rw_cells rsegs m A [CB 8 l].
Proof. intros m A l H L. rewrite <- L. apply rw_cells_of_u8arr. exact H. Qed.

Lemma lor_dot : forall d i, 0 <= d < 128 -> 0 <= i < 7 -> 0 <= Z.lor d (2 ^ i) < 128.
Proof.
  intros d i Hd Hi. pose proof (lor_lt_pow2 d (2 ^ i) 7) as Hl. change (2 ^ 7) with 128 in Hl. apply Hl; [lia|].
  split; [apply Z.pow_nonneg; lia|]. change 128 with (2 ^ 7). apply Z.pow_lt_mono_r; lia.
Qed.

Ltac weq := first [ reflexivity | (f_equal; lia) | (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia) ].

(** A byte store into a u8arr at a variable index: rewrite the stored bytes to [b], the address to
    wa (A + i), update the array, then let store_done transport the rest. *)
Ltac u8_store H i b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
    lazymatch type of H with u8arr _ _ ?A ?l =>
      replace bs with [b] by (symmetry; first [ apply le1_unsigned | apply le1_b8; lia | reflexivity ]);
      change a with (wa (A + i));
      let H' := fresh "HW" in
      pose proof (u8arr_write rsegs mm A l i b H ltac:(lia)) as H';
      clear H; store_done; rename H' into H
    end
  end.

(** A word store (sw) into a u32arr at index i, the stored word being w. *)
Ltac u32_store H i w :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
    lazymatch type of H with u32arr _ _ ?A ?l =>
      change bs with (le4 w);
      replace a with (wa (A + 4 * i)) by (unfold wa; weq);
      let H' := fresh "HW" in
      pose proof (u32arr_write rsegs mm A l i w H ltac:(lia)) as H';
      clear H; store_done; rename H' into H
    end
  end.

Section OCT.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
          (pt pseg pdot : word) (tb sj : list byte) (dj : byte).

Hypothesis LO : lo + 128 <= bv_unsigned sp.
Hypothesis SP0 : bv_unsigned sp <= bv_unsigned pt.
Hypothesis SP1 : bv_unsigned sp <= bv_unsigned pseg.
Hypothesis SP2 : bv_unsigned sp <= bv_unsigned pdot.

Definition saved : list cell :=
  [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition Wf : list ivl :=
  [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned pseg, bv_unsigned pseg + 8);
   (bv_unsigned pdot, bv_unsigned pdot + 1)].

Definition POST (a0' : word) (m' : word -> option byte) : Prop :=
  let '(rc, sg, d) := owed_counter_text_spec (zb tb) in
  a0' = Z_to_bv 64 rc /\
  (rc = 0 -> rw_cells rsegs m' (bv_unsigned pseg) [CB 8 (bz sg)] /\ rw_cells rsegs m' (bv_unsigned pdot) [C1 (b8 d)]) /\
  (rc <> 0 -> exists sg' dv, rw_cells rsegs m' (bv_unsigned pseg) [CB 8 sg'] /\ rw_cells rsegs m' (bv_unsigned pdot) [C1 dv]).

Definition Q (ms' : machine_state) : Prop :=
  exists (a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch Wf m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    POST a0' m'.

(** The epilogue at 0x14fc8: a0 = a1, restore ra, s0..s9, pop the frame, return. *)
Lemma oct_exit : forall (ra' x8 x9 a0' rcw a2' a3' a4' a5' a6' x18 x19 x20 x21 x22 x23 x24 x25 : word)
                        (dw : list word) (sbs : list byte) (m1 : word -> option byte),
  length dw = 8%nat -> length sbs = 8%nat ->
  u32arr rsegs m1 (bv_unsigned sp + -128) dw ->
  u8arr rsegs m1 (bv_unsigned sp + -96) sbs ->
  rw_cells rsegs m1 (bv_unsigned sp + -88) saved ->
  stk rsegs m1 lo (bv_unsigned sp + -128) ->
  munch Wf m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  POST rcw m1 ->
  evt rsegs Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 x8 x9 a0' rcw a2' a3' a4' a5' a6' a7
             x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14fc8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' x8 x9 a0' rcw a2' a3' a4' a5' a6' x18 x19 x20 x21 x22 x23 x24 x25 dw sbs m1
    HL1 HL2 HD HS HSV ST MU WM HMI PO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold saved in HSV.
  do 12 zstep.
  apply rw_cells_of_u32arr in HD. apply rw_cells_of_u8arr in HS.
  rewrite HL1 in HD. rewrite HL2 in HS.
  eapply stk_release in HD; [ | exact ST | lia ]. cbn [cells_size csize Nat.add Nat.mul] in HD.
  replace (bv_unsigned sp + -128 + Z.of_nat 32) with (bv_unsigned sp + -96) in HD by lia.
  eapply stk_release in HS; [ | exact HD | lia ]. cbn [cells_size csize Nat.add] in HS.
  replace (bv_unsigned sp + -96 + Z.of_nat 8) with (bv_unsigned sp + -88) in HS by lia.
  eapply stk_release in HSV; [ | exact HS | lia ]. cbn [cells_size csize Nat.add] in HSV.
  replace (bv_unsigned sp + -88 + Z.of_nat 88) with (bv_unsigned sp) in HSV by lia.
  clear ST HD HS.
  zstep. zstep.
  finish.
Qed.

Definition dsj_ok : Prop := disj (bv_unsigned pseg) 8 (bv_unsigned pdot) 1.
Hypothesis DSJ : dsj_ok.

(** The state of loop 2 at its head 0x14f70: digit i = 8 - k next, k digits left; seg[0..i) holds the
    digits so far, *dots the dots so far. *)
Definition l2_ok (k : nat) : Prop :=
  forall (ra' a5' a6' x19 x20 x21 x22 x23 x24 x25 s1w s2w a0w a1w : word) (n i d : Z) (s dot segacc : list Z)
         (sbs segb : list byte) (m1 : word -> option byte),
  (1 <= k <= 8)%nat -> i = 8 - Z.of_nat k ->
  s1w = Z_to_bv 64 (bv_unsigned pseg + i) -> s2w = Z_to_bv 64 (n - 8) ->
  a0w = Z_to_bv 64 i -> a1w = Z_to_bv 64 (8 - i) ->
  0 <= n <= 8 -> length s = Z.to_nat n -> length dot = 8%nat -> Forall (fun v => 0 <= v <= 1) dot ->
  0 <= d < 128 -> length segacc = Z.to_nat i ->
  owed_counter_text_spec (zb tb) = ct2_go n s dot i k segacc d ->
  u32arr rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -96) sbs -> length sbs = 8%nat -> firstn (Z.to_nat n) sbs = bz s ->
  u8arr rsegs m1 (bv_unsigned pseg) segb -> length segb = 8%nat -> firstn (Z.to_nat i) segb = bz segacc ->
  rw_cells rsegs m1 (bv_unsigned pdot) [C1 (b8 d)] ->
  rw_cells rsegs m1 (bv_unsigned sp + -88) saved ->
  stk rsegs m1 lo (bv_unsigned sp + -128) ->
  munch Wf m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 pdot s1w
             a0w a1w (Z_to_bv 64 (bv_unsigned sp + -96)) (Z_to_bv 64 (bv_unsigned sp + -128))
             (Z_to_bv 64 1) a5' a6' a7 s2w x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f70) fc None m1 (seg_rom rsegs)).

(** The end of a digit at 0x14fb0: a1 -= 1, a0 += 1, s1 += 1, loop while a1 <> 0, else return 0. *)
Lemma l2_tail : forall k, l2_ok k ->
  forall (ra' a5' a6' x19 x20 x21 x22 x23 x24 x25 : word) (n i d : Z) (s dot segacc : list Z)
         (sbs segb : list byte) (m1 : word -> option byte),
  (k <= 7)%nat -> i = 7 - Z.of_nat k ->
  0 <= n <= 8 -> length s = Z.to_nat n -> length dot = 8%nat -> Forall (fun v => 0 <= v <= 1) dot ->
  0 <= d < 128 -> length segacc = Z.to_nat (i + 1) ->
  owed_counter_text_spec (zb tb) = ct2_go n s dot (i + 1) k segacc d ->
  u32arr rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -96) sbs -> length sbs = 8%nat -> firstn (Z.to_nat n) sbs = bz s ->
  u8arr rsegs m1 (bv_unsigned pseg) segb -> length segb = 8%nat -> firstn (Z.to_nat (i + 1)) segb = bz segacc ->
  rw_cells rsegs m1 (bv_unsigned pdot) [C1 (b8 d)] ->
  rw_cells rsegs m1 (bv_unsigned sp + -88) saved ->
  stk rsegs m1 lo (bv_unsigned sp + -128) ->
  munch Wf m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 pdot (Z_to_bv 64 (bv_unsigned pseg + i))
             (Z_to_bv 64 i) (Z_to_bv 64 (8 - i)) (Z_to_bv 64 (bv_unsigned sp + -96)) (Z_to_bv 64 (bv_unsigned sp + -128))
             (Z_to_bv 64 1) a5' a6' a7 (Z_to_bv 64 (n - 8)) x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14fb0) fc None m1 (seg_rom rsegs)).
Proof.
  intros k IH ra' a5' a6' x19 x20 x21 x22 x23 x24 x25 n i d s dot segacc sbs segb m1
    HK Hi Hn Hls Hld HFd Hd Hlg HSPEC HDOT HSB Hlsb HSBF HSEG Hlsg HSEGF HDS HSV ST MU WM HMI.
  unfold l2_ok in IH.
  pose proof (bv_unsigned_in_range 64 pseg) as Rpg. unfold bv_modulus in Rpg.
  pose proof (u8arr_bound _ _ _ _ HSEG) as BSEG. rewrite Hlsg in BSEG.
  do 4 zstep.
  if_cases B.
  - zify_cond B.
    eapply (IH ra' a5' a6' x19 x20 x21 x22 x23 x24 x25 _ _ _ _ n (i + 1) d s dot segacc sbs segb m1);
      first [ eassumption | weq | lia ].
  - zify_cond B.
    zstep.
    eapply oct_exit with (dw := map (Z_to_bv 64) dot) (sbs := sbs);
      [ rewrite length_map; exact Hld | exact Hlsb | exact HDOT | exact HSB | exact HSV | exact ST
      | exact MU | exact WM | exact HMI | ].
    assert (Hk0 : k = 0%nat) by lia. subst k.
    unfold POST. rewrite HSPEC. cbn [ct2_go].
    split; [ weq | split ].
    + intros _. split; [| exact HDS].
      assert (Esg : segb = bz segacc) by (rewrite <- HSEGF; rewrite firstn_all2; [reflexivity | lia]).
      rewrite <- Esg. apply u8arr8; assumption.
    + intros C. exfalso. apply C. reflexivity.
Qed.

Ltac tail_obl :=
  first [ eassumption | lia
        | (apply len_snoc; lia)
        | (rewrite upd_len; lia)
        | (apply firstn_seg_step; [ lia | lia | eassumption ]) ].

Lemma l2_body : forall k, l2_ok k -> l2_ok (S k).
Proof.
  intros k IH. pose proof (l2_tail k IH) as TAIL. clear IH. unfold l2_ok.
  intros ra' a5' a6' x19 x20 x21 x22 x23 x24 x25 s1w s2w a0w a1w n i d s dot segacc sbs segb m1
    HK Hi Es1 Es2 Ea0 Ea1 Hn Hls Hld HFd Hd Hlg HSPEC HDOT HSB Hlsb HSBF HSEG Hlsg HSEGF HDS HSV ST MU WM HMI.
  subst s1w s2w a0w a1w.
  assert (Hi8 : 0 <= i < 8) by lia.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 pseg) as Rpg.
  pose proof (bv_unsigned_in_range 64 pdot) as Rpd.
  pose proof DSJ as DSJ'. unfold dsj_ok, disj in DSJ'.
  unfold bv_modulus in Rsp, Rpg, Rpd.
  pose proof (u8arr_bound _ _ _ _ HSEG) as BSEG. rewrite Hlsg in BSEG.
  pose proof (u8arr_bound _ _ _ _ HSB) as BSB. rewrite Hlsb in BSB.
  pose proof (u32arr_bound _ _ _ _ HDOT) as BDOT. rewrite length_map, Hld in BDOT.
  assert (Hldm : length (map (Z_to_bv 64) dot) = 8%nat) by (rewrite length_map; exact Hld).
  unfold Wf in MU. unfold saved in HSV.
  assert (HS : store_ok rsegs m1 (Z_to_bv 64 (bv_unsigned pseg + i)) 1 = true)
    by (apply (u8arr_store_ok rsegs m1 (bv_unsigned pseg) segb i); [exact HSEG | lia | reflexivity]).
  zstep.
  rewrite (from_eq n i) by lia.
  zstep.
  if_cases B1.
  - (* from < 0: seg[i] = 0 *)
    zify_cond B1.
    assert (Hf : i - (8 - n) < 0) by (clear - B1 Hn Hi8; Z.div_mod_to_equations; lia).
    clear B1.
    zstep.
    u8_store HSEG i (b8 0).
    eapply (TAIL ra' _ _ x19 x20 x21 x22 x23 x24 x25 n i d s dot (segacc ++ [0]) sbs
             (upd segb (Z.to_nat i) (b8 0))).
    all: first [ (rewrite HSPEC; apply ct2_step_neg; lia) | tail_obl ].
  - zify_cond B1.
    assert (Hf : 0 <= i - (8 - n)) by (clear - B1 Hn Hi8; Z.div_mod_to_equations; lia).
    clear B1.
    remember (i - (8 - n)) as f eqn:Ef.
    assert (Hfn : f < n) by lia.
    zstep. zstep.
    rewrite (shl2 f).
    assert (HR1 : ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned sp + -96 + f)) 1
                  = Some [b8 (nth (Z.to_nat f) s 0)]).
    { apply (u8arr_read rsegs m1 (bv_unsigned sp + -96) sbs f); [exact HSB | | lia | reflexivity].
      rewrite nth_error_byte by lia. f_equal. apply (nth_firstn_bz sbs s (Z.to_nat n)); [exact HSBF | lia | lia]. }
    zstep. zstep.
    assert (Hdv : 0 <= nth (Z.to_nat f) dot 0 <= 1) by (apply (nth_Forall (fun v => 0 <= v <= 1)); [exact HFd | lia]).
    assert (HR2 : ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned sp + -128 + 4 * f)) 4
                  = Some (le4 (Z_to_bv 64 (nth (Z.to_nat f) dot 0)))).
    { apply (u32arr_read rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) f); [exact HDOT | | lia | reflexivity].
      apply nth_error_map_lit. lia. }
    zstep.
    rewrite (sx32_lit (nth (Z.to_nat f) dot 0)) by lia.
    zstep.
    u8_store HSEG i (b8 (nth (Z.to_nat f) s 0)).
    zstep.
    if_cases B2.
    + (* dot[from] = 0 *)
      zify_cond B2.
      eapply (TAIL ra' _ _ x19 x20 x21 x22 x23 x24 x25 n i d s dot (segacc ++ [nth (Z.to_nat f) s 0]) sbs
               (upd segb (Z.to_nat i) (b8 (nth (Z.to_nat f) s 0)))).
      all: first [ (rewrite HSPEC; apply (ct2_step_nodot n s dot i k segacc d f); lia) | tail_obl ].
    + zify_cond B2.
      zstep.
      if_cases B3.
      * (* i = 7 with a dot: E_RANGE *)
        zify_cond B3.
        zstep.
        eapply oct_exit with (dw := map (Z_to_bv 64) dot) (sbs := sbs);
          [ exact Hldm | exact Hlsb | exact HDOT | exact HSB | exact HSV | exact ST | exact MU | exact WM
          | exact HMI | ].
        unfold POST. rewrite HSPEC. rewrite (ct2_step_dot7 n s dot i k segacc d f) by lia.
        cbv beta iota zeta.
        split; [ unfold E_RANGE; reflexivity | split ].
        -- intros C. exfalso. unfold E_RANGE in C. lia.
        -- intros _. exists (upd segb (Z.to_nat i) (b8 (nth (Z.to_nat f) s 0))), (b8 d).
           split; [ apply u8arr8; [ exact HSEG | rewrite upd_len; exact Hlsg ] | exact HDS ].
      * (* a dot on digit i < 7: *dots |= 1 << i *)
        zify_cond B3.
        zstep. zstep. zstep.
        rewrite (dots_or d i) by lia.
        zstep.
        rewrite (le1_b8 (Z.lor d (2 ^ i))) by (pose proof (lor_dot d i ltac:(lia) ltac:(lia)); lia).
        mem_after_store.
        zstep.
        eapply (TAIL ra' _ _ x19 x20 x21 x22 x23 x24 x25 n i (Z.lor d (2 ^ i)) s dot
                 (segacc ++ [nth (Z.to_nat f) s 0]) sbs (upd segb (Z.to_nat i) (b8 (nth (Z.to_nat f) s 0)))).
        all: first [ (rewrite HSPEC; apply (ct2_step_dot n s dot i k segacc d f); lia) | (apply lor_dot; lia)
                   | tail_obl ].
Qed.

Lemma l2_loop : forall k, l2_ok k.
Proof.
  induction k as [|k IH]; [ unfold l2_ok; intros; lia | apply l2_body; exact IH ].
Qed.

(** Loop 1 has written only the frame: its footprint is inside Wf. *)
Lemma munch_Wf : forall m1, munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 -> munch Wf m m1.
Proof.
  intros m1 MU. eapply munch_weaken; [| exact MU]. unfold sub_fp, Wf. cbn [outside].
  intros x (H1 & H2 & H3 & _). split; [lia | exact I].
Qed.

(** 0x14f58: a0 = 0, *dots = 0, then loop 2 from digit 0 with the result (n, s, dot) of loop 1. *)
Lemma l2_init : forall (ra' a0' a1' a2' a3' a4' a5' a6' s2w x19 x20 x21 x22 x23 x24 x25 : word) (n : Z)
                       (s dot : list Z) (sbs : list byte) (m1 : word -> option byte),
  s2w = Z_to_bv 64 (n - 8) ->
  0 <= n <= 8 -> length s = Z.to_nat n -> length dot = 8%nat -> Forall (fun v => 0 <= v <= 1) dot ->
  ct1_owe (zb tb) 0 [] (repeat 0 8) = Some (n, s, dot) ->
  u32arr rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -96) sbs -> length sbs = 8%nat -> firstn (Z.to_nat n) sbs = bz s ->
  rw_cells rsegs m1 (bv_unsigned pseg) [CB 8 sj] -> rw_cells rsegs m1 (bv_unsigned pdot) [C1 dj] ->
  rw_cells rsegs m1 (bv_unsigned sp + -88) saved ->
  stk rsegs m1 lo (bv_unsigned sp + -128) ->
  munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 pdot pseg
             a0' a1' a2' a3' a4' a5' a6' a7 s2w x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f58) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' a0' a1' a2' a3' a4' a5' a6' s2w x19 x20 x21 x22 x23 x24 x25 n s dot sbs m1
    Es2 Hn Hls Hld HFd HCT HDOT HSB Hlsb HSBF HSJ HDJ HSV ST MU0 WM HMI.
  subst s2w.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 pseg) as Rpg.
  pose proof (bv_unsigned_in_range 64 pdot) as Rpd.
  pose proof DSJ as DSJ'. unfold dsj_ok, disj in DSJ'.
  unfold bv_modulus in Rsp, Rpg, Rpd.
  pose proof (munch_Wf m1 MU0) as MU. clear MU0. unfold Wf in MU. unfold saved in HSV.
  pose proof (u8arr_bound _ _ _ _ HSB) as BSB. rewrite Hlsb in BSB.
  pose proof (u32arr_bound _ _ _ _ HDOT) as BDOT. rewrite length_map, Hld in BDOT.
  assert (Hldm : length (map (Z_to_bv 64) dot) = 8%nat) by (rewrite length_map; exact Hld).
  zstep. zstep.
  rewrite (le1_b8 0) by lia.
  mem_after_store.
  do 4 zstep.
  assert (Hlsj : length sj = 8%nat) by (destruct HSJ as [[Hwf _] _]; cbn in Hwf; tauto).
  apply u8arr_of_rw_cells in HSJ.
  eapply (l2_loop 8 ra' _ _ x19 x20 x21 x22 x23 x24 x25 _ _ _ _ n 0 0 s dot [] sbs sj);
    first [ eassumption | lia | weq | (rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self) | reflexivity
          | (unfold owed_counter_text_spec; rewrite HCT; reflexivity) ].
Qed.

Hypothesis SEG7 : owed_seg7_contract.
Hypothesis RF : forall m1, munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 -> relro_img m1.

(** A return of -11 from loop 1: seg and *dots are the entry's. *)
Lemma post_fail : forall m1, owed_counter_text_spec (zb tb) = (E_RANGE, [], 0) ->
  rw_cells rsegs m1 (bv_unsigned pseg) [CB 8 sj] -> rw_cells rsegs m1 (bv_unsigned pdot) [C1 dj] ->
  POST (Z_to_bv 64 (-11)) m1.
Proof.
  intros m1 H HJ HD. unfold POST. rewrite H. cbv beta iota zeta. split; [reflexivity | split].
  - intros C. exfalso. unfold E_RANGE in C. lia.
  - intros _. exists sj, dj. split; assumption.
Qed.

(** The state of loop 1 at its head 0x14edc: c = tb[k] <> 0 is in s9, n digits are placed. *)
Definition l1_ok (fuel : nat) : Prop :=
  forall (ra' a0' a1' a2' a3' a4' a5' a6' s2w s3w s9w : word) (k n : Z) (s dot : list Z) (sbs : list byte)
         (m1 : word -> option byte),
  (Z.to_nat (Z.of_nat (length tb) - k) <= fuel)%nat -> 0 <= k ->
  s2w = Z_to_bv 64 n -> s3w = Z_to_bv 64 (bv_unsigned pt + k + 1) ->
  s9w = Z_to_bv 64 (bv_unsigned (nth (Z.to_nat k) tb (Z_to_bv 8 0))) ->
  bv_unsigned (nth (Z.to_nat k) tb (Z_to_bv 8 0)) <> 0 -> In (b8 0) (skipn (Z.to_nat k) tb) ->
  0 <= n <= 8 -> length s = Z.to_nat n -> length dot = 8%nat -> Forall (fun v => 0 <= v <= 1) dot ->
  ct1_owe (zb tb) 0 [] (repeat 0 8) = ct1_owe (skipn (Z.to_nat k) (zb tb)) n s dot ->
  u32arr rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -96) sbs -> length sbs = 8%nat -> firstn (Z.to_nat n) sbs = bz s ->
  bytes_at rsegs m1 (bv_unsigned pt) tb ->
  rw_cells rsegs m1 (bv_unsigned pseg) [CB 8 sj] -> rw_cells rsegs m1 (bv_unsigned pdot) [C1 dj] ->
  rw_cells rsegs m1 (bv_unsigned sp + -88) saved ->
  stk rsegs m1 lo (bv_unsigned sp + -128) ->
  munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 pdot pseg
             a0' a1' a2' a3' a4' a5' a6' a7 s2w s3w (Z_to_bv 64 46) (Z_to_bv 64 (bv_unsigned sp + -128))
             (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -96)) s9w s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14edc) fc None m1 (seg_rom rsegs)).

(** 0x14f34: char k is done; read tb[k+1], loop on it or end loop 1. *)
Lemma l1_next : forall fuel, l1_ok fuel ->
  forall (ra' a0' a1' a2' a3' a4' a5' a6' s2w s3w x25 : word) (k n : Z) (s dot : list Z) (sbs : list byte)
         (m1 : word -> option byte),
  (Z.to_nat (Z.of_nat (length tb) - (k + 1)) <= fuel)%nat -> 0 <= k ->
  s2w = Z_to_bv 64 n -> s3w = Z_to_bv 64 (bv_unsigned pt + k + 1) ->
  In (b8 0) (skipn (Z.to_nat (k + 1)) tb) ->
  0 <= n <= 8 -> length s = Z.to_nat n -> length dot = 8%nat -> Forall (fun v => 0 <= v <= 1) dot ->
  ct1_owe (zb tb) 0 [] (repeat 0 8) = ct1_owe (skipn (Z.to_nat (k + 1)) (zb tb)) n s dot ->
  u32arr rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -96) sbs -> length sbs = 8%nat -> firstn (Z.to_nat n) sbs = bz s ->
  bytes_at rsegs m1 (bv_unsigned pt) tb ->
  rw_cells rsegs m1 (bv_unsigned pseg) [CB 8 sj] -> rw_cells rsegs m1 (bv_unsigned pdot) [C1 dj] ->
  rw_cells rsegs m1 (bv_unsigned sp + -88) saved ->
  stk rsegs m1 lo (bv_unsigned sp + -128) ->
  munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 pdot pseg
             a0' a1' a2' a3' a4' a5' a6' a7 s2w s3w (Z_to_bv 64 46) (Z_to_bv 64 (bv_unsigned sp + -128))
             (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -96)) x25 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f34) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel IH ra' a0' a1' a2' a3' a4' a5' a6' s2w s3w x25 k n s dot sbs m1
    HF Hk Es2 Es3 HIN Hn Hls Hld HFd HCT HDOT HSB Hlsb HSBF HTB HSJ HDJ HSV ST MU WM HMI.
  subst s2w s3w. unfold l1_ok in IH.
  pose proof (skipn_In0_len tb _ HIN) as L.
  pose proof (bv_unsigned_in_range 64 pt) as Rpt. unfold bv_modulus in Rpt.
  pose proof (bytes_at_bound _ _ _ _ HTB) as BTB.
  assert (HR : ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned pt + k + 1)) 1
               = Some [nth (Z.to_nat (k + 1)) tb (Z_to_bv 8 0)]).
  { replace (bv_unsigned pt + k + 1) with (bv_unsigned pt + (k + 1)) by lia. apply oct_byte; [exact HTB | lia]. }
  zstep. zstep. zstep.
  if_cases B.
  - zify_cond B.
    eapply (IH ra' a0' a1' a2' a3' a4' a5' a6' _ _ _ (k + 1) n s dot sbs m1); first [ eassumption | lia | weq ].
  - zify_cond B.
    zstep. zstep.
    eapply (l2_init ra' a0' a1' a2' a3' a4' a5' a6' _ _ _ _ _ _ _ _ n s dot sbs m1).
    all: first [ eassumption | weq | lia
               | (rewrite HCT, (zb_skipn_cons tb (Z.to_nat (k + 1))) by lia; rewrite B; apply ct1_end) ].
Qed.

(** 0x14f00: a0 = (c == '.' ? ' ' : c); a0 &= 0xff; v = owed_seg7(a0); v < 0 or n == 8 returns -11, else
    dot[n] = (c == '.'), s[n++] = v. *)
Lemma l1_seg7 : forall fuel, l1_ok fuel ->
  forall (ra' a0w a1' a2' a3' a4' a5' a6' s2w s3w s9w : word) (k n c : Z) (s dot : list Z) (sbs : list byte)
         (m1 : word -> option byte),
  (Z.to_nat (Z.of_nat (length tb) - (k + 1)) <= fuel)%nat -> 0 <= k ->
  c = bv_unsigned (nth (Z.to_nat k) tb (Z_to_bv 8 0)) -> c <> 0 ->
  a0w = Z_to_bv 64 (if c =? 46 then 32 else c) ->
  s2w = Z_to_bv 64 n -> s3w = Z_to_bv 64 (bv_unsigned pt + k + 1) -> s9w = Z_to_bv 64 c ->
  In (b8 0) (skipn (Z.to_nat k) tb) ->
  ((c =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)) = false ->
  0 <= n <= 8 -> length s = Z.to_nat n -> length dot = 8%nat -> Forall (fun v => 0 <= v <= 1) dot ->
  ct1_owe (zb tb) 0 [] (repeat 0 8) = ct1_owe (skipn (Z.to_nat k) (zb tb)) n s dot ->
  u32arr rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -96) sbs -> length sbs = 8%nat -> firstn (Z.to_nat n) sbs = bz s ->
  bytes_at rsegs m1 (bv_unsigned pt) tb ->
  rw_cells rsegs m1 (bv_unsigned pseg) [CB 8 sj] -> rw_cells rsegs m1 (bv_unsigned pdot) [C1 dj] ->
  rw_cells rsegs m1 (bv_unsigned sp + -88) saved ->
  stk rsegs m1 lo (bv_unsigned sp + -128) ->
  munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 pdot pseg
             a0w a1' a2' a3' a4' a5' a6' a7 s2w s3w (Z_to_bv 64 46) (Z_to_bv 64 (bv_unsigned sp + -128))
             (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -96)) s9w s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f00) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel IH ra' a0w a1' a2' a3' a4' a5' a6' s2w s3w s9w k n c s dot sbs m1
    HF Hk Ec Hc0 Ea0 Es2 Es3 Es9 HIN HNM Hn Hls Hld HFd HCT HDOT HSB Hlsb HSBF HTB HSJ HDJ HSV ST MU WM HMI.
  subst a0w s2w s3w s9w.
  pose proof (skipn_In0_len tb _ HIN) as L.
  assert (Rc : 0 <= c < 256).
  { subst c. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) tb (Z_to_bv 8 0))) as R.
    unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R. }
  assert (HCT1 : ct1_owe (zb tb) 0 [] (repeat 0 8) = ct1_owe (c :: skipn (S (Z.to_nat k)) (zb tb)) n s dot).
  { rewrite HCT, (zb_skipn_cons tb (Z.to_nat k)) by lia. rewrite <- Ec. reflexivity. }
  rewrite (ct1_step_call c _ n s dot Hc0 HNM) in HCT1. clear HCT.
  remember (if c =? 46 then 32 else c) as cc eqn:Ecc.
  assert (Hcc : 0 <= cc < 256) by (subst cc; destruct (c =? 46); lia).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (u8arr_bound _ _ _ _ HSB) as BSB. rewrite Hlsb in BSB.
  pose proof (u32arr_bound _ _ _ _ HDOT) as BDOT. rewrite length_map, Hld in BDOT.
  assert (Hldm : length (map (Z_to_bv 64) dot) = 8%nat) by (rewrite length_map; exact Hld).
  zstep.
  rewrite (land255 cc) by lia.
  zstep.
  pose proof SEG7 as S7. unfold owed_seg7_contract, OWED_SEG7 in S7.
  eapply evt_cut;
    [ eapply S7 with (c := cc); unfold owed_seg7_pre;
      split; [lia | split; [reflexivity | split; [apply RF; exact MU | exact HMI]]] | ].
  clear S7.
  intros ms' [a1x [a2x [a3x [a4x [a5x [a6x ->]]]]]].
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
  destruct (owed_seg7_range cc) as [Ev | Ev].
  - (* v < 0: return -11 *)
    rewrite Ev in HCT1 |- *.
    zstep. zstep.
    if_cases B1.
    + assert (HSP : owed_counter_text_spec (zb tb) = (E_RANGE, [], 0))
        by (unfold owed_counter_text_spec; rewrite HCT1; reflexivity).
      eapply oct_exit with (dw := map (Z_to_bv 64) dot) (sbs := sbs);
        [ exact Hldm | exact Hlsb | exact HDOT | exact HSB | exact HSV | exact ST | apply munch_Wf; exact MU
        | exact WM | exact HMI | apply post_fail; assumption ].
    + exfalso. zify_cond B1. lia.
  - zstep. zstep.
    if_cases B1.
    + exfalso. zify_cond B1. lia.
    + zify_cond B1. zstep.
      if_cases B2.
      * (* n = 8: return -11 *)
        zify_cond B2.
        assert (HSP : owed_counter_text_spec (zb tb) = (E_RANGE, [], 0)).
        { unfold owed_counter_text_spec. rewrite HCT1.
          replace (n =? 8) with true by (symmetry; apply Z.eqb_eq; lia). rewrite orb_true_r. reflexivity. }
        eapply oct_exit with (dw := map (Z_to_bv 64) dot) (sbs := sbs);
          [ exact Hldm | exact Hlsb | exact HDOT | exact HSB | exact HSV | exact ST | apply munch_Wf; exact MU
          | exact WM | exact HMI | apply post_fail; assumption ].
      * zify_cond B2.
        zstep. zstep. rewrite (shl2 n). zstep.
        rewrite (seqz46 c) by lia.
        zstep.
        assert (HS1 : store_ok rsegs m1 (Z_to_bv 64 (bv_unsigned sp + -128 + 4 * n)) 4 = true)
          by (apply (u32arr_store_ok rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) n);
              [exact HDOT | lia | reflexivity]).
        zstep.
        u32_store HDOT n (Z_to_bv 64 (if c =? 46 then 1 else 0)).
        rewrite <- map_upd_at in HDOT by lia.
        assert (Hldm' : length (map (Z_to_bv 64) (upd_at dot n (if c =? 46 then 1 else 0))) = 8%nat)
          by (rewrite length_map, upd_length; lia).
        zstep. zstep.
        rewrite (sw32 (n + 1)) by lia.
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (HS2 : store_ok rsegs mm (Z_to_bv 64 (bv_unsigned sp + -96 + n)) 1 = true)
            by (apply (u8arr_store_ok rsegs mm (bv_unsigned sp + -96) sbs n); [exact HSB | lia | reflexivity]) end.
        zstep.
        u8_store HSB n (b8 (owed_seg7_spec cc)).
        eapply (l1_next fuel IH _ _ _ _ _ _ _ _ _ _ _ k (n + 1) (s ++ [owed_seg7_spec cc])
                 (upd_at dot n (if c =? 46 then 1 else 0)) (upd sbs (Z.to_nat n) (b8 (owed_seg7_spec cc)))).
        all: first [ eassumption | weq | lia
                   | (apply len_snoc; lia)
                   | (rewrite upd_len; lia)
                   | (rewrite upd_length; lia)
                   | (apply firstn_seg_step; [lia | lia | eassumption])
                   | (apply Forall_upd_at; [exact HFd | destruct (c =? 46); lia])
                   | (replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia;
                      apply skipn_In0_next; [exact HIN | rewrite <- Ec; exact Hc0])
                   | (rewrite HCT1; replace ((owed_seg7_spec cc <? 0) || (n =? 8)) with false
                        by (symmetry; apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.eqb_neq]; lia);
                      replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia; reflexivity) ].
Qed.

(** 0x14ef4: a0 = c, or ' ' for '.', then 0x14f00. *)
Lemma l1_call : forall fuel, l1_ok fuel ->
  forall (ra' a0' a1' a2' a3' a4' a5' a6' s2w s3w s9w : word) (k n c : Z) (s dot : list Z) (sbs : list byte)
         (m1 : word -> option byte),
  (Z.to_nat (Z.of_nat (length tb) - (k + 1)) <= fuel)%nat -> 0 <= k ->
  c = bv_unsigned (nth (Z.to_nat k) tb (Z_to_bv 8 0)) -> c <> 0 ->
  s2w = Z_to_bv 64 n -> s3w = Z_to_bv 64 (bv_unsigned pt + k + 1) -> s9w = Z_to_bv 64 c ->
  In (b8 0) (skipn (Z.to_nat k) tb) ->
  ((c =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)) = false ->
  0 <= n <= 8 -> length s = Z.to_nat n -> length dot = 8%nat -> Forall (fun v => 0 <= v <= 1) dot ->
  ct1_owe (zb tb) 0 [] (repeat 0 8) = ct1_owe (skipn (Z.to_nat k) (zb tb)) n s dot ->
  u32arr rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) ->
  u8arr rsegs m1 (bv_unsigned sp + -96) sbs -> length sbs = 8%nat -> firstn (Z.to_nat n) sbs = bz s ->
  bytes_at rsegs m1 (bv_unsigned pt) tb ->
  rw_cells rsegs m1 (bv_unsigned pseg) [CB 8 sj] -> rw_cells rsegs m1 (bv_unsigned pdot) [C1 dj] ->
  rw_cells rsegs m1 (bv_unsigned sp + -88) saved ->
  stk rsegs m1 lo (bv_unsigned sp + -128) ->
  munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Q
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 pdot pseg
             a0' a1' a2' a3' a4' a5' a6' a7 s2w s3w (Z_to_bv 64 46) (Z_to_bv 64 (bv_unsigned sp + -128))
             (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -96)) s9w s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ef4) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel IH ra' a0' a1' a2' a3' a4' a5' a6' s2w s3w s9w k n c s dot sbs m1
    HF Hk Ec Hc0 Es2 Es3 Es9 HIN HNM Hn Hls Hld HFd HCT HDOT HSB Hlsb HSBF HTB HSJ HDJ HSV ST MU WM HMI.
  pose proof (l1_seg7 fuel IH) as SEG. clear IH.
  assert (Rc : 0 <= c < 256).
  { subst c. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) tb (Z_to_bv 8 0))) as R.
    unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R. }
  subst s9w.
  zstep. zstep.
  if_cases E.
  - zify_cond E.
    eapply (SEG _ _ _ _ _ _ _ _ _ _ _ k n c s dot sbs m1);
      first [ eassumption | reflexivity | (rewrite (proj2 (Z.eqb_neq c 46) E); reflexivity) ].
  - zify_cond E. zstep.
    eapply (SEG _ _ _ _ _ _ _ _ _ _ _ k n c s dot sbs m1);
      first [ eassumption | reflexivity | (rewrite (proj2 (Z.eqb_eq c 46) E); reflexivity) ].
Qed.

(** 0x14edc: a '.' after a digit without one sets dot[n-1]; anything else goes to owed_seg7. *)
Lemma l1_body : forall fuel, l1_ok fuel -> l1_ok (S fuel).
Proof.
  intros fuel IH. pose proof (l1_call fuel IH) as CALL. pose proof (l1_next fuel IH) as NEXT. clear IH.
  unfold l1_ok.
  intros ra' a0' a1' a2' a3' a4' a5' a6' s2w s3w s9w k n s dot sbs m1
    HF Hk Es2 Es3 Es9 Hc0 HIN Hn Hls Hld HFd HCT HDOT HSB Hlsb HSBF HTB HSJ HDJ HSV ST MU WM HMI.
  pose proof (skipn_In0_len tb _ HIN) as L.
  assert (HF' : (Z.to_nat (Z.of_nat (length tb) - (k + 1)) <= fuel)%nat) by lia.
  remember (bv_unsigned (nth (Z.to_nat k) tb (Z_to_bv 8 0))) as c eqn:Ec.
  assert (Rc : 0 <= c < 256).
  { subst c. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) tb (Z_to_bv 8 0))) as R.
    unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R. }
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (u8arr_bound _ _ _ _ HSB) as BSB. rewrite Hlsb in BSB.
  pose proof (u32arr_bound _ _ _ _ HDOT) as BDOT. rewrite length_map, Hld in BDOT.
  assert (Hldm : length (map (Z_to_bv 64) dot) = 8%nat) by (rewrite length_map; exact Hld).
  subst s2w s3w s9w.
  zstep.
  if_cases E1.
  - zify_cond E1.
    eapply (CALL _ _ _ _ _ _ _ _ _ _ _ k n c s dot sbs m1);
      first [ eassumption | reflexivity | (apply hnm_of; left; exact E1) ].
  - zify_cond E1. zstep.
    if_cases E2.
    + zify_cond E2.
      assert (Hn0 : n <= 0) by (apply andb_false_iff in E2; destruct E2 as [E2 | E2]; apply Z.ltb_ge in E2; lia).
      eapply (CALL _ _ _ _ _ _ _ _ _ _ _ k n c s dot sbs m1);
        first [ eassumption | reflexivity | (apply hnm_of; right; left; exact Hn0) ].
    + zify_cond E2.
      zstep. rewrite (shl2 n). zstep.
      assert (Hdv : 0 <= nth (Z.to_nat (n - 1)) dot 0 <= 1)
        by (apply (nth_Forall (fun v => 0 <= v <= 1)); [exact HFd | lia]).
      assert (HR : ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned sp + -128 + 4 * (n - 1))) 4
                   = Some (le4 (Z_to_bv 64 (nth (Z.to_nat (n - 1)) dot 0)))).
      { apply (u32arr_read rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) (n - 1));
          [exact HDOT | | lia | reflexivity].
        apply nth_error_map_lit. lia. }
      zstep.
      rewrite (sx32_lit (nth (Z.to_nat (n - 1)) dot 0)) by lia.
      zstep.
      if_cases E4.
      * zify_cond E4.
        assert (HS : store_ok rsegs m1 (Z_to_bv 64 (bv_unsigned sp + -128 + 4 * (n - 1))) 4 = true)
          by (apply (u32arr_store_ok rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) (n - 1));
              [exact HDOT | lia | reflexivity]).
        zstep.
        u32_store HDOT (n - 1) (Z_to_bv 64 1).
        rewrite <- map_upd_at in HDOT by lia.
        zstep.
        eapply (NEXT _ _ _ _ _ _ _ _ _ _ _ k n s (upd_at dot (n - 1) 1) sbs).
        all: first [ eassumption | weq | lia
                   | (rewrite upd_length; lia)
                   | (apply Forall_upd_at; [exact HFd | lia])
                   | (replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia;
                      apply skipn_In0_next; [exact HIN | rewrite <- Ec; exact Hc0])
                   | (rewrite HCT, (zb_skipn_cons tb (Z.to_nat k)) by lia; rewrite <- Ec;
                      replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia;
                      apply ct1_step_merge; lia) ].
      * zify_cond E4.
        eapply (CALL _ _ _ _ _ _ _ _ _ _ _ k n c s dot sbs m1);
          first [ eassumption | reflexivity | (apply hnm_of; right; right; exact E4) ].
Qed.

Lemma l1_loop : forall fuel, l1_ok fuel.
Proof.
  induction fuel as [|fuel IH].
  - unfold l1_ok. intros ra' a0' a1' a2' a3' a4' a5' a6' s2w s3w s9w k n s dot sbs m1 HF Hk _ _ _ _ HIN.
    pose proof (skipn_In0_len tb _ HIN). lia.
  - apply l1_body. exact IH.
Qed.

(** 0x14e70: the prologue, c = tb[0], dot[8] = 0, then loop 1 or (empty text) loop 2. *)
Lemma oct_entry : forall (a3 a4 a5 a6 : word),
  bytes_at rsegs m (bv_unsigned pt) tb -> In (b8 0) tb ->
  rw_cells rsegs m (bv_unsigned pseg) [CB 8 sj] -> rw_cells rsegs m (bv_unsigned pdot) [C1 dj] ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 pt pseg pdot a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e70) fc None m (seg_rom rsegs)).
Proof.
  intros a3 a4 a5 a6 TB TZ SJ DJ MI ST.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 pt) as Rpt.
  pose proof (bytes_at_bound _ _ _ _ TB) as BTB.
  unfold bv_modulus in Rsp, Rpt.
  carve_frame 128%nat ST.
  do 14 zstep.
  assert (TL : (0 < length tb)%nat) by (destruct tb as [|b tb']; [destruct TZ | cbn; lia]).
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HB0 : ov_read_bytes rsegs mm pt 1 = Some [nth 0 tb (Z_to_bv 8 0)]) by
      (rewrite <- (Z_to_bv_bv_unsigned pt) at 1; rewrite <- (Z.add_0_r (bv_unsigned pt));
       apply (oct_byte mm (bv_unsigned pt) tb 0); [assumption | lia]) end.
  zstep.
  do 4 zstep.
  apply frame_split in FR. destruct FR as (HDOT & HSB & Hlsb & HSV).
  replace (bv_unsigned sp + -128 + 32) with (bv_unsigned sp + -96) in HSB by lia.
  replace (bv_unsigned sp + -128 + 40) with (bv_unsigned sp + -88) in HSV by lia.
  zstep.
  if_cases E0.
  - (* empty text *)
    zify_cond E0.
    zstep. zstep.
    eapply (l2_init _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 [] (repeat 0 8)).
    all: first [ eassumption | weq | lia | reflexivity
               | (apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia)
               | (rewrite <- (skipn_O (zb tb)), (zb_skipn_cons tb 0) by lia; rewrite E0; apply ct1_end) ].
  - zify_cond E0.
    do 7 zstep.
    eapply (l1_loop (length tb) _ _ _ _ _ _ _ _ _ _ _ 0 0 [] (repeat 0 8)).
    all: first [ eassumption | weq | lia | reflexivity
               | (apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia) ].
Qed.

End OCT.

Theorem owed_counter_text_holds : owed_seg7_contract -> owed_counter_text_contract.
Proof.
  intros SEG7. unfold owed_counter_text_contract, OWED_COUNTER_TEXT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo tb sj dj PRE.
  unfold owed_counter_text_pre, OWED_COUNTER_TEXT_DEPTH in PRE.
  destruct PRE as (A0 & [TB TZ] & A1 & SJ & A2 & DJ & DSJ & RI & D3 & SP0 & SP1 & SP2 & MI & ST & LO).
  eapply evt_mono.
  - eapply oct_entry.
    all: first [ eassumption | exact DSJ | (intros m1 HM; eapply relro_frame; eassumption) ].
  - intros ms' HQ. exact HQ.
Qed.
