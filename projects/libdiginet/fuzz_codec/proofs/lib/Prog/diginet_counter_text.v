(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 740 of its 758 lines of code are new or changed and 675 lines of the source are left out. *)
(** diginet_counter_text (diginet_codec.c:337-369; 104 instructions at 0x15b24, frame 0x80, calls diginet_seg7 at
    0x15bcc). The frame holds dot[8] (ints) at sp'+0..0x1f, s[8] at sp'+0x20..0x27 and the eleven saved
    registers at sp'+0x28..0x7f (sp' = sp - 0x80). Loop 1 (head 0x15ba4) is one step of ct1_lib per text byte,
    proved by induction on the bytes left; loop 2 (head 0x15c38) is one step of ct2_go per digit. *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_text
  diginet_seg7_c diginet_counter_text_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Local Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* ---- the Gallina side ---- *)

Definition ct_res (o : option (Z * list Z * list Z)) : Z * list Z * Z :=
  match o with None => (E_RANGE, [], 0) | Some (n, s, dot) => ct2 n s dot end.

(* the pattern the first loop asks of diginet_seg7 for the character ch *)
Definition ct1_v (ch : Z) : Z := seg7_spec (if ch =? 46 then 32 else ch).

Lemma skipn_nth_error : forall {A} (l : list A) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros A l. induction l as [|y l IH]; intros [|i] x H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn [skipn]. apply IH. exact H.
Qed.

Lemma skipn_zb : forall tb i b, nth_error tb i = Some b ->
  skipn i (zb tb) = bv_unsigned b :: skipn (S i) (zb tb).
Proof.
  induction tb as [|y tb IH]; intros [|i] b H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - change (skipn (S i) (zb (y :: tb))) with (skipn i (zb tb)).
    change (skipn (S (S i)) (zb (y :: tb))) with (skipn (S i) (zb tb)).
    apply IH. exact H.
Qed.

Lemma in_skipn_next : forall (l : list byte) i b x, nth_error l i = Some b -> b <> x ->
  In x (skipn i l) -> In x (skipn (S i) l).
Proof.
  intros l i b x E N H. rewrite (skipn_nth_error l i b E) in H. destruct H as [H|H]; [congruence | exact H].
Qed.

Lemma nth_error_some_len : forall (l : list byte) i, In (b8 0) (skipn i l) -> exists b, nth_error l i = Some b.
Proof.
  intros l i H. destruct (nth_error l i) as [b|] eqn:E; [eauto|].
  apply nth_error_None in E. rewrite skipn_all2 in H by exact E. destruct H.
Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma b8_ne0 : forall b : byte, bv_unsigned b <> 0 -> b <> b8 0.
Proof. intros b H E. apply H. rewrite E. reflexivity. Qed.

Lemma ct1_zero : forall rest n s dot, ct1_lib (0 :: rest) n s dot = Some (n, s, dot).
Proof. reflexivity. Qed.

Lemma ct1_dotset : forall rest n s dot, 0 < n -> nth (Z.to_nat (n - 1)) dot 0 = 0 ->
  ct1_lib (46 :: rest) n s dot = ct1_lib rest n s (upd_at dot (n - 1) 1).
Proof.
  intros rest n s dot Hn Hd. cbn [ct1_lib]. rewrite (proj2 (Z.ltb_lt 0 n) Hn), Hd. reflexivity.
Qed.

Lemma ct1_digit : forall ch rest n s dot, ch <> 0 ->
  ~ (ch = 46 /\ 0 < n /\ nth (Z.to_nat (n - 1)) dot 0 = 0) ->
  ct1_lib (ch :: rest) n s dot =
    if (ct1_v ch <? 0) || (n =? 8) then None
    else ct1_lib rest (n + 1) (s ++ [ct1_v ch]) (if ch =? 46 then upd_at dot n 1 else dot).
Proof.
  intros ch rest n s dot H0 Hd. cbn [ct1_lib]. rewrite (proj2 (Z.eqb_neq ch 0) H0).
  destruct ((ch =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)) eqn:E; [|reflexivity].
  exfalso. apply Hd. apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
  apply Z.eqb_eq in E1. apply Z.ltb_lt in E2. apply Z.eqb_eq in E3. auto.
Qed.

Lemma ct2_neg : forall n s dot i k sg d, n + -8 + i < 0 ->
  ct2_go n s dot i (S k) sg d = ct2_go n s dot (i + 1) k (sg ++ [0]) d.
Proof.
  intros n s dot i k sg d H. cbn [ct2_go]. replace (i - (8 - n)) with (n + -8 + i) by lia.
  rewrite (proj2 (Z.ltb_lt _ _) H), (proj2 (Z.leb_gt 0 _) H). reflexivity.
Qed.

Lemma ct2_nodot : forall n s dot i k sg d, 0 <= n + -8 + i -> nth (Z.to_nat (n + -8 + i)) dot 0 = 0 ->
  ct2_go n s dot i (S k) sg d = ct2_go n s dot (i + 1) k (sg ++ [nth (Z.to_nat (n + -8 + i)) s 0]) d.
Proof.
  intros n s dot i k sg d H H0. cbn [ct2_go]. replace (i - (8 - n)) with (n + -8 + i) by lia.
  rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.leb_le _ _) H), H0. reflexivity.
Qed.

Lemma ct2_dot : forall n s dot i k sg d, 0 <= n + -8 + i -> nth (Z.to_nat (n + -8 + i)) dot 0 <> 0 ->
  ct2_go n s dot i (S k) sg d =
    if i =? 7 then (E_RANGE, sg ++ [nth (Z.to_nat (n + -8 + i)) s 0], d)
    else ct2_go n s dot (i + 1) k (sg ++ [nth (Z.to_nat (n + -8 + i)) s 0]) (Z.lor d (2 ^ i)).
Proof.
  intros n s dot i k sg d H H0. cbn [ct2_go]. replace (i - (8 - n)) with (n + -8 + i) by lia.
  rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.leb_le _ _) H), (proj2 (Z.eqb_neq _ _) H0). reflexivity.
Qed.

Lemma ct_inv_mono : forall n dot, ct_inv n dot -> n < 8 -> ct_inv (n + 1) dot.
Proof. intros n dot (Hn & Hl & Hz) H. split; [lia|]. split; [exact Hl|]. intros j Hj. apply Hz. lia. Qed.

Lemma Forall_upd_at : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (upd_at l i v).
Proof.
  intros P l i v H Hv. unfold upd_at.
  pose proof (firstn_skipn (Z.to_nat i) l) as E1. pose proof (firstn_skipn (S (Z.to_nat i)) l) as E2.
  assert (H1 : Forall P (firstn (Z.to_nat i) l)) by (rewrite <- E1 in H; apply Forall_app in H; tauto).
  assert (H2 : Forall P (skipn (S (Z.to_nat i)) l)) by (rewrite <- E2 in H; apply Forall_app in H; tauto).
  apply Forall_app. split; [exact H1 | constructor; assumption].
Qed.

Lemma Forall_snoc : forall (P : Z -> Prop) l v, Forall P l -> P v -> Forall P (l ++ [v]).
Proof. intros P l v H Hv. apply Forall_app. split; [exact H | constructor; [exact Hv | constructor]]. Qed.

Lemma firstn_upd_snoc : forall (l : list byte) (j : nat) (xs : list Z) (v : Z),
  (j < length l)%nat -> firstn j l = bz xs -> firstn (S j) (upd l j (b8 v)) = bz (xs ++ [v]).
Proof.
  intros l j xs v Hj H. rewrite upd_firstn_skipn by exact Hj.
  assert (Lf : length (firstn j l) = j) by (apply firstn_length_le; lia).
  rewrite firstn_app, Lf. replace (S j - j)%nat with 1%nat by lia.
  rewrite (firstn_all2 (n := S j) (firstn j l)) by lia. cbn [firstn]. rewrite H.
  unfold bz. rewrite map_app. reflexivity.
Qed.

Lemma nth_error_firstn_bz : forall (l : list byte) (k j : nat) (xs : list Z),
  firstn k l = bz xs -> (j < k)%nat -> (k <= length l)%nat -> nth_error l j = Some (b8 (nth j xs 0)).
Proof.
  induction l as [|y l IH]; intros k j xs H Hj Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [lia|]. cbn [firstn] in H. destruct xs as [|x xs]; [discriminate H|].
  unfold bz in H. cbn [map] in H. injection H as Ey Et. change (map b8 xs) with (bz xs) in Et.
  destruct j as [|j].
  - cbn. rewrite Ey. reflexivity.
  - cbn [nth_error nth]. apply (IH k j xs); [exact Et | lia | lia].
Qed.

Lemma firstn_bz_all : forall (l : list byte) (xs : list Z), length l = 8%nat -> firstn 8 l = bz xs -> l = bz xs.
Proof. intros l xs Hl H. rewrite <- H. symmetry. apply firstn_all2. lia. Qed.

Lemma nth_error_map_w : forall (l : list Z) j, (j < length l)%nat ->
  nth_error (map (Z_to_bv 64) l) j = Some (Z_to_bv 64 (nth j l 0)).
Proof. intros l j H. rewrite nth_error_map, (nth_error_nth' l 0 H). reflexivity. Qed.

Lemma upd_map_w : forall (l : list Z) i v, (Z.to_nat i < length l)%nat ->
  upd (map (Z_to_bv 64) l) (Z.to_nat i) (Z_to_bv 64 v) = map (Z_to_bv 64) (upd_at l i v).
Proof.
  intros l i v H. rewrite upd_firstn_skipn by (rewrite length_map; exact H).
  unfold upd_at. rewrite map_app. cbn [map]. rewrite firstn_map, skipn_map. reflexivity.
Qed.

(* ---- machine values ---- *)

Lemma land_byte : forall b : byte, Z.land (bv_unsigned (zxb b)) 255 = bv_unsigned b.
Proof.
  intros b. pose proof (byte_range b) as R. unfold zxb. rewrite unsigned_lit by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.

Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply bv_swrap_small.
  change (bv_half_modulus 32) with 2147483648. lia.
Qed.

Lemma shl2 : forall x, 0 <= x < 2 ^ 61 -> Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 2 = 4 * x.
Proof. intros x Hx. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

Lemma swrap_add : forall a b, - 2 ^ 31 <= a + b < 2 ^ 31 ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 b)) = a + b.
Proof.
  intros a b H. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 31) with 2147483648 in H.
  Z.div_mod_to_equations. lia.
Qed.

Lemma swrap_inc : forall n, 0 <= n < 8 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 n) + 1) = n + 1.
Proof.
  intros n Hn. rewrite unsigned_lit by lia. apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia.
Qed.

Lemma sllw_pow : forall i, 0 <= i <= 6 ->
  bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 i) mod 32)) = 2 ^ i.
Proof.
  intros i Hi. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  assert (2 ^ i <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia). assert (0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia).
  apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. change (2 ^ 6) with 64 in *. lia.
Qed.

Lemma pow_small : forall i, 0 <= i <= 6 -> 0 < 2 ^ i <= 64.
Proof.
  intros i Hi. assert (2 ^ i <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia).
  assert (0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia). change (2 ^ 6) with 64 in *. lia.
Qed.

Lemma lor_small : forall d i, 0 <= d < 128 -> 0 <= i <= 6 -> 0 <= Z.lor d (2 ^ i) < 128.
Proof.
  intros d i Hd Hi. pose proof (pow_small i Hi). change 128 with (2 ^ 7). apply lor_lt_pow2; lia.
Qed.

Lemma bltz_cond : forall v, - 2 ^ 63 <= v < 2 ^ 63 -> bv_lts (Z_to_bv 64 v) (Z_to_bv 64 0) = (v <? 0).
Proof.
  intros v Hv. rewrite bv_lts_zero_r, unsigned_lit_wrap. apply eq_true_iff_eq. rewrite Z.leb_le, Z.ltb_lt.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 63) with 9223372036854775808 in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lts0_cond : forall v, 0 <= v < 2 ^ 63 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 v) = (0 <? v).
Proof.
  intros v Hv. rewrite bv_lts_zero_l, unsigned_lit by lia.
  destruct (Z.ltb_spec 0 v); cbn [andb]; [apply Z.ltb_lt; lia | reflexivity].
Qed.

Lemma seg7_arg : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 64 c) mod 256 = c.
Proof. intros c Hc. rewrite unsigned_lit by lia. apply Z.mod_small. exact Hc. Qed.

Lemma seg7_range : forall c, 0 <= c < 256 -> seg7_spec c = -1 \/ 0 <= seg7_spec c < 128.
Proof. intros c Hc. rewrite seg7_agree by exact Hc. apply owed_seg7_range. Qed.

Lemma ct1_v_range : forall ch, 0 <= ch < 256 -> ct1_v ch = -1 \/ 0 <= ct1_v ch < 128.
Proof. intros ch H. unfold ct1_v. destruct (ch =? 46); apply seg7_range; lia. Qed.

Lemma le1_b8 : forall v, 0 <= v < 2 ^ 64 -> le1 (Z_to_bv 64 v) = [b8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by exact Hv. reflexivity. Qed.

Lemma text_byte : forall m A (l : list byte) j b a, bytes_at rsegs m A l -> nth_error l j = Some b ->
  a = Z_to_bv 64 (A + Z.of_nat j) -> ov_read_bytes rsegs m a 1 = Some [b].
Proof.
  intros m A l j b a H E Ha. apply (u8ro_read rsegs m A l (Z.of_nat j) b a H); [rewrite Nat2Z.id; exact E | lia | exact Ha].
Qed.

(* ---- cells ---- *)

Lemma rw_cells_app_split : forall m A cs1 cs2,
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

Lemma rw_cells_CB_len : forall m A n bs, rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hn _]. exact Hn. Qed.

Lemma rw_cells_of_u32arr : forall m A ws, u32arr rsegs m A ws -> rw_cells rsegs m A [CB (4 * length ws) (u32s ws)].
Proof.
  intros m A ws [Hb Hw]. rewrite <- u32s_length. apply rw_cells_of_u8arr. split; [exact Hb|].
  rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact Hw.
Qed.

Lemma dot0_u32arr : forall m A,
  rw_cells rsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  u32arr rsegs m A (map (Z_to_bv 64) (repeat 0 8)).
Proof.
  intros m A [[_ Hb] Hw]. split.
  - replace (u32s (map (Z_to_bv 64) (repeat 0 8)))
      with (cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
      by (vm_compute; reflexivity).
    exact Hb.
  - exact Hw.
Qed.

Lemma stk_release_at : forall m lo A cs B, stk rsegs m lo A -> rw_cells rsegs m A cs -> lo <= A ->
  B = A + Z.of_nat (cells_size cs) -> stk rsegs m lo B.
Proof. intros m lo A cs B H1 H2 H3 ->. eapply stk_release; eassumption. Qed.

Lemma u_byte8 : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. pose proof (byte_range b). apply unsigned_lit. lia. Qed.

Ltac zc K := zify_cond K; rewrite ?u_byte8 in K.

Ltac weq := first [ reflexivity
                  | (rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self)
                  | (f_equal; lia)
                  | (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia) ].

(* ---- the walk ---- *)

Section CT.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (lo : Z) (tb : list byte).
Variable SEG7 : diginet_seg7_contract.
Hypothesis Rsp : 0 <= bv_unsigned sp < 2 ^ 64.
Hypothesis LO : lo + 128 <= bv_unsigned sp.
Hypothesis Hlo : 0 <= lo.
Hypothesis HT : bv_unsigned sp <= bv_unsigned a0.
Hypothesis HSG : bv_unsigned sp <= bv_unsigned a1.
Hypothesis HSGB : bv_unsigned a1 + 8 <= 2 ^ 64.
Hypothesis HDT : bv_unsigned sp <= bv_unsigned a2.
Hypothesis HDTB : bv_unsigned a2 + 1 <= 2 ^ 64.
Hypothesis HDJ : disj (bv_unsigned a1) 8 (bv_unsigned a2) 1.

Notation W := [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 8);
               (bv_unsigned a2, bv_unsigned a2 + 1)].
Notation saved := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Notation Sct pc x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1 :=
  (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
           x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

Definition RES (m' : word -> option byte) (res : Z * list Z * Z) (x : word) : Prop :=
  let '(rc, sg, d) := res in
  x = Z_to_bv 64 rc /\
  (rc = 0 -> rw_cells rsegs m' (bv_unsigned a1) [CB 8 (bz sg)] /\ rw_cells rsegs m' (bv_unsigned a2) [C1 (b8 d)]) /\
  (rc <> 0 -> exists sg' dv, rw_cells rsegs m' (bv_unsigned a1) [CB 8 sg'] /\ rw_cells rsegs m' (bv_unsigned a2) [C1 dv]).

Definition POST (res : Z * list Z * Z) (ms' : machine_state) : Prop :=
  exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - DIGINET_COUNTER_TEXT_DEPTH, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 8);
           (bv_unsigned a2, bv_unsigned a2 + 1)] m0 m' /\
    wmono rsegs m0 m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    RES m' res a0'.

(* the frame: dot as 8 ints, s as 8 bytes, the saved registers; and the footprint so far *)
Definition fr_ok (m1 : word -> option byte) (dot : list Z) (sbs : list byte) : Prop :=
  u32arr rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) /\
  u8arr rsegs m1 (bv_unsigned sp + -96) sbs /\
  rw_cells rsegs m1 (bv_unsigned sp + -88) saved /\
  stk rsegs m1 lo (bv_unsigned sp + -128) /\
  munch W m0 m1 /\ wmono rsegs m0 m1 /\ mem_inv rsegs m1.

(* the first loop's state: n digits placed, s their patterns, dot the 8 flags *)
Definition l1_inv (n : Z) (s dot : list Z) (sbs : list byte) : Prop :=
  ct_inv n dot /\ Forall (fun x => 0 <= x <= 1) dot /\ length s = Z.to_nat n /\
  Forall (fun v => 0 <= v < 128) s /\ length sbs = 8%nat /\ firstn (Z.to_nat n) sbs = bz s.

Ltac fr_close := unfold fr_ok; repeat match goal with |- _ /\ _ => split end; assumption.

Lemma res_err : forall m1 sg d sgb dv,
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sgb] -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  RES m1 (E_RANGE, sg, d) (Z_to_bv 64 (-11)).
Proof.
  intros m1 sg d sgb dv H1 H2. unfold RES. split; [reflexivity|].
  split; [intros H; exfalso; unfold E_RANGE in H; lia | intros _; exists sgb, dv; split; assumption].
Qed.

Lemma res_ok : forall m1 sg d,
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 (bz sg)] -> rw_cells rsegs m1 (bv_unsigned a2) [C1 (b8 d)] ->
  RES m1 (0, sg, d) (Z_to_bv 64 0).
Proof.
  intros m1 sg d H1 H2. unfold RES. split; [reflexivity|].
  split; [intros _; split; assumption | intros H; exfalso; apply H; reflexivity].
Qed.

(* 0x15c90: the epilogue *)
Lemma ct_exit : forall (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : word)
    (m1 : word -> option byte) (dot : list Z) (sbs : list byte) (res : Z * list Z * Z),
  length dot = 8%nat -> length sbs = 8%nat -> fr_ok m1 dot sbs -> RES m1 res x10 ->
  evt rsegs (POST res) (Sct 0x15c90 x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1).
Proof.
  intros x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1 dot sbs res
    Ld Lsb FRM HRES.
  destruct FRM as (DOT & SB & SV & STK & MU & WM & HMI).
  do 12 step.
  apply rw_cells_of_u32arr in DOT. apply rw_cells_of_u8arr in SB.
  pose proof (stk_release_at _ _ _ _ (bv_unsigned sp + -96) STK DOT ltac:(lia)
                ltac:(cbn [cells_size csize]; rewrite length_map, Ld; lia)) as ST1.
  pose proof (stk_release_at _ _ _ _ (bv_unsigned sp + -88) ST1 SB ltac:(lia)
                ltac:(cbn [cells_size csize]; rewrite Lsb; lia)) as ST2.
  pose proof (stk_release_at _ _ _ _ (bv_unsigned sp) ST2 SV ltac:(lia) ltac:(cbn [cells_size csize]; lia)) as ST3.
  clear ST1 ST2 STK.
  step.
  finish.
Qed.

Definition L2 (k : nat) : Prop :=
  forall (i d n : Z) (sg s dot : list Z) (res : Z * list Z * Z) (m1 : word -> option byte)
    (sbs segb : list byte) (dv : byte)
    (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : word),
  Z.of_nat k = 8 - i -> 0 <= i < 8 ->
  res = ct2_go n s dot i k sg d ->
  length sg = Z.to_nat i -> Forall (fun v => 0 <= v < 128) sg -> 0 <= d < 128 ->
  l1_inv n s dot sbs -> fr_ok m1 dot sbs ->
  length segb = 8%nat -> firstn (Z.to_nat i) segb = bz sg ->
  u8arr rsegs m1 (bv_unsigned a1) segb -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  x8 = a2 -> x9 = Z_to_bv 64 (bv_unsigned a1 + i) -> x10 = Z_to_bv 64 i -> x11 = Z_to_bv 64 d ->
  x12 = Z_to_bv 64 (8 - i) -> x13 = Z_to_bv 64 (bv_unsigned sp + -96) ->
  x14 = Z_to_bv 64 (bv_unsigned sp + -128) -> x15 = Z_to_bv 64 1 -> x18 = Z_to_bv 64 (n + -8) ->
  evt rsegs (POST res) (Sct 0x15c38 x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1).

(* 0x15c80: the second loop is done; store the dots and return 0 *)
Lemma l2_done : forall (d : Z) (sg dot : list Z) (res : Z * list Z * Z) (m1 : word -> option byte)
    (sbs : list byte) (dv : byte)
    (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : word),
  res = (0, sg, d) -> length sg = 8%nat -> 0 <= d < 128 -> length dot = 8%nat -> length sbs = 8%nat ->
  fr_ok m1 dot sbs -> u8arr rsegs m1 (bv_unsigned a1) (bz sg) -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  x8 = a2 -> x11 = Z_to_bv 64 d ->
  evt rsegs (POST res) (Sct 0x15c80 x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1).
Proof.
  intros d sg dot res m1 sbs dv x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    HR Lsg Hd Ld Lsb FRM SEGB DTC -> ->.
  pose proof HDJ as HDJ'. unfold disj in HDJ'.
  destruct FRM as (DOT & SB & SV & STK & MU & WM & HMI).
  assert (LDW : length (map (Z_to_bv 64) dot) = 8%nat) by (rewrite length_map; exact Ld).
  assert (LBZ : length (bz sg) = 8%nat) by (unfold bz; rewrite length_map; exact Lsg).
  step. step. step.
  rewrite unsigned_lit in DTC by lia.
  apply rw_cells_of_u8arr in SEGB. rewrite LBZ in SEGB.
  subst res. eapply ct_exit; [exact Ld | exact Lsb | fr_close | apply res_ok; assumption].
Qed.

(* 0x15c70: the bottom of the second loop *)
Lemma l2_tail : forall k, L2 k ->
  forall (i d n : Z) (sg s dot : list Z) (res : Z * list Z * Z) (m1 : word -> option byte)
    (sbs segb : list byte) (dv : byte)
    (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : word),
  Z.of_nat k = 8 - (i + 1) -> 0 <= i < 8 ->
  res = ct2_go n s dot (i + 1) k sg d ->
  length sg = Z.to_nat (i + 1) -> Forall (fun v => 0 <= v < 128) sg -> 0 <= d < 128 ->
  l1_inv n s dot sbs -> fr_ok m1 dot sbs ->
  length segb = 8%nat -> firstn (Z.to_nat (i + 1)) segb = bz sg ->
  u8arr rsegs m1 (bv_unsigned a1) segb -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  x8 = a2 -> x9 = Z_to_bv 64 (bv_unsigned a1 + i) -> x10 = Z_to_bv 64 i -> x11 = Z_to_bv 64 d ->
  x12 = Z_to_bv 64 (8 - i) -> x13 = Z_to_bv 64 (bv_unsigned sp + -96) ->
  x14 = Z_to_bv 64 (bv_unsigned sp + -128) -> x15 = Z_to_bv 64 1 -> x18 = Z_to_bv 64 (n + -8) ->
  evt rsegs (POST res) (Sct 0x15c70 x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1).
Proof.
  intros k IH i d n sg s dot res m1 sbs segb dv x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x24 x25 Hk Hi HR Lsg Fsg Hd INV FRM Lseg Fseg SEGB DTC E8 E9 E10 E11 E12 E13 E14 E15 E18.
  subst x8 x9 x10 x11 x12 x13 x14 x15 x18.
  step. step. step. step.
  if_cases K; zify_cond K.
  - eapply (IH (i + 1) d n sg s dot res m1 sbs segb dv); try eassumption; try lia; weq.
  - destruct k as [|k]; [|lia]. cbn [ct2_go] in HR.
    pose proof INV as ((Hn & Hld & Hz) & D01 & Ls & Fs & Lsb & Fsb).
    replace (Z.to_nat (i + 1)) with 8%nat in Lsg, Fseg by lia.
    rewrite (firstn_bz_all segb sg Lseg Fseg) in SEGB.
    eapply (l2_done d sg dot res m1 sbs dv); try eassumption; reflexivity.
Qed.

(* 0x15c38: one digit of the second loop *)
Lemma l2_step : forall k, L2 k -> L2 (S k).
Proof.
  intros k IH. unfold L2.
  intros i d n sg s dot res m1 sbs segb dv x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    Hk Hi HR Lsg Fsg Hd INV FRM Lseg Fseg SEGB DTC E8 E9 E10 E11 E12 E13 E14 E15 E18.
  subst x8 x9 x10 x11 x12 x13 x14 x15 x18.
  pose proof HDJ as HDJ'. unfold disj in HDJ'.
  pose proof INV as ((Hn & Hld & Hz) & D01 & Ls & Fs & Lsb & Fsb).
  destruct FRM as (DOT & SB & SV & STK & MU & WM & HMI).
  assert (LDW : length (map (Z_to_bv 64) dot) = 8%nat) by (rewrite length_map; exact Hld).
  (* 0x15c38 addw a6, s2, a0: from = n - 8 + i *)
  step. rewrite (swrap_add (n + -8) i) by lia.
  (* 0x15c3c bltz a6 *)
  step. rewrite (bltz_cond (n + -8 + i)) by lia.
  if_cases K.
  - (* from < 0: seg[i] = 0 *)
    apply Z.ltb_lt in K.
    pose proof (u8arr_store_ok rsegs m1 (bv_unsigned a1) segb i _ SEGB ltac:(lia) eq_refl) as HS.
    step. rewrite (le1_b8 0) by lia.
    pose proof (u8arr_write rsegs m1 (bv_unsigned a1) segb i (b8 0) SEGB ltac:(lia)) as SEGB'.
    store_done.
    assert (HR' : res = ct2_go n s dot (i + 1) k (sg ++ [0]) d) by (rewrite HR; apply ct2_neg; lia).
    assert (Lsg' : length (sg ++ [0]) = Z.to_nat (i + 1)) by (rewrite length_app; cbn [length]; lia).
    assert (Fsg' : Forall (fun v => 0 <= v < 128) (sg ++ [0])) by (apply Forall_snoc; [exact Fsg | lia]).
    assert (Lseg' : length (upd segb (Z.to_nat i) (b8 0)) = 8%nat) by (rewrite Arr.upd_length; exact Lseg).
    assert (Fseg' : firstn (Z.to_nat (i + 1)) (upd segb (Z.to_nat i) (b8 0)) = bz (sg ++ [0])).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply firstn_upd_snoc; [lia | exact Fseg]. }
    eapply (l2_tail k IH i d n (sg ++ [0]) s dot res _ sbs _ dv); try eassumption; try lia; try fr_close; weq.
  - (* from >= 0: seg[i] = s[from] *)
    apply Z.ltb_ge in K.
    assert (RS : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + -96 + (n + -8 + i))) 1
                 = Some [b8 (nth (Z.to_nat (n + -8 + i)) s 0)]).
    { apply (u8arr_read rsegs m1 (bv_unsigned sp + -96) sbs (n + -8 + i)); [exact SB | | lia | reflexivity].
      apply (nth_error_firstn_bz sbs (Z.to_nat n) _ s Fsb); lia. }
    assert (RD : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + -128 + 4 * (n + -8 + i))) 4
                 = Some (le4 (Z_to_bv 64 (nth (Z.to_nat (n + -8 + i)) dot 0)))).
    { apply (u32arr_read rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) (n + -8 + i));
        [exact DOT | | lia | reflexivity].
      apply nth_error_map_w. lia. }
    pose proof (nth_Forall (fun x => 0 <= x <= 1) dot (Z.to_nat (n + -8 + i)) 0 D01 ltac:(lia)) as Dv.
    pose proof (nth_Forall (fun v => 0 <= v < 128) s (Z.to_nat (n + -8 + i)) 0 Fs ltac:(lia)) as Sv.
    cbv beta in Dv, Sv.
    (* 0x15c40 add a7, a3, a6; 0x15c44 slli a6, a6, 2 *)
    step. step. rewrite (shl2 (n + -8 + i)) by lia.
    (* 0x15c48 lbu a7, 0(a7); 0x15c4c add a6, a4, a6; 0x15c50 lw a6, 0(a6) *)
    step. step. step. rewrite (sx32_small (nth (Z.to_nat (n + -8 + i)) dot 0)) by lia.
    (* 0x15c54 sb a7, 0(s1) *)
    pose proof (u8arr_store_ok rsegs m1 (bv_unsigned a1) segb i _ SEGB ltac:(lia) eq_refl) as HS.
    step. rewrite le1_zxb.
    pose proof (u8arr_write rsegs m1 (bv_unsigned a1) segb i (b8 (nth (Z.to_nat (n + -8 + i)) s 0)) SEGB
                  ltac:(lia)) as SEGB'.
    store_done.
    assert (Lsg' : length (sg ++ [nth (Z.to_nat (n + -8 + i)) s 0]) = Z.to_nat (i + 1))
      by (rewrite length_app; cbn [length]; lia).
    assert (Fsg' : Forall (fun v => 0 <= v < 128) (sg ++ [nth (Z.to_nat (n + -8 + i)) s 0]))
      by (apply Forall_snoc; [exact Fsg | exact Sv]).
    assert (Lseg' : length (upd segb (Z.to_nat i) (b8 (nth (Z.to_nat (n + -8 + i)) s 0))) = 8%nat)
      by (rewrite Arr.upd_length; exact Lseg).
    assert (Fseg' : firstn (Z.to_nat (i + 1)) (upd segb (Z.to_nat i) (b8 (nth (Z.to_nat (n + -8 + i)) s 0)))
                    = bz (sg ++ [nth (Z.to_nat (n + -8 + i)) s 0])).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply firstn_upd_snoc; [lia | exact Fseg]. }
    (* 0x15c58 beqz a6 *)
    step. if_cases K2; zify_cond K2.
    + rewrite (ct2_nodot n s dot i k sg d K K2) in HR.
      eapply (l2_tail k IH i d n _ s dot res _ sbs _ dv); try eassumption; try lia; try fr_close; weq.
    + rewrite (ct2_dot n s dot i k sg d K K2) in HR.
      (* 0x15c5c beq a2, a5 *)
      step. if_cases K3; zify_cond K3.
      * (* the rightmost digit has a dot *)
        rewrite (proj2 (Z.eqb_eq i 7) ltac:(lia)) in HR.
        step.
        subst res. eapply ct_exit; [exact Hld | exact Lsb | fr_close |].
        apply rw_cells_of_u8arr in SEGB'. rewrite Lseg' in SEGB'.
        eapply res_err; eassumption.
      * rewrite (proj2 (Z.eqb_neq i 7) ltac:(lia)) in HR.
        (* 0x15c60 sllw a6, a5, a0; 0x15c64 or a1, a1, a6; 0x15c68 j *)
        pose proof (pow_small i ltac:(lia)) as Pi.
        step. rewrite (sllw_pow i) by lia.
        step. rewrite (unsigned_lit d) by lia. rewrite (unsigned_lit (2 ^ i)) by lia.
        step.
        pose proof (lor_small d i Hd ltac:(lia)) as Hd'.
        eapply (l2_tail k IH i (Z.lor d (2 ^ i)) n _ s dot res _ sbs _ dv); try eassumption; try lia; try fr_close;
          weq.
Qed.

Lemma l2_all : forall k, L2 k.
Proof.
  induction k as [|k IH].
  - unfold L2. intros. lia.
  - apply l2_step. exact IH.
Qed.

(* 0x15c20: the setup of the second loop *)
Lemma l2_entry : forall (n : Z) (s dot : list Z) (res : Z * list Z * Z) (m1 : word -> option byte)
    (sbs sgb : list byte) (dv : byte)
    (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : word),
  res = ct2 n s dot -> l1_inv n s dot sbs -> fr_ok m1 dot sbs ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sgb] -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  x8 = a2 -> x9 = a1 -> x18 = Z_to_bv 64 (n + -8) ->
  evt rsegs (POST res) (Sct 0x15c20 x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1).
Proof.
  intros n s dot res m1 sbs sgb dv x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    HR INV FRM SGC DTC E8 E9 E18.
  subst x8 x9 x18.
  pose proof (rw_cells_CB_len _ _ _ _ SGC) as Lsgb. apply u8arr_of_rw_cells in SGC.
  do 6 step.
  eapply (l2_all 8 0 0 n [] s dot res m1 sbs sgb dv); try eassumption; try lia; try weq; try apply Forall_nil.
Qed.

Definition L1 (k : nat) : Prop :=
  forall (i : nat) (n : Z) (s dot : list Z) (b : byte) (res : Z * list Z * Z) (m1 : word -> option byte)
    (sbs sgb : list byte) (dv : byte)
    (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : word),
  (length tb - i = k)%nat -> nth_error tb i = Some b -> bv_unsigned b <> 0 -> In (b8 0) (skipn i tb) ->
  res = ct_res (ct1_lib (skipn i (zb tb)) n s dot) ->
  l1_inv n s dot sbs -> fr_ok m1 dot sbs ->
  bytes_at rsegs m1 (bv_unsigned a0) tb ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sgb] -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  x8 = a2 -> x9 = a1 -> x10 = zxb b -> x18 = Z_to_bv 64 n -> x19 = Z_to_bv 64 (bv_unsigned a0 + Z.of_nat i + 1) ->
  x20 = Z_to_bv 64 46 -> x21 = Z_to_bv 64 (bv_unsigned sp + -128) -> x22 = Z_to_bv 64 1 -> x23 = Z_to_bv 64 8 ->
  x24 = Z_to_bv 64 (bv_unsigned sp + -96) ->
  evt rsegs (POST res) (Sct 0x15ba4 x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1).

(* 0x15bfc: read the next text byte; loop or leave the first loop *)
Lemma l1_next : forall k, L1 k ->
  forall (i : nat) (n : Z) (s dot : list Z) (res : Z * list Z * Z) (m1 : word -> option byte)
    (sbs sgb : list byte) (dv : byte)
    (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : word),
  (length tb - S i = k)%nat -> In (b8 0) (skipn (S i) tb) ->
  res = ct_res (ct1_lib (skipn (S i) (zb tb)) n s dot) ->
  l1_inv n s dot sbs -> fr_ok m1 dot sbs ->
  bytes_at rsegs m1 (bv_unsigned a0) tb ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sgb] -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  x8 = a2 -> x9 = a1 -> x18 = Z_to_bv 64 n -> x19 = Z_to_bv 64 (bv_unsigned a0 + Z.of_nat i + 1) ->
  x20 = Z_to_bv 64 46 -> x21 = Z_to_bv 64 (bv_unsigned sp + -128) -> x22 = Z_to_bv 64 1 -> x23 = Z_to_bv 64 8 ->
  x24 = Z_to_bv 64 (bv_unsigned sp + -96) ->
  evt rsegs (POST res) (Sct 0x15bfc x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1).
Proof.
  intros k L i n s dot res m1 sbs sgb dv x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    Hk HZ HR INV FRM TX SGC DTC E8 E9 E18 E19 E20 E21 E22 E23 E24.
  subst x8 x9 x18 x19 x20 x21 x22 x23 x24.
  pose proof INV as ((Hn & Hld & Hz) & D01 & Ls & Fs & Lsb & Fsb).
  destruct (nth_error_some_len tb (S i) HZ) as [b' E'].
  assert (Hi : (S i < length tb)%nat) by (apply nth_error_Some; rewrite E'; discriminate).
  pose proof (text_byte m1 (bv_unsigned a0) tb (S i) b' (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat i + 1)) TX E'
                ltac:(f_equal; lia)) as RD.
  (* 0x15bfc lbu a0, 0(s3); 0x15c00 addi s3, s3, 1; 0x15c04 bnez a0 *)
  step. step. step.
  if_cases K; zc K.
  - eapply (L (S i) n s dot b' res m1 sbs sgb dv); try eassumption; try lia; try weq.
  - rewrite (skipn_zb tb (S i) b' E'), K, ct1_zero in HR. cbn [ct_res] in HR.
    (* 0x15c08 j 0x15c1c; 0x15c1c addi s2, s2, -8 *)
    step. step.
    eapply (l2_entry n s dot res m1 sbs sgb dv); try eassumption; try weq.
Qed.

(* 0x15bf0: s[n] = v, n + 1 *)
Lemma l1_put : forall k, L1 k ->
  forall (i : nat) (n v : Z) (s dot : list Z) (res : Z * list Z * Z) (m1 : word -> option byte)
    (sbs sgb : list byte) (dv : byte)
    (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : word),
  (length tb - S i = k)%nat -> In (b8 0) (skipn (S i) tb) ->
  res = ct_res (ct1_lib (skipn (S i) (zb tb)) (n + 1) (s ++ [v]) dot) ->
  0 <= n < 8 -> 0 <= v < 128 -> ct_inv (n + 1) dot -> Forall (fun x => 0 <= x <= 1) dot ->
  length s = Z.to_nat n -> Forall (fun v => 0 <= v < 128) s -> length sbs = 8%nat ->
  firstn (Z.to_nat n) sbs = bz s ->
  fr_ok m1 dot sbs ->
  bytes_at rsegs m1 (bv_unsigned a0) tb ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sgb] -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  x8 = a2 -> x9 = a1 -> x11 = Z_to_bv 64 v -> x18 = Z_to_bv 64 n ->
  x19 = Z_to_bv 64 (bv_unsigned a0 + Z.of_nat i + 1) ->
  x20 = Z_to_bv 64 46 -> x21 = Z_to_bv 64 (bv_unsigned sp + -128) -> x22 = Z_to_bv 64 1 -> x23 = Z_to_bv 64 8 ->
  x24 = Z_to_bv 64 (bv_unsigned sp + -96) ->
  evt rsegs (POST res) (Sct 0x15bf0 x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1).
Proof.
  intros k L i n v s dot res m1 sbs sgb dv x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    Hk HZ HR Hn Hv CI D01 Ls Fs Lsb Fsb FRM TX SGC DTC E8 E9 E11 E18 E19 E20 E21 E22 E23 E24.
  subst x8 x9 x11 x18 x19 x20 x21 x22 x23 x24.
  destruct FRM as (DOT & SB & SV & STK & MU & WM & HMI).
  pose proof CI as (Hn1 & Hld & Hz).
  assert (LDW : length (map (Z_to_bv 64) dot) = 8%nat) by (rewrite length_map; exact Hld).
  (* 0x15bf0 add a0, s8, s2; 0x15bf4 addiw s2, s2, 1 *)
  step. step. rewrite (swrap_inc n) by lia.
  (* 0x15bf8 sb a1, 0(a0) *)
  pose proof (u8arr_store_ok rsegs m1 (bv_unsigned sp + -96) sbs n _ SB ltac:(lia) eq_refl) as HS.
  step. rewrite (le1_b8 v) by lia.
  pose proof (u8arr_write rsegs m1 (bv_unsigned sp + -96) sbs n (b8 v) SB ltac:(lia)) as SB'.
  store_done.
  assert (INV' : l1_inv (n + 1) (s ++ [v]) dot (upd sbs (Z.to_nat n) (b8 v))).
  { split; [exact CI|]. split; [exact D01|]. split; [rewrite length_app; cbn [length]; lia|].
    split; [apply Forall_snoc; [exact Fs | lia]|]. split; [rewrite Arr.upd_length; exact Lsb|].
    replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia. apply firstn_upd_snoc; [lia | exact Fsb]. }
  eapply (l1_next k L i (n + 1) (s ++ [v]) dot res _ _ sgb dv); try eassumption; try fr_close; try weq.
Qed.

(* 0x15bd0: after diginet_seg7 returned the pattern v of the character *)
Lemma l1_after : forall k, L1 k ->
  forall (i : nat) (n : Z) (s dot : list Z) (b : byte) (res : Z * list Z * Z) (m1 : word -> option byte)
    (sbs sgb : list byte) (dv : byte)
    (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : word),
  (length tb - S i = k)%nat -> In (b8 0) (skipn (S i) tb) ->
  res = ct_res (if (ct1_v (bv_unsigned b) <? 0) || (n =? 8) then None
                else ct1_lib (skipn (S i) (zb tb)) (n + 1) (s ++ [ct1_v (bv_unsigned b)])
                       (if bv_unsigned b =? 46 then upd_at dot n 1 else dot)) ->
  l1_inv n s dot sbs -> fr_ok m1 dot sbs ->
  bytes_at rsegs m1 (bv_unsigned a0) tb ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sgb] -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  x8 = a2 -> x9 = a1 -> x10 = Z_to_bv 64 (ct1_v (bv_unsigned b)) -> x18 = Z_to_bv 64 n ->
  x19 = Z_to_bv 64 (bv_unsigned a0 + Z.of_nat i + 1) ->
  x20 = Z_to_bv 64 46 -> x21 = Z_to_bv 64 (bv_unsigned sp + -128) -> x22 = Z_to_bv 64 1 -> x23 = Z_to_bv 64 8 ->
  x24 = Z_to_bv 64 (bv_unsigned sp + -96) -> x25 = Z_to_bv 64 (bv_unsigned b) ->
  evt rsegs (POST res) (Sct 0x15bd0 x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1).
Proof.
  intros k L i n s dot b res m1 sbs sgb dv x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    Hk HZ HR INV FRM TX SGC DTC E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25.
  subst x8 x9 x10 x18 x19 x20 x21 x22 x23 x24 x25.
  pose proof (byte_range b) as Rb.
  pose proof (ct1_v_range (bv_unsigned b) Rb) as Rv.
  pose proof INV as ((Hn & Hld & Hz) & D01 & Ls & Fs & Lsb & Fsb).
  pose proof FRM as (DOT & SB & SV & STK & MU & WM & HMI).
  assert (LDW : length (map (Z_to_bv 64) dot) = 8%nat) by (rewrite length_map; exact Hld).
  (* 0x15bd0 mv a1, a0; 0x15bd4 addi a0, zero, -11; 0x15bd8 bltz a1 *)
  step. step. step. rewrite (bltz_cond (ct1_v (bv_unsigned b))) by lia.
  if_cases K2.
  - try rewrite K2 in HR. cbn [orb ct_res] in HR. subst res.
    eapply ct_exit; [exact Hld | exact Lsb | exact FRM | ]. all: try (eapply res_err; eassumption).
  - try rewrite K2 in HR. cbn [orb] in HR. cbv iota in HR. apply Z.ltb_ge in K2.
    (* 0x15bdc beq s2, s7 *)
    step. if_cases K3; zify_cond K3.
    + rewrite (proj2 (Z.eqb_eq n 8) K3) in HR. cbn [ct_res] in HR. subst res.
      eapply ct_exit; [exact Hld | exact Lsb | exact FRM | ]. all: try (eapply res_err; eassumption).
    + rewrite (proj2 (Z.eqb_neq n 8) K3) in HR. cbv iota in HR.
      (* 0x15be0 bne s9, s4, 0x15bf0 *)
      step. if_cases K4; zc K4.
      * rewrite (proj2 (Z.eqb_neq _ 46) K4) in HR. cbv iota in HR.
        eapply (l1_put k L i n (ct1_v (bv_unsigned b)) s dot res m1 sbs sgb dv); try eassumption; try lia;
          try weq.
        all: try (apply ct_inv_mono; [exact (proj1 INV) | lia]).
      * rewrite (proj2 (Z.eqb_eq _ 46) K4) in HR. cbv iota in HR.
        (* 0x15be4 slli a0, s2, 2; 0x15be8 add a0, s5, a0; 0x15bec sw s6, 0(a0): dot[n] = 1 *)
        step. rewrite (shl2 n) by lia. step.
        pose proof (u32arr_store_ok rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) n _ DOT ltac:(lia)
                      eq_refl) as HS.
        step.
        pose proof (u32arr_write rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) n (Z_to_bv 64 1) DOT
                      ltac:(lia)) as DOT'.
        store_done.
        rewrite (upd_map_w dot n 1) in DOT' by lia.
        eapply (l1_put k L i n (ct1_v (bv_unsigned b)) s (upd_at dot n 1) res _ sbs sgb dv); try eassumption;
          try lia; try fr_close; try weq.
        all: try (apply ct_inv_next; [exact (proj1 INV) | lia]).
        all: try (apply Forall_upd_at; [exact D01 | lia]).
Qed.

(* 0x15bc0: a character that does not set the dot of the digit before it *)
Lemma l1_digit : forall k, L1 k ->
  forall (i : nat) (n : Z) (s dot : list Z) (b : byte) (res : Z * list Z * Z) (m1 : word -> option byte)
    (sbs sgb : list byte) (dv : byte)
    (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : word),
  (length tb - S i = k)%nat -> bv_unsigned b <> 0 -> In (b8 0) (skipn (S i) tb) ->
  ~ (bv_unsigned b = 46 /\ 0 < n /\ nth (Z.to_nat (n - 1)) dot 0 = 0) ->
  res = ct_res (ct1_lib (bv_unsigned b :: skipn (S i) (zb tb)) n s dot) ->
  l1_inv n s dot sbs -> fr_ok m1 dot sbs ->
  bytes_at rsegs m1 (bv_unsigned a0) tb ->
  rw_cells rsegs m1 (bv_unsigned a1) [CB 8 sgb] -> rw_cells rsegs m1 (bv_unsigned a2) [C1 dv] ->
  x8 = a2 -> x9 = a1 -> x10 = zxb b -> x18 = Z_to_bv 64 n -> x19 = Z_to_bv 64 (bv_unsigned a0 + Z.of_nat i + 1) ->
  x20 = Z_to_bv 64 46 -> x21 = Z_to_bv 64 (bv_unsigned sp + -128) -> x22 = Z_to_bv 64 1 -> x23 = Z_to_bv 64 8 ->
  x24 = Z_to_bv 64 (bv_unsigned sp + -96) -> x25 = Z_to_bv 64 (bv_unsigned b) ->
  evt rsegs (POST res) (Sct 0x15bc0 x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 m1).
Proof.
  intros k L i n s dot b res m1 sbs sgb dv x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    Hk Hb0 HZ ND HR INV FRM TX SGC DTC E8 E9 E10 E18 E19 E20 E21 E22 E23 E24 E25.
  subst x8 x9 x10 x18 x19 x20 x21 x22 x23 x24 x25.
  rewrite (ct1_digit (bv_unsigned b) _ n s dot Hb0 ND) in HR.
  pose proof (byte_range b) as Rb.
  pose proof FRM as (DOT & SB & SV & STK & MU & WM & HMI).
  (* 0x15bc0 bne s9, s4, 0x15bc8 *)
  step. if_cases K; zc K.
  - (* not '.': 0x15bc8 andi a0, a0, 0xff; 0x15bcc jal diginet_seg7 *)
    step. rewrite land_byte. step.
    eapply evt_cut; [eapply SEG7; exact HMI|]. intros ms' [y11 ->].
    replace (ret_pc (Z_to_bv 64 0x15bd0)) with (Z_to_bv 64 0x15bd0)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (seg7_arg (bv_unsigned b) Rb).
    eapply (l1_after k L i n s dot b res m1 sbs sgb dv); try eassumption; try weq.
    all: try (unfold ct1_v; rewrite (proj2 (Z.eqb_neq _ 46) K); reflexivity).
  - (* '.': 0x15bc4 addi a0, zero, 0x20; 0x15bc8 andi; 0x15bcc jal diginet_seg7 *)
    step. step. step.
    eapply evt_cut; [eapply SEG7; exact HMI|]. intros ms' [y11 ->].
    replace (ret_pc (Z_to_bv 64 0x15bd0)) with (Z_to_bv 64 0x15bd0)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    eapply (l1_after k L i n s dot b res m1 sbs sgb dv); try eassumption; try weq.
    all: try (unfold ct1_v; rewrite K; vm_compute; reflexivity).
Qed.

(* 0x15ba4: one character of the first loop *)
Lemma l1_step : forall k, L1 k -> L1 (S k).
Proof.
  intros k L. unfold L1.
  intros i n s dot b res m1 sbs sgb dv x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    Hk Eb Hb0 HZ HR INV FRM TX SGC DTC E8 E9 E10 E18 E19 E20 E21 E22 E23 E24.
  subst x8 x9 x10 x18 x19 x20 x21 x22 x23 x24.
  rewrite (skipn_zb tb i b Eb) in HR.
  pose proof (in_skipn_next tb i b (b8 0) Eb (b8_ne0 b Hb0) HZ) as HZ'.
  assert (Hk' : (length tb - S i = k)%nat) by lia.
  pose proof (byte_range b) as Rb.
  pose proof INV as ((Hn & Hld & Hz) & D01 & Ls & Fs & Lsb & Fsb).
  pose proof FRM as (DOT & SB & SV & STK & MU & WM & HMI).
  assert (LDW : length (map (Z_to_bv 64) dot) = 8%nat) by (rewrite length_map; exact Hld).
  (* 0x15ba4 andi s9, a0, 0xff *)
  step. rewrite land_byte.
  (* 0x15ba8 bne s9, s4, 0x15bc0 *)
  step. if_cases K1; zc K1.
  - eapply (l1_digit k L i n s dot b res m1 sbs sgb dv); try eassumption; try weq. all: try intuition.
  - (* '.': 0x15bac blez s2, 0x15bc0 *)
    step. rewrite (lts0_cond n) by lia.
    if_cases K2.
    + apply negb_true_iff, Z.ltb_ge in K2.
      eapply (l1_digit k L i n s dot b res m1 sbs sgb dv); try eassumption; try weq. all: try lia.
    + apply negb_false_iff, Z.ltb_lt in K2.
      (* 0x15bb0 slli a1, s2, 2; 0x15bb4 add a1, a1, s5; 0x15bb8 lw a2, -4(a1) *)
      assert (RD : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + -128 + 4 * (n - 1))) 4
                   = Some (le4 (Z_to_bv 64 (nth (Z.to_nat (n - 1)) dot 0)))).
      { apply (u32arr_read rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) (n - 1));
          [exact DOT | | lia | reflexivity].
        apply nth_error_map_w. lia. }
      pose proof (nth_Forall (fun x => 0 <= x <= 1) dot (Z.to_nat (n - 1)) 0 D01 ltac:(lia)) as Dv.
      cbv beta in Dv.
      step. rewrite (shl2 n) by lia. step. step.
      rewrite (sx32_small (nth (Z.to_nat (n - 1)) dot 0)) by lia.
      (* 0x15bbc beqz a2, 0x15c0c *)
      step. if_cases K3; zify_cond K3.
      * (* 0x15c0c sw s6, -4(a1): dot[n - 1] = 1; 0x15c10 j 0x15bfc *)
        pose proof (u32arr_store_ok rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) (n - 1) _ DOT
                      ltac:(lia) eq_refl) as HS.
        step.
        pose proof (u32arr_write rsegs m1 (bv_unsigned sp + -128) (map (Z_to_bv 64) dot) (n - 1) (Z_to_bv 64 1)
                      DOT ltac:(lia)) as DOT'.
        store_done.
        rewrite (upd_map_w dot (n - 1) 1) in DOT' by lia.
        step.
        rewrite K1, (ct1_dotset _ n s dot K2 K3) in HR.
        assert (INV' : l1_inv n s (upd_at dot (n - 1) 1) sbs).
        { split; [apply ct_inv_dot; [exact (proj1 INV) | lia]|]. split; [apply Forall_upd_at; [exact D01 | lia]|].
          repeat split; assumption. }
        eapply (l1_next k L i n s (upd_at dot (n - 1) 1) res _ sbs sgb dv); try eassumption; try fr_close; try weq.
      * eapply (l1_digit k L i n s dot b res m1 sbs sgb dv); try eassumption; try weq. all: try intuition.
Qed.

Lemma l1_all : forall k, L1 k.
Proof.
  induction k as [|k IH].
  - unfold L1. intros i n s dot b res m1 sbs sgb dv x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
      x24 x25 Hk Eb. exfalso.
    assert (H : (i < length tb)%nat) by (apply nth_error_Some; rewrite Eb; discriminate). lia.
  - apply l1_step. exact IH.
Qed.

(* 0x15b24: the prologue, the NULL tests and the first byte *)
Lemma entry : forall (x13 x14 x15 x16 x17 : word) (sjb : list byte) (djb : byte),
  diginet_counter_text_pre sp a0 a1 a2 m0 lo tb sjb djb ->
  evt rsegs (POST (counter_text_spec (zb tb)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15b24) fc None m0 (seg_rom rsegs)).
Proof.
  intros x13 x14 x15 x16 x17 sjb djb (HA0 & [TX TZ] & HA1 & SGC & HA2 & DTC & _ & _ & _ & _ & HMI & STK & _).
  carve_frame 128%nat STK.
  pose proof (munch_refl W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (nth_error_some_len tb 0 TZ) as [b0 E0].
  (* 0x15b24 .. 0x15b6c: the frame, the saved registers, dot[] = 0, a0 = -1 *)
  do 19 step.
  destruct (rw_cells_app_split _ _ [_; _; _; _] _ FR) as [FD FR2].
  cbn [cells_size csize Nat.add] in FR2.
  replace (bv_unsigned sp + -128 + Z.of_nat 32) with (bv_unsigned sp + -96) in FR2 by lia.
  destruct (rw_cells_app_split _ _ [_] _ FR2) as [FS FV].
  cbn [cells_size csize Nat.add] in FV.
  replace (bv_unsigned sp + -96 + Z.of_nat 8) with (bv_unsigned sp + -88) in FV by lia.
  clear FR FR2.
  lazymatch type of FS with rw_cells _ _ _ [CB _ ?X] => set (sbs0 := X) in *; clearbody sbs0 end.
  apply dot0_u32arr in FD.
  pose proof (rw_cells_CB_len _ _ _ _ FS) as LX. apply u8arr_of_rw_cells in FS.
  (* 0x15b70 beqz a1; 0x15b74 beqz s1; 0x15b78 mv s0, a2; 0x15b7c beqz a2 *)
  step. if_cases K; [exfalso; zify_cond K; lia|].
  step. if_cases K'; [exfalso; zify_cond K'; lia|].
  step. step. if_cases K''; [exfalso; zify_cond K''; lia|].
  (* 0x15b80 lbu a0, 0(a1); 0x15b84 beqz a0, 0x15c14 *)
  pose proof (text_byte _ (bv_unsigned a0) tb 0 b0 a0 TX E0 ltac:(symmetry; apply wa_of_var; lia))
    as RD.
  step. step. if_cases K0; zc K0.
  - (* the empty text: 0x15c14 addi s2, zero, -8; 0x15c18 j 0x15c20 *)
    step. step.
    assert (HR : counter_text_spec (zb tb) = ct2 0 [] (repeat 0 8)).
    { unfold counter_text_spec. pose proof (skipn_zb tb 0 b0 E0) as Ez. change (skipn 0 (zb tb)) with (zb tb) in Ez.
      rewrite Ez, K0. reflexivity. }
    assert (INV : l1_inv 0 [] (repeat 0 8) sbs0).
    { refine (conj ct_inv_0 (conj _ (conj eq_refl (conj (Forall_nil _) (conj LX eq_refl))))).
      apply Forall_forall. intros x Hx. apply repeat_spec in Hx. cbv beta. lia. }
    eapply (l2_entry 0 [] (repeat 0 8) _ _ sbs0 sjb djb); try eassumption; try fr_close; try weq.
  - (* 0x15b88 .. 0x15ba0: the registers of the first loop *)
    do 7 step.
    assert (INV : l1_inv 0 [] (repeat 0 8) sbs0).
    { refine (conj ct_inv_0 (conj _ (conj eq_refl (conj (Forall_nil _) (conj LX eq_refl))))).
      apply Forall_forall. intros x Hx. apply repeat_spec in Hx. cbv beta. lia. }
    eapply (l1_all (length tb - 0) 0%nat 0 [] (repeat 0 8) b0 _ _ sbs0 sjb djb); try eassumption; try fr_close;
      try reflexivity; try lia; try weq.
Qed.

End CT.

Theorem diginet_counter_text_holds : diginet_seg7_contract -> diginet_counter_text_contract.
Proof.
  intros SEG7. unfold diginet_counter_text_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo tb sj dj PRE.
  pose proof PRE as (HA0 & [TX TZ] & HA1 & SGC & HA2 & DTC & HDJ & HT & HSG & HDT & HMI & STK & LO).
  unfold DIGINET_COUNTER_TEXT_DEPTH in LO.
  pose proof (rw_cells_bound rsegs m _ _ SGC) as SGB. pose proof (rw_cells_bound rsegs m _ _ DTC) as DTB.
  cbn [cells_size csize Nat.add] in SGB, DTB.
  pose proof STK as (Hlo & _ & _).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  eapply entry; try eassumption; try lia.
Qed.
