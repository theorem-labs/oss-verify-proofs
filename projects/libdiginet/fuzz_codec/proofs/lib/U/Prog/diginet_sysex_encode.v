(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 552 of its 576 lines of code are new or changed and 120 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells memcpy_c diginet_sysex_encode_c.
Import ListNotations.
Open Scope Z_scope.

(* The range of a word as a Z literal bound. *)
Ltac rng x H := pose proof (bv_unsigned_in_range 64 x) as H; unfold bv_modulus in H;
  change (2 ^ Z.of_N 64) with 18446744073709551616 in H.

(* A store address held in a register as a word variable: the goal [wa e = x] comes before its symmetric form. *)
Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].
(* A byte store of a register value v: the cell [C1] of its low byte. *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(** ---- bytes and byte lists ---- *)

Lemma sxu_bytes256 : forall (f : Z -> bool),
  forallb f (map Z.of_nat (seq 0 256)) = true -> forall x, 0 <= x < 256 -> f x = true.
Proof.
  intros f H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat x). split; [lia |]. apply in_seq. lia.
Qed.

(** Bit 7 of a byte value is its test against 128. *)
Lemma sxu_bit7 : forall x, 0 <= x < 256 -> Z.testbit x 7 = (128 <=? x).
Proof.
  intros x Hx.
  pose proof (sxu_bytes256 (fun y => Bool.eqb (Z.testbit y 7) (128 <=? y)) ltac:(vm_compute; reflexivity) x Hx) as H.
  cbv beta in H. apply Bool.eqb_prop in H. exact H.
Qed.

Lemma sxu_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma sxu_zb_length : forall l, length (zb l) = length l.
Proof. intros l. unfold zb. apply length_map. Qed.

Lemma sxu_b8_unsigned : forall b : byte, b8 (bv_unsigned b) = b.
Proof.
  intros b. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma sxu_bz_zb : forall l, map b8 (zb l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. unfold zb in *. cbn [map]. rewrite IH, sxu_b8_unsigned. reflexivity.
Qed.

(** No payload byte has bit 7 set. *)
Lemma sxu_exists_none : forall l : list byte,
  (forall j, (j < length l)%nat -> bv_unsigned (nth j l (Z_to_bv 8 0)) < 128) ->
  existsb (fun x => Z.testbit x 7) (zb l) = false.
Proof.
  induction l as [|b l IH]; intros H; [reflexivity|].
  unfold zb in *. cbn [map existsb].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0.
  pose proof (sxu_byte_range b) as Rb.
  rewrite sxu_bit7 by lia. rewrite (proj2 (Z.leb_gt 128 (bv_unsigned b)) ltac:(lia)). cbn [orb].
  apply IH. intros j Hj. apply (H (S j)). cbn. lia.
Qed.

(** Payload byte j has bit 7 set. *)
Lemma sxu_exists_one : forall (l : list byte) j,
  (j < length l)%nat -> 128 <= bv_unsigned (nth j l (Z_to_bv 8 0)) ->
  existsb (fun x => Z.testbit x 7) (zb l) = true.
Proof.
  induction l as [|b l IH]; intros j Hj H; [cbn in Hj; lia|].
  unfold zb in *. cbn [map existsb].
  destruct j as [|j].
  - cbn [nth] in H. pose proof (sxu_byte_range b) as Rb.
    rewrite sxu_bit7 by lia. rewrite (proj2 (Z.leb_le 128 (bv_unsigned b)) H). reflexivity.
  - cbn [nth] in H. rewrite (IH j); [apply orb_true_r | cbn in Hj; lia | exact H].
Qed.

(** ---- cells ---- *)

Lemma sxu_cells_split : forall m A cs1 cs2,
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

Lemma sxu_cells_join : forall m A B cs1 cs2,
  B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 -> [[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)].
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

(** [CB (k1 + k2) bs] at A is [CB k1 ..] at A and [CB k2 ..] at A + k1. *)
Lemma sxu_cb_cut : forall m A (k1 k2 : nat) bs,
  rw_cells rsegs m A [CB (k1 + k2) bs] ->
  rw_cells rsegs m A [CB k1 (firstn k1 bs)] /\ rw_cells rsegs m (A + Z.of_nat k1) [CB k2 (skipn k1 bs)].
Proof.
  intros m A k1 k2 bs H.
  assert (L : length bs = (k1 + k2)%nat) by (destruct H as [[[Hl _] _] _]; exact Hl).
  pose proof (rw_cells_split_CB rsegs m A [] (k1 + k2) bs [] [k1; k2] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2.
  apply (sxu_cells_split m A [CB k1 (firstn k1 bs)] [CB k2 (firstn k2 (skipn k1 bs))]) in H2.
  destruct H2 as [H2a H2b]. split; [exact H2a|].
  cbn [cells_size csize] in H2b. rewrite Nat.add_0_r in H2b.
  rewrite firstn_all2 in H2b by (rewrite length_skipn; lia). exact H2b.
Qed.

Lemma sxu_rebase : forall m A B cs, rw_cells rsegs m A cs -> A = B -> rw_cells rsegs m B cs.
Proof. intros; subst; assumption. Qed.

(** A byte of a byte list in memory. *)
Lemma sxu_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

(** [slli 0x38] of a byte value. *)
Lemma sxu_shl56 : forall x, 0 <= x < 256 -> Z.shiftl x 56 mod 18446744073709551616 = x * 72057594037927936.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 56) with 72057594037927936.
  apply Z.mod_small. lia.
Qed.

Lemma sxu_join : forall m A cs1, rw_cells rsegs m A cs1 -> forall B cs2, rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A cs1 H1 B cs2 H2 E. exact (sxu_cells_join m A B cs1 cs2 E H1 H2). Qed.

Lemma sxu_merge : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof (rw_cells_merge rsegs m A [] cs []) as M.
  rewrite app_nil_r in M. cbn [app] in M. apply M. exact H.
Qed.

Lemma sxu_cb_eq : forall m A n bs n' bs', rw_cells rsegs m A [CB n bs] -> n = n' -> bs = bs' -> rw_cells rsegs m A [CB n' bs'].
Proof. intros; subst; assumption. Qed.

(** After the stores of the three header bytes, out is cut into the header, the payload room, the
    0xf7 byte with the bytes kept after it, and the len, display, padding and key fields. *)
Lemma sxu_out_cut : forall m A x y z r (n k : nat),
  rw_cells rsegs m A [x; y; z; CB 28 r] -> (csize x + (csize y + (csize z + 0)) = 4)%nat -> (n + k = 19)%nat ->
  rw_cells rsegs m A [x; y; z] /\
  rw_cells rsegs m (A + 4) [CB n (firstn n r)] /\
  rw_cells rsegs m (A + 4 + Z.of_nat n) [CB 1 (firstn 1 (skipn n r)); CB k (firstn k (skipn 1 (skipn n r)))] /\
  rw_cells rsegs m (A + 24) [CB 8 (skipn k (skipn 1 (skipn n r)))].
Proof.
  intros m A x y z r n k H Hs Hk.
  apply (sxu_cells_split m A [x; y; z] [CB 28 r]) in H. destruct H as [H0 H].
  cbn [cells_size] in H. rewrite Hs in H.
  replace 28%nat with (n + (1 + (k + 8)))%nat in H by lia.
  apply sxu_cb_cut in H. destruct H as [H1 H].
  apply sxu_cb_cut in H. destruct H as [H2 H].
  apply sxu_cb_cut in H. destruct H as [H3 H4].
  split; [exact H0|]. split; [eapply sxu_rebase; [exact H1 | lia] |].
  split.
  - eapply (sxu_join m (A + 4 + Z.of_nat n) [CB 1 (firstn 1 (skipn n r))]); [eapply sxu_rebase; [exact H2 | lia] | exact H3 |].
    cbn [cells_size csize]. lia.
  - eapply sxu_rebase; [exact H4 | lia].
Qed.

Lemma sxu_lit8 : forall v, 0 <= v < 2 ^ 64 -> Z_to_bv 8 (bv_unsigned (Z_to_bv 64 v)) = b8 v.
Proof. intros v Hv. unfold b8. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma sxu_le2_hdr : le2 (Z_to_bv 64 5104) = [b8 240; b8 19].
Proof.
  unfold le2. cbn [Z_to_le_bytes].
  match goal with |- [?x1; ?x2] = [?y1; ?y2] =>
    assert (E1 : x1 = y1) by (apply bv_eq; vm_compute; reflexivity);
    assert (E2 : x2 = y2) by (apply bv_eq; vm_compute; reflexivity);
    rewrite E1, E2; reflexivity
  end.
Qed.

(** [lb] then [bltz]: the sign-extended byte is negative exactly when its bit 7 is set. *)
Lemma sxu_sxb : forall b : byte, (9223372036854775808 <= bv_unsigned (sxb b)) <-> (128 <= bv_unsigned b).
Proof.
  intros b. pose proof (sxu_byte_range b) as R.
  unfold sxb, bv_signed. rewrite unsigned_lit_wrap.
  pose proof (sxu_bytes256 (fun u => Bool.eqb (9223372036854775808 <=? bv_swrap 8 u mod 2 ^ 64) (128 <=? u))
                ltac:(vm_compute; reflexivity) _ R) as H.
  cbv beta in H. apply Bool.eqb_prop in H.
  split; intro H'.
  - apply Z.leb_le. rewrite <- H. apply Z.leb_le. exact H'.
  - apply Z.leb_le. rewrite H. apply Z.leb_le. exact H'.
Qed.

(** The display byte: [addi -0x30; andi 0xef; seqz] on fn. *)
Lemma sxu_disp : forall x, 0 <= x < 256 ->
  Z.b2z (Z.land ((x + -48) mod 18446744073709551616) 239 <? 1) = bit_or_0 ((x =? 64) || (x =? 48)) 1.
Proof.
  intros x Hx.
  pose proof (sxu_bytes256 (fun y => Z.eqb (Z.b2z (Z.land ((y + -48) mod 18446744073709551616) 239 <? 1))
                                           (bit_or_0 ((y =? 64) || (y =? 48)) 1))
                ltac:(vm_compute; reflexivity) x Hx) as H.
  cbv beta in H. apply Z.eqb_eq in H. exact H.
Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Section SysexU.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo dev fn : Z) (pl before : list byte) (pa out lenw : word).
Hypothesis RDEV : 0 <= dev < 256.
Hypothesis RFN : 0 <= fn < 256.
Hypothesis PANZ : bv_unsigned pa <> 0.
Hypothesis OUTNZ : bv_unsigned out <> 0.
Hypothesis OUTA : Z.land (bv_unsigned out) 3 = 0.
Hypothesis HLW : bv_unsigned lenw = Z.of_nat (length pl).
Hypothesis DJ : disj (bv_unsigned pa) (Z.of_nat (length pl)) (bv_unsigned out) 32.
Hypothesis BPA : bv_unsigned pa + Z.of_nat (length pl) <= 2 ^ 64.
Hypothesis BOUT : bv_unsigned out + 32 <= 2 ^ 64.
Hypothesis SPA2 : bv_unsigned sp <= bv_unsigned pa.
Hypothesis SPA4 : bv_unsigned sp <= bv_unsigned out.
Hypothesis LO : lo + 48 <= bv_unsigned sp.
Hypothesis LO0 : 0 <= lo.
Hypothesis MC : memcpy_contract.

(** The contract's postcondition. *)
Definition Qk (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    let '(rc, o) := sysex_spec dev fn (zb pl) in
    a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned out) [CB 32 (cmd_out before o)].

(** The prologue saves s3, s2, s1, s0 and ra at sp-40 .. sp-8 (8 unused bytes at sp-48). *)
Definition saved : list cell := [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(** The epilogue at 0x157e0: restore ra, s0-s3, free the frame, return. *)
Lemma sxu_exit : forall (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 t3' t4' t5' t6' : word)
    (m1 : word -> option byte) (j8 : list byte),
  rw_cells rsegs m1 (bv_unsigned sp + -48) (CB 8 j8 :: saved) ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  (let '(rc, o) := sysex_spec dev fn (zb pl) in
   a0' = Z_to_bv 64 rc /\ rw_cells rsegs m1 (bv_unsigned out) [CB 32 (cmd_out before o)]) ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x157e0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 t3' t4' t5' t6' m1 j8 FR ST MU WM HMI R.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold saved in FR.
  do 6 zstep.
  eapply stk_release in FR; [ | exact ST | lia ].
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  finish.
Qed.

(** ---- the spec on each path ---- *)

Lemma sxu_spec_dev : forall l, 127 < dev -> sysex_spec dev fn l = (E_ARG, None).
Proof. intros l H. unfold sysex_spec. rewrite (proj2 (Z.ltb_lt 127 dev) H). reflexivity. Qed.

Lemma sxu_spec_ref : forall l, dev <= 127 -> fn = 112 -> sysex_spec dev fn l = (E_REFUSED, None).
Proof.
  intros l H1 H2. unfold sysex_spec.
  rewrite (proj2 (Z.ltb_ge 127 dev) ltac:(lia)), (proj2 (Z.eqb_eq fn 112) H2). reflexivity.
Qed.

Lemma sxu_spec_fn : forall l, dev <= 127 -> fn <> 112 -> 127 < fn -> sysex_spec dev fn l = (E_RANGE, None).
Proof.
  intros l H1 H2 H3. unfold sysex_spec.
  rewrite (proj2 (Z.ltb_ge 127 dev) ltac:(lia)), (proj2 (Z.eqb_neq fn 112) H2), (proj2 (Z.ltb_lt 127 fn) H3).
  reflexivity.
Qed.

Lemma sxu_spec_space : forall l, dev <= 127 -> fn <> 112 -> fn <= 127 -> 24 < Z.of_nat (length l) + 5 ->
  sysex_spec dev fn l = (E_SPACE, None).
Proof.
  intros l H1 H2 H3 H4. unfold sysex_spec.
  rewrite (proj2 (Z.ltb_ge 127 dev) ltac:(lia)), (proj2 (Z.eqb_neq fn 112) H2), (proj2 (Z.ltb_ge 127 fn) ltac:(lia)),
    (proj2 (Z.ltb_lt 24 _) H4).
  reflexivity.
Qed.

Lemma sxu_spec_byte : forall l, dev <= 127 -> fn <> 112 -> fn <= 127 -> Z.of_nat (length l) + 5 <= 24 ->
  existsb (fun x => Z.testbit x 7) l = true -> sysex_spec dev fn l = (E_RANGE, None).
Proof.
  intros l H1 H2 H3 H4 H5. unfold sysex_spec.
  rewrite (proj2 (Z.ltb_ge 127 dev) ltac:(lia)), (proj2 (Z.eqb_neq fn 112) H2), (proj2 (Z.ltb_ge 127 fn) ltac:(lia)),
    (proj2 (Z.ltb_ge 24 (Z.of_nat (length l) + 5)) H4), H5.
  reflexivity.
Qed.

Lemma sxu_spec_ok : forall l, dev <= 127 -> fn <> 112 -> fn <= 127 -> Z.of_nat (length l) + 5 <= 24 ->
  existsb (fun x => Z.testbit x 7) l = false ->
  sysex_spec dev fn l = (0, Some ([0xf0; 0x13; dev; fn] ++ l ++ [0xf7], 0, bit_or_0 ((fn =? 0x40) || (fn =? 0x30)) 1)).
Proof.
  intros l H1 H2 H3 H4 H5. unfold sysex_spec.
  rewrite (proj2 (Z.ltb_ge 127 dev) ltac:(lia)), (proj2 (Z.eqb_neq fn 112) H2), (proj2 (Z.ltb_ge 127 fn) ltac:(lia)),
    (proj2 (Z.ltb_ge 24 (Z.of_nat (length l) + 5)) H4), H5.
  reflexivity.
Qed.

(** ---- the 32 bytes of out on success ---- *)

Lemma sxu_kept : forall k, (length pl + k = 19)%nat ->
  firstn k (skipn 1 (skipn (length pl) (skipn 4 before))) = skipn (length pl + 5) (firstn 24 before).
Proof.
  intros k Hk. rewrite !skipn_skipn, skipn_firstn_comm. f_equal; [lia | f_equal; lia].
Qed.

Lemma sxu_out_final : forall m1 (k : nat) (f7 lc dc : byte) (q : list byte),
  (length pl + k = 19)%nat ->
  f7 = b8 247 -> lc = b8 (Z.of_nat (length pl + 5)) -> dc = b8 (bit_or_0 ((fn =? 0x40) || (fn =? 0x30)) 1) ->
  q = firstn 2 (skipn 26 before) ->
  rw_cells rsegs m1 (bv_unsigned out)
    [C2 (Z_to_bv 64 5104); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 dev))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 fn)))] ->
  rw_cells rsegs m1 (bv_unsigned out + 4) [CB (length pl) pl] ->
  rw_cells rsegs m1 (bv_unsigned out + 4 + Z.of_nat (length pl))
    [C1 f7; CB k (firstn k (skipn 1 (skipn (length pl) (skipn 4 before))))] ->
  rw_cells rsegs m1 (bv_unsigned out + 24) [C1 lc; C1 dc; CB 2 q; C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m1 (bv_unsigned out)
    [CB 32 (cmd_out before (Some ([0xf0; 0x13; dev; fn] ++ zb pl ++ [0xf7], 0, bit_or_0 ((fn =? 0x40) || (fn =? 0x30)) 1)))].
Proof.
  intros m1 k f7 lc dc q Hk Ef7 Elc Edc Eqq P0 P1 P2 P3.
  pose proof (sxu_join _ _ _ P0 _ _ P1) as J1. specialize (J1 ltac:(cbn [cells_size csize Nat.add]; lia)).
  pose proof (sxu_join _ _ _ J1 _ _ P2) as J2. specialize (J2 ltac:(rewrite cells_size_app; cbn [cells_size csize]; lia)).
  pose proof (sxu_join _ _ _ J2 _ _ P3) as J3.
  specialize (J3 ltac:(rewrite !cells_size_app; cbn [cells_size csize]; lia)).
  apply sxu_merge in J3.
  eapply sxu_cb_eq; [exact J3 | rewrite !cells_size_app; cbn [cells_size csize]; lia |].
  (* the spec side *)
  unfold cmd_out. cbv beta iota zeta.
  assert (Lbs : length ([0xf0; 0x13; dev; fn] ++ zb pl ++ [0xf7]) = (length pl + 5)%nat)
    by (rewrite !length_app, sxu_zb_length; cbn [length]; lia).
  rewrite Lbs.
  unfold bz. rewrite !map_app. cbn [map]. rewrite sxu_bz_zb.
  (* the cells side *)
  rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
  subst f7 lc dc q.
  rewrite sxu_le2_hdr. cbn [app]. rewrite !sxu_lit8 by lia.
  rewrite (sxu_kept k Hk).
  rewrite <- !app_assoc. cbn [app]. reflexivity.
Qed.

(** ---- 0x157b0: the 0xf7 byte (through the UBSan checks on out + 4 + len), len, display, key ---- *)
Lemma sxu_fin : forall (ra' t0' t1' t2' a0w a1w a2w a3w a4w a5w a6w a7w t3' t4' t5' t6' s2w : word)
    (m1 : word -> option byte) (j8 : list byte) (k : nat),
  bv_unsigned s2w = Z.of_nat (length pl) + 4 ->
  (length pl + k = 19)%nat -> dev <= 127 -> fn <> 112 -> fn <= 127 ->
  (forall j, (j < length pl)%nat -> bv_unsigned (nth j pl (Z_to_bv 8 0)) < 128) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) (CB 8 j8 :: saved) ->
  rw_cells rsegs m1 (bv_unsigned out)
    [C2 (Z_to_bv 64 5104); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 dev))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 fn)))] ->
  rw_cells rsegs m1 (bv_unsigned out + 4) [CB (length pl) pl] ->
  rw_cells rsegs m1 (bv_unsigned out + 4 + Z.of_nat (length pl))
    [CB 1 (firstn 1 (skipn (length pl) (skipn 4 before)));
     CB k (firstn k (skipn 1 (skipn (length pl) (skipn 4 before))))] ->
  rw_cells rsegs m1 (bv_unsigned out + 24) [CB 8 (skipn k (skipn 1 (skipn (length pl) (skipn 4 before))))] ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' out (Z_to_bv 64 fn)
             a0w a1w a2w a3w a4w a5w a6w a7w
             s2w (Z_to_bv 64 (bv_unsigned lenw + 5)) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x157b0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a0w a1w a2w a3w a4w a5w a6w a7w t3' t4' t5' t6' s2w m1 j8 k
    HS2 Hk D7 FN70 F7 ALL FR P0 P1 P2 P3 ST MU WM HMI.
  unfold saved in FR.
  rng sp Rsp. rng out Rout. rng pa Rpa.
  (* not a0, s0; bltu a0, s2: ~out < 4 + len is the UBSan pointer-overflow check of out->bytes + 4 + len *)
  zstep. zstep.
  if_cases T; [ exfalso; zify_cond T; rewrite zb_lxor_ones in T by lia; lia | zify_cond T ].
  (* mv a0, zero; add s2, s0, s2 *)
  zstep. zstep.
  remember (Z_to_bv 64 (bv_unsigned out + bv_unsigned s2w)) as h2 eqn:Eh2.
  assert (Hh2 : bv_unsigned h2 = bv_unsigned out + 4 + Z.of_nat (length pl))
    by (subst h2; rewrite unsigned_lit by lia; lia).
  clear Eh2.
  rewrite <- Hh2 in P2.
  (* addi a1, zero, -9; sb a1, 0(s2) *)
  zstep. zstep.
  (* the display byte, then sb s3, 0x18(s0); sb a1, 0x19(s0); sw zero, 0x1c(s0) *)
  zstep. zstep. zstep.
  zstep. zstep. zstep.
  rewrite Hh2 in P2.
  eapply sxu_exit; [exact FR | exact ST | exact MU | exact WM | exact HMI | ].
  rewrite (sxu_spec_ok (zb pl)); [ | exact D7 | exact FN70 | exact F7 | rewrite sxu_zb_length; lia
                                 | apply sxu_exists_none; exact ALL ].
  cbv beta iota. split; [reflexivity |].
  eapply sxu_out_final; [exact Hk | | | | | exact P0 | exact P1 | exact P2 | exact P3].
  - apply bv_eq. vm_compute. reflexivity.
  - rewrite sxu_lit8 by lia. f_equal. lia.
  - rewrite sxu_disp by lia. apply sxu_lit8. unfold bit_or_0. destruct ((fn =? 64) || (fn =? 48)); lia.
  - rewrite !skipn_skipn. f_equal. f_equal. lia.
Qed.

(** ---- 0x15764: all checks passed; the header stores, then memcpy when len <> 0 ---- *)
Lemma sxu_tail : forall (t0' t1' t2' a0w a3w a4w a5w a6w a7w t3' t4' t5' t6' : word)
    (m1 : word -> option byte) (j8 : list byte),
  Z.of_nat (length pl) <= 19 -> dev <= 127 -> fn <> 112 -> fn <= 127 ->
  (forall j, (j < length pl)%nat -> bv_unsigned (nth j pl (Z_to_bv 8 0)) < 128) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) (CB 8 j8 :: saved) ->
  rw_cells rsegs m1 (bv_unsigned out) [CB 32 before] ->
  bytes_at rsegs m1 (bv_unsigned pa) pl ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' out (Z_to_bv 64 fn) a0w (Z_to_bv 64 dev) pa
             a3w a4w a5w a6w a7w lenw (Z_to_bv 64 (bv_unsigned lenw + 5)) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x15764) fc None m1 (seg_rom rsegs)).
Proof.
  intros t0' t1' t2' a0w a3w a4w a5w a6w a7w t3' t4' t5' t6' m1 j8 L19 D7 FN70 F7 ALL FR OUT HPL ST MU WM HMI.
  unfold saved in FR.
  rng sp Rsp. rng out Rout. rng pa Rpa.
  pose proof DJ as DJ'. unfold disj in DJ'.
  (* andi a0, s0, 3; bnez a0: the UBSan alignment check of out *)
  zstep. zstep.
  if_cases T; [ exfalso; zify_cond T; lia | zify_cond T ].
  (* lui; addi: a0 = 0x13f0; sh a0, 0(s0); sb a1, 2(s0); sb s1, 3(s0) *)
  zstep. zstep. zstep. zstep. zstep.
  rewrite !skipn_skipn in OUT. cbn [Nat.add] in OUT.
  assert (Hk : exists k, (length pl + k = 19)%nat) by (exists (19 - length pl)%nat; lia).
  destruct Hk as [k Hk].
  destruct (sxu_out_cut _ _ _ _ _ _ (length pl) k OUT eq_refl Hk) as (P0 & P1 & P2 & P3).
  clear OUT.
  (* beqz s2 *)
  zstep.
  if_cases KZ.
  - (* len = 0: addi s2, zero, 4 *)
    zify_cond KZ.
    zstep.
    assert (E0 : length pl = 0%nat) by lia.
    assert (Epl : pl = []) by (apply length_zero_iff_nil; exact E0).
    replace (firstn (length pl) (skipn 4 before)) with pl in P1 by (rewrite E0, Epl; reflexivity).
    eapply sxu_fin with (k := k); [ rewrite unsigned_lit by lia; lia | eassumption .. ].
  - (* len <> 0: addi a0, zero, -5; bltu a0, s0: the UBSan pointer-overflow check of out->bytes + 4 *)
    zify_cond KZ.
    zstep. zstep.
    if_cases T6; [ exfalso; zify_cond T6; lia | zify_cond T6 ].
    (* addi a0, s0, 4; mv a1, a2; mv a2, s2; jal memcpy *)
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply MC with (src := pl) (junk := firstn (length pl) (skipn 4 before)).
      - exact HPL.
      - rewrite HLW, Nat2Z.id. reflexivity.
      - rewrite unsigned_lit by lia. rewrite HLW, Nat2Z.id. exact P1.
      - rewrite unsigned_lit by lia. rewrite HLW. lia.
      - exact HMI. }
    intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & mc & E & MUc & WMc & MIc & H1n & HPLn).
    subst ms'.
    rewrite !unsigned_lit in MUc, H1n by lia. rewrite HLW in MUc, H1n. rewrite Nat2Z.id in H1n.
    clear HPLn.
    lazymatch type of MUc with munch _ ?mm _ =>
      transport_after_call rsegs mm mc MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv rsegs mm |- _ => clear H end
    end.
    fix_ret.
    (* addi s2, s2, 4; addi a0, zero, 0x17; bgeu a0, s2: the UBSan bounds check of out->bytes[4 + len] *)
    zstep. zstep. zstep.
    if_cases T7; [ zify_cond T7 | exfalso; zify_cond T7; rewrite ?Z.mod_small in T7 by lia; lia ].
    eapply sxu_fin with (k := k); [ rewrite unsigned_lit by lia; lia | eassumption .. ].
Qed.

(** ---- 0x15738: the payload loop (UBSan pointer-overflow checks of payload + i, then the bit-7 test) ---- *)
Definition sxu_loop_ok (n : nat) : Prop :=
  forall (t0' t1' t2' a7w t3' t4' t5' t6' : word) (cur rem : word) (i : Z) (m1 : word -> option byte) (j8 : list byte),
  Z.of_nat n = Z.of_nat (length pl) - i -> 0 <= i -> i < Z.of_nat (length pl) ->
  bv_unsigned cur = bv_unsigned pa + i -> bv_unsigned rem = Z.of_nat (length pl) - i ->
  Z.of_nat (length pl) <= 19 -> dev <= 127 -> fn <> 112 -> fn <= 127 ->
  (forall j, (j < Z.to_nat i)%nat -> bv_unsigned (nth j pl (Z_to_bv 8 0)) < 128) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) (CB 8 j8 :: saved) ->
  rw_cells rsegs m1 (bv_unsigned out) [CB 32 before] ->
  bytes_at rsegs m1 (bv_unsigned pa) pl ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' out (Z_to_bv 64 fn)
             (Z_to_bv 64 (-11)) (Z_to_bv 64 dev) pa (Z_to_bv 64 1) cur cur rem a7w
             lenw (Z_to_bv 64 (bv_unsigned lenw + 5)) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x15738) fc None m1 (seg_rom rsegs)).

Lemma sxu_loop : forall n, sxu_loop_ok n.
Proof.
  induction n as [|n IH]; unfold sxu_loop_ok;
    intros t0' t1' t2' a7w t3' t4' t5' t6' cur rem i m1 j8 Hn Hi0 Hi HC HR L19 D7 FN70 F7 ALL FR OUT HPL ST MU WM HMI.
  { exfalso. lia. }
  unfold sxu_loop_ok in IH.
  unfold saved in FR.
  rng sp Rsp. rng pa Rpa.
  (* bltu a4, a2: payload + i wrapped below payload *)
  zstep.
  if_cases T1; [ exfalso; zify_cond T1; lia | zify_cond T1 ].
  (* seqz a7, a4; xor a7, a3, a7; beqz a7: payload and payload + i differ in null-ness *)
  zstep. zstep. zstep.
  if_cases T2; [ exfalso; zify_cond T2; rewrite (proj2 (Z.ltb_ge (bv_unsigned cur) 1) ltac:(lia)) in T2;
                 cbv in T2; discriminate | zify_cond T2 ].
  (* beqz a2: payload is NULL *)
  zstep.
  if_cases T3; [ exfalso; zify_cond T3; lia | zify_cond T3 ].
  (* lb a7, 0(a5) *)
  assert (HB : ov_read_bytes rsegs m1 cur 1 = Some [nth (Z.to_nat i) pl (Z_to_bv 8 0)]).
  { rewrite <- (Z_to_bv_bv_unsigned cur). rewrite HC. apply (sxu_byte m1 (bv_unsigned pa) pl i HPL). lia. }
  remember (nth (Z.to_nat i) pl (Z_to_bv 8 0)) as b eqn:Eb.
  pose proof (sxu_byte_range b) as Rb.
  zstep.
  (* bltz a7 *)
  zstep.
  if_cases KN.
  - (* bit 7 set: return E_RANGE *)
    zify_cond KN. apply (proj1 (sxu_sxb b)) in KN.
    eapply sxu_exit; [exact FR | exact ST | exact MU | exact WM | exact HMI | ].
    rewrite (sxu_spec_byte (zb pl)); [ | exact D7 | exact FN70 | exact F7 | rewrite sxu_zb_length; lia | ].
    + cbv beta iota. split; [reflexivity | exact OUT].
    + apply (sxu_exists_one pl (Z.to_nat i)); [lia | rewrite <- Eb; exact KN].
  - zify_cond KN.
    assert (Kb : bv_unsigned b < 128).
    { destruct (Z.lt_ge_cases (bv_unsigned b) 128) as [Hl | Hg]; [exact Hl |].
      apply (proj2 (sxu_sxb b)) in Hg. lia. }
    assert (ALL' : forall j, (j < Z.to_nat (i + 1))%nat -> bv_unsigned (nth j pl (Z_to_bv 8 0)) < 128).
    { intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne]; [rewrite <- Eb; exact Kb |].
      apply ALL. lia. }
    (* addi a6, a6, -1; addi a5, a5, 1; addi a4, a4, 1; bnez a6 *)
    zstep. zstep. zstep. zstep.
    if_cases KL.
    + zify_cond KL.
      eapply (IH _ _ _ _ _ _ _ _ _ _ (i + 1)); try eassumption;
        first [ lia | rewrite unsigned_lit by lia; lia ].
    + zify_cond KL.
      eapply sxu_tail; try eassumption.
      intros j Hj. apply ALL'. lia.
Qed.

(** ---- 0x156b0: prologue and the checks before the loop ---- *)
Lemma sxu_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
  bytes_at rsegs m (bv_unsigned pa) pl ->
  rw_cells rsegs m (bv_unsigned out) [CB 32 before] ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Qk
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dev) (Z_to_bv 64 fn) pa lenw out a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x156b0) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 HPL OUT HMI ST.
  rng sp Rsp. rng out Rout. rng pa Rpa.
  pose proof DJ as DJ'. unfold disj in DJ'.
  assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m)
    by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  carve_frame 48%nat ST.
  (* addi sp; sd ra, s0-s3; mv s1, a1; mv a1, a0; addi a0, zero, -1; beqz a4 *)
  do 6 zstep. do 3 zstep. zstep.
  if_cases K1; [ exfalso; zify_cond K1; lia | zify_cond K1 ].
  (* mv s2, a3; slli a3, a1, 0x38; bltz a3: device > 0x7f *)
  zstep. zstep. zstep.
  if_cases K2.
  { zify_cond K2. rewrite sxu_shl56 in K2 by lia.
    eapply sxu_exit; [eassumption .. | ].
    rewrite (sxu_spec_dev (zb pl)) by lia. cbv beta iota. split; [reflexivity | exact OUT]. }
  zify_cond K2. rewrite sxu_shl56 in K2 by lia.
  assert (D7 : dev <= 127) by lia.
  (* mv s0, a4; seqz a4, s2; snez a3, a2; or a4, a3, a4; beqz a4: len && !payload *)
  zstep. zstep. zstep. zstep. zstep.
  if_cases K3.
  { exfalso. zify_cond K3. rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned pa)) ltac:(lia)) in K3.
    destruct (bv_unsigned lenw <? 1); cbv in K3; discriminate. }
  zify_cond K3.
  replace (0 <? bv_unsigned pa) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  (* addi a0, zero, 0x70; bne s1, a0 *)
  zstep. zstep.
  if_cases K4.
  2: { zify_cond K4. zstep. zstep.
       eapply sxu_exit; [eassumption .. | ].
       rewrite (sxu_spec_ref (zb pl)) by lia. cbv beta iota. split; [reflexivity | exact OUT]. }
  zify_cond K4.
  (* slli a4, s1, 0x38; addi a0, zero, -11; bltz a4: fn > 0x7f *)
  zstep. zstep. zstep.
  if_cases K5.
  { zify_cond K5. rewrite sxu_shl56 in K5 by lia.
    eapply sxu_exit; [eassumption .. | ].
    rewrite (sxu_spec_fn (zb pl)) by lia. cbv beta iota. split; [reflexivity | exact OUT]. }
  zify_cond K5. rewrite sxu_shl56 in K5 by lia.
  assert (F7 : fn <= 127) by lia.
  (* addi s3, s2, 5; addi a4, zero, 0x18; bgeu a4, s3: len + 5 > 24 *)
  zstep. zstep. zstep.
  if_cases K6.
  2: { zify_cond K6. rewrite ?Z.mod_small in K6 by lia. zstep. zstep.
       eapply sxu_exit; [eassumption .. | ].
       rewrite (sxu_spec_space (zb pl)) by (rewrite ?sxu_zb_length; lia).
       cbv beta iota. split; [reflexivity | exact OUT]. }
  zify_cond K6. rewrite ?Z.mod_small in K6 by lia.
  assert (L19 : Z.of_nat (length pl) <= 19) by lia.
  (* beqz s2 *)
  zstep.
  if_cases K7.
  - zify_cond K7.
    eapply sxu_tail; try eassumption.
    intros j Hj. lia.
  - zify_cond K7.
    (* mv a4, a2; mv a5, a2; mv a6, s2 *)
    zstep. zstep. zstep.
    eapply (sxu_loop (length pl)) with (i := 0); try eassumption; try lia.
    all: (intros j Hj; cbn in Hj; lia).
Qed.

End SysexU.

Theorem diginet_sysex_encode_holds : memcpy_contract -> diginet_sysex_encode_contract.
Proof.
  intros MC. unfold diginet_sysex_encode_contract, DIGINET_SYSEX_ENCODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo dev fn pl before PRE.
  unfold diginet_sysex_encode_pre, DIGINET_SYSEX_ENCODE_DEPTH in PRE.
  destruct PRE as (HDEV & HFN & HA2 & HPL & HLEN & HA4 & OUT & HAL & DJ & SPA2 & SPA4 & HMI & ST & LO).
  destruct HDEV as [RDEV ->]. destruct HFN as [RFN ->].
  pose proof (bytes_at_bound rsegs m _ _ HPL) as [_ BPA].
  pose proof (rw_cells_bound rsegs m _ _ OUT) as [_ BOUT]. cbn [cells_size csize Nat.add] in BOUT.
  assert (OUTA : Z.land (bv_unsigned a4) 3 = 0)
    by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact HAL).
  pose proof ST as [LO0 _].
  change (evt rsegs (Qk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo dev fn pl before a4)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dev) (Z_to_bv 64 fn) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x156b0) fc None m (seg_rom rsegs))).
  eapply sxu_entry; first [ exact eq_refl | eassumption | lia ].
Qed.
