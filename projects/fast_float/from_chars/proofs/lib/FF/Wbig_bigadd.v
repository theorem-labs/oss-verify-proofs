(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.

Module U_resize_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition resize_entry : Z := 0x27894.

(* [comment removed for export] *)
Fixpoint fill_from (ws : list word) (i k : nat) (v : word) : list word :=
  match k with
  | O => ws
  | S k' => fill_from (upd ws i v) (S i) k' v
  end.
Definition resize_ws (ws : list word) (len n : Z) (v : word) : list word :=
  if (n <=? len)%Z then ws else fill_from ws (Z.to_nat len) (Z.to_nat (n - len)) v.

Lemma fill_from_length : forall ws i k v, length (fill_from ws i k v) = length ws.
Proof. intros ws i k v. revert ws i. induction k as [|k IH]; intros; cbn; [reflexivity|]. rewrite IH, upd_length. reflexivity. Qed.
Lemma resize_ws_length : forall ws len n v, length (resize_ws ws len n v) = length ws.
Proof. intros. unfold resize_ws. destruct (n <=? len)%Z; [reflexivity| apply fill_from_length]. Qed.

Definition resize_W (A : Z) : list ivl := [(A, A + 498)]%Z.

Definition resize_post
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (ws : list word) (len n : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a3 a4 a5 a6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (resize_W (bv_unsigned a0)) m m'
    /\ wmono USEGS m m'
    /\ u64arr USEGS m' (bv_unsigned a0) (resize_ws ws len n a2)
    /\ rw_cells USEGS m' (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 n)].

Definition resize_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len n : Z),
    u64arr USEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells USEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z ->
    a1 = Z_to_bv 64 n -> (0 <= n <= 62)%Z ->
    evt USEGS (resize_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc ws len n m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x27894) fc None m (seg_rom USEGS)).
End U_resize_stmt.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd.U_resize_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition zfill (xs : list word) (L k : nat) (v : word) : list word :=
  firstn L xs ++ repeat v k ++ skipn (L + k) xs.

Lemma zfill_length : forall xs L k v, (L + k <= length xs)%nat -> length (zfill xs L k v) = length xs.
Proof. intros. unfold zfill. rewrite !app_length, firstn_length, repeat_length, skipn_length. lia. Qed.

Lemma nth_firstn_lt : forall (xs : list word) L j, (j < L)%nat -> nth j (firstn L xs) w0 = nth j xs w0.
Proof.
  intros xs L j Hj. destruct (Nat.lt_ge_cases j (length xs)) as [Hl|Hl].
  - rewrite <- (firstn_skipn L xs) at 2. rewrite app_nth1; [reflexivity|]. rewrite firstn_length. lia.
  - rewrite !nth_overflow; [reflexivity| lia |]. rewrite firstn_length. lia.
Qed.

Lemma zfill_nth_lo : forall xs L k v j, (j < L)%nat -> (L + k <= length xs)%nat -> nth j (zfill xs L k v) w0 = nth j xs w0.
Proof.
  intros xs L k v j Hj Hl. unfold zfill. rewrite app_nth1 by (rewrite firstn_length; lia). apply nth_firstn_lt. exact Hj.
Qed.

Lemma zfill_nth_mid : forall xs L k v j, (L <= j < L + k)%nat -> (L + k <= length xs)%nat -> nth j (zfill xs L k v) w0 = v.
Proof.
  intros xs L k v j Hj Hl. unfold zfill. rewrite app_nth2 by (rewrite firstn_length; lia).
  rewrite firstn_length, Nat.min_l by lia. rewrite app_nth1 by (rewrite repeat_length; lia).
  apply nth_repeat_lt. lia.
Qed.

Lemma zfill_nth_hi : forall xs L k v j, (L + k <= j)%nat -> (L + k <= length xs)%nat -> nth j (zfill xs L k v) w0 = nth j xs w0.
Proof.
  intros xs L k v j Hj Hl. unfold zfill. rewrite app_nth2 by (rewrite firstn_length; lia).
  rewrite firstn_length, Nat.min_l by lia. rewrite app_nth2 by (rewrite repeat_length; lia).
  rewrite repeat_length. rewrite nth_skipn. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma fill_from_zfill : forall k xs L v, (L + k <= length xs)%nat -> fill_from xs L k v = zfill xs L k v.
Proof.
  induction k as [|k IH]; intros xs L v Hl.
  - unfold zfill. cbn [repeat]. rewrite Nat.add_0_r. cbn [app]. symmetry. apply firstn_skipn.
  - cbn [fill_from]. rewrite IH by (rewrite upd_length; lia). unfold zfill.
    rewrite (upd_firstn_skipn xs L v) by lia.
    assert (HL : length (firstn L xs) = L) by (rewrite firstn_length; lia).
    rewrite firstn_app, HL, firstn_all2 by lia. replace (S L - L)%nat with 1%nat by lia. cbn [firstn].
    rewrite skipn_app, HL. replace (S L + k - L)%nat with (S k) by lia. cbn [skipn].
    rewrite skipn_skipn. rewrite (skipn_all2 (firstn L xs)) by lia. cbn [app].
    replace (k + S L)%nat with (L + S k)%nat by lia.
    rewrite <- app_assoc. cbn [app repeat]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bval_zeros_above : forall ws n k, (forall j, (n <= j < n + k)%nat -> limbZ ws j = 0) -> bval ws (n + k) = bval ws n.
Proof.
  intros ws n k Hz. induction k as [|k IH].
  - rewrite Nat.add_0_r. reflexivity.
  - replace (n + S k)%nat with (S (n + k)) by lia. rewrite bval_S. rewrite (Hz (n + k)%nat) by lia. rewrite IH by (intros; apply Hz; lia). lia.
Qed.

Lemma bval_zfill0 : forall xs L k, (L + k <= length xs)%nat -> bval (zfill xs L k w0) (L + k) = bval xs L.
Proof.
  intros xs L k Hl. rewrite bval_zeros_above.
  - apply bval_ext. intros i Hi. apply zfill_nth_lo; lia.
  - intros j Hj. unfold limbZ. rewrite zfill_nth_mid by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bval_agree_above : forall (l1 l2 : list word) k n, (k <= n)%nat ->
  (forall j, (k <= j)%nat -> nth j l1 w0 = nth j l2 w0) ->
  bval l1 n - bval l1 k = bval l2 n - bval l2 k.
Proof.
  intros l1 l2 k n Hkn Hag. induction n as [|n IH].
  - assert (k = 0%nat) as -> by lia. cbn. lia.
  - destruct (Nat.eq_dec k (S n)) as [->|Hne]; [lia|].
    rewrite !bval_S. unfold limbZ. rewrite (Hag n) by lia. specialize (IH ltac:(lia)). lia.
Qed.

Lemma pow64_add : forall a b : nat, 2 ^ (64 * Z.of_nat (a + b)) = 2 ^ (64 * Z.of_nat a) * 2 ^ (64 * Z.of_nat b).
Proof. intros. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

(* [comment removed for export] *)
Definition ladd_inv (x0 cur ys : list word) (s i : nat) (c : Z) : Prop :=
  bval cur (s + i) + c * 2 ^ (64 * Z.of_nat (s + i)) = bval x0 (s + i) + bval ys i * 2 ^ (64 * Z.of_nat s)
  /\ (forall j, (s + i <= j)%nat -> nth j cur w0 = nth j x0 w0)
  /\ length cur = length x0
  /\ (c = 0 \/ c = 1).

Lemma ladd_inv_init : forall x0 ys s, ladd_inv x0 x0 ys s 0 0.
Proof.
  intros. unfold ladd_inv. rewrite Nat.add_0_r. cbn [bval].
  split; [lia|]. split; [intros; reflexivity|]. split; [reflexivity| lia].
Qed.

Lemma ladd_inv_step : forall x0 cur ys s i c,
  ladd_inv x0 cur ys s i c -> (s + i < length x0)%nat ->
  let sum := limbZ x0 (s + i) + limbZ ys i + c in
  ladd_inv x0 (upd cur (s + i) (Z_to_bv 64 sum)) ys s (S i) (if sum <? 2 ^ 64 then 0 else 1).
Proof.
  intros x0 cur ys s i c (Hv & Hag & Hl & Hc) Hlen sum.
  pose proof (limbZ_range x0 (s + i)) as Hx. pose proof (limbZ_range ys i) as Hy.
  unfold ladd_inv. replace (s + S i)%nat with (S (s + i)) by lia.
  split; [| split; [| split]].
  - rewrite bval_push by (rewrite Hl; exact Hlen). rewrite unsigned_lit_wrap.
    rewrite !bval_S. rewrite pow64_S.
    rewrite (pow64_add s i) in *.
    destruct (Z.ltb_spec sum (2 ^ 64)) as [Hlt|Hge].
    + rewrite Z.mod_small by lia. subst sum. nia.
    + rewrite <- (Z.mod_unique_pos sum (2^64) 1 (sum - 2^64)) by lia. subst sum. nia.
  - intros j Hj. rewrite nth_upd_other by lia. apply Hag. lia.
  - rewrite upd_length. exact Hl.
  - destruct (sum <? 2 ^ 64); lia.
Qed.

(* [comment removed for export] *)
Lemma ladd_finish : forall x0 cur ys s n c N,
  ladd_inv x0 cur ys s n c -> (s + n <= N)%nat ->
  bval cur N + c * 2 ^ (64 * Z.of_nat (s + n)) = bval x0 N + bval ys n * 2 ^ (64 * Z.of_nat s).
Proof.
  intros x0 cur ys s n c N (Hv & Hag & Hl & Hc) HN.
  pose proof (bval_agree_above cur x0 (s + n) N HN Hag). lia.
Qed.

(* [comment removed for export] *)
Definition rip_inv (x0 cur ys : list word) (s n j : nat) : Prop :=
  bval cur j + 2 ^ (64 * Z.of_nat j) = bval x0 j + bval ys n * 2 ^ (64 * Z.of_nat s)
  /\ (forall i, (j <= i)%nat -> nth i cur w0 = nth i x0 w0)
  /\ length cur = length x0.

Lemma rip_inv_start : forall x0 cur ys s n, ladd_inv x0 cur ys s n 1 -> rip_inv x0 cur ys s n (s + n).
Proof. intros x0 cur ys s n (Hv & Hag & Hl & _). unfold rip_inv. repeat split; try assumption. lia. Qed.

(* [comment removed for export] *)
Lemma rip_inv_wrap : forall x0 cur ys s n j,
  rip_inv x0 cur ys s n j -> (j < length x0)%nat -> limbZ x0 j + 1 = 2 ^ 64 ->
  rip_inv x0 (upd cur j (Z_to_bv 64 (limbZ x0 j + 1))) ys s n (S j).
Proof.
  intros x0 cur ys s n j (Hv & Hag & Hl) Hj Hw. unfold rip_inv.
  split; [| split; [intros i Hi; rewrite nth_upd_other by lia; apply Hag; lia | rewrite upd_length; exact Hl]].
  rewrite bval_push by (rewrite Hl; exact Hj). rewrite Hw. rewrite unsigned_lit_wrap, Z.mod_same by lia.
  rewrite bval_S, pow64_S. pose proof (limbZ_range x0 j). nia.
Qed.

(* [comment removed for export] *)
Lemma rip_inv_stop : forall x0 cur ys s n j N,
  rip_inv x0 cur ys s n j -> (j < length x0)%nat -> limbZ x0 j + 1 < 2 ^ 64 -> (j < N)%nat ->
  bval (upd cur j (Z_to_bv 64 (limbZ x0 j + 1))) N = bval x0 N + bval ys n * 2 ^ (64 * Z.of_nat s).
Proof.
  intros x0 cur ys s n j N (Hv & Hag & Hl) Hj Hw HN.
  pose proof (limbZ_range x0 j) as Hx.
  assert (E1 : bval (upd cur j (Z_to_bv 64 (limbZ x0 j + 1))) (S j) = bval x0 (S j) + bval ys n * 2 ^ (64 * Z.of_nat s)).
  { rewrite bval_push by (rewrite Hl; exact Hj). rewrite unsigned_lit by lia. rewrite bval_S. nia. }
  pose proof (bval_agree_above (upd cur j (Z_to_bv 64 (limbZ x0 j + 1))) x0 (S j) N ltac:(lia)) as E2.
  assert (Hag' : forall i, (S j <= i)%nat -> nth i (upd cur j (Z_to_bv 64 (limbZ x0 j + 1))) w0 = nth i x0 w0).
  { intros i Hi. rewrite nth_upd_other by lia. apply Hag. lia. }
  specialize (E2 Hag'). lia.
Qed.

(* [comment removed for export] *)
Lemma rip_inv_push : forall x0 cur ys s n N,
  rip_inv x0 cur ys s n N -> (N < length x0)%nat ->
  bval (upd cur N (Z_to_bv 64 1)) (S N) = bval x0 N + bval ys n * 2 ^ (64 * Z.of_nat s).
Proof.
  intros x0 cur ys s n N (Hv & Hag & Hl) HN.
  rewrite bval_push by (rewrite Hl; exact HN). rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rip_room : forall x0 cur ys s n N,
  rip_inv x0 cur ys s n N -> bval x0 N + bval ys n * 2 ^ (64 * Z.of_nat s) < BIG_CAP -> (N < 62)%nat.
Proof.
  intros x0 cur ys s n N (Hv & _ & _) Hcap. unfold BIG_CAP in Hcap.
  pose proof (bval_nonneg cur N).
  destruct (Nat.lt_ge_cases N 62) as [|Hge]; [assumption|]. exfalso.
  assert (2 ^ (64 * 62) <= 2 ^ (64 * Z.of_nat N)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma ladd_carry0 : forall (wx : word) (y E : Z), 0 <= y < 2 ^ 64 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (v_sltu (Z_to_bv 64 (bv_unsigned wx + y)) wx))
                    (bv_unsigned (Z_to_bv 64 (Z.land 0 E))))
  = Z_to_bv 64 (if bv_unsigned wx + y + 0 <? 2 ^ 64 then 0 else 1).
Proof.
  intros wx y E Hy. pose proof (bv_unsigned_in_range 64 wx) as Hx. unfold bv_modulus in Hx.
  rewrite Z.land_0_l. rewrite (unsigned_lit 0) by lia. rewrite Z.lor_0_r.
  rewrite v_sltu_b2z. pose proof (zb_b2z_range (bv_unsigned (Z_to_bv 64 (bv_unsigned wx + y)) <? bv_unsigned wx)) as Hb.
  rewrite (unsigned_lit (Z.b2z _)) by lia. f_equal.
  rewrite unsigned_lit_wrap. rewrite Z.add_0_r.
  destruct (Z.lt_ge_cases (bv_unsigned wx + y) (2 ^ 64)) as [L|G].
  - rewrite Z.mod_small by lia. replace (bv_unsigned wx + y <? bv_unsigned wx) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (bv_unsigned wx + y <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - rewrite <- (Z.mod_unique_pos (bv_unsigned wx + y) (2^64) 1 (bv_unsigned wx + y - 2^64)) by lia.
    replace (bv_unsigned wx + y - 2 ^ 64 <? bv_unsigned wx) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (bv_unsigned wx + y <? 2 ^ 64) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma ladd_carry1 : forall (wx : word) (y : Z), 0 <= y < 2 ^ 64 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (v_sltu (Z_to_bv 64 (bv_unsigned wx + y)) wx))
                    (bv_unsigned (Z_to_bv 64 (Z.land 1 (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned wx + y + 1)) 1))))))
  = Z_to_bv 64 (if bv_unsigned wx + y + 1 <? 2 ^ 64 then 0 else 1).
Proof.
  intros wx y Hy. pose proof (bv_unsigned_in_range 64 wx) as Hx. unfold bv_modulus in Hx.
  rewrite v_sltu_b2z, v_sltiu_b2z. change (bv_wrap 64 1) with 1.
  rewrite !unsigned_lit_wrap.
  set (b1 := (bv_unsigned wx + y) mod 2 ^ 64 <? bv_unsigned wx).
  set (b2 := (bv_unsigned wx + y + 1) mod 2 ^ 64 <? 1).
  assert (E2 : Z.land 1 (Z.b2z b2 mod 2 ^ 64) = Z.b2z b2) by (destruct b2; reflexivity).
  rewrite E2. replace (Z.b2z b2 mod 2 ^ 64) with (Z.b2z b2) by (destruct b2; reflexivity).
  replace (Z.b2z b1 mod 2 ^ 64) with (Z.b2z b1) by (destruct b1; reflexivity).
  f_equal.
  destruct (Z.lt_ge_cases (bv_unsigned wx + y) (2 ^ 64)) as [L|G].
  - assert (Hb1 : b1 = false) by (subst b1; rewrite Z.mod_small by lia; apply Z.ltb_ge; lia). rewrite Hb1.
    destruct (Z.eq_dec (bv_unsigned wx + y + 1) (2 ^ 64)) as [E|NE].
    + assert (Hb2 : b2 = true) by (subst b2; rewrite E, Z.mod_same by lia; reflexivity). rewrite Hb2.
      replace (bv_unsigned wx + y + 1 <? 2 ^ 64) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + assert (Hb2 : b2 = false) by (subst b2; rewrite Z.mod_small by lia; apply Z.ltb_ge; lia). rewrite Hb2.
      replace (bv_unsigned wx + y + 1 <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - assert (Hb1 : b1 = true).
    { subst b1. rewrite <- (Z.mod_unique_pos (bv_unsigned wx + y) (2^64) 1 (bv_unsigned wx + y - 2^64)) by lia. apply Z.ltb_lt; lia. }
    rewrite Hb1. replace (bv_unsigned wx + y + 1 <? 2 ^ 64) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct b2; reflexivity.
Qed.

(* [comment removed for export] *)
Definition sad_inv (ws cur : list word) (y : Z) (i : nat) (cv : Z) : Prop :=
  (bval cur i + cv * 2 ^ (64 * Z.of_nat i) = bval ws i + y)%Z
  /\ (forall j, (i <= j)%nat -> nth j cur w0 = nth j ws w0)
  /\ length cur = length ws.

Lemma sad_inv_init : forall ws y, sad_inv ws ws y 0 y.
Proof. intros. split; [cbn; lia|]. split; [intros; reflexivity| reflexivity]. Qed.

Lemma sad_inv_step : forall ws cur y i cv,
  sad_inv ws cur y i cv -> (i < length ws)%nat -> (0 <= cv < 2^64)%Z ->
  let x := limbZ ws i in
  (bval (upd cur i (Z_to_bv 64 (x + cv))) (S i) + (if (x + cv <? 2^64)%Z then 0 else 1) * 2 ^ (64 * Z.of_nat (S i))
   = bval ws (S i) + y)%Z
  /\ (forall j, (S i <= j)%nat -> nth j (upd cur i (Z_to_bv 64 (x + cv))) w0 = nth j ws w0)
  /\ length (upd cur i (Z_to_bv 64 (x + cv))) = length ws.
Proof.
  intros ws cur y i cv (Hv & Hag & Hl) Hi Hcv x.
  pose proof (limbZ_range ws i) as Hx. fold x in Hx.
  split; [| split; [intros j Hj; rewrite nth_upd_other by lia; apply Hag; lia | rewrite upd_length; exact Hl]].
  rewrite bval_push by (rewrite Hl; exact Hi). rewrite bval_S, pow64_S.
  rewrite unsigned_lit_wrap.
  replace (limbZ ws i) with x by reflexivity.
  destruct (Z.ltb_spec (x + cv) (2 ^ 64)) as [Hlt|Hge].
  - rewrite Z.mod_small by lia. nia.
  - rewrite <- (Z.mod_unique_pos (x + cv) (2^64) 1 (x + cv - 2^64)) by lia. nia.
Qed.

(* [comment removed for export] *)
Lemma sad_inv_wrap : forall ws cur y i cv,
  sad_inv ws cur y i cv -> (i < length ws)%nat -> (0 <= cv < 2^64)%Z -> (2^64 <= limbZ ws i + cv)%Z ->
  sad_inv ws (upd cur i (Z_to_bv 64 (limbZ ws i + cv))) y (S i) 1.
Proof.
  intros ws cur y i cv INV Hi Hcv Hw. pose proof (sad_inv_step ws cur y i cv INV Hi Hcv) as (A & B & C).
  replace (limbZ ws i + cv <? 2 ^ 64)%Z with false in A by (symmetry; apply Z.ltb_ge; lia).
  split; [lia| split; [exact B| exact C]].
Qed.

(* [comment removed for export] *)
Lemma sad_inv_stop : forall ws cur y i cv n,
  sad_inv ws cur y i cv -> (i < length ws)%nat -> (0 <= cv < 2^64)%Z -> (limbZ ws i + cv < 2^64)%Z -> (i < n)%nat ->
  bval (upd cur i (Z_to_bv 64 (limbZ ws i + cv))) n = (bval ws n + y)%Z.
Proof.
  intros ws cur y i cv n INV Hi Hcv Hw Hn. pose proof (sad_inv_step ws cur y i cv INV Hi Hcv) as (A & B & C).
  replace (limbZ ws i + cv <? 2 ^ 64)%Z with true in A by (symmetry; apply Z.ltb_lt; lia).
  pose proof (bval_agree_above _ _ (S i) n ltac:(lia) B). lia.
Qed.

(* [comment removed for export] *)
Lemma sad_inv_push : forall ws cur y n cv,
  sad_inv ws cur y n cv -> (n < length ws)%nat -> (0 <= cv < 2^64)%Z ->
  bval (upd cur n (Z_to_bv 64 cv)) (S n) = (bval ws n + y)%Z.
Proof.
  intros ws cur y n cv (Hv & Hag & Hl) Hn Hcv.
  rewrite bval_push by (rewrite Hl; exact Hn). rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sad_room : forall ws cur y n cv,
  sad_inv ws cur y n cv -> (1 <= cv)%Z -> (bval ws n + y < BIG_CAP)%Z -> (n < 62)%nat.
Proof.
  intros ws cur y n cv (Hv & _ & _) Hcv Hcap. unfold BIG_CAP in Hcap.
  pose proof (bval_nonneg cur n).
  destruct (Nat.lt_ge_cases n 62) as [|Hge]; [assumption|]. exfalso.
  assert (2 ^ (64 * 62) <= 2 ^ (64 * Z.of_nat n)) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ (64 * Z.of_nat n) <= cv * 2 ^ (64 * Z.of_nat n)) by nia. lia.
Qed.

(* [comment removed for export] *)
Lemma sad_bnorm_stop : forall ws cur y i cv n,
  sad_inv ws cur y i cv -> (i < length ws)%nat -> (1 <= cv < 2^64)%Z -> (limbZ ws i + cv < 2^64)%Z -> (i < n)%nat ->
  bnorm ws n -> bnorm (upd cur i (Z_to_bv 64 (limbZ ws i + cv))) n.
Proof.
  intros ws cur y i cv n (Hv & Hag & Hl) Hi Hcv Hw Hn BN. right. unfold limbZ in *.
  pose proof (limbZ_range ws i) as Hx. unfold limbZ in Hx.
  destruct (Nat.eq_dec (n - 1) i) as [E|E].
  - rewrite E, nth_upd_same by (rewrite Hl; exact Hi). rewrite unsigned_lit by lia. lia.
  - rewrite nth_upd_other by lia. rewrite Hag by lia. apply (bnorm_top ws n ltac:(lia) BN).
Qed.

(* [comment removed for export] *)
Lemma addnative_bound : forall b y v K, (0 <= K)%Z -> (0 <= b < 2 ^ (64 * K))%Z -> (0 <= y < 2^64)%Z -> (0 <= v < 2^64)%Z ->
  (b * y + v < 2 ^ (64 * (K + 1)))%Z.
Proof.
  intros b y v K HK Hb Hy Hvv.
  replace (64 * (K + 1))%Z with (64 * K + 64)%Z by lia. rewrite Z.pow_add_r by lia.
  assert (b * y <= (2 ^ (64 * K) - 1) * (2 ^ 64 - 1))%Z by nia.
  nia.
Qed.

(* [comment removed for export] *)
Lemma cap_mul : forall b y K, (0 <= K <= 61)%Z -> (0 <= b < 2 ^ (64 * K))%Z -> (0 <= y < 2^64)%Z -> (b * y < BIG_CAP)%Z.
Proof.
  intros b y K HK Hb Hy. unfold BIG_CAP.
  assert (H1 : (b * y < 2 ^ (64 * K) * 2 ^ 64)%Z).
  { destruct (Z.eq_dec y 0) as [->|]. { rewrite Z.mul_0_r. apply Z.mul_pos_pos; apply Z.pow_pos_nonneg; lia. }
    apply Z.lt_le_trans with (2 ^ (64 * K) * y)%Z. { apply Z.mul_lt_mono_pos_r; lia. }
    apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite <- Z.pow_add_r in H1 by lia.
  eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.
