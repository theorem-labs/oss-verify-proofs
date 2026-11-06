From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import RcModel RcLib RcLeaf.
Import ListNotations.
Open Scope Z_scope.

Lemma rcl_eqb : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rcl_store_ok : forall segs m a n (j : nat), wr_at segs m a n -> Z.of_nat j <= n ->
  store_ok segs m (wa a) j = true.
Proof.
  intros segs m a n j H Hj. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  apply (wr_at_store_ok segs m a n 0 j H); lia.
Qed.

Lemma rcl_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rcl_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rcl_zxb_eqb : forall (b : byte) k, 0 <= k < 2^64 -> bv_eqb (zxb b) (Z_to_bv 64 k) = (bv_unsigned b =? k).
Proof. intros b k Hk. unfold zxb. pose proof (byte_range b). apply rcl_eqb; lia. Qed.

Lemma rcl_rd : forall segs m A bs (i : nat) b, bytes_at segs m A bs -> nth_error bs i = Some b ->
  ov_read_bytes segs m (wa (A + Z.of_nat i)) 1 = Some [b].
Proof.
  intros segs m A bs i b HB E.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; congruence).
  rewrite (rd_byte segs m A bs i HB Hi). rewrite (nth_error_nth bs i (Z_to_bv 8 0) E). reflexivity.
Qed.

Lemma rcl_fin127 : forall s, 0 <= s < 2^64 ->
  Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 s)) 127)) 1) + -1) =
  Z_to_bv 64 (if s mod 128 =? 0 then 0 else -1).
Proof.
  intros s Hs. rewrite v_sltiu_b2z. rewrite (unsigned_lit s Hs).
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2^7) with 128.
  pose proof (Z.mod_pos_bound s 128 ltac:(lia)) as M.
  rewrite (unsigned_lit (s mod 128)) by lia.
  destruct (Z.eqb_spec (s mod 128) 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (s mod 128 <? bv_wrap 64 1) with false by (symmetry; apply Z.ltb_ge; change (bv_wrap 64 1) with 1; lia).
    reflexivity.
Qed.

Lemma rcl_cnt_range : forall f bs k, 0 <= cnt f bs k <= Z.of_nat k.
Proof. intros f bs k. induction k as [|k IH]; cbn [cnt]; [lia|]. destruct (f _); lia. Qed.

Lemma rcl_cnt_S : forall f bs k, cnt f bs (S k) = cnt f bs k + (if f (bt bs (8 + k)) then 1 else 0).
Proof. reflexivity. Qed.

Lemma rcl_out128 : forall x, 0 <= x < 256 -> x < 128 \/ 132 < x ->
  bv_ltu (Z_to_bv 64 4) (Z_to_bv 64 (x + -128)) = true.
Proof.
  intros x Hx Hc. unfold bv_ltu. rewrite !unsigned_lit_wrap. apply Z.ltb_lt.
  change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.

Lemma rcl_small13 : forall (P : Z -> Prop),
  P 0 -> P 1 -> P 2 -> P 3 -> P 4 -> P 5 -> P 6 -> P 7 -> P 8 -> P 9 -> P 10 -> P 11 -> P 12 ->
  forall n, 0 <= n <= 12 -> P n.
Proof.
  intros P H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 n Hn.
  assert (E : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
              n = 11 \/ n = 12) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]; subst n; assumption.
Qed.

Lemma rcl_addiw : forall c, 0 <= c <= 12 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 c) + 1)) = Z_to_bv 64 (c + 1).
Proof. intros c Hc. pattern c. apply rcl_small13; [ | | | | | | | | | | | | | exact Hc]; vm_compute; reflexivity. Qed.

Lemma rcl_blt1 : forall c, 0 <= c <= 12 -> bv_lts (Z_to_bv 64 (c + 1)) (Z_to_bv 64 c) = false.
Proof. intros c Hc. pattern c. apply rcl_small13; [ | | | | | | | | | | | | | exact Hc]; vm_compute; reflexivity. Qed.

Lemma rcl_a7 : forall p, 0 <= p -> p + 20 <= 2^64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_sltiu (Z_to_bv 64 p) (-8)))))
                     (bv_unsigned (Z_to_bv 64 (p + 8)))) = Z_to_bv 64 (p + 8).
Proof.
  intros p H1 H2. rewrite v_sltiu_b2z. rewrite (unsigned_lit p) by lia.
  replace (p <? bv_wrap 64 (-8)) with true
    by (symmetry; apply Z.ltb_lt; change (bv_wrap 64 (-8)) with 18446744073709551608; lia).
  change (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 (Z.b2z true))))) with (Z.ones 64).
  rewrite (unsigned_lit (p + 8)) by lia.
  rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma rcl_all256 : forall f : Z -> bool, forallb f (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 256 -> f x = true.
Proof.
  intros f H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x).
  split; [lia|]. apply in_seq. lia.
Qed.

Lemma rcl_ori_eqb : forall x, 0 <= x < 256 ->
  bv_eqb (Z_to_bv 64 (Z.lor x 4)) (Z_to_bv 64 132) = (x =? 128) || (x =? 132).
Proof.
  intros x Hx. apply Bool.eqb_prop.
  exact (rcl_all256 (fun x => Bool.eqb (bv_eqb (Z_to_bv 64 (Z.lor x 4)) (Z_to_bv 64 132)) ((x =? 128) || (x =? 132)))
           ltac:(vm_compute; reflexivity) x Hx).
Qed.

Ltac rc_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; fold_lit_ux;
  repeat (rewrite unsigned_lit by lia); solve_cond_rec.

Ltac rc_false :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; rc_cond]
  end.

Ltac rc_vm :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

Ltac rc_small n :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [cbv iota | symmetry; pattern n; apply rcl_small13; [ | | | | | | | | | | | | | lia]; vm_compute; reflexivity]
  end.
