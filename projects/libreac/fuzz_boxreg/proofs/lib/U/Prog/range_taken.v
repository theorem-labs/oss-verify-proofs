From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Step Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd lowest_free_base_c range_taken_c.
Import ListNotations.
Open Scope Z_scope.

Lemma rt_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rt_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  first [ reflexivity | f_equal; apply firstn_all2; rewrite length_le4; lia ].
Qed.

Lemma rt_land3 : forall r, Z.land r 3 = r mod 4.
Proof. intros r. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rt_not : forall r, 0 <= r < 2^64 -> Z.lxor r 18446744073709551615 = 2^64 - 1 - r.
Proof.
  intros r Hr. change 18446744073709551615 with (Z.ones 64).
  assert (L : Z.land (Z.lxor r (Z.ones 64)) r = 0).
  { apply Z.bits_inj_0. intros i. rewrite Z.land_spec, Z.lxor_spec.
    destruct (Z.testbit r i) eqn:E; [ | apply andb_false_r ].
    destruct (Z.ltb_spec i 0) as [N|N]; [ rewrite Z.testbit_neg_r in E by lia; discriminate | ].
    destruct (Z.ltb_spec i 64) as [M|M].
    - rewrite Z.ones_spec_low by lia. reflexivity.
    - rewrite (Z_testbit_high 64 r i) in E by lia. discriminate. }
  pose proof (Z.add_nocarry_lxor _ _ L) as A.
  rewrite (Z.lxor_comm (Z.lxor r (Z.ones 64)) r), <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in A.
  rewrite Z.ones_equiv in A |- *. lia.
Qed.

Lemma rt_slt0 : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> y <= x ->
  v_slt (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 0.
Proof.
  intros x y Hx Hy H. unfold v_slt, c_lts. rewrite lts_lit by lia.
  destruct (Z.ltb_spec x y); [ lia | reflexivity ].
Qed.

Lemma rt_slt1 : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> x < y ->
  v_slt (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 1.
Proof.
  intros x y Hx Hy H. unfold v_slt, c_lts. rewrite lts_lit by lia.
  destruct (Z.ltb_spec x y); [ reflexivity | lia ].
Qed.

Lemma rt_t0 : forall n, 0 < n < 2^63 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 n)))))
                     (bv_unsigned (Z_to_bv 64 n))) = Z_to_bv 64 n.
Proof.
  intros n Hn. rewrite rt_slt1 by lia.
  rewrite (unsigned_lit n) by lia.
  replace (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Definition rt_meets (n : Z) (base nch : Z -> Z) (b k : Z) : Prop :=
  exists i, 0 <= i < n /\ b < base i + nch i /\ base i < b + k.

Definition rt_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (n : Z) (base nch : Z -> Z) (b k : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' res a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 res a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m (seg_rom rsegs) /\
    ((rt_meets n base nch b k /\ res = Z_to_bv 64 1) \/ (~ rt_meets n base nch b k /\ res = Z_to_bv 64 0)).

Ltac rt_close :=
  apply evt_done; cbv beta delta [rt_q mkR]; do 15 eexists; split; [ reflexivity | ].

Lemma rt_loop : forall (d : nat) (i : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r n b k : Z) (base nch : Z -> Z),
  d = Z.to_nat (n - i) -> 0 <= i < n -> n <= 5 -> 0 <= r -> r + 288 <= 2^64 ->
  0 <= b -> 0 <= k -> b + k <= 40 ->
  a0 = Z_to_bv 64 (r + 12 + 56 * i) -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 (b + k) -> a3 = Z_to_bv 64 n ->
  a4 = Z_to_bv 64 i -> a5 = Z_to_bv 64 (56 * i) -> a6 = Z_to_bv 64 (2^64 - 1 - r) -> a7 = Z_to_bv 64 0 ->
  t0 = Z_to_bv 64 n -> t1 = Z_to_bv 64 5 ->
  (forall j, 0 <= j < n ->
     ov_read_bytes rsegs m (wa (r + 56 * j + 8)) 4 = Some (le4 (Z_to_bv 64 (base j))) /\
     ov_read_bytes rsegs m (wa (r + 56 * j + 12)) 4 = Some (le4 (Z_to_bv 64 (nch j))) /\
     0 <= base j /\ 0 <= nch j /\ base j + nch j <= 40) ->
  (forall j, 0 <= j < i -> ~ (b < base j + nch j /\ base j < b + k)) ->
  evt rsegs (rt_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n base nch b k)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13cf0) fc None m (seg_rom rsegs)).
Proof.
  induction d as [|d IH];
    intros i ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      r n b k base nch Hd Hi Hn Hr0 Hr Hb Hk Hbk E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 HB HN; [ lia | ].
  subst a0 a1 a2 a3 a4 a5 a6 a7 t0 t1.
  destruct (HB i ltac:(lia)) as (R1 & R2 & G1 & G2 & G3).
  step. if_cases HC; zify_cond HC; [ exfalso; Z.div_mod_to_equations; lia | ].
  step. if_cases HC2; zify_cond HC2; [ exfalso; Z.div_mod_to_equations; lia | ].
  step. rewrite rt_sx32 by lia.
  step. rewrite rt_sx32 by lia.
  step. step. rewrite swrap_add by lia.
  step. if_cases HD; zify_cond HD; [ exfalso; Z.div_mod_to_equations; lia | ].
  step. rewrite swrap_addi by lia.
  assert (NEXT : ~ (b < base i + nch i /\ base i < b + k) -> forall x7 x28 x29 : word,
    evt rsegs (rt_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n base nch b k)
      (MS (mkR ra sp gp tp (Z_to_bv 64 n) (Z_to_bv 64 5) x7 s0 s1 (Z_to_bv 64 (r + 12 + 56 * i)) (Z_to_bv 64 b)
               (Z_to_bv 64 (b + k)) (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 (56 * i))
               (Z_to_bv 64 (2^64 - 1 - r)) (Z_to_bv 64 0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
          F (Z_to_bv 64 0x13d1c) fc None m (seg_rom rsegs))).
  { intros NM x7 x28 x29.
    step. step. step. step.
    if_cases HG; zify_cond HG; rewrite ?Z.mod_small in HG by lia.
    - eapply IH with (i := i + 1) (r := r) (n := n) (b := b) (k := k) (base := base) (nch := nch);
        [ lia | lia | lia | lia | lia | lia | lia | lia
        | word_eq_tac | reflexivity | reflexivity | reflexivity | word_eq_tac | word_eq_tac | reflexivity
        | reflexivity | reflexivity | reflexivity | exact HB | ].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [ exact NM | apply HN; lia ].
    - step. step. step. rt_close.
      right. split.
      + intros (j & Hj & H1 & H2). destruct (Z.eq_dec j i) as [->|NE]; [ exact (NM (conj H1 H2)) | ].
        exact (HN j ltac:(lia) (conj H1 H2)).
      + apply rt_slt0; lia. }
  step. rewrite lts_lit by lia.
  if_cases HE; zify_bool HE.
  - apply NEXT. intros [H1 H2]. lia.
  - step. if_false.
    step. rewrite lts_lit by lia.
    if_cases HF; zify_bool HF.
    + step. step. rt_close.
      left. split; [ exists i; split; [ lia | split; lia ] | apply rt_slt1; lia ].
    + apply NEXT. intros [H1 H2]. lia.
Qed.

Lemma rt_fields :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r b k n : Z) (base nch : Z -> Z),
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 k ->
    0 <= r -> r + 288 <= 2^64 -> r mod 4 = 0 -> 0 <= n <= 5 -> 0 <= b -> 0 <= k -> b + k <= 40 ->
    ov_read_bytes rsegs m (wa (r + 280)) 4 = Some (le4 (Z_to_bv 64 n)) ->
    (forall j, 0 <= j < n ->
       ov_read_bytes rsegs m (wa (r + 56 * j + 8)) 4 = Some (le4 (Z_to_bv 64 (base j))) /\
       ov_read_bytes rsegs m (wa (r + 56 * j + 12)) 4 = Some (le4 (Z_to_bv 64 (nch j))) /\
       0 <= base j /\ 0 <= nch j /\ base j + nch j <= 40) ->
    evt rsegs (rt_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n base nch b k)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RANGE_TAKEN) fc None m (seg_rom rsegs)).
Proof.
  unfold RANGE_TAKEN.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    r b k n base nch E0 E1 E2 Hr0 Hr H4 Hn Hb Hk Hbk RN HB.
  subst a0 a1 a2.
  step. step. if_cases HC; zify_cond HC; [ exfalso; rewrite rt_land3 in HC; lia | ].
  step. rewrite rt_sx32 by lia.
  step. rewrite lts_lit by lia.
  if_cases HD; zify_bool HD.
  - step. step. step. rt_close.
    right. split; [ intros (j & Hj & _); lia | apply rt_slt0; lia ].
  - do 12 step.
    eapply rt_loop with (d := Z.to_nat (n - 0)) (i := 0) (r := r) (n := n) (b := b) (k := k) (base := base)
      (nch := nch);
      [ reflexivity | lia | lia | lia | lia | lia | lia | lia
      | word_eq_tac | reflexivity | rewrite swrap_add by lia; reflexivity | reflexivity | reflexivity
      | reflexivity | rewrite unsigned_lit by lia; rewrite rt_not by lia; reflexivity
      | rewrite swrap_add by lia; rewrite Z.lxor_nilpotent; reflexivity | apply rt_t0; lia | reflexivity
      | exact HB | intros j Hj; lia ].
Qed.

Theorem range_taken_holds : range_taken_contract.
Proof.
  unfold range_taken_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    r b k bs E0 E1 E2 HB HL H4 H1 H40 H3 Hb Hk Hbk.
  unfold boxreg_B1 in H1.
  pose proof (bytes_at_bound rsegs m r bs HB) as RB. rewrite HL in RB. change (Z.of_nat 288) with 288 in RB.
  eapply evt_mono.
  - apply (rt_fields ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m r b k (bx_n bs) (bx_base bs) (bx_nch bs) E0 E1 E2); [ lia | lia | exact H4 | lia | lia | lia | lia
           | | ].
    + exact (rt_rd4 _ _ _ (rd4_bytes_at m r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia))).
    + intros j Hj. destruct (H3 j Hj) as (G1 & G2 & G3).
      split; [ | split; [ | lia ] ].
      * replace (r + 56 * j + 8) with (r + (56 * j + 8)) by lia.
        exact (rt_rd4 _ _ _ (rd4_bytes_at m r bs (56 * j + 8) HB ltac:(lia) ltac:(rewrite HL; lia))).
      * replace (r + 56 * j + 12) with (r + (56 * j + 12)) by lia.
        exact (rt_rd4 _ _ _ (rd4_bytes_at m r bs (56 * j + 12) HB ltac:(lia) ltac:(rewrite HL; lia))).
  - intros ms' H. exact H.
Qed.
