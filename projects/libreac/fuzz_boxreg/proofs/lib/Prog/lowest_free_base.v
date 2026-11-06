From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg BoxregRd lowest_free_base_c.
Import ListNotations.
Open Scope Z_scope.

Definition slice_meets_f (n : Z) (base nch : Z -> Z) (b k : Z) : Prop :=
  exists i, 0 <= i < n /\ b < base i + nch i /\ base i < b + k.

Definition lowest_free_f (n fabric : Z) (base nch : Z -> Z) (k res : Z) : Prop :=
  (res = -1 /\ forall b, 0 <= b -> b + k <= fabric -> slice_meets_f n base nch b k) \/
  (0 <= res /\ res + k <= fabric /\ ~ slice_meets_f n base nch res k /\
   forall b, 0 <= b < res -> slice_meets_f n base nch b k).

Lemma lfb_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  first [ reflexivity | f_equal; apply firstn_all2; rewrite length_le4; lia ].
Qed.

Lemma lfb_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lfb_swrap : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. change (2^31) with 2147483648 in Hz. lia. Qed.

Lemma lfb_signed : forall x, -2^63 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (x mod 18446744073709551616) 9223372036854775808); Z.div_mod_to_equations; lia.
Qed.

Lemma lfb_lts : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !lfb_signed by lia. reflexivity. Qed.

Lemma lfb_eqb : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in Hx, Hy.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma lfb_zx32 : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. f_equal. apply Z.mod_small. lia. Qed.

Ltac lfb_cl := repeat first
  [ rewrite lfb_sx32 by lia | rewrite lfb_zx32 by lia | rewrite unsigned_lit by lia
  | rewrite lfb_swrap by lia | rewrite lfb_lts by lia | rewrite lfb_eqb by lia ].

Definition lfb_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (n fabric : Z) (base nch : Z -> Z) (k : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' res a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 res a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m (seg_rom rsegs) /\
    exists z, res = Z_to_bv 64 z /\ lowest_free_f n fabric base nch k z.

Ltac lfb_close z :=
  apply evt_done; cbv beta delta [lfb_q mkR]; do 15 eexists; split; [ reflexivity | ];
  exists z; split; [ word_eq_tac | unfold lowest_free_f ].

Lemma lfb_inner : forall (d : nat) (i : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
    (r n fabric b k : Z) (base nch : Z -> Z),
  d = Z.to_nat (n - i) -> 0 <= i < n -> n <= 5 -> 0 <= b -> 1 <= k -> b + k <= fabric <= 40 ->
  t0 = Z_to_bv 64 (r + 12 + 56 * i) -> t1 = Z_to_bv 64 (n - i) ->
  a1 = Z_to_bv 64 (b + k) -> a4 = Z_to_bv 64 b ->
  (forall j, 0 <= j < n ->
     bytes_at rsegs m (r + 56 * j + 8) (le4 (Z_to_bv 64 (base j))) /\
     bytes_at rsegs m (r + 56 * j + 12) (le4 (Z_to_bv 64 (nch j))) /\
     0 <= base j /\ 0 <= nch j /\ base j + nch j <= fabric) ->
  (forall j, i <= j < n -> b < base j + nch j -> base j < b + k -> forall x5 x6 x7 x28 : word,
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
                     F (Z_to_bv 64 0x139fc) fc None m (seg_rom rsegs))) ->
  ((forall j, i <= j < n -> ~ (b < base j + nch j /\ base j < b + k)) -> forall x5 x6 x7 x28 : word,
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
                     F (Z_to_bv 64 0x13a0c) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x139d8) fc None m (seg_rom rsegs)).
Proof.
  induction d as [|d IH];
    intros i ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q
      r n fabric b k base nch Hd Hi Hn Hb Hk Hf E5 E6 E11 E14 HB KT KF; [ lia | ].
  subst t0 t1 a1 a4.
  destruct (HB i ltac:(lia)) as (B1 & B2 & G1 & G2 & G3).
  pose proof (lfb_rd4 _ _ _ B1) as R1. pose proof (lfb_rd4 _ _ _ B2) as R2.
  step. lfb_cl. step. lfb_cl.
  if_cases HC1; zify_bool HC1.
  - step. step. step. lfb_cl.
    if_cases HC2; zify_bool HC2.
    + eapply IH with (i := i + 1) (r := r) (n := n) (fabric := fabric) (b := b) (k := k) (base := base) (nch := nch);
        [ lia | lia | lia | lia | lia | lia | word_eq_tac | word_eq_tac | reflexivity | reflexivity | exact HB
        | intros j Hj H1 H2 x5 x6 x7 x28; apply (KT j); lia
        | intros HF x5 x6 x7 x28; apply KF; intros j Hj [H1 H2];
          destruct (Z.eq_dec j i) as [->|NE]; [ lia | apply (HF j); [ lia | split; assumption ] ] ].
    + step. apply KF. intros j Hj [H1 H2]. assert (j = i) by lia. subst j. lia.
  - step. lfb_cl. step. lfb_cl. step. lfb_cl.
    if_cases HC3; zify_bool HC3.
    + eapply (KT i); lia.
    + step. step. step. lfb_cl.
      if_cases HC2; zify_bool HC2.
      * eapply IH with (i := i + 1) (r := r) (n := n) (fabric := fabric) (b := b) (k := k) (base := base) (nch := nch);
          [ lia | lia | lia | lia | lia | lia | word_eq_tac | word_eq_tac | reflexivity | reflexivity | exact HB
          | intros j Hj H1 H2 x5 x6 x7 x28; apply (KT j); lia
          | intros HF x5 x6 x7 x28; apply KF; intros j Hj [H1 H2];
            destruct (Z.eq_dec j i) as [->|NE]; [ lia | apply (HF j); [ lia | split; assumption ] ] ].
      * step. apply KF. intros j Hj [H1 H2]. assert (j = i) by lia. subst j. lia.
Qed.

Lemma lfb_outer : forall (d : nat) (b : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r n fabric k : Z) (base nch : Z -> Z),
  d = Z.to_nat (fabric - b) -> 0 <= n <= 5 -> 0 <= b -> 1 <= k -> b + k <= fabric <= 40 ->
  a0 = Z_to_bv 64 (-1) -> a1 = Z_to_bv 64 (b + k) -> a2 = Z_to_bv 64 (r + 12) -> a3 = Z_to_bv 64 fabric ->
  a4 = Z_to_bv 64 b -> a5 = Z_to_bv 64 n -> a6 = Z_to_bv 64 (k + 1) -> a7 = Z_to_bv 64 n ->
  (forall j, 0 <= j < n ->
     bytes_at rsegs m (r + 56 * j + 8) (le4 (Z_to_bv 64 (base j))) /\
     bytes_at rsegs m (r + 56 * j + 12) (le4 (Z_to_bv 64 (nch j))) /\
     0 <= base j /\ 0 <= nch j /\ base j + nch j <= fabric) ->
  (forall c, 0 <= c < b -> slice_meets_f n base nch c k) ->
  evt rsegs (lfb_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n fabric base nch k)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139cc) fc None m (seg_rom rsegs)).
Proof.
  induction d as [|d IH];
    intros b ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      r n fabric k base nch Hd Hn Hb Hk Hf E10 E11 E12 E13 E14 E15 E16 E17 HB HM; [ lia | ].
  subst a0 a1 a2 a3 a4 a5 a6 a7.
  step. step. step. lfb_cl.
  if_cases HC1; zify_bool HC1.
  - assert (B0 : b = 0).
    { destruct (Z.eq_dec b 0) as [|NE]; [ assumption | ].
      destruct (HM 0 ltac:(lia)) as (j & Hj & _). lia. }
    subst b. step. step. lfb_close 0.
    right. split; [ lia | split; [ lia | split ] ].
    + intros (j & Hj & _). lia.
    + intros c Hc. lia.
  - eapply lfb_inner with (d := Z.to_nat (n - 0)) (i := 0) (r := r) (n := n) (fabric := fabric) (b := b) (k := k)
      (base := base) (nch := nch);
      [ reflexivity | lia | lia | lia | lia | lia | word_eq_tac | word_eq_tac | reflexivity | reflexivity | exact HB
      | intros j Hj H1 H2 x5 x6 x7 x28 | intros HF x5 x6 x7 x28 ].
    + step. lfb_cl. step. lfb_cl. step. lfb_cl.
      if_cases HC2; zify_bool HC2.
      * eapply IH with (b := b + 1) (r := r) (n := n) (fabric := fabric) (k := k) (base := base) (nch := nch);
          [ lia | lia | lia | lia | lia | reflexivity | word_eq_tac | reflexivity | reflexivity | word_eq_tac
          | reflexivity | reflexivity | reflexivity | exact HB | ].
        intros c Hc. destruct (Z.lt_ge_cases c b) as [L|L]; [ apply HM; lia | ].
        exists j. lia.
      * step. step. lfb_close (-1).
        left. split; [ reflexivity | ].
        intros c Hc0 Hck. destruct (Z.lt_ge_cases c b) as [L|L]; [ apply HM; lia | ].
        exists j. lia.
    + step. step. lfb_close b.
      right. split; [ lia | split; [ lia | split; [ | exact HM ] ] ].
      intros (j & Hj & H1 & H2). exact (HF j ltac:(lia) (conj H1 H2)).
Qed.

Lemma lowest_free_base_fields :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (r k n fabric : Z) (base nch : Z -> Z),
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 k ->
    1 <= k < 2^31 ->
    0 <= n <= 5 -> 1 <= fabric <= 40 ->
    bytes_at rsegs m (r + 280) (le4 (Z_to_bv 64 n)) ->
    bytes_at rsegs m (r + 284) (le4 (Z_to_bv 64 fabric)) ->
    (forall i, 0 <= i < n ->
       bytes_at rsegs m (r + 56 * i + 8) (le4 (Z_to_bv 64 (base i))) /\
       bytes_at rsegs m (r + 56 * i + 12) (le4 (Z_to_bv 64 (nch i))) /\
       0 <= base i /\ 0 <= nch i /\ base i + nch i <= fabric) ->
    evt rsegs (lfb_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n fabric base nch k)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LOWEST_FREE_BASE) fc None m (seg_rom rsegs)).
Proof.
  unfold LOWEST_FREE_BASE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    r k n fabric base nch E0 E1 Hk Hn Hf BN BF HB.
  subst a0 a1.
  pose proof (lfb_rd4 _ _ _ BN) as RN. pose proof (lfb_rd4 _ _ _ BF) as RF.
  step. step. lfb_cl. step. step. lfb_cl.
  if_cases HC1; zify_bool HC1.
  - step. step. lfb_cl. step. step. lfb_cl. step.
    eapply lfb_outer with (d := Z.to_nat (fabric - 0)) (b := 0) (r := r) (n := n) (fabric := fabric) (k := k)
      (base := base) (nch := nch);
      [ reflexivity | lia | lia | lia | lia | word_eq_tac | word_eq_tac | word_eq_tac | word_eq_tac | word_eq_tac
      | word_eq_tac | word_eq_tac | word_eq_tac | exact HB | intros c Hc; lia ].
  - step. lfb_close (-1).
    left. split; [ reflexivity | ].
    intros c Hc Hck. lia.
Qed.

Theorem lowest_free_base_holds : lowest_free_base_contract.
Proof.
  unfold lowest_free_base_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    r k bs E0 E1 Hk HB HL H1 H2 H3.
  unfold boxreg_B1 in H1. unfold boxreg_B2 in H2.
  eapply evt_mono.
  - apply (lowest_free_base_fields ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m r k (bx_n bs) (bx_fabric bs) (bx_base bs) (bx_nch bs) E0 E1 Hk H1 H2).
    + exact (rd4_bytes_at m r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)).
    + exact (rd4_bytes_at m r bs 284 HB ltac:(lia) ltac:(rewrite HL; lia)).
    + intros i Hi. destruct (H3 i Hi) as (_ & Hn2 & _ & Hb0 & Hbn).
      split; [ | split; [ | lia ] ].
      * replace (r + 56 * i + 8) with (r + (56 * i + 8)) by lia.
        exact (rd4_bytes_at m r bs (56 * i + 8) HB ltac:(lia) ltac:(rewrite HL; lia)).
      * replace (r + 56 * i + 12) with (r + (56 * i + 12)) by lia.
        exact (rd4_bytes_at m r bs (56 * i + 12) HB ltac:(lia) ltac:(rewrite HL; lia)).
  - intros ms' H. exact H.
Qed.
