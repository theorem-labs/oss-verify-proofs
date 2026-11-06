(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_memset_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition b0 : byte := Z_to_bv 8 0.
Fixpoint incov (l : list (Z * Z)) (a : Z) : Prop :=
  match l with [] => False | (lo, hi) :: l' => (lo <= a < hi)%Z \/ incov l' a end.
Definition zfill (m : word -> option byte) (l : list (Z * Z)) : Prop :=
  forall a, (0 <= a < 2^64)%Z -> incov l a -> m (wa a) = Some b0.

Lemma zfill_nil : forall m, zfill m [].
Proof. intros m a _ H. destruct H. Qed.

Lemma nth_error_repeat_lt : forall {A} (x : A) n i, (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof. intros A x n. induction n as [|n IH]; intros i Hi; [lia|]. destruct i; cbn; [reflexivity| apply IH; lia]. Qed.

Lemma zfill_store : forall m l (A : Z) (w : nat),
  zfill m l -> (0 <= A)%Z -> (A + Z.of_nat w <= 2^64)%Z ->
  zfill (write_to_mem m (wa A) (repeat b0 w)) ((A, A + Z.of_nat w)%Z :: l).
Proof.
  intros m l A w ZF HA Hw a Ra Ha. cbn in Ha.
  rewrite write_to_mem_spec by (rewrite ?repeat_length; lia). rewrite repeat_length, wa_unsigned by lia.
  destruct (Z.leb_spec0 A a); destruct (Z.ltb_spec0 a (A + Z.of_nat w)); cbn [andb].
  - apply nth_error_repeat_lt. lia.
  - apply ZF; [lia|]. destruct Ha; [lia| assumption].
  - apply ZF; [lia|]. destruct Ha; [lia| assumption].
  - apply ZF; [lia|]. destruct Ha; [lia| assumption].
Qed.

Lemma zfill_weaken : forall m l l', zfill m l -> (forall a, incov l' a -> incov l a) -> zfill m l'.
Proof. intros m l l' ZF H a Ra Ha. apply ZF; [exact Ra| apply H; exact Ha]. Qed.

Lemma u8arr_of_zfill : forall segs m D N l,
  wr_at segs m D N -> (0 <= N)%Z -> zfill m l -> (forall a, (D <= a < D + N)%Z -> incov l a) ->
  u8arr segs m D (repeat b0 (Z.to_nat N)).
Proof.
  intros segs m D N l WR HN0 ZF COV. destruct WR as (HD & HN & W).
  split.
  - split; [lia|]. split. { rewrite repeat_length. lia. }
    intros i Hi. rewrite repeat_length in Hi. unfold mrd. rewrite (ZF (D + Z.of_nat i)%Z) by (first [lia | apply COV; lia]).
    symmetry. apply nth_error_repeat_lt. exact Hi.
  - rewrite repeat_length. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
Qed.

Lemma le1_zero : le1 (Z_to_bv 64 0) = repeat b0 1. Proof. reflexivity. Qed.
Lemma le4_zero : le4 (Z_to_bv 64 0) = repeat b0 4. Proof. reflexivity. Qed.
Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat b0 8. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac zstore k w :=
  lazymatch goal with
  | WR : wr_at ?segs ?m ?D ?N |- _ =>
      let SOK := fresh "SOK" in
      pose proof (wr_at_store_ok segs m D N k w WR ltac:(lia) ltac:(lia)) as SOK;
      step;
      clear SOK;
      rewrite ?le1_zero, ?le4_zero, ?le8_zero;
      try change (Z_to_le_bytes 8 0) with (repeat b0 8);
      try change (Z_to_le_bytes 4 0) with (repeat b0 4);
      try change (Z_to_le_bytes 1 0) with (repeat b0 1);
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?a ?bs) _) =>
          (* [comment removed for export] *)
          replace (write_to_mem m a bs) with (write_to_mem m (wa (D + k)) bs)
            by (f_equal; first [reflexivity | addr_eq_tac | unfold wa; word_eq_tac]);
          lazymatch goal with
          | ZF : zfill m ?l, MU : munch ?W ?m0 m, WM : wmono segs ?m1 m |- _ =>
              let ZF' := fresh "ZF" in
              pose proof (zfill_store m l (D + k)%Z w ZF ltac:(lia) ltac:(lia)) as ZF'; clear ZF; rename ZF' into ZF;
              apply (wr_at_write segs m D N (wa (D + k)) bs) in WR;
              apply (munch_write W m0 m (D + k)%Z bs) in MU; [ | lia | rewrite repeat_length; lia | cbn [inside]; rewrite repeat_length; lia ];
              apply (wmono_write segs m1 m (wa (D + k)) bs) in WM;
              let m' := fresh "m" in
              remember (write_to_mem m (wa (D + k)) bs) as m' eqn:Heqm; clear Heqm; try clear m
          end
      end
  end.

Ltac memset_exit :=
  apply evt_done; unfold memset_post;
  do 7 eexists; split; [reflexivity|];
  lazymatch goal with
  | WR : wr_at _ _ _ _, ZF : zfill _ _, MU : munch _ _ _, WM : wmono _ _ _ |- _ =>
      split; [exact MU|]; split; [exact WM|];
      eapply u8arr_of_zfill; [exact WR | lia | exact ZF | intros ? ?; cbn [incov]; lia]
  end.

Lemma negw_land3_zero : forall x, (0 <= x < 2^64)%Z -> (x mod 8 = 0)%Z ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - x)))) 3 = 0%Z.
Proof.
  intros x Hx H8. rewrite Z_to_bv_unsigned. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  change (Z.of_N 32 - 1)%Z with 31%Z. change (2^31)%Z with 2147483648%Z. change (2^2)%Z with 4%Z.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma testbit_high_zero : forall n i, (0 <= n < 2^64)%Z -> (64 <= i)%Z -> Z.testbit n i = false.
Proof.
  intros n i Hn Hi. destruct (Z.eq_dec n 0) as [->|]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma land_clear_low2 : forall n, (0 <= n < 2^64)%Z -> Z.land n 18446744073709551612 = (n - n mod 4)%Z.
Proof.
  intros n Hn.
  transitivity (Z.ldiff n 3).
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec.
    change 3%Z with (Z.ones 2).
    destruct (Z.lt_ge_cases i 64).
    + replace 18446744073709551612%Z with (Z.lxor (Z.ones 64) (Z.ones 2)) by reflexivity.
      rewrite Z.lxor_spec, (Z.ones_spec_low 64) by lia.
      destruct (Z.lt_ge_cases i 2); [rewrite Z.ones_spec_low by lia | rewrite Z.ones_spec_high by lia]; reflexivity.
    + rewrite (testbit_high_zero n i) by lia. reflexivity.
  - pose proof (Z.land_ones n 2 ltac:(lia)) as L. change (Z.ones 2) with 3%Z in L.
    assert (D : Z.land (Z.ldiff n 3) (Z.land n 3) = 0%Z).
    { apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.ldiff_spec, Z.bits_0.
      destruct (Z.testbit n i), (Z.testbit 3 i); reflexivity. }
    assert (U : Z.lor (Z.ldiff n 3) (Z.land n 3) = n).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.land_spec, Z.ldiff_spec.
      destruct (Z.testbit n i), (Z.testbit 3 i); reflexivity. }
    rewrite <- Z.lxor_lor in U by exact D. rewrite <- Z.add_nocarry_lxor in U by exact D.
    change (2^2)%Z with 4%Z in L. lia.
Qed.

(* [comment removed for export] *)
Lemma land4_of_mod8 : forall d, (0 <= d)%Z -> (d mod 8 = 0)%Z -> Z.land d 4 = 0%Z.
Proof.
  intros d Hd H8. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i 2) as [->|Hne].
  - replace d with ((d / 8) * 2^3)%Z by lia. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit 4 i) with false; [apply andb_false_r|].
    symmetry. change 4%Z with (2^2)%Z. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (N4 : Z).
  Notation D := (bv_unsigned a0). Notation N := (bv_unsigned a2).
  Notation POST := (memset_post ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc N m).
  Hypothesis HN4a : (N - 3 <= N4 <= N)%Z.
  Hypothesis HN4b : (N4 mod 4 = 0)%Z.
  Hypothesis BD : (0 <= D /\ D + N <= 2^64)%Z.

  #[using="HN4a HN4b BD"] Lemma memset_loop : forall (k : nat) (P R : Z) (mq : word -> option byte) (cov : list (Z * Z)) (a5 a6 : word),
    (Z.to_nat R <= k)%nat ->
    wr_at PSEGS mq D N -> munch [(D, D + N)]%Z m mq -> wmono PSEGS m mq -> zfill mq cov ->
    (forall a, (D <= a < P)%Z -> incov cov a) ->
    (forall a, (D + N4 - 28 <= a < D + N)%Z -> incov cov a) ->
    (R = D + N4 - P)%Z -> (32 <= R)%Z -> (R mod 4 = 0)%Z -> (D <= P)%Z ->
    evt PSEGS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 31) (Z_to_bv 64 R) a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5e948) fc None mq (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (HN4a HN4b BD : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros P R mq cov a5 a6 Hk WR MU WM ZF COVlo COVhi HR R32 R4 DP; [lia|].
    zstore (P - D)%Z 8%nat. (* [comment removed for export] *)
    zstore (P - D + 8)%Z 8%nat.
    zstore (P - D + 16)%Z 8%nat.
    zstore (P - D + 24)%Z 8%nat.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc.
    - (* [comment removed for export] *)
      cond_cleanup Hc.
      replace (R + -32)%Z with (R - 32)%Z by lia.
      eapply (IH (P + 32)%Z (R - 32)%Z); try eassumption; try lia.
      all: try (Z.div_mod_to_equations; lia).
      + intros a Ha. cbn [incov]. destruct (Z.lt_ge_cases a P); [| lia]. do 4 right. apply COVlo. lia.
      + intros a Ha. cbn [incov]. do 4 right. apply COVhi. lia.
    - (* [comment removed for export] *)
      cond_cleanup Hc.
      step. (* [comment removed for export] *)
      apply evt_done; unfold memset_post.
      do 7 eexists; split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      eapply u8arr_of_zfill; [exact WR | lia | exact ZF |].
      intros a Ha. cbn [incov].
      destruct (Z.lt_ge_cases a P). { do 4 right. apply COVlo. lia. }
      destruct (Z.lt_ge_cases a (D + N4 - 28)). 2:{ do 4 right. apply COVhi. lia. }
      Z.div_mod_to_equations. lia.
  Qed.
End Loop.

Lemma memset_spec : memset_stmt.
Proof.
  unfold memset_stmt. intros until old. intros A1 DST LEN AL. subst a1.
  destruct DST as [BY WR].
  pose proof (bytes_at_bound _ _ _ _ BY) as Bd. rewrite LEN in *. clear BY.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m) as MU.
  pose proof (wmono_refl PSEGS m) as WM.
  pose proof (zfill_nil m) as ZF.
  step. (* [comment removed for export] *)
  if_cases Hn.
  { cond_cleanup Hn. step. memset_exit. }
  cond_cleanup Hn.
  zstore 0%Z 1%nat. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  zstore (bv_unsigned a2 - 1)%Z 1%nat. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases H3.
  { cond_cleanup H3. step. memset_exit. }
  cond_cleanup H3.
  zstore 1%Z 1%nat. zstore 2%Z 1%nat. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  zstore (bv_unsigned a2 - 3)%Z 1%nat. zstore (bv_unsigned a2 - 2)%Z 1%nat.
  step. (* [comment removed for export] *)
  if_cases H7.
  { cond_cleanup H7. step. memset_exit. }
  cond_cleanup H7.
  zstore 3%Z 1%nat.
  step. (* [comment removed for export] *)
  zstore (bv_unsigned a2 - 4)%Z 1%nat.
  step. (* [comment removed for export] *)
  if_cases H9.
  { cond_cleanup H9. step. memset_exit. }
  cond_cleanup H9.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (negw_land3_zero (bv_unsigned a0)) by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit (bv_unsigned a2 - 0)) by lia. rewrite Z.sub_0_r.
  rewrite (land_clear_low2 (bv_unsigned a2)) by lia.
  remember (bv_unsigned a2 - bv_unsigned a2 mod 4)%Z as N4 eqn:HN4.
  assert (HN4r : (bv_unsigned a2 - 3 <= N4 <= bv_unsigned a2)%Z /\ (N4 mod 4 = 0)%Z).
  { subst N4. Z.div_mod_to_equations. lia. }
  clear HN4. destruct HN4r as [HN4a HN4b].
  zstore 0%Z 4%nat. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  zstore (N4 - 4)%Z 4%nat. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases H9b.
  { cond_cleanup H9b. step. memset_exit. }
  cond_cleanup H9b.
  zstore 4%Z 4%nat. zstore 8%Z 4%nat.
  step. (* [comment removed for export] *)
  zstore (N4 - 12)%Z 4%nat. zstore (N4 - 8)%Z 4%nat.
  step. (* [comment removed for export] *)
  if_cases H25.
  { cond_cleanup H25. step. memset_exit. }
  cond_cleanup H25.
  zstore 12%Z 4%nat. zstore 16%Z 4%nat. zstore 20%Z 4%nat. zstore 24%Z 4%nat.
  step. (* [comment removed for export] *)
  rewrite (land4_of_mod8 (bv_unsigned a0)) by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  zstore (N4 - 28)%Z 4%nat. zstore (N4 - 24)%Z 4%nat. zstore (N4 - 20)%Z 4%nat. zstore (N4 - 16)%Z 4%nat.
  step. (* [comment removed for export] *)
  if_cases H32.
  { cond_cleanup H32. step. memset_exit. }
  cond_cleanup H32.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite (unsigned_lit N4) by lia.
  eapply (memset_loop ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m N4
            ltac:(lia) HN4b ltac:(lia) (Z.to_nat (N4 - 24)) (bv_unsigned a0 + 24)%Z (N4 - 24)%Z);
    try eassumption; try lia.
  all: try (intros a Ha; cbn [incov]; lia).
  all: Z.div_mod_to_equations; lia.
Qed.
