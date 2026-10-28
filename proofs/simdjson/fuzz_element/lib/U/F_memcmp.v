(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition memcmp_entry : Z := 0xd06b8.
Definition bcmp_entry : Z := 0xd05e8.

Lemma ro_C1_of_bytes : forall m x b, bytes_at usegs m x [b] -> ro_cells usegs m x [C1 b].
Proof. intros m x b H. split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. exact H. Qed.

Lemma bytes_at_nth : forall (m : mem) a (bs : list byte) j, bytes_at usegs m a bs -> 0 <= j < Z.of_nat (length bs) ->
  bytes_at usegs m (a + j) [nth (Z.to_nat j) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs j (H0 & H1 & H) Hj. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
  specialize (H (Z.to_nat j) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H. apply nth_error_nth'. lia.
Qed.

Definition memcmp_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (bp bq : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (r a1' a2' a3' a4' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs)
    /\ (r = Z_to_bv 64 0 <-> bp = bq).

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : mem) (p q : Z) (bp bq : list byte).
Notation n := (Z.of_nat (length bp)).
Notation BP j := (nth (Z.to_nat j) bp (Z_to_bv 8 0)).
Notation BQ j := (nth (Z.to_nat j) bq (Z_to_bv 8 0)).
Hypothesis LEN : length bq = length bp.
Hypothesis P0 : 0 <= p.
Hypothesis Q0 : 0 <= q.
Hypothesis PH : p + n < 2 ^ 63.
Hypothesis QH : q + n < 2 ^ 63.
Hypothesis SP : bytes_at usegs m p bp.
Hypothesis SQ : bytes_at usegs m q bq.
Hypothesis MI : mem_inv usegs m.
Notation POST := (memcmp_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc bp bq m).
Notation ST pc x10 x11 x12 x13 x14 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

Lemma nth_ext_Z : (forall j, 0 <= j < n -> BP j = BQ j) -> bp = bq.
Proof using LEN.
  intros H. apply (nth_ext bp bq (Z_to_bv 8 0) (Z_to_bv 8 0)); [symmetry; exact LEN|].
  intros k Hk. specialize (H (Z.of_nat k) ltac:(lia)). rewrite Nat2Z.id in H. exact H.
Qed.

Lemma memcmp_loop : forall (k : nat) (i : Z) x13 x14,
  Z.of_nat (S k) = n - i -> 0 <= i -> (forall j, 0 <= j < i -> BP j = BQ j) ->
  evt usegs POST (ST 0xd06bc (Z_to_bv 64 (p + i)) (Z_to_bv 64 (q + i)) (Z_to_bv 64 (n - i)) x13 x14).
Proof using LEN P0 Q0 PH QH SP SQ MI.
  induction k as [|k IH]; intros i x13 x14 Hk Hi Hpre.
  all: pose proof (munch_refl [] m) as MU; pose proof (wmono_refl usegs m) as WM.
  all: pose proof (ro_C1_of_bytes m (p + i) _ (bytes_at_nth m p bp i SP ltac:(lia))) as CP0.
  all: pose proof (ro_C1_of_bytes m (q + i) _ (bytes_at_nth m q bq i SQ ltac:(rewrite LEN; lia))) as CQ0.
  all: assert (EU1 : bv_unsigned (Z_to_bv 64 (p + i)) = p + i) by (apply unsigned_lit; lia).
  all: assert (EU2 : bv_unsigned (Z_to_bv 64 (q + i)) = q + i) by (apply unsigned_lit; lia).
  all: assert (EU3 : bv_unsigned (Z_to_bv 64 (n - i)) = n - i) by (apply unsigned_lit; lia).
  all: set (cp := p + i) in *; set (cq := q + i) in *.
  all: zstep; zstep; zstep.
  all: assert (RB1 : 0 <= bv_unsigned (BP i) < 256) by (pose proof (bv_unsigned_in_range 8 (BP i)) as X; unfold bv_modulus in X; cbn in X; lia).
  all: assert (RB2 : 0 <= bv_unsigned (BQ i) < 256) by (pose proof (bv_unsigned_in_range 8 (BQ i)) as X; unfold bv_modulus in X; cbn in X; lia).
  all: rewrite ZBridge.bv_eqb_Z, !unsigned_lit by lia.
  all: destruct (Z.eqb_spec (bv_unsigned (BP i)) (bv_unsigned (BQ i))) as [E|NE]; cbv [negb].
  -
    zstep. zstep. zstep. zstep.
    replace (n - i + -1) with 0 by lia. if_false.
    zstep. zstep.
    apply evt_done. unfold memcmp_post. do 5 eexists. split; [reflexivity|].
    split; [intros _|reflexivity]. apply nth_ext_Z. intros j Hj.
    destruct (Z.eq_dec j i) as [->|NEj]; [apply bv_eq; exact E | apply Hpre; lia].
  -
    zstep. zstep.
    apply evt_done. unfold memcmp_post. do 5 eexists. split; [reflexivity|].
    split; [intros R0 | intros EQ; exfalso; apply NE; rewrite EQ; reflexivity].
    exfalso. apply NE.
    assert (X : bv_unsigned (Z_to_bv 64 (bv_unsigned (BP i) - bv_unsigned (BQ i))) = 0) by (rewrite R0; reflexivity).
    rewrite Z_to_bv_unsigned in X. unfold bv_wrap, bv_modulus in X. cbn [Z.of_N] in X.
    destruct (Z_lt_le_dec (bv_unsigned (BP i)) (bv_unsigned (BQ i))) as [L|G].
    + replace ((bv_unsigned (BP i) - bv_unsigned (BQ i)) mod 2 ^ 64) with (bv_unsigned (BP i) - bv_unsigned (BQ i) + 2 ^ 64) in X
        by (symmetry; rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia; apply Z.mod_small; lia). lia.
    + rewrite Z.mod_small in X by lia. lia.
  -
    zstep. zstep. zstep. zstep.
    assert (EU4 : bv_unsigned (Z_to_bv 64 (n - i + -1)) = n - i + -1) by (apply unsigned_lit; lia).
    if_true.
    subst cp cq.
    replace (p + i + 1) with (p + (i + 1)) by lia. replace (q + i + 1) with (q + (i + 1)) by lia. replace (n - i + -1) with (n - (i + 1)) by lia.
    apply (IH (i + 1)); [lia | lia|].
    intros j Hj. destruct (Z.eq_dec j i) as [->|NEj]; [apply bv_eq; exact E | apply Hpre; lia].
  - zstep. zstep.
    apply evt_done. unfold memcmp_post. do 5 eexists. split; [reflexivity|].
    split; [intros R0 | intros EQ; exfalso; apply NE; rewrite EQ; reflexivity].
    exfalso. apply NE.
    assert (X : bv_unsigned (Z_to_bv 64 (bv_unsigned (BP i) - bv_unsigned (BQ i))) = 0) by (rewrite R0; reflexivity).
    rewrite Z_to_bv_unsigned in X. unfold bv_wrap, bv_modulus in X. cbn [Z.of_N] in X.
    destruct (Z_lt_le_dec (bv_unsigned (BP i)) (bv_unsigned (BQ i))) as [L|G].
    + replace ((bv_unsigned (BP i) - bv_unsigned (BQ i)) mod 2 ^ 64) with (bv_unsigned (BP i) - bv_unsigned (BQ i) + 2 ^ 64) in X
        by (symmetry; rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia; apply Z.mod_small; lia). lia.
    + rewrite Z.mod_small in X by lia. lia.
Qed.

Lemma memcmp_spec_s : forall x13 x14, evt usegs POST (ST 0xd06b8 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 n) x13 x14).
Proof using LEN P0 Q0 PH QH SP SQ MI.
  intros x13 x14.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (EU3 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  zstep. if_cases K; zify_cond K.
  -
    zstep. zstep.
    apply evt_done. unfold memcmp_post. do 5 eexists. split; [reflexivity|].
    split; [intros _ | reflexivity].
    assert (E0 : n = 0) by lia. destruct bp; [|cbn [length] in E0; lia]. destruct bq; [reflexivity | cbn [length] in LEN; lia].
  - pose proof (memcmp_loop (Z.to_nat (n - 1)) 0 x13 x14 ltac:(lia) ltac:(lia) ltac:(intros j Hj; lia)) as X.
    rewrite !Z.add_0_r, Z.sub_0_r in X. exact X.
Qed.

End Proofs.

Lemma memcmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p q : Z) (bp bq : list byte),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 (Z.of_nat (length bp)) -> length bq = length bp ->
  0 <= p -> 0 <= q -> p + Z.of_nat (length bp) < 2 ^ 63 -> q + Z.of_nat (length bp) < 2 ^ 63 ->
  bytes_at usegs m p bp -> bytes_at usegs m q bq -> mem_inv usegs m ->
  evt usegs (memcmp_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc bp bq m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memcmp_entry) fc None m (seg_rom usegs)).
Proof.
  intros until bq. intros -> -> -> LEN P0 Q0 PH QH SP SQ MI.
  exact (memcmp_spec_s ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq LEN P0 Q0 PH QH SP SQ MI a3 a4).
Qed.

Lemma bcmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p q : Z) (bp bq : list byte),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 (Z.of_nat (length bp)) -> length bq = length bp ->
  0 <= p -> 0 <= q -> p + Z.of_nat (length bp) < 2 ^ 63 -> q + Z.of_nat (length bp) < 2 ^ 63 ->
  bytes_at usegs m p bp -> bytes_at usegs m q bq -> mem_inv usegs m ->
  evt usegs (memcmp_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc bp bq m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 bcmp_entry) fc None m (seg_rom usegs)).
Proof.
  intros until bq. intros -> -> -> LEN P0 Q0 PH QH SP SQ MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep.
  exact (memcmp_spec_s ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq LEN P0 Q0 PH QH SP SQ MI a3 a4).
Qed.
