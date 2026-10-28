(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition rss_entry : Z := 0x8cb64.
Definition can_poison_entry : Z := 0x81d2c.
Definition stack_top_entry : Z := 0x8a770.
Definition stack_bottom_entry : Z := 0x8a7c8.
Definition istrnlen_entry : Z := 0x924e0.

Lemma rss_limit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells bsegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 rss_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros CI MI. unfold g_rss_limit_exceeded, rss_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 4 zstep.
  finish.
Qed.

Lemma can_poison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells bsegs m g_can_poison_memory [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 can_poison_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros CI MI. unfold g_can_poison_memory, can_poison_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 5 zstep.
  finish.
Qed.

Definition stack_cells (T top bottom : Z) (m : mem) : Prop :=
  rw_cells bsegs m (T + off_t_stack_top) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bottom)]
  /\ rw_cells bsegs m (T + off_t_stack_switching) [C1 (Z_to_bv 8 0)].

Lemma stack_top_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (T top bottom : Z),
  stack_cells T top bottom m -> (0 <= bottom < top)%Z -> (top < 2^64)%Z ->
  mem_inv bsegs m ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc top m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 stack_top_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until bottom. intros [C1 C2] Hb Ht MI. unfold off_t_stack_top, off_t_stack_switching, stack_top_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 3 zstep. ifT.
  do 6 zstep.
  rewrite (proj2 (Z.ltb_lt bottom top)) by lia. change (Z.b2z true) with 1%Z.
  change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia.
  finish.
Qed.

Lemma stack_bottom_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (T top bottom : Z),
  stack_cells T top bottom m -> (0 <= bottom < top)%Z -> (top < 2^64)%Z ->
  mem_inv bsegs m ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bottom m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 stack_bottom_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until bottom. intros [C1 C2] Hb Ht MI. unfold off_t_stack_top, off_t_stack_switching, stack_bottom_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 3 zstep. ifT.
  do 6 zstep.
  rewrite (proj2 (Z.ltb_lt bottom top)) by lia. change (Z.b2z true) with 1%Z.
  change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia.
  finish.
Qed.

Fixpoint istrnlen_res (buf : list byte) (n : nat) {struct n} : nat :=
  match n, buf with
  | O, _ => O
  | S _, [] => O
  | S n', b :: buf' => if Z.eqb (bv_unsigned b) 0 then O else S (istrnlen_res buf' n')
  end.

Definition istrnlen_ok (n : nat) (buf : list byte) : Prop := (n <= length buf)%nat \/ In z8 buf.

Lemma istrnlen_le : forall buf n, (istrnlen_res buf n <= n)%nat.
Proof.
  intros buf n. revert buf. induction n as [|n IH]; intros [|b buf]; cbn; try lia.
  destruct (Z.eqb (bv_unsigned b) 0); [lia| specialize (IH buf); lia].
Qed.

Lemma istrnlen_lt : forall buf n i, (i < istrnlen_res buf n)%nat -> exists b, nth_error buf i = Some b /\ bv_unsigned b <> 0%Z.
Proof.
  intros buf n. revert buf. induction n as [|n IH]; intros [|b buf] i Hi; cbn in Hi; try lia.
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E]; [lia|].
  destruct i as [|i]; [exists b; split; [reflexivity| exact E]|].
  cbn [nth_error]. apply (IH buf i). lia.
Qed.

Lemma istrnlen_at : forall buf n, (istrnlen_res buf n < n)%nat -> istrnlen_ok n buf ->
  exists b, nth_error buf (istrnlen_res buf n) = Some b /\ bv_unsigned b = 0%Z.
Proof.
  intros buf n. revert buf. induction n as [|n IH]; intros [|b buf] Hr Hok; cbn in Hr |- *; try lia.
  - destruct Hok as [H|H]; cbn in H; [lia| contradiction].
  - destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E]; [exists b; split; [reflexivity| exact E]|].
    cbn [nth_error]. apply IH; [lia|].
    destruct Hok as [H|H]; [left; cbn in H; lia|].
    destruct H as [H|H]; [subst b; exfalso; apply E; reflexivity| right; exact H].
Qed.

Lemma read1 : forall (m : mem) s buf (i : nat) b, bytes_at bsegs m s buf -> nth_error buf i = Some b ->
  ov_read_bytes bsegs m (Z_to_bv 64 (s + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m s buf i b H E. assert (Hi : (i < length buf)%nat) by (apply nth_error_Some; congruence).
  pose proof (bytes_at_ov_read bsegs m s buf i 1 H ltac:(lia)) as R. unfold wa in R. rewrite R. f_equal.
  clear R H. revert buf E Hi. induction i as [|i IH]; intros [|x buf] E Hi; cbn in *; try discriminate; try lia.
  - injection E as ->. reflexivity.
  - apply IH; [exact E| lia].
Qed.

Section ISTRNLEN.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (s : Z) (N : nat) (buf : list byte).
Hypothesis BA : bytes_at bsegs m s buf.
Hypothesis HOK : istrnlen_ok N buf.
Hypothesis HN : (1 <= N)%nat.
Hypothesis HNr : (Z.of_nat N < 2^64)%Z.
Hypothesis MI : mem_inv bsegs m.
Hypothesis MU : munch [] m m.
Hypothesis WM : wmono bsegs m m.

Definition istrnlen_Q := leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (istrnlen_res buf N)) m.

Lemma istrnlen_loop : forall (k i : nat) a3,
  (i + k = N)%nat -> (1 <= k)%nat -> (i <= istrnlen_res buf N)%nat ->
  evt bsegs istrnlen_Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (Z.of_nat N)) (Z_to_bv 64 s) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x924ec) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros i a3 Hk H1 Hi; [lia|].
  pose proof (istrnlen_le buf N) as HLE.
  pose proof (bytes_at_bound bsegs m s buf BA) as BB.
  destruct (Nat.eq_dec i (istrnlen_res buf N)) as [Ei|Ei].
  -
    destruct (istrnlen_at buf N ltac:(lia) HOK) as (b & Hb & B0).
    rewrite <- Ei in Hb.
    assert (Hil : (i < length buf)%nat) by (apply nth_error_Some; congruence).
    pose proof (read1 m s buf i b BA Hb) as RD.
    assert (Eb : b = Z_to_bv 8 0) by (apply bv_eq; rewrite B0; reflexivity). subst b.
    replace (s + Z.of_nat i)%Z with (Z.of_nat i + s)%Z in RD by lia.
    do 2 zstep. clear RD.
    zstep. ifT.
    zstep. unfold istrnlen_Q. rewrite <- Ei. finish.
  - destruct (istrnlen_lt buf N i ltac:(lia)) as (b & Hb & B0).
    assert (Hil : (i < length buf)%nat) by (apply nth_error_Some; congruence).
    pose proof (read1 m s buf i b BA Hb) as RD.
    replace (s + Z.of_nat i)%Z with (Z.of_nat i + s)%Z in RD by lia.
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn [Z.of_N] in Rb.
    do 2 zstep. clear RD.
    zstep. ifF.
    zstep. zstep.
    destruct k as [|k].
    + ifF. zstep. zstep.
      unfold istrnlen_Q. replace (istrnlen_res buf N) with N by lia. finish.
    + ifT. replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
      eapply (IH (S i)); lia.
Qed.
End ISTRNLEN.

Lemma istrnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s n : Z) (buf : list byte),
  bytes_at bsegs m s buf -> (0 <= n < 2^64)%Z -> istrnlen_ok (Z.to_nat n) buf ->
  mem_inv bsegs m ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (istrnlen_res buf (Z.to_nat n))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 istrnlen_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until buf. intros BA Hn HOK MI. unfold istrnlen_entry.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bytes_at_bound bsegs m s buf BA) as BB.
  zstep.
  destruct (Z.eq_dec n 0) as [N0|N0].
  - subst n. ifT. do 2 zstep. change (Z.of_nat (istrnlen_res buf (Z.to_nat 0))) with 0%Z. finish.
  - ifF. do 2 zstep.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat 0)) by reflexivity.
    replace (Z_to_bv 64 n) with (Z_to_bv 64 (Z.of_nat (Z.to_nat n))) by (f_equal; lia).
    eapply istrnlen_loop with (N := Z.to_nat n) (k := Z.to_nat n) (i := 0%nat); try eassumption; lia.
Qed.
