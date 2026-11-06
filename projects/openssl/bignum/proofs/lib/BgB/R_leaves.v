(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr Walk. 
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_small R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition rss_entry : Z := 0x1ca85c.
Definition can_poison_entry : Z := 0x1bf4d0.
Definition stack_top_entry : Z := 0x1c821c.
Definition stack_bottom_entry : Z := 0x1c8274.
Definition istrnlen_entry : Z := 0x1d01d8.

Lemma rss_limit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells bgbsegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  mem_inv bgbsegs m ->
  evt bgbsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 rss_entry) fc None m (seg_rom bgbsegs)).
Proof.
  intros until m. intros CI MI. unfold g_rss_limit_exceeded, rss_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  do 4 zstep.
  finish.
Qed.

Lemma can_poison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells bgbsegs m g_can_poison_memory [C1 (Z_to_bv 8 1)] ->
  mem_inv bgbsegs m ->
  evt bgbsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 can_poison_entry) fc None m (seg_rom bgbsegs)).
Proof.
  intros until m. intros CI MI. unfold g_can_poison_memory, can_poison_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  do 5 zstep.
  finish.
Qed.

Definition stack_cells (T top bottom : Z) (m : mem) : Prop :=
  rw_cells bgbsegs m (T + off_t_stack_top) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bottom)]
  /\ rw_cells bgbsegs m (T + off_t_stack_switching) [C1 (Z_to_bv 8 0)].

Lemma stack_top_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (T top bottom : Z),
  stack_cells T top bottom m -> (0 <= bottom < top)%Z -> (top < 2^64)%Z ->
  mem_inv bgbsegs m ->
  evt bgbsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc top m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 stack_top_entry) fc None m (seg_rom bgbsegs)).
Proof.
  intros until bottom. intros [C1 C2] Hb Ht MI. unfold off_t_stack_top, off_t_stack_switching, stack_top_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  do 3 zstep. ifT.
  do 6 zstep.
  rewrite (proj2 (Z.ltb_lt bottom top)) by lia. change (Z.b2z true) with 1%Z.
  change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia.
  finish.
Qed.

Lemma stack_bottom_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (T top bottom : Z),
  stack_cells T top bottom m -> (0 <= bottom < top)%Z -> (top < 2^64)%Z ->
  mem_inv bgbsegs m ->
  evt bgbsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bottom m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 stack_bottom_entry) fc None m (seg_rom bgbsegs)).
Proof.
  intros until bottom. intros [C1 C2] Hb Ht MI. unfold off_t_stack_top, off_t_stack_switching, stack_bottom_entry in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
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

Section ISTRNLEN.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (s : Z) (N : nat) (buf : list byte).
Hypothesis BA : bytes_at bgbsegs m s buf.
Hypothesis HOK : istrnlen_ok N buf.
Hypothesis HN : (1 <= N)%nat.
Hypothesis HNr : (Z.of_nat N < 2^64)%Z.
Hypothesis MI : mem_inv bgbsegs m.
Hypothesis MU : munch [] m m.
Hypothesis WM : wmono bgbsegs m m.

Definition istrnlen_Q := leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (istrnlen_res buf N)) m.

End ISTRNLEN.

