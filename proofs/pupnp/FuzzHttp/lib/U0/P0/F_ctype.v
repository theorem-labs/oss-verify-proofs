(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Definition isalnum_entry := 0x17548%Z.
Definition isxdigit_entry := 0x17564%Z.
Definition tolower_entry := 0x17580%Z.

Definition ctype_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (res : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Ltac pg := match goal with |- ?G => idtac G end.

Definition isalnum_expr (c : Z) : Z :=
  Z.lor (Z.b2z (bv_swrap 32 (c + -48) mod 18446744073709551616 <? 10))
        (Z.b2z (bv_swrap 32 (Z.lor c 32 + -97) mod 18446744073709551616 <? 26)).
Definition isxdigit_expr (c : Z) : Z :=
  Z.lor (Z.b2z (bv_swrap 32 (c + -48) mod 18446744073709551616 <? 10))
        (Z.b2z (bv_swrap 32 (Z.lor c 32 + -97) mod 18446744073709551616 <? 6)).
Definition tolower_expr (c : Z) : Z :=
  Z.lor c (Z.shiftl (Z.b2z (bv_swrap 32 (c + -65) mod 18446744073709551616 <? 26)) 5 mod 18446744073709551616).

Lemma isalnum_eval : forall c, 0 <= c < 256 -> Z_to_bv 64 (isalnum_expr c) = Z_to_bv 64 (Z.b2z (is_alnum c)).
Proof.
  intros c Hc. apply word_eq_of_eqb.
  apply (brute256_ok (fun c => isalnum_expr c mod 2^64 =? Z.b2z (is_alnum c) mod 2^64)); [vm_compute; reflexivity| exact Hc].
Qed.
Lemma isxdigit_eval : forall c, 0 <= c < 256 -> Z_to_bv 64 (isxdigit_expr c) = Z_to_bv 64 (Z.b2z (is_xdigit c)).
Proof.
  intros c Hc. apply word_eq_of_eqb.
  apply (brute256_ok (fun c => isxdigit_expr c mod 2^64 =? Z.b2z (is_xdigit c) mod 2^64)); [vm_compute; reflexivity| exact Hc].
Qed.
Lemma tolower_eval : forall c, 0 <= c < 256 -> Z_to_bv 64 (tolower_expr c) = Z_to_bv 64 (to_lower c).
Proof.
  intros c Hc. apply word_eq_of_eqb.
  apply (brute256_ok (fun c => tolower_expr c mod 2^64 =? to_lower c mod 2^64)); [vm_compute; reflexivity| exact Hc].
Qed.

Lemma isalnum_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  (bv_unsigned a0 < 256)%Z ->
  mem_inv rsegs m ->
  evt rsegs (ctype_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.b2z (is_alnum (bv_unsigned a0))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17548) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros Hc MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a0) as R0.
  do 6 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] =>
    change (Z_to_bv 64 (Z.lor x y)) with (Z_to_bv 64 (isalnum_expr (bv_unsigned a0))) end.
  rewrite (isalnum_eval (bv_unsigned a0)) by lia.
  zstep. finish.
Qed.

Lemma isxdigit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  (bv_unsigned a0 < 256)%Z ->
  mem_inv rsegs m ->
  evt rsegs (ctype_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.b2z (is_xdigit (bv_unsigned a0))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17564) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros Hc MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a0) as R0.
  do 6 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] =>
    change (Z_to_bv 64 (Z.lor x y)) with (Z_to_bv 64 (isxdigit_expr (bv_unsigned a0))) end.
  rewrite (isxdigit_eval (bv_unsigned a0)) by lia.
  zstep. finish.
Qed.

Lemma tolower_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  (bv_unsigned a0 < 256)%Z ->
  mem_inv rsegs m ->
  evt rsegs (ctype_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (to_lower (bv_unsigned a0)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17580) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros Hc MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a0) as R0.
  do 4 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] =>
    change (Z_to_bv 64 (Z.lor x y)) with (Z_to_bv 64 (tolower_expr (bv_unsigned a0))) end.
  rewrite (tolower_eval (bv_unsigned a0)) by lia.
  zstep. finish.
Qed.
