(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require F_ctype.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs IcptA0.
Import ListNotations.
Open Scope Z_scope.

Definition ctype_post_A (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (res : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

Lemma isalnum_spec_A : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned a0 < 256 ->
  mem_inv asegs m ->
  evt asegs (ctype_post_A ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.b2z (is_alnum (bv_unsigned a0))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 A0_isalnum) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Hc MI. unfold A0_isalnum.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a0) as R0.
  do 6 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] =>
    change (Z_to_bv 64 (Z.lor x y)) with (Z_to_bv 64 (P0.F_ctype.isalnum_expr (bv_unsigned a0))) end.
  rewrite (P0.F_ctype.isalnum_eval (bv_unsigned a0)) by lia.
  zstep. finish.
Qed.

Lemma isxdigit_spec_A : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned a0 < 256 ->
  mem_inv asegs m ->
  evt asegs (ctype_post_A ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.b2z (is_xdigit (bv_unsigned a0))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 A0_isxdigit) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Hc MI. unfold A0_isxdigit.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a0) as R0.
  do 6 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] =>
    change (Z_to_bv 64 (Z.lor x y)) with (Z_to_bv 64 (P0.F_ctype.isxdigit_expr (bv_unsigned a0))) end.
  rewrite (P0.F_ctype.isxdigit_eval (bv_unsigned a0)) by lia.
  zstep. finish.
Qed.
