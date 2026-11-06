(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit M_memcmp.
Import ListNotations.
Open Scope Z_scope.

Definition memcmp_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A B : Z) (ls rs : list byte) (v : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' A ls /\ bytes_at asegs m' B rs.

Lemma memcmp_specZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A B n : Z) (ls rs : list byte) (v : Z),
  bytes_at asegs m A ls -> bytes_at asegs m B rs -> memcmp_model ls rs (Z.to_nat n) = Some v -> mem_inv asegs m ->
  0 <= A < 2^64 -> 0 <= B < 2^64 -> 0 <= n < 2^64 ->
  evt asegs (memcmp_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A B ls rs v m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz B) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xa2a4c) fc None m (seg_rom asegs)).
Proof.
  intros until v. intros LS RS HM MI HA HB Hn.
  assert (Ea : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (Eb : bv_unsigned (Z_to_bv 64 B) = B) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memcmp_spec with (ls := ls) (rs := rs) (v := v); rewrite ?Ea, ?Eb, ?En; eauto. }
  intros ms' Q. unfold memcmp_post in Q. rewrite !Ea, !Eb in Q. exact Q.
Qed.
