(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit M_memchr.
Import ListNotations.
Open Scope Z_scope.

Definition memchr_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A c n : Z) (buf : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (memchr_res A c n buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' A buf.

Lemma memchr_specZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A c n : Z) (buf : list byte),
  bytes_at asegs m A buf -> memchr_ok A c n buf -> mem_inv asegs m ->
  0 <= A < 2^64 -> 0 <= c < 256 -> 0 <= n < 2^64 ->
  evt asegs (memchr_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz c) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xa1d1c) fc None m (seg_rom asegs)).
Proof.
  intros until buf. intros BUF OK MI HA Hc Hn.
  assert (Ea : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (Ec : bv_unsigned (Z_to_bv 64 c) mod 256 = c) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memchr_spec; rewrite ?Ea, ?Ec, ?En; eauto. }
  intros ms' Q. unfold memchr_post in Q. rewrite !Ea, !Ec, !En in Q. exact Q.
Qed.
