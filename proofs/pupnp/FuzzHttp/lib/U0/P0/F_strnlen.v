(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_memchr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
Import ListNotations.
Open Scope bv_scope.

Definition strnlen_entry := 0x24b98%Z.

Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) buf.

Lemma strnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  evt rsegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24b98) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST BUF OK MI LO SEP A0.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 9 zstep.
  call memchr_spec.
  1:{ exact BUF. }
  1:{ rewrite unsigned_lit by lia. exact OK. }
  1:{ assumption. }
  rewrite unsigned_lit by lia. change (0 mod 256)%Z with 0%Z.
  unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
    zstep. if_cases K; zify_cond K. { exfalso. lia. }
    do 7 zstep.
    replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (strnlen_res (bv_unsigned a1) buf)
      by (unfold strnlen_res; rewrite FB; lia).
    release_frame FR ST (bv_unsigned sp). finish.
  - zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    do 6 zstep.
    lazymatch goal with |- evt _ ?Q _ => set (P := Q) end.
    replace a1 with (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
      by (unfold strnlen_res; rewrite FB; apply Z_to_bv_bv_unsigned).
    release_frame FR ST (bv_unsigned sp). finish.
Qed.
