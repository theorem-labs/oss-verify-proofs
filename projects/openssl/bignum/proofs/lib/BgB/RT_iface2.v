(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_stack_malloc_g (k : nat) : Z :=
  match k with 0%nat => 0x1a1350 | 1%nat => 0x1a14c4 | 2%nat => 0x1a1654 | 3%nat => 0x1a17f0 | _ => 0x1a199c end.

Lemma e_stack_malloc_g_024 : forall k, (k = 0 \/ k = 2 \/ k = 4)%nat -> e_stack_malloc_g k = e_stack_malloc k.
Proof. intros k [->|[->| ->]]; reflexivity. Qed.

Section Contracts2.
Variable RT : rt_sig.

Definition stack_malloc_contract_g (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xbd6df0 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bgbsegs m -> call_ok RT Σ m sp lo ->
  cps bgbsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_stack_malloc_g k) m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at bgbsegs m' f (fs_size k - 8) /\ wr_at bgbsegs m' (shad f) (fs_size k / 8)) c
       /\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP).

Lemma stack_malloc_g_of : forall k, (k = 0 \/ k = 2 \/ k = 4)%nat -> stack_malloc_contract RT k -> stack_malloc_contract_g k.
Proof.
  intros k Hk H. unfold stack_malloc_contract_g. intros. rewrite (e_stack_malloc_g_024 k Hk). eapply H; eassumption.
Qed.

Record rt_contracts2 : Prop := mkRTC2 {
  rc2_stack_malloc : forall k, (k <= 4)%nat -> stack_malloc_contract_g k
}.

Lemma rt_contracts2_of : rt_contracts RT -> stack_malloc_contract_g 1 -> stack_malloc_contract_g 3 -> rt_contracts2.
Proof.
  intros RC H1 H3. constructor. intros k Hk.
  destruct k as [|[|[|[|[|k]]]]]; [| exact H1 | | exact H3 | | lia].
  - apply stack_malloc_g_of; [left; reflexivity | exact (rc_stack_malloc_0 RT RC)].
  - apply stack_malloc_g_of; [right; left; reflexivity | exact (rc_stack_malloc_2 RT RC)].
  - apply stack_malloc_g_of; [right; right; reflexivity | exact (rc_stack_malloc_4 RT RC)].
Qed.

End Contracts2.
