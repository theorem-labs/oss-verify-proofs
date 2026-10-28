(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require KStep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_am_A F_am_K F_am_C F_am_F F_am_G.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.

Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition brk_regs (a0 : word) : _ :=
  mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition brk_res (cur req : Z) (a : brk_ans) : Z := match a with BrkGrown => req | BrkSame => cur end.
Definition brk_mem (cur req : Z) (a : brk_ans) : word -> option byte :=
  match a with
  | BrkGrown => match brk_new_pages cur req with Some (lo, n) => apply_zeros m [(wa lo, Z_to_bv 64 n)] | None => m end
  | BrkSame => m
  end.
End BRKNODES.

Lemma land_neg_aligned cur : 0 < cur < 2^64 -> cur mod 4096 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 (0 + - cur))) 4095 = 0.
Proof.
  intros H AL. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  replace ((0 + - cur) mod 2^64) with ((2^52 - cur / 4096) * 4096) by (Z.div_mod_to_equations; lia).
  change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. apply Z.mod_mul. lia.
Qed.

Lemma brk_new_pages_aligned cur n : 0 <= cur -> 0 < n -> cur mod 4096 = 0 -> n mod 4096 = 0 ->
  brk_new_pages cur (cur + n) = Some (cur, n).
Proof.
  intros C0 N0 CA NA. unfold brk_new_pages. rewrite <- !KStep.round_up_pg_eq.
  rewrite !KStep.round_up_pg_aligned by (auto; rewrite Z.add_mod, CA, NA by lia; reflexivity).
  replace (cur <? cur + n) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. f_equal. lia.
Qed.

Definition fx_rel (A : Z) (a : fixed_ans) (r : word) (u : bool) : Prop :=
  match a with
  | FxKept e => errno_of r = Some e /\ u = false
  | FxDone => r = Z_to_bv 64 A /\ u = true
  | FxLost e => errno_of r = Some e /\ u = true
  end.
Lemma dec_mmap_fixed_shape A L rsp a : dec_mmap_fixed A L rsp = Some a -> exists r u, fx_rel A a r u /\ Nodes.strip rsp = fixed_shape A L r u.
Proof.
  unfold dec_mmap_fixed, fixed_shape. destruct rsp as [r ws zs us cs ci].
  destruct ws; [| discriminate]. destruct zs; [| discriminate]. destruct us as [|[ua un] us].
  - destruct cs; [| discriminate]. rewrite strip_mk.
    destruct (errno_of r) eqn:E; [| discriminate]. intros H; inversion H; subst. exists r, false. cbn. rewrite E. auto.
  - destruct us; [| discriminate]. destruct cs; [| discriminate]. rewrite strip_mk.
    destruct (bv_eqb ua (Z_to_bv 64 A) && bv_eqb un (Z_to_bv 64 (mmap_len L))) eqn:E; [| discriminate].
    apply andb_prop in E. destruct E as [E1 E2]. apply Fs.bv_eqb_eq in E1. apply Fs.bv_eqb_eq in E2. subst ua un.
    destruct (errno_of r) eqn:E.
    + intros H; inversion H; subst. exists r, true. cbn. rewrite E. auto.
    + destruct (bv_eqb r (Z_to_bv 64 A)) eqn:E3; [| discriminate]. apply Fs.bv_eqb_eq in E3. intros H; inversion H; subst. exists (Z_to_bv 64 A), true. cbn. auto.
Qed.