(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Export MM_syscalls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require KStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_am_A F_am_K F_am_C F_am_F F_am_G.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte).
End BRKNODES.
#[using="Type"] Lemma brk_new_pages_aligned cur n : 0 <= cur -> 0 < n -> cur mod 4096 = 0 -> n mod 4096 = 0 ->
brk_new_pages cur (cur + n) = Some (cur, n).
Proof.
intros C0 N0 CA NA. unfold brk_new_pages. rewrite <- !KStep.round_up_pg_eq.
Local Ltac2 Set LiaHints.tbl := fun () => "0030=18926720839.719468241463.724487226168.7000001002006SSS2N0".
rewrite !KStep.round_up_pg_aligned by (auto; rewrite Z.add_mod, CA, NA by lia; reflexivity).
replace (cur <? cur + n) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition fx_rel (A : Z) (a : fixed_ans) (r : word) (u : bool) : Prop :=
match a with
| FxKept e => errno_of r = Some e /\ u = false
| FxDone => r = Z_to_bv 64 A /\ u = true
| FxLost e => errno_of r = Some e /\ u = true
end.
#[using="Type"] Lemma dec_mmap_fixed_shape A L rsp a : dec_mmap_fixed A L rsp = Some a -> exists r u, fx_rel A a r u /\ rstrip rsp = fixed_shape A L r u.
Proof.
unfold dec_mmap_fixed, fixed_shape, rstrip. destruct rsp as [r ws zs us cs ci]; cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
destruct ws; [| discriminate]. destruct zs; [| discriminate]. destruct us as [|[ua un] us].
- destruct cs; [| discriminate]. destruct (errno_of r) eqn:E; [| discriminate]. intros H; inversion H; subst. exists r, false. cbn. rewrite E. auto.
- destruct us; [| discriminate]. destruct cs; [| discriminate]. destruct (bv_eqb ua (Z_to_bv 64 A) && bv_eqb un (Z_to_bv 64 (mmap_len L))) eqn:E; [| discriminate].
apply andb_prop in E. destruct E as [E1 E2]. apply Fs.bv_eqb_eq in E1. apply Fs.bv_eqb_eq in E2. subst ua un.
destruct (errno_of r) eqn:E.
+ intros H; inversion H; subst. exists r, true. cbn. rewrite E. auto.
+ destruct (bv_eqb r (Z_to_bv 64 A)) eqn:E3; [| discriminate]. apply Fs.bv_eqb_eq in E3. intros H; inversion H; subst. exists (Z_to_bv 64 A), true. cbn. auto.
Qed.
End CANSEC1.
