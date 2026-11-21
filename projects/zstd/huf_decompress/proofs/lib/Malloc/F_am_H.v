(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (brk_new_pages_aligned, dec_mmap_fixed_shape)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Export MM_syscalls.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require KStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_am_A F_am_K F_am_C F_am_F F_am_G.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_am_H () := "C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_symK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega7EnvRing5PExpr04C35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7add_modC59OSSVerify5KrLib4Spec5KStepCround_up_pg_alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KStep>round_up_pg_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode=brk_new_pagesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc8ProgDeps9fixed_ans01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK59OSSVerify5KrLib6Malloc8ProgDeps9fixed_ans03C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_writesC4ELinuxProcessSemantics?LinuxProcessSem5State9eff_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_unmapsC4ELinuxProcessSemantics?LinuxProcessSem5State:eff_copiesK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib6Malloc6F_am_H6fx_relC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps>dec_mmap_fixedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes6rstripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;MM_syscalls;fixed_shapeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc8ProgDeps9fixed_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc8ProgDeps9fixed_ans02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition brk_regs (a0 : word) : _ :=
  mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
End BRKNODES.

(* [comment removed for export] *)
Lemma brk_new_pages_aligned cur n : 0 <= cur -> 0 < n -> cur mod 4096 = 0 -> n mod 4096 = 0 ->
  brk_new_pages cur (cur + n) = Some (cur, n).
Proof.
  intros C0 N0 CA NA. unfold brk_new_pages. rewrite <- !KStep.round_up_pg_eq.
  rewrite !KStep.round_up_pg_aligned by (auto; rewrite Z.add_mod, CA, NA by lia; reflexivity).
  replace (cur <? cur + n) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition fx_rel (A : Z) (a : fixed_ans) (r : word) (u : bool) : Prop :=
  match a with
  | FxKept e => errno_of r = Some e /\ u = false
  | FxDone => r = Z_to_bv 64 A /\ u = true
  | FxLost e => errno_of r = Some e /\ u = true
  end.
Lemma dec_mmap_fixed_shape A L rsp a : dec_mmap_fixed A L rsp = Some a -> exists r u, fx_rel A a r u /\ rstrip rsp = fixed_shape A L r u.
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
