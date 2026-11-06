(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefStep RefStmts RefSys.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Syswrap.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

Theorem munmap_refines : munmap_stmt.
Proof.
  unfold munmap_stmt.
  intros md regs mm rom s addr len sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 H10 H11 HS HK.
  pose proof (minv_init s sp 32 Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp 32 Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm.
  note_win HI.
  mrun Hp HS Hag HI HW.
  (* [comment removed for export] *)
  mach_jal Hp HS. mrun Hp HS Hag HI HW.
  (* [comment removed for export] *)
  mach_sys_munmap Hp HS Hag HI.
  (* [comment removed for export] *)
  mach_jal Hp HS. mrun Hp HS Hag HI HW.
  mach_ret Hp HS Hag HK HI Hret.
Qed.

(* [comment removed for export] *)
Ltac mmap_refused Hp HS Hag HI HW HK Hret :=
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_MMAP + 0xd0);
  mach_br_dir Hp HS true ltac:(eperm_tac);
  (* [comment removed for export] *)
  mach_jal Hp HS; mrun Hp HS Hag HI HW;
  (* [comment removed for export] *)
  mach_jal Hp HS; mrun Hp HS Hag HI HW;
  mach_ret Hp HS Hag HK HI Hret.

Ltac mmap_granted Hp HS Hag HI HW HK Hret :=
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_MMAP + 0xd0);
  mach_br_dir Hp HS true ltac:(eperm_tac);
  mach_jal Hp HS; mrun_until Hp HS Hag HI HW (bv_unsigned PC_SYSCALL_RET + 0x8);
  mach_br_dir Hp HS true ltac:(sysret_addr_tac);
  mrun Hp HS Hag HI HW;
  mach_ret Hp HS Hag HK HI Hret.

Theorem mmap_refines : forall k, mmap_stmt k.
Proof.
  intros k. unfold mmap_stmt.
  intros md regs mm rom s len sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4
         H10 H11 H12 H13 H14 H15 HS HK.
  pose proof (minv_init s sp 80 Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp 80 Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm.
  note_win HI.
  pose proof (tsafe_sys_mmap_len _ _ _ _ HS) as Hlen.
  (* [comment removed for export] *)
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_MMAP + 0x3c).
  (* [comment removed for export] *)
  mach_br_dir Hp HS true ltac:(apply mmap_len_ok; alia).
  (* [comment removed for export] *)
  mrun Hp HS Hag HI HW.
  (* [comment removed for export] *)
  destruct k; (mach_sys_mmap Hp HS Hag HI;
    [ mmap_refused Hp HS Hag HI HW HK Hret | mmap_granted Hp HS Hag HI HW HK Hret ]).
Qed.

Theorem mprotect_refines : mprotect_stmt.
Proof.
  unfold mprotect_stmt.
  intros md regs mm rom s addr len sp ret pgbs P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4
         H10 H11 H12 Hpg Hpgv HS HK.
  pose proof (minv_init s sp 32 Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp 32 Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm.
  note_win HI.
  pose proof (tsafe_sys_mprotect_facts _ _ _ _ HS) as (Hlen & Haddr & Htop0).
  unfold page_size in Haddr.
  pose proof (u64_range len) as Hlr. pose proof (page_round_up_Z_bounds (bv_unsigned len) (proj1 Hlr)) as Hpb.
  assert (Hnw : bv_unsigned addr + bv_unsigned len + 8192 <= 2^64) by (clear HK HS; unfold page_size in Hpb; lia).
  assert (Hpgv' : bytes_le_to_Z pgbs = bv_unsigned (Z_to_bv 64 4096)) by (rewrite Hpgv; reflexivity).
  (* [comment removed for export] *)
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_MPROTECT + 0xc).
  (* [comment removed for export] *)
  mach_ld_rdn Hp Hpg Hpgv'.
  (* [comment removed for export] *)
  mrun Hp HS Hag HI HW.
  (* [comment removed for export] *)
  mach_sys_mprotect Hp HS Hag HI;
    (mach_jal Hp HS; mrun Hp HS Hag HI HW;
     try (mach_jal Hp HS; mrun Hp HS Hag HI HW);
     mach_ret Hp HS Hag HK HI Hret).
Qed.

(* [comment removed for export] *)
Ltac mmapf_err Hp HS Hag HI HW HK Hret :=
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_MMAP + 0xd0);
  mach_br_dir Hp HS true ltac:(eperm_tac);
  mach_jal Hp HS; mrun Hp HS Hag HI HW;
  mach_jal Hp HS; mrun Hp HS Hag HI HW;
  mach_ret Hp HS Hag HK HI Hret.

Theorem mmap_fixed_refines : mmap_fixed_stmt.
Proof.
  unfold mmap_fixed_stmt.
  intros md regs mm rom s addr len sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4
         H10 H11 H12 H13 H14 H15 HS HK.
  pose proof (minv_init s sp 80 Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp 80 Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm.
  note_win HI.
  pose proof (tsafe_sys_mmap_fixed_facts _ _ _ _ HS) as (Hlen & Haddr0 & Htop0).
  pose proof (u64_range len) as Hlr. pose proof (page_round_up_Z_bounds (bv_unsigned len) (proj1 Hlr)) as Hpb.
  mrun_until Hp HS Hag HI HW (bv_unsigned PC_MMAP + 0x3c).
  mach_br_dir Hp HS true ltac:(apply mmap_len_ok; alia).
  (* [comment removed for export] *)
  mrun Hp HS Hag HI HW. mach_jal Hp HS. mrun Hp HS Hag HI HW.
  mach_sys_mmap_fixed Hp HS Hag HI.
  - mmapf_err Hp HS Hag HI HW HK Hret.
  - mrun_until Hp HS Hag HI HW (bv_unsigned PC_MMAP + 0xd0).
    mach_br_dir Hp HS true ltac:(eperm_tac).
    mach_jal Hp HS. mrun_until Hp HS Hag HI HW (bv_unsigned PC_SYSCALL_RET + 0x8).
    mach_br_dir Hp HS true ltac:(sysret_addr_tac).
    mrun Hp HS Hag HI HW.
    mach_ret Hp HS Hag HK HI Hret.
  - mmapf_err Hp HS Hag HI HW HK Hret.
Qed.

End Syswrap.
