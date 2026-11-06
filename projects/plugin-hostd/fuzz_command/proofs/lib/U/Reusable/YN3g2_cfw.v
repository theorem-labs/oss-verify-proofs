(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YN3g.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YN3g2_cfw.v, with its module paths changed; 2 of its 54 lines of code are new or changed and 2 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YN3v YH00 YN3f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0d YN3g YK15_cfw YP0n2_cfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma crz_writev_empty : forall regs pc mem rom model fd ch (b0 : word) T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd -> getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 1 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some (Z_to_bv 64 0) ->
access_okb (getr regs 11) 16 = true ->
access_okb b0 0 = true ->
crealizes B (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom) model) T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model fd ch b0 T Hh Hlz Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hiok Hok0 Hc.
eapply (crz_ret_only_copyins_silent B regs pc mem rom model [(getr regs 11, 16%nat)]
(Z_to_bv 64 0) model T Hh Hlz ltac:(rewrite Hno; reflexivity)); [|exact Hh|exact Hlz|exact Hc].
intros eff. rewrite (chk66 segs) by exact Hno. rewrite Hfd, H32.
destruct Hfdc as [Hlk Hch].
unfold check_writev. cbn [in_mem sys_input]. rewrite Hlk, Hch, Hcnt.
change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
unfold import_iovecs, import_iovecs_accesses. rewrite bv_eqb_refl, Hiok. cbn [negb].
rewrite (read_iovec_entry_of (pend_at regs pc mem rom) (getr regs 11) b0 (Z_to_bv 64 0) Hb0 Hl0)
by (change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia).
change (Z.min (bv_unsigned (Z_to_bv 64 0)) MAX_RW_COUNT) with 0%Z. rewrite Hok0. cbn [negb].
cbv zeta.
replace (iovs_total (cap_iovecs [(b0, Z_to_bv 64 0)]) =? 0)%Z with true by reflexivity.
reflexivity.
Qed.
End e.
End d.
