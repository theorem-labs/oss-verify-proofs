(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3g.v, with its module paths and addresses changed. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YN3g.v, with its module paths and module names changed; 9 of its 54 lines of code are new or changed and 408 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-pw/fuzz_rate/lib/Reusable/YN3g2_cfw.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader conjunct of fdchan; the sys_rob conjunct of node_ok; the iovec copy-in ledger). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Import ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import RomBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YN3v YH00 YN3f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0d YN3g YK15_cfw YP0n2_cfw.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import SlotAgree.
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
assert (Hu64 : forall rom' a v, rom_ext rom rom' ->
ms_read_u64 (pend_at regs pc mem rom) a = Some v -> ms_read_u64 (pend_at regs pc mem rom') a = Some v).
{ intros rom' a v Hr. unfold ms_read_u64.
destruct (ms_read_bytes (pend_at regs pc mem rom) a (Z_to_bv 64 8)) as [bs|] eqn:E; [|discriminate].
pose proof (ms_read_bytes_wrom (pend_at regs pc mem rom) rom' a (Z_to_bv 64 8) bs Hr E) as E'.
change (wrom (pend_at regs pc mem rom) rom') with (pend_at regs pc mem rom') in E'.
rewrite E'. exact (fun X => X). }
assert (Hchk : forall rom', rom_ext rom rom' -> forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom') (getr regs 17)) eff model
= check_ret_only_copyins [(getr regs 11, 16%nat)] eff (Z_to_bv 64 0) model []).
{ intros rom' Hr eff.
pose proof (Hu64 rom' _ _ Hr Hb0) as Hb0'. pose proof (Hu64 rom' _ _ Hr Hl0) as Hl0'.
rewrite (chk66 segs) by exact Hno. rewrite Hfd, H32.
(* 08b1429: fdchan is a THREE-way conjunction at the revision --
   fd_lookup .. = Some (FdChannel ch) /\ w_is0 ch = false /\ m_channel_reader model = true --
   so it needs a nested pattern. The old two-way pattern left Hch as the PAIR, and `rewrite Hch`
   quoted the whole first conjunct as its pattern, reporting `Found no subterm matching
   "w_is0 ch = false"`: a mis-destructured hypothesis, not a missing subterm. Hcr is unused on
   this path -- the zero-total branch of check_writev returns before the reader gate at
   Checks/Sys/Fs/ReadWrite.v:5251 -- but it must be bound to reach Hch. *)
destruct Hfdc as [Hlk [Hch Hcr]].
(* 08b1429: the `if w_is0 ch` gate now SURVIVES the reductions below and is the outermost form
   left, so `rewrite Hch` moves to the end of the chain, where the goal actually exposes it. *)
unfold check_writev. cbn [in_mem sys_input]. rewrite Hlk, Hcnt.
change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
unfold import_iovecs, import_iovecs_accesses. rewrite bv_eqb_refl, Hiok. cbn [negb].
rewrite (read_iovec_entry_of (pend_at regs pc mem rom') (getr regs 11) b0 (Z_to_bv 64 0) Hb0' Hl0')
by (change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia).
change (Z.min (bv_unsigned (Z_to_bv 64 0)) MAX_RW_COUNT) with 0%Z. rewrite Hok0. cbn [negb].
cbv zeta.
replace (iovs_total (cap_iovecs [(b0, Z_to_bv 64 0)]) =? 0)%Z with true by reflexivity.
rewrite Hch. cbn [negb].
(* 08b1429: the copyins ledger is now built by State.iovec_entry_accesses (State.v:1713-1722)
   where this script wrote the literal [(getr regs 11, 16%nat)]. It reads the length word at
   the BITVECTOR address `a + 8` while this tree's hypotheses spell it
   `Z_to_bv 64 (bv_unsigned a + 8)`: equal, not syntactically equal. Bridge it with the SAME
   pair read_iovec_entry_of's own proof uses on the same two reads (YP0n.v:1275) --
   read_u64_ms then word_add_BV (YP0n.v:1016). *)
unfold iovec_entry_accesses.
rewrite !read_u64_ms, word_add_BV, Hl0', Hb0'. reflexivity. }
apply (crz_ret_only_copyins_silent B regs pc mem rom model [(getr regs 11, 16%nat)]
(Z_to_bv 64 0) model T Hh Hlz ltac:(rewrite Hno; reflexivity) (Hchk rom (rom_ext_refl rom)) Hh Hlz); [| exact Hc].
apply (rob_pend segs). intros rom' Hr eff. rewrite (Hchk rom' Hr), (Hchk rom (rom_ext_refl rom)). reflexivity.
Qed.
End e.
End d.
