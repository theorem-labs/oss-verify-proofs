From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL0g YL01 YI14 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import Slot SlotCallees.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require SlotInv.
Import ListNotations.
Local Open Scope Z_scope.

(* One iteration of the message loop of LLVMFuzzerTestOneInput (ubsan 0x14060): from the loop head 0x140fc of
   message m (SlotInv.HI) to the loop head of message m + 1, or to the entry of the last rec_clear (pc 0x15ab4,
   returning to 0x143ec; SlotInv.XI). The slot entry is (S, rg, mem0, md0, L0, A0) with the input block (p0, n0)
   holding pl and the resource bound b. *)

Definition head_at {rc : RunCeil} (B : malloc_syms) (API : AllocAPI B) (S : Z) (rg : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model) (L0 : layout) (A0 : astate) (p0 n0 m : Z) (c : config) : Prop :=
  exists (fx : FPState) p n L A regs mem md R O q,
    c = mkCfg (@mkst fx regs (Z_to_bv 64 0x140fc) mem (seg_rom rsegs)) md /\
    SlotInv.HI B API S rg mem0 md0 L0 A0 p0 n0 fx m p n L A regs mem md R O q.

Definition exit_at {rc : RunCeil} (B : malloc_syms) (API : AllocAPI B) (S : Z) (rg : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model) (L0 : layout) (A0 : astate) (c : config) : Prop :=
  exists (fx : FPState) L A regs mem md R O q,
    c = mkCfg (@mkst fx regs (Z_to_bv 64 0x15ab4) mem (seg_rom rsegs)) md /\
    SlotInv.XI B API S rg mem0 md0 L0 A0 fx L A regs mem md R O q.

Definition iter_spec : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
         (ra empty : Z) (rc : RunCeil) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
         (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound),
    frame_given_u B API LS SH SK ra empty -> cmd_callees B API -> harness_props ->
    lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b ->
    spZ rg = S ->
    forall (m : Z) (c : config),
      head_at B (API rc) S rg mem0 md0 L0 A0 p0 n0 m c ->
      SR rsegs c (fun c' => exit_at B (API rc) S rg mem0 md0 L0 A0 c' \/
                            head_at B (API rc) S rg mem0 md0 L0 A0 p0 n0 (m + 1) c').
