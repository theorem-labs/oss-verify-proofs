(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v; 57 of its 93 lines of code are new or changed and 1103 lines of the source are left out. *)
(* UciCcCut: the cut at check_clamp + 0x244, between the five field comparisons and the release of the
   class-1 fake frame. `cc_rel_stmt` is what the walk needs from the release-and-return piece:
   from the state at +0x244 (the five comparisons done, nothing written since the leaf returned), the
   function gives the frame back, restores the eleven callee-saved registers and returns, and the result
   is the caller-journal contract of lib/A/Prog/check_clamp_cg.v.
   The piece it states runs the offsets 0x244 to 0x314 of the listing lib/A/Prog/UciPList.v:
     0x244 .. 0x25c   the three shadow bytes of the local set to the released value and the frame's magic
                      word rewritten;
     0x260            `beqz s2`, never taken (s2 holds the frame, which is at least 4096);
     0x264 .. 0x2ac   the sixteen shadow bytes of the frame set to the stack-after-return value and the
                      frame's flag byte (the word at frame + 120) cleared: the frame is given back;
     0x2b4 .. 0x314   (the arm the `beqz` would take) the eleven reloads and `ret`.
   The flag store is lib/A/Prog/UciCcKit.v `ucc_flag_store_pi`; the journal and the post are
   lib/Reusable/YCbq.v `ajournal` / `acall_kept` and lib/A/Prog/check_clamp_cg.v `uci_cc_post`. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import
UciPSyms UciPList UciPAddr UciPPa UciPImg UciPPaLib UciPCJ.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import Cells Step Frame ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciCg UciCcKit UciCcLeafb.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import check_clamp_cg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module UCells := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The first slot of the release piece. *)
Definition CC_REL : Z := AF_check_clamp + 0x244.
(* The first slot of the five field comparisons. *)
Definition CC_CMP : Z := AF_check_clamp + 0x124.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).

(* What the walk has in hand at +0x244, and what it needs from +0x244 on.
   `regs` is the caller's register map at the entry of check_clamp (so `YK11.getr regs 1` is the return
   address and `spZ regs` the entry stack pointer); `sp1` is the realigned stack pointer this function
   runs on; `F` is the address of the class-1 fake frame and `pos` its slot, `lyc`/`S2` the layout and
   the allocator state with that frame live, `mem` and `md` the memory and the model at +0x244.
   `regs2` is the register map at +0x244. *)
Definition cc_rel_stmt : Prop :=
  astack_free_law segs B -> frame_flag_lawP segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
         (regs regs2 : bvmap 5 word) (mem : word -> option byte) (md : Model)
         (S2 : astate) (pos sp1 F : Z),
    (* the caller's journal, and this function's own journal inside it *)
    @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    @ajournal rc tfib_sink_head segs B CC_STK (spZ regs) [] lyc Sc W memc mdc
      [(CC_CID, pos)] lyc S2 W mem md 0 ->
    (* the fake frame this function took, and the registers that hold it *)
    frames S2 = (CC_CID, pos) :: frames Sc ->
    ablocks B lyc S2 = ablocks B lyc Sc ->
    st_nev S2 = st_nev Sc ->
    F = frame_addr lyc CC_CID pos ->
    YK11.getr regs2 2 = Z_to_bv 64 sp1 -> YK11.getr regs2 8 = w64 (spZ regs) ->
    YK11.getr regs2 18 = Z_to_bv 64 F -> YK11.getr regs2 22 = Z_to_bv 64 (SHADOW_OFF + F / 8) ->
    YK11.getr regs2 23 = Z_to_bv 64 F ->
    (* the registers this piece never writes and never reloads *)
    YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
    YK11.getr regs2 25 = YK11.getr regs 25 -> YK11.getr regs2 26 = YK11.getr regs 26 ->
    YK11.getr regs2 27 = YK11.getr regs 27 ->
    YK0s.ret_ok (YK11.getr regs 1) ->
    (* the ten words this function saved at entry, still where it put them: the `ret` and the ten
       reloads at +0x2e8 .. +0x310 read them back, so the caller sees its own registers again. *)
    Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (spZ regs - fst o) =
        Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o)))))
      [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24)] ->
    (* the frame's flag pointer, as the class-1 stack malloc left it; nothing writes there afterwards *)
    rdword (aview segs (w_H W) mem) (F + 120) = Some (flag_addr lyc CC_CID pos) ->
    (* the fake frame changed the allocator state's frame stack only *)
    mo_le MT Sc S2 0 ->
    (* the geometry the walk established before +0x244 *)
    spZ regs mod 16 = 0 -> sp1 mod 32 = 0 -> spZ regs - 112 <= sp1 <= spZ regs - 96 ->
    sp0 - STK <= spZ regs - CC_STK -> spZ regs <= sp0 ->
    4096 <= F -> F mod 32 = 0 -> F + 128 <= alloc_ceiling ->
    uci_cells B -> AR_laws segs B ->
    count_cid CC_CID (frames Sc) < fs_frames CC_CID ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CC_REL)) mem (YK11.seg_rom segs)) md)
      (@uci_cc_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The five field comparisons, +0x124 .. +0x240, written as a continuation: the piece writes no memory
   and calls nothing, so the memory, the model and the journal come out as they went in, and only the
   caller-saved registers a0 .. a4 change. `pin` is the caller's record, `F + 32` the local copy the
   leaf clamped, `mm` margin_max. The piece must reach +0x244, that is: the abort at +0x318 and the five
   report calls at +0x320, +0x330, +0x344, +0x354 and +0x364 are unreachable. *)
Definition cc_cmp_stmt : Prop :=
  forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
         (Q : world segs -> config -> Prop)
         lyc Sc memc mdc (S2 : astate) (sp0r pos pin F mm : Z) (p : rp_hot),
    @ajournal rc tfib_sink_head segs B CC_STK sp0r [] lyc Sc W memc mdc
      [(CC_CID, pos)] lyc S2 W mem md 0 ->
    YK11.getr regs 19 = w64 pin -> YK11.getr regs 20 = w64 mm ->
    YK11.getr regs 21 = Z_to_bv 64 (F + 32) -> YK11.getr regs 24 = w64 SHADOW_OFF ->
    2 ^ 46 <= pin -> pin + 20 <= 2 ^ 47 -> 4096 <= F -> F + 128 <= alloc_ceiling ->
    F + 128 <= pin ->
    PHC.hot_int p -> 0 <= mm <= INT_MAX ->
    cells_at rsegs (mrestrict (w_H W) mem) pin (PHC.hot_cells p) ->
    cells_at rsegs (mrestrict (w_H W) mem) (F + 32) (PHC.hot_cells (rp_hot_clamp_m p mm)) ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF pin 20 ->
    (forall regs' mat', aregs_preserved regs regs' ->
       SRr segs W (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + CC_REL)) mem
         (YK11.seg_rom segs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
    SRr segs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CC_CMP)) mem
      (YK11.seg_rom segs)) md) Q.
End cut.
