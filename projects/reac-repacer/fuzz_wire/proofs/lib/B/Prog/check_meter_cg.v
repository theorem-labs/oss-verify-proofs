(* check_meter_cg: the ASan walk contract of check_meter (fuzz_wire.asan-ubsan 0x8016c = wire_sigma WS_check_meter,
   lib/B/Prog/WirePAddr.v; 852 bytes), as STATEMENTS only (no proof). No released ASan statement of this function
   exists, so nothing is copied: the text is in the caller-journal form of reac-repacer/fuzz_uci
   lib/B/Prog/check_clamp_cg.v (a fake frame from the stack malloc, a leaf callee, the post that keeps the caller's
   blocks and charges no meter), with the heap-buffer premises of reac-repacer/fuzz_uci lib/B/Prog/check_value_cg.v
   in place of check_clamp's stack-struct ones, since f is a heap block: LLVMFuzzerTestOneInput mallocs it
   (__interceptor_trampoline_malloc 0x52098, jal at 0x7fc7c, of n + (n = 0) bytes), copies the frame in
   (__asan_memcpy, 0x7fca4) and passes it as a0 = s0 at 0x7fcd8. Every address below is read from the disassembly of
   record of fuzz_wire.asan-ubsan (the size from its unstripped twin's symbol table, the GOT words' values from its .got).

   The C (fuzz_wire.c check_meter): eo = 16 when n > 13 and f[12..13] = 0x81 0x00, else 12; want = n >= 1000 &&
   n >= eo + 6 && f[eo..eo+1] = 0x88 0x19; a local uint16_t ctr = UNTOUCHED_CTR (0xa5c3); got = rp_meter_counter (f, n,
   &ctr); abort unless got == want, and ctr == f[eo + 2] | f[eo + 3] << 8 when want, else ctr == UNTOUCHED_CTR.
   The code (DIS of image B):
     +0x0   `addi sp, sp, -128` (0x8016c), +0x4 `sd zero, 0(sp)`, saves (ra, s0 .. s10 at 120 .. 32(sp)); +0x38
            `addi s0, sp, 128`; +0x3c `andi sp, sp, -32` (0x801a8; realigns sp: at most 0x10 more below entry - 128;
            `sd s6, 24(s1)` at +0xfc, 0x80268, s1 = the realigned sp, writes at entry - 0x68 or entry - 0x78, inside
            the 0x80 frame);
     +0x48 .. +0x5c reads __asan_option_detect_stack_use_after_return through its GOT word (0x801b8 / 0x801bc
            `auipc` / `ld` -> 0x988d0 -> 0xa0800, `lw` at 0x801c4) and the shadow base through GOT_CELL_K (0x801b4 /
            0x801c0 -> 0x98878 -> 0xa07f8, `ld s8` at 0x801c8); `beqz a2` at +0x64 (0x801d0) skips the fake stack when
            the flag word is 0 (the flag is 1: wire_cells row 6);
     +0x6c  `jal __asan_stack_malloc_0` (0x3c524; jal at 0x801d8) with a0 = 64 (`li a0, 64` at 0x801d4): the class-0
            fake frame (64 << 0 = 64 bytes); +0xc0 .. +0xc8 (0x8022c .. 0x80234) write its frame header (magic
            0x41b58ab3, the frame description 0x18cc3, the pc 0x8016c) and +0xd4 .. +0xf4 its 8 shadow bytes (0xf1 x4,
            0xf8, 0xf3 x3); the local ctr is at frame + 32 (`addi s5, s6, 32` at 0x80328): +0x1c4 `sb` 2 into its
            shadow byte (0x80330), +0x1d0 `sh` 0xa5c3 into it (0x8033c);
     +0x100 .. +0x1a0 the inlined w_is_tag / w_is_reac: loads f[12] (0x8028c), f[13] (0x802b4, when f[12] = 0x81),
            eo = 12 (0x802bc / 0x8031c) or 16 (0x80468), n < 1000 skips (0x802c4), f[eo] (0x802e4), f[eo + 1]
            (0x80308); want in s10 (0x80310 `seqz`, 0 at 0x80318 / 0x80324);
     +0x1e0 `jal rp_meter_counter` (0x81144; jal at 0x8034c) with a0 = f (s3), a1 = n (s4), a2 = &ctr (s5);
     +0x1e4 `bne a0, s10` to the abort; +0x1e8 `lhu a1, 0(s5)` reads ctr; when want, loads f[eo + 2] (0x80394) and
            f[eo + 3] (0x8039c) and +0x23c `beq` compares; else +0x254 compares ctr with 0xa5c3 (0x803b8 .. 0x803c0);
            a mismatch reaches __asan_handle_no_return (0x58e58; jal at 0x803ac) / abort (0x880cc; jal at 0x803b0);
     each load of f is guarded by its shadow byte, branching to __asan_report_load1 (0x57e5c; jal at 0x8047c,
            0x80488, 0x80498, 0x804a4, 0x804b0, 0x804bc) unless addressable;
     +0x25c .. +0x268 re-poison ctr's shadow (0xf8, 0x803c8) and retire the frame header (0x45e0360e, 0x803d4); on
            the fake-frame path +0x270 .. +0x290 write 0xf5 (stack-after-return) into the frame's 8 shadow bytes and
            `sb zero, 0(a0)` at +0x298 (0x80404) clears the frame's flag byte (a0 = the word at frame + 56 = frame +
            64 - 8, read at 0x80400): the fake frame is released (YG0d.v astack_free_law); on the frame = 0 path
            +0x2a0 .. +0x2bc zero the frame's shadow; +0x2c0 `addi sp, s0, -128`, restores, +0x2f4 `addi sp, sp, 128`.
   With the fake frame obtained (the stack-malloc premise count_cid 0 (frames Sc) < fs_frames 0 and
   stack_malloc_progressP), the dynamic-alloca path (+0x84 .. +0x9c, 0x801f0 .. 0x80208, which probes sp - 4096) is
   never taken. Its only callees are __asan_stack_malloc_0 and the leaf rp_meter_counter, which charge no meter: the
   post is mo_le MT Sc S2 0, as check_clamp's.
   UBSan checks, each branching to `unimp` at +0x304 (0x80470): f + 12 wraps (0x80274 `bgeu s3, a0`, a0 = -12),
   f + 13 wraps (0x8029c `bltu a0, s3`, a0 = -14), f + eo wraps (0x802cc `bltu a1, s9`, a1 = ~f), f + eo + 1 wraps
   (0x802f0 `bgeu s9, a1`), f + eo + 2 / + 3 wrap (0x80364 / 0x8036c `bltu a2, ...`, a2 = ~f). The block premise
   refutes each (as check_value_cg.v's, through the B core's lib/B/YCbq.v amem_range_of_block), and gives the leaf's
   f <> 0 premise. The `unimp` at +0x248 (0x803b4) follows `jal abort`, which does not return.
   The report branches are refuted by the block premise (YCbq.v range_addressable_of_block, shadow_hull_vis_of_block),
   the aborts by the leaf's post (a0 = want, and ctr = the counter when it counts, kept otherwise). *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_meter_counter_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_meter_counter_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_meter's frame (`addi sp, sp, -128` at WS_check_meter), the at most 0x10 bytes of `andi sp, sp, -32` (0x801a8)
   below it, and the ESTACK its two callees (the stack malloc, the leaf rp_meter_counter) use below the realigned sp. *)
Definition CM_FRAME : Z := 0x80.
Definition CM_ALIGN : Z := 0x10.
Definition CM_STK : Z := CM_FRAME + CM_ALIGN + ESTACK.
(* No allocator event: the class-0 stack malloc and its release record none (YG00.v stack_malloc, stack_free). *)
Definition CM_EV : Z := 0.
(* The fake-frame class (`li a0, 64` at 0x801d4, `jal __asan_stack_malloc_0` at 0x801d8). *)
Definition CM_CID : Z := 0.

Section cm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: the caller's journal extended by CM_EV events, callee-saved registers kept, the fake frame
   released (frames S2 = frames Sc), the caller's blocks exactly, every byte outside the call's stack window kept
   (YCbq.v acall_kept with no written range: f's bytes too), and no meter charge. *)
Definition wire_cm_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CM_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CM_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The contract at entry address a, in the caller-journal form. f (a0) holds the n (a1) frame bytes bs, inside one of
   the caller's blocks when n > 0 (check_value_cg.v's form); class 0 has a free fake frame. *)
Definition wire_check_meter_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (f n : Z) (bs : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 n ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CM_STK -> spZ regs <= sp0 ->
    Z.of_nat (length bs) = n ->
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA) ->
    garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs) ->
    count_cid CM_CID (frames Sc) < fs_frames CM_CID ->
    st_nev S + k + CM_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (wire_cm_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The statement the walk will prove: the class-0 stack-malloc entry of the record, the runtime cells, the allocator,
   meter and fake-stack laws (the meter's fs laws too: the fake frame changes the state's st_fs only, YG00.v
   stack_malloc / stack_free, and the post charges 0), and the contracts of __asan_stack_malloc_0 and the leaf
   rp_meter_counter give the contract at WS_check_meter. *)
Definition wire_check_meter_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) CM_CID = wire_sigma WS___asan_stack_malloc_0 ->
  wire_cells B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B CM_CID) ->
  (forall fx' : YK11.FPState, @wire_leaf_wr_at rc B (@LMC.wire_rp_meter_counter_cg) fx') ->
  wire_check_meter_cg (wire_sigma WS_check_meter).
End cm.
