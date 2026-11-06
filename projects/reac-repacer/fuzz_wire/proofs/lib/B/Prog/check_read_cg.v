(* check_read_cg: the ASan walk contract of check_read (fuzz_wire.asan-ubsan 0x805f4 = wire_sigma WS_check_read), as
   STATEMENTS only (no proof), in the caller-journal form of reac-repacer/fuzz_uci's lib/B/Prog/check_clamp_cg.v.

   The C (fuzz_wire.c check_read): fill a local v[12] with UNTOUCHED_SAMPLE, compute the width of len itself,
   rp_slot_read(c, len, slot, v), abort unless the answer is the harness's own rule, and abort unless each sample is
   the one the REAC braid puts in that slot (or, for a declined read, is still UNTOUCHED_SAMPLE).
   The code (image B):
     +0x0   `addi sp, sp, -0xc0`, `sd zero, 0(sp)`, saves ra and s0..s11; +0x3c `addi s0, sp, 0xc0`;
            +0x40 `andi sp, sp, -0x20` (realigns sp: at most 0x10 more below entry - 0xc0), +0x44 `mv s1, sp`;
     +0x50..+0x6c reads __asan_option_detect_stack_use_after_return through its GOT word (0x988d0 -> 0xa0800) and the
            shadow base through 0x98878 (-> 0xa07f8); `beqz a2` at +0x6c skips the fake stack when the flag word is 0
            (the flag is 1: wire_cells);
     +0x74  `jal __asan_stack_malloc_1` (0x3c698) with a0 = 0x80 (+0x70): the class-1 fake frame (64 << 1 = 128
            bytes); v is at frame + 0x20; +0xa8..+0x128 write its frame header (the magic 0x41b58ab3, the
            description and the pc 0x805f4) and its shadow: 0xf1 over the 32-byte left redzone (shadow bytes 0..3),
            0 over the 48 bytes of v (shadow bytes 4..9) and 0xf3 over the 48-byte right redzone (shadow bytes
            0xa..0xf);
     +0x12c..+0x140 fill v with 0x5a5a5a5a word by word (`sw a1, 0(a2)` at 0x8072c): image B inlines this loop, where
            image A calls __asan_memset, so image B's text has no intrinsic premise;
     +0x144..+0x188 the width of len, inlined (w_width, no memory access; its loop body is +0x168..+0x17c);
     +0x194..+0x1a8 and +0x468..+0x484 read c[16] and c[17] (w_is_audio), each behind the shadow byte of its address,
            which branches to __asan_report_load1 (0x57e5c) at 0x80aa4 / 0x80ab0;
     +0x1c8  `jal rp_slot_read` (0x815ec) with a0 = c, a1 = len, a2 = slot, a3 = v;
     +0x1cc  `bne a0, s11` branches to __asan_handle_no_return (0x58e58) / abort (0x880cc) at +0x49c / +0x4a0, and so
            does the sample comparison at +0x338 / +0x344; the walk shows neither is reached;
     +0x294..+0x2e0 the comparison loop reads the braid bytes of c into its 6-byte buffer at s1 + 82, each behind the
            shadow byte of its address, which branches to __asan_report_load1 at 0x80ab4 / 0x80ab8 (through the slow
            paths 0x808dc / 0x808e8); the shadow of the block refutes these two and the two above;
     +0x358..+0x3d4 poison v's shadow with 0xf8 and retire the frame header (the magic 0x45e0360e); on the fake-frame
            path it writes 0xf5 (stack-after-return) into the frame's 16 shadow bytes and `sb zero, 0(a0)` at +0x3d8
            clears the frame's flag byte (a0 = the word at frame + 0x78 = frame + 128 - 8): the fake frame is
            released (YG0d.v astack_free_law); on the frame = 0 path +0x3e0..+0x41c zero the frame's shadow.
   With the fake frame obtained (the stack-malloc premise count_cid 1 (frames Sc) < fs_frames 1 and
   stack_malloc_progressP), the dynamic-alloca path (+0x8c..+0xa4, which probes sp - 4096) is never taken.
   The frame c is the caller's heap block (LLVMFuzzerTestOneInput's fuzz_dup, or check_copy's output), outside this
   call's stack window: the walk reads it through the image view and its shadow, which the caller proves. The leaf
   chain (rp_slot_read -> rp_slot_width -> rp_frame_channels -> reac_frame_clean_len) reads three 8-byte .rodata
   constants: 0x10300 and 0x103b0 through the read-only view (WireCg.v WIRE_RO_RD, wire_rom_view_rd), and 0x10328, an
   owned static of the core, as a constant cell of the record (WireCg.v wire_cells). check_read itself reads no
   .rodata: w_width is inlined with immediates.
   Image B's UBSan checks branch to the `unimp` at 0x80a8c: c + 16 and c + 17 wrapping (+0x18c, +0x460), the braid
   arithmetic of the comparison loop (the `mul` / `mulw` and `add` / `addw` pairs at +0x240..+0x258), c + 50 plus the
   braid offset wrapping (+0x270), and the address checks at +0x294 and +0x300..+0x308. The block premise puts c and
   c + len inside one of the caller's blocks, which the allocator model keeps inside application memory, and the
   width's own bounds (2 <= width <= 40 with 52 + 36 * width <= len, lib/Prog/rp_slot_width_c.v) bound every offset
   into c by len; the three checks at +0x300..+0x308 are on addresses in check_read's own frame (s1 + 82 + 0..5),
   which the stack window bounds. So each trap is refuted and none of them is a hypothesis here. *)
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
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_slot_read_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_read_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_slot_read_cg.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_read's frame (`addi sp, sp, -0xc0` at WS_check_read), the at most 0x10 bytes of `andi sp, sp, -0x20` below
   it, and the ESTACK its two callees (the stack malloc and rp_slot_read) use below the realigned sp. *)
Definition CRD_FRAME : Z := 0xc0.
Definition CRD_ALIGN : Z := 0x10.
Definition CRD_STK : Z := CRD_FRAME + CRD_ALIGN + ESTACK.
(* No allocator event: the class-1 stack malloc and its release record none (YG00.v stack_malloc, stack_free). *)
Definition CRD_EV : Z := 0.
(* The fake-frame class (`addi a0, zero, 0x80` at +0x70, `jal __asan_stack_malloc_1` at +0x74). *)
Definition CRD_CID : Z := 1.
(* W_RECV_MAX: the daemon's receive buffer, the longest frame LLVMFuzzerTestOneInput passes (fuzz/fuzz.h). *)
Definition W_RECV_MAX : Z := 1600.

Section crd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: the caller's journal extended by CRD_EV events, callee-saved registers kept, the fake frame
   released (frames S2 = frames Sc), the caller's blocks exactly, every byte outside the call's stack window kept
   (YCbq.v acall_kept with no written range: check_read writes only its own fake frame), and no meter charge. *)
Definition wire_crd_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CRD_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CRD_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The contract at entry address a, in the caller-journal form. pin (a0) is the frame: len (a1) bytes, held in one
   of the caller's blocks (the buffer form of fuzz_uci's check_value; the shadow of those bytes, which the report
   branches need, follows from the block and AR by YCbq.v range_addressable_of_block and shadow_hull_vis_of_block,
   since pin + len <= bA + nA <= bA + req_size nA, YG00.v req_size); slot (a2) is an int, which the harness takes
   from the input's flag byte and which may be negative; class 1 has a free fake frame; the two read-only constants
   its leaf chain reads are the image's (wire_rom_view_rd). *)
Definition wire_check_read_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (pin len slot : Z)
         (bs : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 pin -> YK11.getr regs 11 = w64 len -> YK11.getr regs 12 = w64 slot ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CRD_STK -> spZ regs <= sp0 ->
    0 <= len <= W_RECV_MAX -> Z.of_nat (length bs) = len ->
    INT_MIN <= slot <= INT_MAX ->
    (0 < len -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= pin /\ pin + len <= bA + nA) ->
    garr8 segs (mrestrict (w_H W) memc) pin (map (fun b : byte => bv_unsigned b) bs) ->
    count_cid CRD_CID (frames Sc) < fs_frames CRD_CID ->
    wire_rom_view_rd W memc ->
    st_nev S + k + CRD_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (wire_crd_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The statement the walk will prove: the class-1 stack-malloc entry of the record, the runtime and constant cells
   (0x10328 among them), the read-only reads of the record (the two constants unowned, errno outside the read-only
   image), the allocator, meter and fake-stack laws (the meter's fs laws too: the fake frame changes the state's st_fs
   only, YG00.v stack_malloc / stack_free, and the post charges 0), and the contract of __asan_stack_malloc_1 and of the
   leaf rp_slot_read give the contract at WS_check_read. rp_slot_read writes v, so it comes through the kit's
   writing wrapper wire_leaf_wr_at: v lies in check_read's live class-1 fake frame, whose bytes are never aowned and
   never in the loaded image. Image B's text calls no interceptor and no __asan_memcpy / __asan_memset, so no
   intrinsic row is a premise (image A's twin carries one for __asan_memset). *)
Definition wire_check_read_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) CRD_CID = wire_sigma WS___asan_stack_malloc_1 ->
  wire_cells B ->
  wire_ro_rd_unowned B -> wire_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B CRD_CID) ->
  (forall fx' : YK11.FPState, @wire_leaf_wr_at rc B (@LSR.wire_rp_slot_read_cg) fx') ->
  wire_check_read_cg (wire_sigma WS_check_read).
End crd.
