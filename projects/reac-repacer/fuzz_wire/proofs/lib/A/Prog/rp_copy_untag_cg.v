(* rp_copy_untag_cg: the ASan contract of rp_copy_untag (fuzz_wire.asan 0x813e0 = wire_sigma WS_rp_copy_untag), as a
   STATEMENT only (no proof). Form: the realizes form of reac-repacer/fuzz_uci's lib/A/Prog/rp_uci_int_cg.v (a
   library function that calls a runtime entry: ecall_pre at entry, return to ra with AR at the same state,
   callee-saved registers kept, the result in a0, every byte outside its stack window and the bytes it writes
   unchanged); its program callee reac_frame_is_reac, a leaf that writes no byte outside its own frame, is a premise
   through the non-writing leaf wrapper wire_leaf_at (fuzz_uci's lib/A/Prog/check_clamp_cg.v takes its writing leaf
   rp_hot_clamp the same way through the writing wrapper uci_leaf_wr_at).

   The C (src/repace_wire.c rp_copy_untag; the model is lib/Prog/rp_copy_untag_c.v): when n >= 50 and the frame f
   carries an 802.1Q tag before the REAC EtherType (f[12..13] = 81 00, f[16..17] = 88 19), memmove (f + 12, f + 16,
   n - 16) and n -= 4; return n when reac_frame_is_reac (f, n) and f[16..17] = 00 00, else 0. The result is
   copy_untag_result n bs and the frame afterwards holds cu_bytes n bs.

   The code (the neutral listing of image A; offsets from 0x813e0):
     +0x0   `addi sp, sp, -32`: frame 0x20 (ra, s0, s1, s2 at sp + 24 / 16 / 8 / 0);
     +0x14  `mv s0, a1`; +0x18 `li a1, 50`; +0x1c `bltu s0, a1, +0x100`: n < 50 goes to +0x100 and returns 0 without
            reading f, its shadow or the runtime cells;
     +0x24  `auipc a0, 0x17`, +0x28 `ld a0, 996(a0)`: the GOT word at 0x987e8; +0x2c `ld s2, 0(a0)`: the shadow base
            from its cell 0xa0778 (rows 1-2 of wire_cells);
     +0x30..+0xa8  the tag test, four 1-byte loads, each after an instrumented check of its shadow byte (srli 3, add s2,
            lb, bnez to a stub that does `andi 7` / `blt` back, else calls the report entry 0x580bc):
              f[12] = 0x81 (load +0x44, check +0x3c, stub +0x120, report call +0x128),
              f[13] = 0    (load +0x64, check +0x5c, stub +0x138, report call +0x144),
              f[16] = 0x88 (load +0x80, check +0x78, stub +0x154, report call +0x160),
              f[17] = 0x19 (load +0xa0, check +0x98, stub +0x164, report call +0x170);
            a mismatch branches to +0xb8;
     +0xac  `addi a2, s0, -16`; +0xb0 `jal` the checked memmove 0x51310 with a0 = f + 12 (+0x30), a1 = f + 16 (+0x6c),
            a2 = n - 16: return address 0x81494 (+0xb4); +0xb4 `addi s0, s0, -4`;
     +0xb8  a0 = f, a1 = s0; +0xc0 `jal reac_frame_is_reac` 0x817bc: return address 0x814a4 (+0xc4);
            +0xc4 `beqz a0, +0x100`;
     +0xc8..+0xfc  the audio test, two 1-byte loads after instrumented checks:
              f[16] = 0 (load +0xdc, check +0xd4, stub +0x12c, report call +0x134), else +0x100,
              f[17] = 0 (load +0xf8, check +0xf0, stub +0x148, report call +0x150): `beqz a0, +0x104`;
     +0x100 `li s0, 0`; +0x104 `mv a0, s0`; restores; +0x118 `addi sp, sp, 32`; +0x11c `ret`.
   It calls nothing else: the checked memmove, reac_frame_is_reac and, on the error paths, the report entry.
   The six error paths are refuted by the frame's range_addressable premise (shadow_hull_vis is the memmove's
   premise); no report entry has a contract. The memmove changes only [f + 12, f + n - 4) and its stack window, and the
   leaf only its stack window; neither holds a shadow byte of the frame (amem_range puts the frame in application
   memory, the stack is above the shadow), so the two checks after them read the shadow bytes of the entry state. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Rt Require Import MemmoveDef.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require reac_frame_is_reac_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_copy_untag_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module PRc := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_copy_untag_c.
Module LIR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.reac_frame_is_reac_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* rp_copy_untag's own frame (`addi sp, sp, -32` at WS_rp_copy_untag) and its stack window: the frame plus the ESTACK
   below the call's sp that the checked memmove (MemmoveDef.v) and the leaf reac_frame_is_reac (its frame 16,
   `addi sp, sp, -16` at 0x817bc) use. *)
Definition RCU_FRAME : Z := 0x20.
Definition RCU_STK : Z := RCU_FRAME + ESTACK.
(* A frame is at most W_RECV_MAX = 1600 bytes: LLVMFuzzerTestOneInput (0x7fe58) cuts the input to it (`li a0, 1600`
   at +0x58, `li s1, 1600` at +0x64; lib/Prog/LLVMFuzzerTestOneInput.v wk) and check_copy (0x80c38) passes that
   length on as a1 (`mv a1, a2` at +0x38; lib/Prog/check_copy_c.v). *)
Definition RCU_LEN_MAX : Z := 1600.

Section rcu. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* The contract at entry address a. n (a1) is a frame length, bs its bytes. When n >= 50 (below it the code returns 0
   at +0x1c before it reads f, as lib/Prog/rp_copy_untag_c.v guards its premise): f (a0) holds bs, and every frame byte
   is visible, writable, not owned by the allocator, outside the call's stack window and addressable in the shadow.
   The post: return to ra at the same AR state, a0 = copy_untag_result n bs; when n >= 50 the frame holds
   cu_bytes n bs; every byte outside the call's stack window keeps its view but the bytes the memmove writes,
   [f + 12, f + n - 4) when cu_moves n bs (rp_copy_untag_c.v cu_footprint). *)
Definition wire_rp_copy_untag_cg (a : Z) : Prop :=
  forall ly S W regs mem md (f n : Z) (bs : list byte),
    ecall_pre segs B ly S W regs mem md ->
    ly_stk_lo ly + RCU_STK <= spZ regs ->
    (forall x, spZ regs - RCU_STK <= x < spZ regs -> apresent (w_H W) mem x) ->
    YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 n ->
    0 <= n <= RCU_LEN_MAX -> Z.of_nat (length bs) = n ->
    (50 <= n ->
       0 < f /\ f + n <= 2 ^ 63 /\
       garr8 segs (mrestrict (w_H W) mem) f (map (fun b : byte => bv_unsigned b) bs) /\
       (forall x, f <= x < f + n ->
          aview segs (w_H W) mem x <> None /\ writable_at segs (mrestrict (w_H W) mem) x /\ ~ aowned B ly S x /\
          ~ (spZ regs - RCU_STK <= x < spZ regs)) /\
       amem_range f n /\
       range_addressable (aview segs (w_H W) mem) SHADOW_OFF f n /\
       shadow_hull_vis (aview segs (w_H W) mem) f n) ->
    SRr segs W (@cfg_at fx segs a regs mem md)
      (fun W' c' => W' = W /\ exists regs' mem' md',
         c' = @cfg_at fx segs (raZ regs) regs' mem' md' /\
         @AR rc segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
         YK11.getr regs' 10 = w64 (PRc.copy_untag_result n bs) /\
         (50 <= n -> forall i, 0 <= i < n ->
            aview segs (w_H W) mem' (f + i) = Some (PRc.cu_byte (PRc.cu_bytes n bs) (Z.to_nat i))) /\
         (forall x, 0 <= x < 2 ^ 64 -> ~ (PRc.cu_moves n bs = true /\ f + 12 <= x < f + n - 4) ->
            ~ (spZ regs - RCU_STK <= x < spZ regs) -> aview segs (w_H W) mem' x = aview segs (w_H W) mem x) /\
         (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x)).

(* The statement the walk will prove: the runtime cells (wire_cells: rows 1-2, the GOT word 0x987e8 and the
   shadow-base cell 0xa0778, read at +0x24..+0x2c; rows 1-19, AsanCells.asan_cells, which the leaf's premise
   asan_cells asks at the call at +0xc0), the allocator laws, the checked memmove's contract (lib/A/Rt/Memmove.v
   asan_memmove_contract proves it at 0x51310) and the leaf statement of reac_frame_is_reac give the contract at
   WS_rp_copy_untag. The leaf premise reads the leaf statement wire_reac_frame_is_reac_cg
   (lib/A/Prog/reac_frame_is_reac_cg.v) through the non-writing leaf wrapper wire_leaf_at. *)
Definition wire_rp_copy_untag_holds_stmt : Prop :=
  wire_cells B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @amemmove_realizes fx' rc segs B (wire_sigma WS___asan_memmove)) ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LIR.wire_reac_frame_is_reac_cg) fx') ->
  wire_rp_copy_untag_cg (wire_sigma WS_rp_copy_untag).
End rcu.
