(* rp_copy_untag_cg: the ASan contract of rp_copy_untag (fuzz_wire.asan-ubsan 0x81414 = wire_sigma WS_rp_copy_untag),
   as a STATEMENT only (no proof). Form: reac-repacer/fuzz_uci's lib/B/Prog/rp_uci_int_cg.v (a library function that
   calls a runtime entry: the runtime contracts' realizes form), with its leaf callees taken through a leaf wrapper
   as fuzz_uci's lib/B/Prog/check_clamp_cg.v takes rp_hot_clamp; here the wrapper without aowned (wire_leaf_at),
   since neither leaf writes a caller byte.

   The C (src/repace_wire.c:88-99 rp_copy_untag; lib/Prog/rp_copy_untag_c.v): when n >= 50 and the frame f carries an
   802.1Q tag (is_tagged_reac), memmove (f + 12, f + 16, n - 16) and n -= 4; return n when reac_frame_is_reac (f, n)
   and f[16] = f[17] = 0 on the frame after the move, else 0. The model is lib/Prog/rp_copy_untag_c.v
   copy_untag_result (the result) and cu_bytes (the frame after the call), of the n bytes.
   The code (listing of image B, offsets from the entry):
     +0x0   `addi sp, sp, -48` (frame RCU_FRAME = 0x30; ra, s0 .. s3 stored at sp + 40 .. sp + 8);
     +0x18  `mv s0, a1` (s0 = n); +0x1c `li a1, 50` / +0x20 `bltu s0, a1, +0xc4`: when n < 50 it returns 0 before any
            call and before any access to f's bytes, their shadow or the runtime cells;
     +0x28 / +0x2c  `auipc` / `ld` of the GOT word 0x98878 (it holds 0xa07f8, the shadow-base cell), +0x30 `ld s3, 0(a0)`
            (s3 = the shadow base);
     +0x38  `jal is_tagged_reac` (0x8103c, a separate function in this image) with a0 = f; return address +0x3c;
     +0x40  `beqz a0, +0x6c` skips the move;
     +0x58 .. +0x60  a0 = f + 12, a2 = n - 16, a1 = f + 16; +0x64 `jal __asan_memmove` (0x510b0); return address +0x68;
     +0x68  `addi s0, s0, -4` (s0 = n - 4);
     +0x74  `jal reac_frame_is_reac` (0x8183c) with a0 = f, a1 = s0; return address +0x78; +0x78 `beqz a0` returns 0;
     +0x88 .. +0x94  the instrumented check of f + 16 (the shadow byte at ((f + 16) >> 3) + s3; +0xec / +0xf0 the
            `andi` / `blt` of the slow path), then +0x98 `lbu a0, 0(s2)` (f[16]); +0x9c `bnez` returns 0;
     +0xac .. +0xb8  the instrumented check of f + 17 (+0xfc / +0x100 slow path), then +0xbc `lbu` (f[17]); +0xc0
            `beqz a0, +0xc8` returns s0, else +0xc4 `li s0, 0` returns 0;
     the error path: `jal __asan_report_load1` (0x57e5c) at +0xf8 (f + 16) and +0x104 (f + 17).
   Its UBSan checks branch to `unimp` at +0xe8: +0x48 `bltu a0, s1` (a0 = -17: f + 16 wraps), +0x4c `beqz s1`
   (f = NULL), +0x54 `bgeu s1, a0` (a0 = -12: f + 12 wraps), +0x7c `beqz s1`, +0x84 `bgeu s1, a0` (a0 = -16), +0xa4
   `bltu a0, s1` (a0 = -18: f + 17 wraps). All are reached only when n >= 50, where `0 < f` and `f + n <= 2 ^ 63`
   below refute each. It calls nothing else.
   The form is the runtime contracts' realizes form (MemmoveDef.v amemmove_realizes): ecall_pre at entry, return to
   ra with AR at the same state, callee-saved registers kept, the result in a0, and every byte outside the stack
   window unchanged but the bytes the memmove writes, [f + 12, f + n - 4) when it moves (lib/Prog/rp_copy_untag_c.v
   cu_footprint). The stack window is its frame plus the ESTACK below the call's sp that __asan_memmove and the two
   leaves (16-byte frames) use. The frame premises are asked only when n >= 50 (the code returns before it reads the
   frame otherwise), and so is the post's frame clause. The report branches are refuted by the frame's
   range_addressable premise (shadow_hull_vis is the memmove's premise), and no report entry has a contract. The
   memmove changes only [f + 12, f + n - 4) and its stack window; neither holds a shadow byte of the frame
   (amem_range puts the frame in application memory, the stack is above the shadow), so the two checks after it read
   the shadow bytes of the entry state. The names and the shape are those
   of image A's statement of the same function (lib/A/Prog/rp_copy_untag_cg.v); image B adds the is_tagged_reac leaf
   premise and its own numbers. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Rt Require Import MemmoveDef.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require is_tagged_reac_cg reac_frame_is_reac_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_copy_untag_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module PRc := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_copy_untag_c.
Module LIT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.is_tagged_reac_cg.
Module LIR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.reac_frame_is_reac_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* rp_copy_untag's own frame (its first instruction `addi sp, sp, -48` at WS_rp_copy_untag) and its stack window: the
   frame plus the ESTACK that __asan_memmove and the leaves use below the call's sp. *)
Definition RCU_FRAME : Z := 0x30.
Definition RCU_STK : Z := RCU_FRAME + ESTACK.
(* A frame is at most W_RECV_MAX = 1600 bytes (fuzz/fuzz.h:35): fuzz/fuzz_wire.c:261-262 cuts n to it before check_copy
   (lib/Prog/check_copy_c.v `n <= 1600`), so the moved length n - 16 is below 2 ^ 32 (MemmoveDef.v
   amemmove_realizes). The shortest frame it reads is 50 bytes (+0x1c `li a1, 50`, +0x20 `bltu s0, a1`). *)
Definition RCU_LEN_MAX : Z := 1600.

(* The return addresses of its three calls, as offsets from its entry (the jal is 4 bytes before): is_tagged_reac at
   +0x38, __asan_memmove at +0x64, reac_frame_is_reac at +0x74 (0x81450, 0x8147c, 0x8148c). *)
Definition WIRE_RCU_RA_TAG : Z := wire_sigma WS_rp_copy_untag + 0x3c.
Definition WIRE_RCU_RA_MEMMOVE : Z := wire_sigma WS_rp_copy_untag + 0x68.
Definition WIRE_RCU_RA_ISREAC : Z := wire_sigma WS_rp_copy_untag + 0x78.

Section rcu. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* The contract at entry address a. n (a1) is a frame length, bs its bytes. When n >= 50 (below it the code returns 0
   at +0x20 before it reads f, as lib/Prog/rp_copy_untag_c.v guards its premise): f (a0) holds bs, f is above 0 and
   f + n at most 2 ^ 63, and every frame byte is visible, writable, not owned by the allocator, outside the call's
   stack window and addressable in the shadow. The post: return to ra at the same AR state, a0 = copy_untag_result n
   bs; when n >= 50 the frame holds cu_bytes n bs; every byte outside the call's stack window keeps its view but the
   bytes the memmove writes, [f + 12, f + n - 4) when cu_moves n bs (rp_copy_untag_c.v cu_footprint). *)
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

(* The statement the walk will prove: the runtime cells (wire_cells: the GOT word 0x98878 and the shadow-base cell
   0xa07f8, read at +0x28 .. +0x30, and the rows lib/B/AsanCells.v asan_cells that the leaves' premise asan_cells
   asks at the calls at +0x38 and +0x74), the allocator laws, the contract of __asan_memmove (lib/B/Rt/Memmove.v
   asan_memmove_contract proves it at 0x510b0), and the leaf statements of is_tagged_reac and reac_frame_is_reac
   (neither writes a caller byte, so each goes through wire_leaf_at, the wrapper without aowned) give the contract at
   WS_rp_copy_untag. *)
Definition wire_rp_copy_untag_holds_stmt : Prop :=
  wire_cells B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @amemmove_realizes fx' rc segs B (wire_sigma WS___asan_memmove)) ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LIT.wire_is_tagged_reac_cg) fx') ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LIR.wire_reac_frame_is_reac_cg) fx') ->
  wire_rp_copy_untag_cg (wire_sigma WS_rp_copy_untag).
End rcu.
