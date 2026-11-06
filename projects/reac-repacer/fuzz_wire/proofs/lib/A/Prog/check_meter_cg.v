(* check_meter_cg: the ASan walk contract of check_meter (fuzz_wire.asan 0x80340 = wire_sigma WS_check_meter), as
   STATEMENTS only (no proof). Form: reac-repacer/fuzz_uci lib/A/Prog/check_clamp_cg.v (the caller-journal form of an
   own function with a fake frame and one writing leaf) at class 0 and without __asan_memcpy; the input buffer is a
   heap block, so its premise is the one of reac-repacer/fuzz_uci lib/A/Prog/check_value_cg.v (a range inside one of
   the caller's blocks), not check_clamp's caller-stack pointer. No released ASan statement of check_meter exists; this
   is written new.

   The C (fuzz_wire.c check_meter): eo = (n > 13 && f[12..13] is the 802.1Q tag) ? 16 : 12; want = n >= 1000 &&
   n >= eo + 6 && f[eo..eo+1] is the REAC EtherType; uint16_t ctr = UNTOUCHED_CTR (0xa5c3); got =
   rp_meter_counter(f, n, &ctr); abort unless got == want, and ctr == f[eo + 2] | f[eo + 3] << 8 when want, else ctr ==
   UNTOUCHED_CTR. Its caller LLVMFuzzerTestOneInput passes f = the fuzz_dup copy, a malloc'd block of max(n, 1) bytes
   (`jal __interceptor_trampoline_malloc` at 0x7fed0, f kept in s0, `jal check_meter` at 0x7ff2c with a0 = s0).
   The code (objdump of record of fuzz_wire.asan; addresses there, offsets from the entry 0x80340):
     0x80340 (+0x0)   `addi sp, sp, -128` (frame 0x80), `sd zero, 0(sp)` at 0x80344, saves of ra and s0..s10 at
                      0x80348..0x80374; `addi s0, sp, 128` at 0x80378;
     0x8037c (+0x3c)  `andi sp, sp, -32` (realigns sp: at most 0x10 more below entry - 0x80); `sd s6, 24(s1)` at
                      0x8043c (s1 = the realigned sp) writes at entry - 0x68 or entry - 0x78, inside the 0x80 frame;
     0x80388..0x8039c reads the shadow base through its GOT word (0x987e8 -> 0xa0778, `ld s8, 0(a1)` at 0x8039c) and
                      __asan_option_detect_stack_use_after_return through its GOT word (0x98840 -> 0xa0780, `lw` at
                      0x80398); `beqz a2` at 0x803a4 skips the fake stack when the flag word is 0;
     0x803a8 (+0x68)  `li a0, 64` (a0 = 0x40); 0x803ac (+0x6c) `jal __asan_stack_malloc_0` (0x3c544): the class-0 fake
                      frame (64 << 0 = 64 bytes); with it, the dynamic-alloca path 0x803c4..0x803dc (which probes
                      sp - 4096) is never taken;
     0x80400..0x80434 the frame header (`sd` at frame + 0, + 8, + 16: 0x41b58ab3, the descriptor 0x18cc3, the entry
                      0x80340) and its shadow (0xf1 x4, 0xf8 over the local, 0xf3 x3);
     0x80440..0x804c8 when n >= 14 reads f[12], f[13]; when n >= 1000 reads f[eo], f[eo + 1] (want in s10); each read
                      is guarded by __asan_report_load1 (0x580bc) at 0x8061c, 0x80644, 0x80650, 0x8065c;
     0x804e0 (+0x1a0) `addi s5, s6, 32`: ctr at frame + 0x20; `sb` 2 to its shadow byte at 0x804e8; `sh` 0xa5c3 (lui
                      0xa / addi 1475 at 0x804ec / 0x804f0) to it at 0x804f4;
     0x80504 (+0x1c4) `jal rp_meter_counter` (0x81168) with a0 = f, a1 = n, a2 = frame + 0x20 (0x804f8..0x80500);
     0x80508..0x80564 `bne a0, s10`; `lhu` of ctr at 0x8050c; when want reads f[eo + 2], f[eo + 3] (report branches
                      at 0x80628, 0x80638) and compares; else compares ctr with 0xa5c3; a mismatch branches to
                      __asan_handle_no_return (0x590b8) / abort (0x88038) at 0x80554 / 0x80558 (+0x214 / +0x218);
     0x80568..0x805cc re-poison the local (0xf8), retire the header (0x45e0360e at frame + 0), and on the fake-frame
                      path write 0xf5 (stack-after-return) over the frame's shadow and `sb zero, 0(a0)` at 0x805a8
                      clears the frame's flag byte (a0 = the word at frame + 56 = frame + 64 - 8, `ld` at 0x805a4): the
                      fake frame is released (YG0d.v astack_free_law).
   No `unimp` in the function (image A has no UBSan). It calls no allocator and no runtime routine that charges the
   meter: the post charges 0 and keeps the caller's blocks. The aborts are refuted by the leaf's post (its result and
   its counter bytes are the plain model's, lib/Prog/rp_meter_counter_c.v, the same expressions check_meter computes);
   the report branches by the shadow of f's block, which the walk derives from the block premise (YCbq.v
   range_addressable_of_block, shadow_hull_vis_of_block). *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_meter_counter_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_meter_counter_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_meter's frame (`addi sp, sp, -128` at 0x80340), the at most 0x10 bytes of `andi sp, sp, -32` (0x8037c) below
   it, and the ESTACK its two callees (the stack malloc and the leaf rp_meter_counter) use below the realigned sp. *)
Definition CM_FRAME : Z := 0x80.
Definition CM_ALIGN : Z := 0x10.
Definition CM_STK : Z := CM_FRAME + CM_ALIGN + ESTACK.
(* No allocator event: the class-0 stack malloc and its release record none (YG00.v stack_malloc, stack_free). *)
Definition CM_EV : Z := 0.
(* The fake-frame class (`li a0, 64` at 0x803a8, `jal __asan_stack_malloc_0` at 0x803ac). *)
Definition CM_CID : Z := 0.

Section cm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
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
   the caller's blocks when n > 0 (the fuzz_dup copy); class 0 has a free fake frame. *)
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
