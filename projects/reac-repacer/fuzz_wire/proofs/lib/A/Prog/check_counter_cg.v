(* The caller-journal form of reac-repacer/fuzz_wire's check_counter in image A, in the form of reac-repacer/fuzz_uci's lib/A/Prog/check_clamp_cg.v (a check that takes a leaf callee through the kit's leaf wrapper), with the heap-buffer premises of its lib/A/Prog/check_value_cg.v. *)
(* check_counter_cg: the ASan walk contract of check_counter (fuzz_wire.asan 0x80660 = wire_sigma WS_check_counter),
   as STATEMENTS only (no proof).

   The C (fuzz_wire.c:133-144 check_counter): return when n < 18; abort unless
   rp_counter(f) == (unsigned)(f[14] | f[15] << 8).
   The code (DIS of image A, 0x80660 .. 0x80708):
     +0x0   `addi sp, sp, -0x20`, +0x4 `sd ra, 24(sp)`, +0x8 `sd s0, 16(sp)`, +0xc `sd s1, 8(sp)` (frame 0x20; the
            three saves are its only stores, so it writes nothing outside its frame);
     +0x10  `li a2, 18`, +0x14 `bltu a1, a2` to +0x6c: n < 18 returns before any other load and before the call;
     +0x18  `mv s0, a0` (s0 = f); +0x1c `auipc a0, 0x18`, +0x20 `ld a0, 0x16c(a0)`: the shadow base's GOT word
            (0x987e8), +0x24 `ld s1, 0(a0)`: the shadow base cell (0xa0778), kept in s1 across the call;
     +0x2c  `jal rp_counter` (0x812f4) with a0 = f (+0x28 `mv a0, s0`);
     +0x30..+0x40 the shadow byte of f + 14, `bnez` to +0x80 (the partial-granule test, then
            `jal __asan_report_load1` at +0x8c);
     +0x44..+0x50 the shadow byte of f + 15; +0x54 `lbu a2, 14(s0)` = f[14]; +0x58 `bnez` to +0x90 (then
            `jal __asan_report_load1` at +0x9c); +0x5c `lbu a1, 0(a1)` = f[15]; +0x60 `slli a1, a1, 8`, +0x64 `or`;
     +0x68  `bne a0, a1` to +0xa0 `jal __asan_handle_no_return`, +0xa4 `jal abort`;
     +0x6c..+0x7c restores ra, s0 and s1 and returns (`ret` at +0x7c, its one return, also the n < 18 path).
   The two report branches are refuted by f's block (its n bytes are addressable in the shadow while the block is
   live: the block premise below; rp_counter writes no byte outside its frame, so the shadow it leaves is the
   caller's); the abort by rp_counter's leaf contract (lib/A/Prog/rp_counter_cg.v: a0 = lib/Prog/rp_counter_c.v
   counter_result of the frame bytes, which is f[14] | f[15] << 8). It allocates nothing, has no fake frame and
   calls no runtime entry but the report sinks and the refuted abort path. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_counter_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_counter_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_counter's frame (`addi sp, sp, -0x20` at WS_check_counter) and the ESTACK its one callee, the leaf
   rp_counter, uses below its sp (the kit's ecall_pre). No `andi sp` realignment: no alignment slack. *)
Definition CK_FRAME : Z := 0x20.
Definition CK_STK : Z := CK_FRAME + ESTACK.
(* No allocator event: it calls neither the allocator nor the fake stack. *)
Definition CK_EV : Z := 0.

Section ck. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: the caller's journal extended by CK_EV events, callee-saved registers kept, the caller's frames
   and blocks exactly, every byte outside the call's stack window kept (YCbq.v acall_kept with no written range: the
   frame f's n bytes are intact for the next check), and no meter charge. *)
Definition wire_ck_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CK_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CK_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The contract at entry address a, in the caller-journal form. f (a0) holds the n (a1) frame bytes bs; when n > 0
   they lie in one block of the caller's (fuzz_dup's heap copy of the frame), visible through the image view. *)
Definition wire_check_counter_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (f n : Z) (bs : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 n ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CK_STK -> spZ regs <= sp0 ->
    (* n is a size_t, so any 64-bit value; the check allocates nothing by n, so no smaller bound is needed. No rom_view
       premise: the check reads no .rodata, its only data reference is the shadow-base GOT word. *)
    0 <= n < 2 ^ 64 -> Z.of_nat (length bs) = n ->
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA) ->
    garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs) ->
    st_nev S + k + CK_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (wire_ck_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The statement the walk will prove: the runtime cells (the shadow base and its GOT word, read at +0x20 / +0x24 and
   by the leaf), the allocator and meter laws, and the leaf contract of rp_counter read through the non-writing
   wrapper (it writes no byte outside its frame) give the contract at WS_check_counter. *)
Definition wire_check_counter_holds_stmt : Prop :=
  wire_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LRC.wire_rp_counter_cg) fx') ->
  wire_check_counter_cg (wire_sigma WS_check_counter).
End ck.
