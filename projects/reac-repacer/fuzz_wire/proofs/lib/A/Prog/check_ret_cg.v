(* The caller-journal form of reac-repacer/fuzz_wire's check_ret in image A, in the form of reac-repacer/fuzz_uci's lib/A/Prog/check_clamp_cg.v (a check that takes a leaf callee through the kit's leaf wrapper), with the heap-buffer premises of its lib/A/Prog/check_value_cg.v. *)
(* check_ret_cg: the ASan walk contract of check_ret (fuzz_wire.asan 0x80154 = wire_sigma WS_check_ret), as STATEMENTS
   only (no proof).

   The C (fuzz_wire.c:72-84 check_ret): want = n >= 14 && w_is_reac(f, 12) (inlined), abort unless
   rp_ret_accept(f, n) == want.
   The code (DIS of image A, 0x80154 .. 0x801fc):
     +0x0   `addi sp, sp, -0x10`, +0x4 `sd ra, 8(sp)`, +0x8 `sd s0, 0(sp)` (frame 0x10; the two saves are its only
            stores, so it writes nothing outside its frame);
     +0xc   `li a2, 14`, +0x10 `bltu a1, a2` to +0x64 (`li s0, 0`): want = 0 when n < 14, no frame byte read;
     +0x14  `auipc a2, 0x18`, +0x18 `ld a2, 0x680(a2)`: the shadow base's GOT word (0x987e8), +0x1c `ld a3, 0(a2)`:
            the shadow base cell (0xa0778);
     +0x20..+0x30 the shadow byte of f + 12, `bnez` to +0x88 (the partial-granule test, then `jal __asan_report_load1`
            at +0x94); +0x34 `lbu` f[12]; +0x3c `bne` 0x88 to +0x64;
     +0x40..+0x50 the shadow byte of f + 13, `bnez` to +0x98 (then `jal __asan_report_load1` at +0xa4); +0x54 `lbu`
            f[13]; +0x58 `addi -25`, +0x5c `seqz s0` (s0 = want);
     +0x68  `jal rp_ret_accept` (0x80fe0) with a0 = f, a1 = n as at entry (nothing before writes a0 or a1);
     +0x6c  `bne a0, s0` to +0x80 `jal __asan_handle_no_return`, +0x84 `jal abort`;
     +0x70..+0x7c restores ra and s0 and returns (`ret` at +0x7c, its one return).
   The two report branches are refuted by f's block (its n bytes are addressable in the shadow while the block is
   live: the block premise below); the abort by rp_ret_accept's leaf contract (lib/A/Prog/rp_ret_accept_cg.v: a0 =
   lib/Prog/rp_ret_accept_c.v ret_accept_result of n and the frame bytes, which is want). It allocates nothing, has no
   fake frame and calls no runtime entry but the report sinks and the refuted abort path. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_ret_accept_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_ret_accept_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_ret's frame (`addi sp, sp, -0x10` at WS_check_ret) and the ESTACK its one callee, the leaf rp_ret_accept,
   uses below its sp (the kit's ecall_pre). No `andi sp` realignment: no alignment slack. *)
Definition CR_FRAME : Z := 0x10.
Definition CR_STK : Z := CR_FRAME + ESTACK.
(* No allocator event: it calls neither the allocator nor the fake stack. *)
Definition CR_EV : Z := 0.

Section cr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: the caller's journal extended by CR_EV events, callee-saved registers kept, the caller's frames
   and blocks exactly, every byte outside the call's stack window kept (YCbq.v acall_kept with no written range: the
   frame f's n bytes are intact for the next check), and no meter charge. *)
Definition wire_cr_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CR_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CR_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The contract at entry address a, in the caller-journal form. f (a0) holds the n (a1) frame bytes bs; when n > 0
   they lie in one block of the caller's (fuzz_dup's heap copy of the frame), visible through the image view. *)
Definition wire_check_ret_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (f n : Z) (bs : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 n ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CR_STK -> spZ regs <= sp0 ->
    (* n is a size_t, so any 64-bit value; the check allocates nothing by n, so no smaller bound is needed. No rom_view
       premise: the check reads no .rodata, its only data reference is the shadow-base GOT word. *)
    0 <= n < 2 ^ 64 -> Z.of_nat (length bs) = n ->
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA) ->
    garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs) ->
    st_nev S + k + CR_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (wire_cr_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The statement the walk will prove: the runtime cells (the shadow base and its GOT word, read at +0x18 / +0x1c and
   by the leaf), the allocator and meter laws, and the leaf contract of rp_ret_accept read through the non-writing
   wrapper (it writes no byte outside its frame) give the contract at WS_check_ret. *)
Definition wire_check_ret_holds_stmt : Prop :=
  wire_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LRA.wire_rp_ret_accept_cg) fx') ->
  wire_check_ret_cg (wire_sigma WS_check_ret).
End cr.
