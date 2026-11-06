(* check_forward_cg: the ASan walk contract of check_forward (fuzz_wire.asan-ubsan 0x7fda4 = wire_sigma
   WS_check_forward), as STATEMENTS only (no proof).

   The C (fuzz_wire.c:50-70 check_forward): got = rp_fwd_class (f, n, bcast); want = RP_FWD_DROP, and when n >= 18,
   f[12] = 0x88, f[13] = 0x19 and (!bcast || f[0] == 0xff), want = (f[16] == 0 && f[17] == 0) ? RP_FWD_AUDIO :
   RP_FWD_CTRL; abort unless got = want. want is lib/Prog/rp_fwd_class_c.v fwd_class_result n bcast of the n bytes,
   the value the leaf post of rp_fwd_class puts in a0, so the abort is unreachable.
   The code (DIS of image B; 0x7fda4, 0x188 bytes):
     +0x0   `addi sp, sp, -0x30` (frame 0x30); +0x4 .. +0x14 save ra, s0 .. s3; s1 = bcast, s2 = n, s0 = f;
     +0x20 .. +0x28 load the shadow base through its GOT word (0x98878 -> 0xa07f8) into s3;
     +0x34  `jal rp_fwd_class` (0x80d9c) with a0 = f, a1 = n, a2 = bcast: the leaf lib/B/Prog/rp_fwd_class_cg.v;
     +0x3c  `bltu s2, a1` (a1 = 18) skips every read of f when n < 18 (want = 0);
     then f[12], f[13], f[0] (only when bcast <> 0: `beqz s1` at +0x90), f[16], f[17], each `lbu` guarded by its
            shadow byte and __asan_report_load1 (0x57e5c; calls at +0x144, +0x154, +0x164, +0x174, +0x184), and
            UBSan's pointer-overflow checks of f + 12, f + 13, f + 16, f + 17 (+0x44, +0x6c, +0xd8, +0xfc) to `unimp`
            at +0x134;
     +0xb4  `bne a0, a1` (got, want) to __asan_handle_no_return / abort (+0x12c / +0x130); otherwise it restores
            ra, s0 .. s3 and returns.
   It stores to its own frame only (and the leaf to the leaf's), so every byte outside the call's stack window is
   kept (acall_kept with no written range): the checks after it read the same n bytes of f.
   f is LLVMFuzzerTestOneInput's fuzz_dup copy (fuzz_wire.c:263): the malloc trampoline's block of max (n, 1) bytes
   (`jal` at 0x7fc7c, `mv s0, a0` at 0x7fc84), passed at 0x7fcb4 with n = min (size - 1, 1600) (0x7fc5c .. 0x7fc68)
   and bcast = data[0] & 1 (`andi s5, s2, 1` at 0x7fc8c). The block premise (f inside one of the caller's blocks
   when n > 0) refutes every report and every wrap, as check_value_cg.v's does for its reply; f is no stack object,
   so no `< sp0` bound is stated. *)
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
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_fwd_class_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_fwd_class_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_forward's own frame (`addi sp, sp, -0x30` at WS_check_forward) and the ESTACK its leaf callee rp_fwd_class
   uses below its sp. *)
Definition CF_FRAME : Z := 0x30.
Definition CF_STK : Z := CF_FRAME + ESTACK.
(* No allocator event: it allocates and frees nothing. *)
Definition CF_EV : Z := 0.
(* n is at most the 1600 bytes of the daemon's receive buffer (LLVMFuzzerTestOneInput's `addi a0, zero, 0x640` /
   `bltu s6, a0` / `addi s1, zero, 0x640` at 0x7fc5c .. 0x7fc68). *)
Definition CF_N_MAX : Z := 1600.

Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: the caller's journal extended by CF_EV events, callee-saved registers kept, the caller's frames
   and blocks exactly, every byte outside the call's stack window kept (YCbq.v acall_kept with no written range), and
   no meter charge. *)
Definition wire_cf_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CF_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CF_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The contract at entry address a, in the caller-journal form. f (a0) holds the n (a1) bytes bs, visible, inside one
   of the caller's blocks when n > 0; bcast (a2) is 0 or 1. *)
Definition wire_check_forward_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (f n bc : Z) (bs : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 n -> YK11.getr regs 12 = w64 bc ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CF_STK -> spZ regs <= sp0 ->
    0 <= n <= CF_N_MAX -> Z.of_nat (length bs) = n -> 0 <= bc <= 1 ->
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA) ->
    garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs) ->
    st_nev S + k + CF_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (wire_cf_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The statement the walk will prove: the runtime cells (the shadow base and its GOT word, read at +0x24 / +0x28 and
   by the leaf; the leaf's asan_cells), the allocator and meter laws, and the leaf contract of rp_fwd_class give the
   contract at WS_check_forward. *)
Definition wire_check_forward_holds_stmt : Prop :=
  wire_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LFC.wire_rp_fwd_class_cg) fx') ->
  wire_check_forward_cg (wire_sigma WS_check_forward).
End cf.
