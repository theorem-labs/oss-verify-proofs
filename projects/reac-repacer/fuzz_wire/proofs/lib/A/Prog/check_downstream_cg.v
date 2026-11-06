(* check_downstream_cg: the ASan walk contract of check_downstream (fuzz_wire.asan 0x801fc = wire_sigma
   WS_check_downstream), as STATEMENTS only (no proof).
   The C (fuzz_wire.c:86-98): `want = n >= 18 && (w_is_reac(f, 12) || (w_is_tag(f) && w_is_reac(f, 16)))`, then
   `if (rp_ds_accept(f, n) != want) abort();`. f is LLVMFuzzerTestOneInput's fuzz_dup copy of the frame (a heap block
   of max(n, 1) bytes, fuzz_wire.c:263), n <= W_RECV_MAX = 1600 (fuzz_wire.c:261-262).
   The code (DIS of image A, 81 words):
     +0x0   `addi sp, sp, -0x10`, +0x4 / +0x8 `sd ra, 8(sp)` / `sd s0, 0(sp)` (frame [sp - 16, sp)); it stores nothing
            else;
     +0x10  `bltu a1, a2, +0xd0` (a2 = 18): n < 18 sets s0 = 0 (+0xd0) and reads no frame byte;
     +0x14 / +0x18 `auipc a2, 0x18` / `ld a2, 0x5d8(a2)` loads the GOT word of the shadow base, +0x1c `ld a3, 0(a2)`
            the shadow base;
     then the frame bytes f[12] (+0x34), f[13] (+0x5c, +0x84), f[16] (+0xa0) and f[17] (+0xc0), each after a load
            of its shadow byte (+0x2c, +0x54, +0x7c, +0x98, +0xb8) whose non-zero value branches to
            __asan_report_load1 (`jal` at +0x100, +0x110, +0x120, +0x130, +0x140) unless the granule holds the
            byte; s0 = want;
     +0xd4  `jal rp_ds_accept` (0x8106c) with a0 = f, a1 = n;
     +0xd8  `bne a0, s0, +0xec` to __asan_handle_no_return / abort (`jal` at +0xec / +0xf0);
     +0xdc .. +0xe8 the epilogue and `ret`.
   It calls nothing else: no allocator call and no fake stack (its frame is the real stack's), so it records no
   allocator event and charges the meter nothing. The report branches are refuted by the shadow of f's block (f lies
   inside one of the caller's blocks when n > 0); the abort by rp_ds_accept's post (a0 = ds_accept_result n bs of the
   released lib/Prog/rp_ds_accept_c.v), which is the want the harness computes on each of its paths.
   f is a heap block, not a caller stack object, so no `pin + size < sp0` bound applies; the real-stack bounds are the
   template's `sp0 - STK <= spZ regs - CDS_STK` and `spZ regs <= sp0`. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_ds_accept_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_ds_accept_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_downstream's frame (`addi sp, sp, -0x10` at WS_check_downstream) and the ESTACK its one callee, the leaf
   rp_ds_accept, may use below its sp (LeafCgKit.v ecall_pre). *)
Definition CDS_FRAME : Z := 0x10.
Definition CDS_STK : Z := CDS_FRAME + ESTACK.
(* No allocator event: it calls no allocator. *)
Definition CDS_EV : Z := 0.
(* The frame's length: at most the daemon's receive buffer, W_RECV_MAX (fuzz/fuzz.h:35, fuzz_wire.c:261-262). *)
Definition CDS_N_MAX : Z := 1600.

Section cds. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: the caller's journal extended by CDS_EV events, callee-saved registers kept, no fake frame
   added, the caller's blocks exactly, every byte outside the call's stack window kept (YCbq.v acall_kept with no
   written range: f's n bytes too, for the checks after it), and no meter charge. *)
Definition wire_cds_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CDS_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CDS_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The contract at entry address a, in the caller-journal form, without a call context. f (a0) holds the n (a1)
   frame bytes bs, inside one of the caller's blocks when n > 0. *)
Definition wire_check_downstream_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (f n : Z) (bs : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 n ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CDS_STK -> spZ regs <= sp0 ->
    0 <= n <= CDS_N_MAX -> Z.of_nat (length bs) = n ->
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA) ->
    garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs) ->
    st_nev S + k + CDS_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (wire_cds_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The statement the walk will prove: the runtime cells (the shadow base and its GOT word), the allocator and meter
   laws, and the leaf contract of rp_ds_accept (lib/A/Prog/rp_ds_accept_cg.v, through WireCg.v wire_leaf_at: it writes
   no byte outside its own frame) give the contract at WS_check_downstream. *)
Definition wire_check_downstream_holds_stmt : Prop :=
  wire_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LDA.wire_rp_ds_accept_cg) fx') ->
  wire_check_downstream_cg (wire_sigma WS_check_downstream).
End cds.
