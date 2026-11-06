(* Modified by Theorem Labs: copied from this unit's lib/A/Prog/check_clamp_cg.v (commit ba35beec1417; itself in the caller-journal form of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v at recipes commit 88154566652a; cgif_file_fuzzer lib/A/ACey.v trfc_specX, lib/YC20.v tlzw_spec) for reac-repacer/fuzz_uci's image B: the B core's names (lib/B/YB1v.v, lib/B/YE2k.v, lib/B/YCbq.v / YC5d.v), the listing modules lib/B/Prog's, every address in the comments measured on fuzz_uci.asan-ubsan, and ONE premise more than image A's text, image B's UBSan premise `pin mod 4 = 0` (the trap 0x7fa74 `andi a0, s3, 3` / 0x7fa78 `bne a0, zero, 0x7fc78`, unimp at 0x7fc78, s3 = pin), in the shape of the UBSan image's lib/U/Prog/check_clamp_c.v (its trap 0x130b0 / 0x130b4, premise bv_unsigned a0 mod 4 = 0). *)
(* check_clamp_cg: the ASan walk contract of check_clamp (fuzz_uci.asan-ubsan 0x7f950 = uci_sigma US_check_clamp,
   AF_check_clamp = 0x668 of lib/B/Prog/UciPList.v), as STATEMENTS only (no proof).

   The C (fuzz_uci.c check_clamp): copy *in (a struct rp_hot of five ints, 20 bytes) to a local, rp_hot_clamp (&local,
   margin_max), and abort unless each field is held (lib/Spec/UciModel.v clamp_prefill .. clamp_servo).
   The code (DIS of image B):
     +0x0   `addi sp, sp, -0x60`, saves; +0x30 `addi s0, sp, 0x60`; +0x34 `andi sp, sp, -0x20` (realigns sp: at most 0x10
            more below entry - 0x60, and `sd s7, 8(s1)` at +0x98 writes there);
     +0x40..+0x58 reads __asan_option_detect_stack_use_after_return through its GOT word (0x97180 -> 0x9f100) and the
            shadow base through 0x97128; `beqz a2` at +0x5c skips the fake stack when the flag word is 0 (the flag is 1:
            uci_cells row 6);
     +0x64  `jal __asan_stack_malloc_1` (0x3c1b8) with a0 = 0x60 (+0x60): the class-1 fake frame (64 << 1 = 128 bytes);
            the local is at frame + 0x20; +0xc4..+0x104 write its frame header and shadow;
     +0x114 `jal __asan_memcpy` (0x50674) with a0 = frame + 0x20, a1 = in, a2 = 0x14;
     +0x120 `jal rp_hot_clamp` (0x7fd38) with a0 = frame + 0x20, a1 = margin_max;
     +0x124 `andi a0, s3, 3` / +0x128 `bne a0, zero` to `unimp` at +0x328: UBSan's alignment check of in (s3 = in);
     then five `lw` of the fields of *in, each guarded by __asan_report_load4 (+0x338 .. +0x37c), compared with the
            local's; a mismatch branches to __asan_handle_no_return / abort at +0x320 / +0x324;
     +0x24c..+0x264 poison the local's shadow (0xf8) and retire the frame header; on the fake-frame path +0x26c..+0x2ac
            write 0xf5 (stack-after-return) into the frame's 16 shadow bytes and `sb zero, 0(a0)` at +0x2b4 clears the
            frame's flag byte (a0 = the word at frame + 0x78 = frame + 128 - 8, read at +0x2b0): the fake frame is
            released (YG0d.v astack_free_law); on the frame = 0 path +0x2bc..+0x2e8 zero the frame's shadow.
   With the fake frame obtained (the stack-malloc premise count_cid 1 (frames Sc) < fs_frames 1 and
   stack_malloc_progressP), the dynamic-alloca path (+0x7c..+0x94, which probes sp - 4096) is never taken.
   The struct *in is the caller's (LLVMFuzzerTestOneInput's frame, sp + 8, on the real stack, outside this call's stack
   window): the walk reads it through the image view and its shadow (range_addressable, shadow_hull_vis), which the
   caller proves. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Cells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import UciPSyms UciPAddr UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require rp_hot_clamp_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_hot_clamp_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module LHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.rp_hot_clamp_cg.
Module PHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_hot_clamp_c.
Module LC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib.Cells.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_clamp's frame (`addi sp, sp, -0x60` at US_check_clamp), the at most 0x10 bytes of `andi sp, sp, -0x20` below
   it, and the ESTACK its three callees (the stack malloc, __asan_memcpy, the leaf rp_hot_clamp) use below the realigned
   sp. *)
Definition CC_FRAME : Z := 0x60.
Definition CC_ALIGN : Z := 0x10.
Definition CC_STK : Z := CC_FRAME + CC_ALIGN + ESTACK.
(* No allocator event: the class-1 stack malloc and its release record none (YG00.v stack_malloc, stack_free). *)
Definition CC_EV : Z := 0.
(* The fake-frame class (`addi a0, zero, 0x60` at +0x60, `jal __asan_stack_malloc_1` at +0x64). *)
Definition CC_CID : Z := 1.

Section cc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* The 20 bytes of the struct, as the image view reads them (lib/Prog/rp_hot_clamp_c.v hot_cells: five little-endian
   int32 fields). *)
Definition uci_hot_bytes (p : rp_hot) : list Z :=
  map (fun b : byte => bv_unsigned b) (LC.cells_bytes (PHC.hot_cells p)).

(* What a call leaves: the caller's journal extended by CC_EV events, callee-saved registers kept, the fake frame
   released (frames S2 = frames Sc), the caller's blocks exactly, every byte outside the call's stack window kept
   (YCbq.v acall_kept with no written range), and no meter charge. *)
Definition uci_cc_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CC_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CC_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The contract at entry address a, in the caller-journal form. pin (a0) holds the 20 bytes of a struct p of ints, on
   the caller's side of this call's sp, visible and addressable in the shadow; mm (a1) is margin_max, an int >= 0;
   class 1 has a free fake frame. *)
Definition uci_check_clamp_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (pin mm : Z) (p : rp_hot),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 pin -> YK11.getr regs 11 = w64 mm ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CC_STK -> spZ regs <= sp0 ->
    PHC.hot_int p -> 0 <= mm <= INT_MAX ->
    (* Image B's UBSan premise: 0x7fa74 `andi a0, s3, 3` / 0x7fa78 `bne a0, zero, 0x7fc78` trap (unimp at 0x7fc78) on a
       misaligned in (s3 = pin); image A's text lacks it. The `<` of :105 is image A's T0.6 fix, the same in both. *)
    pin mod 4 = 0 ->
    spZ regs <= pin -> pin + PHC.RP_HOT_SIZE < sp0 ->
    garr8 segs (mrestrict (w_H W) memc) pin (uci_hot_bytes p) ->
    range_addressable (aview segs (w_H W) memc) SHADOW_OFF pin PHC.RP_HOT_SIZE ->
    shadow_hull_vis (aview segs (w_H W) memc) pin PHC.RP_HOT_SIZE ->
    count_cid CC_CID (frames Sc) < fs_frames CC_CID ->
    st_nev S + k + CC_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (uci_cc_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The statement the walk will prove: the class-1 stack-malloc entry of the record, the runtime cells, the allocator,
   meter and fake-stack laws (the meter's fs laws too: the fake frame changes the state's st_fs only, YG00.v
   stack_malloc / stack_free, and the post charges 0), and the contracts of __asan_stack_malloc_1, __asan_memcpy and the
   leaf rp_hot_clamp give the contract at US_check_clamp. *)
Definition uci_check_clamp_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) CC_CID = uci_sigma US___asan_stack_malloc_1 ->
  uci_cells B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B CC_CID) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (uci_sigma US___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @uci_leaf_wr_at rc B (@LHC.uci_rp_hot_clamp_cg) fx') ->
  uci_check_clamp_cg (uci_sigma US_check_clamp).
End cc.
