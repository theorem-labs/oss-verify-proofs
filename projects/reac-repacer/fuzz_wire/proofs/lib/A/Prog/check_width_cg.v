(* Modified by Theorem Labs: reac-repacer/fuzz_wire's check_width in the caller-journal form of reac-repacer/fuzz_uci's lib/A/Prog/check_clamp_cg.v and check_value_cg.v (the form of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v, origin/ossv/recipes 88154566652a), at this unit's core names and image A. *)
(* check_width_cg: the ASan walk contract of check_width (fuzz_wire.asan 0x80708 = wire_sigma WS_check_width), as
   STATEMENTS only (no proof).

   The C (fuzz_wire.c check_width, lib/Prog/check_width_c.v): abort unless rp_frame_channels (n) is w_width (n), the
   frame law's table walk of fuzz.h, inlined; then abort unless rp_frame_channels (-1 - n) is -1.
   The code (DIS of image A, 0x80708, 0x74 bytes):
     +0x0   `addi sp, sp, -16`, saves ra and s0; +0xc `mv s0, a0`;
     +0x10  `jal rp_frame_channels` (0x8136c) with a0 = n;
     +0x14..+0x44 the inlined w_width walk (no memory access); +0x48 `bne a0, a2` to the abort;
     +0x4c  `not a0, s0`; +0x50 `jal rp_frame_channels` with a0 = -1 - n; +0x58 `bne a0, a1` to the abort;
     +0x5c..+0x68 restores ra and s0 and returns;
     +0x6c  `jal __asan_handle_no_return`, +0x70 `jal abort`: the abort path.
   It makes no ASan runtime call on its normal path, has no shadow check, and allocates nothing. The two aborts are
   refuted by lib/A/Prog/rp_frame_channels_c.v rp_frame_channels_model: for 0 <= n <= W_RECV_MAX it is the inlined walk's
   value, and it is -1 at every negative length. Its one callee is the leaf rp_frame_channels
   (lib/A/Prog/rp_frame_channels_cg.v), which writes no memory outside its own frame and reads three 8-byte .rodata
   constants: 0x10300 and 0x103b0 through the read-only view (WireCg.v WIRE_RO_RD, wire_rom_view_rd), and 0x10328, an
   owned static of the core (Tfib_owned_static), as a constant cell of the record (WireCg.v wire_cells). *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_frame_channels_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LRFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_frame_channels_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_width's frame (`addi sp, sp, -16` at WS_check_width) and the ESTACK its leaf callee uses below its sp. *)
Definition CW_FRAME : Z := 0x10.
Definition CW_STK : Z := CW_FRAME + ESTACK.
(* No allocator event. *)
Definition CW_EV : Z := 0.
(* The harness cuts the input to W_RECV_MAX bytes before it calls check_width (lib/Prog/check_width_c.v). *)
Definition CW_N_MAX : Z := 1600.

Section cw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: the caller's journal extended by CW_EV events, callee-saved registers kept, the caller's frames
   and blocks exactly, every byte outside the call's stack window kept (YCbq.v acall_kept with no written range), and
   no meter charge. *)
Definition wire_cw_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CW_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CW_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The contract at entry address a, in the caller-journal form. n (a0) is the input length, at most W_RECV_MAX; the
   two read-only constants its leaf callee reads are the image's (wire_rom_view_rd). *)
Definition wire_check_width_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (n : Z),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 n ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CW_STK -> spZ regs <= sp0 ->
    0 <= n <= CW_N_MAX ->
    wire_rom_view_rd W memc ->
    st_nev S + k + CW_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (wire_cw_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The statement the walk will prove: the runtime and constant cells of the record (0x10328 among them), the allocator
   and meter laws, the read-only reads of the record (the two constants unowned, errno outside the read-only image), and
   the leaf contract of rp_frame_channels (a non-writing leaf, taken through wire_leaf_at) give the contract at
   WS_check_width. *)
Definition wire_check_width_holds_stmt : Prop :=
  wire_cells B ->
  wire_ro_rd_unowned B -> wire_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LRFC.wire_rp_frame_channels_cg) fx') ->
  wire_check_width_cg (wire_sigma WS_check_width).
End cw.
