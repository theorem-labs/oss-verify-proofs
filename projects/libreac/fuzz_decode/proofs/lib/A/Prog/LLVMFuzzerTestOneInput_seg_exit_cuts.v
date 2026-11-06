(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, with its module names and addresses changed; 81 of its 150 lines of code are new or changed and 490 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit_cuts: the inner cut points of the exit segment of the image-A walk of
   libreac/fuzz_decode's LLVMFuzzerTestOneInput (llvm_a_exit_stmt, lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), and the
   statements of its six pieces. No stepping here.

   The exit segment runs +0x86c .. +0xa48 (map-code.md section 2, offset = 4 * (DecodeList.v line - 28)):
     +0x86c .. +0x904  the four shadow-checked header checks of the copy (res + 12, res + 13, res + len - 2,
                       res + len - 1) and the abort edge +0x900; the accepted case goes on through +0x904 and the
                       `blez a0` at +0x95c to +0x960 (ex_st_960), the refused case to the scan's entry +0x908
                       (ex_st_908);
     +0x908 .. +0x95c  the scan loop L6 (+0x914 .. +0x940) over the refused upstream buffer, its abort edge +0x958,
                       and the `blez a0` at +0x95c to +0x98c (ex_st_98c);
     +0x960 .. +0x974  check_round_trip (res + 50, upb, nch, 12), return +0x978 (ex_st_978);
     +0x978 .. +0x988  check_braid (res + 50, upb, nch, 12), return +0x98c (ex_st_98c);
     +0x98c .. +0x9a4  free (upb), free (res), the local's two shadow bytes back to 0xf8: llvm_a_st_9a8;
     +0x9a8 .. +0xa48  the teardown and the epilogue, shared with the early return: dec_a_post.
   The pieces are ex_check_stmt, ex_scan_stmt, ex_crt_stmt, ex_braid_stmt, ex_free_stmt and ex_tail_stmt below;
   each takes the subset of llvm_a_exit_stmt's premises it uses, and LLVMFuzzerTestOneInput_seg_exit.v composes them.
   The cut predicates have the shape of the interface's llvm_a_st_* (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v):
   exists fx' ly' S' regs' mem' md', the configuration at the cut pc, the zero rounding mode, dec_a_core, the
   blocks up to permutation, the meter, the three frame registers and what the next piece reads. *)
From Stdlib Require Import ZArith NArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YI00 YI04 YG0v YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require check_braid_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require reac_decode_c reac_upstream_channels_c
  reac_upstream_decode_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
Module CDec := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_c.
Module CChan := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_c.
Module CUp := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_decode_c.
Module LCheckBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.check_braid_cg.

Section cuts. Context {rc : YM05.RunCeil}.
(* The Variables of LLVMFuzzerTestOneInput_segs.v's Section seg, in its order. *)
Local Abbreviation tfib_sink_head := dec_A_sink_head.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).
Local Abbreviation BASE cx := (dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL
  RLO RHI cx).

(* The upstream buffer's length (malloc #3 at +0x7c0) and the blocks of the body of the segment. *)
Definition ex_uolen (cx : dctx) : Z := dec_a_uolen (CChan.upstream_result (dec_a_len (d_n cx))).
Definition ex_blocks (cx : dctx) (res upb : Z) : list (Z * Z) :=
  ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++ [(upb, ex_uolen cx)].

(* +0x960: the `blez a0` at +0x95c not taken, so the third reac_upstream_decode accepted the copy (a0 = 12); the
   header checks and the scan have run and written nothing. s2 is still the shadow base; check_round_trip's
   arguments are loaded at +0x960 .. +0x970 (64(s1) = res + 50 into s2). *)
Definition ex_st_960 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res upb : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x960)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core B cx ly' S' W' regs' mem' md' dec_ev_86c /\
    Permutation (ablocks B ly' S') (ex_blocks cx res upb) /\
    4096 <= res /\ 4096 <= upb /\
    mo_le MT (d_S cx) S' (dec_spent_86c MT (d_n cx)) /\ mo_ok MT S' (dec_rest_86c MT) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 22 = w64 (CChan.upstream_result (dec_a_len (d_n cx))) /\
    YK11.getr regs' 23 = w64 upb /\
    CUp.up_ok res upb (dec_a_len (d_n cx)) (d_body cx) = true /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    garr8 segs (rd W' mem') upb
      (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) (CUp.up_nch (dec_a_len (d_n cx))) 12)) /\
    dec_a_fsh cx (aview segs (w_H W') mem') 0 4 /\
    dec_a_slot cx (aview segs (w_H W') mem') 64 (res + 50).

(* +0x978: the return of check_round_trip #2 (+0x974). Its six events and its cost are spent; s2 holds res + 50
   (ld s2, 64(s1) at +0x964, callee-saved across the call). *)
Definition ex_st_978 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res upb : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x978)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core B cx ly' S' W' regs' mem' md' (dec_ev_86c + DEC_CRT_EV) /\
    Permutation (ablocks B ly' S') (ex_blocks cx res upb) /\
    4096 <= res /\ 4096 <= upb /\
    mo_le MT (d_S cx) S' (dec_spent_86c MT (d_n cx) + dec_crt_cost_max MT) /\
    mo_ok MT S' (mo_free MT + mo_free MT) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 18 = w64 (res + 50) /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 22 = w64 (CChan.upstream_result (dec_a_len (d_n cx))) /\
    YK11.getr regs' 23 = w64 upb /\
    CUp.up_ok res upb (dec_a_len (d_n cx)) (d_body cx) = true /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    garr8 segs (rd W' mem') upb
      (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) (CUp.up_nch (dec_a_len (d_n cx))) 12)) /\
    dec_a_fsh cx (aview segs (w_H W') mem') 0 4.

(* +0x908: the `bgez a0` at +0x904 not taken, so the third reac_upstream_decode refused (a0 = -1), and the header
   checks agreed with it (`bne a0, a2` at +0x900 not taken). The scan loop L6 (+0x914 .. +0x940) reads the
   upstream buffer, which still holds the 0xa5 fill, with a shadow check per byte (slow path +0x948 .. +0x954). *)
Definition ex_st_908 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res upb : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x908)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core B cx ly' S' W' regs' mem' md' dec_ev_86c /\
    Permutation (ablocks B ly' S') (ex_blocks cx res upb) /\
    4096 <= res /\ 4096 <= upb /\
    mo_le MT (d_S cx) S' (dec_spent_86c MT (d_n cx)) /\ mo_ok MT S' (dec_rest_86c MT) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 10 = w64 (-1) /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 23 = w64 upb /\
    YK11.getr regs' 24 = w64 (ex_uolen cx) /\
    dec_a_filled W' mem' upb (ex_uolen cx) /\
    dec_a_fsh cx (aview segs (w_H W') mem') 0 4.

(* +0x98c: `mv a0, s7` before free #2, reached from the refused case (+0x95c) and from check_braid's return (+0x988).
   At most check_round_trip's events and cost are spent beyond +0x86c's; what is left pays the two frees. *)
Definition ex_st_98c (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (k res upb : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x98c)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core B cx ly' S' W' regs' mem' md' k /\ k <= dec_ev_86c + DEC_CRT_EV /\
    Permutation (ablocks B ly' S') (ex_blocks cx res upb) /\
    4096 <= res /\ 4096 <= upb /\
    mo_le MT (d_S cx) S' (dec_spent_86c MT (d_n cx) + dec_crt_cost_max MT) /\
    mo_ok MT S' (mo_free MT + mo_free MT) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 23 = w64 upb /\
    dec_a_fsh cx (aview segs (w_H W') mem') 0 4.

(* ---- the six pieces ---- *)

(* +0x86c .. +0x904 and, when the decode was accepted, +0x904 .. +0x95c: the four header checks with their shadow
   checks (slow paths +0xa8c, +0xae8, +0xb24, +0xb44 never taken), the abort edge +0x900 refuted, then +0x960 or the
   scan's entry +0x908. *)
Definition ex_check_stmt : Prop :=
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    BASE cx -> dec_a_rom cx -> llvm_a_st_86c B MT cx W' c' ->
    SRr segs W' c' (fun W2 c2 => ex_st_960 cx W2 c2 \/ ex_st_908 cx W2 c2).

(* +0x908 .. +0x95c: the scan loop L6 over the refused buffer, its report (+0x954) and abort (+0x958) edges refuted,
   and the `blez a0` at +0x95c taken to +0x98c. *)
Definition ex_scan_stmt : Prop :=
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    BASE cx -> dec_a_rom cx -> ex_st_908 cx W' c' -> SRr segs W' c' (ex_st_98c cx).

(* +0x960 .. +0x974: check_round_trip #2 by its contract; its read-only view premise (dec_rom_view_rd) comes from the
   entry's rom_view through the journal's image clause and dec_ro_rd_scoped. *)
Definition ex_crt_stmt : Prop :=
  dec_llvmf_utraces RA_LLVMF B -> dec_crt_cells B ->
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  (forall fx : YK11.FPState,
     @dec_check_round_trip_cg fx rc B MT (decode_sigma DS_check_round_trip) (CTX_check_round_trip RA_LLVMF)) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    BASE cx -> dec_a_rom cx -> ex_st_960 cx W' c' -> SRr segs W' c' (ex_st_978 cx).

(* +0x978 .. +0x988: check_braid #2 by its leaf contract. *)
Definition ex_braid_stmt : Prop :=
  dec_crt_cells B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    BASE cx -> dec_a_rom cx -> ex_st_978 cx W' c' -> SRr segs W' c' (ex_st_98c cx).

(* +0x98c .. +0x9a4: free #2, free #3, the local re-poisoned. *)
Definition ex_free_stmt : Prop :=
  pc_wrap_free (as_code B) = decode_sigma DS___interceptor_trampoline_free ->
  dec_llvmf_utraces RA_LLVMF B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @afree04_rule fx rc tfib_sink_head segs B MT) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    BASE cx -> dec_a_rom cx -> ex_st_98c cx W' c' -> SRr segs W' c' (llvm_a_st_9a8 B MT cx).

(* +0x9a8 .. +0xa48: the teardown and the epilogue, from the join of the two returns. *)
Definition ex_tail_stmt : Prop :=
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  (forall nn, 0 <= nn -> dec_llvmf_cost MT nn <= XL nn) ->
  astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W mem) md -> asink_none segs tfib_K (rd W' mem') md') ->
  (forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W mem) M -> ameta_inv segs tfib_K ly' (rd W' mem') M) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    BASE cx -> dec_a_rom cx -> llvm_a_st_9a8 B MT cx W' c' ->
    SRr segs W' c' (dec_a_post asink_syms tfib_K asink_none ameta_inv RA_LLVMF B MT XL cx).

End cuts.
