(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the interface of the image-A walk of reac-repacer/fuzz_uci's LLVMFuzzerTestOneInput, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v (the context record, a state predicate per cut point, one statement per segment, the composition by SRr_bind / SRr_mono and the srealizes entry of cgif's lib/A/ACfh.v): the cut points, the registers and the frame are fuzz_uci.asan's, the slot is the core's lib/A/ACfn.v tfib_lib_contract_x_all, and the loop of five turns is composed by an induction on the turn. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, with its module paths, module names and addresses changed; 142 of its 254 lines of code are new or changed and 90 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_segs: the INTERFACE of the image-B walk of fuzz_wire.asan-ubsan's LLVMFuzzerTestOneInput
   (0x7fbf8, lib/B/Prog/WirePList.v AF_LLVMFuzzerTestOneInput; the statement wire_llvmf_holds_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_cg.v). It holds no stepping:
   1. the context ucx of one call, the slot pre / post at it, and the values the code derives from the input;
   2. a state predicate per cut point: u_st_oh at +0xb0 (before check_forward; f holds its copy of the frame), u_st_pre
      at +0x108 (before the malloc of c; the seven checks done), u_st_exit at +0x150 (before the free of c; c allocated,
      copied and checked), u_st_ret at +0x160 (the `li a0, 0` that both the refusal and the frees reach);
   3. four segment statements: entry (+0x000 .. +0xb0, or +0x160 on the refusal), turn_a (+0xb0 .. +0x108, the seven
      checks on f), turn_b (+0x108 .. +0x150: malloc c, the copy, check_copy, check_read), exit (+0x150 .. ret with
      the two frees, and +0x160 .. ret);
   4. the composition wire_llvmf_holds_of_segs, proved.

   The code (the listing of image B, offsets from 0x7fbf8; the table in LLVMFuzzerTestOneInput_cg.v). The frame is
   0x40 bytes at sp1 = sp0 - 0x40: the eight saved words ra, s0 .. s6 at sp1 + 0x38 .. sp1 (+0x004 .. +0x020, reloaded
   at +0x164 .. +0x180). Let size be the slot's n and data its p. The `bltu` at +0x30 goes to +0x160 when size = 0 or
   size >= 2 ^ 26 (only the saves come before it; the slot pre leaves only size = 0). Otherwise: s4 = data, the
   UBSan check data = NULL (+0x38) and data[0]'s shadow (+0x50) and the wrap of data + 1 (+0x5c); s6 = size - 1,
   s1 = fn = min (size - 1, 1600) (+0x60 .. +0x70); s2 = data[0] (+0x74); s3 = fn + (fn == 0) (+0x78, +0x7c), the
   malloc of f (+0x84; NULL goes to abort at +0x190), s0 = f (+0x8c); s5 = data[0] & 1, s2 = (data[0] >> 1) - 2
   (+0x90 .. +0x98); `beqz s6` (+0x9c) skips __asan_memcpy (f, data + 1, fn) at +0xac. Then the checks at +0xbc
   (check_forward f fn s5), +0xc8 (check_ret), +0xd4 (check_downstream), +0xe0 (check_meter), +0xec (check_counter),
   +0xf4 (check_width fn), +0x104 (check_read f fn s2); the malloc of c (+0x10c, size s3), s3 = c (+0x114),
   `beqz s6` (+0x118) skips __asan_memcpy (c, f, fn) at +0x128; len = check_copy (c, f, fn) at +0x138, `beqz a0`
   (+0x13c) skips check_read (c, len, s2) at +0x14c; free (c) at +0x154, free (f) at +0x15c; a0 = 0 at +0x160, the
   reloads, sp += 0x40, `ret` at +0x188.

   Every callee is a premise of wire_llvmf_holds_stmt; the walk takes those premises as the record u_prem. *)
From Stdlib Require Import ZArith NArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00 YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YE01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v YCfn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require ZTraceSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import PaBase WirePSyms WirePAddr WirePList WirePImg WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require check_forward_cg check_ret_cg check_downstream_cg
  check_meter_cg check_counter_cg check_width_cg check_read_cg check_copy_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI16.
Module ZTS := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.ZTraceSpec.
Module PFWD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_forward_cg.
Module PRET := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_ret_cg.
Module PDS := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_downstream_cg.
Module PMET := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_meter_cg.
Module PCNT := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_counter_cg.
Module PWID := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_width_cg.
Module PRD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_read_cg.
Module PCPY := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.check_copy_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The frame: 0x40 bytes (WirePImg.v WIRE_LLVMF_FRAME); the eight saved words as (byte below the entry sp, register
   number), the stores at +0x004 .. +0x020 and the reloads at +0x164 .. +0x180. s7 .. s11 are neither saved nor
   written. *)
Definition U_FRAME : Z := 0x40.
Lemma U_FRAME_eq : U_FRAME = WIRE_LLVMF_FRAME.
Proof. reflexivity. Qed.
Definition wire_saved_at : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22)].
(* The cut points, as offsets from the entry: the join after f's copy (the return of __asan_memcpy at +0xac and the
   target of `beqz s6` at +0x9c), the return of the first check_read, the join after the second check_read (its return
   and the target of `beqz a0` at +0x13c), and the `li a0, 0` (the target of the refusal at +0x30, and the return of
   the free of f at +0x15c). *)
Definition U_OH : Z := 0xb0.
Definition U_PRE : Z := 0x108.
Definition U_EXIT : Z := 0x150.
Definition U_RET : Z := 0x160.
(* The model events each cut point has spent at most: the malloc of f; the seven checks; the malloc of c, check_copy
   and the second check_read; the two frees. *)
Definition U_EV_OH : Z := 1.
Definition U_EV_PRE : Z :=
  U_EV_OH + PFWD.CF_EV + PRET.CR_EV + PDS.CDS_EV + PMET.CM_EV + PCNT.CCN_EV + PWID.CW_EV + PRD.CRD_EV.
Definition U_EV_EXIT : Z := U_EV_PRE + 1 + PCPY.CC_EV + PRD.CRD_EV.
Definition U_EV_RET : Z := U_EV_EXIT + 2.

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation tfib_K := YE2k.tfib_K.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The premises of wire_llvmf_holds_stmt, in its order. *)
Record u_prem : Prop := mkUPrem {
  up_wrap_malloc : pc_wrap_malloc (as_code B) = wire_sigma WS___interceptor_trampoline_malloc;
  up_wrap_free : pc_wrap_free (as_code B) = wire_sigma WS___interceptor_trampoline_free;
  up_cells : wire_cells B;
  up_ro_unowned : wire_ro_rd_unowned B;
  up_rom_no_errno : wire_rom_no_errno B;
  up_laws : AR_laws segs B;
  up_model_laws : model_laws (as_universe B);
  up_meter_laws : ameter_laws MT;
  up_meter_fs_laws : ameter_fs_laws MT;
  up_sink_img : @asink_img_laws tfib_sink_head segs B tfib_K;
  up_sink_kept : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W0 mem0) md0 -> asink_none segs tfib_K (rd W' mem') md';
  up_meta_kept : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W0 mem0) M -> ameta_inv segs tfib_K ly' (rd W' mem') M;
  up_ro_below : @ro_below_ofl segs RLO RHI tfib_sink_head;
  up_ufix : wire_llvmf_ufix B;
  up_malloc : forall fx' : YK11.FPState, @amalloc04_rule fx' rc tfib_sink_head segs B MT;
  up_free : forall fx' : YK11.FPState, @afree04_rule fx' rc tfib_sink_head segs B MT;
  up_memcpy : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (wire_sigma WS___asan_memcpy);
  up_cfwd : forall fx' : YK11.FPState, @PFWD.wire_check_forward_cg fx' rc B MT (wire_sigma WS_check_forward);
  up_cret : forall fx' : YK11.FPState, @PRET.wire_check_ret_cg fx' rc B MT (wire_sigma WS_check_ret);
  up_cds : forall fx' : YK11.FPState, @PDS.wire_check_downstream_cg fx' rc B MT (wire_sigma WS_check_downstream);
  up_cmet : forall fx' : YK11.FPState, @PMET.wire_check_meter_cg fx' rc B MT (wire_sigma WS_check_meter);
  up_ccnt : forall fx' : YK11.FPState, @PCNT.wire_check_counter_cg fx' rc B MT (wire_sigma WS_check_counter);
  up_cwid : forall fx' : YK11.FPState, @PWID.wire_check_width_cg fx' rc B MT (wire_sigma WS_check_width);
  up_crd : forall fx' : YK11.FPState, @PRD.wire_check_read_cg fx' rc B MT (wire_sigma WS_check_read);
  up_ccpy : forall fx' : YK11.FPState, @PCPY.wire_check_copy_cg fx' rc B MT (wire_sigma WS_check_copy);
  up_cost : forall n, 0 <= n -> wire_llvmf_cost MT n <= XL n }.

(* ------------------------------------------------------------------ *)
(* 1. The context of one call                                           *)
(* ------------------------------------------------------------------ *)

Record ucx := mkUCx {
  u_fx : YK11.FPState;
  u_ly : alayout;
  u_S : astate;
  u_W : world segs;
  u_regs : bvmap 5 word;
  u_mem : word -> option byte;
  u_md : Model;
  u_p : Z;
  u_n : Z;
  u_pl : list byte;
  u_M : Z }.

Definition u_sp0 (cx : ucx) : Z := spZ (u_regs cx).
Definition u_sp1 (cx : ucx) : Z := u_sp0 cx - U_FRAME.

(* The slot pre at the entry configuration. *)
Definition u_base (cx : ucx) : Prop :=
  @tfib_lib_pre_x rc B MT XL RLO RHI (u_regs cx) (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx)
    (u_p cx) (u_n cx) (u_pl cx) (u_M cx).

(* The slot post at the return, at the one leaf checksum_shape's LIBK hands the continuation
   (lib/ZTraceSpec.v: LIBK pl fs K = K (LL 0 fs [])). *)
Definition u_post (cx : ucx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k,
    c' = @cfg_at (u_fx cx) segs RA_LLVMF regs' mem' md' /\
    @tfib_lib_post_x rc B MT XL (u_regs cx) (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) (u_p cx) (u_n cx)
      (u_M cx) (YO09.LL 0 (m_fs (u_md cx)) []) ly' S' W' regs' mem' md' k.

(* The values the code derives from the input (size = u_n, data = u_p, its bytes u_pl): the flag byte data[0]; the
   frame length fn = min (size - 1, W_RECV_MAX) (s1); the size of each of the blocks f and c, fn + (fn == 0) (s3);
   bcast = data[0] & 1 (s5); slot = (data[0] >> 1) - 2 (s2); and the fn bytes data[1 .. fn] that f and c hold. *)
Definition u_flag (cx : ucx) : Z := nth 0 (map (fun b : byte => bv_unsigned b) (u_pl cx)) 0.
Definition u_fn (cx : ucx) : Z := Z.min (u_n cx - 1) WIRE_RECV_MAX.
Definition u_fsz (cx : ucx) : Z := Z.max (u_fn cx) 1.
Definition u_bc (cx : ucx) : Z := Z.land (u_flag cx) 1.
Definition u_slot (cx : ucx) : Z := Z.shiftr (u_flag cx) 1 - 2.
Definition u_fb (cx : ucx) : list byte := firstn (Z.to_nat (u_fn cx)) (skipn 1 (u_pl cx)).

Lemma u_flag_range : forall cx, 0 <= u_flag cx < 256.
Proof.
intros cx. unfold u_flag. destruct (u_pl cx) as [|b l]; cbn [map nth]; [lia|].
pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia.
Qed.
Lemma u_bc_range : forall cx, 0 <= u_bc cx <= 1.
Proof.
intros cx. unfold u_bc. pose proof (u_flag_range cx) as H.
assert (E : Z.land (u_flag cx) 1 = u_flag cx mod 2)
  by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
rewrite E. pose proof (Z.mod_pos_bound (u_flag cx) 2 ltac:(lia)). lia.
Qed.
Lemma u_slot_range : forall cx, -2 <= u_slot cx <= 125.
Proof.
intros cx. unfold u_slot. pose proof (u_flag_range cx) as H.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
assert (0 <= u_flag cx / 2) by (apply Z.div_pos; lia).
assert (u_flag cx / 2 < 128) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.
Lemma u_slot_int : forall cx, INT_MIN <= u_slot cx <= INT_MAX.
Proof. intros cx. pose proof (u_slot_range cx). unfold INT_MIN, INT_MAX. lia. Qed.
Lemma u_fn_range : forall cx, 0 < u_n cx -> 0 <= u_fn cx <= WIRE_RECV_MAX /\ 1 <= u_fsz cx <= WIRE_RECV_MAX.
Proof. intros cx H. unfold u_fsz, u_fn, WIRE_RECV_MAX. lia. Qed.
Lemma u_fb_length : forall cx, 0 < u_n cx -> u_n cx = Z.of_nat (length (u_pl cx)) ->
  Z.of_nat (length (u_fb cx)) = u_fn cx.
Proof.
intros cx Hn Hl. unfold u_fb. rewrite length_firstn, length_skipn.
unfold u_fn, WIRE_RECV_MAX in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The pieces every cut point shares                                 *)
(* ------------------------------------------------------------------ *)

(* The eight saved words are still the caller's. *)
Definition u_saved (cx : ucx) (r : reader) : Prop :=
  Forall (fun o : Z * Z => rdword r (u_sp0 cx - fst o) = Some (bv_unsigned (YK11.getr (u_regs cx) (Z_to_bv 5 (snd o)))))
    wire_saved_at.

(* The frame invariant: the caller's journal (no file range, no fake frame), no fake frame live, sp = sp1, gp / tp,
   s7 .. s11 (callee-saved, never saved or written here), the saved words, and the live blocks: the caller's and bl
   (the blocks of this call still live), up to order. *)
Definition u_core (cx : ucx) (ly' : alayout) (S' : astate) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (bl : list (Z * Z)) (k : Z) : Prop :=
  @ajournal rc tfib_sink_head segs B LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx)
    [] ly' S' W' mem' md' k /\
  frames S' = [] /\
  spZ regs' = u_sp1 cx /\
  YK11.getr regs' 3 = w64 (as_gp B) /\ YK11.getr regs' 4 = w64 (as_tp B) /\
  YK11.getr regs' 23 = YK11.getr (u_regs cx) 23 /\ YK11.getr regs' 24 = YK11.getr (u_regs cx) 24 /\
  YK11.getr regs' 25 = YK11.getr (u_regs cx) 25 /\ YK11.getr regs' 26 = YK11.getr (u_regs cx) 26 /\
  YK11.getr regs' 27 = YK11.getr (u_regs cx) 27 /\
  u_saved cx (aview segs (w_H W') mem') /\
  Permutation (ablocks B ly' S') (ablocks B (u_ly cx) (u_S cx) ++ bl).

(* The meter after a cost c: spent at most c from the entry, and XL size - c left. The costs of the cut points: the
   malloc of f (U_C_F); with the malloc of c and one call of check_copy (U_C_C); with the two frees, the whole call
   (LLVMFuzzerTestOneInput_cg.v wire_llvmf_cost). Each block is charged at its largest size, WIRE_RECV_MAX. *)
Definition u_meter (cx : ucx) (S' : astate) (c : Z) : Prop :=
  mo_le MT (u_S cx) S' c /\ mo_ok MT S' (XL (u_n cx) - c).
Definition U_C_F : Z := mo_malloc MT WIRE_RECV_MAX.
Definition U_C_C : Z := 2 * mo_malloc MT WIRE_RECV_MAX + wire_ccpy_cost_max MT.

(* The machine at an offset of the entry. *)
Definition u_cfg (cx : ucx) (off : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : config :=
  mkCfg (@YK11.mkst (u_fx cx) regs' (w64 (WIRE_A_LLVMF + off)) mem' (YK11.seg_rom segs)) md'.

(* The registers from +0xb0 to the malloc of c at +0x10c (callee-saved, so every check returns them): s0 = f,
   s1 = fn, s2 = slot, s3 = the block size fn + (fn == 0), s5 = bcast, s6 = size - 1. *)
Definition u_fregs (cx : ucx) (regs' : bvmap 5 word) (f : Z) : Prop :=
  YK11.getr regs' 8 = w64 f /\ YK11.getr regs' 9 = w64 (u_fn cx) /\ YK11.getr regs' 18 = w64 (u_slot cx) /\
  YK11.getr regs' 19 = w64 (u_fsz cx) /\ YK11.getr regs' 21 = w64 (u_bc cx) /\ YK11.getr regs' 22 = w64 (u_n cx - 1).

(* ------------------------------------------------------------------ *)
(* 3. The state at each cut point                                       *)
(* ------------------------------------------------------------------ *)

(* +0xb0, the head of turn_a (`mv a0, s0` before check_forward): the size was not refused (0 < size), f is a new block
   of u_fsz bytes beside the caller's, and it holds the fn bytes data[1 .. fn]. *)
Definition u_st_oh (cx : ucx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (f : Z),
    c' = u_cfg cx U_OH regs' mem' md' /\
    0 < u_n cx /\
    u_core cx ly' S' W' regs' mem' md' [(f, u_fsz cx)] U_EV_OH /\
    u_meter cx S' U_C_F /\
    u_fregs cx regs' f /\
    garr8 segs (rd W' mem') f (map (fun b : byte => bv_unsigned b) (u_fb cx)).

(* +0x108, the head of turn_b (`mv a0, s3` before the malloc of c): as at +0xb0, after the seven checks (each keeps
   the caller's blocks' bytes, f's among them, and charges the meter nothing). *)
Definition u_st_pre (cx : ucx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (f : Z),
    c' = u_cfg cx U_PRE regs' mem' md' /\
    0 < u_n cx /\
    u_core cx ly' S' W' regs' mem' md' [(f, u_fsz cx)] U_EV_PRE /\
    u_meter cx S' U_C_F /\
    u_fregs cx regs' f /\
    garr8 segs (rd W' mem') f (map (fun b : byte => bv_unsigned b) (u_fb cx)).

(* +0x150, the head of exit (`mv a0, s3` before the free of c): the size was not refused (0 < size, as at +0xb0 and
   +0x108), the blocks f and c of u_fsz bytes are live, s0 = f, s3 = c. *)
Definition u_st_exit (cx : ucx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (f c : Z),
    c' = u_cfg cx U_EXIT regs' mem' md' /\
    0 < u_n cx /\
    u_core cx ly' S' W' regs' mem' md' [(f, u_fsz cx); (c, u_fsz cx)] U_EV_EXIT /\
    u_meter cx S' U_C_C /\
    YK11.getr regs' 8 = w64 f /\ YK11.getr regs' 19 = w64 c.

(* +0x160, `li a0, 0`: the caller's blocks only, the whole call's events and cost at most. *)
Definition u_st_ret (cx : ucx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md',
    c' = u_cfg cx U_RET regs' mem' md' /\
    u_core cx ly' S' W' regs' mem' md' [] U_EV_RET /\
    u_meter cx S' (wire_llvmf_cost MT (u_n cx)).

(* ------------------------------------------------------------------ *)
(* 4. The four segment statements                                       *)
(* ------------------------------------------------------------------ *)

(* +0x000 .. +0xb0, or +0x160: the frame and the eight saves; the size refusal at +0x30 (to +0x160 when size = 0; the
   slot pre refutes size >= 2 ^ 26); otherwise s4 = data, the UBSan check data = NULL (refuted: data >= 4096 by the
   input block), the shadow base through its GOT word, data[0]'s shadow check (closed by the shadow of the live input
   block), the UBSan wrap check of data + 1 (refuted), s6, fn, the flag byte, s3, the malloc of f (the malloc rule; its
   NULL branch refuted), s0 = f, bcast, slot, and __asan_memcpy (f, data + 1, fn) unless fn = 0. *)
Definition u_entry_stmt : Prop :=
  u_prem ->
  forall (cx : ucx), u_base cx ->
    SRr segs (u_W cx) (@cfg_at (u_fx cx) segs A_LLVMF (u_regs cx) (u_mem cx) (u_md cx))
      (fun W' c' => u_st_oh cx W' c' \/ u_st_ret cx W' c').

(* +0xb0 .. +0x108: check_forward (f, fn, bcast), check_ret (f, fn), check_downstream (f, fn), check_meter (f, fn),
   check_counter (f, fn), check_width (fn), check_read (f, fn, slot), each by its contract in u_prem. *)
Definition u_turn_a_stmt : Prop :=
  u_prem ->
  forall (cx : ucx) (W' : world segs) (c' : config),
    u_base cx -> u_st_oh cx W' c' -> SRr segs W' c' (u_st_pre cx).

(* +0x108 .. +0x150: the malloc of c (size s3; its NULL branch refuted), s3 = c, __asan_memcpy (c, f, fn) unless
   fn = 0, len = check_copy (c, f, fn), and check_read (c, len, slot) unless len = 0. *)
Definition u_turn_b_stmt : Prop :=
  u_prem ->
  forall (cx : ucx) (W' : world segs) (c' : config),
    u_base cx -> u_st_pre cx W' c' -> SRr segs W' c' (u_st_exit cx).

(* +0x150 .. ret: free (c), free (f), then (as from +0x160 on the refusal) a0 = 0, the eight reloads, sp back to sp0,
   ret. *)
Definition u_exit_stmt : Prop :=
  u_prem ->
  forall (cx : ucx) (W' : world segs) (c' : config),
    u_base cx -> u_st_exit cx W' c' \/ u_st_ret cx W' c' -> SRr segs W' c' (u_post cx).

(* ------------------------------------------------------------------ *)
(* 5. The composition                                                   *)
(* ------------------------------------------------------------------ *)

(* cgif lib/A/ACfh.v:47: an SRr obligation whose post is "AI gives srealizes" is a srealizes. *)
Lemma u_srz_enter : forall (W : world segs) (c : config) (T : TSet),
  AI segs (w_H W) (w_A W) (cfg_model c) ->
  SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) ->
  srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.

(* From the entry the walk reaches the post: entry, then turn_a, turn_b and exit, or exit at once after the refusal. *)
Lemma u_walk : u_entry_stmt -> u_turn_a_stmt -> u_turn_b_stmt -> u_exit_stmt -> u_prem ->
  forall (cx : ucx), u_base cx ->
  SRr segs (u_W cx) (@cfg_at (u_fx cx) segs A_LLVMF (u_regs cx) (u_mem cx) (u_md cx)) (u_post cx).
Proof.
intros EN TA TB EX HP cx HB.
eapply SRr_bind; [exact (EN HP cx HB)|].
intros W1 c1 _ [HA | HR].
- eapply SRr_bind; [exact (TA HP cx W1 c1 HB HA)|].
  intros W2 c2 _ HBb.
  eapply SRr_bind; [exact (TB HP cx W2 c2 HB HBb)|].
  intros W3 c3 _ HEX.
  exact (EX HP cx W3 c3 HB (or_introl HEX)).
- exact (EX HP cx W1 c1 HB (or_intror HR)).
Qed.

Theorem wire_llvmf_holds_of_segs :
  u_entry_stmt -> u_turn_a_stmt -> u_turn_b_stmt -> u_exit_stmt ->
  @wire_llvmf_holds_stmt rc B MT XL RLO RHI.
Proof.
intros EN TA TB EX.
unfold wire_llvmf_holds_stmt.
intros HWM HWF HCELLS HROU HRNE LAWS ML MTL MTF SIL HSINK HMETA ROB UFIX HMAL HFRE HCPY
  CFWD CRET CDS CMET CCNT CWID CRD CCPY HXL.
pose proof (mkUPrem HWM HWF HCELLS HROU HRNE LAWS ML MTL MTF SIL HSINK HMETA ROB UFIX HMAL HFRE HCPY
  CFWD CRET CDS CMET CCNT CWID CRD CCPY HXL) as HP.
intros fx ly S W regs mem md p n pl M K HAI HPRE HK.
change (@LIBK ZTS.checksum_shape pl (m_fs md) K) with (K (YO09.LL 0 (m_fs md) [])).
set (cx := mkUCx fx ly S W regs mem md p n pl M).
assert (HB : u_base cx) by exact HPRE.
eapply u_srz_enter; [exact HAI|].
eapply (SRr_mono segs W (@cfg_at fx segs A_LLVMF regs mem md) (u_post cx)).
- exact (u_walk EN TA TB EX HP cx HB).
- intros W' c' Hwle HPOST HAI'. unfold u_post in HPOST. destruct HPOST as (ly' & S' & regs' & mem' & md' & k & Hc & HQ).
  apply (HK (YO09.LL 0 (m_fs md) []) W' c' Hwle HAI'). exists ly', S', regs', mem', md', k. exact (conj Hc HQ).
Qed.
End seg.
