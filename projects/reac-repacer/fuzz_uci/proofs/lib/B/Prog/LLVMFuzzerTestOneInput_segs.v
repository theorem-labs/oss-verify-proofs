(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the interface of the image-A walk of reac-repacer/fuzz_uci's LLVMFuzzerTestOneInput, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v (the context record, a state predicate per cut point, one statement per segment, the composition by SRr_bind / SRr_mono and the srealizes entry of cgif's lib/A/ACfh.v): the cut points, the registers and the frame are fuzz_uci.asan's, the slot is the core's lib/A/ACfn.v tfib_lib_contract_x_all, and the loop of five turns is composed by an induction on the turn. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, with its module paths, module names and addresses changed; 12 of its 203 lines of code are new or changed and 11 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_segs: the INTERFACE of the image-B walk of fuzz_uci.asan-ubsan's LLVMFuzzerTestOneInput
   (0x7f2e8, lib/B/Prog/UciPList.v AF_LLVMFuzzerTestOneInput; the statement uci_llvmf_holds_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_cg.v). It holds no stepping:
   1. the context ucx of one call and the slot pre / post at it;
   2. a state predicate per cut point: u_st_oh at +0xbc (the head of the five-turn loop, turn i), u_st_pre at +0x180
      (turn i, after the four bytes of cur, the length byte and the slice's bounds, before `lw a2, 8(sp)`), u_st_exit
      at +0x1c8 (after the fifth turn);
   3. four segment statements: entry (+0x000 .. +0xbc), turn_a (+0xbc .. +0x180), turn_b (+0x180 .. the next head or
      +0x1c8, with the calls of check_no_overread and check_value), exit (+0x1c8 .. ret, with the call of check_clamp);
   4. the composition uci_llvmf_holds_of_segs, proved.

   The code (DIS of image B, offsets from 0x7f2e8). The frame is 0x90 bytes at sp1 = sp0 - 0x90: the twelve saved words
   at sp1 + 0x30 .. sp1 + 0x88 (ra, s0 .. s10), the int[5] of results at sp1 + 0x1c, and the 4-byte cur buffer (later
   the struct copy) at sp1 + 8. s0 = n, s1 = p, s2 = margin_max, s5 = the shadow base, s6 = the turn, s7 = the offset
   into the input, s8 = (p != 0), s9 = sp1 + 0x1c, s10 = 5 from +0xbc on. Each turn: cur is the next four input bytes
   (0 past the end), the length byte the next (0 past the end), s4 = p + s7 is the slice's base and s3 = min(n - s7,
   length byte) its length; the slice (s4, s3) goes to check_no_overread (+0x18c) and check_value (+0x19c), and
   check_value's result is stored at s9 + 4 * turn; s7 += s3. After five turns (`bne s6, s10` at +0x1b4, `j` at +0x1b8)
   the five ints are copied to sp1 + 8 (+0x1c8 .. +0x210) and check_clamp (sp1 + 8, margin_max) is called (+0x21c);
   the function returns 0. Every UBSan check branches to `unimp` at +0x25c: the null and wrap checks of p + s7 at each
   input byte read (+0xd0 .. +0xe0, +0x12c .. +0x13c), of the slice base (+0x164, +0x170), of MARGIN_MAX + 4 bit (+0x80)
   and of p itself (+0x54); the wrap checks of sp + 0x1c + 4 j in the copy (+0x1d8 .. +0x208).

   Every callee is a premise of uci_llvmf_holds_stmt; the walk takes those premises as the record u_prem. *)
From Stdlib Require Import ZArith NArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YI00 YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YE01.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v YCfn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require ZTraceSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import PaBase UciPSyms UciPAddr UciPList UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require rp_uci_int_cg check_no_overread_cg check_value_cg check_clamp_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI16.
Module ZTS := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.ZTraceSpec.
Module PR := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.rp_uci_int_cg.
Module PN := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_no_overread_cg.
Module PV := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_value_cg.
Module PK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_clamp_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The frame: 0x90 bytes; the twelve saved words as (byte below the entry sp, register number), the stores at
   +0x004 .. +0x030 and the reloads at +0x224 .. +0x250. *)
Definition U_FRAME : Z := 0x90.
Definition uci_saved_at : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24); (88, 25);
   (96, 26)].
(* The cut points, as offsets from the entry. *)
Definition U_OH : Z := 0xbc.
Definition U_PRE : Z := 0x180.
Definition U_EXIT : Z := 0x1c8.
(* The two values of MARGIN_MAX (lib/Spec/UciModel.v MARGIN_MAX), as the image holds them at 0x20ca0. *)
Definition U_MM0 : Z := 1984.
Definition U_MM1 : Z := 16320.
(* The model events of one turn: check_no_overread's four and check_value's two. *)
Definition U_EV_TURN : Z := PN.CNO_EV + PV.CV_EV.

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation tfib_K := YE2k.tfib_K.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The premises of uci_llvmf_holds_stmt, in its order. *)
Record u_prem : Prop := mkUPrem {
  up_cells : uci_cells B;
  up_ro_unowned : uci_ro_rd_unowned B;
  up_rom_no_errno : uci_rom_no_errno B;
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
  up_cno : forall fx : YK11.FPState,
     @PN.uci_check_no_overread_cg fx rc B MT (uci_sigma US_check_no_overread) CTX_check_no_overread;
  up_cv : forall fx : YK11.FPState, @PV.uci_check_value_cg fx rc B MT (uci_sigma US_check_value);
  up_cc : forall fx : YK11.FPState, @PK.uci_check_clamp_cg fx rc B MT (uci_sigma US_check_clamp);
  up_cost : forall n, 0 <= n -> uci_llvmf_cost MT n <= XL n }.

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

(* ------------------------------------------------------------------ *)
(* 2. The pieces every cut point shares                                 *)
(* ------------------------------------------------------------------ *)

(* The twelve saved words are still the caller's. *)
Definition u_saved (cx : ucx) (r : reader) : Prop :=
  Forall (fun o : Z * Z => rdword r (u_sp0 cx - fst o) = Some (bv_unsigned (YK11.getr (u_regs cx) (Z_to_bv 5 (snd o)))))
    uci_saved_at.

(* The frame invariant: the caller's journal (no file range, no fake frame), sp = sp1, gp / tp, s11 (callee-saved, and
   the one such register this function never saves or writes), the saved words, and the caller's blocks up to
   order. *)
Definition u_core (cx : ucx) (ly' : alayout) (S' : astate) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
  @ajournal rc tfib_sink_head segs B LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx)
    [] ly' S' W' mem' md' k /\
  frames S' = [] /\
  spZ regs' = u_sp1 cx /\
  YK11.getr regs' 3 = w64 (as_gp B) /\ YK11.getr regs' 4 = w64 (as_tp B) /\
  YK11.getr regs' 27 = YK11.getr (u_regs cx) 27 /\
  u_saved cx (aview segs (w_H W') mem') /\
  Permutation (ablocks B ly' S') (ablocks B (u_ly cx) (u_S cx)).

(* The meter after i turns: each turn spends at most one call of check_no_overread and one of check_value at their
   largest slice. *)
Definition U_TURN_COST : Z := uci_cno_cost_max MT + uci_cv_cost_max MT.
Definition u_meter (cx : ucx) (S' : astate) (i : Z) : Prop :=
  mo_le MT (u_S cx) S' (i * U_TURN_COST) /\ mo_ok MT S' (XL (u_n cx) - i * U_TURN_COST).

(* The results of the first i turns: ints, stored at sp1 + 0x1c + 4 j. *)
Definition u_res (cx : ucx) (r : reader) (i : Z) (vs : list Z) : Prop :=
  Z.of_nat (length vs) = i /\ Forall (fun v => INT_MIN <= v <= INT_MAX) vs /\
  forall j, 0 <= j < i -> rd32 r (u_sp1 cx + 0x1c + 4 * j) (nth (Z.to_nat j) vs 0).

(* The machine at an offset of the entry. *)
Definition u_cfg (cx : ucx) (off : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : config :=
  mkCfg (@YK11.mkst (u_fx cx) regs' (w64 (UCI_A_LLVMF + off)) mem' (YK11.seg_rom segs)) md'.

(* The registers every loop cut point holds: s0 = n, s1 = p, s2 = mm (one of the two MARGIN_MAX values), s5 = the
   shadow base, s6 = the turn i, s7 = the input offset off, s8 = 1 (`snez s8, s1` at +0xb0; p >= 4096 by the slot
   pre), s9 = sp1 + 0x1c, s10 = 5. *)
Definition u_lregs (cx : ucx) (regs' : bvmap 5 word) (i off mm : Z) : Prop :=
  YK11.getr regs' 8 = w64 (u_n cx) /\ YK11.getr regs' 9 = w64 (u_p cx) /\
  YK11.getr regs' 18 = w64 mm /\ (mm = U_MM0 \/ mm = U_MM1) /\
  YK11.getr regs' 21 = w64 SHADOW_OFF /\ YK11.getr regs' 22 = w64 i /\ YK11.getr regs' 23 = w64 off /\
  YK11.getr regs' 24 = w64 1 /\ YK11.getr regs' 25 = w64 (u_sp1 cx + 0x1c) /\ YK11.getr regs' 26 = w64 5.

(* ------------------------------------------------------------------ *)
(* 3. The state at each cut point                                       *)
(* ------------------------------------------------------------------ *)

(* +0xbc, the head of turn i (0 <= i <= 4): the `sw zero, 8(sp)` that starts cur. off is the input offset s7. *)
Definition u_st_oh (cx : ucx) (i : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (off mm : Z) (vs : list Z),
    c' = u_cfg cx U_OH regs' mem' md' /\
    u_core cx ly' S' W' regs' mem' md' (i * U_EV_TURN) /\
    u_meter cx S' i /\
    u_lregs cx regs' i off mm /\
    0 <= off <= u_n cx /\
    u_res cx (aview segs (w_H W') mem') i vs.

(* +0x180, turn i before `lw a2, 8(sp)`: the four bytes of cur are stored (cu, their unsigned little-endian value),
   s7 = off is the slice's offset (past the length byte), s4 = p + off its base and s3 = len its length. *)
Definition u_st_pre (cx : ucx) (i : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (off len mm cu : Z) (vs : list Z),
    c' = u_cfg cx U_PRE regs' mem' md' /\
    u_core cx ly' S' W' regs' mem' md' (i * U_EV_TURN) /\
    u_meter cx S' i /\
    u_lregs cx regs' i off mm /\
    YK11.getr regs' 19 = w64 len /\ YK11.getr regs' 20 = w64 (u_p cx + off) /\
    0 <= off /\ 0 <= len <= PR.REPLY_MAX /\ off + len <= u_n cx /\
    0 <= cu < 2 ^ 32 /\ rd32 (aview segs (w_H W') mem') (u_sp1 cx + 8) cu /\
    u_res cx (aview segs (w_H W') mem') i vs.

(* +0x1c8, after the fifth turn: the five results are stored. *)
Definition u_st_exit (cx : ucx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' (mm : Z) (vs : list Z),
    c' = u_cfg cx U_EXIT regs' mem' md' /\
    u_core cx ly' S' W' regs' mem' md' (5 * U_EV_TURN) /\
    u_meter cx S' 5 /\
    YK11.getr regs' 18 = w64 mm /\ (mm = U_MM0 \/ mm = U_MM1) /\
    u_res cx (aview segs (w_H W') mem') 5 vs.

(* ------------------------------------------------------------------ *)
(* 4. The four segment statements                                       *)
(* ------------------------------------------------------------------ *)

(* +0x000 .. +0xbc: the frame and the twelve saves, s0 = n, the `n >> 26` early return (refuted: the slot pre bounds n
   below 2 ^ 26), the shadow base through its GOT word into s5, `beqz s0`; when n > 0 the UBSan check p = NULL
   (refuted: p >= 4096), data[0]'s shadow check against the input block, bit = data[0] & 1, the UBSan wrap check of
   MARGIN_MAX + 4 bit (refuted: MARGIN_MAX + 4 < 2 ^ 64); a0 = MARGIN_MAX + 4 bit (MARGIN_MAX when n = 0), its shadow
   check (closed by the zero-shadow row of uci_cells), s6 = 0, s7 = (n != 0), `lw s2` from the MARGIN_MAX region,
   s8 = (p != 0) = 1, s9 = sp + 0x1c, s10 = 5. *)
Definition u_entry_stmt : Prop :=
  u_prem ->
  forall (cx : ucx), u_base cx ->
    SRr segs (u_W cx) (@cfg_at (u_fx cx) segs A_LLVMF (u_regs cx) (u_mem cx) (u_md cx)) (u_st_oh cx 0).

(* +0xbc .. +0x180 of turn i: cur from the next four input bytes and the length byte, each read only below n, with its
   UBSan null / wrap checks refuted and its shadow checked against the input block; then s4 = p + off with its UBSan
   checks refuted, and len = min(n - off, length byte). *)
Definition u_turn_a_stmt : Prop :=
  u_prem ->
  forall (cx : ucx) (i : Z) (W' : world segs) (c' : config),
    0 <= i < 5 -> u_base cx -> u_st_oh cx i W' c' -> SRr segs W' c' (u_st_pre cx i).

(* +0x180 .. the next head of turn i: cur = the signed int of cu, check_no_overread (p + off, len, cur),
   check_value (p + off, len, cur), its result stored at s9 + 4 i, s7 += len; then the head of turn i + 1, or +0x1c8
   after the fifth turn. *)
Definition u_turn_b_stmt : Prop :=
  u_prem ->
  forall (cx : ucx) (i : Z) (W' : world segs) (c' : config),
    0 <= i < 5 -> u_base cx -> u_st_pre cx i W' c' ->
    SRr segs W' c' (fun W2 c2 => (i < 4 /\ u_st_oh cx (i + 1) W2 c2) \/ (i = 4 /\ u_st_exit cx W2 c2)).

(* +0x1c8 .. ret: the five results copied to sp1 + 8 (the UBSan wrap checks of sp + 0x1c + 4 j refuted by the stack
   bounds), check_clamp (sp1 + 8, margin_max), a0 = 0, the twelve reloads, sp back to sp0, ret. *)
Definition u_exit_stmt : Prop :=
  u_prem ->
  forall (cx : ucx) (W' : world segs) (c' : config),
    u_base cx -> u_st_exit cx W' c' -> SRr segs W' c' (u_post cx).

(* ------------------------------------------------------------------ *)
(* 5. The composition                                                   *)
(* ------------------------------------------------------------------ *)

(* cgif lib/A/ACfh.v:47: an SRr obligation whose post is "AI gives srealizes" is a srealizes. *)
Lemma u_srz_enter : forall (W : world segs) (c : config) (T : TSet),
  AI segs (w_H W) (w_A W) (cfg_model c) ->
  SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) ->
  srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.

(* The loop: from the head of turn i the walk reaches the post. *)
Lemma u_loop : u_turn_a_stmt -> u_turn_b_stmt -> u_exit_stmt -> u_prem ->
  forall (cx : ucx), u_base cx ->
  forall (m : nat) (i : Z), i = 4 - Z.of_nat m -> 0 <= i ->
  forall W' c', u_st_oh cx i W' c' -> SRr segs W' c' (u_post cx).
Proof.
intros TA TB EX HP cx HB m. induction m as [|m IH]; intros i Hi Hi0 W' c' HOH.
- eapply SRr_bind; [exact (TA HP cx i W' c' ltac:(lia) HB HOH)|].
  intros W1 c1 _ HPRE.
  eapply SRr_bind; [exact (TB HP cx i W1 c1 ltac:(lia) HB HPRE)|].
  intros W2 c2 _ [(Hlt & _) | (_ & HEX)]; [lia|].
  exact (EX HP cx W2 c2 HB HEX).
- destruct (Z.lt_ge_cases i 0) as [Hneg | Hnn]; [lia|].
  eapply SRr_bind; [exact (TA HP cx i W' c' ltac:(lia) HB HOH)|].
  intros W1 c1 _ HPRE.
  eapply SRr_bind; [exact (TB HP cx i W1 c1 ltac:(lia) HB HPRE)|].
  intros W2 c2 _ [(_ & HOH2) | (Hi4 & _)]; [|lia].
  exact (IH (i + 1) ltac:(lia) ltac:(lia) W2 c2 HOH2).
Qed.

Theorem uci_llvmf_holds_of_segs :
  u_entry_stmt -> u_turn_a_stmt -> u_turn_b_stmt -> u_exit_stmt ->
  @uci_llvmf_holds_stmt rc B MT XL RLO RHI.
Proof.
intros EN TA TB EX.
unfold uci_llvmf_holds_stmt.
intros HCELLS HROU HRNE LAWS ML MTL MTF SIL HSINK HMETA ROB CNO CV CC HXL.
pose proof (mkUPrem HCELLS HROU HRNE LAWS ML MTL MTF SIL HSINK HMETA ROB CNO CV CC HXL) as HP.
intros fx ly S W regs mem md p n pl M K HAI HPRE HK.
change (@LIBK ZTS.checksum_shape pl (m_fs md) K) with (K (YO09.LL 0 (m_fs md) [])).
set (cx := mkUCx fx ly S W regs mem md p n pl M).
assert (HB : u_base cx) by exact HPRE.
eapply u_srz_enter; [exact HAI|].
eapply (SRr_mono segs W (@cfg_at fx segs A_LLVMF regs mem md) (u_post cx)).
- eapply SRr_bind; [exact (EN HP cx HB)|].
  intros W1 c1 _ HOH.
  exact (u_loop TA TB EX HP cx HB 4%nat 0 ltac:(lia) ltac:(lia) W1 c1 HOH).
- intros W' c' Hwle HPOST HAI'. unfold u_post in HPOST. destruct HPOST as (ly' & S' & regs' & mem' & md' & k & Hc & HQ).
  apply (HK (YO09.LL 0 (m_fs md) []) W' c' Hwle HAI'). exists ly', S', regs', mem', md', k. exact (conj Hc HQ).
Qed.
End seg.
