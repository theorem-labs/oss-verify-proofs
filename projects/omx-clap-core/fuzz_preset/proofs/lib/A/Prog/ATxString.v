(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/ATxLine.v, with its module paths and module names changed; 1231 of its 1334 lines of code are new or changed and 921 lines of the source are left out. *)
(* RULE 24: proves function tx_string (image A').
   fuzz_preset IMAGE A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the walk of
   tx_string (fuzz_preset.c :408-430; 216 instructions from slot 3909 of lib/A/Listing_prog.v, A' 0x852f4) against the
   Tx part's text ttx_string_specX (lib/A/PRH_FnTx.v: the rp_* binders, the entry premise
   PresetRoomPos.iface_room_pos, the run premise, the room and the consumer window guarded by f0 = 0, the post ONE
   BUDGETED fpostWbm (fQmn: the memnorm keep) naming the outcome prhtx_out over what was ACTUALLY appended,
   DEAD-TXSTRING and the exact-or-frozen position), in cgif's per-function form over the listing engine (YC80x /
   YC1fPx over YCbqG's ajournal_x, caller-window form: YCbqGcallW.v ajournal_x_init_W). Every conclusion is
   `srealizes` through SRr'.
   WHAT THIS FILE HOLDS. ONLY image A': the seam offsets and literal addresses (read from A''s listing), the image
   facts, and the runs over PL_prog_A. Everything image-generic is the #102 glue lib/A/Prog/TxStr102Glue.v over
   lib/A/Prog/Tx102Glue.v (the text state), instantiated here at PI_prog_A, the whole-program instance (PALib is
   satisfiable only there). The walk is proved here MODULO the loop step: tx_string_A_of_step takes STEPa, the glue's
   ts_loop premise at A' (the loop head TS_PC_A + 340, .str.26, tx_string.hex), as its premise; the loop body is
   lib/A/Prog/ATxStep.v (ts_step_A, with the closing block ts_at_X_A as its exit), and the function theorem
   tx_string_A_holds is that assembly, in the Section (B, ARx, CTX0 and the image premises as hypotheses).
   THE INSTANCE (after the Sections): tx_string_A_inst states the text at the A' interface instance (B := AD2l.TfibB,
   ARx := PresetCfnA.iface_ARx at CfImg_A, prh_room_live_a8, preset_sink_head, CTX0 := iface_ctx0), every float
   state; it discharges every Section hypothesis by a cited closed lemma (the static image facts by
   lib/A/Prog/ATxStrWitA.v) and carries ONE premise, tx_put's text at the same instance.
   THE RELATION. Every tx_put call crosses the grow's free, so the text concludes SRr' segs RZ_cf with the post's
   journal at WR := wle' SEGS RZ_cf. The entry segment A (ts_A_cps: the prologue and frame_alloc_0, no free) runs at
   wle and is lifted once at its top (YGcfRhLift.ra_rh_of_SRr, a lift of that plain segment); its continuation gets
   the wle journal. THE ONE JOURNAL LIFT is at the cut B, the top of ts_at_B_A (ajournal_xwR_mono with
   YA0nH.wle_wle'); from there every journal is at WR (livea = the glue's ts_liveR at WR), every segment is SRW (SRr'
   at RZ_cf), the runners and the flag store are the R forms at WR, and ts_put_call / ts_LH / ts_loop are the glue's
   (at RCF = WR). The `ret` step is lifted by YA0nH.SRr_SRr'. The text's `(length rp_os <= 4)%nat` is the Section-g
   hypothesis HOS, passed to the glue's ts_put_call.
   THE MEMNORM KEEP. fpostWbm asks `memnorm mem -> memnorm mem'` from the entry to the return. Runs: YGcallMxmn.v's
   memnorm_frame_of (the run's full-memory frame_of from its start st_ok); the tx_put calls: the glue (s10_call_Wbm);
   frame_alloc_0: the stack_malloc rule YGcallMxmn.aj_stack_malloc_at_xm with ASM0 the m-form contract
   YGcallMxmn.astack_malloc_realizes_xm (aj_stack_malloc_at_x's post states the new memory through aview only, so no
   keep follows from it; the premises are the same).
   SEGMENTS: a fresh symbolic state from concrete facts at each seam, environment TE regs0 regsc more (atoms 0-31 the
   entry registers, 32-63 the current ones, 64- extras). A: +0 .. frame_alloc_0's `jal` at +112 (A1 / A2 / A3, the
   glue's entry segments); B: +116 .. the opening quote's `jal tx_put` at +276; C: +280 .. the closing block X or
   the loop head; X: +652 .. the closing quote's `jal tx_put` at +668; G: +672 .. `ret`.
   THE FAKE FRAME F ON A'. Segment B keeps F in a0 / a4 (both caller-saved) and spills it to sp1 + 16 and sp1 + 24
   BEFORE the opening call (+160 `sd a0, 16(s1)`, +208 `sd a4, 24(s1)`). So ts_B_run_A reads the spill off its run's
   final s1 chunks and hands it to the call, ts_put_call carries it across the call (its spill transport), and
   segment C reads F back from sp1 + 24 (+304 `ld a0, 24(s1)`) as a read-only chunk. C writes nothing, so the live
   state and the spill go across C's runs unchanged. A' has no UBSan test of s.
   NUMERALS. DERIVED: the seam offsets 92 / 96 / 116 / 280 / 340 / 652 / 672 (4 * the listing slot from tx_string's
   entry: A' 0x85350 / 0x85354 / 0x85368 / 0x8540c / 0x85448 / 0x85580 / 0x85594) and the same seams from the listing
   base, as a run's pc states them (TS_PC_A + 280 / 340 / 652 / 672 = 15916 / 15976 / 16288 / 16308, TS_PC_A =
   15636), the literal offsets 70432 / 70464 / 70368 from pa_val (A_OBJ 2) (the listing's PAddHi (A_OBJ 2) 0x11320 /
   0x11340 / 0x112e0: .str.25, .str.26, tx_string.hex at 0x21320 / 0x21340 / 0x212e0), atom indices (xr r = 32 + r,
   so 51 = s3; 64 / 65 the extras; 243 = A_OBJ 2). LENGTH: 64, 160, 176, 4096, 2 ^ 31 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47. No
   ADDRESS literal: code addresses are pa_sigma / pa_val of lib/A/PAImg_prog.v; the A' pcs in the comments are
   checked against the listing by lib/A/Prog/ATxStrWitA.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
(* the memnorm keep: YAkMemnorm's memnorm, YGcallMxmn's m-form stack_malloc rule and memnorm_frame_of (Required
   qualified: YGcallMxmn carries its own copies of in_roP / arodata_okP) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YCbqGwild.
(* the re-hiding relation WR, its step relation, and the lift of a plain segment (the free / realloc move) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Tx102Glue TxStr102Glue.
(* pa_slot_lt_ceil_b (fpre's raZ bound at a call), generic in the listing; it loads YF0v.v, which sets the zify
   division flag to false globally: the #[local] reset below follows it *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
(* the loop body (ts_step_A), Required qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require ATxStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image A': tx_string's entry, its seams (DERIVED; see the header) ---- *)
Definition TS_PC_A : Z := 4 * Z.of_nat (A_prog_slot AS_tx_string).
Definition TS_A2_OFF_A : Z := 92.    (* 0x85350: lw a2, 0(a2), the use-after-return flag *)
Definition TS_A3_OFF_A : Z := 96.    (* 0x85354: ld s8, 0(a1), the shadow base *)
Definition TS_B_OFF_A : Z := 116.    (* 0x85368: frame_alloc_0's return *)
Definition TS_C_OFF_A : Z := 280.    (* 0x8540c: the opening quote's return *)
Definition TS_LH_OFF_A : Z := 340.   (* 0x85448: the loop head (li a0, 6; sb a0, 4(s10)) *)
Definition TS_G_OFF_A : Z := 672.    (* 0x85594: the closing quote's return *)
Definition TS_X_OFF_A : Z := 652.    (* 0x85580: the closing quote's block *)
Definition TS_SPAN_A : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* a list is empty or a cons *)
Lemma ts_list_cases_A : forall (l : list Z), l = [] \/ exists x l', l = x :: l'.
Proof. intros [|x l]; [left; reflexivity | right; exists x, l; reflexivity]. Qed.
(* a register a run did not write keeps the segment's start value (the run's env may extend the segment's TE by fresh
   atoms) *)
Ltac tskeep_A HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
#[local] Notation STKS := (@STK_tx_string prh_img_A).
#[local] Notation TEa := (TE (L := A_prog_listing) (PA := PA)).

Definition TS_STR25_A : Z := VAL (A_OBJ 2) + 70432.   (* .str.25 on A', the quote (0x21320) *)
Definition TS_STR26_A : Z := VAL (A_OBJ 2) + 70464.   (* .str.26 on A', the backslash (0x21340) *)
Definition TS_HEX_A : Z := VAL (A_OBJ 2) + 70368.     (* tx_string.hex, the 16 digits (0x212e0) *)

Lemma TS_PC_val_A : BASE + TS_PC_A = SIGMA AS_tx_string.
Proof. vm_compute. reflexivity. Qed.
(* the glue's image facts at A' *)
Lemma pa_hi_ok_A : @pa_hi _ A_prog_listing PA <= 2 ^ 31.
Proof. vm_compute. discriminate. Qed.
(* the whole-program instance's image bounds lie in the ASan low memory (Tx102Glue.v s10_src_img's img_box) *)
Lemma img_box_A : 4096 <= @pa_lo _ A_prog_listing PA /\ @pa_hi _ A_prog_listing PA <= kLowMemEnd.
Proof. vm_compute. split; discriminate. Qed.
Lemma HSTK_A : 4096 + 176 <= STKS.
Proof. vm_compute. discriminate. Qed.
Lemma pst_img_A : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof. exact pst_in_img_A. Qed.
Lemma HSTKP_A : 0 <= @STK_tx_put prh_img_A /\ @STK_tx_put prh_img_A + 176 <= STKS.
Proof. split; vm_compute; discriminate. Qed.
Lemma pst_ro_A : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof. exact pst_not_ro_A. Qed.
(* fpre's raZ bound at A''s two tx_put return slots of this file (C: the opening quote's, 15916 = TS_PC_A + 280; G:
   the closing quote's, 16308 = TS_PC_A + 672), each a CLOSED lemma (PRW_StepKit.v pa_slot_lt_ceil_b; vm_compute only
   on the closed slot test, never inside a walk) *)
Lemma ts_ret_ceil_C_A : bv_unsigned (Z_to_bv 64 (BASE + 15916)) < YM05.alloc_ceiling.
Proof.
pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL) (PI := PA) 15916 ltac:(lia) ltac:(vm_compute; reflexivity)) as H.
pose proof (@pa_B_ok _ _ PA) as HB. rewrite unsigned_lit_small by lia. exact H.
Qed.
Lemma ts_ret_ceil_G_A : bv_unsigned (Z_to_bv 64 (BASE + 16308)) < YM05.alloc_ceiling.
Proof.
pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL) (PI := PA) 16308 ltac:(lia) ltac:(vm_compute; reflexivity)) as H.
pose proof (@pa_B_ok _ _ PA) as HB. rewrite unsigned_lit_small by lia. exact H.
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
(* THE RELATION after the cut B: the journal from the entry at WR, every segment at SRW *)
#[local] Notation WR := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation SRW := (YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B PST ARx WR).
#[local] Notation WRrefl := (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRtrans := (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf).
(* the allocator laws at the cf instance's head (16 fields). MARKED STAND-IN: discharged by tx_string_A_inst below
   (tsi_laws: YGcallcf.AR_laws_x_xs, the laws at ARcf /\ xs_placed_cf, which is the instance's iface_ARx) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* MARKED STAND-IN: PALib's fields at PI_prog_A, the whole-program instance, where A_OBJ 1 is the use-after-return
   flag's GOT word (A' 0xa2068); witness ATxStrWitA.v tsw_PAL_TfibA (PALibA.palib_A) *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
(* MARKED STAND-IN: the listing's __asan_stack_malloc_0 is the code record's frame_alloc_0 (A' 0x3db48); witness
   ATxStrWitA.v tsw_pal_stack_malloc0_TfibA *)
Hypothesis pal_stack_malloc0 : SIGMA AS___asan_stack_malloc_0 = pc_stack_malloc (as_code B) 0.
(* MARKED STAND-IN: the use-after-return flag cell lies in the image, PER-INSTANCE over the CfImg bounds (the glue's
   form; A' 0xaaec0, 4 bytes of .bss, inside CfImg_A's [0x10000, 0x600000)); witness ATxStrWitA.v
   tsw_pal_uar_img_cf_TfibA (TxGlue102ImgCheck.pal_uar_img_A) *)
Hypothesis pal_uar_img : @cf_img_lo ci <= as_uar_cell B /\ as_uar_cell B + 4 <= @cf_img_top ci.
(* the CfImg bounds are a low range, and the instance's pa_lo / pa_hi lie inside them (closed image facts at CfImg_A:
   ATxStrWitA.v tsw_cf_img_ok_A / tsw_img_cf_box_A) *)
Hypothesis cf_img_ok : 0 <= @cf_img_lo ci /\ @cf_img_top ci <= 2 ^ 31.
Hypothesis img_cf_box : @cf_img_lo ci <= @pa_lo _ A_prog_listing PA /\ @pa_hi _ A_prog_listing PA <= @cf_img_top ci.
(* ---- frame class 0 (frame_alloc_0): the m-form contract astack_malloc_realizes_xm (YGcallMxmn.v: FCiface.v's
   astack_malloc_realizes_x plus the memnorm keep) and exactly the hypotheses of YGcallMxmn.v's
   aj_stack_malloc_at_xm (= YGcallSx.v's aj_stack_malloc_at_x's); ASM0 / OWNLOW / SMX are discharged by
   tx_string_A_inst below (tsi_asm0 / tsi_ownlow / tsi_smx) ---- *)
Hypothesis ASM0 : YGcallMxmn.astack_malloc_realizes_xm SEGS B ARx 0.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
(* ---- the glue's Section hypotheses (Tx102Glue.v / TxStr102Glue.v) ---- *)
(* the zero-shadow ranges are granule-aligned; witness ATxStrWitA.v tsw_zs_aligned_TfibA *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* MARKED STAND-IN: the shadow byte of every address inside the CfImg bounds is visible, PER-INSTANCE over cf_img_lo
   / cf_img_top (A' CfImg_A: 0x10000 / 0x600000); discharged by tx_string_A_inst below (tsi_isv:
   AImgShadowVisCf.img_shadow_vis_xs_A) *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md ->
  @cf_img_lo ci <= a < @cf_img_top ci ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the callee's text (PRH_FnTx.v's budgeted ttx_put_specX) at the caller's universe closure CTX0; at the instance it is
   tx_string_A_inst's one premise TXPUT_I *)
Variables (CTX0 : list (list Z)).
Hypothesis TXPUT : ttx_put_specX (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
(* MARKED STAND-IN: the program's statics (prh_pst: alloc.c's six and fuzz_preset.c's g_own_ran_out) are not the
   runtime's own statics and not errno, so a runtime call's image
   clause (acall_kept) keeps them; witness ATxStrWitA.v tsw_pal_pst_static_TfibA *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* ---- frame class 0's inline release (A' 0x855d0 / 0x855d4): exactly the hypotheses of YGcallSx.v's
   aj_flag_store_x; ASFX / FFLX / SFX are discharged by tx_string_A_inst below (tsi_asfx / tsi_fflx / tsi_sfx) ---- *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
(* MARKED STAND-IN: the frame's flag byte is present, so the epilogue's flag store has a writable region; discharged
   by tx_string_A_inst below (tsi_fflp: YG0scf.AR_flag_law_ok_cf's first conjunct) *)
Hypothesis FFLP : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
(* MARKED STAND-IN: fake frames are 64-aligned. Needed because esc[] (F + 32, up to 6 bytes) is handed to tx_put,
   whose src_rd asks for the shadow hull of [F + 32, F + 38); the frame's own 8 shadow bytes cover that hull only
   when shadow_addr F is 8-aligned, i.e. F mod 64 = 0 (the base gives only F mod 32 = 0); discharged by
   tx_string_A_inst below (tsi_fal64: Rtt102CKA.ck_frame_al64) *)
Hypothesis FAL64 : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0.
(* ---- the quote .str.25 and the backslash .str.26 (one read-only byte each, its granule's const-shadow cell holding
   2) and tx_string.hex (16 digits in two zero-shadow granules of .rodata). MARKED STAND-IN: witnesses ATxStrWitA.v
   tsw_lit_img_TfibA / tsw_hex_img_TfibA ---- *)
Hypothesis ts_lit_img_A : kept_img (PA := PA) B TS_STR25_A 1 /\ kept_img (PA := PA) B TS_STR26_A 1.
Hypothesis ts_hex_img_A : kept_at (PA := PA) B [] TS_HEX_A 16.
(* the glue's Context facts, at image A', for the implicit arguments a glue lemma leaves after refine / Unshelve *)
Ltac ts_ctx_A := first [exact HSTK_A | exact HSTKP_A | exact pa_hi_ok_A | exact LAWS | exact PAL | exact pal_uar_img
  | exact pst_img_A | exact pst_ro_A | exact pal_pst_static | exact TXPUT | exact zs_aligned | exact img_shadow_vis_x
  | exact img_box_A | exact img_cf_box | exact cf_img_ok | idtac].
(* the flag-store runner at WR: YGcallSx.v's aj_flag_store_xR at image A''s listing, R := WR *)
Definition ts_flag_store_A := aj_flag_store_xR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) ASFX FFLX SFX
  asym (@pa_wx _ _ PA) (clookup (@pa_tbl _ _ PA)) VAL SIGMA A_prog_listing (@pl_tpi _ PL) (@pl_tw _ PL)
  (pa_fetch_ok (PI := PA)) (@pa_cert _ _ PA) (@pa_B_ok _ _ PA) A_LIM A_LIM_text (@pl_lim _ PL) (@pl_len _ PL)
  (@pl_tpi_eq _ PL) (@pl_tw_eq _ PL) WR WRrefl WRtrans.

Section g.
(* ---- the entry: ttx_string_specX's binders and premises ---- *)
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (dw t s k b0 len0 cap0 f0 own0 : Z) (bs txt : list Z) (Lam : list (Z * Z))
  (peak cnt fail ran most : Z).
(* the model-run position the text takes at the entry (PRH_FnTx.v's rp_* binders) *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
  (rp_H0 : list Z) (rp_hist : list YG00.chunk).
(* the run has at most 4 calls, the text's premise; ts_put_call's premise *)
Hypothesis HOS : (length rp_os <= 4)%nat.
#[local] Notation sp0 := (spZ regs).
(* the glue's definitions at this entry *)
#[local] Notation TSks := (@TS_ks bs).
#[local] Notation TSadd := (@TS_add bs).
#[local] Notation FP0a := (@FP0 t b0 cap0).
#[local] Notation sp1 := (@TS_sp1 regs).
#[local] Notation QFa := (@QF fx rc prh_img_A RL SK A_prog_listing PA B ARx ly S Hp W regs mem md dw t s k b0 len0 cap0
  f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0).
#[local] Notation sidea := (@ts_side rc ci prh_img_A RL A_prog_listing PA B ly S Hp W regs mem dw t s k b0 len0 cap0
  f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0).
(* the live state at WR (after the cut B): the glue's ts_liveR, LHa's live state (ts_LH at RCF = WR) *)
#[local] Notation livea := (@ts_liveR rc ci prh_img_A RL SK A_prog_listing PA B ARx ly S Hp W regs mem md dw t s k b0
  len0 cap0 f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0 WR).
#[local] Notation bregsa := (@ts_bregs regs t).
#[local] Notation spilla := (ts_spill (L := A_prog_listing) (PA := PA) (regs := regs)).
(* the loop head at image A' (TS_PC_A + 340, A' 0x85448; s7 = .str.26, s9 = tx_string.hex) and the loop step there:
   STEPa is the glue's ts_loop premise at A' (at RCF = WR) *)
#[local] Notation LHa := (@ts_LH fx rc ci prh_img_A RL SK A_prog_listing PA TS_PC_A TS_LH_OFF_A TS_STR26_A TS_HEX_A B ARx
  ly S Hp W regs mem md dw t s k b0 len0 cap0 f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0).
#[local] Notation STEPa := (forall i Wc cf, LHa i Wc cf ->
  SRW Wc cf (fun W' c' => QFa W' c' \/ exists i', (length bs - i' < length bs - i)%nat /\ LHa i' W' c')).

Hypothesis HPRE : afn_pre_x SEGS B ARx STKS ly S Hp W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem).
Hypothesis HCL : prh_univ_closure (PI := prh_img_A) B CTX0.
Hypothesis HROOM : room_live_cf S.
Hypothesis HPOS : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S.
Hypothesis H10 : getr regs 10 = w64 t.
Hypothesis H11 : getr regs 11 = w64 s.
Hypothesis HFWIN : fwin (PA := PA) ly W regs mem dw.
Hypothesis HPLACE : prhtx_place (PA := PA) ly S W regs mem dw t.
Hypothesis HTRACE : prhtx_trace (PI := prh_img_A) (PA := PA) B ly W mem t.
Hypothesis HREC : prhtx_rec (PA := PA) W mem t b0 len0 cap0 f0.
Hypothesis HINV : prhtx_inv (PA := PA) B Lam ly S W mem b0 len0 cap0 txt.
Hypothesis HSTR : PRH_Reader.pj_cstrR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) s k bs.
Hypothesis HBVIS : prhtx_bvis (PA := PA) W mem s k.
Hypothesis HLEN : len0 + Z.of_nat (length TSadd) + 1 <= 2 ^ 28.
Hypothesis HLED : prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own0.
(* the run premise of the #102 text, guarded by f0 = 0, and fpre's FRM0-ENTRY conjunct; the guarded room and guarded
   consumer window over the same events *)
Hypothesis HEVS : f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 TSks).
Hypothesis HROOMW : f0 = 0 ->
  YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 TSks)) (st_depot S).
Hypothesis HCONS : f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 TSks)).
Hypothesis HFRM : frm_zero (@YK11.fp_csr fx).
Hypothesis HLIVE : blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX.
Hypothesis HMAX : 2 * (len0 + Z.of_nat (length TSadd) + 1) < cf_malloc_max.
Hypothesis HCNT : count_cid 0 (frames S) < fs_frames 0.

(* ---- A: the entry, the prologue, the flag, frame_alloc_0 (A' 0x852f4 .. the `jal` at 0x85364), in continuation
   form: the continuation is segment B's start (ts_B_run_A's premises, at B's seam TS_B_OFF_A), at the state
   frame_alloc_0 hands back (the layout, the heap list and the world of the entry). Segment A frees nothing: it runs
   at wle (its journal handed on at wle, lifted at the cut B, ts_at_B_A) and is lifted ONCE at its top by
   YGcfRhLift.ra_rh_of_SRr. The prologue's relocation entries are stated per listing by the glue's ts_A1_entry; the
   flag test `beqz a2` (0x8535c) is not taken on the walk (flag = 1, ts_A3_entry's fact) ---- *)
Lemma ts_A_cps :
  (forall Sc memc mdc kj pos rg,
     AJ (STKS + dw) (sp0 + dw) FP0a ly S Hp W mem md [(0, pos)] ly Sc Hp W memc mdc kj ->
     sidea ly Sc Hp W memc b0 cap0 f0 own0 [] [] [] ->
     @ts_saved rc A_prog_listing PA regs W memc ->
     rdword (aview SEGS (w_H W) memc) (frame_addr ly 0 pos + 56) = Some (flag_addr ly 0 pos) ->
     (forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> apresent (w_H W) memc a) ->
     getr rg 2 = w64 sp1 -> getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = getr regs 2 ->
     getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr ly 0 pos) -> getr rg 19 = w64 s ->
     getr rg 20 = w64 t -> getr rg 24 = w64 SHADOW_OFF ->
     SRW W (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_B_OFF_A))) memc (seg_rom SEGS)) mdc) QFa) ->
  SRW W (cfg_at SEGS (SIGMA AS_tx_string) regs mem md) QFa.
Proof.
intros HB.
apply (YGcfRhLift.ra_rh_of_SRr SEGS YGcfRehidePost.RZ_cf).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HFWIN as (Hdw0 & Hdw16 & Hdwtop & Hdwpres).
pose proof HSTK_A as HSTK.
assert (HSIDE0 : sidea ly S Hp W mem b0 cap0 f0 own0 [] [] []) by (eapply ts_side_init; eassumption).
destruct (ts_A1_entry (TS_PC := TS_PC_A) (pa_hi_ok := pa_hi_ok_A) (HSTK := HSTK_A) (LAWS := LAWS) (PAL := PAL)
  (img_box := img_box_A) ch HPRE)
  as [HS SHOK].
pose proof (ajournal_x_init_W (SK := SK) SEGS B PST ARx STKS dw FP0a ly S Hp W regs mem md ch HPRE HFWIN) as HJ.
assert (E1a : forall more, ew (TE (L := A_prog_listing) (PA := PA) regs regs more) 2 = getr regs 2)
  by (intros more; apply te_entry; reflexivity).
assert (E64a : ew (TE (L := A_prog_listing) (PA := PA) regs regs [w64 (as_uar_cell B)]) 64 = w64 (as_uar_cell B))
  by exact (te_more_lt (L := A_prog_listing) (PA := PA) regs regs [w64 (as_uar_cell B)] 0 ltac:(lia)).
remember (TE (L := A_prog_listing) (PA := PA) regs regs [w64 (as_uar_cell B)]) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply te_env).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite E1a; reflexivity).
assert (EE : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros r n Hn; subst E; apply te_entry; exact Hn).
pose (RUNTO := paj_run_to_x (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
pose (RUN := paj_run_x (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
unfold cfg_at. rewrite <- TS_PC_val_A.
(* ---- A1: the entry to the flag's load ---- *)
pose proof HS as HSk1.
paj_run_to_tok_x RUNTO HS HJ SHOK (0, 0) (TS_PC_A + TS_A2_OFF_A).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- dw)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* the run's memnorm keep: YGcallMxmn.memnorm_frame_of from the run's start st_ok and its full-memory frame *)
assert (KN1 : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H W) _ _ _ _ _ HSk1 HF); exact Hm).
clear HSk1.
pmkst HS.
prreg HS (12%bv : bv 5) R12. prreg HS (11%bv : bv 5) R11. prreg HS (10%bv : bv 5) R10.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (2%bv : bv 5) R2. prreg HS (19%bv : bv 5) R19.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (ts_region_nth (L := A_prog_listing) (PA := PA) E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof HJ as (HAR1 & _).
set (regs1 := ms_regs ms) in *. set (mem1 := ms_mem ms) in *.
assert (EP2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (H160 : 160 <= sp0) by lia.
assert (X2 : getr regs1 2 = w64 sp1) by (rewrite R2, EP2; exact (ts_sp1_word (regs := regs) H160)).
assert (X9 : getr regs1 9 = w64 sp1)
  by (rewrite R9, EP2, (ts_sp1_word (regs := regs) H160); apply ts_add0_word).
assert (X8 : getr regs1 8 = getr regs 2) by (rewrite R8; exact EP2).
assert (X10 : getr regs1 10 = w64 t) by (rewrite R10, (EE 10%bv 10%nat) by reflexivity; exact H10).
assert (X19 : getr regs1 19 = w64 s) by (rewrite R19, (EE 11%bv 11%nat) by reflexivity; exact H11).
assert (X3 : getr regs1 3 = getr regs 3) by (rewrite R3; apply EE; reflexivity).
assert (X4 : getr regs1 4 = getr regs 4) by (rewrite R4; apply EE; reflexivity).
assert (X11 : getr regs1 11 = w64 (VAL (A_OBJ 12)))
  by (rewrite R11, HEdef; apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (X12 : getr regs1 12 = w64 (as_uar_cell B)) by (rewrite R12; exact E64a).
assert (HSV : ts_saved (L := A_prog_listing) (PA := PA) (regs := regs) W mem1).
{ intros j Hj. do 13 (destruct j as [|j]; [
    lazymatch goal with |- val_mem _ _ _ _ (bv_unsigned (getr regs (nth ?jj TS_SAVED 0%bv))) =>
      let r := eval vm_compute in (nth jj TS_SAVED 0%bv) in
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      let off := eval vm_compute in (- 8 * (Z.of_nat jj + 1)) in
      pose proof (ts_field (L := A_prog_listing) (PA := PA) E _ 2 sp0 _ _ _ _ _ off 8 (SOff n 0) HR0 Usp
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; change (N.to_nat 8) with 8%nat in V;
      rewrite ts_U_atom_mod, (EE r n) in V by reflexivity;
      change (nth jj TS_SAVED 0%bv) with r;
      replace (sp0 - 8 * (Z.of_nat jj + 1)) with (sp0 + off) by (cbn; lia); exact V
    end |]). lia. }
rename HFr into HFr1. clear HF HG.
(* ---- A2: the flag's load ---- *)
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR1) as (Kcell1 & Kuar1 & _ & _).
rewrite (pal_cell (PI := PA) B PAL) in Kcell1.
destruct (ts_A2_entry (TS_PC := TS_PC_A) (TS_A2_OFF := TS_A2_OFF_A) (pal_uar_img := pal_uar_img)
  (cf_img_ok := cf_img_ok) (regs := regs) regs1 mem1 W X12 Kuar1) as [HS2 SHOK2].
clear HS SHOK.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?n)] => change (BASE + n) with (BASE + (TS_PC_A + TS_A2_OFF_A)) end.
assert (HEI2 : img_env VAL A_LIM (TE (L := A_prog_listing) (PA := PA) regs regs1 [])) by apply te_env.
pose proof HS2 as HSk2.
paj_run_to_tok_x RUNTO HS2 HJ SHOK2 (0, 0) (TS_PC_A + TS_A3_OFF_A).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KN2 : YAkMemnorm.memnorm SEGS mem1 -> YAkMemnorm.memnorm SEGS (ms_mem ms0))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H W) _ _ _ _ _ HSk2 HF); exact Hm).
clear HSk2.
pmkst HS2.
set (regs2 := ms_regs ms0) in *. set (mem2 := ms_mem ms0) in *.
pose proof HJ as (HAR2 & _).
prreg HS2 (12%bv : bv 5) Q12.
assert (Y : forall (r : bv 5), In r [2; 3; 4; 8; 9; 10; 11; 19]%bv -> getr regs2 r = getr regs1 r).
{ intros r Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?rr = _ => let HH := fresh "HH" in prreg HS2 rr HH; unfold regs2; rewrite HH; te_close end |]).
  destruct Hr. }
rename HFr into HFr2. clear HF HG.
(* ---- A3: the shadow base's load, the flag test, to the frame call ---- *)
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR2) as (Kcell2 & _ & _ & _).
rewrite (pal_cell (PI := PA) B PAL) in Kcell2.
destruct (ts_A3_entry (TS_PC := TS_PC_A) (TS_A3_OFF := TS_A3_OFF_A) (pa_hi_ok := pa_hi_ok_A) (cf_img_ok := cf_img_ok)
  (img_cf_box := img_cf_box) (regs := regs)
  regs2 mem2 W ltac:(rewrite (Y 11%bv) by (cbv; tauto); exact X11) Q12 Kcell2) as [HS3 SHOK3].
clear HS2 SHOK2.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?n)] => change (BASE + n) with (BASE + (TS_PC_A + TS_A3_OFF_A)) end.
assert (HEI3 : img_env VAL A_LIM (TE (L := A_prog_listing) (PA := PA) regs regs2 [w64 SHADOW_OFF])) by apply te_env.
pose proof HS3 as HSk3.
paj_run_tok_x RUN HS3 HJ SHOK3 (0, 0).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KN3 : YAkMemnorm.memnorm SEGS mem2 -> YAkMemnorm.memnorm SEGS (ms_mem ms1))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H W) _ _ _ _ _ HSk3 HF); exact Hm).
clear HSk3.
set (regs3 := ms_regs ms1) in *. set (mem3 := ms_mem ms1) in *.
pose proof HJ as (HAR3 & _).
assert (Y3 : forall (r : bv 5), In r [2; 3; 4; 8; 9; 19]%bv -> getr regs3 r = getr regs2 r).
{ intros r Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?rr = _ => let HH := fresh "HH" in prreg HS3 rr HH; unfold regs3; rewrite HH; te_close end |]).
  destruct Hr. }
prreg HS3 (20%bv : bv 5) Z20.
prreg HS3 (24%bv : bv 5) Z24. prreg HS3 (1%bv : bv 5) Z1.
rename HFr into HFr3. clear HF HG.
(* the registers at the call *)
assert (T2 : getr regs3 2 = w64 sp1)
  by (rewrite (Y3 2%bv) by (cbv; tauto); rewrite (Y 2%bv) by (cbv; tauto); exact X2).
assert (T3 : getr regs3 3 = getr regs 3)
  by (rewrite (Y3 3%bv) by (cbv; tauto); rewrite (Y 3%bv) by (cbv; tauto); exact X3).
assert (T4 : getr regs3 4 = getr regs 4)
  by (rewrite (Y3 4%bv) by (cbv; tauto); rewrite (Y 4%bv) by (cbv; tauto); exact X4).
assert (T8 : getr regs3 8 = getr regs 2)
  by (rewrite (Y3 8%bv) by (cbv; tauto); rewrite (Y 8%bv) by (cbv; tauto); exact X8).
assert (T9 : getr regs3 9 = w64 sp1)
  by (rewrite (Y3 9%bv) by (cbv; tauto); rewrite (Y 9%bv) by (cbv; tauto); exact X9).
assert (T19 : getr regs3 19 = w64 s)
  by (rewrite (Y3 19%bv) by (cbv; tauto); rewrite (Y 19%bv) by (cbv; tauto); exact X19).
assert (T20 : getr regs3 20 = w64 t)
  by (unfold regs3; rewrite Z20; rewrite (te_cur regs regs2 _ 10%bv 10) by reflexivity;
      rewrite (Y 10%bv) by (cbv; tauto); exact X10).
assert (T24 : getr regs3 24 = w64 SHADOW_OFF)
  by (unfold regs3; rewrite Z24; exact (te_more_lt regs regs2 [w64 SHADOW_OFF] 0 ltac:(lia))).
(* the realigned frame base *)
assert (HR : sp0 - 176 <= sp1 <= sp0 - 160 /\ sp1 mod 32 = 0).
{ unfold TS_sp1. pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)).
  assert ((sp0 - 160) mod 32 = 0 \/ (sp0 - 160) mod 32 = 16) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
  split; [lia | apply Z.mod_mul; lia]. }
(* memory: the three runs wrote only the probe slot and the saves, below the entry sp *)
assert (K1 : forall x : word, ~ (sp0 - 160 <= bv_unsigned x < sp0) ->
  mrestrict (w_H W) mem1 x = mrestrict (w_H W) mem x).
{ intros x Hx. apply HFr1. intros (r & Hin & Hr). vm_compute in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia |]).
  destruct Hin. }
assert (K2 : forall x : word, mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem1 x).
{ intros x. apply HFr2. intros (r & Hin & Hr). vm_compute in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]). destruct Hin. }
assert (K3 : forall x : word, mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem2 x).
{ intros x. apply HFr3. intros (r & Hin & Hr). vm_compute in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]). destruct Hin. }
assert (K13 : forall x : word, mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem1 x) by (intros x; rewrite K3, K2; reflexivity).
assert (KA13 : forall a, aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem1 a)
  by (intros a; unfold aview, mbyte; rewrite K13; reflexivity).
(* the side facts after the three runs *)
assert (HSIDE3 : sidea ly S Hp W mem3 b0 cap0 f0 own0 [] [] []).
{ apply (ts_side_run (L := A_prog_listing) (PA := PA) (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A)
    (pal_pst_static := pal_pst_static) ly S Hp W mem mem3 _ b0 cap0 f0 own0 [] [] []
    (fun a => sp0 - 160 <= a < sp0) HSIDE0 HAR3).
  - unfold alloc_ceiling in *. lia.
  - exact Hdwtop.
  - lia.
  - intros a Ha. split; [|lia].
    destruct (Hdwpres a Ha) as [Hh [bb Hb]]. split; [exact Hh|]. exists bb.
    pose proof (K13 (Z_to_bv 64 a)) as E13.
    pose proof (K1 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia)) as E1.
    unfold mrestrict in E13, E1. rewrite Hh in E13, E1. rewrite E13, E1. exact Hb.
  - intros x Hx. rewrite K13. exact (K1 x Hx).
  - intros a Ha. left. lia.
  - intros Hm. exact (KN3 (KN2 (KN1 Hm))). }
pmkst HS3. rewrite pal_stack_malloc0. fold regs3 mem3.
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_stack_malloc_at_xm SEGS B PST ARx LAWS Hsegs (pal_env (PI := PA) B PAL) OWNLOW SMX 0 ASM0 ltac:(lia)
    W _ _ (STKS + dw) (sp0 + dw) FP0a ly S Hp W mem md [] ly S Hp _ _
    (sp1 - (sp0 + dw)) (Z_to_bv 64 (BASE + (TS_PC_A + TS_B_OFF_A)))).
  - exact HJ.
  - unfold spZ at 1. rewrite T2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - assert (H16 : sp1 mod 16 = 0) by lia.
    rewrite Zminus_mod, Zplus_mod, Hal16, Hdw16, H16. reflexivity.
  - lia.
  - unfold ESTACK in *. lia.
  - rewrite T3. exact Hgp.
  - rewrite T4. exact Htp.
  - unfold regs3. rewrite Z1. first [reflexivity | f_equal; f_equal; vm_compute; reflexivity].
  - apply ret_ok_codeptr_v;
      [let v := eval vm_compute in (TS_PC_A + TS_B_OFF_A) in change (TS_PC_A + TS_B_OFF_A) with v; lia | reflexivity].
  - exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & rg & mem4 & md4 & pos & Hc2 & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hfresh & Hnev2 &
  Hbb2 & Hz & Hflag & Hfpres & HKept & HJt & Hsetfs & HMN4).
rewrite Hc2.
destruct HKept as (KC1 & KC2 & KC3 & KC4 & KC5 & _).
assert (KT : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KC1; [unfold alloc_ceiling in *; lia | lia]. }
pose proof HJ2 as (HAR4 & _).
assert (FB : fs_frame_bytes 0 = 64) by reflexivity.
rewrite FB in Hflag, Hfpres.
(* presence of the caller window at the call's start *)
assert (PW3 : forall a, sp0 <= a < sp0 + dw -> apresent (w_H W) mem3 a).
{ intros a Ha. destruct (Hdwpres a Ha) as [Hh [bb Hb]]. split; [exact Hh|]. exists bb.
  pose proof (K13 (Z_to_bv 64 a)) as E13.
  pose proof (K1 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia)) as E1.
  unfold mrestrict in E13, E1. rewrite Hh in E13, E1. rewrite E13, E1. exact Hb. }
(* the continuation (segment B on): SRW, under the top lift's plain SRr *)
apply SRr_ret. cbv beta.
apply (HB S2 mem4 md4 0 pos rg).
- exact HJ2.
- apply (ts_side_move (L := A_prog_listing) (PA := PA) (LAWS := LAWS) (pst_img := pst_img_A)
    (pal_pst_static := pal_pst_static) ly S Hp W mem3 ly S2 mem4 md4 b0 cap0 f0 own0 [] [] [] HSIDE3 HAR4 eq_refl Eab
    Hbb2).
  + right. exact Hsetfs.
  + exact Hdwtop.
  + intros a Ha. split; [|lia]. apply KC5; [unfold alloc_ceiling in *; lia | lia | exact (PW3 a Ha)].
  + intros a Ha. apply KT. lia.
  + intros p n i Hin Hi. apply (KC2 p n i Hin Hi). intros [].
  + intros a Hi Ho He. apply KC3; assumption.
  + exact HMN4.
- intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros jj Hjj. rewrite KT by lia. rewrite KA13. reflexivity.
- replace (frame_addr ly 0 pos + 56) with (frame_addr ly 0 pos + 64 - 8) by lia. exact Hflag.
- exact Hfpres.
- assert (P : getr rg 2%bv = getr regs3 2%bv) by exact (HP2 2 ltac:(unfold acallee_saved; lia)). rewrite P. exact T2.
- assert (P : getr rg 3%bv = getr regs3 3%bv) by exact (HP2 3 ltac:(unfold acallee_saved; lia)). rewrite P. exact T3.
- assert (P : getr rg 4%bv = getr regs3 4%bv) by exact (HP2 4 ltac:(unfold acallee_saved; lia)). rewrite P. exact T4.
- assert (P : getr rg 8%bv = getr regs3 8%bv) by exact (HP2 8 ltac:(unfold acallee_saved; lia)). rewrite P. exact T8.
- assert (P : getr rg 9%bv = getr regs3 9%bv) by exact (HP2 9 ltac:(unfold acallee_saved; lia)). rewrite P. exact T9.
- exact Ha0.
- assert (P : getr rg 19%bv = getr regs3 19%bv) by exact (HP2 19 ltac:(unfold acallee_saved; lia)). rewrite P. exact T19.
- assert (P : getr rg 20%bv = getr regs3 20%bv) by exact (HP2 20 ltac:(unfold acallee_saved; lia)). rewrite P. exact T20.
- assert (P : getr rg 24%bv = getr regs3 24%bv) by exact (HP2 24 ltac:(unfold acallee_saved; lia)). rewrite P. exact T24.
Qed.

(* ---- B: after frame_alloc_0 (A' 0x85368): `j` to 0x85370, `mv a4, a0`, the frame test `bnez a0` (F <> 0, taken to
   0x85394), F to sp1 + 16 (`sd a0, 16(s1)`) and sp1 + 48 (`sd a4, 48(s1)`), the fake frame's header (F + 0 / + 8 /
   + 16) with F to sp1 + 24 (`sd a4, 24(s1)`, 0x853c4) between its stores, F's 8 shadow bytes (f1 f1 f1 f1 f8 f3 f3
   f3), a0 = t, a1 = .str.25, a2 = 1, to the opening quote's `jal tx_put` (0x85408). F lives in a0 / a4 only (both
   caller-saved), so the call state hands segment C the spill, not a register. Regions: s1's slots [sp1 + 16, sp1 +
   56), the header [F, F + 24), F's shadow (atom 64, aliased to `(F >> 3) + s8`), all writable ---- *)
Definition ss_Ba : sstate := mkSS (TS_PC_A + TS_B_OFF_A) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 16 56 16 56 [];
    YP09.mkRegion (Some (xr 10)) 0 24 0 24 [];
    YP09.mkRegion (Some 64%nat) 0 8 0 8 [] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 10, mkAF 4096 (2 ^ 47) 5); (xr 24, mkAF SHADOW_OFF SHADOW_OFF 0);
            (64%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)] []
           [(SAlu ALU_ADD (SAlu ALU_SRL (SOff (xr 10) 0) (SLit 3)) (SOff (xr 24) 0), SOff 64 0)]).
(* B's start state from concrete facts: s1 = sp1, a0 = F, s8 = the shadow base, atom 64 = F's shadow pointer *)
Lemma ts_B_entry_A : forall lyc Sc Hpc Wc memc mdc pos rg,
  ARx lyc Sc Hpc Wc memc mdc -> In (0, pos) (frames Sc) ->
  (forall a, frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64 -> apresent (w_H Wc) memc a) ->
  (forall a, sp1 + 16 <= a < sp1 + 56 -> apresent (w_H Wc) memc a) ->
  YM05.alloc_ceiling <= sp1 -> sp1 + 64 <= 2 ^ 47 ->
  getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr lyc 0 pos) -> getr rg 24 = w64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (TE (L := A_prog_listing) (PA := PA) regs rg [w64 (shadow_addr (frame_addr lyc 0 pos))]) ss_Ba
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_B_OFF_A))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE (L := A_prog_listing) (PA := PA) regs rg [w64 (shadow_addr (frame_addr lyc 0 pos))])
    (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Hpc Wc memc mdc pos rg HAR Hin Hfp Hsp Hc Hc47' R9 R10 R24.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HAR Hin) as (F1 & F2 & F3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HAR Hin) as (F32 & _ & _ & Fsh).
change (fs_frame_bytes 0) with 64 in F2, F3, Fsh.
set (F := frame_addr lyc 0 pos) in *.
set (E := TE (L := A_prog_listing) (PA := PA) regs rg [w64 (shadow_addr F)]).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X10 : bv_unsigned (ew E (xr 10)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. apply unsigned_lit_small. lia. }
assert (X24 : bv_unsigned (ew E (xr 24)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 24%bv 24) by reflexivity. rewrite R24. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (Hsh2 : SHADOW_OFF <= shadow_addr F <= SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (Hsh : 0 <= shadow_addr F < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (X64 : bv_unsigned (ew E 64) = shadow_addr F).
{ unfold E. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
unfold SHADOW_OFF in Hsh2.
split.
- apply ts_st_ok.
  all: try change (TE (L := A_prog_listing) (PA := PA) regs rg [w64 (shadow_addr F)]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hsp. lia.
    * apply (ts_rok E _ (xr 10) F); [exact X10 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hfp. lia.
    * apply (ts_rok E _ 64 (shadow_addr F)); [exact X64 | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Fsh o ltac:(lia))).
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X10, X64.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X10, X24, X64.
      unfold TS_sp1 in *. change (2 ^ 5) with 32. change (2 ^ 0) with 1.
      unfold shadow_addr, SHADOW_OFF. repeat split; try lia.
    * cbn [f_alias alias_ok]. split; [|exact I].
      apply (ts_alias_shadow E (xr 10) (xr 24) 64 F X10 X24 X64). lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* segment B's run, in continuation form, at the state ts_A_cps hands over (lyc = ly, Hpc = Hp, Wc = W), after the
   cut B's lift: its journal at WR, the run at WR; the continuation receives the call state at the opening `jal
   tx_put` (A' 0x85408) with everything the glue's tx_put call rule (TxStr102Glue.v ts_put_call) asks, and the spill
   (F at sp1 + 16 and sp1 + 24), read off the run's final s1 chunks *)
Lemma ts_B_run_A : forall Sc memc mdc kj pos rg,
  AJR (STKS + dw) (sp0 + dw) FP0a ly S Hp W mem md [(0, pos)] ly Sc Hp W memc mdc kj ->
  sidea ly Sc Hp W memc b0 cap0 f0 own0 [] [] [] ->
  ts_saved (L := A_prog_listing) (PA := PA) (regs := regs) W memc ->
  rdword (aview SEGS (w_H W) memc) (frame_addr ly 0 pos + 56) = Some (flag_addr ly 0 pos) ->
  (forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> apresent (w_H W) memc a) ->
  getr rg 2 = w64 sp1 -> getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = getr regs 2 ->
  getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr ly 0 pos) -> getr rg 19 = w64 s ->
  getr rg 20 = w64 t -> getr rg 24 = w64 SHADOW_OFF ->
  (forall E ss ms mdc' kj',
     st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_put ->
     bv_unsigned (ew E 2) = sp0 ->
     AJR (STKS + dw) (sp0 + dw) FP0a ly S Hp W mem md [(0, pos)] ly Sc Hp W (ms_mem ms) mdc' kj' ->
     sidea ly Sc Hp W (ms_mem ms) b0 cap0 f0 own0 [] [] [] ->
     ts_saved (L := A_prog_listing) (PA := PA) (regs := regs) W (ms_mem ms) ->
     rdword (aview SEGS (w_H W) (ms_mem ms)) (frame_addr ly 0 pos + 56) = Some (flag_addr ly 0 pos) ->
     ts_bregs (regs := regs) (t := t) (ms_regs ms) ->
     spilla W (ms_mem ms) (frame_addr ly 0 pos) ->
     getr (ms_regs ms) 19 = w64 s -> getr (ms_regs ms) 26 = w64 (shadow_addr (frame_addr ly 0 pos)) ->
     getr (ms_regs ms) 10 = w64 t -> getr (ms_regs ms) 11 = w64 TS_STR25_A -> getr (ms_regs ms) 12 = w64 1 ->
     getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (TS_PC_A + TS_C_OFF_A)) ->
     SRW W (mkCfg ms mdc') QFa) ->
  SRW W (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_B_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Proof.
intros Sc memc mdc kj pos rg HJ HSD HSV Hfl Hfp R2 R3 R4 R8 R9 R10 R19 R20 R24 HK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof HFWIN as (Hdw0 & Hdw16 & Hdwtop & Hdwpres).
pose proof HSTK_A as HSTK.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_frs HJ) as HFRc. pose proof (ajxR_pres HJ) as HPRc.
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (ts_sp1_range (regs := regs) Hal16 ltac:(lia)) as [Hsp1r Hsp1m].
destruct (ts_B_entry_A ly Sc Hp W memc mdc pos rg HARc Hin Hfp ltac:(intros a Ha; apply HPRc; lia)
  ltac:(unfold alloc_ceiling in *; lia) ltac:(lia) R9 R10 R24) as [HS SHOK].
destruct (frames_bounds_x _ _ _ LAWS ly Sc Hp W memc mdc 0 pos HARc Hin) as (F1 & F2 & F3).
change (fs_frame_bytes 0) with 64 in F2, F3.
set (F := frame_addr ly 0 pos) in *.
assert (Hsh : 0 <= shadow_addr F < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (Hshr : SHADOW_OFF <= shadow_addr F <= SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
set (E := TE (L := A_prog_listing) (PA := PA) regs rg [w64 (shadow_addr F)]) in *.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X10 : bv_unsigned (ew E (xr 10)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. apply unsigned_lit_small. lia. }
assert (X64 : bv_unsigned (ew E 64) = shadow_addr F).
{ unfold E. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth]. apply unsigned_lit_small. exact Hsh. }
pose (RUN := paj_run_xR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WR WRrefl WRtrans).
pose proof HS as HSk.
paj_run_tok_xR RUN HS HJ SHOK (0, 0).
{ cbv [ss_Ba ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - (sp0 + dw))); [reflexivity | lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 10) F); [reflexivity | exact X10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 64%nat (shadow_addr F)); [reflexivity | exact X64 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 0, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. fold F. lia. }
  apply awr_ok_nil. }
assert (KN : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H W) _ _ _ _ _ HSk HF); exact Hm).
clear HSk.
pose proof (ajxR_ar HJ) as HARn. pose proof (ajxR_pres HJ) as HPRn.
(* the run's writes: s1's slots, the header, F's shadow *)
assert (HWR : forall a, in_wrange E (ss_mem ss_Ba) a ->
  (sp1 + 16 <= a < sp1 + 56) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 8)).
{ intros a (r & Hin' & Hr). cbv [ss_Ba ss_mem] in Hin'.
  destruct Hin' as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?X9, ?X10, ?X64 in Hr; lia. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 16 <= a < sp1 + 56) -> ~ (F <= a < F + 24) ->
  ~ (shadow_addr F <= a < shadow_addr F + 8) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha N1 N2 N3. apply (ts_keep (L := A_prog_listing) (PA := PA) W E (ss_mem ss_Ba) memc (ms_mem ms)
    (fun a => (sp1 + 16 <= a < sp1 + 56) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 8)) HFr HWR a Ha).
  intros [H|[H|H]]; contradiction. }
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (26%bv : bv 5) Q26.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (24%bv : bv 5) Q24.
(* the spill: the run's stores of a0 = F at sp1 + 16 (0x85394) and of a4 = F at sp1 + 24 (0x853c4), read off the
   final state's s1 chunks (region 0; the chunk is found by its offset, whatever the list's order) *)
pose proof (ts_region_nth_c (L := A_prog_listing) (PA := PA) E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (ts_field (L := A_prog_listing) (PA := PA) E _ (xr 9) sp1 _ _ _ _ _ 16 8 (SOff (xr 10) 0) HR0 X9
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V16.
pose proof (ts_field (L := A_prog_listing) (PA := PA) E _ (xr 9) sp1 _ _ _ _ _ 24 8 (SOff (xr 10) 0) HR0 X9
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V24.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V16, V24. change (N.to_nat 8) with 8%nat in V16, V24.
rewrite ts_U_atom_mod, X10 in V16. rewrite ts_U_atom_mod, X10 in V24.
assert (HSP : spilla W (ms_mem ms) F) by exact (conj V16 V24).
clear HR0 V16 V24.
eapply (HK E _ ms _ _ HS).
- reflexivity.
- reflexivity.
- unfold E. rewrite (te_entry regs rg _ 2%bv 2) by reflexivity. reflexivity.
- exact HJ.
- apply (ts_side_run (L := A_prog_listing) (PA := PA) (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A)
    (pal_pst_static := pal_pst_static) ly Sc Hp W memc (ms_mem ms) _ b0 cap0 f0 own0 [] [] []
    (in_wrange E (ss_mem ss_Ba)) HSD HARn).
  + unfold alloc_ceiling in *. lia.
  + exact Hdwtop.
  + lia.
  + intros a Ha. split; [apply HPRn; lia | lia].
  + intros x Hx. exact (HFr x Hx).
  + intros a Ha. destruct (HWR a Ha) as [H|[H|H]].
    * left. lia.
    * right. exists pos. split; [exact Hin|]. left. unfold in_zr, frame_rng. cbn [fst snd].
      change (fs_frame_bytes 0) with 64. fold F. lia.
    * right. exists pos. split; [exact Hin|]. right. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes 0 / 8) with 8. fold F. lia.
  + exact KN.
- intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros jj Hjj.
  apply KB; unfold shadow_addr, SHADOW_OFF in *; lia.
- rewrite <- Hfl. apply ts_rdword_keep. intros j Hj.
  apply KB; unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia.
- unfold ts_bregs. repeat split.
  + rewrite Q2. unfold E. rewrite (te_cur regs rg _ 2%bv 2) by reflexivity. exact R2.
  + rewrite Q3. unfold E. rewrite (te_cur regs rg _ 3%bv 3) by reflexivity. exact R3.
  + rewrite Q4. unfold E. rewrite (te_cur regs rg _ 4%bv 4) by reflexivity. exact R4.
  + rewrite Q8. unfold E. rewrite (te_cur regs rg _ 8%bv 8) by reflexivity. exact R8.
  + rewrite Q9. unfold E. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. exact R9.
  + rewrite Q20. unfold E. rewrite (te_cur regs rg _ 20%bv 20) by reflexivity. exact R20.
  + rewrite Q24. unfold E. rewrite (te_cur regs rg _ 24%bv 24) by reflexivity. exact R24.
- exact HSP.
- rewrite Q19. unfold E. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. exact R19.
- rewrite Q26. unfold E. rewrite (te_more_lt regs rg _ 0) by lia. reflexivity.
- rewrite Q10. unfold E. rewrite (te_cur regs rg _ 20%bv 20) by reflexivity. exact R20.
- rewrite Q11. unfold E. rewrite te_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite unsigned_lit_small by (apply pa_val_range). reflexivity.
- rewrite Q12. reflexivity.
- rewrite Q1. first [reflexivity | f_equal; f_equal; vm_compute; reflexivity].
Qed.

(* ---- C: after the opening quote (A' 0x8540c): the inline check of s (0x8540c .. 0x85418, slow block 0x8563c,
   report site 0x85648), the first byte (`lbu a1, 0(s3)`), `beqz a1` to the closing block X (0x85580) or the loop
   setup (`ld a0, 24(s1)`: F read back from the spill, s6 = F + 32, s5 = s + 1, s2 = 92, s11 = 48, s9 = hex, s7 =
   .str.26) to the loop head (0x85448). A' has no UBSan test of s and writes nothing here. Regions: s1's spill slot
   sp1 + 24 (atom 64 = F) and the string's first byte (atom 65), both read-only ---- *)
Definition ss_Ca : sstate := mkSS (TS_PC_A + TS_C_OFF_A) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 64 0))];
    YP09.mkRegion (Some (xr 19)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 65 0))] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 19, mkAF 4096 (2 ^ 47 - 8) 3); (xr 24, mkAF SHADOW_OFF SHADOW_OFF 0);
            (64%nat, mkAF 4096 (2 ^ 47) 5); (65%nat, mkAF 0 255 0)] [] []).
Lemma ts_C_entry_A : forall (Wc : world SEGS) memc rg F c0,
  getr rg 9 = w64 sp1 -> getr rg 19 = w64 s -> getr rg 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 -> sp1 + 32 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= s -> s + 1 <= sp1 -> s mod 8 = 0 ->
  4096 <= F <= 2 ^ 47 -> F mod 32 = 0 -> 0 <= c0 < 256 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1 + 24) 8 F ->
  val_mem SEGS (mrestrict (w_H Wc) memc) s 1 c0 ->
  st_ok_pi SEGS VAL (TEa regs rg [w64 F; w64 c0]) ss_Ca
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_C_OFF_A))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SOff (xr 24) 0) [] (TEa regs rg [w64 F; w64 c0]) (mrestrict (w_H Wc) memc).
Proof.
intros Wc memc rg F c0 R9 R19 R24 H1 H2 H3 H4 H5 H6 H7 H8 H9 VF Vc.
set (E := TEa regs rg [w64 F; w64 c0]).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X19 : bv_unsigned (ew E (xr 19)) = s).
{ unfold E, xr. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. rewrite R19. apply unsigned_lit_small. lia. }
assert (X24 : bv_unsigned (ew E (xr 24)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 24%bv 24) by reflexivity. rewrite R24. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (E64 : ew E 64 = w64 F)
  by exact (te_more_lt (L := A_prog_listing) (PA := PA) regs rg [w64 F; w64 c0] 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 c0)
  by exact (te_more_lt (L := A_prog_listing) (PA := PA) regs rg [w64 F; w64 c0] 1 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = F) by (rewrite E64; apply unsigned_lit_small; lia).
assert (X65 : bv_unsigned (ew E 65) = c0) by (rewrite E65; apply unsigned_lit_small; lia).
split.
- apply ts_st_ok.
  all: try change (TEa regs rg [w64 F; w64 c0]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 24 8 (SOff 64 0) F);
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact VF.
    * apply (ts_rok E _ (xr 19) s); [exact X19 | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 0 1 (SOff 65 0) c0);
        [cbn [sv_denot]; rewrite E65, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vc.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X19, X24, X64, X65.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1. repeat split; lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- the model at the end: the calls' sizes and the text appended ---- *)
Lemma ts_ks_fin_A : TxModel.plen (ts_pieces bs) ++ [1] = TSks.
Proof. unfold TS_ks. rewrite s10s_ks. reflexivity. Qed.
Lemma ts_add_fin_A : concat (ts_pieces bs) ++ [34] = TSadd.
Proof.
unfold TS_add. rewrite <- s10_strp_wstr. unfold ts_pieces, TxModel.strp. cbn [concat]. rewrite concat_app.
cbn [concat]. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

(* ---- G: after the closing quote (A' 0x85594): the frame's retire (`sd` of 0x45e0360e at F + 0), `ld a1, 16(s1);
   beqz a1` (not taken: F <> 0), its shadow (eight `sb` of f5 at s10 .. s10 + 7), the flag store (`ld a0, 56(a1); sb
   zero, 0(a0)`, 0x855d0 / 0x855d4), the epilogue (`addi sp, s0, -160` at 0x855fc .. `ret`). Registers: gp, tp pinned
   to the entry's, s0 to the entry sp (atom 2). Regions: s1's slots (F), the frame's first word (writable) and its
   flag pointer (F + 56, atom 65), the frame's shadow (writable), the flag byte (writable), the prologue's saves below
   the entry sp (the entry registers) ---- *)
Definition sr_G_A : list sv := sr_set (sr_set (sr_set cur_atoms 3%bv (SOff 3 0)) 4%bv (SOff 4 0)) 8%bv (SOff 2 0).
Definition G_saves_A : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
   YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
   YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-104) (CVal 8 (SOff 27 0))].
Definition ss_Ga : sstate := mkSS (TS_PC_A + TS_G_OFF_A) sr_G_A
  [ YP09.mkRegion (Some (xr 9)) 16 32 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 64 0)); YP09.mkChunk 24 (CVal 8 (SOff 64 0))];
    YP09.mkRegion (Some 64%nat) 0 64 0 8 [YP09.mkChunk 56 (CVal 8 (SOff 65 0))];
    YP09.mkRegion (Some (xr 26)) 0 8 0 8 [];
    YP09.mkRegion (Some 65%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 2%nat) (-104) 0 0 0 G_saves_A ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (64%nat, mkAF 4096 (2 ^ 47) 5);
            (xr 26, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (65%nat, mkAF 0 (2 ^ 47) 0);
            (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Lemma ts_G_entry_A : forall (Wc : world SEGS) memc rg F fl,
  getr rg 9 = w64 sp1 -> getr rg 26 = w64 (shadow_addr F) ->
  getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = getr regs 2 ->
  2 ^ 46 <= sp1 -> sp1 + 32 <= sp0 - 104 -> sp1 mod 32 = 0 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  4096 <= F -> F + 64 <= sp1 -> F mod 32 = 0 -> in_app F 64 ->
  0 <= fl -> fl + 1 <= sp1 -> (fl + 1 <= F \/ F + 64 <= fl) ->
  (fl + 1 <= shadow_addr F \/ shadow_addr F + 8 <= fl) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1 + 16) 8 F -> val_mem SEGS (mrestrict (w_H Wc) memc) (sp1 + 24) 8 F ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (F + 56) 8 fl ->
  @ts_saved rc A_prog_listing PA regs Wc memc ->
  (forall a, F <= a < F + 8 -> apresent (w_H Wc) memc a) ->
  (forall a, shadow_addr F <= a < shadow_addr F + 8 -> apresent (w_H Wc) memc a) ->
  apresent (w_H Wc) memc fl ->
  st_ok_pi SEGS VAL (TEa regs rg [w64 F; w64 fl]) ss_Ga
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_G_OFF_A))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TEa regs rg [w64 F; w64 fl]) (mrestrict (w_H Wc) memc).
Proof.
intros Wc memc rg F fl R9 R26 R3 R4 R8 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 V16 V24 VFL HSV PF PSH PFL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := TEa regs rg [w64 F; w64 fl]).
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (Hsh' := Hsh). unfold SHADOW_OFF in Hsh'.
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X26 : bv_unsigned (ew E (xr 26)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
assert (E64 : ew E 64 = w64 F) by exact (te_more_lt regs rg [w64 F; w64 fl] 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 fl) by exact (te_more_lt regs rg [w64 F; w64 fl] 1 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = F) by (rewrite E64; apply unsigned_lit_small; lia).
assert (X65 : bv_unsigned (ew E 65) = fl) by (rewrite E65; apply unsigned_lit_small; lia).
assert (X2 : bv_unsigned (ew E 2) = sp0) by (unfold E; rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
assert (EN : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros r n Hn; unfold E; apply te_entry; exact Hn).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TEa regs rg [w64 F; w64 fl]) with E.
- unfold sr_G_A.
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 2%bv 2%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R8].
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 4%bv 4%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R4].
  apply YI04.regs_ok_pin; [apply te_regs_ok | intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 3%bv 3%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R3].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 16 8 (SOff 64 0) F);
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact V16.
    * apply (ts_chunk E _ _ 24 8 (SOff 64 0) F);
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact V24.
  + apply (ts_rok E _ 64 F); [exact X64 | lia | lia | intros o Ho; apply (apresent_writable SEGS); apply PF; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 56 8 (SOff 65 0) fl);
      [cbn [sv_denot]; rewrite E65, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    exact VFL.
  + apply (ts_rok E _ (xr 26) (shadow_addr F)); [exact X26 | lia | lia |
      intros o Ho; apply (apresent_writable SEGS); apply PSH; lia | constructor].
  + apply (ts_rok E _ 65 fl); [exact X65 | lia | lia | intros o Ho; apply (apresent_writable SEGS);
      replace (fl + o) with fl by lia; exact PFL | constructor].
  + apply (ts_rok E _ 2 sp0); [exact X2 | lia | lia | intros o Ho; lia |].
    unfold G_saves_A. repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let j := eval vm_compute in (Z.to_nat (- off / 8 - 1)) in
      let r := eval vm_compute in (nth j TS_SAVED 0%bv) in
      apply (ts_chunk E _ _ off 8 (SOff n 0) (bv_unsigned (getr regs r)));
      [ cbn [sv_denot]; rewrite (EN r n) by reflexivity; rewrite Z.add_0_r; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs r)) as BR; change (bv_modulus 64) with (2 ^ 64) in BR; cbn; lia
      | cbn; lia
      | pose proof (HSV j ltac:(lia)) as V; change (nth j TS_SAVED 0%bv) with r in V;
        replace (sp0 - 8 * (Z.of_nat j + 1)) with (sp0 + off) in V by (cbn; lia); exact V ]
    end.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X64, X26, X65, X2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X64, X26, X65, X2.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
  unfold SHADOW_OFF in *. repeat split; lia.
Qed.

Lemma ts_at_G_A : forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg,
  livea lyc Sc Hpc Wc memc mdc kj pos F b cap f own TSks TSadd ap -> spilla Wc memc F ->
  bregsa rg -> getr rg 26 = w64 (shadow_addr F) ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_G_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg HL [HF16 HF24] HBR R26.
pose proof HL as (HJ & HSD & EF & (HSV & HFL)).
pose proof HBR as (R2 & R3 & R4 & R8 & R9 & R20 & R24).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdwtop & Hdwpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof HSTK_A as HSTK.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLYc. pose proof (ajxR_frs HJ) as HFRc.
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (F32 & _ & Ffr & Fsh).
change (fs_frame_bytes 0) with 64 in Fb2, Fb3, Ffr, Fsh. rewrite <- EF in Fb1, Fb2, Fb3, F32, Ffr, Fsh.
destruct (FFLX lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (Fown & Fapp & Fimg).
pose proof (OWNLOW lyc Sc Hpc Wc memc mdc _ HARc Fown) as Flow.
pose proof (FFLP lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as Fpr.
destruct (ts_sp1_range (regs := regs) Hal16 ltac:(lia)) as (Hsp1a & Hsp1b).
set (fl := flag_addr lyc 0 pos) in *.
assert (Hflf : fl + 1 <= F \/ F + 64 <= fl).
{ destruct (Z_lt_le_dec fl F) as [Hl|Hl]; [left; lia|]. destruct (Z_le_gt_dec (F + 64) fl) as [Hg|Hg]; [right; lia|].
  exfalso. exact (proj2 (Ffr fl ltac:(lia)) Fown). }
assert (Hfls : fl + 1 <= shadow_addr F \/ shadow_addr F + 8 <= fl).
{ destruct (Z_lt_le_dec fl (shadow_addr F)) as [Hl|Hl]; [left; lia|].
  destruct (Z_le_gt_dec (shadow_addr F + 8) fl) as [Hg|Hg]; [right; lia|].
  exfalso. replace fl with (shadow_addr F + (fl - shadow_addr F)) in Fown by lia.
  exact (proj2 (Fsh (fl - shadow_addr F) ltac:(change (64 / 8) with 8; lia)) Fown). }
destruct (ts_G_entry_A Wc memc rg F fl R9 R26 R3 R4 R8 ltac:(lia) ltac:(lia) Hsp1b ltac:(lia) Hal16 Fb1 ltac:(lia) F32 Fb3
  ltac:(lia) ltac:(lia) Hflf Hfls HF16 HF24 (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HFL) HSV
  ltac:(intros a Ha; exact (proj1 (Ffr a ltac:(lia))))
  ltac:(intros a Ha; replace a with (shadow_addr F + (a - shadow_addr F)) by lia;
        exact (proj1 (Fsh (a - shadow_addr F) ltac:(change (64 / 8) with 8; lia)))) Fpr) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TEa regs rg [w64 F; w64 fl])) by apply te_env.
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (U64 : bv_unsigned (ew (TEa regs rg [w64 F; w64 fl]) 64) = F).
{ rewrite (te_more_lt regs rg [w64 F; w64 fl] 0) by lia. cbn [nth]. apply unsigned_lit_small. lia. }
assert (U65 : bv_unsigned (ew (TEa regs rg [w64 F; w64 fl]) 65) = fl).
{ change 65%nat with (64 + 1)%nat. rewrite (te_more_lt regs rg [w64 F; w64 fl] 1) by lia. cbn [nth].
  apply unsigned_lit_small. lia. }
assert (U26 : bv_unsigned (ew (TEa regs rg [w64 F; w64 fl]) (xr 26)) = shadow_addr F).
{ unfold xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
(* G's writes: the frame's first word, its shadow, the flag byte *)
assert (Hwr : forall a, in_wrange (TEa regs rg [w64 F; w64 fl]) (ss_mem ss_Ga) a ->
  (F <= a < F + 8) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = fl).
{ intros a (r & Hr & Ha). cbv [ss_Ga ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
    rewrite ts_bv_some in Ha.
  - lia.
  - left. rewrite U64 in Ha. lia.
  - right; left. rewrite U26 in Ha. lia.
  - right; right. rewrite U65 in Ha. lia.
  - lia. }
(* the run has no inline check: its shadow span is a point far above every region (the flag's lower bound is 0) *)
lazymatch type of HS with st_ok_pi _ _ ?E ?ss _ =>
  let K := eval vm_compute in (run_K A_LIM (SLit 0) [] ss) in
  let r := eval vm_compute in (sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss) in
  lazymatch r with (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss = (st', rs))
    by (vm_compute; reflexivity);
  eapply (ts_flag_store_A Wc FUEL E K (SLit 0) (2 ^ 63, 2 ^ 63) [] ss st' rs _ (STKS + dw) (sp0 + dw) FP0a ly
    (set_depot (st_depot Sc) S) Hp W mem md
    [] lyc Sc Hpc _ _ 0 pos _ ltac:(unfold A_LIM; cbn; lia) HEI ltac:(lia) HS SHOK ltac:(vm_compute; reflexivity) Hrun I
    HJ)
  end end.
- (* no inline check, no obligation *)
  match goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end. apply Forall_nil.
- (* the writes: the own frame's first word and shadow, and the flag *)
  intros a HW. destruct (Hwr a HW) as [H1 | [H1 | H1]].
  + left. right; right; right. exists 0, pos. split; [left; reflexivity|]. left. unfold in_zr, frame_rng.
    cbn [fst snd]. change (fs_frame_bytes 0) with 64. rewrite <- EF. lia.
  + left. right; right; right. exists 0, pos. split; [left; reflexivity|]. right. unfold in_zr.
    cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. rewrite <- EF. lia.
  + right. exact H1.
- (* the flag is 0 after the run *)
  intros ws msr Hlen HSr.
  pose proof (ts_region_nth (L := A_prog_listing) (PA := PA) _ _ _ 3 _ HSr eq_refl) as HR3.
  lazymatch type of HSr with st_ok_pi _ _ (extK ?E0 ?KK ?ws0) _ _ =>
    assert (X65 : bv_unsigned (ew (extK E0 KK ws0) 65) = fl)
      by (rewrite (proj1 (env_agree_extK E0 KK ws0) 65%nat) by (cbv; lia); exact U65) end.
  pose proof (ts_field (L := A_prog_listing) (PA := PA) _ _ 65 fl _ 0 1 0 1 0 1%N (SLit 0) HR3 X65 ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0.
  unfold fl in V0. rewrite V0. f_equal; try (rewrite U_SLit; apply bv_eq; vm_compute; reflexivity).
- (* the epilogue's `ret`: the text's normal arm *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HFr1 HFr2 Hgr.
  cbn [ms_mem mkst] in HFr2.
  (* the flag store's memnorm keep: memnorm_frame_of from the run's start st_ok HS and its full-memory frame HFr1 *)
  assert (KNG : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms'))
    by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HS HFr1); exact Hm).
  assert (K' : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((F <= a < F + 8) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ a = fl) ->
    aview SEGS (w_H Wc) (ms_mem ms') a = aview SEGS (w_H Wc) memc a)
    by (intros a Ha Hn; exact (ts_keep (L := A_prog_listing) (PA := PA) Wc _ (ss_mem ss_Ga) memc (ms_mem ms') _ HFr2 Hwr a Ha Hn)).
  pose proof (ajxR_ar HJ') as HAR'. pose proof (ajxR_pres HJ') as HPR'.
  pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & Eslo & Eshi & _).
  prreg HS' (1%bv : bv 5) Q1.
  assert (X1 : getr (ms_regs ms') 1 = getr regs 1).
  { rewrite Q1. lazymatch goal with |- ew (extK ?E0 ?KK ?ws0) 1 = _ =>
      rewrite (proj1 (env_agree_extK E0 KK ws0) 1%nat) by (cbv; lia) end.
    apply te_entry. reflexivity. }
  (* the `ret` step: a plain SRr step (it frees nothing), lifted by YA0nH.SRr_SRr' *)
  apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (paj_ret_at (PL := PL) (PI := PA) Wc _ _ ms' _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
  intros mat''.
  (* the side facts at the released state *)
  assert (HSIDE' : sidea lyc (stack_free_state 0 pos Sc) Hpc Wc (ms_mem ms') b cap f own TSks TSadd ap).
  { refine (ts_side_move (L := A_prog_listing) (PA := PA) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
      lyc Sc Hpc Wc memc lyc (stack_free_state 0 pos Sc) (ms_mem ms') _ b cap f own TSks TSadd ap HSD HAR' eq_refl
      eq_refl eq_refl _ _ _ _ _ _ _).
    all: lazymatch goal with
    | |- YAkMemnorm.memnorm _ _ -> YAkMemnorm.memnorm _ _ => exact KNG
    | |- _ = _ \/ _ => right; eexists; reflexivity
    | |- _ <= ly_top _ => rewrite Etopc; lia
    | |- forall a, _ -> apresent _ _ _ /\ _ => intros a Ha; rewrite Eslo, Eshi; split; [apply HPR'; lia | lia]
    | |- forall a, _ <= a < ly_top _ -> _ =>
        intros a Ha; apply K'; [lia|]; unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia
    | |- forall p n i, In (p, n) _ -> _ =>
        intros p n i Hpn Hi;
        destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hpn) as (_ & Hb4 & Hbc & Hbapp & Hbown & _);
        pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ 0 pos HARc Hpn Hin) as Hd;
        unfold zdisjoint in Hd; cbn [fst snd] in Hd; change (fs_frame_bytes 0) with 64 in Hd; rewrite <- EF in Hd;
        apply K'; [lia|]; intros [Hw | [Hw | Hw]];
        [ lia
        | unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia
        | exact (proj2 (Hbown (p + i) ltac:(lia)) ltac:(rewrite Hw; exact Fown)) ]
    | |- forall a, in_img _ a -> _ =>
        intros a Ha Hno Her; pose proof (@pa_segs_low _ _ PA a Ha) as Hlow; apply K'; [lia|]; intros [Hw | [Hw | Hw]];
        [ exact (frm_img_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos a HARc Hin ltac:(rewrite <- EF; change (fs_frame_bytes 0) with 64; lia) Ha)
        | unfold SHADOW_OFF in *; lia
        | rewrite Hw in Ha; exact (Fimg Ha) ]
    | _ => idtac
    end. }
  (* the post: the side facts at the released state are the text's body QT (TxStr102Glue.v ts_post), and their
     memnorm keep is fQmn's; ONE fpostWbm (budgeted, no abort arm; fpostW_xbR at WR): the budget and the
     depot's growth are the side facts' at Sc (the release keeps the depot), the journal is the rebased one at WR
     unbased at that budget (YCbqGwild.ajournal_xw_unbase0R) *)
  pose proof HSIDE' as (HWIN' & _ & _ & HMN' & _).
  pose proof HSD as (_ & _ & _ & _ & _ & _ & _ & (WSG & HWIG & HWBG)).
  unfold QF, fpostWbm, fpostWb, YCbqGwild.fpostW_xbR.
  exists lyc, (stack_free_state 0 pos Sc), Hpc, (ms_regs ms'), (ms_mem ms'). eexists. exists kj, WSG.
  split.
  { rewrite X1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [exact HWBG|].
  split.
  { eapply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARx WR _ _ _ _ _ Hp); [|exact HWIG].
    apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) WR). exact HJ'. }
  split; [exact HWIN'|].
  split.
  { eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (map (getr rg) all_regs ++ [w64 F; w64 fl]) HS');
      [| vm_compute; reflexivity].
    split.
    - intros n Hn. lazymatch goal with |- ew (extK ?E0 ?KK ?ws0) n = _ =>
        rewrite (proj1 (env_agree_extK E0 KK ws0) n) by lia end.
      unfold TE. apply Eimg_low. unfold A_TEXT. lia.
    - lazymatch goal with |- ed (extK ?E0 ?KK ?ws0) = _ => rewrite (proj2 (env_agree_extK E0 KK ws0)) end.
      reflexivity. }
  split; [|exact HMN'].
  exact (ts_post lyc (stack_free_state 0 pos Sc) Hpc Wc (ms_mem ms') lyc (stack_free_state 0 pos Sc) (ms_regs ms') _
    b cap f own ap HSIDE' eq_refl eq_refl).
Qed.

(* ---- X: the closing quote's block (A' 0x85580: a0 = t, a1 = .str.25, a2 = 1, `jal tx_put` at 0x85590), every byte
   done; the call through the glue's ts_put_call with the spill carried ---- *)
Definition ss_Xa : sstate := mkSS (TS_PC_A + TS_X_OFF_A) cur_atoms [] None (mkFacts [] [] []).
Lemma ts_at_X_A : forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg,
  livea lyc Sc Hpc Wc memc mdc kj pos F b cap f own (TxModel.plen (ts_pieces bs)) (concat (ts_pieces bs)) ap ->
  spilla Wc memc F ->
  bregsa rg -> getr rg 26 = w64 (shadow_addr F) ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_X_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg HL HSP HBR R26.
pose proof HL as (HJ & _).
pose proof HBR as (R2 & R3 & R4 & R8 & R9 & R20 & R24).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS : st_ok_pi SEGS VAL (TEa regs rg []) ss_Xa
  (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_X_OFF_A))) memc (seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEa regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEa regs rg [])) by apply te_env.
pose (RUN := paj_run_xR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WR WRrefl WRtrans).
pose proof HS as HSk.
paj_run_tok_xR RUN HS HJ SHOK (0, 0).
{ cbv [ss_Xa ss_mem]. apply awr_ok_nil. }
assert (KN : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk HF); exact Hm).
clear HSk.
assert (Hm : forall x, mrestrict (w_H Wc) (ms_mem ms) x = mrestrict (w_H Wc) memc x).
{ intros x. apply HFr. intros (r & Hr & _). cbv [ss_Xa ss_mem In] in Hr. destruct Hr. }
pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
  WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm KN) as HL1.
assert (HSP1 : spilla Wc (ms_mem ms) F).
{ apply (ts_spill_keep (L := A_prog_listing) (PA := PA) (regs := regs) Wc memc); [|exact HSP]. intros a Ha. apply aview_eq_of. apply Hm. }
clear HF HG HFr.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
assert (Z2 : getr (ms_regs ms) 2 = getr rg 2) by tskeep_A HS.
assert (Z3 : getr (ms_regs ms) 3 = getr rg 3) by tskeep_A HS.
assert (Z4 : getr (ms_regs ms) 4 = getr rg 4) by tskeep_A HS.
assert (Z8 : getr (ms_regs ms) 8 = getr rg 8) by tskeep_A HS.
assert (Z9 : getr (ms_regs ms) 9 = getr rg 9) by tskeep_A HS.
assert (Z20 : getr (ms_regs ms) 20 = getr rg 20) by tskeep_A HS.
assert (Z24 : getr (ms_regs ms) 24 = getr rg 24) by tskeep_A HS.
assert (Z26 : getr (ms_regs ms) 26 = getr rg 26) by tskeep_A HS.
assert (HBR' : bregsa (ms_regs ms)).
{ unfold ts_bregs. rewrite Z2, Z3, Z4, Z8, Z9, Z20, Z24. repeat split; assumption. }
assert (X10 : getr (ms_regs ms) 10 = w64 t) by (rewrite Q10; rewrite <- R20; te_close).
assert (X11 : getr (ms_regs ms) 11 = w64 TS_STR25_A).
{ rewrite Q11. rewrite te_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite unsigned_lit_small by (apply pa_val_range). reflexivity. }
pose proof (@pa_B_ok _ _ PA) as HBASE.
assert (HRAOK : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite Q1; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
assert (HRA4 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia).
(* fpre's raZ bound: the return pc is a listing slot (the closed lemma ts_ret_ceil_G_A) *)
assert (HRAC : raZ (ms_regs ms) < YM05.alloc_ceiling) by (unfold raZ; rewrite Q1; exact ts_ret_ceil_G_A).
assert (HE2 : bv_unsigned (ew (TEa regs rg []) 2) = sp0) by (rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
destruct (ts_src_litR (L := A_prog_listing) (PA := PA) (pa_hi_ok := pa_hi_ok_A) (HSTK := HSTK_A) (LAWS := LAWS)
  (zs_aligned := zs_aligned) (img_shadow_vis_x := img_shadow_vis_x) (img_box := img_box_A) (img_cf_box := img_cf_box)
  WR lyc Sc Hpc Wc (ms_mem ms) _ _ pos F b cap f own _ _ ap TS_STR25_A [34] HL1 (proj1 ts_lit_img_A)
  ltac:(cbn; lia) ltac:(intros j Hj; destruct j as [|j]; [vm_compute; reflexivity | cbn in Hj; lia]))
  as (HSRC & HKEPT & HDISJ).
refine (ts_put_call (HSTK := HSTK_A) (LAWS := LAWS) (TXPUT := TXPUT) (HSTKP := HSTKP_A) (pst_ro := pst_ro_A)
  ch Wc (TEa regs rg []) _ ms _ lyc Sc Hpc _ pos F b cap f own _ _ ap 1 TS_STR25_A [34] []
  (conj HPRE (conj HCL (conj HFWIN (conj HPLACE (conj HLEN (conj HLIVE (conj HMAX
    (conj HEVS (conj HROOMW (conj HCONS HFRM))))))))))
  HS eq_refl ltac:(vm_compute; reflexivity) HE2
  HL1 HBR' X10 X11 Q12 HRAOK HRA4 HRAC HSRC eq_refl HKEPT HDISJ ts_ks_fin_A HOS _).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 cap2 f2 own2 prec HL2 HSPk HP2.
rewrite ts_ks_fin_A, ts_add_fin_A in HL2.
rewrite Q1. change (BASE + 16308) with (BASE + (TS_PC_A + TS_G_OFF_A)).
apply (ts_at_G_A ly2 S2 Hp2 W2 mem2 md2 kj2 pos F b2 cap2 f2 own2 (ap ++ prec) regs2 HL2 (HSPk HSP1)
  (ts_bregs_pres _ _ HBR' HP2)).
rewrite (ts_ap _ _ 26%bv HP2) by ts_cs. rewrite Z26. exact R26.
Unshelve. all: ts_ctx_A.
Qed.

(* ---- C at image A' (A' 0x8540c): the loop step at A' is a premise, STEPa (ts_loop's premise with A''s loop head and
   literals). The first run (the check of s, the first byte's load, to `beqz a1`) and the run of either arm write
   nothing: the live state goes across them by the glue's ts_live_sameR, the spill by ts_spill_keep ---- *)
Lemma ts_at_C_A : STEPa -> forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg,
  livea lyc Sc Hpc Wc memc mdc kj pos F b cap f own [1] [34] ap -> spilla Wc memc F ->
  bregsa rg -> getr rg 19 = w64 s -> getr rg 26 = w64 (shadow_addr F) ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_C_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Proof.
intros STEP lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg HL HSP HBR R19 R26.
pose proof HL as (HJ & HSD & EF & (HSV & HFL)). pose proof HSP as (HF16 & HF24).
pose proof HSD as (HWIN & HTX & HPOSs & HMNs & HRO & ((Hl & Hlen & H32 & Hfa & Hga) & HBV) & _).
pose proof HBR as (R2 & R3 & R4 & R8 & R9 & R20 & R24).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdwtop & Hdwpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLYc. pose proof (ajxR_frs HJ) as HFRc.
pose proof (ajxR_pres HJ) as HPRc.
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (F32 & _).
change (fs_frame_bytes 0) with 64 in Fb2, Fb3. rewrite <- EF in Fb1, Fb2, Fb3, F32.
pose proof HBV as (Hs4096 & Hs8 & Hk0 & Hsk & Hamr & Hras & Hhull & Hpres_s).
destruct (ts_sp1_range (regs := regs) Hal16 ltac:(lia)) as (Hsp1a & Hsp1b). pose proof HSTK_A as HSTK.
destruct (Hga 0%nat ltac:(rewrite length_app; cbn; lia)) as (V0 & R0). rewrite Z.add_0_r in V0.
remember (nth 0 (bs ++ [0]) 0) as c0 eqn:Ec0.
destruct (ts_C_entry_A Wc memc rg F c0 R9 R19 R24 ltac:(lia) ltac:(lia) Hsp1b ltac:(lia) ltac:(lia) Hs8 ltac:(lia) F32 R0
  HF24 V0) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TEa regs rg [w64 F; w64 c0])) by apply te_env.
assert (A64 : ew (TEa regs rg [w64 F; w64 c0]) 64 = w64 F)
  by exact (te_more_lt (L := A_prog_listing) (PA := PA) regs rg [w64 F; w64 c0] 0 ltac:(lia)).
assert (A65 : ew (TEa regs rg [w64 F; w64 c0]) 65 = w64 c0)
  by exact (te_more_lt (L := A_prog_listing) (PA := PA) regs rg [w64 F; w64 c0] 1 ltac:(lia)).
pose (RUN := paj_run_xR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WR WRrefl WRtrans).
pose (RUNTO := paj_run_to_xR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WR WRrefl WRtrans).
pose (BR := YSRrG.paj_branchR (PI := PA) WR).
(* the run from C: the check of s, the first byte's load, to `beqz a1` (A' 0x85420) *)
pose proof HS as HSk.
paj_run_tok_xR RUN HS HJ SHOK TS_SPAN_A.
{ (* the inline check of s (A' 0x8540c .. 0x85418, slow block 0x8563c / report site 0x85648): s addressable by
     prhtx_bvis *)
  cbn [ms_mem mkst restrict]. rewrite !ts_U0.
  assert (A56 : ew (TEa regs rg [w64 F; w64 c0]) (xr 24) = getr rg 24)
    by (unfold xr; apply (te_cur regs rg _ 24%bv 24); reflexivity).
  assert (A51 : ew (TEa regs rg [w64 F; w64 c0]) 51 = getr rg 19) by te_close.
  rewrite ?ew_ewset_other by lia.
  rewrite A56, A51, R24, R19. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  apply (range_addressable_sub _ SHADOW_OFF s k s 1 Hras); lia. }
{ cbv [ss_Ca ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KN1 : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk HF); exact Hm).
clear HSk.
(* the run wrote nothing (both regions are read-only) *)
assert (Hm1 : forall x, mrestrict (w_H Wc) (ms_mem ms) x = mrestrict (w_H Wc) memc x).
{ intros x. apply HFr. intros (r & Hr & Ha). cbv [ss_Ca ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia. }
pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
  WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm1 KN1) as HL1.
assert (HSP1 : spilla Wc (ms_mem ms) F).
{ apply (ts_spill_keep (L := A_prog_listing) (PA := PA) (regs := regs) Wc memc); [|exact HSP].
  intros a Ha. apply aview_eq_of. apply Hm1. }
clear HF HG HFr HL HSP.
YSRrG.psrr_branch_tokR RUN BR HS SHOK TS_SPAN_A.
- (* c0 = 0: the empty string, to the closing block X (A' 0x85580, the branch's target) *)
  rewrite branch_eq_U, !ts_U0, U_SLit in Hc. rewrite ?ew_ewset_other in Hc by lia.
  rewrite A65 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  rewrite YP0m.zcanon_small in Hc by lia. apply Z.eqb_eq in Hc.
  destruct (ts_list_cases_A bs) as [Ebs | (cb & post & Ebs)].
  2: { exfalso. rewrite Ebs in Ec0, Hfa. cbn [app nth] in Ec0. inversion Hfa as [|? ? Hcb _]. lia. }
  pose proof HS as HSk2.
  paj_run_to_tok_xR RUNTO HS HJ SHOK TS_SPAN_A (TS_PC_A + TS_X_OFF_A).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (KN2 : YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS (ms_mem ms0))
    by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk2 HF); exact Hm).
  clear HSk2.
  (* the second run wrote nothing either *)
  assert (Hm2 : forall x, mrestrict (w_H Wc) (ms_mem ms0) x = mrestrict (w_H Wc) (ms_mem ms) x).
  { intros x. apply HFr. intros (r & Hri & Hr). vm_compute in Hri.
    repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]); destruct Hri. }
  pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
    WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL1 HJ Hm2 KN2) as HL2.
  assert (HSP2 : spilla Wc (ms_mem ms0) F).
  { apply (ts_spill_keep (L := A_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms)); [|exact HSP1].
    intros a Ha. apply aview_eq_of. apply Hm2. }
  clear HF HG HFr.
  assert (Z2 : getr (ms_regs ms0) 2 = getr rg 2) by tskeep_A HS.
  assert (Z3 : getr (ms_regs ms0) 3 = getr rg 3) by tskeep_A HS.
  assert (Z4 : getr (ms_regs ms0) 4 = getr rg 4) by tskeep_A HS.
  assert (Z8 : getr (ms_regs ms0) 8 = getr rg 8) by tskeep_A HS.
  assert (Z9 : getr (ms_regs ms0) 9 = getr rg 9) by tskeep_A HS.
  assert (Z20 : getr (ms_regs ms0) 20 = getr rg 20) by tskeep_A HS.
  assert (Z24 : getr (ms_regs ms0) 24 = getr rg 24) by tskeep_A HS.
  assert (Z26 : getr (ms_regs ms0) 26 = getr rg 26) by tskeep_A HS.
  pmkst HS. change (BASE + 16288) with (BASE + (TS_PC_A + TS_X_OFF_A)).
  eapply (ts_at_X_A lyc Sc Hpc Wc _ _ _ pos F b cap f own ap).
  + rewrite Ebs. rewrite Ebs in HL2. exact HL2.
  + exact HSP2.
  + unfold ts_bregs. rewrite Z2, Z3, Z4, Z8, Z9, Z20, Z24. repeat split; assumption.
  + rewrite Z26. exact R26.
- (* c0 <> 0: the loop setup (F read back from sp1 + 24), to the loop head (A' 0x85448) *)
  rewrite branch_eq_U, !ts_U0, U_SLit in Hc. rewrite ?ew_ewset_other in Hc by lia.
  rewrite A65 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  rewrite YP0m.zcanon_small in Hc by lia. apply Z.eqb_neq in Hc.
  destruct (ts_list_cases_A bs) as [Ebs | (cb & post & Ebs)].
  1: { exfalso. rewrite Ebs in Ec0. cbn [app nth] in Ec0. lia. }
  assert (Ecb : c0 = cb) by (rewrite Ebs in Ec0; exact Ec0).
  pose proof HS as HSk2.
  paj_run_to_tok_xR RUNTO HS HJ SHOK TS_SPAN_A (TS_PC_A + TS_LH_OFF_A).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (KN2 : YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS (ms_mem ms0))
    by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk2 HF); exact Hm).
  clear HSk2.
  (* the second run wrote nothing either *)
  assert (Hm2 : forall x, mrestrict (w_H Wc) (ms_mem ms0) x = mrestrict (w_H Wc) (ms_mem ms) x).
  { intros x. apply HFr. intros (r & Hri & Hr). vm_compute in Hri.
    repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]); destruct Hri. }
  pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
    WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL1 HJ Hm2 KN2) as HL2.
  assert (HSP2 : spilla Wc (ms_mem ms0) F).
  { apply (ts_spill_keep (L := A_prog_listing) (PA := PA) (regs := regs) Wc (ms_mem ms)); [|exact HSP1].
    intros a Ha. apply aview_eq_of. apply Hm2. }
  clear HF HG HFr.
  assert (Z2 : getr (ms_regs ms0) 2 = getr rg 2) by tskeep_A HS.
  assert (Z3 : getr (ms_regs ms0) 3 = getr rg 3) by tskeep_A HS.
  assert (Z4 : getr (ms_regs ms0) 4 = getr rg 4) by tskeep_A HS.
  assert (Z8 : getr (ms_regs ms0) 8 = getr rg 8) by tskeep_A HS.
  assert (Z9 : getr (ms_regs ms0) 9 = getr rg 9) by tskeep_A HS.
  assert (Z19 : getr (ms_regs ms0) 19 = getr rg 19) by tskeep_A HS.
  assert (Z20 : getr (ms_regs ms0) 20 = getr rg 20) by tskeep_A HS.
  assert (Z24 : getr (ms_regs ms0) 24 = getr rg 24) by tskeep_A HS.
  assert (Z26 : getr (ms_regs ms0) 26 = getr rg 26) by tskeep_A HS.
  prreg HS (11%bv : bv 5) Q11. prreg HS (18%bv : bv 5) Q18. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  rewrite ?ew_ewset_other in Q11, Q18, Q21, Q22, Q23, Q25, Q27 by lia.
  assert (A51 : ew (TEa regs rg [w64 F; w64 c0]) 51 = getr rg 19) by te_close.
  assert (A243 : ew (TEa regs rg [w64 F; w64 c0]) 243 = Z_to_bv 64 (VAL (A_OBJ 2)))
    by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (@pa_val_range _ _ PA (A_OBJ 2)) as RV2.
  pmkst HS. change (BASE + 15976) with (BASE + (TS_PC_A + TS_LH_OFF_A)).
  apply (ts_loop (TS_PC := TS_PC_A) (TS_LH_OFF := TS_LH_OFF_A) (TS_STR26 := TS_STR26_A) (TS_HEX := TS_HEX_A)
    STEP 0 Wc).
  exists lyc, Sc, Hpc, (ms_mem ms0). eexists. eexists.
  exists pos, F, b, cap, f, own, ap, (ms_regs ms0), [], cb, post.
  split; [reflexivity|]. split; [exact Ebs|]. split; [reflexivity|].
  split; [exact HL2|]. split; [exact HSP2|].
  split.
  + unfold ts_lregs. split; [unfold ts_bregs; rewrite Z2, Z3, Z4, Z8, Z9, Z20, Z24; repeat split; assumption|].
    rewrite Q18, Z19, Q21, Q22, Q23, Q25, Z26, Q27, ?A51, ?A64, ?A243, R19.
    unfold w64. rewrite !unsigned_lit_small by lia. cbn [Z.of_nat]. rewrite !Z.add_0_r.
    repeat split; try reflexivity. exact R26.
  + rewrite Q11, A65, Ecb. reflexivity.
Qed.

(* ---- B at image A': segment B's run (ts_B_run_A) to the opening quote's `jal tx_put` (A' 0x85408), the call through
   the glue's ts_put_call (n = 1, .str.25, the quote; it returns on every outcome of tx_put's #102 text), then segment
   C. A' has spilled F before this call, so the call's spill transport (its continuation's second premise) carries
   the spill to C; the continuation also hands C the live state and the kept registers (s3 = s, s10 = F's shadow,
   ts_bregs). THE ONE LIFT: the wle journal ts_A_cps hands over is lifted here, at the cut B, by ajournal_xwR_mono with
   YA0nH.wle_wle'; from here every journal is at WR, every segment SRW, and the first tx_put call is at WR: no lift at
   a call ---- *)
Lemma ts_at_B_A : STEPa -> forall Sc memc mdc kj pos rg,
  AJ (STKS + dw) (sp0 + dw) FP0a ly S Hp W mem md [(0, pos)] ly Sc Hp W memc mdc kj ->
  sidea ly Sc Hp W memc b0 cap0 f0 own0 [] [] [] ->
  ts_saved (L := A_prog_listing) (PA := PA) (regs := regs) W memc ->
  rdword (aview SEGS (w_H W) memc) (frame_addr ly 0 pos + 56) = Some (flag_addr ly 0 pos) ->
  (forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> apresent (w_H W) memc a) ->
  getr rg 2 = w64 sp1 -> getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = getr regs 2 ->
  getr rg 9 = w64 sp1 -> getr rg 10 = w64 (frame_addr ly 0 pos) -> getr rg 19 = w64 s ->
  getr rg 20 = w64 t -> getr rg 24 = w64 SHADOW_OFF ->
  SRW W (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_B_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Proof.
intros STEP Sc memc mdc kj pos rg HJ HSD HSV Hfl Hfp R2 R3 R4 R8 R9 R10 R19 R20 R24.
assert (HJR : AJR (STKS + dw) (sp0 + dw) FP0a ly S Hp W mem md [(0, pos)] ly Sc Hp W memc mdc kj)
  by exact (ajournal_xwR_mono (SK := SK) SEGS B PST ARx (@wle SEGS) WR (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] HJ).
apply (ts_B_run_A Sc memc mdc kj pos rg HJR HSD HSV Hfl Hfp R2 R3 R4 R8 R9 R10 R19 R20 R24).
intros E ss ms mdc' kj' HS Hrv Hpcs HE2 HJ' HSD' HSV' HFL' HBR HSP0 Q19 Q26 X10 X11 X12 Q1.
set (F := frame_addr ly 0 pos) in *.
assert (EKS : TSks = 1 :: ts_rest bs) by (unfold TS_ks, ts_rest; rewrite s10s_ks; reflexivity).
(* B's live state at the opening call: no calls yet (ks = [], add = [], nothing appended); its journal at WR REBASED to
   the current depot (ts_liveR's form; WS = [], the journal from the entry carries no growth yet) *)
pose proof (conj (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx WR _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ [] HJ')
  (conj HSD' (conj (eq_refl F) (conj HSV' HFL')))) as HLIVE0.
pose proof (@pa_B_ok _ _ PA) as HBASE.
assert (EC : TS_PC_A + TS_C_OFF_A = 15916) by (vm_compute; reflexivity).
assert (HRAOK : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite Q1, EC; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
assert (HRA4 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite Q1, EC, unsigned_lit_small by lia; lia).
(* fpre's raZ bound: the return pc is a listing slot (the closed lemma ts_ret_ceil_C_A) *)
assert (HRAC : raZ (ms_regs ms) < YM05.alloc_ceiling) by (unfold raZ; rewrite Q1, EC; exact ts_ret_ceil_C_A).
destruct (ts_src_litR (L := A_prog_listing) (PA := PA) (pa_hi_ok := pa_hi_ok_A) (HSTK := HSTK_A) (LAWS := LAWS)
  (zs_aligned := zs_aligned) (img_shadow_vis_x := img_shadow_vis_x) (img_box := img_box_A) (img_cf_box := img_cf_box)
  WR ly Sc Hp W (ms_mem ms) _ _ pos F b0 cap0 f0 own0 [] [] [] TS_STR25_A [34] HLIVE0 (proj1 ts_lit_img_A)
  ltac:(cbn; lia) ltac:(intros j Hj; destruct j as [|j]; [vm_compute; reflexivity | cbn in Hj; lia]))
  as (HSRC & HKEPT & HDISJ).
refine (ts_put_call (HSTK := HSTK_A) (LAWS := LAWS) (TXPUT := TXPUT) (HSTKP := HSTKP_A) (pst_ro := pst_ro_A)
  ch W E ss ms mdc' ly Sc Hp kj' pos F b0 cap0 f0 own0 [] [] [] 1 TS_STR25_A [34] (ts_rest bs)
  (conj HPRE (conj HCL (conj HFWIN (conj HPLACE (conj HLEN (conj HLIVE (conj HMAX
    (conj HEVS (conj HROOMW (conj HCONS HFRM))))))))))
  HS Hrv Hpcs HE2 HLIVE0 HBR X10 X11 X12 HRAOK HRA4 HRAC HSRC eq_refl HKEPT HDISJ (eq_sym EKS) HOS _).
(* the continuation: segment C, with the spill carried across the call (the call's second premise) *)
intros ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 cap2 f2 own2 prec HL2 HSPk HP2. cbn [app] in HL2.
rewrite Q1.
apply (ts_at_C_A STEP ly2 S2 Hp2 W2 mem2 md2 kj2 pos F b2 cap2 f2 own2 prec regs2 HL2 (HSPk HSP0)
  (ts_bregs_pres _ _ HBR HP2)).
- rewrite (ts_ap _ _ 19%bv HP2) by ts_cs. exact Q19.
- rewrite (ts_ap _ _ 26%bv HP2) by ts_cs. exact Q26.
Unshelve. all: ts_ctx_A.
Qed.

(* ---- the assembly modulo the loop: the entry (ts_A_cps), segment B and the opening quote (ts_at_B_A), segment C to
   the closing block (ts_at_X_A, ts_at_G_A) or the loop head; the loop closes by the glue's ts_loop from STEPa ---- *)
Lemma tx_string_A_of_step : STEPa -> SRW W (cfg_at SEGS (SIGMA AS_tx_string) regs mem md) QFa.
Proof. intros STEP. apply ts_A_cps. exact (ts_at_B_A STEP). Qed.

(* ---- the whole walk: the loop body is ATxStep.ts_step_A (its exit, the closing block, is ts_at_X_A) ---- *)
Lemma tx_string_A_main : SRW W (cfg_at SEGS (SIGMA AS_tx_string) regs mem md) QFa.
Proof.
apply tx_string_A_of_step.
eapply ATxStep.ts_step_A.
all: try eassumption.
all: try exact (proj2 ts_lit_img_A).
unfold ATxStep.ts_HX_A. intros lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg HL HSP HBR R26.
exact (ts_at_X_A lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg HL HSP HBR R26).
Qed.

End g.

(* ---- the Tx part's text ttx_string_specX (lib/A/PRH_FnTx.v) at image A' ---- *)
Theorem tx_string_A_holds : ttx_string_specX (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
Proof.
unfold ttx_string_specX.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s k b0 len0 cap0 f0 own bs txt Lam peak cnt
  fail ran most.
cbv zeta.
intros HPRE0 HCL HROOM HPOS HOS HROOMW HCONS H10 H11 HFWIN HPLACE HTRACE HREC HINV HSTR HBVIS HLEN HLED HEVS HLIVE HMAX
  HCNT.
destruct HPRE0 as (HPRE & HROD & _ & _ & HFRM).
eapply tx_string_A_main; eassumption.
Qed.
End f.
End w.

(* the instance's closed lemmas (Required here, after the walk, so that they do not change the walk's typeclass
   context): the cf laws and frame-class rows at ARcf /\ xs_placed_cf, the A' interface, the static witnesses *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YGcallcf YG0lawscf YGcallScf YG0scf FCifaceCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfImgA AD2l AB1v FCm01xm PresetCfnA AImgShadowVisCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Rtt102CKA ATxStrWitA.
(* ======================================================================================================== *)
(* ---- THE INSTANCE: tx_string_A_holds at the A' interface instance (B := AD2l.TfibB, ARx := PresetCfnA.iface_ARx
   at CfImg_A, RL := prh_room_live_a8, SK := preset_sink_head, CTX0 := iface_ctx0, PI := preset_prh_img). The
   statement of tx_string_A_inst is the body of the interface's tx_string text at that instance. Every Section
   hypothesis but the callee text is DISCHARGED by a cited closed lemma (the discharges of LAWS, OWNLOW, ASFX, FFLX,
   SFX, FFLP and the shadow fact are those of check_round_trip's A' instance, lib/A/Prog/Crt102TopInstA.v):
     the static image facts (PAL, pal_stack_malloc0, pal_uar_img, cf_img_ok, img_cf_box, zs_aligned, pal_pst_static,
     ts_lit_img_A, ts_hex_img_A): ATxStrWitA.v's witnesses; LAWS YGcallcf.AR_laws_x_xs; OWNLOW
     YGcallcf.ARx_owned_low_law_xs; ASM0 FCm01xm.stack_malloc0_contract_xm at ARcf, kept across
     the conjunct xs_placed_cf by YGcallMxmn.astack_malloc_realizes_xm_conj; SMX YGcallScf.stack_malloc_x_any; ASFX
     YGcallScf.astack_free_x_xs; FFLX YGcallScf.frame_flag_x_xs; SFX YGcallScf.stack_free_x_any; FFLP
     YG0scf.AR_flag_law_ok_cf (its first conjunct); FAL64 Rtt102CKA.ck_frame_al64 (the class bound from the laws'
     alx_frames_cid); img_shadow_vis_x AImgShadowVisCf.img_shadow_vis_xs_A.
   CARRIED: TXPUT_I, tx_put's text at the same instance and every float state. ---- *)
Section inst. Context {rc : YM05.RunCeil}.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
#[local] Notation PAI := (@PI_prog_A rc).
#[local] Notation SEGSI := (@pa_segs rc A_prog_listing (@PI_prog_A rc)).
#[local] Notation TA := AD2l.TfibB.
#[local] Notation CP := CfParams_preset.
#[local] Notation RLA := (@PRH_Base.prh_room_live_a8 CfParams_preset).
#[local] Notation ARI := (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB).
#[local] Notation SKA := PresetCfnA.preset_sink_head.
#[local] Notation CTXA := PresetCfnA.iface_ctx0.

Lemma tsi_laws : AR_laws_x SEGSI TA ARI cf_head.
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGSI TA (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGSI TA)). Qed.

Lemma tsi_ownlow : ARx_owned_low_law SEGSI TA ARI.
Proof. exact (YGcallcf.ARx_owned_low_law_xs (cp := CP) SEGSI TA (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGSI TA)). Qed.

Lemma tsi_asm0 : forall fy : YK11.FPState, YGcallMxmn.astack_malloc_realizes_xm (fx := fy) SEGSI TA ARI 0.
Proof.
intros fy. change SEGSI with AB1v.tfibsegs.
exact (YGcallMxmn.astack_malloc_realizes_xm_conj (fx := fy) AB1v.tfibsegs TA
  (YG0ncf.ARcf (rc := rc) (cp := CP) AB1v.tfibsegs TA)
  (fun ly S => YG0ncf.xs_placed_cf (rc := rc) ly S) 0 YGcallScf.xs_placed_cf_set_fs
  (FCm01xm.stack_malloc0_contract_xm (fx := fy) TA (YG0ncf.ARcf (rc := rc) (cp := CP) AB1v.tfibsegs TA)
    (FCifaceCf.fs_iface_ARcf (cp := CP) AB1v.tfibsegs TA (YG0lawscf.AR_laws_ok_cf (cp := CP) AB1v.tfibsegs TA))
    AD2l.TfibB_syms)).
Qed.

Lemma tsi_smx : forall ly S Hp W mem md cid, ARI ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Proof. exact (YGcallScf.stack_malloc_x_any SEGSI ARI). Qed.

Lemma tsi_asfx : forall ly S Hp W mem md mem' md' cid pos,
  ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGSI (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned TA ly S a -> a <> flag_addr ly cid pos ->
     aview SEGSI (w_H W) mem' a = aview SEGSI (w_H W) mem a) ->
  (forall a, aview SEGSI (w_H W) mem a <> None -> aview SEGSI (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARI ly (stack_free_state cid pos S) Hp W mem' md'.
Proof. exact (YGcallScf.astack_free_x_xs (rc := rc) (cp := CP) SEGSI TA). Qed.

Lemma tsi_fflx : forall ly S Hp (W : world SEGSI) mem md cid pos,
  ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned TA ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGSI (flag_addr ly cid pos)).
Proof. exact (YGcallScf.frame_flag_x_xs (rc := rc) (cp := CP) SEGSI TA). Qed.

Lemma tsi_sfx : forall ly S Hp W mem md cid pos, ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Proof. exact (YGcallScf.stack_free_x_any SEGSI ARI). Qed.

Lemma tsi_fflp : forall ly S Hp (W : world SEGSI) mem md cid pos, ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
Proof.
intros ly S Hp W mem md cid pos [HAR _] Hin.
exact (proj1 (YG0scf.AR_flag_law_ok_cf (rc := rc) (cp := CP) SEGSI TA ly S Hp W mem md cid pos HAR Hin)).
Qed.

Lemma tsi_fal64 : forall ly S Hp W mem md cid pos, ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0.
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
exact (Rtt102CKA.ck_frame_al64 TA ARI tsi_laws ly S Hp W mem md cid pos HAR
  (proj1 (alx_frames_cid _ _ _ tsi_laws ly S Hp W mem md cid pos HAR Hin))).
Qed.

Lemma tsi_isv : forall ly S Hp W mem md a, ARI ly S Hp W mem md ->
  @cf_img_lo CfImgA.CfImg_A <= a < @cf_img_top CfImgA.CfImg_A -> aview SEGSI (w_H W) mem (shadow_addr a) <> None.
Proof. exact (AImgShadowVisCf.img_shadow_vis_xs_A (rc := rc) (cp := CP) SEGSI TA AD2l.TfibB_syms). Qed.

(* CARRIED: the callee text, tx_put's, at the same instance and every float state *)
Hypothesis TXPUT_I : forall fy : YK11.FPState,
  @PRH_FnTx.ttx_put_specX fy rc CfImgA.CfImg_A CfParams_preset PresetCfnA.preset_prh_img
    (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PAImg_prog.PI_prog_A rc) AD2l.TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB)
    PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0.

(* THE INSTANCE LEMMA: the body of the interface's tx_string text *)
Theorem tx_string_A_inst : forall fxk : YK11.FPState,
  @PRH_FnTx.ttx_string_specX fxk rc CfImgA.CfImg_A CfParams_preset PresetCfnA.preset_prh_img
    (@PRH_Base.prh_room_live_a8 CfParams_preset) A_prog_listing (@PAImg_prog.PI_prog_A rc) AD2l.TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB)
    PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0.
Proof.
intros fxk.
apply @tx_string_A_holds with (fx := fxk) (rc := rc) (ci := CfImgA.CfImg_A) (SK := SKA) (RL := RLA) (B := TA)
  (ARx := ARI) (CTX0 := CTXA)
  (LAWS := tsi_laws) (PAL := ATxStrWitA.tsw_PAL_TfibA)
  (pal_stack_malloc0 := ATxStrWitA.tsw_pal_stack_malloc0_TfibA)
  (pal_uar_img := ATxStrWitA.tsw_pal_uar_img_cf_TfibA)
  (cf_img_ok := ATxStrWitA.tsw_cf_img_ok_A)
  (img_cf_box := ATxStrWitA.tsw_img_cf_box_A)
  (ASM0 := tsi_asm0 fxk) (OWNLOW := tsi_ownlow) (SMX := tsi_smx)
  (zs_aligned := ATxStrWitA.tsw_zs_aligned_TfibA)
  (img_shadow_vis_x := tsi_isv)
  (TXPUT := TXPUT_I fxk)
  (pal_pst_static := ATxStrWitA.tsw_pal_pst_static_TfibA)
  (ASFX := tsi_asfx) (FFLX := tsi_fflx) (SFX := tsi_sfx) (FFLP := tsi_fflp) (FAL64 := tsi_fal64)
  (ts_lit_img_A := ATxStrWitA.tsw_lit_img_TfibA)
  (ts_hex_img_A := ATxStrWitA.tsw_hex_img_TfibA).
Qed.
End inst.

(* the audit: the axioms of the walk modulo the loop step, of the function theorem (their Section hypotheses are
   their arguments, each MARKED above with its A' witness or its discharge in tx_string_A_inst) and of the instance
   lemma (its one premise, the callee text TXPUT_I, is its argument) *)
Print Assumptions tx_string_A_of_step.
About tx_string_A_of_step.
Print Assumptions tx_string_A_holds.
About tx_string_A_holds.
Print Assumptions tx_string_A_inst.
About tx_string_A_inst.
(* the Print implicit check: the function theorem and the instance lemma, every implicit argument shown (image A'
   names only: PI_prog_A / A_prog_listing / prh_img_A) *)
Set Printing Implicit.
Check tx_string_A_holds.
Check @tx_string_A_inst.
Unset Printing Implicit.
