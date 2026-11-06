(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value: the SHARED CALL KIT of the segment lanes (owner ExvLoop,
   agreed with ExvOpen / ExvDisp 2026-10-29): the two facts every segment with a program call needs, stated over
   ExvB_Stmt.v's EXB (ffa8f3087d2). This file STATES them (as Props); their proofs are lib/B/Prog/ExvB_Loop_kitP.v
   (exv_kit_call, exv_kit_chain), so a lane can code against the statement before the proof lands.
   (a) KIT_EXB_CALL: EXB at the state after a program call made from a cut's state with sp = s1 (the window callee
       form of YCbqGcallW.v aj_call_xW_sp / aj_call_xWF_sp: window e1 = exv_sp E + e_d E - exv_s1 E, so the callee's
       widened journal ends at exv_sp E + e_d E), the callee's footprint inside exv_FP E, the callee's Q giving the
       room (exv_room Sc S2: S2 = Sc for the kit's non-allocating texts, the room / iface implications and the hull
       use of the recursive call's post), the memnorm keep at the post memory (the callee's m-form keep composed with EXB's), Hp
       / ablocks / ledger part (old-pin kit 4f18c75d4900 rebind, ExvLoop 2026-10-29); also the bytes [exv_s1 E, exv_sp E) of ex_value's own frame (the spills, the
       saved registers, 176(s1)) unchanged.
   (b) KIT_CALL_CHAIN: the frame chain a program call made from ex_value takes (aj_call_xW_sp's achain premise), and
       the prhex_ch_apart of it, which tex_value_specX asks of the nested call: ex_value keeps s0 = its entry sp, so
       the chain is ex_value's own record (exv_sp E - 8: the entry ra, exv_sp E - 16: the entry s0) followed by the
       entry chain e_ch E.
   Numerals: 2, 3, 4, 8, 9, 18, 19, 24, 25, 26 (WORD: register numbers of EXB's register facts); 40 (LENGTH: struct
   ex). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* the registers EXB reads (sp, gp, tp, s0, s1, s2, s3, s8, s9, s10) *)
Definition exv_bregs : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* (a) EXB after a program call from sp = s1 in the window form: aj_call_xW_sp / aj_call_xWF_sp's conclusion at
   e1 = exv_sp E + e_d E - exv_s1 E (its callee journal (STK1' + e1) (sp0 + o + e1) is the STK1 / exv_sp E + e_d E
   journal here), with the callee's Q; for a callee that keeps the float state take fx2 := fx. The registers EXB
   reads are the cut's (aregs_preserved of the call gives them for sp, gp, tp, s0-s11). *)
Definition KIT_EXB_CALL : Prop :=
  forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos
    (fx2 : YK11.FPState) (FP1 : list (Z * Z)) (STK1 : Z) ly2 S2 Hp2 (W2 : world rsegs) (regs2 : bvmap 5 word) mem2 md2 k1,
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  (forall a, inFP FP1 a -> inFP (exv_FP E) a) ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx STK1 (exv_sp E + e_d E) FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, exv_s1 E <= a < exv_sp E + e_d E -> ~ inFP FP1 a ->
     aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
  (forall r, In r exv_bregs -> getr regs2 r = getr regs r) ->
  fregs_kept_x fx fx2 -> frm_zero (@YK11.fp_csr fx2) ->
  exv_room Sc S2 -> (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs mem2) ->
  Hp2 = Hpc -> ablocks B ly2 S2 = ablocks B lyc Sc ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) ->
  EXB (fx := fx2) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos /\
  (forall a, exv_s1 E <= a < exv_sp E -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).

(* (b) the call's frame chain (aj_call_xW_sp's achain premise at sp0 + o = exv_s1 E, s0 = exv_sp E) and its
   prhex_ch_apart (tex_value_specX's premise at the nested call), at the call's registers regsc *)
Definition KIT_CALL_CHAIN : Prop :=
  forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos (regsc : bvmap 5 word),
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  getr regsc 2 = w64 (exv_s1 E) -> getr regsc 8 = w64 (exv_sp E) ->
  exists ch1, achain lyc (aview rsegs (w_H Wc) memc) (exv_s1 E) (exv_sp E) ch1 /\
    prhex_ch_apart lyc Wc memc regsc ch1 (e_q E) 40.

(* (c) the read-only view at a cut (fpre's arodata_okP for a callee's text; rom_view for the string runtime texts):
   the entry's, kept by the journal's image clause *)
Definition KIT_RODATA : Prop :=
  forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos,
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  arodata_okP rsegs pa_relro_lo pa_relro_hi B (aview rsegs (w_H Wc) memc) /\
  (* the image view at the NON-owned read-only bytes (B's read-only PT_LOAD holds 63 runtime-owned statics, so the
     whole rom_view is not a cut fact; strcmp takes arodata_okP, ExvB_StrcmpRo.v) *)
  (forall a, in_rom rsegs a -> ~ Exists (in_zr a) (as_owned_static B) ->
     aview rsegs (w_H Wc) memc a = option_map (fun b : byte => bv_unsigned b) (seg_rom rsegs (Z_to_bv 64 a))).

(* (d) the scratch as a callee's destination (wdest_ok at the callee's stack need STK1 from sp = s1) *)
Definition KIT_WDEST : Prop :=
  forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos (regsc : bvmap 5 word) (STK1 : Z),
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  getr regsc 2 = w64 (exv_s1 E) -> 0 <= STK1 -> STK1 + (exv_sp E - exv_s1 E) <= exv_STK E ->
  wdest_ok B STK1 lyc Sc Wc regsc memc (e_scr E) (exv_len E + 1).
End k.
