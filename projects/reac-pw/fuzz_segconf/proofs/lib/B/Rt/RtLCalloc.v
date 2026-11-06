(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the composition technique (an SRr prefix joined to an amreal run with
   YG0d.v:101 amreal_SRr_pre, and the amreal's leaves continued by a second SRr run) is ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/AF0w.v and A/AFij.v, where cgif composes its malloc wrapper's walk the same
   way; the walk of lib/A/DecodeCallocWrap.v is re-run here with a stronger post (see WHY walk_C2X below). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/DecodeCallocTop.v, with its module paths and module names changed; 108 of its 138 lines of code are new or changed and 928 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtLCalloc.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B; lib/Lib/DecodeCallocKit.v to its image-B copy lib/B/DecodeCallocKit.v) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* reac-pw/fuzz_segconf image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...): the closing of interface row 13, the
   calloc wrapper's call rule lib/A/Rt/RtSegCalloc.v aseg_calloc04_rule at the calloc trampoline PC_calloc = 0x56cc4
   (lib/A/Rt/SegRtPC.v) and cstk = ASTACK + 2192 = 18576, at this frame's journal (sink head lib/A/AE2k.v
   tfib_sink_head) and the trivial meter lib/Reusable/YCbp.v ameter_triv (the meter fuzz_command's program closing
   instantiates, CmdProgClosed.v:81; a general meter cannot give the rule's post `mo_le MT Sc S2 (mo_malloc MT (m * n))`).

   [seg_acalloc_of_realizes]: the rule from the calloc realizes form lib/A/Rt/RtLCallocR.v aseg_acalloc_realizes at
   PC_calloc, a trace pc pc0, the cap DEC_CALLOC_MAX = PRIM_MAX and the call depth DEC_CALLOC_DEPTH = 2192 (the
   wrapper's frame 2144 at 0x570c0 / 0x570e8 plus asan_calloc's 48 at 0x33b2c; lib/Lib/DecodeCallocKit.v), by
   lib/A/Rt/YCbpCalloc.v aseg_calloc04_rule_triv.

   [seg_acalloc_of_allocate]: the same rule from the Allocate contract at calloc's call site (lib/A/DecodeCalloc.v
   decode_aalloc_A: Allocate 0x331a4, __asan::instance, the out-of-memory byte, can_fill 0) through the thin walk
   lib/A/DecodeCallocTop.v decode_acalloc_of_allocate_A_holds, under that walk's Section hypotheses.

   [seg_acalloc_closed]: the rule for every symbol record B of the image (SegBSyms B, lib/A/AF0m.v) whose depot hash is
   the image's (the premise lib/A/AFem.v tfib_depot_ok takes), every hypothesis discharged: the walk's rows by
   lib/A/DecodeARows.v, DecodeARowsRt.v, DecodeARowsFill.v, DecodeACallocTp.v, the Allocate contract by
   lib/A/Rt/RtLCallocA.v seg_aalloc_calloc_closed (omx-clap-core/fuzz_state's closed Allocate, relocated).
   [seg_acalloc_closed_segB]: the same at the image's own record lib/A/AD2l.v SegB, with no premise. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YM05 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YGCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YE2k YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import DecodeCallocKit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import DecodeCalloc DecodeCallocRt DecodeCallocWrap.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require DecodeCallocTop DecodeACallocTp DecodeARowsRt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require DecodeARows DecodeARowsFill YD2l.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import SegRtPC RtSegCalloc RtLCallocR YCbpCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtLCallocA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YF0p.
Import ListNotations.
Local Open Scope Z_scope.

Definition SEG_CALLOC_CSTK : Z := 18576.
Lemma seg_calloc_cstk_ok : ASTACK + DEC_CALLOC_DEPTH <= SEG_CALLOC_CSTK.
Proof. vm_compute. discriminate. Qed.
Lemma seg_calloc_max_ok : YGCalloc.PRIM_MAX <= DEC_CALLOC_MAX.
Proof. vm_compute. discriminate. Qed.
Lemma seg_calloc_depth_ok : 0 <= DEC_CALLOC_DEPTH.
Proof. vm_compute. discriminate. Qed.

(* The rule's image premises at segconf A: every loaded byte lies below kLowMemEnd, and the errno word (the record's
   ts_errno, AF0m.v TFIB_ERRNO) lies in a loaded segment; both decided against the image module's segment list. *)
Lemma seg_calloc_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (E : forallb (fun s : Segment => (0 <=? Z.of_N (seg_base s)) &&
  (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd))%bool tfibsegs = true) by (vm_compute; reflexivity).
rewrite forallb_forall in E. specialize (E sg Hin). apply andb_prop in E as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma seg_calloc_errno_img : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (E : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? TFIB_ERRNO) &&
  (TFIB_ERRNO + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in E as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.
(* The record's facts the rule takes: errno (ts_errno), the two one-element traces of malloc's and free's return pc
   (ts_code, in AF0m.v DRV_TRACES by ts_universe_drv), and the model laws (ts_universe, YG05.v model_laws_ok). *)
Lemma seg_calloc_env : forall B, SegBSyms B -> api_env tfibsegs B.
Proof.
intros B HB. unfold api_env. rewrite (ts_errno B HB), (ts_code B HB).
split; [cbv [TFIB_ERRNO kLowMemEnd]; lia|]. split; [exact seg_calloc_errno_img|].
split; apply (ts_universe_drv B HB); vm_compute; repeat (first [left; reflexivity | right]).
Qed.
Lemma seg_calloc_model_laws : forall B, SegBSyms B -> model_laws (as_universe B).
Proof. intros B HB. exact (model_laws_ok _ (ts_universe B HB)). Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Hypothesis ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

Theorem seg_acalloc_of_realizes : forall pc0,
  aseg_acalloc_realizes tfibsegs B PC_calloc pc0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH ->
  @aseg_calloc04_rule fx rc tfib_sink_head tfibsegs B ameter_triv PC_calloc SEG_CALLOC_CSTK.
Proof.
intros pc0 REAL.
exact (@aseg_calloc04_rule_triv fx rc tfib_sink_head tfibsegs B segs_low ENV (AR_laws_ok tfibsegs B) ML
  PC_calloc pc0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH SEG_CALLOC_CSTK seg_calloc_max_ok seg_calloc_depth_ok
  seg_calloc_cstk_ok REAL).
Qed.

(* The thin walk's Section hypotheses (lib/A/DecodeCallocTop.v Section t), its LAWS discharged by YG0q.AR_laws_ok. *)
Hypothesis IMG : forall ly S W regs mem md ch,
acall_pre tfibsegs B ly S W regs mem md ch -> dec_img_cover ly.
Hypothesis HTP : as_tp B = DEC_A_TP.
Hypothesis HINST : as_inst B = DEC_A_instance.
Hypothesis RT_TRY : decode_try_init_spec_A.
Hypothesis RT_MCS : decode_mcs_spec_A.
Hypothesis RT_GETPC : decode_getpc_spec_A.
Hypothesis RT_UNW : decode_unwind_spec_A.
Hypothesis FILL : decode_zero_fill_spec_A B.
Hypothesis CELLS : forall ly S W regs mem md ch,
acall_pre tfibsegs B ly S W regs mem md ch -> dec_cells_A ly W mem.
Hypothesis IMG_CONST : forall ly,
In (z8 (ANum DEC_A_got_real_memset) DEC_A_real_memset) (as_const B ly) /\
In (z8 (ANum DEC_A_real_memset) DEC_A_memset) (as_const B ly) /\
In (c8 (AInst o_space) (ASp 0)) (as_const B ly).
Hypothesis ERRNO_LOW : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd.

Theorem seg_acalloc_of_allocate :
  decode_aalloc_A B ->
  @aseg_calloc04_rule fx rc tfib_sink_head tfibsegs B ameter_triv PC_calloc SEG_CALLOC_CSTK.
Proof.
intros ALLOC.
apply (seg_acalloc_of_realizes DEC_A_calloc_ra0).
exact (@DecodeCallocTop.decode_acalloc_of_allocate_A_holds fx rc B IMG HTP HINST RT_TRY RT_MCS RT_GETPC RT_UNW
  FILL CELLS (AR_laws_ok tfibsegs B) IMG_CONST ERRNO_LOW DEC_CALLOC_MAX_prim ALLOC).
Qed.
End c.

(* The same rule over this image's symbol record: the thin walk's HTP (DecodeACallocTp.v), HINST and ERRNO_LOW (the
   record's ts_inst / ts_errno), the three runtime entries (DecodeARowsRt.v), segs_low, api_env and the model laws
   (above) discharged; the image-cover, unwind, fill, start-up-cell and constant-cell rows stay hypotheses here. *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.
Hypothesis IMG : forall ly S W regs mem md ch,
acall_pre tfibsegs B ly S W regs mem md ch -> dec_img_cover ly.
Hypothesis RT_UNW : decode_unwind_spec_A.
Hypothesis FILL : decode_zero_fill_spec_A B.
Hypothesis CELLS : forall ly S W regs mem md ch,
acall_pre tfibsegs B ly S W regs mem md ch -> dec_cells_A ly W mem.
Hypothesis IMG_CONST : forall ly,
In (z8 (ANum DEC_A_got_real_memset) DEC_A_real_memset) (as_const B ly) /\
In (z8 (ANum DEC_A_real_memset) DEC_A_memset) (as_const B ly) /\
In (c8 (AInst o_space) (ASp 0)) (as_const B ly).

Lemma seg_calloc_inst : as_inst B = DEC_A_instance.
Proof. rewrite (ts_inst B HB). reflexivity. Qed.

Theorem seg_acalloc_of_allocate_rec :
  decode_aalloc_A B ->
  @aseg_calloc04_rule fx rc tfib_sink_head tfibsegs B ameter_triv PC_calloc SEG_CALLOC_CSTK.
Proof.
intros ALLOC.
exact (@seg_acalloc_of_allocate fx rc B seg_calloc_segs_low (seg_calloc_env B HB) (seg_calloc_model_laws B HB)
  IMG (DecodeACallocTp.H_CALLOC_TP_holds B HB) seg_calloc_inst (DecodeARowsRt.dec_a_rt_try fx rc)
  (DecodeARowsRt.dec_a_rt_mcs fx rc) (DecodeARowsRt.dec_a_rt_getpc fx rc) RT_UNW FILL CELLS IMG_CONST
  (proj1 (seg_calloc_env B HB)) ALLOC).
Qed.
End r.

Section f. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.
Hypothesis HDH : forall t, as_dhash B t = tfib_dhash t.

Theorem seg_acalloc_closed : forall fx0 : YK11.FPState,
  @aseg_calloc04_rule fx0 rc tfib_sink_head tfibsegs B ameter_triv PC_calloc SEG_CALLOC_CSTK.
Proof.
intros fx0.
apply (@seg_acalloc_of_allocate_rec fx0 rc B HB (DecodeARows.dec_a_img_cover B fx0 rc)
  (DecodeARows.dec_a_rt_unw fx0 rc) (DecodeARowsFill.dec_a_fill fx0 rc B) (DecodeARows.dec_a_cells B HB fx0 rc)
  (DecodeARows.dec_a_img_const B HB)).
exact (RtLCallocA.seg_aalloc_calloc_closed B HB HDH).
Qed.
End f.

Theorem seg_acalloc_closed_segB : forall (rc : YM05.RunCeil) (fx0 : YK11.FPState),
  @aseg_calloc04_rule fx0 rc tfib_sink_head tfibsegs YD2l.SegB ameter_triv PC_calloc SEG_CALLOC_CSTK.
Proof. intros rc fx0. exact (@seg_acalloc_closed rc YD2l.SegB YD2l.SegB_syms (fun t => eq_refl) fx0). Qed.
