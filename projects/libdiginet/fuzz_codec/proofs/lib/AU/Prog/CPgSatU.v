(* Satisfiability of the image-B contracts at the call sites of image B (stream rule 1j-bis).

   The generic witnesses come from lib/A/Prog/CPgSat.v unchanged: sat_window_aligned /
   sat_window_plain for the stack window at the sp a call is made with, sat_frame_dst(_in) /
   sat_frame_rd(_in) / sat_frame_hull for an object of a side-stack frame, sat_stack_dst for an object on
   the caller's machine stack, sat_block_rd for the input bytes, sat_cobj_frame / sat_cobj_block and the
   frame-size instances sat_main_cobj (class 3) / sat_c0_cobj (class 0) for the one-object premise, and
   sat_frame_not_owned / sat_img_not_owned, and sat_img_bytes_ok, which builds cimg_range's per-byte
   clause from the range's two list facts and its disjointness from the errno word (image B's errno is
   0x5d9cac, TFIB_ERRNO of lib/AU/YF0m.v; every range an image-B contract names ends at or below
   0x9e270). All of these are stated over abstract segments, symbols and
   offsets. sat_img_usable / sat_img_rd / sat_img_rd_in are the exception: they are stated with image A's
   read range (lib/A/Prog/CodecRo.v, IMG_HI = 0x5fb000). They apply at image B all the same, because
   image B's read range (IMG_HI = 0x5fc000) contains image A's, so image B's start-up fact
   img_shadow_vis gives the form they ask for.

   This file holds what is image B's own: the stack window of every call of every caller, and the
   objects of image B's frames at their offsets. The entry function's frame is of class 3 again (480 of
   the 512 bytes it holds, requested at 0x80a0c), but its objects moved: a 3-byte payload object at
   F + 32, the scribble payload at F + 48 (10 bytes; owe_sysex reads its first 2 + chars bytes at
   0x82f70), text[65] at F + 80, the 184-byte call record k at F + 192 (so k.bytes at F + 232, k.out at
   F + 300 and k.want at F + 336), and the dots byte at F + 448. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ===================== the stack windows of every call site of image B =====================
   The entry function's own window is 352 (real frame 320, 32 for the realignment at image B 0x809dc)
   and the deepest below it is check_text_counter's. The core fixes LLVMF_STK at 32768. *)
Lemma satU_T_main_fits : TB_main_need <= 32768.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_rt : 352 + ESTACK <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_check_pers : 352 + TB_check_pers <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_pers_of : 352 + TB_pers_of <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_text_arg : 352 + TB_text_arg <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_check_seg7 : 352 + TB_check_seg7 <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_check_text_counter : 352 + TB_check_text_counter <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_owed_counter_text : 352 + TB_owed_counter_text <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_check_text_scribble : 352 + TB_check_text_scribble <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_owe_sysex : 352 + TB_owe_sysex <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_fader : 352 + TB_fader <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_button : 352 + TB_button <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_touch : 352 + TB_touch <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_vpot : 352 + TB_vpot <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_jog : 352 + TB_jog <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_sysex : 352 + TB_sysex <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_ring : 352 + TB_ring <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_meter : 352 + TB_meter <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_sleds : 352 + TB_sleds <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_cleds : 352 + TB_cleds <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_scribble : 352 + TB_scribble <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_counter : 352 + TB_counter <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_check_refusal : 352 + TB_check_refusal <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_check_range : 352 + TB_check_range <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_check_bytes : 352 + TB_check_bytes <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_main_check_masks : 352 + TB_check_masks <= TB_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* check_personality's three calls *)
Lemma satU_T_cp_pers_of : 32 + TB_pers_of <= TB_check_pers.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_cp_strcmp : 32 + 2 * ESTACK <= TB_check_pers.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_cp_from_name : 32 + TB_from_name <= TB_check_pers.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* check_text_seg7 and check_text_masks *)
Lemma satU_T_cs_seg7 : 48 + TB_seg7 <= TB_check_seg7.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_cs_owed_seg7 : 48 + TB_owed_seg7 <= TB_check_seg7.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_cm_leaves : 48 + TB_meter_mask <= TB_check_masks /\ 48 + TB_meter_segs <= TB_check_masks /\
  48 + TB_ring_dot <= TB_check_masks /\ 48 + TB_ring_fill <= TB_check_masks.
Proof. unfold TB_check_masks, TB_meter_mask, TB_meter_segs, TB_ring_dot, TB_ring_fill.
repeat split; apply Z.leb_le; vm_compute; reflexivity. Qed.
(* the two text checks *)
Lemma satU_T_cts_rt : 160 + ESTACK <= TB_check_text_scribble.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_cts_scribble_text : 160 + TB_scribble_text <= TB_check_text_scribble.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_cts_bcmp : 160 + 2 * ESTACK <= TB_check_text_scribble.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_ctc_rt : 192 + ESTACK <= TB_check_text_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_ctc_owed : 192 + TB_owed_counter_text <= TB_check_text_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_ctc_lib : 192 + TB_counter_text <= TB_check_text_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_ctc_bcmp : 192 + 2 * ESTACK <= TB_check_text_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* the two counter-text functions *)
Lemma satU_T_ct_rt : 224 + ESTACK <= TB_counter_text.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_ct_seg7 : 224 + TB_seg7 <= TB_counter_text.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_oct_rt : 224 + ESTACK <= TB_owed_counter_text.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_oct_owed_seg7 : 224 + TB_owed_seg7 <= TB_owed_counter_text.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* the four encoders that request a frame and call diginet_sysex_encode, and the two that tail-call
   leds_encode (they pop their own 16 bytes first, so the window they need is leds_encode's) *)
Lemma satU_T_ring_rt : 128 + ESTACK <= TB_ring.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_ring_sysex : 128 + TB_sysex <= TB_ring.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_meter_rt : 160 + ESTACK <= TB_meter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_meter_sysex : 160 + TB_sysex <= TB_meter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_leds_rt : 128 + ESTACK <= TB_leds.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_leds_sysex : 128 + TB_sysex <= TB_leds.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_sleds_leds : TB_leds <= TB_sleds.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_cleds_leds : TB_leds <= TB_cleds.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_sc_rt : 160 + ESTACK <= TB_scribble.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_sc_sysex : 160 + TB_sysex <= TB_scribble.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_cnt_rt : 160 + ESTACK <= TB_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_cnt_sysex : 160 + TB_sysex <= TB_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* the leaves that call one helper or wrapper *)
Lemma satU_T_sysex_rt : 48 + ESTACK <= TB_sysex.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_owe_sysex_rt : 48 + ESTACK <= TB_owe_sysex.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_text_arg_rt : 32 + ESTACK <= TB_text_arg.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_check_range_bcmp : 32 + 2 * ESTACK <= TB_check_range.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_check_bytes_bcmp : 32 + 2 * ESTACK <= TB_check_bytes.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma satU_T_from_name_strcmp : 48 + 2 * ESTACK <= TB_from_name.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* ===================== the objects of image B's frames at their offsets ===================== *)

(* The entry function's class-3 frame. The ranges inside the call record take the record's own shadow
   map (23 zero bytes), since k.out at F + 300 is 4-aligned, not 8-aligned. *)
Lemma satU_main_out_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (3, pos) own -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 192) 184 ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + 300) 32.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F HJ H1 H2 HF H64 HBS HT Hw He.
exact (sat_frame_dst_in segs B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T 3 pos F
  192 184 300 32 HJ H1 H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS HT Hw He).
Qed.
Lemma satU_main_k_rd : forall lyc Sc W memc mdc sp T pos F STK sp0,
  AR segs B lyc Sc W memc mdc -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 192) 184 ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + 192) 184.
Proof.
intros lyc Sc W memc mdc sp T pos F STK sp0 HAR H2 HF H64 HBS Hc Hw.
exact (sat_frame_rd segs B LAWS lyc Sc W memc mdc sp T 3 pos F 192 184 STK sp0
  HAR H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS Hc Hw).
Qed.
(* An empty range at a fixed offset of a side-stack frame: the copy helper is called with length 0 too,
   and its law still asks for the bounds and amem_range of the source. *)
Lemma satU_frame_rd_empty : forall lyc Sc W memc mdc sp T cid pos F off STK sp0,
  AR segs B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) -> frame_addr lyc cid pos = F ->
  0 <= off -> off <= fs_frame_bytes cid ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + off) 0.
Proof.
intros lyc Sc W memc mdc sp T cid pos F off STK sp0 HAR Hin HF Ho Hon Hc Hw.
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
rewrite HF in Hf4096, Hfceil, Hfapp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [unfold kLowShadowBeg, kHighMemBeg, in_app in *; lia|].
split; [intros a Ha; lia|].
split; [apply range_addressable_nil; lia|].
split; [intros Hn; lia|].
split.
{ unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
left. lia.
Qed.
(* the payload of a sysex call or of owe_sysex's SYSEX call: the first n bytes of k.bytes, n in 0 .. 24 *)
Lemma satU_main_bytes_rd_n : forall lyc Sc W memc mdc sp T pos F STK sp0 n,
  AR segs B lyc Sc W memc mdc -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  0 <= n -> n <= 24 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 192) 184 ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + 232) n.
Proof.
intros lyc Sc W memc mdc sp T pos F STK sp0 n HAR H2 HF H64 Hn Hn24 HBS Hc Hw.
assert (Hfs : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
destruct (Z.eq_dec n 0) as [->|Hn0].
- exact (satU_frame_rd_empty lyc Sc W memc mdc sp T 3 pos F 232 STK sp0 HAR H2 HF ltac:(lia)
    ltac:(rewrite Hfs; lia) Hc Hw).
- exact (sat_frame_rd_in segs B LAWS lyc Sc W memc mdc sp T 3 pos F 192 184 232 n STK sp0
    HAR H2 HF H64 ltac:(rewrite Hfs; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite Hfs; lia) HBS Hc Hw).
Qed.
(* what owe_sysex may write: the 40 bytes from the record's want to its end, F + 336 .. F + 376 (it
   writes want, want_len and want_display and leaves want_key as it was) *)
Lemma satU_main_want_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (3, pos) own -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 192) 184 ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + 336) 40.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F HJ H1 H2 HF H64 HBS HT Hw He.
exact (sat_frame_dst_in segs B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T 3 pos F
  192 184 336 40 HJ H1 H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS HT Hw He).
Qed.
(* text[65] at F + 80 and the dots byte at F + 448, each with its own shadow map *)
Lemma satU_main_text_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (3, pos) own -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 80) 65 ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + 80) 65.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F HJ H1 H2 HF H64 HBS HT Hw He.
exact (sat_frame_dst segs B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T 3 pos F 80 65
  HJ H1 H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS HT Hw He).
Qed.
Lemma satU_main_text_rd : forall lyc Sc W memc mdc sp T pos F STK sp0,
  AR segs B lyc Sc W memc mdc -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 80) 65 ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + 80) 65.
Proof.
intros lyc Sc W memc mdc sp T pos F STK sp0 HAR H2 HF H64 HBS Hc Hw.
exact (sat_frame_rd segs B LAWS lyc Sc W memc mdc sp T 3 pos F 80 65 STK sp0
  HAR H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS Hc Hw).
Qed.
Lemma satU_main_dots_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (3, pos) own -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 448) 1 ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + 448) 1.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F HJ H1 H2 HF H64 HBS HT Hw He.
exact (sat_frame_dst segs B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T 3 pos F 448 1
  HJ H1 H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS HT Hw He).
Qed.
(* the payload objects at F + 32 (3 bytes; only the entry function's own copy at 0x82fec reads it, the
   case's owe_sysex being inlined) and F + 48 (the 10-byte scribble payload), each with its own shadow
   map, the read range inside it: owe_sysex reads 2 + chars bytes of the scribble payload at 0x82f70,
   which is not a whole object for the Control|24 desk *)
Lemma satU_main_pl_rd : forall lyc Sc W memc mdc sp T pos F STK sp0 boff bn off n,
  AR segs B lyc Sc W memc mdc -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  32 <= boff -> boff <= off -> 0 < n -> off + n <= boff + bn -> boff + bn <= 64 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + boff) bn ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + off) n.
Proof.
intros lyc Sc W memc mdc sp T pos F STK sp0 boff bn off n HAR H2 HF H64 Hb Hbo Hn Hon Hbn HBS Hc Hw.
assert (Hfs : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
exact (sat_frame_rd_in segs B LAWS lyc Sc W memc mdc sp T 3 pos F boff bn off n STK sp0
  HAR H2 HF H64 ltac:(rewrite Hfs; reflexivity) ltac:(lia) Hbo Hn Hon ltac:(rewrite Hfs; lia) HBS Hc Hw).
Qed.
(* The one-object premise at image B's frames is CPgSat's sat_main_cobj (class 3) and sat_c0_cobj
   (class 0): the frame sizes are the same at both images. *)
End c.
End b.
