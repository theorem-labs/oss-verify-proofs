(* Satisfiability of the A-level contracts of lib/A/Prog/CPgEncC.v and CPgChkC.v at the call sites of
   image A (stream rule 1j-bis: one closed lemma at each consumer's call site, showing that the call site
   supplies the premise).

   A call site of codec's own code supplies three kinds of premise, and this file closes each kind at the
   concrete numbers of image A:
   - the stack window: the caller's own T must leave the callee's T below the caller's real frame and its
     realignment. sat_T_* checks that for every call site of every caller, and sat_window_aligned /
     sat_window_plain carry the caller's window premise to the callee's at the sp the call is made with;
   - the objects the call reads and writes. Four kinds lie at the call sites of image A:
     . objects of a side-stack frame the caller owns, at fixed offsets: the entry function's class-3 frame
       (payload F + 32, text F + 64, the call record F + 176 with its bytes F + 216, out F + 284 and want
       F + 320, the dots byte F + 432), the class-0 frames of check_text_scribble, check_text_counter and
       diginet_scribble_encode (8 or 10 bytes at F + 32), the class-1 frames of the two counter-text
       functions (the digits at F + 32, the dot flags at F + 64). sat_frame_dst(_in) / sat_frame_rd(_in)
       build cdst_ok / crd_ok from the caller's journal, the shadow map of an 8-aligned object that covers
       the range, and the offsets; sat_frame_hull shows the 8-byte shadow window the wrappers ask for stays
       inside the frame's own shadow; sat_main_* / sat_c0_* / sat_c1_* instantiate them;
     . objects on the caller's machine stack: text_arg's cursor (the entry function's realigned sp + 152)
       and check_text_counter's own dots byte (its realigned sp + 55). sat_stack_dst builds cdstk_ok;
     . the input bytes, in the input heap block: sat_block_rd builds crd_ok;
     . rows of the registered globals: sat_img_usable / sat_img_rd / sat_img_rd_in build the all-states
       cimg_usable / cimg_range for a whole row or a range inside one (the personality bytes
       PERS + 16 .. PERS + 20) from the start-up facts (lib/A/Prog/CodecRo.v) and the read-only data;
     . a caller object that one of the five frame-requesting functions reads or writes: sat_cobj_frame /
       sat_cobj_block, and their instances sat_main_cobj / sat_c0_cobj, build cobj_ok.
   The remaining premises of a contract are the caller's own invariant and image facts no lemma here
   states: the plain agreement equations, the record's field ranges and the argument values, the
   personality bytes at p + 16 (c24 / pc of lib/Spec/DgnSpec.v), touch's d_strips <= 64, scribble's
   d_chars <= 8, check_text_scribble's n = the desk's chars <= 8, cpers_disj (an image byte against a
   frame byte), and that each image range a contract names lies in the image, in no owned static of
   the runtime (image A: lib/A/AD1k.v tfib_not_owned_static; for the personality bytes over
   [0x9d920, 0x9d950)) and off the errno word (image A: lib/A/AF0m.v ts_errno, TFIB_ERRNO = 0x5d936c;
   every range a contract names ends at or below 0x9d950) -- which is what cimg_range asks for.
   sat_img_bytes_ok builds cimg_range's per-byte clause from those three facts, and sat_img_not_owned
   turns the first two into `~ aowned`. Each lemma below leaves exactly those to the caller.

   The frame's address is 64-aligned (F mod 64 = 0) in the frame lemmas. The side stack's own map makes it
   so -- fs_frame_off is a multiple of 64 for every class (lib/Reusable/YG0f.v) -- but the kit states only
   frame_addr mod 32 = 0 (AR_frames_law), so the walks take it as a named fact. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CodecRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================ the stack windows of every call site ============================
   T_f of lib/A/Prog/CPgBase.v is the stack the call of f uses below its caller's sp. A caller's own T
   must cover its real frame, the 32 bytes its realignment may take, and the deepest T among the calls it
   makes. Each lemma below is that check for one caller, over every call it makes at image A. *)
(* The stack the entry function needs below its caller's sp: its own 320 (real frame 288, 32 for the
   realignment at image A 0x8088c) and the deepest window below it, check_text_counter's. A walk gets
   the premise of each call from LLVMF_STK, which the core fixes at 32768. *)
Definition T_main_need : Z := 8704.
Lemma sat_T_main_fits : T_main_need <= 32768.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* Every call the entry function makes, against its own window. *)
Lemma sat_T_main_rt : 320 + ESTACK <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_check_pers : 320 + T_check_pers <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_pers_of : 320 + T_pers_of <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_text_arg : 320 + T_text_arg <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_check_seg7 : 320 + T_check_seg7 <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_check_text_counter : 320 + T_check_text_counter <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_owed_counter_text : 320 + T_owed_counter_text <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_check_text_scribble : 320 + T_check_text_scribble <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_fader : 320 + T_fader <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_button : 320 + T_button <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_touch : 320 + T_touch <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_vpot : 320 + T_vpot <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_jog : 320 + T_jog <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_sysex : 320 + T_sysex <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_ring : 320 + T_ring <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_meter : 320 + T_meter <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_sleds : 320 + T_sleds <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_cleds : 320 + T_cleds <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_scribble : 320 + T_scribble <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_counter : 320 + T_counter <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_check_refusal : 320 + T_check_refusal <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_check_range : 320 + T_check_range <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_check_bytes : 320 + T_check_bytes <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_main_check_masks : 320 + T_check_masks <= T_main_need.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* check_personality's three calls. *)
Lemma sat_T_cp_pers_of : 32 + T_pers_of <= T_check_pers.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_cp_strcmp : 32 + 2 * ESTACK <= T_check_pers.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_cp_from_name : 32 + T_from_name <= T_check_pers.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* check_text_seg7's two calls. *)
Lemma sat_T_cs_seg7 : 48 + T_seg7 <= T_check_seg7.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_cs_owed_seg7 : 48 + T_owed_seg7 <= T_check_seg7.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* check_text_masks's four calls. *)
Lemma sat_T_cm_meter_mask : 48 + T_meter_mask <= T_check_masks.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_cm_meter_segs : 48 + T_meter_segs <= T_check_masks.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_cm_ring_dot : 48 + T_ring_dot <= T_check_masks.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_cm_ring_fill : 48 + T_ring_fill <= T_check_masks.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* check_text_scribble's calls: the frame request, two fills, the library text, the compare. *)
Lemma sat_T_cts_rt : 160 + ESTACK <= T_check_text_scribble.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_cts_scribble_text : 160 + T_scribble_text <= T_check_text_scribble.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_cts_bcmp : 160 + 2 * ESTACK <= T_check_text_scribble.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* check_text_counter's calls. *)
Lemma sat_T_ctc_rt : 192 + ESTACK <= T_check_text_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_ctc_owed : 192 + T_owed_counter_text <= T_check_text_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_ctc_lib : 192 + T_counter_text <= T_check_text_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_ctc_bcmp : 192 + 2 * ESTACK <= T_check_text_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* the two counter-text functions, scribble_encode, and the leaves that call a wrapper. *)
Lemma sat_T_ct_rt : 192 + ESTACK <= T_counter_text.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_ct_seg7 : 192 + T_seg7 <= T_counter_text.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_oct_rt : 192 + ESTACK <= T_owed_counter_text.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_oct_owed_seg7 : 192 + T_owed_seg7 <= T_owed_counter_text.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_sc_rt : 160 + ESTACK <= T_scribble.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_sc_sysex : 160 + T_sysex <= T_scribble.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_sysex_rt : 48 + ESTACK <= T_sysex.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_ring_rt : 48 + ESTACK <= T_ring.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_meter_rt : 48 + ESTACK <= T_meter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_counter_rt : 64 + ESTACK <= T_counter.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_scribble_text_rt : 16 + ESTACK <= T_scribble_text.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_text_arg_rt : 32 + ESTACK <= T_text_arg.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_check_range_bcmp : 32 + 2 * ESTACK <= T_check_range.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_check_bytes_bcmp : 32 + 2 * ESTACK <= T_check_bytes.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sat_T_from_name_strcmp : 48 + 2 * ESTACK <= T_from_name.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* The caller's window premise at the sp it makes the call with. A caller that realigns sp
   (`andi sp,sp,-32`) uses the first lemma, one that only moves sp by its frame the second. *)
Lemma sat_window_aligned : forall sp sp0 STK frame Tc Tf,
  sp mod 16 = 0 -> 0 <= frame -> 0 <= Tf -> sp0 - STK <= sp - Tc -> sp <= sp0 -> frame + 32 + Tf <= Tc ->
  32 * ((sp - frame) / 32) mod 16 = 0 /\
  sp0 - STK <= 32 * ((sp - frame) / 32) - Tf /\
  32 * ((sp - frame) / 32) <= sp0.
Proof.
intros sp sp0 STK frame Tc Tf H16 Hf HTf Hw Hs Hle.
pose proof (Z.mul_div_le (sp - frame) 32 ltac:(lia)) as Hup.
pose proof (Z.mul_succ_div_gt (sp - frame) 32 ltac:(lia)) as Hlo.
split; [|lia].
replace (32 * ((sp - frame) / 32)) with ((2 * ((sp - frame) / 32)) * 16) by lia.
apply Z.mod_mul. lia.
Qed.
Lemma sat_window_plain : forall sp sp0 STK frame Tc Tf,
  sp mod 16 = 0 -> frame mod 16 = 0 -> 0 <= frame -> 0 <= Tf ->
  sp0 - STK <= sp - Tc -> sp <= sp0 -> frame + Tf <= Tc ->
  (sp - frame) mod 16 = 0 /\ sp0 - STK <= sp - frame - Tf /\ sp - frame <= sp0.
Proof.
intros sp sp0 STK frame Tc Tf H16 Hf16 Hf HTf Hw Hs Hle.
split; [|lia]. rewrite Zminus_mod, H16, Hf16. reflexivity.
Qed.

Lemma mod64_mod8 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 64 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (64 * (x / 64)) with ((8 * (x / 64)) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma div8_of_mod8 : forall F k, F mod 8 = 0 -> (F + k) / 8 = F / 8 + k / 8.
Proof.
intros F k H. pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
rewrite D at 1. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* The shadow bytes of the 8-byte window a wrapper reads around an object of a side-stack frame are the
   frame's own shadow bytes, so AR_frames_law gives them. *)
Lemma sat_frame_hull : forall lyc Sc W memc mdc cid pos F off n,
  AR segs B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos = F -> F mod 64 = 0 -> fs_frame_bytes cid mod 64 = 0 ->
  0 <= off -> 0 < n -> off + n <= fs_frame_bytes cid ->
  shadow_hull_vis (aview segs (w_H W) memc) (F + off) n.
Proof.
intros lyc Sc W memc mdc cid pos F off n HAR Hin HF H64 HFS Ho Hn Hon s Hs.
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (A1 & A2 & A3 & A4).
rewrite HF in A4.
set (fs := fs_frame_bytes cid) in *.
assert (HF8 : F mod 8 = 0) by (apply mod64_mod8; exact H64).
assert (Hfs8 : fs mod 8 = 0) by (apply mod64_mod8; exact HFS).
assert (Hfspos : 0 < fs) by lia.
(* the frame's own shadow base is 8-aligned *)
assert (HSF : shadow_addr F = 8 * (SHADOW_OFF / 8 + F / 64)).
{ unfold shadow_addr.
  pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite H64, Z.add_0_r in D.
  assert (E : F / 8 = 8 * (F / 64)).
  { rewrite D at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (ES : SHADOW_OFF / 8 = 268431360) by (vm_compute; reflexivity).
  rewrite E, ES. unfold SHADOW_OFF. lia. }
set (M := SHADOW_OFF / 8 + F / 64) in *.
assert (E1 : shadow_addr (F + off) = shadow_addr F + off / 8).
{ unfold shadow_addr. rewrite (div8_of_mod8 F off HF8). lia. }
assert (E2 : shadow_addr (F + off + n - 1) = shadow_addr F + (off + n - 1) / 8).
{ unfold shadow_addr. replace (F + off + n - 1) with (F + (off + n - 1)) by lia.
  rewrite (div8_of_mod8 F (off + n - 1) HF8). lia. }
assert (Elo : shadow_addr (F + off) / 8 * 8 = shadow_addr F + (off / 8) / 8 * 8).
{ rewrite E1, HSF, (Z.mul_comm 8 M), (Z.div_add_l M 8 (off / 8) ltac:(lia)). lia. }
assert (Ehi : shadow_addr (F + off + n - 1) / 8 * 8 = shadow_addr F + ((off + n - 1) / 8) / 8 * 8).
{ rewrite E2, HSF, (Z.mul_comm 8 M), (Z.div_add_l M 8 ((off + n - 1) / 8) ltac:(lia)). lia. }
rewrite Elo, Ehi in Hs.
(* the window stays inside the frame's fs / 8 shadow bytes *)
assert (Hd1 : 0 <= (off / 8) / 8 * 8).
{ pose proof (Z.div_pos off 8 ltac:(lia) ltac:(lia)) as H1.
  pose proof (Z.div_pos (off / 8) 8 ltac:(lia) ltac:(lia)). lia. }
assert (Hd2 : ((off + n - 1) / 8) / 8 * 8 + 8 <= fs / 8).
{ assert (Hle : (off + n - 1) / 8 <= (fs - 1) / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_mod fs 8 ltac:(lia)) as Dfs. rewrite Hfs8, Z.add_0_r in Dfs.
  assert (Hfs64 : fs / 8 mod 8 = 0).
  { pose proof (Z.div_mod fs 64 ltac:(lia)) as D64. rewrite HFS, Z.add_0_r in D64.
    assert (E : fs / 8 = 8 * (fs / 64)).
    { rewrite D64 at 1. replace (64 * (fs / 64)) with ((8 * (fs / 64)) * 8) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
    rewrite E. replace (8 * (fs / 64)) with ((fs / 64) * 8) by lia. apply Z.mod_mul. lia. }
  assert (Hfsm1 : (fs - 1) / 8 = fs / 8 - 1).
  { rewrite Dfs at 1. replace (8 * (fs / 8) - 1) with ((fs / 8 - 1) * 8 + 7) by lia.
    rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
  rewrite Hfsm1 in Hle.
  pose proof (Z.div_mod (fs / 8) 8 ltac:(lia)) as D2. rewrite Hfs64, Z.add_0_r in D2.
  assert (Hq : ((off + n - 1) / 8) / 8 <= fs / 8 / 8 - 1).
  { assert (Hle2 : (off + n - 1) / 8 / 8 <= (fs / 8 - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (E3 : (fs / 8 - 1) / 8 = fs / 8 / 8 - 1).
    { rewrite D2 at 1. replace (8 * (fs / 8 / 8) - 1) with ((fs / 8 / 8 - 1) * 8 + 7) by lia.
      rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
    lia. }
  lia. }
destruct (A4 (s - shadow_addr F) ltac:(lia)) as (Hp & _).
replace (shadow_addr F + (s - shadow_addr F)) with s in Hp by lia.
exact (aview_some_of_apresent segs (w_H W) memc s Hp).
Qed.

(* A range a call writes, at a fixed offset of a side-stack frame the caller owns, inside an 8-aligned
   object [F + boff, F + boff + bn) whose shadow map the caller's walk carries. *)
Lemma sat_frame_dst_in : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (sp T : Z) (cid pos F boff bn off n : Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (cid, pos) own -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos = F -> F mod 64 = 0 -> fs_frame_bytes cid mod 64 = 0 ->
  0 <= boff -> boff <= off -> 0 < n -> off + n <= boff + bn -> boff + bn <= fs_frame_bytes cid ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + boff) bn ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + off) n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T cid pos F boff bn off n
HJ Hown Hin HF H64 HFS Hb0 Hbo Hn Hon Hbfs HBS HT Hwin Hest.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & _).
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (A1 & A2 & A3 & A4).
rewrite HF in Hf4096, Hfceil, Hfapp, A3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hbyte : forall a, F + off <= a < F + off + n -> F <= a < F + fs_frame_bytes cid) by lia.
split; [lia|]. split; [unfold kLowShadowBeg, kHighMemBeg, in_app in *; lia|].
split.
{ intros a Ha. right. exists cid, pos. split; [exact Hin|].
  unfold frame_rng, in_zr. cbn [fst snd]. rewrite HF. lia. }
split.
{ intros a Ha. destruct (A3 a (Hbyte a Ha)) as (Hp & Hno).
  split; [|split; [exact Hp | split; [exact Hno | lia]]].
  right. right. right. exists cid, pos. split; [exact Hown|]. left.
  unfold in_zr. cbn [fst snd]. rewrite HF. lia. }
split; [apply (block_shadow_range (aview segs (w_H W) memc) SHADOW_OFF (F + boff) bn (F + off) n HBS); lia|].
split; [intros _; exact (sat_frame_hull lyc Sc W memc mdc cid pos F off n HAR Hin HF H64 HFS ltac:(lia) Hn ltac:(lia))|].
split.
{ unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
left. lia.
Qed.
Lemma sat_frame_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (sp T : Z) (cid pos F off n : Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (cid, pos) own -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos = F -> F mod 64 = 0 -> fs_frame_bytes cid mod 64 = 0 ->
  0 <= off -> 0 < n -> off + n <= fs_frame_bytes cid ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + off) n ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + off) n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T cid pos F off n
HJ Hown Hin HF H64 HFS Ho Hn Hon HBS HT Hwin Hest.
exact (sat_frame_dst_in STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T cid pos F off n off n
  HJ Hown Hin HF H64 HFS Ho ltac:(lia) Hn ltac:(lia) Hon HBS HT Hwin Hest).
Qed.

(* A range a call reads, at a fixed offset of a side-stack frame, inside an 8-aligned object. *)
Lemma sat_frame_rd_in : forall lyc Sc W memc mdc (sp T : Z) (cid pos F boff bn off n STK sp0 : Z),
  AR segs B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos = F -> F mod 64 = 0 -> fs_frame_bytes cid mod 64 = 0 ->
  0 <= boff -> boff <= off -> 0 < n -> off + n <= boff + bn -> boff + bn <= fs_frame_bytes cid ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + boff) bn ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + off) n.
Proof.
intros lyc Sc W memc mdc sp T cid pos F boff bn off n STK sp0 HAR Hin HF H64 HFS Hb0 Hbo Hn Hon Hbfs HBS Hceil Hwin.
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (A1 & A2 & A3 & A4).
rewrite HF in Hf4096, Hfceil, Hfapp, A3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [unfold kLowShadowBeg, kHighMemBeg, in_app in *; lia|].
split.
{ intros a Ha. destruct (A3 a ltac:(lia)) as (Hp & _).
  exact (aview_some_of_apresent segs (w_H W) memc a Hp). }
split; [apply (block_shadow_range (aview segs (w_H W) memc) SHADOW_OFF (F + boff) bn (F + off) n HBS); lia|].
split; [intros _; exact (sat_frame_hull lyc Sc W memc mdc cid pos F off n HAR Hin HF H64 HFS ltac:(lia) Hn ltac:(lia))|].
split.
{ unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
left. lia.
Qed.
Lemma sat_frame_rd : forall lyc Sc W memc mdc (sp T : Z) (cid pos F off n STK sp0 : Z),
  AR segs B lyc Sc W memc mdc -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos = F -> F mod 64 = 0 -> fs_frame_bytes cid mod 64 = 0 ->
  0 <= off -> 0 < n -> off + n <= fs_frame_bytes cid ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + off) n ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + off) n.
Proof.
intros lyc Sc W memc mdc sp T cid pos F off n STK sp0 HAR Hin HF H64 HFS Ho Hn Hon HBS Hceil Hwin.
exact (sat_frame_rd_in lyc Sc W memc mdc sp T cid pos F off n off n STK sp0
  HAR Hin HF H64 HFS Ho ltac:(lia) Hn ltac:(lia) Hon HBS Hceil Hwin).
Qed.

(* A range of the image a call reads, and a range inside one: the start-up certificate of the registered
   globals marks the row usable in EVERY state, which is the form the contracts ask for, because neither
   a side-stack frame request nor a call keeps the shadow byte of a global. *)
Lemma sat_img_usable : forall (G : list (Z * Z)) (q sz a n : Z),
  globs_marked segs B G -> In (q, sz) G -> img_shadow_vis segs B ->
  q <= a -> a + n <= q + sz -> 0 < n ->
  IMG_LO + 64 <= a -> a + n + 64 <= IMG_HI ->
  cimg_usable segs B a n.
Proof.
intros G q sz a n HG Hin HV Hqa Han Hn Hlo Hhi ly' S' W' mem' md' HAR.
split; [exact (ro_usable_glob segs B G ly' S' W' mem' md' q sz a n HG Hin HAR Hqa Han)|].
intros _. exact (ro_hull segs B ly' S' W' mem' md' a n HV HAR Hn Hlo Hhi).
Qed.
Lemma sat_img_rd_in : forall (G : list (Z * Z)) (sp T q sz a n : Z),
  globs_marked segs B G -> In (q, sz) G -> img_shadow_vis segs B ->
  q <= a -> a + n <= q + sz -> 0 < n -> 0 <= a ->
  IMG_LO + 64 <= a -> a + n + 64 <= IMG_HI -> a + n <= 2 ^ 63 ->
  (forall x, a <= x < a + n ->
     in_img segs x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
  amem_range a n -> a + n <= sp - T ->
  cimg_range segs B sp T a n.
Proof.
intros G sp T q sz a n HG Hin HV Hqa Han Hn Ha0 Hlo Hhi H63 Hst Hmem Hwin.
split; [exact Ha0|]. split; [exact Hn|]. split; [lia|]. split; [exact Hmem|].
split; [left; exact Hwin|]. split; [exact Hst|].
exact (sat_img_usable G q sz a n HG Hin HV Hqa Han Hn Hlo Hhi).
Qed.
Lemma sat_img_rd : forall (G : list (Z * Z)) (sp T q sz : Z),
  globs_marked segs B G -> In (q, sz) G -> img_shadow_vis segs B ->
  0 < sz -> 0 <= q -> IMG_LO + 64 <= q -> q + sz + 64 <= IMG_HI -> q + sz <= 2 ^ 63 ->
  (forall x, q <= x < q + sz ->
     in_img segs x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
  amem_range q sz -> q + sz <= sp - T ->
  cimg_range segs B sp T q sz.
Proof.
intros G sp T q sz HG Hin HV Hsz Hq0 Hlo Hhi H63 Hst Hmem Hwin.
exact (sat_img_rd_in G sp T q sz q sz HG Hin HV ltac:(lia) ltac:(lia) Hsz Hq0 Hlo Hhi H63 Hst Hmem Hwin).
Qed.
(* A caller object that lies in one live side-stack frame of the call state, or in one heap block. *)
Lemma sat_cobj_frame : forall lyc Sc cid pos F off n,
  In (cid, pos) (frames Sc) -> frame_addr lyc cid pos = F ->
  0 <= off -> off + n <= fs_frame_bytes cid ->
  cobj_ok B lyc Sc (F + off) n.
Proof.
intros lyc Sc cid pos F off n Hin HF Ho Hon. right. exists cid, pos.
split; [exact Hin|]. rewrite HF. split; lia.
Qed.
Lemma sat_cobj_block : forall lyc Sc b m q n,
  In (b, m) (ablocks B lyc Sc) -> b <= q -> q + n <= b + req_size m ->
  cobj_ok B lyc Sc q n.
Proof.
intros lyc Sc b m q n Hin H1 H2. left. exists b, m. split; [exact Hin | split; [exact H1 | exact H2]].
Qed.
(* the entry function's class-3 frame: text (F + 64, 65), the call record's bytes (F + 216, 24) and out
   (F + 284, 32), the dots byte (F + 432, 1) *)
Lemma sat_main_cobj : forall lyc Sc pos F off n,
  In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> 0 <= off -> off + n <= 512 ->
  cobj_ok B lyc Sc (F + off) n.
Proof.
intros lyc Sc pos F off n Hin HF Ho Hon.
assert (Hfs : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
exact (sat_cobj_frame lyc Sc 3 pos F off n Hin HF Ho ltac:(rewrite Hfs; lia)).
Qed.
(* the class-0 frames of check_text_scribble and check_text_counter: their comparison buffer at F + 32 *)
Lemma sat_c0_cobj : forall lyc Sc pos F off n,
  In (0, pos) (frames Sc) -> frame_addr lyc 0 pos = F -> 0 <= off -> off + n <= 64 ->
  cobj_ok B lyc Sc (F + off) n.
Proof.
intros lyc Sc pos F off n Hin HF Ho Hon.
assert (Hfs : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
exact (sat_cobj_frame lyc Sc 0 pos F off n Hin HF Ho ltac:(rewrite Hfs; lia)).
Qed.

(* The per-byte clause of cimg_range, from the two facts a caller decides over the image's own lists and
   one numeric disjointness from the errno word. *)
Lemma sat_img_bytes_ok : forall (q n : Z),
  (forall x, q <= x < q + n -> in_img segs x) ->
  (forall x, q <= x < q + n -> ~ Exists (in_zr x) (as_owned_static B)) ->
  (as_errno B + 4 <= q \/ q + n <= as_errno B) ->
  forall x, q <= x < q + n ->
    in_img segs x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Proof.
intros q n Himg Hst Herr x Hx.
split; [exact (Himg x Hx)|]. split; [exact (Hst x Hx)|]. lia.
Qed.

(* A range a call writes on the caller's machine stack, above the sp it makes the call with (text_arg's
   cursor struct, check_text_counter's dots byte): inside the caller's own window [sp0 - STK, sp0), whose
   shadow is zero in every state (the stack row of zero_shadow_ranges, AR_zshadow_law). *)
Lemma sat_stack_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (sp T q n : Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> 0 < n ->
  sp0 - STK <= q -> q + n + 64 <= sp0 -> sp <= q -> 0 <= T ->
  cdstk_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T q n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T q n HJ Hn Hlo Hhi Hsp HT.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the stack's shadow row, and the 8-alignment of its low end *)
pose proof (al_zshadow _ _ LAWS lyc Sc W memc mdc _ HAR (or_introl eq_refl)) as Hz. cbn [fst snd] in Hz.
assert (Hal8 : ly_stk_lo lyc mod 8 = 0).
{ destruct HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_top _ LO) as (_ & _ & _ & _ & T5 & _). unfold page_aligned in T5.
  apply Z.mod_divide; [lia|]. apply Z.mod_divide in T5 as [m Hm]; [|lia]. exists (m * 512). lia. }
assert (Hal64 : ly_stk_lo lyc mod 64 = 0).
{ destruct HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_top _ LO) as (_ & _ & _ & _ & T5 & _). unfold page_aligned in T5.
  apply Z.mod_divide; [lia|]. apply Z.mod_divide in T5 as [m Hm]; [|lia]. exists (m * 64). lia. }
rewrite Eslo, Eshi in *.
set (lo := ly_stk_lo ly) in *. set (hi := ly_stk_hi ly) in *.
(* every shadow byte of the stack's granules is zero *)
assert (Hzi : forall x, lo <= x -> x + 8 <= hi -> aview segs (w_H W) memc (SHADOW_OFF + x / 8) = Some 0).
{ intros x Hx1 Hx2.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as D1. rewrite Hal8, Z.add_0_r in D1.
  assert (E : SHADOW_OFF + x / 8 = shadow_of_addr SHADOW_OFF lo + (x / 8 - lo / 8)) by (unfold shadow_of_addr; lia).
  rewrite E. apply Hz.
  assert (Hle : lo / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (Hup : x / 8 + 1 <= hi / 8).
  { replace (x / 8 + 1) with ((x + 8) / 8) by (rewrite <- (Z.div_add (x) 1 8) by lia; f_equal; lia).
    apply Z.div_le_mono; lia. }
  assert (Ehl : (hi - lo) / 8 = hi / 8 - lo / 8).
  { rewrite D1 at 1. replace (hi - 8 * (lo / 8)) with (hi + (- (lo / 8)) * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  lia. }
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha. split; [left; lia|]. split; [apply Hpres; lia|]. split; [|lia].
  apply (al_stack _ _ LAWS lyc Sc W memc mdc a HAR). rewrite Eslo, Eshi. lia. }
split.
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. apply Hzi; lia. }
split.
{ intros _ s Hs. unfold shadow_addr in Hs.
  pose proof (Z.div_mod lo 64 ltac:(lia)) as D64. rewrite Hal64, Z.add_0_r in D64.
  assert (ES : SHADOW_OFF = 8 * 268431360) by (unfold SHADOW_OFF; lia).
  set (u := s - SHADOW_OFF).
  assert (Hu1 : lo / 8 <= u).
  { assert (Hq8 : lo / 8 <= q / 8) by (apply Z.div_le_mono; lia).
    assert (Hl8 : lo / 8 = 8 * (lo / 64)).
    { rewrite D64 at 1. replace (64 * (lo / 64)) with ((8 * (lo / 64)) * 8) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
    assert (Hfl : (SHADOW_OFF + q / 8) / 8 * 8 = SHADOW_OFF + q / 8 / 8 * 8).
    { rewrite ES, (Z.mul_comm 8 268431360), (Z.div_add_l 268431360 8 (q / 8)) by lia. lia. }
    assert (Hm : lo / 8 <= q / 8 / 8 * 8).
    { rewrite Hl8. assert (lo / 64 <= q / 8 / 8).
      { assert (E2 : lo / 64 = (lo / 8) / 8) by (rewrite Hl8, (Z.mul_comm 8 (lo / 64)), (Z.div_mul (lo / 64) 8) by lia; reflexivity).
        rewrite E2. apply Z.div_le_mono; lia. }
      lia. }
    unfold u. lia. }
  assert (Hu2 : u + 1 <= hi / 8).
  { assert (Hfl : (SHADOW_OFF + (q + n - 1) / 8) / 8 * 8 = SHADOW_OFF + (q + n - 1) / 8 / 8 * 8).
    { rewrite ES, (Z.mul_comm 8 268431360), (Z.div_add_l 268431360 8 ((q + n - 1) / 8)) by lia. lia. }
    pose proof (Z.mul_div_le ((q + n - 1) / 8) 8 ltac:(lia)) as Hd.
    assert (Hq : (q + n - 1) / 8 + 8 <= hi / 8).
    { replace ((q + n - 1) / 8 + 8) with ((q + n - 1 + 64) / 8)
        by (rewrite <- (Z.div_add (q + n - 1) 8 8) by lia; f_equal; lia).
      apply Z.div_le_mono; lia. }
    unfold u. lia. }
  replace s with (SHADOW_OFF + (8 * u) / 8) by (rewrite (Z.mul_comm 8 u), (Z.div_mul u 8) by lia; unfold u; lia).
  rewrite (Hzi (8 * u)); [discriminate| |].
  - assert (lo <= 8 * (lo / 8)) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia). lia.
  - pose proof (Z.mul_div_le hi 8 ltac:(lia)). lia. }
split.
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. right. lia. }
right. exact Hsp.
Qed.

(* A range a call reads inside a heap block of the call state (the input bytes): the block's shadow and
   its 8-byte window are AR_shadow_law's. *)
Lemma sat_block_rd : forall lyc Sc W memc mdc (sp T b m q n STK sp0 : Z),
  AR segs B lyc Sc W memc mdc -> In (b, m) (ablocks B lyc Sc) ->
  b <= q -> 0 <= n -> q + n <= b + req_size m ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T q n.
Proof.
intros lyc Sc W memc mdc sp T b m q n STK sp0 HAR Hin Hbq Hn Hqn Hceil Hwin.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & H4096 & Hbceil & Happ & Hpres & _).
destruct (al_shadow _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (HBS & HHV).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (req_size_pos m) as Hrs.
split; [lia|]. split; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ; lia|].
split.
{ intros a Ha. destruct (Hpres a ltac:(lia)) as (Hp & _).
  exact (aview_some_of_apresent segs (w_H W) memc a Hp). }
split; [apply (block_shadow_range (aview segs (w_H W) memc) SHADOW_OFF b (req_size m) q n HBS); lia|].
split.
{ intros Hn0 s Hs. apply HHV. unfold shadow_addr in *.
  assert (H1 : b / 8 <= q / 8) by (apply Z.div_le_mono; lia).
  assert (H2 : (q + n - 1) / 8 <= (b + req_size m - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (H3 : (SHADOW_OFF + b / 8) / 8 <= (SHADOW_OFF + q / 8) / 8) by (apply Z.div_le_mono; lia).
  assert (H4 : (SHADOW_OFF + (q + n - 1) / 8) / 8 <= (SHADOW_OFF + (b + req_size m - 1) / 8) / 8)
    by (apply Z.div_le_mono; lia).
  lia. }
split.
{ unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
left. lia.
Qed.

(* ===================== the objects at the call sites of image A =====================
   The entry function's side-stack frame is of class 3 (448 of the 512 bytes it holds requested at
   0x808bc). Its objects, at the offsets the prologue's shadow map gives: the payload of the counter
   command at F + 32 (10 bytes), text[65] at F + 64, the 184-byte call record k at F + 176, and inside
   it k.bytes at F + 216 (24), k.out at F + 284 (32) and k.want at F + 320 (24), and the dots byte at
   F + 432. Each lemma below is the premise of one argument of one call, at that offset. The ranges
   inside k take k's own shadow map (23 zero bytes from 0x80af4 to 0x8275c), since out is not 8-aligned. *)
Lemma sat_main_out_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (3, pos) own -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 176) 184 ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + 284) 32.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F HJ H1 H2 HF H64 HBS HT Hw He.
exact (sat_frame_dst_in STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T 3 pos F 176 184 284 32
  HJ H1 H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS HT Hw He).
Qed.
(* sysex's payload: the first n bytes of k.bytes, n = k.n in 1 .. 24 *)
Lemma sat_main_bytes_rd_n : forall lyc Sc W memc mdc sp T pos F STK sp0 n,
  AR segs B lyc Sc W memc mdc -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  0 < n -> n <= 24 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 176) 184 ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + 216) n.
Proof.
intros lyc Sc W memc mdc sp T pos F STK sp0 n HAR H2 HF H64 Hn Hn24 HBS Hc Hw.
exact (sat_frame_rd_in lyc Sc W memc mdc sp T 3 pos F 176 184 216 n STK sp0
  HAR H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hn ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS Hc Hw).
Qed.
Lemma sat_main_bytes_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (3, pos) own -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 216) 24 ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + 216) 24.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F HJ H1 H2 HF H64 HBS HT Hw He.
exact (sat_frame_dst STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T 3 pos F 216 24
  HJ H1 H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS HT Hw He).
Qed.
Lemma sat_main_text_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (3, pos) own -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 64) 65 ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + 64) 65.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F HJ H1 H2 HF H64 HBS HT Hw He.
exact (sat_frame_dst STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T 3 pos F 64 65
  HJ H1 H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS HT Hw He).
Qed.
Lemma sat_main_dots_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (3, pos) own -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 432) 1 ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + 432) 1.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F HJ H1 H2 HF H64 HBS HT Hw He.
exact (sat_frame_dst STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T 3 pos F 432 1
  HJ H1 H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS HT Hw He).
Qed.
(* the call record, and the three ranges inside it the checks read *)
Lemma sat_main_k_rd : forall lyc Sc W memc mdc sp T pos F STK sp0,
  AR segs B lyc Sc W memc mdc -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 176) 184 ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + 176) 184.
Proof.
intros lyc Sc W memc mdc sp T pos F STK sp0 HAR H2 HF H64 HBS Hc Hw.
exact (sat_frame_rd lyc Sc W memc mdc sp T 3 pos F 176 184 STK sp0
  HAR H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS Hc Hw).
Qed.
Lemma sat_main_bytes_rd : forall lyc Sc W memc mdc sp T pos F STK sp0,
  AR segs B lyc Sc W memc mdc -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 216) 24 ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + 216) 24.
Proof.
intros lyc Sc W memc mdc sp T pos F STK sp0 HAR H2 HF H64 HBS Hc Hw.
exact (sat_frame_rd lyc Sc W memc mdc sp T 3 pos F 216 24 STK sp0
  HAR H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS Hc Hw).
Qed.
Lemma sat_main_text_rd : forall lyc Sc W memc mdc sp T pos F STK sp0,
  AR segs B lyc Sc W memc mdc -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 64) 65 ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + 64) 65.
Proof.
intros lyc Sc W memc mdc sp T pos F STK sp0 HAR H2 HF H64 HBS Hc Hw.
exact (sat_frame_rd lyc Sc W memc mdc sp T 3 pos F 64 65 STK sp0
  HAR H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS Hc Hw).
Qed.
Lemma sat_main_pl_rd : forall lyc Sc W memc mdc sp T pos F STK sp0,
  AR segs B lyc Sc W memc mdc -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F -> F mod 64 = 0 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 32) 10 ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + 32) 10.
Proof.
intros lyc Sc W memc mdc sp T pos F STK sp0 HAR H2 HF H64 HBS Hc Hw.
exact (sat_frame_rd lyc Sc W memc mdc sp T 3 pos F 32 10 STK sp0
  HAR H2 HF H64 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) HBS Hc Hw).
Qed.
(* The frames of class 0 (64 bytes: check_text_scribble, check_text_counter, diginet_scribble_encode)
   and of class 1 (128 bytes: diginet_counter_text, owed_counter_text). The object of a class-0 frame is
   at offset 32 (the 8-byte comparison buffer of check_text_scribble / check_text_counter, or
   scribble_encode's 10 payload bytes); a class-1
   frame holds the eight digits at offset 32 and the 32 bytes of dot flags at offset 64. *)
Lemma sat_c0_obj_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F n,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (0, pos) own -> In (0, pos) (frames Sc) -> frame_addr lyc 0 pos = F -> F mod 64 = 0 ->
  0 < n -> n <= 24 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + 32) n ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + 32) n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F n HJ H1 H2 HF H64 Hn Hn24 HBS HT Hw He.
assert (Hfs : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
exact (sat_frame_dst STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T 0 pos F 32 n
  HJ H1 H2 HF H64 ltac:(rewrite Hfs; reflexivity) ltac:(lia) Hn ltac:(rewrite Hfs; lia) HBS HT Hw He).
Qed.
Lemma sat_c1_obj_dst : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F off n,
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (1, pos) own -> In (1, pos) (frames Sc) -> frame_addr lyc 1 pos = F -> F mod 64 = 0 ->
  32 <= off -> 0 < n -> off + n <= 128 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + off) n ->
  0 <= T -> sp0 - STK <= sp - T -> sp0 - STK + ESTACK <= sp ->
  cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T (F + off) n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T pos F off n
HJ H1 H2 HF H64 Ho Hn Hon HBS HT Hw He.
assert (Hfs : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
exact (sat_frame_dst STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp T 1 pos F off n
  HJ H1 H2 HF H64 ltac:(rewrite Hfs; reflexivity) ltac:(lia) Hn ltac:(rewrite Hfs; lia) HBS HT Hw He).
Qed.
Lemma sat_c1_obj_rd : forall lyc Sc W memc mdc sp T pos F off n STK sp0,
  AR segs B lyc Sc W memc mdc -> In (1, pos) (frames Sc) -> frame_addr lyc 1 pos = F -> F mod 64 = 0 ->
  32 <= off -> 0 < n -> off + n <= 128 ->
  block_shadow (aview segs (w_H W) memc) SHADOW_OFF (F + off) n ->
  alloc_ceiling <= sp0 - STK -> sp0 - STK <= sp - T ->
  crd_ok segs W memc sp T (F + off) n.
Proof.
intros lyc Sc W memc mdc sp T pos F off n STK sp0 HAR H2 HF H64 Ho Hn Hon HBS Hc Hw.
assert (Hfs : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
exact (sat_frame_rd lyc Sc W memc mdc sp T 1 pos F off n STK sp0
  HAR H2 HF H64 ltac:(rewrite Hfs; reflexivity) ltac:(lia) Hn ltac:(rewrite Hfs; lia) HBS Hc Hw).
Qed.

(* `This byte is not the runtime's own`, which a walk needs to carry a value past its own frame request
   (astack_malloc_realizes keeps a byte only when it is not the runtime's in the state before and in the
   state after). A byte of a live side-stack frame is the client's; an image byte is the runtime's
   exactly when it lies in one of its own statics (AR_owned_image_law). The contracts give cobj_ok and
   cimg_range, and these two turn them into that form. *)
Lemma sat_frame_not_owned : forall lyc Sc cid pos x,
  In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid ->
  ~ aowned B lyc Sc x.
Proof.
intros lyc Sc cid pos x Hin Hx [_ Hnc]. apply Hnc. right. exists (cid, pos).
split; [exact Hin | left; unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma sat_img_not_owned : forall lyc Sc W memc mdc x,
  AR segs B lyc Sc W memc mdc -> in_img segs x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ aowned B lyc Sc x.
Proof.
intros lyc Sc W memc mdc x HAR Hi Hs Ho.
exact (Hs (proj1 (al_owned_image _ _ LAWS lyc Sc W memc mdc x HAR Hi) Ho)).
Qed.
End c.
End b.
