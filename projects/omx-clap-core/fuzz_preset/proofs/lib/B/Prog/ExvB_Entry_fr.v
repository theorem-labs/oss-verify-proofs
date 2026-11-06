(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value (B 0x8352c), ENTRY segment C0: ONE leg of the segment's kept package (ExvB_Entry.v's `exve_kept`), for a
   stretch that writes INSIDE ex_value's own class-1 fake frame (1, pos) - the frame header at f + 0 / 8 / 16, i.e.
   [f, f + 24), and the frame's twelve shadow bytes [shadow_addr f, shadow_addr f + 12) - plus a window [lo, hi) at or
   above the allocation ceiling (the slot 176(s1)).
   `exve_kept_of_frame` concludes the four conjuncts of `exve_kept` at (E, W, W, mem, mem', fun a => lo <= a < hi),
   spelled out: ExvB_Entry.v imports THIS file, so this file does not import it. The helpers `exvf_blk_low` /
   `exvf_frm_low` restate ExvB_Entry.v's `exve_blk_low` / `exve_frm_low` (a live block, a live frame lie below the
   allocation ceiling and in the application range; from alx_blocks / frames_bounds_x), at any ARx state rather than
   at the entry's, with the frame's alignment and size granularity added.
   The argument (S8aEntry.v KEEPhi / KEEPblk / KEEPimg / KEEPfrm, origin/cold/h-hpreset-7-walk-S8a): the frame and its
   shadow lie below the ceiling (frames_bounds_x, alloc_ceiling_val); a live block is apart from the frame
   (sep_block_frame_x) and, being in the application range (alx_blocks' in_app), from every shadow byte; an image
   byte is not a frame byte (frm_img_x) and lies below SHADOW_OFF (B_prog_segs_low); another live frame's bytes are
   apart from this frame's (sep_frames_pos_x) and, both frames 32-aligned (alx_frames) with sizes multiples of 8
   (eh_frames_cid: 0 <= cid), so are the two shadow ranges.
   NUMERALS: 24 / 12 (LENGTH: the header bytes and the shadow bytes written); 128 / 16 (LENGTH: the class-1 frame's
   bytes and its shadow bytes); 8 / 32 / 4 (LENGTH: the shadow granule, the frame alignment, their ratio); 4096 /
   2 ^ 64 (LENGTH: address-space bounds); 17592184995840 (DERIVED: CEIL_MAX / 8, checked by lia from YM05's
   CEIL_MAX). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP03 YP0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallSx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- pure arithmetic of the shadow map ---- *)
(* a range [g, g + s) at or above 0 and below the ceiling has its shadow in [SHADOW_OFF, SHADOW_OFF + CEIL_MAX / 8] *)
Lemma exvf_sh_rng {rc : YM05.RunCeil} : forall g s, 0 <= g -> 0 <= s -> g + s <= alloc_ceiling ->
  SHADOW_OFF <= shadow_addr g /\ shadow_addr g + s / 8 <= SHADOW_OFF + 17592184995840.
Proof.
intros g s Hg Hs Hc. pose proof alloc_ceiling_val as (AC & _).
pose proof (Z.div_mod g 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound g 8 ltac:(lia)) as M1.
pose proof (Z.div_mod s 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound s 8 ltac:(lia)) as M2.
assert (P1 : 0 <= g / 8) by (apply Z.div_pos; lia).
unfold shadow_addr. lia.
Qed.

(* two 32-aligned ranges apart, the second 128 bytes, the first's size a multiple of 8: their shadows are apart *)
Lemma exvf_sh_apart : forall f g s, f mod 32 = 0 -> g mod 32 = 0 -> s mod 8 = 0 ->
  (f + 128 <= g \/ g + s <= f) ->
  shadow_addr g + s / 8 <= shadow_addr f \/ shadow_addr f + 16 <= shadow_addr g.
Proof.
intros f g s Hf Hg Hs Hd. unfold shadow_addr.
apply (proj1 (Z.mod_divide f 32 ltac:(lia))) in Hf as (kf & ->).
apply (proj1 (Z.mod_divide g 32 ltac:(lia))) in Hg as (kg & ->).
apply (proj1 (Z.mod_divide s 8 ltac:(lia))) in Hs as (ks & ->).
assert (E1 : kf * 32 / 8 = kf * 4) by (replace (kf * 32) with (kf * 4 * 8) by ring; apply Z.div_mul; lia).
assert (E2 : kg * 32 / 8 = kg * 4) by (replace (kg * 32) with (kg * 4 * 8) by ring; apply Z.div_mul; lia).
assert (E3 : ks * 8 / 8 = ks) by (apply Z.div_mul; lia).
rewrite E1, E2, E3. lia.
Qed.

Section F. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

(* ExvB_Entry.v's exve_blk_low, at any ARx state: a live block lies below the ceiling and in the application range *)
Lemma exvf_blk_low : forall ly S Hp (W : world rsegs) mem md b n,
  ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) ->
  4096 <= b /\ b + req_size n <= alloc_ceiling /\ in_app b (req_size n).
Proof.
intros ly S Hp W mem md b n HAR Hb.
destruct (alx_blocks rsegs B ARx (eh_laws B ARx SK HYP) ly S Hp W mem md b n HAR Hb) as (_ & H1 & H2 & H3 & _).
auto.
Qed.

(* ExvB_Entry.v's exve_frm_low, at any ARx state: a live frame lies below the ceiling and in the application range,
   32-aligned, its size a multiple of 8 *)
Lemma exvf_frm_low : forall ly S Hp (W : world rsegs) mem md cid p,
  ARx ly S Hp W mem md -> In (cid, p) (frames S) ->
  4096 <= frame_addr ly cid p /\ frame_addr ly cid p + fs_frame_bytes cid <= alloc_ceiling /\
  in_app (frame_addr ly cid p) (fs_frame_bytes cid) /\ frame_addr ly cid p mod 32 = 0 /\
  fs_frame_bytes cid mod 8 = 0.
Proof.
intros ly S Hp W mem md cid p HAR Hin.
destruct (frames_bounds_x rsegs B ARx (eh_laws B ARx SK HYP) ly S Hp W mem md cid p HAR Hin) as (F1 & F2 & F3).
destruct (alx_frames rsegs B ARx (eh_laws B ARx SK HYP) ly S Hp W mem md cid p HAR Hin) as (F4 & _).
pose proof (eh_frames_cid B ARx SK HYP ly S Hp W mem md cid p HAR Hin) as (C0 & _).
split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|].
unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by exact C0.
replace (64 * 2 ^ cid) with (8 * 2 ^ cid * 8) by ring. apply Z.mod_mul. lia.
Qed.

(* THE LEG: a stretch whose writes are the frame header [f, f + 24), the frame's twelve shadow bytes and a window at
   or above the ceiling keeps the entry's bytes in exve_kept's four shapes *)
Lemma exve_kept_of_frame : forall (E : exv_e) (Sc : astate) Hpc (W : world rsegs) mem md mem' (pos lo hi : Z),
  EXV_PRE B ARx E -> ARx (e_ly E) Sc Hpc W mem md ->
  ablocks B (e_ly E) Sc = ablocks B (e_ly E) (e_S E) ->
  incl (frames (e_S E)) (frames Sc) -> In (1, pos) (frames Sc) -> ~ In (1, pos) (frames (e_S E)) ->
  alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     ~ (frame_addr (e_ly E) 1 pos <= a < frame_addr (e_ly E) 1 pos + 24) ->
     ~ (shadow_addr (frame_addr (e_ly E) 1 pos) <= a < shadow_addr (frame_addr (e_ly E) 1 pos) + 12) ->
     aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
  (forall b n i, In (b, n) (ablocks B (e_ly E) (e_S E)) -> 0 <= i < req_size n ->
     aview rsegs (w_H W) mem' (b + i) = aview rsegs (w_H W) mem (b + i)) /\
  (forall a, in_img rsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
  (forall cid p a, In (cid, p) (frames (e_S E)) ->
     (in_zr a (frame_rng (e_ly E) (cid, p)) \/
      in_zr a (shadow_addr (frame_addr (e_ly E) cid p), fs_frame_bytes cid / 8)) ->
     aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a).
Proof.
intros E Sc Hpc W mem md mem' pos lo hi _ HAR Eab Hincl HinF Hnin Hlo Hhi HK.
pose proof (eh_laws B ARx SK HYP) as LAWS.
destruct (exvf_frm_low _ _ _ _ _ _ 1 pos HAR HinF) as (F0 & Fc & Fapp & F32 & _).
assert (HFB : fs_frame_bytes 1 = 128) by reflexivity.
rewrite HFB in Fc, Fapp.
set (F := frame_addr (e_ly E) 1 pos) in *.
pose proof alloc_ceiling_val as (AC & _).
pose proof (exvf_sh_rng F 128 ltac:(lia) ltac:(lia) Fc) as (SF1 & SF2).
replace (128 / 8) with 16 in SF2 by reflexivity.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp.
split.
(* (i) the high bytes: the frame and its shadow lie below the ceiling *)
{ intros a Ha Hn. apply HK; [lia | exact Hn | lia | unfold SHADOW_OFF in *; lia]. }
split.
(* (ii) the bytes of an entry block: apart from the frame, and in the application range, so off every shadow byte *)
{ intros b n i Hb Hi. rewrite <- Eab in Hb.
  destruct (exvf_blk_low _ _ _ _ _ _ b n HAR Hb) as (B0 & Bc & Bapp).
  pose proof (sep_block_frame_x rsegs B ARx LAWS (e_ly E) Sc Hpc W mem md b n 1 pos HAR Hb HinF) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. rewrite HFB in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp.
  apply HK; [lia | lia | lia | unfold SHADOW_OFF in *; lia]. }
split.
(* (iii) an image byte: not a frame byte (frm_img_x), and below SHADOW_OFF *)
{ intros a Hi _ _. pose proof (B_prog_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  apply HK; [lia | lia | | unfold SHADOW_OFF in *; lia].
  intros Hr. apply (frm_img_x rsegs B ARx LAWS (e_ly E) Sc Hpc W mem md 1 pos a HAR HinF); [|exact Hi].
  fold F. rewrite HFB. lia. }
(* (iv) the bytes and the shadow bytes of another live frame of the entry *)
intros cid p a Hf Hz.
assert (Hne : (1, pos) <> (cid, p)) by (intros Heq; rewrite Heq in Hnin; exact (Hnin Hf)).
pose proof (Hincl _ Hf) as HfS.
destruct (exvf_frm_low _ _ _ _ _ _ cid p HAR HfS) as (G0 & Gc & Gapp & G32 & G8).
pose proof (fs_frame_bytes_nonneg cid) as Gs0.
assert (Hd : zdisjoint (frame_rng (e_ly E) (1, pos)) (frame_rng (e_ly E) (cid, p))).
{ destruct (in_split_2 (1, pos) (cid, p) (frames Sc) HinF HfS Hne) as (l1 & l2 & l3 & [Esp | Esp]).
  - exact (sep_frames_pos_x rsegs B ARx LAWS (e_ly E) Sc Hpc W mem md _ _ l1 l2 l3 HAR Esp).
  - pose proof (sep_frames_pos_x rsegs B ARx LAWS (e_ly E) Sc Hpc W mem md _ _ l1 l2 l3 HAR Esp) as H.
    unfold zdisjoint in *. lia. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. fold F in Hd. rewrite HFB in Hd.
unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
set (G := frame_addr (e_ly E) cid p) in *.
pose proof (exvf_sh_rng G (fs_frame_bytes cid) ltac:(lia) Gs0 Gc) as (SG1 & SG2).
pose proof (exvf_sh_apart F G (fs_frame_bytes cid) F32 G32 G8 Hd) as Hsh.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Gapp.
unfold SHADOW_OFF in *.
destruct Hz as [Hz | Hz]; apply HK; lia.
Qed.
End F.
