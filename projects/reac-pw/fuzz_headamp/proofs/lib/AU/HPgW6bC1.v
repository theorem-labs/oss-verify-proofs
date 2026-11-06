(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at 25d4b718638 and the definitions
   w7_kept, w7_hull, w7_strok, w7_strz of proofs/reac-pw/fuzz_role/lib/A/RPgW7bKit.v at 25d4b718638, for
   reac-pw/fuzz_headamp's image B: w7_ -> hw7b_, role's image A code and record -> fuzz_headamp.asan-ubsan's (its own
   code table, pcs, registers and real-frame cells, measured on image B), module paths; the statements of the walk's
   blocks and call steps are new (hw7b_*_stmt), one per block of image B's own code; its hw7b_post,
   hw7b_post_of_run, hw7b_kept, hw7b_hull, hw7b_ra_kept, hw7b_hull_kept, hw7b_strok, hw7b_strz, hw7b_strok_kept and
   hw7b_strok_first_byte are lib/AU/HPgCaseB.v's cb_* since the dedup. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW7bBase.v, with its numbers changed; 102 of its 142 lines of code are new or changed and 274 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bIter.v at f3898085bda; for reac-pw/fuzz_headamp image A: module paths and the rm_ prefix renamed, every pc moved by the code's uniform shift +0xd20, the strlen trampoline 0x41b98 and __asan_memcpy 0x51d0c (W7_STRLEN / W7_MEMCPY of lib/A/HPgW7bBase.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW7bIter.v; 467 of its 535 lines of code are new or changed and 74 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC1.v at f3898085bda (the vocab strings,
   the model of a case-1 turn, e62's bytes at the join, the bounds of the shadow hulls, c1_calls and the block
   lemma w6b_c1) for reac-pw/fuzz_headamp's image B: image B's vocab table and pcs, e62 at F+0x210 with its body
   at F+0x218, the strlen wrapper at STRLEN_ENTRY_B and __asan_memcpy at 0x51d8c through HPgCaseB.cb_memcpy_at,
   the string facts taken from HPgBase.hd_cstr (which carries the tail of the NUL's word, so role's
   c1_vtail / c1_vtail_chk are dropped), and the post HPgSteps.hdu_blk_postE / HPgCaseBJ.cj_J_R. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the block lemma
   HPgW6bBase.hw6b_c1, case 1 of ent_build's `switch (kind % 10)` (pod.h:285-296, ent_text pod.h:209-219) inside
   LLVMFuzzerTestOneInput (0x80c40), from the case entry 0x81e04 to the join J 0x82618. Proves function
   LLVMFuzzerTestOneInput in part (kind: segment lemma, the piece W6b's case 1 of lib/AU/HPgSeg.v); the callees are
   the Section hypotheses MCPY (__asan_memcpy 0x51d8c) and STRL (the strlen wrapper 0x41c18).

   THE WALK, five steps chained by SRr_bind (the registers of image B: s1 = x9 = R, s11 = x27 = SHADOW_OFF,
   s2 = x18 the cursor, t1 = x6 what is left, s7 = x23, s10 = x26, s5 = x21):
     hb1_head  (HPgW6bC1a.v) 0x81e04 .. 0x82114: i = fuzz_u8 % 9, a0 = &vocab[i], t1 = |r'|, s7 = &e62.body,
               [R+0x58] = the kind byte, [R+0x110] = the cursor.
     hb1_vcell (HPgW6bC1a.v) 0x82114 .. 0x41c18: the instrumented check of the 8-byte cell, s10 = a0 = vocab[i],
               s5 = t1.
     strlen    the wrapper's contract (HPgW6bC1k.hb1_strlen_at, Hypothesis STRL) on the image string vocab[i]: its
               bytes, its NUL and the bytes after the NUL to the end of its 8-byte word are read-only image bytes
               (HPgBase.hd_cstr); a0 = len.
     hb1_set   (HPgW6bC1a.v) 0x82138 .. 0x51d8c: s2 = s4 = len (the 0x5f clamp never cuts: the nine lengths are
               12 .. 18); then __asan_memcpy (HPgCaseB.cb_memcpy_at, Hypothesis MCPY) copies the len bytes of
               vocab[i] to e62.body. Both ranges are addressable: the string by hw6b_vocab_ok, e62.body by e62's
               104 addressable bytes (hw6b_in); they do not overlap (the string lies in the image, the frame for
               locals does not).
     hb1_tail  (HPgW6bC1b.v) 0x8215c .. J: the NUL, e62.type, e62.size and, with the kind's bit 7, 'x' and a NUL.
   THE POST AT J. e62 at F + 0x210 holds Layout.ent_mem of the model's ent (hb1_model: ent_build on kind 1): the
   type and size words from hb1_tail, the string from the memcpy, the three bytes after it from hb1_tail, every
   later byte 0 as at the entry. Each byte is checked against the model's list for the nine strings and both
   values of bit 7 by computation (hb1_ent_chk). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgSeg HPgCaseB HPgCaseBJ.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgW6bBase HPgW6bC1k HPgW6bC1a HPgW6bC1b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the vocab strings ======================================== *)
Definition hb1_vlen (i : Z) : Z := Z.of_nat (length (nth (Z.to_nat i) vocab [])).
Lemma hb1_cases9 : forall i, 0 <= i < 9 ->
  i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8.
Proof. intros i Hi. lia. Qed.
Lemma hb1_vlen_in : forall i, 0 <= i < 9 -> In (hb1_vlen i) hb1_lens.
Proof.
intros i Hi. destruct (hb1_cases9 i Hi) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]];
  vm_compute; repeat (first [left; reflexivity | right]).
Qed.
Lemma hb1_vptr_img : forall i, 0 <= i < 9 -> 0x10000 <= hb_vptr i <= 0x21020.
Proof.
intros i Hi. destruct (hb1_cases9 i Hi) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]];
  split; vm_compute; discriminate.
Qed.
Lemma hb1_vlen_bnd : forall i, 0 <= i < 9 -> 12 <= hb1_vlen i <= 18.
Proof.
intros i Hi. destruct (hb1_cases9 i Hi) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute; split; discriminate.
Qed.

(* ======================================== the model of a case-1 turn ======================================== *)
Lemma hb1_testbit7 : forall kd, 0 <= kd < 256 -> Z.testbit kd 7 = negb (kd <? 128).
Proof.
intros kd Hk. apply Bool.eqb_prop.
exact (cb_all256 (fun kd => Bool.eqb (Z.testbit kd 7) (negb (kd <? 128))) ltac:(vm_compute; reflexivity) kd Hk).
Qed.
(* the ent of vocab string s; clr = bit 7 of the kind is clear *)
Definition hb1_ent (s : list byte) (clr : bool) : ent :=
  if clr then Ent POD_STRING (Z.of_nat (length s) + 1) (s ++ [Cursor.NUL])
  else Ent POD_STRING (Z.of_nat (length s) + 1 + 2) ((s ++ [Cursor.NUL]) ++ [Z_to_bv 8 120; Cursor.NUL]).
Lemma hb1_model : forall (b : byte) r, bv_unsigned b mod 10 = 1 ->
  ent_build (b :: r) = (hb1_ent (nth (Z.to_nat (fst (fuzz_u8 r) mod 9)) vocab []) (bv_unsigned b <? 128), snd (fuzz_u8 r)).
Proof.
intros b r Hk. unfold ent_build. cbn [fuzz_u8]. rewrite Hk. change (Z.to_nat 1) with 1%nat. cbv beta iota.
destruct (fuzz_u8 r) as [i r'] eqn:Er. cbv beta iota zeta. cbn [fst snd].
assert (Hs : (length (nth (Z.to_nat (i mod 9)) vocab []) <= 18)%nat) by (apply nth_len_le; vm_compute; reflexivity).
set (s := nth (Z.to_nat (i mod 9)) vocab []) in *.
assert (Ht : ent_text s true = Ent POD_STRING (Z.of_nat (length s) + 1) (s ++ [Cursor.NUL])).
{ unfold ent_text. cbv beta iota zeta. rewrite firstn_all2 by lia. rewrite length_app. cbn [length].
  f_equal. lia. }
rewrite Ht. cbn [e_size e_body].
assert (H96 : (Z.of_nat (length s) + 1 + 2 <=? 96) = true) by (apply Z.leb_le; lia).
rewrite H96, andb_true_r, (hb1_testbit7 (bv_unsigned b) (byte_range b)).
unfold hb1_ent. destruct (bv_unsigned b <? 128); reflexivity.
Qed.

(* ======================================== e62 at J ======================================== *)
(* byte j of e62 as the walk leaves it: type 8, the size word, the string s, 0, x7, 0, then 0 *)
Definition hb1_fb (s : list Z) (len sz x7 j : Z) : Z :=
  if j <? 4 then YO0f.le_byte 8 4 (Z.to_nat j)
  else if j <? 8 then YO0f.le_byte sz 4 (Z.to_nat (j - 4))
  else if j <? 8 + len then nth (Z.to_nat (j - 8)) s 0
  else if j =? 9 + len then YO0f.le_byte x7 1 0
  else 0.
(* for the nine strings and both values of bit 7, that is the model's ent_mem *)
Lemma hb1_ent_chk : forall i clr, 0 <= i < 9 ->
  length (ent_mem (hb1_ent (nth (Z.to_nat i) vocab []) clr)) = 104%nat /\
  forallb (fun j => hb1_fb (hd_zbytes (nth (Z.to_nat i) vocab [])) (hb1_vlen i)
      (hb1_vlen i + (if clr then 1 else 3)) (if clr then 0 else 0x78) (Z.of_nat j) =?
      nth j (hd_zbytes (ent_mem (hb1_ent (nth (Z.to_nat i) vocab []) clr))) 0)
    (seq 0 104) = true.
Proof.
intros i clr Hi.
destruct (hb1_cases9 i Hi) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; destruct clr; split; vm_compute; reflexivity.
Qed.
Lemma hb1_e_mem : forall (H : word -> bool) mem F (s : list byte) sz x7,
  (length s <= 18)%nat ->
  val_mem rsegs (mrestrict H mem) (F + 0x210) 4 8 ->
  val_mem rsegs (mrestrict H mem) (F + 0x214) 4 sz ->
  (forall j, (j < length s)%nat ->
   aview rsegs H mem (F + 0x218 + Z.of_nat j) = Some (bv_unsigned (nth j s (Z_to_bv 8 0)))) ->
  val_mem rsegs (mrestrict H mem) (F + 0x218 + Z.of_nat (length s)) 1 0 ->
  val_mem rsegs (mrestrict H mem) (F + 0x218 + Z.of_nat (length s) + 1) 1 x7 ->
  val_mem rsegs (mrestrict H mem) (F + 0x218 + Z.of_nat (length s) + 2) 1 0 ->
  (forall j, 11 + Z.of_nat (length s) <= j < 104 -> mbyte rsegs (mrestrict H mem) (F + 0x210 + j) = Some (Z_to_bv 8 0)) ->
  forall j, 0 <= j < 104 ->
  mbyte rsegs (mrestrict H mem) (F + 0x210 + j) = Some (Z_to_bv 8 (hb1_fb (hd_zbytes s) (Z.of_nat (length s)) sz x7 j)).
Proof.
intros H mem F s sz x7 Hl T0 T4 Hs T8 T9 T10 Hz j Hj. unfold hb1_fb.
destruct (Z.ltb_spec j 4) as [J1|J1].
{ specialize (T0 (Z.to_nat j) ltac:(lia)). rewrite Z2Nat.id in T0 by lia. exact T0. }
destruct (Z.ltb_spec j 8) as [J2|J2].
{ specialize (T4 (Z.to_nat (j - 4)) ltac:(lia)). rewrite Z2Nat.id in T4 by lia.
  replace (F + 0x210 + j) with (F + 0x214 + (j - 4)) by lia. exact T4. }
destruct (Z.ltb_spec j (8 + Z.of_nat (length s))) as [J3|J3].
{ pose proof (Hs (Z.to_nat (j - 8)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
  replace (F + 0x210 + j) with (F + 0x218 + (j - 8)) by lia.
  unfold aview in Hb. destruct (mbyte rsegs (mrestrict H mem) (F + 0x218 + (j - 8))) as [bb|] eqn:Eb; [|discriminate Hb].
  cbn [option_map] in Hb. injection Hb as Hb. unfold hd_zbytes. rewrite hb1_nth_map, <- Hb, Z_to_bv_bv_unsigned.
  reflexivity. }
destruct (Z.eqb_spec j (9 + Z.of_nat (length s))) as [J4|J4].
{ specialize (T9 0%nat ltac:(lia)).
  replace (F + 0x210 + j) with (F + 0x218 + Z.of_nat (length s) + 1 + Z.of_nat 0) by (cbn [Z.of_nat]; lia). exact T9. }
assert (J5 : j = 8 + Z.of_nat (length s) \/ j = 10 + Z.of_nat (length s) \/ 11 + Z.of_nat (length s) <= j) by lia.
destruct J5 as [J5|[J5|J5]].
- specialize (T8 0%nat ltac:(lia)).
  replace (F + 0x210 + j) with (F + 0x218 + Z.of_nat (length s) + Z.of_nat 0) by (cbn [Z.of_nat]; lia). exact T8.
- specialize (T10 0%nat ltac:(lia)).
  replace (F + 0x210 + j) with (F + 0x218 + Z.of_nat (length s) + 2 + Z.of_nat 0) by (cbn [Z.of_nat]; lia). exact T10.
- exact (Hz j ltac:(lia)).
Qed.
Lemma hb1_le_byte1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia.
reflexivity.
Qed.
Lemma hb1_e_garr8 : forall (H : word -> bool) mem F i (clr : bool), 0 <= i < 9 ->
  (forall j, 0 <= j < 104 -> mbyte rsegs (mrestrict H mem) (F + 0x210 + j) =
    Some (Z_to_bv 8 (hb1_fb (hd_zbytes (nth (Z.to_nat i) vocab [])) (hb1_vlen i)
      (hb1_vlen i + (if clr then 1 else 3)) (if clr then 0 else 0x78) j))) ->
  garr8 rsegs (mrestrict H mem) (F + 0x210) (hd_zbytes (ent_mem (hb1_ent (nth (Z.to_nat i) vocab []) clr))).
Proof.
intros H mem F i clr Hi Hm j Hj.
destruct (hb1_ent_chk i clr Hi) as [Hlen Hchk].
unfold hd_zbytes in Hj. rewrite length_map, Hlen in Hj.
pose proof (proj1 (forallb_forall _ _) Hchk j ltac:(apply in_seq; lia)) as Hq. cbv beta in Hq. apply Z.eqb_eq in Hq.
assert (Hv : 0 <= nth j (hd_zbytes (ent_mem (hb1_ent (nth (Z.to_nat i) vocab []) clr))) 0 < 256).
{ unfold hd_zbytes. rewrite hb1_nth_map. apply byte_range. }
split; [|exact Hv].
intros kk Hk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (Hm (Z.of_nat j) ltac:(lia)), Hq, (hb1_le_byte1 _ Hv). reflexivity.
Qed.

(* ======================================== bounds of shadow hulls ======================================== *)
Lemma hb1_div8 : forall X, X / 8 * 8 <= X < X / 8 * 8 + 8.
Proof.
intros X. pose proof (Z.div_mod X 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as M.
set (q := X / 8) in *. set (m := X mod 8) in *. lia.
Qed.
Lemma hb1_hull_bnd : forall x n a, cb_hull x n a -> SHADOW_OFF + x / 8 - 7 <= a < SHADOW_OFF + (x + n - 1) / 8 + 8.
Proof.
intros x n a Ha. unfold cb_hull, shadow_addr in Ha.
pose proof (hb1_div8 (SHADOW_OFF + x / 8)) as D1. pose proof (hb1_div8 (SHADOW_OFF + (x + n - 1) / 8)) as D2.
set (p := (SHADOW_OFF + x / 8) / 8) in *. set (q := (SHADOW_OFF + (x + n - 1) / 8) / 8) in *.
set (u := x / 8) in *. set (v := (x + n - 1) / 8) in *. lia.
Qed.
(* the hull of a range below 2^47 lies below the high shadow's end *)
Lemma hb1_hull_low : forall x n a, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 -> cb_hull x n a -> 0 <= a < 0x10007fff8008.
Proof.
intros x n a H0 Hn Hxn Ha. pose proof (hb1_hull_bnd x n a Ha) as H1.
pose proof (hb1_div8 x) as D1. pose proof (hb1_div8 (x + n - 1)) as D2.
set (u := x / 8) in *. set (v := (x + n - 1) / 8) in *. unfold SHADOW_OFF in *. lia.
Qed.
(* the hull of a range of the image lies in the low shadow, well above the image *)
Lemma hb1_hull_rom : forall x n a, 0x10000 <= x -> 0 < n -> x + n <= 0x9e000 -> cb_hull x n a ->
  SHADOW_OFF <= a < 0x80010000.
Proof.
intros x n a H0 Hn Hxn Ha. pose proof (hb1_hull_bnd x n a Ha) as H1.
assert (Hu : 8192 <= x / 8)
  by (apply (Z.le_trans _ (0x10000 / 8)); [vm_compute; discriminate | apply Z.div_le_mono; lia]).
assert (Hv : (x + n - 1) / 8 <= 80895)
  by (apply (Z.le_trans _ (0x9dfff / 8)); [apply Z.div_le_mono; lia | vm_compute; discriminate]).
set (u := x / 8) in *. set (v := (x + n - 1) / 8) in *. unfold SHADOW_OFF in *. lia.
Qed.
(* the hull of a part of the frame for locals lies outside the frame (the frame is outside the shadow band) *)
Section hf. Context {rc : YM05.RunCeil}.
Lemma hb1_hull_frame : forall F lo n a, in_app F 1024 -> 0 <= lo -> 0 < n -> lo + n <= 1024 -> cb_hull (F + lo) n a ->
  a < F \/ F + 1024 <= a.
Proof.
intros F lo n a Happ Hlo Hn Hln Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (hb1_hull_bnd (F + lo) n a Ha) as H1.
pose proof (hb1_div8 (F + lo)) as D1. pose proof (hb1_div8 (F + lo + n - 1)) as D2.
set (u := (F + lo) / 8) in *. set (v := (F + lo + n - 1) / 8) in *. unfold SHADOW_OFF in *. lia.
Qed.
End hf.
(* the bytes and the hull a string fact reads: image bytes, or the low shadow *)
Lemma hb1_strz_split : forall x (s : list byte) a, 0x10000 <= x <= 0x21020 -> (length s <= 18)%nat ->
  cb_strz x s a -> (0x10000 <= a < 0x30000) \/ (SHADOW_OFF <= a < 0x80010000).
Proof.
intros x s a Hx Hs [Ha|Ha]; [left; lia|].
right. exact (hb1_hull_rom x (Z.of_nat (length s) + 1) a ltac:(lia) ltac:(lia) ltac:(lia) Ha).
Qed.
(* the two ranges of the image case 1 reads: the strings and the vocab table *)
Lemma hb1_seg_str : cj_in_seg_b 0x10000 0x30000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hb1_seg_tab : cj_in_seg_b 0x9c000 0x9e000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hb1_cs : forall z, existsb (Z.eqb z) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true -> acallee_saved z.
Proof.
intros z H. unfold acallee_saved. apply existsb_exists in H as (w & Hw & Hq). apply Z.eqb_eq in Hq. subst w.
cbn [In] in Hw. lia.
Qed.
Lemma hb1_ne : forall z w, (z =? w) = false -> z <> w.
Proof. intros z w H. apply Z.eqb_neq. exact H. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MCPY : aintrin_realizes rsegs B OCpy HB_MEMCPY.
Hypothesis STRL : astrlen_realizes rsegs B STRLEN_ENTRY_B.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

(* ======================================== strlen, hb1_set, __asan_memcpy ======================================== *)
Lemma hb1_calls : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) R F x (s : list byte)
  (Q : world rsegs -> config -> Prop),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  getr regs 1 = w64 HB1_SLR -> getr regs 10 = w64 x -> getr regs 26 = w64 x -> getr regs 23 = w64 (F + 0x218) ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  R mod 16 = 0 -> sp0 mod 16 = 0 -> R <= sp0 -> 2 * ESTACK - (R - sp0) <= STK ->
  0x7fff7f800000 <= R -> R + 0x220 <= 2 ^ 47 ->
  cb_strok W mem R x s -> aro_unowned rsegs B (aview rsegs (w_H W) mem) -> (12 <= length s <= 18)%nat ->
  0 <= F -> F + 0x218 + 18 < R - 2 * ESTACK ->
  (forall a, F + 0x218 <= a < F + 0x218 + Z.of_nat (length s) ->
   awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  amem_range (F + 0x218) (Z.of_nat (length s)) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF (F + 0x218) (Z.of_nat (length s)) ->
  shadow_hull_vis (aview rsegs (w_H W) mem) (F + 0x218) (Z.of_nat (length s)) ->
  (forall a, cb_hull (F + 0x218) (Z.of_nat (length s)) a -> 0 <= a < R - 2 * ESTACK) ->
  (forall a, cb_strz x s a -> 0 <= a < R - 2 * ESTACK) ->
  (F + 0x218 + Z.of_nat (length s) <= x \/ x + Z.of_nat (length s) <= F + 0x218) ->
  (forall regs2 mem2 md2,
   ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io md md2 ->
   (forall r, acallee_saved r -> r <> 18 -> r <> 20 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
   getr regs2 18 = w64 (Z.of_nat (length s)) -> getr regs2 20 = w64 (Z.of_nat (length s)) ->
   (forall j, (j < length s)%nat ->
    aview rsegs (w_H W) mem2 (F + 0x218 + Z.of_nat j) = Some (bv_unsigned (nth j s (Z_to_bv 8 0)))) ->
   cb_kept W mem mem2 (fun a => R - 2 * ESTACK <= a < R \/ F + 0x218 <= a < F + 0x218 + Z.of_nat (length s)) ->
   SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 HB1_MCR) mem2 (seg_rom rsegs)) md2) Q) ->
  SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 STRLEN_ENTRY_B) mem (seg_rom rsegs)) md) Q.
Proof using MCPY STRL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs R F x s Q
  HJ H1 H10 H26 H23 H2 H9 H3 H4 HR16 Hs16 HRs HSTK HR1 HR2 HSO HARO Hls HF0 HFR Hwr Hamd Hrad Hhud Hhd Hzs Hdis K.
pose proof HSO as (Hx0 & Hk32 & Hx63 & Hbytes & Hnul & Htail & Hstk & Hamx & Hrax & Hhux).
assert (HE : ESTACK = 4096) by reflexivity. rewrite HE in *.
assert (Hsp : spZ regs = sp0 + (R - sp0)) by (unfold spZ; rewrite H2; unfold w64; rewrite unsigned_lit_small; lia).
(* ---- strlen(vocab[i]) ---- *)
eapply SRr_bind.
{ apply (hb1_strlen_at B STRL W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k x
    (Z.of_nat (length s)) (R - sp0) (w64 HB1_SLR) HJ); try assumption; try lia.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - apply ret_ok_even; vm_compute; reflexivity.
  - exact (cb_strok_first_byte W mem R x s HSO).
  - intros a Ha. split.
    + destruct (Z.eq_dec a (x + Z.of_nat (length s))) as [->|Hne]; [rewrite Hnul; discriminate|].
      destruct (Hbytes (Z.to_nat (a - x)) ltac:(lia)) as [Hb _]. rewrite Z2Nat.id in Hb by lia.
      replace (x + (a - x)) with a in Hb by lia. rewrite Hb. discriminate.
    + rewrite Hsp. intros Hc. apply (Hstk a ltac:(lia)). lia.
  - intros a Ha. replace (sp0 + (R - sp0)) with R by lia. exact (Hstk a Ha). }
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & Hio1 & HP1 & H10a & HK1 & Hpr1).
replace (sp0 + (R - sp0)) with R in HK1 by lia.
assert (E : forall r, acallee_saved r -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HP1.
(* ---- 0x82138 .. 0x51d8c ---- *)
eapply SRr_bind.
{ apply (hb1_set B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 (Z.of_nat (length s)) HJ1).
  - exact H10a.
  - lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hr2 & HK2 & Hpr2 & (R1 & R10 & R11 & R12 & R18 & R20)).
assert (EB : forall r, acallee_saved r -> r <> 18 -> r <> 20 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr Hr18 Hr20. rewrite Hr2; [exact (E r Hr) | rewrite cb_cs_bv by exact Hr; unfold acallee_saved in Hr; lia |].
  apply cb_cs_out; [exact Hr|]. unfold acallee_saved in Hr. vm_compute. lia. }
assert (KB : cb_kept W mem mem2 (fun a => R - 2 * 4096 <= a < R)).
{ intros a Ha Hz. cbv beta in Hz. rewrite (HK2 a Ha (fun f => f)). exact (HK1 a Ha Hz). }
assert (Hsp2 : spZ regs2 = sp0 + (R - sp0)).
{ unfold spZ. rewrite (cb_reg_eq regs regs2 2%bv (EB 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia))).
  exact Hsp. }
assert (R10' : getr regs2 10 = w64 (F + 0x218)).
{ rewrite R10, <- H23. exact (E 23 ltac:(unfold acallee_saved; lia)). }
assert (R11' : getr regs2 11 = w64 x).
{ rewrite R11, <- H26. exact (E 26 ltac:(unfold acallee_saved; lia)). }
(* ---- memcpy(e62.body, vocab[i], len) ---- *)
eapply SRr_bind.
{ apply (cb_memcpy_at B HB_MEMCPY MCPY W regs2 mem2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc md2 k (F + 0x218) x
    (Z.of_nat (length s)) (R - sp0) (w64 HB1_MCR) HJ2 R10' R11' R12).
  - lia.
  - lia.
  - lia.
  - exact Hsp2.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - lia.
  - rewrite (cb_reg_eq regs regs2 3%bv (EB 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia))). exact H3.
  - rewrite (cb_reg_eq regs regs2 4%bv (EB 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia))). exact H4.
  - exact R1.
  - apply ret_ok_even; vm_compute; reflexivity.
  - intros a Ha. split; [exact (Hwr a Ha) | lia].
  - exact Hamd.
  - apply (cb_ra_kept W mem mem2); [exact Hrad | lia |]. intros a Ha. apply KB; cbv beta; pose proof (Hhd a Ha); lia.
  - intros Hl. apply (cb_hull_kept W mem mem2); [exact Hhud |]. intros a Ha. apply KB; cbv beta; pose proof (Hhd a Ha); lia.
  - lia.
  - lia.
  - intros a Ha. split.
    + rewrite (KB a ltac:(pose proof (Hzs a ltac:(left; lia)); lia) ltac:(cbv beta; pose proof (Hzs a ltac:(left; lia)); lia)).
      destruct (Hbytes (Z.to_nat (a - x)) ltac:(lia)) as [Hb _]. rewrite Z2Nat.id in Hb by lia.
      replace (x + (a - x)) with a in Hb by lia. rewrite Hb. discriminate.
    + rewrite Hsp2. pose proof (Hzs a ltac:(left; lia)). lia.
  - exact Hdis.
  - unfold amem_range in *. lia.
  - apply (range_addressable_sub _ _ x (Z.of_nat (length s) + 1)); [|lia|lia].
    apply (cb_ra_kept W mem mem2); [exact Hrax | lia |]. intros a Ha. apply KB; cbv beta; pose proof (Hzs a (or_intror Ha)); lia.
  - intros Hl. apply (hm_hull_sub _ x (Z.of_nat (length s) + 1)); [| lia | lia | lia].
    apply (cb_hull_kept W mem mem2); [exact Hhux |]. intros a Ha. apply KB; cbv beta; pose proof (Hzs a (or_intror Ha)); lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & HP3 & R10'' & HD3 & HK3 & Hpr3).
apply K.
- exact HJ3.
- eapply same_io_trans; [eapply same_io_trans; [exact Hio1 | exact Hio2] | exact Hio3].
- intros r Hr Hr18 Hr20. rewrite (HP3 r Hr). exact (EB r Hr Hr18 Hr20).
- rewrite (cb_reg_eq regs2 regs3 18%bv (HP3 18 ltac:(unfold acallee_saved; lia))). exact R18.
- rewrite (cb_reg_eq regs2 regs3 20%bv (HP3 20 ltac:(unfold acallee_saved; lia))). exact R20.
- intros j Hj. rewrite (HD3 (Z.of_nat j) ltac:(lia)).
  rewrite (KB (x + Z.of_nat j) ltac:(pose proof (Hzs (x + Z.of_nat j) ltac:(left; lia)); lia)
    ltac:(cbv beta; pose proof (Hzs (x + Z.of_nat j) ltac:(left; lia)); lia)).
  exact (proj1 (Hbytes j Hj)).
- intros a Ha Hz. cbv beta in Hz. rewrite (HK3 a Ha ltac:(lia) ltac:(lia)). apply KB; [exact Ha | cbv beta; lia].
Qed.

(* ======================================== the block lemma ======================================== *)
Theorem hw6b_c1 : hw6b_c1_stmt B MT.
Proof using MTL MCPY STRL.
unfold hw6b_c1_stmt, hw6b_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b r Hctx Hk1 Hin Hvoc.
pose proof Hctx as (HJ & HR32 & HRsp & HspR & Hown & HFa & Hrom).
pose proof Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & H13 & V40 & Ve8 & V118 & V130 & V138 & V148 &
  Hkd & Hpp1 & Hpp2 & HF1 & HF2 & HF32 & HRc & HFp & Ez & Hrae & Hhe & Hc1 & Hinp & Hhin & HdisF).
destruct Hinp as (Hg & Hrain & Hc0 & Hcr & Ham & Hdis).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
destruct Hvoc as (Hrav & Hvoc).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@asan_consts rc) as (Hac & _).
assert (HT : T_SEG_STK = 16384) by reflexivity. rewrite HT in HspR, HRc, Hdis.
pose proof (hb1_mod16 R HR32) as HR16.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & Happ).
rewrite <- HFa in Happ. change (fs_frame_bytes 4) with 1024 in Happ.
unfold Layout.PP_SIZE in Hpp2.
set (kd := bv_unsigned b) in *.
specialize (H13 ltac:(rewrite Hk1; discriminate)).
pose proof (byte_range b) as Hb256.
(* the index, the string and its facts at the entry *)
set (r1 := snd (fuzz_u8 r)).
assert (Hr1 : (length r1 <= length r)%nat) by (unfold r1; destruct r; cbn; lia).
set (i := fst (fuzz_u8 r) mod 9).
assert (Hi : 0 <= i < 9) by (unfold i; apply Z.mod_pos_bound; lia).
set (x := hb_vptr i).
set (s := nth (Z.to_nat i) vocab []).
pose proof (hb1_vlen_in i Hi) as Hlen. change (hb1_vlen i) with (Z.of_nat (length s)) in Hlen.
pose proof (hb1_vlen_bnd i Hi) as Hlb. change (hb1_vlen i) with (Z.of_nat (length s)) in Hlb.
assert (Hls : (12 <= length s <= 18)%nat) by lia.
pose proof (hb1_vptr_range i) as Hx.
destruct (Hvoc i Hi) as (Vcell & Hcs). change (hb_vptr i) with x in Vcell, Hcs.
change (nth (Z.to_nat i) vocab []) with s in Hcs.
pose proof (hb1_vptr_img i Hi) as Hximg. change (hb_vptr i) with x in Hximg.
(* the geometry: the image's hulls and the frame's hulls lie below the callees' stack and outside the frame *)
assert (Hnf : forall a, in_img rsegs a -> ~ (F <= a < F + 1024)).
{ intros a Hai Hc. apply (frm_img rsegs B LAWS lyc Sc W memc mdc 4 pos a HAR Hin4); [rewrite <- HFa; change (fs_frame_bytes 4) with 1024; lia | exact Hai]. }
assert (HSAFE : forall a, (0x10000 <= a < 0x30000 \/ 0x9c000 <= a < 0x9e000 \/ SHADOW_OFF <= a < 0x80010000) ->
  0 <= a < 2 ^ 64 /\ ~ hb1_head_wr R F a /\ ~ (R - 8192 <= a < R) /\
  ~ (F + 0x218 <= a < F + 0x218 + Z.of_nat (length s)) /\ ~ hb1_tail_wr F (Z.of_nat (length s)) a).
{ intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  assert (Hout : ~ (F <= a < F + 1024)).
  { destruct Ha as [Ha|[Ha|Ha]].
    - apply Hnf. exact (cj_in_seg 0x10000 0x30000 a hb1_seg_str Ha).
    - apply Hnf. exact (cj_in_seg 0x9c000 0x9e000 a hb1_seg_tab Ha).
    - unfold SHADOW_OFF in Ha. lia. }
  unfold SHADOW_OFF in Ha. unfold hb1_head_wr, hb1_tail_wr. repeat split; lia. }
assert (Hhf : forall a, cb_hull (F + 0x210) 104 a -> 0 <= a < 2 ^ 64 /\ ~ hb1_head_wr R F a /\ ~ (R - 8192 <= a < R) /\
  ~ (F + 0x218 <= a < F + 0x218 + Z.of_nat (length s)) /\ ~ hb1_tail_wr F (Z.of_nat (length s)) a).
{ intros a Ha.
  pose proof (hb1_hull_low (F + 0x210) 104 a ltac:(lia) ltac:(lia) ltac:(lia) Ha) as Hb1.
  pose proof (hb1_hull_frame F 0x210 104 a Happ ltac:(lia) ltac:(lia) ltac:(lia) Ha) as Hb2.
  unfold hb1_head_wr, hb1_tail_wr. repeat split; lia. }
(* the string facts at the case entry *)
assert (SO0 : cb_strok W memc R x s).
{ apply (hb1_strok_cstr W memc R x s Hcs); [unfold ESTACK; lia | lia]. }
(* ---- hb1_head ---- *)
eapply SRr_bind; [exact (hb1_head B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp kd r
  Hctx Hk1 Hin)|].
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & Hio1 & Hr1h & HK1 & Hpr1 & (P10 & P6 & P23 & P58 & P110 & Pez)).
change (fst (fuzz_u8 r) mod 9) with i in P10. change (snd (fuzz_u8 r)) with r1 in P6.
(* ---- hb1_vcell ---- *)
eapply SRr_bind.
{ apply (hb1_vcell B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 i HJ1 P10 Hi).
  - rewrite Hr1h; [exact H27 | apply cb_nz; reflexivity | apply cb_notin; reflexivity].
  - apply (cb_ra_kept W memc mem1); [exact Hrav | unfold HB_VOCAB; lia |].
    intros a Ha. pose proof (hb1_hull_rom HB_VOCAB 72 a ltac:(unfold HB_VOCAB; lia) ltac:(lia)
      ltac:(unfold HB_VOCAB; lia) Ha) as Hbb.
    destruct (HSAFE a ltac:(right; right; exact Hbb)) as (A1 & A2 & _). exact (HK1 a A1 A2).
  - apply (cb_val_kept (w_H W) memc mem1 _ _ _ ); [|exact Vcell].
    intros j Hj. destruct (HSAFE (HB_VOCAB + 8 * i + j) ltac:(right; left; unfold HB_VOCAB; lia)) as (A1 & A2 & _).
    exact (HK1 _ A1 A2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hr2 & HK2 & Hpr2 & (Q1 & Q10 & Q26 & Q21)).
assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ hb1_head_wr R F a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. rewrite (HK2 a Ha (fun f => f)). exact (HK1 a Ha Hn). }
assert (Kr : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr ([6; 10; 11; 12; 16; 17; 20; 23] ++ [1; 10; 11; 21; 26])%bv ->
  getr regs2 rr = getr regs rr).
{ intros rr Hr0 Hn. rewrite Hr2; [| exact Hr0 | intros X; apply Hn; apply in_or_app; right; exact X].
  apply Hr1h; [exact Hr0 | intros X; apply Hn; apply in_or_app; left; exact X]. }
(* ---- strlen, hb1_set, memcpy ---- *)
apply (hb1_calls STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k regs2 R F x s _ HJ2 Q1 Q10 Q26).
- rewrite Hr2; [exact P23 | apply cb_nz; reflexivity | apply cb_notin; reflexivity].
- rewrite Kr; [exact H2 | apply cb_nz; reflexivity | apply cb_notin; reflexivity].
- rewrite Kr; [exact H9 | apply cb_nz; reflexivity | apply cb_notin; reflexivity].
- rewrite Kr; [exact H3 | apply cb_nz; reflexivity | apply cb_notin; reflexivity].
- rewrite Kr; [exact H4 | apply cb_nz; reflexivity | apply cb_notin; reflexivity].
- exact HR16.
- exact Hsp0al.
- lia.
- unfold ESTACK. lia.
- lia.
- lia.
- apply (cb_strok_kept W memc mem2 R x s SO0). intros a Ha.
  pose proof (hb1_strz_split x s a ltac:(lia) ltac:(lia) Ha) as Hbb.
  destruct (HSAFE a ltac:(destruct Hbb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb])) as (A1 & A2 & _).
  exact (K12 a A1 A2).
- intros a Har Ho He.
  assert (Hai : in_img rsegs a) by (destruct Har as (sg & Hsg & _ & Hb); exists sg; auto).
  pose proof (hb_segs_low a Hai) as Hlo. unfold kLowMemEnd in Hlo.
  pose proof (Hnf a Hai) as Hnfa.
  rewrite (K12 a ltac:(lia) ltac:(unfold hb1_head_wr; lia)). exact (Hrom a Har).
- exact Hls.
- lia.
- unfold ESTACK. lia.
- intros a Ha. right. right. right. exists 4, pos. split; [exact Hown|]. left.
  unfold in_zr. cbn [fst snd]. rewrite <- HFa. change (fs_frame_bytes 4) with 1024. lia.
- unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
- apply (range_addressable_sub _ _ (F + 0x210) 104); [| lia | lia].
  apply (cb_ra_kept W memc mem2); [exact Hrae | lia |]. intros a Ha.
  destruct (Hhf a Ha) as (A1 & A2 & _). exact (K12 a A1 A2).
- apply (hm_hull_sub _ (F + 0x210) 104); [| lia | lia | lia].
  apply (cb_hull_kept W memc mem2); [exact Hhe |]. intros a Ha.
  destruct (Hhf a Ha) as (A1 & A2 & _). exact (K12 a A1 A2).
- intros a Ha. pose proof (hb1_hull_low (F + 0x218) (Z.of_nat (length s)) a ltac:(lia) ltac:(lia) ltac:(lia) Ha).
  unfold ESTACK. lia.
- intros a Ha. pose proof (hb1_strz_split x s a ltac:(lia) ltac:(lia) Ha) as Hbb.
  unfold SHADOW_OFF in Hbb. unfold ESTACK. lia.
- destruct (Z_le_gt_dec (F + 0x218 + Z.of_nat (length s)) x) as [Hd|Hd]; [left; exact Hd|].
  destruct (Z_le_gt_dec (x + Z.of_nat (length s)) (F + 0x218)) as [Hd'|Hd']; [right; exact Hd'|].
  exfalso. apply (Hnf (Z.max x (F + 0x218))); [|lia].
  pose proof Hcs as (_ & _ & _ & _ & _ & Himg & _).
  replace (Z.max x (F + 0x218)) with (x + (Z.max x (F + 0x218) - x)) by lia.
  apply Himg. unfold hd_zbytes. rewrite length_map. lia.
- (* ---- at 0x8215c: the tail ---- *)
  intros regs3 mem3 md3 HJ3 Hio3 HP3 S18 S20 HD3 HK3.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ hb1_head_wr R F a -> ~ (R - 8192 <= a < R) ->
    ~ (F + 0x218 <= a < F + 0x218 + Z.of_nat (length s)) -> aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) memc a).
  { intros a Ha N1 N2 N3. rewrite (HK3 a Ha ltac:(cbv beta; unfold ESTACK; lia)). exact (K12 a Ha N1). }
  assert (K13 : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 8192 <= a < R) ->
    ~ (F + 0x218 <= a < F + 0x218 + Z.of_nat (length s)) -> aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) mem1 a).
  { intros a Ha N2 N3. rewrite (HK3 a Ha ltac:(cbv beta; unfold ESTACK; lia)). exact (HK2 a Ha (fun f => f)). }
  assert (Kr3 : forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 18 -> bv_unsigned q <> 20 ->
    bv_unsigned q <> 0 -> ~ In q ([6; 10; 11; 12; 16; 17; 20; 23] ++ [1; 10; 11; 21; 26])%bv ->
    getr regs3 q = getr regs q).
  { intros q Hq1 Hq2 Hq3 Hq0 Hq5. rewrite (cb_reg_eq regs2 regs3 q (HP3 _ Hq1 Hq2 Hq3)). exact (Kr q Hq0 Hq5). }
  eapply SRr_mono.
  { apply (hb1_tail B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem3 md3 k regs3 R F pos (Z.of_nat (length s)) kd
      (c + Z.of_nat (length r) - Z.of_nat (length r1)) pp HJ3 HR32 HRsp ltac:(rewrite HT; lia) Hown HFa Hlen
      ltac:(lia)).
    - rewrite Kr3; [exact H9 | apply hb1_cs; reflexivity | apply hb1_ne; reflexivity | apply hb1_ne; reflexivity
        | apply cb_nz; reflexivity | apply cb_notin; reflexivity].
    - rewrite Kr3; [exact H27 | apply hb1_cs; reflexivity | apply hb1_ne; reflexivity | apply hb1_ne; reflexivity
        | apply cb_nz; reflexivity | apply cb_notin; reflexivity].
    - exact S18.
    - exact S20.
    - rewrite (cb_reg_eq regs2 regs3 23%bv (HP3 23 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia))).
      rewrite Hr2; [exact P23 | apply cb_nz; reflexivity | apply cb_notin; reflexivity].
    - lia.
    - lia.
    - lia.
    - apply (cb_val_kept (w_H W) mem1 mem3 _ _ _); [|exact P58].
      intros j Hj. rewrite (HK3 (R + 0x58 + j) ltac:(lia) ltac:(cbv beta; unfold ESTACK; lia)).
      exact (HK2 (R + 0x58 + j) ltac:(lia) (fun f => f)).
    - apply (cb_val_kept (w_H W) memc mem3 _ _ _); [|exact Ve8].
      intros j Hj. apply K3; unfold hb1_head_wr; lia.
    - apply (cb_val_kept (w_H W) mem1 mem3 _ _ _); [|exact P110].
      intros j Hj. rewrite (HK3 (R + 0x110 + j) ltac:(lia) ltac:(cbv beta; unfold ESTACK; lia)).
      exact (HK2 (R + 0x110 + j) ltac:(lia) (fun f => f)).
    - apply (cb_val_kept (w_H W) memc mem3 _ _ _); [|exact V118].
      intros j Hj. apply K3; unfold hb1_head_wr; lia.
    - apply (cb_val_kept (w_H W) memc mem3 _ _ _); [|exact V130].
      intros j Hj. apply K3; unfold hb1_head_wr; lia.
    - apply (cb_val_kept (w_H W) memc mem3 _ _ _); [|exact V138].
      intros j Hj. apply K3; unfold hb1_head_wr; lia.
    - apply (cb_val_kept (w_H W) memc mem3 _ _ _); [|exact V148].
      intros j Hj. apply K3; unfold hb1_head_wr; lia.
    - intros j Hj.
      rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) mem1 mem3 (F + 0x218 + Z.of_nat (length s) + j)
        (K13 (F + 0x218 + Z.of_nat (length s) + j) ltac:(lia) ltac:(lia) ltac:(lia))).
      replace (F + 0x218 + Z.of_nat (length s) + j) with (F + 0x210 + (8 + Z.of_nat (length s) + j)) by lia.
      apply Pez. lia.
    - apply (cb_ra_kept W memc mem3); [exact Hrae | lia |]. intros a Ha.
      destruct (Hhf a Ha) as (A1 & A2 & A3 & A4 & _). exact (K3 a A1 A2 A3 A4). }
  (* ---- the post at J ---- *)
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hr4 & HK4 & Hpr4 &
    (T13 & T6 & T18 & T20 & T23 & T0 & T4 & T8 & T9 & T10)).
  red. exists lyc, Sc, regs4, mem4, md4.
  split; [reflexivity|].
  split; [exact HJ4|].
  split.
  { intros rr Hr0 Hn. pose proof (in_nz_regs rr Hr0) as Hrr. cbv [nz_regs In] in Hrr.
    repeat (destruct Hrr as [<-|Hrr];
      [ first
        [ exfalso; apply Hn; cbv [hw6b_clob In]; repeat (first [left; reflexivity | right]); fail
        | lazymatch goal with |- getr _ ?q = _ =>
            rewrite (Hr4 q ltac:(apply cb_nz; reflexivity) ltac:(apply cb_notin; reflexivity)) end;
          apply Kr3; [apply hb1_cs; reflexivity | apply hb1_ne; reflexivity | apply hb1_ne; reflexivity
            | apply cb_nz; reflexivity | apply cb_notin; reflexivity] ] |]).
    destruct Hrr. }
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split; [eapply same_io_trans; [eapply same_io_trans; [eapply same_io_trans; [exact Hio1 | exact Hio2] | exact Hio3]
    | exact Hio4]|].
  split; [apply mo_le_refl; exact MTL|].
  split.
  { intros a Ha Hn. unfold cj_wr, HSU_E62 in Hn. rewrite HT in Hn.
    rewrite (HK4 a Ha ltac:(unfold hb1_tail_wr; intros X; apply Hn; right; right; lia)).
    apply K3; [exact Ha | unfold hb1_head_wr; intros X; apply Hn;
      destruct X as [X|[X|X]]; [right; left; apply Exists_cons_hd; cbn; lia
      | right; left; apply Exists_cons_tl; apply Exists_cons_hd; cbn; lia | right; right; lia]
      | intros X; apply Hn; left; lia
      | intros X; apply Hn; right; right; lia]. }
  (* cj_J_R *)
  unfold cj_J_R, HSU_E62, Layout.OFF_LEN.
  rewrite (hb1_model b r Hk1). cbn [fst snd].
  change (nth (Z.to_nat (fst (fuzz_u8 r) mod 9)) vocab []) with s.
  split; [rewrite T13; f_equal; lia|].
  split.
  { rewrite T6, (cb_reg_eq regs2 regs3 21%bv (HP3 21 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia))), Q21.
    exact P6. }
  split; [exact T18|]. split; [exact T20|]. split; [exact T23|].
  change (Z.of_nat (length s)) with (hb1_vlen i) in T4.
  apply (hb1_e_garr8 (w_H W) mem4 F i (kd <? 128) Hi).
  apply (hb1_e_mem (w_H W) mem4 F s); [lia | exact T0 | | | exact T8 | exact T9 | exact T10 |].
  + unfold hb1_ty in T4. destruct (kd <? 128); exact T4.
  + intros j Hj. rewrite (HK4 (F + 0x218 + Z.of_nat j) ltac:(lia) ltac:(unfold hb1_tail_wr; lia)). exact (HD3 j Hj).
  + intros j Hj.
    rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) mem1 mem4 (F + 0x210 + j)
      (eq_trans (HK4 (F + 0x210 + j) ltac:(lia) ltac:(unfold hb1_tail_wr; lia))
        (K13 (F + 0x210 + j) ltac:(lia) ltac:(lia) ltac:(lia)))).
    apply Pez. lia.
Qed.
End d.
End b.

Print Assumptions hw6b_c1.
