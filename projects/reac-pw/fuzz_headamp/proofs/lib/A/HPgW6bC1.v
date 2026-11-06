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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW7bIter.v; 412 of its 485 lines of code are new or changed and 69 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC1.v at f3898085bda; for reac-pw/fuzz_headamp image A: module paths and the rm_ / rl_ prefixes renamed, every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0), the strlen trampoline 0x41b98 and __asan_memcpy 0x51d0c, the real-frame cells by the plan's slot map (the cursor's spill R+0xc8 -> R+0x68, in.n R+0xf8 -> R+0x118, &e.body R+0xc0 -> R+0xe0, s5's R+0x70 -> R+0x98, pp R+0x80 -> R+0xf0, vb R+0xb0 -> R+0xd0, &e R+0xf0 -> R+0x110), the frame for locals of class 4 (1024 bytes), the real frame of 0x1e0 bytes, RPgCfgChanges' lemmas -> HPgSteps'. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the block lemma w6b_c1 of
   lib/A/HPgW6bBase.v, case 1 of ent_build's `switch (kind % 10)` (pod.h:285-296, ent_text pod.h:209-219) inside
   LLVMFuzzerTestOneInput (0x80bc0), from the case entry 0x81cf8 to the join J 0x8237c. Proves no function (kind:
   segment lemma).

   THE WALK, five steps chained by SRr_bind:
     c1_head    (HPgW6bC1a.v) 0x81cf8 .. 0x81fa4: i = fuzz_u8 % 9, a0 = &vocab[i], [R+0x68] = the cursor, [R+0x118] = in.n.
     c1_vcell   (HPgW6bC1a.v) 0x81fa4 .. 0x41b98: the instrumented check of the 8-byte cell, s11 = a0 = vocab[i].
     strlen     the wrapper's contract (HPgW7bCall.v w7_strlen_at, Hypothesis STRL) on the image string vocab[i]:
                its bytes, its NUL and the bytes after the NUL to the end of its 8-byte word are read-only image
                bytes (c1_vtail_chk); a0 = len.
     c1_set     (HPgW6bC1a.v) 0x81fc4 .. 0x51d0c: s5 = s9 = len, s8 = &e.body; then __asan_memcpy (HPgW7bKit.v
                w7_memcpy_at, Hypothesis MCPY) copies the len bytes of vocab[i] to e.body. Both ranges are
                addressable: the string by w6b_vocab_ok, e.body by e's 104 addressable bytes (w6b_in); they do not
                overlap (the string lies in the image, the frame for locals does not).
     c1_tail    (HPgW6bC1b.v) 0x81fec .. J: the NUL, e.type, e.size and, with the kind's bit 7, 'x' and a NUL.
   THE POST AT J. e at F + 0xf0 holds Layout.ent_mem of the model's ent (c1_model: ent_build on kind 1): the type and
   size words from c1_tail, the string from the memcpy, the three bytes after it from c1_tail, every later byte 0 as at
   the entry. Each byte is checked against the model's list for the nine strings and both values of bit 7 by
   computation (c1_ent_chk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgSteps HPgMem HPgW6aBase HPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgEntBKit HPgW7bBase HPgW7bKit HPgW7bCall HPgW7bFacts HPgW7bIter.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW6aC2h HPgW6bC1a HPgW6bC1b.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef WrapRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Local Notation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ======================================== the vocab strings ======================================== *)
Definition c1_vlen (i : Z) : Z := Z.of_nat (length (nth (Z.to_nat i) vocab [])).
Lemma c1_cases9 : forall i, 0 <= i < 9 ->
  i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8.
Proof. intros i Hi. lia. Qed.
(* the bytes after each string's NUL to the end of the NUL's 8-byte word are read-only image bytes *)
Lemma c1_vtail_chk : forallb (fun i => forallb w7_rom_some (w7_tail_addrs (w6b_vptr (Z.of_nat i)) (c1_vlen (Z.of_nat i))))
  (seq 0 9) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c1_vtail : forall i, 0 <= i < 9 -> forall a,
  w6b_vptr i + c1_vlen i < a < w6b_vptr i + c1_vlen i - (w6b_vptr i + c1_vlen i) mod 8 + 8 ->
  forall (H : word -> bool) mem, aview rsegs H mem a <> None.
Proof.
intros i Hi a Ha H mem.
pose proof (proj1 (forallb_forall _ _) c1_vtail_chk (Z.to_nat i) ltac:(apply in_seq; lia)) as Hq. cbv beta in Hq.
rewrite Z2Nat.id in Hq by lia.
set (x := w6b_vptr i) in *. set (len := c1_vlen i) in *.
assert (Hm : 0 <= (x + len) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Ha' : In a (w7_tail_addrs x len)).
{ unfold w7_tail_addrs. apply in_map_iff. exists (Z.to_nat (a - (x + len + 1))). split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. revert Ha Hm. generalize ((x + len) mod 8). intros mm Ha Hm. lia. }
pose proof (proj1 (forallb_forall _ _) Hq a Ha') as Hr. unfold w7_rom_some in Hr.
unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)); [discriminate|].
destruct (seg_rom rsegs (Z_to_bv 64 a)); [discriminate | discriminate Hr].
Qed.
Lemma c1_vlen_in : forall i, 0 <= i < 9 -> In (c1_vlen i) c1_lens.
Proof.
intros i Hi. destruct (c1_cases9 i Hi) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]];
  vm_compute; repeat (first [left; reflexivity | right]).
Qed.

(* ======================================== the model of a case-1 turn ======================================== *)
Lemma c1_testbit7 : forall kd, 0 <= kd < 256 -> Z.testbit kd 7 = negb (kd <? 128).
Proof.
intros kd Hk. apply Bool.eqb_prop.
exact (c2_all256 (fun kd => Bool.eqb (Z.testbit kd 7) (negb (kd <? 128))) ltac:(vm_compute; reflexivity) kd Hk).
Qed.
(* the ent of vocab string s; clr = bit 7 of the kind is clear *)
Definition c1_ent (s : list byte) (clr : bool) : ent :=
  if clr then Ent POD_STRING (Z.of_nat (length s) + 1) (s ++ [Cursor.NUL])
  else Ent POD_STRING (Z.of_nat (length s) + 1 + 2) ((s ++ [Cursor.NUL]) ++ [Z_to_bv 8 120; Cursor.NUL]).
Lemma c1_model : forall (b : byte) r, bv_unsigned b mod 10 = 1 ->
  ent_build (b :: r) = (c1_ent (nth (Z.to_nat (fst (fuzz_u8 r) mod 9)) vocab []) (bv_unsigned b <? 128), snd (fuzz_u8 r)).
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
rewrite H96, andb_true_r, (c1_testbit7 (bv_unsigned b) (byte_range b)).
unfold c1_ent. destruct (bv_unsigned b <? 128); reflexivity.
Qed.

(* ======================================== e at J ======================================== *)
(* byte j of e as the walk leaves it: type 8, the size word, the string s, 0, x7, 0, then 0 *)
Definition c1_fb (s : list Z) (len sz x7 j : Z) : Z :=
  if j <? 4 then YO0f.le_byte 8 4 (Z.to_nat j)
  else if j <? 8 then YO0f.le_byte sz 4 (Z.to_nat (j - 4))
  else if j <? 8 + len then nth (Z.to_nat (j - 8)) s 0
  else if j =? 9 + len then YO0f.le_byte x7 1 0
  else 0.
(* for the nine strings and both values of bit 7, that is the model's ent_mem *)
Lemma c1_ent_chk : forall i clr, 0 <= i < 9 ->
  length (ent_mem (c1_ent (nth (Z.to_nat i) vocab []) clr)) = 104%nat /\
  forallb (fun j => c1_fb (u8s (nth (Z.to_nat i) vocab [])) (c1_vlen i) (c1_vlen i + (if clr then 1 else 3))
      (if clr then 0 else 0x78) (Z.of_nat j) =? nth j (u8s (ent_mem (c1_ent (nth (Z.to_nat i) vocab []) clr))) 0)
    (seq 0 104) = true.
Proof.
intros i clr Hi.
destruct (c1_cases9 i Hi) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; destruct clr; split; vm_compute; reflexivity.
Qed.
Lemma c1_e_mem : forall (H : word -> bool) mem F (s : list byte) sz x7,
  (length s <= 18)%nat ->
  val_mem rsegs (mrestrict H mem) (F + 0xf0) 4 8 ->
  val_mem rsegs (mrestrict H mem) (F + 0xf4) 4 sz ->
  (forall j, (j < length s)%nat ->
   aview rsegs H mem (F + 0xf8 + Z.of_nat j) = Some (bv_unsigned (nth j s (Z_to_bv 8 0)))) ->
  val_mem rsegs (mrestrict H mem) (F + 0xf8 + Z.of_nat (length s)) 1 0 ->
  val_mem rsegs (mrestrict H mem) (F + 0xf8 + Z.of_nat (length s) + 1) 1 x7 ->
  val_mem rsegs (mrestrict H mem) (F + 0xf8 + Z.of_nat (length s) + 2) 1 0 ->
  (forall j, 11 + Z.of_nat (length s) <= j < 104 -> mbyte rsegs (mrestrict H mem) (F + 0xf0 + j) = Some (Z_to_bv 8 0)) ->
  forall j, 0 <= j < 104 ->
  mbyte rsegs (mrestrict H mem) (F + 0xf0 + j) = Some (Z_to_bv 8 (c1_fb (u8s s) (Z.of_nat (length s)) sz x7 j)).
Proof.
intros H mem F s sz x7 Hl T0 T4 Hs T8 T9 T10 Hz j Hj. unfold c1_fb.
destruct (Z.ltb_spec j 4) as [J1|J1].
{ specialize (T0 (Z.to_nat j) ltac:(lia)). rewrite Z2Nat.id in T0 by lia. exact T0. }
destruct (Z.ltb_spec j 8) as [J2|J2].
{ specialize (T4 (Z.to_nat (j - 4)) ltac:(lia)). rewrite Z2Nat.id in T4 by lia.
  replace (F + 0xf0 + j) with (F + 0xf4 + (j - 4)) by lia. exact T4. }
destruct (Z.ltb_spec j (8 + Z.of_nat (length s))) as [J3|J3].
{ pose proof (Hs (Z.to_nat (j - 8)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
  replace (F + 0xf0 + j) with (F + 0xf8 + (j - 8)) by lia.
  unfold aview in Hb. destruct (mbyte rsegs (mrestrict H mem) (F + 0xf8 + (j - 8))) as [bb|] eqn:Eb; [|discriminate Hb].
  cbn [option_map] in Hb. injection Hb as Hb. rewrite hm_nth_map, <- Hb, Z_to_bv_bv_unsigned. reflexivity. }
destruct (Z.eqb_spec j (9 + Z.of_nat (length s))) as [J4|J4].
{ specialize (T9 0%nat ltac:(lia)).
  replace (F + 0xf0 + j) with (F + 0xf8 + Z.of_nat (length s) + 1 + Z.of_nat 0) by (cbn [Z.of_nat]; lia). exact T9. }
assert (J5 : j = 8 + Z.of_nat (length s) \/ j = 10 + Z.of_nat (length s) \/ 11 + Z.of_nat (length s) <= j) by lia.
destruct J5 as [J5|[J5|J5]].
- specialize (T8 0%nat ltac:(lia)).
  replace (F + 0xf0 + j) with (F + 0xf8 + Z.of_nat (length s) + Z.of_nat 0) by (cbn [Z.of_nat]; lia). exact T8.
- specialize (T10 0%nat ltac:(lia)).
  replace (F + 0xf0 + j) with (F + 0xf8 + Z.of_nat (length s) + 2 + Z.of_nat 0) by (cbn [Z.of_nat]; lia). exact T10.
- exact (Hz j ltac:(lia)).
Qed.
Lemma c1_le_byte1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia.
reflexivity.
Qed.
Lemma c1_e_garr8 : forall (H : word -> bool) mem F i (clr : bool), 0 <= i < 9 ->
  (forall j, 0 <= j < 104 -> mbyte rsegs (mrestrict H mem) (F + 0xf0 + j) =
    Some (Z_to_bv 8 (c1_fb (u8s (nth (Z.to_nat i) vocab [])) (c1_vlen i) (c1_vlen i + (if clr then 1 else 3))
      (if clr then 0 else 0x78) j))) ->
  garr8 rsegs (mrestrict H mem) (F + 0xf0) (u8s (ent_mem (c1_ent (nth (Z.to_nat i) vocab []) clr))).
Proof.
intros H mem F i clr Hi Hm j Hj.
destruct (c1_ent_chk i clr Hi) as [Hlen Hchk].
rewrite length_map, Hlen in Hj.
pose proof (proj1 (forallb_forall _ _) Hchk j ltac:(apply in_seq; lia)) as Hq. cbv beta in Hq. apply Z.eqb_eq in Hq.
assert (Hv : 0 <= nth j (u8s (ent_mem (c1_ent (nth (Z.to_nat i) vocab []) clr))) 0 < 256).
{ rewrite hm_nth_map. apply byte_range. }
split; [|exact Hv].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (Hm (Z.of_nat j) ltac:(lia)), Hq, (c1_le_byte1 _ Hv). reflexivity.
Qed.

(* ======================================== bounds of shadow hulls ======================================== *)
Lemma c1_div8 : forall X, X / 8 * 8 <= X < X / 8 * 8 + 8.
Proof. intros X. pose proof (Z.div_mod X 8 ltac:(lia)). pose proof (Z.mod_pos_bound X 8 ltac:(lia)). lia. Qed.
Lemma c1_hull_bnd : forall x n a, w7_hull x n a -> SHADOW_OFF + x / 8 - 7 <= a < SHADOW_OFF + (x + n - 1) / 8 + 8.
Proof.
intros x n a Ha. unfold w7_hull, shadow_addr in Ha.
pose proof (c1_div8 (SHADOW_OFF + x / 8)). pose proof (c1_div8 (SHADOW_OFF + (x + n - 1) / 8)). lia.
Qed.
(* the hull of a range below 2^47 lies below the high shadow's end *)
Lemma c1_hull_low : forall x n a, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 -> w7_hull x n a -> 0 <= a < 0x10007fff8008.
Proof.
intros x n a H0 Hn Hxn Ha. pose proof (c1_hull_bnd x n a Ha). pose proof (c1_div8 x). pose proof (c1_div8 (x + n - 1)).
unfold SHADOW_OFF in *. lia.
Qed.
(* the hull of a part of the frame for locals lies outside the frame (the frame is outside the shadow band) *)
Section hf. Context {rc : YM05.RunCeil}.
Lemma c1_hull_frame : forall F lo n a, in_app F 1024 -> 0 <= lo -> 0 < n -> lo + n <= 1024 -> w7_hull (F + lo) n a ->
  a < F \/ F + 1024 <= a.
Proof.
intros F lo n a Happ Hlo Hn Hln Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
pose proof (c1_hull_bnd (F + lo) n a Ha). pose proof (c1_div8 (F + lo)). pose proof (c1_div8 (F + lo + n - 1)).
unfold SHADOW_OFF in *. lia.
Qed.
End hf.
(* the string's bytes and hull lie low *)
Lemma c1_strz_low : forall x (s : list byte) a, 0 <= x <= 0x20fe0 -> (length s <= 18)%nat -> w7_strz x s a ->
  0 <= a < 0x10007fff8008.
Proof.
intros x s a Hx Hs [Ha|Ha]; [lia|]. apply (c1_hull_low x (Z.of_nat (length s) + 1) a); [lia | lia | lia | exact Ha].
Qed.
Lemma c1_cs : forall z, existsb (Z.eqb z) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true -> acallee_saved z.
Proof.
intros z H. unfold acallee_saved. apply existsb_exists in H as (w & Hw & Hq). apply Z.eqb_eq in Hq. subst w.
cbn [In] in Hw. lia.
Qed.
Lemma c1_ne : forall z w, (z =? w) = false -> z <> w.
Proof. intros z w H. apply Z.eqb_neq. exact H. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis MCPY : aintrin_realizes rsegs B OCpy W7_MEMCPY.
Hypothesis STRL : astrlen_realizes rsegs B W7_STRLEN.

(* ======================================== strlen, c1_set, __asan_memcpy ======================================== *)
Lemma c1_calls : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) R F x (s : list byte)
  (Q : world rsegs -> config -> Prop),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  getr regs 1 = w64 C1_SLR -> getr regs 10 = w64 x -> getr regs 27 = w64 x ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  R mod 16 = 0 -> sp0 mod 16 = 0 -> R <= sp0 -> 2 * ESTACK - (R - sp0) <= STK ->
  0x7fff7f800000 <= R -> R + 0x1e0 <= 2 ^ 47 ->
  w7_strok W mem R x s -> aro_unowned rsegs B (aview rsegs (w_H W) mem) -> (12 <= length s <= 18)%nat ->
  val_mem rsegs (mrestrict (w_H W) mem) (R + 0xe0) 8 (F + 0xf8) -> 0 <= F -> F + 0xf8 + 18 < R - 2 * ESTACK ->
  (forall a, F + 0xf8 <= a < F + 0xf8 + Z.of_nat (length s) ->
   awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  amem_range (F + 0xf8) (Z.of_nat (length s)) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF (F + 0xf8) (Z.of_nat (length s)) ->
  shadow_hull_vis (aview rsegs (w_H W) mem) (F + 0xf8) (Z.of_nat (length s)) ->
  (forall a, w7_hull (F + 0xf8) (Z.of_nat (length s)) a -> 0 <= a < R - 2 * ESTACK) ->
  (forall a, w7_strz x s a -> 0 <= a < R - 2 * ESTACK) ->
  (F + 0xf8 + Z.of_nat (length s) <= x \/ x + Z.of_nat (length s) <= F + 0xf8) ->
  (forall regs2 mem2 md2,
   ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io md md2 ->
   (forall r, acallee_saved r -> r <> 21 -> r <> 24 -> r <> 25 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
   getr regs2 21 = w64 (Z.of_nat (length s)) -> getr regs2 24 = w64 (F + 0xf8) ->
   getr regs2 25 = w64 (Z.of_nat (length s)) ->
   (forall j, (j < length s)%nat ->
    aview rsegs (w_H W) mem2 (F + 0xf8 + Z.of_nat j) = Some (bv_unsigned (nth j s (Z_to_bv 8 0)))) ->
   w7_kept W mem mem2 (fun a => R - 2 * ESTACK <= a < R \/ F + 0xf8 <= a < F + 0xf8 + Z.of_nat (length s)) ->
   SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 C1_MCR) mem2 (seg_rom rsegs)) md2) Q) ->
  SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7_STRLEN) mem (seg_rom rsegs)) md) Q.
Proof using LAWS MCPY STRL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs R F x s Q
  HJ H1 H10 H27 H2 H9 H3 H4 HR16 Hs16 HRs HSTK HR1 HR2 HSO HARO Hls Hval HF0 HFR Hwr Hamd Hrad Hhud Hhd Hzs Hdis K.
pose proof HSO as (Hx0 & Hk32 & Hx63 & Hbytes & Hnul & Htail & Hstk & Hamx & Hrax & Hhux).
assert (HE : ESTACK = 4096) by reflexivity. rewrite HE in *.
assert (Hsp : spZ regs = sp0 + (R - sp0)) by (unfold spZ; rewrite H2; unfold w64; rewrite unsigned_lit_small; lia).
(* ---- strlen(vocab[i]) ---- *)
eapply SRr_bind.
{ apply (w7_strlen_at B LAWS W7_STRLEN STRL W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k x
    (Z.of_nat (length s)) (R - sp0) (w64 C1_SLR) HJ); try assumption; try lia.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - apply ret_ok_even; vm_compute; reflexivity.
  - exact (w7_strok_first_byte W mem R x s HSO).
  - intros a Ha. split.
    + destruct (Z.eq_dec a (x + Z.of_nat (length s))) as [->|Hne]; [rewrite Hnul; discriminate|].
      destruct (Hbytes (Z.to_nat (a - x)) ltac:(lia)) as [Hb _]. rewrite Z2Nat.id in Hb by lia.
      replace (x + (a - x)) with a in Hb by lia. rewrite Hb. discriminate.
    + rewrite Hsp. intros Hc. apply (Hstk a ltac:(lia)). lia.
  - intros a Ha. replace (sp0 + (R - sp0)) with R by lia. exact (Hstk a Ha). }
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & Hio1 & HP1 & H10a & HK1 & Hpr1).
replace (sp0 + (R - sp0)) with R in HK1 by lia.
assert (E : forall r, acallee_saved r -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HP1.
(* ---- 0x81fc4 .. 0x51d0c ---- *)
eapply SRr_bind.
{ apply (c1_set B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 R F (Z.of_nat (length s)) HJ1).
  - rewrite <- H9. exact (E 9 ltac:(unfold acallee_saved; lia)).
  - lia.
  - lia.
  - exact HR16.
  - exact H10a.
  - lia.
  - apply (w7_vm_kept W mem mem1 _ _ _ Hval). intros i Hi. apply HK1; lia.
  - lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hr2 & HK2 & Hpr2 & (R1 & R10 & R11 & R12 & R21 & R24 & R25)).
assert (EB : forall r, acallee_saved r -> r <> 21 -> r <> 24 -> r <> 25 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr Hr21 Hr24 Hr25. rewrite Hr2; [exact (E r Hr) | rewrite w7_cs_bv by exact Hr; unfold acallee_saved in Hr; lia |].
  apply w7_cs_out; [exact Hr|]. unfold acallee_saved in Hr. vm_compute. lia. }
assert (KB : w7_kept W mem mem2 (fun a => R - 2 * ESTACK <= a < R)).
{ intros a Ha Hz. cbv beta in Hz. rewrite (HK2 a Ha (fun f => f)). exact (HK1 a Ha Hz). }
assert (Hsp2 : spZ regs2 = sp0 + (R - sp0)).
{ unfold spZ. rewrite (w7_reg_eq regs regs2 2%bv (EB 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia))).
  exact Hsp. }
assert (R11' : getr regs2 11 = w64 x).
{ rewrite R11, <- H27. exact (E 27 ltac:(unfold acallee_saved; lia)). }
(* ---- memcpy(e.body, vocab[i], len) ---- *)
eapply SRr_bind.
{ apply (w7_memcpy_at B LAWS MCPY W regs2 mem2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc md2 k (F + 0xf8) x
    (Z.of_nat (length s)) (R - sp0) (w64 C1_MCR) HJ2 R10 R11' R12).
  - lia.
  - lia.
  - lia.
  - exact Hsp2.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - lia.
  - rewrite (w7_reg_eq regs regs2 3%bv (EB 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia))). exact H3.
  - rewrite (w7_reg_eq regs regs2 4%bv (EB 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia))). exact H4.
  - exact R1.
  - apply ret_ok_even; vm_compute; reflexivity.
  - intros a Ha. split; [exact (Hwr a Ha) | lia].
  - exact Hamd.
  - apply (w7_ra_kept W mem mem2); [exact Hrad | lia |]. intros a Ha. apply KB; cbv beta; pose proof (Hhd a Ha); lia.
  - intros Hl. apply (w7_hull_kept W mem mem2); [exact Hhud |]. intros a Ha. apply KB; cbv beta; pose proof (Hhd a Ha); lia.
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
    apply (w7_ra_kept W mem mem2); [exact Hrax | lia |]. intros a Ha. apply KB; cbv beta; pose proof (Hzs a (or_intror Ha)); lia.
  - intros Hl. apply (hm_hull_sub _ x (Z.of_nat (length s) + 1)); [| lia | lia | lia].
    apply (w7_hull_kept W mem mem2); [exact Hhux |]. intros a Ha. apply KB; cbv beta; pose proof (Hzs a (or_intror Ha)); lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & HP3 & R10' & HD3 & HK3 & Hpr3).
apply K.
- exact HJ3.
- eapply same_io_trans; [eapply same_io_trans; [exact Hio1 | exact Hio2] | exact Hio3].
- intros r Hr Hr21 Hr24 Hr25. rewrite (HP3 r Hr). exact (EB r Hr Hr21 Hr24 Hr25).
- rewrite (w7_reg_eq regs2 regs3 21%bv (HP3 21 ltac:(unfold acallee_saved; lia))). exact R21.
- rewrite (w7_reg_eq regs2 regs3 24%bv (HP3 24 ltac:(unfold acallee_saved; lia))). exact R24.
- rewrite (w7_reg_eq regs2 regs3 25%bv (HP3 25 ltac:(unfold acallee_saved; lia))). exact R25.
- intros j Hj. rewrite (HD3 (Z.of_nat j) ltac:(lia)).
  rewrite (KB (x + Z.of_nat j) ltac:(pose proof (Hzs (x + Z.of_nat j) ltac:(left; lia)); lia)
    ltac:(cbv beta; pose proof (Hzs (x + Z.of_nat j) ltac:(left; lia)); lia)).
  exact (proj1 (Hbytes j Hj)).
- intros a Ha Hz. cbv beta in Hz. rewrite (HK3 a Ha ltac:(lia) ltac:(lia)). apply KB; [exact Ha | cbv beta; lia].
Qed.

(* ======================================== the block lemma ======================================== *)
Theorem w6b_c1 : w6b_c1_stmt B MT.
Proof using MTL LAWS MCPY STRL.
unfold w6b_c1_stmt, w6b_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp b r Hctx Hk1 Hin Hvoc.
pose proof Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & Hrom).
pose proof Hin as (H2 & H3 & H4 & H9 & H23 & H24 & H14 & H25 & H21 & H27 & H20 & Vf8 & Vb0 & Vf0 & Vc0 & V20 & V70 & V80 &
  Hvb & Hkd & Hpp1 & Hpp2 & HF1 & HF2 & HF32 & Ez & Hrae & Hhe & Hc1 & Hw6 & Hhin & HdisF).
destruct Hw6 as (Hg & Hrain & Hc0 & Hcr & Ham & Hdis).
destruct Hvoc as (Hrav & Hvoc).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
assert (HRb : alloc_ceiling <= R - 16384 /\ R + 0x1e0 <= 2 ^ 47) by (rewrite HT in HspR; lia).
destruct HRb as (HRb1 & HRb2).
assert (Hin3 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin3) as (_ & Happ & _ & _).
rewrite <- HFa in Happ. change (fs_frame_bytes 4) with 1024 in Happ.
set (kd := bv_unsigned b) in *.
assert (H20' : getr regs 20 = w64 (kd - 256 * (kd / 128))) by (apply H20; rewrite Hk1; discriminate).
(* the index, the string and its facts at the entry *)
set (r1 := snd (fuzz_u8 r)).
assert (Hr1 : (length r1 <= length r)%nat) by (unfold r1; destruct r; cbn; lia).
set (i := fst (fuzz_u8 r) mod 9).
assert (Hi : 0 <= i < 9) by (apply Z.mod_pos_bound; lia).
set (x := w6b_vptr i).
set (s := nth (Z.to_nat i) vocab []).
pose proof (c1_vlen_in i Hi) as Hlen. change (c1_vlen i) with (Z.of_nat (length s)) in Hlen.
assert (Hls : (12 <= length s <= 18)%nat).
{ unfold c1_lens in Hlen. cbn [In] in Hlen. lia. }
pose proof (c1_vptr_range i) as Hx. change (w6b_vptr i) with x in Hx.
destruct (Hvoc i Hi) as (Vcell & Hcs). change (w6b_vptr i) with x in Vcell, Hcs.
change (nth (Z.to_nat i) vocab []) with s in Hcs.
pose proof Hcs as (_ & _ & _ & Hx0 & Hxs & Himg & _).
rewrite length_map in Hxs, Himg.
assert (SO0 : w7_strok W memc R x s).
{ apply (w7_strok_cstr W memc R x s Hcs).
  - intros a Ha. exact (c1_vtail i Hi a Ha (w_H W) memc).
  - unfold ESTACK. lia.
  - lia. }
(* ---- c1_head ---- *)
eapply SRr_bind; [exact (c1_head B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp kd r Hctx Hin)|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & Hio1 & Hr1h & HK1 & Hpr1 & (R10 & Rc8 & Rf8)).
(* ---- c1_vcell ---- *)
eapply SRr_bind.
{ apply (c1_vcell B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 i HJ1 R10 Hi).
  - rewrite Hr1h; [exact H23 | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
  - apply (w7_ra_kept W memc mem1); [exact Hrav | unfold W6B_VOCAB; lia |].
    intros a Ha. pose proof (c1_hull_low W6B_VOCAB 72 a ltac:(unfold W6B_VOCAB; lia) ltac:(lia)
      ltac:(unfold W6B_VOCAB; lia) Ha).
    apply HK1; [lia | unfold c1_head_wr; lia].
  - apply (w7_vm_kept W memc mem1 _ _ _ Vcell). intros j Hj. apply HK1; [unfold W6B_VOCAB; lia | unfold c1_head_wr, W6B_VOCAB; lia]. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hr2 & HK2 & Hpr2 & (R1 & R10' & R27)).
assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ c1_head_wr R a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. rewrite (HK2 a Ha (fun f => f)). exact (HK1 a Ha Hn). }
assert (Kr : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [1; 10; 11; 12; 14; 25; 27]%bv -> getr regs2 rr = getr regs rr).
{ intros rr Hr0 Hn. rewrite Hr2; [| exact Hr0 | intros X; apply Hn; cbn [In] in X |- *; tauto].
  apply Hr1h; [exact Hr0 | intros X; apply Hn; cbn [In] in X |- *; tauto]. }
assert (Hlow : forall a, 0 <= a < 0x10007fff8008 -> 0 <= a < 2 ^ 64 /\ ~ c1_head_wr R a /\ ~ (R - 8192 <= a < R)).
{ intros a Ha. unfold c1_head_wr. split; [lia|]. split; lia. }
(* ---- strlen, c1_set, memcpy ---- *)
apply (c1_calls STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k regs2 R F x s _ HJ2 R1 R10' R27).
- rewrite Kr; [exact H2 | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
- rewrite Kr; [exact H9 | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
- rewrite Kr; [exact H3 | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
- rewrite Kr; [exact H4 | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
- exact HR16.
- exact Hsp0al.
- lia.
- rewrite HT in HspR. unfold ESTACK. lia.
- lia.
- lia.
- apply (w7_strok_kept W memc mem2 R x s SO0). intros a Ha.
  pose proof (c1_strz_low x s a Hx ltac:(lia) Ha) as Hb. destruct (Hlow a Hb) as (Hb1 & Hb2 & _).
  exact (K12 a Hb1 Hb2).
- intros a Har Ho He. pose proof (w7_in_rom_low a Har) as Hlo. unfold kLowMemEnd in Hlo.
  rewrite (K12 a ltac:(lia) ltac:(unfold c1_head_wr; lia)). exact (Hrom a Har).
- exact Hls.
- apply (w7_vm_kept W memc mem2 _ _ _ Vc0). intros j Hj. apply K12; [lia | unfold c1_head_wr; lia].
- lia.
- unfold ESTACK. lia.
- intros a Ha. right. right. right. exists 4, pos. split; [exact Hown|]. left.
  unfold in_zr. cbn [fst snd]. rewrite <- HFa. change (fs_frame_bytes 4) with 1024. lia.
- unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
- apply (range_addressable_sub _ _ (F + 0xf0) 104); [| lia | lia].
  apply (w7_ra_kept W memc mem2); [exact Hrae | lia |]. intros a Ha.
  pose proof (c1_hull_low (F + 0xf0) 104 a ltac:(lia) ltac:(lia) ltac:(lia) Ha) as Hb.
  destruct (Hlow a Hb) as (Hb1 & Hb2 & _). exact (K12 a Hb1 Hb2).
- apply (hm_hull_sub _ (F + 0xf0) 104); [| lia | lia | lia].
  apply (w7_hull_kept W memc mem2); [exact Hhe |]. intros a Ha.
  pose proof (c1_hull_low (F + 0xf0) 104 a ltac:(lia) ltac:(lia) ltac:(lia) Ha) as Hb.
  destruct (Hlow a Hb) as (Hb1 & Hb2 & _). exact (K12 a Hb1 Hb2).
- intros a Ha. pose proof (c1_hull_low (F + 0xf8) (Z.of_nat (length s)) a ltac:(lia) ltac:(lia) ltac:(lia) Ha).
  unfold ESTACK. lia.
- intros a Ha. pose proof (c1_strz_low x s a Hx ltac:(lia) Ha). unfold ESTACK. lia.
- destruct (Z_le_gt_dec (F + 0xf8 + Z.of_nat (length s)) x) as [Hd|Hd]; [left; exact Hd|].
  destruct (Z_le_gt_dec (x + Z.of_nat (length s)) (F + 0xf8)) as [Hd'|Hd']; [right; exact Hd'|].
  exfalso. apply (frm_img rsegs B LAWS lyc Sc W memc mdc 4 pos (Z.max x (F + 0xf8)) HAR Hin3).
  + rewrite <- HFa. change (fs_frame_bytes 4) with 1024. lia.
  + replace (Z.max x (F + 0xf8)) with (x + (Z.max x (F + 0xf8) - x)) by lia. apply Himg. lia.
- (* ---- at 0x81fec: the tail ---- *)
  intros regs3 mem3 md3 HJ3 Hio3 HP3 S21 S24 S25 HD3 HK3.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ c1_head_wr R a -> ~ (R - 8192 <= a < R) ->
    ~ (F + 0xf8 <= a < F + 0xf8 + Z.of_nat (length s)) -> aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) memc a).
  { intros a Ha N1 N2 N3. rewrite (HK3 a Ha ltac:(cbv beta; unfold ESTACK; lia)). exact (K12 a Ha N1). }
  assert (Kr3 : forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 21 -> bv_unsigned q <> 24 ->
    bv_unsigned q <> 25 -> bv_unsigned q <> 0 -> ~ In q [1; 10; 11; 12; 14; 25; 27]%bv -> getr regs3 q = getr regs q).
  { intros q Hq1 Hq2 Hq3 Hq4 Hq0 Hq5. rewrite (w7_reg_eq regs2 regs3 q (HP3 _ Hq1 Hq2 Hq3 Hq4)). exact (Kr q Hq0 Hq5). }
  eapply SRr_mono.
  { apply (c1_tail B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem3 md3 k regs3 R F pos (Z.of_nat (length s)) kd vb
      (c + Z.of_nat (length r) - Z.of_nat (length r1)) pp HJ3 HR16 HRsp HspR Hown HFa Hlen Hkd).
    - rewrite Kr3; [exact H9 | apply c1_cs; reflexivity | apply c1_ne; reflexivity | apply c1_ne; reflexivity
        | apply c1_ne; reflexivity | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
    - rewrite Kr3; [exact H23 | apply c1_cs; reflexivity | apply c1_ne; reflexivity | apply c1_ne; reflexivity
        | apply c1_ne; reflexivity | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
    - rewrite Kr3; [exact H20' | apply c1_cs; reflexivity | apply c1_ne; reflexivity | apply c1_ne; reflexivity
        | apply c1_ne; reflexivity | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
    - exact S21.
    - exact S24.
    - exact S25.
    - exact Hvb.
    - lia.
    - lia.
    - exact Hpp2.
    - apply (w7_vm_kept W memc mem3 _ _ _ V70). intros j Hj. apply K3; unfold c1_head_wr; lia.
    - apply (w7_vm_kept W memc mem3 _ _ _ V80). intros j Hj. apply K3; unfold c1_head_wr; lia.
    - apply (w7_vm_kept W memc mem3 _ _ _ Vb0). intros j Hj. apply K3; unfold c1_head_wr; lia.
    - apply (w7_vm_kept W memc mem3 _ _ _ Vc0). intros j Hj. apply K3; unfold c1_head_wr; lia.
    - apply (w7_vm_kept W mem1 mem3 _ _ _ Rc8). intros j Hj.
      rewrite (HK3 (R + 0x68 + j) ltac:(lia) ltac:(cbv beta; unfold ESTACK; lia)).
      exact (HK2 (R + 0x68 + j) ltac:(lia) (fun f => f)).
    - apply (w7_vm_kept W memc mem3 _ _ _ Vf0). intros j Hj. apply K3; unfold c1_head_wr; lia.
    - intros j Hj. rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) memc mem3 (F + 0xf8 + Z.of_nat (length s) + j)
        (K3 (F + 0xf8 + Z.of_nat (length s) + j) ltac:(lia) ltac:(unfold c1_head_wr; lia) ltac:(lia) ltac:(lia))).
      replace (F + 0xf8 + Z.of_nat (length s) + j) with (F + 0xf0 + (8 + Z.of_nat (length s) + j)) by lia.
      apply Ez. lia.
    - apply (w7_ra_kept W memc mem3); [exact Hrae | lia |]. intros a Ha.
      pose proof (c1_hull_low (F + 0xf0) 104 a ltac:(lia) ltac:(lia) ltac:(lia) Ha) as Hb.
      pose proof (c1_hull_frame F 0xf0 104 a Happ ltac:(lia) ltac:(lia) ltac:(lia) Ha) as Hf.
      apply K3; unfold c1_head_wr; lia. }
  (* ---- the post at J ---- *)
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hr4 & HK4 & Hpr4 &
    (T20 & T21 & T27 & T25 & T0 & T4 & T8 & T9 & T10)).
  assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ c1_tail_wr F (Z.of_nat (length s)) a ->
    aview rsegs (w_H W) mem4 a = aview rsegs (w_H W) mem3 a) by exact HK4.
  unfold w6_post. exists lyc, Sc, regs4, mem4, md4.
  split; [reflexivity|].
  split; [exact HJ4|].
  split.
  { intros rr Hr0 Hn. pose proof (in_nz_regs rr Hr0) as Hrr. cbv [nz_regs In] in Hrr.
    repeat (destruct Hrr as [<-|Hrr];
      [ first
        [ exfalso; apply Hn; cbv [w6b_clob In]; repeat (first [left; reflexivity | right]); fail
        | lazymatch goal with |- getr _ ?q = _ =>
            rewrite (Hr4 q ltac:(apply c2_nz; reflexivity) ltac:(apply c2_notin; reflexivity)) end;
          apply Kr3; [apply c1_cs; reflexivity | apply c1_ne; reflexivity | apply c1_ne; reflexivity
            | apply c1_ne; reflexivity | apply c2_nz; reflexivity | apply c2_notin; reflexivity] ] |]).
    destruct Hrr. }
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split; [eapply same_io_trans; [eapply same_io_trans; [eapply same_io_trans; [exact Hio1 | exact Hio2] | exact Hio3]
    | exact Hio4]|].
  split; [apply mo_le_refl; exact MTL|].
  split.
  { intros a Ha Hn. unfold w6b_wr in Hn. rewrite HT in Hn.
    rewrite (K4 a Ha ltac:(unfold c1_tail_wr; lia)).
    exact (K3 a Ha ltac:(unfold c1_head_wr; lia) ltac:(lia) ltac:(lia)). }
  unfold w6b_J_R. rewrite (c1_model b r Hk1). cbn [fst snd].
  split; [exact T20|]. split; [exact T21|]. split; [exact T27|].
  split; [exact T25|].
  split.
  { apply (w7_vm_kept W mem1 mem4 _ _ _ Rf8). intros j Hj.
    rewrite (K4 (R + 0x118 + j) ltac:(lia) ltac:(unfold c1_tail_wr; lia)),
      (HK3 (R + 0x118 + j) ltac:(lia) ltac:(cbv beta; unfold ESTACK; lia)).
    exact (HK2 (R + 0x118 + j) ltac:(lia) (fun f => f)). }
  apply (c1_e_garr8 (w_H W) mem4 F i (kd <? 128) Hi).
  apply (c1_e_mem (w_H W) mem4 F s); [lia | exact T0 | exact T4 | | exact T8 | exact T9 | exact T10 |].
  + intros j Hj. rewrite (K4 (F + 0xf8 + Z.of_nat j) ltac:(lia) ltac:(unfold c1_tail_wr; lia)). exact (HD3 j Hj).
  + intros j Hj. rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) memc mem4 (F + 0xf0 + j)
      (eq_trans (K4 (F + 0xf0 + j) ltac:(lia) ltac:(unfold c1_tail_wr; lia))
        (K3 (F + 0xf0 + j) ltac:(lia) ltac:(unfold c1_head_wr; lia) ltac:(lia) ltac:(lia)))).
    apply Ez. lia.
Qed.
End d.
End b.

Print Assumptions w6b_c1.
