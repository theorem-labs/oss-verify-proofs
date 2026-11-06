(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (PresetX, c-libc-stdio lane): c-libc-stdio's strlen and strcmp contracts over the
   second allocator instance IMPLY the generic call-site texts at ARx := ARcf, and the lifts of those texts to
   ARcf /\ xs_placed_cf. rule 24: no function is proved here; these are implications between existing statements,
   and neither side is edited.

   OURS (the premises): lib/Reusable/YGcfStr.v of origin/cold/c-libc-stdio-presetstr-scmpA ca1b007819f:
   strcmp_res, str_meet, amem_range8, astrcmp_realizes_cf, astrlen_realizes_cf. Since ca1b007819f
   astrcmp_realizes_cf takes the per-call `rom_view segs W mem` (as astrlen_realizes_cf does); theirs takes it too.
   THEIRS (the conclusions): c-omx-alloc's YGcallMx.v texts, which carry amem_range8 since
   origin/cold/c-omx-alloc-preset-s1 ae309465079 (c-omx-alloc's choice (a), 01:56Z; BUILT AGAINST its head
   c8cf9d1543e): astrlen_realizes_x, astrcmp_realizes_x, astrlen_realizes_x_conj, astrcmp_realizes_x_conj.
   Until 04:3xZ they came from a marked stand-in, YGcallMx8.v, a verbatim copy of YGcallMx.v at 8150bb43cc9 with
   amem_range -> amem_range8. The swap changed only the Require line below, and the stand-in is deleted.

   The differences, conjunct by conjunct:
   - strlen: none. ecall_pre_x at ARcf (FCiface.v:36) IS ecall_pre_cf (YG0dcf.v:80), src_ok_cf IS src_ok
     (YG0d2cf.v:31), every other premise and the whole post are the same text: the proof is conversion.
   - strcmp, premises: ours quantifies the stop index k and the two bytes c1 c2 met there (str_meet); theirs gives
     each string NUL-terminated at its own kx / ky (first_byte, YG0d.v:373). first_stop finds that k, at most both
     lengths; every per-string premise of ours is theirs cut from kx + 1 / ky + 1 to k + 1 (the 2 ^ 32 and 2 ^ 63
     bounds, src_ok, the window clause, amem_range8, range_addressable, shadow_hull_vis). The cuts of the last two
     are the tree's own: YG0v.v:43 range_addressable_sub and YGcfHeadSh.v:93 shadow_hull_vis_sub_cf. Their
     word-tail premises are not used; their rom_view is passed to ours unchanged.
   - strcmp, post: ours returns a0 = strcmp_res c1 c2, theirs a0 = 0 exactly when kx = ky and the bytes below agree;
     strcmp_res c1 c2 is the zero word exactly when c1 = c2 (strcmp_res_zero), and with first_byte that is
     kx = ky = k and equality below. The frame (2 * ESTACK) and presence clauses are the same text. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0dcf YG0d2cf YGcfStr YGcfHeadSh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The first index at which two NUL-terminated strings differ or both end, at most both lengths. *)
Lemma first_stop : forall (rd : Z -> option Z) x y kx ky,
  0 <= kx -> 0 <= ky ->
  (forall i, 0 <= i < kx -> exists b, rd (x + i) = Some b /\ b <> 0) -> rd (x + kx) = Some 0 ->
  (forall i, 0 <= i < ky -> exists b, rd (y + i) = Some b /\ b <> 0) -> rd (y + ky) = Some 0 ->
  exists k, 0 <= k <= kx /\ k <= ky /\
    (forall i, 0 <= i < k -> exists b, rd (x + i) = Some b /\ rd (y + i) = Some b /\ b <> 0) /\
    exists bx by_, rd (x + k) = Some bx /\ rd (y + k) = Some by_ /\ (bx <> by_ \/ bx = 0).
Proof.
intros rd x y kx ky Hkx Hky Hnx Hzx Hny Hzy.
assert (Hsx : forall i, 0 <= i <= kx -> exists b, rd (x + i) = Some b).
{ intros i Hi. destruct (Z.eq_dec i kx) as [->|Hne]; [exists 0; exact Hzx|].
  destruct (Hnx i ltac:(lia)) as (b & Hb & _). exists b. exact Hb. }
assert (Hsy : forall i, 0 <= i <= ky -> exists b, rd (y + i) = Some b).
{ intros i Hi. destruct (Z.eq_dec i ky) as [->|Hne]; [exists 0; exact Hzy|].
  destruct (Hny i ltac:(lia)) as (b & Hb & _). exists b. exact Hb. }
assert (IND : forall n, 0 <= n -> n <= Z.min kx ky + 1 ->
  (exists k, 0 <= k < n /\
    (forall i, 0 <= i < k -> exists b, rd (x + i) = Some b /\ rd (y + i) = Some b /\ b <> 0) /\
    exists bx by_, rd (x + k) = Some bx /\ rd (y + k) = Some by_ /\ (bx <> by_ \/ bx = 0)) \/
  (forall i, 0 <= i < n -> exists b, rd (x + i) = Some b /\ rd (y + i) = Some b /\ b <> 0)).
{ intros n Hn0. pattern n. revert n Hn0. apply natlike_ind.
  - intros _. right. intros i Hi. lia.
  - intros n Hn IH Hn1. destruct (IH ltac:(lia)) as [(k & Hk & Hrest)|Hr].
    + left. exists k. split; [lia | exact Hrest].
    + destruct (Hsx n ltac:(lia)) as (bx & Hbx). destruct (Hsy n ltac:(lia)) as (by_ & Hby).
      destruct (Z.eq_dec bx by_) as [Heq|Hne]; [destruct (Z.eq_dec bx 0) as [H0|H0]|].
      * left. exists n. split; [lia|]. split; [exact Hr|].
        exists bx, by_. refine (conj Hbx (conj Hby _)). right. exact H0.
      * right. intros i Hi. destruct (Z.eq_dec i n) as [->|Hin].
        -- exists bx. subst by_. refine (conj Hbx (conj Hby H0)).
        -- apply Hr. lia.
      * left. exists n. split; [lia|]. split; [exact Hr|].
        exists bx, by_. refine (conj Hbx (conj Hby _)). left. exact Hne. }
destruct (IND (Z.min kx ky + 1) ltac:(lia) ltac:(lia)) as [(k & Hk & Hpre & Hstop)|Hall].
- exists k. split; [lia|]. split; [lia|]. split; [exact Hpre | exact Hstop].
- exfalso. destruct (Z.le_ge_cases kx ky) as [Hle|Hge].
  + destruct (Hall kx ltac:(lia)) as (b & Hb & _ & Hb0). rewrite Hzx in Hb. injection Hb as <-. apply Hb0. reflexivity.
  + destruct (Hall ky ltac:(lia)) as (b & _ & Hb & Hb0). rewrite Hzy in Hb. injection Hb as <-. apply Hb0. reflexivity.
Qed.

(* strcmp_res (AStrcmpDef.v's CharCmpX, YGcfStr.v:77) is the zero word exactly when the two bytes are equal. *)
Lemma strcmp_res_zero : forall c1 c2, Z_to_bv 64 (strcmp_res c1 c2) = Z_to_bv 64 0 <-> c1 = c2.
Proof.
intros c1 c2. unfold strcmp_res. destruct (Z.eqb_spec c1 c2) as [E|E].
- split; intros _; [exact E | reflexivity].
- split; [|intros E'; contradiction].
  intros H. exfalso. apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
  destruct (c1 <? c2); vm_compute in H; discriminate H.
Qed.

Lemma amem_range8_cut : forall p n n', 0 <= n' <= n -> amem_range8 p n -> amem_range8 p n'.
Proof. intros p n n' Hn H. unfold amem_range8 in *. lia. Qed.

Section CfX.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.

Lemma src_ok_cut : forall W regs mem s n n', n' <= n -> src_ok segs W regs mem s n -> src_ok segs W regs mem s n'.
Proof. intros W regs mem s n n' Hn H a Ha. apply H. lia. Qed.

Theorem astrlen_realizes_cf_x : forall pc,
astrlen_realizes_cf segs B pc ->
astrlen_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) pc.
Proof. intros pc H. exact H. Qed.

Theorem astrcmp_realizes_cf_x : forall pc,
astrcmp_realizes_cf segs B pc ->
astrcmp_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) pc.
Proof.
intros pc AC ly S Hp W regs mem md x y kx ky Hpre Hstk Hwin Ha0 Ha1 Hx Hy Hkx0 Hkx1 Hxk Hky0 Hky1 Hyk Hfbx Hfby
  Hsrcx Hsrcy Hwx Hwy Hamrx Hamry Hrax Hshvx Hray Hshvy _ _ Hrom.
destruct Hfbx as (_ & Hnzx & Hzx). specialize (Hzx ltac:(lia)).
destruct Hfby as (_ & Hnzy & Hzy). specialize (Hzy ltac:(lia)).
destruct (first_stop (aview segs (w_H W) mem) x y kx ky Hkx0 Hky0 Hnzx Hzx Hnzy Hzy)
  as (k & Hkx & Hky & Heq & bx & by_ & Hbx & Hby & Hstop).
assert (Hpre' : ecall_pre_cf segs B ly S Hp W regs mem md) by exact Hpre.
assert (Hmeet : str_meet segs W mem x y k bx by_).
{ unfold str_meet. split; [lia|]. exact (conj Heq (conj Hbx (conj Hby Hstop))). }
eapply SRr_mono; [exact (AC ly S Hp W regs mem md x y k bx by_ Hpre' Hstk Hwin Ha0 Ha1 Hx Hy
  ltac:(lia) ltac:(lia) ltac:(lia) Hmeet
  (src_ok_cut W regs mem x (kx + 1) (k + 1) ltac:(lia) Hsrcx)
  (src_ok_cut W regs mem y (ky + 1) (k + 1) ltac:(lia) Hsrcy)
  (fun a Ha => Hwx a ltac:(lia)) (fun a Ha => Hwy a ltac:(lia))
  (amem_range8_cut x (kx + 1) (k + 1) ltac:(lia) Hamrx)
  (amem_range8_cut y (ky + 1) (k + 1) ltac:(lia) Hamry)
  (range_addressable_sub _ SHADOW_OFF x (kx + 1) x (k + 1) Hrax ltac:(lia) ltac:(lia))
  (shadow_hull_vis_sub_cf _ x (kx + 1) x (k + 1) Hshvx ltac:(lia) ltac:(lia))
  (range_addressable_sub _ SHADOW_OFF y (ky + 1) y (k + 1) Hray ltac:(lia) ltac:(lia))
  (shadow_hull_vis_sub_cf _ y (ky + 1) y (k + 1) Hshvy ltac:(lia) ltac:(lia))
  Hrom)|].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR & Hpres & Hsbm & Hv & Hfr & Hap).
split; [reflexivity|]. exists regs', mem', md', (Z_to_bv 64 (strcmp_res bx by_)).
refine (conj Hc (conj HAR (conj Hpres (conj Hsbm (conj Hv (conj _ (conj Hfr Hap))))))).
refine (iff_trans (strcmp_res_zero bx by_) _). split.
- intros <-. destruct Hstop as [Hne|H0]; [congruence|]. subst bx.
  assert (Ekx : k = kx).
  { destruct (Z.eq_dec k kx) as [E|E]; [exact E|]. destruct (Hnzx k ltac:(lia)) as (b & Hb & Hb0).
    rewrite Hbx in Hb. injection Hb as <-. congruence. }
  assert (Eky : k = ky).
  { destruct (Z.eq_dec k ky) as [E|E]; [exact E|]. destruct (Hnzy k ltac:(lia)) as (b & Hb & Hb0).
    rewrite Hby in Hb. injection Hb as <-. congruence. }
  split; [lia|]. intros i Hi. destruct (Heq i ltac:(lia)) as (b & Hb1 & Hb2 & _). rewrite Hb1, Hb2. reflexivity.
- intros (Ek & Hall).
  assert (Ekx : k = kx).
  { destruct (Z.eq_dec k kx) as [E|E]; [exact E|]. exfalso.
    pose proof (Hall k ltac:(lia)) as Hxy. rewrite Hbx, Hby in Hxy. injection Hxy as Hxy.
    destruct (Hnzx k ltac:(lia)) as (b & Hb & Hb0). rewrite Hbx in Hb. injection Hb as <-.
    destruct Hstop as [Hne|H0]; [exact (Hne Hxy) | exact (Hb0 H0)]. }
  subst k. rewrite Hzx in Hbx. injection Hbx as <-. rewrite Ek, Hzy in Hby. injection Hby as <-. reflexivity.
Qed.

(* The walks' relation ARcf /\ xs_placed_cf (FuzzStrdup.v's ARc): our text, then the _conj lift (YGcallMx.v :580 /
   :596; from the stand-in until the swap). *)
Theorem astrlen_realizes_cf_xs : forall pc,
astrlen_realizes_cf segs B pc ->
astrlen_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S) pc.
Proof.
intros pc H. exact (astrlen_realizes_x_conj segs B _ (fun ly S => xs_placed_cf ly S) pc (astrlen_realizes_cf_x pc H)).
Qed.

Theorem astrcmp_realizes_cf_xs : forall pc,
astrcmp_realizes_cf segs B pc ->
astrcmp_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S) pc.
Proof.
intros pc H. exact (astrcmp_realizes_x_conj segs B _ (fun ly S => xs_placed_cf ly S) pc (astrcmp_realizes_cf_x pc H)).
Qed.

End CfX.
