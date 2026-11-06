(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31, QMm W1 lift kit, image A (a Theorem Labs lane, the image-A lead; owner a Theorem Labs lane 01:53Z).
   QMm W1 made top_x's relation carry arodata_ok_cf (W_LLVMFuzzerTestOneInput_top_x.v:189-191). Every file that
   states a runtime contract at its OWN COPY of that relation must give the copy the same last conjunct and re-prove
   the contract there. Each of those contracts has the same shape: its post gives the relation at mem', W' = W, and
   a VIEW FRAME, `~ aowned at S -> ~ aowned at S' -> ~ (the stack window) -> aview mem' a = aview mem a`, outside
   whatever that rule writes. This file holds the four facts every one of those lifts needs, so the lifts are a
   line each and all say the same thing.

   arodata_view_keep is the whole argument: the view decides the overlay at an arodata address. aview is
   `option_map bv_unsigned (mbyte segs (mrestrict (w_H W) mem) a)` (Reusable/YG0n.v:18), mrestrict hides a byte only
   where w_H W is true (YK04.v:17), and mbyte falls back to seg_rom when the overlay holds nothing (YP09.v:18). An
   arodata address is an image address, and the hidden set is off the segments, so it is not hidden there; so the
   view at it is the overlay byte when there is one and the ROM byte when there is not. If the view does not move
   and the old overlay met arodata_ok_cf, then a byte the new overlay holds there is the ROM byte, whether the old
   overlay held one or not.

   THE 3c FORM: part 3c widens arodata_ok_cf's address side from [cf_relro_lo, cf_relro_hi) to
   YG0dcf.aro_addr_cf (that interval OR one of the image's five cf_ro_reads ranges). This file is written on the
   pre-3c base, so it says the interval; on the 3c base the four statements take `@aro_addr_cf CfImg_A a` in its
   place and nothing else changes, because ReplyKeptAroA.aro_kept_A already covers the wider set.
   rule 24: proves no function (kind: invariant lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YM05 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0n YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyKeptAroA W_journal.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := AB1v.tfibsegs.
(* part 3c has landed on this base, so the arodata addresses are aro_addr_cf: the RELRO interval OR one of the
   image's five read-only read ranges. ReplyKeptAroA.aro_kept_A covers both, so nothing below changes but this line. *)
Local Notation ARO := (@aro_addr_cf CfImg_A).

(* (1) an arodata address that is not an owned static is an image address, in 64 bits *)
Lemma aro_img_A : forall a, ARO a -> ~ Exists (in_zr a) (as_owned_static TfibB) ->
  0 <= a < 2 ^ 64 /\ in_img segs a.
Proof.
intros a Ha Hno. destruct (ReplyKeptAroA.aro_kept_A a Ha Hno) as (Hb & Hi & _).
split; [exact Hb | exact Hi].
Qed.

(* (2) its bounds, for the stack window: the whole arodata range lies below the image's end *)
Lemma aro_low_A : forall a, ARO a -> 0x10000 <= a < 0x5fb000.
Proof.
intros a [Hr | Hro].
- cbn [cf_relro_lo cf_relro_hi CfImg_A] in Hr. lia.
- cbn [cf_ro_reads CfImg_A] in Hro.
  repeat (apply Exists_cons in Hro as [Hz|Hro]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia|]).
  inversion Hro.
Qed.

(* (3) it is not an owned byte of any state the relation holds at (AR_owned_image_law at ARcf) *)
Lemma aro_not_owned_A : forall ly S Hp (W : world segs) mem md a,
  ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md ->
  ARO a -> ~ Exists (in_zr a) (as_owned_static TfibB) -> ~ aowned TfibB ly S a.
intros ly S Hp W mem md a HAR Ha Hno Hown.
apply Hno.
apply (proj1 (alc_owned_image segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)
  ly S Hp W mem md a HAR (proj2 (aro_img_A a Ha Hno)))). exact Hown.
Qed.

(* (4) THE LIFT: a step that keeps the VIEW at the arodata addresses keeps arodata_ok_cf *)
Lemma arodata_view_keep : forall (W : world segs) (mem mem' : word -> option byte),
  (forall a, ARO a -> ~ Exists (in_zr a) (as_owned_static TfibB) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  @arodata_ok_cf CfImg_A segs TfibB mem -> @arodata_ok_cf CfImg_A segs TfibB mem'.
Proof.
intros W mem mem' HV HA a b Hm' Ha Hno.
pose proof (HV a Ha Hno) as E.
assert (Hh : w_H W (Z_to_bv 64 a) = false).
{ apply W_journal.hidden_not_img. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact (proj1 (aro_img_A a Ha Hno)).
  exact (proj2 (aro_img_A a Ha Hno)). }
unfold aview, mbyte, mrestrict in E. rewrite Hh in E. rewrite Hm' in E.
destruct (mem (Z_to_bv 64 a)) as [b0|] eqn:Em.
- cbn in E. injection E as E. apply bv_eq in E as <-. exact (HA a b Em Ha Hno).
- cbn in E. destruct (seg_rom segs (Z_to_bv 64 a)) as [br|] eqn:Er; [|discriminate E].
  cbn in E. injection E as E. apply bv_eq in E as ->. reflexivity.
Qed.

End a.
