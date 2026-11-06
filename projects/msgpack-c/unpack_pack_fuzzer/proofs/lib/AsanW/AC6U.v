(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase ARep ALayout AHeapP.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT}.

Definition RIP (L : alayout) : Z := al_space_beg L + 137438953472.
Lemma ri_in_page : forall L c, 1 <= c < K_NUM_CLASSES -> RIP L + 128 <= aregion_info L c /\ aregion_info L c + 128 <= RIP L + 4096.
Proof. intros L c Hc. unfold RIP, aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_NUM_CLASSES in *. change (2^37) with 137438953472. lia. Qed.
Lemma rip_high : forall L, alayout_ok L -> 0x10007fff8000 <= RIP L /\ RIP L + 4096 <= ATOP.
Proof.
  intros L ALO. pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP. unfold RIP. lia.
Qed.

Lemma c6c_off_page : forall L a, alayout_ok L -> (a < 0xd14f8 \/ (AIMG_HI <= a /\ (a < RIP L \/ RIP L + 4096 <= a))) -> ~ c6_cell L a.
Proof.
  intros L a ALO Ha C. destruct (rip_high L ALO) as [R1 R2]. unfold AIMG_HI in Ha. unfold c6_cell in C.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|(c & Hc & _ & ->)]]]]]]]]; try lia.
  destruct (ri_in_page L c Hc) as [P1 P2]. lia.
Qed.
Lemma c6c_img : forall L a, alayout_ok L -> a < AIMG_HI ->
  ~ (0xd14f8 <= a < 0xd1538) -> ~ (0xd3470 <= a < 0xd3478) -> ~ (0xd9328 <= a < 0xd9360) -> ~ (0x169560 <= a < 0x169568)
  -> ~ (0x16b628 <= a < 0x16b629) -> ~ (0x16b678 <= a < 0x16b680) -> ~ (0x16b6ec <= a < 0x16b6ed) -> ~ (0x16b7d0 <= a < 0x16b7d8) -> ~ c6_cell L a.
Proof.
  intros L a ALO Ha N1 N2 N3 N4 N5 N6 N7 N8 C. destruct (rip_high L ALO) as [R1 R2]. unfold AIMG_HI in Ha. unfold c6_cell in C.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|(c & Hc & _ & ->)]]]]]]]]; try tauto.
  destruct (ri_in_page L c Hc) as [P1 P2]. lia.
Qed.
Lemma c6c_ri : forall L c a, alayout_ok L -> 1 <= c < K_NUM_CLASSES -> aregion_info L c <= a < aregion_info L c + 128 ->
  (a <> aregion_info L c + 68 \/ c = K_BATCH_CLASS) -> ~ c6_cell L a.
Proof.
  intros L c a ALO Hc Ha NF C. destruct (rip_high L ALO) as [R1 R2]. destruct (ri_in_page L c Hc) as [P1 P2]. unfold c6_cell in C.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|(c' & Hc' & NB & E)]]]]]]]]; try lia.
  assert (c' = c) by (unfold aregion_info, ARI_STRIDE in *; lia). subst c'. destruct NF as [NF|NF]; [exact (NF E)| exact (NB NF)].
Qed.

Lemma c6u_nil : forall L, c6_untouched L []. Proof. intros L. constructor. Qed.
Lemma c6u_cons : forall L iv W, (forall a, fst iv <= a < snd iv -> ~ c6_cell L a) -> c6_untouched L W -> c6_untouched L (iv :: W).
Proof. intros L iv W H1 H2. constructor; assumption. Qed.
Lemma c6u_app : forall L W1 W2, c6_untouched L W1 -> c6_untouched L W2 -> c6_untouched L (W1 ++ W2).
Proof. intros L W1 W2 H1 H2. apply Forall_app. split; assumption. Qed.

Lemma c6p_off : forall L lo hi, alayout_ok L -> (hi <= 0xd14f8 \/ (AIMG_HI <= lo /\ (hi <= RIP L \/ RIP L + 4096 <= lo))) ->
  forall a, lo <= a < hi -> ~ c6_cell L a.
Proof. intros L lo hi ALO H a Ha. apply (c6c_off_page L a ALO). lia. Qed.

Lemma c6p_img : forall L lo hi, alayout_ok L -> hi <= AIMG_HI ->
     (hi <= 0xd14f8 \/ (0xd1538 <= lo /\ hi <= 0xd3470) \/ (0xd3478 <= lo /\ hi <= 0xd9328) \/ (0xd9360 <= lo /\ hi <= 0x169560)
      \/ (0x169568 <= lo /\ hi <= 0x16b628) \/ (0x16b629 <= lo /\ hi <= 0x16b678) \/ (0x16b680 <= lo /\ hi <= 0x16b6ec)
      \/ (0x16b6ed <= lo /\ hi <= 0x16b7d0) \/ 0x16b7d8 <= lo) ->
  forall a, lo <= a < hi -> ~ c6_cell L a.
Proof. intros L lo hi ALO HI H a Ha. apply (c6c_img L a ALO); lia. Qed.

Definition c6_imgp (lo hi : Z) : Prop :=
  hi <= AIMG_HI /\
     (hi <= 0xd14f8 \/ (0xd1538 <= lo /\ hi <= 0xd3470) \/ (0xd3478 <= lo /\ hi <= 0xd9328) \/ (0xd9360 <= lo /\ hi <= 0x169560)
      \/ (0x169568 <= lo /\ hi <= 0x16b628) \/ (0x16b629 <= lo /\ hi <= 0x16b678) \/ (0x16b680 <= lo /\ hi <= 0x16b6ec)
      \/ (0x16b6ed <= lo /\ hi <= 0x16b7d0) \/ 0x16b7d8 <= lo).
Lemma c6p_imgp : forall L lo hi, alayout_ok L -> c6_imgp lo hi -> forall a, lo <= a < hi -> ~ c6_cell L a.
Proof. intros L lo hi ALO [H1 H2]. exact (c6p_img L lo hi ALO H1 H2). Qed.

Lemma c6p_ri : forall L c lo hi, alayout_ok L -> 1 <= c < K_NUM_CLASSES -> aregion_info L c <= lo -> hi <= aregion_info L c + 128 ->
  (hi <= aregion_info L c + 68 \/ aregion_info L c + 69 <= lo \/ c = K_BATCH_CLASS) ->
  forall a, lo <= a < hi -> ~ c6_cell L a.
Proof. intros L c lo hi ALO Hc H1 H2 H3 a Ha. apply (c6c_ri L c a ALO Hc); [lia|]. destruct H3 as [H3|[H3|H3]]; [left; lia| left; lia| right; exact H3]. Qed.

Definition c6_std (L : alayout) (lo hi : Z) : Prop :=
     ATOP <= lo
  \/ (al_t L <= lo /\ hi <= al_t L + 4096) \/ (al_ctx L <= lo /\ hi <= al_ctx L + 65536)
  \/ (al_res L <= lo /\ hi <= RIP L)
  \/ (0x7fff7000 <= lo /\ hi <= 0x10007fff8000)
  \/ (AINSTANCE <= lo /\ hi <= 0xd67f0) \/ (0xdacc0 <= lo /\ hi <= 0x15bcf0) \/ (0x1ab988 <= lo /\ hi <= 0x5fb9d0)
  \/ (al_nodes L <= lo /\ hi <= al_nodes L + 1048576) \/ (al_store L <= lo /\ hi <= al_store L + 8388608)
  \/ (al_fake L <= lo /\ hi <= al_fake L + 11571200) \/ (al_dtls L <= lo /\ hi <= al_dtls L + 4096)
  \/ (al_ptr_array L <= lo /\ hi <= al_ptr_array L + 8388608).
Lemma c6p_std : forall L lo hi, alayout_ok L -> (lo < hi -> c6_std L lo hi) -> forall a, lo <= a < hi -> ~ c6_cell L a.
Proof.
  intros L lo hi ALO K a Ha. specialize (K ltac:(lia)). destruct (rip_high L ALO) as [RP1 RP2]. pose proof atop_range as ATR.
  pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP.
  unfold c6_std, AINSTANCE in K. unfold RIP in *.
  destruct K as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]].
  - apply (c6c_off_page L a ALO). right. unfold AIMG_HI, RIP. lia.
  - pose proof (ao_t L ALO) as (_ & _ & _ & _ & OTi). pose proof (ad_t_res L ALO) as D. unfold iclr, AIMG_LO, AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - pose proof (aobj_img _ _ (ao_ctx L ALO) ltac:(lia)) as Oi. pose proof (ad_ctx_res L ALO) as D. unfold AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - apply (c6c_img L a ALO); unfold AIMG_HI; lia.
  - apply (c6c_img L a ALO); unfold AIMG_HI; lia.
  - apply (c6c_img L a ALO); unfold AIMG_HI; lia.
  - pose proof (aobj_img _ _ (ao_nodes L ALO) ltac:(lia)) as Oi. pose proof (ad_nodes_res L ALO) as D. unfold AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - pose proof (aobj_img _ _ (ao_store L ALO) ltac:(lia)) as Oi. pose proof (ad_store_res L ALO) as D. unfold AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - pose proof (aobj_img _ _ (ao_fake L ALO) ltac:(lia)) as Oi. pose proof (ad_fake_res L ALO) as D. unfold AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - pose proof (ao_dtls L ALO) as (_ & _ & _ & _ & Oi). pose proof (ad_dtls_res L ALO) as D. unfold iclr, AIMG_LO, AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - pose proof (aobj_img _ _ (ao_ptr L ALO) ltac:(lia)) as Oi. pose proof (ad_ptr_res L ALO) as D. unfold AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
Qed.
End CANSEC.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB ARep.TwinB ALayout.TwinB AHeapP.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC. Context {rc : runConstT}.

Definition RIP (L : alayout) : Z := al_space_beg L + 137438953472.
Lemma ri_in_page : forall L c, 1 <= c < K_NUM_CLASSES -> RIP L + 128 <= aregion_info L c /\ aregion_info L c + 128 <= RIP L + 4096.
Proof. intros L c Hc. unfold RIP, aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_NUM_CLASSES in *. change (2^37) with 137438953472. lia. Qed.
Lemma rip_high : forall L, alayout_ok L -> 0x10007fff8000 <= RIP L /\ RIP L + 4096 <= ATOP.
Proof.
  intros L ALO. pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP. unfold RIP. lia.
Qed.

Lemma c6c_off_page : forall L a, alayout_ok L -> (a < 0xd3610 \/ (AIMG_HI <= a /\ (a < RIP L \/ RIP L + 4096 <= a))) -> ~ c6_cell L a.
Proof.
  intros L a ALO Ha C. destruct (rip_high L ALO) as [R1 R2]. unfold AIMG_HI in Ha. unfold c6_cell in C.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|(c & Hc & _ & ->)]]]]]]]]; try lia.
  destruct (ri_in_page L c Hc) as [P1 P2]. lia.
Qed.
Lemma c6c_img : forall L a, alayout_ok L -> a < AIMG_HI ->
  ~ (0xd3610 <= a < 0xd3650) -> ~ (0xd5588 <= a < 0xd5590) -> ~ (0xdb4e8 <= a < 0xdb520) -> ~ (0x16b720 <= a < 0x16b728)
  -> ~ (0x16d7e8 <= a < 0x16d7e9) -> ~ (0x16d838 <= a < 0x16d840) -> ~ (0x16d8ac <= a < 0x16d8ad) -> ~ (0x16d990 <= a < 0x16d998) -> ~ c6_cell L a.
Proof.
  intros L a ALO Ha N1 N2 N3 N4 N5 N6 N7 N8 C. destruct (rip_high L ALO) as [R1 R2]. unfold AIMG_HI in Ha. unfold c6_cell in C.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|(c & Hc & _ & ->)]]]]]]]]; try tauto.
  destruct (ri_in_page L c Hc) as [P1 P2]. lia.
Qed.
Lemma c6c_ri : forall L c a, alayout_ok L -> 1 <= c < K_NUM_CLASSES -> aregion_info L c <= a < aregion_info L c + 128 ->
  (a <> aregion_info L c + 68 \/ c = K_BATCH_CLASS) -> ~ c6_cell L a.
Proof.
  intros L c a ALO Hc Ha NF C. destruct (rip_high L ALO) as [R1 R2]. destruct (ri_in_page L c Hc) as [P1 P2]. unfold c6_cell in C.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|(c' & Hc' & NB & E)]]]]]]]]; try lia.
  assert (c' = c) by (unfold aregion_info, ARI_STRIDE in *; lia). subst c'. destruct NF as [NF|NF]; [exact (NF E)| exact (NB NF)].
Qed.

Lemma c6u_nil : forall L, c6_untouched L []. Proof. intros L. constructor. Qed.
Lemma c6u_cons : forall L iv W, (forall a, fst iv <= a < snd iv -> ~ c6_cell L a) -> c6_untouched L W -> c6_untouched L (iv :: W).
Proof. intros L iv W H1 H2. constructor; assumption. Qed.
Lemma c6u_app : forall L W1 W2, c6_untouched L W1 -> c6_untouched L W2 -> c6_untouched L (W1 ++ W2).
Proof. intros L W1 W2 H1 H2. apply Forall_app. split; assumption. Qed.

Lemma c6p_off : forall L lo hi, alayout_ok L -> (hi <= 0xd3610 \/ (AIMG_HI <= lo /\ (hi <= RIP L \/ RIP L + 4096 <= lo))) ->
  forall a, lo <= a < hi -> ~ c6_cell L a.
Proof. intros L lo hi ALO H a Ha. apply (c6c_off_page L a ALO). lia. Qed.

Lemma c6p_img : forall L lo hi, alayout_ok L -> hi <= AIMG_HI ->
     (hi <= 0xd3610 \/ (0xd3650 <= lo /\ hi <= 0xd5588) \/ (0xd5590 <= lo /\ hi <= 0xdb4e8) \/ (0xdb520 <= lo /\ hi <= 0x16b720)
      \/ (0x16b728 <= lo /\ hi <= 0x16d7e8) \/ (0x16d7e9 <= lo /\ hi <= 0x16d838) \/ (0x16d840 <= lo /\ hi <= 0x16d8ac)
      \/ (0x16d8ad <= lo /\ hi <= 0x16d990) \/ 0x16d998 <= lo) ->
  forall a, lo <= a < hi -> ~ c6_cell L a.
Proof. intros L lo hi ALO HI H a Ha. apply (c6c_img L a ALO); lia. Qed.

Definition c6_imgp (lo hi : Z) : Prop :=
  hi <= AIMG_HI /\
     (hi <= 0xd3610 \/ (0xd3650 <= lo /\ hi <= 0xd5588) \/ (0xd5590 <= lo /\ hi <= 0xdb4e8) \/ (0xdb520 <= lo /\ hi <= 0x16b720)
      \/ (0x16b728 <= lo /\ hi <= 0x16d7e8) \/ (0x16d7e9 <= lo /\ hi <= 0x16d838) \/ (0x16d840 <= lo /\ hi <= 0x16d8ac)
      \/ (0x16d8ad <= lo /\ hi <= 0x16d990) \/ 0x16d998 <= lo).
Lemma c6p_imgp : forall L lo hi, alayout_ok L -> c6_imgp lo hi -> forall a, lo <= a < hi -> ~ c6_cell L a.
Proof. intros L lo hi ALO [H1 H2]. exact (c6p_img L lo hi ALO H1 H2). Qed.

Lemma c6p_ri : forall L c lo hi, alayout_ok L -> 1 <= c < K_NUM_CLASSES -> aregion_info L c <= lo -> hi <= aregion_info L c + 128 ->
  (hi <= aregion_info L c + 68 \/ aregion_info L c + 69 <= lo \/ c = K_BATCH_CLASS) ->
  forall a, lo <= a < hi -> ~ c6_cell L a.
Proof. intros L c lo hi ALO Hc H1 H2 H3 a Ha. apply (c6c_ri L c a ALO Hc); [lia|]. destruct H3 as [H3|[H3|H3]]; [left; lia| left; lia| right; exact H3]. Qed.

Definition c6_std (L : alayout) (lo hi : Z) : Prop :=
     ATOP <= lo
  \/ (al_t L <= lo /\ hi <= al_t L + 4096) \/ (al_ctx L <= lo /\ hi <= al_ctx L + 65536)
  \/ (al_res L <= lo /\ hi <= RIP L)
  \/ (0x7fff7000 <= lo /\ hi <= 0x10007fff8000)
  \/ (AINSTANCE <= lo /\ hi <= 0xd89b0) \/ (0xdce80 <= lo /\ hi <= 0x15deb0) \/ (0x1adb48 <= lo /\ hi <= 0x5fdb90)
  \/ (al_nodes L <= lo /\ hi <= al_nodes L + 1048576) \/ (al_store L <= lo /\ hi <= al_store L + 8388608)
  \/ (al_fake L <= lo /\ hi <= al_fake L + 11571200) \/ (al_dtls L <= lo /\ hi <= al_dtls L + 4096)
  \/ (al_ptr_array L <= lo /\ hi <= al_ptr_array L + 8388608).
Lemma c6p_std : forall L lo hi, alayout_ok L -> (lo < hi -> c6_std L lo hi) -> forall a, lo <= a < hi -> ~ c6_cell L a.
Proof.
  intros L lo hi ALO K a Ha. specialize (K ltac:(lia)). destruct (rip_high L ALO) as [RP1 RP2]. pose proof atop_range as ATR.
  pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP.
  unfold c6_std, AINSTANCE in K. unfold RIP in *.
  destruct K as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]].
  - apply (c6c_off_page L a ALO). right. unfold AIMG_HI, RIP. lia.
  - pose proof (ao_t L ALO) as (_ & _ & _ & _ & OTi). pose proof (ad_t_res L ALO) as D. unfold iclr, AIMG_LO, AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - pose proof (aobj_img _ _ (ao_ctx L ALO) ltac:(lia)) as Oi. pose proof (ad_ctx_res L ALO) as D. unfold AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - apply (c6c_img L a ALO); unfold AIMG_HI; lia.
  - apply (c6c_img L a ALO); unfold AIMG_HI; lia.
  - apply (c6c_img L a ALO); unfold AIMG_HI; lia.
  - pose proof (aobj_img _ _ (ao_nodes L ALO) ltac:(lia)) as Oi. pose proof (ad_nodes_res L ALO) as D. unfold AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - pose proof (aobj_img _ _ (ao_store L ALO) ltac:(lia)) as Oi. pose proof (ad_store_res L ALO) as D. unfold AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - pose proof (aobj_img _ _ (ao_fake L ALO) ltac:(lia)) as Oi. pose proof (ad_fake_res L ALO) as D. unfold AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - pose proof (ao_dtls L ALO) as (_ & _ & _ & _ & Oi). pose proof (ad_dtls_res L ALO) as D. unfold iclr, AIMG_LO, AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
  - pose proof (aobj_img _ _ (ao_ptr L ALO) ltac:(lia)) as Oi. pose proof (ad_ptr_res L ALO) as D. unfold AIMG_HI, adisj in *.
    apply (c6c_off_page L a ALO). unfold AIMG_HI, RIP. lia.
Qed.
End CANSEC.
End TwinB.
