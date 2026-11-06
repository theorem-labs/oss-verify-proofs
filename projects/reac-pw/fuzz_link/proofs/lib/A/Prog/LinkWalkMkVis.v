(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module paths and module names changed; 328 of its 367 lines of code are new or changed and 300 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeCut.v, with its module paths and module names changed; 75 of its 149 lines of code are new or changed and 293 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the rest of a C string's NUL granule, visible across a step (shared lemma of the
   mark walks: reac_code_emit's vfprintf call, and any later callee that reads a caller's string).

   The libc string readers (model_decide_c.v astr_rt_ok, 6th conjunct; lib/Rt/SnShared.v pf_arg_asan and
   str_end) ask every byte after the NUL up to the end of its 8-byte granule to be visible. Those bytes are not in a
   read set, so `akept` does not move their value. Their visibility moves by the four classes of the NUL byte e
   (link_amem.v `akb` at the call):
   - the real-stack row outside the window [slo, shi) (both ends multiples of 8, so the whole granule is outside the
     window): above alloc_ceiling and off the image, visibility is presence there, and akept's presence clause
     keeps it;
   - a heap block (q, m) of the call: the granule ends at most at q + round_up (req_size m) 16 (q is 16-aligned);
     a byte below q + req_size m is present by AR's block law at the later state, a byte past it is the chunk's
     junk, visible by AR's junk law (`blk_tail_vis16r`);
   - an image byte: the granule ends at most at pcap_img_end (page-aligned), and the image's file backs every byte
     there (`segs_rom`);
   - a side frame (c, q) of the call: frames are 32-aligned and a multiple of 8 long, so the byte is in the frame,
     which is a frame of the later state, present by AR's frame law.
   The heap-tail lemmas are reac_served_markKitAt.v's (section tv), moved here so
   one copy serves every walk; `tail_vis_transport` is reac_served_markKitAt.v srm_tail_vis without its walk's
   context.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP09 YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the bytes past a heap block, to the next multiple of 16 of its size, are visible at every AR state ---- *)
Section tv. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Lemma chunk_tail_in_ajunk : forall ly S k, In k (st_chunks S) ->
  In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S).
Proof.
  intros ly S k Hk. unfold ajunk. right. right.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma chunk_room_mod16 : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) ->
  (ck_extent k - ck_rz k) mod 16 = 0.
Proof.
  intros ly S rd k M Hk.
  pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & RZ & _ & _ & G).
  assert (EX : ck_extent k mod 16 = 0).
  { destruct (ck_beg k) as [|off|r o|c q]; try solve [destruct G].
    - cbv zeta in G. destruct G as (Gc & _ & _ & Gext & _).
      pose proof (class_ok (prim_class off) ltac:(lia)) as (_ & K2 & _). rewrite Gext.
      apply Z.mod_divide in K2 as [q K2]; [|lia]. rewrite K2. replace (q * 32) with ((q * 2) * 16) by lia.
      apply Z.mod_mul. lia.
    - destruct G as (_ & Hp & _ & Gext & _). pose proof (secondary_geometry (ck_req k)) as SG.
      pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & Hn & _).
      destruct (SG ltac:(lia) Hp) as (_ & _ & _ & _ & S5 & _). rewrite Gext.
      apply Z.mod_divide in S5 as [q S5]; [|unfold kPage; lia]. rewrite S5. unfold kPage.
      replace (q * 4096 - 4096) with ((q * 256 - 256) * 16) by lia. apply Z.mod_mul. lia. }
  apply Z.mod_divide in EX as [a EX]; [|lia]. apply Z.mod_divide in RZ as [b RZ]; [|lia].
  rewrite EX, RZ. replace (a * 16 - b * 16) with ((a - b) * 16) by lia. apply Z.mod_mul. lia.
Qed.

(* past a block of any request (req_size 0 = 1): the bytes after its req_size bytes, to the next multiple of 16 *)
Lemma blk_tail_vis16r : forall ly S (W : world segs) mem md p n a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n <= a < p + round_up (req_size n) 16 -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md p n a (M & _) Hb Ha.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb.
  injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er.
  assert (Hrn : ck_req k = n) by congruence.
  subst u.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & UA & _ & _ & Hn & HX & _).
  pose proof (chunk_room_mod16 ly S _ k M Hk) as R16.
  assert (CN : ck_n k = req_size n) by (unfold ck_n; rewrite <- Hrn; reflexivity).
  assert (RU : round_up (req_size n) 16 <= ck_extent k - ck_rz k).
  { apply round_up_le; [lia | | exact R16]. first [lia | rewrite <- CN; lia | unfold ck_n in *; lia]. }
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ (chunk_tail_in_ajunk ly S k Hk)) as V.
  unfold range_vis in V. cbn [fst snd] in V. rewrite CN in V.
  rewrite aeval_aoff in V by (intros e'; destruct (ck_beg k); cbn; discriminate).
  change (aeval B ly (sptr_exp (ck_beg k))) with (ck_base B ly k) in V.
  replace a with (ck_base B ly k + (ck_rz k + req_size n) + (a - (ck_base B ly k + (ck_rz k + req_size n))))
    by lia.
  apply V. rewrite <- Ep, UA in Ha. lia.
Qed.
End tv.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
(* the image lies in [0x10000, pcap_img_end), and its file backs every byte there (at link's segments:
   LinkPa.v pa_img_range and AB13.v tfib_rom_all) *)
Hypothesis segs_img : forall a, in_img segs a -> 0x10000 <= a < pcap_img_end.
Hypothesis segs_rom : forall a, 0x10000 <= a < pcap_img_end -> seg_rom segs (Z_to_bv 64 a) <> None.

Lemma vis_of_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview segs H m a <> None.
Proof.
  intros H m a [Hh [x Hx]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hx. discriminate.
Qed.

Lemma present_of_vis : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img segs a -> aview segs H m a <> None -> apresent H m a.
Proof.
  intros H m a Ha Hn Hv. unfold aview, mbyte, mrestrict in Hv. unfold apresent.
  rewrite (seg_rom_none segs a Ha Hn) in Hv.
  destruct (H (Z_to_bv 64 a)); [exfalso; exact (Hv eq_refl)|]. split; [reflexivity|].
  destruct (m (Z_to_bv 64 a)) as [x|]; [exists x; reflexivity | exfalso; exact (Hv eq_refl)].
Qed.

Lemma vis_of_rom : forall (H : word -> bool) (m : word -> option byte) a,
  0x10000 <= a < pcap_img_end -> aview segs H m a <> None.
Proof.
  intros H m a Ha. unfold aview, mbyte.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [x|]; cbn [option_map]; [discriminate|].
  destruct (seg_rom segs (Z_to_bv 64 a)) eqn:Er; cbn [option_map]; [discriminate|].
  exfalso. exact (segs_rom a Ha Er).
Qed.

(* THE REST OF A NUL'S GRANULE across a step that keeps the call's memory by akept *)
Theorem tail_vis_transport : forall lyc Sc (W : world segs) memc ly2 S2 (W2 : world segs) mem2 md2 slo shi
    (E : Z -> Prop) e b,
  AR segs B ly2 S2 W2 mem2 md2 ->
  alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 47 ->
  slo mod 8 = 0 -> shi mod 8 = 0 ->
  (forall q m, In (q, m) (ablocks B lyc Sc) -> In (q, m) (ablocks B ly2 S2)) ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S2)) ->
  (forall c q, frame_addr ly2 c q = frame_addr lyc c q) ->
  akept segs B lyc Sc W memc W2 mem2 slo shi E ->
  akb segs B lyc Sc slo shi e -> e < b < e - e mod 8 + 8 ->
  aview segs (w_H W) memc b <> None -> aview segs (w_H W2) mem2 b <> None.
Proof.
  intros lyc Sc W memc ly2 S2 W2 mem2 md2 slo shi E e b HAR2 Hlo Hhi Hslo Hshi Hbl Hfr Hfa HK He Heb Hv0.
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hm8.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct He as [(Hs1 & Hs2) | [(q & m & Hqm & Hq) | [(Hi & _ & _) | (c & q & Hcq & Hr)]]].
  - (* the real-stack row, outside the window *)
    assert (Hnw : ~ (slo <= b < shi)).
    { pose proof (Z.mod_pos_bound slo 8 ltac:(lia)). pose proof (Z.mod_pos_bound shi 8 ltac:(lia)).
      intros Hw. apply Hs2. lia. }
    assert (Hni : ~ in_img segs b).
    { intros Hib. pose proof (segs_img b Hib) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia. }
    destruct HK as (_ & _ & _ & _ & K5 & _).
    apply vis_of_present. apply K5; [lia | exact Hnw |].
    apply present_of_vis; [lia | exact Hni | exact Hv0].
  - (* a heap block of the call *)
    pose proof (Hbl q m Hqm) as Hq2.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hq2) as (Hal & _ & _ & _ & Hpr & _).
    destruct (Z_lt_le_dec b (q + req_size m)) as [Hin | Hout].
    + apply vis_of_present. exact (proj1 (Hpr b ltac:(lia))).
    + apply (blk_tail_vis16r segs B ly2 S2 W2 mem2 md2 q m b HAR2 Hq2).
      split; [exact Hout|]. unfold round_up. lia.
  - (* an image byte *)
    pose proof (segs_img e Hi) as (He1 & He2).
    apply vis_of_rom. unfold pcap_img_end, YImgTop.IMG_TOP in *. lia.
  - (* a side frame of the call *)
    pose proof (Hfr c q Hcq) as Hc2.
    destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hc2) as (Hal & _ & Hpr & _).
    pose proof HAR2 as [M2 _].
    destruct (frame_facts B ly2 S2 _ c q M2 Hc2) as ((Hc0 & Hc10) & _).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. rewrite <- (Hfa c q) in Hr.
    assert (F8 : fs_frame_bytes c mod 8 = 0).
    { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
      replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by ring. apply Z.mod_mul. lia. }
    apply vis_of_present. exact (proj1 (Hpr b ltac:(lia))).
Qed.

End a.
