(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed. *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed; 778 of its 849 lines of code are new or changed and 69 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnTransportCg.v, with its module paths and module names changed; 709 of its 816 lines of code are new or changed and 742 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_kit.v, with its module paths and module names changed; 156 of its 242 lines of code are new or changed and 730 lines of the source are left out. *)
(* on_announce_seg_kitf: the kit's lemmas on struct diginet_frame f and on the frame bytes b at buf at a later state of
   on_announce's image-A walk (beside lib/A/Prog/on_announce_seg_kit.v, which it Requires): onann_f30 (f's 64 bytes
   kept and readable, cmd at f + 30, the body pointer and its length at f + 32 and f + 40, read through the view;
   lib/Prog/diginet_frame_parse_c.v parse_cells), onann_buf_kept (the bytes b at buf placed by trans_src_ok and
   kept, kit onann_src_kept at q = buf), onann_ks (the entry frames' shadow bytes kept by a walk whose written range
   lies in G), and the byte-array helpers they use (onann_garr8_view, onann_view1, onann_rdword_le8,
   onann_fbytes_split, onann_f_split). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TNeed TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require codec_cells diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require DgnTransportLeafb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module CC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.codec_cells.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportLeafb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.


Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.
Variable MT : ameter_ops.

(* ------------------------------------------------------------------ *)
(* 7. f's 64 bytes and the bytes at buf at a later state               *)
(* ------------------------------------------------------------------ *)

(* The shadow bytes of the entry's frames are kept by a walk whose written range lies in G (G is below the shadow
   band). *)
Lemma onann_ks : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 slo shi (E : Z -> Prop),
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, E a -> inG TG.G_HARNESS a) ->
  forall cid p s, In (cid, p) (frames Sc) ->
    in_zr s (shadow_addr (frame_addr lyc cid p), fs_frame_bytes cid / 8) ->
    aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s.
Proof.
  intros LAWS lyc Sc W memc mdc W2 mem2 slo shi E HAR (_ & _ & _ & K4 & _) HEG cid p s Hin Hs.
  apply (K4 cid p s Hin (or_intror Hs)). intro He.
  pose proof (inG_G_HARNESS_hull s (HEG s He)) as Gh.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid p HAR Hin) as (F1 & _ & _).
  pose proof (Z.div_pos (frame_addr lyc cid p) 8 ltac:(lia) ltac:(lia)).
  unfold in_zr in Hs. cbn [fst snd] in Hs.
  unfold shadow_addr, SHADOW_OFF in Hs. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Gh. lia.
Qed.

(* Equal views give equal image bytes; a byte array is kept by a memory whose view keeps its bytes. *)
Lemma onann_mbyte_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
  intros H H' m m' a E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a) as [x|], (mbyte segs (mrestrict H m) a) as [y|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma onann_garr8_view : forall (H H' : word -> bool) (m m' : word -> option byte) p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview segs H' m' a = aview segs H m a) ->
  garr8 segs (mrestrict H m) p l -> garr8 segs (mrestrict H' m') p l.
Proof.
  intros H H' m m' p l E G. apply (garr8_frame segs (mrestrict H m) (mrestrict H' m') p l G).
  intros a Ha. apply onann_mbyte_aview. exact (E a Ha).
Qed.

Lemma onann_garr8_cons : forall (mm : word -> option byte) p x l,
  garr8 segs mm p (x :: l) -> garr8 segs mm p [x] /\ garr8 segs mm (p + 1) l.
Proof.
  intros mm p x l G. destruct (proj1 (garr8_app segs mm p [x] l) G) as [G1 G2].
  split; [exact G1|]. replace (p + 1) with (p + Z.of_nat (length [x])) by (cbn; lia). exact G2.
Qed.

(* A one-byte array read through the view. *)
Lemma onann_view1 : forall (H : word -> bool) (m : word -> option byte) a (x : byte),
  garr8 segs (mrestrict H m) a (map (fun y : byte => bv_unsigned y) [x]) -> aview segs H m a = Some (bv_unsigned x).
Proof.
  intros H m a x G.
  pose proof (garr8_mbyte segs (mrestrict H m) a _ 0 G ltac:(cbn; lia)) as E.
  cbn [nth map Z.of_nat] in E. rewrite Z.add_0_r in E.
  unfold aview. rewrite E. cbn [option_map]. f_equal.
  apply AF0x.unsigned_lit_small8. exact (proj2 (G 0%nat ltac:(cbn; lia))).
Qed.

(* An eight-byte array of the bytes le8 v read through the view (lib/A/AF0x.v val_mem_rdword). *)
Lemma onann_rdword_le8 : forall (H : word -> bool) (m : word -> option byte) a v, 0 <= v < 2 ^ 64 ->
  garr8 segs (mrestrict H m) a (map (fun x : byte => bv_unsigned x) (LMem.le8 (Z_to_bv 64 v))) ->
  rdword (aview segs H m) a = Some v.
Proof.
  intros H m a v Hr G. apply (AF0x.val_mem_rdword H m a v Hr). intros k Hk.
  assert (Hk' : (k < length (map (fun x : byte => bv_unsigned x) (LMem.le8 (Z_to_bv 64 v))))%nat)
    by (rewrite length_map, LMem.length_le8; exact Hk).
  rewrite (garr8_mbyte segs _ a _ k G Hk'). f_equal. f_equal.
  pose proof (LB.decode_leafb_le8_byte v k Hk) as E. change (LMem.wa v) with (Z_to_bv 64 v) in E.
  destruct (nth_error (LMem.le8 (Z_to_bv 64 v)) k) as [x|] eqn:Ex; [|discriminate E].
  cbn [option_map] in E. injection E as E.
  apply nth_error_nth with (d := Z_to_bv 8 0) in Ex.
  rewrite (nth_indep _ 0 ((fun x : byte => bv_unsigned x) (Z_to_bv 8 0))) by exact Hk'.
  rewrite map_nth, Ex. exact E.
Qed.

(* f's 64 bytes as the parse left them (fr_code b = 0): 30 bytes, then cmd, ncmds, body and body_len
   (lib/Prog/diginet_frame_parse_c.v parse_cells). *)
Lemma onann_fbytes_split : forall buf (b fj : list byte), (30 <= length b)%nat -> length fj = 64%nat ->
  exists pre post : list byte, length pre = 30%nat /\
  LCells.cells_bytes (PParse.parse_cells buf b fj) =
    pre ++ DSpec.b8 (DSpec.fr_cmd b) :: DSpec.b8 (DSpec.fr_ncmds b) ::
      (LMem.le8 (Z_to_bv 64 (buf + 30)) ++ LMem.le8 (Z_to_bv 64 (DSpec.fr_body_len b))) ++ post.
Proof.
  intros buf b fj Hb Hfj.
  exists (DSpec.fr_dst b ++ DSpec.fr_src b ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_ethertype b)) ++
          firstn 2 (skipn 14 fj) ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_numbytes b)) ++
          LMem.le2 (Z_to_bv 64 (DSpec.fr_sum b)) ++ LMem.le4 (Z_to_bv 64 (DSpec.fr_send b)) ++
          LMem.le4 (Z_to_bv 64 (DSpec.fr_ack b)) ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_retry b))).
  exists (LMem.le8 (Z_to_bv 64 (DSpec.fr_pad_len b)) ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_body_sum b)) ++
          [DSpec.b8 (if DSpec.fr_sum b =? DSpec.fr_body_sum b then 1 else 0)] ++ skipn 59 fj ++ []).
  split.
  - unfold DSpec.fr_dst, DSpec.fr_src.
    rewrite !length_app, !length_firstn, !length_skipn, !LMem.length_le2, !LMem.length_le4. lia.
  - unfold PParse.parse_cells. cbn [LCells.cells_bytes LCells.cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma onann_f_split : forall (mm : word -> option byte) fp buf (b fj : list byte),
  DSpec.fr_code b = 0 -> length fj = 64%nat ->
  garr8 segs mm fp (frame_f_bytes buf b fj) ->
  garr8 segs mm (fp + 30) (map (fun x : byte => bv_unsigned x) [DSpec.b8 (DSpec.fr_cmd b)]) /\
  garr8 segs mm (fp + 32) (map (fun x : byte => bv_unsigned x)
    (LMem.le8 (Z_to_bv 64 (buf + 30)) ++ LMem.le8 (Z_to_bv 64 (DSpec.fr_body_len b)))).
Proof.
  intros mm fp buf b fj Hc Hfj G.
  destruct (DSpec.fr_code_ok b Hc) as (L30 & _).
  unfold frame_f_bytes, frame_f_cells in G. rewrite Hc in G. cbn [Z.eqb] in G.
  destruct (onann_fbytes_split buf b fj L30 Hfj) as (pre & post & Lp & E).
  rewrite E, map_app in G. apply garr8_app in G. destruct G as [_ G].
  rewrite length_map, Lp in G. cbn [map] in G.
  apply onann_garr8_cons in G. destruct G as [G30 G].
  apply onann_garr8_cons in G. destruct G as [_ G].
  rewrite map_app in G. apply garr8_app in G. destruct G as [G32 _].
  split.
  - exact G30.
  - replace (fp + 32) with (fp + Z.of_nat 30 + 1 + 1) by (cbn; lia). exact G32.
Qed.

(* At a later state whose written range lies in G (a call state or a cut of the walk): f's 64 bytes are the entry's,
   readable (decode_rd_ok), the byte at f + 30 is fr_cmd b and the words at f + 32 and f + 40 are buf + 30 (the
   body) and fr_body_len b; the body has fr_body_len b bytes. *)
Lemma onann_f30 : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 slo shi (E : Z -> Prop)
    (regs : bvmap 5 word) (K fp buf : Z) (b fj : list byte),
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, E a -> inG TG.G_HARNESS a) ->
  trans_dframe_at B lyc Sc W memc regs K fp buf b fj ->
  (forall a, fp <= a < fp + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  decode_rd_ok W2 mem2 fp 64 /\
  aview segs (w_H W2) mem2 (fp + 30) = Some (DSpec.fr_cmd b) /\
  rdword (aview segs (w_H W2) mem2) (fp + 32) = Some (buf + 30) /\
  rdword (aview segs (w_H W2) mem2) (fp + 40) = Some (DSpec.fr_body_len b) /\
  0 <= DSpec.fr_body_len b /\ length (DSpec.fr_body b) = Z.to_nat (DSpec.fr_body_len b).
Proof.
  intros LAWS lyc Sc W memc mdc W2 mem2 slo shi E regs K fp buf b fj HAR HK HEG HD.
  destruct HD as (Hc & Hb0 & Gb & Hsb & Hob & HbG & Hf0 & Hf8 & Hfj & Gf & HF & Hrd & Hof).
  unfold FRAME_F_SIZE in HF, Hrd.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (onann_body_len b Hc) as (Bl0 & Bl1 & Bl2).
  assert (KV : forall a, fp <= a < fp + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct HK as (_ & _ & _ & K4 & _). destruct HF as (cid & p & Hin & F1 & F2).
    apply (K4 cid p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia|].
    intro He. apply (frm_img segs B LAWS lyc Sc W memc mdc cid p a HAR Hin); [lia|].
    exact (trans_g_img a (HEG a He)). }
  pose proof (onann_ks LAWS lyc Sc W memc mdc W2 mem2 slo shi E HAR HK HEG) as KS.
  pose proof (decode_rd_ok_fake_kept B LAWS lyc Sc W W2 memc mem2 mdc fp 64 HAR HF Hrd ltac:(lia) KV KS) as Hrd2.
  (* buf's placement bounds the two words *)
  destruct (DSpec.fr_code_ok b Hc) as (L30 & _).
  pose proof (trans_src_ok_place B LAWS lyc Sc W memc mdc buf (Z.of_nat (length b)) HAR Hsb ltac:(lia)) as Pl.
  assert (Rbuf : 0 <= buf + 30 < 2 ^ 64) by (destruct Pl as [Pl|Pl]; lia).
  assert (Rbl : 0 <= DSpec.fr_body_len b < 2 ^ 64) by (destruct Pl as [Pl|Pl]; lia).
  assert (Rc : 0 <= DSpec.fr_cmd b < 2 ^ 8).
  { unfold DSpec.fr_cmd, DSpec.at8, DSpec.bz. pose proof (bv_unsigned_in_range 8 (nth 28 b (DSpec.b8 0))) as R.
    unfold bv_modulus in R. exact R. }
  destruct (onann_f_split _ fp buf b fj Hc Hfj Gf) as [G30 G32].
  assert (G30' : garr8 segs (mrestrict (w_H W2) mem2) (fp + 30)
                   (map (fun x : byte => bv_unsigned x) [DSpec.b8 (DSpec.fr_cmd b)])).
  { apply (onann_garr8_view (w_H W) (w_H W2) memc mem2 (fp + 30) _); [|exact G30].
    intros a Ha. cbn [map length] in Ha. change (Z.of_nat 1) with 1 in Ha. apply KV. lia. }
  assert (G32' : garr8 segs (mrestrict (w_H W2) mem2) (fp + 32) (map (fun x : byte => bv_unsigned x)
                   (LMem.le8 (Z_to_bv 64 (buf + 30)) ++ LMem.le8 (Z_to_bv 64 (DSpec.fr_body_len b))))).
  { apply (onann_garr8_view (w_H W) (w_H W2) memc mem2 (fp + 32) _); [|exact G32].
    intros a Ha. rewrite length_map, length_app, !LMem.length_le8 in Ha. change (Z.of_nat (8 + 8)) with 16 in Ha.
    apply KV. lia. }
  rewrite map_app in G32'. apply garr8_app in G32'. destruct G32' as [Gw1 Gw2].
  rewrite length_map, LMem.length_le8 in Gw2. change (Z.of_nat 8) with 8 in Gw2.
  replace (fp + 32 + 8) with (fp + 40) in Gw2 by lia.
  split; [exact KV|]. split; [exact Hrd2|]. split.
  { rewrite (onann_view1 (w_H W2) mem2 (fp + 30) _ G30'). unfold DSpec.b8.
    rewrite AF0x.unsigned_lit_small8 by lia. reflexivity. }
  split; [exact (onann_rdword_le8 (w_H W2) mem2 (fp + 32) (buf + 30) Rbuf Gw1)|].
  split; [exact (onann_rdword_le8 (w_H W2) mem2 (fp + 40) (DSpec.fr_body_len b) Rbl Gw2)|].
  split; [exact Bl0 | exact Bl2].
Qed.

(* The frame bytes b at buf at a later state of the walk (onann_src_kept at q = buf, n = length b: buf is off G and
   outside the call's window): placed, their bytes the entry's, b there. *)
Lemma onann_buf_kept : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 pos (regs : bvmap 5 word)
    (fp buf : Z) (b fj : list byte) (E : Z -> Prop),
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (ONANN_CID, pos) :: frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - ONANN_STK) (spZ regs) E ->
  (forall a, E a -> inG TG.G_HARNESS a) ->
  trans_dframe_at B lyc Sc W memc regs ONANN_STK fp buf b fj ->
  trans_src_ok B ly2 S2 W2 mem2 buf (Z.of_nat (length b)) /\
  (forall a, buf <= a < buf + Z.of_nat (length b) -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  garr8 segs (mrestrict (w_H W2) mem2) buf (TW.zs b).
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos regs fp buf b fj E HAR HAR2 Hfr Hperm Hfa Elo Ehi
    HK HEG HD.
  destruct HD as (Hc & Hb0 & Gb & Hsb & Hob & HbG & _).
  destruct (onann_src_kept B LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos (spZ regs - ONANN_STK) (spZ regs)
    E buf (Z.of_nat (length b)) HAR HAR2 Hfr Hperm Hfa Elo Ehi HK HEG HbG Hob Hsb ltac:(lia)) as [Hs2 KV].
  split; [exact Hs2|]. split; [exact KV|].
  apply (onann_garr8_view (w_H W) (w_H W2) memc mem2 buf (TW.zs b)); [|exact Gb].
  intros a Ha. unfold TW.zs in Ha. rewrite length_map in Ha. exact (KV a Ha).
Qed.

End k.
