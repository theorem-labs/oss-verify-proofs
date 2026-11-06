(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AF0x.v, with its module paths and module names changed; 708 of its 766 lines of code are new or changed and 514 lines of the source are left out. *)
(* io_send_seg_entry: the entry stretch of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f, entry
   0x82ffc = TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v), from the entry to the cut IOS_SRF
   (0x83054, the return of spec_read_frame; lib/B/Prog/io_send_seg_cut.v). It proves io_send_seg_cut.v
   ios_entry_stmt.

   The code (io_send_cg.v header, lines 79-89; listing slots IOS_AT 0x0 .. IOS_AT 0x54 of
   lib/B/Prog/DgnTransportBList.v):
     0x82ffc - 0x83020  sp = sp - 160 (IOSEND_FRAME); ra at sp + 152, s0 .. s7 at sp + 144 .. sp + 88 (IOS_SAVED);
     0x83024 - 0x83028  s0 = a2 = len, s1 = a1 = p;
     0x8302c - 0x83038  a0 = the GOT word 0xa3cf0 (object 1), s4 = the cell 0xac678 it points to (object 95): the
                        shadow base SHADOW_OFF;
     0x8303c - 0x83040  s3 = the 1-byte unsigned load of g_fail_next (object 25 = TB_g_fail_next, through the high
                        part hi 50; no instrumented check), then `sb zero, -660(a1)`: the 1-byte store of 0 there
                        (hi 50 - 660 is object 25);
     0x83044 - 0x83050  a2 = sp + 8, a0 = p, a1 = len, the call of spec_read_frame (transportb_sigma
                        TB_spec_read_frame), return address 0x83054.
   No instrumented check, no branch to the trap word and no error path is on this stretch.

   The walk, as image A's lib/A/Prog/io_send_seg_entry.v walks its first run (image A calls __asan_memset where
   image B calls spec_read_frame):
     run 1 (0x82ffc .. 0x83050)  a run of TransportGRunB.v paj_run_x over the caller's G journal, from the symbolic
                                 state ient_regions (the 160-byte frame below sp, the shadow base's GOT word and cell,
                                 and the byte of g_fail_next, whose chunk is the world's byte as atom 33, read from
                                 the world relation by TWorldG.v tw_read_val at the row TMAP_B_g_fail_next) and the
                                 empty shadow entry; its write right awr_ok_x: the frame is a byte of the caller's
                                 window (awr_byte), the two image cells have no writable byte, g_fail_next's byte is a
                                 byte of G;
     spec_read_frame (p, len, sp + 8)  its G-form contract (spec_read_frame_cg.v transport_spec_read_frame_cg, the
                                 9th conjunct of ios_laws) at the run's journal. Its premises: the frame's bytes and
                                 placement kept by the run (it writes only its frame and g_fail_next's byte, apart from
                                 the frame: decode_off_win, iosend_frame_at); decode_off_win at SRF_STK; the frame apart
                                 from the struct (the struct lies in io_send's window, the frame outside it); fp = sp + 8
                                 8-aligned; the struct's write right (transport_twr_ok_g_intro: awr_byte of the window)
                                 and decode_rd_ok (DgnTransportBCg.v stack_zshadow_ra: the machine stack's shadow is 0);
                                 not in G (the stack lies above G). Its post (TransportGCg.v transport_cg_post_out with
                                 the out cell [(sp + 8, 80)]) is folded into io_send's running kept fact by
                                 TransportGCg.v dk_kept_trans_out_g (the struct lies in io_send's own window), as image
                                 A's io_send_seg_tail.v folds check_latest_sent's out cell (ios_cls_at), then shrunk
                                 back to iosend_wr (ient_kept_shrink: the struct lies above alloc_ceiling).

   THE CUT (io_send_seg_cut.v ios_at_srf, at the state (ly2, S2, W2, mem2, md2) and registers regs2 the call
   returns):
     - ios_cur: the post's journal (no event), frames and blocks, meter, and the folded kept fact;
     - ios_saved: the nine words the run stored, kept by the call (they lie above its window and past the struct);
     - ios_regs with fail = g_fail_next Bw and s8 .. s11: the run's registers, kept by the call (aregs_preserved);
     - trans_sframe_at at sp + 8: the post's X (the 80 bytes are TContract.sf_bytes p (rf frame), srf_f_rf), field by
       field (ient_rf_sframe: each field the put chunk at its offset, its value in range by io_send_seg_frm.v
       ios_fields at code SPEC_OK);
     - garr8 and trans_src_ok of the frame: DgnTransportBCg.v trans_src_ok_acall_g with the post's kept fact folded at
       the call memory and its gx_kept;
     - tw_at at ios_B0 Bw: TWorldG.v tw_write of the run's store, then the post's gx_kept (TWorldB.v tw_kept_GB). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_cg check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_frm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg io_send_seg_cut io_send_seg_world.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require TContract.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.

(* ------------------------------------------------------------------ *)
(* The struct spec_frame spec_read_frame leaves                        *)
(* ------------------------------------------------------------------ *)

(* Reads of a concatenation (lib/Prog/T/io_send_sf.v sf_u_at_app_l / _r / sf_u_at_fld). *)
Lemma ient_u_at_app_l : forall (x y : list byte) (k : Z) (n : nat), 0 <= k -> k + Z.of_nat n <= Z.of_nat (length x) ->
  TW.u_at (x ++ y) k n = TW.u_at x k n.
Proof.
  intros x y k n Hk Hn. unfold TW.u_at, TW.sub. f_equal.
  rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length x - Z.to_nat k))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma ient_u_at_app_r : forall (x y : list byte) (k : Z) (n : nat), Z.of_nat (length x) <= k ->
  TW.u_at (x ++ y) k n = TW.u_at y (k - Z.of_nat (length x)) n.
Proof.
  intros x y k n Hk. unfold TW.u_at, TW.sub. f_equal.
  rewrite skipn_app.
  assert (E : skipn (Z.to_nat k) x = []) by (apply skipn_all2; lia).
  rewrite E, app_nil_l.
  replace (Z.to_nat (k - Z.of_nat (length x))) with (Z.to_nat k - length x)%nat by lia.
  reflexivity.
Qed.

Lemma ient_u_at_fld : forall (y : list byte) (n : nat) (v k : Z), k = 0 -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  TW.u_at (TW.put n v ++ y) k n = v.
Proof.
  intros y n v k Hk Hv. subst k.
  rewrite ient_u_at_app_l by (rewrite ?TWL.length_put; lia).
  rewrite TWL.u_at_put. apply Z.mod_small. exact Hv.
Qed.

Ltac ient_len := rewrite ?TWL.length_put, ?repeat_length; lia.
Ltac ient_field :=
  repeat (rewrite ient_u_at_app_r by ient_len);
  apply ient_u_at_fld; [ient_len | assumption].

Lemma ient_sf_len : forall (fa : Z) (f : DSpec.spec_frame), length (TCt.sf_bytes fa f) = 80%nat.
Proof.
  intros fa f. unfold TCt.sf_bytes.
  rewrite !length_app, !TWL.length_put, !repeat_length. reflexivity.
Qed.

(* The 80 bytes sf_bytes fa f at fp hold the struct field by field when every field is in its C range
   (lib/Prog/T/io_send_sf.v sf_bytes_sframe, at the walk's image view). *)
Lemma ient_sframe : forall (W : world tfibsegs) (mem : word -> option byte) (fp fa : Z) (f : DSpec.spec_frame),
  0 < fp -> fp mod 8 = 0 ->
  garr8 tfibsegs (mrestrict (w_H W) mem) fp (TW.zs (TCt.sf_bytes fa f)) ->
  - 2 ^ 31 <= DSpec.sf_code f < 2 ^ 31 ->
  0 <= TCt.sf_ptr fa f (DSpec.sf_dst f) < 2 ^ 64 ->
  0 <= TCt.sf_ptr fa f (DSpec.sf_src f) < 2 ^ 64 ->
  0 <= DSpec.sf_ethertype f < 2 ^ 16 ->
  0 <= DSpec.sf_numbytes f < 2 ^ 16 ->
  0 <= DSpec.sf_sum f < 2 ^ 16 ->
  0 <= DSpec.sf_retry f < 2 ^ 16 ->
  0 <= DSpec.sf_send f < 2 ^ 32 ->
  0 <= DSpec.sf_ack f < 2 ^ 32 ->
  0 <= DSpec.sf_cmd f < 2 ^ 8 ->
  0 <= DSpec.sf_ncmds f < 2 ^ 8 ->
  0 <= TCt.sf_ptr fa f (DSpec.sf_body f) < 2 ^ 64 ->
  0 <= DSpec.sf_body_len f < 2 ^ 64 ->
  0 <= DSpec.sf_pad_len f < 2 ^ 64 ->
  0 <= DSpec.sf_body_sum f < 2 ^ 16 ->
  trans_sframe_at W mem fp fa f.
Proof.
  intros W mem fp fa f Hfp Hal HB Hc Hdst Hsrc Heth Hnum Hsum Hret Hsend Hack Hcmd Hncmds Hbody Hblen Hplen Hbsum.
  split; [exact Hfp|]. split; [exact Hal|].
  exists (TCt.sf_bytes fa f). split; [exact HB|]. split; [apply ient_sf_len|].
  split.
  - unfold TW.s32_at, TCt.sf_bytes.
    rewrite ient_u_at_app_l by ient_len.
    rewrite TWL.u_at_put. change (8 * Z.of_nat 4) with 32.
    change (DSpec.sf_code f mod 2 ^ 32) with (bv_wrap 32 (DSpec.sf_code f)). rewrite bv_swrap_wrap.
    apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
  - unfold TCt.sf_bytes.
    repeat match goal with |- _ /\ _ => split end; ient_field.
Qed.

(* The struct of the parse rf frame, when check_sent_frame's model call succeeds (the parse code is SPEC_OK, and the
   frame ends below 2 ^ 64): every field is in its range (io_send_seg_frm.v ios_fields; ios_len_lt32). *)
Lemma ient_rf_sframe : forall (W : world tfibsegs) (mem : word -> option byte) (fp p : Z) (frame Bm B' : list byte),
  TC.check_sent_frame_m Bm frame = Some (B', tt) ->
  0 < fp -> fp mod 8 = 0 -> 0 <= p -> p + Z.of_nat (length frame) <= 2 ^ 64 ->
  garr8 tfibsegs (mrestrict (w_H W) mem) fp (TW.zs (TCt.sf_bytes p (TC.rf frame))) ->
  trans_sframe_at W mem fp p (TC.rf frame).
Proof.
  intros W mem fp p frame Bm B' HC Hfp Hal Hp Hpl HB.
  pose proof (ios_sf_code _ _ _ HC) as HOK.
  pose proof (ios_len_lt32 _ _ _ HC) as HL32.
  pose proof (ios_len60 _ _ _ HC) as HL60.
  destruct (ios_fields frame HOK) as (HL30 & _ & HNB1 & HNB2 & Fdst & Fsrc & Fet & Fnb & Fsum & Fsend & Fack & Fretry
    & Fcmd & Fncmds & Fbody & Fblen & Fpad & Fbsum).
  assert (EP : forall off, TCt.sf_ptr p (TC.rf frame) off = p + off).
  { intros off. unfold TCt.sf_ptr. rewrite HOK, Z.eqb_refl. reflexivity. }
  pose proof (DSpec.be16_range frame 14) as Rnb.
  apply (ient_sframe W mem fp p (TC.rf frame) Hfp Hal HB).
  - rewrite HOK. unfold DSpec.SPEC_OK. lia.
  - rewrite EP, Fdst. lia.
  - rewrite EP, Fsrc. lia.
  - rewrite Fet. unfold DSpec.fr_ethertype. apply DSpec.be16_range.
  - rewrite Fnb. unfold DSpec.fr_numbytes. apply DSpec.be16_range.
  - rewrite Fsum. unfold DSpec.fr_sum. apply DSpec.be16_range.
  - rewrite Fretry. unfold DSpec.fr_retry. apply DSpec.be16_range.
  - rewrite Fsend. unfold DSpec.fr_send. apply DSpec.be32_range.
  - rewrite Fack. unfold DSpec.fr_ack. apply DSpec.be32_range.
  - rewrite Fcmd. unfold DSpec.fr_cmd. apply DSpec.at8_range.
  - rewrite Fncmds. unfold DSpec.fr_ncmds. apply DSpec.at8_range.
  - rewrite EP, Fbody. lia.
  - rewrite Fblen. unfold DSpec.fr_body_len. unfold DSpec.fr_numbytes in *. lia.
  - rewrite Fpad. unfold DSpec.fr_pad_len, DSpec.fr_body_len. unfold DSpec.fr_numbytes in *. lia.
  - rewrite Fbsum. unfold DSpec.fr_body_sum. apply DSpec.sum16_range.
Qed.

(* ------------------------------------------------------------------ *)
(* Bytes and words                                                     *)
(* ------------------------------------------------------------------ *)

(* B/YF0x.v le_bytes8_sum / unsigned_lit_small8 / val_mem_rdword (the YF* files may not build). *)
Lemma ient_le_bytes8_sum : forall z, 0 <= z < 2 ^ 64 ->
  let b := fun k => YG0f.le_byte z 8 k in
  b 0%nat + 256 * (b 1%nat + 256 * (b 2%nat + 256 * (b 3%nat + 256 * (b 4%nat + 256 * (b 5%nat + 256 * (b 6%nat +
    256 * b 7%nat)))))) = z.
Proof.
intros z Hz. cbn beta. unfold YG0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
change (2 ^ (8 * Z.of_nat 2)) with (256 * 256).
change (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256). change (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256).
rewrite Z.div_1_r. rewrite <- !Z.div_div by lia.
assert (H7 : z / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256).
{ change (2 ^ 64) with (256 * 256 * 256 * 256 * 256 * 256 * 256 * 256) in Hz.
  repeat (apply Z.div_lt_upper_bound; [lia|]). lia. }
rewrite (Z.mod_small (z / 256 / 256 / 256 / 256 / 256 / 256 / 256))
  by (split; [repeat (apply Z.div_pos; [|lia]); lia | exact H7]).
pose proof (Z.div_mod z 256 ltac:(lia)) as E0.
pose proof (Z.div_mod (z / 256) 256 ltac:(lia)) as E1.
pose proof (Z.div_mod (z / 256 / 256) 256 ltac:(lia)) as E2.
pose proof (Z.div_mod (z / 256 / 256 / 256) 256 ltac:(lia)) as E3.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E4.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E5.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E6.
lia.
Qed.

Lemma ient_unsigned_lit_small8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hz.
Qed.

Lemma ient_val_mem_rdword : forall (H : word -> bool) mem a v,
  0 <= v < 2 ^ 64 -> val_mem tfibsegs (mrestrict H mem) a 8 v -> rdword (aview tfibsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hm. unfold rdword, aview.
assert (B : forall k, (k < 8)%nat ->
  mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat k) = Some (Z_to_bv 8 (YG0f.le_byte v 8 k)))
  by (intros k Hk; exact (Hm k Hk)).
assert (R : forall k, 0 <= YG0f.le_byte v 8 k < 256) by (intros k; unfold YG0f.le_byte; apply Z.mod_pos_bound; lia).
replace a with (a + Z.of_nat 0) at 1 by lia.
replace (a + 1) with (a + Z.of_nat 1) by lia. replace (a + 2) with (a + Z.of_nat 2) by lia.
replace (a + 3) with (a + Z.of_nat 3) by lia. replace (a + 4) with (a + Z.of_nat 4) by lia.
replace (a + 5) with (a + Z.of_nat 5) by lia. replace (a + 6) with (a + Z.of_nat 6) by lia.
replace (a + 7) with (a + Z.of_nat 7) by lia.
rewrite !B by lia. cbn [option_map]. rewrite !ient_unsigned_lit_small8 by apply R.
f_equal. apply ient_le_bytes8_sum. exact Hv.
Qed.

(* An aview equality is an mbyte equality of the restricted memories. *)
Lemma ient_mbyte_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H' m' a = aview tfibsegs H m a ->
  mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [b1|]; destruct (mbyte tfibsegs (mrestrict H m) a) as [b2|];
  cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* garr8 at a later memory that keeps the range's bytes. *)
Lemma ient_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) p l,
  garr8 tfibsegs (mrestrict H m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs H' m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H' m') p l.
Proof.
intros H H' m m' p l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros i Hi. assert (Ei : i = 0%nat) by lia. subst i.
rewrite (ient_mbyte_of_aview H H' m m' (p + Z.of_nat j + Z.of_nat 0)).
- exact (Hv 0%nat Hi).
- apply Hk. lia.
Qed.

(* A visible garr8 range. *)
Lemma ient_garr8_vis : forall (H : word -> bool) (m : word -> option byte) q l,
  garr8 tfibsegs (mrestrict H m) q l -> forall a, q <= a < q + Z.of_nat (length l) -> aview tfibsegs H m a <> None.
Proof.
intros H m q l HG a Ha. assert (Hj : (Z.to_nat (a - q) < length l)%nat) by lia.
destruct (HG _ Hj) as [HV _]. specialize (HV 0%nat ltac:(lia)).
replace a with (q + Z.of_nat (Z.to_nat (a - q)) + Z.of_nat 0) by lia.
unfold aview. rewrite HV. discriminate.
Qed.

(* A saved word: the 8-byte chunk of a register's value, read as a word of the view. *)
Lemma ient_save_rd : forall E (H : word -> bool) m sp off e (v : word),
  YP09.chunk_ok tfibsegs E (mrestrict H m) sp (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = v ->
  rdword (aview tfibsegs H m) (sp + off) = Some (bv_unsigned v).
Proof.
intros E H m sp off e v Hc He.
pose proof (bv_unsigned_in_range 64 v) as Rv. change (bv_modulus 64) with (2 ^ 64) in Rv.
apply ient_val_mem_rdword; [exact Rv|].
exact (val_of_chunk_ok tfibsegs E (mrestrict H m) sp off 8%N e (bv_unsigned v) Hc
  ltac:(rewrite He; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Lemma ient_inG1 : forall q n a, inG [(q, n)] a <-> q <= a < q + n.
Proof. intros q n a. unfold inG. rewrite Exists_cons, Exists_nil. unfold in_zr. cbn [fst snd]. tauto. Qed.

(* The world after the store of 0 at g_fail_next, in TWorldG.v tw_write's form. *)
Lemma ient_B0 : forall Bw, ios_B0 Bw = TW.upd Bw (TW.OFF_g_fail_next + 0) (TW.put 1 0).
Proof. intros Bw. unfold ios_B0, TW.set_g_fail_next. rewrite Z.add_0_r. reflexivity. Qed.

(* g_fail_next's byte is a byte of G. *)
Lemma ient_inG_fail : forall a, TB_g_fail_next <= a < TB_g_fail_next + 1 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. exact (ios_inG_row _ _ _ a TMAP_B_g_fail_next Ha). Qed.

(* An apresent byte is visible. *)
Lemma ient_vis_of_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base, 33 the byte of g_fail_next. Regions: the 160-byte
   frame below sp, the shadow base's GOT word (object 1) and its cell (object 95), and the byte of g_fail_next
   (object 25), writable (a byte of G), whose chunk is atom 33. The load of g_fail_next names object 25 (PLdHi); the
   store after it is a plain word, `sb zero, -660(a1)`, with a1 the high part A_HI 50 of the same address: the alias
   (A_HI 50) - 660 = (A_OBJ 25) + 0 lets the run find the region (ient_alias). *)
Definition ient_fail_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 25)) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition ient_regions : smem := [stack_region IOSEND_FRAME; got_regionP; bcell_regionP 32; ient_fail_region].
Definition ient_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 255 0);
           (A_OBJ 25, mkAF TB_g_fail_next TB_g_fail_next 5)] [] [(SOff (A_HI 50) (-660), SOff (A_OBJ 25) 0)].
Definition ss_ient : sstate := mkSS AF_io_send sr_atoms ient_regions None ient_facts.
(* No instrumented check on the stretch: the empty shadow entry; the shadow base of the token engine. *)
Definition IENT_SH : list shent := [].
Definition IENT_Bx : sv := SOff 32 0.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ient_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ient_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac ient_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of the run: the frame below sp (inside the caller's stack window), the two read-only image
   regions (no writable byte), and g_fail_next's byte (a byte of G). *)
Ltac ient_awr UspE U25E :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite UspE in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25E in Ha; apply ient_inG_fail; lia |];
  apply awr_ok_x_nil.

(* One saved word of IOS_SAVED, from the frame region's chunks HC (forall c, In c cs -> chunk_ok ..) and the
   valuation's registers EE. *)
Ltac ient_save HC EE :=
  lazymatch goal with |- rdword (aview _ _ _) (?sp - ?d) = Some (bv_unsigned (YK11.getr _ (Z_to_bv 5 ?r))) =>
    replace (sp - d) with (sp + - d) by lia;
    eapply ient_save_rd;
    [ apply HC; cbn [In]; repeat (first [left; reflexivity | right])
    | lazymatch goal with |- sv_denot _ (SOff ?n 0) = _ =>
        cbn [sv_denot]; rewrite (EE n (Z_to_bv 5 r) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ]
  end.

Section ientw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma ient_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  VAL (A_OBJ 25) = TB_g_fail_next /\ VAL (A_HI 50) = TB_g_fail_next + 660 /\ BASE = transportb_text.
Proof. vm_compute. repeat split. Qed.

(* The return address of the call of spec_read_frame is the cut IOS_SRF. *)
Lemma ient_pc : Z_to_bv 64 (BASE + 7604) = w64 (transportb_text + IOS_SRF).
Proof. unfold w64. f_equal; try (vm_compute; reflexivity). Qed.

(* The two image regions hold what transport_cells says they hold, at any AR state. *)
Lemma ient_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct ient_vals as (V1 & V95 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R95 : 0 <= VAL (A_OBJ 95) < 2 ^ 47) by (rewrite V95; unfold FCells.CELL_K; lia).
  unfold got_regionP, bcell_regionP, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split.
  - rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
    [cbn [sv_denot]; rewrite E95, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V1, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base and the byte of g_fail_next. *)
Definition ient_E (regs : bvmap 5 word) (fb : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 fb]).

(* The alias of the run's facts: the high part of g_fail_next's address less the store's offset is the object. *)
Lemma ient_alias : forall E, img_env VAL A_LIM E ->
  sv_denot E (SOff (A_HI 50) (-660)) = sv_denot E (SOff (A_OBJ 25) 0).
Proof.
intros E HE. cbn [sv_denot].
rewrite (HE (A_HI 50) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
rewrite (HE (A_OBJ 25) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
f_equal; try (vm_compute; reflexivity).
Qed.

(* The entry state and its (empty) shadow entry. *)
Lemma ient_entry : forall ly S (W : world segs) regs mem md fb,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - IOSEND_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> 0 <= fb < 256 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TB_g_fail_next + 0) 1 fb ->
  st_ok_pi segs VAL (ient_E regs fb) ss_ient
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_io_send)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs IENT_Bx IENT_SH (ient_E regs fb) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md fb HCELLS HAR Hpres Hsp Hsp16 Hf Vf.
  assert (EF : TB_g_fail_next = 0x5deda0) by reflexivity.
  assert (FF : IOSEND_FRAME = 160) by reflexivity.
  assert (E2 : ew (ient_E regs fb) 2 = YK11.getr regs 2) by (unfold ient_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew (ient_E regs fb) 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E32 : ew (ient_E regs fb) 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold ient_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew (ient_E regs fb) 33 = Z_to_bv 64 fb)
    by (unfold ient_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (U33 : bv_unsigned (ew (ient_E regs fb) 33) = fb) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (EOB : forall j, (j < 97)%nat -> ew (ient_E regs fb) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold ient_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (ient_img_ok ly S W mem md (ient_E regs fb) HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 95%nat ltac:(lia)) E32)
    as [RG RC].
  destruct ient_vals as (V1 & V95 & V25 & _).
  assert (VB : forall n v0, ew (ient_E regs fb) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (ient_E regs fb) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (B25 : base_val (ient_E regs fb) (Some (A_OBJ 25)) = TB_g_fail_next)
    by (apply VB; [rewrite (EOB 25%nat ltac:(lia)), V25; reflexivity | rewrite EF; lia]).
  assert (U25 : bv_unsigned (ew (ient_E regs fb) (A_OBJ 25)) = TB_g_fail_next) by exact B25.
  split.
  - rewrite restrict_mkst_fx. unfold ss_ient, ient_regions.
    apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC |]]].
      * unfold stack_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. rewrite FF.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * apply Forall_cons; [|apply Forall_nil].
        unfold ient_fail_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite B25. split; [rewrite EF; lia|]. split; [rewrite EF; lia|]. split.
        -- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_g_fail_next + o) G_HARNESS_B_rw).
           apply ient_inG_fail. lia.
        -- constructor; [|constructor].
           apply (chunk_ok_val segs (ient_E regs fb) _ TB_g_fail_next 0 1 (SOff 33 0) fb);
           [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Vf].
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, ient_fail_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (EOB 95%nat ltac:(lia))) by (rewrite V95; unfold FCells.CELL_K; lia).
      rewrite B25.
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite V1, V95. unfold FCells.GOT_CELL_K, FCells.CELL_K in *. rewrite FF, EF.
      repeat split; first [exact I | lia].
    + unfold ient_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U25, U33, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I;
        first [lia | rewrite EF; reflexivity | apply ient_alias; unfold ient_E; apply Eimg_env].
  - unfold sh_ok, IENT_SH. constructor.
Qed.

(* What a journal state says of its layout: AR, and the side-stack frames and the machine stack where the journal's
   start state has them (lib/A/Prog/io_send_seg_tail.v ios_jlayout). *)
Lemma ient_jlayout : forall G STK sp0 FP ly S (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem2 md2 k,
  ajournal_gx G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
  @AR rc segs B ly2 S2 W2 mem2 md2 /\ (forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos) /\
  ly_stk_lo ly2 = ly_stk_lo ly /\ ly_stk_hi ly2 = ly_stk_hi ly.
Proof.
intros G STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & HF & _ & _ & _ & Hlo & Hhi & _).
split; [exact HAR|]. split; [intros cid pos; unfold frame_addr; rewrite HF; reflexivity|].
split; [exact Hlo | exact Hhi].
Qed.

(* A written range E keeps nothing more than E' on the block and frame bytes when it adds only bytes at or above
   alloc_ceiling (io_send's own machine frame; lib/A/Prog/io_send_seg_tail.v ios_kept_shrink). *)
Lemma ient_kept_shrink : forall G lyc Sc (Wa : world segs) mema mda (W : world segs) memc (W2 : world segs) mem2
    slo shi (E E' : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc Wa mema mda ->
  (forall a, E a -> a < alloc_ceiling -> E' a) ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E -> acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E'.
Proof.
intros G lyc Sc Wa mema mda W memc W2 mem2 slo shi E E' LAWS HAR HE (K1 & K2 & K3 & K4 & K5 & K6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact K1|]. split.
{ intros b m i Hb Hi Hn. apply (K2 b m i Hb Hi). intros HE0. apply Hn. apply HE; [exact HE0|].
  destruct (al_blocks _ _ LAWS lyc Sc Wa mema mda b m HAR Hb) as (_ & H4096 & Hbc & _). lia. }
split; [exact K3|]. split.
{ intros cid pos a Hin Hr Hn. apply (K4 cid pos a Hin Hr). intros HE0. apply Hn. apply HE; [exact HE0|].
  destruct (frames_bounds segs B LAWS lyc Sc Wa mema mda cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
split; [exact K5 | exact K6].
Qed.

(* The entry stretch: from the entry configuration to the cut IOS_SRF. *)
Lemma ios_entry : @ios_entry_stmt fx rc B MT.
Proof.
unfold ios_entry_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Q HL HF HCSF HK.
destruct HL as (HCELLS & _ & HRU & HRE & LAWS & MTL & HGX & _ & HSRF & _).
destruct HF as (HJ & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hlo & Hhi & Hp0 & Hgarr & Hsrc & Hoff & Hfat
  & Hfail & Hrom & Htw & _ & _ & Hev).
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8512) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (ESR : SRF_STK = 4144) by reflexivity.
assert (EF : TB_g_fail_next = 0x5deda0) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hwin : forall a, spZ regs - IOSEND_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (GLOW : forall a, inG TG.G_HARNESS_B a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
pose proof (ios_len60 _ _ _ HCSF) as HL60.
assert (HPL : 0 <= p /\ p + Z.of_nat (length frame) <= 2 ^ 47).
{ destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc p (Z.of_nat (length frame)) HAR Hsrc ltac:(lia))
    as [Pl | Pl]; lia. }
(* the byte of g_fail_next, as the world holds it *)
pose proof (TWL.u_at_range Bw TW.OFF_g_fail_next 1) as Rf. change (8 * Z.of_nat 1) with 8 in Rf.
change (TW.u_at Bw TW.OFF_g_fail_next 1) with (TW.g_fail_next Bw) in Rf.
assert (Vf : YI04.val_mem segs (mrestrict (w_H W) memc) (TB_g_fail_next + 0) 1 (TW.g_fail_next Bw))
  by exact (tw_read_val segs (mrestrict (w_H W) memc) TMAP_B Bw TW.OFF_g_fail_next TB_g_fail_next 1 0 1
    TMAP_B_ok Htw TMAP_B_g_fail_next ltac:(lia) ltac:(lia)).
set (fb := TW.g_fail_next Bw) in *.
(* the valuation of the walk and its atoms *)
set (E0 := ient_E regs fb).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ient_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0, ient_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E0, ient_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 fb)
  by (unfold E0, ient_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
destruct ient_vals as (V1 & V95 & V25 & V50 & VBASE).
assert (U25 : bv_unsigned (ew E0 (A_OBJ 25)) = TB_g_fail_next).
{ unfold E0, ient_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V25.
  apply unsigned_lit_small. rewrite EF. lia. }
assert (U25' : bv_unsigned (ew E0 266%nat) = TB_g_fail_next) by exact U25.
destruct (ient_entry lyc Sc W regs memc mdc fb HCELLS HAR ltac:(intros a Ha; apply Hpres0; lia) Hsp Hsp16
  ltac:(lia) Vf) as [HS SHOK].
fold E0 in HS, SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_io_send)) memc (YK11.seg_rom segs)) mdc) Qx)
end.
(* run 1, +0x00 .. +0x54: the frame, the nine saves, s0 = len, s1 = p, the shadow base into s4, g_fail_next's byte
   into s3 and the store of 0 there, the arguments, the call of spec_read_frame. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ient_awr Usp U25'. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
(* the bytes the run wrote: its frame and g_fail_next's byte *)
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 160 <= a < spZ regs) ->
  ~ (TB_g_fail_next <= a < TB_g_fail_next + 1) -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha H1 H2.
  apply (kept_of_frame _ _ _ _ _
    (fun x => (spZ regs - 160 <= x < spZ regs) \/ (TB_g_fail_next <= x < TB_g_fail_next + 1)) HFr);
    [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta.
  ient_win Hin Hx ltac:(rewrite ?Usp, ?U25' in Hx; first [lia | left; lia | right; lia]). }
assert (GA1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the run's last state: the nine saved words (region 0) and the 0 stored at g_fail_next (region 3) *)
pose proof (YC4b.st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as RG0.
pose proof (YC4b.st_ok_region_nth _ _ _ 3%nat _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG0, RG3.
destruct RG0 as (_ & _ & _ & HC0). destruct RG3 as (_ & _ & _ & HC3).
cbn [YP09.r_base YP09.r_chunks base_val] in HC0, HC3.
rewrite Usp in HC0. rewrite U25' in HC3.
rewrite Forall_forall in HC0.
pose proof (Forall_inv HC3) as HCk3. clear HC3.
assert (SV1 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs - fst o) =
          Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) IOS_SAVED).
{ unfold IOS_SAVED.
  repeat (apply Forall_cons; [cbn [fst snd]; ient_save HC0 EE |]).
  apply Forall_nil. }
assert (VF1 : aview segs (w_H W) (ms_mem ms) TB_g_fail_next = Some 0).
{ pose proof (val_of_chunk_ok segs E0 (mrestrict (w_H W) (ms_mem ms)) TB_g_fail_next 0 1%N (SLit 0) 0 HCk3 eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia) 0%nat ltac:(cbn; lia)) as Vm.
  unfold aview. replace TB_g_fail_next with (TB_g_fail_next + 0 + Z.of_nat 0) by lia. rewrite Vm. reflexivity. }
clear HC0 HCk3.
(* the registers at the call *)
pmkst HS.
ient_reg HS (Z_to_bv 5 10) (w64 p) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
ient_reg HS (Z_to_bv 5 11) (w64 (Z.of_nat (length frame))) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H12).
ient_reg HS (Z_to_bv 5 12) (w64 (spZ regs - 152)) Q12
  ltac:(cbn [sv_denot]; rewrite Usp; unfold w64; f_equal; lia).
ient_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 160)) Q2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
ient_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 7604)) R1 ltac:(apply codeptr_val; exact HEI).
ient_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ient_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ient_reg HS (Z_to_bv 5 8) (w64 (Z.of_nat (length frame))) R8
  ltac:(cbn [sv_denot]; rewrite (EE 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H12).
ient_reg HS (Z_to_bv 5 9) (w64 p) R9
  ltac:(cbn [sv_denot]; rewrite (EE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
ient_reg HS (Z_to_bv 5 19) (w64 fb) R19
  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ient_reg HS (Z_to_bv 5 20) (w64 SHADOW_OFF) R20
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ient_reg HS (Z_to_bv 5 24) (YK11.getr regs (Z_to_bv 5 24)) R24
  ltac:(cbn [sv_denot]; rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ient_reg HS (Z_to_bv 5 25) (YK11.getr regs (Z_to_bv 5 25)) R25
  ltac:(cbn [sv_denot]; rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ient_reg HS (Z_to_bv 5 26) (YK11.getr regs (Z_to_bv 5 26)) R26
  ltac:(cbn [sv_denot]; rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ient_reg HS (Z_to_bv 5 27) (YK11.getr regs (Z_to_bv 5 27)) R27
  ltac:(cbn [sv_denot]; rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 160)
  by (rewrite Q2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 160) by exact ESP.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
(* the frame's bytes and placement, and the world, at the call: the run wrote only its frame and g_fail_next *)
assert (KF : forall a, p <= a < p + Z.of_nat (length frame) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha. apply KR1; [lia | unfold decode_off_win in Hoff; lia |].
  intros Hta. destruct Hfat as [Hng | Hgs]; [exact (Hng a Ha (ient_inG_fail a Hta))|].
  unfold TB_g_s in Hgs. rewrite EF in Hta. lia. }
assert (KS : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W) (ms_mem ms) s = aview segs (w_H W) memc s).
{ intros s Hs. apply KR1; [lia | lia | rewrite EF; lia]. }
assert (HGA1 : garr8 segs (mrestrict (w_H W) (ms_mem ms)) p (map DSpec.bz frame)).
{ apply (ient_garr8_kept (w_H W) (w_H W) memc (ms_mem ms) p _ Hgarr). intros a Ha. rewrite length_map in Ha.
  exact (KF a Ha). }
assert (HSR1 : trans_src_ok B lyc Sc W (ms_mem ms) p (Z.of_nat (length frame))).
{ eapply trans_src_ok_view; [exact Hsrc | exact KF | exact KS]. }
assert (HTW1 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) (ios_B0 Bw)).
{ rewrite ient_B0.
  apply (tw_write TMAP_B (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms)) Bw TW.OFF_g_fail_next
    TB_g_fail_next 1 0 1 0 TMAP_B_ok Htw TMAP_B_g_fail_next ltac:(lia) ltac:(lia)).
  - intros j Hj. assert (Ej : j = 0%nat) by lia. subst j. cbn [Z.of_nat]. rewrite !Z.add_0_r. rewrite VF1.
    reflexivity.
  - intros x Hx Hn. pose proof (GLOW x (ios_tw_in_G x Hx)) as Hl. unfold kLowMemEnd in Hl.
    apply KR1; [lia | lia | lia]. }
(* the running kept fact at the call *)
assert (HK1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem ms) (spZ regs - IOSEND_STK) (spZ regs)
                 (iosend_wr (Z.of_nat (length frame)))).
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc (ms_mem ms)
    (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame)))
    (fun a => (spZ regs - IOSEND_STK <= a < spZ regs) \/ (TB_g_fail_next <= a < TB_g_fail_next + 1)) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. apply KR1; [exact Ha | intros H; apply Hn; left; lia | intros H; apply Hn; right; exact H].
  - exact GA1.
  - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. rewrite EF in Hw. lia.
  - intros b m i Hb Hi [Hw | Hw].
    + exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    + apply ios_wr_fail. exact Hw.
  - intros a [Hw | Hw] Hi HnG _ _.
    + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
    + apply HnG. apply ient_inG_fail. exact Hw.
  - intros cid pos a Hin Hr [Hw | Hw].
    + exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
    + apply ios_wr_fail. exact Hw. }
(* +0x54: spec_read_frame (p, len, sp + 8), its G-form contract at the run's journal *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_spec_read_frame) rg mm mdx) Qx) end.
eapply SRr_bind.
{ apply (HSRF fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md1 k (ms_regs ms) p (Z.of_nat (length frame))
    (spZ regs - 152) frame HJ).
  - rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - unfold raZ. rewrite R1, VBASE. rewrite unsigned_lit_small by (unfold transportb_text; lia).
    unfold transportb_text. lia.
  - exact R3.
  - exact R4.
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - rewrite Hsp1. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
  - rewrite Hsp1, ESR. lia.
  - rewrite Hsp1. lia.
  - exact Hp0.
  - lia.
  - exact HGA1.
  - exact HSR1.
  - unfold decode_off_win in *. rewrite Hsp1, ESR. lia.
  - intros x Hx Hw. unfold srf_wr, SRF_SIZE in Hw. unfold decode_off_win in Hoff. lia.
  - replace (spZ regs - 152) with ((spZ regs / 16 * 2 - 19) * 8)
      by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)); lia).
    apply Z_mod_mult.
  - apply (transport_twr_ok_g_intro segs B LAWS TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms)
      md1 k (spZ (ms_regs ms)) (spZ regs - 152) SRF_SIZE HJ).
    intros a Ha. left. unfold SRF_SIZE in Ha. split; [unfold awr_byte; left; lia | rewrite Hsp1; lia].
  - split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha. apply ient_vis_of_present. apply GA1. apply Hpres0. unfold SRF_SIZE in Ha. lia.
    + destruct (stack_zshadow_ra B lyc Sc W (ms_mem ms) md1 (spZ regs - 152) SRF_SIZE HAR1
        ltac:(unfold SRF_SIZE; lia) ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; unfold SRF_SIZE; lia)) as [HRA _].
      exact HRA.
    + destruct (stack_zshadow_ra B lyc Sc W (ms_mem ms) md1 (spZ regs - 152) SRF_SIZE HAR1
        ltac:(unfold SRF_SIZE; lia) ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; unfold SRF_SIZE; lia)) as [_ HHL].
      exact HHL.
    + unfold amem_range. right. unfold SRF_SIZE. lia.
    + lia.
    + unfold SRF_SIZE. lia.
  - unfold decode_off_win. right. rewrite Hsp1. lia.
  - intros x Hx Hg. pose proof (inG_G_HARNESS_hull x Hg) as Gh. unfold TG.G_HARNESS_B_HI in Gh. lia.
  - unfold SRF_EV. unfold IOSEND_EV in Hev. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & e & -> & He & HJ2 & HP2 & Hfr2 & Hperm2 & HKc & HMO2
  & HA0 & HSB & HGK).
assert (Ee : e = 0) by (unfold SRF_EV in He; lia). subst e.
destruct (ient_jlayout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (_ & FAc & Loc & Hic).
destruct (ient_jlayout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (HAR2 & FA2 & Lo2 & Hi2).
(* the struct at sp + 8: present at the returned memory *)
assert (HPo : forall a, inG [(spZ regs - 152, SRF_SIZE)] a -> apresent (w_H W2) mem2 a).
{ intros a Ha. apply ient_inG1 in Ha. unfold SRF_SIZE in Ha.
  apply (apresent_of_aview segs (w_H W2) mem2 a ltac:(lia)).
  - intros Hi. pose proof (transportb_segs_low a Hi). unfold kLowMemEnd in *. lia.
  - apply (ient_garr8_vis (w_H W2) mem2 _ _ HSB). unfold TW.zs. rewrite length_map, ient_sf_len. lia. }
(* the callee's kept fact folded into io_send's own (the struct lies in io_send's window), then shrunk back *)
assert (HK1' : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem ms) (spZ regs - IOSEND_STK) (spZ regs)
  (fun a => iosend_wr (Z.of_nat (length frame)) a \/ srf_wr (spZ regs - 152) a))
  by exact (acall_kept_g_weaken segs B _ _ _ _ _ _ _ _ _ _ _ (fun a Ha => or_introl Ha) HK1).
assert (RK2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - IOSEND_STK) (spZ regs)
  (fun a => iosend_wr (Z.of_nat (length frame)) a \/ srf_wr (spZ regs - 152) a)).
{ apply (dk_kept_trans_out_g segs B LAWS transportb_segs_low TG.G_HARNESS_B [(spZ regs - 152, SRF_SIZE)]
    lyc Sc W memc mdc W (ms_mem ms) W2 mem2 (spZ regs - IOSEND_STK) (spZ regs) (spZ (ms_regs ms) - SRF_STK)
    (spZ (ms_regs ms)) _ (srf_wr (spZ regs - 152)) HAR).
  - lia.
  - lia.
  - intros a Ha. apply ient_inG1 in Ha. unfold SRF_SIZE in Ha. lia.
  - exact HPo.
  - exact HK1'.
  - exact HKc.
  - rewrite Hsp1, ESR. lia.
  - rewrite Hsp1. lia.
  - intros a Ha. right. exact Ha. }
assert (RK : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - IOSEND_STK) (spZ regs)
  (iosend_wr (Z.of_nat (length frame)))).
{ apply (ient_kept_shrink TG.G_HARNESS_B lyc Sc W memc mdc W memc W2 mem2 _ _
    (fun a => iosend_wr (Z.of_nat (length frame)) a \/ srf_wr (spZ regs - 152) a) _ LAWS HAR); [|exact RK2].
  intros a [Ha | Ha] Hc; [exact Ha | unfold srf_wr, SRF_SIZE in Ha; lia]. }
(* the same fold from the call memory: the frame across the call *)
assert (KC : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W (ms_mem ms) W2 mem2 (spZ regs - IOSEND_STK) (spZ regs)
  (srf_wr (spZ regs - 152))).
{ apply (dk_kept_trans_out_g segs B LAWS transportb_segs_low TG.G_HARNESS_B [(spZ regs - 152, SRF_SIZE)]
    lyc Sc W (ms_mem ms) md1 W (ms_mem ms) W2 mem2 (spZ regs - IOSEND_STK) (spZ regs) (spZ (ms_regs ms) - SRF_STK)
    (spZ (ms_regs ms)) (srf_wr (spZ regs - 152)) (srf_wr (spZ regs - 152)) HAR1).
  - lia.
  - lia.
  - intros a Ha. apply ient_inG1 in Ha. unfold SRF_SIZE in Ha. lia.
  - exact HPo.
  - apply dk_kept_refl_g. intros a Ha. pose proof HK1 as (_ & _ & _ & _ & _ & K6). exact (K6 a Ha).
  - exact HKc.
  - rewrite Hsp1, ESR. lia.
  - rewrite Hsp1. lia.
  - intros a Ha. exact Ha. }
assert (SRCK : trans_src_ok B ly2 S2 W2 mem2 p (Z.of_nat (length frame)) /\
  (forall a, p <= a < p + Z.of_nat (length frame) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) (ms_mem ms) a)).
{ apply (trans_src_ok_acall_g B LAWS HRU HRE lyc Sc W (ms_mem ms) md1 ly2 S2 W2 mem2 md2 (spZ regs - IOSEND_STK)
    (spZ regs) (srf_wr (spZ regs - 152)) p (Z.of_nat (length frame)) HAR1 HAR2 Hperm2 Hfr2).
  - intros cid pos. rewrite FA2, FAc. reflexivity.
  - rewrite Lo2, Loc. reflexivity.
  - rewrite Hi2, Hic. reflexivity.
  - exact KC.
  - exact HGK.
  - intros a Ha Hw. unfold srf_wr, SRF_SIZE in Hw. unfold decode_off_win in Hoff. lia.
  - intros a Ha Hw. unfold srf_wr, SRF_SIZE in Hw. lia.
  - exact Hoff.
  - exact HSR1.
  - lia. }
destruct SRCK as [HSR2 KV].
assert (HGA2 : garr8 segs (mrestrict (w_H W2) mem2) p (map DSpec.bz frame)).
{ apply (ient_garr8_kept (w_H W) (w_H W2) (ms_mem ms) mem2 p _ HGA1). intros a Ha. rewrite length_map in Ha.
  exact (KV a Ha). }
(* the world: the run's store, then spec_read_frame keeps G *)
assert (HTW2 : tw_at TMAP_B (aview segs (w_H W2) mem2) (ios_B0 Bw)).
{ apply (tw_kept_GB _ _ _ HTW1). intros b n i Hin Hi. exact (gx_kept_rows _ _ _ _ _ _ HGK b n i Hin Hi). }
(* the nine saved words: above the call's window and past the struct *)
assert (SV2 : ios_saved W2 mem2 regs).
{ unfold ios_saved. rewrite Forall_forall in SV1 |- *. intros o Ho. rewrite <- (SV1 o Ho).
  assert (Hd : 8 <= fst o <= 72)
    by (unfold IOS_SAVED in Ho; cbn [In] in Ho; repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]); destruct Ho).
  apply rdword_ext. intros j Hj.
  pose proof HKc as (K1 & _).
  assert (Hn : ~ inG [(spZ regs - 152, SRF_SIZE)] (spZ regs - fst o + j))
    by (intros Hg; apply ient_inG1 in Hg; unfold SRF_SIZE in Hg; lia).
  refine (eq_trans (eq_sym (gover_out_aview segs _ (w_H W2) mem2 (ms_mem ms) (spZ regs - fst o + j) ltac:(lia) Hn))
    _).
  apply K1; [lia | rewrite Hsp1, ESR; lia]. }
(* the registers *)
assert (HR : ios_regs regs regs2 p frame fb).
{ unfold ios_regs.
  split; [refine (eq_trans (HP2 2 ltac:(unfold acallee_saved; lia)) _); exact Q2|].
  split; [refine (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) _); exact (eq_trans R3 (eq_sym Hgp))|].
  split; [refine (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) _); exact (eq_trans R4 (eq_sym Htp))|].
  split; [refine (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) _); exact R8|].
  split; [refine (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) _); exact R9|].
  split; [refine (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) _); exact R19|].
  refine (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) _); exact R20. }
assert (H811 : forall r, 24 <= r <= 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
  assert (Hc : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]]; [exact R24 | exact R25 | exact R26 | exact R27]. }
(* the struct f at sp + 8: spec_read_frame's X, field by field *)
assert (HSF2 : trans_sframe_at W2 mem2 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (TC.rf frame)).
{ replace (spZ regs - IOSEND_FRAME + IOS_F_OFF) with (spZ regs - 152) by (unfold IOS_F_OFF; lia).
  rewrite srf_f_rf in HSB.
  apply (ient_rf_sframe W2 mem2 (spZ regs - 152) p frame (ios_B0 Bw) (ios_B0 Bw) HCSF); [lia | | lia | lia | exact HSB].
  replace (spZ regs - 152) with ((spZ regs / 16 * 2 - 19) * 8)
    by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)); lia).
  apply Z_mod_mult. }
assert (HCUR : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem2 md2).
{ unfold ios_cur.
  split; [exact HJ2|]. split; [exact Hfr2|]. split; [exact Hperm2|].
  split; [exact HMO2 | exact RK]. }
(* the cut *)
rewrite R1, ient_pc.
specialize (HK ly2 S2 W2 mem2 md2 regs2). unfold cfg_at in HK. apply HK.
unfold ios_at_srf.
split; [exact HCUR|]. split; [exact SV2|]. split; [exact HR|]. split; [exact H811|].
split; [exact HSF2|]. split; [exact HGA2|]. split; [exact HSR2 | exact HTW2].
Qed.
End ientw.
