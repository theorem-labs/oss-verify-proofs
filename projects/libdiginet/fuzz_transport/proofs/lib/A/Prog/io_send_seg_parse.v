(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 678 of its 962 lines of code are new or changed and 855 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcHead.v, with its module paths, module names and numbers changed; 528 of its 590 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_base.v, with its numbers changed; 317 of its 395 lines of code are new or changed and 512 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_lost.v, with its numbers changed; 316 of its 437 lines of code are new or changed and 274 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_data.v, with its module paths and module names changed; 344 of its 398 lines of code are new or changed and 383 lines of the source are left out. *)
(* io_send_seg_parse: the parse of the image-A walk of io_send (fuzz_transport.asan e89be137db17; the statement is
   lib/A/Prog/io_send_cg.v), from the cut IOS_PARSE (0x82db8, io_send_seg_cut.v ios_at_parse) to the join
   IOS_AT 0x314 (0x83074, where the parse's arms meet), as one segment lemma in continuation form: ios_parse_seg.

   It composes two proved stretches:
   - lib/A/Prog/io_send_seg_hdr.v ios_hdr_seg, 0x82db8 .. 0x8302c: the header fields stored into the struct
     spec_frame f at sp + 8 (sp the walk's sp, spZ regs - IOSEND_FRAME), a2 = body_len, a3 = p + 30;
   - lib/A/Prog/io_send_seg_sum.v ios_sum_seg, 0x8302c .. 0x83074: the body sum stored at f + 72, a0 = 0.
   The model premise io_send_m timg_A Bw frame = Some (Bw', r) gives check_sent_frame's model call at ios_B0 Bw
   (io_send_segs.v ios_m_arm), hence sf_code (rf frame) = SPEC_OK (io_send_seg_frm.v ios_sf_code) and the parse
   facts and field values of io_send_seg_frm.v ios_fields.

   What it produces at 0x83074 (registers regs3, memory mem3, at the cut's layout, state and world): the eleven
   facts of io_send_seg_cut.v ios_at_join, in its order:
   - ios_cur: the journal, frames, blocks and meter as at the cut, and acall_kept_g extended over the bytes the
     parse stores, [sp + 16, sp + 82), all in io_send's stack window (ip_kept_step);
   - ios_saved (the saved words lie at sp + 88 .. sp + 160, apart from the stores);
   - ios_regs and s8 .. s11 (both stretches keep sp, gp, tp, s0, s1, s3, s4, s8 .. s11), a0 = 0;
   - trans_sframe_at of rf frame at f = sp + IOS_F_OFF, with SB = ip_sb p frame: the memset's zeros at f + 0 ..
     f + 7, f + 42 .. f + 47 and f + 74 .. f + 79, the header fields ios_hdr_seg stored (fuzz_frame's readings,
     which ios_fields equates with the sf_ fields of rf frame; the pointers dst, src, body are TContract.v sf_ptr
     p (rf frame) 0 / 6 / 30 at code 0) and the body sum ios_sum_seg stored at f + 72;
   - the code bytes f + 0 .. f + 3 still 0;
   - the frame's bytes (garr8), its placement (trans_src_ok), the read-only image bytes (trans_rom_view_rd) and the
     world relation at ios_B0 Bw, each carried by the bytes the parse keeps (it stores only into io_send's frame). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  io_send_segs io_send_seg_frm io_send_seg_world io_send_seg_cut io_send_seg_hdr io_send_seg_sum.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* ------------------------------------------------------------------ *)
(* The 80 bytes of the struct at the join                              *)
(* ------------------------------------------------------------------ *)

(* The struct spec_frame f at the join, as fuzz_frame reads the frame bytes: the memset's zeros where nothing is
   stored (the code included: the store of 0 at 0x83074 comes after the join), the header fields, the body sum. *)
Definition ip_sb (p : Z) (frame : list byte) : list byte :=
  repeat (DSpec.b8 0) 8 ++ TW.put 8 p ++ TW.put 8 (p + 6) ++
  TW.put 2 (DSpec.fr_ethertype frame) ++ TW.put 2 (DSpec.fr_numbytes frame) ++
  TW.put 2 (DSpec.fr_sum frame) ++ TW.put 2 (DSpec.fr_retry frame) ++
  TW.put 4 (DSpec.fr_send frame) ++ TW.put 4 (DSpec.fr_ack frame) ++
  TW.put 1 (DSpec.fr_cmd frame) ++ TW.put 1 (DSpec.fr_ncmds frame) ++ repeat (DSpec.b8 0) 6 ++
  TW.put 8 (p + 30) ++ TW.put 8 (DSpec.fr_body_len frame) ++ TW.put 8 (DSpec.fr_pad_len frame) ++
  TW.put 2 (DSpec.fr_body_sum frame) ++ repeat (DSpec.b8 0) 6.

Lemma ip_sb_length : forall p frame, length (ip_sb p frame) = 80%nat.
Proof. intros p frame. unfold ip_sb. rewrite !length_app, !TWL.length_put, !repeat_length. reflexivity. Qed.

(* Reads of a concatenation (lib/Prog/T/io_send_sf.v sf_u_at_app_l / _r / sf_u_at_fld). *)
Lemma ip_u_at_app_l : forall (x y : list byte) (k : Z) (n : nat), 0 <= k -> k + Z.of_nat n <= Z.of_nat (length x) ->
  TW.u_at (x ++ y) k n = TW.u_at x k n.
Proof.
  intros x y k n Hk Hn. unfold TW.u_at, TW.sub. f_equal.
  rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length x - Z.to_nat k))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma ip_u_at_app_r : forall (x y : list byte) (k : Z) (n : nat), Z.of_nat (length x) <= k ->
  TW.u_at (x ++ y) k n = TW.u_at y (k - Z.of_nat (length x)) n.
Proof.
  intros x y k n Hk. unfold TW.u_at, TW.sub. f_equal.
  rewrite skipn_app.
  assert (E : skipn (Z.to_nat k) x = []) by (apply skipn_all2; lia).
  rewrite E, app_nil_l.
  replace (Z.to_nat (k - Z.of_nat (length x))) with (Z.to_nat k - length x)%nat by lia.
  reflexivity.
Qed.

Lemma ip_u_at_fld : forall (y : list byte) (n : nat) (v k : Z), k = 0 -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  TW.u_at (TW.put n v ++ y) k n = v.
Proof.
  intros y n v k Hk Hv. subst k.
  rewrite ip_u_at_app_l by (rewrite ?TWL.length_put; lia).
  rewrite TWL.u_at_put. apply Z.mod_small. exact Hv.
Qed.

Ltac ip_len := rewrite ?length_map, ?TWL.length_put, ?repeat_length; lia.
Ltac ip_field := repeat (rewrite ip_u_at_app_r by ip_len); apply ip_u_at_fld; [ip_len |].

(* ------------------------------------------------------------------ *)
(* Bytes kept                                                          *)
(* ------------------------------------------------------------------ *)

Lemma ip_rdword_kept : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  pose proof (H 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
  rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Ltac ip_kin := unfold ios_hdr_keep, IOS_SUM_KEEP; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).

Section parse. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

Lemma ip_val_kept : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview segs H m' x = aview segs H m x) ->
  val_mem segs (mrestrict H m') a n v.
Proof.
  intros H m m' a n v Hv Hk kk Hkk.
  rewrite (mbyte_of_aview segs H H m m' (a + Z.of_nat kk) (Hk (a + Z.of_nat kk) ltac:(lia))). exact (Hv kk Hkk).
Qed.

(* The bytes of put n v at a, from val_mem. *)
Lemma ip_garr8_put : forall (m : word -> option byte) a a' (n : nat) v, a' = a ->
  val_mem segs m a n v -> garr8 segs m a' (map DSpec.bz (TW.put n v)).
Proof.
  intros m a a' n v -> Hv j Hj. rewrite length_map, TWL.length_put in Hj.
  assert (Ej : nth j (map DSpec.bz (TW.put n v)) 0 = YO0f.le_byte v n j).
  { change 0 with (DSpec.bz (DSpec.b8 0)). rewrite map_nth. unfold DSpec.bz. apply tw_le_byte_put. exact Hj. }
  rewrite Ej.
  assert (R : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
  split; [|exact R].
  intros kk Hk. assert (Ek : kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (tw_le_byte1 _ R). exact (Hv j Hj).
Qed.

(* The memset's zero bytes. *)
Lemma ip_garr8_zero : forall (H : word -> bool) (m : word -> option byte) a a' (n : nat), a' = a ->
  (forall i, 0 <= i < Z.of_nat n -> aview segs H m (a + i) = Some 0) ->
  garr8 segs (mrestrict H m) a' (map DSpec.bz (repeat (DSpec.b8 0) n)).
Proof.
  intros H m a a' n -> Hz. rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
  apply garr8_zeros. intros x Hx.
  pose proof (Hz (x - a) ltac:(lia)) as E. replace (a + (x - a)) with x in E by lia.
  unfold aview in E. destruct (mbyte segs (mrestrict H m) x) as [b|] eqn:Eb; cbn [option_map] in E;
    [|discriminate E].
  injection E as E. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, E. reflexivity.
Qed.

(* One stretch that changes only bytes Zs of the call's stack window, above the allocation ceiling, keeps
   acall_kept_g (TransportGCg.v dk_kept_step_g at a current world W2). *)
Lemma ip_kept_step : forall G lyc Sc (W : world segs) memc mdc (W2 : world segs) memX memY slo shi
    (Eo Zs : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B G lyc Sc W memc W2 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) memY a = aview segs (w_H W2) memX a) ->
  (forall a, apresent (w_H W2) memX a -> apresent (w_H W2) memY a) ->
  (forall a, Zs a -> alloc_ceiling <= a < 2 ^ 64 /\ slo <= a < shi) ->
  acall_kept_g segs B G lyc Sc W memc W2 memY slo shi Eo.
Proof.
  intros G lyc Sc W memc mdc W2 memX memY slo shi Eo Zs LAWS HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZ.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite (Hkp a ltac:(lia)); [exact (K1 a Ha Hw) |].
    intros Hz. destruct (HZ a Hz) as [_ Hs]. exact (Hw Hs).
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _).
    rewrite (Hkp (b + i) ltac:(lia)); [exact (K2 b m i Hb Hi Hn) |].
    intros Hz. destruct (HZ _ Hz) as [Hz1 _]. lia.
  - intros a Hi HnG Hno He. pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    rewrite (Hkp a ltac:(lia)); [exact (K3 a Hi HnG Hno He) |].
    intros Hz. destruct (HZ a Hz) as [Hz1 _]. lia.
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    rewrite (Hkp a ltac:(lia)); [exact (K4 cid pos a Hin Hr Hn) |].
    intros Hz. destruct (HZ a Hz) as [Hz1 _]. lia.
  - intros a Ha Hw Hp. exact (Hgr a (K5 a Ha Hw Hp)).
  - intros a Ha. exact (Hgr a (K6 a Ha)).
Qed.

(* ------------------------------------------------------------------ *)
(* The parse                                                           *)
(* ------------------------------------------------------------------ *)

Lemma ios_parse_seg : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame Bw Bw' : list byte) (rv : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (regs2 : bvmap 5 word) (Q : world segs -> config -> Prop),
  ios_laws B MT ->
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  TC.io_send_m timg_A Bw frame = Some (Bw', rv) ->
  ios_at_parse B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame Bw ly2 S2 W2 mem2 md2 regs2 ->
  (forall (mem3 : word -> option byte) (md3 : Model) (regs3 : bvmap 5 word),
     ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly2 S2 W2 mem3 md3 /\
     ios_saved W2 mem3 regs /\
     ios_regs regs regs3 p frame (TW.g_fail_next Bw) /\
     (forall r, 24 <= r <= 27 -> YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
     YK11.getr regs3 10 = w64 0 /\
     trans_sframe_at W2 mem3 (spZ regs - IOSEND_FRAME + IOS_F_OFF) p (TC.rf frame) /\
     (forall j, 0 <= j < 4 -> aview segs (w_H W2) mem3 (spZ regs - IOSEND_FRAME + IOS_F_OFF + j) = Some 0) /\
     garr8 segs (mrestrict (w_H W2) mem3) p (map DSpec.bz frame) /\
     trans_src_ok B ly2 S2 W2 mem3 p (Z.of_nat (length frame)) /\
     trans_rom_view_rd W2 mem3 /\
     tw_at TMAP_A (aview segs (w_H W2) mem3) (io_send_segs.ios_B0 Bw) ->
     SRr segs W2 (@cfg_at fx segs (transport_text + IOS_AT 0x314) regs3 mem3 md3) Q) ->
  SRr segs W2 (@cfg_at fx segs (transport_text + IOS_PARSE) regs2 mem2 md2) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' rv ly2 S2 W2 mem2 md2 regs2 Q
    HL HF HM HP HK.
  destruct HL as (_ & _ & LAWS & MTL & HGX & _).
  destruct HF as (HJ0 & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & Hp0 & _ & _ & Hoff & _).
  destruct HP as (HCUR & HSAV & HREG & H2427 & HZ & HTW & HGA & HSRC & HROM).
  pose proof HCUR as (HJ2 & HFR & HPERM & HMO & HKG).
  destruct HREG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
  (* the call state *)
  pose proof HJ0 as (_ & _ & (memS & HJi & _) & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  clear HJi memS.
  (* the model: the parse succeeded *)
  destruct (ios_m_arm Bw frame Bw' rv HM) as (HCSF & _ & _).
  pose proof (ios_sf_code _ _ _ HCSF) as HOK.
  destruct (ios_fields frame HOK) as (HL30 & HET & HNB1 & HNB2 & Fdst & Fsrc & Fet & Fnb & Fsum & Fsend & Fack &
    Fretry & Fcmd & Fncmds & Fbody & Fblen & Fpad & Fbsum).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : IOSEND_STK = 8496) by reflexivity.
  assert (FF : IOSEND_FRAME = 160) by reflexivity.
  assert (FO : IOS_F_OFF = 8) by reflexivity.
  assert (SZ : SF_SIZE = 80) by reflexivity.
  assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
  assert (Hm16 : (spZ regs - IOSEND_FRAME) mod 16 = 0).
  { rewrite FF. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia. rewrite Z_mod_plus_full.
    exact Hsp16. }
  assert (HOFF : p + Z.of_nat (length frame) <= spZ regs - IOSEND_FRAME \/
                 spZ regs - IOSEND_FRAME + IOSEND_FRAME <= p).
  { unfold decode_off_win in Hoff. destruct Hoff as [Ho | Ho]; [left | right]; lia. }
  assert (Hlen : 30 <= Z.of_nat (length frame)) by lia.
  (* 0x82db8 .. 0x8302c: the header parse *)
  apply (ios_hdr_seg B Q STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 0) regs2 (spZ regs - IOSEND_FRAME)
    p frame LAWS HGX HJ2 R2 Hm16 ltac:(lia) ltac:(lia) R8 R9 R20 HZ HGA HSRC HOFF HL30 HET HNB1 HNB2).
  intros regs2' mem2' md2' KRh Q12 Q13 HJh GAh KAh Fh _ G8h SRCh.
  pose proof HJh as (_ & _ & (memS & HJi & _) & _).
  destruct HJi as (HARh & _). clear memS.
  pose proof (trans_src_ok_rd B LAWS ly2 S2 W2 mem2' md2' p (Z.of_nat (length frame)) HARh SRCh ltac:(lia)) as RDh.
  pose proof RDh as (_ & _ & _ & _ & Hp0' & Hp63).
  (* 0x8302c .. 0x83074: the body sum *)
  apply (ios_sum_seg fx rc B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2' md2' (k + 0) regs2'
    (spZ regs - IOSEND_FRAME) p frame Q LAWS HGX HJh
    (eq_trans (KRh 2%bv ltac:(ip_kin)) R2) (eq_trans (KRh 9%bv ltac:(ip_kin)) R9) Q12 Q13
    (eq_trans (KRh 20%bv ltac:(ip_kin)) R20) ltac:(lia) ltac:(lia) G8h RDh HNB1 HNB2).
  intros regs3 mem3 md3 HJs Q10 KRs VS KVs GAs.
  set (sp1 := spZ regs - IOSEND_FRAME) in *.
  (* what the two stretches keep *)
  assert (KR : forall x, In x IOS_SUM_KEEP -> In x ios_hdr_keep -> YK11.getr regs3 x = YK11.getr regs2 x)
    by (intros x H1 H2; rewrite (KRs x H1); exact (KRh x H2)).
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ ios_hdr_wr sp1 a -> ~ (sp1 + 80 <= a < sp1 + 82) ->
    aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
  { intros a Ha H1 H2. rewrite (KVs a Ha H2). exact (KAh a Ha H1). }
  assert (GALL : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a)
    by (intros a Ha; exact (GAs a (GAh a Ha))).
  assert (Hsp1 : sp1 = spZ regs - 160) by (unfold sp1; rewrite FF; reflexivity).
  assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
  apply HK.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - (* ios_cur *)
    split; [exact HJs|]. split; [exact HFR|]. split; [exact HPERM|]. split; [exact HMO|].
    apply (ip_kept_step _ lyc Sc W memc mdc W2 mem2 mem3 _ _ _ (fun a => sp1 + 16 <= a < sp1 + 82)
      LAWS HAR0 HKG).
    + intros a Ha Hn. apply KALL; [exact Ha | unfold ios_hdr_wr; intros [[H1 H2] | [H1 H2]]; apply Hn; lia |
        intros [H1 H2]; apply Hn; lia].
    + exact GALL.
    + intros a Ha. cbv beta in Ha. lia.
  - (* ios_saved *)
    unfold ios_saved in HSAV |- *. apply Forall_forall. intros o Hin.
    pose proof (proj1 (Forall_forall _ _) HSAV o Hin) as Ho. cbv beta in Ho |- *.
    assert (Hob : 8 <= fst o <= 72)
      by (unfold IOS_SAVED in Hin; cbn [In] in Hin;
          repeat (destruct Hin as [<- | Hin]; [cbn [fst]; lia |]); destruct Hin).
    rewrite <- Ho. apply ip_rdword_kept. intros i Hi. apply KALL;
      [lia | unfold ios_hdr_wr; intros [[H1 H2] | [H1 H2]]; lia | intros [H1 H2]; lia].
  - (* ios_regs *)
    split; [exact (eq_trans (KR 2%bv ltac:(ip_kin) ltac:(ip_kin)) R2)|].
    split; [exact (eq_trans (KR 3%bv ltac:(ip_kin) ltac:(ip_kin)) R3)|].
    split; [exact (eq_trans (KR 4%bv ltac:(ip_kin) ltac:(ip_kin)) R4)|].
    split; [exact (eq_trans (KR 8%bv ltac:(ip_kin) ltac:(ip_kin)) R8)|].
    split; [exact (eq_trans (KR 9%bv ltac:(ip_kin) ltac:(ip_kin)) R9)|].
    split; [exact (eq_trans (KR 19%bv ltac:(ip_kin) ltac:(ip_kin)) R19)|].
    exact (eq_trans (KR 20%bv ltac:(ip_kin) ltac:(ip_kin)) R20).
  - (* s8 .. s11 *)
    intros r0 Hr0. rewrite <- (H2427 r0 Hr0). apply KR.
    + assert (Hc : r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
      destruct Hc as [-> | [-> | [-> | ->]]]; ip_kin.
    + assert (Hc : r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
      destruct Hc as [-> | [-> | [-> | ->]]]; ip_kin.
  - (* a0 *)
    exact Q10.
  - (* the struct *)
    destruct Fh as (F16 & F24 & F32 & F34 & F36 & F38 & F40 & F44 & F48 & F49 & F56 & F64 & F72).
    assert (TR : forall a (n : nat) v, sp1 + 16 <= a -> a + Z.of_nat n <= sp1 + 80 ->
      val_mem segs (mrestrict (w_H W2) mem2') a n v -> val_mem segs (mrestrict (w_H W2) mem3) a n v).
    { intros a n v H1 H2 Hv. apply (ip_val_kept _ mem2' mem3 a n v Hv). intros x Hx.
      apply KVs; [lia | intros [H3 H4]; lia]. }
    assert (ZR : forall i, (0 <= i < 8 \/ 42 <= i < 48 \/ 74 <= i < 80) ->
      aview segs (w_H W2) mem3 (sp1 + IOS_F_OFF + i) = Some 0).
    { intros i Hi. assert (Hi' : 0 <= i < 80) by (destruct Hi as [Hi | [Hi | Hi]]; lia).
      rewrite KALL; [apply HZ; rewrite SZ; exact Hi' | rewrite FO; lia |
        unfold ios_hdr_wr; rewrite FO; destruct Hi as [Hi | [Hi | Hi]]; intros [[H1 H2] | [H1 H2]]; lia |
        rewrite FO; destruct Hi as [Hi | [Hi | Hi]]; intros [H1 H2]; lia]. }
    pose proof (ih_at8_range frame 12) as A12. pose proof (ih_at8_range frame 13) as A13.
    pose proof (ih_at8_range frame 14) as A14. pose proof (ih_at8_range frame 15) as A15.
    pose proof (ih_at8_range frame 16) as A16. pose proof (ih_at8_range frame 17) as A17.
    pose proof (ih_at8_range frame 18) as A18. pose proof (ih_at8_range frame 19) as A19.
    pose proof (ih_at8_range frame 20) as A20. pose proof (ih_at8_range frame 21) as A21.
    pose proof (ih_at8_range frame 22) as A22. pose proof (ih_at8_range frame 23) as A23.
    pose proof (ih_at8_range frame 24) as A24. pose proof (ih_at8_range frame 25) as A25.
    pose proof (ih_at8_range frame 26) as A26. pose proof (ih_at8_range frame 27) as A27.
    pose proof (ih_at8_range frame 28) as A28. pose proof (ih_at8_range frame 29) as A29.
    assert (Hq : sp1 = 16 * (sp1 / 16)) by (pose proof (Z.div_mod sp1 16 ltac:(lia)); lia).
    split; [rewrite FO; lia|].
    split.
    { rewrite FO. set (q := sp1 / 16) in Hq. rewrite Hq.
      replace (16 * q + 8) with ((2 * q + 1) * 8) by lia. apply Z_mod_mult. }
    exists (ip_sb p frame).
    split.
    { unfold ip_sb.
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_zero _ _ (sp1 + IOS_F_OFF + 0)); [lia | intros i Hi; rewrite <- Z.add_assoc;
          apply ZR; cbn in Hi; lia]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 16)); [rewrite FO; ip_len | apply TR; [lia | lia | exact F16]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 24)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F24]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 32)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F32]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 34)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F34]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 36)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F36]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 38)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F38]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 40)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F40]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 44)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F44]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 48)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F48]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 49)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F49]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_zero _ _ (sp1 + IOS_F_OFF + 42)); [rewrite ?length_map; ip_len |].
        intros i Hi. rewrite <- Z.add_assoc. apply ZR. cbn in Hi. lia. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 56)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F56]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 64)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F64]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 72)); [rewrite FO; rewrite ?length_map; ip_len | apply TR; [lia | lia | exact F72]]. }
      rewrite map_app; apply (proj2 (garr8_app _ _ _ _ _)); split.
      { apply (ip_garr8_put _ (sp1 + 80)); [rewrite FO; rewrite ?length_map; ip_len | exact VS]. }
      { apply (ip_garr8_zero _ _ (sp1 + IOS_F_OFF + 74)); [rewrite ?length_map; ip_len |].
        intros i Hi. rewrite <- Z.add_assoc. apply ZR. cbn in Hi. lia. } }
    split; [apply ip_sb_length|].
    split.
    { unfold TW.s32_at, ip_sb. rewrite ip_u_at_app_l by ip_len.
      change (TW.u_at (repeat (DSpec.b8 0) 8) 0 4) with 0. rewrite HOK. reflexivity. }
    split.
    { replace (TCt.sf_ptr p (TC.rf frame) (DSpec.sf_dst (TC.rf frame))) with p
        by (unfold TCt.sf_ptr; rewrite HOK, Z.eqb_refl, Fdst; lia).
      unfold ip_sb. ip_field. change (8 * Z.of_nat 8) with 64. lia. }
    split.
    { replace (TCt.sf_ptr p (TC.rf frame) (DSpec.sf_src (TC.rf frame))) with (p + 6)
        by (unfold TCt.sf_ptr; rewrite HOK, Z.eqb_refl, Fsrc; lia).
      unfold ip_sb. ip_field. change (8 * Z.of_nat 8) with 64. lia. }
    split.
    { rewrite Fet. unfold ip_sb. ip_field. change (8 * Z.of_nat 2) with 16. rewrite HET. lia. }
    split.
    { rewrite Fnb. unfold ip_sb. ip_field. change (8 * Z.of_nat 2) with 16.
      unfold DSpec.fr_numbytes, DSpec.be16. lia. }
    split.
    { rewrite Fsum. unfold ip_sb. ip_field. change (8 * Z.of_nat 2) with 16.
      unfold DSpec.fr_sum, DSpec.be16. lia. }
    split.
    { rewrite Fretry. unfold ip_sb. ip_field. change (8 * Z.of_nat 2) with 16.
      unfold DSpec.fr_retry, DSpec.be16. lia. }
    split.
    { rewrite Fsend. unfold ip_sb. ip_field. change (8 * Z.of_nat 4) with 32.
      unfold DSpec.fr_send, DSpec.be32. lia. }
    split.
    { rewrite Fack. unfold ip_sb. ip_field. change (8 * Z.of_nat 4) with 32.
      unfold DSpec.fr_ack, DSpec.be32. lia. }
    split.
    { rewrite Fcmd. unfold ip_sb. ip_field. change (8 * Z.of_nat 1) with 8. unfold DSpec.fr_cmd. lia. }
    split.
    { rewrite Fncmds. unfold ip_sb. ip_field. change (8 * Z.of_nat 1) with 8. unfold DSpec.fr_ncmds. lia. }
    split.
    { replace (TCt.sf_ptr p (TC.rf frame) (DSpec.sf_body (TC.rf frame))) with (p + 30)
        by (unfold TCt.sf_ptr; rewrite HOK, Z.eqb_refl, Fbody; lia).
      unfold ip_sb. ip_field. change (8 * Z.of_nat 8) with 64. lia. }
    split.
    { rewrite Fblen. unfold ip_sb. ip_field. change (8 * Z.of_nat 8) with 64.
      unfold DSpec.fr_body_len. lia. }
    split.
    { rewrite Fpad. unfold ip_sb. ip_field. change (8 * Z.of_nat 8) with 64.
      unfold DSpec.fr_pad_len, DSpec.fr_body_len. lia. }
    { rewrite Fbsum. unfold ip_sb. ip_field. change (8 * Z.of_nat 2) with 16.
      unfold DSpec.fr_body_sum, DSpec.sum16. apply Z.mod_pos_bound. lia. }
  - (* the code bytes *)
    intros j Hj. rewrite KALL;
      [apply HZ; rewrite SZ; lia | rewrite FO; lia | unfold ios_hdr_wr; rewrite FO; intros [[H1 H2] | [H1 H2]]; lia |
       rewrite FO; intros [H1 H2]; lia].
  - (* the frame's bytes *)
    apply (garr8_frame _ _ _ _ _ G8h). intros a Ha. rewrite length_map in Ha.
    apply (mbyte_of_aview segs). apply KVs; [lia | destruct HOFF as [HO | HO]; intros [H1 H2]; lia].
  - (* the frame's placement *)
    destruct SRCh as [Hblk | (HPL & Hrd)]; [left; exact Hblk | right; split; [exact HPL |]].
    eapply trans_rd_ok_view; [exact Hrd | |].
    + intros a Ha. apply KVs; [lia | destruct HOFF as [HO | HO]; intros [H1 H2]; lia].
    + intros s Hs. apply KVs; [lia | intros [H1 H2]; lia].
  - (* the read-only image bytes *)
    unfold trans_rom_view_rd in HROM |- *. intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Hb.
    rewrite KALL; [exact (HROM a Ha) | lia | unfold ios_hdr_wr; intros [[H1 H2] | [H1 H2]]; lia |
      intros [H1 H2]; lia].
  - (* the world relation *)
    apply (tw_kept TMAP_A (aview segs (w_H W2) mem2) _ _ HTW). intros x Hx.
    pose proof (GLOW x (ios_tw_in_G x Hx)) as Hl.
    apply KALL; [lia | unfold ios_hdr_wr; intros [[H1 H2] | [H1 H2]]; lia | intros [H1 H2]; lia].
Qed.

End parse.

Print Assumptions ios_parse_seg.
