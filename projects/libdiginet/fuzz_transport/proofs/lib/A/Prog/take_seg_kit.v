(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1480 of its 1576 lines of code are new or changed and 830 lines of the source are left out. *)
(* take_seg_kit: the shared part of the image-A walk of take (lib/A/Prog/take_cgW.v): the statement's premises as
   the variables of Section Walk / Section Call, the running invariant tkw_inv and the model bundles tkw_mw, tkw_mh,
   tkw_mj, tkw_mt, the cut statements tkw_head_P / tkw_join_P, every helper the cuts use, and the three call
   wrappers tkw_cpyq, tkw_cpyb (__asan_memcpy, TransportGCg.v gx_intrin_at) and tkw_bc (diginet_body_check,
   TransportGCg.v gx_call_cg).

   tkw_inv carries, at every cut: the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []) at the
   current state with the call state's frames and blocks and no meter charge; the kept fact of the post
   (acall_kept_g at gover [(blp, 8); (hdp, 4)] mem memc); the world relation at the current model world; take's
   224-byte frame; the cells at hdp and blp; and the 1484 bytes X at bp.

   The walk is cut over several files so that each compiles in minutes: every file sets Default Proof Using "All", so
   each item here takes the section's variables in one fixed order, and each later file re-opens the same section
   header and names the items of this file through one Local Notation per item. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI16 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YK1b YG0s YA0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit LeafCgFacts AsanKAProof TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg DgnTransportCgRun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGRwA TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import take_seg_model take_seg_run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TFE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportFevt.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module FCs := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Set Default Proof Using "All".

(* ---- small facts: bytes, views, the numbers of the layout ---- *)

(* The bytes of a world field are the little-endian bytes of its value. *)
Lemma tkw_sub_put : forall (Bx : list byte) k (n : nat), 0 <= k -> k + Z.of_nat n <= Z.of_nat (length Bx) ->
  TW.sub Bx k n = TW.put n (TW.u_at Bx k n).
Proof.
  intros Bx k n Hk Hl. unfold TW.put, TW.u_at.
  pose proof (YA0d.Z_to_le_bytes_to_Z (TW.sub Bx k n)) as E.
  rewrite (TWL.length_sub Bx k n Hk Hl) in E. symmetry. exact E.
Qed.

(* A view reads a memory only at its own address. *)
Lemma tkw_aview_raw : forall (H : word -> bool) (m m1 : word -> option byte) a,
  m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview tfibsegs H m1 a = aview tfibsegs H m a.
Proof. intros H m m1 a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

(* garr8 reads a memory only through the view. *)
Lemma tkw_garr8_ext : forall (H H' : word -> bool) (m m' : word -> option byte) base (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H' m' (base + Z.of_nat j) = aview tfibsegs H m (base + Z.of_nat j)) ->
  garr8 tfibsegs (mrestrict H m) base l -> garr8 tfibsegs (mrestrict H' m') base l.
Proof.
  intros H H' m m' base l E G j Hj. destruct (G j Hj) as [V R]. split; [|exact R].
  intros kk Hk. assert (Ek : kk = 0%nat) by lia. subst kk. specialize (V 0%nat Hk).
  pose proof (E j Hj) as Ej. unfold aview in Ej. cbn [Z.of_nat] in V |- *. rewrite Z.add_0_r in V |- *.
  rewrite V in Ej.
  destruct (mbyte tfibsegs (mrestrict H' m') (base + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in Ej;
    [|discriminate Ej].
  injection Ej as Ej. f_equal. apply bv_eq. rewrite Ej. reflexivity.
Qed.

(* A byte of a list held under garr8, through the view. *)
Lemma tkw_view_garr8 : forall (H : word -> bool) (m : word -> option byte) q (l : list byte) i,
  garr8 tfibsegs (mrestrict H m) q (TW.zs l) -> (i < length l)%nat ->
  aview tfibsegs H m (q + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).
Proof.
  intros H m q l i HG Hi. unfold TW.zs in HG.
  assert (Hm : (i < length (map (fun b : byte => bv_unsigned b) l))%nat) by (rewrite length_map; exact Hi).
  destruct (HG i Hm) as [HV _]. specialize (HV 0%nat ltac:(lia)).
  cbn [Z.of_nat] in HV. rewrite Z.add_0_r in HV.
  unfold aview. rewrite HV. cbn [option_map]. f_equal.
  rewrite (nth_indep (map (fun b : byte => bv_unsigned b) l) 0 (bv_unsigned (Z_to_bv 8 0)))
    by (rewrite length_map; exact Hi).
  rewrite (map_nth (fun b : byte => bv_unsigned b)). rewrite TFE.decode_le_byte1. reflexivity.
Qed.

(* garr8 of a list from the view of each of its bytes. *)
Lemma tkw_garr8_of_view : forall (H : word -> bool) (m : word -> option byte) q (l : list byte),
  (forall i, (i < length l)%nat -> aview tfibsegs H m (q + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0)))) ->
  garr8 tfibsegs (mrestrict H m) q (TW.zs l).
Proof.
  intros H m q l HV j Hj. unfold TW.zs in *. rewrite length_map in Hj.
  rewrite (nth_indep (map (fun b : byte => bv_unsigned b) l) 0 (bv_unsigned (Z_to_bv 8 0)))
    by (rewrite length_map; exact Hj).
  rewrite (map_nth (fun b : byte => bv_unsigned b)).
  pose proof (bv_unsigned_in_range 8 (nth j l (Z_to_bv 8 0))) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R.
  split; [|lia].
  intros kk Hk. assert (Ek : kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite TFE.decode_le_byte1.
  specialize (HV j Hj). unfold aview in HV.
  destruct (mbyte tfibsegs (mrestrict H m) (q + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HV;
    [|discriminate HV].
  injection HV as HV. f_equal. apply bv_eq. exact HV.
Qed.

(* The numbers the walk computes with. *)
Lemma tkw_consts : TAKE_STK = 4624 /\ TRANS_BC_STK = 4400 /\ ESTACK = 4096 /\ TK_FRAME = 224 /\
  TAKE_FRAME = 224 /\ TAKE_BODY = 1484 /\ TAKE_EV = 0 /\ TRANS_BC_EV = 0 /\ TRANS_BC_CID = 2.
Proof. repeat split; reflexivity. Qed.

Lemma tkw_addrs : TK_S = 6158784 /\ TK_MAXC = TK_S + 52 /\ TK_MAXB = TK_S + 56 /\ TK_Q0 = TK_S + 1760 /\
  TK_QD = TK_S + 18144 /\ TK_K = 2147450880 /\ TA_g_s = TK_S /\ TW.OFF_g_s = 1648 /\ TW.SZ_g_s = 18264 /\
  TAKE_S = TK_S.
Proof. repeat split; reflexivity. Qed.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation ajx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation ajd := (@ajournal rc tfib_sink_head segs B).

Hypothesis HCELLS : transport_cells B.
Hypothesis HTC : trans_take_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok segs B G.
Hypothesis HGN : gx_noerrno B G.
Hypothesis AIM : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy).
Hypothesis ABC : forall fx' : YK11.FPState,
  @transport_diginet_body_check_cg fx' rc B MT (transport_sigma TS_diginet_body_check).

(* TransportGCg.v dk_kept_step_g at any world of the walk (the step keeps the current world W2). *)
Lemma tkw_kept_step_g : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) memX memY slo shi
    (Eo Zs : Z -> Prop),
  AR segs B lyc Sc W memc mdc ->
  acall_kept_g segs B G lyc Sc W memc W2 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) memY a = aview segs (w_H W2) memX a) ->
  (forall a, apresent (w_H W2) memX a -> apresent (w_H W2) memY a) ->
  (forall a, Zs a -> YM05.alloc_ceiling <= a < 2 ^ 64 -> slo <= a < shi) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> Zs (b + i) -> Eo (b + i)) ->
  (forall a, Zs a -> in_img segs a -> ~ inG G a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> False) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     Zs a -> Eo a) ->
  acall_kept_g segs B G lyc Sc W memc W2 memY slo shi Eo.
Proof.
intros lyc Sc W memc mdc W2 memX memY slo shi Eo Zs HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZw HZb HZi HZf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [apply K1; [exact Ha | exact Hw] | lia | intros HZ; exact (Hw (HZw a HZ Ha))].
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _).
  rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia | intros HZ; exact (Hn (HZb b m i Hb Hi HZ))].
- intros a Hi HnG Hno He. pose proof (decode_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite Hkp; [apply K3; [exact Hi | exact HnG | exact Hno | exact He] | lia | intros HZ; exact (HZi a HZ Hi HnG Hno He)].
- intros cid pos a Hin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < 2 ^ 64).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | exact Ha | intros HZ; exact (Hn (HZf cid pos a Hin Hr HZ))].
- intros a Ha Hw Hp. apply Hgr. apply K5; [exact Ha | exact Hw | exact Hp].
- intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

Section Call.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (St : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (bp blp hdp allow len hd taken : Z) (body : list byte) (Bw Bw' : list byte).

Hypothesis HJ : ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HRET : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis HRA4 : 4096 <= raZ regs.
Hypothesis HGP : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis HTP : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 TAKE_S.
Hypothesis H11 : YK11.getr regs 11 = w64 bp.
Hypothesis H12 : YK11.getr regs 12 = w64 blp.
Hypothesis H13 : YK11.getr regs 13 = w64 allow.
Hypothesis H14 : YK11.getr regs 14 = w64 hdp.
Hypothesis HAL : spZ regs mod 16 = 0.
Hypothesis HWLO : sp0 - STK <= spZ regs - TAKE_STK.
Hypothesis HWHI : spZ regs <= sp0.
Hypothesis HALW : - 2 ^ 31 <= allow < 2 ^ 31.
Hypothesis HBP0 : 0 < bp.
Hypothesis HFAKE : decode_in_fake lyc Sc bp TAKE_BODY.
Hypothesis HTWB : transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc (spZ regs) bp TAKE_BODY.
Hypothesis HRDB : decode_rd_ok W memc bp TAKE_BODY.
Hypothesis HOWB : decode_off_win regs TAKE_STK bp TAKE_BODY.
Hypothesis HNGB : forall x, bp <= x < bp + TAKE_BODY -> ~ inG G x.
Hypothesis HBL8 : blp mod 8 = 0.
Hypothesis HTWL : transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc (spZ regs) blp 8.
Hypothesis HRDL : decode_rd_ok W memc blp 8.
Hypothesis HOWL : decode_off_win regs TAKE_STK blp 8.
Hypothesis HNGL : forall x, blp <= x < blp + 8 -> ~ inG G x.
Hypothesis HHD4 : hdp mod 4 = 0.
Hypothesis HTWH : transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc (spZ regs) hdp 4.
Hypothesis HRDH : decode_rd_ok W memc hdp 4.
Hypothesis HOWH : decode_off_win regs TAKE_STK hdp 4.
Hypothesis HNGH : forall x, hdp <= x < hdp + 4 -> ~ inG G x.
Hypothesis SEP1 : bp + TAKE_BODY <= blp \/ blp + 8 <= bp.
Hypothesis SEP2 : bp + TAKE_BODY <= hdp \/ hdp + 4 <= bp.
Hypothesis SEP3 : blp + 8 <= hdp \/ hdp + 4 <= blp.
Hypothesis HW : tw_at TMAP_A (aview segs (w_H W) memc) Bw.
Hypothesis HGF : TW.g_fail_next Bw <= 1.
Hypothesis HQL : forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN.
Hypothesis HMC : 1 <= TW.S_cfg_max_cmds Bw.
Hypothesis HMB : 1 <= TW.S_cfg_max_body Bw.
Hypothesis HCNT : count_cid TRANS_BC_CID (frames Sc) < fs_frames TRANS_BC_CID.
Hypothesis HNEV : st_nev St + k + TAKE_EV <= EV_MAX.

(* The model's run, as take_seg_model.v tkm_take_m reads it off take_m. *)
Variables (BF : list byte) (keptF : Z).
Hypothesis HLP : TS0.take_loop_m Bw allow 0 0 0 0 0 [] (Z.to_nat (TW.S_queued Bw)) =
  Some (BF, (body, len, hd, taken, keptF)).
Hypothesis HBW' : Bw' = TW.set_S_queued BF keptF.
Hypothesis HFF : tkm_wf BF /\ TW.S_queued BF = TW.S_queued Bw /\ TW.g_fail_next BF = TW.g_fail_next Bw /\
  0 <= taken /\ 0 <= keptF /\ taken + keptF = TW.S_queued Bw /\ 0 <= TW.S_queued Bw <= TW.S_queue_N /\
  0 <= len <= TS0.DIGINET_MAX_BODY_LEN /\ Z.of_nat (length body) = len /\ 0 <= hd < 256 /\
  TW.g_fail_next Bw' = TW.g_fail_next Bw.

Local Abbreviation sp := (spZ regs).
Local Abbreviation SP' := (spZ regs - TK_FRAME).
Local Abbreviation OUTS := [(blp, 8); (hdp, 4)].
Local Abbreviation EW := (take_wr Bw bp blp hdp).
Local Abbreviation GP := (YK11.getr regs (Z_to_bv 5 3)).
Local Abbreviation TP := (YK11.getr regs (Z_to_bv 5 4)).
Local Abbreviation Q := (@transport_take_post fx rc B MT STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc k regs bp blp
  hdp Bw Bw' body len hd taken).

(* The saved s11 .. s0 and ra the prologue stores at sp + 120 .. sp + 216. *)
Definition tk_sv : list word.
Proof using All.
  exact (
    tk_saved (YK11.getr regs (Z_to_bv 5 27)) (YK11.getr regs (Z_to_bv 5 26)) (YK11.getr regs (Z_to_bv 5 25))
      (YK11.getr regs (Z_to_bv 5 24)) (YK11.getr regs (Z_to_bv 5 23)) (YK11.getr regs (Z_to_bv 5 22))
      (YK11.getr regs (Z_to_bv 5 21)) (YK11.getr regs (Z_to_bv 5 20)) (YK11.getr regs (Z_to_bv 5 19))
      (YK11.getr regs (Z_to_bv 5 18)) (YK11.getr regs (Z_to_bv 5 9)) (YK11.getr regs (Z_to_bv 5 8))
      (YK11.getr regs (Z_to_bv 5 1))
  ).
Defined.

(* ---- the running invariant ---- *)

Definition tkw_inv (Wc : world segs) (m : word -> option byte) (md : Model) (B1 : list byte) (hd1 : Z)
    (X : list byte) (ws : list word) : Prop.
Proof using All.
  exact (
    exists ly2 S2,
      ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k /\
      frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ mo_le MT Sc S2 0 /\
      acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW /\
      tw_at TMAP_A (aview segs (w_H Wc) m) B1 /\
      length ws = 15%nat /\ rw_cells rsegs m SP' (tk_fr (ws ++ tk_sv)) /\
      rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd1)] /\
      (exists jb, rw_cells rsegs m blp [CB 8 jb]) /\
      length X = 1484%nat /\ garr8 segs (mrestrict (w_H Wc) m) bp (TW.zs X)
  ).
Defined.

(* The model at the loop head, turn i with fuel n. *)
Definition tkw_mw (B1 : list byte) : Prop.
Proof using All.
  exact (
    tkm_wf B1 /\ TW.S_queued B1 = TW.S_queued Bw /\ TW.S_cfg_max_cmds B1 = TW.S_cfg_max_cmds Bw /\
    TW.S_cfg_max_body B1 = TW.S_cfg_max_body Bw /\ TW.g_fail_next B1 = TW.g_fail_next Bw
  ).
Defined.

Definition tkw_mh (n : nat) (B1 : list byte) (i taken1 kept1 len1 hd1 : Z) (body1 X : list byte) : Prop.
Proof using All.
  exact (
    tkw_mw B1 /\ (forall j, i <= j < TW.S_queued Bw -> TW.S_queue_len B1 j <= 24) /\
    0 <= i /\ 0 <= taken1 /\ 0 <= kept1 /\ taken1 + kept1 = i /\ (taken1 = 0 -> len1 = 0) /\
    0 <= len1 <= 1484 /\ Z.of_nat (length body1) = len1 /\ 0 <= hd1 < 256 /\
    i + Z.of_nat n = TW.S_queued Bw /\ firstn (Z.to_nat len1) X = body1 /\
    TS0.take_loop_m B1 allow i taken1 kept1 len1 hd1 body1 n = Some (BF, (body, len, hd, taken, keptF))
  ).
Defined.

(* What remains after turn i (take_loop_m's test of :377). *)
Definition tkw_next (B1 : list byte) (i taken1 kept1 len1 hd1 : Z) (body1 : list byte) (n : nat)
    : option (list byte * (list byte * Z * Z * Z * Z)).
Proof using All.
  exact (
    if (taken1 =? TW.S_cfg_max_cmds B1) || (len1 =? TW.S_cfg_max_body B1) then
      match TS0.take_tail_m B1 kept1 (i + 1) (Z.to_nat (TW.S_queued B1 - (i + 1))) with
      | None => None
      | Some (B2, kept2) => Some (B2, (body1, len1, hd1, taken1, kept2))
      end
    else TS0.take_loop_m B1 allow (i + 1) taken1 kept1 len1 hd1 body1 n
  ).
Defined.

(* The model at the end of turn i (after the take or the refusal), with fuel n left. *)
Definition tkw_mj (n : nat) (B1 : list byte) (i taken1 kept1 len1 hd1 : Z) (body1 X : list byte) : Prop.
Proof using All.
  exact (
    tkw_mw B1 /\ (forall j, i + 1 <= j < TW.S_queued Bw -> TW.S_queue_len B1 j <= 24) /\
    0 <= i < 512 /\ 0 <= taken1 /\ 0 <= kept1 /\ taken1 + kept1 = i + 1 /\ (taken1 = 0 -> len1 = 0) /\
    0 <= len1 <= 1484 /\ Z.of_nat (length body1) = len1 /\ 0 <= hd1 < 256 /\
    i + 1 + Z.of_nat n = TW.S_queued Bw /\ firstn (Z.to_nat len1) X = body1 /\
    tkw_next B1 i taken1 kept1 len1 hd1 body1 n = Some (BF, (body, len, hd, taken, keptF))
  ).
Defined.

(* The model in the tail loop at turn j with fuel nt. *)
Definition tkw_mt (nt : nat) (B1 : list byte) (j kept1 : Z) (X : list byte) : Prop.
Proof using All.
  exact (
    tkm_wf B1 /\ TW.S_queued B1 = TW.S_queued Bw /\ TW.g_fail_next B1 = TW.g_fail_next Bw /\
    0 <= kept1 < j /\ j + Z.of_nat nt = TW.S_queued Bw /\ firstn (Z.to_nat len) X = body /\
    TS0.take_tail_m B1 kept1 j nt = Some (BF, keptF)
  ).
Defined.

(* ---- what the journal gives at any state of the walk ---- *)

Lemma tkw_jd : forall ly2 S2 (Wc : world segs) m md,
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  exists memS, ajd STK sp0 FP ly St W0 memS md0 own ly2 S2 Wc m md k.
Proof.
  intros ly2 S2 Wc m md J.
  destruct (gx_open segs B G STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k J) as (memS & HJi & _ & _).
  exists memS. exact HJi.
Qed.

Lemma tkw_jf : forall ly2 S2 (Wc : world segs) m md,
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  AR segs B ly2 S2 Wc m md /\ layout_le (length (st_secs St)) ly ly2 /\ frames S2 = own ++ frames St /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) m a) /\ astk_ok STK ly sp0.
Proof.
  intros ly2 S2 Wc m md J. destruct (tkw_jd ly2 S2 Wc m md J) as (memS & HJi).
  destruct HJi as (HAR & Hly & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & Hpr & Hstk & _).
  split; [exact HAR|]. split; [exact Hly|]. split; [exact Hfr|]. split; [exact Hpr | exact Hstk].
Qed.

Lemma tkw_lay : forall ly2 S2 (Wc : world segs) m md,
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) /\
  ly_stk_lo ly2 = ly_stk_lo ly /\ ly_stk_hi ly2 = ly_stk_hi ly.
Proof.
  intros ly2 S2 Wc m md J.
  destruct (tkw_jf _ _ _ _ _ J) as (_ & L2 & _). destruct (tkw_jf _ _ _ _ _ HJ) as (_ & L0 & _).
  destruct L2 as (_ & _ & _ & _ & _ & F2 & _ & _ & _ & Elo & Ehi & _).
  destruct L0 as (_ & _ & _ & _ & _ & F0 & _).
  split; [intros cid pos; unfold frame_addr; rewrite F2, F0; reflexivity | split; [exact Elo | exact Ehi]].
Qed.

Lemma tkw_AR0 : AR segs B lyc Sc W memc mdc.
Proof. exact (proj1 (tkw_jf _ _ _ _ _ HJ)). Qed.

Lemma tkw_spf : YM05.alloc_ceiling <= sp0 - STK /\ sp0 - STK <= sp - TAKE_STK /\ sp <= sp0 /\ sp0 <= 2 ^ 47 /\
  sp0 mod 16 = 0 /\ 0 <= STK /\ ly_stk_lo ly <= sp0 - STK /\ sp0 <= ly_stk_hi ly.
Proof.
  destruct (tkw_jf _ _ _ _ _ HJ) as (_ & _ & _ & _ & (H16 & Hs0 & Hce & Hlo & Hhi & H47 & _)).
  pose proof HWLO as A1. pose proof HWHI as A2. repeat split; lia.
Qed.

Lemma tkw_cellf : 0 <= bp /\ bp + 1484 <= 2 ^ 63 /\ amem_range bp 1484 /\ 4096 <= bp /\
  bp + 1484 <= YM05.alloc_ceiling /\
  0 <= blp /\ blp + 8 <= 2 ^ 63 /\ amem_range blp 8 /\ 0 <= hdp /\ hdp + 4 <= 2 ^ 63 /\ amem_range hdp 4 /\
  (blp + 8 <= sp - TAKE_STK \/ sp <= blp) /\ (hdp + 4 <= sp - TAKE_STK \/ sp <= hdp).
Proof.
  pose proof HRDB as (_ & _ & _ & BM & B0 & B63). pose proof HRDL as (_ & _ & _ & LM & L0 & L63).
  pose proof HRDH as (_ & _ & _ & HM & H0 & H63).
  destruct HFAKE as (cid & pos & Hin & F1 & F2).
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos tkw_AR0 Hin) as (F4096 & Fce & _).
  pose proof HOWL as OL. pose proof HOWH as OH. unfold decode_off_win, TAKE_BODY in *.
  repeat split; first [exact BM | exact LM | exact HM | exact OL | exact OH | lia].
Qed.

(* ---- the bytes of G, of the out cells, of the written range ---- *)

Lemma tkw_inG_gs : forall a, TA_g_s <= a < TA_g_s + 18264 -> inG G a.
Proof.
  intros a Ha. unfold inG, TG.G_HARNESS. apply Exists_exists. exists (0x5df9c0, 18264). split.
  - do 9 right. left. reflexivity.
  - unfold in_zr, TA_g_s in *. cbn [fst snd]. lia.
Qed.

Lemma tkw_G_low : forall a, inG G a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. exact (inG_low segs B decode_segs_low G a HGX Ha). Qed.

Lemma tkw_G_vis : forall (Wc : world segs) a, inG G a -> w_H Wc (Z_to_bv 64 a) = false.
Proof.
  intros Wc a Ha. apply hidden_not_img. pose proof (tkw_G_low a Ha) as Hl.
  rewrite unsigned_lit by (unfold kLowMemEnd in Hl; lia). exact (trans_g_img a Ha).
Qed.

Lemma tkw_outs : forall a, inG OUTS a <-> (blp <= a < blp + 8 \/ hdp <= a < hdp + 4).
Proof. intros a. rewrite !inG_cons. unfold in_zr. cbn [fst snd]. pose proof (inG_nil a). tauto. Qed.

Lemma tkw_EW : forall a, EW a ->
  (TA_g_s + 1760 <= a < TA_g_s + 18148 /\ inG G a) \/ (bp <= a < bp + 1484) \/ inG OUTS a.
Proof.
  intros a [(q & Hq & _ & Hf) | [Hf | [Hb | [Hl | Hh]]]].
  - left. unfold twa_fld, TW.A_S_queue_bytes, TW.OFF_g_s, TW.S_queue_ESZ, TW.S_queue_N in *.
    split; [lia|]. apply tkw_inG_gs. lia.
  - left. unfold twa_fld, TW.A_S_queued, TW.OFF_g_s in Hf. split; [lia|]. apply tkw_inG_gs. lia.
  - right; left. unfold TAKE_BODY in Hb. exact Hb.
  - right; right. apply tkw_outs. left. exact Hl.
  - right; right. apply tkw_outs. right. exact Hh.
Qed.

(* An awr_byte of the call state is one of every later state of the walk (the same frames and blocks). *)
Lemma tkw_rel_awr : forall ly2 S2 (Wc : world segs) m md a,
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  awr_byte STK sp0 FP (ablocks B ly St) (ablocks B lyc Sc) lyc own a ->
  awr_byte STK sp0 FP (ablocks B ly St) (ablocks B ly2 S2) ly2 own a.
Proof.
  intros ly2 S2 Wc m md a J HP Haw.
  destruct (tkw_lay ly2 S2 Wc m md J) as (Hfa & _ & _).
  assert (HI : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym HP) Hbm)).
  destruct Haw as [Hw | [(HF & b & n & Hin & Hb) | [(b & n & Hin & Hn & Hb) | (cid & pos & Hin & Hr)]]].
  - left. exact Hw.
  - right; left. split; [exact HF|]. exists b, n. split; [exact (HI _ Hin) | exact Hb].
  - right; right; left. exists b, n. split; [exact (HI _ Hin)|]. split; [exact Hn | exact Hb].
  - right; right; right. exists cid, pos. split; [exact Hin|]. rewrite Hfa. exact Hr.
Qed.

(* A byte of a cell the caller lets take write (transport_twr_ok_g): an awr_byte of every later state, present
   there, present at the call. *)
Lemma tkw_twr_cur : forall q n ly2 S2 (Wc : world segs) m md a,
  transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc sp q n ->
  (forall x, q <= x < q + n -> ~ inG G x) -> q <= a < q + n ->
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  awr_byte STK sp0 FP (ablocks B ly St) (ablocks B ly2 S2) ly2 own a /\ apresent (w_H Wc) m a /\
  apresent (w_H W) memc a /\ ~ (sp - ESTACK <= a < sp).
Proof.
  intros q n ly2 S2 Wc m md a HT HN Ha J HP.
  destruct (HT a Ha) as [(Haw & Hp0 & _ & Hes) | HGa]; [|exfalso; exact (HN a Ha HGa)].
  pose proof (tkw_rel_awr ly2 S2 Wc m md a J HP Haw) as Haw2.
  destruct (tkw_jd ly2 S2 Wc m md J) as (memS & HJi).
  destruct (awr_byte_present segs B LAWS STK sp0 FP ly St W0 memS md0 own ly2 S2 Wc m md k a HJi Haw2) as [Hp _].
  split; [exact Haw2|]. split; [exact Hp|]. split; [exact Hp0 | exact Hes].
Qed.

Lemma tkw_win_pres : forall ly2 S2 (Wc : world segs) m md a,
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  sp - TAKE_STK <= a < sp -> apresent (w_H Wc) m a.
Proof.
  intros ly2 S2 Wc m md a J Ha. destruct (tkw_jf _ _ _ _ _ J) as (_ & _ & _ & Hpr & _).
  apply Hpr. pose proof tkw_spf. lia.
Qed.

(* ---- views and overlays ---- *)

Lemma tkw_aview_H : forall (H H' : word -> bool) (m : word -> option byte) a,
  H (Z_to_bv 64 a) = false -> H' (Z_to_bv 64 a) = false -> aview segs H' m a = aview segs H m a.
Proof. intros H H' m a E E'. unfold aview, mbyte, mrestrict. rewrite E, E'. reflexivity. Qed.

Lemma tkw_gover_apresent : forall outs (H : word -> bool) (ma mb : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ inG outs a -> apresent H ma a -> apresent H (gover outs ma mb) a.
Proof.
  intros outs H ma mb a Ha Hn (Hh & b & Hb). split; [exact Hh|]. exists b.
  rewrite (gover_out_mem outs ma mb a Ha Hn). exact Hb.
Qed.

Lemma tkw_gover_in : forall outs (ma mb : word -> option byte) a, 0 <= a < 2 ^ 64 -> inG outs a ->
  gover outs ma mb (Z_to_bv 64 a) = mb (Z_to_bv 64 a).
Proof.
  intros outs ma mb a Ha Hin. unfold gover. rewrite unsigned_lit by lia.
  rewrite (proj2 (inGb_spec outs a) Hin). reflexivity.
Qed.

(* Two present bytes with one view: rw_cells carried over. *)
Lemma tkw_cells_keep : forall (H H' : word -> bool) (m m1 : word -> option byte) A cs,
  rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> apresent H m (A + i) /\ apresent H' m1 (A + i) /\
     aview segs H' m1 (A + i) = aview segs H m (A + i)) ->
  rw_cells rsegs m1 A cs.
Proof.
  intros H H' m m1 A cs HC HE. apply (TFE.decode_rw_cells_eq m m1 A cs HC).
  intros i Hi. destruct (HE i Hi) as (P1 & P2 & E). exact (TFE.decode_byte_eq H H' m m1 (A + i) P1 P2 E).
Qed.

(* ---- the kept fact across a step of the walk that writes its window and the written range ---- *)

Lemma tkw_K_step : forall (Wc : world segs) m m1,
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TAKE_STK <= a < sp) -> ~ EW a ->
     aview segs (w_H Wc) m1 a = aview segs (w_H Wc) m a) ->
  (forall a, apresent (w_H Wc) m a -> apresent (w_H Wc) m1 a) ->
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m1 memc) (sp - TAKE_STK) sp EW.
Proof.
  intros Wc m m1 K HV HP.
  pose proof tkw_spf as (S1 & S2 & S3 & S4 & _). pose proof tkw_cellf as (_ & _ & _ & B4 & Bce & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof tkw_AR0 as HAR0.
  apply (tkw_kept_step_g lyc Sc W memc mdc Wc (gover OUTS m memc) (gover OUTS m1 memc) (sp - TAKE_STK) sp EW
           (fun a => (sp - TAKE_STK <= a < sp) \/ (EW a /\ ~ inG OUTS a)) HAR0 K).
  - intros a Ha HZ. destruct (inGb OUTS a) eqn:Eo.
    + apply aview_eq_of. unfold mrestrict.
      rewrite !(tkw_gover_in OUTS _ memc a Ha (proj1 (inGb_spec OUTS a) Eo)). reflexivity.
    + assert (Hn : ~ inG OUTS a) by (apply inGb_false; exact Eo).
      rewrite !(gover_out_aview segs OUTS (w_H Wc) _ memc a Ha Hn).
      apply HV; [exact Ha | intros Hw; apply HZ; left; exact Hw |].
      intros He; apply HZ; right; split; [exact He | exact Hn].
  - intros a Hp. revert Hp. unfold apresent, gover.
    destruct (inGb OUTS (bv_unsigned (Z_to_bv 64 a))); [tauto|]. intros Hp. exact (HP a Hp).
  - intros a [Hw | (He & Hn)] Hc; [exact Hw|]. exfalso.
    destruct (tkw_EW a He) as [(R & _) | [R | R]]; [unfold TA_g_s in R; lia | lia | exact (Hn R)].
  - intros b mm i Hb Hi [Hw | (He & _)]; [|exact He]. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b mm HAR0 Hb) as (_ & _ & Hce & _).
    pose proof (req_size_pos mm) as Hr. destruct (Z_le_gt_dec 0 mm) as [Hm|Hm].
    + specialize (Hr Hm). lia.
    + unfold req_size in *. destruct (Z.eqb_spec mm 0); lia.
  - intros a [Hw | (He & Hn)] Hi HnG _ _.
    + pose proof (decode_segs_low a Hi). unfold kLowMemEnd in *. lia.
    + destruct (tkw_EW a He) as [(_ & HG) | [R | R]]; [exact (HnG HG) | | exact (Hn R)].
      destruct HFAKE as (cid & pos & Hin & F1 & F2).
      exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR0 Hin ltac:(unfold TAKE_BODY in *; lia) Hi).
  - intros cid pos a Hin Hr [Hw | (He & _)]; [|exact He]. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR0 Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* ---- the shadow of the caller's frame bytes, kept from the call ---- *)

Lemma tkw_fsh : forall (Wc : world segs) m s,
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW ->
  forall cid pos, In (cid, pos) (frames Sc) ->
  in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
  aview segs (w_H Wc) m s = aview segs (w_H W) memc s.
Proof.
  intros Wc m s K cid pos Hin Hs.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos tkw_AR0 Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as Hdp.
  pose proof tkw_cellf as (_ & _ & BM & _ & _ & _ & _ & LM & _ & _ & HM & _).
  unfold in_zr in Hs. cbn [fst snd] in Hs.
  assert (Hsr : kLowMemEnd <= s < kHighShadowEnd).
  { unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  assert (HnO : ~ inG OUTS s) by (rewrite tkw_outs; unfold amem_range in *; lia).
  assert (HnE : ~ EW s).
  { intros He. destruct (tkw_EW s He) as [(R & _) | [R | R]];
      [unfold TA_g_s in R; lia | unfold amem_range in BM; lia | exact (HnO R)]. }
  destruct K as (_ & _ & _ & K4 & _).
  rewrite <- (gover_out_aview segs OUTS (w_H Wc) m memc s ltac:(lia) HnO).
  exact (K4 cid pos s Hin (or_intror Hs) HnE).
Qed.

(* The two shadow facts of a range inside the body at any state of the walk. *)
Lemma tkw_body_sh : forall (Wc : world segs) m q n,
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW ->
  bp <= q -> q + n <= bp + TAKE_BODY -> 0 < n ->
  range_addressable (aview segs (w_H Wc) m) SHADOW_OFF q n /\ shadow_hull_vis (aview segs (w_H Wc) m) q n.
Proof.
  intros Wc m q n K H1 H2 Hn.
  destruct HFAKE as (cid & pos & Hin & F1 & F2).
  destruct (dkg_frame_al64 segs B lyc Sc W memc mdc cid pos tkw_AR0 Hin) as (A1 & A2 & A3).
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos tkw_AR0 Hin) as (B1 & B2 & _).
  pose proof (trans_rd_ok_sub W memc bp TAKE_BODY q n HRDB H1 H2 ltac:(lia)) as (R1 & R2 & R3 & R4 & R5 & R6).
  assert (KG : forall g, frame_addr lyc cid pos <= g < frame_addr lyc cid pos + fs_frame_bytes cid ->
    aview segs (w_H Wc) m (shadow_addr g) = aview segs (w_H W) memc (shadow_addr g)).
  { intros g Hg. apply (tkw_fsh Wc m (shadow_addr g) K cid pos Hin). unfold in_zr, shadow_addr. cbn [fst snd].
    pose proof (Z.div_mod (frame_addr lyc cid pos) 64 ltac:(lia)).
    pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)).
    pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia)).
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
    pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.mod_pos_bound g 8 ltac:(lia)). lia. }
  split.
  - intros x Hx. destruct (R2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs |- *.
    rewrite (KG x ltac:(unfold TAKE_BODY in *; lia)). exact Hs.
  - intros s Hs.
    assert (Hhi : (frame_addr lyc cid pos + fs_frame_bytes cid) mod 64 = 0)
      by (rewrite Z.add_mod, A1, A2 by lia; reflexivity).
    destruct (YG0s.hull_inside (frame_addr lyc cid pos) (frame_addr lyc cid pos + fs_frame_bytes cid) q n s
      A1 Hhi ltac:(lia) ltac:(unfold TAKE_BODY in *; lia) ltac:(unfold TAKE_BODY in *; lia) ltac:(lia) Hs)
      as (g & Hg8 & Hgr & ->).
    rewrite (KG g Hgr). exact (R3 _ Hs).
Qed.

(* range_addressable of a cell the caller lets take write, at any state of the walk: a byte of the caller's
   window is machine stack (stack_zshadow_ra), a block byte's shadow is the block's (AR_laws), a byte of an own
   side-stack frame has the shadow kept from the call (tkw_fsh); the shadow of a frame is not application memory. *)
Lemma tkw_cell_ra : forall q n ly2 S2 (Wc : world segs) m md,
  transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc sp q n ->
  (forall x, q <= x < q + n -> ~ inG G x) -> decode_rd_ok W memc q n ->
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW ->
  range_addressable (aview segs (w_H Wc) m) SHADOW_OFF q n.
Proof.
  intros q n ly2 S2 Wc m md HT HN RD J HP K x Hx.
  pose proof RD as (RV & RRA & RH & RM & R0 & R63).
  destruct (HT x Hx) as [(Haw & _ & _ & _) | HGx]; [|exfalso; exact (HN x Hx HGx)].
  destruct (tkw_jf _ _ _ _ _ J) as (HAR2 & _ & _ & _ & _).
  destruct (tkw_jf _ _ _ _ _ HJ) as (HAR0 & _ & Hfr0 & _ & _).
  destruct (tkw_lay _ _ _ _ _ J) as (_ & Elo & Ehi).
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Haw as [Hwin | [(_ & b & mm & Hin & Hb) | [(b & mm & Hin & _ & Hb) | (cid & pos & Hin & Hfr)]]].
  - destruct (stack_zshadow_ra B ly2 S2 Wc m md x 1 HAR2 ltac:(lia) ltac:(rewrite Elo; lia)
      ltac:(rewrite Ehi; lia)) as [RA _].
    exact (RA x ltac:(lia)).
  - exact (range_addressable_of_block segs B LAWS ly2 S2 Wc m md b mm x 1 HAR2
      (Permutation_in _ (Permutation_sym HP) Hin) ltac:(lia) ltac:(lia) x ltac:(lia)).
  - exact (range_addressable_of_block segs B LAWS ly2 S2 Wc m md b mm x 1 HAR2
      (Permutation_in _ (Permutation_sym HP) Hin) ltac:(lia) ltac:(lia) x ltac:(lia)).
  - assert (HinS : In (cid, pos) (frames Sc)) by (rewrite Hfr0; apply in_or_app; left; exact Hin).
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR0 HinS) as (F4 & Fce & _).
    destruct (dkg_frame_al64 segs B lyc Sc W memc mdc cid pos HAR0 HinS) as (A1 & A2 & A3).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hfr as [Hfr | Hfr]; unfold in_zr in Hfr; cbn [fst snd] in Hfr.
    + destruct (RRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
      rewrite (tkw_fsh Wc m (shadow_of_addr SHADOW_OFF x) K cid pos HinS); [exact Hs|].
      unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
      pose proof (Z.div_mod (frame_addr lyc cid pos) 64 ltac:(lia)).
      pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)).
      pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia)).
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
      pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
    + exfalso. pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF, amem_range in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* decode_rd_ok of a non-empty range inside the body at any state of the walk. *)
Lemma tkw_rd_cur : forall (Wc : world segs) m (X : list byte) q n,
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW ->
  garr8 segs (mrestrict (w_H Wc) m) bp (TW.zs X) -> length X = 1484%nat ->
  bp <= q -> q + n <= bp + TAKE_BODY -> 0 < n -> decode_rd_ok Wc m q n.
Proof.
  intros Wc m X q n K GX LX H1 H2 Hn.
  pose proof tkw_cellf as (B0 & B63 & BM & B4 & Bce & _).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & E5 & E6 & _).
  destruct (tkw_body_sh Wc m q n K H1 H2 Hn) as [RA HH].
  pose proof HRDB as (_ & _ & _ & _ & R0 & R63).
  split; [|split; [exact RA | split; [exact HH | split; [|split; lia]]]].
  - intros a Ha. replace a with (bp + Z.of_nat (Z.to_nat (a - bp))) by lia.
    rewrite (tkw_view_garr8 (w_H Wc) m bp X (Z.to_nat (a - bp)) GX ltac:(lia)). discriminate.
  - unfold amem_range in BM |- *. destruct BM as [BMa|BMa]; [left; lia | right; lia].
Qed.

(* ---- across the call of diginet_body_check ---- *)

(* A byte of a cell the caller lets take write is kept by the callee (outside its window, E empty). *)
Lemma tkw_cell_bc : forall q n ly2 S2 (Wc : world segs) m md (W2 : world segs) m2 a,
  transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc sp q n ->
  (forall x, q <= x < q + n -> ~ inG G x) -> decode_rd_ok W memc q n ->
  (q + n <= sp - TAKE_STK \/ sp <= q) -> q <= a < q + n ->
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  acall_kept_g segs B G ly2 S2 Wc m W2 m2 (SP' - TRANS_BC_STK) SP' (fun _ => False) ->
  aview segs (w_H W2) m2 a = aview segs (w_H Wc) m a.
Proof.
  intros q n ly2 S2 Wc m md W2 m2 a HT HN RD HO Ha J HP HF KB.
  pose proof RD as (_ & _ & _ & RM & R0 & R63).
  destruct (HT a Ha) as [(Haw & _ & _ & _) | HGa]; [|exfalso; exact (HN a Ha HGa)].
  destruct KB as (L1 & L2 & _ & L4 & _).
  destruct (tkw_jf _ _ _ _ _ HJ) as (HAR0 & _ & Hfr0 & _ & _).
  destruct (tkw_lay _ _ _ _ _ J) as (Hfa & _ & _).
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Haw as [Hwin | [(_ & b & mm & Hin & Hb) | [(b & mm & Hin & _ & Hb) | (cid & pos & Hin & Hfr)]]].
  - apply L1; lia.
  - replace a with (b + (a - b)) by lia.
    exact (L2 b mm (a - b) (Permutation_in _ (Permutation_sym HP) Hin) ltac:(lia) (fun H => H)).
  - replace a with (b + (a - b)) by lia.
    exact (L2 b mm (a - b) (Permutation_in _ (Permutation_sym HP) Hin) ltac:(lia) (fun H => H)).
  - assert (HinS : In (cid, pos) (frames Sc)) by (rewrite Hfr0; apply in_or_app; left; exact Hin).
    destruct Hfr as [Hfr | Hfr].
    + apply (L4 cid pos a ltac:(rewrite HF; exact HinS)); [|intros []].
      left. unfold in_zr, frame_rng in *. cbn [fst snd] in *. rewrite Hfa. exact Hfr.
    + exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR0 HinS) as (F4 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs. unfold in_zr in Hfr. cbn [fst snd] in Hfr.
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF, amem_range in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* The body's bytes lie in a caller's side-stack frame: kept by the callee. *)
Lemma tkw_body_bc : forall ly2 S2 (Wc : world segs) m md (W2 : world segs) m2 a,
  bp <= a < bp + TAKE_BODY ->
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k -> frames S2 = frames Sc ->
  acall_kept_g segs B G ly2 S2 Wc m W2 m2 (SP' - TRANS_BC_STK) SP' (fun _ => False) ->
  aview segs (w_H W2) m2 a = aview segs (w_H Wc) m a.
Proof.
  intros ly2 S2 Wc m md W2 m2 a Ha J HF (_ & _ & _ & L4 & _).
  destruct HFAKE as (cid & pos & Hin & F1 & F2).
  destruct (tkw_lay _ _ _ _ _ J) as (Hfa & _ & _).
  apply (L4 cid pos a ltac:(rewrite HF; exact Hin)); [|intros []].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa. lia.
Qed.

(* take's own frame lies above the callee's window, at or above alloc_ceiling. *)
Lemma tkw_frame_bc : forall ly2 S2 (Wc : world segs) m (W2 : world segs) m2 a,
  SP' <= a < sp ->
  acall_kept_g segs B G ly2 S2 Wc m W2 m2 (SP' - TRANS_BC_STK) SP' (fun _ => False) ->
  aview segs (w_H W2) m2 a = aview segs (w_H Wc) m a.
Proof.
  intros ly2 S2 Wc m W2 m2 a Ha (L1 & _).
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & _). pose proof tkw_consts as (E1 & E2 & E3 & E4 & _).
  apply L1; lia.
Qed.

(* The kept fact across the call: the callee's acall_kept_g (at the call state ly2 S2, which has the call state's
   frames, blocks and frame addresses) composed with the walk's, at the overlaid memories. The out cells are
   visible at both states and their entry bytes put back on both sides. *)
Lemma tkw_K_bc : forall ly2 S2 (Wc : world segs) m md ly3 S3 (W2 : world segs) m2 md2,
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly3 S3 W2 m2 md2 k ->
  Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) ->
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW ->
  acall_kept_g segs B G ly2 S2 Wc m W2 m2 (SP' - TRANS_BC_STK) SP' (fun _ => False) ->
  acall_kept_g segs B G lyc Sc W memc W2 (gover OUTS m2 memc) (sp - TAKE_STK) sp EW.
Proof.
  intros ly2 S2 Wc m md ly3 S3 W2 m2 md2 J2 HP2 HF2 J3 HP3 K KB.
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & _). pose proof tkw_consts as (E1 & E2 & E3 & E4 & _).
  pose proof tkw_cellf as (_ & _ & _ & _ & _ & L0 & L63 & _ & H0 & H63 & _ & OL & OH).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof tkw_AR0 as HAR0.
  destruct (tkw_lay _ _ _ _ _ J2) as (Hfa & _ & _).
  assert (HOV : forall a, inG OUTS a -> w_H Wc (Z_to_bv 64 a) = false /\ w_H W2 (Z_to_bv 64 a) = false /\
    apresent (w_H W) memc a /\ 0 <= a < 2 ^ 64 /\ ~ (sp - TAKE_STK <= a < sp)).
  { intros a Ha. apply tkw_outs in Ha. destruct Ha as [Ha | Ha].
    - destruct (tkw_twr_cur blp 8 ly2 S2 Wc m md a HTWL HNGL Ha J2 HP2) as (_ & (Hh & _) & Hp0 & _).
      destruct (tkw_twr_cur blp 8 ly3 S3 W2 m2 md2 a HTWL HNGL Ha J3 HP3) as (_ & (Hh2 & _) & _ & _).
      split; [exact Hh|]. split; [exact Hh2|]. split; [exact Hp0|]. split; lia.
    - destruct (tkw_twr_cur hdp 4 ly2 S2 Wc m md a HTWH HNGH Ha J2 HP2) as (_ & (Hh & _) & Hp0 & _).
      destruct (tkw_twr_cur hdp 4 ly3 S3 W2 m2 md2 a HTWH HNGH Ha J3 HP3) as (_ & (Hh2 & _) & _ & _).
      split; [exact Hh|]. split; [exact Hh2|]. split; [exact Hp0|]. split; lia. }
  assert (EQO : forall a, inG OUTS a ->
    aview segs (w_H W2) (gover OUTS m2 memc) a = aview segs (w_H Wc) (gover OUTS m memc) a).
  { intros a Ha. destruct (HOV a Ha) as (Q1 & Q2 & _ & HR & _).
    unfold aview, mbyte, mrestrict. rewrite Q1, Q2. rewrite !(tkw_gover_in OUTS _ memc a HR Ha). reflexivity. }
  assert (KB' : acall_kept_g segs B G lyc Sc Wc (gover OUTS m memc) W2 (gover OUTS m2 memc)
                  (SP' - TRANS_BC_STK) SP' (fun _ => False)).
  { destruct KB as (L1 & L2 & L3 & L4 & L5 & L6).
    split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hw. destruct (inGb OUTS a) eqn:Eo; [exact (EQO a (proj1 (inGb_spec _ _) Eo))|].
      assert (Hn : ~ inG OUTS a) by (apply inGb_false; exact Eo).
      rewrite !(gover_out_aview segs OUTS _ _ memc a ltac:(lia) Hn). exact (L1 a Ha Hw).
    - intros b mm i Hb Hi Hn. destruct (inGb OUTS (b + i)) eqn:Eo; [exact (EQO _ (proj1 (inGb_spec _ _) Eo))|].
      assert (Hn' : ~ inG OUTS (b + i)) by (apply inGb_false; exact Eo).
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b mm HAR0 Hb) as (_ & H4096 & Hbce & _).
      assert (Hr : 0 <= b + i < 2 ^ 64).
      { unfold req_size in *. destruct (Z.eqb_spec mm 0); lia. }
      rewrite !(gover_out_aview segs OUTS _ _ memc (b + i) Hr Hn').
      exact (L2 b mm i (Permutation_in _ (Permutation_sym HP2) Hb) Hi Hn).
    - intros a Hi HnG Hno He. destruct (inGb OUTS a) eqn:Eo; [exact (EQO a (proj1 (inGb_spec _ _) Eo))|].
      assert (Hn : ~ inG OUTS a) by (apply inGb_false; exact Eo).
      pose proof (decode_segs_low a Hi) as Hl.
      rewrite !(gover_out_aview segs OUTS _ _ memc a ltac:(unfold kLowMemEnd in Hl; lia) Hn).
      exact (L3 a Hi HnG Hno He).
    - intros cid pos a Hin Hr Hn. destruct (inGb OUTS a) eqn:Eo; [exact (EQO a (proj1 (inGb_spec _ _) Eo))|].
      assert (Hn' : ~ inG OUTS a) by (apply inGb_false; exact Eo).
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR0 Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      assert (Ha : 0 <= a < 2 ^ 64).
      { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
        pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
        assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
        pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
        unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
      rewrite !(gover_out_aview segs OUTS _ _ memc a Ha Hn').
      apply (L4 cid pos a ltac:(rewrite HF2; exact Hin)); [|exact Hn].
      unfold frame_rng in *. cbn [fst snd] in *. rewrite !Hfa. exact Hr.
    - intros a Ha Hw Hp. destruct (inGb OUTS a) eqn:Eo.
      + pose proof (proj1 (inGb_spec _ _) Eo) as Hin. destruct (HOV a Hin) as (_ & Q2 & (_ & b & Hb) & HR & _).
        split; [exact Q2|]. exists b. rewrite (tkw_gover_in OUTS m2 memc a HR Hin). exact Hb.
      + assert (Hn : ~ inG OUTS a) by (apply inGb_false; exact Eo).
        apply (tkw_gover_apresent OUTS _ m2 memc a ltac:(lia) Hn). apply L5; [exact Ha | exact Hw |].
        exact (gover_out_apresent OUTS _ m memc a ltac:(lia) Hn Hp).
    - intros a Ha.
      assert (Hn : ~ inG OUTS a) by (intros Hin; destruct (HOV a Hin) as (_ & _ & _ & _ & Hw'); lia).
      apply (tkw_gover_apresent OUTS _ m2 memc a ltac:(lia) Hn). exact (L6 a Ha). }
  apply (@dk_kept_trans_g rc segs B G lyc Sc W memc Wc (gover OUTS m memc) W2 (gover OUTS m2 memc) (sp - TAKE_STK)
    sp (SP' - TRANS_BC_STK) SP' EW (fun _ => False)); [lia | lia | exact K | exact KB' | lia | lia | intros a []].
Qed.

(* ---- the journal across a footprint run that writes the frame, the out cells and bytes of G ---- *)

Lemma tkw_jrun : forall ly2 S2 (Wc : world segs) m md m1 md1 (Wr : Z -> Prop),
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall x : word, ~ Wr (bv_unsigned x) -> m1 x = m x) ->
  YK1b.mem_grows m m1 -> same_but_materialized md md1 ->
  (forall a, Wr a -> (SP' <= a < sp) \/ inG OUTS a \/ inG G a) ->
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m1 md1 k.
Proof.
  intros ly2 S2 Wc m md m1 md1 Wr J HP HU HG HS HWr.
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & _). pose proof tkw_consts as (E1 & E2 & E3 & E4 & _).
  assert (HV : forall a, Wr a -> w_H Wc (Z_to_bv 64 a) = false /\
    awr_byte STK sp0 FP (ablocks B ly St) (ablocks B ly2 S2) ly2 own a \/ inG G a).
  { intros a Ha. destruct (HWr a Ha) as [Hf | [Ho | Hg]].
    - left. split; [exact (proj1 (tkw_win_pres ly2 S2 Wc m md a J ltac:(lia)))|]. left. lia.
    - left. apply tkw_outs in Ho. destruct Ho as [Ho | Ho].
      + destruct (tkw_twr_cur blp 8 ly2 S2 Wc m md a HTWL HNGL Ho J HP) as (Hw & (Hh & _) & _).
        split; [exact Hh | exact Hw].
      + destruct (tkw_twr_cur hdp 4 ly2 S2 Wc m md a HTWH HNGH Ho J HP) as (Hw & (Hh & _) & _).
        split; [exact Hh | exact Hw].
    - right. exact Hg. }
  apply (ajournal_gx_exec segs B LAWS decode_segs_low G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k m1 md1
           Wr HGX J).
  - intros x Hx. unfold mrestrict. rewrite (HU x Hx). reflexivity.
  - intros x Hx. unfold mrestrict in *. destruct (w_H Wc x); [exact Hx|]. exact (HG x Hx).
  - intros x Hh. apply HU. intros Hx. destruct (HV _ Hx) as [(Hv & _) | Hg].
    + rewrite Z_to_bv_bv_unsigned in Hv. rewrite Hv in Hh. discriminate.
    + pose proof (tkw_G_vis Wc _ Hg) as Hv. rewrite Z_to_bv_bv_unsigned in Hv. rewrite Hv in Hh. discriminate.
  - exact HS.
  - intros a Ha. destruct (HV a Ha) as [(_ & Hw) | Hg]; [left; split; [exact Hw | lia] | right; left; exact Hg].
Qed.

(* ---- a footprint run from a state register-equivalent to decode's MS form ---- *)

Lemma tkw_run : forall (Wc : world segs) (R : bvmap 5 word) (pc : word) (m : word -> option byte)
    (ms : machine_state) (md : Model) (P : machine_state -> Prop) (Q' : world segs -> config -> Prop),
  ms_eqv (MS R (@YK11.fp_regs fx) pc (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs)) ms ->
  evtF rsegs (LCK.RNG_W (world segs) (@w_H segs) Wc) P
    (MS R (@YK11.fp_regs fx) pc (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs)) ->
  (forall ms1 ms2 md', P ms1 -> ms_eqv ms1 ms2 -> YK1b.mem_grows m (ms_mem ms1) ->
     same_but_materialized md md' -> SRr segs Wc (mkCfg ms2 md') Q') ->
  SRr segs Wc (mkCfg ms md) Q'.
Proof.
  intros Wc R pc m ms md P Q' EQV RUN K.
  pose proof (LeafCgGlue.evtF_eqv rsegs _ P _ _ RUN EQV) as RUN'.
  apply (LeafCgFacts.bridge_evtF_stmt_YA0n Wc ms md _ _ Q' RUN').
  - exact (TFE.decode_fp_avoids Wc).
  - intros ms2 md' (ms1 & HP & HE & HG) Hs. exact (K ms1 ms2 md' HP HE HG Hs).
Qed.

(* ---- what the runs read ---- *)

Lemma tkw_rd_view : forall (Wc : world segs) m a v, aview segs (w_H Wc) m a = Some v -> 0 <= v < 256 ->
  ov_read_bytes rsegs m (wa a) 1 = Some [Z_to_bv 8 v] /\ w_H Wc (Z_to_bv 64 a) = false.
Proof.
  intros Wc m a v Hv Hr. destruct (decode_aview_some Wc m a v Hv) as (Hvis & b & Hb & Eb).
  split; [|exact Hvis]. rewrite (AsanKAProof.rd1 m a b Hb). f_equal. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned, Eb. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma tkw_sh_eq : forall a, shadow_of_addr SHADOW_OFF a = tk_sh a.
Proof. intros a. unfold shadow_of_addr, tk_sh, TK_K, SHADOW_OFF, FCs.ASAN_K. lia. Qed.

Lemma tkw_ovr : forall m a (bs : list byte) (n : nat), bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H L. replace (wa a) with (wa (a + 0)) by (rewrite Z.add_0_r; reflexivity).
  rewrite (bytes_at_read rsegs m a bs 0 n H ltac:(lia) ltac:(rewrite L; change (Z.to_nat 0) with 0%nat; lia)).
  change (Z.to_nat 0) with 0%nat. cbn [skipn]. apply f_equal. apply firstn_all2. lia.
Qed.

Lemma tkw_world_raw : forall (Wc : world segs) m B1, tw_at TMAP_A (aview segs (w_H Wc) m) B1 ->
  tw_at TMAP_A (fun a => option_map (fun x : byte => bv_unsigned x) (mrd rsegs m (wa a))) B1.
Proof.
  intros Wc m B1 H. apply (tw_kept TMAP_A (aview segs (w_H Wc) m)); [exact H|].
  intros x (o & b & n & Hin & Hx). cbv beta. symmetry. apply decode_aview_mrd. apply tkw_G_vis.
  pose proof (TMAP_A_in_G o b n Hin) as HG. unfold inG. apply Exists_exists. exists (b, n).
  split; [exact HG | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The shadow byte of a granule of g_s's payload: 0 at every AR state (trans_take_cells). *)
Lemma tkw_gs_sh : forall ly2 S2 (Wc : world segs) m md a,
  AR segs B ly2 S2 Wc m md -> TA_g_s <= a / 8 * 8 -> a / 8 * 8 + 8 <= TA_g_s + TW.SZ_g_s ->
  ov_read_bytes rsegs m (wa (tk_sh a)) 1 = Some [Z_to_bv 8 0] /\
  rng (LCK.RNG_W (world segs) (@w_H segs) Wc) (tk_sh a) 1.
Proof.
  intros ly2 S2 Wc m md a HAR H1 H2.
  pose proof (decode_zshadow_rd B ly2 S2 Wc m md TA_g_s (TA_g_s + TW.SZ_g_s) (a / 8 * 8) HAR
                ltac:(apply Z_mod_mult) H1 H2 HTC) as Hz.
  assert (E : FCs.shadow_addr (a / 8 * 8) = tk_sh a)
    by (unfold FCs.shadow_addr, tk_sh, TK_K; rewrite Z.div_mul by lia; reflexivity).
  rewrite E in Hz. destruct (tkw_rd_view Wc m (tk_sh a) 0 Hz ltac:(lia)) as [Hr Hv]. split; [exact Hr|].
  assert (Ha : 0 <= a / 8) by (unfold TA_g_s in H1; lia).
  assert (Hb : a / 8 * 8 < 2 ^ 47) by (unfold TA_g_s, TW.SZ_g_s in H2; lia).
  apply TFE.decode_rng_vis; [unfold tk_sh, TK_K, FCs.ASAN_K; lia | unfold tk_sh, TK_K, FCs.ASAN_K; lia |].
  intros i Hi. replace (tk_sh a + i) with (tk_sh a) by lia. exact Hv.
Qed.

(* A field of g_s at offset kk, read as the model's world says. *)
Lemma tkw_fld : forall (Wc : world segs) m B1 kk (c : nat),
  tw_at TMAP_A (aview segs (w_H Wc) m) B1 -> 0 <= kk -> kk + Z.of_nat c <= TW.SZ_g_s ->
  ov_read_bytes rsegs m (wa (TA_g_s + kk)) c = Some (TW.put c (TW.u_at B1 (TW.OFF_g_s + kk) c)) /\
  rng (LCK.RNG_W (world segs) (@w_H segs) Wc) (TA_g_s + kk) (Z.of_nat c) /\
  bytes_at rsegs m (TA_g_s + kk) (TW.put c (TW.u_at B1 (TW.OFF_g_s + kk) c)).
Proof.
  intros Wc m B1 kk c HTW H0 H1.
  pose proof (tkw_world_raw Wc m B1 HTW) as HR.
  pose proof (tw_bytes_at rsegs m TMAP_A B1 TW.OFF_g_s TA_g_s TW.SZ_g_s kk c TMAP_A_ok HR TMAP_A_g_s H0 H1) as BA.
  pose proof (tw_len _ _ _ HTW) as LB.
  rewrite (tkw_sub_put B1 (TW.OFF_g_s + kk) c) in BA
    by (try rewrite LB; unfold TW.W_LEN, TW.OFF_g_s, TW.SZ_g_s in *; lia).
  split; [|split; [|exact BA]].
  - exact (tkw_ovr m (TA_g_s + kk) _ c BA (TWL.length_put c _)).
  - apply TFE.decode_rng_vis; [unfold TA_g_s; lia | unfold TA_g_s, TW.SZ_g_s in *; lia |].
    intros i Hi. apply tkw_G_vis. apply tkw_inG_gs. unfold TW.SZ_g_s in *. lia.
Qed.

(* tkw_fld and tkw_gs_sh at the addresses and the model values the runs name. *)
Lemma tkw_fldv : forall (Wc : world segs) m B1 (A kk v : Z) (c : nat),
  tw_at TMAP_A (aview segs (w_H Wc) m) B1 -> 0 <= kk -> kk + Z.of_nat c <= TW.SZ_g_s ->
  A = TA_g_s + kk -> v = TW.u_at B1 (TW.OFF_g_s + kk) c ->
  ov_read_bytes rsegs m (wa A) c = Some (TW.put c v) /\
  rng (LCK.RNG_W (world segs) (@w_H segs) Wc) A (Z.of_nat c).
Proof.
  intros Wc m B1 A kk v c HTW H0 H1 -> ->.
  destruct (tkw_fld Wc m B1 kk c HTW H0 H1) as (F & R & _). split; [exact F | exact R].
Qed.

Lemma tkw_shv : forall ly2 Sx (Wc : world segs) m md (A : Z), AR segs B ly2 Sx Wc m md ->
  TA_g_s <= A < TA_g_s + TW.SZ_g_s ->
  ov_read_bytes rsegs m (wa (tk_sh A)) 1 = Some [Z_to_bv 8 0] /\
  rng (LCK.RNG_W (world segs) (@w_H segs) Wc) (tk_sh A) 1.
Proof.
  intros ly2 Sx Wc m md A HAR HA.
  apply (tkw_gs_sh ly2 Sx Wc m md A HAR);
    pose proof (Z.div_mod A 8 ltac:(lia)); pose proof (Z.mod_pos_bound A 8 ltac:(lia));
    unfold TA_g_s, TW.SZ_g_s in *; lia.
Qed.

(* The six reads of turn i (take_seg_run.v tk_rd_turn) and their footprint. *)
Lemma tkw_rdt : forall ly2 Sx (Wc : world segs) m md B1 i,
  AR segs B ly2 Sx Wc m md -> tw_at TMAP_A (aview segs (w_H Wc) m) B1 -> 0 <= i < 512 ->
  tk_rd_turn m i (TW.S_queue_len B1 i) (TW.S_queue_display B1 i) (TW.S_cfg_max_cmds B1) (TW.S_cfg_max_body B1) /\
  tk_rng_turn (LCK.RNG_W (world segs) (@w_H segs) Wc) i.
Proof.
  intros ly2 Sx Wc m md B1 i HAR HTW Hi.
  pose proof tkw_addrs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  destruct (tkw_shv ly2 Sx Wc m md TK_MAXC HAR ltac:(unfold TW.SZ_g_s; lia)) as [Sa Ra].
  destruct (tkw_shv ly2 Sx Wc m md TK_MAXB HAR ltac:(unfold TW.SZ_g_s; lia)) as [Sb Rb].
  destruct (tkw_shv ly2 Sx Wc m md (TK_Q0 + 32 * i + 24) HAR ltac:(unfold TW.SZ_g_s; lia)) as [Sq Rq].
  destruct (tkw_shv ly2 Sx Wc m md (TK_Q0 + 32 * i + 25) HAR ltac:(unfold TW.SZ_g_s; lia)) as [Sd Rd].
  destruct (tkw_fldv Wc m B1 TK_MAXC 52 (TW.S_cfg_max_cmds B1) 4 HTW ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)
              ltac:(lia) ltac:(unfold TW.S_cfg_max_cmds; f_equal; unfold TW.A_S_cfg_max_cmds; lia)) as [Fa Ga].
  destruct (tkw_fldv Wc m B1 TK_MAXB 56 (TW.S_cfg_max_body B1) 4 HTW ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)
              ltac:(lia) ltac:(unfold TW.S_cfg_max_body; f_equal; unfold TW.A_S_cfg_max_body; lia)) as [Fb Gb].
  destruct (tkw_fldv Wc m B1 (TK_Q0 + 32 * i + 24) (1760 + 32 * i + 24) (TW.S_queue_len B1 i) 1 HTW
              ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(lia)
              ltac:(unfold TW.S_queue_len; f_equal; unfold TW.A_S_queue_len; lia)) as [Fq Gq].
  destruct (tkw_fldv Wc m B1 (TK_Q0 + 32 * i + 25) (1760 + 32 * i + 25) (TW.S_queue_display B1 i) 1 HTW
              ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(lia)
              ltac:(unfold TW.S_queue_display; f_equal; unfold TW.A_S_queue_display; lia)) as [Fd Gd].
  split.
  - split; [exact Sa|]. split; [exact Sb|]. split; [exact Sq|]. split; [exact Sd|].
    split; [exact Fa|]. split; [exact Fb|]. split; [exact Fq | exact Fd].
  - split; [exact Ra|]. split; [exact Rb|]. split; [exact Rq|]. split; [exact Rd|].
    split; [exact Ga|]. split; [exact Gb|]. split; [exact Gq | exact Gd].
Qed.

(* The three reads of the join (take_seg_run.v tk_rd_join) and their footprint. *)
Lemma tkw_rdj : forall ly2 Sx (Wc : world segs) m md B1,
  AR segs B ly2 Sx Wc m md -> tw_at TMAP_A (aview segs (w_H Wc) m) B1 ->
  tk_rd_join m (TW.S_cfg_max_cmds B1) (TW.S_cfg_max_body B1) (TW.S_queued B1) /\
  tk_rng_join (LCK.RNG_W (world segs) (@w_H segs) Wc).
Proof.
  intros ly2 Sx Wc m md B1 HAR HTW.
  pose proof tkw_addrs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  destruct (tkw_shv ly2 Sx Wc m md TK_MAXC HAR ltac:(unfold TW.SZ_g_s; lia)) as [Sa Ra].
  destruct (tkw_shv ly2 Sx Wc m md TK_MAXB HAR ltac:(unfold TW.SZ_g_s; lia)) as [Sb Rb].
  destruct (tkw_shv ly2 Sx Wc m md TK_QD HAR ltac:(unfold TW.SZ_g_s; lia)) as [Sq Rq].
  destruct (tkw_fldv Wc m B1 TK_MAXC 52 (TW.S_cfg_max_cmds B1) 4 HTW ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)
              ltac:(lia) ltac:(unfold TW.S_cfg_max_cmds; f_equal; unfold TW.A_S_cfg_max_cmds; lia)) as [Fa Ga].
  destruct (tkw_fldv Wc m B1 TK_MAXB 56 (TW.S_cfg_max_body B1) 4 HTW ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)
              ltac:(lia) ltac:(unfold TW.S_cfg_max_body; f_equal; unfold TW.A_S_cfg_max_body; lia)) as [Fb Gb].
  destruct (tkw_fldv Wc m B1 TK_QD 18144 (TW.S_queued B1) 4 HTW ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)
              ltac:(lia) ltac:(unfold TW.S_queued; f_equal; unfold TW.A_S_queued; lia)) as [Fq Gq].
  split.
  - split; [exact Sa|]. split; [exact Sb|]. split; [exact Sq|].
    split; [exact Fa|]. split; [exact Fb | exact Fq].
  - split; [exact Ra|]. split; [exact Rb|]. split; [exact Rq|].
    split; [exact Ga|]. split; [exact Gb | exact Gq].
Qed.

(* The frame and the stack the runs carve, at any state of the walk. *)
Lemma tkw_stkf : forall ly2 S2 (Wc : world segs) m md,
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  stk rsegs m (sp - TAKE_STK) SP' /\ stk rsegs m (sp - TAKE_STK) sp /\
  rng (LCK.RNG_W (world segs) (@w_H segs) Wc) SP' TK_FRAME /\
  0 <= SP' /\ SP' + TK_FRAME < 2 ^ 63 /\ sp - TAKE_STK + TK_FRAME <= SP' /\
  YM05.alloc_ceiling + TRANS_BC_STK <= SP'.
Proof.
  intros ly2 S2 Wc m md J.
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & _). pose proof tkw_consts as (E1 & E2 & E3 & E4 & _).
  pose proof asan_consts as (C1 & _).
  split; [apply (TFE.decode_stk_present (w_H Wc)); [lia | lia |];
          intros a Ha; exact (tkw_win_pres ly2 S2 Wc m md a J ltac:(lia))|].
  split; [apply (TFE.decode_stk_present (w_H Wc)); [lia | lia |];
          intros a Ha; exact (tkw_win_pres ly2 S2 Wc m md a J ltac:(lia))|].
  split; [|repeat split; lia].
  apply TFE.decode_rng_vis; [lia | lia |]. intros i Hi.
  exact (proj1 (tkw_win_pres ly2 S2 Wc m md (SP' + i) J ltac:(lia))).
Qed.

(* The shadow byte of has_display: the disjunction its 4-byte checks take. *)
Lemma tkw_hd_sh : forall ly2 S2 (Wc : world segs) m md,
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW ->
  exists khd, ov_read_bytes rsegs m (wa (tk_sh hdp)) 1 = Some [Z_to_bv 8 khd] /\
    (khd = 0 \/ (hdp mod 8 + 3 < khd /\ khd < 8)) /\
    rng (LCK.RNG_W (world segs) (@w_H segs) Wc) (tk_sh hdp) 1.
Proof.
  intros ly2 S2 Wc m md J HP K.
  pose proof tkw_cellf as (_ & _ & _ & _ & _ & _ & _ & _ & H0 & H63 & _).
  pose proof (tkw_cell_ra hdp 4 ly2 S2 Wc m md HTWH HNGH HRDH J HP K) as RA.
  destruct (RA hdp ltac:(lia)) as (s & Hs & _).
  pose proof (check_passes_lb (aview segs (w_H Wc) m) SHADOW_OFF hdp 4 hdp 4 s RA ltac:(lia) ltac:(lia)
                ltac:(lia) Hs) as Hc.
  rewrite tkw_sh_eq in Hs.
  destruct (tkw_rd_view Wc m (tk_sh hdp) s Hs ltac:(lia)) as [Hr Hv].
  exists s. split; [exact Hr|]. split; [lia|].
  assert (Hd : 0 <= hdp / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply TFE.decode_rng_vis; [unfold tk_sh, TK_K, FCs.ASAN_K; lia | unfold tk_sh, TK_K, FCs.ASAN_K; lia |].
  intros i Hi. replace (tk_sh hdp + i) with (tk_sh hdp) by lia. exact Hv.
Qed.

(* The shadow byte of body_len: 0 (an 8-byte store at an 8-aligned address covers its whole granule). *)
Lemma tkw_bl_sh : forall ly2 S2 (Wc : world segs) m md,
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW ->
  ov_read_bytes rsegs m (wa (tk_sh blp)) 1 = Some [Z_to_bv 8 0] /\
  rng (LCK.RNG_W (world segs) (@w_H segs) Wc) (tk_sh blp) 1.
Proof.
  intros ly2 S2 Wc m md J HP K.
  pose proof tkw_cellf as (_ & _ & _ & _ & _ & L0 & L63 & _).
  pose proof (tkw_cell_ra blp 8 ly2 S2 Wc m md HTWL HNGL HRDL J HP K) as RA.
  destruct (RA blp ltac:(lia)) as (s & Hs & _).
  assert (Hb : 8 * (blp / 8) + 8 <= blp + 8)
    by (pose proof (Z.div_mod blp 8 ltac:(lia)) as Hdm; rewrite HBL8 in Hdm; lia).
  pose proof (check_passes_whole (aview segs (w_H Wc) m) SHADOW_OFF blp 8 blp 8 s RA ltac:(lia) ltac:(lia) Hb Hs)
    as Hc. subst s.
  rewrite tkw_sh_eq in Hs.
  destruct (tkw_rd_view Wc m (tk_sh blp) 0 Hs ltac:(lia)) as [Hr Hv]. split; [exact Hr|].
  assert (Hd : 0 <= blp / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply TFE.decode_rng_vis; [unfold tk_sh, TK_K, FCs.ASAN_K; lia | unfold tk_sh, TK_K, FCs.ASAN_K; lia |].
  intros i Hi. replace (tk_sh blp + i) with (tk_sh blp) by lia. exact Hv.
Qed.

(* A cell the caller lets take write: its bytes are visible, so in every run's footprint. *)
Lemma tkw_cell_rng : forall q n ly2 S2 (Wc : world segs) m md,
  transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc sp q n ->
  (forall x, q <= x < q + n -> ~ inG G x) -> decode_rd_ok W memc q n ->
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  rng (LCK.RNG_W (world segs) (@w_H segs) Wc) q n.
Proof.
  intros q n ly2 S2 Wc m md HT HN RD J HP. pose proof RD as (_ & _ & _ & _ & R0 & R63).
  apply TFE.decode_rng_vis; [lia | lia |]. intros i Hi.
  exact (proj1 (proj1 (proj2 (tkw_twr_cur q n ly2 S2 Wc m md (q + i) HT HN ltac:(lia) J HP)))).
Qed.

(* A cell the caller lets take write lies at or above 4096: each kind of awr_byte does. *)
Lemma tkw_cell_ge : forall q n,
  transport_twr_ok_g segs B G STK sp0 FP ly St lyc Sc own W memc sp q n ->
  (forall x, q <= x < q + n -> ~ inG G x) -> decode_rd_ok W memc q n -> 0 < n -> 4096 <= q.
Proof.
  intros q n HT HN RD Hn. pose proof RD as (_ & _ & _ & RM & R0 & R63).
  destruct (HT q ltac:(lia)) as [(Haw & _ & _ & _) | HGq]; [|exfalso; exact (HN q ltac:(lia) HGq)].
  destruct (tkw_jf _ _ _ _ _ HJ) as (HAR0 & _ & Hfr0 & _ & _).
  pose proof tkw_spf as (P1 & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Haw as [Hwin | [(_ & b & mm & Hin & Hb) | [(b & mm & Hin & _ & Hb) | (cid & pos & Hin & Hfr)]]].
  - lia.
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b mm HAR0 Hin) as (_ & H4096 & _). lia.
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b mm HAR0 Hin) as (_ & H4096 & _). lia.
  - assert (HinS : In (cid, pos) (frames Sc)) by (rewrite Hfr0; apply in_or_app; left; exact Hin).
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR0 HinS) as (F4 & _).
    destruct Hfr as [Hfr | Hfr]; unfold in_zr in Hfr; cbn [fst snd] in Hfr; [lia|].
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF, amem_range in *. lia.
Qed.

Lemma tkw_munch_view : forall (H : word -> bool) (Wl : list (Z * Z)) (m m1 : word -> option byte) a,
  munch Wl m m1 -> 0 <= a < 2 ^ 64 -> outside Wl a -> aview segs H m1 a = aview segs H m a.
Proof. intros H Wl m m1 a MU Ha Ho. apply tkw_aview_raw. apply MU. rewrite unsigned_lit by lia. exact Ho. Qed.

Lemma tkw_pres_grow : forall (H : word -> bool) (m m1 : word -> option byte) a,
  YK1b.mem_grows m m1 -> apresent H m a -> apresent H m1 a.
Proof.
  intros H m m1 a MG (Hh & b & Hb). split; [exact Hh|].
  destruct (m1 (Z_to_bv 64 a)) as [b1|] eqn:E; [exists b1; reflexivity|]. exfalso.
  apply (MG (Z_to_bv 64 a)); [rewrite Hb; discriminate | exact E].
Qed.

Lemma tkw_swrap32 : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
  change (2 ^ 32 / 2) with (2 ^ 31). rewrite Z.mod_small by lia. lia.
Qed.

(* The callee-saved registers the epilogue reloads are the caller's. *)
Lemma tkw_pres_ret : forall (R2 : bvmap 5 word)
    (spx gp tp x5 x6 x7 r10 r1 r2 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  xregs_eqv (mkR (YK11.getr regs (Z_to_bv 5 1)) spx gp tp x5 x6 x7 (YK11.getr regs (Z_to_bv 5 8))
               (YK11.getr regs (Z_to_bv 5 9)) r10 r1 r2 x13 x14 x15 x16 x17 (YK11.getr regs (Z_to_bv 5 18))
               (YK11.getr regs (Z_to_bv 5 19)) (YK11.getr regs (Z_to_bv 5 20)) (YK11.getr regs (Z_to_bv 5 21))
               (YK11.getr regs (Z_to_bv 5 22)) (YK11.getr regs (Z_to_bv 5 23)) (YK11.getr regs (Z_to_bv 5 24))
               (YK11.getr regs (Z_to_bv 5 25)) (YK11.getr regs (Z_to_bv 5 26)) (YK11.getr regs (Z_to_bv 5 27))
               x28 x29 x30 x31) R2 ->
  bv_unsigned spx = sp -> gp = GP -> tp = TP ->
  aregs_preserved regs R2.
Proof.
  intros R2 spx gp tp x5 x6 x7 r10 r1 r2 x13 x14 x15 x16 x17 x28 x29 x30 x31 HX Hsp Egp Etp r Hr.
  rewrite (TFE.decode_getr_xeqv _ _ HX). subst gp tp. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst r;
    first [ reflexivity | transitivity spx; [reflexivity | apply bv_eq; exact Hsp] ].
Qed.

Lemma tkw_twin_G : forall x, tw_in TMAP_A x -> inG G x.
Proof.
  intros x (o & b & n & Hin & Hx). pose proof (TMAP_A_in_G o b n Hin) as HG. unfold inG. apply Exists_exists.
  exists (b, n). split; [exact HG | unfold in_zr; cbn [fst snd]; lia].
Qed.

Lemma tkw_fr_size : forall ws, length ws = 15%nat -> cells_size (tk_fr (ws ++ tk_sv)) = 224%nat.
Proof.
  intros ws L. assert (GS : forall l, cells_size (map C8 l) = (8 * length l)%nat).
  { induction l as [|w l IH]; [reflexivity|]. cbn [map cells_size length]. rewrite IH. cbn [csize]. lia. }
  unfold tk_fr. rewrite GS, length_app, L. reflexivity.
Qed.

(* The two shadow facts of a range of g_s's queue array, at every AR state. *)
Lemma tkw_q_sh : forall ly2 S2 (Wc : world segs) m md q n, AR segs B ly2 S2 Wc m md ->
  TK_Q0 <= q -> q + n <= TK_Q0 + 32 * 512 -> 0 < n ->
  range_addressable (aview segs (w_H Wc) m) SHADOW_OFF q n /\ shadow_hull_vis (aview segs (w_H Wc) m) q n.
Proof.
  intros ly2 S2 Wc m md q n HAR H1 H2 Hn.
  apply (decode_zshadow_ra B ly2 S2 Wc m md TA_g_s (TA_g_s + TW.SZ_g_s) q n HAR HTC Hn);
    unfold TK_Q0, TK_S, TA_g_s, TW.SZ_g_s in *.
  - pose proof (Z.div_mod q 64 ltac:(lia)). pose proof (Z.mod_pos_bound q 64 ltac:(lia)). lia.
  - pose proof (Z.div_mod (q + n - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 64 ltac:(lia)). lia.
Qed.

(* tkw_inv carried across a step of the same world that writes a range D below the ESTACK window and inside the
   written range (not an out cell), and the ESTACK window; the world relation and the body bytes are given. *)
Lemma tkw_inv_step : forall (Wc : world segs) m md m2 md2 ly2 S2 B2 hd1 X2 ws (D : Z -> Prop),
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW ->
  length ws = 15%nat -> rw_cells rsegs m SP' (tk_fr (ws ++ tk_sv)) ->
  rw_cells rsegs m hdp [C4 (Z_to_bv 64 hd1)] -> (exists jb, rw_cells rsegs m blp [CB 8 jb]) ->
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m2 md2 k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ D a -> ~ (SP' - ESTACK <= a < SP') ->
     aview segs (w_H Wc) m2 a = aview segs (w_H Wc) m a) ->
  (forall a, apresent (w_H Wc) m a -> apresent (w_H Wc) m2 a) ->
  (forall a, D a -> EW a /\ ~ inG OUTS a /\ a < SP' - ESTACK) ->
  tw_at TMAP_A (aview segs (w_H Wc) m2) B2 ->
  length X2 = 1484%nat -> garr8 segs (mrestrict (w_H Wc) m2) bp (TW.zs X2) ->
  tkw_inv Wc m2 md2 B2 hd1 X2 ws.
Proof.
  intros Wc m md m2 md2 ly2 S2 B2 hd1 X2 ws D J HF HP HMO K LW FR HDC (jb & BLC) J2 HKE HGR HD HTW2 LX2 GX2.
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & _).
  pose proof tkw_cellf as (B0 & B63 & BM & B4 & Bce & L0 & L63 & LM & H0 & H63 & HM & OL & OH).
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  assert (HKO : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> (a < SP' - ESTACK \/ SP' <= a) ->
    apresent (w_H Wc) m a -> apresent (w_H Wc) m2 a /\ aview segs (w_H Wc) m2 a = aview segs (w_H Wc) m a)
    by (intros a Ha Hd Hw Hp; split; [exact (HGR a Hp) | apply HKE; [exact Ha | exact Hd | lia]]).
  exists ly2, S2. split; [exact J2|]. split; [exact HF|]. split; [exact HP|]. split; [exact HMO|].
  split.
  { apply (tkw_K_step Wc m m2 K); [|exact HGR].
    intros a Ha Hw He. apply HKE; [exact Ha | intros Hd; exact (He (proj1 (HD a Hd))) | lia]. }
  split; [exact HTW2|].
  split; [exact LW|].
  split.
  { apply (tkw_cells_keep (w_H Wc) (w_H Wc) m m2 SP' _ FR). rewrite (tkw_fr_size ws LW). intros i Hi.
    assert (Hp : apresent (w_H Wc) m (SP' + i)) by exact (tkw_win_pres ly2 S2 Wc m md (SP' + i) J ltac:(lia)).
    split; [exact Hp|].
    exact (HKO (SP' + i) ltac:(lia) ltac:(intros Hd; pose proof (proj2 (proj2 (HD _ Hd))); lia) ltac:(lia) Hp). }
  split.
  { apply (tkw_cells_keep (w_H Wc) (w_H Wc) m m2 hdp _ HDC). cbn [cells_size csize]. intros i Hi.
    destruct (tkw_twr_cur hdp 4 ly2 S2 Wc m md (hdp + i) HTWH HNGH ltac:(lia) J HP) as (_ & Hp & _).
    split; [exact Hp|].
    exact (HKO (hdp + i) ltac:(lia)
             ltac:(intros Hd; apply (proj1 (proj2 (HD _ Hd))); apply tkw_outs; right; lia) ltac:(lia) Hp). }
  split.
  { exists jb. apply (tkw_cells_keep (w_H Wc) (w_H Wc) m m2 blp _ BLC). cbn [cells_size csize]. intros i Hi.
    destruct (tkw_twr_cur blp 8 ly2 S2 Wc m md (blp + i) HTWL HNGL ltac:(lia) J HP) as (_ & Hp & _).
    split; [exact Hp|].
    exact (HKO (blp + i) ltac:(lia)
             ltac:(intros Hd; apply (proj1 (proj2 (HD _ Hd))); apply tkw_outs; left; lia) ltac:(lia) Hp). }
  split; [exact LX2 | exact GX2].
Qed.

(* tkw_inv across a run that writes only take's own frame and the cell at hdp: the new frame and the new cell
   are the run's post, the rest is kept because those two ranges hold no byte of G, of the body, or of blp. *)
Lemma tkw_inv_mu : forall (Wc : world segs) m md m2 md2 ly2 Sx B2 hd2 X2 ws (D : Z -> Prop),
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 Sx Wc m md k ->
  frames Sx = frames Sc -> Permutation (ablocks B ly2 Sx) (ablocks B lyc Sc) -> mo_le MT Sc Sx 0 ->
  acall_kept_g segs B G lyc Sc W memc Wc (gover OUTS m memc) (sp - TAKE_STK) sp EW ->
  tw_at TMAP_A (aview segs (w_H Wc) m) B2 ->
  length X2 = 1484%nat -> garr8 segs (mrestrict (w_H Wc) m) bp (TW.zs X2) ->
  (exists jb, rw_cells rsegs m blp [CB 8 jb]) ->
  ajx G 0 [] STK sp0 FP ly St W0 mem0 md0 own ly2 Sx Wc m2 md2 k ->
  (forall x : word, ~ D (bv_unsigned x) -> m2 x = m x) -> YK1b.mem_grows m m2 ->
  (forall a, D a -> (SP' <= a < SP' + TK_FRAME) \/ (hdp <= a < hdp + 4)) ->
  length ws = 15%nat -> rw_cells rsegs m2 SP' (tk_fr (ws ++ tk_sv)) ->
  rw_cells rsegs m2 hdp [C4 (Z_to_bv 64 hd2)] ->
  tkw_inv Wc m2 md2 B2 hd2 X2 ws.
Proof.
  intros Wc m md m2 md2 ly2 Sx B2 hd2 X2 ws D J HF HP HMO K HTW LX2 GX2 (jb & BLC) J2 HU HG HD LW FR2 HDC2.
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  pose proof tkw_addrs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  pose proof tkw_cellf as (B0 & B63 & BM & B4 & Bce & L0 & L63 & LM & H0 & H63 & HM & OL & OH).
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  unfold amem_range in BM, LM, HM.
  assert (HV : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> aview segs (w_H Wc) m2 a = aview segs (w_H Wc) m a)
    by (intros a Ha Hd; apply tkw_aview_raw; apply HU; rewrite unsigned_lit by lia; exact Hd).
  exists ly2, Sx. split; [exact J2|]. split; [exact HF|]. split; [exact HP|]. split; [exact HMO|].
  split.
  { apply (tkw_K_step Wc m m2 K); [|intros a Hp; exact (tkw_pres_grow _ m m2 a HG Hp)].
    intros a Ha Hw He. apply HV; [exact Ha|]. intros Hd.
    destruct (HD a Hd) as [Hf | Hh]; [exact (Hw ltac:(lia)) | exact (He (or_intror (or_intror (or_intror (or_intror Hh)))))]. }
  split.
  { apply (tw_kept TMAP_A (aview segs (w_H Wc) m)); [exact HTW|].
    intros y Hy. pose proof (TMAP_A_hull y Hy) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply HV; [lia|]. intros Hd. destruct (HD y Hd) as [Hf | Hhd]; [lia|].
    exact (HNGH y Hhd (tkw_twin_G y Hy)). }
  split; [exact LW|]. split; [exact FR2|]. split; [exact HDC2|].
  split.
  { exists jb. apply (tkw_cells_keep (w_H Wc) (w_H Wc) m m2 blp _ BLC). cbn [cells_size csize]. intros i Hi.
    destruct (tkw_twr_cur blp 8 ly2 Sx Wc m md (blp + i) HTWL HNGL ltac:(lia) J HP) as (_ & Hp & _).
    split; [exact Hp|]. split; [exact (tkw_pres_grow _ m m2 (blp + i) HG Hp)|].
    apply HV; [lia|]. intros Hd. destruct (HD _ Hd) as [Hf | Hhd]; lia. }
  split; [exact LX2|].
  apply (tkw_garr8_ext (w_H Wc) (w_H Wc) m m2 bp (TW.zs X2)); [|exact GX2].
  intros j Hj. unfold TW.zs in Hj. rewrite length_map in Hj. apply HV; [lia|].
  intros Hd. destruct (HD _ Hd) as [Hf | Hhd]; lia.
Qed.

(* ---- the three calls of __asan_memcpy ---- *)

(* take's frame offset from the caller's sp0, as gx_intrin_at and gx_call_cg read it. *)
Lemma tkw_o16 : (SP' - sp0) mod 16 = 0 /\ SP' - sp0 <= 0 /\ ESTACK - (SP' - sp0) <= STK /\ SP' mod 16 = 0.
Proof.
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & _).
  pose proof (Z.div_mod sp 16 ltac:(lia)) as D1. rewrite HAL in D1.
  pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2. rewrite P5 in D2.
  split; [|split; [lia | split; [lia|]]].
  - replace (SP' - sp0) with ((sp / 16 - 14 - sp0 / 16) * 16) by lia. apply Z.mod_mul. lia.
  - replace SP' with ((sp / 16 - 14) * 16) by lia. apply Z.mod_mul. lia.
Qed.

(* Every shadow byte of application memory lies far below take's frame. *)
Lemma tkw_sh_lt : forall a, 0 <= a <= 140737488355328 -> tk_sh a + 1 <= SP'.
Proof.
  intros a Ha. pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & _). pose proof asan_consts as (AC1 & _).
  pose proof (Z.div_le_mono a 140737488355328 8 ltac:(lia) ltac:(lia)) as Hd.
  change (140737488355328 / 8) with 17592186044416 in Hd.
  pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  unfold tk_sh, TK_K, FCs.ASAN_K. lia.
Qed.

(* The bytes a present range holds, as a list. *)
Lemma tkw_bytes_of : forall (H : word -> bool) (m : word -> option byte) A (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> apresent H m (A + i)) ->
  exists bs : list byte, length bs = n /\
    (forall j, (j < n)%nat -> aview segs H m (A + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0)))).
Proof.
  intros H m A n Hp.
  exists (map (fun j : nat => match m (Z_to_bv 64 (A + Z.of_nat j)) with
                             | Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  split; [rewrite length_map, length_seq; reflexivity|].
  intros j Hj.
  rewrite (nth_indep (map (fun j0 : nat => match m (Z_to_bv 64 (A + Z.of_nat j0)) with
                                           | Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)) (Z_to_bv 8 0)
             (match m (Z_to_bv 64 (A + Z.of_nat 0%nat)) with Some b => b | None => Z_to_bv 8 0 end))
    by (rewrite length_map, length_seq; exact Hj).
  rewrite (map_nth (fun j0 : nat => match m (Z_to_bv 64 (A + Z.of_nat j0)) with
                                    | Some b => b | None => Z_to_bv 8 0 end) (seq 0 n) 0%nat j).
  rewrite seq_nth by exact Hj. cbn [Nat.add].
  destruct (Hp (Z.of_nat j) ltac:(lia)) as (Hh & b & Hb).
  unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
Qed.

Lemma tkw_cb_of : forall (H : word -> bool) (m : word -> option byte) A (n : nat),
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> apresent H m (A + i)) ->
  exists bs : list byte, length bs = n /\ rw_cells rsegs m A [CB n bs] /\
    garr8 segs (mrestrict H m) A (TW.zs bs).
Proof.
  intros H m A n H0 H1 Hp.
  destruct (tkw_bytes_of H m A n Hp) as (bs & Lb & Hv).
  assert (GA : garr8 segs (mrestrict H m) A (TW.zs bs))
    by (apply tkw_garr8_of_view; intros j Hj; apply Hv; lia).
  exists bs. split; [exact Lb|]. split; [|exact GA].
  apply (TFE.decode_rw_of_garr8 H m A [CB n bs]).
  - cbn [cells_wf cell_wf]. split; [exact Lb | exact I].
  - exact H0.
  - cbn [cells_size csize]. lia.
  - cbn [cells_size csize]. intros ii Hii. apply Hp. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact GA.
Qed.

(* Cells off a run's written ranges keep their value. *)
Lemma tkw_keep_cells : forall (ma mb : word -> option byte) (Wr : list (Z * Z)) A cs,
  munch Wr ma mb -> rw_cells rsegs ma A cs -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> outside Wr (A + i)) ->
  rw_cells rsegs mb A cs.
Proof.
  intros ma mb Wr A cs MU HC H0 H1 HO.
  apply (TFE.decode_rw_cells_eq ma mb A cs HC). intros i Hi.
  apply MU. rewrite wa_unsigned by lia. exact (HO i Hi).
Qed.

(* diginet_body_check answers 0 or -10 (lib/Spec/DgnLib.v body_check). *)
Lemma tkw_bcr : forall l, DgnLib.body_check l = 0 \/ DgnLib.body_check l = -10.
Proof.
  intros l. unfold DgnLib.body_check.
  destruct (DgnLib.bc_loop (length l) l 0 0); [right; reflexivity|].
  destruct (DgnSpec.system_at l); [right; reflexivity | left; reflexivity].
Qed.

(* The copy of 32 bytes from &s->queue[js] to &s->queue[kq], kq < js (the refusal copy at +0x244, the tail move at
   +0x380): the destination is a byte range of G the written range holds, the source is apart from it. *)
Lemma tkw_cpyq : forall (Wc : world segs) (md : Model) (m : word -> option byte) (B1 : list byte) (hd1 : Z)
    (X : list byte) (ws : list word) (R : bvmap 5 word) (kq js ret : Z) (Q' : world segs -> config -> Prop),
  tkw_inv Wc m md B1 hd1 X ws ->
  YK11.getr R 10 = w64 (TK_Q0 + 32 * kq) -> YK11.getr R 11 = w64 (TK_Q0 + 32 * js) -> YK11.getr R 12 = w64 32 ->
  YK11.getr R 2 = Z_to_bv 64 SP' -> YK11.getr R 3 = w64 (as_gp B) -> YK11.getr R 4 = w64 (as_tp B) ->
  YK11.getr R 1 = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
  0 <= kq < js -> js < 512 -> kq < TW.S_queued Bw ->
  (forall regs2 mem2 md2,
     tkw_inv Wc mem2 md2 (TW.upd B1 (TW.A_S_queue_bytes kq) (TW.sub B1 (TW.A_S_queue_bytes js) 32)) hd1 X ws ->
     aregs_preserved R regs2 ->
     SRr segs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 ret) mem2 (YK11.seg_rom segs)) md2) Q') ->
  SRr segs Wc (mkCfg (YK11.mkst R (Z_to_bv 64 TK_MEMCPY) m (YK11.seg_rom segs)) md) Q'.
Proof.
  intros Wc md m B1 hd1 X ws R kq js ret Q' INV R10 R11 R12 R2 R3 R4 R1 Hret Hre Hk Hj HkQ K'.
  pose proof INV as (ly2 & S2 & J & HF & HP & HMO & K & HTW & LW & FR & HDC & BLC & LX & GX).
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  pose proof tkw_addrs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  pose proof tkw_cellf as (B0 & B63 & BM & B4 & Bce & L0 & L63 & LM & H0 & H63 & HM & OL & OH).
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  pose proof tkw_o16 as (O16 & ONEG & OBUD & OAL).
  unfold amem_range in BM, LM, HM.
  destruct (tkw_jf _ _ _ _ _ J) as (HAR2 & _ & _ & _ & _).
  assert (HspE : spZ R = SP') by (unfold spZ at 1; rewrite R2; apply unsigned_lit; lia).
  assert (Hsp : spZ R = sp0 + (SP' - sp0)) by (rewrite HspE; lia).
  destruct (tkw_q_sh ly2 S2 Wc m md (TK_Q0 + 32 * kq) 32 HAR2 ltac:(lia) ltac:(lia) ltac:(lia)) as [RAD HHD].
  destruct (tkw_q_sh ly2 S2 Wc m md (TK_Q0 + 32 * js) 32 HAR2 ltac:(lia) ltac:(lia) ltac:(lia)) as [RAS HHS].
  eapply SRr_bind.
  { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS decode_segs_low OCpy (transport_sigma TS___asan_memcpy)
             (AIM fx) G Wc R m STK sp0
             FP ly St W0 mem0 md0 own ly2 S2 md k (TK_Q0 + 32 * kq) (TK_Q0 + 32 * js) 32 (SP' - sp0)
             (Z_to_bv 64 ret) HGX G_HARNESS_rw J R10 R11 R12).
    - lia.
    - lia.
    - lia.
    - exact Hsp.
    - exact O16.
    - exact ONEG.
    - exact OBUD.
    - exact R3.
    - exact R4.
    - exact R1.
    - apply YK0s.ret_ok_even. rewrite unsigned_lit by lia. exact Hre.
    - apply (@transport_twr_ok_g_intro rc tfib_sink_head segs B LAWS G STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k);
        [exact J|].
      intros a Ha. right. apply tkw_inG_gs. lia.
    - left. lia.
    - exact RAD.
    - intros _. exact HHD.
    - split; [lia|]. split; [lia|]. split.
      + intros a Ha. split.
        * eapply gx_rw_vis; [exact G_HARNESS_rw | apply tkw_inG_gs; lia].
        * rewrite HspE. lia.
      + split; [left; lia|]. split; [left; lia|]. split; [exact RAS | intros _; exact HHS]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & J2 & HP2 & _ & HCP & HKE & HGR).
  cbv iota in HCP.
  replace (sp0 + (SP' - sp0)) with SP' in HKE by lia.
  apply (K' regs2 mem2 md2); [|exact HP2].
  apply (tkw_inv_step Wc m md mem2 md2 ly2 S2 _ hd1 X ws (fun a => TK_Q0 + 32 * kq <= a < TK_Q0 + 32 * kq + 32)
           J HF HP HMO K LW FR HDC BLC J2).
  - intros a Ha Hd Hw. exact (HKE a Ha Hd Hw).
  - exact HGR.
  - intros a Ha. split; [|split].
    + left. exists kq. split; [unfold TW.S_queue_N; lia|]. split; [exact HkQ|].
      unfold twa_fld, TW.A_S_queue_bytes, TW.S_queue_ESZ. lia.
    + intros Ho. apply tkw_outs in Ho.
      destruct Ho as [Ho | Ho]; [apply (HNGL a Ho) | apply (HNGH a Ho)]; apply tkw_inG_gs; lia.
    + lia.
  - replace (TW.A_S_queue_bytes kq) with (TW.OFF_g_s + (1760 + 32 * kq)) by (unfold TW.A_S_queue_bytes; lia).
    assert (LS : length (TW.sub B1 (TW.A_S_queue_bytes js) 32) = 32%nat).
    { apply TWL.length_sub; [unfold TW.A_S_queue_bytes; lia|].
      rewrite (tw_len _ _ _ HTW). unfold TW.W_LEN, TW.A_S_queue_bytes. lia. }
    apply (tw_fill TMAP_A (aview segs (w_H Wc) m) (aview segs (w_H Wc) mem2) B1 TW.OFF_g_s TA_g_s TW.SZ_g_s
             (1760 + 32 * kq) (TW.sub B1 (TW.A_S_queue_bytes js) 32) TMAP_A_ok HTW TMAP_A_g_s ltac:(lia)
             ltac:(rewrite LS; lia)).
    + intros i Hi. rewrite LS in Hi.
      replace (TA_g_s + (1760 + 32 * kq) + i) with (TK_Q0 + 32 * kq + i) by lia.
      rewrite (HCP i ltac:(lia)).
      replace (TK_Q0 + 32 * js + i) with (TA_g_s + (1760 + 32 * js) + Z.of_nat (Z.to_nat i)) by lia.
      rewrite (tw_read_bytes TMAP_A _ B1 TW.OFF_g_s TA_g_s TW.SZ_g_s (1760 + 32 * js) 32 (Z.to_nat i) TMAP_A_ok HTW
                 TMAP_A_g_s ltac:(lia) ltac:(lia) ltac:(lia)).
      replace (TW.OFF_g_s + (1760 + 32 * js)) with (TW.A_S_queue_bytes js) by (unfold TW.A_S_queue_bytes; lia).
      reflexivity.
    + intros y Hy Hn. rewrite LS in Hn. pose proof (TMAP_A_hull y Hy) as Hh.
      unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      apply HKE; [lia | lia | lia].
  - exact LX.
  - apply (tkw_garr8_ext (w_H Wc) (w_H Wc) m mem2 bp (TW.zs X)); [|exact GX].
    intros jx Hjx. unfold TW.zs in Hjx. rewrite length_map in Hjx. apply HKE; [lia | | lia].
    intros Hd. apply (HNGB (bp + Z.of_nat jx) ltac:(lia)). apply tkw_inG_gs. lia.
Qed.

(* The bytes of a spliced list. *)
Lemma tkw_splice_len : forall (X src : list byte) (l c : nat), length X = 1484%nat -> (l + c <= 1484)%nat ->
  length src = c -> length (firstn l X ++ src ++ skipn (l + c) X) = 1484%nat.
Proof.
  intros X src l c LX Hc Ls. rewrite !length_app, length_firstn, length_skipn, Ls. lia.
Qed.

Lemma tkw_splice_nth : forall (X src : list byte) (l c j : nat) d, length X = 1484%nat -> (l + c <= 1484)%nat ->
  length src = c ->
  nth j (firstn l X ++ src ++ skipn (l + c) X) d =
  if (j <? l)%nat then nth j X d else if (j <? l + c)%nat then nth (j - l) src d else nth j X d.
Proof.
  intros X src l c j d LX Hc Ls.
  assert (Lf : length (firstn l X) = l) by (rewrite length_firstn; lia).
  destruct (Nat.ltb_spec j l) as [H1|H1].
  - rewrite app_nth1 by lia. rewrite nth_firstn. destruct (Nat.ltb_spec j l); [reflexivity | lia].
  - rewrite app_nth2 by lia. rewrite Lf. destruct (Nat.ltb_spec j (l + c)) as [H2|H2].
    + rewrite app_nth1 by lia. reflexivity.
    + rewrite app_nth2 by lia. rewrite Ls. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma tkw_splice_firstn : forall (X src : list byte) (l c : nat), length X = 1484%nat -> (l + c <= 1484)%nat ->
  length src = c -> firstn (l + c) (firstn l X ++ src ++ skipn (l + c) X) = firstn l X ++ src.
Proof.
  intros X src l c LX Hc Ls.
  assert (Lf : length (firstn l X) = l) by (rewrite length_firstn; lia).
  rewrite firstn_app, Lf, firstn_all2 by lia.
  replace (l + c - l)%nat with c by lia.
  rewrite firstn_app, Ls. replace (c - c)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
  f_equal. apply firstn_all2. lia.
Qed.

Lemma tkw_splice_firstn_le : forall (X src : list byte) (l c l' : nat), (l' <= l)%nat -> (l <= 1484)%nat ->
  length X = 1484%nat -> firstn l' (firstn l X ++ src ++ skipn (l + c) X) = firstn l' X.
Proof.
  intros X src l c l' Hl Hle LX.
  assert (Lf : length (firstn l X) = l) by (rewrite length_firstn; lia).
  rewrite firstn_app, Lf. replace (l' - l)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
  rewrite firstn_firstn. f_equal. lia.
Qed.

(* The copy of :365, clen bytes from &s->queue[i] to bp + len1: the destination lies in the body (a caller's
   side-stack frame byte range the written range holds), the source in g_s, apart from it. *)
Lemma tkw_cpyb : forall (Wc : world segs) (md : Model) (m : word -> option byte) (B1 : list byte) (hd1 : Z)
    (X : list byte) (ws : list word) (R : bvmap 5 word) (i len1 clen ret : Z) (Q' : world segs -> config -> Prop),
  tkw_inv Wc m md B1 hd1 X ws ->
  YK11.getr R 10 = w64 (bp + len1) -> YK11.getr R 11 = w64 (TK_Q0 + 32 * i) -> YK11.getr R 12 = w64 clen ->
  YK11.getr R 2 = Z_to_bv 64 SP' -> YK11.getr R 3 = w64 (as_gp B) -> YK11.getr R 4 = w64 (as_tp B) ->
  YK11.getr R 1 = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
  0 <= i < 512 -> 0 <= len1 -> 0 <= clen <= 24 -> len1 + clen <= 1484 ->
  (forall regs2 mem2 md2,
     tkw_inv Wc mem2 md2 B1 hd1
       (firstn (Z.to_nat len1) X ++ TW.sub B1 (TW.A_S_queue_bytes i) (Z.to_nat clen) ++
        skipn (Z.to_nat len1 + Z.to_nat clen) X) ws ->
     aregs_preserved R regs2 ->
     SRr segs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 ret) mem2 (YK11.seg_rom segs)) md2) Q') ->
  SRr segs Wc (mkCfg (YK11.mkst R (Z_to_bv 64 TK_MEMCPY) m (YK11.seg_rom segs)) md) Q'.
Proof.
  intros Wc md m B1 hd1 X ws R i len1 clen ret Q' INV R10 R11 R12 R2 R3 R4 R1 Hret Hre Hi Hl Hc Hlc K'.
  pose proof INV as (ly2 & S2 & J & HF & HP & HMO & K & HTW & LW & FR & HDC & BLC & LX & GX).
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  pose proof tkw_addrs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  pose proof tkw_o16 as (O16 & ONEG & OBUD & OAL).
  pose proof tkw_cellf as (B0 & B63 & BM & B4 & Bce & L0 & L63 & LM & H0 & H63 & HM & OL & OH).
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  unfold amem_range in BM.
  destruct (tkw_jf _ _ _ _ _ J) as (HAR2 & _ & _ & _ & _).
  assert (HspE : spZ R = SP') by (unfold spZ at 1; rewrite R2; apply unsigned_lit; lia).
  assert (Hsp : spZ R = sp0 + (SP' - sp0)) by (rewrite HspE; lia).
  assert (SEPX : bp + len1 + clen <= TK_Q0 + 32 * i \/ TK_Q0 + 32 * i + clen <= bp + len1).
  { destruct (Z_le_gt_dec (bp + len1 + clen) (TK_Q0 + 32 * i)) as [Hx|Hx]; [left; exact Hx|].
    destruct (Z_le_gt_dec (TK_Q0 + 32 * i + clen) (bp + len1)) as [Hy|Hy]; [right; exact Hy|]. exfalso.
    apply (HNGB (Z.max (bp + len1) (TK_Q0 + 32 * i)) ltac:(lia)). apply tkw_inG_gs. lia. }
  assert (RAD : range_addressable (aview segs (w_H Wc) m) SHADOW_OFF (bp + len1) clen /\
                (0 < clen -> shadow_hull_vis (aview segs (w_H Wc) m) (bp + len1) clen)).
  { destruct (Z.eq_dec clen 0) as [E|E]; [subst clen; split; [apply range_addressable_nil; lia | intros; lia]|].
    destruct (tkw_body_sh Wc m (bp + len1) clen K ltac:(lia) ltac:(lia) ltac:(lia)) as [RA1 RA2].
    split; [exact RA1 | intros _; exact RA2]. }
  assert (RAS : range_addressable (aview segs (w_H Wc) m) SHADOW_OFF (TK_Q0 + 32 * i) clen /\
                (0 < clen -> shadow_hull_vis (aview segs (w_H Wc) m) (TK_Q0 + 32 * i) clen)).
  { destruct (Z.eq_dec clen 0) as [E|E]; [subst clen; split; [apply range_addressable_nil; lia | intros; lia]|].
    destruct (tkw_q_sh ly2 S2 Wc m md (TK_Q0 + 32 * i) clen HAR2 ltac:(lia) ltac:(lia) ltac:(lia)) as [RA1 RA2].
    split; [exact RA1 | intros _; exact RA2]. }
  eapply SRr_bind.
  { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS decode_segs_low OCpy (transport_sigma TS___asan_memcpy)
             (AIM fx) G Wc R m STK sp0
             FP ly St W0 mem0 md0 own ly2 S2 md k (bp + len1) (TK_Q0 + 32 * i) clen (SP' - sp0)
             (Z_to_bv 64 ret) HGX G_HARNESS_rw J R10 R11 R12).
    - lia.
    - lia.
    - lia.
    - exact Hsp.
    - exact O16.
    - exact ONEG.
    - exact OBUD.
    - exact R3.
    - exact R4.
    - exact R1.
    - apply YK0s.ret_ok_even. rewrite unsigned_lit by lia. exact Hre.
    - apply (@transport_twr_ok_g_intro rc tfib_sink_head segs B LAWS G STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k);
        [exact J|].
      intros a Ha. left. split.
      + exact (proj1 (tkw_twr_cur bp TAKE_BODY ly2 S2 Wc m md a HTWB HNGB ltac:(lia) J HP)).
      + rewrite HspE. lia.
    - unfold amem_range. destruct BM as [BMa|BMa]; [left; lia | right; lia].
    - exact (proj1 RAD).
    - exact (proj2 RAD).
    - split; [lia|]. split; [lia|]. split.
      + intros a Ha. split.
        * eapply gx_rw_vis; [exact G_HARNESS_rw | apply tkw_inG_gs; lia].
        * rewrite HspE. lia.
      + split; [lia|]. split; [left; lia|]. exact RAS. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & J2 & HP2 & _ & HCP & HKE & HGR).
  cbv iota in HCP.
  replace (sp0 + (SP' - sp0)) with SP' in HKE by lia.
  apply (K' regs2 mem2 md2); [|exact HP2].
  assert (LS : length (TW.sub B1 (TW.A_S_queue_bytes i) (Z.to_nat clen)) = Z.to_nat clen).
  { apply TWL.length_sub; [unfold TW.A_S_queue_bytes; lia|].
    rewrite (tw_len _ _ _ HTW). unfold TW.W_LEN, TW.A_S_queue_bytes. lia. }
  apply (tkw_inv_step Wc m md mem2 md2 ly2 S2 B1 hd1 _ ws (fun a => bp + len1 <= a < bp + len1 + clen)
           J HF HP HMO K LW FR HDC BLC J2).
  - intros a Ha Hd Hw. exact (HKE a Ha Hd Hw).
  - exact HGR.
  - intros a Ha. split; [|split].
    + right; right; left. unfold TAKE_BODY. lia.
    + rewrite tkw_outs. unfold TAKE_BODY in SEP1, SEP2. lia.
    + lia.
  - apply (tw_kept TMAP_A (aview segs (w_H Wc) m)); [exact HTW|].
    intros y Hy. pose proof (TMAP_A_hull y Hy) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply HKE; [lia | | lia].
    intros Hd. apply (HNGB y ltac:(unfold TAKE_BODY; lia)). exact (tkw_twin_G y Hy).
  - apply tkw_splice_len; [exact LX | lia | exact LS].
  - apply tkw_garr8_of_view.
    rewrite (tkw_splice_len X (TW.sub B1 (TW.A_S_queue_bytes i) (Z.to_nat clen)) (Z.to_nat len1) (Z.to_nat clen)
               LX ltac:(lia) LS).
    intros j Hj.
    rewrite (tkw_splice_nth X _ (Z.to_nat len1) (Z.to_nat clen) j _ LX ltac:(lia) LS).
    destruct (Nat.ltb_spec j (Z.to_nat len1)) as [H1|H1].
    + rewrite HKE by lia. exact (tkw_view_garr8 (w_H Wc) m bp X j GX ltac:(lia)).
    + destruct (Nat.ltb_spec j (Z.to_nat len1 + Z.to_nat clen)) as [H2|H2].
      * replace (bp + Z.of_nat j) with (bp + len1 + (Z.of_nat j - len1)) by lia.
        rewrite (HCP (Z.of_nat j - len1) ltac:(lia)).
        replace (TK_Q0 + 32 * i + (Z.of_nat j - len1))
          with (TA_g_s + (1760 + 32 * i) + Z.of_nat (j - Z.to_nat len1)) by lia.
        rewrite (tw_read_bytes TMAP_A _ B1 TW.OFF_g_s TA_g_s TW.SZ_g_s (1760 + 32 * i) (Z.to_nat clen)
                   (j - Z.to_nat len1) TMAP_A_ok HTW TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) ltac:(lia)).
        replace (TW.OFF_g_s + (1760 + 32 * i)) with (TW.A_S_queue_bytes i) by (unfold TW.A_S_queue_bytes; lia).
        reflexivity.
      * rewrite HKE by lia. exact (tkw_view_garr8 (w_H Wc) m bp X j GX ltac:(lia)).
Qed.

(* ---- the call of diginet_body_check (+0x184) ---- *)

Lemma tkw_bc : forall (Wc : world segs) (md : Model) (m : word -> option byte) (B1 : list byte) (hd1 : Z)
    (X : list byte) (ws : list word) (R : bvmap 5 word) (lenb ret : Z) (Q' : world segs -> config -> Prop),
  tkw_inv Wc m md B1 hd1 X ws ->
  YK11.getr R 10 = w64 bp -> YK11.getr R 11 = w64 lenb ->
  YK11.getr R 2 = Z_to_bv 64 SP' -> YK11.getr R 3 = w64 (as_gp B) -> YK11.getr R 4 = w64 (as_tp B) ->
  YK11.getr R 1 = Z_to_bv 64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
  0 <= lenb <= 1484 ->
  (forall (W2 : world segs) regs2 mem2 md2,
     tkw_inv W2 mem2 md2 B1 hd1 X ws -> aregs_preserved R regs2 ->
     YK11.getr regs2 10 = w64 (DgnLib.body_check (firstn (Z.to_nat lenb) X)) ->
     SRr segs W2 (mkCfg (YK11.mkst regs2 (Z_to_bv 64 ret) mem2 (YK11.seg_rom segs)) md2) Q') ->
  SRr segs Wc (mkCfg (YK11.mkst R (Z_to_bv 64 TK_BC) m (YK11.seg_rom segs)) md) Q'.
Proof.
  intros Wc md m B1 hd1 X ws R lenb ret Q' INV R10 R11 R2 R3 R4 R1 Hret Hre Hlb K'.
  pose proof INV as (ly2 & S2 & J & HF & HP & HMO & K & HTW & LW & FR & HDC & (jb & BLC) & LX & GX).
  pose proof tkw_spf as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof tkw_consts as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  pose proof tkw_addrs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  pose proof tkw_o16 as (O16 & ONEG & OBUD & OAL).
  pose proof tkw_cellf as (B0 & B63 & BM & B4 & Bce & L0 & L63 & LM & H0 & H63 & HM & OL & OH).
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  destruct (tkw_stkf _ _ _ _ _ J) as (STKa & STKb & RFR & SP0 & SP63 & SPLO & SPCE).
  unfold amem_range in BM.
  assert (Hsp : spZ R = SP') by (unfold spZ at 1; rewrite R2; apply unsigned_lit; lia).
  destruct (tkw_lay _ _ _ _ _ J) as (Hfa & Elo & Ehi).
  destruct (tkw_lay _ _ _ _ _ HJ) as (_ & Elo0 & Ehi0).
  set (bb := firstn (Z.to_nat lenb) X).
  assert (Lbb : length bb = Z.to_nat lenb) by (unfold bb; rewrite length_firstn; lia).
  assert (GBB : garr8 segs (mrestrict (w_H Wc) m) bp (TW.zs bb)).
  { apply tkw_garr8_of_view. intros j Hj. rewrite Lbb in Hj. unfold bb. rewrite nth_firstn.
    destruct (Nat.ltb_spec j (Z.to_nat lenb)); [|lia]. exact (tkw_view_garr8 (w_H Wc) m bp X j GX ltac:(lia)). }
  assert (SRC : (0 < length bb)%nat -> trans_src_ok B ly2 S2 Wc m bp (Z.of_nat (length bb))).
  { intros Hpos. rewrite Lbb. rewrite Z2Nat.id by lia.
    apply (trans_src_ok_inner B lyc Sc W memc ly2 S2 Wc m bp lenb).
    - intros bm Hbm. exact (Permutation_in _ (Permutation_sym HP) Hbm).
    - intros f Hf. rewrite HF. exact Hf.
    - exact Hfa.
    - rewrite Elo, Elo0. reflexivity.
    - rewrite Ehi, Ehi0. reflexivity.
    - exact (tkw_rd_cur Wc m X bp lenb K GX LX ltac:(lia) ltac:(lia) ltac:(lia)).
    - right. split.
      + left. destruct HFAKE as (cid & pos & Hin & F1 & F2). exists cid, pos. split; [exact Hin|].
        lia.
      + exact (trans_rd_ok_sub W memc bp TAKE_BODY bp lenb HRDB ltac:(lia) ltac:(lia) ltac:(lia)). }
  eapply SRr_bind.
  { apply (@gx_call_cg fx rc tfib_sink_head segs B MT G STK sp0 FP ly St W0 mem0 md0 own ly2 S2 Wc m md k
             (mkCfg (YK11.mkst R (Z_to_bv 64 TK_BC) m (YK11.seg_rom segs)) md) R TRANS_BC_STK TRANS_BC_EV 0
             (fun _ => False) (fun regs2 _ _ => YK11.getr regs2 10 = w64 (DgnLib.body_check bb)) HGX HGN J).
    intros memS JS.
    apply (ABC fx STK sp0 FP ly St W0 memS md0 own ly2 S2 Wc m md k R bp bb JS).
    - rewrite R1. apply YK0s.ret_ok_even. rewrite unsigned_lit by lia. exact Hre.
    - unfold raZ. rewrite R1, unsigned_lit by lia. lia.
    - exact R3.
    - exact R4.
    - exact R10.
    - rewrite Lbb, Z2Nat.id by lia. exact R11.
    - rewrite Hsp. exact OAL.
    - rewrite Hsp. lia.
    - rewrite Hsp. lia.
    - left. lia.
    - exact SRC.
    - intros _. unfold decode_off_win. rewrite Hsp, Lbb, Z2Nat.id by lia. left. lia.
    - exact GBB.
    - rewrite HF. exact HCNT.
    - lia. }
  cbv beta. intros W2 c2 _ (ly3 & S3 & regs2 & mem2 & md2 & e & -> & He & J3 & HP2 & HF3 & HPm3 & KB & HMO3 & HR10 & HGK).
  assert (E0 : e = 0) by (unfold TRANS_BC_EV in He; lia). subst e. rewrite Z.add_0_r in J3.
  rewrite Hsp in KB. rewrite R1.
  assert (HF3' : frames S3 = frames Sc) by (rewrite HF3; exact HF).
  assert (HP3' : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc)) by exact (Permutation_trans HPm3 HP).
  apply (K' W2 regs2 mem2 md2); [|exact HP2 | exact HR10].
  exists ly3, S3. split; [exact J3|]. split; [exact HF3'|]. split; [exact HP3'|].
  split; [exact (mle_station MT Sc S2 S3 0 0 MTL HMO HMO3)|].
  split; [exact (tkw_K_bc ly2 S2 Wc m md ly3 S3 W2 mem2 md2 J HP HF J3 HP3' K KB)|].
  split.
  { apply (tw_kept_GA (aview segs (w_H Wc) m)); [exact HTW|].
    intros b n i Hin Hi. apply HGK. unfold inG. apply Exists_exists. exists (b, n).
    split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  split; [exact LW|].
  split.
  { apply (tkw_cells_keep (w_H Wc) (w_H W2) m mem2 SP' _ FR). rewrite (tkw_fr_size ws LW). intros i Hi.
    split; [exact (tkw_win_pres ly2 S2 Wc m md (SP' + i) J ltac:(lia))|].
    split; [exact (tkw_win_pres ly3 S3 W2 mem2 md2 (SP' + i) J3 ltac:(lia))|].
    exact (tkw_frame_bc ly2 S2 Wc m W2 mem2 (SP' + i) ltac:(lia) KB). }
  split.
  { apply (tkw_cells_keep (w_H Wc) (w_H W2) m mem2 hdp _ HDC). cbn [cells_size csize]. intros i Hi.
    split; [exact (proj1 (proj2 (tkw_twr_cur hdp 4 ly2 S2 Wc m md (hdp + i) HTWH HNGH ltac:(lia) J HP)))|].
    split; [exact (proj1 (proj2 (tkw_twr_cur hdp 4 ly3 S3 W2 mem2 md2 (hdp + i) HTWH HNGH ltac:(lia) J3 HP3')))|].
    exact (tkw_cell_bc hdp 4 ly2 S2 Wc m md W2 mem2 (hdp + i) HTWH HNGH HRDH OH ltac:(lia) J HP HF KB). }
  split.
  { exists jb. apply (tkw_cells_keep (w_H Wc) (w_H W2) m mem2 blp _ BLC). cbn [cells_size csize]. intros i Hi.
    split; [exact (proj1 (proj2 (tkw_twr_cur blp 8 ly2 S2 Wc m md (blp + i) HTWL HNGL ltac:(lia) J HP)))|].
    split; [exact (proj1 (proj2 (tkw_twr_cur blp 8 ly3 S3 W2 mem2 md2 (blp + i) HTWL HNGL ltac:(lia) J3 HP3')))|].
    exact (tkw_cell_bc blp 8 ly2 S2 Wc m md W2 mem2 (blp + i) HTWL HNGL HRDL OL ltac:(lia) J HP HF KB). }
  split; [exact LX|].
  apply (tkw_garr8_ext (w_H Wc) (w_H W2) m mem2 bp (TW.zs X)); [|exact GX].
  intros j Hj. unfold TW.zs in Hj. rewrite length_map in Hj.
  exact (tkw_body_bc ly2 S2 Wc m md W2 mem2 (bp + Z.of_nat j) ltac:(unfold TAKE_BODY; lia) J HF KB).
Qed.

(* The model's result, read off the option without inversion on it. *)
Lemma tkw_someq : forall (B2 b2 : list byte) (l2 h2 t2 k2 : Z),
  Some (B2, (b2, l2, h2, t2, k2)) = Some (BF, (body, len, hd, taken, keptF)) ->
  B2 = BF /\ b2 = body /\ l2 = len /\ h2 = hd /\ t2 = taken /\ k2 = keptF.
Proof.
  intros B2 b2 l2 h2 t2 k2 Hq.
  split; [exact (f_equal (fun o => match o with Some (W2, _) => W2 | None => [] end) Hq)|].
  split; [exact (f_equal (fun o => match o with Some (_, (b, _, _, _, _)) => b | None => [] end) Hq)|].
  split; [exact (f_equal (fun o => match o with Some (_, (_, l, _, _, _)) => l | None => 0 end) Hq)|].
  split; [exact (f_equal (fun o => match o with Some (_, (_, _, h, _, _)) => h | None => 0 end) Hq)|].
  split; [exact (f_equal (fun o => match o with Some (_, (_, _, _, t, _)) => t | None => 0 end) Hq)
        | exact (f_equal (fun o => match o with Some (_, (_, _, _, _, kq)) => kq | None => 0 end) Hq)].
Qed.

Lemma tkw_somet : forall (B2 : list byte) (k2 : Z),
  Some (B2, k2) = Some (BF, keptF) -> B2 = BF /\ k2 = keptF.
Proof.
  intros B2 k2 Hq.
  split; [exact (f_equal (fun o => match o with Some (W2, _) => W2 | None => [] end) Hq)
        | exact (f_equal (fun o => match o with Some (_, kq) => kq | None => 0 end) Hq)].
Qed.

(* A run that writes nothing: only the model is materialised. *)
Lemma tkw_inv_run0 : forall (Wc : world segs) m md md2 B2 hd2 X2 ws,
  tkw_inv Wc m md B2 hd2 X2 ws -> same_but_materialized md md2 -> tkw_inv Wc m md2 B2 hd2 X2 ws.
Proof.
  intros Wc m md md2 B2 hd2 X2 ws (ly2 & Sx & J & HF & HP & HMO & K & HTW & LW & FR & HDC & BLC & LX & GX) HS.
  exists ly2, Sx.
  split; [apply (tkw_jrun ly2 Sx Wc m md m md2 (fun _ => False) J HP);
            [intros x _; reflexivity | intros x Hx; exact Hx | exact HS | intros a []]|].
  split; [exact HF|]. split; [exact HP|]. split; [exact HMO|]. split; [exact K|]. split; [exact HTW|].
  split; [exact LW|]. split; [exact FR|]. split; [exact HDC|]. split; [exact BLC|].
  split; [exact LX | exact GX].
Qed.

(* ---- the cuts ---- *)

(* The loop head at turn i with S n turns left. *)
Definition tkw_head_P (n : nat) : Prop.
Proof using All.
  exact (
    forall (Wc : world segs) (md : Model) (m : word -> option byte) (B1 : list byte) (hd1 : Z) (X : list byte)
      (j38 : word) (i taken1 kept1 len1 : Z) (body1 : list byte)
      (ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 : word) (ms : machine_state),
    ms_eqv (tk_at_L ra t2 s0 a1 a2 a3 s2 s8 s10 s11 t3 t4 t5 t6 GP TP (@YK11.fp_regs fx) (@YK11.fp_csr fx) m
              SP' i taken1 kept1 len1) ms ->
    tkw_inv Wc m md B1 hd1 X (tk_spill bp blp hdp allow j38) ->
    tkw_mh (Datatypes.S n) B1 i taken1 kept1 len1 hd1 body1 X ->
    SRr segs Wc (mkCfg ms md) Q
  ).
Defined.

(* The end of turn i with n turns left; every path into TK_J has s8 = &s->queue[i] - 1760. *)
Definition tkw_join_P (n : nat) : Prop.
Proof using All.
  exact (
    forall (Wc : world segs) (md : Model) (m : word -> option byte) (B1 : list byte) (hd1 : Z) (X : list byte)
      (j38 : word) (i taken1 kept1 len1 : Z) (body1 : list byte)
      (ra t2 s0 a0 a1 a2 a3 s2 s10 s11 t3 t4 t5 t6 : word) (ms : machine_state),
    ms_eqv (tk_at_J ra t2 s0 a0 a1 a2 a3 s2 (Z_to_bv 64 (TK_S + 32 * i)) s10 s11 t3 t4 t5 t6 GP TP
              (@YK11.fp_regs fx) (@YK11.fp_csr fx) m SP' i taken1 kept1 len1) ms ->
    tkw_inv Wc m md B1 hd1 X (tk_spill bp blp hdp allow j38) -> tkw_mj n B1 i taken1 kept1 len1 hd1 body1 X ->
    SRr segs Wc (mkCfg ms md) Q
  ).
Defined.

End Call.
End Walk.


