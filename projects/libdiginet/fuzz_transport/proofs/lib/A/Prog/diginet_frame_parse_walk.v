(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_leafb.v (origin/ossv/recipes 88154566652a) for reac-repacer/fuzz_uci's image A: module paths and names changed, the cell rows are this unit's AsanCells rows, and the read-only-image helper is dropped. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCcLeafb.v, with its module paths and module names changed; 1109 of its 1232 lines of code are new or changed and 398 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac-repacer/fuzz_uci's check_value in image A, proving the frozen statement
   lib/A/Prog/check_value_cg.v uci_check_value_cg_holds_stmt, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/
   crtA_walk.v, crtA_w_head.v, crtA_w_tail.v, crtA_encw.v, crtA_w_mid.v and crtA_close.v (origin/ossv/recipes
   88154566652a): footprint runs carried into SRr, an inner journal over the call's stack window, each call cut by its
   callee contract, and the helpers of those files (crtA_run, crtA_ms_shape, crtA_ms_reg, crtT_regs_of, crtA_trace0,
   crtT_chain_nil, crtA_byte_eq, crtT_rw_cells_ext, crtA_rng_vis, crtT_aj_md, crtT_not_old, crtT_perm_rm,
   crtA_addressable, crtA_rng_hull, crtA_vis_hull) restated at this unit's image. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_value_cgW.v, with its module paths and module names changed; 754 of its 894 lines of code are new or changed and 1092 lines of the source are left out. *)
(* diginet_frame_parse_walk: frame_diginet_frame_parse_cg (dgnframe_sigma DF_diginet_frame_parse) from the callee
   contract the statement names (__asan_memcpy), and the theorem frame_diginet_frame_parse_cg_holds.

   The walk keeps the CALLER's journal (the premise ajournal ... own lyc Sc W memc mdc k) and extends it at each step:
   a byte the call writes is in the caller's stack window (its own 48-byte frame and the ESTACK __asan_memcpy uses
   below it) or a byte of f, which the caller's frame_twr_ok lets it write. Beside the journal it tracks what it
   kept of the entry memory (fp_keep), the bytes still present (fp_pres) and its own frame (fp_frame).
     1. fp_head_stmt (lib/A/Prog/diginet_frame_parse_segs.v) from the entry: on a code that is not 0, the return;
     2. on code 0: __asan_memcpy (f, buf, 6) (YCbq.v aj_intrin_at; f is the caller's, buf placed by trans_src_ok),
        fp_mid_F, __asan_memcpy (f + 6, buf + 6, 6);
     3. fp_hdr1_stmt, fp_hdr2_stmt, fp_tail_stmt to the return;
     4. the post: the journal, the callee-saved registers, acall_kept with the written range frame_fp_wr f (the
        bytes of f the code never stores read back as fj from the cells), a0 = fr_code b and the 64 bytes at f. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_kit diginet_frame_parse_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit LeafCgFacts LeafCgGlue DgnTransportImg AsanKA
  TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_frame_parse_seg_head
  diginet_frame_parse_seg_hdr1 diginet_frame_parse_seg_hdr2 diginet_frame_parse_seg_tail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module AC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module AImg := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Img0.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
Module FF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportFevt.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ======================================================================== *)
(* Image-level helpers                                                        *)
(* ======================================================================== *)

Lemma fp_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. exact DgnTransportImg.transport_segs_low. Qed.

Lemma fp_outside_dec : forall (L : list (Z * Z)) a, outside L a \/ ~ outside L a.
Proof.
  induction L as [|[lo hi] L IH]; intros a; [left; exact I|].
  cbn [outside]. destruct (IH a) as [H|H].
  - destruct (Z_lt_le_dec a lo) as [H1|H1]; [left; split; [lia | exact H]|].
    destruct (Z_lt_le_dec a hi) as [H2|H2]; [right; intros [H3 _]; lia | left; split; [lia | exact H]].
  - right. intros [_ H3]. exact (H H3).
Qed.

(* aview after a footprint run, outside the ranges it may change. *)
Lemma fp_aview_munch : forall (L : list (Z * Z)) (H : word -> bool) m m' a,
  munch L m m' -> 0 <= a < 2 ^ 64 -> outside L a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
  intros L H m m' a MU Ha Ho. unfold aview, YP09.mbyte, mrestrict.
  rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. rewrite fp_u64 by exact Ha. exact Ho.
Qed.

(* Outside the image, a writable view holds a byte of the overlay. *)
Lemma fp_some_of_wview : forall (m : word -> option byte) (x : word),
  wview AImg.rsegs m x <> None -> ~ in_img tfibsegs (bv_unsigned x) -> m x <> None.
Proof.
  intros m x Hw Hi. unfold wview in Hw. destruct (m x) as [bb|] eqn:E; [discriminate|]. exfalso.
  rewrite (LeafCgGlue.find_segment_out AImg.rsegs (bv_unsigned x) 1) in Hw; [exact (Hw eq_refl)|lia|].
  intros sg Hin Hr. apply Hi. exists sg. split; [exact Hin | lia].
Qed.

(* A present byte stays present across a footprint run (munch L, wmono) whose ranges lie outside the image. *)
Lemma fp_pres_run : forall (L : list (Z * Z)) (H : word -> bool) m m' a,
  munch L m m' -> wmono AImg.rsegs m m' -> (forall z, ~ outside L z -> ~ in_img tfibsegs z) ->
  0 <= a < 2 ^ 64 -> apresent H m a -> apresent H m' a.
Proof.
  intros L H m m' a MU WM Hni Ha (Hh & bb & Hb). split; [exact Hh|].
  destruct (fp_outside_dec L a) as [Ho|Ho].
  - exists bb. rewrite (MU (Z_to_bv 64 a)); [exact Hb|]. rewrite fp_u64 by exact Ha. exact Ho.
  - assert (Hw : wview AImg.rsegs m (Z_to_bv 64 a) <> None) by (unfold wview; rewrite Hb; discriminate).
    pose proof (fp_some_of_wview m' (Z_to_bv 64 a) (WM _ Hw)) as Hs.
    rewrite fp_u64 in Hs by exact Ha. specialize (Hs (Hni a Ho)).
    destruct (m' (Z_to_bv 64 a)) as [bb'|]; [exists bb'; reflexivity | exfalso; exact (Hs eq_refl)].
Qed.

Lemma fp_byte_id : forall x : byte, Z_to_bv 8 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* bytes_at from aview. *)
Lemma fp_bytes_at_of_aview : forall (W : world tfibsegs) mem a (l : list byte),
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall i, (i < length l)%nat ->
     aview tfibsegs (w_H W) mem (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0)))) ->
  bytes_at AImg.rsegs mem a l.
Proof.
  intros W mem a l H0 H1 HA. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite (fp_mrd_of_aview W mem _ _ (HA i Hi)), fp_byte_id. symmetry. apply nth_error_nth'. exact Hi.
Qed.

(* aview from bytes_at, at visible bytes. *)
Lemma fp_aview_of_bytes : forall (W : world tfibsegs) mem a (l : list byte) i,
  bytes_at AImg.rsegs mem a l -> (i < length l)%nat -> w_H W (Z_to_bv 64 (a + Z.of_nat i)) = false ->
  aview tfibsegs (w_H W) mem (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).
Proof.
  intros W mem a l i (_ & _ & HB) Hi Hv. rewrite (fp_aview_mrd W mem _ Hv).
  rewrite (HB i Hi), (nth_error_nth' l (Z_to_bv 8 0) Hi). reflexivity.
Qed.

(* rw_cells from aview and presence. *)
Lemma fp_rw_cells_of : forall (W : world tfibsegs) mem a (cs : list cell),
  cells_wf cs -> 0 <= a -> a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall i, (i < cells_size cs)%nat ->
     aview tfibsegs (w_H W) mem (a + Z.of_nat i) = Some (bv_unsigned (nth i (cells_bytes cs) (Z_to_bv 8 0)))) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> apresent (w_H W) mem (a + i)) ->
  rw_cells AImg.rsegs mem a cs.
Proof.
  intros W mem a cs Hwf H0 H1 HA HP. pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - apply (fp_bytes_at_of_aview W); [exact H0 | rewrite L; exact H1 |]. intros i Hi. apply HA. lia.
  - split; [exact H0|]. split; [exact H1|]. intros i Hi.
    destruct (HP i Hi) as (_ & bb & Hb). unfold wview, wa. rewrite Hb. discriminate.
Qed.

(* garr8 of the bytes of cells, at visible bytes. *)
Lemma fp_garr8_of_rw_cells : forall (W : world tfibsegs) mem a (cs : list cell),
  rw_cells AImg.rsegs mem a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> w_H W (Z_to_bv 64 (a + i)) = false) ->
  garr8 tfibsegs (mrestrict (w_H W) mem) a (map (fun x : byte => bv_unsigned x) (cells_bytes cs)).
Proof.
  intros W mem a cs [[Hwf HB] _] Hv. pose proof (cells_bytes_length cs Hwf) as L.
  apply fp_garr8_of_aview. intros j Hj. rewrite length_map in Hj.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite map_nth. split.
  - apply (fp_aview_of_bytes W mem a _ j HB Hj). apply Hv. lia.
  - apply bv_unsigned_in_range.
Qed.

Lemma fp_nth_skipn : forall (l : list byte) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l i d; [reflexivity|].
  destruct l as [|x l]; cbn [skipn]; [destruct i; reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma fp_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros l i d Hi; [lia|].
  destruct l as [|x l]; cbn [firstn]; [reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Lemma fp_nth_cells_app : forall (cs1 cs2 : list cell) i d, cells_wf cs1 -> (cells_size cs1 <= i)%nat ->
  nth i (cells_bytes (cs1 ++ cs2)) d = nth (i - cells_size cs1) (cells_bytes cs2) d.
Proof.
  intros cs1 cs2 i d Hwf Hi. rewrite cells_bytes_app, app_nth2 by (rewrite cells_bytes_length by exact Hwf; lia).
  rewrite cells_bytes_length by exact Hwf. reflexivity.
Qed.

(* The 64 bytes at f the code never stores (14, 15, 59 .. 63) read back in parse_cells as the bytes before. *)
Lemma fp_parse_unwritten : forall (buf : Z) (b fj : list byte) (i : nat),
  (12 <= length b)%nat -> length fj = 64%nat -> (i = 14 \/ i = 15 \/ 59 <= i < 64)%nat ->
  nth i (cells_bytes (PParse.parse_cells buf b fj)) (Z_to_bv 8 0) = nth i fj (Z_to_bv 8 0).
Proof.
  intros buf b fj i Hb Hfj Hi.
  assert (L1 : length (fr_dst b) = 6%nat) by (unfold fr_dst; rewrite length_firstn; lia).
  assert (L2 : length (fr_src b) = 6%nat) by (unfold fr_src; rewrite length_firstn, length_skipn; lia).
  destruct Hi as [Hi | [Hi | Hi]].
  1, 2: lazymatch goal with |- context [PParse.parse_cells ?u ?v ?w] =>
          replace (PParse.parse_cells u v w) with
            ([CB 6 (fr_dst v); CB 6 (fr_src v); C2 (Z_to_bv 64 (fr_ethertype v))] ++
             (CB 2 (firstn 2 (skipn 14 w)) :: skipn 4 (PParse.parse_cells u v w))) by reflexivity end;
        rewrite fp_nth_cells_app by (cbn [cells_wf cell_wf cells_size csize]; repeat split; lia);
        cbn [cells_size csize Nat.add]; cbn [cells_bytes cbytes];
        rewrite app_nth1 by (rewrite length_firstn, length_skipn; lia);
        rewrite fp_nth_firstn by lia; rewrite fp_nth_skipn; f_equal; lia.
  lazymatch goal with |- context [PParse.parse_cells ?u ?v ?w] =>
    replace (PParse.parse_cells u v w) with (firstn 16 (PParse.parse_cells u v w) ++ [CB 5 (skipn 59 w)])
      by reflexivity end.
  rewrite fp_nth_cells_app.
  - cbn [firstn PParse.parse_cells cells_size csize Nat.add]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite fp_nth_skipn. f_equal. lia.
  - cbn [firstn PParse.parse_cells cells_wf cell_wf].
    rewrite length_firstn, length_skipn. repeat split; lia.
  - cbn [firstn PParse.parse_cells cells_size csize Nat.add]. lia.
Qed.

Lemma fp_u64r : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. exact u64_range. Qed.

(* rw_cells across a footprint run, for cells outside the ranges it may change. *)
Lemma fp_rw_cells_munch : forall (L : list (Z * Z)) m m' A (cs : list cell),
  rw_cells AImg.rsegs m A cs -> munch L m m' ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> outside L a) -> rw_cells AImg.rsegs m' A cs.
Proof.
  intros L m m' A cs RW MU Ho. pose proof RW as [_ (Wa & Wl & _)].
  apply (fp_rw_cells_ext m m' A cs RW). intros a Ha. apply MU. unfold wa. rewrite fp_u64 by lia. exact (Ho a Ha).
Qed.

Lemma fp_munch_trans : forall (L : list (Z * Z)) m1 m2 m3, munch L m1 m2 -> munch L m2 m3 -> munch L m1 m3.
Proof. intros L m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

Lemma fp_wmono_trans : forall m1 m2 m3, wmono AImg.rsegs m1 m2 -> wmono AImg.rsegs m2 m3 -> wmono AImg.rsegs m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. exact (H2 x (H1 x Hx)). Qed.

(* The shadow bytes and the shadow hull of an application range lie in [kLowMemEnd, kHighShadowEnd). *)
Lemma fp_shadow_region : forall x, 0 <= x < kHighMemEnd ->
  kLowMemEnd <= shadow_of_addr SHADOW_OFF x < kHighShadowEnd.
Proof. intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *. Z.div_mod_to_equations. lia. Qed.

Lemma fp_hull_region : forall p n s, 0 <= p -> 0 < n -> p + n <= kHighMemEnd ->
  YG0f.shadow_addr p / 8 * 8 <= s < YG0f.shadow_addr (p + n - 1) / 8 * 8 + 8 ->
  kLowMemEnd <= s < kHighShadowEnd.
Proof.
  intros p n s H0 Hn H1 Hs. unfold YG0f.shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma fp_hull_sub : forall p n p' n' s, 0 <= p -> 0 < n' -> p <= p' -> p' + n' <= p + n ->
  YG0f.shadow_addr p' / 8 * 8 <= s < YG0f.shadow_addr (p' + n' - 1) / 8 * 8 + 8 ->
  YG0f.shadow_addr p / 8 * 8 <= s < YG0f.shadow_addr (p + n - 1) / 8 * 8 + 8.
Proof.
  intros p n p' n' s H0 Hn H1 H2 Hs. unfold YG0f.shadow_addr, SHADOW_OFF in *.
  Z.div_mod_to_equations. lia.
Qed.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy).
(* The four footprint runs (lib/A/Prog/diginet_frame_parse_seg_*.v prove them). *)
Hypothesis HEAD : fp_head_stmt.
Hypothesis HDR1 : fp_hdr1_stmt.
Hypothesis HDR2 : fp_hdr2_stmt.
Hypothesis TAIL : fp_tail_stmt.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).
Ltac kp_by HP i K := etransitivity; [apply (HP i); unfold acallee_saved; lia | exact K].

Section Entry.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (buf f : Z)
  (b fj : list byte).
Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 buf.
Hypothesis H11 : YK11.getr regs 11 = w64 (Z.of_nat (length b)).
Hypothesis H12 : YK11.getr regs 12 = w64 f.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - TRANS_FP_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hbuf0 : buf <> 0.
Hypothesis Hf0 : f <> 0.
Hypothesis Hsrc : trans_src_ok B lyc Sc W memc buf (Z.of_nat (length b)).
Hypothesis Hbw : decode_off_win regs TRANS_FP_STK buf (Z.of_nat (length b)).
Hypothesis Hgb : garr8 segs (mrestrict (w_H W) memc) buf (map bz b).
Hypothesis Hlfj : length fj = 64%nat.
Hypothesis Hgf : garr8 segs (mrestrict (w_H W) memc) f (map bz fj).
Hypothesis Hfake : decode_in_fake lyc Sc f TRANS_FP_F_SIZE.
Hypothesis Htwr : decode_twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) f TRANS_FP_F_SIZE.
Hypothesis Hrd : decode_rd_ok W memc f TRANS_FP_F_SIZE.
Hypothesis Hwin : decode_off_win regs TRANS_FP_STK f TRANS_FP_F_SIZE.
Hypothesis Hdisj : (0 < length b)%nat -> f + TRANS_FP_F_SIZE <= buf \/ buf + Z.of_nat (length b) <= f.

Local Abbreviation SP := (spZ regs).
Local Abbreviation LEN := (Z.of_nat (length b)).
Local Abbreviation J m md := (ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k).
Local Abbreviation POST := (trans_fp_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs buf f b fj).
Local Abbreviation RNGW := (LCK.RNG_W (world segs) (@w_H segs) W).

(* ---- facts of the entry ---- *)

Lemma fp_HAR0 : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma fp_sp : sp0 mod 16 = 0 /\ YM05.alloc_ceiling + TRANS_FP_STK <= SP /\
  (SP <= 2 ^ 47 /\ TRANS_FP_STK = 4144 /\ 0x7fff7f800000 <= YM05.alloc_ceiling <= 0x7fffff800000).
Proof.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (H16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  split; [exact H16|]. split; [lia|]. split; [lia|]. split; [reflexivity | exact CEIL].
Qed.

(* Where buf lies, for every b (the empty one included): a heap block (al_blocks: in [4096, alloc_ceiling), in
   application memory), or with decode_rd_ok (0 <= buf, amem_range); buf <> 0. *)
Lemma fp_bufnums : 0 < buf /\ buf + LEN <= 2 ^ 47 /\ amem_range buf LEN.
Proof.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  destruct Hsrc as [(bA & nA & HinA & H1 & H2) | (_ & (_ & _ & _ & Ham & H0 & H63))].
  - pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA fp_HAR0 HinA) as (_ & H4 & Hc & Happ & _).
    assert (nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. split; [lia|]. split; lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. split; [lia|]. split; lia.
Qed.

(* The bytes at buf, when there are some: decode_rd_ok in every case (DgnTransportCg.v trans_src_ok_rd). *)
Lemma fp_rdb : (0 < length b)%nat -> decode_rd_ok W memc buf LEN.
Proof. intros HL. exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc buf LEN fp_HAR0 Hsrc ltac:(lia)). Qed.

Lemma fp_frm : exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= f /\
  f + 64 <= frame_addr lyc cid pos + fs_frame_bytes cid /\ 4096 <= frame_addr lyc cid pos /\
  frame_addr lyc cid pos + fs_frame_bytes cid <= YM05.alloc_ceiling /\ in_app (frame_addr lyc cid pos) (fs_frame_bytes cid).
Proof.
  destruct Hfake as (cid & pos & Hin & H1 & H2).
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos fp_HAR0 Hin) as (Bf0 & Bfc & Hfa).
  exists cid, pos. unfold TRANS_FP_F_SIZE in H2.
  split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Hfa].
Qed.

Lemma fp_nums : 0 < buf /\ buf + LEN <= 2 ^ 47 /\ 4096 <= f /\ f + 64 <= YM05.alloc_ceiling /\
  amem_range buf LEN /\ in_app f 64 /\ 0x7fff7f800000 <= YM05.alloc_ceiling <= 0x7fffff800000.
Proof.
  destruct fp_bufnums as (B1 & B2 & B3).
  destruct fp_frm as (cid & pos & _ & G1 & G2 & G3 & G4 & G5).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact B3|]. split; [apply (in_app_sub _ _ _ _ G5); lia|]. exact CEIL.
Qed.

(* Window bytes are present at every state of the caller's journal. *)
Lemma fp_win_pres : forall m md, J m md -> forall a, SP - TRANS_FP_STK <= a < SP -> apresent (w_H W) m a.
Proof.
  intros m md Jm a Ha. destruct Jm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  apply Hpres. lia.
Qed.

Lemma fp_buf_memc : forall i, (i < length b)%nat ->
  aview segs (w_H W) memc (buf + Z.of_nat i) = Some (bv_unsigned (nth i b (Z_to_bv 8 0))).
Proof.
  intros i Hi. rewrite (fp_garr8_aview (w_H W) memc buf _ i Hgb) by (rewrite length_map; exact Hi).
  rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hi). rewrite map_nth. reflexivity.
Qed.

Lemma fp_f_memc : forall i, (i < 64)%nat ->
  aview segs (w_H W) memc (f + Z.of_nat i) = Some (bv_unsigned (nth i fj (Z_to_bv 8 0))).
Proof.
  intros i Hi. rewrite (fp_garr8_aview (w_H W) memc f _ i Hgf) by (rewrite length_map; lia).
  rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map; lia). rewrite map_nth. reflexivity.
Qed.

Lemma fp_f_pres : forall a, f <= a < f + 64 -> apresent (w_H W) memc a.
Proof. intros a Ha. exact (proj1 (proj2 (Htwr a ltac:(unfold TRANS_FP_F_SIZE; lia)))). Qed.

Lemma fp_f_vis : forall a, f <= a < f + 64 -> w_H W (Z_to_bv 64 a) = false.
Proof. intros a Ha. exact (proj1 (fp_f_pres a Ha)). Qed.

Lemma fp_buf_vis : forall a, buf <= a < buf + LEN -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. replace a with (buf + Z.of_nat (Z.to_nat (a - buf))) by lia.
  exact (fp_aview_vis W memc _ _ (fp_buf_memc (Z.to_nat (a - buf)) ltac:(lia))).
Qed.

Lemma fp_f_noimg : forall a, f <= a < f + 64 -> ~ in_img segs a.
Proof.
  intros a Ha. destruct fp_frm as (cid & pos & Hin & H1 & H2 & _).
  apply (frm_img segs B LAWS lyc Sc W memc mdc cid pos a fp_HAR0 Hin). lia.
Qed.

(* ---- the footprint ranges (RNG_W W: the bytes W does not hide) ---- *)

Lemma fp_rng_buf : ExecF.rng RNGW buf LEN.
Proof. pose proof fp_nums. apply fp_rng; [lia | lia |]. intros a Ha. exact (fp_buf_vis a Ha). Qed.

Lemma fp_rng_f : ExecF.rng RNGW f 64.
Proof. pose proof fp_nums. apply fp_rng; [lia | lia |]. intros a Ha. exact (fp_f_vis a Ha). Qed.

Lemma fp_rng_frame : ExecF.rng RNGW (SP - 48) 48.
Proof.
  pose proof fp_sp. apply fp_rng; [lia | lia |]. intros a Ha.
  exact (proj1 (fp_win_pres memc mdc HJ a ltac:(unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK; lia))).
Qed.

Lemma fp_shrng_buf : (30 <= length b)%nat -> fp_shrng RNGW buf LEN.
Proof.
  intros H30. pose proof fp_nums as (N1 & N2 & _ & _ & _ & _ & N7).
  destruct (fp_rdb ltac:(lia)) as (_ & _ & HV & _).
  pose proof (fp_rng_hull W memc buf LEN ltac:(lia) ltac:(lia) ltac:(lia) HV) as R.
  unfold fp_shrng. eapply ExecF.rng_sub'; [exact R|]. unfold AC.shadow_addr, AC.ASAN_K. Z.div_mod_to_equations. lia.
Qed.

Lemma fp_shrng_f : fp_shrng RNGW f 64.
Proof.
  pose proof fp_nums as (_ & _ & N3 & N4 & _ & _ & N7).
  destruct Hrd as (_ & _ & HV & _).
  pose proof (fp_rng_hull W memc f 64 ltac:(lia) ltac:(lia) ltac:(lia) HV) as R.
  unfold fp_shrng. eapply ExecF.rng_sub'; [exact R|]. unfold AC.shadow_addr, AC.ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* ---- what a step keeps of the entry memory ---- *)

Definition fp_keep (X : Z -> Prop) (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview segs (w_H W) m a = aview segs (w_H W) memc a.
Definition fp_pres (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) memc a -> apresent (w_H W) m a.
Definition fp_inwin (a : Z) : Prop := SP - TRANS_FP_STK <= a < SP.

Lemma fp_keep0 : forall X, fp_keep X memc.
Proof. intros X a _ _. reflexivity. Qed.

Lemma fp_pres0 : fp_pres memc.
Proof. intros a _ H. exact H. Qed.

Lemma fp_keep_run : forall (X : Z -> Prop) (L : list (Z * Z)) m m',
  fp_keep X m -> munch L m m' -> (forall a, ~ outside L a -> X a) -> fp_keep X m'.
Proof.
  intros X L m m' HK MU HL a Ha HX.
  destruct (fp_outside_dec L a) as [Ho|Ho]; [|exfalso; exact (HX (HL a Ho))].
  rewrite (fp_aview_munch L (w_H W) m m' a MU Ha Ho). exact (HK a Ha HX).
Qed.

Lemma fp_keep_mono : forall (X Y : Z -> Prop) m, fp_keep X m -> (forall a, X a -> Y a) -> fp_keep Y m.
Proof. intros X Y m HK HXY a Ha HY. apply HK; [exact Ha | intros HX; exact (HY (HXY a HX))]. Qed.

Lemma fp_pres_after : forall (L : list (Z * Z)) m m',
  fp_pres m -> munch L m m' -> wmono AImg.rsegs m m' -> (forall z, ~ outside L z -> ~ in_img segs z) -> fp_pres m'.
Proof. intros L m m' HP MU WM Hni a Ha Hp. exact (fp_pres_run L (w_H W) m m' a MU WM Hni Ha (HP a Ha Hp)). Qed.

(* The shadow facts of f at a later memory that kept the shadow region. *)
Lemma fp_ra_f : forall (X : Z -> Prop) m, fp_keep X m -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ X a) ->
  forall p n, f <= p -> p + n <= f + 64 -> 0 <= n ->
  range_addressable (aview segs (w_H W) m) SHADOW_OFF p n.
Proof.
  intros X m HK HX p n H1 H2 Hn x Hx. pose proof fp_nums as (_ & _ & N3 & N4 & _ & _ & N7).
  destruct Hrd as (_ & HRA & _).
  destruct (HRA x ltac:(unfold TRANS_FP_F_SIZE; lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
  pose proof (fp_shadow_region x ltac:(unfold kHighMemEnd; lia)) as R.
  rewrite (HK (shadow_of_addr SHADOW_OFF x) ltac:(unfold kHighShadowEnd, kLowMemEnd in R; lia) (HX _ R)). exact Hs.
Qed.

Lemma fp_hull_f : forall (X : Z -> Prop) m, fp_keep X m -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ X a) ->
  forall p n, f <= p -> p + n <= f + 64 -> 0 < n -> shadow_hull_vis (aview segs (w_H W) m) p n.
Proof.
  intros X m HK HX p n H1 H2 Hn s Hs. pose proof fp_nums as (_ & _ & N3 & N4 & _ & _ & N7).
  destruct Hrd as (_ & _ & HV & _).
  pose proof (fp_hull_sub f 64 p n s ltac:(lia) Hn H1 H2 Hs) as Hs'.
  pose proof (fp_hull_region f 64 s ltac:(lia) ltac:(lia) ltac:(unfold kHighMemEnd; lia) Hs') as R.
  rewrite (HK s ltac:(unfold kHighShadowEnd, kLowMemEnd in R; lia) (HX _ R)). exact (HV s Hs').
Qed.

(* The bytes at buf at the entry memory: range_addressable for every b (the empty range has no byte). *)
Lemma fp_ra_buf0 : range_addressable (aview segs (w_H W) memc) SHADOW_OFF buf LEN.
Proof.
  destruct (Nat.eq_dec (length b) 0) as [E|E].
  - intros x Hx. lia.
  - exact (proj1 (proj2 (fp_rdb ltac:(lia)))).
Qed.

(* The shadow facts of a part of buf at a later memory that kept the shadow region (decode_rd_ok's, at memc). *)
Lemma fp_ra_buf : forall (X : Z -> Prop) m, fp_keep X m -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ X a) ->
  forall p n, buf <= p -> p + n <= buf + LEN -> 0 < n ->
  range_addressable (aview segs (w_H W) m) SHADOW_OFF p n.
Proof.
  intros X m HK HX p n H1 H2 Hn x Hx. pose proof fp_bufnums as (B1 & B2 & _).
  destruct (fp_rdb ltac:(lia)) as (_ & HRA & _).
  destruct (HRA x ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
  pose proof (fp_shadow_region x ltac:(unfold kHighMemEnd; lia)) as R.
  rewrite (HK (shadow_of_addr SHADOW_OFF x) ltac:(unfold kHighShadowEnd, kLowMemEnd in R; lia) (HX _ R)). exact Hs.
Qed.

Lemma fp_hull_buf : forall (X : Z -> Prop) m, fp_keep X m -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ X a) ->
  forall p n, buf <= p -> p + n <= buf + LEN -> 0 < n -> shadow_hull_vis (aview segs (w_H W) m) p n.
Proof.
  intros X m HK HX p n H1 H2 Hn s Hs. pose proof fp_bufnums as (B1 & B2 & _).
  destruct (fp_rdb ltac:(lia)) as (_ & _ & HV & _).
  pose proof (fp_hull_sub buf LEN p n s ltac:(lia) Hn H1 H2 Hs) as Hs'.
  pose proof (fp_hull_region buf LEN s ltac:(lia) ltac:(lia) ltac:(unfold kHighMemEnd; lia) Hs') as R.
  rewrite (HK s ltac:(unfold kHighShadowEnd, kLowMemEnd in R; lia) (HX _ R)). exact (HV s Hs').
Qed.

(* A run that writes no memory: the journal follows its same_but_materialized. *)
Lemma fp_aj_md : forall m md md', J m md -> same_but_materialized md md' -> J m md'.
Proof.
  intros m md md' Jm Hs.
  eapply (ajournal_exec segs B LAWS fp_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k m md'
            (fun _ => False) Jm).
  - intros x _. reflexivity.
  - apply YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a Ha. destruct Ha.
Qed.

(* The journal across a footprint run whose ranges are bytes the caller lets the call write. *)
Lemma fp_aj_run : forall (L : list (Z * Z)) m m' md md',
  J m md -> munch L m m' -> wmono AImg.rsegs m m' -> same_but_materialized md md' ->
  (forall a, ~ outside L a -> 0 <= a < 2 ^ 64 /\ apresent (w_H W) m a /\ ~ in_img segs a /\
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  J m' md'.
Proof.
  intros L m m' md md' Jm MU WM SBM HL.
  apply (ajournal_exec segs B LAWS fp_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k m' md'
           (fun a => ~ outside L a) Jm).
  - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|].
    destruct (fp_outside_dec L (bv_unsigned x)) as [H|H]; [exact H | exfalso; exact (Hx H)].
  - intros x Hx. unfold mrestrict in *. destruct (w_H W x) eqn:Eh; [exact Hx|].
    pose proof (fp_u64r x) as Rx.
    assert (Hp : apresent (w_H W) m (bv_unsigned x)).
    { rewrite <- (Z_to_bv_bv_unsigned x) in Eh, Hx. split; [exact Eh|].
      destruct (m (Z_to_bv 64 (bv_unsigned x))) as [bb|]; [exists bb; reflexivity | exfalso; exact (Hx eq_refl)]. }
    destruct (fp_pres_run L (w_H W) m m' (bv_unsigned x) MU WM
                (fun z Hz => proj1 (proj2 (proj2 (HL z Hz)))) Rx Hp) as (_ & bb & Hb).
    rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate.
  - intros x Hx. destruct (fp_outside_dec L (bv_unsigned x)) as [H|H]; [exact (MU x H)|].
    destruct (HL _ H) as (_ & (Hh & _) & _). rewrite Z_to_bv_bv_unsigned in Hh. congruence.
  - exact SBM.
  - intros a Ha. exact (proj2 (proj2 (proj2 (HL a Ha)))).
Qed.

(* What the call kept, from what the walk tracked. *)
Lemma fp_acall_kept : forall m (E : Z -> Prop), (forall a, E a -> f <= a < f + 64) ->
  fp_keep (fun a => fp_inwin a \/ E a) m -> fp_pres m -> (forall a, fp_inwin a -> apresent (w_H W) m a) ->
  acall_kept segs B lyc Sc W memc W m (SP - TRANS_FP_STK) SP E.
Proof.
  intros m E HE HK HP HW.
  pose proof fp_sp as (_ & Hs1 & Hs2). pose proof fp_nums as (_ & _ & N3 & N4 & _ & _ & N7).
  split.
  { intros a Ha Hw. apply HK; [lia|]. intros [H|H]; [exact (Hw H) | pose proof (HE a H); lia]. }
  split.
  { intros bb mm i Hb Hi HnE.
    pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc bb mm fp_HAR0 Hb) as (_ & H4 & Hc & _).
    apply HK; [lia|]. intros [H|H]; [unfold fp_inwin in H; lia | exact (HnE H)]. }
  split.
  { intros a Hi Hns He. pose proof (fp_segs_low a Hi) as Hlo. apply HK; [unfold kLowMemEnd in Hlo; lia|].
    intros [H|H]; [unfold fp_inwin, kLowMemEnd in *; lia|]. exact (fp_f_noimg a (HE a H) Hi). }
  split.
  { intros cid pos a Hin Hr HnE.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos fp_HAR0 Hin) as (Bf0 & Bfc & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(unfold kHighMemEnd; lia)) as S1.
    pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid)
                  ltac:(unfold kHighMemEnd; lia)) as S2.
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as S3.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    assert (Ha : 0 <= a < YM05.alloc_ceiling) by (unfold kLowMemEnd, kHighShadowEnd in *; destruct Hr; lia).
    apply HK; [lia|]. intros [H|H]; [unfold fp_inwin in H; lia | exact (HnE H)]. }
  split.
  { intros a Ha Hw Hp. apply HP; [lia | exact Hp]. }
  exact HW.
Qed.

(* The return to the caller's ra with the post's facts. *)
Lemma fp_at_ret : forall regs2 m2 md2,
  J m2 md2 -> fp_keep (fun a => fp_inwin a \/ trans_fp_wr f a) m2 -> fp_pres m2 ->
  aregs_preserved regs regs2 -> YK11.getr regs2 10 = w64 (fr_code b) ->
  garr8 segs (mrestrict (w_H W) m2) f (trans_fp_f_bytes buf b fj) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) m2 (YK11.seg_rom segs)) md2) POST.
Proof.
  intros regs2 m2 md2 J2 HK HP HR H10' HG.
  apply SRr_ret. unfold trans_fp_post, decode_cg_post.
  exists lyc, Sc, regs2, m2, md2, 0.
  split; [reflexivity|]. split; [unfold TRANS_FP_EV; lia|].
  split; [rewrite Z.add_0_r; exact J2|]. split; [exact HR|]. split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply fp_acall_kept; [intros a Ha; unfold trans_fp_wr in Ha; lia | exact HK | exact HP |].
    intros a Ha. exact (fp_win_pres m2 md2 J2 a Ha). }
  split; [exact (mle_start MT Sc MTL)|]. split; [exact H10' | exact HG].
Qed.

Lemma fp_not_outside1 : forall lo hi a, ~ outside [(lo, hi)] a -> lo <= a < hi.
Proof.
  intros lo hi a H. destruct (Z_lt_le_dec a lo) as [H1|H1]; [exfalso; apply H; cbn; split; [lia | exact I]|].
  destruct (Z_lt_le_dec a hi) as [H2|H2]; [lia | exfalso; apply H; cbn; split; [lia | exact I]].
Qed.

(* ---- the registers and the frame the walk keeps between the calls ---- *)

(* sp = entry sp - 48, gp, tp, s0 = f, s1 = buf, s2 = size, s3 = ASAN_K, s4 = numbytes, s5 .. s11 the entry's. *)
Definition fp_kregs (rg : bvmap 5 word) : Prop :=
  GR rg 2 = w64 (SP - 48) /\ GR rg 3 = GR regs 3 /\ GR rg 4 = GR regs 4 /\
  GR rg 8 = w64 f /\ GR rg 9 = w64 buf /\ GR rg 18 = w64 LEN /\ GR rg 19 = w64 AC.ASAN_K /\
  GR rg 20 = w64 (fr_numbytes b) /\
  GR rg 21 = GR regs 21 /\ GR rg 22 = GR regs 22 /\ GR rg 23 = GR regs 23 /\ GR rg 24 = GR regs 24 /\
  GR rg 25 = GR regs 25 /\ GR rg 26 = GR regs 26 /\ GR rg 27 = GR regs 27.

Lemma fp_kregs_pres : forall r1 r2, fp_kregs r1 -> aregs_preserved r1 r2 -> fp_kregs r2.
Proof.
  intros r1 r2 (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27) HP.
  unfold fp_kregs.
  split; [kp_by HP 2 K2|]. split; [kp_by HP 3 K3|]. split; [kp_by HP 4 K4|]. split; [kp_by HP 8 K8|].
  split; [kp_by HP 9 K9|]. split; [kp_by HP 18 K18|]. split; [kp_by HP 19 K19|]. split; [kp_by HP 20 K20|].
  split; [kp_by HP 21 K21|]. split; [kp_by HP 22 K22|]. split; [kp_by HP 23 K23|]. split; [kp_by HP 24 K24|].
  split; [kp_by HP 25 K25|]. split; [kp_by HP 26 K26|]. kp_by HP 27 K27.
Qed.

(* The frame the prologue wrote: the caller's s4, s3, s2, s1, s0, ra at [entry sp - 48, entry sp). *)
Definition fp_frame (m : word -> option byte) : Prop :=
  rw_cells AImg.rsegs m (SP - 48) (fp_fr (GR regs 20) (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1)).

Lemma fp_frame_kept : forall m1 m2 md1 md2, fp_frame m1 -> J m1 md1 -> J m2 md2 ->
  (forall a, SP - 48 <= a < SP -> aview segs (w_H W) m2 a = aview segs (w_H W) m1 a) -> fp_frame m2.
Proof.
  intros m1 m2 md1 md2 F J1 J2 E. pose proof fp_sp as (_ & Hs1 & Hs2).
  apply (fp_rw_cells_ext m1 m2 _ _ F). intros a Ha.
  replace (Z.of_nat (cells_size (fp_fr (GR regs 20) (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1)))) with 48 in Ha by reflexivity.
  unfold wa. apply (fp_byte_eq (w_H W) (w_H W) m1 m2 a);
    [apply (fp_win_pres m1 md1 J1) | apply (fp_win_pres m2 md2 J2) | apply E];
    unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *; lia.
Qed.

(* What the body (fp_hdr1, fp_hdr2, fp_tail) leaves, from the memory m4 at FP_RET2 and the registers regs4. *)
Definition fp_body_post (m4 : word -> option byte) (regs4 : bvmap 5 word) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (m5 : word -> option byte),
    ms' = MS (mkR (GR regs 1) (Z_to_bv 64 (bv_unsigned (GR regs4 2) + FP_FRAME)) (GR regs4 3) (GR regs4 4)
                  (GR regs4 5) (GR regs4 6) (GR regs4 7) (GR regs 8) (GR regs 9) (Z_to_bv 64 0)
                  a1' a2' a3' a4' a5' a6' a7' (GR regs 18) (GR regs 19) (GR regs 20)
                  (GR regs4 21) (GR regs4 22) (GR regs4 23) (GR regs4 24) (GR regs4 25) (GR regs4 26)
                  (GR regs4 27) (GR regs4 28) (GR regs4 29) (GR regs4 30) (GR regs4 31))
             (@fp_regs fx) (ret_pc (GR regs 1)) (@fp_csr fx) None m5 (seg_rom AImg.rsegs) /\
    munch [(f, f + 64)] m4 m5 /\ wmono AImg.rsegs m4 m5 /\
    rw_cells AImg.rsegs m5 f (PParse.parse_cells buf b fj).

(* ---- FP_RET2: the body, then the return ---- *)
Lemma fp_at_ret2 : forall regs4 m4 md4,
  J m4 md4 -> fp_keep (fun a => fp_inwin a \/ f <= a < f + 12) m4 -> fp_pres m4 -> fp_frame m4 ->
  fp_kregs regs4 -> fr_code b = 0 ->
  (forall i, 0 <= i < 12 -> aview segs (w_H W) m4 (f + i) = aview segs (w_H W) memc (buf + i)) ->
  SRr segs W (@cfg_at fx segs FP_RET2 regs4 m4 md4) POST.
Proof.
  intros regs4 m4 md4 J4 HK4 HP4 HF4 HR4 Hc HB12.
  pose proof HR4 as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof fp_sp as (H16 & Hs1 & Hs2). pose proof fp_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  pose proof (fr_code_ok b Hc) as (L30 & ET & NB1 & NB2).
  pose proof Hbw as BW. unfold decode_off_win, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in BW.
  pose proof (Hdisj ltac:(lia)) as HD. unfold TRANS_FP_F_SIZE in HD.
  assert (KX : forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ (fp_inwin a \/ f <= a < f + 12)).
  { intros a Ha [H|H]; unfold fp_inwin, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *;
      unfold in_app, kLowMemEnd, kHighShadowEnd, kLowShadowBeg, kHighMemBeg in *; lia. }
  assert (HBM : forall i, (i < length b)%nat ->
            aview segs (w_H W) m4 (buf + Z.of_nat i) = Some (bv_unsigned (nth i b (Z_to_bv 8 0)))).
  { intros i Hi. rewrite (HK4 (buf + Z.of_nat i)); [exact (fp_buf_memc i Hi) | lia |].
    intros [H|H]; unfold fp_inwin, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in H; lia. }
  assert (PRE : fp_body_pre RNGW m4 buf f b (fp_copy_cells b fj)).
  { unfold fp_body_pre.
    split; [exact Hc|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split. { apply (fp_bytes_at_of_aview W m4 buf b); [lia | lia | exact HBM]. }
    split.
    { apply (fp_rw_cells_of W m4 f (fp_copy_cells b fj)).
      - cbn [fp_copy_cells cells_wf cell_wf]. unfold fr_dst, fr_src.
        split; [rewrite length_firstn; lia|]. split; [rewrite length_firstn, length_skipn; lia|].
        split; [rewrite length_skipn; lia | exact I].
      - lia.
      - cbn [fp_copy_cells cells_size csize Nat.add]. lia.
      - intros i Hi. cbn [fp_copy_cells cells_size csize Nat.add] in Hi.
        cbn [fp_copy_cells cells_bytes cbytes]. rewrite app_nil_r. unfold fr_dst, fr_src.
        destruct (Nat.lt_ge_cases i 12) as [Hi12|Hi12].
        + rewrite (HB12 (Z.of_nat i)) by lia. rewrite (fp_buf_memc i) by lia. f_equal. f_equal.
          destruct (Nat.lt_ge_cases i 6) as [Hi6|Hi6].
          * rewrite app_nth1 by (rewrite length_firstn; lia). rewrite fp_nth_firstn by lia. reflexivity.
          * rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
            rewrite app_nth1 by (rewrite length_firstn, length_skipn; lia).
            rewrite fp_nth_firstn by lia. rewrite fp_nth_skipn. f_equal. lia.
        + rewrite (HK4 (f + Z.of_nat i)); [| lia | intros [H|H]; unfold fp_inwin, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in H; lia].
          rewrite (fp_f_memc i) by lia. f_equal. f_equal.
          rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
          rewrite app_nth2 by (rewrite length_firstn, length_skipn; lia). rewrite length_firstn, length_skipn.
          rewrite fp_nth_skipn. f_equal. lia.
      - intros i Hi. cbn [fp_copy_cells cells_size csize Nat.add] in Hi.
        apply HP4; [lia|]. apply fp_f_pres. lia. }
    split; [reflexivity|].
    split; [exact HD|].
    split.
    { destruct (FF.decode_addressable_of (w_H W) m4 buf LEN (fp_ra_buf _ m4 HK4 KX buf LEN ltac:(lia) ltac:(lia) ltac:(lia))
                  N5 ltac:(lia) ltac:(lia)) as [HA _].
      exact HA. }
    split.
    { apply (fp_addressable W m4 f 64); [| lia | exact N6].
      exact (fp_ra_f _ m4 HK4 KX f 64 ltac:(lia) ltac:(lia) ltac:(lia)). }
    split; [exact fp_rng_buf|]. split; [exact fp_rng_f|]. split; [exact (fp_shrng_buf L30)|]. exact fp_shrng_f. }
  assert (SQ : bv_unsigned (GR regs4 2) = SP - 48) by (rewrite K2; unfold w64; apply fp_u64; lia).
  eapply (fp_run W regs4 m4 md4 FP_RET2 (fp_body_post m4 regs4)).
  { unfold LCK.ms_of_regs. rewrite K8, K9, K18, K19, K20. unfold w64.
    eapply ExecF.evtF_cut; [apply HDR1; [exact Hlfj | exact PRE] |].
    intros ms1 (x0 & x3 & x4 & x6 & x7 & ma & -> & MUa & WMa & PREa).
    eapply ExecF.evtF_cut; [apply HDR2; [exact Hlfj | exact PREa] |].
    intros ms2 (y0 & y4 & y5 & y6 & y7 & mb & -> & MUb & WMb & PREb).
    eapply ExecF.evtF_mono.
    { eapply TAIL with (c4 := GR regs 20) (c3 := GR regs 19) (c2 := GR regs 18) (c1 := GR regs 9)
                       (c0 := GR regs 8) (cra := GR regs 1) (fj := fj).
      - exact Hlfj.
      - exact PREb.
      - rewrite SQ.
        assert (HO : forall a, SP - 48 <= a < SP - 48 + Z.of_nat (cells_size (fp_fr (GR regs 20) (GR regs 19)
                       (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1))) -> outside [(f, f + 64)] a).
        { intros a Ha. replace (Z.of_nat (cells_size (fp_fr (GR regs 20) (GR regs 19) (GR regs 18) (GR regs 9) (GR regs 8) (GR regs 1)))) with 48 in Ha by reflexivity.
          cbn [outside]. split; [unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *; lia | exact I]. }
        exact (fp_rw_cells_munch _ ma mb _ _ (fp_rw_cells_munch _ m4 ma _ _ HF4 MUa HO) MUb HO).
      - rewrite SQ. unfold FP_FRAME. lia.
      - rewrite SQ. unfold FP_FRAME. left. unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *. lia.
      - rewrite SQ. unfold FP_FRAME. exact fp_rng_frame. }
    intros ms3 (a1' & a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU5 & WM5 & RW5).
    exists a1', a2', a3', a4', a5', a6', a7', m5. split; [reflexivity|].
    split; [exact (fp_munch_trans _ _ _ _ (fp_munch_trans _ _ _ _ MUa MUb) MU5)|].
    split; [exact (fp_wmono_trans _ _ _ (fp_wmono_trans _ _ _ WMa WMb) WM5)|]. exact RW5. }
  intros ms' md' (ms0 & (a1' & a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU5 & WM5 & RW5) & EQV) SBM.
  destruct (fp_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & G11 & G12 & G18 & G19 & G20 & G21 & G22 &
    G23 & G24 & G25 & G26 & G27).
  assert (Hret : ret_pc (GR regs 1) = GR regs 1) by (apply LeafCgFacts.ret_ok_stmt_YK0s; exact Hra).
  rewrite Hret in EQV. rewrite (fp_ms_shape _ _ _ _ EQV).
  assert (HNO : forall z, ~ outside [(f, f + 64)] z -> ~ in_img segs z)
    by (intros z Hz; exact (fp_f_noimg z (fp_not_outside1 _ _ _ Hz))).
  pose proof RW5 as [[Hwf5 BB5] _].
  assert (CS5 : cells_size (PParse.parse_cells buf b fj) = 64%nat) by reflexivity.
  apply fp_at_ret.
  - apply (fp_aj_run [(f, f + 64)] m4 m5 md4 md' J4 MU5 WM5 SBM).
    intros a Ha. pose proof (fp_not_outside1 _ _ _ Ha) as Ha'.
    split; [lia|]. split; [apply HP4; [lia | exact (fp_f_pres a Ha')]|].
    split; [exact (fp_f_noimg a Ha')|]. exact (proj1 (Htwr a ltac:(unfold TRANS_FP_F_SIZE; lia))).
  - intros a Ha HX.
    destruct (fp_outside_dec [(f, f + 64)] a) as [Ho|Ho].
    + rewrite (fp_aview_munch _ (w_H W) m4 m5 a MU5 Ha Ho). apply HK4; [exact Ha|].
      intros [H|H]; [exact (HX (or_introl H)) | cbn [outside] in Ho; lia].
    + pose proof (fp_not_outside1 _ _ _ Ho) as Ha'.
      assert (Hi : exists i : nat, a = f + Z.of_nat i /\ (i = 14 \/ i = 15 \/ 59 <= i < 64)%nat).
      { exists (Z.to_nat (a - f)). unfold trans_fp_wr in HX. split; [lia|]. lia. }
      destruct Hi as (i & -> & Hi).
      rewrite (fp_aview_of_bytes W m5 f _ i BB5) by
        (first [rewrite (cells_bytes_length _ Hwf5), CS5; lia | apply fp_f_vis; lia]).
      rewrite (fp_parse_unwritten buf b fj i ltac:(lia) Hlfj Hi).
      symmetry. apply fp_f_memc. lia.
  - exact (fp_pres_after [(f, f + 64)] m4 m5 HP4 MU5 WM5 HNO).
  - intros r Hr. unfold acallee_saved in Hr.
    assert (Hc' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    + rewrite G2, SQ. unfold FP_FRAME. replace (SP - 48 + 48) with SP by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    + rewrite G3. exact K3.
    + rewrite G4. exact K4.
    + exact G8.
    + exact G9.
    + exact G18.
    + exact G19.
    + exact G20.
    + rewrite G21. exact K21.
    + rewrite G22. exact K22.
    + rewrite G23. exact K23.
    + rewrite G24. exact K24.
    + rewrite G25. exact K25.
    + rewrite G26. exact K26.
    + rewrite G27. exact K27.
  - rewrite Hc. exact G10.
  - unfold trans_fp_f_bytes, trans_fp_f_cells. rewrite Hc. change (0 =? 0) with true. cbv iota.
    apply (fp_garr8_of_rw_cells W m5 f _ RW5). intros i Hi. rewrite CS5 in Hi. apply fp_f_vis. lia.
Qed.

(* ---- the two __asan_memcpy calls (f + j, buf + j, 6), j = 0 then j = 6 ---- *)
Lemma fp_memcpy_call : forall (j : Z) regsM m3 md3 (raw : Z),
  (j = 0 \/ j = 6) ->
  J m3 md3 -> fp_keep (fun a => fp_inwin a \/ f <= a < f + j) m3 -> fp_pres m3 -> fp_frame m3 ->
  fp_kregs regsM -> fr_code b = 0 ->
  GR regsM 1 = Z_to_bv 64 raw -> raw mod 2 = 0 -> 0 <= raw < 2 ^ 64 ->
  GR regsM 10 = w64 (f + j) -> GR regsM 11 = w64 (buf + j) -> GR regsM 12 = w64 6 ->
  (forall regs2 m4 md4, J m4 md4 -> fp_keep (fun a => fp_inwin a \/ f <= a < f + j + 6) m4 -> fp_pres m4 ->
     fp_frame m4 -> fp_kregs regs2 ->
     (forall i, 0 <= i < 6 -> aview segs (w_H W) m4 (f + j + i) = aview segs (w_H W) memc (buf + j + i)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (f + j <= a < f + j + 6) -> ~ fp_inwin a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) m3 a) ->
     SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 raw) m4 (YK11.seg_rom segs)) md4) POST) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsM (Z_to_bv 64 FP_MEMCPY) m3 (YK11.seg_rom segs)) md3) POST.
Proof.
  intros j regsM m3 md3 raw Hj J3 HK3 HP3 HF3 HR3 Hc G1 Hre Hrr G10 G11 G12 K.
  pose proof HR3 as (K2 & K3 & K4 & _).
  pose proof fp_sp as (H16 & Hs1 & Hs2). pose proof fp_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  pose proof (fr_code_ok b Hc) as (L30 & _).
  pose proof Hbw as BW. unfold decode_off_win, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in BW.
  pose proof (Hdisj ltac:(lia)) as HD. unfold TRANS_FP_F_SIZE in HD.
  assert (KX : forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ (fp_inwin a \/ f <= a < f + j)).
  { intros a Ha [H|H]; unfold fp_inwin, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *;
      unfold in_app, kLowMemEnd, kHighShadowEnd, kLowShadowBeg, kHighMemBeg in *; lia. }
  assert (SPM : spZ regsM = sp0 + (SP - 48 - sp0)).
  { change (spZ regsM) with (bv_unsigned (GR regsM 2)). rewrite K2. unfold w64. rewrite fp_u64 by lia. lia. }
  assert (O16 : (SP - 48 - sp0) mod 16 = 0).
  { pose proof (Z.div_mod SP 16 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite Hal in D1. rewrite H16 in D2.
    replace (SP - 48 - sp0) with ((SP / 16 - 3 - sp0 / 16) * 16) by lia. apply Z.mod_mul. lia. }
  assert (HBUF : forall a, buf + j <= a < buf + j + 6 -> aview segs (w_H W) m3 a = aview segs (w_H W) memc a).
  { intros a Ha. apply HK3; [lia|]. intros [H|H]; unfold fp_inwin, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in H; lia. }
  eapply SRr_bind.
  { apply (aj_intrin_at segs B LAWS fp_segs_low OCpy FP_MEMCPY (AMEMCPY fx) W regsM m3 STK sp0 FP ly S W0
             mem0 md0 own lyc Sc md3 k (f + j) (buf + j) 6 (SP - 48 - sp0) (Z_to_bv 64 raw) J3 G10 G11 G12).
    - lia.
    - lia.
    - lia.
    - exact SPM.
    - exact O16.
    - lia.
    - unfold ESTACK, TRANS_FP_STK, TRANS_FP_FRAME in *. lia.
    - exact (eq_trans K3 Hgp).
    - exact (eq_trans K4 Htp).
    - exact G1.
    - apply YK0s.ret_ok_even. rewrite fp_u64 by lia. exact Hre.
    - intros a Ha. split; [exact (proj1 (Htwr a ltac:(unfold TRANS_FP_F_SIZE; lia)))|].
      unfold ESTACK, TRANS_FP_STK, TRANS_FP_FRAME in *. lia.
    - destruct Hrd as (_ & _ & _ & AM & _). unfold amem_range, TRANS_FP_F_SIZE in *. lia.
    - exact (fp_ra_f _ m3 HK3 KX (f + j) 6 ltac:(lia) ltac:(lia) ltac:(lia)).
    - intros _. exact (fp_hull_f _ m3 HK3 KX (f + j) 6 ltac:(lia) ltac:(lia) ltac:(lia)).
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - rewrite (HBUF a Ha). replace a with (buf + Z.of_nat (Z.to_nat (a - buf))) by lia.
          rewrite fp_buf_memc by lia. discriminate.
        - rewrite SPM. unfold ESTACK, TRANS_FP_STK, TRANS_FP_FRAME in *. lia. }
      split; [lia|].
      split; [unfold amem_range in N5 |- *; lia|].
      split; [exact (fp_ra_buf _ m3 HK3 KX (buf + j) 6 ltac:(lia) ltac:(lia) ltac:(lia))|].
      intros _. exact (fp_hull_buf _ m3 HK3 KX (buf + j) 6 ltac:(lia) ltac:(lia) ltac:(lia)). }
  cbv beta. intros W2 c2 _ (-> & regs2 & m4 & md4 & -> & J4 & HP & HA0 & HCOPY & HV & HPR).
  apply K.
  - exact J4.
  - intros a Ha HX.
    assert (H1 : ~ (f + j <= a < f + j + 6)) by (intros H; apply HX; right; lia).
    assert (H2 : ~ (sp0 + (SP - 48 - sp0) - ESTACK <= a < sp0 + (SP - 48 - sp0))).
    { intros H; apply HX; left. unfold fp_inwin, ESTACK, TRANS_FP_STK, TRANS_FP_FRAME in *. lia. }
    rewrite (HV a Ha H1 H2). apply HK3; [exact Ha|]. intros [H|H]; apply HX; [left; exact H | right; lia].
  - intros a Ha Hp. exact (HPR a (HP3 a Ha Hp)).
  - apply (fp_frame_kept m3 m4 md3 md4 HF3 J3 J4). intros a Ha.
    apply HV; [lia | lia | unfold ESTACK, TRANS_FP_STK, TRANS_FP_FRAME in *; lia].
  - exact (fp_kregs_pres regsM regs2 HR3 HP).
  - intros i Hi. rewrite (HCOPY i Hi). apply HBUF. lia.
  - intros a Ha H1 H2. apply HV; [exact Ha | exact H1 |].
    intros H; apply H2. unfold fp_inwin, ESTACK, TRANS_FP_STK, TRANS_FP_FRAME in *. lia.
Qed.

(* ---- FP_RET1: fp_mid_F, then the second copy and FP_RET2 ---- *)
Lemma fp_at_ret1 : forall regs2 m2 md2,
  J m2 md2 -> fp_keep (fun a => fp_inwin a \/ f <= a < f + 6) m2 -> fp_pres m2 -> fp_frame m2 ->
  fp_kregs regs2 -> fr_code b = 0 ->
  (forall i, 0 <= i < 6 -> aview segs (w_H W) m2 (f + i) = aview segs (w_H W) memc (buf + i)) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 FP_RET1) m2 (YK11.seg_rom segs)) md2) POST.
Proof.
  intros regs2 m2 md2 J2 HK2 HP2 HF2 HR2 Hc HB6.
  pose proof HR2 as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  pose proof fp_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  change (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 FP_RET1) m2 (YK11.seg_rom segs)) md2)
    with (@cfg_at fx segs FP_RET1 regs2 m2 md2).
  eapply (fp_run W regs2 m2 md2 FP_RET1).
  { unfold LCK.ms_of_regs. apply fp_mid_F. }
  intros ms' md' (ms0 & -> & EQV) SBM.
  destruct (fp_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & G11 & G12 & G18 & G19 & G20 & G21 & G22 &
    G23 & G24 & G25 & G26 & G27).
  rewrite (fp_ms_shape _ _ _ _ EQV).
  pose proof FP_vals as (_ & _ & _ & ER2 & _).
  apply (fp_memcpy_call 6 (ms_regs ms') m2 md' FP_RET2).
  - right; reflexivity.
  - exact (fp_aj_md m2 md2 md' J2 SBM).
  - exact HK2.
  - exact HP2.
  - exact HF2.
  - unfold fp_kregs. rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27.
    repeat split; assumption.
  - exact Hc.
  - exact G1.
  - rewrite ER2. reflexivity.
  - rewrite ER2. lia.
  - rewrite G10, K8. unfold w64. rewrite fp_u64 by lia. reflexivity.
  - rewrite G11, K9. unfold w64. rewrite fp_u64 by lia. reflexivity.
  - exact G12.
  - intros regs3 m4 md4 J4 HK4 HP4 HF4 HR4 HB HOUT.
    change (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 FP_RET2) m4 (YK11.seg_rom segs)) md4)
      with (@cfg_at fx segs FP_RET2 regs3 m4 md4).
    apply (fp_at_ret2 regs3 m4 md4 J4).
    + replace (f + 6 + 6) with (f + 12) in HK4 by lia. exact HK4.
    + exact HP4.
    + exact HF4.
    + exact HR4.
    + exact Hc.
    + intros i Hi. destruct (Z_lt_le_dec i 6) as [Hi6|Hi6].
      * rewrite (HOUT (f + i)); [exact (HB6 i ltac:(lia)) | lia | lia |].
        unfold fp_inwin, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK. pose proof fp_sp. lia.
      * replace (f + i) with (f + 6 + (i - 6)) by lia. replace (buf + i) with (buf + 6 + (i - 6)) by lia.
        exact (HB (i - 6) ltac:(lia)).
Qed.

(* ---- the entry: fp_head_stmt, then the return or the first copy ---- *)
Lemma fp_entry : SRr segs W (@cfg_at fx segs FP_ENTRY regs memc mdc) POST.
Proof.
  pose proof fp_sp as (H16 & Hs1 & Hs2). pose proof fp_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  pose proof Hbw as BW. unfold decode_off_win, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in BW.
  pose proof (fp_win_pres memc mdc HJ) as Hpres0.
  destruct (fp_cells2 B HCELLS lyc Sc W memc mdc fp_HAR0) as [GCK CK].
  assert (E10 : GR regs 10 = Z_to_bv 64 buf) by exact H10.
  assert (E11 : GR regs 11 = Z_to_bv 64 LEN) by exact H11.
  assert (E12 : GR regs 12 = Z_to_bv 64 f) by exact H12.
  eapply (fp_run W regs memc mdc FP_ENTRY).
  { unfold LCK.ms_of_regs. rewrite E10, E11, E12.
    eapply HEAD with (lo := SP - TRANS_FP_STK).
    all: try change (bv_unsigned (GR regs 2)) with SP.
    - lia.
    - lia.
    - lia.
    - apply (fp_bytes_at_of_aview W memc buf b); [lia | lia | exact fp_buf_memc].
    - apply (fp_stk_present (w_H W)); [lia | lia | exact Hpres0].
    - unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK, FP_FRAME. lia.
    - unfold AsanKA.off_stk, FP_FRAME. change (bv_unsigned (GR regs 2)) with SP.
      unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *. lia.
    - unfold AC.app_mem, AC.HIGHMEM_BEG, AC.APPMEM_END, AC.LOWMEM_END, FP_FRAME. right.
      unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *. lia.
    - unfold AC.app_mem, AC.HIGHMEM_BEG, AC.APPMEM_END, AC.LOWMEM_END. right.
      unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *. lia.
    - exact GCK.
    - exact CK.
    - unfold AsanKA.off_stk, AC.GOT_CELL_K, FP_FRAME. left. change (bv_unsigned (GR regs 2)) with SP.
      unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *. lia.
    - unfold AsanKA.off_stk, AC.CELL_K, FP_FRAME. left. change (bv_unsigned (GR regs 2)) with SP.
      unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *. lia.
    - destruct (FF.decode_addressable_of (w_H W) memc buf LEN fp_ra_buf0 N5 ltac:(lia) ltac:(lia)) as [HA _].
      exact HA.
    - unfold FP_FRAME. exact fp_rng_frame.
    - apply fp_rng; [unfold AC.GOT_CELL_K; lia | unfold AC.GOT_CELL_K; lia |]. intros a Ha.
      replace a with (AC.GOT_CELL_K + (a - AC.GOT_CELL_K)) by lia.
      apply (fp_covers_visible (w_H W) AC.GOT_CELL_K 8 (a - AC.GOT_CELL_K) (w_Hoff W));
        [vm_compute; reflexivity | lia | unfold AC.GOT_CELL_K; lia].
    - apply fp_rng; [unfold AC.CELL_K; lia | unfold AC.CELL_K; lia |]. intros a Ha.
      replace a with (AC.CELL_K + (a - AC.CELL_K)) by lia.
      apply (fp_covers_visible (w_H W) AC.CELL_K 8 (a - AC.CELL_K) (w_Hoff W));
        [vm_compute; reflexivity | lia | unfold AC.CELL_K; lia].
    - exact fp_rng_buf.
    - exact fp_shrng_buf. }
  intros ms' md' (ms0 & (m1 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & MU & WM & HOR) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with SP in MU. unfold FP_FRAME in MU.
  assert (HNO : forall z, ~ outside [(SP - 48, SP)] z -> ~ in_img segs z).
  { intros z Hz Hi. pose proof (fp_not_outside1 _ _ _ Hz). pose proof (fp_segs_low z Hi).
    unfold kLowMemEnd, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *. lia. }
  assert (J1 : J m1 md').
  { apply (fp_aj_run [(SP - 48, SP)] memc m1 mdc md' HJ MU WM SBM).
    intros a Ha. pose proof (fp_not_outside1 _ _ _ Ha) as Ha'.
    split; [lia|]. split; [apply Hpres0; unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK; lia|].
    split; [exact (HNO a Ha)|]. left. unfold TRANS_FP_STK, TRANS_FP_FRAME, ESTACK in *. lia. }
  assert (KEEP1 : fp_keep fp_inwin m1).
  { apply (fp_keep_run fp_inwin [(SP - 48, SP)] memc m1 (fp_keep0 _) MU).
    intros a Ha. pose proof (fp_not_outside1 _ _ _ Ha). unfold fp_inwin, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK. lia. }
  pose proof (fp_pres_after [(SP - 48, SP)] memc m1 fp_pres0 MU WM HNO) as PRES1.
  destruct HOR as [(Hc & ->) | (Hc & FR & ->)];
    destruct (fp_regs_of EQV) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & G11 & G12 & G18 & G19 & G20 & G21 & G22 &
      G23 & G24 & G25 & G26 & G27).
  - (* a code that is not 0: the return, f untouched *)
    assert (Hret : ret_pc (GR regs 1) = GR regs 1) by (apply LeafCgFacts.ret_ok_stmt_YK0s; exact Hra).
    rewrite Hret in EQV. rewrite (fp_ms_shape _ _ _ _ EQV).
    apply fp_at_ret.
    + exact J1.
    + apply (fp_keep_mono _ _ m1 KEEP1). intros a H. left. exact H.
    + exact PRES1.
    + intros r Hr. unfold acallee_saved in Hr.
      assert (Hc' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hc' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
        assumption.
    + exact G10.
    + unfold trans_fp_f_bytes, trans_fp_f_cells. rewrite (proj2 (Z.eqb_neq _ _) Hc). cbv iota.
      cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply fp_garr8_of_aview. intros jj Hjj. rewrite length_map in Hjj.
      rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hjj).
      rewrite map_nth.
      rewrite (KEEP1 (f + Z.of_nat jj)) by (lia || (unfold fp_inwin, TRANS_FP_STK, TRANS_FP_FRAME, ESTACK; lia)).
      split; [apply fp_f_memc; lia|]. apply bv_unsigned_in_range.
  - (* code 0: __asan_memcpy (f, buf, 6) *)
    rewrite (fp_ms_shape _ _ _ _ EQV).
    pose proof FP_vals as (_ & _ & ER1 & _).
    apply (fp_memcpy_call 0 (ms_regs ms') m1 md' FP_RET1).
    + left; reflexivity.
    + exact J1.
    + apply (fp_keep_mono _ _ m1 KEEP1). intros a H. left. exact H.
    + exact PRES1.
    + exact FR.
    + unfold fp_kregs. rewrite G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27.
      repeat split; reflexivity.
    + exact Hc.
    + exact G1.
    + rewrite ER1. reflexivity.
    + rewrite ER1. lia.
    + rewrite Z.add_0_r. exact G10.
    + rewrite Z.add_0_r. exact G11.
    + exact G12.
    + intros regs2 m2 md2 J2 HK2 HP2 HF2 HR2 HB HOUT.
      apply (fp_at_ret1 regs2 m2 md2 J2).
      * replace (f + 0 + 6) with (f + 6) in HK2 by lia. exact HK2.
      * exact HP2.
      * exact HF2.
      * exact HR2.
      * exact Hc.
      * intros i Hi. pose proof (HB i Hi) as E. rewrite !Z.add_0_r in E. exact E.
Qed.

End Entry.

Theorem fp_walk : @transport_diginet_frame_parse_cg fx rc B MT (transport_sigma TS_diginet_frame_parse).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf f b fj.
  intros HJ Hra Hra4 Hgp Htp H10 H11 H12 Hal Hwlo Hwhi Hbuf0 Hf0 Hsrc Hbw Hgb Hlfj Hgf Hfake Htwr Hrd Hwin Hdisj
    Hnev.
  eapply fp_entry; eassumption.
Qed.
End Walk.

(* The frozen statement: fp_walk at the four footprint runs, proved in lib/A/Prog/diginet_frame_parse_seg_head.v,
   _seg_hdr1.v, _seg_hdr2.v and _seg_tail.v. *)
Theorem transport_diginet_frame_parse_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_diginet_frame_parse_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT HCELLS LAWS MTL AMEMCPY.
  exact (@fp_walk fx rc B MT HCELLS LAWS MTL AMEMCPY
           diginet_frame_parse_seg_head.fp_head_holds diginet_frame_parse_seg_hdr1.fp_hdr1_holds
           diginet_frame_parse_seg_hdr2.fp_hdr2_holds diginet_frame_parse_seg_tail.fp_tail_holds).
Qed.
