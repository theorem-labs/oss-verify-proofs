(* diginet_msg_next_walk_lib: the caller-journal walk of diginet_msg_next (fuzz_decode.asan 0x820e8) from its two
   footprint pieces (lib/A/Prog/diginet_msg_next_segs.v mn_entry_F, mn_body_F), at the premise list of the frozen
   statement lib/A/Prog/diginet_msg_next_cg.v decode_diginet_msg_next_cg.

   The walk:
     1. mn_entry_F runs from the entry under the caller's footprint (every visible byte), carried into SRr by
        lib/A/Prog/DecodeFevt.v decode_run; its premises are the statement's premises read as the run's memory facts
        (the cursor and message bytes from their garr8 and their write right, the body from trans_src_ok (decode_rd_ok
        in every case, trans_src_ok_rd) and decode_off_win, the shadow bytes from decode_rd_ok, the frame from the
        journal's stack window);
     2. pos >= len: the run returns; mw_close builds the post;
     3. else the run stops at the __asan_memset call: the caller's journal follows the run (YCbq.v ajournal_exec,
        the written bytes in the journal's stack window or in [c, c + 25), [mp, mp + 40) by decode_twr_ok), the call
        is the statement's aintrin_realizes (YCbq.v aj_intrin_at, [mp + 8, mp + 24) := 0), and mn_body_F runs
        from its return with the bytes carried across the call (aview kept outside the call's range and window,
        so the raw bytes of present bytes); mw_close builds the post.
   mw_close: the journal follows the last run; acall_kept holds because every byte outside the call's window and
   outside [c, c + 25), [mp, mp + 40) keeps its view, and the bytes of those two ranges outside the written range
   (the cursor's body and len, the message's padding) are the same bytes before and after. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YK1b YP09 YA0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame Cells Step ExecF PropExec Regs6ss MState.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_msg_next_segs TransportFevt LeafCgKit LeafCgFacts AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_cursor_init_c diginet_msg_next_c.
Import ListNotations.
Open Scope Z_scope.
Module MNS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_segs.
Module FF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportFevt.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module LM := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LCe := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module LSt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Step.
Module LFr := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Frame.
Module AI0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Img0.
Module FC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module PCu := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_cursor_init_c.
Module PMs := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_msg_next_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- bytes of the cursor and the message ---- *)

(* The first 16 bytes of the cursor (body, len) do not depend on pos and status. *)
Lemma mw_cur_prefix : forall body L p s p' s' j, (j < 16)%nat ->
  nth_error (LCe.cells_bytes (PCu.cursor_cells body L p s)) j =
  nth_error (LCe.cells_bytes (PCu.cursor_cells body L p' s')) j.
Proof.
  intros body L p s p' s' j Hj.
  assert (E : forall p0 s0, LCe.cells_bytes (PCu.cursor_cells body L p0 s0) =
    (LM.le8 (Z_to_bv 64 body) ++ LM.le8 (Z_to_bv 64 L)) ++ (LM.le8 (Z_to_bv 64 (Z.of_nat p0)) ++ [b8 s0])).
  { intros p0 s0. unfold PCu.cursor_cells. cbn [LCe.cells_bytes LCe.cbytes]. rewrite <- !app_assoc. reflexivity. }
  assert (Hl : (j < length (LM.le8 (Z_to_bv 64 body) ++ LM.le8 (Z_to_bv 64 L)))%nat)
    by (rewrite length_app, !LM.length_le8; lia).
  rewrite !E, !(nth_error_app1 _ _ Hl). reflexivity.
Qed.

(* The message's padding (bytes 4 .. 7) is the old bytes after every step. *)
Lemma mw_msg_pad : forall body mj r j, length mj = 40%nat -> (4 <= j < 8)%nat ->
  nth_error (LCe.cells_bytes (PMs.msg_cells body mj r)) j = nth_error mj j.
Proof.
  intros body mj r j Hl Hj. unfold PMs.msg_cells.
  destruct (is_end r).
  - cbn [LCe.cells_bytes LCe.cbytes]. rewrite app_nil_r. reflexivity.
  - cbn [LCe.cells_bytes LCe.cbytes app].
    destruct j as [|[|[|[|j]]]]; try lia. cbn [nth_error].
    rewrite nth_error_app1 by (rewrite length_firstn, length_skipn; lia).
    rewrite nth_error_firstn. replace (j <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_error_skipn. reflexivity.
Qed.


Lemma mw_msg_len : forall body mj r, length mj = 40%nat ->
  length (LCe.cells_bytes (PMs.msg_cells body mj r)) = 40%nat.
Proof.
  intros body mj r H. unfold PMs.msg_cells. destruct (is_end r).
  - cbn [LCe.cells_bytes LCe.cbytes]. rewrite app_nil_r. exact H.
  - destruct (writes_len (mr_kind r)); cbn [LCe.cells_bytes LCe.cbytes];
      rewrite !length_app, length_firstn, !length_skipn, !LM.length_le8; cbn [length]; lia.
Qed.

(* Every shadow byte of [q, q + n) is the shadow byte of a byte of the range. *)
Lemma mw_shadow_cover : forall q n i, 0 <= q -> 0 < n ->
  0 <= i < FC.shadow_addr (q + n - 1) - FC.shadow_addr q + 1 ->
  exists j, 0 <= j < n /\ FC.shadow_addr (q + j) = FC.shadow_addr q + i.
Proof.
  intros q n i Hq Hn Hi. unfold FC.shadow_addr in *.
  pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Mq.
  pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia)) as Mn.
  set (a := q / 8) in *. set (b := (q + n - 1) / 8) in *. set (r := q mod 8) in *. set (r' := (q + n - 1) mod 8) in *.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - exists 0. split; [lia|]. rewrite !Z.add_0_r. reflexivity.
  - exists (8 * (a + i) - q). split; [lia|].
    replace (q + (8 * (a + i) - q)) with ((a + i) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma mw_shadow_rng_vis : forall (W : world tfibsegs) q n, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 ->
  (forall j, 0 <= j < n -> w_H W (Z_to_bv 64 (FC.shadow_addr (q + j))) = false) ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (FC.shadow_addr q)
    (FC.shadow_addr (q + n - 1) - FC.shadow_addr q + 1).
Proof.
  intros W q n Hq Hn Hn47 Hv. apply FF.decode_rng_vis.
  - unfold FC.shadow_addr, FC.ASAN_K. Z.div_mod_to_equations. lia.
  - unfold FC.shadow_addr, FC.ASAN_K. Z.div_mod_to_equations. lia.
  - intros i Hi. destruct (mw_shadow_cover q n i Hq Hn Hi) as (j & Hj & Ej). rewrite <- Ej. exact (Hv j Hj).
Qed.

(* A byte of the memory above the image (where the image holds no byte) read through mrd is the memory's byte. *)
Lemma mw_mrd_high : forall (m : word -> option byte) a b, kLowMemEnd <= a < 2 ^ 64 ->
  LM.mrd AI0.rsegs m (LM.wa a) = Some b -> m (LM.wa a) = Some b.
Proof.
  intros m a b Ha H. unfold LM.mrd in H. destruct (m (LM.wa a)) as [b'|] eqn:E; [exact H|].
  rewrite FF.decode_seg_rom_high in H; [discriminate H|]. unfold LM.wa.
  rewrite MState.unsigned_lit by (unfold kLowMemEnd in Ha; lia). exact (proj1 Ha).
Qed.

(* A byte the view reads is not hidden: a hidden byte reads nothing, not even the image (w_Hoff, YA0o.v
   seg_rom_hidden). *)
Lemma mw_vis_of_aview : forall (W : world tfibsegs) (m : word -> option byte) a,
  aview tfibsegs (w_H W) m a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m a Hv. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply Hv. unfold aview, YP09.mbyte, mrestrict. rewrite E. cbv beta iota.
  rewrite (YA0o.seg_rom_hidden tfibsegs (w_H W) (Z_to_bv 64 a) (w_Hoff W) E). reflexivity.
Qed.

(* Two memories with the same view at a have the same byte there under the same hidden set. *)
Lemma mw_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a ->
  YP09.mbyte tfibsegs (mrestrict H m') a = YP09.mbyte tfibsegs (mrestrict H m) a.
Proof.
  intros H m m' a E. unfold aview in E. cbv beta in E.
  destruct (YP09.mbyte tfibsegs (mrestrict H m') a) as [x|], (YP09.mbyte tfibsegs (mrestrict H m) a) as [y|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation SK := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMSET : forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset).
Hypothesis HENT : MNS.mn_entry_F.
Hypothesis HBODY : MNS.mn_body_F.
Local Abbreviation ajournalA := (@ajournal rc SK segs B).

Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z).
Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hret : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 c.
Hypothesis H11 : YK11.getr regs 11 = w64 mp.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - TRANS_MN_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hc0 : c <> 0.
Hypothesis Hm0 : mp <> 0.
Hypothesis Hpos : (pos <= length bb)%nat.
Hypothesis Hst : st_ok st.
Hypothesis Gc : garr8 segs (mrestrict (w_H W) memc) c (trans_mn_cur_bytes body (Z.of_nat (length bb)) pos st).
Hypothesis Hmj : length mj = 40%nat.
Hypothesis Gm : garr8 segs (mrestrict (w_H W) memc) mp (map bz mj).
Hypothesis Gb : garr8 segs (mrestrict (w_H W) memc) body (map bz bb).
Hypothesis Hblk : (0 < length bb)%nat -> trans_src_ok B lyc Sc W memc body (Z.of_nat (length bb)).
Hypothesis Hob : (0 < length bb)%nat -> decode_off_win regs TRANS_MN_STK body (Z.of_nat (length bb)).
Hypothesis Hfc : decode_in_fake lyc Sc c TRANS_MN_CUR_SIZE.
Hypothesis Hfm : decode_in_fake lyc Sc mp TRANS_MN_MSG_SIZE.
Hypothesis Htc : decode_twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) c TRANS_MN_CUR_SIZE.
Hypothesis Htm : decode_twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) mp TRANS_MN_MSG_SIZE.
Hypothesis Hrc : decode_rd_ok W memc c TRANS_MN_CUR_SIZE.
Hypothesis Hrm : decode_rd_ok W memc mp TRANS_MN_MSG_SIZE.
Hypothesis Hoc : decode_off_win regs TRANS_MN_STK c TRANS_MN_CUR_SIZE.
Hypothesis Hom : decode_off_win regs TRANS_MN_STK mp TRANS_MN_MSG_SIZE.
Hypothesis Hcm : c + TRANS_MN_CUR_SIZE <= mp \/ mp + TRANS_MN_MSG_SIZE <= c.
Hypothesis Hcb : (0 < length bb)%nat -> c + TRANS_MN_CUR_SIZE <= body \/ body + Z.of_nat (length bb) <= c.
Hypothesis Hmb : (0 < length bb)%nat -> mp + TRANS_MN_MSG_SIZE <= body \/ body + Z.of_nat (length bb) <= mp.

Local Abbreviation L := (Z.of_nat (length bb)).
Local Abbreviation sp := (spZ regs).
Local Abbreviation POST := (trans_mn_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs c mp body bb mj pos st).
Local Abbreviation RNG := (LCK.RNG_W (world segs) (@w_H segs) W).
Local Abbreviation gr r := (YK11.getr regs (Z_to_bv 5 r)).

(* ---- facts of the premises ---- *)

Lemma mw_AR : AR segs B lyc Sc W memc mdc.
Proof. exact (proj1 HJ). Qed.

Lemma mw_win : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a.
Proof.
  intros a Ha. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact (Hp a Ha).
Qed.

Lemma mw_consts : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. exact (proj1 asan_consts). Qed.

Lemma mw_sp : alloc_ceiling + TRANS_MN_STK <= sp /\ sp <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ sp0 <= 2 ^ 47.
Proof.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (H16 & H0 & Hceil & Hlo & Hhi & H47 & _).
  lia.
Qed.

Lemma mw_sp_bounds : 0x7fff7f800000 + 128 + 4096 <= sp /\ sp <= 2 ^ 47.
Proof. pose proof mw_consts. pose proof mw_sp as (H1 & H2 & _). unfold TRANS_MN_STK, TRANS_MN_FRAME, ESTACK in H1. lia. Qed.

(* the frame [sp - 128, sp) is in the journal's stack window *)
Lemma mw_frame_win : forall a, sp - 128 <= a < sp -> apresent (w_H W) memc a.
Proof. intros a Ha. apply mw_win. unfold TRANS_MN_STK, TRANS_MN_FRAME, ESTACK in Hwlo. lia. Qed.

Lemma mw_twr : forall q n, decode_twr_ok B STK sp0 FP ly S lyc Sc own W memc sp q n ->
  forall a, q <= a < q + n ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a.
Proof. intros q n H a Ha. destruct (H a Ha) as (H1 & H2 & _). split; assumption. Qed.

Lemma mw_fake : forall q n, decode_in_fake lyc Sc q n -> 0 <= n ->
  4096 <= q /\ q + n <= alloc_ceiling /\ (forall a, q <= a < q + n -> ~ in_img segs a).
Proof.
  intros q n (cid & p & Hin & H1 & H2) Hn.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid p mw_AR Hin) as (B1 & B2 & _).
  split; [lia|]. split; [lia|].
  intros a Ha.
  refine (proj2 (al_client_img segs B LAWS lyc Sc W memc mdc a mw_AR (or_intror (or_introl _)))).
  exists cid, p. split; [exact Hin | lia].
Qed.

Lemma mw_rd : forall q n, decode_rd_ok W memc q n -> 0 < n ->
  0 <= q /\ q + n <= 2 ^ 63 /\ amem_range q n /\ FC.addressable memc q n /\
  (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (FC.shadow_addr (q + i))) = false) /\
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF q n /\ shadow_hull_vis (aview segs (w_H W) memc) q n.
Proof.
  intros q n (Hv & Hra & Hhull & Ham & H0 & H63) Hn.
  destruct (FF.decode_addressable_of (w_H W) memc q n Hra Ham H0 ltac:(lia)) as [HA HS].
  split; [exact H0|]. split; [exact H63|]. split; [exact Ham|]. split; [exact HA|]. split; [exact HS|].
  split; [exact Hra | exact Hhull].
Qed.

(* c and mp: below the allocator's ceiling, outside the image, present, visible *)
Lemma mw_c : 4096 <= c /\ c + 25 <= alloc_ceiling /\ c + 25 <= 2 ^ 63 /\ amem_range c 25 /\
  FC.addressable memc c 25 /\ (forall i, 0 <= i < 25 -> w_H W (Z_to_bv 64 (FC.shadow_addr (c + i))) = false) /\
  (forall a, c <= a < c + 25 -> ~ in_img segs a) /\
  (forall a, c <= a < c + 25 -> apresent (w_H W) memc a).
Proof.
  destruct (mw_fake c 25 Hfc ltac:(lia)) as (F1 & F2 & F3).
  destruct (mw_rd c 25 Hrc ltac:(lia)) as (_ & R2 & R3 & R4 & R5 & _).
  split; [exact F1|]. split; [exact F2|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [exact R5|]. split; [exact F3|].
  intros a Ha. exact (proj2 (mw_twr c 25 Htc a Ha)).
Qed.

Lemma mw_m : 4096 <= mp /\ mp + 40 <= alloc_ceiling /\ mp + 40 <= 2 ^ 63 /\ amem_range mp 40 /\
  FC.addressable memc mp 40 /\ (forall i, 0 <= i < 40 -> w_H W (Z_to_bv 64 (FC.shadow_addr (mp + i))) = false) /\
  (forall a, mp <= a < mp + 40 -> ~ in_img segs a) /\
  (forall a, mp <= a < mp + 40 -> apresent (w_H W) memc a) /\
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF mp 40 /\ shadow_hull_vis (aview segs (w_H W) memc) mp 40.
Proof.
  destruct (mw_fake mp 40 Hfm ltac:(lia)) as (F1 & F2 & F3).
  destruct (mw_rd mp 40 Hrm ltac:(lia)) as (_ & R2 & R3 & R4 & R5 & R6 & R7).
  split; [exact F1|]. split; [exact F2|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [exact R5|]. split; [exact F3|].
  split; [intros a Ha; exact (proj2 (mw_twr mp 40 Htm a Ha))|].
  split; [exact R6 | exact R7].
Qed.

(* the body when it is not empty: placed by trans_src_ok (trans_src_ok_place: in [4096, alloc_ceiling) or in the
   machine stack below 2 ^ 47), its bytes visible and marked usable (trans_src_ok_rd), outside this call's window
   (decode_off_win) *)
Lemma mw_blk : (0 < length bb)%nat ->
  4096 <= body /\ body + L <= 2 ^ 47 /\ amem_range body L /\
  (forall a, body <= a < body + L -> w_H W (Z_to_bv 64 a) = false) /\
  (body + L <= sp - 128 - 4096 \/ sp <= body) /\
  FC.addressable memc body L /\ (forall i, 0 <= i < L -> w_H W (Z_to_bv 64 (FC.shadow_addr (body + i))) = false).
Proof.
  intros HL. assert (HL' : 0 < L) by lia.
  pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc body L mw_AR (Hblk HL) HL') as Hrd.
  pose proof (trans_src_ok_place B LAWS lyc Sc W memc mdc body L mw_AR (Hblk HL) HL') as Hpl.
  pose proof mw_consts as C.
  destruct (mw_rd body L Hrd HL') as (R1 & R2 & R3 & R4 & R5 & _).
  pose proof (Hob HL) as Ho. unfold decode_off_win, TRANS_MN_STK, TRANS_MN_FRAME, ESTACK in Ho.
  split; [destruct Hpl as [Hp | Hp]; lia|].
  split; [destruct Hpl as [Hp | Hp]; lia|].
  split; [exact R3|].
  split; [intros a Ha; exact (mw_vis_of_aview W memc a (proj1 Hrd a Ha))|].
  split; [lia|].
  split; [exact R4 | exact R5].
Qed.

(* ---- the memory facts the footprint pieces read, at the entry memory ---- *)

Lemma mw_cur_rw : LSt.rw_cells AI0.rsegs memc c (PCu.cursor_cells body L pos st).
Proof.
  pose proof mw_c as (C1 & C2 & C3 & _ & _ & _ & _ & C8).
  apply (FF.decode_rw_of_garr8 (w_H W) memc c); [cbn; tauto | lia | cbn; lia | | exact Gc].
  intros i Hi. apply C8. cbn in Hi. lia.
Qed.

Lemma mw_msg_rw : LSt.rw_cells AI0.rsegs memc mp [LCe.CB 40 mj].
Proof.
  pose proof mw_m as (M1 & M2 & M3 & _ & _ & _ & _ & M8 & _).
  apply (FF.decode_rw_of_garr8 (w_H W) memc mp); [cbn; tauto | lia | cbn; lia | |].
  - intros i Hi. apply M8. cbn in Hi. lia.
  - cbn [LCe.cells_bytes LCe.cbytes]. rewrite app_nil_r. exact Gm.
Qed.

Lemma mw_msg_bytes : LM.bytes_at AI0.rsegs memc mp mj.
Proof.
  pose proof mw_m as (M1 & M2 & M3 & _ & _ & _ & _ & M8 & _).
  apply (FF.decode_garr8_bytes (w_H W) memc mp mj); [lia | rewrite Hmj; lia | | exact Gm].
  intros j Hj. rewrite Hmj in Hj. exact (proj1 (M8 (mp + Z.of_nat j) ltac:(lia))).
Qed.

Lemma mw_body_bytes : (0 < length bb)%nat -> LM.bytes_at AI0.rsegs memc body bb.
Proof.
  intros HL. pose proof (mw_blk HL) as (B1 & B2 & _ & B4 & _).
  apply (FF.decode_garr8_bytes (w_H W) memc body bb); [lia | lia | | exact Gb].
  intros j Hj. exact (B4 (body + Z.of_nat j) ltac:(lia)).
Qed.

(* ---- the footprint ranges ---- *)

Lemma mw_vis : forall a, apresent (w_H W) memc a -> w_H W (Z_to_bv 64 a) = false.
Proof. intros a [H _]. exact H. Qed.

Lemma mw_rng_frame : ExecF.rng RNG (sp - 128) 128.
Proof.
  pose proof mw_sp_bounds. apply FF.decode_rng_vis; [lia | lia |].
  intros i Hi. apply mw_vis, mw_frame_win. lia.
Qed.

Lemma mw_rng_cell : forall a n, In (a, n) decode_asan_cell_ranges -> 0 <= a -> a + n <= 2 ^ 64 -> ExecF.rng RNG a n.
Proof.
  intros a n Hin H0 H1. apply FF.decode_rng_vis; [exact H0 | exact H1 |].
  intros i Hi. exact (FF.decode_cell_visible W a n i Hin Hi).
Qed.

Lemma mw_rng_c : ExecF.rng RNG c 25.
Proof.
  pose proof mw_c as (C1 & C2 & C3 & _ & _ & _ & _ & C8).
  apply FF.decode_rng_vis; [lia | lia |]. intros i Hi. apply mw_vis, C8. lia.
Qed.

Lemma mw_rng_m : ExecF.rng RNG mp 40.
Proof.
  pose proof mw_m as (M1 & M2 & M3 & _ & _ & _ & _ & M8 & _).
  apply FF.decode_rng_vis; [lia | lia |]. intros i Hi. apply mw_vis, M8. lia.
Qed.

Lemma mw_rng_shc : ExecF.rng RNG (FC.shadow_addr c) (FC.shadow_addr (c + 25 - 1) - FC.shadow_addr c + 1).
Proof.
  pose proof mw_c as (C1 & C2 & C3 & _ & _ & C6 & _). pose proof mw_consts.
  apply mw_shadow_rng_vis; [lia | lia | lia | exact C6].
Qed.

Lemma mw_rng_shm : ExecF.rng RNG (FC.shadow_addr mp) (FC.shadow_addr (mp + 40 - 1) - FC.shadow_addr mp + 1).
Proof.
  pose proof mw_m as (M1 & M2 & M3 & _ & _ & M6 & _). pose proof mw_consts.
  apply mw_shadow_rng_vis; [lia | lia | lia | exact M6].
Qed.

Lemma mw_rng_body : (0 < length bb)%nat ->
  ExecF.rng RNG body L /\
  ExecF.rng RNG (FC.shadow_addr body) (FC.shadow_addr (body + L - 1) - FC.shadow_addr body + 1).
Proof.
  intros HL. pose proof (mw_blk HL) as (B1 & B2 & _ & B4 & _ & _ & B7).
  split.
  - apply FF.decode_rng_vis; [lia | lia |]. intros i Hi. apply B4. lia.
  - apply mw_shadow_rng_vis; [lia | lia | lia | exact B7].
Qed.

Lemma mw_off_c : AsanKA.off_stk (gr 2) MNS.MN_FRAME c 25.
Proof.
  unfold AsanKA.off_stk, MNS.MN_FRAME. change (bv_unsigned (gr 2)) with sp.
  unfold decode_off_win, TRANS_MN_STK, TRANS_MN_FRAME, TRANS_MN_CUR_SIZE, ESTACK in Hoc. lia.
Qed.

Lemma mw_off_m : AsanKA.off_stk (gr 2) MNS.MN_FRAME mp 40.
Proof.
  unfold AsanKA.off_stk, MNS.MN_FRAME. change (bv_unsigned (gr 2)) with sp.
  unfold decode_off_win, TRANS_MN_STK, TRANS_MN_FRAME, TRANS_MN_MSG_SIZE, ESTACK in Hom. lia.
Qed.

Lemma mw_off_body : (0 < length bb)%nat -> AsanKA.off_stk (gr 2) MNS.MN_FRAME body L.
Proof.
  intros HL. pose proof (mw_blk HL) as (B1 & B2 & _ & _ & B5 & _).
  unfold AsanKA.off_stk, MNS.MN_FRAME. change (bv_unsigned (gr 2)) with sp. lia.
Qed.

(* ---- the entry piece ---- *)

Lemma mw_entry_run :
  ExecF.evtF AI0.rsegs RNG
    (fun ms' =>
       MNS.mn_post (gr 1) (gr 2) (gr 3) (gr 4) (gr 8) (gr 9) (gr 18) (gr 19) (gr 20) (gr 21) (gr 22) (gr 23)
         (gr 24) (gr 25) (gr 26) (gr 27) (@fp_regs fx) (@fp_csr fx) memc c mp body bb mj pos st ms' \/
       ((pos < length bb)%nat /\
        MNS.mn_call (gr 1) (gr 2) (gr 3) (gr 4) (gr 8) (gr 9) (gr 18) (gr 19) (gr 20) (gr 21) (gr 22) (gr 23)
          (gr 24) (gr 25) (gr 26) (gr 27) (@fp_regs fx) (@fp_csr fx) memc c mp body bb mj pos ms'))
    (@LCK.ms_of_regs fx (transport_sigma TS_diginet_msg_next) regs memc).
Proof.
  pose proof mw_sp as (S1 & S2 & S3 & S4). pose proof mw_sp_bounds as (SB1 & SB2). pose proof mw_consts as CC.
  pose proof mw_c as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof mw_m as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  pose proof HENT as HE. unfold MNS.mn_entry_F in HE.
  unfold LCK.ms_of_regs.
  eapply HE with (lo := sp - TRANS_MN_STK).
  - exact H10.
  - exact H11.
  - exact Hc0.
  - exact Hm0.
  - exact Hpos.
  - exact Hst.
  - exact Hmj.
  - change (bv_unsigned (gr 2)) with sp.
    apply (FF.decode_stk_present (w_H W)); [lia | lia |].
    intros a Ha. apply mw_win. lia.
  - change (bv_unsigned (gr 2)) with sp. unfold MNS.MN_FRAME, TRANS_MN_STK, TRANS_MN_FRAME, ESTACK. lia.
  - change (bv_unsigned (gr 2)) with sp. unfold FC.app_mem, FC.HIGHMEM_BEG, FC.APPMEM_END, MNS.MN_FRAME. lia.
  - change (bv_unsigned (gr 2)) with sp. unfold FC.app_mem, FC.HIGHMEM_BEG, FC.APPMEM_END. lia.
  - exact (FF.decode_cells_asan B HCELLS lyc Sc W memc mdc mw_AR).
  - unfold AsanKA.off_stk, MNS.MN_FRAME, FC.GOT_CELL_K. change (bv_unsigned (gr 2)) with sp. lia.
  - unfold AsanKA.off_stk, MNS.MN_FRAME, FC.CELL_K. change (bv_unsigned (gr 2)) with sp. lia.
  - exact mw_cur_rw.
  - exact mw_msg_rw.
  - exact C5.
  - exact M5.
  - exact mw_off_c.
  - exact mw_off_m.
  - unfold TRANS_MN_CUR_SIZE, TRANS_MN_MSG_SIZE in Hcm. exact Hcm.
  - intros Hlt. assert (HL : (0 < length bb)%nat) by lia.
    pose proof (mw_blk HL) as (_ & _ & _ & _ & _ & B6 & _).
    split; [exact (mw_body_bytes HL)|]. split; [exact B6|]. split; [exact (mw_off_body HL)|].
    pose proof (Hcb HL) as X1. pose proof (Hmb HL) as X2.
    unfold TRANS_MN_CUR_SIZE, TRANS_MN_MSG_SIZE in X1, X2. split; [exact X1 | exact X2].
  - change (bv_unsigned (gr 2)) with sp. exact mw_rng_frame.
  - apply mw_rng_cell; [cbn; tauto | unfold FC.GOT_CELL_K; lia | unfold FC.GOT_CELL_K; lia].
  - apply mw_rng_cell; [cbn; tauto | unfold FC.CELL_K; lia | unfold FC.CELL_K; lia].
  - exact mw_rng_c.
  - exact mw_rng_m.
  - exact mw_rng_shc.
  - exact mw_rng_shm.
  - intros Hlt. exact (mw_rng_body ltac:(lia)).
Qed.


(* ---- the close: from a final state of a footprint run (mn_post) to the statement's post ---- *)

Lemma mw_aview_bytes : forall (m : word -> option byte) A bs j, LM.bytes_at AI0.rsegs m A bs -> (j < length bs)%nat ->
  w_H W (Z_to_bv 64 (A + Z.of_nat j)) = false ->
  aview segs (w_H W) m (A + Z.of_nat j) = option_map (fun b : byte => bv_unsigned b) (nth_error bs j).
Proof.
  intros m A bs j (_ & _ & Hb) Hj Hv. unfold aview. rewrite FF.decode_mbyte_vis by exact Hv.
  rewrite (Hb j Hj). reflexivity.
Qed.

Lemma mw_close : forall (mX : word -> option byte) (mdX : Model) ms1 ms2 md',
  ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mX mdX k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TRANS_MN_STK <= a < sp) -> ~ (c <= a < c + 25) -> ~ (mp <= a < mp + 40) ->
     aview segs (w_H W) mX a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mX a) ->
  MNS.mn_post (gr 1) (gr 2) (gr 3) (gr 4) (gr 8) (gr 9) (gr 18) (gr 19) (gr 20) (gr 21) (gr 22) (gr 23)
    (gr 24) (gr 25) (gr 26) (gr 27) (@fp_regs fx) (@fp_csr fx) mX c mp body bb mj pos st ms1 ->
  Regs6ss.ms_eqv ms1 ms2 -> YK1b.mem_grows mX (ms_mem ms1) -> same_but_materialized mdX md' ->
  SRr segs W (mkCfg ms2 md') POST.
Proof.
  intros mX mdX ms1 ms2 md' HJX VX PX Hpost HE HG Hs.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    -> & MU & Hcur & Hmsg).
  destruct (FF.decode_eqv_mkst _ _ _ _ HE) as (R2 & -> & HX).
  cbn [ms_mem] in HG.
  pose proof mw_sp as (S1 & S2 & S3 & S4). pose proof mw_sp_bounds as (SB1 & SB2). pose proof mw_consts as CC.
  pose proof mw_c as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof mw_m as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  assert (Hsp' : bv_unsigned (gr 2) = sp) by reflexivity.
  (* the bytes of the walk's written range are visible *)
  assert (VWR : forall a, (sp - 128 <= a < sp) \/ (c <= a < c + 25) \/ (mp <= a < mp + 40) ->
            w_H W (Z_to_bv 64 a) = false).
  { intros a [Ha | [Ha | Ha]]; apply mw_vis; [apply mw_frame_win | apply C8 | apply M8]; lia. }
  (* the journal after the last run *)
  assert (JF : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m' md' k).
  { apply (ajournal_exec (SK := SK) segs B LAWS FF.decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mX mdX k
             m' md' (fun a => (sp - 128 <= a < sp) \/ (c <= a < c + 25) \/ (mp <= a < mp + 40)) HJX).
    - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|].
      rewrite Hsp'. unfold MNS.MN_FRAME. cbn [LFr.outside].
      split; [|split; [|split; [|exact I]]]; intros Hin; apply Hx; tauto.
    - intros x Hx. unfold mrestrict in *. destruct (w_H W x); [exact Hx|]. exact (HG x Hx).
    - intros x Hh. apply MU. rewrite Hsp'. unfold MNS.MN_FRAME. cbn [LFr.outside].
      pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
      assert (Hn : ~ ((sp - 128 <= bv_unsigned x < sp) \/ (c <= bv_unsigned x < c + 25) \/
                      (mp <= bv_unsigned x < mp + 40))).
      { intros Hin. pose proof (VWR _ Hin) as Hf. rewrite MState.Z_to_bv_bv_unsigned in Hf. congruence. }
      split; [|split; [|split; [|exact I]]]; intros Hin; apply Hn; tauto.
    - exact Hs.
    - intros a [Ha | [Ha | Ha]].
      + left. unfold TRANS_MN_STK, TRANS_MN_FRAME, ESTACK in Hwlo. lia.
      + exact (proj1 (mw_twr c 25 Htc a Ha)).
      + exact (proj1 (mw_twr mp 40 Htm a Ha)). }
  (* the final bytes of the cursor and the message *)
  pose proof Hcur as [[_ Bcur] _]. pose proof Hmsg as [[_ Bmsg] _].
  pose proof mw_cur_rw as [[_ Bcur0] _]. pose proof mw_msg_bytes as Bmsg0.
  (* every byte outside the call's window and outside the written range keeps its view *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TRANS_MN_STK <= a < sp) -> ~ trans_mn_wr c mp a ->
            aview segs (w_H W) m' a = aview segs (w_H W) memc a).
  { intros a Ha Hw HEa. unfold trans_mn_wr in HEa.
    assert (HC : (c <= a < c + 25) \/ (mp <= a < mp + 40) \/ (~ (c <= a < c + 25) /\ ~ (mp <= a < mp + 40)))
      by lia.
    destruct HC as [HC | [HC | [HC1 HC2]]].
    - (* a in [c, c + 16): the cursor's body and len *)
      assert (Ea : a = c + Z.of_nat (Z.to_nat (a - c))) by lia.
      set (j := Z.to_nat (a - c)) in Ea. rewrite Ea.
      assert (Hj : (j < 16)%nat) by (unfold j; lia).
      assert (Hlen : forall p0 s0, length (LCe.cells_bytes (PCu.cursor_cells body L p0 s0)) = 25%nat)
        by (intros; reflexivity).
      rewrite (mw_aview_bytes m' c _ j Bcur ltac:(rewrite Hlen; lia) ltac:(apply VWR; lia)).
      rewrite (mw_aview_bytes memc c _ j Bcur0 ltac:(rewrite Hlen; lia) ltac:(apply VWR; lia)).
      rewrite (mw_cur_prefix body L (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st)) pos st j Hj).
      reflexivity.
    - (* a in [mp + 4, mp + 8): the message's padding *)
      assert (Ea : a = mp + Z.of_nat (Z.to_nat (a - mp))) by lia.
      set (j := Z.to_nat (a - mp)) in Ea. rewrite Ea.
      assert (Hj : (4 <= j < 8)%nat) by (unfold j; lia).
      assert (Hl : (j < length (LCe.cells_bytes (PMs.msg_cells body mj (msg_step bb pos st))))%nat)
        by (rewrite mw_msg_len by exact Hmj; lia).
      rewrite (mw_aview_bytes m' mp _ j Bmsg Hl ltac:(apply VWR; lia)).
      rewrite (mw_aview_bytes memc mp _ j Bmsg0 ltac:(lia) ltac:(apply VWR; lia)).
      rewrite mw_msg_pad by first [exact Hmj | lia]. reflexivity.
    - (* outside both: the run and the views before *)
      rewrite <- (VX a Ha Hw HC1 HC2). apply aview_eq_of. unfold mrestrict.
      rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
      rewrite MState.unsigned_lit by lia. rewrite Hsp'. unfold MNS.MN_FRAME. cbn [LFr.outside].
      unfold TRANS_MN_STK, TRANS_MN_FRAME, ESTACK in Hw.
      split; [lia | split; [exact HC1 | split; [exact HC2 | exact I]]]. }
  apply SRr_ret. unfold trans_mn_post, decode_cg_post.
  exists lyc, Sc, R2, m', md', 0.
  split.
  { pose proof (LeafCgFacts.ret_ok_stmt_YK0s _ Hret) as Er. change (YK11.getr regs 1) with (gr 1) in Er.
    rewrite Er. reflexivity. }
  split; [unfold TRANS_MN_EV; lia|].
  split; [rewrite Z.add_0_r; exact JF|].
  split.
  { intros r Hr. rewrite (FF.decode_getr_xeqv _ _ HX). unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hr' as [-> | Hr']; [reflexivity|]). subst r. reflexivity. }
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    - intros a Ha Hw. apply KEEP; [lia | exact Hw |]. unfold trans_mn_wr. lia.
    - intros b n i Hin Hi HEi.
      destruct (al_blocks segs B LAWS lyc Sc W memc mdc b n mw_AR Hin) as (_ & B4 & Bc & _).
      apply KEEP; [lia | lia | exact HEi].
    - intros a Himg Hown Herr. pose proof (FF.decode_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow.
      apply KEEP; [lia | lia |]. unfold trans_mn_wr. intros [HE1 | [HE1 | HE1]].
      + exact (C7 a ltac:(lia) Himg).
      + exact (M7 a ltac:(lia) Himg).
      + exact (M7 a ltac:(lia) Himg).
    - intros cid p a Hin Hzr HEa.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid p mw_AR Hin) as (F1 & F2 & _).
      pose proof (fs_frame_bytes_nonneg cid) as F0.
      assert (Ha : 0 <= a < alloc_ceiling).
      { unfold frame_rng, in_zr in Hzr. cbn [fst snd] in Hzr.
        destruct Hzr as [Hz | Hz]; [lia|].
        unfold shadow_addr, SHADOW_OFF in Hz. Z.div_mod_to_equations. lia. }
      apply KEEP; [lia | lia | exact HEa].
    - intros a Ha Hw Hp. destruct (PX a Hp) as [Hh [b Hb]]. split; [exact Hh|].
      destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
      exfalso. apply (HG (Z_to_bv 64 a)); [rewrite Hb; discriminate | exact E].
    - intros a Ha. destruct JF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
      apply Hp. unfold TRANS_MN_STK, TRANS_MN_FRAME, ESTACK in *. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  split; [rewrite (FF.decode_getr_xeqv _ _ HX); reflexivity|].
  split.
  - unfold trans_mn_cur_bytes. apply (FF.decode_bytes_garr8 (w_H W) m' c); [|exact Bcur].
    intros j Hj. apply VWR. right; left. cbn in Hj. lia.
  - unfold trans_mn_msg_bytes. apply (FF.decode_bytes_garr8 (w_H W) m' mp); [|exact Bmsg].
    intros j Hj. apply VWR. right; right.
    rewrite mw_msg_len in Hj by exact Hmj. lia.
Qed.

(* ---- the message after the memset call ---- *)

Lemma mw_msg0 : forall (m1 m2 : word -> option byte),
  LSt.rw_cells AI0.rsegs m1 mp (MNS.mn_msg_pre mj pos) ->
  (forall i, 0 <= i < 40 -> ~ (8 <= i < 24) -> m2 (Z_to_bv 64 (mp + i)) = m1 (Z_to_bv 64 (mp + i))) ->
  (forall i, 8 <= i < 24 -> m2 (Z_to_bv 64 (mp + i)) = Some (Z_to_bv 8 0)) ->
  LSt.rw_cells AI0.rsegs m2 mp (MNS.mn_msg0 mj pos).
Proof.
  intros m1 m2 [[Hwf1 Hb1] Hw1] H2 H3.
  set (X := [nth 0 mj (b8 0); nth 1 mj (b8 0); b8 0; b8 0] ++ firstn 4 (skipn 4 mj)).
  set (Y := LM.le8 (Z_to_bv 64 (Z.of_nat pos)) ++ skipn 32 mj ++ []).
  set (Z16 := LM.le8 (Z_to_bv 64 0) ++ LM.le8 (Z_to_bv 64 0)).
  assert (EP : LCe.cells_bytes (MNS.mn_msg_pre mj pos) = X ++ (firstn 16 (skipn 8 mj) ++ Y)).
  { unfold MNS.mn_msg_pre, X, Y. cbn [LCe.cells_bytes LCe.cbytes app]. reflexivity. }
  assert (E0 : LCe.cells_bytes (MNS.mn_msg0 mj pos) = X ++ (Z16 ++ Y)).
  { unfold MNS.mn_msg0, X, Y, Z16. cbn [LCe.cells_bytes LCe.cbytes app]. rewrite <- !app_assoc. reflexivity. }
  assert (LX : length X = 8%nat) by (unfold X; rewrite length_app, length_firstn, length_skipn, Hmj; reflexivity).
  assert (LF : length (firstn 16 (skipn 8 mj)) = 16%nat) by (rewrite length_firstn, length_skipn, Hmj; reflexivity).
  assert (LZ : length Z16 = 16%nat) by reflexivity.
  assert (LY : length Y = 16%nat) by (unfold Y; rewrite !length_app, length_skipn, Hmj, LM.length_le8; reflexivity).
  rewrite EP in Hb1. apply LM.bytes_at_app in Hb1 as [BX BR]. apply LM.bytes_at_app in BR as [BF BY].
  rewrite LX in BF, BY. rewrite LF in BY.
  pose proof BX as (BX0 & BX1 & _). pose proof BY as (BY0 & BY1 & _).
  assert (Hsz : LCe.cells_size (MNS.mn_msg0 mj pos) = 40%nat) by reflexivity.
  assert (Hsz1 : LCe.cells_size (MNS.mn_msg_pre mj pos) = 40%nat) by reflexivity.
  rewrite Hsz1 in Hw1.
  split; [split|].
  - unfold MNS.mn_msg0. cbn [LCe.cells_wf LCe.cell_wf].
    rewrite length_firstn, !length_skipn, Hmj. cbn. tauto.
  - rewrite E0. apply LM.bytes_at_app. split.
    + apply (FF.decode_bytes_at_eq m1 m2 mp X BX). intros i Hi. rewrite LX in Hi. unfold LM.wa. apply H2; lia.
    + apply LM.bytes_at_app. rewrite LX, LZ. split.
      * split; [lia|]. split; [rewrite LZ; lia|]. intros i Hi. rewrite LZ in Hi.
        assert (Ez : nth_error Z16 i = Some (Z_to_bv 8 0)).
        { unfold Z16. do 16 (destruct i as [|i]; [reflexivity|]). lia. }
        rewrite Ez. unfold LM.mrd, LM.wa. replace (mp + Z.of_nat 8 + Z.of_nat i) with (mp + (8 + Z.of_nat i)) by lia.
        rewrite H3 by lia. reflexivity.
      * apply (FF.decode_bytes_at_eq m1 m2 _ Y BY). intros i Hi. rewrite LY in Hi. unfold LM.wa.
        replace (mp + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat i) with (mp + (24 + Z.of_nat i)) by lia.
        replace (mp + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat i) with (mp + (24 + Z.of_nat i)) by lia.
        apply H2; lia.
  - destruct Hw1 as (W0' & W1' & Hw). rewrite Hsz. split; [exact W0'|]. split; [exact W1'|].
    intros i Hi. change (Z.of_nat 40) with 40 in Hi.
    destruct (Z_lt_le_dec i 8) as [Hi8 | Hi8]; [| destruct (Z_lt_le_dec i 24) as [Hi24 | Hi24]].
    + unfold wview, LM.wa. rewrite H2 by lia. exact (Hw i ltac:(lia)).
    + exact (FF.decode_wview_some m2 _ _ (H3 i ltac:(lia))).
    + unfold wview, LM.wa. rewrite H2 by lia. exact (Hw i ltac:(lia)).
Qed.

(* ---- the memset call and the piece after it ---- *)

Lemma mw_call : forall ms1 ms2 md1, (pos < length bb)%nat ->
  MNS.mn_call (gr 1) (gr 2) (gr 3) (gr 4) (gr 8) (gr 9) (gr 18) (gr 19) (gr 20) (gr 21) (gr 22) (gr 23)
    (gr 24) (gr 25) (gr 26) (gr 27) (@fp_regs fx) (@fp_csr fx) memc c mp body bb mj pos ms1 ->
  Regs6ss.ms_eqv ms1 ms2 -> YK1b.mem_grows memc (ms_mem ms1) -> same_but_materialized mdc md1 ->
  SRr segs W (mkCfg ms2 md1) POST.
Proof.
  intros ms1 ms2 md1 Hlt Hcall HE HG Hs.
  assert (HL : (0 < length bb)%nat) by lia.
  destruct Hcall as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & FR1 & MS1).
  destruct (FF.decode_eqv_mkst _ _ _ _ HE) as (R1 & -> & HX1).
  cbn [ms_mem] in HG.
  pose proof mw_sp as (S1 & S2 & S3 & S4). pose proof mw_sp_bounds as (SB1 & SB2). pose proof mw_consts as CC.
  pose proof mw_c as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof mw_m as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  pose proof (mw_blk HL) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  assert (Hsp' : bv_unsigned (gr 2) = sp) by reflexivity.
  unfold TRANS_MN_STK, TRANS_MN_FRAME, ESTACK in S1, Hwlo.
  unfold TRANS_MN_CUR_SIZE, TRANS_MN_MSG_SIZE in Hcm.
  pose proof (Hmb HL) as HMB. pose proof (Hcb HL) as HCB. unfold TRANS_MN_CUR_SIZE, TRANS_MN_MSG_SIZE in HMB, HCB.
  (* the entry run wrote the frame and the message only *)
  assert (R1raw : forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 128 <= x < sp) -> ~ (mp <= x < mp + 40) ->
            m1 (Z_to_bv 64 x) = memc (Z_to_bv 64 x)).
  { intros x Hx H1 H2. apply MU1. rewrite MState.unsigned_lit by lia. rewrite Hsp'.
    unfold MNS.MN_FRAME. cbn [LFr.outside]. split; [exact H1 | split; [exact H2 | exact I]]. }
  assert (P1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) m1 a).
  { intros a [Hh [b Hb]]. split; [exact Hh|]. destruct (m1 (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
    exfalso. apply (HG (Z_to_bv 64 a)); [rewrite Hb; discriminate | exact E]. }
  (* the journal after the entry run *)
  assert (VW1 : forall a, (sp - 128 <= a < sp) \/ (mp <= a < mp + 40) -> w_H W (Z_to_bv 64 a) = false).
  { intros a [Ha | Ha]; apply mw_vis; [apply mw_frame_win | apply M8]; lia. }
  assert (HJ1 : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 md1 k).
  { apply (ajournal_exec (SK := SK) segs B LAWS FF.decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
             m1 md1 (fun a => (sp - 128 <= a < sp) \/ (mp <= a < mp + 40)) HJ).
    - intros x Hx. unfold mrestrict. rewrite (MU1 x); [reflexivity|].
      rewrite Hsp'. unfold MNS.MN_FRAME. cbn [LFr.outside].
      split; [|split; [|exact I]]; intros Hin; apply Hx; tauto.
    - intros x Hx. unfold mrestrict in *. destruct (w_H W x); [exact Hx|]. exact (HG x Hx).
    - intros x Hh. apply MU1. rewrite Hsp'. unfold MNS.MN_FRAME. cbn [LFr.outside].
      assert (Hn : ~ ((sp - 128 <= bv_unsigned x < sp) \/ (mp <= bv_unsigned x < mp + 40))).
      { intros Hin. pose proof (VW1 _ Hin) as Hf. rewrite MState.Z_to_bv_bv_unsigned in Hf. congruence. }
      split; [|split; [|exact I]]; intros Hin; apply Hn; tauto.
    - exact Hs.
    - intros a [Ha | Ha].
      + left. lia.
      + exact (proj1 (mw_twr mp 40 Htm a Ha)). }
  (* the registers at the call *)
  assert (R10 : YK11.getr R1 10 = w64 (mp + 8)) by (rewrite (FF.decode_getr_xeqv _ _ HX1); reflexivity).
  assert (R11 : YK11.getr R1 11 = w64 0) by (rewrite (FF.decode_getr_xeqv _ _ HX1); reflexivity).
  assert (R12 : YK11.getr R1 12 = w64 16) by (rewrite (FF.decode_getr_xeqv _ _ HX1); reflexivity).
  assert (Rsp : YK11.getr R1 (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (gr 2) - MNS.MN_FRAME))
    by (rewrite (FF.decode_getr_xeqv _ _ HX1); reflexivity).
  assert (Rgp : YK11.getr R1 3 = w64 (as_gp B)) by (rewrite (FF.decode_getr_xeqv _ _ HX1); exact Hgp).
  assert (Rtp : YK11.getr R1 4 = w64 (as_tp B)) by (rewrite (FF.decode_getr_xeqv _ _ HX1); exact Htp).
  assert (Rra : YK11.getr R1 1 = w64 MNS.MN_RET_MEMSET) by (rewrite (FF.decode_getr_xeqv _ _ HX1); reflexivity).
  assert (Ho : spZ R1 = sp0 + (sp - 128 - sp0)).
  { change (spZ R1) with (bv_unsigned (YK11.getr R1 (Z_to_bv 5 2))). rewrite Rsp, Hsp'.
    unfold MNS.MN_FRAME. rewrite MState.unsigned_lit by lia. lia. }
  (* a shadow byte of application memory lies outside the frame and the message *)
  assert (SHO : forall s, kLowMemEnd <= s < kHighShadowEnd ->
            0 <= s < 2 ^ 64 /\ ~ (sp - 128 <= s < sp) /\ ~ (mp <= s < mp + 40)).
  { intros s Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd in *. lia. }
  eapply SRr_bind.
  { change (Z_to_bv 64 MNS.MN_MEMSET) with (Z_to_bv 64 (transport_sigma TS___asan_memset)).
    apply (aj_intrin_at (SK := SK) segs B LAWS FF.decode_segs_low OSet (transport_sigma TS___asan_memset) (AMSET fx)
             W R1 m1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc md1 k (mp + 8) 0 16 (sp - 128 - sp0)
             (w64 MNS.MN_RET_MEMSET) HJ1 R10 R11 R12).
    - lia.
    - lia.
    - lia.
    - exact Ho.
    - rewrite Zminus_mod, (Zminus_mod sp 128), Hal, S3. reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - exact Rgp.
    - exact Rtp.
    - exact Rra.
    - apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - intros a Ha. split; [exact (proj1 (mw_twr mp 40 Htm a ltac:(lia)))|].
      unfold decode_off_win, TRANS_MN_STK, TRANS_MN_FRAME, TRANS_MN_MSG_SIZE, ESTACK in Hom. unfold ESTACK. lia.
    - unfold amem_range in *. lia.
    - intros x Hx. destruct (M9 x ltac:(lia)) as (s & Es & Hok). exists s. split; [|exact Hok].
      rewrite <- Es. apply aview_eq_of. unfold mrestrict.
      assert (Hsx : kLowMemEnd <= shadow_of_addr SHADOW_OFF x < kHighShadowEnd)
        by (unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd; Z.div_mod_to_equations; lia).
      destruct (SHO _ Hsx) as (Q1 & Q2 & Q3). rewrite (R1raw _ Q1 Q2 Q3). reflexivity.
    - intros _ s Hs'.
      assert (Hs2 : shadow_addr mp / 8 * 8 <= s < shadow_addr (mp + 40 - 1) / 8 * 8 + 8).
      { unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia. }
      assert (Hsx : kLowMemEnd <= s < kHighShadowEnd).
      { unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. Z.div_mod_to_equations. lia. }
      destruct (SHO _ Hsx) as (Q1 & Q2 & Q3).
      assert (E : aview segs (w_H W) m1 s = aview segs (w_H W) memc s).
      { apply aview_eq_of. unfold mrestrict. rewrite (R1raw _ Q1 Q2 Q3). reflexivity. }
      rewrite E. exact (M10 s Hs2).
    - exact I. }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10' & HSET & HKEEP & HPRES).
  (* the bytes the call kept, and the 16 it set *)
  assert (R2raw : forall a, 0 <= a < 2 ^ 64 -> ~ (mp + 8 <= a < mp + 24) -> ~ (sp - 128 - 4096 <= a < sp - 128) ->
            apresent (w_H W) m1 a -> mem2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
  { intros a Ha H1 H2 Hp. apply (FF.decode_byte_eq (w_H W) (w_H W) m1 mem2 a Hp (HPRES a Hp)).
    apply HKEEP; [exact Ha | lia | unfold ESTACK; lia]. }
  assert (P2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) by (intros a Hp; exact (HPRES a (P1 a Hp))).
  assert (Rraw : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 128 - 4096 <= a < sp) -> ~ (mp <= a < mp + 40) ->
            apresent (w_H W) memc a -> mem2 (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
  { intros a Ha H1 H2 Hp. rewrite (R2raw a Ha ltac:(lia) ltac:(lia) (P1 a Hp)). apply R1raw; lia. }
  assert (Z2 : forall i, 8 <= i < 24 -> mem2 (Z_to_bv 64 (mp + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. pose proof (HSET (i - 8) ltac:(lia)) as E. cbn iota in E.
    replace (mp + 8 + (i - 8)) with (mp + i) in E by lia.
    destruct (P2 (mp + i) (M8 (mp + i) ltac:(lia))) as [Hh [b Hb]].
    unfold aview, YP09.mbyte, mrestrict in E. rewrite Hh, Hb in E. cbn in E. injection E as E.
    rewrite Hb. f_equal. apply bv_eq. rewrite E. reflexivity. }
  (* the shadow bytes of the three ranges are present at the entry *)
  assert (SHP : forall q n, FC.addressable memc q n ->
            (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (FC.shadow_addr (q + i))) = false) ->
            forall i, 0 <= i < n -> apresent (w_H W) memc (FC.shadow_addr (q + i))).
  { intros q n (A0 & A1 & A2 & AB) Hv i Hi. split; [exact (Hv i Hi)|].
    destruct (AB i Hi) as (_ & b & Hb & _). exists b. unfold FC.APPMEM_END in A2.
    apply (mw_mrd_high memc _ b); [unfold FC.shadow_addr, FC.ASAN_K, kLowMemEnd; Z.div_mod_to_equations; lia | exact Hb]. }
  assert (SHR : forall q n, FC.addressable memc q n ->
            (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (FC.shadow_addr (q + i))) = false) ->
            FC.addressable mem2 q n).
  { intros q n HA Hv. apply (FF.decode_addressable_eq memc mem2 q n HA). intros i Hi.
    pose proof HA as (A0 & A1 & A2 & _). unfold FC.APPMEM_END in A2.
    assert (Hsx : kLowMemEnd <= FC.shadow_addr (q + i) < kHighShadowEnd)
      by (unfold FC.shadow_addr, FC.ASAN_K, kLowMemEnd, kHighShadowEnd; Z.div_mod_to_equations; lia).
    destruct (SHO _ Hsx) as (Q1 & Q2 & Q3). unfold LM.wa.
    apply Rraw; [exact Q1 | unfold kLowMemEnd, kHighShadowEnd in Hsx; lia | exact Q3 | exact (SHP q n HA Hv i Hi)]. }
  (* the callee-saved registers after the call *)
  assert (EQ : forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr R1 (Z_to_bv 5 r)).
  { intros r Hr. exact (HP2 r Hr). }
  assert (E2 : YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (bv_unsigned (gr 2) - MNS.MN_FRAME))
    by (rewrite EQ by (unfold acallee_saved; lia); exact Rsp).
  assert (E3 : YK11.getr regs2 (Z_to_bv 5 3) = gr 3)
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E4 : YK11.getr regs2 (Z_to_bv 5 4) = gr 4)
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E8 : YK11.getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 (FC.shadow_addr (mp + 2)))
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E9 : YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 mp)
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E18 : YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 c)
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E19 : YK11.getr regs2 (Z_to_bv 5 19) = Z_to_bv 64 (Z.of_nat pos))
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E20 : YK11.getr regs2 (Z_to_bv 5 20) = Z_to_bv 64 (mp + 2))
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E21 : YK11.getr regs2 (Z_to_bv 5 21) = Z_to_bv 64 (body + Z.of_nat pos))
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E22 : YK11.getr regs2 (Z_to_bv 5 22) = Z_to_bv 64 (mp + 8))
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E23 : YK11.getr regs2 (Z_to_bv 5 23) = Z_to_bv 64 (FC.shadow_addr (c + 16)))
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E24 : YK11.getr regs2 (Z_to_bv 5 24) = Z_to_bv 64 FC.ASAN_K)
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E25 : YK11.getr regs2 (Z_to_bv 5 25) = Z_to_bv 64 L)
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E26 : YK11.getr regs2 (Z_to_bv 5 26) = Z_to_bv 64 (at8 bb pos))
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  assert (E27 : YK11.getr regs2 (Z_to_bv 5 27) = Z_to_bv 64 body)
    by (rewrite EQ, (FF.decode_getr_xeqv _ _ HX1) by (unfold acallee_saved; lia); reflexivity).
  change (SRr segs W (@cfg_at fx segs MNS.MN_RET_MEMSET regs2 mem2 md2) POST).
  apply (FF.decode_run W regs2 mem2 md2 MNS.MN_RET_MEMSET
           (MNS.mn_post (gr 1) (gr 2) (gr 3) (gr 4) (gr 8) (gr 9) (gr 18) (gr 19) (gr 20) (gr 21) (gr 22) (gr 23)
              (gr 24) (gr 25) (gr 26) (gr 27) (@fp_regs fx) (@fp_csr fx) mem2 c mp body bb mj pos st) POST).
  - unfold LCK.ms_of_regs.
    rewrite E2, E3, E4, E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    pose proof HBODY as HB. unfold MNS.mn_body_F in HB.
    apply (HB RNG (gr 2) (gr 1) (gr 8) (gr 9) (gr 18) (gr 19) (gr 20) (gr 21) (gr 22) (gr 23) (gr 24) (gr 25)
             (gr 26) (gr 27)).
    unfold MNS.mn_ctx. rewrite Hsp'.
    split; [exact Hlt|]. split; [exact Hst|]. split; [exact Hmj|].
    split; [unfold MNS.MN_FRAME; lia|].
    split; [unfold FC.app_mem, FC.HIGHMEM_BEG, FC.APPMEM_END, MNS.MN_FRAME; lia|].
    split; [unfold FC.app_mem, FC.HIGHMEM_BEG, FC.APPMEM_END; lia|].
    split.
    { apply (FF.decode_rw_cells_eq m1 mem2 _ _ FR1). intros i Hi. cbn in Hi. unfold LM.wa.
      rewrite Hsp' in *. unfold MNS.MN_FRAME in *.
      apply R2raw; [lia | lia | lia |]. apply P1, mw_frame_win. lia. }
    split.
    { apply (FF.decode_rw_cells_eq memc mem2 c _ mw_cur_rw). intros i Hi. cbn in Hi. unfold LM.wa.
      apply Rraw; [lia | lia | lia | apply C8; lia]. }
    split.
    { apply (mw_msg0 m1 mem2 MS1); [|exact Z2].
      intros i Hi Hn. apply R2raw; [lia | lia | lia |]. apply P1, M8. lia. }
    split.
    { (* the body's bytes after the call: the same view (it lies outside [mp + 8, mp + 24) and the call's window),
         and visible *)
      apply (FF.decode_garr8_bytes (w_H W) mem2 body bb); [lia | lia | |].
      - intros j Hj. apply B4. lia.
      - apply (garr8_frame segs (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) body (map bz bb) Gb).
        intros a Ha. rewrite length_map in Ha. apply mw_mbyte_of_aview.
        rewrite (HKEEP a ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)).
        apply aview_eq_of. unfold mrestrict. rewrite (R1raw a ltac:(lia) ltac:(lia) ltac:(lia)). reflexivity. }
    split; [exact (SHR c 25 C5 C6)|].
    split; [exact (SHR mp 40 M5 M6)|].
    split; [exact (SHR body L B6 B7)|].
    pose proof mw_off_c as O1. pose proof mw_off_m as O2. pose proof (mw_off_body HL) as O3.
    unfold AsanKA.off_stk in O1, O2, O3 |- *. rewrite Hsp' in O1, O2, O3.
    split; [exact O1|]. split; [exact O2|]. split; [exact O3|].
    pose proof (Hcb HL) as X1. pose proof (Hmb HL) as X2.
    unfold TRANS_MN_CUR_SIZE, TRANS_MN_MSG_SIZE in X1, X2.
    split; [exact Hcm|]. split; [exact X1|]. split; [exact X2|].
    split; [unfold MNS.MN_FRAME; exact mw_rng_frame|].
    split; [exact mw_rng_c|]. split; [exact mw_rng_m|]. split; [exact (proj1 (mw_rng_body HL))|].
    split; [exact mw_rng_shc|]. split; [exact mw_rng_shm|]. exact (proj2 (mw_rng_body HL)).
  - intros ms1' ms2' md' HP' HE' HG' Hs'.
    apply (mw_close mem2 md2 ms1' ms2' md' HJ2); [| | exact HP' | exact HE' | exact HG' | exact Hs'].
    + intros a Ha Hw Hc' Hm'. unfold TRANS_MN_STK, TRANS_MN_FRAME, ESTACK in Hw.
      rewrite (HKEEP a Ha ltac:(lia) ltac:(unfold ESTACK; lia)).
      apply aview_eq_of. unfold mrestrict. rewrite (R1raw a Ha ltac:(lia) Hm'). reflexivity.
    + exact P2.
Qed.

Theorem mw_main : SRr segs W (@cfg_at fx segs (transport_sigma TS_diginet_msg_next) regs memc mdc) POST.
Proof.
  apply (FF.decode_run W regs memc mdc _ _ POST mw_entry_run).
  intros ms1 ms2 md1 HP HE HG Hs.
  destruct HP as [Hpost | [Hlt Hcall]].
  - apply (mw_close memc mdc ms1 ms2 md1 HJ); [intros; reflexivity | intros a Ha; exact Ha | exact Hpost | exact HE |
      exact HG | exact Hs].
  - exact (mw_call ms1 ms2 md1 Hlt Hcall HE HG Hs).
Qed.

End Walk.
