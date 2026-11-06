(* diginet_msg_next_walk_lib: the caller-journal walk of diginet_msg_next (fuzz_decode.asan-ubsan 0x82328) from its
   footprint run (lib/B/Prog/diginet_msg_next_segs.v mn_entry_F), at the premise list of the frozen statement
   lib/B/Prog/diginet_msg_next_cg.v decode_diginet_msg_next_cg.

   Image B's diginet_msg_next calls no function, so the walk is one footprint run and its close:
     1. mn_entry_F runs from the entry to the return under the caller's footprint (every visible byte), carried
        into SRr by lib/B/Prog/DecodeFevt.v decode_run; its premises are the statement's premises read as the run's
        memory facts (the cursor and message bytes from their garr8 and their write right, the body from trans_src_ok
        (decode_rd_ok in every case, trans_src_ok_rd) and decode_off_win, the shadow bytes from decode_rd_ok, the frame
        [sp - 64, sp) from the journal's stack window, c mod 8 = 0 and m mod 8 = 0 as they are, 0 < body from
        trans_src_ok_place);
     2. mw_close: the journal follows the run (YCbq.v ajournal_exec, the written bytes in the journal's stack window
        or in [c, c + 25), [mp, mp + 40) by decode_twr_ok); acall_kept holds because every byte outside the frame and
        outside [c, c + 25), [mp, mp + 40) keeps its view, and the bytes of those two ranges outside the written
        range (the cursor's body and len, the message's padding) are the same bytes before and after. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YK1b YP09 YA0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame Cells Step ExecF PropExec Regs6ss MState.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_msg_next_segs TransportFevt LeafCgKit LeafCgFacts AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_cursor_init_c diginet_msg_next_c.
Import ListNotations.
Open Scope Z_scope.
Module MNS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_segs.
Module FF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.TransportFevt.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module LM := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LCe := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module LSt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Step.
Module LFr := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Frame.
Module BI0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Img0.
Module FC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module PCu := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_cursor_init_c.
Module PMs := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_msg_next_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The statement's entry address is the footprint run's: DDB_diginet_msg_next = 0x82328 = MN_ENTRY. *)
Lemma mw_entry_addr : transportb_sigma TB_diginet_msg_next = MNS.MN_ENTRY.
Proof. reflexivity. Qed.

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

(* A byte the view reads is not hidden: a hidden byte reads nothing, not even the image (w_Hoff, YA0o.v
   seg_rom_hidden). *)
Lemma mw_vis_of_aview : forall (W : world tfibsegs) (m : word -> option byte) a,
  aview tfibsegs (w_H W) m a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m a Hv. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply Hv. unfold aview, YP09.mbyte, mrestrict. rewrite E. cbv beta iota.
  rewrite (YA0o.seg_rom_hidden tfibsegs (w_H W) (Z_to_bv 64 a) (w_Hoff W) E). reflexivity.
Qed.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation SK := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HENT : MNS.mn_entry_F.
Local Abbreviation ajournalB := (@ajournal rc SK segs B).

Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z).
Hypothesis HJ : ajournalB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hret : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis H10 : YK11.getr regs 10 = w64 c.
Hypothesis H11 : YK11.getr regs 11 = w64 mp.
Hypothesis Hwlo : sp0 - STK <= spZ regs - TRANS_MN_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hc0 : c <> 0.
Hypothesis Hm0 : mp <> 0.
Hypothesis Hc8 : c mod 8 = 0.
Hypothesis Hm8 : mp mod 8 = 0.
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

Lemma mw_sp_bounds : 0x7fff7f800000 + 64 <= sp /\ sp <= 2 ^ 47.
Proof. pose proof mw_consts. pose proof mw_sp as (H1 & H2 & _). unfold TRANS_MN_STK, TRANS_MN_FRAME in H1. lia. Qed.

(* the frame [sp - 64, sp) is in the journal's stack window *)
Lemma mw_frame_win : forall a, sp - 64 <= a < sp -> apresent (w_H W) memc a.
Proof. intros a Ha. apply mw_win. unfold TRANS_MN_STK, TRANS_MN_FRAME in Hwlo. lia. Qed.

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
  (forall a, mp <= a < mp + 40 -> apresent (w_H W) memc a).
Proof.
  destruct (mw_fake mp 40 Hfm ltac:(lia)) as (F1 & F2 & F3).
  destruct (mw_rd mp 40 Hrm ltac:(lia)) as (_ & R2 & R3 & R4 & R5 & _).
  split; [exact F1|]. split; [exact F2|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [exact R5|]. split; [exact F3|].
  intros a Ha. exact (proj2 (mw_twr mp 40 Htm a Ha)).
Qed.

(* the body when it is not empty: placed by trans_src_ok (trans_src_ok_place: in [4096, alloc_ceiling) or in the
   machine stack below 2 ^ 47), its bytes visible and marked usable (trans_src_ok_rd), outside this call's window
   (decode_off_win) *)
Lemma mw_blk : (0 < length bb)%nat ->
  4096 <= body /\ body + L <= 2 ^ 47 /\ amem_range body L /\
  (forall a, body <= a < body + L -> w_H W (Z_to_bv 64 a) = false) /\
  (body + L <= sp - 64 \/ sp <= body) /\
  FC.addressable memc body L /\ (forall i, 0 <= i < L -> w_H W (Z_to_bv 64 (FC.shadow_addr (body + i))) = false).
Proof.
  intros HL. assert (HL' : 0 < L) by lia.
  pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc body L mw_AR (Hblk HL) HL') as Hrd.
  pose proof (trans_src_ok_place B LAWS lyc Sc W memc mdc body L mw_AR (Hblk HL) HL') as Hpl.
  pose proof mw_consts as C.
  destruct (mw_rd body L Hrd HL') as (R1 & R2 & R3 & R4 & R5 & _).
  pose proof (Hob HL) as Ho. unfold decode_off_win, TRANS_MN_STK, TRANS_MN_FRAME in Ho.
  split; [destruct Hpl as [Hp | Hp]; lia|].
  split; [destruct Hpl as [Hp | Hp]; lia|].
  split; [exact R3|].
  split; [intros a Ha; exact (mw_vis_of_aview W memc a (proj1 Hrd a Ha))|].
  split; [lia|].
  split; [exact R4 | exact R5].
Qed.

(* ---- the memory facts the footprint run reads, at the entry memory ---- *)

Lemma mw_cur_rw : LSt.rw_cells BI0.rsegs memc c (PCu.cursor_cells body L pos st).
Proof.
  pose proof mw_c as (C1 & C2 & C3 & _ & _ & _ & _ & C8).
  apply (FF.decode_rw_of_garr8 (w_H W) memc c); [cbn; tauto | lia | cbn; lia | | exact Gc].
  intros i Hi. apply C8. cbn in Hi. lia.
Qed.

Lemma mw_msg_rw : LSt.rw_cells BI0.rsegs memc mp [LCe.CB 40 mj].
Proof.
  pose proof mw_m as (M1 & M2 & M3 & _ & _ & _ & _ & M8).
  apply (FF.decode_rw_of_garr8 (w_H W) memc mp); [cbn; tauto | lia | cbn; lia | |].
  - intros i Hi. apply M8. cbn in Hi. lia.
  - cbn [LCe.cells_bytes LCe.cbytes]. rewrite app_nil_r. exact Gm.
Qed.

Lemma mw_msg_bytes : LM.bytes_at BI0.rsegs memc mp mj.
Proof.
  pose proof mw_m as (M1 & M2 & M3 & _ & _ & _ & _ & M8).
  apply (FF.decode_garr8_bytes (w_H W) memc mp mj); [lia | rewrite Hmj; lia | | exact Gm].
  intros j Hj. rewrite Hmj in Hj. exact (proj1 (M8 (mp + Z.of_nat j) ltac:(lia))).
Qed.

Lemma mw_body_bytes : (0 < length bb)%nat -> LM.bytes_at BI0.rsegs memc body bb.
Proof.
  intros HL. pose proof (mw_blk HL) as (B1 & B2 & _ & B4 & _). pose proof mw_consts.
  apply (FF.decode_garr8_bytes (w_H W) memc body bb); [lia | lia | | exact Gb].
  intros j Hj. exact (B4 (body + Z.of_nat j) ltac:(lia)).
Qed.

(* ---- the footprint ranges ---- *)

Lemma mw_vis : forall a, apresent (w_H W) memc a -> w_H W (Z_to_bv 64 a) = false.
Proof. intros a [H _]. exact H. Qed.

Lemma mw_rng_frame : ExecF.rng RNG (sp - 64) 64.
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
  pose proof mw_m as (M1 & M2 & M3 & _ & _ & _ & _ & M8).
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
  intros HL. pose proof (mw_blk HL) as (B1 & B2 & _ & B4 & _ & _ & B7). pose proof mw_consts.
  split.
  - apply FF.decode_rng_vis; [lia | lia |]. intros i Hi. apply B4. lia.
  - apply mw_shadow_rng_vis; [lia | lia | lia | exact B7].
Qed.

Lemma mw_off_c : AsanKA.off_stk (gr 2) MNS.MN_FRAME c 25.
Proof.
  unfold AsanKA.off_stk, MNS.MN_FRAME. change (bv_unsigned (gr 2)) with sp.
  unfold decode_off_win, TRANS_MN_STK, TRANS_MN_FRAME, TRANS_MN_CUR_SIZE in Hoc. lia.
Qed.

Lemma mw_off_m : AsanKA.off_stk (gr 2) MNS.MN_FRAME mp 40.
Proof.
  unfold AsanKA.off_stk, MNS.MN_FRAME. change (bv_unsigned (gr 2)) with sp.
  unfold decode_off_win, TRANS_MN_STK, TRANS_MN_FRAME, TRANS_MN_MSG_SIZE in Hom. lia.
Qed.

Lemma mw_off_body : (0 < length bb)%nat -> AsanKA.off_stk (gr 2) MNS.MN_FRAME body L.
Proof.
  intros HL. pose proof (mw_blk HL) as (B1 & B2 & _ & _ & B5 & _).
  unfold AsanKA.off_stk, MNS.MN_FRAME. change (bv_unsigned (gr 2)) with sp. lia.
Qed.

(* ---- the footprint run: the entry to the return ---- *)

Lemma mw_entry_run :
  ExecF.evtF BI0.rsegs RNG
    (MNS.mn_post (gr 1) (gr 2) (gr 3) (gr 4) (gr 8) (gr 9) (gr 18) (gr 19) (gr 20) (gr 21) (gr 22) (gr 23)
       (gr 24) (gr 25) (gr 26) (gr 27) (@fp_regs fx) (@fp_csr fx) memc c mp body bb mj pos st)
    (@LCK.ms_of_regs fx (transportb_sigma TB_diginet_msg_next) regs memc).
Proof.
  pose proof mw_sp as (S1 & S2 & S3 & S4). pose proof mw_sp_bounds as (SB1 & SB2). pose proof mw_consts as CC.
  pose proof mw_c as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof mw_m as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  pose proof HENT as HE. unfold MNS.mn_entry_F in HE.
  rewrite mw_entry_addr. unfold LCK.ms_of_regs.
  eapply HE with (lo := sp - TRANS_MN_STK).
  - exact H10.
  - exact H11.
  - exact Hc0.
  - exact Hm0.
  - exact Hc8.
  - exact Hm8.
  - exact Hpos.
  - exact Hst.
  - exact Hmj.
  - change (bv_unsigned (gr 2)) with sp.
    apply (FF.decode_stk_present (w_H W)); [lia | lia |].
    intros a Ha. apply mw_win. lia.
  - change (bv_unsigned (gr 2)) with sp. unfold MNS.MN_FRAME, TRANS_MN_STK, TRANS_MN_FRAME. lia.
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
    pose proof (mw_blk HL) as (B1 & _ & _ & _ & _ & B6 & _).
    split; [lia|].
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

(* ---- the close: from a final state of the footprint run (mn_post) to the statement's post ---- *)

Lemma mw_aview_bytes : forall (m : word -> option byte) A bs j, LM.bytes_at BI0.rsegs m A bs -> (j < length bs)%nat ->
  w_H W (Z_to_bv 64 (A + Z.of_nat j)) = false ->
  aview segs (w_H W) m (A + Z.of_nat j) = option_map (fun b : byte => bv_unsigned b) (nth_error bs j).
Proof.
  intros m A bs j (_ & _ & Hb) Hj Hv. unfold aview. rewrite FF.decode_mbyte_vis by exact Hv.
  rewrite (Hb j Hj). reflexivity.
Qed.

Lemma mw_close : forall ms1 ms2 md',
  MNS.mn_post (gr 1) (gr 2) (gr 3) (gr 4) (gr 8) (gr 9) (gr 18) (gr 19) (gr 20) (gr 21) (gr 22) (gr 23)
    (gr 24) (gr 25) (gr 26) (gr 27) (@fp_regs fx) (@fp_csr fx) memc c mp body bb mj pos st ms1 ->
  Regs6ss.ms_eqv ms1 ms2 -> YK1b.mem_grows memc (ms_mem ms1) -> same_but_materialized mdc md' ->
  SRr segs W (mkCfg ms2 md') POST.
Proof.
  intros ms1 ms2 md' Hpost HE HG Hs.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    -> & MU & Hcur & Hmsg).
  destruct (FF.decode_eqv_mkst _ _ _ _ HE) as (R2 & -> & HX).
  cbn [ms_mem] in HG.
  pose proof mw_sp as (S1 & S2 & S3 & S4). pose proof mw_sp_bounds as (SB1 & SB2). pose proof mw_consts as CC.
  pose proof mw_c as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof mw_m as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  assert (Hsp' : bv_unsigned (gr 2) = sp) by reflexivity.
  (* the bytes of the run's written range are visible *)
  assert (VWR : forall a, (sp - 64 <= a < sp) \/ (c <= a < c + 25) \/ (mp <= a < mp + 40) ->
            w_H W (Z_to_bv 64 a) = false).
  { intros a [Ha | [Ha | Ha]]; apply mw_vis; [apply mw_frame_win | apply C8 | apply M8]; lia. }
  (* the journal after the run *)
  assert (JF : ajournalB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m' md' k).
  { apply (ajournal_exec (SK := SK) segs B LAWS FF.decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
             m' md' (fun a => (sp - 64 <= a < sp) \/ (c <= a < c + 25) \/ (mp <= a < mp + 40)) HJ).
    - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|].
      rewrite Hsp'. unfold MNS.MN_FRAME. cbn [LFr.outside].
      split; [|split; [|split; [|exact I]]]; intros Hin; apply Hx; tauto.
    - intros x Hx. unfold mrestrict in *. destruct (w_H W x); [exact Hx|]. exact (HG x Hx).
    - intros x Hh. apply MU. rewrite Hsp'. unfold MNS.MN_FRAME. cbn [LFr.outside].
      pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
      assert (Hn : ~ ((sp - 64 <= bv_unsigned x < sp) \/ (c <= bv_unsigned x < c + 25) \/
                      (mp <= bv_unsigned x < mp + 40))).
      { intros Hin. pose proof (VWR _ Hin) as Hf. rewrite MState.Z_to_bv_bv_unsigned in Hf. congruence. }
      split; [|split; [|split; [|exact I]]]; intros Hin; apply Hn; tauto.
    - exact Hs.
    - intros a [Ha | [Ha | Ha]].
      + left. unfold TRANS_MN_STK, TRANS_MN_FRAME in Hwlo. lia.
      + exact (proj1 (mw_twr c 25 Htc a Ha)).
      + exact (proj1 (mw_twr mp 40 Htm a Ha)). }
  (* the final bytes of the cursor and the message *)
  pose proof Hcur as [[_ Bcur] _]. pose proof Hmsg as [[_ Bmsg] _].
  pose proof mw_cur_rw as [[_ Bcur0] _]. pose proof mw_msg_bytes as Bmsg0.
  (* every byte outside the frame and outside the written range keeps its view *)
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
    - (* outside both: the run kept the byte *)
      apply aview_eq_of. unfold mrestrict.
      rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
      rewrite MState.unsigned_lit by lia. rewrite Hsp'. unfold MNS.MN_FRAME. cbn [LFr.outside].
      unfold TRANS_MN_STK, TRANS_MN_FRAME in Hw.
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
    - intros a Ha Hw Hp. destruct Hp as [Hh [b Hb]]. split; [exact Hh|].
      destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
      exfalso. apply (HG (Z_to_bv 64 a)); [rewrite Hb; discriminate | exact E].
    - intros a Ha. destruct JF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _).
      apply Hp. unfold TRANS_MN_STK, TRANS_MN_FRAME in *. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  split; [rewrite (FF.decode_getr_xeqv _ _ HX); reflexivity|].
  split.
  - unfold trans_mn_cur_bytes. apply (FF.decode_bytes_garr8 (w_H W) m' c); [|exact Bcur].
    intros j Hj. apply VWR. right; left. cbn in Hj. lia.
  - unfold trans_mn_msg_bytes. apply (FF.decode_bytes_garr8 (w_H W) m' mp); [|exact Bmsg].
    intros j Hj. apply VWR. right; right.
    rewrite mw_msg_len in Hj by exact Hmj. lia.
Qed.

(* ---- the walk ---- *)

Theorem mw_main : SRr segs W (@cfg_at fx segs (transportb_sigma TB_diginet_msg_next) regs memc mdc) POST.
Proof.
  apply (FF.decode_run W regs memc mdc _ _ POST mw_entry_run).
  intros ms1 ms2 md1 HP HE HG Hs.
  exact (mw_close ms1 ms2 md1 HP HE HG Hs).
Qed.

End Walk.
