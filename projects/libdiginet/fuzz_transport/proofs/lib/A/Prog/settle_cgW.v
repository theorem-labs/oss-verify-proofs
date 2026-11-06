(* settle_cgW: Theorem transport_settle_cg_holds : the statement transport_settle_cg_holds_stmt of
   lib/A/Prog/settle_cg.v, the image-A caller-journal walk of settle (fuzz_transport.asan e89be137db17, entry 0x83cac =
   transport_sigma TS_settle, 84 bytes, frame 16).

   The walk (the donor walk lib/A/Prog/check_inflight_settle_cgW.v of this unit, with two donor callees and a tail
   jump):
   - an inner journal is started at the entry (lib/Reusable/YCbq.v ajournal_sub_init; stack window
     [spZ regs - SETTLE_STK, spZ regs), no footprint, no frame of its own); every call is made inside it;
   - the world relation is read at the raw memory (csw_view): every payload byte of the harness globals lies in a
     loaded segment, so the world hides none of them;
   - the code runs as the footprint runs of settle_seg_runs.v, carried into SRr by DgnTransportCgRun.v decode_run;
     between the calls the walk keeps settle_inv: the inner journal at the current state, the callee-saved registers
     but sp and s0 of the entry (settle_ks), sp = entry sp - 16, s0 = ticked, the frame [sp - 16, sp) holding the
     entry s0 and ra, and the world relation at the same Bw;
   - a leaf call (check_ack_settle, check_state_settle, check_keepalive_settle) goes through DgnTransportLeafb.v
     decode_leafb_journal (settle_leaf_step): the leaf keeps every byte outside its stack window, so the frame and
     the world bytes are the same after it;
   - a donor call (check_inflight_settle, check_latest_queue) applies the callee's statement to the inner journal; its
     post (DgnTransportCg.v decode_cg_post, YCbq.v acall_kept) keeps the frame (above the callee's window) and every
     byte of G (image bytes outside the owned statics and errno: gx_ok, gx_noerrno), so the world relation holds again
     (settle_donor_post, settle_tw_donor);
   - the tail jump at 0x83cfc runs check_latest_drain from settle's entry sp with settle's ra and s0 (the run restores
     them from the frame): decode_leafb_journal at offset 0, and its return is settle's return;
   - at each of the three returns the inner journal composes with the caller's by YCbq.v ajournal_sub, the kept bytes
     come from YCbq.v acall_kept_of_journal; no event, no frame, the blocks a permutation of the call state's (the two
     donor posts), no meter charge (the two donor posts, YC5d.v mle_station). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Frame Regs6ss ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCgRun DgnTransportLeafb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LeafCgFacts TWorldG TWorldA TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_inflight_settle_cg check_latest_queue_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import settle_cg settle_seg_runs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit AsanKA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_ack_settle_c check_state_settle_c check_keepalive_settle_c check_latest_drain_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_ack_settle_cg check_state_settle_cg check_keepalive_settle_cg check_latest_drain_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module LASc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_settle_c.
Module LSSc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_settle_c.
Module LKSc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_settle_c.
Module LLDc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_drain_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Local Abbreviation segs := tfibsegs.

(* A register of a state reached by a run, read off the run's register map (DgnTransportCgRun.v decode_ms_reg, then
   the map computed). *)
Ltac settle_reg EQV := etransitivity; [apply (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV); reflexivity | reflexivity].

(* A closed arithmetic fact over the unit's constants (no Z_to_bv of an open term). *)
Ltac settle_closed :=
  first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity ].

(* The entry, as the listing layer names it. *)
Lemma settle_entry_at : transport_sigma TS_settle = SETTLE_ENTRY.
Proof. reflexivity. Qed.

(* Every payload byte of the 18 harness globals lies in a loaded segment of image A, so no world hides it. *)
Lemma settle_hull_vis : forall (W : world segs) x,
  TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI -> w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. apply (decode_vis_seg W).
  apply (decode_covers_img TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) x); [vm_compute; reflexivity | lia].
Qed.

(* The world relation at the view of a world is the world relation at the raw memory, and back. *)
Lemma settle_tw_csw : forall (W : world segs) mem Bw,
  tw_at TMAP_A (aview segs (w_H W) mem) Bw -> tw_at TMAP_A (csw_view mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
  unfold csw_view. rewrite (decode_aview_mrd W mem x (settle_hull_vis W x (TMAP_A_hull x Hx))). reflexivity.
Qed.

Lemma settle_tw_aview : forall (W : world segs) mem Bw,
  tw_at TMAP_A (csw_view mem) Bw -> tw_at TMAP_A (aview segs (w_H W) mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
  unfold csw_view. rewrite (decode_aview_mrd W mem x (settle_hull_vis W x (TMAP_A_hull x Hx))). reflexivity.
Qed.

(* The world relation after a step that keeps every byte of the hull's view (the worlds may differ). *)
Lemma settle_tw_keep : forall (W1 W2 : world segs) m1 m2 Bw,
  tw_at TMAP_A (csw_view m1) Bw ->
  (forall x, TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI -> aview segs (w_H W2) m2 x = aview segs (w_H W1) m1 x) ->
  tw_at TMAP_A (csw_view m2) Bw.
Proof.
  intros W1 W2 m1 m2 Bw H K. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
  pose proof (TMAP_A_hull x Hx) as Hh.
  unfold csw_view.
  rewrite <- (decode_aview_mrd W2 m2 x (settle_hull_vis W2 x Hh)), <- (decode_aview_mrd W1 m1 x (settle_hull_vis W1 x Hh)).
  exact (K x Hh).
Qed.

(* RNG_W W holds on a range of the hull. *)
Lemma settle_rng_hull : forall (W : world segs) lo len, TG.G_HARNESS_LO <= lo -> lo + len <= TG.G_HARNESS_HI ->
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
  intros W lo len H1 H2. apply (decode_rng W); [unfold TG.G_HARNESS_LO in *; lia | unfold TG.G_HARNESS_HI in *; lia |].
  intros b Hb. apply settle_hull_vis. lia.
Qed.

(* A byte present in two memories (of two worlds) with the same view is the same byte. *)
Lemma settle_present_eq2 : forall (W W' : world segs) m m' a,
  apresent (w_H W) m a -> apresent (w_H W') m' a -> aview segs (w_H W') m' a = aview segs (w_H W) m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros W W' m m' a (Hh & b & Hb) (Hh' & b' & Hb') E.
  rewrite (decode_aview_mrd W' m' a Hh'), (decode_aview_mrd W m a Hh) in E. unfold mrd, wa in E.
  rewrite Hb, Hb' in E. cbn in E. injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

(* settle's frame, kept by a step that keeps the view of its 16 bytes, present before and after. *)
Lemma settle_frame_keep : forall (W1 W2 : world segs) m1 m2 base (v0 v1 : word),
  (forall i, 0 <= i < 16 -> apresent (w_H W1) m1 (base + i)) ->
  (forall i, 0 <= i < 16 -> apresent (w_H W2) m2 (base + i)) ->
  (forall i, 0 <= i < 16 -> aview segs (w_H W2) m2 (base + i) = aview segs (w_H W1) m1 (base + i)) ->
  rw_cells rsegs m1 base [C8 v0; C8 v1] -> rw_cells rsegs m2 base [C8 v0; C8 v1].
Proof.
  intros W1 W2 m1 m2 base v0 v1 P1 P2 E FR.
  apply (decode_frame_ext base 16 [C8 v0; C8 v1] m1 m2 ltac:(cbn; lia)); [|exact FR].
  intros i Hi. unfold wa. exact (settle_present_eq2 W1 W2 m1 m2 (base + i) (P1 i Hi) (P2 i Hi) (E i Hi)).
Qed.

(* addressable (AsanCells) of a range of the hull from range_addressable of the view. *)
Lemma settle_addr_G : forall (W : world segs) mem p n,
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n ->
  TG.G_HARNESS_LO <= p -> 0 <= n -> p + n <= TG.G_HARNESS_HI ->
  ACells.addressable mem p n.
Proof.
  intros W mem p n HRA H1 H2 H3.
  apply (decode_leafb_addressable W mem p n HRA);
    [unfold TG.G_HARNESS_LO in H1; lia | lia | unfold TG.G_HARNESS_HI, ACells.APPMEM_END in *; lia |].
  intros i Hi. unfold ACells.app_mem, ACells.LOWMEM_END, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *. lia.
Qed.

(* The callee-saved registers but sp and s0. *)
Lemma settle_ks_cases : forall r, (r = 3 \/ r = 4 \/ r = 9 \/ (18 <= r <= 27)) ->
  r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
  r = 26 \/ r = 27.
Proof. intros r H. lia. Qed.

Definition settle_ks (regs R : bvmap 5 word) : Prop :=
  forall r, (r = 3 \/ r = 4 \/ r = 9 \/ (18 <= r <= 27)) -> YKK.getr R (Z_to_bv 5 r) = YKK.getr regs (Z_to_bv 5 r).

Lemma settle_ks_pres : forall regs R R', settle_ks regs R -> aregs_preserved R R' -> settle_ks regs R'.
Proof. intros regs R R' K P r Hr. rewrite (P r ltac:(unfold acallee_saved; lia)). exact (K r Hr). Qed.

Lemma settle_ks_end : forall regs R, settle_ks regs R ->
  YKK.getr R (Z_to_bv 5 2) = YKK.getr regs (Z_to_bv 5 2) ->
  YKK.getr R (Z_to_bv 5 8) = YKK.getr regs (Z_to_bv 5 8) ->
  aregs_preserved regs R.
Proof.
  intros regs R K E2 E8 r Hr. unfold acallee_saved in Hr.
  destruct (Z.eq_dec r 2) as [->|N2]; [exact E2|]. destruct (Z.eq_dec r 8) as [->|N8]; [exact E8|].
  apply K. lia.
Qed.

(* settle_ks of a run's state: each register read off the run's map (from the entry map regs, or from a map R0 that
   has settle_ks). *)
Ltac settle_ks_run0 EQV :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr;
  destruct (settle_ks_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]];
  settle_reg EQV.
Ltac settle_ks_run EQV K0 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; rewrite <- (K0 r Hr);
  destruct (settle_ks_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]];
  settle_reg EQV.

Section settle_walk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

(* The configurations at the two donor entries, as the statements read them. *)
Lemma settle_cis_cfg : forall R m md,
  @cfg_at fx segs (transport_sigma TS_check_inflight_settle) R m md =
  mkCfg (@YKK.mkst fx R (Z_to_bv 64 SETTLE_CIS) m (YKK.seg_rom segs)) md.
Proof. reflexivity. Qed.
Lemma settle_clq_cfg : forall R m md,
  @cfg_at fx segs (transport_sigma TS_check_latest_queue) R m md =
  mkCfg (@YKK.mkst fx R (Z_to_bv 64 SETTLE_CLQ) m (YKK.seg_rom segs)) md.
Proof. reflexivity. Qed.

(* A harness global's payload range is addressable at every AR state when the record's zero shadow covers it in whole
   granules. *)
Lemma settle_zra : forall ly S (W : world segs) mem md lo hi p n,
  @AR rc segs B ly S W mem md -> decode_zshadow_at B lo hi -> lo mod 8 = 0 -> hi mod 8 = 0 ->
  lo <= p -> p + n <= hi ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n.
Proof.
  intros ly S W mem md lo hi p n HAR HZ Hlo Hhi H1 H2 x Hx.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. pose proof (Z.div_mod hi 8 ltac:(lia)) as Dh.
  unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
  assert (Hz := decode_zshadow_rd B ly S W mem md lo hi (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* A donor call keeps the world relation: every byte of G is an image byte outside the owned statics and errno. *)
Lemma settle_tw_donor : forall lyc Sc (W1 W2 : world segs) m1 m2 slo shi (E : Z -> Prop) Bw,
  gx_ok segs B TG.G_HARNESS -> gx_noerrno B TG.G_HARNESS ->
  @acall_kept rc segs B lyc Sc W1 m1 W2 m2 slo shi E ->
  tw_at TMAP_A (csw_view m1) Bw -> tw_at TMAP_A (csw_view m2) Bw.
Proof.
  intros lyc Sc W1 W2 m1 m2 slo shi E Bw HOK HNE HK HW.
  apply (settle_tw_csw W2 m2 Bw).
  apply (tw_kept_GA (aview segs (w_H W1) m1) (aview segs (w_H W2) m2) Bw (settle_tw_aview W1 m1 Bw HW)).
  intros b n i Hin Hi.
  pose proof HK as (_ & _ & K3 & _).
  assert (HG : inG TG.G_HARNESS (b + i)).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia. }
  destruct (HOK (b + i) HG) as [Himg Hno].
  exact (K3 (b + i) Himg Hno (HNE (b + i) HG)).
Qed.

(* What the walk keeps between the calls, at the current state (ly2, S2, W2, R, m, md) of the inner journal. *)
Definition settle_inv (regs : bvmap 5 word) (ticked : Z) (Bw : list byte) (lyc : alayout) (Sc : astate)
    (W : world segs) (memc : word -> option byte) (mdc : Model) (ly2 : alayout) (S2 : astate) (W2 : world segs)
    (R : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
  @ajournal rc AE2k.tfib_sink_head segs B SETTLE_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 m md 0 /\
  settle_ks regs R /\
  YKK.getr R (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -16) /\
  YKK.getr R (Z_to_bv 5 8) = Z_to_bv 64 ticked /\
  rw_cells rsegs m (spZ regs + -16) [C8 (YKK.getr regs (Z_to_bv 5 8)); C8 (YKK.getr regs (Z_to_bv 5 1))] /\
  tw_at TMAP_A (csw_view m) Bw.

(* A call of a leaf from settle's frame (sp - 16): the leaf bridge, then settle_inv at the return. *)
Lemma settle_leaf_step : forall regs ticked Bw lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) R m md
    (PC RET : Z) (X : (word -> option byte) -> Prop) (Q : world segs -> config -> Prop),
  AR_laws segs B ->
  YM05.alloc_ceiling + SETTLE_STK <= spZ regs -> spZ regs <= 2 ^ 47 ->
  YKK.getr regs (Z_to_bv 5 3) = w64 (as_gp B) -> YKK.getr regs (Z_to_bv 5 4) = w64 (as_tp B) ->
  settle_inv regs ticked Bw lyc Sc W memc mdc ly2 S2 W2 R m md ->
  YKK.getr R (Z_to_bv 5 1) = Z_to_bv 64 RET -> bv_unsigned (Z_to_bv 64 RET) mod 2 = 0 ->
  (decode_leafb_ecall_pre B ly2 S2 W2 R m md ->
     SRr segs W2 (@LCK.cfg_at fx PC R m md) (decode_leafb_post B ly2 S2 W2 R m md None [] X)) ->
  (forall R' m' md', settle_inv regs ticked Bw lyc Sc W memc mdc ly2 S2 W2 R' m' md' ->
     SRr segs W2 (@cfg_at fx segs RET R' m' md') Q) ->
  SRr segs W2 (mkCfg (@YKK.mkst fx R (Z_to_bv 64 PC) m (YKK.seg_rom segs)) md) Q.
Proof.
  intros regs ticked Bw lyc Sc W memc mdc ly2 S2 W2 R m md PC RET X Q LAWS HSPLO HSPHI Hgp Htp
    (IJ & KS & SPw & S0w & FR & HW) G1 HRETe LEAF K.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  assert (HSTKv : SETTLE_STK = 8288) by reflexivity.
  assert (GSP : spZ R = spZ regs - 16).
  { change (spZ R) with (bv_unsigned (YKK.getr R (Z_to_bv 5 2))). rewrite SPw, unsigned_lit by lia. lia. }
  eapply SRr_bind.
  { apply (@decode_leafb_journal fx rc AE2k.tfib_sink_head B LAWS W2 R m SETTLE_STK (spZ regs) []
             lyc Sc W memc mdc [] ly2 S2 md 0 (-16) PC None [] X IJ).
    - rewrite GSP. lia.
    - reflexivity.
    - lia.
    - settle_closed.
    - change (YK0s.ret_ok (YKK.getr R (Z_to_bv 5 1))). rewrite G1. apply YK0s.ret_ok_even. exact HRETe.
    - change (YKK.getr R (Z_to_bv 5 3) = w64 (as_gp B)). rewrite (KS 3 ltac:(lia)). exact Hgp.
    - change (YKK.getr R (Z_to_bv 5 4) = w64 (as_tp B)). rewrite (KS 4 ltac:(lia)). exact Htp.
    - intros a Ha. unfold LCK.in_wr in Ha. inversion Ha.
    - exact LEAF. }
  cbv beta. intros W3 c3 _ (-> & R' & m' & md' & Hc & IJ' & HPRES & _ & HEFF & _ & _).
  change (YKK.getr R 1) with (YKK.getr R (Z_to_bv 5 1)) in Hc. rewrite G1 in Hc. subst c3.
  pose proof IJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  pose proof IJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  apply K.
  split; [exact IJ'|].
  split; [exact (settle_ks_pres regs R R' KS HPRES)|].
  split; [rewrite (HPRES 2 ltac:(unfold acallee_saved; lia)); exact SPw|].
  split; [rewrite (HPRES 8 ltac:(unfold acallee_saved; lia)); exact S0w|].
  split.
  { apply (settle_frame_keep W2 W2 m m' (spZ regs + -16)).
    - intros i Hi. apply Hpres1. rewrite HSTKv. lia.
    - intros i Hi. apply Hpres2. rewrite HSTKv. lia.
    - intros i Hi. apply HEFF; [lia | rewrite GSP; lia | intros Hx; unfold LCK.in_wr in Hx; inversion Hx].
    - exact FR. }
  apply (settle_tw_keep W2 W2 m m' Bw HW). intros x Hx.
  apply HEFF; [unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hx; lia
              | rewrite GSP; unfold TG.G_HARNESS_HI in Hx; try unfold ESTACK; try unfold LCK.ESTACK; lia |].
  intros Hy. unfold LCK.in_wr in Hy. inversion Hy.
Qed.

(* A call at PC that changes ra only (settle_jal2_F .. settle_jal4_F): settle_inv at the callee's entry. *)
Lemma settle_jal_step : forall regs ticked Bw lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) R m md
    (PC RET TGT : Z) (Q : world segs -> config -> Prop),
  AR_laws segs B ->
  (forall (RNG : ExecF.footprint)
          (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
     ExecF.evtF rsegs RNG
       (fun ms' => ms' = MS (mkR (Z_to_bv 64 RET) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 TGT) fc None m (seg_rom rsegs))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 PC) fc None m (seg_rom rsegs))) ->
  settle_inv regs ticked Bw lyc Sc W memc mdc ly2 S2 W2 R m md ->
  (forall R' md', settle_inv regs ticked Bw lyc Sc W memc mdc ly2 S2 W2 R' m md' ->
     YKK.getr R' (Z_to_bv 5 1) = Z_to_bv 64 RET ->
     SRr segs W2 (mkCfg (@YKK.mkst fx R' (Z_to_bv 64 TGT) m (YKK.seg_rom segs)) md') Q) ->
  SRr segs W2 (@cfg_at fx segs PC R m md) Q.
Proof.
  intros regs ticked Bw lyc Sc W memc mdc ly2 S2 W2 R m md PC RET TGT Q LAWS JAL
    (IJ & KS & SPw & S0w & FR & HW) K.
  eapply (@decode_run fx W2 R m md PC).
  { unfold LCK.ms_of_regs. apply JAL. }
  intros ms' md' (ms0 & Hms0 & EQV) SBM.
  cbv beta in Hms0. subst ms0.
  rewrite (decode_ms_shape _ _ _ _ EQV).
  apply K.
  - split.
    { apply (@ajournal_exec rc AE2k.tfib_sink_head segs B LAWS decode_segs_low SETTLE_STK (spZ regs) []
               lyc Sc W memc mdc [] ly2 S2 W2 m md 0 m md' (fun _ => False) IJ);
        [ intros x _; reflexivity | apply YK1b.mem_grows_refl | intros x _; reflexivity | exact SBM
        | intros a Ha; destruct Ha ]. }
    split; [settle_ks_run EQV KS|].
    split; [transitivity (YKK.getr R (Z_to_bv 5 2)); [settle_reg EQV | exact SPw]|].
    split; [transitivity (YKK.getr R (Z_to_bv 5 8)); [settle_reg EQV | exact S0w]|].
    split; [exact FR | exact HW].
  - settle_reg EQV.
Qed.

(* What a donor call leaves, read back as settle_inv at the return, with the blocks and the meter of its post. *)
Lemma settle_donor_post : forall regs ticked Bw lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) R m md
    (FSTK : Z) (X : bvmap 5 word -> world segs -> (word -> option byte) -> Prop) (W3 : world segs) (c3 : config),
  gx_ok segs B TG.G_HARNESS -> gx_noerrno B TG.G_HARNESS ->
  YM05.alloc_ceiling + SETTLE_STK <= spZ regs -> spZ regs <= 2 ^ 47 ->
  settle_inv regs ticked Bw lyc Sc W memc mdc ly2 S2 W2 R m md ->
  @decode_cg_post fx rc B MT SETTLE_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 m 0 R FSTK 0 0
    (fun _ => False) X W3 c3 ->
  exists ly3 S3 R' m' md',
    c3 = mkCfg (@YKK.mkst fx R' (YKK.getr R (Z_to_bv 5 1)) m' (YKK.seg_rom segs)) md' /\
    settle_inv regs ticked Bw lyc Sc W memc mdc ly3 S3 W3 R' m' md' /\
    Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) /\ mo_le MT S2 S3 0.
Proof.
  intros regs ticked Bw lyc Sc W memc mdc ly2 S2 W2 R m md FSTK X W3 c3 HOK HNE HSPLO HSPHI
    (IJ & KS & SPw & S0w & FR & HW)
    (ly3 & S3 & R' & m' & md' & e & Hc & He & IJ' & HPRES & _ & Hperm & HK & HMO & _).
  assert (Ee : e = 0) by lia. subst e.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  assert (HSTKv : SETTLE_STK = 8288) by reflexivity.
  assert (GSP : spZ R = spZ regs - 16).
  { change (spZ R) with (bv_unsigned (YKK.getr R (Z_to_bv 5 2))). rewrite SPw, unsigned_lit by lia. lia. }
  pose proof IJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  pose proof IJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  pose proof HK as (K1 & _).
  exists ly3, S3, R', m', md'.
  split; [exact Hc|].
  split.
  { split; [exact IJ'|].
    split; [exact (settle_ks_pres regs R R' KS HPRES)|].
    split; [rewrite (HPRES 2 ltac:(unfold acallee_saved; lia)); exact SPw|].
    split; [rewrite (HPRES 8 ltac:(unfold acallee_saved; lia)); exact S0w|].
    split.
    { apply (settle_frame_keep W2 W3 m m' (spZ regs + -16)).
      - intros i Hi. apply Hpres1. rewrite HSTKv. lia.
      - intros i Hi. apply Hpres2. rewrite HSTKv. lia.
      - intros i Hi. apply K1; [lia | rewrite GSP; lia].
      - exact FR. }
    exact (settle_tw_donor ly2 S2 W2 W3 m m' _ _ _ Bw HOK HNE HK HW). }
  split; [exact Hperm | exact HMO].
Qed.

Theorem transport_settle_cg_holds : @transport_settle_cg_holds_stmt fx rc B MT.
Proof.
  intros HCELLS HZS LAWS MTL HGOK HGNE LAS LSS LCIS LKS LCLQ LLD.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ticked Bw Bw'
    HJ Hra Hra4 Hgp Htp Ha0 Htk Hal Hwlo Hwhi HW HM HQ HNEV.
  destruct HZS as (ZGOT & ZOW & ZQ & ZCMD).
  (* the model *)
  destruct (settle_model Bw Bw' ticked HM) as (MAS & MSS & MIS & MKS & MREST). clear HM.
  (* the journal *)
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
    Hstatic & F5 & HQT).
  pose proof Hstatic as (H16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  assert (HSTKv : SETTLE_STK = 8288) by reflexivity.
  assert (HSPLO : YM05.alloc_ceiling + SETTLE_STK <= spZ regs) by lia.
  assert (HSPHI : spZ regs <= 2 ^ 47) by lia.
  assert (HNEV0 : st_nev Sc + 0 + 0 <= EV_MAX) by (unfold SETTLE_EV in HNEV; lia).
  (* the inner journal at the entry *)
  assert (JI0 : @ajournal rc AE2k.tfib_sink_head segs B SETTLE_STK (spZ regs) [] lyc Sc W memc mdc []
                  lyc Sc W memc mdc 0).
  { apply (@ajournal_sub_init rc AE2k.tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
             mdc k SETTLE_STK (spZ regs) [] (spZ regs - sp0) HJ ltac:(lia)
             ltac:(rewrite Zminus_mod, Hal, H16; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)). }
  pose proof JI0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
  (* the world at the raw memory *)
  pose proof (settle_tw_csw W memc Bw HW) as HWc.
  (* the post at a return, from the inner journal there *)
  assert (FIN : forall ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word),
    @ajournal rc AE2k.tfib_sink_head segs B SETTLE_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 0 ->
    aregs_preserved regs regs2 ->
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
    mo_le MT Sc S2 0 ->
    Bw' = Bw ->
    @transport_settle_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' W2
      (mkCfg (@YKK.mkst fx regs2 (YKK.getr regs (Z_to_bv 5 1)) mem2 (YKK.seg_rom segs)) md2)).
  { intros ly2 S2 W2 mem2 md2 regs2 IJ KP PERM MO EB.
    unfold transport_settle_post, decode_cg_post.
    exists ly2, S2, regs2, mem2, md2, 0.
    split; [reflexivity|].
    split; [unfold SETTLE_EV; lia|].
    split.
    { change own with ([] ++ own).
      apply (ajournal_sub segs B LAWS decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
               SETTLE_STK (spZ regs) [] [] ly2 S2 W2 mem2 md2 0 HJ IJ ltac:(lia) ltac:(lia)).
      intros a (r & Hr & _). destruct Hr. }
    split; [exact KP|].
    split; [pose proof IJ as (_ & _ & _ & _ & _ & Hfr2 & _); exact Hfr2|].
    split; [exact PERM|].
    split.
    { apply (acall_kept_of_journal segs B decode_segs_low SETTLE_STK (spZ regs) [] [] lyc Sc W memc mdc
               ly2 S2 W2 mem2 md2 0 (fun _ => False) IJ HAR).
      - intros a (r & Hr & _). destruct Hr.
      - intros b m i Hb _ _. eapply Permutation_in; [apply Permutation_sym; exact PERM | exact Hb].
      - exact sink_closed_nil. }
    split; [exact MO|].
    exact EB. }
  (* ---- run 1: from the entry to the call of check_ack_settle ---- *)
  rewrite settle_entry_at.
  eapply (@decode_run fx W regs memc mdc SETTLE_ENTRY).
  { unfold LCK.ms_of_regs.
    eapply settle_run1_F with (lo := spZ regs - SETTLE_STK);
      try change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs).
    - exact HWc.
    - apply (decode_leafb_stk W memc (spZ regs - SETTLE_STK) (spZ regs)); [lia | lia |].
      intros a Ha. apply Hpres0. lia.
    - lia.
    - unfold TG.G_HARNESS_HI. lia.
    - apply (decode_rng W); [lia | lia |].
      intros b Hb. destruct (Hpres0 b ltac:(lia)) as [Hh _]. exact Hh. }
  intros msA mdA (ms0 & HP & EQVA) SBMA.
  destruct HP as (s0' & m1 & Hms0 & Es0 & MU & WM & FR & HW1).
  subst ms0 s0'.
  rewrite (decode_ms_shape _ _ _ _ EQVA).
  change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs) in MU, FR.
  (* the inner journal after the two saves *)
  assert (MUw : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) ->
            mrestrict (w_H W) m1 x = mrestrict (w_H W) memc x).
  { intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside].
    split; [lia | exact I]. }
  assert (MGw : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) m1)).
  { intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 16)) as [Hl|Hl];
      [rewrite (MU x); [exact Hx | cbn [outside]; split; [unfold spZ in *; lia | exact I]]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|rewrite (MU x); [exact Hx | cbn [outside]; split; [unfold spZ in *; lia | exact I]]].
    assert (Hw : wview rsegs m1 x <> None).
    { refine (WM x _). unfold wview. destruct (memc x) as [b|] eqn:Em;
        [discriminate | exfalso; first [exact (Hx Em) | exact (Hx eq_refl)]]. }
    unfold wview in Hw. destruct (m1 x) as [b|] eqn:Em1; [discriminate|]. exfalso.
    rewrite (find_segment_none rsegs (bv_unsigned x)) in Hw; [exact (Hw eq_refl)|].
    intros Him. pose proof (decode_segs_low _ Him) as Hlow. unfold kLowMemEnd in Hlow. lia. }
  assert (MHw : forall x : word, w_H W x = true -> m1 x = memc x).
  { intros x Hx.
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 16)) as [Hl|Hl];
      [apply (MU x); cbn [outside]; split; [unfold spZ in *; lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|apply (MU x); cbn [outside]; split; [unfold spZ in *; lia | exact I]].
    exfalso.
    pose proof (proj1 (Hpres0 (bv_unsigned x) ltac:(lia))) as Hhx.
    rewrite Z_to_bv_bv_unsigned in Hhx. congruence. }
  assert (IJ1 : @ajournal rc AE2k.tfib_sink_head segs B SETTLE_STK (spZ regs) [] lyc Sc W memc mdc []
                  lyc Sc W m1 mdA 0).
  { apply (@ajournal_exec rc AE2k.tfib_sink_head segs B LAWS decode_segs_low SETTLE_STK (spZ regs) []
             lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m1 mdA
             (fun a => spZ regs - 16 <= a < spZ regs) JI0 MUw MGw MHw SBMA).
    intros a Ha. left. lia. }
  assert (INV1 : settle_inv regs ticked Bw lyc Sc W memc mdc lyc Sc W (ms_regs msA) m1 mdA).
  { split; [exact IJ1|].
    split; [settle_ks_run0 EQVA|].
    split; [settle_reg EQVA|].
    split; [transitivity (YKK.getr regs (Z_to_bv 5 10)); [settle_reg EQVA | exact Ha0]|].
    split; [exact FR | exact HW1]. }
  assert (GA1 : YKK.getr (ms_regs msA) (Z_to_bv 5 1) = Z_to_bv 64 SETTLE_R1) by settle_reg EQVA.
  clear MUw MGw MHw MU WM EQVA.
  (* ---- the call of check_ack_settle ---- *)
  pose proof INV1 as (IJa & KSa & SPa & S0a & FRa & HWa).
  pose proof IJa as (HARa & _).
  apply (settle_leaf_step regs ticked Bw lyc Sc W memc mdc lyc Sc W (ms_regs msA) m1 mdA
           LASc.CHECK_ACK_SETTLE SETTLE_R1 (fun _ => Bw = Bw) _ LAWS HSPLO HSPHI Hgp Htp INV1 GA1
           ltac:(settle_closed)).
  { intros HPRE.
    pose proof (LAS fx) as LF.
    unfold transport_leaf_at, LAS.transport_check_ack_settle_cg in LF.
    specialize (LF lyc Sc W (ms_regs msA) m1 mdA (spZ regs - SETTLE_STK) Bw Bw HPRE).
    cbv zeta in LF.
    apply LF; clear LF.
    - exact HWa.
    - exact MAS.
    - rewrite SPa, unsigned_lit by lia.
      apply (decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJa); lia.
    - rewrite SPa, unsigned_lit by lia. unfold LASc.CHECK_ACK_SETTLE_FRAME. lia.
    - unfold AKA.off_stk. rewrite SPa, unsigned_lit by lia.
      unfold LASc.CHECK_ACK_SETTLE_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
    - rewrite SPa, unsigned_lit by lia.
      apply (decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJa);
        unfold LASc.CHECK_ACK_SETTLE_FRAME; lia.
    - apply settle_rng_hull; settle_closed.
    - apply settle_rng_hull; settle_closed. }
  intros R1 m2 md2 INV2.
  clear IJa KSa SPa S0a FRa HWa HARa.
  (* ---- the call at 0x83cc0 of check_state_settle ---- *)
  apply (settle_jal_step regs ticked Bw lyc Sc W memc mdc lyc Sc W R1 m2 md2 SETTLE_R1 SETTLE_R2 SETTLE_CSS _
           LAWS settle_jal2_F INV2).
  intros R2 md3 INV3 GB1.
  pose proof INV3 as (IJb & KSb & SPb & S0b & FRb & HWb).
  pose proof IJb as (HARb & _).
  apply (settle_leaf_step regs ticked Bw lyc Sc W memc mdc lyc Sc W R2 m2 md3
           LSSc.CHECK_STATE_SETTLE SETTLE_R2 (fun _ => Bw = Bw) _ LAWS HSPLO HSPHI Hgp Htp INV3 GB1
           ltac:(settle_closed)).
  { intros HPRE.
    pose proof (LSS fx) as LF.
    unfold transport_leaf_at, LSS.transport_check_state_settle_cg in LF.
    specialize (LF lyc Sc W R2 m2 md3 (spZ regs - SETTLE_STK) Bw Bw HPRE).
    cbv zeta in LF.
    assert (RAG : range_addressable (aview segs (w_H W) m2) SHADOW_OFF
                    LSSc.CHECK_STATE_SETTLE_GOT_T LSSc.CHECK_STATE_SETTLE_T_LEN).
    { apply (settle_zra lyc Sc W m2 md3 TA_GOT (TA_GOT + TW.SZ_GOT) _ _ HARb ZGOT); settle_closed. }
    assert (RAO : range_addressable (aview segs (w_H W) m2) SHADOW_OFF
                    LSSc.CHECK_STATE_SETTLE_OW_T LSSc.CHECK_STATE_SETTLE_T_LEN).
    { apply (settle_zra lyc Sc W m2 md3 TA_OW (TA_OW + TW.SZ_OW) _ _ HARb ZOW); settle_closed. }
    apply LF; clear LF.
    - exact HWb.
    - exact MSS.
    - rewrite SPb, unsigned_lit by lia.
      apply (decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJb); lia.
    - rewrite SPb, unsigned_lit by lia. unfold LSSc.CHECK_STATE_SETTLE_FRAME. lia.
    - unfold AKA.off_stk. rewrite SPb, unsigned_lit by lia.
      unfold LSSc.CHECK_STATE_SETTLE_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
    - rewrite SPb, unsigned_lit by lia. apply (@decode_leafb_app_stack rc).
      unfold LSSc.CHECK_STATE_SETTLE_FRAME. lia.
    - rewrite SPb, unsigned_lit by lia. apply (@decode_leafb_app_stack rc). lia.
    - exact (decode_leafb_asan_cells B HCELLS lyc Sc W m2 md3 HARb).
    - unfold AKA.off_stk. rewrite SPb, unsigned_lit by lia.
      unfold LSSc.CHECK_STATE_SETTLE_FRAME, GOT_CELL_K. lia.
    - unfold AKA.off_stk. rewrite SPb, unsigned_lit by lia.
      unfold LSSc.CHECK_STATE_SETTLE_FRAME, CELL_K. lia.
    - apply (settle_addr_G W m2 _ _ RAG); settle_closed.
    - apply (settle_addr_G W m2 _ _ RAO); settle_closed.
    - rewrite SPb, unsigned_lit by lia.
      apply (decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJb);
        unfold LSSc.CHECK_STATE_SETTLE_FRAME; lia.
    - exact (proj1 (decode_leafb_rng_cells W)).
    - exact (proj2 (decode_leafb_rng_cells W)).
    - apply settle_rng_hull; settle_closed.
    - apply settle_rng_hull; settle_closed.
    - apply settle_rng_hull; settle_closed.
    - apply settle_rng_hull; settle_closed.
    - apply (decode_leafb_rng_shadow W m2 _ _ RAG); settle_closed.
    - apply (decode_leafb_rng_shadow W m2 _ _ RAO); settle_closed. }
  intros R3 m3 md4 INV4.
  clear IJb KSb SPb S0b FRb HWb HARb.
  (* ---- the call at 0x83cc4 of check_inflight_settle (donor) ---- *)
  apply (settle_jal_step regs ticked Bw lyc Sc W memc mdc lyc Sc W R3 m3 md4 SETTLE_R2 SETTLE_R3 SETTLE_CIS _
           LAWS settle_jal3_F INV4).
  intros R4 md5 INV5 GC1.
  pose proof INV5 as (IJc & KSc & SPc & S0c & FRc & HWc5).
  assert (GSPc : spZ R4 = spZ regs - 16).
  { change (spZ R4) with (bv_unsigned (YKK.getr R4 (Z_to_bv 5 2))). rewrite SPc, unsigned_lit by lia. lia. }
  rewrite <- settle_cis_cfg.
  eapply SRr_bind.
  { apply (LCIS fx SETTLE_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W m3 md5 0 R4 Bw Bw IJc).
    - change (YK0s.ret_ok (YKK.getr R4 (Z_to_bv 5 1))). rewrite GC1. apply YK0s.ret_ok_even. settle_closed.
    - change (4096 <= bv_unsigned (YKK.getr R4 (Z_to_bv 5 1))). rewrite GC1. settle_closed.
    - change (YKK.getr R4 (Z_to_bv 5 3) = w64 (as_gp B)). rewrite (KSc 3 ltac:(lia)). exact Hgp.
    - change (YKK.getr R4 (Z_to_bv 5 4) = w64 (as_tp B)). rewrite (KSc 4 ltac:(lia)). exact Htp.
    - rewrite GSPc, Zminus_mod, Hal. reflexivity.
    - rewrite GSPc, HSTKv. assert (ECIS : CIS_STK = 4128) by reflexivity. rewrite ECIS. lia.
    - rewrite GSPc. lia.
    - exact (settle_tw_aview W m3 Bw HWc5).
    - exact MIS.
    - unfold CIS_EV. exact HNEV0. }
  intros W4 c4 _ HPOST.
  destruct (settle_donor_post regs ticked Bw lyc Sc W memc mdc lyc Sc W R4 m3 md5 CIS_STK _ W4 c4
              HGOK HGNE HSPLO HSPHI INV5 HPOST) as (ly4 & S4 & R5 & m4 & md6 & Hc4 & INV6 & PERM4 & MO4).
  subst c4. rewrite GC1.
  clear IJc KSc SPc S0c FRc HWc5 GSPc HPOST.
  (* ---- the call at 0x83cc8 of check_keepalive_settle ---- *)
  apply (settle_jal_step regs ticked Bw lyc Sc W memc mdc ly4 S4 W4 R5 m4 md6 SETTLE_R3 SETTLE_R4 SETTLE_CKS _
           LAWS settle_jal4_F INV6).
  intros R6 md7 INV7 GD1.
  pose proof INV7 as (IJd & KSd & SPd & S0d & FRd & HWd).
  apply (settle_leaf_step regs ticked Bw lyc Sc W memc mdc ly4 S4 W4 R6 m4 md7
           LKSc.CHECK_KEEPALIVE_SETTLE SETTLE_R4 (fun _ => Bw = Bw) _ LAWS HSPLO HSPHI Hgp Htp INV7 GD1
           ltac:(settle_closed)).
  { intros HPRE.
    pose proof (LKS fx) as LF.
    unfold transport_leaf_at, LKS.transport_check_keepalive_settle_cg in LF.
    specialize (LF ly4 S4 W4 R6 m4 md7 (spZ regs - SETTLE_STK) Bw Bw HPRE).
    cbv zeta in LF.
    apply LF; clear LF.
    - exact HWd.
    - exact MKS.
    - rewrite SPd, unsigned_lit by lia.
      apply (decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJd); lia.
    - rewrite SPd, unsigned_lit by lia. unfold LKSc.CHECK_KEEPALIVE_SETTLE_FRAME. lia.
    - unfold AKA.off_stk. rewrite SPd, unsigned_lit by lia.
      unfold LKSc.CHECK_KEEPALIVE_SETTLE_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
    - rewrite SPd, unsigned_lit by lia.
      apply (decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJd);
        unfold LKSc.CHECK_KEEPALIVE_SETTLE_FRAME; lia.
    - apply settle_rng_hull; settle_closed.
    - apply settle_rng_hull; settle_closed.
    - apply settle_rng_hull; settle_closed.
    - apply settle_rng_hull; settle_closed.
    - apply settle_rng_hull; settle_closed.
    - apply settle_rng_hull; settle_closed. }
  intros R7 m5 md8 INV8.
  clear IJd KSd SPd S0d FRd HWd.
  (* ---- run 5 at 0x83ccc: g_raw, then the return or the call of check_latest_queue ---- *)
  pose proof INV8 as (IJe & KSe & SPe & S0e & FRe & HWe).
  pose proof IJe as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hprese & _).
  eapply (@decode_run fx W4 R7 m5 md8 SETTLE_R4).
  { unfold LCK.ms_of_regs.
    eapply settle_run5_F with (vra := YKK.getr regs (Z_to_bv 5 1)) (vs0 := YKK.getr regs (Z_to_bv 5 8)).
    - exact HWe.
    - rewrite SPe, unsigned_lit by lia. lia.
    - rewrite SPe, unsigned_lit by lia. lia.
    - rewrite SPe, unsigned_lit by lia. exact FRe.
    - rewrite SPe, unsigned_lit by lia. apply (decode_rng W4); [lia | lia |].
      intros b Hb. destruct (Hprese b ltac:(rewrite HSTKv; lia)) as [Hh _]. exact Hh.
    - apply settle_rng_hull; settle_closed. }
  intros msB mdB (ms1 & HP & EQVB) SBMB.
  assert (IJe' : @ajournal rc AE2k.tfib_sink_head segs B SETTLE_STK (spZ regs) [] lyc Sc W memc mdc []
                   ly4 S4 W4 m5 mdB 0).
  { apply (@ajournal_exec rc AE2k.tfib_sink_head segs B LAWS decode_segs_low SETTLE_STK (spZ regs) []
             lyc Sc W memc mdc [] ly4 S4 W4 m5 md8 0 m5 mdB (fun _ => False) IJe);
      [ intros x _; reflexivity | apply YK1b.mem_grows_refl | intros x _; reflexivity | exact SBMB
      | intros a Ha; destruct Ha ]. }
  destruct HP as [(G0 & a0' & Hms1) | (G0 & a0' & Hms1)]; subst ms1.
  { (* g_raw <> 0: the return *)
    rewrite (decode_ms_shape _ _ _ _ EQVB).
    apply SRr_ret.
    destruct MREST as [(_ & EB) | (G0' & _)]; [|contradiction].
    rewrite (ret_ok_stmt_YK0s (YKK.getr regs (Z_to_bv 5 1)) Hra).
    refine (FIN ly4 S4 W4 m5 mdB (ms_regs msB) IJe' _ PERM4 MO4 EB).
    apply settle_ks_end.
    - settle_ks_run EQVB KSe.
    - transitivity (Z_to_bv 64 (bv_unsigned (YKK.getr R7 (Z_to_bv 5 2)) + 16)); [settle_reg EQVB|].
      rewrite SPe, unsigned_lit by lia. replace (spZ regs + -16 + 16) with (spZ regs) by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - settle_reg EQVB. }
  (* g_raw = 0: the call of check_latest_queue (donor) *)
  rewrite (decode_ms_shape _ _ _ _ EQVB).
  destruct MREST as [(G0' & _) | (_ & MLQ & MTK)]; [contradiction|].
  assert (INV9 : settle_inv regs ticked Bw lyc Sc W memc mdc ly4 S4 W4 (ms_regs msB) m5 mdB).
  { split; [exact IJe'|].
    split; [settle_ks_run EQVB KSe|].
    split; [transitivity (YKK.getr R7 (Z_to_bv 5 2)); [settle_reg EQVB | exact SPe]|].
    split; [transitivity (YKK.getr R7 (Z_to_bv 5 8)); [settle_reg EQVB | exact S0e]|].
    split; [exact FRe | exact HWe]. }
  assert (GE1 : YKK.getr (ms_regs msB) (Z_to_bv 5 1) = Z_to_bv 64 SETTLE_R5) by settle_reg EQVB.
  clear IJe KSe SPe S0e FRe HWe Hprese IJe' EQVB.
  pose proof INV9 as (IJf & KSf & SPf & S0f & FRf & HWf).
  assert (GSPf : spZ (ms_regs msB) = spZ regs - 16).
  { change (spZ (ms_regs msB)) with (bv_unsigned (YKK.getr (ms_regs msB) (Z_to_bv 5 2))).
    rewrite SPf, unsigned_lit by lia. lia. }
  rewrite <- settle_clq_cfg.
  eapply SRr_bind.
  { apply (LCLQ fx SETTLE_STK (spZ regs) [] lyc Sc W memc mdc [] ly4 S4 W4 m5 mdB 0 (ms_regs msB) Bw Bw IJf).
    - change (YK0s.ret_ok (YKK.getr (ms_regs msB) (Z_to_bv 5 1))). rewrite GE1. apply YK0s.ret_ok_even.
      settle_closed.
    - change (4096 <= bv_unsigned (YKK.getr (ms_regs msB) (Z_to_bv 5 1))). rewrite GE1. settle_closed.
    - change (YKK.getr (ms_regs msB) (Z_to_bv 5 3) = w64 (as_gp B)). rewrite (KSf 3 ltac:(lia)). exact Hgp.
    - change (YKK.getr (ms_regs msB) (Z_to_bv 5 4) = w64 (as_tp B)). rewrite (KSf 4 ltac:(lia)). exact Htp.
    - rewrite GSPf, Zminus_mod, Hal. reflexivity.
    - rewrite GSPf, HSTKv. assert (ECLQ : CLQ_STK = 8272) by reflexivity. rewrite ECLQ. lia.
    - rewrite GSPf. lia.
    - exact (settle_tw_aview W4 m5 Bw HWf).
    - exact MLQ.
    - exact HQ.
    - unfold CLQ_EV. exact HNEV0. }
  intros W6 c6 _ HPOST.
  destruct (settle_donor_post regs ticked Bw lyc Sc W memc mdc ly4 S4 W4 (ms_regs msB) m5 mdB CLQ_STK _ W6 c6
              HGOK HGNE HSPLO HSPHI INV9 HPOST) as (ly6 & S6 & R8 & m6 & md9 & Hc6 & INV10 & PERM6 & MO6).
  subst c6. rewrite GE1.
  clear IJf KSf SPf S0f FRf HWf GSPf HPOST.
  assert (PERM : Permutation (ablocks B ly6 S6) (ablocks B lyc Sc))
    by (eapply Permutation_trans; [exact PERM6 | exact PERM4]).
  assert (MO : mo_le MT Sc S6 0) by exact (mle_station MT Sc S4 S6 0 0 MTL MO4 MO6).
  (* ---- run 6 at 0x83cec: s0 = ticked, then the return or the tail jump to check_latest_drain ---- *)
  pose proof INV10 as (IJg & KSg & SPg & S0g & FRg & HWg).
  pose proof IJg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresg & _).
  eapply (@decode_run fx W6 R8 m6 md9 SETTLE_R5).
  { unfold LCK.ms_of_regs. rewrite S0g.
    eapply settle_run6_F with (vra := YKK.getr regs (Z_to_bv 5 1)) (vs0 := YKK.getr regs (Z_to_bv 5 8)).
    - exact Htk.
    - rewrite SPg, unsigned_lit by lia. lia.
    - rewrite SPg, unsigned_lit by lia. lia.
    - rewrite SPg, unsigned_lit by lia. exact FRg.
    - rewrite SPg, unsigned_lit by lia. apply (decode_rng W6); [lia | lia |].
      intros b Hb. destruct (Hpresg b ltac:(rewrite HSTKv; lia)) as [Hh _]. exact Hh. }
  intros msC mdC (ms2 & HP & EQVC) SBMC.
  assert (IJg' : @ajournal rc AE2k.tfib_sink_head segs B SETTLE_STK (spZ regs) [] lyc Sc W memc mdc []
                   ly6 S6 W6 m6 mdC 0).
  { apply (@ajournal_exec rc AE2k.tfib_sink_head segs B LAWS decode_segs_low SETTLE_STK (spZ regs) []
             lyc Sc W memc mdc [] ly6 S6 W6 m6 md9 0 m6 mdC (fun _ => False) IJg);
      [ intros x _; reflexivity | apply YK1b.mem_grows_refl | intros x _; reflexivity | exact SBMC
      | intros a Ha; destruct Ha ]. }
  (* the registers both exits share: ra, sp and s0 of the entry, the other callee-saved ones kept *)
  assert (KST : settle_ks regs (ms_regs msC)).
  { destruct HP as [(_ & Hms2) | (_ & Hms2)]; subst ms2; settle_ks_run EQVC KSg. }
  assert (GT1 : YKK.getr (ms_regs msC) (Z_to_bv 5 1) = YKK.getr regs (Z_to_bv 5 1)).
  { destruct HP as [(_ & Hms2) | (_ & Hms2)]; subst ms2; settle_reg EQVC. }
  assert (GT2 : YKK.getr (ms_regs msC) (Z_to_bv 5 2) = YKK.getr regs (Z_to_bv 5 2)).
  { transitivity (Z_to_bv 64 (bv_unsigned (YKK.getr R8 (Z_to_bv 5 2)) + 16));
      [destruct HP as [(_ & Hms2) | (_ & Hms2)]; subst ms2; settle_reg EQVC|].
    rewrite SPg, unsigned_lit by lia. replace (spZ regs + -16 + 16) with (spZ regs) by lia.
    unfold spZ. apply Z_to_bv_bv_unsigned. }
  assert (GT8 : YKK.getr (ms_regs msC) (Z_to_bv 5 8) = YKK.getr regs (Z_to_bv 5 8)).
  { destruct HP as [(_ & Hms2) | (_ & Hms2)]; subst ms2; settle_reg EQVC. }
  assert (KPT : aregs_preserved regs (ms_regs msC)) by exact (settle_ks_end regs (ms_regs msC) KST GT2 GT8).
  destruct HP as [(K0 & Hms2) | (K0 & Hms2)]; subst ms2.
  { (* ticked = 0: the return *)
    rewrite (decode_ms_shape _ _ _ _ EQVC).
    apply SRr_ret.
    destruct MTK as [(_ & EB) | (K0' & _)]; [|contradiction].
    rewrite (ret_ok_stmt_YK0s (YKK.getr regs (Z_to_bv 5 1)) Hra).
    exact (FIN ly6 S6 W6 m6 mdC (ms_regs msC) IJg' KPT PERM MO EB). }
  (* ticked <> 0: the tail jump to check_latest_drain, from settle's entry sp with settle's ra *)
  rewrite (decode_ms_shape _ _ _ _ EQVC).
  destruct MTK as [(K0' & _) | (_ & MLD & EB)]; [contradiction|].
  clear EQVC.
  set (RT := ms_regs msC) in *.
  pose proof IJg' as (HART & _).
  assert (GTSP : spZ RT = spZ regs).
  { change (spZ RT) with (bv_unsigned (YKK.getr RT (Z_to_bv 5 2))). rewrite GT2. reflexivity. }
  assert (RAQ : range_addressable (aview segs (w_H W6) m6) SHADOW_OFF TA_g_q TW.SZ_g_q).
  { apply (settle_zra ly6 S6 W6 m6 mdC TA_g_q (TA_g_q + TW.SZ_g_q) _ _ HART ZQ); settle_closed. }
  assert (RAC : range_addressable (aview segs (w_H W6) m6) SHADOW_OFF TA_g_cmd TW.SZ_g_cmd).
  { apply (settle_zra ly6 S6 W6 m6 mdC TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd) _ _ HART ZCMD); settle_closed. }
  change (Z_to_bv 64 SETTLE_CLD) with (Z_to_bv 64 LLDc.CHECK_LATEST_DRAIN).
  eapply SRr_mono.
  { apply (@decode_leafb_journal fx rc AE2k.tfib_sink_head B LAWS W6 RT m6 SETTLE_STK (spZ regs) []
             lyc Sc W memc mdc [] ly6 S6 mdC 0 0 LLDc.CHECK_LATEST_DRAIN None [] (fun _ => Bw' = Bw) IJg').
    - rewrite GTSP. lia.
    - reflexivity.
    - lia.
    - settle_closed.
    - change (YK0s.ret_ok (YKK.getr RT (Z_to_bv 5 1))). rewrite GT1. exact Hra.
    - change (YKK.getr RT (Z_to_bv 5 3) = w64 (as_gp B)). rewrite (KST 3 ltac:(lia)). exact Hgp.
    - change (YKK.getr RT (Z_to_bv 5 4) = w64 (as_tp B)). rewrite (KST 4 ltac:(lia)). exact Htp.
    - intros a Ha. unfold LCK.in_wr in Ha. inversion Ha.
    - intros HPRE.
      pose proof (LLD fx) as LF.
      unfold transport_leaf_at, LLD.transport_check_latest_drain_cg in LF.
      specialize (LF ly6 S6 W6 RT m6 mdC (spZ regs - SETTLE_STK) Bw Bw' HPRE).
      cbv zeta in LF.
      rewrite GT2 in LF. change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs) in LF.
      apply LF; clear LF.
      + exact HWg.
      + exact MLD.
      + apply (decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJg'); lia.
      + unfold LLDc.CHECK_LATEST_DRAIN_FRAME. lia.
      + unfold AKA.off_stk. change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs).
        unfold LLDc.CHECK_LATEST_DRAIN_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
      + exact (decode_leafb_asan_cells B HCELLS ly6 S6 W6 m6 mdC HART).
      + apply (@decode_leafb_app_stack rc). unfold LLDc.CHECK_LATEST_DRAIN_FRAME. lia.
      + apply (@decode_leafb_app_stack rc). lia.
      + unfold AKA.off_stk. change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs).
        unfold LLDc.CHECK_LATEST_DRAIN_FRAME, GOT_CELL_K. lia.
      + unfold AKA.off_stk. change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs).
        unfold LLDc.CHECK_LATEST_DRAIN_FRAME, CELL_K. lia.
      + apply (settle_addr_G W6 m6 _ _ RAQ); settle_closed.
      + apply (settle_addr_G W6 m6 _ _ RAC); settle_closed.
      + apply (decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJg');
          unfold LLDc.CHECK_LATEST_DRAIN_FRAME; lia.
      + apply settle_rng_hull; settle_closed.
      + apply settle_rng_hull; settle_closed.
      + apply settle_rng_hull; settle_closed.
      + apply settle_rng_hull; settle_closed.
      + apply settle_rng_hull; settle_closed.
      + exact (proj1 (decode_leafb_rng_cells W6)).
      + exact (proj2 (decode_leafb_rng_cells W6)).
      + exact (decode_leafb_rng_shadow W6 m6 _ _ RAQ ltac:(settle_closed) ltac:(settle_closed) ltac:(settle_closed)).
      + apply settle_rng_hull; settle_closed.
      + exact (decode_leafb_rng_shadow W6 m6 _ _ RAC ltac:(settle_closed) ltac:(settle_closed) ltac:(settle_closed)).
      + apply settle_rng_hull; settle_closed.
      + apply settle_rng_hull; settle_closed.
      + apply settle_rng_hull; settle_closed.
      + apply settle_rng_hull; settle_closed. }
  cbv beta. intros W7 c7 _ (-> & R9 & m7 & md10 & Hc7 & IJh & HPRES & _ & _ & _ & _).
  change (YKK.getr RT 1) with (YKK.getr RT (Z_to_bv 5 1)) in Hc7. rewrite GT1 in Hc7. subst c7.
  refine (FIN ly6 S6 W6 m7 md10 R9 IJh _ PERM MO EB).
  intros r Hr. rewrite (HPRES r Hr). exact (KPT r Hr).
Qed.
End settle_walk.

Print Assumptions transport_settle_cg_holds.
