(* check_inflight_settle_cgW: Theorem transport_check_inflight_settle_cg_holds : the statement
   transport_check_inflight_settle_cg_holds_stmt of lib/B/Prog/check_inflight_settle_cg.v, the image-B caller-journal
   walk of check_inflight_settle (fuzz_transport.asan-ubsan 41113a03c82f, entry 0x85fdc = transportb_sigma
   TB_check_inflight_settle, 200 bytes, frame 32).

   Image A's walk (lib/A/Prog/check_inflight_settle_cgW.v) over image B's kit:
   - an inner journal is started at the entry (lib/Reusable/YCbq.v ajournal_sub_init; stack window
     [spZ regs - CIS_STK, spZ regs), no footprint, no frame of its own);
   - the world relation is read at the raw memory (csw_view): every payload byte of the harness globals lies in a
     loaded segment, so the world hides none of them;
   - the code up to the call runs as the footprint run cis_run1_F (lib/B/Prog/check_inflight_settle_seg_runs.v),
     carried into SRr by lib/B/Prog/TransportFevt.v decode_run; the inner journal is re-established after the four
     saves by YCbq.v ajournal_exec (the written bytes lie in the inner journal's own window);
   - diginet_session_deadline is a leaf: its statement (lib/B/Prog/diginet_session_deadline_cg.v
     transport_diginet_session_deadline_cg, read through DgnTransportBCg.v transport_leaf_at) is applied at the call
     state, and its dleaf_post becomes the inner journal at the return by DgnTransportBLeafb.v decode_leafb_journal.
     Its premises: a0 = &g_s and a1 = g_now (the run's registers), the world relation and the model call
     diginet_session_deadline_m Bw (g_now Bw) = Some d (from the model premise), the ESTACK window below sp - 32 (the
     inner journal), asan_cells (transport_cells), g_s's payload addressable (trans_cis_cells: its zero shadow, read
     through DgnTransportBCg.v decode_zshadow_rd);
   - the leaf keeps every byte outside its stack window, so the frame and the world bytes are the same after it;
   - the code after the call runs as cis_run2_F: every trap test is decided by the model facts, a0 = d is the leaf's
     result; the frame reloads ra, s0, s1, s2. The trap block and the unimp word after it are not reached;
   - the inner journal composes with the caller's by YCbq.v ajournal_sub, the kept bytes come from YCbq.v
     acall_kept_of_journal; no event, no frame, no block, no meter charge (the leaf keeps the allocator state). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Frame Regs6ss ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportFevt DgnTransportBLeafb CgBNoTwin.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_inflight_settle_cg
  check_inflight_settle_seg_runs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit AsanKA diginet_session_deadline_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_session_deadline_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require check_inflight_settle_seg_runs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module LSDc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_deadline_c.
Module CISA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_inflight_settle_seg_runs.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Local Abbreviation segs := tfibsegs.

(* A register of a state reached by a run, read off the run's register map (TransportFevt.v decode_getr_xeqv, then
   the map computed). *)
Ltac cis_reg HX := etransitivity; [apply (decode_getr_xeqv _ _ HX) | reflexivity].

(* The entry, as the listing layer names it. *)
Lemma cis_entry_at : transportb_sigma TB_check_inflight_settle = CIS_ENTRY.
Proof. reflexivity. Qed.

(* Every payload byte of the 18 harness globals lies in a loaded segment of image B, so no world hides it. *)
Lemma cis_hull_vis : forall (W : world segs) x, TG.G_HARNESS_B_LO <= x < TG.G_HARNESS_B_HI ->
  w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx.
  replace x with (TG.G_HARNESS_B_LO + (x - TG.G_HARNESS_B_LO)) by lia.
  apply (decode_covers_visible (w_H W) TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO)
           (x - TG.G_HARNESS_B_LO) (w_Hoff W));
    [vm_compute; reflexivity | unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in *; lia
    | unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia].
Qed.

(* The world relation at the view of a world is the world relation at the raw memory. *)
Lemma cis_tw_csw : forall (W : world segs) mem Bw,
  tw_at TMAP_B (aview segs (w_H W) mem) Bw -> tw_at TMAP_B (csw_view mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept TMAP_B _ _ Bw H). intros x Hx.
  unfold csw_view. rewrite (cgb_aview_mrd (w_H W) mem x (cis_hull_vis W x (TMAP_B_hull x Hx))). reflexivity.
Qed.

(* The world relation after a call that keeps every byte of the hull's view. *)
Lemma cis_tw_kept : forall (W : world segs) mem mem' Bw,
  tw_at TMAP_B (csw_view mem) Bw ->
  (forall x, TG.G_HARNESS_B_LO <= x < TG.G_HARNESS_B_HI -> aview segs (w_H W) mem' x = aview segs (w_H W) mem x) ->
  tw_at TMAP_B (csw_view mem') Bw.
Proof.
  intros W mem mem' Bw H K. apply (tw_kept TMAP_B _ _ Bw H). intros x Hx.
  pose proof (TMAP_B_hull x Hx) as Hh. pose proof (cis_hull_vis W x Hh) as Hv.
  unfold csw_view. rewrite <- (cgb_aview_mrd (w_H W) mem' x Hv), <- (cgb_aview_mrd (w_H W) mem x Hv).
  exact (K x Hh).
Qed.

(* RNG_W W holds on a range of the hull. *)
Lemma cis_rng_hull : forall (W : world segs) lo len, TG.G_HARNESS_B_LO <= lo -> lo + len <= TG.G_HARNESS_B_HI ->
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
  intros W lo len H1 H2.
  apply (decode_leafb_rng W); [unfold TG.G_HARNESS_B_LO in *; lia | unfold TG.G_HARNESS_B_HI in *; lia |].
  intros b Hb. apply cis_hull_vis. lia.
Qed.

Section cis. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

(* g_s's payload is addressable at every AR state: the shadow of its 2283 whole granules is 0. *)
Lemma cis_gs_ra : forall ly S (W : world segs) mem md,
  trans_cis_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF TB_g_s TW.SZ_g_s.
Proof.
  intros ly S W mem md HZ HAR x Hx. unfold TB_g_s, TW.SZ_g_s in Hx.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
  assert (Hz := decode_zshadow_rd B ly S W mem md TB_g_s (TB_g_s + TW.SZ_g_s) (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(unfold TB_g_s; lia) ltac:(unfold TB_g_s, TW.SZ_g_s; lia) HZ).
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Theorem transport_check_inflight_settle_cg_holds : @transport_check_inflight_settle_cg_holds_stmt fx rc B MT.
Proof.
  intros HCELLS HZS LAWS MTL LEAF.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw'
    HJ Hra Hra4 Hgp Htp Hal Hwlo Hwhi HW HM HNEV.
  (* the model *)
  destruct (CISA.cis_model Bw Bw' HM) as (EBw & EA & FLY1 & d & HD & D1 & D2 & FLY2). clear HM.
  unfold TS0.u64, TC.h_ms_m, TS0.u64 in FLY1, D2, FLY2.
  pose proof (CISA.cis_ranges Bw) as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6).
  assert (Rd : 0 <= d < 2 ^ 64).
  { split; [lia|]. pose proof (Z.mod_pos_bound (TW.g_now Bw + 1000000) (2 ^ 64) ltac:(lia)). lia. }
  (* the journal *)
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
    Hstatic & F5 & HQT).
  pose proof Hstatic as (H16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  assert (HSTKv : CIS_STK = 4128) by reflexivity.
  assert (HSPLO : YM05.alloc_ceiling + CIS_STK <= spZ regs) by lia.
  assert (HSPHI : spZ regs <= 2 ^ 47) by lia.
  (* the inner journal at the entry *)
  assert (JI0 : @ajournal rc YE2k.tfib_sink_head segs B CIS_STK (spZ regs) [] lyc Sc W memc mdc []
                  lyc Sc W memc mdc 0).
  { apply (@ajournal_sub_init rc YE2k.tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
             mdc k CIS_STK (spZ regs) [] (spZ regs - sp0) HJ ltac:(lia)
             ltac:(rewrite Zminus_mod, Hal, H16; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)). }
  pose proof JI0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
  (* the world at the raw memory *)
  pose proof (cis_tw_csw W memc Bw HW) as HWc.
  (* ---- the run from the entry to the call ---- *)
  rewrite cis_entry_at.
  eapply (@decode_run fx W regs memc mdc CIS_ENTRY).
  { unfold LCK.ms_of_regs.
    eapply cis_run1_F with (lo := spZ regs - CIS_STK);
      try change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs).
    - exact HWc.
    - apply (decode_leafb_stk W memc (spZ regs - CIS_STK) (spZ regs)); [lia | lia |].
      intros a Ha. apply Hpres0. lia.
    - lia.
    - unfold TG.G_HARNESS_B_HI. lia.
    - exact EA.
    - exact FLY1.
    - apply (decode_leafb_rng W); [lia | lia |].
      intros b Hb. destruct (Hpres0 b ltac:(lia)) as [Hh _]. exact Hh.
    - apply cis_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    - apply cis_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    - apply cis_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    - apply cis_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    - apply cis_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    - apply cis_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia. }
  (* the state at the callee's entry *)
  intros ms1 msA mdA HP EQVA _ SBMA.
  destruct HP as (a2' & m1 & -> & MU & WM & FR & HW1).
  destruct (decode_eqv_mkst _ _ _ _ EQVA) as (RA & -> & HXA).
  change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs) in MU, FR.
  (* the inner journal after the four saves *)
  assert (MUw : forall x : word, ~ (spZ regs - 32 <= bv_unsigned x < spZ regs) ->
            mrestrict (w_H W) m1 x = mrestrict (w_H W) memc x).
  { intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside].
    split; [lia | exact I]. }
  assert (MGw : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) m1)).
  { intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 32)) as [Hl|Hl];
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
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 32)) as [Hl|Hl];
      [apply (MU x); cbn [outside]; split; [unfold spZ in *; lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|apply (MU x); cbn [outside]; split; [unfold spZ in *; lia | exact I]].
    exfalso.
    pose proof (proj1 (Hpres0 (bv_unsigned x) ltac:(lia))) as Hhx.
    rewrite Z_to_bv_bv_unsigned in Hhx. congruence. }
  assert (IJ1 : @ajournal rc YE2k.tfib_sink_head segs B CIS_STK (spZ regs) [] lyc Sc W memc mdc []
                  lyc Sc W m1 mdA 0).
  { apply (@ajournal_exec rc YE2k.tfib_sink_head segs B LAWS decode_segs_low CIS_STK (spZ regs) []
             lyc Sc W memc mdc [] lyc Sc W memc mdc 0 m1 mdA
             (fun a => spZ regs - 32 <= a < spZ regs) JI0 MUw MGw MHw SBMA).
    intros a Ha. left. lia. }
  pose proof IJ1 as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  (* the registers at the call *)
  assert (G1 : YKK.getr RA (Z_to_bv 5 1) = Z_to_bv 64 CIS_RET) by cis_reg HXA.
  assert (G2 : YKK.getr RA (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -32)) by cis_reg HXA.
  assert (G3 : YKK.getr RA (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3)) by cis_reg HXA.
  assert (G4 : YKK.getr RA (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4)) by cis_reg HXA.
  assert (G8 : YKK.getr RA (Z_to_bv 5 8) = Z_to_bv 64 CIS_M) by cis_reg HXA.
  assert (G9 : YKK.getr RA (Z_to_bv 5 9) = Z_to_bv 64 CIS_S1) by cis_reg HXA.
  assert (G10 : YKK.getr RA (Z_to_bv 5 10) = Z_to_bv 64 CIS_GS) by cis_reg HXA.
  assert (G11 : YKK.getr RA (Z_to_bv 5 11) = Z_to_bv 64 (TW.g_now Bw)) by cis_reg HXA.
  assert (G18 : YKK.getr RA (Z_to_bv 5 18) = Z_to_bv 64 CIS_S2) by cis_reg HXA.
  assert (G19 : YKK.getr RA (Z_to_bv 5 19) = YKK.getr regs (Z_to_bv 5 19)) by cis_reg HXA.
  assert (G20 : YKK.getr RA (Z_to_bv 5 20) = YKK.getr regs (Z_to_bv 5 20)) by cis_reg HXA.
  assert (G21 : YKK.getr RA (Z_to_bv 5 21) = YKK.getr regs (Z_to_bv 5 21)) by cis_reg HXA.
  assert (G22 : YKK.getr RA (Z_to_bv 5 22) = YKK.getr regs (Z_to_bv 5 22)) by cis_reg HXA.
  assert (G23 : YKK.getr RA (Z_to_bv 5 23) = YKK.getr regs (Z_to_bv 5 23)) by cis_reg HXA.
  assert (G24 : YKK.getr RA (Z_to_bv 5 24) = YKK.getr regs (Z_to_bv 5 24)) by cis_reg HXA.
  assert (G25 : YKK.getr RA (Z_to_bv 5 25) = YKK.getr regs (Z_to_bv 5 25)) by cis_reg HXA.
  assert (G26 : YKK.getr RA (Z_to_bv 5 26) = YKK.getr regs (Z_to_bv 5 26)) by cis_reg HXA.
  assert (G27 : YKK.getr RA (Z_to_bv 5 27) = YKK.getr regs (Z_to_bv 5 27)) by cis_reg HXA.
  assert (GSP : spZ RA = spZ regs - 32).
  { change (spZ RA) with (bv_unsigned (YKK.getr RA (Z_to_bv 5 2))).
    rewrite G2, unsigned_lit by lia. lia. }
  (* ---- the call of diginet_session_deadline ---- *)
  change (Z_to_bv 64 CIS_CALLEE) with (Z_to_bv 64 LSDc.DIGINET_SESSION_DEADLINE).
  eapply SRr_bind.
  { apply (@decode_leafb_journal fx rc YE2k.tfib_sink_head B LAWS W RA m1 CIS_STK (spZ regs) []
             lyc Sc W memc mdc [] lyc Sc mdA 0 (-32) LSDc.DIGINET_SESSION_DEADLINE (Some d) [] (fun _ => True) IJ1).
    - rewrite GSP. lia.
    - reflexivity.
    - lia.
    - unfold CIS_STK, CIS_FRAME, ESTACK. lia.
    - change (YK0s.ret_ok (YKK.getr RA (Z_to_bv 5 1))).
      rewrite G1. apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - change (YKK.getr RA (Z_to_bv 5 3) = w64 (as_gp B)). rewrite G3. exact Hgp.
    - change (YKK.getr RA (Z_to_bv 5 4) = w64 (as_tp B)). rewrite G4. exact Htp.
    - intros a Ha. unfold LCK.in_wr in Ha. inversion Ha.
    - intros HPRE.
      pose proof (LEAF fx) as LF.
      unfold transport_leaf_at, diginet_session_deadline_cg.transport_diginet_session_deadline_cg in LF.
      specialize (LF lyc Sc W RA m1 mdA (spZ regs - CIS_STK) (TW.g_now Bw) d Bw HPRE).
      cbv zeta in LF.
      pose proof (cis_gs_ra lyc Sc W m1 mdA HZS HAR1) as HRA.
      apply LF; clear LF.
      + exact G10.
      + exact G11.
      + exact RG4.
      + exact HW1.
      + exact HD.
      + rewrite G2, unsigned_lit by lia.
        apply (decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJ1); lia.
      + rewrite G2, unsigned_lit by lia. unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME. lia.
      + unfold AKA.off_stk. rewrite G2, unsigned_lit by lia.
        unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
      + rewrite G2, unsigned_lit by lia. apply (@decode_leafb_app_stack rc).
        unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME. lia.
      + rewrite G2, unsigned_lit by lia. apply (@decode_leafb_app_stack rc). lia.
      + exact (decode_leafb_asan_cells B HCELLS lyc Sc W m1 mdA HAR1).
      + unfold AKA.off_stk. rewrite G2, unsigned_lit by lia.
        unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME, GOT_CELL_K. lia.
      + unfold AKA.off_stk. rewrite G2, unsigned_lit by lia.
        unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME, CELL_K. lia.
      + apply (decode_leafb_addressable W m1 TB_g_s TW.SZ_g_s HRA);
          [unfold TB_g_s; lia | unfold TW.SZ_g_s; lia | unfold TB_g_s, TW.SZ_g_s, APPMEM_END; lia |].
        intros i Hi. unfold app_mem, LOWMEM_END, TB_g_s, TW.SZ_g_s in *. lia.
      + rewrite G2, unsigned_lit by lia.
        apply (decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJ1);
          unfold LSDc.DIGINET_SESSION_DEADLINE_FRAME; lia.
      + exact (proj1 (decode_leafb_rng_cells W)).
      + exact (proj2 (decode_leafb_rng_cells W)).
      + apply cis_rng_hull; unfold LSDc.DIGINET_SESSION_DEADLINE_S, LSDc.DIGINET_SESSION_DEADLINE_SN, TB_g_s,
          TW.SZ_g_s, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
      + apply (decode_leafb_rng_shadow W m1 TB_g_s TW.SZ_g_s HRA);
          unfold TB_g_s, TW.SZ_g_s; lia. }
  cbv beta. intros W2 c2 _.
  intros (-> & regs2 & mem2 & md2 & Hc2 & IJ2 & HPRES & HRES & HEFF & _ & _).
  change (YKK.getr RA 1) with (YKK.getr RA (Z_to_bv 5 1)) in Hc2.
  rewrite G1 in Hc2. subst c2.
  specialize (HRES d eq_refl).
  pose proof IJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  (* the frame the prologue wrote, kept across the call *)
  assert (FR2 : rw_cells rsegs mem2 (spZ regs + -32)
                  [C8 (YKK.getr regs (Z_to_bv 5 18)); C8 (YKK.getr regs (Z_to_bv 5 9));
                   C8 (YKK.getr regs (Z_to_bv 5 8)); C8 (YKK.getr regs (Z_to_bv 5 1))]).
  { apply (decode_rw_cells_eq m1 mem2 (spZ regs + -32)
             [C8 (YKK.getr regs (Z_to_bv 5 18)); C8 (YKK.getr regs (Z_to_bv 5 9));
              C8 (YKK.getr regs (Z_to_bv 5 8)); C8 (YKK.getr regs (Z_to_bv 5 1))] FR).
    intros i Hi. cbn in Hi. unfold wa.
    apply (decode_byte_eq (w_H W) (w_H W) m1 mem2 (spZ regs + -32 + i));
      [ apply (Hpres1 (spZ regs + -32 + i)); lia
      | apply (Hpres2 (spZ regs + -32 + i)); lia
      | apply HEFF; [lia | rewrite GSP; lia | intros Hx; unfold LCK.in_wr in Hx; inversion Hx] ]. }
  (* the world relation at the return *)
  assert (HW2 : tw_at TMAP_B (csw_view mem2) Bw).
  { apply (cis_tw_kept W m1 mem2 Bw HW1). intros x Hx.
    apply HEFF; [unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hx; lia
                | rewrite GSP; unfold TG.G_HARNESS_B_HI in Hx; try unfold ESTACK; try unfold LCK.ESTACK; lia |].
    intros Hy. unfold LCK.in_wr in Hy. inversion Hy. }
  (* the registers at the return *)
  assert (P2 : YKK.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -32))
    by (rewrite (HPRES 2 ltac:(unfold acallee_saved; lia)); exact G2).
  assert (P8 : YKK.getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 CIS_M)
    by (rewrite (HPRES 8 ltac:(unfold acallee_saved; lia)); exact G8).
  assert (P9 : YKK.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 CIS_S1)
    by (rewrite (HPRES 9 ltac:(unfold acallee_saved; lia)); exact G9).
  assert (P18 : YKK.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 CIS_S2)
    by (rewrite (HPRES 18 ltac:(unfold acallee_saved; lia)); exact G18).
  assert (SP2 : bv_unsigned (YKK.getr regs2 (Z_to_bv 5 2)) = spZ regs + -32)
    by (rewrite P2, unsigned_lit by lia; reflexivity).
  (* ---- the run from the return to the return to the caller ---- *)
  eapply (@decode_run fx W regs2 mem2 md2 CIS_RET).
  { unfold LCK.ms_of_regs.
    rewrite P8, P9, P18.
    replace (YKK.getr regs2 (Z_to_bv 5 10)) with (Z_to_bv 64 d) by (symmetry; exact HRES).
    eapply cis_run2_F.
    - exact HW2.
    - exact Rd.
    - exact D1.
    - exact D2.
    - exact FLY2.
    - rewrite SP2. lia.
    - rewrite SP2. lia.
    - rewrite SP2. exact FR2.
    - rewrite SP2. apply (decode_leafb_rng W); [lia | lia |].
      intros b Hb. destruct (Hpres2 b ltac:(lia)) as [Hh _]. exact Hh.
    - apply cis_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    - apply cis_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    - apply cis_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
    - apply cis_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia. }
  intros ms1 msB mdB HP EQVB _ SBMB.
  destruct HP as (a1' & a2'' & a3' & ->).
  destruct (decode_eqv_mkst _ _ _ _ EQVB) as (RB & -> & HXB).
  (* the journal across the second run: it writes nothing *)
  assert (IJ3 : @ajournal rc YE2k.tfib_sink_head segs B CIS_STK (spZ regs) [] lyc Sc W memc mdc []
                  lyc Sc W mem2 mdB 0).
  { apply (@ajournal_exec rc YE2k.tfib_sink_head segs B LAWS decode_segs_low CIS_STK (spZ regs) []
             lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 mem2 mdB (fun _ => False) IJ2);
      [ intros x _; reflexivity | apply YK1b.mem_grows_refl | intros x _; reflexivity | exact SBMB
      | intros a Ha; destruct Ha ]. }
  (* the registers at the return to the caller *)
  assert (KPRES : aregs_preserved regs RB).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                 r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - transitivity (Z_to_bv 64 (bv_unsigned (YKK.getr regs2 (Z_to_bv 5 2)) + 32)); [cis_reg HXB|].
      rewrite SP2. replace (spZ regs + -32 + 32) with (spZ regs) by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 3)); [cis_reg HXB|].
      rewrite (HPRES 3 ltac:(unfold acallee_saved; lia)). exact G3.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 4)); [cis_reg HXB|].
      rewrite (HPRES 4 ltac:(unfold acallee_saved; lia)). exact G4.
    - cis_reg HXB.
    - cis_reg HXB.
    - cis_reg HXB.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 19)); [cis_reg HXB|].
      rewrite (HPRES 19 ltac:(unfold acallee_saved; lia)). exact G19.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 20)); [cis_reg HXB|].
      rewrite (HPRES 20 ltac:(unfold acallee_saved; lia)). exact G20.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 21)); [cis_reg HXB|].
      rewrite (HPRES 21 ltac:(unfold acallee_saved; lia)). exact G21.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 22)); [cis_reg HXB|].
      rewrite (HPRES 22 ltac:(unfold acallee_saved; lia)). exact G22.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 23)); [cis_reg HXB|].
      rewrite (HPRES 23 ltac:(unfold acallee_saved; lia)). exact G23.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 24)); [cis_reg HXB|].
      rewrite (HPRES 24 ltac:(unfold acallee_saved; lia)). exact G24.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 25)); [cis_reg HXB|].
      rewrite (HPRES 25 ltac:(unfold acallee_saved; lia)). exact G25.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 26)); [cis_reg HXB|].
      rewrite (HPRES 26 ltac:(unfold acallee_saved; lia)). exact G26.
    - transitivity (YKK.getr regs2 (Z_to_bv 5 27)); [cis_reg HXB|].
      rewrite (HPRES 27 ltac:(unfold acallee_saved; lia)). exact G27. }
  (* ---- the post ---- *)
  apply SRr_ret.
  unfold transport_cis_post, decode_cg_post.
  exists lyc, Sc, RB, mem2, mdB, 0.
  split.
  { pose proof (ret_ok_stmt_YK0s (YKK.getr regs (Z_to_bv 5 1)) Hra) as ERA.
    rewrite ERA. reflexivity. }
  split; [unfold CIS_EV; lia|].
  split.
  { change own with ([] ++ own).
    apply (ajournal_sub segs B LAWS decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
             CIS_STK (spZ regs) [] [] lyc Sc W mem2 mdB 0 HJ IJ3 ltac:(lia) ltac:(lia)).
    intros a (r & Hr & _). destruct Hr. }
  split; [exact KPRES|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B decode_segs_low CIS_STK (spZ regs) [] [] lyc Sc W memc mdc
             lyc Sc W mem2 mdB 0 (fun _ => False) IJ3 HAR).
    - intros a (r & Hr & _). destruct Hr.
    - intros b m i Hb _ _. exact Hb.
    - exact sink_closed_nil. }
  split; [exact (mle_start MT Sc MTL)|].
  exact EBw.
Qed.
End cis.

Print Assumptions transport_check_inflight_settle_cg_holds.
