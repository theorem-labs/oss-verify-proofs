(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 653 of its 721 lines of code are new or changed and 396 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac-repacer/fuzz_wire's check_width in image A, proving the frozen
   statement lib/A/Prog/check_width_cg.v wire_check_width_holds_stmt. The form is reac-repacer/fuzz_uci's
   lib/A/Prog/check_value_cgW.v (footprint runs carried into SRr, an inner journal over the call's stack window, each
   call cut by its callee's statement) with its segment file lib/A/Prog/UciCvSegs.v, and the leaf call of its
   lib/A/Prog/check_clamp_cgW.v (here through lib/A/Prog/WireCcLeafb.v wcc_leafb_journal, the leaf taken by
   WireCg.v wire_leaf_at). The w_width loop and the frame law are this unit's plain walk lib/Prog/check_width.v
   (width_loop, w_width_frame_law, fc_model_neg), restated over image A's rp_frame_channels_model. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/A/Prog/check_width_cgW.v, with its module paths, module names and numbers changed; 316 of its 451 lines of code are new or changed and 586 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/B/Prog/check_forward_cgW.v, with its module paths and module names changed; 214 of its 297 lines of code are new or changed and 368 lines of the source are left out. *)
(* The walk of reac-repacer/fuzz_wire's check_ret in image A, proving the frozen statement lib/A/Prog/check_ret_cg.v
   wire_check_ret_holds_stmt, in the form of reac-repacer/fuzz_uci's lib/A/Prog/check_clamp_cgW.v and
   check_value_cgW.v: footprint runs carried into SRr (lib/A/Prog/WireChkRun.v wcr_run), the call cut by the leaf's
   contract through the kit's wrapper, the caller's journal re-established over the call's stack window
   (lib/A/Prog/WireCcLeafb.v wcc_leafb_journal), and the post from the inner journal (YCbq.v ajournal_sub,
   acall_kept_of_journal).

   The walk:
     1. an INNER journal at the entry state (YCbq.v ajournal_sub_init): stack window [spZ regs - CR_STK, spZ regs),
        no footprint of its own;
     2. cr_seg1_F (lib/A/Prog/WireCrSegs.v): the 0x10-byte frame (s0, ra) and want in s0; the inner journal follows
        the frame write (YCbq.v ajournal_exec);
     3. rp_ret_accept at +0x68 (lib/A/Prog/rp_ret_accept_cg.v through lib/A/Prog/WireCg.v wire_leaf_at: it writes no
        byte outside its own frame), whose result a0 is the same ret_accept_result as s0;
     4. cr_seg2_F: the property test `bne a0, s0` is not taken, the frame is reloaded and the function returns;
     5. the post: the outer journal by ajournal_sub, acall_kept by acall_kept_of_journal, the meter by mo_le_refl. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o YK1b.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c YP09 YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg check_ret_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WireChkRun WireCcLeafb WireCrSegs.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require LeafCgKit rp_ret_accept_cg rp_ret_accept_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ret_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgKit.
Module AC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.AsanCells.
Module AImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Img0.
Module LRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_ret_accept_cg.
Module ARA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_ret_accept_c.
Module PRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ret_accept_c.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : wire_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis LEAF : forall fx' : YK11.FPState, @wire_leaf_at rc B (@LRA.wire_rp_ret_accept_cg) fx'.
Local Abbreviation ajournalA := (@ajournal rc sink segs B).
Local Abbreviation GR rg i := (YK11.getr rg (Z_to_bv 5 i)).

Theorem wire_check_ret_cg_walk : wire_check_ret_cg B MT (wire_sigma WS_check_ret).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n bs.
  intros HJ Hra Hra4 Hgp Htp H10 H11 Hal Hwlo Hwhi Hn Hlen Hblk Hgarr Hnev.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  (* 1. the inner journal *)
  assert (Hsp16 : sp0 mod 16 = 0).
  { pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _). exact H16. }
  assert (JI0 : ajournalA CR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0).
  { apply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CR_STK (spZ regs) []
             (spZ regs - sp0) HJ).
    - lia.
    - rewrite Zminus_mod, Hal, Hsp16. reflexivity.
    - lia.
    - unfold CR_STK, CR_FRAME, ESTACK. lia.
    - lia. }
  pose proof JI0 as (HARc & Hly0 & _).
  assert (Hsprng : YM05.alloc_ceiling + CR_STK <= spZ regs /\ spZ regs <= 2 ^ 47).
  { pose proof JI0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      (_ & _ & Hc & Hlo & Hhi & H47 & _) & _). unfold CR_STK, CR_FRAME, ESTACK in *. lia. }
  destruct Hsprng as [Hsp1 Hsp2].
  assert (Hpres0 : forall a, spZ regs - CR_STK <= a < spZ regs -> apresent (w_H W) memc a).
  { pose proof JI0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp. }
  (* the runtime cells at the entry memory *)
  pose proof (wcc_leafb_asan_cells B HCELLS lyc Sc W memc mdc HARc) as HAC0.
  pose proof HAC0 as (CK0 & GCK0 & _).
  (* the block of f, when n > 0 *)
  assert (Hfblk : 14 <= n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA)
    by (intros H14; apply Hblk; lia).
  (* the block's own bounds: a live block lies in [4096, alloc_ceiling) (YG0d.v AR_blocks_law). *)
  assert (Hfrng : 14 <= n -> 4096 <= f /\ f + n <= YM05.alloc_ceiling).
  { intros HL. destruct (Hfblk HL) as (bA & nA & HbA & Hb1 & Hb2).
    pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HARc HbA) as (_ & HP4 & HPc & _ & _ & _ & _).
    assert (Hreq : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia). lia. }
  (* 2. the prologue and the want computation *)
  assert (EA0 : GR regs 10 = Z_to_bv 64 f) by exact H10.
  assert (EA1 : GR regs 11 = Z_to_bv 64 n) by exact H11.
  eapply (@wcr_run fx W regs memc mdc (wire_sigma WS_check_ret)).
  { unfold LCK.ms_of_regs. rewrite EA0, EA1.
    change (wire_sigma WS_check_ret) with CR_ENTRY.
    eapply cr_seg1_F with (bs := bs) (lo := spZ regs - CR_STK).
    all: try change (bv_unsigned (GR regs 2)) with (spZ regs).
    - apply (wcr_stk_present (w_H W)); [lia | lia | exact Hpres0].
    - unfold CR_STK, CR_FRAME, ESTACK, CR_FR in *. lia.
    - intros HL. rewrite (wcr_u64 n) in HL by lia.
      destruct (Hfblk HL) as (bA & nA & HbA & Hb1 & Hb2).
      assert (Hreq : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
      pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HARc HbA) as (_ & HP4 & HPc & HPapp & _ & _ & _).
      rewrite (wcr_u64 f) by lia.
      split; [lia|].
      split.
      { apply (wcc_leafb_bytes_garr8 W memc f bs); [exact Hgarr | lia | lia]. }
      split; [unfold CR_FR, CR_STK, CR_FRAME, ESTACK, YM05.alloc_ceiling in *; lia|].
      split; [apply (@wcc_leafb_app_stack rc); unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia|].
      split; [apply (@wcc_leafb_app_stack rc); unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia|].
      split; [exact HAC0|].
      split; [unfold AC.GOT_CELL_K, CR_FR, CR_STK, CR_FRAME, ESTACK, YM05.alloc_ceiling in *; lia|].
      split; [unfold AC.CELL_K, CR_FR, CR_STK, CR_FRAME, ESTACK, YM05.alloc_ceiling in *; lia|].
      apply (@wcc_leafb_addressable_block rc B LAWS lyc Sc W memc mdc bA nA (f + 12) 2 HARc HbA); lia.
    - apply (wcc_leafb_rng_vis W memc); [unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia | unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia |].
      intros a Ha. apply Hpres0. unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *. lia.
    - intros _. exact (proj1 (wcc_leafb_rng_cells W)).
    - intros _. exact (proj2 (wcc_leafb_rng_cells W)).
    - intros HL. rewrite (wcr_u64 n) in HL by lia.
      destruct (Hfblk HL) as (bA & nA & HbA & Hb1 & Hb2). destruct (Hfrng HL) as [Hf4 Hfhi].
      pose proof (@YM05.alloc_ceiling_val rc) as [CEIL2 _].
      rewrite (wcr_u64 f) by lia.
      apply (@wcc_leafb_rng_block rc B LAWS lyc Sc W memc mdc bA nA (f + 12) 2 HARc HbA); [lia|].
      unfold req_size; destruct (Z.eqb_spec nA 0); lia.
    - intros HL. rewrite (wcr_u64 n) in HL by lia.
      destruct (Hfblk HL) as (bA & nA & HbA & Hb1 & Hb2). destruct (Hfrng HL) as [Hf4 Hfhi].
      pose proof (@YM05.alloc_ceiling_val rc) as [CEIL2 _].
      rewrite (wcr_u64 f) by lia.
      apply (@wcc_leafb_rng_shadow_block rc B LAWS lyc Sc W memc mdc bA nA (f + 12) 2 HARc HbA); [lia | lia|].
      unfold req_size; destruct (Z.eqb_spec nA 0); lia. }
  intros ms' md' (ms0 & (a2' & a3' & a4' & a5' & m1 & -> & MU & WM & FR) & EQV) SBM.
  change (bv_unsigned (GR regs 2)) with (spZ regs) in MU, FR.
  destruct (wcr_regs_of EQV) as (E1 & E2 & E3 & E4 & E8 & E9 & E10L & E11L & E12 & E18 & E19 & E20 & E21 & E22 &
    E23 & E24 & E25 & E26 & E27).
  change (bv_unsigned (GR regs 2)) with (spZ regs) in E2.
  (* the same register reads at the statement's notation (getr r 1) as at the kit's (getr r (Z_to_bv 5 1)) *)
  rewrite (wcr_u64 n) in E8 by lia.
  assert (ER1 : YK11.getr (ms_regs ms') 1 = Z_to_bv 64 CR_RET) by exact E1.
  assert (ER3 : YK11.getr (ms_regs ms') 3 = YK11.getr regs 3) by exact E3.
  assert (ER4 : YK11.getr (ms_regs ms') 4 = YK11.getr regs 4) by exact E4.
  rewrite (wcr_ms_shape _ _ _ _ EQV).
  (* the inner journal after the frame write *)
  assert (HJ1 : ajournalA CR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W m1 md' 0).
  { apply (ajournal_exec segs B LAWS WirePImg.wire_segs_low CR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc
             mdc 0 m1 md' (fun a => spZ regs - CR_FR <= a < spZ regs) JI0).
    - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - CR_FR)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
      assert (Hxr : spZ regs - CR_STK <= bv_unsigned x < spZ regs)
        by (unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia).
      destruct (Hpres0 _ Hxr) as [_ (b & Hb)].
      assert (Hw : wview AImg.rsegs m1 x <> None).
      { refine (WM x _). unfold wview. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
      unfold wview in Hw. destruct (m1 x) as [b'|] eqn:Em1; [discriminate|]. exfalso.
      rewrite (LeafCgGlue.find_segment_out AImg.rsegs (bv_unsigned x) 1) in Hw; [exact (Hw eq_refl)|lia|].
      intros sg Hin Hr.
      pose proof (WirePImg.wire_segs_low (bv_unsigned x) (ex_intro _ sg (conj Hin Hr))) as Hlow.
      unfold kLowMemEnd in Hlow. lia.
    - intros x Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - CR_FR)) as [Hl|Hl];
        [apply (MU x); cbn [outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|apply (MU x); cbn [outside]; split; [lia | exact I]].
      exfalso.
      assert (Hxr : spZ regs - CR_STK <= bv_unsigned x < spZ regs)
        by (unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia).
      pose proof (proj1 (Hpres0 _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
    - exact SBM.
    - intros a Ha. cbv beta in Ha. left. unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *. lia. }
  (* 3. the leaf call *)
  assert (SP1 : spZ (ms_regs ms') = spZ regs + -16).
  { change (spZ (ms_regs ms')) with (bv_unsigned (GR (ms_regs ms') 2)). rewrite E2.
    rewrite (wcr_u64 (spZ regs - CR_FR)) by (unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia).
    unfold CR_FR. lia. }
  assert (SPW : bv_unsigned (GR (ms_regs ms') 2) = spZ regs - CR_FR).
  { change (bv_unsigned (GR (ms_regs ms') 2)) with (spZ (ms_regs ms')). rewrite SP1. unfold CR_FR. lia. }
  eapply SRr_bind.
  { eapply (@wcc_leafb_journal fx rc sink B LAWS W (ms_regs ms') m1 CR_STK (spZ regs) [] lyc Sc W memc mdc
              [] lyc Sc md' 0 (-16) ARA.RP_RET_ACCEPT
              (Some (PRA.ret_accept_result n bs)) [] (fun _ => True) HJ1).
    - exact SP1.
    - reflexivity.
    - lia.
    - unfold CR_STK, CR_FRAME. lia.
    - rewrite ER1. unfold CR_RET. apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - rewrite ER3. exact Hgp.
    - rewrite ER4. exact Htp.
    - intros a Ha. unfold LCK.in_wr in Ha. inversion Ha.
    - intros HPRE.
      pose proof (LEAF fx) as LF. unfold wire_leaf_at, LRA.wire_rp_ret_accept_cg in LF.
      specialize (LF lyc Sc W (ms_regs ms') m1 md' bs (spZ regs - CR_STK) HPRE). cbv zeta in LF.
      rewrite E10L, E11L in LF.
      rewrite (wcr_u64 n) in LF by lia.
      change (bv_unsigned (GR (ms_regs ms') 2)) with (spZ (ms_regs ms')) in LF. rewrite SP1 in LF.
      unfold ARA.RP_RET_ACCEPT_FRAME in LF.
      pose proof (wcc_leafb_asan_cells B HCELLS lyc Sc W m1 md' (proj1 HJ1)) as HAC1.
      apply LF; clear LF.
      + eapply (wcc_leafb_stk_journal B); [exact HJ1 | unfold CR_STK, CR_FRAME, ESTACK in *; lia | unfold CR_STK, CR_FRAME, ESTACK in *; lia].
      + unfold CR_STK, CR_FRAME, ESTACK in *; lia.
      + intros HL.
        destruct (Hfblk HL) as (bA & nA & HbA & Hb1 & Hb2). destruct (Hfrng HL) as [Hf4 Hfhi].
        assert (Hreq : nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia).
        pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HARc HbA) as (_ & HP4 & HPc & HPapp & _ & _ & _).
        pose proof (@YM05.alloc_ceiling_val rc) as [CEIL3 _].
        rewrite (wcr_u64 f) by lia.
        split; [lia|].
        split.
        { apply (wcc_leafb_bytes_garr8 W m1 f bs); [|lia|lia].
          apply (wcr_garr8_of_aview (w_H W) m1 f). intros j Hj. rewrite length_map in Hj.
          pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
          split.
          - replace (f + Z.of_nat j) with (bA + (f + Z.of_nat j - bA)) by lia.
            rewrite (F2 bA nA (f + Z.of_nat j - bA) HbA HbA ltac:(lia)
                       ltac:(intros (r0 & Hr0 & _); destruct Hr0)).
            replace (bA + (f + Z.of_nat j - bA)) with (f + Z.of_nat j) by lia.
            exact (wcr_garr8_aview (w_H W) memc f _ j Hgarr ltac:(rewrite length_map; lia)).
          - exact (proj2 (Hgarr j ltac:(rewrite length_map; lia))). }
        split; [unfold AKA.off_stk; rewrite SPW; left; unfold CR_FR, CR_STK, CR_FRAME, ESTACK, YM05.alloc_ceiling in *; lia|].
        split; [apply (@wcc_leafb_app_stack rc); unfold CR_STK, CR_FRAME, ESTACK in *; lia|].
        split; [apply (@wcc_leafb_app_stack rc); unfold CR_STK, CR_FRAME, ESTACK in *; lia|].
        split; [exact HAC1|].
        split; [unfold AKA.off_stk; rewrite SPW; left; unfold AC.GOT_CELL_K, CR_FR, CR_STK, CR_FRAME, ESTACK, YM05.alloc_ceiling in *; lia|].
        split; [unfold AKA.off_stk; rewrite SPW; left; unfold AC.CELL_K, CR_FR, CR_STK, CR_FRAME, ESTACK, YM05.alloc_ceiling in *; lia|].
        apply (@wcc_leafb_addressable_block rc B LAWS lyc Sc W m1 md' bA nA (f + 12) 2 (proj1 HJ1) HbA); lia.
      + eapply (wcc_leafb_rng_journal B); [exact HJ1 | unfold CR_STK, CR_FRAME, ESTACK in *; lia | unfold CR_STK, CR_FRAME, ESTACK in *; lia].
      + intros _. exact (proj1 (wcc_leafb_rng_cells W)).
      + intros _. exact (proj2 (wcc_leafb_rng_cells W)).
      + intros HL. destruct (Hfblk HL) as (bA & nA & HbA & Hb1 & Hb2). destruct (Hfrng HL) as [Hf4 Hfhi].
        pose proof (@YM05.alloc_ceiling_val rc) as [CEIL3 _]. rewrite (wcr_u64 f) by lia.
        apply (@wcc_leafb_rng_block rc B LAWS lyc Sc W m1 md' bA nA (f + 12) 2 (proj1 HJ1) HbA); [lia|].
        unfold req_size; destruct (Z.eqb_spec nA 0); lia.
      + intros HL. destruct (Hfblk HL) as (bA & nA & HbA & Hb1 & Hb2). destruct (Hfrng HL) as [Hf4 Hfhi].
        pose proof (@YM05.alloc_ceiling_val rc) as [CEIL3 _]. rewrite (wcr_u64 f) by lia.
        apply (@wcc_leafb_rng_shadow_block rc B LAWS lyc Sc W m1 md' bA nA (f + 12) 2 (proj1 HJ1) HbA);
          [lia | lia|].
        unfold req_size; destruct (Z.eqb_spec nA 0); lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HRES & Heff & Hgrow & _).
  (* 4. the test and the return *)
  assert (HA0 : GR regs2 10 = w64 (PRA.ret_accept_result n bs)) by exact (HRES _ eq_refl).
  assert (HS0 : GR regs2 8 = Z_to_bv 64 (PRA.ret_accept_result n bs))
    by (etransitivity; [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact E8]).
  assert (SP2 : spZ regs2 = spZ regs - CR_FR).
  { change (spZ regs2) with (bv_unsigned (GR regs2 2)).
    rewrite (HP2 2 ltac:(unfold acallee_saved; lia)), E2.
    apply (wcr_u64 (spZ regs - CR_FR)). unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *. lia. }
  (* the frame is still there: the leaf wrote only below its own sp *)
  assert (HFR2 : rw_cells AImg.rsegs mem2 (spZ regs - CR_FR) [C8 (GR regs 8); C8 (GR regs 1)]).
  { apply (wcr_rw_cells_ext m1 mem2 _ _ FR). intros a Ha.
    cbn [cells_size csize Nat.add] in Ha. change (Z.of_nat 16) with 16 in Ha.
    unfold wa. apply (wcr_byte_eq (w_H W) (w_H W) m1 mem2 a).
    - eapply (wcr_win_of B); [exact HJ1 | unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia].
    - eapply (wcr_win_of B); [exact HJ2 | unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia].
    - apply Heff; [unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia | | intros Hc; unfold LCK.in_wr in Hc; inversion Hc].
      rewrite SP1. unfold ESTACK, CR_FR, CR_STK, CR_FRAME in *. lia. }
  rewrite <- (Z_to_bv_bv_unsigned (YK11.getr (ms_regs ms') 1)).
  eapply (@wcr_run fx W regs2 mem2 md2 (raZ (ms_regs ms'))).
  { unfold LCK.ms_of_regs, raZ. rewrite ER1.
    rewrite (wcr_u64 CR_RET) by (unfold CR_RET; lia).
    rewrite HA0, HS0. unfold w64.
    eapply cr_seg2_F.
    - change (bv_unsigned (GR regs2 2)) with (spZ regs2). rewrite SP2. exact HFR2.
    - change (bv_unsigned (GR regs2 2)) with (spZ regs2). rewrite SP2.
      unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *. lia.
    - change (bv_unsigned (GR regs2 2)) with (spZ regs2). rewrite SP2. eapply (wcc_leafb_rng_journal B); [exact HJ2 | unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia | unfold CR_FR, CR_STK, CR_FRAME, ESTACK in *; lia]. }
  intros ms2' md2' (ms2 & -> & EQV2) SBM2.
  destruct (wcr_regs_of EQV2) as (G1 & G2 & G3 & G4 & G8 & G9 & G10 & G11 & G12 & G18 & G19 & G20 & G21 & G22 &
    G23 & G24 & G25 & G26 & G27).
  assert (Hret : ret_pc (GR regs 1) = GR regs 1) by (apply LeafCgFacts.ret_ok_stmt_YK0s; exact Hra).
  rewrite Hret in EQV2.
  rewrite (wcr_ms_shape _ _ _ _ EQV2).
  assert (HJ2' : ajournalA CR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2' 0)
    by (eapply (wcr_aj_md B LAWS); [exact HJ2 | exact SBM2]).
  (* 5. the post *)
  apply SRr_ret. unfold wire_cr_post.
  exists lyc, Sc, (ms_regs ms2'), mem2, md2'.
  split; [reflexivity|].
  split.
  { pose proof (ajournal_sub segs B LAWS WirePImg.wire_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CR_STK (spZ regs) [] [] lyc Sc W mem2 md2' 0 HJ HJ2' Hwlo Hwhi
                  ltac:(intros a (r0 & Hr0 & _); destruct Hr0)) as J.
    cbn [app] in J. unfold CR_EV. exact J. }
  split.
  { intros i Hi. unfold acallee_saved in Hi.
    assert (Hc : i = 2 \/ i = 3 \/ i = 4 \/ i = 8 \/ i = 9 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/
                 i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia.
    assert (KP : forall j, acallee_saved j -> GR regs2 j = GR (ms_regs ms') j)
      by (intros j Hj; exact (HP2 j Hj)).
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - etransitivity; [exact G2|].
      change (bv_unsigned (GR regs2 2)) with (spZ regs2). rewrite SP2. unfold CR_FR.
      replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
    - etransitivity; [exact G3|]. etransitivity; [exact (KP 3 ltac:(unfold acallee_saved; lia))|]. exact E3.
    - etransitivity; [exact G4|]. etransitivity; [exact (KP 4 ltac:(unfold acallee_saved; lia))|]. exact E4.
    - exact G8.
    - etransitivity; [exact G9|]. etransitivity; [exact (KP 9 ltac:(unfold acallee_saved; lia))|]. exact E9.
    - etransitivity; [exact G18|]. etransitivity; [exact (KP 18 ltac:(unfold acallee_saved; lia))|]. exact E18.
    - etransitivity; [exact G19|]. etransitivity; [exact (KP 19 ltac:(unfold acallee_saved; lia))|]. exact E19.
    - etransitivity; [exact G20|]. etransitivity; [exact (KP 20 ltac:(unfold acallee_saved; lia))|]. exact E20.
    - etransitivity; [exact G21|]. etransitivity; [exact (KP 21 ltac:(unfold acallee_saved; lia))|]. exact E21.
    - etransitivity; [exact G22|]. etransitivity; [exact (KP 22 ltac:(unfold acallee_saved; lia))|]. exact E22.
    - etransitivity; [exact G23|]. etransitivity; [exact (KP 23 ltac:(unfold acallee_saved; lia))|]. exact E23.
    - etransitivity; [exact G24|]. etransitivity; [exact (KP 24 ltac:(unfold acallee_saved; lia))|]. exact E24.
    - etransitivity; [exact G25|]. etransitivity; [exact (KP 25 ltac:(unfold acallee_saved; lia))|]. exact E25.
    - etransitivity; [exact G26|]. etransitivity; [exact (KP 26 ltac:(unfold acallee_saved; lia))|]. exact E26.
    - etransitivity; [exact G27|]. etransitivity; [exact (KP 27 ltac:(unfold acallee_saved; lia))|]. exact E27. }
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (acall_kept_of_journal segs B WirePImg.wire_segs_low CR_STK (spZ regs) [] [] lyc Sc W memc mdc lyc Sc W
             mem2 md2' 0 (fun _ => False) HJ2' HARc).
    - intros a (r0 & Hr0 & _). destruct Hr0.
    - intros b m i Hb _ _. exact Hb.
    - exact sink_closed_nil. }
  exact (mo_le_refl MT MTL Sc).
Qed.

End Walk.

(* The frozen statement: every premise of the walk is a premise of wire_check_ret_holds_stmt. *)
Theorem wire_check_ret_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  @wire_check_ret_holds_stmt fx rc B MT.
Proof.
  intros HCELLS LAWS MTL LEAF. exact (@wire_check_ret_cg_walk fx rc B MT HCELLS LAWS MTL LEAF).
Qed.
