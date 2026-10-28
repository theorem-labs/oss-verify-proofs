(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat LbB_SR LbB_Conv LbB_Ctx LbB_RG2 LbB_Vec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TopDefs LbB_TopKit LbB_TopH2 LbB_TopM1 LbB_TopT LbB_TopC LbB_TopP LbB_TopL.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section TopR.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.
  Hypothesis HPO : binary_parse_stmtA H LINV_P5.
  Hypothesis HTR : po_tr_ok H.

  Definition cut_RS (e : hent H) (c : config) : Prop :=
    exists (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (F' : bvmap 5 word) (fc' : bv 32)
           (x5 x6 x7 x12 x13 x14 x15 x16 x17 x24 x25 x26 x28 x29 x30 x31 : word) (m' : mem) (pc : bptr) (A : Z) (j1 j2 : list byte),
      as_VIS H sk (cfg_ms c) = MS (mkR (Z_to_bv 64 TOP_RS_RA) (Z_to_bv 64 (eS1 e)) (e_gp e) (e_tp e) x5 x6 x7 (Z_to_bv 64 (eSP e))
                    (Z_to_bv 64 (eS1 e)) (Z_to_bv 64 (ff + 2672)) (Z_to_bv 64 (e_N e / 4)) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 2672)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000)
                    (Z_to_bv 64 (ff + 32)) x24 x25 x26 (Z_to_bv 64 (e_N e)) x28 x29 x30 x31)
                                  F' (Z_to_bv 64 VRESIZE) fc' None m' (seg_rom asegs)
      /\ as_AKREL H sk c /\ as_MPRES H (e_mo e) (cfg_model c)
      /\ FPSteps.frm_zero fc'
      /\ hinv H e ff fp XSc sk LBk m'
       /\ rw_cells asegs m' (eS1 e + 24) (top_fr A ff) /\ rw_cells asegs m' (eS1 e + 80) (top_vd ff (e_D e))
      /\ 1 <= e_N e /\ as_AL H sk >= as_AL H (e_s e) - ICM 64
      /\ (exists j, rw_cells asegs m' (sh ff + 4) [CB 313 j])
      /\ rw_cells asegs m' (ff + 2672) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]
      /\ SHAD m' (ff + 2672) (repeat (b8 0) 3)
      /\ rw_cells asegs m' A [C4 (wz RG_ENV); CB 44 j1; C8 (wz 0); CB 8 j2] /\ addressable m' A CTX_SZ
      /\ Permutation LBk ((pc, A, 64) :: e_LB e).

  Lemma seg_RS : forall (e : hent H) (c : config), hpre H e -> cut_RS e c -> as_SR H (hpost H e) c.
  Proof.
    intros e [msF mo] HP CT.
    destruct CT as (ff & fp & XSc & sk & LBk & F' & fc' & x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x24 & x25 & x26 & x28 & x29 & x30 & x31
                    & m' & pc & A & j1 & j2 & VIS & KR & MP & FZ & HI & CFR & CVD & HN1 & AL & (j & CJ) & CV & SV & CC & CA & PERM).
    cbn [cfg_ms cfg_model] in VIS, MP.
    pose proof (rt_bp_base H HH) as HB. pose proof (rt_bp_annot H HH) as HANN.
    pose proof (rt_bp_cost H HH) as (CF0 & CM0). pose proof (rt_bp_live H HH) as LIVE.
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hpre_geo H e HP) as (_ & LO & SSHI & SHIH & SP16 & TP).
    pose proof (hinv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof HP as (_ & _ & _ & NR & _ & _ & _ & _ & BS & BC & BL & _ & SPB & BB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LFL
                      & _ & _ & _ & _ & _ & ALs).
    set (SP := eSP e) in *. set (S1 := eS1 e) in *. set (lo := e_lo e) in *. set (N := e_N e) in *.
    set (n := N / 4).
    assert (Hn : 0 <= n < 2 ^ 24) by (unfold n; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    assert (V8 : (ff + 2672) mod 8 = 0) by (clear - F3; Z.div_mod_to_equations; lia).
    assert (VAPP : aapp (ff + 2672) 24) by (eapply aapp_sub; [exact F10 | lia | lia]).
    destruct (hinv_er H e ff fp XSc sk LBk m' HI) as (errv & ER).
    destruct (Z.eq_dec n 0) as [N0|N0].
    -
      eapply (ah_seq H HB).
      { pose proof (vresize0_sr H HB) as VR0. try specialize (VR0 HANN).
        eapply (VR0 (Z_to_bv 64 TOP_RS_RA) (Z_to_bv 64 S1)) with (V := ff + 2672) (lo := lo);
          rewrite ?HLib.u64_of_Z by lia;
          [exact VIS | reflexivity | fold n; rewrite N0; reflexivity | exact CV | exact SV | exact V8 | lia | lia | left; lia | exact KR
          | exact (proj1 (stk_split asegs m' lo S1 SP (hinv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))) | exact CE | lia
          | exact (hinv_mi H _ _ _ _ _ _ _ HI) | lia | exact (hinv_ac H _ _ _ _ _ _ _ HI)]. }
      intros [msF2 mo2] P2.
      destruct P2 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & VIS2 & KR2 & MP2 & MU2 & WM2 & MI2).
      cbn [cfg_ms cfg_model] in VIS2, MP2. rewrite HLib.u64_of_Z in MU2 by lia.
      rewrite (ret_pc_even TOP_RS_RA ltac:(unfold TOP_RS_RA; lia) eq_refl) in VIS2.
      assert (HI2 : hinv H e ff fp XSc sk LBk m2).
      { eapply (hinv_munch H HB); [exact HP | exact HI | exact MU2 | exact WM2 | exact MI2 | |].
        - eapply stk_wmono; [exact (hinv_stk H _ _ _ _ _ _ _ HI) | exact WM2 | lia].
        - unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. fold lo SP. lia. }
      assert (DJ2 : forall A0 k, (A0 + k <= S1 - 16 \/ S1 <= A0) -> disjoint_from [(S1 - 16, S1)] A0 k)
        by (intros A0 k K0; cbn; split; [lia | exact I]).
      assert (CFR2 : rw_cells asegs m2 (S1 + 24) (top_fr A ff))
        by (eapply rw_cells_transport; [exact CFR | exact MU2 | exact WM2 | apply DJ2; right; lia]).
      assert (CVD2 : rw_cells asegs m2 (S1 + 80) (top_vd ff (e_D e)))
        by (eapply rw_cells_transport; [exact CVD | exact MU2 | exact WM2 | apply DJ2; right; lia]).
      pose proof (seg_LP H HH) as SLP; try specialize (SLP HPO); try specialize (SLP HTR).
      apply SLP; [exact HP|].
      exists ff, fp, XSc, sk, LBk, F', fc', (Z_to_bv 64 TOP_RS_RA), t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, (Z_to_bv 64 (ff + 32)), x24, x25, x26, t3, t4, t5, t6, m2, 0, 0, pc, pc, A, j1, j2.
      cbn [cfg_ms cfg_model]. split; [exact VIS2|]. split; [exact KR2|].
      split; [exact (ah_mpres_trans H HB (e_mo e) mo mo2 MP MP2)|]. split; [exact FZ|]. split; [exact HI2|]. split; [exact CFR2|]. split; [exact CVD2|].
      split; [exact HN1|]. split; [change (e_N e) with N; fold n; lia|]. split; [change (ICM (4 * 0)) with 0; lia|].
      split; [exists j; eapply rw_cells_transport; [exact CJ | exact MU2 | exact WM2 | apply DJ2; cbn; lia]|].
      split; [eapply rw_cells_transport; [exact CV | exact MU2 | exact WM2 | apply DJ2; cbn; lia]|].
      split.
      { destruct SV as (S1a & S1b & U). split; [exact S1a|]. split; [exact S1b|].
        eapply u8arr_transport; [exact U | exact MU2 | exact WM2 | apply DJ2; rewrite repeat_length; cbn].
        assert (sh (ff + 2672) + 3 <= sh aceil) by (rewrite <- (sh_add8 (ff + 2672) 3); apply sh_mono; lia).
        assert (sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia). lia. }
      assert (INc : In (pc, A, 64) LBk) by (apply (Permutation_in _ (Permutation_sym PERM)); left; reflexivity).
      pose proof (ah_blocks H HB _ _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI) INc) as (C0 & C16 & Cn & CI & CCe & CF & CAPP); cbn in C0, C16, Cn, CI, CCe, CF, CAPP.
      split; [eapply rw_cells_transport; [exact CC | exact MU2 | exact WM2 | apply DJ2; cbn; lia]|].
      split.
      { destruct CA as (CA0 & S1a & S1b & U). split; [exact CA0|]. split; [exact S1a|]. split; [exact S1b|].
        eapply u8arr_transport; [exact U | exact MU2 | exact WM2 | apply DJ2; rewrite shadow_of_length by (unfold CTX_SZ; lia)].
        change (nsh CTX_SZ) with 8.
        assert (sh A + 8 <= sh aceil) by (rewrite <- (sh_add8 A 8); apply sh_mono; lia).
        assert (sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia). lia. }
      left. split; [reflexivity|]. split; [reflexivity | exact PERM].
    -
      assert (Hn1 : 1 <= n) by lia.
      assert (AOK : as_alloc_ok H sk LBk (4 * n)).
      { apply (LIVE sk LBk m' (4 * n) (hinv_rh H _ _ _ _ _ _ _ HI) ltac:(lia));
          rewrite ?(lb_small_perm _ _ PERM), ?(nlarge_perm _ _ PERM), ?(Permutation_length PERM); cbn [length];
          rewrite ?lb_small_cons, ?nlarge_cons; cbn [blk_size snd]; change (nsmall 64) with 64; change (nlg 64) with 0;
          pose proof (nsmall_bounds (4 * n) ltac:(lia)); pose proof (nlg_bounds (4 * n));
          unfold TOP_SMALL, TOP_CNT, TOP_LARGE, po_small, po_cnt, po_large in BS, BC, BL; lia. }
      assert (CMA : as_Cm H (4 * n) <= as_AL H sk).
      { rewrite CM0. unfold top_cost in ALs. fold N n in ALs. unfold po_cost in ALs. lia. }
      eapply (ah_seq H HB).
      { pose proof (vresize_sr H HB) as VR1. try specialize (VR1 HANN).
        eapply (VR1 (Z_to_bv 64 TOP_RS_RA) (Z_to_bv 64 S1)) with (V := ff + 2672) (n := n) (lo := lo) (B := e_B e)
          (errv := errv) (LF := (6, ff, fp) :: e_LF e) (shi := e_shi e);
          rewrite ?HLib.u64_of_Z by lia;
          [exact VIS | reflexivity | reflexivity | lia | exact CV | exact SV | exact V8
          | unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in VAPP; lia
          | right; right; right; right; left; unfold AFS_SIZE in *; lia
          | right; right; right; right; right; left; replace (sh (ff + 2672)) with (sh ff + 334) by (rewrite <- (sh_add8 ff 334); f_equal); lia
          | right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia
          | right; exists (6, ff, fp); split; [left; reflexivity | cbn; change (fsz 6) with 4096; lia]
          | eapply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | cbn; lia | cbn; lia]
          | left; unfold VRESIZE_STACK, AOPNEW_STACK, AMALLOC_STACK; lia
          | exact (hinv_rh H _ _ _ _ _ _ _ HI) | exact KR | exact AOK | exact CMA | exact (hinv_ra H _ _ _ _ _ _ _ HI) | lia
          | exact (proj1 (stk_split asegs m' lo S1 SP (hinv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))) | exact CE
          | unfold VRESIZE_STACK, AOPNEW_STACK, AMALLOC_STACK; lia | exact ER | exact (hinv_mi H _ _ _ _ _ _ _ HI) | exact TP
          | clear - S32; Z.div_mod_to_equations; lia | lia | exact (hinv_ac H _ _ _ _ _ _ _ HI) | exact (hinv_rf H _ _ _ _ _ _ _ HI)
          | exact (hinv_s0 H _ _ _ _ _ _ _ HI) | lia]. }
      intros [msF2 mo2] P2.
      destruct P2 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & errv' & P & pid & s' & VIS2 & KR2 & MP2
                      & MI2 & ST2 & ER2 & RA2 & XP2 & BR2 & RH2 & CV2 & CP2 & AP2 & RF2 & AC2 & S02 & AL2).
      cbn [cfg_ms cfg_model] in VIS2, MP2. rewrite HLib.u64_of_Z in ST2, XP2 by lia.
      rewrite (ret_pc_even TOP_RS_RA ltac:(unfold TOP_RS_RA; lia) eq_refl) in VIS2.
      assert (INC : forall b, In b (e_LB e) -> In b LBk) by (intros b Hb; apply (Permutation_in _ (Permutation_sym PERM)); right; exact Hb).
      assert (HI2 : hinv H e ff fp (XSc ++ []) s' ((pid, P, 4 * n) :: LBk) m2).
      { eapply (hinv_sr H HB e ff fp XSc [] [(ff + 2672, ff + 2672 + 24)] sk LBk LBk s' ((pid, P, 4 * n) :: LBk) m' m2 HP HI INC XP2);
          [apply Forall_nil | | exact RF2 | exact RH2 | exact AC2 | exact MI2 | exact ST2 | exists errv'; exact ER2 | exact RA2].
        apply Forall_cons; [| apply Forall_nil]. right; left. cbn. lia. }
      rewrite app_nil_r in HI2.
      assert (XCF : forall A0 k, ((ff <= A0 /\ A0 + k <= ff + 2672) \/ (ff + 2696 <= A0 /\ A0 + k <= ff + 4096)
                                  \/ (sh ff <= A0 /\ A0 + k <= sh ff + 512)) -> 0 <= k ->
                      xclient_range H LBk S1 [(ff + 2672, ff + 2672 + 24)] A0 k).
      { intros A0 k K Kk. split.
        - right; right; right; right. destruct K as [K|[K|K]]; [left; unfold AFS_SIZE in *; lia | left; unfold AFS_SIZE in *; lia | right; left; lia].
        - apply Forall_cons; [| apply Forall_nil]. cbn. destruct K as [K|[K|K]]; try lia; destruct F16; lia. }
      assert (INc : In (pc, A, 64) LBk) by (apply (Permutation_in _ (Permutation_sym PERM)); left; reflexivity).
      pose proof (ah_blocks H HB _ _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI) INc) as (C0 & C16 & Cn & CI & CCe & CF & CAPP); cbn in C0, C16, Cn, CI, CCe, CF, CAPP.
      assert (XCB : forall a k, A <= a -> a + k <= A + 64 -> 0 <= k -> xclient_range H LBk S1 [(ff + 2672, ff + 2672 + 24)] a k).
      { intros a k K1 K2 K3. split; [eapply (aclient_range_block H); [exact INc | exact K1 | exact K2]|].
        apply Forall_cons; [| apply Forall_nil]. cbn. destruct CF; unfold AFS_SIZE in *; lia. }
      assert (XCBs : xclient_range H LBk S1 [(ff + 2672, ff + 2672 + 24)] (sh A) (nsh 64)).
      { split; [exact (aclient_range_block_sh H LBk S1 pc A 64 INc)|].
        apply Forall_cons; [| apply Forall_nil]. cbn.
        pose proof (aapp_disjoint_sh (ff + 2672) 24 A 64 VAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)). lia. }
      assert (CFR2 : rw_cells asegs m2 (S1 + 24) (top_fr A ff)).
      { eapply xpres_rw_cells; [exact XP2 | exact CFR | split; [left; lia | apply Forall_cons; [unfold top_fr; cbn; right; lia | apply Forall_nil]]]. }
      assert (CVD2 : rw_cells asegs m2 (S1 + 80) (top_vd ff (e_D e))).
      { eapply xpres_rw_cells; [exact XP2 | exact CVD | split; [left; lia | apply Forall_cons; [unfold top_vd; cbn; right; lia | apply Forall_nil]]]. }
      pose proof (seg_LP H HH) as SLP; try specialize (SLP HPO); try specialize (SLP HTR).
      apply SLP; [exact HP|].
      exists ff, fp, XSc, s', ((pid, P, 4 * n) :: LBk), F', fc', (Z_to_bv 64 TOP_RS_RA), t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, (Z_to_bv 64 (ff + 32)), x24, x25, x26,
        t3, t4, t5, t6, m2, n, P, pid, pc, A, j1, j2.
      cbn [cfg_ms cfg_model]. split; [exact VIS2|]. split; [exact KR2|].
      split; [exact (ah_mpres_trans H HB (e_mo e) mo mo2 MP MP2)|]. split; [exact FZ|]. split; [exact HI2|]. split; [exact CFR2|]. split; [exact CVD2|].
      split; [exact HN1|]. split; [reflexivity|]. split; [rewrite CM0 in AL2; lia|].
      split; [exists j; eapply xpres_rw_cells; [exact XP2 | exact CJ | apply XCF; [right; right; cbn; lia | cbn; lia]]|].
      split; [exact CV2|].
      split.
      { destruct SV as (S1a & S1b & (UB & UW)). split; [exact S1a|]. split; [exact S1b|].
        replace (sh (ff + 2672)) with (sh ff + 334) in * by (rewrite <- (sh_add8 ff 334); f_equal). split.
        - eapply xpres_bytes_at; [exact XP2 | exact UB | rewrite repeat_length; apply XCF; [right; right; cbn; lia | cbn; lia]].
        - eapply xpres_wr_at; [exact XP2 | exact UW | rewrite repeat_length; apply XCF; [right; right; cbn; lia | cbn; lia]]. }
      split; [eapply xpres_rw_cells; [exact XP2 | exact CC | apply XCB; cbn; lia]|].
      split.
      { destruct CA as (CA0 & S1a & S1b & (UB & UW)). split; [exact CA0|]. split; [exact S1a|]. split; [exact S1b|]. unfold CTX_SZ in *. split.
        - eapply xpres_bytes_at; [exact XP2 | exact UB | rewrite shadow_of_length by lia; exact XCBs].
        - eapply xpres_wr_at; [exact XP2 | exact UW | rewrite shadow_of_length by lia; exact XCBs]. }
      right. split; [lia|]. split; [apply perm_skip; exact PERM|].
      split; [exists (repeat (b8 0) (Z.to_nat (4 * n))); exact CP2 | exact AP2].
  Qed.
End TopR.
