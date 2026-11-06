(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvA_FuzzStmt LbA_PrsStmt LbA_DStat LbA_SR LbA_Conv LbA_Ctx LbA_RG2 LbA_Vec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_TopDefs LbA_TopKit LbA_TopH2 LbA_TopA1 LbA_TopM1 LbA_TopT LbA_TopR.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section TopM.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.
  Hypothesis HPO : binary_parse_stmtA H LINV_P5.
  Hypothesis HTR : po_tr_ok H.

  Lemma seg_CC : forall (e : hent H) msF mo, hpre H e -> 1 <= e_N e ->
    as_AKREL H (e_s e) (mkCfg msF mo) -> as_MPRES H (e_mo e) mo -> hA_post H e (as_VIS H (e_s e) msF) ->
    as_SR H (hpost H e) (mkCfg msF mo).
  Proof.
    intros e msF mo HP HN1 KR MP PA.
    destruct PA as (ff & fp & XSc & x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & VIS & HI & OSH & W334 & (jv & CVJ)).
    pose proof (rt_bp_base H HH) as HB.
    pose proof (rt_bp_cost H HH) as (CF0 & CM0). pose proof (rt_bp_live H HH) as LIVE.
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hpre_geo H e HP) as (_ & LO & SSHI & SHIH & SP16 & TP).
    pose proof (hinv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof HP as (FZ & _ & _ & NR & _ & _ & _ & _ & BS & BC & BL & _ & SPB & BB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LFL
                      & _ & _ & _ & _ & _ & ALs).
    set (SP := eSP e) in *. set (S1 := eS1 e) in *. set (lo := e_lo e) in *. set (N := e_N e) in *.
    destruct (hinv_er H e ff fp XSc (e_s e) (e_LB e) m' HI) as (errv & ER).
    assert (ALp : 0 <= as_AL H (e_s e) - ICM 64 - ICM (4 * (N / 4))).
    { pose proof (top_cost_nonneg (po_cost (N / 4))) as _. unfold top_cost in ALs. fold N in ALs. unfold po_cost in ALs. lia. }

    eapply (ah_seq H HB).
    { eapply (ctx_create_sr H HB (Z_to_bv 64 TOP_CTX_RA) (Z_to_bv 64 S1)) with (evz := RG_ENV) (lo := lo) (B := e_B e) (errv := errv);
        rewrite ?HLib.u64_of_Z by lia;
        [exact VIS | reflexivity | unfold RG_ENV; lia | exact (hinv_rh H _ _ _ _ _ _ _ HI) | exact KR
        | apply (LIVE (e_s e) (e_LB e) m' CTX_SZ (hinv_rh H _ _ _ _ _ _ _ HI) ltac:(unfold CTX_SZ; lia));
          change (nsmall CTX_SZ) with 64; change (nlg CTX_SZ) with 0; unfold TOP_SMALL, TOP_CNT, TOP_LARGE, po_small, po_cnt, po_large in BS, BC, BL; lia
        | rewrite CM0; change (ICM CTX_SZ) with (ICM 64); pose proof (ICM_nonneg (4 * (N / 4)) ltac:(Z.div_mod_to_equations; lia)); lia
        | exact (hinv_ra H _ _ _ _ _ _ _ HI) | lia
        | exact (proj1 (stk_split asegs m' lo S1 SP (hinv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))) | exact CE
        | unfold AOPNEW_STACK, AMALLOC_STACK; lia | exact ER | exact (hinv_mi H _ _ _ _ _ _ _ HI) | exact TP
        | clear - S32; Z.div_mod_to_equations; lia | lia | unfold TOP_CTX_RA; vm_compute; reflexivity | exact (hinv_ac H _ _ _ _ _ _ _ HI)]. }
    intros [msF2 mo2] P2.
    destruct P2 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & errv' & A & j1 & j2 & pc & s' & VIS2 & KR2 & MP2
                    & MI2 & ST2 & ER2 & RA2 & AP2 & BR2 & RH2 & CC2 & CA2 & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, MP2. rewrite HLib.u64_of_Z in ST2, AP2 by lia.
    rewrite (ret_pc_even TOP_CTX_RA ltac:(unfold TOP_CTX_RA; lia) eq_refl) in VIS2.
    pose proof BR2 as (BA0 & BA16 & BAn & BAI & BAC & AF & AAPP). unfold CTX_SZ in *.
    assert (XP2 : xpres H (e_LB e) S1 [] m' m2) by exact (xpres_of_apres H _ _ [] _ _ AP2).
    assert (RF2 : as_RFS H ((6, ff, fp) :: e_LF e) m2) by exact (RFS_via_apres H HB _ _ _ _ _ (hinv_rf H _ _ _ _ _ _ _ HI) AP2).
    assert (HI2 : hinv H e ff fp (XSc ++ []) s' ((pc, A, 64) :: e_LB e) m2).
    { eapply (hinv_sr H HB e ff fp XSc [] [] (e_s e) (e_LB e) (e_LB e) s' ((pc, A, 64) :: e_LB e) m' m2 HP HI (fun b Hb => Hb) XP2);
        [apply Forall_nil | apply Forall_nil | exact RF2 | exact RH2 | exact AC2 | exact MI2 | exact ST2 | exists errv'; exact ER2 | exact RA2]. }
    rewrite app_nil_r in HI2.
    assert (APF : forall A0 k, ff <= A0 -> A0 + k <= ff + 4096 -> aclient_range H (e_LB e) S1 A0 k)
      by (intros A0 k K1 K2; right; right; right; right; left; unfold AFS_SIZE in *; lia).
    assert (APS : forall A0 k, sh ff <= A0 -> A0 + k <= sh ff + 512 -> aclient_range H (e_LB e) S1 A0 k)
      by (intros A0 k K1 K2; right; right; right; right; right; left; lia).
    assert (OSH2 : SHAD m2 (ff + 32) (repeat (b8 0) 313)).
    { destruct OSH as (O1 & O2 & U). split; [exact O1|]. split; [exact O2|].
      replace (sh (ff + 32)) with (sh ff + 4) in * by (rewrite <- (sh_add8 ff 4); f_equal).
      eapply (apres_u8arr H); [exact AP2 | exact U | rewrite repeat_length; apply APS; cbn; lia]. }
    assert (W3342 : wr_at asegs m2 (sh ff + 334) 3) by (eapply (apres_wr_at H); [exact AP2 | exact W334 | apply APS; lia]).
    assert (CVJ2 : rw_cells asegs m2 (ff + 2672) [CB 24 jv]) by (eapply (apres_rw_cells H); [exact AP2 | exact CVJ | apply APF; cbn; lia]).

    eapply (ahh_evt_then H HB (fun ms => exists y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m4,
              ms = MS (mkR (Z_to_bv 64 TOP_RS_RA) (Z_to_bv 64 S1) (e_gp e) (e_tp e) y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                           (Z_to_bv 64 (ff + 2672)) (Z_to_bv 64 (N / 4)) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff))
                           (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 (e_D e)) (Z_to_bv 64 N) (Z_to_bv 64 (ff + 2672)) (Z_to_bv 64 A)
                           (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) (e_s11 e) y28 y29 y30 y31)
                      (e_F e) (Z_to_bv 64 VRESIZE) (e_fc e) None m4 (seg_rom asegs)
              /\ hinv H e ff fp XSc s' ((pc, A, 64) :: e_LB e) m4
              /\ rw_cells asegs m4 (ff + 2672) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]
              /\ SHAD m4 (ff + 2672) (repeat (b8 0) 3)
              /\ SHAD m4 (ff + 32) (repeat (b8 0) 313)
              /\ rw_cells asegs m4 A [C4 (wz RG_ENV); CB 44 j1; C8 (wz 0); CB 8 j2] /\ addressable m4 A CTX_SZ));
      [exact KR2 | exact VIS2 | |].
    { eapply evt_cut.
      { exact (hMS1 (e_gp e) (e_tp e) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (e_s8 e) (e_s11 e) t3 t4 t5 t6 (e_F e) (e_fc e) m2 SP S1 ff
                    (e_D e) N A lo ltac:(lia) ltac:(lia) ltac:(lia) W3342 (hinv_stk H _ _ _ _ _ _ _ HI2) MI2). }
      intros ms3 (z13 & z14 & z15 & z16 & z17 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3 & U3). subst ms3.
      assert (HI3 : hinv H e ff fp XSc s' ((pc, A, 64) :: e_LB e) m3).
      { eapply (hinv_munch H HB); [exact HP | exact HI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 |].
        unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; right. lia. }
      assert (SV3 : SHAD m3 (ff + 2672) (repeat (b8 0) 3)).
      { split; [lia|]. split; [clear - F3; Z.div_mod_to_equations; lia|].
        replace (sh (ff + 2672)) with (sh ff + 334) by (rewrite <- (sh_add8 ff 334); f_equal). exact U3. }
      assert (DJ3 : forall A0 k, (A0 + k <= sh ff + 334 \/ sh ff + 337 <= A0) -> disjoint_from [(sh ff + 334, sh ff + 337)] A0 k)
        by (intros A0 k K0; cbn; split; [lia | exact I]).
      assert (CVJ3 : rw_cells asegs m3 (ff + 2672) [CB 24 jv]) by (eapply rw_cells_transport; [exact CVJ2 | exact MU3 | exact WM3 | apply DJ3; cbn; destruct F16; lia]).
      assert (ACC3 : accessible m3 (ff + 2672) 24).
      { eapply (addressable_accessible m3 (ff + 2672) 24); [| lia | lia | unfold AAPP_HI; lia]. split; [lia|]. exact SV3. }
      assert (SHV3 : shvis m3 (ff + 2672) (ff + 2672 + 24)).
      { pose proof (ah_frm_shvis H HB _ _ (6, ff, fp) (hinv_rf H _ _ _ _ _ _ _ HI3) (or_introl eq_refl)) as X. cbn in X.
        change (fsz 6) with 4096 in X. eapply shvis_sub; [exact X | lia | lia | lia | lia | lia]. }
      pose proof (rt_bp_base H HH) as HB'.
      eapply evt_cut.
      { eapply (ah_memset H HB' (Z_to_bv 64 TOP_MS_RA) (Z_to_bv 64 S1)) with (c := 0) (junk := jv) (lo := lo);
          rewrite ?HLib.u64_of_Z by lia;
          [reflexivity | lia | exact CVJ3 | exact ACC3 | exact SHV3
          | exact (proj1 (stk_split asegs m3 lo S1 SP ST3 ltac:(lia))) | exact CE | unfold AINTRIN_STACK; lia | exact MI3
          | exact (hinv_ac H _ _ _ _ _ _ _ HI3) | lia | eapply aapp_in_app_mem; [exact F10 | lia | lia]
          | eapply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | cbn; lia | cbn; lia] | left; lia]. }
      intros ms4 P4. destruct P4 as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m4 & EQ4 & MU4 & WM4 & MI4 & ST4 & CV4 & AC4).
      subst ms4. rewrite !HLib.u64_of_Z in MU4 by lia. rewrite !HLib.u64_of_Z in ST4, CV4 by lia. unfold AINTRIN_STACK in MU4.
      rewrite (ret_pc_even TOP_MS_RA ltac:(unfold TOP_MS_RA; lia) eq_refl).
      assert (ST4f : stk asegs m4 lo SP).
      { destruct (stk_split asegs m3 lo S1 SP ST3 ltac:(lia)) as [_ STu].
        assert (STu2 : stk asegs m4 S1 SP) by (eapply stk_transport_disjoint; [exact STu | exact MU4 | exact WM4 | cbn; lia]).
        exact (stk_merge asegs m4 lo S1 SP ST4 STu2 ltac:(lia)). }
      assert (HI4 : hinv H e ff fp XSc s' ((pc, A, 64) :: e_LB e) m4).
      { eapply (hinv_munch H HB); [exact HP | exact HI3 | exact MU4 | exact WM4 | exact MI4 | exact ST4f |].
        unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        - right; left. lia.
        - left. fold lo SP. lia. }
      assert (DJ4 : forall A0 k, (A0 + k <= ff + 2672 \/ ff + 2672 + 24 <= A0) -> (A0 + k <= S1 - 4096 \/ S1 <= A0) ->
                      disjoint_from [(ff + 2672, ff + 2672 + 24); (S1 - 4096, S1)] A0 k)
        by (intros A0 k K0 K1; cbn; split; [lia | split; [lia | exact I]]).
      eapply evt_cut.
      { exact (hMS2 (e_gp e) (e_tp e) w0 w1 w2 (Z_to_bv 64 (ff + 2672)) w11 w12 w13 w14 w15 w16 w17 (e_s11 e) w28 w29 w30 w31
                    (e_F e) (e_fc e) m4 SP S1 ff (e_D e) N (ff + 2672) A ltac:(lia)). }
      intros ms5 EQ5. hnf in EQ5. subst ms5. apply evt_done.
      exists w0, w1, w2, w12, w13, w14, w15, w16, w17, w28, w29, w30, w31, m4. split; [reflexivity|].
      split; [exact HI4|].
      split; [apply zero24_cells; exact CV4|].
      assert (SHD : forall a k, 0 <= a -> 0 <= k -> a + 8 * k <= aceil -> disjoint_from [(ff + 2672, ff + 2672 + 24); (S1 - 4096, S1)] (sh a) k).
      { intros a k K1 K2 K3. assert (sh a + k <= sh aceil) by (rewrite <- (sh_add8 a k); apply sh_mono; lia).
        assert (sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
        pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE a (8 * k) F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as X.
        replace (nsh (8 * k)) with k in X by (unfold nsh; Z.div_mod_to_equations; lia).
        cbn. split; [destruct X; unfold AFS_SIZE in *; lia | split; [lia | exact I]]. }
      assert (SHADt : forall a sbs, SHAD m3 a sbs -> a + 8 * Z.of_nat (length sbs) <= aceil -> SHAD m4 a sbs).
      { intros a sbs (S1a & S1b & U) Ka. split; [exact S1a|]. split; [exact S1b|].
        eapply u8arr_transport; [exact U | exact MU4 | exact WM4 | apply SHD; lia]. }
      split; [apply SHADt; [exact SV3 | cbn; lia]|].
      split.
      { apply SHADt; [| rewrite repeat_length; cbn; lia].
        destruct OSH2 as (O1 & O2 & U). split; [exact O1|]. split; [exact O2|].
        eapply u8arr_transport; [exact U | exact MU3 | exact WM3 | apply DJ3; rewrite repeat_length; cbn].
        replace (sh (ff + 32)) with (sh ff + 4) by (rewrite <- (sh_add8 ff 4); f_equal). lia. }
      split.
      { eapply rw_cells_transport; [| exact MU4 | exact WM4 | apply DJ4; cbn; [destruct AF; unfold AFS_SIZE in *; lia | lia]].
        eapply rw_cells_transport; [exact CC2 | exact MU3 | exact WM3 | apply DJ3; cbn].
        pose proof (aapp_disjoint_sh A 64 ff 4096 AAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as X.
        replace (nsh 4096) with 512 in X by reflexivity. lia. }
      { destruct CA2 as (CA0 & S1a & S1b & U). split; [exact CA0|]. split; [exact S1a|]. split; [exact S1b|].
        assert (UA3 : u8arr asegs m3 (sh A) (shadow_of 64)).
        { eapply u8arr_transport; [exact U | exact MU3 | exact WM3 | apply DJ3; rewrite shadow_of_length by lia].
          change (nsh 64) with 8.
          pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE A 64 F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as X.
          change (nsh 64) with 8 in X.
          assert (sh A + 8 <= sh ff \/ sh (ff + 4096) <= sh A).
          { destruct AF as [AF|AF]; [left | right]; unfold AFS_SIZE in *.
            - rewrite <- (sh_add8 A 8). apply sh_mono. lia.
            - apply sh_mono. lia. }
          lia. }
        eapply u8arr_transport; [exact UA3 | exact MU4 | exact WM4 | rewrite shadow_of_length by (unfold CTX_SZ; lia); change (nsh CTX_SZ) with 8; apply SHD; lia]. } }
    intros msF3 mo3 KR3 MP3 P3.
    destruct P3 as (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m4 & VIS3 & HI4 & CV4 & SV4 & OSH4 & CC4 & CA4).
    apply (seg_RS H HH HPO HTR); [exact HP|].
    exists ff, fp, XSc, s', ((pc, A, 64) :: e_LB e), (e_F e), (e_fc e), y5, y6, y7, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m4, pc, A, j1, j2.
    cbn [cfg_ms cfg_model]. split; [exact VIS3|]. split; [exact KR3|].
    split; [exact (ah_mpres_trans H HB (e_mo e) mo mo3 MP (ah_mpres_trans H HB mo mo2 mo3 MP2 MP3))|].
    split; [exact FZ|]. split; [exact HI4|]. split; [exact HN1|].
    split; [rewrite CM0 in AL2; change (ICM CTX_SZ) with (ICM 64) in AL2; lia|].
    split; [exists (repeat (b8 0) 313); destruct OSH4 as (_ & _ & U);
            replace (sh (ff + 32)) with (sh ff + 4) in U by (rewrite <- (sh_add8 ff 4); f_equal);
            pose proof (rw_cells_of_u8arr asegs m4 _ _ U) as X; rewrite repeat_length in X; exact X|].
    split; [exact CV4|]. split; [exact SV4|]. split; [exact CC4|]. split; [exact CA4|]. reflexivity.
  Qed.
End TopM.
