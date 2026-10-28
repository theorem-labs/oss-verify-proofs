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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TopDefs LbB_TopKit LbB_TopH2 LbB_TopA1 LbB_TopM1 LbB_TopT LbB_TopR.
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
    destruct PA as (ff & fp & XSc & x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & VIS & HI & D88 & OSH & W334 & (jv & CVJ)).
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
    assert (D2 : rw_cells asegs m2 (S1 + 88) [C8 (Z_to_bv 64 (e_D e))]) by (eapply (apres_rw_cells H); [exact AP2 | exact D88 | left; lia]).
    assert (SHF : sh ff + 512 <= S1).
    { pose proof (sh_nsh_high ff 4096 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as K. replace (nsh 4096) with 512 in K by reflexivity.
      unfold AHI_LO in K. lia. }
    assert (SHA : sh A + 8 <= S1).
    { pose proof (sh_nsh_high A 64 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as K. change (nsh 64) with 8 in K.
      unfold AHI_LO in K. lia. }
    assert (WH5 : wins_hi [(S1 + 80, S1 + 88)]) by (unfold wins_hi; apply Forall_cons; [right; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]).

    eapply (ahh_evt_then H HB (fun ms => forall msF' mo', as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo2 mo' ->
              as_VIS H s' msF' = ms -> as_SR H (hpost H e) (mkCfg msF' mo')));
      [exact KR2 | exact VIS2 | | intros msF3 mo3 KR3 MP3 PP; exact (PP msF3 mo3 KR3 MP3 eq_refl)].
    eapply evt_cut.
    { exact (hMS1 (e_gp e) (e_tp e) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (e_s8 e) (e_s9 e) (e_s10 e) t3 t4 t5 t6 (e_F e) (e_fc e) m2 SP S1 ff N A lo
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) W3342 (hinv_stk H _ _ _ _ _ _ _ HI2) MI2). }
    intros ms3 (z13 & z14 & z15 & z16 & z17 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3 & U3 & FR3). subst ms3.
    assert (HI3 : hinv H e ff fp XSc s' ((pc, A, 64) :: e_LB e) m3).
    { eapply (hinv_munch H HB); [exact HP | exact HI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 |].
      unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. fold lo SP. lia.
      - right; right. lia. }
    assert (SV3 : SHAD m3 (ff + 2672) (repeat (b8 0) 3)).
    { split; [lia|]. split; [clear - F3; Z.div_mod_to_equations; lia|].
      replace (sh (ff + 2672)) with (sh ff + 334) by (rewrite <- (sh_add8 ff 334); f_equal). exact U3. }
    assert (DJ3 : forall A0 k, (A0 + k <= S1 + 24 \/ S1 + 64 <= A0) -> (A0 + k <= sh ff + 334 \/ sh ff + 337 <= A0) ->
                    disjoint_from [(S1 + 24, S1 + 64); (sh ff + 334, sh ff + 337)] A0 k)
      by (intros A0 k K0 K1; cbn; split; [lia | split; [lia | exact I]]).
    assert (CVJ3 : rw_cells asegs m3 (ff + 2672) [CB 24 jv])
      by (eapply rw_cells_transport; [exact CVJ2 | exact MU3 | exact WM3 | apply DJ3; cbn; [lia | destruct F16; lia]]).
    assert (D3 : rw_cells asegs m3 (S1 + 88) [C8 (Z_to_bv 64 (e_D e))])
      by (eapply rw_cells_transport; [exact D2 | exact MU3 | exact WM3 | apply DJ3; cbn; lia]).
    assert (OSH3 : SHAD m3 (ff + 32) (repeat (b8 0) 313)).
    { eapply SHAD_transport; [exact OSH2 | exact MU3 | exact WM3 |].
      replace (sh (ff + 32)) with (sh ff + 4) by (rewrite <- (sh_add8 ff 4); f_equal).
      apply DJ3; rewrite repeat_length; cbn; lia. }
    assert (CC3 : rw_cells asegs m3 A [C4 (wz RG_ENV); CB 44 j1; C8 (wz 0); CB 8 j2]).
    { eapply rw_cells_transport; [exact CC2 | exact MU3 | exact WM3 | apply DJ3; cbn; [lia |]].
      pose proof (aapp_disjoint_sh A 64 ff 4096 AAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as X.
      replace (nsh 4096) with 512 in X by reflexivity. lia. }
    assert (CA3 : addressable m3 A CTX_SZ).
    { eapply addressable_transport; [exact CA2 | exact MU3 | exact WM3 |]. change (nsh CTX_SZ) with 8.
      apply DJ3; [lia |].
      pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE A 64 F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as X.
      change (nsh 64) with 8 in X.
      assert (sh A + 8 <= sh ff \/ sh (ff + 4096) <= sh A).
      { destruct AF as [AF|AF]; [left | right]; unfold AFS_SIZE in *.
        - rewrite <- (sh_add8 A 8). apply sh_mono. lia.
        - apply sh_mono. lia. }
      lia. }
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
    assert (SHD : forall a k, 0 <= a -> 0 <= k -> a + 8 * k <= aceil -> disjoint_from [(ff + 2672, ff + 2672 + 24); (S1 - 4096, S1)] (sh a) k).
    { intros a k K1 K2 K3. assert (sh a + k <= sh aceil) by (rewrite <- (sh_add8 a k); apply sh_mono; lia).
      assert (sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE a (8 * k) F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as X.
      replace (nsh (8 * k)) with k in X by (unfold nsh; Z.div_mod_to_equations; lia).
      cbn. split; [destruct X; unfold AFS_SIZE in *; lia | split; [lia | exact I]]. }
    assert (SHADt : forall a sbs, SHAD m3 a sbs -> a + 8 * Z.of_nat (length sbs) <= aceil -> SHAD m4 a sbs).
    { intros a sbs (S1a & S1b & U) Ka. split; [exact S1a|]. split; [exact S1b|].
      eapply u8arr_transport; [exact U | exact MU4 | exact WM4 | apply SHD; lia]. }
    assert (SV4 : SHAD m4 (ff + 2672) (repeat (b8 0) 3)) by (apply SHADt; [exact SV3 | cbn; lia]).
    assert (OSH4 : SHAD m4 (ff + 32) (repeat (b8 0) 313)) by (apply SHADt; [exact OSH3 | rewrite repeat_length; cbn; lia]).
    assert (CC4 : rw_cells asegs m4 A [C4 (wz RG_ENV); CB 44 j1; C8 (wz 0); CB 8 j2])
      by (eapply rw_cells_transport; [exact CC3 | exact MU4 | exact WM4 | apply DJ4; cbn; [destruct AF; unfold AFS_SIZE in *; lia | lia]]).
    assert (CA4 : addressable m4 A CTX_SZ).
    { eapply addressable_transport; [exact CA3 | exact MU4 | exact WM4 |]. change (nsh CTX_SZ) with 8. apply SHD; lia. }
    assert (FR4 : rw_cells asegs m4 (S1 + 24) (top_fr A ff)).
    { unfold top_fr. eapply rw_cells_transport; [exact FR3 | exact MU4 | exact WM4 | apply DJ4; cbn; lia]. }
    assert (D4 : rw_cells asegs m4 (S1 + 88) [C8 (Z_to_bv 64 (e_D e))])
      by (eapply rw_cells_transport; [exact D3 | exact MU4 | exact WM4 | apply DJ4; cbn; lia]).
    eapply evt_cut.
    { exact (hMS2 (e_gp e) (e_tp e) w0 w1 w2 (Z_to_bv 64 (ff + 2672)) w11 w12 w13 w14 w15 w16 w17 (e_s8 e) (e_s9 e) (e_s10 e) w28 w29 w30 w31
                  (e_F e) (e_fc e) m4 SP S1 ff N (ff + 2672) lo ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ST4f MI4). }
    intros ms5 (m5 & EQ5 & MU5 & WM5 & MI5 & ST5 & CV5). subst ms5. apply evt_done.
    intros msF3 mo3 KR3 MP3 VIS3.
    assert (HI5 : hinv H e ff fp XSc s' ((pc, A, 64) :: e_LB e) m5).
    { eapply (hinv_munch H HB); [exact HP | exact HI4 | exact MU5 | exact WM5 | exact MI5 | exact ST5 |].
      unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. fold lo SP. lia. }
    assert (DJ5 : forall A0 k, (A0 + k <= S1 + 80 \/ S1 + 88 <= A0) -> disjoint_from [(S1 + 80, S1 + 88)] A0 k)
      by (intros A0 k K0; cbn; split; [lia | exact I]).
    assert (FR5 : rw_cells asegs m5 (S1 + 24) (top_fr A ff)).
    { unfold top_fr. eapply rw_cells_transport; [exact FR4 | exact MU5 | exact WM5 | apply DJ5; cbn; lia]. }
    assert (VD5 : rw_cells asegs m5 (S1 + 80) (top_vd ff (e_D e))).
    { unfold top_vd. apply (proj2 (rw_cells_app asegs m5 (S1 + 80) [C8 (wz (ff + 2672))] [C8 (wz (e_D e))])). split; [exact CV5|].
      replace (S1 + 80 + Z.of_nat (cells_size [C8 (wz (ff + 2672))])) with (S1 + 88) by (cbn; lia).
      eapply rw_cells_transport; [exact D4 | exact MU5 | exact WM5 | apply DJ5; cbn; lia]. }
    assert (CV5z : rw_cells asegs m5 (ff + 2672) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { apply zero24_cells. eapply rw_cells_transport; [exact CV4 | exact MU5 | exact WM5 | apply DJ5; cbn; lia]. }
    assert (SV5 : SHAD m5 (ff + 2672) (repeat (b8 0) 3))
      by (eapply SHAD_transport_hi; [exact SV4 | exact MU5 | exact WM5 | rewrite repeat_length; cbn; unfold AAPP_HI; lia | exact WH5]).
    assert (OSH5 : SHAD m5 (ff + 32) (repeat (b8 0) 313))
      by (eapply SHAD_transport_hi; [exact OSH4 | exact MU5 | exact WM5 | rewrite repeat_length; cbn; unfold AAPP_HI; lia | exact WH5]).
    assert (CC5 : rw_cells asegs m5 A [C4 (wz RG_ENV); CB 44 j1; C8 (wz 0); CB 8 j2])
      by (eapply rw_cells_transport; [exact CC4 | exact MU5 | exact WM5 | apply DJ5; cbn; lia]).
    assert (CA5 : addressable m5 A CTX_SZ)
      by (eapply addressable_transport_hi; [exact CA4 | exact MU5 | exact WM5 | unfold CTX_SZ, AAPP_HI; lia | exact WH5]).
    pose proof (seg_RS H) as SRS. try specialize (SRS HH). try specialize (SRS HPO). try specialize (SRS HTR).
    apply SRS; [exact HP|]. unfold cut_RS.
    exists ff, fp, XSc, s', ((pc, A, 64) :: e_LB e), (e_F e), (e_fc e), w0, w1, w2, w12, w13, w14, w15, w16, w17, (e_s8 e), (e_s9 e), (e_s10 e),
      w28, w29, w30, w31, m5, pc, A, j1, j2.
    cbn [cfg_ms cfg_model]. split; [exact VIS3|]. split; [exact KR3|].
    split; [exact (ah_mpres_trans H HB (e_mo e) mo mo3 MP (ah_mpres_trans H HB mo mo2 mo3 MP2 MP3))|].
    split; [exact FZ|]. split; [exact HI5|]. split; [exact FR5|]. split; [exact VD5|]. split; [exact HN1|].
    split; [rewrite CM0 in AL2; change (ICM CTX_SZ) with (ICM 64) in AL2; lia|].
    split; [exists (repeat (b8 0) 313); destruct OSH5 as (_ & _ & U);
            replace (sh (ff + 32)) with (sh ff + 4) in U by (rewrite <- (sh_add8 ff 4); f_equal);
            pose proof (rw_cells_of_u8arr asegs m5 _ _ U) as X; rewrite repeat_length in X; exact X|].
    split; [exact CV5z|]. split; [exact SV5|]. split; [exact CC5|]. split; [exact CA5|]. apply Permutation_refl.
  Qed.
End TopM.
