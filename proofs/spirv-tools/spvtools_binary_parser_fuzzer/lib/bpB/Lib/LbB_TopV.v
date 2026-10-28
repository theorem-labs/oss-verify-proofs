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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat LbB_SR LbB_Conv LbB_VecD1 LbB_VecD.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TopDefs LbB_TopKit LbB_TopH2 LbB_TopT1 LbB_TopT.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section TopV.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Definition cut_VD (e : hent H) (c : config) : Prop :=
    exists (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (F' : bvmap 5 word) (fc' : bv 32)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m' : mem)
           (n P : Z) (pv : bptr) (A : Z),
      as_VIS H sk (cfg_ms c) = MS (mkR x1 (Z_to_bv 64 (eS1 e)) (e_gp e) (e_tp e) x5 x6 x7 (Z_to_bv 64 (eSP e)) (Z_to_bv 64 (eS1 e))
                                       x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                  F' (Z_to_bv 64 TOP_CD_RA) fc' None m' (seg_rom asegs)
      /\ as_AKREL H sk c /\ as_MPRES H (e_mo e) (cfg_model c)
      /\ FPSteps.frm_zero fc'
      /\ hinv H e ff fp XSc sk LBk m'
      /\ as_AL H sk >= as_AL H (e_s e) - top_cost (e_N e)
      /\ (exists j, rw_cells asegs m' (sh ff + 4) [CB 313 j])
      /\ rw_cells asegs m' (ff + 2672) [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))]
      /\ SHAD m' (ff + 2672) (repeat (b8 0) 3)
      /\ rw_cells asegs m' (eS1 e + 24) (top_fr A ff) /\ rw_cells asegs m' (eS1 e + 80) (top_vd ff (e_D e))
      /\ ((n = 0 /\ P = 0 /\ Permutation LBk (e_LB e))
          \/ (1 <= n <= 2 ^ 24 /\ Permutation LBk ((pv, P, 4 * n) :: e_LB e)
              /\ (exists bs, rw_cells asegs m' P [CB (Z.to_nat (4 * n)) bs]) /\ addressable m' P (4 * n))).

  Lemma seg_VD : forall (e : hent H) (c : config), hpre H e -> cut_VD e c -> as_SR H (hpost H e) c.
  Proof.
    intros e [msF mo] HP CT.
    destruct CT as (ff & fp & XSc & sk & LBk & F' & fc' & x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19
                    & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m' & n & P & pv & Actx & VIS & KR & MP & FZ & HI & AL
                    & (j & CJ) & CV & SV & CFR & CVD & VEC).
    cbn [cfg_ms cfg_model] in VIS, MP.
    pose proof (rt_bp_base H HH) as HB. pose proof (rt_bp_annot H HH) as HANN. pose proof (rt_bp_cost H HH) as (CF0 & _).
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hpre_geo H e HP) as (_ & LO & SSHI & SHIH & SP16 & TP).
    pose proof (hinv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SPB & BB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & _ & _ & _ & ALs).
    set (SP := eSP e) in *. set (S1 := eS1 e) in *. set (lo := e_lo e) in *.
    assert (V8 : (ff + 2672) mod 8 = 0) by (clear - F3; Z.div_mod_to_equations; lia).
    assert (VAPP : aapp (ff + 2672) 24) by (eapply aapp_sub; [exact F10 | lia | lia]).

    eapply (ahh_evt_then H HB); [exact KR | exact VIS | |].
    unfold top_vd in CVD.
    change [C8 (wz (ff + 2672)); C8 (wz (e_D e))] with ([C8 (wz (ff + 2672))] ++ [C8 (wz (e_D e))]) in CVD.
    apply rw_cells_app in CVD as [CVf _].
    { exact (hVD1 x1 (e_gp e) (e_tp e) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                  F' fc' m' SP S1 (ff + 2672) lo ltac:(lia) ltac:(lia) ltac:(lia) CVf (hinv_stk H _ _ _ _ _ _ _ HI) ltac:(lia)
                  (hinv_mi H _ _ _ _ _ _ _ HI)). }
    intros msF1 mo1 KR1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & CD1).
    assert (HI1 : hinv H e ff fp XSc sk LBk m1).
    { eapply (hinv_munch H HB); [exact HP | exact HI | exact MU1 | exact WM1 | exact MI1 | exact ST1 |].
      unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. fold lo SP. lia. }
    assert (CJ1 : rw_cells asegs m1 (sh ff + 4) [CB 313 j]) by (eapply rw_cells_transport; [exact CJ | exact MU1 | exact WM1 | cbn; lia]).
    assert (CV1 : rw_cells asegs m1 (ff + 2672) [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))])
      by (eapply rw_cells_transport; [exact CV | exact MU1 | exact WM1 | cbn; lia]).
    assert (SV1 : SHAD m1 (ff + 2672) (repeat (b8 0) 3)).
    { destruct SV as (S1a & S1b & U). split; [exact S1a|]. split; [exact S1b|].
      eapply u8arr_transport; [exact U | exact MU1 | exact WM1 |]. rewrite repeat_length. cbn.
      assert (sh (ff + 2672) + 3 <= sh aceil) by (rewrite <- (sh_add8 (ff + 2672) 3); apply sh_mono; lia).
      assert (sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia). lia. }
    assert (W334 : forall m2, wr_at asegs m1 (sh ff + 334) 3 -> wmono asegs m1 m2 -> wr_at asegs m2 (sh ff + 334) 3)
      by (intros m2 W WM; exact (wr_at_wmono _ _ _ _ W WM)).
    assert (W3341 : wr_at asegs m1 (sh ff + 334) 3).
    { destruct SV1 as (_ & _ & (_ & W)). rewrite repeat_length in W. replace (sh ff + 334) with (sh (ff + 2672)) by (rewrite <- (sh_add8 ff 334); f_equal). exact W. }
    assert (CFR1 : rw_cells asegs m1 (S1 + 24) (top_fr Actx ff))
      by (eapply rw_cells_transport; [exact CFR | exact MU1 | exact WM1 | unfold top_fr; cbn; lia]).
    pose proof (hchain_call H HB e ff fp XSc sk LBk m1 HP HI1) as (CHN & CHU).
    destruct VEC as [(N0 & P0 & PERM) | (NR & PERM & (bs & CB0) & ADP)].
    -
      subst n P. cbn [Z.mul Z.add] in CV1.
      eapply (ahh_evt_then H HB); [exact KR1 | exact VIS1 | |].
      { eapply (vdestroy0_evt (Z_to_bv 64 0xe8c28) (Z_to_bv 64 S1)) with (Dd := S1 + 112) (V := ff + 2672) (lo := lo) (shi := e_shi e);
          rewrite ?HLib.u64_of_Z by lia;
          [reflexivity | exact CD1 | clear - S32; Z.div_mod_to_equations; lia | lia | lia | exact (hinv_s0 H _ _ _ _ _ _ _ HI1)
          | exact CV1 | exact SV1 | exact V8 | exact VAPP | left; lia | exact (proj1 (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)))
          | exact CE | lia | clear - S32; Z.div_mod_to_equations; lia | lia | exact MI1 | exact (hinv_ac H _ _ _ _ _ _ _ HI1)]. }
      intros msF2 mo2 KR2 MP2 P2.
      destruct P2 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2).
      rewrite HLib.u64_of_Z in MU2, ST2 by lia.
      rewrite (ret_pc_even 0xe8c28 ltac:(lia) eq_refl) in VIS2.
      assert (ST2f : stk asegs m2 lo SP).
      { destruct (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)) as [_ STu].
        assert (STu2 : stk asegs m2 S1 SP) by (eapply stk_transport_disjoint; [exact STu | exact MU2 | exact WM2 | cbn; lia]).
        exact (stk_merge asegs m2 lo S1 SP ST2 STu2 ltac:(lia)). }
      assert (HI2 : hinv H e ff fp XSc sk LBk m2).
      { eapply (hinv_munch H HB); [exact HP | exact HI1 | exact MU2 | exact WM2 | exact MI2 | exact ST2f |].
        unfold hwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. fold lo SP. lia. }
      apply (seg_E H HH); [exact HP|].
      exists ff, fp, XSc, sk, LBk, F', fc', (Z_to_bv 64 0xe8c28), t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7,
        x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, t3, t4, t5, t6, m2, Actx.
      cbn [cfg_ms cfg_model]. split; [exact VIS2|]. split; [exact KR2|].
      split; [exact (ah_mpres_trans H HB (e_mo e) mo mo2 MP (ah_mpres_trans H HB mo mo1 mo2 MP1 MP2))|].
      split; [exact FZ|]. split; [exact HI2|]. split; [exact PERM|]. split; [exact AL|].
      split; [exact (wr_at_wmono _ _ _ _ W3341 WM2)|].
      split; [exists j; eapply rw_cells_transport; [exact CJ1 | exact MU2 | exact WM2 | cbn; lia]|].
      eapply rw_cells_transport; [exact CFR1 | exact MU2 | exact WM2 | unfold top_fr; cbn; lia].
    -
      assert (INv : In (pv, P, 4 * n) LBk) by (apply (Permutation_in _ (Permutation_sym PERM)); left; reflexivity).
      pose proof (ah_blocks H HB _ _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI1) INv) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      pose proof (ah_nodup H HB _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI1)) as ND.
      assert (NDv : ~ In pv (map blk_id (e_LB e))).
      { pose proof (Permutation_NoDup (Permutation_map blk_id PERM) ND) as ND2. cbn [map] in ND2. apply NoDup_cons_iff in ND2 as [X _]. exact X. }
      assert (CB1 : rw_cells asegs m1 P [CB (Z.to_nat (4 * n)) bs]) by (eapply rw_cells_transport; [exact CB0 | exact MU1 | exact WM1 | cbn; lia]).
      assert (AD1 : addressable m1 P (4 * n)).
      { destruct ADP as (A0 & S1a & S1b & U). split; [exact A0|]. split; [exact S1a|]. split; [exact S1b|].
        eapply u8arr_transport; [exact U | exact MU1 | exact WM1 |]. rewrite shadow_of_length by lia. cbn.
        pose proof (sh_nsh_high P (4 * n) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X.
        assert (sh P + nsh (4 * n) <= sh aceil) by (unfold sh, nsh in *; Z.div_mod_to_equations; lia).
        assert (sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia). lia. }
      pose proof (hinv_rf H _ _ _ _ _ _ _ HI1) as RF1.
      destruct (hinv_er H e ff fp XSc sk LBk m1 HI1) as (errv & ER1).
      eapply (ah_seq H HB).
      { eapply (vdestroy_sr H HB HANN (Z_to_bv 64 0xe8c28) (Z_to_bv 64 S1)) with (Dd := S1 + 112) (V := ff + 2672) (P := P) (n := n) (lo := lo)
          (shi := e_shi e) (B := e_B e) (LF := (6, ff, fp) :: e_LF e) (pv := pv) (bs := bs) (errv := errv)
          (CH := (SP, bv_unsigned (e_ra e)) :: e_CH e);
          rewrite ?HLib.u64_of_Z by lia;
          [exact VIS1 | reflexivity | exact CD1 | clear - S32; Z.div_mod_to_equations; lia | lia | lia | exact (hinv_s0 H _ _ _ _ _ _ _ HI1)
          | exact CV1 | exact SV1 | exact V8 | exact VAPP | unfold VD_STACK, AINTRIN_STACK; lia
          | right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia
          | right; exists (6, ff, fp); split; [left; reflexivity | cbn; change (fsz 6) with 4096; lia]
          | destruct BF; [left | right]; unfold AFS_SIZE in *; lia
          | right; right; right; right; left; unfold AFS_SIZE in *; lia
          | exact NR | exact INv | exact CB1 | exact AD1 | exact (hinv_rh H _ _ _ _ _ _ _ HI1) | exact KR1 | rewrite CF0; lia
          | exact (hinv_ra H _ _ _ _ _ _ _ HI1) | lia | exact (proj1 (stk_split asegs m1 lo S1 SP ST1 ltac:(lia))) | exact CE | unfold AFREE_STACK; lia
          | exact ER1 | exact MI1 | exact TP | clear - S32; Z.div_mod_to_equations; lia | lia | exact (hinv_ac H _ _ _ _ _ _ _ HI1) | exact RF1
          | rewrite HLib.u64_of_Z by lia; exact CHN | | exact CHU].
        exact (htrace H e APC0_FREE [TOP_VD_RA] HP ltac:(unfold TOP_PF; cbn; right; left; reflexivity)). }
      intros [msF2 mo2] P2.
      destruct P2 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & s' & VIS2 & KR2 & MP2 & MI2 & ST2 & ER2 & RA2
                      & XP2 & RH2 & AC2 & RF2 & S02 & CV2 & AL2).
      cbn [cfg_ms cfg_model] in VIS2, MP2. rewrite HLib.u64_of_Z in ST2, XP2 by lia.
      rewrite (ret_pc_even 0xe8c28 ltac:(lia) eq_refl) in VIS2.
      assert (PLB : Permutation (as_lb_remove H pv LBk) (e_LB e)).
      { pose proof (lb_remove_perm H HB pv P (4 * n) LBk ND INv) as X.
        apply Permutation_cons_inv with (a := (pv, P, 4 * n)). exact (perm_trans (Permutation_sym X) PERM). }
      assert (INC : forall b, In b (e_LB e) -> In b (as_lb_remove H pv LBk)).
      { intros b Hb. apply (lb_remove_keep H HB); [exact ND | apply (Permutation_in _ (Permutation_sym PERM)); right; exact Hb |].
        intros E. apply NDv. rewrite <- E. apply in_map. exact Hb. }
      assert (HI2 : hinv H e ff fp (XSc ++ []) s' (as_lb_remove H pv LBk) m2).
      { eapply (hinv_sr H HB e ff fp XSc [] [(ff + 2672 + 8, ff + 2672 + 16)] sk LBk (as_lb_remove H pv LBk)); try eassumption.
        - apply Forall_nil.
        - apply Forall_cons; [| apply Forall_nil]. right; left; cbn; lia.
        - exists errv. exact ER2. }
      rewrite app_nil_r in HI2.
      apply (seg_E H HH); [exact HP|].
      exists ff, fp, XSc, s', (as_lb_remove H pv LBk), F', fc', (Z_to_bv 64 0xe8c28), t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7,
        x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, t3, t4, t5, t6, m2, Actx.
      cbn [cfg_ms cfg_model]. split; [exact VIS2|]. split; [exact KR2|].
      split; [exact (ah_mpres_trans H HB (e_mo e) mo mo2 MP (ah_mpres_trans H HB mo mo1 mo2 MP1 MP2))|].
      split; [exact FZ|]. split; [exact HI2|]. split; [exact PLB|]. split; [rewrite CF0 in AL2; lia|].
      assert (XCL : forall A k, (ff <= A /\ A + k <= ff + 2672 + 8) \/ (ff + 2672 + 16 <= A /\ A + k <= ff + 4096)
                               \/ (sh ff <= A /\ A + k <= sh ff + 512) -> 0 <= k ->
                      xclient_range H (as_lb_remove H pv LBk) S1 [(ff + 2672 + 8, ff + 2672 + 16)] A k).
      { intros A k K Hk. split.
        - right; right; right; right. destruct K as [K|[K|K]]; [left; unfold AFS_SIZE in *; lia | left; unfold AFS_SIZE in *; lia | right; left; lia].
        - apply Forall_cons; [| apply Forall_nil]. cbn. destruct K as [K|[K|K]]; try lia; destruct F16; lia. }
      split.
      { destruct W3341 as (X1 & X2 & X). split; [lia|]. split; [lia|]. intros i Hi.
        destruct (XP2 (sh ff + 334 + i) ltac:(lia) ltac:(eapply xclient_range_addr; [apply (XCL (sh ff + 334) 3); [right; right; lia | lia] | lia]))
          as [_ W]. apply W. apply X. exact Hi. }
      split; [exists j; eapply xpres_rw_cells; [exact XP2 | exact CJ1 | apply XCL; [right; right; cbn; lia | cbn; lia]]|].
      eapply xpres_rw_cells; [exact XP2 | exact CFR1 | split; [left; lia | apply Forall_cons; [unfold top_fr; cbn; right; lia | apply Forall_nil]]].
  Qed.
End TopV.
