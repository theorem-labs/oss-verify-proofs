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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat LbB_SR LbB_Conv LbB_Ctx LbB_RG2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TopDefs LbB_TopKit LbB_TopH2 LbB_TopT1 LbB_TopT LbB_TopV.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section TopC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Definition vec_st (e : hent H) (LBk : list block) (m : mem) (n P : Z) (pv : bptr) (pc : bptr) (A : Z) : Prop :=
    (n = 0 /\ P = 0 /\ Permutation LBk ((pc, A, 64) :: e_LB e))
    \/ (1 <= n <= 2 ^ 24 /\ Permutation LBk ((pv, P, 4 * n) :: (pc, A, 64) :: e_LB e)
        /\ (exists bs, rw_cells asegs m P [CB (Z.to_nat (4 * n)) bs]) /\ addressable m P (4 * n)).

  Definition cut_CD (e : hent H) (c : config) : Prop :=
    exists (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (F' : bvmap 5 word) (fc' : bv 32)
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m' : mem) (n P : Z) (pv pc : bptr)
           (A : Z) (j1 j2 : list byte),
      as_VIS H sk (cfg_ms c) = MS (mkR x1 (Z_to_bv 64 (eS1 e)) (e_gp e) (e_tp e) x5 x6 x7 (Z_to_bv 64 (eSP e)) (Z_to_bv 64 (eS1 e))
                                       x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 A) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                  F' (Z_to_bv 64 TOP_PO_RA) fc' None m' (seg_rom asegs)
      /\ as_AKREL H sk c /\ as_MPRES H (e_mo e) (cfg_model c)
      /\ FPSteps.frm_zero fc'
      /\ hinv H e ff fp XSc sk LBk m'
      /\ as_AL H sk >= as_AL H (e_s e) - top_cost (e_N e)
      /\ (exists j, rw_cells asegs m' (sh ff + 4) [CB 313 j])
      /\ rw_cells asegs m' (ff + 2672) [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))]
      /\ SHAD m' (ff + 2672) (repeat (b8 0) 3)
      /\ rw_cells asegs m' (eS1 e + 24) (top_fr A ff) /\ rw_cells asegs m' (eS1 e + 80) (top_vd ff (e_D e))
      /\ rw_cells asegs m' A [C4 (wz RG_ENV); CB 44 j1; C8 (wz 0); CB 8 j2] /\ addressable m' A CTX_SZ
      /\ vec_st e LBk m' n P pv pc A.

  Lemma seg_CD : forall (e : hent H) (c : config), hpre H e -> cut_CD e c -> as_SR H (hpost H e) c.
  Proof.
    intros e [msF mo] HP CT.
    destruct CT as (ff & fp & XSc & sk & LBk & F' & fc' & x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x22
                    & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m' & n & P & pv & pc & A & j1 & j2 & VIS & KR & MP & FZ & HI & AL
                    & (j & CJ) & CV & SV & CFR & CVD & CC & CA & VEC).
    cbn [cfg_ms cfg_model] in VIS, MP.
    pose proof (rt_bp_base H HH) as HB. pose proof (rt_bp_cost H HH) as (CF0 & _).
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    pose proof (hpre_geo H e HP) as (_ & LO & SSHI & SHIH & SP16 & TP).
    pose proof (hinv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SPB & BB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & _ & _ & _ & ALs).
    set (SP := eSP e) in *. set (S1 := eS1 e) in *. set (lo := e_lo e) in *.

    assert (INc : In (pc, A, 64) LBk).
    { destruct VEC as [(_ & _ & PERM) | (_ & PERM & _)]; apply (Permutation_in _ (Permutation_sym PERM)); [left | right; left]; reflexivity. }
    pose proof (ah_blocks H HB _ _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI) INc) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof (ah_nodup H HB _ _ _ (hinv_rh H _ _ _ _ _ _ _ HI)) as ND.
    pose proof (hchain_call H HB e ff fp XSc sk LBk m' HP HI) as (CHN & CHU).
    destruct (hinv_er H e ff fp XSc sk LBk m' HI) as (errv & ER).

    eapply (ahh_evt_then H HB); [exact KR | exact VIS | apply hCD1 |].
    intros msF1 mo1 KR1 MP1 VIS1. hnf in VIS1.
    eapply (ah_seq H HB).
    { eapply (ctx_destroy_sr H HB (Z_to_bv 64 TOP_CD_RA) (Z_to_bv 64 S1)) with (A := A) (p := pc) (evz := RG_ENV) (lo := lo) (B := e_B e)
          (errv := errv) (CH := (SP, bv_unsigned (e_ra e)) :: e_CH e) (j1 := j1) (j2 := j2);
        rewrite ?HLib.u64_of_Z by lia;
        [exact VIS1 | reflexivity | exact (hinv_rh H _ _ _ _ _ _ _ HI) | exact KR1 | exact INc | rewrite CF0; lia
        | exact CC | exact CA | exact (hinv_ra H _ _ _ _ _ _ _ HI) | lia | exact (proj1 (stk_split asegs m' lo S1 SP (hinv_stk H _ _ _ _ _ _ _ HI) ltac:(lia)))
        | exact CE | unfold AFREE_STACK; lia | exact ER | exact (hinv_mi H _ _ _ _ _ _ _ HI) | exact TP
        | clear - S32; Z.div_mod_to_equations; lia | lia | exact (hinv_ac H _ _ _ _ _ _ _ HI)
        | rewrite HLib.u64_of_Z by lia; exact CHN | | exact CHU].
      rewrite HLib.u64_of_Z by (unfold TOP_CD_RA; lia).
      exact (htrace H e APC0_FREE [TOP_CD_RA] HP ltac:(unfold TOP_PF; cbn; left; reflexivity)). }
    intros [msF2 mo2] P2.
    destruct P2 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & s' & VIS2 & KR2 & MP2 & MI2 & ST2 & ER2 & RA2
                    & AP2 & RH2 & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, MP2. rewrite HLib.u64_of_Z in ST2, AP2 by lia.
    rewrite (ret_pc_even TOP_CD_RA ltac:(unfold TOP_CD_RA; lia) eq_refl) in VIS2.
    assert (INC : forall b, In b (e_LB e) -> In b (as_lb_remove H pc LBk)).
    { intros b Hb. apply (lb_remove_keep H HB); [exact ND | |].
      - destruct VEC as [(_ & _ & PERM) | (_ & PERM & _)]; apply (Permutation_in _ (Permutation_sym PERM)); [right | right; right]; exact Hb.
      - intros E. destruct VEC as [(_ & _ & PERM) | (_ & PERM & _)].
        + pose proof (Permutation_NoDup (Permutation_map blk_id PERM) ND) as ND2. cbn [map] in ND2. apply NoDup_cons_iff in ND2 as [X _].
          apply X. cbn [blk_id fst]. rewrite <- E. apply in_map. exact Hb.
        + pose proof (Permutation_NoDup (Permutation_map blk_id PERM) ND) as ND2. cbn [map] in ND2. apply NoDup_cons_iff in ND2 as [_ ND3].
          apply NoDup_cons_iff in ND3 as [X _]. apply X. cbn [blk_id fst]. rewrite <- E. apply in_map. exact Hb. }
    assert (XP2 : xpres H (as_lb_remove H pc LBk) S1 [] m' m2) by exact (xpres_of_apres H _ _ [] _ _ AP2).
    assert (RF2 : as_RFS H ((6, ff, fp) :: e_LF e) m2) by exact (RFS_via_apres H HB _ _ _ _ _ (hinv_rf H _ _ _ _ _ _ _ HI) AP2).
    assert (HI2 : hinv H e ff fp (XSc ++ []) s' (as_lb_remove H pc LBk) m2).
    { eapply (hinv_sr H HB e ff fp XSc [] [] sk LBk (as_lb_remove H pc LBk)); try eassumption; [apply Forall_nil | apply Forall_nil | exists errv; exact ER2]. }
    rewrite app_nil_r in HI2.
    assert (PLB : Permutation LBk ((pc, A, 64) :: as_lb_remove H pc LBk)) by exact (lb_remove_perm H HB pc A 64 LBk ND INc).
    apply (seg_VD H HH); [exact HP|].
    exists ff, fp, XSc, s', (as_lb_remove H pc LBk), F', fc', (Z_to_bv 64 TOP_CD_RA), t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7,
      (Z_to_bv 64 A), x19, x20, x21, x22, x23, x24, x25, x26, x27, t3, t4, t5, t6, m2, n, P, pv, A.
    cbn [cfg_ms cfg_model]. split; [exact VIS2|]. split; [exact KR2|].
    split; [exact (ah_mpres_trans H HB (e_mo e) mo mo2 MP (ah_mpres_trans H HB mo mo1 mo2 MP1 MP2))|].
    split; [exact FZ|]. split; [exact HI2|]. split; [rewrite CF0 in AL2; lia|].

    assert (APF : forall A0 k, ff <= A0 -> A0 + k <= ff + 4096 -> aclient_range H (as_lb_remove H pc LBk) S1 A0 k)
      by (intros A0 k K1 K2; right; right; right; right; left; unfold AFS_SIZE in *; lia).
    assert (APS : forall A0 k, sh ff <= A0 -> A0 + k <= sh ff + 512 -> aclient_range H (as_lb_remove H pc LBk) S1 A0 k)
      by (intros A0 k K1 K2; right; right; right; right; right; left; lia).
    split; [exists j; eapply (apres_rw_cells H); [exact AP2 | exact CJ | apply APS; cbn; lia]|].
    split; [eapply (apres_rw_cells H); [exact AP2 | exact CV | apply APF; cbn; lia]|].
    split.
    { destruct SV as (S1a & S1b & U). split; [exact S1a|]. split; [exact S1b|].
      replace (sh (ff + 2672)) with (sh ff + 334) in * by (rewrite <- (sh_add8 ff 334); f_equal).
      eapply (apres_u8arr H); [exact AP2 | exact U | rewrite repeat_length; apply APS; cbn; lia]. }
    split; [eapply (apres_rw_cells H); [exact AP2 | exact CFR | left; lia]|].
    split; [eapply (apres_rw_cells H); [exact AP2 | exact CVD | left; lia]|].
    destruct VEC as [(N0 & P0 & PERM) | (NR & PERM & (bs & CB0) & ADP)].
    - left. split; [exact N0|]. split; [exact P0|].
      apply Permutation_cons_inv with (a := (pc, A, 64)). exact (perm_trans (Permutation_sym PLB) PERM).
    - right. split; [exact NR|].
      assert (INv : In (pv, P, 4 * n) LBk) by (apply (Permutation_in _ (Permutation_sym PERM)); left; reflexivity).
      assert (Hpv : pv <> pc).
      { intros E. subst pv. pose proof (Permutation_NoDup (Permutation_map blk_id PERM) ND) as ND2. cbn [map] in ND2.
        apply NoDup_cons_iff in ND2 as [X _]. apply X. left. reflexivity. }
      assert (INv2 : In (pv, P, 4 * n) (as_lb_remove H pc LBk)) by (apply (lb_remove_keep H HB); [exact ND | exact INv | exact Hpv]).
      split.
      { apply Permutation_cons_inv with (a := (pc, A, 64)).
        eapply perm_trans; [exact (Permutation_sym PLB)|]. eapply perm_trans; [exact PERM|]. apply perm_swap. }
      split.
      + exists bs. eapply (apres_rw_cells H); [exact AP2 | exact CB0 | eapply (aclient_range_block H); [exact INv2 | lia |]].
        destruct CB0 as [[[X _] _] _]. cbn [cells_size csize]. rewrite Nat.add_0_r. lia.
      + eapply (apres_addressable H); [exact AP2 | exact ADP | exact INv2].
  Qed.
End TopC.
