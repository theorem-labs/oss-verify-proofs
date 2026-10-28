(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_ContStmt LbB_DiagStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmDS LbB_PmVup LbB_PmWKit LbB_PmWG LbB_PmWPT LbB_SegKit LbB_StrPb LbB_MkStr LbB_PmStr.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section DEL.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis HOWN : rt_own H.

  Let HH : asan_rt_hyps H := proj1 HHbp.

  Ltac feedH K := match type of K with ?A -> _ => let P := fresh "P" in assert (P : A); [| specialize (K P); clear P] end.

  Lemma lbr_perm_cons : forall (p : bptr) (A n : Z) (L : list block),
    List.NoDup (map blk_id L) -> In (p, A, n) L -> Permutation L ((p, A, n) :: as_lb_remove H p L).
  Proof.
    intros p A n L ND Hin. destruct (in_split _ _ Hin) as (l1 & l2 & E). subst L.
    rewrite (lbr_split H HH p A n l1 l2 ND). apply Permutation_sym. apply Permutation_middle.
  Qed.

  Lemma nodup_ids_perm : forall (L M : list block), Permutation L M -> List.NoDup (map blk_id L) -> List.NoDup (map blk_id M).
  Proof. intros L M P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P | exact ND]. Qed.

  Lemma nodup_ids_app_r : forall (L1 L2 : list block), List.NoDup (map blk_id (L1 ++ L2)) -> List.NoDup (map blk_id L2).
  Proof. intros L1 L2 ND. rewrite map_app in ND. exact (List.NoDup_app_remove_l _ _ ND). Qed.

  Lemma pmxa_after_del : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl spal s' m' mo' (pid : bptr) (d asz : Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    c_tr c = [(d, asz)] -> pm_bud (wa_n w) c -> In (pid, d, asz) LBs ->
    as_RHEAP H s' (as_lb_remove H pid LB) m' -> as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) -> as_rauxv_ok H m' (wa_B w) -> ACONST m' ->
    apres H (as_lb_remove H pid LB) (wa_s1 w) m m' ->
    as_AL H s' >= as_AL H s ->
    spal + pm_phi_blocks [(d, asz)] <= PM_RESERVE ->
    PMXAT H LINV w s' (as_lb_remove H pid LB) (as_lb_remove H pid LBs) m' mo' (set_trA c []) ins tbl ftbl []
          (spal + pm_phi_blocks [(d, asz)])
    /\ pm_bud (wa_n w) (set_trA c []).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl spal s' m' mo' pid d asz OK X0 Hknn Hfk Htr BUD HinS
           RH' MP' MI' STK' ERR' RA' AC' AP AL HSP.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2]. rewrite app_nil_r in OWN1.
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (A1 & A2 & A3 & A4).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (wk_n H w OK) as WN.
    pose proof (ah_nodup H HH _ _ _ RH) as ND.
    pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    set (x := (pid, d, asz)) in *.
    set (LB' := as_lb_remove H pid LB) in *. set (LBs' := as_lb_remove H pid LBs) in *.
    assert (HinLB : In x LB) by (apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; exact HinS).
    assert (NDs : List.NoDup (map blk_id LBs)) by (apply (nodup_ids_app_r (wa_LB0 w)); exact (nodup_ids_perm _ _ OWN1 ND)).
    pose proof (lbr_perm_cons pid d asz LB ND HinLB) as PL. fold x LB' in PL.
    pose proof (lbr_perm_cons pid d asz LBs NDs HinS) as PS. fold x LBs' in PS.

    assert (OWN1' : Permutation LB' (wa_LB0 w ++ LBs' ++ [])).
    { rewrite app_nil_r. apply Permutation_cons_app_inv with (a := x).
      eapply Permutation_trans; [apply Permutation_sym; exact PL|].
      eapply Permutation_trans; [exact OWN1|]. apply Permutation_app_head. exact PS. }
    assert (PHI0 : pm_phi_blocks [(d, asz)] >= 0).
    { unfold pm_phi_blocks. cbn [fold_right snd]. destruct (ICM_LARGE <? asz); unfold ICM_LARGE in *; [| lia].
      destruct BUD as (_ & _ & _ & _ & _ & _ & _ & _ & Btrp). specialize (Btrp (d, asz) ltac:(rewrite Htr; left; reflexivity)). cbn [snd] in Btrp. lia. }
    assert (CB0 : c_blocks (set_trA c []) ++ [(d, asz)] = c_blocks c).
    { rewrite <- (set_trA_id c) at 2. rewrite Htr. change (set_trA c [(d, asz)]) with (set_trA (set_trA c []) [(d, asz)]).
      rewrite (c_blocks_set_tr (set_trA c []) [(d, asz)] eq_refl). reflexivity. }
    assert (OWN2' : Permutation (lbl LBs') (c_blocks (set_trA c []))).
    { apply Permutation_cons_inv with (a := (d, asz)).
      change ((d, asz) :: lbl LBs') with (lbl (x :: LBs')).
      eapply Permutation_trans; [apply Permutation_map; apply Permutation_sym; exact PS|]. fold (lbl LBs).
      eapply Permutation_trans; [exact OWN2|]. rewrite <- CB0. apply Permutation_sym. apply Permutation_cons_append. }
    assert (BUD' : pm_bud (wa_n w) (set_trA c [])).
    { apply pm_bud_set_tr; [exact BUD | unfold HRep.Zlength; cbn; lia | intros b []]. }
    split; [| exact BUD'].
    assert (Is' : forall b, In b LBs' -> In b LB').
    { intros b Hb. apply (Permutation_in _ (Permutation_sym OWN1')). apply in_app_iff. right. apply in_app_iff. left. exact Hb. }
    assert (I0' : forall b, In b (wa_LB0 w) -> In b LB').
    { intros b Hb. apply (Permutation_in _ (Permutation_sym OWN1')). apply in_app_iff. left. exact Hb. }
    assert (IL : forall b, In b LB' -> In b LB) by (intros b Hb; exact (L3 pid LB b Hb)).

    assert (XP : xpres H LB' (wa_s1 w) ([] ++ []) m m') by (apply xpres_of_apres; exact AP).
    assert (RFS' : as_RFS H (PMLF H w) m') by exact (RFS_via_apres H HH _ _ _ _ _ (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) AP).
    assert (S0' : stack0 m' (wa_lo w) (wa_shi w)) by exact (stack0_xpres H _ _ _ _ _ _ _ XP (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (Forall_nil _)).
    assert (LI' : LINV m').
    { apply (LINV_cl m m' (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)). apply (xpres_img H LB' (wa_s1 w) [] m m' XP). apply Forall_nil. }
    assert (OWN' : lb_own LB' m') by exact (HOWN s' LB' m' RH').
    assert (FXS : Forall (fs_scratch H (PMLF H w)) []) by apply Forall_nil.
    assert (FXD : Forall (xp_ok H w ftbl) []) by apply Forall_nil.

    assert (BLK : forall A n, In (A, n) (c_blocks (set_trA c [])) -> exists q, In (q, A, n) LB').
    { intros A n Hin. apply (Permutation_in _ (Permutation_sym OWN2')) in Hin. destruct (lbl_in_inv LBs' A n Hin) as [q Hq].
      exists q. exact (Is' _ Hq). }
    pose proof (p_range H w OK) as [PR1 PR2]. pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmc_keep_gen (wa_p w) (lbl LB) (lbl LB') m m' (set_trA c [])
                (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
                (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
                (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0))) as KG.
    feedH KG. { lia. }
    feedH KG. { unfold PARSER_SIZE in *. lia. }
    feedH KG.
    { intros a Ha.
      assert (XC : xclient H LB' (wa_s1 w) ([] ++ []) a).
      { eapply (xclient_range_addr H); [apply (xr_parser H HH w LB' ftbl [] [] m' (a - wa_p w) 1 OK RFS' FXS FXD); unfold O_M1, PARSER_SIZE in *; lia | lia]. }
      exact (proj1 (XP a ltac:(unfold O_M1, PARSER_SIZE in *; lia) XC)). }
    feedH KG.
    { intros A n a Hin Ha. destruct (BLK A n Hin) as (q & Hq).
      pose proof (ah_blocks H HH _ _ _ _ RH (IL _ Hq)) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      assert (XC : xclient H LB' (wa_s1 w) ([] ++ []) a).
      { eapply (xclient_range_addr H); [apply (xr_blk H w LB' [] (q, A, n) a 1 Hq); [cbn [blk_addr fst snd]; lia | cbn [blk_addr blk_size fst snd]; lia | apply Forall_nil] | lia]. }
      exact (proj1 (XP a ltac:(lia) XC)). }
    feedH KG.
    { intros A n sbs Hin Hlen SH. destruct (BLK A n Hin) as (q & Hq).
      eapply (xpres_SHAD H); [exact XP | exact SH |].
      apply (xr_blksh H w LB' [] (q, A, n) (sh A) _ Hq); [cbn [blk_addr fst snd]; lia | cbn [blk_addr blk_size fst snd]; lia | apply Forall_nil]. }
    feedH KG.
    { intros b Hb _. destruct b as [A n]. destruct (BLK A n Hb) as (q & Hq). exact (lbl_in LB' q A n Hq). }
    destruct KG as (U1 & U2 & U3 & V1 & V2 & V3 & SHc).
    eapply (pmxa_xp H HH LINV w s LB LBs m mo c ins tbl ftbl [] spal s' LB' LBs' m' mo' (set_trA c []) [] (spal + pm_phi_blocks [(d, asz)]) LB' [] []
                OK X0 Hknn RH' MP' MI' STK' ERR' RA' RFS' AC' S0' LI' FXS XP FXD); try reflexivity.
    - apply Forall_nil.
    - exact Hfk.
    - exact IL.
    - exact I0'.
    - exact OWN1'.
    - exact OWN2'.
    - apply (lb_own_incl LB' _ m'); [exact Is' | exact OWN'].
    - apply (pm_meas_of_bud (wa_n w) (set_trA c []) LBs' ltac:(lia) BUD' OWN2').
    - apply lb_own_nil.
    - cbn. lia.
    - assert (PE : pm_phi c = pm_phi (set_trA c []) + pm_phi_blocks [(d, asz)]).
        { apply (pm_phi_eq_blocks (set_trA c []) c _ eq_refl). rewrite <- CB0. apply pm_phi_blocks_app. }
        lia.
    - apply pm_resv_of_bud; [exact WN | exact BUD'].
    - lia.
    - exact U1.
    - exact U2.
    - exact U3.
    - exact V1.
    - exact V2.
    - exact V3.
    - exact SHc.
  Qed.

  Lemma pm_str_del : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl spal msF R F fc (ret d asz : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    c_tr c = [(d, asz)] -> pm_bud (wa_n w) c ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AOPDEL2) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 d ->
    In (APC0_FREE, [ret]) PM_PF ->
    spal + pm_phi_blocks [(d, asz)] <= PM_RESERVE ->
    (forall msF1 mo1 m1 R1 (s1 : as_St H) (LB1 LBs1 : list block),
       as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s1 LB1 LBs1 m1 mo1 (set_trA c []) ins tbl ftbl [] (spal + pm_phi_blocks [(d, asz)]) ->
       pm_bud (wa_n w) (set_trA c []) ->
       (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
       (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
          rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl spal msF R F fc ret d asz Q OK X Hknn Hfk Htr BUD KR VIS RF
           G1 Hr2 Hr G2 G8 G4 G10 HPF HSP K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (wk_s1 H w OK) as [T1 T2].
    pose proof (wk_n H w OK) as WN.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4). pose proof (pm_phi_le_cap c) as PCc.
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK0.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK0 ltac:(lia)) as [STK1 STK2].

    assert (HinC : In (d, asz) (c_blocks c)).
    { rewrite <- (set_trA_id c). rewrite Htr. change (set_trA c [(d, asz)]) with (set_trA (set_trA c []) [(d, asz)]).
      rewrite (c_blocks_set_tr (set_trA c []) [(d, asz)] eq_refl). apply in_app_iff. right. left. reflexivity. }
    apply (Permutation_in _ (Permutation_sym OWN2)) in HinC. destruct (lbl_in_inv LBs d asz HinC) as [pid HinS].
    assert (HinLB : In (pid, d, asz) LB).
    { apply (Permutation_in _ (Permutation_sym OWN1)). apply in_app_iff. right. apply in_app_iff. left. exact HinS. }
    pose proof (ah_blocks H HH _ _ _ _ RH HinLB) as (R0 & R16 & Rn & RI & RC & RFb & RAPP). cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RFb, RAPP.
    pose proof (lb_own_In _ _ _ (HOWN s LB m RH) HinLB) as WRb. cbn [blk_addr blk_size fst snd] in WRb.
    destruct (rw_cells_of_wr_hi m d asz WRb RI Rn) as (bs & CELLS).
    destruct (sk_blk_shad H HH s m LB pid d asz RH HinLB) as (sbs & SHD & SHL).
    destruct (rt_bp_cost H HHbp) as [CFz CMz].

    assert (TRC : trace_ok (as_TR H) APC0_FREE (ret :: map snd ((wa_sp0 w, wa_ra w) :: wa_CH w))).
    { pose proof (proj1 (Forall_forall _ _) (wk_pf H w OK) _ HPF) as T. cbn [fst snd app] in T. cbn [map snd]. exact T. }
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H HH).
    { eapply (ah_opdel2 H HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m s LB pid d asz (wa_lo w) (wa_B w) errv mo
                ((wa_sp0 w, wa_ra w) :: wa_CH w) bs sbs).
      - exact VIS.
      - exact RH.
      - exact KR.
      - exact HinLB.
      - rewrite CFz. lia.
      - exact CELLS.
      - exact SHD.
      - exact SHL.
      - exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - rewrite G2, u64_of_Z by lia. lia.
      - rewrite G2, u64_of_Z by lia. exact STK1.
      - exact S1.
      - rewrite G2, u64_of_Z by lia. unfold AFREE_STACK, APM_STACK in *. lia.
      - rewrite G4. exact ERR.
      - exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - rewrite G4. exact (wk_tp H w OK).
      - rewrite G2, u64_of_Z by lia. clear - T2. Z.div_mod_to_equations. lia.
      - exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - rewrite G8, u64_of_Z by lia. exact (xa_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - rewrite G1, u64_of_Z by lia. exact TRC.
      - exact G10. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & s1
                      & VIS1 & KR1 & MP1 & MI1 & STKa & ERR1 & RA1 & AP & RH1 & AC1x & AL1).
    cbn [cfg_ms cfg_model] in *.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in STKa, AP by lia. rewrite G4 in ERR1.
    destruct (pmxa_after_del w s LB LBs m mo c ins tbl ftbl spal s1 m1 mo1 pid d asz OK X Hknn Hfk Htr BUD HinS
                RH1 MP1 MI1 STKa (ex_intro _ errv ERR1) RA1 AC1x AP ltac:(rewrite CFz in AL1; lia) HSP) as [X1 BUD1].
    eapply (K ms1 mo1 m1 _ s1 _ _); [exact KR1 | exact VIS1 | apply rfull_mkR | exact X1 | exact BUD1 | |].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - intros k cs Hk Hkc RW.
      eapply (ff_cells_xpres H HHbp w m m1 (as_lb_remove H pid LB) [] [] k cs OK); [| apply Forall_nil | apply xpres_of_apres; exact AP | apply Forall_nil | exact Hk | exact Hkc | exact RW].
      exact (RFS_via_apres H HH _ _ _ _ _ (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) AP).
  Qed.
End DEL.
