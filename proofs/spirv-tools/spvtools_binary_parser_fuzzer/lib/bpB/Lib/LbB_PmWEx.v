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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_DiagStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmDS LbB_PmWKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WEx.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.

  Let HH : asan_rt_hyps H := proj1 HHbp.

  Lemma pmxa_after_ex : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal s' LB' m' mo' XS cost,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_RHEAP H s' LB' m' -> as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) -> as_rauxv_ok H m' (wa_B w) ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) -> LINV m' ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H LB (wa_s1 w) ([(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] ++ XS) m m' ->
    as_AL H s' >= as_AL H s - cost -> 0 <= cost -> spal + cost <= PM_RESERVE ->
    Permutation LB' LB ->
    PMXAT H LINV w s' LB' LBs m' mo' c ins tbl ftbl TB (spal + cost).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal s' LB' m' mo' XS cost OK X0 Hknn Hfk
           RH' MP' MI' STK' ERR' RA' RFS' AC' S0' LI' FXS XP AL Hc Hsc PLB.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (A1 & A2 & A3 & A4).
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [TBO TBL].
    assert (Is : forall b, In b LBs -> In b LB) by (intros b Hb; apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; left; exact Hb).
    assert (It : forall b, In b TB -> In b LB) by (intros b Hb; apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; right; exact Hb).
    assert (Is' : forall b, In b LBs -> In b LB') by (intros b Hb; apply (Permutation_in _ (Permutation_sym PLB)); exact (Is b Hb)).
    assert (FXD : Forall (xp_ok H w ftbl) [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)]) by (apply Forall_cons; [right; reflexivity | apply Forall_nil]).
    destruct (pmc_xp_keep H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal LB' m' LB [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] XS OK X0 RFS' FXS XP FXD Is Is') as (U1 & U2 & U3 & V1 & V2 & V3 & SHc).
    eapply (pmxa_xp H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal s' LB' LBs m' mo' c TB (spal + cost) LB [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] XS
              OK X0 Hknn RH' MP' MI' STK' ERR' RA' RFS' AC' S0' LI' FXS XP FXD); try reflexivity.
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      replace (RtB_Td.ATDLOC + 8 - RtB_Td.ATDLOC) with 8 by lia. exact (RtB_Td.td_wr_any m').
    - exact Hfk.
    - intros b Hb; exact Hb.
    - intros b Hb. apply (Permutation_in _ (Permutation_sym OWN1)). apply in_app_iff. left. exact Hb.
    - eapply Permutation_trans; [exact PLB | exact OWN1].
    - exact OWN2.
    - eapply (lb_own_xpres_xp H HHbp w s LB m m' LB XS LBs ftbl OK (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) RFS' FXS Is Is [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)]);
        [exact FXD | exact XP | exact (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)].
    - exact (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0).
    - eapply (lb_own_xpres_xp H HHbp w s LB m m' LB XS TB ftbl OK (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) RFS' FXS It It [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)]);
        [exact FXD | exact XP | exact TBO].
    - exact TBL.
    - lia.
    - exact A2.
    - lia.
    - exact U1.
    - exact U2.
    - exact U3.
    - exact V1.
    - exact V2.
    - exact V3.
    - exact SHc.
  Qed.

  Lemma parser_ds_obj : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    ds_obj H (PMLF H w) m (wa_s1 w) (wa_p w) 288.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal OK X.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as [PR1 PR2].
    destruct (p_frame H HH w OK) as (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    unfold ds_obj. split; [exact (proj1 (proj2 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)))|].
    split; [Z.div_mod_to_equations; lia|].
    split; [right; exists fp0; split; [right; exact Hfp0 | unfold PARSER_SIZE in *; lia]|].
    split; [lia|]. split; [unfold PARSER_SIZE in *; lia|].
    split; [left; pose proof (wk_s1 H w OK) as (WS1 & _); pose proof (wk_stack H w OK) as (S1 & S2 & _); unfold ADS_STACK, APM_STACK, PARSER_SIZE in *; lia|].
    unfold app_obj. destruct PA as [(L1 & L2)|(L1 & L2)]; unfold aapp_lo, aapp_hi in *; unfold AAPP_HI, AIMG_TOP, AHI_LO, ALOWSH_LO, PARSER_SIZE in *; lia.
  Qed.

  Lemma pm_exhausted : exhausted_stmtA H LINV ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl spal msF R F fc (ret inst_offset opcode type : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AEXHAUSTED) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_p w) -> PropExec.getr R 11%bv = Z_to_bv 64 inst_offset ->
    PropExec.getr R 12%bv = Z_to_bv 64 opcode -> PropExec.getr R 13%bv = Z_to_bv 64 type ->
    0 <= inst_offset < 2 ^ 63 -> 0 <= opcode < 2 ^ 16 -> 0 <= type < 2 ^ 32 ->
    spal + 2 ^ 20 <= PM_RESERVE ->
    In (APC0_FREE, [0xfd148; 0xf8f14; ret]) PM_PF ->
    (forall msF1 mo1 m1 R1 F1 fc1 (s1 : as_St H) (LB1 : list block),
       as_AKREL H s1 (mkCfg msF1 mo1) ->
       as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 ret) fc1 None m1 (seg_rom asegs) -> rfull R1 -> frm_zero fc1 ->
       PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl [] (spal + 2 ^ 20) ->
       (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
       PropExec.getr R1 10%bv = Z_to_bv 64 (2 ^ 64 - 4) ->
       (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
          rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HEX w s LB LBs m mo c ins tbl ftbl spal msF R F fc ret inst_offset opcode type Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 G11 G12 G13 Hio Hop Hty HSP HPF K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND. pose proof (wk_n H w OK) as WN.
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (SC1 & SC2 & SC3 & SC4).
    destruct (cons_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl [] spal OK X) as [OBc CONS].
    pose proof (parser_ds_obj w s LB LBs m mo c ins tbl ftbl [] spal OK X) as OBp.
    pose proof (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as PD.

    assert (ML3 : lb_small LB + 3 * 64512 <= RT_SMALL_MAX /\ Z.of_nat (length LB) + 3 <= RT_CNT_MAX /\ nlarge LB + 3 <= RT_LARGE_MAX).
    { pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
      pose proof (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (M1 & M2 & M3).
      pose proof (wk_meas0 H w OK) as (W1 & W2 & W3).
      rewrite (lb_small_perm _ _ OWN1), (nlarge_perm _ _ OWN1), (Permutation_length OWN1).
      rewrite !lb_small_app, !nlarge_app, !length_app. cbn [lb_small nlarge fold_right length].
      pose proof (nlarge_nonneg (wa_LB0 w)). pose proof (nlarge_nonneg LBs).
      unfold RT_SMALL_MAX, RT_CNT_MAX, RT_LARGE_MAX, po_small, po_cnt, po_large in *. lia. }
    destruct ML3 as (ML1 & ML2 & ML3).
    assert (C8p : forall k v, 0 <= k -> k + 8 <= PARSER_SIZE -> fld ASEGS m (wa_p w + k) 8 v -> rw_cells asegs m (wa_p w + k) [C8 (Z_to_bv 64 v)]).
    { intros k v Hk Hk8 Fk. apply rw_C8_of_rdn; [lia | unfold PARSER_SIZE in *; lia | exact Fk |].
      apply (wr_at_of_mdef m (wa_p w) PARSER_SIZE k 8 PD); unfold PARSER_SIZE in *; lia. }
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H HH).
    { eapply (HEX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (PMLF H w)
                ((wa_sp0 w, wa_ra w) :: wa_CH w) (wa_lo w) (wa_B w) (wa_shi w) errv
                (wa_p w) (wa_cons w) (wa_n w) (c_widx c) (c_icount c) inst_offset opcode type).
      - eapply (pm_ds_pre H LINV w s LB LBs m mo c ins tbl ftbl [] spal msF F fc AEXHAUSTED (2 ^ 20) []);
          [exact OK | exact X | exact KR | exact VIS | exact FZ | exact G2 | exact G8 | exact G4 | rewrite G1, u64_of_Z by lia; exact Hr2
          | rewrite G4; exact ERR | apply lb_own_nil | lia | lia].
      -
        rewrite G2, u64_of_Z by lia. pose proof (wk_stack H w OK) as (S1a & S2 & _). pose proof (wk_s1 H w OK) as (T1 & T2).
        unfold ADS_STACK, APM_STACK in *. lia.
      -
        pose proof (wk_lfb H w OK) as LFB. unfold PMLF. cbn [length]. unfold PM_FRAMES, DS_FRAMES in *. lia.
      - exact ML1.
      - exact ML2.
      - exact ML3.
      - rewrite G1, u64_of_Z by lia. eapply pf_ok_call; [exact (wk_pf H w OK) |].
        intros pp Hpp. cbn in Hpp. destruct Hpp as [<-|[]]. exact HPF.
      - exact G10.
      - exact G11.
      - exact G12.
      - exact G13.
      - exact Hio.
      - exact Hop.
      - exact Hty.
      - rewrite G2, u64_of_Z by lia. exact OBp.
      -
        pose proof (xp_geom H HH w OK) as (_ & _ & _ & _ & _ & _ & (f & Hf & PF1 & PF2 & _)).
        exists f. split; [right; exact Hf | split; [exact PF1 | unfold PARSER_SIZE in PF2; exact PF2]].
      - apply (C8p 8 (wa_cons w)); [lia | unfold PARSER_SIZE; lia | exact (xa_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
      - apply (C8p O_N (wa_n w)); [unfold O_N; lia | unfold O_N, PARSER_SIZE; lia | exact (xa_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
      - apply (C8p O_WIDX (c_widx c)); [unfold O_WIDX; lia | unfold O_WIDX, PARSER_SIZE; lia | exact (xa_widx _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
      - apply (C8p O_ICOUNT (c_icount c)); [unfold O_ICOUNT; lia | unfold O_ICOUNT, PARSER_SIZE; lia | exact (xa_icount _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)].
      - lia.
      - lia.
      - lia.
      - rewrite G2, u64_of_Z by lia. exact OBc.
      -
        destruct (wk_cin H w OK) as (fc0 & Hfc0 & CF1 & CF2).
        exists fc0. split; [right; exact Hfc0 | split; [exact CF1 | exact CF2]].
      - exact CONS.
      - exact (proj2 (proj2 (wk_capp H w OK))). }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & HA0 & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & PLB & FXS & XP
                      & RFS1 & AC1x & S01 & LI1 & AL1).
    cbn [cfg_ms cfg_model] in *.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in STK1 by lia.
    rewrite G2, u64_of_Z in XP by lia. rewrite G4 in ERR1.
    assert (X1 : PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl [] (spal + 2 ^ 20)).
    { eapply (pmxa_after_ex w s LB LBs m mo c ins tbl ftbl [] spal s1 LB1 m1 mo1 XS (2 ^ 20) OK X Hknn Hfk); try eassumption.
      all: first [exists errv1; exact ERR1 | lia]. }
    rewrite (HA0 _ eq_refl) in VIS1.
    eapply (K ms1 mo1 m1 _ F1 fc1 s1 LB1); [exact KR1 | exact VIS1 | apply rfull_mkR | exact FZ1 | exact X1 | | reflexivity |].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - intros k cs Hk Hkc RW. eapply (ff_cells_xpres H HHbp w m m1 LB [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] XS k cs OK RFS1 FXS XP); [| exact Hk | exact Hkc | exact RW].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right.
      pose proof (xp_geom H HH w OK) as (F1' & F2' & F3' & _). unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR in *. lia.
  Qed.
End WEx.
