(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_DiagStmt LbB_PmDS LbB_PmPD LbB_PmVops LbB_PmU2K LbB_PmWKit LbB_PcSrc.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section StrX.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.

  Lemma pm_put_cseq_src : put_cseq_stmtA H LINV ds_repA ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (dso ret p n err len : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 APUT_CSEQ) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + dso) -> PropExec.getr R 11%bv = Z_to_bv 64 p -> PropExec.getr R 12%bv = Z_to_bv 64 n ->
    obj_sh_ok ins dso DS_SIZE = true -> 24 <= dso -> dso + DS_SIZE <= 16376 ->
    Forall (fun ke => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    0 <= n -> (0 < p \/ n = 0) ->
    srcx_keep H (wa_LB0 w ++ LBs) (PMLF H w) (wa_s1 w) [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] m p n ->
    in_app_mem p (p + n) -> (p + n <= wa_s1 w - ADS_STACK \/ wa_s1 w <= p) ->
    (forall a, p <= a < p + n -> ~ (wa_ff w + dso <= a < wa_ff w + dso + DS_SIZE) /\ ~ in_block TB a) ->
    ds_repA LB m (wa_ff w + dso) err len TB -> len + n <= DS_MAXLEN -> spal + ds_cost (len + n) <= PM_RESERVE ->
    ds_K H LINV w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
         (fun LB1 m1 TB1 R1 => ds_repA LB1 m1 (wa_ff w + dso) err (len + n) TB1 /\ PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + dso))
         (spal + ds_cost (len + n)) Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HCSEQ w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret p n err len Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 G11 G12 Ods D1 D2 FTD Hn Hp0 SRC HAPP HSTK HDJ DS0 Hlen Hsc K.
    pose proof aceil_facts as ((ACe1 & ACe2) & ACe3 & ACe4).
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (wk_s1 H w OK) as (WS1 & _).
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [TBO TBL].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    destruct (ff_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal dso DS_SIZE OK X Ods D1 D2) as [OBd IFd].
    pose proof (tb_split H LINV w s LB LBs m mo c ins tbl ftbl TB spal X) as PK.
    assert (Hcost : 0 <= ds_cost (len + n)) by (pose proof (proj2 (proj2 (proj2 (proj2 (dla_def _ _ DSL _ _ _ _ _ _ DS0))))); unfold ds_cost; lia).
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H (HHd H HHbp)).
    { eapply (HCSEQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (wa_LB0 w ++ LBs) (PMLF H w)
                ((wa_sp0 w, wa_ra w) :: wa_CH w) (wa_lo w) (wa_B w) (wa_shi w) errv (wa_ff w + dso) err len p n TB).
      - eapply (pm_ds_pre H LINV w s LB LBs m mo c ins tbl ftbl TB spal msF F fc APUT_CSEQ (ds_cost (len + n)) TB);
          [exact OK | exact X | exact KR | exact VIS | exact FZ | exact G2 | exact G8 | exact G4 | rewrite G1, u64_of_Z by lia; exact Hr2
          | rewrite G4; exact ERR | exact TBO | exact Hcost | exact Hsc].
      - exact G10.
      - exact G11.
      - exact G12.
      - exact DS0.
      - exact PK.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBd.
      - exact IFd.
      - exact Hn.
      - exact Hp0.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact SRC.
      - exact HAPP.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact HSTK.
      - exact HDJ.
      - exact Hlen.
      - exact (proj1 (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl TB spal OK X)).
      - exact (proj2 (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl TB spal OK X)). }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & RES & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & (TB1 & XF & DS1 & TBO1 & WR1) & FXS & XP
                      & RFS1 & AC1 & S01 & LI1 & AL1).
    cbn [cfg_ms cfg_model] in *.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in STK1 by (unfold AAPP_HI in *; lia).
    rewrite G2, u64_of_Z in XP by (unfold AAPP_HI in *; lia). rewrite G4 in ERR1.
    pose proof (proj1 (dla_blocks _ _ DSL _ _ _ _ _ _ DS1)) as TBL1.
    assert (X1 : PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl TB1 (spal + ds_cost (len + n))).
    { eapply (pmxa_after_ds H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal (wa_ff w + dso) s1 LB1 m1 mo1 XS (wa_LB0 w ++ LBs) TB1
                (ds_cost (len + n)) OK X Hknn Hfk).
      - unfold xp_ok; cbn [fst snd]. left. split; [unfold DS_SIZE in *; lia|]. split; [lia|]. split; [unfold DS_SIZE in *; lia|].
        eapply Forall_impl; [| exact FTD]. intros [k e] Hk. cbn [fst snd] in *. lia.
      - exact RH1.
      - exact MP1.
      - exact MI1.
      - exact STK1.
      - exists errv1. exact ERR1.
      - exact RA1.
      - exact RFS1.
      - exact AC1.
      - exact S01.
      - exact LI1.
      - exact FXS.
      - exact XP.
      - exact WR1.
      - exact AL1.
      - exact Hcost.
      - exact Hsc.
      - exact PK.
      - exact (xfer_kept _ _ _ _ _ PK XF).
      - exact TBO1.
      - exact TBL1. }
    eapply (K ms1 mo1 _ F1 fc1 s1 LB1 m1 TB1); [exact KR1 | exact VIS1 | apply rfull_mkR | exact FZ1 | exact X1 | | split; [exact DS1 | ] |].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - cbn. exact (RES _ eq_refl).
    - intros k cs Hk Hkc Hdj RW. eapply (ff_cells_xpres H HHbp w m m1 (wa_LB0 w ++ LBs) [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] XS k cs OK RFS1 FXS XP);
        [| exact Hk | exact Hkc | exact RW]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia.
  Qed.
  Lemma HHx : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma ff23_srcx : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal (dso : Z) (bs : list byte) (n : Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    obj_sh_ok ins 6736 24 = true -> rw_cells asegs m (wa_ff w + 6737) [CB 23 bs] -> 0 <= n <= 23 ->
    (6760 <= dso \/ dso + DS_SIZE <= 6736) -> 0 <= dso -> dso + DS_SIZE <= 16384 ->
    srcx_keep H (wa_LB0 w ++ LBs) (PMLF H w) (wa_s1 w) [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] m (wa_ff w + 6737) n.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal dso bs n OK XA Hok RW Hn HD HD0 HD1.
    pose proof (pmw_frame_facts H w OK) as (E1 & E2 & E3 & _). change (fsz PM_FCLASS) with 16384 in *.
    pose proof (xp_geom H HHx w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). unfold AIMG_TOP, AFS_HDR in E1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof RW as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Lbs _].
    assert (FULL : srcx_keep H (wa_LB0 w ++ LBs) (PMLF H w) (wa_s1 w) [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] m (wa_ff w + 6737) 23).
    { exists bs. split; [rewrite Lbs; reflexivity|].
      intros m' XS s' LB' AC' MI' FXS XP RH' INC'.
      assert (FOf : fsobj H (PMLF H w) (wa_ff w) 16384)
        by (right; exists (PM_FCLASS, wa_ff w, wa_fp w); split; [left; reflexivity | unfold ff_addr, ff_class; cbn [fst snd]; change (fsz PM_FCLASS) with 16384; lia]).
      assert (A0 : 0 <= wa_ff w) by lia. assert (A1 : 0 <= 16384) by lia. assert (A2 : wa_ff w + 16384 <= AAPP_HI) by (unfold AAPP_HI in *; lia).
      pose proof (xp_scr_obj H HHx w m XS (wa_ff w) 16384 OK (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA) FXS FOf A0 A1 A2 FA) as [SXf SXfs].
      assert (XRf : xclient_range H (wa_LB0 w ++ LBs) (wa_s1 w) ([(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] ++ XS) (wa_ff w + 6737) 23).
      { apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia |]. apply Forall_app. split.
        - apply Forall_cons; [cbn [fst snd]; unfold DS_SIZE in *; lia | apply Forall_nil].
        - eapply Forall_impl; [| exact SXf]. intros iv Hiv. cbn beta in *. lia. }
      assert (XRfsh : xclient_range H (wa_LB0 w ++ LBs) (wa_s1 w) ([(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] ++ XS) (sh (wa_ff w)) PM_NSH).
      { apply (xr_fssh H w); [exact OK | apply sh_mono; unfold AFS_HDR in *; lia | |].
        - assert (sh (wa_ff w + 11584) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
          assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia). unfold PM_NSH. lia.
        - apply Forall_app. split.
          + apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold PM_NSH, DS_SIZE in *. rewrite Q13. unfold SHBASE in *. rewrite Q13 in Q6. lia.
          + eapply Forall_impl; [| exact SXfs]. intros iv Hiv. cbn beta in *. unfold PM_NSH, nsh in *. change ((16384 + 7) / 8) with 2048 in Hiv. lia. }
      assert (FSHL : Z.of_nat (length (pm_fsh ins)) = PM_NSH) by (unfold pm_fsh; rewrite length_map, pm_fsh_len; reflexivity).
      assert (XRfsh' : xclient_range H (wa_LB0 w ++ LBs) (wa_s1 w) ([(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] ++ XS) (sh (wa_ff w)) (Z.of_nat (length (pm_fsh ins))))
        by (rewrite FSHL; exact XRfsh).
      pose proof (xpres_SHAD H (wa_LB0 w ++ LBs) (wa_s1 w) _ m m' (wa_ff w) (pm_fsh ins) XP (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA) XRfsh') as FSH'.
      pose proof (xpres_rw_cells H (wa_LB0 w ++ LBs) (wa_s1 w) _ m m' (wa_ff w + 6737) [CB 23 bs] XP RW XRf) as RW'.
      pose proof RW' as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
      split; [exact HB|]. split.
      - apply (addressable_accessible m' (wa_ff w + 6736) 24 (wa_ff w + 6737) 23); [| lia | lia | unfold AAPP_HI in *; lia].
        exact (ff_addressable m' (wa_ff w) ins 6736 24 FSH' Hok).
      - apply (ff_shvis m' (wa_ff w) ins 6737 23 FSH'); unfold AAPP_HI in *; lia. }
    pose proof (srcx_keep_sub H _ _ _ _ m (wa_ff w + 6737) 23 0 n FULL ltac:(lia) ltac:(lia) ltac:(lia)) as S0.
    rewrite Z.add_0_r in S0. exact S0.
  Qed.

  Definition ffs_src (w : pmwA H) (m : mem) (ins : list nat) (dso p n : Z) : Prop :=
    p = wa_ff w + 6737 /\ 0 <= n <= 22 /\ obj_sh_ok ins 6736 24 = true
    /\ (6760 <= dso \/ dso + DS_SIZE <= 6736)
    /\ exists bs, rw_cells asegs m (wa_ff w + 6737) [CB 23 bs].

  Lemma pm_put_cseq_ffs : put_cseq_stmtA H LINV ds_repA ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (dso ret p n err len : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 APUT_CSEQ) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + dso) -> PropExec.getr R 11%bv = Z_to_bv 64 p -> PropExec.getr R 12%bv = Z_to_bv 64 n ->
    obj_sh_ok ins dso DS_SIZE = true -> 24 <= dso -> dso + DS_SIZE <= 16376 ->
    Forall (fun ke => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    ffs_src w m ins dso p n ->
    ds_repA LB m (wa_ff w + dso) err len TB -> len + n <= DS_MAXLEN -> spal + ds_cost (len + n) <= PM_RESERVE ->
    ds_K H LINV w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
         (fun LB1 m1 TB1 R1 => ds_repA LB1 m1 (wa_ff w + dso) err (len + n) TB1 /\ PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + dso))
         (spal + ds_cost (len + n)) Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HCSEQ w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret p n err len Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 G11 G12 Ods D1 D2 FTD (Ep & Hn & Hok & HD & bs & RW) DS0 Hlen Hsc K.
    subst p.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xp_geom H HHx w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof (wk_s1 H w OK) as (WS1 & _). pose proof (wk_stack H w OK) as (WS2 & WS3 & _). unfold APM_STACK in WS3.
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [TBO TBL].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    eapply (pm_put_cseq_src HCSEQ w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret (wa_ff w + 6737) n err len Q
              OK X Hknn Hfk KR VIS RF FZ G1 Hr2 Hr G2 G8 G4 G10 G11 G12 Ods D1 D2 FTD).
    - lia.
    - left. pose proof (pmw_bounds H w OK) as BNDp. lia.
    - apply (ff23_srcx w s LB LBs m mo c ins tbl ftbl TB spal dso bs n OK X Hok RW); [lia | exact HD | lia | lia].
    - unfold in_app_mem. destruct FA as [(L1 & L2)|(L1 & L2)]; unfold aapp_lo, aapp_hi in *;
        unfold ALOWSH_LO, AHI_LO, AAPP_HI, AIMG_TOP, ASHADOW_BASE, AFS_HDR, AFS_SIZE in *; [left | right]; lia.
    - left. unfold ADS_STACK. lia.
    - intros a Ha. split; [unfold DS_SIZE in *; lia|].
      intros (b & Hb & Hr0). assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; right; exact Hb).
      pose proof (blk_apart_ff H HHx w s LB m b OK RH HbL) as BF. lia.
    - exact DS0.
    - exact Hlen.
    - exact Hsc.
    - exact K.
  Qed.

End StrX.

Section StrXK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.

  Definition ds_KX (w : pmwA H) (LBs : list block) (c : pmc) ins tbl ftbl (R : bvmap 5 word) (ret ds : Z) (m : mem)
      (P : list block -> mem -> list block -> bvmap 5 word -> Prop) (spal' : Z) (Q : config -> Prop) : Prop :=
    forall msF1 mo1 R1 F1 fc1 (s1 : as_St H) LB1 m1 TB1 (XS : list (Z * Z)) (LBk : list block),
      as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 ret) fc1 None m1 (seg_rom asegs) ->
      rfull R1 -> frm_zero fc1 ->
      PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl TB1 spal' ->
      (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
      P LB1 m1 TB1 R1 ->
      (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
                    (wa_ff w + k + Z.of_nat (cells_size cs) <= ds \/ ds + DS_SIZE <= wa_ff w + k) ->
                    rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
      as_RFS H (PMLF H w) m1 -> Forall (fs_scratch H (PMLF H w)) XS ->
      xpres H LBk (wa_s1 w) ([(ds, ds + DS_SIZE)] ++ XS) m m1 ->
      (forall b, In b LBs -> In b LBk) ->
      as_SR H Q (mkCfg msF1 mo1).

  Lemma pm_pdiagX : forall (entry : Z) (with_err : bool), pdiag_stmtA H LINV ds_repA entry with_err ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl spal msF R F fc
      (dso ret err : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 entry) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + dso) -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_p w) ->
    PropExec.getr R 12%bv = Z_to_bv 64 (err mod 2 ^ 64) ->
    (if with_err then - 2 ^ 31 <= err < 0 else err = - 4) ->

    obj_sh_ok ins dso DS_SIZE = true -> 24 <= dso -> dso + DS_SIZE <= 16376 ->
    Forall (fun ke => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    ds_KX w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
         (fun LB1 m1 TB1 _ => TB1 = [] /\ ds_repA LB1 m1 (wa_ff w + dso) err 0 []) spal Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros entry with_err HPD w s LB LBs m mo c ins tbl ftbl spal msF R F fc dso ret err Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 G11 G12 Herr Ods D1 D2 FTD K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    destruct (ff_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl [] spal dso DS_SIZE OK X Ods D1 D2) as [OBd IFd].
    destruct (cons_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl [] spal OK X) as [OBc CONS].
    pose proof (wk_pcons H w OK) as PCo.
    destruct (wk_cin H w OK) as (fc0 & Hfc0 & CF1 & CF2).
    pose proof (lf0_apart_ff H w fc0 (wa_cons w) 48 OK Hfc0 CF1 CF2) as CFF.
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H (HHd H HHbp)).
    { eapply (HPD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (PMLF H w)
                ((wa_sp0 w, wa_ra w) :: wa_CH w) (wa_lo w) (wa_B w) (wa_shi w) errv
                (wa_ff w + dso) (wa_p w) (wa_cons w) (c_icount c) err).
      - eapply (pm_ds_pre H LINV w s LB LBs m mo c ins tbl ftbl [] spal msF F fc entry 0 []);
          [exact OK | exact X | exact KR | exact VIS | exact FZ | exact G2 | exact G8 | exact G4 | rewrite G1, u64_of_Z by lia; exact Hr2
          | rewrite G4; exact ERR | apply lb_own_nil | lia | pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (_ & _ & _ & S1 & S2); lia].
      - exact G10.
      - exact G11.
      - exact G12.
      - exact Herr.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact (proj1 (pd_p_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl spal 8 OK X eq_refl ltac:(lia) ltac:(lia))).
      - pose proof (p_range H w OK) as [PR1 PR2]. pose proof aceil_facts as ((ACF1 & ACF2) & _ & _). apply ro_cells_of_fld8; [exact (xa_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | unfold AIMG_TOP in PR1; lia | unfold PARSER_SIZE in PR2; lia].
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact (proj1 (pd_p_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl spal 80 OK X eq_refl ltac:(lia) ltac:(lia))).
      - pose proof (p_range H w OK) as [PR1 PR2]. pose proof aceil_facts as ((ACF1 & ACF2) & _ & _). apply ro_cells_of_fld8; [exact (xa_icount _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | unfold AIMG_TOP in PR1; lia | unfold PARSER_SIZE in PR2; lia].
      - pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (B1 & B2 & _). pose proof (wk_n H w OK). lia.
      - exact (proj2 (proj2 (wk_capp H w OK))).
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBd.
      - pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (W0 & W1 & W2). change (fsz PM_FCLASS) with 16384 in *.
        split; [lia|]. split; [lia|]. intros i Hi. replace (wa_ff w + dso + i) with (wa_ff w + (dso + i)) by lia. apply W2. unfold DS_SIZE in *. lia.
      - exact IFd.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBc.
      - exact CONS.
      - intros a Ha Hb. unfold DS_SIZE in *. destruct CFF as [CF|CF]; lia. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & _ & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & (PL1 & DS1 & WR1) & FXS & XP
                      & RFS1 & AC1 & S01 & LI1 & AL1).
    cbn [cfg_ms cfg_model] in *.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in STK1 by (unfold AAPP_HI in *; lia).
    rewrite G2, u64_of_Z in XP by (unfold AAPP_HI in *; lia). rewrite G4 in ERR1.
    assert (X1 : PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl [] (spal + 0)).
    { eapply (pmxa_after_ds H HHbp LINV w s LB LBs m mo c ins tbl ftbl [] spal (wa_ff w + dso) s1 LB1 m1 mo1 XS LB [] 0
                OK X Hknn Hfk); try eassumption.
      - unfold xp_ok; cbn [fst snd]. left. split; [unfold DS_SIZE in *; lia|]. split; [lia|]. split; [unfold DS_SIZE in *; lia|].
        eapply Forall_impl; [| exact FTD]. intros [k e] Hk. cbn [fst snd] in *. lia.
      - exists errv1. exact ERR1.
      - lia.
      - pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (_ & _ & _ & S1 & S2). lia.
      - apply Permutation_refl.
      - apply lb_own_nil.
      - cbn [length]. lia. }
    rewrite Z.add_0_r in X1.
    assert (MEMk : forall b0, In b0 LBs -> In b0 LB).
    { intros b0 Hb0. pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
      apply (Permutation_in _ (Permutation_sym OWN1)). apply in_app_iff; right; apply in_app_iff; left; exact Hb0. }
    eapply (K ms1 mo1 _ F1 fc1 s1 LB1 m1 [] XS LB); [exact KR1 | exact VIS1 | apply rfull_mkR | exact FZ1 | exact X1 | | split; [reflexivity | exact DS1] | | exact RFS1 | exact FXS | exact XP | exact MEMk].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - intros k cs Hk Hkc Hdj RW. eapply (ff_cells_xpres H HHbp w m m1 LB [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] XS k cs OK RFS1 FXS XP);
        [| exact Hk | exact Hkc | exact RW]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia.
  Qed.

  Lemma pm_put_cseq_imgX : put_cseq_stmtA H LINV ds_repA ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (dso ret p n err len : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 APUT_CSEQ) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + dso) -> PropExec.getr R 11%bv = Z_to_bv 64 p -> PropExec.getr R 12%bv = Z_to_bv 64 n ->
    obj_sh_ok ins dso DS_SIZE = true -> 24 <= dso -> dso + DS_SIZE <= 16376 ->
    Forall (fun ke => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    0 <= n -> AIMG_LO + 64 <= p -> p + n + 64 <= AIMG_TOP ->
    (forall m', ACONST m' -> accessible m' p n) ->
    (exists bs, length bs = Z.to_nat n /\ forall m', mem_inv asegs m' -> bytes_at asegs m' p bs) ->
    ds_repA LB m (wa_ff w + dso) err len TB -> len + n <= DS_MAXLEN -> spal + ds_cost (len + n) <= PM_RESERVE ->
    ds_KX w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
         (fun LB1 m1 TB1 R1 => ds_repA LB1 m1 (wa_ff w + dso) err (len + n) TB1 /\ PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + dso))
         (spal + ds_cost (len + n)) Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HCSEQ w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret p n err len Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 G11 G12 Ods D1 D2 FTD Hn Hp0 Hp ACC BYT DS0 Hlen Hsc K.
    pose proof aceil_facts as ((ACe1 & ACe2) & ACe3 & ACe4).
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (wk_s1 H w OK) as (WS1 & _).
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [TBO TBL].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    destruct (ff_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal dso DS_SIZE OK X Ods D1 D2) as [OBd IFd].
    pose proof (tb_split H LINV w s LB LBs m mo c ins tbl ftbl TB spal X) as PK.
    assert (Hcost : 0 <= ds_cost (len + n)) by (pose proof (proj2 (proj2 (proj2 (proj2 (dla_def _ _ DSL _ _ _ _ _ _ DS0))))); unfold ds_cost; lia).
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H (HHd H HHbp)).
    { eapply (HCSEQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (wa_LB0 w ++ LBs) (PMLF H w)
                ((wa_sp0 w, wa_ra w) :: wa_CH w) (wa_lo w) (wa_B w) (wa_shi w) errv (wa_ff w + dso) err len p n TB).
      - eapply (pm_ds_pre H LINV w s LB LBs m mo c ins tbl ftbl TB spal msF F fc APUT_CSEQ (ds_cost (len + n)) TB);
          [exact OK | exact X | exact KR | exact VIS | exact FZ | exact G2 | exact G8 | exact G4 | rewrite G1, u64_of_Z by lia; exact Hr2
          | rewrite G4; exact ERR | exact TBO | exact Hcost | exact Hsc].
      - exact G10.
      - exact G11.
      - exact G12.
      - exact DS0.
      - exact PK.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBd.
      - exact IFd.
      - exact Hn.
      - left. unfold AIMG_LO in *. lia.
      - destruct BYT as (bs & LEN & BYT'). exists bs. split; [exact LEN|]. intros m' XS s' LB' ACm MIm _ _ _ _.
        split; [exact (BYT' m' MIm)|]. split; [exact (ACC m' ACm)|]. eapply ACONST_shvis; [exact ACm | lia | lia | lia].
      - unfold in_app_mem, ASHADOW_BASE, AIMG_TOP, AIMG_LO in *. left. lia.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). left. unfold ADS_STACK, AIMG_TOP in *. lia.
      - intros a Ha. split.
        + unfold AIMG_TOP, AFS_HDR in *. lia.
        + intros (b & Hb & Hr0). assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; right; exact Hb).
          pose proof (ah_blocks H (HHd H HHbp) _ _ _ _ RH HbL) as (_ & _ & _ & BT & _). lia.
      - exact Hlen.
      - exact (proj1 (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl TB spal OK X)).
      - exact (proj2 (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl TB spal OK X)). }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & RES & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & (TB1 & XF & DS1 & TBO1 & WR1) & FXS & XP
                      & RFS1 & AC1 & S01 & LI1 & AL1).
    cbn [cfg_ms cfg_model] in *.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in STK1 by (unfold AAPP_HI in *; lia).
    rewrite G2, u64_of_Z in XP by (unfold AAPP_HI in *; lia). rewrite G4 in ERR1.
    pose proof (proj1 (dla_blocks _ _ DSL _ _ _ _ _ _ DS1)) as TBL1.
    assert (X1 : PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl TB1 (spal + ds_cost (len + n))).
    { eapply (pmxa_after_ds H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal (wa_ff w + dso) s1 LB1 m1 mo1 XS (wa_LB0 w ++ LBs) TB1
                (ds_cost (len + n)) OK X Hknn Hfk).
      - unfold xp_ok; cbn [fst snd]. left. split; [unfold DS_SIZE in *; lia|]. split; [lia|]. split; [unfold DS_SIZE in *; lia|].
        eapply Forall_impl; [| exact FTD]. intros [k e] Hk. cbn [fst snd] in *. lia.
      - exact RH1.
      - exact MP1.
      - exact MI1.
      - exact STK1.
      - exists errv1. exact ERR1.
      - exact RA1.
      - exact RFS1.
      - exact AC1.
      - exact S01.
      - exact LI1.
      - exact FXS.
      - exact XP.
      - exact WR1.
      - exact AL1.
      - exact Hcost.
      - exact Hsc.
      - exact PK.
      - exact (xfer_kept _ _ _ _ _ PK XF).
      - exact TBO1.
      - exact TBL1. }
    eapply (K ms1 mo1 _ F1 fc1 s1 LB1 m1 TB1 XS (wa_LB0 w ++ LBs)); [exact KR1 | exact VIS1 | apply rfull_mkR | exact FZ1 | exact X1 | | split; [exact DS1 | ] | | exact RFS1 | exact FXS | exact XP | intros b0 Hb0; apply in_app_iff; right; exact Hb0].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - cbn. exact (RES _ eq_refl).
    - intros k cs Hk Hkc Hdj RW. eapply (ff_cells_xpres H HHbp w m m1 (wa_LB0 w ++ LBs) [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] XS k cs OK RFS1 FXS XP);
        [| exact Hk | exact Hkc | exact RW]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia.
  Qed.
  Lemma HHk : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma nodup_app_disj : forall (A : Type) (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
  Proof.
    induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [destruct H1|]. cbn [app] in ND. inversion ND as [|? ? NI ND']; subst.
    destruct H1 as [->|H1]; [apply NI; apply in_or_app; right; exact H2 | exact (IH l2 x ND' H1 H2)].
  Qed.

  Lemma blk_keep_xpres : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal (m1 : mem) (XS : list (Z * Z)) (LBk : list block)
      (dso : Z) (pid : bptr) (d asz : Z) (bs : list byte),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    In (pid, d, asz) LBs -> (forall b, In b LBs -> In b LBk) ->
    24 <= dso -> dso + DS_SIZE <= 16376 ->
    Forall (fun ke : Z * SymExec3.SX2.expr => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    as_RFS H (PMLF H w) m1 -> Forall (fs_scratch H (PMLF H w)) XS ->
    xpres H LBk (wa_s1 w) ([(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] ++ XS) m m1 ->
    bytes_at asegs m d bs -> Z.of_nat (length bs) <= asz -> SHAD m d (shadow_of asz) ->
    bytes_at asegs m1 d bs /\ SHAD m1 d (shadow_of asz).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m1 XS LBk dso pid d asz bs OK X HIn INC D1 D2 FTD RFS1 FXS XP BY BL SH.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    assert (HInL : In (pid, d, asz) LB) by (apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; left; exact HIn).
    pose proof (ah_blocks H HHk _ _ _ _ RH HInL) as (R0 & R16 & Rn & RI & RC & RF' & RAPP). cbn [blk_addr blk_size fst snd] in *.
    assert (FX : Forall (xp_ok H w ftbl) [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)]).
    { apply Forall_cons; [| apply Forall_nil]. unfold xp_ok. left. cbn [fst snd]. split; [unfold DS_SIZE in *; lia|]. split; [lia|]. split; [unfold DS_SIZE in *; lia|].
      eapply Forall_impl; [| exact FTD]. intros [k e] Hk. cbn [fst snd] in *. lia. }
    assert (L0 : 0 <= Z.of_nat (length bs)) by lia.
    pose proof (xr_kept_blk H HHk w s LB m LBk ftbl _ XS m1 pid d asz d (Z.of_nat (length bs)) OK RH HInL (INC _ HIn) RFS1 FXS FX (Z.le_refl d) ltac:(lia) L0) as XR1.
    assert (N0 : 0 <= nsh asz) by (unfold nsh; Z.div_mod_to_equations; lia).
    pose proof (xr_kept_blksh H HHk w s LB m LBk ftbl _ XS m1 pid d asz (sh d) (nsh asz) OK RH HInL (INC _ HIn) RFS1 FXS FX (Z.le_refl _) (Z.le_refl _) N0) as XR2.
    split.
    - exact (xpres_bytes_at H LBk (wa_s1 w) _ m m1 d bs XP BY XR1).
    - apply (xpres_SHAD H LBk (wa_s1 w) _ m m1 d (shadow_of asz) XP SH). rewrite shadow_of_length by lia. exact XR2.
  Qed.

  Lemma blk_keep_fsh : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal (m1 : mem) (pid : bptr) (d asz : Z) (bs : list byte),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    In (pid, d, asz) LBs ->
    munch [(wa_ff w / 8 + 2147450880, wa_ff w / 8 + 2147452928)] m m1 -> wmono asegs m m1 ->
    bytes_at asegs m d bs -> Z.of_nat (length bs) <= asz -> SHAD m d (shadow_of asz) ->
    bytes_at asegs m1 d bs /\ SHAD m1 d (shadow_of asz).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m1 pid d asz bs OK X HIn MU WM BY BL SH.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    assert (HInL : In (pid, d, asz) LB) by (apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; left; exact HIn).
    pose proof (ah_blocks H HHk _ _ _ _ RH HInL) as (R0 & R16 & Rn & RI & RC & RF' & RAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof (blk_apart_ff H HHk w s LB m _ OK RH HInL) as BF. cbn [blk_addr blk_size fst snd] in BF.
    pose proof (xp_geom H HHk w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    assert (D1 : disjoint_from [(wa_ff w / 8 + 2147450880, wa_ff w / 8 + 2147452928)] d asz).
    { cbn [disjoint_from]. split; [| exact Logic.I].
      destruct RAPP as [(L1 & L2)|(L1 & L2)]; destruct FA as [(L3 & L4)|(L3 & L4)]; unfold aapp_lo, aapp_hi in *;
        unfold ALOWSH_LO, AHI_LO, AIMG_TOP, AFS_HDR, AFS_SIZE in *; Z.div_mod_to_equations; lia. }
    assert (D2 : disjoint_from [(wa_ff w / 8 + 2147450880, wa_ff w / 8 + 2147452928)] (sh d) (nsh asz)).
    { cbn [disjoint_from]. split; [| exact Logic.I]. unfold sh, nsh, ASHADOW_BASE.
      destruct BF as [BF|BF]; Z.div_mod_to_equations; lia. }
    split.
    - destruct BY as (B0 & B1 & BB). split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (BB i Hi). unfold mrd, wa.
      rewrite (MU (Z_to_bv 64 (d + Z.of_nat i))); [reflexivity|]. rewrite u64_of_Z by lia.
      cbn [outside]. split; [| exact Logic.I]. cbn [disjoint_from] in D1. destruct D1 as [D1 _]. lia.
    - eapply SHAD_transport; [exact SH | exact MU | exact WM |]. rewrite shadow_of_length by lia. exact D2.
  Qed.

  Definition blk_src (w : pmwA H) (LBs : list block) (m : mem) (p n : Z) : Prop :=
    0 <= p /\ 0 <= n < 262140
    /\ exists (pid : bptr) (asz : Z) (bs : list byte),
         In (pid, p, asz) LBs /\ n <= asz /\ length bs = Z.to_nat n /\ bytes_at asegs m p bs /\ SHAD m p (shadow_of asz).

  Lemma pm_put_cseq_blk : put_cseq_stmtA H LINV ds_repA ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (dso ret p n err len : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 APUT_CSEQ) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + dso) -> PropExec.getr R 11%bv = Z_to_bv 64 p -> PropExec.getr R 12%bv = Z_to_bv 64 n ->
    obj_sh_ok ins dso DS_SIZE = true -> 24 <= dso -> dso + DS_SIZE <= 16376 ->
    Forall (fun ke => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    blk_src w LBs m p n ->
    ds_repA LB m (wa_ff w + dso) err len TB -> len + n <= DS_MAXLEN -> spal + ds_cost (len + n) <= PM_RESERVE ->
    ds_K H LINV w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
         (fun LB1 m1 TB1 R1 => ds_repA LB1 m1 (wa_ff w + dso) err (len + n) TB1 /\ PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + dso))
         (spal + ds_cost (len + n)) Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HCSEQ w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret p n err len Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 G11 G12 Ods D1 D2 FTD (Hp & Hn & pid & asz & bs & HIn & Hna & Lbs & BY & SH) DS0 Hlen Hsc K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xp_geom H HHk w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof (wk_s1 H w OK) as (WS1 & _). pose proof (wk_stack H w OK) as (WS2 & WS3 & _). unfold APM_STACK in WS3.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    assert (HInL : In (pid, p, asz) LB) by (apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; left; exact HIn).
    pose proof (ah_blocks H HHk _ _ _ _ RH HInL) as (R0 & R16 & Rn & RI & RC & RF' & RAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof (blk_apart_ff H HHk w s LB m _ OK RH HInL) as BF. cbn [blk_addr blk_size fst snd] in BF.
    eapply (pm_put_cseq_src H HHbp LINV ds_repA DSL HCSEQ w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret p n err len Q
              OK X Hknn Hfk KR VIS RF FZ G1 Hr2 Hr G2 G8 G4 G10 G11 G12 Ods D1 D2 FTD).
    - lia.
    - left. lia.
    - apply (srcx_keep_blk H HHk (wa_LB0 w ++ LBs) (PMLF H w) (wa_s1 w) _ m p n pid p asz bs m);
        [ apply in_app_iff; right; exact HIn | lia | lia | lia | exact Lbs | exact BY
        | apply (addressable_accessible m p asz p n); [split; [lia | exact SH] | lia | lia | unfold AAPP_HI in *; lia]
        | exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
        | apply Forall_cons; [cbn [fst snd]; unfold DS_SIZE in *; lia | apply Forall_nil]
        | apply Forall_cons; [| apply Forall_nil] ].
      cbn [fst snd]. unfold sh, nsh, ASHADOW_BASE, DS_SIZE in *.
      destruct RAPP as [(L1 & L2)|(L1 & L2)]; destruct FA as [(L3 & L4)|(L3 & L4)]; unfold aapp_lo, aapp_hi in *;
        unfold ALOWSH_LO, AHI_LO, AIMG_TOP, AFS_HDR, AFS_SIZE in *; Z.div_mod_to_equations; lia.
    - unfold in_app_mem. destruct RAPP as [(L1 & L2)|(L1 & L2)]; unfold ALOWSH_LO, AHI_LO, AAPP_HI, AIMG_TOP, ASHADOW_BASE in *; [left | right]; lia.
    - left. unfold ADS_STACK. lia.
    - intros a Ha. split; [unfold DS_SIZE in *; lia|].
      intros (b & Hb & Hr0).
      assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; right; exact Hb).
      destruct (Z.eq_dec (blk_id b) pid) as [E|NE].
      + pose proof (ah_nodup H HHk _ _ _ RH) as ND.
        pose proof (Permutation_NoDup (Permutation_map blk_id OWN1) ND) as ND'. rewrite !map_app in ND'.
        apply List.NoDup_app_remove_l in ND'.
        apply (nodup_app_disj _ (map blk_id LBs) (map blk_id TB) pid ND').
        * apply in_map_iff. exists (pid, p, asz). split; [reflexivity | exact HIn].
        * apply in_map_iff. exists b. split; [exact E | exact Hb].
      + pose proof (ah_disj H HHk _ _ _ b (pid, p, asz) RH HbL HInL NE) as DJ. cbn [blk_addr blk_size blk_id fst snd] in DJ. lia.
    - exact DS0.
    - exact Hlen.
    - exact Hsc.
    - exact K.
  Qed.

End StrXK.
