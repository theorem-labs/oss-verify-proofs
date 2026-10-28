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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_DiagStmt LbB_PmDS.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma ro_cells_of_fld8 : forall M a v, CRep.fld ASEGS M a 8 v -> 0 <= a -> a + 8 <= 2 ^ 64 -> ro_cells asegs M a [C8 (Z_to_bv 64 v)].
Proof.
  intros M a v HF H0 H1. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_of_rdn; [lia | rewrite length_le8; lia | rewrite length_le8; exact HF].
Qed.

Section PD.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.

  Lemma pd_p_obj : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl spal k,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal -> k mod 8 = 0 -> 0 <= k -> k + 8 <= 288 ->
    ds_obj H (PMLF H w) m (wa_s1 w) (wa_p w + k) 8 /\ True.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl spal k OK X Hk8 Hk0 Hk1. split; [|exact I].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as [PR1 PR2].
    destruct (p_frame H (HHd H HHbp) w OK) as (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (proj1 (proj2 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X))) as AD.
    destruct (addressable_split8 m (wa_p w) PARSER_SIZE k AD ltac:(unfold PARSER_SIZE; reflexivity) Hk8 ltac:(unfold PARSER_SIZE; lia)) as [_ AD1].
    destruct (addressable_split8 m (wa_p w + k) (PARSER_SIZE - k) 8 AD1 ltac:(unfold PARSER_SIZE; Z.div_mod_to_equations; lia) eq_refl ltac:(unfold PARSER_SIZE; lia)) as [AD2 _].
    unfold ds_obj. split; [exact AD2|].
    split; [Z.div_mod_to_equations; lia|].
    split; [right; exists fp0; split; [right; exact Hfp0 | unfold PARSER_SIZE in *; lia]|].
    split; [lia|]. split; [unfold PARSER_SIZE in *; lia|].
    split; [left; pose proof (wk_s1 H w OK) as (WS1 & _); pose proof (wk_stack H w OK) as (S1 & S2 & _); unfold ADS_STACK, APM_STACK, PARSER_SIZE in *; lia|].
    unfold app_obj. destruct PA as [(L1 & L2)|(L1 & L2)]; unfold aapp_lo, aapp_hi in *; unfold AAPP_HI, AIMG_TOP, AHI_LO, ALOWSH_LO, PARSER_SIZE in *; lia.
  Qed.

  Lemma pm_pdiag : forall (entry : Z) (with_err : bool), pdiag_stmtA H LINV ds_repA entry with_err ->
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
    ds_K H LINV w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
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
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact (proj1 (pd_p_obj w s LB LBs m mo c ins tbl ftbl spal 8 OK X eq_refl ltac:(lia) ltac:(lia))).
      - pose proof (p_range H w OK) as [PR1 PR2]. pose proof aceil_facts as ((ACF1 & ACF2) & _ & _). apply ro_cells_of_fld8; [exact (xa_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | unfold AIMG_TOP in PR1; lia | unfold PARSER_SIZE in PR2; lia].
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact (proj1 (pd_p_obj w s LB LBs m mo c ins tbl ftbl spal 80 OK X eq_refl ltac:(lia) ltac:(lia))).
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
    eapply (K ms1 mo1 _ F1 fc1 s1 LB1 m1 []); [exact KR1 | exact VIS1 | apply rfull_mkR | exact FZ1 | exact X1 | | split; [reflexivity | exact DS1] |].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - intros k cs Hk Hkc Hdj RW. eapply (ff_cells_xpres H HHbp w m m1 LB [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] XS k cs OK RFS1 FXS XP);
        [| exact Hk | exact Hkc | exact RW]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia.
  Qed.
End PD.
