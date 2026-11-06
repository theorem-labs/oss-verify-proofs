(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HFpu HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition PM_HEAD  : Z := 0x67578.
Definition PM_LATCH : Z := 0x67570.
Definition PM_BODY  : Z := 0x67588.
Definition PM_RET   : Z := 0x673ec.
Definition PM_PRO   : Z := 0x67258.

Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation pm_exit := (PmCoreU1.pm_exit MI ST).

  Definition nodes (c : pmc) : Z := Zlen (t3c (c_m1 c)) + Zlen (t3c (c_m2 c)) + Zlen (t3c (c_m3 c)).
  Definition m3ok (ents : list (Z * (Z * Z))) : Prop := Forall (fun e => 0 <= snd (snd e) < 2 ^ 31) ents.
  Lemma m3ok_val : forall ents p k v, m3ok ents -> In (p, (k, v)) ents -> 0 <= v < 2 ^ 31.
  Proof using. intros ents p k v H Hin. exact (proj1 (Forall_forall _ _) H (p, (k, v)) Hin). Qed.

  Definition m2ok (ents : list (Z * (Z * (Z * Z * Z)))) : Prop :=
    Forall (fun e => 0 <= t3a (snd (snd e)) < 4 /\ 0 <= t3c (snd (snd e)) < 16) ents.
  Lemma m2ok_val : forall ents p k v, m2ok ents -> In (p, (k, v)) ents -> 0 <= t3a v < 4 /\ 0 <= t3c v < 16.
  Proof using. intros ents p k v H Hin. exact (proj1 (Forall_forall _ _) H (p, (k, v)) Hin). Qed.
  Definition macct (c : pmc) : Prop :=
    8 * t3b (c_m1 c) <= 16 * Zlen (t3c (c_m1 c)) + 504 /\ 8 * t3b (c_m2 c) <= 16 * Zlen (t3c (c_m2 c)) + 504 /\
    8 * t3b (c_m3 c) <= 16 * Zlen (t3c (c_m3 c)) + 504 /\ (m3ok (t3c (c_m3 c)) /\ m2ok (t3c (c_m2 c))).
  Definition lacc (c : pmc) : Prop :=
    2 * Zlen (t3c (c_m1 c)) <= c_widx c /\ 2 * Zlen (t3c (c_m2 c)) <= c_widx c /\ 3 * Zlen (t3c (c_m3 c)) <= c_widx c.
  Definition LI (w : pmw MI ST) A M model c R : Prop :=
    PMX w A M model c /\ c_tr c = [] /\ pm_bud (w_n w) c /\ loop_regs w R /\ loop_mem w M /\ c_icount c + 5 <= c_widx c /\ c_endian c < 2 /\ w_words w <> 0
    /\ nodes c + 1 <= c_widx c + 3 /\ macct c /\ lacc c.

  Lemma pm_ret : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (r : word),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> frm_zero (@fp_csr fx) ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 22%bv = r ->
    srealizes SEGS (cfg fx R 0x673ec M model) K.
  Proof using AC MI ST.
    intros w c0 K fx A M model c R r PS X Htr BUD FZ Qsp Qgp Qtp Hs6.
    destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    eapply (pm_exit w c0 K fx A M model c R r X Htr).
    - unfold OPND_SZ in B5. lia. - lia. - lia.
    - exact (ps_diag _ _ _ PS).
    - intros b Hb. eapply (pm_bud_sizes SEGS Ly.L MI ST w A M model c); [exact X | | exact Hb]. repeat (split; [assumption|]). exact B9.
    - intros cls. pose proof (x_geo X) as GEO'. destruct GEO' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gn' & _).
      pose proof (ps_cls _ _ _ PS) as HCL0.
      eapply (cnt_c_blocks SEGS Ly.L MI (proj1 HCL0) (proj1 (proj2 HCL0)) (proj2 (proj2 HCL0))); [repeat (split; [assumption|]); exact B9 | lia].
    - exact (ps_L0 _ _ _ PS).
    - exact FZ.
    - exact (ps_post _ _ _ PS).
    - exact Qsp.
    - rewrite (ps_gp _ _ _ PS). exact Qgp.
    - rewrite (ps_tp _ _ _ PS). exact Qtp.
    - exact Hs6.
    - exact (ps_ret _ _ _ PS). - exact (ps_R0ra _ _ _ PS). - exact (ps_R0sp _ _ _ PS).
  Qed.

  Lemma sextw_sxw : forall e, 0 <= e < 2 ^ 32 -> sext 64 (alu32 ALU_ADD (low32 (sxw e)) (low32 (Z_to_bv 64 0))) = sxw e.
  Proof using.
    intros e He. rewrite w_addw. unfold v_addw, sxw. rewrite (u64_of_Z 0) by lia. rewrite Z.add_0_r.
    rewrite (bv_swrap32_cases e) by lia. destruct (Z.ltb_spec e (2 ^ 31)).
    - rewrite u64_of_Z by lia. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec e (2 ^ 31)); [reflexivity | lia].
    - rewrite <- (Z_to_bv64_add_mod (e - 2 ^ 32)) at 1. rewrite u64_of_Z by lia.
      replace (e - 2 ^ 32 + 2 ^ 64) with (e + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite swrap32_shift.
      rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec e (2 ^ 31)); [lia|]. reflexivity.
  Qed.

  Lemma pm_latch_err : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (e : Z),
    PMS w c0 K -> PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> frm_zero (@fp_csr fx) ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    getr R 22%bv = sxw e -> 0 < e < 2 ^ 32 ->
    srealizes SEGS (cfg fx R 0x67570 M model) K.
  Proof using AC MI ST.
    intros w c0 K fx A M model c R e PS X Htr BUD FZ Qsp Qgp Qtp Hs6 He.
    pose proof (x_ms X) as MS.
    pose (E := Eseed R [Z_to_bv 64 (w_sp w); sxw e]).
    seedHR HR E [(2%bv, EVar 32); (22%bv, EVar 33)] R.
    assert (HK : know_ok SEGS E M []) by (apply Forall_nil).
    xruns HR HK 100%nat STOPS (SCR [true] [] []) 50%N.
    { split_scs; try sc_auto1. all: cbn [sc_denot]; evs. rewrite sextw_sxw by lia. change (Z_to_bv 64 0) with (sxw 0). rewrite br_ne_sxw by lia. bool_lia. }
    postrun. name_run HRn R1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (22%bv) G22. clear HRn HR HK. fixregs.
    rewrite Qgp in G3. rewrite Qtp in G4.
    eapply (pm_ret w c0 K fx A M model c R1); [exact PS | exact X | exact Htr | exact BUD | exact FZ | exact G2 | exact G3 | exact G4 | exact G22].
  Qed.

  Ltac lregs := unfold loop_regs; repeat split; first [assumption | etransitivity; [eassumption|]; first [assumption | reflexivity]].

  Lemma pm_latch_ok : forall (w : pmw MI ST) (fx : FPState) A M model c R K,
    PMX w A M model c -> loop_regs w R -> getr R 22%bv = Z_to_bv 64 0 ->
    (forall R', loop_regs w R' -> getr R' 22%bv = Z_to_bv 64 0 -> srealizes SEGS (cfg fx R' 0x67578 M model) K) ->
    srealizes SEGS (cfg fx R 0x67570 M model) K.
  Proof using AC MI ST.
    intros w fx A M model c R K X LR Hs6 HEADK. pose proof (x_ms X) as MS.
    destruct LR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    pose (E := Eseed R [Z_to_bv 64 (w_sp w)]).
    seedHR HR E [(2%bv, EVar 32); (22%bv, ELit 0)] R.
    assert (HK : know_ok SEGS E M []) by (apply Forall_nil).
    xruns HR HK 100%nat STOPS (SCR [] [] []) 50%N. { split_scs; try sc_auto1. }
    postrun. name_run HRn R1.
    rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
    rreg HRn (18%bv) G18. rreg HRn (19%bv) G19. rreg HRn (20%bv) G20. rreg HRn (21%bv) G21. rreg HRn (25%bv) G25. rreg HRn (22%bv) G22.
    clear HRn HR HK. fixregs.
    apply HEADK; [lregs | exact G22].
  Qed.

  Definition body_stmt (w : pmw MI ST) (c0 : parserC) (K : TSet) (fx : FPState) : Prop :=
    forall A M model c R,
      LI w A M model c R -> c_widx c < w_n w -> getr R 11%bv = Z_to_bv 64 (c_widx c) -> getr R 10%bv = Z_to_bv 64 (w_n w) ->
      (forall (fx' : FPState) A' M' model' c' R', frm_zero (@fp_csr fx') -> fconsts fx' -> LI w A' M' model' c' R' -> c_widx c < c_widx c' ->
          srealizes SEGS (cfg fx' R' 0x67578 M' model') K) ->
      srealizes SEGS (cfg fx R 0x67588 M model) K.

  Lemma pm_loop : forall (w : pmw MI ST) c0 K,
    PMS w c0 K -> (forall fx : FPState, frm_zero (@fp_csr fx) -> fconsts fx -> body_stmt w c0 K fx) ->
    forall (fx : FPState) A M model c R, frm_zero (@fp_csr fx) -> fconsts fx -> LI w A M model c R ->
    srealizes SEGS (cfg fx R 0x67578 M model) K.
  Proof using AC MI ST.
    intros w c0 K PS BODYf fx A M model c R FZ FC HLI.
    remember (Z.to_nat (w_n w - c_widx c)) as n eqn:Hn. revert fx FZ FC A M model c R HLI Hn.
    induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros fx FZ FC A M model c R HLI Hn. pose proof (BODYf fx FZ FC) as BODY.
    destruct HLI as (X & Htr & BUD & LR & LM & Hw5 & He2 & HwN & ACC & MACC).
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & [Gc2 Gcal] & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof LR as LR'. destruct LR' as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    destruct (Z.lt_ge_cases (c_widx c) (w_n w)) as [Hlt|Hge].
    -
      pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat (0x67588 :: STOPS) (SCR [true] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1.
      rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (8%bv) G8. rreg HRn (9%bv) G9.
      rreg HRn (18%bv) G18. rreg HRn (19%bv) G19. rreg HRn (20%bv) G20. rreg HRn (21%bv) G21. rreg HRn (25%bv) G25. rreg HRn (11%bv) G11. rreg HRn (10%bv) G10.
      clear HRn HR HK. fixregs.
      eapply (BODY A M model c R1).
      + split; [exact X|]. split; [exact Htr|]. split; [exact BUD|]. split; [| split; [exact LM | split; [exact Hw5 | split; [exact He2 | split; [exact HwN | split; [exact ACC | exact MACC]]]]]].
        lregs.
      + exact Hlt.
      + exact G11.
      + exact G10.
      + intros fx' A' M' model' c' R' FZ' FC' HLI' Hprog. destruct HLI' as (X' & HLI'). pose proof (x_scal X') as (Sc1' & _).
        eapply (IH (Z.to_nat (w_n w - c_widx c'))); [lia | exact FZ' | exact FC' | split; [exact X' | exact HLI'] | reflexivity].
    -
      pm_seed R w c (@nil word). seedHR HR E [(2%bv, EVar 32); (8%bv, EVar 33)] R. seedHK HK w A M model c E X.
      xruns HR HK 100%nat STOPS (SCR [false] [] []) 50%N. { split_scs; try sc_auto1. }
      postrun. name_run HRn R1. rreg HRn (2%bv) G2. rreg HRn (3%bv) G3. rreg HRn (4%bv) G4. rreg HRn (22%bv) G22. clear HRn HR HK. fixregs.
      rewrite Qgp in G3. rewrite Qtp in G4.
      eapply (pm_ret w c0 K fx A M model c R1); [exact PS | exact X | exact Htr | exact BUD | exact FZ | exact G2 | exact G3 | exact G4 | exact G22].
  Qed.

  Lemma init_bud : forall (c0 : parserC) n,
    fresh_state (pc_state c0) (st_words (pc_state c0)) (st_nwords (pc_state c0)) -> 0 <= n ->
    pm_bud n (PmCoreU1.init_pmc c0).
  Proof using.
    intros c0 n FR Hn. destruct FR as (_ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
    unfold pm_bud, PmCoreU1.init_pmc. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd pc_state].
    rewrite Hm1, Hm2, Hm3. unfold t3b, t3c, Zlength, OPND_SZ. cbn [fst snd length Z.of_nat].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); try lia. intros b [].
  Qed.

  Definition d1_stmt (w : pmw MI ST) (c0 : parserC) (K : TSet) (fx : FPState) : Prop :=
    forall A M model c R,
      PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> w_words w = 0 ->
      getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 10%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
      getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
      srealizes SEGS (cfg fx R PM_PRO M model) K.
  Definition hdr_stmt (w : pmw MI ST) (c0 : parserC) (K : TSet) (fx : FPState) : Prop :=
    forall A M model c R,
      PMX w A M model c -> c_tr c = [] -> pm_bud (w_n w) c -> w_words w <> 0 -> c_widx c <= 5 -> c_icount c = 0 ->
      getr R 8%bv = Z_to_bv 64 (w_p w) -> getr R 10%bv = Z_to_bv 64 (w_p w) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
      getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
      (forall (fx1 : FPState) A' M' model' c' R', frm_zero (@fp_csr fx1) -> fconsts fx1 ->
          PMX w A' M' model' c' -> c_tr c' = [] -> pm_bud (w_n w) c' -> c_widx c' = 5 -> 5 <= w_n w -> c_endian c' < 2 -> c_icount c' = 0 ->
          c_m1 c' = c_m1 c -> c_m2 c' = c_m2 c -> c_m3 c' = c_m3 c ->
          loop_regs w R' -> loop_mem w M' -> srealizes SEGS (cfg fx1 R' PM_HEAD M' model') K) ->
      srealizes SEGS (cfg fx R PM_PRO M model) K.

  #[local] Notation HCL := (cu_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma pm_main :
    (forall (w : pmw MI ST) c0 K (fx : FPState), PMS w c0 K -> frm_zero (@fp_csr fx) -> d1_stmt w c0 K fx) ->
    (forall (w : pmw MI ST) c0 K (fx : FPState), PMS w c0 K -> frm_zero (@fp_csr fx) -> hdr_stmt w c0 K fx) ->
    (forall (w : pmw MI ST) c0 K (fx : FPState), PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> body_stmt w c0 K fx) ->
    parse_module_stmt SEGS Ly.L MI ST kcU1.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros D1 HDR BODY. unfold parse_module_stmt. cbn [kc_pm_stack kc_parse_module kcU1].
    intros fx A s R M model sp ret p c0 L0 K CB ROC FZ Ha0 PR ASP ASC CAL FR WOK WDJ PERM BUD POST.
    eapply (PmCoreU1.pm_prologue MI ST fx A s R M model sp ret p c0 L0 K CB ROC Ha0 PR ASP ASC CAL FR WOK WDJ PERM BUD).
    intros M1 R1 X Q8 Q10 Q2 Q3 Q4.
    destruct CB as [AI MS ROCI SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx]. destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    pose proof BUD as BUD'. destruct BUD' as (Bcaps & Bbig & Bnmax & Bn & BS & BN & BB).

    assert (CNT : forall cls, count_class_f (size_class MI) (BIG MI) L0 cls <= count_class_f (size_class MI) (BIG MI) L0 cls) by (intros; lia).
    assert (BBF : big_bytes_f (round_big MI) (BIG MI) L0 <= big_bytes_f (round_big MI) (BIG MI) L0) by lia.
    assert (PS : PMS (PmCoreU1.mkw MI ST sp 16384 ret p c0 L0 R A M model s) c0 K).
    { constructor; cbn [PmCoreU1.mkw w_A0 w_L0 w_n w_diag w_ret w_R0 w_sp0 w_sp w_STK].
      - exact PERM.
      - intros cls Hc. pose proof (BS cls Hc). pose proof (CNT cls). lia.
      - intros cls Hc. pose proof (BN cls Hc). pose proof (CNT cls). lia.
      - lia.
      - destruct PR as [Pcons Puser Phdr Pins Phunk Pst Pdef Pal Prange Pconsf Pconsm Pconsd]. pose proof (proj1 (sr_w2 _ _ _ _ _ _ _ Pst)) as Hd. cbn in Hd. lia.
      - unfold PmCoreU1.POSTK, w_sp0. cbn [PmCoreU1.mkw w_s w_R0 w_model0 w_p w_cons w_words w_n w_L0 w_A0 w_M0 w_ret w_STK w_sp]. unfold PM_FRAME.
        replace (sp - 864 + 864 - 16384) with (sp - 16384) by lia. replace (sp - 864 + 864) with sp by lia. exact POST.
      - exact Hret. - exact Hra. - unfold w_sp0. cbn [w_sp PmCoreU1.mkw]. unfold PM_FRAME. rewrite Hsp. f_equal. lia. - exact Hgp. - exact Htp.
      - exact (cu_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL). }
    set (w := PmCoreU1.mkw MI ST sp 16384 ret p c0 L0 R A M model s) in *.
    assert (Hn0 : 0 <= w_n w) by (subst w; cbn [w_n PmCoreU1.mkw]; lia).
    pose proof (init_bud c0 (w_n w) FR Hn0) as BUD0.
    pose proof FR as FR'. destruct FR' as (Fw & Fn & Fwi & Fic & Ffl & _).
    destruct (Z.eq_dec (st_words (pc_state c0)) 0) as [Hw0|Hw0].
    - eapply (D1 w c0 K fx PS FZ A M1 model (PmCoreU1.init_pmc c0) R1 X eq_refl BUD0 Hw0 Q8 Q10);
        [exact Q2 | rewrite Q3; exact Hgp | rewrite Q4; exact Htp].
    - eapply (HDR w c0 K fx PS FZ A M1 model (PmCoreU1.init_pmc c0) R1 X eq_refl BUD0 Hw0);
        [cbn; lia | cbn; lia | exact Q8 | exact Q10 | exact Q2 | rewrite Q3; exact Hgp | rewrite Q4; exact Htp |].
      intros fx1 A' M' model' c' R' FZ1 FC1 X' Htr' BUD' Hw5 Hn5 He2 Hic Em1 Em2 Em3 LR LM.
      eapply (pm_loop w c0 K PS (fun fx2 FZ2 FC2 => BODY w c0 K fx2 PS FZ2 FC2) fx1); [exact FZ1 | exact FC1 |].
      split; [exact X'|]. split; [exact Htr'|]. split; [exact BUD'|]. split; [exact LR|]. split; [exact LM|]. split; [lia|]. split; [exact He2|]. split; [unfold w; cbn [w_words PmCoreU1.mkw]; exact Hw0|].
      destruct FR as (_ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & _).
      unfold nodes, macct, m3ok, m2ok, lacc. rewrite Em1, Em2, Em3. unfold PmCoreU1.init_pmc. cbn [c_m1 c_m2 c_m3]. rewrite Hm1, Hm2, Hm3. unfold Zlen. cbn [t3b t3c fst snd length Z.of_nat]. repeat split; try lia; apply Forall_nil.
  Qed.
End PM.
