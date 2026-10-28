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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1 PmExitS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmHex LbB_PmDS LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_PmLH LbB_PmOL LbB_TablStmt LbB_PmLeaf LbB_PmLeafW LbB_PmWords LbB_PmU2K LbB_PmWC1 LbB_PmWX1 LbB_PmWX2 LbB_PmWX5 LbB_PmWX3 LbB_PmWX4 LbB_DiagStmt LbB_PmWXK LbB_PmWXd1 LbB_PmWXd2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PiStmt.
Definition set_m2A (c : pmc) (t : Z * Z * list (Z * (Z * (Z * Z * Z)))) : pmc :=
  {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
     c_m1 := c_m1 c; c_m2 := t; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := c_tr c |}.

Section TXX.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HU16 : put_u16_stmtA H LINV ds_repA.
  Hypothesis HU64 : put_u64_stmtA H LINV ds_repA.
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.

  Lemma HHxx : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Hypothesis HNT : forall (w : pmwA H) s LB LBs m mo c msF R F fc (ty wd enc rid : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf5128) fc None m (seg_rom asegs) -> rfull R -> frm_zero fc ->
    regs_tbl w R RT_X3K -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 26%bv = Z_to_bv 64 ty -> 0 <= ty <= 3 -> PropExec.getr R 24%bv = Z_to_bv 64 wd -> 0 <= wd < 2 ^ 64 ->
    PropExec.getr R 15%bv = Z_to_bv 64 enc -> 0 <= enc < 16 ->
    rw_cells asegs m (wa_ff w + 9060) [C4 (Z_to_bv 64 rid)] -> 0 <= rid < 2 ^ 32 ->
    c_tr c = [] -> pm_bud (wa_n w) c -> 2 * (Zlength (t3c (c_m2 c)) + 1) <= wa_n w + 2 ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> 8 * t3b (c_m2 c) <= 16 * Zlength (t3c (c_m2 c)) + 504 ->
    pi_m2ok (t3c (c_m2 c)) ->
    (forall s' LB' LBs' m' mo' msF' R' F' fc' tbl' (t : Z * Z * list (Z * (Z * (Z * Z * Z)))),
       as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 0xf5d28) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' ->
       PMXA H LINV w s' LB' LBs' m' mo' (set_m2A c t) S_INSTR tbl' [] -> incl TBL_X5 tbl' ->
       regs_tbl w R' RT_X5 -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
       c_tr (set_m2A c t) = [] -> pm_bud (wa_n w) (set_m2A c t) -> (forall q k, In (q, k) (c_blocks (set_m2A c t)) -> k <= 2 ^ 40) ->
       Zlength (t3c (c_m2 c)) <= Zlength (t3c t) <= Zlength (t3c (c_m2 c)) + 1 -> 8 * t3b t <= 16 * Zlength (t3c t) + 504 ->
       pi_m2ok (t3c t) ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).

  Section W.
  Variable w : pmwA H.
  Variable QP : config -> Prop.


  Lemma HD1 : forall s LB LBs m mo c msF R F fc (I : ictxR) (lw : Z),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4b3c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_255C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    ictxA H w m I -> ipureA I -> i_io I + 1 <= c_widx c ->
    EXITKA H LINV w lw QP ->
    as_SR H QP (mkCfg msF mo).
  Proof.
    intros s LB LBs m mo c msF R F fc I lw OK X Htr Hbsz KR VIS RF FZ HT G3 G4 ICX IP Hio1 KX.
    pose proof (pmw_bounds H w OK) as BND. pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (B1 & B2 & B3 & B4).
    pose proof (@PmODefsS1.ipure_ranges TG idescA I IP) as [Riwc Rop]. pose proof IP as (_ & _ & _ & _ & _ & Hd & Rio).
    pose proof ICX as (Cio & Cfw & Ciwc & Cop & Cd).
    eapply pm_xd1 with (w := w) (s := s) (m := m) (c := c) (io := i_io I) (iwc := i_iwc I) (op := i_op I) (d := i_d I) (lw := lw) (Q := QP).
    all: first [eassumption | lia].
  Qed.

  Lemma HD2 : forall s LB LBs m mo c msF R F fc (I : ictxR) (lw : Z),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf48a4) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_2978 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    ictxA H w m I -> ipureA I -> i_io I + 1 <= c_widx c ->
    EXITKA H LINV w lw QP ->
    as_SR H QP (mkCfg msF mo).
  Proof.
    intros s LB LBs m mo c msF R F fc I lw OK X Htr Hbsz KR VIS RF FZ HT G3 G4 ICX IP Hio1 KX.
    pose proof (pmw_bounds H w OK) as BND. pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (B1 & B2 & B3 & B4).
    pose proof (@PmODefsS1.ipure_ranges TG idescA I IP) as [Riwc Rop]. pose proof IP as (_ & _ & _ & _ & _ & Hd & Rio).
    pose proof ICX as (Cio & Cfw & Ciwc & Cop & Cd).
    eapply pm_xd2 with (w := w) (s := s) (m := m) (c := c) (io := i_io I) (iwc := i_iwc I) (op := i_op I) (d := i_d I) (lw := lw) (Q := QP).
    all: first [eassumption | lia].
  Qed.

  Lemma lia_exit : forall (I : ictxR) s LB LBs m mo (c cX : pmc) msF R F fc,
    OBA H LINV w s LB LBs m mo c msF R F fc I OL_HEAD RT_EEF44 S_INSTR TBL_EEF44 ->
    i_io I + 1 <= c_widx c -> pi_nodes c + 2 <= c_widx c + 3 -> iaccA I c ->
    (t3b (c_v3 c) = [] \/ (t3b (c_v3 c) <> [] /\ 42 <= last (t3b (c_v3 c)) 0)) ->
    c_widx cX = c_widx c -> c_icount cX = c_icount c -> c_endian cX = c_endian c -> c_reqconv cX = c_reqconv c ->
    c_m1 cX = c_m1 c -> c_m3 cX = c_m3 c ->
    pm_bud (wa_n w) cX ->
    Zlength (t3c (c_m2 c)) <= Zlength (t3c (c_m2 cX)) <= Zlength (t3c (c_m2 c)) + 1 ->
    (Zlength (t3c (c_m2 cX)) = Zlength (t3c (c_m2 c)) + 1 -> tg_generates_type (i_op I) = true) ->
    8 * t3b (c_m2 cX) <= 16 * Zlength (t3c (c_m2 cX)) + 504 -> pi_m2ok (t3c (c_m2 cX)) ->
    pi_moreA H w (i_io I) cX.
  Proof.
    intros I s LB LBs m mo c cX msF R F fc OB Hio Hnodes IACC Hopt EW EI EE ER EM1 EM3 BUD HL2 HGT MAC2 M2OK.
    destruct OB as [X00 KR0 VIS0 RF0 FZ0 HT00 G3_0 G4_0 Htr Hbsz0 BUD0 IP ICX IFR Hic Hend Hw MACC V3R].
    destruct (@PmExitS1.iacc_exit tg_generates_type I c IACC Hio Hopt) as (L1 & L3 & L2 & LGT).
    unfold pi_moreA. rewrite EW, EI, EE, ER.
    split; [lia|]. split; [lia|]. split; [exact (proj1 Hend)|]. split; [exact (proj2 Hend)|].
    split; [exact (proj1 Hw)|]. split; [exact (proj2 Hw)|]. split; [exact BUD|].
    unfold pi_nodes, pi_macct, pi_lacc in *. rewrite EM1, EM3. unfold Zlen, Zlength in *.
    destruct MACC as (MC1 & MC2 & MC3 & M3OK & M2OK0).
    split; [lia|]. split.
    - split; [exact MC1|]. split; [exact MAC2|]. split; [exact MC3|]. split; [exact M3OK | exact M2OK].
    - split; [lia|]. split; [| lia].
      destruct (Z.eq_dec (Z.of_nat (length (t3c (c_m2 cX)))) (Z.of_nat (length (t3c (c_m2 c))) + 1)) as [E1|NE]; [| lia].
      specialize (LGT (HGT E1)). lia.
  Qed.

  Theorem pm_xexitA_w : forall (I : ictxR) s LB LBs m mo c msF R F fc,
    pmw_okA H w -> OLIA H LINV w s LB LBs m mo c msF R F fc I -> i_io I + i_iwc I <= c_widx c ->
    EXITKA H LINV w (i_io I) QP ->
    as_SR H QP (mkCfg msF mo).
  Proof.
    intros I s LB LBs m mo c msF R F fc OK HOLIA Hexit KX.
    pose proof HOLIA as (OB & Hio1 & Hnodes & Hv1m & Hv2l & Hv3l & ZW & NTY & IACC).
    pose proof OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP ICX IFR Hic Hend Hw MACC V3R].
    pose proof (pmw_bounds H w OK) as BND. pose proof (wk_n H w OK) as WN.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    pose proof (@PmODefsS1.ipure_ranges TG idescA I IP) as [Riwc Rop]. pose proof IP as (_ & _ & _ & _ & _ & _ & Rio).
    pose proof ICX as (Cio & Cfw & Ciwc & Cop & Cd).
    pose proof IFR as (ext & tid & rid & _ & _ & _ & _ & Crid & _ & _ & _ & _ & Rrid).
    pose proof MACC as (MC1 & MC2 & MC3 & M3OK & M2OK).

    eapply (tl_x1 H HHbp LINV LINV_frame HTL w s LB LBs m mo c TBL_EEF44 msF R F fc (i_io I) (i_iwc I) QP OK X0 (incl_refl _) KR0 VIS0 RF0 HT0 G3_0 G4_0
              Cio Ciwc ltac:(lia) ltac:(lia) Hexit V3R).
    {   intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 FK1 Hne.
      eapply (HD1 s LB LBs m1 mo1 c msF1 R1 F fc I (i_io I) OK X1 Htr Hbsz KR1 VIS1 RF1 FZ0 HT1);
        [exact G3_1 | exact G4_1 | | exact IP | exact Hio1 | exact KX].
      destruct ICX as (C1 & C2 & C3 & C4 & C5). unfold ictxA.
      refine (conj _ (conj _ (conj _ (conj _ _)))); (apply FK1; [lia | cbn; lia | assumption]). }
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 FK1 Hopt.

    eapply (tl_x2 H HHbp LINV LINV_frame HTL w s LB LBs m1 mo1 c msF1 R1 F fc (i_io I) (i_iwc I) (i_op I) QP OK X1 KR1 VIS1 RF1 HT1 G3_1 G4_1);
      [apply FK1; [lia | cbn; lia | exact Cio] | apply FK1; [lia | cbn; lia | exact Ciwc] | apply FK1; [lia | cbn; lia | exact Cop]
      | lia | lia | lia | exact Hexit | exact Hend | |].
    {   intros msF2 mo2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 G21_2 NEW.
      eapply (HD2 s LB LBs m1 mo2 c msF2 R2 F fc I (i_io I) OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HT2);
        [exact G3_2 | exact G4_2 | | exact IP | exact Hio1 | exact KX].
      destruct ICX as (C1 & C2 & C3 & C4 & C5). unfold ictxA.
      refine (conj _ (conj _ (conj _ (conj _ _)))); (apply FK1; [lia | cbn; lia | assumption]). }
    intros msF2 mo2 m2 R2 bg KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 G21_2 G18_2 G10_2 Pbg EQW FK2 Ciwc2.

    assert (NTX : i_op I = OP_TYPE_INT \/ i_op I = OP_TYPE_FLOAT -> (i_op I = OP_TYPE_INT -> 4 <= i_iwc I) /\ 3 <= i_iwc I).
    { intros Hop. destruct (PmZw.nty_exit (i_op I) (t3b (c_v3 c)) (c_widx c - i_io I) NTY Hop Hopt) as [NA NB]. split; [intros E; specialize (NA E); lia | lia]. }

    assert (KH : forall cX s' LB' LBs' m' mo' msF' R' tbl',
              as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F (Z_to_bv 64 EXIT_RET) fc None m' (seg_rom asegs) -> rfull R' ->
              PMXA H LINV w s' LB' LBs' m' mo' cX S_INSTR tbl' [] -> incl TBL_EXIT tbl' ->
              regs_tbl w R' RT_EXIT -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
              PropExec.getr R' 23%bv = Z_to_bv 64 0 ->
              c_widx cX = c_widx c -> c_icount cX = c_icount c -> c_endian cX = c_endian c -> c_reqconv cX = c_reqconv c ->
              c_m1 cX = c_m1 c -> c_m3 cX = c_m3 c -> c_tr cX = [] ->
              pm_bud (wa_n w) cX -> (forall q k, In (q, k) (c_blocks cX) -> k <= 2 ^ 40) ->
              Zlength (t3c (c_m2 c)) <= Zlength (t3c (c_m2 cX)) <= Zlength (t3c (c_m2 c)) + 1 ->
              (Zlength (t3c (c_m2 cX)) = Zlength (t3c (c_m2 c)) + 1 -> tg_generates_type (i_op I) = true) ->
              8 * t3b (c_m2 cX) <= 16 * Zlength (t3c (c_m2 cX)) + 504 -> pi_m2ok (t3c (c_m2 cX)) ->
              as_SR H QP (mkCfg msF' mo')).
    { intros cX s' LB' LBs' m' mo' msF' R' tbl' KR VIS RF X INC HT G3 G4 G23 EW EI EE ER EM1 EM3 Etr BUDX HbszX HL2 HGT MAC2 M2X.
      pose proof (lia_exit I s LB LBs m mo c cX msF R F fc OB Hio1 Hnodes IACC Hopt EW EI EE ER EM1 EM3 BUDX HL2 HGT MAC2 M2X) as PM.
      eapply (KX s' LB' LBs' m' mo' cX msF' R' F fc EXIT_RET S_INSTR 0).
      - constructor.
        + exists tbl', 0. split; [exact X | split; [exact INC | intros _; reflexivity]].
        + exact KR. + exact VIS. + exact RF. + exact FZ0. + exact HT. + exact G3. + exact G4.
        + split; [exact G23 | lia].
        + exact Etr. + exact HbszX. + intros _. exact PM.
      - left. split; reflexivity. }

    assert (KB : KB9C H LINV w s LB LBs m2 c F fc QP).
    { intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3.
      eapply (tl_x5 H HHbp LINV LINV_frame w s LB LBs m2 mo3 c TBL_EEF44 msF3 R3 F fc QP OK X3
                ltac:(apply LbB_PmU2K.tbl_incl; vm_compute; reflexivity) KR3 VIS3 RF3 HT3 G3_3 G4_3).
      intros msF4 mo4 m4 R4 KR4 VIS4 RF4 X4 HT4 G3_4 G4_4 G23_4.
      eapply (KH c s LB LBs m4 mo4 msF4 R4 TBL_X5); [exact KR4 | exact VIS4 | exact RF4 | exact X4
                    | apply LbB_PmU2K.tbl_incl; vm_compute; reflexivity | exact HT4 | exact G3_4 | exact G4_4 | exact G23_4
                    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Htr | exact BUD | exact Hbsz
                    | lia | intros E; lia | exact MC2 | exact M2OK]. }

    assert (KN : tg_generates_type (i_op I) = true -> K3234 H LINV w s LB LBs m2 c F fc QP).
    { intros GT msF3 mo3 m3 R3 ty wd enc KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 G26 Hty G24 Hwd G15 Henc FK3.
      destruct (@PmExitS1.iacc_exit tg_generates_type I c IACC Hio1 Hopt) as (L1 & L3 & L2 & LGT).
      eapply (HNT w s LB LBs m3 mo3 c msF3 R3 F fc ty wd enc rid QP OK X3 KR3 VIS3 RF3 FZ0 HT3 G3_3 G4_3 G26 Hty G24 Hwd G15 Henc);
        [ apply (ffkeepX_cell w X3_FFX m2 m3 9060 _ FK3); [| lia | cbn; lia | reflexivity];
          apply (ffkeepX_cell w X2_FFX m1 m2 9060 _ FK2); [| lia | cbn; lia | reflexivity];
          apply FK1; [lia | cbn; lia | exact Crid]
        | lia | exact Htr | exact BUD | unfold Zlen, Zlength in *; lia | exact Hbsz | exact MC2 | exact M2OK | ].
      intros sx LB4 LBs4 m4 mo4 msF4 R4 F4 fc4 tbl4 t KR4 VIS4 RF4 FZ4 X4 IT4 HT4 G3_4 G4_4 Htr4 BUD4 Hbsz4 HL4 MAC4 M2t.
      eapply (tl_x5 H HHbp LINV LINV_frame w sx LB4 LBs4 m4 mo4 (set_m2A c t) tbl4 msF4 R4 F4 fc4 QP OK X4 IT4 KR4 VIS4 RF4 HT4 G3_4 G4_4).
      intros msF5 mo5 m5 R5 KR5 VIS5 RF5 X5 HT5 G3_5 G4_5 G23_5.
      eapply (KX sx LB4 LBs4 m5 mo5 (set_m2A c t) msF5 R5 F4 fc4 EXIT_RET S_INSTR 0).
      - pose proof (lia_exit I s LB LBs m mo c (set_m2A c t) msF R F fc OB Hio1 Hnodes IACC Hopt
                      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl BUD4 ltac:(cbn [set_m2A c_m2]; exact HL4)
                      (fun _ => GT) ltac:(cbn [set_m2A c_m2]; exact MAC4) ltac:(cbn [set_m2A c_m2]; exact M2t)) as PM.
        constructor.
        + exists TBL_X5, 0. split; [exact X5 | split; [apply LbB_PmU2K.tbl_incl; vm_compute; reflexivity | intros _; reflexivity]].
        + exact KR5. + exact VIS5. + exact RF5. + exact FZ4. + exact HT5. + exact G3_5. + exact G4_5.
        + split; [exact G23_5 | lia].
        + exact Htr4. + exact Hbsz4. + intros _. exact PM.
      - left. split; reflexivity. }

    eapply (tl_x3 H HHbp LINV LINV_frame HTL w s LB LBs m2 mo2 c msF2 R2 F fc (i_io I) (i_iwc I) (i_op I) bg QP OK X2 KR2 VIS2 RF2 HT2 G3_2 G4_2
              G21_2 G18_2 G10_2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (proj1 Hw));
      [ intros Hbg HopI; exact (proj1 (NTX (or_introl HopI)) HopI) | exact Pbg | exact (proj2 Hend) | exact KB | | exact KN ].
    intros Hbg HopF.
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 G21_3.
    eapply (tl_x4 H HHbp LINV LINV_frame HTL w s LB LBs m2 mo3 c msF3 R3 F fc (i_io I) (i_iwc I) QP OK X3 KR3 VIS3 RF3 HT3 G3_3 G4_3 G21_3 Ciwc2
              ltac:(lia) _ ltac:(lia) (proj1 Hw) (proj2 Hend) (KN (Pbg Hbg))).
    Unshelve. pose proof (proj2 (NTX (or_intror HopF))). lia.
  Qed.
  End W.

  Theorem pm_xexitA : forall (w : pmwA H) (I : ictxR) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> OLIA H LINV w s LB LBs m mo c msF R F fc I -> i_io I + i_iwc I <= c_widx c ->
    EXITKA H LINV w (i_io I) Q -> as_SR H Q (mkCfg msF mo).
  Proof. intros w I s LB LBs m mo c msF R F fc Q. exact (pm_xexitA_w w Q I s LB LBs m mo c msF R F fc). Qed.

  Section W.
  End W.
End TXX.
