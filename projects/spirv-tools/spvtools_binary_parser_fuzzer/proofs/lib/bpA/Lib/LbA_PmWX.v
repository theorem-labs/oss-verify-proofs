(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1 PmExitS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_RtOwn LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmCall LbA_PmXp LbA_PmGlue LbA_PmVops LbA_PmHdr LbA_PmHex LbA_PmDS LbA_PmExit LbA_PmInit LbA_PmFin LbA_PmExit2 LbA_PmLH LbA_PmOL LbA_TablStmt LbA_PmLeaf LbA_PmLeafW LbA_PmWords LbA_PmU2K LbA_PmWT1 LbA_PmWT2 LbA_PmWT3 LbA_PmWC1 LbA_PmWX1 LbA_PmWX2 LbA_PmWX5 LbA_PmWX3 LbA_PmWX4 LbA_DiagStmt LbA_PmWXK LbA_PmWXd1 LbA_PmWXd2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

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

  Lemma HHxx : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Hypothesis HNT : forall (w : pmwA H) s LB LBs m mo c msF R F fc (ty wd enc rid : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf33c4) fc None m (seg_rom asegs) -> rfull R -> frm_zero fc ->
    regs_tbl w R RT_3054 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 25%bv = Z_to_bv 64 ty -> 0 <= ty <= 3 -> PropExec.getr R 23%bv = Z_to_bv 64 wd -> 0 <= wd < 2 ^ 64 ->
    PropExec.getr R 19%bv = Z_to_bv 64 enc -> 0 <= enc < 2 ^ 64 ->
    rw_cells asegs m (wa_ff w + 10436) [C4 (Z_to_bv 64 rid)] -> 0 <= rid < 2 ^ 32 ->
    c_tr c = [] -> pm_bud (wa_n w) c -> 2 * (Zlength (t3c (c_m2 c)) + 1) <= wa_n w + 2 ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> 8 * t3b (c_m2 c) <= 16 * Zlength (t3c (c_m2 c)) + 504 ->
    (forall s' LB' LBs' m' mo' msF' R' F' fc' tbl' (t : Z * Z * list (Z * (Z * (Z * Z * Z)))),
       as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 0xf3d2c) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' ->
       PMXA H LINV w s' LB' LBs' m' mo' (set_m2A c t) S_INSTR tbl' [] -> incl TBL_X5 tbl' ->
       regs_tbl w R' RT_X5 -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
       c_tr (set_m2A c t) = [] -> pm_bud (wa_n w) (set_m2A c t) -> (forall q k, In (q, k) (c_blocks (set_m2A c t)) -> k <= 2 ^ 40) ->
       Zlength (t3c (c_m2 c)) <= Zlength (t3c t) <= Zlength (t3c (c_m2 c)) + 1 -> 8 * t3b t <= 16 * Zlength (t3c t) + 504 ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).

  Section W.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
            (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
            (F0 : bvmap 5 word) (fc0 : bv 32).
  Let w : pmwA H := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi.
  Let QP : config -> Prop := pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 st0 LB0 LF p c0 lo B shi m0 mo0.

  Lemma HD1 : forall s LB LBs m mo c msF R F fc (I : ictxR),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pm_bud (wa_n w) c ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2e7c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_255C -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    ictxA H w m I -> ipureA I -> i_io I + 1 <= c_widx c ->
    as_SR H QP (mkCfg msF mo).
  Proof.
    intros s LB LBs m mo c msF R F fc I OK X Htr Hbsz BUD KR VIS RF FZ HT G3 G4 ICX IP Hio1.
    pose proof (pmw_bounds H w OK) as BND. pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (B1 & B2 & B3 & B4).
    pose proof (@PmODefsS1.ipure_ranges TG idescA I IP) as [Riwc Rop]. pose proof IP as (_ & _ & _ & _ & _ & Hd & Rio).
    pose proof ICX as (Cio & Cfw & Ciwc & Cop & Cd).
    pose proof (pmxa_restrict H HHxx LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_XD [] OK X tbl_xd_incl (incl_refl _)) as X'.
    exact (pm_xd1 H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU16 HU64 HTL
             ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi
             s LB LBs m mo c msF R F fc (i_io I) (i_iwc I) (i_op I) (i_d I)
             OK X' Htr Hbsz KR VIS RF FZ HT G3 G4 BUD Cio ltac:(lia) Ciwc ltac:(lia) Cop ltac:(lia) Cd Hd).
  Qed.

  Lemma HD2 : forall s LB LBs m mo c msF R F fc (I : ictxR),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pm_bud (wa_n w) c ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2b08) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_2978 -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    PropExec.getr R 19%bv = Z_to_bv 64 (i_io I) ->
    ictxA H w m I -> ipureA I -> i_io I + 1 <= c_widx c -> c_widx c <> i_io I + i_iwc I ->
    as_SR H QP (mkCfg msF mo).
  Proof.
    intros s LB LBs m mo c msF R F fc I OK X Htr Hbsz BUD KR VIS RF FZ HT G3 G4 G19 ICX IP Hio1 NEW.
    pose proof (pmw_bounds H w OK) as BND. pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (B1 & B2 & B3 & B4).
    pose proof (@PmODefsS1.ipure_ranges TG idescA I IP) as [Riwc Rop]. pose proof IP as (_ & _ & _ & _ & _ & Hd & Rio).
    pose proof ICX as (Cio & Cfw & Ciwc & Cop & Cd).
    pose proof (pmxa_restrict H HHxx LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_XD [] OK X tbl_xd_incl (incl_refl _)) as X'.
    exact (pm_xd2 H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU16 HU64 HTL
             ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi
             s LB LBs m mo c msF R F fc (i_io I) (i_iwc I) (i_op I) (i_d I)
             OK X' Htr Hbsz KR VIS RF FZ HT G3 G4 BUD Cio ltac:(lia) ltac:(lia) Ciwc ltac:(lia) Cd Hd).
  Qed.

  Lemma lia_exit : forall (I : ictxR) s LB LBs m mo (c cX : pmc) msF R F fc,
    OBA H LINV w s LB LBs m mo c msF R F fc I OL_HEAD RT_EEF44 S_INSTR TBL_EEF44 ->
    i_io I + 1 <= c_widx c -> nodesA c + 2 <= c_widx c + 3 -> iaccA I c ->
    (t3b (c_v3 c) = [] \/ (t3b (c_v3 c) <> [] /\ 42 <= last (t3b (c_v3 c)) 0)) ->
    forall s' LB' LBs' m' mo' msF' R' F' fc',
    as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 0xee7d8) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' ->
    PMXA H LINV w s' LB' LBs' m' mo' cX S_MODULE TBL_EE648 [] ->
    regs_tbl w R' RT_EE648 -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
    c_widx cX = c_widx c -> c_icount cX = c_icount c -> c_endian cX = c_endian c -> c_reqconv cX = c_reqconv c ->
    c_m1 cX = c_m1 c -> c_m3 cX = c_m3 c -> c_tr cX = [] ->
    pm_bud (wa_n w) cX -> (forall q k, In (q, k) (c_blocks cX) -> k <= 2 ^ 40) ->
    Zlength (t3c (c_m2 c)) <= Zlength (t3c (c_m2 cX)) <= Zlength (t3c (c_m2 c)) + 1 ->
    (Zlength (t3c (c_m2 cX)) = Zlength (t3c (c_m2 c)) + 1 -> tg_generates_type (i_op I) = true) ->
    8 * t3b (c_m2 cX) <= 16 * Zlength (t3c (c_m2 cX)) + 504 ->
    LIA H LINV w s' LB' LBs' m' mo' cX msF' R' F' fc' /\ i_io I + 1 <= c_widx cX.
  Proof.
    intros I s LB LBs m mo c cX msF R F fc OB Hio Hnodes IACC Hopt s' LB' LBs' m' mo' msF' R' F' fc'
           KR VIS RF FZ X HT G3 G4 EW EI EE ER EM1 EM3 Etr BUD Hbsz HL2 HGT MAC2.
    destruct OB as [X00 KR0 VIS0 RF0 FZ0 HT00 G3_0 G4_0 Htr Hbsz0 BUD0 IP ICX IFR Hic Hend Hw MACC V3R].
    destruct (@PmExitS1.iacc_exit tg_generates_type I c IACC Hio Hopt) as (L1 & L3 & L2 & LGT).
    split; [| rewrite EW; exact Hio].
    split.
    - exact X. - exact KR. - exact VIS. - exact RF. - exact FZ. - exact HT. - exact G3. - exact G4. - exact Etr. - exact Hbsz.
    - rewrite EW, EI. lia.
    - rewrite EE, ER. exact Hend.
    - exact Hw.
    - exact BUD.
    - unfold nodesA, macctA, laccA in *. rewrite EW, EM1, EM3. unfold Zlen, Zlength in *.
      destruct MACC as (MC1 & MC2 & MC3 & M3OK).
      split; [lia|]. split; [| ].
      + split; [exact MC1|]. split; [exact MAC2|]. split; [exact MC3 | exact M3OK].
      + split; [lia|]. split; [| lia].
        destruct (Z.eq_dec (Z.of_nat (length (t3c (c_m2 cX)))) (Z.of_nat (length (t3c (c_m2 c))) + 1)) as [E1|NE]; [| lia].
        specialize (LGT (HGT E1)). lia.
  Qed.

  Theorem pm_xexitA : forall (I : ictxR) s LB LBs m mo c msF R F fc,
    pmw_okA H w -> OLIA H LINV w s LB LBs m mo c msF R F fc I -> i_io I + i_iwc I <= c_widx c ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc',
       LIA H LINV w s' LB' LBs' m' mo' c' msF' R' F' fc' -> i_io I + 1 <= c_widx c' -> as_SR H QP (mkCfg msF' mo')) ->
    as_SR H QP (mkCfg msF mo).
  Proof.
    intros I s LB LBs m mo c msF R F fc OK HOLIA Hexit KL.
    pose proof HOLIA as (OB & Hio1 & Hnodes & Hv1m & Hv2l & Hv3l & ZW & NTY & IACC).
    pose proof OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP ICX IFR Hic Hend Hw MACC V3R].
    pose proof (pmw_bounds H w OK) as BND. pose proof (wk_n H w OK) as WN.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    pose proof (@PmODefsS1.ipure_ranges TG idescA I IP) as [Riwc Rop]. pose proof IP as (_ & _ & _ & _ & _ & _ & Rio).
    pose proof ICX as (Cio & Cfw & Ciwc & Cop & Cd).
    pose proof IFR as (ext & tid & rid & _ & _ & _ & _ & Crid & _ & _ & _ & _ & Rrid).
    assert (G27 : PropExec.getr R 27%bv = Z_to_bv 64 (wa_ff w + 10496)).
    { pose proof (ev_world_all H w _ (env_world_seed H w R [])) as (_ & E33 & _).
      rewrite (rt_get w [] R RT_EEF44 27%bv _ HT0 eq_refl). apply (ev_add _ 33 (wa_ff w) 10496 E33); lia. }

    eapply (tl_x1 H HHbp LINV LINV_frame HTL w s LB LBs m mo c TBL_EEF44 msF R F fc (i_io I) (i_iwc I) QP OK X0 (incl_refl _) KR0 VIS0 RF0 HT0 G3_0 G4_0 G27
              Cio Ciwc ltac:(lia) ltac:(lia) Hexit V3R).
    {   intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 FK1 Hne.
      eapply (HD1 s LB LBs m1 mo1 c msF1 R1 F fc I OK X1 Htr Hbsz BUD KR1 VIS1 RF1 FZ0 HT1);
        [exact G3_1 | exact G4_1 | | exact IP | exact Hio1].
      destruct ICX as (C1 & C2 & C3 & C4 & C5). unfold ictxA.
      refine (conj _ (conj _ (conj _ (conj _ _)))); (apply FK1; [lia | cbn; lia | assumption]). }
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 FK1 Hopt.

    eapply (tl_x2 H HHbp LINV LINV_frame HTL w s LB LBs m1 mo1 c msF1 R1 F fc (i_io I) (i_iwc I) (i_op I) QP OK X1 KR1 VIS1 RF1 HT1 G3_1 G4_1);
      [apply FK1; [lia | cbn; lia | exact Cio] | apply FK1; [lia | cbn; lia | exact Ciwc] | apply FK1; [lia | cbn; lia | exact Cop]
      | lia | lia | lia | exact Hexit | exact Hend | |].
    {   intros msF2 mo2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 G19_2 NEW.
      eapply (HD2 s LB LBs m1 mo2 c msF2 R2 F fc I OK X2 Htr Hbsz BUD KR2 VIS2 RF2 FZ0 HT2);
        [exact G3_2 | exact G4_2 | exact G19_2 | | exact IP | exact Hio1 | exact NEW].
      destruct ICX as (C1 & C2 & C3 & C4 & C5). unfold ictxA.
      refine (conj _ (conj _ (conj _ (conj _ _)))); (apply FK1; [lia | cbn; lia | assumption]). }
    intros msF2 mo2 m2 R2 bg KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 G19_2 G23_2 G10_2 Pbg EQW FK2 Ciwc2.

    assert (NTX : i_op I = OP_TYPE_INT \/ i_op I = OP_TYPE_FLOAT -> (i_op I = OP_TYPE_INT -> 4 <= i_iwc I) /\ 3 <= i_iwc I).
    { intros Hop. destruct (PmZw.nty_exit (i_op I) (t3b (c_v3 c)) (c_widx c - i_io I) NTY Hop Hopt) as [NA NB]. split; [intros E; specialize (NA E); lia | lia]. }

    assert (KH : forall cX s' LB' LBs' m' mo' msF' R' F' fc',
              as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 0xee7d8) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' ->
              PMXA H LINV w s' LB' LBs' m' mo' cX S_MODULE TBL_EE648 [] ->
              regs_tbl w R' RT_EE648 -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
              c_widx cX = c_widx c -> c_icount cX = c_icount c -> c_endian cX = c_endian c -> c_reqconv cX = c_reqconv c ->
              c_m1 cX = c_m1 c -> c_m3 cX = c_m3 c -> c_tr cX = [] ->
              pm_bud (wa_n w) cX -> (forall q k, In (q, k) (c_blocks cX) -> k <= 2 ^ 40) ->
              Zlength (t3c (c_m2 c)) <= Zlength (t3c (c_m2 cX)) <= Zlength (t3c (c_m2 c)) + 1 ->
              (Zlength (t3c (c_m2 cX)) = Zlength (t3c (c_m2 c)) + 1 -> tg_generates_type (i_op I) = true) ->
              8 * t3b (c_m2 cX) <= 16 * Zlength (t3c (c_m2 cX)) + 504 ->
              as_SR H QP (mkCfg msF' mo')).
    { intros cX s' LB' LBs' m' mo' msF' R' F' fc' KR VIS RF FZ X HT G3 G4 EW EI EE ER EM1 EM3 Etr BUDX HbszX HL2 HGT MAC2.
      destruct (lia_exit I s LB LBs m mo c cX msF R F fc OB Hio1 Hnodes IACC Hopt s' LB' LBs' m' mo' msF' R' F' fc' KR VIS RF FZ X HT G3 G4
                  EW EI EE ER EM1 EM3 Etr BUDX HbszX HL2 HGT MAC2) as [HL HP].
      exact (KL _ _ _ _ _ _ _ _ _ _ HL HP). }
    pose proof MACC as (MC1 & MC2 & MC3 & M3OK).

    assert (KB : KB9C H LINV w s LB LBs m2 c F fc QP).
    { intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3.
      eapply (tl_x5 H HHbp LINV LINV_frame w s LB LBs m2 mo3 c TBL_EEF44 msF3 R3 F fc QP OK X3
                ltac:(apply LbA_PmU2K.tbl_incl; vm_compute; reflexivity) KR3 VIS3 RF3 HT3 G3_3 G4_3).
      intros msF4 mo4 m4 R4 KR4 VIS4 RF4 X4 HT4 G3_4 G4_4.
      eapply (KH c); [exact KR4 | exact VIS4 | exact RF4 | exact FZ0 | exact X4 | exact HT4 | exact G3_4 | exact G4_4
                    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Htr | exact BUD | exact Hbsz
                    | lia | intros E; lia | exact MC2]. }

    assert (KN : tg_generates_type (i_op I) = true -> K3234 H LINV w s LB LBs m2 c F fc QP).
    { intros GT msF3 mo3 m3 R3 ty wd enc KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 G25 Hty G23 Hwd G19 Henc FK3.
      destruct (@PmExitS1.iacc_exit tg_generates_type I c IACC Hio1 Hopt) as (L1 & L3 & L2 & LGT).
      eapply (HNT w s LB LBs m3 mo3 c msF3 R3 F fc ty wd enc rid QP OK X3 KR3 VIS3 RF3 FZ0 HT3 G3_3 G4_3 G25 Hty G23 Hwd G19 Henc);
        [ apply (ffkeepX_cell w X3_FFX m2 m3 10436 _ FK3); [| lia | cbn; lia | reflexivity];
          apply (ffkeepX_cell w X2_FFX m1 m2 10436 _ FK2); [| lia | cbn; lia | reflexivity];
          apply FK1; [lia | cbn; lia | exact Crid]
        | lia | exact Htr | exact BUD | unfold Zlen, Zlength in *; lia | exact Hbsz | exact MC2 | ].
      intros sx LB4 LBs4 m4 mo4 msF4 R4 F4 fc4 tbl4 t KR4 VIS4 RF4 FZ4 X4 IT4 HT4 G3_4 G4_4 Htr4 BUD4 Hbsz4 HL4 MAC4.
      eapply (tl_x5 H HHbp LINV LINV_frame w sx LB4 LBs4 m4 mo4 (set_m2A c t) tbl4 msF4 R4 F4 fc4 QP OK X4 IT4 KR4 VIS4 RF4 HT4 G3_4 G4_4).
      intros msF5 mo5 m5 R5 KR5 VIS5 RF5 X5 HT5 G3_5 G4_5.
      eapply (KH (set_m2A c t)); [exact KR5 | exact VIS5 | exact RF5 | exact FZ4 | exact X5 | exact HT5 | exact G3_5 | exact G4_5
                    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Htr4 | exact BUD4 | exact Hbsz4
                    | cbn [set_m2A c_m2]; exact HL4 | intros _; exact GT | cbn [set_m2A c_m2]; exact MAC4]. }

    eapply (tl_x3 H HHbp LINV LINV_frame HTL w s LB LBs m2 mo2 c msF2 R2 F fc (i_io I) (i_iwc I) (i_op I) bg QP OK X2 KR2 VIS2 RF2 HT2 G3_2 G4_2
              G19_2 G23_2 G10_2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (proj1 Hw));
      [ intros Hbg HopI; exact (proj1 (NTX (or_introl HopI)) HopI) | exact Pbg | exact (proj2 Hend) | exact KB | | exact KN ].
    intros Hbg HopF.
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 G19_3.
    eapply (tl_x4 H HHbp LINV LINV_frame HTL w s LB LBs m2 mo3 c msF3 R3 F fc (i_io I) (i_iwc I) QP OK X3 KR3 VIS3 RF3 HT3 G3_3 G4_3 G19_3 Ciwc2
              ltac:(lia) _ ltac:(lia) (proj1 Hw) (proj2 Hend) (KN (Pbg Hbg))).
    Unshelve. pose proof (proj2 (NTX (or_intror HopF))). lia.
  Qed.
  End W.
End TXX.
