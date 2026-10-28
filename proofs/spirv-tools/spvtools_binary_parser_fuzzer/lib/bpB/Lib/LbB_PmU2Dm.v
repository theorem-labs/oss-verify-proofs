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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_PmLeaf LbB_PmLeafW LbB_PmVops LbB_PmExit2 LbB_PmU2K LbB_PmOL LbB_PmU2C.

Definition TBL_F0A6C_RUN : list (Z * expr) :=
  TBL_F0A44 ++ [(400, EAlu ALU_ADD (EVar WV_FF) (ELit 9616)); (408, EAlu ALU_ADD (EVar WV_P) (ELit 216));
                (608, EAlu ALU_ADD (EVar WV_FF) (ELit 9050))].

Lemma tbl_f0a6c_incl : incl TBL_F0A6C TBL_F0A6C_RUN.
Proof. apply tbl_incl. vm_compute. reflexivity. Qed.

Section U2Dm.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Lemma HHm : asan_rt_hyps H.
  Proof. exact (proj1 HHbp). Qed.

  Lemma pm_u2dm : forall (w : pmwA H) s LB LBs m mo c msF R F fc (fw : Z) (Q : config -> Prop),
    pmw_okA H w -> HS_F0A44 H LINV w s LB LBs m mo c msF R F fc fw -> fw / 2 ^ 16 <> 0 ->
    (forall msF1 mo1 m1 R1 (r : Z), HS_F0A6C H LINV w s LB LBs m1 mo1 c msF1 R1 F fc fw r ->
       ffkeepX w [(9616, 8)] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc fw Q OK HS Hwc K.
    destruct HS as [X0 Htr Hbsz Hbud Hv1 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Hfw CF CW CO].
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (Z.mod_pos_bound fw (2 ^ 16) ltac:(lia)) as OPR.
    assert (WCR : 0 <= fw / 2 ^ 16 < 2 ^ 16) by (clear - Hfw; Z.div_mod_to_equations; lia).
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 (fw / 2 ^ 16); Z_to_bv 64 (fw mod 2 ^ 16)]
          (@nil kentry) 100%nat [AT_LOOKUP_OPCODE] [false] 41%N
          [OB_INST; OB_FIRST_WORD; OB_INST_WC; OB_OPCODE_DESC] [400; 408; 608] (@nil Z) TBL_F0A6C_RUN (@nil (Z * expr)) RT_F0A44.
    { pose proof (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 (fw / 2 ^ 16); Z_to_bv 64 (fw mod 2 ^ 16)]))
        as (_ & EV33 & _).
      split_scs.
      all: lazymatch goal with
      | |- sc_denot _ _ _ (SCBr _ _ _ _) =>
          apply sc_br_of; ev_xs; apply br_eq0_nz; [clear - WCR; lia | exact Hwc]
      | |- sc_denot _ _ _ (SCReadBase (SA _ ?off) _ _ _) =>
          lazymatch goal with C : rw_cells _ ?mm (wa_ff ?ww + off) [C2 (Z_to_bv 64 ?v)] |- _ =>
            pose proof (rw_cells_read asegs mm _ _ 0%nat _ C eq_refl) as RD;
            cbn [csize cbytes] in RD; rewrite Z.add_0_r in RD; unfold wa in RD; rewrite LbB_Conv.rdn_of_ov in RD;
            eapply (sc_read_cellw asegs _ _ _ (wa_ff ww + off) 2%N v);
            [ split; [change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16); lia | exact RD]
            | lia
            | apply adenot_of_estart; [apply estart_of_ev; [exact EV33 | lia] | lia]
            | ev_xs; reflexivity ]
          end
      end. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    set (E1 := Eseed R (wenv_vals w ++ [Z_to_bv 64 (fw / 2 ^ 16); Z_to_bv 64 (fw mod 2 ^ 16)])) in *.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    lazymatch type of VIS1 with context [Z_to_bv 64 (s_pc ?ss)] =>
      replace (s_pc ss) with AT_LOOKUP_OPCODE in VIS1 by reflexivity end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_F0A44 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_world_all H w E1 (env_world_seed H w R _)) as (_ & EV33 & _).
    assert (U33 : bv_unsigned (edenot E1 (EVar WV_FF)) = wa_ff w).
    { change (EVar WV_FF) with (EVar 33). rewrite EV33. apply u64_of_Z. lia. }
    assert (UFS : bv_unsigned (edenot E1 FSHB) = wa_ff w / 8) by (unfold FSHB; apply srl3_val; [exact EV33 | lia]).
    pose proof (ev_s1 H w E1 OK (env_world_seed H w R _)) as US1.
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2.
    assert (FK1 : ffkeepX w [(9616, 8)] m M1).
    { pose proof (munch_sym E1 m (s_log SSr) [(EVar WV_S1, 0, 832); (EVar WV_FF, 9616, 9624); (FSHB, SHBASE, SHBASE + PM_NSH)]
                    Hlf1 ltac:(vm_compute; reflexivity)) as MU.
      cbn [num_wins map] in MU. rewrite US1, U33, UFS in MU.
      apply (ffkeepX_munch w _ _ _ _ MU (wmono_mem_denot _ _ _)).
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
      - left. lia.
      - right; right. apply Exists_cons_hd. cbn [fst snd]. lia.
      - unfold PM_NSH. destruct Q6 as [D|D]; [left | right; left]; lia. }
    assert (CE : rw_cells asegs M1 (wa_ff w + 9616) [C8 (Z_to_bv 64 0)]).
    { subst M1. eapply (rw_cells_log_nth_2b _ m _ 1%nat (EVar WV_FF) (EVar WV_S1) 9616 8 (ELit 0) 400 408);
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite U33; reflexivity | rewrite US1; left; lia
        | | reflexivity | exact Logic.I | reflexivity].
      split; [lia|]. split; [lia|]. intros i Hi.
      replace (wa_ff w + 9616 + i) with (wa_ff w + (9616 + i)) by lia. apply FW2. lia. }
    assert (MD1 : mdef M1 (wa_ff w + 9616) 8) by exact (mdef_of_rw_cells M1 _ _ CE ltac:(unfold AIMG_TOP, AFS_HDR in *; lia)).
    assert (G1_1 : PropExec.getr R1 1%bv = Z_to_bv 64 0xf0a6c) by (sreg_rw HR1 (1%bv : reg); reflexivity).
    assert (G2_1 : PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w)) by rtf HT1.
    assert (G10_1 : PropExec.getr R1 10%bv = Z_to_bv 64 (fw mod 2 ^ 16)).
    { sreg_rw HR1 (10%bv : reg). unfold E1. ev_xs. reflexivity. }
    assert (G11_1 : PropExec.getr R1 11%bv = Z_to_bv 64 (wa_ff w + 9616)).
    { sreg_rw HR1 (11%bv : reg). apply ev_add; [exact EV33 | lia | lia]. }
    eapply (pm_lookup H HHm LINV LINV_frame _ _ _ _ (tla_lookup_opcode HTL) (fw mod 2 ^ 16) 0 9616 w s LB LBs M1 mo1 c _
              TBL_F0A6C_RUN [] [] 0 msF1 R1 F fc 0xf0a6c Q [] OK X1 KR1 VIS1 RF1 G2_1 G1_1 eq_refl ltac:(lia) G10_1 ltac:(lia)
              ltac:(intros _; exact G11_1) ltac:(intros Hn3; discriminate Hn3) eq_refl);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | apply incl_refl | reflexivity
      | reflexivity | exact MD1 |].
    intros msF2 mo2 m2 R2 r KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 Gr Hr Hiff Hfound Hmiss.
    assert (FK2 : ffkeepX w [(9616, 8)] M1 m2).
    { apply (ffkeepX_munch w _ _ _ _ MU2 WM2). apply Forall_cons; [left; cbn [fst]; unfold TL_STACK; lia|].
      cbn [offs_wins map]. apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
    pose proof (ffkeepX_trans w _ _ _ m M1 m2 FK1 FK2 (incl_refl _) (incl_refl _)) as FK.
    assert (CF2 : rw_cells asegs m2 (wa_ff w + 9120) [C4 (Z_to_bv 64 fw)]).
    { apply (FK 9120 _); [lia | cbn; lia | | exact CF].
      apply Forall_cons; [| apply Forall_nil]; cbn [fst snd cells_size csize]; lia. }
    assert (CW2 : rw_cells asegs m2 (wa_ff w + 9136) [C2 (Z_to_bv 64 (fw / 2 ^ 16))]).
    { apply (FK 9136 _); [lia | cbn; lia | | exact CW].
      apply Forall_cons; [| apply Forall_nil]; cbn [fst snd cells_size csize]; lia. }
    assert (CO2 : rw_cells asegs m2 (wa_ff w + 9050) [C2 (Z_to_bv 64 (fw mod 2 ^ 16))]).
    { apply (FK 9050 _); [lia | cbn; lia | | exact CO].
      apply Forall_cons; [| apply Forall_nil]; cbn [fst snd cells_size csize]; lia. }
    pose proof (regs_keep w [] R1 R2 RT_F0A44 HT1 KEEP2) as HT2. change (rt_keep RT_F0A44) with RT_F0A44 in HT2.
    pose proof (pmxa_restrict H HHm LINV LINV_frame w _ _ _ _ _ _ _ TBL_F0A6C_RUN [] [] 0 TBL_F0A6C [] OK X2
                  tbl_f0a6c_incl (incl_refl _)) as X3.
    apply (K msF2 mo2 m2 R2 r); [constructor | exact FK].
    - exact X3.
    - exact Htr.
    - exact Hbsz.
    - exact Hbud.
    - exact Hv1.
    - exact KR2.
    - exact VIS2.
    - exact RF2.
    - exact FZ0.
    - exact HT2.
    - rewrite (KEEP2 3%bv ltac:(inb)), (HR1 3%bv). exact G3_0.
    - rewrite (KEEP2 4%bv ltac:(inb)), (HR1 4%bv). exact G4_0.
    - exact Hfw.
    - exact Hwc.
    - exact CF2.
    - exact CW2.
    - exact CO2.
    - exact Gr.
    - exact Hr.
    - exact Hiff.
    - exact Hfound.
    - intros Hr0. apply (rw_cells_same M1 m2 _ _ CE). intros a Ha. cbn [cells_size csize] in Ha.
      apply (Hmiss Hr0 a). lia.
  Qed.
End U2Dm.
