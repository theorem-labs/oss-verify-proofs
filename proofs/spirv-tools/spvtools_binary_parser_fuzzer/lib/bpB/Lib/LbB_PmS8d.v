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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_ContStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmWXK LbB_PmS8K.

Definition RT_PM_S8D_S0_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8D_S1_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 0); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 1); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8D_L0_1 : list (reg * expr) := [(1%bv, ELit 999816); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8D_L1_1 : list (reg * expr) := [(1%bv, ELit 999816); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 1); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8D_C_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8D_P_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 0); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 1); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8X_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section S8d.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTLbAPmS8d_0 : list (Z * expr) := TBL_EEF44.
  Lemma pm_s8d_s0 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (spal b0 ty : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] spal -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4164) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8D0 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] ->
    0 <= b0 < 256 /\ b0 mod 2 = 0 ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_CHECK) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXAT H LINV w s LB LBs m1 mo1 c (OB_PARSED_OPERAND :: S_INSTR) TBL_EEF44 [] [] spal -> regs_tbl w R1 RT_CHECK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall rr : reg, In rr [18%bv; 19%bv; 22%bv; 23%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> ffkeepX w [] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc spal b0 ty  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HB0 HB0R HTY KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    destruct HB0R as [HB0a HB0b].
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) m [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) OK (env_world_seed H w R [Z_to_bv 64 b0])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { assert (E41k : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) (EVar 41) = Z_to_bv 64 (b0)) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 b0))); [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41k; symmetry; apply w1_b8; lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 b0]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41)] HK1 60%nat [OL_CHECK] [true] 42%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmS8d_0 (@nil (Z * expr)) RT_PM_S8D_S0_1.
    { split_scs; cbn [sc_denot]; (assert (E41s : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) (EVar 41) = Z_to_bv 64 b0) by reflexivity); first [ rewrite (sc_b0_long_ne (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) 41 b0 E41s HB0a) | rewrite (sc_b0_long_eq (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) 41 b0 E41s HB0a) ]; rewrite ?HB0b; first [ reflexivity | (apply Z.eqb_neq; lia) | (apply Z.eqb_eq; lia) | (apply negb_true_iff; apply Z.eqb_neq; lia) | (apply negb_false_iff; apply Z.eqb_eq; lia) ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8D_S0_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 b0])) as TEF1. change (EVar WV_FF) with (EVar 33%N) in TEF1.
    pose proof (ev_s1 H w _ OK (env_world_seed H w R [Z_to_bv 64 b0])) as TES1. change (EVar WV_S1) with (EVar 35%N) in TES1.
    destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 b0])) as (TEA1 & TEB1 & _).
    assert (TEP1 : bv_unsigned (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) (EVar 32)) = wa_p w) by (rewrite TEA1; apply u64_of_Z; pose proof (pmw_bounds H w OK); lia).
    pose proof (pmw_apart_ff H HHm LINV w _ _ _ _ _ _ _ _ _ _ _ OK X1) as (TPA1 & _). unfold PARSER_SIZE in TPA1.
    assert (TFK1 : ffkeepX w [] m M1).
    { clear - OK Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 AC1 AC2 AC3 AC4 WN Hlf1 TEF1 TES1 TEA1 TEB1 TEP1 TPA1.
      pose proof (pmw_bounds H w OK) as BNDt.
      pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928)] Hlf1 ltac:(vm_compute; reflexivity)) as TMU. cbn [num_wins map] in TMU.
      rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB1 ltac:(lia)) in TMU. rewrite ?TEF1, ?TES1, ?TEP1 in TMU.
      apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)).
      repeat (apply Forall_cons; [cbn [fst snd]; first [left; lia | right; left; lia | (destruct Q6 as [Q6'|Q6']; [left | right; left]; unfold SHBASE in *; lia) | (destruct TPA1 as [TPA'|TPA']; [right; left; lia | left; lia])
         ] |]); apply Forall_nil. }
    assert (HTY_1 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)]) by (apply (ffkeepX_cell w _ _ _ _ _ TFK1 HTY); [lia | cbn; lia | reflexivity]).
    replace (s_pc SSr) with OL_CHECK in VIS1 by reflexivity. eapply (KC msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_CHECK HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 19%bv) | rewrite (HR1 22%bv) | rewrite (HR1 23%bv) | rewrite (HR1 25%bv)]; reflexivity) | exact TFK1 ].
  Qed.

  Lemma pm_s8d_s1 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (spal b0 ty : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] spal -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4164) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8D1 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] ->
    0 <= b0 < 256 /\ b0 mod 2 = 0 ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_PUSHK) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXAT H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] [] spal -> regs_tbl w R1 RT_PUSHK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall rr : reg, In rr [18%bv; 19%bv; 22%bv; 23%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> ffkeepX w [] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc spal b0 ty  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HB0 HB0R HTY KP.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    destruct HB0R as [HB0a HB0b].
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) m [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) OK (env_world_seed H w R [Z_to_bv 64 b0])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { assert (E41k : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) (EVar 41) = Z_to_bv 64 (b0)) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 b0))); [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41k; symmetry; apply w1_b8; lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 b0]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41)] HK1 60%nat [OL_PUSHK] [true] 42%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmS8d_0 (@nil (Z * expr)) RT_PM_S8D_S1_1.
    { split_scs; cbn [sc_denot]; (assert (E41s : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) (EVar 41) = Z_to_bv 64 b0) by reflexivity); first [ rewrite (sc_b0_long_ne (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) 41 b0 E41s HB0a) | rewrite (sc_b0_long_eq (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) 41 b0 E41s HB0a) ]; rewrite ?HB0b; first [ reflexivity | (apply Z.eqb_neq; lia) | (apply Z.eqb_eq; lia) | (apply negb_true_iff; apply Z.eqb_neq; lia) | (apply negb_false_iff; apply Z.eqb_eq; lia) ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8D_S1_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 b0])) as TEF1. change (EVar WV_FF) with (EVar 33%N) in TEF1.
    pose proof (ev_s1 H w _ OK (env_world_seed H w R [Z_to_bv 64 b0])) as TES1. change (EVar WV_S1) with (EVar 35%N) in TES1.
    destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 b0])) as (TEA1 & TEB1 & _).
    assert (TEP1 : bv_unsigned (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) (EVar 32)) = wa_p w) by (rewrite TEA1; apply u64_of_Z; pose proof (pmw_bounds H w OK); lia).
    pose proof (pmw_apart_ff H HHm LINV w _ _ _ _ _ _ _ _ _ _ _ OK X1) as (TPA1 & _). unfold PARSER_SIZE in TPA1.
    assert (TFK1 : ffkeepX w [] m M1).
    { clear - OK Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 AC1 AC2 AC3 AC4 WN Hlf1 TEF1 TES1 TEA1 TEB1 TEP1 TPA1.
      pose proof (pmw_bounds H w OK) as BNDt.
      pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0])) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928)] Hlf1 ltac:(vm_compute; reflexivity)) as TMU. cbn [num_wins map] in TMU.
      rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB1 ltac:(lia)) in TMU. rewrite ?TEF1, ?TES1, ?TEP1 in TMU.
      apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)).
      repeat (apply Forall_cons; [cbn [fst snd]; first [left; lia | right; left; lia | (destruct Q6 as [Q6'|Q6']; [left | right; left]; unfold SHBASE in *; lia) | (destruct TPA1 as [TPA'|TPA']; [right; left; lia | left; lia])
         ] |]); apply Forall_nil. }
    assert (HTY_1 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)]) by (apply (ffkeepX_cell w _ _ _ _ _ TFK1 HTY); [lia | cbn; lia | reflexivity]).
    replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity. eapply (KP msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_PUSHK HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 19%bv) | rewrite (HR1 22%bv) | rewrite (HR1 23%bv) | rewrite (HR1 25%bv)]; reflexivity) | exact TFK1 ].
  Qed.

  Lemma pm_s8d_l0 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (spal b0 cp dp ty : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] spal -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4164) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8D0 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] ->
    0 <= b0 < 256 /\ b0 mod 2 = 1 ->
    rw_cells asegs m (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)] ->
    rw_cells asegs m (wa_ff w + 5952) [C8 (Z_to_bv 64 dp)] ->
    0 <= dp < 2 ^ 64 ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AOPDEL2) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXAT H LINV w s LB LBs m1 mo1 c S_STR TBL_EEF44 [] [] spal -> regs_tbl w R1 RT_S8D0 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf4188 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 8%bv = Z_to_bv 64 (wa_sp0 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 dp -> (forall rr : reg, In rr [18%bv; 19%bv; 22%bv; 23%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> ffkeepX w [] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc spal b0 cp dp ty  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HB0 HB0R HCP HDP HDPR HTY KD.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    destruct HB0R as [HB0a HB0b].
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) m [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5936) 8 (EVar 42); KWord (SA (EVar WV_FF) 5952) 8 (EVar 43)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) as EF.
      apply Forall_cons; [| idtac].
      { assert (E41k : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 41) = Z_to_bv 64 (b0)) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 b0))); [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41k; symmetry; apply w1_b8; lia]. }
      apply Forall_cons; [| idtac].
      { assert (E42k : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 42) = Z_to_bv 64 (cp)) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C8 (Z_to_bv 64 cp))); [exact HCP | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E42k; reflexivity]. }
      apply Forall_cons; [| apply Forall_nil].
      { assert (E43k : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 43) = Z_to_bv 64 (dp)) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5952) _ 0%nat (C8 (Z_to_bv 64 dp))); [exact HDP | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E43k; reflexivity]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5936) 8 (EVar 42); KWord (SA (EVar WV_FF) 5952) 8 (EVar 43)] HK1 60%nat [AOPDEL2] [false] 44%N
          [3; 4; 24; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmS8d_0 (@nil (Z * expr)) RT_PM_S8D_L0_1.
    { split_scs; cbn [sc_denot]; (assert (E41s : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 41) = Z_to_bv 64 b0) by reflexivity); first [ rewrite (sc_b0_long_ne (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) 41 b0 E41s HB0a) | rewrite (sc_b0_long_eq (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) 41 b0 E41s HB0a) ]; rewrite ?HB0b; first [ reflexivity | (apply Z.eqb_neq; lia) | (apply Z.eqb_eq; lia) | (apply negb_true_iff; apply Z.eqb_neq; lia) | (apply negb_false_iff; apply Z.eqb_eq; lia) ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8D_L0_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) as TEF1. change (EVar WV_FF) with (EVar 33%N) in TEF1.
    pose proof (ev_s1 H w _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) as TES1. change (EVar WV_S1) with (EVar 35%N) in TES1.
    destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) as (TEA1 & TEB1 & _).
    assert (TEP1 : bv_unsigned (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 32)) = wa_p w) by (rewrite TEA1; apply u64_of_Z; pose proof (pmw_bounds H w OK); lia).
    pose proof (pmw_apart_ff H HHm LINV w _ _ _ _ _ _ _ _ _ _ _ OK X1) as (TPA1 & _). unfold PARSER_SIZE in TPA1.
    assert (TFK1 : ffkeepX w [] m M1).
    { clear - OK Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 AC1 AC2 AC3 AC4 WN Hlf1 TEF1 TES1 TEA1 TEB1 TEP1 TPA1.
      pose proof (pmw_bounds H w OK) as BNDt.
      pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928)] Hlf1 ltac:(vm_compute; reflexivity)) as TMU. cbn [num_wins map] in TMU.
      rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB1 ltac:(lia)) in TMU. rewrite ?TEF1, ?TES1, ?TEP1 in TMU.
      apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)).
      repeat (apply Forall_cons; [cbn [fst snd]; first [left; lia | right; left; lia | (destruct Q6 as [Q6'|Q6']; [left | right; left]; unfold SHBASE in *; lia) | (destruct TPA1 as [TPA'|TPA']; [right; left; lia | left; lia])
         ] |]); apply Forall_nil. }
    assert (HTY_1 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)]) by (apply (ffkeepX_cell w _ _ _ _ _ TFK1 HTY); [lia | cbn; lia | reflexivity]).
    pose proof (pmw_bounds H w OK) as BNDk. replace (s_pc SSr) with AOPDEL2 in VIS1 by reflexivity. eapply (KD msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8D0 HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 19%bv) | rewrite (HR1 22%bv) | rewrite (HR1 23%bv) | rewrite (HR1 25%bv)]; reflexivity) | exact TFK1 | (rewrite (HR1 _); unfold SSr; cbn [sr_get s_regs nth]; first [reflexivity | (cbn [edenot]; ev_xs; reflexivity)]) ].
  Qed.

  Lemma pm_s8d_l1 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (spal b0 cp dp ty : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] spal -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4164) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8D1 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] ->
    0 <= b0 < 256 /\ b0 mod 2 = 1 ->
    rw_cells asegs m (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)] ->
    rw_cells asegs m (wa_ff w + 5952) [C8 (Z_to_bv 64 dp)] ->
    0 <= dp < 2 ^ 64 ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AOPDEL2) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXAT H LINV w s LB LBs m1 mo1 c S_STR TBL_EEF44 [] [] spal -> regs_tbl w R1 RT_S8D1 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf4188 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 8%bv = Z_to_bv 64 (wa_sp0 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 dp -> (forall rr : reg, In rr [18%bv; 19%bv; 22%bv; 23%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> ffkeepX w [] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc spal b0 cp dp ty  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HB0 HB0R HCP HDP HDPR HTY KD.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    destruct HB0R as [HB0a HB0b].
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) m [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5936) 8 (EVar 42); KWord (SA (EVar WV_FF) 5952) 8 (EVar 43)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) as EF.
      apply Forall_cons; [| idtac].
      { assert (E41k : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 41) = Z_to_bv 64 (b0)) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C1 (b8 b0))); [exact HB0 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41k; symmetry; apply w1_b8; lia]. }
      apply Forall_cons; [| idtac].
      { assert (E42k : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 42) = Z_to_bv 64 (cp)) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5936) _ 0%nat (C8 (Z_to_bv 64 cp))); [exact HCP | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E42k; reflexivity]. }
      apply Forall_cons; [| apply Forall_nil].
      { assert (E43k : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 43) = Z_to_bv 64 (dp)) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 5952) _ 0%nat (C8 (Z_to_bv 64 dp))); [exact HDP | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E43k; reflexivity]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5936) 8 (EVar 42); KWord (SA (EVar WV_FF) 5952) 8 (EVar 43)] HK1 60%nat [AOPDEL2] [false] 44%N
          [3; 4; 24; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmS8d_0 (@nil (Z * expr)) RT_PM_S8D_L1_1.
    { split_scs; cbn [sc_denot]; (assert (E41s : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 41) = Z_to_bv 64 b0) by reflexivity); first [ rewrite (sc_b0_long_ne (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) 41 b0 E41s HB0a) | rewrite (sc_b0_long_eq (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) 41 b0 E41s HB0a) ]; rewrite ?HB0b; first [ reflexivity | (apply Z.eqb_neq; lia) | (apply Z.eqb_eq; lia) | (apply negb_true_iff; apply Z.eqb_neq; lia) | (apply negb_false_iff; apply Z.eqb_eq; lia) ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8D_L1_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) as TEF1. change (EVar WV_FF) with (EVar 33%N) in TEF1.
    pose proof (ev_s1 H w _ OK (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) as TES1. change (EVar WV_S1) with (EVar 35%N) in TES1.
    destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) as (TEA1 & TEB1 & _).
    assert (TEP1 : bv_unsigned (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) (EVar 32)) = wa_p w) by (rewrite TEA1; apply u64_of_Z; pose proof (pmw_bounds H w OK); lia).
    pose proof (pmw_apart_ff H HHm LINV w _ _ _ _ _ _ _ _ _ _ _ OK X1) as (TPA1 & _). unfold PARSER_SIZE in TPA1.
    assert (TFK1 : ffkeepX w [] m M1).
    { clear - OK Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 AC1 AC2 AC3 AC4 WN Hlf1 TEF1 TES1 TEA1 TEB1 TEP1 TPA1.
      pose proof (pmw_bounds H w OK) as BNDt.
      pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 cp; Z_to_bv 64 dp])) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928)] Hlf1 ltac:(vm_compute; reflexivity)) as TMU. cbn [num_wins map] in TMU.
      rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB1 ltac:(lia)) in TMU. rewrite ?TEF1, ?TES1, ?TEP1 in TMU.
      apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)).
      repeat (apply Forall_cons; [cbn [fst snd]; first [left; lia | right; left; lia | (destruct Q6 as [Q6'|Q6']; [left | right; left]; unfold SHBASE in *; lia) | (destruct TPA1 as [TPA'|TPA']; [right; left; lia | left; lia])
         ] |]); apply Forall_nil. }
    assert (HTY_1 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)]) by (apply (ffkeepX_cell w _ _ _ _ _ TFK1 HTY); [lia | cbn; lia | reflexivity]).
    pose proof (pmw_bounds H w OK) as BNDk. replace (s_pc SSr) with AOPDEL2 in VIS1 by reflexivity. eapply (KD msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8D1 HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 19%bv) | rewrite (HR1 22%bv) | rewrite (HR1 23%bv) | rewrite (HR1 25%bv)]; reflexivity) | exact TFK1 | (rewrite (HR1 _); unfold SSr; cbn [sr_get s_regs nth]; first [reflexivity | (cbn [edenot]; ev_xs; reflexivity)]) ].
  Qed.

  Lemma pm_s8d_c : forall (w : pmwA H) s LB LBs m mo c msF R F fc (spal ty : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] spal -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4188) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8D0 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_CHECK) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXAT H LINV w s LB LBs m1 mo1 c (OB_PARSED_OPERAND :: S_INSTR) TBL_EEF44 [] [] spal -> regs_tbl w R1 RT_CHECK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall rr : reg, In rr [18%bv; 19%bv; 22%bv; 23%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> ffkeepX w [] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc spal ty  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HTY KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 60%nat [OL_CHECK] (@nil bool) 41%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmS8d_0 (@nil (Z * expr)) RT_PM_S8D_C_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8D_C_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as TEF1. change (EVar WV_FF) with (EVar 33%N) in TEF1.
    pose proof (ev_s1 H w _ OK (env_world_seed H w R (@nil word))) as TES1. change (EVar WV_S1) with (EVar 35%N) in TES1.
    destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (TEA1 & TEB1 & _).
    assert (TEP1 : bv_unsigned (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 32)) = wa_p w) by (rewrite TEA1; apply u64_of_Z; pose proof (pmw_bounds H w OK); lia).
    pose proof (pmw_apart_ff H HHm LINV w _ _ _ _ _ _ _ _ _ _ _ OK X1) as (TPA1 & _). unfold PARSER_SIZE in TPA1.
    assert (TFK1 : ffkeepX w [] m M1).
    { clear - OK Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 AC1 AC2 AC3 AC4 WN Hlf1 TEF1 TES1 TEA1 TEB1 TEP1 TPA1.
      pose proof (pmw_bounds H w OK) as BNDt.
      pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928)] Hlf1 ltac:(vm_compute; reflexivity)) as TMU. cbn [num_wins map] in TMU.
      rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB1 ltac:(lia)) in TMU. rewrite ?TEF1, ?TES1, ?TEP1 in TMU.
      apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)).
      repeat (apply Forall_cons; [cbn [fst snd]; first [left; lia | right; left; lia | (destruct Q6 as [Q6'|Q6']; [left | right; left]; unfold SHBASE in *; lia) | (destruct TPA1 as [TPA'|TPA']; [right; left; lia | left; lia])
         ] |]); apply Forall_nil. }
    assert (HTY_1 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)]) by (apply (ffkeepX_cell w _ _ _ _ _ TFK1 HTY); [lia | cbn; lia | reflexivity]).
    replace (s_pc SSr) with OL_CHECK in VIS1 by reflexivity. eapply (KC msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_CHECK HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 19%bv) | rewrite (HR1 22%bv) | rewrite (HR1 23%bv) | rewrite (HR1 25%bv)]; reflexivity) | exact TFK1 ].
  Qed.

  Lemma pm_s8d_p : forall (w : pmwA H) s LB LBs m mo c msF R F fc (spal ty : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] spal -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4188) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8D1 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_PUSHK) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXAT H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] [] spal -> regs_tbl w R1 RT_PUSHK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall rr : reg, In rr [18%bv; 19%bv; 22%bv; 23%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> ffkeepX w [] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc spal ty  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HTY KP.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 60%nat [OL_PUSHK] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmS8d_0 (@nil (Z * expr)) RT_PM_S8D_P_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8D_P_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as TEF1. change (EVar WV_FF) with (EVar 33%N) in TEF1.
    pose proof (ev_s1 H w _ OK (env_world_seed H w R (@nil word))) as TES1. change (EVar WV_S1) with (EVar 35%N) in TES1.
    destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (TEA1 & TEB1 & _).
    assert (TEP1 : bv_unsigned (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 32)) = wa_p w) by (rewrite TEA1; apply u64_of_Z; pose proof (pmw_bounds H w OK); lia).
    pose proof (pmw_apart_ff H HHm LINV w _ _ _ _ _ _ _ _ _ _ _ OK X1) as (TPA1 & _). unfold PARSER_SIZE in TPA1.
    assert (TFK1 : ffkeepX w [] m M1).
    { clear - OK Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 AC1 AC2 AC3 AC4 WN Hlf1 TEF1 TES1 TEA1 TEB1 TEP1 TPA1.
      pose proof (pmw_bounds H w OK) as BNDt.
      pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928)] Hlf1 ltac:(vm_compute; reflexivity)) as TMU. cbn [num_wins map] in TMU.
      rewrite ?(srl3_val _ (EVar 33) (wa_ff w) TEB1 ltac:(lia)) in TMU. rewrite ?TEF1, ?TES1, ?TEP1 in TMU.
      apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)).
      repeat (apply Forall_cons; [cbn [fst snd]; first [left; lia | right; left; lia | (destruct Q6 as [Q6'|Q6']; [left | right; left]; unfold SHBASE in *; lia) | (destruct TPA1 as [TPA'|TPA']; [right; left; lia | left; lia])
         ] |]); apply Forall_nil. }
    assert (HTY_1 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)]) by (apply (ffkeepX_cell w _ _ _ _ _ TFK1 HTY); [lia | cbn; lia | reflexivity]).
    replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity. eapply (KP msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_PUSHK HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 19%bv) | rewrite (HR1 22%bv) | rewrite (HR1 23%bv) | rewrite (HR1 25%bv)]; reflexivity) | exact TFK1 ].
  Qed.

  Lemma pm_s8x : forall (w : pmwA H) s LB LBs m mo c msF R F fc (spal : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] spal -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2dec) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf4164) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXAT H LINV w s LB LBs m1 mo1 c S_STR TBL_EEF44 [] [] spal -> regs_tbl w R1 RT_S8D0 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 23%bv = PropExec.getr R 10%bv -> m1 = m -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc spal  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 KXD.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 20%nat [0xf4164] (@nil bool) 41%N
          [3; 4; 24; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmS8d_0 (@nil (Z * expr)) RT_PM_S8X_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8X_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    eapply (KXD msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8D0 HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); [ rewrite (HR1 23%bv); reflexivity | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) ].
  Qed.

End S8d.
