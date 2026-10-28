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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmU3XK.

Definition RT_PM_U9_S2_1 : list (reg * expr) := [(1%bv, ELit 991688); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 32) (ELit 96)); (11%bv, EAlu ALU_ADD (EVar 33) (ELit 4528)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 4528)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section U9s2.
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

  Lemma pm_u9_s2 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (sel : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 20; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf21b4) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (sx32A sel) ->
    0 <= sel < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xfa08c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s
      LB LBs m1 mo1 c [3; 4; 20; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ARM -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      PropExec.getr R1 1%bv = Z_to_bv 64 0xf21c8 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w + 96) ->
      PropExec.getr R1 11%bv = Z_to_bv 64 (wa_ff w + 4528) -> PropExec.getr R1 21%bv = Z_to_bv 64 (wa_ff w + 4528) ->
      rw_cells asegs m1 (wa_ff w + 4528) [C4 (Z_to_bv 64 sel)] -> ffkeepX w [(4528, 4)] m m1 -> (forall rr : reg, In
      rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc sel  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX10 HSEL K2.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 60%nat [0xfa08c] (@nil bool) 41%N
          [3; 4; 20; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U9_S2_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U9_S2_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc.
    change (EVar WV_FF) with (EVar 33%N) in EFc.
    pose proof (pmw_bounds H w OK) as BNDc.
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2).
    change (fsz PM_FCLASS) with 16384 in FW2.
    assert (FK : ffkeepX w [(4528, 4)] m M1).
    { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EVar 33, 4528, 4532)] Hlf1
        ltac:(vm_compute; reflexivity)) as MUc.
      cbn [num_wins map] in MUc. rewrite ?EFc in MUc.
      apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)).
      apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (CK4 : rw_cells asegs M1 (wa_ff w + 4528) [C4 (Z_to_bv 64 sel)]).
    { subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat (EVar 33%N) 4528 4 (EVar 10));
        [ exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFc; reflexivity
        | split; [lia|]; split; [lia|]; intros i Hi;
          replace (wa_ff w + 4528 + i) with (wa_ff w + (4528 + i)) by lia; apply FW2; lia
        | reflexivity | exact Logic.I
        | rewrite (w2lb4_sx32A sel HSEL);
          change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 10)) with (PropExec.getr R 10%bv);
          rewrite HX10; reflexivity ]. }
    eapply (K2 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ARM HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1);
      first [ rtf HT1 | exact CK4 | exact FK
            | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]];
               [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

End U9s2.
