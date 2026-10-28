(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Ox Require F07.
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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmVops LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmPD LbB_PmSL LbB_PmU3XK LbB_SnStmt LbB_PmU9K LbB_PmU9c.

Definition RT_PM_U9_S4P_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 0); (11%bv, ELit 2); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, ELit 0); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section U9s4p.
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

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

  Lemma pm_u9_s4p : forall (w : pmwA H) s LB LBs m mo c msF R F fc (nk : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 20; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf3b10) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_T9F -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 120) [C4 (Z_to_bv 64 nk)] ->
    0 <= nk < 2 ^ 32 ->
    nk = 1 \/ nk = 2 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_PUSHK) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] -> regs_tbl w R1 RT_PUSHK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall r : reg, In r [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 r = PropExec.getr R r) -> ffkeepX w [] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc nk Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 CNK HNKR HNK KP.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 nk])) m [KWord (SA (EVar WV_FF) 120) 4 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 nk])) OK (env_world_seed H w R [Z_to_bv 64 nk])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 nk])) (EVar 41) = Z_to_bv 64 nk) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 120) _ 0%nat (C4 (Z_to_bv 64 nk))); [exact CNK | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; reflexivity]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 nk]
          [KWord (SA (EVar WV_FF) 120) 4 (EVar 41)] HK1 40%nat [OL_PUSHK] [true; false] 42%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U9_S4P_1.
    { split_scs; cbn [sc_denot]; assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 nk])) (EVar 41) = Z_to_bv 64 nk) by reflexivity; cbn [edenot] in E41 |- *; rewrite E41; destruct HNK as [-> | ->]; vm_compute; reflexivity. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U9_S4P_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 nk])) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 nk])) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. assert (FK : ffkeepX w [] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 nk])) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147450880 + 2048)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; first [apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; lia]] |]); apply Forall_nil). }
    replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity.
    eapply (KP msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_PUSHK HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1);
      [ intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; reflexivity
      | exact FK ].
  Qed.

End U9s4p.
