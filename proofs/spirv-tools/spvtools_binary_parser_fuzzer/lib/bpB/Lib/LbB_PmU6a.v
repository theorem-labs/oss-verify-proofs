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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmU3XK LbB_PmU3T LbB_HFind LbB_HEmpStmt LbB_PmWXK LbB_PmU6K.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmEmh.

Definition RT_U6F0 : list (reg * expr) := RT_ARM ++ [(10%bv, ELit 0); (21%bv, WADD WV_FF 9060)].
Definition RT_U6G  : list (reg * expr) := RT_ARM ++ [(21%bv, WADD WV_FF 9060)].
Definition RT_U6E0 : list (reg * expr) := RT_U6G ++ [(10%bv, ELit 0)].
Definition RT_U6E1 : list (reg * expr) := RT_U6G ++ [(10%bv, ELit 1)].
Definition RT_U6M  : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 9060); (23%bv, ELit 2147450880); (24%bv, WADD WV_FF 7984); (26%bv, WADD WV_FF 112); (27%bv, ELit 18446744073709551608)].
Definition RT_U6X  : list (reg * expr) := RT_U6M.

Definition RT_PM_U6_1_1 : list (reg * expr) := [(1%bv, ELit 993120); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 32) (ELit 96)); (11%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_G_1 : list (reg * expr) := [(1%bv, ELit 998056); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_EA0_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 9056)); (11%bv, ELit 0); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, ELit 2147450880); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_EA1_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (11%bv, ELit 0); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, ELit 2147450880); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_EB_1 : list (reg * expr) := [(1%bv, ELit 998108); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 32) (ELit 96)); (11%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, ELit 2147450880); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_H1_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (11%bv, ELit 0); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, ELit 2147450880); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U6_H3_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 0); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9060)); (23%bv, ELit 2147450880); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section U6a.
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
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTLbAPmU6a_0 : list (Z * expr) := TBL_EEF44.
  Lemma pm_u6_1 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (wv : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2744) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 21%bv = Z_to_bv 64 (sx32A wv) ->
    0 < wv < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 LbB_HFind.FIND) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ARM -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf2760 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w + 96) -> PropExec.getr R1 11%bv = Z_to_bv 64 (wa_ff w + 9060) -> PropExec.getr R1 21%bv = Z_to_bv 64 (wa_ff w + 9060) -> rw_cells asegs m1 (wa_ff w + 9060) [C4 (Z_to_bv 64 wv)] -> ffkeepX w [(9060, 4)] m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc wv  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX27 HWV K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KRange (EVar 21) 1 (2 ^ 64)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 21)) with (PropExec.getr R 21%bv). rewrite HX27, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec wv (2 ^ 31)); rewrite Z.mod_small by lia; lia. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 21) 1 (2 ^ 64)] HK1 50%nat [0xfa08c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmU6a_0 (@nil (Z * expr)) RT_PM_U6_1_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U6_1_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(9060, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EVar 33, 9060, 9064)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; apply Exists_cons_hd; cbn [fst snd]; lia] |]); apply Forall_nil). } assert (CD : rw_cells asegs M1 (wa_ff w + 9060) [C4 (Z_to_bv 64 wv)]). { subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat (EVar 33%N) 9060 4 (EVar 21)); [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFc; reflexivity | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 9060 + i) with (wa_ff w + (9060 + i)) by lia; apply FW2; lia | reflexivity | exact Logic.I | cbn [cbytes]; change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 21)) with (PropExec.getr R 21%bv); rewrite HX27; symmetry; apply w2le4_sx32A; lia]. } pose proof (pmw_bounds H w OK) as BNDk. replace (s_pc SSr) with LbB_HFind.FIND in VIS1 by reflexivity. eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ARM HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CD | exact FK | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 22%bv) | rewrite (HR1 25%bv)]; reflexivity) | (rewrite (HR1 _); cbn [sr_get s_regs nth]; first [reflexivity | (eapply ev_add; [reflexivity | lia | lia]) | (cbn [edenot]; ev_xs; first [reflexivity | (rewrite u64_of_Z by lia; reflexivity)])]) ].
  Qed.

  Lemma pm_u6_g : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2760) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_U6F0 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_GENERATES_TYPE) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_U6G -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf3aa8 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = PropExec.getr R 22%bv -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> m1 = m -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 KG.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 30%nat [AT_GENERATES_TYPE] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmU6a_0 (@nil (Z * expr)) RT_PM_U6_G_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U6_G_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with AT_GENERATES_TYPE in VIS1 by reflexivity. eapply (KG msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_U6G HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | (rewrite (HR1 10%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 22%bv) | rewrite (HR1 25%bv)]; reflexivity) | reflexivity ].
  Qed.

  Lemma pm_u6_ea0 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (val : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf3aa8) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_U6E0 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 9056) [C4 (Z_to_bv 64 val)] ->
    0 <= val < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf3ad0) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_U6X -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 19%bv = Z_to_bv 64 (sx32A val) -> ffkeepX w [] m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc val  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 CTID HVAL KEA.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 val])) m [KWord (SA (EVar WV_FF) 9056) 4 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 val])) OK (env_world_seed H w R [Z_to_bv 64 val])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 val])) (EVar 41) = Z_to_bv 64 val) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 9056) _ 0%nat (C4 (Z_to_bv 64 val))); [exact CTID | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; reflexivity]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 val]
          [KWord (SA (EVar WV_FF) 9056) 4 (EVar 41)] HK1 30%nat [0xf3ad0] (@nil bool) 42%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmU6a_0 (@nil (Z * expr)) RT_PM_U6_EA0_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U6_EA0_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 val])) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 val])) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 val])) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147450880 + 2048)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; apply Exists_cons_hd; cbn [fst snd]; lia] |]); apply Forall_nil). } replace (s_pc SSr) with 0xf3ad0 in VIS1 by reflexivity. assert (E41v : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 val])) (EVar 41) = Z_to_bv 64 val) by reflexivity. eapply (KEA msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_U6X HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ exact FK | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 22%bv) | rewrite (HR1 25%bv)]; reflexivity) | (rewrite (HR1 19%bv); cbn [sr_get s_regs nth]; apply (edenot_sext32 _ 41 val E41v); lia) ].
  Qed.

  Lemma pm_u6_ea1 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (val : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf3aa8) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_U6E1 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 9060) [C4 (Z_to_bv 64 val)] ->
    0 <= val < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf3ad0) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_U6X -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 19%bv = Z_to_bv 64 (sx32A val) -> ffkeepX w [] m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc val  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 CRID HVAL KEA.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 val])) m [KWord (SA (EVar WV_FF) 9060) 4 (EVar 41); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 9060)) (ELit 3)) 2147450880) 1 (ELit 0)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 val])) OK (env_world_seed H w R [Z_to_bv 64 val])) as EF.
      apply Forall_cons; [| idtac].
      { assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 val])) (EVar 41) = Z_to_bv 64 val) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 9060) _ 0%nat (C4 (Z_to_bv 64 val))); [exact CRID | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; reflexivity]. }
      apply Forall_cons; [| apply Forall_nil].
      { eapply pmk_sh_ffu with (1 := OK) (2 := X0) (3 := (env_world_seed H w R [Z_to_bv 64 val])); [lia | vm_compute; reflexivity]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 val]
          [KWord (SA (EVar WV_FF) 9060) 4 (EVar 41); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 9060)) (ELit 3)) 2147450880) 1 (ELit 0)] HK1 30%nat [0xf3ad0] (@nil bool) 42%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmU6a_0 (@nil (Z * expr)) RT_PM_U6_EA1_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U6_EA1_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R [Z_to_bv 64 val])) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 val])) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ [Z_to_bv 64 val])) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147450880 + 2048)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; apply Exists_cons_hd; cbn [fst snd]; lia] |]); apply Forall_nil). } replace (s_pc SSr) with 0xf3ad0 in VIS1 by reflexivity. assert (E41v : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 val])) (EVar 41) = Z_to_bv 64 val) by reflexivity. eapply (KEA msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_U6X HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ exact FK | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 22%bv) | rewrite (HR1 25%bv)]; reflexivity) | (rewrite (HR1 19%bv); cbn [sr_get s_regs nth]; apply (edenot_sext32 _ 41 val E41v); lia) ].
  Qed.

  Lemma pm_u6_eb : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf3ad0) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_U6X -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 (LbB_PmEmh.emh_entry LbB_PmEmh.EMH_U32)) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_U6M -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf3adc -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w + 96) -> PropExec.getr R1 11%bv = Z_to_bv 64 (wa_ff w + 9060) -> PropExec.getr R1 19%bv = PropExec.getr R 19%bv -> ffkeepX w [] m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 KE.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 40%nat [0xf9064] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmU6a_0 (@nil (Z * expr)) RT_PM_U6_EB_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U6_EB_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147450880 + 2048)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; apply Exists_cons_hd; cbn [fst snd]; lia] |]); apply Forall_nil). } pose proof (pmw_bounds H w OK) as BNDk. replace (s_pc SSr) with (LbB_PmEmh.emh_entry LbB_PmEmh.EMH_U32) in VIS1 by reflexivity. eapply (KE msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_U6M HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact FK | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 22%bv) | rewrite (HR1 25%bv)]; reflexivity) | (rewrite (HR1 19%bv); reflexivity) | (rewrite (HR1 _); cbn [sr_get s_regs nth]; first [reflexivity | (eapply ev_add; [reflexivity | lia | lia]) | (cbn [edenot]; ev_xs; first [reflexivity | (rewrite u64_of_Z by lia; reflexivity)])]) ].
  Qed.

  Lemma pm_u6_h1 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (q : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf3adc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_U6M -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (q + 20) ->
    16 <= q /\ q + 24 <= 2 ^ 47 ->
    addressable m q 24 ->
    q + 24 <= wa_ff w \/ wa_ff w + 16384 <= q ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf3aec) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_U6M -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 10%bv = Z_to_bv 64 (q + 20) -> PropExec.getr R1 19%bv = PropExec.getr R 19%bv -> ffkeepX w [] m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc q  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX10 HQ AD HQF KH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KRange (EVar 10) 36 (2 ^ 47); KWord (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) 2147450880) 1 (ELit 0)]).
    { apply Forall_cons; [| idtac].
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 10)) with (PropExec.getr R 10%bv). rewrite HX10, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
      apply Forall_cons; [| apply Forall_nil].
      { apply (kshadow0 (Eseed R (wenv_vals w ++ (@nil word))) m (EVar 10) (q + 20)); [ (change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 10)) with (PropExec.getr R 10%bv); exact HX10) | lia | eapply (sh0_of_addressable m q 24 (q + 20)); [exact AD | change (8 * (24 / 8)) with 24; lia] ]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 10) 36 (2 ^ 47); KWord (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) 2147450880) 1 (ELit 0)] HK1 30%nat [0xf3aec] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmU6a_0 (@nil (Z * expr)) RT_PM_U6_H1_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U6_H1_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147450880 + 2048)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; apply Exists_cons_hd; cbn [fst snd]; lia] |]); apply Forall_nil). } replace (s_pc SSr) with 0xf3aec in VIS1 by reflexivity. eapply (KH msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_U6M HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact FK | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 22%bv) | rewrite (HR1 25%bv)]; reflexivity) | (rewrite (HR1 10%bv); exact HX10) | (rewrite (HR1 10%bv); transitivity (PropExec.getr R 10%bv); [reflexivity | exact HX10]) | (rewrite (HR1 19%bv); reflexivity) ].
  Qed.

  Lemma pm_u6_h3 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf3af0) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_U6M -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_PUSHK) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] -> regs_tbl w R1 RT_PUSHK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> m1 = m -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 KP.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 20%nat [OL_PUSHK] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmU6a_0 (@nil (Z * expr)) RT_PM_U6_H3_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U6_H3_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity. eapply (KP msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_PUSHK HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 18%bv) | rewrite (HR1 22%bv) | rewrite (HR1 25%bv)]; reflexivity) | reflexivity ].
  Qed.

End U6a.
