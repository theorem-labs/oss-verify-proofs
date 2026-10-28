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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmFin LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmU3XK LbB_PmU5K.

Definition RT_PM_U5M_L0_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, ELit 18446744071562067968); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_L0Z_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_LHS_1 : list (reg * expr) := [(1%bv, ELit 989324); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (12%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_LHC_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_LTM_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_LTE_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_XNZ_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 0); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section U5Mb.
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

#[local] Definition HTbAPmU5Mb_0 : list (Z * expr) := [(32, EAlu ALU_ADD (EVar 33) (ELit 5472)); (40, EAlu ALU_ADD (EVar 33) (ELit 4496)); (48, EAlu ALU_ADD (EVar 33) (ELit 2048)); (56, EAlu ALU_ADD (EVar 33) (ELit 4032)); (64, EAlu ALU_ADD (EVar 33) (ELit 3056)); (72, EAlu ALU_ADD (EVar 33) (ELit 3008)); (80, EAlu ALU_ADD (EVar 33) (ELit 5008)); (88, EAlu ALU_ADD (EVar 33) (ELit 32)); (96, EAlu ALU_ADD (EVar 33) (ELit 4000)); (104, ELit 65535); (112, EAlu ALU_ADD (EVar 33) (ELit 6000)); (120, EAlu ALU_ADD (EVar 33) (ELit 6464)); (128, EAlu ALU_ADD (EVar 33) (ELit 7952)); (136, EAlu ALU_ADD (EVar 33) (ELit 3024)); (144, EAlu ALU_ADD (EVar 33) (ELit 656)); (152, EAlu ALU_ADD (EVar 33) (ELit 192)); (160, EAlu ALU_ADD (EVar 33) (ELit 1120)); (168, EAlu ALU_ADD (EVar 33) (ELit 3520)); (176, ELit 262140); (184, EAlu ALU_ADD (EVar 32) (ELit 176)); (192, EAlu ALU_ADD (EVar 33) (ELit 5937)); (200, EAlu ALU_ADD (EVar 33) (ELit 4544)); (208, EAlu ALU_ADD (EVar 33) (ELit 2512)); (216, EAlu ALU_ADD (EVar 33) (ELit 1584)); (224, EAlu ALU_ADD (EVar 33) (ELit 3536)); (232, EAlu ALU_ADD (EVar 33) (ELit 8576)); (240, EAlu ALU_ADD (EVar 33) (ELit 7456)); (248, EAlu ALU_ADD (EVar 33) (ELit 4528)); (256, EAlu ALU_ADD (EVar 33) (ELit 7488)); (264, EAlu ALU_ADD (EVar 33) (ELit 10640)); (272, EAlu ALU_ADD (EVar 32) (ELit 96)); (280, EAlu ALU_ADD (EVar 33) (ELit 9056)); (288, EAlu ALU_ADD (EVar 33) (ELit 11104)); (296, EAlu ALU_ADD (EVar 33) (ELit 8544)); (304, EAlu ALU_ADD (EVar 33) (ELit 9060)); (312, EAlu ALU_ADD (EVar 33) (ELit 2976)); (320, EAlu ALU_ADD (EVar 33) (ELit 5936)); (328, EAlu ALU_ADD (EVar 33) (ELit 10176)); (336, EAlu ALU_ADD (EVar 33) (ELit 8512)); (344, EAlu ALU_ADD (EVar 33) (ELit 8016)); (352, EAlu ALU_ADD (EVar 33) (ELit 7424)); (360, EAlu ALU_ADD (EVar 32) (ELit 92)); (368, EAlu ALU_ADD (EVar 32) (ELit 93)); (376, EAlu ALU_ADD (EVar 32) (ELit 40)); (384, EAlu ALU_ADD (EVar 33) (ELit 6928)); (392, EAlu ALU_ADD (EVar 33) (ELit 6960)); (400, EAlu ALU_ADD (EVar 33) (ELit 9616)); (408, EAlu ALU_ADD (EVar 32) (ELit 216)); (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (424, EAlu ALU_ADD (EVar 33) (ELit 96)); (432, EAlu ALU_ADD (EVar 32) (ELit 232)); (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (448, EAlu ALU_ADD (EVar 32) (ELit 224)); (456, EAlu ALU_ADD (EVar 33) (ELit 64)); (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (472, EAlu ALU_ADD (EVar 33) (ELit 176)); (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (488, EAlu ALU_ADD (EVar 33) (ELit 8480)); (496, EAlu ALU_ADD (EVar 33) (ELit 10112)); (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (512, EAlu ALU_ADD (EVar 32) (ELit 88)); (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (528, EAlu ALU_ADD (EVar 32) (ELit 48)); (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (544, ELit 2305843009213693952); (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (560, EAlu ALU_ADD (EVar 32) (ELit 240)); (568, EVar 33); (576, EVar 33); (584, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (592, EAlu ALU_ADD (EVar 32) (ELit 56)); (600, EAlu ALU_ADD (EVar 32) (ELit 272)); (608, EAlu ALU_ADD (EVar 33) (ELit 9050)); (616, ELit 2147450880); (624, EAlu ALU_ADD (EVar 33) (ELit 9040)); (632, EAlu ALU_ADD (EVar 32) (ELit 264)); (640, EAlu ALU_ADD (EVar 33) (ELit 9136)); (648, EVar 32); (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_ADD (EVar 32) (ELit 72)); (680, EVar 33); (688, EAlu ALU_ADD (EVar 33) (ELit 10112)); (696, EAlu ALU_ADD (EVar 33) (ELit 9136)); (704, EVar 32); (712, EAlu ALU_ADD (EVar 33) (ELit 9120)); (720, EAlu ALU_ADD (EVar 33) (ELit 9040))].
  Lemma pm_u5m_l0 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (wv : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf182c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 21%bv = Z_to_bv 64 (sx32A wv) ->
    0 < wv < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf186c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 23%bv = Z_to_bv 64 18446744071562067968 -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> m1 = m -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc wv  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX21 HWV K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KRange (EVar 21) 1 (2 ^ 64)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 21)) with (PropExec.getr R 21%bv). rewrite HX21, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). destruct (sx32A_range' wv ltac:(lia)) as (SR1 & SR2 & SR3). rewrite Z.mod_small by lia. lia. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 21) 1 (2 ^ 64)] HK1 20%nat [0xf186c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_L0_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_L0_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with 0xf186c in VIS1 by reflexivity. eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | (rewrite (HR1 23%bv); reflexivity) | (rewrite (HR1 21%bv); reflexivity) | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_l0z : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf182c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_MLZ -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf18ac) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> m1 = m -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 10%nat [0xf18ac] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_L0Z_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_L0Z_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with 0xf18ac in VIS1 by reflexivity. eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_lhs : forall (w : pmwA H) s LB LBs m mo c msF R F fc (j wr : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf186c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 23%bv = Z_to_bv 64 (sx32A (2 ^ j)) ->
    PropExec.getr R 21%bv = Z_to_bv 64 (sx32A wr) ->
    0 <= j <= 31 ->
    0 <= wr < 2 ^ 32 ->
    Z.testbit wr j = true ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 33; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf188c -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = PropExec.getr R 18%bv -> PropExec.getr R1 11%bv = PropExec.getr R 23%bv -> PropExec.getr R1 12%bv = Z_to_bv 64 (wa_ff w + 7984) -> PropExec.getr R1 23%bv = PropExec.getr R 23%bv -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 7984) [C8 (Z_to_bv 64 0)] -> ffkeepX w [(7984, 8)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc j wr  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX23 HX21 HJ HWR HB K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 40%nat [AT_LOOKUP_OPERAND] [false] 41%N
          [3; 4; 33; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_LHS_1.
    { split_scs. apply (mask_br_set (Eseed R (wenv_vals w ++ (@nil word))) j wr); [change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 23)) with (PropExec.getr R 23%bv); exact HX23 | change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 21)) with (PropExec.getr R 21%bv); exact HX21 | exact HJ | exact HWR | exact HB]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_LHS_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(7984, 8)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147450880 + 2048); (EVar 33, 7984, 7992)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; first [apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; lia]] |]); apply Forall_nil). } assert (CE : rw_cells asegs M1 (wa_ff w + 7984) [C8 (Z_to_bv 64 0)]). { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf1 | reflexivity | cbn [firstn]; repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)), ?EFc; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Q6 Q13 BNDc; unfold SHBASE in *; lia |]); apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite EFc; reflexivity | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 7984 + i) with (wa_ff w + (7984 + i)) by lia; apply FW2; lia | reflexivity | exact Logic.I | reflexivity]. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CE | exact FK | (rewrite (HR1 10%bv); reflexivity) | (rewrite (HR1 11%bv); reflexivity) | (rewrite (HR1 23%bv); reflexivity) | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_lhc : forall (w : pmwA H) s LB LBs m mo c msF R F fc (j wr : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf186c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 23%bv = Z_to_bv 64 (sx32A (2 ^ j)) ->
    PropExec.getr R 21%bv = Z_to_bv 64 (sx32A wr) ->
    0 <= j <= 31 ->
    0 <= wr < 2 ^ 32 ->
    Z.testbit wr j = false ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf1864) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 23%bv = PropExec.getr R 23%bv -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> m1 = m -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc j wr  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX23 HX21 HJ HWR HB K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 10%nat [0xf1864] [true] 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_LHC_1.
    { split_scs. apply (mask_br_clr (Eseed R (wenv_vals w ++ (@nil word))) j wr); [change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 23)) with (PropExec.getr R 23%bv); exact HX23 | change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 21)) with (PropExec.getr R 21%bv); exact HX21 | exact HJ | exact HWR | exact HB]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_LHC_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with 0xf1864 in VIS1 by reflexivity. eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (rewrite (HR1 23%bv); reflexivity) | (rewrite (HR1 21%bv); reflexivity) | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_ltm : forall (w : pmwA H) s LB LBs m mo c msF R F fc (j wr : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1864) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 23%bv = Z_to_bv 64 (sx32A (2 ^ j)) ->
    PropExec.getr R 21%bv = Z_to_bv 64 (sx32A wr) ->
    0 <= j <= 31 ->
    0 <= wr < 2 ^ 32 ->
    1 <= j ->
    wr <> 0 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf186c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 23%bv = Z_to_bv 64 (sx32A (2 ^ (j - 1))) -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> m1 = m -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc j wr  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX23 HX21 HJ HWR HJ1 HNZ K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KRange (EVar 21) 1 (2 ^ 64)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 21)) with (PropExec.getr R 21%bv). rewrite HX21, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). destruct (sx32A_range' wr ltac:(lia)) as (SR1 & SR2 & SR3). rewrite Z.mod_small by lia. lia. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 21) 1 (2 ^ 64)] HK1 10%nat [0xf186c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_LTM_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_LTM_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (rewrite (HR1 23%bv); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e end; apply (mask_srl_val (Eseed R (wenv_vals w ++ [])) j); [change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 23)) with (PropExec.getr R 23%bv); exact HX23 | exact HJ | exact HJ1]) | (rewrite (HR1 21%bv); reflexivity) | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_lte : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1864) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_MLZ -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf18ac) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> m1 = m -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 10%nat [0xf18ac] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_LTE_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_LTE_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with 0xf18ac in VIS1 by reflexivity. eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_xnz : forall (w : pmwA H) s LB LBs m mo c msF R F fc (xj : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf18ac) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 176) [C4 (Z_to_bv 64 xj)] ->
    0 <= xj < 2 ^ 32 ->
    xj <> 0 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_PUSHK) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] -> regs_tbl w R1 RT_PUSHK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> m1 = m -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc xj  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Cj Hxj HNZ KP.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) m [KWord (SA (EVar WV_FF) 176) 4 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) OK (env_world_seed H w R [Z_to_bv 64 xj])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 xj])) as (_ & E33 & _). assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) (EVar 41) = Z_to_bv 64 xj) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_ff w + 176) _ 0%nat (C4 (Z_to_bv 64 xj))); [exact Cj | reflexivity | reflexivity | lia | unfold estart, WV_FF; cbn [a_base a_off]; rewrite E33, u64_of_Z by (pose proof (pmw_bounds H w OK); lia); cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; reflexivity]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 xj]
          [KWord (SA (EVar WV_FF) 176) 4 (EVar 41)] HK1 10%nat [OL_PUSHK] [false] 42%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_XNZ_1.
    { split_scs. cbn [sc_denot]. assert (E41s : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) (EVar 41) = Z_to_bv 64 xj) by reflexivity. rewrite (edenot_sext32 (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) 41 xj E41s Hxj). change (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) (ELit 0)) with (Z_to_bv 64 0). destruct (sx32A_range' xj Hxj) as (SR1 & SR2 & SR3). rewrite br_eq by lia. apply Z.eqb_neq. lia. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_XNZ_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity. eapply (KP msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_PUSHK HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) ].
  Qed.

End U5Mb.
