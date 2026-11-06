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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmCall LbA_PmXp LbA_PmExit LbA_PmInit LbA_PmFin LbA_PmExit2 LbA_DiagStmt LbA_PmDS LbA_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_DStat LbA_TablStmt LbA_PmLH LbA_PmU2K LbA_PmOL LbA_PmLeaf LbA_PmU3XK LbA_PmU5K.

Definition RT_PM_U5M_L0_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8784)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608); (25%bv, ELit 18446744071562067968)].
Definition RT_PM_U5M_L0Z_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8784)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608); (27%bv, ELit 0)].
Definition RT_PM_U5M_LHS_1 : list (reg * expr) := [(1%bv, ELit 980724); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (12%bv, EAlu ALU_ADD (EVar 33) (ELit 8784)); (18%bv, EVar 33); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8784)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_LHC_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8784)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_LTM_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8784)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_LTE_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8784)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608); (27%bv, ELit 0)].
Definition RT_PM_U5M_XNZ_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8784)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608)].

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

#[local] Definition HTbAPmU5Mb_0 : list (Z * expr) := [(1056, EVar 33); (968, EVar 33); (1040, EVar 33); (1048, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (1000, EAlu ALU_ADD (EVar 32) (ELit 48)); (1008, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (936, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (944, EAlu ALU_ADD (EVar 32) (ELit 56)); (960, EAlu ALU_ADD (EVar 33) (ELit 11488)); (712, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 92)) (ELit 3)) (ELit 2147450880)); (632, EAlu ALU_ADD (EVar 32) (ELit 92)); (848, EAlu ALU_ADD (EVar 32) (ELit 88)); (800, EAlu ALU_ADD (EVar 33) (ELit 10512)); (976, ELit 2147450880); (720, EAlu ALU_ADD (EVar 33) (ELit 10496)); (784, EAlu ALU_ADD (EVar 33) (ELit 10416)); (808, EVar 32); (792, EAlu ALU_ADD (EVar 32) (ELit 80)); (344, EAlu ALU_ADD (EVar 33) (ELit 10432)); (440, EAlu ALU_ADD (EVar 33) (ELit 10436)); (216, EAlu ALU_ADD (EVar 33) (ELit 6737)); (488, EAlu ALU_ADD (EVar 33) (ELit 6736)); (888, EAlu ALU_ADD (EVar 33) (ELit 10426)); (648, EAlu ALU_ADD (EVar 33) (ELit 11024)); (520, EAlu ALU_ADD (EVar 33) (ELit 9312)); (728, EAlu ALU_ADD (EVar 33) (ELit 10992)); (704, EAlu ALU_ADD (EVar 33) (ELit 10528)); (688, EAlu ALU_ADD (EVar 33) (ELit 10352)); (736, EAlu ALU_ADD (EVar 33) (ELit 10288)); (640, EAlu ALU_ADD (EVar 33) (ELit 10224)); (608, EAlu ALU_ADD (EVar 33) (ELit 10160)); (680, EAlu ALU_ADD (EVar 33) (ELit 10096)); (592, EAlu ALU_ADD (EVar 33) (ELit 10032)); (528, EAlu ALU_ADD (EVar 33) (ELit 9968)); (496, EAlu ALU_ADD (EVar 33) (ELit 9904)); (504, EAlu ALU_ADD (EVar 33) (ELit 9840)); (296, EAlu ALU_ADD (EVar 33) (ELit 9376)); (392, EAlu ALU_ADD (EVar 33) (ELit 9344)); (776, EAlu ALU_ADD (EVar 33) (ELit 9280)); (128, EAlu ALU_ADD (EVar 33) (ELit 7264)); (536, EAlu ALU_ADD (EVar 33) (ELit 8816)); (584, EAlu ALU_ADD (EVar 33) (ELit 8784)); (144, EAlu ALU_ADD (EVar 33) (ELit 8752)); (232, EAlu ALU_ADD (EVar 33) (ELit 8288)); (304, EAlu ALU_ADD (EVar 33) (ELit 8256)); (576, EAlu ALU_ADD (EVar 33) (ELit 8224)); (696, EAlu ALU_ADD (EVar 33) (ELit 7760)); (672, EAlu ALU_ADD (EVar 33) (ELit 7728)); (112, EAlu ALU_ADD (EVar 33) (ELit 6800)); (136, EAlu ALU_ADD (EVar 33) (ELit 4816)); (24, EAlu ALU_ADD (EVar 33) (ELit 6272)); (72, EAlu ALU_ADD (EVar 33) (ELit 5808)); (224, EAlu ALU_ADD (EVar 33) (ELit 5344)); (32, EAlu ALU_ADD (EVar 33) (ELit 5312)); (48, EAlu ALU_ADD (EVar 33) (ELit 4848)); (256, EAlu ALU_ADD (EVar 33) (ELit 4352)); (248, EAlu ALU_ADD (EVar 33) (ELit 2400)); (184, EAlu ALU_ADD (EVar 33) (ELit 4336)); (56, EAlu ALU_ADD (EVar 33) (ELit 3872)); (152, EAlu ALU_ADD (EVar 33) (ELit 3840)); (64, EAlu ALU_ADD (EVar 33) (ELit 3824)); (320, EAlu ALU_ADD (EVar 33) (ELit 3792)); (240, EAlu ALU_ADD (EVar 33) (ELit 3328)); (40, EAlu ALU_ADD (EVar 33) (ELit 2864)); (360, EAlu ALU_ADD (EVar 32) (ELit 32)); (336, EAlu ALU_ADD (EVar 32) (ELit 152)); (312, EAlu ALU_ADD (EVar 32) (ELit 168)); (400, EAlu ALU_ADD (EVar 32) (ELit 160)); (384, EAlu ALU_ADD (EVar 32) (ELit 144)); (448, EAlu ALU_ADD (EVar 32) (ELit 136)); (352, EAlu ALU_ADD (EVar 32) (ELit 96)); (208, EAlu ALU_ADD (EVar 32) (ELit 176)); (600, EAlu ALU_ADD (EVar 32) (ELit 93)); (544, EAlu ALU_ADD (EVar 32) (ELit 280)); (864, EAlu ALU_ADD (EVar 32) (ELit 272)); (952, EAlu ALU_ADD (EVar 32) (ELit 264)); (872, EAlu ALU_ADD (EVar 32) (ELit 8)); (752, EAlu ALU_ADD (EVar 32) (ELit 40)); (856, EAlu ALU_ADD (EVar 32) (ELit 232)); (896, EAlu ALU_ADD (EVar 32) (ELit 224)); (768, EAlu ALU_ADD (EVar 32) (ELit 216)); (992, EAlu ALU_ADD (EVar 32) (ELit 256)); (928, EAlu ALU_ADD (EVar 32) (ELit 248)); (920, EAlu ALU_ADD (EVar 32) (ELit 240)); (432, EAlu ALU_ADD (EVar 33) (ELit 12480)); (424, EAlu ALU_ADD (EVar 33) (ELit 12016)); (552, EAlu ALU_ADD (EVar 33) (ELit 11552)); (568, EAlu ALU_ADD (EVar 33) (ELit 11520)); (176, EAlu ALU_ADD (EVar 33) (ELit 1936)); (160, EAlu ALU_ADD (EVar 33) (ELit 1472)); (168, EAlu ALU_ADD (EVar 33) (ELit 1008)); (912, EAlu ALU_ADD (EVar 33) (ELit 944)); (80, EAlu ALU_ADD (EVar 33) (ELit 928)); (96, EAlu ALU_ADD (EVar 33) (ELit 896)); (88, EAlu ALU_ADD (EVar 33) (ELit 880)); (264, ELit 16843009); (272, ELit 252645135); (280, ELit 858993459); (288, ELit 1431655765); (368, ELit 18446744072850558157); (120, ELit 65535); (200, ELit 262140); (104, EAlu ALU_ADD (EVar 33) (ELit 848)); (656, EAlu ALU_ADD (EVar 33) (ELit 784)); (616, EAlu ALU_ADD (EVar 33) (ELit 720)); (624, EAlu ALU_ADD (EVar 33) (ELit 656)); (512, EAlu ALU_ADD (EVar 33) (ELit 592)); (464, EAlu ALU_ADD (EVar 33) (ELit 528)); (472, EAlu ALU_ADD (EVar 33) (ELit 464)); (984, EAlu ALU_ADD (EVar 33) (ELit 448)); (408, EAlu ALU_ADD (EVar 33) (ELit 384)); (456, EAlu ALU_ADD (EVar 33) (ELit 320)); (328, EAlu ALU_ADD (EVar 33) (ELit 256)); (416, EAlu ALU_ADD (EVar 33) (ELit 192)); (480, EAlu ALU_ADD (EVar 33) (ELit 128)); (376, EAlu ALU_ADD (EVar 33) (ELit 64)); (192, EAlu ALU_ADD (EVar 33) (ELit 32)); (1016, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (1024, EAlu ALU_ADD (EVar 32) (ELit 72)); (560, EAlu ALU_ADD (EVar 32) (ELit 16)); (840, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 80)) (ELit 3)) (ELit 2147450880)); (880, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (1032, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 248)) (ELit 3)) (ELit 2147450880)); (904, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 256)) (ELit 3)) (ELit 2147450880)); (832, EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)); (744, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (760, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (816, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 40)) (ELit 3)); (824, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (1096, EAlu ALU_ADD (EVar 33) (ELit 10416)); (1088, EAlu ALU_ADD (EVar 33) (ELit 10496)); (1080, EVar 32); (1072, EAlu ALU_ADD (EVar 33) (ELit 10512)); (1064, EAlu ALU_ADD (EVar 33) (ELit 11488))].
  Lemma pm_u5m_l0 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (wv : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xef688) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 27%bv = Z_to_bv 64 (sx32A wv) ->
    0 < wv < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xef6d4) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 25%bv = Z_to_bv 64 18446744071562067968 -> PropExec.getr R1 27%bv = PropExec.getr R 27%bv -> m1 = m -> (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc wv  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX27 HWV K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KRange (EVar 27) 1 (2 ^ 64)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 27)) with (PropExec.getr R 27%bv). rewrite HX27, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). destruct (sx32A_range' wv ltac:(lia)) as (SR1 & SR2 & SR3). rewrite Z.mod_small by lia. lia. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 27) 1 (2 ^ 64)] HK1 20%nat [0xef6d4] (@nil bool) 41%N
          [18; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_L0_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_L0_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with 0xef6d4 in VIS1 by reflexivity. eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | (rewrite (HR1 25%bv); reflexivity) | (rewrite (HR1 27%bv); reflexivity) | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 26%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_l0z : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xef688) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_MLZ -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xefa5c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> m1 = m -> (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 10%nat [0xefa5c] (@nil bool) 41%N
          [18; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_L0Z_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_L0Z_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with 0xefa5c in VIS1 by reflexivity. eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 26%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_lhs : forall (w : pmwA H) s LB LBs m mo c msF R F fc (j wr : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xef6d4) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 25%bv = Z_to_bv 64 (sx32A (2 ^ j)) ->
    PropExec.getr R 27%bv = Z_to_bv 64 (sx32A wr) ->
    0 <= j <= 31 ->
    0 <= wr < 2 ^ 32 ->
    Z.testbit wr j = true ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [18; 46; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xef6f4 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = PropExec.getr R 26%bv -> PropExec.getr R1 11%bv = PropExec.getr R 25%bv -> PropExec.getr R1 12%bv = Z_to_bv 64 (wa_ff w + 8784) -> PropExec.getr R1 25%bv = PropExec.getr R 25%bv -> PropExec.getr R1 27%bv = PropExec.getr R 27%bv -> rw_cells asegs m1 (wa_ff w + 8784) [C8 (Z_to_bv 64 0)] -> ffkeepX w [(8784, 8)] m m1 -> (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc j wr  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX25 HX27 HJ HWR HB K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 40%nat [AT_LOOKUP_OPERAND] [false] 41%N
          [18; 46; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_LHS_1.
    { split_scs. apply (mask_br_set (Eseed R (wenv_vals w ++ (@nil word))) j wr); [change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 25)) with (PropExec.getr R 25%bv); exact HX25 | change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 27)) with (PropExec.getr R 27%bv); exact HX27 | exact HJ | exact HWR | exact HB]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_LHS_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(8784, 8)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147450880 + 2048); (EVar 33, 8784, 8792)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; first [apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; lia]] |]); apply Forall_nil). } assert (CE : rw_cells asegs M1 (wa_ff w + 8784) [C8 (Z_to_bv 64 0)]). { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf1 | reflexivity | cbn [firstn]; repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)), ?EFc; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Q6 Q13 BNDc; unfold SHBASE in *; lia |]); apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite EFc; reflexivity | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 8784 + i) with (wa_ff w + (8784 + i)) by lia; apply FW2; lia | reflexivity | exact Logic.I | reflexivity]. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CE | exact FK | (rewrite (HR1 10%bv); reflexivity) | (rewrite (HR1 11%bv); reflexivity) | (rewrite (HR1 25%bv); reflexivity) | (rewrite (HR1 27%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 26%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_lhc : forall (w : pmwA H) s LB LBs m mo c msF R F fc (j wr : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xef6d4) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 25%bv = Z_to_bv 64 (sx32A (2 ^ j)) ->
    PropExec.getr R 27%bv = Z_to_bv 64 (sx32A wr) ->
    0 <= j <= 31 ->
    0 <= wr < 2 ^ 32 ->
    Z.testbit wr j = false ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xef6cc) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 25%bv = PropExec.getr R 25%bv -> PropExec.getr R1 27%bv = PropExec.getr R 27%bv -> m1 = m -> (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc j wr  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX25 HX27 HJ HWR HB K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 10%nat [0xef6cc] [true] 41%N
          [18; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_LHC_1.
    { split_scs. apply (mask_br_clr (Eseed R (wenv_vals w ++ (@nil word))) j wr); [change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 25)) with (PropExec.getr R 25%bv); exact HX25 | change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 27)) with (PropExec.getr R 27%bv); exact HX27 | exact HJ | exact HWR | exact HB]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_LHC_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with 0xef6cc in VIS1 by reflexivity. eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (rewrite (HR1 25%bv); reflexivity) | (rewrite (HR1 27%bv); reflexivity) | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 26%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_ltm : forall (w : pmwA H) s LB LBs m mo c msF R F fc (j wr : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xef6cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 25%bv = Z_to_bv 64 (sx32A (2 ^ j)) ->
    PropExec.getr R 27%bv = Z_to_bv 64 (sx32A wr) ->
    0 <= j <= 31 ->
    0 <= wr < 2 ^ 32 ->
    1 <= j ->
    wr <> 0 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xef6d4) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 25%bv = Z_to_bv 64 (sx32A (2 ^ (j - 1))) -> PropExec.getr R1 27%bv = PropExec.getr R 27%bv -> m1 = m -> (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc j wr  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX25 HX27 HJ HWR HJ1 HNZ K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KRange (EVar 27) 1 (2 ^ 64)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 27)) with (PropExec.getr R 27%bv). rewrite HX27, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). destruct (sx32A_range' wr ltac:(lia)) as (SR1 & SR2 & SR3). rewrite Z.mod_small by lia. lia. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 27) 1 (2 ^ 64)] HK1 10%nat [0xef6d4] (@nil bool) 41%N
          [18; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_LTM_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_LTM_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (rewrite (HR1 25%bv); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e end; apply (mask_srl_val (Eseed R (wenv_vals w ++ [])) j); [change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 25)) with (PropExec.getr R 25%bv); exact HX25 | exact HJ | exact HJ1]) | (rewrite (HR1 27%bv); reflexivity) | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 26%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_lte : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xef6cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_MLZ -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xefa5c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> m1 = m -> (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 10%nat [0xefa5c] (@nil bool) 41%N
          [18; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_LTE_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_LTE_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with 0xefa5c in VIS1 by reflexivity. eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 26%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_xnz : forall (w : pmwA H) s LB LBs m mo c msF R F fc (xj : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xefa5c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_s1 w + 1108) [C4 (Z_to_bv 64 xj)] ->
    0 <= xj < 2 ^ 32 ->
    xj <> 0 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_PUSHK) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] -> regs_tbl w R1 RT_PUSHK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> m1 = m -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc xj  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Cj Hxj HNZ KP.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) m [KWord (SA (EVar WV_S1) 1108) 4 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) OK (env_world_seed H w R [Z_to_bv 64 xj])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { destruct (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 xj])) as (_ & _ & _ & E35 & _). assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) (EVar 41) = Z_to_bv 64 xj) by reflexivity. eapply (kword_of_rw_cells asegs _ m (wa_s1 w + 1108) _ 0%nat (C4 (Z_to_bv 64 xj))); [exact Cj | reflexivity | reflexivity | lia | unfold estart, WV_S1; cbn [a_base a_off]; rewrite E35, u64_of_Z by (pose proof (pmw_bounds H w OK); lia); cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; reflexivity]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 xj]
          [KWord (SA (EVar WV_S1) 1108) 4 (EVar 41)] HK1 10%nat [0xf22cc] [false] 42%N
          [18; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTbAPmU5Mb_0 (@nil (Z * expr)) RT_PM_U5M_XNZ_1.
    { split_scs. cbn [sc_denot]. assert (E41s : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) (EVar 41) = Z_to_bv 64 xj) by reflexivity. rewrite (edenot_sext32 (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) 41 xj E41s Hxj). change (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 xj])) (ELit 0)) with (Z_to_bv 64 0). destruct (sx32A_range' xj Hxj) as (SR1 & SR2 & SR3). rewrite br_eq by lia. apply Z.eqb_neq. lia. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_XNZ_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity. eapply (KP msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_PUSHK HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 26%bv)]; first [reflexivity | symmetry; rtf HT0]) | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) ].
  Qed.

End U5Mb.
