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

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_DStat LbA_TablStmt LbA_PmLH LbA_PmU2K LbA_PmOL LbA_PmLeaf LbA_PmU3XK.

Definition RT_PM_U9_S2_1 : list (reg * expr) := [(1%bv, ELit 982664); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 32) (ELit 96)); (11%bv, EAlu ALU_ADD (EVar 35) (ELit 1104)); (18%bv, EVar 33); (19%bv, EVar 32); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608); (25%bv, EAlu ALU_ADD (EVar 33) (ELit 944))].

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
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xefe78) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (sx32A sel) ->
    0 <= sel < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf86c4) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ARM -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xefe88 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w + 96) -> PropExec.getr R1 11%bv = Z_to_bv 64 (wa_s1 w + 1104) -> rw_cells asegs m1 (wa_s1 w + 1104) [C4 (Z_to_bv 64 sel)] -> ffkeepX w [] m m1 -> (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc sel  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX10 HSEL K2.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 60%nat [0xf86c4] (@nil bool) 41%N
          [18; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) [(1056, EVar 33); (968, EVar 33); (1040, EVar 33); (1048, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (1000, EAlu ALU_ADD (EVar 32) (ELit 48)); (1008, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (936, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (944, EAlu ALU_ADD (EVar 32) (ELit 56)); (960, EAlu ALU_ADD (EVar 33) (ELit 11488)); (712, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 92)) (ELit 3)) (ELit 2147450880)); (632, EAlu ALU_ADD (EVar 32) (ELit 92)); (848, EAlu ALU_ADD (EVar 32) (ELit 88)); (800, EAlu ALU_ADD (EVar 33) (ELit 10512)); (976, ELit 2147450880); (720, EAlu ALU_ADD (EVar 33) (ELit 10496)); (784, EAlu ALU_ADD (EVar 33) (ELit 10416)); (808, EVar 32); (792, EAlu ALU_ADD (EVar 32) (ELit 80)); (344, EAlu ALU_ADD (EVar 33) (ELit 10432)); (440, EAlu ALU_ADD (EVar 33) (ELit 10436)); (216, EAlu ALU_ADD (EVar 33) (ELit 6737)); (488, EAlu ALU_ADD (EVar 33) (ELit 6736)); (888, EAlu ALU_ADD (EVar 33) (ELit 10426)); (648, EAlu ALU_ADD (EVar 33) (ELit 11024)); (520, EAlu ALU_ADD (EVar 33) (ELit 9312)); (728, EAlu ALU_ADD (EVar 33) (ELit 10992)); (704, EAlu ALU_ADD (EVar 33) (ELit 10528)); (688, EAlu ALU_ADD (EVar 33) (ELit 10352)); (736, EAlu ALU_ADD (EVar 33) (ELit 10288)); (640, EAlu ALU_ADD (EVar 33) (ELit 10224)); (608, EAlu ALU_ADD (EVar 33) (ELit 10160)); (680, EAlu ALU_ADD (EVar 33) (ELit 10096)); (592, EAlu ALU_ADD (EVar 33) (ELit 10032)); (528, EAlu ALU_ADD (EVar 33) (ELit 9968)); (496, EAlu ALU_ADD (EVar 33) (ELit 9904)); (504, EAlu ALU_ADD (EVar 33) (ELit 9840)); (296, EAlu ALU_ADD (EVar 33) (ELit 9376)); (392, EAlu ALU_ADD (EVar 33) (ELit 9344)); (776, EAlu ALU_ADD (EVar 33) (ELit 9280)); (128, EAlu ALU_ADD (EVar 33) (ELit 7264)); (536, EAlu ALU_ADD (EVar 33) (ELit 8816)); (584, EAlu ALU_ADD (EVar 33) (ELit 8784)); (144, EAlu ALU_ADD (EVar 33) (ELit 8752)); (232, EAlu ALU_ADD (EVar 33) (ELit 8288)); (304, EAlu ALU_ADD (EVar 33) (ELit 8256)); (576, EAlu ALU_ADD (EVar 33) (ELit 8224)); (696, EAlu ALU_ADD (EVar 33) (ELit 7760)); (672, EAlu ALU_ADD (EVar 33) (ELit 7728)); (112, EAlu ALU_ADD (EVar 33) (ELit 6800)); (136, EAlu ALU_ADD (EVar 33) (ELit 4816)); (24, EAlu ALU_ADD (EVar 33) (ELit 6272)); (72, EAlu ALU_ADD (EVar 33) (ELit 5808)); (224, EAlu ALU_ADD (EVar 33) (ELit 5344)); (32, EAlu ALU_ADD (EVar 33) (ELit 5312)); (48, EAlu ALU_ADD (EVar 33) (ELit 4848)); (256, EAlu ALU_ADD (EVar 33) (ELit 4352)); (248, EAlu ALU_ADD (EVar 33) (ELit 2400)); (184, EAlu ALU_ADD (EVar 33) (ELit 4336)); (56, EAlu ALU_ADD (EVar 33) (ELit 3872)); (152, EAlu ALU_ADD (EVar 33) (ELit 3840)); (64, EAlu ALU_ADD (EVar 33) (ELit 3824)); (320, EAlu ALU_ADD (EVar 33) (ELit 3792)); (240, EAlu ALU_ADD (EVar 33) (ELit 3328)); (40, EAlu ALU_ADD (EVar 33) (ELit 2864)); (360, EAlu ALU_ADD (EVar 32) (ELit 32)); (336, EAlu ALU_ADD (EVar 32) (ELit 152)); (312, EAlu ALU_ADD (EVar 32) (ELit 168)); (400, EAlu ALU_ADD (EVar 32) (ELit 160)); (384, EAlu ALU_ADD (EVar 32) (ELit 144)); (448, EAlu ALU_ADD (EVar 32) (ELit 136)); (352, EAlu ALU_ADD (EVar 32) (ELit 96)); (208, EAlu ALU_ADD (EVar 32) (ELit 176)); (600, EAlu ALU_ADD (EVar 32) (ELit 93)); (544, EAlu ALU_ADD (EVar 32) (ELit 280)); (864, EAlu ALU_ADD (EVar 32) (ELit 272)); (952, EAlu ALU_ADD (EVar 32) (ELit 264)); (872, EAlu ALU_ADD (EVar 32) (ELit 8)); (752, EAlu ALU_ADD (EVar 32) (ELit 40)); (856, EAlu ALU_ADD (EVar 32) (ELit 232)); (896, EAlu ALU_ADD (EVar 32) (ELit 224)); (768, EAlu ALU_ADD (EVar 32) (ELit 216)); (992, EAlu ALU_ADD (EVar 32) (ELit 256)); (928, EAlu ALU_ADD (EVar 32) (ELit 248)); (920, EAlu ALU_ADD (EVar 32) (ELit 240)); (432, EAlu ALU_ADD (EVar 33) (ELit 12480)); (424, EAlu ALU_ADD (EVar 33) (ELit 12016)); (552, EAlu ALU_ADD (EVar 33) (ELit 11552)); (568, EAlu ALU_ADD (EVar 33) (ELit 11520)); (176, EAlu ALU_ADD (EVar 33) (ELit 1936)); (160, EAlu ALU_ADD (EVar 33) (ELit 1472)); (168, EAlu ALU_ADD (EVar 33) (ELit 1008)); (912, EAlu ALU_ADD (EVar 33) (ELit 944)); (80, EAlu ALU_ADD (EVar 33) (ELit 928)); (96, EAlu ALU_ADD (EVar 33) (ELit 896)); (88, EAlu ALU_ADD (EVar 33) (ELit 880)); (264, ELit 16843009); (272, ELit 252645135); (280, ELit 858993459); (288, ELit 1431655765); (368, ELit 18446744072850558157); (120, ELit 65535); (200, ELit 262140); (104, EAlu ALU_ADD (EVar 33) (ELit 848)); (656, EAlu ALU_ADD (EVar 33) (ELit 784)); (616, EAlu ALU_ADD (EVar 33) (ELit 720)); (624, EAlu ALU_ADD (EVar 33) (ELit 656)); (512, EAlu ALU_ADD (EVar 33) (ELit 592)); (464, EAlu ALU_ADD (EVar 33) (ELit 528)); (472, EAlu ALU_ADD (EVar 33) (ELit 464)); (984, EAlu ALU_ADD (EVar 33) (ELit 448)); (408, EAlu ALU_ADD (EVar 33) (ELit 384)); (456, EAlu ALU_ADD (EVar 33) (ELit 320)); (328, EAlu ALU_ADD (EVar 33) (ELit 256)); (416, EAlu ALU_ADD (EVar 33) (ELit 192)); (480, EAlu ALU_ADD (EVar 33) (ELit 128)); (376, EAlu ALU_ADD (EVar 33) (ELit 64)); (192, EAlu ALU_ADD (EVar 33) (ELit 32)); (1016, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (1024, EAlu ALU_ADD (EVar 32) (ELit 72)); (560, EAlu ALU_ADD (EVar 32) (ELit 16)); (840, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 80)) (ELit 3)) (ELit 2147450880)); (880, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (1032, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 248)) (ELit 3)) (ELit 2147450880)); (904, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 256)) (ELit 3)) (ELit 2147450880)); (832, EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)); (744, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (760, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (816, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 40)) (ELit 3)); (824, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (1096, EAlu ALU_ADD (EVar 33) (ELit 10416)); (1088, EAlu ALU_ADD (EVar 33) (ELit 10496)); (1080, EVar 32); (1072, EAlu ALU_ADD (EVar 33) (ELit 10512)); (1064, EAlu ALU_ADD (EVar 33) (ELit 11488))] (@nil (Z * expr)) RT_PM_U9_S2_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U9_S2_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_s1 H w _ OK (env_world_seed H w R (@nil word))) as ES1c. change (EVar WV_S1) with (EVar 35%N) in ES1c. pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as STKc. pose proof (wr_at_of_stk asegs m (wa_lo w) (wa_sp0 w) STKc) as (WS0 & WS1 & WS2). assert (WRc : wr_at asegs m (wa_s1 w + 1104) 4). { split; [lia|]. split; [lia|]. intros i Hi. replace (wa_s1 w + 1104 + i) with (wa_lo w + (wa_s1 w + 1104 + i - wa_lo w)) by lia. apply WS2. lia. } assert (FK : ffkeepX w [] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EVar 35, 1104, 1108)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?ES1c in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. } assert (CK4 : rw_cells asegs M1 (wa_s1 w + 1104) [C4 (Z_to_bv 64 sel)]). { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf1 | reflexivity | cbn [firstn]; apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite ES1c; reflexivity | exact WRc | reflexivity | exact Logic.I | rewrite (w2lb4_sx32A sel HSEL); change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 10)) with (PropExec.getr R 10%bv); rewrite HX10; reflexivity]. } eapply (K2 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ARM HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CK4 | exact FK | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 26%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

End U9s2.
