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

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_DStat LbA_TablStmt LbA_ContStmt LbA_PmLH LbA_PmU2K LbA_PmOL LbA_PmLeaf LbA_PmU3XK LbA_PmU3T LbA_HFind LbA_HEmpStmt LbA_PmWXK LbA_PmU6K LbA_PmS8K.

Definition RT_PM_S8I_EA_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EVar 32); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608); (27%bv, EAlu ALU_ADD (EVar 33) (ELit 6736))].
Definition RT_PM_S8I_EB_1 : list (reg * expr) := [(1%bv, ELit 987084); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 32) (ELit 176)); (11%bv, EAlu ALU_ADD (EVar 33) (ELit 10436)); (12%bv, ELit 152064); (13%bv, EAlu ALU_ADD (EVar 33) (ELit 848)); (14%bv, EAlu ALU_ADD (EVar 33) (ELit 880)); (18%bv, ELit 2147450880); (19%bv, EVar 32); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608); (27%bv, EAlu ALU_ADD (EVar 33) (ELit 6736))].
Definition RT_PM_S8I_H1_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (11%bv, ELit 0); (18%bv, ELit 2147450880); (19%bv, EVar 32); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608); (27%bv, EAlu ALU_ADD (EVar 33) (ELit 6736))].
Definition RT_PM_S8I_H3_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EVar 32); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512)); (22%bv, ELit 18446744073709551608); (27%bv, ELit 1)].

Section S8i.
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

#[local] Definition HTLbAPmS8i_0 : list (Z * expr) := [(1056, EVar 33); (968, EVar 33); (1040, EVar 33); (1048, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (1000, EAlu ALU_ADD (EVar 32) (ELit 48)); (1008, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (936, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (944, EAlu ALU_ADD (EVar 32) (ELit 56)); (960, EAlu ALU_ADD (EVar 33) (ELit 11488)); (712, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 92)) (ELit 3)) (ELit 2147450880)); (632, EAlu ALU_ADD (EVar 32) (ELit 92)); (848, EAlu ALU_ADD (EVar 32) (ELit 88)); (800, EAlu ALU_ADD (EVar 33) (ELit 10512)); (976, ELit 2147450880); (720, EAlu ALU_ADD (EVar 33) (ELit 10496)); (784, EAlu ALU_ADD (EVar 33) (ELit 10416)); (808, EVar 32); (792, EAlu ALU_ADD (EVar 32) (ELit 80)); (344, EAlu ALU_ADD (EVar 33) (ELit 10432)); (440, EAlu ALU_ADD (EVar 33) (ELit 10436)); (216, EAlu ALU_ADD (EVar 33) (ELit 6737)); (488, EAlu ALU_ADD (EVar 33) (ELit 6736)); (888, EAlu ALU_ADD (EVar 33) (ELit 10426)); (648, EAlu ALU_ADD (EVar 33) (ELit 11024)); (520, EAlu ALU_ADD (EVar 33) (ELit 9312)); (728, EAlu ALU_ADD (EVar 33) (ELit 10992)); (704, EAlu ALU_ADD (EVar 33) (ELit 10528)); (688, EAlu ALU_ADD (EVar 33) (ELit 10352)); (736, EAlu ALU_ADD (EVar 33) (ELit 10288)); (640, EAlu ALU_ADD (EVar 33) (ELit 10224)); (608, EAlu ALU_ADD (EVar 33) (ELit 10160)); (680, EAlu ALU_ADD (EVar 33) (ELit 10096)); (592, EAlu ALU_ADD (EVar 33) (ELit 10032)); (528, EAlu ALU_ADD (EVar 33) (ELit 9968)); (496, EAlu ALU_ADD (EVar 33) (ELit 9904)); (504, EAlu ALU_ADD (EVar 33) (ELit 9840)); (296, EAlu ALU_ADD (EVar 33) (ELit 9376)); (392, EAlu ALU_ADD (EVar 33) (ELit 9344)); (776, EAlu ALU_ADD (EVar 33) (ELit 9280)); (128, EAlu ALU_ADD (EVar 33) (ELit 7264)); (536, EAlu ALU_ADD (EVar 33) (ELit 8816)); (584, EAlu ALU_ADD (EVar 33) (ELit 8784)); (144, EAlu ALU_ADD (EVar 33) (ELit 8752)); (232, EAlu ALU_ADD (EVar 33) (ELit 8288)); (304, EAlu ALU_ADD (EVar 33) (ELit 8256)); (576, EAlu ALU_ADD (EVar 33) (ELit 8224)); (696, EAlu ALU_ADD (EVar 33) (ELit 7760)); (672, EAlu ALU_ADD (EVar 33) (ELit 7728)); (112, EAlu ALU_ADD (EVar 33) (ELit 6800)); (136, EAlu ALU_ADD (EVar 33) (ELit 4816)); (24, EAlu ALU_ADD (EVar 33) (ELit 6272)); (72, EAlu ALU_ADD (EVar 33) (ELit 5808)); (224, EAlu ALU_ADD (EVar 33) (ELit 5344)); (32, EAlu ALU_ADD (EVar 33) (ELit 5312)); (48, EAlu ALU_ADD (EVar 33) (ELit 4848)); (256, EAlu ALU_ADD (EVar 33) (ELit 4352)); (248, EAlu ALU_ADD (EVar 33) (ELit 2400)); (184, EAlu ALU_ADD (EVar 33) (ELit 4336)); (56, EAlu ALU_ADD (EVar 33) (ELit 3872)); (152, EAlu ALU_ADD (EVar 33) (ELit 3840)); (64, EAlu ALU_ADD (EVar 33) (ELit 3824)); (320, EAlu ALU_ADD (EVar 33) (ELit 3792)); (240, EAlu ALU_ADD (EVar 33) (ELit 3328)); (40, EAlu ALU_ADD (EVar 33) (ELit 2864)); (360, EAlu ALU_ADD (EVar 32) (ELit 32)); (336, EAlu ALU_ADD (EVar 32) (ELit 152)); (312, EAlu ALU_ADD (EVar 32) (ELit 168)); (400, EAlu ALU_ADD (EVar 32) (ELit 160)); (384, EAlu ALU_ADD (EVar 32) (ELit 144)); (448, EAlu ALU_ADD (EVar 32) (ELit 136)); (352, EAlu ALU_ADD (EVar 32) (ELit 96)); (208, EAlu ALU_ADD (EVar 32) (ELit 176)); (600, EAlu ALU_ADD (EVar 32) (ELit 93)); (544, EAlu ALU_ADD (EVar 32) (ELit 280)); (864, EAlu ALU_ADD (EVar 32) (ELit 272)); (952, EAlu ALU_ADD (EVar 32) (ELit 264)); (872, EAlu ALU_ADD (EVar 32) (ELit 8)); (752, EAlu ALU_ADD (EVar 32) (ELit 40)); (856, EAlu ALU_ADD (EVar 32) (ELit 232)); (896, EAlu ALU_ADD (EVar 32) (ELit 224)); (768, EAlu ALU_ADD (EVar 32) (ELit 216)); (992, EAlu ALU_ADD (EVar 32) (ELit 256)); (928, EAlu ALU_ADD (EVar 32) (ELit 248)); (920, EAlu ALU_ADD (EVar 32) (ELit 240)); (432, EAlu ALU_ADD (EVar 33) (ELit 12480)); (424, EAlu ALU_ADD (EVar 33) (ELit 12016)); (552, EAlu ALU_ADD (EVar 33) (ELit 11552)); (568, EAlu ALU_ADD (EVar 33) (ELit 11520)); (176, EAlu ALU_ADD (EVar 33) (ELit 1936)); (160, EAlu ALU_ADD (EVar 33) (ELit 1472)); (168, EAlu ALU_ADD (EVar 33) (ELit 1008)); (912, EAlu ALU_ADD (EVar 33) (ELit 944)); (80, EAlu ALU_ADD (EVar 33) (ELit 928)); (96, EAlu ALU_ADD (EVar 33) (ELit 896)); (88, EAlu ALU_ADD (EVar 33) (ELit 880)); (264, ELit 16843009); (272, ELit 252645135); (280, ELit 858993459); (288, ELit 1431655765); (368, ELit 18446744072850558157); (120, ELit 65535); (200, ELit 262140); (104, EAlu ALU_ADD (EVar 33) (ELit 848)); (656, EAlu ALU_ADD (EVar 33) (ELit 784)); (616, EAlu ALU_ADD (EVar 33) (ELit 720)); (624, EAlu ALU_ADD (EVar 33) (ELit 656)); (512, EAlu ALU_ADD (EVar 33) (ELit 592)); (464, EAlu ALU_ADD (EVar 33) (ELit 528)); (472, EAlu ALU_ADD (EVar 33) (ELit 464)); (984, EAlu ALU_ADD (EVar 33) (ELit 448)); (408, EAlu ALU_ADD (EVar 33) (ELit 384)); (456, EAlu ALU_ADD (EVar 33) (ELit 320)); (328, EAlu ALU_ADD (EVar 33) (ELit 256)); (416, EAlu ALU_ADD (EVar 33) (ELit 192)); (480, EAlu ALU_ADD (EVar 33) (ELit 128)); (376, EAlu ALU_ADD (EVar 33) (ELit 64)); (192, EAlu ALU_ADD (EVar 33) (ELit 32)); (1016, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (1024, EAlu ALU_ADD (EVar 32) (ELit 72)); (560, EAlu ALU_ADD (EVar 32) (ELit 16)); (840, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 80)) (ELit 3)) (ELit 2147450880)); (880, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (1032, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 248)) (ELit 3)) (ELit 2147450880)); (904, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 256)) (ELit 3)) (ELit 2147450880)); (832, EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)); (744, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (760, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (816, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 40)) (ELit 3)); (824, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (1096, EAlu ALU_ADD (EVar 33) (ELit 10416)); (1088, EAlu ALU_ADD (EVar 33) (ELit 10496)); (1080, EVar 32); (1072, EAlu ALU_ADD (EVar 33) (ELit 10512)); (1064, EAlu ALU_ADD (EVar 33) (ELit 11488))].
  Lemma pm_s8i_ea : forall (w : pmwA H) s LB LBs m mo c msF R F fc (r : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [18; 37; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0f80) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 r ->
    0 < r < 2 ^ 31 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf0f8c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [14; 18; 37; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_S8C -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 25%bv = PropExec.getr R 10%bv -> ffkeepX w [] m m1 -> (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc r  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX10 HR KEA.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KRange (EVar 10) 1 (2 ^ 31)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 10)) with (PropExec.getr R 10%bv). rewrite HX10, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 10) 1 (2 ^ 31)] HK1 30%nat [0xf0f8c] (@nil bool) 41%N
          [14; 18; 37; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTLbAPmS8i_0 (@nil (Z * expr)) RT_PM_S8I_EA_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8I_EA_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147450880 + 2048)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; apply Exists_cons_hd; cbn [fst snd]; lia] |]); apply Forall_nil). } replace (s_pc SSr) with 0xf0f8c in VIS1 by reflexivity. eapply (KEA msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8C HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ exact FK | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 26%bv)]; reflexivity) | (rewrite (HR1 25%bv); reflexivity) ].
  Qed.

#[local] Definition HTLbAPmS8i_1 : list kentry := [KImg 0x17c000 0x185000; KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 848)) (ELit 3)) 2147450880) 1 (ELit 0)].
  Lemma pm_s8i_eb : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [14; 18; 37; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0f8c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 (emp_entry EMP_EXT)) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [14; 15; 18; 37; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_S8M -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf0fcc -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w + 176) -> PropExec.getr R1 11%bv = Z_to_bv 64 (wa_ff w + 10436) -> PropExec.getr R1 13%bv = Z_to_bv 64 (wa_ff w + 848) -> rw_cells asegs m1 (wa_ff w + 848) [C8 (Z_to_bv 64 (wa_ff w + 10436))] -> ffkeepX w [(848, 8)] m m1 -> (forall rr : reg, In rr [23%bv; 24%bv; 25%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 KE.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m HTLbAPmS8i_1).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| idtac].
      { apply kimg_relro. exact (LINV_relro _ (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)). }
      apply Forall_cons; [| apply Forall_nil].
      { eapply pmk_sh_ffu with (1 := OK) (2 := X0) (3 := (env_world_seed H w R (@nil word))); [lia | vm_compute; reflexivity]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          HTLbAPmS8i_1 HK1 40%nat [0xfa914] (@nil bool) 41%N
          [14; 15; 18; 37; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTLbAPmS8i_0 (@nil (Z * expr)) RT_PM_S8I_EB_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8I_EB_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(848, 8)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EVar 33, 848, 856); (EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147450880 + 2048)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; apply Exists_cons_hd; cbn [fst snd]; lia] |]); apply Forall_nil). } assert (CD : rw_cells asegs M1 (wa_ff w + 848) [C8 (Z_to_bv 64 (wa_ff w + 10436))]). { subst M1. eapply (rw_cells_log_nth_ff H w _ m _ 1%nat 848 8 (EAlu ALU_ADD (EVar 33) (ELit 10436)) _ OK (env_world_seed H w R (@nil word))); [exact Hlf1 | reflexivity | vm_compute; reflexivity | lia | cbn [Z.of_nat]; lia | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 848 + i) with (wa_ff w + (848 + i)) by lia; apply FW2; lia | reflexivity | exact Logic.I | cbn [cbytes]; rewrite (ev_add _ 33 (wa_ff w) 10436 E33c) by lia; reflexivity]. } pose proof (pmw_bounds H w OK) as BNDk. replace (s_pc SSr) with (emp_entry EMP_EXT) in VIS1 by reflexivity. eapply (KE msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8M HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CD | exact FK | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[<-|[]]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 25%bv) | rewrite (HR1 26%bv)]; reflexivity) | (rewrite (HR1 _); cbn [sr_get s_regs nth]; first [reflexivity | (eapply ev_add; [reflexivity | lia | lia]) | (cbn [edenot]; ev_xs; first [reflexivity | (rewrite u64_of_Z by lia; reflexivity)])]) ].
  Qed.

  Lemma pm_s8i_h1 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (q : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [14; 15; 18; 37; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0fcc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8M -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 q ->
    16 <= q /\ q + 24 <= 2 ^ 47 ->
    addressable m q 24 ->
    q + 24 <= wa_ff w \/ wa_ff w + 16384 <= q ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf0fec) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [18; 37; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_S8M -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 10%bv = Z_to_bv 64 (q + 20) -> ffkeepX w [] m m1 -> (forall rr : reg, In rr [23%bv; 24%bv; 25%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc q  Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HX10 HQ AD HQF KH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KRange (EVar 10) 16 (2 ^ 47); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 10) (ELit 20)) (ELit 3)) 2147450880) 1 (ELit 0); KDisj (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 10) (ELit 20)) (ELit 3)) 2147450880) (ELit 1) (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 1952)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| idtac].
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ (@nil word))) (EVar 10)) with (PropExec.getr R 10%bv). rewrite HX10, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
      apply Forall_cons; [| idtac].
      { apply (kshadow0 (Eseed R (wenv_vals w ++ (@nil word))) m (EAlu ALU_ADD (EVar 10) (ELit 20)) (q + 20)); [ apply (eq_trans (y := alu64 ALU_ADD (PropExec.getr R 10%bv) (Z_to_bv 64 20))); [reflexivity | rewrite HX10; apply w_add; lia] | lia | eapply (sh0_of_addressable m q 24 (q + 20)); [exact AD | change (8 * (24 / 8)) with 24; lia] ]. }
      apply Forall_cons; [| apply Forall_nil].
      { eapply pmk_sh_fshdisj with (1 := OK) (2 := X0) (3 := (env_world_seed H w R (@nil word))) (x := q + 20); [ apply (eq_trans (y := alu64 ALU_ADD (PropExec.getr R 10%bv) (Z_to_bv 64 20))); [reflexivity | rewrite HX10; apply w_add; lia] | lia | lia | lia ]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 10) 16 (2 ^ 47); KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 10) (ELit 20)) (ELit 3)) 2147450880) 1 (ELit 0); KDisj (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 10) (ELit 20)) (ELit 3)) 2147450880) (ELit 1) (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 1952)] HK1 30%nat [0xf0fec] (@nil bool) 41%N
          [18; 37; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTLbAPmS8i_0 (@nil (Z * expr)) RT_PM_S8I_H1_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8I_H1_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147450880 + 2048)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); destruct Q6 as [Q6|Q6]; (repeat (apply Forall_cons; [cbn [fst snd]; first [left; unfold SHBASE in *; lia | right; left; unfold SHBASE in *; lia | right; right; apply Exists_cons_hd; cbn [fst snd]; lia] |]); apply Forall_nil). } replace (s_pc SSr) with 0xf0fec in VIS1 by reflexivity. eapply (KH msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8M HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact FK | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[<-|[]]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 25%bv) | rewrite (HR1 26%bv)]; reflexivity) | (rewrite (HR1 10%bv); cbn [sr_get s_regs nth]; apply (eq_trans (y := alu64 ALU_ADD (PropExec.getr R 10%bv) (Z_to_bv 64 20))); [reflexivity | rewrite HX10; apply w_add; lia]) ].
  Qed.

  Lemma pm_s8i_h3 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [18; 37; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0ff0) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8M -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf2298) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [18; 37; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_S8D1 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall rr : reg, In rr [23%bv; 24%bv; 25%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> m1 = m -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 KD.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 20%nat [0xf2298] (@nil bool) 41%N
          [18; 37; 61; 62; 63; 65; 67; 86]%nat (@nil Z) (@nil Z) HTLbAPmS8i_0 (@nil (Z * expr)) RT_PM_S8I_H3_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_S8I_H3_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    eapply (KD msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_S8D1 HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[<-|[]]]]]; [rewrite (HR1 23%bv) | rewrite (HR1 24%bv) | rewrite (HR1 25%bv) | rewrite (HR1 26%bv)]; reflexivity) | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity) ].
  Qed.

End S8i.
