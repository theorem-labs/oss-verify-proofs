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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HArr HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface RtA_IMemset.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FakeStackRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtA_Td LbA_TdKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_Own.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_DiagStmt LbA_DStat LbA_DRep LbA_DKit LbA_DKitN.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_DCtorK LbA_DCtorR1 LbA_DPdK LbA_PmXp LbA_PmSL.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_TablStmt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PrsStmt LbA_WoGen LbA_ExDefs LbA_ExKit LbA_ExT LbA_ExR1 LbA_ExE0.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_ExC LbA_ExS LbA_ExL LbA_ExP2 LbA_ExP2c LbA_ExP3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_ExStmt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_PqS LbA_NPut LbA_DtS LbA_TablOS LbA_TablLeaves.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_ExA LbA_ExTA.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_PmGlue LbA_PcOvf.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_ExR7.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Ex.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA0.
  Hypothesis HU64 : put_u64_stmtA H LINV_P5 ds_repA0.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA0.
  Hypothesis HOS : opcode_string_stmtA H.
  Hypothesis HTS : operand_type_str_stmtA.

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Theorem exhausted_okA : exhausted_stmtA11 H LINV_P5.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo
           s LB LF CH lo B shi errv this pcons nwords widx icount inst_offset opcode type
           DP LO' LFL' B1 B2 B3 PFE Ha0 Ha1 Ha2 Ha3 IOR OPR TYR THO THI C8' C56 C72 C80 NWR WIR ICR PCO PCI C32.
    destruct DP as (VIS & FZ & RH & KR & _ & _ & _ & _ & RA & SPB & B64 & SP16 & ST & CE & _ & ER & MI & TP & RAE & LV & AC
                    & RF & _ & S0 & SHI & CHN & _ & CHU & TR & ALe).
    set (e := XEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF CH
                   this pcons nwords widx icount inst_offset opcode type lo B shi).
    assert (HP : xpre H e).
    { unfold xpre, e, xSP, AEX_STACK, EX_FRAMES, EX_COST. cbn.
      refine (conj FZ (conj RH (conj B1 (conj B2 (conj B3 (conj RA (conj SPB (conj B64 (conj SP16 (conj ST (conj CE (conj LO' _)))))))))))).
      refine (conj (ex_intro _ errv ER) (conj MI (conj TP (conj RAE (conj LV (conj AC (conj RF (conj LFL' (conj S0 (conj SHI _)))))))))).
      refine (conj CHN (conj PFE (conj CHU (conj TR (conj ALe (conj IOR (conj OPR (conj TYR _)))))))).
      exact (conj THO (conj C8' (conj C56 (conj C72 (conj C80 (conj NWR (conj WIR (conj ICR (conj PCO C32))))))))). }
    change this with (x_this e) in Ha0, THI. change pcons with (x_pcons e) in PCI.
    change LF with (x_LF e) in THI, PCI.

    eapply (ahh_evt_then H HH (fun ms => exists ff fp, fresh_frame H (x_LF e) 4 ff fp /\
              LbA_ExC.xcut H e ff fp 0 0 0 0 APUT_CSEQ (x_F e) (x_fc e) EX_RT7 EX_SF [] (x_s e) (x_LB e)
                (fun m' => ds_repA0 (x_LB e) m' (ff + EX_DS_OFF) (-4) 0 []) ms)); [exact KR | exact VIS | |].
    { eapply (LbA_ExE0.ex_e0 H HHbp e _ t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP Ha0 Ha1 Ha2 Ha3).
      intros ff fp R2 m2 FF RF2 HRT2 HP2 MI2 _.
      eapply evt_mono; [exact (LbA_ExA.ex_ph1 H HHbp e ff fp 0 0 0 0 HP FF THI PCI R2 m2 [] (x_s e) (x_LB e) RF2 HRT2 HP2 MI2)|].
      intros ms Hms. exists ff, fp. split; [exact FF | exact Hms]. }
    intros msF1 mo1 KR1 MP1 (ff & fp & FF & CUT).
    assert (X0 : LbA_ExS.xsr H e ff fp 0 0 0 0 APUT_CSEQ EX_RT7 EX_SF 0 0 (mkCfg msF1 mo1)).
    { exists (x_s e), (x_F e), (x_fc e), [], (x_LB e), []. cbn [cfg_ms cfg_model].
      split; [exact KR1|]. split; [exact MP1|]. split; [exact FZ|]. split; [| lia].
      destruct CUT as (R & m1 & E1 & RF1 & HRT1 & HSF1 & HI1 & MI1 & REP1).
      exists R, m1. split; [exact E1|]. split; [exact RF1|]. split; [exact HRT1|]. split; [exact HSF1|]. split; [exact HI1|]. split; [exact MI1|].
      split; [exact REP1|]. split; [apply Permutation_refl | apply lb_own_nil]. }
    clear CUT.

    eapply (LbA_ExP2.seg_A H HHbp e ff fp 0 0 0 0 HP FF HCSEQ _ _ X0). intros c1 X1.
    eapply (LbA_ExL.x_os H HHbp e ff fp 0 0 0 0 HP FF HOS _ EX_RTa EX_SF 38 32768 0xf8460 c1 X1);
      [vm_compute; reflexivity | | reflexivity | lia | vm_compute; reflexivity | vm_compute; reflexivity |].
    { intros R HRT. pose proof (fun r e0 Hi => rtbl_In _ R _ r e0 HRT Hi) as Y.
      pose proof (Y (1%bv : reg) (ELit 1016928) ltac:(apply LbA_DCtorK.inb_In'; vm_compute; reflexivity)) as G1.
      pose proof (Y (2%bv : reg) (EVar 58) ltac:(apply LbA_DCtorK.inb_In'; vm_compute; reflexivity)) as G2.
      pose proof (Y (8%bv : reg) (EVar 33) ltac:(apply LbA_DCtorK.inb_In'; vm_compute; reflexivity)) as G8.
      pose proof (Y (4%bv : reg) (EVar 51) ltac:(apply LbA_DCtorK.inb_In'; vm_compute; reflexivity)) as G4.
      pose proof (Y (10%bv : reg) (EVar 36) ltac:(apply LbA_DCtorK.inb_In'; vm_compute; reflexivity)) as G10.
      exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 G10)))). }
    intros P1 L1 c2 CS1 X2.
    eapply (LbA_ExP2.seg_B H HHbp e ff fp P1 L1 0 0 HP FF THI PCI HCSEQ HU64 _ c2 CS1 X2). intros c3 X3.
    eapply (LbA_ExL.x_ts H HHbp e ff fp P1 L1 0 0 HP FF HTS _ EX_RTb EX_SF (38 + L1 + 18 + 24 + 12) 163840 0xf84fc c3 X3);
      [vm_compute; reflexivity | | reflexivity | lia | vm_compute; reflexivity | vm_compute; reflexivity |].
    { intros R HRT. pose proof (fun r e0 Hi => rtbl_In _ R _ r e0 HRT Hi) as Y.
      pose proof (Y (1%bv : reg) (ELit 1017084) ltac:(apply LbA_DCtorK.inb_In'; vm_compute; reflexivity)) as G1.
      pose proof (Y (2%bv : reg) (EVar 58) ltac:(apply LbA_DCtorK.inb_In'; vm_compute; reflexivity)) as G2.
      pose proof (Y (8%bv : reg) (EVar 33) ltac:(apply LbA_DCtorK.inb_In'; vm_compute; reflexivity)) as G8.
      pose proof (Y (4%bv : reg) (EVar 51) ltac:(apply LbA_DCtorK.inb_In'; vm_compute; reflexivity)) as G4.
      pose proof (Y (10%bv : reg) (EVar 37) ltac:(apply LbA_DCtorK.inb_In'; vm_compute; reflexivity)) as G10.
      exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 G10)))). }
    intros P2 L2 c4 CS2 X4.
    pose proof CS1 as (_ & CN1 & _).
    eapply (LbA_ExP2c.seg_C H HHbp e ff fp P1 L1 P2 L2 HP FF THI PCI HCSEQ HU64 HDTOR _ c4 (38 + L1 + 18 + 24 + 12) CS2 ltac:(lia) X4).
    intros c5 X5.

    exact (LbA_ExP3.x_end H HHbp e ff fp P1 L1 P2 L2 HP FF c5 X5).
  Qed.
End Ex.

Theorem exhausted_A {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps_bp H -> RtA_Td.td_law H -> exhausted_stmtA11 H LINV_P5.
Proof.
  intros H HHbp HTD.
  exact (exhausted_okA H HHbp (LbA_PqS.put_cseq_okA H HHbp) (LbA_NPut.put_u64_ok H HHbp HTD) (LbA_DtS.dtor_okA H HHbp)
           (LbA_TablOS.opcode_string_okA H HHbp) (tla_operand_type_str LbA_TablLeaves.tabl_leaves_okA)).
Qed.
