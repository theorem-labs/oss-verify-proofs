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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td LbB_TdKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtorR1 LbB_DPdK LbB_PmXp LbB_PmSL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_WoGen LbB_ExDefs LbB_ExKit LbB_ExT LbB_ExR1 LbB_ExE0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_ExC LbB_ExS LbB_ExL LbB_ExP2 LbB_ExP2c LbB_ExP3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ExStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PqS LbB_NPut LbB_DtS LbB_TablOS LbB_TablLeaves LbB_DPd.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ExA LbB_ExTA.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmGlue LbB_PcOvf.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ExR7.
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
  Hypothesis HPD : pdiag0_stmtA H LINV_P5 ds_repA0.

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Theorem exhausted_okA : exhausted_stmtA11 H LINV_P5.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo
           s LB LF CH lo B shi errv this pcons nwords widx icount inst_offset opcode type
           DP LO' LFL' B1 B2 B3 PFE Ha0 Ha1 Ha2 Ha3 IOR OPR TYR THO THI C8' C56 C72 C80 NWR WIR ICR PCO PCI C32 P16.
    destruct DP as (VIS & FZ & RH & KR & _ & _ & _ & _ & RA & SPB & B64 & SP16 & ST & CE & _ & ER & MI & TP & RAE & LV & AC
                    & RF & _ & S0 & SHI & CHN & _ & CHU & TR & ALe).
    set (e := XEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF CH
                   this pcons nwords widx icount inst_offset opcode type lo B shi).
    assert (HP : xpre H e).
    { unfold xpre, e, xSP, AEX_STACK, EX_FRAMES, EX_COST. cbn.
      refine (conj FZ (conj RH (conj B1 (conj B2 (conj B3 (conj RA (conj SPB (conj B64 (conj SP16 (conj ST (conj CE (conj LO' _)))))))))))).
      refine (conj (ex_intro _ errv ER) (conj MI (conj TP (conj RAE (conj LV (conj AC (conj RF (conj LFL' (conj S0 (conj SHI _)))))))))).
      refine (conj CHN (conj PFE (conj CHU (conj TR (conj ALe (conj IOR (conj OPR (conj TYR _)))))))).
      exact (conj THO (conj C8' (conj C56 (conj C72 (conj C80 (conj NWR (conj WIR (conj ICR (conj PCO (conj C32 P16)))))))))). }
    change this with (x_this e) in Ha0, THI. change pcons with (x_pcons e) in PCI.
    change LF with (x_LF e) in THI, PCI.

    eapply (ahh_evt_then H HH (fun ms => exists ff fp, fresh_frame H (x_LF e) 3 ff fp /\
              LbB_ExC.xcut H e ff fp 0 0 0 0 APDIAG (x_F e) (x_fc e) EX_RT8 EX_SF [] (x_s e) (x_LB e)
                (fun m' => addressable m' (ff + EX_DS_OFF) DS_SIZE) ms)); [exact KR | exact VIS | |].
    { eapply (LbB_ExE0.ex_e0 H HHbp e _ t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP Ha0 Ha1 Ha2 Ha3).
      intros ff fp R2 m2 FF RF2 HRT2 HP2 MI2 _.
      eapply evt_mono; [exact (LbB_ExA.ex_ph1 H HHbp e ff fp 0 0 0 0 HP FF THI PCI R2 m2 [] (x_s e) (x_LB e) RF2 HRT2 HP2 MI2)|].
      intros ms Hms. exists ff, fp. split; [exact FF | exact Hms]. }
    intros msF1 mo1 KR1 MP1 (ff & fp & FF & CUT).
    assert (X0 : LbB_ExS.xsr0 H e ff fp 0 0 0 0 APDIAG EX_RT8 EX_SF (mkCfg msF1 mo1)).
    { exists (x_s e), (x_F e), (x_fc e), []. cbn [cfg_ms cfg_model].
      split; [exact KR1|]. split; [exact MP1|]. split; [exact FZ|]. split; [exact CUT | lia]. }
    clear CUT.
    pose proof (LbB_ExT.ex_vals H e ff fp HP FF) as (V1 & _).
    pose proof (LbB_ExT.ex_wins H e ff fp HP FF) as (W1 & _ & _ & _ & _ & _ & _ & W8).
    eapply (LbB_ExS.x_pdiag H HHbp e ff fp 0 0 0 0 HP FF THI PCI HPD _ EX_RT8 EX_SF EX_PD_RA _ X0);
      [vm_compute; reflexivity | | unfold EX_PD_RA; reflexivity | unfold EX_PD_RA; lia |].
    { intros R HRT. pose proof (fun r e0 Hi => rtbl_In _ R _ r e0 HRT Hi) as Y.
      pose proof (Y (1%bv : reg) (ELit EX_PD_RA) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G1.
      pose proof (Y (2%bv : reg) (EVar 58) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G2.
      pose proof (Y (8%bv : reg) (EVar 33) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G8.
      pose proof (Y (4%bv : reg) (EVar 51) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G4.
      pose proof (Y (10%bv : reg) (EAlu ALU_ADD (EVar 52) (ELit 32)) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G10.
      pose proof (Y (11%bv : reg) (EVar 32) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G11.
      pose proof (Y (12%bv : reg) (ELit (2 ^ 64 - 4)) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G12.
      split; [exact G1|]. split; [exact G2|]. split; [exact (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e))))|].
      split; [exact G4|].
      split.
      { rewrite G10. unfold wenv; cbn [edenot]; unfold HLib.Eseed, reg_ev, LbB_ExT.Wx;
          lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
                Init.Nat.add Nat.sub nth app].
        unfold EX_DS_OFF. rewrite w_add by lia. reflexivity. }
      split; [exact G11|]. rewrite G12. reflexivity. }
    intros cp Xp.
    eapply (LbB_ExS.x_run H HHbp e ff fp 0 0 0 0 _ EX_PD_RA (keptk EX_RT8) EX_SF 0 0 APUT_CSEQ EX_RT7 EX_SF cp Xp).
    { intros R F' fc' m' XSc s' LBc DB RF' HRT HSF HI MI' SS.
      eapply (LbB_ExA.ex_ph2m H HHbp e ff fp 0 0 0 0 HP FF _ R F' fc' m' XSc s' LBc RF' HRT HSF HI MI').
      intros m'' MU WM. pose proof HI as (_ & _ & RHc & _).
      exact (LbB_ExS.xsess_run H HHbp e ff fp HP FF s' LBc 0 DB m' m'' 0 0 EX_SF [] [] [] [] [] eq_refl ltac:(lia) ltac:(lia) RHc SS MU WM). }
    intros cr Xr.

    eapply (LbB_ExP2.seg_A H HHbp e ff fp 0 0 0 0 HP FF HCSEQ _ _ Xr). intros c1 X1.
    eapply (LbB_ExL.x_os H HHbp e ff fp 0 0 0 0 HP FF HOS _ EX_RTa EX_SF 38 32768 0xf8e18 c1 X1);
      [vm_compute; reflexivity | | reflexivity | lia | vm_compute; reflexivity | vm_compute; reflexivity |].
    { intros R HRT. pose proof (fun r e0 Hi => rtbl_In _ R _ r e0 HRT Hi) as Y.
      pose proof (Y (1%bv : reg) (ELit 1019416) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G1.
      pose proof (Y (2%bv : reg) (EVar 58) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G2.
      pose proof (Y (8%bv : reg) (EVar 33) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G8.
      pose proof (Y (4%bv : reg) (EVar 51) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G4.
      pose proof (Y (10%bv : reg) (EVar 36) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G10.
      exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 G10)))). }
    intros P1 L1 c2 CS1 X2.
    eapply (LbB_ExP2.seg_B H HHbp e ff fp P1 L1 0 0 HP FF THI PCI HCSEQ HU64 _ c2 CS1 X2). intros c3 X3.
    eapply (LbB_ExL.x_ts H HHbp e ff fp P1 L1 0 0 HP FF HTS _ EX_RTb EX_SF (38 + L1 + 18 + 24 + 12) 163840 0xf8eb0 c3 X3);
      [vm_compute; reflexivity | | reflexivity | lia | vm_compute; reflexivity | vm_compute; reflexivity |].
    { intros R HRT. pose proof (fun r e0 Hi => rtbl_In _ R _ r e0 HRT Hi) as Y.
      pose proof (Y (1%bv : reg) (ELit 1019568) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G1.
      pose proof (Y (2%bv : reg) (EVar 58) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G2.
      pose proof (Y (8%bv : reg) (EVar 33) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G8.
      pose proof (Y (4%bv : reg) (EVar 51) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G4.
      pose proof (Y (10%bv : reg) (EVar 37) ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)) as G10.
      exact (conj G1 (conj G2 (conj (eq_trans G8 (eq_sym (Z_to_bv_bv_unsigned (x_sp e)))) (conj G4 G10)))). }
    intros P2 L2 c4 CS2 X4.
    pose proof CS1 as (_ & CN1 & _).
    eapply (LbB_ExP2c.seg_C H HHbp e ff fp P1 L1 P2 L2 HP FF THI PCI HCSEQ HU64 HDTOR _ c4 (38 + L1 + 18 + 24 + 12) CS2 ltac:(lia) X4).
    intros c5 X5.

    exact (LbB_ExP3.x_end H HHbp e ff fp P1 L1 P2 L2 HP FF c5 X5).
  Qed.
End Ex.

Theorem exhausted_A {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps_bp H -> RtB_Td.td_law H -> exhausted_stmtA11 H LINV_P5.
Proof.
  intros H HHbp HTD.
  exact (exhausted_okA H HHbp (LbB_PqS.put_cseq_okA H HHbp) (LbB_NPut.put_u64_ok H HHbp HTD) (LbB_DtS.dtor_okA H HHbp)
           (LbB_TablOS.opcode_string_okA H HHbp) (tla_operand_type_str LbB_TablLeaves.tabl_leaves_okA)
           (LbB_DPd.pdiag0_okA H HHbp)).
Qed.
