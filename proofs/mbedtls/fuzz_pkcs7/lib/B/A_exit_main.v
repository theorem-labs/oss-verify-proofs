(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim AgentLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow Restrict RestrictLib NodesA SymDriveA RestrictRun.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_stdio_defs A_exit_defs A_exit_lib A_unreg_globals A_exit A_code_dd000_de000 .
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_exit_main () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.B.A_exit_defs.exit_commonA"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.regupd"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.B.A_exit_defs.exit_preA"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "stdpp.bitvector.definitions.bv_and"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"].


Lemma exit_commonA_set_ra : ltac2:(CDefT.buildp (gd_tbl_A_exit_main ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Psu,$3.Pcode,(1.&40.)Ptid,$3.Pwp0,(1.&40.)Prp0,(1.&40.)Pwp2,(1.&40.)Prp2,(1.&40.)Pv,(1.&40.)P,(4.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(4.(5.R;.(6.&5.+1.$7.)R2.)R:.R9.R8.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros regs mem su code tid wp0 rp0 wp2 rp2 v EC. destruct EC.
  split; try assumption; rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; cbn in E; discriminate); assumption.
Qed.

Lemma exit_preA_set_ra : ltac2:(CDefT.buildp (gd_tbl_A_exit_main ()) "Psu,$3.Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Pmo,$8.Pcode,(1.&40.)Ppending,(9.(1.&8.))Pv,(1.&40.)P,(:.R7.R6.R5.R4.R3.R2.)(:.R8.(5.R7.(6.&5.+1.$7.)R2.)R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros su regs mem mo code pending v dd_H; ddestruct dd_H as (tid & wp0 & rp0 & wp2 & rp2 & EC & REST)).
  dexists tid, wp0, rp0, wp2, rp2. split; [apply exit_commonA_set_ra; exact EC | exact REST].
Qed.

Lemma E_dd6ec : is_ecall W_dd6ec = false.
Proof. reflexivity. Qed.

Section Thm.
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable K : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000%Z.
  Hypothesis GSB : al_gsb AL = 0x1099f8%Z.
  Hypothesis IMGCS : img_cs AL CS.
  Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_exit_main ()) "Pmo,$8.Pacc,(9.(;.(1.&40.)$<.))P,A1.VK,R2.P,(=.VAL,VCS,R2.)(>.$8.Lmo',$8.(?.(10.(2.$8.)(11.R5.R4.)(12.$8.R1.))(?.A1.VK,R1.(13.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_exit_main ()) "Pmo,$8.Pmo',$8.P,A1.VK,R2.P,(10.$14.(15.R2.)(15.R3.))P,(10.(9.(;.(1.&40.)(1.&40.)))(16.R3.)(16.R4.))P,(10.(9.(1.&40.))(17.R4.)(17.R5.))P,(10.(2.(1.&40.))(18.R5.)(18.R6.))A1.VK,R6.")
(* [comment removed for export] *).
  Variable su : Z.
  Hypothesis SUlo : (4294967296 + 320 <= su)%Z.
  Hypothesis SUhi : (su <= 2^47)%Z.
  Hypothesis FRCS : forall z, (su - 320 <= z < su)%Z -> CS z.

  (* [comment removed for export] *)
  #[using="AL CS IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly SUlo SUhi FRCS"] Theorem main_ret_exitA : ltac2:(CDefT.buildp (gd_tbl_A_exit_main ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))Pmo,$8.Pcode,(1.&40.)Ppending,(9.(1.&8.))P,(:.Vsu,R5.R4.R3.R2.R1.)P,A1.VK,R4.(19.$1:.(1;.(1<.$1=.R7.(1>.&40.+>0::8.)R6.(1?.$1:.))R5.)(20.(21.+1.R3.)(22.(23.&40.R4.(1>.&40.+??.))(24.R5.))))")
(* [comment removed for export] *).
  Proof.
    intros regs mem mo code pending PRE HK.
    replace (Z_to_bv 64 0x0e0aa8) with (0x0e0aa8 : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (RUN : msteps RSEGS (mkst regs (0x0e0aa8 : word) (restrict (Dimg [(su - 320, su)%Z]) mem) (seg_rom RSEGS))
                               (mkst (regupd regs 1 (v_addi (0x0e0aa8 : word) 4)) (Z_to_bv 64 0x0e11a8)
                                     (restrict (Dimg [(su - 320, su)%Z]) mem) (seg_rom RSEGS))).
    { eapply mst_step; [reflexivity | | apply mst_refl].
      rewrite (step_jal_link RSEGS regs (0x0e0aa8 : word) _ (seg_rom RSEGS) W_dd6ec 1 1792 F_dd6ec E_dd6ec D_dd6ec).
      cbn [bv_eqb]. reflexivity. }
    eapply (rrunT AL CS K IMG K_halted K_mat su SUlo FRCS); [exact HK | exact RUN | intros; reflexivity |].
    intros mo' HK' MM'.
    eapply srzJ_conseq.
    - first [ apply (ref_exitA AL CS K IMG ALWF CSOK ASB GSB IMGCS K_halted K_mat K_vmonly su SUlo SUhi FRCS) | apply (ref_exitA AL CS K IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly su SUlo SUhi FRCS) ].
      + apply exit_preA_set_ra. revert PRE. unfold exit_preA. destruct MM' as (Efd & _). unfold m_fds. rewrite Efd. intros PRE; exact PRE.
      + exact HK'.
    - rewrite (mo_mat_fs _ _ MM'). apply t_eq_refl.
  Qed.
End Thm.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
