From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.I Require Import IInst IImgU InstFmtU.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require G_memset G_memcpy G_memchr G_strnlen G_pop_arg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require G_fwritex G_pad.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require G_sn_write G_fwritex_w G_printf_core.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require G_vfprintf_snf G_towrite.
Open Scope Z_scope.

(** The printf route's callee statements closed on segconf's ubsan image (InstFmtU.N_img_fmt), one named theorem
    per function (the unit-level snprintf_holds, vsnprintf_holds and snprintf_m_holds are in Prog/snprintf.v,
    Prog/vsnprintf.v and Prog/snprintf_m.v). Each is DIS's relocatable statement (CJ/RL/G, CJ/RL/GX) with its
    code facts discharged on this image by IInst.inst, as InstFmtU.v does for the instances it exports. *)

#[local] Existing Instance N_img_fmt.
#[local] Hint Extern 1 (RStep.CodeAtT _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.CodeAt _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RoB _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelCode _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelSym _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelNear _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (RStep.ZFact _) => IInst.inst : typeclass_instances.
#[local] Instance N_fwritex_call : G_fwritex.fwritex_call_c := G_fwritex.fwritex_call_c_ok.

(** sn_write (f->write of vsnprintf's FILE) *)
Lemma sn_write_holds : G_sn_write.sn_write_contract.
Proof. exact N_sn_write_contract. Qed.
(** vfprintf on vsnprintf's string FILE *)
Lemma vfprintf_holds : G_vfprintf_snf.vfprintf_snf_stmt.
Proof. exact N_vfprintf. Qed.
(** printf_core, both passes *)
Lemma printf_core_holds : G_printf_core.printf_core_proof_c.
Proof. exact N_printf_core_proof_c. Qed.
Lemma printf_core1_holds : G_printf_core.printf_core1_proof_c.
Proof. exact N_printf_core1_proof_c. Qed.
(** pop_arg *)
Lemma pop_arg_holds : G_pop_arg.pop_arg_contract.
Proof. exact N_pop_arg_contract. Qed.
(** pad *)
Lemma pad_holds : G_pad.pad_contract.
Proof. exact G_pad.pad_contract_ok. Qed.
(** __fwritex: the plain contract and the f->write (sn_write) variant *)
Lemma fwritex_holds : G_fwritex.fwritex_contract.
Proof. exact N_fwritex_contract. Qed.
Lemma fwritex_w_holds : G_fwritex_w.fwritex_w_stmt.
Proof. exact N_fwritex_w_stmt. Qed.
(** __towrite *)
Lemma towrite_holds : G_towrite.towrite_x_stmt.
Proof. exact G_towrite.towrite_x_proof. Qed.
(** strnlen *)
Lemma strnlen_holds : G_strnlen.strnlen_contract.
Proof. exact N_strnlen_contract. Qed.
