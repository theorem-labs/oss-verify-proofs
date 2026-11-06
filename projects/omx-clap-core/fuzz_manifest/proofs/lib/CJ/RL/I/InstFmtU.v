From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.I Require Import IInst IImgU.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.G Require G_memset G_memcpy G_memchr G_strnlen G_pop_arg G_fwritex.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.GX Require G_sn_write G_fwritex_w G_pop_arg_x G_printf_core.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.GX Require G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.GX Require G_vsnprintf G_snprintf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require snprintf_c.
Open Scope Z_scope.

Definition N_img_fmt : RImg :=
  {| img_segs := rsegs; sym := fun k => if Z.eqb k 0x35000 then snprintf_c.IMG_END else N_sym k |}.

#[local] Existing Instance N_img_fmt.
#[local] Hint Extern 1 (RStep.CodeAtT _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.CodeAt _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RoB _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelCode _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelSym _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelNear _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (RStep.ZFact _) => IInst.inst : typeclass_instances.

#[export] Instance N_memset_contract : G_memset.memset_contract := G_memset.memset_contract_ok.
#[export] Instance N_memcpy_contract : G_memcpy.memcpy_contract := G_memcpy.memcpy_contract_ok.
#[export] Instance N_memchr_contract : G_memchr.memchr_contract := G_memchr.memchr_contract_ok.
#[export] Instance N_strnlen_contract : G_strnlen.strnlen_contract := G_strnlen.strnlen_contract_ok.
#[export] Instance N_extenddftf2_contract : G_pop_arg.G_extenddftf2.extenddftf2_contract :=
  G_pop_arg.G_extenddftf2.extenddftf2_contract_ok.
#[export] Instance N_pop_arg_contract : G_pop_arg.pop_arg_contract := G_pop_arg.pop_arg_contract_ok.
#[export] Instance N_fwritex_contract : G_fwritex.fwritex_contract := G_fwritex.fwritex_contract_ok.
#[export] Instance N_sn_write_contract : G_sn_write.sn_write_contract := G_sn_write.sn_write_contract_ok.
#[export] Instance N_fwritex_w_stmt : G_fwritex_w.fwritex_w_stmt := G_fwritex_w.fwritex_w_ok.
#[export] Instance N_pop_arg_x_contract : G_pop_arg_x.pop_arg_x_contract := G_pop_arg_x.pop_arg_x_contract_ok.
#[export] Instance N_printf_core_proof_c : G_printf_core.printf_core_proof_c := G_printf_core.printf_core_proof_c_ok.
#[export] Instance N_printf_core1_proof_c : G_printf_core.printf_core1_proof_c := G_printf_core.printf_core1_proof_c_ok.

Lemma N_vfprintf : G_vfprintf_snf.vfprintf_snf_stmt.
Proof.
  refine (G_vfprintf_snf.vfprintf_snf_proof N_printf_core_proof_c N_printf_core1_proof_c _ _ _ _); intros.
  - apply G_printf_snfsink.snf_sink_frame.
  - apply G_printf_snfsink.snf_sink_flags.
  - apply G_printf_snfsink.snf_out.
  - apply G_printf_snfsink.snf_flush_ok.
Qed.

Lemma N_vsnprintf : G_vsnprintf.vsnprintf_x_stmt.
Proof. exact (G_vsnprintf.vsnprintf_x_proof N_memset_contract N_vfprintf). Qed.

Lemma N_snprintf : G_snprintf.snprintf_x_stmt.
Proof. exact (G_snprintf.snprintf_x_proof N_vsnprintf). Qed.
