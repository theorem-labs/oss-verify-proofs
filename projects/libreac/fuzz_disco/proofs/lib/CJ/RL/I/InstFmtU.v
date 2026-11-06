From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.I Require Import IInst IImgU.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require G_memset G_memcpy G_memchr G_strnlen G_pop_arg G_fwritex.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_sn_write G_fwritex_w G_pop_arg_x G_printf_core.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_vsnprintf G_snprintf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require snprintf_c.
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

(* The code facts of the sn_write and vsnprintf program trees (G_sn_write, G_vsnprintf) as named lemmas, each a
   vm_compute check of the tree's instruction words against this image. N_sn_write_contract and N_vsnprintf below use
   them, so one lemma that you can cite checks each of these two trees. The hints above find the code facts of the
   other trees. *)
Lemma fmt_CODE_sn_write :
  RStep.CodeAtT (@img_segs N_img_fmt) (@sym N_img_fmt 0x7f000300) (G_sn_write.PROGAT_CODE_sn_write N_img_fmt).
Proof. IInst.inst. Qed.
Lemma fmt_CODE_vsnprintf :
  RStep.CodeAtT (@img_segs N_img_fmt) (@sym N_img_fmt 0x7f000200) (G_vsnprintf.PROGAT_CODE_vsnprintf N_img_fmt).
Proof. IInst.inst. Qed.

#[export] Instance N_memset_contract : G_memset.memset_contract := G_memset.memset_contract_ok.
#[export] Instance N_memcpy_contract : G_memcpy.memcpy_contract := G_memcpy.memcpy_contract_ok.
#[export] Instance N_memchr_contract : G_memchr.memchr_contract := G_memchr.memchr_contract_ok.
#[export] Instance N_strnlen_contract : G_strnlen.strnlen_contract := G_strnlen.strnlen_contract_ok.
#[export] Instance N_extenddftf2_contract : G_pop_arg.G_extenddftf2.extenddftf2_contract :=
  G_pop_arg.G_extenddftf2.extenddftf2_contract_ok.
#[export] Instance N_pop_arg_contract : G_pop_arg.pop_arg_contract := G_pop_arg.pop_arg_contract_ok.
#[export] Instance N_fwritex_contract : G_fwritex.fwritex_contract := G_fwritex.fwritex_contract_ok.
#[export] Instance N_sn_write_contract : G_sn_write.sn_write_contract :=
  G_sn_write.sn_write_contract_ok (CODE_sn_write := fmt_CODE_sn_write).
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
Proof. exact (G_vsnprintf.vsnprintf_x_proof (CODE_vsnprintf := fmt_CODE_vsnprintf) N_memset_contract N_vfprintf). Qed.

Lemma N_snprintf : G_snprintf.snprintf_x_stmt.
Proof. exact (G_snprintf.snprintf_x_proof N_vsnprintf). Qed.
