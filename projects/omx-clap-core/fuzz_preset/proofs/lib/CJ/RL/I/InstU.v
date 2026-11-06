From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require Import IInst IImgU.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_FmtFp_facts2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_Scan_iface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_fixunstfsi.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_floatscan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_floatsitf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_floatunsitf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_fmodl.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_fmt_fp_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_fpclassifyl.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_getf2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_letf2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_memchr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_memcpy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_pop_arg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_scalbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_scalbnl.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_scanexp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_signbitl.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_strtod.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_subtf3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_trunctfdf2.

#[local] Existing Instance N_img.
#[local] Hint Extern 1 (RStep.CodeAtT _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.CodeAt _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RoB _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelCode _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelSym _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelNear _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (RStep.ZFact _) => IInst.inst : typeclass_instances.

#[export] Instance N_fe_getround_spec_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_subtf3.G_fe_getround.fe_getround_spec_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_subtf3.G_fe_getround.fe_getround_spec_c_ok.
#[export] Instance N_fe_raise_inexact_spec_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_subtf3.G_fe_getround.fe_raise_inexact_spec_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_subtf3.G_fe_getround.fe_raise_inexact_spec_c_ok.
#[export] Instance N_addtf3_spec_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_subtf3.G_addtf3_E.addtf3_spec_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_subtf3.G_addtf3_E.addtf3_spec_c_ok.
#[export] Instance N_subtf3_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_subtf3.subtf3_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_subtf3.subtf3_contract_ok.
#[export] Instance N_letf2_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_letf2.letf2_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_letf2.letf2_contract_ok.
#[export] Instance N_getf2_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_getf2.getf2_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_getf2.getf2_contract_ok.
#[export] Instance N_floatsitf_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_floatsitf.floatsitf_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_floatsitf.floatsitf_contract_ok.
#[export] Instance N_floatunsitf_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_floatunsitf.floatunsitf_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_floatunsitf.floatunsitf_contract_ok.
#[export] Instance N_fixunstfsi_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fixunstfsi.fixunstfsi_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fixunstfsi.fixunstfsi_contract_ok.
#[export] Instance N_fpclassifyl_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fpclassifyl.fpclassifyl_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fpclassifyl.fpclassifyl_contract_ok.
#[export] Instance N_signbitl_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_signbitl.signbitl_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_signbitl.signbitl_contract_ok.
#[export] Instance N_extenddftf2_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_pop_arg.G_extenddftf2.extenddftf2_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_pop_arg.G_extenddftf2.extenddftf2_contract_ok.
#[export] Instance N_frexpl_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_FmtFp_facts2.G_frexpl.frexpl_contract_ok.
#[export] Instance N_multf3_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_multf3.multf3_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_multf3.multf3_contract_ok.
#[export] Instance N_letf2_callv_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.letf2_callv_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.letf2_callv_c_ok.
#[export] Instance N_floatsitf_callv_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.floatsitf_callv_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.floatsitf_callv_c_ok.
#[export] Instance N_floatsitf_callp_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.floatsitf_callp_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.floatsitf_callp_c_ok.
#[export] Instance N_floatunsitf_callv_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.floatunsitf_callv_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.floatunsitf_callv_c_ok.
#[export] Instance N_extenddftf2_callv_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.extenddftf2_callv_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.extenddftf2_callv_c_ok.
#[export] Instance N_multf3_callq_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.multf3_callq_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.multf3_callq_c_ok.
#[export] Instance N_divtf3_callq_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.divtf3_callq_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.divtf3_callq_c_ok.
#[export] Instance N_addtf3_callq_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.addtf3_callq_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.addtf3_callq_c_ok.
#[export] Instance N_subtf3_callq_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.subtf3_callq_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.subtf3_callq_c_ok.
#[export] Instance N_scalbn_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_scalbn.scalbn_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_scalbn.scalbn_contract_ok.
#[export] Instance N_scalbnl_spec_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_scalbnl.scalbnl_spec_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_scalbnl.scalbnl_spec_c_ok.
#[export] Instance N_fabsl_spec_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_scalbnl.fabsl_spec_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_scalbnl.fabsl_spec_c_ok.
#[export] Instance N_copysignl_spec_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_scalbnl.copysignl_spec_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_scalbnl.copysignl_spec_c_ok.
#[export] Instance N_divtf3_spec_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmodl.G_divtf3_main.divtf3_spec_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmodl.G_divtf3_main.divtf3_spec_c_ok.
#[export] Instance N_rfmodl_spec_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmodl.rfmodl_spec_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmodl.rfmodl_spec_c_ok.
#[export] Instance N_memcpy_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_memcpy.memcpy_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_memcpy.memcpy_contract_ok.
#[export] Instance N_memchr_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_memchr.memchr_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_memchr.memchr_contract_ok.
#[export] Instance N_shlim_spec_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_Scan_iface.G_shgetc_A.shlim_spec_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_Scan_iface.G_shgetc_A.shlim_spec_c_ok.
#[export] Instance N_scanexp_rspec_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_scanexp.scanexp_rspec_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_scanexp.scanexp_rspec_c_ok.
#[export] Instance N_trunctfdf2_contract : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_trunctfdf2.trunctfdf2_contract := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_trunctfdf2.trunctfdf2_contract_ok.
#[export] Instance N_L_ENTRY_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_floatscan.L_ENTRY_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_floatscan.L_ENTRY_c_ok.
#[export] Instance N_rstrtod_wide_proof_c : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_strtod.rstrtod_wide_proof_c := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_strtod.rstrtod_wide_proof_c_ok.
