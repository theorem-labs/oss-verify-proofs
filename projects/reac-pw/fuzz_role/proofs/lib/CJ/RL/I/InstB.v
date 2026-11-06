(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/CJ/RL/I/InstP.v at da0a37fe570; the instances are taken at the symbol map of the ASan image A (IImgA). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/CJ/RL/I/InstA.v at b2957340e99a; the module paths name reac-pw/fuzz_rate instead of reac-pw/fuzz_role, and the instances are taken at reac-pw/fuzz_rate's image-A symbol map (IImgA). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/CJ/RL/I/InstA.v at fbf0205dfe3d; the instances are taken at reac-pw/fuzz_rate's image-B symbol map (IImgB). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/CJ/RL/I/InstB.v at 078e902e9693; the module paths name reac-pw/fuzz_role, and the instances are taken at reac-pw/fuzz_role's image-B symbol map (IImgB). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.I Require Import IInst IImgB.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G Require G_getf2.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G Require G_letf2.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G Require G_subtf3.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G Require C_extendsftf2 G_extendsftf2.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G Require C_floatditf G_floatditf.

#[local] Existing Instance N_img.
#[local] Hint Extern 1 (RStep.CodeAtT _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.CodeAt _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RoB _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelCode _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelSym _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelNear _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (RStep.ZFact _) => IInst.inst : typeclass_instances.

#[export] Instance N_fe_getround_spec_c : OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_subtf3.G_fe_getround.fe_getround_spec_c := OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_subtf3.G_fe_getround.fe_getround_spec_c_ok.
#[export] Instance N_fe_raise_inexact_spec_c : OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_subtf3.G_fe_getround.fe_raise_inexact_spec_c := OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_subtf3.G_fe_getround.fe_raise_inexact_spec_c_ok.
#[export] Instance N_addtf3_spec_c : OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_subtf3.G_addtf3_E.addtf3_spec_c := OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_subtf3.G_addtf3_E.addtf3_spec_c_ok.
#[export] Instance N_subtf3_contract : OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_subtf3.subtf3_contract := OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_subtf3.subtf3_contract_ok.
#[export] Instance N_letf2_contract : OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_letf2.letf2_contract := OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_letf2.letf2_contract_ok.
#[export] Instance N_getf2_contract : OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_getf2.getf2_contract := OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_getf2.getf2_contract_ok.
#[export] Instance N_extendsftf2_contract : OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.C_extendsftf2.extendsftf2_contract := OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_extendsftf2.extendsftf2_contract_ok.
#[export] Instance N_floatditf_contract : OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.C_floatditf.floatditf_contract := OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.G.G_floatditf.floatditf_contract_ok.
