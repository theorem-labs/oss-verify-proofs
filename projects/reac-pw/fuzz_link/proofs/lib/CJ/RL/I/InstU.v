(* reac-pw/fuzz_link: the generic CJ instances on link's ubsan image (IImgU), in the form of libreac/fuzz_pcap's
   lib/CJ/RL/I/InstU.v (ossv/recipes 4b6f0df50aa). pcap's N_printf_core_err is not carried: it instantiates
   G_printf_errsink, pcap's stderr FILE, which link does not use. N_towrite is added (G_towrite, the generic
   __towrite walk). The image module is the ubsan one (lib/U/Img0.v). Each instance discharges its code and
   address obligations by computation on link's image (IInst.inst: code_checkb_t_ok and vm_compute). The N_sym_*
   values are link's ubsan addresses: printf_core, the .got slot of __stack_chk_guard, __stack_chk_guard, and the
   page-rounded end of the writable segments. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require Import IInst IImgU.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require G_memset G_memcpy G_memchr G_strnlen G_pop_arg G_fwritex.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_pop_arg_x G_printf_core G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_towrite.
Open Scope Z_scope.

Module PI := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.

#[local] Existing Instance N_img.
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
#[export] Instance N_pop_arg_x_contract : G_pop_arg_x.pop_arg_x_contract := G_pop_arg_x.pop_arg_x_contract_ok.
#[export] Instance N_printf_core_proof_c : G_printf_core.printf_core_proof_c := G_printf_core.printf_core_proof_c_ok.
#[export] Instance N_printf_core1_proof_c : G_printf_core.printf_core1_proof_c := G_printf_core.printf_core1_proof_c_ok.

Lemma N_printf_core1 : PI.printf_core1_stmt.
Proof. exact N_printf_core1_proof_c. Qed.

Lemma N_towrite : G_towrite.towrite_x_stmt.
Proof. exact G_towrite.towrite_x_proof. Qed.

Lemma N_sym_printf_core : sym 0x18704 = 0x1a9d8.
Proof. vm_compute. reflexivity. Qed.
Lemma N_sym_got : sym 0x22e18 = 0x21110.
Proof. vm_compute. reflexivity. Qed.
Lemma N_sym_guard : sym 0x34288 = 0x960b8.
Proof. vm_compute. reflexivity. Qed.
Lemma N_sym_top : sym 0x35000 = 0x97000.
Proof. vm_compute. reflexivity. Qed.
