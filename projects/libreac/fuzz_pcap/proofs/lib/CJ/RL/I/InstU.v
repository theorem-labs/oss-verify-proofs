From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.I Require Import IInst IImgU.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.G Require G_memset G_memcpy G_memchr G_strnlen G_pop_arg G_fwritex.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.GX Require G_pop_arg_x G_printf_core G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.GX Require G_printf_errsink.
Open Scope Z_scope.

Module PI := OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.

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

Lemma N_printf_core_err : forall Fp fl0 j1 j2 j3 lbfw B m0 RC RCS RE RES,
  PI.printf_core_stmt Fp B PI.SNF_CAP RC RCS RE RES (G_printf_errsink.SINK_err Fp fl0 j1 j2 j3 lbfw B m0)
    G_printf_errsink.TOPOK_err (PI.OUT_snf PI.SNF_CAP) PI.OUTFP_snf.
Proof.
  intros Fp fl0 j1 j2 j3 lbfw B m0 RC RCS RE RES.
  exact (N_printf_core_proof_c (list Z) Fp B PI.SNF_CAP RC RCS RE RES _ G_printf_errsink.TOPOK_err
           (PI.OUT_snf PI.SNF_CAP) PI.OUTFP_snf
           (G_printf_errsink.err_sink_frame Fp fl0 j1 j2 j3 lbfw B m0 RC RCS RE RES)
           (G_printf_errsink.err_sink_flags Fp fl0 j1 j2 j3 lbfw B m0)
           G_printf_errsink.err_topok
           (G_printf_errsink.err_out Fp fl0 j1 j2 j3 lbfw B m0 RC RCS RE RES)).
Qed.

Lemma N_sym_printf_core : sym 0x18704 = (symaddr Symbols.Ubsan.s_printf_core).
Proof. vm_compute. reflexivity. Qed.
Lemma N_sym_got : sym 0x22e18 = (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z).
Proof. vm_compute. reflexivity. Qed.
Lemma N_sym_guard : sym 0x34288 = (symaddr Symbols.Ubsan.s___stack_chk_guard).
Proof. vm_compute. reflexivity. Qed.
Lemma N_sym_top : sym 0x35000 = (symaddr ImgPages.Ubsan.top).
Proof. vm_compute. reflexivity. Qed.
