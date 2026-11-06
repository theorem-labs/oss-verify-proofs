From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require Import IInst IImgP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require InstP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require mf_sink_c mf_sink mf_bridge vfprintf_mf vfprintf_b vfprintf_c.
Open Scope Z_scope.

#[local] Existing Instance N_img.
#[local] Existing Instance InstP.N_fwritex_contract.
#[local] Hint Extern 1 (RStep.CodeAtT _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.CodeAt _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RoB _ _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelCode _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelSym _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (RStep.RelNear _ _) => IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (RStep.ZFact _) => IInst.inst : typeclass_instances.

Lemma printf_core_heap_all_ok : @mf_sink_c.printf_core_heap_all N_img.
Proof. exact InstP.N_printf_core_proof_c. Qed.

Lemma N_vfprintf_mf : @mf_sink_c.vfprintf_mf_stmt N_img.
Proof.
  refine (vfprintf_mf.vfprintf_mf_proof (IMG := N_img) printf_core_heap_all_ok InstP.N_printf_core1 _ _ _).
  - intros. apply mf_sink.mf_sink_frame.
  - intros. apply mf_sink.mf_sink_flags.
  - intros. apply mf_sink.mf_out.
Qed.

Theorem vfprintf_proof : vfprintf_c.vfprintf_contract.
Proof. exact (vfprintf_b.vfprintf_of_mf mf_bridge.mf_cells_of_k mf_bridge.mf_post_of_cells N_vfprintf_mf). Qed.
