(* The slot LLVMFuzzerTestOneInput, plain image, op_write arm, segment B1: text_of's return (0x13fb8, cut
   c1_13fb8) through kernel, the inlined model_begin and model_write to model_write's return (0x13ff8,
   cut c1_13ff8), with the segment footprint. The three pieces: LC1B1K (kernel), LC1B1G (model_begin and
   g_nl.n_sent = 0, to model_write's entry), LC1B1W (model_write). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call LC1B1Lib
  LC1B1K LC1B1G LC1B1W.
Local Open Scope Z_scope.

Section B1.
Hypothesis KERNEL_OK : kernel_contract.
Hypothesis MODEL_WRITE_OK : model_write_contract.

Theorem c1_seg_B1 : forall (E : lenv) (i : Z) (gp : word) (own : Z) (ms : machine_state),
  lenv_ok E -> c1_13fb8 E i gp own ms ->
  evt rsegs (eqv_cl (fun ms' => c1_13ff8 E i gp own ms' /\ seg_fp (e_S E) (c1_hp E) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp own ms HE H.
  eapply evt_eqv_bind; [exact (c1b1_seg_K KERNEL_OK E i gp own ms HE H)|].
  intros c Hc.
  eapply evt_cut; [exact (c1b1_seg_G E i gp own (ms_mem ms) c HE Hc)|].
  intros c' Hc'.
  exact (c1b1_seg_W MODEL_WRITE_OK E i gp own (ms_mem ms) c' HE Hc').
Qed.

End B1.
