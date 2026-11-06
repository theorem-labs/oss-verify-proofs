(* The slot LLVMFuzzerTestOneInput, plain image, op_write arm: segment B whole, from text_of's return
   (0x13fb8, cut c1_13fb8) to the call of free(own) (0x1405c, cut c1_173d4), as B1 (kernel, model_begin,
   model_write: LC1B1) then B2 (the library write, the checks, the refusal test: LC1B2), joined at
   model_write's return 0x13ff8 (c1_13ff8). The segment footprint of B is the two footprints chained. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import kernel_c model_write_c
  reac_link_alias_write_c check_socket_c strlen_c index_of_c check_refused_c check_write_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call LC1B1 LC1B2.
Local Open Scope Z_scope.

Section B.
Hypothesis KERNEL_OK : kernel_contract.
Hypothesis MODEL_WRITE_OK : model_write_contract.
Hypothesis ALIAS_WRITE_OK : reac_link_alias_write_contract.
Hypothesis CHECK_SOCKET_OK : check_socket_contract.
Hypothesis STRLEN_OK : strlen_contract.
Hypothesis INDEX_OF_OK : index_of_contract_P.
Hypothesis CHECK_REFUSED_OK : check_refused_contract.
Hypothesis CHECK_WRITE_OK : check_write_contract.
Hypothesis CHECK_REQUESTS_OK : check_requests_contract.

Theorem c1_seg_B : forall (E : lenv) (i : Z) (gp : word) (own : Z) (ms : machine_state),
  lenv_ok E -> c1_13fb8 E i gp own ms ->
  evt rsegs (eqv_cl (fun ms' => c1_173d4 E i gp own ms' /\ seg_fp (e_S E) (c1_hp E) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp own ms HE H.
  eapply evt_eqv_bind; [exact (c1_seg_B1 KERNEL_OK MODEL_WRITE_OK E i gp own ms HE H)|].
  intros c [Hc F1].
  eapply evt_mono.
  { exact (c1_seg_B2 ALIAS_WRITE_OK CHECK_SOCKET_OK STRLEN_OK INDEX_OF_OK CHECK_REFUSED_OK CHECK_WRITE_OK
             CHECK_REQUESTS_OK E i gp own c HE Hc). }
  intros ms'. apply eqv_cl_mono. intros c' [Hc' F2]. split; [exact Hc'|].
  exact (seg_fp_trans _ _ _ _ _ F1 F2).
Qed.

End B.
