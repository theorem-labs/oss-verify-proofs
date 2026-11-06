(* The op_unmark arm (c3) of LLVMFuzzerTestOneInput, plain image: its one segment, from the loop head of
   operation i (op byte % 6 = 3) to the loop head of operation i + 1 or to the exit, within the arm's write set:
   LC3Head (dispatch, kernel, model_begin) -> c3_mb -> LC3Loop (model_unmark) -> c3_ub -> LC3Tail
   (reac_served_unmark_all, check_socket, check_marks, check_requests, the tail). The callee contracts are
   Section hypotheses. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c model_read_c model_write_c
  bcmp_c reac_served_unmark_all_c check_socket_c check_marks_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC3Lib LC3Defs LC3Head LC3Loop LC3Tail.
Local Open Scope Z_scope.

Section C3Seg.
Hypothesis KERNEL_C : kernel_contract.
Hypothesis MODEL_READ_C : model_read_contract.
Hypothesis MODEL_WRITE_C : model_write_contract.
Hypothesis BCMP_C : bcmp_contract.
Hypothesis UNMARK_ALL_C : reac_served_unmark_all_contract.
Hypothesis CHECK_SOCKET_C : check_socket_contract.
Hypothesis CHECK_MARKS_C : check_marks_contract.
Hypothesis CHECK_REQUESTS_C : check_requests_contract.

Theorem c3_arm : forall (E : lenv) (i : Z) (gp : word) (ms : machine_state),
  lenv_ok E -> lh_ms E i gp ms -> lh_op E ms 3 ->
  evt rsegs (eqv_cl (fun c => ((i < 47 /\ lh_ms E (i + 1) gp c) \/ ex_ms E gp c) /\
                              seg_fp (e_S E) [(e_md E, MD_SIZE); (e_mk E, MK_SIZE)] (ms_mem ms) (ms_mem c))) ms.
Proof.
  intros E i gp ms HE HL HO.
  eapply evt_eqv_cut; [exact (c3_head KERNEL_C E i gp ms HE HL HO)|].
  intros c Hc.
  eapply evt_eqv_cut; [exact (c3_loop MODEL_READ_C MODEL_WRITE_C BCMP_C E i gp (ms_mem ms) c HE Hc)|].
  intros c' Hc'.
  exact (c3_tail UNMARK_ALL_C CHECK_SOCKET_C CHECK_MARKS_C CHECK_REQUESTS_C E i gp (ms_mem ms) c' HE Hc').
Qed.

End C3Seg.

About c3_arm.
Print Assumptions c3_arm.
