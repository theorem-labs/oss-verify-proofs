(* Arm c2 (op_mark), piece HEAD: the loop head with op 2 -> c2_13d70 (dispatch, name_of, kernel,
   model_begin), the two segments LC2Head1 (to the kernel call, c2h_13d48) and LC2Head2 joined with
   c2_post_seq. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LC2HeadA LC2Head1 LC2Head2.
Section H.
Hypothesis KERNEL_OK : kernel_contract.
Lemma c2_head : forall (E : lenv) (i : Z) (gp : word) (ms : machine_state),
  lenv_ok E -> lh_ms E i gp ms -> lh_op E ms 2 ->
  evt rsegs (c2_post E (ms_mem ms) (fun c => exists s, c2_13d70 E i gp s c)) ms.
Proof.
  intros E i gp ms HE HL HO.
  apply (c2_post_seq E (fun c => exists s, c2h_13d48 E i gp s c)).
  - exact (c2h_head1 E i gp ms HE HL HO).
  - intros c (s & Hc). exact (c2h_head2 KERNEL_OK E i gp s c HE Hc).
Qed.
End H.
