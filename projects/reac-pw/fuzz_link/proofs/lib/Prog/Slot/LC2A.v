(* Arm c2 (op_mark), segment A: the loop head of an operation whose byte is 2 mod 6 -> the call of
   mark_quietly at 0x13dac (the SR cut c2_15d88, ra 0x13db0). Composed from the pieces:
     LC2Head  lh_ms / lh_op 2 -> c2_13d70   (dispatch, name_of, kernel, model_begin)
     LC2Read  c2_13d70 -> c2_13da4 \/ c2_1407c   (the name test, model_read)
     LC2Dec   c2_1407c -> c2_13da4 \/ c2_140d4   (model_decide, bcmp, model_write)
     LC2Rem   c2_140d4 -> c2_13da4   (model_remember: strcmp loop, snprintf into the model block)
     LC2Call  c2_13da4 -> c2_15d88   (a0 = marks, a1 = name, jal mark_quietly)
   Every callee contract is a Section hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem kernel_c model_read_c
  model_decide_c bcmp_c model_write_c printf_facts_c strcmp_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs LC2Call
  LC2Head LC2Read LC2Dec LC2Rem.
Local Open Scope Z_scope.

Section A.
Hypothesis KERNEL_OK : kernel_contract.
Hypothesis MODEL_READ_OK : model_read_contract.
Hypothesis MODEL_DECIDE_OK : model_decide_contract.
Hypothesis BCMP_OK : bcmp_contract.
Hypothesis MODEL_WRITE_OK : model_write_contract.
Hypothesis STRCMP_OK : strcmp_contract.
Hypothesis SNPRINTF_OK : snprintf_contract.

(* 0x13d70 -> 0x13dac: the inlined model_mark, then the call *)
Lemma c2_model : forall (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state),
  lenv_ok E -> c2_13d70 E i gp s ms ->
  evt rsegs (c2_post E (ms_mem ms) (c2_15d88 E i gp s)) ms.
Proof.
  intros E i gp s ms HE H.
  eapply c2_post_seq; [eapply c2_read; eauto|].
  intros c [Hd | Hr]; [exact (c2_call E i gp s c Hd)|].
  eapply c2_post_seq; [eapply c2_dec; eauto|].
  intros c' [Hd' | Hm]; [exact (c2_call E i gp s c' Hd')|].
  eapply c2_post_seq; [eapply c2_rem; eauto|].
  intros c'' Hd''. exact (c2_call E i gp s c'' Hd'').
Qed.

Theorem c2_segA : forall (E : lenv) (i : Z) (gp : word) (ms : machine_state),
  lenv_ok E -> lh_ms E i gp ms -> lh_op E ms 2 ->
  evt rsegs (c2_post E (ms_mem ms) (fun c => exists s, c2_15d88 E i gp s c)) ms.
Proof.
  intros E i gp ms HE HL HO.
  eapply c2_post_seq; [eapply c2_head; eauto|].
  intros c [s Hc]. eapply c2_post_mono; [exact (c2_model E i gp s c HE Hc)|].
  intros c' H'. exists s. exact H'.
Qed.
End A.
