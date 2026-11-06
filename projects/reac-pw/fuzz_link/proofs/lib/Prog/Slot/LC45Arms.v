(* Arms 4 and 5 of the slot's loop (fuzz_link.c:744-762), plain image: every evt segment of op_decide
   and op_refused, from the loop head (lh_ms with the op byte, lh_op) to the arm's first allocator-facing
   call, between the calls, and from the last call's return to the next loop head or the exit (c45_fin =
   LLoop's ARM_OK post). Each post is a Theorem Labs lane's form `eqv_cl (fun ms' => <cut> ms' /\ seg_fp (e_S E)
   (c45_hp E) (ms_mem ms) (ms_mem ms'))`, written `eqv_cl (c45_post E (ms_mem ms) <cut>)` (LC45Defs).
   The cuts between are LC45Defs' (allocator-facing calls: text_of x2, free x2, mark_quietly); the leaf
   callees (reac_served_decide, model_decide, check_verdict, check_mark, check_requests) are Section
   hypotheses.

   op_decide:  c45_decide_head  lh_ms (op 4)  -> c45_13aa4 (text_of, ra 0x13aa8)
               c45_decide_to2   c45_13aa8     -> c45_13ab4 (text_of, ra 0x13ab8)
               c45_decide_mid   c45_13ab8     -> c45_13ae8 (free own1, ra 0x13aec)
               c45_decide_fr2   c45_13aec     -> c45_13af0 (free own2, ra 0x13af4)
               c45_decide_end   c45_13af4     -> c45_fin
   op_refused: c45_refused_head lh_ms (op 5)  -> c45_13c70 (mark_quietly, ra 0x13c74)
               c45_refused_end  c45_13c74     -> c45_fin *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import model_decide_c check_verdict_c
  check_write_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC45Defs LC45Call
  LC45ComLib LC45Com LC45D LC45D2 LC45R0 LC45R1.
Local Open Scope Z_scope.

(* a c45_post run followed by an eqv_cl c45_post run from its end is one eqv_cl c45_post run *)
Lemma c45_post_bind : forall E m0 (Q R : machine_state -> Prop) ms,
  evt rsegs (c45_post E m0 Q) ms ->
  (forall ms1, Q ms1 -> evt rsegs (eqv_cl (c45_post E (ms_mem ms1) R)) ms1) ->
  evt rsegs (eqv_cl (c45_post E m0 R)) ms.
Proof.
  intros E m0 Q R ms H K. eapply evt_cut; [exact H|]. intros ms1 [HQ F1].
  eapply evt_mono; [exact (K ms1 HQ)|]. intros ms2 (c & [HR F2] & EQ).
  exists c. split; [split; [exact HR | exact (c45_seg_fp_trans _ _ _ _ _ F1 F2)] | exact EQ].
Qed.

(* the same, when the first run's end is reached only up to register equivalence *)
Lemma c45_post_bind_eqv : forall E m0 (Q R : machine_state -> Prop) ms,
  evt rsegs (eqv_cl (c45_post E m0 Q)) ms ->
  (forall ms1, Q ms1 -> evt rsegs (c45_post E (ms_mem ms1) R) ms1) ->
  evt rsegs (eqv_cl (c45_post E m0 R)) ms.
Proof.
  intros E m0 Q R ms H K. eapply evt_cut; [exact H|]. intros a (c & [HQ F1] & EQ).
  pose proof (evt_register_transport rsegs _ c a EQ (K c HQ)) as T.
  eapply evt_mono; [exact T|]. intros b (c' & [HR F2] & EQ').
  exists c'. split; [split; [exact HR|] | exact EQ'].
  destruct EQ as (_ & _ & _ & _ & _ & _ & EM & _).
  exact (c45_seg_fp_trans _ _ _ _ _ F1 F2).
Qed.

Section Arms.
Hypothesis RSD : reac_served_decide_contract.
Hypothesis MDC : model_decide_contract.
Hypothesis CVC : check_verdict_contract.
Hypothesis CMK : check_mark_contract.
Hypothesis CRQ : check_requests_contract.

(* ---- op_decide (op byte % 6 = 4, 0x13a9c) ---- *)

Lemma c45_decide_head : forall E i gp ms, lenv_ok E -> lh_ms E i gp ms -> lh_op E ms 4 ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_13aa4 E i gp))) ms.
Proof.
  intros E i gp ms OK HL HO.
  eapply c45_post_bind; [exact (c45_dispatch E i gp 4 ms OK HL HO (or_introl eq_refl))|].
  intros ms1 HD. exact (c45_d0 E i gp ms1 OK HD).
Qed.

Lemma c45_decide_to2 : forall E i gp own1 ms, lenv_ok E -> c45_13aa8 E i gp own1 ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_13ab4 E i gp own1))) ms.
Proof. exact c45_d1. Qed.

Lemma c45_decide_mid : forall E i gp own1 own2 ms, lenv_ok E -> c45_13ab8 E i gp own1 own2 ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_13ae8 E i gp own1 own2))) ms.
Proof. exact (c45_d2 RSD MDC CVC). Qed.

Lemma c45_decide_fr2 : forall E i gp own1 own2 ms, lenv_ok E -> c45_13aec E i gp own1 own2 ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_13af0 E i gp own1 own2))) ms.
Proof. exact c45_d3. Qed.

Lemma c45_decide_end : forall E i gp own1 own2 ms, lenv_ok E -> c45_13af4 E i gp own1 own2 ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_fin E i gp))) ms.
Proof.
  intros E i gp own1 own2 ms OK H.
  pose proof (c45_tail E i gp C45_END_D ms OK (or_introl eq_refl) (c45_d4 E i gp own1 own2 ms OK H)) as T.
  eapply evt_mono; [exact T|]. intros ms' HP. exact (c45_eqv_cl_of _ _ HP).
Qed.

(* ---- op_refused (op byte % 6 = 5, 0x13bf4) ---- *)

Lemma c45_refused_head : forall E i gp ms, lenv_ok E -> lh_ms E i gp ms -> lh_op E ms 5 ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (fun ms' => exists w, c45_13c70 E i gp w ms'))) ms.
Proof.
  intros E i gp ms OK HL HO.
  eapply c45_post_bind; [exact (c45_dispatch E i gp 5 ms OK HL HO (or_intror eq_refl))|].
  intros ms1 HD. exact (c45_r0 E i gp ms1 OK HD).
Qed.

Lemma c45_refused_end : forall E i gp w ms, lenv_ok E -> c45_13c74 E i gp w ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_fin E i gp))) ms.
Proof.
  intros E i gp w ms OK H.
  eapply c45_post_bind_eqv; [exact (c45_r1 CMK CRQ E i gp w ms OK H)|].
  intros ms1 HE. exact (c45_tail E i gp C45_END_R ms1 OK (or_intror eq_refl) HE).
Qed.

End Arms.

Check c45_decide_mid.
Check c45_refused_end.

Print Assumptions c45_decide_head.
Print Assumptions c45_decide_to2.
Print Assumptions c45_decide_mid.
Print Assumptions c45_decide_fr2.
Print Assumptions c45_decide_end.
Print Assumptions c45_refused_head.
Print Assumptions c45_refused_end.
