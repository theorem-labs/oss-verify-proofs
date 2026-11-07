(* Runs in the cjson-style library (Lib/Exec.v, [evt]) are runs in cgif's library (YK0j [msteps]),
   and runs transfer between register files that read the same (OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B.RegsExt). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B Require Import RegsExt.
Require OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Exec.
Require OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Frame.
Require OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C.YK0j.
Module CJ := OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Exec.
Module CJF := OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.J.Lib.Frame.
Module CG := OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C.YK0j.

Section S.
Variable segs : list Segment.

Lemma msteps_cj_cg : forall s s', CJ.msteps segs s s' -> CG.msteps segs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 [Hsvc Hst] _ IH].
  - apply CG.mst_refl.
  - eapply CG.mst_step; [exact Hsvc | exact Hst | exact IH].
Qed.

Lemma evt_cg : forall (Q : machine_state -> Prop) s, CJ.evt segs Q s -> exists s', CG.msteps segs s s' /\ Q s'.
Proof. intros Q s (s' & H & HQ). exists s'. split; [apply msteps_cj_cg, H | exact HQ]. Qed.

Lemma msteps_ext : forall s1 s1', CG.msteps segs s1 s1' -> forall s2, msext s1 s2 ->
  exists s2', CG.msteps segs s2 s2' /\ msext s1' s2'.
Proof.
  intros s1 s1' H. induction H as [s|s s' s'' Hsvc Hst _ IH]; intros s2 HE.
  - exists s2. split; [apply CG.mst_refl | exact HE].
  - destruct (step_ext segs s s2 s' HE Hst) as (s2' & Hst2 & HE').
    destruct (IH s2' HE') as (s2'' & H2 & HE''). exists s2''. split; [|exact HE''].
    eapply CG.mst_step; [| exact Hst2 | exact H2].
    destruct HE as (_ & _ & _ & HV & _). rewrite <- HV. exact Hsvc.
Qed.
End S.

(* any register file reads as the mkR tree of its own values *)
Local Open Scope Z_scope.
Definition canon (R : bvmap 5 word) : bvmap 5 word :=
  let g (k : Z) := PropExec.getr R (Z_to_bv 5 k) in
  CJF.mkR (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) (g 12) (g 13) (g 14) (g 15)
          (g 16) (g 17) (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27) (g 28) (g 29) (g 30) (g 31).

Lemma canon_rext : forall R, rext (canon R) R.
Proof.
  intros R r Hr.
  pose proof (bv_unsigned_in_range _ r) as X. change (bv_modulus 5) with 32 in X.
  assert (Er : r = Z_to_bv 5 (bv_unsigned r)) by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range).
  assert (Hk : bv_unsigned r <> 0) by (intro E; unfold is_x0 in Hr; rewrite E in Hr; discriminate Hr).
  remember (bv_unsigned r) as k eqn:Ek. rewrite Er. clear Er Ek Hr.
  assert (k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst k; reflexivity.
Qed.
