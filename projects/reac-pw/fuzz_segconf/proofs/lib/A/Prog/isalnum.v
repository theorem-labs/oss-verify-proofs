(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/isalnum.v, unchanged. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import isalnum_c.
Import ListNotations.
Open Scope Z_scope.

Definition isalnum_reg (c : Z) : word :=
  Z_to_bv 64
    (Z.lor
       (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 c) + -48))) 10))
       (bv_unsigned
          (v_sltiu (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 c)) 32)) + -97)))
             26))).

Lemma isalnum_table :
  forallb (fun n => let c := Z.of_nat n in
                    Z.eqb (bv_unsigned (isalnum_reg c)) (bv_unsigned (Z_to_bv 64 (if alnum_b c then 1 else 0))))
          (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma isalnum_reg_ok : forall c, 0 <= c < 256 -> isalnum_reg c = Z_to_bv 64 (if alnum_b c then 1 else 0).
Proof.
  intros c Hc. apply bv_eq.
  pose proof (proj1 (forallb_forall _ _) isalnum_table (Z.to_nat c)) as H.
  rewrite in_seq in H. specialize (H ltac:(lia)). cbv beta in H.
  rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.

Theorem isalnum_holds : isalnum_contract.
Proof.
  unfold isalnum_contract, ISALNUM.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c Hc ->.
  step. step. step. step. step. step. step.
  apply evt_done. eexists.
  rewrite <- (isalnum_reg_ok c Hc). unfold isalnum_reg, mkR. reflexivity.
Qed.
