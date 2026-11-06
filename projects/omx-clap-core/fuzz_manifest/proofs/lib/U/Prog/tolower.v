From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import tolower_c.
Import ListNotations.
Open Scope Z_scope.

Lemma zbrute : forall (f g : Z -> Z) (lo hi : Z),
  forallb (fun k => Z.eqb (f (lo + Z.of_nat k)) (g (lo + Z.of_nat k))) (seq 0 (Z.to_nat (hi - lo))) = true ->
  forall c, lo <= c < hi -> f c = g c.
Proof.
  intros f g lo hi H c Hc. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (c - lo)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. replace (lo + (c - lo)) with c in H by lia.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma u_if01 : forall b : bool, bv_unsigned (if b then Z_to_bv 64 1 else Z_to_bv 64 0) = if b then 1 else 0.
Proof. intros [|]; reflexivity. Qed.

Lemma tolower_expr : forall c, 0 <= c < 256 ->
  Z_to_bv 64 (Z.lor c (bv_unsigned (Z_to_bv 64 (Z.shiftl
     (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_swrap 32 (c + -65))) 26)) 5))))
  = Z_to_bv 64 (zlower c).
Proof.
  intros c Hc. f_equal. unfold v_sltiu. rewrite u_if01, !unsigned_lit_wrap.
  revert c Hc.
  apply (zbrute (fun c => Z.lor c ((Z.shiftl (if (bv_swrap 32 (c + -65) mod 2^64 <? bv_wrap 64 26) then 1 else 0) 5)
                                   mod 2^64))
                zlower 0 256).
  vm_compute. reflexivity.
Qed.

Theorem tolower_holds : tolower_contract.
Proof.
  unfold tolower_contract, TOLOWER.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HC.
  step. step. step. step. step.
  rewrite (tolower_expr (bv_unsigned a0) HC).
  apply evt_done. eexists. reflexivity.
Qed.
