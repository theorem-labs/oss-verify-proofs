(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Section S.
Variable segs : list Segment.

Lemma mstep_eqv ms ms' ms1 : ms_eqv ms ms' -> mstep segs ms ms1 -> exists ms1', mstep segs ms' ms1' /\ ms_eqv ms1 ms1'.
Proof.
  intros Heqv [Hsvc Hst]. pose proof (step_eqv segs ms ms' Heqv) as R. rewrite Hst in R.
  destruct (RiscvSemantics.step segs ms') as [ms1'| |] eqn:E; cbn in R; try contradiction.
  exists ms1'. split; [| exact R]. split; [| exact E]. destruct Heqv as (_ & _ & _ & Hs & _). congruence.
Qed.

Lemma msteps_eqv ms ms1 : msteps segs ms ms1 -> forall ms', ms_eqv ms ms' -> exists ms1', msteps segs ms' ms1' /\ ms_eqv ms1 ms1'.
Proof.
  induction 1 as [ms|ms msa msb Hst Hs IH]; intros ms' Heqv.
  - exists ms'. split; [apply msteps_refl| exact Heqv].
  - destruct (mstep_eqv ms ms' msa Heqv Hst) as (msa' & Hst' & Ha).
    destruct (IH msa' Ha) as (msb' & Hs' & Hb). exists msb'. split; [eapply msteps_cons; eauto| exact Hb].
Qed.

Lemma evt_eqv (Q : machine_state -> Prop) ms ms' :
  ms_eqv ms ms' -> evt segs Q ms -> evt segs (fun x => exists y, Q y /\ ms_eqv y x) ms'.
Proof.
  intros Heqv (ms1 & Hs & HQ). destruct (msteps_eqv ms ms1 Hs ms' Heqv) as (ms1' & Hs' & H1).
  exists ms1'. split; [exact Hs'|]. exists ms1. auto.
Qed.

Lemma areg_eqv ms ms' r : ms_eqv ms ms' -> is_x0 r = false -> areg ms r = areg ms' r.
Proof. intros (HR & _) Hr. unfold areg. apply HR. exact Hr. Qed.

Lemma at_node_eqv n ms ms' : ms_eqv ms ms' -> at_node segs n ms -> at_node segs n ms'.
Proof.
  intros Heqv H. pose proof Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  assert (A : forall r, is_x0 r = false -> areg ms r = areg ms' r) by (intros; apply areg_eqv; assumption).
  destruct n; cbn in H |- *;
    rewrite <- ?Hsvc, <- ?Hm, <- ?Hro, <- ?(A 10%bv eq_refl), <- ?(A 11%bv eq_refl), <- ?(A 12%bv eq_refl),
            <- ?(A 13%bv eq_refl), <- ?(A 14%bv eq_refl), <- ?(A 15%bv eq_refl); exact H.
Qed.

Lemma nret_eqv ms ms' eff : ms_eqv ms ms' -> ms_eqv (nret ms eff) (nret ms' eff).
Proof. intros H. unfold nret. apply advance_past_svc_eqv, apply_effect_eqv, H. Qed.

Theorem impl_eqv {R} : forall (t : itree node R) (Q : R -> machine_state -> Prop) ms ms',
  impl segs (at_node segs) t Q ms -> ms_eqv ms ms' ->
  impl segs (at_node segs) t (fun r x => exists y, Q r y /\ ms_eqv y x) ms'.
Proof.
  induction t as [r|n k IH]; intros Q ms ms' H Heqv; cbn in H |- *.
  - exact (evt_eqv _ _ _ Heqv H).
  - pose proof (evt_eqv _ _ _ Heqv H) as E. eapply evt_mono; [exact E|].
    intros x (y & [Hat Hk] & Hyx). split; [exact (at_node_eqv n y x Hyx Hat)|].
    intros rsp. apply (IH rsp Q (nret y rsp) (nret x rsp) (Hk rsp)). apply nret_eqv. exact Hyx.
Qed.

Definition mkR_of (R : bvmap 5 word) : bvmap 5 word :=
  mkR (reg_get R 1) (reg_get R 2) (reg_get R 3) (reg_get R 4) (reg_get R 5) (reg_get R 6) (reg_get R 7) (reg_get R 8)
      (reg_get R 9) (reg_get R 10) (reg_get R 11) (reg_get R 12) (reg_get R 13) (reg_get R 14) (reg_get R 15) (reg_get R 16)
      (reg_get R 17) (reg_get R 18) (reg_get R 19) (reg_get R 20) (reg_get R 21) (reg_get R 22) (reg_get R 23) (reg_get R 24)
      (reg_get R 25) (reg_get R 26) (reg_get R 27) (reg_get R 28) (reg_get R 29) (reg_get R 30) (reg_get R 31).

Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

Lemma mkR_of_eqv R : regs_eqv R (mkR_of R).
Proof.
  intros r Hr. destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [first [discriminate Hr | (unfold mkR_of; vm_compute; reflexivity) | reflexivity]|]). lia.
Qed.

Lemma MS_eqv_mkR R F pc fc m ro : ms_eqv (MS R F pc fc None m ro) (MS (mkR_of R) F pc fc None m ro).
Proof. split; [apply mkR_of_eqv|]. repeat split; reflexivity. Qed.
End S.

End AC_1.
