(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Glue/CertSound.v: cert_sound and loop_sound restated over BudgetWit.Rzb.rzb *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import CertSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb PlanSoundB.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS PlanSB CertS.
Open Scope Z_scope.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module CertSB.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma contracts_ok_empty_b : forall C MP PB, c_contracts C = IMap.empty -> contracts_ok_b segs OPS C MP PB.
Proof. intros C MP PB He cid ct Hf. rewrite He in Hf. rewrite IMap.find_empty in Hf. discriminate. Qed.

Definition tpl_rzb (MP : Model -> Prop) (K : TSet) (E0 : env) (T : sstate) : Prop :=
  forall E ms model, eb E = eb E0 -> MP model -> st_ok segs OPS E T ms model -> rzb segs (mkCfg ms model) K.

Theorem cert_sound_b : forall (C : ctx) (p : plan) (st : sstate) (obls : list obligation)
                            (MP : Model -> Prop) (PB : (int -> list byte) -> Prop),
  mp_stable MP ->
  ctx_wfb C = true ->
  itab_ok segs (c_itab C) ->
  c_contracts C = IMap.empty ->
  check segs C p st = Some obls ->
  obls_hold PB obls ->
  vars_below (s_next st) (c_mroot C) = true ->
  forall (K : TSet) E ms model,
    st_ok segs OPS E st ms model -> PB (eb E) -> MP model ->
    leaves_ok_b segs OPS C p MP K E (bv_unsigned (den E (c_mroot C))) ->
    rzb segs (mkCfg ms model) K.
Proof.
  intros C p st obls MP PB HMPA HWF HIT HC HCHK HOB HM K E ms model HS HPB HMP HL.
  eapply (check_sound_b segs OPS C MP PB p st obls HWF HIT (contracts_ok_empty_b C MP PB HC) HMPA HCHK HOB HM K E ms model HS HPB HMP HL).
Qed.

Lemma leaves_ok_plain_b : forall C p MP K E mroot,
  (forall tid T, IMap.find tid (c_cuts C) = Some T -> tpl_rzb MP K E (t_st T)) ->
  (forall eid T, IMap.find eid (c_ecalls C) = Some T ->
     forall E' ms' model', eb E' = eb E -> MP model' -> st_ok segs OPS E' T ms' model' -> ecall_at segs (s_pc T) ->
       rzb segs (mkCfg ms' model') K) ->
  leaves_ok_b segs OPS C p MP K E mroot.
Proof.
  intros C p MP K E mroot Hc He. split.
  - intros tid T Hf E' ms' model' Heb HMP HS _. exact (Hc tid T Hf E' ms' model' Heb HMP HS).
  - exact He.
Qed.

Theorem loop_sound_b : forall (C : ctx) (p : plan) (obls : list obligation) (h : int) (HEAD : template)
                            (MP : Model -> Prop) (PB : (int -> list byte) -> Prop) (K : TSet) (E0 : env),
  mp_stable MP ->
  ctx_wfb C = true ->
  itab_ok segs (c_itab C) ->
  contracts_ok_b segs OPS C MP PB ->
  IMap.find h (c_cuts C) = Some HEAD ->
  c_mroot C = t_measure HEAD ->
  check segs C p (t_st HEAD) = Some obls ->
  obls_hold PB obls ->
  vars_below (s_next (t_st HEAD)) (t_measure HEAD) = true ->
  uses_plain_cut p h = false ->
  PB (eb E0) ->

  (forall tid T, IMap.find tid (c_cuts C) = Some T -> PrimInt63.eqb tid h = false -> tpl_rzb MP K E0 (t_st T)) ->

  (forall eid T, IMap.find eid (c_ecalls C) = Some T ->
     forall E' ms' model', eb E' = eb E0 -> MP model' -> st_ok segs OPS E' T ms' model' -> ecall_at segs (s_pc T) ->
       rzb segs (mkCfg ms' model') K) ->
  tpl_rzb MP K E0 (t_st HEAD).
Proof.
  intros C p obls h HEAD MP PB K E0 HMPA HWF HIT HCO Hh Hm HCHK HOB HMV Hplain HPB Hcuts Hecalls.
  assert (main : forall (k : nat) E ms model,
            bv_unsigned (den E (t_measure HEAD)) < Z.of_nat k ->
            eb E = eb E0 -> MP model -> st_ok segs OPS E (t_st HEAD) ms model ->
            rzb segs (mkCfg ms model) K).
  { induction k as [|k IH]; intros E ms model Hlt Heb HMP HS.
    - exfalso. pose proof (bv_unsigned_in_range _ (den E (t_measure HEAD))). cbn [Z.of_nat] in Hlt. lia.
    - eapply (check_sound_b segs OPS C MP PB p (t_st HEAD) obls HWF HIT HCO HMPA HCHK HOB); [rewrite Hm; exact HMV| exact HS | rewrite Heb; exact HPB | exact HMP |].
      split.
      + intros tid T Hf E' ms' model' Heb' HMP' HS' Hdec.
        destruct (PrimInt63.eqb tid h) eqn:Eth.
        * apply Uint63.eqb_correct in Eth. subst tid. rewrite Hh in Hf. injection Hf as <-.
          destruct Hdec as [Hpc | Hlt'].
          { rewrite Hplain in Hpc. discriminate. }
          rewrite Hm in Hlt'.
          apply (IH E' ms' model'); [ | congruence | exact HMP' | exact HS'].
          rewrite Nat2Z.inj_succ in Hlt. lia.
        * exact (Hcuts tid T Hf Eth E' ms' model' ltac:(congruence) HMP' HS').
      + intros eid T Hf E' ms' model' Heb' HMP' HS' Hat.
        exact (Hecalls eid T Hf E' ms' model' ltac:(congruence) HMP' HS' Hat). }
  intros E ms model Heb HMP HS.
  apply (main (S (Z.to_nat (bv_unsigned (den E (t_measure HEAD))))) E ms model); try assumption.
  pose proof (bv_unsigned_in_range _ (den E (t_measure HEAD))). rewrite Nat2Z.inj_succ, Z2Nat.id; lia.
Qed.

End WithSegs.
End CertSB.
