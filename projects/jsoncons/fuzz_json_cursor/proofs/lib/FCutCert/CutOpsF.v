(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CXF.

Definition forget (r : nat) (ss : sym_state) : option sym_state :=
  if (Nat.ltb 0 r && Nat.ltb r 32 && sr_vars_lt (s_next ss) (s_regs ss) && kn_vars_lt (s_next ss) (s_know ss))%bool
  then Some (SSR (s_pc ss) (sr_upd (s_regs ss) r (EVar (s_next ss))) (s_log ss) (s_know ss) (S (s_next ss)) (s_resv ss))
  else None.

Fixpoint esize (e : expr) : nat :=
  match e with
  | ELit _ | EVar _ | EBlob _ _ _ _ => 1%nat
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esize a + esize b)
  | EExt _ _ _ a => S (esize a)
  end.

Fixpoint esize_le (n : nat) (e : expr) : option nat :=
  match n with
  | O => None
  | S m =>
      match e with
      | ELit _ | EVar _ | EBlob _ _ _ _ => Some m
      | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
          match esize_le m a with Some m' => esize_le m' b | None => None end
      | EExt _ _ _ a => esize_le m a
      end
  end.
Definition big (n : nat) (e : expr) : bool := match esize_le n e with Some _ => false | None => true end.

Definition big_regs (n : nat) (keep : list nat) (ss : sym_state) : list nat :=
  List.filter (fun r => (big n (nth r (s_regs ss) (ELit 0)) && negb (existsb (Nat.eqb r) keep))%bool) (seq 1 31).

Lemma forget_next : forall r ss ss', forget r ss = Some ss' -> s_next ss' = S (s_next ss) /\ s_pc ss' = s_pc ss.
Proof. intros r ss ss' H. unfold forget in H. destruct (_ && _)%bool; [|discriminate]. injection H as <-. split; reflexivity. Qed.

Lemma forget_sound : forall segs nx0 BR F M0 r ss ss' E R Mc,
  forallb (SGP.region_vars_lt nx0) F = true -> SGP.bfacts_vars_lt BR nx0 = true ->
  forget r ss = Some ss' -> SGP.INV2 segs nx0 BR F M0 E ss R Mc ->
  exists E', env_agree (s_next ss) E E' /\ SGP.INV2 segs nx0 BR F M0 E' ss' R Mc /\ s_pc ss' = s_pc ss.
Proof.
  intros segs nx0 BR F M0 r ss ss' E R Mc Fv BRv H HI. unfold forget in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32 && sr_vars_lt (s_next ss) (s_regs ss) && kn_vars_lt (s_next ss) (s_know ss))%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hc Hkn]. apply andb_prop in Hc as [Hc Hsr]. apply andb_prop in Hc as [Hr0 Hr32].
  apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32.
  set (rr := Z_to_bv 5 (Z.of_nat r) : reg).
  set (E' := APS.ext1 E (s_next ss) (getr R rr)).
  pose proof (APS.ext1_agree E (s_next ss) (getr R rr)) as Hag. fold E' in Hag.
  exists E'. split; [exact Hag|]. split; [|reflexivity].
  pose proof (SGP.i_regs _ _ _ _ _ _ _ _ _ HI) as HR. pose proof (SGP.i_know _ _ _ _ _ _ _ _ _ HI) as HK. pose proof (SGP.i_nx _ _ _ _ _ _ _ _ _ HI) as Hnx.
  eapply (SGP.INV2_reenv segs nx0 BR F Fv BRv M0 (s_next ss) E E' ss _ R R Mc HI Hag Hnx); cbn [s_regs s_know s_next].
  -
    pose proof (regs_ok_agree (s_next ss) E E' (s_regs ss) R Hag Hsr HR) as HR'.
    intros q. unfold sr_get. destruct (bv_eqb q 0) eqn:Hq0.
    + rewrite (HR' q). unfold sr_get. rewrite Hq0. reflexivity.
    + rewrite nth_sr_upd. destruct (Nat.eqb (ridx q) r) eqn:Hi.
      * apply Nat.eqb_eq in Hi. assert (q = rr) as ->.
        { apply ridx_inj. unfold rr. rewrite APS.ridx_lit by lia. exact Hi. }
        cbn [edenot]. unfold E'. rewrite APS.ext1_at. reflexivity.
      * rewrite (HR' q). unfold sr_get. rewrite Hq0. reflexivity.
  - exact (know_ok_agree segs (s_next ss) E E' Mc (s_know ss) Hag Hkn HK).
  - lia.
Qed.

End CXF.
