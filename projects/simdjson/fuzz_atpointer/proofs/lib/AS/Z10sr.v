(* SPDX-License-Identifier: MIT *)
(* Image B's start-up join states, plan and hand-off table at the run's CONFIG_RSEQ value [r]
   (0 or 1), from the states computed in AS/Z10s0.v and AS/Z10s1.v; image B's twin of
   AS/Z10qr.v. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z Z2y PlanRegen Z10s Z10s0 Z10s1.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition RG_B (r : Z) : list (nat * acs) * list (nat * acs) * cres := if Z.eqb r 1 then RG_B1 else RG_B0.

(* the join states, the plan with them, and the hand-off table, at flag [r] *)
Definition VJ_B (r : Z) : list (nat * acs) := fst (fst (RG_B r)).
Definition startup_plan_rB (r : Z) : plan := plan_B (VJ_B r).
Definition HS_both_r (r : Z) : nat -> option acs := hlookup (snd (fst (RG_B r))).
(* the hand-off states as a list, for the proofs that check each of them *)
Definition HS_list_rB (r : Z) : list acs := map snd (snd (fst (RG_B r))).
Lemma HS_both_r_In : forall r h ch, HS_both_r r h = Some ch -> In ch (HS_list_rB r).
Proof.
  intros r h ch. unfold HS_both_r, HS_list_rB, hlookup.
  destruct (find _ _) as [[h' a]|] eqn:E; intro H; [|discriminate H].
  injection H as <-. apply find_some in E as [Hin _].
  apply in_map_iff. exists (h', a). split; [reflexivity | exact Hin].
Qed.
