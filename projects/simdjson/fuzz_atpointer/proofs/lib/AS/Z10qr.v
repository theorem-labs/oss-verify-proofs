(* SPDX-License-Identifier: MIT *)
(* Image A's start-up join states, plan and hand-off table at the run's CONFIG_RSEQ value [r]
   (0 or 1), from the states computed in AS/Z10q0.v and AS/Z10q1.v. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z Z2y PlanRegen Z10q Z10q0 Z10q1.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition RG_A (r : Z) : list (nat * acs) * list (nat * acs) * cres := if Z.eqb r 1 then RG_A1 else RG_A0.

(* the join states, the plan with them, and the hand-off table, at flag [r] *)
Definition VJ_A (r : Z) : list (nat * acs) := fst (fst (RG_A r)).
Definition startup_plan_r (r : Z) : plan := plan_A (VJ_A r).
Definition HS_asan_r (r : Z) : nat -> option acs := hlookup (snd (fst (RG_A r))).
(* the hand-off states as a list, for the proofs that check each of them *)
Definition HS_list_r (r : Z) : list acs := map snd (snd (fst (RG_A r))).
Lemma HS_asan_r_In : forall r h ch, HS_asan_r r h = Some ch -> In ch (HS_list_r r).
Proof.
  intros r h ch. unfold HS_asan_r, HS_list_r, hlookup.
  destruct (find _ _) as [[h' a]|] eqn:E; intro H; [|discriminate H].
  injection H as <-. apply find_some in E as [Hin _].
  apply in_map_iff. exists (h', a). split; [reflexivity | exact Hin].
Qed.
