(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start states of the recorded S6 hand-off states beside the computed ones, the variable map read from probes of the run at 727298f3, and the leaf check's carried-fact test the holes' end states are moved with). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsHSTab.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import EAsStartupHSA EAsStartupHSARec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Br3Trans BrRa.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition UW_LONG : kentry := KRange (EVar 10) 0 5.
Definition UW_SHORT : kentry := KRange (EVar 10) 6 10.

Definition s6start0 : acs := set_kn HSA_easan_0 (UW_LONG :: kn HSA_easan_0).
Definition s6start1 : acs := set_kn HSA_easan_0 (UW_SHORT :: kn HSA_easan_0).
Definition s6start2 : acs := set_kn HSA_easan_1 (UW_LONG :: kn HSA_easan_1).
Definition s6start3 : acs := set_kn HSA_easan_1 (UW_SHORT :: kn HSA_easan_1).
Definition s6start4 : acs := HSA_easan_2.
Definition s6start5 : acs := HSA_easan_3.

(** LPS 727298f3: the start states the recorded S6 hand-off states ([EAsStartupHSARec]) gave, made as above; each
    hole's recorded end state is moved to the new start ([ES6End0] .. [ES6End5]) against these and the computed
    ones ([s6start0] .. [s6start5], over the S6 states the run computes in the build). *)
Definition s6start_rec0 : acs := set_kn HSA_easan_rec_0 (UW_LONG :: kn HSA_easan_rec_0).
Definition s6start_rec1 : acs := set_kn HSA_easan_rec_0 (UW_SHORT :: kn HSA_easan_rec_0).
Definition s6start_rec2 : acs := set_kn HSA_easan_rec_1 (UW_LONG :: kn HSA_easan_rec_1).
Definition s6start_rec3 : acs := set_kn HSA_easan_rec_1 (UW_SHORT :: kn HSA_easan_rec_1).
Definition s6start_rec4 : acs := HSA_easan_rec_2.
Definition s6start_rec5 : acs := HSA_easan_rec_3.

(** LPS 727298f3: [vsh_hand], the recorded S6 states' variables in the numbering of the run at 727298f3, a total
    monotone map read from probes of that run: the S6 plans' map [EAsStartupHSA.vsh_s6], whose first step
    (old 44 is new 50, old 61 is new 67: the thread-id word and the canary words) and second (old 326 is new 334 at LPS c0dd863a)
    the run itself shows.  The variables a hole creates
    (at and above the recorded states' counter) move with its last step, as the computed states' counter does. *)
Definition vsh_hand : nat -> nat := vsh_s6.

(** the facts of a start state [S] that a hole's leaf check takes as carried to its end state: the check's own
    classification ([Br3Trans.pre_old], as [Br3Trans.rest3x_chk] computes it) at 1 or 2 *)
Definition carried3 IM A TT classes (S : acs) d bs (cands : list kentry) : list kentry :=
  map fst (filter (fun p => orb (Z.eqb (snd p) 1) (Z.eqb (snd p) 2))
                  (combine cands (Br3Trans.pre_old IM A TT classes S d bs (BrRa.ra_fast (kn S)) (set_kn S cands)))).

Definition S6START_table : list (nat * acs) :=
  [(0%nat, s6start0); (1%nat, s6start1); (2%nat, s6start2); (3%nat, s6start3); (4%nat, s6start4); (5%nat, s6start5)].
Definition S6START (h : nat) : option acs := hs_lookup h S6START_table.

Lemma S6START_pc : forall h ch, S6START h = Some ch -> pc ch = pc HSA_easan_0.
Proof.
  intros h ch H. apply hs_lookup_cases in H. cbn [S6START_table fold_right fst snd] in H.
  repeat (destruct H as [[_ ->]|H]; [vm_compute; reflexivity|]). destruct H.
Qed.

Lemma erange_w_0 : erange (kn HSA_easan_0) (EVar 10) = Some (0, 10).
Proof. vm_compute. reflexivity. Qed.
Lemma erange_w_1 : erange (kn HSA_easan_1) (EVar 10) = Some (0, 10).
Proof. vm_compute. reflexivity. Qed.

Section Split.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).

  (* [comment removed for export] *)
  Lemma s6_split : forall k ch E R FULL model,
    HSA_easan k = Some ch -> CSOK E ch R FULL model ->
    exists h ch', S6START h = Some ch' /\ pc ch' = pc ch /\ CSOK E ch' R FULL model.
  Proof.
    intros k ch E R FULL model Hk HC. apply hs_lookup_cases in Hk. cbn [HSA_easan_table fold_right fst snd] in Hk.
    destruct Hk as [[-> ->]|Hk].
    { destruct (split_sound SEGS A LIMIT SINV argH FS0 HSA_easan_0 (EVar 10) 5 0 10 E R FULL model HC erange_w_0) as [S1 S2].
      destruct (Z_le_gt_dec (bv_unsigned (edenot E (EVar 10))) 5) as [Hle|Hgt].
      - exists 0%nat, s6start0. split; [reflexivity|]. split; [reflexivity|]. exact (S1 Hle).
      - exists 1%nat, s6start1. split; [reflexivity|]. split; [reflexivity|]. exact (S2 ltac:(lia)). }
    destruct Hk as [[-> ->]|Hk].
    { destruct (split_sound SEGS A LIMIT SINV argH FS0 HSA_easan_1 (EVar 10) 5 0 10 E R FULL model HC erange_w_1) as [S1 S2].
      destruct (Z_le_gt_dec (bv_unsigned (edenot E (EVar 10))) 5) as [Hle|Hgt].
      - exists 2%nat, s6start2. split; [reflexivity|]. split; [reflexivity|]. exact (S1 Hle).
      - exists 3%nat, s6start3. split; [reflexivity|]. split; [reflexivity|]. exact (S2 ltac:(lia)). }
    destruct Hk as [[-> ->]|Hk]; [exists 4%nat, s6start4; split; [reflexivity|]; split; [reflexivity|]; exact HC|].
    destruct Hk as [[-> ->]|Hk]; [exists 5%nat, s6start5; split; [reflexivity|]; split; [reflexivity|]; exact HC|].
    destruct Hk.
  Qed.
End Split.
