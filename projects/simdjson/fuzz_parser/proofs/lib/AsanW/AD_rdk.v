(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import RunConst ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Driver AsanCtrl AsanProgDeps ProgA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit APC_mpres.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT}.
Notation ioS := (ioA AAllocAsan).

(* [comment removed for export] *)
Lemma mleaves_true : forall {A} (c : MA A) s, mleaves (fun _ _ => True) c s.
Proof. intros A c s. unfold mleaves. eapply iall_mono; [| apply iall_true]. intros [|p] _; exact I. Qed.

Lemma mleaves_msys : forall {A} (P : A -> APS -> Prop) n (dec : resp -> option A) s, (forall a, P a s) -> mleaves P (msys n dec) s.
Proof.
  intros A P n dec s H. unfold mleaves, msys, enode. cbn. intros rsp. destruct (dec rsp) as [a|]; cbn; [exact (H a)| exact I].
Qed.

(* [comment removed for export] *)
Definition RDI (j : Z) (st : rd_st (ptr := AsanCtrl.aptr)) : Prop := rd_cap st = 2 ^ (16 + j) /\ 0 <= j <= 10.

Definition BODYP (j : Z) (s : APS) (r : rd_st (ptr := AsanCtrl.aptr) + rd_result (ptr := AsanCtrl.aptr)) (s' : APS) : Prop :=
  match r with
  | inl st' => exists j', RDI j' st' /\ j <= j' <= 10 /\ DK (j' - j) s s'
  | inr (RdDone _ _) => exists j', j <= j' <= 10 /\ DK (j' - j) s s'
  | inr RdExit => True
  end.

(* [comment removed for export] *)
Lemma rd_read_part_dk : forall fd path rs j j' (len : Z) (st1 : rd_st (ptr := AsanCtrl.aptr)) s s1,
  RDI j' st1 -> j <= j' <= 10 -> DK (j' - j) s s1 ->
  mleaves (BODYP j s)
    (let want0 := rd_cap st1 - len in
     let want := if 65536 <? want0 then 65536 else want0 in
     a <- msys (NRead fd rs want) (dec_read rs want) ;;
     match a with
     | RdErr _ => io_diag ioS (DReadError path) ;;; mret (inr RdExit)
     | RdData bs =>
         if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
         else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
     end) s1.
Proof.
  intros fd path rs j j' len st1 s s1 HR Hj D. cbv zeta.
  apply (mleaves_bind (fun a s' => s' = s1)); [apply mleaves_msys; reflexivity|].
  intros a s' ->. destruct a as [e|bs].
  - apply (mleaves_bind (fun _ _ => True)); [apply mleaves_true|]. intros _ s'' _. apply mleaves_ret. exact I.
  - destruct (length bs =? 0)%nat; apply mleaves_ret; cbn [BODYP].
    + exists j'. split; [exact Hj| exact D].
    + exists j'. split; [destruct HR as [HC HJ]; split; [exact HC| exact HJ]| split; [exact Hj| exact D]].
Qed.

Lemma body_dk : forall fd path rs j (st : rd_st (ptr := AsanCtrl.aptr)) s,
  RDI j st -> mleaves (BODYP j s) (read_loop_body ioS amalloc_M afree_M rs fd path st) s.
Proof.
  intros fd path rs j st s HR. unfold read_loop_body. cbv zeta.
  destruct (zlength (rd_content st) =? rd_cap st) eqn:EL.
  - destruct (MAX_INPUT <=? rd_cap st) eqn:EM.
    + (* [comment removed for export] *)
      apply (mleaves_bind (fun g _ => g = None)).
      { apply (mleaves_bind (fun _ _ => True)); [apply mleaves_true|]. intros _ s'' _. apply mleaves_ret. reflexivity. }
      intros g s' ->. apply mleaves_ret. exact I.
    + (* [comment removed for export] *)
      assert (J10 : j < 10).
      { destruct HR as [HC HJ]. apply Z.leb_gt in EM. unfold MAX_INPUT in EM. rewrite HC in EM.
        destruct (Z_lt_dec j 10) as [L|L]; [exact L|]. exfalso. assert (j = 10) by lia. subst j. cbn in EM. lia. }
      apply (mleaves_bind (fun g s' => match g with
                                       | None => True
                                       | Some st1 => RDI (j + 1) st1 /\ DK 1 s s' /\ rd_content st1 = rd_content st end)).
      { apply (mleaves_bind (fun nb s' => DK 0 s s')); [exact (amalloc_M_dk _ s)|].
        intros nb s' D0. destruct nb as [nb'|].
        - apply (mleaves_bind (fun _ s'' => DK 1 s s'')).
          + eapply mleaves_mono; [| exact (afree_M_dk _ s')]. intros [] s'' D1. change 1 with (0 + 1). exact (DK_trans _ _ _ _ _ D0 D1).
          + intros [] s'' D1. apply mleaves_ret. unfold RDI. cbn [rd_cap rd_content]. split; [| split; [exact D1| reflexivity]].
            destruct HR as [HC HJ]. split; [| lia]. rewrite HC. replace (16 + (j + 1)) with (Z.succ (16 + j)) by lia.
            rewrite Z.pow_succ_r by lia. lia.
        - apply (mleaves_bind (fun _ _ => True)); [apply mleaves_true|]. intros _ s'' _. apply mleaves_ret. exact I. }
      intros g s1 Hg. destruct g as [st1|]; [| apply mleaves_ret; exact I].
      destruct Hg as (HR1 & D1 & _).
      apply (rd_read_part_dk fd path rs j (j + 1) (zlength (rd_content st)) st1 s s1 HR1); [lia| replace (j + 1 - j) with 1 by lia; exact D1].
  - (* [comment removed for export] *)
    apply (mleaves_bind (fun g s' => g = Some st /\ s' = s)); [apply mleaves_ret; split; reflexivity|].
    intros g s1 [-> ->].
    apply (rd_read_part_dk fd path rs j j (zlength (rd_content st)) st s s HR); [destruct HR; lia| replace (j - j) with 0 by lia; apply DK_refl].
Qed.

(* [comment removed for export] *)
Lemma loop_dk : forall (n : nat) fd path rs j (st : rd_st (ptr := AsanCtrl.aptr)) s,
  RDI j st ->
  mleaves (fun r s' => match r with RdDone _ _ => DK (10 - j) s s' | RdExit => True end)
    (mloop n (read_loop_body ioS amalloc_M afree_M rs fd path) st) s.
Proof.
  induction n as [|n IH]; intros fd path rs j st s HR; cbn [mloop]; [apply mleaves_unr|].
  eapply mleaves_bind; [exact (body_dk fd path rs j st s HR)|].
  intros r s' HB. destruct r as [st'|[|b c]]; cbn [BODYP] in HB.
  - destruct HB as (j' & HR' & Hj & D).
    eapply mleaves_mono; [| exact (IH fd path rs j' st' s' HR')].
    intros [|b c] s'' H; [exact I|]. replace (10 - j) with ((j' - j) + (10 - j')) by lia. exact (DK_trans _ _ _ _ _ D H).
  - apply mleaves_ret. exact I.
  - destruct HB as (j' & Hj & D). apply mleaves_ret. eapply DK_le; [| exact D]. lia.
Qed.

(* [comment removed for export] *)
Theorem read_all_dk : forall rs path s,
  mleaves (fun r s' => match r with RdDone _ _ => DK 10 s s' | RdExit => True end) (read_all ioS amalloc_M afree_M rs path) s.
Proof.
  intros rs path s. unfold read_all.
  apply (mleaves_bind (fun r s' => s' = s)); [apply mleaves_msys; reflexivity|].
  intros r s' ->. destruct r as [e|fd].
  - apply (mleaves_bind (fun _ _ => True)); [apply mleaves_true|]. intros _ s'' _. apply mleaves_ret. exact I.
  - apply (mleaves_bind (fun b s' => DK 0 s s')); [exact (amalloc_M_dk _ s)|].
    intros b s1 D0. destruct b as [buf|].
    + apply (mleaves_bind (fun res s2 => match res with RdDone _ _ => DK 10 s1 s2 | RdExit => True end)).
      { eapply mleaves_mono; [| exact (loop_dk READ_FUEL fd path rs 0 (mkRd buf 65536 []) s1 ltac:(split; [reflexivity| lia]))].
        intros [|b c] s2 H; [exact I| exact H]. }
      intros res s2 Hres. destruct res as [|buf' content]; [apply mleaves_ret; exact I|].
      apply (mleaves_bind (fun _ s3 => s3 = s2)); [apply mleaves_msys; reflexivity|].
      intros _ s3 ->. apply mleaves_ret. change 10 with (0 + 10). exact (DK_trans _ _ _ _ _ D0 Hres).
    + apply (mleaves_bind (fun _ _ => True)); [apply mleaves_true|]. intros _ s'' _. apply mleaves_ret. exact I.
Qed.

End CANSEC1.
