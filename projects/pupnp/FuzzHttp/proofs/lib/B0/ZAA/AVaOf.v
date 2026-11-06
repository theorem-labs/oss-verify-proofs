(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim PEnv APrimSpec2 APrimLem APrimQ APrimDealloc APrimCover ASec ASecD AQuar AQuarM
                        AHeap F_quar_E AQuarR AQuarP F_quar_R F_quar_DR F_quar_D F_quar_P ALedger ALinkPg ALinkVm ALink ALinkPrim ALinkFree
                        AHeap2 AHeapB AFreeL8 ALinkFreeIn.
Import ListNotations.
Open Scope Z_scope.

Definition aux_of (S : asec) : Z := se_nres S / 16384 * (131072 + 131072 / 8 + 2 * 4096).
Definition va_of (s : astB) : vabs :=
  mkVA (sum_mu (bs_prim s) + sum_mfa (bs_prim s)) (map cpair (se_chunks (bs_sec s))) (bs_nsec s) (aux_of (bs_sec s)).

Lemma va_of_linked : forall s, linked (va_of s) (bs_X s).
Proof. intros s. unfold linked, va_of, bs_X. cbn [va_chunks snd]. apply Permutation_refl. Qed.

Lemma recycle1_nres : forall X ch, se_nres (snd (recycle1 X ch)) = se_nres (snd X).
Proof. intros X ch. unfold recycle1. destruct (qc_kind ch); reflexivity. Qed.
Lemma recycle_chunks_nres : forall chs X, se_nres (snd (recycle_chunks X chs)) = se_nres (snd X).
Proof. induction chs as [|ch chs IH]; intros X; [reflexivity|]. cbn [recycle_chunks]. rewrite IH. apply recycle1_nres. Qed.
Lemma dorecycle_nres : forall bs X, se_nres (snd (dorecycle X bs)) = se_nres (snd X).
Proof.
  induction bs as [|b bs IH]; intros X; [reflexivity|]. cbn [dorecycle]. rewrite IH. unfold recycle_batch. cbv zeta. cbn [snd]. apply recycle_chunks_nres.
Qed.

Section VA.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).

#[using="Type"] Theorem free_va_of : forall s LB m ch n l1 l2 H' hs' total',
  RHEAP_B AL E s LB m -> bs_live s = l1 ++ (ch, n) :: l2 ->
  let P := bs_prim s in let glob := q_glob (bs_quar s) in let loc := q_loc (bs_quar s) in
  let X1 := (fst (enq_prim P loc), bs_sec s) in let todo := put_todo P glob loc ch in
  let X' := dorecycle X1 todo in
  let s' := mkASB H' (bs_pages s) (fst X') (snd X') (mkAQ (put_loc P loc ch) (put_glob P glob loc ch)) hs' total' (bs_nsec s) (l1 ++ l2) (bs_depot0 s) in
  let v' := va_dorecycle (va_enq (va_of s) P loc) X1 todo in
  va_prim v' = va_prim (va_of s') /\ Permutation (va_chunks v') (va_chunks (va_of s')) /\ va_nsec v' = va_nsec (va_of s') /\ va_aux v' = va_aux (va_of s').
Proof.
  intros s LB m ch n l1 l2 H' hs' total' HR EL. cbv zeta.
  destruct (free_link_inputs AL E s LB m ch n l1 l2 (va_of s) HR EL (va_of_linked s)) as (_ & _ & _ & LK' & VB & EN & EA). cbv zeta in *.
  unfold va_base in VB. unfold va_of at 2 in VB. cbn [va_prim] in VB.
  unfold va_of at 2 4 6 8. cbn [va_prim va_chunks va_nsec va_aux bs_prim bs_sec bs_nsec].
  split; [lia|]. split; [exact LK'|]. split; [exact EN|]. rewrite EA. unfold va_of. cbn [va_aux]. unfold aux_of. rewrite dorecycle_nres. reflexivity.
Qed.

End VA.
