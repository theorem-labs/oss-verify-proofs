(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad STree Stdio HarnessU Adapter Driver ProgA
  AsanCtrl AsanCtrlProps AsanEmbed AsanInv AsanTotal SizeHist AsanProgDeps AsanOK RSimProg MI_Inv LB_Inv LB_Sum.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import Keeps.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AProto ATsafeCore ATsafeEv ATsafeAlloc ATsafeOps ATsafeProg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tall_True : forall {R} (t : itree node (exc R)), tall (fun _ => True) t.
Proof. induction t as [[|r]|n k IH]; cbn; auto. Qed.

Lemma keeps_alift : forall {B R} (f : APS -> B) (t : AM R), keeps f (alift t).
Proof.
  intros B R f t s. unfold alift. eapply tall_ebind; [apply tall_True|]. intros r _. cbn. reflexivity.
Qed.

Lemma keeps_cl_malloc : forall n, keeps aps_cl (amalloc_M n).
Proof.
  intros n. unfold amalloc_M. apply keeps_getk. intros s0.
  apply keeps_bind; [apply keeps_alift|]. intros x.
  apply keeps_bind; [apply keeps_upd; intros s; reflexivity|]. intros _. apply keeps_ret.
Qed.

Lemma keeps_cl_free : forall p, keeps aps_cl (afree_M p).
Proof.
  intros p. unfold afree_M. apply keeps_getk. intros s0.
  apply keeps_bind; [apply keeps_alift|]. intros x. apply keeps_upd. intros s; reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Client.
Variable NMAX : nat.
Variables SB PA : Z.
Variable Abase : alw.
Local Notation NMAXZ := (Z.of_nat NMAX).
Hypothesis HLIM : NLK0 + NMAXZ * 4096 <= LIMIT.
Hypothesis ABASE_SH : forall z',
  (shad SB <= z' < shad (SB + K_SPACE_SIZE) \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> Abase (page_base_of z').
Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Local Notation TSM := (TSM NMAX (St:=APS)).
Local Notation JJ := (JJ NMAX SB PA Abase).

(* [comment removed for export] *)
Definition clbA (s : APS) : list (AsanCtrl.aptr * Z) :=
  match aps_cl s with Some q => [(q, CLIENT_VEC_BYTES)] | None => [] end.

Definition JC (X : list (AsanCtrl.aptr * Z)) (v : Z) : preT (St:=APS) :=
  fun RNG A s mo => JJ (clbA s ++ X) v RNG A s mo.

Lemma length_clbA : forall s, (length (clbA s) <= 1)%nat.
Proof. intros s. unfold clbA. destruct (aps_cl s); cbn; lia. Qed.

Lemma JC_acct : forall Y v RNG A s mo, JC Y v RNG A s mo -> acct_ok NMAX RNG A mo.
Proof. intros Y v RNG A s mo H. exact (JJ_acct NMAX SB PA Abase HLIM _ _ _ _ _ _ H). Qed.
Lemma JC_perm : forall Y Y' v RNG A s mo, Permutation Y Y' -> JC Y v RNG A s mo -> JC Y' v RNG A s mo.
Proof. intros Y Y' v RNG A s mo HP H. eapply (JJ_perm NMAX SB PA Abase); [| exact H]. apply Permutation_app_head. exact HP. Qed.
Lemma JC_credit : forall Y v v' RNG A s mo, 0 <= v' <= v -> JC Y v RNG A s mo -> JC Y v' RNG A s mo.
Proof. intros Y v v' RNG A s mo Hv H. exact (JJ_credit NMAX SB PA Abase _ _ _ _ _ _ _ Hv H). Qed.
Lemma JC_nonneg : forall Y v RNG A s mo, JC Y v RNG A s mo -> 0 <= v.
Proof. intros Y v RNG A s mo (_ & _ & _ & _ & _ & Hv & _). exact Hv. Qed.
Lemma JC_io : forall n Y v RNG A s mo rsp mo' evs, io_node n -> nstep n mo rsp mo' evs -> JC Y v RNG A s mo -> JC Y v RNG A s mo'.
Proof. intros n Y v RNG A s mo rsp mo' evs Hio Hst H. exact (JJ_io NMAX SB PA Abase HSB HPA n _ _ _ _ _ _ _ _ _ Hio Hst H). Qed.
Lemma JC_so : forall Y v RNG A s mo w, JC Y v RNG A s mo -> JC Y v RNG A (aset_so w s) mo.
Proof. intros Y v RNG A s mo w H. unfold JC. change (clbA (aset_so w s)) with (clbA s). exact (JJ_so NMAX SB PA Abase _ _ _ _ _ _ w H). Qed.

Lemma HISTOK_amb3 n (L : list Z) : (length L <= 3)%nat -> HISTOK (n :: L).
Proof. intros HL. apply (HISTOK_amb n [] L); [apply Forall_nil| unfold BCs, zsum; cbn; unfold HB; lia| unfold N4s, N24s, zcount, zlen; cbn; lia| exact HL]. Qed.

(* [comment removed for export] *)
Lemma TSM_keeps_cl : forall {X} (P : preT (St:=APS)) (m : M APS X) (Q : postM (St:=APS) X) (c : option AsanCtrl.aptr),
  TSM P m Q -> keeps aps_cl m ->
  TSM (fun RNG A s mo => P RNG A s mo /\ aps_cl s = c) m (fun x RNG A s mo => Q x RNG A s mo /\ aps_cl s = c).
Proof.
  intros X P m Q c H HK RNG A s mo [Hp Hc]. unfold MQ.
  eapply TS_mono; [eapply (TS_tall NMAX); [apply (H _ _ _ _ Hp)| apply (HK s)]|].
  intros [|[x s']] RNG' A' mo' _ HQ; cbn in HQ |- *; [exact I|]. destruct HQ as [HQ E]. split; [exact HQ| congruence].
Qed.

(* [comment removed for export] *)
Lemma UC_malloc : forall Y v n, 0 <= n <= REQMAX -> (length Y <= 2)%nat -> HISTOK (n :: map snd Y) ->
  TSM (fun RNG A s mo => JC Y v RNG A s mo /\ n <= v) (amalloc_M n)
      (fun r RNG A s mo => exists q, r = Some q /\ JC ((q, n) :: Y) (v - n) RNG A s mo /\ n < 2^63).
Proof.
  intros Y v n Hn HL _. intros RNG A s mo [HJ Hnv].
  pose proof (TSM_keeps_cl (fun RNG A s' mo => JJ (clbA s ++ Y) v RNG A s' mo /\ n <= v) (amalloc_M n) _ (aps_cl s)
                (U_malloc NMAX SB PA Abase HLIM ABASE_SH (clbA s ++ Y) v n Hn
                   ltac:(apply HISTOK_amb3; rewrite length_map, length_app; pose proof (length_clbA s); lia))
                (keeps_cl_malloc n)) as H.
  eapply TS_mono; [apply (H RNG A s mo); split; [split; [exact HJ| exact Hnv]| reflexivity]|].
  intros [|[r s']] RNG' A' mo' _ HQ; cbn in HQ |- *; [exact I|].
  destruct HQ as [(q & -> & HJ' & Hlt) E]. exists q. split; [reflexivity|]. split; [| exact Hlt].
  unfold JC. assert (EC : clbA s' = clbA s) by (unfold clbA; rewrite E; reflexivity). rewrite EC.
  eapply (JJ_perm NMAX SB PA Abase); [| exact HJ']. apply Permutation_middle.
Qed.

Lemma UC_free : forall Y v p n, TSM (JC ((p, n) :: Y) v) (afree_M p) (fun _ => JC Y v).
Proof.
  intros Y v p n RNG A s mo HJ.
  pose proof (TSM_keeps_cl (JJ ((p, n) :: clbA s ++ Y) v) (afree_M p) _ (aps_cl s)
                (U_free NMAX SB PA Abase HLIM ABASE_SH (clbA s ++ Y) v p n) (keeps_cl_free p)) as H.
  eapply TS_mono; [apply (H RNG A s mo); split; [| reflexivity]|].
  - eapply (JJ_perm NMAX SB PA Abase); [| exact HJ]. apply Permutation_sym, Permutation_middle.
  - intros [|[r s']] RNG' A' mo' _ HQ; cbn in HQ |- *; [exact I|]. destruct HQ as [HJ' E].
    unfold JC. assert (EC : clbA s' = clbA s) by (unfold clbA; rewrite E; reflexivity). rewrite EC. exact HJ'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation cinitA := (HarnessU.client_init amalloc_M (new_handlerA AAllocAsan) aps_cl aset_cl).

Lemma cinit_some : forall s q, aps_cl s = Some q -> cinitA s = mret tt s.
Proof. intros s q H. unfold HarnessU.client_init, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
Lemma cinit_none : forall s, aps_cl s = None ->
  cinitA s = (p <- HarnessU.opnew amalloc_M (new_handlerA AAllocAsan) CLIENT_VEC_BYTES ;; mupd (aset_cl (Some p))) s.
Proof. intros s H. unfold HarnessU.client_init, mbind, mget. cbn. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma opnew8_ok : forall Y v, (length Y <= 3)%nat -> CLIENT_VEC_BYTES <= v ->
  TSM (fun RNG A s mo => JJ Y v RNG A s mo /\ aps_cl s = None)
      (HarnessU.opnew amalloc_M (new_handlerA AAllocAsan) CLIENT_VEC_BYTES)
      (fun p RNG A s mo => JJ ((p, CLIENT_VEC_BYTES) :: Y) (v - CLIENT_VEC_BYTES) RNG A s mo /\ aps_cl s = None).
Proof.
  intros Y v HL Hv. unfold HarnessU.opnew. change (CLIENT_VEC_BYTES =? 0) with false. cbn iota.
  eapply TSM_bind'.
  - eapply TSM_pre; [apply (TSM_keeps_cl _ _ _ None (U_malloc NMAX SB PA Abase HLIM ABASE_SH Y v CLIENT_VEC_BYTES
                               ltac:(unfold CLIENT_VEC_BYTES, REQMAX; lia) ltac:(apply HISTOK_amb3; rewrite length_map; exact HL)) (keeps_cl_malloc _))|].
    intros RNG A s mo [HJ E]. split; [split; [exact HJ| exact Hv]| exact E].
  - intros [q|]; cbv beta.
    + apply TSM_ret. intros RNG A s mo [(q' & Eq & HJ & _) E]. injection Eq as <-.
      split; [exact (JJ_acct NMAX SB PA Abase HLIM _ _ _ _ _ _ HJ)|]. split; [exact HJ| exact E].
    + eapply TSM_pre; [apply TSM_false|]. intros RNG A s mo [(q' & Eq & _) _]. discriminate Eq.
Qed.

Lemma UC_cinit : forall X v, (length X <= 2)%nat -> CLIENT_VEC_BYTES <= v ->
  TSM (JC X v) cinitA (fun _ => JC X (v - CLIENT_VEC_BYTES)).
Proof.
  intros X v HL Hv RNG A s mo HJ. destruct (aps_cl s) as [q|] eqn:E.
  - rewrite (cinit_some s q E). cbn. split; [exact (JC_acct _ _ _ _ _ _ HJ)|]. cbn.
    eapply JC_credit; [| exact HJ]. pose proof (JC_nonneg _ _ _ _ _ _ HJ). unfold CLIENT_VEC_BYTES in *. lia.
  - rewrite (cinit_none s E).
    assert (HJ0 : JJ X v RNG A s mo) by (unfold JC, clbA in HJ; rewrite E in HJ; exact HJ).
    refine (TSM_bind' NMAX _ _ _ _ _ (opnew8_ok X v ltac:(lia) Hv) _ RNG A s mo (conj HJ0 E)).
    intros p. eapply TSM_post; [apply TSM_upd; intros ? ? ? ? [HJ' _]; exact (JJ_acct NMAX SB PA Abase HLIM _ _ _ _ _ _ HJ')|].
    intros [] RNG' A' s'' mo' _ (s' & -> & HJ' & E').
    unfold JC, clbA. destruct s' as [st so rv tp cl]. cbn [aps_cl aset_cl app] in *. subst cl. exact HJ'.
Qed.

(* [comment removed for export] *)
Lemma UC_fuzz : forall X v data, (length X <= 2)%nat -> zlength data <= MAX_INPUT -> FUZZ_COST <= v ->
  TSM (JC X v) (fuzz_oneA AAllocAsan data) (fun _ => JC X (v - FUZZ_COST)).
Proof.
  intros X v data HL _ Hv. unfold fuzz_oneA, HarnessU.fuzz_one. cbn [amalloc a_cl a_set_cl AAllocAsan].
  eapply TSM_bind'; [apply (UC_cinit X v HL); unfold FUZZ_COST, CLIENT_VEC_BYTES in *; lia|]. intros [].
  apply TSM_ret. intros RNG A s mo HJ. split; [exact (JC_acct _ _ _ _ _ _ HJ)|].
  eapply JC_credit; [| exact HJ]. unfold FUZZ_COST, CLIENT_VEC_BYTES in *. lia.
Qed.

Local Notation cexitA := (HarnessU.client_exit afree_M aps_cl aset_cl).

Lemma cexit_none : forall s, aps_cl s = None -> cexitA s = mret tt s.
Proof. intros s H. unfold HarnessU.client_exit, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
Lemma cexit_some : forall s q, aps_cl s = Some q -> cexitA s = (HarnessU.opdelete afree_M q ;;; mupd (aset_cl None)) s.
Proof. intros s q H. unfold HarnessU.client_exit, mbind, mget. cbn. rewrite H. reflexivity. Qed.

Lemma UC_cexit : forall X v, TSM (JC X v) (client_exitA AAllocAsan) (fun _ => JC X v).
Proof.
  intros X v RNG A s mo HJ. change (client_exitA AAllocAsan) with cexitA. destruct (aps_cl s) as [q|] eqn:E.
  - rewrite (cexit_some s q E).
    assert (HJ0 : JJ ((q, CLIENT_VEC_BYTES) :: X) v RNG A s mo) by (unfold JC, clbA in HJ; rewrite E in HJ; exact HJ).
    refine (TSM_bind' NMAX _ _ _ _ _ (U_free NMAX SB PA Abase HLIM ABASE_SH X v q CLIENT_VEC_BYTES) _ RNG A s mo HJ0).
    intros []. eapply TSM_post; [apply TSM_upd; intros ? ? ? ? HJ'; exact (JJ_acct NMAX SB PA Abase HLIM _ _ _ _ _ _ HJ')|].
    intros [] RNG' A' s'' mo' _ (s' & -> & HJ').
    unfold JC, clbA. destruct s' as [st so rv tp cl]. cbn [aps_cl aset_cl app] in *. exact HJ'.
  - rewrite (cexit_none s E). cbn. split; [exact (JC_acct _ _ _ _ _ _ HJ)|]. exact HJ.
Qed.

End Client.
End CANSEC1.
