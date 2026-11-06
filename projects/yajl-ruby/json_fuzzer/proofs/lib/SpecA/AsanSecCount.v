(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanBudget AsanBudget2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section SC.
Variable E : aenv.

Definition is_secb (cm : chunkmeta) : bool := match cm_prim cm with None => true | Some _ => false end.
Definition is_allocb (cm : chunkmeta) : bool := match cm_state cm with CAllocated _ => true | _ => false end.

Lemma zlen_filter_sumZ : forall {A} (p : A -> bool) (l : list A), zlen (List.filter p l) = sumZ (fun x => if p x then 1 else 0) l.
Proof. intros A p l. unfold zlen. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (p x); cbn [length]; lia. Qed.

Lemma filter_map_comm : forall {A B} (p : B -> bool) (f : A -> B) (l : list A), List.filter p (map f l) = map f (List.filter (fun x => p (f x)) l).
Proof. intros A B p f l. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (p (f x)); cbn; rewrite IH; reflexivity. Qed.

(* [comment removed for export] *)
Lemma cover_count : forall secs (M : gmap Z chunkmeta), List.NoDup (map sc_map_beg secs) ->
  (forall sc, In sc secs -> exists cb cm, M !! cb = Some cm /\ cm_prim cm = None /\ cm_alloc_beg cm = sc_map_beg sc + kPageSize
                                         /\ sc_map_size sc = map_size (cm_n cm)) ->
  zlen secs <= sumZ (fun p => if is_secb (snd p) then 1 else 0) (map_to_list M).
Proof.
  intros secs. induction secs as [|sc rest IH]; intros M ND COV.
  - unfold zlen. cbn [length Z.of_nat]. apply sumZ_nonneg. intros [cb cm] _. cbn [snd]. destruct (is_secb cm); lia.
  - destruct (COV sc ltac:(left; reflexivity)) as (cb & cm & H & PC & AB & MS).
    rewrite <- (sumZ_perm _ _ _ (map_to_list_delete M cb cm H)). cbn [sumZ snd]. unfold is_secb at 1. rewrite PC.
    inversion ND as [|x0 l0 NIN NDr X0]; subst.
    specialize (IH (delete cb M) NDr).
    assert (COV' : forall sc', In sc' rest -> exists cb' cm', delete cb M !! cb' = Some cm' /\ cm_prim cm' = None
                      /\ cm_alloc_beg cm' = sc_map_beg sc' + kPageSize /\ sc_map_size sc' = map_size (cm_n cm')).
    { intros sc' Hin. destruct (COV sc' ltac:(right; exact Hin)) as (cb' & cm' & H' & PC' & AB' & MS'). exists cb', cm'.
      split; [| auto]. rewrite lookup_delete_ne; [exact H'|]. intros ->. rewrite H in H'. injection H' as ->.
      apply NIN. apply in_map_iff. exists sc'. split; [unfold kPageSize in *; lia| exact Hin]. }
    specialize (IH COV'). unfold zlen in *. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Lemma sec_chunk_big : forall a cb cm, AWf E [] [] a -> as_chunks a !! cb = Some cm -> cm_prim cm = None -> 64512 < cm_n cm.
Proof.
  intros a cb cm WF H PC. destruct WF as (_ & _ & _ & [K1 _] & _). pose proof (K1 _ _ H) as (_ & HN & _ & PR & _).
  rewrite PC in PR. destruct PR as [PR _].
  destruct (Z.le_gt_cases (cm_n cm) 64512) as [LE|GT]; [| exact GT].
  pose proof (proj2 (from_primary_iff (cm_n cm) ltac:(lia)) LE). congruence.
Qed.

(* [comment removed for export] *)
Lemma alloc_sec_count : forall a, AWf E [] [] a ->
  sumZ (fun p => if is_secb (snd p) && is_allocb (snd p) then 1 else 0) (chunk_list a)
  <= zlen (List.filter (fun b => 64512 <? snd b) (live_blocks a)).
Proof.
  intros a WF. unfold live_blocks. rewrite filter_map_comm. unfold zlen. rewrite length_map. fold (zlen (List.filter (fun x => 64512 <? snd (cm_user_beg (snd x), cm_n (snd x))) (List.filter (fun p => match cm_state (snd p) with CAllocated _ => true | _ => false end) (chunk_list a)))).
  rewrite zlen_filter_sumZ. cbn [snd]. rewrite sumZ_filter.
  apply sumZ_le. intros [cb cm] Hin. cbn [snd]. unfold is_allocb.
  destruct (is_secb cm) eqn:SB; cbn [andb]; [| destruct (cm_state cm); [destruct (64512 <? cm_n cm)|]; lia].
  destruct (cm_state cm) eqn:ST; [| lia].
  apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
  unfold is_secb in SB. destruct (cm_prim cm) eqn:PC; [discriminate|].
  pose proof (sec_chunk_big a cb cm WF Hin PC) as BIG. replace (64512 <? cm_n cm) with true by (symmetry; apply Z.ltb_lt; exact BIG). lia.
Qed.

(* [comment removed for export] *)
Lemma quar_sec_count : forall a, AWf E [] [] a -> AQbound a ->
  64513 * sumZ (fun p => if is_secb (snd p) && negb (is_allocb (snd p)) then 1 else 0) (chunk_list a) <= kThreadQuarantineMax + kQuarantineMax.
Proof.
  intros a WF QB. pose proof (quarantine_sum E a WF QB) as QS.
  etransitivity; [| exact QS]. rewrite <- sumZ_scale. apply sumZ_le. intros [cb cm] Hin. cbn [snd]. unfold is_allocb.
  apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
  pose proof WF as (_ & _ & _ & [K1 _] & _). pose proof (K1 _ _ Hin) as (_ & HN & _).
  destruct (is_secb cm) eqn:SB; cbn [andb negb]; [| destruct (cm_state cm); lia].
  destruct (cm_state cm) eqn:ST; cbn [negb]; [lia|].
  unfold is_secb in SB. destruct (cm_prim cm) eqn:PC; [discriminate|].
  pose proof (sec_chunk_big a cb cm WF Hin PC). lia.
Qed.

Theorem n_chunks_bound : forall a, AWf E [] [] a -> AQbound a -> binv a ->
  n_chunks a <= zlen (List.filter (fun b => 64512 <? snd b) (live_blocks a)) + 4177.
Proof.
  intros a WF QB HBI. destruct HBI as (_ & _ & _ & B8 & B9 & _).
  pose proof (cover_count (as_sec a) (as_chunks a) B9 B8) as C1. fold (chunk_list a) in C1.
  pose proof (alloc_sec_count a WF) as C2. pose proof (quar_sec_count a WF QB) as C3.
  assert (SPLIT : sumZ (fun p => if is_secb (snd p) then 1 else 0) (chunk_list a)
                  = sumZ (fun p => if is_secb (snd p) && is_allocb (snd p) then 1 else 0) (chunk_list a)
                  + sumZ (fun p => if is_secb (snd p) && negb (is_allocb (snd p)) then 1 else 0) (chunk_list a)).
  { rewrite <- sumZ_add. apply sumZ_ext. intros [cb cm] _. cbn [snd]. destruct (is_secb cm), (is_allocb cm); reflexivity. }
  unfold n_chunks. fold (zlen (as_sec a)). unfold kThreadQuarantineMax, kQuarantineMax in C3. lia.
Qed.
End SC.
End RC__1.
