(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* fuzz_reply, both ASan builds: copied from proofs/boost-beast/http_request/lib/As/AsIface.v:291-316 and from
   proofs/boost-beast/http_request/lib/As/AsTRList.v:137-207, both at origin/ossv/recipes 754c3cdb4cc (blobs
   unchanged at de305eb5587): the released trace-recording vocabulary.
   - AsIface.v:291-316: trace_ok, pf_ok, pf_shift, pf_ok_call, pf_ok_site, pf_ok_incl;
   - AsTRList.v:137-207: the boolean checks inb, list_eqb, inlb, prefixes_inb, trace_okb, pf_okb0, their soundness,
     trace_ok_of_incl, pf_ok_of_incl.
   Changes in this copy: the AsIface.v part is taken out of its Section (it uses neither HeapCeil nor the asr record;
   the trace list is already an argument); TR_laws (AsIface.v:318, the C++ operator new trace) is not copied, as
   this unit has no operator new; the donor proof of trace_okb_sound is a KReplay replay, so it is written again
   here, and the Scheme lines that only the replay used are dropped; Stdlib only, no image address, no LPS file.
   Shared by lib/A (asan) and lib/B (asan-ubsan). The per-image lists are lib/A/Prog/trace_list_a.v and
   lib/B/Prog/trace_list_b.v; the per-image wiring is lib/A/Prog/trace_rec_a.v and lib/B/Prog/trace_rec_b.v; the
   frame walk that records a trace is lib/AsTRRecWalk.v.

   PREMISE OF THE TRACE LISTS (not of this file's lemmas): the runtime option fast_unwind_on_malloc is 1, so the
   allocator wrappers record through the fast frame-pointer walk (UnwindFast), not libunwind. The start-up
   certificate states it as rt_fast_unwind, the generated lemma that sits next to asan_cf_cells in
   lib/{A,B}/AsanRT.v from the next start-up regeneration. *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.

(* A trace [pc0; t...] is allowed by the list TRS: pc0 is not one of the return addresses t, and every non-empty
   prefix of pc0 :: t is in TRS (so a walk cut at any depth gives an allowed trace). *)
Definition trace_ok (TRS : list (list Z)) (pc0 : Z) (t : list Z) : Prop :=
  ~ In pc0 t /\ forall j, (1 <= j)%nat -> In (firstn j (pc0 :: t)) TRS.

(* A function's table PF holds (pc0, return addresses up to the one in this function) for each trace whose walk
   reads its frame record; with the function's own return address ra and the frame records CH above it, every such
   trace is allowed. *)
Definition pf_ok (TRS : list (list Z)) (PF : list (Z * list Z)) (ra : Z) (CH : list (Z * Z)) : Prop :=
  Forall (fun pp : Z * list Z => trace_ok TRS (fst pp) (snd pp ++ ra :: map snd CH)) PF.
Definition pf_shift (site : Z) (PF : list (Z * list Z)) : list (Z * list Z) :=
  map (fun pp : Z * list Z => (fst pp, snd pp ++ [site])) PF.

(* From the caller f to the callee g at a call returning to site in f: g's chain is f's frame record (fpf, raf) on
   top of f's chain. *)
Lemma pf_ok_call : forall TRS PFf PFg raf fpf CHf site,
  pf_ok TRS PFf raf CHf -> incl (pf_shift site PFg) PFf -> pf_ok TRS PFg site ((fpf, raf) :: CHf).
Proof.
  intros TRS PFf PFg raf fpf CHf site OK INC. unfold pf_ok in *. apply Forall_forall. intros [pc0 p] IN. cbn.
  assert (IN' : In (pc0, p ++ [site]) PFf). { apply INC. unfold pf_shift. apply in_map_iff. exists (pc0, p). split; [reflexivity| exact IN]. }
  pose proof (proj1 (Forall_forall _ _) OK _ IN') as T. cbn in T. rewrite <- app_assoc in T. exact T.
Qed.
Lemma pf_ok_site : forall TRS PF ra CH pc0 p,
  pf_ok TRS PF ra CH -> In (pc0, p) PF -> trace_ok TRS pc0 (p ++ ra :: map snd CH).
Proof. intros TRS PF ra CH pc0 p OK IN. exact (proj1 (Forall_forall _ _) OK _ IN). Qed.
Lemma pf_ok_incl : forall TRS PF PF' ra CH, pf_ok TRS PF ra CH -> incl PF' PF -> pf_ok TRS PF' ra CH.
Proof. intros TRS PF PF' ra CH OK INC. apply Forall_forall. intros pp IN. exact (proj1 (Forall_forall _ _) OK _ (INC _ IN)). Qed.

(* Boolean checks, closed by vm_compute on a concrete list. *)
Fixpoint inb (x : Z) (l : list Z) : bool :=
  match l with [] => false | y :: l' => if Z.eqb x y then true else inb x l' end.
Fixpoint list_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb x y && list_eqb a' b'
  | _, _ => false
  end.
Fixpoint inlb (t : list Z) (L : list (list Z)) : bool :=
  match L with [] => false | u :: L' => if list_eqb t u then true else inlb t L' end.
(* every non-empty prefix of l, after acc, is in L *)
Fixpoint prefixes_inb (acc : list Z) (l : list Z) (L : list (list Z)) : bool :=
  match l with
  | [] => true
  | x :: l' => inlb (acc ++ [x]) L && prefixes_inb (acc ++ [x]) l' L
  end.
Definition trace_okb (L : list (list Z)) (pc0 : Z) (t : list Z) : bool :=
  negb (inb pc0 t) && prefixes_inb [] (pc0 :: t) L.
(* pf_ok with an empty chain above the function *)
Definition pf_okb0 (L : list (list Z)) (PF : list (Z * list Z)) (ra : Z) : bool :=
  forallb (fun pp : Z * list Z => trace_okb L (fst pp) (snd pp ++ [ra])) PF.

Lemma inb_false : forall x l, inb x l = false -> ~ In x l.
Proof.
  induction l as [|y l IH]; cbn; [tauto|]. destruct (Z.eqb_spec x y); [discriminate|]. intros H [E|K]; [congruence| exact (IH H K)].
Qed.
Lemma list_eqb_eq : forall a b, list_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [E R]. apply Z.eqb_eq in E. subst. f_equal. exact (IH _ R).
Qed.
Lemma inlb_In : forall t L, inlb t L = true -> In t L.
Proof.
  induction L as [|u L IH]; cbn; [discriminate|]. destruct (list_eqb t u) eqn:E.
  - intros _. left. symmetry. exact (list_eqb_eq _ _ E).
  - intros H. right. exact (IH H).
Qed.
Lemma prefixes_inb_sound : forall l acc L, prefixes_inb acc l L = true ->
  forall j, (1 <= j)%nat -> (j <= length l)%nat -> In (acc ++ firstn j l) L.
Proof.
  induction l as [|x l IH]; intros acc L H j Hj Hl; cbn in Hl; [lia|].
  cbn in H. apply andb_true_iff in H as [H1 H2].
  destruct j as [|j]; [lia|]. cbn [firstn]. destruct j as [|j'].
  - cbn [firstn]. exact (inlb_In _ _ H1).
  - replace (acc ++ x :: firstn (S j') l) with ((acc ++ [x]) ++ firstn (S j') l) by (rewrite <- app_assoc; reflexivity).
    apply (IH (acc ++ [x]) L H2); lia.
Qed.

(* Written again (the donor's proof is a replay): a prefix longer than the trace is the whole trace. *)
Lemma trace_okb_sound : forall L pc0 t, trace_okb L pc0 t = true -> trace_ok L pc0 t.
Proof.
  intros L pc0 t H. unfold trace_okb in H. apply andb_true_iff in H as [H1 H2]. split.
  - apply negb_true_iff in H1. exact (inb_false _ _ H1).
  - intros j Hj. destruct (Nat.le_gt_cases j (length (pc0 :: t))) as [Hl|Hl].
    + exact (prefixes_inb_sound (pc0 :: t) [] L H2 j Hj Hl).
    + rewrite firstn_all2 by lia.
      pose proof (prefixes_inb_sound (pc0 :: t) [] L H2 (length (pc0 :: t)) ltac:(cbn; lia) ltac:(lia)) as K.
      rewrite app_nil_l, firstn_all in K. exact K.
Qed.

Lemma pf_okb0_sound : forall L PF ra, pf_okb0 L PF ra = true -> pf_ok L PF ra [].
Proof.
  intros L PF ra H. unfold pf_okb0 in H. unfold pf_ok. apply Forall_forall. intros pp IN.
  pose proof (proj1 (forallb_forall _ _) H pp IN) as Hp. cbn in Hp. cbn [map]. exact (trace_okb_sound _ _ _ Hp).
Qed.

(* A fact about a sub-list holds for any list that contains it. *)
Lemma trace_ok_of_incl : forall L TRS pc0 t, incl L TRS -> trace_ok L pc0 t -> trace_ok TRS pc0 t.
Proof. intros L TRS pc0 t INC [NI OK]. split; [exact NI|]. intros j Hj. apply INC. exact (OK j Hj). Qed.
Lemma pf_ok_of_incl : forall L TRS PF ra CH, incl L TRS -> pf_ok L PF ra CH -> pf_ok TRS PF ra CH.
Proof.
  intros L TRS PF ra CH INC OK. unfold pf_ok in *. apply Forall_forall. intros pp IN.
  apply (trace_ok_of_incl L TRS); [exact INC|]. exact (proj1 (Forall_forall _ _) OK pp IN).
Qed.
