(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad MSafe MSafeP HarnessP Adapter Driver SjStage1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section TargetSafe.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).
Variable raw_free : ptr -> M St unit.
Variable new_handler : M St Empty_set.
Variable emit : Z -> M St unit.
Variable cl_get : St -> option ptr.
Variable cl_set : option ptr -> St -> St.
Variable ownc : option ptr -> list ptr -> assn St.

(* [comment removed for export] *)
Definition OPNEW_MAX : Z := 2^31.

Hypothesis Hm : forall c X n, 0 <= n ->
  mspec (ownc c X) (raw_malloc n) (fun r s mo => match r with Some p => ownc c (p :: X) s mo /\ n < 2^63 | None => ownc c X s mo end).
(* [comment removed for export] *)
Hypothesis HmS : forall c X n, 0 <= n <= OPNEW_MAX ->
  mspecP (ownc c X) (raw_malloc n) (fun r s mo => match r with Some p => ownc c (p :: X) s mo /\ n < 2^63 | None => False end).
Hypothesis Hf : forall c X p, mspec (ownc c (p :: X)) (raw_free p) (fun _ => ownc c X).
Hypothesis Hperm : forall c X Y s mo, Permutation X Y -> ownc c X s mo -> ownc c Y s mo.
Hypothesis Hemit : forall c X v, mspec (ownc c X) (emit v) (fun _ => ownc c X).
(* [comment removed for export] *)
Hypothesis Hcl : forall c X s mo, ownc c X s mo -> cl_get s = c.
Hypothesis Hset : forall c c' X s mo, ownc c X s mo -> ownc c' X (cl_set c' s) mo.

(* [comment removed for export] *)
Definition clb (c : option ptr) : list ptr := match c with Some p => [p] | None => [] end.
Definition own (X : list ptr) : assn St := fun s mo => exists c, ownc c (clb c ++ X) s mo.

Lemma own_perm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Proof. intros X Y s mo HP [c H]. exists c. eapply Hperm; [| exact H]. apply Permutation_app_head. exact HP. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma own_malloc : forall X n, 0 <= n ->
  mspec (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Proof.
  intros X n Hn. apply mspec_exI. intros c. eapply mspec_post; [apply (Hm c (clb c ++ X) n Hn)|].
  intros [p|] s mo; cbn beta iota.
  - intros [H H63]. split; [| exact H63]. exists c. eapply Hperm; [| exact H]. apply Permutation_middle.
  - intros H. exists c. exact H.
Qed.

Lemma own_mallocS : forall X n, 0 <= n <= OPNEW_MAX ->
  mspecP (own X) (raw_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => False end).
Proof.
  intros X n Hn. apply mspecP_exI. intros c. eapply mspecP_post; [apply (HmS c (clb c ++ X) n Hn)|].
  intros [p|] s mo; cbn beta iota; [| intros []].
  intros [H H63]. split; [| exact H63]. exists c. eapply Hperm; [| exact H]. apply Permutation_middle.
Qed.

Lemma own_free : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Proof.
  intros X p. apply mspec_exI. intros c. eapply mspec_conseq; [apply (Hf c (clb c ++ X) p)| |].
  - intros s mo H. eapply Hperm; [| exact H]. apply Permutation_sym, Permutation_middle.
  - intros a s mo H. exists c. exact H.
Qed.

Lemma own_emit : forall X v, mspec (own X) (emit v) (fun _ => own X).
Proof. intros X v. apply mspec_exI. intros c. eapply mspec_post; [apply Hemit|]. intros a s mo H. exists c. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma opnew_spec_c : forall c X n, 0 <= n <= OPNEW_MAX ->
  mspecP (ownc c X) (opnew raw_malloc new_handler n) (fun p => ownc c (p :: X)).
Proof.
  intros c X n Hn. unfold opnew.
  eapply mspecP_bind; [apply HmS; unfold OPNEW_MAX in *; destruct (n =? 0); lia|].
  intros [p|]; cbn beta iota.
  - apply mspecP_pure. intros _. apply mspecP_ret. intros s mo H; exact H.
  - intros s mo [].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma psizes_ok : forall len, 0 <= len <= MAX_INPUT ->
  0 <= SB_BYTES len <= OPNEW_MAX /\ 0 <= TAPE_BYTES len <= OPNEW_MAX /\ 0 <= IMPL_BYTES <= OPNEW_MAX /\ 0 <= SIDX_BYTES len <= OPNEW_MAX
  /\ 0 <= OC_BYTES <= OPNEW_MAX /\ 0 <= ISARR_BYTES <= OPNEW_MAX /\ 0 <= COPY_BYTES len <= OPNEW_MAX.
Proof.
  intros len Hl. pose proof (sizes_pos len ltac:(lia)) as P. pose proof (sizes_upper len ltac:(lia)) as U.
  assert (C : CAP len <= MAX_INPUT) by (unfold CAP, MAX_INPUT in *; lia).
  pose proof (Z.div_le_upper_bound (CAP len) 3 MAX_INPUT ltac:(lia) ltac:(unfold MAX_INPUT in *; lia)).
  unfold OPNEW_MAX, MAX_INPUT in *. lia.
Qed.

Lemma root_copy_ok : forall data n, root_number_alloc data = Some n -> zlength data <= MAX_INPUT -> 0 <= n <= OPNEW_MAX.
Proof.
  intros data n H Hl. pose proof (root_number_alloc_bound data n H) as B. unfold zlength in Hl. unfold OPNEW_MAX, MAX_INPUT in *. lia.
Qed.

Lemma opdelete_spec_c : forall c X p, mspecP (ownc c (p :: X)) (opdelete raw_free p) (fun _ => ownc c X).
Proof. intros c X p. unfold opdelete. apply mspec_mspecP. apply Hf. Qed.

(* [comment removed for export] *)
Definition pbl (b : ptr * ptr * (ptr * ptr * ptr * ptr) * option ptr) : list ptr :=
  let '(sb, tp, (im, si, oc, ia), lb) := b in
  match lb with Some p => [p] | None => [] end ++ [sb; tp; ia; oc; si; im].

Lemma root_copy_spec_c : forall c X data, zlength data <= MAX_INPUT ->
  mspecP (ownc c X) (root_copy raw_malloc raw_free new_handler data) (fun _ => ownc c X).
Proof.
  intros c X data Hl. unfold root_copy.
  destruct (root_number_alloc data) as [n|] eqn:E.
  - eapply mspecP_bind; [apply opnew_spec_c; exact (root_copy_ok data n E Hl)|]. intros q. apply opdelete_spec_c.
  - apply mspecP_ret. intros s mo H; exact H.
Qed.

(* [comment removed for export] *)
Lemma pbl_perm : forall (sb tp im si oc ia : ptr) (X : list ptr),
  Permutation ([ia; oc; si; im; tp; sb] ++ X) ([sb; tp; ia; oc; si; im] ++ X).
Proof.
  intros sb tp im si oc ia X. apply Permutation_app_tail.
  change [sb; tp; ia; oc; si; im] with ([sb; tp] ++ [ia; oc; si; im]). change [ia; oc; si; im; tp; sb] with ([ia; oc; si; im] ++ [tp; sb]).
  eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app_tail. apply perm_swap.
Qed.

Lemma parse_into_doc_spec_c : forall c X data, zlength data <= MAX_INPUT ->
  mspecP (ownc c X) (parse_into_doc raw_malloc raw_free new_handler data) (fun b => ownc c (pbl b ++ X)).
Proof.
  intros c X data Hl. assert (H0 : 0 <= zlength data) by (unfold zlength; lia).
  destruct (psizes_ok (zlength data) ltac:(lia)) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  unfold parse_into_doc. cbv zeta.
  eapply mspecP_bind with (Q1 := fun dd => ownc c (snd dd :: fst dd :: X)).
  { unfold doc_allocate. eapply mspecP_bind; [apply opnew_spec_c; exact S1|]. intros sb.
    eapply mspecP_bind; [apply opnew_spec_c; exact S2|]. intros tp. apply mspecP_ret. intros s mo H; exact H. }
  intros [sb tp]. cbn [fst snd].
  eapply mspecP_bind with (Q1 := fun ii => match ii with (im, si, oc, ia) => ownc c (ia :: oc :: si :: im :: tp :: sb :: X) end).
  { unfold impl_create, impl_set_capacity, impl_set_max_depth.
    eapply mspecP_bind; [apply opnew_spec_c; exact S3|]. intros im.
    eapply mspecP_bind; [apply opnew_spec_c; exact S4|]. intros si.
    eapply mspecP_bind with (Q1 := fun oi => match oi with (oc, ia) => ownc c (ia :: oc :: si :: im :: tp :: sb :: X) end).
    - eapply mspecP_bind; [apply opnew_spec_c; exact S5|]. intros oc.
      eapply mspecP_bind; [apply opnew_spec_c; exact S6|]. intros ia. apply mspecP_ret. intros s mo H; exact H.
    - intros [oc ia]. cbv beta iota. apply mspecP_ret. intros s mo H; exact H. }
  intros [[[im si] oc] ia]. cbv beta iota.
  eapply mspecP_bind with (Q1 := fun lb => ownc c (match lb with Some p => [p] | None => [] end ++ [ia; oc; si; im; tp; sb] ++ X)).
  { unfold padded_alloc. destruct (copy_made (zlength data)) eqn:CM.
    - eapply mspecP_bind; [apply opnew_spec_c; exact S7|]. intros p. apply mspecP_ret. intros s mo H. exact H.
    - apply mspecP_ret. intros s mo H. exact H. }
  intros lb.
  eapply mspecP_seq with (R := ownc c (match lb with Some p => [p] | None => [] end ++ [ia; oc; si; im; tp; sb] ++ X)).
  - destruct lb as [p|]; unfold parse_impl.
    + apply root_copy_spec_c; exact Hl.
    + apply mspecP_ret. intros s mo H. exact H.
  - intros _. apply mspecP_ret. intros s mo H. unfold pbl. rewrite <- app_assoc.
    eapply Hperm; [| exact H]. apply Permutation_app_head. apply pbl_perm.
Qed.

Lemma parser_dtor_spec_c : forall c X b, mspecP (ownc c (pbl b ++ X)) (parser_dtor raw_free b) (fun _ => ownc c X).
Proof.
  intros c X [[[sb tp] [[[im si] oc] ia]] lb]. unfold parser_dtor, pbl. cbv beta iota.
  eapply mspecP_seq with (R := ownc c ([sb; tp; ia; oc; si; im] ++ X)).
  { destruct lb as [p|]; [apply opdelete_spec_c| apply mspecP_ret; intros s mo H; exact H]. }
  intros _. eapply mspecP_seq with (R := ownc c ([ia; oc; si; im] ++ X)).
  { unfold doc_dtor. eapply mspecP_seq; [apply opdelete_spec_c|]. intros _. apply opdelete_spec_c. }
  intros _. unfold impl_dtor.
  eapply mspecP_seq; [apply opdelete_spec_c|]. intros _.
  eapply mspecP_seq; [apply opdelete_spec_c|]. intros _.
  eapply mspecP_seq; [apply opdelete_spec_c|]. intros _.
  apply opdelete_spec_c.
Qed.

Lemma fuzz_one_spec_c : forall c X data, zlength data <= MAX_INPUT ->
  mspecP (ownc c X) (fuzz_one raw_malloc raw_free new_handler data) (fun _ => ownc c X).
Proof.
  intros c X data Hl. unfold fuzz_one.
  eapply mspecP_bind; [apply parse_into_doc_spec_c; exact Hl|]. intros b.
  eapply mspecP_seq; [apply parser_dtor_spec_c|]. intros _. apply mspecP_ret. intros s mo H; exact H.
Qed.

Lemma fuzz_one_spec : forall X data, zlength data <= MAX_INPUT ->
  mspecP (own X) (fuzz_one raw_malloc raw_free new_handler data) (fun _ => own X).
Proof.
  intros X data Hl. apply mspecP_exI. intros c.
  eapply mspecP_post; [apply fuzz_one_spec_c; exact Hl|]. intros a s mo H. exists c. exact H.
Qed.

Lemma client_exit_spec : forall X, mspec (own X) client_exit (fun _ => own X).
Proof. intros X. unfold client_exit. apply mspec_ret. intros s mo H; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_calls_spec : forall X n payload rc, zlength payload <= MAX_INPUT ->
  mspecP (own X) (run_calls (fuzz_one raw_malloc raw_free new_handler) emit n payload rc) (fun _ => own X).
Proof.
  intros X n. induction n as [|n IH]; intros payload rc Hl; cbn [run_calls].
  - apply mspecP_ret. intros s mo H; exact H.
  - eapply mspecP_seq; [apply fuzz_one_spec; exact Hl|]. intros rc'.
    eapply mspecP_seq; [apply mspec_mspecP; apply own_emit|]. intros _. apply IH. exact Hl.
Qed.

Theorem target_run_spec : forall X cfg payload, zlength payload <= MAX_INPUT ->
  mspecP (own X) (target_run raw_malloc raw_free (fuzz_one raw_malloc raw_free new_handler) emit cfg payload) (fun _ => own X).
Proof.
  intros X cfg payload Hlen. unfold target_run.
  eapply mspecP_bind with (Q1 := fun a s mo => match a with
                                               | None => own X s mo
                                               | Some None => own X s mo
                                               | Some (Some p) => own (p :: X) s mo
                                               end).
  { apply mspecP_if; intros _; [apply mspecP_ret; intros s mo H; exact H|].
    eapply mspecP_bind; [apply mspec_mspecP; apply own_malloc; unfold zlength; lia|]. intros [p|]; apply mspecP_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply mspecP_seq; [apply run_calls_spec; exact Hlen|]. intros rc. eapply mspecP_seq; [apply mspec_mspecP; apply own_free|]. intros _. apply mspecP_ret. intros s mo H; exact H.
  - eapply mspecP_seq; [apply run_calls_spec; exact Hlen|]. intros rc. eapply mspecP_seq; [apply mspecP_ret; intros s mo H; exact H|]. intros _. apply mspecP_ret. intros s mo H; exact H.
  - apply mspecP_ret. intros s mo H; exact H.
Qed.

End TargetSafe.
