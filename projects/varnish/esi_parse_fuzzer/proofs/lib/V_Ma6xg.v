(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record mentry : Type := ME {
  me_ptr : Z;            (* [comment removed for export] *)
  me_str : list byte;    (* [comment removed for export] *)
  me_svar : Z;           (* [comment removed for export] *)
  me_sval : Z            (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Fixpoint mtab_cells (es : list mentry) : list cell :=
  match es with
  | [] => []
  | e :: es' => C8 (Z_to_bv 64 (me_ptr e)) :: C8 (Z_to_bv 64 (me_svar e)) :: mtab_cells es'
  end.

Lemma mtab_cells_size : forall es, cells_size (mtab_cells es) = (16 * length es)%nat.
Proof. induction es; cbn; lia. Qed.

(* [comment removed for export] *)
Fixpoint mtab_wf (es : list mentry) : Prop :=
  match es with
  | [] => False
  | [e] => me_ptr e = 0 /\ me_str e = []
  | e :: es' => 0 < me_ptr e < 2^64 /\ (1 <= length (me_str e) <= 8)%nat /\ ~ In (Z_to_bv 8 0) (me_str e) /\ mtab_wf es'
  end.

(* [comment removed for export] *)
Fixpoint is_prefixb (s inp : list byte) : bool :=
  match s, inp with
  | [], _ => true
  | _ :: _, [] => false
  | c :: s', d :: inp' => bv_eqb c d && is_prefixb s' inp'
  end.

(* [comment removed for export] *)
Fixpoint runs_outb (s inp : list byte) : bool :=
  match s, inp with
  | [], _ => false
  | _ :: _, [] => true
  | c :: s', d :: inp' => bv_eqb c d && runs_outb s' inp'
  end.

Fixpoint vm_find (es : list mentry) (inp : list byte) : option nat :=
  match es with
  | [] => Some 0%nat   (* [comment removed for export] *)
  | e :: es' =>
      if me_ptr e =? 0 then Some 0%nat
      else if is_prefixb (me_str e) inp then Some 0%nat
      else if runs_outb (me_str e) inp then None
      else option_map S (vm_find es' inp)
  end.

Lemma vm_find_bound : forall es inp i, mtab_wf es -> vm_find es inp = Some i -> (i < length es)%nat.
Proof.
  induction es as [|e es IH]; intros inp i WF H; cbn in *; [contradiction|].
  destruct es as [|e2 es2].
  - destruct WF as [E0 _]. rewrite E0 in H. cbn in H. inversion H. cbn. lia.
  - (first [ dand4 WF as Hp Hl Hn WF' | destruct WF as (Hp & Hl & Hn & WF') ]).
    destruct (me_ptr e =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|].
    destruct (is_prefixb (me_str e) inp); [inversion H; cbn; lia|].
    destruct (runs_outb (me_str e) inp); [discriminate|].
    destruct (vm_find (e2 :: es2) inp) as [j|] eqn:E; [|discriminate].
    cbn in H. inversion H. subst. specialize (IH inp j WF' E). cbn in IH |- *. lia.
Qed.

(* [comment removed for export] *)
Lemma runs_outb_length : forall s inp, runs_outb s inp = true -> (length inp < length s)%nat.
Proof.
  induction s as [|c s IH]; intros [|d inp] H; cbn in *; try discriminate; [lia|].
  apply andb_prop in H as [_ H]. apply IH in H. lia.
Qed.

Lemma is_prefixb_length : forall s inp, is_prefixb s inp = true -> (length s <= length inp)%nat.
Proof.
  induction s as [|c s IH]; intros [|d inp] H; cbn in *; try discriminate; try lia.
  apply andb_prop in H as [_ H]. apply IH in H. lia.
Qed.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)

Lemma mtab_cell_at_skip : forall pre post k,
  cell_at (mtab_cells (pre ++ post)) (16 * length pre + k) = cell_at (mtab_cells post) k.
Proof.
  induction pre as [|e pre IH]; intros post k; [reflexivity|].
  cbn [app mtab_cells length]. cbn [cell_at csize].
  destruct (Nat.eqb_spec (16 * S (length pre) + k) 0); [lia|].
  destruct (Nat.ltb_spec0 (16 * S (length pre) + k) 8); [lia|].
  destruct (Nat.eqb_spec (16 * S (length pre) + k - 8) 0); [lia|].
  destruct (Nat.ltb_spec0 (16 * S (length pre) + k - 8) 8); [lia|].
  replace (16 * S (length pre) + k - 8 - 8)%nat with (16 * length pre + k)%nat by lia. apply IH.
Qed.

Lemma mtab_cell_ptr : forall es i e, nth_error es i = Some e ->
  cell_at (mtab_cells es) (16 * i) = Some (C8 (Z_to_bv 64 (me_ptr e))).
Proof.
  intros es i e H. (first [ pose proof ((nth_error_split _ _ _ H)) as dR_2; dex2 dR_2 as pre post; destruct dR_2 as [-> Hlen] | pose proof ((nth_error_split _ _ _ H)) as dR_2; dand4 dR_2 as pre post -> Hlen | destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen) ]).
  replace (16 * i)%nat with (16 * length pre + 0)%nat by lia.
  rewrite mtab_cell_at_skip. reflexivity.
Qed.

Lemma mtab_cell_svar : forall es i e, nth_error es i = Some e ->
  cell_at (mtab_cells es) (16 * i + 8) = Some (C8 (Z_to_bv 64 (me_svar e))).
Proof.
  intros es i e H. (first [ pose proof ((nth_error_split _ _ _ H)) as dR_3; dex2 dR_3 as pre post; destruct dR_3 as [-> Hlen] | pose proof ((nth_error_split _ _ _ H)) as dR_3; dand4 dR_3 as pre post -> Hlen | destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen) ]).
  replace (16 * i + 8)%nat with (16 * length pre + 8)%nat by lia.
  rewrite mtab_cell_at_skip. reflexivity.
Qed.

Lemma mtab_read_ptr : forall m T es i e a,
  ro_cells segs m T (mtab_cells es) -> nth_error es i = Some e ->
  a = wa (T + 16 * Z.of_nat i) ->
  ov_read_bytes segs m a 8 = Some (le8 (Z_to_bv 64 (me_ptr e))).
Proof.
  intros m T es i e a TAB H ->.
  replace (16 * Z.of_nat i)%Z with (Z.of_nat (16 * i)) by lia.
  apply (ro_cells_read_at segs m T (mtab_cells es) (16 * i) (C8 (Z_to_bv 64 (me_ptr e))) 8); auto.
  apply mtab_cell_ptr; assumption.
Qed.

Lemma mtab_read_svar : forall m T es i e a,
  ro_cells segs m T (mtab_cells es) -> nth_error es i = Some e ->
  a = wa (T + 16 * Z.of_nat i + 8) ->
  ov_read_bytes segs m a 8 = Some (le8 (Z_to_bv 64 (me_svar e))).
Proof.
  intros m T es i e a TAB H ->.
  replace (T + 16 * Z.of_nat i + 8)%Z with (T + Z.of_nat (16 * i + 8))%Z by lia.
  apply (ro_cells_read_at segs m T (mtab_cells es) (16 * i + 8) (C8 (Z_to_bv 64 (me_svar e))) 8); auto.
  apply mtab_cell_svar; assumption.
Qed.
End WithSegs.

(* [comment removed for export] *)
Section Pure.
  Variable inp : list byte.

  Definition shift (i : nat) (r : option nat) : option nat :=
    match r with Some j => Some (i + j)%nat | None => None end.

  Lemma vm_find_skip : forall es i e,
    nth_error es i = Some e ->
    (forall i' e', (i' < i)%nat -> nth_error es i' = Some e' ->
        me_ptr e' <> 0 /\ is_prefixb (me_str e') inp = false /\ runs_outb (me_str e') inp = false) ->
    vm_find es inp = shift i (vm_find (skipn i es) inp).
  Proof.
    intros es i. revert es. induction i as [|i IH]; intros es e Hn Hpre.
    - change (skipn 0 es) with es. unfold shift. destruct (vm_find es inp); reflexivity.
    - destruct es as [|e0 es']; [discriminate|]. cbn in Hn.
      (first [ pose proof ((Hpre 0%nat e0 ltac:(lia) eq_refl)) as dR_4; dand3 dR_4 as P0 P1 P2 | destruct (Hpre 0%nat e0 ltac:(lia) eq_refl) as (P0 & P1 & P2) ]).
      cbn [vm_find skipn]. replace (me_ptr e0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact P0).
      rewrite P1, P2. rewrite (IH es' e Hn).
      + change (skipn (S i) (e0 :: es')) with (skipn i es'). unfold shift. destruct (vm_find (skipn i es') inp); cbn; [f_equal; lia|reflexivity].
      + intros i' e' Hi' Hn'. apply (Hpre (S i') e'); [lia|exact Hn'].
  Qed.

  (* [comment removed for export] *)
  Definition agree_upto (s : list byte) (j : nat) : Prop := firstn j s = firstn j inp.

  Lemma agree_upto_0 : forall s, agree_upto s 0.
  Proof. intros; reflexivity. Qed.

  Lemma prefix_at_end : forall s j, agree_upto s j -> j = length s -> is_prefixb s inp = true.
  Proof.
    unfold agree_upto. intros s j H ->. rewrite firstn_all in H.
    revert H. generalize inp as l. induction s as [|c s IH]; intros [|d l'] H; cbn in *; try reflexivity; try discriminate.
    injection H as <- H'. rewrite bv_eqb_refl. cbn. apply IH. exact H'.
  Qed.

  Lemma runs_out_at : forall s j, agree_upto s j -> (j < length s)%nat -> j = length inp ->
    is_prefixb s inp = false /\ runs_outb s inp = true.
  Proof.
    unfold agree_upto. intros s j H Hj ->. rewrite (firstn_all inp) in H.
    revert s H Hj. generalize inp as l. induction l as [|d l IH]; intros [|c s] H Hj; cbn in *; try lia; auto.
    injection H as <- H'. rewrite bv_eqb_refl. cbn. apply IH; [exact H'|lia].
  Qed.

  Lemma mismatch_at : forall s j c d, agree_upto s j -> nth_error s j = Some c -> nth_error inp j = Some d -> c <> d ->
    is_prefixb s inp = false /\ runs_outb s inp = false.
  Proof.
    unfold agree_upto. intros s j. revert s. generalize inp as l. intros l s; revert l s.
    induction j as [|j IH]; intros [|d0 l] [|c0 s] c d H Hc Hd Hne; cbn in *; try discriminate.
    - injection Hc as ->. injection Hd as ->. replace (bv_eqb c d) with false; [auto|].
      symmetry. apply Bool.not_true_iff_false. intros Hb. apply Hne. unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. apply bv_eq. exact Hb.
    - injection H as E1 H'. rewrite E1, bv_eqb_refl. cbn. eapply IH; eauto.
  Qed.

  Lemma agree_step : forall s j c, agree_upto s j -> nth_error s j = Some c -> nth_error inp j = Some c -> agree_upto s (S j).
  Proof.
    unfold agree_upto. intros s j. revert s. generalize inp as l. intros l s; revert l s.
    induction j as [|j IH]; intros [|d0 l] [|c0 s] c H Hc Hd; cbn in *; try discriminate.
    - injection Hc as ->. injection Hd as ->. reflexivity.
    - injection H as E1 H'. rewrite E1. f_equal. eapply IH; eauto.
  Qed.
    (* [comment removed for export] *)
  Definition searched (es : list mentry) (i : nat) : Prop :=
    forall i' e', (i' < i)%nat -> nth_error es i' = Some e' ->
      me_ptr e' <> 0%Z /\ is_prefixb (me_str e') inp = false /\ runs_outb (me_str e') inp = false.

  Lemma searched_next : forall es i e, searched es i -> nth_error es i = Some e -> me_ptr e <> 0%Z ->
    is_prefixb (me_str e) inp = false -> runs_outb (me_str e) inp = false -> searched es (S i).
  Proof.
    intros es i e Hs Hn Hp H1 H2 i' e' Hi' Hn'.
    destruct (Nat.eq_dec i' i) as [->|NE].
    - rewrite Hn in Hn'. injection Hn' as <-. auto.
    - apply (Hs i' e'); [lia|exact Hn'].
  Qed.

  Lemma vm_here : forall es i e, searched es i -> nth_error es i = Some e ->
    vm_find es inp = shift i (vm_find (skipn i es) inp).
  Proof. intros es i e Hs Hn. eapply vm_find_skip; eauto. Qed.

  Lemma skipn_nth : forall {A} (l : list A) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
  Proof.
    intros A l. induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate.
    - injection H as ->. reflexivity.
    - apply IH. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma vm_found : forall es i e, searched es i -> nth_error es i = Some e -> me_ptr e <> 0%Z ->
    is_prefixb (me_str e) inp = true -> vm_find es inp = Some i.
  Proof.
    intros es i e Hs Hn Hp Hpre. rewrite (vm_here es i e Hs Hn), (skipn_nth es i e Hn). cbn [vm_find].
    replace (me_ptr e =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hp).
    rewrite Hpre. cbn. f_equal. lia.
  Qed.

  Lemma vm_ranout : forall es i e, searched es i -> nth_error es i = Some e -> me_ptr e <> 0%Z ->
    is_prefixb (me_str e) inp = false -> runs_outb (me_str e) inp = true -> vm_find es inp = None.
  Proof.
    intros es i e Hs Hn Hp H1 H2. rewrite (vm_here es i e Hs Hn), (skipn_nth es i e Hn). cbn [vm_find].
    replace (me_ptr e =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hp).
    rewrite H1, H2. reflexivity.
  Qed.

  Lemma vm_sentinel : forall es i e, searched es i -> nth_error es i = Some e -> me_ptr e = 0%Z ->
    vm_find es inp = Some i.
  Proof.
    intros es i e Hs Hn Hp. rewrite (vm_here es i e Hs Hn), (skipn_nth es i e Hn). cbn [vm_find].
    rewrite Hp. cbn. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wf_entry : forall l i e, mtab_wf l -> nth_error l i = Some e -> me_ptr e <> 0%Z ->
    (1 <= length (me_str e) <= 8)%nat /\ ~ In (Z_to_bv 8 0) (me_str e) /\ (S i < length l)%nat.
  Proof.
    induction l as [|e0 l IH]; intros [|i] e W Hn Hp; cbn in *; try discriminate.
    - injection Hn as ->. destruct l as [|e1 l']; [destruct W as [W0 _]; contradiction|].
      (first [ dand4 W as W0 W1 W2 _ | destruct W as (W0 & W1 & W2 & _) ]). cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; auto.
    - destruct l as [|e1 l']; [destruct i; discriminate|].
      (first [ dand4 W as W0 W1 W2 W' | destruct W as (W0 & W1 & W2 & W') ]). (first [ pose proof ((IH i e W' Hn Hp)) as dR_7; dand3 dR_7 as B1 B2 B3 | destruct (IH i e W' Hn Hp) as (B1 & B2 & B3) ]). cbn in B3 |- *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; auto.
  Qed.

  Lemma wf_ptr_nonneg : forall l i e, mtab_wf l -> nth_error l i = Some e -> (0 <= me_ptr e < 2^64)%Z.
  Proof.
    induction l as [|e0 l IH]; intros [|i] e W Hn; cbn in *; try discriminate.
    - injection Hn as ->. destruct l; [destruct W as [E0 _]; lia | destruct W as (W0 & _); lia].
    - destruct l as [|e1 l']; [destruct i; discriminate|]. (first [ dand4 W as _ _ _ W' | destruct W as (_ & _ & _ & W') ]). eapply IH; eauto.
  Qed.

End Pure.

(* [comment removed for export] *)
Section StrFacts.
  Variable segs : list Segment.

  Definition mtab_strings (m : word -> option byte) (es : list mentry) : Prop :=
    forall i e, nth_error es i = Some e -> me_ptr e <> 0 ->
      exists slack,
        bytes_at segs m (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack)
        /\ ((- (me_ptr e + Z.of_nat (length (me_str e)) + 1)) mod 8 <= Z.of_nat (length slack))
        /\ (length (me_str e) + 1 + length slack <= 16)%nat.

  Definition vm_result (T : Z) (es : list mentry) (inp : list byte) : word :=
    match vm_find es inp with
    | Some i => Z_to_bv 64 (T + 16 * Z.of_nat i)
    | None => Z_to_bv 64 0
    end.

  (* [comment removed for export] *)
  Definition entry_strings_b (e : mentry) : bool :=
    if me_ptr e =? 0 then true
    else
      let n := length (me_str e) in
      let k := (16 - n - 1)%nat in
      match image_bytes segs (me_ptr e + Z.of_nat n + 1) k with
      | Some slack =>
          ro_bytes_b segs (me_ptr e) (me_str e ++ Z_to_bv 8 0 :: slack)
          && ((- (me_ptr e + Z.of_nat n + 1)) mod 8 <=? Z.of_nat k)
          && (0 <=? me_ptr e) && (me_ptr e + 16 <=? 2^64) && (length (me_str e) <=? 14)%nat
      | None => false
      end.

  Definition mtab_strings_b (es : list mentry) : bool := forallb entry_strings_b es.

  Lemma mtab_strings_intro : forall m es,
    mem_inv segs m -> mtab_strings_b es = true -> mtab_strings m es.
  Proof.
    intros m es MI Hb i e Hn Hp.
    unfold mtab_strings_b in Hb. rewrite forallb_forall in Hb.
    specialize (Hb e (nth_error_In _ _ Hn)). unfold entry_strings_b in Hb.
    replace (me_ptr e =? 0) with false in Hb by (symmetry; apply Z.eqb_neq; exact Hp).
    destruct (image_bytes segs (me_ptr e + Z.of_nat (length (me_str e)) + 1) (16 - length (me_str e) - 1)) as [slack|] eqn:E; [|discriminate].
    apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [Hb B2]. apply andb_prop in Hb as [B0 B1].
    apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Nat.leb_le in B4.
    pose proof (image_bytes_length _ _ _ _ E) as Hlen.
    exists slack. split; [|split; [rewrite Hlen; exact B1 | lia]].
    apply ro_bytes_at; [exact MI | lia | | apply ro_bytes_b_sound; exact B0].
    rewrite app_length. cbn [length]. lia.
  Qed.
End StrFacts.
