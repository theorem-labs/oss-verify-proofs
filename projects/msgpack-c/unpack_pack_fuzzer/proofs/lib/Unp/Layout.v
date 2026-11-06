(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Definition bmem := Z -> option Z.

Fixpoint rdZ (m : bmem) (a : Z) (n : nat) : option Z :=
  match n with
  | O => Some 0
  | S n' => match m a, rdZ m (a + 1) n' with
            | Some b, Some r => Some (b + 256 * r)
            | _, _ => None
            end
  end.
Definition u8_at (m : bmem) (a v : Z) : Prop := rdZ m a 1 = Some v.
Definition u32_at (m : bmem) (a v : Z) : Prop := rdZ m a 4 = Some v.
Definition u64_at (m : bmem) (a v : Z) : Prop := rdZ m a 8 = Some v.
Definition optZ_eqb (o : option Z) (v : Z) : bool := match o with Some x => x =? v | None => false end.
Definition u8_b (m : bmem) (a v : Z) : bool := optZ_eqb (rdZ m a 1) v.
Definition u32_b (m : bmem) (a v : Z) : bool := optZ_eqb (rdZ m a 4) v.
Definition u64_b (m : bmem) (a v : Z) : bool := optZ_eqb (rdZ m a 8) v.

Lemma optZ_eqb_true : forall o v, optZ_eqb o v = true <-> o = Some v.
Proof.
  intros [x|] v; cbn; split; intro H; try discriminate.
  - apply Z.eqb_eq in H. now subst. - inversion H. apply Z.eqb_refl.
Qed.
Lemma u8_b_ok : forall m a v, u8_b m a v = true <-> u8_at m a v.   Proof. intros. apply optZ_eqb_true. Qed.
Lemma u32_b_ok : forall m a v, u32_b m a v = true <-> u32_at m a v. Proof. intros. apply optZ_eqb_true. Qed.
Lemma u64_b_ok : forall m a v, u64_b m a v = true <-> u64_at m a v. Proof. intros. apply optZ_eqb_true. Qed.

Definition readable (m : bmem) (a : Z) (n : nat) : Prop := exists v, rdZ m a n = Some v.
Definition readable_b (m : bmem) (a : Z) (n : nat) : bool := match rdZ m a n with Some _ => true | None => false end.
Lemma readable_b_ok : forall m a n, readable_b m a n = true <-> readable m a n.
Proof.
  intros m a n. unfold readable_b, readable. destruct (rdZ m a n); split; intro H; try discriminate; eauto.
  destruct H; discriminate.
Qed.

Definition enc64 (i : Z) : Z := i mod 2^64.

Definition agree_on (m m' : bmem) (a n : Z) : Prop := forall x, a <= x < a + n -> m' x = m x.

Lemma agree_on_sub : forall m m' a n a' n', agree_on m m' a n -> a <= a' -> a' + n' <= a + n -> agree_on m m' a' n'.
Proof. intros m m' a n a' n' H H1 H2 x Hx. apply H. lia. Qed.
Lemma agree_on_refl : forall m a n, agree_on m m a n. Proof. intros m a n x _; reflexivity. Qed.
Lemma agree_on_sym : forall m m' a n, agree_on m m' a n -> agree_on m' m a n.
Proof. intros m m' a n H x Hx. symmetry. now apply H. Qed.
Lemma agree_on_trans : forall m1 m2 m3 a n, agree_on m1 m2 a n -> agree_on m2 m3 a n -> agree_on m1 m3 a n.
Proof. intros m1 m2 m3 a n H1 H2 x Hx. rewrite (H2 x Hx). now apply H1. Qed.

Lemma rdZ_agree : forall m m' a n, agree_on m m' a (Z.of_nat n) -> rdZ m' a n = rdZ m a n.
Proof.
  intros m m' a n. revert a. induction n as [|n IH]; intros a H; cbn; [reflexivity|].
  rewrite (H a) by lia. rewrite IH; [reflexivity|]. intros x Hx. apply H. lia.
Qed.
Lemma u64_at_frame : forall m m' a v, agree_on m m' a 8 -> u64_at m a v -> u64_at m' a v.
Proof. intros m m' a v H Hv. unfold u64_at in *. now rewrite (rdZ_agree m m' a 8 H). Qed.
Lemma u32_at_frame : forall m m' a v, agree_on m m' a 4 -> u32_at m a v -> u32_at m' a v.
Proof. intros m m' a v H Hv. unfold u32_at in *. now rewrite (rdZ_agree m m' a 4 H). Qed.
Lemma u8_at_frame : forall m m' a v, agree_on m m' a 1 -> u8_at m a v -> u8_at m' a v.
Proof. intros m m' a v H Hv. unfold u8_at in *. now rewrite (rdZ_agree m m' a 1 H). Qed.

Definition updated_within (m m' : bmem) (lo n : Z) : Prop := forall x, (x < lo \/ lo + n <= x) -> m' x = m x.
Lemma updated_agree : forall m m' lo n a k, updated_within m m' lo n -> (a + k <= lo \/ lo + n <= a) -> agree_on m m' a k.
Proof. intros m m' lo n a k H Hd x Hx. apply H. lia. Qed.

Fixpoint obj_at (m : bmem) (a : Z) (o : obj) {struct o} : Prop :=
  u32_at m a (obj_type o) /\
  match o with
  | ONil => True
  | OBool b => u8_at m (a + 8) (if b then 1 else 0)
  | OPos u => u64_at m (a + 8) u
  | ONeg i => u64_at m (a + 8) (enc64 i)
  | OF32 bits => u64_at m (a + 8) bits
  | OF64 bits => u64_at m (a + 8) bits
  | OStr p n | OBin p n | OExt p n => u32_at m (a + 8) n /\ u64_at m (a + 16) p
  | OArr p kids => u32_at m (a + 8) (Z.of_nat (length kids)) /\ u64_at m (a + 16) p /\
      (fix objs_at (q : Z) (l : list obj) {struct l} : Prop :=
         match l with [] => True | o' :: l' => obj_at m q o' /\ objs_at (q + OBJ_SIZE) l' end) p kids
  | OMap p kids => u32_at m (a + 8) (Z.of_nat (length kids) / 2) /\ u64_at m (a + 16) p /\
      (fix objs_at (q : Z) (l : list obj) {struct l} : Prop :=
         match l with [] => True | o' :: l' => obj_at m q o' /\ objs_at (q + OBJ_SIZE) l' end) p kids
  end.
Fixpoint objs_at (m : bmem) (q : Z) (l : list obj) : Prop :=
  match l with [] => True | o :: l' => obj_at m q o /\ objs_at m (q + OBJ_SIZE) l' end.
Lemma obj_at_arr : forall m a p kids,
  obj_at m a (OArr p kids) <-> (u32_at m a T_ARRAY /\ u32_at m (a+8) (Z.of_nat (length kids)) /\ u64_at m (a+16) p /\ objs_at m p kids).
Proof.
  intros m a p kids. cbn [obj_at obj_type].
  assert (E : forall q, (fix objs_at0 (q0 : Z) (l : list obj) {struct l} : Prop :=
            match l with [] => True | o' :: l' => obj_at m q0 o' /\ objs_at0 (q0 + OBJ_SIZE) l' end) q kids <-> objs_at m q kids).
  { induction kids as [|o l IH]; intro q; cbn [objs_at]; [tauto|]. rewrite <- IH. tauto. }
  rewrite E. tauto.
Qed.
Lemma obj_at_map : forall m a p kids,
  obj_at m a (OMap p kids) <-> (u32_at m a T_MAP /\ u32_at m (a+8) (Z.of_nat (length kids) / 2) /\ u64_at m (a+16) p /\ objs_at m p kids).
Proof.
  intros m a p kids. cbn [obj_at obj_type].
  assert (E : forall q, (fix objs_at0 (q0 : Z) (l : list obj) {struct l} : Prop :=
            match l with [] => True | o' :: l' => obj_at m q0 o' /\ objs_at0 (q0 + OBJ_SIZE) l' end) q kids <-> objs_at m q kids).
  { induction kids as [|o l IH]; intro q; cbn [objs_at]; [tauto|]. rewrite <- IH. tauto. }
  rewrite E. tauto.
Qed.

Fixpoint obj_at_b (m : bmem) (a : Z) (o : obj) {struct o} : bool :=
  u32_b m a (obj_type o) &&
  match o with
  | ONil => true
  | OBool b => u8_b m (a + 8) (if b then 1 else 0)
  | OPos u => u64_b m (a + 8) u
  | ONeg i => u64_b m (a + 8) (enc64 i)
  | OF32 bits => u64_b m (a + 8) bits
  | OF64 bits => u64_b m (a + 8) bits
  | OStr p n | OBin p n | OExt p n => u32_b m (a + 8) n && u64_b m (a + 16) p
  | OArr p kids => u32_b m (a + 8) (Z.of_nat (length kids)) && u64_b m (a + 16) p &&
      (fix objs_b (q : Z) (l : list obj) {struct l} : bool :=
         match l with [] => true | o' :: l' => obj_at_b m q o' && objs_b (q + OBJ_SIZE) l' end) p kids
  | OMap p kids => u32_b m (a + 8) (Z.of_nat (length kids) / 2) && u64_b m (a + 16) p &&
      (fix objs_b (q : Z) (l : list obj) {struct l} : bool :=
         match l with [] => true | o' :: l' => obj_at_b m q o' && objs_b (q + OBJ_SIZE) l' end) p kids
  end.

Fixpoint objs_at_b (m : bmem) (q : Z) (l : list obj) : bool :=
  match l with [] => true | o :: l' => obj_at_b m q o && objs_at_b m (q + OBJ_SIZE) l' end.
Lemma obj_at_b_arr : forall m a p kids,
  obj_at_b m a (OArr p kids) = u32_b m a T_ARRAY && (u32_b m (a+8) (Z.of_nat (length kids)) && u64_b m (a+16) p && objs_at_b m p kids).
Proof.
  intros m a p kids. cbn [obj_at_b obj_type].
  assert (E : forall q, (fix objs_b (q0 : Z) (l : list obj) {struct l} : bool :=
            match l with [] => true | o' :: l' => obj_at_b m q0 o' && objs_b (q0 + OBJ_SIZE) l' end) q kids = objs_at_b m q kids).
  { induction kids as [|o l IH]; intro q; cbn [objs_at_b]; [reflexivity|]. now rewrite <- IH. }
  now rewrite E.
Qed.
Lemma obj_at_b_map : forall m a p kids,
  obj_at_b m a (OMap p kids) = u32_b m a T_MAP && (u32_b m (a+8) (Z.of_nat (length kids) / 2) && u64_b m (a+16) p && objs_at_b m p kids).
Proof.
  intros m a p kids. cbn [obj_at_b obj_type].
  assert (E : forall q, (fix objs_b (q0 : Z) (l : list obj) {struct l} : bool :=
            match l with [] => true | o' :: l' => obj_at_b m q0 o' && objs_b (q0 + OBJ_SIZE) l' end) q kids = objs_at_b m q kids).
  { induction kids as [|o l IH]; intro q; cbn [objs_at_b]; [reflexivity|]. now rewrite <- IH. }
  now rewrite E.
Qed.

Lemma obj_ind_size (P : obj -> Prop) :
  (forall o, (forall o', (obj_size o' < obj_size o)%nat -> P o') -> P o) -> forall o, P o.
Proof.
  intros H o. remember (obj_size o) as n eqn:E. revert o E.
  induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros o E. apply H. intros o' Ho'. apply (IH (obj_size o')); lia.
Qed.

Lemma in_kids_size : forall o l, In o l -> (obj_size o <= objs_size l)%nat.
Proof.
  intros o l. induction l as [|x l IH]; [intros []|]. intros [->|H]; rewrite objs_size_cons; [lia|].
  specialize (IH H). lia.
Qed.

Lemma objs_at_b_ok_gen : forall m kids,
  (forall o', In o' kids -> forall q, obj_at_b m q o' = true -> obj_at m q o') ->
  forall q, objs_at_b m q kids = true -> objs_at m q kids.
Proof.
  intros m kids IHk. induction kids as [|x l IHl]; intros q Hq; cbn -[obj_at obj_at_b] in Hq |- *; [exact I|].
  apply andb_prop in Hq. destruct Hq as [Hx Hl]. split.
  - apply IHk; [now left|exact Hx].
  - apply IHl; [|exact Hl]. intros o' Ho'. apply IHk. now right.
Qed.

Lemma obj_at_b_ok : forall m o a, obj_at_b m a o = true -> obj_at m a o.
Proof.
  intros m. apply (obj_ind_size (fun o => forall a, obj_at_b m a o = true -> obj_at m a o)).
  intros o IH a H. destruct o.
  1-9: cbn [obj_at_b obj_at obj_type] in H |- *;
       repeat (apply andb_prop in H; destruct H as [H ?]);
       repeat match goal with
         | K : _ && _ = true |- _ => apply andb_prop in K; destruct K
         | K : u32_b _ _ _ = true |- _ => apply u32_b_ok in K
         | K : u64_b _ _ _ = true |- _ => apply u64_b_ok in K
         | K : u8_b _ _ _ = true |- _ => apply u8_b_ok in K
         end; tauto.
  - rewrite obj_at_b_arr in H. apply obj_at_arr.
    apply andb_prop in H. destruct H as [H1 H]. apply andb_prop in H. destruct H as [H H4].
    apply andb_prop in H. destruct H as [H2 H3].
    apply u32_b_ok in H1. apply u32_b_ok in H2. apply u64_b_ok in H3.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    eapply objs_at_b_ok_gen; [|exact H4]. intros o' Hin q Hq. apply IH; [|exact Hq].
    rewrite obj_size_arr. pose proof (in_kids_size o' kids Hin). lia.
  - rewrite obj_at_b_map in H. apply obj_at_map.
    apply andb_prop in H. destruct H as [H1 H]. apply andb_prop in H. destruct H as [H H4].
    apply andb_prop in H. destruct H as [H2 H3].
    apply u32_b_ok in H1. apply u32_b_ok in H2. apply u64_b_ok in H3.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    eapply objs_at_b_ok_gen; [|exact H4]. intros o' Hin q Hq. apply IH; [|exact Hq].
    rewrite obj_size_map. pose proof (in_kids_size o' kids Hin). lia.
Qed.

Fixpoint obj_cells (a : Z) (o : obj) {struct o} : list Z :=
  a :: match o with
       | OArr p kids | OMap p kids =>
           (fix cells (q : Z) (l : list obj) {struct l} : list Z :=
              match l with [] => [] | o' :: l' => obj_cells q o' ++ cells (q + OBJ_SIZE) l' end) p kids
       | _ => []
       end.

Lemma obj_at_frame : forall m m' o a,
  (forall c, In c (obj_cells a o) -> agree_on m m' c OBJ_SIZE) -> obj_at m a o -> obj_at m' a o.
Proof.
  intros m m'. apply (obj_ind_size (fun o => forall a, (forall c, In c (obj_cells a o) -> agree_on m m' c OBJ_SIZE) -> obj_at m a o -> obj_at m' a o)).
  intros o IH a Hag H.
  assert (Ha : agree_on m m' a OBJ_SIZE) by (apply Hag; destruct o; cbn; now left).
  assert (A0 : agree_on m m' a 4) by (eapply agree_on_sub; [exact Ha| lia | unfold OBJ_SIZE; lia]).
  assert (A8 : agree_on m m' (a+8) 8) by (eapply agree_on_sub; [exact Ha| lia | unfold OBJ_SIZE; lia]).
  assert (A84 : agree_on m m' (a+8) 4) by (eapply agree_on_sub; [exact Ha| lia | unfold OBJ_SIZE; lia]).
  assert (A81 : agree_on m m' (a+8) 1) by (eapply agree_on_sub; [exact Ha| lia | unfold OBJ_SIZE; lia]).
  assert (A16 : agree_on m m' (a+16) 8) by (eapply agree_on_sub; [exact Ha| lia | unfold OBJ_SIZE; lia]).
  destruct o.
  1-9: cbn [obj_at obj_type] in H |- *; decompose [and] H; repeat split; eauto using u32_at_frame, u64_at_frame, u8_at_frame.
  -   apply obj_at_arr in H. apply obj_at_arr. destruct H as (H1 & H2 & H3 & H4).
    split; [eauto using u32_at_frame|]. split; [eauto using u32_at_frame|]. split; [eauto using u64_at_frame|].
    assert (IHk : forall o', In o' kids -> forall q, (forall c, In c (obj_cells q o') -> agree_on m m' c OBJ_SIZE) -> obj_at m q o' -> obj_at m' q o').
    { intros o' Hin. apply IH. rewrite obj_size_arr. pose proof (in_kids_size o' kids Hin). lia. }
    assert (Hcells : forall c, In c ((fix cells (q : Z) (l : list obj) {struct l} : list Z :=
              match l with [] => [] | o' :: l' => obj_cells q o' ++ cells (q + OBJ_SIZE) l' end) p kids) -> agree_on m m' c OBJ_SIZE).
    { intros c Hc. apply Hag. cbn. right. exact Hc. }
    clear Hag IH H1 H2 H3. revert p H4 Hcells. induction kids as [|x l IHl]; intros p H4 Hcells; cbn in H4 |- *; [exact I|].
    destruct H4 as [Hx Hl]. split.
    + apply IHk; [now left| |exact Hx]. intros c Hc. apply Hcells. apply in_app_iff. now left.
    + apply IHl; [| exact Hl |]. { intros o' Ho'. apply IHk. now right. } intros c Hc. apply Hcells. apply in_app_iff. now right.
  -   apply obj_at_map in H. apply obj_at_map. destruct H as (H1 & H2 & H3 & H4).
    split; [eauto using u32_at_frame|]. split; [eauto using u32_at_frame|]. split; [eauto using u64_at_frame|].
    assert (IHk : forall o', In o' kids -> forall q, (forall c, In c (obj_cells q o') -> agree_on m m' c OBJ_SIZE) -> obj_at m q o' -> obj_at m' q o').
    { intros o' Hin. apply IH. rewrite obj_size_map. pose proof (in_kids_size o' kids Hin). lia. }
    assert (Hcells : forall c, In c ((fix cells (q : Z) (l : list obj) {struct l} : list Z :=
              match l with [] => [] | o' :: l' => obj_cells q o' ++ cells (q + OBJ_SIZE) l' end) p kids) -> agree_on m m' c OBJ_SIZE).
    { intros c Hc. apply Hag. cbn. right. exact Hc. }
    clear Hag IH H1 H2 H3. revert p H4 Hcells. induction kids as [|x l IHl]; intros p H4 Hcells; cbn in H4 |- *; [exact I|].
    destruct H4 as [Hx Hl]. split.
    + apply IHk; [now left| |exact Hx]. intros c Hc. apply Hcells. apply in_app_iff. now left.
    + apply IHl; [| exact Hl |]. { intros o' Ho'. apply IHk. now right. } intros c Hc. apply Hcells. apply in_app_iff. now right.
Qed.

Definition vec_at (m : bmem) (hdr : Z) (v : vecg) : Prop :=
  u64_at m hdr (v_begin v) /\ u64_at m (hdr + 8) (v_end v) /\ u64_at m (hdr + 16) (v_capend v).
Definition vec_at_b (m : bmem) (hdr : Z) (v : vecg) : bool :=
  u64_b m hdr (v_begin v) && u64_b m (hdr + 8) (v_end v) && u64_b m (hdr + 16) (v_capend v).

Definition ctx_at (m : bmem) (g : unpg) (cur cs trail : Z) : Prop :=
  u64_at m (u_ctx g) (u_data g) /\ u64_at m (u_ctx g + 8) cur /\ u64_at m (u_ctx g + 16) trail /\
  u32_at m (u_ctx g + 24) cs /\ vec_at m (u_ctx g + 32) (u_cstk g) /\ u64_at m (u_ctx g + 56) (u_vis g).
Definition ctx_at_b (m : bmem) (g : unpg) (cur cs trail : Z) : bool :=
  u64_b m (u_ctx g) (u_data g) && u64_b m (u_ctx g + 8) cur && u64_b m (u_ctx g + 16) trail &&
  u32_b m (u_ctx g + 24) cs && vec_at_b m (u_ctx g + 32) (u_cstk g) && u64_b m (u_ctx g + 56) (u_vis g).

Definition vis_at (m : bmem) (g : unpg) : Prop :=
  u64_at m (u_vis g) 0 /\ u64_at m (u_vis g + 8) 0 /\
  u64_at m (u_vis g + 16) LIMIT /\ u64_at m (u_vis g + 24) LIMIT /\ u64_at m (u_vis g + 32) LIMIT /\
  u64_at m (u_vis g + 40) LIMIT /\ u64_at m (u_vis g + 48) LIMIT /\ u64_at m (u_vis g + 56) LIMIT /\
  vec_at m (u_vis g + 88) (u_vstk g) /\ u64_at m (u_vis g + 112) (z_addr (u_zone g)) /\ u8_at m (u_vis g + 120) 0.
Definition vis_at_b (m : bmem) (g : unpg) : bool :=
  u64_b m (u_vis g) 0 && u64_b m (u_vis g + 8) 0 &&
  u64_b m (u_vis g + 16) LIMIT && u64_b m (u_vis g + 24) LIMIT && u64_b m (u_vis g + 32) LIMIT &&
  u64_b m (u_vis g + 40) LIMIT && u64_b m (u_vis g + 48) LIMIT && u64_b m (u_vis g + 56) LIMIT &&
  vec_at_b m (u_vis g + 88) (u_vstk g) && u64_b m (u_vis g + 112) (z_addr (u_zone g)) && u8_b m (u_vis g + 120) 0.

Fixpoint chunks_at (m : bmem) (cs : list (Z * Z)) : Prop :=
  match cs with
  | [] => True
  | (c, _) :: rest => u64_at m c (match rest with [] => 0 | (c', _) :: _ => c' end) /\ chunks_at m rest
  end.
Fixpoint chunks_at_b (m : bmem) (cs : list (Z * Z)) : bool :=
  match cs with
  | [] => true
  | (c, _) :: rest => u64_b m c (match rest with [] => 0 | (c', _) :: _ => c' end) && chunks_at_b m rest
  end.

Definition zone_at (m : bmem) (z : zoneg) : Prop :=
  u64_at m (z_addr z) CHUNK_SIZE0 /\ u64_at m (z_addr z + 8) (z_free z) /\ u64_at m (z_addr z + 16) (z_ptr z) /\
  u64_at m (z_addr z + 24) (z_head z) /\ u64_at m (z_addr z + 32) 0 /\ u64_at m (z_addr z + 40) 0 /\ u64_at m (z_addr z + 48) 0 /\
  chunks_at m (z_chunks z).
Definition zone_at_b (m : bmem) (z : zoneg) : bool :=
  u64_b m (z_addr z) CHUNK_SIZE0 && u64_b m (z_addr z + 8) (z_free z) && u64_b m (z_addr z + 16) (z_ptr z) &&
  u64_b m (z_addr z + 24) (z_head z) && u64_b m (z_addr z + 32) 0 && u64_b m (z_addr z + 40) 0 && u64_b m (z_addr z + 48) 0 &&
  chunks_at_b m (z_chunks z).

Fixpoint cstk_at (m : bmem) (a : Z) (ls : list level) : Prop :=
  match ls with
  | [] => True
  | l :: ls' => u32_at m a (ctype_code (lv_t l)) /\ u32_at m (a + 4) (lv_rest l) /\ cstk_at m (a + 8) ls'
  end.
Fixpoint cstk_at_b (m : bmem) (a : Z) (ls : list level) : bool :=
  match ls with
  | [] => true
  | l :: ls' => u32_b m a (ctype_code (lv_t l)) && u32_b m (a + 4) (lv_rest l) && cstk_at_b m (a + 8) ls'
  end.

Fixpoint vstk_at (m : bmem) (a : Z) (ls : list level) : Prop :=
  match ls with
  | [] => True
  | l :: ls' => u64_at m a (lv_slot l) /\ vstk_at m (a + 8) ls'
  end.
Fixpoint vstk_at_b (m : bmem) (a : Z) (ls : list level) : bool :=
  match ls with
  | [] => true
  | l :: ls' => u64_b m a (lv_slot l) && vstk_at_b m (a + 8) ls'
  end.
Definition stacks_at (m : bmem) (g : unpg) : Prop :=
  cstk_at m (v_begin (u_cstk g)) (u_levels g) /\
  u64_at m (v_begin (u_vstk g)) (u_root g) /\ vstk_at m (v_begin (u_vstk g) + 8) (u_levels g).
Definition stacks_at_b (m : bmem) (g : unpg) : bool :=
  cstk_at_b m (v_begin (u_cstk g)) (u_levels g) &&
  u64_b m (v_begin (u_vstk g)) (u_root g) && vstk_at_b m (v_begin (u_vstk g) + 8) (u_levels g).

Fixpoint conts_at (m : bmem) (cs : list Z) (ls : list level) : Prop :=
  match cs, ls with
  | c :: cs', l :: ls' => u32_at m c (container_type (lv_t l)) /\ u32_at m (c + 8) (lv_n l) /\ u64_at m (c + 16) (lv_P l) /\ conts_at m cs' ls'
  | _, _ => True
  end.
Fixpoint conts_at_b (m : bmem) (cs : list Z) (ls : list level) : bool :=
  match cs, ls with
  | c :: cs', l :: ls' => u32_b m c (container_type (lv_t l)) && u32_b m (c + 8) (lv_n l) && u64_b m (c + 16) (lv_P l) && conts_at_b m cs' ls'
  | _, _ => true
  end.

Definition sbuf_at (m : bmem) (s : sbufg) : Prop :=
  u64_at m (sb_addr s) (sb_size s) /\ u64_at m (sb_addr s + 8) (sb_data s) /\ u64_at m (sb_addr s + 16) (sb_alloc s).
Definition sbuf_at_b (m : bmem) (s : sbufg) : bool :=
  u64_b m (sb_addr s) (sb_size s) && u64_b m (sb_addr s + 8) (sb_data s) && u64_b m (sb_addr s + 16) (sb_alloc s).

Definition op_at (m : bmem) (pk : packg) (cur : Z) : Prop :=
  u64_at m (p_op pk) cur /\ vec_at m (p_op pk + 8) (p_evec pk).
Definition op_at_b (m : bmem) (pk : packg) (cur : Z) : bool :=
  u64_b m (p_op pk) cur && vec_at_b m (p_op pk + 8) (p_evec pk).
Fixpoint pelems_at (m : bmem) (a : Z) (es : list pelem) : Prop :=
  match es with
  | [] => True
  | e :: es' => u64_at m a (pe_ptr e) /\ u64_at m (a + 8) (pe_rest e) /\
               u8_at m (a + 16) (if pe_map e then 1 else 0) /\ u8_at m (a + 17) (if pe_key e then 1 else 0) /\
               pelems_at m (a + ELEM_SIZE) es'
  end.
Fixpoint pelems_at_b (m : bmem) (a : Z) (es : list pelem) : bool :=
  match es with
  | [] => true
  | e :: es' => u64_b m a (pe_ptr e) && u64_b m (a + 8) (pe_rest e) &&
               u8_b m (a + 16) (if pe_map e then 1 else 0) && u8_b m (a + 17) (if pe_key e then 1 else 0) &&
               pelems_at_b m (a + ELEM_SIZE) es'
  end.

Local Ltac bsplit H :=
  repeat (apply andb_prop in H; let H1 := fresh in destruct H as [H H1]; revert H1); intros.
Local Ltac batoms :=
  repeat match goal with
    | H : u64_b _ _ _ = true |- _ => apply u64_b_ok in H
    | H : u32_b _ _ _ = true |- _ => apply u32_b_ok in H
    | H : u8_b _ _ _ = true |- _ => apply u8_b_ok in H
    end.

Lemma vec_at_b_ok : forall m h v, vec_at_b m h v = true -> vec_at m h v.
Proof. intros m h v H. unfold vec_at_b in H. bsplit H. batoms. unfold vec_at. tauto. Qed.
Lemma ctx_at_b_ok : forall m g cur cs tr, ctx_at_b m g cur cs tr = true -> ctx_at m g cur cs tr.
Proof. intros m g cur cs tr H. unfold ctx_at_b in H. bsplit H. batoms. apply vec_at_b_ok in H3. unfold ctx_at. tauto. Qed.
Lemma vis_at_b_ok : forall m g, vis_at_b m g = true -> vis_at m g.
Proof. intros m g H. unfold vis_at_b in H. bsplit H. batoms. apply vec_at_b_ok in H7. unfold vis_at. tauto. Qed.
Lemma chunks_at_b_ok : forall m cs, chunks_at_b m cs = true -> chunks_at m cs.
Proof. intros m cs. induction cs as [|[c sz] rest IH]; cbn; intro H; [exact I|]. bsplit H. batoms. split; [assumption|now apply IH]. Qed.
Lemma zone_at_b_ok : forall m z, zone_at_b m z = true -> zone_at m z.
Proof. intros m z H. unfold zone_at_b in H. bsplit H. batoms. apply chunks_at_b_ok in H6. unfold zone_at. tauto. Qed.
Lemma cstk_at_b_ok : forall m a ls, cstk_at_b m a ls = true -> cstk_at m a ls.
Proof. intros m a ls. revert a. induction ls as [|l ls IH]; intros a H; cbn in *; [exact I|]. bsplit H. batoms. repeat split; auto. Qed.
Lemma vstk_at_b_ok : forall m a ls, vstk_at_b m a ls = true -> vstk_at m a ls.
Proof. intros m a ls. revert a. induction ls as [|l ls IH]; intros a H; cbn in *; [exact I|]. bsplit H. batoms. split; auto. Qed.
Lemma stacks_at_b_ok : forall m g, stacks_at_b m g = true -> stacks_at m g.
Proof. intros m g H. unfold stacks_at_b in H. bsplit H. batoms. unfold stacks_at. auto using cstk_at_b_ok, vstk_at_b_ok. Qed.
Lemma conts_at_b_ok : forall m cs ls, conts_at_b m cs ls = true -> conts_at m cs ls.
Proof.
  intros m cs. induction cs as [|c cs IH]; intros [|l ls] H; cbn in *; try exact I. bsplit H. batoms. repeat split; auto.
Qed.
Lemma sbuf_at_b_ok : forall m s, sbuf_at_b m s = true -> sbuf_at m s.
Proof. intros m s H. unfold sbuf_at_b in H. bsplit H. batoms. unfold sbuf_at. tauto. Qed.
Lemma op_at_b_ok : forall m pk cur, op_at_b m pk cur = true -> op_at m pk cur.
Proof. intros m pk cur H. unfold op_at_b in H. bsplit H. batoms. apply vec_at_b_ok in H0. unfold op_at. tauto. Qed.
Lemma pelems_at_b_ok : forall m a es, pelems_at_b m a es = true -> pelems_at m a es.
Proof. intros m a es. revert a. induction es as [|e es IH]; intros a H; cbn in *; [exact I|]. bsplit H. batoms. repeat split; auto. Qed.

Local Ltac frame_atoms A :=
  repeat split;
  first [ eapply u64_at_frame; [|eassumption] | eapply u32_at_frame; [|eassumption] | eapply u8_at_frame; [|eassumption] ];
  (eapply agree_on_sub; [exact A | lia | lia]).

Lemma vec_at_frame : forall m m' h v, agree_on m m' h 24 -> vec_at m h v -> vec_at m' h v.
Proof. intros m m' h v A H. unfold vec_at in *. decompose [and] H. frame_atoms A. Qed.
Lemma ctx_at_frame : forall m m' g cur cs tr, agree_on m m' (u_ctx g) CTX_SIZE -> ctx_at m g cur cs tr -> ctx_at m' g cur cs tr.
Proof. intros m m' g cur cs tr A H. unfold ctx_at, vec_at, CTX_SIZE in *. decompose [and] H. frame_atoms A. Qed.
Lemma vis_at_frame : forall m m' g, agree_on m m' (u_vis g) VIS_SIZE -> vis_at m g -> vis_at m' g.
Proof. intros m m' g A H. unfold vis_at, vec_at, VIS_SIZE in *. decompose [and] H. frame_atoms A. Qed.
Lemma sbuf_at_frame : forall m m' s, agree_on m m' (sb_addr s) 24 -> sbuf_at m s -> sbuf_at m' s.
Proof. intros m m' s A H. unfold sbuf_at in *. decompose [and] H. frame_atoms A. Qed.
Lemma chunks_at_frame : forall m m' cs, (forall c, In c cs -> agree_on m m' (fst c) 8) -> chunks_at m cs -> chunks_at m' cs.
Proof.
  intros m m' cs. induction cs as [|[c sz] rest IH]; cbn; intros A H; [exact I|]. destruct H as [H1 H2]. split.
  - eapply u64_at_frame; [|exact H1]. apply (A (c, sz)). now left.
  - apply IH; [|exact H2]. intros c' Hc'. apply A. now right.
Qed.
Lemma zone_at_frame : forall m m' z,
  agree_on m m' (z_addr z) ZONE_SIZE -> (forall c, In c (z_chunks z) -> agree_on m m' (fst c) 8) -> zone_at m z -> zone_at m' z.
Proof.
  intros m m' z A Ac H. unfold zone_at, ZONE_SIZE in *. decompose [and] H.
  repeat split; try (eapply u64_at_frame; [|eassumption]; eapply agree_on_sub; [exact A|lia|lia]).
  eapply chunks_at_frame; eauto.
Qed.
Lemma cstk_at_frame : forall m m' a ls, agree_on m m' a (8 * Z.of_nat (length ls)) -> cstk_at m a ls -> cstk_at m' a ls.
Proof.
  intros m m' a ls. revert a. induction ls as [|l ls IH]; intros a A H; cbn [cstk_at] in *; [exact I|].
  cbn [length] in A. rewrite Nat2Z.inj_succ in A.
  destruct H as (H1 & H2 & H3). repeat split.
  - eapply u32_at_frame; [|exact H1]. eapply agree_on_sub; [exact A|lia|lia].
  - eapply u32_at_frame; [|exact H2]. eapply agree_on_sub; [exact A|lia|lia].
  - apply IH; [|exact H3]. eapply agree_on_sub; [exact A|lia|lia].
Qed.
Lemma vstk_at_frame : forall m m' a ls, agree_on m m' a (8 * Z.of_nat (length ls)) -> vstk_at m a ls -> vstk_at m' a ls.
Proof.
  intros m m' a ls. revert a. induction ls as [|l ls IH]; intros a A H; cbn [vstk_at] in *; [exact I|].
  cbn [length] in A. rewrite Nat2Z.inj_succ in A.
  destruct H as (H1 & H2). split.
  - eapply u64_at_frame; [|exact H1]. eapply agree_on_sub; [exact A|lia|lia].
  - apply IH; [|exact H2]. eapply agree_on_sub; [exact A|lia|lia].
Qed.
Lemma pelems_at_frame : forall m m' a es, agree_on m m' a (ELEM_SIZE * Z.of_nat (length es)) -> pelems_at m a es -> pelems_at m' a es.
Proof.
  intros m m' a es. revert a. induction es as [|e es IH]; intros a A H; cbn [pelems_at] in *; [exact I|].
  cbn [length] in A. rewrite Nat2Z.inj_succ in A.
  destruct H as (H1 & H2 & H3 & H4 & H5). unfold ELEM_SIZE in *. repeat split.
  - eapply u64_at_frame; [|exact H1]. eapply agree_on_sub; [exact A|lia|lia].
  - eapply u64_at_frame; [|exact H2]. eapply agree_on_sub; [exact A|lia|lia].
  - eapply u8_at_frame; [|exact H3]. eapply agree_on_sub; [exact A|lia|lia].
  - eapply u8_at_frame; [|exact H4]. eapply agree_on_sub; [exact A|lia|lia].
  - apply IH; [|exact H5]. eapply agree_on_sub; [exact A|lia|lia].
Qed.

Definition dec_sbe (m : bmem) (a : Z) (C : Z -> Z -> obj) : option obj :=
  match rdZ m (a + 8) 4, rdZ m (a + 16) 8 with
  | Some n, Some p => Some (C p n)
  | _, _ => None
  end.
Fixpoint decode_obj (fuel : nat) (m : bmem) (a : Z) {struct fuel} : option obj :=
  match fuel with
  | O => None
  | S f =>
    match rdZ m a 4 with
    | None => None
    | Some t =>
      if t =? T_NIL then Some ONil
      else if t =? T_BOOLEAN then
        match rdZ m (a + 8) 1 with Some b => if b =? 0 then Some (OBool false) else if b =? 1 then Some (OBool true) else None | None => None end
      else if t =? T_POSINT then option_map OPos (rdZ m (a + 8) 8)
      else if t =? T_NEGINT then
        match rdZ m (a + 8) 8 with Some u => if (0 <=? u) && (u <? 2^64) then Some (ONeg (u - 2^64)) else None | None => None end
      else if t =? T_FLOAT32 then option_map OF32 (rdZ m (a + 8) 8)
      else if t =? T_FLOAT64 then option_map OF64 (rdZ m (a + 8) 8)
      else if t =? T_STR then dec_sbe m a OStr
      else if t =? T_BIN then dec_sbe m a OBin
      else if t =? T_EXT then dec_sbe m a OExt
      else if (t =? T_ARRAY) || (t =? T_MAP) then
        match rdZ m (a + 8) 4, rdZ m (a + 16) 8 with
        | Some n, Some p =>
          if n <? 0 then None else
          let cnt := Z.to_nat (if t =? T_ARRAY then n else 2 * n) in
          match (fix dec (k : nat) (q : Z) {struct k} : option (list obj) :=
                   match k with
                   | O => Some []
                   | S k' => match decode_obj f m q, dec k' (q + OBJ_SIZE) with
                             | Some o, Some l => Some (o :: l) | _, _ => None end
                   end) cnt p with
          | Some l => Some (if t =? T_ARRAY then OArr p l else OMap p l)
          | None => None
          end
        | _, _ => None
        end
      else None
    end
  end.

Inductive btree := BLeaf | BNode (l : btree) (k : Z) (v : Z) (r : btree).
Fixpoint bt_get (t : btree) (a : Z) : option Z :=
  match t with
  | BLeaf => None
  | BNode l k v r => match Z.compare a k with Lt => bt_get l a | Eq => Some v | Gt => bt_get r a end
  end.
Definition bmem_of_btree (t : btree) : bmem := bt_get t.

Lemma decode_kids_ok : forall f m,
  (forall a o, decode_obj f m a = Some o -> obj_at m a o) ->
  forall k q l,
  (fix dec (k : nat) (q : Z) {struct k} : option (list obj) :=
     match k with
     | O => Some []
     | S k' => match decode_obj f m q, dec k' (q + OBJ_SIZE) with
               | Some o, Some l => Some (o :: l) | _, _ => None end
     end) k q = Some l -> objs_at m q l /\ length l = k.
Proof.
  intros f m IH k. induction k as [|k IHk]; intros q l H; cbn in H.
  - inversion H. subst. cbn. auto.
  - destruct (decode_obj f m q) as [o|] eqn:Eo; [|discriminate].
    match type of H with context [match ?d with | Some _ => _ | None => _ end] =>
      destruct d as [l'|] eqn:El; [|discriminate] end.
    inversion H. subst. cbn. destruct (IHk _ _ El) as [H1 H2]. repeat split; auto.
Qed.

Lemma decode_obj_ok : forall fuel m a o, decode_obj fuel m a = Some o -> obj_at m a o.
Proof.
  induction fuel as [|f IH]; intros m a o H; [discriminate|]. cbn [decode_obj] in H.
  destruct (rdZ m a 4) as [t|] eqn:Et; [|discriminate].
  destruct (Z.eqb_spec t T_NIL) as [E1|N1]. { inversion H; subst. cbn. split; [exact Et|exact I]. }
  destruct (Z.eqb_spec t T_BOOLEAN) as [E2|N2].
  { subst. destruct (rdZ m (a+8) 1) as [b|] eqn:Eb; [|discriminate].
    destruct (Z.eqb_spec b 0) as [->|Nb0]; [inversion H; subst; cbn; split; [exact Et| exact Eb]|].
    destruct (Z.eqb_spec b 1) as [->|Nb1]; [inversion H; subst; cbn; split; [exact Et| exact Eb]|]. discriminate. }
  destruct (Z.eqb_spec t T_POSINT) as [E3|N3].
  { subst. destruct (rdZ m (a+8) 8) as [u|] eqn:Eu; [|discriminate]. inversion H; subst. cbn. auto. }
  destruct (Z.eqb_spec t T_NEGINT) as [E4|N4].
  { subst. destruct (rdZ m (a+8) 8) as [u|] eqn:Eu; [|discriminate].
    destruct (Z.leb_spec 0 u) as [Hu0|Hu0]; [|discriminate]. destruct (Z.ltb_spec u (2^64)) as [Hu1|Hu1]; [|discriminate]. cbn [andb] in H.
    inversion H; subst. cbn [obj_at obj_type]. split; [exact Et|]. unfold u64_at, enc64. rewrite Eu. f_equal.
    rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. }
  destruct (Z.eqb_spec t T_FLOAT32) as [E5|N5].
  { subst. destruct (rdZ m (a+8) 8) as [u|] eqn:Eu; [|discriminate]. inversion H; subst. cbn. auto. }
  destruct (Z.eqb_spec t T_FLOAT64) as [E6|N6].
  { subst. destruct (rdZ m (a+8) 8) as [u|] eqn:Eu; [|discriminate]. inversion H; subst. cbn. auto. }
  assert (SBE : forall C ty, (forall p n, obj_type (C p n) = ty /\ (forall mm b, obj_at mm b (C p n) <-> (u32_at mm b ty /\ u32_at mm (b+8) n /\ u64_at mm (b+16) p))) ->
            t = ty -> dec_sbe m a C = Some o -> obj_at m a o).
  { intros C ty HC -> Hd. unfold dec_sbe in Hd.
    destruct (rdZ m (a+8) 4) as [n|] eqn:En; [|discriminate]. destruct (rdZ m (a+16) 8) as [p|] eqn:Ep; [|discriminate].
    inversion Hd; subst. destruct (HC p n) as [_ HH]. apply HH. repeat split; assumption. }
  destruct (Z.eqb_spec t T_STR) as [E7|N7]. { eapply SBE; eauto. intros; split; [reflexivity|]. intros; cbn; tauto. }
  destruct (Z.eqb_spec t T_BIN) as [E8|N8]. { eapply SBE; eauto. intros; split; [reflexivity|]. intros; cbn; tauto. }
  destruct (Z.eqb_spec t T_EXT) as [E9|N9]. { eapply SBE; eauto. intros; split; [reflexivity|]. intros; cbn; tauto. }
  destruct ((t =? T_ARRAY) || (t =? T_MAP)) eqn:Eam; [|discriminate].
  destruct (rdZ m (a+8) 4) as [n|] eqn:En; [|discriminate]. destruct (rdZ m (a+16) 8) as [p|] eqn:Ep; [|discriminate].
  destruct (Z.ltb_spec n 0) as [Hn|Hn]; [discriminate|].
  match type of H with context [match ?d with | Some _ => _ | None => _ end] =>
      destruct d as [l|] eqn:El; [|discriminate] end.
  apply (decode_kids_ok f m (IH m)) in El. destruct El as [Hl Hlen].
  destruct (Z.eqb_spec t T_ARRAY) as [E10|N10].
  - inversion H; subst. apply obj_at_arr. rewrite Hlen, Z2Nat.id by lia. repeat split; assumption.
  - destruct (Z.eqb_spec t T_MAP) as [E11|N11]; [|cbn in Eam; congruence]. inversion H; subst. apply obj_at_map.
    rewrite Hlen, Z2Nat.id by lia. replace (2 * n / 2) with n by (rewrite Z.mul_comm, Z.div_mul; lia).
    repeat split; assumption.
Qed.

Fixpoint bt_build_aux (fuel : nat) (l : list (Z * Z)) {struct fuel} : btree :=
  match fuel with
  | O => BLeaf
  | S f =>
    match l with
    | [] => BLeaf
    | _ => let k := Nat.div (length l) 2 in
           match skipn k l with
           | [] => BLeaf
           | (a, v) :: r => BNode (bt_build_aux f (firstn k l)) a v (bt_build_aux f r)
           end
    end
  end.
Definition bt_build (l : list (Z * Z)) : btree := bt_build_aux 64 l.

Fixpoint seg_assoc (base : Z) (bs : list Z) : list (Z * Z) :=
  match bs with [] => [] | b :: bs' => (base, b) :: seg_assoc (base + 1) bs' end.
Definition segs_assoc (segs : list (Z * list Z)) : list (Z * Z) := flat_map (fun s => seg_assoc (fst s) (snd s)) segs.
Definition bmem_of_segs (segs : list (Z * list Z)) : btree := bt_build (segs_assoc segs).

Definition live_of_blocks (blocks : list (Z * Z)) (a n : Z) : bool := existsb (fun b => (fst b =? a) && (snd b =? n)) blocks.

Fixpoint bytes_of_Z (n : nat) (z : Z) : list Z :=
  match n with O => [] | S n' => Z.land z 255 :: bytes_of_Z n' (Z.shiftr z 8) end.
Definition zsegs_assoc (segs : list (Z * Z * Z)) : list (Z * Z) :=
  flat_map (fun s => seg_assoc (fst (fst s)) (bytes_of_Z (Z.to_nat (snd (fst s))) (snd s))) segs.
Definition bmem_of_zsegs (segs : list (Z * Z * Z)) : btree := bt_build (zsegs_assoc segs).

Definition bytes_of_words (n : Z) (ws : list Z) : list Z := firstn (Z.to_nat n) (flat_map (bytes_of_Z 8) ws).
Definition wsegs_assoc (segs : list (Z * Z * list Z)) : list (Z * Z) :=
  flat_map (fun s => seg_assoc (fst (fst s)) (bytes_of_words (snd (fst s)) (snd s))) segs.
Definition bmem_of_wsegs (segs : list (Z * Z * list Z)) : btree := bt_build (wsegs_assoc segs).
