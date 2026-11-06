(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
Module MI_Shadow.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hl_ticks (hl : list (Z * N)) (t : N) : Prop := forall ch, In ch hl -> (snd ch <= t)%N.

Lemma stale_hav_add_some cov t hl b tk :
  hl_ticks hl t ->
  stale (hav_add cov t hl) b (Some tk) = ((b <? cov) && (tk <? t)%N) || stale hl b (Some tk).
Proof.
  intros Ht. unfold hav_add, stale. cbn [existsb fst snd].
  destruct ((b <? cov) && (tk <? t)%N) eqn:E; cbn [orb]; [reflexivity|].
  induction hl as [|[c h] hl IH]; [reflexivity|].
  assert (Hh : (h <= t)%N) by (apply (Ht (c, h)); left; reflexivity).
  assert (IH' : existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) (filter (fun ch : Z * N => cov <? fst ch) hl)
                = existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) hl).
  { apply IH. intros ch Hin. apply Ht. right. exact Hin. }
  rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd].
  - rewrite IH'. reflexivity.
  - rewrite IH'. destruct ((b <? c) && (tk <? h)%N) eqn:E2; cbn; [|reflexivity].
    exfalso. apply Bool.andb_true_iff in E2 as [E2 E3]. apply Z.ltb_lt in E2. apply N.ltb_lt in E3.
    assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
    apply Bool.andb_false_iff in E as [E|E]; [apply Z.ltb_ge in E; lia| apply N.ltb_ge in E; lia].
Qed.

Lemma stale_hav_add_none cov t hl b :
  stale (hav_add cov t hl) b None = (b <? cov) || stale hl b None.
Proof.
  unfold hav_add, stale. cbn [existsb fst snd]. rewrite Bool.andb_true_r.
  destruct (b <? cov) eqn:E; cbn [orb]; [reflexivity|].
  induction hl as [|[c h] hl IH]; [reflexivity|].
  rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd]; rewrite ?Bool.andb_true_r.
  - rewrite IH. reflexivity.
  - rewrite IH. destruct (Z.ltb_spec b c); cbn; [|reflexivity]. exfalso.
    assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
    apply Z.ltb_ge in E. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma havoc_units_lookup x y t h u :
  let u0 := x / 16 in let u1 := (y - 1) / 16 in
  let lastcov := (if y mod 16 =? 0 then 16 else y mod 16) in
  (havoc_units x y t h) !! u =
    if (u0 <=? u) && (u <=? u1) then Some (hav_add (if u =? u1 then lastcov else 16) t (default [] (h !! u))) else h !! u.
Proof.
  cbn zeta. unfold havoc_units.
  set (u0 := x / 16). set (u1 := (y - 1) / 16). set (lastcov := if y mod 16 =? 0 then 16 else y mod 16).
  set (F := fun acc : Z * gmap Z (list (Z * N)) => let (u2, h0) := acc in (u2 + 1, <[u2 := hav_add (if u2 =? u1 then lastcov else 16) t (default [] (h0 !! u2))]> h0)).
  destruct (Z.lt_ge_cases (u1 - u0 + 1) 0) as [Hneg|Hnn].
  - (* [comment removed for export] *)
    destruct (u1 - u0 + 1) eqn:E; try lia. cbn.
    destruct (Z.leb_spec u0 u), (Z.leb_spec u u1); cbn; try reflexivity. lia.
  - assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (u0, h) in fst r = u0 + n /\
              forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v).
    { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = u0 + n /\ forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v)); [| | exact Hn].
      - cbn. split; [lia|]. intros v. destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + 0)); cbn; try reflexivity. lia.
      - intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
        destruct (Z.eq_dec v (u0 + k)) as [->|NE].
        + rewrite lookup_insert_eq. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + (k + 1))); cbn; try lia.
          f_equal. f_equal. rewrite IH. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + k)); cbn; try lia. reflexivity.
        + rewrite lookup_insert_ne by congruence. rewrite IH.
          destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + k)), (Z.ltb_spec v (u0 + (k + 1))); cbn; try reflexivity; lia. }
    destruct (GEN (u1 - u0 + 1) Hnn) as [_ G]. rewrite G.
    destruct (Z.leb_spec u0 u), (Z.ltb_spec u (u0 + (u1 - u0 + 1))), (Z.leb_spec u u1); cbn; try reflexivity; lia.
Qed.

Lemma havoc_pages_lookup p0 p1 t h pg :
  (havoc_pages p0 p1 t h) !! pg = if (p0 <=? pg) && (pg <? p1) then Some t else h !! pg.
Proof.
  unfold havoc_pages.
  set (F := fun acc : Z * gmap Z N => let (pg0, h0) := acc in (pg0 + 1, <[pg0 := t]> h0)).
  destruct (Z.lt_ge_cases (p1 - p0) 0) as [Hneg|Hnn].
  - destruct (p1 - p0) eqn:E; try lia. cbn. destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg p1); cbn; try reflexivity. lia.
  - assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (p0, h) in fst r = p0 + n /\
              forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v).
    { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = p0 + n /\ forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v)); [| | exact Hn].
      - cbn. split; [lia|]. intros v. destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + 0)); cbn; try reflexivity. lia.
      - intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
        destruct (Z.eq_dec v (p0 + k)) as [->|NE].
        + rewrite lookup_insert_eq. destruct (Z.leb_spec p0 (p0 + k)), (Z.ltb_spec (p0 + k) (p0 + (k + 1))); cbn; try lia. reflexivity.
        + rewrite lookup_insert_ne by congruence. rewrite IH.
          destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + k)), (Z.ltb_spec v (p0 + (k + 1))); cbn; try reflexivity; lia. }
    destruct (GEN (p1 - p0) Hnn) as [_ G]. rewrite G.
    destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg (p0 + (p1 - p0))), (Z.ltb_spec pg p1); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma div16_mono a b : a <= b -> a / 16 <= b / 16.
Proof. intros. apply Z.div_le_mono; lia. Qed.

Lemma havoc_units_in x y t h o tko :
  x mod 16 = 0 -> x <= o < y ->
  match tko with Some tk => (tk < t)%N | None => True end ->
  stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = true.
Proof.
  intros Hx Ho Htk. rewrite havoc_units_lookup.
  assert (U0 : x / 16 <= o / 16) by (apply div16_mono; lia).
  assert (U1 : o / 16 <= (y - 1) / 16) by (apply div16_mono; lia).
  destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); try lia. cbn [andb default].
  cbn [default id]. unfold hav_add, stale. cbn [existsb fst snd].
  match goal with |- (?a && ?b) || _ = true => enough (E : a && b = true) by (rewrite E; reflexivity) end.
  apply Bool.andb_true_iff. split.
  - apply Z.ltb_lt. destruct (Z.eqb_spec (o / 16) ((y - 1) / 16)) as [E|NE].
    + destruct (Z.eqb_spec (y mod 16) 0) as [Ey|Ny].
      * pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
      * (* [comment removed for export] *)
        pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)).
        pose proof (Z.div_mod y 16 ltac:(lia)).
        pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
        assert (y / 16 = (y - 1) / 16 \/ y / 16 = (y - 1) / 16 + 1) by (pose proof (div16_mono (y - 1) y ltac:(lia)); pose proof (div16_mono y (y - 1 + 16) ltac:(lia)); rewrite <- Z.div_add in * by lia; nia).
        lia.
    + pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - destruct tko as [tk|]; [apply N.ltb_lt; exact Htk| reflexivity].
Qed.

Lemma havoc_units_out x y t h o tko :
  x mod 16 = 0 -> ~ (x <= o < y) ->
  match tko with Some tk => hl_ticks (default [] (h !! (o / 16))) t | None => True end ->
  stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = stale (default [] (h !! (o / 16))) (o mod 16) tko.
Proof.
  intros Hx Ho Htk. rewrite havoc_units_lookup.
  destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); cbn [andb]; try reflexivity.
  cbn [default id].
  (* [comment removed for export] *)
  assert (Hoy : y <= o).
  { destruct (Z.lt_ge_cases o x); [|lia]. exfalso.
    pose proof (Z.div_mod x 16 ltac:(lia)). pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.mod_pos_bound o 16 ltac:(lia)). nia. }
  assert (E : o / 16 = (y - 1) / 16) by (pose proof (div16_mono (y - 1) o ltac:(lia)); lia).
  rewrite E, Z.eqb_refl.
  pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)). pose proof (Z.div_mod y 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
  assert (Ny : y mod 16 <> 0 /\ y mod 16 <= o mod 16) by nia.
  destruct (Z.eqb_spec (y mod 16) 0) as [|_]; [lia|].
  destruct tko as [tk|].
  - rewrite stale_hav_add_some by (rewrite <- E; exact Htk). destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
  - rewrite stale_hav_add_none. destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
Qed.

Lemma hav_add_ticks cov t hl : hl_ticks hl t -> hl_ticks (hav_add cov t hl) t.
Proof.
  intros H ch Hin. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
  apply H. apply list_elem_of_In. apply list_elem_of_In in Hin. apply list_elem_of_filter in Hin. tauto.
Qed.

Lemma havoc_units_ticks x y t h :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) ->
  forall u hl, havoc_units x y t h !! u = Some hl -> hl_ticks hl t.
Proof.
  intros Hh u hl. rewrite havoc_units_lookup. destruct (_ && _).
  - intros E. inversion E. subst. apply hav_add_ticks. destruct (h !! u) as [hl0|] eqn:E0; cbn; [eapply Hh; exact E0| intros ? []].
  - apply Hh.
Qed.

Lemma havoc_units_default_ticks x y t h o :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) -> hl_ticks (default [] (havoc_units x y t h !! o)) t.
Proof.
  intros Hh. destruct (havoc_units x y t h !! o) as [hl|] eqn:E; cbn; [eapply havoc_units_ticks; eauto| intros ? []].
Qed.

Lemma default_ticks (h : gmap Z (list (Z * N))) t o :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) -> hl_ticks (default [] (h !! o)) t.
Proof. intros Hh. destruct (h !! o) as [hl|] eqn:E; cbn; [eapply Hh; eauto| intros ? []]. Qed.

Section HAVOC.
Variables (p : aptr) (n : Z) (st : mstate).
Hypothesis Al : snd p mod 16 = 0.
Hypothesis Hn : 0 < n.
Let sh := get_shadow st (fst p).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).
Let a := snd p.
Let b := snd p + n.
Let t := s_tick st.
Let fp := (a + 4095) / 4096.
Let lp := b / 4096.

Lemma havoc_shadow :
  get_shadow (havoc p n st) (fst p) =
    mkShadow (r_cells sh)
      (if fp <? lp then
         (if lp * 4096 <? b then havoc_units (lp * 4096) b t (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh)
          else (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh))
       else havoc_units a b t (r_hav sh))
      (if fp <? lp then havoc_pages fp lp t (r_havp sh) else r_havp sh).
Proof.
  unfold havoc. destruct (Z.leb_spec n 0); [lia|]. rewrite get_shadow_upd_shadow, N.eqb_refl.
  subst sh a b t fp lp. destruct (_ <? _); [|reflexivity]. destruct (_ <? _); destruct (_ <? _); reflexivity.
Qed.

Lemma havoc_other_region rid : rid <> fst p -> get_shadow (havoc p n st) rid = get_shadow st rid.
Proof.
  intros NE. unfold havoc. destruct (n <=? 0); [reflexivity|]. rewrite get_shadow_upd_shadow.
  destruct (N.eqb_spec rid (fst p)); [congruence| reflexivity].
Qed.

Lemma fp_ge : a <= fp * 4096.
Proof. subst fp. pose proof (Z.div_mod (a + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (a + 4095) 4096 ltac:(lia)). lia. Qed.
Lemma lp_le : lp * 4096 <= b.
Proof. subst lp. pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.mod_pos_bound b 4096 ltac:(lia)). lia. Qed.
Lemma fp_al : (fp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.
Lemma lp_al : (lp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
Lemma havoc_stale_out o tko :
  ~ (a <= o < b) ->
  match tko with Some tk => True | None => True end ->
  let sh' := get_shadow (havoc p n st) (fst p) in
  stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko
  = stale_pg (r_havp sh !! (o / 4096)) tko || stale (default [] (r_hav sh !! (o / 16))) (o mod 16) tko.
Proof.
  intros Ho _. rewrite havoc_shadow. cbn [r_hav r_havp].
  pose proof fp_ge. pose proof lp_le.
  assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
            match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
  { intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
  destruct (Z.ltb_spec fp lp).
  - f_equal.
    + rewrite havoc_pages_lookup. destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); cbn [andb]; try reflexivity.
      exfalso. apply Ho. pose proof (Z.div_mod o 4096 ltac:(lia)). pose proof (Z.mod_pos_bound o 4096 ltac:(lia)). nia.
    + destruct (Z.ltb_spec (lp * 4096) b); destruct (Z.ltb_spec a (fp * 4096)).
      * rewrite havoc_units_out; [| apply lp_al| lia| apply TKo; apply havoc_units_ticks; exact TK].
        rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
      * rewrite havoc_units_out; [reflexivity| apply lp_al| lia| apply TKo; exact TK].
      * rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
      * reflexivity.
  - f_equal. rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
Qed.

(* [comment removed for export] *)
Lemma havoc_stale_in o tko :
  a <= o < b ->
  match tko with Some tk => (tk < t)%N | None => True end ->
  let sh' := get_shadow (havoc p n st) (fst p) in
  stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko = true.
Proof.
  intros Ho Htk. rewrite havoc_shadow. cbn [r_hav r_havp].
  pose proof fp_ge. pose proof lp_le.
  assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
            match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
  { intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
  apply Bool.orb_true_iff.
  destruct (Z.ltb_spec fp lp).
  - destruct (Z.lt_ge_cases o (fp * 4096)) as [Hhead|Hnh].
    + right. destruct (Z.ltb_spec a (fp * 4096)); [|lia].
      destruct (Z.ltb_spec (lp * 4096) b).
      * rewrite havoc_units_out; [| apply lp_al| nia| apply TKo; apply havoc_units_ticks; exact TK].
        apply havoc_units_in; [exact Al| lia| exact Htk].
      * apply havoc_units_in; [exact Al| lia| exact Htk].
    + destruct (Z.lt_ge_cases o (lp * 4096)) as [Hmid|Htail].
      * left. rewrite havoc_pages_lookup.
        assert (fp <= o / 4096 < lp).
        { split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]. }
        destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); try lia. cbn [andb].
        destruct tko as [tk|]; cbn; [apply N.ltb_lt; exact Htk| reflexivity].
      * right. destruct (Z.ltb_spec (lp * 4096) b); [|lia].
        apply havoc_units_in; [apply lp_al| lia| exact Htk].
  - right. apply havoc_units_in; [exact Al| lia| exact Htk].
Qed.

(* [comment removed for export] *)
Lemma cell_read_havoc_out q :
  ~ (fst q = fst p /\ a <= snd q < b) ->
  cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros Hq. destruct (N.eq_dec (fst q) (fst p)) as [E|NE].
  - rewrite E. assert (Ho : ~ (a <= snd q < b)) by tauto.
    unfold cell_read. pose proof (havoc_stale_out (snd q)) as SO. cbn zeta in SO.
    replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
    subst sh. destruct (r_cells (get_shadow st (fst p)) !! snd q) as [[v tk]|].
    + rewrite (SO (Some tk) Ho I). reflexivity.
    + rewrite (SO None Ho I). reflexivity.
  - rewrite havoc_other_region by exact NE. reflexivity.
Qed.

Lemma cell_read_havoc_in q :
  fst q = fst p -> a <= snd q < b ->
  (forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < t)%N) ->
  exists h, cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = Unknown h.
Proof.
  intros E Ho Htk. rewrite E. unfold cell_read.
  replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
  pose proof (havoc_stale_in (snd q)) as SI. cbn zeta in SI.
  destruct (r_cells sh !! snd q) as [[v tk]|] eqn:Ec.
  - rewrite (SI (Some tk) Ho (Htk v tk eq_refl)). eauto.
  - rewrite (SI None Ho I). eauto.
Qed.

Lemma havoc_cells rid : r_cells (get_shadow (havoc p n st) rid) = r_cells (get_shadow st rid).
Proof.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [rewrite havoc_shadow; reflexivity| rewrite havoc_other_region by exact NE; reflexivity].
Qed.

Lemma havoc_ticks rid :
  (forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl t) ->
  (forall pg tk, r_havp (get_shadow st rid) !! pg = Some tk -> (tk <= t)%N) ->
  (forall u hl, r_hav (get_shadow (havoc p n st) rid) !! u = Some hl -> hl_ticks hl t)
  /\ (forall pg tk, r_havp (get_shadow (havoc p n st) rid) !! pg = Some tk -> (tk <= t)%N).
Proof.
  intros H1 H2. destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite havoc_other_region by exact NE; auto].
  rewrite havoc_shadow. cbn [r_hav r_havp]. split.
  - destruct (fp <? lp); [| apply havoc_units_ticks; exact TK].
    destruct (lp * 4096 <? b); destruct (a <? fp * 4096); repeat apply havoc_units_ticks; exact TK.
  - destruct (fp <? lp); [| exact H2]. intros pg tk. rewrite havoc_pages_lookup. destruct (_ && _); [| apply H2].
    intros X. inversion X. lia.
Qed.
End HAVOC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HDR.
Variables (bp : aptr) (st : mstate).
Hypothesis Al : snd bp mod 16 = 0.
Let sh := get_shadow st (fst bp).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).

Lemma hdr_havoc_shadow :
  get_shadow (hdr_havoc bp st) (fst bp) =
  mkShadow (r_cells sh) (<[snd bp / 16 := hav_add 12 (s_tick st) (default [] (r_hav sh !! (snd bp / 16)))]> (r_hav sh)) (r_havp sh).
Proof. unfold hdr_havoc. rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity. Qed.

Lemma hdr_havoc_other_region rid : rid <> fst bp -> get_shadow (hdr_havoc bp st) rid = get_shadow st rid.
Proof. intros NE. unfold hdr_havoc. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst bp)); [congruence| reflexivity]. Qed.

Lemma cell_read_hdr_havoc_out q :
  ~ (fst q = fst bp /\ snd bp <= snd q < snd bp + 12) ->
  cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros Hq. destruct (N.eq_dec (fst q) (fst bp)) as [E|NE]; [| rewrite hdr_havoc_other_region by exact NE; reflexivity].
  rewrite E. rewrite hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
  destruct (Z.eq_dec (snd q / 16) (snd bp / 16)) as [Eu|Nu].
  - rewrite Eu, lookup_insert_eq. cbn [default id].
    assert (Hb : 12 <= snd q mod 16).
    { pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (snd q) 16 ltac:(lia)).
      assert (~ (snd bp <= snd q < snd bp + 12)) by tauto. nia. }
    destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|].
    + rewrite stale_hav_add_some by (apply default_ticks; exact TK). destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [andb orb]. rewrite <- Eu. reflexivity.
    + rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [orb]. rewrite <- Eu. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma cell_read_hdr_havoc_in q :
  fst q = fst bp -> snd bp <= snd q < snd bp + 12 ->
  (forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < s_tick st)%N) ->
  exists h, cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = Unknown h.
Proof.
  intros E Ho Htk. rewrite E, hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
  assert (Eu : snd q / 16 = snd bp / 16).
  { pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). symmetry. apply Z.div_unique with (r := snd q - snd bp); lia. }
  rewrite Eu, lookup_insert_eq. cbn [default id].
  assert (Hb : snd q mod 16 < 12).
  { pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). nia. }
  destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|] eqn:Ec.
  - unfold hav_add, stale. cbn [existsb fst snd].
    destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. rewrite (proj2 (N.ltb_lt _ _)) by (eapply Htk; reflexivity).
    cbn [andb orb]. rewrite Bool.orb_true_r. eauto.
  - rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. cbn [orb]. rewrite Bool.orb_true_r. eauto.
Qed.

Lemma hdr_havoc_cells rid : r_cells (get_shadow (hdr_havoc bp st) rid) = r_cells (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [rewrite hdr_havoc_shadow; reflexivity| rewrite hdr_havoc_other_region by exact NE; reflexivity]. Qed.

Lemma hdr_havoc_ticks rid :
  (forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl (s_tick st)) ->
  (forall u hl, r_hav (get_shadow (hdr_havoc bp st) rid) !! u = Some hl -> hl_ticks hl (s_tick st))
  /\ r_havp (get_shadow (hdr_havoc bp st) rid) = r_havp (get_shadow st rid).
Proof.
  intros H1. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [| rewrite hdr_havoc_other_region by exact NE; auto].
  rewrite hdr_havoc_shadow. cbn [r_hav r_havp]. split; [| reflexivity].
  intros u hl. destruct (Z.eq_dec u (snd bp / 16)) as [->|Nu].
  - rewrite lookup_insert_eq. intros X. inversion X. subst. apply hav_add_ticks. apply default_ticks. exact TK.
  - rewrite lookup_insert_ne by congruence. apply H1.
Qed.
End HDR.


End CeilWrap.
End MI_Shadow.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Module MI_Ext2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Section EXT2.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).

Lemma inv_M_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> inv_M X st LS -> inv_M X st' LS.
Proof.
  intros HM HG I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.

Lemma inv_L_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> (forall h, get_head st' h = get_head st h) ->
  inv_L st LS -> inv_L st' LS.
Proof.
  intros HM HG HE I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. apply (dll_ext_metas st st' HM). apply L2.
  - exact L3.
  - exact L4.
  - intros m. rewrite !ME. apply L5.
  - intros m Hm. rewrite !ME. apply L6. exact Hm.
  - intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
  - exact L9.
Qed.

Lemma group_ok_ext m b ai : s_metas st' = s_metas st -> s_slots st' = s_slots st ->
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> fst b = rid -> s_regions st' !! rid = Some r) ->
  group_ok X st LS m b ai -> group_ok X st' LS m b ai.
Proof.
  intros HM HS HR I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HS; try assumption.
  - intros Hml. destruct (G13 Hml) as (H0 & r & Hr & Hk & E1 & E2). split; [exact H0|]. exists r. split; [| auto]. apply HR; auto.
  - intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.

Lemma inv_S_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> s_slots st' = s_slots st ->
  inv_S X st BL -> inv_S X st' BL.
Proof.
  intros HM HG HS I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
  - intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
  - intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
  - intros c Hc. rewrite HS. apply S4. exact Hc.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
Qed.
End EXT2.


End CeilWrap.
End MI_Ext2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Module MI_Pres2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition inT (rid : N) (lo hi : Z) (q : aptr) : Prop := fst q = rid /\ lo <= snd q < hi.

Section WRITE_T.
Variables (X : extras) (st st' : mstate) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis IM : inv_M X st LS.
Hypothesis IG : inv_G X st LS.
Hypothesis IS : inv_S X st BL.
Hypothesis ISH : inv_SH st BL.
Variables (m bm : aptr) (i : Z).
Hypothesis Hm : hosts st bm m.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st m).
Hypothesis NH : s_groups st !! (fst bm, sstart (MR st m) i) = None.
Hypothesis NB : forall k, In k BL -> bslot k <> (fst bm, sstart (MR st m) i).
Let lo := sstart (MR st m) i - 3.
Let hi := sstart (MR st m) (i + 1) - 4.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall q, ~ inT (fst bm) lo hi q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

Local Notation R := (MR st).

Lemma known_out q v : ~ inT (fst bm) lo hi q -> known st q v -> known st' q v.
Proof. intros Hq K. unfold known, SHd in *. rewrite RD by exact Hq. exact K. Qed.
Lemma unknown_out q : ~ inT (fst bm) lo hi q -> unknown st q -> unknown st' q.
Proof. intros Hq K. unfold unknown, SHd in *. rewrite RD by exact Hq. exact K. Qed.

Lemma not_inT_lo q : snd q < lo -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [H1 _]]. lia. Qed.
Lemma not_inT_hi q : hi <= snd q -> ~ inT (fst bm) lo hi q.
Proof. intros H [_ [_ H2]]. lia. Qed.
Lemma not_inT_rid q : fst q <> fst bm -> ~ inT (fst bm) lo hi q.
Proof. intros H [H1 _]. exact (H H1). Qed.

Theorem inv_SH_write_T : inv_SH st' BL.
Proof using CE DOM Hi Hm IG IM IS ISH NB NH RD TK TKS.
  pose proof (ce_metas _ _ CE) as HMe. pose proof (ce_groups _ _ CE) as HG. pose proof (ce_slots _ _ CE) as HS. pose proof (ce_regions _ _ CE) as HR.
  pose proof (MR_ext st st' HMe) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct ISH as [D1 D2 D3 D4 D5 D6]. constructor.
  - intros rid sh H. rewrite HR. eapply DOM. exact H.
  - intros rid sh H. rewrite TK. eapply TKS. exact H.
  - (* [comment removed for export] *)
    intros b2 m2 i2 Hb2 Hi2. apply HE in Hb2. rewrite ME in Hi2 |- *.
    apply known_out; [| exact (D3 b2 m2 i2 Hb2 Hi2)].
    destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
    unfold cnt_of in Hi2.
    destruct (aptr_eq_dec m2 m) as [Em|NEm]; [destruct (Z.eq_dec i2 i) as [Ei|NEi]|].
    + subst m2 i2. apply not_inT_lo. subst lo hi. cbn. unfold IB. lia.
    + destruct (sep_hdr0 _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 (or_intror NEi)) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
    + destruct (sep_hdr0 _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 (or_introl NEm)) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
  - (* [comment removed for export] *)
    intros b2 m2 o Hb2 Ho. apply HE in Hb2. apply unknown_out; [| exact (D4 b2 m2 o Hb2 Ho)].
    destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
    destruct (sep_ghdr _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 Hb2 Ef) as [A|A];
      [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; unfold IB; lia.
  - (* [comment removed for export] *)
    intros b2 m2 p2 i2 Hb2 Hml Hs. apply HE in Hb2. rewrite ME in Hml. rewrite HS in Hs. rewrite !ME.
    destruct (D5 b2 m2 p2 i2 Hb2 Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp2 Hp2] & Hi2 & Eb2).
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hp2) in Eb2.
    assert (OUT : forall d, 1 <= d <= 3 -> ~ inT (fst bm) lo hi (fst b2, snd b2 - d)).
    { intros d Hd. subst b2. cbn [fst snd].
      destruct (N.eq_dec (fst bp2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
      assert (NE : p2 <> m \/ i2 <> i).
      { destruct (aptr_eq_dec p2 m) as [->|]; [right| left; assumption]. intros ->.
        pose proof (hosts_inj _ _ _ IM _ _ _ Hp2 Hm). subst bp2. destruct Hb2 as [ai2 Hb2]. rewrite Hb2 in NH. discriminate. }
      destruct (sep_h3 _ _ _ _ IM IG IS m bm i Hm Hi NH p2 bp2 i2 Hp2 Ef Hi2 NE) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; lia. }
    split; [exists v3; split; [apply known_out; [apply (OUT 3); lia| exact K3]| auto]|].
    split; [apply known_out; [apply (OUT 2); lia| exact K2]|].
    split; [apply known_out; [apply (OUT 1); lia| exact K1]| exact Q].
  - (* [comment removed for export] *)
    intros k m2 i2 Hk Hs. rewrite HS in Hs. rewrite !ME.
    destruct (D6 k m2 i2 Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b2 Hb2] & Hi2 & Ek).
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb2) in Ek.
    destruct (is_blocks _ _ _ IS k Hk) as (m2' & i2' & Hs' & Hoff & Hsz & Hfit). rewrite Hs in Hs'. inversion Hs'. subst m2' i2'. clear Hs'.
    pose proof (stride_ge _ _ _ IG _ _ Hb2) as [SG _].
    assert (NH2 : s_groups st !! (fst b2, sstart (R m2) i2) = None).
    { destruct Hb2 as [ai2 Hb2']. pose proof (is_part _ _ _ IS _ _ _ _ Hb2' Hi2) as P. cbn zeta in P.
      rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai2 Hb2')) in P.
      unfold one5 in P. destruct (s_groups st !! (fst b2, sstart (R m2) i2)) eqn:E; [| reflexivity]. exfalso.
      assert (U : In (fst b2, sstart (R m2) i2) (map bslot BL)) by (rewrite <- Ek; apply in_map; exact Hk).
      assert (H : s_groups st !! (fst b2, sstart (R m2) i2) <> None) by congruence. clear - P U H. tauto. }
    assert (NE : m2 <> m \/ i2 <> i).
    { destruct (aptr_eq_dec m2 m) as [->|]; [right| left; assumption]. intros ->.
      pose proof (hosts_inj _ _ _ IM _ _ _ Hb2 Hm). subst b2. exact (NB k Hk Ek). }
    assert (OUT : forall o, sstart (R m2) i2 - 4 <= o < sstart (R m2) (i2 + 1) - 4 -> ~ inT (fst bm) lo hi (fst (bslot k), o)).
    { intros o Ho. rewrite Ek. cbn [fst].
      destruct (N.eq_dec (fst b2) (fst bm)) as [Ef|Nf]; [| apply not_inT_rid; exact Nf].
      destruct (sep_ext _ _ _ _ IM IG IS m bm i Hm Hi NH m2 b2 i2 Hb2 Ef Hi2 NE NH2) as [A|A];
        [apply not_inT_lo| apply not_inT_hi]; cbn; subst lo hi; lia. }
    assert (Esnd : snd (bslot k) = sstart (R m2) i2) by (rewrite Ek; reflexivity).
    rewrite sstart_succ in OUT. unfold UNIT, IB in *.
    split; [apply known_out; [apply OUT; lia| exact A1]|].
    split; [apply known_out; [apply OUT; lia| exact A2]|].
    split; [apply known_out; [apply OUT; lia| exact A3]|].
    split; [apply known_out; [apply OUT; lia| exact A4]|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6).
      repeat split; try (apply known_out; [apply OUT; lia| assumption]). exact B6.
    + split; [intros Hr; apply known_out; [apply OUT; lia| apply A7; exact Hr]|].
      intros a Ha. apply unknown_out; [apply OUT; lia| apply A8; exact Ha].
Qed.
End WRITE_T.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma inv_R_X X X' st L : x_orph X' = x_orph X -> inv_R X st L -> inv_R X' st L.
Proof. intros E I. destruct I; constructor; try assumption. rewrite E. assumption. Qed.
Lemma inv_M_X X X' st LS : x_idle X' = x_idle X -> x_zomb X' = x_zomb X -> inv_M X st LS -> inv_M X' st LS.
Proof. intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; assumption. Qed.
Lemma group_ok_X X X' st LS m b ai : x_fresh X' = x_fresh X -> group_ok X st LS m b ai -> group_ok X' st LS m b ai.
Proof. intros E I. destruct I; constructor; rewrite ?E; assumption. Qed.
Lemma inv_G_X X X' st LS : x_fresh X' = x_fresh X -> x_orph X' = x_orph X -> inv_G X st LS -> inv_G X' st LS.
Proof.
  intros E1 E2 I. destruct I; constructor; rewrite ?E1, ?E2; try assumption.
  intros. eapply group_ok_X; [exact E1|]. eauto.
Qed.

(* [comment removed for export] *)
Lemma inv_SH_incl st BL BL' : (forall k, In k BL' -> In k BL) -> inv_SH st BL -> inv_SH st BL'.
Proof. intros Hsub I. destruct I; constructor; try assumption. intros k m i Hk Hs. apply ish_blk; [apply Hsub; exact Hk| exact Hs]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bl_remove_split BL k : NoDup (map bslot BL) -> In k BL ->
  exists l1 l2, BL = l1 ++ k :: l2 /\ bl_remove (bslot k) BL = l1 ++ l2 /\ ~ In (bslot k) (map bslot l1) /\ ~ In (bslot k) (map bslot l2).
Proof.
  induction BL as [|b BL IH]; intros ND Hin; [destruct Hin|].
  cbn in ND. apply NoDup_cons in ND as [N1 N2].
  destruct Hin as [<-|Hin].
  - exists [], BL. cbn. rewrite aptr_eqb_refl. repeat split; auto. intros H. apply N1. apply list_elem_of_In. exact H.
  - destruct (IH N2 Hin) as (l1 & l2 & E1 & E2 & M1 & M2).
    assert (NE : bslot b <> bslot k).
    { intros E. apply N1. rewrite E. apply list_elem_of_In. apply in_map. exact Hin. }
    exists (b :: l1), l2. cbn. rewrite (aptr_eqb_neq (bslot b) (bslot k)) by exact NE. rewrite E1, E2 at 1. rewrite <- E1.
    repeat split; auto. cbn. intros [H|H]; [exact (NE H)| exact (M1 H)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section REMOVE_BLOCK.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (k : blk).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hk : In k BL.
Hypothesis NP : x_pend X = None.
Let X' := mkX (x_idle X) (x_zomb X) (Some (bslot k)) (x_orph X) (x_fresh X).
Let BL' := bl_remove (bslot k) BL.
(* [comment removed for export] *)
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall m i, s_slots st !! (bslot k) = Some (m, i) ->
  forall q, ~ inT (fst (bslot k)) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).

Theorem INVL_remove_block : INVL X' st' L BL' LS.
Proof using CE DOM Hk INV NP RD TK TKS.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & Hoff & Hsz & Hfit).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
  destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2).
  assert (SUB : forall k', In k' BL' -> In k' BL /\ bslot k' <> bslot k).
  { intros k' H. subst BL'. rewrite EBL' in H. rewrite EBL. apply in_app_iff in H. split.
    - apply in_app_iff. cbn. tauto.
    - intros E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H. }
  (* [comment removed for export] *)
  assert (IS' : inv_S X' st BL').
  { destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
    - exact S1.
    - exact S2.
    - intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
      rewrite NP in P.
      assert (MEMk : In (slot_start' (MR st m2) i2) (map bslot BL) <->
                     In (slot_start' (MR st m2) i2) (map bslot BL') \/ slot_start' (MR st m2) i2 = bslot k).
      { subst BL'. rewrite EBL' , EBL. rewrite !map_app. cbn. rewrite !in_app_iff. cbn. intuition congruence. }
      assert (NOTk : In (slot_start' (MR st m2) i2) (map bslot BL') -> slot_start' (MR st m2) i2 <> bslot k).
      { intros H E. subst BL'. rewrite EBL' in H. rewrite map_app, in_app_iff in H. rewrite E in H. tauto. }
      unfold one5 in P |- *.
      assert (D : @eq (option aptr) (Some (bslot k)) (Some (slot_start' (MR st m2) i2)) <-> slot_start' (MR st m2) i2 = bslot k) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
      assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
      set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
      set (U' := In (slot_start' (MR st m2) i2) (map bslot BL')) in *.
      set (E := slot_start' (MR st m2) i2 = bslot k) in *.
      set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
      set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
      set (P5 := @eq (option aptr) (Some (bslot k)) (Some (slot_start' (MR st m2) i2))) in *.
      set (Q5 := None = Some (slot_start' (MR st m2) i2)) in *.
      fold P5. fold Q5 in P. clearbody U U' E A F Hh P5 Q5. clear - P MEMk NOTk D N5. tauto.
    - intros s Hs'. cbn in Hs'. inversion Hs'. subst s. rewrite Hs. discriminate.
    - subst BL'. rewrite EBL'. pose proof S5 as ND. rewrite EBL in ND. rewrite !map_app in ND |- *. cbn in ND.
      apply NoDup_app in ND as (A1 & A2 & A3). apply NoDup_cons in A3 as [_ A3].
      apply NoDup_app. split; [exact A1|]. split; [| exact A3]. intros x Hx Hx2. apply (A2 x Hx). right. exact Hx2.
    - intros k' Hk'. apply S6. apply SUB. exact Hk'. }
  assert (ISH' : inv_SH st' BL').
  { eapply (inv_SH_write_T X' st st' BL' LS (inv_M_X X X' st LS eq_refl eq_refl IM) (inv_G_X X X' st LS eq_refl eq_refl IG) IS'); try eassumption.
    - apply (inv_SH_incl st BL). { intros k' H. apply SUB. exact H. } exact ISH.
    - (* [comment removed for export] *)
      destruct Hm as [ai Hm']. pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P. cbn zeta in P.
      rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')) in P. unfold one5 in P.
      destruct (s_groups st !! (fst bm, sstart (MR st m) i)) eqn:E; [| reflexivity]. exfalso.
      assert (U : In (fst bm, sstart (MR st m) i) (map bslot BL)) by (rewrite <- Ek; apply in_map; exact Hk).
      assert (H : s_groups st !! (fst bm, sstart (MR st m) i) <> None) by congruence. tauto.
    - intros k' Hk' E. destruct (SUB k' Hk') as [_ NE]. apply NE. rewrite E, Ek. reflexivity.
    - intros q Hq. apply (RD m i Hs). rewrite Ek. exact Hq. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
  - apply (inv_A_ctrl st st' CE). exact IA.
  - apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ctrl st st' LS CE). exact IL.
  - apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
  - apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
  - exact ISH'.
Qed.

Lemma remove_block_members k' : In k' BL' <-> In k' BL /\ bslot k' <> bslot k.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2).
  subst BL'. rewrite EBL', EBL. rewrite !in_app_iff. cbn. split.
  - intros H. split; [tauto|]. intros E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H.
  - intros [[H|[<-|H]] NE]; [tauto| congruence| tauto].
Qed.
End REMOVE_BLOCK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition blk_shadow_ok (st : mstate) (k : blk) (m : aptr) (i : Z) : Prop :=
  let rid := fst (bslot k) in
  let p := snd (bslot k) + UNIT * boff k in
  let e := snd (bslot k) + get_stride (MR st m) - IB in
  let res := e - p - bsize k in
  let q := (p - snd (gbase (MR st m)) - UNIT) / UNIT in
  known st (rid, p - 4) 0
  /\ known st (rid, p - 3) (i + 32 * Z.min res 5)
  /\ known st (rid, p - 2) (byte_of q 0) /\ known st (rid, p - 1) (byte_of q 1) /\ 0 <= q < 2^16
  /\ (5 <= res -> known st (rid, e - 4) (byte_of res 0) /\ known st (rid, e - 3) (byte_of res 1)
                /\ known st (rid, e - 2) (byte_of res 2) /\ known st (rid, e - 1) (byte_of res 3)
                /\ known st (rid, e - 5) 0 /\ res < 2^32)
  /\ (0 < res -> known st (rid, e - res) 0)
  /\ (forall a, p <= a < p + bsize k -> unknown st (rid, a)).

Lemma inv_SH_cons st BL k m i :
  inv_SH st BL -> s_slots st !! (bslot k) = Some (m, i) -> blk_shadow_ok st k m i -> inv_SH st (k :: BL).
Proof.
  intros I Hs Hk. destruct I; constructor; try assumption.
  intros k' m' i' [<-|Hk'] Hs'.
  - rewrite Hs in Hs'. inversion Hs'. subst. exact Hk.
  - apply ish_blk; assumption.
Qed.

Section ADD_BLOCK.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z).
Let k : blk := ((c, off), n).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = Some c.
Let X' := mkX (x_idle X) (x_zomb X) None (x_orph X) (x_fresh X).
Let BL' := k :: BL.
Hypothesis CE : ctrl_eq st st'.
Hypothesis TK : s_tick st' = s_tick st.
Hypothesis RD : forall m i, s_slots st !! c = Some (m, i) ->
  forall q, ~ inT (fst c) (sstart (MR st m) i - 3) (sstart (MR st m) (i + 1) - 4) q ->
  cell_read (get_shadow st' (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Hypothesis DOM : forall rid sh, s_shadow st' !! rid = Some sh -> exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup.
Hypothesis TKS : forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o v t, r_cells sh !! o = Some (v, t) -> 0 <= v < 256 /\ (t <= s_tick st)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N).
Hypothesis BLK : forall m i, s_slots st !! c = Some (m, i) ->
  0 <= off <= 255 /\ 0 <= n /\ UNIT * off + n <= get_stride (MR st m) - IB /\ blk_shadow_ok st' k m i.

Theorem INVL_add_block : INVL X' st' L BL' LS.
Proof using BLK CE DOM HP INV RD TK TKS.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (s_slots st !! c) as [[m i]|] eqn:Hs. 2:{ exfalso. exact (is_pend _ _ _ IS c HP Hs). }
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Ek).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hm) in Ek.
  destruct (BLK m i eq_refl) as (Hoff & Hn & Hfit & SHK).
  (* [comment removed for export] *)
  destruct Hm as [ai Hm'].
  pose proof (is_part _ _ _ IS _ _ _ _ Hm' Hi) as P0. cbn zeta in P0.
  rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai Hm')), <- Ek, HP in P0.
  assert (NU : ~ In c (map bslot BL)) by (unfold one5 in P0; tauto).
  assert (NH : s_groups st !! c = None).
  { destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso. assert (s_groups st !! c <> None) by congruence. unfold one5 in P0. tauto. }
  assert (IS' : inv_S X' st BL').
  { destruct IS as [S1 S2 S3 S4 S5 S6]. constructor.
    - exact S1.
    - exact S2.
    - intros b m2 ai2 i2 Hb Hi2. pose proof (S3 b m2 ai2 i2 Hb Hi2) as P. cbn zeta in P |- *. cbn [x_pend X'].
      rewrite HP in P. subst BL'.
      assert (EQm : In (slot_start' (MR st m2) i2) (map bslot (k :: BL)) <-> c = slot_start' (MR st m2) i2 \/ In (slot_start' (MR st m2) i2) (map bslot BL)) by (cbn; tauto).
      unfold one5 in P |- *. rewrite EQm.
      assert (D : @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2)) <-> c = slot_start' (MR st m2) i2) by (split; [intros H; inversion H; reflexivity| intros ->; reflexivity]).
      assert (N5 : ~ (@None aptr = Some (slot_start' (MR st m2) i2))) by discriminate.
      assert (NU' : c = slot_start' (MR st m2) i2 -> ~ In (slot_start' (MR st m2) i2) (map bslot BL)) by (intros <-; exact NU).
      set (U := In (slot_start' (MR st m2) i2) (map bslot BL)) in *.
      set (E := c = slot_start' (MR st m2) i2) in *.
      set (A := tbit (m_avail (MR st m2)) i2 = true) in *. set (F := tbit (m_freed (MR st m2)) i2 = true) in *.
      set (Hh := s_groups st !! slot_start' (MR st m2) i2 <> None) in *.
      set (P5 := @eq (option aptr) (Some c) (Some (slot_start' (MR st m2) i2))) in *.
      set (Q5 := @eq (option aptr) None (Some (slot_start' (MR st m2) i2))) in *.
      clearbody U E A F Hh P5 Q5. clear - P D N5 NU'. tauto.
    - intros s Hs'. cbn in Hs'. discriminate.
    - subst BL'. cbn. apply NoDup_cons. split; [| exact S5]. intros H. apply NU. apply list_elem_of_In. exact H.
    - intros k' [<-|Hk']; [| apply S6; exact Hk'].
      exists m, i. cbn. auto. }
  assert (ISH' : inv_SH st' BL').
  { apply (inv_SH_cons st' BL k m i).
    - eapply (inv_SH_write_T X st st' BL LS IM IG IS); try eassumption.
      + exists ai. exact Hm'.
      + rewrite <- Ek. exact NH.
      + intros k' Hk' E. apply NU. rewrite Ek, <- E. apply in_map. exact Hk'.
      + intros q Hq. apply (RD m i eq_refl). rewrite Ek. exact Hq.
    - rewrite (ce_slots _ _ CE). exact Hs.
    - exact SHK. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_ctrl X' st st' L CE). apply (inv_R_X X); [reflexivity| exact IR].
  - apply (inv_A_ctrl st st' CE). exact IA.
  - apply (inv_M_ctrl X' st st' LS CE). apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ctrl st st' LS CE). exact IL.
  - apply (inv_G_ctrl X' st st' LS CE). apply (inv_G_X X); [reflexivity| reflexivity| exact IG].
  - apply (inv_S_ctrl X' st st' BL' CE). exact IS'.
  - exact ISH'.
Qed.
End ADD_BLOCK.


End CeilWrap.
End MI_Pres2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Module MI_Pres3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext MI_Ext2 MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 MI_Pres2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ctx_scalars_eq (c c' : mctx) : Prop := mkCS {
  cs_secret : c_secret c' = c_secret c;
  cs_init : c_init_done c' = c_init_done c;
  cs_fmh : c_free_meta_head c' = c_free_meta_head c;
  cs_am : c_avail_meta c' = c_avail_meta c;
  cs_amc : c_avail_meta_count c' = c_avail_meta_count c;
  cs_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
  cs_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
  cs_mah : c_meta_area_head c' = c_meta_area_head c;
  cs_mat : c_meta_area_tail c' = c_meta_area_tail c;
  cs_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
  cs_active : c_active c' = c_active c;
  cs_usage : c_usage c' = c_usage c;
  cs_brk : c_brk c' = c_brk c;
  (* [comment removed for export] *)
  cs_mc : 0 <= c_mmap_counter c' < 2^32;
  cs_seq : 0 <= c_seq c' < 256;
  cs_bounces : forall i v, c_bounces c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256;
  cs_unmap : forall i v, c_unmap_seq c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256
}.

Section CTX.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (f : mctx -> mctx).
Hypothesis INV : INVL X st L BL LS.
Hypothesis CS : ctx_scalars_eq (s_ctx st) (f (s_ctx st)).
Let st' := upd_ctx f st.

Theorem INVL_ctx_scalars : INVL X st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH). destruct CS as [cs_secret cs_init cs_fmh cs_am cs_amc cs_amac cs_shift cs_mah cs_mat cs_amas cs_active cs_usage cs_brk cs_mc cs_seq cs_bounces cs_unmap].
  assert (FR : forall rid r, frontier st' rid r = frontier st rid r) by (intros; unfold frontier, st'; cbn; rewrite cs_amas; reflexivity).
  assert (HE : forall h, get_head st' h = get_head st h) by (intros [sc|]; unfold st'; cbn; unfold active, ctx; cbn; rewrite ?cs_active, ?cs_fmh; reflexivity).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; unfold st'; cbn; rewrite ?cs_shift, ?cs_brk, ?cs_amac, ?cs_amas; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
    + intros rid r H1 H2. rewrite FR. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite FR. exact (ir_brkfront rid r H1 H2).
  - destruct IA; constructor; unfold st'; cbn; rewrite ?cs_secret, ?cs_init, ?cs_fmh, ?cs_am, ?cs_amc, ?cs_amac, ?cs_mah, ?cs_mat, ?cs_amas, ?cs_active, ?cs_usage; try assumption.
    + split; [exact cs_mc|]. split; [exact cs_seq|]. split; [exact cs_bounces| exact cs_unmap].
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
    + intros sc Hsc. unfold usage, ctx. cbn. rewrite cs_usage. exact (ia_usage sc Hsc).
  - apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| exact HE| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto|]. eapply G1. exact Hb.
  - apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
End CTX.

Lemma ctx_scalars_refl c :
  0 <= c_mmap_counter c < 2^32 -> 0 <= c_seq c < 256 ->
  (forall i v, c_bounces c !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256) ->
  (forall i v, c_unmap_seq c !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256) ->
  ctx_scalars_eq c c.
Proof. intros; constructor; auto. Qed.

Lemma ia_ctx_facts st : inv_A st ->
  0 <= c_mmap_counter (s_ctx st) < 2^32 /\ 0 <= c_seq (s_ctx st) < 256
  /\ (forall i v, c_bounces (s_ctx st) !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256)
  /\ (forall i v, c_unmap_seq (s_ctx st) !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256).
Proof. intros IA. exact (ia_ctx _ IA). Qed.

Lemma INVL_step_seq X st L BL LS : INVL X st L BL LS -> INVL X (step_seq st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold step_seq. destruct (Z.eqb_spec (c_seq (ctx st)) 255) as [E|NE]; apply INVL_ctx_scalars; auto; constructor; cbn; auto; try lia.
  - intros i v H. rewrite lookup_empty in H. discriminate.
  - unfold ctx in NE. lia.
Qed.

Lemma INVL_record_seq X st L BL LS sc : INVL X st L BL LS -> INVL X (record_seq sc st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold record_seq. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
  apply INVL_ctx_scalars; auto; constructor; cbn; auto.
  unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros i v. destruct (Z.eq_dec i (sc - 7)) as [->|NEi].
  - rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
  - rewrite lookup_insert_ne by congruence. apply C4.
Qed.

Lemma INVL_set_bounce X st L BL LS i v : INVL X st L BL LS -> 0 <= i < 32 -> 0 <= v < 256 -> INVL X (set_bounce i v st) L BL LS.
Proof.
  intros INV Hi Hv. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold set_bounce. apply INVL_ctx_scalars; auto; constructor; cbn; auto.
  intros j w. destruct (Z.eq_dec j i) as [->|NE].
  - rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
  - rewrite lookup_insert_ne by congruence. apply C3.
Qed.

Lemma bounces_range st i : inv_A st -> 0 <= bounces st i < 256.
Proof.
  intros IA. pose proof (ia_ctx_facts st IA) as (_ & _ & C3 & _). unfold bounces, ctx.
  destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 _ _ E)).
Qed.

Lemma INVL_account_bounce X st L BL LS sc : INVL X st L BL LS -> INVL X (account_bounce sc st) L BL LS.
Proof.
  intros INV. unfold account_bounce. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
  unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct (negb _ && _); [| exact INV].
  pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
  destruct (Z.ltb_spec (bounces st (sc - 7) + 1) 100); apply INVL_set_bounce; auto; lia.
Qed.

Lemma INVL_decay_bounces X st L BL LS sc : INVL X st L BL LS -> INVL X (decay_bounces sc st) L BL LS.
Proof.
  intros INV. unfold decay_bounces. destruct (sc_in_seq_range sc && _) eqn:E; [| exact INV].
  apply Bool.andb_true_iff in E as [E1 E2]. unfold sc_in_seq_range in E1. apply Bool.andb_true_iff in E1 as [E0 E1]. apply Z.leb_le in E0. apply Z.ltb_lt in E1.
  apply Bool.negb_true_iff in E2. apply Z.eqb_neq in E2.
  pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
  apply INVL_set_bounce; auto; lia.
Qed.

Lemma INVL_mmap_counter X st L BL LS : INVL X st L BL LS ->
  INVL X (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  apply INVL_ctx_scalars; auto; constructor; cbn; auto. unfold u32. apply Z.mod_pos_bound. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rem (g : aptr) (l : list aptr) : list aptr := remove (fun x y => aptr_eq_dec x y) g l.
Definition xzomb (X : extras) (l : list aptr) : extras := mkX (x_idle X) l (x_pend X) (x_orph X) (x_fresh X).
Definition xidle (X : extras) (l : list aptr) : extras := mkX l (x_zomb X) (x_pend X) (x_orph X) (x_fresh X).

Lemma in_rem x g l : In x (rem g l) <-> In x l /\ x <> g.
Proof. unfold rem. split; [apply in_remove|]. intros [H NE]. apply in_in_remove; auto. Qed.

(* [comment removed for export] *)
Lemma present_of_mem st m b : m_mem (MR st m) = Some b -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.
Lemma present_of_next st m x : m_next (MR st m) = Some x -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.

Lemma gcnt_ext_groups st st' :
  s_groups st' = s_groups st ->
  (forall b h m, s_groups st !! b = Some h -> g_meta h = Some m ->
     m_sizeclass (MR st' m) = m_sizeclass (MR st m) /\ cnt_of (MR st' m) = cnt_of (MR st m)) ->
  forall sc, gcnt st' sc = gcnt st sc.
Proof.
  intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext_in. intros [b h] Hin. cbn.
  destruct (g_meta h) as [m|] eqn:Eh; [| reflexivity].
  apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
  destruct (HM b h m Hin Eh) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

Section UNZOMBIE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hz : In g (x_zomb X).
Let X' := xzomb X (rem g (x_zomb X)).
Let st' := put_meta g meta0 st.

Lemma uz_R x : MR st' x = if aptr_eqb x g then meta0 else MR st x.
Proof. unfold st', MR. apply get_meta_rec_put. Qed.
Lemma uz_R_other x : x <> g -> MR st' x = MR st x.
Proof. intros NE. rewrite uz_R, aptr_eqb_neq by exact NE. reflexivity. Qed.

Theorem INVL_unzombie : INVL X' st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (im_zomb _ _ _ IM g Hz) as (NIg & Ng & Pg & bg & Mg & NGg).
  assert (NLg : forall b, ~ hosts st b g).
  { intros b [ai Hb]. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hm & _). cbn in Em. inversion Em. subst m. rewrite Mg in Hm. inversion Hm. subst. rewrite Hb in NGg. discriminate. }
  assert (RG : forall b m, hosts st b m -> MR st' m = MR st m).
  { intros b m Hm. apply uz_R_other. intros ->. exact (NLg b Hm). }
  assert (KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None).
  { intros x. unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
    split; [intros _; exact (present_of_mem st g bg Mg)| intros _; discriminate]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_X X); [reflexivity|]. destruct IR; constructor; try assumption.
  - destruct IA; constructor; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
      destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
    + intros sc Hsc. change (usage st' sc) with (usage st sc). rewrite (ia_usage sc Hsc). symmetry. apply gcnt_ext_groups; [reflexivity|].
      intros b h m Hb Eh. destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Em & Hm & _). rewrite Eh in Em. inversion Em. subst m'.
      rewrite (RG b m); [auto|]. destruct h as [gm gai]. cbn in Eh. subst gm. exists gai. exact Hb.
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. rewrite uz_R in Hm |- *. destruct (aptr_eqb m g); [reflexivity|]. apply M1. exact Hm.
    + intros m b Hm. rewrite uz_R in Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [cbn in Hm; discriminate|].
      destruct (M2 m b Hm) as [H|H]; [left; exact H| right]. cbn. apply in_rem. auto.
    + intros b h Hb. destruct (M3 b h Hb) as (m & Em & Hm & Hai). exists m.
      assert (NE : m <> g) by (intros ->; apply (NLg b); destruct h as [gm gai]; cbn in Em; subst gm; exists gai; exact Hb).
      rewrite (uz_R_other m NE). auto.
    + intros m Hm. cbn in Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec m g) as [->|NE]; [reflexivity| exact E].
    + intros z Hz'. cbn in Hz'. apply in_rem in Hz' as [Hz' NE]. destruct (M5 z Hz') as (A1 & A2 & A3 & b & A4 & A5).
      rewrite (uz_R_other z NE). repeat split; auto. exists b. auto.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros x Hx; rewrite uz_R_other; try reflexivity; intros ->; apply NIg; exists h; rewrite E.
      * apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
      * apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
    + intros m. destruct (aptr_eqb_spec m g) as [->|NE].
      * rewrite uz_R, aptr_eqb_refl. cbn. split; [| reflexivity]. split; [intros H; exfalso; exact (NIg H)| intros H; exfalso; apply H; reflexivity].
      * rewrite (uz_R_other m NE). apply L5.
    + intros m Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; apply NIg; exists LFree; exact Hm|]. rewrite (uz_R_other m NE). apply L6. exact Hm.
    + intros sc m Hm. destruct (L7 sc m Hm) as (A1 & A2 & A3).
      destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; apply NIg; exists (LActive sc); exact Hm|]. rewrite (uz_R_other m NE). auto.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    + intros m b ai Hb. pose proof (G1 m b ai Hb) as GO.
      assert (NE : m <> g) by (intros ->; exact (NLg b (ex_intro _ ai Hb))).
      destruct GO; constructor; rewrite ?(uz_R_other m NE); try assumption.
      * apply KEYS. exact g_present.
      * intros Hml. destruct (g_nest Hml) as (p & i & Hs & Hf & He & Hsc & Hst).
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _).
        assert (NEp : p <> g) by (intros ->; exact (NLg bp Hp)).
        exists p, i. rewrite (uz_R_other p NEp). auto 10.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2.
      rewrite (uz_R_other m1) by (intros ->; exact (NLg b1 (ex_intro _ ai1 H1))).
      rewrite (uz_R_other m2) by (intros ->; exact (NLg b2 (ex_intro _ ai2 H2))). eapply G3; eassumption.
    + intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite (RG _ _ Hm). auto.
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
    + intros s m i Hs. destruct (S1 s m i Hs) as ([b Hb] & Hi & E). rewrite (RG _ _ Hb). split; [exists b; exact Hb| auto].
    + intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (S2 b); auto.
    + intros b m ai i Hb Hi. rewrite (RG b m (ex_intro _ ai Hb)) in Hi |- *. apply (S3 b m ai i Hb Hi).
    + intros k Hk. destruct (S6 k Hk) as (m & i & Hs & rest). exists m, i. split; [exact Hs|].
      destruct (S1 _ _ _ Hs) as ([b Hb] & _). rewrite (RG _ _ Hb). exact rest.
  - (* [comment removed for export] *) destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    + intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (D3 b m i Hb Hi).
    + intros b m p i Hb Hml Hs. rewrite (RG _ _ Hb) in Hml.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _). rewrite (RG _ _ Hp). apply (D5 b m p i Hb Hml Hs).
    + intros k m i Hk Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & _). rewrite (RG _ _ Hb). apply (D6 k m i Hk Hs).
Qed.
End UNZOMBIE.


End CeilWrap.
End MI_Pres3.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Ext.
Import MI_Ext2.
Import MI_Shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Pres1.
Import MI_Pres2.
Import MI_Pres3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition xfresh (X : extras) (f : option aptr) : extras := mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) f.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma data0_shape r : data_of r = data_of meta0 <-> r = mkMeta (m_prev r) (m_next r) None 0 0 0 0 0 0.
Proof.
  destruct r; unfold data_of, m_set_prev, m_set_next, meta0; cbn. split; intros H; [injection H; intros; subst; reflexivity| injection H; intros; subst; reflexivity].
Qed.

Lemma data0_mem r : data_of r = data_of meta0 -> m_mem r = None.
Proof. intros H. apply data_of_eq in H. destruct H as (H & _). exact H. Qed.

Section DEXT.
Variables (st st' : mstate).
Hypothesis DE : forall x, data_of (MR st' x) = data_of (MR st x).
Lemma de_fields x :
  m_mem (MR st' x) = m_mem (MR st x) /\ m_avail (MR st' x) = m_avail (MR st x) /\ m_freed (MR st' x) = m_freed (MR st x)
  /\ m_last_idx (MR st' x) = m_last_idx (MR st x) /\ m_freeable (MR st' x) = m_freeable (MR st x)
  /\ m_sizeclass (MR st' x) = m_sizeclass (MR st x) /\ m_maplen (MR st' x) = m_maplen (MR st x).
Proof. apply data_of_eq. apply DE. Qed.
Lemma de_mem x : m_mem (MR st' x) = m_mem (MR st x). Proof. apply de_fields. Qed.
Lemma de_avail x : m_avail (MR st' x) = m_avail (MR st x). Proof. apply de_fields. Qed.
Lemma de_freed x : m_freed (MR st' x) = m_freed (MR st x). Proof. apply de_fields. Qed.
Lemma de_last x : m_last_idx (MR st' x) = m_last_idx (MR st x). Proof. apply de_fields. Qed.
Lemma de_freeable x : m_freeable (MR st' x) = m_freeable (MR st x). Proof. apply de_fields. Qed.
Lemma de_sc x : m_sizeclass (MR st' x) = m_sizeclass (MR st x). Proof. apply de_fields. Qed.
Lemma de_maplen x : m_maplen (MR st' x) = m_maplen (MR st x). Proof. apply de_fields. Qed.
Lemma de_stride x : get_stride (MR st' x) = get_stride (MR st x). Proof. apply get_stride_data. apply DE. Qed.
Lemma de_gbase x : gbase (MR st' x) = gbase (MR st x). Proof. unfold gbase. rewrite de_mem. reflexivity. Qed.
Lemma de_sstart x i : sstart (MR st' x) i = sstart (MR st x) i. Proof. unfold sstart. rewrite de_gbase, de_stride. reflexivity. Qed.
Lemma de_slot_start' x i : slot_start' (MR st' x) i = slot_start' (MR st x) i.
Proof. unfold slot_start'. rewrite de_mem, de_stride. reflexivity. Qed.
Lemma de_cnt x : cnt_of (MR st' x) = cnt_of (MR st x). Proof. unfold cnt_of. rewrite de_last. reflexivity. Qed.
Lemma de_gend x : gend (MR st' x) = gend (MR st x). Proof. unfold gend. rewrite de_sstart, de_cnt. reflexivity. Qed.
End DEXT.

(* [comment removed for export] *)
Record ctx_but_heads (c c' : mctx) : Prop := mkCBH {
  cb_secret : c_secret c' = c_secret c;
  cb_init : c_init_done c' = c_init_done c;
  cb_mc : c_mmap_counter c' = c_mmap_counter c;
  cb_am : c_avail_meta c' = c_avail_meta c;
  cb_amc : c_avail_meta_count c' = c_avail_meta_count c;
  cb_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
  cb_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
  cb_mah : c_meta_area_head c' = c_meta_area_head c;
  cb_mat : c_meta_area_tail c' = c_meta_area_tail c;
  cb_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
  cb_usage : c_usage c' = c_usage c;
  cb_unmap : c_unmap_seq c' = c_unmap_seq c;
  cb_bounces : c_bounces c' = c_bounces c;
  cb_seq : c_seq c' = c_seq c;
  cb_brk : c_brk c' = c_brk c
}.
Lemma cbh_refl c : ctx_but_heads c c. Proof. constructor; reflexivity. Qed.
Lemma cbh_trans a b c : ctx_but_heads a b -> ctx_but_heads b c -> ctx_but_heads a c.
Proof. intros [] []; constructor; congruence. Qed.
Lemma cbh_set_head st h v : ctx_but_heads (s_ctx st) (s_ctx (set_head h v st)).
Proof. destruct h; constructor; reflexivity. Qed.
Lemma cbh_upd_meta st m f : ctx_but_heads (s_ctx st) (s_ctx (upd_meta m f st)).
Proof. constructor; reflexivity. Qed.

Lemma inv_L_lists st LS : inv_L st LS -> lists_ok st LS.
Proof. intros [L1 L2 L3 L4 L5 L6 L7 L9]. constructor; auto. Qed.

Lemma head_of_app (l : list aptr) g : l <> [] -> head_of (l ++ [g]) = head_of l.
Proof. destruct l; cbn; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RELINK.
Variables (X X' : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS LS' : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis DE : forall x, data_of (MR st' x) = data_of (MR st x).
Hypothesis KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None.
Hypotheses (HR : s_regions st' = s_regions st) (HSh : s_shadow st' = s_shadow st) (HN : s_next_rid st' = s_next_rid st)
           (HA : s_areas st' = s_areas st) (HG : s_groups st' = s_groups st) (HS : s_slots st' = s_slots st)
           (HT : s_tick st' = s_tick st) (HX : s_secret st' = s_secret st) (HV : s_reserved st' = s_reserved st).
Hypothesis HC : ctx_but_heads (s_ctx st) (s_ctx st').
Hypothesis XE : x_pend X' = x_pend X /\ x_orph X' = x_orph X /\ x_zomb X' = x_zomb X.
Hypothesis LO' : lists_ok st' LS'.
Hypothesis H_free : forall m, In m (LS' LFree) -> data_of (MR st m) = data_of meta0.
Hypothesis H_active : forall sc m, In m (LS' (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (MR st m) = sc.
Hypothesis H_keys : forall sc, LS' (LActive sc) <> [] -> 0 <= sc < 48.
Hypothesis H_actkeys : forall sc g, c_active (s_ctx st') !! sc = Some g -> 0 <= sc < 48.
Hypothesis H_idle : forall m, In m (x_idle X') -> s_metas st' !! m = Some meta0 /\ ~ in_list LS' m.
Hypothesis H_zomb : forall z, In z (x_zomb X) -> m_next (MR st' z) = None /\ m_prev (MR st' z) = None /\ ~ in_list LS' z.
Hypothesis H_groups : forall m b ai, s_groups st !! b = Some (mkGhdr (Some m) ai) ->
   (x_fresh X' <> Some m -> ai < m_last_idx (MR st m) -> In m (LS' (LActive (m_sizeclass (MR st m)))))
   /\ (x_fresh X' <> Some m -> m_sizeclass (MR st m) < 48 -> ~ in_list LS' m -> m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0)
   /\ (x_fresh X' <> Some m -> forall sc, In m (LS' (LActive sc)) -> Some m <> head_of (LS' (LActive sc)) ->
         m_avail (MR st m) = 0 /\ m_freed (MR st m) <> 0)
   /\ (m_sizeclass (MR st m) = 63 -> ~ in_list LS' m)
   /\ (x_fresh X' <> Some m -> m_sizeclass (MR st m) < 48 -> get_stride (MR st m) < UNIT * size_class (m_sizeclass (MR st m)) ->
         m_avail (MR st m) = 0 /\ m_freed (MR st m) = 0).

Let dmem := de_mem st st' DE. Let davail := de_avail st st' DE. Let dfreed := de_freed st st' DE.
Let dlast := de_last st st' DE. Let dfreeable := de_freeable st st' DE. Let dsc := de_sc st st' DE.
Let dmaplen := de_maplen st st' DE. Let dstride := de_stride st st' DE. Let dgbase := de_gbase st st' DE.
Let dsstart := de_sstart st st' DE. Let dslot := de_slot_start' st st' DE. Let dcnt := de_cnt st st' DE. Let dgend := de_gend st st' DE.

Lemma rl_hosts b m : hosts st' b m <-> hosts st b m. Proof. apply hosts_ext. exact HG. Qed.
Lemma rl_live m : live_group st' m <-> live_group st m. Proof. apply live_group_ext. exact HG. Qed.
Lemma rl_frontier rid r : frontier st' rid r = frontier st rid r.
Proof. unfold frontier. rewrite (cb_amas _ _ HC). reflexivity. Qed.
Lemma rl_usage sc : usage st' sc = usage st sc.
Proof. unfold usage, ctx. rewrite (cb_usage _ _ HC). reflexivity. Qed.
Lemma rl_gcnt sc : gcnt st' sc = gcnt st sc.
Proof.
  apply gcnt_ext_groups; [exact HG|]. intros b h m Hb Hm. rewrite dsc, dcnt. auto.
Qed.

Theorem INVL_relink : INVL X' st' L BL LS'.
Proof.
  destruct XE as (XP & XO & XZ).
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof HC as [cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 cs12 cs13 cs14 cs15].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?HR, ?HN, ?HV, ?HG, ?XO, ?cs6, ?cs7, ?cs10, ?cs15; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite rl_frontier. reflexivity.
    + intros rid r H1 H2. rewrite rl_frontier. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite rl_frontier. exact (ir_brkfront rid r H1 H2).
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?HR, ?HA, ?HX, ?cs1, ?cs2, ?cs3, ?cs4, ?cs5, ?cs6, ?cs8, ?cs9, ?cs10, ?cs11, ?cs12, ?cs13, ?cs14; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite rl_frontier. auto.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
      destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
    + intros sc Hsc. rewrite rl_usage, rl_gcnt. exact (ia_usage sc Hsc).
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. apply data0_shape. rewrite DE. apply data0_shape. apply M1. rewrite <- dmem. exact Hm.
    + intros m b Hm. rewrite dmem in Hm. rewrite rl_hosts, XZ. apply M2. exact Hm.
    + intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & ? & ? & ?). exists m. rewrite dmem, dlast. auto.
    + exact H_idle.
    + intros z Hz. rewrite XZ in Hz. destruct (H_zomb z Hz) as (A1 & A2 & A3). destruct (M5 z Hz) as (_ & _ & _ & b & B1 & B2).
      split; [exact A3|]. split; [exact A1|]. split; [exact A2|]. exists b. rewrite dmem, HG. auto.
  - (* [comment removed for export] *) destruct LO' as [Q1 Q2 Q3 Q4 Q5]. constructor; try assumption.
    + intros m Hm. apply data0_shape. rewrite DE. apply H_free. exact Hm.
    + intros sc m Hm. destruct (H_active sc m Hm) as (A1 & A2 & A3). rewrite rl_live, dsc. auto.
    + intros [sc|] Hne; [| exact I]. apply H_keys. exact Hne.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros m b ai Hb. rewrite HG in Hb. pose proof (G1 m b ai Hb) as GO. destruct (H_groups m b ai Hb) as (P1 & P2 & P3 & P4 & P5).
      destruct GO; constructor; rewrite ?dmem, ?davail, ?dfreed, ?dlast, ?dfreeable, ?dsc, ?dmaplen, ?dstride, ?dcnt, ?dgend, ?HR, ?HS; try assumption.
      * apply KEYS. exact g_present.
      * destruct g_sc as [A|(A1 & A2 & A3 & A4)]; [left; exact A| right]. auto.
      * intros Hml. destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite dgbase, dsstart, dstride, dsc. auto 10.
    + intros b ai Hb. rewrite HG in Hb. exact (G2 b ai Hb).
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !dlast, !dsc. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. rewrite HR in Hr. rewrite XO in Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite rl_hosts, dmaplen. auto.
    + intros b h Hb. rewrite HG in Hb. rewrite HR. exact (G5 b h Hb).
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
    + intros s m i Hs. rewrite HS in Hs. destruct (S1 s m i Hs) as (? & ? & ?). rewrite rl_live, dlast, dslot. auto.
    + intros b m i Hb Hi. rewrite HS, dslot. apply (S2 b); [apply rl_hosts; exact Hb| rewrite <- dlast; exact Hi].
    + intros b m ai i Hb Hi. rewrite HG in Hb. rewrite dlast in Hi. rewrite dslot, HG, davail, dfreed, XP. exact (S3 b m ai i Hb Hi).
    + intros s Hs. rewrite HS. apply S4. rewrite <- XP. exact Hs.
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, dstride. auto.
  - (* [comment removed for export] *) apply (inv_SH_view st st'); auto.
Qed.
End RELINK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma present_MR st x : s_metas st !! x <> None -> s_metas st !! x = Some (MR st x).
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! x); [reflexivity| congruence]. Qed.

Lemma fupd_in LS h l h' m : In m (fupd LS h l h') <-> (h' = h /\ In m l) \/ (h' <> h /\ In m (LS h')).
Proof.
  unfold fupd. destruct (decide (h' = h)) as [E|NE]; split; intros H; try tauto.
  all: destruct H as [[H1 H2]|[H1 H2]]; first [exact H2| congruence].
Qed.

Section OLD.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.

Lemma old_lists : lists_ok st LS. Proof. apply inv_L_lists. exact (proj1 (proj2 (proj2 (proj2 INV)))). Qed.
Lemma old_free m : In m (LS LFree) -> data_of (MR st m) = data_of meta0.
Proof. intros H. apply data0_shape. exact (il_free _ _ (proj1 (proj2 (proj2 (proj2 INV)))) m H). Qed.
Lemma old_active sc m : In m (LS (LActive sc)) -> 0 <= sc < 48 /\ live_group st m /\ m_sizeclass (MR st m) = sc.
Proof. exact (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m). Qed.
Lemma old_keys sc : LS (LActive sc) <> [] -> 0 <= sc < 48.
Proof. intros H. exact (il_keys _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc) H). Qed.
Lemma old_actkeys sc g : c_active (s_ctx st) !! sc = Some g -> 0 <= sc < 48.
Proof. exact (ia_active_keys _ (proj1 (proj2 INV)) sc g). Qed.
Lemma old_idle m : In m (x_idle X) -> s_metas st !! m = Some meta0 /\ ~ in_list LS m.
Proof. exact (im_idle _ _ _ (proj1 (proj2 (proj2 INV))) m). Qed.
Lemma old_zomb z : In z (x_zomb X) -> m_next (MR st z) = None /\ m_prev (MR st z) = None /\ ~ in_list LS z /\
  exists b, m_mem (MR st z) = Some b /\ s_groups st !! b = None.
Proof. intros H. destruct (im_zomb _ _ _ (proj1 (proj2 (proj2 INV))) z H) as (A & B & C & D). auto. Qed.
Lemma old_group m b ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> group_ok X st LS m b ai.
Proof. intros H. exact (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) m b ai H). Qed.
Lemma old_63 m b ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_sizeclass (MR st m) = 63 -> ~ in_list LS m.
Proof. intros H E. destruct (g_sc _ _ _ _ _ _ (old_group m b ai H)) as [[[_ Hlt] _]|(_ & _ & _ & NI)]; [lia| exact NI]. Qed.
(* [comment removed for export] *)
Lemma listed_next m h : In m (LS h) -> m_next (MR st m) <> None.
Proof. intros H. apply (lists_in_next_some st LS old_lists h m H). Qed.
Lemma listed_present m h : In m (LS h) -> s_metas st !! m <> None.
Proof. intros H. destruct (m_next (MR st m)) as [x|] eqn:E; [exact (present_of_next st m x E)|]. exfalso. exact (listed_next m h H E). Qed.
Lemma head_listed h a : get_head st h = Some a -> In a (LS h).
Proof. intros H. rewrite (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) in H. destruct (LS h); cbn in H; [discriminate|]. inversion H. left. reflexivity. Qed.
Lemma prev_listed h a x : In a (LS h) -> m_prev (MR st a) = Some x -> In x (LS h).
Proof. intros Ha Hp. destruct (lists_prev_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hp in E. inversion E. subst. exact Hy. Qed.
Lemma next_listed h a x : In a (LS h) -> m_next (MR st a) = Some x -> In x (LS h).
Proof. intros Ha Hn. destruct (lists_next_in st LS old_lists h a Ha) as (y & Hy & E & _). rewrite Hn in E. inversion E. subst. exact Hy. Qed.
Lemma idle_unlisted m h : In m (x_idle X) -> ~ In m (LS h).
Proof. intros Hi H. apply (proj2 (old_idle m Hi)). exists h. exact H. Qed.
Lemma zomb_unlisted z h : In z (x_zomb X) -> ~ In z (LS h).
Proof. intros Hz H. apply (proj1 (proj2 (proj2 (old_zomb z Hz)))). exists h. exact H. Qed.
Lemma idle_not_live m : In m (x_idle X) -> ~ live_group st m.
Proof.
  intros Hi [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  destruct (old_idle m Hi) as [E _]. unfold MR, get_meta_rec in M. rewrite E in M. cbn in M. discriminate.
Qed.
Lemma zomb_not_live z : In z (x_zomb X) -> ~ live_group st z.
Proof.
  intros Hz [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  destruct (old_zomb z Hz) as (_ & _ & _ & b' & M' & G'). rewrite M in M'. inversion M'. subst. destruct Hb as [ai Hb]. rewrite Hb in G'. discriminate.
Qed.
Lemma free_not_live m : In m (LS LFree) -> ~ live_group st m.
Proof.
  intros Hf [b Hb]. pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ Hb) as M.
  pose proof (data0_mem _ (old_free m Hf)) as D. rewrite D in M. discriminate.
Qed.
End OLD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_set_fresh X st L BL LS f :
  INVL X st L BL LS -> x_fresh X = None -> INVL (xfresh X f) st L BL LS.
Proof.
  intros INV HF.
  refine (INVL_relink X (xfresh X f) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
            (old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
            (old_actkeys _ _ _ _ _ INV) _ _ _).
  - cbn. auto.
  - cbn. apply (old_idle _ _ _ _ _ INV).
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
    assert (NF : x_fresh X <> Some m) by (rewrite HF; discriminate).
    split; [| split; [| split; [| split]]].
    + intros _. exact (g_partial _ _ _ _ _ _ GO NF).
    + intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
    + intros _. exact (g_rest _ _ _ _ _ _ GO NF).
    + exact (old_63 _ _ _ _ _ INV m b ai Hb).
    + intros _. exact (g_under _ _ _ _ _ _ GO NF).
Qed.

Lemma INVL_clear_fresh X st L BL LS g :
  INVL X st L BL LS -> x_fresh X = Some g ->
  (forall b ai, s_groups st !! b = Some (mkGhdr (Some g) ai) ->
     (ai < m_last_idx (MR st g) -> In g (LS (LActive (m_sizeclass (MR st g)))))
     /\ (m_sizeclass (MR st g) < 48 -> ~ in_list LS g -> m_avail (MR st g) = 0 /\ m_freed (MR st g) = 0)
     /\ (forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> m_avail (MR st g) = 0 /\ m_freed (MR st g) <> 0)
     /\ (m_sizeclass (MR st g) < 48 -> get_stride (MR st g) < UNIT * size_class (m_sizeclass (MR st g)) -> m_avail (MR st g) = 0 /\ m_freed (MR st g) = 0)) ->
  INVL (xfresh X None) st L BL LS.
Proof.
  intros INV HF OB.
  refine (INVL_relink X (xfresh X None) st st L BL LS LS INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_refl _) _
            (old_lists _ _ _ _ _ INV) (old_free _ _ _ _ _ INV) (old_active _ _ _ _ _ INV) (old_keys _ _ _ _ _ INV)
            (old_actkeys _ _ _ _ _ INV) _ _ _).
  - cbn. auto.
  - cbn. apply (old_idle _ _ _ _ _ INV).
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _). auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO.
    destruct (aptr_eq_dec m g) as [->|NE].
    + destruct (OB b ai Hb) as (O1 & O2 & O3 & O4). split; [| split; [| split; [| split]]]; auto. exact (old_63 _ _ _ _ _ INV g b ai Hb).
    + assert (NF : x_fresh X <> Some m) by (rewrite HF; congruence).
      split; [| split; [| split; [| split]]].
      * intros _. exact (g_partial _ _ _ _ _ _ GO NF).
      * intros _. exact (g_unlisted _ _ _ _ _ _ GO NF).
      * intros _. exact (g_rest _ _ _ _ _ _ GO NF).
      * exact (old_63 _ _ _ _ _ INV m b ai Hb).
      * intros _. exact (g_under _ _ _ _ _ _ GO NF).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma queue_frame h g st : let st' := queue_st h g st in
  s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_next_rid st' = s_next_rid st
  /\ s_areas st' = s_areas st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_tick st' = s_tick st /\ s_secret st' = s_secret st /\ s_reserved st' = s_reserved st
  /\ ctx_but_heads (s_ctx st) (s_ctx st').
Proof.
  unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|]; [destruct (m_prev (get_meta_rec st a))| destruct h]; cbn;
    repeat split; try reflexivity; constructor; reflexivity.
Qed.

Lemma queue_metas_other h g st x :
  x <> g -> (forall a, get_head st h = Some a -> x <> a /\ m_prev (MR st a) <> Some x) ->
  s_metas (queue_st h g st) !! x = s_metas st !! x.
Proof.
  intros NE H. unfold queue_st, q_link, q_single. destruct (get_head st h) as [a|] eqn:E.
  - destruct (H a eq_refl) as [NA NP]. unfold MR in NP.
    destruct (m_prev (get_meta_rec st a)) as [pv|] eqn:Ep; rewrite !s_metas_upd_meta, !lookup_insert_ne by congruence; reflexivity.
  - rewrite set_head_metas, s_metas_upd_meta, lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma dequeue_frame h m st : let st' := dequeue h m st in
  s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_next_rid st' = s_next_rid st
  /\ s_areas st' = s_areas st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_tick st' = s_tick st /\ s_secret st' = s_secret st /\ s_reserved st' = s_reserved st
  /\ ctx_but_heads (s_ctx st) (s_ctx st').
Proof.
  unfold dequeue.
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; try destruct h; cbn;
  repeat split; try reflexivity; constructor; reflexivity.
Qed.

Lemma dequeue_metas_other h m st x :
  x <> m -> m_prev (MR st m) <> Some x -> m_next (MR st m) <> Some x ->
  s_metas (dequeue h m st) !! x = s_metas st !! x.
Proof.
  intros NE NP NN. unfold dequeue, MR in *.
  rewrite s_metas_upd_meta, lookup_insert_ne by congruence.
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|]; cbn -[get_head optr_eqb aptr_eqb upd_meta set_head];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity;
  rewrite ?set_head_metas, ?s_metas_upd_meta, ?lookup_insert_ne by congruence; try reflexivity.
Qed.

Lemma get_head_active st sc : get_head st (LActive sc) = c_active (s_ctx st) !! sc.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section QUEUE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr) (h : lhead).
Hypothesis INV : INVL X st L BL LS.
Hypothesis NL : m_next (MR st g) = None.
Hypothesis PRES : s_metas st !! g <> None.
Hypothesis HQ : match h with
  | LActive sc => 0 <= sc < 48 /\ live_group st g /\ m_sizeclass (MR st g) = sc /\ x_fresh X = Some g
  | LFree => data_of (MR st g) = data_of meta0 /\ ~ In g (x_idle X) /\ ~ In g (x_zomb X)
  end.
Let st' := queue_st h g st.
Let LS' := fupd LS h (LS h ++ [g]).

Lemma q_in m h' : In m (LS' h') <-> In m (LS h') \/ (h' = h /\ m = g).
Proof.
  unfold LS'. rewrite fupd_in, in_app_iff. cbn. destruct (decide (h' = h)) as [->|NE]; intuition congruence.
Qed.
Lemma q_in_list m : in_list LS' m <-> in_list LS m \/ m = g.
Proof.
  unfold in_list. split.
  - intros [h' H]. apply q_in in H. destruct H as [H|[_ ->]]; [left; exists h'; exact H| right; reflexivity].
  - intros [[h' H]| ->]; [exists h'; apply q_in; left; exact H| exists h; apply q_in; right; auto].
Qed.
Lemma g_unlisted_old h' : ~ In g (LS h').
Proof. exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NL h'). Qed.
Lemma g_not_idle : ~ In g (x_idle X).
Proof.
  destruct h as [sc|]; [| exact (proj1 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hi. exact (idle_not_live _ _ _ _ _ INV g Hi Hl).
Qed.
Lemma g_not_zomb : ~ In g (x_zomb X).
Proof.
  destruct h as [sc|]; [| exact (proj2 (proj2 HQ))]. destruct HQ as (_ & Hl & _). intros Hz. exact (zomb_not_live _ _ _ _ _ INV g Hz Hl).
Qed.
Lemma untouched x : (forall h', ~ In x (LS h')) -> x <> g -> s_metas st' !! x = s_metas st !! x.
Proof.
  intros NI NE. apply queue_metas_other; [exact NE|]. intros a Ha. split.
  - intros ->. exact (NI h (head_listed _ _ _ _ _ INV h a Ha)).
  - intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
Qed.

Theorem INVL_queue : INVL X st' L BL LS'.
Proof.
  destruct (queue_frame h g st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  refine (INVL_relink X X st st' L BL LS LS' INV (queue_data h g st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 FC _ _ _ _ _ _ _ _ _).
  - (* [comment removed for export] *) intros x. split; [| apply queue_keys_mono]. intros K. apply queue_keys in K.
    destruct K as [K|[->|[Hh|(a & Ha & Hp)]]]; [exact K| exact PRES| |].
    + exact (listed_present _ _ _ _ _ INV x h (head_listed _ _ _ _ _ INV h x Hh)).
    + exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h a x (head_listed _ _ _ _ _ INV h a Ha) Hp)).
  - auto.
  - apply lists_queue; [apply (old_lists _ _ _ _ _ INV)| exact NL].
  - intros m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_free _ _ _ _ _ INV m Hm)|]. subst h. exact (proj1 HQ).
  - intros sc m Hm. apply q_in in Hm. destruct Hm as [Hm|[E ->]]; [exact (old_active _ _ _ _ _ INV sc m Hm)|]. subst h. destruct HQ as (A & B & C & _). auto.
  - intros sc Hne. destruct (decide (LActive sc = h)) as [E|NE].
    + subst h. exact (proj1 HQ).
    + unfold LS' in Hne. rewrite fupd_ne in Hne by exact NE. exact (old_keys _ _ _ _ _ INV sc Hne).
  - intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite queue_head in Hx.
    destruct (decide (LActive sc = h)) as [E|NE]; [subst h; exact (proj1 HQ)|]. exact (old_actkeys _ _ _ _ _ INV sc x Hx).
  - intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI].
    assert (NE : m <> g) by (intros ->; exact (g_not_idle Hm)).
    split; [rewrite untouched; [exact E| intros h'; apply (idle_unlisted _ _ _ _ _ INV); exact Hm| exact NE]|].
    rewrite q_in_list. tauto.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    assert (NE : z <> g) by (intros ->; exact (g_not_zomb Hz)).
    assert (E : MR st' z = MR st z).
    { unfold MR, get_meta_rec. rewrite untouched; [reflexivity| intros h'; apply (zomb_unlisted _ _ _ _ _ INV); exact Hz| exact NE]. }
    rewrite E, q_in_list. repeat split; auto. tauto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
    5:{ exact (g_under _ _ _ _ _ _ GO). }
    + intros NF Hai. apply q_in. left. exact (g_partial _ _ _ _ _ _ GO NF Hai).
    + intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO NF Hsc). rewrite q_in_list in NI. tauto.
    + intros NF sc Hm Hh. apply q_in in Hm. destruct Hm as [Hm|[E ->]].
      * apply (g_rest _ _ _ _ _ _ GO NF sc Hm). unfold LS' in Hh. destruct (decide (LActive sc = h)) as [E|NE].
        -- subst h. rewrite fupd_eq in Hh. rewrite head_of_app in Hh; [exact Hh|]. intros E0. rewrite E0 in Hm. exact Hm.
        -- rewrite fupd_ne in Hh by exact NE. exact Hh.
      * exfalso. subst h. apply NF. exact (proj2 (proj2 (proj2 HQ))).
    + intros H63. rewrite q_in_list. intros [NI| ->]; [exact (old_63 _ _ _ _ _ INV m b ai Hb H63 NI)|].
      destruct h as [sc|].
      * destruct HQ as (A & _ & C & _). lia.
      * pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV))) _ _ (ex_intro _ ai Hb)) as M.
        rewrite (data0_mem _ (proj1 HQ)) in M. discriminate.
Qed.
End QUEUE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DEQUEUE.
Variables (X X' : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m : aptr) (h : lhead) (l1 l2 : list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HL : LS h = l1 ++ m :: l2.
Hypothesis HX : (exists sc, h = LActive sc /\ x_fresh X = None /\ X' = xfresh X (Some m)) \/ (h = LFree /\ X' = xidle X (m :: x_idle X)).
Let st' := dequeue h m st.
Let LS' := fupd LS h (l1 ++ l2).

Lemma m_listed : In m (LS h). Proof. rewrite HL. apply in_app_iff. right. left. reflexivity. Qed.
Lemma d_in x h' : In x (LS' h') -> In x (LS h').
Proof.
  unfold LS'. rewrite fupd_in. intros [[-> H]|[_ H]]; [| exact H]. rewrite HL. apply in_app_iff in H. apply in_app_iff. cbn. tauto.
Qed.
Lemma d_in_rev x h' : In x (LS h') -> x <> m -> In x (LS' h').
Proof.
  intros H NE. unfold LS'. apply fupd_in. destruct (decide (h' = h)) as [->|NE'].
  - left. split; [reflexivity|]. rewrite HL in H. apply in_app_iff in H. apply in_app_iff. cbn in H. destruct H as [H|[H|H]]; [tauto| congruence| tauto].
  - right. auto.
Qed.
Lemma d_in_list x : in_list LS' x -> in_list LS x.
Proof. intros [h' H]. exists h'. apply (d_in x h' H). Qed.
Lemma m_out : ~ in_list LS' m.
Proof.
  intros [h' H]. unfold LS' in H. apply fupd_in in H. destruct H as [[-> H]|[NE H]].
  - pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND.
    destruct (NoDup_In_split l1 l2 m ND) as [N1 N2]. apply in_app_iff in H. tauto.
  - apply NE. exact (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h' h m H m_listed).
Qed.
Lemma untouched_d x : (forall h', ~ In x (LS h')) -> s_metas st' !! x = s_metas st !! x.
Proof.
  intros NI. apply dequeue_metas_other.
  - intros ->. exact (NI h m_listed).
  - intros Hp. exact (NI h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
  - intros Hn. exact (NI h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
Qed.
Lemma nonhead_old x : In x (LS' h) -> Some x <> head_of (LS' h) -> Some x <> head_of (LS h).
Proof.
  intros Hx Hh. unfold LS' in Hx, Hh. rewrite fupd_eq in Hx, Hh. rewrite HL. destruct l1 as [|a l1']; cbn in *.
  - intros E. inversion E. subst x.
    pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) h) as ND. rewrite HL in ND. cbn in ND.
    apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hx.
  - exact Hh.
Qed.
Lemma MR'_m : MR st' m = data_of (MR st m).
Proof.
  pose proof (dequeue_data h m st m) as D. fold st' in D. rewrite <- D.
  unfold st', dequeue, MR. rewrite get_meta_rec_upd_same. reflexivity.
Qed.

Theorem INVL_dequeue : INVL X' st' L BL LS'.
Proof.
  destruct (dequeue_frame h m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  refine (INVL_relink X X' st st' L BL LS LS' INV (dequeue_data h m st) _ F1 F2 F3 F4 F5 F6 F7 F8 F9 FC _ _ _ _ _ _ _ _ _).
  - (* [comment removed for export] *) intros x. split; [| apply dequeue_keys_mono]. intros K. apply dequeue_keys in K.
    destruct K as [K|[->|[Hp|Hn]]]; [exact K| exact (listed_present _ _ _ _ _ INV m h m_listed)| |].
    + exact (listed_present _ _ _ _ _ INV x h (prev_listed _ _ _ _ _ INV h m x m_listed Hp)).
    + exact (listed_present _ _ _ _ _ INV x h (next_listed _ _ _ _ _ INV h m x m_listed Hn)).
  - destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; auto.
  - apply lists_dequeue; [apply (old_lists _ _ _ _ _ INV)| exact HL].
  - intros x Hx. exact (old_free _ _ _ _ _ INV x (d_in x LFree Hx)).
  - intros sc x Hx. exact (old_active _ _ _ _ _ INV sc x (d_in x _ Hx)).
  - intros sc Hne. apply (old_keys _ _ _ _ _ INV sc). intros E. apply Hne. unfold LS'. unfold fupd.
    destruct (decide (LActive sc = h)) as [E2|NE2]; [| exact E]. exfalso. rewrite E2, HL in E. destruct l1; discriminate.
  - intros sc x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx. rewrite dequeue_head in Hx.
    destruct (decide (LActive sc = h)) as [E|NE]; [| exact (old_actkeys _ _ _ _ _ INV sc x Hx)].
    apply (old_keys _ _ _ _ _ INV sc). rewrite E, HL. destruct l1; discriminate.
  - intros x Hx.
    assert (OLD : In x (x_idle X) -> s_metas st' !! x = Some meta0 /\ ~ in_list LS' x).
    { intros Hi. destruct (old_idle _ _ _ _ _ INV x Hi) as [E NI]. split.
      - rewrite untouched_d; [exact E|]. intros h'. apply (idle_unlisted _ _ _ _ _ INV). exact Hi.
      - intros IL'. exact (NI (d_in_list x IL')). }
    destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)]; rewrite EX in Hx; cbn in Hx; [exact (OLD Hx)|].
    destruct Hx as [<-|Hx]; [| exact (OLD Hx)].
    split; [| exact m_out].
    rewrite (present_MR st' m (dequeue_key_m h m st)). f_equal. rewrite MR'_m.
    apply (old_free _ _ _ _ _ INV). rewrite <- Eh. exact m_listed.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    assert (E : MR st' z = MR st z).
    { unfold MR, get_meta_rec. rewrite untouched_d; [reflexivity|]. intros h'. apply (zomb_unlisted _ _ _ _ _ INV). exact Hz. }
    rewrite E. repeat split; auto. intros IL'. exact (C (d_in_list z IL')).
  - intros x b ai Hb. pose proof (old_group _ _ _ _ _ INV x b ai Hb) as GO.
    destruct (aptr_eq_dec x m) as [->|NEm].
    + destruct HX as [(sc & Eh & HD & EX)|(Eh & EX)].
      * pose proof m_listed as ML. rewrite Eh in ML. destruct (old_active _ _ _ _ _ INV sc m ML) as (A1 & A2 & A3).
        rewrite EX. cbn. split; [| split; [| split; [| split]]]; [intros NF; exfalso; apply NF; reflexivity..| | intros NF; exfalso; apply NF; reflexivity]. intros H63. lia.
      * exfalso. pose proof m_listed as ML. rewrite Eh in ML. exact (free_not_live _ _ _ _ _ INV m ML (ex_intro _ b (ex_intro _ ai Hb))).
    + assert (HNF : x_fresh X' <> Some x -> x_fresh X <> Some x).
      { destruct HX as [(sc & Eh & HD & ->)|(Eh & ->)]; cbn; [rewrite HD; intros _; discriminate| exact (fun H => H)]. }
      split; [| split; [| split; [| split]]].
      5:{ intros NF. exact (g_under _ _ _ _ _ _ GO (HNF NF)). }
      * intros NF Hai. apply d_in_rev; [| exact NEm]. exact (g_partial _ _ _ _ _ _ GO (HNF NF) Hai).
      * intros NF Hsc NI. apply (g_unlisted _ _ _ _ _ _ GO (HNF NF) Hsc). intros [h' H]. apply NI. exists h'. apply d_in_rev; [exact H| exact NEm].
      * intros NF sc Hx Hh. apply (g_rest _ _ _ _ _ _ GO (HNF NF) sc (d_in x _ Hx)).
        destruct (decide (LActive sc = h)) as [E|NE].
        -- rewrite E in Hx, Hh |- *. exact (nonhead_old x Hx Hh).
        -- unfold LS' in Hh. rewrite fupd_ne in Hh by exact NE. exact Hh.
      * intros H63 IL'. exact (old_63 _ _ _ _ _ INV x b ai Hb H63 (d_in_list x IL')).
Qed.
End DEQUEUE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ROTATE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (a a' : aptr) (rest : list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HL : LS (LActive sc) = a :: rest.
Hypothesis Hn : m_next (MR st a) = Some a'.
Hypothesis OB : x_fresh X <> Some a -> rest <> [] -> m_avail (MR st a) = 0 /\ m_freed (MR st a) <> 0.
Let h := LActive sc.
Let st' := set_head h (Some a') st.
Let LS' := fupd LS h (rest ++ [a]).

Lemma r_in x h' : In x (LS' h') <-> In x (LS h').
Proof.
  unfold LS'. rewrite fupd_in. destruct (decide (h' = h)) as [->|NE].
  - unfold h. rewrite HL, in_app_iff. cbn. tauto.
  - tauto.
Qed.
Lemma r_in_list x : in_list LS' x <-> in_list LS x.
Proof. unfold in_list. split; intros [h' H]; exists h'; apply r_in; exact H. Qed.

Theorem INVL_rotate : INVL X st' L BL LS'.
Proof.
  refine (INVL_relink X X st st' L BL LS LS' INV (fun x => eq_refl) (fun x => iff_refl _)
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (cbh_set_head st h (Some a')) _
            _ _ _ _ _ _ _ _).
  - auto.
  - apply lists_rotate; [apply (old_lists _ _ _ _ _ INV)| exact HL| exact Hn].
  - intros m Hm. apply r_in in Hm. exact (old_free _ _ _ _ _ INV m Hm).
  - intros sc0 m Hm. apply r_in in Hm. exact (old_active _ _ _ _ _ INV sc0 m Hm).
  - intros sc0 Hne. apply (old_keys _ _ _ _ _ INV sc0). intros E. apply Hne. unfold LS', fupd.
    destruct (decide (LActive sc0 = h)) as [E2|NE2]; [| exact E]. exfalso. unfold h in E2. inversion E2. subst. rewrite HL in E. discriminate.
  - intros sc0 x Hx. rewrite <- get_head_active in Hx. unfold st' in Hx.
    destruct (decide (LActive sc0 = h)) as [E|NE].
    + apply (old_keys _ _ _ _ _ INV sc0). unfold h in E. inversion E. subst. rewrite HL. discriminate.
    + rewrite get_head_set_head_other in Hx by exact NE. exact (old_actkeys _ _ _ _ _ INV sc0 x Hx).
  - intros m Hm. cbn in Hm. destruct (old_idle _ _ _ _ _ INV m Hm) as [E NI]. split; [| rewrite r_in_list; exact NI].
    unfold st'. rewrite set_head_metas. exact E.
  - intros z Hz. destruct (old_zomb _ _ _ _ _ INV z Hz) as (A & B & C & _).
    unfold st', MR. rewrite get_meta_rec_set_head. fold (MR st z). rewrite r_in_list. auto.
  - intros m b ai Hb. pose proof (old_group _ _ _ _ _ INV m b ai Hb) as GO. split; [| split; [| split; [| split]]].
    5:{ exact (g_under _ _ _ _ _ _ GO). }
    + intros NF Hai. apply r_in. exact (g_partial _ _ _ _ _ _ GO NF Hai).
    + intros NF Hsc NI. rewrite r_in_list in NI. exact (g_unlisted _ _ _ _ _ _ GO NF Hsc NI).
    + intros NF sc0 Hm Hh. destruct (decide (LActive sc0 = h)) as [E|NE].
      * unfold h in E. inversion E. subst sc0. unfold LS' in Hm, Hh. fold h in Hm, Hh. rewrite fupd_eq in Hm, Hh.
        apply in_app_iff in Hm. destruct Hm as [Hm|[<-|[]]].
        -- apply (g_rest _ _ _ _ _ _ GO NF sc). { unfold h in HL. rewrite HL. right. exact Hm. }
           unfold h in HL. rewrite HL. cbn. intros E2. inversion E2. subst m.
           pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND.
           apply NoDup_cons in ND as [N _]. apply N. apply list_elem_of_In. exact Hm.
        -- apply OB; [exact NF|]. intros ->. cbn in Hh. apply Hh. reflexivity.
      * unfold LS' in Hm, Hh. rewrite fupd_ne in Hm, Hh by exact NE. exact (g_rest _ _ _ _ _ _ GO NF sc0 Hm Hh).
    + intros H63. rewrite r_in_list. exact (old_63 _ _ _ _ _ INV m b ai Hb H63).
Qed.
End ROTATE.


End CeilWrap.
