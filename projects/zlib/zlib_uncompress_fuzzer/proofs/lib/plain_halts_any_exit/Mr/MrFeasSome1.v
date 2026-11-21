(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint gone (B : Z) (allow : bool) {R} (P : R -> Prop) (t : M R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis e k =>
      match e with
      | EMmap a len prot flags =>
          allow = true /\ a = 0 /\ prot = PROT_RW /\ flags = MAP_PRIVATE + MAP_ANON /\ 0 < len <= B /\
          forall z, is_err z = false -> gone B false P (k z)
      | EUndef _ => True
      | _ => False
      end
  end.

Lemma gone_weaken B {R} (P : R -> Prop) (t : M R) : gone B false P t -> gone B true P t.
Proof. destruct t as [r|e k]; cbn; [auto|]. destruct e; auto. intros (H & _). discriminate. Qed.

Lemma gone_sbind B al {R S} (P1 : R -> Prop) (P : S -> Prop) (t : M R) (f : R -> M S) :
  gone B al P1 t -> (forall r, P1 r -> gone B false P (f r)) -> gone B al P (sbind t f).
Proof.
  revert al t. fix IH 2. intros al [r|e k]; cbn; intros H Hf.
  - destruct al; [apply gone_weaken|]; apply Hf; exact H.
  - destruct e; try exact H.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6). repeat (split; [assumption|]).
    intros z Hz. apply IH; [apply H6; exact Hz | exact Hf].
Qed.

Lemma size_class_bounds sc : 0 <= size_class sc <= 8191.
Proof.
  unfold size_class. set (i := Z.to_nat sc).
  assert (H : Forall (fun x => 0 <= x <= 8191) size_classes) by (unfold size_classes; repeat constructor; lia).
  destruct (Nat.lt_ge_cases i (length size_classes)) as [Hlt|Hge].
  - apply (proj1 (List.Forall_forall _ _) H). apply nth_In. exact Hlt.
  - rewrite nth_overflow by exact Hge. lia.
Qed.

Lemma small_cnt_bounds sc i : 0 <= small_cnt sc i <= 32.
Proof.
  unfold small_cnt.
  assert (H : Forall (Forall (fun x => 0 <= x <= 32)) small_cnt_tab) by (unfold small_cnt_tab; repeat constructor; lia).
  set (row := nth (Z.to_nat sc) small_cnt_tab []).
  assert (Hrow : Forall (fun x => 0 <= x <= 32) row).
  { subst row. destruct (Nat.lt_ge_cases (Z.to_nat sc) (length small_cnt_tab)) as [Hlt|Hge].
    - apply (proj1 (List.Forall_forall _ _) H). apply nth_In. exact Hlt.
    - rewrite nth_overflow by exact Hge. constructor. }
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length row)) as [Hlt|Hge].
  - apply (proj1 (List.Forall_forall _ _) Hrow). apply nth_In. exact Hlt.
  - rewrite nth_overflow by exact Hge. lia.
Qed.

Lemma med_cnt_bounds i : 0 <= med_cnt i <= 32.
Proof.
  unfold med_cnt. assert (H : Forall (fun x => 0 <= x <= 32) med_cnt_tab) by (unfold med_cnt_tab; repeat constructor; lia).
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length med_cnt_tab)) as [Hlt|Hge].
  - apply (proj1 (List.Forall_forall _ _) H). apply nth_In. exact Hlt.
  - rewrite nth_overflow by exact Hge. lia.
Qed.

Lemma shiftr1_bounds c : 0 <= c <= 32 -> 0 <= Z.shiftr c 1 <= 32.
Proof. intros H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. Qed.

Lemma halve_even_bounds fuel : forall c u, 0 <= c <= 32 -> 0 <= halve_even fuel c u <= 32.
Proof.
  induction fuel as [|f IH]; intros c u H; cbn [halve_even]; [exact H|].
  destruct (Z.even c && (u <? 4 * c)); [apply IH, shiftr1_bounds, H | exact H].
Qed.
Lemma halve_big_bounds fuel : forall c s, 0 <= c <= 32 -> 0 <= halve_big fuel c s <= 32.
Proof.
  induction fuel as [|f IH]; intros c s H; cbn [halve_big]; [exact H|].
  destruct (65536 * UNIT <=? s * c); [apply IH, shiftr1_bounds, H | exact H].
Qed.
Lemma small_cnt_pick_bounds sc u : 0 <= small_cnt_pick sc u <= 32.
Proof. unfold small_cnt_pick. repeat match goal with |- context [if ?c then _ else _] => destruct c end; apply small_cnt_bounds. Qed.

Lemma round_up_pg_bounds x : x <= round_up_pg x <= x + 4095.
Proof.
  unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (- x) (2 ^ 12) ltac:(lia)). change (2 ^ 12) with 4096 in *. lia.
Qed.

Definition metaok (d : Z) (st : mstate) : Prop := d <= c_avail_meta_count (ctx st).
Definition keeps_count (st st' : mstate) : Prop := c_avail_meta_count (ctx st') = c_avail_meta_count (ctx st).
Lemma kc_metaok d st st' : keeps_count st st' -> metaok d st -> metaok d st'.
Proof. unfold keeps_count, metaok. intros -> H. exact H. Qed.
Lemma metaok_le d d' st : d' <= d -> metaok d st -> metaok d' st.
Proof. unfold metaok. lia. Qed.

Lemma count_upd_meta m f st : c_avail_meta_count (ctx (upd_meta m f st)) = c_avail_meta_count (ctx st).
Proof. reflexivity. Qed.
Lemma count_am_take_ctx m st :
  c_avail_meta_count (ctx (upd_ctx (fun c => set_avail_meta (Some (aadd m META_SIZE)) (set_avail_meta_count (c_avail_meta_count c - 1) c)) st))
  = c_avail_meta_count (ctx st) - 1.
Proof. reflexivity. Qed.

Section Walk.
Context (B : Z) {R : Type} (P : R -> Prop).

Lemma g1_guard al tag c (k bail : M R) : gone B al P k -> gone B al P (guard tag c k bail).
Proof. intros H. unfold guard. destruct c; [exact H | exact I]. Qed.

Lemma g1_queue al h m st (k : mstate -> M R) bail :
  (forall st', keeps_count st st' -> gone B al P (k st')) -> gone B al P (queue h m st k bail).
Proof.
  intros Hk. unfold queue. apply g1_guard, g1_guard. destruct (get_head st h) as [hd|].
  - apply Hk. unfold keeps_count. destruct (m_prev (get_meta_rec st hd)); reflexivity.
  - apply Hk. unfold keeps_count. destruct h; reflexivity.
Qed.

Lemma g1_activate_group al m st (k : mstate -> Z -> M R) bail :
  (forall st' z, keeps_count st st' -> gone B al P (k st' z)) -> gone B al P (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply g1_guard. apply Hk. reflexivity. Qed.

Lemma kc_dequeue h m st : keeps_count st (dequeue h m st).
Proof.
  unfold keeps_count, dequeue.
  destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m))).
  - destruct (m_prev (get_meta_rec st m)); destruct (m_next (get_meta_rec st m));
      match goal with |- context [if ?c then _ else _] => destruct c end; destruct h; reflexivity.
  - destruct h; reflexivity.
Qed.

Lemma g1_alloc_meta al d st (k : mstate -> optr -> M R) bail :
  metaok d st -> 1 <= d ->
  (forall st' m, metaok (d - 1) st' -> gone B al P (k st' (Some m))) -> gone B al P (alloc_meta st k bail).
Proof.
  intros Hm Hd Hk. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else st).
  assert (K0 : keeps_count st st0) by (subst st0; destruct (c_init_done (ctx st) =? 0); reflexivity).
  pose proof (kc_metaok _ _ _ K0 Hm) as Hm0. clearbody st0. clear K0 Hm.
  destruct (c_free_meta_head (ctx st0)) as [m|].
  { apply Hk. eapply metaok_le; [|eapply kc_metaok; [apply kc_dequeue | exact Hm0]]. lia. }
  unfold metaok in Hm0.
  replace (c_avail_meta_count (ctx st0) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  unfold am_take. destruct (c_avail_meta (ctx st0)) as [m|]; [|exact I].
  apply Hk. unfold metaok. rewrite count_upd_meta, count_am_take_ctx. lia.
Qed.

Lemma kc_refl st : keeps_count st st. Proof. reflexivity. Qed.
Lemma kc_trans a b c : keeps_count a b -> keeps_count b c -> keeps_count a c.
Proof. unfold keeps_count. intros H1 H2. rewrite H2. exact H1. Qed.
Lemma kc_set_active sc v st : keeps_count st (set_active sc v st). Proof. reflexivity. Qed.
Lemma kc_upd_meta m f st : keeps_count st (upd_meta m f st). Proof. reflexivity. Qed.
Lemma kc_set_gai g ai st : keeps_count st (set_group_active_idx g ai st).
Proof. unfold keeps_count, set_group_active_idx. destruct (get_group st g); reflexivity. Qed.
Lemma kc_decay sc st : keeps_count st (decay_bounces sc st).
Proof. unfold keeps_count, decay_bounces. destruct (sc_in_seq_range sc && negb (bounces st (sc - 7) =? 0)); reflexivity. Qed.

Lemma g1_try_avail al sc st (k : mstate -> Z -> M R) bail :
  (forall st' z, keeps_count st st' -> gone B al P (k st' z)) -> gone B al P (try_avail sc st k bail).
Proof.
  intros Hk. unfold try_avail. destruct (active st sc) as [m|]; [|apply Hk; apply kc_refl].
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [unfold ta_fin; apply Hk; apply kc_upd_meta|].

  match goal with |- gone B al P (match ?s with Some _ => _ | None => _ end) => destruct s as [[st1 m1]|] eqn:E1 end.

  2:{ destruct (m_freed _ =? 0); [apply Hk; apply kc_dequeue | exact I]. }

  assert (K1 : keeps_count st st1).
  { destruct (m_freed (get_meta_rec st m) =? 0).
    - destruct (active (dequeue (LActive sc) m st) sc); [|discriminate]. injection E1 as E1a E1b. rewrite <- E1a. apply kc_dequeue.
    - destruct (m_next (get_meta_rec st m)); [|discriminate]. injection E1 as E1a E1b. rewrite <- E1a. apply kc_set_active. }

  clear E1.
  match goal with |- gone B al P (let (a, b) := ?x in _) => destruct x as [[st2 m2] mask] eqn:E2 end.

  assert (K2 : keeps_count st st2).
  { match type of E2 with (if ?c then _ else _) = _ => destruct c end.
    - destruct (m_next (get_meta_rec st1 m1)).
      + injection E2 as E2a E2b E2c. rewrite <- E2a. (eapply kc_trans; [exact K1 | apply kc_set_active]).
      + injection E2 as E2a E2b E2c. rewrite <- E2a. exact K1.
    - injection E2 as E2a E2b E2c. rewrite <- E2a. exact K1. }

  clear E2.
  match goal with |- gone B al P (let (a, b) := ?x in _) => destruct x as [st3 m3] eqn:E3 end.

  assert (K3 : keeps_count st st3).
  { match type of E3 with (if ?c then _ else _) = _ => destruct c end.
    - match type of E3 with (if ?c then _ else _) = _ => destruct c end.
      + destruct (m_next (get_meta_rec st2 m2)).
        * injection E3 as E3a E3b. rewrite <- E3a. eapply kc_trans; [exact K2 | apply kc_set_active].
        * injection E3 as E3a E3b. rewrite <- E3a. exact K2.
      + destruct (m_mem (get_meta_rec st2 m2)).
        * pose proof (f_equal fst E3) as E3a. cbn [fst] in E3a. rewrite <- E3a. (eapply kc_trans; [exact K2 | apply kc_set_gai]).
        * injection E3 as E3a E3b. rewrite <- E3a. exact K2.
    - injection E3 as E3a E3b. rewrite <- E3a. exact K2. }

  clear E3.
  apply g1_activate_group. intros st4 z K4. apply g1_guard. unfold ta_fin. apply Hk.

  apply (kc_trans st st3 _ K3). apply (kc_trans st3 st4 _ K4).
  eapply kc_trans; [apply kc_decay | apply kc_upd_meta].

Qed.

Lemma g1_alloc_group lay (asr : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) st sc req (k : mstate -> optr -> M R) bail d :
  metaok d st -> 1 <= d -> 0 <= req <= 2^23 -> 2^24 <= B ->
  (forall st1 sc1 req1 (k1 : mstate -> Z -> M R) bail1, metaok (d - 1) st1 -> 0 <= req1 <= 2^23 ->
     (forall st' idx, 0 <= idx -> gone B false P (k1 st' idx)) -> gone B true P (asr st1 sc1 req1 k1 bail1)) ->
  (forall st' m, gone B false P (k st' (Some m))) ->
  gone B true P (alloc_group R lay asr st sc req k bail).
Proof.
  intros Hm Hd Hreq HB Hasr Hk. unfold alloc_group. eapply g1_alloc_meta; [exact Hm | exact Hd|].
  intros st1 m Hm1. cbv beta iota.
  set (size := UNIT * size_class sc) in *.
  assert (Hsz : 0 <= size <= 131056) by (subst size; pose proof (size_class_bounds sc); unfold UNIT; lia).
  set (c0 := if sc <? 9 then small_cnt_pick sc (usage st1 sc)
             else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) size) in *.
  assert (Hc0 : 0 <= c0 <= 32).
  { subst c0. destruct (sc <? 9); [apply small_cnt_pick_bounds | apply halve_big_bounds, halve_even_bounds, med_cnt_bounds]. }
  set (c1 := if (c0 =? 1) && (size * c0 + UNIT <=? PGSZ / 2) then 2 else c0) in *.
  assert (Hc1 : 0 <= c1 <= 32) by (subst c1; destruct ((c0 =? 1) && (size * c0 + UNIT <=? PGSZ / 2)); lia).
  clearbody c1. clear Hc0. clearbody c0 size.
  destruct (PGSZ / 2 <? size * c1 + UNIT) eqn:Ebr.
  -
    set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage (step_seq (account_bounce sc st1)) (sc + 1) else usage st1 sc) in *.
    clearbody u1.
    set (c2 := if (u1 <? 4 * c1) && negb (is_bouncing sc st1)
               then if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * c1) then 2
                    else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * c1) then 3
                    else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * c1) then 3
                    else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * c1) then 5 else c1
               else c1) in *.
    assert (Hc2 : 0 <= c2 <= 32).
    { subst c2. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. }
    clearbody c2.
    pose proof (round_up_pg_bounds (req + IB + UNIT)) as Hr1. pose proof (round_up_pg_bounds (size * c2 + UNIT)) as Hr2.
    assert (Hlen1 : 0 < round_up_pg (req + IB + UNIT) <= B) by (unfold IB, UNIT in *; lia).
    assert (Hlen2 : 0 < round_up_pg (size * c2 + UNIT) <= B) by (unfold UNIT in *; nia).
    assert (Hev : forall cnt needed, 0 < needed <= B ->
              gone B true P (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
                if negb (mmap_answer_ok (s_atop (step_seq (account_bounce sc st1))) (live_ranges (step_seq (account_bounce sc st1))) needed r) then bad_answer bail else
                if is_err r then free_meta m (step_seq (account_bounce sc st1)) (fun st2 => k st2 None) bail
                else
                  let '(st2, rid) := new_region RKGroup r needed (step_seq (account_bounce sc st1)) in
                  let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
                  let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
                  let ai := (4096 - UNIT) / size - 1 in
                  let ai := if cnt - 1 <? ai then cnt - 1 else ai in
                  let ai := if ai <? 0 then 0 else ai in
                  ag_tail lay st4 sc m (rid, 0) cnt ai k))).
    { intros cnt needed Hn. cbn [gone]. repeat (split; [reflexivity || exact Hn|]).
      intros z Hz. destruct (negb _); [exact I|]. rewrite Hz.
      destruct (new_region _ _ _ _) as [st2 rid]. unfold ag_tail. apply Hk. }
    destruct (negb (is_bouncing sc st1) && (c2 <=? 7)).
    + destruct ((round_up_pg (req + IB + UNIT) <? size + UNIT) || (4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2)).
      * apply Hev. exact Hlen1.
      * apply Hev. exact Hlen2.
    + apply Hev. exact Hlen2.
  -
    apply Z.ltb_ge in Ebr.
    apply Hasr; [exact Hm1 | unfold UNIT, IB, PGSZ in *; nia |].
    intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _) as [g|]; [|exact I]. unfold ag_tail. apply Hk.
Qed.


Lemma ctz32_nonneg first : 0 <= ctz32 first.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

Lemma g1_alloc_slot lay fuel : forall st sc req (k : mstate -> Z -> M R) bail d,
  metaok d st -> Z.of_nat fuel <= d -> 0 <= req <= 2^23 -> 2^24 <= B ->
  (forall st' idx, 0 <= idx -> gone B false P (k st' idx)) ->
  gone B true P (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail d Hm Hf Hreq HB Hk; cbn [alloc_slot]; [exact I|].
  apply g1_try_avail. intros st1 first K1.
  destruct (negb (first =? 0)); [apply gone_weaken, Hk, ctz32_nonneg|].
  eapply (g1_alloc_group lay (alloc_slot lay f) st1 sc req _ bail d); [eapply kc_metaok; eassumption | lia | exact Hreq | exact HB | |].
  - intros st2 sc1 req1 k1 bail1 Hm2 Hreq1 Hk1. eapply IH; [exact Hm2 | lia | exact Hreq1 | exact HB | exact Hk1].
  - intros st2 g. cbv beta iota. apply g1_queue. intros st4 _. apply Hk. lia.
Qed.

Lemma g1_malloc_small_ctrl lay st n (k : mstate -> option (aptr * Z) -> M R) bail d :
  metaok d st -> Z.of_nat FUEL <= d -> 0 <= n <= 2^23 -> 2^24 <= B ->
  (forall st' g idx, gone B false P (k st' (Some (g, idx)))) -> gone B true P (malloc_small_ctrl lay st n k bail).
Proof.
  intros Hm Hf Hn HB Hk. unfold malloc_small_ctrl.
  match goal with |- gone B true P (match ?g with Some _ => _ | None => _ end) => destruct g as [gp|] end.
  - destruct (negb _); [apply gone_weaken, Hk|].
    eapply g1_alloc_slot; [exact Hm | exact Hf | exact Hn | exact HB|].
    intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [apply Hk | exact I].
  - cbn iota. eapply g1_alloc_slot; [exact Hm | exact Hf | exact Hn | exact HB|].
    intros st' idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (active st' _); [apply Hk | exact I].
Qed.

End Walk.

Lemma kc_step_seq st : keeps_count st (step_seq st).
Proof. unfold keeps_count, step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

Lemma g1_malloc_core B lay st n d :
  metaok d st -> Z.of_nat FUEL <= d -> size_overflows n = false -> 0 <= n -> n + 20 <= B -> 2^24 <= B ->
  gone B true (fun r => exists g idx, snd r = Some (g, idx)) (malloc_core lay st n).
Proof.
  intros Hm Hf Hov Hn0 HnB HB. unfold malloc_core. rewrite Hov.
  destruct (MMAP_THRESHOLD <=? n) eqn:Ebig.
  - cbn [gone]. repeat (split; [reflexivity|]). split; [unfold IB, UNIT; lia|].
    intros z Hz. destruct (negb _); [exact I|]. rewrite Hz.
    destruct (new_region _ _ _ _) as [st1 rid] eqn:Enr.
    assert (K1 : keeps_count st st1).
    { unfold new_region in Enr. pose proof (f_equal fst Enr) as E1. cbn [fst] in E1. rewrite <- E1. reflexivity. }
    eapply (g1_alloc_meta B _ false d); [eapply kc_metaok; [|exact Hm]; eapply kc_trans; [exact K1 | apply kc_step_seq] | unfold FUEL in Hf; lia |].
    intros st3 g _. cbv beta iota. cbn. eauto.
  - apply Z.leb_gt in Ebig. eapply g1_malloc_small_ctrl; [exact Hm | exact Hf | unfold MMAP_THRESHOLD in Ebig; lia | exact HB|].
    intros st' g idx. cbn. eauto.
Qed.

Theorem cmalloc_gone B cs n d :
  metaok d cs -> Z.of_nat FUEL <= d -> size_overflows n = false -> 0 <= n -> n + 20 <= B -> 2^24 <= B ->
  gone B true (fun r => snd r <> None) (cmalloc cs n).
Proof.
  intros Hm Hf Hov Hn0 HnB HB. unfold cmalloc.
  eapply gone_sbind; [apply (g1_malloc_core B lay_none cs n d); assumption|].
  intros [st1 r] (g & idx & E). cbn in E. subst r. cbn. discriminate.
Qed.
