(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2 MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma add_bit_lor f i : 0 <= f -> 0 <= i -> Z.testbit f i = false -> f + 2 ^ i = Z.lor f (2 ^ i).
Proof.
  intros Hf Hi Hb. rewrite <- Z.lxor_lor.
  - apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros j Hj.
    rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec j i) as [->|NE].
    + rewrite Hb. reflexivity.
    + rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
  - apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec j i) as [->|NE].
    + rewrite Hb. reflexivity.
    + rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
Qed.

Lemma testbit_add_bit f i j : 0 <= f -> 0 <= i -> 0 <= j -> Z.testbit f i = false ->
  Z.testbit (f + 2 ^ i) j = Z.testbit f j || (i =? j).
Proof.
  intros Hf Hi Hj Hb. rewrite (add_bit_lor f i Hf Hi Hb). rewrite Z.lor_spec. f_equal.
  destruct (Z.eqb_spec i j) as [<-|NE]; [apply Z.pow2_bits_true; lia| apply Z.pow2_bits_false; lia].
Qed.

Lemma bit_eq i : bit i = 2 ^ i. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WR.
Variables (st : mstate) (q : aptr) (v : Z).
Let st' := wr8 q v st.

Lemma wr8_shadow_lookup rid :
  s_shadow st' !! rid = if (rid =? fst q)%N then Some (mkShadow (<[snd q := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst q)))) (r_hav (get_shadow st (fst q))) (r_havp (get_shadow st (fst q)))) else s_shadow st !! rid.
Proof.
  unfold st', wr8, upd_shadow. cbn. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.

Lemma wr8_dom (P : N -> Prop) :
  (forall rid sh, s_shadow st !! rid = Some sh -> P rid) -> P (fst q) ->
  forall rid sh, s_shadow st' !! rid = Some sh -> P rid.
Proof.
  intros H Hq rid sh. rewrite wr8_shadow_lookup. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [auto|]. apply H.
Qed.

Lemma wr8_tks (T : N) :
  (s_tick st <= T)%N ->
  (forall rid sh, s_shadow st !! rid = Some sh ->
      (forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N)) ->
  forall rid sh, s_shadow st' !! rid = Some sh ->
      (forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N).
Proof.
  intros HT H rid sh. rewrite wr8_shadow_lookup. destruct (N.eqb_spec rid (fst q)) as [->|NE]; [| apply H].
  intros E. inversion E. subst sh. cbn.
  assert (G : forall o w t, r_cells (get_shadow st (fst q)) !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N).
  { intros o w t Ho. unfold get_shadow in Ho. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Ho.
    - exact (proj1 (H _ _ E0) o w t Ho).
    - rewrite lookup_empty in Ho. discriminate. }
  assert (G2 : forall u hl ch, r_hav (get_shadow st (fst q)) !! u = Some hl -> In ch hl -> (snd ch <= T)%N).
  { intros u hl ch Hu Hin. unfold get_shadow in Hu. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hu.
    - exact (proj1 (proj2 (H _ _ E0)) u hl ch Hu Hin).
    - rewrite lookup_empty in Hu. discriminate. }
  assert (G3 : forall pg t, r_havp (get_shadow st (fst q)) !! pg = Some t -> (t <= T)%N).
  { intros pg t Hp. unfold get_shadow in Hp. destruct (s_shadow st !! fst q) as [sh0|] eqn:E0; cbn in Hp.
    - exact (proj2 (proj2 (H _ _ E0)) pg t Hp).
    - rewrite lookup_empty in Hp. discriminate. }
  split; [| split; [exact G2| exact G3]].
  intros o w t. destruct (Z.eq_dec o (snd q)) as [->|NEo].
  - rewrite lookup_insert_eq. intros X. inversion X. subst. split; [| exact HT].
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - rewrite lookup_insert_ne by congruence. apply G.
Qed.
End WR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xpend (X : extras) (p : option aptr) : extras := mkX (x_idle X) (x_zomb X) p (x_orph X) (x_fresh X).
Definition xorph (X : extras) (o : option N) : extras := mkX (x_idle X) (x_zomb X) (x_pend X) o (x_fresh X).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition NTF_SPEC : Prop :=
  forall (T : Type) (f : nat) X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
  INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
  x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
  exists st' mi LS',
    nontrivial_free dec_hdr f st g i k bail = k st' mi /\
    match mi with
    | None => INVL (xpend X None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
    end.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma g_remove_perm lG : forall rest b l,
  Permutation lG ((b, l) :: rest) -> (forall y, In y rest -> fst y <> b) -> Permutation (g_remove b lG) rest.
Proof.
  induction lG as [|y lG IH]; intros rest b l P Hr.
  - apply Permutation_nil_cons in P. destruct P.
  - cbn. assert (Hy : In y ((b, l) :: rest)) by (eapply Permutation_in; [exact P| left; reflexivity]).
    destruct (Z.eqb_spec (fst y) b) as [E|NE].
    + destruct Hy as [<-|Hy]; [| exfalso; exact (Hr _ Hy E)].
      apply Permutation_cons_inv with (a := (b, l)). exact P.
    + destruct Hy as [<-|Hy]; [cbn in NE; congruence|].
      (first [ pose proof ((in_split _ _ Hy)) as dR_1; dand3 dR_1 as r1 r2 -> | destruct (in_split _ _ Hy) as (r1 & r2 & ->) ]).
      assert (P' : Permutation lG ((b, l) :: r1 ++ r2)).
      { apply Permutation_cons_inv with (a := y). eapply Permutation_trans; [exact P|].
        change ((b, l) :: r1 ++ y :: r2) with (((b, l) :: r1) ++ y :: r2). change (y :: (b, l) :: r1 ++ r2) with (y :: ((b, l) :: r1) ++ r2).
        apply Permutation_sym. apply Permutation_middle. }
      eapply Permutation_trans; [| apply Permutation_middle]. apply perm_skip. apply (IH _ _ l P').
      intros z Hz. apply Hr. apply in_app_iff in Hz. apply in_app_iff. cbn. tauto.
Qed.

Lemma round_up_ge x : x <= round_up_pg x.
Proof. unfold round_up_pg. pose proof (proj2 (Z.land_nonneg (-x) (PGSZ - 1)) ltac:(right; unfold PGSZ; lia)). lia. Qed.

Lemma perm_filter {A} (f : A -> bool) l l' : Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  induction 1; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; assumption.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eauto.
Qed.

Lemma regions_delete_perm (st : mstate) rid r (F : N * region -> bool) :
  s_regions st !! rid = Some r ->
  Permutation (List.filter F (map_to_list (s_regions st))) (List.filter F ((rid, r) :: map_to_list (delete rid (s_regions st)))).
Proof. intros H. apply perm_filter. apply Permutation_sym. apply map_to_list_delete. exact H. Qed.

Lemma inv_S_X X X' st BL : x_pend X' = x_pend X -> inv_S X st BL -> inv_S X' st BL.
Proof. intros E I. destruct I; constructor; rewrite ?E; assumption. Qed.

Section DROP.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (r : region).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HO : x_orph X = Some rid.
Hypothesis Hr : s_regions st !! rid = Some r.
Let st' := drop_region rid st.
Let L' := KInv.set_groups (g_remove (r_base r) (ld_groups L)) L.
Let X' := xorph X None.

Lemma drop_lookup q : s_regions st' !! q = if (q =? rid)%N then None else s_regions st !! q.
Proof. apply lookup_drop_region. Qed.
Lemma drop_keep q rq : s_regions st !! q = Some rq -> q <> rid -> s_regions st' !! q = Some rq.
Proof. intros H NE. rewrite drop_lookup. destruct (N.eqb_spec q rid); [congruence| exact H]. Qed.
Lemma drop_some q rq : s_regions st' !! q = Some rq -> s_regions st !! q = Some rq /\ q <> rid.
Proof. rewrite drop_lookup. destruct (N.eqb_spec q rid); [discriminate| auto]. Qed.

Theorem INVL_drop_orph : INVL X' st' L' BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  (first [ pose proof ((ir_orph _ _ _ IR rid HO)) as dR_2; dex1 dR_2 as r0; dand3 dR_2 as Hr0 Hk NOG | pose proof ((ir_orph _ _ _ IR rid HO)) as dR_2; dand4 dR_2 as r0 Hr0 Hk NOG | pose proof (ir_orph _ _ _ IR rid HO) as (r0 & Hr0 & Hk & NOG) ]). rewrite Hr in Hr0. symmetry in Hr0. inversion Hr0. subst r0. clear Hr0.
  assert (KEEP : forall q rq, s_regions st !! q = Some rq -> r_kind rq <> RKGroup \/ q <> rid -> s_regions st' !! q = Some rq).
  { intros q rq Hq [K|NE]; apply drop_keep; auto. intros ->. rewrite Hr in Hq. inversion Hq. subst. congruence. }
  assert (FR : forall q rq, frontier st' q rq = frontier st q rq) by (intros; reflexivity).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; cbn -[drop_region g_remove frontier region_live_range round_up_pg Z.mul Z.pow Z.add].
    + intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (ir_ids q rq Hq).
    + intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (ir_shape q rq Hq).
    + intros q1 q2 r1 r2 H1 H2 NE. apply drop_some in H1 as [H1 _]. apply drop_some in H2 as [H2 _]. exact (ir_disj q1 q2 r1 r2 H1 H2 NE).
    + exact ir_resv.
    + (* [comment removed for export] *)
      apply g_remove_perm with (l := r_len r).
      * eapply Permutation_trans; [exact ir_groups|].
        eapply Permutation_trans; [apply Permutation_map; apply (regions_delete_perm st rid r _ Hr)|].
        cbn. rewrite Hk. cbn. apply perm_skip. unfold st', drop_region. cbn. apply Permutation_refl.
      * intros y Hy. apply in_map_iff in Hy as ([q rq] & <- & Hq). apply filter_In in Hq as [Hq Hkq]. cbn in Hkq |- *.
        apply elem_of_list_In in Hq || apply list_elem_of_In in Hq. apply elem_of_map_to_list in Hq.
        unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq].
        destruct (r_kind rq) eqn:Ek; try discriminate.
        intros E. pose proof (ir_disj q rid rq r Hq Hr ltac:(congruence)) as D. unfold region_live_range in D. rewrite Ek, Hk in D.
        (first [ pose proof ((ir_shape _ _ Hq)) as dR_3; dand4 dR_3 as S1 _ S3 _ | pose proof (ir_shape _ _ Hq) as (S1 & _ & S3 & _) ]). (first [ pose proof ((ir_shape _ _ Hr)) as dR_4; dand4 dR_4 as T1 _ T3 _ | pose proof (ir_shape _ _ Hr) as (T1 & _ & T3 & _) ]).
        pose proof (round_up_ge (r_len rq)). pose proof (round_up_ge (r_len r)). lia.
    + eapply Permutation_trans; [exact ir_metas|].
      eapply Permutation_trans; [apply Permutation_map; apply (regions_delete_perm st rid r _ Hr)|].
      cbn. rewrite Hk. cbn. unfold st', drop_region. cbn. apply Permutation_refl.
    + intros q rq Hq K. apply drop_some in Hq as [Hq _]. rewrite FR. exact (ir_metalen q rq Hq K).
    + intros q rq Hq K. apply drop_some in Hq as [Hq _]. rewrite FR. exact (ir_brkfront q rq Hq K).
    + destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
      right. exists q, rq. split; [apply KEEP; [exact Hq| left; congruence]| auto].
    + intros b l. rewrite ir_brkreg. split; ((first [ intro dR_20; dex2 dR_20 as q rq; dand4 dR_20 as Hq K E1 E2 | intro dR_20; dand6 dR_20 as q rq Hq K E1 E2 | intros (q & rq & Hq & K & E1 & E2) ])); exists q, rq.
      * split; [apply KEEP; [exact Hq| left; congruence]| auto].
      * apply drop_some in Hq as [Hq _]. auto.
    + intros q1 q2 r1 r2 H1 H2. apply drop_some in H1 as [H1 _]. apply drop_some in H2 as [H2 _]. exact (ir_brk1 q1 q2 r1 r2 H1 H2).
    + revert ir_brk. change (c_brk (s_ctx st')) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
      * destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply drop_some in Hq as [Hq _]. exact (NB q rq Hq).
      * exact IBK.
      * destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply KEEP; [exact Hq| left; congruence]| auto].
    + (first [ dand3 ir_cursor as C1 C2 C3 | destruct ir_cursor as (C1 & C2 & C3) ]). split; [exact C1|]. split; [exact C2|].
      intros q off E. (first [ pose proof ((C3 q off E)) as dR_6; dex1 dR_6 as rq; dand3 dR_6 as Hq K B | pose proof ((C3 q off E)) as dR_6; dand4 dR_6 as rq Hq K B | destruct (C3 q off E) as (rq & Hq & K & B) ]). exists rq. split; [apply KEEP; [exact Hq| left; destruct K; congruence]| auto].
    + intros q Hq. cbn in Hq. discriminate.
  - destruct IA; constructor; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
      exists rq. rewrite FR. split; [apply KEEP; [exact Hq| left; destruct K; congruence]| auto].
    + intros q Hq. (first [ pose proof ((ia_availptr q Hq)) as dR_7; dex1 dR_7 as rq; destruct dR_7 as [Hrq K] | pose proof ((ia_availptr q Hq)) as dR_7; dand3 dR_7 as rq Hrq K | destruct (ia_availptr q Hq) as (rq & Hrq & K) ]). exists rq. split; [apply KEEP; [exact Hrq| left; destruct K; congruence]| exact K].
  - apply (inv_M_ext X' st st'); [reflexivity| reflexivity|]. apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]. constructor.
    + intros m b ai Hb. apply (group_ok_ext X' st st'); [reflexivity| reflexivity| |].
      * intros q rq Hq K E. apply KEEP; [exact Hq|]. right. intros ->. specialize (NOG b E). rewrite NOG in Hb. discriminate.
      * apply (group_ok_X X); [reflexivity|]. eapply G1. exact Hb.
    + exact G2.
    + exact G3.
    + intros q rq Hq K _. apply drop_some in Hq as [Hq NE]. apply (G4 q rq Hq K). rewrite HO. congruence.
    + intros b h Hb. (first [ pose proof ((G5 b h Hb)) as dR_8; dex1 dR_8 as rq; destruct dR_8 as [Hq K] | pose proof ((G5 b h Hb)) as dR_8; dand3 dR_8 as rq Hq K | destruct (G5 b h Hb) as (rq & Hq & K) ]). exists rq. split; [| exact K]. apply KEEP; [exact Hq|]. right. intros E. specialize (NOG b E). rewrite NOG in Hb. discriminate.
  - apply (inv_S_ext X' st st' BL); [reflexivity| reflexivity| reflexivity|]. apply (inv_S_X X); [reflexivity| exact IS].
  - assert (GS : forall q, q <> rid -> get_shadow st' q = get_shadow st q).
    { intros q NE. unfold get_shadow, st', drop_region. cbn. rewrite lookup_delete_ne by congruence. reflexivity. }
    assert (KN : forall q o v, q <> rid -> known st (q, o) v -> known st' (q, o) v).
    { intros q o v NE K. unfold known, SHd in *. cbn [fst snd] in *. rewrite GS by exact NE. exact K. }
    assert (UN : forall q o, q <> rid -> unknown st (q, o) -> unknown st' (q, o)).
    { intros q o NE K. unfold unknown, SHd in *. cbn [fst snd] in *. rewrite GS by exact NE. exact K. }
    assert (HNE : forall b m, hosts st b m -> fst b <> rid).
    { intros b m [ai Hb] E. specialize (NOG b E). rewrite NOG in Hb. discriminate. }
    destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor.
    + intros q sh Hq. unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq].
      (first [ pose proof ((D1 q sh Hq)) as dR_9; dex1 dR_9 as rq; destruct dR_9 as [Hrq K] | pose proof ((D1 q sh Hq)) as dR_9; dand3 dR_9 as rq Hrq K | destruct (D1 q sh Hq) as (rq & Hrq & K) ]). exists rq. split; [apply drop_keep; auto| exact K].
    + intros q sh Hq. unfold st', drop_region in Hq. cbn in Hq. apply lookup_delete_Some in Hq as [NE Hq]. eapply D2. exact Hq.
    + intros b m i Hb Hi. apply KN; [exact (HNE b m Hb)|]. apply (D3 b m i Hb Hi).
    + intros b m o Hb Ho. apply UN; [exact (HNE b m Hb)|]. apply (D4 b m o Hb Ho).
    + intros b m p i Hb Hml Hs. (first [ pose proof ((D5 b m p i Hb Hml Hs)) as dR_10; dand4 dR_10 as (v3 & K3 & E3 & R3) K2 K1 Q | destruct (D5 b m p i Hb Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q) ]).
      pose proof (HNE b m Hb) as NE.
      split; [exists v3; split; [apply KN; [exact NE| exact K3]| auto]|]. split; [apply KN; [exact NE| exact K2]|]. split; [apply KN; [exact NE| exact K1]| exact Q].
    + intros k m i Hkk Hs. (first [ pose proof ((D6 k m i Hkk Hs)) as dR_11; dand8 dR_11 as A1 A2 A3 A4 A5 A6 A7 A8 | destruct (D6 k m i Hkk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) ]).
      assert (NE : fst (bslot k) <> rid).
      { (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_12; dand3 dR_12 as [b Hb] _ Ek | destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & Ek) ]). rewrite Ek. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb). exact (HNE b m Hb). }
      split; [apply KN; [exact NE| exact A1]|]. split; [apply KN; [exact NE| exact A2]|]. split; [apply KN; [exact NE| exact A3]|]. split; [apply KN; [exact NE| exact A4]|].
      split; [exact A5|]. split.
      * intros Hres. (first [ pose proof ((A6 Hres)) as dR_13; dand6 dR_13 as B1 B2 B3 B4 B5 B6 | destruct (A6 Hres) as (B1 & B2 & B3 & B4 & B5 & B6) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (apply KN; [exact NE| assumption]). exact B6.
      * split; [intros Hres; apply KN; [exact NE| apply A7; exact Hres]|]. intros a Ha. apply UN; [exact NE| apply A8; exact Ha].
Qed.
End DROP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_perm_map {A B} (f : A -> B) l l' x : Permutation l (map f l') -> In x l' -> In (f x) l.
Proof. intros P Hx. eapply Permutation_in; [apply Permutation_sym; exact P|]. apply in_map. exact Hx. Qed.

(* [comment removed for export] *)
Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma group_region_in_ledger X st L rid r :
  inv_R X st L -> s_regions st !! rid = Some r -> r_kind r = RKGroup -> In (r_base r, r_len r) (ld_groups L).
Proof.
  intros IR Hr Hk. pose proof (ir_groups _ _ _ IR) as P.
  apply (In_perm_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) _ _ (rid, r) P).
  apply filter_In. split; [| rewrite Hk; reflexivity]. apply list_elem_of_In. apply elem_of_map_to_list. exact Hr.
Qed.

Lemma brk_quiet_of X st L : inv_R X st L -> brk_quiet L.
Proof.
  intros IR. pose proof (ir_brk _ _ _ IR) as B. unfold brk_quiet.
  destruct (c_brk (s_ctx st)); [destruct B as [-> _]| rewrite B| destruct B as [-> _]]; exact I.
Qed.

End CEIL2.

Section FREE.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Hypothesis NTF : NTF_SPEC.

Theorem free_INVL st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  ftree L (free st (Some (aadd c (UNIT * off))))
        (fun L' st' => exists LS', INVL x0 st' L' (bl_remove c BL) LS').
Proof.
  intros INV Hk.
  (first [ pose proof ((block_facts x0 st L BL LS INV c off n Hk)) as dR_14; dex7 dR_14 as m bm i ai a ar ka; rename dR_14 into BF | pose proof ((block_facts x0 st L BL LS INV c off n Hk)) as dR_14; dand8 dR_14 as m bm i ai a ar ka BF | destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF) ]).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  unfold free. rewrite (free_hdr_eq st c off n m bm i ai a ar ka BF). cbn [sbind].
  set (p := aadd c (UNIT * off)).
  set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)).
  (* [comment removed for export] *)
  assert (CE1 : ctrl_eq st st1) by (eapply ctrl_eq_trans; [apply ctrl_eq_wr8| apply ctrl_eq_wr16]).
  assert (TK1 : s_tick st1 = s_tick st) by reflexivity.
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
  pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [SG _].
  assert (INV1 : INVL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS).
  { change c with (bslot ((c, off), n)) at 1 2.
    apply (INVL_remove_block x0 st st1 L BL LS ((c, off), n) INV Hk eq_refl CE1 TK1).
    - intros m' i' Hs' q Hq. cbn [bslot fst snd] in Hs', Hq. rewrite Hs in Hs'. inversion Hs'. subst m' i'.
      subst st1. unfold wr16. rewrite !cell_read_wr8_other; [reflexivity| | |];
        intros ->; apply Hq; unfold inT; subst p; rewrite Ec; cbn [fst snd aadd]; rewrite sstart_succ; unfold UNIT, IB in *; lia.
    - subst st1. unfold wr16. set (P := fun rid : N => exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup).
      change (forall rid sh, s_shadow (wr8 (aadd (aadd p (-2)) 1) (Z.shiftr 0 8) (wr8 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st))) !! rid = Some sh -> P rid).
      assert (HP : P (fst bm)) by ((first [ pose proof ((ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))) as dR_15; dex1 dR_15 as r; destruct dR_15 as [Hr Hkr] | pose proof ((ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))) as dR_15; dand3 dR_15 as r Hr Hkr | destruct (ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r & Hr & Hkr) ]); exists r; auto).
      assert (Efst : forall d1 d2, fst (aadd (aadd p d1) d2) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      assert (Efst1 : forall d1, fst (aadd p d1) = fst bm) by (intros; subst p; rewrite Ec; reflexivity).
      apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [apply (wr8_dom _ _ _ P); [exact (ish_dom _ _ ISH)|]|]|]; rewrite ?Efst, ?Efst1; exact HP.
    - subst st1. unfold wr16. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. apply wr8_tks; [cbn; lia|]. exact (ish_ticks _ _ ISH). }
  (* [comment removed for export] *)
  unfold free_tail.
  assert (MR1' : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; reflexivity).
  assert (MR1 : forall x, get_meta_rec st1 x = get_meta_rec st x) by exact MR1'.
  rewrite !MR1.
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  rewrite (guard_true 60) by (unfold testbit; rewrite Z.lor_spec; fold (MR st m); rewrite NA, NF; reflexivity).
  fold (MR st m).
  destruct (negb ((m_freed (MR st m) =? 0) || (Z.lor (m_freed (MR st m)) (m_avail (MR st m)) + bit i =? mask_upto (m_last_idx (MR st m))))) eqn:BR.
  - (* [comment removed for export] *)
    cbn [ftree ret]. exists LS.
    pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as GO.
    (first [ pose proof ((g_masks _ _ _ _ _ _ GO)) as dR_16; dand6 dR_16 as M1 M2 M3 M4 M5 M6 | pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6) ]).
    assert (Efun : upd_meta m (m_set_freed (m_freed (MR st m) + bit i)) st1
                  = upd_meta m (fun r => m_set_avail (m_avail (MR st m)) (m_set_freed (m_freed (MR st m) + bit i) r)) st1).
    { unfold upd_meta. f_equal. all: rewrite <- (MR1 m); fold (MR st1 m); destruct (MR st1 m); reflexivity. }
    rewrite Efun.
    assert (Hfr : m_freed (MR st m) <> 0).
    { intros E. rewrite E in BR. cbn in BR. discriminate. }
    apply (INVL_mask_change (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm ai (m_avail (MR st m)) (m_freed (MR st m) + bit i) None INV1).
    + exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF).
    + rewrite !MR1'. rewrite bit_eq. unfold tbit.
      split; [exact M1|]. split; [pose proof (Z.pow_nonneg 2 i); lia|]. split; [exact M3|]. split; [| split].
      * intros j Hj. rewrite testbit_add_bit by (auto; lia). rewrite Bool.orb_true_iff. intros [H|H]; [apply M4; auto| apply Z.eqb_eq in H; lia].
      * intros j Hj Ha. rewrite testbit_add_bit by (auto; lia). rewrite Bool.orb_true_iff. intros [H|H]; [exact (M5 j Hj Ha H)| apply Z.eqb_eq in H; subst j; rewrite NA in Ha; discriminate].
      * pose proof (bf_ai _ _ _ _ _ _ _ _ _ _ _ BF) as AI. intros j Hj. rewrite testbit_add_bit by (auto; lia). unfold tbit in M6. rewrite (M6 j Hj). reflexivity.
    + (* [comment removed for export] *)
      intros j Hj. rewrite !MR1'. cbn zeta.
      (first [ dand7 INV1 as _ _ _ _ _ IS1 _ | destruct INV1 as (_ & _ & _ & _ & _ & IS1 & _) ]).
      pose proof (is_part _ _ _ IS1 bm m ai j (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) ltac:(rewrite MR1'; exact Hj)) as P1.
      rewrite !MR1' in P1. cbn zeta in P1. cbn [x_pend xpend] in P1.
      unfold tbit in *. rewrite bit_eq. rewrite testbit_add_bit by (auto; lia).
      rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))) in P1 |- *.
      assert (N5 : ~ (@None aptr = Some (fst bm, sstart (MR st m) j))) by discriminate.
      destruct (Z.eqb_spec i j) as [<-|NE].
      * rewrite <- Ec in P1 |- *. rewrite NF, Bool.orb_false_l || rewrite Bool.orb_true_r.
        unfold one5 in P1 |- *. rewrite NF in P1.
        clear - P1. revert P1.
        generalize (Z.testbit (m_avail (MR st m)) i = true) as A.
        generalize (In c (map bslot (bl_remove c BL))) as U. generalize (s_groups st1 !! c <> None) as Hh.
        generalize (@eq (option aptr) (Some c) (Some c)) as P5 || idtac.
        intros. assert (FF : ~ (false = true)) by discriminate. assert (N5 : forall x : aptr, ~ (@None aptr = Some x)) by discriminate.
        pose proof (N5 c). pose proof (@eq_refl (option aptr) (Some c)). tauto.
      * rewrite Bool.orb_false_r.
        assert (NS : ~ (Some c = Some (fst bm, sstart (MR st m) j))).
        { intros E. apply NE. assert (E2 : slot_start' (MR st m) i = slot_start' (MR st m) j).
          { rewrite !(slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))). rewrite <- Ec. congruence. }
          exact (proj2 (slot_key_inj _ _ _ IS _ _ _ _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) Hi Hj E2)). }
        unfold one5 in P1 |- *.
        clear - P1 NS N5. revert P1 NS N5.
        generalize (Z.testbit (m_avail (MR st m)) j = true) as A. generalize (Z.testbit (m_freed (MR st m)) j = true) as F.
        generalize (In (fst bm, sstart (MR st m) j) (map bslot (bl_remove c BL))) as U. generalize (s_groups st1 !! (fst bm, sstart (MR st m) j) <> None) as Hh.
        intros. tauto.
    + right. split.
      * intros s Hs'. cbn in Hs'. inversion Hs'. subst s. exists i. rewrite !MR1'. split; [exact Hi|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))). exact Ec.
      * intros s Hs'. discriminate.
    + intros _ sc Hin Hnh. split; [| pose proof (Z.pow_nonneg 2 i); rewrite bit_eq; lia]. exact (proj1 (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hin Hnh)).
    + intros _ Hsc NI. exfalso. apply Hfr. rewrite MR1' in Hsc. exact (proj2 (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc NI)).
    + intros _ Hsc Hst. exfalso. apply Hfr. rewrite MR1' in Hsc, Hst. exact (proj2 (g_under _ _ _ _ _ _ GO ltac:(discriminate) Hsc Hst)).
  - (* [comment removed for export] *)
    pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hb.
    assert (Hsc0 : 0 <= m_sizeclass (MR st m)).
    { pose proof (g_sc _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as [[? _]|(E63 & _)]; lia. }
    (first [ pose proof ((NTF mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1)) as dR_18; dex2 dR_18 as st' mi; dand3 dR_18 as LS' EQ POST | pose proof ((NTF mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1)) as dR_18; dand5 dR_18 as st' mi LS' EQ POST | destruct (NTF mstate FUEL (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i
                (fun st2 mi => match mi with
                               | Some (base, len) => if negb (len =? 0)
                                   then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1))
                                   else ret st2
                               | None => ret st2 end) (ret st1) INV1)
      as (st' & mi & LS' & EQ & POST) ]).
    + apply (hosts_ext st st1); [reflexivity|]. exists ai. exact Hb.
    + rewrite MR1'. exact Hi.
    + cbn [x_pend xpend]. rewrite MR1', Ec. reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold FUEL. lia.
    + rewrite MR1'. unfold FUEL. lia.
    + rewrite EQ. destruct mi as [[base len]|].
      * (first [ dex1 POST as r; dand6 POST as Hb0 Hr Hkr Hlen Hpos INV' | dand7 POST as r Hb0 Hr Hkr Hlen Hpos INV' | destruct POST as (r & Hb0 & Hr & Hkr & Hlen & Hpos & INV') ]).
        destruct (Z.eqb_spec len 0) as [|NZ]; [lia|]. cbn [negb].
        pose proof INV' as (IR' & _).
        cbn [ftree]. split.
        -- split; [exact (brk_quiet_of _ _ _ IR')|]. exists (r_len r). split; [| right; exact Hlen].
           rewrite (conc_eq st' base r Hr), Hb0, Z.add_0_r. exact (group_region_in_ledger _ _ _ _ _ IR' Hr Hkr).
        -- intros z. cbn [answer_ok]. destruct (munmap_answer_ok z); [| exact I].
           cbn [ftree ret]. exists LS'. rewrite (conc_eq st' base r Hr), Hb0, Z.add_0_r.
           apply (INVL_drop_orph (xorph (xpend (xpend x0 (Some c)) None) (Some (fst base))) st' L (bl_remove c BL) LS' (fst base) r INV' eq_refl Hr).
      * cbn [ftree ret]. exists LS'. exact POST.
Qed.
End FREE.
