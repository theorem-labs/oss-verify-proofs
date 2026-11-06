(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Local Open Scope Z_scope.
Local Open Scope stree_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Export MallocCtrlA.
Unset Nia Cache. Unset Nra Cache.
Set Keyed Unification.

Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section CPS.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Context {R1 R2 : Type} (RR : O * R1 -> R2 -> Prop).
Local Notation KREL := (KREL pans pupd).
Local Notation KREL0 := (KREL0 pans pupd).
Local Notation BREL := (BREL pans pupd).
Local Notation prun := (prun pans pupd).

Lemma ag_tail_ctrl sc m p cnt ai k1 k2 :
  KREL RR k1 k2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (ag_tail full_lay st sc m p cnt ai k1)) (ag_tail lay_none cst sc m p cnt ai k2).
Proof. intros HK o st cst ->. unfold ag_tail. cbn [lh_hdr full_lay lay_none]. rewrite <- (strip_hdr_havoc p st). sync.
Qed.

Lemma alloc_group_ctrl rec1 rec2 sc req k1 k2 b1 b2 :
  (forall sc' req' k1' k2' b1' b2', KREL RR k1' k2' -> BREL RR b1' b2' ->
     forall o st cst, cst = strip st -> strel RR (prun o (rec1 st sc' req' k1' b1')) (rec2 cst sc' req' k2' b2')) ->
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (alloc_group R1 full_lay rec1 st sc req k1 b1)) (alloc_group R2 lay_none rec2 cst sc req k2 b2).
Proof.
  intros HR HK HB o st cst ->. pose proof (ag_tail_ctrl) as HT. pose proof (free_meta_ctrl pans pupd RR) as HF. pose proof (alloc_meta_ctrl pans pupd RR) as HA.
  unfold alloc_group, bad_answer. cbn [lh_nest full_lay lay_none]. sync.
Qed.

Lemma alloc_slot_ctrl fuel : forall sc req k1 k2 b1 b2,
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (alloc_slot full_lay fuel st sc req k1 b1)) (alloc_slot lay_none fuel cst sc req k2 b2).
Proof.
  induction fuel as [|f IH]; intros sc req k1 k2 b1 b2 HK HB o st cst ->.
  { cbn [alloc_slot]. sync. }
  pose proof (try_avail_ctrl pans pupd RR) as HTA. pose proof (queue_ctrl pans pupd RR) as HQ.
  pose proof (alloc_group_ctrl (alloc_slot full_lay f) (alloc_slot lay_none f)) as HG.
  cbn [alloc_slot]. sync.
Qed.

Definition DREL {X1 X2} (XX : O * X1 -> X2 -> Prop) (dec1 : decoder X1) (dec2 : decoder X2) : Prop :=
  forall p k1 k2 b1 b2,
    (forall o m idx, strel XX (prun o (k1 m idx)) (k2 m idx)) ->
    BREL XX b1 b2 ->
    forall o st cst, cst = strip st -> strel XX (prun o (dec1 st p k1 b1)) (dec2 cst p k2 b2).

Lemma dec_slots_drel : DREL RR (@dec_slots R1) (@dec_slots R2).
Proof.
  intros p k1 k2 b1 b2 HK HB o st cst ->. unfold dec_slots. srw.
  destruct (s_slots st !! p) as [[m idx]|]; [apply HK | sync].
Qed.

Lemma free_group_ctrl (dec1 : decoder R1) (dec2 : decoder R2) rec1 rec2 g k1 k2 b1 b2 :
  DREL RR dec1 dec2 ->
  (forall g' i' k1' k2' b1' b2', KREL RR k1' k2' -> BREL RR b1' b2' ->
     forall o st cst, cst = strip st -> strel RR (prun o (rec1 st g' i' k1' b1')) (rec2 cst g' i' k2' b2')) ->
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (free_group R1 dec1 rec1 st g k1 b1)) (free_group R2 dec2 rec2 cst g k2 b2).
Proof.
  intros HD HR HK HB o st cst ->. pose proof (free_meta_ctrl pans pupd RR) as HF.
  unfold free_group. sync.

  all: try (eapply HD; [ intros ? ? ? | assumption | solve_eq ]; sync).
Qed.

Lemma nontrivial_free_ctrl (dec1 : decoder R1) (dec2 : decoder R2) (HD : DREL RR dec1 dec2) fuel :
  forall g i k1 k2 b1 b2,
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (nontrivial_free dec1 fuel st g i k1 b1)) (nontrivial_free dec2 fuel cst g i k2 b2).
Proof.
  induction fuel as [|f IH]; intros g i k1 k2 b1 b2 HK HB o st cst ->.
  { cbn [nontrivial_free]. sync. }
  pose proof (free_group_ctrl dec1 dec2 (nontrivial_free dec1 f) (nontrivial_free dec2 f) g) as HG.
  pose proof (activate_group_ctrl pans pupd RR) as HA. pose proof (queue_ctrl pans pupd RR) as HQ.
  cbn [nontrivial_free]. unfold guard. sync.
Qed.

End CPS.

Section TOP.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Local Notation KREL := (KREL pans pupd).
Local Notation BREL := (BREL pans pupd).

Definition CREL (x : O * (mstate * option (aptr * Z))) (y : mstate * option (aptr * Z)) : Prop :=
  strip (fst (snd x)) = fst y /\ snd (snd x) = snd y.

Lemma malloc_small_ctrl_ctrl {R1 R2} (RR : O * R1 -> R2 -> Prop) n k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR ((prun pans pupd) o (malloc_small_ctrl full_lay st n k1 b1)) (malloc_small_ctrl lay_none cst n k2 b2).
Proof.
  intros HK HB o st cst ->. pose proof (alloc_slot_ctrl pans pupd RR FUEL) as HS.
  unfold malloc_small_ctrl. sync.
Qed.

Lemma malloc_core_ctrl n : forall o st cst, cst = strip st ->
  strel CREL ((prun pans pupd) o (malloc_core full_lay st n)) (malloc_core lay_none cst n).
Proof.
  intros o st cst ->.
  pose proof (@malloc_small_ctrl_ctrl _ _ CREL) as HS. pose proof (@alloc_meta_ctrl _ O pans pupd _ _ CREL) as HA.
  unfold malloc_core, bad_answer, ret. sync.
  all: try (split; [ solve_eq | reflexivity ]).
Qed.

Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Lemma rd8_prun {R} st p (k : Z -> M R) o :
  exists o' v, (prun pans pupd) o (rd8 st p k) = (prun pans pupd) o' (k v).
Proof.
  unfold rd8. destruct (cell_read _ _) as [v|hint].
  - exists o, v; reflexivity.
  - unfold prun. cbn [eruns psel].
    destruct (peek_answer_ok (pans o p (conc st p) hint)) eqn:E.
    + eexists _, _; reflexivity.
    + exfalso. unfold peek_answer_ok in E. pose proof (Hpans o p (conc st p) hint).
      apply Bool.andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E|apply Z.ltb_ge in E]; lia.
Qed.

Lemma rd16_prun {R} st p (k : Z -> M R) o :
  exists o' v, (prun pans pupd) o (rd16 st p k) = (prun pans pupd) o' (k v).
Proof.
  unfold rd16. destruct (rd8_prun st p (fun b0 => rd8 st (aadd p 1) (fun b1 => k (b0 + 256 * b1))) o) as (o1 & v1 & ->).
  destruct (rd8_prun st (aadd p 1) (fun b1 => k (v1 + 256 * b1)) o1) as (o2 & v2 & ->). eauto.
Qed.

Lemma enframe_read_off_prun {R} st g idx n ctr (k : Z -> M R) o :
  exists o' off, (prun pans pupd) o (enframe_read_off st g idx n ctr k) = (prun pans pupd) o' (k off).
Proof.
  unfold enframe_read_off.
  match goal with |- exists o' off, (prun pans pupd) o (rd8 ?s ?q ?kk) = _ => destruct (rd8_prun s q kk o) as (o1 & b3 & ->) end.
  destruct (negb (b3 =? 0)).
  - match goal with |- exists o' off, (prun pans pupd) o1 (rd16 ?s ?q ?kk) = _ => destruct (rd16_prun s q kk o1) as (o2 & v & ->) end. eauto.
  - eauto.
Qed.

Lemma enframe_at_ptr st g idx n off :
  snd (enframe_at st g idx n off) = slot_of st g idx \/ snd (enframe_at st g idx n off) = aadd (slot_of st g idx) (UNIT * off).
Proof.
  unfold enframe_at, slot_of, slot_start'. destruct (negb (off =? 0)); cbn -[Z.add Z.mul Z.sub get_stride]; auto.
Qed.

Definition MREL (x : O * (mstate * optr)) (y : mstate * option cptr) : Prop :=
  strip (fst (snd x)) = fst y /\
  match snd (snd x), snd y with
  | None, None => True
  | Some p, Some c => fst p = fst c /\ exists off, snd p = snd c + UNIT * off
  | _, _ => False
  end.

Lemma strel_smap_r {E A R1 R2 R3} (RR : R1 -> R2 -> Prop) (SS : R1 -> R3 -> Prop) (f : R2 -> R3)
  (t1 : stree E A R1) (t2 : stree E A R2) :
  strel RR t1 t2 -> (forall a b, RR a b -> SS a (f b)) -> strel SS t1 (smap f t2).
Proof. induction 1; intros; cbn; constructor; auto. Qed.

Lemma strel_steq_l {E A R1 R2} (RR : R1 -> R2 -> Prop) (t1 t1' : stree E A R1) (t2 : stree E A R2) :
  steq t1 t1' -> strel RR t1' t2 -> strel RR t1 t2.
Proof.
  intros H; revert t2; induction H; intros t2 Ht; inversion Ht; subst; constructor; eauto.
Qed.

Theorem malloc_control st n o :
  strel MREL ((prun pans pupd) o (malloc st n)) (cmalloc (strip st) n).
Proof.
  unfold malloc, cmalloc.
  eapply strel_steq_l. { unfold prun. apply eruns_sbind. }
  eapply strel_sbind.
  { apply (malloc_core_ctrl n o (set_tick (N.succ (s_tick st)) st)). reflexivity. }
  intros [o1 [S r]] [S' r'] [HS Hr]; cbn in HS, Hr; subst r' S'.
  destruct r as [[g idx]|].
  - destruct (enframe_read_off_prun S g idx n (c_mmap_counter (ctx S))
               (fun off => let '(st1, p) := enframe_at S g idx n off in ret (havoc p n st1, Some p)) o1) as (o2 & off & E).
    unfold enframe_full. cbn [fst snd]. unfold prun in E |- *. rewrite E.
    destruct (enframe_at S g idx n off) as [st1 p] eqn:Ea. unfold prun, ret; cbn [eruns psel]. constructor.
    split; cbn.
    + rewrite strip_havoc, strip_strip. pose proof (strip_enframe_at S g idx n off) as H1. rewrite Ea in H1. exact H1.
    + rewrite ?get_meta_rec_strip. pose proof (enframe_at_ptr S g idx n off) as Hp. rewrite Ea in Hp.
      unfold slot_of, slot_start', aadd in Hp. cbn [fst snd] in Hp.
      destruct Hp as [-> | ->]; cbn [fst snd]; [split; [reflexivity| exists 0; lia] | split; [reflexivity | exists off; lia]].
  - unfold prun, ret; cbn [eruns psel]. constructor. split; cbn; [rewrite strip_strip; reflexivity | exact I].
Qed.

Definition FREL (x : O * mstate) (y : mstate) : Prop := strip (snd x) = y.

Theorem free_tail_control (dec1 dec2 : decoder mstate) :
  DREL pans pupd (fun x y => strip (snd x) = strip y) dec1 dec2 ->
  forall st g idx o cst, cst = strip st ->
  strel (fun x y => strip (snd x) = strip y) ((prun pans pupd) o (free_tail dec1 st g idx)) (free_tail dec2 cst g idx).
Proof.
  intros HD st g idx o cst ->.
  pose proof (nontrivial_free_ctrl pans pupd (fun x y => strip (snd x) = strip y) dec1 dec2 HD FUEL) as HN.
  unfold free_tail, guard, bad_answer, ret. sync.
  all: cbn; rewrite ?strip_strip; try reflexivity; try solve_eq.
Qed.

Definition hdr_ok (st : mstate) (p : aptr) (c : cptr) : Prop :=
  exists st1 g idx,
    (forall o, (prun pans pupd) o (free_hdr st p) = SRet (o, Some (st1, g, idx)))
    /\ strip st1 = strip st
    /\ (s_slots st) !! c = Some (g, idx)
    /\ (forall o, strel (fun x y => strip (snd x) = strip y)
                        ((prun pans pupd) o (free_tail dec_hdr st1 g idx))
                        (free_tail dec_slots (strip st) g idx)).

Theorem free_control st p c o :
  hdr_ok st p c ->
  strel FREL ((prun pans pupd) o (free st (Some p))) (cfree (strip st) (Some c)).
Proof.
  intros (st1 & g & idx & Hh & Hs & Hc & Ht).
  unfold free, cfree. rewrite s_slots_strip, Hc.
  eapply strel_steq_l. { unfold prun. apply eruns_sbind. }
  unfold prun in Hh, Ht |- *. rewrite Hh. cbn [sbind fst snd].
  change (x__ <-- free_tail dec_slots (strip st) g idx;; ret (strip x__))
    with (smap strip (free_tail dec_slots (strip st) g idx)).
  apply (strel_smap_r _ _ _ _ _ (Ht o)). intros [o1 S] S' HS. exact HS.
Qed.

Lemma free_tail_slots_control st g idx o :
  strel (fun x y => strip (snd x) = strip y)
        ((prun pans pupd) o (free_tail dec_slots st g idx)) (free_tail dec_slots (strip st) g idx).
Proof. apply free_tail_control; [apply dec_slots_drel | reflexivity]. Qed.

Fixpoint follow {R} (t : M R) (ans : list Z) : option R :=
  match t, ans with
  | SRet r, _ => Some r
  | SVis (EUndef _) _, _ => None
  | SVis _ k, a :: ans' => follow (k a) ans'
  | SVis _ _, [] => None
  end.

Inductive reach : mstate -> list aptr -> list cptr -> Prop :=
| reach_init secret res : reach (minit secret res) [] []
| reach_malloc st L C n o ans o' st' p cst c :
    reach st L C ->
    follow ((prun pans pupd) o (malloc st n)) ans = Some (o', (st', Some p)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, Some c) ->
    reach st' (p :: L) (c :: C)
| reach_malloc_null st L C n o ans o' st' cst :
    reach st L C ->
    follow ((prun pans pupd) o (malloc st n)) ans = Some (o', (st', None)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, None) ->
    reach st' L C
| reach_free st L C i p c o ans o' st' :
    reach st L C ->
    nth_error L i = Some p -> nth_error C i = Some c ->
    follow ((prun pans pupd) o (free st (Some p))) ans = Some (o', st') ->
    reach st' (delete i L) (delete i C)
| reach_free_null st L C o ans o' st' :
    reach st L C ->
    follow ((prun pans pupd) o (free st None)) ans = Some (o', st') ->
    reach st' L C.

End TOP.

End CEIL.
