(* omx-clap-core/fuzz_preset: NO MISS -- every removal of hrun finds its block live.

   S2 (lib/A/Prog/PresetSiteHeap.v, h-pre-b1) needs `hits_from [] (hrun sm x)`: an HRe, an HFr or a pj_free of
   the harness run removes only requests that are live at that point. With it, req_x is a real multiset
   difference and the heap below the slot (the driver's blocks H0) comes out unchanged
   (hlive_from_app_hits / hlive_frame).

   The definitions rm_hits, hev_hits and hits_from are h-pre-b1's, with the same text; rm_hits L s is
   PresetReqAt.subm L s (rm_hits_subm), so the two readings of a pj_free agree.

   The reader's own calls are closed by PresetReqAt.rd_okf. What this file adds is the block structure of a
   written-and-read-back tree (tblk, from PjRoundTrip.ttrace), which is what the rewrite's pj_set needs: the old
   value's blocks, and the object's kids and keys arrays, are part of the copy's blocks (set_tblk). Each pj_free's
   list (HBulk) is pj_free's order; the removals need it only up to Permutation: pj_frees_blocks (a tree the reader
   built from x, through NB_frees) and fo_tblk (a written-and-read tree).

   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip PresetReqAt.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ the state is read up to Permutation *)

Lemma rm1_perm : forall z a b, Permutation a b -> Permutation (rm1 z a) (rm1 z b).
Proof.
  intros z a b H. destruct (in_dec Z.eq_dec z a) as [Hin | Hout].
  - assert (Hinb : In z b) by (apply (Permutation_in z H); exact Hin).
    apply (perm_cons_cancel z).
    apply (Permutation_trans (Permutation_sym (rm1_in z a Hin))).
    exact (Permutation_trans H (rm1_in z b Hinb)).
  - assert (Houtb : ~ In z b) by (intros Hb; apply Hout; apply (Permutation_in z (Permutation_sym H)); exact Hb).
    rewrite (rm1_notin z a Hout), (rm1_notin z b Houtb). exact H.
Qed.

Lemma rmall_perm : forall L a b, Permutation a b -> Permutation (rmall L a) (rmall L b).
Proof.
  induction L as [|z L IH]; intros a b H; [exact H|].
  rewrite !rmall_cons. apply IH. apply rm1_perm. exact H.
Qed.

Lemma hstep_perm : forall e a b, Permutation a b -> Permutation (hstep a e) (hstep b e).
Proof.
  intros [n | m n | n | L] a b H; cbn [hstep].
  - apply perm_skip. exact H.
  - apply perm_skip. apply rm1_perm. exact H.
  - apply rm1_perm. exact H.
  - apply rmall_perm. exact H.
Qed.

Lemma hlive_from_perm : forall es a b, Permutation a b -> Permutation (hlive_from a es) (hlive_from b es).
Proof.
  induction es as [|e r IH]; intros a b H; [exact H|].
  rewrite !hlive_from_cons. apply IH. apply hstep_perm. exact H.
Qed.

Lemma okf_perm : forall es a b, Permutation a b -> okf a es -> okf b es.
Proof. intros es a b H. apply okf_mono. apply subm_perm. apply Permutation_sym. exact H. Qed.

Lemma hlive_frame : forall es A s, okf s es -> Permutation (hlive_from (A ++ s) es) (A ++ hlive_from s es).
Proof.
  intros es A s H.
  apply (Permutation_trans (hlive_from_perm es (A ++ s) (s ++ A) (Permutation_app_comm A s))).
  rewrite (hlive_from_okf es s A H). apply Permutation_app_comm.
Qed.

Lemma rm1_mid : forall z A B, Permutation (rm1 z (A ++ z :: B)) (A ++ B).
Proof.
  intros z A B.
  apply (Permutation_trans (rm1_perm z (A ++ z :: B) (z :: A ++ B) (Permutation_sym (Permutation_middle A B z)))).
  rewrite rm1_cons_eq. apply Permutation_refl.
Qed.

(* ================================================================ pj_free's order for a tree the reader built

   pj_frees ok x (PresetReqAt) lists the blocks of the tree pj_parse builds from x (complete, or the partial tree a
   refusal leaves) in pj_free's order. NB_frees: jfv / jfl give the reader's live blocks up to Permutation, from any
   heap; pj_frees_blocks: pj_frees ok x is a Permutation of rd_blocks (rtr ok x). *)

Lemma frame_mid : forall es A B s C, okf B es -> Permutation (hlive_from B es) C ->
  Permutation (hlive_from (A ++ B ++ s) es) (A ++ C ++ s).
Proof.
  intros es A B s C Hk Hp.
  assert (Hk' : okf (B ++ s) es) by (apply (okf_mono es B); [exists s; apply Permutation_refl | exact Hk]).
  apply (Permutation_trans (hlive_frame es A (B ++ s) Hk')). apply Permutation_app_head.
  rewrite (hlive_from_okf es B s Hk). apply Permutation_app_tail. exact Hp.
Qed.

Lemma jbind_tr : forall (A B : Type) (m : M A) (k : A -> M B) ok,
  snd (fst (jbind m k ok)) =
  match m ok with (Some a, t, ok1) => t ++ snd (fst (k a ok1)) | (None, t, _) => t end.
Proof.
  intros A B m k ok. unfold jbind.
  destruct (m ok) as [[[a|] t] ok1]; [destruct (k a ok1) as [[r t'] ok2]|]; reflexivity.
Qed.

(* a leaf's trace leaves its leaf block (lf) live *)
Definition leafok (tr : list ev) : Prop := forall s, hlive_from s (rd_hevs tr) = lf tr ++ s.

Local Ltac hl := cbn [fst snd rd_hevs flat_map rd_hev app lf hlive_from fold_left hstep].

Lemma string_live : forall z ok,
  match jr_string z ok with
  | (Some _, t, _) => leafok t
  | (None, t, _) => leafok t /\ lf t = []
  end.
Proof.
  intros z ok. unfold jr_string. destruct (scan z) as [q|].
  - unfold jbind, jalloc. destruct (take ok) as [b ok1]. destruct b; cbv beta iota.
    + destruct (decode z) as [[s r]|]; cbv beta iota.
      * unfold jret. intros s0. hl. reflexivity.
      * unfold jfree, jrefuse. split; [|reflexivity]. intros s0. hl. rewrite rm1_cons_eq. reflexivity.
    + split; [intros s0; reflexivity | reflexivity].
  - unfold jrefuse. split; [intros s0; reflexivity | reflexivity].
Qed.

Lemma leaf_string : forall y ok, leafok (snd (fst (jbind (jr_string y) (fun '(s, r) => jret (JStr s, r)) ok))).
Proof.
  intros y ok. pose proof (string_live y ok) as H. unfold jbind.
  destruct (jr_string y ok) as [[[[z r]|] t] ok1]; cbv beta iota.
  - unfold jret. cbn [fst snd]. rewrite app_nil_r. exact H.
  - cbn [fst snd]. exact (proj1 H).
Qed.

Lemma leaf_lit : forall w v x ok, leafok (snd (fst (lit w v x ok))).
Proof. intros w v x ok. unfold lit. destruct (prefixb w x); unfold jret, jrefuse; intros s; reflexivity. Qed.

Lemma name_live : forall o y ok,
  match jr_name o y ok with
  | (Some _, tn, _) => leafok tn
  | (None, tn, _) => leafok tn /\ lf tn = []
  end.
Proof.
  intros o y ok. unfold jr_name. destruct o.
  - destruct (skip y) as [|b z].
    + unfold jrefuse. split; [intros s; reflexivity | reflexivity].
    + destruct (b =? 34).
      * pose proof (jr_string_spec z ok) as Hs. pose proof (string_live z ok) as Hl.
        unfold jbind at 1.
        destruct (jr_string z ok) as [[[[nm r]|] t] ok1]; cbv beta iota.
        -- destruct Hs as (q & Hsc & Hd & Ht & Hlen). subst t.
           assert (Hb : sblock z = S q) by (unfold sblock; rewrite Hsc; reflexivity).
           destruct (skip r) as [|c r1].
           ++ unfold jbind, jfree, jrefuse. rewrite Hb. split; [|reflexivity].
              intros s. hl. rewrite rm1_cons_eq. reflexivity.
           ++ destruct (c =? 58).
              ** unfold jret. intros s. hl. reflexivity.
              ** unfold jbind, jfree, jrefuse. rewrite Hb. split; [|reflexivity].
                 intros s. hl. rewrite rm1_cons_eq. reflexivity.
        -- exact Hl.
      * unfold jrefuse. split; [intros s; reflexivity | reflexivity].
  - unfold jret. intros s. reflexivity.
Qed.

(* a grow, granted or refused, from the container's arrays: the arrays after it (gheld, when refused) *)
Lemma grow_perm : forall o n cap ok,
  match grow o n cap ok with
  | (Some c, tg, _) => Permutation (hlive_from (arrz o cap) (rd_hevs tg)) (arrz o c)
  | (None, tg, _) => Permutation (hlive_from (arrz o cap) (rd_hevs tg)) (gheld o cap tg)
  end.
Proof.
  intros o n cap ok. unfold grow.
  destruct (Nat.ltb n cap).
  { unfold jret. apply Permutation_refl. }
  cbv zeta.
  destruct (jrealloc_cases (56 * cap) (56 * (if Nat.eqb cap 0 then 8 else 2 * cap)) ok) as [[ok1 E1] | [ok1 E1]].
  - unfold jbind. rewrite E1. cbv beta iota.
    destruct o.
    + destruct (jrealloc_cases (8 * cap) (8 * (if Nat.eqb cap 0 then 8 else 2 * cap)) ok1)
        as [[ok2 E2] | [ok2 E2]]; try unfold jbind; rewrite E2; cbv beta iota; unfold jret;
        cbn [fst snd]; rewrite rd_hevs_app; cbn [rd_hevs flat_map app].
      * destruct cap as [|c].
        -- cbn [Nat.eqb arrz]. rewrite !rd_hev_grow_O. cbn [app].
           cbn [hstep hlive_from fold_left]. apply perm_swap.
        -- rewrite (rd_hev_grow_S (56 * S c) _ ltac:(lia)), (rd_hev_grow_S (8 * S c) _ ltac:(lia)).
           cbn [app arrz Nat.eqb].
           cbn [hstep hlive_from fold_left]. rewrite rm1_cons_eq.
           destruct (rm1_two (Z.of_nat (56 * (2 * S c)) + HEAD) (Z.of_nat (8 * S c) + HEAD))
             as [H2 | [Heq H2]]; rewrite H2.
           ++ apply perm_swap.
           ++ rewrite <- Heq. apply perm_swap.
      * destruct cap as [|c].
        -- cbn [Nat.eqb arrz gheld]. rewrite rd_hev_grow_O. cbn [app rd_hev].
           cbn [hstep hlive_from fold_left]. apply Permutation_refl.
        -- rewrite (rd_hev_grow_S (56 * S c) _ ltac:(lia)). cbn [app arrz Nat.eqb rd_hev gheld].
           cbn [hstep hlive_from fold_left]. rewrite rm1_cons_eq. apply Permutation_refl.
    + unfold jret. cbn [fst snd]. rewrite rd_hevs_app. cbn [rd_hevs flat_map app].
      destruct cap as [|c].
      * cbn [Nat.eqb arrz]. rewrite rd_hev_grow_O. cbn [app].
        cbn [hstep hlive_from fold_left]. apply Permutation_refl.
      * rewrite (rd_hev_grow_S (56 * S c) _ ltac:(lia)). cbn [app arrz Nat.eqb].
        cbn [hstep hlive_from fold_left]. rewrite rm1_cons_eq. apply Permutation_refl.
  - unfold jbind. rewrite E1. cbv beta iota. cbn [fst snd rd_hevs flat_map rd_hev app gheld hlive_from fold_left].
    apply Permutation_refl.
Qed.

Lemma cont_frees : forall loop floop d o x ok s,
  (forall d' o' n cap acc af y ok' s',
     Permutation (hlive_from (af ++ arrz o' cap ++ s') (rd_hevs (snd (fst (loop d' o' n cap acc y ok')))))
                 (floop d' o' n cap af y ok' ++ s')) ->
  Permutation (hlive_from s (rd_hevs (snd (fst (jr_cont loop d o x ok))))) (jf_cont floop d o x ok ++ s).
Proof.
  intros loop floop d o x ok s H. unfold jr_cont, jf_cont.
  destruct (Nat.ltb MAXD (S d)); [unfold jrefuse; apply Permutation_refl|].
  cbv zeta. destruct (skip (tl x)) as [|c r].
  - exact (H (S d) o 0%nat 0%nat [] [] [] ok s).
  - destruct (c =? closer o); [unfold jret; apply Permutation_refl|].
    exact (H (S d) o 0%nat 0%nat [] [] (c :: r) ok s).
Qed.

Section Frees.

Variable sm : list Z -> Z * Z.

Lemma leaf_number : forall x ok, leafok (snd (fst (jr_number sm x ok))).
Proof.
  intros x ok. unfold jr_number. cbv zeta.
  set (j := match x with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end).
  destruct (skipn j x) as [|c z].
  - unfold jrefuse. intros s. reflexivity.
  - destruct (negb (digit c)).
    + unfold jrefuse. intros s. reflexivity.
    + destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end).
      * unfold jrefuse. intros s. reflexivity.
      * destruct (span numch z) as [a r].
        unfold jbind, jalloc. destruct (take ok) as [b ok1]. destruct b; cbv beta iota.
        -- destruct (whole sm (firstn j x ++ c :: a)); unfold jret, jrefuse; intros s; hl; reflexivity.
        -- intros s. reflexivity.
Qed.

Lemma frees_fuel : forall f,
  (forall d x ok s, Permutation (hlive_from s (rd_hevs (snd (fst (jrv sm f d x ok))))) (jfv sm f d x ok ++ s)) /\
  (forall d o n cap acc af y ok s,
     Permutation (hlive_from (af ++ arrz o cap ++ s) (rd_hevs (snd (fst (jrl sm f d o n cap acc y ok)))))
                 (jfl sm f d o n cap af y ok ++ s)).
Proof.
  induction f as [|f [IHv IHl]].
  - split.
    + intros d x ok s. cbn [jrv jfv]. unfold jrefuse. apply Permutation_refl.
    + intros d o n cap acc af y ok s. cbn [jrl jfl]. unfold jrefuse. rewrite <- app_assoc. apply Permutation_refl.
  - split.
    + intros d x ok s. cbn [jrv jfv].
      destruct (skip x) as [|b y]; cbn [fst snd]; [unfold jrefuse; apply Permutation_refl|].
      destruct (b =? 123); cbn [fst snd]; [apply cont_frees; exact IHl|].
      destruct (b =? 91); cbn [fst snd]; [apply cont_frees; exact IHl|].
      assert (HL : forall T, leafok T -> Permutation (hlive_from s (rd_hevs T)) (lf T ++ s)).
      { intros T HT. rewrite (HT s). apply Permutation_refl. }
      apply HL.
      destruct (b =? 34); [apply leaf_string|].
      destruct (b =? 116); [apply leaf_lit|].
      destruct (b =? 102); [apply leaf_lit|].
      destruct (b =? 110); [apply leaf_lit|].
      apply leaf_number.
    + intros d o n cap acc af y ok s. cbn [jrl jfl].
      rewrite jbind_tr.
      pose proof (grow_perm o n cap ok) as Gp. pose proof (proj1 (grow_okf o n cap ok)) as Gk.
      destruct (grow o n cap ok) as [[[cap1|] tg] ok1]; cbn [fst snd] in Gk, Gp |- *.
      2: { rewrite <- app_assoc. exact (frame_mid _ af (arrz o cap) s _ Gk Gp). }
      rewrite rd_hevs_app, hlive_from_app.
      apply (Permutation_trans (hlive_from_perm _ _ (af ++ arrz o cap1 ++ s) (frame_mid _ af (arrz o cap) s _ Gk Gp))).
      rewrite jbind_tr.
      pose proof (name_live o y ok1) as Hn.
      destruct (jr_name o y ok1) as [[[[nm y1]|] tn] ok2]; cbn [fst snd] in Hn |- *.
      2: { destruct Hn as [Hn1 Hn2]. rewrite (Hn1 (af ++ arrz o cap1 ++ s)), Hn2, app_nil_l, <- app_assoc.
           apply Permutation_refl. }
      rewrite rd_hevs_app, hlive_from_app, (Hn (af ++ arrz o cap1 ++ s)).
      rewrite jbind_tr.
      pose proof (IHv d y1 ok2 (lf tn ++ af ++ arrz o cap1 ++ s)) as Hv.
      assert (PA : Permutation (jfv sm f d y1 ok2 ++ lf tn ++ af ++ arrz o cap1 ++ s)
                               (af ++ jfv sm f d y1 ok2 ++ lf tn ++ arrz o cap1 ++ s)).
      { pose proof (Permutation_app_swap_app (jfv sm f d y1 ok2 ++ lf tn) af (arrz o cap1 ++ s)) as P.
        rewrite <- !app_assoc in P. exact P. }
      destruct (jrv sm f d y1 ok2) as [[[[v r]|] tv] ok3]; cbn [fst snd] in Hv |- *.
      2: { rewrite <- !app_assoc. exact (Permutation_trans Hv PA). }
      rewrite rd_hevs_app, hlive_from_app.
      apply (Permutation_trans (hlive_from_perm _ _ _ (Permutation_trans Hv PA))).
      destruct (skip r) as [|c r1]; cbn [fst snd].
      { unfold jrefuse. rewrite <- !app_assoc. apply Permutation_refl. }
      destruct (c =? 44); cbn [fst snd].
      { pose proof (IHl d o (S n) cap1 ((nm, v) :: acc) (af ++ jfv sm f d y1 ok2 ++ lf tn) r1 ok3 s) as Hl.
        rewrite <- !app_assoc in Hl. exact Hl. }
      destruct (c =? closer o); unfold jret, jrefuse; rewrite <- !app_assoc; apply Permutation_refl.
Qed.

(* J1: the reader's live blocks, from any heap, are jfv / jfl's list (and no removal misses) *)
Theorem NB_frees : forall f,
  (forall d x ok s, okf s (rd_hevs (snd (fst (jrv sm f d x ok)))) /\
     Permutation (hlive_from s (rd_hevs (snd (fst (jrv sm f d x ok))))) (jfv sm f d x ok ++ s)) /\
  (forall d o n cap acc af y ok s,
     okf (af ++ arrz o cap ++ s) (rd_hevs (snd (fst (jrl sm f d o n cap acc y ok)))) /\
     Permutation (hlive_from (af ++ arrz o cap ++ s) (rd_hevs (snd (fst (jrl sm f d o n cap acc y ok)))))
                 (jfl sm f d o n cap af y ok ++ s)).
Proof.
  intros f. destruct (NB_fuel sm f) as [Kv Kl]. destruct (frees_fuel f) as [Pv Pl]. split.
  - intros d x ok s. split; [|apply Pv]. exact (okf_mono _ [] s (subm_nil s) (Kv d x ok)).
  - intros d o n cap acc af y ok s. split; [|apply Pl].
    apply (okf_mono _ (arrz o cap)); [|exact (Kl d o n cap acc y ok)].
    exists (af ++ s). apply Permutation_app_swap_app.
Qed.

(* J2: pj_free (out)'s list is the reader's live blocks, in pj_free's order *)
Theorem pj_frees_blocks : forall ok x, Permutation (pj_frees sm ok x) (rd_blocks (rtr sm ok x)).
Proof.
  intros ok x. unfold pj_frees, rtr, jr_run, jr_value, rd_blocks, hlive.
  pose proof (proj1 (frees_fuel (S (2 * length x))) 0%nat x ok []) as H. rewrite app_nil_r in H.
  apply Permutation_sym.
  destruct (jrv sm (S (2 * length x)) 0 x ok) as [[[[t r]|] tr] ok']; cbn [fst snd] in H |- *; exact H.
Qed.

End Frees.

(* ================================================================ h-pre-b1's reading of a removal *)

(* The removals of F, one block at a time, each find its request live. *)
Fixpoint rm_hits (F s : list Z) : Prop :=
  match F with
  | [] => True
  | z :: F' => In z s /\ rm_hits F' (rm1 z s)
  end.

(* A heap event removes only requests that are live in s. *)
Definition hev_hits (s : list Z) (e : hev) : Prop :=
  match e with
  | HMal _ => True
  | HRe m _ => In m s
  | HFr n => In n s
  | HBulk L => rm_hits L s
  end.

Fixpoint hits_from (s : list Z) (es : list hev) : Prop :=
  match es with
  | [] => True
  | e :: r => hev_hits s e /\ hits_from (hstep s e) r
  end.

Lemma rm_hits_subm : forall L s, subm L s -> rm_hits L s.
Proof.
  induction L as [|z L IH]; intros s H; [exact I|].
  destruct H as [d Hd].
  assert (Hin : In z s).
  { apply (Permutation_in z (Permutation_sym Hd)). left. reflexivity. }
  split; [exact Hin|]. apply IH. exists d.
  apply (rm1_perm_cons z s (L ++ d)). exact Hd.
Qed.

Lemma subm_rm_hits : forall L s, rm_hits L s -> subm L s.
Proof.
  induction L as [|z L IH]; intros s H; [apply subm_nil|].
  destruct H as [Hin Hr]. destruct (IH (rm1 z s) Hr) as [d Hd].
  exists d. apply (Permutation_trans (rm1_in z s Hin)).
  cbn [app]. apply perm_skip. exact Hd.
Qed.

Theorem hits_from_okf : forall es s, okf s es -> hits_from s es.
Proof.
  induction es as [|e r IH]; intros s H; [exact I|].
  destruct H as [Hh Hr]. split; [|apply IH; exact Hr].
  destruct e as [n | m n | n | L]; cbn [hits hev_hits] in *; try exact Hh.
  apply rm_hits_subm. exact Hh.
Qed.

Theorem okf_hits_from : forall es s, hits_from s es -> okf s es.
Proof.
  induction es as [|e r IH]; intros s H; [exact I|].
  destruct H as [Hh Hr]. split; [|apply IH; exact Hr].
  destruct e as [n | m n | n | L]; cbn [hits hev_hits] in *; try exact Hh.
  apply subm_rm_hits. exact Hh.
Qed.

(* ================================================================ realloc chains (the writer, rendered()) *)

Lemma chain_okf_h : forall cs hd old s, Forall (fun c => 0 < c) cs -> 0 < old ->
  okf ((old + hd) :: s) (chain hd old cs) /\
  (cs <> [] -> hlive_from ((old + hd) :: s) (chain hd old cs) = (last cs 0 + hd) :: s).
Proof.
  induction cs as [|c cs IH]; intros hd old s Hall Hold.
  - split; [exact I | intros H; contradiction].
  - apply Forall_cons_iff in Hall as [Hc Hall].
    cbn [chain]. rewrite (proj2 (Z.eqb_neq old 0)) by lia.
    assert (Hst : hstep ((old + hd) :: s) (HRe (old + hd) (c + hd)) = (c + hd) :: s).
    { cbn [hstep]. rewrite rm1_cons_eq. reflexivity. }
    destruct (IH hd c s Hall Hc) as [Hok Hlive].
    split.
    + cbn [okf]. split; [cbn [hits]; left; reflexivity|]. rewrite Hst. exact Hok.
    + intros _. rewrite hlive_from_cons, Hst.
      destruct cs as [|c2 cs].
      * cbn [chain last]. reflexivity.
      * cbn [last]. rewrite (Hlive ltac:(discriminate)). reflexivity.
Qed.

Lemma chain_okf : forall cs hd s, Forall (fun c => 0 < c) cs ->
  okf s (chain hd 0 cs) /\ (cs <> [] -> hlive_from s (chain hd 0 cs) = (last cs 0 + hd) :: s).
Proof.
  intros [|c cs] hd s Hall.
  - split; [exact I | intros H; contradiction].
  - apply Forall_cons_iff in Hall as [Hc Hall].
    cbn [chain]. rewrite Z.eqb_refl.
    assert (Hst : hstep s (HMal (c + hd)) = (c + hd) :: s) by reflexivity.
    destruct (chain_okf_h cs hd c s Hall Hc) as [Hok Hlive].
    split.
    + cbn [okf]. split; [exact I|]. rewrite Hst. exact Hok.
    + intros _. rewrite hlive_from_cons, Hst.
      destruct cs as [|c2 cs].
      * cbn [chain last]. reflexivity.
      * cbn [last]. rewrite (Hlive ltac:(discriminate)). reflexivity.
Qed.

Lemma dbl_pos : forall f c need, 0 < c -> 0 < dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [exact Hc|].
  destruct (need <=? c); [exact Hc|]. apply IH. lia.
Qed.

Lemma newcap_pos : forall c need, 0 <= c -> 0 < newcap c need.
Proof.
  intros c need Hc. unfold newcap. destruct (c =? 0) eqn:E.
  - apply dbl_pos. lia.
  - apply Z.eqb_neq in E. apply dbl_pos. lia.
Qed.

Lemma grow_calls_pos : forall ls k c, 0 <= c -> Forall (fun z => 0 < z) (grow_calls k c ls).
Proof.
  induction ls as [|l ls IH]; intros k c Hc; cbn [grow_calls]; [constructor|].
  destruct (c <? k + l + 1).
  - constructor; [apply newcap_pos; exact Hc|]. apply IH. pose proof (newcap_pos c (k + l + 1) Hc). lia.
  - apply IH. exact Hc.
Qed.

Lemma wcaps_pos : forall t p, Forall (fun z => 0 < z) (wcaps t p).
Proof. intros t p. unfold wcaps. apply grow_calls_pos. lia. Qed.

Lemma tx_caps_pos : forall ls k c, 0 <= k -> Forall (fun z => 0 <= z) ls ->
  Forall (fun z => 0 < z) (tx_caps k c ls).
Proof.
  induction ls as [|l ls IH]; intros k c Hk Hall; cbn [tx_caps]; [constructor|].
  apply Forall_cons_iff in Hall as [Hl Hall].
  destruct (c <? k + l + 1).
  - constructor; [lia|]. apply IH; [lia | exact Hall].
  - apply IH; [lia | exact Hall].
Qed.

(* tx_val's inner fixpoints, as standalone functions *)
Fixpoint txa (p : bool) (d : nat) (i : nat) (l : list jv) {struct l} : list Z :=
  match l with
  | [] => []
  | u :: r => (if Nat.eqb i 0 then [] else [1]) ++ (if p then tx_line (S d) else []) ++
              tx_val p (S d) u ++ txa p d (S i) r
  end.

Fixpoint txo (p : bool) (d : nat) (i : nat) (l : list (list Z * jv)) {struct l} : list Z :=
  match l with
  | [] => []
  | (k, u) :: r => (if Nat.eqb i 0 then [] else [1]) ++ (if p then tx_line (S d) else []) ++
                   tx_str k ++ [1] ++ (if p then [1] else []) ++ tx_val p (S d) u ++ txo p d (S i) r
  end.

Lemma txa_fix : forall (p : bool) (d : nat) (l : list jv) (i : nat),
  (fix go (i : nat) (l : list jv) {struct l} : list Z :=
     match l with
     | [] => @nil Z
     | u :: r => (if Nat.eqb i 0 then @nil Z else [1]) ++ (if p then tx_line (S d) else @nil Z) ++
                 tx_val p (S d) u ++ go (S i) r
     end) i l = txa p d i l.
Proof.
  intros p d l. induction l as [|u r IH]; intros i; [reflexivity|].
  cbn [txa]. rewrite <- (IH (S i)). reflexivity.
Qed.

Lemma txo_fix : forall (p : bool) (d : nat) (l : list (list Z * jv)) (i : nat),
  (fix go (i : nat) (l : list (list Z * jv)) {struct l} : list Z :=
     match l with
     | [] => @nil Z
     | (k, u) :: r => (if Nat.eqb i 0 then @nil Z else [1]) ++ (if p then tx_line (S d) else @nil Z) ++
                      tx_str k ++ [1] ++ (if p then [1] else @nil Z) ++ tx_val p (S d) u ++ go (S i) r
     end) i l = txo p d i l.
Proof.
  intros p d l. induction l as [|[k u] r IH]; intros i; [reflexivity|].
  cbn [txo]. rewrite <- (IH (S i)). reflexivity.
Qed.

Lemma tx_arr_eq : forall items p d, tx_val p d (JArr items) =
  1 :: txa p d 0 items ++ (match items with [] => [] | _ :: _ => if p then tx_line d else [] end) ++ [1].
Proof. intros items p d. cbn [tx_val]. rewrite txa_fix. reflexivity. Qed.

Lemma tx_obj_eq : forall ms p d, tx_val p d (JObj ms) =
  1 :: txo p d 0 ms ++ (match ms with [] => [] | _ :: _ => if p then tx_line d else [] end) ++ [1].
Proof. intros ms p d. cbn [tx_val]. rewrite txo_fix. reflexivity. Qed.

Definition nng (l : list Z) : Prop := Forall (fun z => 0 <= z) l.

Lemma nng_app : forall a b, nng a -> nng b -> nng (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. split; assumption. Qed.

Lemma nng_tx_line : forall d, nng (tx_line d).
Proof.
  intros d. unfold tx_line, nng. constructor; [lia|].
  apply Forall_forall. intros z Hz. apply repeat_spec in Hz. lia.
Qed.

Lemma nng_tx_str : forall z, nng (tx_str z).
Proof.
  intros z. unfold tx_str, nng. constructor; [lia|]. apply Forall_app. split.
  - apply Forall_forall. intros w Hw. apply in_flat_map in Hw as (c & _ & Hc).
    unfold tx_ch in Hc. destruct ((c =? 34) || (c =? 92)); [cbn [In] in Hc; destruct Hc as [<-|[<-|[]]]; lia|].
    destruct (32 <=? c); [cbn [In] in Hc; destruct Hc as [<-|[]]; lia|].
    destruct ((c =? 10) || (c =? 9) || (c =? 13)); cbn [In] in Hc; destruct Hc as [<-|[]]; lia.
  - constructor; [lia | constructor].
Qed.

Lemma nng_tx_val : forall t p d, nng (tx_val p d t).
Proof.
  intros t. induction t as [| | | txt bits | z | items IH | ms IH] using jv_ind'; intros p d.
  - unfold nng. repeat constructor; lia.
  - unfold nng. repeat constructor; lia.
  - unfold nng. repeat constructor; lia.
  - unfold nng. constructor; [lia | constructor].
  - apply nng_tx_str.
  - assert (Hgo : forall l i, Forall (fun t => forall p' d', nng (tx_val p' d' t)) l -> nng (txa p d i l)).
    { induction l as [|u r IHl]; intros i Hf; [constructor|].
      apply Forall_cons_iff in Hf as [Hu Hr]. cbn [txa].
      apply nng_app; [destruct (Nat.eqb i 0); [constructor|constructor; [lia|constructor]]|].
      apply nng_app; [destruct p; [apply nng_tx_line|constructor]|].
      apply nng_app; [apply Hu|]. apply IHl. exact Hr. }
    rewrite tx_arr_eq. constructor; [lia|].
    apply nng_app; [apply Hgo; exact IH|].
    apply nng_app; [destruct items; [constructor|destruct p; [apply nng_tx_line|constructor]]|].
    constructor; [lia|constructor].
  - assert (Hgo : forall l i, Forall (fun m => forall p' d', nng (tx_val p' d' (snd m))) l -> nng (txo p d i l)).
    { induction l as [|[k u] r IHl]; intros i Hf; [constructor|].
      apply Forall_cons_iff in Hf as [Hu Hr]. cbn [txo].
      apply nng_app; [destruct (Nat.eqb i 0); [constructor|constructor; [lia|constructor]]|].
      apply nng_app; [destruct p; [apply nng_tx_line|constructor]|].
      apply nng_app; [apply nng_tx_str|].
      apply nng_app; [constructor; [lia|constructor]|].
      apply nng_app; [destruct p; [constructor; [lia|constructor]|constructor]|].
      apply nng_app; [apply (Hu p (S d))|]. apply IHl. exact Hr. }
    rewrite tx_obj_eq. constructor; [lia|].
    apply nng_app; [apply Hgo; exact IH|].
    apply nng_app; [destruct ms; [constructor|destruct p; [apply nng_tx_line|constructor]]|].
    constructor; [lia|constructor].
Qed.

Lemma rcaps_pos : forall t p, Forall (fun z => 0 < z) (rcaps t p).
Proof.
  intros t p. unfold rcaps. apply tx_caps_pos; [lia|].
  constructor; [lia|]. apply Forall_app. split; [apply nng_tx_val|].
  destruct p; [constructor; [lia|constructor] | constructor].
Qed.

Lemma firstn_forall : forall (A : Type) (P : A -> Prop) l k, Forall P l -> Forall P (firstn k l).
Proof.
  intros A P l. induction l as [|u l IH]; intros k H; [rewrite firstn_nil; constructor|].
  destruct k as [|k]; [constructor|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [firstn]. constructor; [exact H1|]. apply IH. exact H2.
Qed.

Lemma wcaps_cons : forall t p, exists c r, wcaps t p = c :: r.
Proof.
  intros t p. unfold wcaps, wdpieces.
  assert (Hne : exists u pr, wvpieces t p 0 = u :: pr).
  { destruct t; cbn [wvpieces]; eexists; eexists; reflexivity. }
  destruct Hne as (u & pr & Hu). rewrite Hu.
  cbn [app piece_lens map grow_calls].
  rewrite (proj2 (Z.ltb_lt 0 (0 + Z.of_nat (length u) + 1))) by lia.
  eexists; eexists; reflexivity.
Qed.

Lemma rcaps_cons : forall t p, exists c r, rcaps t p = c :: r.
Proof.
  intros t p. unfold rcaps. cbn [tx_caps].
  rewrite (proj2 (Z.ltb_lt 0 (0 + 0 + 1))) by lia. eexists; eexists; reflexivity.
Qed.

Lemma w_evs_ok : forall t p s,
  okf s (w_evs t p) /\ hlive_from s (w_evs t p) = (last (wcaps t p) 0 + HEAD) :: s.
Proof.
  intros t p s. unfold w_evs.
  destruct (chain_okf (wcaps t p) HEAD s (wcaps_pos t p)) as [H1 H2].
  split; [exact H1|]. apply H2.
  destruct (wcaps_cons t p) as (c & r & E). rewrite E. discriminate.
Qed.

Lemma r_evs_ok : forall t p s,
  okf s (r_evs t p) /\ hlive_from s (r_evs t p) = (last (rcaps t p) 0 + 0) :: s.
Proof.
  intros t p s. unfold r_evs.
  destruct (chain_okf (rcaps t p) 0 s (rcaps_pos t p)) as [H1 H2].
  split; [exact H1|]. apply H2.
  destruct (rcaps_cons t p) as (c & r & E). rewrite E. discriminate.
Qed.

Lemma w_starved_ok : forall t p k s, okf s (w_starved t p k).
Proof.
  intros t p k s. unfold w_starved.
  destruct (chain_okf (firstn k (wcaps t p)) HEAD s (firstn_forall _ _ _ k (wcaps_pos t p))) as [H1 H2].
  apply okf_app. split; [exact H1|].
  destruct k as [|k]; [exact I|].
  assert (Hne : firstn (S k) (wcaps t p) <> []).
  { destruct (wcaps_cons t p) as (c & r & E). rewrite E. cbn [firstn]. discriminate. }
  rewrite (H2 Hne). cbn [okf hits]. split; [left; reflexivity | exact I].
Qed.

(* ================================================================ the blocks of a written-and-read tree *)

(* the capacity parse_items leaves after k items, from (n, cap) *)
Fixpoint capf (n cap k : nat) : nat :=
  match k with O => cap | S k' => capf (S n) (gcap n cap) k' end.

Lemma ncap_capf : forall k n cap, capf n cap (S k) = gcap (n + k) (capf n cap k).
Proof.
  induction k as [|k IH]; intros n cap.
  - cbn [capf]. rewrite Nat.add_0_r. reflexivity.
  - replace (capf n cap (S (S k))) with (capf (S n) (gcap n cap) (S k)) by reflexivity.
    replace (capf n cap (S k)) with (capf (S n) (gcap n cap) k) by reflexivity.
    rewrite (IH (S n) (gcap n cap)).
    replace (S n + k)%nat with (n + S k)%nat by lia. reflexivity.
Qed.

Lemma ncap_eq : forall k, ncap k = capf 0 0 k.
Proof.
  induction k as [|k IH]; [reflexivity|].
  cbn [ncap]. rewrite IH, (ncap_capf k 0 0). cbn [Nat.add]. reflexivity.
Qed.

Definition kblk (k : list Z) : Z := Z.of_nat (S (length (flat_map ech k))) + HEAD.

Fixpoint tblk (t : jv) : list Z :=
  match t with
  | JNum txt _ => [Z.of_nat (S (length txt)) + HEAD]
  | JStr z => [Z.of_nat (S (length (flat_map ech z))) + HEAD]
  | JArr items => arrz false (capf 0 0 (length items)) ++ concat (map tblk items)
  | JObj ms => arrz true (capf 0 0 (length ms)) ++
               concat (map (fun m => kblk (fst m) :: tblk (snd m)) ms)
  | _ => []
  end.

Lemma rm1_two_s : forall a b s, Permutation (rm1 b (a :: b :: s)) (a :: s).
Proof.
  intros a b s. cbn [rm1]. destruct (a =? b) eqn:E.
  - apply Z.eqb_eq in E. subst a. apply Permutation_refl.
  - rewrite Z.eqb_refl. apply Permutation_refl.
Qed.

Lemma grow_ev_ok : forall o n cap s,
  okf (arrz o cap ++ s) (rd_hevs (grow_ev o n cap)) /\
  Permutation (hlive_from (arrz o cap ++ s) (rd_hevs (grow_ev o n cap))) (arrz o (gcap n cap) ++ s).
Proof.
  intros o n cap s. unfold grow_ev, gcap.
  destruct (Nat.ltb n cap) eqn:E.
  { cbn [rd_hevs flat_map okf hlive_from fold_left]. split; [exact I | apply Permutation_refl]. }
  destruct cap as [|c].
  - cbn [Nat.eqb arrz app]. destruct o.
    + cbn [rd_hevs flat_map]. rewrite !rd_hev_grow_O. cbn [app].
      cbn [okf hits hstep hlive_from fold_left]. split; [repeat split; exact I|].
      cbn [arrz app]. apply perm_swap.
    + cbn [rd_hevs flat_map]. rewrite rd_hev_grow_O. cbn [app].
      cbn [okf hits hstep hlive_from fold_left]. split; [repeat split; exact I|].
      cbn [arrz app]. apply Permutation_refl.
  - set (K := Z.of_nat (56 * S c) + HEAD). set (Y := Z.of_nat (8 * S c) + HEAD).
    set (K' := Z.of_nat (56 * (2 * S c)) + HEAD). set (Y' := Z.of_nat (8 * (2 * S c)) + HEAD).
    destruct o.
    + cbn [rd_hevs flat_map].
      rewrite (rd_hev_grow_S (56 * S c) _ ltac:(lia)), (rd_hev_grow_S (8 * S c) _ ltac:(lia)).
      cbn [app arrz Nat.eqb].
      cbn [okf hits hstep hlive_from fold_left]. fold K. fold Y. fold K'. fold Y'.
      rewrite rm1_cons_eq.
      split.
      * split; [left; reflexivity|]. split; [right; left; reflexivity | exact I].
      * cbn [arrz]. fold K'. fold Y'.
        apply (Permutation_trans (perm_skip Y' (rm1_two_s K' Y s))).
        apply perm_swap.
    + cbn [rd_hevs flat_map]. rewrite (rd_hev_grow_S (56 * S c) _ ltac:(lia)).
      cbn [app arrz Nat.eqb].
      cbn [okf hits hstep hlive_from fold_left]. fold K. fold K'.
      rewrite rm1_cons_eq.
      split; [split; [left; reflexivity | exact I]|].
      cbn [arrz]. fold K'. apply Permutation_refl.
Qed.

Definition TTOK (t : jv) : Prop :=
  forall s, okf s (rd_hevs (ttrace t)) /\
            Permutation (hlive_from s (rd_hevs (ttrace t))) (tblk t ++ s).

Lemma perm_mv : forall (a : Z) A B C, Permutation (A ++ a :: B ++ C) (B ++ a :: A ++ C).
Proof.
  intros a A B C.
  apply (Permutation_trans (Permutation_sym (Permutation_middle A (B ++ C) a))).
  apply (Permutation_trans (perm_skip a (Permutation_app_swap_app A B C))).
  apply (Permutation_middle B (A ++ C) a).
Qed.

Lemma tgo_arr_ok : forall l n cap s, Forall TTOK l ->
  okf (arrz false cap ++ s) (rd_hevs (tgo_arr n cap l)) /\
  Permutation (hlive_from (arrz false cap ++ s) (rd_hevs (tgo_arr n cap l)))
              (arrz false (capf n cap (length l)) ++ concat (map tblk l) ++ s).
Proof.
  induction l as [|u r IH]; intros n cap s Hf.
  - cbn [tgo_arr rd_hevs flat_map length capf map concat app].
    split; [exact I | apply Permutation_refl].
  - apply Forall_cons_iff in Hf as [Hu Hr].
    cbn [tgo_arr]. rewrite !rd_hevs_app.
    destruct (grow_ev_ok false n cap s) as [G1 G2].
    destruct (Hu (hlive_from (arrz false cap ++ s) (rd_hevs (grow_ev false n cap)))) as [U1 U2].
    set (S1 := hlive_from (arrz false cap ++ s) (rd_hevs (grow_ev false n cap))) in *.
    set (S2 := hlive_from S1 (rd_hevs (ttrace u))) in *.
    assert (HS2 : Permutation S2 (arrz false (gcap n cap) ++ (tblk u ++ s))).
    { apply (Permutation_trans U2).
      apply (Permutation_trans (Permutation_app_head (tblk u) G2)).
      apply (Permutation_trans (Permutation_app_swap_app (tblk u) (arrz false (gcap n cap)) s)).
      apply Permutation_refl. }
    destruct (IH (S n) (gcap n cap) (tblk u ++ s) Hr) as [R1 R2].
    split.
    + apply okf_app. split; [exact G1|].
      apply okf_app. split; [exact U1|].
      apply (okf_perm _ _ _ (Permutation_sym HS2)). exact R1.
    + rewrite !hlive_from_app.
      apply (Permutation_trans (hlive_from_perm (rd_hevs (tgo_arr (S n) (gcap n cap) r)) S2
                                 (arrz false (gcap n cap) ++ (tblk u ++ s)) HS2)).
      apply (Permutation_trans R2).
      cbn [length capf map concat].
      rewrite <- !app_assoc.
      apply Permutation_app_head.
      apply (Permutation_trans (Permutation_app_swap_app (concat (map tblk r)) (tblk u) s)).
      apply Permutation_refl.
Qed.

Lemma rd_hevs_cons : forall e t, rd_hevs (e :: t) = rd_hev e ++ rd_hevs t.
Proof. reflexivity. Qed.

Lemma tgo_obj_ok : forall l n cap s, Forall (fun m => TTOK (snd m)) l ->
  okf (arrz true cap ++ s) (rd_hevs (tgo_obj n cap l)) /\
  Permutation (hlive_from (arrz true cap ++ s) (rd_hevs (tgo_obj n cap l)))
              (arrz true (capf n cap (length l)) ++
               concat (map (fun m => kblk (fst m) :: tblk (snd m)) l) ++ s).
Proof.
  induction l as [|[k u] r IH]; intros n cap s Hf.
  - cbn [tgo_obj rd_hevs flat_map length capf map concat app].
    split; [exact I | apply Permutation_refl].
  - apply Forall_cons_iff in Hf as [Hu Hr]. cbn [snd] in Hu.
    cbn [tgo_obj]. rewrite rd_hevs_app, rd_hevs_cons, rd_hevs_app.
    change (rd_hev (EAlloc (S (length (flat_map ech k))))) with [HMal (kblk k)].
    destruct (grow_ev_ok true n cap s) as [G1 G2].
    set (S1 := hlive_from (arrz true cap ++ s) (rd_hevs (grow_ev true n cap))) in *.
    assert (HS1k : Permutation (kblk k :: S1) (kblk k :: arrz true (gcap n cap) ++ s))
      by (apply perm_skip; exact G2).
    destruct (Hu (kblk k :: S1)) as [U1 U2].
    set (S2 := hlive_from (kblk k :: S1) (rd_hevs (ttrace u))) in *.
    assert (HS2 : Permutation S2 (arrz true (gcap n cap) ++ (kblk k :: tblk u ++ s))).
    { apply (Permutation_trans U2).
      apply (Permutation_trans (Permutation_app_head (tblk u) HS1k)).
      exact (perm_mv (kblk k) (tblk u) (arrz true (gcap n cap)) s). }
    destruct (IH (S n) (gcap n cap) (kblk k :: tblk u ++ s) Hr) as [R1 R2].
    assert (Hst : hlive_from S1 [HMal (kblk k)] = kblk k :: S1) by reflexivity.
    split.
    + apply okf_app. split; [exact G1|]. fold S1.
      apply okf_app. split; [cbn [okf hits]; split; exact I|].
      rewrite Hst. apply okf_app. split; [exact U1|].
      fold S2. apply (okf_perm _ _ _ (Permutation_sym HS2)). exact R1.
    + rewrite !hlive_from_app. fold S1. rewrite Hst. fold S2.
      apply (Permutation_trans (hlive_from_perm (rd_hevs (tgo_obj (S n) (gcap n cap) r)) S2
                                 (arrz true (gcap n cap) ++ (kblk k :: tblk u ++ s)) HS2)).
      apply (Permutation_trans R2).
      cbn [length capf map concat fst snd].
      rewrite <- !app_assoc.
      apply Permutation_app_head.
      apply (Permutation_trans (Permutation_sym (Permutation_middle _ (tblk u ++ s) (kblk k)))).
      apply perm_skip. apply Permutation_app_swap_app.
Qed.

Theorem tt_ok : forall t, TTOK t.
Proof.
  intros t. induction t as [| | | txt bits | z | items IH | ms IH] using jv_ind'; intros s.
  - cbn [ttrace rd_hevs flat_map okf tblk app]. split; [exact I | apply Permutation_refl].
  - cbn [ttrace rd_hevs flat_map okf tblk app]. split; [exact I | apply Permutation_refl].
  - cbn [ttrace rd_hevs flat_map okf tblk app]. split; [exact I | apply Permutation_refl].
  - cbn [ttrace rd_hevs flat_map rd_hev app okf hits hstep hlive_from fold_left tblk].
    split; [split; exact I | apply Permutation_refl].
  - cbn [ttrace rd_hevs flat_map rd_hev app okf hits hstep hlive_from fold_left tblk].
    split; [split; exact I | apply Permutation_refl].
  - rewrite tt_arr.
    destruct (tgo_arr_ok items 0 0 s IH) as [H1 H2].
    cbn [arrz app] in H1, H2. split; [exact H1|].
    apply (Permutation_trans H2). cbn [tblk]. rewrite <- app_assoc. apply Permutation_refl.
  - rewrite tt_obj.
    destruct (tgo_obj_ok ms 0 0 s IH) as [H1 H2].
    cbn [arrz app] in H1, H2. split; [exact H1|].
    apply (Permutation_trans H2). cbn [tblk]. rewrite <- app_assoc. apply Permutation_refl.
Qed.

Corollary ttrace_okf : forall t s, okf s (rd_hevs (ttrace t)).
Proof. intros t s. exact (proj1 (tt_ok t s)). Qed.

Corollary ttrace_blocks : forall t, Permutation (rd_blocks (ttrace t)) (tblk t).
Proof.
  intros t. unfold rd_blocks, hlive.
  apply (Permutation_trans (proj2 (tt_ok t []))). rewrite app_nil_r. apply Permutation_refl.
Qed.

(* pj_free's list of a written-and-read tree (or a pj_set result) holds the tree's blocks *)
Lemma fo_tblk : forall t, Permutation (fo t) (tblk t).
Proof.
  intros t. induction t as [| | | txt bits | z | items IH | ms IH] using jv_ind'.
  1-5: apply Permutation_refl.
  - cbn [fo tblk]. rewrite <- ncap_eq.
    apply (Permutation_trans (Permutation_app_comm _ _)). apply Permutation_app_head.
    induction IH as [|u r Hu Hr IHr]; [apply Permutation_refl|].
    cbn [map concat]. apply Permutation_app; assumption.
  - cbn [fo tblk]. rewrite <- ncap_eq.
    apply (Permutation_trans (Permutation_app_comm _ _)). apply Permutation_app_head.
    induction IH as [|[k u] r Hu Hr IHr]; [apply Permutation_refl|].
    cbn [map concat fst snd] in Hu |- *. apply Permutation_app; [|exact IHr].
    apply (Permutation_trans (Permutation_app_comm _ _)). cbn [app]. apply perm_skip. exact Hu.
Qed.

Corollary fo_blocks : forall t, Permutation (fo t) (rd_blocks (ttrace t)).
Proof. intros t. apply (Permutation_trans (fo_tblk t)). apply Permutation_sym. apply ttrace_blocks. Qed.

Lemma tblk_member : forall ms k u, In (k, u) ms -> subm (tblk u) (tblk (JObj ms)).
Proof.
  intros ms k u Hin. cbn [tblk].
  apply (subm_trans _ (concat (map (fun m => kblk (fst m) :: tblk (snd m)) ms))).
  - clear - Hin. induction ms as [|m r IH]; [destruct Hin|].
    cbn [map concat]. destruct Hin as [-> | Hin].
    + cbn [fst snd]. exists (kblk k :: concat (map (fun m => kblk (fst m) :: tblk (snd m)) r)).
      exact (Permutation_middle (tblk u) (concat (map (fun m => kblk (fst m) :: tblk (snd m)) r)) (kblk k)).
    + apply (subm_trans _ (concat (map (fun m => kblk (fst m) :: tblk (snd m)) r))); [apply IH; exact Hin|].
      exists (kblk (fst m) :: tblk (snd m)).
      apply Permutation_app_comm.
  - exists (arrz true (capf 0 0 (length ms))). apply Permutation_app_comm.
Qed.

Lemma tblk_array : forall ms, subm (arrz true (ncap (length ms))) (tblk (JObj ms)).
Proof.
  intros ms. cbn [tblk]. rewrite ncap_eq.
  exists (concat (map (fun m => kblk (fst m) :: tblk (snd m)) ms)). apply Permutation_refl.
Qed.

(* ================================================================ the harness's segments *)

Lemma seg_step : forall a es d b, okf a es -> Permutation b (a ++ d) ->
  okf b es /\ Permutation (hlive_from b es) (hlive_from a es ++ d).
Proof.
  intros a es d b Hk Hb. split.
  - apply (okf_perm es (a ++ d) b (Permutation_sym Hb)).
    apply (okf_mono es a (a ++ d)); [exists d; apply Permutation_refl | exact Hk].
  - apply (Permutation_trans (hlive_from_perm es b (a ++ d) Hb)).
    rewrite (hlive_from_okf es a d Hk). apply Permutation_refl.
Qed.

Lemma bulk_ok : forall L S R, Permutation S (L ++ R) ->
  hits S (HBulk L) /\ Permutation (hstep S (HBulk L)) R.
Proof.
  intros L S R H. split.
  - cbn [hits]. exists R. exact H.
  - cbn [hstep]. apply (Permutation_trans (rmall_perm L S (L ++ R) H)).
    rewrite (rmall_drop L L R (Permutation_refl L)). apply Permutation_refl.
Qed.

Section Run2.

Variable sm : list Z -> Z * Z.

Definition pacc (y : list Z) (ok : list bool) : list Z :=
  match fst (jr_run sm y ok) with Some _ => rd_blocks (rtr sm ok y) | None => [] end.

Lemma parse_ok : forall y ok s,
  okf s (parse_evs sm y ok) /\ hlive_from s (parse_evs sm y ok) = pacc y ok ++ s.
Proof.
  intros y ok s. unfold parse_evs, pacc, rtr.
  pose proof (rd_closed sm y ok s) as Hc.
  pose proof (okf_mono _ [] s (subm_nil s) (rd_okf sm y ok)) as Hk.
  destruct (fst (jr_run sm y ok)) as [t|].
  - rewrite app_nil_r. split; [exact Hk | exact Hc].
  - split.
    + apply okf_app. split; [exact Hk|]. rewrite Hc.
      cbn [okf hits]. split; [|exact I]. exists s.
      apply Permutation_app_tail. apply Permutation_sym. exact (pj_frees_blocks sm ok y).
    + rewrite hlive_from_app, Hc, hlive_from_cons, hlive_from_nil. cbn [hstep].
      rewrite (rmall_drop (pj_frees sm ok y) (rd_blocks (snd (jr_run sm y ok))) s
                 (Permutation_sym (pj_frees_blocks sm ok y))).
      reflexivity.
Qed.

Lemma parse_wf : forall t p, pj_wf sm t -> parse_evs sm (wdoc t p) [] = rd_hevs (ttrace t).
Proof.
  intros t p Hw. unfold parse_evs, rtr.
  pose proof (G9 sm t Hw p) as E. unfold json_read in E. rewrite E.
  rewrite (G9_trace sm t Hw p). apply app_nil_r.
Qed.

Lemma rt_tr_wf : forall t p, pj_wf sm t -> rt_tr sm t p = ttrace t.
Proof. intros t p Hw. unfold rt_tr, rtr. exact (G9_trace sm t Hw p). Qed.

Lemma rt_text_ok : forall t p s, pj_wf sm t ->
  okf s (rt_text sm t p) /\ Permutation (hlive_from s (rt_text sm t p)) (tblk t ++ s).
Proof.
  intros t p s Hw.
  unfold rt_text. rewrite (parse_wf t p Hw).
  destruct (w_evs_ok t p s) as [W1 W2].
  set (W := last (wcaps t p) 0 + HEAD) in *.
  destruct (r_evs_ok t p (W :: s)) as [R1 R2].
  replace (last (rcaps t p) 0 + 0) with (last (rcaps t p) 0) in R2 by lia.
  set (R := last (rcaps t p) 0) in *.
  destruct (tt_ok t (R :: W :: s)) as [T1 T2].
  set (S3 := hlive_from (R :: W :: s) (rd_hevs (ttrace t))) in *.
  assert (HinR : In R S3).
  { apply (Permutation_in R (Permutation_sym T2)). apply in_or_app. right. left. reflexivity. }
  assert (HS4 : Permutation (rm1 R S3) (tblk t ++ W :: s)).
  { apply (Permutation_trans (rm1_perm R _ _ T2)). apply rm1_mid. }
  assert (HinW : In W (rm1 R S3)).
  { apply (Permutation_in W (Permutation_sym HS4)). apply in_or_app. right. left. reflexivity. }
  assert (HS5 : Permutation (rm1 W (rm1 R S3)) (tblk t ++ s)).
  { apply (Permutation_trans (rm1_perm W _ _ HS4)). apply rm1_mid. }
  unfold r_free, w_free. fold R. fold W.
  split.
  - apply okf_app. split; [exact W1|]. rewrite W2.
    apply okf_app. split; [exact R1|]. rewrite R2.
    apply okf_app. split; [exact T1|]. fold S3.
    cbn [app okf hits hstep]. split; [exact HinR|]. split; [exact HinW | exact I].
  - rewrite !hlive_from_app, W2, R2. fold S3.
    cbn [hlive_from fold_left hstep]. exact HS5.
Qed.

End Run2.

(* ---------------------------------------------------------------- the rewrite (C:606-649) *)

Lemma list_max_cons' : forall a l, list_max (a :: l) = Nat.max a (list_max l).
Proof. reflexivity. Qed.

Lemma depth_set : forall ms k v,
  (depth (JObj (pj_set_model ms k v)) <= Nat.max (depth (JObj ms)) (S (depth v)))%nat.
Proof.
  induction ms as [|[k' u] r IH]; intros k v.
  - cbn [pj_set_model depth map]. rewrite list_max_cons'. change (list_max []) with 0%nat. lia.
  - cbn [pj_set_model]. destruct (list_eq_dec Z.eq_dec k' k) as [Heq | Hne].
    + clear Heq. cbn [depth map]. rewrite !list_max_cons'.
      repeat match goal with |- context [list_max ?l] =>
        let X := fresh "X" in set (X := list_max l) in * end.
      lia.
    + clear Hne. specialize (IH k v). cbn [depth map] in IH |- *. rewrite !list_max_cons'.
      repeat match goal with |- context [list_max ?l] =>
        let X := fresh "X" in set (X := list_max l) in * end.
      lia.
Qed.

Lemma wf_copy : forall sm ms, pj_wf sm (JObj ms) -> pj_wf sm (copy_set ms).
Proof.
  intros sm ms Hw. unfold copy_set. apply wf_set.
  - exact Hw.
  - apply wf_string. unfold MOD_VAL. repeat constructor; lia.
  - unfold MOD_KEY. repeat constructor; lia.
  - pose proof (depth_set ms MOD_KEY (JStr MOD_VAL)) as H.
    pose proof (proj2 (wf_good sm (JObj ms) Hw)) as Hd.
    replace (depth (JStr MOD_VAL)) with 0%nat in H by reflexivity.
    unfold MAXD in *. lia.
Qed.

Lemma mfind_in : forall ms u, mfind ms = Some u -> exists k, In (k, u) ms.
Proof.
  induction ms as [|[k u'] r IH]; intros u H; [discriminate|].
  cbn [mfind] in H. destruct (zl_eqb k MOD_KEY).
  - injection H as <-. exists k. left. reflexivity.
  - destruct (IH u H) as [k' Hk]. exists k'. right. exact Hk.
Qed.

Lemma zl_eqb_true : forall a b, zl_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [zl_eqb] in H; try discriminate.
  - reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.

Lemma zl_eqb_refl : forall a, zl_eqb a a = true.
Proof. induction a as [|x a IH]; [reflexivity|]. cbn [zl_eqb]. rewrite Z.eqb_refl, IH. reflexivity. Qed.

(* pj_get finds the first member named modifiedAt; pj_set replaces that member's value *)
Lemma mfind_split : forall ms u v, mfind ms = Some u ->
  exists A B, ms = A ++ (MOD_KEY, u) :: B /\ pj_set_model ms MOD_KEY v = A ++ (MOD_KEY, v) :: B.
Proof.
  induction ms as [|[k w] r IH]; intros u v H; [discriminate|].
  cbn [mfind] in H. destruct (zl_eqb k MOD_KEY) eqn:E.
  - injection H as ->. apply zl_eqb_true in E. subst k. exists [], r. split; [reflexivity|].
    cbn [pj_set_model]. destruct (list_eq_dec Z.eq_dec MOD_KEY MOD_KEY) as [_|N]; [reflexivity|].
    contradiction N. reflexivity.
  - destruct (IH u v H) as (A & B & -> & Hs). exists ((k, w) :: A), B. split; [reflexivity|].
    cbn [pj_set_model]. destruct (list_eq_dec Z.eq_dec k MOD_KEY) as [Ek|_].
    + subst k. rewrite zl_eqb_refl in E. discriminate.
    + rewrite Hs. reflexivity.
Qed.

(* no member named modifiedAt: pj_set appends it *)
Lemma mfind_none : forall ms v, mfind ms = None -> pj_set_model ms MOD_KEY v = ms ++ [(MOD_KEY, v)].
Proof.
  induction ms as [|[k w] r IH]; intros v H; [reflexivity|].
  cbn [mfind] in H. destruct (zl_eqb k MOD_KEY) eqn:E; [discriminate|].
  cbn [pj_set_model]. destruct (list_eq_dec Z.eq_dec k MOD_KEY) as [Ek|_].
  - subst k. rewrite zl_eqb_refl in E. discriminate.
  - rewrite (IH v H). reflexivity.
Qed.

Lemma tblk_split : forall A k u B,
  Permutation (tblk (JObj (A ++ (k, u) :: B)))
              (tblk u ++ arrz true (capf 0 0 (length A + S (length B))) ++
               concat (map (fun m => kblk (fst m) :: tblk (snd m)) A) ++
               kblk k :: concat (map (fun m => kblk (fst m) :: tblk (snd m)) B)).
Proof.
  intros A k u B. cbn [tblk]. rewrite length_app, map_app, concat_app. cbn [length map concat fst snd app].
  set (X := arrz true (capf 0 0 (length A + S (length B)))).
  set (CA := concat (map (fun m => kblk (fst m) :: tblk (snd m)) A)).
  set (CB := concat (map (fun m => kblk (fst m) :: tblk (snd m)) B)).
  replace (X ++ CA ++ kblk k :: tblk u ++ CB) with ((X ++ CA ++ [kblk k]) ++ tblk u ++ CB)
    by (rewrite <- !app_assoc; reflexivity).
  apply (Permutation_trans (Permutation_app_swap_app _ _ _)).
  rewrite <- !app_assoc. apply Permutation_refl.
Qed.

Lemma swap_bulk : forall (F U R : list Z) (v : Z) T T', Permutation F U -> Permutation T (U ++ R) ->
  Permutation T' (v :: R) -> Permutation (rmall F (v :: T)) T'.
Proof.
  intros F U R v T T' HF HT HT'.
  assert (P : Permutation (v :: T) (F ++ v :: R)).
  { apply (Permutation_trans (perm_skip v HT)).
    apply (Permutation_trans (Permutation_middle U R v)).
    apply Permutation_app_tail. apply Permutation_sym. exact HF. }
  apply (Permutation_trans (rmall_perm F _ _ P)).
  rewrite (rmall_drop F F (v :: R) (Permutation_refl _)). apply Permutation_sym. exact HT'.
Qed.

(* pj_string and pj_set on the copy's blocks leave the blocks of copy_set ms *)
Lemma set_tblk : forall ms, Permutation (hlive_from (tblk (JObj ms)) (set_evs ms)) (tblk (copy_set ms)).
Proof.
  intros ms. unfold set_evs, copy_set.
  set (vb := Z.of_nat (S (length MOD_VAL)) + HEAD).
  assert (Hvb : tblk (JStr MOD_VAL) = [vb]) by (unfold vb; vm_compute; reflexivity).
  destruct (mfind ms) as [u|] eqn:Em.
  - destruct (mfind_split ms u (JStr MOD_VAL) Em) as (A & B & Ems & Eset). rewrite Eset.
    pose proof (tblk_split A MOD_KEY (JStr MOD_VAL) B) as H2. rewrite Hvb in H2.
    pose proof (tblk_split A MOD_KEY u B) as H1. rewrite <- Ems in H1.
    cbn [hlive_from fold_left hstep].
    exact (swap_bulk (fo u) (tblk u) _ vb _ _ (fo_tblk u) H1 H2).
  - rewrite (mfind_none ms (JStr MOD_VAL) Em).
    set (D := concat (map (fun m => kblk (fst m) :: tblk (snd m)) ms)).
    assert (HT : tblk (JObj ms) = arrz true (ncap (length ms)) ++ D) by (cbn [tblk]; rewrite ncap_eq; reflexivity).
    assert (HT2 : tblk (JObj (ms ++ [(MOD_KEY, JStr MOD_VAL)])) =
                  arrz true (gcap (length ms) (ncap (length ms))) ++ D ++ [kblk MOD_KEY; vb]).
    { cbn [tblk]. rewrite length_app, map_app, concat_app. cbn [length map concat fst snd app].
      rewrite Hvb, Nat.add_1_r, ncap_capf. cbn [Nat.add app]. rewrite <- ncap_eq. reflexivity. }
    assert (Hk : kblk MOD_KEY = Z.of_nat (S (length MOD_KEY)) + HEAD) by (vm_compute; reflexivity).
    rewrite hlive_from_cons, rd_hevs_app, hlive_from_app, HT, HT2, Hk. cbn [hstep].
    destruct (grow_ev_ok true (length ms) (ncap (length ms)) (vb :: D)) as [_ G2].
    apply (Permutation_trans (hlive_from_perm _ _ _
             (Permutation_trans (hlive_from_perm _ _ _ (Permutation_middle _ _ _)) G2))).
    cbn [rd_hevs flat_map rd_hev app hlive_from fold_left hstep].
    apply (Permutation_trans (Permutation_middle _ _ _)). apply Permutation_app_head.
    exact (Permutation_app_comm [Z.of_nat (S (length MOD_KEY)) + HEAD; vb] D).
Qed.

Lemma set_evs_ok : forall ms L, Permutation L (tblk (JObj ms)) -> okf L (set_evs ms).
Proof.
  intros ms L HL. unfold set_evs. cbn [okf hits hstep]. split; [exact I|].
  set (vb := Z.of_nat (S (length MOD_VAL)) + HEAD).
  destruct (mfind ms) as [u|] eqn:Em.
  - cbn [okf hits]. split; [|exact I].
    destruct (mfind_in ms u Em) as [k Hk].
    apply (subm_trans _ (tblk u)); [apply subm_perm; apply Permutation_sym; apply fo_tblk|].
    apply (subm_trans _ (tblk (JObj ms))); [exact (tblk_member ms k u Hk)|].
    apply (subm_trans _ L); [apply subm_perm; exact HL|].
    exists [vb]. apply Permutation_cons_append.
  - rewrite rd_hevs_app. apply okf_app. split.
    + destruct (tblk_array ms) as [D HD].
      destruct (grow_ev_ok true (length ms) (ncap (length ms)) (vb :: D)) as [G1 _].
      apply (okf_perm _ (arrz true (ncap (length ms)) ++ vb :: D)); [|exact G1].
      apply Permutation_sym.
      apply (Permutation_trans (perm_skip vb (Permutation_trans HL HD))).
      apply Permutation_middle.
    + cbn [rd_hevs flat_map rd_hev app okf hits]. split; exact I.
Qed.

Section Run3.

Variable sm : list Z -> Z * Z.

Lemma rw_ok : forall ms Lc, pj_wf sm (JObj ms) -> Permutation Lc (tblk (JObj ms)) ->
  okf Lc (rw_evs sm ms) /\ Permutation (hlive_from Lc (rw_evs sm ms)) (hlive_from Lc (set_evs ms)).
Proof.
  intros ms Lc Hw HL.
  pose proof (wf_copy sm ms Hw) as Hc.
  set (c := copy_set ms) in *.
  unfold rw_evs. fold c.
  rewrite (parse_wf sm c true Hc).
  pose proof (set_evs_ok ms Lc HL) as S1.
  set (C := hlive_from Lc (set_evs ms)).
  destruct (w_evs_ok c true C) as [W1 W2].
  set (W := last (wcaps c true) 0 + HEAD) in *.
  destruct (tt_ok c (W :: C)) as [T1 T2].
  set (S3 := hlive_from (W :: C) (rd_hevs (ttrace c))) in *.
  assert (HinW : In W S3).
  { apply (Permutation_in W (Permutation_sym T2)). apply in_or_app. right. left. reflexivity. }
  assert (HS4 : Permutation (rm1 W S3) (fo c ++ C)).
  { apply (Permutation_trans (rm1_perm W _ _ T2)).
    apply (Permutation_trans (rm1_mid W (tblk c) C)).
    apply Permutation_app_tail. apply Permutation_sym. apply fo_tblk. }
  destruct (bulk_ok (fo c) (rm1 W S3) C HS4) as [B1 B2].
  unfold w_free. fold W.
  split.
  - apply okf_app. split; [exact S1|]. fold C.
    apply okf_app. split; [exact W1|]. rewrite W2.
    apply okf_app. split; [exact T1|]. fold S3.
    cbn [app okf hits hstep]. split; [exact HinW|]. split; [exact B1 | exact I].
  - rewrite !hlive_from_app. fold C. rewrite W2. fold S3.
    cbn [hlive_from fold_left]. cbn [hstep] in B2 |- *. exact B2.
Qed.

Lemma round_trip_ok : forall t, pj_wf sm t ->
  okf [] (round_trip sm t) /\ Permutation (hlive (round_trip sm t)) [].
Proof.
  intros t Hw. unfold round_trip, hlive.
  destruct (rt_text_ok sm t false [] Hw) as [A1 A2]. rewrite app_nil_r in A2.
  set (S1 := hlive_from [] (rt_text sm t false)) in *.
  destruct (rt_text_ok sm t true S1 Hw) as [B1 B2].
  set (S2 := hlive_from S1 (rt_text sm t true)) in *.
  assert (HS2 : Permutation S2 (fo t ++ S1)).
  { apply (Permutation_trans B2). apply Permutation_app_tail. apply Permutation_sym. apply fo_tblk. }
  destruct (bulk_ok (fo t) S2 S1 HS2) as [C1 C2].
  set (S3 := hstep S2 (HBulk (fo t))) in *.
  assert (HS3 : Permutation S3 (tblk t)) by (apply (Permutation_trans C2); exact A2).
  assert (Hpre : okf [] (rt_text sm t false ++ rt_text sm t true ++ [HBulk (fo t)]) /\
                 hlive_from [] (rt_text sm t false ++ rt_text sm t true ++ [HBulk (fo t)]) = S3).
  { split.
    - apply okf_app. split; [exact A1|]. fold S1.
      apply okf_app. split; [exact B1|]. fold S2.
      cbn [okf]. split; [exact C1 | exact I].
    - rewrite !hlive_from_app. fold S1. fold S2. reflexivity. }
  destruct Hpre as [P1 P2].
  rewrite !app_assoc. rewrite <- (app_assoc (rt_text sm t false)).
  destruct t as [| | | txt bits | z | items | ms].
  1-6: (split;
        [ apply okf_app; split; [exact P1|]; rewrite P2;
          cbn [okf]; split; [|exact I];
          refine (proj1 (bulk_ok (fo _) S3 [] _));
          rewrite app_nil_r; apply (Permutation_trans HS3); apply Permutation_sym; apply fo_tblk
        | rewrite hlive_from_app, P2; cbn [hlive_from fold_left];
          refine (proj2 (bulk_ok (fo _) S3 [] _));
          rewrite app_nil_r; apply (Permutation_trans HS3); apply Permutation_sym; apply fo_tblk ]).
  destruct (rw_ok ms S3 Hw HS3) as [R1 R2].
  set (S4 := hlive_from S3 (rw_evs sm ms)) in *.
  assert (HS4 : Permutation S4 (fo (copy_set ms) ++ [])).
  { rewrite app_nil_r. apply (Permutation_trans R2).
    apply (Permutation_trans (hlive_from_perm _ _ _ HS3)).
    apply (Permutation_trans (set_tblk ms)). apply Permutation_sym. apply fo_tblk. }
  destruct (bulk_ok _ S4 [] HS4) as [D1 D2].
  split.
  - apply okf_app. split; [exact P1|]. rewrite P2.
    apply okf_app. split; [exact R1|]. fold S4. cbn [okf]. split; [exact D1 | exact I].
  - rewrite hlive_from_app, P2, hlive_from_app. fold S4. cbn [hlive_from fold_left]. exact D2.
Qed.

End Run3.

(* ---------------------------------------------------------------- the starved writes (C:545-568) *)

Lemma w_pair_ok : forall t p s, okf s (w_evs t p ++ w_free t p) /\ hlive_from s (w_evs t p ++ w_free t p) = s.
Proof.
  intros t p s. destruct (w_evs_ok t p s) as [W1 W2]. unfold w_free. split.
  - apply okf_app. split; [exact W1|]. rewrite W2. cbn [okf hits]. split; [left; reflexivity | exact I].
  - rewrite hlive_from_app, W2, hlive_from_cons, hlive_from_nil. cbn [hstep]. apply rm1_cons_eq.
Qed.

Lemma w_starved_live : forall t p k s, hlive_from s (w_starved t p k) = s.
Proof.
  intros t p k s. unfold w_starved. rewrite hlive_from_app.
  destruct k as [|k]; [rewrite firstn_O; reflexivity|].
  destruct (chain_okf (firstn (S k) (wcaps t p)) HEAD s (firstn_forall _ _ _ (S k) (wcaps_pos t p))) as [_ H2].
  assert (Hne : firstn (S k) (wcaps t p) <> []).
  { destruct (wcaps_cons t p) as (c & r & E). rewrite E. cbn [firstn]. discriminate. }
  rewrite (H2 Hne), hlive_from_cons, hlive_from_nil. cbn [hstep]. apply rm1_cons_eq.
Qed.

Lemma starved_write_ok : forall x t p rest s, okf s rest -> hlive_from s rest = s ->
  okf s (starved_write x t p rest) /\ hlive_from s (starved_write x t p rest) = s.
Proof.
  intros x t p rest s Hk Hl. unfold starved_write.
  destruct (w_pair_ok t p s) as [P1 P2].
  rewrite app_assoc. split.
  - apply okf_app. split; [exact P1|]. rewrite P2.
    destruct (wcalls t p) as [|n]; [exact I|].
    apply okf_app. split; [apply w_starved_ok|]. rewrite w_starved_live. exact Hk.
  - rewrite hlive_from_app, P2. destruct (wcalls t p) as [|n]; [reflexivity|].
    rewrite hlive_from_app, w_starved_live. exact Hl.
Qed.

Lemma starved_writes_ok : forall x t s, okf s (starved_writes x t) /\ hlive_from s (starved_writes x t) = s.
Proof.
  intros x t s. unfold starved_writes.
  destruct (starved_write_ok x t false [] s I eq_refl) as [A1 A2].
  exact (starved_write_ok x t true _ s A1 A2).
Qed.

(* ================================================================ NO MISS *)

Theorem no_miss_okf : forall sm x, okf [] (hrun sm x).
Proof.
  intros sm x. unfold hrun. cbv zeta.
  destruct (MAXB <? Z.of_nat (length x)); [exact I|].
  set (CP := Z.of_nat (length x) + FUZZ_PAD).
  set (SC := Z.of_nat (length x) + 1).
  set (Lr := pj_frees sm [] x).
  set (A := pacc sm x []).
  assert (HP : forall s, okf s (parse_evs sm x []) /\ hlive_from s (parse_evs sm x []) = A ++ s)
    by (intros s; exact (parse_ok sm x [] s)).
  set (TF := match fst (jr_run sm x []) with Some _ => [HBulk Lr] | None => [] end).
  assert (HTF : forall s, okf (A ++ s) TF /\ hlive_from (A ++ s) TF = s).
  { intros s. unfold TF, A, pacc, Lr. destruct (fst (jr_run sm x [])) as [t|].
    - cbn [okf hits]. split.
      + split; [|exact I]. exists s.
        apply Permutation_app_tail. apply Permutation_sym. exact (pj_frees_blocks sm [] x).
      + rewrite hlive_from_cons, hlive_from_nil. cbn [hstep].
        apply rmall_drop. apply Permutation_sym. exact (pj_frees_blocks sm [] x).
    - split; [exact I | reflexivity]. }
  set (C := [CP; CP; CP]).
  assert (HC : hlive_from [] [HMal CP; HMal CP; HMal CP] = C) by reflexivity.
  assert (HF : okf C [HFr CP; HFr CP; HFr CP] /\ hlive_from C [HFr CP; HFr CP; HFr CP] = []).
  { unfold C. cbn [okf hits hstep hlive_from fold_left]. rewrite !rm1_cons_eq. split.
    - split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity | exact I].
    - reflexivity. }
  assert (HS : forall s, okf s [HMal SC; HFr SC] /\ hlive_from s [HMal SC; HFr SC] = s).
  { intros s. cbn [okf hits hstep hlive_from fold_left]. rewrite rm1_cons_eq.
    split; [split; [exact I|]; split; [left; reflexivity | exact I] | reflexivity]. }
  (* the prefix up to the branch point leaves A *)
  set (PRE := [HMal CP; HMal CP; HMal CP] ++ parse_evs sm x [] ++ parse_evs sm x [] ++ parse_evs sm x [] ++
              TF ++ TF ++ TF ++ [HFr CP; HFr CP; HFr CP] ++ parse_evs sm x [] ++ [HMal SC; HFr SC]).
  assert (HPRE : okf [] PRE /\ hlive_from [] PRE = A).
  { unfold PRE. split.
    - apply okf_app. split; [cbn [okf hits]; repeat split|]. rewrite HC.
      apply okf_app. split; [apply HP|]. rewrite (proj2 (HP C)).
      apply okf_app. split; [apply HP|]. rewrite (proj2 (HP (A ++ C))).
      apply okf_app. split; [apply HP|]. rewrite (proj2 (HP (A ++ A ++ C))).
      apply okf_app. split; [apply HTF|]. rewrite (proj2 (HTF (A ++ A ++ C))).
      apply okf_app. split; [apply HTF|]. rewrite (proj2 (HTF (A ++ C))).
      apply okf_app. split; [apply HTF|]. rewrite (proj2 (HTF C)).
      apply okf_app. split; [apply HF|]. rewrite (proj2 HF).
      apply okf_app. split; [apply HP|]. rewrite (proj2 (HP [])), app_nil_r.
      apply HS.
    - rewrite !hlive_from_app, HC, (proj2 (HP C)), (proj2 (HP (A ++ C))), (proj2 (HP (A ++ A ++ C))).
      rewrite (proj2 (HTF (A ++ A ++ C))), (proj2 (HTF (A ++ C))), (proj2 (HTF C)), (proj2 HF).
      rewrite (proj2 (HP [])), app_nil_r. apply HS. }
  destruct HPRE as [HP1 HP2].
  match goal with |- okf [] (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5 ++ ?l6 ++ ?l7 ++ ?l8 ++ ?l9 ++ ?l10 ++ ?TL) =>
    replace (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9 ++ l10 ++ TL) with (PRE ++ TL)
      by (unfold PRE; rewrite <- !app_assoc; reflexivity) end.
  apply okf_app. split; [exact HP1|]. rewrite HP2.
  unfold A, pacc. destruct (fst (jr_run sm x [])) as [t|] eqn:Ej.
  - (* accepted: check_round_trip, the starved parse and writes, pj_free (&doc) *)
    set (Ar := rd_blocks (rtr sm [] x)).
    assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); unfold json_read; exact Ej).
    destruct (round_trip_ok sm t Hw) as [R1 R2].
    destruct (seg_step [] (round_trip sm t) Ar Ar R1 (Permutation_refl _)) as [R3 R4].
    fold (hlive (round_trip sm t)) in R4.
    assert (HR : Permutation (hlive_from Ar (round_trip sm t)) Ar).
    { apply (Permutation_trans R4). apply (Permutation_trans (Permutation_app_tail Ar R2)). apply Permutation_refl. }
    apply okf_app. split; [exact R3|].
    set (S1 := hlive_from Ar (round_trip sm t)) in *.
    assert (HRL : Permutation S1 Lr).
    { apply (Permutation_trans HR). apply Permutation_sym. exact (pj_frees_blocks sm [] x). }
    unfold starved_parse.
    destruct (calls (rtr sm [] x)) as [|took].
    + rewrite app_nil_l. destruct (starved_writes_ok x t S1) as [W1 W2].
      apply okf_app. split; [exact W1|]. fold S1. rewrite W2.
      cbn [okf hits]. split; [|exact I]. exists []. rewrite app_nil_r. exact HRL.
    + destruct (parse_ok sm x (okk (pick x (S took))) S1) as [Q1 Q2].
      apply okf_app. split; [exact Q1|]. fold S1. rewrite Q2.
      destruct (starved_writes_ok x t (pacc sm x (okk (pick x (S took))) ++ S1)) as [W1 W2].
      apply okf_app. split; [exact W1|]. rewrite W2.
      cbn [okf hits]. split; [|exact I].
      exists (pacc sm x (okk (pick x (S took)))).
      apply (Permutation_trans (Permutation_app_comm _ _)). apply Permutation_app_tail. exact HRL.
  - (* refused: the starved parse only *)
    unfold starved_parse. destruct (calls (rtr sm [] x)) as [|took]; [exact I|].
    exact (proj1 (parse_ok sm x (okk (pick x (S took))) [])).
Qed.

(* THE S1 FACT S2 READS: every HRe / HFr / HBulk of the harness run removes requests that are live there. *)
Theorem no_miss : forall sm x, hits_from [] (hrun sm x).
Proof. intros sm x. apply hits_from_okf. apply no_miss_okf. Qed.

(* and in S2's frame form: the heap below the slot (H0) comes out of any prefix unchanged *)
Theorem hlive_from_app_hits : forall es A s, hits_from s es ->
  Permutation (hlive_from (A ++ s) es) (A ++ hlive_from s es).
Proof. intros es A s H. apply hlive_frame. apply okf_hits_from. exact H. Qed.
