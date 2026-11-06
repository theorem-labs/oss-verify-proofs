(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Ceiling ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim APrimLem LJ APrimSpec APrimSpec2 APrimQ ASec AQuar F_poison F_flush F_sec_C F_quar_E AQuarM ALinkPg ALinkVm ALink ALinkPrim.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma flush_tree_eq : forall p n, flush_tree p n = flush_treeL p n.
Proof.
  intros p n. unfold flush_tree, flush_treeL, flush_range, inner_range.
  change (pgup (sh p)) with (pgupZ (shZ p)). change (pgdn (sh (p + n))) with (pgdnZ (shZ (p + n))).
  destruct (pgdnZ (shZ (p + n)) <=? pgupZ (shZ p)); reflexivity.
Qed.
Lemma sec_dealloc_tree_eq : forall sc, sec_dealloc_tree sc = ebind (flush_treeL (sc_beg sc) (sc_msize sc)) (fun _ => t_unmap (sc_beg sc) (sc_msize sc)).
Proof. intros sc. unfold sec_dealloc_tree. rewrite flush_tree_eq. reflexivity. Qed.

Fixpoint rem1 (c : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with [] => [] | x :: r => if (fst x =? fst c) && (snd x =? snd c) then r else x :: rem1 c r end.
Lemma rem1_perm : forall c l, In c l -> Permutation l (c :: rem1 c l).
Proof.
  intros c l. induction l as [|x r IH]; intros H; [destruct H|]. cbn [rem1].
  destruct ((fst x =? fst c) && (snd x =? snd c)) eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2. destruct x as [x1 x2], c as [c1 c2]. cbn in E1, E2. subst. apply Permutation_refl.
  - destruct H as [->|H]; [rewrite !Z.eqb_refl in E; discriminate|].
    eapply Permutation_trans; [apply perm_skip; exact (IH H)| apply perm_swap].
Qed.

Section F.
Context {HC : HasCeiling}.
Variable Bs : vmbase.
Variable AL : alayout.
Hypothesis BO : base_ok Bs.
Hypothesis SPACE_EQ : vb_space Bs = al_space AL.
Hypothesis SPACE_AL : al_space AL mod 65536 = 0.

Notation kept mo mo' := (m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).
#[using="Type"] Lemma kept_trans : forall mo mo1 mo2 : Model, kept mo mo1 -> kept mo1 mo2 -> kept mo mo2.
Proof. intros mo mo1 mo2 [A B] [C D]. split; congruence. Qed.

Definition va_cd (v : vabs) (c : Z) (k : pclass) : vabs := mkVA (va_prim v + D_cdealloc c k) (va_chunks v) (va_nsec v) (va_aux v).
Definition ok_cd (v : vabs) (c : Z) (k : pclass) : Prop :=
  1 <= c <= 31 /\ pclass_wf c k /\ drain_budget c k /\ vroom Bs v (D_cdealloc c k + D_cdealloc c k / 8 + 2 * page_size).

Definition va_recycle1 (v : vabs) (X : pstate) (ch : qchunk) : vabs :=
  match qc_kind ch with
  | QPrim c _ => va_cd v c (get_cls (fst X) c)
  | QSec sc => mkVA (va_prim v) (rem1 (sc_beg sc, sc_msize sc) (va_chunks v)) (va_nsec v) (va_aux v)
  end.
Definition ok_recycle1 (v : vabs) (X : pstate) (ch : qchunk) : Prop :=
  match qc_kind ch with
  | QPrim c _ => ok_cd v c (get_cls (fst X) c)
  | QSec sc => In (sc_beg sc, sc_msize sc) (va_chunks v)
  end.

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_recycle1 : forall v mo X ch (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> ok_recycle1 v X ch ->
  (forall mo', LINK Bs (va_recycle1 v X ch) mo' -> kept mo mo' -> Q (Ok tt) mo') ->
  stwfL (t_recycle1 AL X ch) mo Q.
Proof.
  intros v mo X ch Q L OK K. unfold t_recycle1, ok_recycle1, va_recycle1 in *. destruct (qc_kind ch) as [c u|sc].
  - destruct OK as (C & W & D & V). exact (link_cdealloc Bs AL BO SPACE_EQ SPACE_AL v mo c _ Q L C W D V K).
  - rewrite sec_dealloc_tree_eq. exact (link_dealloc Bs v mo _ _ _ Q BO L (rem1_perm _ _ OK) K).
Qed.

Fixpoint va_recycle_chunks (v : vabs) (X : pstate) (chs : list qchunk) : vabs :=
  match chs with [] => v | ch :: r => va_recycle_chunks (va_recycle1 v X ch) (recycle1 X ch) r end.
Fixpoint ok_recycle_chunks (v : vabs) (X : pstate) (chs : list qchunk) : Prop :=
  match chs with [] => True | ch :: r => ok_recycle1 v X ch /\ ok_recycle_chunks (va_recycle1 v X ch) (recycle1 X ch) r end.

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_recycle_chunks : forall chs v mo X (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> ok_recycle_chunks v X chs ->
  (forall mo', LINK Bs (va_recycle_chunks v X chs) mo' -> kept mo mo' -> Q (Ok tt) mo') ->
  stwfL (t_recycle_chunks AL X chs) mo Q.
Proof.
  induction chs as [|ch r IH]; intros v mo X Q L OK K; cbn [t_recycle_chunks va_recycle_chunks ok_recycle_chunks] in *.
  - apply stwf_ret. apply K; [exact L| split; reflexivity].
  - destruct OK as [O1 OR]. apply stwf_ebind. apply (link_recycle1 v mo X ch); [exact L| exact O1|].
    intros mo1 L1 K1. apply (IH _ mo1 _ Q L1 OR). intros mo2 L2 K2. apply K; [exact L2| exact (kept_trans _ _ _ K1 K2)].
Qed.

Definition va_recycle_batch (v : vabs) (X : pstate) (b : qbatch) : vabs :=
  va_cd (va_recycle_chunks v X (qb_chunks b)) K_BCLASS (get_cls (fst (recycle_chunks X (qb_chunks b))) K_BCLASS).
Definition ok_recycle_batch (v : vabs) (X : pstate) (b : qbatch) : Prop :=
  ok_recycle_chunks v X (qb_chunks b)
  /\ ok_cd (va_recycle_chunks v X (qb_chunks b)) K_BCLASS (get_cls (fst (recycle_chunks X (qb_chunks b))) K_BCLASS).

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_recycle_batch : forall v mo X b (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> ok_recycle_batch v X b ->
  (forall mo', LINK Bs (va_recycle_batch v X b) mo' -> kept mo mo' -> Q (Ok tt) mo') ->
  stwfL (t_recycle_batch AL X b) mo Q.
Proof.
  intros v mo X b Q L [O1 (C & W & D & V)] K. unfold t_recycle_batch. apply stwf_ebind.
  apply (link_recycle_chunks _ v mo X); [exact L| exact O1|]. intros mo1 L1 K1.
  apply (link_cdealloc Bs AL BO SPACE_EQ SPACE_AL _ mo1 K_BCLASS _ Q L1 C W D V).
  intros mo2 L2 K2. apply K; [exact L2| exact (kept_trans _ _ _ K1 K2)].
Qed.

Fixpoint va_dorecycle (v : vabs) (X : pstate) (bs : list qbatch) : vabs :=
  match bs with [] => v | b :: r => va_dorecycle (va_recycle_batch v X b) (recycle_batch X b) r end.
Fixpoint ok_dorecycle (v : vabs) (X : pstate) (bs : list qbatch) : Prop :=
  match bs with [] => True | b :: r => ok_recycle_batch v X b /\ ok_dorecycle (va_recycle_batch v X b) (recycle_batch X b) r end.

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_dorecycle : forall bs v mo X (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> ok_dorecycle v X bs ->
  (forall mo', LINK Bs (va_dorecycle v X bs) mo' -> kept mo mo' -> Q (Ok tt) mo') ->
  stwfL (t_dorecycle AL X bs) mo Q.
Proof.
  induction bs as [|b r IH]; intros v mo X Q L OK K; cbn [t_dorecycle va_dorecycle ok_dorecycle] in *.
  - apply stwf_ret. apply K; [exact L| split; reflexivity].
  - destruct OK as [O1 OR]. apply stwf_ebind. apply (link_recycle_batch v mo X b); [exact L| exact O1|].
    intros mo1 L1 K1. apply (IH _ mo1 _ Q L1 OR). intros mo2 L2 K2. apply K; [exact L2| exact (kept_trans _ _ _ K1 K2)].
Qed.

Definition D_enq (P : prim) (l : list qbatch) : Z :=
  if enq_refills P l then D_gfa (get_cls P K_BCLASS) K_BCLASS (max_count K_BCLASS / 2) else 0.
Definition va_enq (v : vabs) (P : prim) (l : list qbatch) : vabs := mkVA (va_prim v + D_enq P l) (va_chunks v) (va_nsec v) (va_aux v).
Definition ok_enq (v : vabs) (P : prim) (l : list qbatch) : Prop :=
  enq_refills P l = true ->
  pclass_wf K_BCLASS (get_cls P K_BCLASS) /\ refill_budget K_BCLASS (get_cls P K_BCLASS)
  /\ vroom Bs v (D_enq P l + D_enq P l / 8 + 4 * page_size).

#[using="AL"] Lemma va_enq_noop : forall v P l, enq_refills P l = false -> va_enq v P l = v.
Proof. intros [a b c d] P l E. unfold va_enq, D_enq. rewrite E. cbn. f_equal. lia. Qed.

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_enq : forall v mo P l (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> ok_enq v P l ->
  (forall mo', LINK Bs (va_enq v P l) mo' -> kept mo mo' -> Q (Ok tt) mo') ->
  stwfL (t_enq AL P l) mo Q.
Proof.
  intros v mo P l Q L OK K. unfold t_enq. destruct (enq_refills P l) eqn:E.
  - destruct (OK E) as (W & R & V). unfold D_enq in V. rewrite E in V.
    apply (link_refill Bs AL BO SPACE_EQ SPACE_AL v mo K_BCLASS _ Q L ltac:(lia) W R V).
    intros mo' L' K'. apply K; [| exact K']. unfold va_enq, D_enq. rewrite E. exact L'.
  - apply stwf_ret. apply K; [rewrite (va_enq_noop v P l E); exact L| split; reflexivity].
Qed.

Definition va_put (v : vabs) (X : pstate) (Qq : aquar) (ch : qchunk) : vabs :=
  let v1 := va_enq v (fst X) (q_loc Qq) in
  if put_drains (fst X) Qq ch then va_dorecycle v1 (fst (q_put_enq (fst X) Qq ch), snd X) (snd (q_drain_sel (snd (q_put_enq (fst X) Qq ch)))) else v1.
Definition ok_put (v : vabs) (X : pstate) (Qq : aquar) (ch : qchunk) : Prop :=
  ok_enq v (fst X) (q_loc Qq)
  /\ (put_drains (fst X) Qq ch = true ->
      ok_dorecycle (va_enq v (fst X) (q_loc Qq)) (fst (q_put_enq (fst X) Qq ch), snd X) (snd (q_drain_sel (snd (q_put_enq (fst X) Qq ch))))).

#[using="BO SPACE_EQ SPACE_AL"] Theorem link_put : forall v mo X Qq ch (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> ok_put v X Qq ch ->
  (forall mo', LINK Bs (va_put v X Qq ch) mo' -> kept mo mo' -> Q (Ok tt) mo') ->
  stwfL (t_put AL X Qq ch) mo Q.
Proof.
  intros v mo X Qq ch Q L [OE OD] K. unfold t_put, va_put in *. apply stwf_ebind.
  apply (link_enq v mo (fst X) (q_loc Qq)); [exact L| exact OE|]. intros mo1 L1 K1.
  destruct (put_drains (fst X) Qq ch) eqn:E.
  - unfold t_drain. apply (link_dorecycle _ _ mo1 _ Q L1 (OD eq_refl)). intros mo2 L2 K2. apply K; [exact L2| exact (kept_trans _ _ _ K1 K2)].
  - apply stwf_ret. apply K; [exact L1| exact K1].
Qed.

Definition used (v : vabs) : Z :=
  vb_used Bs + va_prim v + va_prim v / 8 + chunks_weight (va_chunks v) + 8192 * va_nsec v + va_aux v.
#[using="Type"] Lemma vroom_used : forall v e, vroom Bs v e <-> used v + e <= target_alloc_limit.
Proof. intros v e. unfold vroom, used. split; intros H; exact H. Qed.

Definition sok_cd (c : Z) (k : pclass) : Prop := 1 <= c <= 31 /\ pclass_wf c k /\ drain_budget c k.
Definition sok_recycle1 (v : vabs) (X : pstate) (ch : qchunk) : Prop :=
  match qc_kind ch with QPrim c _ => sok_cd c (get_cls (fst X) c) | QSec sc => In (sc_beg sc, sc_msize sc) (va_chunks v) end.
Fixpoint sok_recycle_chunks (v : vabs) (X : pstate) (chs : list qchunk) : Prop :=
  match chs with [] => True | ch :: r => sok_recycle1 v X ch /\ sok_recycle_chunks (va_recycle1 v X ch) (recycle1 X ch) r end.
Definition sok_recycle_batch (v : vabs) (X : pstate) (b : qbatch) : Prop :=
  sok_recycle_chunks v X (qb_chunks b) /\ sok_cd K_BCLASS (get_cls (fst (recycle_chunks X (qb_chunks b))) K_BCLASS).
Fixpoint sok_dorecycle (v : vabs) (X : pstate) (bs : list qbatch) : Prop :=
  match bs with [] => True | b :: r => sok_recycle_batch v X b /\ sok_dorecycle (va_recycle_batch v X b) (recycle_batch X b) r end.

Definition R_cd (c : Z) (k : pclass) : Z := D_cdealloc c k + D_cdealloc c k / 8.
Definition R_recycle1 (X : pstate) (ch : qchunk) : Z := match qc_kind ch with QPrim c _ => R_cd c (get_cls (fst X) c) | QSec _ => 0 end.
Fixpoint R_recycle_chunks (X : pstate) (chs : list qchunk) : Z :=
  match chs with [] => 0 | ch :: r => R_recycle1 X ch + R_recycle_chunks (recycle1 X ch) r end.
Definition R_recycle_batch (X : pstate) (b : qbatch) : Z :=
  R_recycle_chunks X (qb_chunks b) + R_cd K_BCLASS (get_cls (fst (recycle_chunks X (qb_chunks b))) K_BCLASS).
Fixpoint R_dorecycle (X : pstate) (bs : list qbatch) : Z :=
  match bs with [] => 0 | b :: r => R_recycle_batch X b + R_dorecycle (recycle_batch X b) r end.

#[using="AL"] Lemma D_cd_facts : forall c k, sok_cd c k -> 0 <= D_cdealloc c k /\ D_cdealloc c k mod 8 = 0.
Proof.
  intros c k (C & W & DB). unfold D_cdealloc. destruct (p_cnt k =? max_count c); [|split; [lia| reflexivity]].
  unfold pclass_wf in W. cbv zeta in W. destruct W as (W1 & _ & _ & _ & W5 & W6 & _). pose proof (max_count_range c C) as [Hmc _].
  destruct (efa_new_facts AL k (p_nf k + max_count c / 2) W5 W6) as (_ & _ & _ & _ & F5 & F6).
  - rewrite W1. pose proof (Z.div_pos (max_count c) 2 ltac:(lia) ltac:(lia)). lia.
  - exact DB.
  - split; [exact F5|]. clear - F6. Z.div_mod_to_equations. lia.
Qed.

#[using="AL"] Lemma used_cd : forall v c k, sok_cd c k -> va_prim v mod 8 = 0 -> used (va_cd v c k) = used v + R_cd c k.
Proof.
  intros v c k S PA. destruct (D_cd_facts c k S) as [D0 D8]. unfold used, va_cd, R_cd. cbn [va_prim va_chunks va_nsec va_aux].
  assert (E : (va_prim v + D_cdealloc c k) / 8 = va_prim v / 8 + D_cdealloc c k / 8) by (clear - PA D8; Z.div_mod_to_equations; lia).
  rewrite E. lia.
Qed.

#[using="AL"] Lemma chunks_weight_rem1 : forall c l, chunks_sane l -> chunks_weight (rem1 c l) <= chunks_weight l.
Proof.
  intros c l. induction l as [|x r IH]; intros SN; [cbn; lia|]. apply Forall_cons_iff in SN as [Sx Sr].
  assert (WX : 0 <= snd x + hull_bytes (fst x) (snd x)).
  { destruct Sx as (A & B & _). pose proof (hull_bytes_bound (fst x) (snd x) ltac:(lia) ltac:(lia)). lia. }
  cbn [rem1]. destruct ((fst x =? fst c) && (snd x =? snd c)); unfold chunks_weight in *; cbn [fold_right] in *; [lia|].
  specialize (IH Sr). lia.
Qed.
#[using="Type"] Lemma chunks_sane_rem1 : forall c l, chunks_sane l -> chunks_sane (rem1 c l).
Proof.
  intros c l. induction l as [|x r IH]; intros SN; [exact SN|]. apply Forall_cons_iff in SN as [Sx Sr]. cbn [rem1].
  destruct ((fst x =? fst c) && (snd x =? snd c)); [exact Sr| apply Forall_cons; [exact Sx| exact (IH Sr)]].
Qed.

Definition vinv (v : vabs) : Prop := chunks_sane (va_chunks v) /\ va_prim v mod 8 = 0.
#[using="Type"] Lemma vinv_of_LINK : forall v mo, LINK Bs v mo -> vinv v.
Proof. intros v mo L. split; [exact (lk_sane _ _ _ L)|]. destruct (lk_pal _ _ _ L) as [A _]. clear - A. Z.div_mod_to_equations. lia. Qed.

#[using="AL"] Lemma room_recycle1 : forall v X ch, vinv v -> sok_recycle1 v X ch ->
  vinv (va_recycle1 v X ch) /\ used (va_recycle1 v X ch) <= used v + R_recycle1 X ch /\ 0 <= R_recycle1 X ch
  /\ (forall E, 0 <= E -> vroom Bs v (R_recycle1 X ch + 2 * page_size + E) -> ok_recycle1 v X ch).
Proof.
  intros v X ch [SN PA] S. unfold sok_recycle1, va_recycle1, R_recycle1, ok_recycle1 in *. destruct (qc_kind ch) as [c u|sc].
  - destruct (D_cd_facts _ _ S) as [D0 D8]. pose proof (used_cd v c _ S PA) as U.
    assert (R0 : 0 <= R_cd c (get_cls (fst X) c)) by (unfold R_cd; pose proof (Z.div_pos (D_cdealloc c (get_cls (fst X) c)) 8 D0 ltac:(lia)); lia).
    split; [split; [exact SN| unfold va_cd; cbn [va_prim]; clear - PA D8; Z.div_mod_to_equations; lia]|].
    split; [lia|]. split; [exact R0|]. intros E HE V. destruct S as (C & W & DB). split; [exact C|]. split; [exact W|]. split; [exact DB|].
    apply (proj2 (vroom_used _ _)). apply (proj1 (vroom_used _ _)) in V. unfold R_cd in V. unfold page_size in *. lia.
  - split; [split; [exact (chunks_sane_rem1 _ _ SN)| exact PA]|]. split.
    + unfold used. cbn [va_prim va_chunks va_nsec va_aux]. pose proof (chunks_weight_rem1 (sc_beg sc, sc_msize sc) _ SN). lia.
    + split; [lia|]. intros E HE V. exact S.
Qed.

#[using="AL"] Lemma room_recycle_chunks : forall chs v X, vinv v -> sok_recycle_chunks v X chs ->
  vinv (va_recycle_chunks v X chs) /\ used (va_recycle_chunks v X chs) <= used v + R_recycle_chunks X chs /\ 0 <= R_recycle_chunks X chs
  /\ (forall E, 0 <= E -> vroom Bs v (R_recycle_chunks X chs + 2 * page_size + E) -> ok_recycle_chunks v X chs).
Proof.
  induction chs as [|ch r IH]; intros v X I S; cbn [sok_recycle_chunks va_recycle_chunks R_recycle_chunks ok_recycle_chunks] in *.
  - split; [exact I|]. split; [lia|]. split; [lia|]. intros; exact Logic.I.
  - destruct S as [S1 SR]. destruct (room_recycle1 v X ch I S1) as (I1 & U1 & R1 & O1).
    destruct (IH _ _ I1 SR) as (I2 & U2 & R2 & O2). split; [exact I2|]. split; [lia|]. split; [lia|].
    intros E HE V. split.
    + apply (O1 (R_recycle_chunks (recycle1 X ch) r + E)); [lia|]. apply (proj2 (vroom_used _ _)). apply (proj1 (vroom_used _ _)) in V. lia.
    + apply (O2 E HE). apply (proj2 (vroom_used _ _)). apply (proj1 (vroom_used _ _)) in V. lia.
Qed.

#[using="AL"] Lemma room_recycle_batch : forall v X b, vinv v -> sok_recycle_batch v X b ->
  vinv (va_recycle_batch v X b) /\ used (va_recycle_batch v X b) <= used v + R_recycle_batch X b /\ 0 <= R_recycle_batch X b
  /\ (forall E, 0 <= E -> vroom Bs v (R_recycle_batch X b + 2 * page_size + E) -> ok_recycle_batch v X b).
Proof.
  intros v X b I [S1 S2]. unfold va_recycle_batch, R_recycle_batch, ok_recycle_batch.
  destruct (room_recycle_chunks _ v X I S1) as (I1 & U1 & R1 & O1). destruct I1 as [SN1 PA1].
  destruct (D_cd_facts _ _ S2) as [D0 D8]. pose proof (used_cd _ K_BCLASS _ S2 PA1) as U2.
  assert (R0 : 0 <= R_cd K_BCLASS (get_cls (fst (recycle_chunks X (qb_chunks b))) K_BCLASS)).
  { unfold R_cd. pose proof (Z.div_pos (D_cdealloc K_BCLASS (get_cls (fst (recycle_chunks X (qb_chunks b))) K_BCLASS)) 8 D0 ltac:(lia)). lia. }
  split; [split; [exact SN1| unfold va_cd; cbn [va_prim]; clear - PA1 D8; Z.div_mod_to_equations; lia]|].
  split; [lia|]. split; [lia|]. intros E HE V. split.
  - apply (O1 (R_cd K_BCLASS (get_cls (fst (recycle_chunks X (qb_chunks b))) K_BCLASS) + E)); [lia|]. apply (proj2 (vroom_used _ _)). apply (proj1 (vroom_used _ _)) in V. lia.
  - destruct S2 as (C & W & DB). split; [exact C|]. split; [exact W|]. split; [exact DB|].
    apply (proj2 (vroom_used _ _)). apply (proj1 (vroom_used _ _)) in V. unfold R_cd in *. unfold page_size in *. lia.
Qed.

#[using="AL"] Theorem room_dorecycle : forall bs v X, vinv v -> sok_dorecycle v X bs ->
  vinv (va_dorecycle v X bs) /\ used (va_dorecycle v X bs) <= used v + R_dorecycle X bs /\ 0 <= R_dorecycle X bs
  /\ (forall E, 0 <= E -> vroom Bs v (R_dorecycle X bs + 2 * page_size + E) -> ok_dorecycle v X bs).
Proof.
  induction bs as [|b r IH]; intros v X I S; cbn [sok_dorecycle va_dorecycle R_dorecycle ok_dorecycle] in *.
  - split; [exact I|]. split; [lia|]. split; [lia|]. intros; exact Logic.I.
  - destruct S as [S1 SR]. destruct (room_recycle_batch v X b I S1) as (I1 & U1 & R1 & O1).
    destruct (IH _ _ I1 SR) as (I2 & U2 & R2 & O2). split; [exact I2|]. split; [lia|]. split; [lia|].
    intros E HE V. split.
    + apply (O1 (R_dorecycle (recycle_batch X b) r + E)); [lia|]. apply (proj2 (vroom_used _ _)). apply (proj1 (vroom_used _ _)) in V. lia.
    + apply (O2 E HE). apply (proj2 (vroom_used _ _)). apply (proj1 (vroom_used _ _)) in V. lia.
Qed.

#[using="BO SPACE_EQ SPACE_AL"] Theorem link_enq_dorecycle : forall v mo P S loc todo (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> ok_enq v P loc -> ok_dorecycle (va_enq v P loc) (fst (enq_prim P loc), S) todo ->
  (forall mo', LINK Bs (va_dorecycle (va_enq v P loc) (fst (enq_prim P loc), S) todo) mo' -> kept mo mo' -> Q (Ok tt) mo') ->
  stwfL (ebind (t_enq AL P loc) (fun _ => t_dorecycle AL (fst (enq_prim P loc), S) todo)) mo Q.
Proof.
  intros v mo P S loc todo Q L OE OD K. apply stwf_ebind. apply (link_enq v mo P loc); [exact L| exact OE|]. intros mo1 L1 K1.
  apply (link_dorecycle _ _ mo1 _ Q L1 OD). intros mo2 L2 K2. apply K; [exact L2| exact (kept_trans _ _ _ K1 K2)].
Qed.
End F.
