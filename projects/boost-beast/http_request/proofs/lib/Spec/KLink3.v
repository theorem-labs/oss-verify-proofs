(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim Monad MSafeP STree Malloc Prog KInv MmNodes GapGrid KLink KLink2.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require MI_Contracts.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Notation mspec := (MSafeP.mspec mmsafe).
Notation MP := (Monad.M PState).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TBFree.
Context {R : Type}.
Implicit Types (k : mstate -> mapinfo -> M R) (bail : M R) (P : R -> Prop).

Lemma tb_undef : forall u (k0 : Z -> M R) P, tbound (SVis (EUndef u) k0) 0 0 P.
Proof. intros. cbn. splits; [lia|lia|]. intros z []. Qed.

Lemma tb_guard : forall tag c (t bail : M R) P, tbound t 0 0 P -> tbound (guard tag c t bail) 0 0 P.
Proof. intros. unfold guard. destruct c; [assumption| apply tb_undef]. Qed.

Lemma tb_queue : forall h m st (k1 : mstate -> M R) bail P,
  (forall st', tbound (k1 st') 0 0 P) -> tbound (queue h m st k1 bail) 0 0 P.
Proof. intros. unfold queue. apply tb_guard. apply tb_guard. destruct (get_head st h); apply H. Qed.

Lemma tb_free_meta : forall m st (k1 : mstate -> M R) bail P,
  (forall st', tbound (k1 st') 0 0 P) -> tbound (free_meta m st k1 bail) 0 0 P.
Proof. intros. unfold free_meta. apply tb_queue. exact H. Qed.

Lemma tb_activate_group : forall m st (k2 : mstate -> Z -> M R) bail P,
  (forall st' z, tbound (k2 st' z) 0 0 P) -> tbound (activate_group m st k2 bail) 0 0 P.
Proof. intros. unfold activate_group. apply tb_guard. apply H. Qed.

Lemma tb_dec_slots : forall st p (k3 : aptr -> Z -> M R) bail P,
  (forall g i, tbound (k3 g i) 0 0 P) -> tbound (dec_slots st p k3 bail) 0 0 P.
Proof. intros. unfold dec_slots. destruct (_ !! _) as [[g i]|]; [apply H| apply tb_undef]. Qed.

Lemma tb_free_group : forall rec st g k bail P,
  (forall st1 m idx k', (forall st3 mi, tbound (k' st3 mi) 0 0 P) -> tbound (rec st1 m idx k' bail) 0 0 P) ->
  (forall st' mi, tbound (k st' mi) 0 0 P) ->
  tbound (free_group R dec_slots rec st g k bail) 0 0 P.
Proof.
  intros rec st g k bail P Hrec Hk. unfold free_group.
  destruct (m_mem _) as [p|]; [| apply tb_undef].
  destruct (negb _).
  - apply tb_free_meta. intros; apply Hk.
  - apply tb_dec_slots. intros g' i. apply Hrec. intros st3 mi. apply tb_free_meta. intros; apply Hk.
Qed.

Lemma tb_nontrivial_free : forall fuel st g i k bail P,
  (forall st' mi, tbound (k st' mi) 0 0 P) ->
  tbound (nontrivial_free dec_slots fuel st g i k bail) 0 0 P.
Proof.
  induction fuel as [|f IH]; intros st g i k bail P Hk; cbn [nontrivial_free]; [apply tb_undef|].
  destruct (_ && _).
  - destruct (m_next _).
    + apply tb_guard. destruct (optr_eqb _ _); [destruct (active _ _)|];
        [apply tb_activate_group; intros; apply tb_free_group; auto| apply tb_free_group; auto| apply tb_free_group; auto].
    + apply tb_free_group; auto.
  - destruct (_ =? _).
    + apply tb_guard. destruct (negb _); [apply tb_queue; intros; apply Hk| apply Hk].
    + apply Hk.
Qed.
End TBFree.

Lemma tb_free_tail : forall st g idx, tbound (free_tail dec_slots st g idx) 0 0 (fun _ => True).
Proof.
  intros st g idx. unfold free_tail. apply tb_guard. destruct (negb _); [exact I|].
  apply tb_nontrivial_free. intros st2 [[base len]|]; [|exact I].
  destruct (negb _); [|exact I]. cbn. splits; [lia|lia|]. intros z _. destruct (munmap_answer_ok z); [exact I|].
  unfold bad_answer. apply tb_undef.
Qed.

Lemma tb_sbind_ret {A B} : forall (t : stree ev Z A) (g : A -> B) (P : B -> Prop) cb ck,
  tbound t cb ck (fun a => P (g a)) -> tbound (sbind t (fun a => SRet (g a))) cb ck P.
Proof.
  intros t. induction t as [r|e k IH]; intros g P cb ck H; cbn in *; [exact H|].
  destruct H as (H1 & H2 & H3). splits; [exact H1| exact H2|]. intros z Hz. apply IH. exact (H3 z Hz).
Qed.

Lemma tb_cfree : forall cs c, tbound (cfree cs (Some c)) 0 0 (fun _ => True).
Proof.
  intros cs c. unfold cfree. destruct (_ !! _) as [[g idx]|]; [| apply tb_undef].
  apply (tb_sbind_ret _ strip (fun _ => True)). apply tb_free_tail.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HCNT : Z := 3072.   (* [comment removed for export] *)
Definition live_cnt_ok (L : mled) : Prop :=
  exists X : list cptr, (forall c, In c (ld_live L) -> In c X) /\ Z.of_nat (length X) + 1 <= HCNT.

Inductive hreach : mstate -> mled -> Prop :=
| hreach_init secret resv : 0 <= secret < 2^64 -> hreach (strip (minit secret resv)) (led_init resv)
| hreach_malloc cs L n L' cs' r :
    hreach cs L -> 0 <= n -> live_cnt_ok L -> cpath L (cmalloc cs n) L' (cs', r) ->
    hreach cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end)
| hreach_free cs L c L' cs' :
    hreach cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
    hreach cs' (set_live (ap_remove c (ld_live L')) L').

Lemma hreach_creach : forall cs L, hreach cs L -> creach cs L.
Proof.
  intros cs L H. induction H.
  - apply creach_init. assumption.
  - eapply creach_malloc; eauto.
  - eapply creach_free; eauto.
Qed.

(* [comment removed for export] *)
Section HC.
Context {HC : HeapCeil}.

Definition OWN (X : list bptr) (G : PState -> Model -> Prop) : assn PState := fun s mo =>
  (exists L, hreach (ps_m s) L /\ KLB L (ps_brk s) mo /\ incl (map fst X) (ld_live L) /\ BUD L mo 0 0)
  /\ List.NoDup (map fst X) /\ G s mo.

(* [comment removed for export] *)
Definition MBUD (cs : mstate) (n : Z) : Prop :=
  forall L, hreach cs L -> ltotal L <= BUDCAP -> lcount L + RESV_MAX < GRID_J -> live_cnt_ok L /\ exists cb ck,
    0 <= cb /\ 0 <= ck /\ tbound (cmalloc cs n) cb ck (fun r => snd r <> None)
    /\ ltotal L + cb <= BUDCAP /\ lcount L + ck + RESV_MAX < GRID_J.

Lemma OWN_G : forall X G s mo, OWN X G s mo -> G s mo.
Proof. intros X G s mo (_ & _ & H). exact H. Qed.

Lemma OWN_perm : forall X Y G s mo, Permutation X Y -> OWN X G s mo -> OWN Y G s mo.
Proof.
  intros X Y G s mo HP ((L & Hc & HK & Hi & HB) & Hnd & HG).
  assert (HP' : Permutation (map fst X) (map fst Y)) by (apply Permutation_map; exact HP).
  split; [|split; [|exact HG]].
  - exists L. split; [exact Hc|]. split; [exact HK|]. split; [|exact HB]. intros c Hc'. apply Hi.
    eapply Permutation_in; [apply Permutation_sym; exact HP'| exact Hc'].
  - eapply Permutation_NoDup; [exact HP'| exact Hnd].
Qed.

Lemma OWN_weakG : forall X G G' s mo, OWN X G s mo -> (G s mo -> G' s mo) -> OWN X G' s mo.
Proof. intros X G G' s mo (A & B & C) H. split; [exact A|]. split; [exact B|]. auto. Qed.

Lemma OWN_other : forall X G s s' mo, OWN X G s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> G s' mo -> OWN X G s' mo.
Proof.
  intros X G s s' mo ((L & Hc & HK & Hi & HB) & Hnd & HG) Hm Hb HG'. split; [|split; [exact Hnd|exact HG']].
  exists L. rewrite Hm, Hb. auto.
Qed.

Lemma OWN_nodup : forall X G s mo, OWN X G s mo -> List.NoDup (map fst X).
Proof. intros X G s mo (_ & H & _). exact H. Qed.

(* [comment removed for export] *)
Lemma OWN_vm : forall X G s mo mo', OWN X G s mo -> mminv mo' -> m_halted mo' = None -> m_vmmaps mo' = m_vmmaps mo ->
  G s mo' -> OWN X G s mo'.
Proof.
  intros X G s mo mo' ((L & Hc & HK & Hi & HB) & Hnd & HG) MI HH E HG'. split; [|split; [exact Hnd| exact HG']].
  exists L. split; [exact Hc|]. split; [eapply KLB_vm_eq; eauto|]. split; [exact Hi|]. unfold BUD in *. rewrite E. exact HB.
Qed.

Lemma KLB_set_live : forall L v pbrk mo, KLB L pbrk mo -> KLB (set_live v L) pbrk mo.
Proof.
  intros L v pbrk mo K. destruct K; constructor; cbn; auto.
Qed.

Lemma event_post_live : forall L e z, ld_live (event_post L e z) = ld_live L.
Proof.
  intros L e z. destruct e; cbn; repeat (destruct (_ =? _)); try reflexivity;
  try (destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[? ?]|]; reflexivity);
  try (destruct (is_err z); reflexivity); try (destruct (_ || _); reflexivity).
Qed.

Lemma cpath_live {R} : forall L (t : stree ev Z R) L' r, cpath L t L' r -> ld_live L' = ld_live L.
Proof. intros L t L' r H. induction H; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

Lemma aptr_eqb_eq : forall a b, aptr_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma in_ap_remove : forall x c l, In x l -> x <> c -> In x (ap_remove c l).
Proof.
  intros x c l. induction l as [|y l IH]; intros Hin Hne; [destruct Hin|].
  cbn. destruct (aptr_eqb y c) eqn:E.
  - apply aptr_eqb_eq in E. subst y. destruct Hin as [->|Hin]; [congruence| exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; assumption].
Qed.

Lemma cmalloc_overflow : forall cs n, size_overflows n = true -> cmalloc cs n = SRet (strip cs, None).
Proof. intros cs n H. unfold cmalloc, malloc_core. rewrite H. reflexivity. Qed.

Lemma mspec_get_bind {A} (P : assn PState) (f : PState -> MP A) Q :
  (forall s0, mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q) -> mspec P (x <- mget ;; f x) Q.
Proof. intros H s mo HP. unfold mbind, mget. cbn. apply (H s). auto. Qed.

(* [comment removed for export] *)
Theorem raw_malloc_spec : forall X G n, frame_ok G -> 0 <= n ->
  mspec (fun s mo => OWN X G s mo /\ MBUD (ps_m s) n) (raw_malloc n)
        (fun r s mo => match r with
                       | Some p => OWN (p :: X) G s mo /\ n < 2^63
                       | None => False
                       end).
Proof.
  intros X G n HG Hn. unfold raw_malloc.
  apply mspec_get_bind. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [((L & Hc & HK & Hi & HB0) & Hnd & HGs) HB]].
  destruct (HB L Hc ltac:(unfold BUD in HB0; lia) ltac:(unfold BUD in HB0; lia)) as (HLC & cb & ck & Hcb & Hck & TB & B1 & B2).
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cmalloc (ps_m s0) n) _ (fun r => snd r <> None) G L s0 cb ck HG (MI_Contracts.cmalloc_contract_proof _ _ _ (hreach_creach _ _ Hc) Hn) TB Hcb Hck)|].
    intros s mo [-> ->]. splits; auto. unfold BUD. splits; auto. exact (kb_limit _ _ _ HK). }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HP & HK' & HG' & Hm & Hfa & Hso & HB').
  pose proof (cpath_live _ _ _ _ Hp) as Hlive. cbn [snd] in HPost, HP.
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros []. apply mspec_ret. intros s mo [-> ->].
  assert (Hcr : hreach st' (match p with Some c => set_live (c :: ld_live L') L' | None => L' end)).
  { exact (hreach_malloc _ _ _ _ _ _ Hc Hn HLC Hp). }
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
  destruct p as [c|]; [| exact (HP eq_refl)].
  split.
  - split; [|split; [|exact HG2]].
    + exists (set_live (c :: ld_live L') L'). split; [exact Hcr|]. split; [apply KLB_set_live; exact HK'|].
      split; [| unfold BUD, ltotal, lcount, lbrk_bytes, lbrk_cnt in *; cbn; exact HB'].
      cbn. intros x [<-|Hx]; [left; reflexivity| right]. rewrite Hlive. apply Hi. exact Hx.
    + cbn. constructor; [|exact Hnd]. intros Hin. apply HPost. rewrite Hlive. apply Hi. exact Hin.
  - destruct (size_overflows n) eqn:E.
    + exfalso. rewrite (cmalloc_overflow _ _ E) in Hp. inversion Hp.
    + unfold size_overflows in E. apply Z.leb_gt in E. lia.
Qed.

Theorem raw_free_spec : forall X G p, frame_ok G ->
  mspec (OWN (p :: X) G) (raw_free p) (fun _ => OWN X G).
Proof.
  intros X G p HG. unfold raw_free.
  apply mspec_get_bind. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> ((L & Hc & HK & Hi & HB0) & Hnd & HGs)].
  assert (Hin : In (fst p) (ld_live L)) by (apply Hi; left; reflexivity).
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cfree (ps_m s0) (Some (fst p))) _ (fun _ => True) G L s0 0 0 HG
                               (MI_Contracts.cfree_contract_proof _ _ _ (hreach_creach _ _ Hc) Hin) (tb_cfree _ _) (Z.le_refl 0) (Z.le_refl 0))|].
    intros s mo [-> ->]. splits; auto. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & _ & _ & HK' & HG' & Hm & Hfa & Hso & HB').
  pose proof (cpath_live _ _ _ _ Hp) as Hlive.
  apply mspec_upd'. intros s mo [-> ->].
  assert (Hcr : hreach st' (set_live (ap_remove (fst p) (ld_live L')) L')).
  { exact (hreach_free _ _ _ _ _ Hc Hin Hp). }
  split; [|split; [inversion Hnd; assumption| apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']]].
  exists (set_live (ap_remove (fst p) (ld_live L')) L'). split; [exact Hcr|]. split; [apply KLB_set_live; exact HK'|].
  split; [| unfold BUD, ltotal, lcount, lbrk_bytes, lbrk_cnt in *; cbn; exact HB'].
  cbn. intros x Hx. rewrite Hlive. apply in_ap_remove.
  - apply Hi. right. exact Hx.
  - inversion Hnd; subst. intros ->. apply H1. exact Hx.
Qed.
End HC.
