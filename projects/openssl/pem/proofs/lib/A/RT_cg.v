(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record cgraph : Type := mkCG { cg_site : list (Z * Z); cg_call : list (Z * Z) }.

(* [comment removed for export] *)
Definition cg_link (cg : cgraph) (r r' : Z) : Prop := exists F, In (r, F) (cg_site cg) /\ In (r', F) (cg_call cg).

Fixpoint cg_linked (cg : cgraph) (ch : list Z) : Prop :=
  match ch with
  | [] => True
  | r :: t => match t with [] => True | r' :: _ => cg_link cg r r' /\ cg_linked cg t end
  end.

(* [comment removed for export] *)
Definition cg_ctx (cg : cgraph) (G : Z) (ch : list Z) : Prop :=
  match ch with [] => False | r :: _ => In (r, G) (cg_call cg) /\ cg_linked cg ch end.

Lemma cg_ctx_call : forall cg F G r ch,
  cg_ctx cg F ch -> In (r, F) (cg_site cg) -> In (r, G) (cg_call cg) -> cg_ctx cg G (r :: ch).
Proof.
  intros cg F G r ch H HS HC. destruct ch as [|r0 t]; [destruct H|]. destruct H as [H0 HL].
  split; [exact HC|]. cbn [cg_linked]. split; [exists F; split; assumption|]. exact HL.
Qed.

Lemma cg_linked_tail : forall cg r t, cg_linked cg (r :: t) -> cg_linked cg t.
Proof. intros cg r t H. destruct t as [|r' t']; [exact I|]. exact (proj2 H). Qed.

(* [comment removed for export] *)
Lemma cg_linked_calls : forall cg t r, cg_linked cg (r :: t) -> Forall (fun x => exists G, In (x, G) (cg_call cg)) t.
Proof.
  intros cg t. induction t as [|r' t IH]; intros r H; [constructor|].
  destruct H as [(F & _ & HC) HL]. constructor; [exists F; exact HC|]. exact (IH r' HL).
Qed.

Lemma cg_ctx_calls : forall cg G ch, cg_ctx cg G ch -> Forall (fun x => exists G', In (x, G') (cg_call cg)) ch.
Proof.
  intros cg G ch H. destruct ch as [|r t]; [destruct H|]. destruct H as [H0 HL].
  constructor; [exists G; exact H0|]. exact (cg_linked_calls cg t r HL).
Qed.

(* [comment removed for export] *)
Fixpoint lprefix (pre l : list Z) : Prop :=
  match pre, l with
  | [], _ => True
  | x :: pre', y :: l' => x = y /\ lprefix pre' l'
  | _ :: _, [] => False
  end.

Lemma lprefix_length : forall pre l, lprefix pre l -> (length pre <= length l)%nat.
Proof.
  induction pre as [|x pre IH]; intros l H; [cbn; lia|].
  destruct l as [|y l]; [destruct H|]. destruct H as [_ H]. specialize (IH l H). cbn [length]. lia.
Qed.

Lemma lprefix_Forall : forall (P : Z -> Prop) pre l, Forall P l -> lprefix pre l -> Forall P pre.
Proof.
  intros P. induction pre as [|x pre IH]; intros l Hall Hpre; [constructor|].
  destruct l as [|y l]; [destruct Hpre|]. destruct Hpre as [-> Hpre]. inversion Hall; subst.
  constructor; [assumption| eapply IH; eassumption].
Qed.

Lemma lprefix_refl : forall l, lprefix l l.
Proof. induction l as [|x l IH]; [exact I| split; [reflexivity| exact IH]]. Qed.

Lemma cg_linked_prefix : forall cg pre l, cg_linked cg l -> lprefix pre l -> cg_linked cg pre.
Proof.
  intros cg. induction pre as [|x pre IH]; intros l HL HP; [exact I|].
  destruct l as [|y l]; [destruct HP|]. destruct HP as [<- HP].
  destruct pre as [|x' pre']; [exact I|].
  destruct l as [|y' l']; [destruct HP|]. pose proof HP as [<- _].
  destruct HL as [H1 H2]. split; [exact H1|]. exact (IH (x' :: l') H2 HP).
Qed.

(* [comment removed for export] *)
Definition cg_preds (cg : cgraph) (r : Z) : list Z :=
  flat_map (fun sf => if fst sf =? r then map fst (filter (fun cf => snd cf =? snd sf) (cg_call cg)) else []) (cg_site cg).

Lemma cg_preds_spec : forall cg r r', cg_link cg r r' -> In r' (cg_preds cg r).
Proof.
  intros cg r r' (F & HS & HC). unfold cg_preds. apply in_flat_map. exists (r, F). split; [exact HS|].
  cbn [fst snd]. rewrite Z.eqb_refl. apply in_map_iff. exists (r', F). split; [reflexivity|].
  apply filter_In. split; [exact HC|]. cbn [snd]. apply Z.eqb_refl.
Qed.

(* [comment removed for export] *)
Fixpoint cg_up (cg : cgraph) (fuel : nat) (r : Z) : list (list Z) :=
  [r] :: match fuel with
         | O => []
         | S f => flat_map (fun r' => map (cons r) (cg_up cg f r')) (cg_preds cg r)
         end.

Lemma cg_up_complete : forall cg fuel r t, cg_linked cg (r :: t) -> (length t <= fuel)%nat -> In (r :: t) (cg_up cg fuel r).
Proof.
  intros cg. induction fuel as [|f IH]; intros r t HL Hlen.
  - destruct t; [left; reflexivity| cbn in Hlen; lia].
  - destruct t as [|r' t']; [left; reflexivity|]. cbn [cg_up]. right.
    destruct HL as [H1 H2]. apply in_flat_map. exists r'. split; [exact (cg_preds_spec cg r r' H1)|].
    apply in_map. apply IH; [exact H2| cbn [length] in Hlen; lia].
Qed.

(* [comment removed for export] *)
Definition cg_traces (cg : cgraph) (eps : list (Z * Z)) (drv : list Z) : list (list Z) :=
  flat_map (fun ep => ([snd ep] :: map (fun ra => [snd ep; ra]) drv)
                      ++ flat_map (fun rc => if snd rc =? fst ep then map (cons (snd ep)) (cg_up cg 28 (fst rc)) else [])
                                  (cg_call cg)) eps.

Lemma cg_traces_pc : forall cg eps drv E pc, In (E, pc) eps -> In [pc] (cg_traces cg eps drv).
Proof.
  intros cg eps drv E pc H. unfold cg_traces. apply in_flat_map. exists (E, pc). split; [exact H|].
  apply in_or_app. left. left. reflexivity.
Qed.

Lemma cg_traces_drv : forall cg eps drv E pc ra, In (E, pc) eps -> In ra drv -> In [pc; ra] (cg_traces cg eps drv).
Proof.
  intros cg eps drv E pc ra H Hra. unfold cg_traces. apply in_flat_map. exists (E, pc). split; [exact H|].
  apply in_or_app. left. right. cbn [snd]. apply in_map_iff. exists ra. split; [reflexivity| exact Hra].
Qed.

Lemma cg_traces_chain : forall cg eps drv E pc ch r t,
  In (E, pc) eps -> cg_ctx cg E ch -> lprefix (r :: t) ch -> (length t <= 28)%nat -> In (pc :: r :: t) (cg_traces cg eps drv).
Proof.
  intros cg eps drv E pc ch r t H HC HP Hlen. unfold cg_traces. apply in_flat_map. exists (E, pc). split; [exact H|].
  apply in_or_app. right. destruct ch as [|r0 t0]; [destruct HC|]. destruct HC as [H0 HL]. pose proof HP as [<- _].
  apply in_flat_map. exists (r, E). split; [exact H0|]. cbn [fst snd]. rewrite Z.eqb_refl.
  apply in_map. apply cg_up_complete; [|exact Hlen]. exact (cg_linked_prefix cg (r :: t) (r :: t0) HL HP).
Qed.

(* [comment removed for export] *)
Lemma cg_up_forall : forall (P : Z -> Prop) cg, (forall rc, In rc (cg_call cg) -> P (fst rc)) ->
  forall fuel r p, P r -> In p (cg_up cg fuel r) -> Forall P p.
Proof.
  intros P cg HP. induction fuel as [|f IH]; intros r p Hr Hin; cbn [cg_up] in Hin.
  - destruct Hin as [<-|[]]. constructor; [exact Hr| constructor].
  - destruct Hin as [<-|Hin]; [constructor; [exact Hr| constructor]|].
    apply in_flat_map in Hin as (r' & Hr' & Hin). apply in_map_iff in Hin as (q & <- & Hq).
    constructor; [exact Hr|]. apply (IH r' q); [|exact Hq].
    unfold cg_preds in Hr'. apply in_flat_map in Hr' as (sf & _ & Hx). destruct (fst sf =? r); [|destruct Hx].
    apply in_map_iff in Hx as (cf & <- & Hcf). apply filter_In in Hcf as [Hcf _]. exact (HP cf Hcf).
Qed.

Lemma cg_traces_forall : forall (P : Z -> Prop) cg eps drv,
  (forall ep, In ep eps -> P (snd ep)) -> Forall P drv -> (forall rc, In rc (cg_call cg) -> P (fst rc)) ->
  forall tr, In tr (cg_traces cg eps drv) -> Forall P tr.
Proof.
  intros P cg eps drv Hpc Hdrv Hc tr Hin. unfold cg_traces in Hin. apply in_flat_map in Hin as (ep & Hep & Hin).
  pose proof (Hpc ep Hep) as Ppc. apply in_app_or in Hin as [Hin|Hin].
  - destruct Hin as [<-|Hin]; [constructor; [exact Ppc| constructor]|].
    apply in_map_iff in Hin as (ra & <- & Hra). constructor; [exact Ppc|]. constructor; [|constructor].
    exact (proj1 (Forall_forall _ _) Hdrv ra Hra).
  - apply in_flat_map in Hin as (rc & Hrc & Hin). destruct (snd rc =? fst ep); [|destruct Hin].
    apply in_map_iff in Hin as (q & <- & Hq). constructor; [exact Ppc|].
    exact (cg_up_forall P cg Hc 28 (fst rc) q (Hc rc Hrc) Hq).
Qed.

(* [comment removed for export] *)
Definition cg_site_ok (pcs : list Z) (r : Z) : Prop := 4096 <= r < 2 ^ 64 /\ ~ In r pcs.
Definition cg_wf (cg : cgraph) (eps : list (Z * Z)) (drv : list Z) (nmax : Z) : Prop :=
  Forall (fun rc => cg_site_ok (map snd eps) (fst rc)) (cg_call cg) /\ Z.of_nat (length (cg_traces cg eps drv)) <= nmax.

Definition memZ (x : Z) (l : list Z) : bool := existsb (Z.eqb x) l.
Lemma memZ_false : forall x l, memZ x l = false -> ~ In x l.
Proof.
  intros x l H Hin. unfold memZ in H. assert (E : existsb (Z.eqb x) l = true) by (apply existsb_exists; exists x; split; [exact Hin| apply Z.eqb_refl]).
  rewrite E in H. discriminate.
Qed.

Definition cg_wfb (cg : cgraph) (eps : list (Z * Z)) (drv : list Z) (nmax : Z) : bool :=
  forallb (fun rc => (4096 <=? fst rc) && (fst rc <? 2 ^ 64) && negb (memZ (fst rc) (map snd eps))) (cg_call cg)
  && (Z.of_nat (length (cg_traces cg eps drv)) <=? nmax).

Lemma cg_wfb_sound : forall cg eps drv nmax, cg_wfb cg eps drv nmax = true -> cg_wf cg eps drv nmax.
Proof.
  intros cg eps drv nmax H. unfold cg_wfb in H. apply andb_prop in H as [H1 H2]. split.
  - apply Forall_forall. intros rc Hrc. pose proof (proj1 (forallb_forall _ _) H1 rc Hrc) as X. cbv beta in X.
    apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    split; [lia|]. apply memZ_false. destruct (memZ (fst rc) (map snd eps)); [discriminate X3| reflexivity].
  - apply Z.leb_le. exact H2.
Qed.

Lemma cg_ctx_sites_ok : forall cg eps drv nmax G ch, cg_wf cg eps drv nmax -> cg_ctx cg G ch -> Forall (cg_site_ok (map snd eps)) ch.
Proof.
  intros cg eps drv nmax G ch [W _] HC. pose proof (cg_ctx_calls cg G ch HC) as HF.
  eapply Forall_impl; [|exact HF]. cbv beta. intros x (G' & HG). exact (proj1 (Forall_forall _ _) W (x, G') HG).
Qed.

(* [comment removed for export] *)
Definition cg_has (cg : cgraph) (sites calls : list (Z * Z)) : Prop := incl sites (cg_site cg) /\ incl calls (cg_call cg).

Lemma cg_has_sub : forall cg s c s' c', cg_has cg s c -> incl s' s -> incl c' c -> cg_has cg s' c'.
Proof. intros cg s c s' c' [H1 H2] I1 I2. split; eapply incl_tran; eassumption. Qed.

Lemma cg_has_site : forall cg s c r F, cg_has cg s c -> In (r, F) s -> In (r, F) (cg_site cg).
Proof. intros cg s c r F [H _] Hin. exact (H _ Hin). Qed.
Lemma cg_has_call : forall cg s c r G, cg_has cg s c -> In (r, G) c -> In (r, G) (cg_call cg).
Proof. intros cg s c r G [_ H] Hin. exact (H _ Hin). Qed.

(* [comment removed for export] *)
Definition memP (x : Z * Z) (l : list (Z * Z)) : bool := existsb (fun y => (fst x =? fst y) && (snd x =? snd y)) l.
Lemma memP_true : forall x l, memP x l = true -> In x l.
Proof.
  intros [a b] l H. unfold memP in H. apply existsb_exists in H as ([a' b'] & Hin & E). cbn [fst snd] in E.
  apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst. exact Hin.
Qed.
Definition inclP (l1 l2 : list (Z * Z)) : bool := forallb (fun x => memP x l2) l1.
Lemma inclP_sound : forall l1 l2, inclP l1 l2 = true -> incl l1 l2.
Proof. intros l1 l2 H x Hx. apply memP_true. exact (proj1 (forallb_forall _ _) H x Hx). Qed.

Lemma cg_has_lit : forall s c s' c', inclP s' s = true -> inclP c' c = true -> cg_has (mkCG s c) s' c'.
Proof. intros s c s' c' H1 H2. split; apply inclP_sound; assumption. Qed.
