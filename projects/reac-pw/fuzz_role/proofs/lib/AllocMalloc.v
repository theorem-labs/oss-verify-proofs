(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO0v.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/Reusable/YO0v.v; 1277 of its 1541 lines of code are new or changed and 706 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0y YO03 YO0m YO0p.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import AllocSI AllocGS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Fixpoint lw {A : Type} (F : kreq -> Z -> Prop) (P : A -> Prop) (t : itree astate A) : Prop :=
match t with
| IRet a => P a
| IFail _ => True
| IAsk q _ k => forall z, F q z -> lw F P (k z)
end.
Definition FA (q : kreq) (z : Z) : Prop := True.
Definition G4 (F : kreq -> Z -> Prop) : Prop := forall q z, F q z -> mmapclass q = true -> z = 1.

Lemma lw_mono {A} F (P P' : A -> Prop) t : (forall a, P a -> P' a) -> lw F P t -> lw F P' t.
Proof.
induction t as [a|q sn k IH|f]; cbn; intros HP H.
- apply HP, H.
- intros z Hz. apply IH; [exact HP | apply H, Hz].
- exact I.
Qed.
Lemma lw_conj {A} F (P P' : A -> Prop) t : lw F P t -> lw F P' t -> lw F (fun a => P a /\ P' a) t.
Proof.
induction t as [a|q sn k IH|f]; cbn; intros H H'.
- split; assumption.
- intros z Hz. apply IH; [apply H, Hz | apply H', Hz].
- exact I.
Qed.
Lemma lw_ibind {A B} F (t : itree astate A) (k : A -> itree astate B) P :
lw F (fun a => lw F P (k a)) t -> lw F P (ibind t k).
Proof.
induction t as [a|q sn c IH|f]; cbn; intros H.
- exact H.
- intros z Hz. apply IH. apply H, Hz.
- exact I.
Qed.
Lemma itok_lw {A} (t : itree astate A) (P Q : A -> Prop) :
lw FA P t -> itok t (fun a => P a -> Q a) -> itok t Q.
Proof.
induction t as [a|q sn k IH|f]; cbn; intros HL HI.
- apply HI, HL.
- destruct HI as [Hr HI]. split; [exact Hr|]. intros z Hz. apply IH; [apply HL; exact I | apply HI, Hz].
- exact HI.
Qed.
Lemma lw_cpath04 {A} (t : itree astate A) P tr a : lw canswer04 P t -> cpath04 t tr a -> P a.
Proof.
revert tr. induction t as [a'|q sn k IH|f]; intros tr HL HC; destruct tr as [|[q' z] tr]; cbn in HC; try contradiction.
- subst. exact HL.
- destruct HC as (-> & Hc & HC). cbn in HL. eapply IH; [apply HL, Hc | exact HC].
Qed.
Lemma lw_yields {A} (t : itree astate A) P tr a : lw FA P t -> yields t tr a -> P a.
Proof.
revert tr. induction t as [a'|q sn k IH|f]; intros tr HL HC; destruct tr as [|[q' z] tr]; cbn in HC; try contradiction.
- subst. exact HL.
- destruct HC as (-> & Hc & HC). cbn in HL. eapply IH; [apply HL; exact I | exact HC].
Qed.
Lemma G4_04 : G4 canswer04.
Proof. intros q z H E. unfold canswer04 in H. rewrite E in H. exact H. Qed.

Section st.
Context {A B : Type} (F : kreq -> Z -> Prop).
Lemma lw_ret (a : A) s (P : A * astate -> Prop) : P (a, s) -> lw F P (ret a s).
Proof. intros H; exact H. Qed.
Lemma lw_bind (m : M B) (k : B -> M A) s P :
lw F (fun r => lw F P (k (fst r) (snd r))) (m s) -> lw F P (bind m k s).
Proof. intros H. unfold bind. apply lw_ibind. eapply lw_mono; [|exact H]. intros [b s'] Hb. exact Hb. Qed.
Lemma lw_fail f s (P : A * astate -> Prop) : lw F P (@fail A f s).
Proof. exact I. Qed.
End st.
Lemma lw_get F s (P : astate * astate -> Prop) : P (s, s) -> lw F P (get s).
Proof. intros H; exact H. Qed.
Lemma lw_put F s s' (P : unit * astate -> Prop) : P (tt, s') -> lw F P (put s' s).
Proof. intros H; exact H. Qed.
Lemma lw_modify F f s (P : unit * astate -> Prop) : P (tt, f s) -> lw F P (modify f s).
Proof. intros H; exact H. Qed.
Lemma lw_ask F q s (P : bool * astate -> Prop) : (forall z, F q z -> P (negb (z =? 0), s)) -> lw F P (ask q s).
Proof. intros H. exact H. Qed.
Lemma lw_askz F q s (P : Z * astate -> Prop) : (forall z, F q z -> P (z, s)) -> lw F P (askz q s).
Proof. intros H. exact H. Qed.
Lemma lw_massert F b i s (P : unit * astate -> Prop) : (b = true -> P (tt, s)) -> lw F P (massert b i s).
Proof. intros H. unfold massert. destruct b; [apply H; reflexivity | exact I]. Qed.
Lemma lw_mcheck F b i s (P : unit * astate -> Prop) : (b = true -> P (tt, s)) -> lw F P (mcheck b i s).
Proof. intros H. unfold mcheck. destruct b; [apply H; reflexivity | exact I]. Qed.
Lemma lw_getm F p s (P : ameta * astate -> Prop) :
(forall am, MT s p = Some (MUsed am) -> P (am, s)) -> lw F P (getm p s).
Proof.
intros H. unfold getm. apply lw_bind. apply lw_get. cbn [fst snd]. unfold MT in H.
destruct (mlookup (st_metas s) p) as [[| |am]|]; try exact I. exact (H am eq_refl).
Qed.
Lemma lw_setm F p am s (P : unit * astate -> Prop) : P (tt, upd_meta p (MUsed am) s) -> lw F P (setm p am s).
Proof. intros H; exact H. Qed.
Lemma lw_setslot F p x s (P : unit * astate -> Prop) : P (tt, upd_meta p x s) -> lw F P (setslot p x s).
Proof. intros H; exact H. Qed.
Lemma lw_get_links F p s (P : (option sptr * option sptr) * astate -> Prop) :
(forall x, MT s p = Some x -> P (links_of x, s)) -> lw F P (get_links p s).
Proof.
intros H. unfold get_links. apply lw_bind. apply lw_get. cbn [fst snd]. unfold MT in H.
destruct (mlookup (st_metas s) p) as [x|]; [exact (H x eq_refl) | exact I].
Qed.
Lemma lw_set_links F p pr nx s (P : unit * astate -> Prop) :
(forall x, MT s p = Some x -> P (tt, upd_meta p (with_links x pr nx) s)) -> lw F P (set_links p pr nx s).
Proof.
intros H. unfold set_links. apply lw_bind. apply lw_get. cbn [fst snd]. unfold MT in H.
destruct (mlookup (st_metas s) p) as [x|]; [exact (H x eq_refl) | exact I].
Qed.
Lemma lw_get_head F h s (P : option sptr * astate -> Prop) :
P (match h with HActive sc => nth (Z.to_nat sc) (st_active s) None | HFreeMeta => st_free_meta_head s end, s) ->
lw F P (get_head h s).
Proof. intros H. unfold get_head. destruct h; exact H. Qed.
Lemma lw_set_head F h v s (P : unit * astate -> Prop) : P (tt, set_head_st h v s) -> lw F P (set_head h v s).
Proof. intros H. destruct h; exact H. Qed.

Class PreR (Rl : astate -> astate -> Prop) : Prop := {
pr_refl : forall s, Rl s s;
pr_trans : forall a b c, Rl a b -> Rl b c -> Rl a c }.
Class SLok (Rl : astate -> astate -> Prop) : Prop :=
sl_ok : forall s p x pr nx, MT s p = Some x -> Rl s (upd_meta p (with_links x pr nx) s).

Section rp.
Context (F : kreq -> Z -> Prop) (Rl : astate -> astate -> Prop) `{PR : PreR Rl}.
Definition RP {A} (m : M A) : Prop := let _ := PR in forall s, lw F (fun r => Rl s (snd r)) (m s).
Lemma lw_use {A B} (m : M A) (k : A -> M B) s0 s P :
lw F (fun r => Rl s (snd r)) (m s) -> Rl s0 s -> (forall a s', Rl s0 s' -> lw F P (k a s')) -> lw F P (bind m k s).
Proof.
intros Hm H0 Hk. apply lw_bind. eapply lw_mono; [|exact Hm]. intros [a s'] H'. cbn [fst snd] in *.
apply Hk. eapply pr_trans; eauto.
Qed.
Lemma RP_ret {A} (a : A) : RP (ret a).
Proof. intros s. exact (pr_refl s). Qed.
Lemma RP_fail {A} f : RP (@fail A f).
Proof. intros s. exact I. Qed.
Lemma RP_bind {A B} (m : M A) (k : A -> M B) : RP m -> (forall a, RP (k a)) -> RP (bind m k).
Proof.
intros Hm Hk s. eapply lw_use; [apply Hm | apply pr_refl |].
intros a s' H. eapply lw_mono; [|apply Hk]. intros r Hr. eapply pr_trans; eauto.
Qed.
Lemma RP_get : RP get.
Proof. intros s. exact (pr_refl s). Qed.
Lemma RP_modify f : (forall s, Rl s (f s)) -> RP (modify f).
Proof. intros H s. exact (H s). Qed.
Lemma RP_massert b i : RP (massert b i).
Proof. intros s. unfold massert. destruct b; [exact (pr_refl s) | exact I]. Qed.
Lemma RP_mcheck b i : RP (mcheck b i).
Proof. intros s. unfold mcheck. destruct b; [exact (pr_refl s) | exact I]. Qed.
Lemma RP_ask q : RP (ask q).
Proof. intros s z _. exact (pr_refl s). Qed.
Lemma RP_askz q : RP (askz q).
Proof. intros s z _. exact (pr_refl s). Qed.
Lemma RP_getm p : RP (getm p).
Proof. intros s. apply lw_getm. intros. exact (pr_refl s). Qed.
Lemma RP_get_links p : RP (get_links p).
Proof. intros s. apply lw_get_links. intros. exact (pr_refl s). Qed.
Lemma RP_get_head h : RP (get_head h).
Proof. intros s. apply lw_get_head. exact (pr_refl s). Qed.
Lemma RP_set_head h v : (forall s, Rl s (set_head_st h v s)) -> RP (set_head h v).
Proof. intros H s. apply lw_set_head. exact (H s). Qed.
Lemma RP_setm p am : (forall s, Rl s (upd_meta p (MUsed am) s)) -> RP (setm p am).
Proof. intros H s. apply lw_setm. exact (H s). Qed.
Lemma RP_setslot p x : (forall s, Rl s (upd_meta p x s)) -> RP (setslot p x).
Proof. intros H s. apply lw_setslot. exact (H s). Qed.
Context `{SL : SLok Rl}.
Lemma RP_set_links p pr nx : RP (set_links p pr nx).
Proof. intros s. apply lw_set_links. intros x Hx. exact (sl_ok s p x pr nx Hx). Qed.
Lemma RP_set_prev p pr : RP (set_prev p pr).
Proof. unfold set_prev. apply RP_bind; [apply RP_get_links | intros; apply RP_set_links]. Qed.
Lemma RP_set_next p nx : RP (set_next p nx).
Proof. unfold set_next. apply RP_bind; [apply RP_get_links | intros; apply RP_set_links]. Qed.
Lemma RP_queue h m : (forall s v, Rl s (set_head_st h v s)) -> RP (queue h m).
Proof.
intros HH. unfold queue. apply RP_bind; [apply RP_get_links | intros l].
apply RP_bind; [apply RP_massert | intros _].
apply RP_bind; [apply RP_get_head | intros [head|]].
- apply RP_bind; [apply RP_get_links | intros lh]. destruct (fst lh); [| apply RP_fail].
apply RP_bind; [apply RP_set_links | intros _]. apply RP_bind; [apply RP_set_next | intros _]. apply RP_set_prev.
- apply RP_bind; [apply RP_set_links | intros _]. apply RP_set_head. intros s. apply HH.
Qed.
Lemma RP_dequeue h m : (forall s v, Rl s (set_head_st h v s)) -> RP (dequeue h m).
Proof.
intros HH. unfold dequeue. apply RP_bind; [apply RP_get_links | intros l].
apply RP_bind; [| intros _; apply RP_set_links].
destruct (osptr_eqb (snd l) (Some m)); [apply RP_set_head; intros s0; apply HH|].
destruct (fst l) as [pr|]; [| apply RP_fail]. destruct (snd l) as [nx|]; [| apply RP_fail].
apply RP_bind; [apply RP_set_next | intros _]. apply RP_bind; [apply RP_set_prev | intros _].
apply RP_bind; [apply RP_get_head | intros hd]. destruct (osptr_eqb hd (Some m)); [apply RP_set_head; intros s1; apply HH | apply RP_ret].
Qed.
End rp.

Definition prj (am : ameta) : sptr * Z * Z * Z * list (option frame) :=
(am_mem am, am_last am, am_sc am, am_maplen am, map ss_fr (am_slots am)).
Definition MS (s : astate) (q : sptr) : option (sptr * Z * Z * Z * list (option frame)) :=
match MT s q with Some (MUsed am) => Some (prj am) | _ => None end.
Lemma prj_fr a a' i : prj a = prj a' -> ss_fr (nth_slot a i) = ss_fr (nth_slot a' i).
Proof.
unfold prj, nth_slot. intros E. injection E as E1 E2 E3 E4 E5.
rewrite <- (map_nth ss_fr (am_slots a)), <- (map_nth ss_fr (am_slots a')), E5. reflexivity.
Qed.
Lemma prj_geo a a' : prj a = prj a' ->
am_mem a = am_mem a' /\ am_last a = am_last a' /\ am_sc a = am_sc a' /\ am_maplen a = am_maplen a'.
Proof. unfold prj. intros E. injection E as E1 E2 E3 E4 E5. auto. Qed.
Lemma prj_stride a a' : prj a = prj a' -> stride_of a = stride_of a'.
Proof. intros E. destruct (prj_geo _ _ E) as (_&E2&E3&E4). unfold stride_of. rewrite E2, E3, E4. reflexivity. Qed.
Lemma prj_slot_start a a' i : prj a = prj a' -> slot_start a i = slot_start a' i.
Proof. intros E. unfold slot_start. rewrite (prj_stride _ _ E). destruct (prj_geo _ _ E) as (->&_). reflexivity. Qed.

Definition owned_mapsK (X : list sptr) (K : nat -> Prop) (s : astate) : Prop :=
forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> rg_live rg = true ->
K k \/ exists g am, usedX X s g am /\ 0 < am_maplen am /\ prid (am_mem am) = k.
Definition WI (PS PG PN : Prop) (X : list sptr) (R : option (sptr * Z)) (K : nat -> Prop) (s : astate) : Prop :=
(PS -> owned_mapsK X K s /\ empty_ok X R s /\ empty_unique X R s /\ children_ok X s /\ hand_keys s) /\
(PG -> GSX X s) /\ (PN -> NLX X s).
Definition K0 (k : nat) : Prop := False.
Lemma WI_SIX PS PG PN X R s : WI PS PG PN X R K0 s -> PS -> SIX X R s.
Proof.
intros [H _] P. destruct (H P) as (OM & R2). split; [|exact R2].
intros k rg H1 H2 H3. destruct (OM k rg H1 H2 H3) as [[] | E]. exact E.
Qed.
Lemma WI_GSX PS PG PN X R K s : WI PS PG PN X R K s -> PG -> GSX X s.
Proof. intros (_ & H & _) P. exact (H P). Qed.
Lemma WI_NLX PS PG PN X R K s : WI PS PG PN X R K s -> PN -> NLX X s.
Proof. intros (_ & _ & H) P. exact (H P). Qed.
Lemma WI_of PS PG PN X R s : (PS -> SIX X R s) -> (PG -> GSX X s) -> (PN -> NLX X s) -> WI PS PG PN X R K0 s.
Proof.
intros HS HG HN. split; [|split; [exact HG | exact HN]]. intros P. destruct (HS P) as (OM & R2). split; [|exact R2].
intros k rg H1 H2 H3. right. exact (OM k rg H1 H2 H3).
Qed.

Definition corr (X : list sptr) (s : astate) (X' : list sptr) (s' : astate) : Prop :=
(forall g a', usedX X' s' g a' -> exists a, usedX X s g a /\ prj a = prj a') /\
(forall g a, usedX X s g a -> exists a', usedX X' s' g a' /\ prj a = prj a').
Definition regs_le (s s' : astate) : Prop :=
forall k rg, region_of s' k = Some rg -> rg_kind rg = RkMap -> rg_live rg = true ->
exists rg0, region_of s k = Some rg0 /\ rg_kind rg0 = RkMap /\ rg_live rg0 = true.
Definition hk (s : astate) : Z := hand s - Z.of_nat (length (st_metas s)).

Lemma corr_trans X1 s1 X2 s2 X3 s3 : corr X1 s1 X2 s2 -> corr X2 s2 X3 s3 -> corr X1 s1 X3 s3.
Proof.
intros [A1 B1] [A2 B2]. split.
- intros g a3 H3. destruct (A2 g a3 H3) as (a2 & H2 & E2). destruct (A1 g a2 H2) as (a1 & H1 & E1).
exists a1. split; [exact H1 | congruence].
- intros g a1 H1. destruct (B1 g a1 H1) as (a2 & H2 & E2). destruct (B2 g a2 H2) as (a3 & H3 & E3).
exists a3. split; [exact H3 | congruence].
Qed.
Lemma corr_MS X s s' : (forall q, MS s' q = MS s q) -> corr X s X s'.
Proof.
intros H. split.
- intros g a' Hu'. pose proof (usedX_MT _ _ _ _ Hu') as [M' NX]. specialize (H g). unfold MS in H. rewrite M' in H.
destruct (MT s g) as [[| |a]|] eqn:E; try discriminate. assert (Hp : prj a' = prj a) by congruence.
exists a. split; [apply usedX_intro; assumption | symmetry; exact Hp].
- intros g a Hu. pose proof (usedX_MT _ _ _ _ Hu) as [M NX]. specialize (H g). unfold MS in H. rewrite M in H.
destruct (MT s' g) as [[| |a']|] eqn:E; try discriminate. assert (Hp : prj a' = prj a) by congruence.
exists a'. split; [apply usedX_intro; assumption | symmetry; exact Hp].
Qed.
Lemma corr_eqv X s X' s' : (forall g a, usedX X' s' g a <-> usedX X s g a) -> corr X s X' s'.
Proof.
intros H. split.
- intros g a Hu. exists a. split; [apply H, Hu | reflexivity].
- intros g a Hu. exists a. split; [apply H, Hu | reflexivity].
Qed.
Lemma corr_metas X s s' : st_metas s' = st_metas s -> corr X s X s'.
Proof. intros E. apply corr_eqv. intros g a. unfold usedX, MTX, MT. rewrite E. tauto. Qed.
Lemma regs_le_refl s : regs_le s s.
Proof. intros k rg H1 H2 H3. exists rg. auto. Qed.
Lemma regs_le_trans s1 s2 s3 : regs_le s1 s2 -> regs_le s2 s3 -> regs_le s1 s3.
Proof.
intros A B k rg H1 H2 H3. destruct (B k rg H1 H2 H3) as (rg2 & E2 & K2 & L2). exact (A k rg2 E2 K2 L2).
Qed.
Lemma regs_le_eq s s' : st_regions s' = st_regions s -> regs_le s s'.
Proof. intros E k rg H1 H2 H3. exists rg. unfold region_of in *. rewrite E in H1. auto. Qed.

Lemma WI_corr PS PG PN X R K s X' s' :
corr X s X' s' -> regs_le s s' -> hk s' = hk s -> WI PS PG PN X R K s -> WI PS PG PN X' R K s'.
Proof.
intros [CB CF] RL HK (HS & HG & HN). split; [|split].
- intros PS0. destruct (HS PS0) as (OM & EO & EU & CO & HKs). split; [|split; [|split; [|split]]].
+ intros k rg Hk Hm Hl. destruct (RL k rg Hk Hm Hl) as (rg0 & H0 & Hm0 & Hl0).
destruct (OM k rg0 H0 Hm0 Hl0) as [Kk | (g & a & Hu & Hml & Hp)]; [left; exact Kk | right].
destruct (CF g a Hu) as (a' & Hu' & Ep). destruct (prj_geo _ _ Ep) as (E1 & _ & _ & E4).
exists g, a'. split; [exact Hu'|]. rewrite <- E1, <- E4. auto.
+ intros g a' Hu' Hfl Hun. destruct (CB g a' Hu') as (a & Hu & Ep).
destruct (prj_geo _ _ Ep) as (_ & E2 & E3 & E4). rewrite <- E3, <- E4. apply (EO g a Hu); [|exact Hun].
intros i Hi. rewrite (prj_fr _ _ i Ep). apply Hfl. lia.
+ intros g1 a1' g2 a2' H1 H2 F1 F2 U1 U2 Hsc.
destruct (CB g1 a1' H1) as (a1 & H1' & E1). destruct (CB g2 a2' H2) as (a2 & H2' & E2).
destruct (prj_geo _ _ E1) as (_&L1&S1&_). destruct (prj_geo _ _ E2) as (_&L2&S2&_).
apply (EU g1 a1 g2 a2 H1' H2'); [| | exact U1 | exact U2 | congruence].
* intros i Hi. rewrite (prj_fr _ _ i E1). apply F1. lia.
* intros i Hi. rewrite (prj_fr _ _ i E2). apply F2. lia.
+ intros g a' i fr Hu' Hi Hfr Hk. destruct (CB g a' Hu') as (a & Hu & Ep). destruct (prj_geo _ _ Ep) as (_&L&S&_).
destruct (CO g a i fr Hu ltac:(lia) ltac:(rewrite (prj_fr _ _ i Ep); exact Hfr) Hk) as (c & ac & Huc & Hmlc & Hmemc & Hscc).
destruct (CF c ac Huc) as (ac' & Huc' & Epc). destruct (prj_geo _ _ Epc) as (M'&_&S'&ML').
exists c, ac'. split; [exact Huc'|]. split; [lia|]. split; [|lia].
rewrite <- M', Hmemc. apply prj_slot_start. exact Ep.
+ unfold hand_keys, hk in *. lia.
- intros PG0. pose proof (HG PG0) as GS0. intros g a' Hu' Hml. destruct (CB g a' Hu') as (a & Hu & Ep).
destruct (prj_geo _ _ Ep) as (_&_&S&ML). destruct (GS0 g a Hu ltac:(lia)) as [G1 G2]. split.
+ intros Hs. rewrite <- ML. apply G1. lia.
+ intros Hs fr Hfr. rewrite <- ML. apply G2; [lia|]. rewrite (prj_fr _ _ 0 Ep). exact Hfr.
- intros PN0 g a' Hu' Hml. destruct (CB g a' Hu') as (a & Hu & Ep).
destruct (prj_geo _ _ Ep) as (_&L&_&ML). rewrite <- L. apply (HN PN0 g a Hu). lia.
Qed.
Lemma WI_R PS PG PN X R K s : WI PS PG PN X None K s -> WI PS PG PN X R K s.
Proof.
intros [HS HG]. split; [|exact HG]. intros P. destruct (HS P) as (OM & EO & EU & CO & HKs).
split; [exact OM|]. split; [|split; [|split; [exact CO | exact HKs]]].
- intros g am Hu Hf _. apply (EO g am Hu Hf). intros i E. discriminate.
- intros g1 a1 g2 a2 H1 H2 F1 F2 _ _ Hs. apply (EU g1 a1 g2 a2 H1 H2 F1 F2); [intros i E; discriminate | intros i E; discriminate | exact Hs].
Qed.
Lemma WI_same PS PG PN X R K s s' :
st_metas s' = st_metas s -> st_regions s' = st_regions s -> hand s' = hand s -> WI PS PG PN X R K s -> WI PS PG PN X R K s'.
Proof.
intros Em Er Eh. apply WI_corr; [apply corr_metas, Em | apply regs_le_eq, Er | unfold hk; rewrite Em, Eh; reflexivity].
Qed.
Lemma len_upd_In s g x : In g (keys s) -> length (st_metas (upd_meta g x s)) = length (st_metas s).
Proof.
intros H. pose proof (keys_upd_In g x s H) as E. unfold keys in E.
rewrite <- (length_map fst (st_metas (upd_meta g x s))), E, length_map. reflexivity.
Qed.
Lemma len_upd_notIn s g x : ~ In g (keys s) -> length (st_metas (upd_meta g x s)) = S (length (st_metas s)).
Proof.
intros H. pose proof (keys_upd_notIn g x s H) as E. unfold keys in E.
rewrite <- (length_map fst (st_metas (upd_meta g x s))), E, length_app, length_map. cbn. lia.
Qed.
Lemma WI_new_region PS PG PN X R s x :
WI PS PG PN X R K0 s -> WI PS PG PN X R (fun k => k = length (st_regions s)) (set_regions (st_regions s ++ [x]) s).
Proof.
intros [HS HG]. split.
- intros P. destruct (HS P) as (OM & EO & EU & CO & HK). split; [|split; [exact EO|split; [exact EU|split; [exact CO|exact HK]]]].
intros k rg Hk Hm Hl. destruct (Nat.eq_dec k (length (st_regions s))) as [E|Ne]; [left; exact E|].
assert (Hk' : region_of s k = Some rg).
{ unfold region_of in *. cbn in Hk. destruct (Nat.lt_ge_cases k (length (st_regions s))) as [Hlt|Hge].
- rewrite nth_error_app1 in Hk by exact Hlt. exact Hk.
- rewrite nth_error_app2 in Hk by exact Hge. destruct (k - length (st_regions s))%nat as [|n] eqn:E; [lia|].
destruct n; cbn in Hk; discriminate. }
destruct (OM k rg Hk' Hm Hl) as [[]|E]. right. exact E.
- exact HG.
Qed.
Lemma WI_kill PS PG PN X R s r len :
WI PS PG PN X R (fun k => k = r) s -> WI PS PG PN X R K0 (set_regions (lupd (st_regions s) r (mkRegion RkMap len [] false)) s).
Proof.
intros [HS HG]. split.
- intros P. destruct (HS P) as (OM & EO & EU & CO & HK). split; [|split; [exact EO|split; [exact EU|split; [exact CO|exact HK]]]].
intros k rg Hk Hm Hl. rewrite region_of_upd in Hk.
destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:E.
{ injection Hk as <-. cbn in Hl. discriminate. }
destruct (OM k rg Hk Hm Hl) as [Ek | Ow]; [|right; exact Ow]. exfalso. subst k.
apply andb_false_iff in E. destruct E as [E|E]; [rewrite Nat.eqb_refl in E; discriminate|].
apply Nat.ltb_ge in E. pose proof (YO0z.region_of_lt _ _ _ Hk). lia.
- exact HG.
Qed.
Lemma WI_enframe PS PG PN X g idx am x fr s :
WI PS PG PN X (Some (g, idx)) K0 s -> usedX X s g am -> 0 <= idx <= am_last am ->
length (am_slots am) = Z.to_nat (am_last am + 1) -> ss_fr x = Some fr -> fr_kind fr = FUser ->
(PG -> 0 < am_maplen am -> am_sc am = 63 -> idx = 0 -> am_maplen am * PGSZ <= fr_n fr + 3 * PGSZ) ->
WI PS PG PN X None K0 (upd_meta g (MUsed (upd_slot am idx x)) s).
Proof.
intros (HS & HG & HN) Hu Hi Hlen Hx Hfk HB.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
pose proof (upd_slot_fields am idx x) as (Fm & Fl & Fsc & Fml & Fst & _).
assert (NS : forall j, 0 <= j -> nth_slot (upd_slot am idx x) j = if j =? idx then x else nth_slot am j).
{ intros j Hj. apply nth_slot_upd_slot; lia. }
set (a1 := upd_slot am idx x) in *.
assert (UB : forall q a, usedX X (upd_meta g (MUsed a1) s) q a -> (q = g /\ a = a1) \/ (q <> g /\ usedX X s q a)).
{ intros q a H. apply usedX_upd in H as [(E1 & _ & E3) | (E1 & E2)]; [left; split; [exact E1 | congruence] | right; auto]. }
assert (UF : forall q a, usedX X s q a -> exists a', usedX X (upd_meta g (MUsed a1) s) q a' /\
am_mem a' = am_mem a /\ am_maplen a' = am_maplen a /\ am_sc a' = am_sc a).
{ intros q a H. destruct (sptr_eq_dec q g) as [->|Hne].
- pose proof (usedX_fun _ _ _ _ _ H Hu) as ->. exists a1. split; [apply usedX_upd; left; auto|]. auto.
- exists a. split; [apply usedX_upd; right; auto | auto]. }
assert (HAS : forall q a, usedX X (upd_meta g (MUsed a1) s) q a -> q = g -> exists i, 0 <= i <= am_last a /\ ss_fr (nth_slot a i) <> None).
{ intros q a H Eq. subst q. destruct (UB g a H) as [[_ ->] | [N _]]; [|exfalso; exact (N eq_refl)].
exists idx. rewrite Fl. split; [lia|]. rewrite NS by lia. rewrite Z.eqb_refl, Hx. discriminate. }
split; [|split].
- intros P. destruct (HS P) as (OM & EO & EU & CO & HK). split; [|split; [|split; [|split]]].
 + intros k rg Hk Hm Hl. destruct (OM k rg Hk Hm Hl) as [[]|(q & a & Hq & Hml & Hp)]. right.
destruct (UF q a Hq) as (a' & Hq' & E1 & E2 & _). exists q, a'. rewrite E1, E2. auto.
 + intros q a Hq Hf Hun. destruct (UB q a Hq) as [[-> ->] | [Hne Hq0]].
* exfalso. destruct (HAS g a1 Hq eq_refl) as (i & Hi' & Hn). exact (Hn (Hf i Hi')).
* apply (EO q a Hq0 Hf). intros i E. injection E as E1 _. exact (Hne (eq_sym E1)).
 + intros q1 b1 q2 b2 H1 H2 F1 F2 _ _ Hs.
destruct (UB q1 b1 H1) as [[-> ->] | [N1 H1']]; [exfalso; destruct (HAS g a1 H1 eq_refl) as (i & Hi' & Hn); exact (Hn (F1 i Hi'))|].
destruct (UB q2 b2 H2) as [[-> ->] | [N2 H2']]; [exfalso; destruct (HAS g a1 H2 eq_refl) as (i & Hi' & Hn); exact (Hn (F2 i Hi'))|].
apply (EU q1 b1 q2 b2 H1' H2' F1 F2); [intros i E; injection E as E1 _; exact (N1 (eq_sym E1)) | intros i E; injection E as E1 _; exact (N2 (eq_sym E1)) | exact Hs].
 + intros q a j f Hq Hj Hf Hkd. destruct (UB q a Hq) as [[-> ->] | [Hne Hq0]].
* rewrite Fl in Hj. rewrite NS in Hf by lia. destruct (j =? idx) eqn:Ej.
{ rewrite Hx in Hf. injection Hf as <-. rewrite Hfk in Hkd. discriminate. }
destruct (CO g am j f Hu Hj Hf Hkd) as (c & ac & Hc & Hml & Hmem & Hsc).
destruct (UF c ac Hc) as (ac' & Hc' & E1 & E2 & E3). exists c, ac'. split; [exact Hc'|].
rewrite E1, E2, E3, Fsc. split; [exact Hml|]. split; [|exact Hsc]. rewrite Hmem. unfold slot_start. rewrite Fm, Fst. reflexivity.
* destruct (CO q a j f Hq0 Hj Hf Hkd) as (c & ac & Hc & Hml & Hmem & Hsc).
destruct (UF c ac Hc) as (ac' & Hc' & E1 & E2 & E3). exists c, ac'. split; [exact Hc'|].
rewrite E1, E2, E3. auto.
 + unfold hand_keys in *. rewrite len_upd_In by (eapply MT_Some_In_keys; exact Mg). exact HK.
- intros P q a Hq Hml. destruct (UB q a Hq) as [[-> ->] | [Hne Hq0]].
 + rewrite Fml in Hml |- *. rewrite Fsc. destruct (HG P g am Hu Hml) as [G1 G2]. split; [exact G1|].
intros H63 f0 Hf0. rewrite NS in Hf0 by lia. destruct (0 =? idx) eqn:E0.
* apply Z.eqb_eq in E0. rewrite Hx in Hf0. injection Hf0 as <-. apply HB; auto.
* apply G2; assumption.
 + exact (HG P q a Hq0 Hml).
- intros P q a Hq Hml. destruct (UB q a Hq) as [[-> ->] | [Hne Hq0]].
 + rewrite Fml in Hml. rewrite Fl. exact (HN P g am Hu Hml).
 + exact (HN P q a Hq0 Hml).
Qed.
Lemma WI_install PS PG PN X K s s' g a1 :
WI PS PG PN (g :: X) None K s -> memb g X = false ->
MT s' g = Some (MUsed a1) -> (forall q, q <> g -> MT s' q = MT s q) ->
length (st_metas s') = length (st_metas s) -> hand s' = hand s -> (forall k, region_of s' k = region_of s k) ->
(forall i, ss_fr (nth_slot a1 i) = None) ->
(forall k, K k -> 0 < am_maplen a1 /\ prid (am_mem a1) = k) ->
(PG -> 0 < am_maplen a1 -> am_sc a1 < 48 -> am_maplen a1 * PGSZ <= MMAX) ->
(am_maplen a1 = 0 -> 1 <= am_last a1) ->
WI PS PG PN X (Some (g, 0)) K0 s'.
Proof.
intros (HS & HG & HN) NX EM EO EL EH ER HF1 HKk HB HL.
split; [|split].
- intros P. destruct (HS P) as (OM & EOk & EU & CO & HK). split; [|split; [|split; [|split]]].
 + intros k rg Hk Hm Hl. rewrite ER in Hk. right. destruct (OM k rg Hk Hm Hl) as [Kk | (q & a & Hq & Hml & Hp)].
* destruct (HKk k Kk) as [Hml Hp]. exists g, a1. split; [apply (ux_used_m X s s' g a1 NX EM)|]. auto.
* exists q, a. split; [exact (proj2 (ux_used_fwd X s s' g a1 NX EM EO q a Hq)) | auto].
 + intros q a Hq Hf Hun. destruct (ux_used_bwd X s s' g a1 NX EM EO q a Hq) as [[-> ->]|[Hne Hq0]].
* exfalso. exact (Hun 0 eq_refl).
* apply (EOk q a Hq0 Hf). intros i E. discriminate.
 + intros q1 b1 q2 b2 H1 H2 F1 F2 U1 U2 Hs.
destruct (ux_used_bwd X s s' g a1 NX EM EO q1 b1 H1) as [[-> ->]|[N1 H1']]; [exfalso; exact (U1 0 eq_refl)|].
destruct (ux_used_bwd X s s' g a1 NX EM EO q2 b2 H2) as [[-> ->]|[N2 H2']]; [exfalso; exact (U2 0 eq_refl)|].
apply (EU q1 b1 q2 b2 H1' H2' F1 F2); [intros i E; discriminate | intros i E; discriminate | exact Hs].
 + intros q a i f Hq Hi Hf Hkd. destruct (ux_used_bwd X s s' g a1 NX EM EO q a Hq) as [[-> ->]|[Hne Hq0]].
* rewrite HF1 in Hf. discriminate.
* destruct (CO q a i f Hq0 Hi Hf Hkd) as (c & ac & Hc & R1 & R2 & R3). exists c, ac.
split; [exact (proj2 (ux_used_fwd X s s' g a1 NX EM EO c ac Hc)) | auto].
 + unfold hand_keys in *. rewrite EH, EL. exact HK.
- intros P q a Hq Hml. destruct (ux_used_bwd X s s' g a1 NX EM EO q a Hq) as [[-> ->]|[Hne Hq0]].
 + split; [apply HB; assumption|]. intros _ fr Hfr. rewrite HF1 in Hfr. discriminate.
 + exact (HG P q a Hq0 Hml).
- intros P q a Hq Hml. destruct (ux_used_bwd X s s' g a1 NX EM EO q a Hq) as [[-> ->]|[Hne Hq0]].
 + exact (HL Hml).
 + exact (HN P q a Hq0 Hml).
Qed.
Lemma WI_nested PS PG PN X g idx am x fr s2 s4 m a1 :
WI PS PG PN (m :: X) (Some (g, idx)) K0 s2 -> memb m X = false -> usedX (m :: X) s2 g am ->
0 <= idx <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
ss_fr x = Some fr -> am_sc am < 48 ->
MT s4 m = Some (MUsed a1) -> MT s4 g = Some (MUsed (upd_slot am idx x)) ->
(forall q, q <> m -> q <> g -> MT s4 q = MT s2 q) ->
length (st_metas s4) = length (st_metas s2) -> hand s4 = hand s2 -> (forall k, region_of s4 k = region_of s2 k) ->
(forall i, ss_fr (nth_slot a1 i) = None) -> am_maplen a1 = 0 -> am_mem a1 = slot_start am idx -> am_sc a1 < am_sc am ->
1 <= am_last a1 ->
WI PS PG PN X (Some (m, 0)) K0 s4.
Proof.
intros (HS & HG & HN) NX Hu Hi Hlen Hx Hsc48 EM EG EO EL EH ER HF1 Hml1 Hmem1 Hsc1 HL1.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg NXg].
assert (Hgm : g <> m).
{ intros ->. rewrite memb_cons, sptr_eqb_refl in NXg. discriminate. }
assert (NXg' : memb g X = false) by (rewrite memb_cons in NXg; apply orb_false_elim in NXg; tauto).
pose proof (upd_slot_fields am idx x) as (Fm & Fl & Fsc & Fml & Fst & _).
assert (NS : forall j, 0 <= j -> nth_slot (upd_slot am idx x) j = if j =? idx then x else nth_slot am j).
{ intros j Hj. apply nth_slot_upd_slot; lia. }
set (a2 := upd_slot am idx x) in *.
assert (BW : forall q a, usedX X s4 q a -> (q = m /\ a = a1) \/ (q = g /\ a = a2) \/ (q <> m /\ q <> g /\ usedX (m :: X) s2 q a)).
{ intros q a H. pose proof (usedX_MT _ _ _ _ H) as [Mq NXq].
destruct (sptr_eq_dec q m) as [->|N1]; [left; split; [reflexivity|congruence]|].
destruct (sptr_eq_dec q g) as [->|N2]; [right; left; split; [reflexivity|congruence]|].
right; right. split; [exact N1|]. split; [exact N2|]. apply usedX_intro.
- rewrite memb_cons, NXq. apply sptr_eqb_neq in N1. rewrite N1. reflexivity.
- rewrite <- (EO q N1 N2). exact Mq. }
assert (FW : forall q a, usedX (m :: X) s2 q a -> exists a', usedX X s4 q a' /\
am_mem a' = am_mem a /\ am_maplen a' = am_maplen a /\ am_sc a' = am_sc a).
{ intros q a H. pose proof (usedX_MT _ _ _ _ H) as [Mq NXq].
assert (N1 : q <> m) by (intros ->; rewrite memb_cons, sptr_eqb_refl in NXq; discriminate).
assert (NXq' : memb q X = false) by (rewrite memb_cons in NXq; apply orb_false_elim in NXq; tauto).
destruct (sptr_eq_dec q g) as [->|N2].
- pose proof (usedX_fun _ _ _ _ _ H Hu) as ->. exists a2. split; [apply usedX_intro; assumption|]. auto.
- exists a. split; [apply usedX_intro; [exact NXq' | rewrite (EO q N1 N2); exact Mq] | auto]. }
assert (U1 : usedX X s4 m a1) by (apply usedX_intro; assumption).
assert (FA2 : ~ (forall i, 0 <= i <= am_last a2 -> ss_fr (nth_slot a2 i) = None)).
{ intros H. specialize (H idx ltac:(rewrite Fl; lia)). rewrite NS in H by lia. rewrite Z.eqb_refl, Hx in H. discriminate. }
assert (UR : forall q, q <> g -> forall i, Some (g, idx) <> Some (q, i)).
{ intros q N i E. injection E as E1 _. exact (N (eq_sym E1)). }
split; [|split].
- intros P. destruct (HS P) as (OM & EOk & EU & CO & HK). split; [|split; [|split; [|split]]].
 + intros k rg Hk Hm Hl. rewrite ER in Hk. right. destruct (OM k rg Hk Hm Hl) as [[] | (q & a & Hq & Hml & Hp)].
destruct (FW q a Hq) as (a' & Hq' & E1 & E2 & _). exists q, a'. rewrite E1, E2. auto.
 + intros q a Hq Hf Hun. destruct (BW q a Hq) as [[-> ->] | [[-> ->] | (N1 & N2 & Hq0)]].
* exfalso. exact (Hun 0 eq_refl).
* exfalso. exact (FA2 Hf).
* exact (EOk q a Hq0 Hf (UR q N2)).
 + intros q1 b1 q2 b2 H1 H2 F1 F2 V1 V2 Hs.
destruct (BW q1 b1 H1) as [[-> ->] | [[-> ->] | (N1 & N2 & H1')]]; [exfalso; exact (V1 0 eq_refl) | exfalso; exact (FA2 F1)|].
destruct (BW q2 b2 H2) as [[-> ->] | [[-> ->] | (N3 & N4 & H2')]]; [exfalso; exact (V2 0 eq_refl) | exfalso; exact (FA2 F2)|].
exact (EU q1 b1 q2 b2 H1' H2' F1 F2 (UR q1 N2) (UR q2 N4) Hs).
 + intros q a j f Hq Hj Hf Hkd. destruct (BW q a Hq) as [[-> ->] | [[-> ->] | (N1 & N2 & Hq0)]].
* rewrite HF1 in Hf. discriminate.
* rewrite Fl in Hj. rewrite NS in Hf by lia. destruct (j =? idx) eqn:Ej.
{ apply Z.eqb_eq in Ej. subst j. exists m, a1. split; [exact U1|]. split; [exact Hml1|]. split; [|rewrite Fsc; exact Hsc1].
rewrite Hmem1. unfold slot_start. rewrite Fm, Fst. reflexivity. }
destruct (CO g am j f Hu Hj Hf Hkd) as (c & ac & Hc & R1 & R2 & R3).
destruct (FW c ac Hc) as (ac' & Hc' & E1 & E2 & E3). exists c, ac'. split; [exact Hc'|].
rewrite E1, E2, E3, Fsc. split; [exact R1|]. split; [|exact R3]. rewrite R2. unfold slot_start. rewrite Fm, Fst. reflexivity.
* destruct (CO q a j f Hq0 Hj Hf Hkd) as (c & ac & Hc & R1 & R2 & R3).
destruct (FW c ac Hc) as (ac' & Hc' & E1 & E2 & E3). exists c, ac'. split; [exact Hc'|]. rewrite E1, E2, E3. auto.
 + unfold hand_keys in *. rewrite EH, EL. exact HK.
- intros P q a Hq Hml. destruct (BW q a Hq) as [[-> ->] | [[-> ->] | (N1 & N2 & Hq0)]].
 + lia.
 + rewrite Fml in Hml |- *. rewrite Fsc. destruct (HG P g am Hu Hml) as [G1 _]. split; [exact G1 | intros; lia].
 + exact (HG P q a Hq0 Hml).
- intros P q a Hq Hml. destruct (BW q a Hq) as [[-> ->] | [[-> ->] | (N1 & N2 & Hq0)]].
 + exact HL1.
 + rewrite Fml in Hml. rewrite Fl. exact (HN P g am Hu Hml).
 + exact (HN P q a Hq0 Hml).
Qed.
Ltac ms := cbn beta iota zeta delta [fst snd].

Definition RT (s s' : astate) : Prop :=
(forall q, MS s' q = MS s q) /\ st_regions s' = st_regions s /\ hand s' = hand s /\ keys s' = keys s.
#[export] Instance RT_pre : PreR RT.
Proof.
split.
- intros s. split; [intros q; reflexivity | repeat split; reflexivity].
- intros a b c (A1&A2&A3&A4) (B1&B2&B3&B4). split; [intros q; rewrite B1, A1; reflexivity | repeat split; congruence].
Qed.
Lemma RT_upd s p x : In p (keys s) -> MS (upd_meta p x s) p = MS s p -> RT s (upd_meta p x s).
Proof.
intros Hk Hp. split; [|split; [reflexivity | split; [reflexivity | apply keys_upd_In, Hk]]].
intros q. destruct (sptr_eq_dec q p) as [->|Hne]; [exact Hp|]. unfold MS. rewrite MT_upd_other by exact Hne. reflexivity.
Qed.
#[export] Instance RT_sl : SLok RT.
Proof.
intros s p x pr nx Hx. apply RT_upd; [eapply MT_Some_In_keys; exact Hx|].
unfold MS. rewrite MT_upd_same, Hx. destruct x as [| |am]; [reflexivity | reflexivity | destruct am; reflexivity].
Qed.
Lemma RT_setm s p a a' : MT s p = Some (MUsed a) -> prj a' = prj a -> RT s (upd_meta p (MUsed a') s).
Proof. intros H E. apply RT_upd; [eapply MT_Some_In_keys; exact H|]. unfold MS. rewrite MT_upd_same, H, E. reflexivity. Qed.
Lemma RT_head h v s : RT s (set_head_st h v s).
Proof. destruct h; (split; [intros q; reflexivity | repeat split; reflexivity]). Qed.
Lemma decay_RP F sc : RP F RT (decay_bounces sc).
Proof.
unfold decay_bounces. destruct (bounce_idx sc); [|apply RP_ret].
apply RP_modify. intros s. cbv beta zeta.
match goal with |- context [if ?c then _ else _] => destruct c end; [apply pr_refl|].
split; [intros q; reflexivity | repeat split; reflexivity].
Qed.
Lemma activate_RT F m s : lw F (fun r => RT s (snd r)) (activate_group m s).
Proof.
unfold activate_group. apply lw_bind, lw_getm. intros am Hm. ms.
apply lw_bind, lw_massert. intros _. ms.
apply lw_bind, lw_setm. ms. apply lw_ret. ms.
apply (RT_setm s m am); [exact Hm | destruct am; reflexivity].
Qed.
Lemma try_avail_RT F sc s : lw F (fun r => RT s (snd r)) (try_avail sc s).
Proof.
assert (G : forall s1, RT s s1 -> lw F (fun r => RT s (snd r)) (try_avail sc s1)); [|apply G, pr_refl].
intros s1 H1. unfold try_avail.
apply lw_bind, lw_get_head. ms.
destruct (nth (Z.to_nat sc) (st_active s1) None) as [m0|]; [|exact H1].
apply lw_bind, lw_getm. intros am0 M0. ms.
destruct (negb (am_avail am0 =? 0)).
{ apply lw_bind, lw_setm. ms. apply lw_ret. ms.
eapply pr_trans; [exact H1 | apply (RT_setm s1 m0 am0); [exact M0 | destruct am0; reflexivity]]. }
match goal with |- lw _ _ (bind ?mm _ _) => assert (R1 : RP F RT mm) end.
{ destruct (am_freed am0 =? 0).
- apply RP_bind; [apply (RP_dequeue F RT); intros; apply RT_head | intros; apply RP_get_head].
- apply RP_bind; [apply RP_set_head; intros; apply RT_head | intros; apply RP_ret]. }
eapply (lw_use F RT); [apply R1 | exact H1 |]. intros om1 s2 H2. ms.
destruct om1 as [m1|]; [|exact H2].
apply lw_bind, lw_getm. intros am1 M1. ms.
match goal with |- lw _ _ (bind ?mm _ _) => assert (R2 : RP F RT mm) end.
{ destruct (am_freed am1 =? ones (am_last am1)); [|apply RP_ret].
destruct (am_next am1); [|apply RP_fail]. apply RP_bind; [apply RP_set_head; intros; apply RT_head | intros; apply RP_ret]. }
eapply (lw_use F RT); [apply R2 | exact H2 |]. intros m2 s3 H3. ms.
apply lw_bind, lw_getm. intros am2 M2. ms.
match goal with |- lw _ _ (bind ?mm _ _) => assert (R3 : lw F (fun r => RT s3 (snd r)) (mm s3)) end.
{ destruct (Z.land (am_freed am2) (ones (am_aidx am2)) =? 0); [|exact (pr_refl s3)].
destruct (negb (osptr_eqb (am_next am2) (Some m2))).
- destruct (am_next am2); [|exact I]. apply lw_bind, lw_set_head. ms. apply lw_ret. ms. apply RT_head.
- apply lw_bind, lw_setm. ms. apply lw_ret. ms. apply (RT_setm s3 m2 am2); [exact M2 | destruct am2; reflexivity]. }
eapply (lw_use F RT); [exact R3 | exact H3 |]. intros m3 s4 H4. ms.
eapply (lw_use F RT); [apply activate_RT | exact H4 |]. intros mask s5 H5. ms.
apply lw_bind, lw_massert. intros _. ms.
apply lw_bind, lw_getm. intros am3 M3. ms.
eapply (lw_use F RT); [apply decay_RP | exact H5 |]. intros u s6 H6. ms.
apply lw_bind, lw_getm. intros am3' M3'. ms.
apply lw_bind, lw_setm. ms. apply lw_ret. ms.
eapply pr_trans; [exact H6 | apply (RT_setm s6 m3 am3'); [exact M3' | destruct am3'; reflexivity]].
Qed.
Lemma RT_corr X s s' : RT s s' -> corr X s X s' /\ regs_le s s' /\ hk s' = hk s.
Proof.
intros (H1 & H2 & H3 & H4). split; [apply corr_MS, H1|]. split; [apply regs_le_eq, H2|].
unfold hk. rewrite H3. f_equal. f_equal. rewrite <- (length_map fst (st_metas s')), <- (length_map fst (st_metas s)).
change (length (keys s') = length (keys s)). rewrite H4. reflexivity.
Qed.

Definition RA (s s' : astate) : Prop :=
st_metas s' = st_metas s /\ st_free_meta_head s' = st_free_meta_head s /\ regs_le s s' /\
st_areas s' = st_areas s /\ st_avail_meta_count s' = st_avail_meta_count s.
Lemma RA_refl s : RA s s.
Proof. split; [reflexivity|]. split; [reflexivity|]. split; [apply regs_le_refl | split; reflexivity]. Qed.
Lemma regs_le_app s s' x : st_regions s' = st_regions s ++ [x] -> rg_kind x <> RkMap -> regs_le s s'.
Proof.
intros E Hx k rg Hk Hm Hl. unfold region_of in *. rewrite E in Hk.
destruct (Nat.lt_ge_cases k (length (st_regions s))) as [Hlt|Hge].
- rewrite nth_error_app1 in Hk by exact Hlt. exists rg. auto.
- rewrite nth_error_app2 in Hk by exact Hge. destruct (k - length (st_regions s))%nat as [|n].
+ cbn in Hk. injection Hk as <-. contradiction.
+ destruct n; cbn in Hk; discriminate.
Qed.
Lemma regs_le_lupd s s' r x : st_regions s' = lupd (st_regions s) r x ->
(rg_kind x = RkMap -> rg_live x = true ->
rg_kind (nth r (st_regions s) (mkRegion RkMap 0 [] false)) = RkMap /\ rg_live (nth r (st_regions s) (mkRegion RkMap 0 [] false)) = true) ->
regs_le s s'.
Proof.
intros E Hx k rg Hk Hm Hl. unfold region_of in *. rewrite E, nth_error_lupd in Hk.
destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:C.
- injection Hk as <-. apply andb_prop in C as [C1 C2]. apply Nat.eqb_eq in C1. apply Nat.ltb_lt in C2. subst k.
exists (nth r (st_regions s) (mkRegion RkMap 0 [] false)). split; [apply nth_error_nth'; exact C2 | apply Hx; assumption].
- exists rg. auto.
Qed.
Lemma area_from_brk_lw F s : lw F (fun r => RA s (snd r)) (area_from_brk s).
Proof.
unfold area_from_brk. apply lw_bind, lw_get. ms.
destruct ((st_avail_meta_area_count s =? 0) && match st_brk s with BrkDead => false | _ => true end); [|exact (RA_refl s)].
destruct (st_brk s) as [| |r p].
- apply lw_bind, lw_ask. intros z1 _. ms. apply lw_bind, lw_ask. intros z2 _. ms.
destruct (negb (z2 =? 0)).
+ apply lw_bind. unfold new_region. apply lw_bind, lw_get. ms. apply lw_bind, lw_put. ms. apply lw_ret. ms.
apply lw_bind, lw_modify. ms. apply lw_bind, lw_ask. intros z3 _. ms. apply lw_ret. ms.
split; [reflexivity|]. split; [reflexivity|]. split; [|split; reflexivity].
apply (regs_le_app s _ (mkRegion RkBrk (2 * PGSZ) [] true)); [reflexivity | discriminate].
+ apply lw_bind, lw_modify. ms. apply lw_ret. ms.
split; [reflexivity|]. split; [reflexivity|]. split; [apply regs_le_eq; reflexivity | split; reflexivity].
- exact (RA_refl s).
- apply lw_bind, lw_ask. intros z _. ms. destruct (negb (z =? 0)).
+ apply lw_bind. unfold upd_region. apply lw_modify. ms. apply lw_bind, lw_modify. ms. apply lw_ret. ms.
split; [reflexivity|]. split; [reflexivity|]. split; [|split; reflexivity].
eapply regs_le_lupd; [reflexivity|]. cbn. intros E. discriminate.
+ apply lw_bind, lw_modify. ms. apply lw_ret. ms.
split; [reflexivity|]. split; [reflexivity|]. split; [apply regs_le_eq; reflexivity | split; reflexivity].
Qed.
Lemma area_from_mmap_lw F s : lw F (fun r => RA s (snd r) /\ (G4 F -> fst r = true)) (area_from_mmap s).
Proof.
unfold area_from_mmap. apply lw_bind, lw_get. ms.
destruct (st_avail_meta_area_count s =? 0); [|apply lw_ret; ms; split; [exact (RA_refl s) | reflexivity]].
apply lw_bind, lw_ask. intros z Hz. ms. destruct (z =? 0) eqn:Ez; cbn [negb].
- apply lw_ret. ms. split; [exact (RA_refl s)|]. intros HG. pose proof (HG _ _ Hz eq_refl). apply Z.eqb_eq in Ez. lia.
- apply lw_bind. unfold new_region. apply lw_bind, lw_get. ms. apply lw_bind, lw_put. ms. apply lw_ret. ms.
apply lw_bind, lw_modify. ms. apply lw_ret. ms. split; [|reflexivity].
split; [reflexivity|]. split; [reflexivity|]. split; [|split; reflexivity].
apply (regs_le_app s _ (mkRegion RkMetaRes (Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ) [] true)); [reflexivity | discriminate].
Qed.
Ltac ohand := let H0 := fresh in intros H0; unfold hand, nareas;
cbn [st_areas st_avail_meta_count set_avail_meta_area_count set_avail_meta_areas set_area_tail set_area_head
set_areas set_avail_meta_count set_avail_meta set_regions]; rewrite length_app, H0; cbn [length]; unfold METAS_PER_AREA; lia.
Lemma open_area_lw F nu s : lw F (fun r => st_metas (snd r) = st_metas s /\ st_free_meta_head (snd r) = st_free_meta_head s /\
regs_le s (snd r) /\ (st_avail_meta_count s = 0 -> hand (snd r) = hand s) /\ (G4 F -> fst r = true)) (open_area nu s).
Proof.
unfold open_area. apply lw_bind, lw_get. ms.
destruct nu.
- apply lw_bind, lw_ask. intros z Hz. ms. destruct (z =? 0) eqn:Ez; cbn [negb].
+ apply lw_ret. ms. split; [reflexivity|]. split; [reflexivity|]. split; [apply regs_le_refl|]. split; [reflexivity|].
intros HG. pose proof (HG _ _ Hz eq_refl). apply Z.eqb_eq in Ez. lia.
+ apply lw_bind. unfold upd_region. apply lw_modify. ms. apply lw_bind, lw_modify. ms. apply lw_ret. ms.
split; [reflexivity|]. split; [reflexivity|]. split; [|split; [ohand | reflexivity]].
eapply regs_le_lupd; [reflexivity|]. cbn. intros H1 H2. split; assumption.
- apply lw_bind, lw_ret. ms. apply lw_bind, lw_ret. ms. apply lw_bind, lw_modify. ms. apply lw_ret. ms.
split; [reflexivity|]. split; [reflexivity|]. split; [apply regs_le_eq; reflexivity|]. split; [ohand | reflexivity].
Qed.
Lemma new_area_lw F s : lw F (fun r => st_metas (snd r) = st_metas s /\ st_free_meta_head (snd r) = st_free_meta_head s /\
regs_le s (snd r) /\ (st_avail_meta_count s = 0 -> hand (snd r) = hand s) /\ (G4 F -> fst r = true))
((nu <- area_from_brk ;; rs <- area_from_mmap ;; if rs then open_area nu else ret false) s).
Proof.
apply lw_bind. eapply lw_mono; [|apply area_from_brk_lw]. intros [nu s1] H1. ms. cbn beta iota delta [fst snd] in H1.
apply lw_bind. eapply lw_mono; [|apply area_from_mmap_lw]. intros [rs s2] H2. ms. cbn beta iota delta [fst snd] in H2.
destruct H1 as (A1&B1&C1&D1&E1). destruct H2 as ((A2&B2&C2&D2&E2) & G2).
assert (Hh : hand s2 = hand s) by (unfold hand, nareas; rewrite D2, D1, E2, E1; reflexivity).
destruct rs.
- eapply lw_mono; [|apply open_area_lw]. intros [ok s3] H3. cbn beta iota delta [fst snd] in H3 |- *. destruct H3 as (A3&B3&C3&D3&E3).
split; [congruence|]. split; [congruence|]. split; [eapply regs_le_trans; [exact C1 | eapply regs_le_trans; [exact C2|exact C3]]|].
split; [|exact E3]. intros H0. rewrite D3 by congruence. exact Hh.
- apply lw_ret. ms. split; [congruence|]. split; [congruence|]. split; [eapply regs_le_trans; eauto|].
split; [intros _; exact Hh|]. intros HG. specialize (G2 HG). discriminate.
Qed.

Definition ig_st (m : sptr) (sc cnt aidx maplen : Z) (mem : sptr) (sl : slotst) (s : astate) : astate :=
set_head_st (HActive sc) (Some m)
(upd_meta m (with_links (MUsed (new_am mem sc cnt aidx maplen sl)) (Some m) (Some m))
(upd_meta m (MUsed (new_am mem sc cnt aidx maplen sl)) (set_usage (zset sc (usage_of s sc + cnt) (st_usage s)) s))).
Lemma install_group_lw F m sc cnt aidx maplen mem sl s : active_hd s sc = None ->
lw F (fun r => snd r = ig_st m sc cnt aidx maplen mem sl s) (install_group m sc cnt aidx maplen mem sl s).
Proof.
intros Hhd. unfold install_group. apply lw_bind, lw_get. ms. apply lw_bind. unfold set_usage_of. apply lw_modify. ms.
apply lw_bind, lw_setm. ms. unfold queue. apply lw_bind, lw_get_links. intros x Hx. rewrite MT_upd_same in Hx. injection Hx as <-. ms.
apply lw_bind, lw_massert. intros _. ms. apply lw_bind, lw_get_head. ms.
unfold active_hd in Hhd.
match goal with |- context [nth (Z.to_nat sc) (st_active ?st) None] => change (nth (Z.to_nat sc) (st_active st) None) with (nth (Z.to_nat sc) (st_active s) None) end.
rewrite Hhd. ms.
apply lw_bind, lw_set_links. intros x Hx. rewrite MT_upd_same in Hx. injection Hx as <-. ms. apply lw_set_head. reflexivity.
Qed.
Definition NMr (s s' : astate) : Prop :=
st_metas s' = st_metas s /\ st_regions s' = st_regions s /\ hand s' = hand s /\ st_free_meta_head s' = st_free_meta_head s.
Lemma step_seq_lw F s : lw F (fun r => NMr s (snd r)) (step_seq s).
Proof. unfold step_seq. apply lw_modify. ms. destruct (st_seq s =? 255); repeat split; reflexivity. Qed.
Lemma account_bounce_lw F sc s : lw F (fun r => NMr s (snd r)) (account_bounce sc s).
Proof.
unfold account_bounce. destruct (bounce_idx sc); [apply lw_modify; ms | apply lw_ret; ms; repeat split; reflexivity].
match goal with |- context [if ?c then _ else _] => destruct c end; repeat split; reflexivity.
Qed.
Lemma len_keys s : length (st_metas s) = length (keys s).
Proof. unfold keys. rewrite length_map. reflexivity. Qed.

Lemma alloc_meta_spec' X R U s (Q : option sptr * astate -> Prop) :
Inv X R U s ->
(forall s', Inv X R U s' -> am_frame s s' -> (forall g am, usedX X s' g am <-> usedX X s g am) -> ub_same s s' ->
regs_le s s' -> hk s' = hk s -> Q (None, s')) ->
(forall m s', Inv (m :: X) R U s' -> memb m X = false -> In m (keys s') ->
(MT s' m = Some MRaw \/ MT s' m = Some (MFree None None)) -> am_frame s s' ->
(forall g am, usedX (m :: X) s' g am <-> usedX X s g am) -> ub_same s s' -> regs_le s s' -> hk s' = hk s -> Q (Some m, s')) ->
itok (alloc_meta s) Q.
Proof.
intros HI HQn HQs.
unfold alloc_meta. mbinds. apply itok_modify. msimp.
set (s0 := set_init_done true s).
assert (HI0 : Inv X R U s0) by (apply Inv_set_init_done; exact HI).
assert (Fr0 : am_frame s s0) by (repeat split; try reflexivity; intros k rg Hk _; exact Hk).
assert (Hinit0 : st_init_done s0 = true) by reflexivity.
mbinds. eapply dequeue_head_free_spec; [exact HI0 | |].
-
intros Hfh Hnofree. msimp. mbinds. apply itok_get. msimp.
assert (TAKE : forall s1, Inv X R U s1 -> am_frame s s1 -> st_metas s1 = st_metas s -> 0 < st_avail_meta_count s1 ->
regs_le s s1 -> hand s1 = hand s ->
itok ((s2 <- get ;;
put (set_avail_meta (padd (st_avail_meta s2) META_SIZE) (set_avail_meta_count (st_avail_meta_count s2 - 1) s2)) ;;
setslot (st_avail_meta s2) MRaw ;; ret (Some (st_avail_meta s2))) s1) Q).
{ intros s1 HI1 Fr1 Em1 Hc1 RL1 Hh1.
mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_setslot'. msimp. apply itok_ret.
destruct (take_slot_Inv X R U s1 HI1 Hc1) as (Hfresh & NX & HI2 & EU2).
apply HQs.
+ exact HI2.
+ exact NX.
+ rewrite keys_upd_notIn by exact Hfresh. apply in_app_iff. right. left. reflexivity.
+ left. apply MT_upd_same.
+ eapply am_frame_trans; [exact Fr1|]. repeat split; try reflexivity. intros k rg Hk _. exact Hk.
+ intros g am. rewrite EU2. unfold usedX, MTX, MT. rewrite Em1. reflexivity.
+ eapply ub_same_trans; [| apply ub_same_upd_notIn; [exact Hfresh | reflexivity]]. apply ub_same_metas. exact Em1.
+ exact RL1.
 + unfold hk. rewrite len_upd_notIn by exact Hfresh. cbn [st_metas set_avail_meta set_avail_meta_count]. rewrite Em1.
unfold hand, nareas in *. cbn [st_areas st_avail_meta_count upd_meta set_metas set_avail_meta set_avail_meta_count]. lia. }
destruct (0 <? st_avail_meta_count s0) eqn:Ec.
+ apply Z.ltb_lt in Ec. mbinds. apply itok_ret. msimp. cbn [negb].
apply TAKE; [exact HI0 | exact Fr0 | reflexivity | exact Ec | apply regs_le_eq; reflexivity | reflexivity].
+ apply Z.ltb_ge in Ec. pose proof (inv_keys HI0) as (_ & _ & _ & _ & Krange).
assert (Hm0 : st_avail_meta_count s0 = 0) by lia.
apply itok_bind.
apply (itok_lw _ _ _ (new_area_lw FA s0)).
eapply new_area_spec; [exact HI0 | exact Hm0 | exact Hinit0 |].
intros ok s1 HI1 Fr1 Em1 Hi1 Hok (_ & _ & RL1 & Hh1 & _). cbn [fst snd] in RL1, Hh1. msimp. destruct ok; cbn [negb].
* apply TAKE; [exact HI1 | eapply am_frame_trans; [exact Fr0 | exact Fr1] | rewrite Em1; reflexivity | apply Hok; reflexivity
| exact RL1 | rewrite (Hh1 Hm0); reflexivity].
* apply itok_ret. apply HQn; [exact HI1 | eapply am_frame_trans; [exact Fr0 | exact Fr1] | | | exact RL1 |].
-- intros g am. unfold usedX, MTX, MT. rewrite Em1. reflexivity.
-- apply ub_same_metas. rewrite Em1. reflexivity.
-- unfold hk. rewrite Em1, (Hh1 Hm0). reflexivity.
-
intros m s' HI' NX Mm Sb Ea EU UB. msimp. apply itok_ret.
pose proof Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
apply HQs.
+ exact HI'.
+ exact NX.
+ eapply MT_Some_In_keys. exact Mm.
+ right. exact Mm.
+ eapply am_frame_trans; [exact Fr0|].
repeat split; try assumption.
* intros k rg Hk _. unfold region_of in *. rewrite E15. exact Hk.
* rewrite E15. lia.
+ intros g am. rewrite EU. reflexivity.
+ eapply ub_same_trans; [apply ub_same_metas; reflexivity | exact UB].
+ apply regs_le_eq. exact E15.
+ unfold hk, hand, nareas. rewrite E16, E4, !len_keys, E17. reflexivity.
Qed.

Lemma MT_ig m sc cnt aidx maplen mem sl s q :
MT (ig_st m sc cnt aidx maplen mem sl s) q =
if sptr_eqb q m then Some (MUsed (am_set_links (Some m) (Some m) (new_am mem sc cnt aidx maplen sl))) else MT s q.
Proof.
unfold ig_st, set_head_st. change (MT (set_active ?l ?st) q) with (MT st q). rewrite !MT_upd.
destruct (sptr_eqb q m); reflexivity.
Qed.
Lemma len_ig m sc cnt aidx maplen mem sl s : In m (keys s) ->
length (st_metas (ig_st m sc cnt aidx maplen mem sl s)) = length (st_metas s).
Proof.
intros H. unfold ig_st, set_head_st. change (st_metas (set_active ?l ?st)) with (st_metas st).
rewrite len_upd_In by (rewrite keys_upd_In; exact H). rewrite len_upd_In by exact H. reflexivity.
Qed.
Lemma ig_frameless m sc cnt aidx maplen mem sl i : ss_fr sl = None ->
ss_fr (nth_slot (am_set_links (Some m) (Some m) (new_am mem sc cnt aidx maplen sl)) i) = None.
Proof. intros H. unfold nth_slot. cbn [am_slots am_set_links new_am]. rewrite nth_repeat'. destruct (Nat.ltb _ _); [exact H | reflexivity]. Qed.

Definition slot_post' (PS PG PN : Prop) X U s sc req (r : Z * astate) : Prop :=
slot_post X U s sc req r /\
((fst r = -1 /\ WI PS PG PN X None K0 (snd r)) \/
(0 <= fst r /\ exists g, active_hd (snd r) sc = Some g /\ WI PS PG PN X (Some (g, fst r)) K0 (snd r))).
Definition group_post' (PS PG PN : Prop) X U s sc req (r : option sptr * astate) : Prop :=
group_post X U s sc req r /\
match fst r with None => WI PS PG PN X None K0 (snd r) | Some m => WI PS PG PN X (Some (m, 0)) K0 (snd r) end.

Theorem alloc_mutual' (PS PG PN : Prop) fuel :
(forall X U s sc req (Q : Z * astate -> Prop),
Inv X None U s -> WI PS PG PN X None K0 s -> 0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc -> (need sc <= fuel)%nat ->
(forall r, slot_post' PS PG PN X U s sc req r -> Q r) -> itok (alloc_slot fuel sc req s) Q) /\
(forall X U s sc req (Q : option sptr * astate -> Prop),
Inv X None U s -> WI PS PG PN X None K0 s -> 0 <= sc < 48 -> 0 <= req -> req + IB <= class_size sc -> (need sc <= S fuel)%nat ->
active_hd s sc = None ->
(forall r, group_post' PS PG PN X U s sc req r -> Q r) -> itok (alloc_group fuel sc req s) Q).
Proof.
induction fuel as [|f [IHs IHg]].
{ split; intros X U s sc req Q HI HW Hsc Hreq Hfit Hf; pose proof (need_ge2 sc); lia. }
split.
-
intros X U s sc req Q HI HW Hsc Hreq Hfit Hf HQ.
cbn fix beta iota delta [alloc_slot]. mbinds.
apply (itok_lw _ _ _ (try_avail_RT FA sc s)).
eapply try_avail_spec; [exact HI | exact Hsc | |].
+ intros s1 HI1 Hhd1 EH1 UB1 RT1. cbn [snd] in RT1. msimp. cbn [Z.eqb negb].
destruct (RT_corr X s s1 RT1) as (C1 & RL1 & HK1).
pose proof (WI_corr _ _ _ _ _ _ _ _ _ C1 RL1 HK1 HW) as HW1.
mbinds.
eapply IHg; [exact HI1 | exact HW1 | exact Hsc | exact Hreq | exact Hfit | exact Hf | exact Hhd1 |].
intros [og s2] [[HB [UB2 Hpost]] HW2]. msimp. cbn [fst snd] in HB, UB2, Hpost, HW2.
assert (HB' : heads_below s s2 sc) by (intros c Hc; rewrite (HB c Hc); apply EH1; lia).
assert (UB' : ub_same s s2) by (eapply ub_same_trans; [exact UB1 | exact UB2]).
destruct og as [g|].
* apply itok_ret. apply HQ. split.
{ unfold slot_post; cbn [fst snd]; split; [exact HB'|]. split; [exact UB'|]. right. cbn [fst snd]. split; [lia|].
destruct Hpost as (am & H1 & H2 & H3 & H4 & H5 & H6). exists g, am. repeat (split; [assumption|]). exact H6. }
right. cbn [fst snd]. split; [lia|]. destruct Hpost as (am & H1 & H2 & _). exists g. split; [exact H2 | exact HW2].
* apply itok_ret. apply HQ. split.
{ unfold slot_post; cbn [fst snd]; split; [exact HB'|]. split; [exact UB'|]. left. split; [reflexivity | exact Hpost]. }
left. cbn [fst snd]. split; [reflexivity | exact HW2].
+ intros first s1 (Hnz & g & am & HI1 & Hhd1 & U1 & Sc1 & Str1 & Hidx & EH1 & UB1) RT1. cbn [snd] in RT1. msimp.
destruct (RT_corr X s s1 RT1) as (C1 & RL1 & HK1).
pose proof (WI_corr _ _ _ _ _ _ _ _ _ C1 RL1 HK1 HW) as HW1.
destruct (first =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|]. cbn [negb].
apply itok_ret. apply HQ. split.
{ unfold slot_post; cbn [fst snd]; split; [intros c Hc; apply EH1; lia|]. split; [exact UB1|]. right. cbn [fst snd].
split; [lia|]. exists g, am. repeat (split; [assumption|]). split; [lia | lia]. }
right. cbn [fst snd]. split; [lia|]. exists g. split; [exact Hhd1 | apply WI_R; exact HW1].
-
intros X U s sc req Q HI HW Hsc Hreq Hfit Hf Hhd HQ.
pose proof (class_size_bounds sc Hsc) as [S16 Smax].
cbn fix beta iota delta [alloc_group]. mbinds.
eapply alloc_meta_spec'; [exact HI | |].
{ intros s1 HI1 Fr1 EU1 UB1 RL1 HK1. msimp. apply itok_ret. apply HQ. split.
{ unfold group_post, slot_post; cbn [fst snd]; split; [|split; [exact UB1 | exact HI1]].
intros c Hc. destruct Fr1 as (EA & _). unfold active_hd. rewrite EA. reflexivity. }
cbn [fst snd]. eapply WI_corr; [apply corr_eqv; exact EU1 | exact RL1 | exact HK1 | exact HW]. }
intros m s1 HI1 NX Km Mm Fr1 EU1 UB1 RL1 HK1. msimp. mbinds. apply itok_get. msimp. cbn zeta.
assert (HW1 : WI PS PG PN (m :: X) None K0 s1) by (eapply WI_corr; [apply corr_eqv; exact EU1 | exact RL1 | exact HK1 | exact HW]).
pose proof Fr1 as (EA1 & EUs1 & _ & Len1 & Emc1).
assert (Hhd1 : active_hd s1 sc = None) by (unfold active_hd; rewrite EA1; exact Hhd).
pose proof (initial_cnt_facts sc (usage_of s1 sc) Hsc) as (Hc0 & Hc0s & Hc026).
set (cnt0 := initial_cnt sc (usage_of s1 sc)) in *.
assert (FRESH : forall q a, usedX (m :: X) s1 q a -> (prid (am_mem a) < length (st_regions s1))%nat).
{ intros q a Hu. apply EU1 in Hu. pose proof (used_group_prid_lt _ _ _ _ q a HI Hu). lia. }
destruct (PGSZ / 2 <? class_size sc * cnt0 + UNIT) eqn:Ebr.
+
set (plan := mmap_plan s1 sc req cnt0 (usage_of s1 sc)).
pose proof (mmap_plan_len_bound s1 sc req cnt0 (usage_of s1 sc) ltac:(unfold IB in Hfit; lia) ltac:(lia)) as PB.
destruct plan as [cnt needed] eqn:Ep. subst plan. cbn [fst snd].
rewrite Ep in PB. cbn [snd] in PB.
pose proof (mmap_plan_facts s1 sc req cnt0 (usage_of s1 sc) cnt needed Hsc Hc0 Hc0s Hreq Hfit Hc026 Ep)
as (Hcnt & Hcs & Hc26 & Nmod & N4096 & Nmax & Nfit & Nreq & Npr).
mbinds. apply (itok_lw _ _ _ (account_bounce_lw FA sc s1)).
eapply account_bounce_spec; [exact HI1|]. intros s2 HI2 (Em2 & Ea2 & Er2 & Eu2 & Ec2 & _) NM2. cbn [snd] in NM2. msimp.
mbinds. apply (itok_lw _ _ _ (step_seq_lw FA s2)).
eapply step_seq_spec; [exact HI2|]. intros s3 HI3 (Em3 & Ea3 & Er3 & Eu3 & Ec3 & _) NM3. cbn [snd] in NM3. msimp.
assert (HW3 : WI PS PG PN (m :: X) None K0 s3).
{ destruct NM2 as (A2&B2&C2&_). destruct NM3 as (A3&B3&C3&_).
apply (WI_same _ _ _ _ _ _ s2 s3 A3 B3 C3). apply (WI_same _ _ _ _ _ _ s1 s2 A2 B2 C2). exact HW1. }
mbinds. apply itok_ask; [cbn; unfold PGSZ in N4096; clear - N4096 Nmax; lia|]. intros z _. msimp.
assert (EU3 : forall q a, usedX (m :: X) s3 q a <-> usedX (m :: X) s1 q a).
{ intros q a. unfold usedX, MTX, MT. rewrite Em3, Em2. tauto. }
destruct (z =? 0); cbn [negb].
*
mbinds. eapply free_meta_spec; [exact HI3 | left; reflexivity |]. intros s4 HI4 Sb4 Ea4 EU4 UB4. msimp.
apply itok_ret. apply HQ. split.
{ unfold group_post, slot_post; cbn [fst snd]; split; [|split].
-- intros c Hc. unfold active_hd. rewrite Ea4, Ea3, Ea2, EA1. reflexivity.
-- eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [|exact UB4].
apply ub_same_metas. rewrite Em3, Em2. reflexivity.
-- cbn [fst snd]. rewrite (remove_head_notin m X NX) in HI4. exact HI4. }
cbn [fst snd]. rewrite (remove_head_notin m X NX) in EU4.
pose proof Sb4 as (_&_&_&F4&_&_&_&_&_&_&_&_&_&_&F15&F16&F17).
eapply WI_corr; [apply corr_eqv; exact EU4 | apply regs_le_eq; exact F15 | | exact HW3].
unfold hk, hand, nareas. rewrite F16, F4, !len_keys, F17. reflexivity.
*
rewrite (page_round_fixed needed Nmod) in PB |- *.
mbinds. eapply new_region_spec; [exact HI3 | | reflexivity | unfold PGSZ in N4096; lia]. intros s4 HI4 Es4. msimp.
mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp.
set (r := length (st_regions s3)).
set (s5 := set_mmap_counter (Z.land (st_mmap_counter s4 + 1) (2 ^ 32 - 1)) s4).
pose proof (inv_ctx HI4) as (_&_&_&_&_&_&_&_&C9&_).
assert (HI5 : Inv (m :: X) None U s5) by (apply Inv_set_mmap_counter; [exact HI4 | apply land32_range; lia]).
assert (EU5 : forall q a, usedX (m :: X) s5 q a <-> usedX (m :: X) s1 q a).
{ intros q a. rewrite <- EU3. unfold usedX, MTX, MT. subst s5 s4. cbn. tauto. }
assert (Hr5 : region_of s5 r = Some (mkRegion RkMap needed [] true)).
{ subst s5 s4 r. unfold region_of. cbn [st_regions set_mmap_counter set_regions]. apply region_of_app_new. }
set (aidx := if (if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1) <? 0 then 0
else if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1).
assert (Haidx : 0 <= aidx <= cnt - 1).
{ subst aidx. destruct (cnt - 1 <? (4096 - UNIT) / class_size sc - 1) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
(destruct (_ <? 0) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]); lia. }
assert (Hml : 1 <= needed / 4096).
{ apply Z.div_le_lower_bound; unfold PGSZ in *; lia. }
assert (Hml' : needed / 4096 * 4096 = needed).
{ pose proof (Z_div_mod_eq_full needed 4096). unfold PGSZ in Nmod. lia. }
assert (Hhd5 : active_hd s5 sc = None).
{ unfold active_hd. subst s5 s4. cbn [st_active set_mmap_counter set_regions]. rewrite Ea3, Ea2. exact Hhd1. }
assert (HW5 : WI PS PG PN (m :: X) None (fun k => k = r) s5).
{ subst s5. rewrite Es4. apply (WI_same _ _ _ _ _ _ (set_regions (st_regions s3 ++ [mkRegion RkMap needed [] true]) s3));
[reflexivity | reflexivity | reflexivity |]. apply WI_new_region. exact HW3. }
assert (Km5 : In m (keys s5)).
{ apply MT_Some_In_keys with (x := match MT s1 m with Some x => x | None => MRaw end).
unfold MT in *. subst s5. rewrite Es4. cbn [st_metas set_mmap_counter set_regions]. rewrite Em3, Em2.
destruct Mm as [M|M]; rewrite M; reflexivity. }
mbinds.
apply (itok_lw _ _ _ (install_group_lw FA m sc cnt aidx (needed / 4096) (SP r 0) slot_zero s5 Hhd5)).
eapply (install_group_spec X U s5 m sc cnt aidx (needed / 4096) (SP r 0) slot_zero).
-- exact HI5.
-- exact NX.
-- exact Hsc.
-- exact Hcnt.
-- exact Haidx.
-- lia.
-- exact Hhd5.
-- left. split; [reflexivity | lia].
--
right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride.
split; [exact Hsc|]. split; [|split].
++ intros Hlt. destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
** apply andb_prop in E as [E _]. apply Z.eqb_eq in E. split; [exact E|]. rewrite new_am_allocated by lia. reflexivity.
** lia.
++ intros H26. right. specialize (Hc26 H26). lia.
++ destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
** apply andb_prop in E as [E _]. apply Z.eqb_eq in E. rewrite E. unfold UNIT. lia.
** replace (cnt - 1 + 1) with cnt by lia. exact Hcs.
--
intros _. exists r, (mkRegion RkMap needed [] true). cbn [am_mem am_maplen am_last new_am rg_kind rg_live rg_len].
split; [reflexivity|]. split; [exact Hr5|]. split; [reflexivity|]. split; [reflexivity|].
rewrite new_am_stride. unfold PGSZ. split; [lia|]. split.
{ destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)) eqn:E.
++ apply andb_prop in E as [E _]. apply Z.eqb_eq in E. rewrite E. unfold UNIT. lia.
++ destruct (Z.eq_dec cnt 1) as [->|Hne1].
{ exfalso. cbn [Z.sub Z.eqb] in E. destruct (needed / 4096 =? 0) eqn:E2; [apply Z.eqb_eq in E2; lia | discriminate]. }
replace (cnt - 1 + 1) with cnt by lia. specialize (Nfit ltac:(lia)). lia. }
cbn [am_sc new_am]. intros Hl0 _. specialize (Npr ltac:(lia)). unfold PGSZ in Npr |- *. lia.
-- intros H0. lia.
-- intros q a Hu Hp. exfalso. apply EU5 in Hu. pose proof (FRESH q a Hu). cbn [prid] in Hp. rewrite <- Er2, <- Er3 in H. subst r. clear - H Hp. lia.
-- intros _ q a Hu _ Hp. apply EU5 in Hu. pose proof (FRESH q a Hu). cbn [prid] in Hp. rewrite <- Er2, <- Er3 in H. subst r. clear - H Hp. lia.
-- intros s6 HI6 Hhd6 U6 EH6 Er6 Ec6 UB6 Es6. cbn [snd] in Es6. msimp. apply itok_ret. apply HQ. split.
{ unfold group_post, slot_post; cbn [fst snd]; split; [|split].
++ intros c Hc. rewrite (EH6 c ltac:(lia) ltac:(lia)). unfold active_hd. subst s5 s4. cbn [st_active set_mmap_counter set_regions].
rewrite Ea3, Ea2, EA1. reflexivity.
++ eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [|exact UB6].
apply ub_same_metas. subst s5 s4. cbn. rewrite Em3, Em2. reflexivity.
++ cbn [fst snd]. eexists. split; [exact HI6|]. split; [exact Hhd6|]. split; [exact U6|].
pose proof (links_fields (Some m) (Some m) (new_am (SP r 0) sc cnt aidx (needed / 4096) slot_zero)) as (_ & Ll & Ls & _).
rewrite Ls, Ll. cbn [am_sc am_last new_am]. split; [reflexivity|]. split; [|lia].
rewrite (strip_stride _ (new_am (SP r 0) sc cnt aidx (needed / 4096) slot_zero)) by (unfold strip; reflexivity).
rewrite new_am_stride. destruct ((cnt - 1 =? 0) && negb (needed / 4096 =? 0)); unfold UNIT, IB in *; lia. }
cbn [fst snd]. rewrite Es6.
apply (WI_install PS PG PN X (fun k => k = r) s5 _ m (am_set_links (Some m) (Some m) (new_am (SP r 0) sc cnt aidx (needed / 4096) slot_zero)) HW5 NX).
++ rewrite MT_ig, sptr_eqb_refl. reflexivity.
++ intros q Hq. rewrite MT_ig. apply sptr_eqb_neq in Hq. rewrite Hq. reflexivity.
++ apply len_ig. exact Km5.
++ reflexivity.
++ intros k. reflexivity.
++ intros i. apply ig_frameless. reflexivity.
++ intros k ->. cbn [am_maplen am_mem am_set_links new_am prid]. split; [clear - Hml; lia | reflexivity].
++ intros _ _ _. cbn [am_maplen am_set_links new_am]. clear - Hml' PB. unfold PGSZ. lia.
++ cbn [am_maplen am_set_links new_am]. intros H0. clear - Hml H0. lia.
+
apply Z.ltb_ge in Ebr.
pose proof (nested_facts sc cnt0 Hsc ltac:(lia) Hc026 Ebr) as NF. cbv zeta in NF.
destruct NF as (H23 & Hc2 & Htot & Hj & Hj48 & Hjfit & Hjlt).
set (total := UNIT + cnt0 * class_size sc - IB) in *. set (j := size_to_class total) in *.
mbinds.
eapply (IHs (m :: X) U s1 j total); [exact HI1 | exact HW1 | exact Hj48 | lia | exact Hjfit | |].
{ pose proof (need_nested sc j H23 ltac:(lia)). lia. }
intros [idx s2] [[HB2 [UB2 Hpost]] HW2]. msimp. cbn [fst snd] in HB2, UB2, Hpost, HW2.
destruct (idx <? 0) eqn:Eneg.
*
apply Z.ltb_lt in Eneg. destruct Hpost as [[_ HI2] | [Hge _]]; [|cbn [fst] in Hge; lia]. cbn [snd] in HI2.
destruct HW2 as [[_ HW2] | [Hge _]]; [|lia].
mbinds. eapply free_meta_spec; [exact HI2 | left; reflexivity |]. intros s3 HI3 Sb3 Ea3 EU3 UB3. msimp.
apply itok_ret. apply HQ. split.
{ unfold group_post, slot_post; cbn [fst snd]; split; [|split].
-- intros c Hc. pose proof (HB2 c ltac:(lia)) as E. unfold active_hd in E |- *. rewrite Ea3, E, EA1. reflexivity.
-- eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [exact UB2 | exact UB3].
-- cbn [fst snd]. rewrite (remove_head_notin m X NX) in HI3. exact HI3. }
cbn [fst snd]. rewrite (remove_head_notin m X NX) in EU3.
pose proof Sb3 as (_&_&_&F4&_&_&_&_&_&_&_&_&_&_&F15&F16&F17).
eapply WI_corr; [apply corr_eqv; exact EU3 | apply regs_le_eq; exact F15 | | exact HW2].
unfold hk, hand, nareas. rewrite F16, F4, !len_keys, F17. reflexivity.
* apply Z.ltb_ge in Eneg. destruct Hpost as [[Hm1 _] | [_ (g & am & HI2 & Hhd2 & U2 & Sc2 & Str2 & Hidx2)]]; [cbn [fst] in Hm1; lia|].
cbn [fst snd] in HI2, Hhd2, U2, Hidx2, HB2.
destruct HW2 as [[Hm1 _] | [_ (g' & Hhd2' & HW2)]]; [lia|]. rewrite Hhd2 in Hhd2'. injection Hhd2' as <-.
mbinds. apply itok_get_head. msimp. change (nth (Z.to_nat j) (st_active s2) None) with (active_hd s2 j). rewrite Hhd2. msimp.
pose proof (inv_groups HI2 g am U2) as G2. pose proof G2 as ((_ & _ & Glen & _) & Gml & _ & Gcl & _).
assert (Hstr : stride_of am = class_size j).
{ destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [lia|]. specialize (C26 ltac:(lia)).
unfold stride_of. rewrite Sc2. destruct C26 as [C|C]; [rewrite C|].
- destruct (am_last am =? 0); reflexivity.
- destruct (am_last am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
mbinds. eapply itok_getm; [exact (proj1 (usedX_MT _ _ _ _ U2))|]. msimp.
mbinds. apply itok_mcheck; [rewrite Hstr; apply Z.eqb_refl|]. msimp.
mbinds. apply itok_get. msimp.
pose proof (inv_ctx HI2) as (_&_&_&_&_&_&_&_&C9&_).
mbinds. eapply (enframe_spec (m :: X) U s2 g idx (class_size j - IB) (st_mmap_counter s2) FGroup am);
[exact HI2 | exact U2 | pose proof (class_size_bounds j Hj48); unfold IB; lia | rewrite Hstr; lia | lia | intros _; rewrite Hstr; reflexivity | intros H63; exfalso; lia
| intros _ _; rewrite Sc2; exact Hhd2 |].
intros off s3 hdr Hoff Hofit Hoff0 Es3 HI3. msimp. specialize (Hoff0 eq_refl). subst off. rewrite Z.mul_0_r, padd_0.
set (am' := upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) in Es3.
pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold am' in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
assert (U3 : usedX (m :: X) s3 g am').
{ rewrite Es3. apply usedX_upd. left. pose proof (usedX_MT _ _ _ _ U2) as [_ NXg]. auto. }
assert (Hext1 : group_extent (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk) = total).
{ unfold group_extent. rewrite new_am_stride. cbn [am_last new_am Z.eqb andb negb].
destruct (cnt0 - 1 =? 0); cbn [andb]; subst total; (replace (cnt0 - 1 + 1) with cnt0 by lia); lia. }
assert (Hhd3 : active_hd s3 sc = None).
{ rewrite Es3. unfold active_hd. cbn. pose proof (HB2 sc ltac:(lia)) as E. unfold active_hd in E. rewrite E, EA1. exact Hhd. }
assert (Hgm : g <> m).
{ intros ->. pose proof (usedX_MT _ _ _ _ U2) as [_ NXg]. rewrite memb_cons, sptr_eqb_refl in NXg. discriminate. }
assert (Km3 : In m (keys s3)).
{ rewrite Es3, keys_upd_In by (eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U2))).
pose proof (inv_X HI2 m (or_introl eq_refl)) as [K _]. exact K. }
mbinds.
apply (itok_lw _ _ _ (install_group_lw FA m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk s3 Hhd3)).
eapply (install_group_spec X U s3 m sc cnt0 (cnt0 - 1) 0 (slot_start am idx) slot_junk).
-- exact HI3.
-- exact NX.
-- exact Hsc.
-- lia.
-- lia.
-- lia.
-- exact Hhd3.
-- right. split; reflexivity.
-- right. cbn [am_sc am_last am_maplen new_am]. rewrite new_am_stride. cbn [Z.eqb andb negb].
replace ((cnt0 - 1 =? 0) && false) with false by (destruct (cnt0 - 1 =? 0); reflexivity).
split; [exact Hsc|]. split; [lia|]. split; [auto|]. replace (cnt0 - 1 + 1) with cnt0 by lia. exact Hc0s.
-- intros H0. cbn in H0. lia.
-- intros _. exists g, am', idx, (mkFrame 0 (class_size j - IB) FGroup). rewrite Fl, Fsc, Fss. cbn [fr_kind fr_n].
split; [exact U3|]. split; [lia|]. split.
{ unfold am'. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. subst total. unfold UNIT, IB in *. nia.
-- intros q a Hu Hp. rewrite prid_slot_start in Hp. rewrite Es3 in Hu.
assert (Htot2 : 0 < total <= class_size j - IB).
{ pose proof Hjfit as HJ. subst total. unfold UNIT, IB in *. split; [nia | lia]. }
destruct (nested_lam (m :: X) U s2 g idx am hdr (class_size j - IB) q a sc cnt0 HI2 U2 ltac:(rewrite Hstr; reflexivity)
ltac:(rewrite Hext1; exact Htot2) Hu Hp) as [D | [I | P]].
++ left. exact D.
++ right; left. rewrite Es3. exact I.
++ right; right. split; [reflexivity|]. exact P.
-- intros H0. lia.
-- intros s4 HI4 Hhd4 U4 EH4 Er4 Ec4 UB4 Es4. cbn [snd] in Es4. msimp. apply itok_ret. apply HQ. split.
{ unfold group_post, slot_post; cbn [fst snd]; split; [|split].
++ intros c Hc. rewrite (EH4 c ltac:(lia) ltac:(lia)). rewrite Es3. unfold active_hd. cbn [st_active upd_meta set_metas].
pose proof (HB2 c ltac:(lia)) as E. unfold active_hd in E. rewrite E, EA1. reflexivity.
++ eapply ub_same_trans; [exact UB1|]. eapply ub_same_trans; [exact UB2|]. eapply ub_same_trans; [|exact UB4].
rewrite Es3. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact (proj1 (usedX_MT _ _ _ _ U2))|].
rewrite (proj1 (usedX_MT _ _ _ _ U2)). cbn. apply blocks_of_upd_slot_same; [lia | exact Glen |].
unfold slotst_block, slot_block. cbn. destruct (inv_reserved HI2 g idx eq_refl) as (am_ & U_ & _ & Hfr_ & _).
pose proof (usedX_fun _ _ _ _ _ U_ U2) as E_. rewrite E_ in Hfr_. rewrite Hfr_. reflexivity.
++ cbn [fst snd]. eexists. split; [exact HI4|]. split; [exact Hhd4|]. split; [exact U4|].
pose proof (links_fields (Some m) (Some m) (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk)) as (_ & Ll & Ls & _).
rewrite Ls, Ll. cbn [am_sc am_last new_am]. split; [reflexivity|]. split; [|lia].
rewrite (strip_stride _ (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk)) by (unfold strip; reflexivity).
rewrite new_am_stride. cbn [Z.eqb andb negb]. replace ((cnt0 - 1 =? 0) && false) with false by (destruct (cnt0 - 1 =? 0); reflexivity). lia. }
cbn [fst snd]. rewrite Es4.
apply (WI_nested PS PG PN X g idx am (mkSlot (Some hdr) (Some (mkFrame 0 (class_size j - IB) FGroup)))
(mkFrame 0 (class_size j - IB) FGroup) s2 _ m (am_set_links (Some m) (Some m) (new_am (slot_start am idx) sc cnt0 (cnt0 - 1) 0 slot_junk))
HW2 NX U2 ltac:(lia) Glen eq_refl ltac:(lia)).
++ rewrite MT_ig, sptr_eqb_refl. reflexivity.
++ rewrite MT_ig. apply sptr_eqb_neq in Hgm. rewrite Hgm. rewrite Es3. apply MT_upd_same.
++ intros q N1 N2. rewrite MT_ig. apply sptr_eqb_neq in N1. rewrite N1. rewrite Es3. apply MT_upd_other. exact N2.
++ rewrite len_ig by exact Km3. rewrite Es3. apply len_upd_In. eapply MT_Some_In_keys. exact (proj1 (usedX_MT _ _ _ _ U2)).
++ rewrite Es3. reflexivity.
++ intros k. rewrite Es3. reflexivity.
++ intros i. apply ig_frameless. reflexivity.
++ reflexivity.
++ reflexivity.
++ cbn [am_sc am_set_links new_am]. lia.
++ cbn [am_last am_set_links new_am]. lia.
Qed.

Lemma upd_region_lw F r f s :
lw F (fun x => snd x = set_regions (lupd (st_regions s) r (f (nth r (st_regions s) (mkRegion RkMap 0 [] false)))) s) (upd_region r f s).
Proof. unfold upd_region. apply lw_modify. reflexivity. Qed.
Lemma direct_frameless r ml i : ss_fr (nth_slot (direct_am r ml) i) = None.
Proof. unfold nth_slot, direct_am. cbn [am_slots]. destruct (Z.to_nat i) as [|[|k]]; reflexivity. Qed.

Theorem malloc_WI (PS PG PN : Prop) U s n (Q : option sptr * astate -> Prop) :
Inv [] None U s -> WI PS PG PN [] None K0 s -> 0 <= n ->
(forall r, Inv [] None U (snd r) -> WI PS PG PN [] None K0 (snd r) -> Q r) ->
itok (malloc n s) Q.
Proof.
intros HI HW Hn HQ. unfold malloc.
destruct (size_overflows n) eqn:Eov.
{ apply itok_ret. apply HQ; [exact HI | exact HW]. }
destruct (MMAP_THRESHOLD <=? n) eqn:Eth.
-
apply Z.leb_le in Eth.
mbinds. apply itok_ask; [cbn [req_ok]; unfold size_overflows in Eov; apply Z.leb_gt in Eov; unfold IB, UNIT; lia|]. intros z _. msimp.
destruct (z =? 0); cbn [negb].
{ apply itok_ret. apply HQ; [exact HI | exact HW]. }
mbinds. eapply new_region_spec; [exact HI | | reflexivity | pose proof (page_round_ge (n + IB + UNIT)); unfold IB, UNIT in *; lia]. intros s1 HI1 Es1. msimp.
set (r := length (st_regions s)).
assert (Hr1 : region_of s1 r = Some (mkRegion RkMap (page_round (n + IB + UNIT)) [] true)).
{ rewrite Es1. apply region_of_app_new. }
assert (EU1 : forall q a, usedX [] s1 q a <-> usedX [] s q a) by (intros; rewrite Es1; unfold usedX, MTX, MT; cbn; tauto).
assert (HW1 : WI PS PG PN [] None (fun k => k = r) s1) by (rewrite Es1; apply WI_new_region; exact HW).
mbinds. apply (itok_lw _ _ _ (step_seq_lw FA s1)).
eapply step_seq_spec; [exact HI1|]. intros s2 HI2 (Em2 & Ea2 & Er2 & Eu2 & Ec2 & _) NM2. cbn [snd] in NM2. msimp.
assert (HW2 : WI PS PG PN [] None (fun k => k = r) s2).
{ destruct NM2 as (A&B&C&_). exact (WI_same _ _ _ _ _ _ _ _ A B C HW1). }
assert (Hr2 : region_of s2 r = Some (mkRegion RkMap (page_round (n + IB + UNIT)) [] true)) by (unfold region_of in *; rewrite Er2; exact Hr1).
assert (EU2 : forall q a, usedX [] s2 q a <-> usedX [] s q a) by (intros; rewrite <- EU1; unfold usedX, MTX, MT; rewrite Em2; tauto).
assert (FRESH : forall q a, usedX [] s q a -> (prid (am_mem a) < r)%nat).
{ intros q a Hu. exact (used_group_prid_lt _ _ _ _ q a HI Hu). }
pose proof (page_round_ge (n + IB + UNIT)) as PR1. pose proof (page_round_mod (n + IB + UNIT)) as PR2.
mbinds. eapply alloc_meta_spec'; [exact HI2 | |].
+
intros s3 HI3 (Ea3 & Eu3 & Erg3 & Len3 & Ec3) EU3 UB3 RL3 HK3. msimp.
assert (HW3 : WI PS PG PN [] None (fun k => k = r) s3) by (eapply WI_corr; [apply corr_eqv; exact EU3 | exact RL3 | exact HK3 | exact HW2]).
mbinds. apply itok_ask.
{ cbn [req_ok]. exists (mkRegion RkMap (page_round (n + IB + UNIT)) [] true). cbn [rg_kind rg_live rg_len].
split; [apply Erg3; [exact Hr2 | reflexivity]|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [unfold IB, UNIT; lia|].
apply Forall_forall. intros [q a] Hin Hml. cbn [snd] in *.
apply (used_metas_iff s3 q a (proj1 (inv_keys HI3))) in Hin.
assert (Hu : usedX [] s q a) by (apply EU2, EU3; exact Hin).
pose proof (FRESH q a Hu). lia. }
intros z' _. msimp. mbinds.
apply (itok_lw _ _ _ (upd_region_lw FA r (fun rg => mkRegion RkMap (rg_len rg) [] false) s3)).
eapply upd_region_kill_spec; [exact HI3 | apply Erg3; [exact Hr2 | reflexivity] | reflexivity | |].
{ intros q a Hu _. apply EU3, EU2 in Hu. pose proof (FRESH q a Hu). lia. }
intros s4 HI4 Em4 _ Es4. cbn [snd] in Es4. msimp. apply itok_ret. apply HQ; [exact HI4 |]. cbn [snd].
rewrite Es4. apply WI_kill. exact HW3.
+
intros g s3 HI3 NX Kg Mg (Ea3 & Eu3 & Erg3 & Len3 & Ec3) EU3 UB3 RL3 HK3. msimp.
assert (HW3 : WI PS PG PN [g] None (fun k => k = r) s3) by (eapply WI_corr; [apply corr_eqv; exact EU3 | exact RL3 | exact HK3 | exact HW2]).
set (maplen := page_round (n + IB + UNIT) / 4096).
assert (Hml : page_round (n + IB + UNIT) = maplen * PGSZ).
{ subst maplen. rewrite Z.mul_comm. unfold PGSZ. pose proof (Z_div_mod_eq_full (page_round (n + IB + UNIT)) 4096). unfold PGSZ in PR2. lia. }
assert (Hml1 : 1 <= maplen) by (clear - Hml PR1 Eth; unfold MMAP_THRESHOLD, PGSZ, IB, UNIT in *; nia).
mbinds. change (mkAMeta None None (SP r 0) 0 0 0 63 (page_round (n + IB + UNIT) / 4096) 0 [slot_zero]) with (direct_am r maplen).
eapply install_direct_spec; [exact HI3 | exact NX | apply Erg3; [exact Hr2 | reflexivity] | reflexivity | reflexivity | exact Hml | exact Hml1 | |].
{ intros q a Hu Hp. apply EU3, EU2 in Hu. pose proof (FRESH q a Hu). lia. }
intros s4 Es4 HI4 U4 UB4. msimp.
assert (HW4 : WI PS PG PN [] (Some (g, 0)) K0 s4).
{ rewrite Es4. apply (WI_install PS PG PN [] (fun k => k = r) s3 _ g (direct_am r maplen) HW3 NX).
- apply MT_upd_same.
- intros q Hq. apply MT_upd_other. exact Hq.
- apply len_upd_In. exact Kg.
- reflexivity.
- intros k. reflexivity.
- intros i. apply direct_frameless.
- intros k ->. cbn [am_maplen am_mem direct_am prid]. split; [lia | reflexivity].
- intros _ _ H. cbn [am_sc direct_am] in H. lia.
- cbn [am_maplen direct_am]. intros H0. lia. }
mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp.
pose proof (inv_ctx HI4) as (_&_&_&_&_&_&_&_&C9&_).
set (s5 := set_mmap_counter _ s4).
assert (HI5 : Inv [] (Some (g, 0)) U s5) by (apply Inv_set_mmap_counter; [exact HI4 | apply land32_range; lia]).
assert (U5 : usedX [] s5 g (direct_am r maplen)) by (unfold usedX, MTX, MT in *; subst s5; cbn; exact U4).
assert (HW5 : WI PS PG PN [] (Some (g, 0)) K0 s5) by (apply (WI_same _ _ _ _ _ _ s4 s5); [reflexivity | reflexivity | reflexivity | exact HW4]).
assert (Hstr : stride_of (direct_am r maplen) = maplen * 4096 - UNIT).
{ unfold stride_of, direct_am. cbn [am_last am_maplen am_sc Z.eqb andb].
destruct (maplen =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
mbinds. eapply (enframe_spec [] U s5 g 0 n _ FUser (direct_am r maplen));
[exact HI5 | exact U5 | exact Hn | rewrite Hstr; unfold PGSZ, UNIT, IB in *; lia | apply land32_range; lia | discriminate | auto
| cbn; lia |].
intros off s6 hdr Hoff Hfit _ Es6 HI6. msimp. apply itok_ret. apply HQ; [exact HI6|]. cbn [snd]. rewrite Es6.
apply (WI_enframe PS PG PN [] g 0 (direct_am r maplen) (mkSlot (Some hdr) (Some (mkFrame off n FUser))) (mkFrame off n FUser) s5 HW5 U5);
[cbn [am_last direct_am]; lia | reflexivity | reflexivity | reflexivity |].
intros _ _ _ _. cbn [fr_n am_maplen direct_am]. rewrite <- Hml. pose proof (page_round_lt (n + IB + UNIT)). unfold IB, UNIT, PGSZ in *. lia.
-
apply Z.leb_gt in Eth.
pose proof (size_to_class_range n ltac:(lia)) as [Hsc0 Hfit0].
mbinds. apply itok_get. msimp. cbn zeta.
set (sc0 := size_to_class n) in *.
match goal with |- itok (bind (match nth (Z.to_nat ?c) _ _ with _ => _ end) _ _) _ => set (sc := c) end.
assert (Hsc : 0 <= sc < 48 /\ n + IB <= class_size sc).
{ subst sc. destruct (_ && (usage_of s sc0 =? 0)) eqn:E.
- apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [E E32].
apply andb_prop in E as [_ E4]. apply Z.ltb_lt in E32.
destruct (_ <=? 12); [|auto]. split; [lia|]. pose proof (class_size_mono sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
- auto. }
destruct Hsc as [Hsc Hfit]. clearbody sc.
change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc).
mbinds.
match goal with |- itok (?mm s) ?K =>
assert (FAST : itok (mm s) (fun r => match fst r with
| None => snd r = s
| Some (gm, idx) => exists am, Inv [] (Some (gm, idx)) U (snd r) /\ usedX [] (snd r) gm am /\
n + IB <= stride_of am /\ 0 <= idx <= am_last am /\ am_sc am = sc /\
active_hd (snd r) sc = Some gm /\ WI PS PG PN [] (Some (gm, idx)) K0 (snd r) end)) end.
{ destruct (active_hd s sc) as [gm|] eqn:Ehd; [|apply itok_ret; reflexivity].
destruct (head_used _ _ _ _ sc gm HI Hsc Ehd) as (am & Hu & Hsa).
pose proof (usedX_MT _ _ _ _ Hu) as [Mgm NXgm].
mbinds. eapply itok_getm; [exact Mgm|]. msimp.
destruct (am_avail am =? 0) eqn:Eav; [apply itok_ret; reflexivity|]. apply Z.eqb_neq in Eav.
mbinds. apply itok_setm'. msimp. apply itok_ret. cbn [fst snd].
rewrite <- Hsa in Hsc, Ehd.
destruct (take_bit_Inv [] U s gm am HI Hu Hsc Ehd Eav) as (Hk & Hfirst & Hbit & HI1).
pose proof (inv_groups HI gm am Hu) as ((_ & Gai & _) & _).
eexists. split; [exact HI1|]. split; [apply usedX_upd; left; auto|].
split.
{ pose proof (avail_bit_not_undersized [] None U s gm am (ctz32 (lowbit (am_avail am))) HI Hu Hsc ltac:(lia)
ltac:(rewrite Z.lor_spec, Hbit; reflexivity)) as Hus.
rewrite Hsa in Hus.
replace (stride_of (am_set_avail (am_avail am - lowbit (am_avail am)) am)) with (stride_of am) by (destruct am; reflexivity). lia. }
split; [cbn [am_last am_set_avail]; lia|]. split; [exact Hsa|]. split; [rewrite <- Hsa; exact Ehd|].
apply WI_R. destruct (RT_corr [] s _ (RT_setm s gm am (am_set_avail (am_avail am - lowbit (am_avail am)) am) Mgm ltac:(destruct am; reflexivity)))
as (C1 & RL1 & HK1).
exact (WI_corr _ _ _ _ _ _ _ _ _ C1 RL1 HK1 HW). }
revert FAST. apply itok_mono. intros [r s1] Hfast. cbn [fst snd] in Hfast. msimp.
mbinds.
match goal with |- itok (?mm s1) ?K =>
assert (SLOW : itok (mm s1) (fun r => match fst r with
| None => Inv [] None U (snd r) /\ WI PS PG PN [] None K0 (snd r)
| Some (gm, idx) => exists am, Inv [] (Some (gm, idx)) U (snd r) /\ usedX [] (snd r) gm am /\
n + IB <= stride_of am /\ 0 <= idx <= am_last am /\ am_sc am = sc /\
active_hd (snd r) sc = Some gm /\ WI PS PG PN [] (Some (gm, idx)) K0 (snd r) end)) end.
{ destruct r as [[gm idx]|].
- apply itok_ret. cbn [fst snd]. exact Hfast.
- subst s1. mbinds. destruct (alloc_mutual' PS PG PN NEST_FUEL) as [AS _].
eapply AS; [exact HI | exact HW | exact Hsc | exact Hn | exact Hfit | apply need_le_fuel; lia |].
intros [idx s2] [[_ [UB2 Hpost]] HW2]. cbn [fst snd] in Hpost, UB2, HW2. msimp.
destruct Hpost as [[-> HI2] | (Hidx & g & am & HI2 & Hhd2 & U2 & Sc2 & Str2 & Hlast)].
+ cbn. destruct HW2 as [[_ HW2] | [H _]]; [|lia]. split; [exact HI2 | exact HW2].
+ destruct (idx <? 0) eqn:E; [apply Z.ltb_lt in E; lia|].
destruct HW2 as [[H _] | [_ (g' & Hhd' & HW2)]]; [lia|]. rewrite Hhd2 in Hhd'. injection Hhd' as <-.
mbinds. apply itok_get_head. msimp. change (nth (Z.to_nat sc) (st_active s2) None) with (active_hd s2 sc). rewrite Hhd2.
apply itok_ret. cbn [fst snd]. exists am. repeat (split; [assumption|]). split; [lia | split; [exact Sc2 | split; [exact Hhd2 | exact HW2]]]. }
revert SLOW. apply itok_mono. intros [gi s2] Hslow. cbn [fst snd] in Hslow. msimp.
destruct gi as [[gm idx]|].
2:{ apply itok_ret. destruct Hslow as [HI2 HW2]. apply HQ; [exact HI2 | exact HW2]. }
destruct Hslow as (am & HI2 & U2 & Str2 & Hidx & Sc2 & Hhd2 & HW2).
mbinds. apply itok_get. msimp.
pose proof (inv_ctx HI2) as (_&_&_&_&_&_&_&_&C9&_).
assert (H63 : am_sc am <> 63) by lia.
mbinds. eapply (enframe_spec [] U s2 gm idx n (st_mmap_counter s2) FUser am);
[exact HI2 | exact U2 | exact Hn | unfold IB in *; lia | lia | discriminate | intros H; exfalso; exact (H63 H)
| intros _ _; rewrite Sc2; exact Hhd2 |].
intros off s3 hdr Hoff Hofit _ Es3 HI3. msimp. apply itok_ret. apply HQ; [exact HI3|]. cbn [snd]. rewrite Es3.
pose proof (inv_groups HI2 gm am U2) as ((_ & _ & Glen & _) & _).
apply (WI_enframe PS PG PN [] gm idx am (mkSlot (Some hdr) (Some (mkFrame off n FUser))) (mkFrame off n FUser) s2 HW2 U2 Hidx Glen eq_refl eq_refl).
intros _ _ H63' _. lia.
Qed.

Ltac bz := cbv beta iota zeta.
Definition nnraw (s s' : astate) : Prop := forall q, MT s' q = Some MRaw -> MT s q = Some MRaw.
Definition RC (s s' : astate) : Prop := nnraw s s' /\ hand s' = hand s /\ st_free_meta_head s' = st_free_meta_head s.
Definition RW (s s' : astate) : Prop := nnraw s s' /\ hand s' = hand s.
#[export] Instance RC_pre : PreR RC.
Proof.
split.
- intros s. split; [intros q H; exact H | split; reflexivity].
- intros a b c (A1&A2&A3) (B1&B2&B3). split; [intros q H; apply A1, B1, H | split; congruence].
Qed.
#[export] Instance RW_pre : PreR RW.
Proof.
split.
- intros s. split; [intros q H; exact H | reflexivity].
- intros a b c (A1&A2) (B1&B2). split; [intros q H; apply A1, B1, H | congruence].
Qed.
Lemma nnraw_upd s p x : x <> MRaw -> nnraw s (upd_meta p x s).
Proof.
intros Hx q H. rewrite MT_upd in H. destruct (sptr_eqb q p); [injection H as E; exfalso; exact (Hx E) | exact H].
Qed.
Lemma with_links_raw x pr nx : with_links x pr nx <> MRaw.
Proof. destruct x; discriminate. Qed.
#[export] Instance RC_sl : SLok RC.
Proof. intros s p x pr nx _. split; [apply nnraw_upd, with_links_raw | split; reflexivity]. Qed.
#[export] Instance RW_sl : SLok RW.
Proof. intros s p x pr nx _. split; [apply nnraw_upd, with_links_raw | reflexivity]. Qed.
Lemma RC_setm s p am : RC s (upd_meta p (MUsed am) s).
Proof. split; [apply nnraw_upd; discriminate | split; reflexivity]. Qed.
Lemma RC_head sc v s : RC s (set_head_st (HActive sc) v s).
Proof. split; [intros q H; exact H | split; reflexivity]. Qed.
Lemma RW_head h v s : RW s (set_head_st h v s).
Proof. destruct h; (split; [intros q H; exact H | reflexivity]). Qed.
Lemma RC_same s s' : st_metas s' = st_metas s -> hand s' = hand s -> st_free_meta_head s' = st_free_meta_head s -> RC s s'.
Proof. intros E1 E2 E3. split; [intros q H; unfold MT in *; rewrite E1 in H; exact H | split; assumption]. Qed.
Definition HR (s s' : astate) : Prop :=
(hand s' = hand s /\ (st_free_meta_head s = None -> st_free_meta_head s' = None)) \/ st_free_meta_head s' = None.
Lemma HR_trans a b c : HR a b -> HR b c -> HR a c.
Proof.
intros [[B1 B2]|B] [[C1 C2]|C]; try (right; assumption).
- left. split; [congruence | auto].
- right. auto.
Qed.
Lemma RC_HR s s' : RC s s' -> HR s s'.
Proof. intros (_ & E1 & E2). left. split; [exact E1 | rewrite E2; auto]. Qed.
Definition rawin (X : list sptr) (s : astate) : Prop := forall q, MT s q = Some MRaw -> In q X.
Lemma rawin_nn X s s' : rawin X s -> nnraw s s' -> rawin X s'.
Proof. intros H N q E. apply H, N, E. Qed.

Lemma decay_RC F sc : RP F RC (decay_bounces sc).
Proof.
unfold decay_bounces. destruct (bounce_idx sc); [|apply RP_ret].
apply RP_modify. intros s. bz.
match goal with |- context [if ?c then _ else _] => destruct c end; [apply pr_refl | apply RC_same; reflexivity].
Qed.
Lemma activate_RC F m : RP F RC (activate_group m).
Proof.
unfold activate_group. apply RP_bind; [apply RP_getm | intros am]. bz.
apply RP_bind; [apply RP_massert | intros _]. apply RP_bind; [apply RP_setm; intros; apply RC_setm | intros; apply RP_ret].
Qed.
Lemma try_avail_RC F sc : RP F RC (try_avail sc).
Proof.
unfold try_avail. apply RP_bind; [apply RP_get_head | intros [m0|]; bz; [|apply RP_ret]].
apply RP_bind; [apply RP_getm | intros am0]. bz.
destruct (negb (am_avail am0 =? 0)); [apply RP_bind; [apply RP_setm; intros; apply RC_setm | intros; apply RP_ret]|].
apply RP_bind.
{ destruct (am_freed am0 =? 0).
- apply RP_bind; [apply (RP_dequeue F RC); intros; apply RC_head | intros; apply RP_get_head].
- apply RP_bind; [apply RP_set_head; intros; apply RC_head | intros; apply RP_ret]. }
intros [m1|]; bz; [|apply RP_ret].
apply RP_bind; [apply RP_getm | intros am1].
apply RP_bind.
{ destruct (am_freed am1 =? ones (am_last am1)); [|apply RP_ret].
destruct (am_next am1); [|apply RP_fail]. apply RP_bind; [apply RP_set_head; intros; apply RC_head | intros; apply RP_ret]. }
intros m2. apply RP_bind; [apply RP_getm | intros am2]. bz.
apply RP_bind.
{ destruct (Z.land (am_freed am2) (ones (am_aidx am2)) =? 0); [|apply RP_ret].
destruct (negb (osptr_eqb (am_next am2) (Some m2))).
- destruct (am_next am2); [|apply RP_fail]. apply RP_bind; [apply RP_set_head; intros; apply RC_head | intros; apply RP_ret].
- apply RP_bind; [apply RP_setm; intros; apply RC_setm | intros; apply RP_ret]. }
intros m3. apply RP_bind; [apply activate_RC | intros mask].
apply RP_bind; [apply RP_massert | intros _]. apply RP_bind; [apply RP_getm | intros am3].
apply RP_bind; [apply decay_RC | intros _]. apply RP_bind; [apply RP_getm | intros am3'].
bz. apply RP_bind; [apply RP_setm; intros; apply RC_setm | intros; apply RP_ret].
Qed.
Lemma enframe_RC F g idx n ctr k : RP F RC (enframe g idx n ctr k).
Proof.
unfold enframe. apply RP_bind; [apply RP_getm | intros am]. apply RP_bind; [apply RP_mcheck | intros _]. bz.
apply RP_bind.
{ destruct ((stride_of am - IB - n) / UNIT =? 0); [apply RP_ret|].
destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|]; [apply RP_ret | apply RP_bind; [apply RP_askz | intros; apply RP_ret]]. }
intros off0. bz. apply RP_bind; [apply RP_massert | intros _]. bz.
apply RP_bind; [apply RP_setm; intros; apply RC_setm | intros; apply RP_ret].
Qed.
Lemma step_seq_RC F : RP F RC step_seq.
Proof. unfold step_seq. apply RP_modify. intros s. destruct (st_seq s =? 255); apply RC_same; reflexivity. Qed.
Lemma account_bounce_RC F sc : RP F RC (account_bounce sc).
Proof.
unfold account_bounce. destruct (bounce_idx sc); [|apply RP_ret]. apply RP_modify. intros s. bz.
match goal with |- context [if ?c then _ else _] => destruct c end; apply RC_same; reflexivity.
Qed.
Lemma new_region_RC F k len s : lw F (fun r => RC s (snd r)) (new_region k len s).
Proof. unfold new_region. apply lw_bind, lw_get. ms. apply lw_bind, lw_put. ms. apply lw_ret. ms. apply RC_same; reflexivity. Qed.
Lemma install_group_RCm F m sc cnt aidx maplen mem sl s :
lw F (fun r => RC s (snd r) /\ MT (snd r) m <> Some MRaw) (install_group m sc cnt aidx maplen mem sl s).
Proof.
unfold install_group. apply lw_bind, lw_get. ms. apply lw_bind. unfold set_usage_of. apply lw_modify. ms.
apply lw_bind, lw_setm. ms.
eapply lw_mono; [|apply (RP_queue F RC (HActive sc) m (fun s0 v => RC_head sc v s0))].
intros [u s3] H3. cbn [fst snd] in H3 |- *. split.
- eapply pr_trans; [|exact H3]. eapply pr_trans; [|apply RC_setm]. apply RC_same; reflexivity.
- intros E. destruct H3 as [N3 _]. apply N3 in E. rewrite MT_upd_same in E. discriminate.
Qed.
Lemma free_meta_lw F m s : lw F (fun r => forall q, MT (snd r) q = Some MRaw -> MT s q = Some MRaw /\ q <> m) (free_meta m s).
Proof.
unfold free_meta. apply lw_bind, lw_setslot. ms.
eapply lw_mono; [|apply (RP_queue F RW HFreeMeta m (fun s0 v => RW_head HFreeMeta v s0))].
intros [u s2] [N2 _] q E. cbn [snd] in E. apply N2 in E. rewrite MT_upd in E.
destruct (sptr_eqb q m) eqn:Eq; [discriminate|]. split; [exact E | apply sptr_eqb_neq; exact Eq].
Qed.
Lemma alloc_meta_lw F s : lw F (fun r => (forall q, MT (snd r) q = Some MRaw -> MT s q = Some MRaw \/ fst r = Some q) /\
HR s (snd r) /\ (G4 F -> fst r <> None)) (alloc_meta s).
Proof.
unfold alloc_meta. apply lw_bind, lw_modify. ms.
apply lw_bind. unfold dequeue_head. apply lw_bind, lw_get_head. ms.
change (st_free_meta_head (set_init_done true s)) with (st_free_meta_head s).
destruct (st_free_meta_head s) as [m0|] eqn:Eh.
- apply lw_bind. eapply lw_mono; [|apply (RP_dequeue F RW HFreeMeta m0 (fun s0 v => RW_head HFreeMeta v s0))].
intros [u s1] [N1 H1]. ms. apply lw_ret. ms. apply lw_ret. ms.
split; [intros q E; left; exact (N1 q E)|].
split; [left; split; [exact H1 | intros E; change (st_free_meta_head s = None) in E; rewrite Eh in E; discriminate] | intros _; discriminate].
- apply lw_ret. ms. apply lw_bind, lw_get. ms. apply lw_bind.
eapply lw_mono with (P := fun r => st_metas (snd r) = st_metas s /\ st_free_meta_head (snd r) = st_free_meta_head s /\ (G4 F -> fst r = true)).
+ intros [ok s1] (A1 & B1 & G1). cbn [fst snd] in A1, B1, G1. ms. destruct ok; cbn [negb].
* apply lw_bind, lw_get. ms. apply lw_bind, lw_put. ms. apply lw_bind, lw_setslot. ms. apply lw_ret. ms.
split; [|split; [right; cbn [st_free_meta_head upd_meta set_metas set_avail_meta set_avail_meta_count]; rewrite B1; exact Eh | intros _; discriminate]].
intros q E. rewrite MT_upd in E. destruct (sptr_eqb q (st_avail_meta s1)) eqn:Eq.
-- right. apply sptr_eqb_eq in Eq. subst q. reflexivity.
-- left. unfold MT in *. cbn [st_metas set_avail_meta set_avail_meta_count] in E. rewrite A1 in E. exact E.
* apply lw_ret. ms. split; [intros q E; left; unfold MT in *; rewrite A1 in E; exact E|].
split; [right; rewrite B1; exact Eh | intros G; specialize (G1 G); discriminate].
+ destruct (0 <? st_avail_meta_count (set_init_done true s)).
* apply lw_ret. ms. split; [reflexivity|]. split; [reflexivity | intros _; reflexivity].
* eapply lw_mono; [|apply new_area_lw]. intros [ok s1] (A & B & _ & _ & E). cbn [fst snd] in *.
split; [exact A|]. split; [exact B | exact E].
Qed.

Theorem alloc_struct F fuel :
(forall X sc req s, rawin X s -> lw F (fun r => rawin X (snd r) /\ (G4 F -> 0 <= fst r /\ HR s (snd r))) (alloc_slot fuel sc req s)) /\
(forall X sc req s, rawin X s -> lw F (fun r => rawin X (snd r) /\ (G4 F -> fst r <> None /\ HR s (snd r))) (alloc_group fuel sc req s)).
Proof.
induction fuel as [|f [IHs IHg]]; [split; intros; exact I|].
split.
- intros X sc req s Hr. cbn fix beta iota delta [alloc_slot].
apply lw_bind. eapply lw_mono; [|apply try_avail_RC]. intros [first s1] H1. ms. cbn [snd] in H1.
destruct (negb (first =? 0)).
+ apply lw_ret. ms. split; [eapply rawin_nn; [exact Hr | exact (proj1 H1)]|].
intros _. split; [unfold ctz32; apply Z.log2_nonneg | apply RC_HR, H1].
+ apply lw_bind. eapply lw_mono; [|apply IHg; eapply rawin_nn; [exact Hr | exact (proj1 H1)]].
intros [og s2] [R2 G2]. ms. cbn [fst snd] in R2, G2.
destruct og as [g|]; apply lw_ret; ms; (split; [exact R2|]); intros G; destruct (G2 G) as [N2 H2].
* split; [lia | eapply HR_trans; [apply RC_HR, H1 | exact H2]].
* exfalso. apply N2. reflexivity.
- intros X sc req s Hr. cbn fix beta iota delta [alloc_group].
apply lw_bind. eapply lw_mono; [|apply alloc_meta_lw]. intros [om s1] (R1 & H1 & G1). cbn [fst snd] in R1, H1, G1. ms.
destruct om as [m|].
2:{ apply lw_ret. ms. split; [intros q E; destruct (R1 q E) as [E'|E']; [exact (Hr q E') | discriminate] | intros G; exfalso; apply (G1 G); reflexivity]. }
assert (Hr1 : rawin (m :: X) s1).
{ intros q E. destruct (R1 q E) as [E'|E']; [right; exact (Hr q E') | left; injection E' as ->; reflexivity]. }
apply lw_bind, lw_get. ms.
destruct (PGSZ / 2 <? _).
+ eapply (lw_use F RC); [apply account_bounce_RC | apply pr_refl | intros u2 s2 H2; ms].
eapply (lw_use F RC); [apply step_seq_RC | exact H2 | intros u3 s3 H3; ms].
apply lw_bind, lw_ask. intros z Hz. ms. destruct (z =? 0) eqn:Ez; cbn [negb].
* apply lw_bind. eapply lw_mono; [|apply free_meta_lw]. intros [u4 s4] H4. ms. cbn [snd] in H4. apply lw_ret. ms. split.
{ intros q E. destruct (H4 q E) as [E3 Hq]. destruct (Hr1 q (proj1 H3 q E3)) as [->|Hin]; [exfalso; exact (Hq eq_refl) | exact Hin]. }
intros G. exfalso. pose proof (G _ _ Hz eq_refl). apply Z.eqb_eq in Ez. lia.
* eapply (lw_use F RC); [apply new_region_RC | exact H3 | intros r4 s4 H4; ms].
apply lw_bind, lw_get. ms.
eapply (lw_use F RC); [apply lw_put; ms; apply RC_same; reflexivity | exact H4 | intros u5 s5 H5; ms].
apply lw_bind. eapply lw_mono; [|apply install_group_RCm]. intros [u6 s6] [H6 M6]. ms. cbn [snd] in H6, M6. apply lw_ret. ms.
assert (C : RC s1 s6) by (eapply pr_trans; [exact H5 | exact H6]).
split.
{ intros q E. pose proof (proj1 C q E) as E1. destruct (Hr1 q E1) as [->|Hin]; [exfalso; exact (M6 E) | exact Hin]. }
intros G. split; [discriminate | eapply HR_trans; [exact H1 | apply RC_HR, C]].
+ apply lw_bind. eapply lw_mono; [|apply (IHs (m :: X)); exact Hr1]. intros [idx s2] [R2 G2]. ms. cbn [fst snd] in R2, G2.
destruct (idx <? 0) eqn:E.
* apply lw_bind. eapply lw_mono; [|apply free_meta_lw]. intros [u3 s3] H3. ms. cbn [snd] in H3. apply lw_ret. ms. split.
{ intros q Eq. destruct (H3 q Eq) as [E2 Hq]. destruct (R2 q E2) as [->|Hin]; [exfalso; exact (Hq eq_refl) | exact Hin]. }
intros G. exfalso. destruct (G2 G) as [Hge _]. apply Z.ltb_lt in E. lia.
* apply lw_bind, lw_get_head. ms. destruct (nth (Z.to_nat _) (st_active s2) None) as [g|]; [|exact I].
apply lw_bind, lw_getm. intros amg _. ms. apply lw_bind, lw_mcheck. intros _. ms. apply lw_bind, lw_get. ms.
eapply (lw_use F RC); [apply enframe_RC | apply pr_refl | intros p s3 H3; ms].
apply lw_bind. eapply lw_mono; [|apply install_group_RCm]. intros [u4 s4] [H4 M4]. ms. cbn [snd] in H4, M4. apply lw_ret. ms.
assert (C : RC s2 s4) by (eapply pr_trans; [exact H3 | exact H4]).
split.
{ intros q Eq. pose proof (proj1 C q Eq) as E2. destruct (R2 q E2) as [->|Hin]; [exfalso; exact (M4 Eq) | exact Hin]. }
intros G. destruct (G2 G) as [_ H2]. split; [discriminate | eapply HR_trans; [exact H1 | eapply HR_trans; [exact H2 | apply RC_HR, C]]].
Qed.

Theorem malloc_struct F s n : rawin [] s -> lw F (fun r => rawin [] (snd r) /\ (G4 F -> HR s (snd r))) (malloc n s).
Proof.
intros Hr. assert (HR0 : HR s s) by (left; split; [reflexivity | auto]).
unfold malloc. destruct (size_overflows n); [apply lw_ret; ms; split; [exact Hr | intros _; exact HR0]|].
destruct (MMAP_THRESHOLD <=? n).
- apply lw_bind, lw_ask. intros z Hz. ms. destruct (z =? 0) eqn:Ez; cbn [negb].
{ apply lw_ret. ms. split; [exact Hr | intros _; exact HR0]. }
eapply (lw_use F RC); [apply new_region_RC | apply pr_refl | intros r1 s1 H1; ms].
eapply (lw_use F RC); [apply step_seq_RC | exact H1 | intros u2 s2 H2; ms].
apply lw_bind. eapply lw_mono; [|apply alloc_meta_lw]. intros [og s3] (R3 & H3 & G3). ms. cbn [fst snd] in R3, H3, G3.
destruct og as [g|].
+ apply lw_bind, lw_setm. ms.
match goal with |- lw _ _ (bind _ _ ?st) => set (s4 := st) end.
assert (M4 : forall q, MT s4 q = Some MRaw -> q <> g /\ MT s3 q = Some MRaw).
{ intros q E. subst s4. rewrite MT_upd in E. destruct (sptr_eqb q g) eqn:Eq; [discriminate | split; [apply sptr_eqb_neq; exact Eq | exact E]]. }
assert (H4 : RC s3 s4) by apply RC_setm.
apply lw_bind, lw_get. ms.
eapply (lw_use F RC); [apply lw_put; ms; apply RC_same; reflexivity | apply (pr_refl s4) | intros u5 s5 H5; ms].
eapply (lw_use F RC); [apply enframe_RC | exact H5 | intros p s6 H6; ms].
apply lw_ret. ms. split.
{ intros q E. destruct (M4 q (proj1 H6 q E)) as [Hq E3]. destruct (R3 q E3) as [E2|E2].
- exfalso. exact (Hr q (proj1 H2 q E2)).
- injection E2 as E2. exfalso. exact (Hq (eq_sym E2)). }
intros G. eapply HR_trans; [apply RC_HR, H2 | eapply HR_trans; [exact H3 | apply RC_HR; eapply pr_trans; [exact H4 | exact H6]]].
+ apply lw_bind, lw_ask. intros z' _. ms. apply lw_bind. unfold upd_region. apply lw_modify. ms. apply lw_ret. ms. split.
{ intros q E. destruct (R3 q E) as [E2|E2]; [exact (Hr q (proj1 H2 q E2)) | discriminate]. }
intros G. exfalso. apply (G3 G). reflexivity.
- apply lw_bind, lw_get. ms.
match goal with |- lw _ _ (bind ?mm _ _) => assert (FA1 : RP F RC mm) end.
{ match goal with |- RP _ _ (match ?t with _ => _ end) => destruct t as [gm|] end; [|apply RP_ret]. apply RP_bind; [apply RP_getm | intros am].
destruct (am_avail am =? 0); [apply RP_ret|]. bz. apply RP_bind; [apply RP_setm; intros; apply RC_setm | intros; apply RP_ret]. }
eapply (lw_use F RC); [apply FA1 | apply pr_refl | intros r1 s1 H1; ms].
apply lw_bind.
eapply lw_mono with (P := fun r => rawin [] (snd r) /\ (G4 F -> HR s (snd r))).
+ intros [gi s2] [R2 G2]. ms. cbn [snd] in R2, G2.
destruct gi as [[gm idx]|]; [|apply lw_ret; ms; split; assumption].
apply lw_bind, lw_get. ms.
eapply (lw_use F RC); [apply enframe_RC | apply pr_refl | intros p s3 H3; ms].
apply lw_ret. ms. split; [eapply rawin_nn; [exact R2 | exact (proj1 H3)] | intros G; eapply HR_trans; [exact (G2 G) | apply RC_HR, H3]].
+ destruct r1 as [gi|].
* apply lw_ret. ms. split; [eapply rawin_nn; [exact Hr | exact (proj1 H1)] | intros _; apply RC_HR, H1].
* apply lw_bind. eapply lw_mono; [|apply (proj1 (alloc_struct F NEST_FUEL)); eapply rawin_nn; [exact Hr | exact (proj1 H1)]].
intros [idx s2] [R2 G2]. ms. cbn [fst snd] in R2, G2.
destruct (idx <? 0).
-- apply lw_ret. ms. split; [exact R2 | intros G; eapply HR_trans; [apply RC_HR, H1 | exact (proj2 (G2 G))]].
-- apply lw_bind, lw_get_head. ms. destruct (nth (Z.to_nat _) (st_active s2) None) as [gm|]; [|exact I].
apply lw_ret. ms. split; [exact R2 | intros G; eapply HR_trans; [apply RC_HR, H1 | exact (proj2 (G2 G))]].
Qed.

Lemma rawin_noraw s : noraw s <-> rawin [] s.
Proof. split; [intros H q E; exfalso; exact (H q E) | intros H q E; exact (H q E)]. Qed.
Lemma used_len_l (l : list (sptr * mslot)) : (forall p x, In (p, x) l -> exists am, x = MUsed am) ->
length (flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) l) = length l.
Proof.
induction l as [|[p x] l IH]; intros H; [reflexivity|].
destruct (H p x (or_introl eq_refl)) as [am ->]. cbn. f_equal. apply IH. intros p' x' Hi. exact (H p' x' (or_intror Hi)).
Qed.

Theorem malloc_SI : forall s n tr r s', WF s -> SI s -> 0 <= n -> yields (malloc n s) tr (r, s') -> SI s'.
Proof.
intros s n tr r s' HW HS Hn Hy.
assert (T : itok (malloc n s) (fun x => WI True False False [] None K0 (snd x))).
{ apply (malloc_WI True False False U0 s n); [exact HW | apply WI_of; [intros _; exact HS | intros [] | intros []] | exact Hn | intros x _ H; exact H]. }
exact (WI_SIX _ _ _ _ _ _ (itok_yields _ _ _ _ T Hy) I).
Qed.
Theorem malloc_GS : forall s n tr r s', WF s -> GS s -> 0 <= n -> yields (malloc n s) tr (r, s') -> GS s'.
Proof.
intros s n tr r s' HW HG Hn Hy.
assert (T : itok (malloc n s) (fun x => WI False True False [] None K0 (snd x))).
{ apply (malloc_WI False True False U0 s n); [exact HW | apply WI_of; [intros [] | intros _; exact HG | intros []] | exact Hn | intros x _ H; exact H]. }
exact (WI_GSX _ _ _ _ _ _ _ (itok_yields _ _ _ _ T Hy) I).
Qed.
Theorem malloc_NL : forall s n tr r s', WF s -> NL s -> 0 <= n -> yields (malloc n s) tr (r, s') -> NL s'.
Proof.
intros s n tr r s' HW HL Hn Hy.
assert (T : itok (malloc n s) (fun x => WI False False True [] None K0 (snd x))).
{ apply (malloc_WI False False True U0 s n); [exact HW | apply WI_of; [intros [] | intros [] | intros _; exact HL] | exact Hn | intros x _ H; exact H]. }
exact (WI_NLX _ _ _ _ _ _ _ (itok_yields _ _ _ _ T Hy) I).
Qed.
Theorem malloc_noraw : forall s n tr r s', noraw s -> yields (malloc n s) tr (r, s') -> noraw s'.
Proof.
intros s n tr r s' HN Hy. apply rawin_noraw. apply rawin_noraw in HN.
exact (proj1 (lw_yields _ _ _ _ (malloc_struct FA s n HN) Hy)).
Qed.
Theorem malloc_hand : forall s n tr r s', WF s -> SI s -> noraw s -> 0 <= n ->
cpath04 (malloc n s) tr (r, s') -> hand s' <= Z.max (hand s) (nused s').
Proof.
intros s n tr r s' HW HS HN Hn Hc.
pose proof (cpath04_yields _ _ _ Hc) as Hy.
pose proof (malloc_SI s n tr r s' HW HS Hn Hy) as HS'.
assert (HW' : WF s').
{ assert (T : itok (malloc n s) (fun x => Inv [] None U0 (snd x))).
{ apply (malloc_WI False False False U0 s n); [exact HW | apply WI_of; intros [] | exact Hn | intros x H _; exact H]. }
exact (itok_yields _ _ _ _ T Hy). }
pose proof (malloc_noraw s n tr r s' HN Hy) as HN'.
pose proof (lw_cpath04 _ _ _ _ (malloc_struct canswer04 s n (proj1 (rawin_noraw s) HN)) Hc) as [_ HR1].
specialize (HR1 G4_04). cbn [snd] in HR1.
destruct HR1 as [[Eh _] | Ehd]; [lia|].
assert (E : hand s' = nused s').
{ destruct HS' as (_ & _ & _ & _ & HK). unfold hand_keys in HK. rewrite HK. unfold nused. f_equal. symmetry. apply used_len_l.
intros p x Hin. pose proof (mlookup_of_In _ p x (proj1 (inv_keys HW')) Hin) as Mx.
destruct x as [pr nx| |am]; [|exfalso; exact (HN' p Mx) | exists am; reflexivity].
exfalso. destruct (inv_rings HW') as ((ms & Rg & Hall) & _ & _).
destruct Rg as [_ Hhd]. rewrite Ehd in Hhd. destruct ms as [|m0 ms]; [|discriminate].
exact (Hall p pr nx Mx). }
lia.
Qed.
