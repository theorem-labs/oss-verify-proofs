(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1og X1of
X1q8 X1po X1pv X1pf X1px X1pm X1pj X1pk X1pz X1q0 X1q1 X1q2
X1qg X1pw X1q9 X1qa X1qq X1qr X1qh X1qb X1ph X1q6 X1qc
X1qn X1qo X1qp X1py X1pp X1pq X1pr.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma try_avail_natP {R} sc st (k : mstate -> Z -> M R) bail :
steq (try_avail sc st k bail) (sbind (try_avail sc st kP bP) (KF k bail)).
Proof. exact (try_avail_nat sc st k bail). Qed.
Lemma alloc_meta_natP {R} st (k : mstate -> optr -> M R) bail :
steq (alloc_meta st k bail) (sbind (alloc_meta st kP bP) (KF k bail)).
Proof. exact (alloc_meta_nat st k bail). Qed.
Lemma alloc_slot_natP lay f {R} st sc req (k : mstate -> Z -> M R) bail :
steq (alloc_slot lay f st sc req k bail) (sbind (alloc_slot lay f st sc req kP bP) (KF k bail)).
Proof. exact (alloc_slot_nat lay f R st sc req k bail). Qed.
Lemma alloc_group_natP lay f {R} st sc req (k : mstate -> optr -> M R) bail :
steq (alloc_group R lay (alloc_slot lay f) st sc req k bail) (sbind (alloc_group _ lay (alloc_slot lay f) st sc req kP bP) (KF k bail)).
Proof. exact (alloc_group_nat lay (fun R => @alloc_slot R lay f) (alloc_slot_nat lay f) st sc req k bail). Qed.

Fixpoint gtree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
match t with
| SRet r => Post L r
| SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> gtree L (k v) Post
| SVis (EUndef _) _ => False
| SVis e k => event_pre L e /\ forall a, answer_ok L e a = true -> gtree (event_post L e a) (k a) Post
end.

Lemma ftree_gtree {R} (t : M R) : forall L P, ftree L t P -> gtree L t P.
Proof.
induction t as [r|e k IHt]; intros L P H; [exact H|].
destruct e; cbn [ftree gtree] in H |- *; try exact H.
all: try (destruct H as [He Hk]; split; [exact He|]; intros a Ha; specialize (Hk a); rewrite Ha in Hk; apply IHt; exact Hk).
intros v Hv. apply IHt. apply H. exact Hv.
Qed.

Lemma gtree_steq {R} (t t' : M R) : steq t t' -> forall L P, gtree L t P -> gtree L t' P.
Proof.
induction 1 as [r|e k1 k2 Hk IHt]; intros L P H; [exact H|].
destruct e; cbn [gtree] in H |- *; try exact H.
all: try (destruct H as [He Hk']; split; [exact He|]; intros a Ha; apply IHt; apply Hk'; exact Ha).
intros v Hv. apply IHt. apply H. exact Hv.
Qed.

Lemma gtree_mono {R} (P P' : mled -> R -> Prop) : (forall L r, P L r -> P' L r) -> forall (t : M R) L, gtree L t P -> gtree L t P'.
Proof.
intros HP. induction t as [r|e k IHt]; intros L H; [apply HP; exact H|].
destruct e; cbn [gtree] in H |- *; try exact H.
all: try (destruct H as [He Hk]; split; [exact He|]; intros a Ha; apply IHt; apply Hk; exact Ha).
intros v Hv. apply IHt. apply H. exact Hv.
Qed.

Lemma gtree_vis_inv {R} L e (k : Z -> M R) P : gtree L (SVis e k) P -> is_peek e = false ->
event_pre L e /\ forall a, answer_ok L e a = true -> gtree (event_post L e a) (k a) P.
Proof.
intros H Hp. destruct e; cbn in Hp; try discriminate; cbn [gtree] in H; try (destruct H; fail).
all: destruct H as [He Hk]; split; [exact He|]; intros a Ha; apply Hk; exact Ha.
Qed.

Lemma gtree_not_bad {R} L (b : bool) (bail t : M R) P : gtree L (if negb b then bad_answer bail else t) P -> b = true /\ gtree L t P.
Proof. destruct b; cbn; [auto| intros H; destruct H]. Qed.

Lemma gtree_sbind_inv {R S} (t : M R) : forall (g : R -> M S) L P,
gtree L (sbind t g) P -> gtree L t (fun L1 x => gtree L1 (g x) P).
Proof.
induction t as [r|e k IHt]; intros g L P H; cbn [sbind] in H; [exact H|].
destruct e; cbn [gtree] in H |- *; try exact H.
all: try (destruct H as [He Hk]; split; [exact He|]; intros a Ha; apply IHt; apply Hk; exact Ha).
intros v Hv. apply IHt. apply H. exact Hv.
Qed.

Lemma gtree_ret_inv {R} L (r : R) P : gtree L (SRet r) P -> P L r.
Proof. intros H. exact H. Qed.

Lemma gtree_cpath {R} (t : M R) : forall L P L1 x, gtree L t P -> cpath L t L1 x -> P L1 x.
Proof.
induction t as [r|e k IHt]; intros L P L1 x H CP.
- inversion CP; subst. exact H.
- inversion CP; subst. destruct e; cbn [gtree] in H; try (destruct H; fail).
all: try (destruct H as [_ Hk]; eapply IHt; [apply Hk; eassumption| eassumption]).
cbn in H3. discriminate H3.
Qed.

Lemma strip_queue_st h g s : queue_st h g (strip s) = strip (queue_st h g s).
Proof.
unfold queue_st, q_link, q_single. rewrite get_head_strip. destruct (get_head s h); [| rewrite strip_upd_meta, strip_set_head; reflexivity].
rewrite !get_meta_rec_strip. destruct (m_prev _); rewrite ?strip_upd_meta; reflexivity.
Qed.
Lemma rebase_queue_st rho resv {ceil} h g cs : queue_st h g (rebase rho resv ceil cs) = rebase rho resv ceil (queue_st h g cs).
Proof.
unfold queue_st, q_link, q_single. rewrite get_head_rebase. destruct (get_head cs h); [| rewrite rebase_upd_meta, rebase_set_head; reflexivity].
rewrite !get_meta_rec_rebase. destruct (m_prev _); rewrite ?rebase_upd_meta; reflexivity.
Qed.
Lemma RC_queue_st rho resv {ceil} h g sG sC : RC rho resv ceil sG sC -> RC rho resv ceil (queue_st h g sG) (queue_st h g sC).
Proof. apply (RC_lift rho resv (queue_st h g)); [intros s; apply strip_queue_st| intros cs; apply rebase_queue_st]. Qed.
Lemma RC_fm_st rho resv {ceil} g sG sC : RC rho resv ceil sG sC -> RC rho resv ceil (fm_st sG g) (fm_st sC g).
Proof. intros H. unfold fm_st. apply RC_queue_st. apply RC_put_meta. exact H. Qed.
Lemma RC_agt rho resv {ceil} sc m p cnt ai sG sC : RC rho resv ceil sG sC -> RC rho resv ceil (agt sG sc m p cnt ai) (agt sC sc m p cnt ai).
Proof.
intros H. unfold agt.
assert (H0 : RC rho resv ceil (hdr_havoc p sG) (hdr_havoc p sC)) by (eapply RC_layout; [exact H| apply strip_hdr_havoc| apply strip_hdr_havoc]).
rewrite (RC_usage _ _ _ _ sc H0).
assert (H2 : RC rho resv ceil (upd_meta m (agG sc p cnt ai) (set_usage sc (usage (hdr_havoc p sG) sc + cnt) (hdr_havoc p sG)))
(upd_meta m (agG sc p cnt ai) (set_usage sc (usage (hdr_havoc p sG) sc + cnt) (hdr_havoc p sC)))).
{ apply RC_upd_meta. apply RC_set_usage. exact H0. }
assert (H3 : RC rho resv ceil (put_group p (Some m) ai (upd_meta m (agG sc p cnt ai) (set_usage sc (usage (hdr_havoc p sG) sc + cnt) (hdr_havoc p sG))))
(put_group p (Some m) ai (upd_meta m (agG sc p cnt ai) (set_usage sc (usage (hdr_havoc p sG) sc + cnt) (hdr_havoc p sC))))).
{ apply RC_put_group. exact H2. }
rewrite (RC_MRc _ _ _ _ m H3). apply RC_add_slots. exact H3.
Qed.

Lemma queue_st_frame h g st : s_regions (queue_st h g st) = s_regions st /\ c_brk (s_ctx (queue_st h g st)) = c_brk (s_ctx st)
/\ c_avail_meta_areas (s_ctx (queue_st h g st)) = c_avail_meta_areas (s_ctx st).
Proof.
unfold queue_st, q_link, q_single. destruct (get_head st h); [destruct (m_prev _); repeat split; reflexivity|].
destruct h; repeat split; reflexivity.
Qed.
Lemma fm_st_frame g st : s_regions (fm_st st g) = s_regions st /\ c_brk (s_ctx (fm_st st g)) = c_brk (s_ctx st)
/\ c_avail_meta_areas (s_ctx (fm_st st g)) = c_avail_meta_areas (s_ctx st).
Proof. unfold fm_st. destruct (queue_st_frame LFree g (put_meta g meta0 st)) as (A & B & C). rewrite A, B, C. repeat split; reflexivity. Qed.

Lemma JR_fm_st J rho sG sC g : JR J rho sG sC -> JR J rho (fm_st sG g) (fm_st sC g).
Proof.
intros R. destruct (fm_st_frame g sG) as (A & B & C). apply (JR_frame J rho sG sC); [exact R| exact A| exact B| exact C|].
apply RC_fm_st. exact (jr_rc _ _ _ _ R).
Qed.
Lemma JR_queue_st J rho sG sC h g : JR J rho sG sC -> JR J rho (queue_st h g sG) (queue_st h g sC).
Proof.
intros R. destruct (queue_st_frame h g sG) as (A & B & C). apply (JR_frame J rho sG sC); [exact R| exact A| exact B| exact C|].
apply RC_queue_st. exact (jr_rc _ _ _ _ R).
Qed.
Lemma JR_upd_meta J rho sG sC m f : JR J rho sG sC -> JR J rho (upd_meta m f sG) (upd_meta m f sC).
Proof. intros R. apply (JR_frame J rho sG sC); [exact R| reflexivity| reflexivity| reflexivity| apply RC_upd_meta; exact (jr_rc _ _ _ _ R)]. Qed.
Lemma JR_agt J rho sG sC sc m p cnt ai : JR J rho sG sC -> JR J rho (agt sG sc m p cnt ai) (agt sC sc m p cnt ai).
Proof. intros R. apply (JR_frame J rho sG sC); [exact R| reflexivity| reflexivity| reflexivity| apply RC_agt; exact (jr_rc _ _ _ _ R)]. Qed.
Lemma JR_nest J rho sG sC m g idx j size cnt :
JR J rho sG sC -> JR J rho (upd_meta m (m_set_maplen 0) (nest_layout sG g idx j size cnt)) (upd_meta m (m_set_maplen 0) (nest_layout sC g idx j size cnt)).
Proof.
intros R. apply (JR_frame J rho sG sC); [exact R| | | |].
- rewrite s_regions_upd_meta. apply s_regions_nest_layout.
- rewrite s_ctx_upd_meta, s_ctx_nest_layout. reflexivity.
- rewrite s_ctx_upd_meta, s_ctx_nest_layout. reflexivity.
- apply RC_upd_meta. eapply RC_layout; [exact (jr_rc _ _ _ _ R)| apply strip_nest_layout| apply strip_nest_layout].
Qed.
Lemma JR_step_bounce J rho sG sC sc : JR J rho sG sC -> JR J rho (step_seq (account_bounce sc sG)) (step_seq (account_bounce sc sC)).
Proof.
intros R. destruct (account_bounce_fields sc sG) as (_ & _ & _ & A4 & _). destruct (step_seq_fields (account_bounce sc sG)) as (_ & _ & _ & B4 & _).
apply (JR_frame J rho sG sC); [exact R| rewrite B4, A4; reflexivity| | |].
- unfold step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
- unfold step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
- apply RC_step_seq. apply RC_account_bounce. exact (jr_rc _ _ _ _ R).
Qed.

Lemma RC_is_bouncing rho resv {ceil} sG sC sc : RC rho resv ceil sG sC -> is_bouncing sc sC = is_bouncing sc sG.
Proof. intros H. unfold is_bouncing, bounces, ctx. rewrite (RC_ctx _ _ _ _ H). reflexivity. Qed.
Lemma RC_slot_of rho resv {ceil} sG sC g i : RC rho resv ceil sG sC -> slot_of sC g i = slot_of sG g i.
Proof. intros H. unfold slot_of. rewrite (RC_MRc _ _ _ _ g H). reflexivity. Qed.
Lemma JR_upd_ctx_mc J rho sG sC : JR J rho sG sC ->
JR J rho (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) sG) (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) sC).
Proof. intros R. apply (JR_frame J rho sG sC); [exact R| reflexivity| reflexivity| reflexivity| apply RC_upd_ctx; exact (jr_rc _ _ _ _ R)]. Qed.

Section AS2.
Variables (BLG BLC : list blk).

Definition PostR {Y} (PUG PUC : mled -> option (mstate * Y) -> Prop) (J' : jled) (x y : option (mstate * Y)) : Prop :=
match x, y with
| Some (s1, v), Some (s1', v') => v' = v /\ PUG (projG J') x /\ PUC (projC J') y /\ exists rho', JR J' rho' s1 s1'
| None, None => True
| _, _ => False
end.

Definition ENT2 (X : extras) (J : jled) (rho : N -> Z) (sG sC : mstate) (LSG LSC : lhead -> list aptr) : Prop :=
INVL X sG (projG J) BLG LSG /\ INVL X sC (projC J) BLC LSC /\ JR J rho sG sC.

Definition SLOT_REL (f : nat) : Prop :=
forall X J rho sG sC LSG LSC sc req (PUG PUC : mled -> option (mstate * Z) -> Prop),
ENT2 X J rho sG sC LSG LSC -> x_pend X = None -> x_fresh X = None -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
gtree (projG J) (alloc_slot full_lay f sG sc req kP bP) PUG ->
gtree (projC J) (alloc_slot full_lay f sC sc req kP bP) PUC ->
jsim J (alloc_slot full_lay f sG sc req kP bP) (alloc_slot full_lay f sC sc req kP bP) (PostR PUG PUC).

Section AG2.
Variable f : nat.
Hypothesis IH : SLOT_REL f.

#[using="IH"] Theorem alloc_group_rel X J rho sG sC LSG LSC sc req (PUG PUC : mled -> option (mstate * optr) -> Prop) :
ENT2 X J rho sG sC LSG LSC -> x_pend X = None -> x_fresh X = None -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
gtree (projG J) (alloc_group _ full_lay (alloc_slot full_lay f) sG sc req kP bP) PUG ->
gtree (projC J) (alloc_group _ full_lay (alloc_slot full_lay f) sC sc req kP bP) PUC ->
jsim J (alloc_group _ full_lay (alloc_slot full_lay f) sG sc req kP bP)
(alloc_group _ full_lay (alloc_slot full_lay f) sC sc req kP bP) (PostR PUG PUC).
Proof.
intros (INVG & INVC & R) HP HF Hsc Hreq Hfit FTG FTC.
unfold alloc_group in FTG, FTC |- *.

match goal with |- jsim _ (alloc_meta sG ?kg bP) (alloc_meta sC ?kc bP) _ =>
apply (jsim_steq J (sbind (alloc_meta sG kP bP) (KF kg bP)) _ (sbind (alloc_meta sC kP bP) (KF kc bP)) _);
[apply steq_sym; apply alloc_meta_natP| apply steq_sym; apply alloc_meta_natP|];
apply (gtree_steq _ _ (alloc_meta_natP sG kg bP)) in FTG; apply (gtree_steq _ _ (alloc_meta_natP sC kc bP)) in FTC
end.
apply gtree_sbind_inv in FTG. apply gtree_sbind_inv in FTC.
pose proof (alloc_meta_rel X BLG BLC sG sC J J rho sG sC LSG LSC
ltac:(split; [exact INVG|]; split; [exact INVC|]; split; [exact R|]; split; [apply amf_refl|]; split; [apply amf_refl| apply jf_refl])) as AM.
eapply jsim_bind_path; [exact AM|].
intros J1 x y PAM CP.
pose proof (gtree_cpath _ _ _ _ _ FTG (jcpath_cpath_G _ _ _ _ _ _ _ AM CP)) as FTG1.
pose proof (gtree_cpath _ _ _ _ _ FTC (jcpath_cpath_C _ _ _ _ _ _ _ AM CP)) as FTC1.
clear FTG FTC. cbn beta in FTG1, FTC1.
destruct x as [[sG1 moG]|]; destruct y as [[sC1 moC]|]; cbn in PAM; try contradiction; [| exact I].
destruct PAM as (EMO & rho1 & LSG1 & LSC1 & R1 & AFG & AFC & JF1 & INV1). subst moC.
cbn [KF] in FTG1, FTC1 |- *.
destruct moG as [m|].
2:{ apply jsim_ret. cbn. split; [reflexivity|]. split; [exact FTG1|]. split; [exact FTC1|]. exists rho1. exact R1. }
destruct INV1 as (INVG1 & INVC1 & NIm).
pose proof (jr_rc _ _ _ _ R1) as HRC1.
rewrite (RC_usage _ _ _ _ sc HRC1) in FTC1 |- *.
cbv zeta in FTG1, FTC1 |- *.
change (if sc <? 9 then small_cnt_pick sc (usage sG1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage sG1 sc)) (UNIT * size_class sc))
with (cnt0_of sc (usage sG1 sc)) in FTG1, FTC1 |- *.
change (if (cnt0_of sc (usage sG1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage sG1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage sG1 sc))
with (ag_cnt1 sc (usage sG1 sc)) in FTG1, FTC1 |- *.
change (lh_nest full_lay) with nest_layout in FTG1, FTC1 |- *.
pose proof (ag_arith sc req (usage sG1 sc)) as AR.
set (c1 := ag_cnt1 sc (usage sG1 sc)) in *.
destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
-
pose proof (RC_step_seq _ _ _ _ (RC_account_bounce _ _ sc _ _ HRC1)) as HRC1'.
rewrite (RC_is_bouncing _ _ _ _ sc HRC1) in FTC1 |- *. rewrite (RC_usage _ _ _ _ (sc + 1) HRC1') in FTC1 |- *.
set (st1G := step_seq (account_bounce sc sG1)) in *. set (st1C := step_seq (account_bounce sc sC1)) in *.
match goal with |- jsim _ ?t _ _ => match t with (let '(a, b) := ?cn in _) => set (CN := cn) in FTG1, FTC1 |- * end end.
clearbody CN. destruct CN as [c3 n3]. cbv iota beta in FTG1, FTC1 |- *.
apply gtree_vis_inv in FTG1 as [PREG FKG]; [| reflexivity]. apply gtree_vis_inv in FTC1 as [PREC FKC]; [| reflexivity].
apply jsim_vis.
+ cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. left.
cbn in PREG. destruct PREG as [(Q & _ & _ & _ & LEN)|(cur & _ & _ & _ & _ & F)]; [| discriminate F].
split; [exact Q|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity| exact LEN].
+ exact I.
+ intros zG zC Hz. pose proof (jans_ok_G _ _ _ _ _ Hz) as AG. pose proof (jans_ok_C _ _ _ _ _ Hz) as AC. pose proof (jans_ok_class _ _ _ _ _ Hz) as CL.
specialize (FKG zG AG). specialize (FKC zC AC).
apply gtree_not_bad in FKG as [OKG FKG]. apply gtree_not_bad in FKC as [OKC FKC]. rewrite OKG, OKC. cbn [negb].
cbn in CL. apply Bool.eqb_prop in CL. rewrite <- CL.
cbn [jevent_post]. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
unfold event_post in FKG, FKC. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in FKG, FKC. change (PROT_RW =? PROT_NONE) with false in FKG, FKC. cbn iota in FKG, FKC.
rewrite <- CL in FKC.
destruct (is_err zG) eqn:ER.
*
rewrite (free_meta_eq st1G) in FKG |- *. rewrite (free_meta_eq st1C) in FKC |- *.
apply jsim_ret. cbn. split; [reflexivity|]. split; [exact FKG|]. split; [exact FKC|].
exists rho1. apply JR_fm_st. unfold st1G, st1C. apply JR_step_bounce. exact R1.
*
cbn [new_region] in FKG, FKC |- *. rewrite !ag_tail_eq in FKG, FKC |- *.
rewrite (RC_next_rid _ _ _ _ HRC1') in FKC |- *.
apply jsim_ret. cbn [PostR]. split; [reflexivity|]. split; [exact FKG|]. split; [exact FKC|].
exists (nupd rho1 (s_next_rid st1G) zC). apply JR_agt. apply JR_upd_ctx_mc. apply JR_upd_meta.
pose proof (JR_new_group J1 rho1 st1G st1C zG zC n3 _ (projG J1) ltac:(unfold st1G, st1C; apply JR_step_bounce; exact R1)
(proj1 (INVL_step_seq _ _ _ _ _ (INVL_account_bounce _ _ _ _ _ sc INVG1)))) as R2.
unfold new_region in R2. cbn [fst] in R2. rewrite (RC_next_rid _ _ _ _ HRC1') in R2. exact R2.
-
pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
pose proof (nest_ok_sound sc c1 NEST) as N0. cbn zeta in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
set (size := UNIT * size_class sc) in *. set (j := size_to_class (UNIT + c1 * size - IB)) in *. set (req' := UNIT + c1 * size - IB) in *.
match goal with |- jsim _ (alloc_slot full_lay f sG1 j req' ?kg bP) (alloc_slot full_lay f sC1 j req' ?kc bP) _ =>
apply (jsim_steq J1 (sbind (alloc_slot full_lay f sG1 j req' kP bP) (KF kg bP)) _ (sbind (alloc_slot full_lay f sC1 j req' kP bP) (KF kc bP)) _);
[apply steq_sym; apply alloc_slot_natP| apply steq_sym; apply alloc_slot_natP|];
apply (gtree_steq _ _ (alloc_slot_natP full_lay f sG1 j req' kg bP)) in FTG1; apply (gtree_steq _ _ (alloc_slot_natP full_lay f sC1 j req' kc bP)) in FTC1
end.
apply gtree_sbind_inv in FTG1. apply gtree_sbind_inv in FTC1.
eapply jsim_bind.
{ apply (IH (xidle X (m :: x_idle X)) J1 rho1 sG1 sC1 LSG1 LSC1 j req'); [split; [exact INVG1| split; [exact INVC1| exact R1]]| exact HP| exact HF| lia| exact N5| lia| exact FTG1| exact FTC1]. }
clear FTG1 FTC1. intros J2 x y PR2.
destruct x as [[sG2 idxG]|]; destruct y as [[sC2 idxC]|]; cbn in PR2; try contradiction; [| exact I].
destruct PR2 as (EI & FTG2 & FTC2 & rho2 & R2). subst idxC. cbn [KF] in FTG2, FTC2 |- *.
pose proof (jr_rc _ _ _ _ R2) as HRC2.
destruct (idxG <? 0).
+
rewrite (free_meta_eq sG2) in FTG2 |- *. rewrite (free_meta_eq sC2) in FTC2 |- *.
apply jsim_ret. cbn. split; [reflexivity|]. split; [exact FTG2|]. split; [exact FTC2|]. exists rho2. apply JR_fm_st. exact R2.
+ rewrite (RC_active _ _ _ _ j HRC2) in FTC2 |- *. rewrite (RC_slot_of _ _ _ _ _ idxG HRC2) in FTC2 |- * || idtac.
destruct (active sG2 j) as [g|]; [| apply jsim_undef].
rewrite (RC_slot_of _ _ _ _ g idxG HRC2) in FTC2 |- *.
rewrite !ag_tail_eq in FTG2, FTC2 |- *.
apply jsim_ret. cbn [PostR]. split; [reflexivity|]. split; [exact FTG2|]. split; [exact FTC2|].
exists rho2. apply JR_agt. apply JR_nest. exact R2.
Qed.
End AG2.

#[using="Type"] Lemma optr_eqb_None x : optr_eqb x None = true -> x = None.
Proof. destruct x; cbn; [discriminate| reflexivity]. Qed.

#[using="Type"] Theorem alloc_slot_rel : forall f, SLOT_REL f.
Proof.
induction f as [|f IHf]; intros X J rho sG sC LSG LSC sc req PUG PUC (INVG & INVC & R) HP HF Hsc Hreq Hfit FTG FTC.
- cbn [alloc_slot]. apply jsim_undef.
- cbn [alloc_slot] in FTG, FTC |- *.
match goal with |- jsim _ (try_avail sc sG ?kg bP) (try_avail sc sC ?kc bP) _ =>
apply (jsim_steq J (sbind (try_avail sc sG kP bP) (KF kg bP)) _ (sbind (try_avail sc sC kP bP) (KF kc bP)) _);
[apply steq_sym; apply try_avail_natP| apply steq_sym; apply try_avail_natP|];
apply (gtree_steq _ _ (try_avail_natP sc sG kg bP)) in FTG; apply (gtree_steq _ _ (try_avail_natP sc sC kc bP)) in FTC
end.
destruct (try_avail_ok _ X (projG J) BLG sc kP bP HP HF Hsc sG LSG INVG) as (sG1 & fG & LSG1 & EG & TAG).
destruct (try_avail_ok _ X (projC J) BLC sc kP bP HP HF Hsc sC LSC INVC) as (sC1 & fC & LSC1 & EC & TAC).
pose proof (try_avail_RC rho (j_resvC J) sG sC sc sG1 sC1 fG fC (jr_rc _ _ _ _ R) EG EC) as [EF RC1]. subst fC.
rewrite EG in FTG |- *. rewrite EC in FTC |- *. cbn [sbind KF kP] in FTG, FTC |- *.
destruct TAG as [TFG RESG]. destruct TAC as [TFC RESC].
assert (IRG1 : exists X1 LS1, INVL X1 sG1 (projG J) BLG LS1).
{ destruct RESG as [(_ & _ & INV1)|(g & bg & ai & idx & _ & _ & _ & _ & _ & _ & _ & _ & INV1)]; eexists _, _; exact INV1. }
assert (R1 : JR J rho sG1 sC1).
{ destruct IRG1 as (X1 & LS1 & INV1). apply (JR_reinv J rho sG sC sG1 sC1 X X1 R (proj1 INVG) (proj1 INV1) (taf_regions _ _ _ TFG) RC1). }
destruct (Z.eqb_spec fG 0) as [E0|NZ]; cbn [negb] in FTG, FTC |- *.
+
destruct RESG as [(_ & HAG & INVG1)|(g & bg & ai & idx & NZ' & _)]; [| exfalso; apply NZ'; exact E0].
destruct RESC as [(_ & HAC & INVC1)|(g & bg & ai & idx & NZ' & _)]; [| exfalso; apply NZ'; exact E0].
match goal with |- jsim _ (alloc_group _ _ _ sG1 sc req ?kg bP) (alloc_group _ _ _ sC1 sc req ?kc bP) _ =>
apply (jsim_steq J (sbind (alloc_group _ full_lay (alloc_slot full_lay f) sG1 sc req kP bP) (KF kg bP)) _
(sbind (alloc_group _ full_lay (alloc_slot full_lay f) sC1 sc req kP bP) (KF kc bP)) _);
[apply steq_sym; apply alloc_group_natP| apply steq_sym; apply alloc_group_natP|];
apply (gtree_steq _ _ (alloc_group_natP full_lay f sG1 sc req kg bP)) in FTG; apply (gtree_steq _ _ (alloc_group_natP full_lay f sC1 sc req kc bP)) in FTC
end.
apply gtree_sbind_inv in FTG. apply gtree_sbind_inv in FTC.
eapply jsim_bind.
{ apply (alloc_group_rel f IHf X J rho sG1 sC1 LSG1 LSC1 sc req); [split; [exact INVG1| split; [exact INVC1| exact R1]]| exact HP| exact HF| exact Hsc| exact Hreq| exact Hfit| exact FTG| exact FTC]. }
clear FTG FTC. intros J2 x y PR.
destruct x as [[sG2 goG]|]; destruct y as [[sC2 goC]|]; cbn in PR; try contradiction; [| exact I].
destruct PR as (EGO & FTG2 & FTC2 & rho2 & R2). subst goC. cbn [KF] in FTG2, FTC2 |- *.
pose proof (jr_rc _ _ _ _ R2) as HRC2.
destruct goG as [g|].
*
cbv zeta in FTG2, FTC2 |- *.
set (sG3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) sG2) in *.
set (sC3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) sC2) in *.
assert (HRC3 : RC rho2 (j_resvC J2) (j_ceilC J2) sG3 sC3) by (apply RC_upd_meta; exact HRC2).
assert (HN : m_next (get_meta_rec sG3 g) = None /\ m_prev (get_meta_rec sG3 g) = None).
{ unfold queue, guard in FTG2. destruct (optr_eqb (m_next (get_meta_rec sG3 g)) None) eqn:E1; [| destruct FTG2].
destruct (optr_eqb (m_prev (get_meta_rec sG3 g)) None) eqn:E2; [| destruct FTG2]. split; apply optr_eqb_None; assumption. }
destruct HN as [HN1 HN2].
rewrite (queue_eq (LActive sc) g sG3 _ bP HN1 HN2) in FTG2 |- *.
rewrite (queue_eq (LActive sc) g sC3 _ bP) in FTC2 |- * by (rewrite (RC_MRc _ _ _ _ g HRC3); assumption).
apply jsim_ret. cbn [PostR]. split; [reflexivity|]. split; [exact FTG2|]. split; [exact FTC2|].
exists rho2. apply JR_queue_st. apply JR_upd_meta. exact R2.
* apply jsim_ret. cbn [PostR]. split; [reflexivity|]. split; [exact FTG2|]. split; [exact FTC2|]. exists rho2. exact R2.
+
apply jsim_ret. cbn [PostR]. split; [reflexivity|]. split; [exact FTG|]. split; [exact FTC|]. exists rho. exact R1.
Qed.
End AS2.
