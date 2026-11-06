(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the cf bridge of the generic realloc rule (YGcallRx.v), as YGcallcf.v is for malloc / free.
   The cf instance of the generic rules runs over the relation ARcf /\ xs_placed_cf (YGcallcf.v; xs_placed_cf is
   YG0ncf.v's). h-mani-a8's realloc texts (YGcfRealloc.v) are ReallocP.v's P forms at the cf instance with the leaf
   realloc_leaf_cf, which already carries xs_placed_cf at the post layout; so:
   - realloc_leaf_cf_x / realloc_leaf_x_xs_cf: realloc_leaf_cf IS YGcallRx.v's realloc_leaf_x at ARcf /\ xs_placed_cf
     and XS := xs_cf (both directions; the ghost set realloc_hp_cf is Hp on PNull and remove on success, and the frame
     exceptions agree arm by arm). No leaf-keep stand-in is needed: the keep is the leaf's last conjunct.
   - arealloc_realizes_x_cf: the cf text, for every Hp, gives the generic text the rule takes (pc0 := CfImg's
     cf_pc_realloc_ra0, by name). Both texts are arealloc_realizes_allP written out, rpre := True dropped, with the
     premise ~ In (sptr_addr B ly p) Hp after a0 (the freed base is not hidden), so the premises pass one for one.
   - realloc_x_null_post_cf: the NULL arm of aj_realloc_x (acall_pre_x, the old block, mt_refused, realloc_leaf_x at
     (PNull, S2)) gives malloc_cf_null_post, through a Theorem Labs lane's realloc_cf_null_post_of_leaf (the same from the NULL
     arm of the rules over R: realloc_x_null_post_cfR below).
   - realloc_model_law_x_cf: YGcallRx.v's realloc model law (the rule's RMX) at the cf instance, for every headroom k:
     RQ := qtight s /\ ROOM_cf_k s (RK_realloc + k) (YGcfRoomKeep.v), WFx := Wf_cf, cited from h-mani-a8's
     amx_realloc_cf (YGcfAmx2.v).
   Uses the shared cf instance classes CfImg / CfParams only; no preset name, no address, no ledger, no numeral. *)
(* Modified by Theorem Labs, 2026-10-30 (the cf bridge of the realloc rules over R, YGcallRx.v section 3R): the cf
   instance runs at R := wle' segs RZ_cf (YA0nH.v, YGcfRehidePost.v) and APOST := APOST_cf (YGcallcf.v), from the cgif
   layer's primed row YGcfInstReallocK.arealloc_realizes_cf_k (realloc(p, n) frees the old block inside the call, so
   its walk is amreal' segs RZ_cf and its leaf YG0dcfR.realloc_leaf_cf_rh):
   - realloc_leaf_cf_xR / realloc_leaf_x_xs_cfR: realloc_leaf_cf_rh IS YGcallRx.v's realloc_leaf_xR at APOST_cf and
     XS := xs_cf (both directions; arm by arm as realloc_leaf_cf_x, the frame's re-hide antecedent passed through);
   - arealloc_realizes_x_cfR: the primed row, for every Hp and k, gives arealloc_realizes_xR at R := wle' segs RZ_cf,
     APOST := APOST_cf and RQ := qtight s /\ ROOM_cf_k s (RK_realloc + k) /\ cf_hull_adm s n: the row's entry room
     and entry hull admission are RQ's second and third conjuncts;
   - realloc_model_law_x_cfR: realloc_model_law_x_cf at that RQ (the law reads its first two conjuncts);
   - realloc_x_null_post_cfR: the NULL arm of the rules over R (realloc_leaf_xR at APOST_cf, (PNull, S2)) gives
     malloc_cf_null_post, as realloc_x_null_post_cf does for the wle arm: on a refused path free_cf PNull keeps st_secs
     (YGcfSecsStep.secs_free_null_step) and the NULL malloc_cf hides nothing (YGcfNullCall.malloc_cf_null_dead_empty),
     so the post's dead set dead_shadow_new ly S S2 is empty, its wle_in step is wle and its view premise holds; the
     leaf is then realloc_leaf_x (the step YGcfNullCall.afree_null_realizes_cf_of_rh takes for free(NULL));
   - Section instR, aj_realloc_at_x_cfR / aj_realloc_x_cfR: YGcallRx.v's rules over R at this instance (POST_AR_cf,
     POST_J_cf), from the primed row.
   The plain bridges above stay as they are: they are the wle instance, from YGcfRealloc.v's texts. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbq YCbqG YGcallx YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ReallocP YGcfRealloc YGcallRx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG07cf YG03cf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomKeep YGcfRoomStep YG03dcf YGcfAmx YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YG0dcfR YGcfInstReallocK.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep YGcfNullCall.
Import ListNotations.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section J.
Variable segs : list Segment.
Variable B : asyms.

(* The ghost set after a non-NULL realloc result. *)
Lemma realloc_hp_cf_nn : forall ly p q Hp, q <> PNull -> realloc_hp_cf B ly p q Hp = remove Z.eq_dec (sptr_addr B ly p) Hp.
Proof. intros ly p q Hp Hq. destruct q; [exfalso; exact (Hq eq_refl) | reflexivity | reflexivity | reflexivity]. Qed.

(* h-mani-a8's realloc leaf is the generic one at ARcf /\ xs_placed_cf, XS := xs_cf. *)
Lemma realloc_leaf_cf_x : forall Hp ly S W regs mem md p n_old n r W' c',
realloc_leaf_cf segs B ly S Hp W regs mem md p n_old n r W' c' ->
realloc_leaf_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) xs_cf
  Hp ly S W regs mem md p n_old n r W' c'.
Proof.
intros Hp ly S W regs mem md p n_old n [q S2] W' c'
(ly' & regs' & mem' & md' & Hc & Hpost & Hres & HQT & Hcopy & Herr & HX & HE & HR).
cbn [fst snd] in *.
destruct Hpost as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
exists ly', regs', mem', md'. cbn [fst snd]. split; [exact Hc|]. split; [exact Hres|]. split; [exact HQT|].
split; [|split; [|exact (conj HE HR)]].
- intros Eq. subst q. cbn [realloc_hp_cf] in A1. split; [|exact (Herr eq_refl)].
  refine (conj (conj A1 HX) (conj A2 (conj A3 (conj A4 (conj A5 (conj _ A7)))))).
  intros a Ha N1 N2 N3 N4. apply (A6 a Ha N1 N2 N3).
  intros [[Hf _] | [[Hf _] | HXa]]; [exact (Hf eq_refl) | exact (Hf eq_refl) | exact (N4 HXa)].
- intros Hq. rewrite (realloc_hp_cf_nn ly p q Hp Hq) in A1. split; [|exact (Hcopy Hq)].
  refine (conj (conj A1 HX) (conj A2 (conj A3 (conj A4 (conj A5 (conj _ A7)))))).
  intros a Ha N1 N2 N3 N4. apply (A6 a Ha N1 N2 N3).
  intros [[_ H] | [[_ H] | H]]; apply N4; [left; exact H | right; left; exact H | right; right; exact H].
Qed.

(* And back: the generic leaf at ARcf /\ xs_placed_cf is h-mani-a8's. *)
Lemma realloc_leaf_x_xs_cf : forall Hp ly S W regs mem md p n_old n r W' c',
realloc_leaf_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) xs_cf
  Hp ly S W regs mem md p n_old n r W' c' ->
realloc_leaf_cf segs B ly S Hp W regs mem md p n_old n r W' c'.
Proof.
intros Hp ly S W regs mem md p n_old n [q S2] W' c' (ly' & regs' & mem' & md' & Hc & Hres & HQT & LN & LS & HE & HR).
cbn [fst snd] in *.
destruct (asptr_null_dec q) as [-> | Hq].
- destruct (LN eq_refl) as (((A1 & HX) & A2 & A3 & A4 & A5 & A6 & A7) & Herr & Hoom).
  exists ly', regs', mem', md'. cbn [fst snd]. split; [exact Hc|].
  split.
  { cbn [realloc_hp_cf]. refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj _ A7)))))).
    intros a Ha N1 N2 N3 N4. apply (A6 a Ha N1 N2 N3). intros HXa. apply N4. right. right. exact HXa. }
  split; [exact Hres|]. split; [exact HQT|]. split; [intros Hf; exfalso; exact (Hf eq_refl)|].
  split; [intros _; exact (conj Herr Hoom) | exact (conj HX (conj HE HR))].
- destruct (LS Hq) as (((A1 & HX) & A2 & A3 & A4 & A5 & A6 & A7) & Hcopy).
  exists ly', regs', mem', md'. cbn [fst snd]. split; [exact Hc|].
  split.
  { rewrite (realloc_hp_cf_nn ly p q Hp Hq). refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj _ A7)))))).
    intros a Ha N1 N2 N3 N4. apply (A6 a Ha N1 N2 N3).
    intros [H | [H | H]]; apply N4; [left; exact (conj Hq H) | right; left; exact (conj Hq H) | right; right; exact H]. }
  split; [exact Hres|]. split; [exact HQT|]. split; [intros _; exact Hcopy|].
  split; [intros E; exfalso; exact (Hq E) | exact (conj HX (conj HE HR))].
Qed.

(* h-mani-a8's realloc text, for every ghost set, gives the generic text the rule takes. *)
Lemma arealloc_realizes_x_cf : forall pc, (forall Hp, arealloc_realizes_cf segs B Hp pc) ->
arealloc_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S)
  (QMm_cf segs B) malloc_cf cf_malloc_max free_cf xs_cf pc cf_pc_realloc_ra0.
Proof.
intros pc H Hp ly S W regs mem md p n_old n ch HPRE Hin H10 Hhid H11 Hn Hlive Htr.
pose proof (H Hp ly S W regs mem md p n_old n ch (acall_pre_x_xs_cf segs B ly S Hp W regs mem md ch HPRE)
  Hin H10 Hhid H11 Hn Hlive Htr) as H0.
cbv beta in H0 |- *.
eapply amreal_mono; [|exact H0].
intros r W' c' [HL HN]. split; [exact (realloc_leaf_cf_x Hp ly S W regs mem md p n_old n r W' c' HL) | exact HN].
Qed.

(* The NULL arm of aj_realloc_x at the cf instance gives malloc_cf_null_post at the call. *)
Lemma realloc_x_null_post_cf : forall Hp ly S W regs mem md ch p n_old n tr S2 W2 c2,
acall_pre_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) (QMm_cf segs B)
  ly S Hp W regs mem md ch ->
In (p, n_old) (blocks S) ->
mt_refused malloc_cf free_cf n tr S S2 ->
realloc_leaf_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) xs_cf
  Hp ly S W regs mem md p n_old n (PNull, S2) W2 c2 ->
malloc_cf_null_post segs B ly S Hp W regs mem md n (PNull, S2) W2 c2.
Proof.
intros Hp ly S W regs mem md ch p n_old n tr S2 W2 c2 HPRE Hin Href HL.
exact (realloc_cf_null_post_of_leaf segs B ly S Hp W regs mem md ch p n_old n tr S2 W2 c2
  (acall_pre_x_xs_cf segs B ly S Hp W regs mem md ch HPRE) Hin Href
  (realloc_leaf_x_xs_cf Hp ly S W regs mem md p n_old n (PNull, S2) W2 c2 HL)).
Qed.

(* YGcfAmx2.v's realloc_cf_atok walk, with the post Wf_cf U at the result instead of realloc_post_cf: the realloc tree
   keeps the instance invariant at every universe U (free(NULL), malloc, and on success free p, each by its model
   law at U). Its only use: the depot step below, at U = univ_at. *)
Lemma realloc_cf_atok_wf : forall U s p n_old n tr,
universe_ok U -> Wf_cf U s -> YGcfRoomPre.ROOM_cf s -> In (p, n_old) (blocks s) -> 1 <= n < cf_malloc_max ->
blocks_bytes s + n <= LIVE_MAX -> admits U tr s ->
(forall s1 trc r, Wf_cf U s1 -> YGcfAmx2.nfr s s1 -> apath (malloc_cf n tr s1) trc r -> batch_room_cf (snd r)) ->
atok_cf true (realloc_tree_with malloc_cf free_cf p n tr s) (fun _ r => Wf_cf U (snd r)).
Proof.
intros U s p n_old n tr HU W HR Hp Hn Hlive Htr HK.
unfold realloc_tree_with. apply atok_cf_bind.
assert (A1 : atok_cf true (free_cf PNull tr s) (free_post_ycf U s PNull 0)).
{ unfold YGcfRoomPre.ROOM_cf in HR. destruct HR as (_ & _ & HB). eapply YG03dcf.ml_free_cf; eauto. }
eapply atok_cf_mono; [|exact (YGcfAmx.atok_cf_ipost _ _ _ _ (YGcfAmx.atok_cf_ipost _ _ _ _ A1
  (YGcfAmx2.ipost_free_null tr s)) (YGcfAmx2.ipost_free_null_depot tr s))].
intros b [[] s1] [[F1 N1] D1]. cbn [fst snd] in *.
pose proof (admits_keep U tr s s1 Htr (or_introl D1)) as Htr1.
unfold free_post_ycf in F1. cbn [snd] in F1. destruct F1 as (W1 & _ & _ & _ & (l1 & l2 & Bs1 & Bl1) & _).
assert (B1 : blocks s1 = blocks s).
{ rewrite Bl1. destruct Bs1 as [[_ E]|E]; [exact E|].
  exfalso. apply (YGcfAmx2.no_null_block _ _ _ _ s 0 W). rewrite E. apply in_or_app. right. left. reflexivity. }
pose proof (YGcfAmx2.ROOM_cf_nfr s s1 N1 HR) as HR1. unfold YGcfRoomPre.ROOM_cf in HR1. destruct HR1 as (HS1 & HE1 & HB1).
assert (Hlive1 : blocks_bytes s1 + n <= LIVE_MAX)
  by (rewrite YGcfAmx2.blocks_bytes_blocks, B1, <- YGcfAmx2.blocks_bytes_blocks; exact Hlive).
pose proof (YGcfAmx.atok_cf_ipost _ _ _ _ (malloc_ok_cf U s1 n tr HU W1 ltac:(lia) Hlive1 Htr1 HS1 HE1 HB1)
  (YGcfAmx.dep_malloc_cf n tr s1)) as A2.
pose proof (YGcfAmx2.atok_cf_with_path _ _ _ _ A2) as A2p.
assert (A2b : atok_cf b (malloc_cf n tr s1) (fun b0 a => (malloc_post_cf U s1 n b0 a /\
  (st_depot (snd a) = st_depot s1 \/ st_depot (snd a) = st_depot s1 ++ [tr])) /\ exists trc, apath (malloc_cf n tr s1) trc a)).
{ apply YGcfAmx2.atok_cf_any_ns; [intros b1 b2 a H; exact H | exact A2p]. }
apply atok_cf_bind. eapply atok_cf_mono; [|exact A2b].
intros b2 [q s2] [[M2 D2] [trc Hpath]]. cbn [fst snd] in D2.
pose proof (admits_keep U tr s1 s2 Htr1 D2) as Htr2.
unfold malloc_post_cf in M2. cbv beta iota in M2. destruct M2 as (W2 & _ & _ & _ & Bl2 & _).
assert (HB2 : batch_room_cf s2) by exact (HK s1 trc (q, s2) W1 N1 Hpath).
assert (SUCC : forall q', blocks s2 = blocks s1 ++ [(q', n)] ->
  atok_cf b2 ((YG00.bind (free_cf p tr) (fun _ => YG00.ret q')) s2) (fun _ r => Wf_cf U (snd r))).
{ intros q' Bq. apply atok_cf_bind.
  assert (Hp2 : In (p, n_old) (blocks s2)) by (rewrite Bq, B1; apply in_or_app; left; exact Hp).
  assert (A3 : atok_cf true (free_cf p tr s2) (free_post_ycf U s2 p n_old)) by (eapply YG03dcf.ml_free_cf; eauto).
  assert (A3b : atok_cf b2 (free_cf p tr s2) (free_post_ycf U s2 p n_old))
    by (apply YGcfAmx2.atok_cf_any_ns; [intros b1 b3 a H; exact H | exact A3]).
  eapply atok_cf_mono; [|exact A3b]. intros b3 [[] s3] F3. cbn [fst snd]. apply atok_cf_ret.
  unfold free_post_ycf in F3. cbn [snd] in F3. exact (proj1 F3). }
destruct q as [|qo|qr qo|qc qp].
- apply atok_cf_ret. exact W2.
- apply SUCC. exact (proj1 Bl2).
- apply SUCC. exact (proj1 Bl2).
- apply SUCC. exact (proj1 Bl2).
Qed.

(* The realloc model law of the generic rule (YGcallRx.v's RMX) at the cf instance, for every headroom k. The depot
   step: realloc_cf_atok_wf holds at EVERY universe, so it is run at YGcallx.v's univ_at (the call's depot plus its
   trace), with the inner malloc's batch room as in YGcfAmx2.amx_realloc_cf_k; the post's Wf_cf there bounds the new
   depot (univ_at_step). *)
Lemma realloc_model_law_x_cf : forall k, universe_ok (as_universe B) ->
realloc_model_law_x B (fun s _ _ => qtight s /\ YGcfRoomKeep.ROOM_cf_k s (YGcfRoomKeep.RK_realloc + k))
  malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)).
Proof.
intros k HU s p n_old n tr HW (HQ & HRk) Hp Hn Hlive Htr.
destruct (YGcfAmx2.amx_realloc_cf B s p n_old n tr k HU HW HQ HRk Hp Hn Hlive Htr) as (H1 & H2 & H3 & H4).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
intros tr' r Hpath.
pose proof (wfc_depot _ _ _ _ _ HW) as Hd.
assert (HR : YGcfRoomPre.ROOM_cf s).
{ apply YGcfRoomKeep.RK_zero. apply (YGcfRoomKeep.RK_mono s (YGcfRoomKeep.RK_realloc + k) 0); [lia | exact HRk]. }
assert (HK : forall s1 trc r, Wf_cf (univ_at (st_depot s) tr) s1 -> YGcfAmx2.nfr s s1 -> apath (malloc_cf n tr s1) trc r ->
  batch_room_cf (snd r)).
{ intros s1 trc [q s'] W1 N1 Hp1. cbn [snd].
  assert (R1 : YGcfRoomKeep.ROOM_cf_k s1 (S (S k))) by exact (YGcfAmx2.ROOM_cf_k_nfr s s1 _ N1 HRk).
  pose proof (YGcfRoomStep.malloc_room_keep_cf (S k) n tr s1 trc q s'
    (YGcfRoomStep.room_shape_cf_of_WfP_cf _ _ _ _ _ W1) R1 Hp1) as R2.
  apply (YGcfRoomKeep.RK_mono _ _ 0) in R2; [|lia]. apply YGcfRoomKeep.RK_zero in R2. exact (proj2 (proj2 R2)). }
pose proof (realloc_cf_atok_wf (univ_at (st_depot s) tr) s p n_old n tr (univ_at_ok _ _ _ HU Hd Htr)
  (Wf_cf_univ _ _ _ HW (univ_at_fits _ _ tr Hd)) HR Hp Hn Hlive (univ_at_admits _ _ _ Htr) HK) as A.
destruct (atok_cf_apath _ _ _ tr' r A Hpath) as (ns & WV).
exact (univ_at_step _ _ _ (wfc_depot _ _ _ _ _ WV)).
Qed.

(* ---------------------------------------------------------------------------- *)
(* The cf bridge of the rules over R (YGcallRx.v section 3R).                      *)

(* The primed realloc leaf is the generic leaf over R at APOST := APOST_cf, XS := xs_cf. *)
Lemma realloc_leaf_cf_xR : forall Hp ly S W regs mem md p n_old n r W' c',
YG0dcfR.realloc_leaf_cf_rh segs B ly S Hp W regs mem md p n_old n r W' c' ->
realloc_leaf_xR segs B xs_cf (APOST_cf segs B) Hp ly S W regs mem md p n_old n r W' c'.
Proof.
intros Hp ly S W regs mem md p n_old n [q S2] W' c'
(ly' & regs' & mem' & md' & Hc & Hpost & Hres & HQT & Hcopy & Herr & HX & HE & HR).
cbn [fst snd] in *.
destruct Hpost as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
exists ly', regs', mem', md'. cbn [fst snd]. split; [exact Hc|]. split; [exact Hres|]. split; [exact HQT|].
split; [|split; [|exact (conj HE HR)]].
- intros Eq. subst q. cbn [realloc_hp_cf] in A1. split; [|exact (Herr eq_refl)].
  refine (conj (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj _ A7)))))) HX).
  intros a Ha N1 N2 N3 N4 N5. apply (A6 a Ha N1 N2 N3); [|exact N5].
  intros [[Hf _] | [[Hf _] | HXa]]; [exact (Hf eq_refl) | exact (Hf eq_refl) | exact (N4 HXa)].
- intros Hq. rewrite (realloc_hp_cf_nn ly p q Hp Hq) in A1. split; [|exact (Hcopy Hq)].
  refine (conj (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj _ A7)))))) HX).
  intros a Ha N1 N2 N3 N4 N5. apply (A6 a Ha N1 N2 N3); [|exact N5].
  intros [[_ H] | [[_ H] | H]]; apply N4; [left; exact H | right; left; exact H | right; right; exact H].
Qed.

(* And back: the generic leaf over R at APOST_cf is the primed realloc leaf. *)
Lemma realloc_leaf_x_xs_cfR : forall Hp ly S W regs mem md p n_old n r W' c',
realloc_leaf_xR segs B xs_cf (APOST_cf segs B) Hp ly S W regs mem md p n_old n r W' c' ->
YG0dcfR.realloc_leaf_cf_rh segs B ly S Hp W regs mem md p n_old n r W' c'.
Proof.
intros Hp ly S W regs mem md p n_old n [q S2] W' c' (ly' & regs' & mem' & md' & Hc & Hres & HQT & LN & LS & HE & HR).
cbn [fst snd] in *.
destruct (asptr_null_dec q) as [-> | Hq].
- destruct (LN eq_refl) as (((A1 & A2 & A3 & A4 & A5 & A6 & A7) & HX) & Herr & Hoom).
  exists ly', regs', mem', md'. cbn [fst snd]. split; [exact Hc|].
  split.
  { cbn [realloc_hp_cf]. refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj _ A7)))))).
    intros a Ha N1 N2 N3 N4 N5. apply (A6 a Ha N1 N2 N3); [|exact N5]. intros HXa. apply N4. right. right. exact HXa. }
  split; [exact Hres|]. split; [exact HQT|]. split; [intros Hf; exfalso; exact (Hf eq_refl)|].
  split; [intros _; exact (conj Herr Hoom) | exact (conj HX (conj HE HR))].
- destruct (LS Hq) as (((A1 & A2 & A3 & A4 & A5 & A6 & A7) & HX) & Hcopy).
  exists ly', regs', mem', md'. cbn [fst snd]. split; [exact Hc|].
  split.
  { rewrite (realloc_hp_cf_nn ly p q Hp Hq). refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj _ A7)))))).
    intros a Ha N1 N2 N3 N4 N5. apply (A6 a Ha N1 N2 N3); [|exact N5].
    intros [H | [H | H]]; apply N4; [left; exact (conj Hq H) | right; left; exact (conj Hq H) | right; right; exact H]. }
  split; [exact Hres|]. split; [exact HQT|]. split; [intros _; exact Hcopy|].
  split; [intros E; exfalso; exact (Hq E) | exact (conj HX (conj HE HR))].
Qed.

(* The cgif layer's primed realloc row, for every ghost set and headroom, gives the generic text over R at
   R := wle' segs RZ_cf, APOST := APOST_cf, with the room RQ := qtight /\ ROOM_cf_k (RK_realloc + k) /\ cf_hull_adm:
   the row's entry room and entry hull admission are RQ's last two conjuncts; the post's room is dropped. *)
Lemma arealloc_realizes_x_cfR : forall pc, (forall Hp k, YGcfInstReallocK.arealloc_realizes_cf_k segs B Hp pc k) ->
forall k,
arealloc_realizes_xR segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) (QMm_cf segs B) (fun s n _ => qtight s /\ YGcfRoomKeep.ROOM_cf_k s (YGcfRoomKeep.RK_realloc + k) /\ cf_hull_adm s n)
  malloc_cf cf_malloc_max free_cf xs_cf (wle' segs YGcfRehidePost.RZ_cf) (APOST_cf segs B) pc cf_pc_realloc_ra0.
Proof.
intros pc H k Hp ly S W regs mem md p n_old n ch HPRE (_ & HRk & HADM) Hin H10 Hhid H11 Hn Hlive Htr.
pose proof (H Hp k ly S W regs mem md p n_old n ch (acall_pre_x_xs_cf segs B ly S Hp W regs mem md ch HPRE) HRk
  Hin H10 Hhid H11 Hn Hlive Htr HADM) as H0.
cbv beta in H0 |- *.
eapply (amrealG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [|exact H0].
intros r W' c' [[HL HN] _]. split; [exact (realloc_leaf_cf_xR Hp ly S W regs mem md p n_old n r W' c' HL) | exact HN].
Qed.

(* The realloc model law at the room of the rules over R (its third conjunct, the hull admission, is unused). *)
Lemma realloc_model_law_x_cfR : forall k, universe_ok (as_universe B) ->
realloc_model_law_x B (fun s n _ => qtight s /\ YGcfRoomKeep.ROOM_cf_k s (YGcfRoomKeep.RK_realloc + k) /\ cf_hull_adm s n)
  malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)).
Proof.
intros k HU s p n_old n tr HW (HQ & HRk & _).
exact (realloc_model_law_x_cf k HU s p n_old n tr HW (conj HQ HRk)).
Qed.

(* The NULL arm of the rules over R at the cf instance gives malloc_cf_null_post at the call: the refused path's dead
   set is empty (free_cf PNull keeps st_secs, the NULL malloc_cf hides nothing), so the leaf at APOST_cf is the leaf at
   acall_post_x, and realloc_x_null_post_cf applies. *)
Lemma realloc_x_null_post_cfR : forall Hp ly S W regs mem md ch p n_old n tr S2 W2 c2,
acall_pre_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) (QMm_cf segs B)
  ly S Hp W regs mem md ch ->
In (p, n_old) (blocks S) -> mt_refused malloc_cf free_cf n tr S S2 ->
realloc_leaf_xR segs B xs_cf (APOST_cf segs B) Hp ly S W regs mem md p n_old n (PNull, S2) W2 c2 ->
malloc_cf_null_post segs B ly S Hp W regs mem md n (PNull, S2) W2 c2.
Proof.
intros Hp ly S W regs mem md ch p n_old n tr S2 W2 c2 HPRE Hin Href HL.
pose proof Href as (S1 & t1 & t2 & Hp1 & _ & Hp2 & _).
assert (SS : st_secs S1 = st_secs S) by exact (YGcfSecsStep.secs_free_null_step tr S t1 S1 Hp1).
assert (DN : forall a, ~ YGcfRehidePost.dead_shadow_new ly S S2 a).
{ intros a HD. apply (YGcfNullCall.malloc_cf_null_dead_empty ly n tr S1 t2 S2 a Hp2).
  apply (YGcfRehidePost.dead_shadow_new_mono_l ly S S1 S2 a); [|exact HD].
  intros r sm0 Hr Hl. exists sm0. rewrite SS. split; [exact Hr|]. split; [exact Hl | reflexivity]. }
apply (realloc_x_null_post_cf Hp ly S W regs mem md ch p n_old n tr S2 W2 c2 HPRE Hin Href).
destruct HL as (ly' & regs' & mem' & md' & Hc & Hres & HQT & LN & LS & HE & HR).
cbn [fst snd] in Hc, Hres, HQT, LN, LS, HE, HR.
unfold realloc_leaf_x, realloc_leaf_xR.
exists ly', regs', mem', md'. cbn [fst snd].
split; [exact Hc|]. split; [exact Hres|]. split; [exact HQT|].
split; [|split; [intros Hf; exfalso; exact (Hf eq_refl) | exact (conj HE HR)]].
intros _. destruct (LN eq_refl) as ((HP & HX) & Herr & Hoom). split; [|exact (conj Herr Hoom)].
rewrite YGcfRehidePost.acall_post_cf_rh_unfold in HP. destruct HP as (AR & LL & WI & AP & IO & VW & ST).
refine (conj (conj AR HX) (conj LL (conj _ (conj AP (conj IO (conj _ ST)))))).
- hnf. intros a Ha. destruct (WI a Ha) as [H1 | H2]; [exact H1 | destruct (DN _ H2)].
- intros a Ha N1 N2 N3 N4. exact (VW a Ha N1 N2 N3 N4 (DN a)).
Qed.

(* YGcallRx.v's rules over R at the cf instance: R := wle' segs RZ_cf, APOST := APOST_cf with its laws POST_AR_cf /
   POST_J_cf (YGcallcf.v), the room RQ above, the text from the primed row (arealloc_realizes_x_cfR) and the model law
   realloc_model_law_x_cfR. The engine laws are the rules' own Section hypotheses at ARcf /\ xs_placed_cf. *)
Section instR.
Context {SK : YI16.sink_head}.
Variable PST : list (Z * Z).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : YCbq.api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).
Hypothesis WFL : ARx_wf_law segs (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) (Wf_cf (as_universe B)).
Hypothesis XSL : ARx_xs_law segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) xs_cf.
Hypothesis UOK : universe_ok (as_universe B).

Definition aj_realloc_at_x_cfR (k : nat) (pc : Z)
  (AREAL : forall Hp k, YGcfInstReallocK.arealloc_realizes_cf_k segs B Hp pc k) :=
  fun (WS : list (list Z)) => aj_realloc_at_xR (SK := SK) segs B PST (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) (QMm_cf segs B) (fun s n _ => qtight s /\ YGcfRoomKeep.ROOM_cf_k s (YGcfRoomKeep.RK_realloc + k) /\ cf_hull_adm s n)
    malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)) xs_cf LAWS segs_low errno_low WFL
    (realloc_model_law_x_cfR k UOK) XSL (wle' segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)
    (APOST_cf segs B) (POST_AR_cf segs B) (POST_J_cf (SK := SK) segs B LAWS segs_low errno_low OWNLOW)
    pc cf_pc_realloc_ra0 (arealloc_realizes_x_cfR pc AREAL k) (WS := WS).

Definition aj_realloc_x_cfR (k : nat) (pc : Z)
  (AREAL : forall Hp k, YGcfInstReallocK.arealloc_realizes_cf_k segs B Hp pc k) :=
  fun (WS : list (list Z)) => aj_realloc_xR (SK := SK) segs B PST (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S) (QMm_cf segs B) (fun s n _ => qtight s /\ YGcfRoomKeep.ROOM_cf_k s (YGcfRoomKeep.RK_realloc + k) /\ cf_hull_adm s n)
    malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)) xs_cf LAWS segs_low errno_low WFL
    (realloc_model_law_x_cfR k UOK) XSL (wle' segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)
    (APOST_cf segs B) (POST_AR_cf segs B) (POST_J_cf (SK := SK) segs B LAWS segs_low errno_low OWNLOW)
    pc cf_pc_realloc_ra0 (arealloc_realizes_x_cfR pc AREAL k) (WS := WS).
End instR.
End J.
End G.
