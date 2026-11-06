(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_ameta_iface MallocInv_tryavail MallocInv_free MallocInv_actw MallocInv_act MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_tav_iface MallocInv_tav2.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tav_owned : forall A B sc x, tavrel A B sc -> owned_of B x -> owned_of A x.
Proof. intros A B sc x TV [Hc | Hd]; [left; exact Hc | right]. apply (proj1 (tv_dom A B sc TV x)). exact Hd. Qed.

Lemma tav_chain : forall A B C sc s s1 s2,
  ntframe A s s1 -> tavrel A B sc -> ntframe B s1 s2 -> tavrel B C sc ->
  ntframe A s s2 /\ tavrel A C sc.
Proof.
  intros A B C sc s s1 s2 NF1 TV1 NF2 TV2. split.
  - apply (ntframe_trans A B s s1 s2 NF1 NF2); [intros x; apply (tav_owned A B sc x TV1) | exact (tv_live A B sc TV1)].
  - exact (tavrel_trans A B C sc TV1 TV2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Hdr.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.

  Lemma hdr_geom : 16 <= mt_stride mt /\ 1 <= mt_cnt mt /\ gext_lo mt = mt_mem mt /\ mt_mem mt + 28 <= gext_hi mt /\
                   0x1000 <= mt_mem mt /\ gext_hi mt + 4 <= alloc_ceiling.
  Proof.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (Hw32 & _ & Hsc & Hlen & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hmem & Hfit & Hce & _).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS. pose proof (w_last_range (mt_w32 mt)) as Hl.
    assert (Hc : 1 <= mt_cnt mt) by (unfold mt_cnt, mt_last; llia).
    assert (16 <= mt_cnt mt * mt_stride mt) by nia.
    unfold gext_lo, gext_hi. llia.
  Qed.

  (* [comment removed for export] *)
  Lemma fact_at_aib : forall f x, has A f -> f_a f <= x < f_a f + f_n f -> x = mt_mem mt + 8 ->
    f = FCT (mt_mem mt + 8) 1 aib.
  Proof.
    intros f x Hf Hx ->. pose proof hdr_geom as (HS & Hc & Glo & Ghi & _).
    pose proof (has_addr A HW f Hf) as (Hfn & _).
    destruct (fact_locate A HW ma mt aib slots Hma Hr f Hf) as [(fl & ->) | [Hh | [(j & st & Hj & Hin) | [(j & ch & Hj & Hlo & Hhi) | (Hm & Hg)]]]].
    - exfalso. cbn [f_a f_n] in Hx. pose proof (mfield_range fl). pose proof (meta_clear_of_gext A HW ma mt aib slots Hma Hr). llia.
    - destruct Hh as [<- | [<- | []]]; [exfalso; cbn [f_a f_n] in Hx; llia | reflexivity].
    - exfalso. pose proof (slot_fact_bounds A HW ma mt aib slots j st f Hma Hr Hj Hin) as [B1 B2].
      unfold slot_start, slot_start_g in B1. assert (0 <= Z.of_nat j * mt_stride mt) by nia. llia.
    - exfalso. unfold slot_start, slot_start_g in Hlo. assert (0 <= Z.of_nat j * mt_stride mt) by nia. llia.
    - exfalso. llia.
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_nolive : forall p n x, a_live A p = Some n -> mt_mem mt <= x < mt_mem mt + 16 -> ~ (p <= x < p + n).
  Proof.
    intros p n x Hp Hx Hin. apply (proj1 (wf_live_map A HW p n)) in Hp.
    destruct Hp as (mb & mtb & aibb & slb & i & off & Hmb & Hrb & Hi0 & Hi & ->).
    destruct (live_geom A HW mb mtb aibb slb i off n Hmb Hrb Hi0 Hi) as (q & Hq & Hn & Hoff & Hfit & _ & _ & G1 & G2 & G3 & G4 & _).
    pose proof (round16_ge n) as Hr16. pose proof hdr_geom as (HS & Hc & Glo & Ghi & _).
    destruct (wf_grp A HW mb mtb aibb slb Hmb Hrb) as (Hw32b & _ & Hscb & _). pose proof (stride_ge16 mtb ltac:(llia) Hscb) as HSb.
    destruct (Z.eq_dec ma mb) as [<- | Hne].
    - rewrite Hma in Hmb. injection Hmb as <-. unfold gext_lo in G1. llia.
    - destruct (wf_laminar A HW ma mt aib slots mb mtb aibb slb Hma Hr Hmb Hrb Hne)
        as [Hd | [Hd | [ (j & ch & Hj0 & Hj & Hjlo & Hjhi) | (j & ch & Hj0 & Hj & Hjlo & Hjhi) ]]].
      + unfold gext_lo in *. llia.
      + unfold gext_lo in *. llia.
      + (* [comment removed for export] *)
        unfold slot_start, slot_start_g, gext_lo in *. assert (0 <= j * mt_stride mt) by nia. llia.
      + (* [comment removed for export] *)
        assert (Hji : j <> i) by (intros ->; rewrite Hi in Hj; discriminate).
        unfold slot_start, slot_end, slot_start_g, slot_end_g, gext_lo, gext_hi in *.
        destruct (Z.lt_total j i) as [Hlt | [E | Hgt]]; [| exact (Hji E) |].
        * pose proof (slots_disjoint (mt_mem mtb) (mt_stride mtb) j i HSb Hj0 Hi0 Hlt). llia.
        * pose proof (slots_disjoint (mt_mem mtb) (mt_stride mtb) i j HSb Hi0 Hj0 Hgt). llia.
  Qed.

  Lemma hdr_dom : forall x, mt_mem mt <= x < mt_mem mt + 16 -> dom A x.
  Proof. intros x Hx. pose proof hdr_geom as (HS & Hc & Glo & Ghi & _). apply (grp_dom A ma mt aib slots x HW Hma Hr). llia. Qed.

  Lemma writes_ok_aib : forall ws v, writes_ok A ws -> writes_ok A (FCT (mt_mem mt + 8) 1 v :: ws).
  Proof.
    intros ws v H. apply writes_ok_cons; [exact H|]. cbn [f_a f_n]. intros x Hx. split; [left; apply hdr_dom; llia|].
    intros p n Hp. apply (hdr_nolive p n x Hp). llia.
  Qed.

  Lemma has_aib : has A (FCT (mt_mem mt + 8) 1 aib).
  Proof. right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. left. right. left. reflexivity. Qed.
End Hdr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AibExt.
  Variable B : astate.
  Hypothesis HW : WF B.
  Variables (sc m : Z) (rest : list Z) (mt : meta_rec) (aib : Z) (sl : list slot_st).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active B sc = m :: rest.
  Hypothesis Hm : a_meta B m = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib sl.
  Hypothesis Hav0 : mt_avail mt = 0.
  Variable aib' : Z.
  Hypothesis Haib' : 0 <= aib' < 256.
  Hypothesis Hge : aib mod 32 <= aib' mod 32.
  Hypothesis Hle : aib' mod 32 <= mt_last mt.

  Definition xa_mt : meta_rec := MT (gu_f mt (mt_avail mt) (mt_freed mt)) (RGroup aib' sl).
  Definition xaA : astate := set_live (ameta_upd B m xa_mt) (a_live B).

  Lemma xa_mt_f : forall fl, mt_f xa_mt fl = mt_f mt fl.
  Proof. intros fl. unfold xa_mt. rewrite mt_f_MT. destruct fl; reflexivity. Qed.
  Lemma xa_mt_role : mt_role xa_mt = RGroup aib' sl. Proof. reflexivity. Qed.
  Lemma xa_mt_w32 : mt_w32 xa_mt = mt_w32 mt. Proof. apply xa_mt_f. Qed.
  Lemma xa_mt_mem : mt_mem xa_mt = mt_mem mt. Proof. apply xa_mt_f. Qed.
  Lemma xa_mt_prev : mt_prev xa_mt = mt_prev mt. Proof. apply xa_mt_f. Qed.
  Lemma xa_mt_next : mt_next xa_mt = mt_next mt. Proof. apply xa_mt_f. Qed.
  Lemma xa_mt_avail : mt_avail xa_mt = mt_avail mt. Proof. apply xa_mt_f. Qed.
  Lemma xa_mt_freed : mt_freed xa_mt = mt_freed mt. Proof. apply xa_mt_f. Qed.
  Lemma xa_mt_sc : mt_sc xa_mt = mt_sc mt. Proof. unfold mt_sc. rewrite xa_mt_w32. reflexivity. Qed.
  Lemma xa_mt_cnt : mt_cnt xa_mt = mt_cnt mt. Proof. unfold mt_cnt, mt_last. rewrite xa_mt_w32. reflexivity. Qed.
  Lemma xa_mt_last : mt_last xa_mt = mt_last mt. Proof. unfold mt_last. rewrite xa_mt_w32. reflexivity. Qed.

  Lemma xa_grp : 0 <= mt_w32 mt < 2^64 /\ Z.of_nat (length sl) = mt_cnt mt /\
    0 <= mt_freed mt < 2 ^ (mt_cnt mt) /\ 0 <= aib < 256 /\ aib mod 32 <= mt_last mt /\ mt_cnt mt <= 32 /\ mt_sc mt = sc.
  Proof.
    destruct (wf_grp B HW m mt aib sl Hm Hr) as (H1 & _ & _ & H4 & _ & H6 & _ & H8 & _ & H10 & _).
    destruct (wf_act_mem B HW sc m ltac:(rewrite Hact; left; reflexivity)) as (mt' & aibx & sl' & Hm' & _ & Hs). rewrite Hm in Hm'. injection Hm' as <-.
    pose proof (w_last_range (mt_w32 mt)) as Hl.
    assert (Hc : mt_cnt mt <= 32) by (unfold mt_cnt, mt_last in *; llia).
    repeat split; auto; llia.
  Qed.

  Theorem WF_xaA : WF xaA.
  Proof.
    pose proof xa_grp as (Hw & Hlen & Hfr & Haib & Haibl & Hc & Hs).
    destruct (wf_grp B HW m mt aib sl Hm Hr) as (_ & _ & _ & _ & Hav & _ & Hdisj & _ & _ & _ & Hidle & _).
    apply (WF_grp_upd B HW m mt aib sl Hm Hr (mt_avail mt) (mt_freed mt) aib' sl (a_live B)).
    - reflexivity.
    - intros j st st' Hj Hj'. rewrite Hj in Hj'. injection Hj' as <-. left. reflexivity.
    - exact Hav.
    - exact Hfr.
    - exact Hdisj.
    - exact Haib'.
    - rewrite Hav0. apply Z.pow_pos_nonneg; llia.
    - exact Hle.
    - exact Hidle.
    - intros j off n Hj Hj0. exact (wf_live B HW m mt aib sl j off n Hm Hr Hj Hj0).
    - intros j Hj. apply (wf_inactive B HW m mt aib sl j Hm Hr). llia.
    - rewrite Hs, Hact. cbn [hd]. intros _ Hne. exfalso. exact (Hne eq_refl).
    - intros H. llia.
    - intros _ Hnz. left. exact Hnz.
    - intros q n. rewrite (wf_live_map B HW q n). unfold is_live. split.
      + intros (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & E).
        destruct (Z.eq_dec x m) as [-> | Hne].
        * left. rewrite Hm in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-. exists j, off. auto.
        * right. exists x, mtx, aibx, slx, j, off. auto 10.
      + intros [(j & off & Hj0 & Hj & E) | (x & mtx & aibx & slx & j & off & Hne & Hx & Hrx & Hj0 & Hj & E)].
        * exists m, mt, aib, sl, j, off. auto 10.
        * exists x, mtx, aibx, slx, j, off. auto 10.
  Qed.

  Lemma xaA_meta_same : a_meta xaA m = Some xa_mt.
  Proof. unfold xaA, set_live, ameta_upd, set_meta. cbn. apply aupd_same. Qed.
  Lemma xaA_meta_other : forall x, x <> m -> a_meta xaA x = a_meta B x.
  Proof. intros x Hne. unfold xaA, set_live, ameta_upd, set_meta. cbn. apply aupd_other. exact Hne. Qed.
  Lemma xaA_meta_inv : forall x mtx, a_meta xaA x = Some mtx -> (x = m /\ mtx = xa_mt) \/ (x <> m /\ a_meta B x = Some mtx).
  Proof.
    intros x mtx Hx. destruct (Z.eq_dec x m) as [-> | Hne].
    - left. rewrite xaA_meta_same in Hx. injection Hx as <-. auto.
    - right. rewrite (xaA_meta_other x Hne) in Hx. auto.
  Qed.

  Lemma xaA_ctx : a_ctx xaA = a_ctx B. Proof. reflexivity. Qed.
  Lemma xaA_active : a_active xaA = a_active B. Proof. reflexivity. Qed.
  Lemma xaA_areas : a_areas xaA = a_areas B. Proof. reflexivity. Qed.
  Lemma xaA_freelist : a_freelist xaA = a_freelist B. Proof. reflexivity. Qed.
  Lemma xaA_live : a_live xaA = a_live B. Proof. reflexivity. Qed.
  Lemma xaA_xmaps : a_xmaps xaA = a_xmaps B. Proof. reflexivity. Qed.
  Lemma xaA_pages : a_pages xaA = a_pages B. Proof. reflexivity. Qed.
  Lemma xaA_mblocks : a_mblocks xaA = a_mblocks B. Proof. reflexivity. Qed.
  Lemma xaA_brk_lo : a_brk_lo xaA = a_brk_lo B. Proof. reflexivity. Qed.

  Lemma dom_xaA : forall x, dom xaA x <-> dom B x.
  Proof. exact (dom_grp_upd B m mt aib sl Hm Hr (mt_avail mt) (mt_freed mt) aib' sl (a_live B)). Qed.
  Lemma VMok_xaA : forall h, VMok B h -> VMok xaA h.
  Proof. exact (VMok_grp_upd B m mt aib sl Hm Hr (mt_avail mt) (mt_freed mt) aib' sl (a_live B)). Qed.

  Lemma meta_usage_xaA : forall c x, meta_usage xaA c x = meta_usage B c x.
  Proof.
    intros c x. unfold meta_usage. destruct (Z.eq_dec x m) as [-> | Hne].
    - rewrite xaA_meta_same, Hm, Hr. cbn [mt_role xa_mt MT]. rewrite xa_mt_sc, xa_mt_cnt. reflexivity.
    - rewrite (xaA_meta_other x Hne). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma has_xaA : forall f, has xaA f -> has B f \/ f = FCT (mt_mem mt + 8) 1 aib'.
  Proof.
    intros f Hf.
    destruct (has_grp_upd B m mt (mt_avail mt) (mt_freed mt) aib' sl (a_live B) f Hf) as [[HfB _] | [[fl ->] | [Hhdr | (j & st & Hj & Hin)]]].
    - left. exact HfB.
    - left. right; right; left. exists m, mt, fl. split; [exact Hm|]. destruct fl; reflexivity.
    - destruct Hhdr as [<- | [<- | []]]; [left | right; reflexivity].
      right; right; right. exists m, mt, aib, sl. split; [exact Hm|]. split; [exact Hr|]. left. left. reflexivity.
    - left. right; right; right. exists m, mt, aib, sl. split; [exact Hm|]. split; [exact Hr|]. right. exists j, st. auto.
  Qed.

  Lemma tavrel_xaA : tavrel B xaA sc.
  Proof.
    constructor; try reflexivity; try tauto.
    - intros x mtx aibx slx Hx Hrx. destruct (xaA_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')].
      + exists mt, aib. cbn in Hrx. injection Hrx as <- <-. split; [exact Hm|]. split; [exact Hr|]. split; [symmetry; apply xa_mt_w32 | symmetry; apply xa_mt_mem].
      + exists mtx, aibx. auto.
    - intros x mt0 aib0 slx Hx Hrx. destruct (Z.eq_dec x m) as [-> | Hne].
      + rewrite Hm in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
        exists xa_mt, aib'. split; [apply xaA_meta_same|]. split; [reflexivity|]. split; [symmetry; apply xa_mt_w32 | symmetry; apply xa_mt_mem].
      + exists mt0, aib0. rewrite (xaA_meta_other x Hne). auto.
    - intros x mt0 Hx Hng. destruct (Z.eq_dec x m) as [-> | Hne]; [exfalso; rewrite Hm in Hx; injection Hx as <-; exact (Hng aib sl Hr)|].
      rewrite (xaA_meta_other x Hne). exact Hx.
    - intros x mtx Hx Hng. destruct (xaA_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')]; [exfalso; exact (Hng aib' sl eq_refl) | exact Hx'].
    - exact dom_xaA.
  Qed.

  (* [comment removed for export] *)
  Lemma xaA_commit : forall m0 mm, RepW B m0 [FCT (mt_mem mt + 8) 1 aib'] mm -> Rep xaA mm.
  Proof.
    intros m0 mm RW. pose proof WF_xaA as HW'.
    apply (repw_commit B xaA m0 _ mm RW).
    - intros x b (f & Hf & Hfb). destruct (has_xaA f Hf) as [HfB | ->]; [left; exists f; auto | right].
      destruct Hfb as [Hx _]. cbn [f_a f_n] in Hx. rewrite wlook_hit by (cbn [f_a f_n]; llia). discriminate.
    - intros x b (f & Hf & [Hx ->]) Hw.
      destruct (wlook [FCT (mt_mem mt + 8) 1 aib'] x) as [b'|] eqn:E; [| exfalso; exact (Hw eq_refl)].
      destruct (wlook_some_cov _ _ _ E) as (w & [<- | []] & Hxw). cbn [f_a f_n] in Hxw. rewrite <- E.
      pose proof (fact_at_aib xaA HW' m xa_mt aib' sl xaA_meta_same eq_refl f x Hf Hx ltac:(rewrite xa_mt_mem; llia)) as ->.
      rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite xa_mt_mem. reflexivity.
    - intros x Hx. apply (proj1 (dom_xaA x)). exact Hx.
  Qed.
End AibExt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tavrel_rotA : forall A sc h rest mth, WF A -> 0 <= sc < 48 -> a_active A sc = h :: rest -> a_meta A h = Some mth ->
  tavrel A (rotA A sc h rest) sc.
Proof.
  intros A sc h rest mth HW Hsc Hact Hh.
  apply (tavrel_of_tkeep A (rotA A sc h rest) sc (tkeep_rotA A HW sc h rest mth Hsc Hact Hh)); try reflexivity.
  intros x Hx. rewrite (rotA_active_sc A sc h rest) in Hx. rewrite Hact. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
Qed.

Section TavRot.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Variables (sc h : Z) (rest : list Z) (mth : meta_rec).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active A sc = h :: rest.
  Hypothesis Hh : a_meta A h = Some mth.
  Hypothesis Hav0 : mt_avail mth = 0.
  Hypothesis Hfr0 : mt_freed mth <> 0.
  Implicit Types (P : R -> mstate -> Prop).

  Let A1 := rotA A sc h rest.

  Theorem ts_tav_rotate : forall (K : unit -> M R) P,
    (forall s', II sp0 argv envp cb D A1 s' -> ntframe A s s' -> tavrel A A1 sc -> tsafe (K tt s') P) ->
    tsafe ((x <- m_sd (Z_to_bv 64 (caddr (KActive sc))) (Z_to_bv 64 (mt_next mth)) ;; K x) s) P.
  Proof.
    intros K P HK. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (rot_next_range sp0 argv envp cb D A s HII sc h rest mth Hsc Hact Hh) as [N1 N2]. ceil.
    pose proof (repw_init A (ms_mem s) HW HR) as RW0.
    unfold m_sd. eapply (ts_sd_ctxW A s (ms_mem s) [] (KActive sc)); [exact RW0 | exact HWIN | exact Hsc | reflexivity |].
    intros m1 RW1. rewrite uZ in RW1 by llia.
    pose proof (WF_rotA A HW sc h rest mth Hsc Hact Hh Hav0 Hfr0) as HW1. fold A1 in HW1.
    pose proof (tkeep_rotA A HW sc h rest mth Hsc Hact Hh) as TK. fold A1 in TK.
    assert (WO : writes_ok A [FCT (caddr (KActive sc)) (clen (KActive sc)) (mt_next mth)]) by (apply (writes_ok_ctx A [] (KActive sc) _ HW (writes_ok_nil A) Hsc)).
    assert (HR1 : Rep A1 m1).
    { apply (repw_commit2 A A1 (ms_mem s) _ m1 HW1 RW1).
      - intros f Hf. destruct (has_rotA A HW sc h rest mth Hsc Hact Hh f Hf) as [(Hf0 & _) | ->]; [left; exact Hf0 | right].
        cbn [f_a f_n]. intros x Hx. apply (wlook_cov_some _ (FCT (caddr (KActive sc)) (clen (KActive sc)) (mt_next mth)) x); [left; reflexivity | cbn [f_a f_n clen]; llia].
      - intros x b Hw. right; left. destruct (wlook_some_cov _ _ _ Hw) as (w & [<- | []] & Hxw). cbn [f_a f_n clen] in Hxw.
        rewrite wlook_hit in Hw by (cbn [f_a f_n clen]; llia). injection Hw as <-. cbn [f_v f_a].
        exists (KActive sc). split; [exact Hsc|]. cbn [clen]. split; [llia|].
        unfold A1. rewrite (rotA_ctx_valid A HW sc h rest mth Hsc Hact Hh (KActive sc) Hsc).
        destruct (cslot_eq_dec (KActive sc) (KActive sc)); [reflexivity | contradiction].
      - intros x Hx. apply (proj1 (dom_rotA A sc h rest x)). exact Hx. }
    apply (HK (upd s m1 (ms_vm s))).
    - apply II_intro.
      + exact (IS_commit sp0 argv envp cb A A1 s _ m1 HI RW1 WO HW1 HR1).
      + cbn [ms_vm upd]. apply (VMok_rotA A sc h rest). exact (ii_vm HII).
      + apply (tk_AvOK A A1 sc TK (ii_av HII)). apply (tk_ctx _ _ _ TK); [exact I | discriminate | discriminate].
      + apply (tk_UsOK A A1 sc TK (ii_us HII)). intros c Hc. apply (tk_ctx _ _ _ TK); [exact Hc | discriminate | discriminate].
      + apply (tk_deads A A1 sc TK). exact (ii_dd HII).
    - exact (ntframe_commit A s _ m1 HW RW1 WO).
    - exact (tavrel_rotA A sc h rest mth HW Hsc Hact Hh).
  Qed.
End TavRot.

End WithLayout.
