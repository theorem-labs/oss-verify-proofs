(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_membuffer_assign.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Notation L := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation lbrm k LB := (lb_remove (ai_K_eqb rsegs AI) k LB).

  Definition bsub (OB LB : list BLK) : Prop := forall b, In b OB -> In b LB.

  #[using="Type"] Lemma in_lb_remove : forall (b : BLK) k LB, In b LB -> blk_id b <> k -> In b (lbrm k LB).
  Proof.
    intros b k LB. induction LB as [|b0 LB IH]; intros HIN NE; [destruct HIN|].
    unfold lb_remove in *. rewrite list.filter_cons. destruct (decide _) as [D|D].
    - destruct HIN as [->|H]; [left; reflexivity| right; apply IH; assumption].
    - destruct HIN as [->|H]; [| apply IH; assumption]. exfalso. apply D.
      destruct (ai_K_eqb rsegs AI (blk_id b) k) eqn:Q; [| exact I].
      apply (proj1 (ai_K_eqb_eq rsegs AI (blk_id b) k)) in Q. contradiction.
  Qed.

  #[using="Type"] Lemma bsub_remove : forall (b : BLK) OB LB,
    bsub (b :: OB) LB -> NoDup (map blk_id (b :: OB)) -> bsub OB (lbrm (blk_id b) LB).
  Proof.
    intros b OB LB SUB ND b' Hb'. apply in_lb_remove; [apply SUB; right; exact Hb'|].
    cbn in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite <- E.
    apply base.list_elem_of_In. apply in_map. exact Hb'.
  Qed.

  #[using="Type"] Lemma bsub_remove_mid : forall (b : BLK) OB1 OB2 LB,
    bsub (OB1 ++ b :: OB2) LB -> NoDup (map blk_id (OB1 ++ b :: OB2)) -> bsub (OB1 ++ OB2) (lbrm (blk_id b) LB).
  Proof.
    intros b OB1 OB2 LB SUB ND b' Hb'. apply in_lb_remove.
    - apply SUB. apply in_app_or in Hb'. apply in_or_app. destruct Hb'; [left; assumption| right; right; assumption].
    - rewrite map_app in ND. cbn in ND. apply list.NoDup_app in ND. destruct ND as (ND1 & DJ & ND2).
      intros E. apply in_app_or in Hb'. destruct Hb' as [H1|H2].
      + apply (DJ (blk_id b')). { apply base.list_elem_of_In. apply in_map. exact H1. } rewrite E. left.
      + inversion ND2 as [|x l NI ND']; subst. apply NI. rewrite <- E. apply base.list_elem_of_In. apply in_map. exact H2.
  Qed.

  #[using="Type"] Lemma nodup_remove_mid : forall (b : BLK) (OB1 OB2 : list BLK),
    NoDup (map blk_id (OB1 ++ b :: OB2)) -> NoDup (map blk_id (OB1 ++ OB2)).
  Proof.
    intros b OB1 OB2 ND. rewrite map_app in *. cbn in ND. apply list.NoDup_app in ND. destruct ND as (ND1 & DJ & ND2).
    apply list.NoDup_app. split; [exact ND1|]. split.
    - intros x H1 H2. apply (DJ x H1). right. exact H2.
    - inversion ND2; assumption.
  Qed.

  #[using="Type"] Lemma fresh_nodup : forall s (b : BLK) LB OB m,
    RHEAP rsegs AI s (b :: LB) m -> bsub OB LB -> NoDup (map blk_id OB) -> NoDup (map blk_id (b :: OB)).
  Proof.
    intros s b LB OB m HR SUB ND. cbn. constructor; [| exact ND].
    pose proof (ai_blocks_nodup rsegs AI _ _ _ HR) as NDL. cbn in NDL. inversion NDL as [|x l NI ND']; subst.
    intros HIN. apply NI. apply base.list_elem_of_In. apply base.list_elem_of_In in HIN.
    apply in_map_iff in HIN. destruct HIN as (b' & E & Hb'). rewrite <- E. apply in_map. apply SUB. exact Hb'.
  Qed.

  #[using="Type"] Lemma bsub_fresh : forall (b : BLK) LB OB, bsub OB LB -> bsub (b :: OB) (b :: LB).
  Proof. intros b LB OB SUB b' [<-|H]; [left; reflexivity| right; apply SUB; exact H]. Qed.

  #[using="Type"] Lemma bsub_app : forall OB1 OB2 LB, bsub (OB1 ++ OB2) LB <-> bsub OB1 LB /\ bsub OB2 LB.
  Proof.
    intros OB1 OB2 LB. unfold bsub. split.
    - intros H. split; intros b Hb; apply H; apply in_or_app; auto.
    - intros [H1 H2] b Hb. apply in_app_or in Hb. destruct Hb; auto.
  Qed.

  #[using="Type"] Lemma bsub_disjoint : forall s LB m OB (b1 b2 : BLK),
    RHEAP rsegs AI s LB m -> bsub OB LB -> NoDup (map blk_id OB) -> In b1 OB -> In b2 OB -> b1 <> b2 ->
    blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
  Proof.
    intros s LB m OB b1 b2 HR SUB ND H1 H2 NE. eapply (ai_blocks_disjoint rsegs AI); [exact HR| apply SUB; exact H1| apply SUB; exact H2| exact NE].
  Qed.

  #[using="Type"] Lemma nodup_in_neq : forall (OB1 OB2 : list BLK) b1 b2,
    NoDup (map blk_id (OB1 ++ OB2)) -> In b1 OB1 -> In b2 OB2 -> b1 <> b2.
  Proof.
    intros OB1 OB2 b1 b2 ND H1 H2 ->. rewrite map_app in ND. apply list.NoDup_app in ND. destruct ND as (_ & DJ & _).
    apply (DJ (blk_id b2)); apply base.list_elem_of_In; apply in_map; assumption.
  Qed.

  Fixpoint flseg (m : mem) (FB : list BLK) (N : Z) {struct FB} : Prop :=
    match FB with
    | [] => N = 0
    | b :: FB' => N <> 0 /\ b = (blk_id b, N, 24) /\
        exists (nx : Z) (j1 j2 : word), rw_cells rsegs m N [C8 (wz nx); C8 j1; C8 j2] /\ flseg m FB' nx
    end.

  #[using="Type"] Lemma flseg_shape : forall FB m N b, flseg m FB N -> In b FB -> b = (blk_id b, blk_addr b, 24) /\ blk_addr b <> 0.
  Proof.
    induction FB as [|b0 FB IH]; intros m N b FL Hb; [destruct Hb|]. cbn [flseg] in FL.
    destruct FL as (NZ & Eb & nx & j1 & j2 & _ & FL'). destruct Hb as [<-|Hb]; [| eapply IH; eauto].
    rewrite Eb. cbn. split; [reflexivity| exact NZ].
  Qed.

  #[using="Type"] Lemma flseg_transport : forall FB m m' W N,
    flseg m FB N -> munch W m m' -> wmono rsegs m m' ->
    (forall b, In b FB -> disjoint_from W (blk_addr b) 24) -> flseg m' FB N.
  Proof.
    induction FB as [|b FB IH]; intros m m' W N FL MU WM SEP; cbn [flseg] in *; [exact FL|].
    destruct FL as (NZ & EB & nx & j1 & j2 & NC & FL'). split; [exact NZ|]. split; [exact EB|].
    exists nx, j1, j2. split.
    - eapply rw_cells_transport; [exact NC| exact MU| exact WM|]. specialize (SEP b (or_introl eq_refl)). rewrite EB in SEP. exact SEP.
    - eapply IH; [exact FL'| exact MU| exact WM|]. intros b0 H. apply SEP. right. exact H.
  Qed.

  Definition hd_addr (ns : list (BLK * Z)) (TAIL : Z) : Z := match ns with [] => TAIL | (b, _) :: _ => blk_addr b end.
  Fixpoint last_addr (ns : list (BLK * Z)) (pv : Z) : Z := match ns with [] => pv | (b, _) :: ns' => last_addr ns' (blk_addr b) end.

  Fixpoint dlseg (m : mem) (ns : list (BLK * Z)) (pv TAIL : Z) {struct ns} : Prop :=
    match ns with
    | [] => True
    | (b, it) :: ns' => blk_size b = 24 /\ blk_addr b <> 0 /\ blk_addr b <> TAIL /\ 0 <= it < 2^64 /\
        rw_cells rsegs m (blk_addr b) (node_cells pv (hd_addr ns' TAIL) it) /\ dlseg m ns' (blk_addr b) TAIL
    end.

  #[using="Type"] Lemma dlseg_transport : forall ns m m' W pv TAIL,
    dlseg m ns pv TAIL -> munch W m m' -> wmono rsegs m m' ->
    (forall b it, In (b, it) ns -> disjoint_from W (blk_addr b) 24) -> dlseg m' ns pv TAIL.
  Proof.
    induction ns as [|[b it] ns IH]; intros m m' W pv TAIL DL MU WM SEP; cbn [dlseg] in *; [exact I|].
    destruct DL as (SZ & NZ & NT & ITR & NC & DL'). split; [exact SZ|]. split; [exact NZ|]. split; [exact NT|]. split; [exact ITR|]. split.
    - eapply rw_cells_transport; [exact NC| exact MU| exact WM|]. eapply SEP. left. reflexivity.
    - eapply IH; [exact DL'| exact MU| exact WM|]. intros b0 it0 H. eapply SEP. right. exact H.
  Qed.

  #[using="Type"] Lemma dlseg_facts : forall ns m pv TAIL b it, dlseg m ns pv TAIL -> In (b, it) ns ->
    blk_size b = 24 /\ blk_addr b <> 0 /\ blk_addr b <> TAIL /\ 0 <= it < 2^64.
  Proof.
    induction ns as [|[b0 it0] ns IH]; intros m pv TAIL b it DL H; [destruct H|]. cbn [dlseg] in DL.
    destruct DL as (SZ & NZ & NT & ITR & NC & DL'). destruct H as [E|H]; [injection E as -> ->; auto| eapply IH; eauto].
  Qed.

  #[using="Type"] Lemma last_addr_app : forall ns1 ns2 pv, last_addr (ns1 ++ ns2) pv = last_addr ns2 (last_addr ns1 pv).
  Proof. induction ns1 as [|[b it] ns1 IH]; intros ns2 pv; cbn; [reflexivity| apply IH]. Qed.

  #[using="Type"] Lemma hd_addr_app : forall ns1 ns2 TAIL, ns1 <> [] -> hd_addr (ns1 ++ ns2) TAIL = hd_addr ns1 TAIL.
  Proof. intros [|[b it] ns1] ns2 TAIL H; [congruence| reflexivity]. Qed.

  #[using="Type"] Lemma dlseg_snoc : forall ns m m' W pv TAIL (bn : BLK) (IT : Z),
    dlseg m ns pv TAIL -> munch W m m' -> wmono rsegs m m' ->
    (forall b it, In (b, it) (removelast ns) -> disjoint_from W (blk_addr b) 24) ->
    (forall ns0 bl itl, ns = ns0 ++ [(bl, itl)] ->
       rw_cells rsegs m' (blk_addr bl) (node_cells (last_addr ns0 pv) (blk_addr bn) itl)) ->
    rw_cells rsegs m' (blk_addr bn) (node_cells (last_addr ns pv) TAIL IT) ->
    blk_size bn = 24 -> blk_addr bn <> 0 -> blk_addr bn <> TAIL -> 0 <= IT < 2^64 ->
    dlseg m' (ns ++ [(bn, IT)]) pv TAIL.
  Proof.
    induction ns as [|[b it] ns IH]; intros m m' W pv TAIL bn IT DL MU WM TR LASTN NCN SZN NZN NTN ITR.
    - cbn. repeat (split; [assumption|]). exact I.
    - cbn [dlseg app] in *. destruct DL as (SZ & NZ & NT & ITR0 & NC & DL').
      split; [exact SZ|]. split; [exact NZ|]. split; [exact NT|]. split; [exact ITR0|].
      destruct ns as [|[b2 it2] ns'] eqn:EN.
      +   cbn. split.
        * specialize (LASTN [] b it eq_refl). cbn in LASTN. exact LASTN.
        * cbn in NCN. repeat (split; [assumption|]). exact I.
      + rewrite <- EN in *. rewrite hd_addr_app by (rewrite EN; congruence). split.
        * eapply rw_cells_transport; [exact NC| exact MU| exact WM|]. eapply (TR b it). rewrite EN. cbn. destruct ns'; left; reflexivity.
        * eapply (IH m m' W); try eassumption.
          -- intros b0 it0 H. eapply TR. rewrite EN. rewrite EN in H. cbn [removelast]. cbn [removelast] in H.
             destruct ns' as [|x l]; [destruct H| right; exact H].
          -- intros ns0 bl itl E. specialize (LASTN ((b, it) :: ns0) bl itl ltac:(rewrite E; reflexivity)). cbn in LASTN. exact LASTN.
  Qed.

  #[using="Type"] Lemma dlseg_last_cells : forall ns0 m pv TAIL bl itl,
    dlseg m (ns0 ++ [(bl, itl)]) pv TAIL ->
    rw_cells rsegs m (blk_addr bl) (node_cells (last_addr ns0 pv) TAIL itl) /\ blk_size bl = 24 /\ blk_addr bl <> 0 /\ blk_addr bl <> TAIL.
  Proof.
    induction ns0 as [|[b it] ns0 IH]; intros m pv TAIL bl itl DL; cbn [dlseg app] in DL.
    - destruct DL as (SZ & NZ & NT & _ & NC & _). cbn in NC. auto.
    - destruct DL as (_ & _ & _ & _ & _ & DL'). cbn. eapply IH. exact DL'.
  Qed.

  #[using="Type"] Lemma dlseg_heap_pres : forall ns m m' (LBK : list BLK) SP pv TAIL,
    dlseg m ns pv TAIL -> heap_pres AI LBK SP m m' -> (forall b it, In (b, it) ns -> In b LBK) -> dlseg m' ns pv TAIL.
  Proof.
    induction ns as [|[b it] ns IH]; intros m m' LBK SP pv TAIL DL HP SUB; cbn [dlseg] in *; [exact I|].
    destruct DL as (SZ & NZ & NT & ITR & NC & DL'). repeat (split; [assumption|]). split.
    - eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact NC|].
      eapply client_range_block; [eapply SUB; left; reflexivity| lia| cbn; lia].
    - eapply IH; [exact DL'| exact HP|]. intros b0 it0 H. eapply SUB. right. exact H.
  Qed.

  Record hdr := mkHdr { hA : Z; hk : K; hid : Z; nA : Z; nlen : Z; ncap : Z; nk : K; vA : Z; vlen : Z; vcap : Z; vk : K }.
  Definition hblocks (h : hdr) : list BLK := [(hk h, hA h, 88); (vk h, vA h, vcap h + 1); (nk h, nA h, ncap h + 1)].

  Definition hdro_mem (m : mem) (h : hdr) : Prop :=
    (exists pad, rw_cells rsegs m (hA h) [C8 (wz (nA h)); C8 (wz (nlen h)); C4 (wz (hid h)); C4 pad])
    /\ rw_cells rsegs m (hA h + 24) (mbuf_cells (vA h) (vlen h) (vcap h))
    /\ (exists bs, rw_cells rsegs m (vA h) [CB (Z.to_nat (vcap h + 1)) bs] /\ nth_error bs (Z.to_nat (vlen h)) = Some (Z_to_bv 8 0))
    /\ rw_cells rsegs m (hA h + 56) (mbuf_cells (nA h) (nlen h) (ncap h))
    /\ (exists bs, rw_cells rsegs m (nA h) [CB (Z.to_nat (ncap h + 1)) bs] /\ nth_error bs (Z.to_nat (nlen h)) = Some (Z_to_bv 8 0)).

  Definition hdro_pure (h : hdr) : Prop :=
    1 <= vlen h <= vcap h /\ vcap h <= 6 * vlen h + 6 /\ 1 <= nlen h <= ncap h /\ ncap h <= nlen h + 5 /\ - 2^31 <= hid h < 2^31.
  Definition hdro (m : mem) (LB : list BLK) (h : hdr) : Prop := hdro_mem m h /\ hdro_pure h /\ bsub (hblocks h) LB.

  #[using="Type"] Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
  Proof.
    induction W as [|[lo hi] W IH]; intros A n A' n' D H1 H2; cbn in *; [exact I|].
    destruct D as [D1 D2]. split; [lia| eapply IH; eauto].
  Qed.

  Definition hregions (h : hdr) : list (Z * Z) := [(hA h, 88); (vA h, vcap h + 1); (nA h, ncap h + 1)].

  #[using="Type"] Lemma hregion_block : forall h A n, In (A, n) (hregions h) -> exists k, In (k, A, n) (hblocks h).
  Proof.
    intros h A n [E|[E|[E|[]]]]; injection E as <- <-; unfold hblocks.
    - exists (hk h). left. reflexivity.
    - exists (vk h). right. left. reflexivity.
    - exists (nk h). right. right. left. reflexivity.
  Qed.

  #[using="Type"] Lemma in_hdrs_blocks : forall hs h b, In h hs -> In b (hblocks h) -> In b (concat (map hblocks hs)).
  Proof.
    induction hs as [|h0 hs IH]; intros h b Hh Hb; [destruct Hh|]. change (In b (hblocks h0 ++ concat (map hblocks hs))). apply in_or_app.
    destruct Hh as [<-|Hh]; [left; exact Hb| right; eapply IH; eauto].
  Qed.

  #[using="Type"] Lemma hdro_mem_transport : forall m m' W h,
    hdro_mem m h -> munch W m m' -> wmono rsegs m m' -> 0 <= vcap h -> 0 <= ncap h ->
    (forall A n, In (A, n) (hregions h) -> disjoint_from W A n) -> hdro_mem m' h.
  Proof.
    intros m m' W h ([pad HC] & VC & [vbs [VB VN]] & NC & [nbs [NB NN]]) MU WM VP NP SEP.
    pose proof (SEP _ _ (or_introl eq_refl)) as D1. pose proof (SEP _ _ (or_intror (or_introl eq_refl))) as D2.
    pose proof (SEP _ _ (or_intror (or_intror (or_introl eq_refl)))) as D3.
    split; [| split; [| split; [| split]]].
    - exists pad. eapply rw_cells_transport; [exact HC| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D1| lia| cbn; lia].
    - eapply rw_cells_transport; [exact VC| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D1| lia| cbn; lia].
    - exists vbs. split; [| exact VN]. eapply rw_cells_transport; [exact VB| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D2| lia| cbn; lia].
    - eapply rw_cells_transport; [exact NC| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D1| lia| cbn; lia].
    - exists nbs. split; [| exact NN]. eapply rw_cells_transport; [exact NB| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D3| lia| cbn; lia].
  Qed.

  #[using="Type"] Lemma hdro_mem_heap_pres : forall m m' (LBK : list BLK) SP h,
    hdro_mem m h -> heap_pres AI LBK SP m m' -> bsub (hblocks h) LBK -> 0 <= vcap h -> 0 <= ncap h -> hdro_mem m' h.
  Proof.
    intros m m' LBK SP h ([pad HC] & VC & [vbs [VB VN]] & NC & [nbs [NB NN]]) HP SUB VP NP.
    pose proof (SUB _ (or_introl eq_refl)) as B1. pose proof (SUB _ (or_intror (or_introl eq_refl))) as B2.
    pose proof (SUB _ (or_intror (or_intror (or_introl eq_refl)))) as B3.
    split; [| split; [| split; [| split]]].
    - exists pad. eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact HC|]. eapply client_range_block; [exact B1| cbn; lia| cbn; lia].
    - eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact VC|]. eapply client_range_block; [exact B1| cbn; lia| cbn; lia].
    - exists vbs. split; [| exact VN]. eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact VB|]. eapply client_range_block; [exact B2| cbn; lia| cbn; lia].
    - eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact NC|]. eapply client_range_block; [exact B1| cbn; lia| cbn; lia].
    - exists nbs. split; [| exact NN]. eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact NB|]. eapply client_range_block; [exact B3| cbn; lia| cbn; lia].
  Qed.

  Fixpoint hdrs_mem (m : mem) (hs : list hdr) : Prop :=
    match hs with [] => True | h :: hs' => hdro_mem m h /\ hdro_pure h /\ hdrs_mem m hs' end.
  Definition hdrs_blocks (hs : list hdr) : list BLK := concat (map hblocks hs).

  #[using="Type"] Lemma hdrs_blocks_cons : forall h hs, hdrs_blocks (h :: hs) = hblocks h ++ hdrs_blocks hs.
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma hdrs_mem_transport : forall hs m m' W,
    hdrs_mem m hs -> munch W m m' -> wmono rsegs m m' ->
    (forall h A n, In h hs -> In (A, n) (hregions h) -> disjoint_from W A n) -> hdrs_mem m' hs.
  Proof.
    induction hs as [|h hs IH]; intros m m' W HS MU WM SEP; cbn in *; [exact I|].
    destruct HS as (HM & HP & HS'). split; [| split; [exact HP|]].
    - eapply hdro_mem_transport; [exact HM| exact MU| exact WM| unfold hdro_pure in HP; lia| unfold hdro_pure in HP; lia|].
      intros A n H. apply (SEP h); [left; reflexivity| exact H].
    - eapply IH; [exact HS'| exact MU| exact WM|]. intros h0 A n H0 H. apply (SEP h0); [right; exact H0| exact H].
  Qed.

  #[using="Type"] Lemma hdrs_mem_heap_pres : forall hs m m' (LBK : list BLK) SP,
    hdrs_mem m hs -> heap_pres AI LBK SP m m' -> bsub (hdrs_blocks hs) LBK -> hdrs_mem m' hs.
  Proof.
    induction hs as [|h hs IH]; intros m m' LBK SP HS HP SUB; cbn in *; [exact I|].
    destruct HS as (HM & HP0 & HS'). change (bsub (hblocks h ++ hdrs_blocks hs) LBK) in SUB. apply bsub_app in SUB. destruct SUB as [S1 S2].
    split; [| split; [exact HP0|]].
    - eapply hdro_mem_heap_pres; [exact HM| exact HP| exact S1| unfold hdro_pure in HP0; lia| unfold hdro_pure in HP0; lia].
    - eapply IH; [exact HS'| exact HP| exact S2].
  Qed.

End W.
