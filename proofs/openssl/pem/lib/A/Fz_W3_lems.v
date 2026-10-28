(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_libiface_pem D_agree D_clx Fz_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_writec Fz_W1_read Fz_W1_pploc Fz_W3_iface Fz_W3_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nd_split : forall (l1 l2 : list Z), List.NoDup (l1 ++ l2) -> List.NoDup l1 /\ List.NoDup l2 /\ (forall x, In x l1 -> In x l2 -> False).
Proof.
  intros l1 l2 ND. induction l1 as [|x l1 IH]; cbn in *.
  - split; [constructor|]. split; [exact ND|]. intros x F; destruct F.
  - inversion ND as [|y l NI ND']; subst. destruct (IH ND') as (A & B & C).
    split; [constructor; [intros X; apply NI; apply in_or_app; left; exact X| exact A]|]. split; [exact B|].
    intros z [<-|Hz] Hz2; [apply NI; apply in_or_app; right; exact Hz2| exact (C _ Hz Hz2)].
Qed.
Lemma nd_drop : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ x :: l2) -> List.NoDup (l1 ++ l2).
Proof.
  intros l1 l2 x ND. induction l1 as [|y l1 IH]; cbn in *; [inversion ND; assumption|].
  inversion ND as [|z l NI ND']; subst. constructor; [| exact (IH ND')]. intros X. apply NI. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right; right; exact X].
Qed.
Lemma nd_insert1 : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) -> List.NoDup (l1 ++ x :: l2).
Proof.
  intros l1 l2 x ND NI. induction l1 as [|y l1 IH]; cbn in *.
  - constructor; [exact NI| exact ND].
  - inversion ND as [|z l NIy ND']; subst. constructor.
    + intros X. apply in_app_iff in X. destruct X as [X|[<-|X]]; [apply NIy; apply in_or_app; left; exact X| apply NI; left; reflexivity| apply NIy; apply in_or_app; right; exact X].
    + apply IH; [exact ND'| intros X; apply NI; right; exact X].
Qed.
Lemma live_remove_all_sub : forall ps (l : list (Z * Z)) e, In e (live_remove_all ps l) -> In e l /\ ~ In (fst e) ps.
Proof.
  intros ps l e. induction ps as [|p ps IH]; cbn; intros H; [split; [exact H| intros F; exact F]|].
  apply live_remove_sub in H as H0. destruct (IH H0) as [A B].
  split; [exact A|]. intros [E|X]; [| exact (B X)].
  unfold live_remove in H. apply stdpp.base.list_elem_of_In in H. apply stdpp.list_basics.list.list_elem_of_filter in H. destruct H as [H _].
  rewrite <- E, Z.eqb_refl in H. exact H.
Qed.
Lemma live_remove_all_keep : forall ps (l : list (Z * Z)) e, In e l -> ~ In (fst e) ps -> In e (live_remove_all ps l).
Proof.
  intros ps l e He NI. induction ps as [|p ps IH]; cbn; [exact He|].
  apply live_remove_keep; [apply IH; intros X; apply NI; right; exact X| intros E; apply NI; left; exact (eq_sym E)].
Qed.
Lemma mbio_T_blocks : forall K q, mbio_T K q <-> In q (mbio_blocks K).
Proof. intros K q. unfold mbio_T. tauto. Qed.
Lemma mbio_ent_fst : forall K max, map fst (mbio_ent K max) = mbio_blocks K.
Proof. intros K max. unfold mbio_ent, mbio_blocks. rewrite map_app. cbn. destruct (k_d K); reflexivity. Qed.
Lemma in_mbio_W : forall K max x y, In (x, y) (mbio_W K max) <-> exists e, In e (mbio_ent K max) /\ x = fst e /\ y = fst e + snd e.
Proof.
  intros K max x y. unfold mbio_W. rewrite in_map_iff. split.
  - intros (e & E & He). exists e. injection E. intros <- <-. split; [exact He|]. split; reflexivity.
  - intros (e & He & -> & ->). exists e. split; [reflexivity| exact He].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mbio_fp (K : mbk) (max : Z) (a : Z) : Prop := exists e, In e (mbio_ent K max) /\ fst e <= a < fst e + snd e.

Lemma mb_inner_agree : forall live (m m' : mem) K len max off flw blw,
  mb_inner live m K len max off flw blw -> agree_on (mbio_fp K max) m m' -> mb_inner live m' K len max off flw blw.
Proof.
  intros live m m' K len max off flw blw (rmaxw & IBB & ALBB & CBB & IBM & ALBM & IRP & ALRP & HO & HL & HM & REST) AG.
  assert (AGs : forall (P : Z -> Prop), (forall x, P x -> mbio_fp K max x) -> agree_on P m m')
    by (intros P HP a Ha; exact (AG a (HP _ Ha))).
  assert (E1 : In (k_bb K, 16) (mbio_ent K max)) by (unfold mbio_ent; apply in_or_app; left; cbn; tauto).
  assert (E2 : In (k_bm K, 32) (mbio_ent K max)) by (unfold mbio_ent; apply in_or_app; left; cbn; tauto).
  assert (E3 : In (k_rp K, 32) (mbio_ent K max)) by (unfold mbio_ent; apply in_or_app; left; cbn; tauto).
  exists rmaxw. split; [exact IBB|]. split; [exact ALBB|].
  split; [eapply rw_cells_agree_nw; [exact CBB| apply AGs; intros x Hx; exists (k_bb K, 16); split; [exact E1| cbn in *; lia]]|].
  split; [exact IBM|]. split; [exact ALBM|]. split; [exact IRP|]. split; [exact ALRP|]. split; [exact HO|]. split; [exact HL|]. split; [exact HM|].
  destruct (k_d K) as [d|] eqn:KD.
  - destruct REST as (junk & ID & M0 & CBM & CRP & LJ & CD).
    assert (E4 : In (d, max) (mbio_ent K max)) by (unfold mbio_ent; rewrite KD; apply in_or_app; right; left; reflexivity).
    exists junk. split; [exact ID|]. split; [exact M0|].
    split; [eapply rw_cells_agree_nw; [exact CBM| apply AGs; intros x Hx; exists (k_bm K, 32); split; [exact E2| cbn in *; lia]]|].
    split; [eapply rw_cells_agree_nw; [exact CRP| apply AGs; intros x Hx; exists (k_rp K, 32); split; [exact E3| unfold readp_cells in Hx; cbn in *; lia]]|].
    split; [exact LJ|]. eapply rw_cells_agree_nw; [exact CD| apply AGs; intros x Hx; exists (d, max); split; [exact E4| cbn in *; lia]].
  - destruct REST as (M0 & CBM & CRP). split; [exact M0|].
    split; [eapply rw_cells_agree_nw; [exact CBM| apply AGs; intros x Hx; exists (k_bm K, 32); split; [exact E2| cbn in *; lia]]|].
    eapply rw_cells_agree_nw; [exact CRP| apply AGs; intros x Hx; exists (k_rp K, 32); split; [exact E3| unfold readp_cells in Hx; cbn in *; lia]].
Qed.

Lemma mbio_repx_agree : forall live (m m' : mem) K BI BM blw meth len max off,
  mbio_repx live m K BI BM blw meth len max off -> agree_on (mbio_fp K max) m m' -> mbio_repx live m' K BI BM blw meth len max off.
Proof.
  intros live m m' K BI BM blw meth len max off (fl & rrw & numw & padw & nr & nw & EBI & EBM & IBI & AL & ND & HM & HD & W1 & FL & TL & INR) AG.
  assert (E0 : In (k_bi K, 128) (mbio_ent K max)) by (unfold mbio_ent; apply in_or_app; left; cbn; tauto).
  assert (AGb : forall lo n, BI <= lo -> lo + n <= BI + 128 -> agree_on (fun x => lo <= x < lo + n) m m')
    by (intros lo n H1 H2 a Ha; apply AG; exists (k_bi K, 128); split; [exact E0| cbn in *; subst BI; lia]).
  exists fl, rrw, numw, padw, nr, nw. split; [exact EBI|]. split; [exact EBM|]. split; [exact IBI|]. split; [exact AL|]. split; [exact ND|]. split; [exact HM|].
  split; [eapply rw_cells_agree_nw; [exact HD| unfold bio_head; cbn [cells_size csize Nat.add]; exact (AGb BI 40 ltac:(lia) ltac:(lia))]|].
  split; [eapply rw_cells_agree_nw; [exact W1| unfold bio_w1_cells; cbn [cells_size csize Nat.add]; exact (AGb (BI + 40) 32 ltac:(lia) ltac:(lia))]|].
  split; [exact FL|].
  split; [eapply rw_cells_agree_nw; [exact TL| unfold bio_tail; cbn [cells_size csize Nat.add]; exact (AGb (BI + 72) 56 ltac:(lia) ltac:(lia))]|].
  exact (mb_inner_agree _ _ _ _ _ _ _ _ _ INR AG).
Qed.
Lemma mbio_rep_agree : forall live (m m' : mem) K BI meth len max off,
  mbio_rep live m K BI meth len max off -> agree_on (mbio_fp K max) m m' -> mbio_rep live m' K BI meth len max off.
Proof. intros live m m' K BI meth len max off [BM R] AG. exists BM. exact (mbio_repx_agree _ _ _ _ _ _ _ _ _ _ _ R AG). Qed.

(* [comment removed for export] *)
Lemma mb_inner_live : forall live live' (m : mem) K len max off flw blw,
  mb_inner live m K len max off flw blw -> (forall e, In e (mbio_ent K max) -> In e live -> In e live') -> mb_inner live' m K len max off flw blw.
Proof.
  intros live live' m K len max off flw blw (rmaxw & IBB & ALBB & CBB & IBM & ALBM & IRP & ALRP & HO & HL & HM & REST) KP.
  assert (E1 : In (k_bb K, 16) (mbio_ent K max)) by (unfold mbio_ent; apply in_or_app; left; cbn; tauto).
  assert (E2 : In (k_bm K, 32) (mbio_ent K max)) by (unfold mbio_ent; apply in_or_app; left; cbn; tauto).
  assert (E3 : In (k_rp K, 32) (mbio_ent K max)) by (unfold mbio_ent; apply in_or_app; left; cbn; tauto).
  exists rmaxw. split; [exact (KP _ E1 IBB)|]. split; [exact ALBB|]. split; [exact CBB|]. split; [exact (KP _ E2 IBM)|]. split; [exact ALBM|].
  split; [exact (KP _ E3 IRP)|]. split; [exact ALRP|]. split; [exact HO|]. split; [exact HL|]. split; [exact HM|].
  destruct (k_d K) as [d|] eqn:KD; [| exact REST].
  destruct REST as (junk & ID & R2). exists junk. split; [| exact R2].
  apply KP; [| exact ID]. unfold mbio_ent. rewrite KD. apply in_or_app. right. left. reflexivity.
Qed.
Lemma mbio_repx_live : forall live live' (m : mem) K BI BM blw meth len max off,
  mbio_repx live m K BI BM blw meth len max off -> (forall e, In e (mbio_ent K max) -> In e live -> In e live') -> mbio_repx live' m K BI BM blw meth len max off.
Proof.
  intros live live' m K BI BM blw meth len max off (fl & rrw & numw & padw & nr & nw & EBI & EBM & IBI & R) KP.
  exists fl, rrw, numw, padw, nr, nw. split; [exact EBI|]. split; [exact EBM|].
  split; [apply KP; [unfold mbio_ent; apply in_or_app; left; cbn; subst BI; tauto| exact IBI]|].
  destruct R as (AL & ND & HM & HD & W1 & FL & TL & INR).
  split; [exact AL|]. split; [exact ND|]. split; [exact HM|]. split; [exact HD|]. split; [exact W1|]. split; [exact FL|]. split; [exact TL|].
  exact (mb_inner_live _ _ _ _ _ _ _ _ _ INR KP).
Qed.
Lemma mbio_rep_live : forall live live' (m : mem) K BI meth len max off,
  mbio_rep live m K BI meth len max off -> (forall e, In e (mbio_ent K max) -> In e live -> In e live') -> mbio_rep live' m K BI meth len max off.
Proof. intros live live' m K BI meth len max off [BM R] KP. exists BM. exact (mbio_repx_live _ _ _ _ _ _ _ _ _ _ _ R KP). Qed.

(* [comment removed for export] *)
Lemma mbio_repx_ents : forall live (m : mem) K BI BM blw meth len max off e,
  mbio_repx live m K BI BM blw meth len max off -> In e (mbio_ent K max) -> In e live.
Proof.
  intros live m K BI BM blw meth len max off e (fl & rrw & numw & padw & nr & nw & EBI & EBM & IBI & AL & ND & HM & HD & W1 & FL & TL & INR) He.
  destruct INR as (rmaxw & IBB & _ & _ & IBM & _ & IRP & _ & _ & _ & _ & REST).
  unfold mbio_ent in He. apply in_app_iff in He. destruct He as [He|He].
  - destruct He as [<-|[<-|[<-|[<-|[]]]]]; [subst BI; exact IBI| exact IBB| exact IBM| exact IRP].
  - destruct (k_d K) as [d|]; [| destruct He]. destruct He as [<-|[]]. destruct REST as (junk & ID & _). exact ID.
Qed.
Lemma mbio_rep_ents : forall live (m : mem) K BI meth len max off e,
  mbio_rep live m K BI meth len max off -> In e (mbio_ent K max) -> In e live.
Proof. intros live m K BI meth len max off e [BM R] He. exact (mbio_repx_ents _ _ _ _ _ _ _ _ _ _ _ R He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W3L.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variable GOBJ : Z -> Z -> Prop.
  Hypothesis AFP : art_facts_pem RT GOBJ.
  Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
  Variable libenv_fp : list (Z * Z) -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
  Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
  Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
  Variables FZ_SITES FZ_CALLS : list (Z * Z).

  Local Notation pem_entry := (pem_entry RT).
  Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
  Local Notation pem_err := (pem_err RT errst_at_rest errst_live).
  Local Notation pem_frame := (pem_frame RT).

  (* [comment removed for export] *)
  Lemma com_lists : forall (en : pem_entry) Σ (m : mem) off crem lrem cur,
    pem_com en Σ m off crem lrem cur -> incl_live (e_live RT en) (rt_live RT Σ) /\ (forall e, In e cur -> In e (rt_live RT Σ)).
  Proof.
    intros en Σ m off crem lrem cur COM.
    pose proof COM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PERM & _).
    split; intros e He; apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; [right| left]; exact He.
  Qed.

  Lemma cur_live_facts : forall (en : pem_entry) Σ (m : mem) off crem lrem cur e,
    pem_com en Σ m off crem lrem cur -> In e cur -> 0 < snd e ->
    In e (rt_live RT Σ) /\ 0 < fst e /\ fst e + snd e <= e_lo RT en /\ (snd e <= 64512 -> 0x10007fff8000 <= fst e)
    /\ (forall a, fst e <= a < fst e + snd e -> ~ aclient (e_live RT en) (e_frames RT en) (e_PL RT en) a).
  Proof using AF AFP.
    intros en Σ m off crem lrem cur e COM He POS.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS & FRS & REST).
    assert (CLV : forall e, In e cur -> In e (rt_live RT Σ)) by (intros e0 He0; apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; left; exact He0).
    assert (ELV : incl_live (e_live RT en) (rt_live RT Σ)) by (intros e0 He0; apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; exact He0).
    pose proof (CLV _ He) as INe. destruct e as [p n]. cbn [fst snd] in *.
    pose proof (af_live_range RT AF Σ m p n ART0 INe) as (P0 & PLO & PSEG).
    split; [exact INe|]. split; [exact P0|]. split; [lia|]. split; [intros Hn; exact (afp_live_hi RT GOBJ AFP Σ m p n ART0 INe Hn)|].
    intros a Ha AC. destruct AC as [H|[H|[H|[H|H]]]].
    - clear - H Ha PLO LOR LOW PD. unfold e_sp1, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
    - pose proof (client_static_range a H). clear - H0 Ha PSEG P0. unfold SEGTOP_A in *. lia.
    - destruct H as (p2 & n2 & Hin & Hp). pose proof (ELV _ Hin) as Hin2.
      assert (NE : (p, n) <> (p2, n2)) by (intros E; injection E; intros _ <-; apply (CFR _ He); cbn; apply in_map_iff; exists (p, n2); split; [reflexivity| exact Hin]).
      destruct (live_ne_apart RT AF Σ m p n p2 n2 ART0 INe Hin2 NE); lia.
    - destruct H as (f & k & Hin & Hf). assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
      pose proof (af_frames_range RT AF Σ m f k ART0 Hin') as (_ & _ & _ & R3). destruct (R3 p n INe); lia.
    - destruct H as (f & k & Hin & Hf). assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
      pose proof (af_fshadow_apart RT AF Σ m f k ART0 Hin') as (SL & _). destruct (SL p n INe); lia.
  Qed.
  (* [comment removed for export] *)

  Lemma outside_intro : forall (W : list (Z * Z)) x, (forall iv, In iv W -> ~ (fst iv <= x < snd iv)) -> outside W x.
  Proof.
    intros W x H. induction W as [|[lo hi] W IH]; cbn; [exact I|].
    split; [exact (H (lo, hi) (or_introl eq_refl))| apply IH; intros iv Hiv; apply H; right; exact Hiv].
  Qed.

  (* [comment removed for export] *)
  Definition seg_ok (en : pem_entry) (cur : list (Z * Z)) (iv : Z * Z) : Prop :=
       (e_sp1 RT en <= fst iv /\ snd iv <= e_PL RT en - 104)
    \/ (exists e, In e cur /\ 0 < snd e /\ fst e <= fst iv /\ snd iv <= fst e + snd e)
    \/ (e_f RT en <= fst iv /\ snd iv <= e_f RT en + 120).

  (* [comment removed for export] *)
  Lemma seg_byte_facts : forall (en : pem_entry) Σ (m : mem) off crem lrem cur iv a,
    pem_com en Σ m off crem lrem cur -> seg_ok en cur iv -> fst iv <= a < snd iv ->
       aclient (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) a
    /\ ~ aclient (e_live RT en) (e_frames RT en) (e_PL RT en) a
    /\ ~ client_static a /\ ~ (0x7fff8000 <= a < 0x10007fff8000) /\ a < e_PL RT en - 104
    /\ (forall p n, In (p, n) (e_live RT en) -> ~ (p <= a < p + n)).
  Proof using AF AFP.
    intros en Σ m off crem lrem cur iv a COM OK Ha.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & REST).
    pose proof (af_sp0_range RT AF Σ m ART0) as SPR. pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
    assert (ELV : incl_live (e_live RT en) (rt_live RT Σ)) by (intros e0 He0; apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; exact He0).
    assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
    pose proof (af_frames_range RT AF Σ m _ _ ART0 INF) as (_ & FR2 & _ & FR4). change (fs_size 1) with 128 in FR2, FR4.
    destruct OK as [[O1 O2]|[(e & He & POS & O1 & O2)|[O1 O2]]].
    - (* [comment removed for export] *)
      assert (R : e_sp1 RT en <= a < e_PL RT en - 104) by lia. clear O1 O2 Ha. unfold e_sp1 in *.
      split; [apply acl_stack; unfold USTACK_TOP, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *; lia|].
      split. { intros AC. destruct AC as [H|[H|[H|[H|H]]]].
        + lia.
        + pose proof (client_static_range a H). unfold SEGTOP_A, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
        + destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 (ELV _ Hin)) as (_ & X & _). unfold STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
        + destruct H as (f & k & Hin & Hf). assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
          pose proof (af_frames_range RT AF Σ m f k ART0 Hin') as (_ & X & _). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)). unfold fs_size, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
        + destruct H as (f & k & Hin & Hf). assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
          pose proof (af_frames_range RT AF Σ m f k ART0 Hin') as (X0 & X & _). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)).
          unfold shad, SHB, fs_size, STACK_WIN, RT_STACK, PEM_CALLEE_STACK, USTACK_TOP in *. Z.div_mod_to_equations. lia. }
      split; [intros H; pose proof (client_static_range a H); unfold SEGTOP_A, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *; lia|].
      split; [unfold STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *; lia|]. split; [lia|].
      intros p n Hin Hp. pose proof (af_live_range RT AF Σ m p n ART0 (ELV _ Hin)) as (_ & X & _). unfold STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
    - (* [comment removed for export] *)
      destruct (cur_live_facts en Σ m off crem lrem cur e COM He POS) as (INe & P0 & PLO & PHI & NAC). destruct e as [p n]. cbn [fst snd] in *.
      pose proof (af_live_range RT AF Σ m p n ART0 INe) as (_ & PR2 & PSEG). pose proof (afp_live_mem RT GOBJ AFP Σ m p n ART0 INe ltac:(lia)) as (PSH & P47).
      split; [apply (acl_live _ _ _ p n); [exact INe| lia]|].
      split; [intros AC; exact (NAC a ltac:(lia) AC)|].
      split; [intros H; pose proof (client_static_range a H); unfold SEGTOP_A in *; lia|].
      split; [lia|]. split; [unfold e_sp1, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *; lia|].
      intros p2 n2 Hin Hp2. apply (NAC a ltac:(lia)). apply (acl_live _ _ _ p2 n2); [exact Hin| exact Hp2].
    - (* [comment removed for export] *)
      pose proof (af_frames_hi RT AF Σ m _ _ ART0 INF) as FHI. change (fs_size 1) with 128 in FHI.
      split; [apply (acl_frame _ _ _ (e_f RT en) 1%nat); [exact INF| change (fs_size 1) with 128; lia]|].
      split. { intros AC. destruct AC as [H|[H|[H|[H|H]]]].
        + unfold e_sp1, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
        + pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
        + destruct H as (p & n & Hin & Hp). destruct (FR4 p n (ELV _ Hin)); lia.
        + destruct H as (f & k & Hin & Hf). assert (Hin' : In (f, k) ([] ++ rt_frames RT (e_Σ RT en))) by exact Hin.
          pose proof (af_frames_disj RT AF Σ m (e_f RT en) 1%nat f k [] _ ART0 FRS Hin') as D. change (fs_size 1) with 128 in D.
          pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)). unfold fs_size in *. lia.
        + destruct H as (f & k & Hin & Hf). assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
          pose proof (af_fshadow_apart RT AF Σ m f k ART0 Hin') as (_ & SF). destruct (SF _ _ INF) as [X|X]; change (fs_size 1) with 128 in X; lia. }
      split; [intros H; pose proof (client_static_range a H); unfold SEGTOP_A in *; lia|].
      split; [lia|]. split; [unfold e_sp1, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *; lia|].
      intros p n Hin Hp. destruct (FR4 p n (ELV _ Hin)); lia.
  Qed.
  (* [comment removed for export] *)
  Lemma com_seg : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur Wseg,
    pem_com en Σ m off crem lrem cur -> munch Wseg m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (e_lo RT en) (e_sp1 RT en) ->
    Forall (seg_ok en cur) Wseg ->
    pem_com en Σ m' off crem lrem cur.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros en Σ m m' off crem lrem cur Wseg COM MU WM MI' ST' HW.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    (* [comment removed for export] *)
    assert (AGo : forall (P : Z -> Prop), (forall x iv, P x -> In iv Wseg -> ~ (fst iv <= x < snd iv)) -> agree_on P m m').
    { intros P HP a Ha. apply MU. apply outside_intro. intros iv Hiv. exact (HP _ _ Ha Hiv). }
    assert (BF : forall iv a, In iv Wseg -> fst iv <= a < snd iv ->
         aclient (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) a /\ ~ aclient (e_live RT en) (e_frames RT en) (e_PL RT en) a
      /\ ~ client_static a /\ ~ (0x7fff8000 <= a < 0x10007fff8000) /\ a < e_PL RT en - 104 /\ (forall p n, In (p, n) (e_live RT en) -> ~ (p <= a < p + n))).
    { intros iv a Hiv Ha. exact (seg_byte_facts en Σ m off crem lrem cur iv a COM (proj1 (Forall_forall _ _) HW iv Hiv) Ha). }
    split. { apply (af_frame RT AF Σ m m' (e_sp1 RT en) ART0); [clear - LOW LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia| | exact WM].
             intros a NA. apply MU. apply outside_intro. intros iv Hiv R. exact (NA (proj1 (BF iv _ Hiv R))). }
    split; [exact MI'|]. split; [exact ST'|]. split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|]. split; [exact LOW|]. split; [exact LOR|]. split; [exact HLOS|].
    split. { eapply cl_env_seg; [exact CLE| exact MU|]. intros x Hx. apply outside_intro. intros iv Hiv R. exact (proj1 (proj2 (proj2 (BF iv x Hiv R))) (cl_cell_static _ Hx)). }
    split. { eapply sec_off_agree; [exact SEC|]. intros a Ea. apply MU. apply outside_intro. intros iv Hiv R.
             apply (proj1 (proj2 (proj2 (BF iv _ Hiv R)))). apply client_static_intro. rewrite Ea. unfold SEC_INIT. lia. }
    split. { eapply libenv_agree; [exact LE|]. apply AGo. intros x iv Hx Hiv R. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p & n & Hin & Hp)].
             - exact (proj1 (proj2 (proj2 (BF iv x Hiv R))) CS).
             - exact (proj2 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) p n (INCL _ Hin) Hp). }
    split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|]. split; [exact NTL|].
    split. { eapply mbio_rep_agree; [exact MB|]. apply AGo. intros x iv (e & He & Hx) Hiv R. destruct e as [p n].
             exact (proj2 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) p n (KLV _ He) Hx). }
    split; [exact OFF|]. split; [exact BLT|]. split; [exact KLV|]. split; [exact PERM|]. split; [exact CFR|]. split; [exact ND|]. split; [exact LPOS|].
    split; [exact FRS|]. split; [exact FRN|]. split; [exact SP0|]. split; [exact CG|]. split; [exact LIV|]. split; [exact LR0|]. split; [exact CR|]. split; [exact CR0|]. split; [exact CRE|].
    split; [exact CGH|]. split; [exact CGS|]. split; [exact CTX|].
    split. { eapply uw_chain_agree; [exact UWC|]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx.
             pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (BF iv _ Hiv R)))))). unfold e_PL in *. lia. }
    split; [exact F0|]. split; [exact F64|]. split; [exact FTOP|]. split; [exact FSEG|]. split; [exact FSH|].
    split. { eapply rw_cells_agree; [exact FFS| | exact WM]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx.
             pose proof (proj1 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) as NS. apply NS. unfold ff_shadow in Hx. cbn [cells_size csize Nat.add] in Hx.
             pose proof (af_sp0_range RT AF Σ m ART0). pose proof (af_sp0_win RT AF Σ m ART0). unfold shad, SHB, USTACK_TOP, STACK_WIN in *.
             clear - Hx F0 FTOP. Z.div_mod_to_equations. lia. }
    split. { eapply rw_cells_agree; [exact SAVED| | exact WM]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx. unfold pem_saved in Hx. cbn [cells_size csize Nat.add] in Hx.
             pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R)))))). lia. }
    split. { eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply MU. apply outside_intro. intros iv Hiv R. exact (proj1 (proj2 (BF iv _ Hiv R)) Ha). }
    split; [exact FLR|]. split; [exact NDO|]. split; [exact OUTS|]. split; [exact FDO| exact MST].
  Qed.
  (* [comment removed for export] *)
  Lemma libenv_keep : forall (m m' : mem) LBL E KEEP fr sp W,
    libenv m LBL E -> rt_pres_fp KEEP fr sp W m m' -> incl_live LBL KEEP -> (forall x, libenv_fp LBL x -> outside W x) -> libenv m' LBL E.
  Proof using libenv_agree libenv_fp_where.
    intros m m' LBL E KEEP fr sp W LE PR INCL HO. eapply libenv_agree; [exact LE|]. intros a Ha. apply PR; [| exact (HO _ Ha)].
    destruct (libenv_fp_where _ _ Ha) as [(_ & CS & _)|(p & n & Hin & Hp)]; [apply acl_static; exact CS| apply (acl_live _ _ _ p n); [exact (INCL _ Hin)| exact Hp]].
  Qed.
  Lemma pem_err_keep : forall (en : pem_entry) Σ Σ' strs (m m' : mem) KEEP fr sp W,
    pem_err en Σ strs m -> rt_pres_fp KEEP fr sp W m m' -> In (e_E RT en, 904) KEEP -> (forall e, In e strs -> In e KEEP) ->
    (forall x, e_E RT en <= x < e_E RT en + 904 -> outside W x) -> (forall e x, In e strs -> fst e <= x < fst e + snd e -> outside W x) ->
    (forall e, In e strs -> In e (rt_live RT Σ')) ->
    pem_err en Σ' strs m'.
  Proof using errst_rest_agree errst_live_agree errst_fp_where.
    intros en Σ Σ' strs m m' KEEP fr sp W (PE & SZ & LV & FR) PR INE INS HOE HOS LV'.
    assert (AG : agree_on (errst_fp (e_E RT en) strs) m m').
    { intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R|(p & n & Hin & Hp)].
      - apply PR; [apply (acl_live _ _ _ (e_E RT en) 904); [exact INE| exact R]| exact (HOE _ R)].
      - apply PR; [apply (acl_live _ _ _ p n); [exact (INS _ Hin)| exact Hp]| exact (HOS (p, n) _ Hin Hp)]. }
    split; [| split; [exact SZ| split; [exact LV'| exact FR]]].
    destruct PE as [[-> R]|(top & bot & L & LEN)]; [left; split; [reflexivity| exact (errst_rest_agree _ _ _ _ R AG)]| right; exists top, bot; split; [exact (errst_live_agree _ _ _ _ _ _ L AG)| exact LEN]].
  Qed.
  Lemma mbio_rep_keep : forall live live' (m m' : mem) K BI meth len max off KEEP fr sp W,
    mbio_rep live m K BI meth len max off -> rt_pres_fp KEEP fr sp W m m' -> (forall e, In e (mbio_ent K max) -> In e KEEP /\ In e live') ->
    (forall e x, In e (mbio_ent K max) -> fst e <= x < fst e + snd e -> outside W x) -> mbio_rep live' m' K BI meth len max off.
  Proof.
    intros live live' m m' K BI meth len max off KEEP fr sp W MB PR KP HO.
    apply (mbio_rep_live live); [| intros e He _; exact (proj2 (KP _ He))].
    eapply mbio_rep_agree; [exact MB|]. intros a (e & He & Ha). destruct e as [p n].
    apply PR; [apply (acl_live _ _ _ p n); [exact (proj1 (KP _ He))| exact Ha]| exact (HO _ _ He Ha)].
  Qed.
  Lemma mbio_repx_keep : forall live live' (m m' : mem) K BI BM blw meth len max off KEEP fr sp W,
    mbio_repx live m K BI BM blw meth len max off -> rt_pres_fp KEEP fr sp W m m' -> (forall e, In e (mbio_ent K max) -> In e KEEP /\ In e live') ->
    (forall e x, In e (mbio_ent K max) -> fst e <= x < fst e + snd e -> outside W x) -> mbio_repx live' m' K BI BM blw meth len max off.
  Proof.
    intros live live' m m' K BI BM blw meth len max off KEEP fr sp W MB PR KP HO.
    apply (mbio_repx_live live); [| intros e He _; exact (proj2 (KP _ He))].
    eapply mbio_repx_agree; [exact MB|]. intros a (e & He & Ha). destruct e as [p n].
    apply PR; [apply (acl_live _ _ _ p n); [exact (proj1 (KP _ He))| exact Ha]| exact (HO _ _ He Ha)].
  Qed.
  (* [comment removed for export] *)
  Lemma cells_keep : forall (m m' : mem) p n A cs KEEP fr sp W,
    rw_cells asegs m A cs -> rt_pres_fp KEEP fr sp W m m' -> In (p, n) KEEP -> p <= A -> A + Z.of_nat (cells_size cs) <= p + n ->
    (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' A cs.
  Proof.
    intros m m' p n A cs KEEP fr sp W C PR INK H1 H2 HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. cbv beta in Ha.
    apply PR; [apply (acl_live _ _ _ p n); [exact INK| lia]| exact (HO _ Ha)].
  Qed.
  (* [comment removed for export] *)
  Lemma stack_keep : forall (m m' : mem) A cs KEEP fr sp W,
    rw_cells asegs m A cs -> rt_pres_fp KEEP fr sp W m m' -> sp <= A -> A + Z.of_nat (cells_size cs) <= USTACK_TOP ->
    (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' A cs.
  Proof.
    intros m m' A cs KEEP fr sp W C PR H1 H2 HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. cbv beta in Ha.
    apply PR; [apply acl_stack; lia| exact (HO _ Ha)].
  Qed.
  (* [comment removed for export] *)
  Lemma frame_keep : forall (m m' : mem) f A cs KEEP fr sp W,
    rw_cells asegs m A cs -> rt_pres_fp KEEP fr sp W m m' -> In (f, 1%nat) fr -> f <= A -> A + Z.of_nat (cells_size cs) <= f + 120 ->
    (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' A cs.
  Proof.
    intros m m' f A cs KEEP fr sp W C PR INF H1 H2 HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. cbv beta in Ha.
    apply PR; [apply (acl_frame _ _ _ f 1%nat); [exact INF| change (fs_size 1) with 128; lia]| exact (HO _ Ha)].
  Qed.
  Lemma fshadow_keep : forall (m m' : mem) f cs KEEP fr sp W,
    rw_cells asegs m (shad f) cs -> Z.of_nat (cells_size cs) = 16 -> f mod 64 = 0 -> rt_pres_fp KEEP fr sp W m m' -> In (f, 1%nat) fr ->
    (forall x, shad f <= x < shad f + 16 -> outside W x) -> rw_cells asegs m' (shad f) cs.
  Proof.
    intros m m' f cs KEEP fr sp W C SZ F64 PR INF HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. cbv beta in Ha. rewrite SZ in Ha.
    apply PR; [| exact (HO _ Ha)]. apply (acl_fshadow _ _ _ f 1%nat); [exact INF|]. change (fs_size 1) with (64 * 2).
    rewrite (shad_add64 f 2 F64). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma com_call : forall (en : pem_entry) Σ Σ' (m m' : mem) off off' crem crem' lrem lrem' cur cur' KEEP W cost,
    pem_com en Σ m off crem lrem cur ->
    ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' (e_lo RT en) (e_sp1 RT en) ->
    rt_pres_fp KEEP (rt_frames RT Σ) (e_sp1 RT en) W m m' ->
    cl_env m' (Z_to_bv 8 1) (e_canary RT en) -> sec_off m' -> libenv m' (e_LBL RT en) (e_E RT en) ->
    mbio_rep (rt_live RT Σ') m' (e_K RT en) (e_BI RT en) (e_meth RT en) (e_blen RT en) (e_bmax RT en) off' -> e_boff RT en <= off' <= e_blen RT en ->
    rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_cg RT Σ' = rt_cg RT Σ ->
    rt_credit RT Σ - cost <= rt_credit RT Σ' -> 0 <= crem' -> crem' + cost <= crem ->
    0 <= lrem' -> Z.of_nat (length (rt_live RT Σ')) + lrem' <= Z.of_nat (length (rt_live RT Σ)) + lrem ->
    incl_live (e_live RT en) KEEP ->
    (forall a, aclient (e_live RT en) (e_frames RT en) (e_PL RT en) a -> outside (pem_W RT en) a -> outside W a) ->
    (forall x, e_sp1 RT en <= x < USTACK_TOP -> outside W x) ->
    (forall x, shad (e_f RT en) <= x < shad (e_f RT en) + 16 -> outside W x) ->
    Permutation (rt_live RT Σ') (cur' ++ e_live RT en) -> (forall e, In e cur' -> ~ In (fst e) (map fst (e_live RT en))) ->
    List.NoDup (map fst cur' ++ e_E RT en :: mbio_blocks (e_K RT en)) -> (forall e, In e (rt_live RT Σ') -> 0 < snd e) ->
    (forall e, In e ((e_E RT en, 904) :: e_LBL RT en) -> ~ In (fst e) (mbio_blocks (e_K RT en) ++ map fst cur')) ->
    pem_com en Σ' m' off' crem' lrem' cur'.
  Proof using AF AFP.
    intros en Σ Σ' m m' off off' crem crem' lrem lrem' cur cur' KEEP W cost COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 MB1 OFF1 FRS1 SP1 CG1 CR1 CR0' CRM LR0' LRM
           KP HWP HWS HWF PERM1 CFR1 ND1 LPOS1 NTL1.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
    pose proof (af_sp0_range RT AF Σ m ART0) as SPR.
    split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|].
    split; [rewrite SP1; exact LOW|]. split; [exact LOR|]. split; [exact HLOS|]. split; [exact CLE1|]. split; [exact SEC1|]. split; [exact LE1|].
    split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|]. split; [exact NTL1|]. split; [exact MB1|]. split; [exact OFF1|]. split; [exact BLT|]. split; [exact KLV|].
    split; [exact PERM1|]. split; [exact CFR1|]. split; [exact ND1|]. split; [exact LPOS1|].
    split; [rewrite FRS1; exact FRS|]. split; [exact FRN|]. split; [rewrite SP1; exact SP0|]. split; [rewrite CG1; exact CG|].
    split; [lia|]. split; [exact LR0'|]. split; [lia|]. split; [exact CR0'|]. split; [exact CRE|].
    split; [rewrite CG1; exact CGH|]. split; [exact CGS|]. split; [rewrite CG1; exact CTX|].
    split. { eapply uw_chain_agree; [exact UWC|]. intros a Ha. cbv beta in Ha. unfold e_PL in *. apply PR; [apply acl_stack; unfold e_sp1, e_PL in *; lia| apply HWS; unfold e_sp1, e_PL in *; lia]. }
    split; [exact F0|]. split; [exact F64|]. split; [exact FTOP|]. split; [exact FSEG|]. split; [exact FSH|].
    split; [exact (fshadow_keep m m' _ _ KEEP _ _ W FFS eq_refl F64 PR INF HWF)|].
    split. { eapply stack_keep; [exact SAVED| exact PR| unfold e_sp1; lia| unfold pem_saved; cbn [cells_size csize Nat.add]; lia|].
             intros x Hx. unfold pem_saved in Hx. cbn [cells_size csize Nat.add] in Hx. apply HWS. unfold e_sp1. lia. }
    split. { eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply PR; [| exact (HWP _ Ha Ho)].
             destruct Ha as [H|[H|[H|[H|H]]]].
             - apply acl_stack. unfold e_sp1. lia.
             - apply acl_static. exact H.
             - destruct H as (p & n & Hin & Hp). apply (acl_live _ _ _ p n); [exact (KP _ Hin)| exact Hp].
             - destruct H as (f & k & Hin & Hf). apply (acl_frame _ _ _ f k); [rewrite FRS; right; exact Hin| exact Hf].
             - destruct H as (f & k & Hin & Hf). apply (acl_fshadow _ _ _ f k); [rewrite FRS; right; exact Hin| exact Hf]. }
    split; [exact FLR|]. split; [exact NDO|]. split; [exact OUTS|]. split; [exact FDO| exact MST].
  Qed.
  (* [comment removed for export] *)
  Lemma grow_pot_nonneg : forall (en : pem_entry) lenX lenY maxX maxY off,
    e_boff RT en <= off <= e_blen RT en -> 0 <= lenX -> 0 <= lenY -> lenX + lenY <= 2 * (off - e_boff RT en) ->
    maxX <= gr_n (lenX + 255) -> maxY <= gr_n (lenY + 255) -> 0 <= grow_pot RT en maxX maxY.
  Proof.
    intros en lenX lenY maxX maxY off HO HX HY HS MX MY. unfold grow_pot, grow_cap, e_plen. unfold gr_n in *.
    Z.div_mod_to_equations. nia.
  Qed.
End W3L.

(* [comment removed for export] *)
Lemma first_nul_split : forall (z : byte) (l : list byte), In z l -> exists a b, l = a ++ z :: b /\ ~ In z a.
Proof.
  intros z l. induction l as [|x l IH]; intros H; [destruct H|].
  destruct (bv_eq_dec _ x z) as [->|NE].
  - exists [], l. split; [reflexivity| intros []].
  - destruct H as [->|H]; [exfalso; exact (NE eq_refl)|]. destruct (IH H) as (a & b & -> & NA). exists (x :: a), b. split; [reflexivity|].
    intros [E|X]; [exact (NE E)| exact (NA X)].
Qed.
