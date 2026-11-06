(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
#[local] Ltac lia ::= am_lia.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Ltac box H := let T := type of H in change (boxed T) in H.

Section Pf.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Ztac := try ceil; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma compact_roundtrip_k : forall c k, compact_of SBEG c (chunk_of_compact SBEG c k) = k.
  Proof using. intros c k. (lazymatch goal with |- ?G => let G' := eval unfold compact_of, chunk_of_compact in G in change_no_check G' end). replace (region_beg SBEG c + 16 * k - region_beg SBEG c) with (k * 16) by lia. apply Z.div_mul. lia. Qed.

  Lemma carved_roundtrip : forall st Lc FF c a {qt qg : Z}, WFq bt st Lc FF qt qg -> 1 <= c <= 30 -> carved bt st c a ->
    chunk_of_compact SBEG c (compact_of SBEG c a) = a.
  Proof using.
    intros st Lc FF c a qt qg W Hc CV. destruct (carved_range bt st Lc FF W c a Hc CV) as (C1 & C2 & C3 & C4 & C5).
    destruct CV as (j & Hj & Hle & Ea). pose proof (csize_pos c Hc) as (_ & S3).
    (lazymatch goal with |- ?G => let G' := eval unfold chunk_of_compact, compact_of in G in change_no_check G' end). subst a. (lazymatch goal with |- ?G => let G' := eval unfold chunk_addr in G in change_no_check G' end).
    replace (region_beg SBEG c + j * csize c - region_beg SBEG c) with (j * csize c) by lia.
    assert (E2 : csize c = 16 * (csize c / 16)) by (apply Z.div_exact; lia). rewrite E2 at 1.
    replace (j * (16 * (csize c / 16))) with ((j * (csize c / 16)) * 16) by lia. rewrite Z.div_mul by lia. nia.
  Qed.

  Lemma partition_live_ext : forall st Lc Lc' c,
    (forall a, in_live_c Lc' c a <-> in_live_c Lc c a) -> partition_c bt st Lc c -> partition_c bt st Lc' c.
  Proof using.
    intros st Lc Lc' c P H. unfold partition_c in *.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact H9 | exact H10]]]]]]]]].
    - intros a. rewrite (P a). exact (H1 a).
    - intros a [X Y]. apply (H2 a). split; [apply (P a); exact X | exact Y].
    - intros a [X Y]. apply (H3 a). split; [apply (P a); exact X | exact Y].
    - intros a [X Y]. apply (H4 a). split; [apply (P a); exact X | exact Y].
    - exact H5. - exact H6. - exact H7.
    - intros a Hb Hc X. apply (H8 a Hb Hc). destruct X as [X|X]; [left; apply (P a); exact X | right; exact X].
  Qed.

  Lemma in_live_c_cons : forall Lc p n c a,
    in_live_c ((p, n) :: Lc) c a <-> (is_primary n = true /\ blk_class n = c /\ prim_alloc_beg p n = a) \/ in_live_c Lc c a.
  Proof using.
    intros Lc p n c a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
    - intros (p' & n' & [E | Hin] & X); [injection E as <- <-; left; exact X | right; exists p', n'; split; assumption].
    - intros [X | (p' & n' & Hin & X)]; [exists p, n; split; [left; reflexivity | exact X] | exists p', n'; split; [right; exact Hin | exact X]].
  Qed.

  (* [comment removed for export] *)
  Lemma space_facts : forall st Lc FF {qt qg : Z}, WFq bt st Lc FF qt qg ->
    dyn_ok IA (bt_resv6 bt) (bt_resv6 bt + bt_resv6_len bt) /\ bt_resv6 bt mod PG = 0
    /\ bt_resv6 bt <= SBEG /\ SBEG + KSPACE + PG <= bt_resv6 bt + bt_resv6_len bt
    /\ AS_HEAPLO <= bt_resv6 bt.     (* [comment removed for export] *)
  Proof using.
    intros st Lc FF qt qg W. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & IN6 & R6a & R6b & _) & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ IN6)) as (D & _ & M & _). split; [exact D|]. repeat (split; [assumption|]).
    destruct D as (D1 & D2 & D3 & D4 & D5). ulia.
  Qed.
  Lemma space_ablk : forall st Lc FF {qt qg : Z}, WFq bt st Lc FF qt qg ->
    forall p n, SBEG + 16 <= p -> 0 <= n -> p + n <= SBEG + KSPACE + PG -> ablk_ok IA p n.
  Proof using.
    intros st Lc FF qt qg W p n A B C. destruct (space_facts st Lc FF W) as ((D1 & D2 & D3 & D4 & D5) & M & S1 & S2 & S3).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. clear D4 D5. (lazymatch goal with |- ?G => let G' := eval unfold ablk_ok, PTRLO in G in change_no_check G' end). ulia.
  Qed.

  Theorem OPS_WF_cache_pop_pf : OPS_WF_cache_pop bt.
  Proof using.
    intros st Lc FF c ks k n W Hc Hks Hn HP Hcl HCNT HBYT. cbn zeta.
    set (ch := chunk_of_compact SBEG c k). set (p := ch + rz n).
    pose proof W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (L1 & L2 & L3) & WK & WD & WM & WMP & G).
    destruct (WC c Hc) as (C1 & C2 & C3).
    assert (Hk : In k (a_cache st c)) by (rewrite Hks; apply in_app_iff; right; left; reflexivity).
    destruct (C3 k Hk) as (K1 & CV). fold ch in CV.
    assert (ND : List.NoDup (ks ++ [k])) by (rewrite <- Hks; destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & N9 & _) & _); exact N9).
    assert (NK : ~ In k ks) by (pose proof (NoDup_remove_2 ks [] k ND) as X; rewrite app_nil_r in X; exact X).
    assert (BC : blk_class n = c) by ((lazymatch goal with |- ?G => let G' := eval unfold blk_class in G in change_no_check G' end); exact Hcl).
    assert (AB : prim_alloc_beg p n = ch) by ((lazymatch goal with |- ?G => let G' := eval unfold prim_alloc_beg, p in G in change_no_check G' end); lia).
    pose proof (rz_range n) as RZ. pose proof (rz_mod16 n) as RZ16.
    destruct (carved_range bt st Lc FF W c ch Hc CV) as (CR1 & CR2 & CR3 & CR4 & CR5).
    pose proof (prim_user_in_chunk n ltac:(lia) HP) as (U1 & U2). rewrite Hcl in U1, U2.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    (* [comment removed for export] *)
    assert (CC : in_cache_c bt st c ch) by (exists k; split; [exact Hk | reflexivity]).
    destruct (WR1 c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & PART & FHK).
    pose proof PART as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
    assert (NL : ~ in_live_c Lc c ch) by (intros X; exact (P3 ch (conj X CC))).
    assert (NQ : ~ in_quar_c st c ch) by (intros X; exact (P5 ch (conj X CC))).
    assert (NIn : ~ In (p, n) Lc).
    { intros X. apply NL. exists p, n. repeat split; assumption. }
    (lazymatch goal with |- ?G => let G' := eval unfold WF, op_cache_pop, set_cache in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact] in G in change_no_check G' end).
    rewrite Hks, removelast_last.
    split; [| split; [| split; [exact WQ | split; [| split; [| split; [exact WK | split; [exact WD | split; [exact WM | split; [exact WMP | destruct G as ((GA & GC & GB) & GOK); split; [split; [exact GA | split; [(lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [PHI snd] in G in change_no_check G' end); lia]] | exact GOK]]]]]]]]]].
    - (* [comment removed for export] *) split; [| intros c' Hc'; destruct (WR2 c' Hc') as [E1 E2]; (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cache] in G in change_no_check G' end); split; [exact E1|]; (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c' c); [lia | exact E2]].
      intros c' Hc'. destruct (WR1 c' Hc') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART' & FHK').
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cache] in G in change_no_check G' end). repeat (split; [assumption|]). split; [| exact FHK'].
      destruct (Z.eq_dec c' c) as [-> | NE].
      + (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval unfold partition_c in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold in_cache_c, in_fa_c, in_batch in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache a_reg a_tq a_gq] in G in change_no_check G' end). rewrite fupdZ_same.
        unfold in_cache_c, in_fa_c, in_batch in P1, P2, P3, P4, P5, P6, P7, P8. rewrite Hks in P1, P3, P5, P7, P8.
        assert (CK : forall a, (exists k', In k' (ks ++ [k]) /\ a = chunk_of_compact SBEG c k') <->
                               ((exists k', In k' ks /\ a = chunk_of_compact SBEG c k') \/ a = ch)).
        { intros a. split.
          - intros (k' & Hk' & ->). apply in_app_iff in Hk'. destruct Hk' as [Hk'|[<-|[]]]; [left; exists k'; split; [exact Hk'|reflexivity] | right; reflexivity].
          - intros [(k' & Hk' & ->)| ->]; [exists k'; split; [apply in_app_iff; left; exact Hk'|reflexivity] | exists k; split; [apply in_app_iff; right; left; reflexivity|reflexivity]]. }
        assert (CI : forall k', ch = chunk_of_compact SBEG c k' -> k' = k).
        { intros k' E. apply (f_equal (compact_of SBEG c)) in E. unfold ch in E. rewrite !compact_roundtrip_k in E. symmetry. exact E. }
        split; [| split; [| split; [| split; [| split; [| split; [exact P6 | split; [| split; [| split; [exact (NoDup_remove_1 ks [] k ltac:(rewrite app_nil_r; exact ND) ) || (pose proof (NoDup_remove_1 ks [] k ND) as X; rewrite app_nil_r in X; exact X) | exact P10]]]]]]]]].
        * intros a. rewrite in_live_c_cons, (P1 a), (CK a). split.
          -- intros [X|[X|[[X|X]|[X|X]]]]; try am_tauto. left; left. split; [exact HP|]. split; [exact BC|]. rewrite AB. symmetry. exact X.
          -- intros [[(_ & _ & X)|X]|[X|[X|[X|X]]]]; try am_tauto. right; right; left. right. rewrite <- X, AB. reflexivity.
        * intros a [X Y]. apply in_live_c_cons in X. destruct X as [(_ & _ & X)|X]; [| exact (P2 a (conj X Y))]. rewrite AB in X. subst a. exact (NQ Y).
        * intros a [X Y]. apply in_live_c_cons in X. destruct X as [(_ & _ & X)|X].
          -- rewrite AB in X. subst a. destruct Y as (k' & Hk' & E). rewrite <- (CI k' E) in NK. exact (NK Hk').
          -- apply (P3 a). split; [exact X | apply (CK a); left; exact Y].
        * intros a [X Y]. apply in_live_c_cons in X. destruct X as [(_ & _ & X)|X]; [| exact (P4 a (conj X Y))].
          rewrite AB in X. subst a. apply (P7 ch). split; [apply (CK ch); right; reflexivity | exact Y].
        * intros a [X Y]. apply (P5 a). split; [exact X | apply (CK a); left; exact Y].
        * intros a [X Y]. apply (P7 a). split; [apply (CK a); left; exact X | exact Y].
        * intros a Hb Hc24 X. apply (P8 a Hb Hc24). destruct X as [X|[X|[X|X]]].
          -- apply in_live_c_cons in X. destruct X as [(_ & _ & X)|X]; [| left; exact X]. rewrite AB in X. subst a.
             right; right; left. apply (CK ch). right. reflexivity.
          -- right; left; exact X.
          -- right; right; left. apply (CK a). left. exact X.
          -- right; right; right. exact X.
      + (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval unfold partition_c, in_cache_c in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache] in G in change_no_check G' end). rewrite (fupdZ_other _ _ _ _ _ NE).
        apply (partition_live_ext st Lc). 2: exact PART'.
        intros a. rewrite in_live_c_cons. split; [intros [(_ & X & _)|X]; [exfalso; apply NE; rewrite <- X, BC; reflexivity | exact X] | intros X; right; exact X].
    - (* [comment removed for export] *) intros c' Hc'. destruct (WC c' Hc') as (D1 & D2 & D3). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache a_cinit] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE].
      + rewrite Hks in D1, D3. rewrite length_app in D1. cbn [length] in D1. split; [lia|]. split; [intros Hf; rewrite (proj1 (D2 Hf)) in Hks; destruct ks; discriminate Hks|].
        intros k' Hk'. apply D3. apply in_app_iff. left. exact Hk'.
      + exact (conj D1 (conj D2 D3)).
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_sec a_nres a_tq a_gq] in G in change_no_check G' end). repeat (split; [assumption|]).
      split. { intros s0 Hs. rewrite <- (S6 s0 Hs). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). split; [intros [E|X]; [| exact X] | intros X; right; exact X].
               exfalso. destruct (S4 s0 Hs) as (N64 & _). injection E as E1 E2. apply (is_primary_iff n ltac:(lia)) in HP. lia. }
      split; [| exact S8]. intros p' n' [E|Hin] HP'; [injection E as <- <-; rewrite HP in HP'; discriminate HP' | exact (S7 p' n' Hin HP')].
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split; [| split].
      + intros p' n' [E|Hin]; [injection E as <- <- | exact (L1 p' n' Hin)].
        split; [lia|]. split.
        { (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end). rewrite <- Zplus_mod_idemp_r, <- Zplus_mod_idemp_l, CR5, RZ16. reflexivity. }
        split; [apply (space_ablk st Lc FF W); (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end); ulia|]. intros _. rewrite BC, AB. exact CV.
      + constructor; [exact NIn | exact L2].
      + intros p1 n1 p2 n2 [E1|H1] [E2|H2] NE.
        * exfalso. apply NE. rewrite <- E1, <- E2. reflexivity.
        * injection E1 as <- <-. destruct (L1 p2 n2 H2) as (M1 & M2 & (M3 & M4 & M6 & M7) & M5).
          destruct (is_primary n2) eqn:HP2.
          -- pose proof (live_chunk bt st Lc FF W p2 n2 H2 HP2) as G2. cbn zeta in G2. destruct G2 as (G1' & G2' & G3' & G4' & G5' & G6').
             destruct (chunk_cases bt st Lc FF W c ch (blk_class n2) (prim_alloc_beg p2 n2) Hc G1' CV G2') as [[EC EA] | D].
             ++ exfalso. apply NL. rewrite EC, EA. exact G3'.
             ++ (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end). unfold prim_alloc_beg in *. (first [clear - D G6' G5' U1 RZ | idtac]; lia).
          -- destruct (live_sec bt st Lc FF W p2 n2 H2 HP2) as (sc & Hs & Eu & En).
             destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
             destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end); (first [clear - H A6 En Eu CR3 RZ A5 U1 CR4 | idtac]; ulia).
        * injection E2 as <- <-. destruct (L1 p1 n1 H1) as (M1 & M2 & (M3 & M4 & M6 & M7) & M5).
          destruct (is_primary n1) eqn:HP1.
          -- pose proof (live_chunk bt st Lc FF W p1 n1 H1 HP1) as G2. cbn zeta in G2. destruct G2 as (G1' & G2' & G3' & G4' & G5' & G6').
             destruct (chunk_cases bt st Lc FF W c ch (blk_class n1) (prim_alloc_beg p1 n1) Hc G1' CV G2') as [[EC EA] | D].
             ++ exfalso. apply NL. rewrite EC, EA. exact G3'.
             ++ (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end). unfold prim_alloc_beg in *. (first [clear - D G6' G5' U1 RZ | idtac]; lia).
          -- destruct (live_sec bt st Lc FF W p1 n1 H1 HP1) as (sc & Hs & Eu & En).
             destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
             destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end); (first [clear - H A6 En Eu CR3 RZ A5 U1 CR4 | idtac]; ulia).
        * exact (L3 p1 n1 p2 n2 H1 H2 NE).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma writableZ_of_def : forall M lo hi, (forall i, lo <= i < hi -> M (Z_to_bv 64 i) <> None) -> writableZ SG M lo hi.
  Proof using. intros M lo hi H i Hi. split; [exact (H i Hi) | apply store_ok1_some; exact (H i Hi)]. Qed.

  Lemma writableZ_sub : forall M lo hi lo' hi', writableZ SG M lo hi -> lo <= lo' -> hi' <= hi -> writableZ SG M lo' hi'.
  Proof using. intros M lo hi lo' hi' W A B i Hi. apply W. lia. Qed.

  (* [comment removed for export] *)
  Lemma rep_shadow_frame_grow : forall st Lc Lc' M M',
    DEFK M M' -> rep_shadow bt st Lc M ->
    (forall g, live_granule Lc g -> live_granule Lc' g) ->
    (forall c, 1 <= c <= 30 -> 0 <= region_beg SBEG c /\ region_beg SBEG c + r_mapped_user (a_reg st c) <= CEIL
                            /\ 0 <= fa_beg SBEG c /\ fa_beg SBEG c + r_mapped_fa (a_reg st c) <= CEIL) ->
    (forall sc, In sc (a_sec st) -> 0 <= sc_map sc /\ sc_map sc + sc_mapsz sc <= CEIL /\ sc_map sc <= sc_user sc /\ sc_user sc + sc_n sc <= sc_map sc + sc_mapsz sc
                                    /\ (sc_map sc + sc_mapsz sc) mod 8 = 0) ->
    (forall c i, 1 <= c <= 30 -> foot_shreg bt st Lc' c i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall sc i, In sc (a_sec st) -> foot_shsec st sc i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_shadow bt st Lc' M'.
  Proof using.
    intros st Lc Lc' M M' DEF (S1 & S2 & S3 & S4 & S5 & S6) MONO RC RS AG AGS. (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
    try ceil; unfold foot_shreg, foot_shsec, user_granule, sh_lo, SB in *.
    split. { intros c g Hc Hg NL. destruct (RC c Hc) as (Q1 & Q2 & Q3 & Q4).
             assert (NL0 : ~ live_granule Lc g) by (intros X; exact (NL (MONO g X))).
             pose proof (S1 c g Hc Hg NL0) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [clear -Hg Q1; Ztac | clear -Hg Q2; Ztac |]. apply (AG c); [exact Hc | | clear -Hg Q1 Q2; Ztac]. left.
             replace (0x7fff8000 + g - 0x7fff8000) with g by lia. split; [clear -Hg; Ztac | exact NL]. }
    split. { intros c g Hc Hg. destruct (RC c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (S2 c g Hc Hg) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [clear -Hg Q3; Ztac | clear -Hg Q4; Ztac |]. apply (AG c); [exact Hc | right; clear -Hg; Ztac | clear -Hg Q3 Q4; Ztac]. }
    split. { intros sc g Hs Hg NU. destruct (RS sc Hs) as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (S3 sc g Hs Hg NU) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [clear -Hg Q1; Ztac | clear -Hg Q2; Ztac |]. apply (AGS sc); [exact Hs | | clear -Hg Q1 Q2; Ztac].
             replace (0x7fff8000 + g - 0x7fff8000) with g by lia. split; [clear -Hg; Ztac | left; exact NU]. }
    split. { intros sc g Hs HQ HU. destruct (RS sc Hs) as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (S4 sc g Hs HQ HU) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [clear -HU Q1 Q3; Ztac | clear -HU Q2 Q4 Q5; Ztac |]. apply (AGS sc); [exact Hs | | clear -HU Q1 Q2 Q3 Q4 Q5; Ztac].
             replace (0x7fff8000 + g - 0x7fff8000) with g by lia. split; [clear -HU Q3 Q4 Q5; Ztac | right; exact HQ]. }
    split. { intros c g Hc Hg. exact (def_keep M M' _ DEF (S5 c g Hc Hg)). }
    intros sc g Hs Hg. exact (def_keep M M' _ DEF (S6 sc g Hs Hg)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem OPS_REP_cache_hit_pf : OPS_REP_cache_hit bt.
  Proof using.
    intros st Lc FF M M' mdl mdl' c ks k n W R Hc Hks Hn HP Hcl. cbn zeta. intros AGR CNT HDR SH0 SHK SBM MI.
    set (ab := chunk_of_compact SBEG c k) in *. set (p := ab + rz n) in *.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (L1 & L2 & L3) & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    destruct (space_facts st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by lia.
    destruct (WC c Hc) as (C1 & C2 & C3).
    assert (Hk : In k (a_cache st c)) by (rewrite Hks; apply in_app_iff; right; left; reflexivity).
    destruct (C3 k Hk) as (K1 & CV). fold ab in CV.
    assert (BC : blk_class n = c) by ((lazymatch goal with |- ?G => let G' := eval unfold blk_class in G in change_no_check G' end); exact Hcl).
    assert (AB : prim_alloc_beg p n = ab) by ((lazymatch goal with |- ?G => let G' := eval unfold prim_alloc_beg, p in G in change_no_check G' end); lia).
    pose proof (rz_range n) as RZ.
    destruct (carved_range bt st Lc FF W c ab Hc CV) as (CR1 & CR2 & CR3 & CR4 & CR5).
    pose proof (prim_user_in_chunk n ltac:(lia) HP) as (U1 & U2). rewrite Hcl in U1, U2.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    assert (CC : in_cache_c bt st c ab) by (exists k; split; [exact Hk | reflexivity]).
    destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK). pose proof PART as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
    assert (NL : ~ in_live_c Lc c ab) by (intros X; exact (P3 ab (conj X CC))).
    assert (NQ : ~ in_quar_c st c ab) by (intros X; exact (P5 ab (conj X CC))).
    pose proof (agrees_DEFK _ _ _ AGR) as DEF. pose proof (agrees_at' _ _ _ AGR) as AGF.
    (* [comment removed for export] *)
    assert (FZ : forall i, foot_cache_hit bt c p n i -> (T <= i < T + PG) \/ (ab <= i < ab + csize c) \/ (SB <= i < AS_HEAPLO) \/ CEIL <= i).
    { intros i Hf. unfold foot_cache_hit, T_PC, PC_SZ, sh_lo, sh_hi in Hf. clear -Hf Hc CR3 CR4 X14 X15 U1 RZ Hn.
      unfold p in Hf. try ceil; unfold AS_HEAPLO, SB, PG, KSPACE, NMAX in *. Ztac. }
    assert (AGZ : forall i, 0 <= i -> i < CEIL -> ~ (T <= i < T + PG) -> ~ (ab <= i < ab + csize c) -> ~ (SB <= i < AS_HEAPLO) ->
                  M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i H0 H1 N1 N2 N3. apply AGF; [| ulia]. intros Hf. destruct (FZ i Hf) as [Z|[Z|[Z|Z]]]; ulia. }
    (* [comment removed for export] *)
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    assert (IMGfree : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply AGZ; [ulia | ulia | | | ulia].
      - intros X. destruct (dyn_kind_facts bt st Lc FF W i (dyn_kind_fixed bt st _ _ i INT X)) as (_ & _ & NH & _). exact (NH Hi).
      - intros X. destruct (dyn_kind_facts bt st Lc FF W i (dyn_kind_space bt st Lc FF W i ltac:(ulia))) as (_ & _ & NH & _). exact (NH Hi). }
    assert (IMGK : forall i, img_kind bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i [Hi _] _. exact (IMGfree i Hi). }
    assert (FIXfree : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> PG -> hi - lo < KSPACE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hin Hlen Hlen2 i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hin)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hin) (all_ranges_fixed bt st _ INT)
                    ltac:(intros E; injection E; intros; ulia)) as D. hnf in D. cbn in D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hin Hlen2); apply AGZ; (first [clear - Hr A3 Hi D H CR3 A5 CR4 | idtac]; ulia). }
    assert (DYNfree : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hin i Hi Hr. destruct (RNG _ _ (all_ranges_dyn bt st _ Hin)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT Hin) as D. hnf in D. cbn in D.
      destruct (space_vs_dyn bt st Lc FF W lo hi Hin); apply AGZ; (first [clear - Hr A3 Hi D H CR3 A5 CR4 | idtac]; ulia). }
    assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((TD1 & TD2 & TD3 & _ & TD5) & _). box TD5.
    assert (RIfree : forall i, SBEG + KSPACE <= i < SBEG + KSPACE + PG -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply AGZ; ulia. }
    assert (CHKfree : forall c' a', 1 <= c' <= 30 -> carved bt st c' a' -> ~ (c' = c /\ a' = ab) ->
                      forall i, a' <= i < a' + csize c' -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c' a' Hc' CV' NE i Hi. destruct (carved_range bt st Lc FF W c' a' Hc' CV') as (D1 & D2 & D3 & D4 & D5).
      destruct (chunk_cases bt st Lc FF W c ab c' a' Hc Hc' CV CV') as [[EC EA] | D]; [exfalso; apply NE; split; congruence|].
      apply AGZ; (first [clear - D3 Hi X14 D4 X15 TPG D SPH R6a | idtac]; ulia). }
    assert (FAfree : forall c0, 1 <= c0 <= 30 -> forall i, fa_beg SBEG c0 <= i < fa_beg SBEG c0 + 2 ^ 29 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c0 Hc0 i Hi. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & _).
      apply AGZ; [ulia | ulia | ulia | | ulia].
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c0 c) as [LT|[->|GT]]; [| ulia |].
      - assert (c0 * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). ulia.
      - assert (c * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (c * 2 ^ 32 + 2 ^ 32) with ((c + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). ulia. }
    (* [comment removed for export] *)
    assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros p' n' i Hown Hf Hr.
      destruct (hdr_zone bt st Lc FF W p' n' i Hown Hf) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')].
      - apply (CHKfree (blk_class n') (prim_alloc_beg p' n') HC' CV'); [| lia]. intros [EC EA].
        destruct Hown as [HL | HQ'].
        + pose proof (live_chunk bt st Lc FF W p' n' HL HP') as G'. cbn zeta in G'. destruct G' as (_ & _ & G3 & _). apply NL. rewrite <- EC, <- EA. exact G3.
        + pose proof (quar_chunk bt st Lc FF W (p' - 16) n' HQ' HP') as G'. cbn zeta in G'. replace (p' - 16 + 16) with p' in G' by lia.
          destruct G' as (_ & _ & G3 & _). apply NQ. rewrite <- EC, <- EA. exact G3.
      - destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNfree _ _ (sec_dyn st sc' Hs')); ulia. }
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & YC).
    (lazymatch goal with |- ?G => let G' := eval unfold op_cache_pop in G in change_no_check G' end). rewrite Hks, removelast_last. (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Y2, Y4, Y6, Y8, Y10, Y12, Y14, Y16.
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact R1 | exact YC |]. intros c0 i Hc0 Hi. rewrite Forall_forall in YC. destruct (YC c0 Hc0).
             exact (IMGK i (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) ltac:(lia)). }
    (* [comment removed for export] *)
    split. { change (rep_instance bt st M'). eapply rep_instance_frame; [exact DEF | exact R2 | ulia | ulia | ulia | ulia | exact S1 |].
             intros i Hi Hr. destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
             - pose proof W as (_ & _ & _ & (SS1 & SS2 & SS3 & _) & _). apply (FIXfree _ _ IN8); ulia.
             - exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact Hi | exact NI])) Hr). }
    (* [comment removed for export] *)
    split. { destruct R3 as (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TW & TC1 & TC2 & TC3 & TC4). (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_cinit a_cache set_cache] in G in change_no_check G' end).
             assert (AGT : forall i, ((T <= i < T + T_PC + PC_SZ * c \/ T + T_PC + PC_SZ * c + 4 <= i < T + 2768 \/ T + 3168 <= i < T + PG)
                                      \/ (bt_tctx bt <= i < bt_tctx bt + 160)) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros i Hi Hr. destruct Hi as [Hi | Hi].
               - apply AGF; [| exact Hr]. intros Hf. unfold foot_cache_hit, sh_lo, sh_hi in Hf. unfold T_PC, PC_SZ in *.
                 destruct Hf as [Z|[Z|[Z|[Z|Z]]]]; try (first [clear - Z Hi Hc TPG U1 CR4 CR3 X2 | idtac]; ulia); clear -Z Hi Hc CR3 CR4 X14 X15 X1 X2 U1 RZ Hn TPG TD5; unfold p in Z; try ceil; unfold AS_HEAPLO, AS_LO, SB, PG, KSPACE, NMAX in *; Ztac.
               - apply (FIXfree _ _ INC); ulia. }
             unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
             split; [frZ AGT T1|]. split; [frZ AGT T2|]. split; [frZ AGT T3|]. split; [frB AGT T4|]. split; [frZ AGT T5|]. split; [frB AGT T6|].
             split. { eapply rep_list_frame; [exact TL | ulia | ulia |]. intros i Hi Hr. apply AGT; ulia. }
             split. { intros c' Hc'. pose proof (cache_len bt st Lc FF W c' Hc') as CL'. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE].
                      - destruct (TP c Hc) as (PC1 & PC2 & PC3 & PC4). (lazymatch goal with |- ?G => let G' := eval unfold rep_pclass in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). unfold T_PC, PC_SZ in PC1, PC2, PC3, PC4.
                        rewrite Hks in CL'. rewrite length_app in CL'. cbn [length] in CL'.
                        split; [exact CNT|]. split; [frZ AGT PC2|]. split; [frZ AGT PC3|].
                        intros i k' Hk'. pose proof (nth_error_lt _ _ _ Hk') as Hl.
                        pose proof (PC4 i k' ltac:(rewrite Hks, nth_error_app1 by exact Hl; exact Hk')) as CC4. frZ AGT CC4.
                      - eapply rep_pclass_frame; [exact (TP c' Hc') | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | exact CL' |]. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). intros i Hi Hr. apply AGT; [| exact Hr]. left.
                        clear -Hi NE Hc Hc'. nia. }
             split; [frW DEF TW|]. split; [frZ AGT TC1|]. split; [frZ AGT TC2|]. split; [frZ AGT TC3 | frZ AGT TC4]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. destruct (R4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
             change (a_reg (set_cache st c ks) c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | ulia | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. unfold foot_region in Hi. destruct Hi as [[Hi _] | Hi]; [apply RIfree; ulia | apply (FAfree c0 Hc0); ulia]. }
    (* [comment removed for export] *)
    assert (BR : forall b, In b (a_tq st ++ a_gq st) -> 0 <= ba_addr b /\ ba_addr b + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b)) <= BATCHCAP).
    { intros b Hb. destruct (batch_facts bt st Lc FF W b Hb) as (_ & BL1 & BL2 & BL3). ulia. }
    assert (BA : forall b i, In b (a_tq st ++ a_gq st) -> foot_batch b i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros b i Hb Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL1 & BL2 & BL3).
      apply (CHKfree BATCHCLASS (ba_addr b) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb); [| change (csize BATCHCLASS) with 8192; ulia].
      intros [EC EA]. destruct (WR1 BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _).
      destruct PARTB as (_ & _ & _ & _ & _ & _ & _ & NB & _).
      apply (NB (ba_addr b) ltac:(exists b; split; [exact Hb | reflexivity]) eq_refl). right; right; left. rewrite EA, EC. exact CC. }
    split. { change (a_tq (set_cache st c ks)) with (a_tq st). eapply rep_batches_frame; [exact DEF | exact R5 | intros b Hb; apply BR; apply in_app_iff; left; exact Hb |].
             intros b i Hb Hi Hr. apply (BA b i); [apply in_app_iff; left; exact Hb | exact Hi | exact Hr]. }
    split. { change (a_gq (set_cache st c ks)) with (a_gq st). eapply rep_batches_frame; [exact DEF | exact R6 | intros b Hb; apply BR; apply in_app_iff; right; exact Hb |].
             intros b i Hb Hi Hr. apply (BA b i); [apply in_app_iff; right; exact Hb | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNfree _ _ (sec_dyn st sc Hs)); ulia. }
    (* [comment removed for export] *)
    split. { destruct R8 as [HL HQ]. split.
             - intros p' n' [E | Hin]; [injection E as <- <-; exact HDR|].
               destruct (live_range bt st Lc FF W p' n' Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n').
               eapply rep_hdr_frame; [exact DEF | exact (HL p' n' Hin) | ulia | ulia |]. intros i Hi Hr. exact (HDRfree p' n' i (or_introl Hin) Hi Hr).
             - change (quar (set_cache st c ks)) with (quar st). intros m n' Hin. destruct (HQ m n' Hin) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m n' Hin) as (A1 & A2 & A3). pose proof (rz_range n').
               eapply rep_hdr_frame; [exact DEF | exact Hh | ulia | ulia |]. intros i Hi Hr.
               apply (HDRfree (m + 16) n' i); [right; replace (m + 16 - 16) with m by lia; exact Hin | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact R9 | ulia | ulia | ulia | ulia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). ulia.
             - intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) Hr).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hb. set (b := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody b.
               destruct HIn as [Eb | Hnb].
               + apply (FIXfree _ _ INN); [ulia | ulia | rewrite Eb; lia | exact Hr].
               + apply (DYNfree _ _ (node_dyn st b Hnb)); [lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2].
             eapply rep_fake_frame; [exact DEF | exact R10 | ulia | ulia | ulia | ulia | ulia | ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXfree _ _ INFS); ulia.
               + exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) Hr).
               + (* [comment removed for export] *) destruct (dtls_cell_facts bt st Lc FF W i Hi) as (DF1 & DF2 & DF3 & DF4 & DF5 & DF6 & DF7).
                 apply AGZ; [lia | exact DF2 | exact DF5 | | clear -DF4; ulia].
                 intros X. apply (DF6 _ _ IN6 ltac:(clear -R6a R6b; unfold KSPACE, PG in *; lia)). clear -X CR3 CR4 R6a R6b. ulia.
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXfree _ _ INFS); ulia. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact R11 | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) Hr). }
    (* [comment removed for export] *)
    split. { change (rep_shadow bt st ((p, n) :: Lc) M'). eapply (rep_shadow_frame_grow st Lc); [exact DEF | exact R12 | | | | |].
             - intros g (p' & n' & Hin & Hg). exists p', n'. split; [right; exact Hin | exact Hg].
             - intros c0 Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _). ulia.
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A3 A4 A5 A6 A7. try ceil; unfold PG, AS_HEAPLO, NMAX in *. Ztac.
             - intros c0 i Hc0 Hi Hr. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14).
               apply AGF; [| exact Hr]. intros Hf. unfold foot_shreg, sh_lo in Hi. unfold foot_cache_hit, sh_lo, sh_hi in Hf.
               destruct Hf as [Z|[Z|[Z|[Z|Z]]]].
               + clear -Z Hi Hc X1 X14 TD5 E1 E2 E5 E6 E8 X15. Zlia.
               + clear -Z Hi Hc X1 X14 TD5 E1 E2 E5 E6 E8 X15. Zlia.
               + clear -Z Hi Hc X14 SBH CR3 CR4 RZ U1 Hn E1 E2 E5 E6 X15. unfold p in *. Zlia.
               + destruct Hi as [[Hi NLV] | Hi].
                 * apply NLV. exists p, n. split; [left; reflexivity|]. (lazymatch goal with |- ?G => let G' := eval unfold user_granule in G in change_no_check G' end). clear -Z. Zlia.
                 * (* [comment removed for export] *)
                   pose proof (pg8 _ E12) as AL. unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
                   destruct (Z.lt_ge_cases c0 c) as [LT|GE].
                   -- assert (HM : c0 * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
                      clear -Z Hi HM E6 CR1 RZ. unfold p in *. Zlia.
                   -- assert (HM : c * 2 ^ 32 <= c0 * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; lia).
                      clear -Z Hi HM AL CR2 Q2 Q3 U1. unfold p in *. Zlia.
               + clear -Z Hi E2 E5 E6 X15. Zlia.
             - intros sc i Hs Hi Hr. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply AGF; [| exact Hr]. intros Hf. unfold foot_shsec, sh_lo in Hi. destruct Hi as [Hi _]. unfold foot_cache_hit, sh_lo, sh_hi in Hf.
               unfold p in *.
               destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [D|D];
               destruct Hf as [Z|[Z|[Z|[Z|Z]]]]; clear -Z Hi D A1 A2 X1 X14 X15 TD5 SBH CR3 CR4 U1 RZ Hn Hc; Zlia. }
    (* [comment removed for export] *)
    split. { change (rep_ledger bt st mdl'). exact (rep_ledger_sbm bt st mdl mdl' SBM R13). }
    (* [comment removed for export] *)
    split. { destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_aa a_reg a_sec a_dep a_kact set_cache] in G in change_no_check G' end).
             pose proof (same_but_materialized_frame mdl mdl' SBM) as Fm.
             destruct Fm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
             split; [exact B1|]. split; [exact MI|]. split; [exact B3|].
             split. { intros p' n' [E | Hin]; [| exact (B4 p' n' Hin)]. injection E as <- <-. destruct (B5 c Hc) as [BU _].
                      intros a Ha. apply BU. unfold sh_lo, sh_hi in *. pose proof (pg8 _ Q11) as AL. pose proof (pg8 _ Q13) as AL2.
                      clear -Ha AL AL2 CR1 CR2 Q2 Q3 U1 RZ Hn. unfold p, SB in *. Ztac. }
             split; [exact B5|]. split; [exact B6|]. split; [exact B7|].
             rewrite E3. change (prim_charge (set_cache st c ks)) with (prim_charge st). change (sec_charge (set_cache st c ks)) with (sec_charge st).
             change (depot_charge (set_cache st c ks)) with (depot_charge st). change (a_shsec (set_cache st c ks)) with (a_shsec st). exact B8. }
    (* [comment removed for export] *)
    split. { intros p' n' [E | Hin].
             - injection E as <- <-. destruct (R4 c Hc) as [_ (_ & _ & F3)]. split.
               + eapply writableZ_sub; [frW DEF F3 | ulia | ulia].
               + apply writableZ_of_def. intros i Hi. apply (def_keep M M' _ DEF).
                 destruct R12 as (_ & _ & _ & _ & S5' & _). unfold sh_lo, sh_hi in Hi.
                 replace i with (SB + (i - SB)) by lia. apply (S5' c (i - SB) Hc).
                 pose proof (pg8 _ Q11) as AL. pose proof (pg8 _ Q13) as AL2.
                 clear -Hi AL AL2 CR1 CR2 Q3 U1 RZ Hn. unfold p, SB in *. Ztac.
             - destruct (R15 p' n' Hin) as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f k0 Hf. frW DEF (R16 f k0 Hf). }
    split; [eapply (cellZ_frame _ _ _ _ _ _ R17); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia)) ltac:(ulia))] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ R18); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia)) ltac:(ulia))] |].
    exact (rep_last_keep bt _ _ M M' DEF R19 (fun H => H)).
  Qed.

End Pf.
