(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsAinvOpsQ3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stmts.
  Context {RUN : run_ceil}.

  (* [comment removed for export] *)
  Definition foot_quar_newbatch (T p n ba : Z) (tq : list batch) (a : Z) : Prop :=
    a = p - 16 \/ (p <= a < p + 8) \/ (sh_lo p <= a < sh_hi p n)
    \/ (ba <= a < ba + 32)
    \/ (T + T_QC <= a < T + T_QC + 32)
    \/ (match rev tq with [] => False | b :: _ => ba_addr b <= a < ba_addr b + 8 end)
    \/ (T + T_PC + PC_SZ * BATCHCLASS <= a < T + T_PC + PC_SZ * BATCHCLASS + 4)
    \/ (T + 2768 <= a < T + 3168) \/ CEIL <= a.

  (* [comment removed for export] *)
  Definition OBL_cache_chunk_stmt (bt : as_boot) : Prop := forall st Lc FF M mdl c k,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 -> In k (a_cache st c) ->
    let a := chunk_of_compact (bt_spacebeg bt) c k in
    carved bt st c a /\ AS_HEAPLO <= a /\ a + csize c <= CEIL /\ a mod 16 = 0 /\ 0 <= k < 2 ^ 32
    /\ (a + csize c <= bt_thread bt \/ bt_thread bt + PG <= a)
    /\ (bt_tctx bt + 0x10000 <= a \/ a + csize c <= bt_tctx bt)
    /\ (forall p n, In (p, n) Lc -> a + csize c <= p - 16 \/ p + up8 n <= a)
    /\ (forall b, In b (a_tq st ++ a_gq st) -> a + csize c <= ba_addr b \/ ba_addr b + BATCHSZ <= a)
    /\ (forall z, a <= z < a + csize c -> lzb mdl z = false)
    /\ writableZ (bt_segs bt) M a (a + csize c)
    /\ (forall z, a <= z < a + csize c -> rt_priv (bt_ia bt) Lc FF z).

End Stmts.

Section Q.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Ztac := try ceil; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem OBL_cache_chunk_pf : OBL_cache_chunk_stmt bt.
  Proof using.
    intros st Lc FF M mdl c k W R Hc Hk. cbn zeta.
    set (a := chunk_of_compact SBEG c k).
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & WL & WK & WD & WM & (RNG & PWS & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    destruct (WC c Hc) as (C1 & C2 & C3). destruct (C3 k Hk) as [Kr CV]. fold a in CV.
    destruct (carved_range bt st Lc FF W c a Hc CV) as (A1 & A2 & A3 & A4 & A5).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (csize_pos c Hc) as ((CS1 & CS2) & CS3).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & _).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). box SP4. box SP5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    assert (INC' : in_cache_c bt st c a) by (exists k; split; [exact Hk | reflexivity]).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as SPC.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, FAKE_SIZE in G in change_no_check G' end); lia)) as SPF. box SPT. box SPC. box SPF.
    (* [comment removed for export] *)
    assert (LIVE : forall p n, In (p, n) Lc -> a + csize c <= p - 16 \/ p + up8 n <= a).
    { intros p n Hin. destruct (live_ext bt st Lc FF W p n Hin) as (lo & hi & EXT & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
      destruct EXT as [(HP & Elo & Ehi & CV' & HC' & LIV & S1 & S2) | (HP & sc & Hs & Eu & En & Elo & Ehi)].
      - destruct (chunk_cases bt st Lc FF W c a (blk_class n) lo Hc HC' CV CV') as [[EC EA] | D].
        + exfalso. destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK). destruct PART as (_ & _ & LC & _).
          apply (LC a). split; [rewrite EC, EA; exact LIV | exact INC'].
        + subst lo hi. unfold up8 in *. clear -D B2 B8 CS1. lia.
      - destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [DS|DS]; subst lo hi;
          destruct (sec_facts bt st Lc FF W sc Hs) as (F1 & F2 & _); unfold up8 in *; clear -DS B1 B2 B8 A3 A4 X14 X15 F1 F2; ulia. }
    split; [exact CV|]. split; [clear -A3 SPH SP7; ulia|]. split; [clear -A4 X15; ulia|]. split; [exact A5|]. split; [exact Kr|].
    split; [clear -SPT A3 A4; Zlia|].
    split; [clear -SPC A3 A4; Zlia|].
    split; [exact LIVE|].
    split. { intros b Hb. destruct (batch_facts bt st Lc FF W b Hb) as (CVB & BL & B1 & B2).
             destruct (chunk_cases bt st Lc FF W c a BATCHCLASS (ba_addr b) Hc ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CV CVB) as [[EC EA] | D].
             - exfalso. destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK). destruct PART as (_ & _ & _ & _ & _ & _ & _ & NB & _).
               apply (NB a ltac:(exists b; split; [exact Hb | symmetry; exact EA]) EC). right. right. left. exact INC'.
             - change (csize BATCHCLASS) with 8192 in D. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). lia. }
    split. { intros z Hz. exact (rep_nolazy_chunk bt st Lc FF M mdl W R c a z Hc CV Hz). }
    split. { destruct R as (_ & _ & _ & R4 & _). destruct (R4 c Hc) as [_ (_ & _ & F3)]. eapply writableZ_sub; [exact F3 | lia | lia]. }
    intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold rt_priv in G in change_no_check G' end). split; [clear -Hz A4 X15; ulia|]. split; [clear -Hz A3 I2 SPH SP7; ulia|].
    destruct (heap_not_shadowish bt st Lc FF W Lc z ltac:(intros p n H; exact H) ltac:(clear -Hz A3 SPH SP7; ulia)) as (N1 & N2 & N3 & N4).
    intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
    - destruct V as (p & n & Hin & Hz'). pose proof (up8_facts n ltac:(destruct (live_range bt st Lc FF W p n Hin) as (_ & _ & L3 & _); lia)) as (U1 & _).
      destruct (LIVE p n Hin); clear -H Hz Hz' U1 CS1; lia.
    - destruct V as (f & kk & Hf & Hz'). destruct (fake_frame_facts bt st Lc FF W f kk Hf) as (F1 & F2 & F3 & F4 & _).
      clear -SPF Hz Hz' F1 F2 A3 A4. Zlia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma partition_ext_nb : forall st st' Lc Lc' c ba,
    (forall a, in_live_c Lc' c a <-> in_live_c Lc c a) ->
    (forall a, in_quar_c st' c a <-> in_quar_c st c a) ->
    (forall a, in_batch st' a <-> in_batch st a \/ a = ba) ->
    c <> BATCHCLASS ->
    a_cache st' c = a_cache st c -> a_reg st' = a_reg st ->
    partition_c bt st Lc c -> partition_c bt st' Lc' c.
  Proof using.
    intros st st' Lc Lc' c ba HL HQ HB NC EC ER H. unfold partition_c in *.
    unfold in_cache_c, in_fa_c, carved in *. rewrite EC, ER.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact H9 | exact H10]]]]]]]]].
    - intros a. rewrite (HL a), (HQ a), (H1 a). split; intros X; decompose [and or] X; tauto.
    - intros a [X Y]. apply (H2 a). split; [apply (HL a); exact X | apply (HQ a); exact Y].
    - intros a [X Y]. apply (H3 a). split; [apply (HL a); exact X | exact Y].
    - intros a [X Y]. apply (H4 a). split; [apply (HL a); exact X | exact Y].
    - intros a [X Y]. apply (H5 a). split; [apply (HQ a); exact X | exact Y].
    - intros a [X Y]. apply (H6 a). split; [apply (HQ a); exact X | exact Y].
    - exact H7.
    - intros a Hb Hc X. exact (NC Hc).
  Qed.

  Lemma partition_mlq_nb : forall st st' Lc Lc' c ab ba,
    (forall a, in_live_c Lc' c a <-> in_live_c Lc c a /\ a <> ab) ->
    (forall a, in_quar_c st' c a <-> in_quar_c st c a \/ a = ab) ->
    (forall a, in_batch st' a <-> in_batch st a \/ a = ba) ->
    c <> BATCHCLASS ->
    a_cache st' c = a_cache st c -> a_reg st' = a_reg st ->
    in_live_c Lc c ab ->
    partition_c bt st Lc c -> partition_c bt st' Lc' c.
  Proof using.
    intros st st' Lc Lc' c ab ba HL HQ HB NC EC ER LAB H. unfold partition_c in *.
    unfold in_cache_c, in_fa_c, carved in *. rewrite EC, ER.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (NQ : ~ in_quar_c st c ab) by (intros X; exact (H2 ab (conj LAB X))).
    assert (NCa : ~ (exists k, In k (a_cache st c) /\ ab = chunk_of_compact SBEG c k)) by (intros X; exact (H3 ab (conj LAB X))).
    assert (NF : ~ (exists k, In k (r_free (a_reg st c)) /\ ab = chunk_of_compact SBEG c k)) by (intros X; exact (H4 ab (conj LAB X))).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact H9 | exact H10]]]]]]]]].
    - intros a. rewrite (HL a), (HQ a), (H1 a). split.
      + intros X. destruct (Z.eq_dec a ab) as [-> | NE]; [right; left; right; reflexivity|]. decompose [and or] X; tauto.
      + intros X. decompose [and or] X; try tauto. subst a. left. exact LAB.
    - intros a [X Y]. apply (HL a) in X. apply (HQ a) in Y. destruct X as [X NE]. destruct Y as [Y | Y]; [exact (H2 a (conj X Y)) | exact (NE Y)].
    - intros a [X Y]. apply (HL a) in X. destruct X as [X _]. exact (H3 a (conj X Y)).
    - intros a [X Y]. apply (HL a) in X. destruct X as [X _]. exact (H4 a (conj X Y)).
    - intros a [X Y]. apply (HQ a) in X. destruct X as [X | ->]; [exact (H5 a (conj X Y)) | exact (NCa Y)].
    - intros a [X Y]. apply (HQ a) in X. destruct X as [X | ->]; [exact (H6 a (conj X Y)) | exact (NF Y)].
    - exact H7.
    - intros a Hb Hc X. exact (NC Hc).
  Qed.

  Lemma coc_inj : forall c k k', chunk_of_compact SBEG c k = chunk_of_compact SBEG c k' -> k = k'.
  Proof using. intros c k k' E. apply (f_equal (compact_of SBEG c)) in E. rewrite !compact_roundtrip_k in E. exact E. Qed.

  (* [comment removed for export] *)
  Lemma partition_c24 : forall st st' Lc Lc' (mv : option Z) ba k ks,
    let c := BATCHCLASS in
    (forall a, in_live_c Lc' c a <-> in_live_c Lc c a /\ mv <> Some a) ->
    (forall a, in_quar_c st' c a <-> in_quar_c st c a \/ mv = Some a) ->
    (forall ab, mv = Some ab -> in_live_c Lc c ab) ->
    (forall a, in_batch st' a <-> in_batch st a \/ a = ba) ->
    a_cache st c = ks ++ [k] -> a_cache st' c = ks -> ba = chunk_of_compact SBEG c k ->
    a_reg st' = a_reg st ->
    partition_c bt st Lc c -> partition_c bt st' Lc' c.
  Proof using.
    intros st st' Lc Lc' mv ba k ks c HL HQ HMV HB EC EC' Eba ER H. unfold partition_c in *.
    unfold in_cache_c, in_fa_c in *. rewrite EC' in *. rewrite EC in *.
    assert (CVeq : forall a, carved bt st' c a <-> carved bt st c a) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold carved in G in change_no_check G' end); rewrite ER; tauto).
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (INk : In k (ks ++ [k])) by (apply in_app_iff; right; left; reflexivity).
    assert (INCba : exists k0, In k0 (ks ++ [k]) /\ ba = chunk_of_compact SBEG c k0) by (exists k; split; [exact INk | exact Eba]).
    assert (CVba : carved bt st c ba) by (apply (H1 ba); right; right; left; exact INCba).
    assert (NKks : ~ In k ks) by (intros X; pose proof (NoDup_remove_2 _ _ _ H9) as NK; rewrite app_nil_r in NK; exact (NK X)).
    (* [comment removed for export] *)
    assert (SPLIT : forall a, (exists k0, In k0 (ks ++ [k]) /\ a = chunk_of_compact SBEG c k0) <->
                              (exists k0, In k0 ks /\ a = chunk_of_compact SBEG c k0) \/ a = ba).
    { intros a. split.
      - intros (k0 & Hk0 & E0). apply in_app_iff in Hk0. destruct Hk0 as [Hk0 | [<- | []]]; [left; exists k0; split; assumption | right; rewrite E0, Eba; reflexivity].
      - intros [(k0 & Hk0 & E0) | ->]; [exists k0; split; [apply in_app_iff; left; exact Hk0 | exact E0] | exact INCba]. }
    assert (NCba : ~ (exists k0, In k0 ks /\ ba = chunk_of_compact SBEG c k0)).
    { intros (k0 & Hk0 & E0). rewrite Eba in E0. apply coc_inj in E0. subst k0. exact (NKks Hk0). }
    assert (NLba : ~ in_live_c Lc c ba) by (intros X; exact (H3 ba (conj X INCba))).
    assert (NQba : ~ in_quar_c st c ba) by (intros X; exact (H5 ba (conj X INCba))).
    assert (NFba : ~ (exists k0, In k0 (r_free (a_reg st c)) /\ ba = chunk_of_compact SBEG c k0)) by (intros X; exact (H7 ba (conj INCba X))).
    rewrite ER.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    - intros a. rewrite (CVeq a), (HL a), (HQ a), (HB a), (H1 a), (SPLIT a). split.
      + intros [X|[X|[[X| ->]|[X|[_ X]]]]].
        * destruct mv as [ab|]; [destruct (Z.eq_dec ab a) as [-> | NE]; [right; left; right; reflexivity | left; split; [exact X | congruence]] | left; split; [exact X | congruence]].
        * right; left; left; exact X.
        * right; right; left; exact X.
        * do 4 right. split; [reflexivity | right; reflexivity].
        * right; right; right; left; exact X.
        * do 4 right. split; [reflexivity | left; exact X].
      + intros [[X _]|[[X|X]|[X|[X|[_ [X| ->]]]]]]; [left; exact X | right; left; exact X | left; exact (HMV a X) | right; right; left; left; exact X | do 3 right; left; exact X | do 4 right; split; [reflexivity | exact X] |].
        right; right; left. right. reflexivity.
    - intros a [X Y]. apply (HL a) in X. apply (HQ a) in Y. destruct X as [X NE]. destruct Y as [Y|Y]; [exact (H2 a (conj X Y)) | exact (NE Y)].
    - intros a [X Y]. apply (HL a) in X. destruct X as [X _]. exact (H3 a (conj X (proj2 (SPLIT a) (or_introl Y)))).
    - intros a [X Y]. apply (HL a) in X. destruct X as [X _]. exact (H4 a (conj X Y)).
    - intros a [X Y]. apply (HQ a) in X. pose proof (proj2 (SPLIT a) (or_introl Y)) as Y'.
      destruct X as [X | X]; [exact (H5 a (conj X Y')) | exact (H3 a (conj (HMV a X) Y'))].
    - intros a [X Y]. apply (HQ a) in X. destruct X as [X | X]; [exact (H6 a (conj X Y)) | exact (H4 a (conj (HMV a X) Y))].
    - intros a [X Y]. exact (H7 a (conj (proj2 (SPLIT a) (or_introl X)) Y)).
    - intros a Hb _ X. apply (HB a) in Hb. destruct Hb as [Hb | ->].
      + apply (H8 a Hb eq_refl). destruct X as [X|[X|[X|X]]].
        * left. exact (proj1 (proj1 (HL a) X)).
        * apply (HQ a) in X. destruct X as [X|X]; [right; left; exact X | left; exact (HMV a X)].
        * right; right; left. exact (proj2 (SPLIT a) (or_introl X)).
        * tauto.
      + destruct X as [X|[X|[X|X]]].
        * exact (NLba (proj1 (proj1 (HL ba) X))).
        * apply (HQ ba) in X. destruct X as [X|X]; [exact (NQba X) | exact (NLba (HMV ba X))].
        * exact (NCba X).
        * exact (NFba X).
    - pose proof (NoDup_remove_1 _ _ _ H9) as ND. rewrite app_nil_r in ND. exact ND.
    - exact H10.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma live_not_quar : forall st Lc FF p n {qt qg : Z}, WFq bt st Lc FF qt qg -> In (p, n) Lc -> forall n', ~ In (p - 16, n') (quar st).
  Proof using.
    intros st Lc FF p n qt qg W Hin.
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM & WMP & G).
    destruct (LV1 p n Hin) as (N1 & P16 & ABL & CVL).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    intros n' HQ'. destruct (quar_item bt st Lc FF W (p - 16) n' HQ') as (N1' & [[HP' CV'] | [HP' RG']]).
      - replace (p - 16 + 16) with p in CV' by lia.
        destruct (is_primary n) eqn:HP.
        + pose proof (live_chunk bt st Lc FF W p n Hin HP) as Gv. cbn zeta in Gv. destruct Gv as (G1 & G2 & G3 & G4 & G5 & G6).
          pose proof (quar_chunk bt st Lc FF W (p - 16) n' HQ' HP') as Gq. cbn zeta in Gq. replace (p - 16 + 16) with p in Gq by lia.
          destruct Gq as (G1' & G2' & G3' & G4' & G5' & G6').
          destruct (chunk_cases bt st Lc FF W _ _ _ _ G1 G1' G2 G2') as [[EC EA] | D].
          * destruct (WR1 _ G1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK). destruct PART as (_ & LQ & _).
            apply (LQ (prim_alloc_beg p n)). split; [exact G3|]. rewrite EC, EA. exact G3'.
          * pose proof (csize_pos _ G1) as ((CS1 & _) & _). pose proof (csize_pos _ G1') as ((CS1' & _) & _). unfold prim_alloc_beg in *.
            pose proof (rz_range n). pose proof (rz_range n'). clear -D CS1 CS1' G5 G5' H H0 N1 N1'. lia.
        + destruct (live_sec bt st Lc FF W p n Hin HP) as (sc & Hs & Eu & En).
          destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
          destruct (carved_range bt st Lc FF W _ _ ltac:(apply (prim_user_in_chunk n' ltac:(lia) HP')) CV') as (C1 & C2 & C3 & C4 & _).
          pose proof (rz_range n'). pose proof (csize_pos (class_of (needed n')) ltac:(apply (prim_user_in_chunk n' ltac:(lia) HP'))) as ((CS1 & _) & _).
          destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); unfold prim_alloc_beg, blk_class in *; ulia.
      - destruct RG' as (sc & Hs & Eu & En). replace (p - 16 + 16) with p in Eu by lia.
        destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        destruct (is_primary n) eqn:HP.
        + pose proof (prim_block_in_space bt st Lc FF p n W Hin HP) as [B1 B2]. pose proof (rz_range n).
          destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
        + destruct (live_sec bt st Lc FF W p n Hin HP) as (sc2 & Hs2 & Eu2 & En2).
          destruct (sec_facts bt st Lc FF W sc2 Hs2) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
          destruct (sec_cases bt st Lc FF W sc sc2 Hs Hs2) as [<- | D]; [| ulia].
          apply (sec_live_not_quar bt st Lc FF W sc Hs); [rewrite Eu, En2; exact Hin | rewrite Eu, En; exact HQ'].
  Qed.


  Lemma op_quar_newbatch_eq : forall st k ks m n, a_cache st BATCHCLASS = ks ++ [k] ->
    op_quar_newbatch (op_cache_pop st BATCHCLASS) (chunk_of_compact SBEG BATCHCLASS k) m n
    = set_tq (set_cache st BATCHCLASS ks) (a_tq st ++ [BATCH (chunk_of_compact SBEG BATCHCLASS k) [(m, n)]]).
  Proof using. intros st k ks m n E. (lazymatch goal with |- ?G => let G' := eval unfold op_quar_newbatch, op_cache_pop in G in change_no_check G' end). rewrite E, removelast_last. reflexivity. Qed.

  Lemma quar_newbatch_split : forall st ks ba m n,
    quar (set_tq (set_cache st BATCHCLASS ks) (a_tq st ++ [BATCH ba [(m, n)]])) = flat_map ba_items (a_tq st) ++ (m, n) :: flat_map ba_items (a_gq st).
  Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_tq set_cache] in G in change_no_check G' end). rewrite !flat_map_app. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite <- app_assoc. reflexivity. Qed.

  Lemma quar_old_split : forall st, quar st = flat_map ba_items (a_tq st) ++ flat_map ba_items (a_gq st).
  Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). rewrite flat_map_app. reflexivity. Qed.

  Lemma quar_newbatch_in : forall st ks ba m n x,
    In x (quar (set_tq (set_cache st BATCHCLASS ks) (a_tq st ++ [BATCH ba [(m, n)]]))) <-> x = (m, n) \/ In x (quar st).
  Proof using.
    intros. rewrite quar_newbatch_split, quar_old_split, !in_app_iff. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). split; intros H; decompose [or] H; clear H; subst; auto 10.
  Qed.

  (* [comment removed for export] *)
  Theorem OPS_WFq_quar_newbatch2_pf : forall st Lc FF L1 L2 p n k ks (qt qg : Z),
    WFq bt st Lc FF qt qg -> Lc = L1 ++ (p, n) :: L2 ->
    a_cache st BATCHCLASS = ks ++ [k] ->
    WFq bt (op_quar_newbatch (op_cache_pop st BATCHCLASS) (chunk_of_compact SBEG BATCHCLASS k) (p - 16) n) (L1 ++ L2) FF (q_bytes (a_tq st) + n + BATCHSZ) qg.
  Proof using.
    intros st Lc FF L1 L2 p n k ks qt qg W HL HC.
    rewrite (op_quar_newbatch_eq st k ks (p - 16) n HC).
    set (ba := chunk_of_compact SBEG BATCHCLASS k). set (nb := BATCH ba [(p - 16, n)]). set (st' := set_tq (set_cache st BATCHCLASS ks) (a_tq st ++ [nb])).
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM & WMP & G).
    assert (Hin : In (p, n) Lc) by (rewrite HL; apply in_app_iff; right; left; reflexivity).
    destruct (LV1 p n Hin) as (N1 & P16 & ABL & CVL).
    assert (NDL : List.NoDup (L1 ++ (p, n) :: L2)) by (rewrite <- HL; exact LV2).
    assert (INL : forall x, In x (L1 ++ L2) <-> In x Lc /\ x <> (p, n)) by (intros x; rewrite HL; apply in_remove_mid; exact NDL).
    assert (INQ : forall x, In x (quar st') <-> x = (p - 16, n) \/ In x (quar st)) by (intros x; (lazymatch goal with |- ?G => let G' := eval unfold st', nb in G in change_no_check G' end); apply quar_newbatch_in).
    pose proof (live_not_quar st Lc FF p n W Hin) as NQP.
    assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    destruct (WC BATCHCLASS HC24) as (C1 & C2 & C3).
    assert (HkIn : In k (a_cache st BATCHCLASS)) by (rewrite HC; apply in_app_iff; right; left; reflexivity).
    destruct (C3 k HkIn) as [Kr CVba]. fold ba in CVba.
    assert (INCba : in_cache_c bt st BATCHCLASS ba) by (exists k; split; [exact HkIn | reflexivity]).
    assert (HBt : forall a, in_batch st' a <-> in_batch st a \/ a = ba).
    { intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_batch, st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_tq set_cache] in G in change_no_check G' end). rewrite <- app_assoc. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). split.
      - intros (b0 & Hb0 & E0). apply in_app_iff in Hb0. destruct Hb0 as [Hb0 | [<- | Hb0]]; [left; exists b0; split; [apply in_app_iff; left; exact Hb0 | exact E0] | right; symmetry; exact E0 | left; exists b0; split; [apply in_app_iff; right; exact Hb0 | exact E0]].
      - intros [(b0 & Hb0 & E0) | ->]; [| exists nb; split; [apply in_app_iff; right; left; reflexivity | reflexivity]].
        apply in_app_iff in Hb0. destruct Hb0 as [Hb0|Hb0]; exists b0; split; [apply in_app_iff; left; exact Hb0 | exact E0 | apply in_app_iff; right; right; exact Hb0 | exact E0]. }
    assert (CACHE24 : a_cache st' BATCHCLASS = ks) by ((lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_tq set_cache] in G in change_no_check G' end); apply fupdZ_same).
    assert (CACHEo : forall c, c <> BATCHCLASS -> a_cache st' c = a_cache st c) by (intros c NE; (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_tq set_cache] in G in change_no_check G' end); apply fupdZ_other; exact NE).
    (* [comment removed for export] *)
    assert (NBA : ~ In ba (map ba_addr (a_tq st ++ a_gq st))).
    { intros X. apply in_map_iff in X. destruct X as (b0 & E0 & Hb0).
      destruct (WR1 BATCHCLASS HC24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK). destruct PART as (_ & _ & _ & _ & _ & _ & _ & NB & _).
      apply (NB ba ltac:(exists b0; split; [exact Hb0 | exact E0]) eq_refl). right. right. left. exact INCba. }
    assert (G' : (bt_spacebeg bt mod 2 ^ 16 = 0 /\ Z.of_nat (length (L1 ++ L2)) <= LMAX /\ PHI (L1 ++ L2) <= GBUDGET) /\ bt_ok bt /\ dep0_ok bt).   (* [comment removed for export] *)
    { destruct G as ((GA & GC & GB) & GOK). rewrite HL in GC, GB. rewrite length_app in GC. cbn [length] in GC. rewrite PHI_app in GB. cbn [PHI snd] in GB. rewrite length_app, PHI_app.
      split; [split; [exact GA | split; [lia | clear -GB N1; unfold MBLK in *; lia]] | exact GOK]. }
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end). split; [| split; [| split; [| split; [| split; [| split; [exact WK | split; [exact WD | split; [exact WM | split; [exact WMP | exact G']]]]]]]]].
    - (* [comment removed for export] *) split; [| intros c NC; destruct (WR2 c NC) as [E1 E2]; split; [exact E1 | rewrite (CACHEo c ltac:(unfold BATCHCLASS in *; lia)); exact E2]].
      intros c Hc. destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). change (a_reg st' c) with (a_reg st c). repeat (split; [assumption|]). split; [| exact FHK].
      destruct (Z.eq_dec c BATCHCLASS) as [-> | NC].
      + (* [comment removed for export] *)
        destruct (is_primary n) eqn:HP.
        * pose proof (live_chunk bt st Lc FF W p n Hin HP) as Gv. cbn zeta in Gv. destruct Gv as (G1 & G2 & G3 & G4 & G5 & G6).
          destruct (Z.eq_dec (blk_class n) BATCHCLASS) as [EC | NEC].
          -- apply (partition_c24 st st' Lc (L1 ++ L2) (Some (prim_alloc_beg p n)) ba k ks); [| | | exact HBt | exact HC | exact CACHE24 | reflexivity | reflexivity | exact PART].
             ++ intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
                ** intros (p' & n' & Hin' & HP' & HC' & HA'). apply INL in Hin'. destruct Hin' as [Hin' NE'].
                   split; [exists p', n'; repeat split; assumption|]. intros E. injection E as <-.
                   destruct (live_range bt st Lc FF W p' n' Hin') as (L1' & _ & L3' & _).
                   pose proof (rz_unif n n' ltac:(lia) ltac:(lia) HP HP' ltac:(rewrite EC, HC'; reflexivity)) as ER.
                   assert (p' = p) by (unfold prim_alloc_beg in HA'; clear -HA' ER; lia). subst p'.
                   destruct (Z.eq_dec n' n) as [-> | NE2]; [exact (NE' eq_refl)|].
                   destruct (LV3 p n' p n Hin' Hin ltac:(clear -NE2; congruence)); clear -H N1 L3'; lia.
                ** intros [(p' & n' & Hin' & X) NE']. exists p', n'. split; [| exact X]. apply INL. split; [exact Hin'|].
                   intros E. injection E as -> ->. apply NE'. destruct X as (_ & _ & X). rewrite X. reflexivity.
             ++ intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). split.
                ** intros (m & n' & Hq & X). apply INQ in Hq. destruct Hq as [E | Hq]; [| left; exists m, n'; split; assumption].
                   injection E as -> ->. right. destruct X as (_ & _ & X). rewrite <- X. (lazymatch goal with |- ?G => let G' := eval unfold prim_alloc_beg in G in change_no_check G' end). do 2 f_equal. lia.
                ** intros [(m & n' & Hq & X) | E].
                   { exists m, n'. split; [apply INQ; right; exact Hq | exact X]. }
                   { injection E as <-. exists (p - 16), n. split; [apply INQ; left; reflexivity|]. replace (p - 16 + 16) with p by lia. split; [exact HP | split; [exact EC | reflexivity]]. }
             ++ intros ab E. injection E as <-. rewrite <- EC. exact G3.
          -- apply (partition_c24 st st' Lc (L1 ++ L2) None ba k ks); [| | intros ab E; discriminate E | exact HBt | exact HC | exact CACHE24 | reflexivity | reflexivity | exact PART].
             ++ intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
                ** intros (p' & n' & Hin' & X). apply INL in Hin'. split; [exists p', n'; split; [exact (proj1 Hin') | exact X] | intros E; discriminate E].
                ** intros [(p' & n' & Hin' & X) _]. exists p', n'. split; [| exact X]. apply INL. split; [exact Hin'|].
                   intros E. injection E as -> ->. apply NEC. destruct X as (_ & X & _). exact X.
             ++ intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). split.
                ** intros (m & n' & Hq & X). apply INQ in Hq. destruct Hq as [E | Hq]; [| left; exists m, n'; split; assumption].
                   injection E as -> ->. exfalso. apply NEC. destruct X as (_ & X & _). exact X.
                ** intros [(m & n' & Hq & X) | E]; [| discriminate E]. exists m, n'. split; [apply INQ; right; exact Hq | exact X].
        * apply (partition_c24 st st' Lc (L1 ++ L2) None ba k ks); [| | intros ab E; discriminate E | exact HBt | exact HC | exact CACHE24 | reflexivity | reflexivity | exact PART].
          -- intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
             ++ intros (p' & n' & Hin' & X). apply INL in Hin'. split; [exists p', n'; split; [exact (proj1 Hin') | exact X] | intros E; discriminate E].
             ++ intros [(p' & n' & Hin' & X) _]. exists p', n'. split; [| exact X]. apply INL. split; [exact Hin'|].
                intros E. injection E as -> ->. destruct X as (X & _). rewrite HP in X. discriminate X.
          -- intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). split.
             ++ intros (m & n' & Hq & X). apply INQ in Hq. destruct Hq as [E | Hq]; [| left; exists m, n'; split; assumption].
                injection E as -> ->. destruct X as (X & _). rewrite HP in X. discriminate X.
             ++ intros [(m & n' & Hq & X) | E]; [| discriminate E]. exists m, n'. split; [apply INQ; right; exact Hq | exact X].
      + (* [comment removed for export] *)
        destruct (is_primary n) eqn:HP.
        * pose proof (live_chunk bt st Lc FF W p n Hin HP) as Gv. cbn zeta in Gv. destruct Gv as (G1 & G2 & G3 & G4 & G5 & G6).
          destruct (Z.eq_dec c (blk_class n)) as [-> | NE].
          -- apply (partition_mlq_nb st st' Lc (L1 ++ L2) (blk_class n) (prim_alloc_beg p n) ba); [| | exact HBt | exact NC | exact (CACHEo _ NC) | reflexivity | exact G3 | exact PART].
             ++ intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
                ** intros (p' & n' & Hin' & HP' & HC' & HA'). apply INL in Hin'. destruct Hin' as [Hin' NE'].
                   split; [exists p', n'; repeat split; assumption|]. intros ->.
                   destruct (live_range bt st Lc FF W p' n' Hin') as (L1' & _ & L3' & _).
                   pose proof (rz_unif n n' ltac:(lia) ltac:(lia) HP HP' (eq_sym HC')) as ER.
                   assert (p' = p) by (unfold prim_alloc_beg in HA'; clear -HA' ER; lia). subst p'.
                   destruct (Z.eq_dec n' n) as [-> | NE2]; [exact (NE' eq_refl)|].
                   destruct (LV3 p n' p n Hin' Hin ltac:(clear -NE2; congruence)); clear -H N1 L3'; lia.
                ** intros [(p' & n' & Hin' & X) NE']. exists p', n'. split; [| exact X]. apply INL. split; [exact Hin'|].
                   intros E. injection E as -> ->. apply NE'. destruct X as (_ & _ & X). symmetry. exact X.
             ++ intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). split.
                ** intros (m & n' & Hq & X). apply INQ in Hq. destruct Hq as [E | Hq]; [| left; exists m, n'; split; assumption].
                   injection E as -> ->. right. destruct X as (_ & _ & X). rewrite <- X. (lazymatch goal with |- ?G => let G' := eval unfold prim_alloc_beg in G in change_no_check G' end). f_equal. lia.
                ** intros [(m & n' & Hq & X) | ->].
                   { exists m, n'. split; [apply INQ; right; exact Hq | exact X]. }
                   { exists (p - 16), n. split; [apply INQ; left; reflexivity|]. replace (p - 16 + 16) with p by lia. split; [exact HP | split; reflexivity]. }
          -- apply (partition_ext_nb st st' Lc (L1 ++ L2) c ba); [| | exact HBt | exact NC | exact (CACHEo _ NC) | reflexivity | exact PART].
             ++ intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
                ** intros (p' & n' & Hin' & X). apply INL in Hin'. exists p', n'. split; [exact (proj1 Hin') | exact X].
                ** intros (p' & n' & Hin' & X). exists p', n'. split; [| exact X]. apply INL. split; [exact Hin'|].
                   intros E. injection E as -> ->. apply NE. destruct X as (_ & X & _). symmetry. exact X.
             ++ intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). split.
                ** intros (m & n' & Hq & X). apply INQ in Hq. destruct Hq as [E | Hq]; [| exists m, n'; split; assumption].
                   injection E as -> ->. exfalso. apply NE. destruct X as (_ & X & _). symmetry. exact X.
                ** intros (m & n' & Hq & X). exists m, n'. split; [apply INQ; right; exact Hq | exact X].
        * apply (partition_ext_nb st st' Lc (L1 ++ L2) c ba); [| | exact HBt | exact NC | exact (CACHEo _ NC) | reflexivity | exact PART].
          -- intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
             ++ intros (p' & n' & Hin' & X). apply INL in Hin'. exists p', n'. split; [exact (proj1 Hin') | exact X].
             ++ intros (p' & n' & Hin' & X). exists p', n'. split; [| exact X]. apply INL. split; [exact Hin'|].
                intros E. injection E as -> ->. destruct X as (X & _). rewrite HP in X. discriminate X.
          -- intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). split.
             ++ intros (m & n' & Hq & X). apply INQ in Hq. destruct Hq as [E | Hq]; [| exists m, n'; split; assumption].
                injection E as -> ->. destruct X as (X & _). rewrite HP in X. discriminate X.
             ++ intros (m & n' & Hq & X). exists m, n'. split; [apply INQ; right; exact Hq | exact X].
    - (* [comment removed for export] *) intros c Hc. destruct (WC c Hc) as (D1 & D2 & D3). destruct (Z.eq_dec c BATCHCLASS) as [-> | NC].
      + rewrite CACHE24. rewrite HC, length_app in D1. cbn [length] in D1. split; [lia|]. split; [intros F; pose proof (proj1 (D2 F)) as E0; rewrite HC in E0; destruct ks; discriminate E0|].
        intros k' Hk'. apply D3. rewrite HC. apply in_app_iff. left. exact Hk'.
      + rewrite (CACHEo c NC). exact (conj D1 (conj D2 D3)).
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine, wf_quarantine_q in G in change_no_check G' end). change (a_tq st') with (a_tq st ++ [nb]). change (a_gq st') with (a_gq st).
      assert (WBeq : forall b0, wf_batch bt st' b0 <-> wf_batch bt st b0) by (intros b0; (lazymatch goal with |- ?G => let G' := eval unfold wf_batch in G in change_no_check G' end); tauto).
      split. { rewrite Forall_app. split; [rewrite Forall_forall in Q1 |- *; intros b0 Hb0; apply WBeq; exact (Q1 b0 Hb0)|].
               constructor; [| constructor]. apply WBeq. (lazymatch goal with |- ?G => let G' := eval unfold wf_batch, nb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items ba_addr length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end).
               split; [(lazymatch goal with |- ?G => let G' := eval unfold BATCHCAP in G in change_no_check G' end); lia|]. split; [exact CVba|]. intros m n' [E | []]. injection E as <- <-. replace (p - 16 + 16) with p by lia. split; [lia|].
               destruct (is_primary n) eqn:HP; [left; split; [reflexivity | exact (CVL eq_refl)] | right; split; [reflexivity | exact (S7 p n Hin HP)]]. }
      split; [rewrite Forall_forall in Q2 |- *; intros b0 Hb0; apply (wf_batch0_mono bt st); [intros c0 a0 H0; exact H0 | intros p0 n0 H0; exact H0 | exact (Q2 b0 Hb0)]|].
      split. { rewrite q_bytes_app. (lazymatch goal with |- ?G => let G' := eval cbn [q_bytes fold_right] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold nb, ba_bytes in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items fold_right snd] in G in change_no_check G' end). lia. }
      split; [exact Q4|].
      split. { rewrite <- app_assoc. (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end). rewrite map_app. (lazymatch goal with |- ?G => let G' := eval cbn [map ba_addr] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold nb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr] in G in change_no_check G' end).
               apply NoDup_Add with (a := ba) (l := map ba_addr (a_tq st) ++ map ba_addr (a_gq st)); [apply Add_app|].
               rewrite <- map_app. split; [exact Q5 | exact NBA]. }
      (lazymatch goal with |- ?G => let G' := eval unfold st', nb in G in change_no_check G' end). rewrite quar_newbatch_split. rewrite quar_old_split in Q6.
      rewrite map_app. (lazymatch goal with |- ?G => let G' := eval cbn [map fst] in G in change_no_check G' end). apply NoDup_Add with (a := p - 16) (l := map fst (flat_map ba_items (a_tq st)) ++ map fst (flat_map ba_items (a_gq st))); [apply Add_app|].
      rewrite <- map_app. split; [exact Q6|].
      intros HIn. apply in_map_iff in HIn. destruct HIn as ([m n'] & E & HIn). cbn in E. subst m.
      apply (NQP n'). rewrite quar_old_split. exact HIn.
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). change (a_sec st') with (a_sec st). change (a_nres st') with (a_nres st). repeat (split; [assumption|]).
      split. { intros s0 Hs. rewrite (INL (sc_user s0, sc_n s0)), (INQ (sc_user s0 - 16, sc_n s0)). split.
               - intros [X NE] [E | Y]; [| exact (proj1 (S6 s0 Hs) X Y)]. apply NE. injection E as E1 E2. f_equal; lia.
               - intros X. destruct (S4 s0 Hs) as (N64 & _).
                 assert (DEC : (sc_user s0, sc_n s0) = (p, n) \/ (sc_user s0, sc_n s0) <> (p, n)).
                 { destruct (Z.eq_dec (sc_user s0) p) as [E1|NE1]; [destruct (Z.eq_dec (sc_n s0) n) as [E2|NE2]; [left; rewrite E1, E2; reflexivity | right; congruence] | right; congruence]. }
                 destruct DEC as [E | NE].
                 + exfalso. apply X. left. injection E as E1 E2. rewrite E1, E2. reflexivity.
                 + split; [| exact NE]. apply (S6 s0 Hs). intros Y. apply X. right. exact Y. }
      split. { intros p' n' Hin' HP'. apply INL in Hin'. exact (S7 p' n' (proj1 Hin') HP'). }
      intros m n' Hq HP'. apply INQ in Hq. destruct Hq as [E | Hq]; [| exact (S8 m n' Hq HP')]. injection E as -> ->. replace (p - 16 + 16) with p by lia. exact (S7 p n Hin HP').
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split; [intros p' n' Hin'; apply INL in Hin'; exact (LV1 p' n' (proj1 Hin'))|].
      split; [exact (NoDup_remove_1 _ _ _ NDL)|].
      intros p1 n1 p2 n2 H1 H2 NE. apply INL in H1. apply INL in H2. exact (LV3 p1 n1 p2 n2 (proj1 H1) (proj1 H2) NE).
  Qed.


End Q.
End AsAinvOpsQ3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 AsAinvOpsQ3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

Section Q2.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Ztac := try ceil; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Definition OPS_REP_quar_newbatch2x : Prop := forall st Lc FF L1 L2 (M M' : mem) mdl mdl' p n k ks,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> Lc = L1 ++ (p, n) :: L2 ->
    a_cache st BATCHCLASS = ks ++ [k] ->
    let ba := chunk_of_compact SBEG BATCHCLASS k in
    agrees_off (foot_quar_newbatch T p n ba (a_tq st)) M M' ->
    byteZ SG M' (p - 16) 3 ->
    (forall g, user_granule p n g -> byteZ SG M' (SB + g) 0xfd) ->
    cellZ SG M' ba 8 0 -> cellZ SG M' (ba + 8) 8 (BATCHSZ + n) -> cellZ SG M' (ba + 16) 8 1 -> cellZ SG M' (ba + 24) 8 (p - 16) ->
    cellZ SG M' (T + T_QC) 8 (Z.of_nat (length (a_tq st)) + 1) ->
    (a_tq st = [] -> cellZ SG M' (T + T_QC + 8) 8 ba) ->
    (forall b0 q0, a_tq st = b0 :: q0 -> cellZ SG M' (T + T_QC + 8) 8 (ba_addr b0)) ->
    cellZ SG M' (T + T_QC + 16) 8 ba ->
    cellZ SG M' (T + T_QC + 24) 8 (q_bytes (a_tq st) + (n + BATCHSZ)) ->
    (forall tq' b, a_tq st = tq' ++ [b] -> cellZ SG M' (ba_addr b) 8 ba) ->
    cellZ SG M' (T + T_PC + PC_SZ * BATCHCLASS) 4 (Z.of_nat (length ks)) ->
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    Rep bt (op_quar_newbatch (op_cache_pop st BATCHCLASS) ba (p - 16) n) (L1 ++ L2) FF M' mdl'.

  Theorem OPS_REP_quar_newbatch2x_pf : OPS_REP_quar_newbatch2x.
  Proof using.
    intros st Lc FF L1 L2 M M' mdl mdl' p n k ks W R HL HC. cbn zeta.
    intros AGR ST3 SHFD CB0 CB8 CB16 CB24 CL0 CL8e CL8n CL16 CL24 CNX CCNT SBM MI.
    rewrite (op_quar_newbatch_eq bt st k ks (p - 16) n HC).
    set (ba := chunk_of_compact SBEG BATCHCLASS k) in *. set (nb := BATCH ba [(p - 16, n)]). set (st' := set_tq (set_cache st BATCHCLASS ks) (a_tq st ++ [nb])).
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & (WQ1 & WQ2 & WQ3 & WQ4 & WQ5 & WQ6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by lia.
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((TD1 & TD2 & TD3 & _ & TD5) & _). box TD5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    assert (Hin : In (p, n) Lc) by (rewrite HL; apply in_app_iff; right; left; reflexivity).
    destruct (live_range bt st Lc FF W p n Hin) as (PL1 & PL2 & PL3 & PL4). pose proof (rz_range n) as RZ. pose proof (rounded_ge n) as (RG1 & RG2 & RG3 & RG4).
    try ceil; unfold AS_HEAPLO, PTRLO, NMAX in PL1, PL2, PL3.
    assert (NDL : List.NoDup (L1 ++ (p, n) :: L2)) by (rewrite <- HL; exact LV2).
    assert (INL : forall x, In x (L1 ++ L2) <-> In x Lc /\ x <> (p, n)) by (intros x; rewrite HL; apply in_remove_mid; exact NDL).
    assert (INQ : forall x, In x (quar st') <-> x = (p - 16, n) \/ In x (quar st)) by (intros x; (lazymatch goal with |- ?G => let G' := eval unfold st', nb in G in change_no_check G' end); apply quar_newbatch_in).
    assert (QE : quar st' = flat_map ba_items (a_tq st) ++ (p - 16, n) :: flat_map ba_items (a_gq st)) by ((lazymatch goal with |- ?G => let G' := eval unfold st', nb in G in change_no_check G' end); apply quar_newbatch_split).
    pose proof (quar_old_split st) as QE0.
    assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    destruct (WC BATCHCLASS HC24) as (WC1 & WC2 & WC3).
    assert (HkIn : In k (a_cache st BATCHCLASS)) by (rewrite HC; apply in_app_iff; right; left; reflexivity).
    destruct (WC3 k HkIn) as [Kr CVB]. fold ba in CVB.
    assert (INCba : in_cache_c bt st BATCHCLASS ba) by (exists k; split; [exact HkIn | reflexivity]).
    assert (Eba : ba = chunk_of_compact SBEG BATCHCLASS k) by reflexivity. clearbody ba.
    destruct (carved_range bt st Lc FF W BATCHCLASS ba HC24 CVB) as (BA1 & BA2 & BB1 & BB2 & BA5). change (csize BATCHCLASS) with 8192 in BA2, BB2. unfold KSPACE in BB2.
    pose proof (agrees_DEFK _ _ _ AGR) as DEF. pose proof (agrees_at' _ _ _ AGR) as AGF.
    (* [comment removed for export] *)
    destruct (WR1 BATCHCLASS HC24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _). pose proof PARTB as (_ & _ & NLC & _ & NQC & _ & _ & NBL & _).
    assert (NBA : forall b0, In b0 (a_tq st ++ a_gq st) -> ba_addr b0 <> ba).
    { intros b0 Hb0 E0. apply (NBL ba ltac:(exists b0; split; [exact Hb0 | exact E0]) eq_refl). right. right. left. exact INCba. }
    (* [comment removed for export] *)
    set (ZL := fun i => exists tq' bl, a_tq st = tq' ++ [bl] /\ ba_addr bl <= i < ba_addr bl + 8).
    assert (ZLfacts : forall i, ZL i -> exists bl, In bl (a_tq st ++ a_gq st) /\ In bl (a_tq st) /\ carved bt st BATCHCLASS (ba_addr bl)
                        /\ SBEG <= ba_addr bl /\ ba_addr bl + BATCHSZ <= SBEG + KSPACE /\ ba_addr bl <= i < ba_addr bl + 8 /\ (forall tq' bl', a_tq st = tq' ++ [bl'] -> bl' = bl)).
    { intros i (tq2 & bl & Etq & Hi2). assert (Hbl : In bl (a_tq st)) by (rewrite Etq; apply in_app_iff; right; left; reflexivity).
      assert (Hbl2 : In bl (a_tq st ++ a_gq st)) by (apply in_app_iff; left; exact Hbl).
      destruct (batch_facts bt st Lc FF W bl Hbl2) as (CVl & _ & Bl1 & Bl2). exists bl. repeat (split; [assumption|]).
      intros tq3 bl3 E3. rewrite Etq in E3. apply app_inj_tail in E3. symmetry. exact (proj2 E3). }
    (* [comment removed for export] *)
    assert (LOC : (is_primary n = true /\ SBEG <= p - rz n /\ p + n <= p - rz n + csize (blk_class n) /\ p - rz n + csize (blk_class n) <= SBEG + KSPACE
                     /\ carved bt st (blk_class n) (p - rz n) /\ 1 <= blk_class n <= 30 /\ in_live_c Lc (blk_class n) (p - rz n) /\ rz n + rounded n <= csize (blk_class n))
                  \/ (is_primary n = false /\ exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n
                                               /\ sc_map sc + PG + 16 <= p /\ p + n <= sc_map sc + sc_mapsz sc /\ 0 < sc_map sc /\ sc_map sc + sc_mapsz sc <= CEIL
                                               /\ p + 8 <= sc_map sc + sc_mapsz sc)).
    { destruct (is_primary n) eqn:HP.
      - left. pose proof (live_chunk bt st Lc FF W p n Hin HP) as Gv. cbn zeta in Gv. destruct Gv as (G1 & G2 & G3 & G4 & G5 & G6). unfold prim_alloc_beg in *.
        destruct (carved_range bt st Lc FF W _ _ G1 G2) as (D1 & D2 & D3 & D4 & D5).
        pose proof (csize_class_of (needed n)) as CC. unfold blk_class in *.
        assert (NB : 1 <= needed n <= 65536) by (pose proof HP as HP2; unfold is_primary in HP2; apply Z.leb_le in HP2; unfold needed in *; lia).
        specialize (CC NB). assert (EN : needed n = rounded n + rz n) by reflexivity. repeat split; try assumption; lia.
      - right. split; [reflexivity|]. destruct (live_sec bt st Lc FF W p n Hin HP) as (sc & Hs & Eu & En). exists sc.
        destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). rewrite Eu, En in *.
        unfold sc_mapsz in *. pose proof (sec_map_size_ge n ltac:(lia)) as [SG1 SG2]. unfold PG in *. repeat split; try assumption; try lia. }
    (* [comment removed for export] *)
    assert (FZ : forall i, foot_quar_newbatch T p n ba (a_tq st) i ->
              (i = p - 16 \/ p <= i < p + 8) \/ (ba <= i < ba + BATCHSZ) \/ (T <= i < T + PG) \/ (SB <= i < AS_HEAPLO) \/ CEIL <= i \/ ZL i).
    { intros i Hf. unfold foot_quar_newbatch, T_QC, T_PC, PC_SZ, BATCHCLASS, sh_lo, sh_hi in Hf.
      destruct Hf as [Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]]]; try (clear -Z PL1 PL2; Zlia).
      destruct (rev (a_tq st)) as [|bl rl] eqn:ER; [destruct Z|]. do 5 right. exists (rev rl), bl. split; [| exact Z].
      rewrite <- (rev_involutive (a_tq st)), ER. (lazymatch goal with |- ?G => let G' := eval cbn [rev] in G in change_no_check G' end). reflexivity. }
    assert (BLKZ : forall i, (i = p - 16 \/ p <= i < p + 8) ->
             (0 <= i < CEIL /\ ~ (ia_img_lo IA <= i < ia_img_hi IA) /\ ~ in_band i) /\
             ((is_primary n = true /\ p - rz n <= i < p - rz n + csize (blk_class n)) \/
              (is_primary n = false /\ exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n /\ sc_map sc + PG <= i < sc_map sc + sc_mapsz sc))).
    { intros i Hi. destruct LOC as [(HP & Z1 & Z2 & Z3 & CV & HC' & LIV & RR) | (HP & sc & Hs & Eu & En & Z1 & Z2 & Z3 & Z4 & Z5)].
      - split; [clear -Hi Z1 Z2 Z3 RZ RR RG1 RG2 RG3 RG4 SBH I2 X15; (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); Zlia|]. left. split; [exact HP|]. lia.
      - split; [| right; split; [exact HP|]; exists sc; repeat split; try assumption; ulia].
        destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((D1 & D1' & D3 & D4 & D5) & _).
        clear -Hi Z1 Z2 Z3 Z4 Z5 D1 D1' D3 D4 D5 RZ. (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end). Zlia. }
    assert (AGZ : forall i, 0 <= i -> i < CEIL -> ~ (i = p - 16 \/ p <= i < p + 8) -> ~ (ba <= i < ba + BATCHSZ) ->
                  ~ (T <= i < T + PG) -> ~ (SB <= i < AS_HEAPLO) -> ~ ZL i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi0 Hi1 N1 N2 N3 N4 N5. apply AGF; [| ulia]. intros Hf. destruct (FZ i Hf) as [Z|[Z|[Z|[Z|[Z|Z]]]]]; try am_tauto. ulia. }
    (* [comment removed for export] *)
    assert (ZLspace : forall i, ZL i -> SBEG <= i < SBEG + KSPACE) by (intros i Zi; destruct (ZLfacts i Zi) as (bl & _ & _ & _ & Bl1 & Bl2 & Hi2 & _); unfold BATCHSZ in Bl2; lia).
    assert (IMGfree : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply AGZ; [ulia | ulia | | | | ulia |].
      - intros Hbk. destruct (BLKZ i Hbk) as [(_ & NI & _) _]. exact (NI Hi).
      - intros X. destruct (dyn_kind_facts bt st Lc FF W i (dyn_kind_space bt st Lc FF W i ltac:(ulia))) as (_ & _ & NH & _). exact (NH Hi).
      - intros X. destruct (dyn_kind_facts bt st Lc FF W i (dyn_kind_fixed bt st _ _ i INT X)) as (_ & _ & NH & _). exact (NH Hi).
      - intros Zi. pose proof (ZLspace i Zi). destruct (dyn_kind_facts bt st Lc FF W i (dyn_kind_space bt st Lc FF W i ltac:(ulia))) as (_ & _ & NH & _). exact (NH Hi). }
    assert (IMGK : forall i, img_kind bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i [Hi _] _. exact (IMGfree i Hi). }
    assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
    (* [comment removed for export] *)
    assert (CH24vsFA : forall a c0 i, carved bt st BATCHCLASS a -> 1 <= c0 <= 30 -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + 2 ^ 29 -> ~ (a <= i < a + 8192)).
    { intros a c0 i CVa Hc0 Hi Hin2. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & _).
      destruct (carved_range bt st Lc FF W BATCHCLASS a HC24 CVa) as (D1 & D2 & _). change (csize BATCHCLASS) with 8192 in D2.
      pose proof (region_facts bt st Lc FF W BATCHCLASS HC24) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c0 BATCHCLASS) as [LT|[->|GT]]; [| ulia |].
      * assert (c0 * 2 ^ 32 + 2 ^ 32 <= BATCHCLASS * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; unfold BATCHCLASS in *; lia). ulia.
      * assert (BATCHCLASS * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (BATCHCLASS * 2 ^ 32 + 2 ^ 32) with ((BATCHCLASS + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; unfold BATCHCLASS in *; lia). ulia. }
    (* [comment removed for export] *)
    assert (FIXfree : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> PG -> hi - lo < KSPACE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo Hlen Hlen2 i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hlo) (all_ranges_fixed bt st _ INT) ltac:(intros E; injection E; intros; ulia)) as D. hnf in D. cbn in D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hlo Hlen2) as [SP|SP]; apply AGZ; try (first [clear - Hr A3 Hi SP BB1 D A5 BB2 | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [(first [clear - Hbk SP Hi Z1 RZ | idtac]; ulia) | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hlo (sec_dyn st sc Hs)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia).
      - intros Zi. pose proof (ZLspace i Zi). ulia.
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [(first [clear - Hbk SP Hi Z3 Z2 PL3 | idtac]; ulia) | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hlo (sec_dyn st sc Hs)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia).
      - intros Zi. pose proof (ZLspace i Zi). ulia. }
    (* [comment removed for export] *)
    assert (FIXfreeT : forall lo hi, In (lo, hi) (bt_fixed bt) -> (hi <= T \/ T + PG <= lo) -> hi - lo < KSPACE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo Hlen Hlen2 i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof Hlen as D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hlo Hlen2) as [SP|SP]; apply AGZ; try (first [clear - Hr A3 Hi SP BB1 Hlen A5 BB2 | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [(first [clear - Hbk SP Hi Z1 RZ | idtac]; ulia) | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hlo (sec_dyn st sc Hs)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia).
      - intros Zi. pose proof (ZLspace i Zi). ulia.
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [(first [clear - Hbk SP Hi Z3 Z2 PL3 | idtac]; ulia) | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hlo (sec_dyn st sc Hs)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia).
      - intros Zi. pose proof (ZLspace i Zi). ulia. }
    (* [comment removed for export] *)
    assert (DYNfree : forall lo hi, In (lo, hi) (dyn_ranges st) ->
               (forall sc, In sc (a_sec st) -> sc_user sc = p -> sc_n sc = n -> (lo, hi) <> (sc_map sc, sc_map sc + sc_mapsz sc)) ->
               forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo NSELF i Hi Hr. destruct (RNG _ _ (all_ranges_dyn bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT Hlo) as D. hnf in D. cbn in D.
      destruct (space_vs_dyn bt st Lc FF W lo hi Hlo) as [SP|SP]; apply AGZ; try (first [clear - Hr A3 Hi SP BB1 D A5 BB2 | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [ulia | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_dyn bt st _ Hlo) (all_ranges_dyn bt st _ (sec_dyn st sc Hs)) (NSELF sc Hs Eu En)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia).
      - intros Zi. pose proof (ZLspace i Zi). ulia.
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [ulia | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_dyn bt st _ Hlo) (all_ranges_dyn bt st _ (sec_dyn st sc Hs)) (NSELF sc Hs Eu En)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia).
      - intros Zi. pose proof (ZLspace i Zi). ulia. }
    (* [comment removed for export] *)
    assert (CHKfree : forall c' a', 1 <= c' <= 30 -> carved bt st c' a' ->
               ~ (is_primary n = true /\ c' = blk_class n /\ a' = p - rz n) -> ~ (c' = BATCHCLASS /\ a' = ba) ->
               forall i, a' <= i < a' + csize c' ->
               (forall tq' bl, a_tq st = tq' ++ [bl] -> c' = BATCHCLASS -> a' = ba_addr bl -> ba_addr bl + 8 <= i) ->
               M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c' a' Hc' CV' NE NB i Hi ZOK. destruct (carved_range bt st Lc FF W c' a' Hc' CV') as (D1 & D2 & D3 & D4 & D5).
      apply AGZ; try (first [clear - D3 Hi X14 D4 X15 TPG SPH R6a | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]].
        + destruct LOC as [(_ & Z1 & Z2 & Z3 & CV & HC' & _) | (HP' & _)]; [| rewrite HP in HP'; discriminate HP'].
          destruct (chunk_cases bt st Lc FF W c' a' (blk_class n) (p - rz n) Hc' HC' CV' CV) as [[EC EA] | D]; [apply NE; repeat split; assumption | (first [clear - D Zc Hi | idtac]; ulia)].
        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); (first [clear - H1 Zc D3 Hi D4 | idtac]; ulia).
      - intros HB2. destruct (chunk_cases bt st Lc FF W c' a' BATCHCLASS ba Hc' HC24 CV' CVB) as [[EC EA] | D]; [apply NB; split; assumption|].
        change (csize BATCHCLASS) with 8192 in D. ulia.
      - intros Zi. destruct (ZLfacts i Zi) as (bl & Hbl2 & Hbl & CVl & Bl1 & Bl2 & Hi2 & UQ). destruct Zi as (tq2 & bl2 & Etq & _). pose proof (UQ _ _ Etq) as ->.
        destruct (chunk_cases bt st Lc FF W c' a' BATCHCLASS (ba_addr bl) Hc' HC24 CV' CVl) as [[EC EA] | D].
        + pose proof (ZOK tq2 bl Etq EC EA). lia.
        + change (csize BATCHCLASS) with 8192 in D. lia. }
    assert (RIfree : forall i, SBEG + KSPACE <= i < SBEG + KSPACE + PG -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply AGZ; try ulia.
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]].
        + destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [ulia | rewrite HP in HP'; discriminate HP'].
        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
      - intros Zi. destruct (ZLfacts i Zi) as (bl & _ & _ & _ & Bl1 & Bl2 & Hi2 & _). unfold BATCHSZ in Bl2. ulia. }
    assert (FAfree : forall c0, 1 <= c0 <= 30 -> forall i, fa_beg SBEG c0 <= i < fa_beg SBEG c0 + 2 ^ 29 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c0 Hc0 i Hi. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & _).
      apply AGZ; [ulia | ulia | | intros X; exact (CH24vsFA ba c0 i CVB Hc0 Hi ltac:(unfold BATCHSZ in X; exact X)) | ulia | ulia |].
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]].
        + destruct LOC as [(_ & Z1 & Z2 & Z3 & CV & HC' & _) | (HP' & _)]; [| rewrite HP in HP'; discriminate HP'].
          destruct (carved_range bt st Lc FF W _ _ HC' CV) as (D1 & D2 & _). pose proof (region_facts bt st Lc FF W _ HC') as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
          unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
          destruct (Z.lt_trichotomy c0 (blk_class n)) as [LT|[->|GT]]; [| ulia |].
          * assert (c0 * 2 ^ 32 + 2 ^ 32 <= blk_class n * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). ulia.
          * assert (blk_class n * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (blk_class n * 2 ^ 32 + 2 ^ 32) with ((blk_class n + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). ulia.
        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
      - intros Zi. destruct (ZLfacts i Zi) as (bl & _ & _ & CVl & Bl1 & Bl2 & Hi2 & _). apply (CH24vsFA (ba_addr bl) c0 i CVl Hc0 Hi). lia. }
    (* [comment removed for export] *)
    assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> i <> p - 16 -> 0 <= i < 2 ^ 64 ->
               M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros p' n' i Hown Hf NI Hr. pose proof (rz_range n') as RZ'.
      (* [comment removed for export] *)
      assert (NOTB : forall tq' bl, a_tq st = tq' ++ [bl] -> is_primary n' = true -> blk_class n' = BATCHCLASS -> prim_alloc_beg p' n' = ba_addr bl -> False).
      { intros tq2 bl Etq HP' EC EA. assert (Hbl : In bl (a_tq st ++ a_gq st)) by (rewrite Etq; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
        apply (NBL (ba_addr bl) ltac:(exists bl; split; [exact Hbl | reflexivity]) eq_refl). rewrite <- EA, <- EC.
        destruct Hown as [HL' | HQ'].
        - left. pose proof (live_chunk bt st Lc FF W p' n' HL' HP') as G'. cbn zeta in G'. destruct G' as (_ & _ & G3 & _). exact G3.
        - right; left. pose proof (quar_chunk bt st Lc FF W (p' - 16) n' HQ' HP') as G'. cbn zeta in G'. replace (p' - 16 + 16) with p' in G' by lia. destruct G' as (_ & _ & G3 & _). exact G3. }
      destruct (hdr_zone bt st Lc FF W p' n' i Hown Hf) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')].
      - destruct LOC as [(HP & Y1 & Y2 & Y3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & Y1 & Y2 & Y3 & Y4 & Y5)].
        + destruct (chunk_cases bt st Lc FF W (blk_class n') (prim_alloc_beg p' n') (blk_class n) (p - rz n) HC' HCn CV' CV) as [[EC EA] | D].
          * pose proof (rz_unif n n' ltac:(lia) N1' HP HP' (eq_sym EC)) as ER. unfold prim_alloc_beg in EA.
            assert (p' = p) by (clear -EA ER; lia). subst p'.
            apply AGZ; try ulia.
            -- intros HB2. destruct (chunk_cases bt st Lc FF W BATCHCLASS ba (blk_class n) (p - rz n) HC24 HCn CVB CV) as [[EC2 EA2] | D3]; [| change (csize BATCHCLASS) with 8192 in D3; unfold prim_alloc_beg in *; ulia].
               exfalso. apply (NLC ba). split; [rewrite EC2, EA2; exact LIV | exact INCba].
            -- intros Zi. destruct (ZLfacts i Zi) as (bl & Hbl2 & Hbl & CVl & Bl1 & Bl2 & Hi2 & UQ). destruct Zi as (tq2 & bl2 & Etq & _). pose proof (UQ _ _ Etq) as ->.
               destruct (chunk_cases bt st Lc FF W BATCHCLASS (ba_addr bl) (blk_class n) (p - rz n) HC24 HCn CVl CV) as [[EC2 EA2] | D3]; [| change (csize BATCHCLASS) with 8192 in D3; unfold prim_alloc_beg in *; ulia].
               apply (NOTB tq2 bl Etq HP' (eq_trans EC (eq_sym EC2))). (lazymatch goal with |- ?G => let G' := eval unfold prim_alloc_beg in G in change_no_check G' end). rewrite EA2. clear -ER; lia.
          * apply (CHKfree (blk_class n') (prim_alloc_beg p' n') HC' CV'); [intros (_ & EC & EA); unfold prim_alloc_beg in *; lia | | lia |].
            -- intros [EC EA]. destruct Hown as [HL' | HQ'].
               ++ apply (NLC ba). split; [| exact INCba]. rewrite <- EA, <- EC.
                  pose proof (live_chunk bt st Lc FF W p' n' HL' HP') as G'. cbn zeta in G'. destruct G' as (_ & _ & G3 & _). exact G3.
               ++ apply (NQC ba). split; [| exact INCba]. rewrite <- EA, <- EC.
                  pose proof (quar_chunk bt st Lc FF W (p' - 16) n' HQ' HP') as G'. cbn zeta in G'. replace (p' - 16 + 16) with p' in G' by lia. destruct G' as (_ & _ & G3 & _). exact G3.
            -- intros tq2 bl Etq EC EA. exfalso. exact (NOTB tq2 bl Etq HP' EC EA).
        + apply (CHKfree (blk_class n') (prim_alloc_beg p' n') HC' CV'); [intros (HP2 & _); rewrite HP in HP2; discriminate HP2 | | lia |].
          -- intros [EC EA]. destruct Hown as [HL' | HQ'].
             ++ apply (NLC ba). split; [| exact INCba]. rewrite <- EA, <- EC.
                pose proof (live_chunk bt st Lc FF W p' n' HL' HP') as G'. cbn zeta in G'. destruct G' as (_ & _ & G3 & _). exact G3.
             ++ apply (NQC ba). split; [| exact INCba]. rewrite <- EA, <- EC.
                pose proof (quar_chunk bt st Lc FF W (p' - 16) n' HQ' HP') as G'. cbn zeta in G'. replace (p' - 16 + 16) with p' in G' by lia. destruct G' as (_ & _ & G3 & _). exact G3.
          -- intros tq2 bl Etq EC EA. exfalso. exact (NOTB tq2 bl Etq HP' EC EA).
      - destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        destruct LOC as [(HP & Y1 & Y2 & Y3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & Y1 & Y2 & Y3 & Y4 & Y5)].
        + apply (DYNfree _ _ (sec_dyn st sc' Hs')); [| ulia | exact Hr]. intros sc2 Hs2 Eu2 En2 E.
          pose proof (prim_block_in_space bt st Lc FF p n W Hin HP) as [B1 B2].
          destruct (sec_facts bt st Lc FF W sc2 Hs2) as (B1' & B2' & B3' & B4' & B5' & B6' & _). rewrite Eu2, En2 in *.
          destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc2 Hs2)); (first [clear - H1 B6' Y1 RZ PL3 B5' Y3 Y2 | idtac]; ulia).
        + destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D].
          * assert (p' = p) by congruence. subst p'.
            pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (sec_dyn st sc Hs)) as DT. hnf in DT. cbn in DT.
            destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((SD1 & SD1' & SD3 & SD4 & SD5) & _).
            destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [SP|SP]; destruct SD5; apply AGZ; try (first [clear - Hr Z1 Eu PL3 PL2 NI H2 Y2 BB1 SPH R6a DT SP Y1 X14 BB2 | idtac]; ulia); intros Zi; pose proof (ZLspace i Zi); (first [clear - H3 H2 Z1 Y2 Eu PL3 SPH R6a SP | idtac]; ulia).
          * apply (DYNfree _ _ (sec_dyn st sc' Hs')); [| ulia | exact Hr]. intros sc2 Hs2 Eu2 En2 E.
            destruct (sec_cases bt st Lc FF W sc sc2 Hs Hs2) as [<- | D2]; [injection E; intros; ulia|].
            destruct (sec_facts bt st Lc FF W sc2 Hs2) as (B1' & B2' & B3' & B4' & B5' & B6' & _). rewrite Eu2, En2 in *. (first [clear - B6' B5' D2 Y2 Y1 PL3 | idtac]; ulia). }
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & YC).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Y2, Y4, Y6, Y8, Y10, Y12, Y14, Y16.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact R1 | exact YC |]. intros c0 i Hc0 Hi. rewrite Forall_forall in YC. destruct (YC c0 Hc0).
             exact (IMGK i (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) ltac:(lia)). }
    (* [comment removed for export] *)
    split. { change (rep_instance bt st M'). eapply rep_instance_frame; [exact DEF | exact R2 | ulia | ulia | ulia | ulia | exact S1 |].
             intros i Hi Hr. destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
             - apply (FIXfree _ _ IN8); ulia.
             - exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact Hi | exact NI])) Hr). }
    (* [comment removed for export] *)
    split. { destruct R3 as (T1 & T2 & T3 & T4 & T5 & T6 & (TL1 & TL2 & TL3 & TL4) & TP & TW & TC1 & TC2 & TC3 & TC4). (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end).
             change (a_tq st') with (a_tq st ++ [nb]). change (a_cinit st') with (a_cinit st).
             assert (AGT : forall i, ((T <= i < T + T_QC \/ T + T_QC + 32 <= i < T + T_PC + PC_SZ * BATCHCLASS \/ T + T_PC + PC_SZ * BATCHCLASS + 4 <= i < T + 2768 \/ T + 3168 <= i < T + PG)
                                     \/ (bt_tctx bt <= i < bt_tctx bt + 160)) ->
                          0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros i Hi Hr. destruct Hi as [Hi | Hi].
               - apply AGF; [| exact Hr]. intros Hf. unfold foot_quar_newbatch, sh_lo, sh_hi in Hf. unfold T_QC, T_PC, PC_SZ, BATCHCLASS in *.
                 destruct Hf as [Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]]].
                 6: { revert Z. destruct (rev (a_tq st)) as [|bl rl] eqn:ER; intros Z; [destruct Z|].
                      assert (Hbl : In bl (a_tq st ++ a_gq st)) by (apply in_app_iff; left; apply in_rev; rewrite ER; left; reflexivity).
                      destruct (batch_facts bt st Lc FF W bl Hbl) as (_ & _ & Bl1 & Bl2). clear -Z Hi Bl1 Bl2 TPG X1 X2 X14 X15. Zlia. }
                 1-2: destruct (BLKZ i ltac:(am_tauto)) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]];
                      [ destruct LOC as [(_ & W1 & W2 & W3 & _) | (HP' & _)]; [clear -Zc Hi W1 W3 TPG X1 X2 RZ; (first [clear - Zc Hi TPG W3 W1 | idtac]; (first [clear - Zc Hi TPG W3 W1 | idtac]; Zlia)) | rewrite HP in HP'; discriminate HP']
                      | pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (sec_dyn st sc Hs)) as DT; hnf in DT; cbn in DT; clear -Zc Hi DT X1 X2; (first [clear - DT Zc Hi | idtac]; (first [clear - DT Zc Hi | idtac]; Zlia)) ].
                 all: clear -Z Hi X1 X2 TPG TD5 SBH PL1 PL2 BB1 BB2 X14 X15; (first [clear - Z Hi PL2 PL1 TD5 TPG BB2 BB1 X2 | idtac]; Zlia).
               - apply (FIXfree _ _ INC); ulia. }
             unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
             split; [frZ AGT T1|]. split; [frZ AGT T2|]. split; [frZ AGT T3|]. split; [frB AGT T4|]. split; [frZ AGT T5|]. split; [frB AGT T6|].
             split. { (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end). rewrite length_app. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). rewrite Nat2Z.inj_add. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end).
                      split; [exact CL0|].
                      split. { destruct (a_tq st) as [|b0 q0] eqn:ETQ; (lazymatch goal with |- ?G => let G' := eval cbn [app] in G in change_no_check G' end); [(lazymatch goal with |- ?G => let G' := eval unfold nb in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr] in G in change_no_check G' end); exact (CL8e eq_refl) | exact (CL8n b0 q0 eq_refl)]. }
                      split. { rewrite rev_app_distr. (lazymatch goal with |- ?G => let G' := eval cbn [rev app] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold nb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr] in G in change_no_check G' end). exact CL16. }
                      rewrite q_bytes_app. (lazymatch goal with |- ?G => let G' := eval cbn [q_bytes fold_right] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold nb, ba_bytes in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items fold_right snd] in G in change_no_check G' end).
                      replace (q_bytes (a_tq st) + (BATCHSZ + (n + 0) + 0)) with (q_bytes (a_tq st) + (n + BATCHSZ)) by lia. exact CL24. }
             split. { intros c' Hc'. destruct (Z.eq_dec c' BATCHCLASS) as [-> | NC].
                      - change (a_cache st' BATCHCLASS) with (fupdZ (a_cache st) BATCHCLASS ks BATCHCLASS). rewrite fupdZ_same.
                        destruct (TP BATCHCLASS Hc') as (P1 & P2 & P3 & P4). rewrite HC in P4. (lazymatch goal with |- ?G => let G' := eval unfold rep_pclass in G in change_no_check G' end). unfold T_PC, PC_SZ, BATCHCLASS in *.
                        pose proof (cache_len bt st Lc FF W 24 Hc') as CL'. rewrite HC, length_app in CL'. cbn [length] in CL'.
                        split; [exact CCNT|]. split; [frZ AGT P2|]. split; [frZ AGT P3|].
                        intros i k0 Hk0. pose proof (nth_error_lt _ _ _ Hk0) as Hl. pose proof (P4 i k0 ltac:(rewrite nth_error_app1 by exact Hl; exact Hk0)) as C. frZ AGT C.
                      - change (a_cache st' c') with (fupdZ (a_cache st) BATCHCLASS ks c'). rewrite (fupdZ_other _ _ _ _ _ NC).
                        pose proof (cache_len bt st Lc FF W c' Hc') as CL'.
                        eapply rep_pclass_frame; [exact (TP c' Hc') | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | exact CL' |].
                        unfold T_PC, PC_SZ, BATCHCLASS in *. intros i Hi Hr. apply AGT; [| exact Hr]. left. clear -Hi Hc' NC. lia. }
             split; [frW DEF TW|]. split; [frZ AGT TC1|]. split; [frZ AGT TC2|]. split; [frZ AGT TC3 | frZ AGT TC4]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. destruct (R4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
             change (a_reg st' c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | ulia | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. unfold foot_region in Hi. destruct Hi as [[Hi _] | Hi]; [apply RIfree; ulia | apply (FAfree c0 Hc0); ulia]. }
    (* [comment removed for export] *)
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). ulia. }
    (* [comment removed for export] *)
    assert (BA : forall b0 i, In b0 (a_tq st ++ a_gq st) -> foot_batch b0 i ->
                 (forall tq' bl, a_tq st = tq' ++ [bl] -> b0 = bl -> ba_addr bl + 8 <= i) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros b0 i Hb0 Hi ZOK Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b0 Hb0) as (CVb & BLb & BL2 & BL3).
      apply (CHKfree BATCHCLASS (ba_addr b0) HC24 CVb); [| | change (csize BATCHCLASS) with 8192; ulia |].
      - intros (HP & EC & EA). destruct LOC as [(_ & _ & _ & _ & _ & _ & LIV & _) | (HP' & _)]; [| rewrite HP in HP'; discriminate HP'].
        apply (NBL (ba_addr b0) ltac:(exists b0; split; [exact Hb0 | reflexivity]) eq_refl). left. rewrite EC, EA. exact LIV.
      - intros [_ EA]. exact (NBA b0 Hb0 EA).
      - intros tq2 bl Etq _ EA. apply (ZOK tq2 bl Etq). apply (NoDup_map_inj ba_addr (a_tq st ++ a_gq st) b0 bl WQ5 Hb0); [| exact EA].
        rewrite Etq. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity. }
    (* [comment removed for export] *)
    split. { change (a_tq st') with (a_tq st ++ [nb]). intros i b0 Hb0.
             destruct (Nat.lt_ge_cases i (length (a_tq st))) as [LT | GE].
             - rewrite nth_error_app1 in Hb0 by exact LT.
               assert (Hin0 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; left; exact (nth_error_In _ _ Hb0)).
               destruct (BR b0 Hin0) as (Q1 & Q2 & Q3). destruct (R5 i b0 Hb0) as (C1 & C2 & C3 & C4 & CW). unfold BATCHSZ, BATCHCAP in Q2, Q3.
               assert (AGb : forall j, ba_addr b0 + 8 <= j < ba_addr b0 + 24 + 8 * Z.of_nat (length (ba_items b0)) -> 0 <= j < 2 ^ 64 -> M' (Z_to_bv 64 j) = M (Z_to_bv 64 j)).
               { intros j Hj Hrj. apply (BA b0 j Hin0); [(lazymatch goal with |- ?G => let G' := eval unfold foot_batch in G in change_no_check G' end); lia | intros tq2 bl _ E; rewrite <- E; lia | exact Hrj]. }
               split. { destruct (Nat.eq_dec (S i) (length (a_tq st))) as [EL | NEL].
                        - (* [comment removed for export] *)
                          rewrite nth_error_app2, EL, Nat.sub_diag by lia. (lazymatch goal with |- ?G => let G' := eval cbn [nth_error] in G in change_no_check G' end). unfold nb at 1. (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr] in G in change_no_check G' end).
                          assert (Etq : a_tq st = firstn i (a_tq st) ++ [b0]).
                          { rewrite <- (firstn_skipn i (a_tq st)) at 1. f_equal.
                            destruct (skipn i (a_tq st)) as [|x r] eqn:ES.
                            + exfalso. pose proof (f_equal (@length batch) ES) as LL. rewrite length_skipn in LL. cbn in LL. lia.
                            + pose proof (f_equal (@length batch) ES) as LL. rewrite length_skipn in LL. cbn in LL.
                              assert (r = []) by (destruct r; [reflexivity | cbn in LL; lia]). subst r. f_equal.
                              pose proof (nth_error_skipn i (a_tq st) 0%nat) as NS. rewrite ES, Nat.add_0_r in NS. cbn in NS. congruence. }
                          exact (CNX _ _ Etq).
                        - rewrite nth_error_app1 by lia.
                          eapply (cellZ_frame _ _ _ _ _ _ C1); [lia | lia |]. intros j Hj. apply (BA b0 j Hin0); [(lazymatch goal with |- ?G => let G' := eval unfold foot_batch in G in change_no_check G' end); lia | | lia].
                          intros tq2 bl Etq Ebl. exfalso. subst b0. apply NEL.
                          pose proof (f_equal (@length batch) Etq) as LL. rewrite length_app in LL. cbn in LL.
                          assert (NDt : List.NoDup (a_tq st ++ a_gq st)).
                          { apply (NoDup_map_inv ba_addr). exact WQ5. }
                          rewrite Etq in Hb0.
                          destruct (Nat.lt_ge_cases i (length tq2)) as [LT2 | GE2].
                          + exfalso. rewrite nth_error_app1 in Hb0 by exact LT2. apply NoDup_app_remove_r in NDt. rewrite Etq in NDt.
                            apply (NoDup_remove_2 tq2 [] bl); [exact NDt | rewrite app_nil_r; exact (nth_error_In _ _ Hb0)].
                          + lia. }
               split; [frZ AGb C2|]. split; [frZ AGb C3|]. split; [| frW DEF CW].
               intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Hl. pose proof (C4 j mn Hj) as CC4. frZ AGb CC4.
             - (* [comment removed for export] *)
               rewrite nth_error_app2 in Hb0 by exact GE. destruct (i - length (a_tq st))%nat as [|kk] eqn:EK; [| destruct kk; discriminate Hb0]. cbn in Hb0. injection Hb0 as <-.
               assert (EI : i = length (a_tq st)) by lia. subst i.
               (lazymatch goal with |- ?G => let G' := eval unfold nb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr ba_items length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end).
               split. { rewrite nth_error_app2, Nat.sub_succ_l, Nat.sub_diag by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). exact CB0. }
               split; [(lazymatch goal with |- ?G => let G' := eval unfold ba_bytes in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ba_items fold_right snd] in G in change_no_check G' end); replace (BATCHSZ + (n + 0)) with (BATCHSZ + n) by lia; exact CB8|].
               split; [exact CB16|].
               split. { intros j mn Hj. destruct j as [|j']; [| destruct j'; discriminate Hj]. cbn in Hj. injection Hj as <-. (lazymatch goal with |- ?G => let G' := eval cbn [fst] in G in change_no_check G' end).
                        replace (ba + 24 + 8 * Z.of_nat 0) with (ba + 24) by lia. exact CB24. }
               destruct (R4 BATCHCLASS HC24) as [_ (_ & _ & F3)]. pose proof (region_facts bt st Lc FF W BATCHCLASS HC24) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3' & _).
               eapply writableZ_sub; [frW DEF F3 | lia | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia]. }
    (* [comment removed for export] *)
    split. { change (a_gq st') with (a_gq st). eapply rep_batches_frame; [exact DEF | exact R6 | intros b0 Hb0; apply BR; apply in_app_iff; right; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; right; exact Hb0 | exact Hi | | exact Hr].
             intros tq2 bl Etq ->. exfalso. rewrite Etq, map_app, map_app in WQ5. cbn [map] in WQ5. rewrite <- app_assoc in WQ5. cbn in WQ5.
             apply (NoDup_remove_2 _ _ _ WQ5). apply in_app_iff. right. apply in_map. exact Hb0. }
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply AGZ; try ulia.
               + intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc2 & Hs2 & Eu2 & En2 & Zc)]].
                 * destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [| rewrite HP in HP'; discriminate HP']. destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
                 * destruct (sec_cases bt st Lc FF W sc sc2 Hs Hs2) as [<- | D]; ulia.
               + intros HB2. destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
               + intros HT. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (sec_dyn st sc Hs)) as DT. hnf in DT. cbn in DT. ulia.
               + destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((SD1 & SD1' & SD3 & SD4 & SD5) & _). intros HB.
                 clear -Hi HB SD5 A1 A2 A3 A4 A5 A6 A7. Zlia.
               + intros Zi. pose proof (ZLspace i Zi). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia. }
    (* [comment removed for export] *)
    split. { change (quar st') with (quar st') . destruct R8 as [HLh HQh]. split.
             - intros p' n' Hin'. apply INL in Hin'. destruct Hin' as [Hin' NE'].
               destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n').
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | ulia | ulia |]. intros i Hi Hr. apply (HDRfree p' n' i (or_introl Hin') Hi); [| exact Hr].
               intros ->.
               destruct (hdr_zone bt st Lc FF W p' n' (p - 16) (or_introl Hin') Hi) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')].
               + destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                 * destruct (chunk_cases bt st Lc FF W (blk_class n') (prim_alloc_beg p' n') (blk_class n) (p - rz n) HC' HCn CV' CV) as [[EC EA] | D]; [| unfold prim_alloc_beg in *; ulia].
                   pose proof (rz_unif n n' ltac:(lia) N1' HP HP' (eq_sym EC)) as ER. unfold prim_alloc_beg in EA.
                   assert (p' = p) by (clear -EA ER; lia). subst p'. destruct (Z.eq_dec n' n) as [-> | NE2]; [exact (NE' eq_refl)|].
                   destruct (LV3 p n' p n Hin' Hin ltac:(clear -NE2; congruence)) as [OV|OV]; clear -OV N1' PL3; lia.
                 * pose proof (carved_range bt st Lc FF W _ _ HC' CV') as (D1 & D2 & D3 & D4 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); unfold prim_alloc_beg in *; ulia.
               + destruct (sec_facts bt st Lc FF W sc' Hs') as (B1 & B2 & B3 & B4 & B5 & B6 & _).
                 destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                 * destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc' Hs')); ulia.
                 * destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D]; [| ulia]. apply NE'. f_equal; congruence.
             - intros m n' Hq. apply INQ in Hq. destruct Hq as [E | Hq].
               + (* [comment removed for export] *)
                 injection E as -> ->. replace (p - 16 + 16) with p by lia. destruct (HLh p n Hin) as (H1 & (b1 & Hb1 & H2) & H3 & H4 & HW & H5 & HLC).
                 assert (AGh : forall i, (p - rz n <= i < p - 16 \/ p - 15 <= i < p) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
                 { intros i Hi Hr. apply AGZ; try ulia.
                   - (* [comment removed for export] *) intros HB2.
                     destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                     + destruct (chunk_cases bt st Lc FF W BATCHCLASS ba (blk_class n) (p - rz n) HC24 HCn CVB CV) as [[EC2 EA2] | D2].
                       * apply (NLC ba). split; [rewrite EC2, EA2; exact LIV | exact INCba].
                       * change (csize BATCHCLASS) with 8192 in D2. clear -Hi HB2 D2 V2 RZ RR RG2 PL3. Zlia.
                     + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [DS|DS]; clear -Hi HB2 DS A1 A2 BB1 BB2 V1 V2 V3 RZ PL3; Zlia.
                   - intros HT. destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                     + clear -Hi HT V1 V2 V3 TPG X1 X2 RZ RR RG2 PL3. Zlia.
                     + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (sec_dyn st sc Hs)) as DT. hnf in DT. cbn in DT.
                       clear -Hi HT DT A1 A2 V1 V2 V3 X1 X2 RZ PL3; Zlia.
                   - intros HS. destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                     + clear -Hi HS V1 SBH RZ. Zlia.
                     + destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((_ & _ & _ & _ & SD5) & _). clear -Hi HS SD5 V1 V2 V3 V4 RZ PL3. Zlia.
                   - intros Zi. destruct (ZLfacts i Zi) as (bl & Hbl2 & Hbl & CVl & Bl1 & Bl2 & Hi2 & UQ).
                     destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                     + destruct (chunk_cases bt st Lc FF W BATCHCLASS (ba_addr bl) (blk_class n) (p - rz n) HC24 HCn CVl CV) as [[EC2 EA2] | D2].
                       * apply (NBL (ba_addr bl) ltac:(exists bl; split; [exact Hbl2 | reflexivity]) eq_refl). left. rewrite EC2, EA2. exact LIV.
                       * change (csize BATCHCLASS) with 8192 in D2. clear -Hi Hi2 D2 V2 RZ RR RG2 PL3. Zlia.
                     + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [DS|DS]; clear -Hi Hi2 DS A1 A2 Bl1 Bl2 V1 V2 V3 RZ PL3; unfold BATCHSZ in Bl2; Zlia. }
                 split.
                 * (lazymatch goal with |- ?G => let G' := eval unfold rep_hdr in G in change_no_check G' end). split; [exact ST3|]. split; [exists b1; split; [exact Hb1 | frB AGh H2]|]. split; [frZ AGh H3|]. split; [frZ AGh H4|]. split; [frW DEF HW|]. split; [frZ AGh H5|].
                   intros Hrz. pose proof (rz_cases n) as RZC. destruct (HLC Hrz) as [L1' L2']. split; [frZ AGh L1' | frZ AGh L2'].
                 * destruct (R15 p n Hin) as [W1 _]. destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                   -- destruct (R4 _ HCn) as [_ (_ & _ & F3)]. destruct (carved_range bt st Lc FF W _ _ HCn CV) as (D1 & D2 & _).
                      pose proof (region_facts bt st Lc FF W _ HCn) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3' & _).
                      eapply writableZ_sub; [frW DEF F3 | lia | lia].
                   -- destruct (In_nth_error _ _ Hs) as [kk Hk]. destruct (R7 kk sc Hk) as (_ & _ & _ & _ & SW). eapply writableZ_sub; [frW DEF SW | ulia | lia].
               + (* [comment removed for export] *)
                 destruct (HQh m n' Hq) as [Hh HW]. split; [| frW DEF HW].
                 destruct (quar_item_range bt st Lc FF W m n' Hq) as (A1 & A2 & A3). pose proof (rz_range n').
                 eapply rep_hdr_frame; [exact DEF | exact Hh | ulia | ulia |]. intros i Hi Hr.
                 apply (HDRfree (m + 16) n' i); [right; replace (m + 16 - 16) with m by lia; exact Hq | exact Hi | | exact Hr].
                 intros ->.
                 destruct (hdr_zone bt st Lc FF W (m + 16) n' (p - 16) ltac:(right; replace (m + 16 - 16) with m by lia; exact Hq) Hi)
                   as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')].
                 * destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                   -- destruct (chunk_cases bt st Lc FF W (blk_class n') (prim_alloc_beg (m + 16) n') (blk_class n) (p - rz n) HC' HCn CV' CV) as [[EC EA] | D]; [| unfold prim_alloc_beg in *; ulia].
                      destruct (WR1 _ HCn) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK). destruct PART as (_ & LQ & _).
                      apply (LQ (p - rz n)). split; [exact LIV|]. rewrite <- EC, <- EA.
                      pose proof (quar_chunk bt st Lc FF W m n' Hq HP') as G'. cbn zeta in G'. destruct G' as (_ & _ & G3 & _). exact G3.
                   -- pose proof (carved_range bt st Lc FF W _ _ HC' CV') as (D1 & D2 & D3 & D4 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); unfold prim_alloc_beg in *; ulia.
                 * destruct (sec_facts bt st Lc FF W sc' Hs') as (B1 & B2 & B3 & B4 & B5 & B6 & _).
                   destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                   -- destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc' Hs')); ulia.
                   -- destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D]; [| ulia].
                      apply (sec_live_not_quar bt st Lc FF W sc Hs); [rewrite Eu, En; exact Hin|]. rewrite Eu, En. replace (p - 16) with m by lia.
                      replace n' with n in Hq by congruence. exact Hq. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact R9 | ulia | ulia | ulia | ulia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). ulia.
             - intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) Hr).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXfree _ _ INN); [ulia | ulia | rewrite Eb; lia | exact Hr].
               + apply (DYNfree _ _ (node_dyn st bb Hnb)); [| lia | exact Hr]. intros sc Hs _ _ E.
                 destruct (sec_vs_node bt st Lc FF W sc bb Hs Hnb); destruct (sec_facts bt st Lc FF W sc Hs) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & _); injection E; intros; ulia. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact R10 | ulia | ulia | ulia | ulia | ulia | ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXfree _ _ INFS); ulia.
               + exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) Hr).
               + apply (FIXfreeT _ _ (dtls_member bt st Lc FF W) (dtls_vs_thread bt st Lc FF W)); ulia.
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXfree _ _ INFS); ulia. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact R11 | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) Hr). }
    (* [comment removed for export] *)
    split. { destruct R12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
             change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st).
             assert (EXQ : forall g, existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? g) && (g <? (fst mn + 16 + snd mn + 7) / 8)) (quar st')
                               = ((p / 8 <=? g) && (g <? (p + n + 7) / 8)) || existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? g) && (g <? (fst mn + 16 + snd mn + 7) / 8)) (quar st)).
             { intros g. rewrite QE, QE0, existsb_app_mid. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). replace (p - 16 + 16) with p by lia. reflexivity. }
             (* [comment removed for export] *)
             assert (AGS : forall i, SB <= i < SB + CEIL / 8 -> ~ (SB + p / 8 <= i < SB + (p + n + 7) / 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros i Hi NU. apply AGF; [| clear -Hi; Zlia]. intros Hf. unfold foot_quar_newbatch, sh_lo, sh_hi, T_QC, T_PC, PC_SZ, BATCHCLASS in Hf.
               destruct Hf as [Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]]].
               6: { revert Z. destruct (rev (a_tq st)) as [|bl rl] eqn:ER; intros Z; [destruct Z|].
                    assert (Hbl : In bl (a_tq st ++ a_gq st)) by (apply in_app_iff; left; apply in_rev; rewrite ER; left; reflexivity).
                    destruct (batch_facts bt st Lc FF W bl Hbl) as (_ & _ & Bl1 & Bl2). clear -Z Hi Bl1 SBH. Zlia. }
               1-2: destruct (BLKZ i ltac:(am_tauto)) as [(_ & _ & NB) _]; apply NB; (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); clear -Hi; (first [clear - Hi | idtac]; Zlia).
               all: clear -Z Hi NU PL1 PL2 BB1 BB2 X1 X14 X15 TD5 SBH; Zlia. }
             split. { intros c0 g Hc0 Hg NL'. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _).
                      rewrite EXQ. destruct (Sumbool.sumbool_of_bool ((p / 8 <=? g) && (g <? (p + n + 7) / 8))) as [UG | NUG]; rewrite ?UG, ?NUG; (lazymatch goal with |- ?G => let G' := eval cbn [orb] in G in change_no_check G' end).
                      - apply SHFD. (lazymatch goal with |- ?G => let G' := eval unfold user_granule in G in change_no_check G' end). apply andb_prop in UG. destruct UG as [U1 U2]. apply Z.leb_le in U1. apply Z.ltb_lt in U2. lia.
                      - assert (NL0 : ~ live_granule Lc g).
                        { intros (p' & n' & Hin' & Hg'). destruct (Z.eq_dec p' p) as [-> | NEp]; [destruct (Z.eq_dec n' n) as [-> | NEn]|].
                          - unfold user_granule in Hg'. apply Bool.andb_false_iff in NUG. destruct NUG as [X|X]; [apply Z.leb_gt in X | apply Z.ltb_ge in X]; lia.
                          - apply NL'. exists p, n'. split; [apply INL; split; [exact Hin' | congruence] | exact Hg'].
                          - apply NL'. exists p', n'. split; [apply INL; split; [exact Hin' | congruence] | exact Hg']. }
                        pose proof (SH1 c0 g Hc0 Hg NL0) as BY. eapply (byteZ_frame _ _ _ _ _ BY); [clear -Hg E1 X14; Zlia | clear -Hg E2 E5 X15; Zlia |].
                        apply AGS; [clear -Hg E1 E2 E5 X14 X15; Zlia|]. apply Bool.andb_false_iff in NUG.
                        destruct NUG as [X|X]; [apply Z.leb_gt in X | apply Z.ltb_ge in X]; clear -X; Zlia. }
             split. { intros c0 g Hc0 Hg. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & _).
                      pose proof (SH2 c0 g Hc0 Hg) as BY. eapply (byteZ_frame _ _ _ _ _ BY); [clear -Hg E1 E2 E8 X14; Zlia | clear -Hg E5 E6 X15; Zlia |].
                      apply AGS; [clear -Hg E1 E2 E5 E6 E8 X14 X15; Zlia|]. intros HU. pose proof (pg8 _ E12) as AL.
                      (* [comment removed for export] *)
                      destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                      - destruct (carved_range bt st Lc FF W _ _ HCn CV) as (D1 & D2 & _). pose proof (region_facts bt st Lc FF W _ HCn) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
                        unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
                        destruct (Z.lt_ge_cases c0 (blk_class n)) as [LT|GE].
                        + assert (HM : c0 * 2 ^ 32 + 2 ^ 32 <= blk_class n * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
                          clear -Hg HU HM E6 D1 RZ. Zlia.
                        + assert (HM : blk_class n * 2 ^ 32 <= c0 * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; lia).
                          clear -Hg HU HM AL D2 F2 F3 V2. Zlia.
                      - destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [D|D]; clear -Hg HU D AL V1 V2 E1 E2 E5 E6 E8 PL3; Zlia. }
             split. { intros sc g Hs Hg NUG. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). pose proof (pg8 _ A3) as AL.
                      pose proof (SH3 sc g Hs Hg NUG) as BY. eapply (byteZ_frame _ _ _ _ _ BY); [clear -Hg A1; Zlia | clear -Hg A2; Zlia |].
                      apply AGS; [clear -Hg A1 A2; Zlia|]. intros HU.
                      destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc2 & Hs2 & Eu & En & V1 & V2 & V3 & V4 & V5)].
                      - destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [D|D]; clear -Hg HU D AL V1 V2 V3 PL3 RZ; Zlia.
                      - destruct (sec_cases bt st Lc FF W sc2 sc Hs2 Hs) as [<- | D].
                        + apply NUG. (lazymatch goal with |- ?G => let G' := eval unfold user_granule in G in change_no_check G' end). rewrite Eu, En. clear -HU; Zlia.
                        + destruct (sec_facts bt st Lc FF W sc2 Hs2) as (B1 & B2 & B3 & _). pose proof (pg8 _ B3) as AL2.
                          destruct D as [D|D]; clear -Hg HU D AL AL2 V1 V2; Zlia. }
             split. { intros sc g Hs HQ HU. apply INQ in HQ. destruct HQ as [E | HQ].
                      - injection E as E1 E2. apply SHFD. unfold user_granule in *. rewrite <- E2. replace p with (sc_user sc) by lia. exact HU.
                      - destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
                        pose proof (SH4 sc g Hs HQ HU) as BY. unfold user_granule in HU. eapply (byteZ_frame _ _ _ _ _ BY); [clear -HU A1 A5; Zlia | clear -HU A2 A6; Zlia |].
                        apply AGS; [clear -HU A1 A2 A5 A6; Zlia|]. intros HU2.
                        destruct LOC as [(HP & V1 & V2 & V3 & CV & HCn & LIV & RR) | (HP & sc2 & Hs2 & Eu & En & V1 & V2 & V3 & V4 & V5)].
                        + destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [D|D]; clear -HU HU2 D V1 V2 V3 PL3 A5 A6 A7 RZ; Zlia.
                        + destruct (sec_cases bt st Lc FF W sc2 sc Hs2 Hs) as [<- | D].
                          * apply (sec_live_not_quar bt st Lc FF W sc2 Hs2); [rewrite Eu, En; exact Hin | exact HQ].
                          * pose proof (pg8 _ A3) as AL. destruct (sec_facts bt st Lc FF W sc2 Hs2) as (B1 & B2 & B3 & _). pose proof (pg8 _ B3) as AL2.
                            destruct D as [D|D]; clear -HU HU2 D AL AL2 V1 V2 A5 A6; Zlia. }
             split. { intros c0 g Hc0 Hg. exact (def_keep M M' _ DEF (SH5 c0 g Hc0 Hg)). }
             intros sc g Hs Hg. exact (def_keep M M' _ DEF (SH6 sc g Hs Hg)). }
    (* [comment removed for export] *)
    split. { change (rep_ledger bt st mdl'). exact (rep_ledger_sbm bt st mdl mdl' SBM R13). }
    (* [comment removed for export] *)
    split. { destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st). change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st). change (a_dep st') with (a_dep st). change (a_shsec st') with (a_shsec st).
             pose proof (same_but_materialized_frame mdl mdl' SBM) as Fm.
             destruct Fm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
             split; [exact B1|]. split; [exact MI|]. split; [exact B3|].
             split; [intros p' n' Hin'; apply INL in Hin'; exact (B4 p' n' (proj1 Hin'))|].
             split; [exact B5|]. split; [exact B6|]. split; [exact B7|].
             rewrite E3. change (prim_charge st') with (prim_charge st). change (sec_charge st') with (sec_charge st). change (depot_charge st') with (depot_charge st). exact B8. }
    (* [comment removed for export] *)
    split. { intros p' n' Hin'. apply INL in Hin'. destruct (R15 p' n' (proj1 Hin')) as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f k0 Hf. frW DEF (R16 f k0 Hf). }
    split; [eapply (cellZ_frame _ _ _ _ _ _ R17); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia)) ltac:(ulia))] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ R18); [ulia | ulia | intros i Hi; exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia)) ltac:(ulia))] |].
    exact (rep_last_keep bt _ _ M M' DEF R19 (fun H => H)).
  Qed.

End Q2.
