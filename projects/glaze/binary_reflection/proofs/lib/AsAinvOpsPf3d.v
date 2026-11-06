(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvFreeS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition up8 (n : Z) : Z := (n + 7) / 8 * 8.
Lemma up8_facts : forall n, 1 <= n -> n <= up8 n /\ 8 <= up8 n /\ up8 n <= n + 7 /\ up8 n mod 8 = 0.
Proof. intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end). Z.div_mod_to_equations. lia. Qed.
Lemma up8_le : forall p n c, p mod 8 = 0 -> c mod 8 = 0 -> p + n <= c -> p + up8 n <= c.
Proof. intros p n c Hp Hc H. (lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end). Z.div_mod_to_equations. lia. Qed.

Section S.
  Context {RC : run_ceil}.
  (* [comment removed for export] *)
  Definition rt_priv (IA : as_addrs) (Lc FF : list (Z * Z)) (a : Z) : Prop :=
    a < CEIL /\ ~ (ia_img_lo IA <= a < ia_img_hi IA) /\ ~ app_visible IA Lc FF a.

  (* [comment removed for export] *)
  Definition OBL_nolazy_rt_stmt (bt : as_boot) : Prop := forall st Lc FF M mdl a,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl ->
    (bt_thread bt <= a < bt_thread bt + PG) \/ (bt_tctx bt <= a < bt_tctx bt + 0x10000)
    \/ (exists p n, In (p, n) Lc /\ p - 16 <= a < p + up8 n)
    \/ (exists b, In b (a_tq st ++ a_gq st) /\ ba_addr b <= a < ba_addr b + BATCHSZ) ->
    lzb mdl a = false.
  (* [comment removed for export] *)
  Definition OBL_freed_private_stmt (bt : as_boot) : Prop := forall st Lc FF L1 L2 p n a,
    WF bt st Lc FF -> Lc = L1 ++ (p, n) :: L2 ->
    (p - 16 <= a < p + up8 n \/ sh_lo p <= a < sh_hi p n) -> rt_priv (bt_ia bt) (L1 ++ L2) FF a.
  (* [comment removed for export] *)
  Definition OBL_rt_private_stmt (bt : as_boot) : Prop := forall st Lc FF a,
    WF bt st Lc FF ->
    (bt_thread bt <= a < bt_thread bt + PG) \/ (exists b, In b (a_tq st ++ a_gq st) /\ ba_addr b <= a < ba_addr b + BATCHSZ) ->
    rt_priv (bt_ia bt) Lc FF a.
  (* [comment removed for export] *)
  Definition OBL_stats_not_rep_stmt (bt : as_boot) : Prop := forall st Lc FF a, WF bt st Lc FF ->
    bt_thread bt + 2768 <= a < bt_thread bt + 3168 -> ~ rep_cells bt st Lc FF a.
  (* [comment removed for export] *)
  Definition OBL_blk_geom_stmt (bt : as_boot) : Prop := forall st Lc FF p n,
    WF bt st Lc FF -> In (p, n) Lc ->
    (p + up8 n <= bt_thread bt \/ bt_thread bt + PG <= p - 16)
    /\ (bt_tctx bt + 0x10000 <= p - 16 \/ p + up8 n <= bt_tctx bt)
    /\ ablk_ok (bt_ia bt) (p - 16) (16 + up8 n).
  Definition OBL_batch_geom_stmt (bt : as_boot) : Prop := forall st Lc FF b p n,
    WF bt st Lc FF -> In b (a_tq st ++ a_gq st) -> In (p, n) Lc ->
    (ba_addr b + BATCHSZ <= p - 16 \/ p + up8 n <= ba_addr b)
    /\ (ba_addr b + BATCHSZ <= bt_thread bt \/ bt_thread bt + PG <= ba_addr b)
    /\ AS_HEAPLO <= ba_addr b /\ ba_addr b + BATCHSZ <= CEIL.
  (* [comment removed for export] *)
  Definition OBL_hdr_writable_stmt (bt : as_boot) : Prop := forall st Lc FF M mdl p n,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> In (p, n) Lc -> writableZ (bt_segs bt) M (p - 16) (p + up8 n).
  (* [comment removed for export] *)
  Definition OBL_X_vs_node_stmt (bt : as_boot) : Prop := forall st Lc FF p n id a,
    WF bt st Lc FF -> In (p, n) Lc -> 1 <= id <= dp_nids (a_dep st) ->
    (p - 16 <= a < p + up8 n \/ bt_thread bt <= a < bt_thread bt + PG \/ CEIL <= a) ->
    ~ foot_node bt (a_dep st) id a.
  (* [comment removed for export] *)
  Definition OBL_store_private_stmt (bt : as_boot) : Prop := forall st Lc FF blk a,
    WF bt st Lc FF -> In blk (dp_storeblocks (a_dep st)) -> blk <= a < blk + 2 ^ 23 -> rt_priv (bt_ia bt) Lc FF a.

  Definition free_obls (bt : as_boot) : Prop :=
    OBL_nolazy_rt_stmt bt /\ OBL_freed_private_stmt bt /\ OBL_rt_private_stmt bt /\ OBL_stats_not_rep_stmt bt
    /\ OBL_blk_geom_stmt bt /\ OBL_batch_geom_stmt bt /\ OBL_hdr_writable_stmt bt /\ OBL_X_vs_node_stmt bt
    /\ OBL_store_private_stmt bt.
End S.
End AsAinvFreeS.
Require Stdlib.NArith.NArith Stdlib.Sorting.Permutation OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvOpsPf3c.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

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
  Lemma page_base_val : forall w : word, bv_unsigned (page_base w) = (bv_unsigned w / 4096) * 4096.
  Proof.
    intros w. (lazymatch goal with |- ?G => let G' := eval unfold page_base, page_base_of, page_size in G in change_no_check G' end). pose proof (u64_range w) as R.
    rewrite u_Z2bv; [reflexivity | |]; Z.div_mod_to_equations; lia.
  Qed.

  Lemma pg_in_ivs_member : forall l a, 0 <= a < 2 ^ 64 -> pg_in_ivz l a ->
    exists b n, In (b, n) l /\ bv_unsigned b <= a < bv_unsigned b + bv_unsigned n.
  Proof.
    intros l a Ha H. destruct H as [_ H]. unfold page_in_ranges in H. apply existsb_exists in H. destruct H as ([b n] & Hin & Hr).
    cbn [fst snd] in Hr. apply andb_prop in Hr. destruct Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    rewrite page_base_val, u_Z2bv in H1, H2 by lia. unfold page_size in H2.
    exists b, n. split; [exact Hin|]. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lzb_true_pg : forall mdl a, 0 <= a < 2 ^ 64 -> (lzb mdl a = true <-> pg_in_ivz (m_vm_lazy mdl) a).
  Proof. intros mdl a Ha. (lazymatch goal with |- ?G => let G' := eval unfold lzb, pg_in_ivz in G in change_no_check G' end). tauto. Qed.

  Section NoLazy.
    Variables (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model).
    Context {qt qg : Z}.
    Hypothesis W : WFq bt st Lc FF qt qg.
    Hypothesis R : Rep bt st Lc FF M mdl.

    Lemma rep_lazy_cases : forall a, 0 <= a < CEIL -> ~ in_band a -> lzb mdl a = true ->
      (((bt_resv6 bt <= a < bt_resv6 bt + bt_resv6_len bt) \/ (bt_ptrarr bt <= a < bt_ptrarr bt + 2 ^ 23) \/ (bt_store0 bt <= a < bt_store0 bt + 2 ^ 23))
         /\ ~ committed bt st a /\ ~ (SBEG + KSPACE <= a < SBEG + KSPACE + PG) /\ ~ holes bt st a)
      \/ (exists b, In b (dp_storeblocks (a_dep st)) /\ b <= a < b + 2 ^ 23).
    Proof.
      intros a Ha Hb Hl. apply (lzb_true_pg mdl a ltac:(ulia)) in Hl.
      destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & LZ & _) & _).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & LZ0 & LZB & LRI & M06 & M0K) & _).
      destruct (proj1 (LZ a) Hl) as [(P0 & NC & NH) | SB0]; [left | right; exact SB0].
      split; [exact (LZ0 a P0 Ha Hb)|]. split; [exact NC|]. split; [| exact NH]. intros Hr. exact (LRI a Hr P0).
    Qed.


    (* [comment removed for export] *)
    Lemma rep_nolazy_img : forall a, ia_img_lo IA <= a < ia_img_hi IA -> lzb mdl a = false.
    Proof.
      intros a Ha. destruct (lzb mdl a) eqn:E; [| reflexivity]. exfalso.
      pose proof (img_lits bt st Lc FF W) as [I1 I2]. apply (lzb_true_pg mdl a ltac:(ulia)) in E.
      destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & FA & _) & _).
      destruct (pg_in_ivs_member _ a ltac:(ulia) E) as (b & n & Hin & Hr).
      rewrite Forall_forall in FA. destruct (FA _ Hin) as (A1 & A2 & A3 & A4 & A5). cbn [fst snd] in A1, A2, A3, A4, A5.
      pose proof (u64_range b) as Rb. unfold PG in A1, A2. ulia.
    Qed.

    Lemma rep_nolazy_stack : forall a, CEIL <= a < 2 ^ 64 -> lzb mdl a = false.
    Proof.
      intros a Ha. destruct (lzb mdl a) eqn:E; [| reflexivity]. exfalso. apply (lzb_true_pg mdl a ltac:(ulia)) in E.
      destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & FA & _) & _).
      destruct (pg_in_ivs_member _ a ltac:(ulia) E) as (b & n & Hin & Hr).
      rewrite Forall_forall in FA. destruct (FA _ Hin) as (_ & _ & _ & A4 & _). cbn [fst snd] in A4. ulia.
    Qed.

    (* [comment removed for export] *)
    Lemma rep_nolazy_fixed : forall lo hi a, In (lo, hi) (bt_fixed bt) ->
      hi - lo < KSPACE -> hi - lo <> 2 ^ 23 -> lo <= a < hi -> lzb mdl a = false.
    Proof.
      intros lo hi a Hin Hl1 Hl2 Ha. destruct (lzb mdl a) eqn:E; [| reflexivity]. exfalso.
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & _) & _).
      destruct (RNG _ _ (all_ranges_fixed bt st _ Hin)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      destruct (rep_lazy_cases a ltac:(ulia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); ulia) E) as [([Z6 | [Z8 | ZS]] & NC & NRI & _) | (b & Hb & Zb)].
      - pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hin) (all_ranges_fixed bt st _ IN6) ltac:(intros EQ; injection EQ; intros; ulia)) as D. hnf in D. cbn in D. lia.
      - pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hin) (all_ranges_fixed bt st _ IN8) ltac:(intros EQ; injection EQ; intros; lia)) as D. hnf in D. cbn in D. lia.
      - pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hin) (all_ranges_fixed bt st _ INS) ltac:(intros EQ; injection EQ; intros; lia)) as D. hnf in D. cbn in D. lia.
      - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hin (store_dyn st b Hb)) as D. hnf in D. cbn in D. lia.
    Qed.

    Lemma rep_nolazy_thread : forall a, T <= a < T + PG -> lzb mdl a = false.
    Proof.
      intros a Ha. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & INT & _) & _).
      apply (rep_nolazy_fixed _ _ a INT); ulia.
    Qed.
    Lemma rep_nolazy_tctx : forall a, bt_tctx bt <= a < bt_tctx bt + 0x10000 -> lzb mdl a = false.
    Proof.
      intros a Ha. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INC & _) & _).
      apply (rep_nolazy_fixed _ _ a INC); ulia.
    Qed.
    Lemma rep_nolazy_fs : forall a, bt_fs bt <= a < bt_fs bt + FAKE_SIZE -> lzb mdl a = false.
    Proof.
      intros a Ha. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & _) & _).
      apply (rep_nolazy_fixed _ _ a INFS); ulia.
    Qed.


    Lemma rep_nolazy_reginfo : forall a, SBEG + KSPACE <= a < SBEG + KSPACE + PG -> lzb mdl a = false.
    Proof.
      intros a Ha. destruct (lzb mdl a) eqn:E; [| reflexivity]. exfalso.
      destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by lia.
      destruct (rep_lazy_cases a ltac:(ulia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); ulia) E) as [(_ & _ & NRI & _) | (b & Hb & Zb)]; [exact (NRI Ha)|].
      destruct (space_vs_dyn bt st Lc FF W _ _ (store_dyn st b Hb)); ulia.
    Qed.

    (* [comment removed for export] *)
    Lemma rep_nolazy_chunk : forall c ch a, 1 <= c <= 30 -> carved bt st c ch -> ch <= a < ch + csize c -> lzb mdl a = false.
    Proof.
      intros c ch a Hc CV Ha. destruct (lzb mdl a) eqn:E; [| reflexivity]. exfalso.
      destruct (carved_range bt st Lc FF W c ch Hc CV) as (C1 & C2 & C3 & C4 & C5).
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & _).
      destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by lia.
      destruct (rep_lazy_cases a ltac:(ulia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); ulia) E) as [(_ & NC & _) | (b & Hb & Zb)].
      - apply NC. left. exists c. split; [exact Hc|]. left. lia.
      - destruct (space_vs_dyn bt st Lc FF W _ _ (store_dyn st b Hb)); ulia.
    Qed.

    Lemma rep_nolazy_fa : forall c a, 1 <= c <= 30 -> fa_beg SBEG c <= a < fa_beg SBEG c + r_mapped_fa (a_reg st c) -> lzb mdl a = false.
    Proof.
      intros c a Hc Ha. destruct (lzb mdl a) eqn:E; [| reflexivity]. exfalso.
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
      destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by lia.
      destruct (rep_lazy_cases a ltac:(ulia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); ulia) E) as [(_ & NC & _) | (b & Hb & Zb)].
      - apply NC. left. exists c. split; [exact Hc|]. right. lia.
      - destruct (space_vs_dyn bt st Lc FF W _ _ (store_dyn st b Hb)); ulia.
    Qed.

    Lemma rep_nolazy_batch : forall b a, In b (a_tq st ++ a_gq st) -> ba_addr b <= a < ba_addr b + BATCHSZ -> lzb mdl a = false.
    Proof.
      intros b a Hb Ha. destruct (batch_facts bt st Lc FF W b Hb) as (CV & _).
      apply (rep_nolazy_chunk BATCHCLASS (ba_addr b) a ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CV). change (csize BATCHCLASS) with 8192. ulia.
    Qed.


    Lemma rep_nolazy_sec : forall sc a, In sc (a_sec st) -> sc_map sc <= a < sc_map sc + sc_mapsz sc -> lzb mdl a = false.
    Proof.
      intros sc a Hs Ha. destruct (lzb mdl a) eqn:E; [| reflexivity]. exfalso.
      destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & _) & _).
      destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((D1 & D1' & D3 & D4 & D5) & D2 & _).
      destruct (rep_lazy_cases a ltac:(ulia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); ulia) E) as [([Z6 | [Z8 | ZS]] & NC & NRI & _) | (b & Hb & Zb)].
      - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (sec_dyn st sc Hs)) as D. hnf in D. cbn in D. lia.
      - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 (sec_dyn st sc Hs)) as D. hnf in D. cbn in D. lia.
      - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INS (sec_dyn st sc Hs)) as D. hnf in D. cbn in D. lia.
      - destruct (sec_vs_store bt st Lc FF W sc b Hs Hb); lia.
    Qed.

    Lemma rep_nolazy_ptrarr : forall a, bt_ptrarr bt <= a < bt_ptrarr bt + 8 * a_nres st -> lzb mdl a = false.
    Proof.
      intros a Ha. destruct (lzb mdl a) eqn:E; [| reflexivity]. exfalso.
      pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & _) & _).
      destruct (RNG _ _ (all_ranges_fixed bt st _ IN8)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      destruct (rep_lazy_cases a ltac:(ulia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); ulia) E) as [(_ & NC & _) | (b & Hb & Zb)].
      - apply NC. right. exact Ha.
      - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 (store_dyn st b Hb)) as D. hnf in D. cbn in D. lia.
    Qed.
  End NoLazy.



  (* [comment removed for export] *)
  Lemma tq_batch_len : forall st Lc FF {qt qg : Z} b, WFq bt st Lc FF qt qg -> In b (a_tq st) -> 1 <= Z.of_nat (length (ba_items b)) <= BATCHCAP.
  Proof. intros st Lc FF qt qg b W Hb. destruct W as (_ & _ & (QT & _) & _). rewrite Forall_forall in QT. destruct (QT b Hb) as (L & _). exact L. Qed.

  Lemma read_tq : forall st Lc FF M mdl, Rep bt st Lc FF M mdl ->
    rep_list bt M (T + T_QC) (a_tq st) /\ rep_batches bt M (a_tq st)
    /\ (forall b, In b (a_tq st) -> forall (W : WF bt st Lc FF), carved bt st BATCHCLASS (ba_addr b) /\ 1 <= Z.of_nat (length (ba_items b)) <= BATCHCAP).
  Proof.
    intros st Lc FF M mdl R. destruct R as (_ & _ & (_ & _ & _ & _ & _ & _ & TL & _) & _ & R5 & _).
    split; [exact TL|]. split; [exact R5|]. intros b Hb W. destruct (batch_facts bt st Lc FF W b ltac:(apply in_app_iff; left; exact Hb)) as (CV & _ & _). split; [exact CV | exact (tq_batch_len st Lc FF b W Hb)].
  Qed.

  Lemma read_tq_last : forall st Lc FF M mdl tq' b {qt qg : Z}, WFq bt st Lc FF qt qg -> Rep bt st Lc FF M mdl -> a_tq st = tq' ++ [b] ->
    cellZ SG M (T + T_QC) 8 (Z.of_nat (length (a_tq st))) /\ cellZ SG M (T + T_QC + 16) 8 (ba_addr b) /\ cellZ SG M (T + T_QC + 24) 8 (q_bytes (a_tq st))
    /\ cellZ SG M (ba_addr b) 8 0 /\ cellZ SG M (ba_addr b + 8) 8 (ba_bytes b) /\ cellZ SG M (ba_addr b + 16) 8 (Z.of_nat (length (ba_items b)))
    /\ (forall j mn, nth_error (ba_items b) j = Some mn -> cellZ SG M (ba_addr b + 24 + 8 * Z.of_nat j) 8 (fst mn))
    /\ writableZ SG M (ba_addr b) (ba_addr b + BATCHSZ)
    /\ carved bt st BATCHCLASS (ba_addr b) /\ 1 <= Z.of_nat (length (ba_items b)) <= BATCHCAP
    /\ SBEG <= ba_addr b /\ ba_addr b + BATCHSZ <= SBEG + KSPACE.
  Proof.
    intros st Lc FF M mdl tq' b qt qg W R E. destruct (read_tq st Lc FF M mdl R) as ((L1 & L2 & L3 & L4) & RB & _).
    assert (Hb : In b (a_tq st ++ a_gq st)) by (rewrite E; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
    destruct (batch_facts bt st Lc FF W b Hb) as (CV & BL & B1 & B2).
    assert (HN : nth_error (a_tq st) (length tq') = Some b) by (rewrite E, nth_error_app2, Nat.sub_diag by lia; reflexivity).
    destruct (RB _ _ HN) as (C1 & C2 & C3 & C4 & CW).
    rewrite E in L3. rewrite rev_app_distr in L3. cbn [rev app] in L3. rewrite <- E in L3 |- * || idtac.
    assert (HN2 : nth_error (a_tq st) (S (length tq')) = None).
    { rewrite E. apply (proj2 (nth_error_None _ _)) || (apply nth_error_None). rewrite length_app. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    rewrite HN2 in C1. clear BL. pose proof (tq_batch_len st Lc FF b W ltac:(rewrite E; apply in_app_iff; right; left; reflexivity)) as [BL1 BL2].
    split; [exact L1|]. split; [exact L3|]. split; [exact L4|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
    split; [exact CW|]. split; [exact CV|]. split; [lia|]. lia.
  Qed.

End Pf.
End AsAinvOpsPf3c.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b AsAinvOpsPf3c.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
#[local] Ltac lia ::= am_lia.

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
  Lemma fold_items_app : forall l1 l2, fold_right (fun it acc => snd it + acc) 0 (l1 ++ l2) =
    fold_right (fun it acc => snd it + acc) 0 l1 + fold_right (fun (it : Z * Z) acc => snd it + acc) 0 l2.
  Proof using. induction l1 as [|x r IH]; intros l2; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); [reflexivity | rewrite IH; lia]. Qed.
  Lemma q_bytes_app : forall q1 q2, q_bytes (q1 ++ q2) = q_bytes q1 + q_bytes q2.
  Proof using. intros q1 q2. (lazymatch goal with |- ?G => let G' := eval unfold q_bytes in G in change_no_check G' end). induction q1 as [|x r IH]; (lazymatch goal with |- ?G => let G' := eval cbn [fold_right app] in G in change_no_check G' end); [reflexivity | rewrite IH; lia]. Qed.

  Lemma op_quar_append_eq : forall st tq' b m n, a_tq st = tq' ++ [b] ->
    op_quar_append st m n = set_tq st (tq' ++ [BATCH (ba_addr b) (ba_items b ++ [(m, n)])]).
  Proof using. intros st tq' b m n E. (lazymatch goal with |- ?G => let G' := eval unfold op_quar_append in G in change_no_check G' end). rewrite E, rev_app_distr. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite rev_involutive. reflexivity. Qed.

  Lemma quar_set_tq : forall st q, quar (set_tq st q) = flat_map ba_items (q ++ a_gq st).
  Proof using. intros. reflexivity. Qed.

  Lemma quar_split : forall st tq' b, a_tq st = tq' ++ [b] ->
    quar st = flat_map ba_items tq' ++ ba_items b ++ flat_map ba_items (a_gq st).
  Proof using. intros st tq' b E. (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). rewrite E, !flat_map_app. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite app_nil_r, app_assoc. reflexivity. Qed.

  Lemma quar_append_split : forall st tq' b m n, a_tq st = tq' ++ [b] ->
    quar (set_tq st (tq' ++ [BATCH (ba_addr b) (ba_items b ++ [(m, n)])])) =
    (flat_map ba_items tq' ++ ba_items b) ++ (m, n) :: flat_map ba_items (a_gq st).
  Proof using.
    intros st tq' b m n E. rewrite quar_set_tq, !flat_map_app. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite app_nil_r, <- !app_assoc. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). reflexivity.
  Qed.

  Lemma quar_append_in : forall st tq' b m n x, a_tq st = tq' ++ [b] ->
    In x (quar (set_tq st (tq' ++ [BATCH (ba_addr b) (ba_items b ++ [(m, n)])]))) <-> x = (m, n) \/ In x (quar st).
  Proof using.
    intros st tq' b m n x E. rewrite (quar_append_split st tq' b m n E), (quar_split st tq' b E).
    rewrite !in_app_iff. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). split; intros H; decompose [or] H; clear H; subst; auto 10.
  Qed.

  Lemma in_remove_mid : forall {A} (l1 l2 : list A) x y, List.NoDup (l1 ++ x :: l2) ->
    (In y (l1 ++ l2) <-> In y (l1 ++ x :: l2) /\ y <> x).
  Proof using.
    intros A l1 l2 x y ND. pose proof (NoDup_remove_2 _ _ _ ND) as NI. rewrite !in_app_iff. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). split.
    - intros H. split; [am_tauto|]. intros ->. apply NI. apply in_app_iff. exact H.
    - intros [[H|[H|H]] NE]; [left; exact H | exfalso; exact (NE (eq_sym H)) | right; exact H].
  Qed.

  (* [comment removed for export] *)
  Lemma partition_move_live_quar : forall st st' Lc Lc' c ab,
    (forall a, in_live_c Lc' c a <-> in_live_c Lc c a /\ a <> ab) ->
    (forall a, in_quar_c st' c a <-> in_quar_c st c a \/ a = ab) ->
    (forall a, in_batch st' a <-> in_batch st a) ->
    a_cache st' c = a_cache st c -> a_reg st' = a_reg st ->
    in_live_c Lc c ab ->
    partition_c bt st Lc c -> partition_c bt st' Lc' c.
  Proof using.
    intros st st' Lc Lc' c ab HL HQ HB EC ER LAB H. unfold partition_c in *.
    unfold in_cache_c, in_fa_c, carved in *. rewrite EC, ER.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (NQ : ~ in_quar_c st c ab) by (intros X; exact (H2 ab (conj LAB X))).
    assert (NC : ~ (exists k, In k (a_cache st c) /\ ab = chunk_of_compact SBEG c k)) by (intros X; exact (H3 ab (conj LAB X))).
    assert (NF : ~ (exists k, In k (r_free (a_reg st c)) /\ ab = chunk_of_compact SBEG c k)) by (intros X; exact (H4 ab (conj LAB X))).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact H9 | exact H10]]]]]]]]].
    - intros a. rewrite (HL a), (HQ a), (HB a), (H1 a). split.
      + intros X. destruct (Z.eq_dec a ab) as [-> | NE]; [right; left; right; reflexivity|]. decompose [or] X; am_tauto.
      + intros X. decompose [and or] X; try am_tauto. subst a. left. exact LAB.
    - intros a [X Y]. apply (HL a) in X. apply (HQ a) in Y. destruct X as [X NE]. destruct Y as [Y | Y]; [exact (H2 a (conj X Y)) | exact (NE Y)].
    - intros a [X Y]. apply (HL a) in X. destruct X as [X _]. exact (H3 a (conj X Y)).
    - intros a [X Y]. apply (HL a) in X. destruct X as [X _]. exact (H4 a (conj X Y)).
    - intros a [X Y]. apply (HQ a) in X. destruct X as [X | ->]; [exact (H5 a (conj X Y)) | exact (NC Y)].
    - intros a [X Y]. apply (HQ a) in X. destruct X as [X | ->]; [exact (H6 a (conj X Y)) | exact (NF Y)].
    - exact H7.
    - intros a Hb Hc X. apply (HB a) in Hb. apply (H8 a Hb Hc). destruct X as [X|[X|[X|X]]].
      + apply (HL a) in X. left. exact (proj1 X).
      + apply (HQ a) in X. destruct X as [X | ->]; [right; left; exact X | left; exact LAB].
      + am_tauto. + am_tauto.
  Qed.

  Lemma partition_ext : forall st st' Lc Lc' c,
    (forall a, in_live_c Lc' c a <-> in_live_c Lc c a) ->
    (forall a, in_quar_c st' c a <-> in_quar_c st c a) ->
    (forall a, in_batch st' a <-> in_batch st a) ->
    a_cache st' c = a_cache st c -> a_reg st' = a_reg st ->
    partition_c bt st Lc c -> partition_c bt st' Lc' c.
  Proof using.
    intros st st' Lc Lc' c HL HQ HB EC ER H. unfold partition_c in *.
    unfold in_cache_c, in_fa_c, carved in *. rewrite EC, ER.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact H9 | exact H10]]]]]]]]].
    - intros a. rewrite (HL a), (HQ a), (HB a). exact (H1 a).
    - intros a [X Y]. apply (H2 a). split; [apply (HL a); exact X | apply (HQ a); exact Y].
    - intros a [X Y]. apply (H3 a). split; [apply (HL a); exact X | exact Y].
    - intros a [X Y]. apply (H4 a). split; [apply (HL a); exact X | exact Y].
    - intros a [X Y]. apply (H5 a). split; [apply (HQ a); exact X | exact Y].
    - intros a [X Y]. apply (H6 a). split; [apply (HQ a); exact X | exact Y].
    - exact H7.
    - intros a Hb Hc X. apply (H8 a); [apply (HB a); exact Hb | exact Hc |].
      destruct X as [X|[X|[X|X]]]; [left; apply (HL a); exact X | right; left; apply (HQ a); exact X | am_tauto | am_tauto].
  Qed.

  (* [comment removed for export] *)
  Theorem OPS_WFq_quar_append_pf : forall st Lc FF L1 L2 p n tq' b (qt qg : Z),
    WFq bt st Lc FF qt qg -> Lc = L1 ++ (p, n) :: L2 -> a_tq st = tq' ++ [b] ->
    Z.of_nat (length (ba_items b)) < BATCHCAP ->
    WFq bt (op_quar_append st (p - 16) n) (L1 ++ L2) FF (q_bytes (a_tq st) + n) qg.
  Proof using.
    intros st Lc FF L1 L2 p n tq' b qt qg W HL Htq HBC.
    rewrite (op_quar_append_eq st tq' b (p - 16) n Htq).
    set (b' := BATCH (ba_addr b) (ba_items b ++ [(p - 16, n)])). set (st' := set_tq st (tq' ++ [b'])).
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM & WMP & G).
    assert (Hin : In (p, n) Lc) by (rewrite HL; apply in_app_iff; right; left; reflexivity).
    destruct (LV1 p n Hin) as (N1 & P16 & PLO & CVL).
    assert (NDL : List.NoDup (L1 ++ (p, n) :: L2)) by (rewrite <- HL; exact LV2).
    assert (INL : forall x, In x (L1 ++ L2) <-> In x Lc /\ x <> (p, n)) by (intros x; rewrite HL; apply in_remove_mid; exact NDL).
    assert (INQ : forall x, In x (quar st') <-> x = (p - 16, n) \/ In x (quar st)) by (intros x; (lazymatch goal with |- ?G => let G' := eval unfold st', b' in G in change_no_check G' end); apply quar_append_in; exact Htq).
    assert (Hb : In b (a_tq st)) by (rewrite Htq; apply in_app_iff; right; left; reflexivity).
    assert (WB : wf_batch bt st b) by (rewrite Forall_forall in Q1; exact (Q1 b Hb)).
    destruct WB as (WB1 & WB2 & WB3).
    (* [comment removed for export] *)
    assert (NQP : forall n', ~ In (p - 16, n') (quar st)).
    { intros n' HQ'. destruct (quar_item bt st Lc FF W (p - 16) n' HQ') as (N1' & [[HP' CV'] | [HP' RG']]).
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
          apply (sec_live_not_quar bt st Lc FF W sc Hs); [rewrite Eu, En2; exact Hin | rewrite Eu, En; exact HQ']. }
    assert (G' : (bt_spacebeg bt mod 2 ^ 16 = 0 /\ Z.of_nat (length (L1 ++ L2)) <= LMAX /\ PHI (L1 ++ L2) <= GBUDGET) /\ bt_ok bt /\ dep0_ok bt).   (* [comment removed for export] *)
    { destruct G as ((GA & GC & GB) & GOK). rewrite HL in GC, GB. rewrite length_app in GC. cbn [length] in GC. rewrite PHI_app in GB. cbn [PHI snd] in GB. rewrite length_app, PHI_app.
      split; [split; [exact GA | split; [lia | clear -GB N1; unfold MBLK in *; lia]] | exact GOK]. }
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end). split; [| split; [exact WC | split; [| split; [| split; [| split; [exact WK | split; [exact WD | split; [exact WM | split; [exact WMP | exact G']]]]]]]]].
    - (* [comment removed for export] *) split; [| exact WR2]. intros c Hc. destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). change (a_reg st' c) with (a_reg st c). repeat (split; [assumption|]). split; [| exact FHK].
      assert (HBt : forall a, in_batch st' a <-> in_batch st a).
      { intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_batch, st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq set_tq] in G in change_no_check G' end). rewrite Htq, <- !app_assoc. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). split; intros (b0 & Hb0 & E0);
          (apply in_app_iff in Hb0; destruct Hb0 as [Hb0 | [<- | Hb0]];
           [exists b0; split; [apply in_app_iff; left; exact Hb0 | exact E0]
           | first [exists b; split; [apply in_app_iff; right; left; reflexivity | exact E0] | exists b'; split; [apply in_app_iff; right; left; reflexivity | exact E0]]
           | exists b0; split; [apply in_app_iff; right; right; exact Hb0 | exact E0]]). }
      destruct (is_primary n) eqn:HP.
      + pose proof (live_chunk bt st Lc FF W p n Hin HP) as Gv. cbn zeta in Gv. destruct Gv as (G1 & G2 & G3 & G4 & G5 & G6).
        destruct (Z.eq_dec c (blk_class n)) as [-> | NE].
        * apply (partition_move_live_quar st st' Lc (L1 ++ L2) (blk_class n) (prim_alloc_beg p n)); [| | exact HBt | reflexivity | reflexivity | exact G3 | exact PART].
          -- intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
             ++ intros (p' & n' & Hin' & HP' & HC' & HA'). apply INL in Hin'. destruct Hin' as [Hin' NE'].
                split; [exists p', n'; repeat split; assumption|]. intros ->.
                destruct (live_range bt st Lc FF W p' n' Hin') as (L1' & _ & L3' & _).
                pose proof (rz_unif n n' ltac:(lia) ltac:(lia) HP HP' (eq_sym HC')) as ER.
                assert (p' = p) by (unfold prim_alloc_beg in HA'; clear -HA' ER; lia). subst p'.
                destruct (Z.eq_dec n' n) as [-> | NE2]; [exact (NE' eq_refl)|].
                destruct (LV3 p n' p n Hin' Hin ltac:(clear -NE2; congruence)); clear -H N1 L3'; lia.
             ++ intros [(p' & n' & Hin' & X) NE']. exists p', n'. split; [| exact X]. apply INL. split; [exact Hin'|].
                intros E. injection E as -> ->. apply NE'. destruct X as (_ & _ & X). symmetry. exact X.
          -- intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). split.
             ++ intros (m & n' & Hq & X). apply INQ in Hq. destruct Hq as [E | Hq]; [| left; exists m, n'; split; assumption].
                injection E as -> ->. right. destruct X as (_ & _ & X). rewrite <- X. (lazymatch goal with |- ?G => let G' := eval unfold prim_alloc_beg in G in change_no_check G' end). f_equal. lia.
             ++ intros [(m & n' & Hq & X) | ->].
                ** exists m, n'. split; [apply INQ; right; exact Hq | exact X].
                ** exists (p - 16), n. split; [apply INQ; left; reflexivity|]. replace (p - 16 + 16) with p by lia. split; [exact HP | split; reflexivity].
        * apply (partition_ext st st' Lc (L1 ++ L2) c); [| | exact HBt | reflexivity | reflexivity | exact PART].
          -- intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
             ++ intros (p' & n' & Hin' & X). apply INL in Hin'. exists p', n'. split; [exact (proj1 Hin') | exact X].
             ++ intros (p' & n' & Hin' & X). exists p', n'. split; [| exact X]. apply INL. split; [exact Hin'|].
                intros E. injection E as -> ->. apply NE. destruct X as (_ & X & _). symmetry. exact X.
          -- intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). split.
             ++ intros (m & n' & Hq & X). apply INQ in Hq. destruct Hq as [E | Hq]; [| exists m, n'; split; assumption].
                injection E as -> ->. exfalso. apply NE. destruct X as (_ & X & _). symmetry. exact X.
             ++ intros (m & n' & Hq & X). exists m, n'. split; [apply INQ; right; exact Hq | exact X].
      + apply (partition_ext st st' Lc (L1 ++ L2) c); [| | exact HBt | reflexivity | reflexivity | exact PART].
        * intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
          -- intros (p' & n' & Hin' & X). apply INL in Hin'. exists p', n'. split; [exact (proj1 Hin') | exact X].
          -- intros (p' & n' & Hin' & X). exists p', n'. split; [| exact X]. apply INL. split; [exact Hin'|].
             intros E. injection E as -> ->. destruct X as (X & _). rewrite HP in X. discriminate X.
        * intros a. (lazymatch goal with |- ?G => let G' := eval unfold in_quar_c in G in change_no_check G' end). split.
          -- intros (m & n' & Hq & X). apply INQ in Hq. destruct Hq as [E | Hq]; [| exists m, n'; split; assumption].
             injection E as -> ->. destruct X as (X & _). rewrite HP in X. discriminate X.
          -- intros (m & n' & Hq & X). exists m, n'. split; [apply INQ; right; exact Hq | exact X].
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine, wf_quarantine_q in G in change_no_check G' end). change (a_tq st') with (tq' ++ [b']). change (a_gq st') with (a_gq st).
      split. { rewrite Forall_app. split; [rewrite Forall_forall in Q1 |- *; intros b0 Hb0; apply Q1; rewrite Htq; apply in_app_iff; left; exact Hb0|].
               constructor; [| constructor]. (lazymatch goal with |- ?G => let G' := eval unfold wf_batch, b' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items ba_addr] in G in change_no_check G' end). rewrite length_app. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end).
               split; [lia|]. split; [exact WB2|]. intros m n' Hmn. apply in_app_iff in Hmn. destruct Hmn as [Hmn | [E | []]]; [exact (WB3 m n' Hmn)|].
               injection E as <- <-. replace (p - 16 + 16) with p by lia. split; [lia|].
               destruct (is_primary n) eqn:HP; [left; split; [reflexivity | exact (CVL eq_refl)] | right; split; [reflexivity | exact (S7 p n Hin HP)]]. }
      split; [exact Q2|].
      split. { rewrite q_bytes_app. (lazymatch goal with |- ?G => let G' := eval cbn [q_bytes fold_right] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold b', ba_bytes in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end). rewrite fold_items_app. (lazymatch goal with |- ?G => let G' := eval cbn [fold_right snd] in G in change_no_check G' end).
               rewrite Htq, q_bytes_app. (lazymatch goal with |- ?G => let G' := eval cbn [q_bytes fold_right] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold ba_bytes in G in change_no_check G' end). lia. }
      split; [exact Q4|].
      split. { replace (map ba_addr ((tq' ++ [b']) ++ a_gq st)) with (map ba_addr (a_tq st ++ a_gq st)); [exact Q5|].
               rewrite Htq, !map_app. reflexivity. }
      (lazymatch goal with |- ?G => let G' := eval unfold st', b' in G in change_no_check G' end). rewrite (quar_append_split st tq' b (p - 16) n Htq). rewrite (quar_split st tq' b Htq) in Q6.
      rewrite map_app. (lazymatch goal with |- ?G => let G' := eval cbn [map fst] in G in change_no_check G' end). apply NoDup_Add with (a := p - 16) (l := map fst (flat_map ba_items tq' ++ ba_items b) ++ map fst (flat_map ba_items (a_gq st))).
      { rewrite map_app. apply Add_app. }
      rewrite <- map_app, <- app_assoc. split; [exact Q6|].
      intros HIn. apply in_map_iff in HIn. destruct HIn as ([m n'] & E & HIn). cbn in E. subst m.
      apply (NQP n'). rewrite (quar_split st tq' b Htq). exact HIn.
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

  Lemma WFq_mono : forall st Lc FF qt qg qt' qg', WFq bt st Lc FF qt qg -> qt <= qt' -> qg <= qg' -> WFq bt st Lc FF qt' qg'.
  Proof using.
    intros st Lc FF qt qg qt' qg' W H1 H2. pose proof W as (WR & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & REST).
    split; [exact WR|]. split; [exact WC|]. split; [| exact REST]. split; [exact Q1|]. split; [exact Q2|]. split; [lia|]. split; [lia|]. exact (conj Q5 Q6).
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma existsb_app_mid : forall {A} (f : A -> bool) l1 x l2, existsb f (l1 ++ x :: l2) = f x || existsb f (l1 ++ l2).
  Proof using. intros A f l1 x l2. rewrite !existsb_app. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). destruct (f x), (existsb f l1); reflexivity. Qed.

  Theorem OPS_REP_quar_append_pf : OPS_REP_quar_append bt.
  Proof using.
    intros st Lc FF L1 L2 M M' mdl mdl' p n tq' b W R HL Htq HBC. cbn zeta. intros AGR ST3 SHFD CSZ CCNT CIT CQB SBM MI.
    rewrite (op_quar_append_eq st tq' b (p - 16) n Htq).
    set (cnt := Z.of_nat (length (ba_items b))) in *.
    set (b' := BATCH (ba_addr b) (ba_items b ++ [(p - 16, n)])). set (st' := set_tq st (tq' ++ [b'])).
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
    assert (INQ : forall x, In x (quar st') <-> x = (p - 16, n) \/ In x (quar st)) by (intros x; (lazymatch goal with |- ?G => let G' := eval unfold st', b' in G in change_no_check G' end); apply quar_append_in; exact Htq).
    assert (QE : quar st' = (flat_map ba_items tq' ++ ba_items b) ++ (p - 16, n) :: flat_map ba_items (a_gq st)) by ((lazymatch goal with |- ?G => let G' := eval unfold st', b' in G in change_no_check G' end); apply quar_append_split; exact Htq).
    pose proof (quar_split st tq' b Htq) as QE0.
    assert (Hb : In b (a_tq st ++ a_gq st)) by (rewrite Htq; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
    destruct (batch_facts bt st Lc FF W b Hb) as (CVB & BL & BB1 & BB2). unfold BATCHSZ, KSPACE in BB2. unfold BATCHCAP in BL, HBC.
    pose proof (agrees_DEFK _ _ _ AGR) as DEF. pose proof (agrees_at' _ _ _ AGR) as AGF.
    (* [comment removed for export] *)
    assert (LOC : (is_primary n = true /\ SBEG <= p - rz n /\ p + n <= p - rz n + csize (blk_class n) /\ p - rz n + csize (blk_class n) <= SBEG + KSPACE
                     /\ carved bt st (blk_class n) (p - rz n) /\ 1 <= blk_class n <= 30 /\ in_live_c Lc (blk_class n) (p - rz n) /\ rz n + rounded n <= csize (blk_class n))
                  \/ (is_primary n = false /\ exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n
                                               /\ sc_map sc + PG + 16 <= p /\ p + n <= sc_map sc + sc_mapsz sc /\ 0 < sc_map sc /\ sc_map sc + sc_mapsz sc <= CEIL
                                               /\ p + 8 <= sc_map sc + sc_mapsz sc)).
    { destruct (is_primary n) eqn:HP.
      - left. pose proof (live_chunk bt st Lc FF W p n Hin HP) as Gv. cbn zeta in Gv. destruct Gv as (G1 & G2 & G3 & G4 & G5 & G6). unfold prim_alloc_beg in *.
        destruct (carved_range bt st Lc FF W _ _ G1 G2) as (C1 & C2 & C3 & C4 & C5).
        pose proof (csize_class_of (needed n)) as CC. unfold blk_class in *.
        assert (NB : 1 <= needed n <= 65536) by (pose proof HP as HP2; unfold is_primary in HP2; apply Z.leb_le in HP2; unfold needed in *; lia).
        specialize (CC NB). assert (EN : needed n = rounded n + rz n) by reflexivity. repeat split; try assumption; lia.
      - right. split; [reflexivity|]. destruct (live_sec bt st Lc FF W p n Hin HP) as (sc & Hs & Eu & En). exists sc.
        destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). rewrite Eu, En in *.
        unfold sc_mapsz in *. pose proof (sec_map_size_ge n ltac:(lia)) as [SG1 SG2]. unfold PG in *. repeat split; try assumption; try lia. }
    destruct (carved_range bt st Lc FF W BATCHCLASS (ba_addr b) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVB) as (CB1 & CB2 & CB3 & CB4 & CB5).
    change (csize BATCHCLASS) with 8192 in CB2, CB4.
    (* [comment removed for export] *)
    assert (FZ : forall i, foot_quar_append bt p n (ba_addr b) cnt i ->
              (i = p - 16 \/ p <= i < p + 8) \/ (ba_addr b <= i < ba_addr b + BATCHSZ) \/ (T <= i < T + PG) \/ (SB <= i < AS_HEAPLO) \/ CEIL <= i).
    { intros i Hf. unfold foot_quar_append, T_QC, sh_lo, sh_hi in Hf. destruct BL as [BL1 BL2]. unfold cnt in Hf.
      clear -Hf BL1 HBC PL1 PL2. Zlia. }
    assert (BLKZ : forall i, (i = p - 16 \/ p <= i < p + 8) ->
             (0 <= i < CEIL /\ ~ (ia_img_lo IA <= i < ia_img_hi IA) /\ ~ in_band i) /\
             ((is_primary n = true /\ p - rz n <= i < p - rz n + csize (blk_class n)) \/
              (is_primary n = false /\ exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n /\ sc_map sc + PG <= i < sc_map sc + sc_mapsz sc))).
    { intros i Hi. destruct LOC as [(HP & Z1 & Z2 & Z3 & CV & HC & LIV & RR) | (HP & sc & Hs & Eu & En & Z1 & Z2 & Z3 & Z4 & Z5)].
      - split; [clear -Hi Z1 Z2 Z3 RZ RR RG1 RG2 RG3 RG4 SBH I2 X15; (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); Zlia|]. left. split; [exact HP|]. lia.
      - split; [| right; split; [exact HP|]; exists sc; repeat split; try assumption; ulia].
        destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((D1 & D1' & D3 & D4 & D5) & _).
        clear -Hi Z1 Z2 Z3 Z4 Z5 D1 D1' D3 D4 D5 RZ. (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end). Zlia. }
    assert (AGZ : forall i, 0 <= i -> i < CEIL -> ~ (i = p - 16 \/ p <= i < p + 8) -> ~ (ba_addr b <= i < ba_addr b + BATCHSZ) ->
                  ~ (T <= i < T + PG) -> ~ (SB <= i < AS_HEAPLO) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi0 Hi1 N1 N2 N3 N4. apply AGF; [| ulia]. intros Hf. destruct (FZ i Hf) as [Z|[Z|[Z|[Z|Z]]]]; try am_tauto. ulia. }
    assert (IMGfree : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply AGZ; [ulia | ulia | | | | ulia].
      - intros Hbk. destruct (BLKZ i Hbk) as [(_ & NI & _) _]. exact (NI Hi).
      - intros X. destruct (dyn_kind_facts bt st Lc FF W i (dyn_kind_space bt st Lc FF W i ltac:(ulia))) as (_ & _ & NH & _). exact (NH Hi).
      - intros X. destruct (dyn_kind_facts bt st Lc FF W i (dyn_kind_fixed bt st _ _ i INT X)) as (_ & _ & NH & _). exact (NH Hi). }
    assert (IMGK : forall i, img_kind bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i [Hi _] _. exact (IMGfree i Hi). }
    assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
    (* [comment removed for export] *)
    assert (FIXfree : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> PG -> hi - lo < KSPACE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo Hlen Hlen2 i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hlo) (all_ranges_fixed bt st _ INT) ltac:(intros E; injection E; intros; ulia)) as D. hnf in D. cbn in D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hlo Hlen2) as [SP|SP]; apply AGZ; try (first [clear - Hr A3 Hi SP BB1 D A5 BB2 | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [(first [clear - Hbk SP Hi Z1 RZ | idtac]; ulia) | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hlo (sec_dyn st sc Hs)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [(first [clear - Hbk SP Hi Z3 Z2 PL3 | idtac]; ulia) | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hlo (sec_dyn st sc Hs)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia). }
    (* [comment removed for export] *)
    assert (FIXfreeT : forall lo hi, In (lo, hi) (bt_fixed bt) -> (hi <= T \/ T + PG <= lo) -> hi - lo < KSPACE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo Hlen Hlen2 i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof Hlen as D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hlo Hlen2) as [SP|SP]; apply AGZ; try (first [clear - Hr A3 Hi SP BB1 Hlen A5 BB2 | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [(first [clear - Hbk SP Hi Z1 RZ | idtac]; ulia) | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hlo (sec_dyn st sc Hs)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [(first [clear - Hbk SP Hi Z3 Z2 PL3 | idtac]; ulia) | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hlo (sec_dyn st sc Hs)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia). }
    (* [comment removed for export] *)
    assert (DYNfree : forall lo hi, In (lo, hi) (dyn_ranges st) ->
               (forall sc, In sc (a_sec st) -> sc_user sc = p -> sc_n sc = n -> (lo, hi) <> (sc_map sc, sc_map sc + sc_mapsz sc)) ->
               forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo NSELF i Hi Hr. destruct (RNG _ _ (all_ranges_dyn bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT Hlo) as D. hnf in D. cbn in D.
      destruct (space_vs_dyn bt st Lc FF W lo hi Hlo) as [SP|SP]; apply AGZ; try (first [clear - Hr A3 Hi SP BB1 D A5 BB2 | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [ulia | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_dyn bt st _ Hlo) (all_ranges_dyn bt st _ (sec_dyn st sc Hs)) (NSELF sc Hs Eu En)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]]; [destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [ulia | rewrite HP in HP'; discriminate HP']|].
        pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_dyn bt st _ Hlo) (all_ranges_dyn bt st _ (sec_dyn st sc Hs)) (NSELF sc Hs Eu En)) as D2. hnf in D2. cbn in D2. (first [clear - D2 Zc Hi | idtac]; ulia). }
    (* [comment removed for export] *)
    assert (CHKfree : forall c' a', 1 <= c' <= 30 -> carved bt st c' a' ->
               ~ (is_primary n = true /\ c' = blk_class n /\ a' = p - rz n) -> ~ (c' = BATCHCLASS /\ a' = ba_addr b) ->
               forall i, a' <= i < a' + csize c' -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c' a' Hc' CV' NE NB i Hi. destruct (carved_range bt st Lc FF W c' a' Hc' CV') as (D1 & D2 & D3 & D4 & D5).
      apply AGZ; try (first [clear - D3 Hi X14 D4 X15 TPG SPH R6a | idtac]; ulia).
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]].
        + destruct LOC as [(_ & Z1 & Z2 & Z3 & CV & HC & _) | (HP' & _)]; [| rewrite HP in HP'; discriminate HP'].
          destruct (chunk_cases bt st Lc FF W c' a' (blk_class n) (p - rz n) Hc' HC CV' CV) as [[EC EA] | D]; [apply NE; repeat split; assumption | (first [clear - D Zc Hi | idtac]; ulia)].
        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); (first [clear - H1 Zc D3 Hi D4 | idtac]; ulia).
      - intros HB2. destruct (chunk_cases bt st Lc FF W c' a' BATCHCLASS (ba_addr b) Hc' ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CV' CVB) as [[EC EA] | D]; [apply NB; split; assumption|].
        change (csize BATCHCLASS) with 8192 in D. ulia. }
    assert (RIfree : forall i, SBEG + KSPACE <= i < SBEG + KSPACE + PG -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply AGZ; try ulia. intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]].
      - destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [ulia | rewrite HP in HP'; discriminate HP'].
      - destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia. }
    assert (FAfree : forall c0, 1 <= c0 <= 30 -> forall i, fa_beg SBEG c0 <= i < fa_beg SBEG c0 + 2 ^ 29 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c0 Hc0 i Hi. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & _).
      apply AGZ; [ulia | ulia | | destruct (carved_range bt st Lc FF W BATCHCLASS (ba_addr b) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVB) as (D1 & D2 & _); change (csize BATCHCLASS) with 8192 in D2; pose proof (region_facts bt st Lc FF W BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as RF; cbn zeta in RF; destruct RF as (F1 & F2 & F3 & F4 & F5 & _) | ulia | ulia].
      - intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]].
        + destruct LOC as [(_ & Z1 & Z2 & Z3 & CV & HC & _) | (HP' & _)]; [| rewrite HP in HP'; discriminate HP'].
          destruct (carved_range bt st Lc FF W _ _ HC CV) as (D1 & D2 & _). pose proof (region_facts bt st Lc FF W _ HC) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
          unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
          destruct (Z.lt_trichotomy c0 (blk_class n)) as [LT|[->|GT]]; [| ulia |].
          * assert (c0 * 2 ^ 32 + 2 ^ 32 <= blk_class n * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). ulia.
          * assert (blk_class n * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (blk_class n * 2 ^ 32 + 2 ^ 32) with ((blk_class n + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). ulia.
        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
      - unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
        destruct (Z.lt_trichotomy c0 BATCHCLASS) as [LT|[->|GT]]; [| ulia |].
        * assert (c0 * 2 ^ 32 + 2 ^ 32 <= BATCHCLASS * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; unfold BATCHCLASS in *; lia). ulia.
        * assert (BATCHCLASS * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (BATCHCLASS * 2 ^ 32 + 2 ^ 32) with ((BATCHCLASS + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; unfold BATCHCLASS in *; lia). ulia. }
    (* [comment removed for export] *)
    assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> i <> p - 16 -> 0 <= i < 2 ^ 64 ->
               M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros p' n' i Hown Hf NI Hr. pose proof (rz_range n') as RZ'.
      destruct (hdr_zone bt st Lc FF W p' n' i Hown Hf) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')].
      - (* [comment removed for export] *)
        destruct LOC as [(HP & Y1 & Y2 & Y3 & CV & HC & LIV & RR) | (HP & sc & Hs & Eu & En & Y1 & Y2 & Y3 & Y4 & Y5)].
        + destruct (chunk_cases bt st Lc FF W (blk_class n') (prim_alloc_beg p' n') (blk_class n) (p - rz n) HC' HC CV' CV) as [[EC EA] | D].
          * (* [comment removed for export] *)
            pose proof (rz_unif n n' ltac:(lia) N1' HP HP' (eq_sym EC)) as ER. unfold prim_alloc_beg in EA.
            assert (p' = p) by (clear -EA ER; lia). subst p'.
            apply AGZ; try ulia. intros HB2. destruct (carved_range bt st Lc FF W BATCHCLASS (ba_addr b) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVB) as (D1 & D2 & _). change (csize BATCHCLASS) with 8192 in D2.
            destruct (chunk_cases bt st Lc FF W BATCHCLASS (ba_addr b) (blk_class n) (p - rz n) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) HC CVB CV) as [[EC2 EA2] | D3]; [| change (csize BATCHCLASS) with 8192 in D3; unfold prim_alloc_beg in *; ulia].
            destruct (WR1 BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _). destruct PARTB as (_ & _ & _ & _ & _ & _ & _ & NBL & _).
            exfalso. apply (NBL (ba_addr b) ltac:(exists b; split; [exact Hb | reflexivity]) eq_refl). left. rewrite EC2, EA2. exact LIV.
          * apply (CHKfree (blk_class n') (prim_alloc_beg p' n') HC' CV'); [intros (_ & EC & EA); unfold prim_alloc_beg in *; lia | | lia].
            intros [EC EA]. destruct (WR1 BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _). destruct PARTB as (_ & _ & _ & _ & _ & _ & _ & NBL & _).
            apply (NBL (ba_addr b) ltac:(exists b; split; [exact Hb | reflexivity]) eq_refl). rewrite <- EA, <- EC.
            destruct Hown as [HL' | HQ'].
            -- left. pose proof (live_chunk bt st Lc FF W p' n' HL' HP') as G'. cbn zeta in G'. destruct G' as (_ & _ & G3 & _). exact G3.
            -- right; left. pose proof (quar_chunk bt st Lc FF W (p' - 16) n' HQ' HP') as G'. cbn zeta in G'. replace (p' - 16 + 16) with p' in G' by lia. destruct G' as (_ & _ & G3 & _). exact G3.
        + (* [comment removed for export] *)
          apply (CHKfree (blk_class n') (prim_alloc_beg p' n') HC' CV'); [intros (HP2 & _); rewrite HP in HP2; discriminate HP2 | | lia].
          intros [EC EA]. destruct (WR1 BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _). destruct PARTB as (_ & _ & _ & _ & _ & _ & _ & NBL & _).
          apply (NBL (ba_addr b) ltac:(exists b; split; [exact Hb | reflexivity]) eq_refl). rewrite <- EA, <- EC.
          destruct Hown as [HL' | HQ'].
          -- left. pose proof (live_chunk bt st Lc FF W p' n' HL' HP') as G'. cbn zeta in G'. destruct G' as (_ & _ & G3 & _). exact G3.
          -- right; left. pose proof (quar_chunk bt st Lc FF W (p' - 16) n' HQ' HP') as G'. cbn zeta in G'. replace (p' - 16 + 16) with p' in G' by lia. destruct G' as (_ & _ & G3 & _). exact G3.
      - (* [comment removed for export] *)
        destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        destruct LOC as [(HP & Y1 & Y2 & Y3 & CV & HC & LIV & RR) | (HP & sc & Hs & Eu & En & Y1 & Y2 & Y3 & Y4 & Y5)].
        + apply (DYNfree _ _ (sec_dyn st sc' Hs')); [| ulia | exact Hr]. intros sc2 Hs2 Eu2 En2 E.
          pose proof (prim_block_in_space bt st Lc FF p n W Hin HP) as [B1 B2].
          destruct (sec_facts bt st Lc FF W sc2 Hs2) as (B1' & B2' & B3' & B4' & B5' & B6' & _). rewrite Eu2, En2 in *.
          destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc2 Hs2)); (first [clear - H1 B6' Y1 RZ PL3 B5' Y3 Y2 | idtac]; ulia).
        + destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D].
          * (* [comment removed for export] *)
            assert (p' = p) by congruence. subst p'.
            pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (sec_dyn st sc Hs)) as DT. hnf in DT. cbn in DT.
            destruct (carved_range bt st Lc FF W BATCHCLASS (ba_addr b) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVB) as (D1 & D2 & _). change (csize BATCHCLASS) with 8192 in D2.
            destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((SD1 & SD1' & SD3 & SD4 & SD5) & _).
            destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); destruct SD5; apply AGZ; (first [clear - Hr Z1 Eu PL3 PL2 NI H3 Y2 BB1 SPH R6a DT H2 BB2 | idtac]; ulia).
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
             change (a_tq st') with (tq' ++ [b']). change (a_cinit st') with (a_cinit st). change (a_cache st') with (a_cache st).
             assert (AGT : forall i, ((T <= i < T + T_QC + 24 \/ T + T_QC + 32 <= i < T + 2800 \/ T + 3168 <= i < T + PG) \/ (bt_tctx bt <= i < bt_tctx bt + 160)) ->
                          0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros i Hi Hr. destruct Hi as [Hi | Hi].
               - apply AGF; [| exact Hr]. intros Hf. unfold foot_quar_append, sh_lo, sh_hi in Hf. unfold T_QC in *.
                 destruct BL as [BL1 BL2]. unfold cnt in Hf.
                 destruct Hf as [Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]].
                 1-2: destruct (BLKZ i ltac:(am_tauto)) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]];
                      [ destruct LOC as [(_ & W1 & W2 & W3 & _) | (HP' & _)]; [clear -Zc Hi W1 W3 TPG X1 X2 RZ; (first [clear - Zc Hi TPG W3 W1 | idtac]; Zlia) | rewrite HP in HP'; discriminate HP']
                      | pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (sec_dyn st sc Hs)) as DT; hnf in DT; cbn in DT; clear -Zc Hi DT X1 X2; (first [clear - DT Zc Hi | idtac]; Zlia) ].
                 all: clear -Z Hi X1 X2 TPG TD5 PL1 PL2 BB1 BB2 BL1 BL2 X14 X15; (first [clear - Z Hi PL2 PL1 TD5 TPG BB2 BB1 BL2 X2 | idtac]; Zlia).
               - apply (FIXfree _ _ INC); ulia. }
             unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
             split; [frZ AGT T1|]. split; [frZ AGT T2|]. split; [frZ AGT T3|]. split; [frB AGT T4|]. split; [frZ AGT T5|]. split; [frB AGT T6|].
             split. { (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end). rewrite Htq in TL1, TL2, TL3. rewrite !length_app in *. cbn [length] in *.
                      split; [frZ AGT TL1|].
                      split. { destruct tq' as [|b0 r]; cbn [app] in *; [cbn in TL2 |- *; frZ AGT TL2 | frZ AGT TL2]. }
                      split. { rewrite rev_app_distr in *. cbn [rev app] in *. unfold b' at 1. (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr] in G in change_no_check G' end). frZ AGT TL3. }
                      rewrite q_bytes_app. (lazymatch goal with |- ?G => let G' := eval cbn [q_bytes fold_right] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold b', ba_bytes in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end). rewrite fold_items_app. (lazymatch goal with |- ?G => let G' := eval cbn [fold_right snd] in G in change_no_check G' end).
                      rewrite Htq, q_bytes_app in CQB. cbn [q_bytes fold_right] in CQB. unfold ba_bytes in CQB.
                      replace (q_bytes tq' + (BATCHSZ + (fold_right (fun it acc => snd it + acc) 0 (ba_items b) + (n + 0)) + 0))
                        with (q_bytes tq' + (BATCHSZ + fold_right (fun it acc => snd it + acc) 0 (ba_items b) + 0) + n) by lia. exact CQB. }
             split. { intros c' Hc'. pose proof (cache_len bt st Lc FF W c' Hc') as CL'.
                      eapply rep_pclass_frame; [exact (TP c' Hc') | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | exact CL' |].
                      (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). intros i Hi Hr. apply AGT; [| exact Hr]. left. clear -Hi Hc'. lia. }
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
    assert (BA : forall b0 i, In b0 (a_tq st ++ a_gq st) -> b0 <> b -> foot_batch b0 i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros b0 i Hb0 NEb Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b0 Hb0) as (CVb & BLb & BL2 & BL3).
      apply (CHKfree BATCHCLASS (ba_addr b0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb); [| | change (csize BATCHCLASS) with 8192; ulia].
      - intros (HP & EC & EA). destruct LOC as [(_ & _ & _ & _ & _ & _ & LIV & _) | (HP' & _)]; [| rewrite HP in HP'; discriminate HP'].
        destruct (WR1 BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _). destruct PARTB as (_ & _ & _ & _ & _ & _ & _ & NBL & _).
        apply (NBL (ba_addr b0) ltac:(exists b0; split; [exact Hb0 | reflexivity]) eq_refl). left. rewrite EC, EA. exact LIV.
      - intros [_ EA]. apply NEb. apply (NoDup_map_inj ba_addr (a_tq st ++ a_gq st) b0 b WQ5 Hb0 Hb EA). }
    split. { change (a_tq st') with (tq' ++ [b']). intros i b0 Hb0.
             assert (NDtq : List.NoDup (map ba_addr (tq' ++ [b]))) by (rewrite <- Htq; rewrite map_app in WQ5; exact (NoDup_app_remove_r _ _ WQ5)).
             destruct (Nat.lt_ge_cases i (length tq')) as [LT | GE].
             - (* [comment removed for export] *)
               rewrite nth_error_app1 in Hb0 by exact LT.
               assert (Hb0' : nth_error (a_tq st) i = Some b0) by (rewrite Htq, nth_error_app1 by exact LT; exact Hb0).
               assert (Hin0 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; left; exact (nth_error_In _ _ Hb0')).
               assert (NEb : b0 <> b).
               { intros ->. rewrite map_app in NDtq. cbn [map] in NDtq. apply (NoDup_remove_2 _ [] _ NDtq). rewrite app_nil_r. apply in_map. exact (nth_error_In _ _ Hb0). }
               destruct (BR b0 Hin0) as (Q1 & Q2 & Q3). destruct (R5 i b0 Hb0') as (C1 & C2 & C3 & C4 & CW).
               assert (AGb : forall j, ba_addr b0 <= j < ba_addr b0 + 24 + 8 * Z.of_nat (length (ba_items b0)) -> 0 <= j < 2 ^ 64 -> M' (Z_to_bv 64 j) = M (Z_to_bv 64 j))
                 by (intros j Hj Hrj; exact (BA b0 j Hin0 NEb Hj Hrj)).
               unfold BATCHSZ, BATCHCAP in Q2, Q3.
               split. { replace (nth_error (tq' ++ [b']) (S i)) with (match nth_error (a_tq st) (S i) with Some bb => Some (if Nat.eqb (S i) (length tq') then b' else bb) | None => None end).
                        - destruct (nth_error (a_tq st) (S i)) as [bb|] eqn:E; [| frZ AGb C1].
                          destruct (Nat.eqb_spec (S i) (length tq')) as [E2|NE2]; [| frZ AGb C1].
                          rewrite Htq, E2, nth_error_app2, Nat.sub_diag in E by lia. cbn in E. injection E as <-. (lazymatch goal with |- ?G => let G' := eval unfold b' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr] in G in change_no_check G' end). frZ AGb C1.
                        - rewrite Htq. destruct (Nat.eqb_spec (S i) (length tq')) as [E2|NE2].
                          + rewrite E2, !nth_error_app2, Nat.sub_diag by lia. reflexivity.
                          + assert (S i < length tq')%nat by lia. rewrite !nth_error_app1 by lia. destruct (nth_error tq' (S i)); reflexivity. }
               split; [frZ AGb C2|]. split; [frZ AGb C3|]. split; [| frW DEF CW].
               intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Hl. pose proof (C4 j mn Hj) as CC4. frZ AGb CC4.
             - (* [comment removed for export] *)
               rewrite nth_error_app2 in Hb0 by exact GE. destruct (i - length tq')%nat as [|k] eqn:EK; [| destruct k; discriminate Hb0]. cbn in Hb0. injection Hb0 as <-.
               assert (EI : i = length tq') by lia. subst i.
               assert (HbN : nth_error (a_tq st) (length tq') = Some b) by (rewrite Htq, nth_error_app2, Nat.sub_diag by lia; reflexivity).
               destruct (R5 _ b HbN) as (C1 & C2 & C3 & C4 & CW). destruct BL as [BL1 BL2].
               assert (AGb : forall j, (ba_addr b <= j < ba_addr b + 8 \/ ba_addr b + 24 <= j < ba_addr b + 24 + 8 * cnt) -> 0 <= j < 2 ^ 64 -> M' (Z_to_bv 64 j) = M (Z_to_bv 64 j)).
               { intros j Hj Hrj. apply AGF; [| exact Hrj]. intros Hf. unfold foot_quar_append, sh_lo, sh_hi, T_QC in Hf. unfold cnt in *.
                 destruct Hf as [Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]].
                 1-2: destruct (BLKZ j ltac:(am_tauto)) as [_ [(HP & Zc) | (HP & sc & Hs & Eu & En & Zc)]];
                      [ destruct LOC as [(_ & V1 & V2 & V3 & CV & HC & LIV & RR) | (HP' & _)]; [| rewrite HP in HP'; discriminate HP'];
                        destruct (chunk_cases bt st Lc FF W BATCHCLASS (ba_addr b) (blk_class n) (p - rz n) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) HC CVB CV) as [[EC2 EA2] | D2];
                        [ destruct (WR1 BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _); destruct PARTB as (_ & _ & _ & _ & _ & _ & _ & NBL & _);
                          exfalso; apply (NBL (ba_addr b) ltac:(exists b; split; [exact Hb | reflexivity]) eq_refl); left; rewrite EC2, EA2; exact LIV
                        | change (csize BATCHCLASS) with 8192 in D2; clear -Z Hj D2 V2 RZ RR RG2 BL1 BL2; (first [clear - D2 Z Hj RR BL2 RG2 RZ | idtac]; Zlia) ]
                      | destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _); destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [DS|DS]; clear -Z Hj Zc DS A1 A2 BB1 BB2 CB1 CB2 X14 X15 BL1 BL2; (first [clear - DS Zc Hj BB1 BB2 BL2 | idtac]; Zlia) ].
                 all: clear -Z Hj BB1 BB2 BL1 BL2 X1 X2 X14 X15 TPG TD5 SBH PL1 PL2; (first [clear - Z Hj BB1 PL2 SBH TPG BB2 BL2 X15 | idtac]; Zlia). }
               (lazymatch goal with |- ?G => let G' := eval unfold b' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_addr ba_items] in G in change_no_check G' end). rewrite length_app. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end).
               split. { rewrite nth_error_app2, Nat.sub_succ_l, Nat.sub_diag by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite Htq, nth_error_app2 in C1 by lia.
                        replace (S (length tq') - length tq')%nat with 1%nat in C1 by lia. cbn in C1. unfold cnt in *. frZ AGb C1. }
               split; [(lazymatch goal with |- ?G => let G' := eval unfold b' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end); rewrite fold_items_app || idtac; exact CSZ || ((lazymatch goal with |- ?G => let G' := eval unfold ba_bytes in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end); rewrite fold_items_app; (lazymatch goal with |- ?G => let G' := eval cbn [fold_right snd] in G in change_no_check G' end); unfold ba_bytes in CSZ; replace (BATCHSZ + (fold_right (fun it acc => snd it + acc) 0 (ba_items b) + (n + 0))) with (BATCHSZ + fold_right (fun it acc => snd it + acc) 0 (ba_items b) + n) by lia; exact CSZ)|].
               split; [rewrite Nat2Z.inj_add; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); unfold cnt in CCNT; exact CCNT|].
               split; [| frW DEF CW].
               intros j mn Hj. destruct (Nat.lt_ge_cases j (length (ba_items b))) as [LTj | GEj].
               + rewrite nth_error_app1 in Hj by exact LTj. pose proof (C4 j mn Hj) as CC4. unfold cnt in *. frZ AGb CC4.
               + rewrite nth_error_app2 in Hj by exact GEj. destruct (j - length (ba_items b))%nat as [|k2] eqn:EK2; [| destruct k2; discriminate Hj]. cbn in Hj. injection Hj as <-.
                 assert (EJ : j = length (ba_items b)) by lia. subst j. (lazymatch goal with |- ?G => let G' := eval cbn [fst] in G in change_no_check G' end). unfold cnt in CIT. exact CIT. }
    (* [comment removed for export] *)
    split. { change (a_gq st') with (a_gq st). eapply rep_batches_frame; [exact DEF | exact R6 | intros b0 Hb0; apply BR; apply in_app_iff; right; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; right; exact Hb0 | | exact Hi | exact Hr].
             intros ->. rewrite Htq, map_app, map_app in WQ5. cbn [map] in WQ5. rewrite <- app_assoc in WQ5. cbn in WQ5.
             apply (NoDup_remove_2 _ _ _ WQ5). apply in_app_iff. right. apply in_map. exact Hb0. }
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply AGZ; try ulia.
               + intros Hbk. destruct (BLKZ i Hbk) as [_ [(HP & Zc) | (HP & sc2 & Hs2 & Eu2 & En2 & Zc)]].
                 * destruct LOC as [(_ & Z1 & Z2 & Z3 & _) | (HP' & _)]; [| rewrite HP in HP'; discriminate HP']. destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); (first [clear - H1 Hbk A7 A6 A5 Hi Z1 RZ Z3 Z2 PL3 | idtac]; ulia).
                 * destruct (sec_cases bt st Lc FF W sc sc2 Hs Hs2) as [<- | D]; ulia.
               + intros HB2. destruct (carved_range bt st Lc FF W BATCHCLASS (ba_addr b) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVB) as (D1 & D2 & _). change (csize BATCHCLASS) with 8192 in D2. destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
               + intros HT. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (sec_dyn st sc Hs)) as DT. hnf in DT. cbn in DT. ulia.
               + destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((SD1 & SD1' & SD3 & SD4 & SD5) & _). intros HB.
                 clear -Hi HB SD5 A1 A2 A3 A4 A5 A6 A7. Zlia. }
    (* [comment removed for export] *)
    split. { destruct R8 as [HLh HQh]. split.
             - intros p' n' Hin'. apply INL in Hin'. destruct Hin' as [Hin' NE'].
               destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n').
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | ulia | ulia |]. intros i Hi Hr. apply (HDRfree p' n' i (or_introl Hin') Hi); [| exact Hr].
               intros ->. (* [comment removed for export] *)
               destruct (hdr_zone bt st Lc FF W p' n' (p - 16) (or_introl Hin') Hi) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')].
               + destruct LOC as [(HP & V1 & V2 & V3 & CV & HC & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                 * destruct (chunk_cases bt st Lc FF W (blk_class n') (prim_alloc_beg p' n') (blk_class n) (p - rz n) HC' HC CV' CV) as [[EC EA] | D]; [| unfold prim_alloc_beg in *; ulia].
                   pose proof (rz_unif n n' ltac:(lia) N1' HP HP' (eq_sym EC)) as ER. unfold prim_alloc_beg in EA.
                   assert (p' = p) by (clear -EA ER; lia). subst p'. destruct (Z.eq_dec n' n) as [-> | NE2]; [exact (NE' eq_refl)|].
                   destruct (LV3 p n' p n Hin' Hin ltac:(clear -NE2; congruence)) as [OV|OV]; clear -OV N1' PL3; lia.
                 * pose proof (carved_range bt st Lc FF W _ _ HC' CV') as (D1 & D2 & D3 & D4 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); unfold prim_alloc_beg in *; ulia.
               + destruct (sec_facts bt st Lc FF W sc' Hs') as (B1 & B2 & B3 & B4 & B5 & B6 & _).
                 destruct LOC as [(HP & V1 & V2 & V3 & CV & HC & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                 * destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc' Hs')); ulia.
                 * destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D]; [| ulia]. apply NE'. f_equal; congruence.
             - intros m n' Hq. apply INQ in Hq. destruct Hq as [E | Hq].
               + (* [comment removed for export] *)
                 injection E as -> ->. replace (p - 16 + 16) with p by lia. destruct (HLh p n Hin) as (H1 & (b1 & Hb1 & H2) & H3 & H4 & HW & H5 & HLC).
                 assert (AGh : forall i, (p - rz n <= i < p - 16 \/ p - 15 <= i < p) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
                 { intros i Hi Hr. apply AGF; [| exact Hr]. intros Hf. unfold foot_quar_append, sh_lo, sh_hi, T_QC in Hf. destruct BL as [BL1 BL2]. unfold cnt in Hf.
                   destruct LOC as [(HP & V1 & V2 & V3 & CV & HC & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                   - destruct (chunk_cases bt st Lc FF W BATCHCLASS (ba_addr b) (blk_class n) (p - rz n) ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) HC CVB CV) as [[EC2 EA2] | D2].
                     + destruct (WR1 BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _). destruct PARTB as (_ & _ & _ & _ & _ & _ & _ & NBL & _).
                       exfalso. apply (NBL (ba_addr b) ltac:(exists b; split; [exact Hb | reflexivity]) eq_refl). left. rewrite EC2, EA2. exact LIV.
                     + change (csize BATCHCLASS) with 8192 in D2. clear -Hf Hi D2 V1 V2 V3 RZ RR RG2 BL1 HBC BB1 BB2 X1 X2 X14 X15 SBH TD5 PL1 PL2 PL3 TPG.
                       try ceil; unfold AS_HEAPLO, AS_LO, SB, PG, KSPACE, BATCHSZ, BATCHCAP in *. destruct Hf as [Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]]; dsj; Z.div_mod_to_equations; (first [clear - Z H2 H10 H9 V1 RZ PL3 SBH H1 V2 HBC H3 V3 PL2 | idtac]; lia).
                   - destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (sec_dyn st sc Hs)) as DT. hnf in DT. cbn in DT.
                     destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((SD1 & SD1' & SD3 & SD4 & SD5) & _).
                     destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [DS|DS]; clear -Hf Hi DT DS A1 A2 V1 V2 V3 BB1 BB2 X1 X2 X14 X15 SD5 TD5 RZ BL1 HBC PL1 PL2 PL3;
                       try ceil; unfold AS_HEAPLO, AS_LO, SB, PG, KSPACE, BATCHSZ, BATCHCAP in *; destruct Hf as [Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]]; dsj; Z.div_mod_to_equations; (first [clear - Z H3 H5 H4 H1 V2 PL3 H10 H9 V1 RZ DS BB1 H2 PL2 X14 BB2 HBC | idtac]; lia). }
                 split.
                 * (lazymatch goal with |- ?G => let G' := eval unfold rep_hdr in G in change_no_check G' end). split; [exact ST3|]. split; [exists b1; split; [exact Hb1 | frB AGh H2]|]. split; [frZ AGh H3|]. split; [frZ AGh H4|]. split; [frW DEF HW|]. split; [frZ AGh H5|].
                   intros Hrz. pose proof (rz_cases n) as RZC. destruct (HLC Hrz) as [L1' L2']. split; [frZ AGh L1' | frZ AGh L2'].
                 * destruct (R15 p n Hin) as [W1 _]. destruct LOC as [(HP & V1 & V2 & V3 & CV & HC & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                   -- destruct (R4 _ HC) as [_ (_ & _ & F3)]. destruct (carved_range bt st Lc FF W _ _ HC CV) as (D1 & D2 & _).
                      pose proof (region_facts bt st Lc FF W _ HC) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3' & _).
                      eapply writableZ_sub; [frW DEF F3 | lia | lia].
                   -- destruct (R7 _ _ ltac:(destruct (In_nth_error _ _ Hs) as [k Hk]; exact Hk)) as (_ & _ & _ & _ & SW) || idtac.
                      destruct (In_nth_error _ _ Hs) as [k Hk]. destruct (R7 k sc Hk) as (_ & _ & _ & _ & SW). eapply writableZ_sub; [frW DEF SW | ulia | lia].
               + (* [comment removed for export] *)
                 destruct (HQh m n' Hq) as [Hh HW]. split; [| frW DEF HW].
                 destruct (quar_item_range bt st Lc FF W m n' Hq) as (A1 & A2 & A3). pose proof (rz_range n').
                 eapply rep_hdr_frame; [exact DEF | exact Hh | ulia | ulia |]. intros i Hi Hr.
                 apply (HDRfree (m + 16) n' i); [right; replace (m + 16 - 16) with m by lia; exact Hq | exact Hi | | exact Hr].
                 intros ->. (* [comment removed for export] *)
                 destruct (hdr_zone bt st Lc FF W (m + 16) n' (p - 16) ltac:(right; replace (m + 16 - 16) with m by lia; exact Hq) Hi)
                   as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')].
                 * destruct LOC as [(HP & V1 & V2 & V3 & CV & HC & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                   -- destruct (chunk_cases bt st Lc FF W (blk_class n') (prim_alloc_beg (m + 16) n') (blk_class n) (p - rz n) HC' HC CV' CV) as [[EC EA] | D]; [| unfold prim_alloc_beg in *; ulia].
                      destruct (WR1 _ HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK). destruct PART as (_ & LQ & _).
                      apply (LQ (p - rz n)). split; [exact LIV|]. rewrite <- EC, <- EA.
                      pose proof (quar_chunk bt st Lc FF W m n' Hq HP') as G'. cbn zeta in G'. destruct G' as (_ & _ & G3 & _). exact G3.
                   -- pose proof (carved_range bt st Lc FF W _ _ HC' CV') as (D1 & D2 & D3 & D4 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); unfold prim_alloc_beg in *; ulia.
                 * destruct (sec_facts bt st Lc FF W sc' Hs') as (B1 & B2 & B3 & B4 & B5 & B6 & _).
                   destruct LOC as [(HP & V1 & V2 & V3 & CV & HC & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                   -- destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc' Hs')); ulia.
                   -- destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D]; [| ulia].
                      apply (sec_live_not_quar bt st Lc FF W sc Hs); [rewrite Eu, En; exact Hin|]. rewrite Eu, En. replace (p - 16) with m by lia.
                      replace n' with n in Hq by congruence. exact Hq. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact R9 | ulia | ulia | ulia | ulia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). ulia.
             - intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) Hr).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXfree _ _ INN); [ulia | ulia | rewrite Eb; lia | exact Hr].
               + apply (DYNfree _ _ (node_dyn st bb Hnb)); [| lia | exact Hr]. intros sc Hs _ _ E.
                 destruct (sec_vs_node bt st Lc FF W sc bb Hs Hnb); destruct (sec_facts bt st Lc FF W sc Hs) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & _); injection E; intros; ulia. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2].
             eapply rep_fake_frame; [exact DEF | exact R10 | ulia | ulia | ulia | ulia | ulia | ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXfree _ _ INFS); ulia.
               + exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) Hr).
               + apply (FIXfreeT _ _ (dtls_member bt st Lc FF W) (dtls_vs_thread bt st Lc FF W)); ulia.
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXfree _ _ INFS); ulia. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact R11 | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. exact (IMGK i (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) Hr). }
    (* [comment removed for export] *)
    split. { destruct R12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
             change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st).
             assert (EXQ : forall g, existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? g) && (g <? (fst mn + 16 + snd mn + 7) / 8)) (quar st')
                               = ((p / 8 <=? g) && (g <? (p + n + 7) / 8)) || existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? g) && (g <? (fst mn + 16 + snd mn + 7) / 8)) (quar st)).
             { intros g. rewrite QE, QE0, existsb_app_mid. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). replace (p - 16 + 16) with p by lia. rewrite <- app_assoc. reflexivity. }
             (* [comment removed for export] *)
             assert (AGS : forall i, SB <= i < SB + CEIL / 8 -> ~ (SB + p / 8 <= i < SB + (p + n + 7) / 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros i Hi NU. apply AGF; [| clear -Hi; Zlia]. intros Hf. unfold foot_quar_append, sh_lo, sh_hi, T_QC in Hf. destruct BL as [BL1 BL2]. unfold cnt in Hf.
               destruct Hf as [Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]].
               1-2: destruct (BLKZ i ltac:(am_tauto)) as [(_ & _ & NB) _]; apply NB; (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end); clear -Hi; (first [clear - Hi | idtac]; Zlia).
               all: clear -Z Hi NU PL1 PL2 BB1 BB2 X1 X14 X15 TD5 SBH CB1 CB2 BL1 BL2; Zlia. }
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
                      destruct LOC as [(HP & V1 & V2 & V3 & CV & HC & LIV & RR) | (HP & sc & Hs & Eu & En & V1 & V2 & V3 & V4 & V5)].
                      - destruct (carved_range bt st Lc FF W _ _ HC CV) as (D1 & D2 & _). pose proof (region_facts bt st Lc FF W _ HC) as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
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
                      destruct LOC as [(HP & V1 & V2 & V3 & CV & HC & LIV & RR) | (HP & sc2 & Hs2 & Eu & En & V1 & V2 & V3 & V4 & V5)].
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
                        destruct LOC as [(HP & V1 & V2 & V3 & CV & HC & LIV & RR) | (HP & sc2 & Hs2 & Eu & En & V1 & V2 & V3 & V4 & V5)].
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

End Pf.
