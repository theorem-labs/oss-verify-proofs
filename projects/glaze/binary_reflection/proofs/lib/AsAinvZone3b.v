(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvFacts3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Facts.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Variables (st : ast) (Lc FF : list (Z * Z)).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  (* [comment removed for export] *)
  Lemma fixed_range : forall lo hi, In (lo, hi) (bt_fixed bt) ->
    dyn_ok IA lo hi /\ lo < hi /\ lo mod PG = 0 /\ hi mod PG = 0.
  Proof. intros lo hi Hin. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _). exact (RNG lo hi (all_ranges_fixed bt st _ Hin)). Qed.

  (* [comment removed for export] *)
  Lemma fixed_members :
    In (bt_resv6 bt, bt_resv6 bt + bt_resv6_len bt) (bt_fixed bt) /\ In (bt_ptrarr bt, bt_ptrarr bt + 2 ^ 23) (bt_fixed bt)
    /\ In (bt_fs bt, bt_fs bt + FAKE_SIZE) (bt_fixed bt) /\ In (T, T + PG) (bt_fixed bt)
    /\ In (bt_nodes0 bt, bt_nodes0 bt + 2 ^ 20) (bt_fixed bt) /\ In (bt_store0 bt, bt_store0 bt + 2 ^ 23) (bt_fixed bt)
    /\ In (bt_tctx bt, bt_tctx bt + 0x10000) (bt_fixed bt).
  Proof.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & IN6 & _ & _ & IN8 & INFS & INT & INN & INS & INC & _) & _).
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma thread_page_facts :
    dyn_ok IA T (T + PG) /\ T mod PG = 0 /\ 0 < T /\ T + PG <= CEIL
    /\ (T + PG <= ia_img_lo IA \/ ia_img_hi IA <= T) /\ (T + PG <= AS_LO \/ AS_HEAPLO <= T).
  Proof.
    destruct fixed_members as (_ & _ & _ & INT & _). destruct (fixed_range _ _ INT) as ((D1 & D2 & D3 & D4 & D5) & L & M1 & M2).
    repeat split; try assumption.
  Qed.

  (* [comment removed for export] *)
  Definition img_lo_small : Prop := ia_img_lo IA <= 0x10000.


  (* [comment removed for export] *)
  Lemma thread_dyn :
    0 < T /\ T + PG <= CEIL /\ (T + PG <= ia_img_lo IA \/ ia_img_hi IA <= T) /\ (T + PG <= AS_LO \/ AS_HEAPLO <= T) /\ T mod PG = 0
    /\ 0 < bt_tctx bt /\ bt_tctx bt + 0x10000 <= CEIL /\ (bt_tctx bt + 0x10000 <= ia_img_lo IA \/ ia_img_hi IA <= bt_tctx bt)
    /\ (bt_tctx bt + 0x10000 <= AS_LO \/ AS_HEAPLO <= bt_tctx bt) /\ bt_tctx bt mod PG = 0
    /\ (bt_tctx bt + 0x10000 <= T \/ T + PG <= bt_tctx bt)
    /\ 0 <= SBEG /\ SBEG + KSPACE + PG <= CEIL /\ AS_HEAPLO <= SBEG /\ SBEG mod 2 ^ 16 = 0.
  Proof.
    destruct fixed_members as (IN6 & _ & _ & INT & _ & _ & INC).
    destruct (fixed_range _ _ INT) as ((D1 & D2 & D3 & D4 & D5) & L & M1 & M2).
    destruct (fixed_range _ _ INC) as ((E1 & E2 & E3 & E4 & E5) & L' & N1 & N2).
    pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INC) (all_ranges_fixed bt st _ INT) ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as D.
    hnf in D. cbn in D.
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X14 & X15 & X16).
    repeat split; try assumption; lia.
  Qed.

  Lemma ptrarr_facts : dyn_ok IA (bt_ptrarr bt) (bt_ptrarr bt + 2 ^ 23) /\ bt_ptrarr bt mod PG = 0.
  Proof. destruct fixed_members as (_ & IN8 & _). destruct (fixed_range _ _ IN8) as (D & _ & M & _). exact (conj D M). Qed.
  Lemma nodes0_facts : dyn_ok IA (bt_nodes0 bt) (bt_nodes0 bt + 2 ^ 20) /\ bt_nodes0 bt mod PG = 0.
  Proof. destruct fixed_members as (_ & _ & _ & _ & INN & _). destruct (fixed_range _ _ INN) as (D & _ & M & _). exact (conj D M). Qed.
  Lemma store0_facts : dyn_ok IA (bt_store0 bt) (bt_store0 bt + 2 ^ 23) /\ bt_store0 bt mod PG = 0.
  Proof. destruct fixed_members as (_ & _ & _ & _ & _ & INS & _). destruct (fixed_range _ _ INS) as (D & _ & M & _). exact (conj D M). Qed.
  Lemma resv6_range : dyn_ok IA (bt_resv6 bt) (bt_resv6 bt + bt_resv6_len bt) /\ bt_resv6 bt mod PG = 0
    /\ bt_resv6 bt <= SBEG /\ SBEG + KSPACE + PG <= bt_resv6 bt + bt_resv6_len bt /\ AS_HEAPLO <= bt_resv6 bt /\ ia_img_hi IA <= bt_resv6 bt.
  Proof.
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH).
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    repeat split; try assumption. ulia.
  Qed.

  (* [comment removed for export] *)
  Lemma fixed_sep : forall lo hi lo' hi', In (lo, hi) (bt_fixed bt) -> In (lo', hi') (bt_fixed bt) -> (lo, hi) <> (lo', hi') ->
    hi <= lo' \/ hi' <= lo.
  Proof.
    intros lo hi lo' hi' H1 H2 NE.
    pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ H1) (all_ranges_fixed bt st _ H2) NE) as D. hnf in D. cbn in D. exact D.
  Qed.
  Lemma fixed_dyn_sep : forall lo hi lo' hi', In (lo, hi) (bt_fixed bt) -> In (lo', hi') (dyn_ranges st) -> hi <= lo' \/ hi' <= lo.
  Proof.
    intros lo hi lo' hi' H1 H2. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W H1 H2) as D. hnf in D. cbn in D. exact D.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_above_img : img_lo_small -> forall p n, In (p, n) Lc -> ia_img_hi IA <= p - 16.
  Proof.
    intros IL p n Hin. unfold img_lo_small in IL. pose proof (img_lits bt st Lc FF W) as [I1 I2].
    destruct (is_primary n) eqn:HP.
    - pose proof (prim_block_in_space bt st Lc FF p n W Hin HP) as [B1 B2]. pose proof (rz_range n).
      destruct resv6_range as (_ & _ & R1 & _ & R3 & R4). ulia.
    - destruct (live_sec bt st Lc FF W p n Hin HP) as (sc & Hs & Eu & En).
      destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
      destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((D1 & D2 & D3 & D4 & D5) & _).
      unfold sc_mapsz in *. pose proof (sec_map_size_ge (sc_n sc) ltac:(lia)) as (G1 & G2 & G3). pose proof (rz_range (sc_n sc)).
      clear -IL I1 I2 A1 A5 D4 G1 H A7 Eu. unfold sc_user, sec_user_off in *. ulia.
  Qed.

End Facts.
End AsAinvFacts3.
Module AsAinvZone3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b AsAinvFacts3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Zone.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Variables (st : ast) (Lc FF : list (Z * Z)).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_QC, T_PC, PC_SZ, T_UNW, NMAX in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Generic.
    Variable Zn : Z -> Prop.
    Hypothesis ZIMG : forall i, Zn i -> ia_img_lo IA <= i < ia_img_hi IA -> False.
    Hypothesis ZFIX : forall lo hi i, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi - lo <> PG -> Zn i -> lo <= i < hi -> False.
    Hypothesis ZTHR : forall i, Zn i -> thread_cells bt i -> False.
    Hypothesis ZDYN : forall lo hi i, In (lo, hi) (dyn_ranges st) -> Zn i -> lo <= i < hi -> False.
    Hypothesis ZRI : forall c0 i, 1 <= c0 <= 30 -> Zn i -> reginfo bt c0 <= i < reginfo bt c0 + 72 -> ~ (reginfo bt c0 + 64 <= i < reginfo bt c0 + 68) -> False.
    Hypothesis ZFA : forall c0 i, 1 <= c0 <= 30 -> Zn i -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + r_mapped_fa (a_reg st c0) -> False.
    Hypothesis ZCV : forall c0 a i, 1 <= c0 <= 30 -> carved bt st c0 a -> Zn i -> a <= i < a + csize c0 -> False.
    Hypothesis ZSHR : forall c0 i, 1 <= c0 <= 30 -> Zn i ->
      (sh_lo (region_beg SBEG c0) <= i < SB + (region_beg SBEG c0 + r_mapped_user (a_reg st c0)) / 8)
      \/ (sh_lo (fa_beg SBEG c0) <= i < SB + (fa_beg SBEG c0 + r_mapped_fa (a_reg st c0)) / 8) -> False.
    Hypothesis ZSHS : forall sc i, In sc (a_sec st) -> Zn i -> sh_lo (sc_map sc) <= i < SB + (sc_map sc + sc_mapsz sc) / 8 -> False.
    (* [comment removed for export] *)
    Hypothesis ZDT : forall i, Zn i -> bt_dtls bt + 24 <= i < bt_dtls bt + 32 -> False.

    Theorem zone_not_cells : forall i, Zn i -> rep_cells bt st Lc FF i -> False.
    Proof.
      intros i Hz HC.
      pose proof W as ((WR1 & WR2) & WC & WQ & (SS1 & SS2 & SS3 & _) & WL & WK & WD & WM & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
      assert (IMGoff : img_kind bt i -> False) by (intros [Hh _]; exact (ZIMG i Hz Hh)).
      unfold rep_cells in HC.
      destruct HC as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]]].
      - exact (IMGoff (img_kinds bt st Lc FF W i (or_introl K))).
      - destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN|NI].
        + apply (ZFIX _ _ i IN8); [ulia | ulia | exact Hz | clear -IN SS1 SS3; lia].
        + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact K | exact NI]))).
      - exact (ZTHR i Hz K).
      - destruct K as (c0 & Hc0 & K). unfold foot_region in K.
        destruct K as [[K1 K2]|K]; [exact (ZRI c0 i Hc0 Hz K1 K2) |].
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _).
        apply (ZFA c0 i Hc0 Hz). clear -K Q7. lia.
      - destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & B1 & B2).
        apply (ZCV BATCHCLASS (ba_addr b) i ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CVb Hz). change (csize BATCHCLASS) with 8192. unfold BATCHCAP in *. clear -K BL. lia.
      - destruct K as (sc & Hs' & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (ZDYN _ _ i (sec_dyn st sc Hs') Hz). pose proof (rz_range (sc_n sc)). clear -K A5 A6 A7 H. ulia.
      - destruct K as (p & n & Hown & K).
        destruct (hdr_zone bt st Lc FF W p n i Hown K) as [(HP & Hi & S1 & S2 & CV & Hc1 & N1 & S3) | (HP & sc & Hsc & Eu & En & Hi & N1)].
        + apply (ZCV (blk_class n) (prim_alloc_beg p n) i Hc1 CV Hz). clear -Hi S2 N1. lia.
        + destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
          apply (ZDYN _ _ i (sec_dyn st sc Hsc) Hz). rewrite Eu, En in *. clear -Hi A5 A6 N1. ulia.
      - exact (IMGoff (img_kinds bt st Lc FF W i ltac:(right; right; left; exact K))).
      - destruct K as (id & Hid & K). unfold foot_node in K. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
        pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
        destruct HIn as [Eb | Hnb]; [apply (ZFIX _ _ i INN); [ulia | ulia | exact Hz | rewrite Eb; lia] | apply (ZDYN _ _ i (node_dyn st bb Hnb) Hz); lia].
      - unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
        1-3: apply (ZFIX _ _ i INFS); [ulia | ulia | exact Hz | ulia].
        + exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact K))).
        + exact (ZDT i Hz K).
      - destruct K as (f & k & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _).
        apply (ZFIX _ _ i INFS); [ulia | ulia | exact Hz | ulia].
      - exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact K))).
      - destruct K as (c0 & Hc0 & K). unfold foot_shreg in K. apply (ZSHR c0 i Hc0 Hz). destruct K as [[K _]|K]; [left; exact K | right; exact K].
      - destruct K as (sc & Hs' & K). unfold foot_shsec in K. destruct K as [K _]. exact (ZSHS sc i Hs' Hz K).
      - exact (IMGoff (img_kinds bt st Lc FF W i ltac:(do 5 right; exact K))).
    Qed.
  End Generic.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma band_facts : ia_img_hi IA <= AS_LO /\ 0 <= ia_img_lo IA /\ AS_HEAPLO <= SBEG /\ SBEG + KSPACE + PG <= CEIL /\ 0 < SBEG
                     /\ SB + CEIL / 8 < AS_HEAPLO /\ AS_HEAPLO < CEIL.
  Proof.
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    destruct (space_facts bt st Lc FF W) as (_ & _ & SP7 & _ & SPH).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X14 & X15 & _).
    repeat split; try assumption; try ulia. clear -I1 I2 SP7 SPH X14 X15. Zlia.
  Qed.

  (* [comment removed for export] *)
  Lemma shreg_in_band : forall c0 i, 1 <= c0 <= 30 ->
    (sh_lo (region_beg SBEG c0) <= i < SB + (region_beg SBEG c0 + r_mapped_user (a_reg st c0)) / 8)
    \/ (sh_lo (fa_beg SBEG c0) <= i < SB + (fa_beg SBEG c0 + r_mapped_fa (a_reg st c0)) / 8) -> in_band i.
  Proof.
    intros c0 i Hc0 K. pose proof band_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
    unfold in_band, sh_lo in *. clear -K B3 B4 B5 B6 Q1 Q2 Q5 Q6 Q8. Zlia.
  Qed.
  Lemma shsec_in_band : forall sc i, In sc (a_sec st) -> sh_lo (sc_map sc) <= i < SB + (sc_map sc + sc_mapsz sc) / 8 -> in_band i.
  Proof.
    intros sc i Hs K. pose proof band_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). unfold in_band, sh_lo in *. clear -K A1 A2 B6 B7. Zlia.
  Qed.
  (* [comment removed for export] *)
  Lemma thread_cells_where : forall i, thread_cells bt i -> (T <= i < T + 2768 \/ i = T + T_UNW) \/ (bt_tctx bt <= i < bt_tctx bt + 160).
  Proof. intros i K. unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in *. lia. Qed.

  Section Shapes.
    Variable Zn : Z -> Prop.

    (* [comment removed for export] *)
    Section Ceil.
      Hypothesis ZC : forall i, Zn i -> CEIL <= i.
      Lemma ceilz_img : forall i, Zn i -> ia_img_lo IA <= i < ia_img_hi IA -> False.
      Proof. intros i Hz Hi. pose proof band_facts as (B1 & _ & B3 & B4 & _). pose proof (ZC i Hz). clear -Hi B1 B3 B4 H. ulia. Qed.
      Lemma ceilz_fix : forall lo hi i, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi - lo <> PG -> Zn i -> lo <= i < hi -> False.
      Proof. intros lo hi i Hin _ _ Hz Hi. destruct (fixed_range bt st Lc FF W lo hi Hin) as ((_ & _ & D3 & _) & _). pose proof (ZC i Hz). lia. Qed.
      Lemma ceilz_thr : forall i, Zn i -> thread_cells bt i -> False.
      Proof.
        intros i Hz K. pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & _). pose proof (ZC i Hz).
        destruct (thread_cells_where i K); unfold T_UNW, PG in *; lia.
      Qed.
      Lemma ceilz_dyn : forall lo hi i, In (lo, hi) (dyn_ranges st) -> Zn i -> lo <= i < hi -> False.
      Proof.
        intros lo hi i Hin Hz Hi. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
        destruct (RNG lo hi (all_ranges_dyn bt st _ Hin)) as ((_ & _ & D3 & _) & _). pose proof (ZC i Hz). lia.
      Qed.
      Lemma ceilz_ri : forall c0 i, 1 <= c0 <= 30 -> Zn i -> reginfo bt c0 <= i < reginfo bt c0 + 72 -> ~ (reginfo bt c0 + 64 <= i < reginfo bt c0 + 68) -> False.
      Proof.
        intros c0 i Hc0 Hz Hi _. pose proof band_facts as (_ & _ & _ & B4 & _). pose proof (ZC i Hz).
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (_ & _ & _ & _ & _ & _ & _ & _ & Q9 & Q10 & _). lia.
      Qed.
      Lemma ceilz_fa : forall c0 i, 1 <= c0 <= 30 -> Zn i -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + r_mapped_fa (a_reg st c0) -> False.
      Proof.
        intros c0 i Hc0 Hz Hi. pose proof band_facts as (_ & _ & _ & B4 & _). pose proof (ZC i Hz).
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _). ulia.
      Qed.
      Lemma ceilz_cv : forall c0 a i, 1 <= c0 <= 30 -> carved bt st c0 a -> Zn i -> a <= i < a + csize c0 -> False.
      Proof.
        intros c0 a i Hc0 CV Hz Hi. pose proof band_facts as (_ & _ & _ & B4 & _). pose proof (ZC i Hz).
        destruct (carved_range bt st Lc FF W c0 a Hc0 CV) as (_ & _ & _ & C4 & _). ulia.
      Qed.
      Lemma ceilz_shr : forall c0 i, 1 <= c0 <= 30 -> Zn i ->
        (sh_lo (region_beg SBEG c0) <= i < SB + (region_beg SBEG c0 + r_mapped_user (a_reg st c0)) / 8)
        \/ (sh_lo (fa_beg SBEG c0) <= i < SB + (fa_beg SBEG c0 + r_mapped_fa (a_reg st c0)) / 8) -> False.
      Proof. intros c0 i Hc0 Hz K. pose proof (shreg_in_band c0 i Hc0 K) as IB. pose proof band_facts as (_ & _ & _ & _ & _ & _ & B7). pose proof (ZC i Hz). unfold in_band in IB. lia. Qed.
      Lemma ceilz_shs : forall sc i, In sc (a_sec st) -> Zn i -> sh_lo (sc_map sc) <= i < SB + (sc_map sc + sc_mapsz sc) / 8 -> False.
      Proof. intros sc i Hs Hz K. pose proof (shsec_in_band sc i Hs K) as IB. pose proof band_facts as (_ & _ & _ & _ & _ & _ & B7). pose proof (ZC i Hz). unfold in_band in IB. lia. Qed.
      Lemma ceilz_dt : forall i, Zn i -> bt_dtls bt + 24 <= i < bt_dtls bt + 32 -> False.
      Proof. intros i Hz K. destruct (dtls_cell_facts bt st Lc FF W i K) as (_ & D2 & _). pose proof (ZC i Hz). lia. Qed.
      Theorem ceilz_not_cells : forall i, Zn i -> rep_cells bt st Lc FF i -> False.
      Proof. exact (zone_not_cells Zn ceilz_img ceilz_fix ceilz_thr ceilz_dyn ceilz_ri ceilz_fa ceilz_cv ceilz_shr ceilz_shs ceilz_dt). Qed.
    End Ceil.

    (* [comment removed for export] *)
    Section Stats.
      Hypothesis ZT : forall i, Zn i -> T + 2768 <= i < T + 3168.
      Lemma statz_img : forall i, Zn i -> ia_img_lo IA <= i < ia_img_hi IA -> False.
      Proof. intros i Hz Hi. destruct (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & D4 & _). pose proof (ZT i Hz). unfold PG in *. lia. Qed.
      Lemma statz_fix : forall lo hi i, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi - lo <> PG -> Zn i -> lo <= i < hi -> False.
      Proof.
        intros lo hi i Hin _ Hlen Hz Hi. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
        pose proof (fixed_sep bt st Lc FF W _ _ _ _ Hin INT ltac:(intros E; injection E; intros; subst; apply Hlen; lia)) as D.
        pose proof (ZT i Hz). unfold PG in *. lia.
      Qed.
      Lemma statz_thr : forall i, Zn i -> thread_cells bt i -> False.
      Proof.
        intros i Hz K. pose proof (ZT i Hz). destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _ & _ & INC).
        pose proof (fixed_sep bt st Lc FF W _ _ _ _ INC INT ltac:(intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); intros; lia)) as D.
        destruct (thread_cells_where i K); unfold T_UNW, PG in *; lia.
      Qed.
      Lemma statz_dyn : forall lo hi i, In (lo, hi) (dyn_ranges st) -> Zn i -> lo <= i < hi -> False.
      Proof.
        intros lo hi i Hin Hz Hi. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
        pose proof (fixed_dyn_sep bt st Lc FF W _ _ _ _ INT Hin) as D. pose proof (ZT i Hz). unfold PG in *. lia.
      Qed.
      Lemma stats_vs_space : forall i, Zn i -> SBEG <= i < SBEG + KSPACE + PG -> False.
      Proof.
        intros i Hz Hi. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
        destruct (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG, KSPACE in G in change_no_check G' end); lia)); pose proof (ZT i Hz); unfold PG in *; lia.
      Qed.
      Lemma statz_ri : forall c0 i, 1 <= c0 <= 30 -> Zn i -> reginfo bt c0 <= i < reginfo bt c0 + 72 -> ~ (reginfo bt c0 + 64 <= i < reginfo bt c0 + 68) -> False.
      Proof.
        intros c0 i Hc0 Hz Hi _. apply (stats_vs_space i Hz).
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (_ & _ & _ & _ & _ & _ & _ & _ & Q9 & Q10 & _). ulia.
      Qed.
      Lemma statz_fa : forall c0 i, 1 <= c0 <= 30 -> Zn i -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + r_mapped_fa (a_reg st c0) -> False.
      Proof.
        intros c0 i Hc0 Hz Hi. apply (stats_vs_space i Hz).
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _). ulia.
      Qed.
      Lemma statz_cv : forall c0 a i, 1 <= c0 <= 30 -> carved bt st c0 a -> Zn i -> a <= i < a + csize c0 -> False.
      Proof.
        intros c0 a i Hc0 CV Hz Hi. apply (stats_vs_space i Hz). destruct (carved_range bt st Lc FF W c0 a Hc0 CV) as (_ & _ & C3 & C4 & _). ulia.
      Qed.
      Lemma stats_vs_band : forall i, Zn i -> in_band i -> False.
      Proof.
        intros i Hz Hi. destruct (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & D5). pose proof (ZT i Hz). unfold in_band, PG in *. lia.
      Qed.
      Lemma statz_shr : forall c0 i, 1 <= c0 <= 30 -> Zn i ->
        (sh_lo (region_beg SBEG c0) <= i < SB + (region_beg SBEG c0 + r_mapped_user (a_reg st c0)) / 8)
        \/ (sh_lo (fa_beg SBEG c0) <= i < SB + (fa_beg SBEG c0 + r_mapped_fa (a_reg st c0)) / 8) -> False.
      Proof. intros c0 i Hc0 Hz K. exact (stats_vs_band i Hz (shreg_in_band c0 i Hc0 K)). Qed.
      Lemma statz_shs : forall sc i, In sc (a_sec st) -> Zn i -> sh_lo (sc_map sc) <= i < SB + (sc_map sc + sc_mapsz sc) / 8 -> False.
      Proof. intros sc i Hs Hz K. exact (stats_vs_band i Hz (shsec_in_band sc i Hs K)). Qed.
      Lemma statz_dt : forall i, Zn i -> bt_dtls bt + 24 <= i < bt_dtls bt + 32 -> False.
      Proof. intros i Hz K. destruct (dtls_cell_facts bt st Lc FF W i K) as (_ & _ & _ & _ & D5 & _). pose proof (ZT i Hz). apply D5. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia. Qed.
      Theorem statz_not_cells : forall i, Zn i -> rep_cells bt st Lc FF i -> False.
      Proof. exact (zone_not_cells Zn statz_img statz_fix statz_thr statz_dyn statz_ri statz_fa statz_cv statz_shr statz_shs statz_dt). Qed.
    End Stats.

    (* [comment removed for export] *)
    Section RIpage.
      Hypothesis ZP : forall i, Zn i -> SBEG + KSPACE <= i < SBEG + KSPACE + PG.
      Lemma ripz_img : forall i, Zn i -> ia_img_lo IA <= i < ia_img_hi IA -> False.
      Proof. intros i Hz Hi. pose proof band_facts as (B1 & _ & B3 & _). pose proof (ZP i Hz). clear -Hi B1 B3 H. ulia. Qed.
      Lemma ripz_fix : forall lo hi i, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi - lo <> PG -> Zn i -> lo <= i < hi -> False.
      Proof. intros lo hi i Hin Hlen _ Hz Hi. destruct (space_vs_fixed bt st Lc FF W lo hi Hin Hlen); pose proof (ZP i Hz); ulia. Qed.
      Lemma ripz_thr : forall i, Zn i -> thread_cells bt i -> False.
      Proof.
        intros i Hz K. pose proof (ZP i Hz). destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _ & _ & INC).
        destruct (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG, KSPACE in G in change_no_check G' end); lia));
          destruct (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)); destruct (thread_cells_where i K); unfold T_UNW, PG, KSPACE in *; lia.
      Qed.
      Lemma ripz_dyn : forall lo hi i, In (lo, hi) (dyn_ranges st) -> Zn i -> lo <= i < hi -> False.
      Proof. intros lo hi i Hin Hz Hi. destruct (space_vs_dyn bt st Lc FF W lo hi Hin); pose proof (ZP i Hz); ulia. Qed.
      Lemma ripz_fa : forall c0 i, 1 <= c0 <= 30 -> Zn i -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + r_mapped_fa (a_reg st c0) -> False.
      Proof.
        intros c0 i Hc0 Hz Hi. pose proof (ZP i Hz).
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _). ulia.
      Qed.
      Lemma ripz_cv : forall c0 a i, 1 <= c0 <= 30 -> carved bt st c0 a -> Zn i -> a <= i < a + csize c0 -> False.
      Proof. intros c0 a i Hc0 CV Hz Hi. pose proof (ZP i Hz). destruct (carved_range bt st Lc FF W c0 a Hc0 CV) as (_ & _ & C3 & C4 & _). ulia. Qed.
      Lemma ripage_vs_band : forall i, Zn i -> in_band i -> False.
      Proof. intros i Hz Hi. pose proof band_facts as (_ & _ & B3 & _). pose proof (ZP i Hz). unfold in_band in *. ulia. Qed.
      Lemma ripz_shr : forall c0 i, 1 <= c0 <= 30 -> Zn i ->
        (sh_lo (region_beg SBEG c0) <= i < SB + (region_beg SBEG c0 + r_mapped_user (a_reg st c0)) / 8)
        \/ (sh_lo (fa_beg SBEG c0) <= i < SB + (fa_beg SBEG c0 + r_mapped_fa (a_reg st c0)) / 8) -> False.
      Proof. intros c0 i Hc0 Hz K. exact (ripage_vs_band i Hz (shreg_in_band c0 i Hc0 K)). Qed.
      Lemma ripz_shs : forall sc i, In sc (a_sec st) -> Zn i -> sh_lo (sc_map sc) <= i < SB + (sc_map sc + sc_mapsz sc) / 8 -> False.
      Proof. intros sc i Hs Hz K. exact (ripage_vs_band i Hz (shsec_in_band sc i Hs K)). Qed.
      (* [comment removed for export] *)
      Hypothesis ZRI : forall c0 i, 1 <= c0 <= 30 -> Zn i -> reginfo bt c0 <= i < reginfo bt c0 + 72 -> ~ (reginfo bt c0 + 64 <= i < reginfo bt c0 + 68) -> False.
      Lemma ripz_dt : forall i, Zn i -> bt_dtls bt + 24 <= i < bt_dtls bt + 32 -> False.
      Proof.
        intros i Hz K. destruct (dtls_cell_facts bt st Lc FF W i K) as (_ & _ & _ & _ & _ & D6 & _). pose proof (ZP i Hz) as P.
        pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & IN6 & R6a & R6b & _) & _).
        apply (D6 _ _ IN6); [unfold KSPACE, PG in *; lia | unfold KSPACE, PG in *; lia].
      Qed.
      Theorem ripz_not_cells : forall i, Zn i -> rep_cells bt st Lc FF i -> False.
      Proof. exact (zone_not_cells Zn ripz_img ripz_fix ripz_thr ripz_dyn ZRI ripz_fa ripz_cv ripz_shr ripz_shs ripz_dt). Qed.
    End RIpage.

    (* [comment removed for export] *)
    Section Band.
      Hypothesis ZB : forall i, Zn i -> in_band i.
      Lemma bandz_img : forall i, Zn i -> ia_img_lo IA <= i < ia_img_hi IA -> False.
      Proof. intros i Hz Hi. pose proof band_facts as (B1 & _). pose proof (ZB i Hz). unfold in_band in *. lia. Qed.
      Lemma bandz_fix : forall lo hi i, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi - lo <> PG -> Zn i -> lo <= i < hi -> False.
      Proof. intros lo hi i Hin _ _ Hz Hi. destruct (fixed_range bt st Lc FF W lo hi Hin) as ((_ & _ & _ & _ & D5) & _). pose proof (ZB i Hz). unfold in_band in *. lia. Qed.
      Lemma bandz_thr : forall i, Zn i -> thread_cells bt i -> False.
      Proof.
        intros i Hz K. pose proof (ZB i Hz) as IB. unfold in_band in IB. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _ & _ & INC).
        destruct (fixed_range bt st Lc FF W _ _ INT) as ((_ & _ & _ & _ & D5) & _). destruct (fixed_range bt st Lc FF W _ _ INC) as ((_ & _ & _ & _ & E5) & _).
        destruct (thread_cells_where i K); unfold T_UNW, PG in *; lia.
      Qed.
      Lemma bandz_dyn : forall lo hi i, In (lo, hi) (dyn_ranges st) -> Zn i -> lo <= i < hi -> False.
      Proof.
        intros lo hi i Hin Hz Hi. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
        destruct (RNG lo hi (all_ranges_dyn bt st _ Hin)) as ((_ & _ & _ & _ & D5) & _). pose proof (ZB i Hz). unfold in_band in *. lia.
      Qed.
      Lemma band_vs_space : forall i, Zn i -> SBEG <= i -> False.
      Proof. intros i Hz Hi. pose proof band_facts as (_ & _ & B3 & _). pose proof (ZB i Hz). unfold in_band in *. lia. Qed.
      Lemma bandz_ri : forall c0 i, 1 <= c0 <= 30 -> Zn i -> reginfo bt c0 <= i < reginfo bt c0 + 72 -> ~ (reginfo bt c0 + 64 <= i < reginfo bt c0 + 68) -> False.
      Proof.
        intros c0 i Hc0 Hz Hi _. apply (band_vs_space i Hz).
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (_ & _ & _ & _ & _ & _ & _ & _ & Q9 & _). ulia.
      Qed.
      Lemma bandz_fa : forall c0 i, 1 <= c0 <= 30 -> Zn i -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + r_mapped_fa (a_reg st c0) -> False.
      Proof.
        intros c0 i Hc0 Hz Hi. apply (band_vs_space i Hz).
        pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & _). unfold fa_beg, KFAOFF in *. lia.
      Qed.
      Lemma bandz_cv : forall c0 a i, 1 <= c0 <= 30 -> carved bt st c0 a -> Zn i -> a <= i < a + csize c0 -> False.
      Proof. intros c0 a i Hc0 CV Hz Hi. apply (band_vs_space i Hz). destruct (carved_range bt st Lc FF W c0 a Hc0 CV) as (_ & _ & C3 & _). lia. Qed.
      Hypothesis ZSHR : forall c0 i, 1 <= c0 <= 30 -> Zn i ->
        (sh_lo (region_beg SBEG c0) <= i < SB + (region_beg SBEG c0 + r_mapped_user (a_reg st c0)) / 8)
        \/ (sh_lo (fa_beg SBEG c0) <= i < SB + (fa_beg SBEG c0 + r_mapped_fa (a_reg st c0)) / 8) -> False.
      Hypothesis ZSHS : forall sc i, In sc (a_sec st) -> Zn i -> sh_lo (sc_map sc) <= i < SB + (sc_map sc + sc_mapsz sc) / 8 -> False.
      Lemma bandz_dt : forall i, Zn i -> bt_dtls bt + 24 <= i < bt_dtls bt + 32 -> False.
      Proof. intros i Hz K. destruct (dtls_cell_facts bt st Lc FF W i K) as (_ & _ & _ & D4 & _). pose proof (ZB i Hz) as B. unfold in_band in B. exact (D4 B). Qed.
      Theorem bandz_not_cells : forall i, Zn i -> rep_cells bt st Lc FF i -> False.
      Proof. exact (zone_not_cells Zn bandz_img bandz_fix bandz_thr bandz_dyn bandz_ri bandz_fa bandz_cv ZSHR ZSHS bandz_dt). Qed.
    End Band.
  End Shapes.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem ceil_not_cells : forall i, CEIL <= i -> rep_cells bt st Lc FF i -> False.
  Proof. exact (ceilz_not_cells (fun i => CEIL <= i) (fun i H => H)). Qed.

  Theorem stats_not_cells : forall i, T + 2768 <= i < T + 3168 -> rep_cells bt st Lc FF i -> False.
  Proof. exact (statz_not_cells (fun i => T + 2768 <= i < T + 3168) (fun i H => H)). Qed.

  Theorem rijunk_not_cells : forall c i, 1 <= c <= 30 -> reginfo bt c + 72 <= i < reginfo bt c + 128 -> rep_cells bt st Lc FF i -> False.
  Proof.
    intros c i Hc Hi. apply (ripz_not_cells (fun i => reginfo bt c + 72 <= i < reginfo bt c + 128)); [| | exact Hi].
    - intros j Hj. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (_ & _ & _ & _ & _ & _ & _ & _ & Q9 & Q10 & _). lia.
    - intros c0 j Hc0 Hj K _. unfold reginfo in *. clear -Hc Hc0 Hj K. nia.
  Qed.

  (* [comment removed for export] *)
  Theorem ushadow_not_cells : forall c i, 1 <= c <= 30 ->
    let lo := region_beg SBEG c + r_mapped_user (a_reg st c) in
    sh_lo lo <= i < sh_lo lo + KUSERMAP / 8 -> rep_cells bt st Lc FF i -> False.
  Proof.
    intros c i Hc lo Hi.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & _).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
    pose proof band_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X16).
    assert (Elo : lo = region_beg SBEG c + r_mapped_user (a_reg st c)) by reflexivity.
    assert (AL : lo mod 8 = 0 /\ SBEG <= lo /\ lo + KUSERMAP <= fa_beg SBEG c /\ region_beg SBEG c mod 8 = 0).
    { rewrite Elo. unfold fa_beg, region_beg, KFAOFF, KREGION, KREGION_EXHAUST, KUSERMAP in *. clear -Y2 Y3 Q1 Q8 X16 Hc. Z.div_mod_to_equations. lia. }
    destruct AL as (AL1 & AL2 & AL3 & AL5). clearbody lo.
    apply (bandz_not_cells (fun i => sh_lo lo <= i < sh_lo lo + KUSERMAP / 8)); [| | | exact Hi].
    - intros j Hj. unfold in_band, sh_lo, KUSERMAP in *. unfold fa_beg, KFAOFF in *. clear -Hj B3 B4 B6 AL2 AL3 Q5. Zlia.
    - intros c0 j Hc0 Hj K. unfold sh_lo, KUSERMAP in *.
      destruct (Z.eq_dec c0 c) as [-> | NE].
      + (* [comment removed for export] *)
        unfold fa_beg, KFAOFF, KREGION_EXHAUST in *. clear -Hj K AL1 AL5 Elo Y3 Q8. Zlia.
      + pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
        pose proof W as ((WR1' & _) & _). destruct (WR1' c0 Hc0) as (_ & _ & Z3 & _).
        unfold fa_beg, region_beg, KFAOFF, KREGION, KREGION_EXHAUST, KUSERMAP in *.
        destruct (Z.lt_trichotomy c0 c) as [LT|[EQ|GT]]; [| exact (NE EQ) |].
        * assert (HM : c0 * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32) by (clear -LT; nia). clear -Hj K HM Elo Y3 Q8 P8 Z3 P6 X16 B5. Zlia.
        * assert (HM : c * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (clear -GT; nia). clear -Hj K HM Elo Y3 Q8 P8 Z3 P6 X16 B5. Zlia.
    - intros sc j Hs Hj K. unfold sh_lo, KUSERMAP in *.
      destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & _).
      destruct (fixed_members bt st Lc FF W) as (IN6 & _). destruct (space_facts bt st Lc FF W) as (_ & _ & SP7 & SP8 & _).
      pose proof (fixed_dyn_sep bt st Lc FF W _ _ _ _ IN6 (sec_dyn st sc Hs)) as D.
      unfold fa_beg, KFAOFF in *. clear -Hj K A3 A4 D SP7 SP8 AL1 AL2 AL3 Q5. Zlia.
  Qed.
End Zone.
End AsAinvZone3.
Module AsAinvLowSh3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b AsAinvFacts3 AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

Section LowSh.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_QC, T_PC, PC_SZ, T_UNW, NMAX in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Definition img_shadow (i : Z) : Prop := SB + ia_img_lo IA / 8 <= i < SB + (ia_img_hi IA + 7) / 8.

  Lemma imgshadow_not_cells : forall st Lc FF {qt qg : Z}, WFq bt st Lc FF qt qg ->
    forall i, img_shadow i -> rep_cells bt st Lc FF i -> False.
  Proof.
    intros st Lc FF qt qg W.
    pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    apply (bandz_not_cells bt st Lc FF W img_shadow).
    - intros j Hj. unfold img_shadow, in_band in *. clear -Hj B1 B2. Zlia.
    - intros c0 j Hc0 Hj K. unfold img_shadow, sh_lo in *.
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
      unfold fa_beg, KFAOFF in *. clear -Hj K B1 B3 Q1 Q8. Zlia.
    - intros sc j Hs Hj K. unfold img_shadow, sh_lo in *.
      destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & _).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
      destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((_ & _ & _ & D4 & _) & _).
      clear -Hj K A3 A4 D4 B2. Zlia.
  Qed.

  (* [comment removed for export] *)
  Theorem AAINVP_lowsh_frame : forall (P : ast -> Prop) Lc FF B C K (M M' : mem) mdl,
    AAINVP P bt Lc FF B C K M mdl ->
    (forall a : word, M' a <> M a -> img_shadow (u a) /\ M' a <> None) ->
    AAINVP P bt Lc FF B C K M' mdl.
  Proof.
    intros P Lc FF B C K M M' mdl (st & W & R & BP) CH. exists st. split; [exact W|]. split; [| exact BP].
    apply (Rep_frame_q bt st Lc FF M M' mdl W R). intros a NE. destruct (CH a NE) as [Hz Hd]. split; [| exact Hd].
    intros HC. exact (imgshadow_not_cells st Lc FF W (u a) Hz HC).
  Qed.



End LowSh.
End AsAinvLowSh3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b AsAinvFacts3 AsAinvZone3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

Section ZoneB.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Variables (st : ast) (Lc FF : list (Z * Z)).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uilia := unfold IB, DEPOT_TAB, DEPOT_NIDS, DEPOT_MAP1, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  Ltac uall := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *.

  Definition instpad (i : Z) : Prop := IB bt + 882 <= i < IB bt + 888.

  (* [comment removed for export] *)
  Lemma instpad_img : forall i, instpad i -> ia_img_lo IA <= i < ia_img_hi IA.
  Proof using W qg qt FF Lc st RUN.
    intros i Hi. unfold instpad, IB in Hi.
    pose proof (bt_ok_W bt st Lc FF W) as (I1 & I2 & PR & QI1 & _).
    destruct QI1 as (plo & phi & Hin & P1 & P2). destruct (PR plo phi (or_introl Hin)) as [P3 P4]. lia.
  Qed.

  Theorem instpad_not_cells : forall i, instpad i -> rep_cells bt st Lc FF i -> False.
  Proof using W qg qt RUN.
    intros i Hz HC. pose proof (instpad_img i Hz) as HI. unfold instpad in Hz.
    pose proof W as ((WR1 & WR2) & WC & WQ & (SS1 & SS2 & SS3 & _) & WL & WK & WD & WM & (RNG & PWS & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (img_lits bt st Lc FF W) as [L1 L2].
    pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (img_pw bt st Lc FF W) as IPW. unfold img_ranges in IPW. cbn [PW seps fst snd] in IPW.
    destruct IPW as ((J1 & J2 & J3 & J4 & J5 & J6 & J7 & _) & _).
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & _).
    (* [comment removed for export] *)
    assert (FIXoff : forall lo hi, In (lo, hi) (bt_fixed bt) -> lo <= i < hi -> False).
    { intros lo hi Hin Hlo. destruct (fixed_range bt st Lc FF W lo hi Hin) as ((_ & _ & _ & D4 & _) & _). lia. }
    assert (DYNoff : forall lo hi, In (lo, hi) (dyn_ranges st) -> lo <= i < hi -> False).
    { intros lo hi Hin Hlo. destruct (RNG _ _ (all_ranges_dyn bt st _ Hin)) as ((_ & _ & _ & D4 & _) & _). lia. }
    assert (SPACEoff : SBEG <= i -> False) by (intros HS; clear -HS HI L2 B3; ulia).
    assert (BANDoff : in_band i -> False) by (intros HB; unfold in_band in HB; clear -HB HI L2; ulia).
    unfold rep_cells in HC. unfold IB, DEPOT_TAB, DEPOT_NIDS, DEPOT_MAP1, SSOBJ, IA_FLAG, IA_INST in *.
    destruct HC as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]]].
    - (* [comment removed for export] *) destruct K as (c & Hc & Hin). rewrite Forall_forall in DC.
      apply (DC c Hc i Hin). (lazymatch goal with |- ?G => let G' := eval unfold img_dyn in G in change_no_check G' end). right; left. lia.
    - unfold instance_cells, IB in K. cbn zeta in K.
      destruct K as [K|[K|[K|[K|[K|[K|K]]]]]]; try lia. exact (FIXoff _ _ IN8 ltac:(clear -K SS1 SS3; lia)).
    - destruct (thread_cells_where bt i K) as [A|A]; [exact (FIXoff _ _ INT ltac:(unfold T_UNW, PG in *; lia)) | exact (FIXoff _ _ INC ltac:(lia))].
    - destruct K as (c0 & Hc0 & K). unfold foot_region in K.
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
      apply SPACEoff. unfold fa_beg, KFAOFF in *. clear -K Q1 Q7 Q9 R6a. destruct K as [[K _]|K]; ulia.
    - destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & BB1 & BB2). apply SPACEoff. lia.
    - destruct K as (sc & Hs' & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      apply (DYNoff _ _ (sec_dyn st sc Hs')). pose proof (rz_range (sc_n sc)). clear -K A5 A6 A7 H. ulia.
    - destruct K as (p & n & Hown & K).
      destruct (hdr_zone bt st Lc FF W p n i Hown K) as [(HP & Hi & S1 & S2 & CV & Hc1 & N1 & S3) | (HP & sc & Hsc & Eu & En & Hi & N1)].
      + apply SPACEoff. lia.
      + destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hsc)). rewrite Eu, En in *. clear -Hi A5 A6 N1. ulia.
    - unfold foot_depot_static in K. uall. clear -K Hz J1 J2. lia.
    - destruct K as (id & Hid & K). unfold foot_node in K. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
      pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
      destruct HIn as [Eb | Hnb]; [apply (FIXoff _ _ INN); rewrite Eb; lia | apply (DYNoff _ _ (node_dyn st bb Hnb)); lia].
    - unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
      1-3: apply (FIXoff _ _ INFS); ulia.
      + clear -K Hz J5. lia.
      + apply (FIXoff _ _ (dtls_member bt st Lc FF W)); ulia.
    - destruct K as (f & k & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _).
      apply (FIXoff _ _ INFS). ulia.
    - unfold ialloc_cells in K. uall. clear -K Hz J3 J4. lia.
    - destruct K as (c0 & Hc0 & K). unfold foot_shreg in K. apply BANDoff. apply (shreg_in_band bt st Lc FF W c0 i Hc0). destruct K as [[K _]|K]; [left; exact K | right; exact K].
    - destruct K as (sc & Hs' & K). unfold foot_shsec in K. destruct K as [K _]. apply BANDoff. exact (shsec_in_band bt st Lc FF W sc i Hs' K).
    - unfold rtc_cells in K. uall. clear -K Hz J6 J7. lia.
  Qed.

  (* [comment removed for export] *)
  Section Tjunk.
    Variable Zn : Z -> Prop.
    Hypothesis ZT : forall i, Zn i -> T + 2688 <= i < T + 3168.
    Lemma tjz_img : forall i, Zn i -> ia_img_lo IA <= i < ia_img_hi IA -> False.
    Proof using ZT W qg qt FF Lc st RUN. intros i Hz Hi. destruct (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & D4 & _). pose proof (ZT i Hz). unfold PG in *. lia. Qed.
    Lemma tjz_fix : forall lo hi i, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi - lo <> PG -> Zn i -> lo <= i < hi -> False.
    Proof using ZT W qg qt FF Lc st RUN.
      intros lo hi i Hin _ Hlen Hz Hi. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
      pose proof (fixed_sep bt st Lc FF W _ _ _ _ Hin INT ltac:(intros E; injection E; intros; subst; apply Hlen; lia)) as D.
      pose proof (ZT i Hz). unfold PG in *. lia.
    Qed.
    Lemma tjz_thr : forall i, Zn i -> thread_cells bt i -> False.
    Proof using ZT W qg qt FF Lc st RUN.
      intros i Hz K. pose proof (ZT i Hz). destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _ & _ & INC).
      pose proof (fixed_sep bt st Lc FF W _ _ _ _ INC INT ltac:(intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); intros; lia)) as D.
      unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW, PG in *. lia.
    Qed.
    Lemma tjz_dyn : forall lo hi i, In (lo, hi) (dyn_ranges st) -> Zn i -> lo <= i < hi -> False.
    Proof using ZT W qg qt FF Lc bt RUN.
      intros lo hi i Hin Hz Hi. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
      pose proof (fixed_dyn_sep bt st Lc FF W _ _ _ _ INT Hin) as D. pose proof (ZT i Hz). unfold PG in *. lia.
    Qed.
    Lemma tjunk_vs_space : forall i, Zn i -> SBEG <= i < SBEG + KSPACE + PG -> False.
    Proof using ZT W qg qt FF Lc st RUN.
      intros i Hz Hi. destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _).
      destruct (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG, KSPACE in G in change_no_check G' end); lia)); pose proof (ZT i Hz); unfold PG in *; lia.
    Qed.
    Lemma tjz_ri : forall c0 i, 1 <= c0 <= 30 -> Zn i -> reginfo bt c0 <= i < reginfo bt c0 + 72 -> ~ (reginfo bt c0 + 64 <= i < reginfo bt c0 + 68) -> False.
    Proof using ZT W qg qt FF Lc st RUN.
      intros c0 i Hc0 Hz Hi _. apply (tjunk_vs_space i Hz).
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (_ & _ & _ & _ & _ & _ & _ & _ & Q9 & Q10 & _). ulia.
    Qed.
    Lemma tjz_fa : forall c0 i, 1 <= c0 <= 30 -> Zn i -> fa_beg SBEG c0 <= i < fa_beg SBEG c0 + r_mapped_fa (a_reg st c0) -> False.
    Proof using ZT W qg qt FF Lc RUN.
      intros c0 i Hc0 Hz Hi. apply (tjunk_vs_space i Hz).
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _). ulia.
    Qed.
    Lemma tjz_cv : forall c0 a i, 1 <= c0 <= 30 -> carved bt st c0 a -> Zn i -> a <= i < a + csize c0 -> False.
    Proof using ZT W qg qt FF Lc RUN.
      intros c0 a i Hc0 CV Hz Hi. apply (tjunk_vs_space i Hz). destruct (carved_range bt st Lc FF W c0 a Hc0 CV) as (_ & _ & C3 & C4 & _). ulia.
    Qed.
    Lemma tjunk_vs_band : forall i, Zn i -> in_band i -> False.
    Proof using ZT W qg qt FF Lc st bt RUN.
      intros i Hz Hi. destruct (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & D5). pose proof (ZT i Hz). unfold in_band, PG in *. lia.
    Qed.
    Lemma tjz_shr : forall c0 i, 1 <= c0 <= 30 -> Zn i ->
      (sh_lo (region_beg SBEG c0) <= i < SB + (region_beg SBEG c0 + r_mapped_user (a_reg st c0)) / 8)
      \/ (sh_lo (fa_beg SBEG c0) <= i < SB + (fa_beg SBEG c0 + r_mapped_fa (a_reg st c0)) / 8) -> False.
    Proof using ZT W qg qt FF Lc RUN. intros c0 i Hc0 Hz K. exact (tjunk_vs_band i Hz (shreg_in_band bt st Lc FF W c0 i Hc0 K)). Qed.
    Lemma tjz_shs : forall sc i, In sc (a_sec st) -> Zn i -> sh_lo (sc_map sc) <= i < SB + (sc_map sc + sc_mapsz sc) / 8 -> False.
    Proof using ZT W qg qt FF Lc bt RUN. intros sc i Hs Hz K. exact (tjunk_vs_band i Hz (shsec_in_band bt st Lc FF W sc i Hs K)). Qed.
    Lemma tjz_dt : forall i, Zn i -> bt_dtls bt + 24 <= i < bt_dtls bt + 32 -> False.
    Proof using ZT W qg qt FF Lc st RUN. intros i Hz K. destruct (dtls_cell_facts bt st Lc FF W i K) as (_ & _ & _ & _ & D5 & _). pose proof (ZT i Hz). apply D5. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia. Qed.
    Theorem tjz_not_cells : forall i, Zn i -> rep_cells bt st Lc FF i -> False.
    Proof using ZT W qg qt RUN. exact (zone_not_cells bt st Lc FF W Zn tjz_img tjz_fix tjz_thr tjz_dyn tjz_ri tjz_fa tjz_cv tjz_shr tjz_shs tjz_dt). Qed.
  End Tjunk.
  Theorem tjunk_not_cells : forall i, T + 2688 <= i < T + 3168 -> rep_cells bt st Lc FF i -> False.
  Proof using W qg qt RUN. exact (tjz_not_cells (fun i => T + 2688 <= i < T + 3168) (fun i H => H)). Qed.
End ZoneB.
