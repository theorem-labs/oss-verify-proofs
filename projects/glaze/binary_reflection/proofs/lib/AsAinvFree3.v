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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

Section Free.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, PTRHI in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, PTRHI, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma up8_rounded : forall n, 1 <= n -> up8 n <= rounded n /\ rounded n mod 8 = 0 /\ 8 <= rounded n.
  Proof using.
    intros n Hn. pose proof (rounded_ge n) as (R1 & R2 & R3 & R4). unfold up8, rounded, RoundUp in *.
    Z.div_mod_to_equations. nia.
  Qed.

  Lemma sec_map_room : forall n, 1 <= n -> rounded n + PG + rz n <= sec_map_size n.
  Proof using.
    intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold sec_map_size, sec_needed in G in change_no_check G' end). pose proof (rz_range n).
    pose proof (RoundUp_ge (rounded n + 2 * rz n) PG ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)). unfold PG in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section W.
    Variables (st : ast) (Lc FF : list (Z * Z)).
    Context {qt qg : Z}.
    Hypothesis W : WFq bt st Lc FF qt qg.   (* [comment removed for export] *)

    Definition ext (p n lo hi : Z) : Prop :=
      (is_primary n = true /\ lo = p - rz n /\ hi = p - rz n + csize (blk_class n) /\ carved bt st (blk_class n) lo /\ 1 <= blk_class n <= 30
         /\ in_live_c Lc (blk_class n) lo /\ SBEG <= lo /\ hi <= SBEG + KSPACE)
      \/ (is_primary n = false /\ exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n /\ lo = sc_map sc + PG /\ hi = sc_map sc + sc_mapsz sc).

    Lemma live_ext : forall p n, In (p, n) Lc ->
      exists lo hi, ext p n lo hi /\ lo <= p - rz n /\ p + up8 n <= hi /\ p + rounded n <= hi /\ lo mod 16 = 0 /\ hi mod 16 = 0
                    /\ 0 < lo /\ hi <= CEIL /\ 16 <= rz n <= 2048 /\ p mod 16 = 0 /\ 1 <= n <= NMAX
                    /\ boxed (hi <= ia_img_lo IA \/ ia_img_hi IA <= lo) /\ boxed (hi <= AS_LO \/ AS_HEAPLO <= lo).
    Proof using W qg qt FF.
      intros p n Hin. destruct (live_range bt st Lc FF W p n Hin) as (L1 & L2 & L3 & L4). pose proof (rz_range n) as RZ.
      pose proof (up8_rounded n ltac:(lia)) as (U1 & U2 & U3).
      pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X14 & X15 & X16).
      destruct (is_primary n) eqn:HP.
      - pose proof (live_chunk bt st Lc FF W p n Hin HP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6). unfold prim_alloc_beg in *.
        destruct (carved_range bt st Lc FF W _ _ G1 G2) as (C1 & C2 & C3 & C4 & C5). pose proof (csize_pos _ G1) as ((S1 & S2) & S3).
        pose proof (csize_class_of (needed n)) as CC. unfold blk_class in *.
        assert (NB : 1 <= needed n <= 65536) by (pose proof HP as HP2; unfold is_primary in HP2; apply Z.leb_le in HP2; unfold needed in *; lia).
        specialize (CC NB). assert (EN : needed n = rounded n + rz n) by reflexivity.
        exists (p - rz n), (p - rz n + csize (class_of (needed n))).
        split. { left. (lazymatch goal with |- ?G => let G' := eval unfold blk_class in G in change_no_check G' end). repeat split; try assumption; try reflexivity; lia. }
        pose proof (rz_mod16 n) as RM.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact C5|]. split; [clear -C5 S3; Z.div_mod_to_equations; lia|].
        destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). pose proof (img_lits bt st Lc FF W) as [I1 I2].
        split; [ulia|]. split; [ulia|]. split; [exact RZ|]. split; [exact L4|]. split; [exact L3|]. (lazymatch goal with |- ?G => let G' := eval unfold boxed in G in change_no_check G' end). split; ulia.
      - destruct (live_sec bt st Lc FF W p n Hin HP) as (sc & Hs & Eu & En).
        destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). rewrite Eu, En in *.
        pose proof (sec_map_room n ltac:(lia)) as SR. unfold sc_mapsz in *. rewrite En in *.
        exists (sc_map sc + PG), (sc_map sc + sec_map_size n).
        split. { right. split; [exact HP|]. exists sc. repeat split; try assumption. (lazymatch goal with |- ?G => let G' := eval unfold sc_mapsz in G in change_no_check G' end). rewrite En. reflexivity. }
        pose proof (sec_map_size_ge n ltac:(lia)) as (SG1 & SG2 & SG3).
        split; [ulia|]. split; [ulia|]. split; [ulia|]. split; [clear -A3; unfold PG in *; Z.div_mod_to_equations; lia|].
        split; [clear -A3 SG2; unfold PG in *; Z.div_mod_to_equations; lia|].
        pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
        destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((D1 & D1' & D3 & D4 & D5) & D2 & _).
        split; [ulia|]. split; [ulia|]. split; [exact RZ|]. split; [exact L4|]. split; [exact L3|]. (lazymatch goal with |- ?G => let G' := eval unfold boxed in G in change_no_check G' end). unfold sc_mapsz in D4, D5. rewrite ?En in D4, D5. split; clear -D4 D5 A3; unfold PG in *; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma live_ext_sep : forall p n p' n' lo hi lo' hi', In (p, n) Lc -> In (p', n') Lc -> (p, n) <> (p', n') ->
      ext p n lo hi -> ext p' n' lo' hi' -> hi <= lo' \/ hi' <= lo.
    Proof using W qg qt FF RUN.
      intros p n p' n' lo hi lo' hi' Hin Hin' NE E E'.
      destruct (live_range bt st Lc FF W p n Hin) as (L1 & L2 & L3 & L4). destruct (live_range bt st Lc FF W p' n' Hin') as (L1' & L2' & L3' & L4').
      destruct E as [(HP & -> & -> & CV & HC & LIV & S1 & S2) | (HP & sc & Hs & Eu & En & -> & ->)];
      destruct E' as [(HP' & -> & -> & CV' & HC' & LIV' & S1' & S2') | (HP' & sc' & Hs' & Eu' & En' & -> & ->)].
      - destruct (chunk_cases bt st Lc FF W _ _ _ _ HC HC' CV CV') as [[EC EA] | D]; [| exact D].
        exfalso. pose proof (rz_unif n n' ltac:(lia) ltac:(lia) HP HP' EC) as ER.
        assert (p' = p) by (clear -EA ER; lia). subst p'.
        destruct (Z.eq_dec n n') as [<- | NEn]; [exact (NE eq_refl)|].
        destruct W as (_ & _ & _ & _ & (_ & _ & SEP) & _). destruct (SEP p n p n' Hin Hin' ltac:(clear -NEn; congruence)) as [OV|OV]; clear -OV L3 L3'; lia.
      - destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc' Hs')); ulia.
      - destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
      - destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D]; [| ulia].
        exfalso. apply NE. f_equal; congruence.
    Qed.

    (* [comment removed for export] *)
    Lemma live_ext_vs_fixed : forall p n lo hi flo fhi, In (p, n) Lc -> ext p n lo hi ->
      In (flo, fhi) (bt_fixed bt) -> fhi - flo < KSPACE -> hi <= flo \/ fhi <= lo.
    Proof using W qg qt FF RUN.
      intros p n lo hi flo fhi Hin E Hf Hlen.
      destruct E as [(HP & -> & -> & CV & HC & LIV & S1 & S2) | (HP & sc & Hs & Eu & En & -> & ->)].
      - destruct (space_vs_fixed bt st Lc FF W flo fhi Hf Hlen); ulia.
      - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hf (sec_dyn st sc Hs)) as D. hnf in D. cbn in D. ulia.
    Qed.

    Lemma live_ext_vs_batch : forall p n lo hi b, In (p, n) Lc -> ext p n lo hi -> In b (a_tq st ++ a_gq st) ->
      hi <= ba_addr b \/ ba_addr b + BATCHSZ <= lo.
    Proof using W qg qt FF RUN.
      intros p n lo hi b Hin E Hb. destruct (batch_facts bt st Lc FF W b Hb) as (CVB & BL & B1 & B2).
      destruct E as [(HP & -> & -> & CV & HC & LIV & S1 & S2) | (HP & sc & Hs & Eu & En & -> & ->)].
      - destruct (chunk_cases bt st Lc FF W _ _ BATCHCLASS (ba_addr b) HC ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) CV CVB) as [[EC EA] | D].
        + exfalso. destruct W as ((WR & _) & _). destruct (WR BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK).
          destruct PART as (_ & _ & _ & _ & _ & _ & _ & NB & _).
          apply (NB (ba_addr b) ltac:(exists b; split; [exact Hb | reflexivity]) eq_refl). left. rewrite <- EC, <- EA. exact LIV.
        + change (csize BATCHCLASS) with 8192 in D. ulia.
      - destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia.
    Qed.

    Lemma live_ext_vs_node : forall p n lo hi bb, In (p, n) Lc -> ext p n lo hi -> In bb (node_blocks bt (a_dep st)) ->
      hi <= bb \/ bb + 2 ^ 20 <= lo.
    Proof using W qg qt FF RUN.
      intros p n lo hi bb Hin E Hbb. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & _) & _).
      destruct Hbb as [<- | Hnb].
      - exact (live_ext_vs_fixed p n lo hi _ _ Hin E INN ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)).
      - destruct E as [(HP & -> & -> & CV & HC & LIV & S1 & S2) | (HP & sc & Hs & Eu & En & -> & ->)].
        + destruct (space_vs_dyn bt st Lc FF W _ _ (node_dyn st bb Hnb)); ulia.
        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (sec_vs_node bt st Lc FF W sc bb Hs Hnb); ulia.
    Qed.

    Lemma live_ext_vs_store : forall p n lo hi bb, In (p, n) Lc -> ext p n lo hi -> In bb (store_blocks bt (a_dep st)) ->
      hi <= bb \/ bb + 2 ^ 23 <= lo.
    Proof using W qg qt FF RUN.
      intros p n lo hi bb Hin E Hbb. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & _) & _).
      destruct Hbb as [<- | Hsb].
      - exact (live_ext_vs_fixed p n lo hi _ _ Hin E INS ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)).
      - destruct E as [(HP & -> & -> & CV & HC & LIV & S1 & S2) | (HP & sc & Hs & Eu & En & -> & ->)].
        + destruct (space_vs_dyn bt st Lc FF W _ _ (store_dyn st bb Hsb)); ulia.
        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). destruct (sec_vs_store bt st Lc FF W sc bb Hs Hsb); ulia.
    Qed.

    (* [comment removed for export] *)
    Lemma live_ext_vs_frame : forall p n lo hi f k, In (p, n) Lc -> ext p n lo hi -> In (f, k) FF ->
      hi <= f \/ f + FS k <= lo.
    Proof using W qg qt RUN.
      intros p n lo hi f k Hin E Hf. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & _) & _).
      destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & _).
      destruct (live_ext_vs_fixed p n lo hi _ _ Hin E INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); lia)); ulia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma OBL_hdr_writable_pf : forall M mdl p n, Rep bt st Lc FF M mdl -> In (p, n) Lc -> writableZ SG M (p - 16) (p + up8 n).
    Proof using W qg qt.
      intros M mdl p n R Hin. destruct (live_ext p n Hin) as (lo & hi & E & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
      destruct E as [(HP & -> & -> & CV & HC & LIV & S1 & S2) | (HP & sc & Hs & Eu & En & -> & ->)].
      - destruct R as (_ & _ & _ & R4 & _). destruct (R4 _ HC) as [_ (_ & _ & F3)].
        destruct (carved_range bt st Lc FF W _ _ HC CV) as (C1 & C2 & _). pose proof (region_facts bt st Lc FF W _ HC) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & _).
        eapply writableZ_sub; [exact F3 | lia | lia].
      - destruct R as (_ & _ & _ & _ & _ & _ & R7 & _). destruct (In_nth_error _ _ Hs) as [i Hi]. destruct (R7 i sc Hi) as (_ & _ & _ & _ & SW).
        eapply writableZ_sub; [exact SW | ulia | lia].
    Qed.

    Lemma OBL_blk_geom_pf : forall p n, In (p, n) Lc ->
      (p + up8 n <= bt_thread bt \/ bt_thread bt + PG <= p - 16) /\ (bt_tctx bt + 0x10000 <= p - 16 \/ p + up8 n <= bt_tctx bt)
      /\ ablk_ok IA (p - 16) (16 + up8 n).
    Proof using W qg qt FF st.
      intros p n Hin. destruct (live_ext p n Hin) as (lo & hi & E & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & INT & INN & INS & INC & _) & _).
      split; [| split].
      - destruct (live_ext_vs_fixed p n lo hi _ _ Hin E INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG, KSPACE in G in change_no_check G' end); lia)); ulia.
      - destruct (live_ext_vs_fixed p n lo hi _ _ Hin E INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)); ulia.
      - (lazymatch goal with |- ?G => let G' := eval unfold ablk_ok in G in change_no_check G' end). unfold boxed in X11, X12.
        assert (LO16 : PTRLO <= p - 16).
        { destruct E as [(HP & -> & -> & CV & HC & LIV & S1 & S2) | (HP & sc & Hs & Eu & En & -> & ->)].
          - destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). clear -S1 X8 SP7 SPH. ulia.
          - destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & _). clear -X1 X8 A1 A3. unfold PTRLO, PG in *. Z.div_mod_to_equations. lia. }
        clear -LO16 X1 X2 X7 X8 X9 X11 X12. dsj; ulia.
    Qed.

    Lemma OBL_batch_geom_pf : forall b p n, In b (a_tq st ++ a_gq st) -> In (p, n) Lc ->
      (ba_addr b + BATCHSZ <= p - 16 \/ p + up8 n <= ba_addr b) /\ (ba_addr b + BATCHSZ <= bt_thread bt \/ bt_thread bt + PG <= ba_addr b)
      /\ AS_HEAPLO <= ba_addr b /\ ba_addr b + BATCHSZ <= CEIL.
    Proof using W qg qt FF.
      intros b p n Hb Hin. destruct (live_ext p n Hin) as (lo & hi & E & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
      destruct (batch_facts bt st Lc FF W b Hb) as (CVB & BL & B1 & B2).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & INT & _) & _).
      pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F14 & F15 & _).
      destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
      destruct (live_ext_vs_batch p n lo hi b Hin E Hb); destruct (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG, KSPACE in G in change_no_check G' end); lia)); ulia.
    Qed.

    Lemma OBL_X_vs_node_pf : forall p n id a, In (p, n) Lc -> 1 <= id <= dp_nids (a_dep st) ->
      (p - 16 <= a < p + up8 n \/ bt_thread bt <= a < bt_thread bt + PG \/ CEIL <= a) -> ~ foot_node bt (a_dep st) id a.
    Proof using W qg qt FF.
      intros p n id a Hin Hid Ha HN. unfold foot_node in HN.
      destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3). pose proof (node_addr_block bt st id Hid) as Hbk.
      set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
      destruct (node_blocks_range bt st Lc FF W bb HIn) as (B1 & B2 & B3).
      destruct Ha as [Ha | [Ha | Ha]]; [| | ulia].
      - destruct (live_ext p n Hin) as (lo & hi & E & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
        destruct (live_ext_vs_node p n lo hi bb Hin E HIn); lia.
      - pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & _ & _ & _ & _ & INFS & INT & INN & _) & _).
        destruct HIn as [Eb | Hnb].
        + pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INT) (all_ranges_fixed bt st _ INN) ltac:(intros EQ; injection EQ; intros; ulia)) as D. hnf in D. cbn in D. rewrite <- Eb in *. ulia.
        + pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (node_dyn st bb Hnb)) as D. hnf in D. cbn in D. ulia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma heap_not_shadowish : forall Lc' a, (forall p n, In (p, n) Lc' -> In (p, n) Lc) -> (a < AS_LO \/ AS_HEAPLO <= a) ->
      ~ in_block_shadow Lc' a /\ ~ in_frame_shadow FF a /\ ~ in_stack_shadow a /\ ~ in_image_shadow IA a.
    Proof using W qg qt st.
      intros Lc' a SUB Ha. pose proof (bt_ok_W bt st Lc FF W) as BT.
      split; [| split; [| split]].
      - intros (p & n & Hin & Hs). unfold sh_lo, sh_hi in Hs. destruct (live_range bt st Lc FF W p n (SUB p n Hin)) as (L1 & L2 & L3 & L4).
        clear -Ha Hs L1 L2. Zlia.
      - intros (f & k & Hf & Hs). unfold sh_lo, sh_hi in Hs. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
        pose proof (fs_range bt st Lc FF W) as ((G1 & _ & G2 & _ & G5) & G3). clear -Ha Hs F1 F2 F4 G1 G2. Zlia.
      - intros Hs. unfold in_stack_shadow, sh_lo in Hs. clear -Ha Hs. Zlia.
      - intros Hs. unfold in_image_shadow, sh_lo, sh_hi in Hs. destruct BT as (I1 & I2 & _). clear -Ha Hs I1 I2. Zlia.
    Qed.

    Lemma OBL_nolazy_rt_pf : forall M mdl a, Rep bt st Lc FF M mdl ->
      (bt_thread bt <= a < bt_thread bt + PG) \/ (bt_tctx bt <= a < bt_tctx bt + 0x10000)
      \/ (exists p n, In (p, n) Lc /\ p - 16 <= a < p + up8 n)
      \/ (exists b, In b (a_tq st ++ a_gq st) /\ ba_addr b <= a < ba_addr b + BATCHSZ) -> lzb mdl a = false.
    Proof using W qg qt.
      intros M mdl a R [Ha | [Ha | [(p & n & Hin & Ha) | (b & Hb & Ha)]]].
      - exact (rep_nolazy_thread bt st Lc FF M mdl W R a Ha).
      - exact (rep_nolazy_tctx bt st Lc FF M mdl W R a Ha).
      - destruct (live_ext p n Hin) as (lo & hi & E & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
        destruct E as [(HP & -> & -> & CV & HC & LIV & S1 & S2) | (HP & sc & Hs & Eu & En & -> & ->)].
        + apply (rep_nolazy_chunk bt st Lc FF M mdl W R _ _ a HC CV). lia.
        + destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). apply (rep_nolazy_sec bt st Lc FF M mdl W R sc a Hs). ulia.
      - exact (rep_nolazy_batch bt st Lc FF M mdl W R b a Hb Ha).
    Qed.

    (* [comment removed for export] *)
    Lemma OBL_rt_private_pf : forall a,
      (bt_thread bt <= a < bt_thread bt + PG) \/ (exists b, In b (a_tq st ++ a_gq st) /\ ba_addr b <= a < ba_addr b + BATCHSZ) ->
      rt_priv IA Lc FF a.
    Proof using W qg qt.
      intros a Ha. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & _) & _).
      pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
      destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). pose proof (img_lits bt st Lc FF W) as [I1 I2].
      destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((TD1 & TD2 & TD3 & TD4 & TD5) & _).
      assert (HZ : a < CEIL /\ ~ (ia_img_lo IA <= a < ia_img_hi IA) /\ (a < AS_LO \/ AS_HEAPLO <= a)).
      { destruct Ha as [Ha | (b & Hb & Ha)]; [clear -Ha TD1 TD3 TD4 TD5; dsj; ulia|].
        destruct (batch_facts bt st Lc FF W b Hb) as (_ & _ & B1 & B2). clear -Ha B1 B2 SPH SP7 X15 I2. ulia. }
      clear TD4 TD5. destruct HZ as (HZ1 & HZ2 & HZ3). split; [exact HZ1|]. split; [exact HZ2|].
      destruct (heap_not_shadowish Lc a ltac:(intros p n H; exact H) HZ3) as (N1 & N2 & N3 & N4). clear HZ3.
      intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
      - destruct V as (p & n & Hin & Hpa). destruct (live_ext p n Hin) as (lo & hi & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
        pose proof (up8_facts n ltac:(lia)) as (U1 & _).
        destruct Ha as [Ha | (b & Hb & Ha)].
        + destruct (live_ext_vs_fixed p n lo hi _ _ Hin E INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG, KSPACE in G in change_no_check G' end); lia)); ulia.
        + destruct (live_ext_vs_batch p n lo hi b Hin E Hb); ulia.
      - destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
        destruct Ha as [Ha | (b & Hb & Ha)].
        + pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INT) (all_ranges_fixed bt st _ INFS) ltac:(intros EQ; injection EQ; intros; ulia)) as D. hnf in D. cbn in D. ulia.
        + destruct (batch_facts bt st Lc FF W b Hb) as (_ & _ & B1 & B2).
          destruct (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); lia)); ulia.
    Qed.

    Lemma OBL_store_private_pf : forall blk a, In blk (dp_storeblocks (a_dep st)) -> blk <= a < blk + 2 ^ 23 ->
      rt_priv IA Lc FF a.
    Proof using W qg qt.
      intros blk a Hb Ha. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & _) & _).
      destruct (store_blocks_range bt st Lc FF W blk ltac:(right; exact Hb)) as (B1 & B2 & B3).
      destruct (RNG _ _ (all_ranges_dyn bt st _ (store_dyn st blk Hb))) as ((SD1 & SD2 & SD3 & SD4 & SD5) & _).
      split; [ulia|]. split; [clear -Ha SD4; dsj; ulia|].
      destruct (heap_not_shadowish Lc a ltac:(intros p n H; exact H) ltac:(clear -Ha SD5; dsj; ulia)) as (N1 & N2 & N3 & N4). clear SD4 SD5.
      intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
      - destruct V as (p & n & Hin & Hpa). destruct (live_ext p n Hin) as (lo & hi & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
        pose proof (up8_facts n ltac:(lia)) as (U1 & _).
        destruct (live_ext_vs_store p n lo hi blk Hin E ltac:(right; exact Hb)); lia.
      - destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
        destruct (fs_vs_dyn bt st Lc FF W _ _ (store_dyn st blk Hb)); ulia.
    Qed.

    Lemma frame_gran : forall f k, In (f, k) FF -> f mod 8 = 0 /\ FS k mod 8 = 0.
    Proof using W qg qt Lc st bt RUN.
      intros f k Hf. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
      pose proof (fs_range bt st Lc FF W) as (_ & G3).
      assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by (unfold KMAXCLASS in F5; lia).
      rewrite F7. (lazymatch goal with |- ?G => let G' := eval unfold fake_frame_addr, FS in G in change_no_check G' end). unfold PG in G3.
      destruct K as [-> | [-> | [-> | ->]]]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); Z.div_mod_to_equations; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma OBL_freed_private_pf : forall L1 L2 p n a, Lc = L1 ++ (p, n) :: L2 ->
      (p - 16 <= a < p + up8 n \/ sh_lo p <= a < sh_hi p n) -> rt_priv IA (L1 ++ L2) FF a.
    Proof using W qg qt st.
      intros L1 L2 p n a HL Ha.
      assert (Hin : In (p, n) Lc) by (rewrite HL; apply in_app_iff; right; left; reflexivity).
      pose proof W as (_ & _ & _ & _ & (_ & ND & _) & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & _) & _).
      assert (NDL : List.NoDup (L1 ++ (p, n) :: L2)) by (rewrite <- HL; exact ND).
      assert (INL : forall x, In x (L1 ++ L2) -> In x Lc /\ x <> (p, n)) by (intros x Hx; rewrite HL; apply (in_remove_mid L1 L2 (p, n) x NDL); exact Hx).
      destruct (live_ext p n Hin) as (lo & hi & E & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
      pose proof (up8_facts n ltac:(lia)) as (U1 & U2 & U3 & U4).
      pose proof (bt_ok_W bt st Lc FF W) as (I1 & I2 & _).
      destruct Ha as [Ha | Ha].
      - (* [comment removed for export] *)
        split; [ulia|]. split; [clear -Ha X1 X2 X8 X11; Zlia|].
        destruct (heap_not_shadowish (L1 ++ L2) a ltac:(intros p' n' H; exact (proj1 (INL _ H))) ltac:(clear -Ha X1 X2 X8 X12; Zlia)) as (N1 & N2 & N3 & N4).
        intros [V | [V | [V | [V | [V | V]]]]]; [| | exact (N1 V) | exact (N2 V) | exact (N3 V) | exact (N4 V)].
        + destruct V as (p' & n' & Hin' & Hpa). destruct (INL _ Hin') as [Hin2 NE].
          destruct (live_ext p' n' Hin2) as (lo' & hi' & E' & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
          pose proof (up8_facts n' ltac:(lia)) as (V1 & _).
          destruct (live_ext_sep p n p' n' lo hi lo' hi' Hin Hin2 ltac:(congruence) E E'); lia.
        + destruct V as (f & k & Hf & Hfa). destruct (live_ext_vs_frame p n lo hi f k Hin E Hf); lia.
      - (* [comment removed for export] *)
        unfold sh_lo, sh_hi in Ha. split; [clear -Ha X1 X2 X6 X7 X8 U1; Zlia|]. split; [clear -Ha X1 X2 X6 X7 X8 U1 I2; Zlia|].
        intros [V | [V | [V | [V | [V | V]]]]].
        + destruct V as (p' & n' & Hin' & Hpa). destruct (INL _ Hin') as [Hin2 _].
          pose proof W as (_ & _ & _ & _ & (WL0 & _) & _). destruct (WL0 p' n' Hin2) as (_ & _ & (LB1 & LB2 & LB3 & LB4) & _).
          clear -Ha Hpa LB1 LB4 X1 X2 X6 X7 X8 U1. Zlia.
        + destruct V as (f & k & Hf & Hfa). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & _).
          pose proof (fs_range bt st Lc FF W) as ((G1 & _ & G2 & _ & G5) & _). clear -Ha Hfa F1 F2 G1 G2 G5 X1 X2 X6 X7 X8 U1. Zlia.
        + destruct V as (p' & n' & Hin' & Hs). unfold sh_lo, sh_hi in Hs. destruct (INL _ Hin') as [Hin2 NE].
          destruct (live_ext p' n' Hin2) as (lo' & hi' & E' & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
          pose proof (up8_facts n' ltac:(lia)) as (V1 & _).
          destruct (live_ext_sep p n p' n' lo hi lo' hi' Hin Hin2 ltac:(congruence) E E') as [D|D].
          * apply (gran_sep lo' hi' p n (a - SB)); [left; split; [lia | clear -Y4; Zlia] | clear -Ha; Zlia | clear -Hs Y1 Y2 V1 Y5 Y8; Zlia].
          * apply (gran_sep lo hi p' n' (a - SB)); [left; split; [lia | clear -X4; Zlia] | clear -Hs; Zlia | clear -Ha X1 X2 X5 X8 U1; Zlia].
        + destruct V as (f & k & Hf & Hs). unfold sh_lo, sh_hi in Hs. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
          destruct (frame_gran f k Hf) as [FM1 FM2].
          destruct (live_ext_vs_frame p n lo hi f k Hin E Hf) as [D|D].
          * apply (gran_sep f (f + FS k) p n (a - SB)); [left; split; [lia | exact FM1] | clear -Ha; Zlia | clear -Hs FM1 FM2 F4; Zlia].
          * apply (gran_sep lo hi f (FS k) (a - SB)); [left; split; [lia | clear -X4; Zlia] | clear -Hs; Zlia | clear -Ha X1 X2 X5 X8 U1; Zlia].
        + unfold in_stack_shadow, sh_lo in V. clear -Ha V X2 X7 U1. Zlia.
        + unfold in_image_shadow, sh_lo, sh_hi in V. clear -Ha V X1 X2 X4 X5 X6 X7 X8 X11 U1 I1 I2. Zlia.
    Qed.

    (* [comment removed for export] *)
    Lemma OBL_stats_not_rep_pf : forall a, bt_thread bt + 2768 <= a < bt_thread bt + 3168 -> ~ rep_cells bt st Lc FF a.
    Proof using W qg qt RUN.
      intros a Ha RC. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & _).
      pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
      assert (TFIX : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> PG -> lo <= a < hi -> False).
      { intros lo hi Hlo Hlen Hr. pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hlo) (all_ranges_fixed bt st _ INT) ltac:(intros EQ; injection EQ; intros; ulia)) as D. hnf in D. cbn in D. ulia. }
      assert (TDYN : forall lo hi, In (lo, hi) (dyn_ranges st) -> lo <= a < hi -> False).
      { intros lo hi Hlo Hr. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT Hlo) as D. hnf in D. cbn in D. ulia. }
      pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG, KSPACE in G in change_no_check G' end); lia)) as TSP.
      (* [comment removed for export] *)
      destruct (dyn_kind_facts bt st Lc FF W a (dyn_kind_fixed bt st _ _ a INT ltac:(ulia))) as (D1 & D2 & D3 & D4).
      destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
      destruct RC as [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | K]]]]]]]]]]]]]].
      - destruct (img_kinds bt st Lc FF W a ltac:(left; exact K)) as [HH _]. exact (D3 HH).
      - destruct (decide (bt_ptrarr bt <= a < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
        + pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _). apply (TFIX _ _ IN8); ulia.
        + destruct (img_kinds bt st Lc FF W a ltac:(right; left; split; [exact K | exact NI])) as [HH _]. exact (D3 HH).
      - unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in K. destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; try ulia. all: apply (TFIX _ _ INC); ulia.
      - destruct K as (c & Hc & K). unfold foot_region in K. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
        destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _). ulia.
      - destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (_ & BL & B1 & B2). ulia.
      - destruct K as (sc & Hs & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
        apply (TDYN _ _ (sec_dyn st sc Hs)). ulia.
      - destruct K as (p' & n' & Hown & K). pose proof (rz_range n') as RZ'.
        destruct (hdr_zone bt st Lc FF W p' n' a Hown K) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')]; [ulia|].
        destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). apply (TDYN _ _ (sec_dyn st sc' Hs')). ulia.
      - destruct (img_kinds bt st Lc FF W a ltac:(right; right; left; exact K)) as [HH _]. exact (D3 HH).
      - destruct K as (id & Hid & K). unfold foot_node in K. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3).
        pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
        destruct HIn as [Eb | Hnb]; [apply (TFIX _ _ INN); [ulia | rewrite Eb; lia] | apply (TDYN _ _ (node_dyn st bb Hnb)); lia].
      - unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
        1-3: apply (TFIX _ _ INFS); ulia.
        + destruct (img_kinds bt st Lc FF W a ltac:(do 3 right; left; exact K)) as [HH _]. exact (D3 HH).
        + pose proof (dtls_vs_thread bt st Lc FF W) as DV. ulia.
      - destruct K as (f & k & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
        apply (TFIX _ _ INFS); ulia.
      - destruct (img_kinds bt st Lc FF W a ltac:(do 4 right; left; exact K)) as [HH _]. exact (D3 HH).
      - destruct K as (c & Hc & K). unfold foot_shreg, sh_lo in K. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
        destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). unfold in_band in D4. clear -Ha K D4 X14 Q1 Q2 Q5 Q6 Q8 X15. Zlia.
      - destruct K as (sc & Hs & K). unfold foot_shsec, sh_lo in K. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). unfold in_band in D4. clear -Ha K D4 A1 A2. Zlia.
      - destruct (img_kinds bt st Lc FF W a ltac:(do 5 right; exact K)) as [HH _]. exact (D3 HH).
    Qed.
  End W.

  (* [comment removed for export] *)
  Theorem free_obls_but_stats_pf :
    OBL_nolazy_rt_stmt bt /\ OBL_freed_private_stmt bt /\ OBL_rt_private_stmt bt
    /\ OBL_blk_geom_stmt bt /\ OBL_batch_geom_stmt bt /\ OBL_hdr_writable_stmt bt /\ OBL_X_vs_node_stmt bt
    /\ OBL_store_private_stmt bt.
  Proof using.
    split; [intros st Lc FF M mdl a W R H; exact (OBL_nolazy_rt_pf st Lc FF W M mdl a R H)|].
    split; [intros st Lc FF L1 L2 p n a W HL H; exact (OBL_freed_private_pf st Lc FF W L1 L2 p n a HL H)|].
    split; [intros st Lc FF a W H; exact (OBL_rt_private_pf st Lc FF W a H)|].
    split; [intros st Lc FF p n W H; exact (OBL_blk_geom_pf st Lc FF W p n H)|].
    split; [intros st Lc FF b p n W Hb H; exact (OBL_batch_geom_pf st Lc FF W b p n Hb H)|].
    split; [intros st Lc FF M mdl p n W R H; exact (OBL_hdr_writable_pf st Lc FF W M mdl p n R H)|].
    split; [intros st Lc FF p n id a W H Hid Ha; exact (OBL_X_vs_node_pf st Lc FF W p n id a H Hid Ha)|].
    intros st Lc FF blk a W Hb Ha; exact (OBL_store_private_pf st Lc FF W blk a Hb Ha).
  Qed.

  Theorem OBL_stats_not_rep_wf : forall st Lc FF a, WF bt st Lc FF ->
    bt_thread bt + 2768 <= a < bt_thread bt + 3168 -> ~ rep_cells bt st Lc FF a.
  Proof using. intros st Lc FF a W H. exact (OBL_stats_not_rep_pf st Lc FF W a H). Qed.


  Theorem free_obls_pf : free_obls bt.
  Proof using.
    pose proof OBL_stats_not_rep_wf as ST. destruct free_obls_but_stats_pf as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    (lazymatch goal with |- ?G => let G' := eval unfold free_obls in G in change_no_check G' end). repeat (split; [assumption|]). exact A8.
  Qed.
End Free.
