(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma writableZ_local : forall SEGS M M' lo hi, writableZ SEGS M lo hi -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> writableZ SEGS M' lo hi.
Proof.
  intros SEGS M M' lo hi W H0 H1 AG. apply (writableZ_frame SEGS M M' lo hi W). intros i Hi. left. apply AG; lia.
Qed.
Ltac frWL AG H := eapply (writableZ_local _ _ _ _ _ H); [lia | lia | let i := fresh "i" in let Hi := fresh "Hi" in let Hr := fresh "Hr" in intros i Hi Hr; apply AG; [| exact Hr]; first [lia | eauto 7 | idtac]].

Section Groups.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (M M' : mem).
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).

  (* [comment removed for export] *)
  Definition instance_supp (a : Z) : Prop := instance_cells bt st a \/ (bt_ptrarr bt <= a < bt_ptrarr bt + 8 * a_nres st).
  Lemma rep_instance_local :
    rep_instance bt st M ->
    0 <= IB bt + 112 -> IB bt + 985 < 2 ^ 64 -> 0 <= bt_ptrarr bt -> bt_ptrarr bt + 8 * a_nres st < 2 ^ 64 ->
    Z.of_nat (length (a_sec st)) <= a_nres st ->
    (forall i, instance_supp i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_instance bt st M'.
  Proof using.
    intros (I1 & I2 & I3 & I4 & I5 & I6 & IL & IP & IW) R1 R2 R3 R4 R5 AG. unfold rep_instance, instance_supp, instance_cells in *.
    split; [frZ AG I1|]. split; [frZ AG I2|]. split; [frB AG I3|]. split; [frB AG I4|]. split; [frB AG I5|]. split; [frB AG I6|].
    split. { eapply rep_list_frame; [exact IL | lia | lia |]. intros i Hi Hr. apply AG; lia. }
    split. { intros i s Hs. pose proof (nth_error_lt _ _ _ Hs) as Hl. pose proof (IP i s Hs) as C. frZ AG C. }
    frWL AG IW.
  Qed.

  (* [comment removed for export] *)
  Definition thread_supp (a : Z) : Prop := thread_cells bt a \/ (T <= a < T + PG).
  Lemma rep_thread_local :
    rep_thread bt st M ->
    0 <= T -> T + PG < 2 ^ 64 -> 0 <= bt_tctx bt -> bt_tctx bt + 160 < 2 ^ 64 ->
    (forall c, 1 <= c <= 30 -> Z.of_nat (length (a_cache st c)) <= 16) ->
    (forall i, thread_supp i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_thread bt st M'.
  Proof using.
    intros (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TW & C1 & C2 & C3 & C4) R1 R2 R3 R4 CL AG. unfold rep_thread, thread_supp, thread_cells in *.
    unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
    split; [frZ AG T1|]. split; [frZ AG T2|]. split; [frZ AG T3|]. split; [frB AG T4|]. split; [frZ AG T5|]. split; [frB AG T6|].
    split. { eapply rep_list_frame; [exact TL | lia | lia |]. intros i Hi Hr. apply AG; lia. }
    split. { intros c Hc. pose proof (CL c Hc). eapply rep_pclass_frame; [exact (TP c Hc) | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); lia | lia |].
             (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). intros i Hi Hr. apply AG; [|lia]. nia. }
    split; [frWL AG TW|]. split; [frZ AG C1|]. split; [frZ AG C2|]. split; [frZ AG C3 | frZ AG C4].
  Qed.

  (* [comment removed for export] *)
  Definition region_supp (c : Z) (i : Z) : Prop :=
    (reginfo bt c <= i < reginfo bt c + 128)
    \/ (fa_beg SBEG c <= i < fa_beg SBEG c + r_mapped_fa (a_reg st c))
    \/ (region_beg SBEG c <= i < region_beg SBEG c + r_mapped_user (a_reg st c)).
  Lemma rep_region_local : forall c,
    rep_reginfo bt M c (a_reg st c) -> rep_freearray bt M c (a_reg st c) ->
    0 <= reginfo bt c -> reginfo bt c + 128 < 2 ^ 64 -> 0 <= fa_beg SBEG c -> fa_beg SBEG c + r_mapped_fa (a_reg st c) < 2 ^ 64 ->
    0 <= region_beg SBEG c -> region_beg SBEG c + r_mapped_user (a_reg st c) < 2 ^ 64 ->
    4 * Z.of_nat (length (r_free (a_reg st c))) <= r_mapped_fa (a_reg st c) ->
    (forall i, region_supp c i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_reginfo bt M' c (a_reg st c) /\ rep_freearray bt M' c (a_reg st c).
  Proof using.
    intros c (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GW) (F1 & F2 & F3) R1 R2 R3 R4 R5 R6 R7 AG. unfold region_supp in AG.
    split.
    - (lazymatch goal with |- ?G => let G' := eval unfold rep_reginfo in G in change_no_check G' end).
      split; [frZ AG G1|]. split; [frZ AG G2|]. split; [frZ AG G3|]. split; [frZ AG G4|]. split; [frZ AG G5|].
      split; [frZ AG G6|]. split; [frZ AG G7|]. split; [frZ AG G8|]. split; [frB AG G9|]. frWL AG GW.
    - (lazymatch goal with |- ?G => let G' := eval unfold rep_freearray in G in change_no_check G' end). split; [| split; [frWL AG F2 | frWL AG F3]].
      intros i k Hk. pose proof (nth_error_lt _ _ _ Hk) as Hl. pose proof (F1 i k Hk) as C. frZ AG C.
  Qed.

  (* [comment removed for export] *)
  Definition batch_supp (b : batch) (i : Z) : Prop := ba_addr b <= i < ba_addr b + BATCHSZ.
  Lemma rep_batches_local : forall q,
    rep_batches bt M q ->
    (forall b, In b q -> 0 <= ba_addr b /\ ba_addr b + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b)) <= BATCHCAP) ->
    (forall b i, In b q -> batch_supp b i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_batches bt M' q.
  Proof using.
    intros q RB RNG AG i b Hb. pose proof (nth_error_In _ _ Hb) as Hin. destruct (RNG b Hin) as (R1 & R2 & R3).
    destruct (RB i b Hb) as (B1 & B2 & B3 & B4 & BW). unfold batch_supp, BATCHSZ, BATCHCAP in *.
    assert (AGb : forall i0, ba_addr b <= i0 < ba_addr b + 8192 -> 0 <= i0 < 2 ^ 64 ->
                  M' (Z_to_bv 64 i0) = M (Z_to_bv 64 i0)) by (intros i0 H0 H1; exact (AG b i0 Hin H0 H1)).
    split; [frZ AGb B1|]. split; [frZ AGb B2|]. split; [frZ AGb B3|]. split; [| frWL AGb BW].
    intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Hl. pose proof (B4 j mn Hj) as C. frZ AGb C.
  Qed.

  (* [comment removed for export] *)
  Definition sec_supp (sc : schunk) (i : Z) : Prop := sc_map sc <= i < sc_map sc + sc_mapsz sc.
  Lemma rep_secondary_local :
    rep_secondary bt st M ->
    (forall sc, In sc (a_sec st) -> 0 <= sc_map sc /\ sc_map sc + sc_mapsz sc < 2 ^ 64 /\ 32 <= sc_mapsz sc) ->
    (forall sc i, In sc (a_sec st) -> sec_supp sc i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_secondary bt st M'.
  Proof using.
    intros RS RNG AG i sc Hs. pose proof (nth_error_In _ _ Hs) as Hin. destruct (RNG sc Hin) as (R1 & R2 & R3).
    destruct (RS i sc Hs) as (S1 & S2 & S3 & S4 & SW). unfold sec_supp in *.
    assert (AGs : forall i0, sc_map sc <= i0 < sc_map sc + sc_mapsz sc -> 0 <= i0 < 2 ^ 64 -> M' (Z_to_bv 64 i0) = M (Z_to_bv 64 i0))
      by (intros i0 H0 H1; exact (AG sc i0 Hin H0 H1)).
    split; [frZ AGs S1|]. split; [frZ AGs S2|]. split; [frZ AGs S3|]. split; [frZ AGs S4|]. frWL AGs SW.
  Qed.

  (* [comment removed for export] *)
  Definition hdr_supp (p n : Z) (i : Z) : Prop := foot_hdr p n i \/ (p - 8 <= i < p).
  Lemma rep_hdr_local : forall p n s,
    rep_hdr bt M p n s -> rz n <= p -> p < 2 ^ 64 - 16 ->
    (forall i, hdr_supp p n i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_hdr bt M' p n s.
  Proof using.
    intros p n s (H1 & (b1 & Hb1 & H2) & H3 & H4 & HW & H5 & HL) R1 R2 AG. pose proof (rz_range n) as RZ. unfold hdr_supp, foot_hdr in AG. (lazymatch goal with |- ?G => let G' := eval unfold rep_hdr in G in change_no_check G' end).
    split; [frB AG H1|]. split; [exists b1; split; [exact Hb1 | frB AG H2]|]. split; [frZ AG H3|]. split; [frZ AG H4|]. split; [frWL AG HW|]. split; [frZ AG H5|].
    intros Hrz. destruct (HL Hrz) as [L1 L2]. split; [frZ AG L1 | frZ AG L2].
  Qed.
  Lemma rep_headers_local :
    rep_headers bt st Lc M ->
    (forall p n, In (p, n) Lc -> rz n <= p /\ p < 2 ^ 64 - 16) ->
    (forall m n, In (m, n) (quar st) -> rz n <= m + 16 /\ m + 16 < 2 ^ 64 - 24) ->
    (forall p n i, In (p, n) Lc -> hdr_supp p n i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall m n i, In (m, n) (quar st) -> hdr_supp (m + 16) n i \/ (m + 16 <= i < m + 24) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_headers bt st Lc M'.
  Proof using.
    intros [HLc HQ] RL RQ AGL AGQ. split.
    - intros p n Hin. destruct (RL p n Hin) as [R1 R2]. eapply rep_hdr_local; [exact (HLc p n Hin) | lia | lia |].
      intros i Hi Hr. exact (AGL p n i Hin Hi Hr).
    - intros m n Hin. destruct (RQ m n Hin) as [R1 R2]. destruct (HQ m n Hin) as [Hh HW]. pose proof (rz_range n). split.
      + eapply rep_hdr_local; [exact Hh | lia | lia |]. intros i Hi Hr. exact (AGQ m n i Hin (or_introl Hi) Hr).
      + eapply (writableZ_local _ _ _ _ _ HW); [lia | lia |]. intros i Hi Hr. exact (AGQ m n i Hin (or_intror Hi) Hr).
  Qed.

  (* [comment removed for export] *)
  Lemma rep_depot_local :
    rep_depot bt st M ->
    0 <= DEPOT_TAB bt -> DEPOT_TAB bt + 0x400010 + 8 * 2 ^ 15 < 2 ^ 64 -> 0 <= SSOBJ bt -> SSOBJ bt + 16 + 16 * 2 ^ 12 < 2 ^ 64 ->
    (forall id, 1 <= id <= dp_nids (a_dep st) -> 0 <= node_addr bt (a_dep st) id /\ node_addr bt (a_dep st) id + 16 < 2 ^ 64) ->
    (forall b, In b (node_blocks bt (a_dep st)) -> 0 <= b /\ b + 2 ^ 20 <= 2 ^ 64) ->
    (forall b, In b (store_blocks bt (a_dep st)) -> 0 <= b /\ b + 2 ^ 23 <= 2 ^ 64) ->
    (forall i, foot_depot_static bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall id i, 1 <= id <= dp_nids (a_dep st) -> foot_node bt (a_dep st) id i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall b i, In b (node_blocks bt (a_dep st)) -> b <= i < b + 2 ^ 20 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall b i, In b (store_blocks bt (a_dep st)) -> b <= i < b + 2 ^ 23 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_depot bt st M'.
  Proof using.
    intros (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9) R1 R2 R3 R4 RN RNB RSB AG AGN AGB AGS.
    unfold foot_depot_static, foot_node, DEPOT_NIDS, DEPOT_MAP1 in *. (lazymatch goal with |- ?G => let G' := eval unfold rep_depot, DEPOT_NIDS, DEPOT_MAP1 in G in change_no_check G' end).
    split. { intros i Hi. pose proof (D1 i Hi) as C. frZ AG C. }
    split; [frZ AG D2|]. split; [frB AG D3|].
    split. { intros i Hi. pose proof (D4 i Hi) as C. frZ AG C. }
    split. { intros id Hid. destruct (RN id Hid) as [N1 N2]. destruct (D5 id Hid) as (C1 & C2 & C3).
             assert (AGi : forall i, node_addr bt (a_dep st) id <= i < node_addr bt (a_dep st) id + 16 -> 0 <= i < 2 ^ 64 ->
                           M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) by (intros i H0 H1; exact (AGN id i Hid H0 H1)).
             split; [frZ AGi C1|]. split; [frZ AGi C2|]. frZ AGi C3. }
    split. { intros b Hb. destruct (RNB b Hb) as [B0 B1]. eapply (writableZ_local _ _ _ _ _ (D6 b Hb)); [lia | lia |]. intros i Hi Hr. exact (AGB b i Hb Hi Hr). }
    split; [frZ AG D7|].
    split. { intros i Hi. destruct (D8 i Hi) as (C1 & C2 & C3). split; [frZ AG C1|]. split; [frZ AG C2|]. frB AG C3. }
    intros b Hb. destruct (RSB b Hb) as [B0 B1]. eapply (writableZ_local _ _ _ _ _ (D9 b Hb)); [lia | lia |]. intros i Hi Hr. exact (AGS b i Hb Hi Hr).
  Qed.

  (* [comment removed for export] *)
  Lemma rep_fake_local :
    rep_fake bt st FF M ->
    0 <= bt_fs bt -> bt_fs bt + FAKE_SIZE < 2 ^ 64 -> 0 <= bt_tls_fs bt -> bt_tls_fs bt + 16 < 2 ^ 64 -> 0 <= bt_dtls bt -> bt_dtls bt + 32 < 2 ^ 64 ->
    (forall f k, In (f, k) FF -> bt_fs bt + 0x9000 <= f /\ f + FS k <= bt_fs bt + FAKE_SIZE /\ 8 <= FS k) ->
    (forall i, foot_fake_static bt i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall i, bt_fs bt <= i < bt_fs bt + FAKE_SIZE -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_fake bt st FF M'.
  Proof using.
    intros (K1 & K2 & K3 & K4 & KW & KT & KS & KD1 & KD2) R1 R2 R3 R4 R5 R6 RF AG AGW. unfold foot_fake_static, FAKE_SIZE in *. (lazymatch goal with |- ?G => let G' := eval unfold rep_fake in G in change_no_check G' end).
    split. { intros k Hk. pose proof (K1 k Hk) as C. frZ AG C. }
    split; [frB AG K2|].
    split. { intros k pos Hk Hp. pose proof (flag_addr_range (bt_fs bt) k pos Hk Hp) as FR. pose proof (K3 k pos Hk Hp) as C. frB AG C. }
    split. { intros f k Hin. destruct (RF f k Hin) as (F1 & F2 & F3). pose proof (K4 f k Hin) as C.
             eapply (cellZ_frame _ _ _ _ _ _ C); [lia | lia |]. intros i Hi. apply AGW; lia. }
    split; [frWL AGW KW|]. split; [frZ AG KT|]. split; [frZ AGW KS|]. split; [frZ AG KD1 | frZ AG KD2].
  Qed.

  (* [comment removed for export] *)
  Definition shreg_supp (c : Z) (i : Z) : Prop :=
    foot_shreg bt st Lc c i \/ (sh_lo (region_beg SBEG c) <= i < SB + (region_beg SBEG c + r_mapped_user (a_reg st c)) / 8).
  Definition shsec_supp (sc : schunk) (i : Z) : Prop :=
    foot_shsec st sc i \/ (sh_lo (sc_map sc) <= i < SB + (sc_map sc + sc_mapsz sc) / 8).
  Lemma rep_shadow_local :
    rep_shadow bt st Lc M ->
    (forall c, 1 <= c <= 30 -> 0 <= region_beg SBEG c /\ region_beg SBEG c + r_mapped_user (a_reg st c) <= CEIL
                            /\ 0 <= fa_beg SBEG c /\ fa_beg SBEG c + r_mapped_fa (a_reg st c) <= CEIL) ->
    (forall sc, In sc (a_sec st) -> 0 <= sc_map sc /\ sc_map sc + sc_mapsz sc <= CEIL /\ sc_map sc <= sc_user sc /\ sc_user sc + sc_n sc <= sc_map sc + sc_mapsz sc
                                    /\ (sc_map sc + sc_mapsz sc) mod 8 = 0) ->
    (forall c i, 1 <= c <= 30 -> shreg_supp c i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall sc i, In sc (a_sec st) -> shsec_supp sc i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    rep_shadow bt st Lc M'.
  Proof using.
    intros (S1 & S2 & S3 & S4 & S5 & S6) RC RS AG AGS. (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end). ceil; unfold shreg_supp, shsec_supp, foot_shreg, foot_shsec, user_granule, sh_lo, SB in *.
    split. { intros c g Hc Hg NL. destruct (RC c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (S1 c g Hc Hg NL) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [lia | lia |]. apply (AG c); [exact Hc | | lia]. left. left.
             replace (0x7fff8000 + g - 0x7fff8000) with g by lia. split; [lia | exact NL]. }
    split. { intros c g Hc Hg. destruct (RC c Hc) as (Q1 & Q2 & Q3 & Q4). pose proof (S2 c g Hc Hg) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [lia | lia |]. apply (AG c); [exact Hc | left; right; lia | lia]. }
    split. { intros sc g Hs Hg NU. destruct (RS sc Hs) as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (S3 sc g Hs Hg NU) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [lia | lia |]. apply (AGS sc); [exact Hs | | lia]. left.
             replace (0x7fff8000 + g - 0x7fff8000) with g by lia. split; [lia | left; exact NU]. }
    split. { intros sc g Hs HQ HU. destruct (RS sc Hs) as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof (S4 sc g Hs HQ HU) as C.
             eapply (byteZ_frame _ _ _ _ _ C); [lia | lia |]. apply (AGS sc); [exact Hs | | lia]. left.
             replace (0x7fff8000 + g - 0x7fff8000) with g by lia. split; [lia | right; exact HQ]. }
    split. { intros c g Hc Hg. destruct (RC c Hc) as (Q1 & Q2 & Q3 & Q4).
             rewrite (AG c (0x7fff8000 + g) Hc ltac:(right; lia) ltac:(lia)). exact (S5 c g Hc Hg). }
    intros sc g Hs Hg. destruct (RS sc Hs) as (Q1 & Q2 & Q3 & Q4 & Q5).
    rewrite (AGS sc (0x7fff8000 + g) Hs ltac:(right; lia) ltac:(lia)). exact (S6 sc g Hs Hg).
  Qed.
End Groups.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Local.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).

  (* [comment removed for export] *)
  Definition rep_wr (st : ast) (Lc FF : list (Z * Z)) (a : Z) : Prop :=
    (bt_ptrarr bt <= a < bt_ptrarr bt + 8 * a_nres st)
    \/ (T <= a < T + PG)
    \/ (exists c, 1 <= c <= 30 /\ ((reginfo bt c <= a < reginfo bt c + 128)
                                  \/ (fa_beg SBEG c <= a < fa_beg SBEG c + r_mapped_fa (a_reg st c))
                                  \/ (region_beg SBEG c <= a < region_beg SBEG c + r_mapped_user (a_reg st c))))
    \/ (exists b, In b (a_tq st ++ a_gq st) /\ ba_addr b <= a < ba_addr b + BATCHSZ)
    \/ (exists sc, In sc (a_sec st) /\ sc_map sc <= a < sc_map sc + sc_mapsz sc)
    \/ (exists p n, In (p, n) Lc /\ (p - 8 <= a < p + n \/ sh_lo p <= a < sh_hi p n))
    \/ (exists m n, In (m, n) (quar st) /\ m + 8 <= a < m + 24)
    \/ (exists b, In b (node_blocks bt (a_dep st)) /\ b <= a < b + 2 ^ 20)
    \/ (exists b, In b (store_blocks bt (a_dep st)) /\ b <= a < b + 2 ^ 23)
    \/ (bt_fs bt <= a < bt_fs bt + FAKE_SIZE)
    \/ (exists f k, In (f, k) FF /\ sh_lo f <= a < sh_hi f (FS k))
    \/ (exists c, 1 <= c <= 30 /\ sh_lo (region_beg SBEG c) <= a < SB + (region_beg SBEG c + r_mapped_user (a_reg st c)) / 8)
    \/ (exists sc, In sc (a_sec st) /\ sh_lo (sc_map sc) <= a < SB + (sc_map sc + sc_mapsz sc) / 8)
    \/ shmaps a.
  Definition rep_supp (st : ast) (Lc FF : list (Z * Z)) (a : Z) : Prop := rep_cells bt st Lc FF a \/ rep_wr st Lc FF a.

  Tactic Notation "pickc" integer(n) := left; do n right; left.
  Tactic Notation "pickw" integer(n) := right; do n right; left.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  Theorem Rep_local : forall st Lc FF M M' mdl {qt qg : Z},
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M mdl ->
    (forall i, rep_supp st Lc FF i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    Rep bt st Lc FF M' mdl.
  Proof using.
    intros st Lc FF M M' mdl qt qg W R AG.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & YC).
    ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in *.
    pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _).
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    unfold Rep, rep_supp, rep_wr in *.
    split. { (* [comment removed for export] *) eapply cells_hold_frame; [exact R1 | exact YC |]. intros c i Hc Hi.
             rewrite Forall_forall in YC. destruct (YC c Hc). apply AG; [| ulia]. pickc 0. exists c. split; assumption. }
    split. { (* [comment removed for export] *)
             eapply rep_instance_local; [exact R2 | ulia | ulia | ulia | ulia | exact S1 |].
             intros i [Hi|Hi] Hr; apply AG; [pickc 1; exact Hi | exact Hr | pickw 0; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_thread_local; [exact R3 | ulia | ulia | ulia | ulia | exact (cache_len bt st Lc FF W) |].
             intros i [Hi|Hi] Hr; apply AG; [pickc 2; exact Hi | exact Hr | pickw 1; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) intros c Hc. destruct (R4 c Hc) as [G F]. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
             destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
             eapply rep_region_local; [exact G | exact F | ulia | ulia | ulia | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. unfold region_supp in Hi.
             destruct Hi as [Hi | [Hi | Hi]].
             - destruct (decide (reginfo bt c + 64 <= i < reginfo bt c + 68)) as [J|J].
               + apply AG; [pickw 2; exists c; split; [exact Hc | left; lia] | exact Hr].
               + destruct (decide (i < reginfo bt c + 72)) as [J2|J2].
                 * apply AG; [pickc 3; exists c; split; [exact Hc | left; split; [lia | exact J]] | exact Hr].
                 * apply AG; [pickw 2; exists c; split; [exact Hc | left; lia] | exact Hr].
             - apply AG; [pickw 2; exists c; split; [exact Hc | right; left; exact Hi] | exact Hr].
             - apply AG; [pickw 2; exists c; split; [exact Hc | right; right; exact Hi] | exact Hr]. }
    assert (BR : forall b, In b (a_tq st ++ a_gq st) -> 0 <= ba_addr b /\ ba_addr b + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b)) <= BATCHCAP).
    { intros b Hb. destruct (batch_facts bt st Lc FF W b Hb) as (_ & L1 & L2 & L3). unfold BATCHSZ in *. repeat split; ulia. }
    split. { (* [comment removed for export] *) eapply rep_batches_local; [exact R5 | intros b Hb; apply BR; apply in_app_iff; left; exact Hb |].
             intros b i Hb Hi Hr. apply AG; [pickw 3; exists b; split; [apply in_app_iff; left; exact Hb | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_batches_local; [exact R6 | intros b Hb; apply BR; apply in_app_iff; right; exact Hb |].
             intros b i Hb Hi Hr. apply AG; [pickw 3; exists b; split; [apply in_app_iff; right; exact Hb | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_secondary_local; [exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). pose proof (rz_range (sc_n sc)). unfold sc_user, sec_user_off in *. ulia.
             - intros sc i Hs Hi Hr. apply AG; [pickw 4; exists sc; split; [exact Hs | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_headers_local; [exact R8 | | | |].
             - intros p n Hin. destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n). ulia.
             - intros m n Hin. destruct (quar_item_range bt st Lc FF W m n Hin) as (A1 & A2 & A3). pose proof (rz_range n). ulia.
             - intros p n i Hin [Hi|Hi] Hr; apply AG; [pickc 6; exists p, n; split; [left; exact Hin | exact Hi] | exact Hr | | exact Hr].
               pickw 5. exists p, n. split; [exact Hin|]. left. destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4). lia.
             - intros m n i Hin [[Hi|Hi]|Hi] Hr; apply AG; try exact Hr.
               + pickc 6. exists (m + 16), n. split; [right; replace (m + 16 - 16) with m by lia; exact Hin | exact Hi].
               + pickw 6. exists m, n. split; [exact Hin | lia].
               + pickw 6. exists m, n. split; [exact Hin | lia]. }
    split. { (* [comment removed for export] *) eapply rep_depot_local; [exact R9 | ulia | ulia | ulia | ulia | | | | | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). ulia.
             - intros b Hb. destruct (node_blocks_range bt st Lc FF W b Hb) as (A1 & A2 & _). ulia.
             - intros b Hb. destruct (store_blocks_range bt st Lc FF W b Hb) as (A1 & A2 & _). ulia.
             - intros i Hi Hr. apply AG; [pickc 7; exact Hi | exact Hr].
             - intros id i Hid Hi Hr. apply AG; [pickc 8; exists id; split; [exact Hid | exact Hi] | exact Hr].
             - intros b i Hb Hi Hr. apply AG; [pickw 7; exists b; split; [exact Hb | exact Hi] | exact Hr].
             - intros b i Hb Hi Hr. apply AG; [pickw 8; exists b; split; [exact Hb | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_local; [exact R10 | ulia | ulia | ulia | ulia | ulia | ulia | | |].
             - intros f k Hin. destruct (fake_frame_facts bt st Lc FF W f k Hin) as (A1 & A2 & A3 & A4 & _). (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end). ulia.
             - intros i Hi Hr. apply AG; [pickc 9; exact Hi | exact Hr].
             - intros i Hi Hr. apply AG; [pickw 9; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_ialloc_frame; [exact R11 | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. apply AG; [pickc 11; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_shadow_local; [exact R12 | | | |].
             - intros c Hc. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
               destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). ulia.
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros c i Hc [Hi|Hi] Hr; apply AG; [pickc 12; exists c; split; [exact Hc | exact Hi] | exact Hr | pickw 11; exists c; split; [exact Hc | exact Hi] | exact Hr].
             - intros sc i Hs [Hi|Hi] Hr; apply AG; [pickc 13; exists sc; split; [exact Hs | exact Hi] | exact Hr | pickw 12; exists sc; split; [exact Hs | exact Hi] | exact Hr]. }
    split; [exact R13|]. split; [exact R14|].
    split. { intros p n Hin. destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n).
             destruct (R15 p n Hin) as [W1 W2]. split.
             - eapply (writableZ_local _ _ _ _ _ W1); [ulia | ulia |]. intros i Hi Hr. apply AG; [pickw 5; exists p, n; split; [exact Hin | left; lia] | exact Hr].
             - eapply (writableZ_local _ _ _ _ _ W2); [(lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end); ulia | (lazymatch goal with |- ?G => let G' := eval unfold sh_hi in G in change_no_check G' end); ulia |]. intros i Hi Hr. apply AG; [pickw 5; exists p, n; split; [exact Hin | right; exact Hi] | exact Hr]. }
    split. { intros f k Hin. destruct (fake_frame_facts bt st Lc FF W f k Hin) as (A1 & A2 & A3 & A4 & _).
             eapply (writableZ_local _ _ _ _ _ (R16 f k Hin)); [unfold sh_lo, FAKE_SIZE in *; ulia | unfold sh_hi, FAKE_SIZE in *; ulia |].
             intros i Hi Hr. apply AG; [pickw 10; exists f, k; split; [exact Hin | exact Hi] | exact Hr]. }
    split. { eapply (cellZ_frame _ _ _ _ _ _ R17); [ulia | ulia |]. intros i Hi. apply AG; [left; do 14 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia | ulia]. }
    split. { eapply (cellZ_frame _ _ _ _ _ _ R18); [ulia | ulia |]. intros i Hi. apply AG; [left; do 14 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia | ulia]. }
    split.
    - intros z Hz. rewrite (AG z ltac:(right; do 13 right; exact Hz) ltac:(unfold shmaps, AS_GAPLO, AS_GAPHI in Hz; ulia)). exact (proj1 R19 z Hz).
    - intros NE a Ha. pose proof (bv_unsigned_in_range 64 a) as RA.
      assert (EA : Z_to_bv 64 (bv_unsigned a) = a) by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; exact RA).
      change (bv_modulus 64) with (2 ^ 64) in RA.
      rewrite <- EA. rewrite (AG (bv_unsigned a)); [rewrite EA; exact (proj2 R19 NE a Ha) | | lia].
      left. right. left. (lazymatch goal with |- ?G => let G' := eval unfold instance_cells in G in change_no_check G' end). cbn zeta. do 5 right. left. lia.
  Qed.
End Local.
