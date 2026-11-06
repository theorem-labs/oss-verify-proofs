(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanClient
  AsanRepFrame AsanDepot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RF2.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation IC := (ae_ic E).
#[warnings="-notation-for-abbreviation"] Notation INST := (ae_instance E).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation RI := (ae_region_info E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation IMGR := (arep_img_ranges E).
#[warnings="-notation-for-abbreviation"] Notation THRR := (arep_thr_ranges E).

(* [comment removed for export] *)
Ltac zconsts Hx := unfold kInsSpaceBeg, kInsSecondary, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kInsQuarantine, kInsQMutex,
  kInsQGlobal, kInsFallbackMutex, kInsMaxUserDefined, kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats,
  kThrStats, kThrUnwinding, kRegSize, kBatchCap, kChunksBlockCount, kIaPageSizeOff in Hx |- *.
(* [comment removed for export] *)
Ltac ag AG ARM := let Hx := fresh "Hx" in intros x Hx; cbn -[Z.add Z.mul Z.sub Z.of_nat Z.to_nat free_array region_beg region_of get_region Z.pow] in Hx; apply AG; ARM Hx.
Ltac agN AG k := ag AG ltac:(fun Hx => eexists; split; [eapply nth_error_In with (n := k); reflexivity| cbn [fst snd length asan_flags_bytes]; zconsts Hx; lia]).

Section FR.
Variables (s : astate) (m m' : mem).
Hypothesis WM : wmono segs m m'.

(* [comment removed for export] *)
Hypothesis AGimg : forall a, in_ranges IMGR a -> m' (wa a) = m (wa a).
Lemma frameA' : arep_instance segs E s m -> arep_instance segs E s m'.
Proof.
  clear WM. intros RA. destruct RA as (A1 & A2 & A3 & A4 & (bsl & A5 & L5) & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  unfold arep_instance. repeat match goal with |- _ /\ _ => split end.
  all: try (exists bsl; split; [| exact L5]).
  all: first [ eapply rw_cells_agree'; [| eassumption]; agN AGimg 0%nat
             | eapply u64arr_agree; [| eassumption]; rewrite ?L5; agN AGimg 0%nat ].
Qed.
Lemma frameI' : arep_globals segs E s m -> arep_globals segs E s m'.
Proof.
  intros RI'. destruct RI' as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18). unfold arep_globals.
  split; [eapply u8arr_agree; [| exact I1]; agN AGimg 1%nat|].
  split; [eapply rw_cells_agree'; [| exact I2]; agN AGimg 2%nat|].
  split; [eapply rw_cells_agree'; [| exact I3]; agN AGimg 3%nat|].
  split; [eapply rw_cells_agree'; [| exact I4]; agN AGimg 4%nat|].
  split; [eapply rw_cells_agree'; [| exact I5]; agN AGimg 5%nat|].
  split; [eapply rw_cells_agree'; [| exact I6]; agN AGimg 6%nat|].
  split; [eapply rw_cells_agree'; [| exact I7]; agN AGimg 7%nat|].
  split; [eapply rw_cells_agree'; [| exact I8]; agN AGimg 8%nat|].
  split; [eapply rw_cells_agree'; [| exact I9]; agN AGimg 9%nat|].
  split; [eapply rw_cells_agree'; [| exact I10]; agN AGimg 10%nat|].
  split; [eapply rw_cells_agree'; [| exact I11]; agN AGimg 11%nat|].
  split; [eapply rw_cells_agree'; [| exact I12]; agN AGimg 12%nat|].
  split; [eapply rw_cells_agree'; [| exact I13]; agN AGimg 13%nat|].
  split; [eapply u64arr_agree; [| exact I14]; agN AGimg 14%nat|].
  split; [eapply rw_cells_agree'; [| exact I15]; agN AGimg 15%nat|].
  split; [intros Hia; eapply rw_cells_agree'; [| exact (I16 Hia)]; agN AGimg 16%nat|].
  split.
  { eapply u8arr_agree; [| exact I17]. intros x Hx. rewrite zeros_ia_len in Hx.
    apply AGimg. eexists; split; [eapply nth_error_In with (n := 16%nat); reflexivity| cbn [fst snd]; zconsts Hx; clear -Hx; lia]. }
  eapply wr_at_transport; [exact I18| exact WM].
Qed.

(* [comment removed for export] *)
Hypothesis AGri : forall a, RI <= a < RI + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Lemma frameB' : arep_regioninfo segs E s m -> arep_regioninfo segs E s m'.
Proof.
  clear WM AGimg. intros RB. unfold arep_regioninfo in *. intros c Hc. eapply rw_cells_agree'; [| exact (RB c Hc)]. unfold kNumClasses in Hc.
  ag AGri ltac:(fun Hx => zconsts Hx; lia).
Qed.

(* [comment removed for export] *)
Hypothesis AGfa : forall a c, 0 <= c < kNumClasses -> free_array SB c <= a < free_array SB c + rg_mapped_fa (region_of s c) -> m' (wa a) = m (wa a).
Lemma frameC' : arep_region_mem segs E s m -> arep_region_mem segs E s m'.
Proof.
  clear AGimg AGri. intros RC. unfold arep_region_mem in *. intros c Hc. destruct (RC c Hc) as (W & junk & U & L). split.
  - eapply wr_at_transport; [exact W| exact WM].
  - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact U].
    intros x Hx. rewrite length_app, length_map in Hx. apply (AGfa x c Hc). unfold kNumClasses in Hc. zconsts Hx. lia.
Qed.

(* [comment removed for export] *)
Hypothesis AGthr : forall a, in_ranges THRR a -> m' (wa a) = m (wa a).
Lemma frameD' : arep_thread segs E s m -> arep_thread segs E s m'.
Proof.
  clear WM AGimg AGri AGfa. intros RD. destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8). unfold arep_thread.
  split; [eapply rw_cells_agree'; [| exact D1]; agN AGthr 0%nat|].
  split; [eapply rw_cells_agree'; [| exact D2]; agN AGthr 1%nat|].
  split; [eapply rw_cells_agree'; [| exact D3]; agN AGthr 2%nat|].
  split.
  { intros c Hc. destruct (D4 c Hc) as (X1 & junk & X2 & L). unfold kNumClasses in Hc. split.
    - eapply rw_cells_agree'; [| exact X1]. unfold percls_cells. agN AGthr 3%nat.
    - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2].
      ag AGthr ltac:(fun Hx => eexists; split; [eapply nth_error_In with (n := 3%nat); reflexivity| cbn [fst snd]; rewrite length_app, length_map in Hx; zconsts Hx; lia]). }
  split; [eapply rw_cells_agree'; [| exact D5]; agN AGthr 4%nat|].
  split; [eapply u64arr_agree; [| exact D6]; ag AGthr ltac:(fun Hx => eexists; split; [eapply nth_error_In with (n := 5%nat); reflexivity| cbn [fst snd]; zconsts Hx; lia])|].
  split; [eapply u64arr_agree; [| exact D7]; ag AGthr ltac:(fun Hx => eexists; split; [eapply nth_error_In with (n := 5%nat); reflexivity| cbn [fst snd]; zconsts Hx; lia])|].
  eapply rw_cells_agree'; [| exact D8]; agN AGthr 6%nat.
Qed.

(* [comment removed for export] *)
Hypothesis AGptr : forall a, ae_ptr_array E <= a < ae_ptr_array E + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Hypothesis AGsec : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Lemma frameE' : arep_secondary segs E s m -> arep_secondary segs E s m'.
Proof.
  clear AGimg AGri AGfa AGthr. intros RE. destruct RE as [E1 E2]. unfold arep_secondary. split.
  - destruct E1 as [E1|(E11 & junk & U & L)]; [left; exact E1| right]. split; [exact E11|]. exists junk. split; [| exact L].
    eapply u64arr_agree; [| exact U].
    pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). clear L.
    intros x Hx. rewrite length_app, length_map in Hx. apply AGptr. unfold kChunksBlockCount in L' |- *. lia.
  - intros i c Hi. destruct (E2 i c Hi) as [X1 X2]. split; [| eapply wr_at_transport; [exact X2| exact WM]].
    eapply rw_cells_agree'; [| exact X1]. intros x Hx. cbn in Hx. apply (AGsec x c); [eapply nth_error_In; exact Hi| lia].
Qed.

(* [comment removed for export] *)
Hypothesis AGcm : forall a cb cm, as_chunks s !! cb = Some cm -> chunk_meta_fp cm a -> m' (wa a) = m (wa a).
Lemma frameF' : arep_chunks segs s m -> arep_chunks segs s m'.
Proof.
  clear WM AGimg AGri AGfa AGthr AGptr AGsec. intros RF. unfold arep_chunks in *. intros cb cm Hcm. destruct (RF cb cm Hcm) as (X0 & (b1 & Hb1 & X1) & X2 & X3). split; [exact X0|].
  split; [| split].
  - exists b1. split; [exact Hb1|]. eapply rw_cells_agree'; [| exact X1]. intros x Hx. cbn in Hx. apply (AGcm x cb cm Hcm). left; lia.
  - intros Hrz. eapply rw_cells_agree'; [| exact (X2 Hrz)]. intros x Hx. cbn in Hx. apply (AGcm x cb cm Hcm). right; left; split; [exact Hrz| lia].
  - destruct (cm_state cm) as [i|i j] eqn:ST; [exact I|].
    eapply rw_cells_agree'; [| exact X3]. intros x Hx. cbn in Hx. apply (AGcm x cb cm Hcm). right; right; rewrite ST; lia.
Qed.

(* [comment removed for export] *)
Hypothesis AGbat : forall a b, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Lemma frameG' : arep_batches segs s m -> arep_batches segs s m'.
Proof.
  clear WM AGimg AGri AGfa AGthr AGptr AGsec AGcm. intros RG.
  assert (BL : forall l, (forall b, In b l -> In b (as_tq s ++ as_gq s)) -> arep_batch_list segs s l m -> arep_batch_list segs s l m').
  { induction l as [|b l IH]; intros SUB H; [exact I|]. destruct H as [[X1 (junk & X2 & L)] H2]. split; [| apply IH; [intros b' Hb'; apply SUB; right; exact Hb'| exact H2]].
    split.
    - eapply rw_cells_agree'; [| exact X1]. intros x Hx. cbn -[Z.add Z.mul] in Hx. apply (AGbat x b); [apply SUB; left; reflexivity| zconsts Hx; lia].
    - exists junk. split; [| exact L]. eapply u64arr_agree; [| exact X2].
      pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). clear L.
      intros x Hx. rewrite length_app, length_map in Hx. apply (AGbat x b); [apply SUB; left; reflexivity| unfold kBatchCap in L' |- *; lia]. }
  destruct RG as [G1 G2]. split; (apply BL; [| assumption]); intros b Hb; apply in_app_iff; [left| right]; exact Hb.
Qed.

(* [comment removed for export] *)
Hypothesis AGdep : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Lemma frameH' : arep_depot (DepotR segs E) s m -> arep_depot (DepotR segs E) s m'.
Proof. clear AGimg AGri AGfa AGthr AGptr AGsec AGcm AGbat. intros RH. unfold arep_depot in *. eapply DepotR_frame; [exact RH| exact WM| exact AGdep]. Qed.

(* [comment removed for export] *)
Hypothesis AGsh : forall g v, Sh E s (8 * g) = Some v -> m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Lemma frameJ' : arep_shadow segs E s m -> arep_shadow segs E s m'.
Proof.
  clear WM AGimg AGri AGfa AGthr AGptr AGsec AGcm AGbat AGdep. intros RJ. unfold arep_shadow in *. intros g v Hg. eapply rw_cells_agree'; [| exact (RJ g v Hg)].
  intros x Hx. cbn in Hx. replace x with (kShadowBase + g) by lia. exact (AGsh g v Hg).
Qed.
End FR.
End RF2.
End RC__1.
