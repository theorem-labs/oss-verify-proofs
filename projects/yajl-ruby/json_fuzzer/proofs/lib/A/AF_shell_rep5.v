(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanRepFrame2 AsanDepot
  AsanWf1 AsanWf2 AsanWf3 AsanWf4.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require AsanRepHit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AF_fakestack_rep AX_unreg AX_Exit AF_statics AF_place A_bundle A_benv5 A_init5 A_instD5 A_balloc5 AF_alloc_iface AF_kit3 AF_tkit AF_caT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition IA : Z := 0xaed80.

Section ShellRep.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
(* [comment removed for export] *)
Hypothesis IMGE : fst (ae_img E0) = 0x10000 /\ 0x5f3000 <= snd (ae_img E0).
#[local, warnings="-notation-for-abbreviation"] Notation T := (ae_thread E0).
#[local, warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E0).
#[local, warnings="-notation-for-abbreviation"] Notation FP := (arep_fp E0 (DepotFP E0)).

Let IC0 : ae_ic E0 = asan_ic.
Proof. destruct ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC & _). exact IC. Qed.

(* [comment removed for export] *)
Definition shellW (a : Z) : Prop := (T <= a < T + 4096) \/ (IA <= a < IA + 0x81030) \/ (0x13d608 <= a < 0x13d60c).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XFER.
Variables (s : astate) (m m' : mem) (mo : Model).
Hypothesis WM : wmono asegs m m'.
Hypothesis AG : forall a, FP s a -> ~ shellW a -> m' (wa a) = m (wa a).
Hypothesis WF : AWf E0 [] [] s.
Hypothesis K : AKern E0 s mo.
Hypothesis BS : blocks_sep E0 s.

Ltac consts := rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in *; unfold kSpaceSize, kDepotNodeBlockBytes, kStoreBlockBytes, kPtrArrayLen, kResvLen, kPageSize, IA in *.

(* [comment removed for export] *)
Lemma Tfacts : placed_s T 4096 /\ (T + 4096 <= ae_depot_nodes E0 \/ ae_depot_nodes E0 + kDepotNodeBlockBytes <= T).
Proof.
  destruct PL0OK as (_ & _ & (_ & TR2 & _) & _). split; [exact TR2|].
  destruct ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TDN & _). exact TDN.
Qed.

(* [comment removed for export] *)
Lemma Tpage_apart : forall a, T <= a < T + 4096 ->
     ~ (ae_resv_beg E0 <= a < ae_resv_beg E0 + 0x2000011000)
  /\ ~ (ae_ptr_array E0 <= a < ae_ptr_array E0 + 0x800000)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall b len, (In b (ae_depot_nodes E0 :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E0 :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (b <= a < b + len))
  /\ ~ (kLowAppEnd < a < kHighMemBeg) /\ ~ (0x10000 <= a < 0x603000).
Proof.
  intros a Ha. pose proof WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & S3 & _). pose proof Tfacts as [Tpl TDN].
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & _).
  split; [clear -Ha E19; lia|]. split; [clear -Ha E23; lia|]. split.
  { intros sc Hsc. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof (RSV _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  split.
  { intros b len H. destruct H as [[[<-|Hb] ->]|[[<-|Hb] ->]].
    - clear -Ha TDN. lia.
    - destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia.
    - pose proof (ak_store_sep _ _ _ K) as (_ & _ & X & _). unfold kPageSize, kStoreBlockBytes in *. clear -Ha X. lia.
    - destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  unfold app_mem in E14. unfold placed_s, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Tpl. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *. destruct Tpl as (T1 & T2 & T3 & T4). clear -Ha E14 T1 T2 T3 T4. split; lia.
Qed.

(* [comment removed for export] *)
Lemma img_apart : forall a, 0x10000 <= a < 0x603000 ->
     ~ (ae_resv_beg E0 <= a < ae_resv_beg E0 + 0x2000011000)
  /\ ~ (ae_ptr_array E0 <= a < ae_ptr_array E0 + 0x800000)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall b len, (In b (ae_depot_nodes E0 :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E0 :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (b <= a < b + len))
  /\ ~ (kLowAppEnd < a < kHighMemBeg).
Proof.
  intros a Ha. pose proof WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & S3 & _). destruct IMGE as [EI1 EI2].
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31 & E32 & E33 & _).
  rewrite kHighMemBeg_val in E2. split; [clear -Ha E2; lia|]. split.
  { unfold img_sep, app_mem in *. rewrite EI1 in E33. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in E16. clear -Ha E16 E33 EI2. lia. }
  split.
  { intros sc Hsc. destruct (S3 sc Hsc) as (_ & AM & _ & POS & _ & _ & RSV). pose proof (RSV _ E29) as X. rewrite EI1 in X. cbn [fst snd] in X.
    unfold app_mem in AM. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in AM. clear -Ha X EI2 AM POS. lia. }
  split.
  { intros b len H. destruct (BS b len H) as (AM & _ & _ & _ & _ & IS). unfold img_sep in IS. rewrite EI1 in IS.
    assert (0 < len) by (destruct H as [[_ ->]|[_ ->]]; cbv; reflexivity).
    unfold app_mem in AM. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in AM. clear -Ha IS EI2 AM H0. lia. }
  rewrite kLowAppEnd_val. clear -Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma AG_far : forall a, FP s a -> ~ (T <= a < T + 4096) -> ~ (0x10000 <= a < 0x603000) -> m' (wa a) = m (wa a).
Proof. intros a Ha NT NI. apply AG; [exact Ha|]. unfold shellW, IA. clear -NT NI. lia. Qed.
Lemma AG_img : forall a, FP s a -> 0x10000 <= a < 0x603000 -> ~ (IA <= a < IA + 0x81030) -> ~ (0x13d608 <= a < 0x13d60c) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha HI N1 N2. apply AG; [exact Ha|]. pose proof Tfacts as [(T1 & T2 & T3 & T4) _].
  unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in *. unfold shellW. clear -HI N1 N2 T3. lia.
Qed.

(* [comment removed for export] *)
Lemma xferA : arep_instance asegs E0 s m -> arep_instance asegs E0 s m'.
Proof.
  intros RA. destruct RA as (A1 & A2 & A3 & A4 & (bsl & A5 & L5) & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  assert (AGI : agree_on m m' (ae_instance E0) 3632).
  { intros x Hx. unfold ae_instance in Hx. rewrite IC0 in Hx. cbn [aic_instance asan_ic] in Hx.
    apply AG_img; [eapply (fp_img_nth E0 (DepotFP E0) s 0%nat); [reflexivity| unfold ae_instance; rewrite IC0; cbn [aic_instance asan_ic]; clear -Hx; lia]
                 | clear -Hx; lia| unfold IA; clear -Hx; lia| clear -Hx; lia]. }
  unfold arep_instance.
  unfold kInsSpaceBeg, kInsSecondary, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kInsQuarantine, kInsQMutex, kInsQGlobal, kInsFallbackMutex, kInsMaxUserDefined in *.
  repeat match goal with |- _ /\ _ => split end.
  all: try (exists bsl; split; [| exact L5]).
  all: first [ eapply rw_cells_agree'; [| eassumption]; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; intros x Hx; apply AGI; clear -Hx; lia
             | eapply u64arr_agree; [| eassumption]; rewrite ?L5; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; intros x Hx; apply AGI; clear -Hx; lia ].
Qed.

(* [comment removed for export] *)
Lemma AGri : forall a, ae_region_info E0 <= a < ae_region_info E0 + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  apply AG_far; [right; left; exact Ha| intros HT; destruct (Tpage_apart a HT) as (NR & _)| intros HI; destruct (img_apart a HI) as (NR & _)];
    unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *; clear -Ha NR E3 E4; lia.
Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha.
  assert (RM : in_some_region_map E0 s a = true).
  { unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'. split; [apply In_ziota; unfold kNumClasses in Hc; lia|].
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  pose proof (region_map_in_space E0 [] [] s a WF RM) as SP. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  apply AG_far; [do 3 right; left; exists c'; split; [exact Hc| exact Ha]| intros HT; destruct (Tpage_apart a HT) as (NR & _)| intros HI; destruct (img_apart a HI) as (NR & _)];
    unfold kSpaceSize in *; clear -SP NR E3 E4; lia.
Qed.
Lemma AGptr : forall a, ae_ptr_array E0 <= a < ae_ptr_array E0 + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. unfold kChunksBlockCount in Ha.
  apply AG_far; [do 4 right; left; unfold kChunksBlockCount; exact Ha| intros HT; destruct (Tpage_apart a HT) as (_ & NP & _)| intros HI; destruct (img_apart a HI) as (_ & NP & _)];
    clear -Ha NP; lia.
Qed.
Lemma AGsec : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & POS & MODS & _).
  pose proof (AsanRepFrame.pos_mod_ge E0 (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. unfold kPageSize in GE.
  apply AG_far; [do 5 right; left; exists sc; split; [exact Hsc| exact Ha]| intros HT; destruct (Tpage_apart a HT) as (_ & _ & NS & _)| intros HI; destruct (img_apart a HI) as (_ & _ & NS & _)];
    pose proof (NS sc Hsc); clear -Ha GE H; lia.
Qed.
Lemma AGcm : forall a cb cm, as_chunks s !! cb = Some cm -> chunk_meta_fp cm a -> m' (wa a) = m (wa a).
Proof.
  intros a cb cm Hcm Ha. pose proof (chunk_meta_in_block E0 [] [] s cb cm a WF Hcm Ha) as [BL BU]. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  apply AG_far; [do 6 right; left; exists cb, cm; split; [exact Hcm| exact Ha]| intros HT; destruct (Tpage_apart a HT) as (NR & _ & NS & _)| intros HI; destruct (img_apart a HI) as (NR & _ & NS & _)];
    (destruct (block_where E0 [] [] s cb cm WF Hcm) as [(I1 & I2 & _)|(sc & Hsc & _ & L1 & L2)];
     [unfold kSpaceSize in *; clear -BL BU I1 I2 NR E3 E4; lia| pose proof (NS sc Hsc); unfold kPageSize in *; clear -BL BU L1 L2 H; lia]).
Qed.
Lemma AGbat : forall a b, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha. pose proof WF as (WE & WR & _ & _ & WQ & _).
  destruct (batch_block E0 [] s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  pose proof (carved_in_space E0 s kBatchClass _ HB24 WR CV) as [I1 I2].
  assert (CS : class_size kBatchClass = 8192) by reflexivity. pose proof WE as (E1 & E2 & E3 & E4 & _).
  apply AG_far; [do 7 right; left; exists b; split; [exact Hb| exact Ha]| intros HT; destruct (Tpage_apart a HT) as (NR & _)| intros HI; destruct (img_apart a HI) as (NR & _)];
    unfold kBatchCap, kSpaceSize, kRegionSize in *; clear -Ha NR I1 I2 CS E3 E4; lia.
Qed.
Lemma AGdep : forall a, DepotFP E0 s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. destruct (DepotFP_where E0 s a Ha) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
  - unfold depot_static in Hr. rewrite IC0 in Hr. cbn [aic_theDepot aic_stackStore asan_ic] in Hr.
    destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in R; (apply AG_img; [do 8 right; left; exact Ha| | unfold IA|]; clear -R; lia).
  - apply AG_far; [do 8 right; left; exact Ha| intros HT; destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _)| intros HI; destruct (img_apart a HI) as (_ & _ & _ & NB & _)];
      exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
  - apply AG_far; [do 8 right; left; exact Ha| intros HT; destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _)| intros HI; destruct (img_apart a HI) as (_ & _ & _ & NB & _)];
      exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
Qed.
(* [comment removed for export] *)
Lemma shadow_cell_band : forall g v, Sh E0 s (8 * g) = Some v -> kLowAppEnd < kShadowBase + g < kHighMemBeg.
Proof.
  intros g v Hg. pose proof alloc_ceiling_range as CR. pose proof WF as WF0.
  unfold Sh in Hg.
  destruct (in_some_region_map E0 s (8 * g)) eqn:RM.
  - pose proof (region_map_in_space E0 [] [] s (8 * g) WF0 RM) as SP. pose proof (proj1 WF0) as (E1 & E2 & E3 & E4 & E5 & _).
    rewrite kHighMemBeg_val, kLowAppEnd_val in *. unfold kSpaceSize, kShadowBase in *. clear -SP E2 E3 E4 E5 CR. lia.
  - destruct (in_some_sec_map s (8 * g)) eqn:SM.
    + unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb). apply andb_true_iff in Hb as [B1 B2].
      apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof WF0 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & HB & SE & _).
      unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in *. unfold kShadowBase in *. clear -B1 B2 HB SE CR. lia.
    + cbn [orb] in Hg. destruct (sh_default_dom E0 (8 * g) && negb (sh_excluded E0 (8 * g))) eqn:C; [|discriminate].
      apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
      * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
        rewrite kHighMemBeg_val, kLowAppEnd_val in *. unfold kShadowBase in *. clear -C1 C2. lia.
      * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
        rewrite kHighMemBeg_val, kLowAppEnd_val in *. unfold kShadowBase, kHighMemEnd in *. clear -C1 C2. lia.
Qed.
Lemma AGsh : forall g v, Sh E0 s (8 * g) = Some v -> m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg. pose proof (shadow_cell_band g v Hg) as BD.
  apply AG_far; [do 9 right; exists g, v; split; [reflexivity| exact Hg]| intros HT; destruct (Tpage_apart _ HT) as (_ & _ & _ & _ & NBAND & _)| intros HI; destruct (img_apart _ HI) as (_ & _ & _ & _ & NBAND)];
    exact (NBAND BD).
Qed.

Lemma xferB : arep_regioninfo asegs E0 s m -> arep_regioninfo asegs E0 s m'.
Proof. exact (frameB' asegs E0 s m m' AGri). Qed.
Lemma xferC : arep_region_mem asegs E0 s m -> arep_region_mem asegs E0 s m'.
Proof. exact (frameC' asegs E0 s m m' WM AGfa). Qed.
Lemma xferE : arep_secondary asegs E0 s m -> arep_secondary asegs E0 s m'.
Proof. exact (frameE' asegs E0 s m m' WM AGptr AGsec). Qed.
Lemma xferF : arep_chunks asegs s m -> arep_chunks asegs s m'.
Proof. exact (frameF' asegs s m m' AGcm). Qed.
Lemma xferG : arep_batches asegs s m -> arep_batches asegs s m'.
Proof. exact (frameG' asegs s m m' AGbat). Qed.
Lemma xferH : arep_depot (DepotR asegs E0) s m -> arep_depot (DepotR asegs E0) s m'.
Proof. exact (frameH' asegs E0 s m m' WM AGdep). Qed.
Lemma xferJ : arep_shadow asegs E0 s m -> arep_shadow asegs E0 s m'.
Proof. exact (frameJ' asegs E0 s m m' AGsh). Qed.
End XFER.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lits := rewrite ?IC0; cbn [aic_instance aic_asan_flags aic_common_flags aic_shadow_dyn_addr aic_kHighMemEnd aic_can_poison_memory aic_asan_inited aic_malloc_context_size
       aic_page_size_cached aic_dying_flag aic_stack_anchor aic_REAL_memcpy_var aic_malloc_hook_table aic_internal_alloc_initialized aic_internal_allocator_instance
       aic_theDepot aic_stackStore asan_ic].

(* [comment removed for export] *)
Definition shell_iv (lo : Z) (iv : Z * Z) : Prop :=
     lo <= fst iv
  \/ (IA <= fst iv /\ snd iv <= IA + 0x81030)
  \/ (0x13d608 <= fst iv /\ snd iv <= 0x13d60c)
  \/ (T + 2856 <= fst iv /\ snd iv <= T + 2872)
  \/ (T + 3168 <= fst iv /\ snd iv <= T + 3169).

(* [comment removed for export] *)
Definition shell_st (ii' : bool) (ts' : tstats) (a : astate) : astate := upd_ts (fun _ => ts') (upd_ia_inited ii' a).

Lemma shell_st_id : forall a, shell_st (as_ia_inited a) (as_ts a) a = a.
Proof. intros a. destruct a. reflexivity. Qed.

(* [comment removed for export] *)
Definition ts_agree78 (t t' : tstats) : Prop :=
  (forall i, i <> 7%nat -> i <> 8%nat -> nth_error (tstats_words t') i = nth_error (tstats_words t) i) /\ ts_by_size t' = ts_by_size t.

Lemma ts_agree78_refl : forall t, ts_agree78 t t.
Proof. intros t. split; [intros; reflexivity| reflexivity]. Qed.
Lemma ts_agree78_realloc : forall n t, ts_agree78 t (ts_on_realloc n t).
Proof.
  intros n t. split; [| reflexivity]. intros i H7 H8. unfold tstats_words, ts_on_realloc.
  do 7 (destruct i as [|i]; [reflexivity|]). destruct i as [|i]; [congruence|]. destruct i as [|i]; [congruence|]. reflexivity.
Qed.

Lemma outside_shell : forall W lo x,
  Forall (shell_iv lo) W -> x < lo -> ~ shellW x -> outside W x.
Proof.
  intros W lo x FW Hx NS. unfold shellW in NS. eapply outside_of_Forall; [exact FW|].
  intros [u v] Hiv. unfold shell_iv in Hiv. cbn [fst snd] in *. unfold IA in *. lia.
Qed.

(* [comment removed for export] *)
Lemma thread_shell_st : forall (ii : bool) (ts' : tstats) (a : astate) (m : mem),
     rw_cells asegs m (T + kThrStackTop) [C8 (zw (ae_stack_top E0)); C8 (zw (ae_stack_bottom E0))]
  /\ rw_cells asegs m (T + 40) [C1 (AsanRep.zb 0)]
  /\ rw_cells asegs m (T + kThrQCache) [C8 (zw (qcount (as_tq a))); C8 (zw (list_first (as_tq a))); C8 (zw (list_last (as_tq a))); C8 (zw (tq_bytes a))]
  /\ (forall c, 0 <= c < kNumClasses ->
        rw_cells asegs m (T + kThrCache + kPerClassSize * c) (percls_cells a c)
        /\ exists junk, u32arr asegs m (T + kThrCache + kPerClassSize * c + 16) (map zw (get_cache a c) ++ junk)
                       /\ (length (get_cache a c) + length junk = 16)%nat)
  /\ rw_cells asegs m (T + kThrCacheStats + 16) [C8 (zw (as_cache_allocated a)); C8 (zw (as_cache_mapped a))]
  /\ u64arr asegs m (T + kThrStats) (tstats_words ts')
  /\ u64arr asegs m (T + kThrStats + 112) (map (fun c => zw (match ts_by_size ts' !! c with Some v => v | None => 0 end)) (ziota 0 32))
  /\ rw_cells asegs m (T + kThrUnwinding) [C1 (AsanRep.zb 0)] ->
  arep_thread asegs E0 (shell_st ii ts' a) m.
Proof. intros ii ts' a m H. destruct a. exact H. Qed.

Lemma globals_shell_st : forall (ii : bool) (ts' : tstats) (a : astate) (m : mem),
  let IC := ae_ic E0 in
     u8arr asegs m (aic_asan_flags IC) (map AsanRep.zb (asan_flags_bytes IC))
  /\ rw_cells asegs m (aic_common_flags IC + 34) [C1 (AsanRep.zb 1)]
  /\ rw_cells asegs m (aic_common_flags IC + 120) [C8 (zw kClearShadowMmapThreshold)]
  /\ rw_cells asegs m (aic_common_flags IC + 219) [C1 (AsanRep.zb 1)]
  /\ rw_cells asegs m (aic_shadow_dyn_addr IC) [C8 (zw kShadowBase)]
  /\ rw_cells asegs m (aic_kHighMemEnd IC) [C8 (zw kHighMemEnd); C8 (zw 0); C8 (zw 0)]
  /\ rw_cells asegs m (aic_can_poison_memory IC) [C1 (AsanRep.zb 1)]
  /\ rw_cells asegs m (aic_asan_inited IC) [C1 (AsanRep.zb 1)]
  /\ rw_cells asegs m (aic_malloc_context_size IC) [C4 (zw kMallocContextSize)]
  /\ rw_cells asegs m (aic_page_size_cached IC) [C8 (zw kPageSize)]
  /\ rw_cells asegs m (aic_dying_flag IC) [C4 (zw 0)]
  /\ rw_cells asegs m (aic_stack_anchor IC) [C8 (zw (ae_sp0 E0 - kStackAnchorDelta))]
  /\ rw_cells asegs m (aic_REAL_memcpy_var IC) [C8 (zw (aic_musl_memcpy IC)); C8 (zw (aic_musl_memset IC))]
  /\ u64arr asegs m (aic_malloc_hook_table IC) (map zw (List.repeat 0 10))
  /\ rw_cells asegs m (aic_internal_alloc_initialized IC) [C1 (AsanRep.zb (boolz ii)); C1 (AsanRep.zb 0)]
  /\ (ii = true ->
        rw_cells asegs m (aic_internal_allocator_instance IC + kIaPageSizeOff) [C8 (zw kPageSize); C8 (zw (aic_internal_allocator_instance IC + kIaChunksPtrOff + 8))])
  /\ u8arr asegs m (aic_internal_allocator_instance IC + 8) (zeros (Z.to_nat 0x40000))
  /\ wr_at asegs m (aic_internal_allocator_instance IC) 0x81030 ->
  arep_globals asegs E0 (shell_st ii ts' a) m.
Proof. intros ii ts' a m IC H. destruct a. exact H. Qed.

Lemma arep_batch_list_st : forall s s' l m, arep_batch_list asegs s l m -> arep_batch_list asegs s' l m.
Proof.
  intros s s' l m. induction l as [|b l IH]; [intros X; exact X|].
  intros [H1 H2]. split; [exact H1| exact (IH H2)].
Qed.

Lemma others_shell_st : forall (ii : bool) (ts' : tstats) (a : astate) (m : mem),
  (arep_instance asegs E0 a m -> arep_instance asegs E0 (shell_st ii ts' a) m)
  /\ (arep_regioninfo asegs E0 a m -> arep_regioninfo asegs E0 (shell_st ii ts' a) m)
  /\ (arep_region_mem asegs E0 a m -> arep_region_mem asegs E0 (shell_st ii ts' a) m)
  /\ (arep_secondary asegs E0 a m -> arep_secondary asegs E0 (shell_st ii ts' a) m)
  /\ (arep_chunks asegs a m -> arep_chunks asegs (shell_st ii ts' a) m)
  /\ (arep_batches asegs a m -> arep_batches asegs (shell_st ii ts' a) m)
  /\ (arep_depot (DepotR asegs E0) a m -> arep_depot (DepotR asegs E0) (shell_st ii ts' a) m)
  /\ (arep_shadow asegs E0 a m -> arep_shadow asegs E0 (shell_st ii ts' a) m).
Proof.
  intros ii ts' a m. destruct a. do 5 (split; [intros HH; exact HH|]).
  split; [intros [H1 H2]; split; eapply arep_batch_list_st; eassumption|].
  split; intros HH; exact HH.
Qed.

Theorem ARep_shell : forall (a : astate) (m m' : mem) (mo : Model) (W : list (Z * Z)) (lo : Z) (ii' : bool) (ts' : tstats),
  ARep asegs E0 (DepotR asegs E0) a m -> AWf E0 [] [] a -> AKern E0 a mo -> blocks_sep E0 a ->
  wmono asegs m m' -> munch W m m' -> alloc_ceiling <= lo -> Forall (shell_iv lo) W ->
  (* [comment removed for export] *)
  rw_cells asegs m' 0x13d608 [C1 (Z_to_bv 8 (boolz ii')); C1 (Z_to_bv 8 0)] ->
  (ii' = true -> rw_cells asegs m' (IA + kIaPageSizeOff) [C8 (wz 4096); C8 (wz (IA + kIaChunksPtrOff + 8))]) ->
  u8arr asegs m' (IA + 8) (zeros (Z.to_nat 0x40000)) ->
  (* [comment removed for export] *)
  ts_agree78 (as_ts a) ts' ->
  rw_cells asegs m' (T + 2856) [C8 (wz (ts_reallocs ts')); C8 (wz (ts_realloced ts'))] ->
  rw_cells asegs m' (T + 3168) [C1 (Z_to_bv 8 0)] ->
  ARep asegs E0 (DepotR asegs E0) (shell_st ii' ts' a) m'.
Proof.
  intros a m m' mo W lo ii' ts' REP WF K BS WM MU LO FW NI15 NI16 NI17 TS78 NST NUNW.
  pose proof ENV0 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _ & _ & _ & _ & IMG_LOW & _). destruct IMGE as [EI1 EI2]. pose proof alloc_ceiling_range as CR.
  assert (IMG_IN : forall r, In r (arep_img_ranges E0 ++ depot_static E0) -> fst (ae_img E0) <= fst r /\ fst r + snd r <= fst (ae_img E0) + snd (ae_img E0)).
  { intros r Hr. pose proof (IMG_LOW r Hr) as X. rewrite EI1. clear -X EI2. lia. }
  pose proof (Tfacts) as [(T1 & T3 & T4 & T5) TDN]. unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in T4, T5.
  assert (AG : forall x, FP a x -> ~ shellW x -> m' (wa x) = m (wa x)).
  { intros x Hx NS. pose proof (fp_below_ceiling E0 (DepotFP E0) [] [] IMG_IN (DepotFP_where E0) a x WF BS Hx) as UB.
    assert (X0 : 0 <= x).
    { destruct (fp_locate E0 (DepotFP E0) [] [] IMG_IN (DepotFP_where E0) a x WF BS Hx) as [(r & Hr & R)|[[R _]|[R _]]].
      - pose proof (IMG_LOW r Hr). clear -H R. lia. - pose proof (sh_band_below_ceiling x R) as R'. rewrite ?kLowAppEnd_val in R'. clear -R'. lia.
      - unfold app_addr in R. rewrite ?kHighMemBeg_val in R. clear -R. lia. }
    pose proof (MU (wa x)) as E. rewrite wa_unsigned in E by (clear -X0 UB CR; lia). apply E. eapply outside_shell; [exact FW| clear -UB LO; lia| exact NS]. }
  assert (AGT : forall x, T <= x < T + 4096 -> ~ (T + 2856 <= x < T + 2872) -> x <> T + 3168 -> m' (wa x) = m (wa x)).
  { intros x HT X1 X2.
    pose proof (MU (wa x)) as E. rewrite wa_unsigned in E by (clear -HT T1 T3 CR; lia). apply E. clear E.
    clear -FW HT X1 X2 T1 T3 T4 LO. eapply outside_of_Forall; [exact FW|].
    intros [u v] Hiv. unfold shell_iv in Hiv. cbn [fst snd] in *. unfold IA in *. lia. }
  destruct REP as (RA & RB & RC & RD & RE & RF & RG & RH & RI' & RJ).
  assert (RA' : arep_instance asegs E0 a m') by (eapply xferA; eassumption).
  assert (RB' : arep_regioninfo asegs E0 a m') by (eapply xferB; eassumption).
  assert (RC' : arep_region_mem asegs E0 a m') by (eapply xferC; eassumption).
  assert (RE' : arep_secondary asegs E0 a m') by (eapply xferE; eassumption).
  assert (RF' : arep_chunks asegs a m') by (eapply xferF; eassumption).
  assert (RG' : arep_batches asegs a m') by (eapply xferG; eassumption).
  assert (RH' : arep_depot (DepotR asegs E0) a m') by (eapply (xferH a m m' mo); eassumption).
  assert (RJ' : arep_shadow asegs E0 a m') by (eapply xferJ; eassumption).
  (* [comment removed for export] *)
  destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  assert (AGD : forall A k, T <= A -> A + k <= T + 4096 -> (A + k <= T + 2856 \/ T + 2872 <= A) -> A + k <= T + 3168 -> agree_on m m' A k).
  { intros A k H1 H2 H3 H4 x Hx. apply AGT; clear -H1 H2 H3 H4 Hx; lia. }
  unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in *.
  assert (RD' : arep_thread asegs E0 (shell_st ii' ts' a) m').
  { apply thread_shell_st. unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding.
    split; [eapply rw_cells_agree'; [| exact D1]; apply AGD; cbn; clear; lia|].
    split; [eapply rw_cells_agree'; [| exact D2]; apply AGD; cbn; clear; lia|].
    split; [eapply rw_cells_agree'; [| exact D3]; apply AGD; cbn; clear; lia|].
    split.
    { intros c Hc. destruct (D4 c Hc) as (X1 & junk & X2 & L). split.
      - eapply rw_cells_agree'; [| exact X1]. apply AGD; cbn [cells_size percls_cells csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear -Hc; lia.
      - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map, L. apply AGD; cbn; clear -Hc; lia. }
    split; [eapply rw_cells_agree'; [| exact D5]; apply AGD; cbn; clear; lia|].
    split.
    { apply AsanRepHit.u64arr_of_cells.
      - replace (length (tstats_words ts')) with (length (tstats_words (as_ts a))) by (unfold tstats_words; rewrite !length_map; reflexivity).
        eapply wr_at_transport; [exact (proj2 D6)| exact WM].
      - intros i w Hi. destruct TS78 as [TW _].
        assert (LT : (i < 14)%nat).
        { replace 14%nat with (length (tstats_words ts')) by (unfold tstats_words; rewrite length_map; reflexivity). apply nth_error_Some. rewrite Hi. discriminate. }
        destruct (Nat.eq_dec i 7) as [->|Ni7].
        { unfold tstats_words in Hi. cbn in Hi. injection Hi as <-. replace (T + 2800 + 8 * Z.of_nat 7) with (T + 2856) by (clear; lia).
          pose proof (rwc_split asegs m' _ [C8 (zw (ts_reallocs ts'))] [C8 (zw (ts_realloced ts'))] NST) as [X _]. exact X. }
        destruct (Nat.eq_dec i 8) as [->|Ni8].
        { unfold tstats_words in Hi. cbn in Hi. injection Hi as <-. replace (T + 2800 + 8 * Z.of_nat 8) with (T + 2856 + Z.of_nat (cells_size [C8 (zw (ts_reallocs ts'))])) by (cbn; clear; lia).
          pose proof (rwc_split asegs m' _ [C8 (zw (ts_reallocs ts'))] [C8 (zw (ts_realloced ts'))] NST) as [_ X]. exact X. }
        rewrite (TW i Ni7 Ni8) in Hi. eapply rw_cells_agree'; [| exact (AsanRepHit.u64arr_cell asegs m _ _ i w D6 Hi)].
        apply AGD; cbn; clear -LT Ni7 Ni8; lia. }
    split.
    { destruct TS78 as [_ ->]. eapply u64arr_agree; [| exact D7]. rewrite length_map. cbn [length ziota Z.of_nat Pos.of_succ_nat Pos.succ]. apply AGD; clear; lia. }
    exact NUNW. }
  (* [comment removed for export] *)
  destruct RI' as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18).
  assert (AGI : forall (k : nat) A n kk, nth_error (arep_img_ranges E0) k = Some (A, n) -> kk <= n -> (k < 15)%nat -> agree_on m m' A kk).
  { intros k A n kk Hk Hkk LT x Hx. apply AG; [eapply (fp_img_nth E0 (DepotFP E0) a k); [exact Hk| clear -Hx Hkk; lia]|].
    unfold shellW. revert Hk; unfold arep_img_ranges; cbv zeta; unfold ae_instance; lits;
      do 15 (destruct k as [|k]; [cbn; intros Hk; injection Hk as <- <-; cbn [length asan_flags_bytes Z.of_nat Pos.of_succ_nat Pos.succ] in *; unfold IA; clear -Hx Hkk T4; lia|]); clear -LT; lia. }
  assert (RI'' : arep_globals asegs E0 (shell_st ii' ts' a) m').
  { apply globals_shell_st. cbv zeta.
    split; [eapply u8arr_agree; [| exact I1]; eapply (AGI 1%nat); [reflexivity| rewrite length_map; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I2]; eapply (AGI 2%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I3]; eapply (AGI 3%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I4]; eapply (AGI 4%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I5]; eapply (AGI 5%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I6]; eapply (AGI 6%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I7]; eapply (AGI 7%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I8]; eapply (AGI 8%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I9]; eapply (AGI 9%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I10]; eapply (AGI 10%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I11]; eapply (AGI 11%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I12]; eapply (AGI 12%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply rw_cells_agree'; [| exact I13]; eapply (AGI 13%nat); [reflexivity| cbn; clear; lia| clear; lia]|].
    split; [eapply u64arr_agree; [| exact I14]; eapply (AGI 14%nat); [reflexivity| rewrite length_map, repeat_length; clear; lia| clear; lia]|].
    rewrite IC0. cbn [aic_internal_alloc_initialized aic_internal_allocator_instance asan_ic]. fold IA.
    split; [exact NI15|]. split; [exact NI16|]. split; [exact NI17|]. eapply wr_at_transport; [| exact WM]. revert I18. lits. intros I18. exact I18. }
  destruct (others_shell_st ii' ts' a m') as (OA & OB & OC & OE & OF & OG & OH & OJ).
  split; [exact (OA RA')|]. split; [exact (OB RB')|]. split; [exact (OC RC')|]. split; [exact RD'|]. split; [exact (OE RE')|].
  split; [exact (OF RF')|]. split; [exact (OG RG')|]. split; [exact (OH RH')|]. split; [exact RI''| exact (OJ RJ')].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AKern_shell_st : forall ii ts' a mo, AKern E0 a mo -> AKern E0 (shell_st ii ts' a) mo.
Proof.
  intros ii ts' a mo HK. eapply AF_tkit.AKern_ext; [| | | | | exact HK]; destruct a; reflexivity.
Qed.

Lemma model_shell_st : forall ii ts' a,
  (AWf E0 [] [] a -> AWf E0 [] [] (shell_st ii ts' a))
  /\ (res_ok a -> res_ok (shell_st ii ts' a))
  /\ (AQbound a -> AQbound (shell_st ii ts' a))
  /\ (depot_inv E0 a -> depot_inv E0 (shell_st ii ts' a))
  /\ (AsanBudget2.binv a -> AsanBudget2.binv (shell_st ii ts' a))
  /\ live_blocks (shell_st ii ts' a) = live_blocks a
  /\ as_nprim_ever (shell_st ii ts' a) = as_nprim_ever a /\ as_ndepot_ins (shell_st ii ts' a) = as_ndepot_ins a
  /\ as_residue (shell_st ii ts' a) = as_residue a /\ as_ia_inited (shell_st ii ts' a) = ii /\ as_ts (shell_st ii ts' a) = ts'
  /\ (sstats_ok a -> sstats_ok (shell_st ii ts' a)) /\ (csmall a -> csmall (shell_st ii ts' a)).
Proof.
  intros ii ts' a. split.
  { intros W. eapply AWf_same_core; [| exact W]. eapply same_core_trans; [apply same_core_upd_ia| apply same_core_upd_ts]. }
  destruct a. repeat (split; [first [intros HH; exact HH| reflexivity]|]). intros HH; exact HH.
Qed.

(* [comment removed for export] *)
Lemma rt_fpc_shell : forall x, rt_fpc E0 FSB0 PL0 x ->
  (0x10000 <= x < 0x603000 /\ ~ (IA <= x < IA + 0x81030) /\ ~ (0x13d608 <= x < 0x13d60c)) \/ rt_high2 E0 PL0 x.
Proof.
  intros x Hx. destruct (rt_fpc_where E0 FSB0 PL0 x Hx) as [(X1 & _ & _ & NM)|X]; [left| right; exact X].
  split; [exact X1|]. unfold IA. split; intros R; apply NM; unfold in_cells, img_mut;
    cbn [aic_instance aic_internal_alloc_initialized aic_internal_allocator_instance aic_theDepot aic_stackStore asan_ic c_errno ACONSTS].
  - exists (716160, 528432). split; [right; right; left; reflexivity| cbn [fst snd]; clear -R; lia].
  - exists (1299976, 4). split; [right; left; reflexivity| cbn [fst snd]; clear -R; lia].
Qed.

Theorem AINV_shell : forall (a : astate) (m m' : mem) (mo : Model) (W : list (Z * Z)) (lo : Z) (ii' : bool) (ts' : tstats),
  AINV E0 FSB0 PL0 a m mo ->
  wmono asegs m m' -> munch W m m' -> alloc_ceiling <= lo -> Forall (shell_iv lo) W -> mem_inv asegs m' ->
  rw_cells asegs m' 0x13d608 [C1 (Z_to_bv 8 (boolz ii')); C1 (Z_to_bv 8 0)] ->
  (ii' = true -> rw_cells asegs m' (IA + kIaPageSizeOff) [C8 (wz 4096); C8 (wz (IA + kIaChunksPtrOff + 8))]) ->
  u8arr asegs m' (IA + 8) (zeros (Z.to_nat 0x40000)) ->
  ts_agree78 (as_ts a) ts' ->
  rw_cells asegs m' (T + 2856) [C8 (wz (ts_reallocs ts')); C8 (wz (ts_realloced ts'))] ->
  rw_cells asegs m' (T + 3168) [C1 (Z_to_bv 8 0)] ->
  AINV E0 FSB0 PL0 (shell_st ii' ts' a) m' mo.
Proof.
  intros a m m' mo W lo ii' ts' (REP & WF & K & RO & QB & DI & BI & MI & RT & SST & CSM) WM MU LO FW MI' NI15 NI16 NI17 TS78 NST NUNW.
  pose proof alloc_ceiling_range as CR.
  pose proof (Tfacts) as [(T1 & T3 & T4 & T5) TDN]. unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in T4, T5.
  destruct PL0OK as ((c0 & cl & (_ & (CP1 & CP2 & CP3 & _) & _) & CC1 & CC2) & (d0 & dl & (_ & (DP1 & DP2 & DP3 & _) & _) & DD1 & DD2) & _ & CT & DT & _).
  unfold A_IMG_END in CP3, DP3.
  pose proof (blocks_sep_of E0 a mo ENV0 WF K) as BS.
  pose proof (ARep_shell a m m' mo W lo ii' ts' REP WF K BS WM MU LO FW NI15 NI16 NI17 TS78 NST NUNW) as REP'.
  destruct (model_shell_st ii' ts' a) as (MW & MR & MQ & MD & MB & _ & _ & _ & _ & _ & _ & MS & MC).
  (* [comment removed for export] *)
  assert (AGR : forall x, rt_fpc E0 FSB0 PL0 x -> m' (wa x) = m (wa x)).
  { intros x Hx. destruct (rt_fpc_shell x Hx) as [(R1 & R2 & R3)|RH].
    - pose proof (MU (wa x)) as E. rewrite wa_unsigned in E by (clear -R1; lia). apply E. clear E.
      eapply outside_of_Forall; [exact FW|]. intros [u v] Hiv. unfold shell_iv in Hiv. cbn [fst snd] in *. unfold IA in *. clear -R1 R2 R3 Hiv LO T4 CR. lia.
    - unfold rt_high2 in RH. pose proof (MU (wa x)) as E. rewrite wa_unsigned in E by (clear -RH T1 T3 CP1 CP2 CC1 CC2 DP1 DP2 DD1 DD2 CR; lia). apply E. clear E.
      eapply outside_of_Forall; [exact FW|]. intros [u v] Hiv. unfold shell_iv in Hiv. cbn [fst snd] in *. unfold IA in *.
      clear -RH Hiv LO T1 T3 T4 CP1 CP2 CP3 CC1 CC2 DP1 DP2 DP3 DD1 DD2 CT DT CR. lia. }
  split; [exact REP'|]. split; [exact (MW WF)|]. split; [exact (AKern_shell_st ii' ts' a mo K)|]. split; [exact (MR RO)|]. split; [exact (MQ QB)|].
  split; [exact (MD DI)|]. split; [exact (MB BI)|]. split; [exact MI'|]. split; [eapply rt_misc5_agree; [exact RT| exact AGR]|]. split; [exact (MS SST)| exact (MC CSM)].
Qed.

End ShellRep.
End RC__1.
