(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Cells Step.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep
     AsanWf1 AsanFrame AsanWf2 AsanWf3 AsanWf4 AsanWf5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section CL.
Variable E : aenv.
Variable P : list Z.
Variable D : list batch.
Local Notation SB := (ae_space_beg E).
Notation AWF := (AWf E P D).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AWf_init :
  wf_env E -> List.NoDup (map depot_hash (ae_keys0 E ++ [])) ->
  AWf E [] [] (astate0 E).
Proof.
  intros WE ND. split; [exact WE|]. split; [| split; [| split; [| split; [| split]]]].
  - split; [intros c r H; cbn in H; rewrite lookup_empty in H; discriminate|].
    intros c Hc. cbn zeta. unfold region_of, get_region. cbn. rewrite lookup_empty. cbn.
    pose proof (class_size_mod c Hc) as [_ SZ].
    repeat split; try (cbn; lia); try reflexivity; try (unfold kFreeArrayOffset, kFreeArraySize; lia). constructor.
  - split; [intros c l H; cbn in H; rewrite lookup_empty in H; discriminate|]. split; [intros _; split; reflexivity|].
    intros c Hc. unfold get_cache. cbn. rewrite lookup_empty. split; [pose proof (hint_range c Hc); unfold max_count, zlen; cbn; lia|].
    split; [constructor| intros x []].
  - split; [intros cb cm H; cbn in H; rewrite lookup_empty in H; discriminate|].
    intros cb1 cm1 cb2 cm2 H; cbn in H; rewrite lookup_empty in H; discriminate.
  - split; [intros b []|]. split; [intros b []|]. split; [cbn; constructor| intros b1 b2 cb []].
  - split; [left; split; reflexivity|]. split; [unfold n_chunks; cbn; lia|]. split; [intros sc []|]. split; [cbn; constructor| intros a b []].
  - split; [exact ND|]. unfold zlen; cbn; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition user_lo (cm : chunkmeta) : Z := cm_user_beg cm.
Definition user_hi (cm : chunkmeta) : Z := cm_user_beg cm + cm_n cm.

(* [comment removed for export] *)
Definition blk_lo (cm : chunkmeta) : Z := cm_alloc_beg cm.
Definition blk_hi (s : astate) (cm : chunkmeta) : Z :=
  match cm_prim cm with
  | Some c => cm_alloc_beg cm + class_size c
  | None => cm_alloc_beg cm - kPageSize + map_size (cm_n cm)
  end.

Lemma chunk_user_in_block : forall s cb cm, AWF s -> as_chunks s !! cb = Some cm ->
  blk_lo cm + 16 <= user_lo cm /\ user_hi cm <= blk_hi s cm /\ cb = user_lo cm - kChunkHeaderSize.
Proof.
  intros s cb cm WF Hcm. destruct WF as (WE & WR & WC & [K1 _] & _).
  destruct (K1 _ _ Hcm) as (A & B & C & D0 & _).
  unfold user_lo, user_hi, blk_lo, blk_hi, cm_chunk_beg, cm_user_beg in *. rewrite C in *.
  change (16 * 2 ^ rz_log (cm_n cm)) with (rz_size (cm_n cm)) in *.
  pose proof (rz_size_pos (cm_n cm)) as RP.
  split; [lia|]. split; [| exact A].
  destruct (cm_prim cm) as [c|].
  - destruct D0 as (D1 & D2 & _). pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1) as LE.
    pose proof (malloc_class_ok (cm_n cm) ltac:(lia)) as [_ NE]. rewrite <- D2 in NE. unfold needed1 in NE.
    pose proof (rounded_ge (cm_n cm)). lia.
  - pose proof (map_size_facts (cm_n cm)) as (_ & MG & _). pose proof (needed_ge (cm_n cm)). unfold kPageSize in *. lia.
Qed.

Lemma chunk_user_aligned : forall s cb cm, AWF s -> as_chunks s !! cb = Some cm -> user_lo cm mod 16 = 0.
Proof.
  intros s cb cm WF Hcm. pose proof WF as X. destruct X as ((SBM & _) & WR & WC & [K1 _] & WQ & (_ & _ & S3 & _) & _).
  destruct (K1 _ _ Hcm) as (A & B & C & D0 & _). unfold user_lo, cm_user_beg. rewrite C.
  change (16 * 2 ^ rz_log (cm_n cm)) with (rz_size (cm_n cm)). pose proof (rz_size_mod16 (cm_n cm)) as RM.
  apply Z.mod_divide in RM; [|lia]. destruct RM as [qr Hqr]. rewrite Hqr.
  destruct (cm_prim cm) as [c|].
  - destruct D0 as (D1 & D2 & (k & Hk & Hab & _) & _).
    assert (Hc : 1 <= c <= kLargestClassID).
    { subst c. apply malloc_class_ok. pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1). lia. }
    rewrite Hab. unfold region_beg, kRegionSize. pose proof (class_size_mod c Hc) as [CM _].
    apply Z.mod_divide in SBM; [|lia]. destruct SBM as [q Hq]. apply Z.mod_divide in CM; [|lia]. destruct CM as [q' Hq'].
    rewrite Hq, Hq'. apply Z.mod_divide; [lia|]. exists (q * 2^12 + c * 2^28 + k * q' * 2 + qr). lia.
  - destruct D0 as (_ & sc & Hsc & Hab & _). destruct (S3 sc Hsc) as (AL & _). rewrite Hab. unfold kPageSize in *.
    apply Z.mod_divide in AL; [|lia]. destruct AL as [q Hq]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (q * 256 + 256 + qr). lia.
Qed.

(* [comment removed for export] *)
Lemma chunk_block_committed : forall s cb cm, AWF s -> as_chunks s !! cb = Some cm ->
  match cm_prim cm with
  | Some c => 1 <= c <= kLargestClassID /\ region_beg SB c <= blk_lo cm
              /\ blk_hi s cm <= region_beg SB c + rg_mapped_user (get_region s c)
  | None => exists sc, In sc (as_sec s) /\ blk_lo cm = sc_map_beg sc + kPageSize /\ blk_hi s cm = sc_map_beg sc + sc_map_size sc
  end.
Proof.
  intros s cb cm WF Hcm. destruct WF as (WE & [_ W2] & WC & [K1 _] & _).
  destruct (K1 _ _ Hcm) as (A & B & C & D0 & _). unfold blk_lo, blk_hi.
  destruct (cm_prim cm) as [c|].
  - destruct D0 as (D1 & D2 & (k & Hk & Hab & Hk1) & _).
    assert (Hc : 1 <= c <= kLargestClassID).
    { subst c. apply malloc_class_ok. pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1). lia. }
    destruct (W2 c Hc) as (A1 & _). unfold region_of in *. pose proof (class_size_mod c Hc) as [_ SZ].
    split; [exact Hc|]. rewrite Hab. split; [nia| nia].
  - destruct D0 as (_ & sc & Hsc & Hab & Hms & _). exists sc. split; [exact Hsc|]. split; [exact Hab|]. rewrite Hab, <- Hms. lia.
Qed.

(* [comment removed for export] *)
Theorem chunks_disjoint : forall s cb1 cm1 cb2 cm2, AWF s ->
  as_chunks s !! cb1 = Some cm1 -> as_chunks s !! cb2 = Some cm2 -> cb1 <> cb2 ->
  blk_hi s cm1 <= blk_lo cm2 \/ blk_hi s cm2 <= blk_lo cm1.
Proof.
  intros s cb1 cm1 cb2 cm2 WF H1 H2 NE.
  pose proof WF as X. destruct X as (WE & WR & WC & [K1 K2] & WQ & (_ & _ & S3 & S4 & S5) & WD).
  pose proof (K2 _ _ _ _ H1 H2 NE) as ABNE.
  destruct (K1 _ _ H1) as (_ & B1 & _ & D1 & _). destruct (K1 _ _ H2) as (_ & B2 & _ & D2 & _).
  unfold blk_lo, blk_hi.
  destruct (cm_prim cm1) as [c1|] eqn:P1; destruct (cm_prim cm2) as [c2|] eqn:P2.
  - destruct D1 as (D11 & D12 & CV1 & _). destruct D2 as (D21 & D22 & CV2 & _).
    assert (Hc1 : 1 <= c1 <= kLargestClassID) by (subst c1; apply malloc_class_ok; pose proof (proj1 (from_primary_iff (cm_n cm1) ltac:(lia)) D11); lia).
    assert (Hc2 : 1 <= c2 <= kLargestClassID) by (subst c2; apply malloc_class_ok; pose proof (proj1 (from_primary_iff (cm_n cm2) ltac:(lia)) D21); lia).
    destruct (carved_blocks_disjoint E s c1 (cm_alloc_beg cm1) c2 (cm_alloc_beg cm2) Hc1 Hc2 WR CV1 CV2) as [[_ EQ]|[X|X]]; [exfalso; exact (ABNE EQ)| left; exact X| right; exact X].
  - destruct D1 as (D11 & D12 & CV1 & _). destruct D2 as (_ & sc & Hsc & Hab & Hms & _).
    assert (Hc1 : 1 <= c1 <= kLargestClassID) by (subst c1; apply malloc_class_ok; pose proof (proj1 (from_primary_iff (cm_n cm1) ltac:(lia)) D11); lia).
    pose proof (carved_in_space E s c1 _ Hc1 WR CV1) as [I1 I2]. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & OUT & _).
    rewrite Hab, <- Hms. unfold kRegionSize, kSpaceSize, kPageSize in *. lia.
  - destruct D2 as (D21 & D22 & CV2 & _). destruct D1 as (_ & sc & Hsc & Hab & Hms & _).
    assert (Hc2 : 1 <= c2 <= kLargestClassID) by (subst c2; apply malloc_class_ok; pose proof (proj1 (from_primary_iff (cm_n cm2) ltac:(lia)) D21); lia).
    pose proof (carved_in_space E s c2 _ Hc2 WR CV2) as [I1 I2]. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & OUT & _).
    rewrite Hab, <- Hms. unfold kRegionSize, kSpaceSize, kPageSize in *. lia.
  - destruct D1 as (_ & sc1 & Hsc1 & Hab1 & Hms1 & _). destruct D2 as (_ & sc2 & Hsc2 & Hab2 & Hms2 & _).
    assert (NEs : sc1 <> sc2) by (intros ->; apply ABNE; rewrite Hab1, Hab2; reflexivity).
    destruct (S5 sc1 sc2 Hsc1 Hsc2 NEs); rewrite Hab1, Hab2, <- Hms1, <- Hms2; unfold kPageSize; lia.
Qed.

Corollary live_blocks_disjoint : forall s cb1 cm1 cb2 cm2, AWF s ->
  as_chunks s !! cb1 = Some cm1 -> as_chunks s !! cb2 = Some cm2 -> cb1 <> cb2 ->
  user_hi cm1 <= user_lo cm2 \/ user_hi cm2 <= user_lo cm1.
Proof.
  intros s cb1 cm1 cb2 cm2 WF H1 H2 NE.
  pose proof (chunk_user_in_block s cb1 cm1 WF H1) as (A1 & B1 & _). pose proof (chunk_user_in_block s cb2 cm2 WF H2) as (A2 & B2 & _).
  destruct (chunks_disjoint s cb1 cm1 cb2 cm2 WF H1 H2 NE); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma find_chunk_block : forall s cb cm a, AWF s -> as_chunks s !! cb = Some cm ->
  blk_lo cm <= a < blk_hi s cm -> find_chunk s a = Some cm.
Proof.
  intros s cb cm a WF Hcm Ha. unfold find_chunk.
  assert (SPAN : forall cm', blk_hi s cm' = cm_alloc_beg cm' + block_span cm').
  { intros cm'. unfold blk_hi, block_span. destruct (cm_prim cm'); lia. }
  set (f := fun (_ : Z) (cm0 : chunkmeta) (acc : option chunkmeta) => match acc with Some _ => acc | None =>
             if (cm_alloc_beg cm0 <=? a) && (a <? cm_alloc_beg cm0 + block_span cm0) then Some cm0 else None end).
  assert (IND : forall mm, (forall k v, mm !! k = Some v -> as_chunks s !! k = Some v) ->
            (map_fold f None mm = None /\ mm !! cb = None) \/ map_fold f None mm = Some cm).
  { intros mm. induction mm as [|k v mm NONE FIRST IH] using map_first_key_ind; intros SUB.
    - left. split; [apply map_fold_empty| apply lookup_empty].
    - rewrite map_fold_insert_first_key by assumption.
      assert (SUB' : forall k0 v0, mm !! k0 = Some v0 -> as_chunks s !! k0 = Some v0).
      { intros k0 v0 H. apply SUB. rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite NONE in H. discriminate. }
      pose proof (SUB k v ltac:(apply lookup_insert_eq)) as Hk.
      destruct (IH SUB') as [[R NCB]|R]; rewrite R; cbn.
      + destruct ((cm_alloc_beg v <=? a) && (a <? cm_alloc_beg v + block_span v)) eqn:C.
        * right. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
          destruct (Z.eq_dec k cb) as [->|NE]; [rewrite Hcm in Hk; injection Hk as <-; reflexivity|].
          exfalso. destruct (chunks_disjoint s k v cb cm WF Hk Hcm NE) as [DJ|DJ]; rewrite SPAN in *; unfold blk_lo in *; lia.
        * left. split; [reflexivity|]. rewrite lookup_insert_ne; [exact NCB|]. intros ->.
          rewrite Hcm in Hk. injection Hk as <-. rewrite SPAN in Ha. unfold blk_lo in Ha.
          assert (C' : (cm_alloc_beg cm <=? a) && (a <? cm_alloc_beg cm + block_span cm) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
          rewrite C' in C. discriminate.
      + right. reflexivity. }
  destruct (IND (as_chunks s) ltac:(auto)) as [[_ X]|X]; [rewrite Hcm in X; discriminate| exact X].
Qed.

Lemma existsb_In : forall {A} (f : A -> bool) l x, In x l -> f x = true -> existsb f l = true.
Proof. intros A f l x Hin Hf. apply existsb_exists. exists x. auto. Qed.

Theorem block_Sh : forall s cb cm a, AWF s -> as_chunks s !! cb = Some cm ->
  blk_lo cm <= a < blk_hi s cm -> Sh E s a = Some (chunk_shadow cm a).
Proof.
  intros s cb cm a WF Hcm Ha. unfold Sh.
  rewrite (find_chunk_block s cb cm a WF Hcm Ha).
  pose proof (chunk_block_committed s cb cm WF Hcm) as CB. unfold blk_hi in *.
  destruct (cm_prim cm) as [c|].
  - destruct CB as (Hc & L1 & L2). unfold in_some_region_map.
    rewrite (existsb_In _ (ziota 0 32) c); [reflexivity| apply In_ziota; unfold kLargestClassID in Hc; lia|].
    unfold region_of. apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold blk_lo in *; lia.
  - destruct CB as (sc & Hsc & L1 & L2). unfold in_some_sec_map.
    rewrite (existsb_In _ (as_sec s) sc Hsc); [rewrite orb_true_r; reflexivity|].
    apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold blk_lo, kPageSize in *; lia.
Qed.

(* [comment removed for export] *)
Corollary live_block_Sh : forall s cb cm i g, AWF s -> as_chunks s !! cb = Some cm -> cm_state cm = CAllocated i ->
  cm_user_beg cm <= 8 * g < cm_user_beg cm + cm_n cm ->
  Sh E s (8 * g) = Some (if 8 * g + 8 <=? cm_user_beg cm + cm_n cm then 0 else cm_n cm mod 8).
Proof.
  intros s cb cm i g WF Hcm ST Hg.
  pose proof (chunk_user_in_block s cb cm WF Hcm) as (A & B & _). unfold user_lo, user_hi in *.
  pose proof (chunk_user_aligned s cb cm WF Hcm) as AL. unfold user_lo in AL.
  rewrite (block_Sh s cb cm (8 * g) WF Hcm ltac:(lia)). f_equal.
  unfold chunk_shadow. rewrite ST.
  set (ub := cm_user_beg cm) in *. set (n := cm_n cm) in *.
  pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
  apply Z.mod_divide in AL; [|lia]. destruct AL as [q Hq].
  replace (8 * g <? ub) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (8 * g + 8 <=? ub + n) eqn:C.
  - apply Z.leb_le in C. replace (8 * g <? ub + n / 8 * 8) with true by (symmetry; apply Z.ltb_lt; nia). reflexivity.
  - apply Z.leb_gt in C. replace (8 * g <? ub + n / 8 * 8) with false by (symmetry; apply Z.ltb_ge; nia).
    replace (8 * g <? ub + n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Corollary live_block_Sh_hull : forall s cb cm a, AWF s -> as_chunks s !! cb = Some cm ->
  cm_user_beg cm - 8 <= a < round_up (cm_user_beg cm + cm_n cm) 8 -> exists v, Sh E s a = Some v.
Proof.
  intros s cb cm a WF Hcm Ha. eexists. apply (block_Sh s cb cm a WF Hcm).
  pose proof (chunk_user_in_block s cb cm WF Hcm) as (A & B & _). unfold user_lo, user_hi in *.
  split; [lia|].
  (* [comment removed for export] *)
  assert (AL8 : blk_hi s cm mod 8 = 0).
  { pose proof (chunk_user_aligned s cb cm WF Hcm) as UA. unfold user_lo, cm_user_beg in UA.
    unfold blk_hi. pose proof WF as X. destruct X as (WE & WR & WC & [K1 _] & WQ & (_ & _ & S3 & _) & _). destruct (K1 _ _ Hcm) as (_ & Bn & C & D0 & _).
    destruct (cm_prim cm) as [c|].
    - destruct D0 as (D1 & D2 & _). assert (Hc : 1 <= c <= kLargestClassID).
      { subst c. apply malloc_class_ok. pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1). lia. }
      pose proof (class_size_mod c Hc) as [CM _]. pose proof (rz_size_mod16 (cm_n cm)) as RM. rewrite C in UA.
      change (16 * 2 ^ rz_log (cm_n cm)) with (rz_size (cm_n cm)) in UA.
      apply Z.mod_divide in CM; [|lia]. destruct CM as [q Hq]. apply Z.mod_divide in RM; [|lia]. destruct RM as [q' Hq'].
      apply Z.mod_divide in UA; [|lia]. destruct UA as [u Hu]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (2 * u - 2 * q' + 4 * q). lia.
    - pose proof (map_size_facts (cm_n cm)) as (MM & _). destruct D0 as (_ & sc & Hsc & Hab & Hms & _).
      destruct (S3 sc Hsc) as (AL & _). rewrite Hab. unfold kPageSize in *.
      apply Z.mod_divide in AL; [|lia]. destruct AL as [q Hq]. apply Z.mod_divide in MM; [|lia]. destruct MM as [q' Hq'].
      apply Z.mod_divide; [lia|]. exists (512 * q + 512 * q'). lia. }
  pose proof (round_up_lt (cm_user_beg cm + cm_n cm) 8 ltac:(lia)). pose proof (round_up_mod (cm_user_beg cm + cm_n cm) 8 ltac:(lia)).
  apply Z.mod_divide in AL8; [|lia]. destruct AL8 as [p Hp].
  match goal with H : round_up _ 8 mod 8 = 0 |- _ => apply Z.mod_divide in H; [|lia]; destruct H as [r Hr] end. nia.
Qed.

(* [comment removed for export] *)
Lemma ARep_shadow_cells : forall segs DepotR s m g v,
  ARep segs E DepotR s m -> Sh E s (8 * g) = Some v -> rw_cells segs m (kShadowBase + g) [C1 (zb v)].
Proof. intros segs DepotR s m g v (_ & _ & _ & _ & _ & _ & _ & _ & _ & SH) H. exact (SH g v H). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_map_in_space : forall s a, AWF s -> in_some_region_map E s a = true -> SB <= a < SB + kSpaceSize.
Proof.
  intros s a WF H. pose proof WF as (WE & [WR0 WR] & _).
  assert (RG : forall c, 0 <= c < 32 -> let r := region_of s c in 0 <= rg_mapped_user r <= kFreeArrayOffset /\ 0 <= rg_mapped_fa r <= kFreeArraySize).
  { intros c Hc. destruct (Z_le_dec 1 c); [destruct (Z_le_dec c kLargestClassID)|].
    - destruct (WR c ltac:(lia)) as (A1 & _ & A2 & _ & A3 & _ & A4 & _). cbn. lia.
    - unfold region_of, get_region. destruct (as_regions s !! c) as [r|] eqn:Hr; [pose proof (WR0 c r Hr); lia|]. cbn. unfold kFreeArrayOffset, kFreeArraySize; lia.
    - unfold region_of, get_region. destruct (as_regions s !! c) as [r|] eqn:Hr; [pose proof (WR0 c r Hr); lia|]. cbn. unfold kFreeArrayOffset, kFreeArraySize; lia. }
  unfold in_some_region_map in H. apply orb_true_iff in H as [H|H]; apply existsb_exists in H as (c & Hc & Hb);
    apply In_ziota in Hc; apply andb_true_iff in Hb as [B1 B2]; apply Z.leb_le in B1; apply Z.ltb_lt in B2;
    destruct (RG c ltac:(lia)) as [R1 R2]; unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *; cbn in *; lia.
Qed.

(* [comment removed for export] *)
Lemma reserved_range_no_map : forall s a lo n, AWF s -> In (lo, n) (ae_reserved E) ->
  (lo + n <= ae_resv_beg E \/ ae_resv_beg E + 0x2000011000 <= lo) -> lo <= a < lo + n ->
  in_some_region_map E s a = false /\ in_some_sec_map s a = false.
Proof.
  intros s a lo n WF HIN DJ Ha. pose proof WF as (WE & _ & _ & _ & _ & (_ & _ & S3 & _) & _).
  pose proof WE as (_ & E2 & E3 & E4 & _).
  split.
  - destruct (in_some_region_map E s a) eqn:RM; [| reflexivity]. exfalso. pose proof (region_map_in_space s a WF RM). unfold kSpaceSize in *. lia.
  - destruct (in_some_sec_map s a) eqn:SM; [| reflexivity]. exfalso. unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb).
    apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
    destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). specialize (RSV _ HIN). cbn [fst snd] in RSV. lia.
Qed.

Lemma Sh_fs_none : forall s a, AWF s -> in_fakestack E a = true -> Sh E s a = None.
Proof.
  intros s a WF FS. pose proof WF as ((_ & E2 & E3 & E4 & _ & _ & _ & _ & E9' & E9 & E10 & E11 & _) & _).
  pose proof FS as FS'. unfold in_fakestack in FS'. apply andb_true_iff in FS' as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2.
  destruct (reserved_range_no_map s a _ _ WF E9' E11 ltac:(lia)) as [RM SM].
  unfold Sh. rewrite RM, SM. cbn [orb]. unfold sh_excluded. rewrite FS. cbn [orb negb]. rewrite andb_false_r. reflexivity.
Qed.

Lemma Sh_iarena_none : forall s a, AWF s -> in_iarena E a = true -> Sh E s a = None.
Proof.
  intros s a WF IA. pose proof WF as (WE & _). pose proof WE as (_ & E2 & E3 & E4 & WE').
  repeat match type of WE' with _ /\ _ => destruct WE' as [?X WE'] end.
  match goal with H : In (ae_iarena E, kIArenaLen) (ae_reserved E) |- _ => rename H into IIN end.
  match goal with H : ae_iarena E + kIArenaLen <= ae_resv_beg E \/ _ |- _ => rename H into IDJ end.
  pose proof IA as IA'. unfold in_iarena in IA'. apply andb_true_iff in IA' as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2.
  destruct (reserved_range_no_map s a _ _ WF IIN IDJ ltac:(lia)) as [RM SM].
  unfold Sh. rewrite RM, SM. cbn [orb]. unfold sh_excluded. rewrite IA. rewrite orb_true_r. cbn [orb negb]. rewrite andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Sh_reginfo_none : forall s a, AWF s -> in_reginfo E a = true -> Sh E s a = None.
Proof.
  intros s a WF RI. pose proof WF as (WE & _ & _ & _ & _ & (_ & _ & S3 & _) & _). pose proof WE as (_ & E2 & E3 & E4 & _).
  pose proof RI as RI'. unfold in_reginfo in RI'. apply andb_true_iff in RI' as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2.
  assert (RM : in_some_region_map E s a = false).
  { destruct (in_some_region_map E s a) eqn:RM; [| reflexivity]. exfalso. pose proof (region_map_in_space s a WF RM). lia. }
  assert (SM : in_some_sec_map s a = false).
  { destruct (in_some_sec_map s a) eqn:SM; [| reflexivity]. exfalso. unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb).
    apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
    destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof WE as (_ & _ & _ & _ & _ & _ & RIN & _).
    specialize (RSV _ RIN). cbn [fst snd] in RSV. unfold kPageSize, kSpaceSize in *. lia. }
  unfold Sh. rewrite RM, SM. cbn [orb]. unfold sh_excluded. rewrite RI. rewrite !orb_true_r. cbn [negb]. rewrite andb_false_r. reflexivity.
Qed.

Lemma Sh_excluded_none : forall s a, AWF s -> sh_excluded E a = true -> Sh E s a = None.
Proof.
  intros s a WF H. unfold sh_excluded in H. apply orb_true_iff in H as [H|H]; [apply orb_true_iff in H as [H|H]|];
    [apply Sh_fs_none| apply Sh_iarena_none| apply Sh_reginfo_none]; assumption.
Qed.

Lemma sh_default_dom_high : forall a, kHighMemBeg <= a <= kHighMemEnd -> sh_default_dom E a = true.
Proof.
  intros a Ha. unfold sh_default_dom. apply orb_true_iff. right. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.
Lemma sh_default_dom_low : forall a, 0 <= a < kLowAppEnd -> in_img E a = false -> sh_default_dom E a = true.
Proof.
  intros a Ha Hi. unfold sh_default_dom. apply orb_true_iff. left. rewrite Hi. apply andb_true_iff. split; [| reflexivity].
  apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma Sh_outside_zero_dom : forall s a, sh_default_dom E a = true -> sh_excluded E a = false ->
  in_some_region_map E s a = false -> in_some_sec_map s a = false -> Sh E s a = Some 0.
Proof.
  intros s a Ha FS RM SM. unfold Sh. rewrite RM, SM, FS, Ha. reflexivity.
Qed.
Lemma Sh_outside_zero : forall s a, kHighMemBeg <= a <= kHighMemEnd -> sh_excluded E a = false ->
  in_some_region_map E s a = false -> in_some_sec_map s a = false -> Sh E s a = Some 0.
Proof. intros s a Ha. apply Sh_outside_zero_dom. apply sh_default_dom_high. exact Ha. Qed.

(* [comment removed for export] *)
Lemma Sh_total_dom : forall s a, sh_default_dom E a = true -> sh_excluded E a = false -> exists v, Sh E s a = Some v.
Proof.
  intros s a Ha FS. unfold Sh. destruct (in_some_region_map E s a || in_some_sec_map s a); [eexists; reflexivity|].
  rewrite FS, Ha. eexists; reflexivity.
Qed.
Lemma Sh_total : forall s a, kHighMemBeg <= a <= kHighMemEnd -> sh_excluded E a = false -> exists v, Sh E s a = Some v.
Proof. intros s a Ha. apply Sh_total_dom. apply sh_default_dom_high. exact Ha. Qed.

End CL.
End RC__1.
