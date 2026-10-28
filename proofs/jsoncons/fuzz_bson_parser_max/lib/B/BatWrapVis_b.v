(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatLift_b BatFsInv_b BatFsInvLaws_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section Vis.
Variable rn : art_run.
Variables (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (M : word -> option byte) (model : Model).
(* [comment removed for export] *)
Hypothesis LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
  0x696000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES).
Hypothesis CLI : art_client_ok rn LB FF LK A M.

#[using="Type"] Lemma art_vis_notlazy : forall x : word, page_in_ranges (page_base x) (m_vm_lazy model) = false -> bhid A model x = false.
Proof. intros x H. unfold bhid, mkH. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma art_vis_allowed : forall x : word, page_allowedb A (page_base x) = true -> bhid A model x = false.
Proof. intros x H. unfold bhid, mkH. rewrite H. apply andb_false_r. Qed.
#[using="LAZY"] Lemma art_vis_byte : forall x : word,
  (U x < 0x696000 \/ rn_HI rn <= U x \/ in_block LB (U x) \/ ar_fs (rn_ar rn) <= U x < ar_fs (rn_ar rn) + FS_BYTES) -> bhid A model x = false.
Proof.
  intros x H. apply art_vis_notlazy. destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:E; [|reflexivity]. exfalso.
  destruct (LAZY x E) as (L1 & L2 & L3 & L4). destruct H as [H | [H | [H | H]]]; [lia | lia | exact (L3 H) | exact (L4 H)].
Qed.
#[using="Type"] Lemma art_vis_shadow : forall a n x, shadow_allowed A a n -> in_shadow_of a n x -> bhid A model (Z_to_bv 64 x) = false.
Proof. intros a n x SA Hx. apply art_vis_allowed. exact (SA x Hx). Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma in_shadow_of_sub : forall a n a' n' x, a <= a' -> a' + n' <= a + n -> 0 < n' -> in_shadow_of a' n' x -> in_shadow_of a n x.
Proof.
  intros a n a' n' x H1 H2 Hn (X1 & X2). unfold in_shadow_of, HeapIfaceA.S in *.
  assert (a / 8 <= a' / 8) by (apply Z.div_le_mono; lia). assert ((a' + n' - 1) / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* [comment removed for export] *)
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Variable g : art_fsg.
Hypothesis FS : art_fsinv rn g FF LK M.

#[using="LK M LAZY CLI HLlo HLhi g FS"] Lemma art_aclient_vis : forall sp scr a, 0 <= a < 2 ^ 64 ->
  (hl_img_lo L <= a < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp scr a) -> bhid A model (Z_to_bv 64 a) = false.
Proof.
  intros sp scr a Ra H. rewrite HLlo, HLhi in H.
  pose proof CLI as (C1 & _ & SAst & SAfs & _).
  assert (UA : U (Z_to_bv 64 a) = a) by (apply art_u_lit; exact Ra).
  destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
  - apply art_vis_byte. rewrite UA. lia.
  - apply art_vis_byte. rewrite UA. right; right; left. exact H.
  - apply art_vis_byte. rewrite UA. right; left. unfold rn_HI. lia.
  - apply art_vis_byte. rewrite UA. rewrite HLlo, HLhi in H. lia.
  - apply art_vis_byte. rewrite UA. right; right; right. destruct H as (f & Hf & R1 & _).
    pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). unfold FS_BYTES in *. lia.
  - exact (art_vis_shadow _ _ _ SAst H).
  - destruct H as (f & Hf & H). apply (art_vis_shadow (ar_fs (rn_ar rn)) FS_BYTES a SAfs).
    pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
    apply (in_shadow_of_sub _ _ (ff_addr f) (ff_bytes (ff_class f))); [lia | lia | lia | exact H].
  - destruct H as (b & Hb & H). destruct (C1 b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & SAb & _). exact (art_vis_shadow _ _ _ SAb H).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_S_mono : forall a b, a <= b -> HeapIfaceA.S a <= HeapIfaceA.S b.
Proof. intros a b H. unfold HeapIfaceA.S. assert (a / 8 <= b / 8) by (apply Z.div_le_mono; lia). lia. Qed.
#[using="Type"] Lemma art_S_lo : forall a, 0 <= a -> 0x7fff8000 <= HeapIfaceA.S a.
Proof. intros a H. unfold HeapIfaceA.S, HeapIfaceA.SB. assert (0 <= a / 8) by (apply Z.div_pos; lia). lia. Qed.
#[using="Type"] Lemma art_S_hi : forall a, a < 2 ^ 47 -> HeapIfaceA.S a < 0x10007fff8000.
Proof. intros a H. unfold HeapIfaceA.S, HeapIfaceA.SB. assert (a / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415 in *. lia. Qed.
#[using="Type"] Lemma art_in_shadow_of_S : forall lo n a, lo <= a < lo + n -> in_shadow_of lo n (HeapIfaceA.S a).
Proof. intros lo n a H. split; apply art_S_mono; lia. Qed.

Hypothesis IMGSH : shadow_allowed A 0x10000 (0x696000 - 0x10000).

#[using="LK M CLI HLlo HLhi g FS IMGSH"] Lemma art_buf_shadow_allowed : forall sp scr b n a, 0 <= b ->
  (forall i, 0 <= i < n -> hl_img_lo L <= b + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp scr (b + i)) ->
  (b + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= b) -> b + n <= ar_sptop (rn_ar rn) ->
  b <= a < b + n -> page_allowedb A (page_base (Z_to_bv 64 (HeapIfaceA.S a))) = true.
Proof.
  intros sp scr b n a Hb CLS APP TOP Ha. specialize (CLS (a - b) ltac:(lia)). replace (b + (a - b)) with a in CLS by ring. rewrite HLlo, HLhi in CLS.
  pose proof CLI as (C1 & _ & SAst & SAfs & _ & _ & _ & _ & _ & CT).
  pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & G2 & _ & _ & (_ & _ & G7) & _).
  unfold BIGSHADOW_LO, BIGSHADOW_HI in APP.
  assert (NOSH : forall x y, 0 <= x -> x + y <= 2 ^ 47 -> 0 < y -> in_shadow_of x y a -> False).
  { intros x y Hx Hxy Hy (X1 & X2). pose proof (art_S_lo x Hx). pose proof (art_S_hi (x + y - 1) ltac:(lia)). lia. }
  destruct CLS as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
  - apply IMGSH. apply art_in_shadow_of_S. lia.
  - destruct H as (b' & Hb' & R). destruct (C1 b' Hb') as (_ & _ & _ & _ & _ & _ & _ & _ & SAb & _). apply SAb. apply art_in_shadow_of_S. exact R.
  - apply SAst. apply art_in_shadow_of_S. lia.
  - apply IMGSH. apply art_in_shadow_of_S. lia.
  - destruct H as (f & Hf & R1 & _). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
    apply SAfs. apply art_in_shadow_of_S. unfold FS_BYTES in *. lia.
  - exfalso. apply (NOSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [lia | lia | lia | exact H].
  - exfalso. destruct H as (f & Hf & H). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
    unfold FS_BYTES in *. apply (NOSH (ff_addr f) (ff_bytes (ff_class f))); [lia | lia | exact I3 | exact H].
  - exfalso. destruct H as (b' & Hb' & H). destruct (C1 b' Hb') as (K1 & _ & _ & K4 & K5 & _). apply (NOSH (fst b') (snd b')); [lia | lia | exact K4 | exact H].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_page_base_word : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x / 8 = y / 8 -> page_base (Z_to_bv 64 x) = page_base (Z_to_bv 64 y).
Proof.
  intros x y Hx Hy E. unfold page_base, page_base_of, page_size. rewrite !art_u_lit by lia.
  replace (x / 4096) with (x / 8 / 512) by (rewrite Z.div_div by lia; reflexivity). replace (y / 4096) with (y / 8 / 512) by (rewrite Z.div_div by lia; reflexivity).
  rewrite E. reflexivity.
Qed.
End Vis.

(* [comment removed for export] *)
Lemma art_aacc_zero : forall (M : word -> option byte) p n, 0 <= p -> 0 < n -> aacc M p n ->
  forall x, 0x7fff8000 + p / 8 <= x < 0x7fff8000 + (p + n - 1) / 8 -> byte_at M x 0.
Proof.
  intros M p n Hp Hn AC x Hx. set (a := 8 * (x - 0x7fff8000) + 7).
  pose proof (Z.div_mod p 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as R1.
  pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as R2.
  assert (Ha : p <= a < p + n) by (unfold a; lia).
  assert (Sa : HeapIfaceA.S a = x).
  { unfold HeapIfaceA.S, HeapIfaceA.SB, a. replace (8 * (x - 2147450880) + 7) with (7 + (x - 2147450880) * 8) by ring. rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
  assert (Ma : a mod 8 = 7).
  { unfold a. replace (8 * (x - 2147450880) + 7) with (7 + (x - 2147450880) * 8) by ring. rewrite Z.mod_add by lia. reflexivity. }
  destruct (AC a Ha) as [Z0 | (v & Bv & Rv & Lv)]; [rewrite Sa in Z0; exact Z0 | lia].
Qed.
Lemma art_aacc_last : forall (M : word -> option byte) p n, 0 < n -> aacc M p n ->
  exists k, byte_at M (0x7fff8000 + (p + n - 1) / 8) k /\ (k = 0 \/ (p + n - 1) mod 8 < k <= 7).
Proof.
  intros M p n Hn AC. destruct (AC (p + n - 1) ltac:(lia)) as [Z0 | (v & Bv & Rv & Lv)]; unfold HeapIfaceA.S, HeapIfaceA.SB in *.
  - exists 0. split; [rewrite Z.add_comm; exact Z0 | left; reflexivity].
  - exists v. split; [rewrite Z.add_comm; exact Bv | right; lia].
Qed.

(* [comment removed for export] *)
Lemma art_shadow_preimage : forall b n x, 0 <= b -> 0 < n -> HeapIfaceA.S b <= x <= HeapIfaceA.S (b + n - 1) -> exists a, b <= a < b + n /\ HeapIfaceA.S a = x.
Proof.
  intros b n x Hb Hn (X1 & X2). unfold HeapIfaceA.S, HeapIfaceA.SB in *.
  pose proof (Z.div_mod b 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound b 8 ltac:(lia)) as R1.
  pose proof (Z.div_mod (b + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (b + n - 1) 8 ltac:(lia)) as R2.
  destruct (Z.eq_dec (x - 2147450880) (b / 8)) as [E | NE].
  - exists b. split; [lia | lia].
  - exists (8 * (x - 2147450880)). split; [lia|]. replace (8 * (x - 2147450880)) with (0 + (x - 2147450880) * 8) by ring. rewrite Z.div_add by lia. change (0 / 8) with 0. lia.
Qed.
