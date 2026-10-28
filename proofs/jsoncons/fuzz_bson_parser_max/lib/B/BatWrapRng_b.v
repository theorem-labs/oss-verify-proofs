(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatCellEx_b BatPoison_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b BatFsInv_b BatFsInvLaws_b Ba0RegionPoisoned_b Ba0AsanMemcpy_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatWrapC_b BatWrapVis_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma keeps_cs_preserved : forall R R' : bvmap 5 word, keeps_cs R R' -> regs_preserved R R'.
Proof.
  intros R R' KC r Hr. unfold callee_saved_idx in Hr. rewrite <- (Z_to_bv_bv_unsigned _ r). set (z := bv_unsigned r) in *. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [apply KC; unfold callee_saved; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right] |]). destruct Hr.
Qed.
(* [comment removed for export] *)
Ltac lit_cell H :=
  unfold cell in H;
  match type of H with rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
    match goal with |- rdn _ _ ?w _ = _ => replace w with (Z_to_bv 64 a : word) by (apply bv_eq; reflexivity); exact H end end.
(* [comment removed for export] *)
Ltac conj_find H := first [ exact H | exact (proj1 H) | let H' := fresh in pose proof (proj2 H) as H'; conj_find H' ].
Lemma le1_one : word_to_le_bytes 1 (Z_to_bv 64 1) = [Z_to_bv 8 1].
Proof. vm_compute. repeat f_equal; apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Lemma art_cli_facts : forall rn LB FF LK A (M : word -> option byte), art_client_ok rn LB FF LK A M ->
  shadow_allowed A (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn)) /\ shadow_allowed A (ar_fs (rn_ar rn)) FS_BYTES
  /\ shadow_allowed A 0x10000 (0x696000 - 0x10000) /\ ar_sptop (rn_ar rn) + 16 <= 2 ^ 47.
Proof. intros rn LB FF LK A M (_ & _ & C3 & C4 & _ & _ & _ & _ & _ & _ & C11 & C12 & _). repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma art_rng_off_window : forall p n lo hi, 0 < n -> lo < hi -> (forall i, 0 <= i < n -> ~ (lo <= p + i < hi)) -> p + n <= lo \/ hi <= p.
Proof.
  intros p n lo hi Hn Hw OFF. destruct (Z_lt_le_dec p hi) as [Lt | Ge]; [left | right; exact Ge].
  pose proof (OFF 0 ltac:(lia)) as O0. rewrite Z.add_0_r in O0.
  destruct (Z_lt_le_dec lo (p + n)) as [X | X]; [|lia].
  exfalso. apply (OFF (lo - p) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma in_block_dec : forall (LB : list (Z * Z)) x, in_block LB x \/ ~ in_block LB x.
Proof.
  induction LB as [|b LB IH]; intros x; [right; intros (b & [] & _)|].
  destruct (IH x) as [H | H]; [left; destruct H as (b' & Hb' & R); exists b'; split; [right; exact Hb' | exact R]|].
  destruct (Z_le_gt_dec (fst b) x) as [L1 | L1]; [destruct (Z_lt_le_dec x (fst b + snd b)) as [L2 | L2]|].
  - left. exists b. split; [left; reflexivity | lia].
  - right. intros (b' & [<- | Hb'] & R); [lia | apply H; exists b'; split; assumption].
  - right. intros (b' & [<- | Hb'] & R); [lia | apply H; exists b'; split; assumption].
Qed.
Lemma in_fframe_dec : forall (FF : list fframe) x, in_fframe FF x \/ ~ in_fframe FF x.
Proof.
  induction FF as [|f FF IH]; intros x; [right; intros (f & [] & _)|].
  destruct (IH x) as [H | H]; [left; destruct H as (f' & Hf' & R); exists f'; split; [right; exact Hf' | exact R]|].
  assert (D : (ff_addr f <= x < ff_addr f + ff_bytes (ff_class f) - 8 /\ ~ (ff_addr f + 24 <= x < ff_addr f + 32))
              \/ ~ (ff_addr f <= x < ff_addr f + ff_bytes (ff_class f) - 8 /\ ~ (ff_addr f + 24 <= x < ff_addr f + 32))) by lia.
  destruct D as [D | D].
  - left. exists f. split; [left; reflexivity | exact D].
  - right. intros (f' & [<- | Hf'] & R); [exact (D R) | apply H; exists f'; split; assumption].
Qed.

Section Rng.
Variable rn : art_run.
Variables (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (M : word -> option byte) (model : Model).
Hypothesis LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
  0x696000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES).
Hypothesis CLI : art_client_ok rn LB FF LK A M.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Variable g : art_fsg.
Hypothesis FS : art_fsinv rn g FF LK M.
Hypothesis SHDEF : forall a : word, in_shadow_rw (U a) -> M a <> None.           (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="LB FF LK A M CLI"] Lemma art_cli_hi : 0x7fff7f800000 <= rn_HI rn /\ rn_HI rn + 8388608 + 16 <= 2 ^ 47.
Proof. pose proof CLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & C10 & _ & C12 & _). unfold rn_HI. lia. Qed.
#[local] Ltac hi_facts := pose proof art_cli_hi as (HI1 & HI2).

#[local] Abbreviation Mr0 := (mrestrict (bhid A model) M).
#[local] Abbreviation cls := (fun sp scr a => hl_img_lo L <= a < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp scr a).

(* [comment removed for export] *)
#[using="LK A M CLI HLlo HLhi g FS"] Lemma art_cls_off_scratch : forall sp scr a, rn_HI rn <= sp - scr -> cls sp scr a -> ~ (sp - scr <= a < sp).
Proof.
  intros sp scr a SHI Ha X. pose proof CLI as (C1 & _). hi_facts.
  pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & _ & G3 & _).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
  destruct Ha as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; rewrite ?HLlo, ?HLhi in H.
  - lia.
  - destruct H as (b' & Hb' & Rb). destruct (C1 b' Hb') as (_ & _ & _ & _ & K5 & _). rewrite HIeq in K5. lia.
  - lia.
  - lia.
  - destruct H as (f & Hf & R1 & _). pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). unfold FS_BYTES in *. lia.
  - destruct H as (_ & X2). pose proof (art_S_hi (ahl_ceil (rn_ar rn) + (2 ^ 47 - ahl_ceil (rn_ar rn)) - 1) ltac:(lia)). lia.
  - destruct H as (f & Hf & (_ & X2)). pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
    unfold FS_BYTES in *. pose proof (art_S_hi (ff_addr f + ff_bytes (ff_class f) - 1) ltac:(lia)). lia.
  - destruct H as (b' & Hb' & (_ & X2)). destruct (C1 b' Hb') as (_ & _ & _ & _ & K5 & _). rewrite HIeq in K5.
    pose proof (art_S_hi (fst b' + snd b' - 1) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
#[using="LK M CLI HLlo HLhi g FS"] Lemma art_rng_shadow_allowed : forall sp scr b n a, 0 <= b ->
  (forall i, 0 <= i < n -> cls sp scr (b + i)) ->
  (b + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= b) -> b + n <= 2 ^ 47 ->
  b <= a < b + n -> page_allowedb A (page_base (Z_to_bv 64 (HeapIfaceA.S a))) = true.
Proof.
  intros sp scr b n a Hb CLS APP TOP Ha. hi_facts. specialize (CLS (a - b) ltac:(lia)). replace (b + (a - b)) with a in CLS by ring. cbn beta in CLS. rewrite HLlo, HLhi in CLS.
  pose proof CLI as (C1 & _). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (SAst & SAfs & IMGSH & _).
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
  - exfalso. pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & G2 & G3 & _). apply (NOSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [unfold rn_HI in *; lia | lia | unfold rn_HI in *; lia | exact H].
  - exfalso. destruct H as (f & Hf & H). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
    pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & G2 & G3 & _). unfold FS_BYTES in *. apply (NOSH (ff_addr f) (ff_bytes (ff_class f))); [lia | unfold rn_HI in *; lia | exact I3 | exact H].
  - exfalso. destruct H as (b' & Hb' & H). destruct (C1 b' Hb') as (K1 & _ & _ & K4 & K5 & _). apply (NOSH (fst b') (snd b')); [lia | unfold rn_HI in *; lia | exact K4 | exact H].
Qed.

(* [comment removed for export] *)
#[using="LB FF LK A M CLI"] Lemma art_rng_app8 : forall p n, 0 <= p -> 0 <= n -> app_rng (rn_ar rn) p n -> in_app8 p n.
Proof.
  intros p n Hp Hn (_ & APP & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16).
  unfold in_app8, LOWEND, HIGHBEG, HIGHEND. unfold BIGSHADOW_LO, BIGSHADOW_HI in APP. destruct APP as [X | X]; [left | right]; lia.
Qed.

(* [comment removed for export] *)
#[using="LK LAZY CLI HLlo HLhi g FS SHDEF"] Lemma art_rng_facts : forall sp scr p n, 0 <= p -> 0 < n -> n <= 2 ^ 40 ->
  (forall i, 0 <= i < n -> cls sp scr (p + i)) -> aacc M p n -> app_rng (rn_ar rn) p n ->
  let fS := Ba0RegionPoisoned_b.SB + p / 8 in let lS := Ba0RegionPoisoned_b.SB + (p + n - 1) / 8 in
  art_vis (bhid A model) p n
  /\ (Ba0RegionPoisoned_b.SB <= fS <= lS /\ lS + 8 <= rn_HI rn)
  /\ (forall x : word, fS <= U x < lS -> Mr0 x = Some (Z_to_bv 8 0))
  /\ (exists k, Mr0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 k) /\ (k = 0 \/ (p + n - 1) mod 8 < k <= 7))
  /\ (exists w0 w1, rdn ASEGS Mr0 (Z_to_bv 64 (fS - fS mod 8)) 8 = Some w0 /\ rdn ASEGS Mr0 (Z_to_bv 64 (lS - lS mod 8)) 8 = Some w1).
Proof.
  intros sp scr p n Hp Hn Hn40 CLS AACC APPR fS lS. pose proof APPR as (_ & APP & TOP). hi_facts.
  destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16).
  assert (P47 : p + n + 16 <= 2 ^ 47) by (clear - TOP T16; lia).
  assert (VSH : forall a, p <= a < p + n -> page_allowedb A (page_base (Z_to_bv 64 (HeapIfaceA.S a))) = true).
  { intros a Ha. apply (art_rng_shadow_allowed sp scr p n a Hp CLS APP ltac:(lia) Ha). }
  assert (FL : Ba0RegionPoisoned_b.SB <= fS <= lS /\ lS < 0x10007fff8000).
  { unfold fS, lS, Ba0RegionPoisoned_b.SB. pose proof (art_S_lo p Hp). pose proof (art_S_hi (p + n - 1) ltac:(lia)). pose proof (art_S_mono p (p + n - 1) ltac:(lia)).
    unfold HeapIfaceA.S, HeapIfaceA.SB in *. lia. }
  assert (SfS : HeapIfaceA.S p = fS) by (unfold HeapIfaceA.S, HeapIfaceA.SB, fS, Ba0RegionPoisoned_b.SB; lia).
  assert (SlS : HeapIfaceA.S (p + n - 1) = lS) by (unfold HeapIfaceA.S, HeapIfaceA.SB, lS, Ba0RegionPoisoned_b.SB; lia).
  assert (VSHx : forall x, fS <= x <= lS -> page_allowedb A (page_base (Z_to_bv 64 x)) = true).
  { intros x Hx. destruct (art_shadow_preimage p n x Hp Hn ltac:(rewrite SfS, SlS; exact Hx)) as (a & Ha & Sa). rewrite <- Sa. apply VSH. exact Ha. }
  unfold Ba0RegionPoisoned_b.SB in FL.
  assert (RfS : 0 <= fS /\ lS < 2 ^ 64) by lia.
  split.
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
    apply (art_aclient_vis rn LB FF LK A M model LAZY CLI L HLlo HLhi g FS sp scr (U x)); [pose proof (u64_range x); lia|].
    replace (U x) with (p + (U x - p)) by ring. apply CLS. lia. }
  split. { unfold Ba0RegionPoisoned_b.SB. lia. }
  split.
  { intros x Hx. unfold mrestrict. rewrite (art_vis_allowed A model x ltac:(rewrite <- (Z_to_bv_bv_unsigned 64 x); apply VSHx; lia)).
    pose proof (art_aacc_zero M p n Hp Hn AACC (U x) ltac:(unfold fS, lS, Ba0RegionPoisoned_b.SB in Hx; lia)) as Bz.
    unfold byte_at in Bz. rewrite Z_to_bv_bv_unsigned in Bz. exact Bz. }
  split.
  { destruct (art_aacc_last M p n Hn AACC) as (kS & BkS & HkS). exists kS. split; [|exact HkS].
    unfold mrestrict. rewrite (art_vis_allowed A model (Z_to_bv 64 lS) ltac:(apply VSHx; lia)). exact BkS. }
  assert (SHRW : forall y q, fS <= q <= lS -> q - q mod 8 <= y < q - q mod 8 + 8 -> in_shadow_rw y /\ page_allowedb A (page_base (Z_to_bv 64 y)) = true).
  { intros y q Hq Hy. pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Rq.
    assert (E8 : y / 8 = q / 8). { symmetry. apply (Z.div_unique y 8 (q / 8) (y - 8 * (q / 8))); clear - Hy Dq Rq; lia. }
    assert (Ry : 0 <= y < 2 ^ 64 /\ 0 <= q < 2 ^ 64) by (clear - Hy Hq RfS Rq FL; lia).
    split.
    - unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI. unfold BIGSHADOW_LO, BIGSHADOW_HI in APP.
      pose proof (Z.div_mod p 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Rs.
      pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Re.
      assert (EfS : fS = 0x7fff8000 + p / 8) by reflexivity. assert (ElS : lS = 0x7fff8000 + (p + n - 1) / 8) by reflexivity.
      clear - APP Hy Hq Dq Rq Ds Rs De Re EfS ElS Hn Hn40 Hp P47. destruct APP as [X | X]; [left | right]; lia.
    - rewrite (art_page_base_word y q (proj1 Ry) (proj2 Ry) E8). apply VSHx. exact Hq. }
  assert (DEF8 : forall q, fS <= q <= lS -> exists w, rdn ASEGS Mr0 (Z_to_bv 64 (q - q mod 8)) 8 = Some w).
  { intros q Hq. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Rq.
    destruct (art_rdn_defined 8 Mr0 (q - q mod 8) ltac:(lia) ltac:(cbn; lia)) as (w & Hw & _); [|exists w; exact Hw].
    intros x Hx. cbn in Hx. destruct (SHRW (U x) q Hq ltac:(lia)) as (RW & AL).
    unfold mrestrict. rewrite (art_vis_allowed A model x ltac:(rewrite <- (Z_to_bv_bv_unsigned 64 x); exact AL)).
    exact (SHDEF x RW). }
  destruct (DEF8 fS ltac:(lia)) as (w0 & H0). destruct (DEF8 lS ltac:(lia)) as (w1 & H1). exists w0, w1. split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_rng_rdn : forall p (n : nat) bs, 0 <= p -> p + Z.of_nat n < 2 ^ 64 -> art_vis (bhid A model) p (Z.of_nat n) ->
  rdn ASEGS M (Z_to_bv 64 p) n = Some bs -> rdn ASEGS Mr0 (Z_to_bv 64 p) n = Some bs.
Proof.
  intros p n bs Hp Hn V RD. rewrite (rdn_mrestrict_eq ASEGS (bhid A model) n M (Z_to_bv 64 p)); [exact RD|].
  apply (art_vis_avoids (bhid A model) p n Hp Hn V).
Qed.
#[using="Type"] Lemma art_rng_store_ok : forall p (n : nat), 0 <= p -> p + Z.of_nat n < 2 ^ 64 -> art_vis (bhid A model) p (Z.of_nat n) ->
  store_ok ASEGS M (Z_to_bv 64 p) n = true -> store_ok ASEGS Mr0 (Z_to_bv 64 p) n = true.
Proof.
  intros p n Hp Hn V OK. rewrite (art_store_ok_ext ASEGS n Mr0 M (Z_to_bv 64 p)); [exact OK | rewrite art_u_lit by lia; lia |].
  intros x Hx. rewrite art_u_lit in Hx by lia. unfold mrestrict. rewrite (V x Hx). reflexivity.
Qed.
(* [comment removed for export] *)
Hypothesis HLroimg : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x696000.
#[using="LK A M CLI g FS HLroimg"] Lemma art_clientw_not_private : forall sp scr x, aclientw L (rn_ar rn) LB FF sp scr x -> (x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) ->
  ~ art_private L (rn_ar rn) LB FF x.
Proof.
  intros sp scr x CW APP PRIV. hi_facts. pose proof CLI as (C1 & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in APP.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
  pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & G2 & G3 & G4 & _).
  assert (NOSH : forall a y, 0 <= a -> a + y <= 2 ^ 47 -> 0 < y -> in_shadow_of a y x -> False).
  { intros a y Ha Hay Hy (X1 & X2). pose proof (art_S_lo a Ha). pose proof (art_S_hi (a + y - 1) ltac:(lia)). lia. }
  unfold aclientw, aclient_g in CW.
  destruct PRIV as [NC | [RO | (b & Hb & BS)]].
  - apply NC. unfold aclient, aclient_g.
    destruct CW as [H|[H|[H|[H|[H|[H|H]]]]]].
    + left; exact H.
    + right; left. split; [exact (proj1 H) | lia].
    + right; right; left. split; [exact (proj1 H) | intros X; apply (proj2 H); left; exact X].
    + do 3 right; left; exact H.
    + do 4 right; left; exact H.
    + do 5 right; left; exact H.
    + destruct H as (b & _ & []).
  - pose proof (HLroimg x RO) as IM.
    destruct CW as [H|[H|[H|[H|[H|[H|H]]]]]].
    + destruct H as (b & Hb & Rb). destruct (C1 b Hb) as (_ & K2 & _). lia.
    + lia.
    + apply (proj2 H). right; exact RO.
    + destruct H as (f & Hf & R1 & _). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). unfold FS_BYTES in *. lia.
    + apply (NOSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [lia | lia | lia | exact H].
    + destruct H as (f & Hf & H). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
      unfold FS_BYTES in *. apply (NOSH (ff_addr f) (ff_bytes (ff_class f))); [lia | lia | exact I3 | exact H].
    + destruct H as (b & _ & []).
  - destruct (C1 b Hb) as (K1 & _ & _ & K4 & K5 & _). apply (NOSH (fst b) (snd b)); [lia | lia | exact K4 | exact BS].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma art_clientw_cls : forall sp scr x, aclientw L (rn_ar rn) LB FF sp scr x -> cls sp scr x.
Proof. intros sp scr x H. right. apply aclientw_client. exact H. Qed.
(* [comment removed for export] *)
Hypothesis HLstimg : forall a, hl_rt_static L a -> 0x10000 <= a < 0x696000.
#[using="LK A M CLI g FS HLstimg"] Lemma art_clientw_not_static : forall sp scr x, aclientw L (rn_ar rn) LB FF sp scr x -> (x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) -> ~ hl_rt_static L x.
Proof.
  intros sp scr x CW APP ST. hi_facts. pose proof CLI as (C1 & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in APP. pose proof (HLstimg x ST) as IM.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
  pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & G2 & G3 & G4 & _).
  assert (NOSH : forall a y, 0 <= a -> a + y <= 2 ^ 47 -> 0 < y -> in_shadow_of a y x -> False).
  { intros a y Ha Hay Hy (X1 & X2). pose proof (art_S_lo a Ha). pose proof (art_S_hi (a + y - 1) ltac:(lia)). lia. }
  unfold aclientw, aclient_g in CW.
  destruct CW as [H|[H|[H|[H|[H|[H|H]]]]]].
  + destruct H as (b & Hb & Rb). destruct (C1 b Hb) as (_ & K2 & _). lia.
  + lia.
  + apply (proj2 H). left; exact ST.
  + destruct H as (f & Hf & R1 & _). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). unfold FS_BYTES in *. lia.
  + apply (NOSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [lia | lia | lia | exact H].
  + destruct H as (f & Hf & H). pose proof (fsinv_frame_in rn g FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
    unfold FS_BYTES in *. apply (NOSH (ff_addr f) (ff_bytes (ff_class f))); [lia | lia | exact I3 | exact H].
  + destruct H as (b & _ & []).
Qed.
End Rng.
