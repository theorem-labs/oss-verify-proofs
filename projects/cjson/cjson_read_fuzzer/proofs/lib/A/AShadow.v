(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma SHADOW_OFFSET_val : SHADOW_OFFSET = 2147450880.
Proof. reflexivity. Qed.

Lemma SH_def : forall a, SH a = SHADOW_OFFSET + a / 8.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma SH_shiftr : forall a, Z.shiftr a 3 + 2147450880 = SH a.
Proof. intros a. rewrite Z.shiftr_div_pow2 by lia. unfold SH, SHADOW_OFFSET. lia. Qed.

Lemma SH_mono : forall a b, a <= b -> SH a <= SH b.
Proof. intros a b H. unfold SH. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.

Lemma SH_eq_iff : forall a b, SH a = SH b <-> a / 8 = b / 8.
Proof. intros a b. unfold SH. lia. Qed.

Lemma SH_granule : forall g r, 0 <= r < 8 -> SH (8 * g + r) = SHADOW_OFFSET + g.
Proof. intros g r Hr. unfold SH. f_equal. Z.div_mod_to_equations. lia. Qed.

Lemma SH_aligned_add : forall A i, A mod 8 = 0 -> SH (A + i) = SH A + i / 8.
Proof. intros A i HA. unfold SH. Z.div_mod_to_equations. lia. Qed.

Lemma SH_succ_granule : forall a, SH (a + 8) = SH a + 1.
Proof. intros a. unfold SH. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma SH_same : forall a b, a / 8 = b / 8 -> SH a = SH b.
Proof. intros a b H. unfold SH. lia. Qed.

Lemma same_granule_aligned : forall a k, (k = 1 \/ k = 2 \/ k = 4 \/ k = 8) -> a mod k = 0 ->
  forall i, 0 <= i < k -> (a + i) / 8 = a / 8.
Proof. intros a k Hk Ha i Hi. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma SH_range_card : forall lo hi, lo < hi -> SH (hi - 1) - SH lo <= (hi - lo) / 8 + 1.
Proof. intros lo hi H. unfold SH. Z.div_mod_to_equations. lia. Qed.

Lemma SH_lt_of : forall a b, a / 8 < b / 8 -> SH a < SH b.
Proof. intros a b H. unfold SH. lia. Qed.

(* [comment removed for export] *)
Lemma SH_low : forall a, 0 <= a < SHADOW_OFFSET -> KLOWSHADOW_BEG <= SH a < KLOWSHADOW_END.
Proof. intros a H. unfold SH, SHADOW_OFFSET, KLOWSHADOW_BEG, KLOWSHADOW_END in *. Z.div_mod_to_equations. lia. Qed.

Lemma SH_high : forall a, KHIGHMEM_BEG <= a <= KHIGHMEM_END -> KHIGHSHADOW_BEG <= SH a < KHIGHSHADOW_END.
Proof.
  intros a H. unfold SH, SHADOW_OFFSET, KHIGHMEM_BEG, KHIGHMEM_END, KHIGHSHADOW_BEG, KHIGHSHADOW_END in *.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma SH_bounds : forall a, 0 <= a < 2^47 -> 2147450880 <= SH a < 0x10007fff8000.
Proof. intros a H. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. Qed.

Lemma SH_below_ceiling : forall a, 0 <= a < 2^47 -> SH a + 8 <= alloc_ceiling.
Proof.
  intros a H. unfold SH, SHADOW_OFFSET. unfold alloc_ceiling, sp_window_lo, stack_max_size.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition shpage (a : Z) : Z := SH a / 4096 * 4096.
Lemma shpage_le : forall a, shpage a <= SH a < shpage a + 4096.
Proof. intros a. unfold shpage. Z.div_mod_to_equations. lia. Qed.
Lemma shpage_aligned : forall a, shpage a mod 4096 = 0.
Proof. intros a. unfold shpage. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Lemma shpage_same : forall a b, a / 32768 = b / 32768 -> SHADOW_OFFSET mod 4096 = 0 -> shpage a = shpage b.
Proof. intros a b H _. unfold shpage, SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition shchk (m : word -> option byte) (a k : Z) : Prop :=
  exists v, shb m a v /\ (v = 0 \/ (a mod 8 + k <= v /\ v <= 7)).

(* [comment removed for export] *)
Definition sh_zero (m : word -> option byte) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> shb m a 0.

(* [comment removed for export] *)
Definition sh_vis (m : word -> option byte) (lo hi : Z) : Prop :=
  forall j, SH lo / 8 * 8 <= j < SH (hi - 1) / 8 * 8 + 8 -> m (wa j) <> None.

(* [comment removed for export] *)
Definition sh_bytes (m : word -> option byte) (g8 : Z) (vs : list Z) : Prop :=
  cells_at asegs m (SH g8) (shcells vs).

(* [comment removed for export] *)
Definition shbase_cells (m : word -> option byte) : Prop :=
  ro_cells asegs m 0xa1f80 [C8 (Z_to_bv 64 0xaa278)]
  /\ ro_cells asegs m 0xaa278 [C8 (Z_to_bv 64 0x7fff8000)].

Definition uar_cells (m : word -> option byte) : Prop :=
  ro_cells asegs m 0xa1fd8 [C8 (Z_to_bv 64 0xaa280)]
  /\ ro_cells asegs m 0xaa280 [C4 (Z_to_bv 64 1)].

Lemma shbase_cells_addrs :
  GOT_SHADOW_OFF = 0xa1f80 /\ A_SHADOW_OFF_CELL = 0xaa278 /\ SHADOW_OFFSET = 0x7fff8000
  /\ GOT_UAR = 0xa1fd8 /\ A_UAR_OPTION = 0xaa280.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zb_inj_small : forall v w, 0 <= v < 256 -> 0 <= w < 256 -> zb v = zb w -> v = w.
Proof.
  intros v w Hv Hw E. unfold zb in E.
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 8) with 256 in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma shb_functional : forall m a v w, shb m a v -> shb m a w -> 0 <= v < 256 -> 0 <= w < 256 -> v = w.
Proof. intros m a v w H1 H2 Hv Hw. unfold shb in *. rewrite H1 in H2. apply zb_inj_small; auto. congruence. Qed.

Lemma shb_same_granule : forall m a b v, a / 8 = b / 8 -> shb m a v -> shb m b v.
Proof. intros m a b v E H. unfold shb in *. rewrite <- (SH_same a b E). exact H. Qed.

Lemma shb_vis : forall m a v, shb m a v -> m (wa (SH a)) <> None.
Proof. intros m a v H. unfold shb in H. rewrite H. discriminate. Qed.

Lemma shchk_of_shb0 : forall m a k, shb m a 0 -> shchk m a k.
Proof. intros m a k H. exists 0. split; [exact H| left; reflexivity]. Qed.

Lemma shchk_weaken : forall m a k k', shchk m a k -> k' <= k -> shchk m a k'.
Proof. intros m a k k' (v & H & Hv) Hk. exists v. split; [exact H| lia]. Qed.

Lemma sh_zero_shb : forall m lo hi a, sh_zero m lo hi -> lo <= a < hi -> shb m a 0.
Proof. intros m lo hi a H Ha. apply H. exact Ha. Qed.

Lemma sh_zero_shchk : forall m lo hi a k, sh_zero m lo hi -> lo <= a < hi -> shchk m a k.
Proof. intros. apply shchk_of_shb0. eapply sh_zero_shb; eauto. Qed.

Lemma sh_zero_sub : forall m lo hi lo' hi', sh_zero m lo hi -> lo <= lo' -> hi' <= hi -> sh_zero m lo' hi'.
Proof. intros m lo hi lo' hi' H Hl Hh a Ha. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma sh_zero_granules : forall m lo hi, sh_zero m lo hi -> lo < hi ->
  sh_zero m (lo / 8 * 8) ((hi - 1) / 8 * 8 + 8).
Proof.
  intros m lo hi H Hlt a Ha.
  destruct (Z.lt_ge_cases a lo) as [Hlo|Hlo].
  - apply (shb_same_granule m lo). { Z.div_mod_to_equations. lia. } apply H. lia.
  - destruct (Z.lt_ge_cases a hi) as [Hhi|Hhi]. { apply H. lia. }
    apply (shb_same_granule m (hi - 1)). { Z.div_mod_to_equations. lia. } apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_ok_shb : forall m A n i, shadow_ok m A n -> 0 <= i < n ->
  exists v, shb m (A + i) v /\ (v = 0 \/ ((A + i) mod 8 < v /\ v < 8)).
Proof. intros m A n i [H _] Hi. exact (H i Hi). Qed.

Lemma shadow_ok_vis : forall m A n, shadow_ok m A n -> sh_vis m A (A + n).
Proof. intros m A n [_ H] j Hj. apply H. exact Hj. Qed.

(* [comment removed for export] *)
Lemma shadow_ok_shchk : forall m A n a k,
  shadow_ok m A n -> A <= a -> a + k <= A + n ->
  (k = 1 \/ k = 2 \/ k = 4 \/ k = 8) -> a mod k = 0 ->
  shchk m a k.
Proof.
  intros m A n a k SO H1 H2 Hk Hal.
  (nelim (shadow_ok_shb m A n (a - A) SO ltac:(lia)) 3%nat; intros v Hv Cv).
  replace (A + (a - A)) with a in * by lia.
  exists v. split; [exact Hv|].
  destruct Cv as [Cv|[Cv1 Cv2]]; [left; exact Cv| right].
  (nelim (shadow_ok_shb m A n (a + (k - 1) - A) SO ltac:(lia)) 3%nat; intros v' Hv' Cv').
  replace (A + (a + (k - 1) - A)) with (a + (k - 1)) in * by lia.
  assert (G : (a + (k - 1)) / 8 = a / 8) by (apply (same_granule_aligned a k Hk Hal); lia).
  apply (shb_same_granule m _ a) in Hv'; [|exact G].
  assert (v' = v) by (eapply shb_functional; eauto; lia). subst v'.
  destruct Cv' as [Cv'|[Cv1' Cv2']]; [lia|].
  split; [|lia]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_ok_shchk1 : forall m A n a, shadow_ok m A n -> A <= a < A + n -> shchk m a 1.
Proof. intros. eapply shadow_ok_shchk; eauto; lia. Qed.

Lemma shadow_ok_sub : forall m A n A' n', shadow_ok m A n -> A <= A' -> A' + n' <= A + n -> 0 < n' ->
  shadow_ok m A' n'.
Proof.
  intros m A n A' n' [H V] H1 H2 H3. split.
  - intros i Hi. (nelim (H (A' + i - A) ltac:(lia)) 3%nat; intros v Hv Cv).
    replace (A + (A' + i - A)) with (A' + i) in * by lia. exists v. auto.
  - intros j Hj. apply V.
    pose proof (SH_mono A A' H1). pose proof (SH_mono (A' + n' - 1) (A + n - 1) ltac:(lia)).
    Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_ok_sh_zero : forall m A n lo hi,
  shadow_ok m A n -> A <= lo -> lo mod 8 = 0 -> hi <= A + n -> (hi - lo) mod 8 = 0 ->
  sh_zero m lo hi.
Proof.
  intros m A n lo hi SO H1 H2 H3 H4 a Ha.
  destruct (shadow_ok_shchk m A n (a / 8 * 8) 8 SO) as (v & Hv & Cv); (* [comment removed for export] *)
    [Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| lia| Z.div_mod_to_equations; lia|].
  apply (shb_same_granule m (a / 8 * 8) a) in Hv; [| Z.div_mod_to_equations; lia].
  destruct Cv as [->|[C1v C2v]]; [exact Hv|]. exfalso. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma asegs_noseg_high : forall x : word, AIMG_HI <= bv_unsigned x -> noseg asegs x.
Proof.
  intros x Hx s Hs. unfold AIMG_HI in Hx. cbn in Hs.
  destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia.
Qed.

Lemma asegs_rom_shadow : forall a, 0 <= a < 2^47 -> seg_rom asegs (wa (SH a)) = None.
Proof.
  intros a Ha. apply seg_rom_noseg. apply asegs_noseg_high.
  pose proof (SH_bounds a Ha). unfold AIMG_HI. rewrite wa_unsigned; lia.
Qed.

Lemma mrd_shadow : forall m a b, 0 <= a < 2^47 -> mrd asegs m (wa (SH a)) = Some b -> m (wa (SH a)) = Some b.
Proof.
  intros m a b Ha H. unfold mrd in H. destruct (m (wa (SH a))) as [b'|] eqn:E; [congruence|].
  rewrite asegs_rom_shadow in H by exact Ha. discriminate.
Qed.

Lemma shcells_length : forall vs, length (shcells vs) = length vs.
Proof. intros vs. unfold shcells. apply length_map. Qed.

Lemma shcells_wf : forall vs, cells_wf (shcells vs).
Proof. unfold shcells. induction vs as [|v vs IH]; cbn; [exact I|]. split; [exact I| exact IH]. Qed.

Lemma shcells_bytes : forall vs, cells_bytes (shcells vs) = map zb vs.
Proof. unfold shcells. induction vs as [|v vs IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma shcells_size : forall vs, cells_size (shcells vs) = length vs.
Proof. unfold shcells. induction vs as [|v vs IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sh_bytes_shb : forall m g8 vs i v a,
  sh_bytes m g8 vs -> g8 mod 8 = 0 -> nth_error vs i = Some v ->
  g8 + 8 * Z.of_nat i <= a < g8 + 8 * Z.of_nat i + 8 -> 0 <= a < 2^47 ->
  shb m a v.
Proof.
  intros m g8 vs i v a [Hwf HB] Hal Hn Ha Ha47.
  rewrite shcells_bytes in HB. (nelim HB 3%nat; intros H0 H1 HB).
  assert (Hi : (i < length vs)%nat).
  { destruct (Nat.lt_ge_cases i (length vs)) as [Hlt|Hge]; [exact Hlt|].
    apply (proj2 (nth_error_None vs i)) in Hge. congruence. }
  specialize (HB i ltac:(rewrite length_map; exact Hi)).
  rewrite (map_nth_error zb i vs Hn) in HB.
  assert (E : SH g8 + Z.of_nat i = SH a) by (unfold SH; Z.div_mod_to_equations; lia).
  rewrite E in HB. unfold shb. apply mrd_shadow; [exact Ha47| exact HB].
Qed.

Lemma rw_cells_sh_bytes : forall m g8 vs, rw_cells asegs m (SH g8) (shcells vs) -> sh_bytes m g8 vs.
Proof. intros m g8 vs [H _]. exact H. Qed.

(* [comment removed for export] *)
Lemma sh_bytes_zero : forall m g8 n, sh_bytes m g8 (repeat 0 n) -> g8 mod 8 = 0 ->
  0 <= g8 -> g8 + 8 * Z.of_nat n <= 2^47 ->
  sh_zero m g8 (g8 + 8 * Z.of_nat n).
Proof.
  intros m g8 n H Hal H0 Hhi a Ha.
  set (i := Z.to_nat ((a - g8) / 8)).
  eapply (sh_bytes_shb m g8 (repeat 0 n) i 0 a H Hal).
  - apply nth_error_repeat. subst i. Z.div_mod_to_equations. lia.
  - subst i. Z.div_mod_to_equations. lia.
  - lia.
Qed.

Lemma rw_cells_sh_zero : forall m g8 n, rw_cells asegs m (SH g8) (shcells (repeat 0 n)) -> g8 mod 8 = 0 ->
  0 <= g8 -> g8 + 8 * Z.of_nat n <= 2^47 -> sh_zero m g8 (g8 + 8 * Z.of_nat n).
Proof. intros. apply sh_bytes_zero; auto. apply rw_cells_sh_bytes. assumption. Qed.

(* [comment removed for export] *)
Lemma shadow_enc_length : forall n, 0 <= n -> Z.of_nat (length (shadow_enc n)) = (n + 7) / 8.
Proof.
  intros n Hn. unfold shadow_enc. rewrite length_app, repeat_length.
  destruct (Z.eqb_spec (n mod 8) 0); cbn [length]; Z.div_mod_to_equations; lia.
Qed.

Lemma shadow_enc_nth_zero : forall n i, 0 <= n -> (Z.of_nat i < n / 8) ->
  nth_error (shadow_enc n) i = Some 0.
Proof.
  intros n i Hn Hi. unfold shadow_enc. rewrite nth_error_app1 by (rewrite repeat_length; lia).
  apply nth_error_repeat. lia.
Qed.

Lemma shadow_enc_nth_last : forall n, 0 <= n -> n mod 8 <> 0 ->
  nth_error (shadow_enc n) (Z.to_nat (n / 8)) = Some (n mod 8).
Proof.
  intros n Hn Hm. unfold shadow_enc. rewrite nth_error_app2 by (rewrite repeat_length; lia).
  rewrite repeat_length, Nat.sub_diag. destruct (Z.eqb_spec (n mod 8) 0); [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma shadow_enc_shb : forall m A n a,
  sh_bytes m A (shadow_enc n) -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 -> A <= a < A + n ->
  shb m a (if (a - A) / 8 <? n / 8 then 0 else n mod 8).
Proof.
  intros m A n a H Hal HA Hn Ha.
  destruct (Z.ltb_spec ((a - A) / 8) (n / 8)) as [L|L].
  - eapply (sh_bytes_shb m A (shadow_enc n) (Z.to_nat ((a - A) / 8)) 0 a H Hal).
    + apply shadow_enc_nth_zero; [lia|]. Z.div_mod_to_equations. lia.
    + Z.div_mod_to_equations. lia.
    + lia.
  - assert (Hm : n mod 8 <> 0) by (Z.div_mod_to_equations; lia).
    assert (E : (a - A) / 8 = n / 8) by (Z.div_mod_to_equations; lia).
    eapply (sh_bytes_shb m A (shadow_enc n) (Z.to_nat (n / 8)) (n mod 8) a H Hal).
    + apply shadow_enc_nth_last; lia.
    + Z.div_mod_to_equations. lia.
    + lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_enc_addressable : forall m A n i,
  sh_bytes m A (shadow_enc n) -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 -> 0 <= i < n ->
  exists v, shb m (A + i) v /\ (v = 0 \/ ((A + i) mod 8 < v /\ v < 8)).
Proof.
  intros m A n i H Hal HA Hn Hi.
  pose proof (shadow_enc_shb m A n (A + i) H Hal HA Hn ltac:(lia)) as SB.
  eexists. split; [exact SB|].
  destruct (Z.ltb_spec ((A + i - A) / 8) (n / 8)); [left; reflexivity| right].
  Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_enc_shchk : forall m A n a k,
  sh_bytes m A (shadow_enc n) -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  A <= a -> a + k <= A + n -> (k = 1 \/ k = 2 \/ k = 4 \/ k = 8) -> a mod k = 0 ->
  shchk m a k.
Proof.
  intros m A n a k H Hal HA Hn H1 H2 Hk Hak.
  pose proof (shadow_enc_shb m A n a H Hal HA Hn ltac:(lia)) as SB.
  eexists. split; [exact SB|].
  destruct (Z.ltb_spec ((a - A) / 8) (n / 8)); [left; reflexivity| right].
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_enc_sh_zero : forall m A n,
  sh_bytes m A (shadow_enc n) -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  sh_zero m A (A + n / 8 * 8).
Proof.
  intros m A n H Hal HA Hn a Ha.
  pose proof (shadow_enc_shb m A n a H Hal HA Hn ltac:(Z.div_mod_to_equations; lia)) as SB.
  destruct (Z.ltb_spec ((a - A) / 8) (n / 8)); [exact SB|]. exfalso. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bytes_at_pointwise : forall m a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall i b, nth_error bs i = Some b -> m (wa (a + Z.of_nat i)) = Some b) ->
  bytes_at asegs m a bs.
Proof.
  intros m a bs Ha Hl H. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. destruct (nth_error bs i) as [b|] eqn:E.
  - unfold mrd. rewrite (H i b E). reflexivity.
  - apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_ok_full_granule : forall m A n g,
  shadow_ok m A n -> A <= 8 * g + 7 -> 8 * g + 8 <= A + n -> m (wa (SHADOW_OFFSET + g)) = Some (zb 0).
Proof.
  intros m A n g SO H1 H2.
  (nelim (shadow_ok_shb m A n (8 * g + 7 - A) SO ltac:(lia)) 3%nat; intros v Hv Cv).
  replace (A + (8 * g + 7 - A)) with (8 * g + 7) in * by lia.
  unfold shb in Hv. rewrite (SH_granule g 7) in Hv by lia.
  destruct Cv as [->|[C1 C2]]; [exact Hv|]. exfalso. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_ok_mid_zeros : forall m A n,
  shadow_ok m A n -> 0 <= A -> A + n < 2^47 ->
  let sb := SH ((A + 7) / 8 * 8) in let se := SH ((A + n) / 8 * 8) in
  sb <= se ->
  bytes_at asegs m sb (repeat (Z_to_bv 8 0) (Z.to_nat (se - sb))).
Proof.
  intros m A n SO HA Hn sb se Hle.
  assert (R1 : 2147450880 <= sb) by (subst sb; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia).
  assert (R2 : se < 0x10007fff8000) by (subst se; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia).
  apply bytes_at_pointwise; [lia| rewrite repeat_length; lia|].
  intros i b E.
  assert (Hi : (i < Z.to_nat (se - sb))%nat).
  { destruct (Nat.lt_ge_cases i (Z.to_nat (se - sb))) as [L|L]; [exact L|].
    rewrite (proj2 (nth_error_None _ _)) in E; [congruence|]. rewrite repeat_length. exact L. }
  rewrite nth_error_repeat in E by exact Hi. inversion E; subst b.
  replace (sb + Z.of_nat i) with (SHADOW_OFFSET + ((A + 7) / 8 + Z.of_nat i)).
  2:{ subst sb. unfold SH. lia. }
  change (Z_to_bv 8 0) with (zb 0).
  apply (shadow_ok_full_granule m A n); [exact SO| Z.div_mod_to_equations; lia|].
  subst sb se. unfold SH in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_ok_head_zeros : forall m A n j,
  shadow_ok m A n -> SH A <= j < SH (A + n - 1) -> m (wa j) = Some (zb 0).
Proof.
  intros m A n j SO Hj.
  replace j with (SHADOW_OFFSET + (j - SHADOW_OFFSET)) by lia.
  apply (shadow_ok_full_granule m A n); [exact SO| |]; unfold SH in Hj; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma vis_read8 : forall m lo,
  (forall j, lo <= j < lo + 8 -> m (wa j) <> None) -> 0 <= lo -> lo + 8 <= 2^64 ->
  exists bs, length bs = 8%nat /\ ov_read_bytes asegs m (wa lo) 8 = Some bs.
Proof.
  intros m lo V H0 H8.
  assert (G : forall k, (k <= 8)%nat -> exists bs, length bs = k /\
            forall i, (i < k)%nat -> m (wa (lo + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - (nelim (IH ltac:(lia)) 3%nat; intros bs Hl Hb).
      destruct (m (wa (lo + Z.of_nat k))) as [b|] eqn:E.
      2:{ exfalso. apply (V (lo + Z.of_nat k)); [lia| exact E]. }
      exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|NE].
      + rewrite nth_error_app2, Hl, Nat.sub_diag by lia. exact E.
      + rewrite nth_error_app1 by lia. apply Hb. lia. }
  (nelim (G 8%nat ltac:(lia)) 3%nat; intros bs Hl Hb). exists bs. split; [exact Hl|].
  replace (wa lo) with (wa (lo + 0)) by (f_equal; lia).
  assert (BA : bytes_at asegs m lo bs).
  { split; [lia|]. split; [rewrite Hl; lia|]. intros i Hi. unfold mrd. rewrite (Hb i ltac:(lia)).
    destruct (nth_error bs i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia. }
  rewrite (bytes_at_read asegs m lo bs 0 8 BA ltac:(lia) ltac:(rewrite Hl; cbn; lia)).
  replace (skipn (Z.to_nat 0) bs) with bs by reflexivity.
  rewrite firstn_all2; [reflexivity| rewrite Hl; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shb_ext : forall m m' a v, shb m a v -> m' (wa (SH a)) = m (wa (SH a)) -> shb m' a v.
Proof. intros m m' a v H E. unfold shb in *. rewrite E. exact H. Qed.

Lemma shb_munch : forall W m m' a v, shb m a v -> munch W m m' ->
  0 <= SH a < 2^64 -> outside W (SH a) -> shb m' a v.
Proof.
  intros W m m' a v H MU HR HO. eapply shb_ext; [exact H|]. apply MU. rewrite wa_unsigned by lia. exact HO.
Qed.

Lemma shb_munch_disjoint : forall W m m' a v, shb m a v -> munch W m m' ->
  0 <= SH a < 2^64 -> disjoint_from W (SH a) 1 -> shb m' a v.
Proof.
  intros W m m' a v H MU HR HD. eapply shb_munch; eauto. eapply disjoint_outside; [exact HD| lia].
Qed.

Lemma shchk_munch_disjoint : forall W m m' a k, shchk m a k -> munch W m m' ->
  0 <= SH a < 2^64 -> disjoint_from W (SH a) 1 -> shchk m' a k.
Proof. intros W m m' a k (v & H & C) MU HR HD. exists v. split; [eapply shb_munch_disjoint; eauto| exact C]. Qed.

Lemma sh_zero_munch : forall W m m' lo hi, sh_zero m lo hi -> munch W m m' ->
  0 <= SH lo -> SH (hi - 1) < 2^64 ->
  disjoint_from W (SH lo) (SH (hi - 1) + 1 - SH lo) -> sh_zero m' lo hi.
Proof.
  intros W m m' lo hi H MU H0 H1 HD a Ha.
  pose proof (SH_mono lo a ltac:(lia)). pose proof (SH_mono a (hi - 1) ltac:(lia)).
  eapply shb_munch; [apply H; exact Ha| exact MU| lia|].
  eapply disjoint_outside; [exact HD|]. lia.
Qed.

Lemma sh_vis_munch : forall W m m' lo hi, sh_vis m lo hi -> munch W m m' ->
  0 <= SH lo / 8 * 8 -> SH (hi - 1) / 8 * 8 + 8 <= 2^64 ->
  disjoint_from W (SH lo / 8 * 8) (SH (hi - 1) / 8 * 8 + 8 - SH lo / 8 * 8) -> sh_vis m' lo hi.
Proof.
  intros W m m' lo hi H MU H0 H1 HD j Hj. rewrite (MU (wa j)).
  - apply H. exact Hj.
  - rewrite wa_unsigned by lia. eapply disjoint_outside; [exact HD|]. lia.
Qed.

Lemma shadow_ok_munch : forall W m m' A n, shadow_ok m A n -> munch W m m' -> 0 < n ->
  0 <= SH A / 8 * 8 -> SH (A + n - 1) / 8 * 8 + 8 <= 2^64 ->
  disjoint_from W (SH A / 8 * 8) (SH (A + n - 1) / 8 * 8 + 8 - SH A / 8 * 8) -> shadow_ok m' A n.
Proof.
  intros W m m' A n [H V] MU Hn H0 H1 HD. split.
  - intros i Hi. (nelim (H i Hi) 3%nat; intros v Hv Cv). exists v. split; [|exact Cv].
    pose proof (SH_mono A (A + i) ltac:(lia)). pose proof (SH_mono (A + i) (A + n - 1) ltac:(lia)).
    eapply shb_munch; [exact Hv| exact MU| Z.div_mod_to_equations; lia|].
    eapply disjoint_outside; [exact HD|]. Z.div_mod_to_equations; lia.
  - intros j Hj. rewrite (MU (wa j)).
    + apply V. exact Hj.
    + rewrite wa_unsigned by lia. eapply disjoint_outside; [exact HD|]. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_zero_ext : forall m m' lo hi,
  sh_zero m lo hi -> (forall j, SH lo <= j <= SH (hi - 1) -> m' (wa j) = m (wa j)) -> sh_zero m' lo hi.
Proof.
  intros m m' lo hi H E a Ha. eapply shb_ext; [apply H; exact Ha|]. apply E.
  split; apply SH_mono; lia.
Qed.

Lemma shchk_ext : forall m m' a k, shchk m a k -> m' (wa (SH a)) = m (wa (SH a)) -> shchk m' a k.
Proof. intros m m' a k (v & H & C) E. exists v. split; [eapply shb_ext; eauto| exact C]. Qed.

Lemma sh_vis_ext : forall m m' lo hi,
  sh_vis m lo hi -> (forall j, SH lo / 8 * 8 <= j < SH (hi - 1) / 8 * 8 + 8 -> m' (wa j) = m (wa j)) ->
  sh_vis m' lo hi.
Proof. intros m m' lo hi H E j Hj. rewrite (E j Hj). apply H. exact Hj. Qed.

Lemma shadow_ok_ext : forall m m' A n,
  shadow_ok m A n -> 0 < n ->
  (forall j, SH A / 8 * 8 <= j < SH (A + n - 1) / 8 * 8 + 8 -> m' (wa j) = m (wa j)) ->
  shadow_ok m' A n.
Proof.
  intros m m' A n [H V] Hn E. split.
  - intros i Hi. (nelim (H i Hi) 3%nat; intros v Hv Cv). exists v. split; [|exact Cv].
    eapply shb_ext; [exact Hv|]. apply E.
    pose proof (SH_mono A (A + i) ltac:(lia)). pose proof (SH_mono (A + i) (A + n - 1) ltac:(lia)).
    Z.div_mod_to_equations. lia.
  - intros j Hj. rewrite (E j Hj). apply V. exact Hj.
Qed.

(* [comment removed for export] *)
Lemma shb_write_other : forall m a v (w : Z) bs,
  shb m a v -> 0 <= w -> w + Z.of_nat (length bs) <= 2^64 -> 0 <= SH a < 2^64 ->
  (SH a + 1 <= w \/ w + Z.of_nat (length bs) <= SH a) ->
  shb (write_to_mem m (wa w) bs) a v.
Proof.
  intros m a v w bs H Hw Hl HR HD. eapply shb_munch_disjoint; [exact H| | exact HR|].
  - apply (munch_write [(w, w + Z.of_nat (length bs))] m m w bs); [apply munch_refl| exact Hw| exact Hl|]. cbn. lia.
  - cbn. lia.
Qed.

Lemma shbase_cells_munch : forall W m m', shbase_cells m -> munch W m m' ->
  disjoint_from W 0xa1f80 8 -> disjoint_from W 0xaa278 8 -> shbase_cells m'.
Proof.
  intros W m m' [G1 G2] MU D1 D2. split; (eapply ro_cells_transport; [eassumption| exact MU| cbn; assumption]).
Qed.

Lemma uar_cells_munch : forall W m m', uar_cells m -> munch W m m' ->
  disjoint_from W 0xa1fd8 8 -> disjoint_from W 0xaa280 4 -> uar_cells m'.
Proof.
  intros W m m' [G1 G2] MU D1 D2. split; (eapply ro_cells_transport; [eassumption| exact MU| cbn; assumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shb_load : forall m a v E,
  shb m a v -> E = a -> 0 <= a ->
  ov_read_bytes asegs m (Z_to_bv 64 (Z.shiftr E 3 + 2147450880)) 1 = Some [zb v].
Proof.
  intros m a v E H -> Ha. rewrite SH_shiftr. unfold shb in H.
  rewrite ov_rdn. cbn [rdn]. unfold mrd. fold (wa (SH a)). rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shb_load' : forall m a v E,
  shb m a v -> E = a -> 0 <= a ->
  ov_read_bytes asegs m (Z_to_bv 64 (2147450880 + Z.shiftr E 3)) 1 = Some [zb v].
Proof. intros m a v E H HE Ha. rewrite Z.add_comm. apply (shb_load m a v E H HE Ha). Qed.

(* [comment removed for export] *)
Lemma shb_load_div : forall m a v E,
  shb m a v -> E = a -> 0 <= a ->
  ov_read_bytes asegs m (Z_to_bv 64 (E / 8 + 2147450880)) 1 = Some [zb v].
Proof. intros m a v E H HE Ha. change 8 with (2 ^ 3). rewrite <- (Z.shiftr_div_pow2 E 3) by lia. apply (shb_load m a v E H HE Ha). Qed.

Lemma shb_load_div' : forall m a v E,
  shb m a v -> E = a -> 0 <= a ->
  ov_read_bytes asegs m (Z_to_bv 64 (2147450880 + E / 8)) 1 = Some [zb v].
Proof. intros m a v E H HE Ha. change 8 with (2 ^ 3). rewrite <- (Z.shiftr_div_pow2 E 3) by lia. apply (shb_load' m a v E H HE Ha). Qed.

(* [comment removed for export] *)
Lemma shb_load_at : forall m a v (x : word),
  shb m a v -> bv_unsigned x = SH a ->
  ov_read_bytes asegs m x 1 = Some [zb v].
Proof.
  intros m a v x H Hx. unfold shb in H.
  replace x with (wa (SH a)).
  - rewrite ov_rdn. cbn [rdn]. unfold mrd. rewrite H. reflexivity.
  - apply bv_eq. rewrite <- Hx. unfold wa. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma sxb_zb_small : forall v, 0 <= v < 128 -> sxb (zb v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sxb, zb. f_equal. rewrite Z_to_bv_signed. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. cbn. lia.
Qed.

Lemma zxb_zb : forall v, 0 <= v < 256 -> bv_unsigned (zb v) = v.
Proof. intros v Hv. unfold zb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma zxb_zb_w : forall v, 0 <= v < 256 -> zxb (zb v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zxb. f_equal. apply zxb_zb. exact Hv. Qed.

Lemma signed_lit_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. cbn [Z.of_N]. change (2^64 `div` 2) with (2^63). lia.
Qed.

Lemma land7_mod : forall e, 0 <= e -> Z.land e 7 = e mod 8.
Proof. intros e He. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac shbase_split SB :=
  let G1 := fresh "GOTSH" in let G2 := fresh "SHOFF" in
  destruct SB as [G1 G2].

Ltac uar_split SB :=
  let G1 := fresh "GOTUAR" in let G2 := fresh "UAROPT" in
  destruct SB as [G1 G2].

(* [comment removed for export] *)
Ltac evt_mem :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => m end.

(* [comment removed for export] *)
Ltac sh_transport_via MU H :=
  lazymatch type of H with
  | shb _ _ _ => apply (fun HH => shb_munch_disjoint _ _ _ _ _ HH MU) in H;
                 [| unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia ]
  | shchk _ _ _ => apply (fun HH => shchk_munch_disjoint _ _ _ _ _ HH MU) in H;
                 [| unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia ]
  | sh_zero _ _ _ => apply (fun HH => sh_zero_munch _ _ _ _ _ HH MU) in H;
                 [| unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia
                  | unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia
                  | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia ]
  | shadow_ok _ _ _ => apply (fun HH => shadow_ok_munch _ _ _ _ _ HH MU) in H;
                 [| lia
                  | unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia
                  | unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia
                  | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia ]
  end.

Ltac sh_now H :=
  let m := evt_mem in
  lazymatch type of H with
  | ?P m _ _ => idtac
  | ?P ?m0 _ _ =>
      lazymatch goal with
      | MU : munch _ m0 m |- _ => sh_transport_via MU H
      | _ => fail "sh_now: no hypothesis [munch W" m0 m "] to transport" H
      end
  end.


(* [comment removed for export] *)
Ltac addr_diff_ok k :=
  let t := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 16384))%Z in
  lazymatch t with true => idtac | false => fail end.

Ltac solve_load_base ::=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | (* [comment removed for export] *)
                replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_store ::=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                (* [comment removed for export] *)
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

Ltac stepL_store_ok ::=
  lazymatch goal with
  | |- store_ok ?segs ?m ?a ?n = true /\ ?a = ?a' =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          split;
          [ apply (rw_cells_store_ok_at segs m A cs kn c0 n a H); first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]
          | unify a' (wa (A + Z.of_nat kn)%Z); addr_eq_tac ]
        end
    | HS : store_ok segs m ?a2 n = true |- _ =>
        split; [ first [ exact HS | rewrite <- HS; f_equal; word_eq_tac ] | first [ unify a' a2; first [reflexivity | word_eq_tac] | reflexivity ] ]
    end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition chk_post (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
  (m ro : word -> option byte) (rd ru : positive) : machine_state -> Prop :=
  fun ms' => exists sv u : word, ms' = MS (tset ru u (tset rd sv R)) F pc fc rv m ro.

(* [comment removed for export] *)
Ltac tree_val p R :=
  (* [comment removed for export] *)
  eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => (Z_to_bv 64 0 : word) end).

(* [comment removed for export] *)
Ltac instr_at segs pc :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w => let d := eval vm_compute in (decode_any w) in
               lazymatch d with Some (?i, _) => i | None => fail "undecodable instruction at" pc end
  | None => fail "no instruction at" pc
  end.

(* [comment removed for export] *)
Ltac sh_load SHB :=
  lazymatch type of SHB with shb ?m0 ?a ?v =>
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let i := instr_at segs pc in
    lazymatch i with
    | Load _ _ ?rd ?rs _ =>
        let p := eval vm_compute in (bv_key rs) in
        let vrs := tree_val p R in
        let SHR := fresh "SHR" in
        lazymatch vrs with
        | Z_to_bv 64 (Z.shiftr ?E 3 + 2147450880) =>
            pose proof (shb_load m0 a v E SHB ltac:(lia) ltac:(lia)) as SHR
        | Z_to_bv 64 (2147450880 + Z.shiftr ?E 3) =>
            pose proof (shb_load' m0 a v E SHB ltac:(lia) ltac:(lia)) as SHR
        | Z_to_bv 64 (?E / 8 + 2147450880) =>
            pose proof (shb_load_div m0 a v E SHB ltac:(lia) ltac:(lia)) as SHR
        | Z_to_bv 64 (2147450880 + ?E / 8) =>
            pose proof (shb_load_div' m0 a v E SHB ltac:(lia) ltac:(lia)) as SHR
        | _ =>
            first [ pose proof (shb_load_at m0 a v vrs SHB ltac:(assumption)) as SHR
                  | pose proof (shb_load_at m0 a v vrs SHB ltac:(symmetry; assumption)) as SHR
                  | pose proof (shb_load_at m0 a v vrs SHB ltac:(rewrite ?unsigned_lit by lia; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia)) as SHR
                  | fail 1 "sh_load: shadow-address register holds" vrs "- need [bv_unsigned _ = SH" a "]" ]
        end;
        step; try clear SHR
    | _ => fail "sh_load: not at a load:" i
    end
  end end.

(* [comment removed for export] *)
Ltac sh_cond_prep :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  fold_lit_ux;
  rewrite ?land7_mod by lia;
  rewrite ?signed_lit_small by (Z.div_mod_to_equations; lia);
  rewrite ?unsigned_lit by (Z.div_mod_to_equations; lia);
  (* [comment removed for export] *)
  rewrite ?Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 64) with 18446744073709551616%Z.
Ltac sh_dlia := Z.div_mod_to_equations; lia.
Ltac sh_solve_cond_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); sh_solve_cond_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); sh_solve_cond_rec
  | |- (?a <? ?b) = true => first [reflexivity | apply Z.ltb_lt; first [lia | sh_dlia]]
  | |- (?a <? ?b) = false => first [reflexivity | apply Z.ltb_ge; first [lia | sh_dlia]]
  | |- (?a <=? ?b) = true => first [reflexivity | apply Z.leb_le; first [lia | sh_dlia]]
  | |- (?a <=? ?b) = false => first [reflexivity | apply Z.leb_gt; first [lia | sh_dlia]]
  | |- (?a =? ?b) = true => first [reflexivity | apply Z.eqb_eq; first [lia | sh_dlia]]
  | |- (?a =? ?b) = false => first [reflexivity | apply Z.eqb_neq; first [lia | sh_dlia]]
  | _ => first [ reflexivity
               | apply Z.ltb_lt; sh_dlia | apply Z.ltb_ge; sh_dlia
               | apply Z.leb_le; sh_dlia | apply Z.leb_gt; sh_dlia
               | apply Z.eqb_eq; sh_dlia | apply Z.eqb_neq; sh_dlia ]
  end.
Ltac sh_solve_cond := sh_cond_prep; sh_solve_cond_rec.
Ltac sh_if_true :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; sh_solve_cond]
  end.
Ltac sh_if_false :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; sh_solve_cond]
  end.
Ltac sh_resolve_if := first [ sh_if_false | sh_if_true | fail 1 "asan check: cannot decide the branch (shadow fact too weak / address mismatch?)" ].

(* [comment removed for export] *)
Ltac sh_run_until segs OK :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) => idtac
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let i := instr_at segs pc in
      lazymatch i with
      | Jal ?rd _ => let r := eval vm_compute in (bv_unsigned rd) in
                     lazymatch r with
                     | 0%Z => step; sh_run_until segs OK
                     | _ => fail "asan check: reached the report call at" pc "(shadow fact too weak?)"
                     end
      | _ => zstep; sh_run_until segs OK
      end
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => sh_resolve_if; sh_run_until segs OK
  end.

Ltac sh_finish rdk ruk :=
  lazymatch goal with
  | |- evt ?segs (chk_post ?R ?F ?pc ?fc ?rv ?m ?ro _ _) (MS ?R2 _ _ _ _ _ _) =>
      let sv := tree_val rdk R2 in let u := tree_val ruk R2 in
      apply evt_done; exists sv, u; cbv beta iota delta [tset]; reflexivity
  end.

(* [comment removed for export] *)
Ltac sh_join v Cv rdk :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?T1 else Z_to_bv 64 ?T2) ?fc ?rv ?m ?ro) =>
    let okslow := lazymatch c with
                  | negb (bv_eqb _ _) => constr:((T2, T1))
                  | bv_eqb _ _ => constr:((T1, T2))
                  end in
    lazymatch okslow with
    | (?OK, ?SLOW) =>
      let i := instr_at segs SLOW in
      (* [comment removed for export] *)
      let i := lazymatch i with
               | Jal _ ?off => let tgt := eval vm_compute in (bv_unsigned (Z_to_bv 64 SLOW + sext 64 off : word)) in
                               instr_at segs tgt
               | _ => i end in
      let ruk := lazymatch i with
                 | OpImm ALU_AND ?ru _ _ => eval vm_compute in (bv_key ru)
                 | _ => rdk
                 end in
      apply (evt_cut segs (chk_post R F (Z_to_bv 64 OK) fc rv m ro rdk ruk) Q);
      [ lazymatch type of Cv with
        | _ \/ _ =>
          let Clo := fresh "Clo" in let Chi := fresh "Chi" in
          destruct Cv as [-> | [Clo Chi]];
          [ sh_run_until segs OK; sh_finish rdk ruk
          | rewrite ?(sxb_zb_small v), ?(zxb_zb_w v) by lia; sh_run_until segs OK; sh_finish rdk ruk ]
        | v = 0 => subst v; sh_run_until segs OK; sh_finish rdk ruk
        end
      | let ms1 := fresh "ms" in let sv := fresh "sv" in let u := fresh "u" in
        intros ms1 nelH_; (nelim nelH_ 3%nat; intros sv u ->); cbv beta iota delta [tset]; regs_fold_fix (* [comment removed for export] *); try clear Cv; try clear v ]
    end
  end.

(* [comment removed for export] *)
Ltac sh_to_branch segs :=
  do 2 (lazymatch goal with
        | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc2) _ _ _ _) =>
            let i2 := instr_at segs pc2 in
            lazymatch i2 with Branch _ _ _ _ => idtac | _ => step end
        | _ => idtac end).

(* [comment removed for export] *)
Ltac asan_chk H :=
  sh_now H;
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let i := instr_at segs pc in
    lazymatch i with
    | Load _ _ ?rd _ _ =>
      let rdk := eval vm_compute in (bv_key rd) in
      lazymatch type of H with
      | shchk _ ?a ?k =>
          let v := fresh "shv" in let SHB := fresh "SHB" in let Cv := fresh "Cv" in
          (nelim H 3%nat; intros v SHB Cv);
          sh_load SHB; sh_to_branch segs; step; sh_join v Cv rdk; try clear SHB
      | shb _ ?a 0 =>
          sh_load H; sh_to_branch segs; step; sh_resolve_if
      | shb _ ?a ?v =>
          fail "asan_chk: for a symbolic shadow value use a [shchk] fact (lemma shchk_of_...)"
      end
    | _ => fail "asan_chk: pc" pc "is not at a load"
    end
  end.

(* [comment removed for export] *)
Ltac asan_chk8 H := asan_chk H.


End CeilWrap.
(* [comment removed for export] *)
Ltac shbase_split SB :=
  let G1 := fresh "GOTSH" in let G2 := fresh "SHOFF" in
  destruct SB as [G1 G2].
Ltac uar_split SB :=
  let G1 := fresh "GOTUAR" in let G2 := fresh "UAROPT" in
  destruct SB as [G1 G2].
Ltac evt_mem :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => m end.
Ltac sh_transport_via MU H :=
  lazymatch type of H with
  | shb _ _ _ => apply (fun HH => shb_munch_disjoint _ _ _ _ _ HH MU) in H;
                 [| unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia ]
  | shchk _ _ _ => apply (fun HH => shchk_munch_disjoint _ _ _ _ _ HH MU) in H;
                 [| unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia ]
  | sh_zero _ _ _ => apply (fun HH => sh_zero_munch _ _ _ _ _ HH MU) in H;
                 [| unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia
                  | unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia
                  | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia ]
  | shadow_ok _ _ _ => apply (fun HH => shadow_ok_munch _ _ _ _ _ HH MU) in H;
                 [| lia
                  | unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia
                  | unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia
                  | cbn [disjoint_from]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia ]
  end.
Ltac sh_now H :=
  let m := evt_mem in
  lazymatch type of H with
  | ?P m _ _ => idtac
  | ?P ?m0 _ _ =>
      lazymatch goal with
      | MU : munch _ m0 m |- _ => sh_transport_via MU H
      | _ => fail "sh_now: no hypothesis [munch W" m0 m "] to transport" H
      end
  end.
Ltac addr_diff_ok k :=
  let t := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 16384))%Z in
  lazymatch t with true => idtac | false => fail end.
Ltac solve_load_base ::=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | 
                replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.
Ltac solve_store ::=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.
Ltac stepL_store_ok ::=
  lazymatch goal with
  | |- store_ok ?segs ?m ?a ?n = true /\ ?a = ?a' =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        addr_diff_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          split;
          [ apply (rw_cells_store_ok_at segs m A cs kn c0 n a H); first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]
          | unify a' (wa (A + Z.of_nat kn)%Z); addr_eq_tac ]
        end
    | HS : store_ok segs m ?a2 n = true |- _ =>
        split; [ first [ exact HS | rewrite <- HS; f_equal; word_eq_tac ] | first [ unify a' a2; first [reflexivity | word_eq_tac] | reflexivity ] ]
    end
  end.
Ltac tree_val p R :=
  (* [comment removed for export] *)
  eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => (Z_to_bv 64 0 : word) end).
Ltac instr_at segs pc :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w => let d := eval vm_compute in (decode_any w) in
               lazymatch d with Some (?i, _) => i | None => fail "undecodable instruction at" pc end
  | None => fail "no instruction at" pc
  end.
Ltac sh_load SHB :=
  lazymatch type of SHB with shb ?m0 ?a ?v =>
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let i := instr_at segs pc in
    lazymatch i with
    | Load _ _ ?rd ?rs _ =>
        let p := eval vm_compute in (bv_key rs) in
        let vrs := tree_val p R in
        let SHR := fresh "SHR" in
        lazymatch vrs with
        | Z_to_bv 64 (Z.shiftr ?E 3 + 2147450880) =>
            pose proof (shb_load m0 a v E SHB ltac:(lia) ltac:(lia)) as SHR
        | Z_to_bv 64 (2147450880 + Z.shiftr ?E 3) =>
            pose proof (shb_load' m0 a v E SHB ltac:(lia) ltac:(lia)) as SHR
        | Z_to_bv 64 (?E / 8 + 2147450880) =>
            pose proof (shb_load_div m0 a v E SHB ltac:(lia) ltac:(lia)) as SHR
        | Z_to_bv 64 (2147450880 + ?E / 8) =>
            pose proof (shb_load_div' m0 a v E SHB ltac:(lia) ltac:(lia)) as SHR
        | _ =>
            first [ pose proof (shb_load_at m0 a v vrs SHB ltac:(assumption)) as SHR
                  | pose proof (shb_load_at m0 a v vrs SHB ltac:(symmetry; assumption)) as SHR
                  | pose proof (shb_load_at m0 a v vrs SHB ltac:(rewrite ?unsigned_lit by lia; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia)) as SHR
                  | fail 1 "sh_load: shadow-address register holds" vrs "- need [bv_unsigned _ = SH" a "]" ]
        end;
        step; try clear SHR
    | _ => fail "sh_load: not at a load:" i
    end
  end end.
Ltac sh_cond_prep :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  fold_lit_ux;
  rewrite ?land7_mod by lia;
  rewrite ?signed_lit_small by (Z.div_mod_to_equations; lia);
  rewrite ?unsigned_lit by (Z.div_mod_to_equations; lia);
  
  rewrite ?Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 64) with 18446744073709551616%Z.
Ltac sh_dlia := Z.div_mod_to_equations; lia.
Ltac sh_solve_cond_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); sh_solve_cond_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); sh_solve_cond_rec
  | |- (?a <? ?b) = true => first [reflexivity | apply Z.ltb_lt; first [lia | sh_dlia]]
  | |- (?a <? ?b) = false => first [reflexivity | apply Z.ltb_ge; first [lia | sh_dlia]]
  | |- (?a <=? ?b) = true => first [reflexivity | apply Z.leb_le; first [lia | sh_dlia]]
  | |- (?a <=? ?b) = false => first [reflexivity | apply Z.leb_gt; first [lia | sh_dlia]]
  | |- (?a =? ?b) = true => first [reflexivity | apply Z.eqb_eq; first [lia | sh_dlia]]
  | |- (?a =? ?b) = false => first [reflexivity | apply Z.eqb_neq; first [lia | sh_dlia]]
  | _ => first [ reflexivity
               | apply Z.ltb_lt; sh_dlia | apply Z.ltb_ge; sh_dlia
               | apply Z.leb_le; sh_dlia | apply Z.leb_gt; sh_dlia
               | apply Z.eqb_eq; sh_dlia | apply Z.eqb_neq; sh_dlia ]
  end.
Ltac sh_solve_cond := sh_cond_prep; sh_solve_cond_rec.
Ltac sh_if_true :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; sh_solve_cond]
  end.
Ltac sh_if_false :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; sh_solve_cond]
  end.
Ltac sh_resolve_if := first [ sh_if_false | sh_if_true | fail 1 "asan check: cannot decide the branch (shadow fact too weak / address mismatch?)" ].
Ltac sh_run_until segs OK :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) => idtac
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let i := instr_at segs pc in
      lazymatch i with
      | Jal ?rd _ => let r := eval vm_compute in (bv_unsigned rd) in
                     lazymatch r with
                     | 0%Z => step; sh_run_until segs OK
                     | _ => fail "asan check: reached the report call at" pc "(shadow fact too weak?)"
                     end
      | _ => zstep; sh_run_until segs OK
      end
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => sh_resolve_if; sh_run_until segs OK
  end.
Ltac sh_finish rdk ruk :=
  lazymatch goal with
  | |- evt ?segs (chk_post ?R ?F ?pc ?fc ?rv ?m ?ro _ _) (MS ?R2 _ _ _ _ _ _) =>
      let sv := tree_val rdk R2 in let u := tree_val ruk R2 in
      apply evt_done; exists sv, u; cbv beta iota delta [tset]; reflexivity
  end.
Ltac sh_join v Cv rdk :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?T1 else Z_to_bv 64 ?T2) ?fc ?rv ?m ?ro) =>
    let okslow := lazymatch c with
                  | negb (bv_eqb _ _) => constr:((T2, T1))
                  | bv_eqb _ _ => constr:((T1, T2))
                  end in
    lazymatch okslow with
    | (?OK, ?SLOW) =>
      let i := instr_at segs SLOW in
      
      let i := lazymatch i with
               | Jal _ ?off => let tgt := eval vm_compute in (bv_unsigned (Z_to_bv 64 SLOW + sext 64 off : word)) in
                               instr_at segs tgt
               | _ => i end in
      let ruk := lazymatch i with
                 | OpImm ALU_AND ?ru _ _ => eval vm_compute in (bv_key ru)
                 | _ => rdk
                 end in
      apply (evt_cut segs (chk_post R F (Z_to_bv 64 OK) fc rv m ro rdk ruk) Q);
      [ lazymatch type of Cv with
        | _ \/ _ =>
          let Clo := fresh "Clo" in let Chi := fresh "Chi" in
          destruct Cv as [-> | [Clo Chi]];
          [ sh_run_until segs OK; sh_finish rdk ruk
          | rewrite ?(sxb_zb_small v), ?(zxb_zb_w v) by lia; sh_run_until segs OK; sh_finish rdk ruk ]
        | v = 0 => subst v; sh_run_until segs OK; sh_finish rdk ruk
        end
      | let ms1 := fresh "ms" in let sv := fresh "sv" in let u := fresh "u" in
        intros ms1 nelH_; (nelim nelH_ 3%nat; intros sv u ->); cbv beta iota delta [tset]; regs_fold_fix (* [comment removed for export] *); try clear Cv; try clear v ]
    end
  end.
Ltac sh_to_branch segs :=
  do 2 (lazymatch goal with
        | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc2) _ _ _ _) =>
            let i2 := instr_at segs pc2 in
            lazymatch i2 with Branch _ _ _ _ => idtac | _ => step end
        | _ => idtac end).
Ltac asan_chk H :=
  sh_now H;
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let i := instr_at segs pc in
    lazymatch i with
    | Load _ _ ?rd _ _ =>
      let rdk := eval vm_compute in (bv_key rd) in
      lazymatch type of H with
      | shchk _ ?a ?k =>
          let v := fresh "shv" in let SHB := fresh "SHB" in let Cv := fresh "Cv" in
          (nelim H 3%nat; intros v SHB Cv);
          sh_load SHB; sh_to_branch segs; step; sh_join v Cv rdk; try clear SHB
      | shb _ ?a 0 =>
          sh_load H; sh_to_branch segs; step; sh_resolve_if
      | shb _ ?a ?v =>
          fail "asan_chk: for a symbolic shadow value use a [shchk] fact (lemma shchk_of_...)"
      end
    | _ => fail "asan_chk: pc" pc "is not at a load"
    end
  end.
Ltac asan_chk8 H := asan_chk H.
