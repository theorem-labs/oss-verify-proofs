(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
Module RT_shlem.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rt_SH_mono : forall a b, a <= b -> SH a <= SH b.
Proof. intros a b H. unfold SH. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.
Lemma rt_SH_aligned_add : forall A i, A mod 8 = 0 -> SH (A + i) = SH A + i / 8.
Proof. intros A i HA. unfold SH. Z.div_mod_to_equations. lia. Qed.
Lemma rt_SH_lt_of : forall a b, a / 8 < b / 8 -> SH a < SH b.
Proof. intros a b H. unfold SH. lia. Qed.
Lemma rt_SH_bounds : forall a, 0 <= a < 2^47 -> 2147450880 <= SH a < 0x10007fff8000.
Proof. intros a H. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. Qed.

Lemma rt_noseg_high : forall x : word, AIMG_HI <= bv_unsigned x -> noseg asegs x.
Proof.
  intros x Hx s Hs. unfold AIMG_HI in Hx. cbn in Hs.
  destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia.
Qed.
Lemma rt_rom_shadow : forall a, 0 <= a < 2^47 -> seg_rom asegs (wa (SH a)) = None.
Proof.
  intros a Ha. apply seg_rom_noseg. apply rt_noseg_high.
  pose proof (rt_SH_bounds a Ha). unfold AIMG_HI. rewrite wa_unsigned; lia.
Qed.
Lemma rt_mrd_shadow : forall m a b, 0 <= a < 2^47 -> mrd asegs m (wa (SH a)) = Some b -> m (wa (SH a)) = Some b.
Proof.
  intros m a b Ha H. unfold mrd in H. destruct (m (wa (SH a))) as [b'|] eqn:E; [congruence|].
  rewrite rt_rom_shadow in H by exact Ha. discriminate.
Qed.

Lemma rt_shcells_length : forall vs, length (shcells vs) = length vs.
Proof. intros vs. unfold shcells. apply length_map. Qed.
Lemma rt_shcells_wf : forall vs, cells_wf (shcells vs).
Proof. unfold shcells. induction vs as [|v vs IH]; cbn; [exact I|]. split; [exact I| exact IH]. Qed.
Lemma rt_shcells_bytes : forall vs, cells_bytes (shcells vs) = map zb vs.
Proof. unfold shcells. induction vs as [|v vs IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma rt_shcells_size : forall vs, cells_size (shcells vs) = length vs.
Proof. unfold shcells. induction vs as [|v vs IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rt_sh_bytes_shb : forall m g8 vs i v a,
  cells_at asegs m (SH g8) (shcells vs) -> g8 mod 8 = 0 -> nth_error vs i = Some v ->
  g8 + 8 * Z.of_nat i <= a < g8 + 8 * Z.of_nat i + 8 -> 0 <= a < 2^47 ->
  shb m a v.
Proof.
  intros m g8 vs i v a [Hwf HB] Hal Hn Ha Ha47.
  rewrite rt_shcells_bytes in HB. destruct HB as (H0 & H1 & HB).
  assert (Hi : (i < length vs)%nat).
  { destruct (Nat.lt_ge_cases i (length vs)) as [Hlt|Hge]; [exact Hlt|].
    apply (proj2 (nth_error_None vs i)) in Hge. congruence. }
  specialize (HB i ltac:(rewrite length_map; exact Hi)).
  rewrite (map_nth_error zb i vs Hn) in HB.
  assert (E : SH g8 + Z.of_nat i = SH a) by (unfold SH; Z.div_mod_to_equations; lia).
  rewrite E in HB. unfold shb. apply rt_mrd_shadow; [exact Ha47| exact HB].
Qed.

Lemma rt_shadow_enc_length : forall n, 0 <= n -> Z.of_nat (length (shadow_enc n)) = (n + 7) / 8.
Proof.
  intros n Hn. unfold shadow_enc. rewrite length_app, repeat_length.
  destruct (Z.eqb_spec (n mod 8) 0); cbn [length]; Z.div_mod_to_equations; lia.
Qed.
Lemma rt_shadow_enc_nth_zero : forall n i, 0 <= n -> (Z.of_nat i < n / 8) -> nth_error (shadow_enc n) i = Some 0.
Proof.
  intros n i Hn Hi. unfold shadow_enc. rewrite nth_error_app1 by (rewrite repeat_length; lia).
  apply nth_error_repeat. lia.
Qed.
Lemma rt_shadow_enc_nth_last : forall n, 0 <= n -> n mod 8 <> 0 ->
  nth_error (shadow_enc n) (Z.to_nat (n / 8)) = Some (n mod 8).
Proof.
  intros n Hn Hm. unfold shadow_enc. rewrite nth_error_app2 by (rewrite repeat_length; lia).
  rewrite repeat_length, Nat.sub_diag. destruct (Z.eqb_spec (n mod 8) 0); [lia| reflexivity].
Qed.
Lemma rt_shadow_enc_shb : forall m A n a,
  cells_at asegs m (SH A) (shcells (shadow_enc n)) -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 -> A <= a < A + n ->
  shb m a (if (a - A) / 8 <? n / 8 then 0 else n mod 8).
Proof.
  intros m A n a H Hal HA Hn Ha.
  destruct (Z.ltb_spec ((a - A) / 8) (n / 8)) as [L|L].
  - eapply (rt_sh_bytes_shb m A (shadow_enc n) (Z.to_nat ((a - A) / 8)) 0 a H Hal).
    + apply rt_shadow_enc_nth_zero; [lia|]. Z.div_mod_to_equations. lia.
    + Z.div_mod_to_equations. lia.
    + lia.
  - assert (Hm : n mod 8 <> 0) by (Z.div_mod_to_equations; lia).
    assert (E : (a - A) / 8 = n / 8) by (Z.div_mod_to_equations; lia).
    eapply (rt_sh_bytes_shb m A (shadow_enc n) (Z.to_nat (n / 8)) (n mod 8) a H Hal).
    + apply rt_shadow_enc_nth_last; lia.
    + Z.div_mod_to_equations. lia.
    + lia.
Qed.
(* [comment removed for export] *)
Lemma rt_shadow_enc_addressable : forall m A n i,
  cells_at asegs m (SH A) (shcells (shadow_enc n)) -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 -> 0 <= i < n ->
  exists v, shb m (A + i) v /\ (v = 0 \/ ((A + i) mod 8 < v /\ v < 8)).
Proof.
  intros m A n i H Hal HA Hn Hi.
  pose proof (rt_shadow_enc_shb m A n (A + i) H Hal HA Hn ltac:(lia)) as SB.
  eexists. split; [exact SB|].
  destruct (Z.ltb_spec ((A + i - A) / 8) (n / 8)); [left; reflexivity| right].
  Z.div_mod_to_equations. lia.
Qed.


End CeilWrap.
End RT_shlem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_iface.
Import RT_shlem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cells_at_app : forall m A cs1 cs2,
  cells_at asegs m A (cs1 ++ cs2) <-> cells_at asegs m A cs1 /\ cells_at asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold cells_at. rewrite cells_wf_app, cells_bytes_app, bytes_at_app. split.
  - intros [[W1 W2] [B1 B2]]. rewrite cells_bytes_length in B2 by exact W1. tauto.
  - intros [[W1 B1] [W2 B2]]. rewrite cells_bytes_length by exact W1. tauto.
Qed.

Lemma wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at asegs m A (n1 + n2) <-> wr_at asegs m A n1 /\ wr_at asegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). repeat split; try lia; intros i Hi; [apply H; lia|].
    replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hl & HA) & (Hb & Hl2 & HB)). split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i n1); [apply HA; lia|]. replace (A + i) with (A + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells asegs m A (cs1 ++ cs2) <-> rw_cells asegs m A cs1 /\ rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells. rewrite cells_at_app, cells_size_app, Nat2Z.inj_add, wr_at_app by lia. tauto.
Qed.

Lemma rw_cells_cells : forall m A cs, rw_cells asegs m A cs -> cells_at asegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

(* [comment removed for export] *)
Lemma rw_cells_take : forall m A cs1 cs2, rw_cells asegs m A (cs1 ++ cs2) -> rw_cells asegs m A cs1.
Proof. intros m A cs1 cs2 H. apply rw_cells_app in H. tauto. Qed.
Lemma rw_cells_drop : forall m A cs1 cs2, rw_cells asegs m A (cs1 ++ cs2) -> rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. intros m A cs1 cs2 H. apply rw_cells_app in H. tauto. Qed.
Lemma rw_cells_mid : forall m A cs1 cs2 cs3, rw_cells asegs m A (cs1 ++ cs2 ++ cs3) ->
  rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. intros m A cs1 cs2 cs3 H. apply rw_cells_drop in H. apply rw_cells_take in H. exact H. Qed.

(* [comment removed for export] *)
Lemma zcells_app : forall a b, shcells (a ++ b) = shcells a ++ shcells b.
Proof. intros. unfold shcells. apply map_app. Qed.
Lemma zrep_length : forall v k, 0 <= k -> Z.of_nat (length (zrep v k)) = k.
Proof. intros. unfold zrep. rewrite repeat_length. lia. Qed.
Lemma shcells_size_Z : forall vs, Z.of_nat (cells_size (shcells vs)) = Z.of_nat (length vs).
Proof. intros. rewrite rt_shcells_size. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma asegs_val : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) asegs
  = [(0x10000, 0x20000, false); (0x30000, 0x71000, false); (0xa1000, 0x2000, true); (0xa3000, 0x55c000, true)].
Proof. vm_compute. reflexivity. Qed.

Lemma asegs_In : forall s, In s asegs ->
  (Z.of_N (seg_base s) = 0x10000 /\ Z.of_N (seg_size s) = 0x20000 /\ seg_writable s = false)
  \/ (Z.of_N (seg_base s) = 0x30000 /\ Z.of_N (seg_size s) = 0x71000 /\ seg_writable s = false)
  \/ (Z.of_N (seg_base s) = 0xa1000 /\ Z.of_N (seg_size s) = 0x2000 /\ seg_writable s = true)
  \/ (Z.of_N (seg_base s) = 0xa3000 /\ Z.of_N (seg_size s) = 0x55c000 /\ seg_writable s = true).
Proof.
  intros s Hs. pose proof asegs_val as E.
  destruct asegs as [|s1 [|s2 [|s3 [|s4 [|s5 l]]]]]; try discriminate. cbn in E. injection E as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12.
  destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; [left|right;left|right;right;left|right;right;right]; auto.
Qed.

(* [comment removed for export] *)
Lemma noseg_high : forall x : word, AIMG_HI <= bv_unsigned x -> noseg asegs x.
Proof. exact rt_noseg_high. Qed.

Lemma noseg_Z : forall a, AIMG_HI <= a < 2^64 -> noseg asegs (wa a).
Proof. intros a Ha. apply noseg_high. rewrite wa_unsigned by (unfold AIMG_HI in *; lia). lia. Qed.

(* [comment removed for export] *)
Lemma wview_noseg_some : forall m (x : word), noseg asegs x -> wview asegs m x <> None -> m x <> None.
Proof.
  intros m x Hx Hw Hm. apply Hw. unfold wview. rewrite Hm. rewrite (find_segment_noseg asegs x 1 Hx ltac:(lia)). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stk_wmono_noseg : forall m m' lo hi,
  stk asegs m lo hi -> wmono asegs m m' -> AIMG_HI <= lo -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) HW Hlo. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as [Hw [b Hb]]. pose proof (HW _ Hw) as Hw'. split; [exact Hw'|].
  assert (NS : noseg asegs (wa a)) by (apply noseg_Z; lia).
  pose proof (wview_noseg_some m' (wa a) NS Hw') as Hs. unfold mrd. destruct (m' (wa a)) as [b'|]; [eexists; reflexivity| congruence].
Qed.

Lemma stk_sub : forall m lo hi lo' hi', stk asegs m lo hi -> lo <= lo' -> hi' <= hi -> stk asegs m lo' hi'.
Proof. intros m lo hi lo' hi' (H1 & H2 & H) Ha Hb. split; [lia|]. split; [lia|]. intros a Hr. apply H. lia. Qed.

Lemma stk_wr_at : forall m lo hi a n, stk asegs m lo hi -> lo <= a -> a + n <= hi -> wr_at asegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hn. split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma stk_some : forall m lo hi a, stk asegs m lo hi -> lo <= a < hi -> AIMG_HI <= lo -> m (wa a) <> None.
Proof.
  intros m lo hi a (H1 & H2 & H) Ha Hlo. destruct (H a Ha) as [Hw _]. apply wview_noseg_some; [apply noseg_Z; lia| exact Hw].
Qed.

(* [comment removed for export] *)
Lemma stk_of_rw_cellsZ : forall m A cs n, rw_cells asegs m A cs -> Z.of_nat (cells_size cs) = n -> stk asegs m A (A + n).
Proof. intros m A cs n H <-. apply stk_of_rw_cells. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rt_bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma rt_Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (rt_bytes_le_to_Z_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.

Lemma rt_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (rt_bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply rt_Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Lemma c8_of_bytes : forall m A,
  0 <= A -> A + 8 <= 2^64 ->
  (forall i, 0 <= i < 8 -> wview asegs m (wa (A + i)) <> None /\ exists b, mrd asegs m (wa (A + i)) = Some b) ->
  exists v : word, rw_cells asegs m A [C8 v].
Proof.
  intros m A HA HB H.
  assert (G : forall k, (k <= 8)%nat -> exists bs, length bs = k /\ forall i, (i < k)%nat -> mrd asegs m (wa (A + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs). destruct (H (Z.of_nat k) ltac:(lia)) as [_ (b & Hb)].
      exists (bs ++ [b]). split. { rewrite length_app; cbn; lia. }
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G 8%nat ltac:(lia)) as (bs & Hlen & Hbs).
  exists (le_bytes_to_word bs). split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r, rt_le8_of_bytes by exact Hlen.
    split; [lia|]. rewrite Hlen. split; [cbn; lia|]. intros i Hi. apply Hbs. exact Hi.
  - cbn [cells_size csize]. split; [lia|]. split; [cbn; lia|]. intros i Hi. apply (proj1 (H i ltac:(cbn in Hi; lia))).
Qed.

(* [comment removed for export] *)
Definition gerror_ssp_addrs : list Z :=
  map (fun i => AGERROR0 + Z.of_nat i) (seq 0 8) ++ map (fun i => AGERROR1 + Z.of_nat i) (seq 0 8)
  ++ map (fun i => ASSP + Z.of_nat i) (seq 0 8).

Lemma wview_empty : forall m (x : word),
  wview asegs m x = match m x with Some b => Some b | None => wview asegs (fun _ => None) x end.
Proof. intros m x. unfold wview. destruct (m x); reflexivity. Qed.

Lemma gerror_ssp_image :
  forallb (fun a => match seg_rom asegs (wa a), wview asegs (fun _ => None) (wa a) with
                    | Some _, Some _ => true | _, _ => false end) gerror_ssp_addrs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma In_gerror_ssp_addrs : forall a,
  (AGERROR0 <= a < AGERROR0 + 8 \/ AGERROR1 <= a < AGERROR1 + 8 \/ ASSP <= a < ASSP + 8) -> In a gerror_ssp_addrs.
Proof.
  intros a Ha. unfold gerror_ssp_addrs. rewrite !in_app_iff, !in_map_iff.
  destruct Ha as [H|[H|H]]; [left| right; left| right; right];
    [exists (Z.to_nat (a - AGERROR0))| exists (Z.to_nat (a - AGERROR1))| exists (Z.to_nat (a - ASSP))];
    (split; [lia| apply in_seq; lia]).
Qed.

Lemma gerror_ssp_bytes : forall m a,
  (AGERROR0 <= a < AGERROR0 + 8 \/ AGERROR1 <= a < AGERROR1 + 8 \/ ASSP <= a < ASSP + 8) ->
  wview asegs m (wa a) <> None /\ exists b, mrd asegs m (wa a) = Some b.
Proof.
  intros m a Ha. pose proof gerror_ssp_image as F. rewrite forallb_forall in F.
  specialize (F a (In_gerror_ssp_addrs a Ha)). cbn beta in F.
  destruct (seg_rom asegs (wa a)) as [r|] eqn:ER; [|discriminate].
  destruct (wview asegs (fun _ => None) (wa a)) as [w|] eqn:EW; [|discriminate].
  split.
  - rewrite wview_empty. destruct (m (wa a)); [discriminate|]. rewrite EW. discriminate.
  - unfold mrd. destruct (m (wa a)) as [b|]; [exists b; reflexivity|]. rewrite ER. eexists; reflexivity.
Qed.

Lemma gerror0_cell : forall m, exists v : word, rw_cells asegs m AGERROR0 [C8 v].
Proof. intros m. apply c8_of_bytes; [unfold AGERROR0; lia| unfold AGERROR0; lia|]. intros i Hi. apply gerror_ssp_bytes. left. lia. Qed.
Lemma gerror1_cell : forall m, exists v : word, rw_cells asegs m AGERROR1 [C8 v].
Proof. intros m. apply c8_of_bytes; [unfold AGERROR1; lia| unfold AGERROR1; lia|]. intros i Hi. apply gerror_ssp_bytes. right; left. lia. Qed.
Lemma ssp_cell : forall m, exists v : word, rw_cells asegs m ASSP [C8 v].
Proof. intros m. apply c8_of_bytes; [unfold ASSP; lia| unfold ASSP; lia|]. intros i Hi. apply gerror_ssp_bytes. right; right. lia. Qed.


End CeilWrap.
