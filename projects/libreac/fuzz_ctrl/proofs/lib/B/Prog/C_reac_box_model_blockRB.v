(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_ctrl_classify_box_frameLib.v, with its module paths and module names changed; 805 of its 936 lines of code are new or changed and 858 lines of the source are left out. *)
(* GENERATED - do not edit.  C_reac_box_model_blockRB.v is the re-based copy of lib/B/Prog/reac_box_model_block.v at 20372bbcc3a
   (source sha256 13776076e131201f48cef61f548252511d37e8ca260bde60ad0ff58253bfdc20) by gen_rb_modelblock.py
   (its sha256 is cited in the commit that adds this file); the substitutions are listed there.  Dropped here: fwords, entry, td_tail, epi0. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Export asan_stack_malloc_cF asan_stack_malloc_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import sh_word_on asan_stack_malloc_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c_on reac_box_model_block_cF_on.
Import ListNotations.
Open Scope Z_scope.

(* reac_box_model_block, image B (asan-ubsan, entry 0x865d8): reac_box_model_block_holds from the contracts of
   __asan_stack_malloc_0, __asan_memset, __asan_memcpy, build_dt1_single, dt1_head and name_field. The plain proof
   (lib/U/Prog/C_reac_box_model_blockRB.v) with the ASan frame of this build: the class-0 frame request, the frame words
   and their shadow, the shadow check before each instrumented load and store (each passes from the addressable-range
   premises, so __asan_report_* is not reached), and the frame exit. This build saves ra, s0..s9 (11 words). *)


(* Every byte readable in m is readable in m'. *)
Definition rd_mono (m m' : word -> option byte) : Prop :=
  forall x : word, (exists b, mrd rsegs m x = Some b) -> exists b, mrd rsegs m' x = Some b.

Lemma rd_mono_refl : forall m, rd_mono m m.
Proof. intros m x H. exact H. Qed.

Lemma rd_mono_trans : forall m1 m2 m3, rd_mono m1 m2 -> rd_mono m2 m3 -> rd_mono m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.

Lemma wtm_cases : forall bs m (a x : word), write_to_mem m a bs x = m x \/ exists v, write_to_mem m a bs x = Some v.
Proof.
  induction bs as [|b bs IH]; intros m a x; cbn [write_to_mem]; [left; reflexivity|].
  destruct (IH (fun y => if bv_eqb y a then Some b else m y) (a + 1)%bv x) as [E|E]; [|right; exact E].
  rewrite E. destruct (bv_eqb x a); [right; eexists; reflexivity | left; reflexivity].
Qed.

Lemma rd_mono_write : forall m0 m a bs, rd_mono m0 m -> rd_mono m0 (write_to_mem m a bs).
Proof.
  intros m0 m a bs H x Hx. destruct (H x Hx) as [v Hv]. unfold mrd in *.
  destruct (wtm_cases bs m a x) as [E|[w E]]; rewrite E; [exists v; exact Hv | exists w; reflexivity].
Qed.

Lemma rd_mono_munch : forall W m m', munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> exists b, mrd rsegs m' x = Some b) -> rd_mono m m'.
Proof.
  intros W m m' Hm H x Hx. destruct (rc_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - unfold mrd in *. rewrite (Hm x Ho). exact Hx.
  - exact (H x Ho).
Qed.

Lemma stk_mono : forall m m' lo hi, stk rsegs m lo hi -> wmono rsegs m m' -> rd_mono m m' -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) Hw Hr. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Lemma shadow_rw_mono : forall m m', shadow_rw m -> wmono rsegs m m' -> rd_mono m m' -> shadow_rw m'.
Proof.
  intros m m' H Hw Hr a Ha. destruct (H a Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

(* route (C): the region form of shadow_rw_mono. *)
Lemma shadow_rw_on_mono_mem : forall (P : Z -> Prop) m m', shadow_rw_on P m -> wmono rsegs m m' -> rd_mono m m' ->
  shadow_rw_on P m'.
Proof. intros P m m' H Hw Hr a Hp Ha. destruct (H a Hp Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb]. Qed.

Lemma fs_place_mono : forall m m' FS, fs_place m FS -> wmono rsegs m m' -> rd_mono m m' -> fs_place m' FS.
Proof.
  intros m m' FS (P1 & P2 & P3 & P4 & P5) Hw Hr. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split; [exact P4|]. exact (stk_mono m m' _ _ P5 Hw Hr).
Qed.

Lemma wv_store_ok : forall m m' a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> wview rsegs m (wa (a + i)) <> None) -> wmono rsegs m m' ->
  0 <= a -> a + Z.of_nat n <= 2^64 -> store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' a n H Hw Ha Hn.
  assert (WR : wr_at rsegs m' a (Z.of_nat n)) by (split; [lia|]; split; [lia|]; intros i Hi; apply Hw, H, Hi).
  pose proof (wr_at_store_ok rsegs m' a (Z.of_nat n) 0 n WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

Lemma stk_wv : forall m lo hi a, stk rsegs m lo hi -> lo <= a < hi -> wview rsegs m (wa a) <> None.
Proof. intros m lo hi a (_ & _ & H) Ha. exact (proj1 (H a Ha)). Qed.

Lemma addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hi.
Qed.

Lemma bytes_keep : forall m m' A bs, bytes_at rsegs m A bs ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> mrd rsegs m' (wa x) = mrd rsegs m (wa x)) -> bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (Ha & Hl & H) Hk. split; [lia|]. split; [lia|]. intros i Hi. rewrite Hk by lia. apply H, Hi.
Qed.

Lemma addr_keep : forall m m' p n, addressable m p n ->
  (forall i, 0 <= i < n -> mrd rsegs m' (wa (shadow_addr (p + i))) = mrd rsegs m (wa (shadow_addr (p + i)))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & Hn & He & HA) Hk. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. rewrite Hk by exact Hi.
  split; [exact Hb | exact Hok].
Qed.

Lemma app_not_shadow : forall x y, app_mem x -> in_shadow y -> x <> y.
Proof.
  unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros; lia.
Qed.

Lemma sh_range : forall L H x, L mod 8 = 0 -> H mod 8 = 0 ->
  (shadow_addr L <= shadow_addr x < shadow_addr H <-> L <= x < H).
Proof. intros L H x HL HH. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma sh_range8 : forall fr x, fr mod 8 = 0 ->
  (shadow_addr fr <= shadow_addr x < shadow_addr fr + 8 <-> fr <= x < fr + 64).
Proof. intros fr x Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma sh_add8 : forall fr i, fr mod 8 = 0 -> shadow_addr (fr + 8 * i) = shadow_addr fr + i.
Proof. intros fr i Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x / 32 * 32.
Proof.
  intros x Hx.
  replace 18446744073709551584 with (Z.land (Z.lnot (Z.ones 5)) (Z.ones 64)) by reflexivity.
  rewrite Z.land_assoc, (Z.land_comm x), <- Z.land_assoc, (Z.land_ones x 64) by lia.
  rewrite Z.mod_small by lia. rewrite Z.land_comm, <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma bytes_le_to_Z_nonneg' : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma bytes_le_to_Z_cons' : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg' bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  assert (D : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 256) = 0).
  { apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma Z_to_le_bytes_to_Z' : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons'.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg' bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.

Lemma rd8_le8 : forall m a, 0 <= a -> a + 8 <= 2^64 ->
  (forall i, 0 <= i < 8 -> exists b, mrd rsegs m (wa (a + i)) = Some b) -> exists w, bytes_at rsegs m a (le8 w).
Proof.
  intros m a Ha Hl H.
  destruct (H 0 ltac:(lia)) as [b0 E0]. destruct (H 1 ltac:(lia)) as [b1 E1].
  destruct (H 2 ltac:(lia)) as [b2 E2]. destruct (H 3 ltac:(lia)) as [b3 E3].
  destruct (H 4 ltac:(lia)) as [b4 E4]. destruct (H 5 ltac:(lia)) as [b5 E5].
  destruct (H 6 ltac:(lia)) as [b6 E6]. destruct (H 7 ltac:(lia)) as [b7 E7].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (EL : le8 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])) = [b0; b1; b2; b3; b4; b5; b6; b7]).
  { rewrite <- store_bytes_8. cbn [width_bytes]. rewrite unsigned_lit_wrap.
    rewrite Z_to_le_bytes_mod by (cbn; lia).
    exact (Z_to_le_bytes_to_Z' [b0; b1; b2; b3; b4; b5; b6; b7]). }
  rewrite EL. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error]; simpl Z.of_nat;
    [rewrite Z.add_0_r in E0; replace (a + Z.of_nat 0) with a by lia; exact E0
    | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | lia].
Qed.

Lemma rd_of_bytes : forall m A bs, bytes_at rsegs m A bs ->
  forall y, A <= y < A + Z.of_nat (length bs) -> exists b, mrd rsegs m (wa y) = Some b.
Proof.
  intros m A bs (Ha & Hl & H) y Hy. pose proof (H (Z.to_nat (y - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (y - A))) with y in E by lia.
  destruct (nth_error bs (Z.to_nat (y - A))) as [v|] eqn:En; [exists v; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma rd_of_stk : forall m lo hi, stk rsegs m lo hi -> forall y, lo <= y < hi -> exists b, mrd rsegs m (wa y) = Some b.
Proof. intros m lo hi (_ & _ & H) y Hy. exact (proj2 (H y Hy)). Qed.

Lemma not_outside_in : forall W x, ~ outside W x -> exists r, In r W /\ fst r <= x < snd r.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn in H; [exfalso; exact (H I)|].
  destruct (Z.le_gt_cases lo x); destruct (Z.lt_ge_cases x hi).
  - exists (lo, hi). split; [left; reflexivity | cbn; lia].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
Qed.

Lemma rd_mono_list : forall W m m', munch W m m' ->
  Forall (fun r => forall y, fst r <= y < snd r -> exists b, mrd rsegs m' (wa y) = Some b) W -> rd_mono m m'.
Proof.
  intros W m m' Hm HF. apply (rd_mono_munch W m m' Hm). intros x Hx.
  destruct (not_outside_in W _ Hx) as (r & Hr & Hin). rewrite Forall_forall in HF.
  pose proof (HF r Hr (bv_unsigned x) Hin) as R. unfold wa in R. rewrite Z_to_bv_lit_self in R. exact R.
Qed.


Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Lemma bytes_ro : forall m A c, bytes_at rsegs m A (cbytes c) -> cell_wf c -> ro_cells rsegs m A [c].
Proof. intros m A c H Hw. split; [split; [exact Hw | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact H]. Qed.
Lemma bytes_ro8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. exact (bytes_ro m A (C8 v) H I). Qed.
Lemma bytes_ro4 : forall m A v, bytes_at rsegs m A (le4 v) -> ro_cells rsegs m A [C4 v].
Proof. intros m A v H. exact (bytes_ro m A (C4 v) H I). Qed.

(* --- generic ASan shadow-check infrastructure (as in reac_ctrl_classify_box_frame.v) --- *)
Lemma acl_app_in : forall m p n i, addressable m p n -> 0 <= i < n -> app_mem (p + i).
Proof. intros m p n i (_ & _ & _ & HA) Hi. exact (proj1 (HA i Hi)). Qed.

Lemma acl_app_not_shadow : forall x, app_mem x -> in_shadow x -> False.
Proof. unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros; lia. Qed.

Lemma acl_addr_sub : forall m p n p' n', addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma acl_addr_join : forall m p n n', addressable m p n -> addressable m (p + n) n' -> 0 <= n' ->
  addressable m p (n + n').
Proof.
  intros m p n n' (H0 & Hn & He & HA) (H0' & Hn' & He' & HA') Hn''. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.lt_ge_cases i n) as [L|L]; [apply HA; lia|].
  replace (p + i) with (p + n + (i - n)) by lia. apply HA'. lia.
Qed.

Lemma acl_shadow : forall mc p n j w X, addressable mc p n -> 0 <= j -> 1 <= w -> j + w <= n ->
  X mod 8 + w <= 8 -> X = p + j ->
  exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + ASAN_K)) 1 = Some [k]
                   /\ (bv_signed k = 0 \/ X mod 8 + (w - 1) < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros mc p n j w X HA Hj Hw Hjw Hm ->.
  pose proof (rt_shadow_rd mc p n [] HA (fun _ _ => I)) as HSR.
  pose proof (rt_addressable mc p n HA) as HAD.
  destruct (asan_shadow_read rsegs mc ASAN_K p n [] j HSR ltac:(lia)) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [|apply rc_byte_signed].
  exact (asan_check_lt rsegs mc ASAN_K p n j w k HAD Hj Hw Hjw Hm BK).
Qed.

Lemma acl_sh_lt : forall x L, L mod 8 = 0 -> x < L -> shadow_addr x < shadow_addr L.
Proof. unfold shadow_addr. intros x L HL Hx. Z.div_mod_to_equations. lia. Qed.
Lemma acl_sh_ge : forall x L, L <= x -> shadow_addr L <= shadow_addr x.
Proof. unfold shadow_addr. intros x L H. pose proof (Z.div_le_mono L x 8 ltac:(lia) H). lia. Qed.

Lemma acl_win_sh : forall x lo hi, lo mod 8 = 0 -> ~ (lo <= x < hi) ->
  ~ (shadow_addr lo <= shadow_addr x < shadow_addr hi).
Proof.
  intros x lo hi Hm Hx [H1 H2]. destruct (Z_lt_le_dec x lo) as [L|L].
  - pose proof (acl_sh_lt x lo Hm L). lia.
  - pose proof (acl_sh_ge x hi ltac:(lia)). lia.
Qed.

Lemma acl_sh_out : forall x a b, app_mem x -> 0 <= a -> b <= APPMEM_END -> ~ (shadow_addr a <= x < shadow_addr b).
Proof.
  intros x a b Hx Ha Hb. unfold shadow_addr.
  pose proof (Z.div_pos a 8 Ha ltac:(lia)) as H1.
  pose proof (Z.div_le_mono b APPMEM_END 8 ltac:(lia) Hb) as H2.
  replace (APPMEM_END / 8) with 0x100000000000 in H2 by reflexivity.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Lemma acl_mod_al : forall x j w, x mod 4 = 0 -> 0 <= j -> j mod 4 + w <= 4 -> (x + j) mod 8 + w <= 8.
Proof. intros x j w H Hj Hw. Z.div_mod_to_equations. lia. Qed.
Lemma acl_mod_al0 : forall x, x mod 4 = 0 -> x mod 8 + 4 <= 8.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma acl_bytes_rd : forall mc A bs x, bytes_at rsegs mc A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs mc (wa x) = Some b.
Proof.
  intros mc A bs x (_ & _ & H) Hx.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E.
  - exists b. rewrite <- E, <- H by lia. f_equal. f_equal. lia.
  - apply nth_error_None in E. lia.
Qed.

Lemma acl_rw : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hwm Ho. split; [split; [exact Hwf|]|].
  - eapply fl_bytes; [exact Hb | exact Hm |]. rewrite cells_bytes_length by exact Hwf. exact Ho.
  - eapply wr_at_transport; eassumption.
Qed.

Ltac steps_until_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evt segs Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 1 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]) ];
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac pre_no X RX := idtac.
Ltac no_extra X := idtac.
Ltac add1 X :=
  step; let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
  rewrite ?(unsigned_lit (X mod 8)) by (clear -MB; lia); clear MB.

(* The tls premise at the frame release: the run wrote only W, fp_w cs FS and Y (the thread cells are apart from the
   last two), so the thread cells and the pointers read from them are those of m (as in fl_fp_ret / acl_tls_ret). *)
Lemma acl_tls_ret : forall cs m m' TP FS lo hi W D Y Wm,
  fp cs m TP FS lo hi W D ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
     fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y)) ->
  munch Wm m m' -> sub_fp Wm (W ++ fp_w cs FS ++ Y) ->
  forall DT TS C T DB k, asan_tls_cells m' TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y).
Proof.
  intros cs m m' TP FS lo hi W D Y Wm (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _)
    Htls Hm Hs DT TS C T DB k HT.
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0)).
  { apply Forall_forall. intros [a bnd] Hin x Hx. apply Hs. apply fl_out_app.
    - exact (fl_dj_out W _ a bnd x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
    - exact (fl_dj_out_r _ _ a bnd x (Htls _ _ _ _ _ _ HT0) Hin Hx). }
  destruct (fl_tls_same m m' Wm TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0. exact (Htls _ _ _ _ _ _ HT0).
Qed.

(* --- functional helpers (image-independent, ported from the ubsan twin) --- *)
Ltac cond_unlit :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
  end.
Ltac nf := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; unfold_cond; fold_lit_ux; cond_unlit; solve_cond_rec]
  end.
Ltac nt := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; unfold_cond; fold_lit_ux; cond_unlit; solve_cond_rec]
  end.
Ltac bstep := step; nf.

Lemma mb_word : forall (x : word) z, bv_unsigned x = z -> x = Z_to_bv 64 z.
Proof. intros x z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma mb_stk_hi : forall segs m lo h hi, stk segs m lo h -> h = hi -> stk segs m lo hi.
Proof. intros; subst; assumption. Qed.

Ltac dj := cbn [disjoint_from outside cells_size csize Nat.add]; repeat split; try exact I; lia.
Ltac sfp := unfold sub_fp; cbn [outside]; intros; repeat split; try exact I; lia.

Lemma mb_rw1 : forall segs m A n X, rw_cells segs m A [CB n X] -> bytes_at segs m A X.
Proof. intros segs m A n X [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma mb_upd : forall segs m m' A N X k n Y W,
  rw_cells segs m A [CB N X] -> (k + n <= N)%nat -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (Z.of_nat k) -> disjoint_from W (A + Z.of_nat (k + n)) (Z.of_nat (N - (k + n))) ->
  bytes_at segs m' (A + Z.of_nat k) Y -> length Y = n ->
  rw_cells segs m' A [CB N (upd_bytes X k Y)].
Proof.
  intros segs m m' A N X k n Y W [[Hwf HB] HW] Hkn MU WM D1 D2 HBY LY.
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LX _].
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW.
  pose proof (bytes_at_sub segs m A X 0 k HB ltac:(lia)) as B1.
  change (skipn 0 X) with X in B1. cbn [Z.of_nat] in B1. rewrite Z.add_0_r in B1.
  pose proof (bytes_at_sub segs m A X (k + n) (N - (k + n)) HB ltac:(lia)) as B3.
  rewrite firstn_all2 in B3 by (rewrite length_skipn; lia).
  apply (bytes_at_transport segs W m m') in B1;
    [|exact MU | rewrite length_firstn; replace (Nat.min k (length X)) with k by lia; exact D1].
  apply (bytes_at_transport segs W m m') in B3;
    [|exact MU | rewrite length_skipn; replace (length X - (k + n))%nat with (N - (k + n))%nat by lia; exact D2].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length by lia; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold upd_bytes. apply bytes_at_app. split; [exact B1|].
    rewrite length_firstn. replace (Nat.min k (length X)) with k by lia.
    apply bytes_at_app. split; [exact HBY|]. rewrite LY.
    replace (A + Z.of_nat k + Z.of_nat n) with (A + Z.of_nat (k + n)) by lia. exact B3.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. eapply wr_at_transport; [exact HW | exact WM].
Qed.

Lemma mb_mid : forall segs m A pre mid post, rw_cells segs m A (pre ++ mid ++ post) ->
  bytes_at segs m (A + Z.of_nat (cells_size pre)) (cells_bytes mid).
Proof.
  intros segs m A pre mid post [[Hwf HB] _].
  apply cells_wf_app in Hwf. destruct Hwf as [Hpre _].
  rewrite !cells_bytes_app in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  apply bytes_at_app in HB. destruct HB as [HB _].
  rewrite cells_bytes_length in HB by exact Hpre. exact HB.
Qed.

Lemma mb_l4 : forall a b c d e f g h : byte, a = e -> b = f -> c = g -> d = h -> [a; b; c; d] = [e; f; g; h].
Proof. intros; subst; reflexivity. Qed.

Lemma mb_synth3 : forall row nb, synth row 3 nb = if fwm row <=? 9999 then dt1s 0 (digits (fwm row)) else zeros 32.
Proof. reflexivity. Qed.
Lemma mb_rc3 : forall row, rc row 3 = if fwm row <=? 9999 then 1 else -1.
Proof. reflexivity. Qed.
Lemma mb_synth4 : forall row nb, synth row 4 nb = dt1s 1536 (rvb row).
Proof. reflexivity. Qed.
Lemma mb_rc4 : forall row, rc row 4 = 1.
Proof. reflexivity. Qed.

Lemma mb_cons : forall (a b : byte) l l', a = b -> l = l' -> a :: l = b :: l'.
Proof. intros; subst; reflexivity. Qed.

Lemma mb_whi : forall w, 0 <= w < 65536 -> whi w = Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 w) ≫ 8))).
Proof.
  intros w Hw. unfold whi, bz. apply Z_to_bv8_mod. rewrite (unsigned_lit w) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite (unsigned_lit (w / 256)) by lia.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma mb_wlo : forall w, 0 <= w < 65536 -> wlo w = Z_to_bv 8 (bv_unsigned (Z_to_bv 64 w)).
Proof.
  intros w Hw. unfold wlo, bz. apply Z_to_bv8_mod. rewrite unsigned_lit by lia. change (2^8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma mb_synth5 : forall row nb, synth row 5 nb = if has row =? 0 then zeros 32 else idf (nmr row nb).
Proof. reflexivity. Qed.
Lemma mb_rc5 : forall row, rc row 5 = if has row =? 0 then 0 else 1.
Proof. reflexivity. Qed.
Lemma mb_synth6 : forall row nb, synth row 6 nb = if has row =? 0 then zeros 32 else idl (nmr row nb).
Proof. reflexivity. Qed.
Lemma mb_rc6 : forall row, rc row 6 = if has row =? 0 then 0 else 1.
Proof. reflexivity. Qed.

Lemma mb_flat : forall segs m A N X cs, rw_cells segs m A (CB N X :: cs) ->
  rw_cells segs m A [CB (N + cells_size cs) (X ++ cells_bytes cs)].
Proof.
  intros segs m A N X cs [[[LX Hcs] HB] HW]. cbn [cell_wf] in LX.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite length_app, cells_bytes_length by exact Hcs. lia.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize] in *. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma mb_unflat : forall segs m A N X cs, rw_cells segs m A [CB (N + cells_size cs) (X ++ cells_bytes cs)] ->
  length X = N -> cells_wf cs -> rw_cells segs m A (CB N X :: cs).
Proof.
  intros segs m A N X cs [[_ HB] HW] LX Hcs.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact LX | exact Hcs].
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in HB. exact HB.
  - cbn [cells_size csize] in *. rewrite Nat.add_0_r in HW. exact HW.
Qed.

Lemma mb_upd_app : forall (X R Y : list byte) k, (k + length Y <= length X)%nat ->
  upd_bytes (X ++ R) k Y = upd_bytes X k Y ++ R.
Proof.
  intros X R Y k H. unfold upd_bytes. rewrite firstn_app, skipn_app.
  replace (k - length X)%nat with 0%nat by lia. replace (k + length Y - length X)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma mb_first_upd : forall (X Y : list byte) k, length X = 32%nat -> (k + length Y = 31)%nat ->
  firstn 31 (upd_bytes X k Y) = firstn k X ++ Y.
Proof.
  intros X Y k LX LY. unfold upd_bytes. rewrite LY, app_assoc, firstn_app, length_app, length_firstn.
  replace (31 - (Nat.min k (length X) + length Y))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. apply firstn_all2. rewrite length_app, length_firstn. lia.
Qed.

Lemma mb_nmf_len : forall nb, (length nb <= 16)%nat -> length (nmf nb) = 16%nat.
Proof. intros nb L. unfold nmf. rewrite length_app, repeat_length. pose proof (rs_takenz_len nb). lia. Qed.

Lemma mb_sx32_eq0 : forall x, 0 <= x < 2^32 -> bv_eqb (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold sx32, bv_eqb. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  apply Bool.eq_iff_eq_true. rewrite !Z.eqb_eq. split; intros H; lia.
Qed.

Ltac mb_bytes :=
  repeat (apply mb_cons; [first [reflexivity | apply Z_to_bv8_mod; vm_compute; reflexivity] |]); reflexivity.

Lemma mb_stamp8 : forall s,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s)))))
                                     127))) = Z_to_bv 8 ((- s) mod 128).
Proof. intros s. exact (f_equal (hd (bz 0)) (rc_le1_stamp s)). Qed.

Lemma mb_psum_app : forall A B k, psum (A ++ B) (length A + k) = psum A (length A) + psum B k.
Proof.
  intros A B k. induction k as [|k IH].
  - rewrite Nat.add_0_r, psum_app_l by lia. cbn [psum]. lia.
  - rewrite Nat.add_succ_r. cbn [psum]. rewrite IH, app_nth2 by lia.
    replace (length A + k - length A)%nat with k by lia. lia.
Qed.

Lemma mb_sltiu1 : forall x, 0 <= x < 2^64 - 10 -> v_sltiu (Z_to_bv 64 x) (-10) = Z_to_bv 64 1.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia.
  assert (E : bv_wrap 64 (-10) = 18446744073709551606) by reflexivity. rewrite E.
  replace (x <? 18446744073709551606) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma mb_idl_eq : forall (H S6 : list byte) c, length H = 9%nat -> length S6 = 6%nat ->
  firstn 31 (upd_bytes (upd_bytes (H ++ zeros 23) 9 S6) 15 [c; bz 247]) = H ++ S6 ++ [c; bz 247] ++ zeros 14.
Proof.
  intros H S6 c LH LS.
  change (H ++ zeros 23) with (H ++ [] ++ zeros 23).
  rewrite (rs_upd_fill H [] S6 23 9) by (cbn [length]; lia). rewrite LS.
  change (H ++ ([] ++ S6) ++ zeros (23 - 6)) with (H ++ S6 ++ zeros 17).
  rewrite (rs_upd_fill H S6 [c; bz 247] 17 15) by (cbn [length]; lia).
  change (17 - length [c; bz 247])%nat with 15%nat.
  assert (E : H ++ (S6 ++ [c; bz 247]) ++ zeros 15 = (H ++ S6 ++ [c; bz 247] ++ zeros 14) ++ [bz 0])
    by (rewrite <- !app_assoc; reflexivity).
  rewrite E.
  assert (L : length (H ++ S6 ++ [c; bz 247] ++ zeros 14) = 31%nat) by (rewrite !length_app, LH, LS; reflexivity).
  rewrite <- L at 1. apply firstn_app_exact.
Qed.

Ltac nfc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false by (vm_compute; reflexivity); cbv iota
  end.

Ltac st0 := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?x ?bs) _) =>
      is_var x;
      replace (write_to_mem mm x bs) with (write_to_mem mm (wa (bv_unsigned x + Z.of_nat 0)) bs)
        by (f_equal; symmetry; apply rc_wa_add0)
  end; mem_after_store_opt.

Lemma mb_synth0 : forall row nb, synth row 0 nb = if synok row then gram row else zeros 32.
Proof. reflexivity. Qed.
Lemma mb_rc0 : forall row, rc row 0 = if synok row then 1 else -1.
Proof. reflexivity. Qed.

Lemma mb_synok_iff : forall row, synok row = true <->
  0 <= ic row /\ 0 <= oc row /\ ic row mod 4 = 0 /\ oc row mod 4 = 0 /\ ic row / 4 + oc row / 4 <= 12.
Proof. intros r. unfold synok. rewrite !andb_true_iff, !Z.leb_le, !Z.eqb_eq. tauto. Qed.

Lemma mb_synok_false : forall row,
  ~ (0 <= ic row /\ 0 <= oc row /\ ic row mod 4 = 0 /\ oc row mod 4 = 0 /\ ic row / 4 + oc row / 4 <= 12) ->
  synok row = false.
Proof. intros r H. destruct (synok r) eqn:E; [|reflexivity]. exfalso. apply H. apply mb_synok_iff. exact E. Qed.

Lemma mb_sltu0 : forall x (y : word), bv_unsigned y <= x < 2^64 -> v_sltu (Z_to_bv 64 x) y = Z_to_bv 64 0.
Proof.
  intros x y H. pose proof (zr_word y) as Ry. unfold inr64 in Ry.
  unfold v_sltu, c_ltu, bv_ltu. rewrite unsigned_lit by lia.
  replace (x <? bv_unsigned y) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma mb_slti0 : forall x, 0 <= x < 2^63 -> v_slti (Z_to_bv 64 x) 0 = Z_to_bv 64 0.
Proof.
  intros x H. unfold v_slti, zsig. rewrite zb_signed, unsigned_lit by lia.
  replace (x <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (x <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma mb_lts_lit : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed. rewrite !unsigned_lit by lia.
  replace (x <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma mb_addiw : forall x d, 0 <= x < 2^64 -> 0 <= x + d < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + d)) = Z_to_bv 64 (x + d).
Proof. intros x d H1 H2. rewrite unsigned_lit by lia. rewrite rc_swrap_small by lia. reflexivity. Qed.

Lemma mb_swrap_lit : forall x, 0 <= x < 2^31 -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x))) = Z_to_bv 64 x.
Proof. intros x H. rewrite unsigned_lit by lia. rewrite rc_swrap_small by lia. reflexivity. Qed.

Lemma mb_zext32 : forall x, 0 <= x < 2^32 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32))) 32 = x.
Proof.
  intros x H. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

Lemma mb_rep_snoc : forall (x : byte) n, repeat x n ++ [x] = repeat x (S n).
Proof. intros x n. induction n as [|n IH]; [reflexivity|]. cbn [repeat app]. rewrite IH. reflexivity. Qed.

Lemma mb_fill_step : forall (H P : list byte) b, length H = 8%nat -> (length P < 24)%nat ->
  upd_bytes (H ++ P ++ zeros (24 - length P)) (8 + length P) [b] = H ++ (P ++ [b]) ++ zeros (24 - length (P ++ [b])).
Proof.
  intros H P b LH LP. rewrite (rs_upd_fill H P [b] (24 - length P) (8 + length P)) by (cbn [length]; lia).
  rewrite length_app. cbn [length].
  replace (24 - length P - 1)%nat with (24 - (length P + 1))%nat by lia. reflexivity.
Qed.

Ltac bst := step; first [nf | nfc].


Section Main.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  Hypothesis HSM : asan_stack_malloc_0_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).

  Lemma STW0 : forall a, bv_unsigned sp - 4272 <= a < bv_unsigned sp -> wview rsegs m (wa a) <> None.
  Proof. intros a Ha. exact (stk_wv m _ _ _ ST0 Ha). Qed.

  Lemma HA1 : A mod 32 = 0 /\ bv_unsigned sp - 176 <= A <= bv_unsigned sp - 160.
  Proof. rewrite HA. Z.div_mod_to_equations. lia. Qed.

  Definition SAVES : list cell :=
    [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* The writes of the run outside o: the window, the class-0 hint word, flag j, the frame and its shadow. *)
  Definition Wf (fr j n : Z) : list ivl :=
    [(bv_unsigned sp - 4272, bv_unsigned sp); (FS, FS); (fs_flag FS 0 j, fs_flag FS 0 j + n);
     (fr, fr + 64); (shadow_addr fr, shadow_addr fr + 8)].

  (* The frame: real (f = 0, fr = A - 64 = sp) or fake (fr = f, the class-0 frame j, sp = A, the flag-byte address
     w56 at fr + 56). *)
  Definition FK (fr f spc j n : Z) (w56 : word) : Prop :=
    (f = 0 /\ fr = A - 64 /\ spc = A - 64 /\ j = 0 /\ n = 0) \/
    (0 <= j < fs_M 0 /\ fr = fs_frame FS 0 j /\ f = fr /\ spc = A /\ w56 = Z_to_bv 64 (fs_flag FS 0 j) /\ n = 1).

  Definition BI (W : list ivl) (fr : Z) (w56 : word) (mc : word -> option byte) : Prop :=
    munch W m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (bv_unsigned sp + -88) SAVES /\
    (exists h, bytes_at rsegs mc FS (le8 h)) /\
    bytes_at rsegs mc (fr + 56) (le8 w56).

  Definition KB (Q : machine_state -> Prop) : Prop :=
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
           (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      FK fr f spc j n w56 -> BI (Wf fr j n) fr w56 mc ->
      evt rsegs Q (MS (mkR (Z_to_bv 64 0x86648) (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                         a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                         (Z_to_bv 64 b) (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                         t3' t4' t5' t6') F (Z_to_bv 64 0x866d4) fc None mc (seg_rom rsegs)).

  Lemma app_range : forall X n, 0 < n -> (forall i, 0 <= i < n -> app_mem (X + i)) ->
    X + n <= 2147450880 \/ 17594333495296 <= X.
  Proof.
    intros X n Hn H. pose proof (H 0 ltac:(lia)) as H0. pose proof (H (n - 1) ltac:(lia)) as H1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H0, H1.
    destruct (Z.le_gt_cases (X + n) 2147450880) as [L|L]; [left; exact L|].
    destruct (Z.le_gt_cases 17594333495296 X) as [G|G]; [right; exact G|].
    exfalso. pose proof (H (2147450880 - X) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H2. lia.
  Qed.

  (* What every frame gives: alignment, place, writable and AppMem bytes, writable shadow bytes. *)
  Lemma fk_facts : forall fr f spc j n w56, FK fr f spc j n w56 ->
    fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\ (spc = A \/ spc = fr) /\
    (forall i, 0 <= i < 64 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 64 -> app_mem (fr + i)) /\
    (fr + 64 <= 2147450880 \/ 17594333495296 <= fr) /\
    (forall i, 0 <= i < 8 -> wview rsegs m (wa (fr / 8 + off + i)) <> None) /\
    2147450880 <= fr / 8 + off /\ fr / 8 + off + 8 <= 17594333495296.
  Proof.
    intros fr f spc j n w56 HK.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & _).
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
    assert (B : fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\ (spc = A \/ spc = fr) /\
                (forall i, 0 <= i < 64 -> wview rsegs m (wa (fr + i)) <> None) /\
                (forall i, 0 <= i < 64 -> app_mem (fr + i))).
    { destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)]; subst fr.
      - split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia|].
        intros i Hi. destruct AW0 as (_ & _ & _ & AW).
        pose proof (proj1 (AW (A - 64 + i - (bv_unsigned sp - 4272)) ltac:(lia))) as AP.
        replace (bv_unsigned sp - 4272 + (A - 64 + i - (bv_unsigned sp - 4272))) with (A - 64 + i) in AP by lia.
        exact AP.
      - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat] in *. change (2 ^ (14 - 0)) with 16384 in Hj.
        change (2 ^ 0) with 1 in *.
        split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ P5); lia|].
        intros i Hi. apply P4. lia. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (app_range fr 64 ltac:(lia) B6) as B7.
    assert (B8 : forall i, 0 <= i < 8 -> fr / 8 + off + i = shadow_addr (fr + 8 * i)).
    { intros i Hi. rewrite sh_add8 by exact B1. unfold shadow_addr. rewrite Hoff. lia. }
    do 7 (split; [assumption|]).
    split.
    - (* route (C): the frame's 8 shadow bytes lie in the run's region R: those of the real frame [A - 64, A) in
         the window's shadow-word cover (R's 1st disjunct), those of the class-0 frame fs_frame FS 0 j in the
         class-0 block's shadow (R's 2nd disjunct, asan_stack_malloc_shadow_R FS 0) *)
      intros i Hi. rewrite B8 by exact Hi.
      assert (HR : reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb (shadow_addr (fr + 8 * i))).
      { clear - HK Hi HAlo HAhi.
        unfold reac_box_model_block_shadow_R, sh_word_on, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi,
          asan_stack_malloc_shadow_R, shadow_addr, REAC_BOX_MODEL_BLOCK_K, ASAN_K.
        destruct HK as [(_ & Efr & _) | (Hj & Efr & _)].
        - left. split; [lia|]. subst fr. Z.div_mod_to_equations. lia.
        - right; left. change (fs_M 0%nat) with 16384 in Hj. subst fr. unfold fs_frame, fs_B. cbn [Z.of_nat].
          Z.div_mod_to_equations. lia. }
      apply (proj1 (SR0 _ HR (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
    - rewrite Hoff. unfold ASAN_K. split; Z.div_mod_to_equations; lia.
  Qed.

  Ltac bi_intro H :=
    let MU := fresh "MU" in let WM := fresh "WM" in let RM := fresh "RM" in let MI := fresh "MI" in
    let SV := fresh "SV" in let HH := fresh "HH" in let hh := fresh "h" in let F56 := fresh "F56" in
    destruct H as (MU & WM & RM & MI & SV & (hh & HH) & F56).

  (* The byte x is writable in m: in the window (ST0), in the frame (FW) or a shadow byte of the frame (SW). *)
  Ltac wv_tac :=
    let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii;
    first [ match goal with
            | STW : forall a, bv_unsigned sp - 4272 <= a < bv_unsigned sp -> wview rsegs m (wa a) <> None |- _ =>
                apply STW; lia
            end
          | apply STW0; lia
          | match goal with
            | FW : forall i, 0 <= i < 64 -> wview rsegs m (wa (?fr + i)) <> None |- wview _ _ (wa ?x) <> None =>
                replace x with (fr + (x - fr)) by lia; apply FW; lia
            end
          | match goal with
            | SW : forall i, 0 <= i < 8 -> wview rsegs m (wa (?s + i)) <> None |- wview _ _ (wa ?x) <> None =>
                replace x with (s + (x - s)) by lia; apply SW; lia
            end ].

  (* store_ok of n bytes at a in the current memory. *)
  Ltac wst a n :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) n = true)
          by (eapply wv_store_ok; [ wv_tac | eassumption | lia | lia ])
    end.

  (* +0xa0 .. +0x100: the frame record (fr at A+24), the three magic frame words and the frame's shadow. *)


  (* The runtime state the post names, carried across the body (asan_cells, shadow_rw, the window addressable, fp and
     the tls premise). *)
  Definition JR (m' : word -> option byte) : Prop :=
    asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m') /\ addressable m' (bv_unsigned sp - 4272) 4272 /\
    fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) /\
    reac_box_model_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp).

  Lemma JR_m : JR m.
  Proof.
    split; [exact AC0|]. split; [exact (fun P HP => HP)|]. split; [exact AW0|]. split; [exact FP0 | exact TLS0].
  Qed.

  (* The runtime state survives writes inside the function's window [sp - 4272, sp). *)
  Lemma jr_win : forall W' m1 m2, JR m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 ->
    sub_fp W' [(bv_unsigned sp - 4272, bv_unsigned sp)] -> JR m2.
  Proof.
    intros W' m1 m2 (AC & SW & AW & FP & TL) MU WM Hs.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' (bv_unsigned sp - 4272) (bv_unsigned sp) x Hs HHM Hx)).
    unfold JR, reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K in *.
    split; [|split; [|split; [|split]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply (fl_out_lo W' (bv_unsigned sp - 4272) (bv_unsigned sp) x Hs).
      left. clear -Hx HHM'. unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - intros P HP. exact (B.ShadowRwOnK.fl_shadow_rw_on P W' m1 m2 (SW P HP) MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_fp [0%nat] m1 m2 (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
               (if o =? 0 then [] else [(o, o + 32)]) (reac_box_model_block_D p o) W' FP MU WM Hs).
    - exact (fl_tls [0%nat] m1 m2 (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
               (if o =? 0 then [] else [(o, o + 32)]) (reac_box_model_block_D p o) W'
               (fp_w [0%nat] FS ++ [(shadow_addr (bv_unsigned sp - 4272), shadow_addr (bv_unsigned sp))]) FP MU Hs TL).
  Qed.

  (* The remaining premises of the contract, used by the body (KB Q0). *)
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rb : 0 <= b < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
  Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
    (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
  Hypothesis AP : p <> 0 -> addressable m p 296.
  Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    addressable m (rname row) (Z.of_nat (length nb)).
  Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).

  (* The post's fp at m': the run wrote only within the window+o (fp's W), the class-0 side-stack bytes (fp_w [0] FS)
     and the window's shadow (reac_box_model_block_X); the thread cells and the header points FS+88/FS+96 are apart
     from all of these (FP0's W-disjointness and TLS0), the side stack stays readable (rd_mono), and the hint and the
     flag bytes read back as 0/1 (given). *)
  Lemma br_fp : forall (Wm : list ivl) (m' : word -> option byte) (h' : word) (flags' : list byte),
    munch Wm m m' -> wmono rsegs m m' -> rd_mono m m' ->
    sub_fp Wm (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS) ->
    bytes_at rsegs m' (fs_hint FS 0) (le8 h') ->
    bytes_at rsegs m' (fs_flag FS 0 0) flags' -> Z.of_nat (length flags') = fs_M 0 ->
    Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags' ->
    fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Proof.
    intros Wm m' h' flags' MU WM RM Hs Hint' Hflags' Hlen' HF01'.
    pose proof FP0 as (DT & TS & C & T & DB & k & HT & HTP & HPl & H88 & H96 & HCL & HFS & HApp & HWd & HDd).
    pose proof (TLS0 DT TS C T DB k HT) as TLSdj.
    pose proof HPl as (P1 & P2 & P3 & P4 & P5).
    clear FP0 TLS0 HSM Hoff HA HS16 ST0 MI0 AC0 SR0 AW0 Rp Rb Ro HP HN HO AP ANB AO AJ1 AJ2 NDJ HCL.
    assert (OUTC : forall x, outside (reac_box_model_block_W o (bv_unsigned sp)) x ->
                    outside (reac_box_model_block_X (bv_unsigned sp) FS) x -> outside Wm x).
    { intros x H1 H2. apply Hs. apply fl_out_app; [exact H1 | exact H2]. }
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x)
                   (fp_tls (bv_unsigned tp) DT TS C T DB k)).
    { apply Forall_forall. intros [a bnd] Hin x Hx. apply OUTC.
      - exact (fl_dj_out _ _ a bnd x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
      - exact (fl_dj_out_r _ _ a bnd x TLSdj Hin Hx). }
    cbn [fp_tls] in Hc.
    repeat (let O := fresh "O" in apply Forall_cons_iff in Hc; destruct Hc as [O Hc]; cbn [fst snd] in O).
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFM : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    assert (EFS : FS + FS_SIZE <= APPMEM_END) by (pose proof HAE; lia).
    assert (O88 : forall y, FS + 80 <= y < FS + 104 -> outside Wm y).
    { intros y Hy.
      assert (Hap : app_mem y) by (apply P4; unfold FS_SIZE; lia).
      apply OUTC.
      - apply (fl_dj_out _ _ FS (fs_frame FS 0 0) y HWd
                 ltac:(apply in_or_app; right; left; reflexivity)). rewrite EFR0. lia.
      - unfold reac_box_model_block_X. apply fl_out_app.
        + unfold fp_w, fp_w1; cbn [flat_map app outside].
          split; [unfold fs_hint; cbn [Z.of_nat]; lia|].
          split; [unfold fs_flag, fs_M; cbn [Z.of_nat]; lia|].
          split; [rewrite EFR0; lia|].
          split; [|exact I].
          exact (acl_sh_out y (fs_frame FS 0 0) (fs_frame FS 0 (fs_M 0)) Hap
            ltac:(rewrite EFR0; lia) ltac:(rewrite EFM; unfold FS_SIZE in EFS; lia)).
        + cbn [outside fst snd]. split; [|exact I].
          assert (Hle : 0 <= bv_unsigned sp - 4272) by (pose proof HHM; unfold HIGHMEM_BEG in *; lia).
          exact (acl_sh_out y (bv_unsigned sp - 4272) (bv_unsigned sp) Hap Hle HAE). }
    destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
      & T19).
    exists DT, TS, C, T, DB, k.
    split.
    { unfold asan_tls_cells.
      split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|].
      split; [fl_cellO MU|]. split; [exact T6|]. split; [fl_cellO MU|]. split; [fl_cellO MU|].
      split; [fl_cellO MU|]. split; [fl_cellO MU|].
      split; [destruct T11 as (tb & te & T11); exists tb, te; fl_cellO MU|].
      split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|].
      split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [exact T18|]. fl_cellO MU. }
    split; [fl_cellO MU|].
    split.
    { unfold fs_place. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      eapply fl_stk; [exact P5 | exact MU | exact WM |].
      intros y Hy. right. apply RM. exact (proj2 ((proj2 (proj2 P5)) y Hy)). }
    split; [fl_cellO MU|].
    split; [fl_cellO MU|].
    split.
    { constructor; [|constructor]. split; [cbn; lia|]. exists h', flags'.
      split; [exact Hint'|]. split; [exact Hflags'|]. split; [exact Hlen' | exact HF01']. }
    split; [exact HFS|]. split; [exact HApp|]. split; [exact HWd | exact HDd].
  Qed.

  (* The full body footprint stays apart from the runtime's cells [RT_LO, RT_HI): the window and the side stack are
     above them, o is apart (AO), and every shadow byte is apart from application memory. *)
  Lemma br_out_rt : forall (Wm : list ivl) x,
    sub_fp Wm (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS) ->
    RT_LO <= x < RT_HI -> outside Wm x.
  Proof.
    intros Wm x Hs Hx.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & _) & _ & _ & _ & HFSb & _ & _ & _).
    unfold HIGHMEM_BEG, APPMEM_END in HHM'. unfold RT_LO, RT_HI in Hx. unfold ASAN_GT in P3.
    assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia).
    apply Hs. apply fl_out_app.
    - unfold reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K. cbn [outside]. split; [lia|].
      destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside]; [exact I|].
      destruct (AO Eo) as (_ & _ & DRT). unfold RT_LO, RT_HI in DRT. split; [lia | exact I].
    - assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      assert (EFM : fs_frame FS 0 (fs_M 0) = FS + 1085440).
      { unfold fs_frame, fs_B, fs_M.
        replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
        replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
      assert (EFS : FS + FS_SIZE <= APPMEM_END) by (pose proof HFSb; pose proof HAE; unfold APPMEM_END in *; lia).
      unfold reac_box_model_block_X, fp_w, fp_w1; cbn [flat_map app outside].
      split; [unfold fs_hint; cbn [Z.of_nat]; lia|].
      split; [unfold fs_flag, fs_M; cbn [Z.of_nat]; lia|].
      split; [rewrite EFR0; lia|].
      split; [exact (acl_sh_out x (fs_frame FS 0 0) (fs_frame FS 0 (fs_M 0)) Hap
                ltac:(rewrite EFR0; lia) ltac:(rewrite EFM; unfold FS_SIZE in EFS; lia))|].
      cbn [outside]. split; [|exact I].
      exact (acl_sh_out x (bv_unsigned sp - 4272) (bv_unsigned sp) Hap
               ltac:(unfold APPMEM_END in *; lia) HAE).
  Qed.

  Lemma br_ac : forall (Wm : list ivl) (m' : word -> option byte), munch Wm m m' ->
    sub_fp Wm (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS) ->
    asan_cells m'.
  Proof.
    intros Wm m' MU Hs. apply (fl_asan_cells Wm m m' AC0 MU). intros x Hx. exact (br_out_rt Wm x Hs Hx).
  Qed.

  Definition Q0 (frq jq nq : Z) : machine_state -> Prop :=
    fun ms => reac_box_model_block_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb ms /\
      munch (Wf frq jq nq ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) m (ms_mem ms) /\
      (nq = 1 -> mrd rsegs (ms_mem ms) (wa (fs_flag FS 0 jq)) = Some (Z_to_bv 8 0)).

  (* 0x86e74: a0 = s5, the saved registers (ra, s0..s9) restored and the frame popped, ret. *)
  (* Every byte of the function's window is addressable at m (AW0), so its shadow bytes are 0. *)
  Lemma win_shadow0 : forall i, 0 <= i < 4272 ->
    mrd rsegs m (wa (shadow_addr (bv_unsigned sp - 4272 + i))) = Some (Z_to_bv 8 0).
  Proof.
    intros i Hi. pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    destruct AW0 as (A0 & An & Ae & HAd).
    assert (Hal : (bv_unsigned sp - 4272) mod 8 = 0) by (pose proof HS16; Z.div_mod_to_equations; lia).
    assert (Hi7 : 0 <= 8 * (i / 8) + 7 < 4272) by (Z.div_mod_to_equations; lia).
    destruct (HAd (8 * (i / 8) + 7) Hi7) as (Hap & bsh & Hb & Hok).
    assert (Esh : shadow_addr (bv_unsigned sp - 4272 + (8 * (i / 8) + 7)) = shadow_addr (bv_unsigned sp - 4272 + i)).
    { unfold shadow_addr. Z.div_mod_to_equations. lia. }
    assert (Em7 : (bv_unsigned sp - 4272 + (8 * (i / 8) + 7)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
    unfold shadow_ok in Hok. rewrite Em7 in Hok.
    assert (Hb0 : bv_signed bsh = 0) by (destruct Hok as [H0|[H1 H2]]; lia).
    rewrite <- Esh, Hb. f_equal.
    apply bv_eq. pose proof (bv_unsigned_in_range 8 bsh) as Hr. unfold bv_modulus in Hr.
    unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hb0.
    change (2 ^ Z.of_N 8) with 256 in *. change (2 ^ Z.of_N 8 / 2) with 128 in *.
    change (bv_unsigned (Z_to_bv 8 0)) with 0. Z.div_mod_to_equations. lia.
  Qed.

  (* 0x86e74: the epilogue, but with s6 (clobbered by the jump-table dispatch) left general. Like td_tail but the
     s6 slot is a parameter: the restore (ld s6, 96(sp)) overwrites it, so its input value is irrelevant. *)

  (* The class-0 flag array reads back 0/1 at the frame release: every flag byte but the frame's own flag j is kept
     from m (0/1 by FP0's fp_cls), and flag j is cleared to 0 by the release (side stack) or kept (real stack, n=0).
     This is the readback br_fp needs; no body-invariant flag state is required beyond the fine footprint. *)
  Lemma rel_flags : forall (fr f spc j n : Z) (w56 : word) (m' : word -> option byte),
    FK fr f spc j n w56 ->
    munch (Wf fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) m m' ->
    (n = 1 -> mrd rsegs m' (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
    exists flags', bytes_at rsegs m' (fs_flag FS 0 0) flags' /\ Z.of_nat (length flags') = fs_M 0 /\
      Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'.
  Proof.
    intros fr f spc j n w56 m' HK MU Hfj.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _ & _ & HCL & HFSl & _ & _ & HDd).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFSl, P4, P5.
    apply Forall_cons_iff in HCL. destruct HCL as [(_ & hh & flags & _ & HFl & HLen & HF01) _].
    assert (EF0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EFM0 : fs_M 0 = 16384) by reflexivity.
    assert (EFj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (FK0 : 0 <= j /\ j < 16384) by
      (destruct HK as [(_&_&_&Ej&_)|(Hj&_)]; [lia | change (fs_M 0) with 16384 in Hj; lia]).
    destruct FK0 as (Hj0 & Hj16).
    assert (FAPP : forall x, FS + 4096 <= x < FS + 4096 + 16384 -> app_mem x)
      by (intros x Hx; apply P4; lia).
    assert (FR64 : fr + 64 <= APPMEM_END) by (pose proof (FAP 63 ltac:(lia)) as HA63; unfold app_mem, APPMEM_END in HA63; lia).
    (* a flag byte outside [flag j, flag j + n) is outside the fine footprint *)
    assert (Hout : forall x, FS + 4096 <= x < FS + 4096 + 16384 ->
                     (x < FS + 4096 + j \/ FS + 4096 + j + n <= x) ->
                     outside (Wf fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) x).
    { intros x Hx Hxj. apply fl_out_app.
      - unfold Wf. cbn [outside]. rewrite EFj.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
        assert (Hap : app_mem x) by (apply FAPP; lia).
        replace (shadow_addr fr + 8) with (shadow_addr (fr + 64))
          by (unfold shadow_addr; Z.div_mod_to_equations; lia).
        exact (acl_sh_out x fr (fr + 64) Hap ltac:(lia) FR64).
      - destruct ((p =? 0) || (o =? 0)) eqn:Epo; cbn [outside]; [exact I|].
        split; [|exact I].
        apply orb_false_iff in Epo. destruct Epo as [Ep0 Eo0].
        assert (Hin_o : In (o, o + 32) (reac_box_model_block_D p o)).
        { unfold reac_box_model_block_D. apply in_or_app. right. rewrite Eo0. left; reflexivity. }
        assert (Hin_f : In (fs_flag FS 0 0, fs_flag FS 0 0 + fs_M 0) (fp_w [0%nat] FS)).
        { unfold fp_w, fp_w1. cbn [flat_map app]. right; left; reflexivity. }
        unfold fp_dj in HDd. rewrite Forall_forall in HDd. pose proof (HDd _ Hin_o) as HD1.
        rewrite Forall_forall in HD1. pose proof (HD1 _ Hin_f) as HD2.
        unfold ly_dj in HD2. cbn [fst snd] in HD2. rewrite EF0, EFM0 in HD2. lia. }
    assert (HLfs : Z.of_nat (length flags) = 16384) by (rewrite HLen; reflexivity).
    rewrite EF0 in HFl.
    destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
    - (* real-stack frame: n = 0, no flag touched; the array is kept entirely *)
      subst n j. exists flags. rewrite EF0.
      split; [|split; [rewrite HLen; reflexivity | exact HF01]].
      eapply fl_bytes; [exact HFl | exact MU |].
      intros x Hx. apply Hout; [lia | lia].
    - (* side-stack frame: n = 1, flag j cleared to 0 *)
      subst n. remember (Z.to_nat j) as jn eqn:Ejn0.
      assert (Ejn : Z.of_nat jn = j) by (subst jn; apply Z2Nat.id; lia).
      assert (HjL : (jn + 1 <= length flags)%nat) by lia.
      pose proof (bytes_at_sub rsegs m (FS + 4096) flags 0 jn) as B1.
      specialize (B1 HFl ltac:(lia)).
      change (skipn 0 flags) with flags in B1. cbn [Z.of_nat] in B1. rewrite Z.add_0_r in B1.
      pose proof (bytes_at_sub rsegs m (FS + 4096) flags (jn + 1) (length flags - (jn + 1))) as B3.
      specialize (B3 HFl ltac:(lia)).
      rewrite firstn_all2 in B3 by (rewrite length_skipn; lia).
      (* transport the two kept parts to m' *)
      assert (B1' : bytes_at rsegs m' (FS + 4096) (firstn jn flags)).
      { apply (fl_bytes _ m m' _ _ B1 MU). intros x Hx. rewrite length_firstn in Hx.
        apply Hout; [lia | left; lia]. }
      assert (B3' : bytes_at rsegs m' (FS + 4096 + Z.of_nat (jn + 1)) (skipn (jn + 1) flags)).
      { apply (fl_bytes _ m m' _ _ B3 MU). intros x Hx. rewrite length_skipn in Hx.
        apply Hout; [lia | right; lia]. }
      clear B1 B3.
      (* the cleared middle byte *)
      assert (Bmid : bytes_at rsegs m' (FS + 4096 + Z.of_nat jn) [Z_to_bv 8 0]).
      { split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
        assert (i = 0%nat) by lia. subst i. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
        rewrite Ejn, <- EFj. exact (Hfj eq_refl). }
      exists (firstn jn flags ++ [Z_to_bv 8 0] ++ skipn (jn + 1) flags). rewrite EF0.
      split; [|split].
      + apply bytes_at_app. split; [exact B1'|]. rewrite length_firstn, Nat.min_l by lia.
        apply bytes_at_app. split; [exact Bmid|].
        replace (FS + 4096 + Z.of_nat jn + Z.of_nat (length [Z_to_bv 8 0])) with (FS + 4096 + Z.of_nat (jn + 1))
          by (cbn [length]; lia).
        exact B3'.
      + rewrite !length_app, length_firstn, length_skipn, Nat.min_l by lia. cbn [length].
        rewrite <- HLen. f_equal. lia.
      + pose proof HF01 as HFa. rewrite <- (firstn_skipn jn flags) in HFa. apply Forall_app in HFa.
        destruct HFa as [Hfst _].
        pose proof HF01 as HFb. rewrite <- (firstn_skipn (jn + 1) flags) in HFb. apply Forall_app in HFb.
        destruct HFb as [_ Hsk1].
        apply Forall_app. split; [exact Hfst|]. apply Forall_app.
        split; [constructor; [left; reflexivity | constructor] | exact Hsk1].
  Qed.
End Main.

(* route (C): SR0 names b row nb, so fk_facts' closed form takes them; they are implicit, inferred from SR0, so
   every caller keeps the argument list `fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 ...`. *)
Arguments fk_facts sp tp m p {b} o FS off A {row nb}.
