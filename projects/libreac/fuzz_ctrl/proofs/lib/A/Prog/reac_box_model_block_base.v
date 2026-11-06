(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1316 of its 1346 lines of code are new or changed and 218 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c reac_box_model_block_c.
Import ListNotations.
Open Scope Z_scope.

(* reac_box_model_block, image A (asan, entry 0x85b44), part 1 of the proof of reac_box_model_block_holds
   (reac_box_model_block.v): the frame request and the frame words (entry, fwords), the body-end invariant EB, the
   frame-release read-back facts and the restore/return (epi_close). The epilogue stepping is in
   reac_box_model_block_epi.v and the body in reac_box_model_block_body*.v; each re-opens Section Main with the same
   variables and hypotheses and uses the lemmas below applied to them. *)


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


Section Main.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  Hypothesis HSM : asan_stack_malloc_0_contract.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
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
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* The writes of the run outside o: the window, the class-0 hint word, flag j, the frame and its shadow. *)
  Definition Wf (fr j n : Z) : list ivl :=
    [(bv_unsigned sp - 4272, bv_unsigned sp); (FS, FS + 8); (fs_flag FS 0 j, fs_flag FS 0 j + n);
     (fr, fr + 64); (shadow_addr fr, shadow_addr fr + 8)].

  (* The frame: real (f = 0, fr = A - 64 = sp) or fake (fr = f, the class-0 frame j, sp = A, the flag-byte address
     w56 at fr + 56). *)
  Definition FK (fr f spc j n : Z) (w56 : word) : Prop :=
    (f = 0 /\ fr = A - 64 /\ spc = A - 64 /\ j = 0 /\ n = 0) \/
    (0 <= j < fs_M 0 /\ fr = fs_frame FS 0 j /\ f = fr /\ spc = A /\ w56 = Z_to_bv 64 (fs_flag FS 0 j) /\ n = 1).

  Definition BI (W : list ivl) (fr : Z) (w56 : word) (mc : word -> option byte) : Prop :=
    munch W m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (bv_unsigned sp + -104) SAVES /\
    (exists h, bytes_at rsegs mc FS (le8 h)) /\
    bytes_at rsegs mc (fr + 56) (le8 w56).

  Definition KB (Q : machine_state -> Prop) : Prop :=
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
           (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      FK fr f spc j n w56 -> BI (Wf fr j n) fr w56 mc ->
      evt rsegs Q (MS (mkR (Z_to_bv 64 0x85bbc) (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                         a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                         (Z_to_bv 64 b) (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                         t3' t4' t5' t6') F (Z_to_bv 64 0x85c48) fc None mc (seg_rom rsegs)).

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
    - intros i Hi. rewrite B8 by exact Hi. apply (proj1 (SR0 _ (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
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

  (* +0xa8 .. +0x100: the frame words and the frame's shadow. *)
  Lemma fwords : forall fr f spc j n w56 mc (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Q,
    FK fr f spc j n w56 -> BI (Wf fr j n) fr w56 mc -> KB Q ->
    evt rsegs Q (MS (mkR (Z_to_bv 64 0x85bbc) (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                       a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                       (Z_to_bv 64 b) (Z_to_bv 64 fr) s8 (wa off) s10 s11
                       t3' t4' t5' t6') F (Z_to_bv 64 0x85bec) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Q HK HB K.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & _).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'. pose proof HP as (P1 & P2 & P3 & P4 & P5).
    unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    pose proof (app_range FS 8 ltac:(lia) ltac:(intros i Hi; apply P4; lia)) as FSA.
    pose proof HB as HB'. bi_intro HB'. unfold Wf, shadow_addr in MU.
    assert (Hspc : 0 <= spc < 2 ^ 64) by lia.
    assert (HS1 : store_ok rsegs mc (wa (A + 8)) 8 = true)
      by (eapply wv_store_ok; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia | exact WM | lia | lia]).
    step. store_done.
    do 8 step.
    wst fr 8%nat. step. store_done.
    wst (fr + 8) 8%nat. step. store_done.
    wst (fr + 16) 8%nat. step. store_done.
    step. step.
    rewrite (unsigned_lit fr) by lia. rewrite rc_shr3.
    wst (fr / 8 + off + 4) 1%nat. step. store_done.
    wst (fr / 8 + off + 5) 1%nat. step. store_done.
    wst (fr / 8 + off + 6) 1%nat. step. store_done.
    wst (fr / 8 + off + 7) 1%nat. step. store_done.
    step.
    wst (fr / 8 + off) 1%nat. step. store_done.
    wst (fr / 8 + off + 1) 1%nat. step. store_done.
    wst (fr / 8 + off + 2) 1%nat. step. store_done.
    wst (fr / 8 + off + 3) 1%nat. step. store_done.
    eapply K; [exact HK|].
    split; [unfold Wf, shadow_addr; exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [eexists; eassumption | assumption].
  Qed.

  Lemma entry : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q (m0 : word -> option byte), m0 = m -> KB Q ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0 K.
    pose proof FP0 as FPm. unfold reac_box_model_block_W in FPm. pose proof STW0 as STW.
    unfold REAC_BOX_MODEL_BLOCK.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (MU : munch [(bv_unsigned sp - 4272, bv_unsigned sp)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    rewrite <- Hoff in CK.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (bv_unsigned sp - 160) _ ST0c ltac:(lia)) as [STa STb].
    clear ST0c.
    carve_frame 104%nat STb.
    step.
    assert (HS0 : store_ok rsegs m0 (wa (bv_unsigned sp + -160)) 8 = true).
    { eapply wv_store_ok; [ | apply wmono_refl | lia | lia]. intros i Hi.
      apply (stk_wv m0 (bv_unsigned sp - 160) (bv_unsigned sp + -104)); [exact STb | lia]. }
    step. store_done.
    do 13 step.
    step. step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160))) 18446744073709551584 = A)
      by (rewrite unsigned_lit, land_align32 by lia; rewrite HA; f_equal; f_equal; lia).
    rewrite EA.
    do 11 step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    (* the side-stack state at m1 *)
    pose proof (fl_fp [0%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HCL as HCL0. apply Forall_cons_iff in HCL0. destruct HCL0 as [(_ & h & flags & HH & HF & HFl & HFb) _].
    pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
    cbn [fp_tls app] in Hw0.
    repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof (stk_merge rsegs m1 _ _ _ STa STb ltac:(lia)) as STc.
    destruct (stk_split rsegs m1 _ A _ STc ltac:(lia)) as [STA _].
    pose proof HSM as HM. unfold asan_stack_malloc_0_contract, asan_stack_malloc_contract in HM. cbv zeta in HM.
    eapply evt_cut.
    { eapply HM with (lo := bv_unsigned sp - 4272) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
        (DB := DB) (k := k) (flags := flags); unfold ASAN_STACK_MALLOC_K; rewrite ?(unsigned_lit A) by lia.
      - rewrite unsigned_lit by lia. unfold fs_B. cbn. lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - exact (fl_asan_cells _ m m1 AC0 MU ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I])).
      - exact (shadow_rw_mono m m1 SR0 WM RM).
      - exact MI.
      - exact HT.
      - intros Hc. lia.
      - exact HTP.
      - exact HP.
      - exact H88.
      - exact H96.
      - exact HH.
      - exact HF.
      - exact HFl.
      - exact HFb.
      - exact STA.
      - lia.
      - lia.
      - intros a Ha. apply HAPP. lia.
      - cbn [disjoint_from].
        repeat split; try exact I;
          match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
            match goal with Hd : ly_dj _ _ lo hi |- _ => unfold ly_dj in Hd; lia end end. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E & WM2 & MI2 & ST2
                    & HP2 & (h2 & HH2) & ALT).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 547772)) with (Z_to_bv 64 547772) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit A) in ST2 by lia. unfold ASAN_STACK_MALLOC_K in *.
    unfold fs_hint in HH2. cbn [Z.of_nat] in HH2. rewrite Z.add_0_r in HH2.
    pose proof FPm as (DT' & TS' & C' & T' & DB' & k' & _ & _ & HPm & _).
    pose proof HPm as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    destruct ALT as [(Hall & Ex0 & MU2) | (i & Hi & Hpre & Hnth & FRM)].
    - (* the real-stack frame [A - 64, A) *)
      subst x0. rewrite (unsigned_lit A) in MU2 by lia. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      rewrite Z.add_0_r in MU2.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2). constructor; [|constructor; [|constructor]]; cbn [fst snd].
        - intros y Hy. apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - intros y Hy. apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf (A - 64) 0 0) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      destruct (rd8_le8 m2 (A - 8) ltac:(lia) ltac:(lia) ltac:(intros y Hy; apply (rd_of_stk _ _ _ ST2); lia))
        as (w56 & F56).
      clear MU MU2 WM WM2 RM RM2 FR STA STa STb STc MI.
      unfold Wf, shadow_addr in MU3.
      step. step. step. step.
      replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
      step. step.
      match goal with |- context [Z.land ?x 18446744073709551584] =>
        replace (Z.land x 18446744073709551584) with (A - 64)
          by (rewrite ?(unsigned_lit A), ?unsigned_lit by lia; rewrite land_align32 by lia;
              Z.div_mod_to_equations; lia) end.
      step. step.
      rewrite (unsigned_lit A) by lia.
      wst (A - 4096) 8%nat. step. store_done.
      step.
      rewrite (rc_lts_signed (A - 64) (A - 4096)) by lia.
      replace (A - 64 <? A - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step.
      eapply (fwords (A - 64) 0 (A - 64) 0 0 w56); [left; repeat split; lia | | exact K].
      split; [unfold Wf, shadow_addr; exact MU3|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|].
      replace (A - 64 + 56) with (A - 8) by lia. assumption.
    - (* the side-stack frame fs_frame FS 0 jj *)
      unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
      rewrite (unsigned_lit A), (unsigned_lit 64) in FRM by lia.
      replace (fs_B 0) with 64 in FRM by reflexivity.
      replace (fs_shadow_n 0 64) with 8 in FRM by reflexivity.
      destruct FRM as (Ex0 & Hm64 & _ & HFL & H24 & H56 & HSH & HADD & STF & APF & FSlo & FShi & GT & FRA' & DIS
                       & MU2).
      remember ((bv_unsigned h + i) mod fs_M 0) as jj eqn:Ejj.
      assert (Hjj : 0 <= jj < fs_M 0) by (subst jj; apply Z.mod_pos_bound; reflexivity).
      remember (fs_frame FS 0 jj) as fr eqn:Efr.
      subst x0. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2. rewrite Z.add_0_r in MU2.
      unfold ASAN_GT in GT. unfold FS_SIZE in FShi.
      assert (EFl : fs_flag FS 0 jj = FS + 4096 + jj) by (unfold fs_flag; cbn; lia).
      assert (EM0 : fs_M 0 = 16384) by reflexivity.
      rewrite EM0 in Hjj.
      assert (SHb : shadow_addr fr + 8 <= bv_unsigned sp - 4272)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2).
        repeat constructor; cbn [fst snd]; intros y Hy.
        - apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HFL). cbn. lia.
        - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ H56). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
        - apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf fr jj 1) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(rewrite EFl; cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      clear MU MU2 WM WM2 RM RM2 FR STA STa STb STc MI.
      step. step. step. step.
      rewrite (rc_neq0_64 fr) by lia. cbn [negb]. cbv iota.
      eapply (fwords fr fr A jj 1 (Z_to_bv 64 (fs_flag FS 0 jj))); [right; repeat split; lia | | exact K].
      split; [exact MU3|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|].
      replace (fr + 56) with (fr + 64 - 8) by lia. assumption.
  Qed.

  (* The runtime state the post names, carried across the body (asan_cells, shadow_rw, the window addressable, fp and
     the tls premise). *)
  Definition JR (m' : word -> option byte) : Prop :=
    asan_cells m' /\ shadow_rw m' /\ addressable m' (bv_unsigned sp - 4272) 4272 /\
    fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) /\
    reac_box_model_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp).

  Lemma JR_m : JR m.
  Proof.
    split; [exact AC0|]. split; [exact SR0|]. split; [exact AW0|]. split; [exact FP0 | exact TLS0].
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
    - exact (fl_shadow_rw W' m1 m2 SW MU WM SHo).
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

  Definition Q0 : machine_state -> Prop :=
    reac_box_model_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb.

  (* 0x86520: a0 = s5, the saved registers restored and the frame popped, ret. *)
  Lemma td_tail : forall (r : Z) (m' : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word) (spc fr f : Z),
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    rw_cells rsegs m' (bv_unsigned sp + -104) SAVES ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (bv_unsigned sp - 4272) (bv_unsigned sp) ->
    asan_cells m' -> shadow_rw m' -> addressable m' (bv_unsigned sp - 4272) 4272 ->
    fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    reac_box_model_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (if (p =? 0) || (o =? 0)
     then munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m m'
     else bytes_at rsegs m' o (synth row b nb) /\
          munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp); (o, o + 32)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m m') ->
    evt rsegs Q0
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86520) fc None m' (seg_rom rsegs)).
  Proof.
    intros r m' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 spc fr f
      Er FR WM MI ST AC SW AW FP TL POSTMU.
    subst r. pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp. unfold SAVES in FR.
    do 17 step.
    apply evt_done. unfold Q0, reac_box_model_block_post. cbv beta.
    do 14 eexists. exists m'. split; [reflexivity|].
    split; [exact POSTMU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact AC|]. split; [exact SW|]. split; [exact AW|]. split; [exact FP | exact TL].
  Qed.

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

  Lemma out_appinv : forall WA WB x, outside (WA ++ WB) x -> outside WA x /\ outside WB x.
  Proof.
    induction WA as [|[lo hi] WA IH]; intros WB x H; cbn [app outside] in *; [split; [exact I | exact H]|].
    destruct H as [H1 H2]. destruct (IH WB x H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
  Qed.

  (* The frame footprint Wf is contained in the post's write set W ++ X (used to carry JR across the body). *)
  Lemma wf_sub : forall fr f spc j n w56, FK fr f spc j n w56 ->
    sub_fp (Wf fr j n)
      (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS).
  Proof.
    intros fr f spc j n w56 HK x Hout.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _ & _ & _ & _ & _).
    pose proof HPl as (_ & P2 & _ & _ & _).
    assert (FSm8 : FS mod 8 = 0) by (clear -P2; Z.div_mod_to_equations; lia).
    clear HSM Hoff HA HS16 ST0 MI0 AC0 SR0 AW0 FP0 TLS0 Rp Rb Ro HP HN HO AP ANB AO AJ1 AJ2 NDJ HPl P2
      DT TS C T DB k HHM HAE.
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFM : fs_frame FS 0 (fs_M 0) = fs_frame FS 0 0 + 1048576).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    assert (EH : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (FR0m8 : fs_frame FS 0 0 mod 8 = 0) by (rewrite EFR0; clear -FSm8; Z.div_mod_to_equations; lia).
    assert (EM : fs_M 0 = 16384) by reflexivity.
    apply out_appinv in Hout. destruct Hout as [HoutW HoutX].
    unfold reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K in HoutW.
    cbn [outside] in HoutW. destruct HoutW as [Hwin _].
    unfold reac_box_model_block_X, fp_w in HoutX. cbn [flat_map app] in HoutX.
    apply out_appinv in HoutX. destruct HoutX as [Hfpw Hwsh].
    unfold fp_w1 in Hfpw. cbn [outside] in Hfpw.
    destruct Hfpw as (Hhint & Hflag & Hframe & Hfsh & _).
    cbn [outside] in Hwsh. destruct Hwsh as [Hwsh _].
    rewrite EH in Hhint. rewrite EFM in Hframe, Hfsh. rewrite EM in Hflag.
    unfold Wf. cbn [outside]. split; [exact Hwin|]. split; [exact Hhint|].
    split; [|split].
    - (* flag interval *)
      destruct HK as [(_ & _ & _ & _ & En) | (Hj & _ & _ & _ & _ & En)].
      + subst n. lia.
      + subst n. rewrite EM in Hj.
        assert (EFl : fs_flag FS 0 j = fs_flag FS 0 0 + j) by (unfold fs_flag, fs_M; cbn [Z.of_nat]; lia).
        rewrite EFl. clear -Hflag Hj. lia.
    - (* frame interval *)
      destruct HK as [(_ & Efr & _ & _ & _) | (Hj & Efr & _ & _ & _ & _)].
      + subst fr. clear -Hwin HAlo HAhi. lia.
      + subst fr. rewrite EM in Hj.
        assert (EFj : fs_frame FS 0 j = fs_frame FS 0 0 + 64 * j) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
        rewrite EFj. clear -Hframe Hj. lia.
    - (* frame shadow interval *) split; [|exact I].
      destruct HK as [(_ & Efr & _ & _ & _) | (Hj & Efr & _ & _ & _ & _)].
      + subst fr. intros [L1 L2].
        assert (Am8 : (A - 64) mod 8 = 0) by (clear -HA32; Z.div_mod_to_equations; lia).
        assert (E1 : shadow_addr A = shadow_addr (A - 64) + 8).
        { pose proof (sh_add8 (A - 64) 8 Am8) as H. replace (A - 64 + 8 * 8) with A in H by lia. lia. }
        assert (G1 : shadow_addr (bv_unsigned sp - 4272) <= shadow_addr (A - 64))
          by (apply acl_sh_ge; clear -HAlo; lia).
        assert (G2 : shadow_addr A <= shadow_addr (bv_unsigned sp))
          by (apply acl_sh_ge; clear -HAhi; lia).
        rewrite <- E1 in L2. apply Hwsh.
        exact (conj (Z.le_trans _ _ _ G1 L1) (Z.lt_le_trans _ _ _ L2 G2)).
      + subst fr. intros [L1 L2]. rewrite EM in Hj.
        assert (EFj : fs_frame FS 0 j = fs_frame FS 0 0 + 64 * j) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
        assert (E1 : shadow_addr (fs_frame FS 0 0 + 64 * j) = shadow_addr (fs_frame FS 0 0) + 8 * j).
        { pose proof (sh_add8 (fs_frame FS 0 0) (8 * j) FR0m8) as H.
          replace (fs_frame FS 0 0 + 8 * (8 * j)) with (fs_frame FS 0 0 + 64 * j) in H by lia. lia. }
        assert (E3 : shadow_addr (fs_frame FS 0 0 + 1048576) = shadow_addr (fs_frame FS 0 0) + 131072).
        { pose proof (sh_add8 (fs_frame FS 0 0) 131072 FR0m8) as H.
          replace (fs_frame FS 0 0 + 8 * 131072) with (fs_frame FS 0 0 + 1048576) in H by lia. lia. }
        rewrite EFj, E1 in L1, L2.
        assert (Lo : shadow_addr (fs_frame FS 0 0) <= shadow_addr (fs_frame FS 0 0) + 8 * j) by (clear -Hj; lia).
        assert (Hi : shadow_addr (fs_frame FS 0 0) + 8 * j + 8 <= shadow_addr (fs_frame FS 0 0) + 131072)
          by (clear -Hj; lia).
        apply Hfsh. rewrite E3.
        exact (conj (Z.le_trans _ _ _ Lo L1) (Z.lt_le_trans _ _ _ L2 Hi)).
  Qed.

  (* The whole body's write set from m: the frame pieces (Wf) and, when the box is written, o. *)
  Definition EBW (fr j n : Z) : list ivl :=
    Wf fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)]).

  Lemma ebw_sub : forall fr f spc j n w56, FK fr f spc j n w56 ->
    sub_fp (EBW fr j n)
      (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS).
  Proof.
    intros fr f spc j n w56 HK x Hout. unfold EBW.
    apply fl_out_app; [exact (wf_sub fr f spc j n w56 HK x Hout)|].
    destruct ((p =? 0) || (o =? 0)) eqn:E; [exact I|].
    apply orb_false_iff in E. destruct E as [_ Eo].
    apply out_appinv in Hout. destruct Hout as [HoutW _].
    unfold reac_box_model_block_W in HoutW. rewrite Eo in HoutW. cbn [outside] in HoutW.
    cbn [outside]. destruct HoutW as [_ Ho]. exact Ho.
  Qed.

  (* The runtime-state facts the post needs (asan_cells, shadow_rw, fp, tls), rebuilt from the body munch and the
     hint and flags read back at the final memory (addressable is handled separately in epi). *)
  Lemma epi_state : forall fr f spc j n w56 (m'' : word -> option byte) (h'' : word) (flags'' : list byte),
    FK fr f spc j n w56 ->
    munch (EBW fr j n) m m'' -> wmono rsegs m m'' -> rd_mono m m'' ->
    bytes_at rsegs m'' (fs_hint FS 0) (le8 h'') ->
    bytes_at rsegs m'' (fs_flag FS 0 0) flags'' -> Z.of_nat (length flags'') = fs_M 0 ->
    Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'' ->
    asan_cells m'' /\ shadow_rw m'' /\
    fp [0%nat] m'' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) /\
    reac_box_model_block_tls m'' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Proof.
    intros fr f spc j n w56 m'' h'' flags'' HK MU WM RM Hint Hflags Hlen HF01.
    pose proof (ebw_sub fr f spc j n w56 HK) as SUB.
    split; [exact (br_ac (EBW fr j n) m'' MU SUB)|].
    split; [exact (shadow_rw_mono m m'' SR0 WM RM)|].
    split.
    - exact (br_fp (EBW fr j n) m'' h'' flags'' MU WM RM SUB Hint Hflags Hlen HF01).
    - unfold reac_box_model_block_tls, REAC_BOX_MODEL_BLOCK_K. intros DT TS C T DB k HT.
      unfold reac_box_model_block_X in SUB.
      exact (acl_tls_ret [0%nat] m m'' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
               (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o)
               [(shadow_addr (bv_unsigned sp - 4272), shadow_addr (bv_unsigned sp))] (EBW fr j n)
               FP0 TLS0 MU SUB DT TS C T DB k HT).
  Qed.

  (* The window is addressable at a memory whose window shadow bytes are all 0. *)
  Lemma epi_addr : forall (m'' : word -> option byte),
    (forall i, 0 <= i < 4272 ->
       mrd rsegs m'' (wa (shadow_addr (bv_unsigned sp - 4272 + i))) = Some (Z_to_bv 8 0)) ->
    addressable m'' (bv_unsigned sp - 4272) 4272.
  Proof.
    intros m'' HSH. pose proof HHM as HHM'. pose proof HAE as HAE'.
    unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct AW0 as (A0 & An & Ae & HAd). split; [exact A0|]. split; [exact An|]. split; [exact Ae|].
    intros i Hi. destruct (HAd i Hi) as (Hap & _). unfold addr_byte. split; [exact Hap|].
    exists (Z_to_bv 8 0). split; [exact (HSH i Hi)|].
    unfold shadow_ok. left. reflexivity.
  Qed.

  (* The shadow byte of a window byte apart from the real-stack frame is outside the body's write set EBW. *)
  Lemma win_sh_out : forall fr f spc j n w56 x, FK fr f spc j n w56 ->
    bv_unsigned sp - 4272 <= x < bv_unsigned sp -> ~ (fr <= x < fr + 64) ->
    outside (EBW fr j n) (shadow_addr x).
  Proof.
    intros fr f spc j n w56 x HK Hxw Hxfr.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Hapx : app_mem x).
    { pose proof (acl_app_in m (bv_unsigned sp - 4272) 4272 (x - (bv_unsigned sp - 4272)) AW0 ltac:(lia)) as H.
      replace (bv_unsigned sp - 4272 + (x - (bv_unsigned sp - 4272))) with x in H by lia. exact H. }
    pose proof (rt_app_shadow x Hapx) as Hsh.
    assert (Hylo : LOWMEM_END <= shadow_addr x).
    { clear -Hsh. unfold in_shadow in Hsh. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    assert (Hyhi : shadow_addr x < HIGHMEM_BEG).
    { clear -Hsh. unfold in_shadow in Hsh. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
    unfold LOWMEM_END in Hylo. unfold HIGHMEM_BEG in Hyhi.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (Hn : 0 <= n <= 1) by (destruct HK as [(_ & _ & _ & _ & En) | (_ & _ & _ & _ & _ & En)]; lia).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _ & _ & _ & _ & _).
    pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4.
    pose proof (P4 FS ltac:(lia)) as AFS. pose proof (P4 (FS + 7) ltac:(lia)) as AFS7.
    assert (Efl : fs_flag FS 0 j = FS + 4096 + j) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
    assert (Aflag : app_mem (fs_flag FS 0 j)).
    { rewrite Efl. apply P4. destruct HK as [(_ & _ & _ & Ej & _) | (Hj & _)].
      - subst j; lia.
      - unfold fs_M in Hj; cbn [Z.of_nat] in Hj; change (2 ^ (14 - 0)) with 16384 in Hj; lia. }
    pose proof (FAP 0%Z ltac:(lia)) as AFr. rewrite Z.add_0_r in AFr.
    pose proof (FAP 63 ltac:(lia)) as AFr63.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AFS, AFS7, Aflag, AFr, AFr63.
    unfold EBW, Wf. apply fl_out_app.
    - cbn [outside]. split; [clear -Hyhi HHM'; lia|].
      split; [clear -Hylo Hyhi AFS AFS7; lia|].
      split; [clear -Hylo Hyhi Aflag Hn; lia|].
      split; [clear -Hylo Hyhi AFr AFr63; lia|].
      split; [|exact I].
      pose proof (acl_win_sh x fr (fr + 64) FR8 Hxfr) as HW.
      pose proof (sh_add8 fr 8 FR8) as E. replace (fr + 8 * 8) with (fr + 64) in E by lia.
      rewrite E in HW. exact HW.
    - destruct ((p =? 0) || (o =? 0)) eqn:Eo; [exact I|].
      apply orb_false_iff in Eo. destruct Eo as [_ Eo].
      apply Z.eqb_neq in Eo.
      destruct (AO Eo) as (AOa & _ & _).
      pose proof (acl_app_in m o 32 0 AOa ltac:(lia)) as Ao0. rewrite Z.add_0_r in Ao0.
      pose proof (acl_app_in m o 32 31 AOa ltac:(lia)) as Ao31.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ao0, Ao31.
      cbn [outside]. split; [clear -Hylo Hyhi Ao0 Ao31; lia | exact I].
  Qed.

  (* Every window shadow byte reads 0 at the final memory (release zeroed the real-stack frame's shadow). *)
  Lemma epi_shadow0 : forall fr f spc j n w56 (m'' : word -> option byte),
    FK fr f spc j n w56 ->
    munch (EBW fr j n) m m'' ->
    (f = 0 -> forall x, A - 64 <= x < A -> mrd rsegs m'' (wa (shadow_addr x)) = Some (Z_to_bv 8 0)) ->
    forall i, 0 <= i < 4272 ->
      mrd rsegs m'' (wa (shadow_addr (bv_unsigned sp - 4272 + i))) = Some (Z_to_bv 8 0).
  Proof.
    intros fr f spc j n w56 m'' HK MU FR0sh i Hi.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    set (x := bv_unsigned sp - 4272 + i).
    assert (Hax : app_mem x) by (exact (acl_app_in m (bv_unsigned sp - 4272) 4272 i AW0 Hi)).
    assert (Hxb : 0 <= shadow_addr x < 2 ^ 64)
      by (pose proof (rt_shadow_bound (shadow_addr x) (rt_app_shadow x Hax)) as HB; clear -HB; lia).
    assert (DEC : (f = 0 /\ A - 64 <= x < A) \/ ~ (fr <= x < fr + 64)).
    { destruct HK as [(Ef & Efr & _) | (Hj & Efr & Ef & _)].
      - destruct (Z_le_dec (A - 64) x) as [D1|D1]; destruct (Z_lt_dec x A) as [D2|D2];
          [left; split; [exact Ef | lia] | right; subst fr; lia | right; subst fr; lia | right; subst fr; lia].
      - right. subst fr.
        pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & HFS & _). unfold FS_SIZE in HFS.
        unfold fs_frame, fs_B, fs_M in *; cbn [Z.of_nat] in *.
        change (2 ^ (14 - 0)) with 16384 in Hj. change (2 ^ 0) with 1 in *.
        unfold x; clear -HFS Hj Hi; lia. }
    destruct DEC as [[Ef Hxf] | Hnf].
    - exact (FR0sh Ef x Hxf).
    - assert (OUT : outside (EBW fr j n) (shadow_addr x))
        by (apply (win_sh_out fr f spc j n w56); [exact HK | unfold x; lia | exact Hnf]).
      pose proof (MU (wa (shadow_addr x))) as Heq.
      rewrite wa_unsigned in Heq by exact Hxb. specialize (Heq OUT).
      replace (mrd rsegs m'' (wa (shadow_addr x))) with (mrd rsegs m (wa (shadow_addr x)))
        by (unfold mrd; rewrite Heq; reflexivity).
      unfold x. exact (win_shadow0 i Hi).
  Qed.

  (* The class-0 flag array read back at the final memory: all 0/1 (the release cleared the frame's flag to 0). *)
  Lemma epi_flags : forall fr f spc j n w56 (m'' : word -> option byte),
    FK fr f spc j n w56 ->
    munch (EBW fr j n) m m'' ->
    (n = 1 -> mrd rsegs m'' (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
    exists flags'', bytes_at rsegs m'' (fs_flag FS 0 0) flags'' /\
      Z.of_nat (length flags'') = fs_M 0 /\
      Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags''.
  Proof.
    intros fr f spc j n w56 m'' HK MU Hrel.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DT & TS & C & T & DB & k0 & HT & HTP & HPl & H88 & H96 & HCL & HFS & HApp & HWd & HDd).
    unfold FS_SIZE in HFS. pose proof HPl as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in P4.
    apply Forall_inv in HCL. destruct HCL as (_ & hm & flags_m & _ & Hflm & Hlen & Hforall).
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (Ef0 : fs_flag FS 0 0 = FS + 4096) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
    assert (Efl : fs_flag FS 0 j = FS + 4096 + j) by
      (unfold fs_flag; cbn [Z.of_nat];
       replace (2 ^ (15 - 0)) with 32768 by reflexivity; replace (2 ^ 15) with 32768 by reflexivity; lia).
    assert (EM : fs_M 0 = 16384) by reflexivity.
    destruct (fk_facts fr f spc j n w56 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (Hn : 0 <= n <= 1) by (destruct HK as [(_ & _ & _ & _ & En) | (_ & _ & _ & _ & _ & En)]; lia).
    (* flag positions apart from position j are outside EBW *)
    assert (FOUT : forall x, fs_flag FS 0 0 <= x < fs_flag FS 0 0 + fs_M 0 ->
              ~ (fs_flag FS 0 j <= x < fs_flag FS 0 j + n) -> outside (EBW fr j n) x).
    { intros x Hx Hxj. rewrite Ef0, EM in Hx.
      assert (Hxapp : app_mem x) by (apply P4; lia).
      assert (OW : outside (reac_box_model_block_W o (bv_unsigned sp)) x).
      { apply (fl_dj_out (reac_box_model_block_W o (bv_unsigned sp))
                 (fp_tls (bv_unsigned tp) DT TS C T DB k0 ++ [(FS, fs_frame FS 0 0)]) FS (fs_frame FS 0 0) x HWd).
        - apply in_or_app; right; left; reflexivity.
        - rewrite EFR0; lia. }
      unfold reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K in OW. cbn [outside] in OW. destruct OW as [OWwin OWo].
      unfold EBW, Wf. apply fl_out_app.
      - cbn [outside]. split; [exact OWwin|].
        split; [clear -Hx; lia|].
        split; [exact Hxj|].
        split; [clear -Hx FRlo; lia|].
        split; [|exact I].
        pose proof (FAP 0%Z ltac:(lia)) as AFr. rewrite Z.add_0_r in AFr.
        pose proof (rt_app_shadow fr AFr) as Hfrsh.
        pose proof (FAP 56 ltac:(lia)) as AFr56.
        pose proof (rt_app_shadow (fr + 56) AFr56) as Hfrsh2.
        pose proof (sh_add8 fr 7 FR8) as E7. replace (fr + 8 * 7) with (fr + 56) in E7 by lia.
        rewrite E7 in Hfrsh2.
        assert (Hfrlo : LOWMEM_END <= shadow_addr fr)
          by (clear -Hfrsh; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia).
        assert (Hfrhi : shadow_addr fr + 7 < HIGHMEM_BEG)
          by (clear -Hfrsh2; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia).
        unfold LOWMEM_END in Hfrlo. unfold HIGHMEM_BEG in Hfrhi.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxapp.
        clear -Hfrlo Hfrhi Hxapp. lia.
      - destruct ((p =? 0) || (o =? 0)) eqn:Eq; [exact I|].
        apply orb_false_iff in Eq. destruct Eq as [_ Eq]. rewrite Eq in OWo. exact OWo. }
    assert (MRDeq : forall x, fs_flag FS 0 0 <= x < fs_flag FS 0 0 + fs_M 0 ->
              ~ (fs_flag FS 0 j <= x < fs_flag FS 0 j + n) -> mrd rsegs m'' (wa x) = mrd rsegs m (wa x)).
    { intros x Hx Hxj. pose proof (MU (wa x)) as Heq.
      rewrite wa_unsigned in Heq by (rewrite Ef0, EM in Hx; clear -Hx P1 HFS HAE'; lia).
      specialize (Heq (FOUT x Hx Hxj)). unfold mrd. rewrite Heq. reflexivity. }
    assert (Hlenn : length flags_m = Z.to_nat (fs_M 0)) by (rewrite <- Hlen; rewrite Nat2Z.id; reflexivity).
    rewrite EM in Hlenn.
    destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En)].
    - (* real-stack: n = 0, flag array unchanged *)
      subst n. exists flags_m. split; [|split; [exact Hlen | exact Hforall]].
      apply (bytes_keep m m'' _ flags_m Hflm). intros x Hx. rewrite Hlen in Hx.
      apply MRDeq; [exact Hx | clear; lia].
    - (* side-stack: n = 1, position j cleared to 0 *)
      subst n.
      assert (Hjlt : (Z.to_nat j < length flags_m)%nat).
      { rewrite Hlenn. unfold fs_M in Hj; cbn [Z.of_nat] in Hj.
        change (2 ^ (14 - 0)) with 16384 in Hj. lia. }
      exists (upd_bytes flags_m (Z.to_nat j) [Z_to_bv 8 0]).
      destruct Hflm as (Ha & Hl & Hh).
      split; [|split].
      + split; [exact Ha|]. split; [rewrite upd_bytes_length by (cbn [length]; lia); exact Hl|].
        intros k Hk. rewrite upd_bytes_length in Hk by (cbn [length]; lia).
        rewrite upd_bytes_nth by (cbn [length]; lia).
        change (@length byte [Z_to_bv 8 0]) with 1%nat.
        destruct ((Z.to_nat j <=? k)%nat && (k <? Z.to_nat j + 1)%nat)%bool eqn:Ec.
        * apply andb_true_iff in Ec. destruct Ec as [Ec1 Ec2].
          apply Nat.leb_le in Ec1. apply Nat.ltb_lt in Ec2.
          assert (Ekj : k = Z.to_nat j) by lia. subst k. rewrite Nat.sub_diag. cbn [nth_error].
          replace (fs_flag FS 0 0 + Z.of_nat (Z.to_nat j)) with (fs_flag FS 0 j)
            by (rewrite Z2Nat.id by lia; rewrite Ef0, Efl; lia).
          exact (Hrel eq_refl).
        * rewrite <- (Hh k Hk). apply MRDeq.
          { rewrite Ef0, EM. rewrite Hlenn in Hk. clear -Hk. lia. }
          { rewrite Ef0, Efl. apply andb_false_iff in Ec.
            assert (k <> Z.to_nat j).
            { destruct Ec as [E|E]; [apply Nat.leb_nle in E | apply Nat.ltb_nlt in E]; lia. }
            assert (Z.of_nat k <> j) by (rewrite <- (Z2Nat.id j) by lia; clear -H; lia).
            clear -H0. lia. }
      + rewrite upd_bytes_length by (cbn [length]; lia). exact Hlen.
      + apply Forall_forall. intros y Hy. apply In_nth_error in Hy. destruct Hy as [i Hi].
        assert (Hib : (i < length flags_m)%nat).
        { rewrite <- (upd_bytes_length flags_m (Z.to_nat j) [Z_to_bv 8 0]) by (cbn [length]; lia).
          apply nth_error_Some. rewrite Hi; discriminate. }
        rewrite upd_bytes_nth in Hi by (cbn [length]; lia).
        change (@length byte [Z_to_bv 8 0]) with 1%nat in Hi.
        destruct ((Z.to_nat j <=? i)%nat && (i <? Z.to_nat j + 1)%nat)%bool.
        * destruct (i - Z.to_nat j)%nat as [|nn]; cbn [nth_error] in Hi;
            [injection Hi as <-; left; reflexivity | destruct nn; discriminate].
        * rewrite Forall_forall in Hforall. apply Hforall. apply nth_error_In in Hi. exact Hi.
  Qed.
  (* --- single-byte read-after-write (for the inline shadow/flag release stores) --- *)
  Lemma mrd_w1 : forall (m0 : word -> option byte) (a : Z) (v : byte) (y : Z),
    0 <= a < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
    mrd rsegs (write_to_mem m0 (wa a) [v]) (wa y) =
      (if y =? a then Some v else mrd rsegs m0 (wa y)).
  Proof.
    intros m0 a v y Ha Hy. unfold mrd. rewrite write_to_mem_spec by (cbn [length]; lia).
    rewrite !wa_unsigned by lia.
    destruct (Z.eqb_spec y a) as [->|Hne].
    - replace ((a <=? a) && (a <? a + Z.of_nat (length [v])))%bool with true.
      2:{ symmetry. apply andb_true_iff. split; [apply Z.leb_le; lia | apply Z.ltb_lt; cbn [length]; lia]. }
      rewrite Z.sub_diag. reflexivity.
    - replace ((a <=? y) && (y <? a + Z.of_nat (length [v])))%bool with false.
      2:{ symmetry. apply andb_false_iff.
          destruct (Z_le_dec a y) as [L|L]; [right; apply Z.ltb_ge; cbn [length]; lia | left; apply Z.leb_gt; lia]. }
      reflexivity.
  Qed.

  (* A read apart from an n-byte store sees the old memory. *)
  Lemma mrd_wn_ne : forall (m0 : word -> option byte) (a : Z) (bs : list byte) (y : Z),
    0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
    (y < a \/ a + Z.of_nat (length bs) <= y) ->
    mrd rsegs (write_to_mem m0 (wa a) bs) (wa y) = mrd rsegs m0 (wa y).
  Proof.
    intros m0 a bs y Ha Hl Hy Hd. unfold mrd. rewrite write_to_mem_spec by lia.
    rewrite !wa_unsigned by lia.
    replace ((a <=? y) && (y <? a + Z.of_nat (length bs)))%bool with false
      by (symmetry; apply andb_false_iff;
          destruct Hd as [D|D]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
    reflexivity.
  Qed.

  (* bytes_at survives a write whose footprint is outside the byte range. *)
  Lemma bytes_keep_out : forall (W : list ivl) (m1 m2 : word -> option byte) (AA : Z) (bs : list byte),
    bytes_at rsegs m1 AA bs -> munch W m1 m2 ->
    (forall x, AA <= x < AA + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m2 AA bs.
  Proof.
    intros W m1 m2 AA bs H MU HOut. pose proof H as (HbA & HbL & _).
    apply (bytes_keep m1 m2 AA bs H). intros x Hx.
    unfold mrd. rewrite (MU (wa x)); [reflexivity|]. rewrite wa_unsigned by lia. apply HOut; lia.
  Qed.

  (* The body-end invariant at 0x864c0: the whole-body munch, the carried runtime facts, the saved registers, the
     side-stack hint word, the frame's flag-address word (fr + 56), and the box result when it is written. *)
  Definition EB (fr f j n : Z) (w56 : word) (mc : word -> option byte) : Prop :=
    munch (EBW fr j n) m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (bv_unsigned sp + -104) SAVES /\
    (exists h, bytes_at rsegs mc FS (le8 h)) /\
    bytes_at rsegs mc (fr + 56) (le8 w56) /\
    (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)).

  Lemma inside_appl : forall W W' a n, inside W a n -> inside (W ++ W') a n.
  Proof.
    induction W as [|[lo hi] W IH]; intros W' a n H; cbn [app inside] in *; [contradiction|].
    destruct H as [H|H]; [left; exact H | right; apply IH; exact H].
  Qed.

  Lemma zeqb_addcancel : forall a u v, (a + u =? a + v) = (u =? v).
  Proof.
    intros a u v. destruct (Z.eqb_spec u v) as [->|H];
      [apply Z.eqb_eq; reflexivity | apply Z.eqb_neq; lia].
  Qed.

  (* wf_sub without the output interval: the frame footprint sits in the window plus the asan write set. *)
  Lemma wf_sub0 : forall fr f spc j n w56, FK fr f spc j n w56 ->
    sub_fp (Wf fr j n)
      ([(bv_unsigned sp - 4272, bv_unsigned sp)] ++ reac_box_model_block_X (bv_unsigned sp) FS).
  Proof.
    intros fr f spc j n w56 HK x Hout.
    pose proof HA1 as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HPl & _ & _ & _ & _ & _).
    pose proof HPl as (_ & P2 & _ & _ & _).
    assert (FSm8 : FS mod 8 = 0) by (clear -P2; Z.div_mod_to_equations; lia).
    clear HSM Hoff HA HS16 ST0 MI0 AC0 SR0 AW0 FP0 TLS0 Rp Rb Ro HP HN HO AP ANB AO AJ1 AJ2 NDJ HPl P2
      DT TS C T DB k HHM HAE.
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFM : fs_frame FS 0 (fs_M 0) = fs_frame FS 0 0 + 1048576).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    assert (EH : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (FR0m8 : fs_frame FS 0 0 mod 8 = 0) by (rewrite EFR0; clear -FSm8; Z.div_mod_to_equations; lia).
    assert (EM : fs_M 0 = 16384) by reflexivity.
    apply out_appinv in Hout. destruct Hout as [HoutW HoutX].
    cbn [outside] in HoutW. destruct HoutW as [Hwin _].
    unfold reac_box_model_block_X, fp_w in HoutX. cbn [flat_map app] in HoutX.
    apply out_appinv in HoutX. destruct HoutX as [Hfpw Hwsh].
    unfold fp_w1 in Hfpw. cbn [outside] in Hfpw.
    destruct Hfpw as (Hhint & Hflag & Hframe & Hfsh & _).
    cbn [outside] in Hwsh. destruct Hwsh as [Hwsh _].
    rewrite EH in Hhint. rewrite EFM in Hframe, Hfsh. rewrite EM in Hflag.
    unfold Wf. cbn [outside]. split; [exact Hwin|]. split; [exact Hhint|].
    split; [|split].
    - destruct HK as [(_ & _ & _ & _ & En) | (Hj & _ & _ & _ & _ & En)].
      + subst n. lia.
      + subst n. rewrite EM in Hj.
        assert (EFl : fs_flag FS 0 j = fs_flag FS 0 0 + j) by (unfold fs_flag, fs_M; cbn [Z.of_nat]; lia).
        rewrite EFl. clear -Hflag Hj. lia.
    - destruct HK as [(_ & Efr & _ & _ & _) | (Hj & Efr & _ & _ & _ & _)].
      + subst fr. clear -Hwin HAlo HAhi. lia.
      + subst fr. rewrite EM in Hj.
        assert (EFj : fs_frame FS 0 j = fs_frame FS 0 0 + 64 * j) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
        rewrite EFj. clear -Hframe Hj. lia.
    - split; [|exact I].
      destruct HK as [(_ & Efr & _ & _ & _) | (Hj & Efr & _ & _ & _ & _)].
      + subst fr. intros [L1 L2].
        assert (Am8 : (A - 64) mod 8 = 0) by (clear -HA32; Z.div_mod_to_equations; lia).
        assert (E1 : shadow_addr A = shadow_addr (A - 64) + 8).
        { pose proof (sh_add8 (A - 64) 8 Am8) as H. replace (A - 64 + 8 * 8) with A in H by lia. lia. }
        assert (G1 : shadow_addr (bv_unsigned sp - 4272) <= shadow_addr (A - 64))
          by (apply acl_sh_ge; clear -HAlo; lia).
        assert (G2 : shadow_addr A <= shadow_addr (bv_unsigned sp))
          by (apply acl_sh_ge; clear -HAhi; lia).
        rewrite <- E1 in L2. apply Hwsh.
        exact (conj (Z.le_trans _ _ _ G1 L1) (Z.lt_le_trans _ _ _ L2 G2)).
      + subst fr. intros [L1 L2]. rewrite EM in Hj.
        assert (EFj : fs_frame FS 0 j = fs_frame FS 0 0 + 64 * j) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
        assert (E1 : shadow_addr (fs_frame FS 0 0 + 64 * j) = shadow_addr (fs_frame FS 0 0) + 8 * j).
        { pose proof (sh_add8 (fs_frame FS 0 0) (8 * j) FR0m8) as H.
          replace (fs_frame FS 0 0 + 8 * (8 * j)) with (fs_frame FS 0 0 + 64 * j) in H by lia. lia. }
        assert (E3 : shadow_addr (fs_frame FS 0 0 + 1048576) = shadow_addr (fs_frame FS 0 0) + 131072).
        { pose proof (sh_add8 (fs_frame FS 0 0) 131072 FR0m8) as H.
          replace (fs_frame FS 0 0 + 8 * 131072) with (fs_frame FS 0 0 + 1048576) in H by lia. lia. }
        rewrite EFj, E1 in L1, L2.
        assert (Lo : shadow_addr (fs_frame FS 0 0) <= shadow_addr (fs_frame FS 0 0) + 8 * j) by (clear -Hj; lia).
        assert (Hi : shadow_addr (fs_frame FS 0 0) + 8 * j + 8 <= shadow_addr (fs_frame FS 0 0) + 131072)
          by (clear -Hj; lia).
        apply Hfsh. rewrite E3.
        exact (conj (Z.le_trans _ _ _ Lo L1) (Z.lt_le_trans _ _ _ L2 Hi)).
  Qed.

  (* The body write set sits in the post footprint (window, or window+output, plus the asan write set). *)
  Lemma ebw_sub0 : forall fr f spc j n w56, FK fr f spc j n w56 ->
    sub_fp (EBW fr j n)
      ((if (p =? 0) || (o =? 0)
        then [(bv_unsigned sp - 4272, bv_unsigned sp)]
        else [(bv_unsigned sp - 4272, bv_unsigned sp); (o, o + 32)])
       ++ reac_box_model_block_X (bv_unsigned sp) FS).
  Proof.
    intros fr f spc j n w56 HK. destruct ((p =? 0) || (o =? 0)) eqn:Ebox.
    - unfold EBW. rewrite Ebox. rewrite app_nil_r. apply (wf_sub0 fr f spc j n w56 HK).
    - pose proof (ebw_sub fr f spc j n w56 HK) as H.
      unfold reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K in H.
      apply orb_false_iff in Ebox. destruct Ebox as [_ Eo]. rewrite Eo in H. exact H.
  Qed.

  (* Normalize a just-stored address to wa-form (as store_done's first step). *)
  Ltac norm_store :=
    lazymatch goal with
    | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
        let E := addr_expr a in
        lazymatch a with
        | wa _ => idtac
        | Z_to_bv 64 _ => change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs)
        | _ => replace (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs) by (f_equal; addr_eq_tac)
        end
    end.

  (* After a bare store step (write_to_mem left visible, wa-normalized), carry the four body facts across it. *)
  Ltac estep_upd :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?pm (wa ?A0) ?bb) _) =>
        (match goal with WM : wmono rsegs ?m0 pm |- _ => apply (wmono_write rsegs m0 pm (wa A0) bb) in WM end);
        (match goal with RM : rd_mono ?m0 pm |- _ => apply (rd_mono_write m0 pm (wa A0) bb) in RM end);
        (match goal with MU : munch ?W ?m0 pm |- _ =>
           apply (munch_write W m0 pm A0 bb) in MU;
             [ | lia | simpl_sizes; lia
             | unfold EBW, Wf, shadow_addr; rewrite ?Hoff; apply inside_appl; cbn [inside]; simpl_sizes; lia ] end);
        (match goal with MI : mem_inv rsegs pm, HS : store_ok rsegs pm ?aw _ |- _ =>
           apply (mem_inv_store rsegs pm (wa A0) bb) in MI;
             [ | first [ exact HS | rewrite ?length_le8, ?length_le1; cbn [length]; exact HS ] ] end)
    end.

  (* One inline shadow-zero store at address a. *)
  Ltac shst a :=
    wst a 1%nat; step; norm_store;
    (lazymatch goal with
     | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa _) ?l) _) => try (replace l with [Z_to_bv 8 0] by reflexivity)
     end); estep_upd.

  (* The 0x86520 restore/return, from the body facts carried to the final memory. *)
  Lemma epi_close : forall (fr f spc j n : Z) (w56 : word) (mfin : word -> option byte) (hfin : word) (r : Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31 : word),
    FK fr f spc j n w56 ->
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    munch (EBW fr j n) m mfin -> wmono rsegs m mfin -> rd_mono m mfin -> mem_inv rsegs mfin ->
    rw_cells rsegs mfin (bv_unsigned sp + -104) SAVES ->
    bytes_at rsegs mfin (fs_hint FS 0) (le8 hfin) ->
    (f = 0 -> forall x, A - 64 <= x < A -> mrd rsegs mfin (wa (shadow_addr x)) = Some (Z_to_bv 8 0)) ->
    (n = 1 -> mrd rsegs mfin (wa (fs_flag FS 0 j)) = Some (Z_to_bv 8 0)) ->
    (if (p =? 0) || (o =? 0)
     then munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m mfin
     else bytes_at rsegs mfin o (synth row b nb) /\
          munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp); (o, o + 32)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m mfin) ->
    evt rsegs Q0
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86520) fc None mfin (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mfin hfin r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x26 x27 x28 x29 x30 x31
      HK Hr MUf WMf RMf MIf SVf HHf SHRB FLRB POSTMU.
    destruct (epi_flags fr f spc j n w56 mfin HK MUf FLRB) as (flags'' & Hfl & Hflen & Hf01).
    pose proof (epi_state fr f spc j n w56 mfin hfin flags'' HK MUf WMf RMf HHf Hfl Hflen Hf01)
      as (ACm & SWm & FPm & TLm).
    eapply td_tail.
    - exact Hr.
    - exact SVf.
    - exact WMf.
    - exact MIf.
    - exact (stk_mono m mfin _ _ ST0 WMf RMf).
    - exact ACm.
    - exact SWm.
    - apply epi_addr. exact (epi_shadow0 fr f spc j n w56 mfin HK MUf SHRB).
    - exact FPm.
    - exact TLm.
    - exact POSTMU.
  Qed.


End Main.
