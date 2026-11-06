(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth
  RcSynthLib RcLay RcLayLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c reac_box_model_block_c ctrl_lay_block_c.
Import ListNotations.
Open Scope Z_scope.

(* ctrl_lay_block, image A (asan, entry 0x855f4): ctrl_lay_block_holds (the contract of ctrl_lay_block_c.v) from the
   contracts of reac_box_model_block, __asan_stack_malloc_1 and its inline release, __asan_memset and __asan_memcpy.
   The plain proof (lib/Prog/ctrl_lay_block.v) with the ASan frame of this build: the class-1 frame request (side
   frame or real-stack fallback with the probe), the frame words and their shadow, the shadow check before each
   instrumented load and store, and the frame release. The generic infrastructure follows reac_box_model_block.v and
   reac_ctrl_classify_box_frame.v. *)

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

(* Existence of a byte string for a range that is readable everywhere (ported from asan_memcpy.v). *)
Lemma lay_bytes_exist : forall (mm : word -> option byte) (k : nat) (A : Z), 0 <= A -> A + Z.of_nat k <= 2^64 ->
  (forall j, 0 <= j < Z.of_nat k -> exists b, mrd rsegs mm (wa (A + j)) = Some b) ->
  exists bs, length bs = k /\ bytes_at rsegs mm A bs.
Proof.
  intros mm k. induction k as [|k IH]; intros A H0 H1 H.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as (bs & L & B).
    { intros j Hj. replace (A + 1 + j) with (A + (j + 1)) by lia. apply H. lia. }
    exists (b :: bs). split; [cbn; lia|]. destruct B as (_ & _ & B).
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i].
    + rewrite Z.add_0_r. exact Hb.
    + cbn [nth_error]. rewrite <- (B i ltac:(cbn [length] in Hi; lia)).
      replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. reflexivity.
Qed.

(* addressable of fr for L bytes from n shadow bytes read as 0x00 (ported from Tk/AW/SmLib.v addressable_zero). *)
Lemma lay_addr_zero : forall (mm : word -> option byte) (fr L n : Z), 0 <= fr -> fr mod 8 = 0 -> 0 <= L <= 8 * n ->
  fr + L <= APPMEM_END -> (forall i, 0 <= i < L -> app_mem (fr + i)) ->
  bytes_at rsegs mm (shadow_addr fr) (repeat (Z_to_bv 8 0) (Z.to_nat n)) -> addressable mm fr L.
Proof.
  intros mm fr L n H0 HM HL HE APP (B0 & B1 & B). split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply APP; lia|]. exists (Z_to_bv 8 0).
  assert (E : shadow_addr (fr + i) = shadow_addr fr + Z.of_nat (Z.to_nat (i / 8))).
  { rewrite Z2Nat.id by (apply Z.div_pos; lia). unfold shadow_addr.
    rewrite (Z.div_mod fr 8) at 1 by lia. rewrite HM, Z.add_0_r, (Z.mul_comm 8 (fr / 8)), Z.div_add_l by lia. lia. }
  pose proof (B (Z.to_nat (i / 8))) as R. rewrite repeat_length in R.
  assert (LT : (Z.to_nat (i / 8) < Z.to_nat n)%nat).
  { assert (i / 8 < n) by (apply Z.div_lt_upper_bound; lia). pose proof (Z.div_pos i 8 ltac:(lia) ltac:(lia)). lia. }
  specialize (R LT). rewrite nth_error_repeat in R by exact LT.
  split.
  - rewrite E. exact R.
  - left. reflexivity.
Qed.

(* Proof speed (common.md, Proof speed (2)): lia case-splits the disjunctions, the mod facts and the propositional
   implications (each one a disjunction for lia) of the whole hypothesis context, and the unit's lia
   (lib/Lib/LiaTwx2.v) destructs every Section range `0 <= _ < _` and tries every implication at each call.
   rs_hide_all hides the first three behind rs_hold at the top of a slow part; `unfold rs_hold in H` brings one back.
   The Section-L proofs that use it start with
     Proof using <the Section variables the proof used before this change>.  clear <the other Section hypotheses>.
     pose proof Rp as [Rp0 Rp1]; ...  apply rs_hide in Rp; ...
   so every statement after `End L` keeps its Section arguments, the unused hypotheses are out of lia's context, and
   the ranges are plain local copies. Measured on ly_pro_go: 467 s, 187 s with the disjunction and mod cases alone,
   79 s with the implication case as well; the whole file 1104 s -> 190 s (rocq compile -time, same VM). *)
Local Definition rs_hold (A : Prop) : Prop := A.
Local Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Local Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H
  | H : _ = _ mod _ |- _ => apply rs_hide in H
  | H : ?A -> _ |- _ => lazymatch type of A with Prop => apply rs_hide in H end end.

Section L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr ob tb mb nb gb : list byte).

  Local Notation S := (bv_unsigned sp).
  Local Notation K := CTRL_LAY_BLOCK_K.

  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rmd : 0 <= md < 2^64.
  Hypothesis Rg : 0 <= g < 2^64.
  Hypothesis SP16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - K) S.
  (* plain disjointness of the window [S-K, S) from the row and f *)
  Hypothesis DJ1 : ly_dj (S - K) S (p + 18) (p + 50).
  Hypothesis DJ2 : ly_dj (S - K) S f (f + 24).
  Hypothesis DJ3 : ly_k fr = 2 -> ly_dj (S - K) S (ly_tm fr) (ly_tm fr + 32).
  Hypothesis DJ3g : g <> 0 -> ly_al fr <> 0 -> ly_dj (S - K) S g (g + ly_al fr).
  Hypothesis DJ3m : 3 <= ly_k fr <= 9 -> md <> 0 ->
    ly_dj (S - K) S md (md + 296) /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       ly_dj (S - K) S (rname mb) (rname mb + Z.of_nat (length nb))).
  Hypothesis F8 : f mod 8 = 0.
  Hypothesis F24 : f + 24 <= 2^64.
  Hypothesis FL : length fr = 24%nat.
  Hypothesis FB : bytes_at rsegs m f fr.
  Hypothesis K9 : ly_k fr <= 9.
  Hypothesis AOL : ly_ao fr + ly_al fr <= 32.
  Hypothesis TM : ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm fr) tb.
  Hypothesis P0 : p <> 0.
  Hypothesis P50 : p + 50 <= 2^64.
  Hypothesis BLK : rw_cells rsegs m (p + 18) [CB 32 ob].
  Hypothesis DB1 : ly_dj (p + 18) (p + 50) f (f + 24).
  Hypothesis DB2 : ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32).
  Hypothesis DB3 : 3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296).
  Hypothesis DBN : 3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) ->
    has mb <> 0 -> rname mb <> 0 -> ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb)).
  Hypothesis MDP : 3 <= ly_k fr <= 9 -> md <> 0 ->
    md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       name_ok nb /\ bytes_at rsegs m (rname mb) nb).
  Hypothesis GP : g <> 0 -> ly_al fr <> 0 ->
    Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr).
  Hypothesis MI0 : mem_inv rsegs m.
  (* asan *)
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= S - K.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - K) K.
  Hypothesis AF : addressable m f 24.
  Hypothesis AR : addressable m (p + 18) 32.
  Hypothesis AP50 : app_mem (p + 50).
  Hypothesis ARDJ : p + 50 <= RT_LO \/ RT_HI <= p + 18.
  Hypothesis ATM : ly_k fr = 2 -> addressable m (ly_tm fr) 32.
  Hypothesis AG : g <> 0 -> ly_al fr <> 0 ->
    addressable m g (ly_al fr) /\ app_mem (g + ly_al fr) /\ app_mem (g + 7) /\ app_mem (p + 25 + ly_ao fr).
  Hypothesis AMD : 3 <= ly_k fr <= 9 -> md <> 0 ->
    addressable m md 296 /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       addressable m (rname mb) (Z.of_nat (length nb))).
  Hypothesis AJ5 : ly_k fr = 5 -> addressable m JOIN_0014 32.
  Hypothesis AJ6 : ly_k fr = 6 -> addressable m JOIN_0013 32.
  Hypothesis FP0 : fp [0%nat; 1%nat] m (bv_unsigned tp) FS (S - K) S
    (ctrl_lay_block_W p S) (ctrl_lay_block_D p f).
  Hypothesis FPT : ly_k fr = 2 -> fp_dj [(ly_tm fr, ly_tm fr + 32)] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPG : g <> 0 -> ly_al fr <> 0 -> fp_dj [(g, g + ly_al fr)] (fp_w [0%nat; 1%nat] FS).
  Hypothesis FPM : 3 <= ly_k fr <= 9 -> md <> 0 ->
    fp_dj [(md, md + 296)] (fp_w [0%nat; 1%nat] FS) /\
    ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)).
  Hypothesis TLS0 : ctrl_lay_block_tls m (bv_unsigned tp) FS (S - K) S.

  Definition LAY : list byte :=
    ly_lay (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))) g (ly_ao fr) (ly_al fr) gb.
  Definition BASE : list byte := ly_base (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))).

  Definition Q : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch ([(p + 18, p + 50); (S - K, S)] ++ fp_w [0%nat; 1%nat] FS ++
             [(shadow_addr (S - K), shadow_addr S)]) m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' (S - K) S /\
      rw_cells rsegs m' (p + 18) [CB 32 LAY] /\
      asan_cells m' /\ shadow_rw m' /\
      addressable m' (S - K) K /\
      fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
      ctrl_lay_block_tls m' (bv_unsigned tp) FS (S - K) S.

  Hypothesis HSM : asan_stack_malloc_1_contract.
  Hypothesis MEMS : asan_memset_contract.
  Hypothesis MEMC : asan_memcpy_contract.
  Hypothesis BOX : reac_box_model_block_contract.

  Local Notation SP2 := ((S - 128) / 32 * 32).

  Lemma SP2_facts : SP2 mod 32 = 0 /\ S - 160 <= SP2 <= S - 128.
  Proof using FL K9 MDP P0 Rf Rg Rmd Rp SP16 TM gb.
    clear ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 SR0 HHM HAE AW0 AF AR AP50 ARDJ
      ATM AG AMD AJ5 AJ6 FP0 FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    Z.div_mod_to_equations. lia. Qed.

  Lemma STW0 : forall a, S - K <= a < S -> wview rsegs m (wa a) <> None.
  Proof. intros a Ha. exact (stk_wv m _ _ _ ST0 Ha). Qed.

  (* The frame base frb: real (sfr = 0, frb = SP2 - 96, sp = frb) or side (sfr = frb = fs_frame FS 1 j, sp = SP2). *)
  Definition FK (frb sfr spc j : Z) (w120 : word) : Prop :=
    (sfr = 0 /\ frb = SP2 - 96 /\ spc = SP2 - 96) \/
    (0 <= j < fs_M 1 /\ frb = fs_frame FS 1 j /\ sfr = frb /\ spc = SP2 /\ w120 = Z_to_bv 64 (fs_flag FS 1 j)).

  (* The 96-byte region [frb, frb + 96) the setup writes, and its 12 shadow bytes. *)
  Lemma fk_facts : forall frb sfr spc j w120, FK frb sfr spc j w120 ->
    frb mod 8 = 0 /\ FS + 36864 <= frb /\ frb + 96 <= SP2 /\ (spc = SP2 \/ spc = frb) /\
    (forall i, 0 <= i < 96 -> wview rsegs m (wa (frb + i)) <> None) /\
    (forall i, 0 <= i < 96 -> app_mem (frb + i)) /\
    (frb + 96 <= LOWMEM_END \/ HIGHMEM_BEG <= frb) /\
    (forall i, 0 <= i < 12 -> wview rsegs m (wa (frb / 8 + ASAN_K + i)) <> None) /\
    LOWMEM_END <= frb / 8 + ASAN_K /\ frb / 8 + ASAN_K + 12 <= HIGHMEM_BEG.
  Proof using AW0 FL FP0 HAE HHM K9 MDP P0 Rf Rg Rmd Rp SP16 SR0 ST0 TM gb.
    clear DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 AF AR AP50 ARDJ ATM AG AMD AJ5 AJ6
      FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros frb sfr spc j w120 HK.
    pose proof SP2_facts as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & _).
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5. unfold ASAN_GT in P3.
    unfold CTRL_LAY_BLOCK_K in *.
    assert (B : frb mod 8 = 0 /\ FS + 36864 <= frb /\ frb + 96 <= SP2 /\ (spc = SP2 \/ spc = frb) /\
                (forall i, 0 <= i < 96 -> wview rsegs m (wa (frb + i)) <> None) /\
                (forall i, 0 <= i < 96 -> app_mem (frb + i))).
    { destruct HK as [(Ef & Efr & Esp) | (Hj & Efr & Ef & Esp & Ew)]; subst frb.
      - split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia|].
        intros i Hi. replace (SP2 - 96 + i) with (S - 4512 + (SP2 - 96 + i - (S - 4512))) by lia.
        apply (acl_app_in m (S - 4512) 4512); [exact AW0 | lia].
      - replace (fs_M 1) with 8192 in Hj by reflexivity.
        unfold fs_frame, fs_B in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 1) with 2 in *.
        split; [Z.div_mod_to_equations; lia|]. split; [lia|].
        split; [lia|]. split; [left; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ P5); lia|].
        intros i Hi. apply P4. lia. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (app_range frb 96 ltac:(lia) B6) as B7.
    assert (B8 : forall i, 0 <= i < 12 -> frb / 8 + ASAN_K + i = shadow_addr (frb + 8 * i)).
    { intros i Hi. rewrite sh_add8 by exact B1. unfold shadow_addr. lia. }
    do 7 (split; [assumption|]).
    split.
    - intros i Hi. rewrite B8 by exact Hi. apply (proj1 (SR0 _ (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
    - unfold ASAN_K, LOWMEM_END, HIGHMEM_BEG. split; Z.div_mod_to_equations; lia.
  Qed.

  (* ---- entry: 0x855f4 -> 0x85718 (prologue, class-1 frame request, header words, frame shadow, row memset) ---- *)

  (* The asan writes beyond the plain ones: the class-0 and class-1 side-stack bytes and the window's shadow. *)
  Definition lay_X : list ivl := fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (S - K), shadow_addr S)].
  (* The 12 callee-saved registers the prologue stores at [S - 96, S). *)
  Definition SAVES : list cell :=
    [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* The writes of the run up to the body: the window, the class-1 hint word and flag byte, the frame, its shadow. *)
  Definition Wf (frb j n : Z) : list ivl :=
    [(S - K, S); (fs_hint FS 1, fs_hint FS 1 + 8); (fs_flag FS 1 j, fs_flag FS 1 j + n);
     (frb, frb + 128); (shadow_addr frb, shadow_addr frb + 16)].

  (* The mid state after the malloc dispatch, carried into fwords; w120 is the flag-address word at frb + 120 (only
     the side frame, sfr <> 0, keeps it).  The window is still addressable (the request wrote no shadow byte of it)
     and fp and the tls premise hold (the request's hint word and flag byte are back to 0/1 values). *)
  Definition BI (W : list ivl) (frb sfr : Z) (w120 : word) (mc : word -> option byte) : Prop :=
    munch W m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 96) SAVES /\
    (sfr <> 0 -> bytes_at rsegs mc (frb + 120) (le8 w120)) /\
    addressable mc (S - K) K /\
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
    ctrl_lay_block_tls mc (bv_unsigned tp) FS (S - K) S.

  (* The body-entry state at 0x85718: the runtime cells readable, the window and saves held, the row zeroed, the
     frame descriptor word kept (side frame only), the box output [frb + 32, frb + 64) addressable, fp and the tls
     premise, and every window byte outside the frame [frb, frb + 96) addressable (FI's parts). *)
  Definition ME (frb sfr : Z) (w120 : word) (mc : word -> option byte) : Prop :=
    munch (ctrl_lay_block_W p S ++ lay_X) m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    asan_cells mc /\ shadow_rw mc /\ stk rsegs mc (S - K) S /\
    rw_cells rsegs mc (S - 96) SAVES /\
    rw_cells rsegs mc (p + 18) [CB 32 ly_zero] /\
    bytes_at rsegs mc f fr /\ (sfr <> 0 -> bytes_at rsegs mc (frb + 120) (le8 w120)) /\
    addressable mc (p + 18) 32 /\ addressable mc f 24 /\ addressable mc (frb + 32) 32 /\
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
    ctrl_lay_block_tls mc (bv_unsigned tp) FS (S - K) S /\
    (forall x, S - K <= x < S -> (x < frb \/ frb + 96 <= x) -> addressable mc x 1).

  Definition KB (Q : machine_state -> Prop) : Prop :=
    forall (frb sfr spc j : Z) (w120 : word) (mc : word -> option byte)
           (xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      FK frb sfr spc j w120 -> ME frb sfr w120 mc ->
      evt rsegs Q (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
                          a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
                          (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md) (Z_to_bv 64 p) (Z_to_bv 64 (frb / 8 + ASAN_K))
                          (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                      F (Z_to_bv 64 0x85718) fc None mc (seg_rom rsegs)).

  (* ---- shadow-footprint helpers (ports of reac_ctrl_classify_box_frame.v to class [0; 1]) ---- *)

  Lemma lay_frame_mod8 : forall c, FS mod 4096 = 0 -> fs_frame FS c 0 mod 8 = 0.
  Proof.
    intros c H. unfold fs_frame, fs_B. Z.div_mod_to_equations.
    assert (0 <= Z.of_nat c) by apply Zle_0_nat. lia.
  Qed.

  (* A byte of a data range (f or the row) is apart from the class-0/1 side-stack bytes (FP0's D-disjointness). *)
  Lemma lay_out_fpw_d : forall a b x, In (a, b) (ctrl_lay_block_D p f) -> a <= x < b ->
    outside (fp_w [0%nat; 1%nat] FS) x.
  Proof.
    intros a b x Hin Hx.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & _ & _ & _ & DJ).
    exact (fl_dj_out_r _ _ a b x DJ Hin Hx).
  Qed.

  (* The shadow byte of an app point apart from the class-0/1 side-stack bytes is apart from them. *)
  Lemma lay_out_fpw_sh : forall x, app_mem x -> outside (fp_w [0%nat; 1%nat] FS) x ->
    outside (fp_w [0%nat; 1%nat] FS) (shadow_addr x).
  Proof.
    intros x Hap Ho.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & P5) & _).
    pose proof (rt_app_shadow x Hap) as Hs. unfold FS_SIZE in P4.
    assert (NA : forall a b, (forall z, a <= z < b -> app_mem z) -> ~ (a <= shadow_addr x < b)).
    { intros a b Hab Hin. exact (acl_app_not_shadow _ (Hab _ Hin) Hs). }
    cbn [fp_w flat_map fp_w1 app outside] in *.
    destruct Ho as (_ & _ & H30 & _ & _ & _ & H31 & _).
    split; [apply NA; intros z Hz; apply P4; unfold fs_hint in *; cbn [Z.of_nat] in *; lia|].
    split; [apply NA; intros z Hz; apply P4; unfold fs_flag, fs_M in *; cbn [Z.of_nat Pos.of_succ_nat] in *; lia|].
    split; [apply NA; intros z Hz; apply P4; unfold fs_frame, fs_M, fs_B in *; cbn [Z.of_nat Pos.of_succ_nat] in *; lia|].
    split; [exact (acl_win_sh x _ _ (lay_frame_mod8 0 P2) H30)|].
    split; [apply NA; intros z Hz; apply P4; unfold fs_hint in *; cbn [Z.of_nat] in *; lia|].
    split; [apply NA; intros z Hz; apply P4; unfold fs_flag, fs_M in *; cbn [Z.of_nat Pos.of_succ_nat] in *; lia|].
    split; [apply NA; intros z Hz; apply P4; unfold fs_frame, fs_M, fs_B in *; cbn [Z.of_nat Pos.of_succ_nat] in *; lia|].
    split; [exact (acl_win_sh x _ _ (lay_frame_mod8 1 P2) H31) | exact I].
  Qed.

  (* A point of application memory that is outside [a, b) (an all-app range) has an in_shadow image, so is outside. *)
  Lemma lay_sh_app_out : forall y a b, in_shadow y -> (forall z, a <= z < b -> app_mem z) -> ~ (a <= y < b).
  Proof. intros y a b Hy Hab [H1 H2]. exact (acl_app_not_shadow y (Hab y (conj H1 H2)) Hy). Qed.

  (* The shadow of an app point apart from the side stack and the window is outside the footprint. *)
  Lemma lay_out_Wc_sh : forall x, app_mem x -> outside (fp_w [0%nat; 1%nat] FS) x ->
    (x < S - K \/ S <= x) -> outside (ctrl_lay_block_W p S ++ lay_X) (shadow_addr x).
  Proof using AR FL FP0 HHM K9 MDP P0 Rf Rg Rmd Rp SP16 TM gb.
    clear ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 SR0 HAE AW0 AF AP50 ARDJ ATM AG
      AMD AJ5 AJ6 FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    unfold rs_hold in SP16.
    intros x Hap Hfpw Hw. pose proof (rt_app_shadow x Hap) as Hsh.
    pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
    assert (SK8 : (S - K) mod 8 = 0) by (pose proof SP16; unfold CTRL_LAY_BLOCK_K; Z.div_mod_to_equations; lia).
    assert (Hlt : shadow_addr x < S - K).
    { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh. lia. }
    assert (Orow : ~ (p + 18 <= shadow_addr x < p + 50)).
    { apply lay_sh_app_out; [exact Hsh | intros z Hz;
        replace z with (p + 18 + (z - (p + 18))) by lia;
        exact (acl_app_in m (p + 18) 32 (z - (p + 18)) AR ltac:(lia))]. }
    assert (Owin : ~ (shadow_addr (S - K) <= shadow_addr x < shadow_addr S)).
    { apply acl_win_sh; [exact SK8 | lia]. }
    unfold ctrl_lay_block_W, lay_X. apply fl_out_app; [| apply fl_out_app].
    - cbn [outside]. split; [lia | split; [exact Orow | exact I]].
    - exact (lay_out_fpw_sh x Hap Hfpw).
    - cbn [outside]. split; [exact Owin | exact I].
  Qed.

  (* addressable of a data range survives the whole run's writes. *)
  Lemma lay_addr_keep : forall mc a b a' n',
    munch (ctrl_lay_block_W p S ++ lay_X) m mc -> In (a, b) (ctrl_lay_block_D p f) ->
    addressable m a' n' -> a <= a' -> a' + n' <= b -> (a' < S - K \/ S <= a') -> (b <= S - K \/ S <= a) ->
    addressable mc a' n'.
  Proof.
    intros mc a b a' n' MU Hin HA H1 H2 Hw Hbw.
    apply (addr_munch _ m mc a' n' HA MU). intros i Hi.
    apply lay_out_Wc_sh.
    - destruct HA as (_ & _ & _ & HAd). exact (proj1 (HAd i Hi)).
    - exact (lay_out_fpw_d a b (a' + i) Hin ltac:(lia)).
    - clear -Hw H1 H2 Hbw Hi. lia.
  Qed.

  Lemma acl_out_app_inv : forall A B x, outside (A ++ B) x -> outside A x /\ outside B x.
  Proof.
    induction A as [|[lo hi] A IH]; intros B x H; cbn [app outside] in *; [split; [exact I | exact H]|].
    destruct H as [H1 H2]. destruct (IH B x H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
  Qed.

  (* f (a data range of D, read only) is apart from the whole run's footprint. *)
  Lemma lay_f_out : forall x, f <= x < f + 24 -> outside (ctrl_lay_block_W p S ++ lay_X) x.
  Proof.
    intros x Hx. pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof (acl_app_in m f 24 (x - f) AF ltac:(lia)) as Hap. replace (f + (x - f)) with x in Hap by lia.
    unfold ctrl_lay_block_W, lay_X. apply fl_out_app; [| apply fl_out_app].
    - cbn [outside]. split; [unfold ly_dj in DJ2; lia | split; [unfold ly_dj in DB1; lia | exact I]].
    - exact (lay_out_fpw_d f (f + 24) x ltac:(left; reflexivity) Hx).
    - cbn [outside]. split; [| exact I].
      exact (acl_sh_out x (S - K) S Hap ltac:(unfold HIGHMEM_BEG in HHM'; lia) HAE').
  Qed.

  (* The fwords footprint Wf lies inside the whole run's footprint. *)
  Lemma lay_Wf_sub : forall frb sfr spc j n w120, FK frb sfr spc j w120 -> 0 <= n <= 1 ->
    (n = 0 \/ 0 <= j < fs_M 1) -> sub_fp (Wf frb j n) (ctrl_lay_block_W p S ++ lay_X).
  Proof.
    intros frb sfr spc j n w120 HK Hn Hnj.
    destruct (fk_facts frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _ & _).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & _) & _).
    pose proof SP2_facts as (HA32 & HAlo & HAhi).
    assert (S8 : S mod 8 = 0) by (pose proof SP16 as H16; clear -H16; Z.div_mod_to_equations; lia).
    assert (Esh : shadow_addr frb + 16 = shadow_addr (frb + 128))
      by (replace (frb + 128) with (frb + 8 * 16) by lia; symmetry; apply sh_add8; exact FR8).
    intros x Hf. unfold ctrl_lay_block_W, lay_X in Hf.
    apply acl_out_app_inv in Hf. destruct Hf as (HfW & Hf). apply acl_out_app_inv in Hf. destruct Hf as (Hfpw & Hfsh).
    cbn [outside] in HfW, Hfsh. destruct HfW as (HWwin & _). destruct Hfsh as (HWsh & _).
    cbn [fp_w flat_map fp_w1 app outside] in Hfpw.
    destruct Hfpw as (Oh0 & Ofl0 & Ofr0 & Osh0 & Oh1 & Ofl1 & Ofr1 & Osh1 & _).
    unfold Wf. cbn [outside].
    unfold fs_hint, fs_flag, fs_M in Oh1, Ofl1 |- *.
    cbn [Z.of_nat Pos.of_succ_nat] in Oh1, Ofl1 |- *.
    change (2 ^ (14 - 1)) with 8192 in Ofl1 |- *.
    change (2 ^ 15) with 32768 in Ofl1 |- *. change (2 ^ (15 - 1)) with 16384 in Ofl1 |- *.
    split; [exact HWwin|].
    split; [clear -Oh1; lia|].
    assert (Oflag : ~ (FS + 4096 + 32768 - 16384 + j <= x < FS + 4096 + 32768 - 16384 + j + n)).
    { destruct Hnj as [Hn0 | Hjb]; [subst n; lia |
        replace (fs_M 1) with 8192 in Hjb by reflexivity; clear -Ofl1 Hjb Hn; lia]. }
    split; [exact Oflag|].
    destruct HK as [(Ef & Efr & Esp) | (Hj & Efr & Ef & Esp & Ew)].
    - (* real: frame and its shadow are in the window and its shadow *)
      subst frb. unfold CTRL_LAY_BLOCK_K in HWwin, HWsh.
      split; [clear -HWwin HAlo HAhi; lia|].
      split; [| exact I]. rewrite Esh.
      pose proof (acl_sh_ge (SP2 - 96) (S - 4512) ltac:(clear -HAlo; lia)) as G1.
      pose proof (acl_sh_lt (SP2 - 96 + 128) S S8 ltac:(clear -HAhi; lia)) as G2.
      clear -HWsh G1 G2. lia.
    - (* side: frame and its shadow are in the class-1 side-stack ranges (fs_frame kept folded) *)
      subst frb. replace (fs_M 1) with 8192 in Hj by reflexivity.
      assert (B1 : fs_frame FS 1 0 <= fs_frame FS 1 j)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 1) with 2; clear -Hj; lia).
      assert (B2 : fs_frame FS 1 j + 128 <= fs_frame FS 1 (fs_M 1))
        by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 1) with 2; change (2 ^ (14 - 1)) with 8192; clear -Hj; lia).
      split; [clear -Ofr1 B1 B2; lia|].
      split; [| exact I]. rewrite Esh.
      pose proof (acl_sh_ge (fs_frame FS 1 j) (fs_frame FS 1 0) B1) as G1.
      pose proof (acl_sh_ge (fs_frame FS 1 (fs_M 1)) (fs_frame FS 1 j + 128) B2) as G2.
      clear -Osh1 G1 G2. lia.
  Qed.

  (* The row [p + 18, p + 50) is apart from the fwords footprint Wf. *)
  Lemma lay_row_out_Wf : forall frb sfr spc j n w120 x, FK frb sfr spc j w120 -> 0 <= n <= 1 ->
    (n = 0 \/ 0 <= j < fs_M 1) -> p + 18 <= x < p + 50 -> outside (Wf frb j n) x.
  Proof.
    intros frb sfr spc j n w120 x HK Hn Hnj Hx.
    destruct (fk_facts frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _ & _).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & _) & _).
    pose proof SP2_facts as (HA32 & HAlo & HAhi).
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    pose proof (acl_app_in m (p + 18) 32 (x - (p + 18)) AR ltac:(clear -Hx; lia)) as Hap.
    replace (p + 18 + (x - (p + 18))) with x in Hap by (clear -Hx; lia).
    pose proof (lay_out_fpw_d (p + 18) (p + 50) x ltac:(right; left; reflexivity) Hx) as Hfpw.
    cbn [fp_w flat_map fp_w1 app outside] in Hfpw.
    destruct Hfpw as (Oh0 & Ofl0 & Ofr0 & Osh0 & Oh1 & Ofl1 & Ofr1 & Osh1 & _).
    assert (Esh : shadow_addr frb + 16 = shadow_addr (frb + 128))
      by (replace (frb + 128) with (frb + 8 * 16) by (clear; lia); symmetry; apply sh_add8; exact FR8).
    assert (Hfrb0 : 0 <= frb) by (clear -FRlo P1; lia).
    assert (HfrbA : frb + 128 <= APPMEM_END) by (clear -FRhi HAhi HAE'; unfold APPMEM_END; lia).
    assert (Osf : ~ (shadow_addr frb <= x < shadow_addr frb + 16)).
    { rewrite Esh. apply acl_sh_out; [exact Hap | exact Hfrb0 | exact HfrbA]. }
    unfold Wf. cbn [outside].
    split; [unfold ly_dj in DJ1; clear -DJ1 Hx; lia|].
    split; [exact Oh1|].
    split.
    { unfold fs_flag, fs_M in Ofl1 |- *. cbn [Z.of_nat Pos.of_succ_nat] in Ofl1 |- *.
      change (2 ^ (14 - 1)) with 8192 in Ofl1. change (2 ^ 15) with 32768 in Ofl1 |- *.
      change (2 ^ (15 - 1)) with 16384 in Ofl1 |- *.
      destruct Hnj as [Hn0 | Hjb]; [subst n; lia |
        replace (fs_M 1) with 8192 in Hjb by reflexivity; clear -Ofl1 Hjb Hn; lia]. }
    destruct HK as [(Ef & Efr & Esp) | (Hj & Efr & Ef & Esp & Ew)].
    - subst frb. split; [| split; [exact Osf | exact I]].
      unfold ly_dj in DJ1. unfold CTRL_LAY_BLOCK_K in DJ1. clear -DJ1 HAlo HAhi Hx. lia.
    - subst frb. split; [| split; [exact Osf | exact I]].
      replace (fs_M 1) with 8192 in Hj by reflexivity.
      assert (B1 : fs_frame FS 1 0 <= fs_frame FS 1 j)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 1) with 2; clear -Hj; lia).
      assert (B2 : fs_frame FS 1 j + 128 <= fs_frame FS 1 (fs_M 1))
        by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
            change (2 ^ 1) with 2; change (2 ^ (14 - 1)) with 8192; clear -Hj; lia).
      clear -Ofr1 B1 B2. lia.
  Qed.
  (* The runtime state the post names, carried across the body: asan_cells, shadow_rw, the window addressable, fp and
     the tls premise.  (ports reac_box_model_block.v JR / jr_win to class [0;1].) *)
  Definition JR (m' : word -> option byte) : Prop :=
    asan_cells m' /\ shadow_rw m' /\ addressable m' (S - K) K /\
    fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
    ctrl_lay_block_tls m' (bv_unsigned tp) FS (S - K) S.

  Lemma JR_m : JR m.
  Proof.
    split; [exact AC0|]. split; [exact SR0|]. split; [exact AW0|]. split; [exact FP0 | exact TLS0].
  Qed.

  (* The runtime state survives writes inside the function's window [S - K, S). *)
  Lemma jr_win : forall W' m1 m2, JR m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 ->
    sub_fp W' [(S - K, S)] -> JR m2.
  Proof.
    intros W' m1 m2 (AC & SW & AW & FP & TL) MU WM Hs.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' (S - K) S x Hs HHM Hx)).
    unfold JR, ctrl_lay_block_W, CTRL_LAY_BLOCK_K in *.
    split; [|split; [|split; [|split]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply (fl_out_lo W' (S - K) S x Hs).
      left. clear -Hx HHM'. unfold RT_LO, RT_HI, HIGHMEM_BEG, CTRL_LAY_BLOCK_K in *. lia.
    - exact (fl_shadow_rw W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - exact (fl_fp [0%nat; 1%nat] m1 m2 (bv_unsigned tp) FS (S - K) S [(p + 18, p + 50)]
               (ctrl_lay_block_D p f) W' FP MU WM Hs).
    - exact (fl_tls [0%nat; 1%nat] m1 m2 (bv_unsigned tp) FS (S - K) S [(p + 18, p + 50)]
               (ctrl_lay_block_D p f) W'
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (S - K), shadow_addr S)]) FP MU Hs TL).
  Qed.


  Lemma lay_sh_lo : forall a x, 0 <= a -> x < 2147450880 -> x < shadow_addr a.
  Proof. intros a x Ha Hx. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. Qed.

  (* The full body footprint stays apart from the runtime's cells [RT_LO, RT_HI): the window and the side stack are
     above them, the row is apart (ARDJ), and every shadow byte and FS byte is above application memory.
     (ports reac_box_model_block.v br_out_rt / br_ac to class [0;1].) *)
  Local Opaque shadow_addr.
  Lemma lay_out_rt : forall Wm x, sub_fp Wm (ctrl_lay_block_W p S ++ lay_X) -> RT_LO <= x < RT_HI -> outside Wm x.
  Proof using ARDJ FL FP0 HHM K9 MDP P0 Rf Rg Rmd Rp TM gb.
    clear SP16 ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 SR0 HAE AW0 AF AR AP50 ATM
      AG AMD AJ5 AJ6 FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    unfold rs_hold in ARDJ.
    intros Wm x Hs Hx.
    pose proof HHM as HHM'. unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HHM'. unfold RT_LO, RT_HI in Hx.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFSlo & _ & _ & _).
    unfold ASAN_GT in P3.
    assert (XF : x < FS) by lia.
    assert (XF0 : 0 <= FS) by lia.
    apply Hs. apply fl_out_app.
    - unfold ctrl_lay_block_W. cbn [outside]. unfold CTRL_LAY_BLOCK_K.
      pose proof ARDJ as A. unfold RT_LO, RT_HI, CTRL_LAY_BLOCK_K in A. destruct A as [A|A];
        (repeat match goal with
         | |- _ /\ _ => split
         | |- True => exact I
         | |- ~ (_ <= x < _) => lia
         end).
    - unfold lay_X, fp_w, fp_w1. cbn [flat_map app outside].
      unfold fs_hint, fs_flag, fs_frame, fs_B, fs_M, CTRL_LAY_BLOCK_K.
      change (Z.of_nat 0) with 0 in *. change (Z.of_nat 1) with 1 in *.
      repeat match goal with
        | |- _ /\ _ => split
        | |- True => exact I
        | |- ~ (shadow_addr ?a <= x < _) =>
            assert (x < shadow_addr a) by (apply lay_sh_lo; lia); lia
        | |- ~ (_ <= x < _) => lia
        end.
  Qed.

  Lemma lay_ac : forall (Wm : list ivl) (m' : word -> option byte), munch Wm m m' ->
    sub_fp Wm (ctrl_lay_block_W p S ++ lay_X) -> asan_cells m'.
  Proof.
    intros Wm m' MU Hs. apply (fl_asan_cells Wm m m' AC0 MU). intros x Hx. exact (lay_out_rt Wm x Hs Hx).
  Qed.
  Local Transparent shadow_addr.

  (* 0x85928: the saved registers restored and the frame popped (sp = s0 - 128 + 128 = S), then ret. *)
  Lemma lay_tail : forall (m' : word -> option byte)
      (xra xsp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    rw_cells rsegs m' (bv_unsigned sp + -96) SAVES ->
    munch ([(p + 18, p + 50); (S - K, S)] ++ fp_w [0%nat; 1%nat] FS ++
           [(shadow_addr (S - K), shadow_addr S)]) m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - K) S ->
    rw_cells rsegs m' (p + 18) [CB 32 LAY] ->
    asan_cells m' -> shadow_rw m' -> addressable m' (S - K) K ->
    fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) ->
    ctrl_lay_block_tls m' (bv_unsigned tp) FS (S - K) S ->
    evt rsegs Q
      (MS (mkR xra xsp gp tp x5 x6 x7 sp (Z_to_bv 64 SP2) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x85928) fc None m' (seg_rom rsegs)).
  Proof using FL HHM MDP Rf Rg Rmd Rp TM.
    clear SP16 ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB K9 AOL P0 P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 SR0 HAE AW0 AF AR AP50
      ARDJ ATM AG AMD AJ5 AJ6 FP0 FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    intros m' xra xsp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      FR MU WM MI ST BK AC SR AW FP TL.
    unfold SAVES in FR. pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (SPlo : 2 ^ 32 <= S < 2 ^ 64)
      by (pose proof HHM; pose proof Rsp; unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in *; lia).
    do 15 step.
    apply evt_done. unfold Q. cbv beta.
    do 15 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact BK|]. split; [exact AC|]. split; [exact SR|]. split; [exact AW|].
    split; [exact FP | exact TL].
  Qed.

  (* writability of a byte of the window, frame or frame-shadow, at the base memory m. *)
  Ltac lay_wv :=
    let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii;
    first
      [ solve [ match goal with
                | SW : forall i, 0 <= i < 12 -> wview rsegs m (wa (?sb + i)) <> None |- wview _ _ (wa ?x) <> None =>
                    replace x with (sb + (x - sb)) by lia; apply SW; lia end ]
      | solve [ match goal with
                | FW : forall i, 0 <= i < 96 -> wview rsegs m (wa (?fb + i)) <> None |- wview _ _ (wa ?x) <> None =>
                    replace x with (fb + (x - fb)) by lia; apply FW; lia end ]
      | solve [ apply STW0; unfold CTRL_LAY_BLOCK_K in *; lia ]
      | match goal with |- ?G => fail 100 "WVFAIL" G end ].
  Ltac wst a n :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) n = true)
          by (eapply wv_store_ok; [ lay_wv | eassumption | lia | lia ])
    end.


  (* ===== ported from the image-B proof (a working branch fe5ef33a7fe): LC, FI, stage statements, helpers ===== *)
  (* The output-block carry invariant: the 32-byte output cell and the 12 callee-saved registers the prologue stores
     are in mc at [S - 128, S), the local stack region below is still a stack, the writes so far are confined to the
     output block [p + 18, p + 50), the window [S - K, S) and lay_X (the class-0/1 side-stack bytes and the window's
     shadow: the frame setup writes the frame's shadow bytes, and in the side case the frame itself), wmono/mem_inv
     hold, and the output block holds X.
     (ports lib/U/Prog/ctrl_lay_block.v LC to this image's sp-128 frame: a 32-byte cell above SAVES.) *)
  Definition LC (mc : word -> option byte) (gj X : list byte) : Prop :=
    rw_cells rsegs mc (bv_unsigned sp + -128) (CB 32 gj :: SAVES) /\
    stk rsegs mc (S - K) (bv_unsigned sp + -128) /\
    munch ([(p + 18, p + 50); (S - K, S)] ++ lay_X) m mc /\
    wmono rsegs m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (p + 18) [CB 32 X] /\ bytes_at rsegs mc f fr.

  Lemma LC_intro : forall mc gj X,
    rw_cells rsegs mc (bv_unsigned sp + -128) (CB 32 gj :: SAVES) ->
    stk rsegs mc (S - K) (bv_unsigned sp + -128) ->
    munch ([(p + 18, p + 50); (S - K, S)] ++ lay_X) m mc ->
    wmono rsegs m mc -> mem_inv rsegs mc -> rw_cells rsegs mc (p + 18) [CB 32 X] -> bytes_at rsegs mc f fr ->
    LC mc gj X.
  Proof. intros. unfold LC. tauto. Qed.

  Lemma LC_sok : forall mc gj X i, LC mc gj X -> 0 <= i < 32 ->
    store_ok rsegs mc (wa (p + 18 + i)) 1 = true.
  Proof.
    intros mc gj X i (FR & ST & MU & WM & MI & BK & Bf) Hi.
    destruct (ly_rw_cb _ _ _ _ _ BK) as (_ & _ & HW).
    apply (wr_at_store_ok rsegs mc (p + 18) (Z.of_nat 32) i 1 HW); lia.
  Qed.

  Lemma LC_store : forall mc gj X a bs, LC mc gj X -> length bs = 1%nat -> p + 18 <= a < p + 50 ->
    LC (write_to_mem mc (Z_to_bv 64 a) bs) gj (upd_bytes X (Z.to_nat (a - (p + 18))) bs).
  Proof using DB1 DJ1 FL K9 MDP P0 P50 Rf Rg Rmd Rp SP16 TM gb.
    clear ST0 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL BLK DB2 DB3 DBN GP MI0 AC0 SR0 HHM HAE AW0 AF AR AP50 ARDJ ATM AG AMD
      AJ5 AJ6 FP0 FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    intros mc gj X a bs (FR & ST & MU & WM & MI & BK & Bf) Hl Ha.
    destruct (ly_rw_cb _ _ _ _ _ BK) as (XL & XB & XW).
    pose proof DJ1 as D1. pose proof DB1 as D2.
    unfold ly_dj, CTRL_LAY_BLOCK_K in D1. unfold ly_dj in D2.
    change (Z_to_bv 64 a) with (wa a).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - apply rw_cells_frame; [exact FR | lia | rewrite Hl; lia |].
      unfold SAVES. cbn [cells_size csize]. rewrite Hl. lia.
    - apply stk_write; [exact ST | lia | rewrite Hl; lia].
    - apply munch_write; [exact MU | lia | rewrite Hl; lia | cbn [inside app]; rewrite Hl; left; lia].
    - apply wmono_write. exact WM.
    - apply mem_inv_store; [exact MI|]. rewrite Hl.
      replace a with (p + 18 + (a - (p + 18))) by lia.
      apply (wr_at_store_ok rsegs mc (p + 18) (Z.of_nat 32) (a - (p + 18)) 1 XW); lia.
    - apply ly_rw_cb_eq; [rewrite upd_bytes_length; lia | |].
      + replace (wa a) with (wa (p + 18 + (a - (p + 18)))) by (f_equal; lia).
        apply bytes_at_write_inside; [exact XB | lia | rewrite Hl, XL; lia].
      + apply wr_at_write. exact XW.
    - apply (bytes_at_write_other rsegs mc a bs f fr Bf); [lia | rewrite Hl; lia | rewrite FL, Hl; lia].
  Qed.

  (* From per-byte readability, a concrete byte list that is present in memory. *)
  Lemma bytes_at_of_rd : forall (n : nat) (mm : word -> option byte) (A : Z),
    0 <= A -> A + Z.of_nat n <= 2^64 ->
    (forall i, (i < n)%nat -> exists b, mrd rsegs mm (wa (A + Z.of_nat i)) = Some b) ->
    exists bs, length bs = n /\ bytes_at rsegs mm A bs.
  Proof.
    induction n as [|n IH]; intros mm A HA Hhi Hrd.
    - exists []. split; [reflexivity|]. split; [exact HA|]. split; [cbn [length]; lia|].
      intros i Hi. cbn [length] in Hi. lia.
    - destruct (IH mm A HA ltac:(lia) (fun i Hi => Hrd i ltac:(lia))) as (bs & Hl & Hba).
      destruct (Hrd n ltac:(lia)) as (b & Hb).
      destruct Hba as (_ & _ & Hbs).
      exists (bs ++ [b]). split; [rewrite length_app; cbn [length]; lia|].
      split; [exact HA|].
      split; [rewrite length_app, Hl; cbn [length]; rewrite Nat2Z.inj_add; cbn [Z.of_nat]; lia|].
      intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      destruct (Nat.eq_dec i n) as [->|Hne].
      + rewrite nth_error_app2 by lia. replace (n - length bs)%nat with 0%nat by lia. cbn [nth_error]. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia.
  Qed.

  (* The 12 shadow bytes of a 96-byte frame form a writable cell block (track target for the inline release). *)
  Lemma frame_shadow_rwcells : forall (mm : word -> option byte) (frb : Z),
    frb mod 8 = 0 -> frb + 96 <= APPMEM_END ->
    (forall i, 0 <= i < 96 -> app_mem (frb + i)) -> shadow_rw mm ->
    exists junk, length junk = 12%nat /\ rw_cells rsegs mm (shadow_addr frb) [CB 12 junk].
  Proof.
    intros mm frb Hm Hhi Happ Hsr.
    assert (Hshlo : 0 <= shadow_addr frb).
    { pose proof (Happ 0 ltac:(lia)) as A0. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A0.
      unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
    assert (Hshhi : shadow_addr frb + 12 <= 2^64).
    { unfold shadow_addr, ASAN_K, APPMEM_END in *. Z.div_mod_to_equations. lia. }
    assert (Hin : forall i, 0 <= i < 12 -> in_shadow (shadow_addr frb + i)).
    { intros i Hi. replace (shadow_addr frb + i) with (shadow_addr (frb + 8 * i))
        by (rewrite sh_add8 by exact Hm; reflexivity).
      apply rt_app_shadow. apply Happ. lia. }
    assert (Hrd : forall i, (i < 12)%nat -> exists b, mrd rsegs mm (wa (shadow_addr frb + Z.of_nat i)) = Some b).
    { intros i Hi. destruct (Hsr _ (Hin (Z.of_nat i) ltac:(lia))) as (_ & b & Hb). exists b. exact Hb. }
    destruct (bytes_at_of_rd 12 mm (shadow_addr frb) Hshlo ltac:(cbn [Z.of_nat]; lia) Hrd) as (junk & Hjl & Hjba).
    exists junk. split; [exact Hjl|].
    split; [split|].
    - cbn [cells_wf cell_wf]. split; [exact Hjl | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hjba.
    - cbn [cells_size csize]. split; [exact Hshlo|]. split; [cbn [Z.of_nat]; lia|].
      intros i Hi. cbn [Z.of_nat] in Hi. exact (proj1 (Hsr _ (Hin i ltac:(lia)))).
  Qed.

  (* The collector: a frame whose 12 shadow bytes all read 0 is addressable over its 96 bytes. *)
  Lemma frame_shadow_addressable : forall (mm : word -> option byte) (frb : Z) (bs : list byte),
    frb mod 8 = 0 -> 0 <= frb -> frb + 96 <= APPMEM_END ->
    (forall i, 0 <= i < 96 -> app_mem (frb + i)) ->
    length bs = 12%nat -> (forall b, In b bs -> bv_signed b = 0) ->
    bytes_at rsegs mm (shadow_addr frb) bs -> addressable mm frb 96.
  Proof.
    intros mm frb bs Hm Hlo Hhi Happ Hlen Hzero Hba.
    split; [exact Hlo|]. split; [lia|]. split; [exact Hhi|].
    intros i Hi. split; [apply Happ; exact Hi|].
    assert (Hdiv : (frb + i) / 8 = frb / 8 + i / 8) by (Z.div_mod_to_equations; lia).
    assert (Hsh : shadow_addr (frb + i) = shadow_addr frb + i / 8)
      by (unfold shadow_addr; rewrite Hdiv; lia).
    rewrite Hsh.
    assert (Hk8 : 0 <= i / 8 < 12) by (Z.div_mod_to_equations; lia).
    set (k := Z.to_nat (i / 8)).
    assert (Hkn : (k < 12)%nat) by (unfold k; lia).
    assert (Hik : i / 8 = Z.of_nat k) by (unfold k; rewrite Z2Nat.id by lia; reflexivity).
    rewrite Hik.
    destruct Hba as (Ba & Bb & Bc).
    destruct (nth_error bs k) as [b|] eqn:En; [|apply nth_error_None in En; lia].
    exists b. split.
    - rewrite (Bc k ltac:(lia)). exact En.
    - unfold shadow_ok. left. apply Hzero. eapply nth_error_In. exact En.
  Qed.

  (* The frame invariant the body carries at the epilogue (pc 0x85884): the frame layout FK, the side-stack flag
     pointer, the runtime cells, the shadow map writable, the side-stack package and tls, and every window byte outside
     the 96-byte frame [frb, frb + 96) addressable.  NOT whole-window addressable (the frame's guard bytes are marked
     unusable mid-body in the real case); ly_epi re-establishes it from the zeroed frame shadow (real) or from the last
     conjunct alone (side: the frame is not in the window). *)
  Definition FI (mc : word -> option byte) (frb sfr spc j : Z) (w120 : word) : Prop :=
    FK frb sfr spc j w120 /\
    (sfr <> 0 -> bytes_at rsegs mc (frb + 120) (le8 w120)) /\
    asan_cells mc /\ shadow_rw mc /\
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
    ctrl_lay_block_tls mc (bv_unsigned tp) FS (S - K) S /\
    (forall x, S - K <= x < S -> (x < frb \/ frb + 96 <= x) -> addressable mc x 1).

  (* Stage statement at the epilogue (pc 0x85884), proved by ly_epi: s0 = entry sp, s1 = SP2, s2 = sfr (the
     side-stack frame or 0), s8 = shadow_addr frb, s9 = frb, s10 = ASAN_K, sp = spc. *)
  Definition EPI_T : Prop :=
    forall (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    FI mc frb sfr spc j w120 -> LC mc gj LAY ->
    evt rsegs Q
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) x19 x20 x21 x22 x23
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85884) fc None mc (seg_rom rsegs)).

  (* Stage statement after the frame setup and the checked_memset of the output block (pc 0x85718), proved by
     ly_dispatch: s3 = g, s4 = f, s5 = p + 18, s6 = md, s7 = p (image A); the frame's middle 32 bytes [frb + 32, frb + 64)
     are marked usable.  (The frame-setup lane may strengthen the premises; it reports each change.) *)
  Definition DISP_T : Prop :=
    forall (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FI mc frb sfr spc j w120 -> LC mc gj ly_zero -> addressable mc (frb + 32) 32 ->
    evt rsegs Q
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
               (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md) (Z_to_bv 64 p)
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85718) fc None mc (seg_rom rsegs)).

  Lemma le1_byte : forall v, le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
  Proof.
    intros v. unfold le1. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z.
    rewrite (Z_to_le_bytes_mod 1 v 64 ltac:(lia)). cbn [Z_to_le_bytes]. reflexivity.
  Qed.

  (* The tail of a cell block is itself a cell block at the shifted base. *)
  Lemma rw_cells_tail : forall (mm : word -> option byte) (A : Z) (pre post : list cell),
    rw_cells rsegs mm A (pre ++ post) -> rw_cells rsegs mm (A + Z.of_nat (cells_size pre)) post.
  Proof.
    intros mm A pre post [[Hwf Hb] Hwr].
    apply cells_wf_app in Hwf. destruct Hwf as [Hwfp Hwfq].
    rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
    rewrite cells_bytes_length in Hb by exact Hwfp.
    destruct Hwr as (HA & HAn & HW). rewrite cells_size_app, Nat2Z.inj_add in HAn.
    split; [split; [exact Hwfq | exact Hb]|].
    split; [lia|]. split; [lia|].
    intros i Hi. replace (A + Z.of_nat (cells_size pre) + i) with (A + (Z.of_nat (cells_size pre) + i)) by lia.
    apply HW. rewrite cells_size_app, Nat2Z.inj_add. lia.
  Qed.

  (* Step a shadow byte store at offset o (= nat index k), updating the tracked [CB 12] shadow cell HSH. *)
  Ltac tsh frb FSW o k :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (store_ok rsegs mm (wa (shadow_addr frb + o)) 1 = true) as HSo
        by (eapply wv_store_ok;
            [ let ii := fresh in let Hii := fresh in intros ii Hii;
              assert (ii = 0) by lia; subst ii; rewrite Z.add_0_r; unfold shadow_addr; apply FSW; lia
            | eassumption | lia | lia ])
    end;
    step;
    change (Z_to_bv 64 (shadow_addr frb + o)) with (wa (shadow_addr frb + Z.of_nat k));
    rewrite le1_byte;
    repeat lazymatch goal with Hx : store_ok _ _ _ _ = _ |- _ => clear Hx end;
    mem_after_store.

  (* ===== epilogue: ly_epi (insert below this line) ===== *)
  (* (ported from the image-B proof lib/B/Prog/ctrl_lay_block.v (not in this delivery) ly_epi; the A code 0x85884 ->
     0x85928 is B's 0x8638c -> 0x86430 with the addresses moved.) *)

  (* The tls premise survives the inline frame release: the run writes only Wm inside the caller's writes W, the class
     bytes fp_w cs FS and the window's shadow; the thread cells are apart from all of these (fp's own W-disjointness and
     the caller's tls bound), so the pointers they hold are unchanged.  (port of lib/B/Prog/RcAsanFPLib.v fl_tls_free,
     the companion of fl_fp_free for ctrl_lay_block_tls.) *)
  Lemma ly_epi_tls_free : forall cs m m' TP FS lo hi W D Wm X,
    fp cs m TP FS lo hi W D -> munch Wm m m' ->
    sub_fp Wm (W ++ fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)]) ->
    (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
       fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)])) ->
    (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) X) ->
    forall DT TS C T DB k, asan_tls_cells m' TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) X.
  Proof.
    intros cs m1 m2 TP FS1 lo hi W D Wm X (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _)
      Hm Hs Htls2 Htls DT TS C T DB k HT.
    pose proof (Htls2 DT0 TS0 C0 T0 DB0 k0 HT0) as TLSdj.
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply Hs. apply fl_out_app.
      - exact (fl_dj_out W _ a b x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
      - exact (fl_dj_out_r _ _ a b x TLSdj Hin Hx). }
    destruct (fl_tls_same m1 m2 Wm TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT0 TS0 C0 T0 DB0 k0. exact (Htls DT TS C T DB k HT0).
  Qed.

  (* A range is addressable when each of its bytes is. *)
  Lemma ly_epi_addr_pw : forall (mm : word -> option byte) lo n, 0 <= lo -> 0 <= n -> lo + n <= APPMEM_END ->
    (forall x, lo <= x < lo + n -> addressable mm x 1) -> addressable mm lo n.
  Proof.
    intros mm lo n H0 Hn He H. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
    intros i Hi. destruct (H (lo + i) ltac:(lia)) as (_ & _ & _ & Ha).
    pose proof (Ha 0 ltac:(lia)) as Hb. rewrite Z.add_0_r in Hb. exact Hb.
  Qed.

  (* The shadow byte of an application byte is not in a range of application bytes. *)
  Lemma ly_epi_sh_not_app : forall x a n, app_mem x -> (forall i, 0 <= i < n -> app_mem (a + i)) ->
    ~ (a <= shadow_addr x < a + n).
  Proof.
    intros x a n Hx Ha [H1 H2]. apply (acl_app_not_shadow (shadow_addr x)); [| exact (rt_app_shadow x Hx)].
    replace (shadow_addr x) with (a + (shadow_addr x - a)) by lia. apply Ha. lia.
  Qed.

  (* The class-c state that fl_fp_free asks for, from fp_cls. *)
  Lemma ly_epi_cls_out : forall (mm : word -> option byte) (c : nat), fp_cls mm FS c ->
    (exists h', bytes_at rsegs mm (fs_hint FS c) (le8 h')) /\
    (exists flags', bytes_at rsegs mm (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags').
  Proof.
    intros mm c (_ & h & fl & Hh & Hf & Hl & HF). split; [exists h; exact Hh | exists fl; tauto].
  Qed.

  (* The class-c state survives writes apart from its hint word and its flag bytes. *)
  Lemma ly_epi_cls_keep : forall (W' : list ivl) (mm mm' : word -> option byte) (c : nat),
    (forall x, fs_hint FS c <= x < fs_hint FS c + 8 -> outside W' x) ->
    (forall x, fs_flag FS c 0 <= x < fs_flag FS c 0 + fs_M c -> outside W' x) ->
    munch W' mm mm' -> fp_cls mm FS c -> fp_cls mm' FS c.
  Proof.
    intros W' mm mm' c HH HF Hm (Hc & h & flags & Hh & Hf & Hl & HB).
    split; [exact Hc|]. exists h, flags.
    split; [eapply fl_bytes; [exact Hh | exact Hm | intros x Hx; apply HH; rewrite length_le8 in Hx; lia]|].
    split; [eapply fl_bytes; [exact Hf | exact Hm | intros x Hx; apply HF; lia]|].
    split; assumption.
  Qed.

  (* The class-c state survives the clearing of one flag byte a (to 0) and writes apart from the rest. *)
  Lemma ly_epi_cls_clear : forall (W' : list ivl) (mm mm' : word -> option byte) (c : nat) (a : Z),
    (forall x, fs_hint FS c <= x < fs_hint FS c + 8 -> outside W' x) ->
    fs_flag FS c 0 <= a < fs_flag FS c 0 + fs_M c ->
    (forall x, fs_flag FS c 0 <= x < fs_flag FS c 0 + fs_M c -> x <> a -> outside W' x) ->
    bytes_at rsegs mm' a [Z_to_bv 8 0] -> munch W' mm mm' -> fp_cls mm FS c -> fp_cls mm' FS c.
  Proof using FL K9 MDP P0 Rf Rg Rmd Rp TM gb sp.
    clear SP16 ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 SR0 HHM HAE AW0 AF AR AP50
      ARDJ ATM AG AMD AJ5 AJ6 FP0 FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    intros W' mm mm' c a HH Ha HF Hz Hm (Hc & h & flags & Hh & Hf & Hl & HB).
    set (k := Z.to_nat (a - fs_flag FS c 0)).
    assert (Hk : (k + length [Z_to_bv 8 0] <= length flags)%nat) by (unfold k; cbn [length]; lia).
    split; [exact Hc|]. exists h, (upd_bytes flags k [Z_to_bv 8 0]).
    split; [eapply fl_bytes; [exact Hh | exact Hm | intros x Hx; apply HH; rewrite length_le8 in Hx; lia]|].
    split; [|split; [rewrite upd_bytes_length by exact Hk; exact Hl|]].
    - destruct Hf as (Hf0 & Hf1 & Hf2). destruct Hz as (_ & _ & Hz2).
      split; [exact Hf0|]. split; [rewrite upd_bytes_length by exact Hk; exact Hf1|].
      intros i Hi. rewrite upd_bytes_length in Hi by exact Hk.
      rewrite (upd_bytes_nth flags k [Z_to_bv 8 0] i Hk Hi). cbn [length].
      destruct (Nat.leb k i && Nat.ltb i (k + 1))%bool eqn:Eb.
      + apply andb_true_iff in Eb as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
        replace (i - k)%nat with 0%nat by lia. cbn [nth_error].
        transitivity (mrd rsegs mm' (wa (a + Z.of_nat 0))).
        * f_equal. f_equal. unfold k in *. lia.
        * exact (Hz2 0%nat ltac:(cbn [length]; lia)).
      + assert (Hne : fs_flag FS c 0 + Z.of_nat i <> a).
        { intros E. apply andb_false_iff in Eb as [E1|E1];
            [apply Nat.leb_gt in E1 | apply Nat.ltb_ge in E1]; unfold k in *; lia. }
        unfold mrd. rewrite Hm; [exact (Hf2 i Hi)|]. rewrite wa_unsigned by lia. apply HF; [lia | exact Hne].
    - rewrite Forall_forall in HB |- *. intros b Hb.
      destruct (In_nth_error _ _ Hb) as (i & Hi).
      assert (Hil : (i < length flags)%nat).
      { rewrite <- (upd_bytes_length flags k [Z_to_bv 8 0] Hk). apply nth_error_Some. rewrite Hi. discriminate. }
      rewrite (upd_bytes_nth flags k [Z_to_bv 8 0] i Hk Hil) in Hi. cbn [length] in Hi.
      revert Hi. destruct (Nat.leb k i && Nat.ltb i (k + 1))%bool; intros Hi.
      + destruct (i - k)%nat as [|n]; cbn [nth_error] in Hi.
        * injection Hi as Hzb. subst b. left. reflexivity.
        * destruct n; cbn in Hi; discriminate.
      + exact (HB b (nth_error_In _ _ Hi)).
  Qed.

  (* A point outside a concrete write list: each range by lia. *)
  Ltac ly_epi_out := cbn [outside]; repeat (split; [lia|]); exact I.

  (* An untracked shadow byte store at offset o (the side frame's shadow beyond the 12 tracked bytes). *)
  Ltac ly_epi_ush frb FSW o :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (store_ok rsegs mm (wa (shadow_addr frb + o)) 1 = true) as HSo
        by (eapply wv_store_ok;
            [ let ii := fresh in let Hii := fresh in intros ii Hii;
              assert (ii = 0) by lia; subst ii; rewrite Z.add_0_r; unfold shadow_addr; apply FSW; lia
            | eassumption | lia | lia ])
    end;
    step; store_done.

  (* Real case (sfr = 0, frb = SP2 - 96, A excerpt 166-174 then 195-206): the frame's shadow bytes 4..7 <- 0xf8, the
     header word, then all 12 frame shadow bytes <- 0 (tracked as a [CB 12] cell, so the frame is addressable again);
     the rest of the window keeps its shadow (FI's last conjunct). *)
  Lemma ly_epi_real : forall (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    FI mc frb sfr spc j w120 -> sfr = 0 -> LC mc gj LAY ->
    evt rsegs Q
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) x19 x20 x21 x22 x23
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85884) fc None mc (seg_rom rsegs)).
  Proof using AMD AR ARDJ AW0 DB3 DBN DJ1 DJ3m FL FP0 FPM HAE HHM K9 MDP P0 Rf Rg Rmd Rp SP16 SR0 ST0 TM.
    clear DJ2 DJ3 DJ3g F8 F24 FB AOL P50 BLK DB1 DB2 GP MI0 AC0 AF AP50 ATM AG AJ5 AJ6 FPT FPG TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23
      x28 x29 x30 x31 (HK & _ & ACc & SRc & FPc & TLc & AWo) Hsfr0 LCH.
    pose proof (fk_facts _ _ _ _ _ HK) as (FR8 & FRlo & FRhi & _ & FW & FAP & _ & FSW & FSlo & FShi).
    pose proof FP0 as (_ & _ & _ & _ & _ & _ & _ & _ & (FSpos & _) & _).
    pose proof SP2_facts as (_ & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    assert (EH : HIGHMEM_BEG = 17594333495296) by reflexivity.
    assert (EA : APPMEM_END = 140737488355328) by reflexivity.
    assert (EL : LOWMEM_END = 2147450880) by reflexivity.
    assert (EAK : ASAN_K = 2147450880) by reflexivity.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    assert (WL : S - K <= frb /\ frb + 96 <= S - 128).
    { destruct HK as [(_ & E & _)|(_ & _ & Esfr & _)]; [lia|]. exfalso. lia. }
    destruct WL as (WL & WH). clear HAlo HAhi FRhi.
    assert (FHI : HIGHMEM_BEG <= frb) by lia.
    assert (FRge0 : 0 <= frb) by lia.
    assert (SHlo : 0 <= shadow_addr frb) by (unfold shadow_addr; lia).
    assert (SHhi : shadow_addr frb + 16 <= 2 ^ 64) by (unfold shadow_addr; lia).
    assert (SHL : LOWMEM_END <= shadow_addr frb) by (unfold shadow_addr; lia).
    assert (SHH : shadow_addr frb + 12 <= HIGHMEM_BEG) by (unfold shadow_addr; lia).
    assert (FRlt2 : frb + 8 <= 2 ^ 64) by lia.
    assert (DJmagic : shadow_addr frb + 12 <= frb) by lia.
    clear FSlo FShi.
    rs_hide_all.
    pose proof LCH as (_ & _ & _ & WMc & MIc & _ & _).
    destruct (frame_shadow_rwcells mc frb FR8 ltac:(lia) FAP SRc) as (junk & _ & HSH).
    pose proof (munch_refl [(shadow_addr frb, shadow_addr frb + 12); (frb, frb + 8)] mc) as MUcc.
    pose proof (wmono_refl rsegs mc) as WMcc.
    pose proof (rd_mono_refl mc) as RMcc.
    step.
    tsh frb FSW 4 4%nat. tsh frb FSW 5 5%nat. tsh frb FSW 6 6%nat. tsh frb FSW 7 7%nat.
    step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HM8 : store_ok rsegs mm (wa frb) 8 = true)
        by (eapply wv_store_ok; [ intros i Hi; apply FW; lia | eassumption | lia | lia ]) end.
    step. store_done.
    step. rewrite (rc_eqb sfr 0) by lia. rewrite (proj2 (Z.eqb_eq sfr 0) Hsfr0). cbv iota.
    tsh frb FSW 4 4%nat. tsh frb FSW 5 5%nat. tsh frb FSW 6 6%nat. tsh frb FSW 7 7%nat.
    tsh frb FSW 0 0%nat. tsh frb FSW 1 1%nat. tsh frb FSW 2 2%nat. tsh frb FSW 3 3%nat.
    tsh frb FSW 8 8%nat. tsh frb FSW 9 9%nat. tsh frb FSW 10 10%nat. tsh frb FSW 11 11%nat.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m' end.
    (* ===== the runtime state at 0x85928 and lay_tail ===== *)
    destruct LCH as (FRc & STc & MUc & _ & _ & BKc & _).
    pose proof FPc as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & PApp & _) & _ & _ & HCLc & HFSc & _).
    assert (E96 : shadow_addr (frb + 96) = shadow_addr frb + 12)
      by (rewrite <- (sh_add8 frb 12 FR8); f_equal; lia).
    assert (SH1 : shadow_addr (S - K) <= shadow_addr frb) by exact (acl_sh_ge frb (S - K) WL).
    assert (SH2 : shadow_addr frb + 12 <= shadow_addr S) by (rewrite <- E96; apply acl_sh_ge; lia).
    destruct HSH as [[_ HSHba] _]. cbn [cells_bytes cbytes app] in HSHba.
    assert (AFrame : addressable m' frb 96).
    { refine (frame_shadow_addressable m' frb _ FR8 FRge0 _ FAP _ _ HSHba).
      - lia.
      - reflexivity.
      - intros b Hb. cbn [In] in Hb. repeat (destruct Hb as [Hb|Hb]; [subst b; reflexivity|]). contradiction. }
    assert (AW' : addressable m' (S - K) K).
    { apply ly_epi_addr_pw; [lia | lia | lia |].
      intros x Hx.
      assert (Hax : app_mem x) by (unfold app_mem; right; lia).
      destruct (Z_lt_le_dec x frb) as [Hlt|Hge]; [| destruct (Z_lt_le_dec x (frb + 96)) as [Hin|Hge2]].
      2: { apply (acl_addr_sub m' frb 96 x 1 AFrame); lia. }
      all: apply (addr_munch _ mc m' x 1 (AWo x ltac:(lia) ltac:(lia)) MUcc);
           intros i Hi; assert (i = 0) by lia; subst i; rewrite Z.add_0_r;
           cbn [outside]; (split; [|split; [|exact I]]);
           [ rewrite <- E96; apply acl_win_sh; [exact FR8 | lia]
           | apply (ly_epi_sh_not_app x frb 8 Hax); intros k Hk; apply FAP; lia ]. }
    assert (FR128 : rw_cells rsegs m' (bv_unsigned sp + -128) (CB 32 gj :: SAVES)).
    { apply (acl_rw _ mc m' _ _ FRc MUcc WMcc).
      intros x Hx. cbn [cells_size csize SAVES Nat.add] in Hx. ly_epi_out. }
    assert (FRm' : rw_cells rsegs m' (bv_unsigned sp + -96) SAVES).
    { pose proof (rw_cells_tail m' (bv_unsigned sp + -128) [CB 32 gj] SAVES FR128) as HT.
      cbn [cells_size csize Nat.add] in HT.
      replace (bv_unsigned sp + -128 + Z.of_nat 32) with (bv_unsigned sp + -96) in HT by lia. exact HT. }
    assert (BKm' : rw_cells rsegs m' (p + 18) [CB 32 LAY]).
    { apply (acl_rw _ mc m' _ _ BKc MUcc WMcc).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      pose proof (acl_app_in m (p + 18) 32 (x - (p + 18)) AR ltac:(lia)) as Hapx.
      replace (p + 18 + (x - (p + 18))) with x in Hapx by lia. unfold app_mem in Hapx.
      pose proof DJ1 as D. unfold ly_dj in D. ly_epi_out. }
    assert (STm' : stk rsegs m' (S - K) S).
    { apply (stk_merge rsegs m' (S - K) (bv_unsigned sp + -128) S).
      - exact (stk_mono mc m' _ _ STc WMcc RMcc).
      - pose proof (stk_of_rw_cells rsegs m' _ _ FR128) as HS.
        cbn [cells_size csize Nat.add SAVES] in HS.
        replace (bv_unsigned sp + -128 + Z.of_nat 128) with S in HS by lia. exact HS.
      - lia. }
    assert (ACm' : asan_cells m').
    { apply (fl_asan_cells _ mc m' ACc MUcc). intros x Hx. unfold RT_LO, RT_HI in Hx. ly_epi_out. }
    pose proof (shadow_rw_mono mc m' SRc WMcc RMcc) as SRm'.
    assert (FSout : forall x, FS <= x < FS + FS_SIZE ->
      outside [(shadow_addr frb, shadow_addr frb + 12); (frb, frb + 8)] x).
    { intros x Hx. pose proof (PApp x Hx) as Hap. unfold app_mem in Hap. ly_epi_out. }
    assert (SUBcc : sub_fp [(shadow_addr frb, shadow_addr frb + 12); (frb, frb + 8)]
      (ctrl_lay_block_W p S ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (S - K), shadow_addr S)])).
    { unfold sub_fp, ctrl_lay_block_W. intros x H.
      cbn [outside app fp_w flat_map fp_w1] in H.
      destruct H as (HW1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPsh & _).
      cbn [outside]. split; [|split; [|exact I]].
      - intros Hc. apply HPsh. lia.
      - intros Hc. apply HW1. lia. }
    assert (SUBmu : sub_fp [(shadow_addr frb, shadow_addr frb + 12); (frb, frb + 8)]
      ([(p + 18, p + 50); (S - K, S)] ++ lay_X)).
    { unfold sub_fp, lay_X. intros x H.
      cbn [outside app fp_w flat_map fp_w1] in H.
      destruct H as (_ & HW2 & _ & _ & _ & _ & _ & _ & _ & _ & HPsh & _).
      cbn [outside]. split; [|split; [|exact I]].
      - intros Hc. apply HPsh. lia.
      - intros Hc. apply HW2. lia. }
    assert (FPm' : fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f)).
    { apply (fl_fp_free [0%nat; 1%nat] mc m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S)
               (ctrl_lay_block_D p f) _ FPc TLc MUcc WMcc SUBcc).
      - intros x Hx. apply FSout. unfold FS_SIZE. lia.
      - intros x Hx. left. apply FSout. exact Hx.
      - intros c Hc. apply ly_epi_cls_out.
        exact (fl_cls _ mc m' FS c FSout MUcc (proj1 (Forall_forall _ _) HCLc c Hc)). }
    pose proof (ly_epi_tls_free [0%nat; 1%nat] mc m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S)
                  (ctrl_lay_block_D p f) _ (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (S - K), shadow_addr S)])
                  FPc MUcc SUBcc TLc TLc) as TLm'.
    pose proof (munch_trans _ m mc m' MUc (munch_weaken _ _ mc m' SUBmu MUcc)) as MUm'.
    apply lay_tail.
    - exact FRm'.
    - exact MUm'.
    - exact WMc.
    - exact MIc.
    - exact STm'.
    - exact BKm'.
    - exact ACm'.
    - exact SRm'.
    - exact AW'.
    - exact FPm'.
    - exact TLm'.
  Qed.

  (* Side case (sfr = frb = fs_frame FS 1 j, A excerpt 166-194): the frame's shadow bytes 4..7 <- 0xf8, the header
     word, then the 16 shadow bytes of the 128-byte side frame <- 0xf5 (released), then the class-1 flag byte (its
     address is the word at frb + 120) <- 0.  The window keeps its shadow (FI's last conjunct): the side frame is
     below it. *)
  Lemma ly_epi_side : forall (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    FI mc frb sfr spc j w120 -> sfr <> 0 -> LC mc gj LAY ->
    evt rsegs Q
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) x19 x20 x21 x22 x23
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85884) fc None mc (seg_rom rsegs)).
  Proof using AMD AR ARDJ AW0 DB3 DBN DJ3m FL FP0 FPM HAE HHM K9 MDP P0 Rf Rg Rmd Rp SP16 SR0 ST0 TM.
    clear DJ1 DJ2 DJ3 DJ3g F8 F24 FB AOL P50 BLK DB1 DB2 GP MI0 AC0 AF AP50 ATM AG AJ5 AJ6 FPT FPG TLS0 HSM MEMS MEMC
      BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23
      x28 x29 x30 x31 (HK & HFLAG & ACc & SRc & FPc & TLc & AWo) Hsfr LCH.
    pose proof (fk_facts _ _ _ _ _ HK) as (FR8 & _ & _ & _ & FW & FAP & _ & _ & FSlo & _).
    specialize (HFLAG Hsfr).
    destruct HK as [(E0 & _ & _)|(Hj & Efr & Esfr & Espc & Ew)]; [exfalso; exact (Hsfr E0)|].
    subst sfr spc w120.
    pose proof FP0 as (_ & _ & _ & _ & _ & _ & _ & _ & (FSpos & _ & PGT & PApp & PStk) & _ & _ & _ & HFS0 & _).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    assert (EH : HIGHMEM_BEG = 17594333495296) by reflexivity.
    assert (EA : APPMEM_END = 140737488355328) by reflexivity.
    assert (EL : LOWMEM_END = 2147450880) by reflexivity.
    assert (EAK : ASAN_K = 2147450880) by reflexivity.
    assert (EZ : FS_SIZE = 11571200) by reflexivity.
    assert (EGT : ASAN_GT = 6283264) by reflexivity.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    assert (EfM1 : fs_M 1 = 8192) by reflexivity.
    assert (EfM0 : fs_M 0 = 16384) by reflexivity.
    assert (EfH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn; lia).
    assert (EfH1 : fs_hint FS 1 = FS + 8) by (unfold fs_hint; cbn; lia).
    assert (EfL0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn; lia).
    assert (EfL1 : fs_flag FS 1 0 = FS + 20480) by (unfold fs_flag; cbn; lia).
    assert (Efa : fs_flag FS 1 j = FS + 20480 + j) by (unfold fs_flag; cbn; lia).
    assert (EfF0 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn; lia).
    assert (EfF1 : fs_frame FS 1 (fs_M 1) = FS + 2134016) by (unfold fs_frame, fs_B; cbn; lia).
    assert (Efr' : frb = FS + 1085440 + j * 128) by (rewrite Efr; unfold fs_frame, fs_B; cbn; lia).
    rewrite EfM1 in Hj. clear Efr.
    set (fa := fs_flag FS 1 j) in *. clearbody fa.
    assert (SHlo : 0 <= shadow_addr frb) by (unfold shadow_addr; lia).
    assert (SHL : LOWMEM_END <= shadow_addr frb) by (unfold shadow_addr; lia).
    assert (SHtop : shadow_addr frb + 16 <= HIGHMEM_BEG) by (unfold shadow_addr; Z.div_mod_to_equations; lia).
    rs_hide_all.
    assert (SHFS : shadow_addr frb + 16 <= FS \/ FS + FS_SIZE <= shadow_addr frb).
    { destruct (app_range FS FS_SIZE ltac:(lia) (fun i Hi => PApp (FS + i) ltac:(lia))) as [Hlo|Hhi]; lia. }
    clear FSlo.
    (* The side stack and the flag pointer are hidden behind a conjunction while the stores run: a bytes_at, a
       ro_cells or a stk hypothesis about the current memory is transported (with its lia side conditions) at every
       store, and these two are needed only at the load and at the flag store. *)
    pose proof FPc as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & PStkc) & _).
    pose proof (conj PStkc I) as PStkH. clear PStkc.
    pose proof (conj HFLAG I) as HFLAGh. clear HFLAG.
    assert (FSW16 : forall i, 0 <= i < 16 -> wview rsegs m (wa (frb / 8 + ASAN_K + i)) <> None).
    { intros i Hi. replace (frb / 8 + ASAN_K + i) with (shadow_addr (frb + 8 * i))
        by (rewrite sh_add8 by exact FR8; unfold shadow_addr; lia).
      exact (proj1 (SR0 _ (rt_app_shadow _ (PApp (frb + 8 * i) ltac:(lia))))). }
    assert (FWa : wview rsegs m (wa fa) <> None) by exact (stk_wv m FS (FS + FS_SIZE) fa PStk ltac:(lia)).
    pose proof LCH as (_ & _ & _ & WMc & MIc & _ & _).
    destruct (frame_shadow_rwcells mc frb FR8 ltac:(lia) FAP SRc) as (junk & _ & HSH).
    pose proof (munch_refl [(shadow_addr frb, shadow_addr frb + 16); (frb, frb + 8); (fa, fa + 1)] mc) as MUcc.
    pose proof (wmono_refl rsegs mc) as WMcc.
    pose proof (rd_mono_refl mc) as RMcc.
    step.
    tsh frb FSW16 4 4%nat. tsh frb FSW16 5 5%nat. tsh frb FSW16 6 6%nat. tsh frb FSW16 7 7%nat.
    step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HM8 : store_ok rsegs mm (wa frb) 8 = true)
        by (eapply wv_store_ok; [ intros i Hi; apply FW; lia | eassumption | lia | lia ]) end.
    step. store_done.
    step. rewrite (rc_eqb frb 0) by lia. rewrite (proj2 (Z.eqb_neq frb 0) Hsfr). cbv iota.
    step.
    tsh frb FSW16 4 4%nat. tsh frb FSW16 5 5%nat. tsh frb FSW16 6 6%nat. tsh frb FSW16 7 7%nat.
    tsh frb FSW16 0 0%nat. tsh frb FSW16 1 1%nat. tsh frb FSW16 2 2%nat. tsh frb FSW16 3 3%nat.
    ly_epi_ush frb FSW16 12. ly_epi_ush frb FSW16 13. ly_epi_ush frb FSW16 14. ly_epi_ush frb FSW16 15.
    tsh frb FSW16 8 8%nat. tsh frb FSW16 9 9%nat. tsh frb FSW16 10 10%nat. tsh frb FSW16 11 11%nat.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HRO : ro_cells rsegs mm (frb + 120) [C8 (Z_to_bv 64 fa)])
        by (apply bytes_ro8; eapply fl_bytes;
            [ exact (proj1 HFLAGh) | exact MUcc
            | intros x Hx; rewrite length_le8 in Hx; ly_epi_out ]) end.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (RMcc (wa fa) (rd_of_stk mc FS (FS + FS_SIZE) (proj1 PStkH) fa ltac:(lia))) as (fb & Hfb);
      assert (HFc : rw_cells rsegs mm fa [C1 fb])
        by (split; [split|];
            [ cbn [cells_wf cell_wf]; tauto
            | cbn [cells_bytes cbytes app]; split; [lia|];
              split; [cbn [length Z.of_nat Pos.of_succ_nat]; lia|];
              intros i Hi; cbn [length] in Hi; assert (i = 0%nat) by lia; subst i;
              cbn [nth_error]; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; exact Hfb
            | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]; split; [lia|]; split; [lia|];
              intros i Hi; assert (i = 0) by lia; subst i; rewrite Z.add_0_r; apply WMc; exact FWa ]) end.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HSf : store_ok rsegs mm (wa fa) 1 = true)
        by (eapply wv_store_ok; [ intros i Hi; assert (i = 0) by lia; subst i; rewrite Z.add_0_r; exact FWa
                                | eassumption | lia | lia ]) end.
    step.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) =>
        rewrite ?le1_byte;
        repeat lazymatch goal with Hx : store_ok _ _ _ _ = _ |- _ => clear Hx end;
        mem_after_store
    | _ => idtac
    end.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m' end.
    (* ===== the runtime state at 0x85928 and lay_tail ===== *)
    destruct LCH as (FRc & STc & MUc & _ & _ & BKc & _).
    pose proof FPc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCLc & _ & _ & _ & HDdc).
    destruct HFc as [[_ HFz] _]. cbn [cells_bytes cbytes app] in HFz.
    assert (ShA : shadow_addr (fs_frame FS 1 0) <= shadow_addr frb) by (apply acl_sh_ge; lia).
    assert (ShB : shadow_addr frb + 16 <= shadow_addr (fs_frame FS 1 (fs_M 1))).
    { rewrite <- (sh_add8 frb 16 FR8). apply acl_sh_ge. lia. }
    assert (AW' : addressable m' (S - K) K).
    { apply ly_epi_addr_pw; [lia | lia | lia |].
      intros x Hx.
      assert (Hax : app_mem x) by (unfold app_mem; right; lia).
      apply (addr_munch _ mc m' x 1 (AWo x ltac:(lia) ltac:(lia)) MUcc).
      intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
      pose proof (acl_sh_ge x (frb + 8 * 16) ltac:(lia)) as Hg. rewrite (sh_add8 frb 16 FR8) in Hg.
      cbn [outside]. split; [lia|]. split; [|split; [|exact I]].
      - apply (ly_epi_sh_not_app x frb 8 Hax). intros k Hk. apply FAP. lia.
      - apply (ly_epi_sh_not_app x fa 1 Hax). intros k Hk. apply PApp. lia. }
    assert (FR128 : rw_cells rsegs m' (bv_unsigned sp + -128) (CB 32 gj :: SAVES)).
    { apply (acl_rw _ mc m' _ _ FRc MUcc WMcc).
      intros x Hx. cbn [cells_size csize SAVES Nat.add] in Hx. ly_epi_out. }
    assert (FRm' : rw_cells rsegs m' (bv_unsigned sp + -96) SAVES).
    { pose proof (rw_cells_tail m' (bv_unsigned sp + -128) [CB 32 gj] SAVES FR128) as HT.
      cbn [cells_size csize Nat.add] in HT.
      replace (bv_unsigned sp + -128 + Z.of_nat 32) with (bv_unsigned sp + -96) in HT by lia. exact HT. }
    assert (BKm' : rw_cells rsegs m' (p + 18) [CB 32 LAY]).
    { apply (acl_rw _ mc m' _ _ BKc MUcc WMcc).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      pose proof (acl_app_in m (p + 18) 32 (x - (p + 18)) AR ltac:(lia)) as Hapx.
      replace (p + 18 + (x - (p + 18))) with x in Hapx by lia. unfold app_mem in Hapx.
      pose proof (fl_dj_out_r _ _ (p + 18) (p + 50) x HDdc
                    ltac:(unfold ctrl_lay_block_D; cbn [In]; right; left; reflexivity) ltac:(lia)) as Ho.
      cbn [outside app fp_w flat_map fp_w1] in Ho.
      destruct Ho as (_ & _ & _ & _ & _ & Hf1 & Hfr1 & _).
      cbn [outside]. split; [lia|]. split; [|split; [|exact I]].
      - intros Hc. apply Hfr1. lia.
      - intros Hc. apply Hf1. lia. }
    assert (STm' : stk rsegs m' (S - K) S).
    { apply (stk_merge rsegs m' (S - K) (bv_unsigned sp + -128) S).
      - exact (stk_mono mc m' _ _ STc WMcc RMcc).
      - pose proof (stk_of_rw_cells rsegs m' _ _ FR128) as HS.
        cbn [cells_size csize Nat.add SAVES] in HS.
        replace (bv_unsigned sp + -128 + Z.of_nat 128) with S in HS by lia. exact HS.
      - lia. }
    assert (ACm' : asan_cells m').
    { apply (fl_asan_cells _ mc m' ACc MUcc). intros x Hx. unfold RT_LO, RT_HI in Hx. ly_epi_out. }
    pose proof (shadow_rw_mono mc m' SRc WMcc RMcc) as SRm'.
    assert (SUBcc : sub_fp [(shadow_addr frb, shadow_addr frb + 16); (frb, frb + 8); (fa, fa + 1)]
      (ctrl_lay_block_W p S ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (S - K), shadow_addr S)])).
    { unfold sub_fp, ctrl_lay_block_W. intros x H.
      cbn [outside app fp_w flat_map fp_w1] in H.
      destruct H as (_ & _ & _ & _ & _ & _ & _ & Hf1 & Hfr1 & Hsh1 & _).
      cbn [outside]. split; [|split; [|split; [|exact I]]].
      - intros Hc. apply Hsh1. lia.
      - intros Hc. apply Hfr1. lia.
      - intros Hc. apply Hf1. lia. }
    assert (SUBmu : sub_fp [(shadow_addr frb, shadow_addr frb + 16); (frb, frb + 8); (fa, fa + 1)]
      ([(p + 18, p + 50); (S - K, S)] ++ lay_X)).
    { unfold sub_fp, lay_X. intros x H.
      cbn [outside app fp_w flat_map fp_w1] in H.
      destruct H as (_ & _ & _ & _ & _ & _ & _ & Hf1 & Hfr1 & Hsh1 & _).
      cbn [outside]. split; [|split; [|split; [|exact I]]].
      - intros Hc. apply Hsh1. lia.
      - intros Hc. apply Hfr1. lia.
      - intros Hc. apply Hf1. lia. }
    assert (FPm' : fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f)).
    { apply (fl_fp_free [0%nat; 1%nat] mc m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S)
               (ctrl_lay_block_D p f) _ FPc TLc MUcc WMcc SUBcc).
      - intros x Hx. ly_epi_out.
      - intros x Hx. right. exact (RMcc (wa x) (rd_of_stk mc FS (FS + FS_SIZE) (proj1 PStkH) x Hx)).
      - intros c Hc. apply ly_epi_cls_out. cbn [In] in Hc.
        destruct Hc as [<-|[<-|[]]].
        + refine (ly_epi_cls_keep _ mc m' 0%nat _ _ MUcc (Forall_inv HCLc)); intros x Hx; ly_epi_out.
        + refine (ly_epi_cls_clear _ mc m' 1%nat fa _ _ _ HFz MUcc (Forall_inv (Forall_inv_tail HCLc)));
            [intros x Hx; ly_epi_out | lia | intros x Hx Hne; ly_epi_out]. }
    pose proof (ly_epi_tls_free [0%nat; 1%nat] mc m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S)
                  (ctrl_lay_block_D p f) _ (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (S - K), shadow_addr S)])
                  FPc MUcc SUBcc TLc TLc) as TLm'.
    pose proof (munch_trans _ m mc m' MUc (munch_weaken _ _ mc m' SUBmu MUcc)) as MUm'.
    apply lay_tail.
    - exact FRm'.
    - exact MUm'.
    - exact WMc.
    - exact MIc.
    - exact STm'.
    - exact BKm'.
    - exact ACm'.
    - exact SRm'.
    - exact AW'.
    - exact FPm'.
    - exact TLm'.
  Qed.

  Lemma ly_epi : EPI_T.
  Proof.
    unfold EPI_T. intros mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23
      x28 x29 x30 x31 HFI LCH.
    destruct (Z.eq_dec sfr 0) as [E0|N0].
    - exact (ly_epi_real mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23
               x28 x29 x30 x31 HFI E0 LCH).
    - exact (ly_epi_side mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23
               x28 x29 x30 x31 HFI N0 LCH).
  Qed.

  (* ===== g copy, box result copy, k = 1 loop: ly_args, ly_cpy, ly_loop (insert below this line) ===== *)
  (* --- shared by ly_args, ly_cpy and ly_loop --- *)
  Lemma outside_app_l : forall A B x, outside (A ++ B) x -> outside A x.
  Proof.
    induction A as [|[lo hi] A IH]; intros B x H; cbn [app outside] in *; [exact I|].
    destruct H as [H1 H2]. split; [exact H1 | exact (IH B x H2)].
  Qed.

  (* The stack pointer of the body: S - 256 <= spc <= S - 128 in both frame cases. *)
  Lemma fk_spc : forall frb sfr spc j w120, FK frb sfr spc j w120 -> S - 256 <= spc <= S - 128.
  Proof using AW0 FL FP0 HAE HHM K9 MDP P0 Rf Rg Rmd Rp SP16 SR0 ST0 TM gb.
    clear DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 AF AR AP50 ARDJ ATM AG AMD AJ5 AJ6
      FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    intros frb sfr spc j w120 HK. pose proof SP2_facts as (_ & HAlo & HAhi).
    pose proof (fk_facts frb sfr spc j w120 HK) as (_ & _ & H3 & H4 & _).
    destruct HK as [(_ & E1 & E2) | (_ & _ & _ & E2 & _)]; lia.
  Qed.

  (* The output block and the window hold application bytes only: their writes miss every shadow byte. *)
  Lemma W_shadow_out : forall x, in_shadow x -> outside (ctrl_lay_block_W p S) x.
  Proof using AR FL HHM K9 MDP P0 Rf Rg Rmd Rp SP16 TM gb.
    clear ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 SR0 HAE AW0 AF AP50 ARDJ ATM AG
      AMD AJ5 AJ6 FP0 FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    intros x Hx. unfold ctrl_lay_block_W. cbn [outside].
    pose proof HHM as HHM'. unfold in_shadow, HIGHMEM_BEG, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in *.
    split; [lia|]. split; [|exact I]. intros Hin.
    assert (A : app_mem x).
    { replace x with (p + 18 + (x - (p + 18))) by lia. apply (acl_app_in m (p + 18) 32); [exact AR | lia]. }
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A. lia.
  Qed.

  (* One pair of ranges of an apart list. *)
  Lemma fp_dj_in : forall W D w d, fp_dj W D -> In w W -> In d D -> ly_dj (fst w) (snd w) (fst d) (snd d).
  Proof.
    intros W D w d H Hw Hd. unfold fp_dj in H. rewrite Forall_forall in H. specialize (H w Hw).
    rewrite Forall_forall in H. exact (H d Hd).
  Qed.

  (* Membership of a literal range in fp_w, ctrl_lay_block_D or ctrl_lay_block_W. *)
  Ltac in_list := cbn [fp_w fp_w1 flat_map app ctrl_lay_block_D ctrl_lay_block_W In];
    repeat first [left; reflexivity | right].

  (* The side-stack flag pointer word [frb + 120, frb + 128) of a side frame is apart from the function's writes W: it
     lies in the class-1 frames, below the window (fp: FS + FS_SIZE <= S - K) and apart from the output block (fp: D
     apart from fp_w). *)
  Lemma FI_out120 : forall frb sfr spc j w120, FK frb sfr spc j w120 -> sfr <> 0 ->
    forall x, frb + 120 <= x < frb + 128 -> outside (ctrl_lay_block_W p S) x.
  Proof.
    intros frb sfr spc j w120 HK Hs x Hx.
    destruct HK as [(E & _) | (Hj & Efr & _)]; [exfalso; exact (Hs E)|].
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & HFS & _ & _ & HDd).
    pose proof (fp_dj_in _ _ (p + 18, p + 50) (fs_frame FS 1 0, fs_frame FS 1 (fs_M 1)) HDd ltac:(in_list)
                  ltac:(in_list)) as D1.
    cbn [fst snd] in D1. unfold ly_dj in D1. clear HDd.
    replace (fs_M 1) with 8192 in * by reflexivity.
    unfold fs_frame, fs_B, FS_SIZE in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
    change (2 ^ 20) with 1048576 in *. change (2 ^ 1) with 2 in *.
    unfold ctrl_lay_block_W, CTRL_LAY_BLOCK_K in *. cbn [outside]. subst frb.
    clear -Hj Hx HFS D1. lia.
  Qed.

  (* FI survives writes inside the function's W (the window and the output block) whose side-stack bytes read back. *)
  Lemma FI_keep : forall mc mc' W' frb sfr spc j w120, FI mc frb sfr spc j w120 ->
    munch W' mc mc' -> wmono rsegs mc mc' -> sub_fp W' (ctrl_lay_block_W p S) ->
    (forall x, FS <= x < FS + FS_SIZE -> outside W' x \/ exists b, mrd rsegs mc' (wa x) = Some b) ->
    FI mc' frb sfr spc j w120.
  Proof.
    intros mc mc' W' frb sfr spc j w120 (HK & H120 & AC & SR & FP & TL & HA) MU WM Hs HRD.
    assert (SHo : forall x, in_shadow x -> outside W' x) by (intros x Hx; apply Hs, W_shadow_out, Hx).
    split; [exact HK|]. split; [|split; [|split; [|split; [|split]]]].
    - intros Hs0. apply (fl_bytes W' mc mc' _ _ (H120 Hs0) MU). intros x Hx. rewrite length_le8 in Hx.
      apply Hs. exact (FI_out120 frb sfr spc j w120 HK Hs0 x ltac:(cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia)).
    - apply (fl_asan_cells W' mc mc' AC MU). intros x Hx. apply (lay_out_rt W' x); [|exact Hx].
      intros y Hy. apply Hs. exact (outside_app_l _ _ y Hy).
    - exact (fl_shadow_rw W' mc mc' SR MU WM SHo).
    - exact (fl_fp_W [0%nat; 1%nat] mc mc' (bv_unsigned tp) FS (S - K) S _ _ W' FP MU WM Hs HRD).
    - unfold ctrl_lay_block_tls in *.
      exact (fl_tls_W [0%nat; 1%nat] mc mc' (bv_unsigned tp) FS (S - K) S _ _ W' _ FP MU Hs TL).
    - intros x Hx Hf. exact (fl_addressable W' mc mc' x 1 (HA x Hx Hf) MU SHo).
  Qed.

  Lemma outside_of_forall : forall W x, (forall a b, In (a, b) W -> ~ (a <= x < b)) -> outside W x.
  Proof.
    induction W as [|[lo hi] W IH]; intros x H; cbn [outside]; [exact I|].
    split; [apply H; left; reflexivity|]. apply IH. intros a b Hin. apply H. right. exact Hin.
  Qed.

  (* The shadow bytes of an addressable range apart from the window and from the class-0/1 side-stack bytes are
     outside the body footprint: the footprint's application ranges hold no shadow byte, and its shadow ranges are the
     shadow of the window and of the side-stack frames. *)
  Lemma LC_sh_out : forall q n, addressable m q n -> ly_dj (S - K) S q (q + n) ->
    (forall a b, In (a, b) (fp_w [0%nat; 1%nat] FS) -> ly_dj q (q + n) a b) ->
    forall i, 0 <= i < n -> outside ([(p + 18, p + 50); (S - K, S)] ++ lay_X) (shadow_addr (q + i)).
  Proof using AR FL FP0 HHM K9 MDP P0 Rf Rg Rmd Rp SP16 TM gb.
    clear ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 SR0 HAE AW0 AF AP50 ARDJ ATM AG
      AMD AJ5 AJ6 FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    unfold rs_hold in SP16.
    intros q n HA DW DF i Hi.
    pose proof (acl_app_in m q n i HA Hi) as Ay.
    pose proof (rt_app_shadow _ Ay) as Sy.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFS & _ & _ & _).
    clear P5.
    assert (NA : forall z, app_mem z -> z <> shadow_addr (q + i))
      by (intros z Hz E; rewrite E in Hz; exact (acl_app_not_shadow _ Hz Sy)).
    pose proof (DF (fs_frame FS 0 0) (fs_frame FS 0 (fs_M 0)) ltac:(in_list)) as DF0.
    pose proof (DF (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) ltac:(in_list)) as DF1.
    apply fl_out_app.
    - cbn [outside]. split; [|split; [|exact I]].
      + intros Hin. apply (NA (shadow_addr (q + i))); [|reflexivity].
        replace (shadow_addr (q + i)) with (p + 18 + (shadow_addr (q + i) - (p + 18))) by lia.
        apply (acl_app_in m (p + 18) 32); [exact AR | lia].
      + pose proof HHM as HHM'. clear -Sy HHM'.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
    - unfold lay_X. apply fl_out_app.
      + apply outside_of_forall. intros a b Hin Hab.
        cbn [fp_w fp_w1 flat_map app In] in Hin.
        unfold FS_SIZE in P4. unfold ly_dj in DF0, DF1. clear DF.
        unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B in *.
        change (Z.of_nat 0) with 0 in *. change (Z.of_nat 1) with 1 in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ (15 - 0)) with 32768 in *.
        change (2 ^ (15 - 1)) with 16384 in *. change (2 ^ (14 - 0)) with 16384 in *.
        change (2 ^ (14 - 1)) with 8192 in *. change (2 ^ 0) with 1 in *. change (2 ^ 1) with 2 in *.
        change (2 ^ 15) with 32768 in *.
        destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-;
          first
          [ apply (NA (shadow_addr (q + i))); [apply P4; clear -Hab; lia | reflexivity]
          | rewrite sh_range in Hab by (clear -P2; Z.div_mod_to_equations; lia); clear -Hab DF0 DF1 Hi; lia ].
      + cbn [outside]. split; [|exact I].
        rewrite sh_range by (pose proof SP16; unfold CTRL_LAY_BLOCK_K; Z.div_mod_to_equations; lia).
        unfold ly_dj in DW. clear -DW Hi. lia.
  Qed.

  (* A data range addressable at entry stays addressable across the body (LC's footprint misses its shadow). *)
  Lemma LC_addr : forall mc gj X q n, LC mc gj X -> addressable m q n -> ly_dj (S - K) S q (q + n) ->
    (forall a b, In (a, b) (fp_w [0%nat; 1%nat] FS) -> ly_dj q (q + n) a b) -> addressable mc q n.
  Proof.
    intros mc gj X q n (_ & _ & MU & _) HA DW DF. exact (addr_munch _ m mc q n HA MU (LC_sh_out q n HA DW DF)).
  Qed.

  Lemma LC_addr_f : forall mc gj X, LC mc gj X -> addressable mc f 24.
  Proof.
    intros mc gj X LCH. apply (LC_addr mc gj X f 24 LCH AF DJ2). intros a b Hin.
    exact (fp_dj_in _ _ (f, f + 24) (a, b) (fl_fp_dj _ _ _ _ _ _ _ _ FP0) ltac:(in_list) Hin).
  Qed.

  Lemma LC_addr_p : forall mc gj X, LC mc gj X -> addressable mc (p + 18) 32.
  Proof.
    intros mc gj X LCH. apply (LC_addr mc gj X (p + 18) 32 LCH AR).
    { replace (p + 18 + 32) with (p + 50) by lia. exact DJ1. }
    intros a b Hin. replace (p + 18 + 32) with (p + 50) by lia.
    exact (fp_dj_in _ _ (p + 18, p + 50) (a, b) (fl_fp_dj _ _ _ _ _ _ _ _ FP0) ltac:(in_list) Hin).
  Qed.

  Lemma LC_addr_g : forall mc gj X, LC mc gj X -> g <> 0 -> ly_al fr <> 0 -> addressable mc g (ly_al fr).
  Proof.
    intros mc gj X LCH G0 A0. apply (LC_addr mc gj X g (ly_al fr) LCH (proj1 (AG G0 A0)) (DJ3g G0 A0)).
    intros a b Hin. exact (fp_dj_in _ _ (g, g + ly_al fr) (a, b) (FPG G0 A0) ltac:(left; reflexivity) Hin).
  Qed.

  (* After a call of __asan_memcpy into [D, D + N) inside the output block, run on the body stack spc: the carry
     invariant (with the new output bytes X') and the frame invariant hold.  The callee wrote only [D, D + N) and its
     own stack below spc (the window), so the saved registers, the stack below S - 128, the f record, the runtime cells,
     the shadow and the side stack keep. *)
  Lemma LC_FI_memcpy : forall mc m' gj X X' D N frb sfr spc j w120,
    LC mc gj X -> FI mc frb sfr spc j w120 -> p + 18 <= D -> D + N <= p + 50 -> 0 <= N ->
    munch [(D, D + N); (spc - ASAN_MEMCPY_K, spc)] mc m' -> wmono rsegs mc m' -> mem_inv rsegs m' ->
    stk rsegs m' (S - K) spc -> rw_cells rsegs m' (p + 18) [CB 32 X'] ->
    LC m' gj X' /\ FI m' frb sfr spc j w120.
  Proof using AMD AR ARDJ AW0 DB1 DB3 DBN DJ1 DJ2 DJ3m FL FP0 FPM HAE HHM K9 MDP P0 Rf Rg Rmd Rp SP16 SR0 ST0 TM gb.
    clear DJ3 DJ3g F8 F24 FB AOL P50 BLK DB2 GP MI0 AC0 AF AP50 ATM AG AJ5 AJ6 FPT FPG TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros mc m' gj X X' D N frb sfr spc j w120 (FR & ST & MU & WM & MI & BK & Bf) FIH HD1 HD2 HN MUc WMc MIc STc BKc.
    pose proof (fk_spc frb sfr spc j w120 (proj1 FIH)) as Hspc.
    pose proof DJ1 as D1. pose proof DJ2 as D2. pose proof DB1 as D3.
    unfold ly_dj, CTRL_LAY_BLOCK_K in D1, D2. unfold ly_dj in D3. unfold ASAN_MEMCPY_K in *.
    unfold CTRL_LAY_BLOCK_K in *.
    destruct (ly_rw_cb _ _ _ _ _ BKc) as (XL & XB & _).
    rs_hide_all.
    assert (RD : forall x, ~ outside [(D, D + N); (spc - 2224, spc)] x -> exists b, mrd rsegs m' (wa x) = Some b).
    { intros x Hx. cbn [outside] in Hx.
      destruct (Z_lt_le_dec x D) as [L|L]; [|destruct (Z_lt_le_dec x (D + N)) as [L2|L2]].
      - apply (rd_of_stk m' (S - 4512) spc STc). lia.
      - apply (rd_of_bytes m' (p + 18) X' XB). rewrite XL. lia.
      - apply (rd_of_stk m' (S - 4512) spc STc). lia. }
    assert (SUB : sub_fp [(D, D + N); (spc - 2224, spc)] (ctrl_lay_block_W p S)).
    { intros x Hx. unfold ctrl_lay_block_W, CTRL_LAY_BLOCK_K in Hx. cbn [outside] in *. lia. }
    split.
    - apply LC_intro.
      + apply (rw_cells_transport rsegs _ mc m' _ _ FR MUc WMc).
        unfold SAVES. cbn [disjoint_from cells_size csize]. unfold rs_hold in D1. lia.
      + apply (fl_stk _ mc m' _ _ ST MUc WMc). intros x Hx.
        destruct (Z_lt_le_dec x spc) as [L|L].
        * right. apply (rd_of_stk m' (S - 4512) spc STc). lia.
        * left. cbn [outside]. unfold rs_hold in D1. lia.
      + apply (munch_trans _ m mc m' MU). eapply munch_weaken; [|exact MUc].
        intros x Hx. cbn [app outside] in Hx |- *. lia.
      + exact (wmono_trans rsegs m mc m' WM WMc).
      + exact MIc.
      + exact BKc.
      + apply (bytes_at_transport rsegs _ mc m' f fr Bf MUc). rewrite FL. cbn [disjoint_from].
        unfold rs_hold in D2, D3. lia.
    - apply (FI_keep mc m' _ frb sfr spc j w120 FIH MUc WMc SUB). intros x _.
      destruct (rc_outside_dec [(D, D + N); (spc - 2224, spc)] x) as [Ho|Ho];
        [left; exact Ho | right; exact (RD x Ho)].
  Qed.

  Lemma stk_shrink : forall mm lo hi hi', stk rsegs mm lo hi -> lo <= hi' <= hi -> stk rsegs mm lo hi'.
  Proof. intros mm lo hi hi' (H0 & H1 & H) Hh. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

  (* An application byte apart from the output block, the window and the class-0/1 side-stack bytes is outside the
     body footprint. *)
  Lemma out_foot : forall x, app_mem x -> ~ (p + 18 <= x < p + 50) -> ~ (S - K <= x < S) ->
    (forall a b, In (a, b) (fp_w [0%nat; 1%nat] FS) -> ~ (a <= x < b)) ->
    outside ([(p + 18, p + 50); (S - K, S)] ++ lay_X) x.
  Proof.
    intros x Hx H1 H2 H3. apply fl_out_app; [cbn [outside]; tauto|].
    unfold lay_X. apply fl_out_app; [exact (outside_of_forall _ x H3)|].
    cbn [outside]. split; [|exact I].
    apply acl_sh_out; [exact Hx | pose proof HHM; unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in *; lia | exact HAE].
  Qed.

  (* Every byte from p + 18 to p + 50 is an application byte. *)
  Lemma app_blk : forall x, p + 18 <= x <= p + 50 -> app_mem x.
  Proof.
    intros x Hx. destruct (Z.eq_dec x (p + 50)) as [->|Hne]; [exact AP50|].
    replace x with (p + 18 + (x - (p + 18))) by lia. apply (acl_app_in m (p + 18) 32); [exact AR | lia].
  Qed.

  (* 0x85840: the g copy.  g = 0 or al = 0 (byte 17 of the f record): to the epilogue with LAY = BASE; else the
     checked loads of bytes 17 and 16 of the f record (al, ao) and checked_memcpy of the al bytes of g to p + 18 + ao,
     then to the epilogue with LAY.  (Image A has no range check of p + 18 + ao.) *)
  Lemma ly_args : EPI_T -> forall (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
    FI mc frb sfr spc j w120 -> LC mc gj BASE ->
    evt rsegs Q
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
               (Z_to_bv 64 (p + 18)) x22 x23
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85840) fc None mc (seg_rom rsegs)).
  Proof using AF AG AMD AOL AP50 AR ARDJ AW0 DB1 DB3 DBN DJ1 DJ2 DJ3g DJ3m F24 F8 FL FP0 FPG FPM GP HAE HHM K9 MDP
    MEMC P0 P50 Rf Rg Rmd Rp SP16 SR0 ST0 TM.
    clear DJ3 FB BLK DB2 MI0 AC0 ATM AJ5 AJ6 FPT TLS0 HSM MEMS BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros EPI mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 FIH LCH.
    pose proof (LC_addr_f mc gj BASE LCH) as AFc.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FBc).
    pose proof (rd_byte rsegs mc f fr 16 FBc ltac:(lia)) as R16.
    pose proof (rd_byte rsegs mc f fr 17 FBc ltac:(lia)) as R17.
    step. rewrite (rc_eqb g 0) by lia.
    destruct (Z.eqb_spec g 0) as [G0|G0]; cbv iota.
    { eapply EPI; [exact FIH|]. replace LAY with BASE; [exact LCH|].
      unfold LAY, BASE, ly_lay. rewrite (proj2 (Z.eqb_eq g 0) G0). reflexivity. }
    step.
    pose proof (acl_shadow mc f 24 17 1 (f + 17) AFc ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite Z.add_mod by lia; rewrite F8; cbn; lia) eq_refl) as SH.
    assert (RX : 0 <= f + 17 < 2^64) by lia.
    chk_core (f + 17) RX (Z_to_bv 5 12) SH pre_sr no_extra.
    step. step. rewrite (rc_u8_eqb fr 17 0) by lia.
    destruct (Z.eqb_spec (rc_u8 fr 17) 0) as [A0|A0]; cbv iota.
    { eapply EPI; [exact FIH|]. replace LAY with BASE; [exact LCH|].
      unfold LAY, BASE, ly_lay, ly_al. rewrite (proj2 (Z.eqb_eq _ 0) A0), orb_true_r. reflexivity. }
    step.
    pose proof (acl_shadow mc f 24 16 1 (f + 16) AFc ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite Z.add_mod by lia; rewrite F8; cbn; lia) eq_refl) as SH16.
    assert (RX16 : 0 <= f + 16 < 2^64) by lia.
    chk_core (f + 16) RX16 (Z_to_bv 5 13) SH16 pre_sr no_extra.
    step.
    pose proof (rc_u8_range fr 16) as RAO. pose proof (rc_u8_range fr 17) as RAL.
    step. step. step.
    destruct (GP G0 A0) as (GL & GBm & GD). pose proof (DJ3g G0 A0) as DJg.
    pose proof (AG G0 A0) as (AGa & AGe & AG7 & AP7).
    pose proof (FPG G0 A0) as FPg.
    unfold ly_dj in GD, DJg. unfold ly_ao, ly_al in *.
    rs_hide_all.
    assert (GBc : bytes_at rsegs mc g gb).
    { apply (fl_bytes _ m mc g gb GBm MU). intros x Hx. rewrite GL in Hx.
      apply out_foot.
      - replace x with (g + (x - g)) by lia. apply (acl_app_in m g (rc_u8 fr 17) (x - g) AGa). lia.
      - unfold rs_hold in GD. lia.
      - unfold rs_hold in DJg. unfold CTRL_LAY_BLOCK_K in DJg |- *. lia.
      - intros a b Hin. pose proof (fp_dj_in _ _ (g, g + rc_u8 fr 17) (a, b) FPg ltac:(left; reflexivity) Hin) as Dab.
        unfold ly_dj in Dab. cbn [fst snd] in Dab. lia. }
    pose proof (LC_addr_g mc gj BASE LCH G0 A0) as AGc. unfold ly_al in AGc.
    pose proof (LC_addr_p mc gj BASE LCH) as ARc.
    destruct (ly_rw_split3 rsegs mc (p + 18) BASE (Z.to_nat (rc_u8 fr 16)) (Z.to_nat (rc_u8 fr 17)) BK
                ltac:(lia)) as (B1 & B2 & B3).
    rewrite Z2Nat.id in B2, B3 by lia. rewrite Z2Nat.id in B3 by lia.
    pose proof (fk_spc frb sfr spc j w120 (proj1 FIH)) as Hspc.
    pose proof FIH as (_ & _ & ACc & SRc & _).
    assert (UAO : bv_unsigned (zxb (nth 16 fr (Z_to_bv 8 0))) = rc_u8 fr 16) by (apply rc_zxb_u).
    assert (UAL : bv_unsigned (zxb (nth 17 fr (Z_to_bv 8 0))) = rc_u8 fr 17) by (apply rc_zxb_u).
    rewrite UAO.
    assert (UA0 : bv_unsigned (Z_to_bv 64 (p + 18 + rc_u8 fr 16)) = p + 18 + rc_u8 fr 16)
      by (apply unsigned_lit; lia).
    assert (UG : bv_unsigned (Z_to_bv 64 g) = g) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 spc) = spc)
      by (apply unsigned_lit; pose proof HHM; unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in *;
          pose proof (zr_word sp) as Rsp; unfold inr64 in Rsp; lia).
    pose proof MEMC as HM. unfold asan_memcpy_contract in HM. cbv zeta in HM.
    eapply evt_cut.
    { eapply HM with (src := gb) (lo := S - K).
      all: rewrite ?UA0, ?UAL, ?UG, ?USP; unfold ASAN_MEMCPY_K.
      - exact GBc.
      - lia.
      - exact B2.
      - unfold rs_hold in GD. lia.
      - unfold rs_hold in GD. lia.
      - exact AGc.
      - apply (acl_addr_sub mc (p + 18) 32); [exact ARc | lia | lia | lia].
      - right. exact AGe.
      - right. apply app_blk. lia.
      - right. split; [exact AG7|].
        replace (p + 18 + rc_u8 fr 16 + 7) with (p + 25 + rc_u8 fr 16) by lia. exact AP7.
      - pose proof ARDJ as AJ. unfold rs_hold in AJ. unfold RT_LO, RT_HI in *. lia.
      - pose proof DJ1 as D1. unfold ly_dj, CTRL_LAY_BLOCK_K in D1. lia.
      - unfold rs_hold, CTRL_LAY_BLOCK_K in DJg. lia.
      - apply (stk_shrink mc (S - K) (S + -128) spc ST). unfold CTRL_LAY_BLOCK_K. lia.
      - unfold CTRL_LAY_BLOCK_K. lia.
      - exact HHM.
      - pose proof HAE. lia.
      - exact ACc.
      - exact SRc.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MUc & WMc & MIc & STc & RWc & _ & _ & _).
    rewrite UA0, UAL, USP in MUc. rewrite USP in STc. rewrite UA0, UAL in RWc. unfold ASAN_MEMCPY_K in MUc.
    assert (B1c : rw_cells rsegs m' (p + 18)
                    [CB (Z.to_nat (rc_u8 fr 16)) (firstn (Z.to_nat (rc_u8 fr 16)) BASE)]).
    { apply (rw_cells_transport rsegs _ mc m' _ _ B1 MUc WMc). cbn [disjoint_from cells_size csize].
      pose proof DJ1 as D1. unfold ly_dj, CTRL_LAY_BLOCK_K in D1. lia. }
    assert (B3c : rw_cells rsegs m' (p + 18 + rc_u8 fr 16 + rc_u8 fr 17)
                    [CB (32 - Z.to_nat (rc_u8 fr 16) - Z.to_nat (rc_u8 fr 17))
                       (skipn (Z.to_nat (rc_u8 fr 16) + Z.to_nat (rc_u8 fr 17)) BASE)]).
    { apply (rw_cells_transport rsegs _ mc m' _ _ B3 MUc WMc). cbn [disjoint_from cells_size csize].
      pose proof DJ1 as D1. unfold ly_dj, CTRL_LAY_BLOCK_K in D1. lia. }
    assert (GLn : length gb = Z.to_nat (rc_u8 fr 17)) by lia.
    pose proof (ly_rw_join3 rsegs _ _ _ _ _ _ _ _ _ B1c RWc B3c ltac:(lia) ltac:(lia) ltac:(lia)) as BJ.
    assert (EL : LAY = firstn (Z.to_nat (rc_u8 fr 16)) BASE ++ gb ++
                       skipn (Z.to_nat (rc_u8 fr 16) + Z.to_nat (rc_u8 fr 17)) BASE).
    { unfold LAY, ly_lay, ly_put, ly_ao, ly_al.
      rewrite (proj2 (Z.eqb_neq g 0) G0), (proj2 (Z.eqb_neq _ 0) A0). cbn [orb]. fold BASE.
      rewrite GLn. reflexivity. }
    rewrite <- EL in BJ.
    destruct (LC_FI_memcpy mc m' gj BASE LAY (p + 18 + rc_u8 fr 16) (rc_u8 fr 17) frb sfr spc j w120 LCH FIH
                ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MIc STc BJ) as (LC2 & FI2).
    rewrite (ret_pc_even 0x85884) by lia.
    eapply EPI; [exact FI2 | exact LC2].
  Qed.

  (* 0x8583c: checked_memcpy (__asan_memcpy) of the 32 bytes at src (BASE: the box result at frb + 32, or the k = 2 template) to the
     output block, then the g copy (ly_args). *)
  Lemma ly_cpy : EPI_T -> forall (mc : word -> option byte) (gj X sb : list byte) (src frb sfr spc j : Z)
      (w120 xra x5 x6 x7 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
    FI mc frb sfr spc j w120 -> LC mc gj X ->
    bytes_at rsegs mc src sb -> length sb = 32%nat -> sb = BASE -> 0 <= src < 2^64 ->
    (src + 32 <= p + 18 \/ p + 50 <= src) ->
    addressable mc src 32 -> app_mem (src + 32) -> (src + 32 <= S - K \/ spc <= src) ->
    evt rsegs Q
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               (Z_to_bv 64 (p + 18)) (Z_to_bv 64 src) (Z_to_bv 64 32) x13 x14 x15 x16 x17
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) x22 x23
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x8583c) fc None mc (seg_rom rsegs)).
  Proof using AF AG AMD AOL AP50 AR ARDJ AW0 DB1 DB3 DBN DJ1 DJ2 DJ3g DJ3m F24 F8 FL FP0 FPG FPM GP HAE HHM K9 MDP
    MEMC P0 P50 Rf Rg Rmd Rp SP16 SR0 ST0 TM.
    clear DJ3 FB BLK DB2 MI0 AC0 ATM AJ5 AJ6 FPT TLS0 HSM MEMS BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros EPI mc gj X sb src frb sfr spc j w120 xra x5 x6 x7 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31
      FIH LCH SB SL ESB RS DS AS AE DSW.
    pose proof (LC_addr_p mc gj X LCH) as ARc.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FBc).
    pose proof (fk_spc frb sfr spc j w120 (proj1 FIH)) as Hspc.
    pose proof FIH as (_ & _ & ACc & SRc & _).
    step.
    assert (U18 : bv_unsigned (Z_to_bv 64 (p + 18)) = p + 18) by (apply unsigned_lit; lia).
    assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
    assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 spc) = spc)
      by (apply unsigned_lit; pose proof HHM; unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in *;
          pose proof (zr_word sp) as Rsp; unfold inr64 in Rsp; lia).
    pose proof MEMC as HM. unfold asan_memcpy_contract in HM. cbv zeta in HM.
    eapply evt_cut.
    { eapply HM with (src := sb) (lo := S - K).
      all: rewrite ?U18, ?U32, ?US, ?USP; unfold ASAN_MEMCPY_K.
      - exact SB.
      - exact SL.
      - exact BK.
      - lia.
      - lia.
      - exact AS.
      - exact ARc.
      - right. exact AE.
      - right. apply app_blk. lia.
      - right. split; [apply (acl_app_in mc src 32 7 AS); lia | apply app_blk; lia].
      - pose proof ARDJ as AJ. unfold RT_LO, RT_HI in *. lia.
      - pose proof DJ1 as D1. unfold ly_dj, CTRL_LAY_BLOCK_K in D1. lia.
      - unfold CTRL_LAY_BLOCK_K in DSW. lia.
      - apply (stk_shrink mc (S - K) (S + -128) spc ST). unfold CTRL_LAY_BLOCK_K. lia.
      - unfold CTRL_LAY_BLOCK_K. lia.
      - exact HHM.
      - pose proof HAE. lia.
      - exact ACc.
      - exact SRc.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MUc & WMc & MIc & STc & RWc & _ & _ & _).
    rewrite U18, U32, USP in MUc. rewrite USP in STc. rewrite U18, U32 in RWc.
    change (Z.to_nat 32) with 32%nat in RWc.
    rewrite ESB in RWc.
    destruct (LC_FI_memcpy mc m' gj X BASE (p + 18) 32 frb sfr spc j w120 LCH FIH
                ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MIc STc RWc) as (LC2 & FI2).
    rewrite (ret_pc_even 0x85840) by lia.
    eapply ly_args; [exact EPI | exact FI2 | exact LC2].
  Qed.

  (* A one-byte store into the output block keeps FI. *)
  Lemma FI_store : forall mc gj X frb sfr spc j w120 a bs, FI mc frb sfr spc j w120 -> LC mc gj X ->
    length bs = 1%nat -> p + 18 <= a < p + 50 -> FI (write_to_mem mc (Z_to_bv 64 a) bs) frb sfr spc j w120.
  Proof using AMD AR ARDJ DB3 DBN DJ3m FL FP0 FPM HHM K9 MDP P0 P50 Rf Rg Rmd Rp SP16 TM gb.
    clear ST0 DJ1 DJ2 DJ3 DJ3g F8 F24 FB AOL BLK DB1 DB2 GP MI0 AC0 SR0 HAE AW0 AF AP50 ATM AG AJ5 AJ6 FPT FPG TLS0
      HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    intros mc gj X frb sfr spc j w120 a bs FIH (_ & _ & _ & _ & _ & BK & _) Hl Ha.
    destruct (ly_rw_cb _ _ _ _ _ BK) as (XL & XB & _).
    change (Z_to_bv 64 a) with (wa a).
    apply (FI_keep mc _ [(p + 18, p + 50)] frb sfr spc j w120 FIH).
    - apply munch_write; [exact (munch_refl _ mc) | lia | rewrite Hl; lia | cbn [inside]; rewrite Hl; left; lia].
    - exact (wmono_write rsegs mc mc (wa a) bs (wmono_refl rsegs mc)).
    - intros x Hx. unfold ctrl_lay_block_W in Hx. cbn [outside] in *. tauto.
    - intros x _. destruct (rc_outside_dec [(p + 18, p + 50)] x) as [Ho|Ho]; [left; exact Ho | right].
      apply (rd_mono_write mc mc (wa a) bs (rd_mono_refl mc)).
      apply (rd_of_bytes mc (p + 18) X XB). rewrite XL. cbn [outside] in Ho. lia.
  Qed.

  (* The shadow check of a 1-byte store at X (as chk_core): the slow path `andi r, X, 7` and `bge r, k` to the report
     call, else `j` back to the store, as the check passes. *)
  Ltac chk_st X RX r SH :=
    let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
    destruct SH as (k & RK & OK & KR);
    pre_sr X RX; steps_until_if; clear RK;
    unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
    lazymatch goal with
    | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
        let G := fresh "G" in
        enough (G : forall rr : word, evt segs Q (MS (bvmap_set r rr R) F B fc rv mm ro));
        [ let K0 := fresh "K0" in
          destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
          [ bjoin G r
          | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7;
            step;
            let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
            rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
            replace (X mod 8 <? bv_signed k) with true
              by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]);
            cbn [negb]; cbv iota; clear MB; step; bjoin G r ]
        | intros ?; simp_regs; clear OK KR ]
    end.

  (* 0x85768: the k = 1 loop head with n turns left at turn i (i + n = 16; a0 = s7 = p + 19 + 2 i, a2 = n, a3 = 122):
     the checked stores of 0 at s7 - 1 = p + 18 + 2 i and of 122 at s7 = p + 19 + 2 i, then a0 and s7 move by 2 and a2
     counts down: the next turn, or after 16 turns (LAY's base ly_desc) the g copy (ly_args). *)
  Lemma ly_loop : EPI_T -> forall (n i : nat) (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z)
      (w120 xra x5 x6 x7 x11 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    (i + n = 16)%nat -> (0 < n)%nat -> ly_k fr = 1 ->
    FI mc frb sfr spc j w120 -> LC mc gj (ly_dp i) ->
    evt rsegs Q
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               (Z_to_bv 64 (p + 19 + 2 * Z.of_nat i)) x11 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 122) x14 x15 x16 x17
               (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18)) x22
               (Z_to_bv 64 (p + 19 + 2 * Z.of_nat i))
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85768) fc None mc (seg_rom rsegs)).
  Proof using AF AG AMD AOL AP50 AR ARDJ AW0 DB1 DB3 DBN DJ1 DJ2 DJ3g DJ3m F24 F8 FL FP0 FPG FPM GP HAE HHM K9 MDP
    MEMC P0 P50 Rf Rg Rmd Rp SP16 SR0 ST0 TM.
    clear DJ3 FB BLK DB2 MI0 AC0 ATM AJ5 AJ6 FPT TLS0 HSM MEMS BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros EPI n. induction n as [|n IH];
      intros i mc gj frb sfr spc j w120 xra x5 x6 x7 x11 x14 x15 x16 x17 x22 x28 x29 x30 x31 Hin Hn K1 FIH LCH; [lia|].
    pose proof (LC_addr_p mc gj (ly_dp i) LCH) as ARc.
    step. replace (p + 19 + 2 * Z.of_nat i + -1) with (p + 18 + 2 * Z.of_nat i) by lia.
    assert (RX : 0 <= p + 18 + 2 * Z.of_nat i < 2^64) by lia.
    pose proof (acl_shadow mc (p + 18) 32 (2 * Z.of_nat i) 1 (p + 18 + 2 * Z.of_nat i) ARc ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(pose proof (Z.mod_pos_bound (p + 18 + 2 * Z.of_nat i) 8 eq_refl); lia) eq_refl) as SH.
    chk_st (p + 18 + 2 * Z.of_nat i) RX (Z_to_bv 5 15) SH.
    pose proof (LC_sok mc gj (ly_dp i) (2 * Z.of_nat i) LCH ltac:(lia)) as HS1.
    step.
    pose proof (LC_store mc gj (ly_dp i) (p + 18 + 2 * Z.of_nat i) (le1 (Z_to_bv 64 0)) LCH (length_le1 _)
                  ltac:(lia)) as LC1.
    pose proof (FI_store mc gj (ly_dp i) frb sfr spc j w120 (p + 18 + 2 * Z.of_nat i) (le1 (Z_to_bv 64 0)) FIH LCH
                  (length_le1 _) ltac:(lia)) as FI1.
    replace (Z.to_nat (p + 18 + 2 * Z.of_nat i - (p + 18))) with (2 * i)%nat in LC1 by lia.
    change (Z_to_bv 64 (p + 18 + 2 * Z.of_nat i)) with (wa (p + 18 + 2 * Z.of_nat i)) in LC1, FI1.
    remember (write_to_mem mc (wa (p + 18 + 2 * Z.of_nat i)) (le1 (Z_to_bv 64 0))) as mc1 eqn:E1.
    clear E1 HS1 LCH FIH ARc.
    pose proof (LC_addr_p mc1 gj _ LC1) as ARc1.
    assert (RX2 : 0 <= p + 19 + 2 * Z.of_nat i < 2^64) by lia.
    pose proof (acl_shadow mc1 (p + 18) 32 (2 * Z.of_nat i + 1) 1 (p + 19 + 2 * Z.of_nat i) ARc1 ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(pose proof (Z.mod_pos_bound (p + 19 + 2 * Z.of_nat i) 8 eq_refl); lia)
      ltac:(lia)) as SH2.
    chk_core (p + 19 + 2 * Z.of_nat i) RX2 (Z_to_bv 5 14) SH2 pre_sr no_extra.
    pose proof (LC_sok mc1 gj _ (2 * Z.of_nat i + 1) LC1 ltac:(lia)) as HS2.
    step.
    pose proof (LC_store mc1 gj _ (p + 18 + (2 * Z.of_nat i + 1)) (le1 (Z_to_bv 64 122)) LC1 (length_le1 _)
                  ltac:(lia)) as LC2.
    pose proof (FI_store mc1 gj _ frb sfr spc j w120 (p + 18 + (2 * Z.of_nat i + 1)) (le1 (Z_to_bv 64 122)) FI1 LC1
                  (length_le1 _) ltac:(lia)) as FI2.
    replace (Z.to_nat (p + 18 + (2 * Z.of_nat i + 1) - (p + 18))) with (2 * i + 1)%nat in LC2 by lia.
    change (Z_to_bv 64 (p + 18 + (2 * Z.of_nat i + 1))) with (wa (p + 18 + (2 * Z.of_nat i + 1))) in LC2, FI2.
    remember (write_to_mem mc1 (wa (p + 18 + (2 * Z.of_nat i + 1))) (le1 (Z_to_bv 64 122))) as mc2 eqn:E2.
    clear E2 HS2 LC1 FI1 ARc1.
    change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in LC2.
    change (le1 (Z_to_bv 64 122)) with [Z_to_bv 8 122] in LC2.
    rewrite (ly_dp_step i ltac:(lia)) in LC2.
    step. step. step. step.
    rewrite (ly_eqb_near (Z.of_nat (Datatypes.S n) + -1) 0) by lia.
    destruct (Nat.eq_dec n 0) as [N0|N0].
    - subst n. replace (Z.of_nat 1 + -1 =? 0) with true by reflexivity. cbn [negb]. step.
      assert (I15 : i = 15%nat) by lia. subst i.
      assert (EB : BASE = ly_desc) by (unfold BASE, ly_base; rewrite K1; reflexivity).
      rewrite ly_dp_16, <- EB in LC2.
      eapply ly_args; [exact EPI | exact FI2 | exact LC2].
    - replace (Z.of_nat (Datatypes.S n) + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb].
      replace (Z.of_nat (Datatypes.S n) + -1) with (Z.of_nat n) by lia.
      replace (p + 19 + 2 * Z.of_nat i + 2) with (p + 19 + 2 * Z.of_nat (Datatypes.S i)) by lia.
      eapply (IH (Datatypes.S i)); [lia | lia | exact K1 | exact FI2 | exact LC2].
  Qed.


  (* ===== dispatch: BOXARM_T, ly_dispatch (insert below this line) ===== *)
  (* Stage statement at the box arms' join (pc 0x85818), proved by ly_box: a1 = b = ly_bb k (k = 3 .. 9), the other
     registers as at the dispatch (DISP_T: s6 = md, s7 = p). *)
  Definition BOXARM_T : Prop :=
    forall (b : Z) (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    b = ly_bb (ly_k fr) -> 3 <= ly_k fr <= 9 ->
    FI mc frb sfr spc j w120 -> LC mc gj ly_zero -> addressable mc (frb + 32) 32 ->
    evt rsegs Q
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2)
               x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
               (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md) (Z_to_bv 64 p)
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85818) fc None mc (seg_rom rsegs)).

  (* A find_segment hit lies inside a segment of the list. *)
  Lemma ly_fs_in : forall (l : list Segment) x n seg, find_segment l x n = Some seg ->
    In seg l /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
  Proof.
    induction l as [|s l IH]; intros x n seg H; cbn in H; [discriminate|].
    match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
    - injection H as <-. apply andb_prop in E as [_ E2]. apply Z.leb_le in E2.
      split; [left; reflexivity | exact E2].
    - destruct (IH x n seg H) as (H1 & H2). split; [right; exact H1 | exact H2].
  Qed.

  (* Every read-only byte of the image lies below 0x5fe000, the top of its last segment. *)
  Lemma ly_ro_low : forall x, 0 <= x < 2^64 -> ro_addr rsegs (wa x) = true -> x < 0x5fe000.
  Proof.
    intros x Hx H. unfold ro_addr, wa in H. rewrite (unsigned_lit x Hx) in H.
    destruct (find_segment rsegs x 1) as [seg|] eqn:E; [|discriminate H].
    destruct (ly_fs_in rsegs x 1 seg E) as (Hin & Hhi).
    assert (C : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in C. specialize (C seg Hin). apply Z.leb_le in C. lia.
  Qed.

  (* 0x85718: the checked load of the kind byte k at f + 2, the k > 9 check and the jump table at 0x211b4 (image words:
     k = 0 -> 0x85840, 1 -> 0x85758, 2 -> 0x857d0, 3 -> 0x85818 with a1 = 0, 4 -> 0x857c0, 5 -> 0x857fc, 6 -> 0x85804,
     7 -> 0x857f4, 8 -> 0x85814, 9 -> 0x857c8).  k = 0: the g copy (ly_args) with
     BASE = ly_zero; k = 1: the loop (ly_loop); k = 2: the checked 8-byte load of the template pointer at f + 8 and the
     copy of the 32 template bytes (ly_cpy); k = 3 .. 9: a1 = ly_bb k, then the box arms' join (BOXARM_T).  Every shadow
     check passes, as the f record is addressable. *)
  Lemma ly_dispatch : EPI_T -> BOXARM_T -> DISP_T.
  Proof using AF AG AMD AOL AP50 AR ARDJ ATM AW0 DB1 DB2 DB3 DBN DJ1 DJ2 DJ3 DJ3g DJ3m F24 F8 FL FP0 FPG FPM FPT GP
    HAE HHM K9 MDP MEMC P0 P50 Rf Rg Rmd Rp SP16 SR0 ST0 TM.
    clear FB BLK MI0 AC0 AJ5 AJ6 TLS0 HSM MEMS BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros EPI BX. unfold BOXARM_T in BX. unfold DISP_T.
    intros mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
    repeat lazymatch goal with |- _ -> _ => let H := fresh "HD" in intro H end.
    lazymatch goal with H : FI mc frb sfr spc j w120 |- _ => rename H into FIH end.
    lazymatch goal with H : LC mc gj ly_zero |- _ => rename H into LCH end.
    lazymatch goal with H : addressable mc (frb + 32) 32 |- _ => rename H into AFR end.
    pose proof (LC_addr_f mc gj ly_zero LCH) as AFc.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FBc).
    pose proof (fk_spc frb sfr spc j w120 (proj1 FIH)) as Hspc.
    pose proof (rd_byte rsegs mc f fr 2 FBc ltac:(lia)) as R2.
    (* the checked load of k at f + 2, and k <= 9 *)
    step.
    pose proof (acl_shadow mc f 24 2 1 (f + 2) AFc ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite Z.add_mod by lia; rewrite F8; cbn; lia) eq_refl) as SH2.
    assert (RX2 : 0 <= f + 2 < 2^64) by lia.
    chk_core (f + 2) RX2 (Z_to_bv 5 12) SH2 pre_sr no_extra.
    step. clear R2. step. step. rewrite (rc_u8_gtu fr 2 9) by lia.
    replace (9 <? rc_u8 fr 2) with false by (symmetry; apply Z.ltb_ge; unfold ly_k in K9; lia). cbv iota.
    assert (KR : 0 <= ly_k fr) by (unfold ly_k; pose proof (rc_u8_range fr 2); lia).
    assert (KC : ly_k fr = 0 \/ ly_k fr = 1 \/ ly_k fr = 2 \/ 3 <= ly_k fr <= 9) by lia.
    destruct KC as [KE|[KE|[KE|KB]]].
    - (* k = 0: the g copy, BASE = ly_zero *)
      rewrite (rc_zxb_lit fr 2 _ KE). do 8 step.
      eapply ly_args; [exact EPI | exact FIH |].
      replace BASE with ly_zero; [exact LCH|]. unfold BASE, ly_base. rewrite KE. reflexivity.
    - (* k = 1: the loop setup at 0x85758 (s7 = a0 = p + 19, a2 = 16, a3 = 122), then the loop at turn 0 *)
      rewrite (rc_zxb_lit fr 2 _ KE). do 8 step. step. step. step. step.
      replace (Z_to_bv 64 (p + 19)) with (Z_to_bv 64 (p + 19 + 2 * Z.of_nat 0)) by (f_equal; lia).
      change (Z_to_bv 64 16) with (Z_to_bv 64 (Z.of_nat 16)).
      eapply (ly_loop EPI 16 0); [lia | lia | exact KE | exact FIH | exact LCH].
    - (* k = 2: the checked 8-byte load of the template pointer tm at f + 8, then the copy of tb from tm *)
      rewrite (rc_zxb_lit fr 2 _ KE). do 8 step.
      destruct (TM KE) as (T32 & TL & RO).
      step.
      pose proof (rt_shadow_rd mc f 24 [] AFc (fun _ _ => I)) as HSR.
      destruct (asan_shadow_read rsegs mc ASAN_K f 24 [] 8 HSR ltac:(lia)) as (k8 & RK8 & BK8).
      pose proof (asan_check_8 rsegs mc ASAN_K f 24 8 k8 (rt_addressable mc f 24 AFc) (rt_rt3 mc f 24 AFc)
                    ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_mod by lia; rewrite F8; reflexivity) BK8) as K8.
      pose proof (rc_signed0_unsigned0 k8 K8) as K8u. clear HSR BK8 K8.
      assert (RX8 : 0 <= f + 8 < 2^64) by lia.
      pre_sr (f + 8) RX8. steps_until_if. clear RK8.
      unfold zxb. rewrite K8u, (rc_eqb 0 0) by lia. cbn [Z.eqb negb]. cbv iota.
      destruct (ly_rd8 rsegs mc f fr FBc FL) as (L & EL & HR).
      step. rewrite (ly_ld8 fr L FL EL). clear HR.
      step. step. step.
      pose proof (ly_le_range (firstn 8 (skipn 8 fr))) as TR.
      rewrite length_firstn, length_skipn, FL in TR.
      change (256 ^ Z.of_nat (Nat.min 8 (24 - 8))) with (2^64) in TR.
      assert (TM0 : 0 <= ly_tm fr < 2^64) by (unfold ly_tm; lia).
      pose proof (DJ3 KE) as DW. pose proof (DB2 KE) as DP. unfold ly_dj in DW, DP.
      (* tm + 31 is a read-only image byte, so tm + 32 is an application byte below LOWMEM_END *)
      destruct (nth_error tb 31) as [b31|] eqn:E31; [|apply nth_error_None in E31; lia].
      pose proof (ro_bytes_nth rsegs tb (ly_tm fr) 31 b31 RO E31) as (_ & RA).
      pose proof (ly_ro_low (ly_tm fr + Z.of_nat 31) ltac:(lia) RA) as LO.
      eapply ly_cpy; [exact EPI | exact FIH | exact LCH | | exact TL | | exact TM0 | lia | | | lia].
      + apply ro_bytes_at; [exact MI | lia | rewrite TL; lia | exact RO].
      + unfold BASE, ly_base. rewrite KE. reflexivity.
      + apply (LC_addr mc gj ly_zero (ly_tm fr) 32 LCH (ATM KE) (DJ3 KE)). intros a c Hin.
        exact (fp_dj_in _ _ (ly_tm fr, ly_tm fr + 32) (a, c) (FPT KE) ltac:(left; reflexivity) Hin).
      + unfold app_mem, LOWMEM_END. left. lia.
    - (* k = 3 .. 9: a1 = ly_bb k, then the box arms' join *)
      assert (KC : ly_k fr = 3 \/ ly_k fr = 4 \/ ly_k fr = 5 \/ ly_k fr = 6 \/ ly_k fr = 7 \/ ly_k fr = 8 \/
                   ly_k fr = 9) by lia.
      destruct KC as [KE|[KE|[KE|[KE|[KE|[KE|KE]]]]]]; rewrite (rc_zxb_lit fr 2 _ KE); do 8 step;
        repeat lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x85818) _ _ _ _) => fail | _ => step end;
        (eapply BX; [unfold ly_bb; rewrite KE; reflexivity | exact KB | exact FIH | exact LCH | exact AFR]).
  Qed.


  (* ===== entry and fwords bridge: ly_pro (insert below this line) ===== *)

  (* The class-0 and class-1 side stacks in numbers (fs_hint / fs_flag / fs_frame of asan_stack_malloc_c.v).
     (as the image-B pro_num) *)
  Lemma lay_num :
    fs_hint FS 0 = FS /\ fs_hint FS 1 = FS + 8 /\ fs_M 0 = 16384 /\ fs_M 1 = 8192 /\ fs_B 1 = 128 /\
    (forall jj, fs_flag FS 0 jj = FS + 4096 + jj) /\ (forall jj, fs_flag FS 1 jj = FS + 20480 + jj) /\
    (forall jj, fs_frame FS 0 jj = FS + 36864 + 64 * jj) /\
    (forall jj, fs_frame FS 1 jj = FS + 1085440 + 128 * jj).
  Proof.
    unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
    repeat split; intros; lia.
  Qed.

  (* A byte the run did not write keeps its value. *)
  Lemma munch_mrd_out : forall W m1 m2 x, munch W m1 m2 -> 0 <= x < 2^64 -> outside W x ->
    mrd rsegs m2 (wa x) = mrd rsegs m1 (wa x).
  Proof.
    intros W m1 m2 x MU Hx Hout. unfold mrd. rewrite (MU (wa x)); [reflexivity|].
    rewrite wa_unsigned by lia. exact Hout.
  Qed.

  Lemma bytes_at_1 : forall (mm : word -> option byte) (A : Z) (b : byte),
    bytes_at rsegs mm A [b] -> mrd rsegs mm (wa A) = Some b.
  Proof.
    intros mm A b (_ & _ & H). pose proof (H 0%nat ltac:(cbn [length]; lia)) as E.
    cbn [Z.of_nat nth_error] in E. rewrite Z.add_0_r in E. exact E.
  Qed.

  (* A cell followed by a cell block at its end is one block. *)
  Lemma lay_rw_cons : forall (mm : word -> option byte) (A : Z) (c : cell) (cs : list cell),
    rw_cells rsegs mm A [c] -> rw_cells rsegs mm (A + Z.of_nat (csize c)) cs -> rw_cells rsegs mm A (c :: cs).
  Proof.
    intros mm A c cs [[[Hw1 _] Hb1] (Ha1 & Hn1 & Hr1)] [[Hw2 Hb2] (Ha2 & Hn2 & Hr2)].
    cbn [cells_bytes cells_size] in Hb1, Hn1, Hr1. rewrite app_nil_r in Hb1. rewrite Nat.add_0_r in Hn1, Hr1.
    pose proof (cbytes_length c Hw1) as Hl.
    split; [split; [split; assumption |] |].
    - cbn [cells_bytes]. apply (proj2 (bytes_at_app rsegs mm A _ _)). split; [exact Hb1|]. rewrite Hl. exact Hb2.
    - cbn [cells_size]. split; [exact Ha1|]. split; [rewrite Nat2Z.inj_add; lia|].
      intros i Hi. rewrite Nat2Z.inj_add in Hi.
      destruct (Z.lt_ge_cases i (Z.of_nat (csize c))) as [L|G].
      + apply Hr1. lia.
      + replace (A + i) with (A + Z.of_nat (csize c) + (i - Z.of_nat (csize c))) by lia. apply Hr2. lia.
  Qed.

  (* The class-c state that fl_fp_free asks for at mm: the hint word and the flag array, each byte 0 or 1. *)
  Definition lay_cls (mm : word -> option byte) (c : nat) : Prop :=
    (exists h', bytes_at rsegs mm (fs_hint FS c) (le8 h')) /\
    (exists flags', bytes_at rsegs mm (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags').

  (* fp and the tls premise carried from m1 to m2 across writes Wm inside the function's footprint that leave the
     side stack's header points FS + 80 .. FS + 104 alone, given the class-0/1 state at m2. *)
  Lemma lay_fp_tls : forall (m1 m2 : word -> option byte) (Wm : list ivl),
    fp [0%nat; 1%nat] m1 (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) ->
    ctrl_lay_block_tls m1 (bv_unsigned tp) FS (S - K) S ->
    munch Wm m1 m2 -> wmono rsegs m1 m2 -> rd_mono m1 m2 ->
    sub_fp Wm (ctrl_lay_block_W p S ++ lay_X) ->
    (forall x, FS + 80 <= x < FS + 104 -> outside Wm x) ->
    (forall c, In c [0%nat; 1%nat] -> lay_cls m2 c) ->
    fp [0%nat; 1%nat] m2 (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
    ctrl_lay_block_tls m2 (bv_unsigned tp) FS (S - K) S.
  Proof.
    intros m1 m2 Wm FP1 TL1 MU WM RM Hs O88 Hcls.
    split.
    - apply (fl_fp_free [0%nat; 1%nat] m1 m2 (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S)
               (ctrl_lay_block_D p f) Wm FP1 TL1 MU WM Hs O88); [|exact Hcls].
      intros x Hx. right. apply RM.
      pose proof FP1 as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & P5) & _).
      exact (rd_of_stk _ _ _ P5 x Hx).
    - exact (ly_epi_tls_free [0%nat; 1%nat] m1 m2 (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S)
               (ctrl_lay_block_D p f) Wm (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (S - K), shadow_addr S)])
               FP1 MU Hs TL1 TL1).
  Qed.

  (* A byte of the side stack's header [FS, FS + 36864) is outside Wf unless it is the class-1 hint word or the
     request's flag byte. *)
  Lemma lay_hdr_out_Wf : forall frb sfr spc j n w120 x, FK frb sfr spc j w120 ->
    FS <= x < FS + 36864 -> ~ (fs_hint FS 1 <= x < fs_hint FS 1 + 8) ->
    ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + n) -> outside (Wf frb j n) x.
  Proof using AW0 FL FP0 HAE HHM K9 MDP P0 Rf Rg Rmd Rp SP16 SR0 ST0 TM gb.
    clear DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 AF AR AP50 ARDJ ATM AG AMD AJ5 AJ6
      FPT FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    intros frb sfr spc j n w120 x HK Hx Hh Hf.
    destruct (fk_facts frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _ & _).
    pose proof SP2_facts as (_ & _ & SP2hi).
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFS & _).
    unfold FS_SIZE in HFS, P4.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    assert (Hap : app_mem x) by (apply P4; lia).
    assert (Esh : shadow_addr frb + 16 = shadow_addr (frb + 128))
      by (replace (frb + 128) with (frb + 8 * 16) by lia; symmetry; apply sh_add8; exact FR8).
    unfold Wf. cbn [outside].
    split; [lia|]. split; [exact Hh|]. split; [exact Hf|]. split; [lia|].
    split; [| exact I].
    rewrite Esh. apply acl_sh_out; [exact Hap | lia | unfold APPMEM_END; lia].
  Qed.

  (* The class-1 flag array after the frame request: m's array with the byte of the frame j set to 1 when n = 1, the
     rest untouched (Wf writes only [fs_flag FS 1 j, fs_flag FS 1 j + n) of it).  (port of the image-B pro_cls1) *)
  Lemma lay_cls1 : forall frb sfr spc j n w120 (mc : word -> option byte),
    FK frb sfr spc j w120 -> 0 <= n <= 1 -> (n = 0 \/ 0 <= j < fs_M 1) -> munch (Wf frb j n) m mc ->
    (n = 1 -> bytes_at rsegs mc (fs_flag FS 1 j) [Z_to_bv 8 1]) ->
    exists flags', bytes_at rsegs mc (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
      Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'.
  Proof.
    intros frb sfr spc j n w120 mc HK Hn Hnj MU HFL.
    pose proof lay_num as (NH0 & NH1 & NM0 & NM1 & NB1 & NF0 & NF1 & NR0 & NR1).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & HCL & HFS & _).
    unfold FS_SIZE in HFS.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    apply Forall_inv_tail in HCL. apply Forall_inv in HCL.
    destruct HCL as (_ & h & flags & _ & Hfl & Hln & Hfb).
    rewrite NM1 in Hln.
    assert (OUT : forall x, FS + 20480 <= x < FS + 28672 -> ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + n) ->
      outside (Wf frb j n) x).
    { intros x Hx Hne. apply (lay_hdr_out_Wf frb sfr spc j n w120 x HK); [lia | rewrite NH1; lia | exact Hne]. }
    assert (Hn01 : n = 0 \/ n = 1) by lia.
    destruct Hn01 as [-> | ->].
    - exists flags. split; [|split; [rewrite NM1; exact Hln | exact Hfb]].
      apply (fl_bytes _ m mc _ _ Hfl MU). intros x Hx. rewrite (NF1 0) in Hx.
      apply OUT; lia.
    - destruct Hnj as [E|Hj]; [lia|]. rewrite NM1 in Hj.
      pose proof (bytes_at_1 _ _ _ (HFL eq_refl)) as Hfj.
      destruct Hfl as (Ba & Bl & BH).
      set (J := Z.to_nat j).
      assert (HJlt : (J < length flags)%nat) by (unfold J; clear - Hj Hln; lia).
      assert (EjZ : Z.of_nat J = j) by (unfold J; rewrite Z2Nat.id; clear - Hj; lia).
      assert (Ej : fs_flag FS 1 j = fs_flag FS 1 0 + Z.of_nat J)
        by (rewrite (NF1 j), (NF1 0); clear - EjZ; lia).
      assert (HLfir : length (firstn J flags) = J) by (apply firstn_length_le; clear - HJlt; lia).
      assert (HLsk : length (skipn (Datatypes.S J) flags) = (length flags - Datatypes.S J)%nat)
        by (apply length_skipn).
      exists (firstn J flags ++ Z_to_bv 8 1 :: skipn (Datatypes.S J) flags).
      assert (HL : length (firstn J flags ++ Z_to_bv 8 1 :: skipn (Datatypes.S J) flags) = length flags)
        by (rewrite length_app; cbn [length]; rewrite HLfir, HLsk; clear -HJlt; lia).
      assert (OTH : forall i, (i < length flags)%nat -> i <> J ->
        mrd rsegs mc (wa (fs_flag FS 1 0 + Z.of_nat i)) = nth_error flags i).
      { intros i Hi Hne. rewrite <- (BH i Hi).
        apply (munch_mrd_out (Wf frb j 1) m mc); [exact MU | |].
        - rewrite (NF1 0). clear - Hi Hln HFS EK Rsp P1. lia.
        - apply OUT; [rewrite (NF1 0); clear - Hi Hln; lia|].
          rewrite Ej, (NF1 0). clear - Hne EjZ Hi Hln. lia. }
      split; [|split].
      + split; [exact Ba|]. split; [rewrite HL; exact Bl|].
        intros i Hi. rewrite HL in Hi.
        destruct (lt_eq_lt_dec i J) as [[Hlt|Heq]|Hgt].
        * rewrite nth_error_app1 by (rewrite HLfir; clear - Hlt; lia).
          rewrite nth_error_firstn. replace (Nat.ltb i J) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
          apply OTH; clear - Hi Hlt; lia.
        * subst i. rewrite nth_error_app2 by (rewrite HLfir; clear - HLfir; lia).
          rewrite HLfir, Nat.sub_diag. cbn [nth_error]. rewrite <- Ej. exact Hfj.
        * rewrite nth_error_app2 by (rewrite HLfir; clear - Hgt; lia). rewrite HLfir.
          destruct (i - J)%nat as [|d] eqn:Ed; [exfalso; clear -Hgt Ed; lia|].
          cbn [nth_error]. rewrite nth_error_skipn.
          replace (Datatypes.S J + d)%nat with i by (clear - Ed Hgt; lia).
          apply OTH; clear - Hi Hgt; lia.
      + rewrite HL, NM1. exact Hln.
      + apply Forall_app. split.
        * pose proof (firstn_skipn J flags) as Esp2. rewrite <- Esp2 in Hfb. apply Forall_app in Hfb.
          exact (proj1 Hfb).
        * apply Forall_cons; [right; reflexivity|].
          pose proof (firstn_skipn (Datatypes.S J) flags) as Esp2. rewrite <- Esp2 in Hfb.
          apply Forall_app in Hfb. exact (proj2 Hfb).
  Qed.

  (* The runtime state at the fwords entry (0x8569c), from the function entry m across the frame request's writes
     Wm (inside Wf, apart from the window's shadow): the window addressable, fp and the tls premise. *)
  Lemma lay_bi_rt : forall (Wm : list ivl) frb sfr spc j n w120 (mc : word -> option byte),
    FK frb sfr spc j w120 -> 0 <= n <= 1 -> (n = 0 \/ 0 <= j < fs_M 1) ->
    munch Wm m mc -> sub_fp Wm (Wf frb j n) -> wmono rsegs m mc -> rd_mono m mc ->
    (exists h, bytes_at rsegs mc (fs_hint FS 1) (le8 h)) ->
    (n = 1 -> bytes_at rsegs mc (fs_flag FS 1 j) [Z_to_bv 8 1]) ->
    (forall x, S - K <= x < S -> outside Wm (shadow_addr x)) ->
    addressable mc (S - K) K /\
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
    ctrl_lay_block_tls mc (bv_unsigned tp) FS (S - K) S.
  Proof using AW0 FL FP0 HAE HHM K9 MDP P0 Rf Rg Rmd Rp SP16 SR0 ST0 TLS0 TM gb.
    clear DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 AF AR AP50 ARDJ ATM AG AMD AJ5 AJ6
      FPT FPG FPM HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    intros Wm frb sfr spc j n w120 mc HK Hn Hnj MU Hsub WM RM HH HFL Hsh.
    pose proof (munch_weaken _ _ _ _ Hsub MU) as MUf.
    pose proof (lay_Wf_sub frb sfr spc j n w120 HK Hn Hnj) as SUBf.
    assert (SUBm : sub_fp Wm (ctrl_lay_block_W p S ++ lay_X)) by (intros x Hx; exact (Hsub x (SUBf x Hx))).
    pose proof lay_num as (NH0 & NH1 & NM0 & NM1 & NB1 & NF0 & NF1 & NR0 & NR1).
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & _ & _ & _ & HCL & _).
    apply Forall_inv in HCL. destruct HCL as (_ & h0 & fl0 & Hh0 & Hf0 & Hl0 & Hb0).
    rewrite NM0 in Hl0.
    assert (OH : forall x, FS <= x < FS + 20480 -> ~ (FS + 8 <= x < FS + 16) -> outside Wm x).
    { intros x Hx Hne. apply Hsub. apply (lay_hdr_out_Wf frb sfr spc j n w120 x HK); [lia | rewrite NH1; lia |].
      rewrite (NF1 j). destruct Hnj; lia. }
    assert (HCLS : forall c, In c [0%nat; 1%nat] -> lay_cls mc c).
    { intros c Hc. cbn [In] in Hc. destruct Hc as [<- | [<- | []]].
      - split; [exists h0 | exists fl0; split; [|split; [rewrite NM0; exact Hl0 | exact Hb0]]].
        + apply (fl_bytes _ m mc _ _ Hh0 MU). intros x Hx. rewrite length_le8, NH0 in Hx.
          change (Z.of_nat 8) with 8 in Hx. apply OH; lia.
        + apply (fl_bytes _ m mc _ _ Hf0 MU). intros x Hx. rewrite (NF0 0), Hl0 in Hx. apply OH; lia.
      - split; [exact HH | exact (lay_cls1 frb sfr spc j n w120 mc HK Hn Hnj MUf HFL)]. }
    destruct (lay_fp_tls m mc Wm FP0 TLS0 MU WM RM SUBm ltac:(intros x Hx; apply OH; lia) HCLS) as [FPc TLc].
    split; [|split; [exact FPc | exact TLc]].
    apply (addr_munch Wm m mc (S - K) K AW0 MU). intros i Hi. apply Hsh. lia.
  Qed.

  (* fp, the tls premise and the window's addressability outside the frame [frb, frb + 96), carried across the
     fwords stores (the window, the 3 header words, the frame's 12 shadow bytes) and the memset of the row. *)
  Lemma lay_fw_rt : forall frb sfr spc j w120 (mc mp : word -> option byte),
    FK frb sfr spc j w120 ->
    fp [0%nat; 1%nat] mc (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) ->
    ctrl_lay_block_tls mc (bv_unsigned tp) FS (S - K) S -> addressable mc (S - K) K ->
    munch [(S - K, S); (frb, frb + 24); (shadow_addr frb, shadow_addr frb + 12); (p + 18, p + 50)] mc mp ->
    wmono rsegs mc mp -> rd_mono mc mp ->
    fp [0%nat; 1%nat] mp (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f) /\
    ctrl_lay_block_tls mp (bv_unsigned tp) FS (S - K) S /\
    (forall x, S - K <= x < S -> (x < frb \/ frb + 96 <= x) -> addressable mp x 1).
  Proof using AR AW0 FL FP0 HAE HHM K9 MDP P0 Rf Rg Rmd Rp SP16 SR0 ST0 TM gb.
    clear DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FB AOL P50 BLK DB1 DB2 DB3 DBN GP MI0 AC0 AF AP50 ARDJ ATM AG AMD AJ5 AJ6 FPT
      FPG FPM TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros frb sfr spc j w120 mc mp HK FPc TLc AWc MU WM RM.
    destruct (fk_facts frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _ & _ & _ & _).
    pose proof SP2_facts as (_ & _ & SP2hi).
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    pose proof lay_num as (NH0 & NH1 & NM0 & NM1 & NB1 & NF0 & NF1 & NR0 & NR1).
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFS & _ & HWd & _).
    unfold FS_SIZE in HFS, P4.
    rs_hide_all.
    assert (E96 : shadow_addr frb + 12 = shadow_addr (frb + 96))
      by (replace (frb + 96) with (frb + 8 * 12) by lia; symmetry; apply sh_add8; exact FR8).
    (* the row is apart from the side stack's header (fp's W-disjointness) *)
    assert (X0 : ly_dj (p + 18) (p + 50) FS (FS + 36864)).
    { assert (IPW : In (p + 18, p + 50) (ctrl_lay_block_W p S))
        by (unfold ctrl_lay_block_W; cbn [In]; right; left; reflexivity).
      assert (IFS : In (FS, fs_frame FS 0 0) (fp_tls (bv_unsigned tp) DT TS C T DB k0 ++ [(FS, fs_frame FS 0 0)]))
        by (apply in_or_app; right; left; reflexivity).
      unfold fp_dj in HWd. rewrite Forall_forall in HWd. pose proof (HWd _ IPW) as H1.
      rewrite Forall_forall in H1. pose proof (H1 _ IFS) as H2. cbn [fst snd] in H2.
      rewrite (NR0 0) in H2. replace (FS + 36864 + 64 * 0) with (FS + 36864) in H2 by lia. exact H2. }
    assert (SUBd : sub_fp [(S - K, S); (frb, frb + 24); (shadow_addr frb, shadow_addr frb + 12); (p + 18, p + 50)]
                     (ctrl_lay_block_W p S ++ lay_X)).
    { intros x Hx. pose proof (lay_Wf_sub frb sfr spc j 0 w120 HK ltac:(lia) (or_introl eq_refl) x Hx) as Hf.
      unfold Wf in Hf. cbn [outside] in Hf. destruct Hf as (Hw & _ & _ & Hfr & Hsh & _).
      unfold ctrl_lay_block_W, lay_X in Hx. apply acl_out_app_inv in Hx. destruct Hx as (HW & _).
      cbn [outside] in HW. destruct HW as (_ & Hrow & _).
      cbn [outside]. split; [exact Hw|]. split; [lia|]. split; [lia|]. split; [exact Hrow | exact I]. }
    assert (OH : forall x, FS <= x < FS + 36864 ->
      outside [(S - K, S); (frb, frb + 24); (shadow_addr frb, shadow_addr frb + 12); (p + 18, p + 50)] x).
    { intros x Hx. assert (Hap : app_mem x) by (apply P4; lia).
      cbn [outside]. split; [lia|]. split; [lia|].
      split; [rewrite E96; apply acl_sh_out; [exact Hap | lia | unfold APPMEM_END; lia]|].
      split; [unfold ly_dj in X0; lia | exact I]. }
    assert (HCLS : forall c, In c [0%nat; 1%nat] -> lay_cls mp c).
    { intros c Hc. pose proof FPc as (DT' & TS' & C' & T' & DB' & k' & _ & _ & _ & _ & _ & HCL' & _).
      rewrite Forall_forall in HCL'.
      destruct (fl_cls_h _ mc mp FS c OH MU (HCL' c Hc)) as (_ & h & flags & Hh & Hf & Hl & Hb).
      split; [exists h; exact Hh | exists flags; split; [exact Hf | split; assumption]]. }
    destruct (lay_fp_tls mc mp _ FPc TLc MU WM RM SUBd ltac:(intros x Hx; apply OH; lia) HCLS) as [FPp TLp].
    split; [exact FPp|]. split; [exact TLp|].
    intros x Hx Hfx.
    assert (Hap : app_mem x).
    { replace x with (S - K + (x - (S - K))) by lia. apply (acl_app_in m (S - K) K); [exact AW0 | lia]. }
    pose proof (rt_app_shadow x Hap) as Hsx.
    apply (addr_munch _ mc mp x 1 (acl_addr_sub mc (S - K) K x 1 AWc ltac:(lia) ltac:(lia) ltac:(lia)) MU).
    intros i Hi. replace (x + i) with x by lia.
    cbn [outside].
    split.
    { apply (lay_sh_app_out _ (S - K) S Hsx). intros z Hz. replace z with (S - K + (z - (S - K))) by lia.
      apply (acl_app_in m (S - K) K); [exact AW0 | lia]. }
    split.
    { apply (lay_sh_app_out _ frb (frb + 24) Hsx). intros z Hz. replace z with (frb + (z - frb)) by lia.
      apply FAP. lia. }
    split; [rewrite E96; exact (acl_win_sh x frb (frb + 96) FR8 ltac:(lia))|].
    split; [| exact I].
    apply (lay_sh_app_out _ (p + 18) (p + 50) Hsx). intros z Hz. replace z with (p + 18 + (z - (p + 18))) by lia.
    apply (acl_app_in m (p + 18) 32); [exact AR | lia].
  Qed.

  (* 0x8569c -> 0x85718: the window store at SP2+24, the 3-word frame header at frb, the 12 shadow bytes
     (0xf1 x4, 0x00 x4, 0xf3 x4), then the checked memset of the row [p+18, p+50).  Hands ME over to KB. *)
  Lemma fwords : forall (frb sfr spc j n : Z) (w120 : word) (mc : word -> option byte)
      (xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Q,
    FK frb sfr spc j w120 -> 0 <= n <= 1 -> (n = 0 \/ 0 <= j < fs_M 1) ->
    BI (Wf frb j n) frb sfr w120 mc -> KB Q ->
    evt rsegs Q (MS (mkR xra (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
                       a0' a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) s5 (Z_to_bv 64 md) (Z_to_bv 64 p)
                       s8 (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 0x8569c) fc None mc (seg_rom rsegs)).
  Proof using AC0 AF AMD AP50 AR ARDJ AW0 BLK DB1 DB3 DBN DJ1 DJ2 DJ3m FB FL FP0 FPM HAE HHM K9 MDP MEMS P0 P50 Rf
    Rg Rmd Rp SP16 SR0 ST0 TM gb.
    clear DJ3 DJ3g F8 F24 AOL DB2 GP MI0 ATM AG AJ5 AJ6 FPT FPG TLS0 HSM MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros frb sfr spc j n w120 mc xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Q HK Hn Hnj HB HKB.
    pose proof SP2_facts as (SP2m & SP2lo & SP2hi).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts frb sfr spc j w120 HK) as (FR8 & FRlo & FRhi & Hspc & FW & FAP & FRA & SW12 & SHlo & SHhi).
    unfold LOWMEM_END in SHlo. unfold HIGHMEM_BEG in SHhi.
    assert (SHub : frb / 8 + ASAN_K + 12 <= 2 ^ 64) by lia.
    assert (S8 : S mod 8 = 0) by (pose proof SP16 as H16; clear -H16; Z.div_mod_to_equations; lia).
    rs_hide_all.
    assert (SKv : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    assert (Rfrb : 0 <= frb < 2 ^ 64).
    { pose proof (FAP 0 ltac:(lia)) as Hap0. rewrite Z.add_0_r in Hap0.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap0. lia. }
    assert (Rspc : 0 <= spc < 2 ^ 64) by (unfold rs_hold in Hspc; destruct Hspc as [E|E]; rewrite E; lia).
    destruct HB as (MU & WM & RM & MI & SV & F120 & AWc & FPc & TLc).
    pose proof (stk_mono m mc (S - K) S ST0 WM RM) as STK.
    unfold Wf in MU. unfold shadow_addr in MU.
    (* The run's own stores from mc (the window store, the 3 header words, the 12 frame-shadow bytes): it carries the
       side frame's word at frb + 120 (apart from all of them there), fp, the tls premise and the window's shadow
       outside the frame to the body entry. *)
    pose proof (munch_refl [(S - K, S); (frb, frb + 24); (frb / 8 + ASAN_K, frb / 8 + ASAN_K + 12)] mc) as MUc.
    pose proof (wmono_refl rsegs mc) as WMc. pose proof (rd_mono_refl mc) as RMc.
    (* window store at SP2 + 24 *)
    assert (HSw : store_ok rsegs mc (wa (SP2 + 24)) 8 = true)
      by (eapply wv_store_ok; [ intros ii Hii; apply STW0; unfold CTRL_LAY_BLOCK_K in *; lia
                              | exact WM | lia | lia ]).
    step. store_done.
    do 7 step.
    wst frb 8%nat. step. store_done.
    wst (frb + 8) 8%nat. step. store_done.
    wst (frb + 16) 8%nat. step. store_done.
    step. step.
    rewrite (unsigned_lit frb) by lia. rewrite rc_shr3.
    wst (frb / 8 + ASAN_K) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 1) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 2) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 3) 1%nat. step. store_done.
    step.
    wst (frb / 8 + ASAN_K + 8) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 9) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 10) 1%nat. step. store_done.
    wst (frb / 8 + ASAN_K + 11) 1%nat. step. store_done.
    step.
    (* capture the 8 frame-shadow cells so the 4 middle zeros survive for the box addressability. *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
      assert (RDB : forall jj, 0 <= jj < Z.of_nat 8 ->
                      exists b, mrd rsegs mg (wa (frb / 8 + ASAN_K + jj)) = Some b) end.
    { intros jj Hjj. apply RM.
      pose proof (FAP (8 * jj) ltac:(lia)) as Hap.
      pose proof (proj2 (SR0 (shadow_addr (frb + 8 * jj)) (rt_app_shadow (frb + 8 * jj) Hap))) as [bb Hbb].
      exists bb. replace (frb / 8 + ASAN_K + jj) with (shadow_addr (frb + 8 * jj)); [exact Hbb|].
      rewrite sh_add8 by exact FR8. unfold shadow_addr. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
      destruct (lay_bytes_exist mg 8%nat (frb / 8 + ASAN_K) ltac:(lia) ltac:(lia) RDB) as (bs8 & Lbs8 & HB4) end.
    do 8 (destruct bs8 as [|? bs8]; [cbn in Lbs8; lia|]). destruct bs8; [|cbn in Lbs8; lia].
    wst (frb / 8 + ASAN_K + 4) 1%nat. step.
    apply (bytes_at_write_inside rsegs _ (frb / 8 + ASAN_K) _ 4 (le1 (Z_to_bv 64 0))) in HB4;
      [| lia | rewrite length_le1; cbn [length]; lia].
    store_done. change (Z.to_nat 4) with 4%nat in HB4.
    cbn [upd_bytes firstn skipn app length Nat.add Nat.sub le1 Z_to_le_bytes] in HB4.
    wst (frb / 8 + ASAN_K + 5) 1%nat. step.
    apply (bytes_at_write_inside rsegs _ (frb / 8 + ASAN_K) _ 5 (le1 (Z_to_bv 64 0))) in HB4;
      [| lia | rewrite length_le1; cbn [length]; lia].
    store_done. change (Z.to_nat 5) with 5%nat in HB4.
    cbn [upd_bytes firstn skipn app length Nat.add Nat.sub le1 Z_to_le_bytes] in HB4.
    wst (frb / 8 + ASAN_K + 6) 1%nat. step.
    apply (bytes_at_write_inside rsegs _ (frb / 8 + ASAN_K) _ 6 (le1 (Z_to_bv 64 0))) in HB4;
      [| lia | rewrite length_le1; cbn [length]; lia].
    store_done. change (Z.to_nat 6) with 6%nat in HB4.
    cbn [upd_bytes firstn skipn app length Nat.add Nat.sub le1 Z_to_le_bytes] in HB4.
    wst (frb / 8 + ASAN_K + 7) 1%nat. step.
    apply (bytes_at_write_inside rsegs _ (frb / 8 + ASAN_K) _ 7 (le1 (Z_to_bv 64 0))) in HB4;
      [| lia | rewrite length_le1; cbn [length]; lia].
    store_done. change (Z.to_nat 7) with 7%nat in HB4.
    cbn [upd_bytes firstn skipn app length Nat.add Nat.sub le1 Z_to_le_bytes] in HB4.
    do 3 step.
    step.
    (* now at ASAN_MEMSET (0x524c4): discharge the checked memset of the row [p+18, p+50). *)
    pose proof (lay_Wf_sub frb sfr spc j n w120 HK Hn Hnj) as SUBf. unfold Wf, shadow_addr in SUBf.
    pose proof (munch_weaken _ _ _ _ SUBf MU) as MUe.
    pose proof (lay_ac _ _ MU SUBf) as AC1.
    pose proof (shadow_rw_mono m _ SR0 WM RM) as SR1.
    pose proof (acl_rw _ m _ (p + 18) [CB 32 ob] BLK MU WM
                  ltac:(intros x Hx; cbn [cells_size csize Nat.add] in Hx; change (Z.of_nat 32) with 32 in Hx;
                        apply (lay_row_out_Wf frb sfr spc j n w120 x HK Hn Hnj); lia)) as RW1.
    pose proof (lay_addr_keep _ (p + 18) (p + 50) (p + 18) 32 MUe
                  ltac:(right; left; reflexivity) AR ltac:(lia) ltac:(lia)
                  ltac:(unfold ly_dj in DJ1; unfold CTRL_LAY_BLOCK_K in *; lia)
                  ltac:(unfold ly_dj in DJ1; unfold CTRL_LAY_BLOCK_K in *; lia)) as AD1.
    assert (SPCr : S - 256 <= spc <= S - 128)
      by (destruct HK as [(_ & _ & Esp) | (_ & _ & _ & Esp & _)]; subst spc; lia).
    destruct (stk_split rsegs _ (S - K) spc S STK ltac:(unfold CTRL_LAY_BLOCK_K in *; lia)) as [STKlo STKhi].
    assert (Ed : bv_unsigned (Z_to_bv 64 (p + 18)) = p + 18) by (apply unsigned_lit; lia).
    assert (Ev : bv_unsigned (Z_to_bv 64 0) = 0) by (apply unsigned_lit; lia).
    assert (En : bv_unsigned (Z_to_bv 64 32) = 32) by (apply unsigned_lit; lia).
    assert (Es : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; lia).
    pose proof MEMS as HM. unfold asan_memset_contract, ASAN_MEMSET_K in HM. cbv zeta in HM.
    eapply evt_cut.
    { eapply HM with (lo := S - K) (junk := ob).
      all: rewrite ?Ed, ?Ev, ?En, ?Es.
      - change (Z.to_nat 32) with 32%nat. exact RW1.
      - lia.
      - exact AD1.
      - right. replace (p + 18 + 32) with (p + 50) by lia. exact AP50.
      - right. replace (p + 18 + 7) with (p + 18 + 7) by lia.
        exact (acl_app_in m (p + 18) 32 7 AR ltac:(lia)).
      - replace (p + 18 + 32) with (p + 50) by lia. exact ARDJ.
      - unfold ly_dj in DJ1. unfold CTRL_LAY_BLOCK_K in *.
        destruct DJ1 as [DJ|DJ]; [right | left]; lia.
      - exact STKlo.
      - unfold CTRL_LAY_BLOCK_K in *. lia.
      - exact HHM.
      - lia.
      - exact AC1.
      - exact SR1.
      - exact MI. }
    intros ms' POST.
    destruct POST as (u0 & u1 & u2 & pa1 & pa2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & mp &
                      Ems & MUp & WMp & MIp & STp & RWp & ACp & SRp).
    subst ms'. rewrite ?Ed, ?Ev, ?En, ?Es in MUp. rewrite Es in STp. rewrite ?Ed, ?Ev, ?En in RWp.
    unfold ASAN_MEMSET_K in MUp. replace (p + 18 + 32) with (p + 50) in MUp by lia.
    replace (ret_pc (Z_to_bv 64 546584)) with (Z_to_bv 64 546584)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    (* rd_mono from the memory before the memset to mp, from the memset footprint *)
    lazymatch type of MUp with munch _ ?mg _ => assert (RMp : rd_mono mg mp) end.
    { apply (rd_mono_list _ _ _ MUp). constructor; [|constructor; [|constructor]]; cbn [fst snd].
      - intros y Hy. pose proof RWp as RWc. destruct RWc as [[_ HBrow] _].
        cbn [cells_bytes cbytes] in HBrow. rewrite app_nil_r in HBrow.
        apply (rd_of_bytes _ _ _ HBrow). rewrite repeat_length. clear -Hy. lia.
      - intros y Hy. apply (rd_of_stk _ _ _ STp). clear -Hy SPCr. unfold CTRL_LAY_BLOCK_K. lia. }
    assert (SUBms : sub_fp [(p + 18, p + 50); (spc - 2208, spc)] (ctrl_lay_block_W p S ++ lay_X)).
    { intros x Hx. unfold ctrl_lay_block_W, lay_X in Hx. apply acl_out_app_inv in Hx. destruct Hx as (HW & _).
      cbn [outside] in HW. destruct HW as (Hwin & Hrow & _). cbn [outside].
      split; [exact Hrow|]. split; [clear -Hwin SPCr; unfold CTRL_LAY_BLOCK_K in *; lia | exact I]. }
    (* fp, the tls premise and the window's addressability outside the frame, carried from mc across the run's own
       stores and the memset (lay_fw_rt). *)
    assert (MUd : munch [(S - K, S); (frb, frb + 24); (frb / 8 + ASAN_K, frb / 8 + ASAN_K + 12); (p + 18, p + 50)]
                    mc mp).
    { eapply munch_trans; [eapply munch_weaken; [|exact MUc] | eapply munch_weaken; [|exact MUp]].
      - intros x Hx. cbn [outside] in Hx |- *. tauto.
      - intros x (Hw & _ & _ & Hr & _). cbn [outside].
        split; [exact Hr | split; [clear -Hw SPCr; unfold CTRL_LAY_BLOCK_K in *; lia | exact I]]. }
    destruct (lay_fw_rt frb sfr spc j w120 mc mp HK FPc TLc AWc MUd (wmono_trans rsegs _ _ _ WMc WMp)
                (rd_mono_trans _ _ _ RMc RMp)) as (FPp & TLp & AWp).
    unfold KB in HKB.
    eapply HKB; [ exact HK | ].
    unfold ME.
    split; [ eapply munch_trans; [exact MUe | eapply munch_weaken; [exact SUBms | exact MUp]] | ].
    split; [ eapply wmono_trans; [exact WM | exact WMp] | ].
    split; [ eapply rd_mono_trans; [exact RM | exact RMp] | ].
    split; [ exact MIp | ].
    split; [ exact ACp | ].
    split; [ exact SRp | ].
    split; [ exact (stk_mono _ mp (S - K) S STK WMp RMp) | ].
    split.
    { eapply rw_cells_transport; [exact SV | exact MUp | exact WMp |].
      cbn [disjoint_from cells_size csize Nat.add SAVES]. split; [|split; [|exact I]];
        clear -DJ1 SPCr; unfold ly_dj in DJ1; unfold CTRL_LAY_BLOCK_K in *; lia. }
    split; [ change ly_zero with (repeat (Z_to_bv 8 0) 32); exact RWp | ].
    split.
    { eapply fl_bytes;
        [ exact FB
        | eapply munch_trans; [exact MUe | eapply munch_weaken; [exact SUBms | exact MUp]]
        | intros x Hx; apply (lay_f_out x); rewrite FL in Hx; lia ]. }
    split.
    { (* the side frame (sfr <> 0): [frb + 120, frb + 128) lies in the class-1 side-stack frame j, below the window,
         apart from the row, the frame header words and the frame shadow. *)
      intros Hs. specialize (F120 Hs).
      destruct HK as [(E0 & _) | (Hj & Efr & _ & Esp & _)]; [exfalso; exact (Hs E0)|].
      replace (fs_M 1) with 8192 in Hj by reflexivity.
      pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFSlo & _ & _ & _).
      unfold FS_SIZE in P4, HFSlo.
      assert (B : fs_frame FS 1 0 <= frb /\ frb + 128 <= fs_frame FS 1 (fs_M 1) /\ frb + 128 <= FS + 2134016).
      { rewrite Efr. unfold fs_frame, fs_B, fs_M. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 1) with 2. change (2 ^ (14 - 1)) with 8192. change (2 ^ 20) with 1048576. clear -Hj. lia. }
      destruct B as (B1 & B2 & B3).
      pose proof (P4 (frb + 120) ltac:(clear -B3 FRlo; lia)) as A120.
      pose proof (P4 (frb + 127) ltac:(clear -B3 FRlo; lia)) as A127.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A120, A127.
      pose proof (lay_out_fpw_d (p + 18) (p + 50) (p + 18) ltac:(right; left; reflexivity) ltac:(clear; lia)) as O18.
      cbn [fp_w flat_map fp_w1 app outside] in O18. destruct O18 as (_ & _ & _ & _ & _ & _ & O18 & _).
      pose proof (bytes_at_transport rsegs _ _ _ _ _ F120 MUc) as F120a.
      rewrite length_le8 in F120a. change (Z.of_nat 8) with 8 in F120a. cbn [disjoint_from] in F120a.
      specialize (F120a ltac:(split; [|split; [|split; [|exact I]]]; clear -B3 HFSlo A120 A127 SHlo SHhi; lia)).
      pose proof (bytes_at_transport rsegs _ _ _ _ _ F120a MUp) as F120b.
      rewrite length_le8 in F120b. change (Z.of_nat 8) with 8 in F120b. cbn [disjoint_from] in F120b.
      apply F120b. split; [|split; [|exact I]]; clear -O18 B1 B2 B3 HFSlo SKv Esp SP2lo; lia. }
    split.
    { eapply lay_addr_keep; [ eapply munch_trans; [exact MUe | eapply munch_weaken; [exact SUBms | exact MUp]]
                            | right; left; reflexivity | exact AR | lia | lia
                            | unfold ly_dj in DJ1; unfold CTRL_LAY_BLOCK_K in *; lia
                            | unfold ly_dj in DJ1; unfold CTRL_LAY_BLOCK_K in *; lia ]. }
    split.
    { eapply lay_addr_keep; [ eapply munch_trans; [exact MUe | eapply munch_weaken; [exact SUBms | exact MUp]]
                            | left; reflexivity | exact AF | lia | lia
                            | unfold ly_dj in DJ2; unfold CTRL_LAY_BLOCK_K in *; lia
                            | unfold ly_dj in DJ2, DB1; unfold CTRL_LAY_BLOCK_K in *; lia ]. }
    split.
    { pose proof (acl_app_in m (p + 18) 32 0 AR ltac:(lia)) as Ap18u. rewrite Z.add_0_r in Ap18u.
      pose proof AP50 as AP50u.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ap18u, AP50u.
      cbn [upd_bytes firstn skipn length Nat.add Nat.sub] in HB4.
      pose proof (bytes_at_transport rsegs _ _ mp _ _ HB4 MUp
                    ltac:(cbn [disjoint_from fst snd length]; change (Z.of_nat 8) with 8;
                          split; [|split; [|exact I]]; clear -Ap18u AP50u SHlo SHhi HHM' SKv SPCr; lia)) as HB4p.
      lazymatch type of HB4p with bytes_at _ _ _ (?x0 :: ?x1 :: ?x2 :: ?x3 :: ?rest) =>
        pose proof (proj2 (proj1 (bytes_at_app rsegs mp (frb / 8 + ASAN_K) [x0; x1; x2; x3] rest) HB4p)) as HB4s end.
      cbn [length] in HB4s. change (Z.of_nat 4) with 4 in HB4s.
      try rewrite (unsigned_lit 0) in HB4s by (clear; lia).
      apply (lay_addr_zero mp (frb + 32) 32 4).
      - clear -Rfrb. lia.
      - clear -FR8. unfold rs_hold in FR8. Z.div_mod_to_equations. lia.
      - clear. lia.
      - clear -FRhi SP2hi HAE'. unfold APPMEM_END. lia.
      - intros i Hi. replace (frb + 32 + i) with (frb + (32 + i)) by (clear; lia). apply FAP. clear -Hi. lia.
      - replace (shadow_addr (frb + 32)) with (frb / 8 + ASAN_K + 4)
          by (clear -FR8; unfold rs_hold in FR8; unfold shadow_addr; Z.div_mod_to_equations; lia).
        exact HB4s. }
    split; [exact FPp|]. split; [exact TLp | exact AWp].
  Qed.

  (* KB from the dispatch stage: the memory ME describes at 0x85718 gives FI, LC (the 32-byte cell at S - 128 holds
     whatever the window holds there: gj) and the box output [frb + 32, frb + 64) addressable. *)
  Lemma ly_kb : DISP_T -> KB Q.
  Proof using AMD ARDJ DB3 DBN DJ3m FL FPM HHM K9 MDP P0 Rf Rg Rmd Rp TM.
    clear SP16 ST0 DJ1 DJ2 DJ3 DJ3g F8 F24 FB AOL P50 BLK DB1 DB2 GP MI0 AC0 SR0 HAE AW0 AF AR AP50 ATM AG AJ5 AJ6 FP0
      FPT FPG TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    intros HD frb sfr spc j w120 mc xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HK
      (MU & WM & RM & MI & AC & SR & STK & SV & RW & FBc & F120 & _ & _ & AM & FPc & TLc & AWo).
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    destruct (stk_split rsegs mc (S - K) (S - 96) S STK ltac:(lia)) as [STlo _].
    destruct (stk_carve rsegs mc (S - K) (S - 96) 32 STlo ltac:(change (Z.of_nat 32) with 32; lia))
      as [STc [gj Hgj]].
    change (Z.of_nat 32) with 32 in STc, Hgj.
    assert (LCc : LC mc gj ly_zero).
    { apply LC_intro.
      - replace (bv_unsigned sp + -128) with (S - 96 - 32) by lia.
        apply lay_rw_cons; [exact Hgj|]. cbn [csize]. change (Z.of_nat 32) with 32.
        replace (S - 96 - 32 + 32) with (S - 96) by lia. exact SV.
      - replace (bv_unsigned sp + -128) with (S - 96 - 32) by lia. exact STc.
      - eapply munch_weaken; [|exact MU]. intros x Hx. unfold ctrl_lay_block_W. cbn [outside app] in Hx |- *.
        tauto.
      - exact WM.
      - exact MI.
      - exact RW.
      - exact FBc. }
    assert (FIc : FI mc frb sfr spc j w120).
    { split; [exact HK|]. split; [exact F120|]. split; [exact AC|]. split; [exact SR|].
      split; [exact FPc|]. split; [exact TLc | exact AWo]. }
    (* the s0 slot is the entry sp in both KB and DISP_T *)
    exact (HD mc gj frb sfr spc j w120 xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' FIc LCc AM).
  Qed.

  (* 0x855f4 -> 0x8569c: the 128-byte frame (sd zero at S - 128 and the 12 saves), sp aligned to SP2, the flag word
     (UAR = 1: the frame request runs) and the shadow offset s10 = ASAN_K, the class-1 frame request frame_alloc_1
     (HSM), then the side frame or the real-stack fallback frb = SP2 - 96 with its page probe at SP2 - 4096; hands BI
     over to fwords. *)
  Lemma ly_pro_go : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m0 : word -> option byte), m0 = m -> KB Q ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g)
                     a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m0 (seg_rom rsegs)).
  Proof using AC0 AF AMD AP50 AR ARDJ AW0 BLK DB1 DB3 DBN DJ1 DJ2 DJ3m FB FL FP0 FPM HAE HHM HSM K9 MDP MEMS MI0 P0
    P50 Rf Rg Rmd Rp SP16 SR0 ST0 TLS0 TM.
    clear DJ3 DJ3g F8 F24 AOL DB2 GP ATM AG AJ5 AJ6 FPT FPG MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m0 Em0 HKB.
    unfold CTRL_LAY_BLOCK.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof SP2_facts as (SP2m & SP2lo & SP2hi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (EK : CTRL_LAY_BLOCK_K = 4512) by reflexivity.
    rs_hide_all.
    assert (MU : munch [(S - K, S)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    destruct (stk_split rsegs m0 _ (S - 128) _ ST0c ltac:(lia)) as [STa STb]. clear ST0c.
    carve_frame 96%nat STb.
    step.
    assert (HS0 : store_ok rsegs m0 (wa (S + -128)) 8 = true).
    { eapply wv_store_ok; [ | apply wmono_refl | lia | lia]. intros i Hi.
      apply (stk_wv m0 (S - 128) (S + -96)); [exact STb | lia]. }
    step. store_done.
    do 12 step.
    step. step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = SP2)
      by (rewrite unsigned_lit, land_align32 by lia; f_equal; f_equal; lia).
    rewrite EA.
    (* s0 = sp (the entry sp), s1 = sp = SP2 *)
    do 12 step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    (* ---- the class-1 frame request __asan_stack_malloc_1 (0x3d72c), L = 96, at sp = SP2 ---- *)
    pose proof FP0 as FPm. unfold ctrl_lay_block_W in FPm.
    pose proof (fl_fp [0%nat; 1%nat] m _ (bv_unsigned tp) FS (S - K) S [(p + 18, p + 50)]
                  (ctrl_lay_block_D p f) [(S - K, S)] FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HCL as HCL1. apply Forall_inv_tail in HCL1. apply Forall_inv in HCL1.
    destruct HCL1 as (_ & h & flags & HH & HF & HFl & HFb).
    pose proof FP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCL0 & _).
    pose proof HCL0 as HCL0'. apply Forall_inv_tail in HCL0'. apply Forall_inv in HCL0'.
    destruct HCL0' as (_ & hm & flm & HHm & _). clear HCL0.
    pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
    cbn [fp_tls app] in Hw0.
    repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    destruct (stk_split rsegs _ (S - K) SP2 (S - 128) STa ltac:(lia)) as [STsp _].
    pose proof lay_num as (NH0 & NH1 & NM0 & NM1 & NB1 & NF0 & NF1 & NR0 & NR1).
    pose proof HSM as HM. unfold asan_stack_malloc_1_contract, asan_stack_malloc_contract in HM. cbv zeta in HM.
    eapply evt_cut.
    { eapply HM with (lo := S - K) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
        (DB := DB) (k := k) (flags := flags); unfold ASAN_STACK_MALLOC_K; rewrite ?(unsigned_lit SP2) by lia.
      - rewrite unsigned_lit by lia. unfold fs_B. cbn. lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - exact (fl_asan_cells _ m _ AC0 MU
                 ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I])).
      - exact (shadow_rw_mono m _ SR0 WM RM).
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
      - exact STsp.
      - lia.
      - lia.
      - intros a Ha. apply HAPP. lia.
      - cbn [disjoint_from].
        repeat split; try exact I;
          match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
            match goal with Hd : ly_dj _ _ lo hi |- _ => unfold ly_dj in Hd; lia end end. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E & WM2 & MI2
                    & ST2 & HP2 & (h2 & HH2) & ALT).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 546412)) with (Z_to_bv 64 546412)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit SP2) in ST2 by lia.
    clear HT HTP H88 H96 HF HFb HCL HDd HWd Hw0.
    destruct ALT as [(Hall & Ex0 & MU2) | (i & Hi & Hpre & Hnth & FRM)].
    - (* ---- the real-stack fallback: frb = SP2 - 96, sfr = 0, the page probe at SP2 - 4096 ---- *)
      subst x0. rewrite (unsigned_lit SP2) in MU2 by lia. unfold ASAN_STACK_MALLOC_K in MU2.
      lazymatch type of MU2 with munch _ ?mg _ => assert (RM2 : rd_mono mg m2) end.
      { apply (rd_mono_list _ _ _ MU2). constructor; [|constructor; [|constructor]]; cbn [fst snd].
        - intros y Hy. apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn [Z.of_nat]. lia.
        - intros y Hy. apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch [(S - K, S); (fs_hint FS 1, fs_hint FS 1 + 8)] m m2).
      { eapply munch_trans.
        - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in Hx |- *. tauto.
        - eapply munch_weaken; [|exact MU2]. intros x (Hw & Hh & _). cbn [outside].
          split; [exact Hh | split; [lia | exact I]]. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3.
      pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ _ m2 _ _ FR MU2 WM2
                    ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES]; rewrite NH1; lia)) as FR2.
      clear MU MU2 WM WM2 RM RM2 FR STa STsp STb MI.
      step. step. step. step.
      replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
      step. step.
      match goal with |- context [Z.land ?x 18446744073709551584] =>
        replace (Z.land x 18446744073709551584) with (SP2 - 96)
          by (rewrite ?(unsigned_lit SP2), ?unsigned_lit by lia; rewrite land_align32 by lia;
              Z.div_mod_to_equations; lia) end.
      step. step.
      rewrite (unsigned_lit SP2) by lia.
      wst (SP2 - 4096) 8%nat. step. store_done.
      step.
      rewrite (rc_lts_signed (SP2 - 96) (SP2 - 4096)) by lia.
      replace (SP2 - 96 <? SP2 - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step.
      (* the hint word is readable again at the current memory (the probe wrote only inside the window) *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
        assert (HHc : exists hh, bytes_at rsegs mg (fs_hint FS 1) (le8 hh)) end.
      { apply (rd8_le8 _ (fs_hint FS 1) ltac:(rewrite NH1; lia) ltac:(rewrite NH1; lia)).
        intros y Hy. apply RM3. apply (rd_of_bytes _ _ _ HHm). rewrite length_le8. cbn [Z.of_nat]. lia. }
      eapply (fwords (SP2 - 96) 0 (SP2 - 96) 0 0 (Z_to_bv 64 0));
        [ left; repeat split; reflexivity | lia | left; reflexivity | | exact HKB ].
      assert (SHW : forall x, S - K <= x < S ->
                outside [(S - K, S); (fs_hint FS 1, fs_hint FS 1 + 8)] (shadow_addr x)).
      { intros x Hx.
        assert (Hap : app_mem x)
          by (replace x with (S - K + (x - (S - K))) by lia; apply (acl_app_in m (S - K) K); [exact AW0 | lia]).
        pose proof (rt_app_shadow x Hap) as Hsh.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
        cbn [outside]. split; [lia|]. split; [| exact I].
        intros Hc. apply (acl_app_not_shadow (shadow_addr x)); [apply P4; rewrite NH1 in Hc; lia|].
        apply rt_app_shadow. exact Hap. }
      destruct (lay_bi_rt [(S - K, S); (fs_hint FS 1, fs_hint FS 1 + 8)] (SP2 - 96) 0 (SP2 - 96) 0 0
                  (Z_to_bv 64 0) _ ltac:(left; repeat split; reflexivity) ltac:(lia) ltac:(left; reflexivity)
                  MU3 ltac:(intros x Hx; unfold Wf in Hx; cbn [outside] in Hx |- *; tauto)
                  WM3 RM3 HHc ltac:(intros Hc; discriminate Hc) SHW)
        as (AWc & FPc & TLc).
      unfold BI.
      split; [ eapply munch_weaken; [|exact MU3]; intros x Hx; unfold Wf in Hx;
               cbn [outside] in Hx |- *; tauto | ].
      split; [ exact WM3 | ]. split; [ exact RM3 | ]. split; [ assumption | ].
      split; [ replace (S - 96) with (bv_unsigned sp + -96) by lia; exact FR2 | ].
      split; [ intros Hc; exfalso; exact (Hc eq_refl) | ].
      split; [ exact AWc | ]. split; [ exact FPc | exact TLc ].
    - (* ---- the class-1 side frame fs_frame FS 1 jj ---- *)
      unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
      rewrite (unsigned_lit SP2), (unsigned_lit 96) in FRM by lia.
      replace (fs_B 1) with 128 in FRM by reflexivity.
      replace (fs_shadow_n 1 96) with 16 in FRM by reflexivity.
      unfold ASAN_STACK_MALLOC_K in FRM.
      destruct FRM as (Ex0 & Hm64 & _ & HFLg & H24 & H120 & HSH & HADD & STF & APF & FSlo & FShi & GT & FRA' & DIS
                       & MU2).
      unfold FS_SIZE in FShi.
      remember ((bv_unsigned h + i) mod fs_M 1) as jj eqn:Ejj.
      assert (Hjj : 0 <= jj < fs_M 1) by (subst jj; apply Z.mod_pos_bound; reflexivity).
      pose proof Hjj as Hjjn. rewrite NM1 in Hjjn.
      remember (fs_frame FS 1 jj) as fr0 eqn:Efr.
      subst x0. clear DIS FRA' HADD H24 Hpre Hnth.
      assert (Fr8 : fr0 mod 8 = 0) by (clear -Hm64; Z.div_mod_to_equations; lia).
      assert (FRlo0 : 0 < fr0) by (clear -FSlo P1; lia).
      assert (FRhi0 : fr0 + 128 <= S - K) by (clear -FShi HFS'; lia).
      assert (SHlo0 : 2147450880 <= shadow_addr fr0 /\ shadow_addr fr0 + 16 <= 17594333495296).
      { pose proof (rt_app_shadow _ (APF fr0 ltac:(lia))) as A0.
        pose proof (rt_app_shadow _ (APF (fr0 + 120) ltac:(lia))) as A1.
        replace (shadow_addr (fr0 + 120)) with (shadow_addr fr0 + 15) in A1
          by (replace (fr0 + 120) with (fr0 + 8 * 15) by lia; rewrite sh_add8 by exact Fr8; reflexivity).
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in A0, A1.
        lia. }
      destruct SHlo0 as (SHlo0 & SHhi0).
      assert (Wside : munch [(S - K, S); (fs_hint FS 1, fs_hint FS 1 + 8);
                             (fs_flag FS 1 jj, fs_flag FS 1 jj + 1); (fr0 + 24, fr0 + 32);
                             (fr0 + 120, fr0 + 128); (shadow_addr fr0, shadow_addr fr0 + 16)] m m2).
      { eapply munch_trans.
        - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in Hx |- *. tauto.
        - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx |- *.
          destruct Hx as (Hw & Hh & Hfl & H24r & H120r & Hshr & _).
          split; [exact Hh|]. split; [exact Hfl|]. split; [exact H24r|].
          split; [clear -H120r; lia|]. split; [exact Hshr|].
          split; [clear -Hw SP2lo SP2hi EK; unfold CTRL_LAY_BLOCK_K in *; lia | exact I]. }
      lazymatch type of MU2 with munch _ ?mg _ => assert (RM2 : rd_mono mg m2) end.
      { apply (rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
        - apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn [Z.of_nat]. lia.
        - apply (rd_of_bytes _ _ _ HFLg). cbn [length Z.of_nat]. lia.
        - apply (rd_of_stk _ _ _ STF). lia.
        - apply (rd_of_stk _ _ _ STF). lia.
        - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
        - apply (rd_of_stk _ _ _ ST2). lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3.
      pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ _ m2 _ _ FR MU2 WM2
                    ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES]; rewrite NH1, (NF1 jj); lia)) as FR2.
      clear MU MU2 WM WM2 RM RM2 FR STa STsp STb MI HSH.
      step. step. step. step.
      rewrite (rc_neq0_64 fr0) by lia. cbn [negb]. cbv iota.
      eapply (fwords fr0 fr0 SP2 jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)));
        [ right; repeat split; [lia | lia | exact Efr] | lia | right; exact Hjj
        | | exact HKB ].
      assert (SHW : forall x, S - K <= x < S ->
                outside [(S - K, S); (fs_hint FS 1, fs_hint FS 1 + 8);
                         (fs_flag FS 1 jj, fs_flag FS 1 jj + 1); (fr0 + 24, fr0 + 32);
                         (fr0 + 120, fr0 + 128); (shadow_addr fr0, shadow_addr fr0 + 16)] (shadow_addr x)).
      { intros x Hx.
        assert (Hap : app_mem x)
          by (replace x with (S - K + (x - (S - K))) by lia; apply (acl_app_in m (S - K) K); [exact AW0 | lia]).
        pose proof (rt_app_shadow x Hap) as Hsh.
        assert (NA : forall a b, (forall z, a <= z < b -> app_mem z) -> ~ (a <= shadow_addr x < b))
          by (intros a b Hab Hin; exact (acl_app_not_shadow _ (Hab _ Hin) Hsh)).
        pose proof Hsh as Hshn.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshn.
        cbn [outside]. split; [lia|].
        split; [apply NA; intros z Hz; apply P4; rewrite NH1 in Hz; lia|].
        split; [apply NA; intros z Hz; apply P4; rewrite (NF1 jj) in Hz; lia|].
        split; [apply NA; intros z Hz; apply APF; lia|].
        split; [apply NA; intros z Hz; apply APF; lia|].
        split; [| exact I].
        replace (shadow_addr fr0 + 16) with (shadow_addr (fr0 + 128))
          by (replace (fr0 + 128) with (fr0 + 8 * 16) by lia; rewrite sh_add8 by exact Fr8; reflexivity).
        exact (acl_win_sh x fr0 (fr0 + 128) Fr8 ltac:(lia)). }
      destruct (lay_bi_rt _ fr0 fr0 SP2 jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)) _
                  ltac:(right; repeat split; [lia | lia | exact Efr])
                  ltac:(lia) ltac:(right; exact Hjj) Wside
                  ltac:(intros x Hx; unfold Wf in Hx; cbn [outside] in Hx |- *;
                        destruct Hx as (Hw & Hh & Hfl & Hfrr & Hshr & _);
                        repeat split; try exact I; lia)
                  WM3 RM3 ltac:(exists h2; exact HH2) ltac:(intros _; exact HFLg) SHW)
        as (AWc & FPc & TLc).
      unfold BI.
      split; [ eapply munch_weaken; [|exact Wside]; intros x Hx; unfold Wf in Hx; cbn [outside] in Hx |- *;
               destruct Hx as (Hw & Hh & Hfl & Hfrr & Hshr & _); repeat split; try exact I; lia | ].
      split; [ exact WM3 | ]. split; [ exact RM3 | ]. split; [ exact MI2 | ].
      split; [ replace (S - 96) with (bv_unsigned sp + -96) by lia; exact FR2 | ].
      split; [ intros _; replace (fr0 + 120) with (fr0 + 128 - 8) by lia; exact H120 | ].
      split; [ exact AWc | ]. split; [ exact FPc | exact TLc ].
  Qed.

  (* 0x855f4: the function entry (the A excerpt's frame setup), to the dispatch stage DISP_T. *)
  Lemma ly_pro : DISP_T ->
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g)
                     a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m (seg_rom rsegs)).
  Proof.
    intros HD t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6.
    exact (ly_pro_go t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m eq_refl (ly_kb HD)).
  Qed.


  (* ===== box call: LC_after_box, ly_boxcall (insert below this line) ===== *)
  (* (ported from the image-B proof lib/B/Prog/ctrl_lay_block.v (not in this delivery), the block below its marker
     `box arms and dispatch`; image A moves the call to 0x85818 / 0x85828 and keeps md in s6 and frb + 32 in s7.) *)

  (* ---------------- the box call at 0x85818: reac_box_model_block(md, b, frb + 32) ----------------
     The callee runs at sp = spc with its 4272-byte window inside the function's window [S - K, S) (SP2 is S - 128
     or S - 144, so spc >= S - 240), and writes its 32-byte output block at frb + 32 (the frame's middle 32 bytes),
     the class-0 side-stack bytes and the shadow of its own window.
     Every lia of this part runs with a cleared context: the section's hypotheses make the full one too big. *)

  (* S is a multiple of 16, so SP2 is S - 128 or S - 144. *)
  Lemma SP2_tight : S - 144 <= SP2.
  Proof. pose proof SP16 as H16. clear -H16. Z.div_mod_to_equations. lia. Qed.

  Lemma box_S8 : S mod 8 = 0 /\ (S - K) mod 8 = 0.
  Proof.
    pose proof SP16 as H16. clear -H16. unfold CTRL_LAY_BLOCK_K. Z.div_mod_to_equations. lia.
  Qed.

  (* Every shadow byte lies in [LOWMEM_END, HIGHMEM_BEG]. *)
  Lemma box_sh_bound : forall z, 0 <= z <= APPMEM_END -> LOWMEM_END <= shadow_addr z <= HIGHMEM_BEG.
  Proof.
    intros z Hz. unfold shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hz |- *.
    clear -Hz. Z.div_mod_to_equations. lia.
  Qed.

  (* --- apartness lists --- *)
  Lemma dj_in : forall L Y a b c d, fp_dj L Y -> In (a, b) L -> In (c, d) Y -> ly_dj a b c d.
  Proof.
    intros L Y a b c d H Ha Hc. unfold fp_dj in H. rewrite Forall_forall in H.
    pose proof (H _ Ha) as H1. rewrite Forall_forall in H1. exact (H1 _ Hc).
  Qed.

  Lemma dj_mk : forall L Y, (forall a b c d, In (a, b) L -> In (c, d) Y -> ly_dj a b c d) -> fp_dj L Y.
  Proof.
    intros L Y H. apply Forall_forall. intros [a b] Ha. apply Forall_forall. intros [c d] Hc.
    exact (H a b c d Ha Hc).
  Qed.

  Lemma dj_one : forall A n Y, fp_dj [(A, A + n)] Y -> forall c d, In (c, d) Y -> A + n <= c \/ d <= A.
  Proof.
    intros A n Y H c d Hc.
    exact (dj_in [(A, A + n)] Y A (A + n) c d H (or_introl eq_refl) Hc).
  Qed.

  (* Every range of Y is inside a range of X. *)
  Lemma dj_cover : forall L X Y, fp_dj L X ->
    (forall c d, In (c, d) Y -> exists a b, In (a, b) X /\ a <= c /\ d <= b) -> fp_dj L Y.
  Proof.
    intros L X Y H HY. apply dj_mk. intros a b c d Hab Hcd.
    destruct (HY c d Hcd) as (c' & d' & Hin & H1 & H2).
    pose proof (dj_in L X a b c' d' H Hab Hin) as HD. unfold ly_dj in HD |- *.
    clear -HD H1 H2. lia.
  Qed.

  Lemma disjoint_from_app : forall X Y A n, disjoint_from X A n -> disjoint_from Y A n ->
    disjoint_from (X ++ Y) A n.
  Proof.
    induction X as [|[lo hi] X IH]; intros Y A n HX HY; cbn [app disjoint_from] in *; [exact HY|].
    split; [exact (proj1 HX) | exact (IH Y A n (proj2 HX) HY)].
  Qed.

  Lemma disjoint_of_in : forall L A n, (forall a b, In (a, b) L -> A + n <= a \/ b <= A) ->
    disjoint_from L A n.
  Proof.
    induction L as [|[lo hi] L IH]; intros A n H; cbn [disjoint_from]; [exact I|].
    split; [apply H; left; reflexivity | apply IH; intros a b Hin; apply H; right; exact Hin].
  Qed.

  Lemma outside_of_in : forall L x, (forall a b, In (a, b) L -> ~ (a <= x < b)) -> outside L x.
  Proof.
    induction L as [|[lo hi] L IH]; intros x H; cbn [outside]; [exact I|].
    split; [apply H; left; reflexivity | apply IH; intros a b Hin; apply H; right; exact Hin].
  Qed.

  Lemma out_in : forall L x a b, outside L x -> In (a, b) L -> ~ (a <= x < b).
  Proof.
    induction L as [|[lo hi] L IH]; intros x a b HO Hin; cbn [In] in Hin; [destruct Hin|].
    cbn [outside] in HO. destruct HO as [H1 H2]. destruct Hin as [E|Hin]; [|exact (IH x a b H2 Hin)].
    injection E as <- <-. exact H1.
  Qed.

  Lemma out_app_inv : forall A B x, outside (A ++ B) x -> outside A x /\ outside B x.
  Proof.
    induction A as [|[lo hi] A IH]; intros B x H; cbn [app outside] in *; [split; [exact I | exact H]|].
    destruct H as [H1 H2]. destruct (IH B x H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
  Qed.

  (* The side stack's place and the ranges of fp_w [0%nat; 1%nat] FS in numbers (fs_* of asan_stack_malloc_c:
     class c holds fs_M c = 2 ^ (14 - c) frames of fs_B c = 64 * 2 ^ c bytes at FS + 36864 + c * 2 ^ 20). *)
  Lemma box_fs :
    0 < FS /\ FS mod 4096 = 0 /\ ASAN_GT <= FS /\ FS + 11571200 <= S - K /\
    (forall i, 0 <= i < 11571200 -> app_mem (FS + i)) /\
    fs_hint FS 0%nat = FS /\ fs_hint FS 1%nat = FS + 8 /\
    fs_flag FS 0%nat 0 = FS + 4096 /\ fs_M 0%nat = 16384 /\
    fs_flag FS 1%nat 0 = FS + 20480 /\ fs_M 1%nat = 8192 /\
    fs_frame FS 0%nat 0 = FS + 36864 /\ fs_frame FS 0%nat (fs_M 0%nat) = FS + 1085440 /\
    fs_frame FS 1%nat 0 = FS + 1085440 /\ fs_frame FS 1%nat (fs_M 1%nat) = FS + 2134016 /\
    (forall jj, fs_frame FS 1%nat jj = FS + 1085440 + 128 * jj).
  Proof.
    pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & _) & _ & _ & _ & HFS & _).
    unfold FS_SIZE in HFS, P4.
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    split; [exact HFS|]. split; [intros i Hi; apply P4; clear -Hi; lia|].
    clear. unfold fs_hint, fs_flag, fs_frame, fs_B, fs_M. cbn [Z.of_nat Pos.of_succ_nat].
    change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. change (2 ^ 0) with 1.
    change (2 ^ (14 - 0)) with 16384. change (2 ^ (14 - 1)) with 8192.
    change (2 ^ (15 - 0)) with 32768. change (2 ^ (15 - 1)) with 16384.
    repeat (split; [lia|]). intros jj. lia.
  Qed.

  (* fp_w [0%nat] FS is the class-0 part of fp_w [0%nat; 1%nat] FS. *)
  Lemma box_fpw0 : forall r, In r (fp_w [0%nat] FS) -> In r (fp_w [0%nat; 1%nat] FS).
  Proof.
    intros r H. cbn [fp_w fp_w1 flat_map app In] in H |- *.
    destruct H as [H|[H|[H|[H|[]]]]]; [left | right; left | right; right; left | right; right; right; left];
      exact H.
  Qed.

  Lemma box_fpw_f1 : In (fs_frame FS 1%nat 0, fs_frame FS 1%nat (fs_M 1%nat)) (fp_w [0%nat; 1%nat] FS).
  Proof. cbn [fp_w fp_w1 flat_map app In]. do 6 right. left. reflexivity. Qed.

  (* The four ranges of fp_w [0%nat] FS in numbers. *)
  Lemma box_fpw0_cases : forall a b, In (a, b) (fp_w [0%nat] FS) ->
    (a = FS /\ b = FS + 8) \/ (a = FS + 4096 /\ b = FS + 20480) \/
    (a = FS + 36864 /\ b = FS + 1085440) \/ (2147450880 <= a /\ b <= 17594333495296).
  Proof.
    intros a b Hin.
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    pose proof HAE as HA. pose proof HHM as HH.
    unfold APPMEM_END, HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HA, HH. unfold CTRL_LAY_BLOCK_K in F4.
    assert (FSB : 0 < FS /\ FS + 11571200 <= 140737488355328) by (clear -F1 F4 HA; lia).
    pose proof (box_sh_bound (fs_frame FS 0%nat 0) ltac:(unfold APPMEM_END; clear -FSB E7; lia)) as B0.
    pose proof (box_sh_bound (fs_frame FS 0%nat (fs_M 0%nat))
                  ltac:(unfold APPMEM_END; clear -FSB E8; lia)) as B0'.
    unfold LOWMEM_END, HIGHMEM_BEG in B0, B0'.
    cbn [fp_w fp_w1 flat_map app In] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-.
    - left. clear -E1. lia.
    - right. left. clear -E3 E4. lia.
    - right. right. left. clear -E7 E8. lia.
    - right. right. right. clear -B0 B0'. lia.
  Qed.

  (* Every range of fp_w [0%nat; 1%nat] FS is inside the side stack or inside the shadow. *)
  Lemma box_fpw_cases : forall a b, In (a, b) (fp_w [0%nat; 1%nat] FS) ->
    (FS <= a /\ b <= FS + 11571200) \/ (2147450880 <= a /\ b <= 17594333495296).
  Proof.
    intros a b Hin.
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    pose proof HAE as HA. pose proof HHM as HH.
    unfold APPMEM_END, HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HA, HH. unfold CTRL_LAY_BLOCK_K in F4.
    assert (FSB : 0 < FS /\ FS + 11571200 <= 140737488355328) by (clear -F1 F4 HA; lia).
    pose proof (box_sh_bound (fs_frame FS 0%nat 0) ltac:(unfold APPMEM_END; clear -FSB E7; lia)) as B0.
    pose proof (box_sh_bound (fs_frame FS 0%nat (fs_M 0%nat))
                  ltac:(unfold APPMEM_END; clear -FSB E8; lia)) as B0'.
    pose proof (box_sh_bound (fs_frame FS 1%nat 0) ltac:(unfold APPMEM_END; clear -FSB E9; lia)) as B1.
    pose proof (box_sh_bound (fs_frame FS 1%nat (fs_M 1%nat))
                  ltac:(unfold APPMEM_END; clear -FSB E10; lia)) as B1'.
    unfold LOWMEM_END, HIGHMEM_BEG in B0, B0', B1, B1'.
    cbn [fp_w fp_w1 flat_map app In] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-.
    - left. clear -E1. lia.
    - left. clear -E3 E4. lia.
    - left. clear -E7 E8. lia.
    - right. clear -B0 B0'. lia.
    - left. clear -E2. lia.
    - left. clear -E5 E6. lia.
    - left. clear -E9 E10. lia.
    - right. clear -B1 B1'. lia.
  Qed.

  (* A byte at or above the function's window is apart from the side-stack bytes. *)
  Lemma box_win_out_fpw : forall x, S - K <= x -> outside (fp_w [0%nat; 1%nat] FS) x.
  Proof.
    intros x Hx. pose proof box_fs as (F1 & F2 & F3 & F4 & _). pose proof HHM as HH.
    unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HH. unfold CTRL_LAY_BLOCK_K in Hx, F4.
    apply outside_of_in. intros a b Hin. destruct (box_fpw_cases a b Hin) as [HB|HB];
      clear -Hx HB F4 HH; lia.
  Qed.

  (* A byte below the side stack's lower bound ASAN_GT is apart from the side-stack bytes. *)
  Lemma box_lo_out_fpw : forall x, 0 <= x < ASAN_GT -> outside (fp_w [0%nat; 1%nat] FS) x.
  Proof.
    intros x Hx. pose proof box_fs as (F1 & F2 & F3 & _). unfold ASAN_GT in Hx, F3.
    apply outside_of_in. intros a b Hin. destruct (box_fpw_cases a b Hin) as [HB|HB];
      clear -Hx HB F3; lia.
  Qed.

  (* An application byte never holds a shadow byte. *)
  Lemma box_app_not_sh : forall A n x, 0 < n -> (forall i, 0 <= i < n -> app_mem (A + i)) -> in_shadow x ->
    ~ (A <= x < A + n).
  Proof.
    intros A n x Hn HA Hx. pose proof (app_range A n Hn HA) as HR.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx.
    clear -HR Hx. lia.
  Qed.

  (* The shadow byte of an application byte apart from the side stack's frames is apart from the side-stack
     bytes. *)
  Lemma box_sh_out_fpw : forall x, app_mem x -> outside (fp_w [0%nat; 1%nat] FS) x ->
    outside (fp_w [0%nat; 1%nat] FS) (shadow_addr x).
  Proof.
    intros x Hap Ho. pose proof (rt_app_shadow x Hap) as Hs.
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    assert (M0 : fs_frame FS 0%nat 0 mod 8 = 0)
      by (rewrite E7; clear -F2; Z.div_mod_to_equations; lia).
    assert (M1 : fs_frame FS 1%nat 0 mod 8 = 0)
      by (rewrite E9; clear -F2; Z.div_mod_to_equations; lia).
    assert (NA : forall a b, FS <= a -> b <= FS + 11571200 -> ~ (a <= shadow_addr x < b)).
    { intros a b Ha Hb Hc.
      exact (box_app_not_sh FS 11571200 (shadow_addr x) ltac:(clear; lia) F5 Hs
               ltac:(clear -Ha Hb Hc; lia)). }
    cbn [fp_w fp_w1 flat_map app outside] in Ho |- *.
    destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & _).
    split; [apply NA; clear -E1; lia|]. split; [apply NA; clear -E3 E4; lia|].
    split; [apply NA; clear -E7 E8; lia|].
    split; [exact (acl_win_sh x _ _ M0 O3)|].
    split; [apply NA; clear -E2; lia|]. split; [apply NA; clear -E5 E6; lia|].
    split; [apply NA; clear -E9 E10; lia|].
    split; [exact (acl_win_sh x _ _ M1 O7) | exact I].
  Qed.

  (* --- the body's writes so far: [(p + 18, p + 50); (S - K, S)] ++ lay_X --- *)

  (* The shadow byte of an application byte outside the window and the side-stack bytes is outside the body's
     writes. *)
  Lemma box_out_body_sh : forall x, app_mem x -> (x < S - K \/ S <= x) ->
    outside (fp_w [0%nat; 1%nat] FS) x ->
    outside ([(p + 18, p + 50); (S - K, S)] ++ lay_X) (shadow_addr x).
  Proof.
    intros x Hap Hw Ho. pose proof (rt_app_shadow x Hap) as Hs.
    pose proof box_S8 as (S8 & SK8).
    cbn [app outside]. split; [|split].
    - intros Hc. exact (box_app_not_sh (p + 18) 32 _ ltac:(clear; lia)
        (fun i Hi => acl_app_in m (p + 18) 32 i AR Hi) Hs ltac:(clear -Hc; lia)).
    - intros Hc. exact (box_app_not_sh (S - K) K _ ltac:(unfold CTRL_LAY_BLOCK_K; clear; lia)
        (fun i Hi => acl_app_in m (S - K) K i AW0 Hi) Hs ltac:(clear -Hc; lia)).
    - unfold lay_X. apply fl_out_app; [exact (box_sh_out_fpw x Hap Ho)|].
      cbn [outside]. split; [|exact I]. apply (acl_win_sh x (S - K) S SK8). clear -Hw. lia.
  Qed.

  (* A range of application bytes apart from the output block, the window and the side-stack bytes is apart from
     every write of the body so far. *)
  Lemma box_dj_body : forall A n, 0 < n -> (forall i, 0 <= i < n -> app_mem (A + i)) ->
    ly_dj (p + 18) (p + 50) A (A + n) -> ly_dj (S - K) S A (A + n) ->
    fp_dj [(A, A + n)] (fp_w [0%nat; 1%nat] FS) ->
    disjoint_from ([(p + 18, p + 50); (S - K, S)] ++ lay_X) A n.
  Proof.
    intros A n Hn HA D1 D2 D3. unfold ly_dj in D1, D2.
    pose proof HAE as HE. pose proof HHM as HH.
    pose proof (app_range A n Hn HA) as HR.
    unfold APPMEM_END, HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HE, HH.
    assert (B1 : LOWMEM_END <= shadow_addr (S - K) <= HIGHMEM_BEG).
    { apply box_sh_bound. unfold APPMEM_END, CTRL_LAY_BLOCK_K. clear -HE HH. lia. }
    assert (B2 : LOWMEM_END <= shadow_addr S <= HIGHMEM_BEG).
    { apply box_sh_bound. unfold APPMEM_END. clear -HE HH. lia. }
    cbn [app disjoint_from]. split; [clear -D1; lia|]. split; [clear -D2; lia|].
    unfold lay_X. apply disjoint_from_app.
    - apply disjoint_of_in. intros a b Hin. exact (dj_one A n _ D3 a b Hin).
    - cbn [disjoint_from]. split; [|exact I]. unfold LOWMEM_END, HIGHMEM_BEG in B1, B2.
      clear -HR B1 B2. lia.
  Qed.

  (* A byte list of m apart from the output block, the window and the side-stack bytes is still there in mc.
     The empty list needs no apartness. *)
  Lemma box_keep_bytes : forall (mc : word -> option byte) (A : Z) (bs : list byte),
    munch ([(p + 18, p + 50); (S - K, S)] ++ lay_X) m mc ->
    bytes_at rsegs m A bs ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> app_mem (A + i)) ->
    ly_dj (p + 18) (p + 50) A (A + Z.of_nat (length bs)) ->
    ly_dj (S - K) S A (A + Z.of_nat (length bs)) ->
    fp_dj [(A, A + Z.of_nat (length bs))] (fp_w [0%nat; 1%nat] FS) ->
    bytes_at rsegs mc A bs.
  Proof.
    intros mc A bs MU HB HA D1 D2 D3.
    destruct bs as [|b0 bs'].
    - destruct HB as (Ha & Hl & _). split; [exact Ha|]. split; [cbn [length] in Hl |- *; exact Hl|].
      intros i Hi. cbn [length] in Hi. lia.
    - exact (bytes_at_transport rsegs _ m mc A _ HB MU
               (box_dj_body A (Z.of_nat (length (b0 :: bs'))) ltac:(cbn [length]; clear; lia)
                  HA D1 D2 D3)).
  Qed.

  Lemma box_keep_addr : forall (mc : word -> option byte) (A n : Z),
    munch ([(p + 18, p + 50); (S - K, S)] ++ lay_X) m mc ->
    addressable m A n -> ly_dj (S - K) S A (A + n) ->
    fp_dj [(A, A + n)] (fp_w [0%nat; 1%nat] FS) -> addressable mc A n.
  Proof.
    intros mc A n MU HA D2 D3. unfold ly_dj in D2.
    apply (addr_munch _ m mc A n HA MU). intros i Hi.
    apply box_out_body_sh.
    - exact (acl_app_in m A n i HA Hi).
    - clear -D2 Hi. lia.
    - exact (fl_dj_out_r [(A, A + n)] _ A (A + n) (A + i) D3 (or_introl eq_refl) ltac:(clear -Hi; lia)).
  Qed.

  (* The geometry of the box call: the callee's window [spc - 4272, spc) is inside [S - K, S); the frame is the
     real-stack frame at spc (sfr = 0) or a class-1 side-stack frame (sfr = frb, spc = SP2). *)
  Lemma box_geo : forall frb sfr spc j w120, FK frb sfr spc j w120 ->
    spc mod 16 = 0 /\ S - K <= spc - 4272 /\ spc + 128 <= S /\ frb mod 8 = 0 /\ FS + 36864 <= frb /\
    (forall i, 0 <= i < 96 -> app_mem (frb + i)) /\
    ((sfr = 0 /\ spc = frb /\ frb + 96 <= S + -128) \/
     (sfr = frb /\ spc = SP2 /\ FS + 1085440 <= frb /\ frb + 128 <= FS + 2134016)).
  Proof.
    intros frb sfr spc j w120 HK.
    pose proof (fk_facts frb sfr spc j w120 HK) as (M8 & FSlo & FR96 & _ & _ & APPf & _).
    pose proof SP2_facts as (A32 & Alo & Ahi). pose proof SP2_tight as AT.
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & Ej).
    unfold CTRL_LAY_BLOCK_K.
    destruct HK as [(Hs & Hf & Hsp) | (Hj & Hf & Hs & Hsp & _)].
    - split; [rewrite Hsp; clear -A32; Z.div_mod_to_equations; lia|].
      split; [clear -Hsp AT; lia|]. split; [clear -Hsp Ahi; lia|].
      split; [exact M8|]. split; [exact FSlo|]. split; [exact APPf|].
      left. split; [exact Hs|]. split; [clear -Hf Hsp; lia | clear -Hf Ahi; lia].
    - split; [rewrite Hsp; clear -A32; Z.div_mod_to_equations; lia|].
      split; [clear -Hsp AT; lia|]. split; [clear -Hsp Ahi; lia|].
      split; [exact M8|]. split; [exact FSlo|]. split; [exact APPf|].
      right. rewrite E6 in Hj. rewrite Ej in Hf.
      split; [exact Hs|]. split; [exact Hsp|]. split; [clear -Hf Hj; lia | clear -Hf Hj; lia].
  Qed.

  (* reac_box_model_block's writes, called at sp = spc with the output block at frb + 32. *)
  Definition BOXW (frb spc : Z) : list ivl :=
    [(spc - REAC_BOX_MODEL_BLOCK_K, spc); (frb + 32, frb + 64)] ++ reac_box_model_block_X spc FS.

  (* The ranges of BOXW in numbers: the callee's window, its output block, the class-0 hint, flags and frames, and
     shadow bytes. *)
  Lemma box_call_cases : forall frb spc a b, 4272 <= spc <= APPMEM_END -> In (a, b) (BOXW frb spc) ->
    (a = spc - 4272 /\ b = spc) \/ (a = frb + 32 /\ b = frb + 64) \/
    (a = FS /\ b = FS + 8) \/ (a = FS + 4096 /\ b = FS + 20480) \/ (a = FS + 36864 /\ b = FS + 1085440) \/
    (2147450880 <= a /\ b <= 17594333495296).
  Proof.
    intros frb spc a b Hspc Hin. unfold BOXW, reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K in Hin.
    apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    - cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-;
        [left | right; left]; split; reflexivity.
    - apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      + destruct (box_fpw0_cases a b Hin) as [H|[H|[H|H]]];
          [do 2 right; left | do 3 right; left | do 4 right; left | do 5 right]; exact H.
      + cbn [In] in Hin. destruct Hin as [E|[]]. injection E as <- <-. do 5 right.
        pose proof (box_sh_bound (spc - 4272) ltac:(clear -Hspc; lia)) as B1.
        pose proof (box_sh_bound spc ltac:(clear -Hspc; lia)) as B2.
        unfold LOWMEM_END, HIGHMEM_BEG in B1, B2. clear -B1 B2. lia.
  Qed.

  (* A range of application bytes apart from the callee's window, from its output block and from the class-0 hint,
     flags and frames is apart from every write of the box call. *)
  Lemma box_dj_call : forall frb spc A n, 4272 <= spc <= APPMEM_END -> 0 < n ->
    (forall i, 0 <= i < n -> app_mem (A + i)) ->
    (A + n <= spc - 4272 \/ spc <= A) -> (A + n <= frb + 32 \/ frb + 64 <= A) ->
    (A + n <= FS \/ FS + 8 <= A) -> (A + n <= FS + 4096 \/ FS + 20480 <= A) ->
    (A + n <= FS + 36864 \/ FS + 1085440 <= A) ->
    disjoint_from (BOXW frb spc) A n.
  Proof.
    intros frb spc A n Hspc Hn HA D1 D2 D3 D4 D5. pose proof (app_range A n Hn HA) as HR.
    apply disjoint_of_in. intros a b Hin.
    destruct (box_call_cases frb spc a b Hspc Hin) as [E|[E|[E|[E|[E|E]]]]];
      clear -E HR D1 D2 D3 D4 D5; lia.
  Qed.

  (* Every write of the box call is a write of the body: its window is inside the function's window, its output
     block is inside the window (real case) or a part of the class-1 frames (side case), its class-0 side-stack bytes
     are in fp_w [0%nat; 1%nat] FS and the shadow of its window is in the shadow of the function's window. *)
  Lemma box_sub_body : forall frb sfr spc j w120, FK frb sfr spc j w120 ->
    sub_fp (BOXW frb spc) ([(p + 18, p + 50); (S - K, S)] ++ lay_X).
  Proof.
    intros frb sfr spc j w120 HK x HO.
    pose proof (box_geo frb sfr spc j w120 HK) as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    cbn [app outside] in HO. destruct HO as (HR & HW & HO).
    unfold lay_X in HO. destruct (out_app_inv _ _ _ HO) as [HFW HSH].
    cbn [outside] in HSH. destruct HSH as [HSH _].
    unfold BOXW, reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K. cbn [app outside].
    split; [clear -HW G2 G3; lia|].
    split.
    - destruct GC as [(C1 & C2 & C3) | (C1 & C2 & C3 & C4)]; [clear -HW G2 G3 C2; lia|].
      pose proof (out_in _ _ _ _ HFW box_fpw_f1) as H7. rewrite E9, E10 in H7. clear -H7 C3 C4. lia.
    - apply fl_out_app.
      + apply outside_of_in. intros a b Hin. exact (out_in _ _ _ _ HFW (box_fpw0 (a, b) Hin)).
      + cbn [outside]. split; [|exact I].
        pose proof (acl_sh_ge (spc - 4272) (S - K) ltac:(clear -G2; lia)) as H1.
        pose proof (acl_sh_ge S spc ltac:(clear -G3; lia)) as H2.
        clear -HSH H1 H2. lia.
  Qed.

  (* --- small tools --- *)
  Lemma box_stk_sub : forall (mm : word -> option byte) lo hi lo' hi', stk rsegs mm lo hi ->
    0 <= lo' -> lo <= lo' -> hi' <= hi -> hi' <= 2 ^ 64 -> stk rsegs mm lo' hi'.
  Proof.
    intros mm lo hi lo' hi' (H0 & H1 & H) Ha Hb Hc Hd. split; [exact Ha|]. split; [exact Hd|].
    intros a Haa. apply H. clear -Haa Hb Hc. lia.
  Qed.

  Lemma box_addr_pt : forall (mm : word -> option byte) (A n : Z), 0 <= A -> 0 <= n -> A + n <= APPMEM_END ->
    (forall x, A <= x < A + n -> addressable mm x 1) -> addressable mm A n.
  Proof.
    intros mm A n H0 Hn Hhi H. split; [exact H0|]. split; [exact Hn|]. split; [exact Hhi|].
    intros i Hi. destruct (H (A + i) ltac:(clear -Hi; lia)) as (_ & _ & _ & HA).
    pose proof (HA 0 ltac:(clear; lia)) as Hb. rewrite Z.add_0_r in Hb. exact Hb.
  Qed.

  (* The output block and the record at f are apart from the side-stack bytes (FP0's data ranges). *)
  Lemma box_row_fpw : fp_dj [(p + 18, p + 18 + 32)] (fp_w [0%nat; 1%nat] FS).
  Proof.
    pose proof (fl_fp_dj [0%nat; 1%nat] m (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S)
                  (ctrl_lay_block_D p f) FP0) as HD.
    apply dj_mk. intros a b c d Hab Hcd. cbn [In] in Hab. destruct Hab as [E|[]]. injection E as <- <-.
    pose proof (dj_in _ _ (p + 18) (p + 50) c d HD
                  ltac:(unfold ctrl_lay_block_D; cbn [In]; right; left; reflexivity) Hcd) as H.
    unfold ly_dj in H |- *. clear -H. lia.
  Qed.

  Lemma box_f_fpw : fp_dj [(f, f + 24)] (fp_w [0%nat; 1%nat] FS).
  Proof.
    pose proof (fl_fp_dj [0%nat; 1%nat] m (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S)
                  (ctrl_lay_block_D p f) FP0) as HD.
    apply dj_mk. intros a b c d Hab Hcd. cbn [In] in Hab. destruct Hab as [E|[]]. injection E as <- <-.
    exact (dj_in _ _ f (f + 24) c d HD ltac:(unfold ctrl_lay_block_D; cbn [In]; left; reflexivity) Hcd).
  Qed.

  (* The output block and the record at f are apart from the class-1 frames. *)
  Lemma box_row_f1 : (p + 50 <= FS + 1085440 \/ FS + 2134016 <= p + 18) /\
                     (f + 24 <= FS + 1085440 \/ FS + 2134016 <= f).
  Proof.
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    pose proof (dj_one (p + 18) 32 _ box_row_fpw _ _ box_fpw_f1) as H1.
    pose proof (dj_one f 24 _ box_f_fpw _ _ box_fpw_f1) as H2.
    rewrite E9, E10 in H1, H2. split; [clear -H1; lia | clear -H2; lia].
  Qed.

  (* A range apart from the side-stack bytes is apart from the class-0 hint, flags and frames in numbers. *)
  Lemma box_dj_cls0 : forall A n, fp_dj [(A, A + n)] (fp_w [0%nat; 1%nat] FS) ->
    (A + n <= FS \/ FS + 8 <= A) /\ (A + n <= FS + 4096 \/ FS + 20480 <= A) /\
    (A + n <= FS + 36864 \/ FS + 1085440 <= A).
  Proof.
    intros A n H.
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    assert (I1 : In (fs_hint FS 0%nat, fs_hint FS 0%nat + 8) (fp_w [0%nat; 1%nat] FS))
      by (cbn [fp_w fp_w1 flat_map app In]; left; reflexivity).
    assert (I2 : In (fs_flag FS 0%nat 0, fs_flag FS 0%nat 0 + fs_M 0%nat) (fp_w [0%nat; 1%nat] FS))
      by (cbn [fp_w fp_w1 flat_map app In]; right; left; reflexivity).
    assert (I3 : In (fs_frame FS 0%nat 0, fs_frame FS 0%nat (fs_M 0%nat)) (fp_w [0%nat; 1%nat] FS))
      by (cbn [fp_w fp_w1 flat_map app In]; right; right; left; reflexivity).
    pose proof (dj_one A n _ H _ _ I1) as H1. pose proof (dj_one A n _ H _ _ I2) as H2.
    pose proof (dj_one A n _ H _ _ I3) as H3.
    rewrite E1 in H1. rewrite E3, E4 in H2. rewrite E7, E8 in H3.
    split; [clear -H1; lia|]. split; [clear -H2; lia | clear -H3; lia].
  Qed.

  (* A range below the side stack (an image block) is apart from the side-stack bytes. *)
  Lemma box_lo_fpw_dj : forall A n, 0 <= A -> A + n <= ASAN_GT -> fp_dj [(A, A + n)] (fp_w [0%nat; 1%nat] FS).
  Proof.
    intros A n H0 Hn. pose proof box_fs as (F1 & F2 & F3 & _).
    apply dj_mk. intros a b c d Hab Hcd. cbn [In] in Hab. destruct Hab as [E|[]]. injection E as <- <-.
    destruct (box_fpw_cases c d Hcd) as [HB|HB]; unfold ly_dj, ASAN_GT in Hn, F3 |- *;
      clear -Hn HB F3; lia.
  Qed.

  (* ly_bb picks the JOIN block: b = 1 only for k = 5 and b = 2 only for k = 6. *)
  Lemma box_bb5 : ly_bb (ly_k fr) = 1 -> ly_k fr = 5.
  Proof.
    intros HB. unfold ly_bb in HB.
    destruct (Z.eqb_spec (ly_k fr) 3) as [E|_]; [discriminate HB|].
    destruct (Z.eqb_spec (ly_k fr) 4) as [E|_]; [discriminate HB|].
    destruct (Z.eqb_spec (ly_k fr) 5) as [E|_]; [exact E|].
    destruct (Z.eqb_spec (ly_k fr) 6) as [E|_]; [discriminate HB|].
    destruct (Z.eqb_spec (ly_k fr) 7) as [E|_]; [discriminate HB|].
    destruct (Z.eqb_spec (ly_k fr) 8) as [E|_]; discriminate HB.
  Qed.

  Lemma box_bb6 : ly_bb (ly_k fr) = 2 -> ly_k fr = 6.
  Proof.
    intros HB. unfold ly_bb in HB.
    destruct (Z.eqb_spec (ly_k fr) 3) as [E|_]; [discriminate HB|].
    destruct (Z.eqb_spec (ly_k fr) 4) as [E|_]; [discriminate HB|].
    destruct (Z.eqb_spec (ly_k fr) 5) as [E|_]; [discriminate HB|].
    destruct (Z.eqb_spec (ly_k fr) 6) as [E|_]; [exact E|].
    destruct (Z.eqb_spec (ly_k fr) 7) as [E|_]; [discriminate HB|].
    destruct (Z.eqb_spec (ly_k fr) 8) as [E|_]; discriminate HB.
  Qed.

  (* The shadow byte of an application byte apart from the callee's window and from the side-stack bytes is
     outside the box call's writes. *)
  Lemma box_out_call_sh : forall frb spc x, 4272 <= spc <= APPMEM_END -> spc mod 8 = 0 ->
    (forall i, 0 <= i < 4272 -> app_mem (spc - 4272 + i)) ->
    (forall i, 0 <= i < 32 -> app_mem (frb + 32 + i)) ->
    app_mem x -> outside (fp_w [0%nat; 1%nat] FS) x -> (x < spc - 4272 \/ spc <= x) ->
    outside (BOXW frb spc) (shadow_addr x).
  Proof.
    intros frb spc x Hspc M8 Aw Ao Hap Hfpw Hx. pose proof (rt_app_shadow x Hap) as Hs.
    unfold BOXW, reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K. cbn [app outside].
    split.
    { intros Hc. exact (box_app_not_sh (spc - 4272) 4272 _ ltac:(clear; lia) Aw Hs ltac:(clear -Hc; lia)). }
    split.
    { intros Hc. exact (box_app_not_sh (frb + 32) 32 _ ltac:(clear; lia) Ao Hs ltac:(clear -Hc; lia)). }
    apply fl_out_app.
    - apply outside_of_in. intros a b Hin.
      exact (out_in _ _ _ _ (box_sh_out_fpw x Hap Hfpw) (box_fpw0 (a, b) Hin)).
    - cbn [outside]. split; [|exact I].
      apply (acl_win_sh x (spc - 4272) spc ltac:(clear -M8; Z.div_mod_to_equations; lia)).
      clear -Hx. lia.
  Qed.

  (* The output block is apart from the box call's other writes. *)
  Lemma box_dj_out : forall frb spc, 4272 <= spc <= APPMEM_END ->
    (forall i, 0 <= i < 32 -> app_mem (frb + 32 + i)) ->
    (spc <= frb + 32 \/ frb + 64 <= spc - 4272) ->
    (frb + 64 <= FS \/ FS + 1085440 <= frb + 32) ->
    disjoint_from ([(spc - REAC_BOX_MODEL_BLOCK_K, spc)] ++ reac_box_model_block_X spc FS) (frb + 32) 32.
  Proof.
    intros frb spc Hspc Ao D1 D2. pose proof (app_range (frb + 32) 32 ltac:(clear; lia) Ao) as HR.
    unfold reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K. cbn [app disjoint_from].
    split; [clear -D1; lia|].
    apply disjoint_from_app.
    - apply disjoint_of_in. intros a b Hin.
      destruct (box_fpw0_cases a b Hin) as [E|[E|[E|E]]]; clear -E D2 HR; lia.
    - cbn [disjoint_from]. split; [|exact I].
      pose proof (box_sh_bound (spc - 4272) ltac:(clear -Hspc; lia)) as B1.
      pose proof (box_sh_bound spc ltac:(clear -Hspc; lia)) as B2.
      unfold LOWMEM_END, HIGHMEM_BEG in B1, B2. clear -B1 B2 HR. lia.
  Qed.

  (* The box call keeps the output-block carry invariant: it writes only below sp = spc, its own output block
     [frb + 32, frb + 64), the class-0 side-stack bytes and the shadow of its window, so the frame cell at
     [S - 128, S), the output block [p + 18, p + 50) and the record at f keep their bytes; the window's bytes
     read back (its own window from the callee's stk, the output block from the premise). *)
  Lemma LC_after_box : forall (mc m' : word -> option byte) (gj X : list byte) (frb sfr spc j : Z) (w120 : word),
    FK frb sfr spc j w120 -> LC mc gj X ->
    munch (BOXW frb spc) mc m' -> wmono rsegs mc m' -> mem_inv rsegs m' ->
    stk rsegs m' (spc - REAC_BOX_MODEL_BLOCK_K) spc ->
    (forall x, frb + 32 <= x < frb + 64 -> exists bb, mrd rsegs m' (wa x) = Some bb) ->
    LC m' gj X.
  Proof.
    intros mc m' gj X frb sfr spc j w120 HK LCH MUc WMc MIc STc RDo.
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FBc).
    pose proof (box_geo frb sfr spc j w120 HK) as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & _).
    pose proof HAE as HE. pose proof HHM as HH. pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    unfold APPMEM_END in HE. unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HH.
    unfold CTRL_LAY_BLOCK_K in F4, G2. unfold REAC_BOX_MODEL_BLOCK_K in STc.
    assert (SPC : 4272 <= spc <= APPMEM_END) by (unfold APPMEM_END; clear -G2 G3 HE HH; lia).
    assert (AWIN : forall i, 0 <= i < 4512 -> app_mem (S - 4512 + i)).
    { intros i Hi. replace (S - 4512 + i) with (S - K + i) by (unfold CTRL_LAY_BLOCK_K; ring).
      exact (acl_app_in m (S - K) K i AW0 ltac:(unfold CTRL_LAY_BLOCK_K; clear -Hi; lia)). }
    assert (FRB : frb + 64 <= S + -128).
    { destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]; [clear -C3; lia | clear -C4 F4 HH; lia]. }
    assert (BOXLO : forall y, S - 4512 <= y -> y < spc - 4272 -> ~ (frb + 32 <= y < frb + 64)).
    { intros y Hy Hd Hc. destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
        [clear -C2 Hd Hc; lia | clear -C3 C4 Hy Hc F4; lia]. }
    assert (DJF : disjoint_from (BOXW frb spc) (S + -128) 128).
    { apply (box_dj_call frb spc).
      - exact SPC.
      - clear; lia.
      - intros i Hi. replace (S + -128 + i) with (S - 4512 + (4384 + i)) by ring.
        apply AWIN. clear -Hi. lia.
      - right. clear -G3. lia.
      - right. clear -FRB. lia.
      - right. clear -F4 HH. lia.
      - right. clear -F4 HH. lia.
      - right. clear -F4 HH. lia. }
    assert (DJB : disjoint_from (BOXW frb spc) (p + 18) 32).
    { pose proof DJ1 as D1. unfold ly_dj, CTRL_LAY_BLOCK_K in D1.
      pose proof (box_dj_cls0 (p + 18) 32 box_row_fpw) as (Z1 & Z2 & Z3).
      apply (box_dj_call frb spc).
      - exact SPC.
      - clear; lia.
      - intros i Hi. exact (acl_app_in m (p + 18) 32 i AR Hi).
      - clear -D1 G2 G3. lia.
      - destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
          [clear -D1 G2 G3 C2 C3; lia|].
        pose proof box_row_f1 as (R1 & _). clear -R1 C3 C4. lia.
      - exact Z1.
      - exact Z2.
      - exact Z3. }
    assert (DJf : disjoint_from (BOXW frb spc) f 24).
    { pose proof DJ2 as D2. unfold ly_dj, CTRL_LAY_BLOCK_K in D2.
      pose proof (box_dj_cls0 f 24 box_f_fpw) as (Z1 & Z2 & Z3).
      apply (box_dj_call frb spc).
      - exact SPC.
      - clear; lia.
      - intros i Hi. exact (acl_app_in m f 24 i AF Hi).
      - clear -D2 G2 G3. lia.
      - destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
          [clear -D2 G2 G3 C2 C3; lia|].
        pose proof box_row_f1 as (_ & R2). clear -R2 C3 C4. lia.
      - exact Z1.
      - exact Z2.
      - exact Z3. }
    apply LC_intro.
    - apply (rw_cells_transport rsegs _ mc m' _ _ FR MUc WMc).
      replace (Z.of_nat (cells_size (CB 32 gj :: SAVES))) with 128 by reflexivity.
      exact DJF.
    - apply (fl_stk (BOXW frb spc) mc m' (S - K) (bv_unsigned sp + -128) ST MUc WMc).
      intros x Hx. unfold CTRL_LAY_BLOCK_K in Hx.
      destruct (Z_lt_le_dec x (spc - 4272)) as [L1|L1]; [|destruct (Z_lt_le_dec x spc) as [L2|L2]].
      + left. apply outside_of_in. intros a b Hin.
        destruct (box_call_cases frb spc a b SPC Hin) as [E|[E|[E|[E|[E|E]]]]];
          [ clear -E L1; lia
          | destruct E as [Ea Eb]; subst a; subst b; exact (BOXLO x ltac:(clear -Hx; lia) L1)
          | clear -E Hx F4; lia | clear -E Hx F4; lia | clear -E Hx F4; lia | clear -E Hx HH; lia ].
      + right. exact (rd_of_stk m' _ _ STc x ltac:(clear -L1 L2; lia)).
      + destruct (Z_lt_le_dec x (frb + 32)) as [L3|L3]; [|destruct (Z_lt_le_dec x (frb + 64)) as [L4|L4]].
        * left. apply outside_of_in. intros a b Hin.
          destruct (box_call_cases frb spc a b SPC Hin) as [E|[E|[E|[E|[E|E]]]]];
            [clear -E L2 | clear -E L3 | clear -E Hx F4 | clear -E Hx F4 | clear -E Hx F4
             | clear -E Hx HH]; lia.
        * right. exact (RDo x ltac:(clear -L3 L4; lia)).
        * left. apply outside_of_in. intros a b Hin.
          destruct (box_call_cases frb spc a b SPC Hin) as [E|[E|[E|[E|[E|E]]]]];
            [clear -E L2 | clear -E L4 | clear -E Hx F4 | clear -E Hx F4 | clear -E Hx F4
             | clear -E Hx HH]; lia.
    - apply (munch_trans _ m mc m' MU).
      exact (munch_weaken _ _ mc m' (box_sub_body frb sfr spc j w120 HK) MUc).
    - exact (wmono_trans rsegs m mc m' WM WMc).
    - exact MIc.
    - apply (rw_cells_transport rsegs _ mc m' _ _ BK MUc WMc).
      replace (Z.of_nat (cells_size [CB 32 X])) with 32 by reflexivity. exact DJB.
    - apply (bytes_at_transport rsegs _ mc m' _ _ FBc MUc).
      replace (Z.of_nat (length fr)) with 24 by (rewrite FL; reflexivity). exact DJf.
  Qed.

  (* The class-1 side-stack state survives the box call: it writes no byte of the class-1 hint [FS + 8, FS + 16)
     or of the class-1 flag bytes [FS + 20480, FS + 28672). *)
  Lemma box_cls1 : forall (mc m' : word -> option byte) (frb sfr spc j : Z) (w120 : word),
    FK frb sfr spc j w120 -> munch (BOXW frb spc) mc m' -> fp_cls mc FS 1%nat -> fp_cls m' FS 1%nat.
  Proof.
    intros mc m' frb sfr spc j w120 HK MU (Hc & h & flags & HH8 & HF & HFl & HFb).
    pose proof (box_geo frb sfr spc j w120 HK) as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & _).
    pose proof HAE as HE. pose proof HHM as HHm.
    unfold APPMEM_END in HE. unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HHm.
    unfold CTRL_LAY_BLOCK_K in F4, G2.
    assert (SPC : 4272 <= spc <= APPMEM_END) by (unfold APPMEM_END; clear -G2 G3 HE HHm; lia).
    assert (FRBlo : FS + 1085440 <= frb).
    { destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]; [clear -C2 G2 F4; lia | exact C3]. }
    assert (DJh : disjoint_from (BOXW frb spc) (FS + 8) 8).
    { apply (box_dj_call frb spc).
      - exact SPC.
      - clear; lia.
      - intros i Hi. replace (FS + 8 + i) with (FS + (8 + i)) by ring. apply F5. clear -Hi. lia.
      - left. clear -F4 G2. lia.
      - left. clear -FRBlo. lia.
      - right. clear; lia.
      - left. clear; lia.
      - left. clear; lia. }
    assert (DJfl : disjoint_from (BOXW frb spc) (FS + 20480) 8192).
    { apply (box_dj_call frb spc).
      - exact SPC.
      - clear; lia.
      - intros i Hi. replace (FS + 20480 + i) with (FS + (20480 + i)) by ring. apply F5. clear -Hi. lia.
      - left. clear -F4 G2. lia.
      - left. clear -FRBlo. lia.
      - right. clear; lia.
      - right. clear; lia.
      - left. clear; lia. }
    split; [exact Hc|]. exists h, flags.
    split.
    { apply (bytes_at_transport rsegs _ mc m' _ _ HH8 MU). rewrite E2.
      replace (Z.of_nat (length (le8 h))) with 8 by (rewrite length_le8; reflexivity). exact DJh. }
    split.
    { apply (bytes_at_transport rsegs _ mc m' _ _ HF MU). rewrite E5.
      replace (Z.of_nat (length flags)) with 8192 by (rewrite HFl, E6; reflexivity). exact DJfl. }
    split; [exact HFl | exact HFb].
  Qed.

  (* The box call keeps the frame invariant: the callee's post gives asan_cells, shadow_rw, its window addressable
     and its class-0 fp; the class-1 state, the thread cells and the flag-pointer word are untouched (fl_fp_ret,
     ly_epi_tls_free), and every window byte outside the frame is addressable (inside the callee's window from its
     post, elsewhere by transport). *)
  Lemma FI_after_box : forall (mc m' : word -> option byte) (frb sfr spc j : Z) (w120 : word) (W' D' : list ivl),
    FI mc frb sfr spc j w120 ->
    munch (BOXW frb spc) mc m' -> wmono rsegs mc m' ->
    asan_cells m' -> shadow_rw m' ->
    addressable m' (spc - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    fp [0%nat] m' (bv_unsigned tp) FS (spc - REAC_BOX_MODEL_BLOCK_K) spc W' D' ->
    FI m' frb sfr spc j w120.
  Proof.
    intros mc m' frb sfr spc j w120 W' D' FIH MU WM AC' SR' AW' FP'.
    pose proof FIH as (HK & HFL & ACc & SRc & FPc & TLc & AWx).
    pose proof (box_geo frb sfr spc j w120 HK) as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    pose proof HAE as HE. pose proof HHM as HHm.
    unfold APPMEM_END in HE. unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HHm.
    unfold CTRL_LAY_BLOCK_K in F4, G2. unfold REAC_BOX_MODEL_BLOCK_K in AW'.
    assert (SPC : 4272 <= spc <= APPMEM_END) by (unfold APPMEM_END; clear -G2 G3 HE HHm; lia).
    assert (SPC8 : spc mod 8 = 0) by (clear -G1; Z.div_mod_to_equations; lia).
    assert (AW1 : forall y, S - K <= y < S -> app_mem y).
    { intros y Hy. replace y with (S - K + (y - (S - K))) by ring.
      apply (acl_app_in m (S - K) K); [exact AW0 | unfold CTRL_LAY_BLOCK_K in Hy |- *; clear -Hy; lia]. }
    assert (AWIN : forall i, 0 <= i < 4272 -> app_mem (spc - 4272 + i)).
    { intros i Hi. apply AW1. unfold CTRL_LAY_BLOCK_K. clear -Hi G2 G3. lia. }
    assert (AOUT : forall i, 0 <= i < 32 -> app_mem (frb + 32 + i)).
    { intros i Hi. replace (frb + 32 + i) with (frb + (32 + i)) by ring. apply G6. clear -Hi. lia. }
    assert (SUB : sub_fp (BOXW frb spc)
                    (ctrl_lay_block_W p S ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (S - K), shadow_addr S)])).
    { intros x HO. apply (box_sub_body frb sfr spc j w120 HK).
      unfold ctrl_lay_block_W in HO. cbn [app outside] in HO |- *. unfold lay_X.
      destruct HO as (H1 & H2 & H3). split; [exact H2|]. split; [exact H1 | exact H3]. }
    split; [exact HK|].
    split.
    { intros Hsfr. pose proof (HFL Hsfr) as HB.
      destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]; [exfalso; exact (Hsfr C1)|].
      apply (bytes_at_transport rsegs _ mc m' _ _ HB MU).
      replace (Z.of_nat (length (le8 w120))) with 8 by (rewrite length_le8; reflexivity).
      apply (box_dj_call frb spc).
      - exact SPC.
      - clear; lia.
      - intros i Hi. replace (frb + 120 + i) with (FS + (frb + 120 + i - FS)) by ring.
        apply F5. clear -Hi C3 C4. lia.
      - left. clear -C4 F4 G2. lia.
      - right. clear; lia.
      - right. clear -C3. lia.
      - right. clear -C3. lia.
      - right. clear -C3. lia. }
    split; [exact AC'|]. split; [exact SR'|].
    split.
    { pose proof FP' as (DT & TS & C & T & DB & kk & HT & HTP & HP & H88 & H96 & HCL & _).
      assert (FP1 : fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (FS + 11571200) (FS + 11571200) [] []).
      { exists DT, TS, C, T, DB, kk.
        split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|]. split; [exact H96|].
        split.
        { constructor; [|constructor; [|constructor]].
          - rewrite Forall_forall in HCL. apply HCL. cbn [In]. left. reflexivity.
          - apply (box_cls1 mc m' frb sfr spc j w120 HK MU).
            pose proof FPc as (DTa & TSa & Ca & Ta & DBa & ka & _ & _ & _ & _ & _ & HCLc & _).
            rewrite Forall_forall in HCLc. apply HCLc. cbn [In]. right. left. reflexivity. }
        split; [unfold FS_SIZE; clear; lia|].
        split; [intros a Ha; exfalso; clear -Ha; lia|].
        split; [constructor | constructor]. }
      exact (fl_fp_ret [0%nat; 1%nat] mc m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S)
               (ctrl_lay_block_D p f) [(shadow_addr (S - K), shadow_addr S)] (BOXW frb spc)
               (FS + 11571200) (FS + 11571200) [] [] FPc TLc MU SUB FP1). }
    split.
    { exact (ly_epi_tls_free [0%nat; 1%nat] mc m' (bv_unsigned tp) FS (S - K) S (ctrl_lay_block_W p S)
               (ctrl_lay_block_D p f) (BOXW frb spc)
               (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (S - K), shadow_addr S)]) FPc MU SUB TLc TLc). }
    intros x Hx Hfr.
    destruct (Z_lt_le_dec x (spc - 4272)) as [L1|L1]; [|destruct (Z_lt_le_dec x spc) as [L2|L2]].
    - apply (addr_munch (BOXW frb spc) mc m' x 1 (AWx x Hx Hfr) MU). intros i Hi.
      replace (x + i) with x by (clear -Hi; lia).
      exact (box_out_call_sh frb spc x SPC SPC8 AWIN AOUT (AW1 x Hx)
               (box_win_out_fpw x ltac:(clear -Hx; lia)) (or_introl L1)).
    - exact (acl_addr_sub m' (spc - 4272) 4272 x 1 AW' ltac:(clear -L1; lia) ltac:(clear; lia)
               ltac:(clear -L2; lia)).
    - apply (addr_munch (BOXW frb spc) mc m' x 1 (AWx x Hx Hfr) MU). intros i Hi.
      replace (x + i) with x by (clear -Hi; lia).
      exact (box_out_call_sh frb spc x SPC SPC8 AWIN AOUT (AW1 x Hx)
               (box_win_out_fpw x ltac:(clear -Hx; lia)) (or_intror L2)).
  Qed.

  (* The output block stays addressable across the box call: none of the writes is one of its shadow bytes. *)
  Lemma box_out_addr : forall (mc m' : word -> option byte) (frb sfr spc j : Z) (w120 : word),
    FK frb sfr spc j w120 -> munch (BOXW frb spc) mc m' -> addressable mc (frb + 32) 32 ->
    addressable m' (frb + 32) 32.
  Proof.
    intros mc m' frb sfr spc j w120 HK MU AO.
    pose proof (box_geo frb sfr spc j w120 HK) as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    pose proof HAE as HE. pose proof HHM as HHm.
    unfold APPMEM_END in HE. unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HHm.
    unfold CTRL_LAY_BLOCK_K in F4, G2.
    assert (SPC8 : spc mod 8 = 0) by (clear -G1; Z.div_mod_to_equations; lia).
    assert (M36 : (FS + 36864) mod 8 = 0) by (clear -F2; Z.div_mod_to_equations; lia).
    assert (AOUT : forall i, 0 <= i < 32 -> app_mem (frb + 32 + i)).
    { intros i Hi. replace (frb + 32 + i) with (frb + (32 + i)) by ring. apply G6. clear -Hi. lia. }
    assert (AWIN : forall i, 0 <= i < 4272 -> app_mem (spc - 4272 + i)).
    { intros i Hi. replace (spc - 4272 + i) with (S - K + (spc - 4272 + i - (S - K)))
        by (unfold CTRL_LAY_BLOCK_K; ring).
      apply (acl_app_in m (S - K) K); [exact AW0 | unfold CTRL_LAY_BLOCK_K; clear -Hi G2 G3; lia]. }
    apply (addr_munch (BOXW frb spc) mc m' (frb + 32) 32 AO MU). intros i Hi.
    pose proof (rt_app_shadow (frb + 32 + i) (AOUT i Hi)) as Hs.
    unfold BOXW, reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K. cbn [app outside].
    split.
    { intros Hc. exact (box_app_not_sh (spc - 4272) 4272 _ ltac:(clear; lia) AWIN Hs ltac:(clear -Hc; lia)). }
    split.
    { intros Hc. exact (box_app_not_sh (frb + 32) 32 _ ltac:(clear; lia) AOUT Hs ltac:(clear -Hc; lia)). }
    apply fl_out_app.
    - cbn [fp_w fp_w1 flat_map app outside].
      split.
      { intros Hc. exact (box_app_not_sh FS 11571200 _ ltac:(clear; lia) F5 Hs ltac:(clear -E1 Hc; lia)). }
      split.
      { intros Hc. exact (box_app_not_sh FS 11571200 _ ltac:(clear; lia) F5 Hs
          ltac:(clear -E3 E4 Hc; lia)). }
      split.
      { intros Hc. exact (box_app_not_sh FS 11571200 _ ltac:(clear; lia) F5 Hs
          ltac:(clear -E7 E8 Hc; lia)). }
      split; [|exact I].
      apply (acl_win_sh (frb + 32 + i) (fs_frame FS 0%nat 0) (fs_frame FS 0%nat (fs_M 0%nat))
               ltac:(rewrite E7; exact M36)).
      rewrite E7, E8. destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
        [clear -C2 G2 F4 Hi; lia | clear -C3 Hi; lia].
    - cbn [outside]. split; [|exact I].
      apply (acl_win_sh (frb + 32 + i) (spc - 4272) spc
               ltac:(clear -SPC8; Z.div_mod_to_equations; lia)).
      destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
        [clear -C2 Hi; lia | clear -C3 C4 F4 G2 Hi; lia].
  Qed.

  (* fp for the box call's window: the class-0 side-stack state, the callee's window inside the function's, and
     its writes (its window and its output block) apart from the thread cells and the side stack's header (in the
     side case the output block is a class-1 frame, which the tls premise keeps apart from them). *)
  Lemma box_fp_call : forall (mc : word -> option byte) (frb sfr spc j : Z) (w120 : word),
    FK frb sfr spc j w120 -> FI mc frb sfr spc j w120 ->
    (md <> 0 -> fp_dj [(md, md + 296)] (fp_w [0%nat; 1%nat] FS)) ->
    fp [0%nat] mc (bv_unsigned tp) FS (spc - REAC_BOX_MODEL_BLOCK_K) spc
      (reac_box_model_block_W (frb + 32) spc) (reac_box_model_block_D md (frb + 32)).
  Proof.
    intros mc frb sfr spc j w120 HK FIH FPMd.
    pose proof FIH as (_ & _ & ACc & SRc & FPc & TLc & AWx).
    pose proof (box_geo frb sfr spc j w120 HK) as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    pose proof HAE as HE. pose proof HHM as HHm.
    unfold APPMEM_END in HE. unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HHm.
    unfold CTRL_LAY_BLOCK_K in F4, G2.
    pose proof (app_range frb 96 ltac:(clear; lia) G6) as FRA.
    pose proof FPc as (DT & TS & C & T & DB & kk & HT & HTP & HP & H88 & H96 & HCL & HFS & HAP & HWd & HDd).
    assert (O0 : ((frb + 32) =? 0) = false) by (apply Z.eqb_neq; clear -G5 F1; lia).
    assert (DOUT : fp_dj [(frb + 32, frb + 32 + 32)] (fp_w [0%nat] FS)).
    { apply dj_mk. intros a b c d Hab Hcd. cbn [In] in Hab. destruct Hab as [E|[]]. injection E as <- <-.
      destruct (box_fpw0_cases c d Hcd) as [E|[E|[E|E]]]; unfold ly_dj.
      - destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
          [clear -E C2 G2 F4; lia | clear -E C3; lia].
      - destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
          [clear -E C2 G2 F4; lia | clear -E C3; lia].
      - destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
          [clear -E C2 G2 F4; lia | clear -E C3; lia].
      - clear -E FRA. lia. }
    exists DT, TS, C, T, DB, kk.
    split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|]. split; [exact H96|].
    split.
    { rewrite Forall_forall in HCL |- *. intros c Hin. apply HCL. cbn [In] in Hin |- *.
      destruct Hin as [E|[]]. left. exact E. }
    split; [unfold FS_SIZE, REAC_BOX_MODEL_BLOCK_K; clear -F4 G2; lia|].
    split.
    { intros a Ha. unfold REAC_BOX_MODEL_BLOCK_K in Ha. apply HAP.
      unfold CTRL_LAY_BLOCK_K. clear -Ha G2 G3. lia. }
    split.
    { unfold reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K. rewrite O0. cbn [app].
      apply dj_mk. intros a b c d Hab Hcd. cbn [In] in Hab.
      destruct Hab as [E|[E|[]]]; injection E as <- <-.
      - pose proof (dj_in _ _ (S - K) S c d HWd
                      ltac:(unfold ctrl_lay_block_W; cbn [In]; left; reflexivity) Hcd) as H.
        unfold ly_dj, CTRL_LAY_BLOCK_K in H |- *. clear -H G2 G3. lia.
      - destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)].
        + pose proof (dj_in _ _ (S - K) S c d HWd
                        ltac:(unfold ctrl_lay_block_W; cbn [In]; left; reflexivity) Hcd) as H.
          unfold ly_dj, CTRL_LAY_BLOCK_K in H |- *. clear -H G2 G3 C2 C3. lia.
        + apply in_app_or in Hcd. destruct Hcd as [Hcd|Hcd].
          * pose proof (TLc DT TS C T DB kk HT) as TD.
            pose proof (dj_in _ _ c d _ _ TD Hcd (in_or_app _ _ _ (or_introl box_fpw_f1))) as H.
            unfold ly_dj in H |- *. rewrite E9, E10 in H. clear -H C3 C4. lia.
          * cbn [In] in Hcd. destruct Hcd as [E|[]]. injection E as <- <-.
            unfold ly_dj. rewrite E7. clear -C3. lia. }
    unfold reac_box_model_block_D. rewrite O0. cbn [app].
    apply dj_mk. intros a b c d Hab Hcd.
    destruct (Z.eqb_spec md 0) as [M0|M0]; cbn [app In] in Hab.
    - destruct Hab as [E|[]]; injection E as <- <-.
      exact (dj_in _ _ (frb + 32) (frb + 32 + 32) c d DOUT (or_introl eq_refl) Hcd).
    - destruct Hab as [E|[E|[]]]; injection E as <- <-.
      + exact (dj_in _ _ md (md + 296) c d (FPMd M0) (or_introl eq_refl) (box_fpw0 (c, d) Hcd)).
      + exact (dj_in _ _ (frb + 32) (frb + 32 + 32) c d DOUT (or_introl eq_refl) Hcd).
  Qed.

  Lemma BASE_box : 3 <= ly_k fr <= 9 -> BASE = ly_Z md mb nb (ly_bb (ly_k fr)).
  Proof.
    intros KB. unfold BASE, ly_base.
    rewrite (proj2 (Z.eqb_neq (ly_k fr) 0) ltac:(lia)), (proj2 (Z.eqb_neq (ly_k fr) 1) ltac:(lia)),
      (proj2 (Z.eqb_neq (ly_k fr) 2) ltac:(lia)).
    reflexivity.
  Qed.

  (* 0x85818: s7 = frb + 32 (the frame's middle 32 bytes), a0 = s6 = md, a2 = s7, then
     reac_box_model_block(md, b, frb + 32) by its contract.  At 0x85828 the result r is -1 (md = 0) or
     rc mb b, and r = 1 means the output block holds BASE; LC, FI and the addressable output block carry
     across the call (LC_after_box, FI_after_box, box_out_addr). *)
  Lemma ly_boxcall : reac_box_model_block_contract ->
    forall (b : Z) (mc : word -> option byte) (gj : list byte) (frb sfr spc j : Z) (w120 : word)
      (xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    (forall (mc' : word -> option byte) (gj' : list byte) (r : Z)
       (xra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       FI mc' frb sfr spc j w120 -> LC mc' gj' ly_zero -> addressable mc' (frb + 32) 32 ->
       -1 <= r <= 1 -> (r = 1 -> bytes_at rsegs mc' (frb + 32) BASE /\ length BASE = 32%nat) ->
       (r <> 1 -> BASE = ly_zero) ->
       0 <= frb + 32 < 2 ^ 64 -> app_mem (frb + 64) ->
       (frb + 64 <= p + 18 \/ p + 50 <= frb + 32) -> (frb + 64 <= S - K \/ spc <= frb + 32) ->
       evt rsegs Q
         (MS (mkR xra' (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 SP2)
                  (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f) (Z_to_bv 64 (p + 18))
                  (Z_to_bv 64 md) (Z_to_bv 64 (frb + 32))
                  (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
                  t3' t4' t5' t6')
             F (Z_to_bv 64 0x85828) fc None mc' (seg_rom rsegs))) ->
    b = ly_bb (ly_k fr) -> 3 <= ly_k fr <= 9 -> FI mc frb sfr spc j w120 -> LC mc gj ly_zero ->
    addressable mc (frb + 32) 32 ->
    evt rsegs Q
      (MS (mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 SP2) x10 (Z_to_bv 64 b)
               x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
               (Z_to_bv 64 (p + 18)) (Z_to_bv 64 md) (Z_to_bv 64 p)
               (Z_to_bv 64 (shadow_addr frb)) (Z_to_bv 64 frb) (Z_to_bv 64 ASAN_K) s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x85818) fc None mc (seg_rom rsegs)).
  Proof using AF AJ5 AJ6 AMD AR ARDJ AW0 DB3 DBN DJ1 DJ2 DJ3m FL FP0 FPM HAE HHM K9 MDP P0 Rf Rg Rmd Rp SP16 SR0 ST0
    TM.
    clear DJ3 DJ3g F8 F24 FB AOL P50 BLK DB1 DB2 GP MI0 AC0 AP50 ATM AG FPT FPG TLS0 HSM MEMS MEMC BOX.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    unfold rs_hold in DJ3m, DB3, DBN, MDP, AMD, AJ5, AJ6, FPM.
    intros BOXC b mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      KB -> KB9 FIH LCH AO.
    pose proof FIH as (HK & HFL & ACc & SRc & FPc & TLc & AWx).
    pose proof LCH as (FR & ST & MU & WM & MI & BK & FBc).
    pose proof (box_geo frb sfr spc j w120 HK) as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
    pose proof box_fs as (F1 & F2 & F3 & F4 & F5 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    pose proof HAE as HE. pose proof HHM as HHm. pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    unfold APPMEM_END in HE. unfold HIGHMEM_BEG, CTRL_LAY_BLOCK_K in HHm.
    unfold CTRL_LAY_BLOCK_K in F4, G2.
    assert (RFRB : 0 <= frb /\ frb + 128 <= 2 ^ 64).
    { change (2 ^ 64) with 18446744073709551616.
      destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
        [clear -C3 F1 G5 HE; lia | clear -C3 C4 F1 F4 HE; lia]. }
    assert (SPC : 4272 <= spc <= APPMEM_END) by (unfold APPMEM_END; clear -G2 G3 HE HHm; lia).
    assert (BBR : 0 <= ly_bb (ly_k fr) <= 6).
    { clear. unfold ly_bb.
      repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. }
    assert (AOUT : forall i, 0 <= i < 32 -> app_mem (frb + 32 + i)).
    { intros i Hi. replace (frb + 32 + i) with (frb + (32 + i)) by ring. apply G6. clear -Hi. lia. }
    (* the frame's bytes are readable and writable in mc *)
    assert (FRW : forall i, 0 <= i < 96 -> wview rsegs mc (wa (frb + i)) <> None /\
                            exists bb, mrd rsegs mc (wa (frb + i)) = Some bb).
    { intros i Hi. destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)].
      - destruct ST as (_ & _ & HS). apply HS. unfold CTRL_LAY_BLOCK_K. clear -C2 C3 G2 Hi. lia.
      - pose proof FPc as (DTa & TSa & Ca & Ta & DBa & ka & _ & _ & (_ & _ & _ & _ & P5) & _).
        destruct P5 as (_ & _ & HS). apply HS. unfold FS_SIZE. clear -C3 C4 Hi. lia. }
    destruct (bytes_at_of_rd 32 mc (frb + 32) ltac:(clear -RFRB; lia) ltac:(clear -RFRB; lia)
                ltac:(intros i Hi;
                      replace (frb + 32 + Z.of_nat i) with (frb + (32 + Z.of_nat i)) by ring;
                      exact (proj2 (FRW (32 + Z.of_nat i) ltac:(clear -Hi; lia)))))
      as (obx & OL & OB).
    assert (OW : wr_at rsegs mc (frb + 32) 32).
    { split; [clear -RFRB; lia|]. split; [clear -RFRB; lia|].
      intros i Hi. replace (frb + 32 + i) with (frb + (32 + i)) by ring.
      exact (proj1 (FRW (32 + i) ltac:(clear -Hi; lia))). }
    assert (RWO : rw_cells rsegs mc (frb + 32) [CB 32 obx])
      by (apply ly_rw_cb_eq; [exact OL | exact OB | exact OW]).
    (* the three moves and the call (the step tactic normalises frb + 32 and md) *)
    assert (SPC64 : 0 <= spc < 2 ^ 64).
    { pose proof SPC as SPC'. unfold APPMEM_END in SPC'.
      change (2 ^ 64) with 18446744073709551616. clear -SPC'. lia. }
    assert (USP : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; exact SPC64).
    step. step. step. step.
    eapply evt_cut.
    { eapply BOXC with (p := md) (b := ly_bb (ly_k fr)) (o := frb + 32) (FS := FS) (row := mb) (nb := nb)
        (ob := obx).
      all: rewrite ?USP.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact Rmd.
      - clear -BBR. lia.
      - clear -RFRB. lia.
      - clear -G1. Z.div_mod_to_equations. lia.
      - exact (box_stk_sub mc (S - K) (bv_unsigned sp + -128) (spc - REAC_BOX_MODEL_BLOCK_K) spc ST
                 ltac:(unfold REAC_BOX_MODEL_BLOCK_K; clear -G2 HHm; lia)
                 ltac:(unfold REAC_BOX_MODEL_BLOCK_K, CTRL_LAY_BLOCK_K; clear -G2; lia)
                 ltac:(clear -G3; lia) ltac:(clear -SPC64; lia)).
      - intros M0. destruct (MDP KB9 M0) as (M8 & ML & MB & _).
        destruct (DJ3m KB9 M0) as (DS & _). unfold ly_dj, CTRL_LAY_BLOCK_K in DS.
        destruct (FPM KB9 M0) as (FPmd & _).
        destruct (AMD KB9 M0) as (AMDa & _).
        pose proof (dj_one md 296 _ FPmd _ _ box_fpw_f1) as MDF. rewrite E9, E10 in MDF.
        split; [exact M8|]. split; [exact ML|].
        split.
        { apply (box_keep_bytes mc md mb MU MB).
          - intros i Hi. rewrite ML in Hi. apply (acl_app_in m md 296 i AMDa). clear -Hi. lia.
          - rewrite ML. exact (DB3 KB9 M0).
          - rewrite ML. unfold ly_dj, CTRL_LAY_BLOCK_K. clear -DS. lia.
          - rewrite ML. exact FPmd. }
        split; [unfold REAC_BOX_MODEL_BLOCK_K; clear -DS G2 G3; lia|].
        right. destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
          [clear -DS G2 G3 C2 C3; lia | clear -MDF C3 C4; lia].
      - intros M0 HB5 HH1 HR. destruct (MDP KB9 M0) as (_ & _ & _ & NM).
        destruct (NM HB5 HH1 HR) as (NO & NB).
        destruct (DJ3m KB9 M0) as (_ & DN). pose proof (DN HB5 HH1 HR) as DNm.
        unfold ly_dj, CTRL_LAY_BLOCK_K in DNm.
        destruct (FPM KB9 M0) as (_ & FPn). pose proof (FPn HB5 HH1 HR) as FPnm.
        destruct (AMD KB9 M0) as (_ & AMn). pose proof (AMn HB5 HH1 HR) as AMnm.
        pose proof (dj_one (rname mb) (Z.of_nat (length nb)) _ FPnm _ _ box_fpw_f1) as NF.
        rewrite E9, E10 in NF.
        split; [exact NO|].
        split.
        { apply (box_keep_bytes mc (rname mb) nb MU NB).
          - intros i Hi. exact (acl_app_in m (rname mb) (Z.of_nat (length nb)) i AMnm Hi).
          - exact (DBN KB9 M0 HB5 HH1 HR).
          - unfold ly_dj, CTRL_LAY_BLOCK_K. clear -DNm. lia.
          - exact FPnm. }
        split; [unfold REAC_BOX_MODEL_BLOCK_K; clear -DNm G2 G3; lia|].
        right. destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
          [clear -DNm G2 G3 C2 C3; lia | clear -NF C3 C4; lia].
      - intros _. split; [exact RWO|].
        split; [unfold REAC_BOX_MODEL_BLOCK_K;
                destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
                [clear -C2; lia | clear -C3 C4 F4 G2; lia]|].
        right. unfold JOIN_0014. unfold ASAN_GT in F3. clear -G5 F3. lia.
      - exact MI.
      - exact ACc.
      - exact SRc.
      - unfold REAC_BOX_MODEL_BLOCK_K, HIGHMEM_BEG. clear -G2 HHm. lia.
      - exact (proj2 SPC).
      - unfold REAC_BOX_MODEL_BLOCK_K.
        apply box_addr_pt; [clear -G2 HHm; lia | clear; lia | unfold APPMEM_END; clear -G3 HE; lia|].
        intros x Hx. apply AWx; [unfold CTRL_LAY_BLOCK_K; clear -Hx G2 G3; lia|].
        destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
          [left; clear -Hx C2; lia | right; clear -Hx C3 C4 F4 G2; lia].
      - intros M0. destruct (DJ3m KB9 M0) as (DS & _). unfold ly_dj, CTRL_LAY_BLOCK_K in DS.
        destruct (FPM KB9 M0) as (FPmd & _). destruct (AMD KB9 M0) as (AMDa & _).
        apply (box_keep_addr mc md 296 MU AMDa);
          [unfold ly_dj, CTRL_LAY_BLOCK_K; clear -DS; lia | exact FPmd].
      - intros M0 HB5 HH1 HR.
        destruct (DJ3m KB9 M0) as (_ & DN). pose proof (DN HB5 HH1 HR) as DNm.
        unfold ly_dj, CTRL_LAY_BLOCK_K in DNm.
        destruct (FPM KB9 M0) as (_ & FPn). pose proof (FPn HB5 HH1 HR) as FPnm.
        destruct (AMD KB9 M0) as (_ & AMn). pose proof (AMn HB5 HH1 HR) as AMnm.
        apply (box_keep_addr mc (rname mb) (Z.of_nat (length nb)) MU AMnm);
          [unfold ly_dj, CTRL_LAY_BLOCK_K; clear -DNm; lia | exact FPnm].
      - intros _. split; [exact AO|].
        split; [replace (frb + 32 + 32) with (frb + 64) by ring; apply G6; clear; lia|].
        right. unfold RT_HI. unfold ASAN_GT in F3. clear -G5 F3. lia.
      - intros HB1. pose proof (box_bb5 HB1) as K5.
        apply (box_keep_addr mc JOIN_0014 32 MU (AJ5 K5));
          [unfold ly_dj, JOIN_0014, CTRL_LAY_BLOCK_K; clear -HHm; lia
           | apply box_lo_fpw_dj; unfold JOIN_0014, ASAN_GT; clear; lia].
      - intros HB2. pose proof (box_bb6 HB2) as K6.
        apply (box_keep_addr mc JOIN_0013 32 MU (AJ6 K6));
          [unfold ly_dj, JOIN_0013, CTRL_LAY_BLOCK_K; clear -HHm; lia
           | apply box_lo_fpw_dj; unfold JOIN_0013, ASAN_GT; clear; lia].
      - exact (box_fp_call mc frb sfr spc j w120 HK FIH (fun M0 => proj1 (FPM KB9 M0))).
      - intros M0 HB5 HH1 HR. destruct (FPM KB9 M0) as (_ & FPn).
        apply (dj_cover _ (fp_w [0%nat; 1%nat] FS)); [exact (FPn HB5 HH1 HR)|].
        intros c d Hcd. exists c, d. split; [exact (box_fpw0 (c, d) Hcd)|]. split; clear; lia.
      - intros DT TS C T DB kk HT. pose proof (TLc DT TS C T DB kk HT) as TD.
        apply (dj_cover _ (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr (S - K), shadow_addr S)])); [exact TD|].
        intros c d Hcd. apply in_app_or in Hcd. destruct Hcd as [Hcd|Hcd].
        + exists c, d. split; [apply in_or_app; left; exact (box_fpw0 (c, d) Hcd)|].
          split; clear; lia.
        + cbn [In] in Hcd. destruct Hcd as [E|[]]. injection E as <- <-.
          exists (shadow_addr (S - K)), (shadow_addr S).
          split; [apply in_or_app; right; cbn [In]; left; reflexivity|].
          split; [apply acl_sh_ge; unfold REAC_BOX_MODEL_BLOCK_K, CTRL_LAY_BLOCK_K; clear -G2; lia
                 | apply acl_sh_ge; clear -G3; lia]. }
    intros ms' POST. unfold reac_box_model_block_post in POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                      -> & MW & WMc & MIc & STc & ACc' & SRc' & AWc' & FPc' & TLc').
    rewrite USP in MW, STc, AWc', FPc', TLc'.
    replace (ret_pc (Z_to_bv 64 0x85828)) with (Z_to_bv 64 0x85828)
      by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    assert (O0 : ((frb + 32) =? 0) = false) by (apply Z.eqb_neq; clear -G5 F1; lia).
    rewrite O0, orb_false_r in MW. rewrite O0, orb_false_r.
    assert (DJO : disjoint_from ([(spc - REAC_BOX_MODEL_BLOCK_K, spc)] ++ reac_box_model_block_X spc FS)
                    (frb + 32) 32).
    { apply box_dj_out; [exact SPC | exact AOUT | |].
      - destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
          [left; clear -C2; lia | right; unfold REAC_BOX_MODEL_BLOCK_K; clear -C3 C4 F4 G2; lia].
      - destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
          [right; clear -C2 G2 F4; lia | right; clear -C3; lia]. }
    assert (KBrow : frb + 64 <= p + 18 \/ p + 50 <= frb + 32).
    { pose proof DJ1 as D1. unfold ly_dj, CTRL_LAY_BLOCK_K in D1.
      destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)]; [clear -D1 G2 G3 C2 C3; lia|].
      pose proof box_row_f1 as (R1 & _). clear -R1 C3 C4. lia. }
    assert (KBwin : frb + 64 <= S - K \/ spc <= frb + 32).
    { destruct GC as [(C1 & C2 & C3)|(C1 & C2 & C3 & C4)];
        [right; clear -C2; lia | left; unfold CTRL_LAY_BLOCK_K; clear -C3 C4 F4; lia]. }
    destruct (Z.eqb_spec md 0) as [M0|M0]; cbv iota in MW |- *.
    - (* md = 0: the callee writes nothing in the output block and returns -1 *)
      assert (MUc : munch (BOXW frb spc) mc m').
      { apply (munch_weaken ([(spc - REAC_BOX_MODEL_BLOCK_K, spc)] ++ reac_box_model_block_X spc FS)
                 (BOXW frb spc) mc m'); [|exact MW].
        intros x Hx. unfold BOXW in Hx. cbn [app outside] in Hx |- *.
        destruct Hx as (H1 & _ & H3). split; [exact H1 | exact H3]. }
      assert (OB' : bytes_at rsegs m' (frb + 32) obx).
      { apply (bytes_at_transport rsegs _ mc m' _ _ OB MW).
        replace (Z.of_nat (length obx)) with 32 by (rewrite OL; reflexivity). exact DJO. }
      apply (KB m' gj (-1) (Z_to_bv 64 0x85828) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6').
      + exact (FI_after_box mc m' frb sfr spc j w120 _ _ FIH MUc WMc ACc' SRc' AWc' FPc').
      + apply (LC_after_box mc m' gj ly_zero frb sfr spc j w120 HK LCH MUc WMc MIc STc).
        intros x Hx. apply (rd_of_bytes m' (frb + 32) obx OB'). rewrite OL. clear -Hx. lia.
      + exact (box_out_addr mc m' frb sfr spc j w120 HK MUc AO).
      + clear; lia.
      + intros H1. exfalso. clear -H1. lia.
      + intros _. rewrite (BASE_box KB9). unfold ly_Z.
        rewrite (proj2 (Z.eqb_eq md 0) M0). reflexivity.
      + clear -RFRB. lia.
      + replace (frb + 64) with (frb + (64)) by ring. apply G6. clear; lia.
      + exact KBrow.
      + exact KBwin.
    - (* md <> 0: the callee wrote synth mb b nb into the output block and returned rc mb b *)
      destruct MW as (SB & MW).
      destruct (MDP KB9 M0) as (_ & ML & _ & _).
      pose proof (RcSynthLib.rs_synth_len mb (ly_bb (ly_k fr)) nb ML) as SL.
      assert (MUc : munch (BOXW frb spc) mc m').
      { apply (munch_weaken ([(spc - REAC_BOX_MODEL_BLOCK_K, spc); (frb + 32, frb + 32 + 32)] ++
                             reac_box_model_block_X spc FS) (BOXW frb spc) mc m'); [|exact MW].
        intros x Hx. unfold BOXW in Hx. cbn [app outside] in Hx |- *.
        destruct Hx as (H1 & H2 & H3). split; [exact H1|]. split; [clear -H2; lia | exact H3]. }
      assert (RC : -1 <= rc mb (ly_bb (ly_k fr)) <= 1).
      { clear. unfold rc.
        repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. }
      apply (KB m' gj (rc mb (ly_bb (ly_k fr))) (Z_to_bv 64 0x85828) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7'
               t3' t4' t5' t6').
      + exact (FI_after_box mc m' frb sfr spc j w120 _ _ FIH MUc WMc ACc' SRc' AWc' FPc').
      + apply (LC_after_box mc m' gj ly_zero frb sfr spc j w120 HK LCH MUc WMc MIc STc).
        intros x Hx. apply (rd_of_bytes m' (frb + 32) (synth mb (ly_bb (ly_k fr)) nb) SB).
        rewrite SL. clear -Hx. lia.
      + exact (box_out_addr mc m' frb sfr spc j w120 HK MUc AO).
      + exact RC.
      + intros R1. rewrite (BASE_box KB9). unfold ly_Z.
        rewrite (proj2 (Z.eqb_neq md 0) M0), (proj2 (Z.eqb_eq _ 1) R1). split; [exact SB | exact SL].
      + intros R1. rewrite (BASE_box KB9). unfold ly_Z.
        rewrite (proj2 (Z.eqb_neq md 0) M0), (proj2 (Z.eqb_neq _ 1) R1). reflexivity.
      + clear -RFRB. lia.
      + replace (frb + 64) with (frb + (64)) by ring. apply G6. clear; lia.
      + exact KBrow.
      + exact KBwin.
  Qed.


  (* ===== glue: ly_box (insert below this line) ===== *)
  (* 0x85818: the box call (ly_boxcall, with the callee contract BOX), then at 0x85828 `li a1,1; bne a0,a1,0x85840`:
     r = 1 -> 0x85830 (a2 = 32, a0 = s5 = p + 18, a1 = s7 = frb + 32) and the checked_memcpy of the box result
     (ly_cpy with src = frb + 32); r <> 1 -> BASE = ly_zero and the g copy (ly_args). *)
  Lemma ly_box : EPI_T -> BOXARM_T.
  Proof using AF AG AJ5 AJ6 AMD AOL AP50 AR ARDJ AW0 BOX DB1 DB3 DBN DJ1 DJ2 DJ3g DJ3m F24 F8 FL FP0 FPG FPM GP HAE
    HHM K9 MDP MEMC P0 P50 Rf Rg Rmd Rp SP16 SR0 ST0 TM.
    clear DJ3 FB BLK DB2 MI0 AC0 ATM FPT TLS0 HSM MEMS.
    pose proof Rp as [Rp0 Rp1]; pose proof Rf as [Rf0 Rf1]; pose proof Rmd as [Rmd0 Rmd1]; pose proof Rg as [Rg0 Rg1].
    apply rs_hide in Rp; apply rs_hide in Rf; apply rs_hide in Rmd; apply rs_hide in Rg.
    rs_hide_all.
    intros EPI. unfold BOXARM_T.
    intros b mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hb KB9 FIH LCH AO.
    apply (ly_boxcall BOX b mc gj frb sfr spc j w120 xra x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31);
      [| exact Hb | exact KB9 | exact FIH | exact LCH | exact AO].
    intros mc' gj' r xra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      FI' LC' AO' RR R1 Rn1 RO AE DP DW.
    assert (RC : r = -1 \/ r = 0 \/ r = 1) by (clear -RR; lia).
    destruct RC as [E|[E|E]]; subst r; step; step;
      try (lazymatch goal with |- context [bv_eqb ?u ?v] =>
             let e := eval vm_compute in (bv_eqb u v) in change (bv_eqb u v) with e end);
      cbn [negb]; cbv iota.
    1, 2: (* r <> 1: BASE = ly_zero, so the zeroed output block already holds BASE *)
      rewrite <- (Rn1 ltac:(clear; lia)) in LC'; eapply ly_args; [exact EPI | exact FI' | exact LC'].
    (* r = 1: the output block holds BASE; copy it to p + 18 *)
    destruct (R1 eq_refl) as (SB & SL).
    step. step. step.
    replace (frb + 64) with (frb + 32 + 32) in AE, DP, DW by ring.
    eapply ly_cpy; [exact EPI | exact FI' | exact LC' | exact SB | exact SL | reflexivity | exact RO | exact DP
                   | exact AO' | exact AE | exact DW].
  Qed.

  (* The whole run from the entry: frame setup, dispatch, box arms, copies and epilogue. *)
  Lemma ly_main : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 f) (Z_to_bv 64 md) (Z_to_bv 64 g)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m (seg_rom rsegs)).
  Proof. exact (ly_pro (ly_dispatch ly_epi (ly_box ly_epi))). Qed.


End L.

Theorem ctrl_lay_block_holds : asan_stack_malloc_1_contract -> asan_memset_contract -> asan_memcpy_contract ->
  reac_box_model_block_contract -> ctrl_lay_block_contract.
Proof.
  intros HSM MEMS MEMC BOX. unfold ctrl_lay_block_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p f md g FS fr ob tb mb nb gb -> -> -> ->.
  intros. eapply ly_main; eassumption.
Qed.
