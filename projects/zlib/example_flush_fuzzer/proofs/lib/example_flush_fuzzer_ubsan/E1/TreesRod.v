(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 MemRel RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState TreesTab TreeModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Record trod : Type := TROD {
  tr_length_code : Z; tr_extra_lbits : Z; tr_base_length : Z;
  tr_dist_code : Z; tr_extra_dbits : Z; tr_base_dist : Z;
  tr_static_ltree : Z; tr_static_dtree : Z; tr_bl_order : Z; tr_extra_blbits : Z;
  tr_lo : Z; tr_hi : Z;
  tr_sdesc : Z }.

Section WithR.
Variable R : trod.

Definition A_static_l_desc : Z := tr_sdesc R.
Definition A_static_d_desc : Z := tr_sdesc R + 32.
Definition A_static_bl_desc : Z := tr_sdesc R + 64.

Definition SDA (t : tree_id) : Z := match t with TL => A_static_l_desc | TD => A_static_d_desc | TB => A_static_bl_desc end.
Definition STP (t : tree_id) : Z := match t with TL => tr_static_ltree R | TD => tr_static_dtree R | TB => 0 end.
Definition EXP (t : tree_id) : Z := match t with TL => tr_extra_lbits R | TD => tr_extra_dbits R | TB => tr_extra_blbits R end.

Definition sdesc_w64 (j : Z) : Z :=
  match j with
  | 0 => tr_static_ltree R | 1 => tr_extra_lbits R | 2 => 257 + 286 * 2 ^ 32 | 3 => 15
  | 4 => tr_static_dtree R | 5 => tr_extra_dbits R | 6 => 0 + 30 * 2 ^ 32 | 7 => 15
  | 8 => 0 | 9 => tr_extra_blbits R | 10 => 0 + 19 * 2 ^ 32 | _ => 7
  end.
Definition sdesc_w32 (j : Z) : Z :=
  match j with
  | 0 => tr_static_ltree R mod 2 ^ 32 | 1 => tr_static_ltree R / 2 ^ 32
  | 2 => tr_extra_lbits R mod 2 ^ 32 | 3 => tr_extra_lbits R / 2 ^ 32
  | 4 => 257 | 5 => 286 | 6 => 15
  | 8 => tr_static_dtree R mod 2 ^ 32 | 9 => tr_static_dtree R / 2 ^ 32
  | 10 => tr_extra_dbits R mod 2 ^ 32 | 11 => tr_extra_dbits R / 2 ^ 32
  | 13 => 30 | 14 => 15
  | 18 => tr_extra_blbits R mod 2 ^ 32 | 19 => tr_extra_blbits R / 2 ^ 32
  | 21 => 19 | 22 => 7
  | _ => 0
  end.

Definition trees_rod_clear (mem : word -> option byte) : Prop :=
  rom_clear mem (tr_lo R) (tr_hi R) /\ rom_clear mem (tr_sdesc R) (tr_sdesc R + 96).

Definition trod_ok (segs : list Segment) : Prop :=
  chk_rom segs (tr_length_code R) (tab8_byte (arr_get length_code_a)) 256 = true
  /\ chk_rom segs (tr_dist_code R) (tab8_byte (arr_get dist_code_a)) 512 = true
  /\ chk_rom segs (tr_bl_order R) (tab8_byte (arr_get bl_order_a)) 19 = true
  /\ chk_rom segs (tr_extra_lbits R) (tab32_byte (arr_get extra_lbits_a)) (4 * 29) = true
  /\ chk_rom segs (tr_base_length R) (tab32_byte (arr_get base_length_a)) (4 * 29) = true
  /\ chk_rom segs (tr_extra_dbits R) (tab32_byte (arr_get extra_dbits_a)) (4 * 30) = true
  /\ chk_rom segs (tr_base_dist R) (tab32_byte (arr_get base_dist_a)) (4 * 30) = true
  /\ chk_rom segs (tr_extra_blbits R) (tab32_byte (arr_get extra_blbits_a)) (4 * 19) = true
  /\ chk_rom segs (tr_static_ltree R) (ct_byte (arr_get static_ltree_fc) (arr_get static_ltree_dl)) (4 * 288) = true
  /\ chk_rom segs (tr_static_dtree R) (ct_byte (arr_get static_dtree_fc) (arr_get static_dtree_dl)) (4 * 30) = true
  /\ chk_rom segs (tr_sdesc R) (tab64_byte sdesc_w64) (8 * 12) = true
  /\ chk_rom segs (tr_sdesc R) (tab32_byte sdesc_w32) (4 * 24) = true
  /\ (tr_lo R <= tr_length_code R /\ tr_length_code R + 256 <= tr_hi R)
  /\ (tr_lo R <= tr_dist_code R /\ tr_dist_code R + 512 <= tr_hi R)
  /\ (tr_lo R <= tr_bl_order R /\ tr_bl_order R + 19 <= tr_hi R)
  /\ (tr_lo R <= tr_extra_lbits R /\ tr_extra_lbits R + 116 <= tr_hi R)
  /\ (tr_lo R <= tr_base_length R /\ tr_base_length R + 116 <= tr_hi R)
  /\ (tr_lo R <= tr_extra_dbits R /\ tr_extra_dbits R + 120 <= tr_hi R)
  /\ (tr_lo R <= tr_base_dist R /\ tr_base_dist R + 120 <= tr_hi R)
  /\ (tr_lo R <= tr_extra_blbits R /\ tr_extra_blbits R + 76 <= tr_hi R)
  /\ (tr_lo R <= tr_static_ltree R /\ tr_static_ltree R + 1152 <= tr_hi R)
  /\ (tr_lo R <= tr_static_dtree R /\ tr_static_dtree R + 120 <= tr_hi R)
  /\ (0 <= tr_lo R /\ tr_hi R < 2 ^ 32) /\ (0 <= tr_sdesc R /\ tr_sdesc R + 96 < 2 ^ 32).


Lemma trees_rod_clear_wbytes : forall mem (b : Z) bs,
  trees_rod_clear mem ->
  (forall x : word, b <= bv_unsigned x < b + Z.of_nat (length bs) -> mem x <> None) ->
  0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  trees_rod_clear (wbytes mem (zw b) bs).
Proof.
  intros mem b bs [H1 H2] Hm Hb0 Hb1. split; apply rom_clear_wbytes; assumption.
Qed.

Lemma trees_rod_clear_agree : forall F mem m,
  trees_rod_clear mem -> agree_out F mem m ->
  (forall x : word, in_franges F (bv_unsigned x) -> mem x <> None) ->
  trees_rod_clear m.
Proof.
  intros F mem m [H1 H2] Hag HF. split; eapply rom_clear_agree; eassumption.
Qed.

Lemma trees_rod_clear_wr : forall m M, trees_rod_clear m -> wr_ok m M -> trees_rod_clear M.
Proof. intros m M [H1 H2] HW. split; eapply rom_clear_wr; eassumption. Qed.

Lemma mapped_rod_apart : forall segs m lo n,
  trod_ok segs -> trees_rod_clear m ->
  (forall x : word, lo <= bv_unsigned x < lo + n -> m x <> None) ->
  0 <= lo -> lo + n <= 2 ^ 64 ->
  (lo + n <= tr_lo R \/ tr_hi R <= lo \/ n <= 0)
  /\ (lo + n <= tr_sdesc R \/ tr_sdesc R + 96 <= lo \/ n <= 0).
Proof.
  intros segs m lo n HOK [H1 H2] Hm Hlo Hhi.
  do 12 (apply proj2 in HOK).
  destruct HOK as (_ & _ & _ & L4 & _ & _ & _ & _ & _ & _ & B1 & B2).
  split.
  - destruct (mapped_clear_apart m lo n (tr_lo R) (tr_hi R) H1 Hm Hlo Hhi ltac:(lia) ltac:(lia)); lia.
  - destruct (mapped_clear_apart m lo n (tr_sdesc R) (tr_sdesc R + 96) H2 Hm Hlo Hhi ltac:(lia) ltac:(lia)); lia.
Qed.


Section Reads.
Variable segs : list Segment.
Variable m : word -> option byte.
Hypothesis HOK : trod_ok segs.
Hypothesis HRC : trees_rod_clear m.

Local Tactic Notation "getchk" int_or_var(n) :=
  let H := fresh "CHK" in
  pose proof HOK as H;
  do n (apply proj2 in H); apply proj1 in H.

Local Ltac bounds :=
  let H := fresh "BND" in
  pose proof HOK as H; do 12 (apply proj2 in H).

Local Ltac clear_tab := intros x Hx; apply (proj1 HRC); lia.
Local Ltac clear_sd := intros x Hx; apply (proj2 HRC); lia.

Local Tactic Notation "rd1" integer(n) constr(BND) constr(A) constr(f) constr(N) :=
  intros i a v Hi -> ->; getchk n; bounds;
  eapply (cell_read_at segs m _ 1%nat);
  [ apply (tab_cell1 segs m A f N); [assumption | clear_tab | lia | lia | lia]
  | pose proof (BND i); rewrite Z.mod_small; [reflexivity | change (2 ^ (8 * Z.of_nat 1)) with 256; lia] ].

Lemma length_code_read : forall i a v, 0 <= i < 256 -> a = tr_length_code R + i -> v = arr_get length_code_a i ->
  exists bs, rdn segs m (zw a) 1 = Some bs /\ bytes_le_to_Z bs = v.
Proof. rd1 0 length_code_bound (tr_length_code R) (arr_get length_code_a) 256%nat. Qed.
Lemma dist_code_read : forall i a v, 0 <= i < 512 -> a = tr_dist_code R + i -> v = arr_get dist_code_a i ->
  exists bs, rdn segs m (zw a) 1 = Some bs /\ bytes_le_to_Z bs = v.
Proof. rd1 1 dist_code_bound (tr_dist_code R) (arr_get dist_code_a) 512%nat. Qed.

Lemma length_code_cells : cells segs m (tr_length_code R) 1 1 256 (arr_get length_code_a).
Proof.
  getchk 0. bounds. intros i Hi. replace (tr_length_code R + 1 * i) with (tr_length_code R + i) by lia.
  apply (tab_cell1 segs m _ _ 256%nat); [assumption | clear_tab | lia | lia | lia].
Qed.
Lemma dist_code_cells : cells segs m (tr_dist_code R) 1 1 512 (arr_get dist_code_a).
Proof.
  getchk 1. bounds. intros i Hi. replace (tr_dist_code R + 1 * i) with (tr_dist_code R + i) by lia.
  apply (tab_cell1 segs m _ _ 512%nat); [assumption | clear_tab | lia | lia | lia].
Qed.
Lemma bl_order_cells : cells segs m (tr_bl_order R) 1 1 19 (arr_get bl_order_a).
Proof.
  getchk 2. bounds. intros i Hi. replace (tr_bl_order R + 1 * i) with (tr_bl_order R + i) by lia.
  apply (tab_cell1 segs m _ _ 19%nat); [assumption | clear_tab | lia | lia | lia].
Qed.

Local Tactic Notation "rd4" integer(n) constr(BND) constr(A) constr(f) constr(N) :=
  intros i a v Hi -> ->; getchk n; bounds;
  eapply (cell_read_at segs m _ 4%nat);
  [ apply (tab_cell4 segs m A f N); [assumption | clear_tab | lia | lia | lia]
  | pose proof (BND i); rewrite Z.mod_small; [reflexivity | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia] ].

Lemma extra_lbits_read : forall i a v, 0 <= i < 29 -> a = tr_extra_lbits R + 4 * i -> v = arr_get extra_lbits_a i ->
  exists bs, rdn segs m (zw a) 4 = Some bs /\ bytes_le_to_Z bs = v.
Proof. rd4 3 extra_lbits_bound (tr_extra_lbits R) (arr_get extra_lbits_a) 29%nat. Qed.
Lemma extra_dbits_read : forall i a v, 0 <= i < 30 -> a = tr_extra_dbits R + 4 * i -> v = arr_get extra_dbits_a i ->
  exists bs, rdn segs m (zw a) 4 = Some bs /\ bytes_le_to_Z bs = v.
Proof. rd4 5 extra_dbits_bound (tr_extra_dbits R) (arr_get extra_dbits_a) 30%nat. Qed.
Lemma extra_blbits_read : forall i a v, 0 <= i < 19 -> a = tr_extra_blbits R + 4 * i -> v = arr_get extra_blbits_a i ->
  exists bs, rdn segs m (zw a) 4 = Some bs /\ bytes_le_to_Z bs = v.
Proof. rd4 7 extra_blbits_bound (tr_extra_blbits R) (arr_get extra_blbits_a) 19%nat. Qed.

Lemma extra_lbits_cells : cells segs m (tr_extra_lbits R) 4 4 29 (arr_get extra_lbits_a).
Proof. getchk 3. bounds. intros i Hi. apply (tab_cell4 segs m _ _ 29%nat); [assumption | clear_tab | lia | lia | lia]. Qed.
Lemma base_length_cells : cells segs m (tr_base_length R) 4 4 29 (arr_get base_length_a).
Proof. getchk 4. bounds. intros i Hi. apply (tab_cell4 segs m _ _ 29%nat); [assumption | clear_tab | lia | lia | lia]. Qed.
Lemma extra_dbits_cells : cells segs m (tr_extra_dbits R) 4 4 30 (arr_get extra_dbits_a).
Proof. getchk 5. bounds. intros i Hi. apply (tab_cell4 segs m _ _ 30%nat); [assumption | clear_tab | lia | lia | lia]. Qed.
Lemma base_dist_cells : cells segs m (tr_base_dist R) 4 4 30 (arr_get base_dist_a).
Proof. getchk 6. bounds. intros i Hi. apply (tab_cell4 segs m _ _ 30%nat); [assumption | clear_tab | lia | lia | lia]. Qed.

Lemma static_ltree_cells :
  cells segs m (tr_static_ltree R) 4 2 288 (arr_get static_ltree_fc)
  /\ cells segs m (tr_static_ltree R + 2) 4 2 288 (arr_get static_ltree_dl).
Proof.
  getchk 8. bounds.
  split; intros i Hi.
  - apply (ct_cell_fc segs m _ _ (arr_get static_ltree_dl) 288%nat); [assumption | clear_tab | lia | lia | lia].
  - replace (tr_static_ltree R + 2 + 4 * i) with (tr_static_ltree R + 4 * i + 2) by lia.
    apply (ct_cell_dl segs m _ (arr_get static_ltree_fc) _ 288%nat); [assumption | clear_tab | lia | lia | lia].
Qed.

Lemma static_dtree_cells :
  cells segs m (tr_static_dtree R) 4 2 30 (arr_get static_dtree_fc)
  /\ cells segs m (tr_static_dtree R + 2) 4 2 30 (arr_get static_dtree_dl).
Proof.
  getchk 9. bounds.
  split; intros i Hi.
  - apply (ct_cell_fc segs m _ _ (arr_get static_dtree_dl) 30%nat); [assumption | clear_tab | lia | lia | lia].
  - replace (tr_static_dtree R + 2 + 4 * i) with (tr_static_dtree R + 4 * i + 2) by lia.
    apply (ct_cell_dl segs m _ (arr_get static_dtree_fc) _ 30%nat); [assumption | clear_tab | lia | lia | lia].
Qed.


Lemma sdesc_cell8 : forall i, 0 <= i < 12 -> cell segs m (tr_sdesc R + 8 * i) 8 (sdesc_w64 i).
Proof.
  getchk 10. bounds. intros i Hi.
  apply (tab_cell8 segs m _ sdesc_w64 12%nat); [assumption | clear_sd | lia | lia | lia].
Qed.

Lemma sdesc_cell4 : forall i, 0 <= i < 24 -> cell segs m (tr_sdesc R + 4 * i) 4 (sdesc_w32 i).
Proof.
  getchk 11. bounds. intros i Hi.
  apply (tab_cell4 segs m _ sdesc_w32 24%nat); [assumption | clear_sd | lia | lia | lia].
Qed.

Lemma sdesc_cells : forall t,
  cell segs m (SDA t) 8 (STP t)
  /\ cell segs m (SDA t + 8) 8 (EXP t)
  /\ cell segs m (SDA t + 16) 4 (sd_extra_base t)
  /\ cell segs m (SDA t + 20) 4 (sd_elems t)
  /\ cell segs m (SDA t + 24) 4 (sd_max_length t).
Proof.
  intros t.
  pose proof sdesc_cell8 as C8. pose proof sdesc_cell4 as C4.
  destruct t; cbn [SDA STP EXP sd_extra_base sd_elems sd_max_length];
    unfold A_static_l_desc, A_static_d_desc, A_static_bl_desc, L_CODES, D_CODES, BL_CODES, LITERALS, MAX_BITS, MAX_BL_BITS.
  - pose proof (C8 0 ltac:(lia)) as P0. pose proof (C8 1 ltac:(lia)) as P1.
    pose proof (C4 4 ltac:(lia)) as I4. pose proof (C4 5 ltac:(lia)) as I5. pose proof (C4 6 ltac:(lia)) as I6.
    cbn [sdesc_w64 sdesc_w32] in P0, P1, I4, I5, I6.
    replace (tr_sdesc R + 8 * 0) with (tr_sdesc R) in P0 by lia. replace (tr_sdesc R + 8 * 1) with (tr_sdesc R + 8) in P1 by lia.
    replace (tr_sdesc R + 4 * 4) with (tr_sdesc R + 16) in I4 by lia. replace (tr_sdesc R + 4 * 5) with (tr_sdesc R + 20) in I5 by lia.
    replace (tr_sdesc R + 4 * 6) with (tr_sdesc R + 24) in I6 by lia.
    replace (256 + 1) with 257 by lia.
    repeat split; assumption.
  - pose proof (C8 4 ltac:(lia)) as P0. pose proof (C8 5 ltac:(lia)) as P1.
    pose proof (C4 12 ltac:(lia)) as I4. pose proof (C4 13 ltac:(lia)) as I5. pose proof (C4 14 ltac:(lia)) as I6.
    cbn [sdesc_w64 sdesc_w32] in P0, P1, I4, I5, I6.
    replace (tr_sdesc R + 8 * 4) with (tr_sdesc R + 32) in P0 by lia. replace (tr_sdesc R + 8 * 5) with (tr_sdesc R + 32 + 8) in P1 by lia.
    replace (tr_sdesc R + 4 * 12) with (tr_sdesc R + 32 + 16) in I4 by lia. replace (tr_sdesc R + 4 * 13) with (tr_sdesc R + 32 + 20) in I5 by lia.
    replace (tr_sdesc R + 4 * 14) with (tr_sdesc R + 32 + 24) in I6 by lia.
    repeat split; assumption.
  - pose proof (C8 8 ltac:(lia)) as P0. pose proof (C8 9 ltac:(lia)) as P1.
    pose proof (C4 20 ltac:(lia)) as I4. pose proof (C4 21 ltac:(lia)) as I5. pose proof (C4 22 ltac:(lia)) as I6.
    cbn [sdesc_w64 sdesc_w32] in P0, P1, I4, I5, I6.
    replace (tr_sdesc R + 8 * 8) with (tr_sdesc R + 64) in P0 by lia. replace (tr_sdesc R + 8 * 9) with (tr_sdesc R + 64 + 8) in P1 by lia.
    replace (tr_sdesc R + 4 * 20) with (tr_sdesc R + 64 + 16) in I4 by lia. replace (tr_sdesc R + 4 * 21) with (tr_sdesc R + 64 + 20) in I5 by lia.
    replace (tr_sdesc R + 4 * 22) with (tr_sdesc R + 64 + 24) in I6 by lia.
    repeat split; assumption.
Qed.


End Reads.
End WithR.
End FXG.
