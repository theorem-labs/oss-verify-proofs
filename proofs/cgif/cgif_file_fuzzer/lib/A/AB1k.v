(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1a YK1e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0c YK0e YK0f YK09 YA0c YA0e YA0f.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Definition tfibst_text_start : Z := 0x64f7c.
Definition tfibst_text_count : nat := 62.
Definition tfibst_tbl : ctable := Eval vm_compute in (build_table tfibsegs tfibst_text_start tfibst_text_count TEmpty).
Lemma tfibst_tbl_eq : tfibst_tbl = build_table tfibsegs tfibst_text_start tfibst_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl tfibst_tbl). Qed.
Lemma tfibst_tbl_ok : table_ok tfibsegs tfibst_tbl.
Proof. rewrite tfibst_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Section d. Context {fx : YK11.FPState}.
Lemma fetch_lit : forall (p : word) (w : bv 32),
clookup tfibst_tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word tfibsegs p = Some w.
Proof.
intros p w H.
rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply tfibst_tbl_ok. exact H.
Qed.
End d.
Ltac ftac := apply fetch_lit; vm_compute; reflexivity.
Section f. Context {fx : YK11.FPState}.
Lemma F_000 : fetch_word tfibsegs (Z_to_bv 64 0x64fb0) = Some (0x00155593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_000 : decode_any (0x00155593%bv : bv 32) = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_004 : fetch_word tfibsegs (Z_to_bv 64 0x64fb4) = Some (0x55555637%bv : bv 32).
Proof. ftac. Qed.
Lemma D_004 : decode_any (0x55555637%bv : bv 32) = Some (Lui 12 349525, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_008 : fetch_word tfibsegs (Z_to_bv 64 0x64fb8) = Some (0x333336b7%bv : bv 32).
Proof. ftac. Qed.
Lemma D_008 : decode_any (0x333336b7%bv : bv 32) = Some (Lui 13 209715, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_00c : fetch_word tfibsegs (Z_to_bv 64 0x64fbc) = Some (0x0f0f1737%bv : bv 32).
Proof. ftac. Qed.
Lemma D_00c : decode_any (0x0f0f1737%bv : bv 32) = Some (Lui 14 61681, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_010 : fetch_word tfibsegs (Z_to_bv 64 0x64fc0) = Some (0x010107b7%bv : bv 32).
Proof. ftac. Qed.
Lemma D_010 : decode_any (0x010107b7%bv : bv 32) = Some (Lui 15 4112, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_014 : fetch_word tfibsegs (Z_to_bv 64 0x64fc4) = Some (0x00b56533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_014 : decode_any (0x00b56533%bv : bv 32) = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_018 : fetch_word tfibsegs (Z_to_bv 64 0x64fc8) = Some (0x5556059b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_018 : decode_any (0x5556059b%bv : bv 32) = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_01c : fetch_word tfibsegs (Z_to_bv 64 0x64fcc) = Some (0x3336861b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_01c : decode_any (0x3336861b%bv : bv 32) = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_020 : fetch_word tfibsegs (Z_to_bv 64 0x64fd0) = Some (0xf0f7069b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_020 : decode_any (0xf0f7069b%bv : bv 32) = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_024 : fetch_word tfibsegs (Z_to_bv 64 0x64fd4) = Some (0x1017871b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_024 : decode_any (0x1017871b%bv : bv 32) = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_028 : fetch_word tfibsegs (Z_to_bv 64 0x64fd8) = Some (0x00255793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_028 : decode_any (0x00255793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_02c : fetch_word tfibsegs (Z_to_bv 64 0x64fdc) = Some (0x00f56533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_02c : decode_any (0x00f56533%bv : bv 32) = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_030 : fetch_word tfibsegs (Z_to_bv 64 0x64fe0) = Some (0x02059793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_030 : decode_any (0x02059793%bv : bv 32) = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_034 : fetch_word tfibsegs (Z_to_bv 64 0x64fe4) = Some (0x00f585b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_034 : decode_any (0x00f585b3%bv : bv 32) = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_038 : fetch_word tfibsegs (Z_to_bv 64 0x64fe8) = Some (0x02061793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_038 : decode_any (0x02061793%bv : bv 32) = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_03c : fetch_word tfibsegs (Z_to_bv 64 0x64fec) = Some (0x00f60633%bv : bv 32).
Proof. ftac. Qed.
Lemma D_03c : decode_any (0x00f60633%bv : bv 32) = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_040 : fetch_word tfibsegs (Z_to_bv 64 0x64ff0) = Some (0x02069793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_040 : decode_any (0x02069793%bv : bv 32) = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_044 : fetch_word tfibsegs (Z_to_bv 64 0x64ff4) = Some (0x00f686b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_044 : decode_any (0x00f686b3%bv : bv 32) = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_048 : fetch_word tfibsegs (Z_to_bv 64 0x64ff8) = Some (0x02071793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_048 : decode_any (0x02071793%bv : bv 32) = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_04c : fetch_word tfibsegs (Z_to_bv 64 0x64ffc) = Some (0x00f70733%bv : bv 32).
Proof. ftac. Qed.
Lemma D_04c : decode_any (0x00f70733%bv : bv 32) = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_050 : fetch_word tfibsegs (Z_to_bv 64 0x65000) = Some (0x00455793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_050 : decode_any (0x00455793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_054 : fetch_word tfibsegs (Z_to_bv 64 0x65004) = Some (0x00f56533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_054 : decode_any (0x00f56533%bv : bv 32) = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_058 : fetch_word tfibsegs (Z_to_bv 64 0x65008) = Some (0x00855793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_058 : decode_any (0x00855793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_05c : fetch_word tfibsegs (Z_to_bv 64 0x6500c) = Some (0x00f56533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_05c : decode_any (0x00f56533%bv : bv 32) = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_060 : fetch_word tfibsegs (Z_to_bv 64 0x65010) = Some (0x01055793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_060 : decode_any (0x01055793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_064 : fetch_word tfibsegs (Z_to_bv 64 0x65014) = Some (0x00f56533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_064 : decode_any (0x00f56533%bv : bv 32) = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_068 : fetch_word tfibsegs (Z_to_bv 64 0x65018) = Some (0x02055793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_068 : decode_any (0x02055793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_06c : fetch_word tfibsegs (Z_to_bv 64 0x6501c) = Some (0x00f56533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_06c : decode_any (0x00f56533%bv : bv 32) = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_070 : fetch_word tfibsegs (Z_to_bv 64 0x65020) = Some (0xfff54513%bv : bv 32).
Proof. ftac. Qed.
Lemma D_070 : decode_any (0xfff54513%bv : bv 32) = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_074 : fetch_word tfibsegs (Z_to_bv 64 0x65024) = Some (0x00155793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_074 : decode_any (0x00155793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_078 : fetch_word tfibsegs (Z_to_bv 64 0x65028) = Some (0x00b7f5b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_078 : decode_any (0x00b7f5b3%bv : bv 32) = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_07c : fetch_word tfibsegs (Z_to_bv 64 0x6502c) = Some (0x40b50533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_07c : decode_any (0x40b50533%bv : bv 32) = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_080 : fetch_word tfibsegs (Z_to_bv 64 0x65030) = Some (0x00c575b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_080 : decode_any (0x00c575b3%bv : bv 32) = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_084 : fetch_word tfibsegs (Z_to_bv 64 0x65034) = Some (0x00255513%bv : bv 32).
Proof. ftac. Qed.
Lemma D_084 : decode_any (0x00255513%bv : bv 32) = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_088 : fetch_word tfibsegs (Z_to_bv 64 0x65038) = Some (0x00c57533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_088 : decode_any (0x00c57533%bv : bv 32) = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_08c : fetch_word tfibsegs (Z_to_bv 64 0x6503c) = Some (0x00a58533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_08c : decode_any (0x00a58533%bv : bv 32) = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_090 : fetch_word tfibsegs (Z_to_bv 64 0x65040) = Some (0x00455593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_090 : decode_any (0x00455593%bv : bv 32) = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_094 : fetch_word tfibsegs (Z_to_bv 64 0x65044) = Some (0x00b50533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_094 : decode_any (0x00b50533%bv : bv 32) = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_098 : fetch_word tfibsegs (Z_to_bv 64 0x65048) = Some (0x00d57533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_098 : decode_any (0x00d57533%bv : bv 32) = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_09c : fetch_word tfibsegs (Z_to_bv 64 0x6504c) = Some (0x02e50533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_09c : decode_any (0x02e50533%bv : bv 32) = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0a0 : fetch_word tfibsegs (Z_to_bv 64 0x65050) = Some (0x03855513%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0a0 : decode_any (0x03855513%bv : bv 32) = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0a4 : fetch_word tfibsegs (Z_to_bv 64 0x65054) = Some (0x40a0053b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0a4 : decode_any (0x40a0053b%bv : bv 32) = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0a8 : fetch_word tfibsegs (Z_to_bv 64 0x65058) = Some (0xfff00593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0a8 : decode_any (0xfff00593%bv : bv 32) = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0ac : fetch_word tfibsegs (Z_to_bv 64 0x6505c) = Some (0x00a59533%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0ac : decode_any (0x00a59533%bv : bv 32) = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0b0 : fetch_word tfibsegs (Z_to_bv 64 0x65060) = Some (0xfff54513%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0b0 : decode_any (0xfff54513%bv : bv 32) = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Definition sm (s k : Z) : Z := Z.lor s (Z.shiftr s k).
Definition Qb (m s : Z) : Prop := 0 <= s < 2 ^ 47 /\ forall i, m <= i <= 46 -> Z.testbit s i = true.
Lemma shiftr_range47 : forall s k, 0 <= s < 2 ^ 47 -> 0 <= k -> 0 <= Z.shiftr s k < 2 ^ 47.
Proof.
intros s k Hs Hk. rewrite Z.shiftr_div_pow2 by lia.
assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Lemma lor_range47 : forall a b, 0 <= a < 2 ^ 47 -> 0 <= b < 2 ^ 47 -> 0 <= Z.lor a b < 2 ^ 47.
Proof.
intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
intros k Hk. rewrite Z.lor_spec.
rewrite (Z_testbit_high 47 a k) by lia. rewrite (Z_testbit_high 47 b k) by lia. reflexivity.
Qed.
Lemma Qb_start : forall x, 2 ^ 46 <= x < 2 ^ 47 -> Qb 46 x.
Proof.
intros x Hx. split; [lia|]. intros i Hi. replace i with 46 by lia.
apply Z.testbit_true; [lia|].
replace (x / 2 ^ 46) with 1; [reflexivity|].
apply (Z.div_unique x (2 ^ 46) 1 (x - 2 ^ 46)); lia.
Qed.
Lemma Qb_step : forall m k s, Qb m s -> 0 <= m -> 0 < k -> k <= 47 - m -> Qb (Z.max 0 (m - k)) (sm s k).
Proof.
intros m k s [Hs Hb] Hm Hk Hkm. unfold sm.
pose proof (shiftr_range47 s k Hs ltac:(lia)) as Hr.
split; [apply lor_range47; lia|].
intros i Hi. rewrite Z.lor_spec.
destruct (Z_le_gt_dec m i) as [Hle|Hgt].
- rewrite (Hb i) by lia. reflexivity.
- rewrite Z.shiftr_spec by lia. rewrite (Hb (i + k)) by lia. apply Bool.orb_true_r.
Qed.
Lemma Qb_full : forall s, Qb 0 s -> s = 2 ^ 47 - 1.
Proof.
intros s [Hs Hb]. apply Z.bits_inj'. intros n Hn.
destruct (Z_lt_le_dec n 47) as [Hlt|Hge].
- rewrite (Hb n) by lia. symmetry. change (2 ^ 47 - 1) with (Z.pred (2 ^ 47)). rewrite <- Z.ones_equiv.
rewrite Z.testbit_ones_nonneg by lia. apply Z.ltb_lt. lia.
- rewrite (Z_testbit_high 47 s n) by lia. rewrite (Z_testbit_high 47 (2 ^ 47 - 1) n) by lia. reflexivity.
Qed.
Definition s1 (x : Z) : Z := sm x 1.
Definition s2 (x : Z) : Z := sm (s1 x) 2.
Definition s4 (x : Z) : Z := sm (s2 x) 4.
Definition s8 (x : Z) : Z := sm (s4 x) 8.
Definition s16 (x : Z) : Z := sm (s8 x) 16.
Definition s32 (x : Z) : Z := sm (s16 x) 32.
Lemma smear_facts : forall x, 2 ^ 46 <= x < 2 ^ 47 ->
Qb 45 (s1 x) /\ Qb 43 (s2 x) /\ Qb 39 (s4 x) /\ Qb 31 (s8 x) /\ Qb 15 (s16 x) /\ s32 x = 2 ^ 47 - 1.
Proof.
intros x Hx.
pose proof (Qb_start x Hx) as Q0.
pose proof (Qb_step 46 1 x Q0 ltac:(lia) ltac:(lia) ltac:(lia)) as Q1. change (Z.max 0 (46 - 1)) with 45 in Q1.
pose proof (Qb_step 45 2 _ Q1 ltac:(lia) ltac:(lia) ltac:(lia)) as Q2. change (Z.max 0 (45 - 2)) with 43 in Q2.
pose proof (Qb_step 43 4 _ Q2 ltac:(lia) ltac:(lia) ltac:(lia)) as Q4. change (Z.max 0 (43 - 4)) with 39 in Q4.
pose proof (Qb_step 39 8 _ Q4 ltac:(lia) ltac:(lia) ltac:(lia)) as Q8. change (Z.max 0 (39 - 8)) with 31 in Q8.
pose proof (Qb_step 31 16 _ Q8 ltac:(lia) ltac:(lia) ltac:(lia)) as Q16. change (Z.max 0 (31 - 16)) with 15 in Q16.
pose proof (Qb_step 15 32 _ Q16 ltac:(lia) ltac:(lia) ltac:(lia)) as Q32. change (Z.max 0 (15 - 32)) with 0 in Q32.
exact (conj Q1 (conj Q2 (conj Q4 (conj Q8 (conj Q16 (Qb_full _ Q32)))))).
Qed.
Lemma u64_of_Z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.
Lemma Vsrli : forall s k, 0 <= s < 2 ^ 64 -> v_srli (Z_to_bv 64 s) k = Z_to_bv 64 (Z.shiftr s k).
Proof. intros s k Hs. unfold v_srli. rewrite u64_of_Z by lia. reflexivity. Qed.
Lemma Vor : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_or (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof. intros a b Ha Hb. unfold v_or. rewrite !u64_of_Z by lia. reflexivity. Qed.
Ltac red_if :=
repeat match goal with
| |- context [if bv_eqb ?a ?b then ?x else ?y] =>
let v := eval vm_compute in (bv_eqb a b) in
lazymatch v with
| true => change (if bv_eqb a b then x else y) with x
| false => change (if bv_eqb a b then x else y) with y
end
end.
Ltac gr := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac | rewrite getr_zero ].
Ltac pcn :=
rewrite YK1e.v_addi_lit;
lazymatch goal with
| |- msteps _ (mkst _ (Z_to_bv 64 (?a + ?b)) _ _) _ =>
let c := eval vm_compute in (a + b)%Z in change (Z_to_bv 64 (a + b)%Z) with (Z_to_bv 64 c)
end.
Ltac nv :=
lazymatch goal with
| |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ =>
lazymatch v with
| Z_to_bv 64 _ => idtac
| _ => let u := eval vm_compute in (bv_unsigned v) in
replace v with (Z_to_bv 64 u) by (apply bv_eq; vm_compute; reflexivity)
end
end.
Ltac ist L F D :=
eapply mst_step; [reflexivity | eapply L; [exact F | reflexivity | exact D] |]; red_if; pcn; gr.
Definition kept6 (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r.
Lemma seg1 : forall regs mem rom x,
getr regs 10 = Z_to_bv 64 x -> 2 ^ 46 <= x < 2 ^ 47 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 0x64fb0) mem rom) (mkst regs' (Z_to_bv 64 0x64ff0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (s2 x)
/\ getr regs' 11 = Z_to_bv 64 0x5555555555555555
/\ getr regs' 12 = Z_to_bv 64 0x3333333333333333
/\ getr regs' 13 = Z_to_bv 64 0xf0f0f0f
/\ getr regs' 14 = Z_to_bv 64 0x1010101
/\ kept6 regs regs'.
Proof.
intros regs mem rom x H10 Hx.
destruct (smear_facts x Hx) as (Q1 & Q2 & _).
destruct Q1 as [R1 _]. destruct Q2 as [R2 _].
pose proof (shiftr_range47 x 1 ltac:(lia) ltac:(lia)) as Hh1.
pose proof (shiftr_range47 (s1 x) 2 R1 ltac:(lia)) as Hh2.
eexists. split.
- ist (YK11.step_srli tfibsegs) F_000 D_000.
rewrite H10. change (bv_unsigned (1%bv : bv 6)) with 1%Z. rewrite Vsrli by lia.
ist (step_lui tfibsegs) F_004 D_004. nv.
ist (step_lui tfibsegs) F_008 D_008. nv.
ist (step_lui tfibsegs) F_00c D_00c. nv.
ist (step_lui tfibsegs) F_010 D_010. nv.
ist (step_or tfibsegs) F_014 D_014.
rewrite H10. rewrite Vor by lia. change (Z.lor x (Z.shiftr x 1)) with (s1 x).
ist (step_addiw tfibsegs) F_018 D_018. nv.
ist (step_addiw tfibsegs) F_01c D_01c. nv.
ist (step_addiw tfibsegs) F_020 D_020. nv.
ist (step_addiw tfibsegs) F_024 D_024. nv.
ist (YK11.step_srli tfibsegs) F_028 D_028.
change (bv_unsigned (2%bv : bv 6)) with 2%Z. rewrite Vsrli by lia.
ist (step_or tfibsegs) F_02c D_02c.
rewrite Vor by lia. change (Z.lor (s1 x) (Z.shiftr (s1 x) 2)) with (s2 x).
ist (step_slli tfibsegs) F_030 D_030. nv.
ist (step_add tfibsegs) F_034 D_034. nv.
ist (step_slli tfibsegs) F_038 D_038. nv.
ist (step_add tfibsegs) F_03c D_03c. nv.
apply mst_refl.
- gr. repeat (split; [reflexivity|]).
intros r ? ? ? ? ? ?. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma seg2 : forall regs mem rom x,
getr regs 10 = Z_to_bv 64 (s2 x) -> 2 ^ 46 <= x < 2 ^ 47 ->
getr regs 11 = Z_to_bv 64 0x5555555555555555 ->
getr regs 12 = Z_to_bv 64 0x3333333333333333 ->
getr regs 13 = Z_to_bv 64 0xf0f0f0f ->
getr regs 14 = Z_to_bv 64 0x1010101 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 0x64ff0) mem rom) (mkst regs' (Z_to_bv 64 0x6502c) mem rom)
/\ getr regs' 10 = Z_to_bv 64 0xffff800000000000
/\ getr regs' 11 = Z_to_bv 64 0x5555400000000000
/\ getr regs' 12 = Z_to_bv 64 0x3333333333333333
/\ getr regs' 13 = Z_to_bv 64 0xf0f0f0f0f0f0f0f
/\ getr regs' 14 = Z_to_bv 64 0x101010101010101
/\ kept6 regs regs'.
Proof.
intros regs mem rom x H10 Hx H11 H12 H13 H14.
destruct (smear_facts x Hx) as (_ & [R2 _] & [R4 _] & [R8 _] & [R16 _] & E32).
pose proof (shiftr_range47 (s2 x) 4 R2 ltac:(lia)) as Hh4.
pose proof (shiftr_range47 (s4 x) 8 R4 ltac:(lia)) as Hh8.
pose proof (shiftr_range47 (s8 x) 16 R8 ltac:(lia)) as Hh16.
pose proof (shiftr_range47 (s16 x) 32 R16 ltac:(lia)) as Hh32.
eexists. split.
- ist (step_slli tfibsegs) F_040 D_040. rewrite H13. nv.
ist (step_add tfibsegs) F_044 D_044. rewrite H13. nv.
ist (step_slli tfibsegs) F_048 D_048. rewrite H14. nv.
ist (step_add tfibsegs) F_04c D_04c. rewrite H14. nv.
ist (YK11.step_srli tfibsegs) F_050 D_050.
rewrite H10. change (bv_unsigned (4%bv : bv 6)) with 4%Z. rewrite Vsrli by lia.
ist (step_or tfibsegs) F_054 D_054.
rewrite H10. rewrite Vor by lia. change (Z.lor (s2 x) (Z.shiftr (s2 x) 4)) with (s4 x).
ist (YK11.step_srli tfibsegs) F_058 D_058.
change (bv_unsigned (8%bv : bv 6)) with 8%Z. rewrite Vsrli by lia.
ist (step_or tfibsegs) F_05c D_05c.
rewrite Vor by lia. change (Z.lor (s4 x) (Z.shiftr (s4 x) 8)) with (s8 x).
ist (YK11.step_srli tfibsegs) F_060 D_060.
change (bv_unsigned (16%bv : bv 6)) with 16%Z. rewrite Vsrli by lia.
ist (step_or tfibsegs) F_064 D_064.
rewrite Vor by lia. change (Z.lor (s8 x) (Z.shiftr (s8 x) 16)) with (s16 x).
ist (YK11.step_srli tfibsegs) F_068 D_068.
change (bv_unsigned (32%bv : bv 6)) with 32%Z. rewrite Vsrli by lia.
ist (step_or tfibsegs) F_06c D_06c.
rewrite Vor by lia. change (Z.lor (s16 x) (Z.shiftr (s16 x) 32)) with (s32 x). rewrite E32.
ist (step_xori tfibsegs) F_070 D_070. nv.
ist (YK11.step_srli tfibsegs) F_074 D_074. nv.
ist (step_and tfibsegs) F_078 D_078. rewrite H11. nv.
apply mst_refl.
- gr. rewrite H12. repeat (split; [reflexivity|]).
intros r ? ? ? ? ? ?. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma seg3 : forall regs mem rom,
getr regs 10 = Z_to_bv 64 0xffff800000000000 ->
getr regs 11 = Z_to_bv 64 0x5555400000000000 ->
getr regs 12 = Z_to_bv 64 0x3333333333333333 ->
getr regs 13 = Z_to_bv 64 0xf0f0f0f0f0f0f0f ->
getr regs 14 = Z_to_bv 64 0x101010101010101 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 0x6502c) mem rom) (mkst regs' (Z_to_bv 64 0x65064) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
/\ kept6 regs regs'.
Proof.
intros regs mem rom H10 H11 H12 H13 H14.
eexists. split.
- ist (step_sub tfibsegs) F_07c D_07c. rewrite H10, H11. nv.
ist (step_and tfibsegs) F_080 D_080. rewrite H12. nv.
ist (YK11.step_srli tfibsegs) F_084 D_084. nv.
ist (step_and tfibsegs) F_088 D_088. rewrite H12. nv.
ist (step_add tfibsegs) F_08c D_08c. nv.
ist (YK11.step_srli tfibsegs) F_090 D_090. nv.
ist (step_add tfibsegs) F_094 D_094. nv.
ist (step_and tfibsegs) F_098 D_098. rewrite H13. nv.
ist (step_mul tfibsegs) F_09c D_09c. rewrite H14. nv.
ist (YK11.step_srli tfibsegs) F_0a0 D_0a0. nv.
ist (step_subw tfibsegs) F_0a4 D_0a4. nv.
ist (step_addi tfibsegs) F_0a8 D_0a8. nv.
ist (step_sll tfibsegs) F_0ac D_0ac. nv.
ist (step_xori tfibsegs) F_0b0 D_0b0. nv.
change (Z_to_bv 64 140737488355327) with (Z_to_bv 64 (2 ^ 47 - 1)).
apply mst_refl.
- gr. split; [reflexivity|].
intros r ? ? ? ? ? ?. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma kept6_trans : forall a b c, kept6 a b -> kept6 b c -> kept6 a c.
Proof. intros a b c H1 H2 r ? ? ? ? ? ?. rewrite (H2 r), (H1 r) by assumption. reflexivity. Qed.
Theorem sealedtop_run : forall regs mem rom,
2 ^ 46 <= bv_unsigned (getr regs 10) < 2 ^ 47 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 0x64fb0) mem rom) (mkst regs' (Z_to_bv 64 0x65064) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
/\ kept6 regs regs'.
Proof.
intros regs mem rom Hx.
set (x := bv_unsigned (getr regs 10)) in *.
assert (H10 : getr regs 10 = Z_to_bv 64 x) by (subst x; symmetry; apply Z_to_bv_bv_unsigned).
destruct (seg1 regs mem rom x H10 Hx) as (r1 & M1 & A0 & A1 & A2 & A3 & A4 & K1).
destruct (seg2 r1 mem rom x A0 Hx A1 A2 A3 A4) as (r2 & M2 & B0 & B1 & B2 & B3 & B4 & K2).
destruct (seg3 r2 mem rom B0 B1 B2 B3 B4) as (r3 & M3 & C0 & K3).
exists r3. split; [|split; [exact C0|]].
- eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. exact M3.
- eapply kept6_trans; [|exact K3]. eapply kept6_trans; [exact K1|exact K2].
Qed.
End f.
Import AX2. Import AX2S. Import APC. Import APG. Import APSG. Import APSXG.
Definition SEALEDTOP_PC : Z := 0x64fb0.
Definition SEALEDTOP_END : Z := 0x65064.
Definition SEALEDTOP_VAL : Z := 2 ^ 47 - 1.
Definition xn_sealedtop (nx0 : nat) (args : list expr) (cs : acs) : option acs :=
if negb (Z.eqb (pc cs) SEALEDTOP_PC) then None else
let e := reg cs 10 in
match xlo (kn cs) e, xhi (kn cs) e with
| Some lo, Some hi =>
if (Z.leb (2 ^ 46) lo && Z.ltb hi (2 ^ 47))%bool
then after_call nx0 cs SEALEDTOP_END (Some (ELit SEALEDTOP_VAL)) (kn cs)
else None
| _, _ => None
end.
#[local] Instance asanreflect_fx : YK11.FPState := YK11.fx0.
Section g.
Variable A : atable.
Variable nx0 : nat.
Variables LIMIT TOP : Z.
Hypothesis SEGS_wx : YK04.wx_segs_nowrap tfibsegs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment tfibsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Hypothesis TOP_ok' : top_ok TOP.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> TOP <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.
Theorem xn_sealedtop_sound : forall args,
node1_stmt tfibsegs A nx0 LIMIT TOP SINV argH FS0 always (xn_sealedtop nx0 args).
Proof.
intros args cs cs' E R FULL model T HC _ Hn Hk.
unfold xn_sealedtop in Hn.
destruct (Z.eqb (pc cs) SEALEDTOP_PC) eqn:Hpc; [|discriminate Hn]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (xlo (kn cs) (reg cs 10)) as [lo|] eqn:Hlo; [|discriminate Hn].
destruct (xhi (kn cs) (reg cs 10)) as [hi|] eqn:Hhi; [|discriminate Hn].
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate Hn] end.
apply andb_prop in Hcond as [Hl Hh]. apply Z.leb_le in Hl. apply Z.ltb_lt in Hh.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
set (M := Mr A TOP argH E cs model FULL) in *.
pose proof (xlo_sound tfibsegs E M (kn cs) _ _ HKN Hlo) as Xlo.
pose proof (xhi_sound tfibsegs E M (kn cs) _ _ HKN Hhi) as Xhi.
pose proof (w_reg_sound tfibsegs A LIMIT TOP SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : bv 5)) by (apply bv_eq; reflexivity). rewrite E10 in R10.
assert (Hx : 2 ^ 46 <= bv_unsigned (getr R 10) < 2 ^ 47) by (rewrite R10; lia).
destruct (sealedtop_run R M (seg_rom tfibsegs) Hx) as (regs' & Hms & Ha0 & Hkept).
eapply (call_node_sound tfibsegs A nx0 LIMIT TOP SEGS_wx SEGS_in_hull HULL_ok TOP_ok' SINV argH argH_high argH_agree
SINV_frame SINV_agree FS0 cs cs' E R FULL model T SEALEDTOP_END (Some (ELit SEALEDTOP_VAL)) (kn cs) regs' M HC Hn).
- rewrite Hpc. exact Hms.
- intros r Hr0 Hcs. apply Hkept; intros ->; apply Hcs; cbn; tauto.
- exact Ha0.
- exact HKN.
- exact Hk.
Qed.
End g.
