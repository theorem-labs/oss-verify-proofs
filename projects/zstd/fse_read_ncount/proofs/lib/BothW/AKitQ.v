(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma le4_two_bytes : forall b0 b1 : Z, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
le4 (Z_to_bv 64 (b0 + 256 * b1)) = [Z_to_bv 8 b0; Z_to_bv 8 b1; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
intros b0 b1 H0 H1. unfold le4. Local Ltac2 Set LiaHints.tbl := fun () => "0040=12526687165.541891549101.563368316589.565502415661.500000700800900:S2H02H1SSS".
rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
rewrite !Z.shiftr_shiftr by lia. change (8+8) with 16. change (16+8) with 24. rewrite !Z.shiftr_div_pow2 by lia.
change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
f_equal; [apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia|].
f_equal. apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rw_C1x4_to_C4 : forall m A (b0 b1 : Z), 0 <= b0 < 256 -> 0 <= b1 < 256 ->
rw_cells bsegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
rw_cells bsegs m A [C4 (Z_to_bv 64 (b0 + 256 * b1))].
Proof.
intros m A b0 b1 H0 H1 H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
#[using="Type"] Lemma rw_C4_to_C1x4 : forall m A (b0 b1 : Z), 0 <= b0 < 256 -> 0 <= b1 < 256 ->
rw_cells bsegs m A [C4 (Z_to_bv 64 (b0 + 256 * b1))] ->
rw_cells bsegs m A [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros m A b0 b1 H0 H1 H. eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
#[using="Type"] Lemma rw_hdr_to_C4 : forall m A (b0 b1 : Z) cs, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
rw_cells bsegs m A (C1 (Z_to_bv 8 b0) :: C1 (Z_to_bv 8 b1) :: C2 (Z_to_bv 64 0) :: cs) ->
rw_cells bsegs m A (C4 (Z_to_bv 64 (b0 + 256 * b1)) :: cs).
Proof.
intros m A b0 b1 cs H0 H1 H. pose proof H as [[Hwf _] _]. cbn in Hwf.
eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
#[using="Type"] Lemma rw_C4_to_hdr : forall m A (b0 b1 : Z) cs, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
rw_cells bsegs m A (C4 (Z_to_bv 64 (b0 + 256 * b1)) :: cs) ->
rw_cells bsegs m A (C1 (Z_to_bv 8 b0) :: C1 (Z_to_bv 8 b1) :: C2 (Z_to_bv 64 0) :: cs).
Proof.
intros m A b0 b1 cs H0 H1 H. pose proof H as [[Hwf _] _]. cbn in Hwf.
eapply rw_cells_recast; [exact H| cbn; tauto| | reflexivity].
cbn [cells_bytes cbytes app]. rewrite le4_two_bytes by lia. reflexivity.
Qed.
#[using="Type"] Lemma stk_cb : forall m lo hi, stk bsegs m lo hi -> lo <= hi ->
exists bs, rw_cells bsegs m lo [CB (Z.to_nat (hi - lo)) bs].
Proof.
intros m lo hi ST Hle. Local Ltac2 Set LiaHints.tbl := fun () => "0030=23726385554.860199235148.68787689837.8 00000100600;SS3HleS3Hle".
destruct (stk_carve bsegs m lo hi (Z.to_nat (hi - lo)) ST ltac:(lia)) as [_ [bs H]].
exists bs. rewrite Z2Nat.id in H by lia. replace (hi - (hi - lo)) with lo in H by lia. exact H.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stk_of_cb : forall m lo n bs, rw_cells bsegs m lo [CB (Z.to_nat n) bs] -> 0 <= n -> stk bsegs m lo (lo + n).
Proof.
intros m lo n bs H Hn. pose proof (stk_of_rw_cells bsegs m lo _ H) as S. cbn [cells_size csize] in S.
Local Ltac2 Set LiaHints.tbl := fun () => "0010<2431592901.8000004S2Hn".
rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stk_merge3 : forall m a b c d, stk bsegs m a b -> stk bsegs m b c -> stk bsegs m c d -> a <= b <= c -> c <= d -> stk bsegs m a d.
Proof. intros. eapply stk_merge; [| eapply stk_merge; [| | ]|]; eauto; lia. Qed.
#[using="Type"] Lemma cb_zero_le8 : forall m A n j,
rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
0 <= j -> 8 * j + 8 <= n ->
bytes_at bsegs m (A + 8 * j) (le8 (Z_to_bv 64 0)).
Proof.
intros m A n j [[_ HB] _] Hj Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
destruct HB as (H0 & H1 & HB). rewrite repeat_length in H1, HB.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>10093995185.1238874946637.1239175361847.1242757428529.1062844515555.1000000400A00N00X00eS2HiS2H12Hj2Hn2HiS2H12Hj2Hn2HiS2H12Hj2HnS2H02H12Hj2Hn".
split; [lia|]. split; [rewrite length_le8; lia|].
intros i Hi. rewrite length_le8 in Hi.
replace (A + 8 * j + Z.of_nat i) with (A + Z.of_nat (Z.to_nat (8 * j) + i)) by lia.
rewrite HB by lia. rewrite nth_error_repeat' by lia.
replace (le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8) by reflexivity.
rewrite nth_error_repeat' by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma u64arr_snoc : forall m A ws (w : word),
u64arr bsegs m A ws -> rw_cells bsegs m (A + 8 * Z.of_nat (length ws)) [C8 w] ->
u64arr bsegs m A (ws ++ [w]).
Proof.
intros m A ws w [HB HW] [[_ HB2] HW2]. cbn [cells_bytes cbytes app cells_size csize Nat.add] in HB2, HW2.
rewrite app_nil_r in HB2. split.
- rewrite u64s_app. cbn [u64s app]. rewrite app_nil_r. apply bytes_at_app. split; [exact HB|].
rewrite u64s_length. Local Ltac2 Set LiaHints.tbl := fun () => "0060>19079768206.1520619448828.1224933907259.1240069627426.1553122453302.1567506511655.9 00000900=00D00M00T00US2H32Hi1lS2H3S2H02H3S2H32Hi1lS2H32HiS".
replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia. exact HB2.
- rewrite length_app. cbn [length]. destruct HW as (H0 & H1 & HW). destruct HW2 as (_ & H3 & HW2).
split; [lia|]. split; [lia|]. intros i Hi.
destruct (Z_lt_le_dec i (8 * Z.of_nat (length ws))); [apply HW; lia|].
replace (A + i) with (A + 8 * Z.of_nat (length ws) + (i - 8 * Z.of_nat (length ws))) by lia. apply HW2. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma junk_stk : forall m A len, (exists bs, rw_cells bsegs m A [CB (Z.to_nat len) bs]) -> 0 <= len -> stk bsegs m A (A + len).
Proof. intros m A len [bs H] Hl. eapply stk_of_cb; eauto. Qed.
#[using="Type"] Lemma u64arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u64arr bsegs m A [].
Proof.
intros m A H0 H1. split.
- Local Ltac2 Set LiaHints.tbl := fun () => "0050=20621550845.524931798586.540669651966.541283725690.744200565785.700000400800<00@00DS2H1S2H0S2H1S2HiS2Hi".
split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma u64arr_one : forall m A (w : word), rw_cells bsegs m A [C8 w] -> u64arr bsegs m A [w].
Proof.
intros m A w H. pose proof (rw_cells_bound bsegs m A _ H) as B. cbn [cells_size csize Nat.add] in B.
change [w] with ([] ++ [w]). apply u64arr_snoc; [apply u64arr_nil; lia|]. cbn [length Z.of_nat Z.mul]. rewrite Z.add_0_r. exact H.
Qed.
#[using="Type"] Lemma byte0_of_word : forall s0 hi, 0 <= s0 < 256 -> 0 <= hi -> Z.land (s0 + 256 * hi) 255 = s0.
Proof.
intros s0 hi H0 Hh. change 255 with (Z.ones 8). Local Ltac2 Set LiaHints.tbl := fun () => "0020>12110314666.1263368326006.5 00000900:S2H01H2H1S".
rewrite Z.land_ones by lia. change (2^8) with 256.
Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma byte0_cas_val : forall x s1, 0 <= x -> 0 <= s1 < 256 ->
Z.lxor x (Z.land (Z.lxor x s1) 255) = x - x mod 256 + s1.
Proof.
intros x s1 Hx Hs. set (r := x - x mod 256 + s1).
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>14733259133.1219518110623.1220630096075.1224994891013.1235055524057.1241126368384.2842675671692.1247815771673.2053764606531.1263370423289.1200000100600>00?00D00U00a00m012013SS3HgeS2Hk3HltSS3HltS3Rlo1H2H02H43H10S2Hx2Hs1H2H0S2Hs1H2H02H4S3HgeS".
assert (Hr : 0 <= r) by (subst r; Z.div_mod_to_equations; lia).
assert (Rlo : r mod 2^8 = s1) by (subst r; change (2^8) with 256; Z.div_mod_to_equations; lia).
assert (Rhi : r / 2^8 = x / 2^8) by (subst r; change (2^8) with 256; Z.div_mod_to_equations; lia).
apply Z.bits_inj'. intros k Hk.
rewrite Z.lxor_spec, Z.land_spec, Z.lxor_spec. change 255 with (Z.ones 8).
destruct (Z_lt_le_dec k 8) as [Hlt|Hge].
- rewrite Z.ones_spec_low by lia. rewrite <- (Z.mod_pow2_bits_low r 8 k) by lia. rewrite Rlo.
destruct (Z.testbit x k), (Z.testbit s1 k); reflexivity.
- rewrite Z.ones_spec_high by lia.
replace k with ((k - 8) + 8) at 4 by lia. rewrite <- (Z.div_pow2_bits r 8 (k - 8)) by lia. rewrite Rhi.
rewrite Z.div_pow2_bits by lia. replace (k - 8 + 8) with k by lia.
destruct (Z.testbit x k), (Z.testbit s1 k); reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma byte0_cas : forall s0 s1 hi, 0 <= s0 < 256 -> 0 <= s1 < 256 -> 0 <= hi ->
Z.lxor (s0 + 256 * hi) (Z.land (Z.lxor (s0 + 256 * hi) s1) 255) = s1 + 256 * hi.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "0030=34525805172.74519168643.146790055736.7 00000400=00CS2H0S1H2H22H3S1H2H1".
rewrite byte0_cas_val by lia. Z.div_mod_to_equations. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition afree_unw (RNG : footprint) (lo : Z) (m : amem) (top : Z) (sp s0 ra : word) (trt : list Z) : Prop :=
(exists tr, trt = bv_unsigned ra :: tr /\ uchain m top AFREE_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr
/\ (length tr <= 28)%nat /\ bv_unsigned sp + 16 < top /\ rng RNG lo (top - lo))
\/ (trt = [] /\ top <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47).
#[using="Type"] Lemma afree_unw_length : forall RNG lo m top sp s0 ra trt, afree_unw RNG lo m top sp s0 ra trt -> (length trt <= 29)%nat.
Proof. intros RNG lo m top sp s0 ra trt [(tr & -> & _ & L & _)|(-> & _)]; cbn; lia. Qed.
#[using="Type"] Lemma afree_unw_sp47 : forall RNG lo m top sp s0 ra trt, afree_unw RNG lo m top sp s0 ra trt -> top <= 2^47 -> bv_unsigned sp < 2^47.
Proof. intros RNG lo m top sp s0 ra trt [(tr & _ & _ & _ & B & _)|(_ & _ & B)] T; lia. Qed.
End CANSEC1.
