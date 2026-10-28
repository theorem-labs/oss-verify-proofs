(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 YI06 UI5b YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition byte_at (mem : word -> option byte) (a : Z) : Z :=
match mbyte ubs0segs mem a with Some b => bv_unsigned b | None => 0 end.
Lemma byte_at_range : forall mem a, 0 <= byte_at mem a < 256.
Proof using.
intros mem a. unfold byte_at. destruct (mbyte ubs0segs mem a) as [b|]; [|lia].
pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia.
Qed.
Lemma byte_at_val : forall mem a, present mem a -> val_mem ubs0segs mem a 1 (byte_at mem a).
Proof using.
intros mem a [b Hb] k Hk. destruct k; [|lia]. rewrite Z.add_0_r. unfold byte_at, mbyte. rewrite Hb.
f_equal. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H.
change (2 ^ 8) with 256. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma byte_at_mbyte : forall mem a, present mem a -> mbyte ubs0segs mem a = Some (Z_to_bv 8 (byte_at mem a)).
Proof using.
intros mem a [b Hb]. unfold byte_at, mbyte. rewrite Hb. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma div_256 : forall x y, 0 <= x < 256 -> (x + 256 * y) / 256 = y.
Proof using. intros x y Hx. rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. lia. Qed.
Lemma mod_256 : forall x y, 0 <= x < 256 -> (x + 256 * y) mod 256 = x.
Proof using. intros x y Hx. rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia. lia. Qed.
Lemma lor_shl8 : forall hi lo, 0 <= hi -> 0 <= lo < 256 -> Z.lor (hi * 256) lo = lo + 256 * hi.
Proof using.
intros hi lo Hhi Hlo.
assert (Hland : Z.land (hi * 256) lo = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n 8) as [Hn8|Hn8].
- change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z.bits_above_log2 lo); [apply andb_false_r | lia |].
destruct (Z.eq_dec lo 0) as [->|Hnz]; [cbn; lia|].
assert (Z.log2 lo < 8); [apply Z.log2_lt_pow2; lia | lia]. }
rewrite <- (Z.lxor_lor _ _ Hland), <- (Z.add_nocarry_lxor _ _ Hland). lia.
Qed.
Lemma val_mem_1 : forall m a b0,
mbyte ubs0segs m a = Some (Z_to_bv 8 b0) -> 0 <= b0 < 256 -> val_mem ubs0segs m a 1 b0.
Proof using.
intros m a b0 H0 R0 k Hk. destruct k; [|lia]. rewrite Z.add_0_r, H0. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma val_mem_2 : forall m a b0 b1,
mbyte ubs0segs m a = Some (Z_to_bv 8 b0) -> mbyte ubs0segs m (a + 1) = Some (Z_to_bv 8 b1) ->
0 <= b0 < 256 -> 0 <= b1 < 256 -> val_mem ubs0segs m a 2 (b0 + 256 * b1).
Proof using.
intros m a b0 b1 H0 H1 R0 R1 k Hk. unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with (256 * 256).
rewrite (Z.mod_small (b0 + 256 * b1)) by lia.
destruct k as [|[|k]]; [| | lia].
- rewrite Z.add_0_r, H0. f_equal. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. rewrite mod_256 by lia. reflexivity.
- change (Z.of_nat 1) with 1. rewrite H1. f_equal. change (8 * 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite div_256 by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma val_mem_4 : forall m a b0 b1,
mbyte ubs0segs m a = Some (Z_to_bv 8 b0) -> mbyte ubs0segs m (a + 1) = Some (Z_to_bv 8 b1) ->
mbyte ubs0segs m (a + 2) = Some (Z_to_bv 8 0) -> mbyte ubs0segs m (a + 3) = Some (Z_to_bv 8 0) ->
0 <= b0 < 256 -> 0 <= b1 < 256 -> val_mem ubs0segs m a 4 (b0 + 256 * b1).
Proof using.
intros m a b0 b1 H0 H1 H2 H3 R0 R1 k Hk. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 65536).
rewrite (Z.mod_small (b0 + 256 * b1)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia].
- rewrite Z.add_0_r, H0. f_equal. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. rewrite mod_256 by lia. reflexivity.
- change (Z.of_nat 1) with 1. rewrite H1. f_equal. change (8 * 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite div_256 by lia. rewrite Z.mod_small by lia. reflexivity.
- change (Z.of_nat 2) with 2. rewrite H2. f_equal. change (8 * 2) with 16. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with (256 * 256).
rewrite Z.div_small by lia. reflexivity.
- change (Z.of_nat 3) with 3. rewrite H3. f_equal. change (8 * 3) with 24. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with (256 * 256 * 256).
rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma frameconfig_obj : forall m dst lp img b0 b1 b2 b3 b4 b5 b6 b7 b8,
word_mem ubs0segs m dst lp -> 0 <= lp < 2 ^ 64 -> word_mem ubs0segs m (dst + 8) img -> 0 <= img < 2 ^ 64 ->
mbyte ubs0segs m (dst + 16) = Some (Z_to_bv 8 b0) -> mbyte ubs0segs m (dst + 17) = Some (Z_to_bv 8 b1) ->
mbyte ubs0segs m (dst + 18) = Some (Z_to_bv 8 0) -> mbyte ubs0segs m (dst + 19) = Some (Z_to_bv 8 0) ->
mbyte ubs0segs m (dst + 20) = Some (Z_to_bv 8 b2) -> mbyte ubs0segs m (dst + 21) = Some (Z_to_bv 8 b3) ->
mbyte ubs0segs m (dst + 22) = Some (Z_to_bv 8 0) -> mbyte ubs0segs m (dst + 23) = Some (Z_to_bv 8 0) ->
mbyte ubs0segs m (dst + 24) = Some (Z_to_bv 8 b4) -> mbyte ubs0segs m (dst + 25) = Some (Z_to_bv 8 b5) ->
mbyte ubs0segs m (dst + 26) = Some (Z_to_bv 8 b7) -> mbyte ubs0segs m (dst + 27) = Some (Z_to_bv 8 b8) ->
mbyte ubs0segs m (dst + 28) = Some (Z_to_bv 8 b6) ->
0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 ->
0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= b8 < 256 ->
obj_at ubs0segs m dst LAY_FrameConfig [lp; img; b0 + 256 * b1; b2 + 256 * b3; b4 + 256 * b5; b7 + 256 * b8; b6].
Proof using.
intros m dst lp img b0 b1 b2 b3 b4 b5 b6 b7 b8 Wl Rl Wi Ri H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28
R0 R1 R2 R3 R4 R5 R6 R7 R8.
cbn [obj_at LAY_FrameConfig]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
repeat split.
- rewrite Z.add_0_r. apply val_mem_word_mem. exact Wl.
- lia. - change (2 ^ (8 * 8)) with (2 ^ 64). lia.
- apply val_mem_word_mem. exact Wi.
- lia. - change (2 ^ (8 * 8)) with (2 ^ 64). lia.
- apply val_mem_4; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add Pos.succ]; try assumption.
- lia. - change (2 ^ (8 * 4)) with (256 * 256 * 65536). lia.
- apply val_mem_4; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add Pos.succ]; try assumption.
- lia. - change (2 ^ (8 * 4)) with (256 * 256 * 65536). lia.
- apply val_mem_2; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add Pos.succ]; try assumption.
- lia. - change (2 ^ (8 * 2)) with (256 * 256). lia.
- apply val_mem_2; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add Pos.succ]; try assumption.
- lia. - change (2 ^ (8 * 2)) with (256 * 256). lia.
- apply val_mem_1; assumption.
- lia. - change (2 ^ (8 * 1)) with 256. lia.
Qed.
Lemma st_chunk_byte : forall E ss ms i rg p off e a v,
st_ok ubs0segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CVal 1 e)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
mbyte ubs0segs (ms_mem ms) (a + off) = Some (Z_to_bv 8 v).
Proof using.
intros E ss ms i rg p off e a v HS Hi Hb Hin Hp He Hv.
pose proof (mem_ok_region ubs0segs E (ms_mem ms) (ss_mem ss) rg (st_ok_mem_ok ubs0segs E ss ms HS) ltac:(eapply nth_error_In; exact Hi)) as HR.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
pose proof (val_of_chunk_ok ubs0segs E (ms_mem ms) a off 1%N e v Hc He ltac:(cbn; lia) ltac:(cbn; lia)) as Hv1.
specialize (Hv1 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv1. rewrite Hv1. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma st_chunk_zero : forall E ss ms i rg p off len a j,
st_ok ubs0segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CZero len)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> 0 <= j < len ->
mbyte ubs0segs (ms_mem ms) (a + off + j) = Some (Z_to_bv 8 0).
Proof using.
intros E ss ms i rg p off len a j HS Hi Hb Hin Hp Hj.
pose proof (mem_ok_region ubs0segs E (ms_mem ms) (ss_mem ss) rg (st_ok_mem_ok ubs0segs E ss ms HS) ltac:(eapply nth_error_In; exact Hi)) as HR.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
destruct (Hc j ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [cbyte c_val c_off] in Hb1, Hb2. injection Hb1 as <-. exact Hb2.
Qed.
Lemma st_chunk_zero_word : forall E ss ms i rg p off len a o,
st_ok ubs0segs E ss ms -> nth_error (ss_mem ss) i = Some rg -> r_base rg = Some p ->
In (mkChunk off (CZero len)) (r_chunks rg) ->
bv_unsigned (ew E p) = a -> off <= o -> o + 8 <= off + len ->
word_mem ubs0segs (ms_mem ms) (a + o) 0.
Proof using.
intros E ss ms i rg p off len a o HS Hi Hb Hin Hp Ho1 Ho2 k Hk.
replace (a + o + Z.of_nat k) with (a + off + (o - off + Z.of_nat k)) by lia.
rewrite (st_chunk_zero E ss ms i rg p off len a _ HS Hi Hb Hin Hp) by lia.
f_equal. unfold le_byte. rewrite Z.mod_0_l by lia. rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma denot_pal3 : forall E n8 n7 b8 b7,
ew E n8 = Z_to_bv 64 b8 -> ew E n7 = Z_to_bv 64 b7 -> 0 <= b8 < 256 -> 0 <= b7 < 256 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SAlu ALU_OR (SAlu ALU_SLL (SOff n8 0) (SLit 8)) (SOff n7 0)) (SLit 1))
(SAlu ALU_OR (SAlu ALU_SLL (SOff n8 0) (SLit 8)) (SOff n7 0)))
= Z_to_bv 64 (3 * (b7 + 256 * b8)).
Proof using.
intros E n8 n7 b8 b7 H8 H7 R8 R7.
assert (Hor : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff n8 0) (SLit 8)) (SOff n7 0)) = b7 + 256 * b8).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite (U_atom E n8 b8 H8), (U_atom E n7 b7 H7) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (b8 * 256)) by (unfold M64; lia). rewrite lor_shl8 by lia. apply zcanon_id. unfold M64; lia. }
rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hor, U_SLit.
change (Z.land (zcanon 1) 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id ((b7 + 256 * b8) * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_and1_byte : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
U E (SAlu ALU_AND (SOff n 0) (SLit 1)) = Z.land b 1.
Proof using. intros E n b Hn Hb. rewrite U_and_lit by lia. rewrite (U_atom E n b Hn) by lia. reflexivity. Qed.
Lemma land1_low : forall lo hi, 0 <= lo -> 0 <= hi -> Z.land (lo + 256 * hi) 1 = Z.land lo 1.
Proof using.
intros lo hi Hlo Hhi. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
destruct (Z.eq_dec n 0) as [->|Hnz].
- rewrite !Z.bit0_odd. replace (lo + 256 * hi) with (lo + 2 * (128 * hi)) by lia. rewrite Z.odd_add_mul_2. reflexivity.
- rewrite (Z.bits_above_log2 1); [rewrite !andb_false_r; reflexivity | lia | cbn; lia].
Qed.
End c.
