(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di.

Module B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Definition w8 (b0 b1 b2 b3 b4 b5 b6 b7 : byte) : Z :=
bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))).
Lemma zb8_eq : forall (b : byte) z, z mod 256 = bv_unsigned b -> Z_to_bv 8 z = b.
Proof.
intros b z H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.of_N]. exact H.
Qed.
Lemma Z_to_le_bytes_S : forall n z, Z_to_le_bytes (S n) z = Z_to_bv 8 z :: Z_to_le_bytes n (Z.shiftr z 8).
Proof. reflexivity. Qed.
Lemma zle_step : forall (b : byte) r n, 0 <= r ->
Z_to_le_bytes (S n) (bv_unsigned b + 256 * r) = b :: Z_to_le_bytes n r.
Proof.
intros b r n Hr. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
rewrite Z_to_le_bytes_S. f_equal.
- apply zb8_eq. symmetry. apply Z.mod_unique with (q := r); [left; lia| lia].
- f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. symmetry. apply Z.div_unique with (r := bv_unsigned b); [left; lia| lia].
Qed.
Lemma le8_of_bytes : forall b0 b1 b2 b3 b4 b5 b6 b7 : byte,
le8 (Z_to_bv 64 (w8 b0 b1 b2 b3 b4 b5 b6 b7)) = [b0; b1; b2; b3; b4; b5; b6; b7].
Proof.
intros.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5.
pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
rewrite Z.mod_small by (unfold w8; change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
unfold w8.
rewrite (zle_step b0) by lia. rewrite (zle_step b1) by lia. rewrite (zle_step b2) by lia. rewrite (zle_step b3) by lia.
rewrite (zle_step b4) by lia. rewrite (zle_step b5) by lia. rewrite (zle_step b6) by lia.
replace (bv_unsigned b7) with (bv_unsigned b7 + 256 * 0) by lia. rewrite (zle_step b7) by lia. reflexivity.
Qed.
Lemma bytes_are_C8s : forall (n : nat) (bs : list byte), length bs = (8 * n)%nat ->
exists ws, length ws = n /\ cells_bytes (map C8 ws) = bs.
Proof.
induction n as [|n IH]; intros bs L.
- exists []. destruct bs; [split; reflexivity| cbn in L; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bs]]]]]]]]; cbn in L; try lia.
destruct (IH bs ltac:(lia)) as (ws & Lw & E).
exists (Z_to_bv 64 (w8 b0 b1 b2 b3 b4 b5 b6 b7) :: ws).
split; [cbn; lia|]. cbn [map cells_bytes cbytes]. rewrite le8_of_bytes, E. reflexivity.
Qed.
Lemma rw_cells_recast : forall segs m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Hb'. split; [split; [exact Hwf'| rewrite Hb'; exact Hb]|].
rewrite <- (cells_bytes_length cs' Hwf'), Hb', (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma rw_cells_CB_C8s : forall segs m A (n : nat) bs,
rw_cells segs m A [CB (8 * n) bs] -> exists ws, length ws = n /\ rw_cells segs m A (map C8 ws).
Proof.
intros segs m A n bs H.
assert (L : length bs = (8 * n)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (bytes_are_C8s n bs L) as (ws & Lw & E). exists ws. split; [exact Lw|].
eapply rw_cells_recast; [exact H| |].
- clear. induction ws; cbn; [exact I| split; [exact I| exact IHws]].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact E.
Qed.

Ltac frame2 FR :=
let fw := fresh "fw" in let L := fresh "Lfw" in let FR' := fresh "FR'" in
lazymatch type of FR with rw_cells ?segs _ _ _ =>
destruct (rw_cells_CB_C8s segs _ _ 2%nat _ FR) as (fw & L & FR'); clear FR;
let u0 := fresh "u" in let u1 := fresh "u" in
destruct fw as [|u0 [|u1 [|? ?]]]; cbn in L; try lia; cbn [map] in FR'; rename FR' into FR
end.

Lemma cells_at_app : forall segs m A cs1 cs2,
cells_at segs m A (cs1 ++ cs2) <-> cells_at segs m A cs1 /\ cells_at segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold cells_at.
rewrite cells_wf_app, cells_bytes_app, bytes_at_app. split.
- intros [[W1 W2] [B1 B2]]. rewrite cells_bytes_length in B2 by exact W1. tauto.
- intros [[W1 B1] [W2 B2]]. rewrite cells_bytes_length by exact W1. tauto.
Qed.

Lemma cells_size_C8s : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws; cbn; [reflexivity|]. rewrite IHws. lia. Qed.
Lemma cells_wf_C8s : forall ws, cells_wf (map C8 ws).
Proof. induction ws; cbn; [exact I| split; [exact I| exact IHws]]. Qed.

Lemma bytes_at_sub : forall segs m A bs (o n : nat),
bytes_at segs m A bs -> (o + n <= length bs)%nat -> bytes_at segs m (A + Z.of_nat o) (firstn n (skipn o bs)).
Proof.
intros segs m A bs o n B H.
rewrite <- (firstn_skipn o bs) in B. apply bytes_at_app in B. destruct B as [_ B].
rewrite firstn_length_le in B by lia.
rewrite <- (firstn_skipn n (skipn o bs)) in B. apply bytes_at_app in B. destruct B as [B _]. exact B.
Qed.

Lemma C8s_skipn : forall (ws : list word) k, skipn (8 * k) (cells_bytes (map C8 ws)) = cells_bytes (map C8 (skipn k ws)).
Proof.
induction ws as [|w ws IH]; intros k.
- cbn. rewrite !skipn_nil. reflexivity.
- destruct k as [|k]; [reflexivity|]. replace (8 * S k)%nat with (8 * k + 8)%nat by lia.
rewrite <- skipn_skipn. cbn [map cells_bytes cbytes].
rewrite skipn_app. rewrite (skipn_all2 (le8 w)) by (rewrite length_le8; lia). rewrite length_le8, Nat.sub_diag. cbn [skipn app]. apply IH.
Qed.

Lemma C8s_first16 : forall (ws : list word) k d, (k + 2 <= length ws)%nat ->
firstn 16 (skipn (8 * k) (cells_bytes (map C8 ws))) = le8 (nth k ws d) ++ le8 (nth (k + 1) ws d).
Proof.
intros ws k d H. rewrite C8s_skipn.
destruct (skipn k ws) as [|a [|b rest]] eqn:E.
- exfalso. apply (f_equal (@length word)) in E. rewrite length_skipn in E. cbn in E. lia.
- exfalso. apply (f_equal (@length word)) in E. rewrite length_skipn in E. cbn in E. lia.
- assert (Ha : nth k ws d = a). { rewrite <- (Nat.add_0_r k), <- nth_skipn, E. reflexivity. }
assert (Hb : nth (k + 1) ws d = b). { rewrite <- nth_skipn, E. reflexivity. }
rewrite Ha, Hb. cbn [map cells_bytes cbytes]. rewrite app_assoc, firstn_app, length_app, !length_le8.
change (16 - (8 + 8))%nat with 0%nat. rewrite firstn_O, app_nil_r. rewrite firstn_all2; [reflexivity|].
rewrite length_app, !length_le8. lia.
Qed.

Lemma ro_win2 : forall segs m A ws (o n k : nat) d,
ro_cells segs m A (map C8 ws) -> (8 * k = o + n)%nat -> (k + 2 <= length ws)%nat ->
ro_cells segs m (A + Z.of_nat o) [CB n (firstn n (skipn o (cells_bytes (map C8 ws)))); C8 (nth k ws d); C8 (nth (k + 1) ws d)].
Proof.
intros segs m A ws o n k d [W B] Hk H.
assert (LB : length (cells_bytes (map C8 ws)) = (8 * length ws)%nat) by (rewrite cells_bytes_length by apply cells_wf_C8s; apply cells_size_C8s).
pose proof (bytes_at_sub segs m A _ o (n + 16) B ltac:(lia)) as B'.
rewrite <- (firstn_skipn n (firstn (n + 16) _)) in B'. apply bytes_at_app in B'. destruct B' as [B1 B2].
rewrite firstn_firstn, Nat.min_l in B1, B2 by lia. rewrite firstn_length_le in B2 by (rewrite length_skipn; lia).
split.
- cbn. split; [rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity| exact (conj I (conj I I))].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply bytes_at_app. split; [exact B1|].
rewrite firstn_length_le by (rewrite length_skipn; lia).
replace (le8 (nth k ws d) ++ le8 (nth (k + 1) ws d)) with (firstn 16 (skipn (8 * k) (cells_bytes (map C8 ws)))) by (apply C8s_first16; lia).
replace (8 * k)%nat with (n + o)%nat by lia. rewrite <- skipn_skipn.
rewrite skipn_firstn_comm in B2. replace (n + 16 - n)%nat with 16%nat in B2 by lia. exact B2.
Qed.

Lemma C8s_firstn_bytes : forall (ws : list word) k cnt, (k + cnt <= length ws)%nat ->
firstn (8 * cnt) (skipn (8 * k) (cells_bytes (map C8 ws))) = cells_bytes (map C8 (firstn cnt (skipn k ws))).
Proof.
intros ws k cnt H. rewrite C8s_skipn. remember (skipn k ws) as l eqn:E.
assert (Hl : (cnt <= length l)%nat) by (subst l; rewrite length_skipn; lia). clear E H.
revert l Hl. induction cnt as [|c IH]; intros l Hl; [reflexivity|].
destruct l as [|w l]; [cbn in Hl; lia|]. cbn [firstn map cells_bytes cbytes].
replace (8 * S c)%nat with (length (le8 w) + 8 * c)%nat by (rewrite length_le8; lia).
rewrite firstn_app_2. f_equal. apply IH. cbn in Hl. lia.
Qed.

Lemma ro_win : forall segs m A ws (o n k cnt : nat),
ro_cells segs m A (map C8 ws) -> (8 * k = o + n)%nat -> (k + cnt <= length ws)%nat ->
ro_cells segs m (A + Z.of_nat o) (CB n (firstn n (skipn o (cells_bytes (map C8 ws)))) :: map C8 (firstn cnt (skipn k ws))).
Proof.
intros segs m A ws o n k cnt [W B] Hk H.
assert (LB : length (cells_bytes (map C8 ws)) = (8 * length ws)%nat) by (rewrite cells_bytes_length by apply cells_wf_C8s; apply cells_size_C8s).
pose proof (bytes_at_sub segs m A _ o (n + 8 * cnt) B ltac:(lia)) as B'.
rewrite <- (firstn_skipn n (firstn (n + 8 * cnt) _)) in B'. apply bytes_at_app in B'. destruct B' as [B1 B2].
rewrite firstn_firstn, Nat.min_l in B1, B2 by lia. rewrite firstn_length_le in B2 by (rewrite length_skipn; lia).
split.
- cbn. split; [rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity| apply cells_wf_C8s].
- cbn [cells_bytes cbytes app]. apply bytes_at_app. split; [exact B1|].
rewrite firstn_length_le by (rewrite length_skipn; lia).
rewrite <- C8s_firstn_bytes by lia. replace (8 * k)%nat with (n + o)%nat by lia. rewrite <- skipn_skipn.
rewrite skipn_firstn_comm in B2. replace (n + 8 * cnt - n)%nat with (8 * cnt)%nat in B2 by lia. exact B2.
Qed.

Lemma bytes_eq_of_unsigned : forall (a b : list byte), map bv_unsigned a = map bv_unsigned b -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma ro_cells_C8s_of_bytes : forall segs m A bs ws,
ro_cells segs m A [CB (length bs) bs] -> cells_bytes (map C8 ws) = bs -> ro_cells segs m A (map C8 ws).
Proof.
intros segs m A bs ws [_ B] E. split; [apply cells_wf_C8s|]. rewrite E. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma land_shiftr_scaled16 : forall t, 0 <= t ->
Z.land (Z.shiftr t 41) 2032 = 16 * Z.land (Z.shiftr t 45) 127.
Proof.
intros t Ht. apply Z.bits_inj'. intros k Hk.
rewrite Z.land_spec, Z.shiftr_spec by lia.
change 16 with (2 ^ 4). rewrite (Z.mul_comm (2 ^ 4)), Z.mul_pow2_bits by lia.
destruct (Z.lt_ge_cases k 4) as [L|L].
- rewrite (Z.testbit_neg_r _ (k - 4)) by lia.
replace (Z.testbit 2032 k) with false; [apply andb_false_r|].
destruct (Z.eq_dec k 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 1) as [->|]; [reflexivity|].
destruct (Z.eq_dec k 2) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 3) as [->|]; [reflexivity|]. lia.
- rewrite Z.land_spec, Z.shiftr_spec by lia. replace (k - 4 + 45) with (k + 41) by lia. f_equal.
change 2032 with (Z.shiftl 127 4). rewrite Z.shiftl_spec by lia. reflexivity.
Qed.

Lemma land_shiftr_scaled32 : forall t, 0 <= t ->
Z.land (Z.shiftr t 40) 4064 = 32 * Z.land (Z.shiftr t 45) 127.
Proof.
intros t Ht. apply Z.bits_inj'. intros k Hk.
rewrite Z.land_spec, Z.shiftr_spec by lia.
change 32 with (2 ^ 5). rewrite (Z.mul_comm (2 ^ 5)), Z.mul_pow2_bits by lia.
destruct (Z.lt_ge_cases k 5) as [L|L].
- rewrite (Z.testbit_neg_r _ (k - 5)) by lia.
replace (Z.testbit 4064 k) with false; [apply andb_false_r|].
destruct (Z.eq_dec k 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 1) as [->|]; [reflexivity|].
destruct (Z.eq_dec k 2) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 3) as [->|]; [reflexivity|].
destruct (Z.eq_dec k 4) as [->|]; [reflexivity|]. lia.
- rewrite Z.land_spec, Z.shiftr_spec by lia. replace (k - 5 + 45) with (k + 40) by lia. f_equal.
change 4064 with (Z.shiftl 127 5). rewrite Z.shiftl_spec by lia. reflexivity.
Qed.

Lemma shiftl57_shiftr53 : forall k, 0 <= k ->
Z.shiftr (Z.shiftl k 57 mod 2 ^ 64) 53 = 16 * (k mod 128).
Proof.
intros k Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_eq k 128) by lia.
replace (k * 2 ^ 57) with ((k - 128 * (k / 128)) * 2 ^ 57 + (k / 128) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. pose proof (Z.mod_pos_bound k 128 ltac:(lia)). rewrite (Z.mod_eq k 128) in H by lia.
rewrite Z.mod_small by lia.
symmetry. apply Z.div_unique_pos with 0; lia.
Qed.

Lemma land127_range : forall t, 0 <= Z.land t 127 < 128.
Proof.
intros t. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Ltac getreg R n :=
let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
eval cbv beta iota delta [tget] in (match tget p R with Some v => v | None => w0 end).

Ltac setf n x :=
lazymatch goal with |- evt _ _ (MS _ ?F _ _ _ _ _) => let v := getreg F n in set (x := v) end.

Ltac setx n x :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => let v := getreg R n in set (x := v) end.

Ltac name_freg n :=
lazymatch goal with |- evt _ _ (MS _ ?F _ _ _ _ _) =>
let v := getreg F n in
first [ is_var v
| lazymatch v with
| Z_to_bv 64 (Zpos _) => idtac
| Z_to_bv 64 Z0 => idtac
| Z_to_bv 64 (Zneg _) => idtac
| _ => let x := fresh "v" in set (x := v)
end ]
end.
Ltac name_fregs :=
name_freg 0; name_freg 1; name_freg 2; name_freg 3; name_freg 4; name_freg 5; name_freg 6; name_freg 7;
name_freg 10; name_freg 11; name_freg 12; name_freg 13; name_freg 14; name_freg 15; name_freg 16; name_freg 17;
name_freg 28; name_freg 29; name_freg 30; name_freg 31; name_freg 8; name_freg 9; name_freg 18.
Ltac nstep := zstep; try name_fregs.
Ltac at_pc a :=
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
let e := eval vm_compute in (Z.eqb p a) in lazymatch e with true => idtac end end.

Ltac run_to a := repeat (tryif at_pc a then fail else zstep).
Ltac nrun_to a := repeat (tryif at_pc a then fail else nstep).
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Definition w8 (b0 b1 b2 b3 b4 b5 b6 b7 : byte) : Z :=
bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))).
Lemma zb8_eq : forall (b : byte) z, z mod 256 = bv_unsigned b -> Z_to_bv 8 z = b.
Proof.
intros b z H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.of_N]. exact H.
Qed.
Lemma Z_to_le_bytes_S : forall n z, Z_to_le_bytes (S n) z = Z_to_bv 8 z :: Z_to_le_bytes n (Z.shiftr z 8).
Proof. reflexivity. Qed.
Lemma zle_step : forall (b : byte) r n, 0 <= r ->
Z_to_le_bytes (S n) (bv_unsigned b + 256 * r) = b :: Z_to_le_bytes n r.
Proof.
intros b r n Hr. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
rewrite Z_to_le_bytes_S. f_equal.
- apply zb8_eq. symmetry. apply Z.mod_unique with (q := r); [left; lia| lia].
- f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. symmetry. apply Z.div_unique with (r := bv_unsigned b); [left; lia| lia].
Qed.
Lemma le8_of_bytes : forall b0 b1 b2 b3 b4 b5 b6 b7 : byte,
le8 (Z_to_bv 64 (w8 b0 b1 b2 b3 b4 b5 b6 b7)) = [b0; b1; b2; b3; b4; b5; b6; b7].
Proof.
intros.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5.
pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
rewrite Z.mod_small by (unfold w8; change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
unfold w8.
rewrite (zle_step b0) by lia. rewrite (zle_step b1) by lia. rewrite (zle_step b2) by lia. rewrite (zle_step b3) by lia.
rewrite (zle_step b4) by lia. rewrite (zle_step b5) by lia. rewrite (zle_step b6) by lia.
replace (bv_unsigned b7) with (bv_unsigned b7 + 256 * 0) by lia. rewrite (zle_step b7) by lia. reflexivity.
Qed.
Lemma bytes_are_C8s : forall (n : nat) (bs : list byte), length bs = (8 * n)%nat ->
exists ws, length ws = n /\ cells_bytes (map C8 ws) = bs.
Proof.
induction n as [|n IH]; intros bs L.
- exists []. destruct bs; [split; reflexivity| cbn in L; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bs]]]]]]]]; cbn in L; try lia.
destruct (IH bs ltac:(lia)) as (ws & Lw & E).
exists (Z_to_bv 64 (w8 b0 b1 b2 b3 b4 b5 b6 b7) :: ws).
split; [cbn; lia|]. cbn [map cells_bytes cbytes]. rewrite le8_of_bytes, E. reflexivity.
Qed.
Lemma rw_cells_recast : forall segs m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Hb'. split; [split; [exact Hwf'| rewrite Hb'; exact Hb]|].
rewrite <- (cells_bytes_length cs' Hwf'), Hb', (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma rw_cells_CB_C8s : forall segs m A (n : nat) bs,
rw_cells segs m A [CB (8 * n) bs] -> exists ws, length ws = n /\ rw_cells segs m A (map C8 ws).
Proof.
intros segs m A n bs H.
assert (L : length bs = (8 * n)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (bytes_are_C8s n bs L) as (ws & Lw & E). exists ws. split; [exact Lw|].
eapply rw_cells_recast; [exact H| |].
- clear. induction ws; cbn; [exact I| split; [exact I| exact IHws]].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact E.
Qed.

Ltac frame2 FR :=
let fw := fresh "fw" in let L := fresh "Lfw" in let FR' := fresh "FR'" in
lazymatch type of FR with rw_cells ?segs _ _ _ =>
destruct (rw_cells_CB_C8s segs _ _ 2%nat _ FR) as (fw & L & FR'); clear FR;
let u0 := fresh "u" in let u1 := fresh "u" in
destruct fw as [|u0 [|u1 [|? ?]]]; cbn in L; try lia; cbn [map] in FR'; rename FR' into FR
end.

Lemma cells_at_app : forall segs m A cs1 cs2,
cells_at segs m A (cs1 ++ cs2) <-> cells_at segs m A cs1 /\ cells_at segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold cells_at.
rewrite cells_wf_app, cells_bytes_app, bytes_at_app. split.
- intros [[W1 W2] [B1 B2]]. rewrite cells_bytes_length in B2 by exact W1. tauto.
- intros [[W1 B1] [W2 B2]]. rewrite cells_bytes_length by exact W1. tauto.
Qed.

Lemma cells_size_C8s : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws; cbn; [reflexivity|]. rewrite IHws. lia. Qed.
Lemma cells_wf_C8s : forall ws, cells_wf (map C8 ws).
Proof. induction ws; cbn; [exact I| split; [exact I| exact IHws]]. Qed.

Lemma bytes_at_sub : forall segs m A bs (o n : nat),
bytes_at segs m A bs -> (o + n <= length bs)%nat -> bytes_at segs m (A + Z.of_nat o) (firstn n (skipn o bs)).
Proof.
intros segs m A bs o n B H.
rewrite <- (firstn_skipn o bs) in B. apply bytes_at_app in B. destruct B as [_ B].
rewrite firstn_length_le in B by lia.
rewrite <- (firstn_skipn n (skipn o bs)) in B. apply bytes_at_app in B. destruct B as [B _]. exact B.
Qed.

Lemma C8s_skipn : forall (ws : list word) k, skipn (8 * k) (cells_bytes (map C8 ws)) = cells_bytes (map C8 (skipn k ws)).
Proof.
induction ws as [|w ws IH]; intros k.
- cbn. rewrite !skipn_nil. reflexivity.
- destruct k as [|k]; [reflexivity|]. replace (8 * S k)%nat with (8 * k + 8)%nat by lia.
rewrite <- skipn_skipn. cbn [map cells_bytes cbytes].
rewrite skipn_app. rewrite (skipn_all2 (le8 w)) by (rewrite length_le8; lia). rewrite length_le8, Nat.sub_diag. cbn [skipn app]. apply IH.
Qed.

Lemma C8s_first16 : forall (ws : list word) k d, (k + 2 <= length ws)%nat ->
firstn 16 (skipn (8 * k) (cells_bytes (map C8 ws))) = le8 (nth k ws d) ++ le8 (nth (k + 1) ws d).
Proof.
intros ws k d H. rewrite C8s_skipn.
destruct (skipn k ws) as [|a [|b rest]] eqn:E.
- exfalso. apply (f_equal (@length word)) in E. rewrite length_skipn in E. cbn in E. lia.
- exfalso. apply (f_equal (@length word)) in E. rewrite length_skipn in E. cbn in E. lia.
- assert (Ha : nth k ws d = a). { rewrite <- (Nat.add_0_r k), <- nth_skipn, E. reflexivity. }
assert (Hb : nth (k + 1) ws d = b). { rewrite <- nth_skipn, E. reflexivity. }
rewrite Ha, Hb. cbn [map cells_bytes cbytes]. rewrite app_assoc, firstn_app, length_app, !length_le8.
change (16 - (8 + 8))%nat with 0%nat. rewrite firstn_O, app_nil_r. rewrite firstn_all2; [reflexivity|].
rewrite length_app, !length_le8. lia.
Qed.

Lemma ro_win2 : forall segs m A ws (o n k : nat) d,
ro_cells segs m A (map C8 ws) -> (8 * k = o + n)%nat -> (k + 2 <= length ws)%nat ->
ro_cells segs m (A + Z.of_nat o) [CB n (firstn n (skipn o (cells_bytes (map C8 ws)))); C8 (nth k ws d); C8 (nth (k + 1) ws d)].
Proof.
intros segs m A ws o n k d [W B] Hk H.
assert (LB : length (cells_bytes (map C8 ws)) = (8 * length ws)%nat) by (rewrite cells_bytes_length by apply cells_wf_C8s; apply cells_size_C8s).
pose proof (bytes_at_sub segs m A _ o (n + 16) B ltac:(lia)) as B'.
rewrite <- (firstn_skipn n (firstn (n + 16) _)) in B'. apply bytes_at_app in B'. destruct B' as [B1 B2].
rewrite firstn_firstn, Nat.min_l in B1, B2 by lia. rewrite firstn_length_le in B2 by (rewrite length_skipn; lia).
split.
- cbn. split; [rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity| exact (conj I (conj I I))].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply bytes_at_app. split; [exact B1|].
rewrite firstn_length_le by (rewrite length_skipn; lia).
replace (le8 (nth k ws d) ++ le8 (nth (k + 1) ws d)) with (firstn 16 (skipn (8 * k) (cells_bytes (map C8 ws)))) by (apply C8s_first16; lia).
replace (8 * k)%nat with (n + o)%nat by lia. rewrite <- skipn_skipn.
rewrite skipn_firstn_comm in B2. replace (n + 16 - n)%nat with 16%nat in B2 by lia. exact B2.
Qed.

Lemma C8s_firstn_bytes : forall (ws : list word) k cnt, (k + cnt <= length ws)%nat ->
firstn (8 * cnt) (skipn (8 * k) (cells_bytes (map C8 ws))) = cells_bytes (map C8 (firstn cnt (skipn k ws))).
Proof.
intros ws k cnt H. rewrite C8s_skipn. remember (skipn k ws) as l eqn:E.
assert (Hl : (cnt <= length l)%nat) by (subst l; rewrite length_skipn; lia). clear E H.
revert l Hl. induction cnt as [|c IH]; intros l Hl; [reflexivity|].
destruct l as [|w l]; [cbn in Hl; lia|]. cbn [firstn map cells_bytes cbytes].
replace (8 * S c)%nat with (length (le8 w) + 8 * c)%nat by (rewrite length_le8; lia).
rewrite firstn_app_2. f_equal. apply IH. cbn in Hl. lia.
Qed.

Lemma ro_win : forall segs m A ws (o n k cnt : nat),
ro_cells segs m A (map C8 ws) -> (8 * k = o + n)%nat -> (k + cnt <= length ws)%nat ->
ro_cells segs m (A + Z.of_nat o) (CB n (firstn n (skipn o (cells_bytes (map C8 ws)))) :: map C8 (firstn cnt (skipn k ws))).
Proof.
intros segs m A ws o n k cnt [W B] Hk H.
assert (LB : length (cells_bytes (map C8 ws)) = (8 * length ws)%nat) by (rewrite cells_bytes_length by apply cells_wf_C8s; apply cells_size_C8s).
pose proof (bytes_at_sub segs m A _ o (n + 8 * cnt) B ltac:(lia)) as B'.
rewrite <- (firstn_skipn n (firstn (n + 8 * cnt) _)) in B'. apply bytes_at_app in B'. destruct B' as [B1 B2].
rewrite firstn_firstn, Nat.min_l in B1, B2 by lia. rewrite firstn_length_le in B2 by (rewrite length_skipn; lia).
split.
- cbn. split; [rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity| apply cells_wf_C8s].
- cbn [cells_bytes cbytes app]. apply bytes_at_app. split; [exact B1|].
rewrite firstn_length_le by (rewrite length_skipn; lia).
rewrite <- C8s_firstn_bytes by lia. replace (8 * k)%nat with (n + o)%nat by lia. rewrite <- skipn_skipn.
rewrite skipn_firstn_comm in B2. replace (n + 8 * cnt - n)%nat with (8 * cnt)%nat in B2 by lia. exact B2.
Qed.

Lemma bytes_eq_of_unsigned : forall (a b : list byte), map bv_unsigned a = map bv_unsigned b -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma ro_cells_C8s_of_bytes : forall segs m A bs ws,
ro_cells segs m A [CB (length bs) bs] -> cells_bytes (map C8 ws) = bs -> ro_cells segs m A (map C8 ws).
Proof.
intros segs m A bs ws [_ B] E. split; [apply cells_wf_C8s|]. rewrite E. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma land_shiftr_scaled16 : forall t, 0 <= t ->
Z.land (Z.shiftr t 41) 2032 = 16 * Z.land (Z.shiftr t 45) 127.
Proof.
intros t Ht. apply Z.bits_inj'. intros k Hk.
rewrite Z.land_spec, Z.shiftr_spec by lia.
change 16 with (2 ^ 4). rewrite (Z.mul_comm (2 ^ 4)), Z.mul_pow2_bits by lia.
destruct (Z.lt_ge_cases k 4) as [L|L].
- rewrite (Z.testbit_neg_r _ (k - 4)) by lia.
replace (Z.testbit 2032 k) with false; [apply andb_false_r|].
destruct (Z.eq_dec k 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 1) as [->|]; [reflexivity|].
destruct (Z.eq_dec k 2) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 3) as [->|]; [reflexivity|]. lia.
- rewrite Z.land_spec, Z.shiftr_spec by lia. replace (k - 4 + 45) with (k + 41) by lia. f_equal.
change 2032 with (Z.shiftl 127 4). rewrite Z.shiftl_spec by lia. reflexivity.
Qed.

Lemma land_shiftr_scaled32 : forall t, 0 <= t ->
Z.land (Z.shiftr t 40) 4064 = 32 * Z.land (Z.shiftr t 45) 127.
Proof.
intros t Ht. apply Z.bits_inj'. intros k Hk.
rewrite Z.land_spec, Z.shiftr_spec by lia.
change 32 with (2 ^ 5). rewrite (Z.mul_comm (2 ^ 5)), Z.mul_pow2_bits by lia.
destruct (Z.lt_ge_cases k 5) as [L|L].
- rewrite (Z.testbit_neg_r _ (k - 5)) by lia.
replace (Z.testbit 4064 k) with false; [apply andb_false_r|].
destruct (Z.eq_dec k 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 1) as [->|]; [reflexivity|].
destruct (Z.eq_dec k 2) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 3) as [->|]; [reflexivity|].
destruct (Z.eq_dec k 4) as [->|]; [reflexivity|]. lia.
- rewrite Z.land_spec, Z.shiftr_spec by lia. replace (k - 5 + 45) with (k + 40) by lia. f_equal.
change 4064 with (Z.shiftl 127 5). rewrite Z.shiftl_spec by lia. reflexivity.
Qed.

Lemma shiftl57_shiftr53 : forall k, 0 <= k ->
Z.shiftr (Z.shiftl k 57 mod 2 ^ 64) 53 = 16 * (k mod 128).
Proof.
intros k Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_eq k 128) by lia.
replace (k * 2 ^ 57) with ((k - 128 * (k / 128)) * 2 ^ 57 + (k / 128) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. pose proof (Z.mod_pos_bound k 128 ltac:(lia)). rewrite (Z.mod_eq k 128) in H by lia.
rewrite Z.mod_small by lia.
symmetry. apply Z.div_unique_pos with 0; lia.
Qed.

Lemma land127_range : forall t, 0 <= Z.land t 127 < 128.
Proof.
intros t. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Ltac getreg R n :=
let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
eval cbv beta iota delta [tget] in (match tget p R with Some v => v | None => w0 end).

Ltac setf n x :=
lazymatch goal with |- evt _ _ (MS _ ?F _ _ _ _ _) => let v := getreg F n in set (x := v) end.

Ltac setx n x :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => let v := getreg R n in set (x := v) end.

Ltac name_freg n :=
lazymatch goal with |- evt _ _ (MS _ ?F _ _ _ _ _) =>
let v := getreg F n in
first [ is_var v
| lazymatch v with
| Z_to_bv 64 (Zpos _) => idtac
| Z_to_bv 64 Z0 => idtac
| Z_to_bv 64 (Zneg _) => idtac
| _ => let x := fresh "v" in set (x := v)
end ]
end.
Ltac name_fregs :=
name_freg 0; name_freg 1; name_freg 2; name_freg 3; name_freg 4; name_freg 5; name_freg 6; name_freg 7;
name_freg 10; name_freg 11; name_freg 12; name_freg 13; name_freg 14; name_freg 15; name_freg 16; name_freg 17;
name_freg 28; name_freg 29; name_freg 30; name_freg 31; name_freg 8; name_freg 9; name_freg 18.
Ltac nstep := zstep; try name_fregs.
Ltac at_pc a :=
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
let e := eval vm_compute in (Z.eqb p a) in lazymatch e with true => idtac end end.

Ltac run_to a := repeat (tryif at_pc a then fail else zstep).
Ltac nrun_to a := repeat (tryif at_pc a then fail else nstep).
