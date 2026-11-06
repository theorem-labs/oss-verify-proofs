(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1dg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition f32 (ws : list word) : list cell := map C4 ws.
Lemma f32_app : forall a b, f32 (a ++ b) = f32 a ++ f32 b.
Proof. intros. unfold f32. apply map_app. Qed.
Lemma cells_size_f32 : forall ws, cells_size (f32 ws) = (4 * length ws)%nat.
Proof. induction ws; cbn; [reflexivity|]. unfold f32 in IHws. rewrite IHws. lia. Qed.
Lemma f32_cons : forall w ws, f32 (w :: ws) = C4 w :: f32 ws.
Proof. reflexivity. Qed.
Lemma f32_nil : f32 [] = [].
Proof. reflexivity. Qed.
Lemma length_f32 : forall ws, length (f32 ws) = length ws.
Proof. intros. unfold f32. apply length_map. Qed.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
intros segs m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hn & H). repeat split; try lia.
+ intros i Hi. apply H. lia.
+ intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
- intros ((Ha & Hn & HA) & (Hb & Hm & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app, Nat2Z.inj_add.
split.
- intros ([[W1 W2] [B1 B2]] & WR). rewrite (cells_bytes_length cs1 W1) in B2.
apply wr_at_app in WR as [WR1 WR2]; [|lia|lia].
exact (conj (conj (conj W1 B1) WR1) (conj (conj W2 B2) WR2)).
- intros ([[W1 B1] WR1] & [[W2 B2] WR2]). rewrite (cells_bytes_length cs1 W1).
refine (conj (conj (conj W1 W2) (conj B1 B2)) _). apply wr_at_app; [lia|lia|]. split; assumption.
Qed.

Lemma rw_cells_uncons : forall segs m A c cs,
rw_cells segs m A (c :: cs) -> rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
intros segs m A c cs H. change (c :: cs) with ([c] ++ cs) in H. apply rw_cells_app in H.
cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma rw_cells_snoc : forall segs m A cs c,
rw_cells segs m A cs -> rw_cells segs m (A + Z.of_nat (cells_size cs)) [c] -> rw_cells segs m A (cs ++ [c]).
Proof. intros segs m A cs c H1 H2. apply rw_cells_app. split; assumption. Qed.

Lemma rw_cells_join : forall segs m A cs1 cs2,
rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof. intros segs m A cs1 cs2 H1 H2. apply rw_cells_app. split; assumption. Qed.

Lemma rw_cells_nil : forall segs m A, (0 <= A <= 2^64)%Z -> rw_cells segs m A [].
Proof.
intros segs m A HA. split; [split; [exact I| apply bytes_at_nil; exact HA]|].
cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Ltac is_pos_lit p := lazymatch p with xH => idtac | xO ?q => is_pos_lit q | xI ?q => is_pos_lit q end.
Ltac is_Z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => is_pos_lit p | Zneg ?p => is_pos_lit p end.
Ltac fold_of_nat_lits_in H :=
repeat match type of H with
| context [Z.of_nat ?n] => let v := eval cbv in (Z.of_nat n) in is_Z_lit v; change (Z.of_nat n) with v in H
end.
Ltac fold_of_nat_lits :=
repeat match goal with
| |- context [Z.of_nat ?n] => let v := eval cbv in (Z.of_nat n) in is_Z_lit v; change (Z.of_nat n) with v
end.

Tactic Notation "chunk_uncons" hyp(H) "as" ident(H1) :=
apply rw_cells_uncons in H; destruct H as [H1 H]; cbn [csize] in H; fold_of_nat_lits_in H.

Lemma rw_cells_f32_split : forall segs m A l n,
rw_cells segs m A (f32 l) ->
rw_cells segs m A (f32 (firstn n l)) /\ rw_cells segs m (A + Z.of_nat (4 * length (firstn n l)))%Z (f32 (skipn n l)).
Proof.
intros segs m A l n H. rewrite <- (firstn_skipn n l) in H at 1. rewrite f32_app in H.
apply rw_cells_app in H. rewrite cells_size_f32 in H. exact H.
Qed.
Tactic Notation "chunk_split_f32" hyp(H) "at" constr(n) "as" ident(H1) :=
apply (rw_cells_f32_split _ _ _ _ n) in H; destruct H as [H1 H];
cbn [firstn skipn app length Nat.mul Nat.add] in H1, H; fold_of_nat_lits_in H.

Ltac simpl_sizes ::=
rewrite ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].
Ltac simpl_sizes_goal ::=
literal_cell_sizes;
try match goal with |- context [cells_size (_ ++ _)] => rewrite !cells_size_app end;
try match goal with |- context [cells_size (f32 _)] => rewrite !cells_size_f32 end;
try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end.

Create HintDb chunk_sizes discriminated.
#[export] Hint Rewrite length_f32 cells_size_f32 : chunk_sizes.

Lemma zb8_eq : forall (b : byte) z, z mod 256 = bv_unsigned b -> Z_to_bv 8 z = b.
Proof.
intros b z H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.of_N]. exact H.
Qed.
Lemma le4_of_bytes : forall b0 b1 b2 b3 : byte,
le4 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)) = [b0; b1; b2; b3].
Proof.
intros b0 b1 b2 b3.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
rewrite Z.mod_small by (cbn; lia).
cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
set (u := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
f_equal; [apply zb8_eq; subst u; symmetry; rewrite <- (Z.mod_small (bv_unsigned b0) 256) at 1 by lia; apply Z.mod_unique with (q:= bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3); [left; lia| lia] |].
f_equal; [apply zb8_eq; replace (u / 256) with (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3)) by (subst u; apply Z.div_unique with (r := bv_unsigned b0); [left; lia|lia]);
symmetry; apply Z.mod_unique with (q := bv_unsigned b2 + 256 * bv_unsigned b3); [left; lia|lia] |].
f_equal; [apply zb8_eq; replace (u / 256 / 256) with (bv_unsigned b2 + 256 * bv_unsigned b3) by (subst u; rewrite Zdiv.Zdiv_Zdiv by lia; apply Z.div_unique with (r := bv_unsigned b0 + 256 * bv_unsigned b1); [left; lia|lia]);
symmetry; apply Z.mod_unique with (q := bv_unsigned b3); [left; lia|lia] |].
f_equal. apply zb8_eq. replace (u / 256 / 256 / 256) with (bv_unsigned b3) by (subst u; rewrite !Zdiv.Zdiv_Zdiv by lia; apply Z.div_unique with (r := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2); [left; lia|lia]).
apply Z.mod_small. lia.
Qed.

Lemma bytes_are_f32 : forall (n : nat) (bs : list byte), length bs = (4 * n)%nat ->
exists ws, length ws = n /\ cells_bytes (f32 ws) = bs.
Proof.
induction n as [|n IH]; intros bs L.
- exists []. destruct bs; [split; reflexivity| cbn in L; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 bs]]]]; cbn in L; try lia.
destruct (IH bs ltac:(lia)) as (ws & Lw & E).
exists (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) :: ws).
split; [cbn; lia|]. rewrite f32_cons. cbn [cells_bytes cbytes]. rewrite le4_of_bytes, E. reflexivity.
Qed.

Lemma rw_cells_recast : forall segs m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Hb'. split; [split; [exact Hwf'| rewrite Hb'; exact Hb]|].
rewrite <- (cells_bytes_length cs' Hwf'), Hb', (cells_bytes_length cs Hwf). exact Hw.
Qed.
Lemma cells_wf_f32 : forall ws, cells_wf (f32 ws).
Proof. induction ws; cbn; [exact I| split; [exact I| exact IHws]]. Qed.

Lemma rw_cells_CB_f32 : forall segs m A (n : nat) bs,
rw_cells segs m A [CB (4 * n) bs] -> exists ws, length ws = n /\ rw_cells segs m A (f32 ws).
Proof.
intros segs m A n bs H.
assert (L : length bs = (4 * n)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (bytes_are_f32 n bs L) as (ws & Lw & E). exists ws. split; [exact Lw|].
eapply rw_cells_recast; [exact H| apply cells_wf_f32|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact E.
Qed.

Lemma rw_cells_f32_CB : forall segs m A ws,
rw_cells segs m A (f32 ws) -> rw_cells segs m A [CB (4 * length ws) (cells_bytes (f32 ws))].
Proof.
intros segs m A ws H. eapply rw_cells_recast; [exact H| |].
- cbn. split; [|exact I]. rewrite cells_bytes_length by apply cells_wf_f32. apply cells_size_f32.
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity.
Qed.

Lemma rw_cells_f32_mid : forall segs m A ws i k,
rw_cells segs m A (f32 ws) -> (i <= length ws)%nat ->
rw_cells segs m (A + 4 * Z.of_nat i)%Z (f32 (firstn k (skipn i ws))).
Proof.
intros segs m A ws i k H Hi.
rewrite <- (firstn_skipn i ws) in H. rewrite f32_app in H. apply rw_cells_app in H. destruct H as [_ H].
rewrite cells_size_f32, firstn_length_le in H by exact Hi.
replace (Z.of_nat (4 * i)) with (4 * Z.of_nat i)%Z in H by lia.
rewrite <- (firstn_skipn k (skipn i ws)) in H. rewrite f32_app in H. apply rw_cells_app in H. destruct H as [H _]. exact H.
Qed.

Lemma f32_split : forall segs m A ws (i : nat), (i <= length ws)%nat ->
rw_cells segs m A (f32 ws) ->
rw_cells segs m A (f32 (firstn i ws)) /\ rw_cells segs m (A + 4 * Z.of_nat i) (f32 (skipn i ws)).
Proof.
intros segs m A ws i Hi H. rewrite <- (firstn_skipn i ws) in H. rewrite f32_app in H.
apply rw_cells_app in H. rewrite cells_size_f32, firstn_length_le in H by exact Hi.
replace (Z.of_nat (4 * i)) with (4 * Z.of_nat i)%Z in H by lia. exact H.
Qed.
Lemma f32_join : forall segs m A ws1 ws2,
rw_cells segs m A (f32 ws1) -> rw_cells segs m (A + 4 * Z.of_nat (length ws1)) (f32 ws2) ->
rw_cells segs m A (f32 (ws1 ++ ws2)).
Proof.
intros segs m A ws1 ws2 H1 H2. rewrite f32_app. apply rw_cells_join; [exact H1|].
rewrite cells_size_f32. replace (Z.of_nat (4 * length ws1)) with (4 * Z.of_nat (length ws1))%Z by lia. exact H2.
Qed.

Ltac chunk_snoc HD H1 :=
lazymatch type of HD with
| rw_cells ?segs ?m ?A ?cs =>
lazymatch type of H1 with
| rw_cells _ _ ?A1 [?c] =>
let E := fresh in
assert (E : A1 = (A + Z.of_nat (cells_size cs))%Z)
by (rewrite ?cells_size_app, ?cells_size_f32, ?length_app, ?length_f32; autorewrite with chunk_sizes; cbn [cells_size csize length]; lia);
rewrite E in H1; pose proof (rw_cells_snoc segs m A cs c HD H1) as HD';
clear HD H1 E; rename HD' into HD
end
end.

Ltac chunk_cat H1 H2 :=
lazymatch type of H1 with rw_cells ?segs ?m ?A1 ?cs1 =>
lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
let H := fresh "CAT" in
assert (H : rw_cells segs m A1 (cs1 ++ cs2))
by (apply rw_cells_join; [exact H1 |
replace (A1 + Z.of_nat (cells_size cs1))%Z with A2
by (rewrite ?cells_size_app, ?cells_size_f32; autorewrite with chunk_sizes;
cbn [cells_size csize Nat.add Nat.mul length]; fold_of_nat_lits; lia);
exact H2]);
clear H1 H2; cbn [app] in H; rename H into H1
end end.

Lemma ro_cells_app : forall segs m A cs1 cs2,
ro_cells segs m A (cs1 ++ cs2) <-> ro_cells segs m A cs1 /\ ro_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold ro_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
split.
- intros [[W1 W2] [B1 B2]]. rewrite (cells_bytes_length cs1 W1) in B2. exact (conj (conj W1 B1) (conj W2 B2)).
- intros [[W1 B1] [W2 B2]]. rewrite (cells_bytes_length cs1 W1). exact (conj (conj W1 W2) (conj B1 B2)).
Qed.
Lemma ro_f32_mid : forall segs m A ws (i k : nat),
ro_cells segs m A (f32 ws) -> (i <= length ws)%nat ->
ro_cells segs m (A + 4 * Z.of_nat i) (f32 (firstn k (skipn i ws))).
Proof.
intros segs m A ws i k H Hi.
rewrite <- (firstn_skipn i ws) in H. rewrite f32_app in H. apply ro_cells_app in H. destruct H as [_ H].
rewrite cells_size_f32, firstn_length_le in H by exact Hi.
replace (Z.of_nat (4 * i)) with (4 * Z.of_nat i) in H by lia.
rewrite <- (firstn_skipn k (skipn i ws)) in H. rewrite f32_app in H. apply ro_cells_app in H. destruct H as [H _]. exact H.
Qed.
Lemma ro_f32_uncons : forall segs m A w ws,
ro_cells segs m A (f32 (w :: ws)) -> ro_cells segs m (A + 4) (f32 ws).
Proof.
intros segs m A w ws H. rewrite f32_cons in H. change (C4 w :: f32 ws) with ([C4 w] ++ f32 ws) in H.
apply ro_cells_app in H. destruct H as [_ H]. exact H.
Qed.
Lemma rw_f32_uncons : forall segs m A w ws,
rw_cells segs m A (f32 (w :: ws)) -> rw_cells segs m (A + 4) (f32 ws).
Proof.
intros segs m A w ws H. rewrite f32_cons in H. apply rw_cells_uncons in H. destruct H as [_ H]. exact H.
Qed.
