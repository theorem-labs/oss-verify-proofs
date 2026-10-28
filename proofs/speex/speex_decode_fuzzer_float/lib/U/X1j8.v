(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii X1io.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rl X1nw X1qz X1r0 X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition buf_pre (buf : list Z) (bytes : list byte) : Prop :=
firstn (length buf) (ubytes bytes) = buf /\ (length buf <= length bytes)%nat.

Lemma nth_firstn_lt : forall {X} (l : list X) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
induction l as [|x l IH]; intros [|n] [|k] d Hk; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma pre_znth : forall buf bytes i, buf_pre buf bytes -> 0 <= i -> (Z.to_nat i < length buf)%nat ->
znth buf i = bv_unsigned (nth (Z.to_nat i) bytes (Z_to_bv 8 0)).
Proof.
intros buf bytes i [PRE LE] Hi Hl. rewrite <- PRE. unfold znth. destruct (Z.ltb_spec i 0); [lia|].
rewrite nth_firstn_lt by lia. unfold ubytes. rewrite <- (map_nth bv_unsigned). reflexivity.
Qed.

Lemma pre_zslice : forall buf bytes off n, buf_pre buf bytes -> 0 <= off -> 0 <= n -> (Z.to_nat off + Z.to_nat n <= length buf)%nat ->
zslice off n buf = ubytes (firstn (Z.to_nat n) (skipn (Z.to_nat off) bytes)).
Proof.
intros buf bytes off n [PRE LE] Ho Hn Hl. unfold zslice, ztake, zdrop. rewrite <- PRE.
rewrite ubytes_firstn, ubytes_skipn. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

Lemma pre_zslice4 : forall buf bytes off, buf_pre buf bytes -> 0 <= off -> (Z.to_nat off + 4 <= length buf)%nat ->
zslice off 4 buf = [bv_unsigned (nth (Z.to_nat off) bytes (Z_to_bv 8 0)); bv_unsigned (nth (Z.to_nat (off + 1)) bytes (Z_to_bv 8 0));
bv_unsigned (nth (Z.to_nat (off + 2)) bytes (Z_to_bv 8 0)); bv_unsigned (nth (Z.to_nat (off + 3)) bytes (Z_to_bv 8 0))].
Proof.
intros buf bytes off PRE Ho Hl. pose proof PRE as [_ LE]. rewrite (pre_zslice buf bytes off 4 PRE) by lia.
rewrite ubytes_firstn, ubytes_skipn.
rewrite (ubytes_skip_cons bytes off), (ubytes_skip_cons bytes (off + 1)), (ubytes_skip_cons bytes (off + 1 + 1)), (ubytes_skip_cons bytes (off + 1 + 1 + 1)) by lia.
change (Z.to_nat 4) with 4%nat. cbn [firstn].
replace (off + 1 + 1) with (off + 2) by lia. replace (off + 2 + 1) with (off + 3) by lia. reflexivity.
Qed.

Lemma find_byte_bridge : forall c (l : list byte) s,
X1qz.find_byte c (ubytes l) s = match X1rl.find_byte c l with Some j => Some (s + Z.of_nat j) | None => None end.
Proof.
intros c l. induction l as [|b l IH]; intros s; cbn [ubytes map X1qz.find_byte X1rl.find_byte]; [reflexivity|].
fold (ubytes l). destruct (bv_unsigned b =? c); [f_equal; lia|].
rewrite IH. destruct (X1rl.find_byte c l); [f_equal; lia| reflexivity].
Qed.

Lemma recell_zero8 : forall m X pre post,
rw_cells rsegs m X (pre ++ C8 (Z_to_bv 64 0) :: post) -> rw_cells rsegs m X (pre ++ C4 (wz 0) :: C4 (wz 0) :: post).
Proof.
intros m X pre post H. eapply rw_cells_recell; [exact H| | |].
- apply cells_wf_app. pose proof (proj1 (proj1 H)) as WF. apply cells_wf_app in WF. destruct WF as [W1 W2].
split; [exact W1|]. cbn in W2 |- *. tauto.
- rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite le8_zero_split. rewrite <- app_assoc. reflexivity.
- rewrite !cells_size_app. reflexivity.
Qed.

Lemma le8_split_u32 : forall v, 0 <= v < 2^32 -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
intros v Hv. unfold le8, le4, RiscvSemantics.word_to_le_bytes. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite !Z.mod_small by lia. cbn [Z_to_le_bytes app].
rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add].
rewrite !Z.shiftr_0_l.
rewrite (Z.shiftr_eq_0 v 32), (Z.shiftr_eq_0 v 40), (Z.shiftr_eq_0 v 48), (Z.shiftr_eq_0 v 56); try lia; try reflexivity.
all: destruct (Z.eq_dec v 0) as [->|]; [cbn; lia|]; apply Z.log2_lt_pow2; lia.
Qed.

Lemma nth_upd_bytes_in : forall (l xs : list byte) i n d, (i <= n < i + length xs)%nat -> (i + length xs <= length l)%nat ->
nth n (upd_bytes l i xs) d = nth (n - i) xs d.
Proof.
intros l xs i n d Hn Hl. unfold upd_bytes.
rewrite app_nth2 by (rewrite firstn_length_le; lia). rewrite firstn_length_le by lia.
rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma upd_bytes_self : forall (l : list byte) i n, (i + n <= length l)%nat -> upd_bytes l i (firstn n (skipn i l)) = l.
Proof.
intros l i n H. unfold upd_bytes. rewrite firstn_length_le by (rewrite skipn_length; lia).
transitivity (firstn i l ++ firstn n (skipn i l) ++ skipn n (skipn i l)).
- f_equal. f_equal. rewrite skipn_skipn. f_equal. lia.
- rewrite firstn_skipn. apply firstn_skipn.
Qed.

Lemma swrap32_word_inj : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 ->
Z_to_bv 64 (bv_swrap 32 x) = Z_to_bv 64 (bv_swrap 32 y) -> x = y.
Proof.
intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
unfold bv_wrap in E. change (bv_modulus 64) with (2^64) in E.
apply (bits_inj_upto 32); [lia| exact Hx| exact Hy|]. intros i Hi.
apply (f_equal (fun z => Z.testbit z i)) in E. cbv beta in E.
rewrite !testbit_mod64 in E by lia. rewrite !testbit_swrap32 in E by lia.
destruct (Z.ltb_spec i 32); [exact E| lia].
Qed.

Lemma ogg_page_checksum_zero4 : forall (h : list byte) body, (26 <= length h)%nat ->
ogg_page_checksum (ubytes (upd_bytes h 22 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0])) body = ogg_page_checksum (ubytes h) body.
Proof.
intros h body Hl. unfold ogg_page_checksum. rewrite ubytes_zero4 by lia.
set (U := ubytes h). assert (LU : (26 <= length U)%nat) by (subst U; rewrite ubytes_length; lia).
assert (L22 : length (firstn 22 U) = 22%nat) by (rewrite firstn_length_le; lia).
unfold ztake, zdrop. change (Z.to_nat 22) with 22%nat. change (Z.to_nat 26) with 26%nat.
rewrite firstn_app, L22, firstn_firstn, Nat.min_id, Nat.sub_diag, firstn_O, app_nil_r.
rewrite skipn_app, L22, (skipn_all2 (firstn 22 U)) by lia. cbn [app Nat.sub].
change (skipn 4 ([0; 0; 0; 0] ++ skipn 26 U)) with (skipn 26 U). reflexivity.
Qed.

Lemma Z_to_bv8_unsigned : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma testbit_small_signed_hi8 : forall y i, -2^7 <= y < 2^7 -> 7 <= i -> Z.testbit y i = Z.testbit y 7.
Proof.
intros y i Hy Hi.
destruct (Z.lt_ge_cases y 0).
- assert (T : forall j, 7 <= j -> Z.testbit y j = true).
{ intros j Hj. apply Z.testbit_true; [lia|].
assert (H0 : y / 2^j = -1).
{ symmetry. apply Z.div_unique with (r := y + 2^j); [| lia].
left. assert (2^7 <= 2^j) by (apply Z.pow_le_mono_r; lia). lia. }
rewrite H0. reflexivity. }
rewrite !T by lia. reflexivity.
- rewrite !(Z.bits_above_log2 y) ; try lia.
+ destruct (Z.eq_dec y 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 7; [apply Z.log2_lt_pow2; lia| lia].
+ destruct (Z.eq_dec y 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 7; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma testbit_sxb8 : forall q i, 0 <= q < 256 -> 0 <= i < 64 ->
Z.testbit (bv_unsigned (sxb (Z_to_bv 8 q))) i = if i <? 8 then Z.testbit q i else Z.testbit q 7.
Proof.
intros q i Hq Hi. unfold sxb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite testbit_mod64 by lia.
unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with (2^7). change (bv_modulus 8) with (2^8).
rewrite (Z.mod_small q) by lia.
set (y := (q + 2^7) mod 2^8 - 2^7).
assert (Hy : -2^7 <= y < 2^7) by (subst y; pose proof (Z.mod_pos_bound (q + 2^7) (2^8) ltac:(lia)); lia).
assert (E : y mod 2^8 = q mod 2^8).
{ subst y. rewrite Zminus_mod_idemp_l. replace (q + 2^7 - 2^7) with q by lia. reflexivity. }
destruct (Z.ltb_spec i 8).
- rewrite <- (Z.mod_pow2_bits_low y 8 i), <- (Z.mod_pow2_bits_low q 8 i) by lia. rewrite E. reflexivity.
- rewrite (testbit_small_signed_hi8 y i) by lia.
rewrite <- (Z.mod_pow2_bits_low y 8 7), <- (Z.mod_pow2_bits_low q 8 7) by lia. rewrite E. reflexivity.
Qed.

Lemma unsigned_b8 : forall q, 0 <= q < 256 -> bv_unsigned (Z_to_bv 8 q) = q.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Ltac tb1x := first [ progress (rewrite testbit_sxb8 by tb_lia)
| match goal with |- context [?i <? ?j] => is_lit i; is_lit j; let v := eval vm_compute in (i <? j) in change (i <? j) with v; cbv iota end
| tb1 ].
Ltac tbx := repeat tb1x; unfold tbit.
Ltac word_bitsx :=
unfold wz; apply word_eq_bits64;
let l := eval vm_compute in (zseq 64) in change (zseq 64) with l;
repeat (apply Forall_cons; [tbx; tb_close|]); try apply Forall_nil.

Section Chk.
Context {RCEIL : RunCeiling}.
Variables c0 c1 c2 c3 q0 q1 q2 q3 : Z.
Hypothesis Hc0 : 0 <= c0 < 256. Hypothesis Hc1 : 0 <= c1 < 256. Hypothesis Hc2 : 0 <= c2 < 256. Hypothesis Hc3 : 0 <= c3 < 256.
Hypothesis Hq0 : 0 <= q0 < 256. Hypothesis Hq1 : 0 <= q1 < 256. Hypothesis Hq2 : 0 <= q2 < 256. Hypothesis Hq3 : 0 <= q3 < 256.
Definition chkword := Z.lor (Z.lor (Z.shiftl c3 24) (Z.shiftl c2 16)) (Z.lor (Z.shiftl c1 8) c0).

#[using="Hc0 Hc1 Hc2 Hc3"] Lemma chk_saved : sx32 (Z_to_bv 64 chkword) = Z_to_bv 64 (bv_swrap 32 (c0 + 256 * (c1 + 256 * (c2 + 256 * c3)))).
Proof.
unfold sx32, chkword. rewrite Z_to_bv_unsigned. unfold bv_wrap at 1. change (bv_modulus 64) with (2^64). word_bitsx.
Qed.

#[using="Hq0 Hq1 Hq2 Hq3"] Lemma chk_recomputed :
Z_to_bv 64 (Z.lor (Z.lor (Z.land (Z.shiftl (bv_unsigned (sxb (Z_to_bv 8 q3))) 24) 18446744073709551615)
(Z.land (Z.shiftl (bv_unsigned (Z_to_bv 8 q2)) 16) 18446744073709551615))
(Z.lor (Z.land (Z.shiftl (bv_unsigned (Z_to_bv 8 q1)) 8) 18446744073709551615) (bv_unsigned (Z_to_bv 8 q0))))
= Z_to_bv 64 (bv_swrap 32 (q0 + 256 * (q1 + 256 * (q2 + 256 * q3)))).
Proof. rewrite !unsigned_b8 by lia. word_bitsx. Qed.

#[using="Hc0 Hc1 Hc2 Hc3 Hq0 Hq1 Hq2 Hq3"] Lemma chk_compare : sx32 (Z_to_bv 64 chkword) =
Z_to_bv 64 (Z.lor (Z.lor (Z.land (Z.shiftl (bv_unsigned (sxb (Z_to_bv 8 q3))) 24) 18446744073709551615)
(Z.land (Z.shiftl (bv_unsigned (Z_to_bv 8 q2)) 16) 18446744073709551615))
(Z.lor (Z.land (Z.shiftl (bv_unsigned (Z_to_bv 8 q1)) 8) 18446744073709551615) (bv_unsigned (Z_to_bv 8 q0))))
<-> [c0; c1; c2; c3] = [q0; q1; q2; q3].
Proof.
rewrite chk_saved, chk_recomputed. split.
- intros E. apply swrap32_word_inj in E; [|lia|lia]. f_equal; [lia|]. f_equal; [lia|]. f_equal; [lia|]. f_equal. lia.
- intros E. injection E as -> -> -> ->. reflexivity.
Qed.

#[using="Hc0"] Lemma chk_b0 : le1 (Z_to_bv 64 chkword) = [Z_to_bv 8 c0].
Proof. unfold chkword. le1_by_bits. Qed.
#[using="Hc0 Hc1"] Lemma chk_b1 : le1 (Z_to_bv 64 (Z.shiftr chkword 8)) = [Z_to_bv 8 c1].
Proof. unfold chkword. le1_by_bits. Qed.
#[using="Hc0 Hc1 Hc2"] Lemma chk_b2 : le1 (Z_to_bv 64 (Z.shiftr chkword 16)) = [Z_to_bv 8 c2].
Proof. unfold chkword. le1_by_bits. Qed.
#[using="Hc0 Hc1 Hc2 Hc3"] Lemma chk_b3 : le1 (Z_to_bv 64 (Z.shiftr chkword 24)) = [Z_to_bv 8 c3].
Proof. unfold chkword. le1_by_bits. Qed.
End Chk.

Lemma oggs_compare : forall b0 b1 b2 b3 : byte,
bv_eqb (n:=64) (Z_to_bv 64 (Z.lor (Z.lor (Z.land (Z.shiftl (bv_unsigned (sxb b3)) 24) 18446744073709551615)
(Z.land (Z.shiftl (bv_unsigned b2) 16) 18446744073709551615))
(Z.lor (Z.land (Z.shiftl (bv_unsigned b1) 8) 18446744073709551615) (bv_unsigned b0))))
(Z_to_bv 64 1399285583) = true
<-> [bv_unsigned b0; bv_unsigned b1; bv_unsigned b2; bv_unsigned b3] = OGGS_MAGIC.
Proof.
intros b0 b1 b2 b3. rewrite <- (Z_to_bv8_unsigned b3) at 1.
pose proof (byte_range b0) as H0. pose proof (byte_range b1) as H1. pose proof (byte_range b2) as H2. pose proof (byte_range b3) as H3.
set (u0 := bv_unsigned b0) in *. set (u1 := bv_unsigned b1) in *. set (u2 := bv_unsigned b2) in *. set (u3 := bv_unsigned b3) in *.
clearbody u0 u1 u2 u3.
assert (W : Z_to_bv 64 (Z.lor (Z.lor (Z.land (Z.shiftl (bv_unsigned (sxb (Z_to_bv 8 u3))) 24) 18446744073709551615)
(Z.land (Z.shiftl u2 16) 18446744073709551615))
(Z.lor (Z.land (Z.shiftl u1 8) 18446744073709551615) u0))
= Z_to_bv 64 (bv_swrap 32 (u0 + 256 * (u1 + 256 * (u2 + 256 * u3))))) by word_bitsx.
rewrite W. change (Z_to_bv 64 1399285583) with (Z_to_bv 64 (bv_swrap 32 (79 + 256 * (103 + 256 * (103 + 256 * 83))))).
rewrite bv_eqb_eq. unfold OGGS_MAGIC. split.
- intros E. apply swrap32_word_inj in E; [|lia|lia]. f_equal; [lia|]. f_equal; [lia|]. f_equal; [lia|]. f_equal. lia.
- intros E. injection E as -> -> -> ->. reflexivity.
Qed.

Lemma checksum_model : forall buf bytes ret hb bb,
buf_pre buf bytes -> 0 <= ret -> 27 <= hb -> 0 <= bb -> (Z.to_nat ret + Z.to_nat hb + Z.to_nat bb <= length buf)%nat ->
ogg_page_checksum (zslice ret hb buf) (zslice (ret + hb) bb buf) =
ogg_page_checksum (ubytes (firstn (Z.to_nat hb) (skipn (Z.to_nat ret) (upd_bytes bytes (Z.to_nat (ret + 22)) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]))))
(ubytes (firstn (Z.to_nat bb) (skipn (Z.to_nat (ret + hb)) (upd_bytes bytes (Z.to_nat (ret + 22)) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0])))).
Proof.
intros buf bytes ret hb bb PRE Hr Hh Hb Hl. pose proof PRE as [_ LE].
rewrite (pre_zslice buf bytes ret hb PRE), (pre_zslice buf bytes (ret + hb) bb PRE) by lia.
replace (Z.to_nat (ret + 22)) with (Z.to_nat ret + 22)%nat by lia.
rewrite slice_upd_bytes_in by (cbn [length]; lia).
replace (Z.to_nat (ret + hb)) with (Z.to_nat ret + Z.to_nat hb)%nat by lia.
rewrite slice_upd_bytes_out by (cbn [length]; lia).
rewrite ogg_page_checksum_zero4 by (rewrite firstn_length_le by (rewrite skipn_length; lia); lia).
match goal with |- ?a = ?a => reflexivity end.
Qed.

Definition og_cells (D : Z) (ogo : option page) (ogc : list cell) : list cell :=
match ogo with Some og => page_cells D og | None => ogc end.

Definition pageseek_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A G D lo : Z) (bytes : list byte) (ogc : list cell) (m : mem)
(r : Z) (ogo : option page) (sy' : sync_st bptr) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' A (sync_cells D sy') /\ sync_fields_ok sy'
/\ u8arr rsegs m' D bytes
/\ rw_cells rsegs m' G (og_cells D ogo ogc).

Lemma zsum_bytes_le : forall l, bytes_ok l -> 0 <= zsum l <= 255 * zlength l.
Proof.
induction l as [|x l IH]; intros H; [rewrite zlength_nil; cbn; lia|].
inversion H; subst. cbn [zsum]. rewrite zlength_cons. specialize (IH ltac:(assumption)). lia.
Qed.

