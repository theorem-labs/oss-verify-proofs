(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bk X1cf.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fd.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Definition rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition memmove_entry := 0x3a060.

Definition mv (buf : list byte) (off i : nat) : list byte := firstn i (skipn off buf) ++ skipn i buf.

Lemma mv_0 : forall buf off, mv buf off 0 = buf.
Proof. intros. reflexivity. Qed.

Lemma mv_length : forall buf off i, (off + i <= length buf)%nat -> length (mv buf off i) = length buf.
Proof. intros. unfold mv. rewrite app_length, firstn_length_le, skipn_length by (rewrite skipn_length; lia). lia. Qed.

Lemma mv_skipn : forall buf off i j, (off + i <= length buf)%nat -> (i <= j)%nat -> skipn j (mv buf off i) = skipn j buf.
Proof.
intros buf off i j Hl Hij. unfold mv.
rewrite skipn_app, firstn_length_le by (rewrite skipn_length; lia).
rewrite skipn_all2 by (rewrite firstn_length_le by (rewrite skipn_length; lia); lia). cbn [app].
rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma mv_read : forall buf off i k, (off + i + k <= length buf)%nat ->
firstn k (skipn (off + i) (mv buf off i)) = firstn k (skipn (off + i) buf).
Proof. intros. rewrite mv_skipn by lia. reflexivity. Qed.

Lemma mv_write : forall buf off i k, (off + i + k <= length buf)%nat ->
upd_bytes (mv buf off i) i (firstn k (skipn (off + i) buf)) = mv buf off (i + k).
Proof.
intros buf off i k Hl. unfold upd_bytes.
rewrite firstn_length_le by (rewrite skipn_length; lia).
rewrite (mv_skipn buf off i (i + k)) by lia.
unfold mv. rewrite firstn_app, firstn_firstn, Nat.min_id.
rewrite (firstn_length_le (skipn off buf)) by (rewrite skipn_length; lia). rewrite Nat.sub_diag, firstn_O, app_nil_r.
rewrite app_assoc. f_equal.
rewrite <- (firstn_skipn i (firstn (i + k) (skipn off buf))).
rewrite firstn_firstn. replace (Nat.min i (i + k)) with i by lia. f_equal.
rewrite skipn_firstn_comm, skipn_skipn. replace (i + k - i)%nat with k by lia. f_equal. f_equal. lia.
Qed.

Lemma mv_done : forall buf off n, mv buf off n = firstn n (skipn off buf) ++ skipn n buf.
Proof. intros. reflexivity. Qed.

Lemma mv_off0 : forall buf i, mv buf 0 i = buf.
Proof. intros. unfold mv. cbn [skipn]. apply firstn_skipn. Qed.

Lemma bytes_at_sub : forall m A bs (i k : nat), bytes_at rsegs m A bs -> (i + k <= length bs)%nat ->
bytes_at rsegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
intros m A bs i k HB Hik.
rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
rewrite firstn_length_le in HB by lia.
rewrite <- (firstn_skipn k (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma u8arr_read_n : forall m A bs (i : Z) (k : nat) a,
u8arr rsegs m A bs -> 0 <= i -> (Z.to_nat i + k <= length bs)%nat -> a = wa (A + i) ->
ov_read_bytes rsegs m a k = Some (firstn k (skipn (Z.to_nat i) bs)).
Proof. intros m A bs i k a [HB _] Hi Hk ->. apply bytes_at_read; assumption. Qed.

Lemma u8arr_store_ok_n : forall m A bs (i : Z) (k : nat) a,
u8arr rsegs m A bs -> 0 <= i -> (Z.to_nat i + k <= length bs)%nat -> a = wa (A + i) ->
store_ok rsegs m a k = true.
Proof. intros m A bs i k a [_ HW] Hi Hk ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma u8arr_write_n : forall m A bs (i : Z) (xs : list byte),
u8arr rsegs m A bs -> 0 <= i -> (Z.to_nat i + length xs <= length bs)%nat ->
u8arr rsegs (write_to_mem m (wa (A + i)) xs) A (upd_bytes bs (Z.to_nat i) xs).
Proof.
intros m A bs i xs [HB HW] Hi Hl. split.
- apply bytes_at_write_inside; assumption.
- rewrite upd_bytes_length by lia. apply wr_at_write. exact HW.
Qed.

Lemma firstn1_nth : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
intros l k d Hk. revert l Hk. induction k as [|k IH]; intros [|x l] Hk; cbn in Hk |- *; try lia; [reflexivity|].
apply IH. lia.
Qed.

Lemma u8arr_app : forall m A l1 l2, u8arr rsegs m A (l1 ++ l2) <-> u8arr rsegs m A l1 /\ u8arr rsegs m (A + Z.of_nat (length l1)) l2.
Proof.
intros m A l1 l2. unfold u8arr. rewrite bytes_at_app, app_length. unfold wr_at. split.
- intros [[B1 B2] (W0 & W1 & W)]. pose proof (bytes_at_bound _ _ _ _ B1). pose proof (bytes_at_bound _ _ _ _ B2).
split; (split; [assumption|]); (split; [lia|]); (split; [lia|]).
+ intros i Hi. apply W. lia.
+ intros i Hi. replace (A + Z.of_nat (length l1) + i) with (A + (Z.of_nat (length l1) + i)) by lia. apply W. lia.
- intros [[B1 (W0 & W1 & W)] [B2 (V0 & V1 & V)]]. split; [split; assumption|]. split; [lia|]. split; [lia|].
intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (length l1))); [apply W; lia|].
replace (A + i) with (A + Z.of_nat (length l1) + (i - Z.of_nat (length l1))) by lia. apply V. lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8).
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8).
+ rewrite Z.mod_pow2_bits_low, Z.lor_spec, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
+ rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (testbit_high_false _ 8); lia.
- replace (Z.lor (bv_unsigned b) (bytes_le_to_Z bs ≪ 8) ≫ 8) with (bytes_le_to_Z bs); [exact IH|].
rewrite Z.shiftr_lor, Z.shiftr_shiftl_l by lia. cbn [Z.sub Z.pos_sub]. rewrite Z.shiftl_0_r.
rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.

Lemma bytes_le_to_Z_bound8 : forall bs : list byte, length bs = 8%nat -> 0 <= bytes_le_to_Z bs < 2^64.
Proof.
intros bs Hl. pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs) as X. rewrite Hl in X.
cbn [Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in X. lia.
Qed.

Lemma le8_le_bytes_to_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite unsigned_lit by (apply bytes_le_to_Z_bound8; exact Hl).
rewrite <- Hl. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma le8_extract_le_bytes_to_word : forall bs : list byte, length bs = 8%nat -> le8 (bv_extract 0 64 (le_bytes_to_word bs)) = bs.
Proof.
intros bs Hl. unfold le8, word_to_le_bytes. rewrite bv_extract_unsigned, Z.shiftr_0_r.
unfold le_bytes_to_word. rewrite !Z_to_bv_unsigned.
pose proof (bytes_le_to_Z_bound8 bs Hl).
rewrite !bv_wrap_small by (unfold bv_modulus; rewrite ?bv_wrap_small by (unfold bv_modulus; lia); lia).
rewrite <- Hl. apply Z_to_le_bytes_of_bytes.
Qed.

Definition memmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 : word) (D off n : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(D, D + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ u8arr rsegs m' D (firstn (Z.to_nat n) (skipn (Z.to_nat off) buf) ++ skipn (Z.to_nat n) buf).

Section MM.
Context {RCEIL : RunCeiling}.
Variables (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (D off n : Z) (buf : list byte).
Hypothesis Ha0 : a0 = Z_to_bv 64 D.
Hypothesis Hoff : 0 <= off.
Hypothesis Hn : 0 <= n.
Hypothesis LEN : off + n <= Z.of_nat (length buf).
Hypothesis TOP : D + Z.of_nat (length buf) < 2^63.
Hypothesis ARR0 : u8arr rsegs m D buf.
Hypothesis MI0 : mem_inv rsegs m.

Notation S := (D + off).
Notation W := [(D, D + n)].
Notation POST := (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 D off n buf m).

Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 D) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Definition INV (m1 : word -> option byte) (i : Z) : Prop :=
u8arr rsegs m1 D (mv buf (Z.to_nat off) (Z.to_nat i)) /\ mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1.

#[using="ARR0 MI0"] Lemma inv_start : INV m 0.
Proof. split; [rewrite mv_0; exact ARR0|]. split; [exact MI0|]. split; [apply munch_refl| apply wmono_refl]. Qed.

#[using="Ha0"] Lemma fin : forall m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
INV m1 n -> evt rsegs POST (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 D) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m1 (seg_rom rsegs)).
Proof.
intros until x31. intros sfH_; first [ sf_destruct 4%nat sfH_ as ARR MI MU WM | sf_fb; destruct sfH_ as (ARR & MI & MU & WM) ]. apply evt_done. unfold memmove_post. rewrite Ha0.
sf_eexists 15%nat. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ARR.
Qed.

#[using="Ha0 Hoff LEN TOP ARR0"] Lemma loopA : forall (k : nat) (i : Z) m1 x5 x6 x7 x11 xa3 xa4 x15 x16 x17 x28 x29 x30 x31,
Z.to_nat (n - i) = k -> 0 <= i < n -> INV m1 i ->
xa3 = Z_to_bv 64 (D + i) -> xa4 = Z_to_bv 64 (S + i) ->
evt rsegs POST (ST 0x3a098 m1 x5 x6 x7 x11 (Z_to_bv 64 (D + n)) xa3 xa4 x15 x16 x17 x28 x29 x30 x31).
Proof.
induction k as [|k IH]; intros i m1 x5 x6 x7 x11 xa3 xa4 x15 x16 x17 x28 x29 x30 x31 Hk Hi sfH_; first [ sf_destruct 4%nat sfH_ as ARR MI MU WM | sf_fb; destruct sfH_ as (ARR & MI & MU & WM) ]; intros -> ->; [lia|].
pose proof (u8arr_bound rsegs m D buf ARR0) as AB0.
pose proof (mv_length buf (Z.to_nat off) (Z.to_nat i) ltac:(lia)) as ML.
pose proof (u8arr_read_n m1 D _ (off + i) 1 _ ARR ltac:(lia) ltac:(rewrite ML; lia) eq_refl) as RD.
replace (Z.to_nat (off + i)) with (Z.to_nat off + Z.to_nat i)%nat in RD by lia.
rewrite (mv_read buf (Z.to_nat off) (Z.to_nat i) 1) in RD by lia.
replace (wa (D + (off + i))) with (wa (D + off + i)) in RD by (f_equal; lia).
rewrite (firstn1_nth buf _ (Z_to_bv 8 0)) in RD by lia.
set (b := nth (Z.to_nat off + Z.to_nat i) buf (Z_to_bv 8 0)) in RD.

zstep. zstep. zstep.
pose proof (u8arr_store_ok_n m1 D _ i 1 (wa (D + i)) ARR ltac:(lia) ltac:(rewrite ML; lia) eq_refl) as SOK.
zstep.
change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
change (Z_to_bv 64 (D + i)) with (wa (D + i)) at 2.
pose proof (u8arr_write_n m1 D _ i [b] ARR ltac:(lia) ltac:(cbn [length]; rewrite ML; lia)) as ARR2.
assert (EQ : upd_bytes (mv buf (Z.to_nat off) (Z.to_nat i)) (Z.to_nat i) [b] = mv buf (Z.to_nat off) (Z.to_nat (i + 1))).
{ unfold b. rewrite <- (firstn1_nth buf (Z.to_nat off + Z.to_nat i) (Z_to_bv 8 0)) by lia.
rewrite (mv_write buf (Z.to_nat off) (Z.to_nat i) 1) by lia. f_equal. lia. }
rewrite EQ in ARR2. clear EQ ARR ML. store_done. rename ARR2 into ARR.

zstep. zstep. if_cases K; zify_cond K; rewrite ?land_ones64, ?Z.mod_small in K by lia.
- eapply (IH (i + 1)); [lia| lia| | f_equal; lia| f_equal; lia]. split; [exact ARR|]. split; [assumption|]. split; assumption.
-
zstep. zstep. apply fin. replace n with (i + 1) by lia. split; [exact ARR|]. split; [assumption|]. split; assumption.
Qed.

Ltac inv_split := split; [eassumption|]; split; [assumption|]; split; assumption.

#[using="Ha0 Hoff LEN TOP ARR0"] Lemma loopA_entry : forall (i : Z) m1 x5 x6 x7 x11 xa2 xa3 xa4 x15 x16 x17 x28 x29 x30 x31,
0 <= i <= n -> INV m1 i ->
xa2 = Z_to_bv 64 (n - i) -> xa3 = Z_to_bv 64 (D + i) -> xa4 = Z_to_bv 64 (S + i) ->
evt rsegs POST (ST 0x3a090 m1 x5 x6 x7 x11 xa2 xa3 xa4 x15 x16 x17 x28 x29 x30 x31).
Proof.
intros i m1 x5 x6 x7 x11 xa2 xa3 xa4 x15 x16 x17 x28 x29 x30 x31 Hi sfH_; first [ sf_destruct 4%nat sfH_ as ARR MI MU WM | sf_fb; destruct sfH_ as (ARR & MI & MU & WM) ]; intros -> -> ->.
pose proof (u8arr_bound rsegs m D buf ARR0) as AB0.
zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in K by lia.
-   zstep. apply fin. replace n with i by lia. inv_split.
- zstep. replace (D + i + (n - i)) with (D + n) by lia.
eapply (loopA (Z.to_nat (n - i)) i); [lia| lia| inv_split| reflexivity| reflexivity].
Qed.

#[using="Ha0 Hoff LEN TOP ARR0"] Lemma loopC : forall (k : nat) (i : Z) m1 x5 x6 x7 xa2 xa3 xa4 x15 x16 x17 x28 x29 x30 x31,
(Z.to_nat (n - i) <= 8 * k)%nat -> 0 <= i -> 8 <= n - i -> INV m1 i ->
xa2 = Z_to_bv 64 (n - i) -> xa3 = Z_to_bv 64 (D + i) -> xa4 = Z_to_bv 64 (S + i) ->
evt rsegs POST (ST 0x3a1c0 m1 x5 x6 x7 (Z_to_bv 64 7) xa2 xa3 xa4 x15 x16 x17 x28 x29 x30 x31).
Proof.
induction k as [|k IH]; intros i m1 x5 x6 x7 xa2 xa3 xa4 x15 x16 x17 x28 x29 x30 x31 Hk Hi Hrem sfH_; first [ sf_destruct 4%nat sfH_ as ARR MI MU WM | sf_fb; destruct sfH_ as (ARR & MI & MU & WM) ]; intros -> -> ->; [lia|].
pose proof (u8arr_bound rsegs m D buf ARR0) as AB0.
pose proof (mv_length buf (Z.to_nat off) (Z.to_nat i) ltac:(lia)) as ML.
pose proof (u8arr_read_n m1 D _ (off + i) 8 _ ARR ltac:(lia) ltac:(rewrite ML; lia) eq_refl) as RD.
replace (Z.to_nat (off + i)) with (Z.to_nat off + Z.to_nat i)%nat in RD by lia.
rewrite (mv_read buf (Z.to_nat off) (Z.to_nat i) 8) in RD by lia.
replace (wa (D + (off + i))) with (wa (D + off + i)) in RD by (f_equal; lia).
set (bs8 := firstn 8 (skipn (Z.to_nat off + Z.to_nat i) buf)) in RD.
assert (L8 : length bs8 = 8%nat) by (subst bs8; rewrite firstn_length_le by (rewrite skipn_length; lia); reflexivity).

zstep. zstep.
pose proof (u8arr_store_ok_n m1 D _ i 8 (wa (D + i)) ARR ltac:(lia) ltac:(rewrite ML; lia) eq_refl) as SOK.
zstep.
rewrite (le8_extract_le_bytes_to_word bs8 L8).
change (Z_to_bv 64 (D + i)) with (wa (D + i)) at 2.
pose proof (u8arr_write_n m1 D _ i bs8 ARR ltac:(lia) ltac:(rewrite L8, ML; lia)) as ARR2.
assert (EQ : upd_bytes (mv buf (Z.to_nat off) (Z.to_nat i)) (Z.to_nat i) bs8 = mv buf (Z.to_nat off) (Z.to_nat (i + 8))).
{ unfold bs8. rewrite (mv_write buf (Z.to_nat off) (Z.to_nat i) 8) by lia. f_equal. lia. }
rewrite EQ in ARR2. clear EQ ARR ML.
apply (mem_inv_store rsegs m1 (wa (D + i)) bs8) in MI; [| rewrite L8; exact SOK].
store_done. rename ARR2 into ARR.

zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in K by lia.
- eapply (IH (i + 8)); [lia| lia| lia| inv_split| f_equal; lia| f_equal; lia| f_equal; lia].
-
zstep. eapply (loopA_entry (i + 8)); [lia| inv_split| f_equal; lia| f_equal; lia| f_equal; lia].
Qed.

#[using="Ha0 Hoff LEN TOP ARR0"] Lemma entry40 : forall (i : Z) m1 x5 x6 x7 x11 xa2 xa3 xa4 x15 x16 x17 x28 x29 x30 x31,
0 <= i <= n -> INV m1 i ->
xa2 = Z_to_bv 64 (n - i) -> xa3 = Z_to_bv 64 (D + i) -> xa4 = Z_to_bv 64 (S + i) ->
evt rsegs POST (ST 0x3a1b4 m1 x5 x6 x7 x11 xa2 xa3 xa4 x15 x16 x17 x28 x29 x30 x31).
Proof.
intros i m1 x5 x6 x7 x11 xa2 xa3 xa4 x15 x16 x17 x28 x29 x30 x31 Hi HINV -> -> ->.
pose proof HINV as sfP_; first [ sf_destruct 4%nat sfP_ as ARR MI MU WM | sf_fb; destruct sfP_ as (ARR & MI & MU & WM) ].
pose proof (u8arr_bound rsegs m D buf ARR0) as AB0.
zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in K by lia.
- eapply (loopA_entry i); [lia| exact HINV| reflexivity| reflexivity| reflexivity].
- zstep. eapply (loopC (Z.to_nat (n - i)) i); [lia| lia| lia| exact HINV| reflexivity| reflexivity| reflexivity].
Qed.

#[using="Ha0 Hoff LEN TOP ARR0"] Lemma loopB : forall (k : nat) (i : Z) m1 x5 x6 x7 xa1 xa2 x13 x14 xa5 xa6 x17 x28 x29 x30 x31,
Z.to_nat (n - i) = k -> 0 <= i <= n -> INV m1 i ->
xa1 = Z_to_bv 64 (S + i) -> xa2 = Z_to_bv 64 (n - i) -> xa5 = Z_to_bv 64 (D + i + 1) -> xa6 = Z_to_bv 64 (D + i) ->
evt rsegs POST (ST 0x3a100 m1 x5 x6 x7 xa1 xa2 x13 x14 xa5 xa6 x17 x28 x29 x30 x31).
Proof.
induction k as [|k IH]; intros i m1 x5 x6 x7 xa1 xa2 x13 x14 xa5 xa6 x17 x28 x29 x30 x31 Hk Hi sfH_; first [ sf_destruct 4%nat sfH_ as ARR MI MU WM | sf_fb; destruct sfH_ as (ARR & MI & MU & WM) ]; intros -> -> -> ->.
- pose proof (u8arr_bound rsegs m D buf ARR0) as AB0.
zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in K by lia; [| exfalso; lia].
zstep. apply fin. replace n with i by lia. inv_split.
- pose proof (u8arr_bound rsegs m D buf ARR0) as AB0.
zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in K by lia.
{ zstep. apply fin. replace n with i by lia. inv_split. }
pose proof (mv_length buf (Z.to_nat off) (Z.to_nat i) ltac:(lia)) as ML.
pose proof (u8arr_read_n m1 D _ (off + i) 1 _ ARR ltac:(lia) ltac:(rewrite ML; lia) eq_refl) as RD.
replace (Z.to_nat (off + i)) with (Z.to_nat off + Z.to_nat i)%nat in RD by lia.
rewrite (mv_read buf (Z.to_nat off) (Z.to_nat i) 1) in RD by lia.
replace (wa (D + (off + i))) with (wa (D + off + i)) in RD by (f_equal; lia).
rewrite (firstn1_nth buf _ (Z_to_bv 8 0)) in RD by lia.
set (b := nth (Z.to_nat off + Z.to_nat i) buf (Z_to_bv 8 0)) in RD.

zstep. zstep. zstep. zstep. zstep.
pose proof (u8arr_store_ok_n m1 D _ i 1 (wa (D + i)) ARR ltac:(lia) ltac:(rewrite ML; lia) eq_refl) as SOK.
zstep.
change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
change (Z_to_bv 64 (D + i)) with (wa (D + i)) at 2.
pose proof (u8arr_write_n m1 D _ i [b] ARR ltac:(lia) ltac:(cbn [length]; rewrite ML; lia)) as ARR2.
assert (EQ : upd_bytes (mv buf (Z.to_nat off) (Z.to_nat i)) (Z.to_nat i) [b] = mv buf (Z.to_nat off) (Z.to_nat (i + 1))).
{ unfold b. rewrite <- (firstn1_nth buf (Z.to_nat off + Z.to_nat i) (Z_to_bv 8 0)) by lia.
rewrite (mv_write buf (Z.to_nat off) (Z.to_nat i) 1) by lia. f_equal. lia. }
rewrite EQ in ARR2. clear EQ ARR ML. store_done. rename ARR2 into ARR.

zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
+ eapply (IH (i + 1)); [lia| lia| inv_split| f_equal; lia| f_equal; lia| f_equal; lia| f_equal; lia].
+
zstep. eapply (entry40 (i + 1)); [lia| inv_split| f_equal; lia| f_equal; lia| f_equal; lia].
Qed.

#[using="Ha0 Hoff Hn LEN TOP ARR0 MI0"] Lemma memmove_body :
a1 = Z_to_bv 64 (D + off) -> a2 = Z_to_bv 64 n ->
forall x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
evt rsegs POST (ST memmove_entry m x5 x6 x7 a1 a2 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
intros -> -> x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31. unfold memmove_entry.
pose proof (u8arr_bound rsegs m D buf ARR0) as AB0.
pose proof inv_start as HINV. pose proof HINV as sfP_; first [ sf_destruct 4%nat sfP_ as ARR MI MU WM | sf_fb; destruct sfP_ as (ARR & MI & MU & WM) ].

zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
{
zstep. apply fin. split; [| split; [exact MI| split; [exact MU| exact WM]]].
replace (Z.to_nat off) with 0%nat by lia. rewrite mv_off0. exact ARR0. }

zstep. zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
-
rewrite Z.shiftl_mul_pow2 in K1 by lia. change (2^1) with 2 in K1.
rewrite (Z.mod_small (n * 2)) in K1 by lia.
assert (Hn0 : 0 < n).
{ destruct (Z.eq_dec n 0) as [E|]; [| lia]. exfalso. rewrite E in K1. rewrite !Z.mod_small in K1 by lia. lia. }
replace ((0 - n * 2) mod 18446744073709551616) with (18446744073709551616 - n * 2) in K1
by (apply Z.mod_unique with (q := -1); lia).
assert (Hoffn : n <= off).
{ destruct (Z.lt_ge_cases off n); [| lia]. exfalso.
replace ((D + off - (n + D)) mod 18446744073709551616) with (18446744073709551616 + off - n) in K1
by (apply Z.mod_unique with (q := -1); lia). lia. }
zstep.

pose proof ARR0 as [HB0 HW0].
pose proof (bytes_at_sub m D buf (Z.to_nat off) (Z.to_nat n) HB0 ltac:(lia)) as SRC.
replace (D + Z.of_nat (Z.to_nat off)) with (D + off) in SRC by lia.
rewrite <- (firstn_skipn (Z.to_nat n) buf) in ARR0.
pose proof (proj1 (u8arr_app m D _ _) ARR0) as [DST REST]. rewrite firstn_skipn in ARR0.
rewrite firstn_length_le in REST by lia.
apply rw_cells_of_u8arr in DST. rewrite firstn_length_le in DST by lia.
eapply evt_mono.
{ eapply (memcpy_spec ra sp gp tp _ _ _ s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (D + off)) (Z_to_bv 64 n));
rewrite ?unsigned_lit by lia.
- exact SRC.
- rewrite firstn_length_le by (rewrite skipn_length; lia). reflexivity.
- exact DST.
- right. lia.
- exact MI0. }
cbv beta. intros ms' PO. first [ sf_destruct 21%nat PO as y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' -> MU' WM' MI' DST' SRC' | sf_fb; destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MU' & WM' & MI' & DST' & SRC') ].
rewrite !unsigned_lit in MU', DST' by lia.
unfold memmove_post. sf_eexists 15%nat. split; [rewrite Ha0; reflexivity|].
split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
apply (proj2 (u8arr_app m' D _ _)). split.
+ apply u8arr_of_rw_cells in DST'. exact DST'.
+ rewrite firstn_length_le by (rewrite skipn_length; lia).
eapply u8arr_transport; [exact REST| exact MU'| exact WM'|]. cbn. rewrite skipn_length. lia.
-
clear K1.

zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [exfalso; lia|].

zstep. if_cases K3; zify_cond K3.
+
zstep. zstep. if_cases K4; zify_cond K4.
*
zstep. zstep. eapply (entry40 0); [lia| exact HINV| f_equal; lia| f_equal; lia| f_equal; lia].
*
zstep. zstep. eapply (loopB (Z.to_nat n) 0); [lia| lia| exact HINV| f_equal; lia| f_equal; lia| f_equal; lia| f_equal; lia].
+
zstep. zstep. eapply (loopA_entry 0); [lia| exact HINV| f_equal; lia| f_equal; lia| f_equal; lia].
Qed.
End MM.

Lemma memmove_fwd_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D off n : Z) (buf : list byte),
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (D + off) -> a2 = Z_to_bv 64 n ->
0 <= off -> 0 <= n -> off + n <= Z.of_nat (length buf) -> D + Z.of_nat (length buf) < 2^63 ->
u8arr rsegs m D buf -> mem_inv rsegs m ->
evt rsegs (memmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 D off n buf m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 memmove_entry) fc None m (seg_rom rsegs)).
Proof.
intros until buf. intros Ha0 Ha1 Ha2 Hoff Hn LEN TOP ARR MI.
pose proof (memmove_body ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m D off n buf Ha0 Hoff Hn LEN TOP ARR MI Ha1 Ha2
t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6) as X.
rewrite <- Ha0 in X. exact X.
Qed.
