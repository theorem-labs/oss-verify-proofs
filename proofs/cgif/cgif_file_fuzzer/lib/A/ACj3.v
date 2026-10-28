(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5x YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac upd_aboveF HUP HFr AG ltac :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; ltac Hb Hrg|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma denot_atom_mod : forall E n v M, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
(bv_unsigned (Z_to_bv 64 (bv_unsigned (ew E n) + 0))) mod M = v mod M.
Proof. intros E n v M Hn Hv. rewrite Hn, Z.add_0_r, !unsigned_lit_small by (rewrite ?unsigned_lit_small by lia; lia). reflexivity. Qed.
Lemma val_mem_mod : forall segs (m : word -> option byte) a n v,
val_mem segs m a n (v mod 2 ^ (8 * Z.of_nat n)) <-> val_mem segs m a n v.
Proof.
intros segs m a n v. unfold val_mem, YO0f.le_byte.
assert (E : (v mod 2 ^ (8 * Z.of_nat n)) mod 2 ^ (8 * Z.of_nat n) = v mod 2 ^ (8 * Z.of_nat n)).
{ apply Z.mod_mod. apply Z.pow_nonzero; lia. }
rewrite E. tauto.
Qed.
Lemma low_byte_mod : forall u n k, 0 <= u -> (k < n)%nat ->
Z_to_bv 8 (Z.shiftr (u mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr u (8 * Z.of_nat k)).
Proof.
intros u n k Hu Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hl|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma val_of_chunk_any : forall segs E mem base off (n : N) (e : sv),
YP09.chunk_ok segs E mem base (YP09.mkChunk off (CVal n e)) -> (Z.of_N n <= 8) ->
val_mem segs mem (base + off) (N.to_nat n) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros segs E mem base off n e H Hn k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. unfold YP09.byte_of_word in Hb1.
injection Hb1 as <-. rewrite Hb2. f_equal.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hu. change (bv_modulus 64) with (2 ^ 64) in Hu.
set (u := bv_unsigned (sv_denot E e)) in *.
assert (Hm : 0 <= u mod 2 ^ (8 * Z.of_N n) < 2 ^ (8 * Z.of_nat (N.to_nat n))).
{ rewrite Hnn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
rewrite (le_byte_small _ _ _ Hm Hk). rewrite <- Hnn. symmetry. apply low_byte_mod; [lia | exact Hk].
Qed.
Lemma field_of_region_any : forall E m n b cs lo hi wlo whi od (w : N) e,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> (Z.of_N w <= 8) ->
val_mem SEGS m (b + od) (N.to_nat w) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E m n b cs lo hi wlo whi od w e (_ & _ & _ & Hcs) Hn Hc Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_any SEGS E m b od w e Hck Hw).
Qed.
Lemma val_mem_of_present4 : forall segs (m : word -> option byte) a,
(forall i, 0 <= i < 4 -> exists b, mbyte segs m (a + i) = Some b) ->
exists v, 0 <= v < 2 ^ 32 /\ val_mem segs m a 4 v.
Proof.
intros segs m a Hp.
destruct (Hp 0 ltac:(lia)) as [b0 M0]. destruct (Hp 1 ltac:(lia)) as [b1 M1].
destruct (Hp 2 ltac:(lia)) as [b2 M2]. destruct (Hp 3 ltac:(lia)) as [b3 M3].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in R0, R1, R2, R3. cbn [Z.of_N] in R0, R1, R2, R3. change (2 ^ 8) with 256 in R0, R1, R2, R3.
set (v := bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))).
exists v. split; [subst v; lia|].
assert (BY : forall (k : nat) (c : byte) (lo hi : Z),
v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
Z_to_bv 8 (YO0f.le_byte v 4 k) = c).
{ intros k c lo hi Hdec Hlo Hhi. unfold YO0f.le_byte. rewrite (Z.mod_small v) by (cbn; subst v; lia).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. change (2 ^ 8) with 256 in Hc.
replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
2:{ apply Z.div_unique with (r := lo); [left; lia | lia]. }
replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
2:{ apply Z.mod_unique with (q := hi); [left; lia | lia]. }
apply Z_to_bv_bv_unsigned. }
intros k Hk.
destruct k as [|[|[|[|k]]]]; [| | | |lia];
[ change (a + Z.of_nat 0) with (a + 0) | change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2 | change (Z.of_nat 3) with 3 ].
- rewrite M0. f_equal. symmetry. apply (BY 0%nat b0 0 (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))); cbn; subst v; lia.
- rewrite M1. f_equal. symmetry. apply (BY 1%nat b1 (bv_unsigned b0) (bv_unsigned b2 + 256 * bv_unsigned b3)); cbn; subst v; lia.
- rewrite M2. f_equal. symmetry. apply (BY 2%nat b2 (bv_unsigned b0 + 256 * bv_unsigned b1) (bv_unsigned b3)); cbn; subst v; lia.
- rewrite M3. f_equal. symmetry. apply (BY 3%nat b3 (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)) 0); cbn; subst v; lia.
Qed.
Lemma length_list_set' : forall {X} (l : list X) i x, length (list_set l i x) = length l.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x; cbn; [reflexivity | reflexivity | reflexivity | rewrite IH; reflexivity]. Qed.
Lemma obj_at_hole4 : forall (mem mem' : word -> option byte) a lay sz vals (j : nat) (off : Z),
obj_at SEGS mem a lay vals -> lay_inside lay sz = true -> nth_error lay j = Some (off, 4%N) ->
lay_upd_ok lay 0 [j] [(off, off + 4)] = true -> (j < length vals)%nat ->
(forall i, 0 <= i < sz -> ~ (off <= i < off + 4) -> mbyte SEGS mem' (a + i) = mbyte SEGS mem (a + i)) ->
(forall i, 0 <= i < 4 -> exists b, mbyte SEGS mem' (a + off + i) = Some b) ->
exists v, 0 <= v < 2 ^ 32 /\ obj_at SEGS mem' a lay (list_set vals j v).
Proof.
intros mem mem' a lay sz vals j off Hobj Hin Hj Hok Hlen Hkeep Hpres.
destruct (val_mem_of_present4 SEGS mem' (a + off) Hpres) as (v & Hv & Hvm).
exists v. split; [exact Hv|].
apply (obj_at_upd SEGS mem mem' a lay sz vals (list_set vals j v) [j] [(off, off + 4)] Hobj Hin Hok).
- apply length_list_set'.
- intros i Hi Hw. apply Hkeep; [exact Hi|]. unfold in_wins in Hw. cbn [existsb fst snd] in Hw.
intros Hc. destruct (Z.leb_spec off i); destruct (Z.ltb_spec i (off + 4)); cbn in Hw; try discriminate; lia.
- intros j' f v' Hj' Hf Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []].
rewrite Hj in Hf. injection Hf as <-. rewrite nth_error_list_set_same in Hv' by exact Hlen. injection Hv' as <-.
split; cbn [fst snd N.to_nat Z.of_N]; [exact Hvm | change (2 ^ (8 * 4)) with (2 ^ 32); exact Hv].
- intros j' Hj'. apply nth_error_list_set_other. intros ->. apply Hj'. left. reflexivity.
Qed.
Lemma zero_shadow_of_bytes : forall (rd : Z -> option Z) a len,
a mod 8 = 0 -> len mod 8 = 0 -> 0 <= len ->
(forall i, 0 <= i < len / 8 -> rd (SHADOW_OFF + a / 8 + i) = Some 0) ->
range_addressable rd SHADOW_OFF a len.
Proof.
intros rd a len Ha Hl Hlen Hz. apply zero_shadow_range; [exact Ha | exact Hl |].
intros i Hi. unfold shadow_of_addr. apply Hz. exact Hi.
Qed.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma region_kept_frame_sub : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= b + lo -> b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos HJ1 Hn Hin Hlo Hhi HnF Hp2.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply HnF; exact Ha].
- intros _. apply (apresent_writable SEGS). apply Hp2. lia.
Qed.
Lemma region_kept_fshadow_sub : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
shadow_addr (frame_addr lyc cid pos) <= b + lo -> b + hi <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n b lo hi wlo whi cs cid pos HJ1 Hn Hin Hlo Hhi HnF Hp2.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply (K4 cid pos a Hin); [right; unfold in_zr; cbn [fst snd]; lia | apply HnF; exact Ha].
- intros _. apply (apresent_writable SEGS). apply Hp2. lia.
Qed.
Lemma region_kept_block_subw : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs b m,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E n) = b -> In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) ->
0 <= lo -> hi <= req_size m ->
(forall a, b + lo <= a < b + hi -> ~ inFP FP1 a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 n lo hi wlo whi cs b m HJ1 Hn Hin Hin2 Hlo Hhi HnF Hp2.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (G2 b m (a - b) Hin Hin2); [lia|].
replace (b + (a - b)) with a by lia. apply HnF. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp2. lia.
Qed.
Lemma sep_tmp_entry : forall ly3 S3 W3 m3 md3 (entry : list (Z * Z)) pt n b m,
AR SEGS B ly3 S3 W3 m3 md3 -> Permutation (ablocks B ly3 S3) (entry ++ [(pt, n)]) -> In (b, m) entry ->
b + req_size m <= pt \/ pt + req_size n <= b.
Proof.
intros ly3 S3 W3 m3 md3 entry pt n b m HAR HP Hin.
apply in_split in Hin as (l1 & l2 & El). rewrite El in HP.
assert (HP2 : Permutation (ablocks B ly3 S3) ((pt, n) :: (b, m) :: l1 ++ l2)).
{ eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip.
apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ _ _ _ HAR HP2) as Hs. unfold zdisjoint, block_rng in Hs. cbn [fst snd] in Hs. lia.
Qed.
Lemma region_kept_img_sub : forall E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 lo (n : nat) v wlo whi cs,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
val_mem SEGS (mrestrict (w_H W) memc) lo n v -> val_mem SEGS (mrestrict (w_H W2) mem2) lo n v -> whi <= wlo ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion None lo (lo + Z.of_nat n) wlo whi cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 lo n v wlo whi cs _ V1 V2 Hro.
apply (region_kept_val SEGS _ _ _ lo n v); [exact V1 | exact V2 | exact Hro].
Qed.
End h.
End g.
End d.
