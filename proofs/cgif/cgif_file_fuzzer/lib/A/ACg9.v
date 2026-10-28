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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC87.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgm ACgo ACg8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require AChd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy ACgv.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Context {AX : af_paramsX}.
#[local] Notation path := (@afx_path AX).
#[local] Notation pf := (@afx_pf AX).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma af_land_le : forall x k, 0 <= k -> 0 <= Z.land x k <= k.
Proof.
intros x k Hk. apply (Z.ldiff_le _ _ Hk). apply Z.bits_inj'. intros n Hn.
rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit x n), (Z.testbit k n); reflexivity.
Qed.
Lemma af_bU_andx : forall E n (w : N) x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ Z.of_N w -> 0 < Z.of_N w <= 64 ->
U E (SAlu ALU_AND (SExt false w (SOff n 0)) (SLit k)) = Z.land x k.
Proof.
intros E n w x k He Rx Rk Rw. assert (P64 : 2 ^ Z.of_N w <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext, (U_atom E n x He Rx), U_lit by lia.
rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones _) k), Z.land_ones by lia. rewrite (Z.mod_small k) by lia.
apply zcanon_id. unfold M64. pose proof (af_land_le x k ltac:(lia)). lia.
Qed.
Lemma af_bU_and : forall E n x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
U E (SAlu ALU_AND (SOff n 0) (SLit k)) = Z.land x k.
Proof.
intros E n x k He Rx Rk. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x He Rx), U_lit by lia.
apply zcanon_id. unfold M64. pose proof (af_land_le x k ltac:(lia)). lia.
Qed.
Lemma af_bbr_fd : forall E fd delay (b : bool), ew E 72 = Z_to_bv 64 fd -> ew E 51 = Z_to_bv 64 delay -> 0 <= fd < 65536 -> 0 <= delay < 65536 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_SRL (SAlu ALU_ADD (SOff 72 0) (SExt false 16 (SOff 51 0))) (SLit 16))) (sv_denot E (SLit 0)) = b ->
if b then 65535 < delay + fd else delay + fd <= 65535.
Proof.
intros E fd delay b E72 E51 Rfd Rdl H. rewrite branch_ne_U in H. rewrite U_SAlu in H. cbn [zalu_raw] in H. rewrite U_SAlu in H. cbn [zalu_raw] in H.
rewrite U_zext, (U_atom E 72 fd E72), (U_atom E 51 delay E51), !U_lit in H by lia.
change (Z.land 16 63) with 16 in H. change (2 ^ Z.of_N 16) with 65536 in H.
rewrite (Z.mod_small delay 65536), (zcanon_id (fd + delay)), Z.shiftr_div_pow2 in H by (unfold M64; lia). change (2 ^ 16) with 65536 in H.
assert (Rq : 0 <= (fd + delay) / 65536 < 2) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite zcanon_id in H by (unfold M64; lia).
destruct b; [apply Bool.negb_true_iff in H | apply Bool.negb_false_iff in H].
- apply Z.eqb_neq in H. assert (1 <= (fd + delay) / 65536) by lia.
pose proof (Z.mul_div_le (fd + delay) 65536 ltac:(lia)). lia.
- apply Z.eqb_eq in H. pose proof (Z.div_mod (fd + delay) 65536 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (fd + delay) 65536 ltac:(lia)). lia.
Qed.
Lemma af_bbr_and1 : forall E n (w : N) x (b : bool), ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 1 < 2 ^ Z.of_N w -> 0 < Z.of_N w <= 64 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SExt false w (SOff n 0)) (SLit 1))) (sv_denot E (SLit 0)) = b ->
if b then Z.land x 1 <> 0 else Z.land x 1 = 0.
Proof.
intros E n w x b He Rx Rk Rw H. rewrite branch_ne_U, (af_bU_andx E n w x 1 He Rx ltac:(lia) Rw), U_lit in H by lia.
destruct b; [apply Bool.negb_true_iff in H; apply Z.eqb_neq in H | apply Bool.negb_false_iff in H; apply Z.eqb_eq in H]; exact H.
Qed.
Lemma af_land5 : forall x, Z.land x 5 = 0 <-> Z.land x 1 = 0 /\ Z.land x 4 = 0.
Proof. intros x. replace 5 with (Z.lor 1 4) by reflexivity. rewrite Z.land_lor_distr_r. apply Z.lor_eq_0_iff. Qed.
Lemma af_bbr_flags : forall E fattr hattr (b : bool), ew E 49 = Z_to_bv 64 fattr -> ew E 71 = Z_to_bv 64 hattr -> 0 <= fattr < 2 ^ 32 -> 0 <= hattr < 2 ^ 32 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_OR (SAlu ALU_AND (SOff 71 0) (SLit 5)) (SAlu ALU_AND (SExt false 32 (SOff 49 0)) (SLit 4)))) (sv_denot E (SLit 0)) = b ->
if b then Z.land hattr 1 = 0 /\ Z.land hattr 4 = 0 /\ Z.land fattr 4 = 0 else Z.land hattr 1 <> 0 \/ Z.land hattr 4 <> 0 \/ Z.land fattr 4 <> 0.
Proof.
intros E fattr hattr b E49 E71 Rf Rh H. rewrite branch_eq_U, U_SAlu in H. cbn [zalu_raw] in H.
rewrite (af_bU_and E 71 hattr 5 E71 ltac:(lia) ltac:(lia)), (af_bU_andx E 49 32 fattr 4 E49 ltac:(lia) ltac:(cbn; lia) ltac:(lia)), U_lit in H by lia.
pose proof (af_land_le hattr 5 ltac:(lia)) as R5. pose proof (af_land_le fattr 4 ltac:(lia)) as R4.
pose proof (Z.add_lor_land (Z.land hattr 5) (Z.land fattr 4)) as AL.
assert (RA : 0 <= Z.land (Z.land hattr 5) (Z.land fattr 4)) by (apply Z.land_nonneg; lia).
assert (ROR : 0 <= Z.lor (Z.land hattr 5) (Z.land fattr 4)) by (apply Z.lor_nonneg; lia).
rewrite zcanon_id in H by (unfold M64; lia).
destruct b.
- apply Z.eqb_eq in H. apply Z.lor_eq_0_iff in H as [H5 H4]. apply af_land5 in H5 as [H1 H4']. split; [exact H1 | split; [exact H4' | exact H4]].
- apply Z.eqb_neq in H. destruct (Z.eq_dec (Z.land hattr 1) 0) as [A1 | A1]; [| left; exact A1].
destruct (Z.eq_dec (Z.land hattr 4) 0) as [A4 | A4]; [| right; left; exact A4]. right. right. intros F4. apply H.
apply Z.lor_eq_0_iff. split; [apply af_land5; split; assumption | exact F4].
Qed.
Lemma af_bbr_a0 : forall E n (v : word) (b : bool), ew E n = v ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> if b then v = Z_to_bv 64 0 else v <> Z_to_bv 64 0.
Proof.
intros E n v b He H. rewrite branch_eq_U, U_SOff, U_lit, He, Z.add_0_r in H by lia.
pose proof (bv_unsigned_in_range _ v) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite zcanon_id in H by (unfold M64; lia).
destruct b.
- apply Z.eqb_eq in H. rewrite <- (Z_to_bv_bv_unsigned _ v), H. reflexivity.
- apply Z.eqb_neq in H. intros Q. apply H. rewrite Q. apply unsigned_lit_small. lia.
Qed.
Lemma af_bbr_a0ne : forall E n (v : word) (b : bool), ew E n = v ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> if b then v <> Z_to_bv 64 0 else v = Z_to_bv 64 0.
Proof.
intros E n v b He H. rewrite branch_ne_U in H.
pose proof (af_bbr_a0 E n v (negb b) He ltac:(rewrite branch_eq_U; destruct b; [apply Bool.negb_true_iff in H | apply Bool.negb_false_iff in H]; exact H)) as Q.
destruct b; exact Q.
Qed.
Section e.
Variables (G : YO07.gcfg) (attr gen delay ctrans nlp : Z) (lpal img : list Z).
#[local] Abbreviation cmpqM HD := (fun pq : Z * Z => negb (YO07.cmp_pixel G (YI0b.af_nf G attr gen delay ctrans nlp lpal img) HD (fst pq) (snd pq))).
Lemma af_merged_head : forall gs (k : nat) hd, YO07.s_ihead gs = Z.of_nat k -> (k < 3)%nat -> qslot gs k = Some hd ->
delay + YO07.f_delay hd <= 65535 -> YO07.flag (YO07.g_gen G) 1 = false ->
af_merged G attr gen delay ctrans nlp lpal img gs =
(if af_same G attr gen delay ctrans nlp lpal img hd then Some (YO07.q_set gs (Z.of_nat k) (Some (YO07.set_delay hd (delay + YO07.f_delay hd)))) else None).
Proof.
intros gs k hd Hih Hk Hq Hfd Hg. unfold af_merged. rewrite Hih, (qslot_get gs k Hk), Hq, Hg.
replace (delay + YO07.f_delay hd <=? 65535) with true by (symmetry; apply Z.leb_le; exact Hfd). cbn [andb negb]. reflexivity.
Qed.
Lemma af_merged_none_fd : forall gs (k : nat) hd, YO07.s_ihead gs = Z.of_nat k -> (k < 3)%nat -> qslot gs k = Some hd ->
65535 < delay + YO07.f_delay hd -> af_merged G attr gen delay ctrans nlp lpal img gs = None.
Proof.
intros gs k hd Hih Hk Hq Hfd. unfold af_merged. rewrite Hih, (qslot_get gs k Hk), Hq.
replace (delay + YO07.f_delay hd <=? 65535) with false by (symmetry; apply Z.leb_gt; exact Hfd). reflexivity.
Qed.
Lemma af_merged_none_keep : forall gs, YO07.flag (YO07.g_gen G) 1 = true -> af_merged G attr gen delay ctrans nlp lpal img gs = None.
Proof.
intros gs Hg. unfold af_merged. destruct (YO07.q_get gs (YO07.s_ihead gs)) as [hd|]; [| reflexivity].
rewrite Hg, Bool.andb_false_r. reflexivity.
Qed.
Lemma af_from_merge_none : forall gs, af_merged G attr gen delay ctrans nlp lpal img gs = None ->
af_from_merge G attr gen delay ctrans nlp lpal img gs = af_rest G attr gen delay ctrans nlp lpal img gs.
Proof. intros gs H. unfold af_from_merge. rewrite H. reflexivity. Qed.
Lemma af_from_merge_same : forall gs gs', af_merged G attr gen delay ctrans nlp lpal img gs = Some gs' ->
af_from_merge G attr gen delay ctrans nlp lpal img gs = gs'.
Proof. intros gs gs' H. unfold af_from_merge. rewrite H. reflexivity. Qed.
Lemma af_merged_some_fd : forall gs (k : nat) hd gs', YO07.s_ihead gs = Z.of_nat k -> (k < 3)%nat -> qslot gs k = Some hd ->
af_merged G attr gen delay ctrans nlp lpal img gs = Some gs' -> delay + YO07.f_delay hd <= 65535.
Proof.
intros gs k hd gs' Hih Hk Hq H. unfold af_merged in H. rewrite Hih, (qslot_get gs k Hk), Hq in H.
destruct (Z.leb_spec (delay + YO07.f_delay hd) 65535) as [L | L]; [exact L | cbn [andb] in H; discriminate H].
Qed.
Lemma af_same_fast : forall hd, Z.land attr 1 = 0 -> Z.land (YO07.f_attr hd) 1 = 0 -> Z.land attr 4 = 0 -> Z.land (YO07.f_attr hd) 4 = 0 ->
af_same G attr gen delay ctrans nlp lpal img hd = YO07.list_eqb img (YO07.f_img hd).
Proof. intros hd H1 H2 H3 H4. unfold af_same, YO07.flag. rewrite H1, H2, H3, H4. reflexivity. Qed.
Lemma af_same_slow : forall hd, (Z.land attr 1 <> 0 \/ Z.land (YO07.f_attr hd) 1 <> 0 \/ Z.land attr 4 <> 0 \/ Z.land (YO07.f_attr hd) 4 <> 0) ->
af_same G attr gen delay ctrans nlp lpal img hd = forallb (cmpqM hd) (combine img (YO07.f_img hd)).
Proof.
intros hd H. unfold af_same, YO07.flag.
destruct (Z.eqb_spec (Z.land attr 1) 0) as [A1 | A1]; cbn [negb andb]; [| reflexivity].
destruct (Z.eqb_spec (Z.land (YO07.f_attr hd) 1) 0) as [A2 | A2]; cbn [negb andb]; [| reflexivity].
destruct (Z.eqb_spec (Z.land attr 4) 0) as [A3 | A3]; cbn [negb andb]; [| reflexivity].
destruct (Z.eqb_spec (Z.land (YO07.f_attr hd) 4) 0) as [A4 | A4]; cbn [negb andb]; [| reflexivity].
exfalso. destruct H as [H | [H | [H | H]]]; apply H; assumption.
Qed.
Lemma af_prefix_step : forall (P : Z * Z -> bool) (a b : list Z) (k : nat), (k < length a)%nat -> (k < length b)%nat ->
forallb P (combine (firstn k a) (firstn k b)) = true -> P (nth k a 0, nth k b 0) = true ->
forallb P (combine (firstn (Datatypes.S k) a) (firstn (Datatypes.S k) b)) = true.
Proof.
intros P a. induction a as [|x a IH]; intros b k Ha Hb Hp Hk; [cbn in Ha; lia|].
destruct b as [|y b]; [cbn in Hb; lia|]. destruct k as [|k].
- cbn in Hk |- *. rewrite Hk. reflexivity.
- cbn [firstn combine forallb nth length] in *. apply andb_prop in Hp as [Hp1 Hp2]. rewrite Hp1. cbn [andb].
apply (IH b k); [lia | lia | exact Hp2 | exact Hk].
Qed.
Lemma af_prefix_false : forall (P : Z * Z -> bool) (a b : list Z) (k : nat), (k < length a)%nat -> (k < length b)%nat ->
P (nth k a 0, nth k b 0) = false -> forallb P (combine a b) = false.
Proof.
intros P a. induction a as [|x a IH]; intros b k Ha Hb Hk; [cbn in Ha; lia|].
destruct b as [|y b]; [cbn in Hb; lia|]. destruct k as [|k].
- cbn in Hk |- *. rewrite Hk. reflexivity.
- cbn [combine forallb nth length] in *. rewrite (IH b k); [apply Bool.andb_false_r | lia | lia | exact Hk].
Qed.
Lemma af_prefix_all : forall (P : Z * Z -> bool) (a b : list Z) (k : nat), length a = k -> length b = k ->
forallb P (combine (firstn k a) (firstn k b)) = forallb P (combine a b).
Proof. intros P a b k Ha Hb. rewrite !firstn_all2 by lia. reflexivity. Qed.
End e.
Lemma af_land4_6 : forall x, Z.land x 4 <> 0 -> Z.land x 6 <> 0.
Proof.
intros x H E. apply H. replace 4 with (Z.land 6 4) by reflexivity. rewrite Z.land_assoc, E. reflexivity.
Qed.
Lemma af_flag1_false : forall x, Z.land x 1 = 0 -> YO07.flag x 1 = false.
Proof. intros x H. unfold YO07.flag. rewrite H. reflexivity. Qed.
Lemma af_flag1_true : forall x, Z.land x 1 <> 0 -> YO07.flag x 1 = true.
Proof. intros x H. unfold YO07.flag. destruct (Z.eqb_spec (Z.land x 1) 0) as [E | E]; [exfalso; exact (H E) | reflexivity]. Qed.
Section h.
Variable K : asink_syms.
#[local] Abbreviation cmpq G attr gen delay ctrans nlp lpal img HD := (fun pq : Z * Z => negb (YO07.cmp_pixel G (YI0b.af_nf G attr gen delay ctrans nlp lpal img) HD (fst pq) (snd pq))).
Lemma af_xb_head : forall (m : word -> option byte) md s N GPAL gs f,
cgif_relA SEGS K m md s pf N GPAL gs -> cgif_live gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
exists HD, qslot gs (Z.to_nat (cg_ihead s)) = Some HD /\ frame_relbA SEGS true m N f HD.
Proof.
intros m md s N GPAL gs f XR XLV Hih Hn.
apply (proj1 (cgif_relA_split SEGS K m md s pf N GPAL gs)) in XR as (_ & _ & XL).
pose proof (proj1 (af_xlive_iff SEGS m s N GPAL gs) (XL XLV)) as [_ XSL].
assert (Hk : (Z.to_nat (cg_ihead s) < 3)%nat) by (destruct Hih as [-> | ->]; cbv; lia).
pose proof (XSL _ Hk I) as R. rewrite Hn in R.
assert (Ew : wgk (Z.to_nat (cg_ihead s)) = true) by (destruct Hih as [-> | ->]; reflexivity). rewrite Ew in R.
destruct (qslot gs (Z.to_nat (cg_ihead s))) as [HD|]; [| destruct R].
exists HD. split; [reflexivity | exact R].
Qed.
Lemma af_xb_ih : forall (m : word -> option byte) md s N GPAL gs,
cgif_relA SEGS K m md s pf N GPAL gs -> cgif_live gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
YO07.s_ihead gs = Z.of_nat (Z.to_nat (cg_ihead s)) /\ (Z.to_nat (cg_ihead s) < 3)%nat.
Proof.
intros m md s N GPAL gs XR XLV Hih.
apply (proj1 (cgif_relA_split SEGS K m md s pf N GPAL gs)) in XR as (_ & _ & XL).
destruct (XL XLV) as (_ & _ & XHih & _). rewrite <- XHih. destruct Hih as [-> | ->]; split; cbv; first [reflexivity | lia].
Qed.
Lemma af_xb_c_fd : forall (m : word -> option byte) md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f HD,
cgif_relA SEGS K m md s pf N GPAL gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
qslot gs (Z.to_nat (cg_ihead s)) = Some HD -> frame_relbA SEGS true m N f HD ->
af_xok s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF -> 65535 < delay + fr_delay f ->
af_xc s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF.
Proof.
intros m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f HD XR Hih Hq XF [XLV XGF] Hfd. split; [exact XLV|]. rewrite XGF.
destruct (af_xb_ih m md s N GPAL gs XR XLV Hih) as [Eih Hk]. apply af_from_merge_none.
apply (af_merged_none_fd _ _ _ _ _ _ _ _ gs _ HD Eih Hk Hq). destruct XF as (_ & _ & Ed & _). rewrite <- Ed. exact Hfd.
Qed.
Lemma af_xb_c_keep : forall s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF,
af_xok s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF -> Z.land (cg_gen s) 1 <> 0 ->
af_xc s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF.
Proof.
intros s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF [XLV XGF] Hg. split; [exact XLV|]. rewrite XGF. apply af_from_merge_none.
apply af_merged_none_keep. cbn [gcfg_of YO07.g_gen]. apply af_flag1_true. exact Hg.
Qed.
Lemma af_xb_merged : forall (m : word -> option byte) md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs f HD,
cgif_relA SEGS K m md s pf N GPAL gs -> cgif_live gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
qslot gs (Z.to_nat (cg_ihead s)) = Some HD -> frame_relbA SEGS true m N f HD ->
delay + fr_delay f <= 65535 -> Z.land (cg_gen s) 1 = 0 ->
delay + YO07.f_delay HD <= 65535 /\
YI0b.af_merged (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG gs =
(if af_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG HD
then Some (YO07.q_set gs (YO07.s_ihead gs) (Some (YO07.set_delay HD (delay + YO07.f_delay HD)))) else None).
Proof.
intros m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs f HD XR XLV Hih Hq XF Hfd Hg.
destruct (af_xb_ih m md s N GPAL gs XR XLV Hih) as [Eih Hk].
assert (Hfd' : delay + YO07.f_delay HD <= 65535) by (destruct XF as (_ & _ & Ed & _); rewrite <- Ed; exact Hfd).
split; [exact Hfd'|]. rewrite Eih.
apply (af_merged_head _ _ _ _ _ _ _ _ gs _ HD Eih Hk Hq Hfd'). cbn [gcfg_of YO07.g_gen]. apply af_flag1_false. exact Hg.
Qed.
Lemma af_xb_l0 : forall (m : word -> option byte) md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f HD,
cgif_relA SEGS K m md s pf N GPAL gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
qslot gs (Z.to_nat (cg_ihead s)) = Some HD -> frame_relbA SEGS true m N f HD ->
af_xok s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF ->
delay + fr_delay f <= 65535 -> Z.land (cg_gen s) 1 = 0 ->
(Z.land fattr 1 <> 0 \/ (Z.land (fr_attr f) 1 <> 0 \/ Z.land (fr_attr f) 4 <> 0 \/ Z.land fattr 4 <> 0)) ->
af_xl s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD 0.
Proof.
intros m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f HD XR Hih Hq XF [XLV XGF] Hfd Hg Hslow.
destruct (af_xb_merged m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs f HD XR XLV Hih Hq XF Hfd Hg) as [_ XM].
split; [exact XLV|]. split; [exact XGF|]. split; [exact Hq|]. split; [| reflexivity].
rewrite XM, af_same_slow; [reflexivity|]. destruct XF as (Ea & _). rewrite <- Ea.
destruct Hslow as [H | [H | [H | H]]]; [left; exact H | right; left; exact H | right; right; right; exact H | right; right; left; exact H].
Qed.
Lemma af_xb_sm_fast : forall (m : word -> option byte) md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f HD,
cgif_relA SEGS K m md s pf N GPAL gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
qslot gs (Z.to_nat (cg_ihead s)) = Some HD -> frame_relbA SEGS true m N f HD ->
af_xok s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF ->
delay + fr_delay f <= 65535 -> Z.land (cg_gen s) 1 = 0 ->
Z.land fattr 1 = 0 -> Z.land (fr_attr f) 1 = 0 -> Z.land fattr 4 = 0 -> Z.land (fr_attr f) 4 = 0 ->
IMG = YO07.f_img HD -> af_xsm s delay gs gsF HD.
Proof.
intros m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f HD XR Hih Hq XF [XLV XGF] Hfd Hg H1 H2 H3 H4 HE.
destruct (af_xb_merged m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs f HD XR XLV Hih Hq XF Hfd Hg) as [Hfd' XM].
pose proof XF as (Ea & _). rewrite Ea in H2, H4.
rewrite (af_same_fast _ _ _ _ _ _ _ _ HD H1 H2 H3 H4), (proj2 (YC87.list_eqb_true_iff _ _) HE) in XM.
split; [exact XLV|]. split; [exact Hq|]. split; [exact Hfd'|]. rewrite XGF. exact (af_from_merge_same _ _ _ _ _ _ _ _ gs _ XM).
Qed.
Lemma af_xb_c_fast : forall (m : word -> option byte) md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f HD,
cgif_relA SEGS K m md s pf N GPAL gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
qslot gs (Z.to_nat (cg_ihead s)) = Some HD -> frame_relbA SEGS true m N f HD ->
af_xok s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF ->
delay + fr_delay f <= 65535 -> Z.land (cg_gen s) 1 = 0 ->
Z.land fattr 1 = 0 -> Z.land (fr_attr f) 1 = 0 -> Z.land fattr 4 = 0 -> Z.land (fr_attr f) 4 = 0 ->
IMG <> YO07.f_img HD -> af_xc s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF.
Proof.
intros m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f HD XR Hih Hq XF [XLV XGF] Hfd Hg H1 H2 H3 H4 HE.
destruct (af_xb_merged m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs f HD XR XLV Hih Hq XF Hfd Hg) as [Hfd' XM].
pose proof XF as (Ea & _). rewrite Ea in H2, H4.
rewrite (af_same_fast _ _ _ _ _ _ _ _ HD H1 H2 H3 H4) in XM.
destruct (YO07.list_eqb IMG (YO07.f_img HD)) eqn:LE; [exfalso; exact (HE (proj1 (YC87.list_eqb_true_iff _ _) LE))|].
split; [exact XLV|]. rewrite XGF. exact (af_from_merge_none _ _ _ _ _ _ _ _ gs XM).
Qed.
Lemma af_bcmp_model : forall (m : word -> option byte) (rd : Z -> option Z) x y (A Bl : list Z) n,
(forall a, rd a = option_map (fun b : byte => bv_unsigned b) (mbyte SEGS m a)) ->
garr8 SEGS m x A -> garr8 SEGS m y Bl -> Z.of_nat (length A) = n -> Z.of_nat (length Bl) = n ->
((forall i, 0 <= i < n -> rd (x + i) = rd (y + i)) <-> A = Bl).
Proof.
intros m rd x y A Bl n Hrd GA GB LA LB. split.
- intros H. apply (nth_ext A Bl 0 0); [lia|]. intros k Hk.
pose proof (H (Z.of_nat k) ltac:(lia)) as E.
rewrite (YC87.rd_garr8 SEGS m rd Hrd x A (Z.of_nat k) GA ltac:(lia) ltac:(lia)) in E.
rewrite (YC87.rd_garr8 SEGS m rd Hrd y Bl (Z.of_nat k) GB ltac:(lia) ltac:(lia)) in E.
rewrite Nat2Z.id in E. injection E as E. exact E.
- intros <- i Hi.
rewrite (YC87.rd_garr8 SEGS m rd Hrd x A i GA ltac:(lia) ltac:(lia)).
rewrite (YC87.rd_garr8 SEGS m rd Hrd y A i GB ltac:(lia) ltac:(lia)). reflexivity.
Qed.
Lemma af_xb_headq : forall (m : word -> option byte) md s N GPAL gs f HD,
cgif_relA SEGS K m md s pf N GPAL gs -> cgif_live gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f -> qslot gs (Z.to_nat (cg_ihead s)) = Some HD -> frame_relbA SEGS true m N f HD.
Proof.
intros m md s N GPAL gs f HD XR XLV Hih Hn Hq. destruct (af_xb_head m md s N GPAL gs f XR XLV Hih Hn) as (HD' & Hq' & XF).
rewrite Hq in Hq'. injection Hq' as <-. exact XF.
Qed.
Lemma af_xl_pix : forall (m : word -> option byte) (rd : Z -> option Z) md s N img lpa fattr nlp GPAL IMG LPAL gs f HD kk bc bb,
(forall a, rd a = option_map (fun b : byte => bv_unsigned b) (mbyte SEGS m a)) ->
af_xrel K m md s N img lpa fattr nlp GPAL IMG LPAL gs -> cgif_live gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f -> qslot gs (Z.to_nat (cg_ihead s)) = Some HD ->
0 <= kk < N -> rd (img + kk) = Some bc -> rd (fr_img f + kk) = Some bb ->
bc = nth (Z.to_nat kk) IMG 0 /\ bb = nth (Z.to_nat kk) (YO07.f_img HD) 0.
Proof.
intros m rd md s N img lpa fattr nlp GPAL IMG LPAL gs f HD kk bc bb Hrd (XR & XGI & XGIL & XGL) XLV Hih Hn Hq Hkk Rc Rb.
pose proof (af_xb_headq m md s N GPAL gs f HD XR XLV Hih Hn Hq) as (_ & _ & _ & _ & _ & _ & _ & GFI & LFI & _).
rewrite (YC87.rd_garr8 SEGS m rd Hrd img IMG kk XGI ltac:(lia) ltac:(lia)) in Rc. injection Rc as Rc.
rewrite (YC87.rd_garr8 SEGS m rd Hrd (fr_img f) (YO07.f_img HD) kk GFI ltac:(lia) ltac:(lia)) in Rb. injection Rb as Rb.
split; symmetry; assumption.
Qed.
Lemma af_xl_verdict : forall (m : word -> option byte) (rd : Z -> option Z) md s N img lpa lpal fattr fgen delay nlp tidx GPAL IMG LPAL gs f HD bc bb,
(forall a, rd a = option_map (fun b : byte => bv_unsigned b) (mbyte SEGS m a)) ->
af_xrel K m md s N img lpa fattr nlp GPAL IMG LPAL gs -> cgif_live gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f -> qslot gs (Z.to_nat (cg_ihead s)) = Some HD ->
(Z.land fattr 1 <> 0 -> lpa = lpal) ->
(Z.land fattr 1 = 0 \/ Z.land (fr_attr f) 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
0 <= bc < 256 -> 0 <= bb < 256 ->
(AChd.tcmp_zero rd (cg_pal s) (cg_ngp s) lpal fattr nlp tidx (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f) bc bb <->
YO07.cmp_pixel (gcfg_of s GPAL) (YI0b.af_nf (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG) HD bc bb = false).
Proof.
intros m rd md s N img lpa lpal fattr fgen delay nlp tidx GPAL IMG LPAL gs f HD bc bb Hrd (XR & XGI & XGIL & XGL) XLV Hih Hn Hq Hlp Hg4 Rbc Rbb.
pose proof (af_xb_headq m md s N GPAL gs f HD XR XLV Hih Hn Hq) as XF.
pose proof XF as (Ea & _ & _ & Enl & Ect & _ & _ & GFI & LFI & GFL).
apply (proj1 (cgif_relA_split SEGS K m md s pf N GPAL gs)) in XR as (_ & _ & XL). destruct (XL XLV) as (_ & _ & _ & XGP & _).
apply (YC87.tcmp_zero_model SEGS m rd Hrd (gcfg_of s GPAL) (YI0b.af_nf (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG) HD).
- reflexivity.
- intros H4. unfold YI0b.af_nf, YO07.new_frame. cbn [YO07.f_ctrans]. unfold YO07.flag.
destruct (Z.eqb_spec (Z.land fattr 6) 0) as [E6 | E6]; [exfalso; exact (af_land4_6 fattr H4 E6) | reflexivity].
- reflexivity.
- exact Ea.
- intros H4. apply Ect. exact (af_land4_6 _ H4).
- exact Enl.
- reflexivity.
- intros H1. cbn [YI0b.af_nf YO07.new_frame YO07.f_lpal]. destruct (XGL H1) as [Hg Hgl]. rewrite <- (Hlp H1). split; [exact Hg | lia].
- intros H1. destruct (GFL H1) as [Hg Hgl]. split; [exact Hg | lia].
- intros H1. destruct (XGP (Hg4 H1)) as [Hg Hgl]. cbn [gcfg_of YO07.g_gpal YO07.g_ngp]. split; [exact Hg | lia].
- exact Rbc.
- exact Rbb.
Qed.
Lemma af_xl_step : forall s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD kk N,
af_xl s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD kk -> 0 <= kk < N -> Z.of_nat (length IMG) = N -> Z.of_nat (length (YO07.f_img HD)) = N ->
YO07.cmp_pixel (gcfg_of s GPAL) (YI0b.af_nf (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG) HD (nth (Z.to_nat kk) IMG 0) (nth (Z.to_nat kk) (YO07.f_img HD) 0) = false ->
af_xl s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD (kk + 1).
Proof.
intros s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD kk N (X1 & X2 & X3 & X4 & X5) Hkk LI LF Hc.
split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
replace (Z.to_nat (kk + 1)) with (Datatypes.S (Z.to_nat kk)) by lia.
apply af_prefix_step; [lia | lia | exact X5 | cbn [fst snd]; rewrite Hc; reflexivity].
Qed.
Lemma af_xl_c : forall s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD kk N,
af_xl s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD kk -> 0 <= kk < N -> Z.of_nat (length IMG) = N -> Z.of_nat (length (YO07.f_img HD)) = N ->
YO07.cmp_pixel (gcfg_of s GPAL) (YI0b.af_nf (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG) HD (nth (Z.to_nat kk) IMG 0) (nth (Z.to_nat kk) (YO07.f_img HD) 0) = true ->
af_xc s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF.
Proof.
intros s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD kk N (X1 & X2 & X3 & X4 & X5) Hkk LI LF Hc.
split; [exact X1|]. rewrite X2. apply af_from_merge_none. rewrite X4.
rewrite (af_prefix_false _ IMG (YO07.f_img HD) (Z.to_nat kk)); [reflexivity | lia | lia | cbn [fst snd]; rewrite Hc; reflexivity].
Qed.
Lemma af_xl_sm : forall (m : word -> option byte) md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD,
cgif_relA SEGS K m md s pf N GPAL gs -> (cg_ihead s = 1 \/ cg_ihead s = 2) ->
af_xl s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD N -> Z.of_nat (length IMG) = N -> Z.of_nat (length (YO07.f_img HD)) = N ->
af_xsm s delay gs gsF HD.
Proof.
intros m md s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD XR Hih (X1 & X2 & X3 & X4 & X5) LI LF.
rewrite (af_prefix_all _ IMG (YO07.f_img HD) (Z.to_nat N)) in X5 by lia. rewrite X5 in X4.
destruct (af_xb_ih m md s N GPAL gs XR X1 Hih) as [Eih Hk].
split; [exact X1|]. split; [exact X3|].
split; [exact (af_merged_some_fd _ _ _ _ _ _ _ _ gs _ HD _ Eih Hk X3 X4)|].
rewrite X2. exact (af_from_merge_same _ _ _ _ _ _ _ _ gs _ X4).
Qed.
End h.
Section j.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma af_lpa_eq : forall ly S W mem md g s N img fattr fgen delay tidx lpa lpal nlp rest cfp,
AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) ->
obj_at SEGS (mrestrict (w_H W) mem) cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal -> Z.land fattr 1 <> 0 -> lpa = lpal.
Proof.
intros ly S W mem md g s N img fattr fgen delay tidx lpa lpal nlp rest cfp HAR HPerm HCF Hlpa H1.
pose proof asan_consts as (C1 & _).
assert (Hlpab : In (lpa, 3 * nlp) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. right.
destruct (Z.eqb_spec (Z.land fattr 1) 0) as [E0 | E0]; [exfalso; exact (H1 E0) | left; reflexivity]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ lpa (3 * nlp) HAR Hlpab) as (_ & Hl4096 & Hlceil & _ & _ & _ & Hl0 & _).
pose proof (req_size_pos (3 * nlp) ltac:(clear - Hl0; lia)) as [Hrl _].
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. cbn [snd] in Rlpal. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rlpal.
apply (f_equal bv_unsigned) in Hlpa. rewrite !unsigned_lit_small in Hlpa by (clear - Hl4096 Hlceil Hrl Rlpal C1; lia). exact Hlpa.
Qed.
End j.
Lemma af_bU_zx32 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 32 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff n 0)) (SLit 32)) (SLit 32)) = x.
Proof.
intros E n x He Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
change (Z.land (zcanon 32) 63) with 32.
rewrite (cl_U_sext32 E (SOff n 0) x (U_atom E n x He ltac:(lia)) Rx).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
assert (Em : zcanon ((if x <? 2 ^ 31 then x else x - 2 ^ 32 + 2 ^ 64) * 2 ^ 32) = x * 2 ^ 32).
{ unfold zcanon, M64. destruct (x <? 2 ^ 31).
- apply Z.mod_small. lia.
- replace ((x - 2 ^ 32 + 2 ^ 64) * 2 ^ 32) with (x * 2 ^ 32 + (2 ^ 32 - 1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite Em, Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma af_bbr_and1g : forall E a x (b : bool), U E a = x -> 0 <= x < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND a (SLit 1))) (sv_denot E (SLit 0)) = b -> if b then Z.land x 1 <> 0 else Z.land x 1 = 0.
Proof.
intros E a x b Ha Rx H. rewrite branch_ne_U, U_SAlu in H. cbn [zalu_raw] in H. rewrite Ha, !U_lit in H by lia.
rewrite zcanon_id in H by (unfold M64; pose proof (af_land_le x 1 ltac:(lia)); lia).
destruct b; [apply Bool.negb_true_iff in H; apply Z.eqb_neq in H | apply Bool.negb_false_iff in H; apply Z.eqb_eq in H]; exact H.
Qed.
Lemma af_bbr_flagsg : forall E a fattr hattr (b : bool), U E a = fattr -> ew E 71 = Z_to_bv 64 hattr -> 0 <= fattr < 2 ^ 32 -> 0 <= hattr < 2 ^ 32 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_OR (SAlu ALU_AND (SOff 71 0) (SLit 5)) (SAlu ALU_AND a (SLit 4)))) (sv_denot E (SLit 0)) = b ->
if b then Z.land hattr 1 = 0 /\ Z.land hattr 4 = 0 /\ Z.land fattr 4 = 0 else Z.land hattr 1 <> 0 \/ Z.land hattr 4 <> 0 \/ Z.land fattr 4 <> 0.
Proof.
intros E a fattr hattr b Ha E71 Rf Rh H. rewrite branch_eq_U, U_SAlu in H. cbn [zalu_raw] in H.
rewrite (af_bU_and E 71 hattr 5 E71 ltac:(lia) ltac:(lia)), U_lit in H by lia.
rewrite (U_SAlu E ALU_AND a (SLit 4)) in H. cbn [zalu_raw] in H. rewrite Ha, U_lit in H by lia.
pose proof (af_land_le hattr 5 ltac:(lia)) as R5. pose proof (af_land_le fattr 4 ltac:(lia)) as R4.
rewrite (zcanon_id (Z.land fattr 4)) in H by (unfold M64; lia).
pose proof (Z.add_lor_land (Z.land hattr 5) (Z.land fattr 4)) as AL.
assert (RA : 0 <= Z.land (Z.land hattr 5) (Z.land fattr 4)) by (apply Z.land_nonneg; lia).
assert (ROR : 0 <= Z.lor (Z.land hattr 5) (Z.land fattr 4)) by (apply Z.lor_nonneg; lia).
rewrite zcanon_id in H by (unfold M64; lia).
destruct b.
- apply Z.eqb_eq in H. apply Z.lor_eq_0_iff in H as [H5 H4]. apply af_land5 in H5 as [H1 H4']. split; [exact H1 | split; [exact H4' | exact H4]].
- apply Z.eqb_neq in H. destruct (Z.eq_dec (Z.land hattr 1) 0) as [A1 | A1]; [| left; exact A1].
destruct (Z.eq_dec (Z.land hattr 4) 0) as [A4 | A4]; [| right; left; exact A4]. right. right. intros F4. apply H.
apply Z.lor_eq_0_iff. split; [apply af_land5; split; assumption | exact F4].
Qed.
End d.
End c.
