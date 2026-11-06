(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import BigModel BigFactsBase BigFactsOps BigFactsRun.
Import ListNotations.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__BigFactsDigits () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsDigits."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsOps."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsRun."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel.W."; "Stdlib.ZArith.BinInt.Z."], [["1O"; "1S"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2iff"; "2not"]; ["2or"; "3add"; "3sub"; "4le"; "4lt"; "5Forall"; "5firstn"; "5nth"; "6Z"; "0J"; "0N"; "7val"; "7wordZ"; "7words_ok"; "8acarry"; "8e3402"]; ["8mcarry"; "8nwords"; "8pow10_check"; "8wlist"; "8wordi"; "9okN"; "9reduced"; "9reduced_ws"; "9wf"; ":all_digits"; ":dec"; ":dec_acc"; ";DDproduct"; "<M"; "<add"; "<b2z"]; ["<ltu"; ";add_word"; ";mul_word"; ";nth_w"; ";num_words_est"; ";round_up"; ";s_words"; ";size"; ";st"; ";sto"; ";words"; "=add"; "=div"; "=le"; "=lt"; "=max"]; ["=modulo"; "=mul"; "=of_nat"; "=pow"; "=sub"; "0V"; "0V'"; "0a"; "0acc"; "0b"; "0c"; "0d"; "0ds"; "0hl"; "0i"; "0j"]; ["0k"; "0m"; "0n"; "0p"; "0s"; "0s'"; "0s0"; "0t"; "0v"; "0w"; "0ws"; "0x"; "0y"]]).
Definition nwords (v : Z) : nat := if v <=? 0 then 0%nat else Z.to_nat (Z.log2 v / 64 + 1).
Lemma Mpow_nat : ltac2:(TCodec.tc2 tcn__BigFactsDigits "@'8'='H&R3&Q=&R2r1%211%5241+2&R1+R0%2215%:241%=3<61pU2?1").
Proof. intros k. rewrite M_val. change 18446744073709551616 with (2^64). rewrite <- Z.pow_mul_r by lia. reflexivity. Qed.
Lemma Mpow_pos : ltac2:(TCodec.tc2 tcn__BigFactsDigits ";'8&QNz&R3&Q=&R2r1%211%5241%8271pU2:1").
Proof. intros k. apply Z.pow_pos_nonneg. rewrite M_val; lia. lia. Qed.
Lemma Mpow_S : ltac2:(TCodec.tc2 tcn__BigFactsDigits "A'8'='H&R3&Q=&R2(1r1%211%411%7261&R1%715%:291%32:1%>3=51pU2@1").
Proof. intros k. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. Qed.
Lemma Mpow_le_mono : ltac2:(TCodec.tc2 tcn__BigFactsDigits "B'8'Cr2r1%3221&QM&R3&Q=&R2r3%211%5241%41:%7261%9231p0;1pTD@1pT@A1").
Proof. intros a b. intros. apply Z.pow_le_mono_r. rewrite M_val; lia. lia. Qed.
Lemma Mpow_lt_mono : ltac2:(TCodec.tc2 tcn__BigFactsDigits "B'8&Dr2r1%3221&QN&R3&Q=&R2r3%211%5241%41:%7261%9231p0;1pTD@1pT@A1").
Proof. intros a b. intros. apply Z.pow_lt_mono_r. rewrite M_val; lia. lia. lia. Qed.
Lemma nwords_0 : ltac2:(TCodec.tc2 tcn__BigFactsDigits "7'='8&Q1z%211(0%63521"). Proof. reflexivity. Qed.
Lemma nwords_nonpos : ltac2:(TCodec.tc2 tcn__BigFactsDigits ">'H&QMr1z%3221'='8&Q1r2%211(0%63521p081pUB=1").
Proof. intros v. intros. unfold nwords. destruct (Z.leb_spec v 0); auto. lia. Qed.
Lemma nwords_spec : ltac2:(TCodec.tc2 tcn__BigFactsDigits "I'H&QNzr1%3221'<&QM&R3&Q=&R2&B&Q1r2%211u1%5221%711%:291%<216%:16%=2<1%D291%A241p0C1pUBH1").
Proof. intros v.
intros Hv. unfold nwords. destruct (Z.leb_spec v 0). lia.
destruct (Z.log2_spec v Hv) as [L1 L2]. pose proof (Z.log2_nonneg v) as L0.
set (l := Z.log2 v) in *.
assert (Hq: 0 <= l / 64) by (apply Z.div_pos; lia).
replace (Z.of_nat (Z.to_nat (l / 64 + 1) - 1)) with (l / 64) by lia.
replace (Z.of_nat (Z.to_nat (l / 64 + 1))) with (l / 64 + 1) by lia.
rewrite M_val. change 18446744073709551616 with (2^64). rewrite <- !Z.pow_mul_r by lia.
pose proof (Z.div_mod l 64 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound l 64 ltac:(lia)) as MB.
split.
- eapply Z.le_trans; [|exact L1]. apply Z.pow_le_mono_r; lia.
- eapply Z.lt_le_trans; [exact L2|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma nwords_pos : ltac2:(TCodec.tc2 tcn__BigFactsDigits "='H&QNzr1%3221'Cu1&Q1r2%211%5241p071pUB<1").
Proof. intros v. intros. unfold nwords. destruct (Z.leb_spec v 0). lia. pose proof (Z.log2_nonneg v). assert (0 <= Z.log2 v / 64) by (apply Z.div_pos; lia). lia. Qed.
Lemma nwords_unique : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q0'H'8'Cu1r1%3221'<&QM&R3&Q=&R2&Br2%221:%411%7261r3%:221&QN%917%<2;1%3251%@251'=&Q1r4%211%43J1;p061p0H1pU2M1pUBO1").
Proof. intros v k.
intros Hk [H1 H2]. pose proof (Mpow_pos (k - 1)).
destruct (nwords_spec v ltac:(lia)) as [A B]. pose proof (nwords_pos v ltac:(lia)) as P.
destruct (Nat.lt_trichotomy (nwords v) k) as [C|[C|C]]; auto; exfalso.
- pose proof (Mpow_le_mono (nwords v) (k - 1) ltac:(lia)). lia.
- pose proof (Mpow_le_mono k (nwords v - 1) ltac:(lia)). lia.
Qed.
Lemma nwords_le_iff : ltac2:(TCodec.tc2 tcn__BigFactsDigits "G'H'8&QMzr2%3221&>'C&Q1r3%211%4217&QN&R3&Q=&R2%11<%4231%6291%=281p0?1pU2D1pUBF1").
Proof. intros v k.
intros Hv. destruct (Z.eq_dec v 0) as [->|].
{ rewrite nwords_0. split; intros. apply Mpow_pos. lia. }
destruct (nwords_spec v ltac:(lia)) as [A B]. split; intros C.
- eapply Z.lt_le_trans; [exact B|]. apply Mpow_le_mono; auto.
- destruct (Nat.le_gt_cases (nwords v) k); auto. exfalso.
pose proof (Mpow_le_mono k (nwords v - 1) ltac:(lia)). lia.
Qed.
Lemma nwords_lt_pow : ltac2:(TCodec.tc2 tcn__BigFactsDigits "A'H&QMzr1%3221&QNr2&R3&Q=&R2&Q1%115%311%6251%9281p0;1pUB@1").
Proof. intros v. intros. apply (proj1 (nwords_le_iff v (nwords v) H)). lia. Qed.
Lemma nwords_ge_iff : ltac2:(TCodec.tc2 tcn__BigFactsDigits "N'H'8&QMzr2%3221&>'C&Q1r3%211%4271'@'=(0%23>;1&R3&Q=&R2&Bu1%22A1%411%7261%F21?%=2:1%D2?1p0F1pU2K1pUBM1").
Proof. intros v k.
intros Hv. split; intros C.
- destruct k. auto. right. destruct (Z_lt_le_dec v (W.M ^ Z.of_nat (S k - 1))); auto. exfalso.
pose proof (proj2 (nwords_le_iff v (S k - 1) Hv) l). lia.
- destruct C as [->|C]. lia. destruct (Nat.le_gt_cases k (nwords v)); auto. exfalso.
pose proof (proj1 (nwords_le_iff v (nwords v) Hv) ltac:(lia)).
pose proof (Mpow_le_mono (nwords v) (k - 1) ltac:(lia)). lia.
Qed.
Lemma nwords_mono : ltac2:(TCodec.tc2 tcn__BigFactsDigits "B'H'<&QMzr2%3221r1%5231%7231'C&Q1r3%211%319%5221p071pTD@1pT@A1").
Proof. intros a b. intros. apply (proj2 (nwords_le_iff a (nwords b) ltac:(lia))). eapply Z.le_lt_trans. apply (proj2 H). apply nwords_lt_pow. lia. Qed.
Lemma nwords_1 : ltac2:(TCodec.tc2 tcn__BigFactsDigits "B'H'<&QNzr1%3221&Q=%5231%7231'='8&Q1r2%211u1%63521p081pUBA1").
Proof. intros v. intros. apply nwords_unique. lia. change (Z.of_nat (1 - 1)) with 0. change (Z.of_nat 1) with 1. rewrite Z.pow_0_r, Z.pow_1_r. lia. Qed.
Definition wordi (v : Z) (i : nat) : Z := (v / W.M ^ Z.of_nat i) mod W.M.
Definition wlist (v : Z) (n : nat) : words := map (fun i => wordi v i) (seq 0 n).
Lemma wordi_range : ltac2:(TCodec.tc2 tcn__BigFactsDigits ":'H'8&L&Q4r2r1%3221%511pTN71pUB91").
Proof. intros v i. unfold wordi, wordZ. apply Z.mod_pos_bound. rewrite M_val; lia. Qed.
Lemma wlist_length : ltac2:(TCodec.tc2 tcn__BigFactsDigits "<'H'8'=&6&Q3r2r1%3221%5281%73813pU691pUB;1").
Proof. intros v n. unfold wlist. rewrite length_map, length_seq. reflexivity. Qed.
Lemma wlist_words_ok : ltac2:(TCodec.tc2 tcn__BigFactsDigits ":'H'8&M&Q3r2r1%3221%511pU671pUB91").
Proof. intros v n. unfold wlist, words_ok. apply Forall_map. apply Forall_forall. intros; apply wordi_range. Qed.
Lemma wlist_nth : ltac2:(TCodec.tc2 tcn__BigFactsDigits "D'H'8&Dr1r2%3221'=&QC&Q3r4r3%3221%5218&Q4%125:%93?31p0;1pTN@1pU6A1pUBC1").
Proof. intros v n i.
intros. unfold wlist, nth_w. rewrite (nth_indep _ 0 (wordi v 0%nat)) by (rewrite length_map, length_seq; lia).
rewrite (map_nth (fun i => wordi v i)), seq_nth; auto.
Qed.
Lemma wordi_0 : ltac2:(TCodec.tc2 tcn__BigFactsDigits ";'H'=&Q4r1(0%3221&R0&Q=%2251%83941pUB:1").
Proof. intros v. unfold wordi. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r. reflexivity. Qed.
Lemma wordi_S : ltac2:(TCodec.tc2 tcn__BigFactsDigits "D'H'8&QMzr2%3221'=&Q4r3(1%116%4231&QL&Q=%2261%821;%:3@51p0<1pTNA1pUBC1").
Proof. intros v i.
intros. unfold wordi. rewrite Mpow_S. rewrite <- Z.div_div. reflexivity. rewrite M_val; lia. apply Mpow_pos.
Qed.
Lemma wlist_S : ltac2:(TCodec.tc2 tcn__BigFactsDigits "I'H'8&QMzr2%3221'=&QJ&Q3r3(1%117%4231(4&R0&Q=%2271&QL%1293%;21?%73D41%?3>91p0A1pU6F1pUBH1").
Proof. intros v n.
intros Hv. unfold wlist. rewrite <- cons_seq. simpl map. rewrite wordi_0. f_equal.
rewrite <- seq_shift, map_map. apply map_ext. intros; apply wordi_S; auto.
Qed.
Lemma val_wlist : ltac2:(TCodec.tc2 tcn__BigFactsDigits "G'H'8&QMzr2%3221'=&K&Q3r3%2216%411&R0&R3&Q=&R2%11<%4231%6291%=3C81p0?1pU6D1pUBF1").
Proof. intros v n.
revert v. induction n as [|n IH]; intros v Hv.
- change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
- rewrite wlist_S by auto. rewrite val_cons, IH. 2: apply Z.div_pos; [lia|rewrite M_val; lia].
rewrite Mpow_S. rewrite Z.rem_mul_r. lia. rewrite M_val; lia. apply Mpow_pos.
Qed.
Lemma val_wlist_small : ltac2:(TCodec.tc2 tcn__BigFactsDigits "J'H'8'<&QMzr2%3221&QN&R3&Q=&R2r1%211%5241%7291%=291'=&K&Q3r3%221?%411%63F13p081pU6G1pUBI1").
Proof. intros v n. intros. rewrite val_wlist by lia. apply Z.mod_small. lia. Qed.
Lemma wordi_zero : ltac2:(TCodec.tc2 tcn__BigFactsDigits "9'8'='H&Q4zr1%3221%63513pTN81").
Proof. intros i. unfold wordi. rewrite Z.div_0_l. reflexivity. pose proof (Mpow_pos i). lia. Qed.
Lemma wordi_val : ltac2:(TCodec.tc2 tcn__BigFactsDigits "B&QJ'8&Mr2%211'='H&Q4&Kr3%211%4218&QC%124:%93831p0;1pTN?1pUFA1").
Proof. intros ws i.
revert ws. induction i as [|i IH]; intros ws Hw.
- rewrite wordi_0. destruct ws as [|w t]. reflexivity. rewrite val_cons. inversion Hw; subst.
unfold nth_w; simpl. unfold wordZ in *. rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_small; auto.
- destruct ws as [|w t]. { rewrite val_nil, wordi_zero. reflexivity. }
inversion Hw; subst. rewrite wordi_S. 2: apply val_nonneg; auto.
rewrite val_cons. replace ((w + W.M * val t) / W.M) with (val t). apply IH; auto.
unfold wordZ in *. rewrite Z.mul_comm, Z_div_plus_full, Z.div_small; lia.
Qed.
Lemma wlist_val : ltac2:(TCodec.tc2 tcn__BigFactsDigits "@&QJ&Mr1%211'=&Q3&Kr2%211&6'H%2214%7241%93=16p0;1pUF?1").
Proof. intros ws.
intros Hw. apply (nth_ext _ _ 0 0). rewrite wlist_length; auto.
intros n Hn. rewrite wlist_length in Hn. pose proof (wlist_nth (val ws) (length ws) n Hn). unfold nth_w in H. rewrite H.
apply wordi_val; auto.
Qed.
Lemma reduced_length_nwords : ltac2:(TCodec.tc2 tcn__BigFactsDigits "E&QJ&Mr1%211&Q7r2%211'='8&6'Hr3%3221&Q1&K%114%311%:3951p0<1p0@1pUFD1").
Proof. intros ws.
intros Hw Hr. destruct ws as [|w t] eqn:E. reflexivity.
assert (NE: ws <> []) by (subst; discriminate). rewrite <- E in *.
pose proof (reduced_val_lower ws Hw Hr NE) as L. pose proof (val_bound ws Hw) as [_ U].
symmetry. apply nwords_unique. subst; simpl; lia.
replace (Z.of_nat (length ws - 1)) with (Z.of_nat (length ws) - 1). lia. subst ws; simpl length. lia.
Qed.
Lemma reduced_is_wlist : ltac2:(TCodec.tc2 tcn__BigFactsDigits "C&QJ&Mr1%211&Q7r2%211'=r3&Q3&K%113&Q1%112%5231%83?71p0:1p0>1pUFB1").
Proof. intros ws. intros. rewrite <- reduced_length_nwords by auto. symmetry. apply wlist_val; auto. Qed.
Lemma wlist_reduced : ltac2:(TCodec.tc2 tcn__BigFactsDigits ">'H&QMzr1%3221&Q7&Q3r2&Q1%112%4231%611p081pUB=1").
Proof. intros v.
intros Hv. destruct (Z.eq_dec v 0) as [->|]. { rewrite nwords_0. left. reflexivity. }
apply reduced_ws_intro. intros NE. rewrite wlist_length. rewrite wlist_nth. 2: pose proof (nwords_pos v ltac:(lia)); lia.
destruct (nwords_spec v ltac:(lia)) as [A B].
pose proof (nwords_pos v ltac:(lia)) as P. pose proof (Mpow_pos (nwords v - 1)) as Q.
assert (U: v / W.M ^ Z.of_nat (nwords v - 1) < W.M).
{ apply Z.div_lt_upper_bound. lia. rewrite Z.mul_comm, <- Mpow_S. replace (S (nwords v - 1)) with (nwords v) by lia. auto. }
assert (L: 1 <= v / W.M ^ Z.of_nat (nwords v - 1)).
{ apply Z.div_le_lower_bound. lia. lia. }
unfold wordi. rewrite Z.mod_small by lia. lia.
Qed.
Lemma wordi_high : ltac2:(TCodec.tc2 tcn__BigFactsDigits "D'H'8&QMzr2%3221'C&Q1r3%211%4216'=&Q4r4%2216%43?1<p061p0<1pTNA1pUBC1").
Proof. intros v i.
intros Hv Hi. unfold wordi. rewrite Z.div_small. reflexivity. split; auto.
eapply Z.lt_le_trans. apply nwords_lt_pow; auto. apply Mpow_le_mono; auto.
Qed.
Lemma wordi_top_nonzero : ltac2:(TCodec.tc2 tcn__BigFactsDigits "C'H&QNzr1%3221&?'=&Q4r2&B&Q1%113u1%4221%7261%93?1=%;11p0=1pUBB1").
Proof. intros v.
intros Hv. pose proof (wlist_reduced v ltac:(lia)) as R. pose proof (nwords_pos v Hv).
apply reduced_ws_top in R. rewrite wlist_length, wlist_nth in R by lia. exact R.
intros E. apply (f_equal (@length Z)) in E. rewrite wlist_length in E. simpl in E. lia.
Qed.
Lemma nwords_mul10_add : ltac2:(TCodec.tc2 tcn__BigFactsDigits "M'H&QMzr2%3221'<&QN&Q=%2251%4251'C&Q1&QK&R1+:r4%3221r3%6221%811&A%:16u1%3221%>251p0@1p0F1pTHK1pUBL1").
Proof. intros v d.
intros Hv Hd. apply (proj2 (nwords_le_iff (10 * v + d) (nwords v + 1) ltac:(lia))).
pose proof (nwords_lt_pow v Hv) as B. replace (nwords v + 1)%nat with (S (nwords v)) by lia. rewrite Mpow_S.
pose proof (Mpow_pos (nwords v)). rewrite M_val in *. nia.
Qed.
Lemma nwords_mul10_add_ge : ltac2:(TCodec.tc2 tcn__BigFactsDigits "E'H&QMzr2%3221'C&Q1r4%211&QK&R1+:%2215r3%5221%911%;281p0=1p0>1pTHC1pUBD1").
Proof. intros v d. intros. apply nwords_mono. lia. Qed.
Definition e3402 (m : Z) : Z := (m * 3402) / 1024.
Fixpoint pow10_check (k : nat) (p : Z) (m : Z) : bool :=
match k with
| O => true
| S k' => (p <? 2 ^ (e3402 m + 1)) && pow10_check k' (10 * p) (m + 1)
end.
Lemma pow10_check_sound : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q='8'H&QMzr1%3221'=r3&R3+:r2%3221%63;51'3&Q2r5r4%3321:(;%=3621'<%C26A&QN&QK&R2r7%211%42<1%62H1%9281+2&O%11F+1%;221%K251%>2I1p081pU0Q51p0D1p0L1p0Q41pU4Q91pU8Q:1pU2Q<1").
Proof. intros k.
induction k as [|k IH]; intros p m Hm Hp Hc j Hj. lia.
cbn [pow10_check] in Hc. apply andb_prop in Hc. destruct Hc as [H1 H2]. apply Z.ltb_lt in H1.
destruct (Z.eq_dec j m). { subst j p. exact H1. }
apply (IH (10 * p) (m + 1)); [lia| |exact H2|lia]. subst p. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia.
Qed.
Lemma pow10_base : ltac2:(TCodec.tc2 tcn__BigFactsDigits "9'='3&Q2uQP0+1z%43321(;%83721").
Proof. vm_compute. reflexivity. Qed.
Lemma pow10_1024 : ltac2:(TCodec.tc2 tcn__BigFactsDigits "9&QN&R3+:+QP0%3221+2+SZ:%6221%8241").
Proof. vm_compute. reflexivity. Qed.
Lemma e3402_shift : ltac2:(TCodec.tc2 tcn__BigFactsDigits "='H'=&O&QKr1+QP0%3221%511%614+SZ:%7221%:3;41pU4<1").
Proof. intros m. unfold e3402. rewrite Z.mul_add_distr_r. replace (1024 * 3402) with (3402 * 1024) by lia. rewrite Z_div_plus_full by lia. reflexivity. Qed.
Lemma pow10_lt_e3402 : ltac2:(TCodec.tc2 tcn__BigFactsDigits "D'H&QMzr1%3221&QN&R3+:r2%3221+2&QK&O%115+1%4221%:261%<281p0>1pU4C1").
Proof. intros m.
intros Hm. remember (Z.to_nat (m / 1024)) as q eqn:Eq. revert m Hm Eq.
induction q as [|q IH]; intros m Hm Eq.
- apply (pow10_check_sound 1024 1 0 ltac:(lia) eq_refl pow10_base).
pose proof (Z.div_mod m 1024 ltac:(lia)). pose proof (Z.mod_pos_bound m 1024 ltac:(lia)).
assert (m / 1024 = 0) by lia. simpl. lia.
- pose proof (Z.div_mod m 1024 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound m 1024 ltac:(lia)) as MB.
assert (Hm': 1024 <= m) by lia.
specialize (IH (m - 1024)). replace m with ((m - 1024) + 1024) by lia.
rewrite e3402_shift. rewrite Z.pow_add_r by lia.
assert (He: 0 <= e3402 (m - 1024)) by (unfold e3402; apply Z.div_pos; lia).
replace (e3402 (m - 1024) + 3402 + 1) with ((e3402 (m - 1024) + 1) + 3402) by lia. rewrite (Z.pow_add_r 2) by lia.
assert (IH': 10 ^ (m - 1024) < 2 ^ (e3402 (m - 1024) + 1)).
{ apply IH. lia. replace (m - 1024) with (m + (-1) * 1024) by lia. rewrite Z_div_plus_full by lia. lia. }
pose proof pow10_1024. pose proof (Z.pow_pos_nonneg 10 (m - 1024) ltac:(lia) ltac:(lia)).
apply Z.mul_lt_mono_nonneg; lia.
Qed.
Theorem pow10_lt_num_words_est : ltac2:(TCodec.tc2 tcn__BigFactsDigits "?'8&QN&R3+:&R2r1%211%5241&Q=&QD%115%711%:241%<261pU4>1").
Proof. intros m.
rewrite Mpow_nat. unfold num_words_est.
destruct (Nat.ltb_spec m 10).
- change (Z.of_nat 1%nat) with 1. eapply Z.le_lt_trans. apply Z.pow_le_mono_r. lia. apply (proj1 (Nat2Z.inj_le m 9)). lia.
vm_compute. reflexivity.
- pose proof (pow10_lt_e3402 (Z.of_nat m) ltac:(lia)) as P. unfold e3402 in P.
set (e := Z.of_nat m * 3402 / 1024) in *.
assert (He: 0 <= e) by (subst e; apply Z.div_pos; lia).
assert (Hq: e + 1 <= 64 * ((e + 1 + 63) / 64)).
{ pose proof (Z.div_mod (e + 1 + 63) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (e + 1 + 63) 64 ltac:(lia)). lia. }
rewrite Z2Nat.id. 2: apply Z.div_pos; lia.
eapply Z.lt_le_trans. exact P. apply Z.pow_le_mono_r. lia. exact Hq.
Qed.
Theorem nwords_bound : ltac2:(TCodec.tc2 tcn__BigFactsDigits "J'H'8'<&QMzr2%3221&QN&R3+:&R2r1%211%5241%7291%=291'C&Q1r3%211&QD%11@%6231p081pQDG1pUBI1").
Proof. intros v J.
intros Hv. apply (proj2 (nwords_le_iff v (num_words_est J) ltac:(lia))). eapply Z.lt_trans. apply (proj2 Hv). apply pow10_lt_num_words_est.
Qed.
Corollary nwords_bound_le : ltac2:(TCodec.tc2 tcn__BigFactsDigits "M'H'8'<&QMzr3%3221&QN&R3+:&R2r2%211%5241%7291%=291'C%12<6&Q1r5%211&QD%11A%7231p071p0:1pU4I1pQDJ1pUBL1").
Proof. intros v J m. intros. eapply Nat.le_trans. apply nwords_bound; eauto. apply num_words_est_mono; auto. Qed.
Lemma round_up_ge_S : ltac2:(TCodec.tc2 tcn__BigFactsDigits ":'8'C&Ar1u1%3221&QE%114%7231pU691").
Proof. intros n. pose proof (round_up_gt n). lia. Qed.
Theorem digit_step_no_realloc : ltac2:(TCodec.tc2 tcn__BigFactsDigits "QO'H'8'<&QMzr4%3221&QN&R3+:&R2r2%211%5241%7291%=291+9%>2<1%@2<1&Dr3%22@1'C&A&Q1r7%211u1%5221&QE&QD%11J%311%;251&R1%12J:%<11%>21:%@216&QKr6%2261%B11%D21@%F21<%Q:2Q94(1r5%211%Q711%Q:2Q91%Q<2:1%QB271%QC291%QD2@1%QE2F1p0Q31p0Q71p0Q;1pU4QJ1pQDQK1pTHQM1pUBQN1").
Proof. intros v d J m.
intros Hv Hd HJ. pose proof (round_up_ge_S (num_words_est m)) as R.
assert (B: 0 <= 10 * v + d < 10 ^ Z.of_nat (S J)). { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. }
pose proof (nwords_bound_le v J m Hv ltac:(lia)).
pose proof (nwords_bound_le (10 * v + d) (S J) m B ltac:(lia)).
pose proof (nwords_bound_le (10 * v) (S J) m ltac:(rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia) ltac:(lia)).
repeat split; try lia.
Qed.
Lemma nwords_after_growth : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q@'H'8'Cu1r3%3221'<&QMzr5%3221&QN&R1+:&R3&Q=&R2&Br4%221@%411%7261%:291%<2>1%B2>1%B2A7+B%D291%F231%?2@D&QKr7+1%3221%F251%H2A1%N2;1&Q1%11M%Q5218p041p0=1p0B1p0Q61pUDQ<1pU@Q=1pU2Q=1pUBQ?1").
Proof. intros v k t w.
intros Hk Hv Ht Hw. apply (proj2 (nwords_le_iff w k ltac:(lia))).
replace (W.M ^ Z.of_nat k) with (W.M ^ Z.of_nat (S (k - 1))) by (f_equal; lia). rewrite Mpow_S.
assert (P: 10 ^ t * 10 <= 10 ^ 19). { replace (10 ^ 19) with (10 ^ 18 * 10) by reflexivity. apply Z.mul_le_mono_nonneg_r. lia. apply Z.pow_le_mono_r; lia. }
assert (Q: 10 ^ 19 < W.M) by (rewrite M_val; reflexivity).
pose proof (Mpow_pos (k - 1)). pose proof (Z.pow_pos_nonneg 10 t ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma mod_Mpow_S : ltac2:(TCodec.tc2 tcn__BigFactsDigits "N'H'8&QMzr2%3221'=&R0r3&R3&Q=&R2(1%119%311%6251%9281&QK&R1&Q4%12<@%:1A%=2<1%5231%A2@2%8221%D3J:1p0F1pTNK1pUBM1").
Proof. intros v i.
intros Hv. rewrite Mpow_S, (Z.mul_comm W.M), Z.rem_mul_r. unfold wordi. lia. pose proof (Mpow_pos i); lia. rewrite M_val; lia.
Qed.
Lemma div_Mpow_S : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q0'H'8&QMzr2%3221'=&QL&QK&R1r4&R3&Q=&R2%11:%4231%7261r3%:221(1%11@%811%;2:1%@251%A279%A2?1%C21>%E3K41p0G1pTNL1pTDN1pT@O1").
Proof. intros a b i.
intros Hb. pose proof (Mpow_pos i). rewrite Mpow_S, (Z.mul_comm W.M). rewrite <- Z.div_div. 2: lia. 2: rewrite M_val; lia.
rewrite Z_div_plus_full_l. reflexivity. lia.
Qed.
Lemma split_Mpow_S : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q1'H'8&QMzr2%3221'=r3&QK&R1&QL&R3&Q=&R2(1%11;%311%6251%82;1%:212&Q4%12>A%91B%<2;1%?231%A261&R0%12D4%D231%G3MF1p0I1pTNN1pUBQ01").
Proof. intros v i. intros Hv. pose proof (mod_Mpow_S v i Hv). pose proof (Z.div_mod v (W.M ^ Z.of_nat (S i)) ltac:(pose proof (Mpow_pos (S i)); lia)). lia. Qed.
Definition mcarry (y v : Z) (i : nat) : Z := (y * (v mod W.M ^ Z.of_nat i)) / W.M ^ Z.of_nat i.
Lemma mcarry_0 : ltac2:(TCodec.tc2 tcn__BigFactsDigits ";'H'=&Q0r2r1(0%43321z%73821pUB91pUJ:1").
Proof. intros y v. unfold mcarry. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.mod_1_r, Z.mul_0_r. reflexivity. Qed.
Lemma mcarry_bound : ltac2:(TCodec.tc2 tcn__BigFactsDigits "G'H'8&QMzr3%3221'<&Q0r4r2%33261%9281&QO&R4+1%2271%42=1%?271%<271p0>1pTNC1pUBE1pUJF1").
Proof. intros y v i.
intros Hy. unfold mcarry. pose proof (Mpow_pos i) as P. pose proof (Z.mod_pos_bound v _ P) as [A B].
split. apply Z.div_pos; nia.
destruct (Z.eq_dec y 0). subst. rewrite Z.mul_0_l, Z.div_0_l; lia.
assert (y * (v mod W.M ^ Z.of_nat i) / W.M ^ Z.of_nat i < y). { apply Z.div_lt_upper_bound. lia. nia. } lia.
Qed.
Lemma mcarry_wordZ : ltac2:(TCodec.tc2 tcn__BigFactsDigits ">'H'8&Lr3%211&Q0r4r2%33251%711p061pTN:1pUB<1pUJ=1").
Proof. intros y v i. intros Hy. pose proof (mcarry_bound y v i ltac:(unfold wordZ in Hy; lia)). unfold wordZ in *. lia. Qed.
Theorem mul_limb_step : ltac2:(TCodec.tc2 tcn__BigFactsDigits "QH'H'8&Lr3%211&QMz%2214&Q4r4%2217&Q0r6r5%33215'9%12@@&Q<r2r7%3221&Q>&:r1%23HH1%4217'<'=&R1r9r8%3221%H21=%63Q1:1&5%13Q3Q3A&Q?&Q@%@3Q6Q6D%22@1%411%D261(1%11H%Q13?>1%B3Q=41%D2=1tUDQ?F1tTLQ0L1tTFQAQ31tUHQBQ81p0Q<1p0Q@1pTNQD1pUBQF1pUJQG1").
Proof. intros y v i.
intros Hy Hv. cbn zeta.
pose proof (wordi_range v i) as Hx. pose proof (DDproduct_correct (wordi v i) y Hx Hy) as DC.
pose proof (DDproduct_hi_bound (wordi v i) y Hx Hy) as HB.
destruct (DDproduct (wordi v i) y) as [hi lo]. cbn [fst snd] in *. destruct DC as (Whi & Wlo & E).
pose proof (mcarry_wordZ y v i Hy) as Wc. set (c := mcarry y v i) in *.
pose proof (add_carry lo c Wlo Wc) as AC. set (b := W.b2z (W.ltu (W.add lo c) lo)) in *.
pose proof (b2z_range (W.ltu (W.add lo c) lo)) as Rb. fold b in Rb.
pose proof (add_range lo c) as Ww. set (w := W.add lo c) in *.
pose proof (Mpow_pos i) as P. pose proof (Z.mod_pos_bound v _ P) as [MA MB].
assert (K1: (y * (v mod W.M ^ Z.of_nat (S i))) / W.M ^ Z.of_nat i = y * wordi v i + c).
{ rewrite mod_Mpow_S by auto.
replace (y * (wordi v i * W.M ^ Z.of_nat i + v mod W.M ^ Z.of_nat i)) with ((y * wordi v i) * W.M ^ Z.of_nat i + y * (v mod W.M ^ Z.of_nat i)) by lia.
rewrite Z_div_plus_full_l by lia. unfold c, mcarry. lia. }
split.
-
unfold wordi.
assert (Hyv: y * v = (y * (v / W.M ^ Z.of_nat (S i))) * W.M ^ Z.of_nat (S i) + y * (v mod W.M ^ Z.of_nat (S i))).
{ pose proof (Z.div_mod v (W.M ^ Z.of_nat (S i)) ltac:(pose proof (Mpow_pos (S i)); lia)). nia. }
set (q := v / W.M ^ Z.of_nat (S i)) in *. set (r := v mod W.M ^ Z.of_nat (S i)) in *.
rewrite Hyv. rewrite Mpow_S.
replace (y * q * (W.M * W.M ^ Z.of_nat i) + y * r) with (y * r + (y * q * W.M) * W.M ^ Z.of_nat i) by lia.
rewrite Z_div_plus_full by lia. rewrite K1.
replace (y * wordi v i + c + y * q * W.M) with ((lo + c) + (hi + y * q) * W.M) by lia.
rewrite Z_mod_plus_full. unfold w, W.add, W.wrap. reflexivity.
-
assert (K2: mcarry y v (S i) = (y * wordi v i + c) / W.M).
{ unfold mcarry at 1. rewrite (mod_Mpow_S v i) at 1 by auto. rewrite Z.mul_add_distr_l, Z.mul_assoc.
rewrite div_Mpow_S. 2: unfold wordZ in Hy; nia. unfold c, mcarry. reflexivity. }
rewrite K2. replace (y * wordi v i + c) with (w + (b + hi) * W.M) by lia. rewrite Z_div_plus_full by (rewrite M_val; lia).
unfold wordZ in Ww. rewrite Z.div_small by lia. rewrite add_small; auto. lia. unfold wordZ; rewrite M_val in *; lia. unfold wordZ in *; lia.
Qed.
Lemma mcarry_top : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q1'H'8&QMzr3%3221'<&QN&R3&Q=&R2r2%211%5241%72:1%92:1'=&Q0r5r4%3321@&QL&R1%1254%>1D%A2@1%5231%;3K71p0=1p0H1pU6M1pUBO1pUJQ01").
Proof. intros y v n. intros. unfold mcarry. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma mul_top_word : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q1'H'8&Lr3%211'<&QMz%2215&QN&R3&Q=&R2r2%211%5241%72=1%<291'=&Q0r5r4%3321C&Q4&R1%1254%321G%93K51p0;1p0I1pU6M1pUBO1pUJQ01").
Proof. intros y v n.
intros Hy Hv. rewrite mcarry_top by (unfold wordZ in Hy; lia). unfold wordi. symmetry. apply Z.mod_small. split.
apply Z.div_pos. unfold wordZ in Hy; nia. apply Mpow_pos.
apply Z.div_lt_upper_bound. apply Mpow_pos. unfold wordZ in Hy. pose proof (Mpow_pos n). nia.
Qed.
Lemma mul_value_bound : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q2'H'8&Lr3%211'<&QMz%2215&QN&R3&Q=&R2r2%211%5241%72=1%<291&R1r5r4%3221%@2?1(1%11E%=11%@2?1%B261%G261p0<1p0J1pU6N1pUBQ01pUJQ11").
Proof. intros y v n. intros Hy Hv. rewrite Mpow_S. unfold wordZ in Hy. pose proof (Mpow_pos n). nia. Qed.
Definition acarry (y v : Z) (i : nat) : Z := if W.M ^ Z.of_nat i <=? v mod W.M ^ Z.of_nat i + y then 1 else 0.
Lemma acarry_range : ltac2:(TCodec.tc2 tcn__BigFactsDigits "A'H'8'<&QMz&Nr3r2r1%43321%7261+1%9231%;231pTN=1pUB?1pUJ@1").
Proof. intros y v i. unfold acarry. destruct (Z.leb _ _); lia. Qed.
Lemma acarry_div : ltac2:(TCodec.tc2 tcn__BigFactsDigits "O'H'8'Cu1r1%3221&Lr4%211'=&Nr5r3%33261&QL&QK&R0&R3&Q=&R2%118%4231%62?1%821<%:213%@3I<1p0B1p0F1pTNK1pUBM1pUJN1").
Proof. intros y v i.
intros Hi Hy. pose proof (Mpow_pos i) as P. pose proof (Z.mod_pos_bound v _ P) as [A B].
assert (yM: y < W.M ^ Z.of_nat i). { unfold wordZ in Hy. eapply Z.lt_le_trans. apply (proj2 Hy). replace W.M with (W.M ^ Z.of_nat 1) at 1. apply Mpow_le_mono; lia. change (Z.of_nat 1) with 1. rewrite Z.pow_1_r. reflexivity. }
unfold acarry. destruct (Z.leb_spec (W.M ^ Z.of_nat i) (v mod W.M ^ Z.of_nat i + y)).
- apply Z.div_unique with (v mod W.M ^ Z.of_nat i + y - W.M ^ Z.of_nat i); unfold wordZ in Hy; lia.
- symmetry. apply Z.div_small. unfold wordZ in Hy; lia.
Qed.
Theorem add_limb0 : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q5'H&Lr2%211&QMz%2214&Q4r3(0%3221&Q>r1r5%3221'<'=&QKr6%2261%=21;%53E91&Q?&Q@%12<F%311&Nu1%23:?1%=3M41%?291tUDOA1tUHQ0F1p0K1p0O1pUBQ31pUJQ41").
Proof. intros y v.
intros Hy Hv. cbn zeta. pose proof (wordi_range v 0) as Hx.
rewrite acarry_div by (auto; lia). change (Z.of_nat 1) with 1. rewrite Z.pow_1_r.
rewrite !wordi_0. split.
- unfold W.add, W.wrap. rewrite Z.add_mod_idemp_l. reflexivity. rewrite M_val; lia.
- pose proof (add_carry (v mod W.M) y ltac:(rewrite <- wordi_0; apply wordi_range) Hy) as AC.
pose proof (add_range (v mod W.M) y) as R. unfold wordZ in R.
pose proof (b2z_range (W.ltu (W.add (v mod W.M) y) (v mod W.M))) as B.
apply Z.div_unique with (W.add (v mod W.M) y); lia.
Qed.
Theorem add_limbS y v i : wordZ y -> 0 <= v -> (1 <= i)%nat ->
let x := wordi v i in
let c := acarry y v i in
let d := W.add x c in
d = wordi (v + y) i /\
acarry y v (S i) = (if c =? 1 then W.b2z (W.ltu d c) else 0).
Proof.
intros Hy Hv Hi. cbn zeta. pose proof (wordi_range v i) as Hx.
pose proof (Mpow_pos i) as P. pose proof (Z.mod_pos_bound v _ P) as [A B].
assert (yM: y < W.M ^ Z.of_nat i). { unfold wordZ in Hy. eapply Z.lt_le_trans. apply (proj2 Hy). replace W.M with (W.M ^ Z.of_nat 1) at 1. apply Mpow_le_mono; lia. change (Z.of_nat 1) with 1. rewrite Z.pow_1_r. reflexivity. }
pose proof (acarry_div y v i Hi Hy) as CD. pose proof (acarry_range y v i) as CR.
set (c := acarry y v i) in *.
split.
- unfold wordi at 2.
assert (Hs: v + y = (v mod W.M ^ Z.of_nat i + y) + (wordi v i + v / W.M ^ Z.of_nat (S i) * W.M) * W.M ^ Z.of_nat i).
{ pose proof (split_Mpow_S v i Hv) as Sp. rewrite Mpow_S in Sp at 2. lia. }
rewrite Hs. rewrite Z_div_plus_full by lia. rewrite <- CD.
replace (c + (wordi v i + v / W.M ^ Z.of_nat (S i) * W.M)) with ((wordi v i + c) + (v / W.M ^ Z.of_nat (S i)) * W.M) by lia.
rewrite Z_mod_plus_full. unfold W.add, W.wrap. reflexivity.
- unfold acarry at 1. rewrite mod_Mpow_S by auto.
destruct (Z.eqb_spec c 1) as [C1|C0].
+
assert (R: W.M ^ Z.of_nat i <= v mod W.M ^ Z.of_nat i + y). { unfold c, acarry in C1. destruct (Z.leb_spec (W.M ^ Z.of_nat i) (v mod W.M ^ Z.of_nat i + y)); auto; lia. }
rewrite C1. unfold W.ltu, W.b2z, W.add, W.wrap. unfold wordZ in *.
destruct (Z.eq_dec (wordi v i) (W.M - 1)) as [T|T].
* rewrite T. replace (W.M - 1 + 1) with W.M by lia. rewrite Z.mod_same by lia. cbn [Z.ltb].
destruct (Z.leb_spec (W.M ^ Z.of_nat (S i)) ((W.M - 1) * W.M ^ Z.of_nat i + v mod W.M ^ Z.of_nat i + y)); auto.
exfalso. rewrite Mpow_S in *. nia.
* assert (Hw1: 0 <= wordi v i + 1 < W.M) by (clear -Hx T; lia). rewrite (Z.mod_small (wordi v i + 1) W.M Hw1).
clearbody c. destruct (Z.ltb_spec (wordi v i + 1) 1); try lia.
destruct (Z.leb_spec (W.M ^ Z.of_nat (S i)) (wordi v i * W.M ^ Z.of_nat i + v mod W.M ^ Z.of_nat i + y)); auto.
exfalso. rewrite Mpow_S in *. nia.
+ clearbody c. assert (c = 0) by lia. assert (R: v mod W.M ^ Z.of_nat i + y < W.M ^ Z.of_nat i).
{ destruct (Z_lt_le_dec (v mod W.M ^ Z.of_nat i + y) (W.M ^ Z.of_nat i)); auto. exfalso.
assert (1 <= (v mod W.M ^ Z.of_nat i + y) / W.M ^ Z.of_nat i) by (apply Z.div_le_lower_bound; lia). lia. }
destruct (Z.leb_spec (W.M ^ Z.of_nat (S i)) (wordi v i * W.M ^ Z.of_nat i + v mod W.M ^ Z.of_nat i + y)); auto.
exfalso. rewrite Mpow_S in *. unfold wordZ in Hx. nia.
Qed.
Lemma acarry_stays_0 : ltac2:(TCodec.tc2 tcn__BigFactsDigits "N'H'8&Lr3%211&QMz%2214'Cu1%2217'=&Nr6r5r4%43321%63A1;r7(1%116%93381%;3F1@p061p0>1p0B1p0F1pTNJ1pUBL1pUJM1").
Proof. intros y v i. intros. pose proof (add_limbS y v i H H0 H1) as [_ E]. rewrite H2 in E. simpl in E. exact E. Qed.
Lemma add_above_carry : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q8'H'8&Lr4%211&QMz%2214'Cu1%2217'=&Nr7r6r5%43321%63A1;%:243'<&Q4&QKr8r9%3221%521;%624<%@3K21%@356>%B3M1G%;231p0=1p0?1p0G1p0K1p0O1pU0Q31pTNQ41pUBQ61pUJQ71").
Proof. intros y v i j.
intros Hy Hv Hi Hc Hij. induction Hij.
- split; auto. pose proof (add_limbS y v i Hy Hv Hi) as [E _]. rewrite Hc in E. rewrite <- E. unfold W.add, W.wrap. rewrite Z.add_0_r. apply Z.mod_small. apply wordi_range.
- destruct IHHij as [E C]. pose proof (acarry_stays_0 y v m Hy Hv ltac:(lia) C) as C'. split; auto.
pose proof (add_limbS y v (S m) Hy Hv ltac:(lia)) as [E' _]. rewrite C' in E'. rewrite <- E'. unfold W.add, W.wrap. rewrite Z.add_0_r. apply Z.mod_small. apply wordi_range.
Qed.
Lemma add_top_word : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q6'H'8&Lr3%211'<&QMz%2215&QN&R3&Q=&R2r2%211%5241%72=1%<291'Cu1%221A'=&Nr6r5r4%43321&Q4&QK%1256%3215%:3O51p0<1p0@1p0N1pU6Q21pUBQ41pUJQ51").
Proof. intros y v n.
intros Hy Hv Hn. pose proof (add_limbS y v n Hy ltac:(lia) Hn) as [E _]. rewrite <- E.
rewrite (wordi_high v n) by (try lia; apply (proj2 (nwords_le_iff v n ltac:(lia))); lia).
unfold W.add, W.wrap. rewrite Z.add_0_l. symmetry; apply Z.mod_small. pose proof (acarry_range y v n). rewrite M_val; lia.
Qed.
Lemma add_value_bound : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q7'H'8&Lr3%211'<&QMz%2215&QN&R3&Q=&R2r2%211%5241%72=1%<291'Cu1%221A&QKr5r6%3221%C2B1(1r4%211%A11%D2C1%F271%K271p0=1p0A1p0O1pU6Q31pUBQ51pUJQ61").
Proof. intros y v n.
intros Hy Hv Hn. rewrite Mpow_S. unfold wordZ in Hy. pose proof (Mpow_pos n).
assert (W.M <= W.M ^ Z.of_nat n). { replace W.M with (W.M ^ Z.of_nat 1) at 1. apply Mpow_le_mono; lia. change (Z.of_nat 1) with 1. rewrite Z.pow_1_r; auto. }
rewrite M_val in *. nia.
Qed.
Lemma nwords_by_top : ltac2:(TCodec.tc2 tcn__BigFactsDigits "QC'H'8'Cu1r1%3221'<&QM&R3&Q=&R2&Br2%221:%411%7261r3%:221&QN(1%118%;11%>2=1%5271%B271'=&Q4r4%221<z%53N21&Q1r5%211%93Q117&?%I29Q1%;251%=3Q619%411%Q2261p0;1%71<%H1@%C3Q;;1p031%Q8251p0G1p0Q;1pU6Q@1pU8QB1").
Proof. intros p n.
intros Hn [L U]. pose proof (Mpow_pos n) as P.
assert (Hp: 0 < p) by (pose proof (Mpow_pos (n - 1)); lia).
assert (T: wordi p n = p / W.M ^ Z.of_nat n).
{ unfold wordi. apply Z.mod_small. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound. lia. rewrite Z.mul_comm, <- Mpow_S. auto. }
split; intros W0.
- rewrite T in W0. apply Z.div_small_iff in W0; try lia. assert (E: nwords p = n) by (apply nwords_unique; lia). split; auto.
rewrite <- E at 1. apply wordi_top_nonzero. lia.
- apply nwords_unique. lia. replace (S n - 1)%nat with n by lia. split; try lia. rewrite T in W0.
destruct (Z_lt_le_dec p (W.M ^ Z.of_nat n)); auto. exfalso. apply W0. apply Z.div_small. lia.
Qed.
Theorem mul_reduce_facts : ltac2:(TCodec.tc2 tcn__BigFactsDigits "QK'H&Lr2%211&QM+1r3%3221&QNz%2214'8&Q1r4%211&R1r6r5%3221'<r1%A2<1&R3&Q=&R2(1%11H%311%6251%E291%;291'=&Q4%12=O%33Q21I%G1Q1%53I1N&?&Bu1%22Q21%92Q71%;3Q:1Q1%611%I281p0;1%91<%F1Q9%A3Q5=1p031%O251%Q02E1tU8QDQ21tU6Q:Q71p0Q<1p0Q@1p0QE1pUBQI1pUJQJ1").
Proof. intros y v.
intros Hy Hy1 Hv. cbn zeta. destruct (nwords_spec v Hv) as [L U]. pose proof (nwords_pos v Hv) as Hn.
pose proof (mul_value_bound y v (nwords v) Hy ltac:(lia)) as B. split. auto.
apply nwords_by_top. auto. split. 2: lia. pose proof (Mpow_pos (nwords v - 1)). nia.
Qed.
Theorem add_reduce_facts : ltac2:(TCodec.tc2 tcn__BigFactsDigits "QG'H&Lr2%211&QNz%2214'8&Q1r3%211&QKr4r5%3221'<&QMr1%22=1&R3&Q=&R2(1%11E%311%6251%F291%<291'=&Q4%12=L%33O1J%H1N%53J1H&?&Bu1%22L1%92Q41%;3Q71Q2%611%J281p0;1%91<%F1Q3%A3Q6=1p031%Q0251%Q12E1tU8QAQ31tU6Q;Q81p0Q=1p0QA1pUBQE1pUJQF1").
Proof. intros y v.
intros Hy Hv. cbn zeta. destruct (nwords_spec v Hv) as [L U]. pose proof (nwords_pos v Hv) as Hn.
pose proof (add_value_bound y v (nwords v) Hy ltac:(lia) Hn) as B. split. auto.
apply nwords_by_top. auto. unfold wordZ in Hy. lia.
Qed.
Lemma nwords_small y : wordZ y -> nwords y = (if (y =? 0)%Z then 0%nat else 1%nat).
Proof. intros Hy. unfold wordZ in Hy. destruct (Z.eqb_spec y 0). subst; apply nwords_0. apply nwords_1. lia. Qed.
Theorem mul_word_is_wlist : ltac2:(TCodec.tc2 tcn__BigFactsDigits "QF'8'QI'H'QH&Q5r4r3%3221&Q6%114&L%116'C(1&QGr6%211%411r7%7221&5&QBr5%23581%43GE1'<'=&QJ&QFr1%211&Q3&R1&Kr8%711%311%521C&Q1%112%9231%?3>;1%L1=%A3Q;14%C231tU<Q<E1p0K1p0Q41p0Q71p0Q:1pU>Q?1pUJQA1pU:QC1pQFQE1").
Proof. intros N s y s0.
intros Hok Hr Hy Hn. destruct (mul_word_mspec N s y Hok Hy Hn s0) as [(Hok' & Hr' & Hv' & _) _].
cbn zeta. rewrite <- Hv'. split.
apply reduced_is_wlist. apply (okN_words N); auto. exact Hr'.
unfold size. apply reduced_length_nwords. apply (okN_words N); auto. exact Hr'.
Qed.
Theorem add_word_is_wlist : ltac2:(TCodec.tc2 tcn__BigFactsDigits "QF'8'QI'H'QH&Q5r4r3%3221&Q6%114&L%116'C(1&QGr6%211%411r7%7221&5&QAr5%23581%43GE1'<'=&QJ&QFr1%211&Q3&QK&Kr8%711%311%521C&Q1%112%9231%?3>;1%L1=%A3Q;14%C231tU<Q<E1p0K1p0Q41p0Q71p0Q:1pU>Q?1pUJQA1pU:QC1pQFQE1").
Proof. intros N s y s0.
intros Hok Hr Hy Hn. destruct (add_word_mspec N s y Hok Hy Hn s0) as [(Hok' & Hr' & Hv' & _) _].
cbn zeta. rewrite <- Hv'. split.
apply reduced_is_wlist. apply (okN_words N); auto. exact Hr'.
unfold size. apply reduced_length_nwords. apply (okN_words N); auto. exact Hr'.
Qed.
Lemma reduced_sto_shape : ltac2:(TCodec.tc2 tcn__BigFactsDigits "L'QI&Q8r1%211&Q6r2%211'<'=&QJ&QFr3%211&Q3&K%113&Q1%112%5231%;3:71'8&QG%11;%?3316%A251p0C1p0G1pU:K1").
Proof. intros s.
intros [Hw _] Hr. split. apply reduced_is_wlist; auto. unfold size. apply reduced_length_nwords; auto.
Qed.
Lemma dec_acc_app' : ltac2:(TCodec.tc2 tcn__BigFactsDigits "A'H'7%112'=&Q;r3&2r2r1%33921%6251%7264%8214%:3=31pTD<1pT@=1pTB@1").
Proof. intros acc a b. revert acc; induction a; intros; simpl; auto. Qed.
Lemma dec_firstn_S : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q3'7'H%211'8&Dr1&6r2%2271%5241'=&Q:&F(1%117r3%43?21%611&QK&R1+:%93D>6%;11%4231&R4&Gz%24JD<1+Q@%5221%<271%E3N>1p0G1pQDN1pTJQ01").
Proof. intros ds J.
intros HJ. unfold dec. rewrite (firstn_S_nth ds J HJ). rewrite dec_acc_app'. unfold nth_w. cbn [dec_acc]. lia.
Qed.
Lemma all_digits_firstn : ltac2:(TCodec.tc2 tcn__BigFactsDigits "C'7'H%211'8'='3&Q9r2%211(;%63521&Fr3%23<61%811%;3:16p061pQD>1pTJ@1").
Proof. intros ds J.
unfold all_digits. rewrite !forallb_forall. intros H x Hx. apply H. rewrite <- (firstn_skipn J ds). apply in_app_iff. auto.
Qed.
Lemma all_digits_Forall : ltac2:(TCodec.tc2 tcn__BigFactsDigits "G'7'H%211'E'<&QM+Q@r1%3221+QI%5231%7231qTF;1%:3<16'='3&Q9r2%211(;%63521p081pTJD1").
Proof. intros ds.
unfold all_digits. rewrite forallb_forall, Forall_forall. intros H x Hx. unfold is_digit. specialize (H x Hx).
rewrite andb_true_iff, !Z.leb_le. exact H.
Qed.
Lemma dec_firstn_bound : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q5'7'H%211'8'='3&Q9r2%211(;%63521'C&6r3%22=1%4281'<&QMz&Q:&Fr4%23E91%411%7261&QN&R3+:&R2%11@%4231%6281%@281p0B1p0H1pQDQ01pTJQ21").
Proof. intros ds J.
intros Hd HJ. pose proof (dec_bound (firstn J ds) (all_digits_firstn ds J Hd)) as B.
rewrite length_firstn, Nat.min_l in B by auto. exact B.
Qed.
Lemma dec_firstn_all : ltac2:(TCodec.tc2 tcn__BigFactsDigits ">'7'H%211'=&Q:&F&6r1%2271%43812%611%714%93;21pTJ;1").
Proof. intros ds. rewrite firstn_all. reflexivity. Qed.
Lemma digit_val : ltac2:(TCodec.tc2 tcn__BigFactsDigits "Q3'7'H%211'8'E'<&QM+Q@r1%3221+QI%5231%7231qTF<1r2%;3>21&D&6r3%22B1%4261z&R4&Gr4%24H714%421C%E261+9%G231%I231p0;1p0A1pQDN1pTJQ01").
Proof. intros ds J. intros H HJ. rewrite Forall_forall in H. specialize (H (nth J ds 0) (nth_In ds 0 HJ)). lia. Qed.
Theorem digit_step_facts : ltac2:(TCodec.tc2 tcn__BigFactsDigits "S8'7'H%211'8'E'<&QM+Q@r1%3221+QI%5231%7231qTF<1r3%;3>21&D&6r4%22B1%4261'Cr5%62F1%321:&Q:&Fr6%23K61%411&R4&Gr7z%34Q1721%521L(1%115r8%=3Q621%?11'=&QK&R1+:%221Or2%5221%73Q?Q81%Q;2@3+9%Q=251%Q?231%Q?2DQ7&QN&R3&R2%11C%32>1%52Q=1%QG271%QG2LQE%J1H%711%92D1%;2QI1%QM251&Q1%11QF&QD%11Q6%QB231%51K%QD213%71R2%QF215&Au1%22:1&QE%11:%QL231%62:5%QN213%82:7%R0215%RA231%RB261%RC2=1%RD2@1%RE2C1%RF2I1%RG2Q01%RH2Q91%RI2Q>1tT>RNQG1tTHROQM1tT<S0R41p0R:1p0R?1p0RE1pU4S21pQDS31pTJS51").
Proof. intros ds J m.
intros Hds HJ Hm. cbn zeta. pose proof (all_digits_Forall ds Hds) as AD.
pose proof (dec_firstn_S ds J HJ) as E. pose proof (digit_val ds J Hds HJ) as Dd.
pose proof (dec_firstn_bound ds J AD ltac:(lia)) as B. pose proof (dec_firstn_bound ds (S J) AD ltac:(lia)) as B'.
destruct (digit_step_no_realloc (dec (firstn J ds)) (nth J ds 0 - 48) J m B Dd ltac:(lia)) as (R1 & R2 & R3 & R4).
rewrite <- E in R3.
pose proof (nwords_bound_le (dec (firstn J ds)) J m B ltac:(lia)).
pose proof (nwords_bound_le (dec (firstn (S J) ds)) (S J) m B' ltac:(lia)).
assert (nwords (10 * dec (firstn J ds)) <= num_words_est m)%nat.
{ eapply Nat.le_trans. 2: exact H0. apply nwords_mono. rewrite E. lia. }
repeat split; auto; lia.
Qed.
