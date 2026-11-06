(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cn.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition fsqrt_s (md : rmode) (a : word) : word := nan_box (Z_to_bv 32 (fst (fp_sqrt fmt_single md (bv_unsigned (unbox_s a))))).
Definition fmin_d (a b : word) : word := Z_to_bv 64 (fst (fp_minmax fmt_double false (bv_unsigned a) (bv_unsigned b))).
Definition fmax_d (a b : word) : word := Z_to_bv 64 (fst (fp_minmax fmt_double true (bv_unsigned a) (bv_unsigned b))).
Definition fmin_s (a b : word) : word := nan_box (Z_to_bv 32 (fst (fp_minmax fmt_single false (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))))).
Definition fmax_s (a b : word) : word := nan_box (Z_to_bv 32 (fst (fp_minmax fmt_single true (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))))).
Definition fminmax_d (is_max : bool) : word -> word -> word := if is_max then fmax_d else fmin_d.
Definition fminmax_s (is_max : bool) : word -> word -> word := if is_max then fmax_s else fmin_s.
Definition fclass_d (a : word) : word := Z_to_bv 64 (fp_class fmt_double (bv_unsigned a)).
Definition fclass_s (a : word) : word := Z_to_bv 64 (fp_class fmt_single (bv_unsigned (unbox_s a))).

Definition fma_a (op : fmaop) (f : format) (a : Z) : Z :=
match op with F_MADD | F_MSUB => a | F_NMSUB | F_NMADD => fp_neg f a end.
Definition fma_z (op : fmaop) (f : format) (z : Z) : Z :=
match op with F_MADD | F_NMSUB => z | F_MSUB | F_NMADD => fp_neg f z end.
Definition fmadd_d (md : rmode) (a b c : word) : word :=
Z_to_bv 64 (fst (fp_fma fmt_double md (bv_unsigned a) (bv_unsigned b) (bv_unsigned c))).
Definition fmsub_d (md : rmode) (a b c : word) : word :=
Z_to_bv 64 (fst (fp_fma fmt_double md (bv_unsigned a) (bv_unsigned b) (fp_neg fmt_double (bv_unsigned c)))).
Definition fnmsub_d (md : rmode) (a b c : word) : word :=
Z_to_bv 64 (fst (fp_fma fmt_double md (fp_neg fmt_double (bv_unsigned a)) (bv_unsigned b) (bv_unsigned c))).
Definition fnmadd_d (md : rmode) (a b c : word) : word :=
Z_to_bv 64 (fst (fp_fma fmt_double md (fp_neg fmt_double (bv_unsigned a)) (bv_unsigned b) (fp_neg fmt_double (bv_unsigned c)))).
Definition fma_d (op : fmaop) : rmode -> word -> word -> word -> word :=
match op with F_MADD => fmadd_d | F_MSUB => fmsub_d | F_NMSUB => fnmsub_d | F_NMADD => fnmadd_d end.
Definition fmadd_s (md : rmode) (a b c : word) : word :=
nan_box (Z_to_bv 32 (fst (fp_fma fmt_single md (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b)) (bv_unsigned (unbox_s c))))).
Definition fmsub_s (md : rmode) (a b c : word) : word :=
nan_box (Z_to_bv 32 (fst (fp_fma fmt_single md (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b)) (fp_neg fmt_single (bv_unsigned (unbox_s c)))))).
Definition fnmsub_s (md : rmode) (a b c : word) : word :=
nan_box (Z_to_bv 32 (fst (fp_fma fmt_single md (fp_neg fmt_single (bv_unsigned (unbox_s a))) (bv_unsigned (unbox_s b)) (bv_unsigned (unbox_s c))))).
Definition fnmadd_s (md : rmode) (a b c : word) : word :=
nan_box (Z_to_bv 32 (fst (fp_fma fmt_single md (fp_neg fmt_single (bv_unsigned (unbox_s a))) (bv_unsigned (unbox_s b)) (fp_neg fmt_single (bv_unsigned (unbox_s c)))))).
Definition fma_s (op : fmaop) : rmode -> word -> word -> word -> word :=
match op with F_MADD => fmadd_s | F_MSUB => fmsub_s | F_NMSUB => fnmsub_s | F_NMADD => fnmadd_s end.
Definition fma_fl (op : fmaop) (f : format) (md : rmode) (a b z : Z) : fflags :=
snd (fp_fma f md (fma_a op f a) b (fma_z op f z)).

Definition fsgnj_s (op : fsgnop) (a b : word) : word := nan_box (sgnj_val op (unbox_s a) (unbox_s b)).
Definition fmv_s (a : word) : word := nan_box (unbox_s a).
Definition fabs_s (a : word) : word := nan_box (Z_to_bv 32 (Z.land (bv_unsigned (unbox_s a)) (Z.ones 31))).
Definition fneg_s (a : word) : word := nan_box (Z_to_bv 32 (Z.lxor (bv_unsigned (unbox_s a)) (2^31))).

Definition fcvt_s_l (md : rmode) (x : word) : word := nan_box (Z_to_bv 32 (fst (fp_of_int fmt_single md true 64 (bv_unsigned x)))).
Definition fcvt_s_lu (md : rmode) (x : word) : word := nan_box (Z_to_bv 32 (fst (fp_of_int fmt_single md false 64 (bv_unsigned x)))).
Definition fcvt_w_s (md : rmode) (a : word) : word := sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_single md true 32 (bv_unsigned (unbox_s a))))).
Definition fcvt_wu_s (md : rmode) (a : word) : word := sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_single md false 32 (bv_unsigned (unbox_s a))))).
Definition fcvt_l_s (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_to_int fmt_single md true 64 (bv_unsigned (unbox_s a)))).
Definition fcvt_lu_s (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_to_int fmt_single md false 64 (bv_unsigned (unbox_s a)))).

Lemma exec_fsqrt_s : forall sz rd rs1 rm c md,
rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
exec sz (Fsqrt FMT_S rd rs1 rm) c =
EDone (fset rd (fsqrt_s md (fget c rs1))
(accrue (snd (fp_sqrt fmt_single md (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof.
intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
cbn [fp_format fread fwrite]. unfold fsqrt_s. destruct (fp_sqrt _ _ _); reflexivity.
Qed.

Lemma exec_fminmax_d' : forall sz op rd rs1 rs2 c,
exec sz (Fminmax op FMT_D rd rs1 rs2) c =
EDone (fset rd (fminmax_d (match op with F_MIN => false | F_MAX => true end) (fget c rs1) (fget c rs2))
(accrue (snd (fp_minmax fmt_double (match op with F_MIN => false | F_MAX => true end) (bv_unsigned (fget c rs1)) (bv_unsigned (fget c rs2))))
(with_pc (c_pc c + sz) c))).
Proof. intros. unfold exec. cbn [fp_format fread fwrite]. unfold fminmax_d, fmin_d, fmax_d. destruct op; destruct (fp_minmax _ _ _ _); reflexivity. Qed.

Lemma exec_fminmax_s : forall sz op rd rs1 rs2 c,
exec sz (Fminmax op FMT_S rd rs1 rs2) c =
EDone (fset rd (fminmax_s (match op with F_MIN => false | F_MAX => true end) (fget c rs1) (fget c rs2))
(accrue (snd (fp_minmax fmt_single (match op with F_MIN => false | F_MAX => true end) (bv_unsigned (unbox_s (fget c rs1))) (bv_unsigned (unbox_s (fget c rs2)))))
(with_pc (c_pc c + sz) c))).
Proof. intros. unfold exec. cbn [fp_format fread fwrite]. unfold fminmax_s, fmin_s, fmax_s. destruct op; destruct (fp_minmax _ _ _ _); reflexivity. Qed.

Lemma exec_fclass_d : forall sz rd rs1 c,
exec sz (Fclass FMT_D rd rs1) c = EDone (rset rd (fclass_d (fget c rs1)) (with_pc (c_pc c + sz) c)).
Proof. reflexivity. Qed.
Lemma exec_fclass_s : forall sz rd rs1 c,
exec sz (Fclass FMT_S rd rs1) c = EDone (rset rd (fclass_s (fget c rs1)) (with_pc (c_pc c + sz) c)).
Proof. reflexivity. Qed.

Lemma exec_fma_d : forall sz op rd rs1 rs2 rs3 rm c md,
rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
exec sz (Fma op FMT_D rd rs1 rs2 rs3 rm) c =
EDone (fset rd (fma_d op md (fget c rs1) (fget c rs2) (fget c rs3))
(accrue (fma_fl op fmt_double md (bv_unsigned (fget c rs1)) (bv_unsigned (fget c rs2)) (bv_unsigned (fget c rs3)))
(with_pc (c_pc c + sz) c))).
Proof.
intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
cbn [fp_format fread fwrite]. unfold fma_d, fma_fl, fma_a, fma_z, fmadd_d, fmsub_d, fnmsub_d, fnmadd_d.
destruct op; destruct (fp_fma _ _ _ _ _); reflexivity.
Qed.

Lemma exec_fma_s : forall sz op rd rs1 rs2 rs3 rm c md,
rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
exec sz (Fma op FMT_S rd rs1 rs2 rs3 rm) c =
EDone (fset rd (fma_s op md (fget c rs1) (fget c rs2) (fget c rs3))
(accrue (fma_fl op fmt_single md (bv_unsigned (unbox_s (fget c rs1))) (bv_unsigned (unbox_s (fget c rs2))) (bv_unsigned (unbox_s (fget c rs3))))
(with_pc (c_pc c + sz) c))).
Proof.
intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
cbn [fp_format fread fwrite]. unfold fma_s, fma_fl, fma_a, fma_z, fmadd_s, fmsub_s, fnmsub_s, fnmadd_s.
destruct op; destruct (fp_fma _ _ _ _ _); reflexivity.
Qed.

Lemma exec_fsgnj_s : forall sz op rd rs1 rs2 c,
exec sz (Fsgnj op FMT_S rd rs1 rs2) c = EDone (fset rd (fsgnj_s op (fget c rs1) (fget c rs2)) (with_pc (c_pc c + sz) c)).
Proof. reflexivity. Qed.

Lemma exec_fcvt_w_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
exec sz (Fcvt FC_W FC_S rd rs1 rm) c =
EDone (rset rd (fcvt_w_s md (fget c rs1)) (accrue (snd (fp_to_int fmt_single md true 32 (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_w_s. fcvt_tac H. Qed.
Lemma exec_fcvt_wu_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
exec sz (Fcvt FC_WU FC_S rd rs1 rm) c =
EDone (rset rd (fcvt_wu_s md (fget c rs1)) (accrue (snd (fp_to_int fmt_single md false 32 (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_wu_s. fcvt_tac H. Qed.
Lemma exec_fcvt_l_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
exec sz (Fcvt FC_L FC_S rd rs1 rm) c =
EDone (rset rd (fcvt_l_s md (fget c rs1)) (accrue (snd (fp_to_int fmt_single md true 64 (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_l_s. fcvt_tac H. Qed.
Lemma exec_fcvt_lu_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
exec sz (Fcvt FC_LU FC_S rd rs1 rm) c =
EDone (rset rd (fcvt_lu_s md (fget c rs1)) (accrue (snd (fp_to_int fmt_single md false 64 (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_lu_s. fcvt_tac H. Qed.
Lemma exec_fcvt_s_l : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
exec sz (Fcvt FC_S FC_L rd rs1 rm) c =
EDone (fset rd (fcvt_s_l md (rget c rs1)) (accrue (snd (fp_of_int fmt_single md true 64 (bv_unsigned (rget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_s_l. fcvt_tac H. Qed.
Lemma exec_fcvt_s_lu : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
exec sz (Fcvt FC_S FC_LU rd rs1 rm) c =
EDone (fset rd (fcvt_s_lu md (rget c rs1)) (accrue (snd (fp_of_int fmt_single md false 64 (bv_unsigned (rget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_s_lu. fcvt_tac H. Qed.

Definition sgnj_sign32 (op : fsgnop) (a b : bv 32) : bool :=
let sa := Z.testbit (bv_unsigned a) 31 in
let sb := Z.testbit (bv_unsigned b) 31 in
match op with F_SGNJ => sb | F_SGNJN => negb sb | F_SGNJX => xorb sa sb end.

Lemma sgnj_val_unsigned32 : forall op (a b : bv 32),
bv_unsigned (sgnj_val op a b) = Z.lor (Z.shiftl (if sgnj_sign32 op a b then 1 else 0) 31) (bv_unsigned a mod 2^31)%Z.
Proof.
intros op a b. unfold sgnj_val, bit, sgnj_sign32. change (Z.of_N (32-1)) with 31%Z.
rewrite bv_concat_unsigned by reflexivity.
rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
change (Z.of_N (32-1)) with 31%Z.
destruct (match op with F_SGNJ => _ | _ => _ end); reflexivity.
Qed.

Lemma testbit_sign31 : forall (c : bool) i, (0 <= i)%Z ->
Z.testbit (Z.shiftl (if c then 1 else 0) 31) i = (c && Z.eqb i 31)%bool.
Proof.
intros c i Hi. destruct (Z.lt_ge_cases i 31).
- rewrite Z.shiftl_spec_low by lia. destruct c; cbn; [|reflexivity]. symmetry. apply Z.eqb_neq. lia.
- rewrite Z.shiftl_spec_high by lia. destruct c.
+ destruct (Z.eqb_spec i 31). { subst. reflexivity. } cbn. apply Z.bits_above_log2; cbn; lia.
+ rewrite Z.bits_0. reflexivity.
Qed.

Lemma testbit_bv32_high : forall (a : bv 32) i, (32 <= i)%Z -> Z.testbit (bv_unsigned a) i = false.
Proof.
intros a i Hi. pose proof (bv_unsigned_in_range 32 a) as Hr. unfold bv_modulus in Hr.
destruct (Z.eq_dec (bv_unsigned a) 0) as [E|E]. { rewrite E. apply Z.bits_0. }
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32%Z; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma Z_lxor_lt_pow2 : forall a b n, (0 < n)%Z -> (0 <= a < 2^n)%Z -> (0 <= b < 2^n)%Z -> (0 <= Z.lxor a b < 2^n)%Z.
Proof.
intros a b n Hn Ha Hb.
assert (H0 : (0 <= Z.lxor a b)%Z) by (apply Z.lxor_nonneg; lia).
split; [exact H0|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
apply Z.log2_lt_pow2; [lia|].
pose proof (Z.log2_lxor a b (proj1 Ha) (proj1 Hb)) as Hl.
assert (Z.log2 a < n)%Z by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
assert (Z.log2 b < n)%Z by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
lia.
Qed.

Ltac sgnj_bits32 a :=
apply bv_eq; rewrite sgnj_val_unsigned32; unfold sgnj_sign32; rewrite ?Z_to_bv_unsigned;
pose proof (bv_unsigned_in_range 32 a);
try (rewrite bv_wrap_small; [| unfold bv_modulus in *;
solve [ rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound (bv_unsigned a) (2^31)); lia
| apply Z_lxor_lt_pow2; lia ] ]);
apply Z.bits_inj'; intros i Hi;
rewrite ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec, ?testbit_sign31, <- ?Z.land_ones, ?Z.land_spec by lia;
destruct (Z.lt_ge_cases i 31);
[ rewrite ?Z.ones_spec_low, ?(Z.pow2_bits_false 31) by lia; replace (Z.eqb i 31) with false by (symmetry; apply Z.eqb_neq; lia)
| rewrite ?Z.ones_spec_high by lia;
destruct (Z.eqb_spec i 31); [subst; rewrite ?Z.pow2_bits_true by lia | rewrite ?(testbit_bv32_high a i), ?(Z.pow2_bits_false 31 i) by lia] ];
repeat match goal with |- context [Z.testbit ?x ?k] => destruct (Z.testbit x k) end; reflexivity.

Lemma sgnj_self32 : forall a : bv 32, sgnj_val F_SGNJ a a = a.
Proof. intros a. sgnj_bits32 a. Qed.
Lemma sgnjx_self32 : forall a : bv 32, sgnj_val F_SGNJX a a = Z_to_bv 32 (Z.land (bv_unsigned a) (Z.ones 31)).
Proof. intros a. sgnj_bits32 a. Qed.
Lemma sgnjn_self32 : forall a : bv 32, sgnj_val F_SGNJN a a = Z_to_bv 32 (Z.lxor (bv_unsigned a) (2^31)).
Proof. intros a. sgnj_bits32 a. Qed.

Lemma fsgnj_s_self : forall a, fsgnj_s F_SGNJ a a = fmv_s a.
Proof. intros a. unfold fsgnj_s, fmv_s. rewrite sgnj_self32. reflexivity. Qed.
Lemma fsgnjx_s_self : forall a, fsgnj_s F_SGNJX a a = fabs_s a.
Proof. intros a. unfold fsgnj_s, fabs_s. rewrite sgnjx_self32. reflexivity. Qed.
Lemma fsgnjn_s_self : forall a, fsgnj_s F_SGNJN a a = fneg_s a.
Proof. intros a. unfold fsgnj_s, fneg_s. rewrite sgnjn_self32. reflexivity. Qed.
Lemma fmv_s_nan_box : forall v, fmv_s (nan_box v) = nan_box v.
Proof. intros v. unfold fmv_s. rewrite unbox_nan_box. reflexivity. Qed.

Lemma extract_le4_low32 : forall v : word, bv_extract 0 32 (le_bytes_to_word (le4 v)) = low32 v.
Proof.
intros v. apply bv_eq. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
change (Z.of_N 32) with 32%Z. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Definition fzero_s : word := Z_to_bv 64 0xFFFFFFFF00000000.

Lemma bword_eqz_true : forall b, bv_eqb (bword b) (Z_to_bv 64 0) = true -> b = false.
Proof. intros b H; rewrite bword_eqb0 in H; destruct b; cbn in H; congruence. Qed.
Lemma bword_eqz_false : forall b, bv_eqb (bword b) (Z_to_bv 64 0) = false -> b = true.
Proof. intros b H; rewrite bword_eqb0 in H; destruct b; cbn in H; congruence. Qed.
Lemma bword_nez_true : forall b, negb (bv_eqb (bword b) (Z_to_bv 64 0)) = true -> b = true.
Proof. intros b H; rewrite bword_eqb0 in H; destruct b; cbn in H; congruence. Qed.
Lemma bword_nez_false : forall b, negb (bv_eqb (bword b) (Z_to_bv 64 0)) = false -> b = false.
Proof. intros b H; rewrite bword_eqb0 in H; destruct b; cbn in H; congruence. Qed.
Ltac bfact B :=
first [ apply bword_eqz_true in B | apply bword_eqz_false in B
| apply bword_nez_true in B | apply bword_nez_false in B ].
