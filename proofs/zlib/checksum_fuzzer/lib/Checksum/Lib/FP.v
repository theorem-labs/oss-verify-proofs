(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tset_tset_same {A} (p : positive) (x y : A) t : tset p x (tset p y t) = tset p x t.
Proof. revert t; induction p; intros [|l v r]; cbn; try rewrite IHp; reflexivity. Qed.

Lemma tset_tset_comm {A} (p q : positive) (x y : A) t :
  p <> q -> tset p x (tset q y t) = tset q y (tset p x t).
Proof.
  revert q t; induction p; intros [q|q|] [|l v r] Hne; cbn; try reflexivity; try congruence;
  try (rewrite IHp by congruence; reflexivity).
Qed.

Lemma bvmap_set_set_same : forall (k : reg) (x y : word) (F : bvmap 5 word),
  bvmap_set k x (bvmap_set k y F) = bvmap_set k x F.
Proof. intros. unfold bvmap_set. apply tset_tset_same. Qed.

(* [comment removed for export] *)
Lemma bvmap_set_set_same' : forall (k k' : reg) (x y : word) (F : bvmap 5 word),
  bv_unsigned k = bv_unsigned k' ->
  bvmap_set k x (bvmap_set k' y F) = bvmap_set k x F.
Proof. intros k k' x y F H. replace k' with k by (apply bv_eq; exact H). apply bvmap_set_set_same. Qed.

Lemma bvmap_set_set_comm : forall (k k' : reg) (x y : word) (F : bvmap 5 word),
  bv_eqb k k' = false ->
  bvmap_set k x (bvmap_set k' y F) = bvmap_set k' y (bvmap_set k x F).
Proof.
  intros k k' x y F H. unfold bvmap_set. apply tset_tset_comm.
  intros E. unfold bv_eqb in H. apply Z.eqb_neq in H. apply H.
  pose proof (bv_key_inj k k' E). congruence.
Qed.

Lemma freg_get_same : forall (F : bvmap 5 word) (k r : reg) v,
  bv_unsigned k = bv_unsigned r -> reg_get (bvmap_set k v F) r = v.
Proof. intros F k r v H. replace r with k by (apply bv_eq; exact H). apply reg_get_set_same. Qed.

Lemma freg_get_other : forall (F : bvmap 5 word) (k r : reg) v,
  bv_eqb k r = false -> reg_get (bvmap_set k v F) r = reg_get F r.
Proof.
  intros F k r v H. apply reg_get_set_other. unfold bv_eqb in H. apply Z.eqb_neq in H.
  intros E. apply H. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition frm0 (fc : bv 32) : Prop := Z.land (Z.shiftr (bv_unsigned fc) 5) 7 = 0%Z.

(* [comment removed for export] *)

Lemma rmode_dyn : forall (rm : bv 3) (c : core),
  bv_unsigned rm = 7%Z -> frm0 (c_fcsr c) ->
  rmode_of_field (bv_unsigned rm) (frm_of c) = Some RNE.
Proof. intros rm c Hrm H. unfold rmode_of_field, frm_of. rewrite Hrm. cbn [Z.eqb Pos.eqb]. unfold frm0 in H. rewrite H. reflexivity. Qed.

Lemma rmode_static : forall (rm : bv 3) (c : core) md,
  bv_eqb rm (Z_to_bv 3 7) = false -> rmode_of_Z (bv_unsigned rm) = Some md ->
  rmode_of_field (bv_unsigned rm) (frm_of c) = Some md.
Proof.
  intros rm c md H Hmd. unfold rmode_of_field. unfold bv_eqb in H.
  change (bv_unsigned (Z_to_bv 3 7)) with 7%Z in H. rewrite H. exact Hmd.
Qed.

Lemma fflags_bits_range : forall fl, (0 <= fflags_bits fl < 32)%Z.
Proof. intros [[] [] [] [] []]; cbv; split; congruence. Qed.

Lemma land_shiftr_lor_low : forall a b k n, (0 <= a)%Z -> (0 <= b < 2^k)%Z -> (0 <= k)%Z -> (0 <= n)%Z ->
  Z.land (Z.shiftr (Z.lor a b) k) n = Z.land (Z.shiftr a k) n.
Proof.
  intros a b k n Ha Hb Hk Hn. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, !Z.shiftr_spec, Z.lor_spec by lia.
  replace (Z.testbit b (i + k)) with false. { rewrite orb_false_r. reflexivity. }
  symmetry. destruct (Z.eq_dec b 0). { subst. apply Z.bits_0. }
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma Z_lor_lt_pow2 : forall a b n, (0 <= a < 2^n)%Z -> (0 <= b < 2^n)%Z -> (0 <= Z.lor a b < 2^n)%Z.
Proof.
  intros a b n Ha Hb.
  assert (Hn : (0 <= n)%Z). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  split. { apply Z.lor_nonneg; lia. }
  destruct (Z.eq_dec a 0). { subst. rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0). { subst. rewrite Z.lor_0_r. lia. }
  assert (Hp : (0 < Z.lor a b)%Z). { pose proof (Z.lor_nonneg a b). destruct (Z.eq_dec (Z.lor a b) 0); [|lia]. apply Z.lor_eq_0_iff in e. lia. }
  apply Z.log2_lt_pow2; [exact Hp|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma frm0_accrue : forall (fc : bv 32) fl,
  frm0 fc -> frm0 (Z_to_bv 32 (Z.lor (bv_unsigned fc) (fflags_bits fl))).
Proof.
  intros fc fl H. unfold frm0 in *.
  pose proof (bv_unsigned_in_range 32 fc) as Hf. unfold bv_modulus in Hf.
  pose proof (fflags_bits_range fl) as Hb.
  assert (HR : (0 <= Z.lor (bv_unsigned fc) (fflags_bits fl) < 2^32)%Z).
  { apply Z_lor_lt_pow2; lia. }
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  rewrite land_shiftr_lor_low by lia. exact H.
Qed.

Lemma land7_shiftr5_zero_iff : forall z, (0 <= z)%Z ->
  (Z.land (Z.shiftr z 5) 7 = 0 <-> (forall i, 5 <= i <= 7 -> Z.testbit z i = false))%Z.
Proof.
  intros z Hz. change 7%Z with (Z.ones 3) at 1. split.
  - intros H i Hi. apply (f_equal (fun x => Z.testbit x (i - 5))) in H.
    rewrite Z.bits_0, Z.land_spec, Z.shiftr_spec, Z.ones_spec_low in H by lia.
    rewrite andb_true_r in H. replace (i - 5 + 5)%Z with i in H by lia. exact H.
  - intros H. apply Z.bits_inj'. intros j Hj. rewrite Z.bits_0, Z.land_spec, Z.shiftr_spec by lia.
    destruct (Z.ltb_spec0 j 3).
    + rewrite H by lia. reflexivity.
    + rewrite Z.ones_spec_high by lia. apply andb_false_r.
Qed.

Lemma testbit_mod_pow2_low : forall z n i, (0 <= i < n)%Z -> Z.testbit (z mod 2^n) i = Z.testbit z i.
Proof. intros. rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_low by lia. apply andb_true_r. Qed.

(* [comment removed for export] *)
Lemma frm0_slice_set_fflags : forall (fc : bv 32) (v : word),
  frm0 fc -> frm0 (slice_set fc 0 5 v).
Proof.
  intros fc v H. unfold frm0, slice_set in *.
  pose proof (bv_unsigned_in_range 32 fc) as Hf. unfold bv_modulus in Hf.
  rewrite Z_to_bv_unsigned. change (bv_wrap 32 ?x) with (x mod 2^32)%Z.
  apply land7_shiftr5_zero_iff. { apply Z.mod_pos_bound. lia. }
  pose proof (proj1 (land7_shiftr5_zero_iff (bv_unsigned fc) ltac:(lia)) H) as H'.
  intros i Hi. rewrite testbit_mod_pow2_low by lia.
  change (Z.shiftl (Z.ones 5) 0) with 31%Z.
  rewrite Z.lor_spec, !Z.land_spec, Z.lnot_spec by lia. rewrite H' by lia.
  change 31%Z with (Z.ones 5). rewrite Z.ones_spec_high by lia. cbn. apply andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma frm0_slice_get : forall fc, frm0 fc -> slice_get fc 5 3 = Z_to_bv 64 0.
Proof. intros fc H. unfold slice_get. change (Z.ones 3) with 7%Z. unfold frm0 in H. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fari_sem (op : fariop) : format -> rmode -> Z -> Z -> Z * fflags :=
  match op with F_ADD => fp_add | F_SUB => fp_sub | F_MUL => fp_mul | F_DIV => fp_div end.
Definition fcmp_sem (op : fcmpop) : format -> Z -> Z -> bool * fflags :=
  match op with F_EQ => fp_eq | F_LT => fp_lt | F_LE => fp_le end.

(* [comment removed for export] *)
Definition fadd_d (md : rmode) (a b : word) : word := Z_to_bv 64 (fst (fp_add fmt_double md (bv_unsigned a) (bv_unsigned b))).
Definition fsub_d (md : rmode) (a b : word) : word := Z_to_bv 64 (fst (fp_sub fmt_double md (bv_unsigned a) (bv_unsigned b))).
Definition fmul_d (md : rmode) (a b : word) : word := Z_to_bv 64 (fst (fp_mul fmt_double md (bv_unsigned a) (bv_unsigned b))).
Definition fdiv_d (md : rmode) (a b : word) : word := Z_to_bv 64 (fst (fp_div fmt_double md (bv_unsigned a) (bv_unsigned b))).
Definition fari_d (op : fariop) : rmode -> word -> word -> word :=
  match op with F_ADD => fadd_d | F_SUB => fsub_d | F_MUL => fmul_d | F_DIV => fdiv_d end.
Definition fsqrt_d (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_sqrt fmt_double md (bv_unsigned a))).

Definition feq_d (a b : word) : bool := fst (fp_eq fmt_double (bv_unsigned a) (bv_unsigned b)).
Definition flt_d (a b : word) : bool := fst (fp_lt fmt_double (bv_unsigned a) (bv_unsigned b)).
Definition fle_d (a b : word) : bool := fst (fp_le fmt_double (bv_unsigned a) (bv_unsigned b)).
Definition fcmp_d (op : fcmpop) : word -> word -> bool :=
  match op with F_EQ => feq_d | F_LT => flt_d | F_LE => fle_d end.

(* [comment removed for export] *)
Definition fadd_s (md : rmode) (a b : word) : word := nan_box (Z_to_bv 32 (fst (fp_add fmt_single md (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))))).
Definition fsub_s (md : rmode) (a b : word) : word := nan_box (Z_to_bv 32 (fst (fp_sub fmt_single md (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))))).
Definition fmul_s (md : rmode) (a b : word) : word := nan_box (Z_to_bv 32 (fst (fp_mul fmt_single md (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))))).
Definition fdiv_s (md : rmode) (a b : word) : word := nan_box (Z_to_bv 32 (fst (fp_div fmt_single md (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))))).
Definition fari_s (op : fariop) : rmode -> word -> word -> word :=
  match op with F_ADD => fadd_s | F_SUB => fsub_s | F_MUL => fmul_s | F_DIV => fdiv_s end.
Definition feq_s (a b : word) : bool := fst (fp_eq fmt_single (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))).
Definition flt_s (a b : word) : bool := fst (fp_lt fmt_single (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))).
Definition fle_s (a b : word) : bool := fst (fp_le fmt_single (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))).
Definition fcmp_s (op : fcmpop) : word -> word -> bool :=
  match op with F_EQ => feq_s | F_LT => flt_s | F_LE => fle_s end.

(* [comment removed for export] *)
Definition bword (b : bool) : word := if b then Z_to_bv 64 1 else Z_to_bv 64 0.

(* [comment removed for export] *)
Definition fcvt_w_d (md : rmode) (a : word) : word := sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_double md true 32 (bv_unsigned a)))).
Definition fcvt_wu_d (md : rmode) (a : word) : word := sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_double md false 32 (bv_unsigned a)))).
Definition fcvt_l_d (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_to_int fmt_double md true 64 (bv_unsigned a))).
Definition fcvt_lu_d (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_to_int fmt_double md false 64 (bv_unsigned a))).
(* [comment removed for export] *)
Definition fcvt_d_w (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md true 32 (bv_unsigned x))).
Definition fcvt_d_wu (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md false 32 (bv_unsigned x))).
Definition fcvt_d_l (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md true 64 (bv_unsigned x))).
Definition fcvt_d_lu (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md false 64 (bv_unsigned x))).
Definition fcvt_s_w (md : rmode) (x : word) : word := nan_box (Z_to_bv 32 (fst (fp_of_int fmt_single md true 32 (bv_unsigned x)))).
Definition fcvt_s_wu (md : rmode) (x : word) : word := nan_box (Z_to_bv 32 (fst (fp_of_int fmt_single md false 32 (bv_unsigned x)))).
(* [comment removed for export] *)
Definition fcvt_d_s (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_convert fmt_single fmt_double md (bv_unsigned (unbox_s a)))).
Definition fcvt_s_d (md : rmode) (a : word) : word := nan_box (Z_to_bv 32 (fst (fp_convert fmt_double fmt_single md (bv_unsigned a)))).

(* [comment removed for export] *)
Definition fabs_d (a : word) : word := Z_to_bv 64 (Z.land (bv_unsigned a) (Z.ones 63)).
Definition fneg_d (a : word) : word := Z_to_bv 64 (Z.lxor (bv_unsigned a) (2^63)).

(* [comment removed for export] *)
Definition fari_fl (op : fariop) (f : format) (md : rmode) (a b : Z) : fflags := snd (fari_sem op f md a b).
Definition fcmp_fl (op : fcmpop) (f : format) (a b : Z) : fflags := snd (fcmp_sem op f a b).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma exec_fcmp_d : forall sz op rd rs1 rs2 c,
  exec sz (Fcmp op FMT_D rd rs1 rs2) c =
  EDone (rset rd (bword (fcmp_d op (fget c rs1) (fget c rs2)))
          (accrue (fcmp_fl op fmt_double (bv_unsigned (fget c rs1)) (bv_unsigned (fget c rs2))) (with_pc (c_pc c + sz) c))).
Proof.
  intros. unfold exec. cbn [fp_format fread].
  unfold fcmp_d, fcmp_fl, feq_d, flt_d, fle_d, fcmp_sem, bword.
  destruct op; [destruct (fp_eq _ _ _)|destruct (fp_lt _ _ _)|destruct (fp_le _ _ _)]; reflexivity.
Qed.

Lemma exec_fcmp_s : forall sz op rd rs1 rs2 c,
  exec sz (Fcmp op FMT_S rd rs1 rs2) c =
  EDone (rset rd (bword (fcmp_s op (fget c rs1) (fget c rs2)))
          (accrue (fcmp_fl op fmt_single (bv_unsigned (unbox_s (fget c rs1))) (bv_unsigned (unbox_s (fget c rs2)))) (with_pc (c_pc c + sz) c))).
Proof.
  intros. unfold exec. cbn [fp_format fread].
  unfold fcmp_s, fcmp_fl, feq_s, flt_s, fle_s, fcmp_sem, bword.
  destruct op; [destruct (fp_eq _ _ _)|destruct (fp_lt _ _ _)|destruct (fp_le _ _ _)]; reflexivity.
Qed.

Lemma exec_fari_d : forall sz op rd rs1 rs2 rm c md,
  rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fari op FMT_D rd rs1 rs2 rm) c =
  EDone (fset rd (fari_d op md (fget c rs1) (fget c rs2))
          (accrue (fari_fl op fmt_double md (bv_unsigned (fget c rs1)) (bv_unsigned (fget c rs2))) (with_pc (c_pc c + sz) c))).
Proof.
  intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
  cbn [fp_format fread fwrite].
  unfold fari_d, fari_fl, fadd_d, fsub_d, fmul_d, fdiv_d, fari_sem.
  destruct op; [destruct (fp_add _ _ _ _)|destruct (fp_sub _ _ _ _)|destruct (fp_mul _ _ _ _)|destruct (fp_div _ _ _ _)]; reflexivity.
Qed.

Lemma exec_fari_s : forall sz op rd rs1 rs2 rm c md,
  rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fari op FMT_S rd rs1 rs2 rm) c =
  EDone (fset rd (fari_s op md (fget c rs1) (fget c rs2))
          (accrue (fari_fl op fmt_single md (bv_unsigned (unbox_s (fget c rs1))) (bv_unsigned (unbox_s (fget c rs2)))) (with_pc (c_pc c + sz) c))).
Proof.
  intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
  cbn [fp_format fread fwrite].
  unfold fari_s, fari_fl, fadd_s, fsub_s, fmul_s, fdiv_s, fari_sem.
  destruct op; [destruct (fp_add _ _ _ _)|destruct (fp_sub _ _ _ _)|destruct (fp_mul _ _ _ _)|destruct (fp_div _ _ _ _)]; reflexivity.
Qed.

Lemma exec_fsqrt_d : forall sz rd rs1 rm c md,
  rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fsqrt FMT_D rd rs1 rm) c =
  EDone (fset rd (fsqrt_d md (fget c rs1))
          (accrue (snd (fp_sqrt fmt_double md (bv_unsigned (fget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof.
  intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
  cbn [fp_format fread fwrite]. unfold fsqrt_d. destruct (fp_sqrt _ _ _); reflexivity.
Qed.

Lemma exec_fminmax_d : forall sz op rd rs1 rs2 c,
  exec sz (Fminmax op FMT_D rd rs1 rs2) c =
  let r := fp_minmax fmt_double (match op with F_MIN => false | F_MAX => true end) (bv_unsigned (fget c rs1)) (bv_unsigned (fget c rs2)) in
  EDone (fset rd (Z_to_bv 64 (fst r)) (accrue (snd r) (with_pc (c_pc c + sz) c))).
Proof. intros. unfold exec. cbn [fp_format fread fwrite]. destruct (fp_minmax _ _ _ _); reflexivity. Qed.

(* [comment removed for export] *)
Ltac fcvt_tac H :=
  unfold exec, resolve_rm; unfold frm_of in *; cbn [c_fcsr with_pc]; rewrite H;
  cbn [fp_format fread fwrite Z.eqb Pos.eqb];
  first [ destruct (fp_to_int _ _ _ _ _); reflexivity
        | destruct (fp_of_int _ _ _ _ _); reflexivity
        | destruct (fp_convert _ _ _ _); reflexivity ].

Lemma exec_fcvt_w_d : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_W FC_D rd rs1 rm) c =
  EDone (rset rd (fcvt_w_d md (fget c rs1)) (accrue (snd (fp_to_int fmt_double md true 32 (bv_unsigned (fget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_w_d. fcvt_tac H. Qed.
Lemma exec_fcvt_wu_d : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_WU FC_D rd rs1 rm) c =
  EDone (rset rd (fcvt_wu_d md (fget c rs1)) (accrue (snd (fp_to_int fmt_double md false 32 (bv_unsigned (fget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_wu_d. fcvt_tac H. Qed.
Lemma exec_fcvt_l_d : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_L FC_D rd rs1 rm) c =
  EDone (rset rd (fcvt_l_d md (fget c rs1)) (accrue (snd (fp_to_int fmt_double md true 64 (bv_unsigned (fget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_l_d. fcvt_tac H. Qed.
Lemma exec_fcvt_lu_d : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_LU FC_D rd rs1 rm) c =
  EDone (rset rd (fcvt_lu_d md (fget c rs1)) (accrue (snd (fp_to_int fmt_double md false 64 (bv_unsigned (fget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_lu_d. fcvt_tac H. Qed.
Lemma exec_fcvt_d_w : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_D FC_W rd rs1 rm) c =
  EDone (fset rd (fcvt_d_w md (rget c rs1)) (accrue (snd (fp_of_int fmt_double md true 32 (bv_unsigned (rget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_d_w. fcvt_tac H. Qed.
Lemma exec_fcvt_d_wu : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_D FC_WU rd rs1 rm) c =
  EDone (fset rd (fcvt_d_wu md (rget c rs1)) (accrue (snd (fp_of_int fmt_double md false 32 (bv_unsigned (rget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_d_wu. fcvt_tac H. Qed.
Lemma exec_fcvt_d_l : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_D FC_L rd rs1 rm) c =
  EDone (fset rd (fcvt_d_l md (rget c rs1)) (accrue (snd (fp_of_int fmt_double md true 64 (bv_unsigned (rget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_d_l. fcvt_tac H. Qed.
Lemma exec_fcvt_d_lu : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_D FC_LU rd rs1 rm) c =
  EDone (fset rd (fcvt_d_lu md (rget c rs1)) (accrue (snd (fp_of_int fmt_double md false 64 (bv_unsigned (rget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_d_lu. fcvt_tac H. Qed.
Lemma exec_fcvt_s_w : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_S FC_W rd rs1 rm) c =
  EDone (fset rd (fcvt_s_w md (rget c rs1)) (accrue (snd (fp_of_int fmt_single md true 32 (bv_unsigned (rget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_s_w. fcvt_tac H. Qed.
Lemma exec_fcvt_s_wu : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_S FC_WU rd rs1 rm) c =
  EDone (fset rd (fcvt_s_wu md (rget c rs1)) (accrue (snd (fp_of_int fmt_single md false 32 (bv_unsigned (rget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_s_wu. fcvt_tac H. Qed.
Lemma exec_fcvt_d_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_D FC_S rd rs1 rm) c =
  EDone (fset rd (fcvt_d_s md (fget c rs1)) (accrue (snd (fp_convert fmt_single fmt_double md (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_d_s. fcvt_tac H. Qed.
Lemma exec_fcvt_s_d : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_S FC_D rd rs1 rm) c =
  EDone (fset rd (fcvt_s_d md (fget c rs1)) (accrue (snd (fp_convert fmt_double fmt_single md (bv_unsigned (fget c rs1)))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_s_d. fcvt_tac H. Qed.

(* [comment removed for export] *)
Lemma exec_csr_rw : forall sz op rd rs1 csr c lo len,
  csr_slice csr = Some (lo, len) ->
  exec sz (Csr op rd rs1 csr) c =
  let f := c_fcsr c in
  let old := slice_get f lo len in
  let operand := rget c rs1 in
  let newv := match op with CSR_RW => operand | CSR_RS => bv_or old operand | CSR_RC => bv_and old (bv_not operand) end in
  let writes := match op with CSR_RW => true | _ => negb (is_x0 rs1) end in
  EDone (rset rd old (if writes then with_fcsr (slice_set f lo len newv) (with_pc (c_pc c + sz) c) else with_pc (c_pc c + sz) c)).
Proof.
  intros. unfold exec.
  assert (E : csr_read_only csr = false).
  { destruct (csr_read_only csr) eqn:E0; [|reflexivity]. exfalso.
    pose proof (csr_read_only_unimplemented csr E0). congruence. }
  unfold csr_write_illegal. rewrite E, Bool.andb_false_r. unfold Sem.exec_csr. rewrite H. reflexivity.
Qed.

Lemma exec_csri_rw : forall sz op rd uimm csr c lo len,
  csr_slice csr = Some (lo, len) ->
  exec sz (CsrI op rd uimm csr) c =
  let f := c_fcsr c in
  let old := slice_get f lo len in
  let operand := zext 64 uimm in
  let newv := match op with CSR_RW => operand | CSR_RS => bv_or old operand | CSR_RC => bv_and old (bv_not operand) end in
  let writes := match op with CSR_RW => true | _ => negb (Z.eqb (bv_unsigned uimm) 0) end in
  EDone (rset rd old (if writes then with_fcsr (slice_set f lo len newv) (with_pc (c_pc c + sz) c) else with_pc (c_pc c + sz) c)).
Proof.
  intros. unfold exec.
  assert (E : csr_read_only csr = false).
  { destruct (csr_read_only csr) eqn:E0; [|reflexivity]. exfalso.
    pose proof (csr_read_only_unimplemented csr E0). congruence. }
  unfold csr_write_illegal. rewrite E, Bool.andb_false_r. unfold Sem.exec_csr. rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sgnj_sign (op : fsgnop) (a b : word) : bool :=
  let sa := Z.testbit (bv_unsigned a) 63 in
  let sb := Z.testbit (bv_unsigned b) 63 in
  match op with F_SGNJ => sb | F_SGNJN => negb sb | F_SGNJX => xorb sa sb end.

Lemma sgnj_val_unsigned : forall op (a b : word),
  bv_unsigned (sgnj_val op a b) = Z.lor (Z.shiftl (if sgnj_sign op a b then 1 else 0) 63) (bv_unsigned a mod 2^63)%Z.
Proof.
  intros op a b. unfold sgnj_val, bit, sgnj_sign. change (Z.of_N (64-1)) with 63%Z.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
  change (Z.of_N (64-1)) with 63%Z.
  destruct (match op with F_SGNJ => _ | _ => _ end); reflexivity.
Qed.

Lemma testbit_sign63 : forall (c : bool) i, (0 <= i)%Z ->
  Z.testbit (Z.shiftl (if c then 1 else 0) 63) i = (c && Z.eqb i 63)%bool.
Proof.
  intros c i Hi. destruct (Z.lt_ge_cases i 63).
  - rewrite Z.shiftl_spec_low by lia. destruct c; cbn; [|reflexivity]. symmetry. apply Z.eqb_neq. lia.
  - rewrite Z.shiftl_spec_high by lia. destruct c.
    + destruct (Z.eqb_spec i 63). { subst. reflexivity. } cbn. apply Z.bits_above_log2; cbn; lia.
    + rewrite Z.bits_0. reflexivity.
Qed.

Lemma testbit_word_high : forall (a : word) i, (64 <= i)%Z -> Z.testbit (bv_unsigned a) i = false.
Proof.
  intros a i Hi. pose proof (bv_unsigned_in_range 64 a) as Hr. unfold bv_modulus in Hr.
  destruct (Z.eq_dec (bv_unsigned a) 0) as [E|E]. { rewrite E. apply Z.bits_0. }
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Ltac sgnj_bits a :=
  apply bv_eq; rewrite sgnj_val_unsigned; unfold sgnj_sign, fabs_d, fneg_d; rewrite ?Z_to_bv_unsigned;
  pose proof (bv_unsigned_in_range 64 a);
  try (rewrite bv_wrap_small; [| unfold bv_modulus in *;
        solve [ rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound (bv_unsigned a) (2^63)); lia
              | apply Z_lxor_range; lia ] ]);
  apply Z.bits_inj'; intros i Hi;
  rewrite ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec, ?testbit_sign63, <- ?Z.land_ones, ?Z.land_spec by lia;
  destruct (Z.lt_ge_cases i 63);
  [ rewrite ?Z.ones_spec_low, ?(Z.pow2_bits_false 63) by lia; replace (Z.eqb i 63) with false by (symmetry; apply Z.eqb_neq; lia)
  | rewrite ?Z.ones_spec_high by lia;
    destruct (Z.eqb_spec i 63); [subst; rewrite ?Z.pow2_bits_true by lia | rewrite ?(testbit_word_high a i), ?(Z.pow2_bits_false 63 i) by lia] ];
  repeat match goal with |- context [Z.testbit ?x ?k] => destruct (Z.testbit x k) end; reflexivity.

Lemma sgnj_self : forall a : word, sgnj_val F_SGNJ a a = a.
Proof. intros a. sgnj_bits a. Qed.
Lemma sgnjx_self : forall a : word, sgnj_val F_SGNJX a a = fabs_d a.
Proof. intros a. sgnj_bits a. Qed.
Lemma sgnjn_self : forall a : word, sgnj_val F_SGNJN a a = fneg_d a.
Proof. intros a. sgnj_bits a. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fmv_x_w_val : forall f : word, sext 64 (low32 f) = sx32 f.
Proof. intros f. exact (b_lw_val f). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bv_lit_eq : forall n (x : bv n) z, bv_unsigned x = z -> x = Z_to_bv n z.
Proof. intros n x z E. subst z. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity| apply bv_unsigned_in_range]. Qed.

(* [comment removed for export] *)
