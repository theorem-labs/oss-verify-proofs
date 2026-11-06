(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qcrs QUcd QCUT.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Definition mstep (ms ms' : machine_state) : Prop :=
ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'.

Inductive msteps : machine_state -> machine_state -> Prop :=
| msteps_refl : forall ms, msteps ms ms
| msteps_cons : forall ms ms1 ms2, mstep ms ms1 -> msteps ms1 ms2 -> msteps ms ms2.

Lemma msteps_one : forall ms ms', mstep ms ms' -> msteps ms ms'.
Proof. intros. eapply msteps_cons; [eassumption|apply msteps_refl]. Qed.

Lemma msteps_trans : forall a b c, msteps a b -> msteps b c -> msteps a c.
Proof. intros a b c H; induction H; intros; [assumption|]. eapply msteps_cons; eauto. Qed.

Definition evt (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
exists ms', msteps ms ms' /\ Q ms'.

Lemma evt_done : forall (Q : machine_state -> Prop) ms, Q ms -> evt Q ms.
Proof. intros Q ms H. exists ms. split; [apply msteps_refl|exact H]. Qed.

Lemma evt_step : forall Q ms ms1, mstep ms ms1 -> evt Q ms1 -> evt Q ms.
Proof. intros Q ms ms1 H (ms' & Hs & HQ). exists ms'. split; [eapply msteps_cons; eauto|exact HQ]. Qed.

Lemma evt_cut : forall (P Q : machine_state -> Prop) ms,
evt P ms -> (forall ms', P ms' -> evt Q ms') -> evt Q ms.
Proof.
intros P Q ms (ms1 & H1 & HP) K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
exists ms2. split; [eapply msteps_trans; eauto| exact HQ].
Qed.

Lemma evt_mono : forall (P Q : machine_state -> Prop) ms,
evt P ms -> (forall ms', P ms' -> Q ms') -> evt Q ms.
Proof. intros P Q ms H K. eapply evt_cut; [exact H|]. intros ms' HP. apply evt_done, K, HP. Qed.

Lemma evt_eq : forall Q ms ms', ms = ms' -> evt Q ms' -> evt Q ms.
Proof. intros; subst; assumption. Qed.

End WithSegs.

Arguments mstep segs ms ms' /.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qcrs QUcd QCUT.
Import ListNotations.
Open Scope bv_scope.

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

Definition frm0 (fc : bv 32) : Prop := Z.land (Z.shiftr (bv_unsigned fc) 5) 7 = 0%Z.

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

Lemma frm0_slice_get : forall fc, frm0 fc -> slice_get fc 5 3 = Z_to_bv 64 0.
Proof. intros fc H. unfold slice_get. change (Z.ones 3) with 7%Z. unfold frm0 in H. rewrite H. reflexivity. Qed.

Definition fari_sem (op : fariop) : format -> rmode -> Z -> Z -> Z * fflags :=
match op with F_ADD => fp_add | F_SUB => fp_sub | F_MUL => fp_mul | F_DIV => fp_div end.
Definition fcmp_sem (op : fcmpop) : format -> Z -> Z -> bool * fflags :=
match op with F_EQ => fp_eq | F_LT => fp_lt | F_LE => fp_le end.

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

Definition bword (b : bool) : word := if b then Z_to_bv 64 1 else Z_to_bv 64 0.

Definition fcvt_w_d (md : rmode) (a : word) : word := sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_double md true 32 (bv_unsigned a)))).
Definition fcvt_wu_d (md : rmode) (a : word) : word := sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_double md false 32 (bv_unsigned a)))).
Definition fcvt_l_d (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_to_int fmt_double md true 64 (bv_unsigned a))).
Definition fcvt_lu_d (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_to_int fmt_double md false 64 (bv_unsigned a))).

Definition fcvt_d_w (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md true 32 (bv_unsigned x))).
Definition fcvt_d_wu (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md false 32 (bv_unsigned x))).
Definition fcvt_d_l (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md true 64 (bv_unsigned x))).
Definition fcvt_d_lu (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md false 64 (bv_unsigned x))).
Definition fcvt_s_w (md : rmode) (x : word) : word := nan_box (Z_to_bv 32 (fst (fp_of_int fmt_single md true 32 (bv_unsigned x)))).
Definition fcvt_s_wu (md : rmode) (x : word) : word := nan_box (Z_to_bv 32 (fst (fp_of_int fmt_single md false 32 (bv_unsigned x)))).

Definition fcvt_d_s (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_convert fmt_single fmt_double md (bv_unsigned (unbox_s a)))).
Definition fcvt_s_d (md : rmode) (a : word) : word := nan_box (Z_to_bv 32 (fst (fp_convert fmt_double fmt_single md (bv_unsigned a)))).

Definition fabs_d (a : word) : word := Z_to_bv 64 (Z.land (bv_unsigned a) (Z.ones 63)).
Definition fneg_d (a : word) : word := Z_to_bv 64 (Z.lxor (bv_unsigned a) (2^63)).

Definition fari_fl (op : fariop) (f : format) (md : rmode) (a b : Z) : fflags := snd (fari_sem op f md a b).
Definition fcmp_fl (op : fcmpop) (f : format) (a b : Z) : fflags := snd (fcmp_sem op f a b).

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
intros. assert (Hro : csr_read_only csr = false)
by (destruct (csr_read_only csr) eqn:E; [apply csr_read_only_unimplemented in E; congruence|reflexivity]).
unfold exec. cbv zeta. unfold csr_write_illegal. rewrite Hro, Bool.andb_false_r.
unfold Sem.exec_csr. rewrite H. reflexivity.
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
intros. assert (Hro : csr_read_only csr = false)
by (destruct (csr_read_only csr) eqn:E; [apply csr_read_only_unimplemented in E; congruence|reflexivity]).
unfold exec. cbv zeta. unfold csr_write_illegal. rewrite Hro, Bool.andb_false_r.
unfold Sem.exec_csr. rewrite H. reflexivity.
Qed.

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

Lemma fmv_x_w_val : forall f : word, sext 64 (low32 f) = sx32 f.
Proof. intros f. exact (b_lw_val f). Qed.

Lemma bv_lit_eq : forall n (x : bv n) z, bv_unsigned x = z -> x = Z_to_bv n z.
Proof. intros n x z E. subst z. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity| apply bv_unsigned_in_range]. Qed.

End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qcrs QUcd QCUT.
Import ListNotations.
Open Scope bv_scope.

Definition inr64 (e : Z) : Prop := (0 <= e < 2^64)%Z.

Lemma zr_word : forall x : word, inr64 (bv_unsigned x).
Proof. intros x. pose proof (bv_unsigned_in_range 64 x). unfold bv_modulus in *. exact H. Qed.
Lemma zr_bv : forall n (x : bv n), (n <= 64)%N -> inr64 (bv_unsigned x).
Proof.
intros n x Hn. pose proof (bv_unsigned_in_range n x) as H. unfold bv_modulus, inr64 in *.
split; [lia|]. apply Z.lt_le_trans with (2 ^ Z.of_N n)%Z; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_lit : forall z, (0 <= z < 2^64)%Z -> inr64 z.
Proof. intros; assumption. Qed.
Lemma zr_mod64 : forall e, inr64 (e mod 2^64).
Proof. intros. unfold inr64. apply Z.mod_pos_bound. lia. Qed.
Lemma zr_mod : forall e k, (0 <= k <= 64)%Z -> inr64 (e mod 2^k).
Proof.
intros e k Hk. unfold inr64. pose proof (Z.mod_pos_bound e (2^k) ltac:(apply Z.pow_pos_nonneg; lia)).
split; [lia|]. apply Z.lt_le_trans with (2^k)%Z; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_mod_any : forall e p, (0 < p <= 2^64)%Z -> inr64 (e mod p).
Proof. intros e p Hp. unfold inr64. pose proof (Z.mod_pos_bound e p ltac:(lia)). lia. Qed.
Lemma zr_land_l : forall a b, inr64 a -> (0 <= b)%Z -> inr64 (Z.land a b).
Proof.
intros a b [Ha Ha'] Hb. unfold inr64. pose proof (Z.land_nonneg a b) as Hn.
split; [lia|].
destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]; [lia|].
destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. lia. }
apply Z.log2_lt_pow2; [lia|].
pose proof (Z.log2_land a b ltac:(lia) Hb).
assert (Z.log2 a < 64)%Z by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma zr_land_r : forall a b, (0 <= a)%Z -> inr64 b -> inr64 (Z.land a b).
Proof. intros. rewrite Z.land_comm. apply zr_land_l; assumption. Qed.

Lemma land_mask_mod : forall e m, (0 <= m < 2^64)%Z -> Z.land e m = Z.land (e mod 2^64) m.
Proof.
intros e m Hm. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit m i) with false. { rewrite !andb_false_r. reflexivity. }
symmetry. destruct (Z.eq_dec m 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma zr_land_lit : forall e m, (0 <= m < 2^64)%Z -> inr64 (Z.land e m).
Proof.
intros e m Hm. rewrite land_mask_mod by exact Hm. apply zr_land_r; [|exact Hm].
apply Z.mod_pos_bound. lia.
Qed.
Lemma zr_lor : forall a b, inr64 a -> inr64 b -> inr64 (Z.lor a b).
Proof. intros a b Ha Hb. unfold inr64 in *. apply Z_lor_range; lia. Qed.
Lemma zr_lxor : forall a b, inr64 a -> inr64 b -> inr64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold inr64 in *. apply Z_lxor_range; lia. Qed.
Lemma zr_shiftr : forall a k, inr64 a -> (0 <= k)%Z -> inr64 (Z.shiftr a k).
Proof. intros a k Ha Hk. unfold inr64 in *. apply Z_shiftr_range; lia. Qed.
Lemma zr_div : forall a k, inr64 a -> (0 < k)%Z -> inr64 (a / k).
Proof.
intros a k [Ha Ha'] Hk. unfold inr64. split. { apply Z.div_pos; lia. }
apply Z.le_lt_trans with a; [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Lemma zr_b2z : forall b, inr64 (Z.b2z b).
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zr_ite : forall (b : bool) x y, inr64 x -> inr64 y -> inr64 (if b then x else y).
Proof. intros [|]; auto. Qed.

Lemma inr64_unsigned_lit : forall e, inr64 e -> bv_unsigned (Z_to_bv 64 e) = e.
Proof. intros e H. apply unsigned_lit. exact H. Qed.

Ltac nc_cbv_zxb := lazymatch goal with |- ?G => let G' := eval cbv delta [zxb] in G in change_no_check G' end.

Ltac is_Zlit_zb a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac slim := repeat match goal with x := _ : Z |- _ => clearbody x end.
Ltac flia := first [ assumption | slim; lia | lazymatch goal with x := _ : Z |- _ => lia end ]. Ltac mkr__flia_0 := first [ assumption | slim; lia | lazymatch goal with x := _ : Z |- _ => lia end ].

Ltac zrange :=
lazymatch goal with
| |- inr64 ?e =>
lazymatch e with
| bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
| Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
| apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
| Z.lor _ _ => apply zr_lor; [zrange | zrange]
| Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
| Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
| Z.modulo _ (2^64)%Z => apply zr_mod64
| Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
| Z.div _ _ => apply zr_div; [zrange | flia]
| Z.b2z _ => apply zr_b2z
| (if _ then _ else _) => apply zr_ite; [zrange | zrange]
| _ => first [ apply zr_lit; flia
| is_var e; progress (unfold e); zrange ]
end
| |- (0 <= ?e < _)%Z => change (inr64 e); zrange
end
with zrange_nonneg :=
lazymatch goal with
| |- (0 <= ?e)%Z =>
first [ apply (proj1 (A:=(0 <= e)%Z) (B:=(e < 2^64)%Z)); change (inr64 e); zrange
| apply Z.land_nonneg; left; zrange_nonneg
| apply Z.lor_nonneg; split; zrange_nonneg
| apply Z.lxor_nonneg; split; zrange_nonneg
| apply Z.shiftr_nonneg; zrange_nonneg
| apply Z.shiftl_nonneg; zrange_nonneg
| flia
| is_var e; progress (unfold e); zrange_nonneg ]
end.

Lemma Z_to_bv_mod64 : forall e, Z_to_bv 64 (e mod 2^64) = Z_to_bv 64 e.
Proof.
intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
apply Z.mod_mod. lia.
Qed.

Lemma zb_land_pow2_small : forall y k, (0 <= y < 2^k)%Z -> (0 <= k)%Z -> Z.land y (2^k) = 0%Z.
Proof.
intros y k Hy Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i k) as [->|Hne].
- rewrite Z.pow2_bits_true by lia. rewrite andb_true_r.
apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
- rewrite Z.pow2_bits_eqb by lia. replace (k =? i)%Z with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.
Lemma zb_lxor_pow2_small : forall y k, (0 <= y < 2^k)%Z -> (0 <= k)%Z -> Z.lxor y (2^k) = (y + 2^k)%Z.
Proof. intros. symmetry. apply Z.add_nocarry_lxor. apply zb_land_pow2_small; assumption. Qed.

Lemma zb_lxor_sign : forall x, (0 <= x < 2^64)%Z -> Z.lxor x (2^63) = ((x + 2^63) mod 2^64)%Z.
Proof.
intros x Hx. destruct (Z.lt_ge_cases x (2^63)).
- rewrite zb_lxor_pow2_small by lia. rewrite Z.mod_small by lia. reflexivity.
- set (y := (x - 2^63)%Z). replace x with (y + 2^63)%Z by lia.
rewrite <- (zb_lxor_pow2_small y 63) at 1 by lia. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
replace (y + 2^63 + 2^63)%Z with (y + 1 * 2^64)%Z by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.

Lemma zb_signed : forall x : word,
bv_signed x = (if bv_unsigned x <? 2^63 then bv_unsigned x else bv_unsigned x - 2^64)%Z.
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as Hr. unfold bv_modulus in Hr.
unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *. change (2^64 / 2)%Z with (2^63)%Z.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)).
- rewrite Z.mod_small by lia. lia.
- rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma bv_eqb_Z : forall x y : word, bv_eqb x y = (bv_unsigned x =? bv_unsigned y)%Z.
Proof. reflexivity. Qed.

Lemma bv_lts_lxor : forall x y : word,
bv_lts x y = (Z.lxor (bv_unsigned x) (2^63) <? Z.lxor (bv_unsigned y) (2^63))%Z.
Proof.
intros x y. unfold bv_lts. rewrite !zb_signed.
pose proof (bv_unsigned_in_range 64 x) as Hx. pose proof (bv_unsigned_in_range 64 y) as Hy. unfold bv_modulus in *.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *.
rewrite !zb_lxor_sign by lia.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); destruct (Z.ltb_spec0 (bv_unsigned y) (2^63)).
- rewrite !Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite (Z.mod_small (bv_unsigned x + _)) by lia.
rewrite <- (Z.mod_add (bv_unsigned y + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite (Z.mod_small (bv_unsigned y + _)) by lia.
rewrite <- (Z.mod_add (bv_unsigned x + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite <- (Z.mod_add (bv_unsigned x + _) (-1)), Z.mod_small by lia.
rewrite <- (Z.mod_add (bv_unsigned y + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.

Lemma bv_lts_zero_r : forall x : word, bv_lts x (Z_to_bv 64 0) = (2^63 <=? bv_unsigned x)%Z.
Proof.
intros x. unfold bv_lts. rewrite (zb_signed x). change (bv_signed (Z_to_bv 64 0)) with 0%Z.
pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); apply eq_true_iff_eq; rewrite Z.ltb_lt, Z.leb_le; lia.
Qed.

Lemma bv_lts_zero_l : forall x : word,
bv_lts (Z_to_bv 64 0) x = ((0 <? bv_unsigned x) && (bv_unsigned x <? 2^63))%Z.
Proof.
intros x. unfold bv_lts. rewrite (zb_signed x). change (bv_signed (Z_to_bv 64 0)) with 0%Z.
pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); apply eq_true_iff_eq; rewrite andb_true_iff, !Z.ltb_lt; lia.
Qed.

Lemma v_sltu_b2z : forall x y : word, v_sltu x y = Z_to_bv 64 (Z.b2z (bv_unsigned x <? bv_unsigned y)%Z).
Proof. intros. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_slt_b2z : forall x y : word,
v_slt x y = Z_to_bv 64 (Z.b2z (Z.lxor (bv_unsigned x) (2^63) <? Z.lxor (bv_unsigned y) (2^63))%Z).
Proof. intros. unfold v_slt, c_lts. rewrite bv_lts_lxor. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_sltiu_b2z : forall (x : word) imm, v_sltiu x imm = Z_to_bv 64 (Z.b2z (bv_unsigned x <? bv_wrap 64 imm)%Z).
Proof. intros. unfold v_sltiu. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_slti_b2z : forall (x : word) imm,
v_slti x imm = Z_to_bv 64 (Z.b2z (Z.lxor (bv_unsigned x) (2^63) <? imm + 2^63)%Z).
Proof.
intros. unfold v_slti, zsig. rewrite zb_signed.
pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
rewrite zb_lxor_sign by lia.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)).
- rewrite Z.mod_small by lia.
destruct (Z.ltb_spec0 (bv_unsigned x) imm); destruct (Z.ltb_spec0 (bv_unsigned x + 2^63) (imm + 2^63)); try reflexivity; exfalso; lia.
- rewrite <- (Z.mod_add _ (-1)), Z.mod_small by lia.
destruct (Z.ltb_spec0 (bv_unsigned x - 2^64) imm); destruct (Z.ltb_spec0 (bv_unsigned x + 2^63 + -1 * 2^64) (imm + 2^63)); try reflexivity; exfalso; lia.
Qed.

Lemma zb_b2z_nonzero : forall b, Z.b2z b <> 0%Z <-> b = true.
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_b2z_zero : forall b, Z.b2z b = 0%Z <-> b = false.
Proof. intros [|]; cbv; split; congruence. Qed.

Lemma zb_land_mask : forall x k, (0 <= k)%Z -> Z.land x (2^k - 1) = (x mod 2^k)%Z.
Proof. intros. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. f_equal. Qed.

Lemma zb_shl_shr : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
Z.shiftr ((Z.shiftl x k) mod 2^64) k = (x mod 2^(64 - k))%Z.
Proof.
intros x k Hx Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
replace (2^64)%Z with (2^(64-k) * 2^k)%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.

Lemma zb_lxor_eq0 : forall a b, (Z.lxor a b = 0)%Z <-> a = b.
Proof. intros. apply Z.lxor_eq_0_iff. Qed.

Lemma zb_lxor_ones : forall x, (0 <= x < 2^64)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof.
intros x Hx. change 18446744073709551615%Z with (Z.ones 64).
pose proof (Z.add_lnot_diag x).
assert (E : Z.lxor x (Z.ones 64) = ((Z.lnot x) mod 2^64)%Z).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^64)) with (2^64 - 1)%Z.
replace (Z.lnot x) with (-x - 1)%Z by lia.
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Ltac mlia := Z.div_mod_to_equations; lia.

Ltac zb_fold_lits :=
repeat match goal with
| |- context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
| |- context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
| |- context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
| |- context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
| |- context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
| |- context [Z.modulo ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
| |- context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v
| |- context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
| |- context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
replace (bv_wrap n z) with v by (vm_compute; reflexivity)
| |- context [Z_to_bv 64 ?z] => is_Zlit_zb z;
lazymatch eval vm_compute in (Z.leb 18446744073709551616 z) with true => idtac end;
let v := eval vm_compute in (z mod 18446744073709551616)%Z in
replace (Z_to_bv 64 z) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
end.

Lemma unsigned_lit_land : forall e, bv_unsigned (Z_to_bv 64 e) = Z.land e 18446744073709551615.
Proof. intros. rewrite unsigned_lit_wrap. change 18446744073709551615%Z with (Z.ones 64). symmetry. apply Z.land_ones. lia. Qed.
Lemma Z_to_bv_land64 : forall e, Z_to_bv 64 (Z.land e 18446744073709551615) = Z_to_bv 64 e.
Proof. intros. rewrite <- unsigned_lit_land. apply Z_to_bv_bv_unsigned. Qed.
Lemma zb_shl_shr_land : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
Z.shiftr (Z.land (Z.shiftl x k) 18446744073709551615) k = Z.land x (2^(64 - k) - 1).
Proof.
intros x k Hx Hk. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite zb_shl_shr, <- zb_land_mask by lia. reflexivity.
Qed.

Ltac zs_wrap e := rewrite (unsigned_lit_wrap e). Ltac mkr__zs_wrap_1 e := rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H := rewrite (unsigned_lit_wrap e) in H. Ltac mkr__zs_wrap_in_2 e H := rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms :=
match goal with
| |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
| |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
| |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
end. Ltac mkr__zs_idioms_3 := match goal with
| |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
| |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
| |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
end.
Ltac zs_idioms_in H :=
match type of H with
| context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
| context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
| context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
end. Ltac mkr__zs_idioms_in_4 H := match type of H with
| context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
| context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
| context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
end.

Ltac zs_wrap_land e := rewrite (unsigned_lit_land e).
Ltac zs_wrap_land_in e H := rewrite (unsigned_lit_land e) in H.
Ltac zs_idioms_land :=
match goal with
| |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
end.
Ltac zs_idioms_land_in H :=
match type of H with
| context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
end.

Ltac zsimp :=
repeat match goal with |- context [v_sltu _ _] => rewrite v_sltu_b2z end;
repeat match goal with |- context [v_slt _ _] => rewrite v_slt_b2z end;
repeat match goal with |- context [v_sltiu _ _] => rewrite v_sltiu_b2z end;
repeat match goal with |- context [v_slti _ _] => rewrite v_slti_b2z end;
nc_cbv_zxb;
zb_fold_lits;
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
first [ rewrite (inr64_unsigned_lit e) by zrange
| zs_wrap e ]
| |- _ => progress zs_idioms
end; zb_fold_lits. Ltac mkr__zsimp_5 := repeat match goal with |- context [v_sltu _ _] => rewrite v_sltu_b2z end;
repeat match goal with |- context [v_slt _ _] => rewrite v_slt_b2z end;
repeat match goal with |- context [v_sltiu _ _] => rewrite v_sltiu_b2z end;
repeat match goal with |- context [v_slti _ _] => rewrite v_slti_b2z end;
nc_cbv_zxb;
zb_fold_lits;
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
first [ rewrite (inr64_unsigned_lit e) by zrange
| zs_wrap e ]
| |- _ => progress zs_idioms
end; zb_fold_lits.

Ltac zb_fold_lits_in H :=
repeat match type of H with
| context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v in H
| context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H
| context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v in H
| context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v in H
| context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
| context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v in H
| context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
| context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
replace (bv_wrap n z) with v in H by (vm_compute; reflexivity)
end.

Ltac zsimp_in H :=
repeat match type of H with context [v_sltu _ _] => rewrite v_sltu_b2z in H end;
repeat match type of H with context [v_slt _ _] => rewrite v_slt_b2z in H end;
repeat match type of H with context [v_sltiu _ _] => rewrite v_sltiu_b2z in H end;
repeat match type of H with context [v_slti _ _] => rewrite v_slti_b2z in H end;
cbv delta [zxb] in H;
zb_fold_lits_in H;
repeat match type of H with
| context [bv_unsigned (Z_to_bv 64 ?e)] =>
first [ rewrite (inr64_unsigned_lit e) in H by zrange
| zs_wrap_in e H ]
| _ => progress (zs_idioms_in H)
end; zb_fold_lits_in H.

Ltac decide_tests :=
repeat match goal with
| |- context [Z.eqb ?x ?y] =>
first [ rewrite (proj2 (Z.eqb_eq x y)) by mlia | rewrite (proj2 (Z.eqb_neq x y)) by mlia ]
| |- context [Z.ltb ?x ?y] =>
first [ rewrite (proj2 (Z.ltb_lt x y)) by mlia | rewrite (proj2 (Z.ltb_ge x y)) by mlia ]
| |- context [Z.leb ?x ?y] =>
first [ rewrite (proj2 (Z.leb_le x y)) by mlia | rewrite (proj2 (Z.leb_gt x y)) by mlia ]
end; cbn [andb orb negb].

Ltac zr_pose e := let H := fresh "R" in assert (H : inr64 e) by zrange; unfold inr64 in H.

Ltac zb_masks :=
repeat match goal with
| |- context [Z.land ?x ?m] =>
is_Zlit_zb m;
let k := eval vm_compute in (Z.log2 (m + 1)) in
let m' := eval vm_compute in (2 ^ k - 1)%Z in
constr_eq m m';
let p := eval vm_compute in (2 ^ k)%Z in
replace (Z.land x m) with (x mod p)%Z by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
| H : context [Z.land ?x ?m] |- _ =>
is_Zlit_zb m;
let k := eval vm_compute in (Z.log2 (m + 1)) in
let m' := eval vm_compute in (2 ^ k - 1)%Z in
constr_eq m m';
let p := eval vm_compute in (2 ^ k)%Z in
replace (Z.land x m) with (x mod p)%Z in H by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
end.

Ltac pose_word_ranges :=
repeat match goal with
| |- context [bv_unsigned ?x] =>
lazymatch goal with
| _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
| _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
end
| _ : context [bv_unsigned ?x] |- _ =>
lazymatch goal with
| _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
| _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
end
end.

Ltac zb_bits_norm :=
intros;
rewrite ?Z.land_lor_distr_l in *;
rewrite ?Z.lor_eq_0_iff in *;
rewrite ?zb_lxor_eq0 in *;
zb_masks;
rewrite ?Z.shiftr_div_pow2 in * by lia;
zb_fold_lits.

Ltac blia := zb_bits_norm; pose_word_ranges; mlia. Ltac mkr__blia_6 := zb_bits_norm; pose_word_ranges; mlia.

Ltac decide_tests_b :=
repeat match goal with
| |- context [Z.eqb ?x ?y] =>
first [ rewrite (proj2 (Z.eqb_eq x y)) by blia | rewrite (proj2 (Z.eqb_neq x y)) by blia ]
| |- context [Z.ltb ?x ?y] =>
first [ rewrite (proj2 (Z.ltb_lt x y)) by blia | rewrite (proj2 (Z.ltb_ge x y)) by blia ]
| |- context [Z.leb ?x ?y] =>
first [ rewrite (proj2 (Z.leb_le x y)) by blia | rewrite (proj2 (Z.leb_gt x y)) by blia ]
end; cbn [andb orb negb].

Lemma Z_to_bv_eqm : forall e1 e2, (e1 mod 2^64 = e2 mod 2^64)%Z -> Z_to_bv 64 e1 = Z_to_bv 64 e2.
Proof. intros e1 e2 H. rewrite <- (Z_to_bv_mod64 e1), <- (Z_to_bv_mod64 e2), H. reflexivity. Qed.

Ltac word_eq_tac :=
first [ exact eq_refl
| f_equal; lia
| apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
| apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT.
Import ListNotations.
Open Scope Z_scope.

Fixpoint le_val (bs : list Z) : Z :=
match bs with [] => 0 | b :: bs' => b + 256 * le_val bs' end.
Fixpoint ones (n : nat) : Z := match n with O => 0 | S n' => 1 + 256 * ones n' end.
Definition highs (n : nat) : Z := 128 * ones n.
Definition bytes_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.

Lemma le_val_range : forall bs, bytes_ok bs -> 0 <= le_val bs < 256 ^ Z.of_nat (length bs).
Proof.
induction bs as [|b bs IH]; intros H; cbn [le_val length]; [lia|].
inversion H; subst. specialize (IH ltac:(assumption)).
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma split_mod : forall x y M, 0 <= x < 256 -> 0 < M -> (x + 256 * y) mod (256 * M) = x + 256 * (y mod M).
Proof.
intros x y M Hx HM. rewrite Z.rem_mul_r by lia.
rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma testbit_split : forall x y i, 0 <= x < 256 -> 0 <= i ->
Z.testbit (x + 256 * y) i = if i <? 8 then Z.testbit x i else Z.testbit y (i - 8).
Proof.
intros x y i Hx Hi. destruct (Z.ltb_spec0 i 8).
- rewrite <- (Z.mod_pow2_bits_low _ 8) by lia. change (2^8) with 256.
rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia. reflexivity.
- replace i with ((i - 8) + 8) at 1 by lia. rewrite <- Z.div_pow2_bits by lia. change (2^8) with 256.
rewrite (Z.mul_comm 256 y), Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma land_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b -> 0 <= Z.land a b < 2^n.
Proof.
intros a b n Ha Hb.
assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
pose proof (Z.land_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]. { apply Z.pow_pos_nonneg; lia. }
destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. apply Z.pow_pos_nonneg; lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.land a b) n ltac:(lia))).
pose proof (Z.log2_land a b ltac:(lia) Hb). assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
intros a b n Ha Hb.
assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
pose proof (Z.lor_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec a 0) as [->|]. { rewrite Z.lor_0_l. lia. }
destruct (Z.eq_dec b 0) as [->|]. { rewrite Z.lor_0_r. lia. }
assert (Hp : 0 < Z.lor a b). { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hp)). rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 ->
Z.land (x + 256 * y) (x' + 256 * y') = Z.land x x' + 256 * Z.land y y'.
Proof.
intros x y x' y' Hx Hx'.
pose proof (land_lt_pow2 x x' 8 ltac:(cbn; lia) ltac:(lia)) as Hl. change (2^8) with 256 in Hl.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !testbit_split by lia.
destruct (i <? 8); rewrite Z.land_spec; reflexivity.
Qed.

Lemma lnot_split : forall b w, Z.lnot (b + 256 * w) = (255 - b) + 256 * Z.lnot w.
Proof. intros. unfold Z.lnot. lia. Qed.

Lemma byte_fact1 : forall b, 1 <= b < 256 -> Z.land (Z.land (b - 1) (255 - b)) 128 = 0.
Proof.
intros b Hb.
assert (C : forallb (fun b => Z.land (Z.land (b - 1) (255 - b)) 128 =? 0) (map Z.of_nat (seq 1 255)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. apply Z.eqb_eq, C. apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

Theorem haszero_iff : forall bs, bytes_ok bs ->
let n := length bs in let w := le_val bs in
Z.land (Z.land ((w - ones n) mod 256 ^ Z.of_nat n) (Z.lnot w)) (highs n) <> 0 <-> In 0 bs.
Proof.
induction bs as [|b bs IH]; intros H; cbn [length le_val ones highs].
- cbn. split; [|intros []]. intros C; apply C. reflexivity.
- inversion H as [|b' bs' Hb Hbs]; subst. specialize (IH Hbs). cbn zeta in IH.
unfold highs in *. cbn [ones].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
pose proof (Z.pow_pos_nonneg 256 (Z.of_nat (length bs)) ltac:(lia) ltac:(lia)) as HM.
rewrite lnot_split.
replace (128 * (1 + 256 * ones (length bs))) with (128 + 256 * (128 * ones (length bs))) by lia.
destruct (Z.eq_dec b 0) as [->|Hb0].
+ replace (0 + 256 * le_val bs - (1 + 256 * ones (length bs))) with (255 + 256 * (le_val bs - ones (length bs) - 1)) by lia.
rewrite split_mod by lia. rewrite land_split by lia. change (Z.land 255 (255 - 0)) with 255.
rewrite land_split by lia. change (Z.land 255 128) with 128.
split; [intros; left; reflexivity| intros _]. lia.
+ replace (b + 256 * le_val bs - (1 + 256 * ones (length bs))) with ((b - 1) + 256 * (le_val bs - ones (length bs))) by lia.
rewrite split_mod by lia.
rewrite land_split by lia.
rewrite land_split. 2:{ pose proof (land_lt_pow2 (b-1) (255-b) 8 ltac:(cbn; lia) ltac:(lia)). cbn in *. lia. }
2:{ lia. }
rewrite byte_fact1 by lia.
split.
* intros Hnz. right. apply IH. lia.
* intros [Hz|Hin]; [lia|]. apply IH in Hin. lia.
Qed.

Definition ONES64b  : Z := 0x0101010101010101.
Definition HIGHS64b : Z := 0x8080808080808080.

Lemma ones_8 : ones 8 = ONES64b. Proof. reflexivity. Qed.
Lemma highs_8 : highs 8 = HIGHS64b. Proof. reflexivity. Qed.

Lemma testbit_high_false : forall x n i, 0 <= x < 2^n -> 0 <= n <= i -> Z.testbit x i = false.
Proof.
intros x n i Hx Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma land_mod_pow2_r : forall a b n, 0 <= a < 2^n -> 0 <= n -> Z.land a (b mod 2^n) = Z.land a b.
Proof.
intros a b n Ha Hn. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i n).
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite (testbit_high_false a n i) by lia. reflexivity.
Qed.

Lemma lnot_mod64 : forall w, 0 <= w < 2^64 -> Z.lxor w 18446744073709551615 = (Z.lnot w) mod 2^64.
Proof.
intros w Hw. change 18446744073709551615 with (Z.ones 64). rewrite <- Z.land_ones by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
destruct (Z.eq_dec w 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma demorgan_highs : forall D w H, 0 <= D < 2^64 -> 0 <= w < 2^64 -> 0 <= H < 2^64 ->
Z.land (Z.lor (Z.lxor D 18446744073709551615) w) H = H <-> Z.land (Z.land D (Z.lnot w)) H = 0.
Proof.
intros D w H HD Hw HH. change 18446744073709551615 with (Z.ones 64).
assert (HI : forall x, 0 <= x < 2^64 -> forall i, 64 <= i -> Z.testbit x i = false).
{ intros x Hx i Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia]. }
split; intros E; apply Z.bits_inj'; intros i Hi.
- rewrite Z.bits_0, !Z.land_spec, Z.lnot_spec by lia.
apply (f_equal (fun x => Z.testbit x i)) in E. rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec in E.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.ones_spec_low in E by lia.
destruct (Z.testbit D i), (Z.testbit w i), (Z.testbit H i); cbn in *; congruence.
+ rewrite (HI D) by lia. reflexivity.
- apply (f_equal (fun x => Z.testbit x i)) in E. rewrite Z.bits_0, !Z.land_spec, Z.lnot_spec in E by lia.
rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.ones_spec_low by lia.
destruct (Z.testbit D i), (Z.testbit w i), (Z.testbit H i); cbn in *; congruence.
+ rewrite (HI H) by lia. apply andb_false_r.
Qed.

Theorem haszero64_clang : forall bs, bytes_ok bs -> length bs = 8%nat ->
let w := le_val bs in
Z.land (Z.lor ((72340172838076672 - w) mod 18446744073709551616) w) 9259542123273814144 = 9259542123273814144
<-> ~ In 0 bs.
Proof.
intros bs Hok Hlen w. change 18446744073709551616 with (2^64).
pose proof (le_val_range bs Hok) as Hw. rewrite Hlen in Hw. change (256 ^ Z.of_nat 8) with (2^64) in Hw.
pose proof (haszero_iff bs Hok) as HZ. rewrite Hlen in HZ. cbn zeta in HZ. fold w in HZ, Hw.
change (256 ^ Z.of_nat 8) with (2^64) in HZ. rewrite ones_8, highs_8 in HZ. unfold ONES64b, HIGHS64b in HZ.
set (D := (w - 72340172838076673) mod 2 ^ 64) in HZ.
assert (HD : 0 <= D < 2^64) by (apply Z.mod_pos_bound; lia).
replace ((72340172838076672 - w) mod 2 ^ 64) with (Z.lxor D 18446744073709551615).
2:{ rewrite lnot_mod64 by lia. unfold Z.lnot. subst D. Z.div_mod_to_equations. lia. }
rewrite demorgan_highs by lia.

destruct HZ as [HZ1 HZ2]. split.
- intros E I. apply HZ2 in I. apply I. exact E.
- intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
exfalso. apply NI. apply HZ1. exact NE.
Qed.

Lemma lor_shiftl8_add : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + 256 * y.
Proof.
intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
rewrite <- Z.lxor_lor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia]. }
symmetry. replace (256 * y) with (y * 256) by lia. apply Z.add_nocarry_lxor.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma bytes_ok_map : forall bs : list byte, bytes_ok (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; cbn; constructor; [|exact IH].
pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.

Lemma bytes_le_to_Z_le_val : forall bs : list byte, bytes_le_to_Z bs = le_val (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z le_val map]; [reflexivity|].
rewrite IH. apply lor_shiftl8_add.
- pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
- pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)). lia.
Qed.

Lemma load8_le_val : forall bs : list byte, length bs = 8%nat ->
bv_unsigned (bv_extract 0 64 (le_bytes_to_word bs)) = le_val (map bv_unsigned bs).
Proof.
intros bs Hlen. unfold le_bytes_to_word. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
rewrite bytes_le_to_Z_le_val.
pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr. rewrite length_map, Hlen in Hr.
change (256 ^ Z.of_nat 8) with (2^64) in Hr.
rewrite (bv_wrap_small 64 (le_val _)) by (change (bv_modulus 64) with (2^64); lia).
apply bv_wrap_small. change (bv_modulus 64) with (2^64); lia.
Qed.

