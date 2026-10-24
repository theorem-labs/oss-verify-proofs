(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition M64 : Z := 2 ^ 64.
Definition M32 : Z := 2 ^ 32.
Definition zcanon (z : Z) : Z := z mod M64.
Definition zs64 (z : Z) : Z := bv_swrap 64 z.
Definition zs32 (z : Z) : Z := bv_swrap 32 z.
Definition zu32 (z : Z) : Z := z mod M32.
Definition zalu_raw (shmask : Z) (width : N) (op : aluop) (a b : Z) : Z :=
match op with
| ALU_ADD => a + b
| ALU_SUB => a - b
| ALU_SLL => Z.shiftl a (Z.land b shmask)
| ALU_SLT => if bv_swrap width a <? bv_swrap width b then 1 else 0
| ALU_SLTU => if a <? b then 1 else 0
| ALU_XOR => Z.lxor a b
| ALU_SRL => Z.shiftr a (Z.land b shmask)
| ALU_SRA => Z.shiftr (bv_swrap width a) (Z.land b shmask)
| ALU_OR => Z.lor a b
| ALU_AND => Z.land a b
end.
Definition zalu64 (op : aluop) (a b : Z) : Z :=
zcanon (zalu_raw 63 64 op (zcanon a) (zcanon b)).
Definition zalu32 (op : aluop) (a b : Z) : Z :=
zcanon (bv_swrap 32 (zalu_raw 31 32 op (zu32 a) (zu32 b))).
Definition zmd_raw (width : N) (op : mulop) (a b : Z) : Z :=
let sa := bv_swrap width a in
let sb := bv_swrap width b in
match op with
| M_MUL => a * b
| M_MULH => Z.shiftr (sa * sb) (Z.of_N width)
| M_MULHSU => Z.shiftr (sa * b) (Z.of_N width)
| M_MULHU => Z.shiftr (a * b) (Z.of_N width)
| M_DIV => if b =? 0 then -1 else Z.quot sa sb
| M_DIVU => if b =? 0 then -1 else Z.div a b
| M_REM => if b =? 0 then a else Z.rem sa sb
| M_REMU => if b =? 0 then a else Z.modulo a b
end.
Definition zmd64 (op : mulop) (a b : Z) : Z :=
zcanon (zmd_raw 64 op (zcanon a) (zcanon b)).
Definition zmd32 (op : mulop) (a b : Z) : Z :=
zcanon (bv_swrap 32 (zmd_raw 32 op (zu32 a) (zu32 b))).
Definition zext_low (sg : bool) (w : N) (a : Z) : Z :=
let l := (zcanon a) mod 2 ^ Z.of_N w in
zcanon (if sg then bv_swrap w l else l).
Inductive fpop1 : Type :=
| FP1_nanbox
| FP1_sqrt (fmt : ffmt) (md : rmode)
| FP1_class (fmt : ffmt)
| FP1_cvt (dst src : fcvt_ty) (md : rmode).
Inductive fpop2 : Type :=
| FP2_sgnj (op : fsgnop) (fmt : ffmt)
| FP2_ari (op : fariop) (fmt : ffmt) (md : rmode)
| FP2_minmax (op : fminmaxop) (fmt : ffmt)
| FP2_cmp (op : fcmpop) (fmt : ffmt).
Inductive fpop3 : Type :=
| FP3_fma (op : fmaop) (fmt : ffmt) (md : rmode).
Definition fp_arg (fmt : ffmt) (w : word) : Z :=
match fmt with FMT_S => bv_unsigned (unbox_s w) | FMT_D => bv_unsigned w end.
Definition fp_res (fmt : ffmt) (v : Z) : word :=
match fmt with FMT_S => nan_box (Z_to_bv 32 v) | FMT_D => Z_to_bv 64 v end.
Definition fari_sem (op : fariop) (f : format) (md : rmode) (a b : Z) : Z * fflags :=
match op with
| F_ADD => fp_add f md a b | F_SUB => fp_sub f md a b
| F_MUL => fp_mul f md a b | F_DIV => fp_div f md a b
end.
Definition fcmp_sem (op : fcmpop) (f : format) (a b : Z) : bool * fflags :=
match op with F_EQ => fp_eq f a b | F_LT => fp_lt f a b | F_LE => fp_le f a b end.
Definition fma_args (op : fmaop) (f : format) (a z : Z) : Z * Z :=
match op with
| F_MADD => (a, z) | F_MSUB => (a, fp_neg f z)
| F_NMSUB => (fp_neg f a, z) | F_NMADD => (fp_neg f a, fp_neg f z)
end.
Definition fcvt_ity (t : fcvt_ty) : option (bool * Z) :=
match t with
| FC_W => Some (true, 32) | FC_WU => Some (false, 32)
| FC_L => Some (true, 64) | FC_LU => Some (false, 64)
| _ => None
end.
Definition fcvt_fty (t : fcvt_ty) : option ffmt :=
match t with FC_S => Some FMT_S | FC_D => Some FMT_D | _ => None end.
Definition int_res (bits v : Z) : word :=
if bits =? 32 then sext 64 (Z_to_bv 32 v) else Z_to_bv 64 v.
Definition fcvt_denot (dst src : fcvt_ty) (md : rmode) (a : word) : word :=
match fcvt_fty dst, fcvt_fty src with
| Some df, Some sf => fp_res df (fst (fp_convert (fp_format sf) (fp_format df) md (fp_arg sf a)))
| None, Some sf =>
match fcvt_ity dst with
| Some (sgn, bits) => int_res bits (fst (fp_to_int (fp_format sf) md sgn bits (fp_arg sf a)))
| None => w0
end
| Some df, None =>
match fcvt_ity src with
| Some (sgn, bits) => fp_res df (fst (fp_of_int (fp_format df) md sgn bits (bv_unsigned a)))
| None => w0
end
| None, None => w0
end.
Definition fpop1_denot (op : fpop1) (a : word) : word :=
match op with
| FP1_nanbox => nan_box (low32 a)
| FP1_sqrt fmt md => fp_res fmt (fst (fp_sqrt (fp_format fmt) md (fp_arg fmt a)))
| FP1_class fmt => Z_to_bv 64 (fp_class (fp_format fmt) (fp_arg fmt a))
| FP1_cvt dst src md => fcvt_denot dst src md a
end.
Definition fpop2_denot (op : fpop2) (a b : word) : word :=
match op with
| FP2_sgnj o fmt =>
match fmt with
| FMT_S => nan_box (sgnj_val o (unbox_s a) (unbox_s b))
| FMT_D => sgnj_val o a b
end
| FP2_ari o fmt md => fp_res fmt (fst (fari_sem o (fp_format fmt) md (fp_arg fmt a) (fp_arg fmt b)))
| FP2_minmax o fmt =>
fp_res fmt (fst (fp_minmax (fp_format fmt) (match o with F_MIN => false | F_MAX => true end)
(fp_arg fmt a) (fp_arg fmt b)))
| FP2_cmp o fmt => if fst (fcmp_sem o (fp_format fmt) (fp_arg fmt a) (fp_arg fmt b)) then w1 else w0
end.
Definition fpop3_denot (op : fpop3) (a b c : word) : word :=
match op with
| FP3_fma o fmt md =>
let f := fp_format fmt in
let '(a', c') := fma_args o f (fp_arg fmt a) (fp_arg fmt c) in
fp_res fmt (fst (fp_fma f md a' (fp_arg fmt b) c'))
end.
Scheme Equality for ffmt.
Scheme Equality for rmode.
Scheme Equality for fariop.
Scheme Equality for fmaop.
Scheme Equality for fsgnop.
Scheme Equality for fminmaxop.
Scheme Equality for fcmpop.
Scheme Equality for fcvt_ty.
Definition fpop1_beq (x y : fpop1) : bool :=
match x, y with
| FP1_nanbox, FP1_nanbox => true
| FP1_sqrt f m, FP1_sqrt f' m' => ffmt_beq f f' && rmode_beq m m'
| FP1_class f, FP1_class f' => ffmt_beq f f'
| FP1_cvt d s m, FP1_cvt d' s' m' => fcvt_ty_beq d d' && fcvt_ty_beq s s' && rmode_beq m m'
| _, _ => false
end.
Definition fpop2_beq (x y : fpop2) : bool :=
match x, y with
| FP2_sgnj o f, FP2_sgnj o' f' => fsgnop_beq o o' && ffmt_beq f f'
| FP2_ari o f m, FP2_ari o' f' m' => fariop_beq o o' && ffmt_beq f f' && rmode_beq m m'
| FP2_minmax o f, FP2_minmax o' f' => fminmaxop_beq o o' && ffmt_beq f f'
| FP2_cmp o f, FP2_cmp o' f' => fcmpop_beq o o' && ffmt_beq f f'
| _, _ => false
end.
Definition fpop3_beq (x y : fpop3) : bool :=
match x, y with
| FP3_fma o f m, FP3_fma o' f' m' => fmaop_beq o o' && ffmt_beq f f' && rmode_beq m m'
end.
Lemma ffmt_beq_eq : forall o p, ffmt_beq o p = true -> o = p.
Proof. intros o p H. destruct o, p; cbn in H; congruence. Qed.
Lemma rmode_beq_eq : forall o p, rmode_beq o p = true -> o = p.
Proof. intros o p H. destruct o, p; cbn in H; congruence. Qed.
Lemma fariop_beq_eq : forall o p, fariop_beq o p = true -> o = p.
Proof. intros o p H. destruct o, p; cbn in H; congruence. Qed.
Lemma fmaop_beq_eq : forall o p, fmaop_beq o p = true -> o = p.
Proof. intros o p H. destruct o, p; cbn in H; congruence. Qed.
Lemma fsgnop_beq_eq : forall o p, fsgnop_beq o p = true -> o = p.
Proof. intros o p H. destruct o, p; cbn in H; congruence. Qed.
Lemma fminmaxop_beq_eq : forall o p, fminmaxop_beq o p = true -> o = p.
Proof. intros o p H. destruct o, p; cbn in H; congruence. Qed.
Lemma fcmpop_beq_eq : forall o p, fcmpop_beq o p = true -> o = p.
Proof. intros o p H. destruct o, p; cbn in H; congruence. Qed.
Lemma fcvt_ty_beq_eq : forall o p, fcvt_ty_beq o p = true -> o = p.
Proof. intros o p H. destruct o, p; cbn in H; congruence. Qed.
Ltac beq_eq_tac :=
intros x y H; destruct x, y; cbn in H; try discriminate;
repeat match goal with
| H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
end;
repeat match goal with
| H : ffmt_beq _ _ = true |- _ => apply ffmt_beq_eq in H
| H : rmode_beq _ _ = true |- _ => apply rmode_beq_eq in H
| H : fariop_beq _ _ = true |- _ => apply fariop_beq_eq in H
| H : fmaop_beq _ _ = true |- _ => apply fmaop_beq_eq in H
| H : fsgnop_beq _ _ = true |- _ => apply fsgnop_beq_eq in H
| H : fminmaxop_beq _ _ = true |- _ => apply fminmaxop_beq_eq in H
| H : fcmpop_beq _ _ = true |- _ => apply fcmpop_beq_eq in H
| H : fcvt_ty_beq _ _ = true |- _ => apply fcvt_ty_beq_eq in H
end; subst; reflexivity.
Lemma fpop1_beq_eq : forall x y, fpop1_beq x y = true -> x = y.
Proof. beq_eq_tac. Qed.
Lemma fpop2_beq_eq : forall x y, fpop2_beq x y = true -> x = y.
Proof. beq_eq_tac. Qed.
Lemma fpop3_beq_eq : forall x y, fpop3_beq x y = true -> x = y.
Proof. beq_eq_tac. Qed.
Inductive sv : Type :=
| SLit (z : Z)
| SOff (n : nat) (z : Z)
| SAlu (op : aluop) (a b : sv)
| SAluw (op : aluop) (a b : sv)
| SMd (op : mulop) (a b : sv)
| SMdw (op : mulop) (a b : sv)
| SExt (sg : bool) (w : N) (a : sv)
| SData (d : nat) (i : Z) (n : N)
| SF1 (op : fpop1) (a : sv)
| SF2 (op : fpop2) (a b : sv)
| SF3 (op : fpop3) (a b c : sv).
Record env := mkEnv { ew : nat -> word; ed : nat -> list byte }.
Definition data_word (E : env) (d : nat) (i : Z) (n : N) : Z :=
bytes_le_to_Z (firstn (N.to_nat n) (skipn (Z.to_nat i) (ed E d))).
Fixpoint sv_denot (E : env) (v : sv) : word :=
match v with
| SLit z => Z_to_bv 64 z
| SOff n z => Z_to_bv 64 (bv_unsigned (ew E n) + z)
| SData d i n => Z_to_bv 64 (data_word E d i n)
| SAlu op a b => alu64 op (sv_denot E a) (sv_denot E b)
| SAluw op a b => sext 64 (alu32 op (low32 (sv_denot E a)) (low32 (sv_denot E b)))
| SMd op a b => mul_div op (sv_denot E a) (sv_denot E b)
| SMdw op a b => sext 64 (mul_div op (low32 (sv_denot E a)) (low32 (sv_denot E b)))
| SExt sg w a => if sg then sext 64 (bv_extract 0 w (sv_denot E a))
else zext 64 (bv_extract 0 w (sv_denot E a))
| SF1 op a => fpop1_denot op (sv_denot E a)
| SF2 op a b => fpop2_denot op (sv_denot E a) (sv_denot E b)
| SF3 op a b c => fpop3_denot op (sv_denot E a) (sv_denot E b) (sv_denot E c)
end.
Scheme Equality for aluop.
Scheme Equality for mulop.
Fixpoint sv_eqb (a b : sv) : bool :=
match a, b with
| SLit x, SLit y => Z.eqb x y
| SOff n x, SOff m y => Nat.eqb n m && Z.eqb x y
| SAlu o a1 a2, SAlu p b1 b2 => aluop_beq o p && sv_eqb a1 b1 && sv_eqb a2 b2
| SAluw o a1 a2, SAluw p b1 b2 => aluop_beq o p && sv_eqb a1 b1 && sv_eqb a2 b2
| SMd o a1 a2, SMd p b1 b2 => mulop_beq o p && sv_eqb a1 b1 && sv_eqb a2 b2
| SMdw o a1 a2, SMdw p b1 b2 => mulop_beq o p && sv_eqb a1 b1 && sv_eqb a2 b2
| SExt s w a1, SExt t x b1 => Bool.eqb s t && N.eqb w x && sv_eqb a1 b1
| SData d i w, SData d' i' w' => Nat.eqb d d' && Z.eqb i i' && N.eqb w w'
| SF1 o a1, SF1 p b1 => fpop1_beq o p && sv_eqb a1 b1
| SF2 o a1 a2, SF2 p b1 b2 => fpop2_beq o p && sv_eqb a1 b1 && sv_eqb a2 b2
| SF3 o a1 a2 a3, SF3 p b1 b2 b3 => fpop3_beq o p && sv_eqb a1 b1 && sv_eqb a2 b2 && sv_eqb a3 b3
| _, _ => false
end.
Lemma aluop_beq_eq : forall o p, aluop_beq o p = true -> o = p.
Proof. intros o p H. destruct o, p; cbn in H; congruence. Qed.
Lemma mulop_beq_eq : forall o p, mulop_beq o p = true -> o = p.
Proof. intros o p H. destruct o, p; cbn in H; congruence. Qed.
Lemma sv_eqb_eq : forall a b, sv_eqb a b = true -> a = b.
Proof.
induction a; destruct b; cbn; intros H; try discriminate;
repeat match goal with
| H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
end;
repeat match goal with
| H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
| H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
| H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H
| H : Bool.eqb _ _ = true |- _ => apply eqb_prop in H
| H : aluop_beq _ _ = true |- _ => apply aluop_beq_eq in H
| H : mulop_beq _ _ = true |- _ => apply mulop_beq_eq in H
| H : fpop1_beq _ _ = true |- _ => apply fpop1_beq_eq in H
| H : fpop2_beq _ _ = true |- _ => apply fpop2_beq_eq in H
| H : fpop3_beq _ _ = true |- _ => apply fpop3_beq_eq in H
end; subst; f_equal; auto.
Qed.
Lemma sv_eqb_denot : forall E a b, sv_eqb a b = true -> sv_denot E a = sv_denot E b.
Proof. intros E a b H. apply sv_eqb_eq in H. subst. reflexivity. Qed.
Lemma zcanon_wrap : forall z, zcanon z = bv_wrap 64 z.
Proof. reflexivity. Qed.
Lemma zu32_wrap : forall z, zu32 z = bv_wrap 32 z.
Proof. reflexivity. Qed.
Lemma zcanon_range : forall z, 0 <= zcanon z < 2^64.
Proof. intros z. unfold zcanon, M64. apply Z.mod_pos_bound. lia. Qed.
Lemma zcanon_small : forall z, 0 <= z < 2^64 -> zcanon z = z.
Proof. intros z H. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma Z_to_bv64_canon : forall z, Z_to_bv 64 (zcanon z) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. apply (bv_wrap_idemp 64 z).
Qed.
Lemma unsigned_lit : forall z, bv_unsigned (Z_to_bv 64 z) = zcanon z.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma signed_lit : forall z, bv_signed (Z_to_bv 64 z) = bv_swrap 64 (zcanon z).
Proof. intros z. rewrite Z_to_bv_signed. symmetry. apply (bv_swrap_wrap 64 z). Qed.
Lemma lit_of_word : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply Z_to_bv_bv_unsigned. Qed.
Lemma zcanon_unsigned : forall (x : word), zcanon (bv_unsigned x) = bv_unsigned x.
Proof. intros x. apply zcanon_small. apply (bv_unsigned_in_range 64 x). Qed.
Lemma land63_lit : forall b,
bv_unsigned (bv_and (Z_to_bv 64 b) (Z_to_bv 64 63)) = Z.land (zcanon b) 63.
Proof. intros b. rewrite bv_and_unsigned, !unsigned_lit. reflexivity. Qed.
Lemma Z_land_63_range : forall b, 0 <= Z.land b 63 < 64.
Proof.
intros b. split; [apply Z.land_nonneg; right; lia|].
change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia.
apply Z.mod_pos_bound. lia.
Qed.
Lemma Z_land_31_range : forall b, 0 <= Z.land b 31 < 32.
Proof.
intros b. split; [apply Z.land_nonneg; right; lia|].
change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia.
apply Z.mod_pos_bound. lia.
Qed.
Lemma zalu64_sound : forall op a b,
alu64 op (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (zalu64 op a b).
Proof.
intros op a b. unfold zalu64. rewrite Z_to_bv64_canon.
apply bv_eq. rewrite (Z_to_bv_unsigned 64 (zalu_raw _ _ _ _ _)).
pose proof (zcanon_range a) as Ha. pose proof (zcanon_range b) as Hb.
destruct op; cbn [alu64 alu zalu_raw].
- rewrite bv_add_unsigned, !unsigned_lit. reflexivity.
- rewrite bv_sub_unsigned, !unsigned_lit. reflexivity.
- rewrite bv_shiftl_unsigned, land63_lit, unsigned_lit. reflexivity.
- unfold bv_lts. rewrite !signed_lit.
destruct (Z.ltb _ _); rewrite Z_to_bv_unsigned; reflexivity.
- unfold bv_ltu. rewrite !unsigned_lit.
destruct (Z.ltb _ _); rewrite Z_to_bv_unsigned; reflexivity.
- rewrite bv_xor_unsigned, !unsigned_lit. symmetry. apply bv_wrap_small.
change (bv_modulus 64) with (2^64). apply Z_lxor_range; assumption.
- rewrite bv_shiftr_unsigned, land63_lit, unsigned_lit. symmetry. apply bv_wrap_small.
change (bv_modulus 64) with (2^64). apply Z_shiftr_range; [assumption|].
apply Z_land_63_range.
- rewrite bv_ashiftr_unsigned, land63_lit, signed_lit. reflexivity.
- rewrite bv_or_unsigned, !unsigned_lit. symmetry. apply bv_wrap_small.
change (bv_modulus 64) with (2^64). apply Z_lor_range; assumption.
- rewrite bv_and_unsigned, !unsigned_lit. symmetry. apply bv_wrap_small.
change (bv_modulus 64) with (2^64). apply Z_land_range; lia.
Qed.
Lemma alu64_unsigned : forall op (x y : word),
bv_unsigned (alu64 op x y) = bv_wrap 64 (zalu_raw 63 64 op (bv_unsigned x) (bv_unsigned y)).
Proof.
intros op x y.
rewrite <- (lit_of_word x) at 1. rewrite <- (lit_of_word y) at 1.
rewrite zalu64_sound, Z_to_bv_unsigned. unfold zalu64.
rewrite !zcanon_unsigned. unfold zcanon, M64. apply (bv_wrap_idemp 64).
Qed.
Lemma low32_lit_unsigned : forall a, bv_unsigned (low32 (Z_to_bv 64 a)) = zu32 a.
Proof.
intros a. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
unfold zu32, M32.
change (bv_wrap 32 (bv_wrap 64 a)) with ((a mod 2^64) mod 2^32).
apply Z.mod_mod_divide. exists (2^32). reflexivity.
Qed.
Lemma zu32_range : forall z, 0 <= zu32 z < 2^32.
Proof. intros z. unfold zu32, M32. apply Z.mod_pos_bound. lia. Qed.
Lemma land31_lit : forall (y : bv 32),
bv_unsigned (bv_and y (Z_to_bv 32 31)) = Z.land (bv_unsigned y) 31.
Proof. intros y. rewrite bv_and_unsigned, Z_to_bv_unsigned. reflexivity. Qed.
Lemma alu32_unsigned : forall op (x y : bv 32),
bv_unsigned (alu32 op x y) = bv_wrap 32 (zalu_raw 31 32 op (bv_unsigned x) (bv_unsigned y)).
Proof.
intros op x y.
pose proof (bv_unsigned_in_range 32 x) as Hx. pose proof (bv_unsigned_in_range 32 y) as Hy.
change (bv_modulus 32) with (2^32) in Hx, Hy.
destruct op; cbn [alu32 alu zalu_raw].
- apply bv_add_unsigned.
- apply bv_sub_unsigned.
- rewrite bv_shiftl_unsigned, land31_lit. reflexivity.
- unfold bv_lts. destruct (Z.ltb _ _); rewrite Z_to_bv_unsigned; reflexivity.
- unfold bv_ltu. destruct (Z.ltb _ _); rewrite Z_to_bv_unsigned; reflexivity.
- rewrite bv_xor_unsigned. symmetry. apply bv_wrap_small.
change (bv_modulus 32) with (2^32).
split; [apply Z.lxor_nonneg; lia|].
apply (Z_bounded_by_bits 32); [lia| apply Z.lxor_nonneg; lia|].
intros k Hk. rewrite Z.lxor_spec, !(Z_testbit_high 32) by lia. reflexivity.
- rewrite bv_shiftr_unsigned, land31_lit. symmetry. apply bv_wrap_small.
change (bv_modulus 32) with (2^32).
pose proof (Z_land_31_range (bv_unsigned y)).
split; [apply Z.shiftr_nonneg; lia|].
rewrite Z.shiftr_div_pow2 by lia.
apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
pose proof (Z.pow_pos_nonneg 2 (Z.land (bv_unsigned y) 31)). nia.
- rewrite bv_ashiftr_unsigned, land31_lit. reflexivity.
- rewrite bv_or_unsigned. symmetry. apply bv_wrap_small.
change (bv_modulus 32) with (2^32).
split; [apply Z.lor_nonneg; lia|].
apply (Z_bounded_by_bits 32); [lia| apply Z.lor_nonneg; lia|].
intros k Hk. rewrite Z.lor_spec, !(Z_testbit_high 32) by lia. reflexivity.
- rewrite bv_and_unsigned. symmetry. apply bv_wrap_small.
change (bv_modulus 32) with (2^32).
split; [apply Z.land_nonneg; lia|].
apply (Z_bounded_by_bits 32); [lia| apply Z.land_nonneg; lia|].
intros k Hk. rewrite Z.land_spec, !(Z_testbit_high 32) by lia. reflexivity.
Qed.
Lemma zalu32_sound : forall op a b,
sext 64 (alu32 op (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b))) = Z_to_bv 64 (zalu32 op a b).
Proof.
intros op a b. unfold zalu32. rewrite Z_to_bv64_canon.
apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned. f_equal.
unfold bv_signed. rewrite alu32_unsigned, !low32_lit_unsigned. apply (bv_swrap_wrap 32).
Qed.
Lemma zmd64_sound : forall op a b,
mul_div op (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (zmd64 op a b).
Proof.
intros op a b. unfold zmd64. rewrite Z_to_bv64_canon.
apply bv_eq. rewrite (Z_to_bv_unsigned 64 (zmd_raw _ _ _ _)).
pose proof (zcanon_range a) as Ha. pose proof (zcanon_range b) as Hb.
destruct op; cbn [mul_div zmd_raw]; rewrite ?unsigned_lit, ?signed_lit.
- rewrite bv_mul_unsigned, !unsigned_lit. reflexivity.
- unfold bv_mulhss. rewrite Z_to_bv_unsigned, !signed_lit. reflexivity.
- unfold bv_mulhsu. rewrite Z_to_bv_unsigned, !signed_lit, unsigned_lit. reflexivity.
- unfold bv_mulhuu. rewrite Z_to_bv_unsigned, !unsigned_lit. reflexivity.
- destruct (Z.eqb _ 0); [rewrite Z_to_bv_unsigned; reflexivity|].
rewrite bv_quots_unsigned, !signed_lit. reflexivity.
- destruct (Z.eqb (zcanon b) 0) eqn:Hz; [rewrite Z_to_bv_unsigned; reflexivity|].
rewrite bv_divu_unsigned, !unsigned_lit. symmetry. apply bv_wrap_small.
change (bv_modulus 64) with (2^64). apply Z.eqb_neq in Hz.
split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. nia.
- destruct (Z.eqb _ 0); [rewrite unsigned_lit; symmetry; apply zcanon_small; exact Ha|].
rewrite bv_rems_unsigned, !signed_lit. reflexivity.
- destruct (Z.eqb (zcanon b) 0) eqn:Hz; [rewrite unsigned_lit; symmetry; apply zcanon_small; exact Ha|].
rewrite bv_modu_unsigned, !unsigned_lit. symmetry. apply bv_wrap_small.
change (bv_modulus 64) with (2^64). apply Z.eqb_neq in Hz.
pose proof (Z.mod_pos_bound (zcanon a) (zcanon b)). lia.
Qed.
Lemma mul_div_unsigned : forall n op (x y : bv n),
bv_unsigned (mul_div op x y) = bv_wrap n (zmd_raw n op (bv_unsigned x) (bv_unsigned y)).
Proof.
intros n op x y.
pose proof (bv_unsigned_in_range n x) as Hx. pose proof (bv_unsigned_in_range n y) as Hy.
destruct op; cbn [mul_div zmd_raw]; fold (bv_signed x) (bv_signed y).
- apply bv_mul_unsigned.
- unfold bv_mulhss. rewrite Z_to_bv_unsigned. reflexivity.
- unfold bv_mulhsu. rewrite Z_to_bv_unsigned. reflexivity.
- unfold bv_mulhuu. rewrite Z_to_bv_unsigned. reflexivity.
- destruct (Z.eqb _ 0); [rewrite Z_to_bv_unsigned; reflexivity|].
rewrite bv_quots_unsigned. reflexivity.
- destruct (Z.eqb (bv_unsigned y) 0) eqn:Hz; [rewrite Z_to_bv_unsigned; reflexivity|].
rewrite bv_divu_unsigned. symmetry. apply bv_wrap_small. apply Z.eqb_neq in Hz.
split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. nia.
- destruct (Z.eqb _ 0); [symmetry; apply bv_wrap_small; lia|].
rewrite bv_rems_unsigned. reflexivity.
- destruct (Z.eqb (bv_unsigned y) 0) eqn:Hz; [symmetry; apply bv_wrap_small; lia|].
rewrite bv_modu_unsigned. symmetry. apply bv_wrap_small. apply Z.eqb_neq in Hz.
pose proof (Z.mod_pos_bound (bv_unsigned x) (bv_unsigned y)). lia.
Qed.
Lemma zmd32_sound : forall op a b,
sext 64 (mul_div op (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b))) = Z_to_bv 64 (zmd32 op a b).
Proof.
intros op a b. unfold zmd32. rewrite Z_to_bv64_canon.
apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned. f_equal.
unfold bv_signed. rewrite mul_div_unsigned, !low32_lit_unsigned. apply (bv_swrap_wrap 32).
Qed.
Lemma zext_low_sound : forall (sg : bool) (w : N) (a : Z),
(if sg then sext 64 (bv_extract 0 w (Z_to_bv 64 a)) else zext 64 (bv_extract 0 w (Z_to_bv 64 a)))
= Z_to_bv 64 (zext_low sg w a).
Proof.
intros sg w a. unfold zext_low. rewrite Z_to_bv64_canon.
apply bv_eq. destruct sg.
- unfold sext. rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned. f_equal.
- unfold zext. rewrite bv_zero_extend_unsigned', Z_to_bv_unsigned. f_equal.
Qed.
Record afact := mkAF { af_lo : Z; af_hi : Z; af_al2 : Z }.
Definition afact_ok (E : env) (n : nat) (f : afact) : Prop :=
af_lo f <= bv_unsigned (ew E n) <= af_hi f
/\ bv_unsigned (ew E n) mod 2 ^ (af_al2 f) = 0
/\ 0 <= af_al2 f <= 64.
Record acond := mkAC { ac_c : branch_cond; ac_a : sv; ac_b : sv }.
Record facts := mkFacts { f_atoms : list (nat * afact); f_conds : list acond; f_alias : list (sv * sv) }.
Fixpoint atoms_ok (E : env) (l : list (nat * afact)) : Prop :=
match l with
| [] => True
| (n, f) :: r => afact_ok E n f /\ atoms_ok E r
end.
Definition acond_ok (E : env) (c : acond) : Prop :=
branch_taken (ac_c c) (sv_denot E (ac_a c)) (sv_denot E (ac_b c)) = true.
Fixpoint conds_ok (E : env) (l : list acond) : Prop :=
match l with
| [] => True
| c :: r => acond_ok E c /\ conds_ok E r
end.
Fixpoint alias_ok (E : env) (l : list (sv * sv)) : Prop :=
match l with
| [] => True
| (a, b) :: r => sv_denot E a = sv_denot E b /\ alias_ok E r
end.
Definition facts_ok (E : env) (G : facts) : Prop :=
atoms_ok E (f_atoms G) /\ (conds_ok E (f_conds G) /\ alias_ok E (f_alias G)).
Fixpoint alias_lookup (l : list (sv * sv)) (v : sv) : sv :=
match l with
| [] => v
| (a, b) :: r => if sv_eqb a v then b else alias_lookup r v
end.
Lemma alias_lookup_sound : forall E l v, alias_ok E l -> sv_denot E (alias_lookup l v) = sv_denot E v.
Proof.
induction l as [|[a b] r IH]; cbn; intros v H; [reflexivity|].
destruct H as [Hab Hr]. destruct (sv_eqb a v) eqn:He.
- apply sv_eqb_eq in He. subst. symmetry. exact Hab.
- apply IH. exact Hr.
Qed.
Definition aliased (G : facts) (v : sv) : sv := alias_lookup (f_alias G) v.
Lemma aliased_sound : forall E G v, facts_ok E G -> sv_denot E (aliased G v) = sv_denot E v.
Proof. intros E G v (_ & _ & Ha). apply alias_lookup_sound. exact Ha. Qed.
Fixpoint atom_lookup (l : list (nat * afact)) (n : nat) : option afact :=
match l with
| [] => None
| (m, f) :: r => if Nat.eqb m n then Some f else atom_lookup r n
end.
Lemma atom_lookup_ok : forall E l n f,
atoms_ok E l -> atom_lookup l n = Some f -> afact_ok E n f.
Proof.
induction l as [|[m g] r IH]; cbn; intros n f Hok Hl; [discriminate|].
destruct Hok as [Hg Hr].
destruct (Nat.eqb m n) eqn:Hmn.
- apply Nat.eqb_eq in Hmn. subst. congruence.
- eapply IH; eauto.
Qed.
Fixpoint sv_range (G : facts) (v : sv) : option (Z * Z) :=
match v with
| SLit z => Some (zcanon z, zcanon z)
| SOff n x =>
match atom_lookup (f_atoms G) n with
| Some f => if (0 <=? af_lo f + x) && (af_hi f + x <? M64)
then Some (af_lo f + x, af_hi f + x) else None
| None => None
end
| SExt false w a => if (Z.of_N w <? 64) then Some (0, 2 ^ Z.of_N w - 1) else None
| SAlu ALU_SLTU _ _ => Some (0, 1)
| SAlu ALU_SLT _ _ => Some (0, 1)
| SAlu ALU_AND a (SLit m) => if 0 <=? m then
match sv_range G a with
| Some (lo, hi) => Some (0, Z.min hi (zcanon m))
| None => Some (0, zcanon m)
end
else None
| SAlu ALU_SRL a (SLit s) =>
match sv_range G a with
| Some (lo, hi) => Some (Z.shiftr lo (Z.land (zcanon s) 63), Z.shiftr hi (Z.land (zcanon s) 63))
| None => None
end
| _ => None
end.
Lemma denot_SOff : forall E n x, bv_unsigned (sv_denot E (SOff n x)) = zcanon (bv_unsigned (ew E n) + x).
Proof. intros. cbn. apply unsigned_lit. Qed.
Lemma Z_land_upper : forall a m, 0 <= m -> 0 <= Z.land a m <= m.
Proof.
intros a m Hm. split; [apply Z.land_nonneg; right; lia|].
destruct (Z.eq_dec m 0) as [->|Hne]; [rewrite Z.land_0_r; lia|].
assert (Hlog : 0 <= Z.log2 m) by (apply Z.log2_nonneg).
apply Z.ldiff_le; [lia|].
apply Z.bits_inj'. intros k Hk.
rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit a k), (Z.testbit m k); reflexivity.
Qed.
Lemma Z_land_upper_l : forall a m, 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
intros a m Ha Hm. rewrite Z.land_comm. pose proof (Z_land_upper m a Ha). lia.
Qed.
Lemma sv_range_sound : forall E G v lo hi,
facts_ok E G -> sv_range G v = Some (lo, hi) ->
lo <= bv_unsigned (sv_denot E v) <= hi.
Proof.
intros E G v. induction v; intros lo hi HG Hr; cbn in Hr; try discriminate.
- injection Hr as <- <-. cbn. rewrite unsigned_lit. lia.
- destruct (atom_lookup (f_atoms G) n) as [f|] eqn:Hl; [|discriminate].
destruct (0 <=? af_lo f + z) eqn:H1; [|discriminate].
destruct (af_hi f + z <? M64) eqn:H2; [|discriminate].
cbn in Hr. injection Hr as <- <-.
apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hl) as (Hb & _ & _).
rewrite denot_SOff. unfold M64 in H2. rewrite zcanon_small by lia. lia.
- destruct op; try discriminate.
+ injection Hr as <- <-. cbn [sv_denot]. cbn [alu64 alu].
destruct (bv_lts _ _);
[change (bv_unsigned (Z_to_bv 64 1)) with 1 | change (bv_unsigned (Z_to_bv 64 0)) with 0]; lia.
+ injection Hr as <- <-. cbn [sv_denot]. cbn [alu64 alu].
destruct (bv_ltu _ _);
[change (bv_unsigned (Z_to_bv 64 1)) with 1 | change (bv_unsigned (Z_to_bv 64 0)) with 0]; lia.
+ destruct v2; try discriminate.
pose proof (zcanon_range z) as Hz.
destruct (sv_range G v1) as [[lo1 hi1]|] eqn:Hr1.
* injection Hr as <- <-. cbn [sv_denot].
rewrite alu64_unsigned. cbn [zalu_raw]. rewrite unsigned_lit.
specialize (IHv1 lo1 hi1 HG eq_refl).
pose proof (u64_range (sv_denot E v1)) as Hv.
pose proof (Z_land_63_range (zcanon z)) as Hs.
assert (Hsh : 0 <= bv_unsigned (sv_denot E v1) ≫ Z.land (zcanon z) 63 <= bv_unsigned (sv_denot E v1)).
{ split; [apply Z.shiftr_nonneg; lia|].
rewrite Z.shiftr_div_pow2 by lia.
apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
pose proof (Z.pow_pos_nonneg 2 (Z.land (zcanon z) 63)). nia. }
rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia).
rewrite !Z.shiftr_div_pow2 by lia.
split; apply Z.div_le_mono; try lia; apply Z.pow_pos_nonneg; lia.
* discriminate.
+ destruct v2; try discriminate.
destruct (0 <=? z) eqn:Hz0; [|discriminate]. apply Z.leb_le in Hz0.
pose proof (zcanon_range z) as Hz.
assert (Hland : 0 <= Z.land (bv_unsigned (sv_denot E v1)) (zcanon z) <= zcanon z)
by (apply Z_land_upper; lia).
assert (Hden : bv_unsigned (sv_denot E (SAlu ALU_AND v1 (SLit z)))
= Z.land (bv_unsigned (sv_denot E v1)) (zcanon z)).
{ cbn [sv_denot]. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite unsigned_lit.
apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
rewrite Hden.
destruct (sv_range G v1) as [[lo1 hi1]|] eqn:Hr1.
* injection Hr as <- <-. specialize (IHv1 lo1 hi1 HG eq_refl).
pose proof (Z_land_upper_l (bv_unsigned (sv_denot E v1)) (zcanon z)).
pose proof (u64_range (sv_denot E v1)). lia.
* injection Hr as <- <-. lia.
- destruct sg; [discriminate|].
destruct (Z.of_N w <? 64) eqn:Hw; [|discriminate]. apply Z.ltb_lt in Hw.
injection Hr as <- <-. cbn [sv_denot].
unfold zext. rewrite bv_zero_extend_unsigned', bv_extract_unsigned, Z.shiftr_0_r.
pose proof (bv_wrap_in_range w (bv_unsigned (sv_denot E v))) as Hr.
unfold bv_modulus in Hr.
rewrite bv_wrap_small.
+ lia.
+ change (bv_modulus 64) with (2^64).
assert (2 ^ Z.of_N w <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Scheme Equality for branch_cond.
Definition neg_bc (c : branch_cond) : branch_cond :=
match c with
| BC_EQ => BC_NE | BC_NE => BC_EQ
| BC_LT => BC_GE | BC_GE => BC_LT
| BC_LTU => BC_GEU | BC_GEU => BC_LTU
end.
Lemma branch_taken_neg : forall c a b,
branch_taken (neg_bc c) a b = negb (branch_taken c a b).
Proof. intros c a b. destruct c; cbn; rewrite ?negb_involutive; reflexivity. Qed.
Fixpoint cond_assumed (l : list acond) (c : branch_cond) (a b : sv) : bool :=
match l with
| [] => false
| ac :: r => (branch_cond_beq (ac_c ac) c && sv_eqb (ac_a ac) a && sv_eqb (ac_b ac) b)
|| cond_assumed r c a b
end.
Lemma branch_cond_beq_eq : forall c d, branch_cond_beq c d = true -> c = d.
Proof. intros c d H. destruct c, d; cbn in H; congruence. Qed.
Lemma cond_assumed_sound : forall E l c a b,
conds_ok E l -> cond_assumed l c a b = true ->
branch_taken c (sv_denot E a) (sv_denot E b) = true.
Proof.
induction l as [|ac r IH]; cbn; intros c a b Hok H; [discriminate|].
destruct Hok as [Hac Hr].
apply orb_prop in H. destruct H as [H|H]; [|eapply IH; eauto].
apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
apply branch_cond_beq_eq in H1. apply sv_eqb_eq in H2. apply sv_eqb_eq in H3.
subst. exact Hac.
Qed.
Definition ranges_ltu (ra rb : option (Z * Z)) : option bool :=
match ra, rb with
| Some (alo, ahi), Some (blo, bhi) =>
if ahi <? blo then Some true else if bhi <=? alo then Some false else None
| _, _ => None
end.
Definition ranges_disjoint (ra rb : option (Z * Z)) : bool :=
match ra, rb with
| Some (alo, ahi), Some (blo, bhi) => (ahi <? blo) || (bhi <? alo)
| _, _ => false
end.
Definition decide_eq (G : facts) (a b : sv) : option bool :=
if sv_eqb a b then Some true else
match a, b with
| SLit x, SLit y => Some (zcanon x =? zcanon y)
| SOff n x, SOff m y =>
if Nat.eqb n m then Some (zcanon x =? zcanon y)
else if ranges_disjoint (sv_range G a) (sv_range G b) then Some false else None
| SOff n x, SLit c | SLit c, SOff n x =>
if ranges_disjoint (sv_range G a) (sv_range G b) then Some false else
match atom_lookup (f_atoms G) n with
| Some f => if negb ((c - x) mod 2 ^ af_al2 f =? 0) then Some false else None
| None => None
end
| _, _ => if ranges_disjoint (sv_range G a) (sv_range G b) then Some false else None
end.
Definition decide_ltu (G : facts) (a b : sv) : option bool :=
if sv_eqb a b then Some false else
match ranges_ltu (sv_range G a) (sv_range G b) with
| Some r => Some r
| None =>
match a, b with
| SOff n x, SOff m y =>
if Nat.eqb n m then
match sv_range G a, sv_range G b with
| Some _, Some _ => Some (x <? y)
| _, _ => None
end
else None
| _, _ => None
end
end.
Definition half64 : Z := 2 ^ 63.
Definition decide_lts (G : facts) (a b : sv) : option bool :=
if sv_eqb a b then Some false else
match sv_range G a, sv_range G b with
| Some (alo, ahi), Some (blo, bhi) =>
if (ahi <? half64) && (bhi <? half64) then decide_ltu G a b
else None
| _, _ => None
end.
Definition decide_cond (G : facts) (c : branch_cond) (a b : sv) : option bool :=
if cond_assumed (f_conds G) c a b then Some true
else if cond_assumed (f_conds G) (neg_bc c) a b then Some false
else match c with
| BC_EQ => decide_eq G a b
| BC_NE => option_map negb (decide_eq G a b)
| BC_LTU => decide_ltu G a b
| BC_GEU => option_map negb (decide_ltu G a b)
| BC_LT => decide_lts G a b
| BC_GE => option_map negb (decide_lts G a b)
end.
Lemma ranges_disjoint_sound : forall E G a b,
facts_ok E G -> ranges_disjoint (sv_range G a) (sv_range G b) = true ->
sv_denot E a <> sv_denot E b.
Proof.
intros E G a b HG H Heq. unfold ranges_disjoint in H.
destruct (sv_range G a) as [[alo ahi]|] eqn:Ha; [|discriminate].
destruct (sv_range G b) as [[blo bhi]|] eqn:Hb; [|discriminate].
pose proof (sv_range_sound E G a alo ahi HG Ha).
pose proof (sv_range_sound E G b blo bhi HG Hb).
rewrite Heq in *. apply orb_prop in H. destruct H as [H|H]; apply Z.ltb_lt in H; lia.
Qed.
Lemma bv_eqb_unsigned : forall (a b : word), bv_eqb a b = (bv_unsigned a =? bv_unsigned b).
Proof. reflexivity. Qed.
Lemma mod_eq_small_diff : forall a b m, 0 < m ->
a mod m = b mod m -> - m < a - b < m -> a = b.
Proof.
intros a b m Hm Heq Hd.
pose proof (Z.div_mod a m ltac:(lia)) as Ha. pose proof (Z.div_mod b m ltac:(lia)) as Hb.
set (qa := a / m) in *. set (qb := b / m) in *.
assert (a - b = m * (qa - qb)) by lia.
assert (qa - qb = 0) by nia. lia.
Qed.
Lemma SOff_eq_iff : forall E n x y,
(sv_denot E (SOff n x) = sv_denot E (SOff n y)) <-> zcanon x = zcanon y.
Proof.
intros E n x y.
pose proof (zcanon_range x) as Hx. pose proof (zcanon_range y) as Hy.
assert (Hux : zcanon (bv_unsigned (ew E n) + x) = zcanon (bv_unsigned (ew E n) + zcanon x))
by (unfold zcanon, M64; rewrite Zplus_mod_idemp_r; reflexivity).
assert (Huy : zcanon (bv_unsigned (ew E n) + y) = zcanon (bv_unsigned (ew E n) + zcanon y))
by (unfold zcanon, M64; rewrite Zplus_mod_idemp_r; reflexivity).
split.
- intros H. apply (f_equal bv_unsigned) in H. rewrite !denot_SOff, Hux, Huy in H.
unfold zcanon, M64 in H, Hx, Hy. pose proof (u64_range (ew E n)).
apply (mod_eq_small_diff _ _ (2^64)) in H; [unfold zcanon, M64; lia | lia | lia].
- intros H. apply bv_eq. rewrite !denot_SOff, Hux, Huy, H. reflexivity.
Qed.
Lemma bv_eqb_false_iff : forall (a b : word), bv_eqb a b = false <-> a <> b.
Proof.
intros a b. rewrite bv_eqb_unsigned. rewrite Z.eqb_neq.
split; intros H Heq; apply H; [rewrite Heq; reflexivity | apply bv_eq; exact Heq].
Qed.
Lemma bv_eqb_true_iff : forall (a b : word), bv_eqb a b = true <-> a = b.
Proof.
intros a b. rewrite bv_eqb_unsigned. rewrite Z.eqb_eq.
split; intros H; [apply bv_eq; exact H | rewrite H; reflexivity].
Qed.
Lemma ranges_disjoint_eqb : forall E G a b,
facts_ok E G -> ranges_disjoint (sv_range G a) (sv_range G b) = true ->
bv_eqb (sv_denot E a) (sv_denot E b) = false.
Proof.
intros E G a b HG H. apply bv_eqb_false_iff. eapply ranges_disjoint_sound; eauto.
Qed.
Lemma mod_pow2_of_mod_2_64 : forall a b k, 0 <= k <= 64 ->
a mod 2^64 = b mod 2^64 -> a mod 2^k = b mod 2^k.
Proof.
intros a b k Hk H.
rewrite <- (Z.mod_mod_divide a (2^64) (2^k)), <- (Z.mod_mod_divide b (2^64) (2^k)).
- rewrite H. reflexivity.
- exists (2^(64-k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
- exists (2^(64-k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma align_neq : forall E n f x c,
afact_ok E n f -> ((c - x) mod 2 ^ af_al2 f =? 0) = false ->
bv_eqb (sv_denot E (SOff n x)) (Z_to_bv 64 c) = false.
Proof.
intros E n f x c (Hb & Hal & Hk) Hne. apply Z.eqb_neq in Hne.
rewrite bv_eqb_unsigned, denot_SOff, unsigned_lit. apply Z.eqb_neq. intros Heq.
unfold zcanon, M64 in Heq. apply (mod_pow2_of_mod_2_64 _ _ (af_al2 f)) in Heq; [|lia].
apply Hne. rewrite <- Zminus_mod_idemp_l, <- Heq.
rewrite Zplus_mod, Hal, Z.add_0_l, Zmod_mod, Zminus_mod_idemp_l.
rewrite Z.sub_diag. apply Zmod_0_l.
Qed.
Lemma decide_eq_sound : forall E G a b r,
facts_ok E G -> decide_eq G a b = Some r ->
bv_eqb (sv_denot E a) (sv_denot E b) = r.
Proof.
intros E G a b r HG H. unfold decide_eq in H.
destruct (sv_eqb a b) eqn:Heq.
{ injection H as <-. apply bv_eqb_true_iff. apply sv_eqb_denot. exact Heq. }
assert (Hdis : ranges_disjoint (sv_range G a) (sv_range G b) = true ->
Some false = Some r -> bv_eqb (sv_denot E a) (sv_denot E b) = r).
{ intros Hd Hs. injection Hs as <-. eapply ranges_disjoint_eqb; eauto. }
destruct a as [x|n x|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ?|? ? ?|? ? ? ?];
destruct b as [y|m y|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ?|? ? ?|? ? ? ?];
try (destruct (ranges_disjoint _ _) eqn:Hd; [apply Hdis; [reflexivity|exact H] | discriminate]).
- injection H as <-. cbn [sv_denot]. rewrite bv_eqb_unsigned, !unsigned_lit. reflexivity.
- destruct (ranges_disjoint _ _) eqn:Hd; [apply Hdis; [reflexivity|exact H] |].
destruct (atom_lookup (f_atoms G) m) as [f|] eqn:Hl; [|discriminate].
destruct ((x - y) mod 2 ^ af_al2 f =? 0) eqn:Hm; cbn in H; [discriminate|].
injection H as <-. cbn [sv_denot] . rewrite bv_eqb_unsigned, Z.eqb_sym, <- bv_eqb_unsigned.
eapply align_neq; [eapply atom_lookup_ok; [apply HG|exact Hl] | exact Hm].
- destruct (ranges_disjoint _ _) eqn:Hd; [apply Hdis; [reflexivity|exact H] |].
destruct (atom_lookup (f_atoms G) n) as [f|] eqn:Hl; [|discriminate].
destruct ((y - x) mod 2 ^ af_al2 f =? 0) eqn:Hm; cbn in H; [discriminate|].
injection H as <-.
eapply align_neq; [eapply atom_lookup_ok; [apply HG|exact Hl] | exact Hm].
- destruct (Nat.eqb n m) eqn:Hnm.
+ apply Nat.eqb_eq in Hnm. subst m. injection H as <-.
destruct (zcanon x =? zcanon y) eqn:Hz.
* apply bv_eqb_true_iff. apply SOff_eq_iff. apply Z.eqb_eq. exact Hz.
* apply bv_eqb_false_iff. intros Heq'. apply SOff_eq_iff in Heq'.
apply Z.eqb_neq in Hz. exact (Hz Heq').
+ destruct (ranges_disjoint _ _) eqn:Hd; [apply Hdis; [reflexivity|exact H] | discriminate].
Qed.
Lemma bv_ltu_unsigned : forall (a b : word), bv_ltu a b = (bv_unsigned a <? bv_unsigned b).
Proof. reflexivity. Qed.
Lemma ranges_ltu_sound : forall E G a b r,
facts_ok E G -> ranges_ltu (sv_range G a) (sv_range G b) = Some r ->
bv_ltu (sv_denot E a) (sv_denot E b) = r.
Proof.
intros E G a b r HG H. unfold ranges_ltu in H.
destruct (sv_range G a) as [[alo ahi]|] eqn:Ha; [|discriminate].
destruct (sv_range G b) as [[blo bhi]|] eqn:Hb; [|discriminate].
pose proof (sv_range_sound E G a alo ahi HG Ha) as Ra.
pose proof (sv_range_sound E G b blo bhi HG Hb) as Rb.
rewrite bv_ltu_unsigned.
destruct (ahi <? blo) eqn:H1.
- injection H as <-. apply Z.ltb_lt in H1. apply Z.ltb_lt. lia.
- destruct (bhi <=? alo) eqn:H2; [|discriminate].
injection H as <-. apply Z.leb_le in H2. apply Z.ltb_ge. lia.
Qed.
Lemma SOff_nowrap : forall E G n x lo hi,
facts_ok E G -> sv_range G (SOff n x) = Some (lo, hi) ->
bv_unsigned (sv_denot E (SOff n x)) = bv_unsigned (ew E n) + x.
Proof.
intros E G n x lo hi HG Hr. cbn in Hr.
destruct (atom_lookup (f_atoms G) n) as [f|] eqn:Hl; [|discriminate].
destruct (0 <=? af_lo f + x) eqn:H1; [|discriminate].
destruct (af_hi f + x <? M64) eqn:H2; [|discriminate].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold M64 in H2.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hl) as (Hb & _ & _).
rewrite denot_SOff. apply zcanon_small. lia.
Qed.
Lemma decide_ltu_sound : forall E G a b r,
facts_ok E G -> decide_ltu G a b = Some r ->
bv_ltu (sv_denot E a) (sv_denot E b) = r.
Proof.
intros E G a b r HG H. unfold decide_ltu in H.
destruct (sv_eqb a b) eqn:Heq.
{ injection H as <-. rewrite (sv_eqb_denot E a b Heq). rewrite bv_ltu_unsigned. apply Z.ltb_irrefl. }
destruct (ranges_ltu (sv_range G a) (sv_range G b)) as [r'|] eqn:Hrl.
{ injection H as <-. eapply ranges_ltu_sound; eauto. }
destruct a as [x|n x|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ?|? ? ?|? ? ? ?]; try discriminate.
destruct b as [y|m y|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ?|? ? ?|? ? ? ?]; try discriminate.
destruct (Nat.eqb n m) eqn:Hnm; [|discriminate]. apply Nat.eqb_eq in Hnm. subst m.
destruct (sv_range G (SOff n x)) as [[alo ahi]|] eqn:Ha; [|discriminate].
destruct (sv_range G (SOff n y)) as [[blo bhi]|] eqn:Hb; [|discriminate].
injection H as <-.
rewrite bv_ltu_unsigned, (SOff_nowrap E G n x alo ahi HG Ha), (SOff_nowrap E G n y blo bhi HG Hb).
destruct (x <? y) eqn:Hxy.
- apply Z.ltb_lt in Hxy. apply Z.ltb_lt. lia.
- apply Z.ltb_ge in Hxy. apply Z.ltb_ge. lia.
Qed.
Lemma bv_lts_signed : forall (a b : word), bv_lts a b = (bv_signed a <? bv_signed b).
Proof. reflexivity. Qed.
Lemma signed_of_small : forall (a : word),
bv_unsigned a < half64 -> bv_signed a = bv_unsigned a.
Proof.
intros a H. unfold bv_signed. apply bv_swrap_small.
pose proof (u64_range a). unfold half64 in H.
change (bv_half_modulus 64) with (2^63). lia.
Qed.
Lemma decide_lts_sound : forall E G a b r,
facts_ok E G -> decide_lts G a b = Some r ->
bv_lts (sv_denot E a) (sv_denot E b) = r.
Proof.
intros E G a b r HG H. unfold decide_lts in H.
destruct (sv_eqb a b) eqn:Heq.
{ injection H as <-. rewrite (sv_eqb_denot E a b Heq). rewrite bv_lts_signed. apply Z.ltb_irrefl. }
destruct (sv_range G a) as [[alo ahi]|] eqn:Ha; [|discriminate].
destruct (sv_range G b) as [[blo bhi]|] eqn:Hb; [|discriminate].
destruct (ahi <? half64) eqn:H1; [|discriminate].
destruct (bhi <? half64) eqn:H2; [|discriminate]. cbn in H.
apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
pose proof (sv_range_sound E G a alo ahi HG Ha) as Ra.
pose proof (sv_range_sound E G b blo bhi HG Hb) as Rb.
rewrite bv_lts_signed, !signed_of_small by lia. rewrite <- bv_ltu_unsigned.
eapply decide_ltu_sound; eauto.
Qed.
Lemma decide_cond_sound : forall E G c a b r,
facts_ok E G -> decide_cond G c a b = Some r ->
branch_taken c (sv_denot E a) (sv_denot E b) = r.
Proof.
intros E G c a b r HG H. unfold decide_cond in H.
destruct (cond_assumed (f_conds G) c a b) eqn:Hc1.
{ injection H as <-. eapply cond_assumed_sound; [apply (proj1 (proj2 HG)) | exact Hc1]. }
destruct (cond_assumed (f_conds G) (neg_bc c) a b) eqn:Hc2.
{ injection H as <-.
pose proof (cond_assumed_sound E _ _ _ _ (proj1 (proj2 HG)) Hc2) as Hn.
rewrite branch_taken_neg in Hn. destruct (branch_taken c _ _); [discriminate|reflexivity]. }
destruct c; cbn [branch_taken].
- eapply decide_eq_sound; eauto.
- destruct (decide_eq G a b) as [r'|] eqn:Hd; [|discriminate]. cbn in H. injection H as <-.
f_equal. eapply decide_eq_sound; eauto.
- eapply decide_lts_sound; eauto.
- destruct (decide_lts G a b) as [r'|] eqn:Hd; [|discriminate]. cbn in H. injection H as <-.
f_equal. eapply decide_lts_sound; eauto.
- eapply decide_ltu_sound; eauto.
- destruct (decide_ltu G a b) as [r'|] eqn:Hd; [|discriminate]. cbn in H. injection H as <-.
f_equal. eapply decide_ltu_sound; eauto.
Qed.
Lemma land_low_mask : forall a m k, 0 <= k -> 0 <= m < 2 ^ k ->
Z.land a m = Z.land (a mod 2 ^ k) m.
Proof.
intros a m k Hk Hm.
rewrite <- (Z.land_ones a k) by lia.
rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) m).
rewrite (Z.land_ones m k) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma land_neg_pow2 : forall a j, 0 <= j ->
Z.land a (- 2 ^ j) = a - a mod 2 ^ j.
Proof.
intros a j Hj.
assert (H : Z.land a (- 2 ^ j) = Z.shiftl (Z.shiftr a j) j).
{ apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.shiftl_spec by lia.
replace (- 2 ^ j) with (Z.lnot (Z.ones j))
by (unfold Z.ones; rewrite Z.shiftl_1_l; unfold Z.lnot; lia).
rewrite Z.lnot_spec by lia.
destruct (Z_lt_le_dec i j).
- rewrite Z.ones_spec_low by lia. rewrite (Z.testbit_neg_r _ (i - j)) by lia.
apply andb_false_r.
- rewrite Z.ones_spec_high by lia. rewrite Z.shiftr_spec by lia.
replace (i - j + j) with i by lia. apply andb_true_r. }
rewrite H, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
pose proof (Z.div_mod a (2^j) ltac:(apply Z.pow_nonzero; lia)). lia.
Qed.
Lemma mod_add_mul_cancel : forall u x k, 0 <= k -> u mod 2 ^ k = 0 ->
(u + x) mod 2 ^ k = x mod 2 ^ k.
Proof.
intros u x k Hk Hu.
rewrite Zplus_mod, Hu, Z.add_0_l. apply Zmod_mod.
Qed.
Definition is_pow2 (z : Z) : option Z :=
if 0 <? z then let k := Z.log2 z in if 2 ^ k =? z then Some k else None else None.
Lemma is_pow2_sound : forall z k, is_pow2 z = Some k -> 0 <= k /\ z = 2 ^ k.
Proof.
intros z k H. unfold is_pow2 in H.
destruct (0 <? z) eqn:Hz; [|discriminate].
destruct (2 ^ Z.log2 z =? z) eqn:He; [|discriminate].
injection H as <-. apply Z.eqb_eq in He. split; [apply Z.log2_nonneg| lia].
Qed.
Lemma land_mod_r : forall a m, 0 <= a < 2^64 -> Z.land a (m mod 2^64) = Z.land a m.
Proof.
intros a m Ha. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z_lt_le_dec i 64).
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite (Z_testbit_high 64 a i) by lia. reflexivity.
Qed.
Definition zsigned64 (m : Z) : Z :=
let mc := zcanon m in if mc <? 2^63 then mc else mc - 2^64.
Lemma zsigned64_mod : forall m, zsigned64 m mod 2^64 = m mod 2^64.
Proof.
intros m. unfold zsigned64. pose proof (zcanon_range m).
destruct (zcanon m <? 2^63) eqn:H1.
- unfold zcanon, M64. apply Zmod_mod.
- unfold zcanon, M64 in *. rewrite <- (Z_mod_plus_full _ 1).
replace (m mod 2^64 - 2^64 + 1 * 2^64) with (m mod 2^64) by lia. apply Zmod_mod.
Qed.
Definition s_and_ptr (G : facts) (n : nat) (x : Z) (neg : bool) (m : Z) : option sv :=
match atom_lookup (f_atoms G) n with
| None => None
| Some f =>
let k := af_al2 f in
let ms := zsigned64 m in
if (0 <=? ms) && (ms <? 2 ^ k) then Some (SLit (Z.land (if neg then - x else x) ms))
else if neg then None
else match is_pow2 (- ms) with
| Some j => if j <=? k then Some (SOff n (x - x mod 2 ^ j)) else None
| None => None
end
end.
Lemma Z_to_bv64_mod : forall a, Z_to_bv 64 (a mod 2^64) = Z_to_bv 64 a.
Proof. intros a. apply (Z_to_bv64_canon a). Qed.
Lemma Z_to_bv64_eq_mod : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. rewrite <- (Z_to_bv64_mod a), <- (Z_to_bv64_mod b), H. reflexivity. Qed.
Definition owrap (z : Z) : Z := let w := zcanon z in if w <? 2^63 then w else w - M64.
Lemma owrap_mod : forall z, owrap z mod 2^64 = z mod 2^64.
Proof.
intros z. unfold owrap, zcanon, M64. pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)) as Hb.
destruct (z mod 2^64 <? 2^63) eqn:E.
- apply Z.mod_mod. lia.
- replace (z mod 2 ^ 64 - 2 ^ 64) with (z mod 2^64 + (-1) * 2^64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Lemma SOff_owrap : forall E n c, sv_denot E (SOff n (owrap c)) = sv_denot E (SOff n c).
Proof.
intros E n c. cbn [sv_denot]. apply Z_to_bv64_eq_mod.
rewrite <- Zplus_mod_idemp_r, owrap_mod, Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma denot_neg_ptr : forall E n x z, zcanon z = 0 ->
sv_denot E (SAlu ALU_SUB (SLit z) (SOff n x)) = Z_to_bv 64 (- (bv_unsigned (ew E n) + x)).
Proof.
intros E n x z Hz. cbn [sv_denot]. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw].
rewrite Hz. rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod.
unfold zcanon, M64. rewrite Z.sub_0_l.
rewrite <- (Z.sub_0_l (bv_unsigned (ew E n) + x)).
rewrite <- Zminus_mod_idemp_r. reflexivity.
Qed.
Lemma and_lit_Z : forall A m,
alu64 ALU_AND (Z_to_bv 64 A) (Z_to_bv 64 m) = Z_to_bv 64 (Z.land (zcanon A) (zsigned64 m)).
Proof.
intros A m. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw]. rewrite Z_to_bv64_canon.
f_equal. pose proof (zcanon_range A).
rewrite <- (land_mod_r (zcanon A) (zsigned64 m)) by lia. rewrite zsigned64_mod. reflexivity.
Qed.
Lemma s_and_ptr_sound : forall E G n x neg m v (a : sv),
facts_ok E G ->
s_and_ptr G n x neg m = Some v ->
sv_denot E a = Z_to_bv 64 (if neg then - (bv_unsigned (ew E n) + x) else bv_unsigned (ew E n) + x) ->
sv_denot E v = alu64 ALU_AND (sv_denot E a) (Z_to_bv 64 m).
Proof.
intros E G n x neg m v a HG H Ha. unfold s_and_ptr in H.
destruct (atom_lookup (f_atoms G) n) as [f|] eqn:Hl; [|discriminate].
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hl) as (Hb & Hal & Hk).
rewrite Ha, and_lit_Z.
set (u := bv_unsigned (ew E n)) in *. set (ms := zsigned64 m) in *.
destruct ((0 <=? ms) && (ms <? 2 ^ af_al2 f)) eqn:H1.
- injection H as <-. cbn [sv_denot]. apply andb_prop in H1 as [H0 H1].
apply Z.leb_le in H0. apply Z.ltb_lt in H1. f_equal.
rewrite (land_low_mask (zcanon _) ms (af_al2 f)) by lia.
rewrite (land_low_mask (if neg then - x else x) ms (af_al2 f)) by lia.
f_equal. unfold zcanon, M64.
rewrite Z.mod_mod_divide by (exists (2^(64 - af_al2 f)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
destruct neg.
+ replace (- (u + x)) with (- u + - x) by lia. symmetry. apply mod_add_mul_cancel; [lia|].
apply Z_mod_zero_opp_full. exact Hal.
+ symmetry. apply mod_add_mul_cancel; [lia| exact Hal].
- destruct neg; [discriminate|].
destruct (is_pow2 (- ms)) as [j|] eqn:Hp; [|discriminate].
apply is_pow2_sound in Hp as [Hj Hmj].
destruct (j <=? af_al2 f) eqn:Hjk; [|discriminate]. apply Z.leb_le in Hjk.
injection H as <-. cbn [sv_denot]. fold u.
replace ms with (- 2 ^ j) by lia. rewrite land_neg_pow2 by lia.
apply Z_to_bv64_eq_mod.
unfold zcanon, M64.
rewrite Z.mod_mod_divide by (exists (2^(64 - j)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
assert (Huj : u mod 2 ^ j = 0).
{ rewrite <- (Z.mod_mod_divide u (2^af_al2 f) (2^j))
by (exists (2^(af_al2 f - j)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Hal. reflexivity. }
rewrite (mod_add_mul_cancel u x j Hj Huj).
rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Definition s_lit01 (b : bool) : sv := SLit (if b then 1 else 0).
Definition s_alu (G : facts) (op : aluop) (a b : sv) : sv :=
match a, b with
| SLit x, SLit y => SLit (zalu64 op x y)
| _, _ =>
match op with
| ALU_ADD =>
match a, b with
| SOff n x, SLit y => SOff n (owrap (x + y))
| SLit y, SOff n x => SOff n (owrap (x + y))
| _, _ => SAlu op a b
end
| ALU_SUB =>
match a, b with
| SOff n x, SLit y => SOff n (owrap (x - y))
| SOff n x, SOff m y => if Nat.eqb n m then SLit (zcanon (x - y)) else SAlu op a b
| _, _ => SAlu op a b
end
| ALU_AND =>
match a, b with
| SOff n x, SLit m =>
match s_and_ptr G n x false m with Some v => v | None => SAlu op a b end
| SAlu ALU_SUB (SLit z) (SOff n x), SLit m =>
if zcanon z =? 0 then
match s_and_ptr G n x true m with Some v => v | None => SAlu op a b end
else SAlu op a b
| _, _ => SAlu op a b
end
| ALU_SLTU => match decide_ltu G a b with Some r => s_lit01 r | None => SAlu op a b end
| ALU_SLT => match decide_lts G a b with Some r => s_lit01 r | None => SAlu op a b end
| _ => SAlu op a b
end
end.
Definition s_alu' (G : facts) (op : aluop) (a b : sv) : sv := aliased G (s_alu G op a b).
Lemma SOff_add_lit : forall E n x y,
sv_denot E (SOff n (owrap (x + y))) = alu64 ALU_ADD (sv_denot E (SOff n x)) (Z_to_bv 64 y).
Proof.
intros. rewrite SOff_owrap. cbn [sv_denot]. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw].
rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64.
rewrite <- Zplus_mod. f_equal. lia.
Qed.
Lemma SOff_add_lit_l : forall E n x y,
sv_denot E (SOff n (owrap (x + y))) = alu64 ALU_ADD (Z_to_bv 64 y) (sv_denot E (SOff n x)).
Proof.
intros. rewrite SOff_owrap. cbn [sv_denot]. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw].
rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64.
rewrite <- Zplus_mod. f_equal. lia.
Qed.
Lemma SOff_sub_lit : forall E n x y,
sv_denot E (SOff n (owrap (x - y))) = alu64 ALU_SUB (sv_denot E (SOff n x)) (Z_to_bv 64 y).
Proof.
intros. rewrite SOff_owrap. cbn [sv_denot]. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw].
rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64.
rewrite <- Zminus_mod. f_equal. lia.
Qed.
Lemma SOff_sub_SOff : forall E n x y,
sv_denot E (SLit (zcanon (x - y))) = alu64 ALU_SUB (sv_denot E (SOff n x)) (sv_denot E (SOff n y)).
Proof.
intros. cbn [sv_denot]. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw].
rewrite !Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64.
rewrite <- Zminus_mod. f_equal. lia.
Qed.
Lemma s_lit01_ltu : forall E a b,
sv_denot E (s_lit01 (bv_ltu a b)) = alu64 ALU_SLTU a b.
Proof. intros. cbn [alu64 alu]. destruct (bv_ltu a b); reflexivity. Qed.
Lemma s_lit01_lts : forall E a b,
sv_denot E (s_lit01 (bv_lts a b)) = alu64 ALU_SLT a b.
Proof. intros. cbn [alu64 alu]. destruct (bv_lts a b); reflexivity. Qed.
Lemma s_alu_sound : forall E G op a b,
facts_ok E G ->
sv_denot E (s_alu G op a b) = alu64 op (sv_denot E a) (sv_denot E b).
Proof.
intros E G op a b HG.
assert (Hlit : forall x y, sv_denot E (SLit (zalu64 op x y)) = alu64 op (sv_denot E (SLit x)) (sv_denot E (SLit y))).
{ intros. cbn [sv_denot]. symmetry. apply zalu64_sound. }
unfold s_alu.
destruct a as [x|n x|aop a1 a2|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ?|? ? ?|? ? ? ?];
destruct b as [y|m y|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ?|? ? ?|? ? ? ?];
try apply Hlit;
destruct op; try reflexivity;
try (match goal with
| |- context [decide_ltu G ?a ?b] =>
destruct (decide_ltu G a b) as [r|] eqn:Hd; [|reflexivity];
rewrite <- (decide_ltu_sound E G a b r HG Hd); apply s_lit01_ltu
| |- context [decide_lts G ?a ?b] =>
destruct (decide_lts G a b) as [r|] eqn:Hd; [|reflexivity];
rewrite <- (decide_lts_sound E G a b r HG Hd); apply s_lit01_lts
end).
all: try apply SOff_add_lit_l; try apply SOff_add_lit; try apply SOff_sub_lit.
all: try match goal with
| HG : facts_ok _ ?G' |- context [s_and_ptr ?G' ?n ?x false ?y] =>
destruct (s_and_ptr G' n x false y) as [v|] eqn:Hs; [|reflexivity];
eapply s_and_ptr_sound; [exact HG | exact Hs | reflexivity]
| |- context [Nat.eqb ?n ?m] =>
destruct (Nat.eqb n m) eqn:Hnm; [|reflexivity]; apply Nat.eqb_eq in Hnm; subst m;
apply SOff_sub_SOff
end.
all: destruct aop; try reflexivity;
destruct a1 as [z| | | | | | | | | | ]; try reflexivity;
destruct a2 as [ |n' x'| | | | | | | | | ]; try reflexivity.
destruct (zcanon z =? 0) eqn:Hz; [|reflexivity]. apply Z.eqb_eq in Hz.
destruct (s_and_ptr G n' x' true y) as [v|] eqn:Hs; [|reflexivity].
eapply s_and_ptr_sound; [exact HG | exact Hs |]. apply denot_neg_ptr. exact Hz.
Qed.
Lemma s_alu'_sound : forall E G op a b,
facts_ok E G ->
sv_denot E (s_alu' G op a b) = alu64 op (sv_denot E a) (sv_denot E b).
Proof. intros. unfold s_alu'. rewrite aliased_sound by assumption. apply s_alu_sound. assumption. Qed.
Definition s_aluw (op : aluop) (a b : sv) : sv :=
match a, b with
| SLit x, SLit y => SLit (zalu32 op x y)
| _, _ => SAluw op a b
end.
Lemma s_aluw_sound : forall E op a b,
sv_denot E (s_aluw op a b) = sext 64 (alu32 op (low32 (sv_denot E a)) (low32 (sv_denot E b))).
Proof.
intros E op a b. destruct a; destruct b; try reflexivity.
cbn [s_aluw sv_denot]. symmetry. apply zalu32_sound.
Qed.
Definition s_md (op : mulop) (a b : sv) : sv :=
match a, b with
| SLit x, SLit y => SLit (zmd64 op x y)
| _, _ => SMd op a b
end.
Lemma s_md_sound : forall E op a b,
sv_denot E (s_md op a b) = mul_div op (sv_denot E a) (sv_denot E b).
Proof.
intros E op a b. destruct a; destruct b; try reflexivity.
cbn [s_md sv_denot]. symmetry. apply zmd64_sound.
Qed.
Definition s_mdw (op : mulop) (a b : sv) : sv :=
match a, b with
| SLit x, SLit y => SLit (zmd32 op x y)
| _, _ => SMdw op a b
end.
Lemma s_mdw_sound : forall E op a b,
sv_denot E (s_mdw op a b) = sext 64 (mul_div op (low32 (sv_denot E a)) (low32 (sv_denot E b))).
Proof.
intros E op a b. destruct a; destruct b; try reflexivity.
cbn [s_mdw sv_denot]. symmetry. apply zmd32_sound.
Qed.
Definition s_ext (sg : bool) (w : N) (a : sv) : sv :=
match a with
| SLit x => SLit (zext_low sg w x)
| _ => SExt sg w a
end.
Lemma s_ext_sound : forall E (sg : bool) (w : N) a,
sv_denot E (s_ext sg w a) =
(if sg then sext 64 (bv_extract 0 w (sv_denot E a)) else zext 64 (bv_extract 0 w (sv_denot E a))).
Proof.
intros E sg w a. destruct a; try (cbn [s_ext sv_denot]; destruct sg; reflexivity).
cbn [s_ext sv_denot]. symmetry. apply zext_low_sound.
Qed.
Definition sv_lit (v : sv) : option Z :=
match v with SLit z => Some (zcanon z) | _ => None end.
Lemma sv_lit_sound : forall E v z, sv_lit v = Some z -> sv_denot E v = Z_to_bv 64 z /\ 0 <= z < 2^64.
Proof.
intros E v z H. destruct v; cbn in H; try discriminate. injection H as <-.
split; [cbn; symmetry; apply Z_to_bv64_canon | apply zcanon_range].
Qed.
