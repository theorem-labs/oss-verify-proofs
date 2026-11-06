(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module U32.

Definition w32 : w64 := wlit 32%uint63.
Definition core32 (v : sv) : sv :=
  match v with
  | VExt false lo n x => if PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb n 4%uint63 then x else v
  | VAlu ALU_SRL (VAlu ALU_SLL x (VL s1)) (VL s2) => if weqb s1 w32 && weqb s2 w32 then x else v
  | _ => v
  end.

Fixpoint strip32 (v : sv) : sv :=
  match v with
  | VExt _ lo n x => if PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb n 4%uint63 then strip32 x else v
  | VAlu ALU_SRL (VAlu ALU_SLL x (VL s1)) (VL s2) => if weqb s1 w32 && weqb s2 w32 then strip32 x else v
  | VAlu ALU_ADD a b => VAlu ALU_ADD (strip32 a) (strip32 b)
  | VAlu ALU_SUB a b => VAlu ALU_SUB (strip32 a) (strip32 b)
  | VAluw ALU_ADD a b => VAlu ALU_ADD (strip32 a) (strip32 b)
  | VAluw ALU_SUB a b => VAlu ALU_SUB (strip32 a) (strip32 b)
  | _ => v
  end.

Definition same32 (a b : sv) : bool := sv_eqb (core32 a) (core32 b) || msame (strip32 a) (strip32 b).

Definition zx_forms (v : sv) : list sv :=
  [VAlu ALU_SRL (VAlu ALU_SLL v (VL w32)) (VL w32); sv_alu ALU_SRL (sv_alu ALU_SLL v (VL w32)) (VL w32); VExt false 0%uint63 4%uint63 v].
Definition is_zx_of (v c : sv) : bool := existsb (sv_eqb c) (zx_forms v).

Definition below (v : sv) (k : Z) : bool :=
  match sv_umax v with Some m => Z.ltb (w2Z m) (2 ^ k) | None => false end.
Fixpoint sx32_shaped (v : sv) : bool :=
  below v 31 || match v with
                | VAluw _ _ _ => true
                | VAlu ALU_SLL a (VL s) => Z.leb (w2Z s) 31 && below a (31 - w2Z s)
                | VAlu ALU_OR a b | VAlu ALU_AND a b | VAlu ALU_XOR a b => sx32_shaped a && sx32_shaped b
                | _ => false
                end.

Definition nz_known (fs : list fact) (c : sv) : bool :=
  match decide_eq0 fs c with
  | Some false => true
  | _ => let x := core32 c in negb (sv_eqb x c) && sx32_shaped x && match decide_eq0 fs x with Some false => true | _ => false end
  end.

Definition bounded_count (fs : list fact) (c : sv) : bool :=
  match decide_ltu fs c (VL (wlit 1001%uint63)) with Some true => nz_known fs c | _ => false end.

Lemma wrap64 : forall x, bv_wrap 64 x = x mod two64.
Proof. intros x. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. Qed.

Lemma shamt_w32 : to_Z (shamt6 w32) = 32.
Proof. reflexivity. Qed.

Lemma zx_shift_den : forall E x,
  bv_unsigned (den E (VAlu ALU_SRL (VAlu ALU_SLL x (VL w32)) (VL w32))) = bv_unsigned (den E x) mod 2 ^ 32.
Proof.
  intros E x. cbn [den alu64 alu]. rewrite bv_shiftr_unsigned, bv_shiftl_unsigned, !shamt6_bv, !shamt_w32.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2, wrap64 by lia.
  pose proof (bv_unsigned_in_range _ (den E x)) as R. rewrite bv_modulus_64 in R.
  set (u := bv_unsigned (den E x)) in *. unfold two64 in *.
  replace 18446744073709551616 with (2 ^ 32 * 2 ^ 32) by reflexivity. rewrite Zmult_mod_distr_r.
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma zx_ext_den : forall E x, bv_unsigned (den E (VExt false 0%uint63 4%uint63 x)) = bv_unsigned (den E x) mod 2 ^ 32.
Proof.
  intros E x. cbn [den]. unfold ext_word. rewrite Z_to_bv_unsigned. change (to_Z 0%uint63) with 0. change (to_Z 4%uint63) with 4.
  pose proof (ext_Z_false_lt 0 4 (bv_unsigned (den E x)) ltac:(lia)) as R.
  rewrite wrap64, Z.mod_small by (unfold two64; change (2 ^ (8 * 4)) with 4294967296 in R; lia).
  unfold ext_Z. cbn [Z.mul]. rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
Qed.

Lemma sx_ext_den32 : forall E x, bv_unsigned (den E (VExt true 0%uint63 4%uint63 x)) mod 2 ^ 32 = bv_unsigned (den E x) mod 2 ^ 32.
Proof.
  intros E x. cbn [den]. unfold ext_word. rewrite Z_to_bv_unsigned. change (to_Z 0%uint63) with 0. change (to_Z 4%uint63) with 4.
  pose proof (ext_Z_range true 0 4 (bv_unsigned (den E x)) ltac:(lia) ltac:(lia) ltac:(lia)) as R.
  rewrite wrap64, (Z.mod_small _ two64) by exact R.
  unfold ext_Z. replace (2 ^ (8 * 0)) with 1 by reflexivity. rewrite Z.div_1_r.
  replace (2 ^ (8 * 4)) with (2 ^ 32) by reflexivity. replace (2 ^ (8 * 4 - 1)) with (2 ^ 31) by reflexivity.
  pose proof (Z.mod_pos_bound (bv_unsigned (den E x)) (2 ^ 32) ltac:(lia)) as U.
  set (u := bv_unsigned (den E x) mod 2 ^ 32) in *.
  destruct (Z.leb (2 ^ 31) u) eqn:L.
  - unfold two64. rewrite <- (Z.mod_unique_pos (u - 2 ^ 32) 18446744073709551616 (-1) (u + (18446744073709551616 - 2 ^ 32))) by lia.
    replace (u + (18446744073709551616 - 2 ^ 32)) with (u + 4294967295 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. subst u. apply Z.mod_mod. lia.
  - unfold two64. rewrite (Z.mod_small u) by lia. subst u. apply Z.mod_mod. lia.
Qed.

Lemma core32_den : forall E v, bv_unsigned (den E (core32 v)) mod 2 ^ 32 = bv_unsigned (den E v) mod 2 ^ 32.
Proof.
  intros E v. unfold core32.
  destruct v as [| | op a b | | | | sx lo n x | | | |]; try reflexivity.
  - destruct op; try reflexivity. destruct a as [| | op2 x s1v | | | | | | | |]; try reflexivity. destruct op2; try reflexivity.
    destruct s1v as [s1| | | | | | | | | |]; try reflexivity. destruct b as [s2| | | | | | | | | |]; try reflexivity.
    destruct (weqb s1 w32 && weqb s2 w32) eqn:Q; [|reflexivity]. apply andb_prop in Q as [Q1 Q2].
    apply (proj1 (weqb_ok _ _)) in Q1. apply (proj1 (weqb_ok _ _)) in Q2. subst s1 s2.
    rewrite zx_shift_den. symmetry. apply Z.mod_mod. lia.
  - destruct sx; [reflexivity|]. destruct (PrimInt63.eqb lo 0 && PrimInt63.eqb n 4) eqn:Q; [|reflexivity].
    apply andb_prop in Q as [Q1 Q2]. apply Uint63.eqb_correct in Q1. apply Uint63.eqb_correct in Q2. subst lo n.
    rewrite zx_ext_den. symmetry. apply Z.mod_mod. lia.
Qed.

Section Strip32.
Variable E : env.
Lemma mod64_mod32 : forall z, (z mod two64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. unfold two64. rewrite (Z.mod_eq z 18446744073709551616) by lia.
  replace (z - 18446744073709551616 * (z / 18446744073709551616)) with (z + (- (4294967296 * (z / 18446744073709551616))) * 2 ^ 32) by lia.
  apply Z_mod_plus_full.
Qed.

Lemma sx32Z_mod32 : forall u, 0 <= u < 2 ^ 32 -> sx32Z u mod 2 ^ 32 = u.
Proof.
  intros u Hu. unfold sx32Z. destruct (Z.leb_spec (2 ^ 31) u).
  - rewrite <- (Z.mod_unique_pos (u - 2 ^ 32) (2 ^ 64) (-1) (u + (2 ^ 64 - 2 ^ 32))) by lia.
    replace (u + (2 ^ 64 - 2 ^ 32)) with (u + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma low32_val : forall w : word, bv_unsigned (low32 w) = bv_unsigned w mod 2 ^ 32.
Proof.
  intros w. unfold low32. rewrite bv_extract_unsigned. rewrite Z.shiftr_0_r. unfold bv_wrap. reflexivity.
Qed.

Lemma den_add_mod32 : forall a b, bv_unsigned (den E (VAlu ALU_ADD a b)) mod 2 ^ 32 = (bv_unsigned (den E a) + bv_unsigned (den E b)) mod 2 ^ 32.
Proof.
  intros a b. change (den E (VAlu ALU_ADD a b)) with (alu64 ALU_ADD (den E a) (den E b)). cbn [alu64 alu].
  rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64. apply mod64_mod32.
Qed.
Lemma den_sub_mod32 : forall a b, bv_unsigned (den E (VAlu ALU_SUB a b)) mod 2 ^ 32 = (bv_unsigned (den E a) - bv_unsigned (den E b)) mod 2 ^ 32.
Proof.
  intros a b. change (den E (VAlu ALU_SUB a b)) with (alu64 ALU_SUB (den E a) (den E b)). cbn [alu64 alu].
  rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64. apply mod64_mod32.
Qed.
Lemma den_addw_mod32 : forall a b, bv_unsigned (den E (VAluw ALU_ADD a b)) mod 2 ^ 32 = (bv_unsigned (den E a) + bv_unsigned (den E b)) mod 2 ^ 32.
Proof.
  intros a b. cbn [den]. rewrite sext32_unsigned. unfold alu32, alu. rewrite sx32Z_mod32.
  2: { pose proof (bv_unsigned_in_range 32 (low32 (den E a) + low32 (den E b))%bv) as R. change (bv_modulus 32) with (2 ^ 32) in R. exact R. }
  rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite !low32_val.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Lemma den_subw_mod32 : forall a b, bv_unsigned (den E (VAluw ALU_SUB a b)) mod 2 ^ 32 = (bv_unsigned (den E a) - bv_unsigned (den E b)) mod 2 ^ 32.
Proof.
  intros a b. cbn [den]. rewrite sext32_unsigned. unfold alu32, alu. rewrite sx32Z_mod32.
  2: { pose proof (bv_unsigned_in_range 32 (low32 (den E a) - low32 (den E b))%bv) as R. change (bv_modulus 32) with (2 ^ 32) in R. exact R. }
  rewrite bv_sub_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite !low32_val.
  rewrite <- Zminus_mod by lia. reflexivity.
Qed.

Definition S32 (v : sv) : Prop := bv_unsigned (den E (strip32 v)) mod 2 ^ 32 = bv_unsigned (den E v) mod 2 ^ 32.

Lemma add_mod32_congr : forall a b a' b', a mod 2 ^ 32 = a' mod 2 ^ 32 -> b mod 2 ^ 32 = b' mod 2 ^ 32 -> (a + b) mod 2 ^ 32 = (a' + b') mod 2 ^ 32.
Proof. intros a b a' b' Ha Hb. rewrite <- Z.add_mod_idemp_l, Ha, <- Z.add_mod_idemp_r, Hb, Z.add_mod_idemp_r, Z.add_mod_idemp_l by lia. reflexivity. Qed.
Lemma sub_mod32_congr : forall a b a' b', a mod 2 ^ 32 = a' mod 2 ^ 32 -> b mod 2 ^ 32 = b' mod 2 ^ 32 -> (a - b) mod 2 ^ 32 = (a' - b') mod 2 ^ 32.
Proof. intros a b a' b' Ha Hb. rewrite <- Zminus_mod_idemp_l, Ha, <- Zminus_mod_idemp_r, Hb, Zminus_mod_idemp_r, Zminus_mod_idemp_l. reflexivity. Qed.

Lemma strip32_mod32_aux : forall v, S32 v /\ (forall x y, v = VAlu ALU_SLL x y -> S32 x).
Proof.
  induction v as [w|k o|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|lo n a IHa u IHu|sx j o IHo n|sx k o n|op a IHa];
    (split; [| intros x y Hxy; try discriminate Hxy]); unfold S32; cbn [strip32]; fold strip32; try reflexivity.
  -   destruct op; try reflexivity.
    + rewrite !den_add_mod32. apply add_mod32_congr; [exact (proj1 IHa)| exact (proj1 IHb)].
    + rewrite !den_sub_mod32. apply sub_mod32_congr; [exact (proj1 IHa)| exact (proj1 IHb)].
    +   destruct a as [| |opa x y| | | | | | | |]; try reflexivity. destruct opa; try reflexivity.
      destruct y as [s1| | | | | | | | | |]; try reflexivity. destruct b as [s2| | | | | | | | | |]; try reflexivity.
      destruct (weqb s1 w32 && weqb s2 w32) eqn:Q; [|reflexivity].
      apply andb_prop in Q as [Q1 Q2]. apply (proj1 (weqb_ok _ _)) in Q1. apply (proj1 (weqb_ok _ _)) in Q2. subst s1 s2.
      rewrite zx_shift_den, Z.mod_mod by lia. exact (proj2 IHa x (VL w32) eq_refl).
  -   injection Hxy as E1 E2 E3. subst x y. exact (proj1 IHa).
  -   destruct op; try reflexivity.
    + rewrite den_add_mod32, den_addw_mod32. apply add_mod32_congr; [exact (proj1 IHa)| exact (proj1 IHb)].
    + rewrite den_sub_mod32, den_subw_mod32. apply sub_mod32_congr; [exact (proj1 IHa)| exact (proj1 IHb)].
  -   destruct (PrimInt63.eqb lo 0 && PrimInt63.eqb n 4) eqn:Q; [|reflexivity].
    apply andb_prop in Q as [Q1 Q2]. apply Uint63.eqb_correct in Q1. apply Uint63.eqb_correct in Q2. subst lo n.
    rewrite (proj1 IHa). destruct sx; [rewrite sx_ext_den32; reflexivity|]. rewrite zx_ext_den, Z.mod_mod by lia. reflexivity.
Qed.

Lemma strip32_mod32 : forall v, bv_unsigned (den E (strip32 v)) mod 2 ^ 32 = bv_unsigned (den E v) mod 2 ^ 32.
Proof. intros v. exact (proj1 (strip32_mod32_aux v)). Qed.
End Strip32.

Lemma same32_sound : forall E a b, same32 a b = true -> bv_unsigned (den E a) mod 2 ^ 32 = bv_unsigned (den E b) mod 2 ^ 32.
Proof.
  intros E a b H. unfold same32 in H. apply orb_prop in H as [H|H].
  - apply sv_eqb_eq in H. rewrite <- (core32_den E a), <- (core32_den E b), H. reflexivity.
  - rewrite <- (strip32_mod32 E a), <- (strip32_mod32 E b), (msame_sound E _ _ H). reflexivity.
Qed.

Lemma zx_forms_den : forall E v c, In c (zx_forms v) -> bv_unsigned (den E c) = bv_unsigned (den E v) mod 2 ^ 32.
Proof.
  intros E v c H. unfold zx_forms in H. destruct H as [<-|[<-|[<-|[]]]].
  - apply zx_shift_den.
  - rewrite !den_sv_alu. rewrite <- (zx_shift_den E v). reflexivity.
  - apply zx_ext_den.
Qed.

Definition sxP (x : Z) : Prop := forall n, 32 <= n < 64 -> Z.testbit x n = Z.testbit x 31.

Lemma below_sound : forall E v k, below v k = true -> 0 <= bv_unsigned (den E v) < 2 ^ k.
Proof.
  intros E v k H. unfold below in H. destruct (sv_umax v) as [m|] eqn:U; [|discriminate]. apply Z.ltb_lt in H.
  pose proof (sv_umax_sound_gen E v m U). pose proof (bv_unsigned_in_range _ (den E v)). lia.
Qed.

Lemma sxP_small : forall x, 0 <= x < 2 ^ 31 -> sxP x.
Proof.
  intros x Hx n Hn. destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite !Z.testbit_0_l; reflexivity|].
  assert (L : Z.log2 x < 31) by (apply Z.log2_lt_pow2; lia).
  rewrite !Z.bits_above_log2 by lia. reflexivity.
Qed.

Lemma sxP_lor : forall a b, sxP a -> sxP b -> sxP (Z.lor a b).
Proof. intros a b Ha Hb n Hn. rewrite !Z.lor_spec, (Ha n Hn), (Hb n Hn). reflexivity. Qed.
Lemma sxP_land : forall a b, sxP a -> sxP b -> sxP (Z.land a b).
Proof. intros a b Ha Hb n Hn. rewrite !Z.land_spec, (Ha n Hn), (Hb n Hn). reflexivity. Qed.
Lemma sxP_lxor : forall a b, sxP a -> sxP b -> sxP (Z.lxor a b).
Proof. intros a b Ha Hb n Hn. rewrite !Z.lxor_spec, (Ha n Hn), (Hb n Hn). reflexivity. Qed.

Definition HI32 : Z := Z.ones 32 * 2 ^ 32.
Lemma HI32_val : HI32 = 2 ^ 64 - 2 ^ 32.
Proof. reflexivity. Qed.
Lemma HI32_bits : forall n, Z.testbit HI32 n = (32 <=? n) && (n <? 64).
Proof.
  intros n. unfold HI32. rewrite Z.mul_pow2_bits, Z.testbit_ones by lia.
  destruct (Z.leb_spec 32 n), (Z.ltb_spec n 64), (Z.leb_spec 0 (n - 32)), (Z.ltb_spec (n - 32) 32); cbn; lia || reflexivity.
Qed.

Lemma sxP_sx32Z : forall u, 0 <= u < 2 ^ 32 -> sxP (sx32Z u).
Proof.
  intros u Hu. unfold sx32Z. destruct (Z.leb_spec (2 ^ 31) u) as [GE|LT]; [| apply sxP_small; lia].
  assert (E : (u - 2 ^ 32) mod 2 ^ 64 = u + HI32).
  { rewrite HI32_val. rewrite <- (Z.mod_unique_pos (u - 2 ^ 32) (2 ^ 64) (-1) (u + (2 ^ 64 - 2 ^ 32))); lia. }
  rewrite E.
  assert (UB : forall n, 32 <= n -> Z.testbit u n = false).
  { intros n Hn. destruct (Z.eq_dec u 0) as [->|NZ]; [apply Z.testbit_0_l|]. apply Z.bits_above_log2; [lia|].
    pose proof (proj1 (Z.log2_lt_pow2 u 32 ltac:(lia)) ltac:(lia)). lia. }
  assert (NC : Z.land u HI32 = 0).
  { apply Z.bits_inj_0. intros n. rewrite Z.land_spec, HI32_bits.
    destruct (Z.lt_ge_cases n 0); [rewrite Z.testbit_neg_r by lia; reflexivity|].
    destruct (Z.lt_ge_cases n 32).
    - destruct (Z.leb_spec 32 n); [lia|]. cbn. apply andb_false_r.
    - rewrite UB by lia. reflexivity. }
  rewrite (Z.add_nocarry_lxor _ _ NC).
  assert (B31 : Z.testbit u 31 = true).
  { apply Z.testbit_true; [lia|]. replace (u / 2 ^ 31) with 1; [reflexivity|].
    apply (Z.div_unique_pos u (2 ^ 31) 1 (u - 2 ^ 31)); lia. }
  intros n Hn. rewrite !Z.lxor_spec, !HI32_bits, UB, B31 by lia.
  destruct (Z.leb_spec 32 n), (Z.ltb_spec n 64), (Z.leb_spec 32 31), (Z.ltb_spec 31 64); cbn; lia || reflexivity.
Qed.

Lemma sxP_nz : forall x, 0 <= x < 2 ^ 64 -> sxP x -> x mod 2 ^ 32 = 0 -> x = 0.
Proof.
  intros x Hx SX M. apply Z.bits_inj_0. intros n.
  assert (LOW : forall m, m < 32 -> Z.testbit x m = false).
  { intros m Hm. rewrite <- (Z.mod_pow2_bits_low x 32 m Hm), M. apply Z.testbit_0_l. }
  destruct (Z.lt_ge_cases n 32); [apply LOW; lia|].
  destruct (Z.lt_ge_cases n 64); [rewrite (SX n ltac:(lia)); apply LOW; lia|].
  destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|]. pose proof (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia)) ltac:(lia)). lia.
Qed.

Lemma sxP_low31 : forall x, 0 <= x < 2 ^ 64 -> sxP x -> x mod 2 ^ 32 < 2 ^ 31 -> x = x mod 2 ^ 32.
Proof.
  intros x Hx SX L.
  pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)) as M.
  assert (B31 : Z.testbit x 31 = false).
  { rewrite <- (Z.mod_pow2_bits_low x 32 31) by lia.
    destruct (Z.eq_dec (x mod 2 ^ 32) 0) as [->|NZ]; [apply Z.testbit_0_l|].
    apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia. }
  assert (HI : x / 2 ^ 32 = 0).
  { apply Z.bits_inj_0. intros n.
    destruct (Z.lt_ge_cases n 0); [apply Z.testbit_neg_r; lia|].
    rewrite Z.div_pow2_bits by lia.
    destruct (Z.lt_ge_cases (n + 32) 64).
    - rewrite (SX (n + 32)) by lia. exact B31.
    - destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.testbit_0_l|]. apply Z.bits_above_log2; [lia|].
      pose proof (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia)) ltac:(lia)). lia. }
  pose proof (Z.div_mod x (2 ^ 32) ltac:(lia)) as E. rewrite HI in E. lia.
Qed.

Lemma sx32_shaped_sound : forall E v, sx32_shaped v = true -> sxP (bv_unsigned (den E v)).
Proof.
  intros E v. induction v as [w|k o|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|lo n a IHa v IHv|sx j o IHo n|sx k o n|op a IHa];
    intros H; cbn [sx32_shaped] in H; fold sx32_shaped in H;
    (destruct (below _ 31) eqn:BL; [apply sxP_small; exact (below_sound E _ 31 BL)| cbn [orb] in H]); try discriminate H.
  -
    destruct op; try discriminate H.
    +   destruct b as [s| | | | | | | | | |]; try discriminate H. apply andb_prop in H as [S31 BA].
      apply Z.leb_le in S31. pose proof (below_sound E a _ BA) as RA. pose proof (w2Z_range s) as RS.
      cbn [den alu64 alu]. rewrite bv_shiftl_unsigned, shamt6_bv, Z.shiftl_mul_pow2, wrap64 by apply int_range.
      assert (SH : to_Z (shamt6 s) = w2Z s).
      { rewrite shamt6_ok. replace 63 with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      rewrite SH. apply sxP_small.
      assert (P : 0 < 2 ^ w2Z s) by (apply Z.pow_pos_nonneg; lia).
      assert (M : bv_unsigned (den E a) * 2 ^ w2Z s < 2 ^ 31).
      { apply (Z.lt_le_trans _ (2 ^ (31 - w2Z s) * 2 ^ w2Z s)); [nia|]. rewrite <- Z.pow_add_r by lia. replace (31 - w2Z s + w2Z s) with 31 by lia. lia. }
      rewrite Z.mod_small by (unfold two64; nia). nia.
    +   apply andb_prop in H as [H1 H2]. cbn [den alu64 alu]. rewrite bv_xor_unsigned. apply sxP_lxor; auto.
    +   apply andb_prop in H as [H1 H2]. cbn [den alu64 alu]. rewrite bv_or_unsigned. apply sxP_lor; auto.
    +   apply andb_prop in H as [H1 H2]. cbn [den alu64 alu]. rewrite bv_and_unsigned. apply sxP_land; auto.
  -   cbn [den]. rewrite sext32_unsigned. apply sxP_sx32Z.
    pose proof (bv_unsigned_in_range 32 (alu32 op (low32 (den E a)) (low32 (den E b)))) as R. change (bv_modulus 32) with (2 ^ 32) in R. exact R.
Qed.

Lemma core32_unwrap_den : forall E c, core32 c <> c -> bv_unsigned (den E c) = bv_unsigned (den E (core32 c)) mod 2 ^ 32.
Proof.
  intros E c N. unfold core32 in *.
  destruct c as [| | op a b | | | | sx lo n x | | | |]; try (exfalso; exact (N eq_refl)).
  - destruct op; try (exfalso; exact (N eq_refl)). destruct a as [| | op2 x s1v | | | | | | | |]; try (exfalso; exact (N eq_refl)).
    destruct op2; try (exfalso; exact (N eq_refl)).
    destruct s1v as [s1| | | | | | | | | |]; try (exfalso; exact (N eq_refl)). destruct b as [s2| | | | | | | | | |]; try (exfalso; exact (N eq_refl)).
    destruct (weqb s1 w32 && weqb s2 w32) eqn:Q; [| exfalso; exact (N eq_refl)]. apply andb_prop in Q as [Q1 Q2].
    apply (proj1 (weqb_ok _ _)) in Q1. apply (proj1 (weqb_ok _ _)) in Q2. subst s1 s2. apply zx_shift_den.
  - destruct sx; [exfalso; exact (N eq_refl)|]. destruct (PrimInt63.eqb lo 0 && PrimInt63.eqb n 4) eqn:Q; [| exfalso; exact (N eq_refl)].
    apply andb_prop in Q as [Q1 Q2]. apply Uint63.eqb_correct in Q1. apply Uint63.eqb_correct in Q2. subst lo n. apply zx_ext_den.
Qed.

Lemma nz_known_sound : forall E fs c, facts_hold E fs -> nz_known fs c = true -> bv_unsigned (den E c) <> 0.
Proof.
  intros E fs c FH H. unfold nz_known in H.
  assert (DZ : forall v, decide_eq0 fs v = Some false -> bv_unsigned (den E v) <> 0).
  { intros v D X. pose proof (decide_eq0_sound E fs FH _ _ D) as Q. apply (proj1 (eqb_iff _ _ false)) in Q.
    apply Q. apply bv_eq. rewrite X, Z_to_bv_unsigned. reflexivity. }
  destruct (decide_eq0 fs c) as [[|]|] eqn:D2; [| exact (DZ c D2)|];
    cbv zeta in H; apply andb_prop in H as [H D3]; apply andb_prop in H as [NE SX]; apply negb_true_iff in NE;
    (destruct (decide_eq0 fs (core32 c)) as [[|]|] eqn:D4; try discriminate D3);
    (assert (N : core32 c <> c) by (intros X; rewrite X, sv_eqb_refl in NE; discriminate NE));
    rewrite (core32_unwrap_den E c N); intros M;
    pose proof (bv_unsigned_in_range _ (den E (core32 c))) as R; rewrite bv_modulus_64, two64_eq in R;
    exact (DZ _ D4 (sxP_nz _ R (sx32_shaped_sound E _ SX) M)).
Qed.

Lemma bounded_count_sound : forall E fs c, facts_hold E fs ->
  bounded_count fs c = true -> 1 <= bv_unsigned (den E c) <= 1000.
Proof.
  intros E fs c FH H. unfold bounded_count in H.
  destruct (decide_ltu fs c (VL (wlit 1001))) as [[|]|] eqn:D1; try discriminate.
  pose proof (decide_ltu_sound E fs FH _ _ _ D1) as L. apply (proj1 (ltu_iff _ _ true)) in L.
  cbn [den] in L. rewrite wbv_unsigned, wlit_ok in L. change (to_Z 1001%uint63) with 1001 in L.
  pose proof (nz_known_sound E fs c FH H) as NZ.
  pose proof (bv_unsigned_in_range _ (den E c)). lia.
Qed.

End U32.
