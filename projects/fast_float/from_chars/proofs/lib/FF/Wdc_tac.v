(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.fast_float.from_chars.lib.Ox.F112_003.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma mod64_mod32 : forall e, ((e mod 2^64) mod 2^32 = e mod 2^32)%Z.
Proof.
  intros e. rewrite (Z.mod_eq e (2^64)) by lia.
  replace (e - 2 ^ 64 * (e / 2 ^ 64))%Z with (e + (- (2^32 * (e / 2^64))) * 2^32)%Z by lia.
  apply Z.mod_add. lia.
Qed.

Lemma swrap32_congr : forall a b, (a mod 2^32 = b mod 2^32)%Z -> bv_swrap 32 a = bv_swrap 32 b.
Proof.
  intros a b H. unfold bv_swrap, bv_wrap. f_equal.
  change (bv_modulus 32) with (2^32)%Z.
  rewrite <- (Z.add_mod_idemp_l a), <- (Z.add_mod_idemp_l b) by lia. rewrite H. reflexivity.
Qed.

Lemma swrap32_id : forall z, (-2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31)%Z. lia. Qed.

Lemma uw_add : forall e k, bv_swrap 32 (bv_unsigned (Z_to_bv 64 e) + k) = bv_swrap 32 (e + k).
Proof.
  intros. apply swrap32_congr. rewrite unsigned_lit_wrap.
  rewrite <- Z.add_mod_idemp_l, mod64_mod32, Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma uw_sub : forall e k, bv_swrap 32 (k - bv_unsigned (Z_to_bv 64 e)) = bv_swrap 32 (k - e).
Proof.
  intros. apply swrap32_congr. rewrite unsigned_lit_wrap.
  rewrite <- Zminus_mod_idemp_r, mod64_mod32, Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma uw_sub2 : forall e1 e2, bv_swrap 32 (bv_unsigned (Z_to_bv 64 e1) - bv_unsigned (Z_to_bv 64 e2)) = bv_swrap 32 (e1 - e2).
Proof.
  intros. rewrite uw_sub. apply swrap32_congr. rewrite unsigned_lit_wrap.
  rewrite <- Zminus_mod_idemp_l, mod64_mod32, Zminus_mod_idemp_l. reflexivity.
Qed.

Lemma word_add_lit : forall e k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) + k) = Z_to_bv 64 (e + k).
Proof.
  intros. apply bv_eq. rewrite !unsigned_lit_wrap.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma word_sub_lit : forall e k, Z_to_bv 64 (k - bv_unsigned (Z_to_bv 64 e)) = Z_to_bv 64 (k - e).
Proof.
  intros. apply bv_eq. rewrite !unsigned_lit_wrap.
  rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma word_sub_lit2 : forall e1 e2, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e1) - bv_unsigned (Z_to_bv 64 e2)) = Z_to_bv 64 (e1 - e2).
Proof.
  intros. apply bv_eq. rewrite !unsigned_lit_wrap.
  rewrite Zminus_mod_idemp_r, Zminus_mod_idemp_l. reflexivity.
Qed.

Lemma word_add_lit2 : forall e1 e2, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e1) + bv_unsigned (Z_to_bv 64 e2)) = Z_to_bv 64 (e1 + e2).
Proof.
  intros. apply bv_eq. rewrite !unsigned_lit_wrap.
  rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Lemma uw_add2 : forall e1 e2, bv_swrap 32 (bv_unsigned (Z_to_bv 64 e1) + bv_unsigned (Z_to_bv 64 e2)) = bv_swrap 32 (e1 + e2).
Proof.
  intros. rewrite uw_add. apply swrap32_congr. rewrite unsigned_lit_wrap.
  rewrite <- Z.add_mod_idemp_r, mod64_mod32, Z.add_mod_idemp_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma uw_mod32 : forall p k, bv_swrap 32 (p mod 2^32 + k) = bv_swrap 32 (p + k).
Proof. intros. apply swrap32_congr. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_le_l : forall a b, (0 <= a)%Z -> (Z.land a b <= a)%Z.
Proof.
  intros a b Ha.
  assert (D : Z.land (Z.ldiff a b) (Z.land a b) = 0%Z).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  pose proof (Z.lor_ldiff_and a b) as E.
  rewrite <- Z.lxor_lor in E by exact D. rewrite <- Z.add_nocarry_lxor in E by exact D.
  destruct (Z.ldiff_nonneg a b) as [_ H2]. specialize (H2 (or_introl Ha)). lia.
Qed.
Lemma land_le_r : forall a b, (0 <= b)%Z -> (Z.land a b <= b)%Z.
Proof. intros. rewrite Z.land_comm. apply land_le_l. assumption. Qed.
Lemma land_range_r : forall a b, (0 <= b)%Z -> (0 <= Z.land a b <= b)%Z.
Proof. intros. split; [apply Z.land_nonneg; right; assumption | apply land_le_r; assumption]. Qed.

(* [comment removed for export] *)
Ltac mlia := first [ lia | Z.div_mod_to_equations; lia ].
Ltac trap_dead :=
  let Hc := fresh "Hc" in
  if_cases Hc; [ cond_cleanup Hc; rewrite ?signed_lit in Hc by lia; exfalso; mlia | clear Hc ].

Lemma zxb_lit8 : forall t, (0 <= t < 256)%Z -> zxb (Z_to_bv 8 t) = Z_to_bv 64 t.
Proof.
  intros t Ht. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

(* [comment removed for export] *)
Ltac gen_val e := let X := fresh "rv" in set (X := e) in *; clearbody X.
Ltac gen_big :=
  repeat match goal with
  | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
  | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
  | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
  | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
  | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
  | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
  | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
  | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
  | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
  | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
  | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
  | |- context [Some (zx8 ?a)] => gen_val (zx8 a)
  | |- context [Some (zx16 ?a)] => gen_val (zx16 a)
  | |- context [Some (sx32 ?a)] => gen_val (sx32 a)
  end.
Ltac gstep := step; gen_big.
(* [comment removed for export] *)
Ltac gen_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key k) in
    let v := eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end) in
    tryif is_var v then idtac else gen_val v
  end.

Ltac show_regs :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mm _) =>
    idtac "pc=" pc "mem=" mm;
    let pr k := let p := eval vm_compute in (bv_key k) in
                let v := eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end) in idtac k ":=" v in
    pr (1:reg); pr (5:reg); pr (6:reg); pr (7:reg); pr (8:reg); pr (9:reg); pr (10:reg); pr (11:reg); pr (12:reg); pr (13:reg);
    pr (14:reg); pr (15:reg); pr (16:reg); pr (17:reg); pr (18:reg); pr (19:reg); pr (20:reg); pr (21:reg); pr (22:reg);
    pr (23:reg); pr (24:reg); pr (25:reg); pr (26:reg); pr (27:reg); pr (28:reg); pr (29:reg); pr (30:reg); pr (31:reg)
  end.
