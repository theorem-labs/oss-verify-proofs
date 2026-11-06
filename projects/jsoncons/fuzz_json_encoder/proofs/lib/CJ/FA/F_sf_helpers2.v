(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_sf_helpers.
Import ListNotations.
Local Open Scope Z_scope.

From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SF_buildtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shr56_mul64_range : forall y k, 0 <= Z.shiftr (mul64 y k) 56 < 256.
Proof.
  intros. unfold mul64. pose proof (wrap64_range (y * k)) as H.
  rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. } apply Z.div_lt_upper_bound; lia.
Qed.

Lemma clz64_mirror_range : forall x, 0 <= clz64_mirror x < 256.
Proof. intros x. unfold clz64_mirror. cbv zeta. apply shr56_mul64_range. Qed.

Lemma lor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros a b Ha Hb. split. { apply Z.lor_nonneg; lia. }
  destruct (Z.eq_dec a 0) as [->|Na]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|Nb]. { rewrite Z.lor_0_r. lia. }
  assert (Hl : Z.lor a b <> 0). { intro E. apply Z.lor_eq_0_iff in E. lia. }
  pose proof (Z.lor_nonneg a b).
  change 256 with (2^8). apply Z.log2_lt_pow2; [lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma clz128_mirror_range : forall hi lo, 0 <= clz128_mirror hi lo < 256.
Proof.
  intros. unfold clz128_mirror. cbv zeta. apply lor_lt_256.
  - apply clz64_mirror_range.
  - destruct (hi =? 0); cbv; split; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land63_mod : forall y, Z.land y 63 = y mod 64.
Proof. intros. symmetry. apply mod64_land63. Qed.
Lemma landM32_mod : forall y, Z.land y 4294967295 = y mod 2^32.
Proof. intros. change 4294967295 with (2^32 - 1). apply zb_land_mask. lia. Qed.
Lemma swrap32_arith : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. intros. reflexivity. Qed.
Lemma shr_land_W64 : forall x k, (0 <= x < 2^64) -> 0 <= k -> Z.land (Z.shiftr x k) 18446744073709551615 = Z.shiftr x k.
Proof. intros. rewrite land_W64. apply Z.mod_small. apply (zr_shiftr x k); assumption. Qed.
Lemma land_ones_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros. rewrite Z.land_comm, land_W64. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Ltac amt := rewrite ?land_W64, ?land63_mod, ?landM32_mod, ?swrap32_arith;
            repeat (rewrite zb_lxor_ones by (Z.div_mod_to_equations; lia));
            rewrite ?Z.shiftr_div_pow2 by lia;
            zb_fold_lits; Z.div_mod_to_equations; lia.
Ltac not_bitop t :=
  lazymatch t with
  | Z.lor _ _ => fail | Z.shiftl _ _ => fail | Z.b2z _ => fail | Z.ltb _ _ => fail | Z.eqb _ _ => fail
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac zeq2 :=
  first
  [ reflexivity
  | lazymatch goal with
    | |- Z.land _ 63 = Z.land _ 63 => first [ amt | f_equal; zeq2 ]   (* [comment removed for export] *)
    | |- Z.lor ?a ?b = Z.lor _ _ =>
        first [ f_equal; zeq2 | rewrite (Z.lor_comm a b); f_equal; zeq2
              | lazymatch a with Z.lor ?a1 ?a2 =>
                  first [ rewrite <- (Z.lor_assoc a1 a2 b);
                          first [ f_equal; zeq2 | rewrite (Z.lor_comm a1 (Z.lor a2 b)); f_equal; zeq2 ]
                        | rewrite (Z.lor_comm (Z.lor a1 a2) b), (Z.lor_assoc b a1 a2); f_equal; zeq2 ] end ]
    | |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq2 | rewrite (Z.land_comm a b); f_equal; zeq2 ]
    | |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq2 | rewrite (Z.lxor_comm a b); f_equal; zeq2 ]
    | |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq2 | rewrite (Z.add_comm a b); f_equal; zeq2 ]
    | |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq2
    | |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq2
    | |- Z.b2z _ = Z.b2z _ => f_equal; zeq2
    | |- Z.ltb _ _ = Z.ltb _ _ => f_equal; zeq2
    | |- Z.eqb _ _ = Z.eqb _ _ => f_equal; zeq2
    end
  | lazymatch goal with |- ?l = ?r => not_bitop l; not_bitop r end; amt ].
Ltac strip_lands :=
  repeat match goal with
  | |- context [Z.land (Z.shiftr ?x ?k) 18446744073709551615] =>
      rewrite (shr_land_W64 x k) by (first [zrange | zrange_nonneg | lia])
  end.

(* [comment removed for export] *)
Definition nd_hi (sigHi sigLo : Z) : Z := let '(h, _, _) := norm_denormal sigHi sigLo in h.
Definition nd_lo (sigHi sigLo : Z) : Z := let '(_, l, _) := norm_denormal sigHi sigLo in l.
Definition nd_clz (sigHi sigLo : Z) : Z := let '(_, _, c) := norm_denormal sigHi sigLo in c.
Lemma norm_denormal_eta : forall sigHi sigLo,
  norm_denormal sigHi sigLo = (nd_hi sigHi sigLo, nd_lo sigHi sigLo, nd_clz sigHi sigLo).
Proof. intros. unfold nd_hi, nd_lo, nd_clz. destruct (norm_denormal sigHi sigLo) as [[h l] c]. reflexivity. Qed.

Lemma nd_clz_eq : forall sigHi sigLo, nd_clz sigHi sigLo = clz128_mirror sigHi sigLo.
Proof.
  intros. unfold nd_clz, norm_denormal.
  destruct (shl128_mirror sigHi sigLo (sub64 (clz128_mirror sigHi sigLo) 15)) as [h l]. reflexivity.
Qed.
Lemma nd_clz_range : forall sigHi sigLo, 0 <= nd_clz sigHi sigLo < 256.
Proof. intros. rewrite nd_clz_eq. apply clz128_mirror_range. Qed.

(* [comment removed for export] *)
Lemma clz128_hi_nz : forall hi lo, hi <> 0 -> clz128_mirror hi lo = clz64_mirror hi.
Proof.
  intros. unfold clz128_mirror. replace (hi =? 0) with false by (symmetry; apply Z.eqb_neq; assumption).
  cbn. apply Z.lor_0_r.
Qed.
Lemma clz128_hi_z : forall hi lo, hi = 0 -> clz128_mirror hi lo = Z.lor (clz64_mirror lo) 64.
Proof. intros. subst. reflexivity. Qed.

(* [comment removed for export] *)