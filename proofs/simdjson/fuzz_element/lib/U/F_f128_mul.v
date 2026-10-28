(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_sf_helpers F_f128_mul_core1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Lemma land63_mod : forall y, Z.land y 63 = y mod 64.
Proof. intros. symmetry. apply mod64_land63. Qed.
Lemma landM32_mod : forall y, Z.land y 4294967295 = y mod 2^32.
Proof. intros. change 4294967295 with (2^32 - 1). apply zb_land_mask. lia. Qed.

Ltac amt := rewrite ?land_W64, ?land63_mod, ?landM32_mod;
            repeat (rewrite zb_lxor_ones by (Z.div_mod_to_equations; lia));
            rewrite ?Z.shiftr_div_pow2 by lia;
            zb_fold_lits; Z.div_mod_to_equations; lia.

Lemma pe_n : forall pe, -127 <= pe <= 0 -> Z.land (Z.land pe 18446744073709551615 + 127) 18446744073709551615 = pe + 127.
Proof. intros. amt. Qed.
Lemma pe_shift : forall pe, -127 <= pe <= 0 -> Z.land (1 - Z.land pe 18446744073709551615) 18446744073709551615 = 1 - pe.
Proof. intros. amt. Qed.
Lemma shr_land_W64 : forall x k, (0 <= x < 2^64) -> 0 <= k -> Z.land (Z.shiftr x k) 18446744073709551615 = Z.shiftr x k.
Proof. intros. rewrite land_W64. apply Z.mod_small. apply (zr_shiftr x k); assumption. Qed.

Ltac strip_lands :=
  repeat match goal with
  | |- context [Z.land (Z.shiftr ?x ?k) 18446744073709551615] =>
      rewrite (shr_land_W64 x k) by (first [zrange | zrange_nonneg | lia])
  end.

Ltac not_bitop t :=
  lazymatch t with
  | Z.lor _ _ => fail | Z.shiftl _ _ => fail | Z.b2z _ => fail | Z.ltb _ _ => fail | Z.eqb _ _ => fail
  | _ => idtac
  end.
Ltac zeq2 :=
  first
  [ reflexivity
  | lazymatch goal with
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

Lemma sticky_b2z : forall x, 0 <= x -> (if negb (x =? 0) then 1 else 0) = Z.b2z (0 <? x).
Proof. intros. rewrite zb_negb_eqb0 by assumption. reflexivity. Qed.

Ltac mf_pure :=
  unfold mul_finish; unfold_sf; zb_fold_lits;
  rewrite ?pe_n, ?pe_shift by lia;
  decide_tests_b;
  rewrite ?sticky_b2z by zrange_nonneg;
  strip_lands; rewrite ?Z.lor_0_r, ?Z.lor_0_l;
  f_equal; zeq2.

Lemma mf_caseC : forall s pe hh hl lh ll,
  -63 < pe <= 0 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s (hh ≫ Z.land (1 - pe) 63)
    (Z.lor (Z.land (Z.land (hh ≪ 1) W64 ≪ Z.land (Z.land (pe + -2) W64) 63) W64) (Z.land (hl ≫ Z.land (1 - pe) 63) W64))
    (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) W64) (Z.land (lh ≫ Z.land (1 - pe) 63) W64))
    (Z.lor (Z.lor (Z.b2z (0 <? Z.lor (Z.land (ll ≪ Z.land (pe + 127) 63) W64) 0)) 0)
          (Z.lor (Z.land (Z.land (lh ≪ 1) W64 ≪ Z.land (Z.land (pe + -2) W64) 63) W64) (Z.land (ll ≫ Z.land (1 - pe) 63) W64))).
Proof. intros * Hpe Hhh Hhl Hlh Hll.   unfold mul_finish; unfold_sf; zb_fold_lits;
  rewrite ?pe_n, ?pe_shift by lia;
  decide_tests_b;
  rewrite ?sticky_b2z by zrange_nonneg;
  strip_lands; rewrite ?Z.lor_0_r, ?Z.lor_0_l. f_equal; zeq2. Qed.

Lemma mf_caseB : forall s pe hh hl lh ll,
  pe = -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
    (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) W64) 0)
    (Z.lor (Z.lor (Z.b2z (0 <? Z.lor (Z.land (ll ≪ Z.land (pe + 127) 63) W64) 0)) 0) (Z.land (lh ≫ Z.land (1 - pe) 63) W64)).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Lemma mf_caseA : forall s pe hh hl lh ll,
  -126 <= pe < -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
    (Z.lor (Z.lor (Z.land ((hl ≫ 1) ≫ Z.land (Z.lxor (pe + 127) W64) 63) W64) (Z.land (hh ≪ Z.land (pe + 127) 63) W64)) 0)
    (Z.lor (Z.lor (Z.b2z (0 <? Z.lor (Z.lor (Z.land ((ll ≫ 1) ≫ Z.land (Z.lxor (pe + 127) W64) 63) W64)
                                            (Z.land (lh ≪ Z.land (pe + 127) 63) W64))
                                     (Z.land (ll ≪ Z.land (pe + 127) 63) W64)))
                  (Z.land (hl ≪ Z.land (pe + 127) 63) W64))
           (Z.land (lh ≫ Z.land (1 - pe) 63) W64)).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Lemma mf_normal : forall s pe hh hl lh ll,
  0 < pe <= 131072 ->
  mul_finish s pe hh hl lh ll =
  mul_round s (Z.lor (Z.land (pe ≪ 48) W64) (Z.land hh 281474976710655)) hl lh ll.
Proof.
  intros * Hpe. unfold mul_finish. unfold_sf. zb_fold_lits. decide_tests_b.
  rewrite (land_W64 pe), Z.mod_small by lia. reflexivity.
Qed.

Lemma mf_tiny : forall s pe hh hl lh ll,
  -131072 <= pe < -126 ->
  mul_finish s pe hh hl lh ll = mk128 s 0.
Proof.
  intros * Hpe. unfold mul_finish. unfold_sf. zb_fold_lits.
  replace (Z.land (1 - Z.land pe 18446744073709551615) 18446744073709551615) with (1 - pe) by (symmetry; amt).
  decide_tests_b. reflexivity.
Qed.

Lemma sext32_small : forall z, (-2147483648 <= z < 2147483648)%Z -> bv_swrap 32 z = z.
Proof.
  intros. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32 `div` 2)%Z with 2147483648%Z. lia.
Qed.

Lemma land_sub_neg : forall c pe, (pe <= 0)%Z -> (0 <= c)%Z -> (c - pe < 18446744073709551616)%Z ->
  Z.land (c - Z.land pe 18446744073709551615) 18446744073709551615 = (c - pe)%Z.
Proof. intros. amt. Qed.

Ltac zz := zsimp; rewrite ?Z.add_0_r; try rewrite !land_sub_neg by alia; try rewrite !sext32_small by alia.
Ltac zzstep := step; zz.

Ltac if_decide :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      let K := fresh "K" in
      destruct c eqn:K;

      [ tryif (exfalso; zify_cond K; sf_prune; zb_masks_fast; lia1) then idtac else clear K
      | tryif (exfalso; zify_cond K; sf_prune; zb_masks_fast; lia1) then idtac else clear K ]
  | _ => idtac
  end.

Ltac zrange2 :=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | Z.shiftr _ _ => apply zr_shiftr; [zrange2 | first [lia | zrange_nonneg]]
      | Z.lor _ _ => apply zr_lor; [zrange2 | zrange2]
      | _ => zrange
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange2
  end.

Section MulCore.

End MulCore.
