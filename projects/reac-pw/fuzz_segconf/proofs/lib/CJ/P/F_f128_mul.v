(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require SFModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require F_sf_helpers2.
Module F_f128_mul_core1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SFModel.
Export OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.F_sf_helpers2.SF_buildtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
Ltac model_reg_tac n X mexpr ::=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      first [ constr_eq e mexpr
            | replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
                by (first [ zeq_special e mexpr
                          | f_equal; zeq_fast
                          | rewrite Z_to_bv_land64; f_equal; zeq_fast
                          | apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq_fast
                          | idtac "note: model_reg" X ": slow path for" e; fail
                          | f_equal; zeq
                          | apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
                          | apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
      name_as_tac X mexpr
  | _ => fail "model_reg: register" n "holds" w
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sf_vocab :=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI];
  rewrite ?b2z_Zb2z.

(* [comment removed for export] *)
Ltac fold_head_let :=
  lazymatch goal with
  | |- (let x := ?b in ?c) = ?r =>
      match goal with
      | H := ?b' : Z |- _ =>
          constr_eq b b';
          let c' := eval cbv beta in ((fun x : Z => c) H) in
          change ((let x := b in c) = r) with (c' = r)
      end
  end.
Ltac fold_model_lets := repeat fold_head_let.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MC_tail (signHi expSum hi_hi hi_lo lo_hi lo_lo scale : Z) : Z :=
  let scaleAdj := scale - 0x3fff in
  let productExponent := expSum + scaleAdj in
  if is_neg64 (shl64 hi_hi 15) then
    let productExponent1 := productExponent + 1 in
    if negb (productExponent1 <? 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
    else mul_finish signHi productExponent1 hi_hi hi_lo lo_hi lo_lo
  else
    let hi_hi1 := Z.lor (shl64 hi_hi 1) (shr64 hi_lo 63) in
    let hi_lo1 := Z.lor (shl64 hi_lo 1) (shr64 lo_hi 63) in
    let lo_hi1 := Z.lor (shl64 lo_hi 1) (shr64 lo_lo 63) in
    let lo_lo1 := shl64 lo_lo 1 in
    if 0x7fff <=? productExponent then mk128 (Z.lor signHi INF_HI) 0
    else mul_finish signHi productExponent hi_hi1 hi_lo1 lo_hi1 lo_lo1.
End F_f128_mul_core1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import SFModel.
Import F_f128_mul_core1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma sticky_b2z : forall x, 0 <= x -> (if negb (x =? 0) then 1 else 0) = Z.b2z (0 <? x).
Proof. intros. rewrite zb_negb_eqb0 by assumption. reflexivity. Qed.

Ltac mf_pure :=
  unfold mul_finish; unfold_sf; zb_fold_lits;
  rewrite ?pe_n, ?pe_shift by lia;
  decide_tests_b;
  rewrite ?sticky_b2z by zrange_nonneg;
  strip_lands; rewrite ?Z.lor_0_r, ?Z.lor_0_l;
  f_equal; zeq2.

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

(* [comment removed for export] *)
Lemma land_sub_neg : forall c pe, (pe <= 0)%Z -> (0 <= c)%Z -> (c - pe < 18446744073709551616)%Z ->
  Z.land (c - Z.land pe 18446744073709551615) 18446744073709551615 = (c - pe)%Z.
Proof. intros. amt. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zz := zsimp; rewrite ?Z.add_0_r; try rewrite !land_sub_neg by alia; try rewrite !sext32_small by alia.

(* [comment removed for export] *)
Ltac if_decide :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      let K := fresh "K" in
      destruct c eqn:K;
      (* [comment removed for export] *)
      [ tryif (exfalso; zify_cond K; sf_prune; zb_masks_fast; lia1) then idtac else clear K
      | tryif (exfalso; zify_cond K; sf_prune; zb_masks_fast; lia1) then idtac else clear K ]
  | _ => idtac
  end.

(* [comment removed for export] *)
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