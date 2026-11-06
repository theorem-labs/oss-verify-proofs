(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma slt0_nonneg : forall x, 0 <= x < 2^63 -> (Z.lxor x 9223372036854775808 <? 9223372036854775808) = false.
Proof.
  intros x Hx. apply Z.ltb_ge.
  assert (E : Z.lxor x 9223372036854775808 = x + 9223372036854775808).
  { symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 63 n) as [<-|NE]; [| apply andb_false_r].
    rewrite andb_true_r. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite E. lia.
Qed.

Ltac swrap_fix := repeat match goal with |- context [bv_swrap 32 ?z] =>
  rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); lia) end.
Ltac po_fix :=
  repeat match goal with
  | |- context [Z.lxor ?x 9223372036854775808 <? 9223372036854775808] => rewrite (slt0_nonneg x) by lia
  | |- context [?a + ?b <? ?b] => replace (a + b <? b) with false by (symmetry; apply Z.ltb_ge; lia)
  | |- context [?a + ?b <? ?a] => replace (a + b <? a) with false by (symmetry; apply Z.ltb_ge; lia)
  | |- context [?a <? 1] => replace (a <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
  | |- context [?a =? 0] => replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia)
  | |- context [0 <? ?a] => replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia)
  end; cbn [Z.b2z]; change (Z.lxor 0 0) with 0; change (Z.lxor 0 1) with 1; change (Z.lxor 1 0) with 1.
(* [comment removed for export] *)
Ltac al_fix :=
  repeat match goal with
  | |- context [Z.land ?x 3] => replace (Z.land x 3) with 0
        by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; Z.div_mod_to_equations; lia)
  | |- context [Z.land ?x 7] => replace (Z.land x 7) with 0
        by (symmetry; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia)
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma signed_of_Z64 : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Lemma mulh_guard : forall a b, 0 <= a < 2^31 -> 0 <= b < 2^31 ->
  bv_eqb (Z_to_bv 64 (bv_signed (Z_to_bv 64 a) * bv_signed (Z_to_bv 64 b) / 18446744073709551616))
         (Z_to_bv 64 (bv_signed (Z_to_bv 64 (a mod 18446744073709551616 * b)) / 9223372036854775808)) = true.
Proof.
  intros a b Ha Hb. rewrite (Z.mod_small a) by lia. rewrite !signed_of_Z64 by nia. rewrite !Z.div_small by nia. reflexivity.
Qed.
Ltac mulh_fix :=
  lazymatch goal with
  | |- context [bv_signed (Z_to_bv 64 _) * bv_signed (Z_to_bv 64 _) / 18446744073709551616] =>
      (* [comment removed for export] *)
      repeat match goal with
      | |- context [bv_signed (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ?w) * _)) * bv_signed (Z_to_bv 64 _) / 18446744073709551616] =>
          rewrite (unsigned_lit w) by lia
      end;
      repeat match goal with
      | |- context [bv_eqb (Z_to_bv 64 (bv_signed (Z_to_bv 64 ?a) * bv_signed (Z_to_bv 64 ?b) / 18446744073709551616)) _] =>
          rewrite (mulh_guard a b) by lia
      end
  end.
Ltac guard_fix := try sx32_fix; swrap_fix; po_fix; al_fix; try mulh_fix.

(* [comment removed for export] *)
Ltac gwalk1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | shbr_inv | shbr_x3 | br | progress guard_fix; br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
Ltac gwalk stops := repeat (tryif at_stop stops then fail else gwalk1).
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

(* [comment removed for export] *)
Ltac awalk1 ::= gwalk1.
Ltac cwalk1 ::= gwalk1.
Ltac lwalk1 ::= gwalk1.
