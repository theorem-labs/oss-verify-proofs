(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_lits Lept_env LeptC_kit LeptL_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma lmask_bytes : forall m : mem, mem_inv asegs m ->
  exists bs, bytes_at asegs m 0x26420 bs /\ Z.of_nat (length bs) = 132.
Proof.
  intros m MI. destruct (image_bytes asegs 0x26420 132) as [bs|] eqn:IB; [| vm_compute in IB; discriminate IB].
  assert (OK : ro_bytes_b asegs 0x26420 bs = true) by (vm_compute in IB; injection IB as <-; vm_compute; reflexivity).
  pose proof (Lept_lits.image_bytes_length _ _ _ IB) as LB.
  exists bs. split; [apply ro_bytes_at; [exact MI| lia| rewrite LB; lia| apply ro_bytes_b_sound; exact OK]| rewrite LB; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma rmask32_bytes : forall m : mem, mem_inv asegs m ->
  exists bs, bytes_at asegs m 0x26360 bs /\ Z.of_nat (length bs) = 132.
Proof.
  intros m MI. destruct (image_bytes asegs 0x26360 132) as [bs|] eqn:IB; [| vm_compute in IB; discriminate IB].
  assert (OK : ro_bytes_b asegs 0x26360 bs = true) by (vm_compute in IB; injection IB as <-; vm_compute; reflexivity).
  pose proof (Lept_lits.image_bytes_length _ _ _ IB) as LB.
  exists bs. split; [apply ro_bytes_at; [exact MI| lia| rewrite LB; lia| apply ro_bytes_b_sound; exact OK]| rewrite LB; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma srai63_nonneg : forall X, 0 <= X < 2^63 -> bv_signed (Z_to_bv 64 X) ≫ 63 = 0.
Proof. intros X H. rewrite signed_lit64 by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Lemma srai63_nonneg_div : forall X, 0 <= X < 2^63 -> bv_signed (Z_to_bv 64 X) / 9223372036854775808 = 0.
Proof. intros X H. rewrite signed_lit64 by lia. apply Z.div_small. lia. Qed.
Lemma srai63_neg : forall X, - 2^63 <= X < 0 -> bv_signed (Z_to_bv 64 X) ≫ 63 = -1.
Proof. intros X H. rewrite signed_lit64 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^63) with 9223372036854775808 in *. Z.div_mod_to_equations. lia. Qed.
Lemma lxor_sign_nonneg : forall X, 0 <= X < 2^63 -> Z.lxor X 9223372036854775808 = X + 9223372036854775808.
Proof.
  intros X H. change 9223372036854775808 with (2^63).
  rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec n 63) as [->|NE].
  - rewrite (Z.bits_above_log2 X 63); [reflexivity| lia|]. destruct (Z.eq_dec X 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - rewrite Z.pow2_bits_false by lia. apply andb_false_r.
Qed.
Lemma sgtz_nonneg : forall X, 0 <= X < 2^63 -> Z.b2z (9223372036854775808 <? Z.lxor X 9223372036854775808) = Z.b2z (0 <? X).
Proof. intros X H. rewrite lxor_sign_nonneg by lia. f_equal. destruct (Z.ltb_spec 9223372036854775808 (X + 9223372036854775808)), (Z.ltb_spec 0 X); lia || reflexivity. Qed.
Lemma land_ones64 : forall E, 0 <= E < 2^64 -> Z.land 18446744073709551615 E = E.
Proof. intros E H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma land_negw_sgtz : forall E, 0 <= E < 2^63 -> Z.land (bv_swrap 32 (0 - Z.b2z (0 <? E)) mod 18446744073709551616) E = E.
Proof.
  intros E H. destruct (Z.eq_dec E 0) as [->|NE]; [apply Z.land_0_r|].
  replace (0 <? E) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change (bv_swrap 32 (0 - 1) mod 18446744073709551616) with 18446744073709551615. apply land_ones64. lia.
Qed.
Lemma land_neg_sgtz : forall E, 0 <= E < 2^63 -> Z.land ((0 - Z.b2z (0 <? E)) mod 18446744073709551616) E = E.
Proof.
  intros E H. destruct (Z.eq_dec E 0) as [->|NE]; [apply Z.land_0_r|].
  replace (0 <? E) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((0 - 1) mod 18446744073709551616) with 18446744073709551615. apply land_ones64. lia.
Qed.
Lemma swrap32_modadd : forall A B, - 2^31 <= A + B < 2^31 -> bv_swrap 32 (A mod 18446744073709551616 + B) = A + B.
Proof.
  intros A B H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  change (2^31) with 2147483648 in H.
  Z.div_mod_to_equations. lia.
Qed.
Lemma lxor_sign_high : forall Y, 9223372036854775808 <= Y < 18446744073709551616 -> Z.lxor Y 9223372036854775808 = Y - 9223372036854775808.
Proof.
  intros Y H. set (Y' := Y - 9223372036854775808). replace Y with (Y' + 9223372036854775808) by (unfold Y'; lia).
  rewrite <- (lxor_sign_nonneg Y') by (unfold Y'; lia). rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. unfold Y'. lia.
Qed.
Lemma sgtz_nonpos : forall E, - 2^63 <= E <= 0 ->
  Z.b2z (9223372036854775808 <? Z.lxor (E mod 18446744073709551616) 9223372036854775808) = 0.
Proof.
  intros E H. destruct (Z.eq_dec E 0) as [->|NE]; [reflexivity|].
  assert (M : E mod 18446744073709551616 = E + 18446744073709551616).
  { symmetry. apply (Z.mod_unique _ _ (-1)); lia. }
  rewrite M, lxor_sign_high by lia.
  replace (9223372036854775808 <? E + 18446744073709551616 - 9223372036854775808) with false; [reflexivity|].
  symmetry. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Ltac show_reg n := reg_val (Z_to_bv 5 n) ltac:(fun x => idtac "REG" n "=" x).

(* [comment removed for export] *)
Ltac cn BD :=
  rewrite ?Z.sub_0_r, ?Z.add_0_l, ?Z.add_0_r, ?Z.land_0_l;
  repeat match goal with |- context [bv_swrap 32 (?A mod 18446744073709551616 + ?B)] =>
    rewrite (swrap32_modadd A B) by (clear - BD; unfold hid in *; lia) end;
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - BD; unfold hid in *; lia) end;
  repeat match goal with
  | |- context [Z.b2z (9223372036854775808 <? Z.lxor (?E mod 18446744073709551616) 9223372036854775808)] =>
      rewrite (sgtz_nonpos E) by (clear - BD; unfold hid in *; lia)
  end;
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by (clear - BD; unfold hid in *; lia) end;
  repeat match goal with
  | |- context [bv_signed (Z_to_bv 64 ?X) ≫ 63] => rewrite (srai63_nonneg X) by (clear - BD; unfold hid in *; lia)
  | |- context [bv_signed (Z_to_bv 64 ?X) / 9223372036854775808] => rewrite (srai63_nonneg_div X) by (clear - BD; unfold hid in *; lia)
  | |- context [Z.b2z (9223372036854775808 <? Z.lxor ?X 9223372036854775808)] => rewrite (sgtz_nonneg X) by (clear - BD; unfold hid in *; lia)
  | |- context [Z.land (bv_swrap 32 (0 - Z.b2z (0 <? ?E)) mod 18446744073709551616) ?E] => rewrite (land_negw_sgtz E) by (clear - BD; unfold hid in *; lia)
  | |- context [Z.land ((0 - Z.b2z (0 <? ?E)) mod 18446744073709551616) ?E] => rewrite (land_neg_sgtz E) by (clear - BD; unfold hid in *; lia)
  end;
  rewrite ?Z.sub_0_r, ?Z.add_0_l, ?Z.add_0_r, ?Z.land_0_l.

(* [comment removed for export] *)
Ltac merge4 PC r1 r2 r3 r4 :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u1 u2 u3 u4 : word,
                 ms' = MS (@bvmap_set 5 word r1 u1 (@bvmap_set 5 word r2 u2 (@bvmap_set 5 word r3 u3 (@bvmap_set 5 word r4 u4 R))))
                          F (Z_to_bv 64 PC) fc rv m ro));
      [ | let u1 := fresh "u" in let u2 := fresh "u" in let u3 := fresh "u" in let u4 := fresh "u" in let E := fresh "E" in
          let ms := fresh "ms" in intros ms (u1 & u2 & u3 & u4 & E); subst ms; norm_regset ]
  end.
Ltac merge_done4 := apply evt_done; do 4 eexists; norm_regset; reflexivity.
