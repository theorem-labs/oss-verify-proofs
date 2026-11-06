(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cs X1dg X1df X1ck X1co X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0ys X0wh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yt.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation mem := (word -> option byte).

Lemma land3_al a : a mod 4 = 0 -> Z.land a 3 = 0.
Proof. intros H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.
Lemma land7_al a : a mod 8 = 0 -> Z.land a 7 = 0.
Proof. intros H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Ltac bdec1 :=
lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
match constr:((R, pc)) with
| context [Z.ltb ?a ?b] => first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; lia) ]
| context [Z.eqb ?a ?b] => first [ replace (Z.eqb a b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia) ]
end
end.
Ltac alitx1 := match goal with |- context [Z.lxor ?a ?b] => alit_bin Z.lxor a b end.
Ltac balits := repeat first [ alit1 | alitx1 ].
Ltac bdec := repeat bdec1; cbn [Z.b2z negb andb orb]; balits.

Ltac bnorm :=
repeat match goal with
| |- context [bv_swrap 32 ?a] => rewrite (swrap32_small a) by lia
| |- context [Z.shiftl ?a ?k] => rewrite (Z.shiftl_mul_pow2 a k) by lia
| |- context [?a mod 18446744073709551616] => rewrite (Z.mod_small a 18446744073709551616) by lia
| |- context [Z.lxor ?y 9223372036854775808] =>
replace (Z.lxor y 9223372036854775808) with (y + 9223372036854775808) by (change 9223372036854775808 with (2 ^ 63); symmetry; apply zb_lxor_pow2_small; lia)
| |- context [Z.lxor ?y 18446744073709551615] => rewrite (zb_lxor_ones y) by lia
| |- context [Z.lxor ?a ?a] => rewrite (Z.lxor_nilpotent a)
| |- context [Z.land ?a 3] => rewrite (land3_al a) by assumption
| |- context [Z.land ?a 7] => rewrite (land7_al a) by assumption
end; change (2 ^ 2) with 4 in *.
Ltac bato p := repeat (tryif at_pc p then fail else (tryif at_if then first [ lit_if | (bdec; lit_if) | sh_if | (bnorm; bdec; first [ lit_if | sh_if ]) ] else astep)); first [ at_pc p | show_pc_fail p ].

Ltac lsp_rdB RO CDB CD row i :=
lazymatch goal with MI : mem_inv bsegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
let U := fresh "U" in let N := fresh "N" in let RD := fresh "RD" in
pose proof (RO mc MI) as U;
assert (N : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia);
pose proof (u8ro_read bsegs mc CDB CD (row + i) _ (wa (row + i + CDB)) U N ltac:(lia) ltac:(f_equal; lia)) as RD; clear U N
end.

Ltac vloop_factsB OBQ MU OF IQ ON qoff NZ :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of MU with munch ?W ?m0 mc =>
pose proof (aobj_munch bsegs W m0 mc IQ ON OBQ MU (shfree_of_aobj bsegs W m0 IQ ON OF OBQ)) as OBQc;
pose proof (munch_refl [(IQ + qoff, IQ + qoff + NZ)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (D0 : rw_cells bsegs mc (IQ + qoff) (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia)
end end.
