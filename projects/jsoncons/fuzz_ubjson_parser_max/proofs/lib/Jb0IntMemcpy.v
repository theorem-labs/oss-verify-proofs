(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import muslA.Jb0MemcpyBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0IntMemcpy () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.muslA.Jb0MemcpyBase."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "5wbytes"; "6msteps"; "7at_"; "7ret_ok"; "8getr"; "8mkst"; "9keeps"; ":memk"; ";loaded_segments"]; ["<add"; "<le"; "<of_nat"; "0bs"; "0dst"; "0fx"; "0k"; "0mem0"; "0n"; "0q"; "0regs"; "0regs'"; "0ret"; "0rom"; "0src"; "=BV"]; ["=Z_to_bv"; "=bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Section ALL.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.
#[local] Notation MK := (memk mem0 dst bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac cond :=
rwH; rewrite ?at_addi; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Lemma loop_run : ltac2:(TCodec.tc2 tcn__Jb0IntMemcpy "RJ'0&6y5'Q1yR0%211%5241'5&:r2%211'3&;r4(O+1(1%33?21%6251r3%93?21r5+;%93E17%<231&9vN%2218%A3G41r6+=%A3M1?%D231vD%921E%H3N31r7+<%H3Q41F%K231vH%@281%O3Q531&Az%221@&@&Br:%211%42>1%521Q4%Q93Q=1<'4'2'8&?&<vEr;+a[[8%Q?3QI1Q=/01QI&>vGvCr9%443Q221vM%<5;:721r1%847Q66O%?5>2H14%B3A41&=%12@5%F231qQHR71%I2R81p0K1p0Q31p0Q71p0Q?1p0QG1p0R01p0R;1pQ>R?1pQJRB1pQFRB1pQDRI1").
Proof.
induction q as [|q IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hq;
pose proof (u64_range src); pose proof (u64_range dst).
- eexists. split.
+ mlbu (ltac:(oF' 0x8ad68%Z)) (ltac:(oD' 0x8ad68%Z)) k.
msb (ltac:(oF' 0x8ad6c%Z)) (ltac:(oD' 0x8ad6c%Z)) k ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0x8ad70%Z)) (ltac:(oD' 0x8ad70%Z)).
stepn (ltac:(oF' 0x8ad74%Z)) (ltac:(oD' 0x8ad74%Z)).
stepb_ft (ltac:(oF' 0x8ad78%Z)) (ltac:(oD' 0x8ad78%Z)) ltac:(cond).
stepret (ltac:(oF' 0x8ad7c%Z)) (ltac:(oD' 0x8ad7c%Z)) ret ltac:(rwH; reflexivity).
replace (MK (k + 1)) with (MK n) by (f_equal; lia).
apply mst_refl.
+ post.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x8ad68 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = at_ dst n /\ keeps regs r)).
+ eexists. split.
* mlbu (ltac:(oF' 0x8ad68%Z)) (ltac:(oD' 0x8ad68%Z)) k.
msb (ltac:(oF' 0x8ad6c%Z)) (ltac:(oD' 0x8ad6c%Z)) k ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0x8ad70%Z)) (ltac:(oD' 0x8ad70%Z)).
stepn (ltac:(oF' 0x8ad74%Z)) (ltac:(oD' 0x8ad74%Z)).
stepb_tk (ltac:(oF' 0x8ad78%Z)) (ltac:(oD' 0x8ad78%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
Theorem int_memcpy_run : ltac2:(TCodec.tc2 tcn__Jb0IntMemcpy "R6&6y5'Q1yR0%211%5241&:r1%211'3&;r3(O+1(1%33>21%6251r2%93>21r4+:%93D17%<231vD%?3D21r5+;%?3J1=%B231vN%E3J21r6+<%E3Q01C%H231&Q0vH%22Q21%M3Q241'4'2'8&?&<vEr8+a[ZL%Q33Q<1Q1/01Q<vGvM%8576321r7&7vC%236Q01%=5<QA416%@3?61&=%12>QD%D231qQHQH1%G2QI1p0I1p0Q21p0Q91p0Q@1p0QK1pQJR01pQFR01").
Proof.
intros regs ret Hret H1 H10 H11 H12. pose proof (u64_range src); pose proof (u64_range dst).
rewrite <- (memk_n mem0 dst src n bs HOK).
replace (mkst regs (0x8ad5c : word) mem0 rom) with (mkst regs (0x8ad5c : word) (MK 0) rom) by reflexivity.
destruct (Z.eq_dec n 0) as [Hz|Hz].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x8ad5c%Z)) (ltac:(oD' 0x8ad5c%Z)) ltac:(cond).
stepret (ltac:(oF' 0x8ad7c%Z)) (ltac:(oD' 0x8ad7c%Z)) ret ltac:(rwH; reflexivity).
replace (MK 0) with (MK n) by (f_equal; lia).
apply mst_refl.
+ post.
- assert (Hq : exists q : nat, (Z.of_nat q + 1 = n)%Z) by (exists (Z.to_nat (n - 1)); rewrite Z2Nat.id; lia).
destruct Hq as (q & Hq).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x8ad68 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = at_ dst n /\ keeps regs r)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0x8ad5c%Z)) (ltac:(oD' 0x8ad5c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x8ad60%Z)) (ltac:(oD' 0x8ad60%Z)).
stepn (ltac:(oF' 0x8ad64%Z)) (ltac:(oD' 0x8ad64%Z)).
apply mst_refl.
* cbv beta. post.
-- rewrite at_0. reflexivity.
-- rewrite at_0. reflexivity.
-- unfold v_add, at_. f_equal. unorm. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (loop_run q r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
End ALL.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
