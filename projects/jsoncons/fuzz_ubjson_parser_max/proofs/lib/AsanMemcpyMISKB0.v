(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib AsanMemcpyBaseKB0 AsanMemcpyALKB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanMemcpyMISKB0 () := ([""; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemcpyBaseKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemcpyMISKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1I"; "1and"; "1eq"; "1ex"; "1or"; "2Z"; "3bvmap"; "4memk"; "5asanreflect_fx"; "6msteps"; "7at_"; "8getr"; "8mkst"; "9keeps"; ":loaded_segments"; ";add"]; [";land"; ";le"; ";lt"; ";pow"; "0a2"; "0bs"; "0dst"; "0k"; "0m"; "0mem0"; "0n"; "0regs"; "0regs'"; "0ret"; "0rom"; "0src"]; ["<BV"; "<Z_to_bv"; "<bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section MIS.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.
#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
#[local] Notation B := (b_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.
Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msw F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac sbp := apply sb_val_plain.
Lemma b4_blk : ltac2:(TCodec.tc2 tcn__AsanMemcpyMISKB0 "S5&6y5'Q2yR0%211%5241'5'2&;r4(Q0+1(0%33<21%6251r3%93<21r5+;%93B17%<231&:vO%2218%A3D41r6+=%A3J1?%D231vF%921E%H3K31r7+<%H3Q11F%K231%M3Q01K&Az%221>&?+4%22:1vJ%7221'3'1'9&>&<&8r;+QTjkH%Q;3QB1Q9/01QB&7vIvEr9%443N21vN%<5;:721r1+QTjm4%QF3QM1QD/01QM%J28I%<4;Q6:1%C5B6318%F3E81%QN28QIr:%R13R421%R12;QF%QE2QD8%R43R721%R42>QA%QH2Q@;%R73R:21%R72AQ=r8%R:3R=21&=%12Q0E%Q6231%Q7271%Q82;1%Q92?1%Q:2C1qQJRD1%Q=2RE1p0Q?1p0QE1p0QI1p0QO1p0R71p0R@1pQ:RM1pQ@RL1pQLRO1pQHRO1").
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
- mlbu (ltac:(oF' 0x126b78%Z)) (ltac:(oD' 0x126b78%Z)) k. mlbu (ltac:(oF' 0x126b7c%Z)) (ltac:(oD' 0x126b7c%Z)) (k+1)%Z. mlbu (ltac:(oF' 0x126b80%Z)) (ltac:(oD' 0x126b80%Z)) (k+2)%Z. mlbu (ltac:(oF' 0x126b84%Z)) (ltac:(oD' 0x126b84%Z)) (k+3)%Z.
stepn (ltac:(oF' 0x126b88%Z)) (ltac:(oD' 0x126b88%Z)).
stepn (ltac:(oF' 0x126b8c%Z)) (ltac:(oD' 0x126b8c%Z)).
msb (ltac:(oF' 0x126b90%Z)) (ltac:(oD' 0x126b90%Z)) k ltac:(sbp). msb (ltac:(oF' 0x126b94%Z)) (ltac:(oD' 0x126b94%Z)) (k+1)%Z ltac:(sbp).
msb (ltac:(oF' 0x126b98%Z)) (ltac:(oD' 0x126b98%Z)) (k+2)%Z ltac:(sbp). msb (ltac:(oF' 0x126b9c%Z)) (ltac:(oD' 0x126b9c%Z)) (k+3)%Z ltac:(sbp).
stepn (ltac:(oF' 0x126ba0%Z)) (ltac:(oD' 0x126ba0%Z)).
mk_eq. apply mst_refl.
- post.
Qed.
Lemma b8_blk : ltac2:(TCodec.tc2 tcn__AsanMemcpyMISKB0 "S5&6y5'Q2yR0%211%5241'5'2&;r4(Q0+1(0%33<21%6251r3%93<21r5+;%93B17%<231&:vO%2218%A3D41r6+=%A3J1?%D231vF%921E%H3K31r7+<%H3Q11F%K231%M3Q01K&Az%221>&?+8%22:1vJ%7221'3'1'9&>&<&8r;+QTji4%Q;3QB1Q9/01QB&7vIvEr9%443N21vN%<5;:721r1+QTjk@%QF3QM1QD/01QM%J28I%<4;Q6:1%C5B6318%F3E81%QN28QIr:%R13R421%R12;QF%QE2QD8%R43R721%R42>QA%QH2Q@;%R73R:21%R72AQ=r8%R:3R=21&=%12Q0E%Q6231%Q7271%Q82;1%Q92?1%Q:2C1qQJRD1%Q=2RE1p0Q?1p0QE1p0QI1p0QO1p0R71p0R@1pQ:RM1pQ@RL1pQLRO1pQHRO1").
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
- mlbu (ltac:(oF' 0x126b24%Z)) (ltac:(oD' 0x126b24%Z)) k. mlbu (ltac:(oF' 0x126b28%Z)) (ltac:(oD' 0x126b28%Z)) (k+1)%Z. mlbu (ltac:(oF' 0x126b2c%Z)) (ltac:(oD' 0x126b2c%Z)) (k+2)%Z. mlbu (ltac:(oF' 0x126b30%Z)) (ltac:(oD' 0x126b30%Z)) (k+3)%Z.
mlbu (ltac:(oF' 0x126b34%Z)) (ltac:(oD' 0x126b34%Z)) (k+4)%Z. mlbu (ltac:(oF' 0x126b38%Z)) (ltac:(oD' 0x126b38%Z)) (k+5)%Z. mlbu (ltac:(oF' 0x126b3c%Z)) (ltac:(oD' 0x126b3c%Z)) (k+6)%Z. mlbu (ltac:(oF' 0x126b40%Z)) (ltac:(oD' 0x126b40%Z)) (k+7)%Z.
stepn (ltac:(oF' 0x126b44%Z)) (ltac:(oD' 0x126b44%Z)).
msb (ltac:(oF' 0x126b48%Z)) (ltac:(oD' 0x126b48%Z)) k ltac:(sbp). msb (ltac:(oF' 0x126b4c%Z)) (ltac:(oD' 0x126b4c%Z)) (k+1)%Z ltac:(sbp).
msb (ltac:(oF' 0x126b50%Z)) (ltac:(oD' 0x126b50%Z)) (k+2)%Z ltac:(sbp). msb (ltac:(oF' 0x126b54%Z)) (ltac:(oD' 0x126b54%Z)) (k+3)%Z ltac:(sbp).
stepn (ltac:(oF' 0x126b58%Z)) (ltac:(oD' 0x126b58%Z)).
msb (ltac:(oF' 0x126b5c%Z)) (ltac:(oD' 0x126b5c%Z)) (k+4)%Z ltac:(sbp). msb (ltac:(oF' 0x126b60%Z)) (ltac:(oD' 0x126b60%Z)) (k+5)%Z ltac:(sbp).
msb (ltac:(oF' 0x126b64%Z)) (ltac:(oD' 0x126b64%Z)) (k+6)%Z ltac:(sbp). msb (ltac:(oF' 0x126b68%Z)) (ltac:(oD' 0x126b68%Z)) (k+7)%Z ltac:(sbp).
stepn (ltac:(oF' 0x126b6c%Z)) (ltac:(oD' 0x126b6c%Z)).
mk_eq. apply mst_refl.
- post.
Qed.
Lemma b16_blk : ltac2:(TCodec.tc2 tcn__AsanMemcpyMISKB0 "S5&6y5'Q2yR0%211%5241'5'2&;r4(Q0+1(0%33<21%6251r3%93<21r5+;%93B17%<231&:vO%2218%A3D41r6+=%A3J1?%D231vF%921E%H3K31r7+<%H3Q11F%K231%M3Q01K&Az%221>&?+@%22:1vJ%7221'3'1'9&>&<&8r;+QTjd@%Q;3QB1Q9/01QB&7vIvEr9%443N21vN%<5;:721r1+QTjhL%QF3QM1QD/01QM%J28I%<4;Q6:1%C5B6318%F3E81%QN28QIr:%R13R421%R12;QF%QE2QD8%R43R721%R42>QA%QH2Q@;%R73R:21%R72AQ=r8%R:3R=21&=%12Q0E%Q6231%Q7271%Q82;1%Q92?1%Q:2C1qQJRD1%Q=2RE1p0Q?1p0QE1p0QI1p0QO1p0R71p0R@1pQ:RM1pQ@RL1pQLRO1pQHRO1").
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
- mlbu (ltac:(oF' 0x126a90%Z)) (ltac:(oD' 0x126a90%Z)) k. mlbu (ltac:(oF' 0x126a94%Z)) (ltac:(oD' 0x126a94%Z)) (k+1)%Z. mlbu (ltac:(oF' 0x126a98%Z)) (ltac:(oD' 0x126a98%Z)) (k+2)%Z. mlbu (ltac:(oF' 0x126a9c%Z)) (ltac:(oD' 0x126a9c%Z)) (k+3)%Z.
mlbu (ltac:(oF' 0x126aa0%Z)) (ltac:(oD' 0x126aa0%Z)) (k+4)%Z. mlbu (ltac:(oF' 0x126aa4%Z)) (ltac:(oD' 0x126aa4%Z)) (k+5)%Z. mlbu (ltac:(oF' 0x126aa8%Z)) (ltac:(oD' 0x126aa8%Z)) (k+6)%Z. mlbu (ltac:(oF' 0x126aac%Z)) (ltac:(oD' 0x126aac%Z)) (k+7)%Z.
msb (ltac:(oF' 0x126ab0%Z)) (ltac:(oD' 0x126ab0%Z)) k ltac:(sbp). msb (ltac:(oF' 0x126ab4%Z)) (ltac:(oD' 0x126ab4%Z)) (k+1)%Z ltac:(sbp).
msb (ltac:(oF' 0x126ab8%Z)) (ltac:(oD' 0x126ab8%Z)) (k+2)%Z ltac:(sbp). msb (ltac:(oF' 0x126abc%Z)) (ltac:(oD' 0x126abc%Z)) (k+3)%Z ltac:(sbp).
mlbu (ltac:(oF' 0x126ac0%Z)) (ltac:(oD' 0x126ac0%Z)) (k+8)%Z. mlbu (ltac:(oF' 0x126ac4%Z)) (ltac:(oD' 0x126ac4%Z)) (k+9)%Z. mlbu (ltac:(oF' 0x126ac8%Z)) (ltac:(oD' 0x126ac8%Z)) (k+10)%Z. mlbu (ltac:(oF' 0x126acc%Z)) (ltac:(oD' 0x126acc%Z)) (k+11)%Z.
msb (ltac:(oF' 0x126ad0%Z)) (ltac:(oD' 0x126ad0%Z)) (k+4)%Z ltac:(sbp). msb (ltac:(oF' 0x126ad4%Z)) (ltac:(oD' 0x126ad4%Z)) (k+5)%Z ltac:(sbp).
msb (ltac:(oF' 0x126ad8%Z)) (ltac:(oD' 0x126ad8%Z)) (k+6)%Z ltac:(sbp). msb (ltac:(oF' 0x126adc%Z)) (ltac:(oD' 0x126adc%Z)) (k+7)%Z ltac:(sbp).
mlbu (ltac:(oF' 0x126ae0%Z)) (ltac:(oD' 0x126ae0%Z)) (k+12)%Z. mlbu (ltac:(oF' 0x126ae4%Z)) (ltac:(oD' 0x126ae4%Z)) (k+13)%Z. mlbu (ltac:(oF' 0x126ae8%Z)) (ltac:(oD' 0x126ae8%Z)) (k+14)%Z. mlbu (ltac:(oF' 0x126aec%Z)) (ltac:(oD' 0x126aec%Z)) (k+15)%Z.
stepn (ltac:(oF' 0x126af0%Z)) (ltac:(oD' 0x126af0%Z)).
msb (ltac:(oF' 0x126af4%Z)) (ltac:(oD' 0x126af4%Z)) (k+8)%Z ltac:(sbp). msb (ltac:(oF' 0x126af8%Z)) (ltac:(oD' 0x126af8%Z)) (k+9)%Z ltac:(sbp).
msb (ltac:(oF' 0x126afc%Z)) (ltac:(oD' 0x126afc%Z)) (k+10)%Z ltac:(sbp). msb (ltac:(oF' 0x126b00%Z)) (ltac:(oD' 0x126b00%Z)) (k+11)%Z ltac:(sbp).
stepn (ltac:(oF' 0x126b04%Z)) (ltac:(oD' 0x126b04%Z)).
msb (ltac:(oF' 0x126b08%Z)) (ltac:(oD' 0x126b08%Z)) (k+12)%Z ltac:(sbp). msb (ltac:(oF' 0x126b0c%Z)) (ltac:(oD' 0x126b0c%Z)) (k+13)%Z ltac:(sbp).
msb (ltac:(oF' 0x126b10%Z)) (ltac:(oD' 0x126b10%Z)) (k+14)%Z ltac:(sbp). msb (ltac:(oF' 0x126b14%Z)) (ltac:(oD' 0x126b14%Z)) (k+15)%Z ltac:(sbp).
stepn (ltac:(oF' 0x126b18%Z)) (ltac:(oD' 0x126b18%Z)).
mk_eq. apply mst_refl.
- post.
Qed.
Lemma t4_run : ltac2:(TCodec.tc2 tcn__AsanMemcpyMISKB0 "SJ&6y5'Q2yR0%211%5241'5'2&;r4(Q0+1(0%33<21%6251r3%93<21r5+;%93B17%<231&:vO%2218%A3D41r6+=%A3J1?%D231vF%921E%H3K31r7+<%H3Q11F%K231&Q1%12Q2L%O3Q231'1&Az%221I&B&C+2+R0%3221%52O1%:271%:29B'4&@+4%22F1%Q@3QA1>%QA3QB23&?r8%2216vJ%E221%G261%<281'3'9&>&<&8r<+QTjR<%QM3R41QK/01R4&7vIvEr:%443Q@21vN%<5;:721r1+QTjm4%R83R?1R6/01R?r9%Q121Q0%M2:1%>4=QJ<1%E5D851:%H3G:1%RB2:R=r;%RE3RH21%RE2=R:%R92R88%RH3RK21%RH2@R5%R<2R4;%RK3RN21%RK2CR1%R02S1@%RN3S121&=%12Q2G%R1231%R2271%R32;1%R42?1%R52C1qQJS81%Q>2S91p0Q@1p0QN1p0R01p0R<1p0RD1p0RL1p0S51pQBS@1pQ@SA1pQLSD1pQHSD1").
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn (ltac:(oF' 0x12684c%Z)) (ltac:(oD' 0x12684c%Z)).
stepb_ft (ltac:(oF' 0x126850%Z)) (ltac:(oD' 0x126850%Z)) ltac:(cond).
stepn (ltac:(oF' 0x126854%Z)) (ltac:(oD' 0x126854%Z)).
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126b78 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x12684c%Z)) (ltac:(oD' 0x12684c%Z)).
stepb_tk (ltac:(oF' 0x126850%Z)) (ltac:(oD' 0x126850%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Lemma b8_tail : ltac2:(TCodec.tc2 tcn__AsanMemcpyMISKB0 "SJ&6y5'Q2yR0%211%5241'5'2&;r4(Q0+1(0%33<21%6251r3%93<21r5+;%93B17%<231&:vO%2218%A3D41r6+=%A3J1?%D231vF%921E%H3K31r7+<%H3Q11F%K231&Q1%12Q2L%O3Q231'1&Az%221I&B&C+2+R0%3221%52O1%:271%:29B'4&@+4%22F1%Q@3QA1>%QA3QB23&?r8%2216vJ%E221%G261%<281'3'9&>&<&8r<+QTjk@%QM3R41QK/01R4&7vIvEr:%443Q@21vN%<5;:721r1+QTjm4%R83R?1R6/01R?r9%Q121Q0%M2:1%>4=QJ<1%E5D851:%H3G:1%RB2:R=r;%RE3RH21%RE2=R:%R92R88%RH3RK21%RH2@R5%R<2R4;%RK3RN21%RK2CR1%R02S1@%RN3S121&=%12Q2G%R1231%R2271%R32;1%R42?1%R52C1qQJS81%Q>2S91p0Q@1p0QN1p0R01p0R<1p0RD1p0RL1p0S51pQBS@1pQ@SA1pQLSD1pQHSD1").
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn (ltac:(oF' 0x126b70%Z)) (ltac:(oD' 0x126b70%Z)).
stepb_tk (ltac:(oF' 0x126b74%Z)) (ltac:(oD' 0x126b74%Z)) ltac:(cond).
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126b78 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x126b70%Z)) (ltac:(oD' 0x126b70%Z)).
stepb_ft (ltac:(oF' 0x126b74%Z)) (ltac:(oD' 0x126b74%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Lemma t8_run : ltac2:(TCodec.tc2 tcn__AsanMemcpyMISKB0 "T7&6y5'Q2yR0%211%5241'5'2&;r4(Q0+1(0%33<21%6251r3%93<21r5+;%93B17%<231&:vO%2218%A3D41r6+=%A3J1?%D231vF%921E%H3K31r7+<%H3Q11F%K231&Q1%12Q2L%O3Q231'1&Az%221I&B&C+2+R0%3221%52O1%:271%:29B'4&@+8%22F1%Q@3QA1>%QA3QB23%6221r8+4%8221%QF3QG1D%QG3QH23%<221&?r:r9%?21>%4231%A23:%6221vJ%Q0221'3'9&>&<&8r>+QTjR4%R63R=1R4/01R=&7vIvEr<%443QI21vN%<5;:721r1+QTjm4%RA3RH1R?/01RHr;%Q:21Q9%O2:1%Q<23Q5%Q1221%@4?R5>1%G5F:71<%J3I<1%RM2<RHr=%S03S321%S02?RE%RD2RC8%S33S621%S32BR@%RG2R?;%S63S921%S62ER<%R;2S<B%S93S<21&=%12Q4I%R<231%R=271%R>2;1%R?2?1%R@2C1qQJSC1%Q@2SD1p0QB1p0QL1p0R31p0R;1p0R=1p0RI1p0S11p0S91p0SB1pQBSM1pQ@SN1pQLT11pQHT11").
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
-
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x12684c : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x126844%Z)) (ltac:(oD' 0x126844%Z)).
stepb_ft (ltac:(oF' 0x126848%Z)) (ltac:(oD' 0x126848%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126b24 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x126844%Z)) (ltac:(oD' 0x126844%Z)).
stepb_tk (ltac:(oF' 0x126848%Z)) (ltac:(oD' 0x126848%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126b70 : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Lemma b16_tail : ltac2:(TCodec.tc2 tcn__AsanMemcpyMISKB0 "T7&6y5'Q2yR0%211%5241'5'2&;r4(Q0+1(0%33<21%6251r3%93<21r5+;%93B17%<231&:vO%2218%A3D41r6+=%A3J1?%D231vF%921E%H3K31r7+<%H3Q11F%K231&Q1%12Q2L%O3Q231'1&Az%221I&B&C+2+R0%3221%52O1%:271%:29B'4&@+8%22F1%Q@3QA1>%QA3QB23%6221r8+4%8221%QF3QG1D%QG3QH23%<221&?r:r9%?21>%4231%A23:%6221vJ%Q0221'3'9&>&<&8r>+QTjhL%R63R=1R4/01R=&7vIvEr<%443QI21vN%<5;:721r1+QTjm4%RA3RH1R?/01RHr;%Q:21Q9%O2:1%Q<23Q5%Q1221%@4?R5>1%G5F:71<%J3I<1%RM2<RHr=%S03S321%S02?RE%RD2RC8%S33S621%S32BR@%RG2R?;%S63S921%S62ER<%R;2S<B%S93S<21&=%12Q4I%R<231%R=271%R>2;1%R?2?1%R@2C1qQJSC1%Q@2SD1p0QB1p0QL1p0R31p0R;1p0R=1p0RI1p0S11p0S91p0SB1pQBSM1pQ@SN1pQLT11pQHT11").
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
- eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x12684c : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x126b1c%Z)) (ltac:(oD' 0x126b1c%Z)).
stepb_tk (ltac:(oF' 0x126b20%Z)) (ltac:(oD' 0x126b20%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126b24 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x126b1c%Z)) (ltac:(oD' 0x126b1c%Z)).
stepb_ft (ltac:(oF' 0x126b20%Z)) (ltac:(oD' 0x126b20%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126b70 : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Lemma t16_run : ltac2:(TCodec.tc2 tcn__AsanMemcpyMISKB0 "SL&6y5'Q2yR0%211%5241'5'2&;r4(Q0+1(0%33<21%6251r3%93<21r5+;%93B17%<231&:vO%2218%A3D41r6+=%A3J1?%D231vF%921E%H3K31r7+<%H3Q11F%K231&Q1%12Q2L%O3Q231'1&Az%221I&B+Q0%22L1%7241%726?&?r8&@+@%22D1%5241+8%52G1%8231+4%82J1%;231vJ%E221'3'9&>&<&8r<+QTjQL%QK3R21QI/01R2&7vIvEr:%443Q>21vN%<5;:721r1+QTjm4%R63R=1R4/01R=r9%Q121Q0%Q42:1%Q323O%Q6221%Q525N%Q8221%B4AQL@1%I5H<91>%L3K>1%RD2>R?r;%RG3RJ21%RG2AR<%R;2R:8%RJ3RM21%RJ2DR7%R>2R6;%RM3S021%RM2GR3%R22S3D%S03S321&=%12Q6K%R3231%R4271%R52;1%R62?1%R72C1qQJS:1%QB2S;1p0QD1p0R31p0R51p0R>1p0RF1p0RN1p0S71pQBSB1pQ@SC1pQLSF1pQHSF1").
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
-
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126844 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x12683c%Z)) (ltac:(oD' 0x12683c%Z)).
stepb_ft (ltac:(oF' 0x126840%Z)) (ltac:(oD' 0x126840%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126a90 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0x12683c%Z)) (ltac:(oD' 0x12683c%Z)).
stepb_tk (ltac:(oF' 0x126840%Z)) (ltac:(oD' 0x126840%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans ASEGS0 _ (fun r => mkst r (0x126b1c : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
End MIS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
