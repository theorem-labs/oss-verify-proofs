(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SumsLib Sums_codeK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanIMemcpyKB0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanIMemcpyKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SumsLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1list"; "1nat"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "5asan_imemcpy_entry"; "5asanreflect_fx"; "5imemcpy_clob"; "5imemcpy_words"; "6wbytes"; "7msteps"; "8at_"]; ["8regs_agree"; "8ret_ok"; "9getr"; "9mkst"; ":code_at"; ":cpyH"; ":memk"; ";loaded_segments"; "<In"; "=le"; "=lt"; "=of_nat"; "=sub"; "0base"; "0bs"; "0dst"]; ["0i"; "0k"; "0mem0"; "0n"; "0r"; "0regs"; "0regs'"; "0ret"; "0rom"; "0segs"; "0src"; ">BV"; ">Z_to_bv"; ">bv"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition imemcpy_words : list (bv 32) :=
[W_1037ac; W_1037b0; W_1037b4; W_1037b8; W_1037bc; W_1037c0; W_1037c4; W_1037c8; W_1037cc].
Definition imemcpy_clob : list reg := [11; 12; 13; 14].
Section IMEMCPY.
Variable segs : list Segment.
Variable base : word.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 imemcpy_words.
Hypothesis HOK : cpyH segs mem0 dst src n bs.
#[local] Abbreviation MK := (memk mem0 dst bs).
#[local] Abbreviation B := (b_ bs).
#[local] Abbreviation CL := (fun r => In r imemcpy_clob).
Let Hn0 : (0 <= n)%Z := cHn _ _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := cHnws _ _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := cHnwd _ _ _ _ _ _ HOK.
Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at imemcpy_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & _).
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vn.
Ltac msb F D kk :=
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | apply sb_val_b | lia | lia]
| step_simpl]; vn.
Lemma imemcpy_loop : ltac2:(TCodec.tc2 tcn__AsanIMemcpyKB0 "S1'1&8y5'Q=yR0%211%5241'7&Ar2%211'5&Br4(Q;+1(3%33?21%6251r3%93?21r5+;%93E17%<231&?vQ:%2218%A3G41r6+=%A3M1?%D231vO%921E%H3N31r7+<%H3Q41F%K231vQ3%@281%O3Q531'4&Iz%221A&J%12C8%6231&Kr:%211&L%12>Q7%221C%Q=3QA41'6'>vQ9&C&:r;vM%Q721K&FvQ2vNr9%443Q421vQ8%;5:9721r1%847Q86Q1%>5=2G14%A3@41&@%R:1R;&H&;%23381qR:41%631D:%Q8281qR>R>1%L2R?1p0N1p0Q61p0Q>1p0QF1p0QN1p0R71p0RB1pR4RF1pR@RI1pR<RI1pR2S01").
Proof.
get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
-
eexists. split.
+ mlbu C12 D_1037b8 k.
msb C16 D_1037bc k.
an C20 D_1037c0.
an C24 D_1037c4.
ab_ft C28 D_1037c8 ltac:(condz).
aret C32 D_1037cc ret.
replace (k + 1)%Z with n by lia. apply mst_refl.
+ unfold imemcpy_clob. solve_regs_agree.
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
/\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
+ eexists. split.
* mlbu C12 D_1037b8 k.
msb C16 D_1037bc k.
an C20 D_1037c0.
an C24 D_1037c4.
ab_tk C28 D_1037c8 ltac:(condz).
apply mst_refl.
* post. unfold imemcpy_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
Theorem imemcpy_run : ltac2:(TCodec.tc2 tcn__AsanIMemcpyKB0 "R<&8y5'Q=yR0%211%5241&Ar1%211'5&Br3(Q;+1(3%33>21%6251r2%93>21r4+:%93D17%<231vO%?3D21r5+;%?3J1=%B231vQ:%E3J21r6+<%E3Q01C%H231&Q<vQ3%22Q21%M3Q241'6'4'>vQ9&C&:r8&?vMz%3221vQ2vQ8%9587321r7&=vN%236Q11%>5=QB416%A3@61&@%QJ1QK&H&;%233QH1qR:41%631DQJ%J281qR>QN1%M2QO1p0O1p0Q81p0Q?1p0QF1p0R11pR@R61pR<R61").
Proof.
get_code. intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
rewrite <- (memk_n _ _ _ _ _ _ HOK). change mem0 with (MK 0).
destruct (Z.eq_dec n 0) as [Hz|Hnz].
-
eexists. split.
+ ab_tk C0 D_1037ac ltac:(condz).
aret C32 D_1037cc ret.
rewrite Hz. apply mst_refl.
+ apply regs_agree_refl.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
/\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
+ eexists. split.
* ab_ft C0 D_1037ac ltac:(condz).
av C4 D_1037b0 (at_ dst n) ltac:(apply v_add_at; lia).
an C8 D_1037b4.
apply mst_refl.
* post; rewrite ?at_0; try reflexivity. unfold imemcpy_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (imemcpy_loop (Z.to_nat (n - 1)) r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End IMEMCPY.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
Definition asan_imemcpy_entry : word := 0x8ad5c.
Lemma asan_imemcpy_code : ltac2:(TCodec.tc2 tcn__AsanIMemcpyKB0 "6&D&G&9z&<%544321").
Proof. unfold imemcpy_words. code_at_vm. Qed.
Theorem asan_imemcpy : ltac2:(TCodec.tc2 tcn__AsanIMemcpyKB0 "RI'Q=yR0%211'2y8%511%311p051'7'0%115&8y5%221;'E&Gr8r7r6r5r4%76654321&Ar2%211'5&B(Q;+1(3%33B21%52;1r3%83O21+:%83G16%:2A1r:%=3Q421+;%=3L1;%?2G1%A3Q815+<%A3Q01?%C2L1&Q<%12Q>:%G3Q>31'6'4'>&C&:r9&9r?%554321Dr1&=r>r;%33621%;5:5Q?1J%=3QA71&@%R21QF&H&;%233;1qR:41%631A=%F281qR>QL1%I2QM1p0K1p0Q21p0Q71p0Q=1p0QG1p0QK1pR@R?1pR<R51pRBR<1pQNR:1pR8R=1pRFRD1pR0RE1pR6RA1").
Proof.
intros mem0 dst src n bs rom regs ret HOK.
rewrite <- (at_0 asan_imemcpy_entry).
apply (imemcpy_run _ _ mem0 dst src n bs rom asan_imemcpy_code HOK).
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
