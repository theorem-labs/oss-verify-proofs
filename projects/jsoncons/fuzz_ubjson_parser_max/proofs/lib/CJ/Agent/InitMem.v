(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import StrFun.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_InitMem () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.InitMem.CEIL_WRAP_1.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2not"; "3N"; "3Z"]; ["4word_le8"; "5wview"; "6rw_bytes_b"; "7u64s"; "8CB"; "8cell"; "8cells_bytes"; "8cells_size"; "8cells_wf"; "9le8"; "9mrd"; "9wa"; ":rw_cells"; ";flat_map"; ";nth_error"; "<add"]; ["<le"; "<lt"; "<of_N"; "<of_nat"; "<pow"; "<shiftr"; "0a"; "0b"; "0bs"; "0cs"; "0cs'"; "0i"; "0k"; "0m"; "0segs"; "=Z_to_bv"]; ["=bv"; "=bv_extract"; "=bv_unsigned"; "0v"; "0ws"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma extract_byte_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_InitMem "F'Q@yR0%211'>'<y8%611&QAr1r2%349251&Q?&Q5&QB%12=5&Q2%118%5231%72=1%?3=91pRJA1pS8C1").
Proof. intros v k. apply bv_eq. rewrite bv_extract_unsigned, Z_to_bv_unsigned. reflexivity. Qed.
Lemma word_le8_le8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_InitMem "?'Q@yR0%211'<'6y8%611%311&@r1%211&I%113%:3631pS8<1").
Proof.
intros v. unfold word_le8, le8, word_to_le_bytes. cbn [Z_to_le_bytes].
rewrite !extract_byte_eq. rewrite !Z.shiftr_shiftr by lia. cbn [Z.of_N Z.add].
rewrite Z.shiftr_0_r. reflexivity.
Qed.
Lemma flat_map_word_le8 : ltac2:(TCodec.tc2 tcn__CJ_Agent_InitMem "A'6'Q@yR0%211%411'<y8%611%811&M&@r1%349521&C%113%:3731pS:<1").
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [flat_map u64s]. rewrite word_le8_le8, IH. reflexivity. Qed.
Section WithSegs.
Variable segs : list Segment.
Fixpoint rw_bytes_b (A : Z) (bs : list byte) : bool :=
match bs with
| [] => true
| b :: bs' =>
match seg_rom segs (wa A), wview segs (fun _ => None) (wa A) with
| Some b', Some _ => bv_eqb b b' && rw_bytes_b (A + 1) bs'
| _, _ => false
end
end.
Lemma rw_bytes_b_sound : ltac2:(TCodec.tc2 tcn__CJ_Agent_InitMem "RF'6'Q@y8%211%411'?yR0%611'9%116p031'<'3&Br2r3%3221(:%73621';&Q0r4&QBr1%22B1%5241&Q1&O&Q3&5r5%22L1%411%62<1%82:1%@2:1%?1F(1%11Q3%L3N31p051pR>Q21z%G21Fr6%@2Q:1%B11%D2A1&Q4+2+R0%3221%Q0251'7&Nr9%23QE1Q:(2%12QGQ3%Q@3QB31&JvQ>r8&K%Q41QA%Q62:1%311%73651%;2R1QF%QJ3QL21&=&A%13;:6%QN3R01Q3%411%QH261p0A1pR@R:1pRHI1p0K1p0Q51p0Q81p0R01pRLR91p2R?1pRBRA1").
Proof.
induction bs as [|b0 bs IH]; intros A m Hb Hm HA Hl i b Hn; [destruct i; discriminate|].
cbn [rw_bytes_b] in Hb.
destruct (seg_rom segs (wa A)) as [b'|] eqn:Er; [|discriminate].
destruct (wview segs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
apply andb_prop in Hb. destruct Hb as [Hbe Hb]. unfold bv_eqb in Hbe. apply Z.eqb_eq in Hbe. apply bv_eq in Hbe. subst b'.
cbn [length] in Hl, Hm.
destruct i as [|i].
- cbn in Hn. injection Hn as ->. rewrite Z.add_0_r.
assert (Hnone : m (wa A) = None). { apply Hm. rewrite wa_unsigned by lia. lia. }
split. { unfold mrd. rewrite Hnone. exact Er. }
unfold wview in *. rewrite Hnone. intros C. rewrite C in Ew. discriminate.
- cbn in Hn. replace (A + Z.of_nat (S i))%Z with ((A + 1) + Z.of_nat i)%Z by lia.
apply (IH (A + 1)%Z m Hb); try lia; [|exact Hn]. intros a Ha. apply Hm. lia.
Qed.
Lemma rw_cells_image0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_InitMem "R8'Q@yR0%211'9y8%511%311p051'?'6%115';&Q0r3&QBr1%22?1%5241&Q1&O&Q3&5r2%22B1%411%62<1%82:1%@2:1'<r5%118(1%11K%53K31p071pR>Q11'3&B%12I@(:%<3421zr4%O221%G2Q72%I11%K2A1&Q4+2+R0%3221%Q7251&LvQ>r7r6(4'E(D%Q62QFN%221O(8%115%73631%<4;:91p0>1p0G1p0K1p0Q11pRBQK1p2QN1pRLR01").
Proof.
intros m A bs Hm Hb HA Hl. pose proof (rw_bytes_b_sound bs A m Hb Hm HA Hl) as G.
split; [split|].
- cbn. split; [reflexivity| exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [lia|].
intros i Hi. destruct (nth_error bs i) as [b|] eqn:E. { apply (proj1 (G i b E)). } apply nth_error_None in E. lia.
- cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E. { apply (proj2 (G _ b E)). } apply nth_error_None in E. lia.
Qed.
Lemma rw_cells_recast : ltac2:(TCodec.tc2 tcn__CJ_Agent_InitMem "Q;'Q@yR0%211'9y8%511%311p051'?'6'E%211&LvQ>r4r3r2%544321&H%113'<%<1@&F%118%21:%53421'7&G%11>r5%311%;3531r8r7%F4E215p041p0;1p0B1p0E1pRFL1pRDM1p2Q11pRLQ31").
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
End WithSegs.
End CEIL_WRAP_1.
