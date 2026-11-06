(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums L5Defs L5Core L5CoreKit Js0Sums.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSrcSMemmove () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSums.APSX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5CoreKit.L5K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSrcSMemmove.PMCP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSrcSMemmove.PMCP.Generic."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0CPY"; "1Some"; "1length"; "1list"; "1nat"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M"; "0M3"; "0R"]; ["0R3"; "5copy_spec"; "6wbytes"; "7msteps"; "8CS"; "9defined"; "9ra_ok"; "9writable"; ";copy1_spec"; ":copy1_spec"; "<FPState"; "<getr"; "<mkst"; "<rdn"; "<seg_rom"; "<v_add"]; ["<v_slli"; "<v_sub"; "=mem_grows"; ">loaded_segments"; "?In"; "@add"; "@le"; "@lt"; "@modulo"; "@mul"; "@of_nat"; "@pow"; "@sub"; "0a"; "0bs"; "0d"]; ["0dst"; "0fx"; "0i"; "0k"; "0n"; "0pc"; "0r"; "0s"; "0segs"; "0src"; "AZ_to_bv"; "Abv"; "Abv_unsigned"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation RSEGS := Plain.M.loaded_segments.
Module PMCP.
Section Generic.
Variable segs : list Segment.
Lemma rdn_of_defined : ltac2:(TCodec.tc2 tcn__PmSrcSMemmove "QJ'QKyR0%211'5y8%511%311p051'4';&Q6zr1%3221&Q5r2&Q:r3%211%5241&Q;+2+R0%3221%>251&Er5r4%<11%433<1'8'3%11K'6'7%Q013&MvQHr7&QJ%12Q7>r6%645421(1%12<Q0%;3:31&2%12Q:Q3%>3Q817%@241qRNB1%E2C1p0G1p0M1p0Q91pRLQ>1pS8Q@1pLQB1").
Proof. intros M.
induction k as [|k IH]; intros a Ha Hk D. { exists []. split; reflexivity. }
cbn [rdn]. pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|congruence].
destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & RB & LB).
{ intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply D. lia. }
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1%bv : bv 64)) with 1. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity. }
rewrite RB. exists (b :: bs). split; [reflexivity| cbn; lia].
Qed.
Lemma wbytes_defined : ltac2:(TCodec.tc2 tcn__PmSrcSMemmove "Q:'QKyR0%211'5y8%511%311p051';'3%115&Q6zr2%3221&Q5r3&Q:&2%12>6%311%6251&Q;+2+R0%3221%?251&E&Br5&QJr4%22O1%5341A%@2MB%B11%93351p0;1p0H1pRNM1pS2Q01pLQ21").
Proof. intros M dst bs.
intros Hd Hn i Hi.
replace (dst + i) with (bv_unsigned (Z_to_bv 64 dst) + Z.of_nat (Z.to_nat i)) by (rewrite L5.unsigned_lit by lia; lia).
rewrite AX2S.wbytes_nth; [discriminate| rewrite L5.unsigned_lit by lia; lia| lia].
Qed.
Lemma wbytes_out : ltac2:(TCodec.tc2 tcn__PmSrcSMemmove "QK'QKyR0%211'5y8%511%311p051';'3%115'6&Q6zr3%3221&Q7&Q;+2+R0%3221%5271%;271&Q5r4&Q:&2%12F=%311%6251%B21:&9r6%E219r5%92N1%;11%>251%F2>1%L261%911'7&Br8&QJr7%22Q=1%32Q>=%6452@1%612%93Q<21p0;1p0N1p0G1p0Q01pRLQ?1pRNQ>1pS2QA1pLQC1").
Proof. intros M dst bs a.
intros Hd Hn Ha Hout. destruct (Z_lt_le_dec a dst) as [Lo|Hi].
- apply wbytes_below; rewrite !L5.unsigned_lit by lia; lia.
- apply wbytes_above. rewrite !L5.unsigned_lit by lia. lia.
Qed.
Definition copy1_spec (pc : Z) : Prop :=
forall (fx : FPState) mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
1 <= n -> length bs = Z.to_nat n ->
rdn segs mem0 src (length bs) = Some bs ->
store_ok segs mem0 dst (length bs) = true ->
(bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
bv_unsigned src + n < 2 ^ 63 -> bv_unsigned dst + n < 2 ^ 63 ->
ret_ok ret -> getr regs 1%bv = ret ->
getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
exists regs',
msteps segs (@mkst fx regs (Z_to_bv 64 pc) mem0 (seg_rom segs)) (@mkst fx regs' ret (wbytes mem0 dst bs) (seg_rom segs))
/\ APSX.kept_ok regs regs' /\ getr regs' 10%bv = dst.
Lemma copy1_of_copy_spec : ltac2:(TCodec.tc2 tcn__PmSrcSMemmove "<';'J&Ar1vQHr2%43321pS461&H%114p031pS<;1").
Proof. intros pc.
intros C fx mem0 dst src n bs regs ret Hn LEN RD ST AP Hs Hd RET R1 R10 R11 R12.
apply (C fx mem0 dst src n bs regs ret); try assumption; lia.
Qed.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).
Lemma copy_run : ltac2:(TCodec.tc2 tcn__PmSrcSMemmove "U9';&Hr1%211'J&<y5'QKyR0%211%5241'5y8%611%311p061'7&Kr6&QJ&Q:u:%211%42A1%7261r4%72B1%;3B31r7u;%:11%<2I1%?241%A3H17r8u<%@11%B2O1%E241%G3N1=r9u1%F11%H2Q51%K241%M3Q41C&Fr5%211&Q6+1%221Gzr:%5221&Q7&Q5r;%221B&Q;+2+QO%3221%8251%?2<7r<%:219%<215':r>%>215r=%G221%A228%I215%7231&GvQHr@r?%443219&ErA%2314>'8'6'C&LrFrErH%R82RC1rD&N%11A%8576431r2%R>2RIC%;5:21S04%=3F41&Q2%129S3%QE2QBS4+R0%Q=2Q<1%QB2S71%E241&9%QK2C<rC%QF2E1%QH2?1%K241%611r3%S02S;1%RK11rG%113%S73S931p071p0?1pRLSJ1%Q:3SI>Q9'4&Q4&D%233SM1%S<1Q0%S>2SK1%SA2S91%SB2>2%SD3SK21p061pS6:1%SF2Q7S@%SE2T0K%SI3T021%QE241%QF2@1%QG2B1%QH2Q81%QI2Q;1qNT01%QL2T11qQ2T71%QN2T81p0R01p0R41p0R:1p0RC1p0RG1p0RI1p0S31p0S71p0S;1p0S?1p0SF1p0SM1p0T41pS>U01pS:U11pSDU21pS2U31pLTE1pQ0TK1pS4U21p2U41pS<U81").
Proof. intros pc CPY fx R M dst src n r.
intros H10 H11 H12 H1 RA Hn Hd Hdn Hs Hsn AP W D.
destruct (rdn_of_defined M (Z.to_nat n) src Hs ltac:(lia)) as (bs & RD & LEN). { rewrite Z2Nat.id by lia. exact D. }
destruct (CPY fx M (Z_to_bv 64 dst) (Z_to_bv 64 src) n bs R (Z_to_bv 64 r) Hn LEN
ltac:(rewrite LEN; exact RD)
ltac:(rewrite LEN; replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) by (f_equal; lia); apply W; lia)
ltac:(rewrite !L5.unsigned_lit by lia; lia) ltac:(rewrite L5.unsigned_lit by lia; lia) ltac:(rewrite L5.unsigned_lit by lia; lia)
(L5K.ret_ok_lit r RA) H1 H10 H11 H12) as (R3 & MS & KO & A10).
exists R3, (wbytes M (Z_to_bv 64 dst) bs). split; [exact MS|]. split; [apply wbytes_grows|].
split. { intros a Ha Hout. apply wbytes_out; [lia| rewrite LEN; lia| exact Ha| rewrite LEN, Z2Nat.id by lia; exact Hout]. }
split. { pose proof (wbytes_defined M dst bs Hd ltac:(rewrite LEN; lia)) as X. rewrite LEN, Z2Nat.id in X by lia. exact X. }
split; [intros i Hi; apply (L5K.kept_ok_index R R3 i KO Hi)| exact A10].
Qed.
End Generic.
End PMCP.
Module PMCPS.
Open Scope bv_scope.
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma a4_val : ltac2:(TCodec.tc2 tcn__PmSrcSMemmove "Q3';'6&Q6+1r1%3221&Q7&Q;+2+QN%3221%5271%;271'7&QLyR0&Q1&QJz%2241&Q0r2%5271%321D%8251%;2:1&Q<+R0%E2D1&Q9%12F9%5231%C3Q071p0E1pS:Q21").
Proof. intros n.
intros Hn. unfold v_sub, v_slli. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite (Z.mod_small n) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
rewrite (Z.mod_small 0) by lia. rewrite (Z.mod_small (n * 2)) by lia.
replace (0 - n * 2)%Z with (2 ^ 64 - 2 * n + (-1) * 2 ^ 64)%Z by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma a3_val : ltac2:(TCodec.tc2 tcn__PmSrcSMemmove "QA'QKyR0%211';&Q6+1r1%3221&Q7&Q5&QLr4%22;1r2%5221&Q;+2+QO%3221%;251r3%<291%>214'7&Q1r5&O&QJ%12KAr6%4221%7261%F2O1&Q8&Q<%I2Q2:%J2Q37%3221%421K+R0%I2H1%8231%C3Q7:1p0E1p0I1p0Q61pS:Q;1pS@Q=1pS0Q>1").
Proof. intros d s n.
intros Hn Hdn Hsn. pose proof (bv_unsigned_in_range _ d) as Bd. pose proof (bv_unsigned_in_range _ s) as Bs.
unfold v_sub, v_add. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z in *.
rewrite (Z.mod_small n) by lia. rewrite (Z.mod_small (n + bv_unsigned d)) by lia.
f_equal. lia.
Qed.
Theorem memmove_disjoint : ltac2:(TCodec.tc2 tcn__PmSrcSMemmove "4&I&Q3+eU[4%3221").
Proof.
intros fx0 mem0 dst src n bs regs ret Hn LEN RD ST AP Hs Hd RET R1 R10 R11 R12.
pose proof (bv_unsigned_in_range _ dst) as Bd. pose proof (bv_unsigned_in_range _ src) as Bs.
change (bv_modulus 64) with (2 ^ 64)%Z in Bd, Bs.
assert (NE : c_eq (getr regs 10) (getr regs 11) = false).
{ rewrite R10, R11. unfold c_eq. apply bv_eqb_neq. intros E. rewrite E in AP. lia. }
assert (GE : c_ltu (v_sub (Z_to_bv 64 0) (v_slli (Z_to_bv 64 n) 1)) (v_sub src (v_add (Z_to_bv 64 n) dst)) = false).
{ unfold c_ltu, bv_ltu. apply Z.ltb_ge. rewrite a4_val by lia.
rewrite a3_val by lia.
destruct AP as [A|A].
- rewrite Z.mod_small by lia. lia.
- replace (bv_unsigned src - bv_unsigned dst - n)%Z with (2 ^ 64 + bv_unsigned src - bv_unsigned dst - n + (-1) * 2 ^ 64)%Z by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
destruct (Js0Sums.src0_copy_spec_memcpy fx0 mem0 dst src n bs
(regupd (regupd (regupd (regupd regs 13 (v_add (getr regs 12) (getr regs 10))) 14 (v_slli (getr regs 12) 1))
13 (v_sub (getr regs 11) (v_add (getr regs 12) (getr regs 10)))) 14 (v_sub (Z_to_bv 64 0) (v_slli (getr regs 12) 1)))
ret ltac:(lia) LEN RD ST AP ltac:(lia) ltac:(lia) RET) as (regs' & MS & KO & A10).
1-4: gres; assumption.
exists regs'. split; [|split; [|exact A10]].
- stepb_ft (ltac:(oF' 0xa9564%Z)) (ltac:(oD' 0xa9564%Z)) ltac:(exact NE).
stepn (ltac:(oF' 0xa9568%Z)) (ltac:(oD' 0xa9568%Z)).
stepn (ltac:(oF' 0xa956c%Z)) (ltac:(oD' 0xa956c%Z)).
stepn (ltac:(oF' 0xa9570%Z)) (ltac:(oD' 0xa9570%Z)).
stepn (ltac:(oF' 0xa9574%Z)) (ltac:(oD' 0xa9574%Z)).
stepb_tk (ltac:(oF' 0xa9578%Z)) (ltac:(oD' 0xa9578%Z)) ltac:(rewrite ?R10, ?R11, ?R12; exact GE).
stepn (ltac:(oF' 0xa95b8%Z)) (ltac:(oD' 0xa95b8%Z)).
lazymatch goal with |- msteps _ (mkst _ ?p _ _) _ => replace p with (Z_to_bv 64 0xa9160) by (apply bv_eq; reflexivity) end.
exact MS.
- intros r Hr0 Hr. rewrite (KO r Hr0 Hr).
assert (r <> 13 /\ r <> 14) as (N13 & N14).
{ split; intros ->; apply Hr; vm_compute; tauto. }
rewrite !getr_other by assumption. reflexivity.
Qed.
End FPX_1.
Lemma memcpy_copy1 : ltac2:(TCodec.tc2 tcn__PmSrcSMemmove "4&I&Q3+eT[0%3221").
Proof. apply PMCP.copy1_of_copy_spec. exact Js0Sums.src0_copy_spec_memcpy. Qed.
Definition memcpy_run := PMCP.copy_run RSEGS 0xa9160 memcpy_copy1.
Definition memmove_run := PMCP.copy_run RSEGS 0xa9564 (fun fx => @memmove_disjoint fx).
End PMCPS.
