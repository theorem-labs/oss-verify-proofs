(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim Frame RefMemcpyLib Ju0MemcpyBase Ju0Memchr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0Strnlen () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0Strnlen.FPX_1.SNL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.musl.Ju0Memchr."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2or"]; ["3Z"; "0K"; "4store_ok"; "4word_to_le_bytes"; "5bvmap"; "6msteps"; "7frame_mod"; "8ret_ok"; "9mem1"; ":getr"; ":mkst"; ":rdn"; ";keeps_cs"; "<mchrH"; "=loaded_segments"; ">add"]; [">le"; ">lt"; ">of_nat"; ">sub"; "0a"; "0buf"; "0fx"; "0mem"; "0mem'"; "0n"; "0ra"; "0regs"; "0regs'"; "0ret"; "0rom"; "0s"]; ["0s0"; "0s1"; "0sp"; "?BV"; "?Z_to_bv"; "?bv"; "?bv_unsigned"; "0v"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Section SNL.
Variable mem : word -> option byte.
Variables s sp : word.
Variable buf : list byte.
Variables K n : Z.
Variable rom : word -> option byte.
Hypothesis HOK : mchrH mem s buf K n.
Hypothesis HsK : (0 < bv_unsigned s + K)%Z.
Hypothesis Hstk : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true.
Hypothesis Hspr : (0x13ab0 <= bv_unsigned sp - 32)%Z.
Hypothesis Hdisj : (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32
\/ bv_unsigned sp <= bv_unsigned s)%Z.
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation W8 v := (word_to_le_bytes 8 v).
Definition mem1 (ra s0 s1 : word) : word -> option byte :=
wbytes (wbytes (wbytes mem (Z_to_bv 64 (usp - 8)) (W8 ra)) (Z_to_bv 64 (usp - 16)) (W8 s0))
(Z_to_bv 64 (usp - 24)) (W8 s1).
Lemma lenW8 : ltac2:(TCodec.tc2 tcn__Ju0Strnlen "?'QEyR0%211'='5&3y8%711&Cu8r1%3221%7251%:3914pS@<1").
Proof. intros v. apply length_N_to_le_bytes. Qed.
Lemma mem1_out : ltac2:(TCodec.tc2 tcn__Ju0Strnlen "Q4'QEyR0%211'?&Q1&QFr1%2261&Q3vQB%5291+H%4221%9261&Q0%1258%=231'='7y8%D11%311&Hr5r4r3r2%544321vQ7%113%=3931p0?1pR:N1pS4O1pS2Q01pRFQ11").
Proof.
clear HOK HsK Hstk Hdisj. intros ra s0 s1 a Ha. pose proof (u64_range sp). unfold mem1.
rewrite !wbytes_outside; rewrite ?lenW8; unfold in_rng; u_norm; try lia; reflexivity.
Qed.
Lemma HOK1 : ltac2:(TCodec.tc2 tcn__Ju0Strnlen "A'QEyR0%211'M&Hr3r2r1%43321vQ?vQ5vAvQ9%:554321pS4<1pS2=1pRF>1").
Proof.
intros ra s0 s1. pose proof (u64_range sp). pose proof (u64_range s). destruct HOK. split; try assumption.
- rewrite <- Hbuf. apply rdn_ext; [lia|]. intros x Hx. apply mem1_out. lia.
- intros i Hi. rewrite mem1_out; [apply Hro; exact Hi | u_norm; lia].
Qed.
Lemma frame1 : ltac2:(TCodec.tc2 tcn__Ju0Strnlen "O'QEyR0%211&FvQ7&Hr3r2r1%43321(2'9'@%22;1(8&QD&Q3&QFvQB%22B1+Q0%5221%72E1%94E;13(6%11<%@3=31%H3GB1pS4J1pS2K1pRFL1").
Proof.
clear HOK HsK Hstk Hdisj. intros ra s0 s1. pose proof (u64_range sp). split.
- intros a [Ha _]. unfold in_rng in Ha. revert Ha. u_norm. intros Ha. apply mem1_out. lia.
- unfold mem1. eapply mem_grows_trans; [| apply wbytes_grows].
eapply mem_grows_trans; [| apply wbytes_grows]. apply wbytes_grows.
Qed.
Lemma rd_ra : ltac2:(TCodec.tc2 tcn__Ju0Strnlen "Q3'QEyR0%211'='7'4y8%711%311%511&K&N&Hr3r2r1%43321&QD&Q3&QFvQB%22D1+8%5221%72G1u8%@4?:21(0&C%124@%32F1%L3F51pS4N1pS2O1pRFQ01").
Proof.
clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
apply rdn_wbytes_hit8. u_norm. lia.
Qed.
Lemma rd_s0 : ltac2:(TCodec.tc2 tcn__Ju0Strnlen "Q3'QEyR0%211'='7'4y8%711%311%511&K&N&Hr3r2r1%43321&QD&Q3&QFvQB%22D1+@%5221%72G1u8%@4?:21(0&C%124?%32F1%L3F51pS4N1pS2O1pRFQ01").
Proof.
clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
apply rdn_wbytes_hit8. u_norm. lia.
Qed.
Lemma rd_s1 : ltac2:(TCodec.tc2 tcn__Ju0Strnlen "Q3'QEyR0%211'='7'4y8%711%311%511&K&N&Hr3r2r1%43321&QD&Q3&QFvQB%22D1+H%5221%72G1u8%@4?:21(0&C%124>%32F1%L3F51pS4N1pS2O1pRFQ01").
Proof.
clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1. apply rdn_wbytes_hit8. u_norm. lia.
Qed.
Ltac okstk :=
repeat (eapply store_ok_mono; [apply wbytes_grows|]);
eapply (store_ok_sub RSEGS mem (Z_to_bv 64 (usp - 32)) _ 32 8);
[u_norm; lia | exact Hstk | u_norm; lia | u_norm; cbn; lia].
Ltac kept_cs := cbv [callee_saved In]; tauto.
Ltac msd F D aa :=
chain_step; [reflexivity
| eapply step_sd_at with (a := aa);
[exact F | reflexivity | exact D
| gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia
| gres; rwH; reflexivity
| okstk ]
| step_simpl]; vnorm.
Ltac mld8 F D vv RD :=
chain_step; [reflexivity
| eapply step_ld with (v := vv);
[exact F | reflexivity | exact D
| gres; imm_norm; rwH;
lazymatch goal with |- rdn _ _ ?a _ = _ =>
lazymatch type of RD with rdn _ _ ?c _ = _ =>
replace a with c by (unfold v_addi; unorm; f_equal; lia) end end;
exact RD
| apply bytes_le_to_Z_8 ]
| step_simpl]; vnorm.
Section SE.
Local Abbreviation SEC_T_strnlen_run := (ltac2:(TCodec.tc2 tcn__Ju0Strnlen "R@&Dy5'QEyR0%211%5241&Gr1%211'=&Ir3(QC+1(;%33>21%6251r2%93>21r4+2%93D17%<231vQB%?3D21r5+:%?3J1=%B231vQ?%E3J21r6+;%E3Q01C%H231&QDvQ9%22Q21%M3Q241'>'<'E&N&JvQ6r8+e[U8%Q33Q<1Q1/01Q<vQ7vQ>%8576321r7&H+8%Q;3QF1Q9%Q>2;1+9%Q>3QI1Q<%QA2>1%73841%B5AQF91;%E3D;1&L%12CQI%QG2QJQ6vA%Q02R01%QK3R031%M251%N281qRJR21%Q12R31p0Q31p0Q<1p0QC1p0QJ1p0R51pRLR:1pRHR:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_strnlen_run) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_strnlen_run) 1%nat 0%nat).
Lemma strnlen_run : ltac:(sec_stmt2 constr:(SEC_T_strnlen_run) 2%nat 0%nat).
Proof.
intros Hret H1 H2 H10 H11.
pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs.
pose proof (KL _ _ _ _ _ HOK) as HKL.
destruct HOK as [Hbuf Hwin Hnw HK0 _ _ HKn Hn64 Hro].
set (s0 := getr regs 8). set (s1 := getr regs 9).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa0b8 : word) (mem1 ret s0 s1) rom)
(fun r => getr r 1 = (0xaaccc : word) /\ getr r 2 = Z_to_bv 64 (usp - 32)
/\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = s
/\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 n
/\ (forall x : reg, In x callee_saved -> x <> 1 -> x <> 2 -> x <> 8 -> x <> 9 -> getr r x = getr regs x))).
{ eexists. split.
- stepiv (ltac:(oF' 0xaaca8%Z)) (ltac:(oD' 0xaaca8%Z)) (Z_to_bv 64 (usp - 32))
ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).
msd (ltac:(oF' 0xaacac%Z)) (ltac:(oD' 0xaacac%Z)) (Z_to_bv 64 (usp - 8)).
msd (ltac:(oF' 0xaacb0%Z)) (ltac:(oD' 0xaacb0%Z)) (Z_to_bv 64 (usp - 16)).
msd (ltac:(oF' 0xaacb4%Z)) (ltac:(oD' 0xaacb4%Z)) (Z_to_bv 64 (usp - 24)).
stepn (ltac:(oF' 0xaacb8%Z)) (ltac:(oD' 0xaacb8%Z)).
stepn (ltac:(oF' 0xaacbc%Z)) (ltac:(oD' 0xaacbc%Z)).
stepn (ltac:(oF' 0xaacc0%Z)) (ltac:(oD' 0xaacc0%Z)).
stepn (ltac:(oF' 0xaacc4%Z)) (ltac:(oD' 0xaacc4%Z)).
stepn (ltac:(oF' 0xaacc8%Z)) (ltac:(oD' 0xaacc8%Z)).
rwH. fold s0 s1. unfold mem1. apply mst_refl.
- cbv beta. repeat split; gres; rwH; try reflexivity; try bveq.
intros x Hx N1 N2 N8 N9. cbv [callee_saved In] in Hx.
repeat (destruct Hx as [<-|Hx];
[first [ exfalso; match goal with N : ?a <> ?a |- _ => apply N; reflexivity end
| gres; reflexivity ] |]).
destruct Hx. }
cbv beta. intros r1 (R1 & R2 & R8 & R9 & R10 & R11 & R12 & RK).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaaccc : word) (mem1 ret s0 s1) rom)
(fun r => getr r 10 = Z_to_bv 64 (bv_unsigned s + K) /\ keeps_cs r1 r)).
{ destruct (ref_memchr0 (mem1 ret s0 s1) s buf K n rom r1 (0xaaccc : word) (HOK1 ret s0 s1)
ltac:(apply ret_ok_even; reflexivity) R1 R10 R11 R12) as (r & RUN & KC & A10).
exists r. split; [exact RUN | split; [exact A10 | exact KC]]. }
cbv beta. intros r2 (A10 & KC).
assert (S2 : getr r2 2 = Z_to_bv 64 (usp - 32)) by (rewrite (KC 2) by kept_cs; exact R2).
assert (S9 : getr r2 9 = s) by (rewrite (KC 9) by kept_cs; exact R9).
eexists. split.
- stepb_ft (ltac:(oF' 0xaaccc%Z)) (ltac:(oD' 0xaaccc%Z)) ltac:(rwH; apply c_eq_neq; unorm; lia).
stepiv (ltac:(oF' 0xaacd0%Z)) (ltac:(oD' 0xaacd0%Z)) (Z_to_bv 64 K)
ltac:(gres; rwH; unfold v_sub; unorm; f_equal; lia).
stepn (ltac:(oF' 0xaacd4%Z)) (ltac:(oD' 0xaacd4%Z)).
mld8 (ltac:(oF' 0xaacd8%Z)) (ltac:(oD' 0xaacd8%Z)) ret (rd_ra ret s0 s1).
mld8 (ltac:(oF' 0xaacdc%Z)) (ltac:(oD' 0xaacdc%Z)) s0 (rd_s0 ret s0 s1).
mld8 (ltac:(oF' 0xaace0%Z)) (ltac:(oD' 0xaace0%Z)) s1 (rd_s1 ret s0 s1).
stepiv (ltac:(oF' 0xaace4%Z)) (ltac:(oD' 0xaace4%Z)) sp
ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
stepret (ltac:(oF' 0xaace8%Z)) (ltac:(oD' 0xaace8%Z)) ret ltac:(reflexivity).
apply mst_refl.
- split.
+ intros x Hx. pose proof Hx as Hx'. cbv [callee_saved In] in Hx.
repeat (destruct Hx as [<-|Hx];
[ gres; subst s0 s1; first [ symmetry; assumption | reflexivity
| rewrite (KC _ Hx'); apply (RK _ Hx'); intros E; discriminate E ] |]).
destruct Hx.
+ gres. reflexivity.
Qed.
End SE.
End SNL.
Theorem ref_strnlen : ltac2:(TCodec.tc2 tcn__Ju0Strnlen "TD'QEyR0%211'7y8%511%311p051'4%114'@&Dy5%221;'Mr9r8r6r5r4%6554321&Q1z&O&QF%12H:%3219%6251'='1&B&Nr;&QD&Q3+Q0%22;1%42Q41uQ0%948721(:%=3<21&Q0+R^e@r:%E2Q<1%<21;%5241'?r<%J2QA1&Q2&3%12Q@9%311%Q0251%Q02QGH%G21F%@231%A239%<221&G%11Q=&I(QC+1(;%33QG21%52QD1r7%Q:3R421+2%83QL16%:2QJ1r>%Q?3R921+:%=3R11;%?2Q21r@%QD3R>21+;%B3R61@%D2QC1r=%QD2RD1%QJ3RD31'>'<'E&JvQ6+e[U8%M3RL1K/01RLrEr?%756G321r2r1%:592@14%<3R641&L%12M5%Q926KrA%R92S91%R?3S931&F(2'9%12S=S5(8rC%RJ2SA1%RA21R@%RC2SC1%54SCS;1RB(6%118%;3931%=3JF1%Q22?1%Q32D1%Q42G1qRBSF1%Q72SG1qRJSB1%Q92SC1p0Q;1p0QB1p0QH1p0QN1p0R71p0R:1p0RH1p0RO1p0S>1p0SF1pRLT91pRHSO1pRNT61pRDT41pQ4T51pR<T71pS6T?1pS0T@1pR@T<1").
Proof.
intros mem s sp buf K n rom regs ret HOK HsK Hstk Hspr Hdisj Hret H1 H2 H10 H11.
destruct (strnlen_run mem s sp buf K n rom HOK HsK Hstk Hspr Hdisj regs ret Hret H1 H2 H10 H11)
as (r & RUN & KC & A10).
exists r, (mem1 mem sp ret (getr regs 8) (getr regs 9)).
split; [exact RUN | split; [exact KC | split; [exact A10 | apply frame1; exact Hspr]]].
Qed.
End FPX_1.
