(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2 SymExec2Sound SymRun SymDrive
RefMemcpyLib AgentLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SymAux RefPrintfLib Ju0PrintfBufBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0PrintfBuf () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0PrintfBuf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0PrintfBuf.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0PrintfBufBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymAux."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "0E"; "4word_to_le_bytes"]; ["5ALU_ADD"; "6bvmap"; "7msteps"; "8frame_mod"; ":pf_fuel"; ":pf_post"; ":pf_regions"; ":pf_stops"; "9pf_post"; ";pfH"; ";pf_kn"; ";pf_sr"; "<getr"; "<mkst"; "<rdn"; "=callee_saved"]; ["=keeps_cs"; ">log_covered"; ">same_regs"; "?kread"; "@EAlu"; "@ELit"; "@EVar"; "@SA"; "@SCR"; "@SS"; "@adenot"; "@carry"; "@expr"; "@kentry"; "@s_log"; "@s_pc"]; ["@s_regs"; "@scripts"; "@sentry"; "@sidecond"; "@sym_exec"; "@sym_state"; "Ascs_denot"; "Bloaded_segments"; "Cadd"; "Cle"; "Clt"; "Cmodulo"; "Cpow"; "Csub"; "0can"; "0dirs"]; ["0fx"; "0hs'"; "0k"; "0kn'"; "0mem"; "0mem'"; "0regs"; "0regs'"; "0rom"; "0scr'"; "0scs"; "0sp"; "0ss'"; "DBV"; "DZ_to_bv"; "Dbv"]; ["Dbv_unsigned"; "0w"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition pf_stops : list Z := [0x341c8].
Definition pf_fuel : nat := 3000.
Definition pf_regions : list sregion :=
[(SA (EVar 0) (-1056), 1056); (SA (ELit 0) 0xb7120, 4); (SA (ELit 0) 0xb7148, 8); (SA (EVar 1) 0, 2)].
Definition pf_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop :=
exists regs' mem',
msteps RSEGS (mkst regs (Z_to_bv 64 0x34274) mem rom) (mkst regs' (Z_to_bv 64 0x341c8) mem' rom)
/\ keeps_cs regs regs'
/\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0xb7120, 4);
(Z_to_bv 64 0xb7148, 8); (Z_to_bv 64 w, 2)]
/\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
/\ rdn RSEGS mem' (Z_to_bv 64 0xb7148) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
/\ rdn RSEGS mem' (Z_to_bv 64 0xb7120) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
Section Package.
Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
Hypothesis PH : pfH mem sp w can.
Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x341c8.
Hypothesis R2 : getr regs 2 = sp.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.
Let E := pfE regs sp w can.
Lemma adenot_lit0 : ltac2:(TCodec.tc2 tcn__Ju0PrintfBuf "N'=':&QIzr1%3221&QJ&QL+2+R0%3221%5271%;271';'R?yR0%211&Q:v>(Q7(Q5%11Br2%4221%7261&R>%12;4%>3;31p0@1pT6M1").
Proof.
intros k Hk. unfold adenot. cbn [a_base a_off edenot]. unfold v_addi.
rewrite u64_lit by lia. f_equal; lia.
Qed.
Lemma adenot_var1 : ltac2:(TCodec.tc2 tcn__Ju0PrintfBuf "E'=';'R?yR0%211&Q:v>(Q7(Q6u1%211r1%5221%8271&R>&QHvRA%2216%42?1%B3?61pT6D1").
Proof.
intros k. destruct PH. unfold adenot. cbn [a_base a_off edenot].
change (ev E 1) with (Z_to_bv 64 w). unfold v_addi. rewrite u64_lit by lia. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_pf_case := (ltac2:(TCodec.tc2 tcn__Ju0PrintfBuf "T8'3'1%211'QE'QC%511'QA'Q=%811';'7%1286%2216&QD&QG&D(8&G(Q8r6(4'Q<%211%31F%63521(Q9+V`cD&K'QB%911&JuQ8%7565321%=1M%E7DCBA:21(6r5r4%34Q3Q121r3%54MQ221%Q03M71'=&Q?%11I+V`^8%Q53421&Q1&F&Q>r7%211%5241%Q<3QD1Q5&Q2&Q@r8%211&O%53Q021%QC3QK1Q<%QC2QEQH%QD21QL&Q;r9%@11%331Q4Q;%Q04QKQNQ@Q2%Q147R21Q0%QL3731'5%11QB&Q3(Q5z%211+flZ8u8%65R0L321(0(Q4(@(Q6u1%211+2%=11%73631%92R31%R@3B;1+flY0u4%D5R>Q4A21+5%E11%@2R:1%RG3I41%I5RCQ1=G>+Q@%J11%E2R?1%RL3N41r:+1%Q05RJ2D1E+:%Q111%L2RF1%S33Q541&QFvR4v>r=%44S3321&EvR6vR8vR;vRA%5549321p071p0=1p0E1p0K1p0Q31p0QH1p0R21p0R:1p0RB1p0RH1pT4T01pT8SK1pTDSN1pTFT01pTJT31pT0T51")) (only parsing).
Variable dirs : ltac:(sec_ty2 constr:(SEC_T_pf_case) 0%nat 0%nat).
Variable ss' : ltac:(sec_ty2 constr:(SEC_T_pf_case) 1%nat 0%nat).
Variable scs : ltac:(sec_ty2 constr:(SEC_T_pf_case) 2%nat 0%nat).
Variable scr' : ltac:(sec_ty2 constr:(SEC_T_pf_case) 3%nat 0%nat).
Variable kn' : ltac:(sec_ty2 constr:(SEC_T_pf_case) 4%nat 0%nat).
Variable hs' : ltac:(sec_ty2 constr:(SEC_T_pf_case) 5%nat 0%nat).
Lemma pf_case : ltac:(sec_stmt2 constr:(SEC_T_pf_case) 6%nat 0%nat).
Proof.
intros Hrun Hpc Hcov Hsame Hcarry K1 K2 K3 K4 Hsc.
pose proof (pf_regs_ok regs sp w can R1 R2 R11) as HR.
pose proof (pf_know_ok regs mem sp w can PH) as HK.
fold E in HR, HK.
destruct (run_sound RSEGS pf_fuel pf_stops (SCR dirs [] []) 0x34274 pf_sr pf_kn 40 ss' scs scr' E mem rom regs
Hrun HR HK Hsc) as (R' & HR' & Hlf & Hms).
rewrite Hpc in Hms.
assert (HK' : know_ok RSEGS E (mem_denot E mem (s_log ss')) kn').
{ eapply carry_after; [exact Hcarry | exact Hlf | exact HK | constructor]. }
destruct PH. pose proof (u64_range sp) as Hsp.
assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
assert (Hw1 : ev E 1 = Z_to_bv 64 w) by reflexivity.
exists R', (mem_denot E mem (s_log ss')).
split; [exact Hms|]. split; [|split; [|split; [|split]]].
- eapply (keeps_cs_of_same E); eassumption.
- replace [(Z_to_bv 64 (bv_unsigned sp - 1056), 1056); (Z_to_bv 64 0xb7120, 4);
(Z_to_bv 64 0xb7148, 8); (Z_to_bv 64 w, 2)]
with (map (rdenot E) pf_regions).
2:{ unfold pf_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot].
change (ev E 0) with sp. rewrite Hw1, Z0, (u64_lit w) by lia.
repeat (f_equal; [try (f_equal; lia)..]). all: f_equal; lia. }
apply log_covered_frame; [exact Hcov | | exact Hlf].
intros r Hr. unfold pf_regions in Hr. cbn [In] in Hr.
unfold flat, estart.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd a_base a_off edenot];
try change (ev E 0) with sp; rewrite ?Hw1, ?Z0, ?(u64_lit w) by lia; lia.
- pose proof (kread_rdn RSEGS E _ kn' (EVar 1) 0 1 _ HK' K3 ltac:(lia) ltac:(lia)) as B0.
pose proof (kread_rdn RSEGS E _ kn' (EVar 1) 1 1 _ HK' K4 ltac:(lia) ltac:(lia)) as B1.
rewrite adenot_var1 in B0, B1.
apply rdn_2.
+ rewrite u64_lit by lia. lia.
+ rewrite Z.add_0_r in B0. apply B0.
unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
+ rewrite u64_lit by lia. apply B1.
unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hw1, (u64_lit w) by lia. lia.
- pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0xb7148 8 _ HK' K1 ltac:(lia) ltac:(lia)) as B.
rewrite adenot_lit0 in B by lia. cbn [edenot] in B. rewrite Hw1, alu_add_Z in B.
apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
- pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0xb7120 4 _ HK' K2 ltac:(lia) ltac:(lia)) as B.
rewrite adenot_lit0 in B by lia. cbn [edenot] in B.
apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
Qed.
End SE.
End Package.
End FPX_1.
Ltac sc_bool :=
match goal with
| Hw4 : ?w mod 4 = ?r |- _ =>
first [ rewrite (mod4_shift w _ r Hw4); reflexivity
| rewrite Hw4; reflexivity ]
end.
Ltac sc_pf :=
cbn [sc_denot edenot ev pfE vals_ev pf_vals nth app];
first
[ rewrite lin_neg1_val, u64_lit by lia; first [ apply bt_geu_Z; lia | apply bt_geu_Z_false; lia ]
| apply bt_and3; [lia | cbv beta iota; sc_bool]
| apply bt_and3_0; [lia | cbv beta iota; sc_bool] ].
Section FPX_2. Context {fx : PropExec.FPState}.
Definition pf_run (dirs : list bool) :=
sym_exec RSEGS pf_fuel true pf_stops (SCR dirs [] []) (SS 0x34274 pf_sr [] pf_kn 40) [].
Definition dirsA : list bool := [true; true; false; true; false].
Definition dirsB : list bool := [false; false; true; true; true].
Definition dirsC : list bool := [false; false; true; true; false].
Definition dirsD : list bool := [false; false; true; false; false].
Definition resA := Eval vm_compute in (pf_run dirsA).
Definition carA := Eval vm_compute in (carry (s_log (fst (fst resA))) pf_kn []).
Definition resB := Eval vm_compute in (pf_run dirsB).
Definition carB := Eval vm_compute in (carry (s_log (fst (fst resB))) pf_kn []).
Definition resC := Eval vm_compute in (pf_run dirsC).
Definition carC := Eval vm_compute in (carry (s_log (fst (fst resC))) pf_kn []).
Definition resD := Eval vm_compute in (pf_run dirsD).
Definition carD := Eval vm_compute in (carry (s_log (fst (fst resD))) pf_kn []).
End FPX_2.
Ltac run_case dirs res car :=
lazymatch goal with
| PH : pfH ?mem ?sp ?w ?can, R1 : getr ?regs 1 = _, R2 : getr _ 2 = _, R11 : getr _ 11 = _ |- pf_post _ _ ?rom _ _ =>
eapply (pf_case regs mem rom sp w can PH R1 R2 R11 dirs
(fst (fst res)) (snd (fst res)) (snd res) (fst (fst car)) (snd car));
[ vm_compute; reflexivity
| reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| vm_compute; reflexivity
| let v := eval vm_compute in (snd (fst res)) in
change (snd (fst res)) with v;
destruct PH; split_scs; sc_pf ]
end.
Section FPX_3. Context {fx : PropExec.FPState}.
Lemma pf_caseA : ltac2:(TCodec.tc2 tcn__Ju0PrintfBuf "QO&Ay5'R?yR0%211%5241'5y8%611%311p061'='Ir5r3r2r1%544321';&QK+4%2271z%53<21&Lr8(R=+1(9%33L21%6251&R>+V`^8%22N1%@3N41r9+2%;3Q419%>231r6%F3Q421r:+;%A3Q:1?%D231%>2Q:G%L3Q:21&HvR0r;r7%4632:@J1p061p0=1p0D1p0Q01p0Q71pSNQ>1pU4Q?1pTHQG1pTBQB1pT:QC1pT>QI1").
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsA resA carA. Qed.
Lemma pf_caseB : ltac2:(TCodec.tc2 tcn__Ju0PrintfBuf "QO&Ay5'R?yR0%211%5241'5y8%611%311p061'='Ir5r3r2r1%544321';&QK+4%2271+2%53<21&Lr8(R=+1(9%33L21%6251&R>+V`^8%22N1%@3N41r9%:3Q3>8%=221r6%E3Q321r:+;%@3Q91>%C231z%>2Q:1%L3Q:31&HvR0r;r7%4632;@J1p061p0>1p0D1p0Q01p0Q71pSNQ>1pU4Q?1pTHQG1pTBQB1pT:QC1pT>QI1").
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsB resB carB. Qed.
Lemma pf_caseC : ltac2:(TCodec.tc2 tcn__Ju0PrintfBuf "QO&Ay5'R?yR0%211%5241'5y8%611%311p061'='Ir5r3r2r1%544321';&QK+4%2271+1%53<21&Lr8(R=(9%23K61%5241&R>+V`^8%22M1%?3M41r9+2%:3Q319%=231r6%E3Q321r:+;%@3Q91?%C231z%?2Q:1%L3Q:31&HvR0r;r7%4632;AJ1p061p0>1p0E1p0Q01p0Q71pSNQ>1pU4Q?1pTHQG1pTBQB1pT:QC1pT>QI1").
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsC resC carC. Qed.
Lemma pf_caseD : ltac2:(TCodec.tc2 tcn__Ju0PrintfBuf "R0&Ay5'R?yR0%211%5241'5y8%611%311p061'='Ir5r3r2r1%544321';&QK+4%2271+3%53<21&Lr8(R=+1(9%33L21%6251&R>+V`^8%22N1%@3N41r9+2%;3Q419%>231r6%F3Q421r:+;%A3Q:1?%D231z%?2Q;1%M3Q;31&HvR0r;r7%4632;AK1p061p0>1p0E1p0Q11p0Q81pSNQ?1pU4Q@1pTHQH1pTBQC1pT:QD1pT>QJ1").
Proof. intros regs mem rom sp w can PH Hw4 R1 R2 R11. run_case dirsD resD carD. Qed.
Theorem printf0_buffered : ltac2:(TCodec.tc2 tcn__Ju0PrintfBuf "T:&Ay5'R?yR0%211%5241'5y8%611%311p061'='Ir5r3r2r1%544321';&Lr7(R=+1(9%33G21%6251&R>+V`^8%22I1%;3I41r8+2%;3O19%>231%@3N1Er9+;%@3Q41>%C231z%>2Q51%G3Q531'<':'B&QG&MvR0r<+V`cD%H2Q?1r;r:%7565321%857Q7JQ62%;3:21&Q0%129Q:&C(2'7%12QIQB(6&QM&R@%12QNN+QQ0%4221%Q:2R11%74R1QJ13+flY0%Q=2R41+4%;4R5QN21+flZ8%QA2R81+8%?4R9R221%QD2R;Q@%A4R;R41Q@(4%11D%G3E31%H3F61%I3G;1%J3H@1%L3Q3R61'3%11R@%RC11&Nu2%24Q?R<>1(0+Q@%R52RH1+:%R72RJ1%B1RJ%Q83RK21%Q93RL51%82=1%RD3=:1u8%>4QKRHM1&?&QH%12R=R<%RB2S91%4261%A2F1%RM3F71u4%G4R4S1Q:1+5%RI2S@1%;241%H2M1%S43M51%R<281%R=2B1%R>2Q31%R?2R11%R@2R41qT<SB1%RC2SC1qT@SI1%RE2SJ1p0RG1p0RO1p0S51p0SB1pSNSI1pU4SJ1pTHT21pTBSM1pT:SN1pT>T41").
Proof.
intros regs mem rom sp w can PH R1 R2 R11.
destruct (mod4_cases w) as [H0|[H1|[H2|H3]]].
- exact (pf_caseA regs mem rom sp w can PH H0 R1 R2 R11).
- exact (pf_caseC regs mem rom sp w can PH H1 R1 R2 R11).
- exact (pf_caseB regs mem rom sp w can PH H2 R1 R2 R11).
- exact (pf_caseD regs mem rom sp w can PH H3 R1 R2 R11).
Qed.
End FPX_3.
Print Assumptions printf0_buffered.
