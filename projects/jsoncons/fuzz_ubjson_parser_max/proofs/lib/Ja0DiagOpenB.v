(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA
Ja0RegionPoisoned Ja0AsanMemcpy Ja0DiagKit Ja0DiagChk Ja0DiagMemcpy Ja0DiagStrnlen Ja0DiagGlue Ja0DiagOP Ja0DiagOpenPre.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DiagOpenB () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagGlue.DG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagOpenB.DOB.UA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagOpenPre.DOP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3add"; "4map"; "5Z"]; ["6word_to_le_bytes"; "7bvmap"; "0M"; "0M5"; "0ME"; "0ME2"; "0MF"; "0MX"; "0MY"; "0R"; "0R5"; "0RE"; "0RE2"; "0RF"; "0RX"; "0RY"]; ["8msteps"; "9agree0"; ":PRE17"; ":SUF1"; ";open_mid"; "<u32_at"; "<u64_at"; "<u8_at"; "=FPState"; "=getr"; "=mkst"; "=rdn"; "=seg_rom"; ">mem_grows"; "?loaded_segments"; "0S"]; ["@In"; "Aadd"; "Ale"; "Alt"; "Aof_nat"; "Apow"; "Asub"; "0a"; "0b0"; "0b1"; "0b2"; "0b3"; "0bs"; "0can"; "0fx"; "0fx'"]; ["0fx''"; "0fx5"; "0fxE"; "0fxE2"; "0fxF"; "0k"; "0p"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0w"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module DOB.
Import DK. Import DSN. Import DG. Import AS0DIAGOP.
Lemma u8s_of_u32 : ltac2:(TCodec.tc2 tcn__Ja0DiagOpenB "R<'R8yR0%211'8y8%511%311p051'?&QBzr6%3221&QAr7+4%3221&QE+2+R0%3221%<251&Q5&Q>r9r8%44321<':'5%11E&>&R9%11L&@u4&R7%12Q3;%4231%84Q1N61(3r5r4(7%11Q3%53Q431%63Q551%73Q6Q31%83Q7Q11%E3C:1'9&Q7r;r:%34N21L+1%Q:231%64Q151Q:%Q<25Q7%84Q371Q?+3%Q?281%;4Q6:1E%=241%>271%?2;1p0A1p0Q81p0Q>1p0QH1pSHQM1pSFQN1pSDQO1pSBR01pTFR11pS@R21pQ6R41").
Proof. intros M a w b0 b1 b2 b3.
intros Ha Hb C E. unfold L5.u32_at in C. unfold L5.u8_at.
destruct (word_to_le_bytes 4 (Z_to_bv 64 w)) as [|c0 [|c1 [|c2 [|c3 [|]]]]] eqn:EL; try discriminate E.
cbn [map] in E. injection E as E0 E1 E2 E3.
assert (X : forall c b, bv_unsigned c = b -> (c : byte) = Z_to_bv 8 b) by (intros c b <-; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (Ja0DiagStrlen.rdn_byte_at M a _ _ 0%nat C ltac:(lia) Ha ltac:(lia)) as R0. pose proof (Ja0DiagStrlen.rdn_byte_at M a _ _ 1%nat C ltac:(lia) Ha ltac:(lia)) as R1.
pose proof (Ja0DiagStrlen.rdn_byte_at M a _ _ 2%nat C ltac:(lia) Ha ltac:(lia)) as R2. pose proof (Ja0DiagStrlen.rdn_byte_at M a _ _ 3%nat C ltac:(lia) Ha ltac:(lia)) as R3.
cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ] in R0, R1, R2, R3. rewrite Z.add_0_r in R0.
rewrite (X c0 b0 E0) in R0. rewrite (X c1 b1 E1) in R1. rewrite (X c2 b2 E2) in R2. rewrite (X c3 b3 E3) in R3.
repeat split; assumption.
Qed.
Ltac rdn_bytes :=
repeat (apply rdn_cons; [lia | cbn; lia | (match goal with |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => try (progress (ring_simplify a)) end; match goal with H : L5.u8_at _ _ ?a _ |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => exact H end) | ]);
reflexivity.
Section UA.
Context (fx : FPState).
Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
#[local] Notation n := (Z.of_nat (length bs)).
Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 685072.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1273408.
Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 127129.
Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.
Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
Hypothesis Hal : S mod 16 = 0.
Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
Hypothesis HD : L5.defined M (S - 5440) 5440.
Hypothesis HIMG : L5.img_clear M 65536 1261568.
Hypothesis Hp : S <= p /\ p + n + 1 + 16 <= 2 ^ 47.
Hypothesis Hn : n = 63.
Hypothesis HSTR : cstr M p bs t8.
Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.
Hypothesis HFMT : L5KA.zeros_at M 2147466768 8.
Hypothesis Hcan : 0 <= can < 2 ^ 64.
Hypothesis HC : diag_cells M can.
Hypothesis HSN : sn_cells M.
Hypothesis HMC : mc_icpt_globs M.
Definition PRE17 : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 127129) 17 with Some l => l | None => [] end.
Definition SUF1 : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 127148) 1 with Some l => l | None => [] end.
Lemma suf1_img : ltac2:(TCodec.tc2 tcn__Ja0DiagOpenB "H':'8'5'R8y8%211%411%611&Q;&Q>yR0%811(0%118q031&R7+SlU<%2271u1%;4:521(1&Q3%22@1%G3@41"). Proof. vm_compute. reflexivity. Qed.
Lemma PRE17_eq : ltac2:(TCodec.tc2 tcn__Ja0DiagOpenB "Q<':'5'R8y8%211%411&Q2&>'?&R7%117(3+S3+S<+S9+QJ+Q0+S1+S>+S?+SD+S@+S5(7%11@%>3A91%?3B81%@3C51%A3D71%B3E:1%C3F>1%D3G;1%E3H=1%F3I?1%G3J@1%H3KB1%I3LH1%J3ME1%K3NG1%L3OI1%M3Q0K1%N3Q1M1%Q34Q2Q6Q01%Q;3Q6Q51").
Proof. apply list_bv_eq. vm_compute. reflexivity. Qed.
Lemma SUF1_len : ltac2:(TCodec.tc2 tcn__Ja0DiagOpenB ":':'6&4'R8y8%211&Q3%5221u1%93821"). Proof. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_open_B_tail := (ltac2:(TCodec.tc2 tcn__Ja0DiagOpenB "ZB'Q8&Ay5'R8yR0%211%5241'8y8%611%311p061&Q4vIvBvQ?vR6vQMvQLr2r1%9887654321';'9'Q0&Q>&Q:r7r6&R7+QScfH%22K1r5&Q<%119%9587431r3+QS\h4%92Q21%=53D1C5%@3?51':&Q9&QDuA%211%A2Q<1%52L1+R2%D2Q=1%93Q=31u:%911%H2QC1%<2Q31+2%K2QD1%@3QD31u;%@11%O2QJ1%C2Q:1&QF+QS8%22QA1%Q42QM1%I3QM51u<%I11%Q82R31%L2QC1%N3R21?u9%N11%Q=2R81%Q12QH1+QVkb0%Q@2R91%Q53R931uB%Q511%QD2R?1%Q82QO1%Q:3R>1KuC%Q:11%QI2RD1%Q=2R41%Q?3RC1GuF%Q?11%QN2RI1%QB2R91&QA&4%12RFR=%QE11+B%5221%R62RO1%QK3RO81&Q6+^@%Q92RH1%34R?RDQ81+QS0%Q<2RK1+A%?2<1%84RDRI31+QRH%QA2S01+SlU<%<4RHRM21+QR@%QE2S41+1%@4RLS121'5%11S>%SA11&Q;%RM2SFC&=%12R@M%44S4S931(1&2&Q2%23SH1S?%42;1%RJ3;61%S72T0Du1%=4S=SB21&Q3%:2A1%S03A31&Q5+QVkeH%24SCSH1RE&Q1%13T0SJSO&Q=%12T2SLpTHT<T7&<&QB&R9%12TAT1%32RF1&QC+QR8%RK2T:1%3251%T4251%:11%SI1T:%T21T;%SF3TE21p041pTHTL1%C2T2T?'6&Q@(3u2u3u4u8uEuGuHuIuJuK(7%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ES@1%D3F@1%E3GB1%F3HD1%G3IF1%I3JU91%TC1U;%U22UM1%TF2U41r9%TH213%TJ3UN31p071pT<Q21r8+QS\h@%U;2V41%U?5831U>U7%UB3UA1U3+aH%T>2UM1%U@2V91%U53V9TA1%UB2V;RK%U73V;T:1%U83V<SO2%U93V=SK5z%UG2V@1%U<3V@SI1%SA4UMV2:3+a@%TJ2V91%SD4V0V516+b8%TM2V<1%R921R7+a8%U02V?1%R82R:1%V9241%R?11p01R3pTHVN1+QR^Y4%V82W11%V<5V2VC1VBV4%V?3V>N1%UM1R2%V<2W71%V02VG1%V>2W7VL%V33W721+5%S44VEVJU21+QVke0%T;4VGVL1M+QVkdH+Vam\H%T>4VJVO21+QVkcH%T@4VLW11Q2+QVkc8%TB4VNW31Q4+QVkc0%TD4W0W51Q6+QVkb8%TF4W2W71Q8+QVkb@%TH4W4W91Q:%VC1RF%W22WM1%VF2W=1%VG2WD2%VI3WM21%W<261%W=291%W>2<1%W?2?1%W@2B1%WA2E1%WB2I1%WC2L1%WD2SK1%WE2SN1%WF2Q11%WG2VE1%WH2Q81qQ>X51%WK2X61qQLX<1%WM2X=1qT:XD1%WO2XE1p0RA1p0SE1p0QE1pQBT81pR0XD1pT2XK1%X52T<1%X62T?1%X72TB1%X82R61%X92R:1%X:2R<1%X;2R@1%X<2RB1%X=2VF1%X>2RE1%X?2RH1%X@2W>1%XA2WF1%XB2RO1qQ<XO1%XE2Y01qQJY61%XG2Y71qT8Y>1%XI2Y?1p0S;1p0T?1p0TA1pQ@U21pQNY>1pT0YE1%XO2U61%Y02U91%Y12U<1%Y22U@1%Y32UG1%Y42V61%Y52V;1%Y62V@1%Y72VF1%Y82VK1%Y92W81%Y:2W>1%Y;2WD1%Y<2WL1%Y=2X21%Y>2X<1%Y?2XD1%Y@2XO1qQ:YM1%YC2YN1qQHZ41%YE2Z51qT6Z<1%YG2Z=1p0YI1pQ8Z41pQFZ:1pT4ZA1")) (only parsing).
Variable fx5 : ltac:(sec_ty2 constr:(SEC_T_open_B_tail) 0%nat 0%nat).
Variable R5 : ltac:(sec_ty2 constr:(SEC_T_open_B_tail) 1%nat 0%nat).
Variable M5 : ltac:(sec_ty2 constr:(SEC_T_open_B_tail) 2%nat 0%nat).
Theorem open_B_tail : ltac:(sec_stmt2 constr:(SEC_T_open_B_tail) 3%nat 0%nat).
Proof.
intros INV.
pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
assert (Pr : 140735332552704 <= p <= 140737488355311) by lia.
assert (Nr : 0 <= n <= 131071) by lia.
assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
destruct INV as (A05 & MG05 & T). dk_split T.
assert (W5 : L5.writable RSEGS M5 (S - 5440) 5440) by (eapply writable_grows; [exact MG05 | exact HW]).
assert (D5 : L5.defined M5 (S - 5440) 5440) by (eapply defined_grows; [exact MG05 | exact HD]).
assert (IMG5 : L5.img_clear M5 65536 1261568) by (apply (imgc_ext M M5); [intros x Hx; apply A05; flia | lia | lia | exact HIMG]).
cfeed P (doDs_conc fx5 R5 M5 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fx6 R6 M6 MG6 FR6 FZ6 MS6 KS6.
assert (AG56 : forall x : word, bv_unsigned x < S - 1088 \/ S - 1024 <= bv_unsigned x -> M6 x = M5 x) by (intros x Hx; apply FR6; lia).
assert (A06 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M6 x = M x) by (intros x Hx Hf; rewrite AG56 by lia; apply A05; assumption).
assert (MG06 : mem_grows M M6) by (eapply mem_grows_trans; eassumption).
assert (W6 : L5.writable RSEGS M6 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (STR6 : cstr M6 p bs t8) by (apply (cstr_ext M M6); [lia | lia | intros x Hx; apply A06; flia | exact HSTR]).
assert (HSN6 : sn_cells M6) by (apply (sn_cells_agree M M6 S); [lia | exact A06 | exact HSN]).
assert (HMC6 : mc_icpt_globs M6) by (apply (mc_globs_agree M M6 S); [lia | exact A06 | exact HMC]).
assert (SK6 : L5KA.zeros_at M6 (SB + S / 8 - 680) 688).
{ apply (zeros_ext M M6); [intros x Hx; apply A06; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
assert (RDS6 : rdn RSEGS M6 (Z_to_bv 64 p) (length bs) = Some bs).
{ destruct STR6 as [A _ _]. rewrite (SeqExec.rdn_firstn RSEGS M6 _ _ _ (length bs) A) by lia. f_equal. rewrite firstn_app, firstn_all2 by lia. rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
destruct (memcpy_stage fx6 R6 M6 (S - 1088) (S - 447) p n bs) as (R7 & M7 & MS7 & V7 & KS7 & AG67 & MG7 & RD7);
[ sc | sc | sc | sc | sc | reflexivity | lia | lia | lia | (right; unfold HIGHBEG, HIGHEND; lia) | (right; unfold HIGHBEG, HIGHEND; lia) | lia | lia | lia | lia | lia
| dk_gmem | (apply (L5.writable_sub RSEGS M6 (S - 5440) 5440); [exact W6 | lia | lia]) | exact RDS6 | (destruct HSN6 as (_ & _ & _ & G & _); exact G) | exact HMC6
| (apply (zsh_of_hullm _ p n n); [lia | lia | lia | intros x Hx; assert (0 <= p / 8) by (apply Z.div_pos; lia); rewrite A06 by (unfold SB in Hx; flia); apply HSH; exact Hx])
| (apply (stk_zsh M6 S); [exact Hal | lia | exact SK6 | lia | lia | lia]) | ].
assert (A07 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M7 x = M x) by (intros x Hx Hf; rewrite AG67 by lia; apply A06; assumption).
assert (MG07 : mem_grows M M7) by (eapply mem_grows_trans; eassumption).
assert (W7 : L5.writable RSEGS M7 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (D7 : L5.defined M7 (S - 5440) 5440) by (eapply defined_grows; eassumption).
assert (IMG7 : L5.img_clear M7 65536 1261568) by (apply (imgc_ext M M7); [intros x Hx; apply A07; flia | lia | lia | exact HIMG]).
assert (FW7 : L5.writable RSEGS M7 1273408 152) by (eapply writable_grows; eassumption).
assert (AG67' : forall x : word, S - 1088 <= bv_unsigned x -> ~ (S - 447 <= bv_unsigned x < S - 447 + n) -> M7 x = M6 x) by (intros x Hx Hd; apply AG67; [lia | exact Hd]).
assert (AG57 : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 447 <= bv_unsigned x < S - 447 + n) -> M7 x = M5 x) by (intros x Hx Hd; rewrite AG67' by (first [exact Hd | lia]); apply AG56; lia).
assert (AG57s : forall x : word, bv_unsigned x < 2 ^ 32 -> M7 x = M5 x) by (intros x Hx; rewrite AG67 by lia; apply AG56; lia).
assert (F87 : L5.u8_at RSEGS M7 1273408 5).
{ apply u8_of_u32_5; [lia | lia|]. scc. }
cfeed P (doEb_conc fx6 R7 M7 (fun j => match j with 2%nat => S - 1088 | 33%nat => p | 34%nat => n | 40%nat => can | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.
assert (AG78 : forall x : word, bv_unsigned x < S - 1136 \/ S - 1024 <= bv_unsigned x -> ~ (1273448 <= bv_unsigned x < 1273456) -> M8 x = M7 x) by (intros x Hx Hf; apply FR8; lia).
assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG78 by (unfold filew in Hf; lia); apply A07; assumption).
assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (AG58s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1273448 <= bv_unsigned x < 1273456) -> M8 x = M5 x) by (intros x Hx Hf; rewrite AG78 by lia; apply AG57s; lia).
assert (AG58h : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 447 <= bv_unsigned x < S - 447 + n) -> M8 x = M5 x) by (intros x Hx Hd; rewrite AG78 by lia; apply AG57; lia).
assert (NE : Z.eqb (S - 447 + n) (S - 464) = false) by (apply Z.eqb_neq; lia).
destruct (wv_entry_stage fx8 R8 M8 1273408 (S - 1136) 127148 1 (S - 447 + n) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG8W & MGW);
[ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
rewrite NE in W11, W12, W18, W19.
assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG8W by lia; apply A08; assumption).
assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
assert (IMGW : L5.img_clear MW 65536 1261568) by (apply (imgc_ext M MW); [intros x Hx; apply A0W; flia | lia | lia | exact HIMG]).
assert (BUFW : rdn RSEGS MW (Z_to_bv 64 (S - 464)) (17 + length bs) = Some (PRE17 ++ bs)).
{ assert (AG5Wb : forall x : word, S - 464 <= bv_unsigned x < S - 447 -> MW x = M5 x) by (intros x Hx; rewrite AG8W by lia; apply AG58h; lia).
assert (AG7Wb : forall x : word, S - 447 <= bv_unsigned x < S - 447 + n -> MW x = M7 x) by (intros x Hx; rewrite AG8W by lia; apply AG78; lia).
assert (P17_5 : rdn RSEGS M5 (Z_to_bv 64 (S - 464)) 17 = Some PRE17).
{ rewrite PRE17_eq. cbn [map].
rdn_bytes. }
assert (P7 : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 17 = Some PRE17) by (apply (rdn_xfer M5 MW); [intros x Hx; apply AG5Wb; cbn in Hx; lia | lia | cbn; lia | exact P17_5]).
assert (PB : rdn RSEGS MW (Z_to_bv 64 (S - 447)) (length bs) = Some bs) by (apply (rdn_xfer M7 MW); [intros x Hx; apply AG7Wb; lia | lia | lia | exact RD7]).
apply rdn_app_Z; [lia | lia | exact P7|]. replace (S - 464 + Z.of_nat 17) with (S - 447) by lia. exact PB. }
assert (SUFW : rdn RSEGS MW (Z_to_bv 64 127148) 1 = Some SUF1).
{ rewrite (rdn_img MW 65536 1261568) by (first [exact IMGW | cbn; lia | lia]). exact suf1_img. }
exists fx8, RW, MW.
split. { eapply msteps_trans; [exact MS6|]. eapply msteps_trans; [exact MS7|]. eapply msteps_trans; [exact MS8|]. exact MSW. }
split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
split; [replace (S - 1128) with (S - 1136 + 8) by lia; exact I0|]. split; [replace (S - 1120) with (S - 1136 + 16) by lia; replace (n + 17) with (S - 447 + n - (S - 464)) by lia; exact I1|].
split; [replace (S - 1112) with (S - 1136 + 24) by lia; exact I2|]. split; [replace (S - 1104) with (S - 1136 + 32) by lia; exact I3|].
split; [exact BUFW|]. split; [exact SUFW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
intros fx' RX MX AGXW MGXW KXW.
assert (AGX8 : forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = M8 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG8W; lia).
assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R8 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
assert (AGX7 : forall x : word, S - 1024 <= bv_unsigned x -> MX x = M7 x) by (intros x Hx; rewrite AGX8 by lia; apply AG78; lia).
assert (AGX5 : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 447 <= bv_unsigned x < S - 447 + n) -> MX x = M5 x) by (intros x Hx Hd; rewrite AGX7 by lia; apply AG57; lia).
assert (AGX5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1273448 <= bv_unsigned x < 1273456) -> MX x = M5 x) by (intros x Hx Hf; rewrite AGX8 by lia; apply AG58s; assumption).
assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
assert (IMGX : L5.img_clear MX 65536 1261568) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
assert (FWX : L5.writable RSEGS MX 1273408 152) by (eapply writable_grows; eassumption).
cfeed P (doGb1_conc fx' RX MX (fun j => match j with 2%nat => S - 1136 | 33%nat => p | 34%nat => n | 40%nat => can
| 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
| 122%nat => U RX 22 | 123%nat => U RX 23 | 124%nat => U RX 24 | 125%nat => U RX 25 | 127%nat => U RX 27 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fx9 R9 M9 MG9 FR9 FZ9 MS9 KS9.
assert (AGX9 : forall x : word, bv_unsigned x < S - 1152 \/ S - 480 <= bv_unsigned x -> ~ (1273440 <= bv_unsigned x < 1273456) -> ~ (1273464 <= bv_unsigned x < 1273472) -> M9 x = MX x) by (intros x Hx Hf1 Hf2; apply FR9; lia).
assert (A09 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M9 x = M x) by (intros x Hx Hf; rewrite AGX9 by (unfold filew in Hf; lia); apply AGX0; assumption).
assert (MG09 : mem_grows M M9) by (eapply mem_grows_trans; eassumption).
assert (W9 : L5.writable RSEGS M9 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (AG59s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1273440 <= bv_unsigned x < 1273456) -> ~ (1273464 <= bv_unsigned x < 1273472) -> M9 x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGX9 by lia; apply AGX5s; lia).
assert (EQ : Z.eqb (S - 464) (S - 464) = true) by (apply Z.eqb_refl).
destruct (wv_entry_stage fx9 R9 M9 1273408 (S - 592) 0 0 (S - 464) (S - 464) 2) as (RW2 & MW2 & MSW2 & X17 & X10 & X11 & X12 & X18 & X19 & X22 & KSW2 & J0 & J1 & J2 & J3 & AG9W & MGW2);
[ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
rewrite EQ in X11, X12, X18, X19.
assert (A0W2 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW2 x = M x) by (intros x Hx Hf; rewrite AG9W by lia; apply A09; assumption).
assert (MG0W2 : mem_grows M MW2) by (eapply mem_grows_trans; eassumption).
exists fx9, RW2, MW2.
split. { eapply msteps_trans; [exact MS9|]. exact MSW2. }
split; [exact X17|]. split; [exact X10|]. split; [rewrite X11; f_equal; lia|]. split; [exact X12|].
split; [rewrite (KSW2 9%nat) by (cbn; tauto); sc|]. split; [exact X18|]. split; [rewrite X19; f_equal; lia|]. split; [rewrite X22; f_equal; lia|].
split; [replace (S - 568) with (S - 592 + 24) by lia; exact J2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact J3|].
split; [scc|]. split; [exact A0W2|]. split; [exact MG0W2|].
intros fx'' RY MY AGYW MGYW KYW.
assert (AGY9 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = M9 x) by (intros x Hx; rewrite AGYW by exact Hx; apply AG9W; lia).
assert (KY : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr R9 (reg k)) by (intros k Hk; rewrite (KYW k Hk); apply KSW2; cbn in Hk |- *; tauto).
assert (AGYX : forall x : word, S - 480 <= bv_unsigned x -> MY x = MX x) by (intros x Hx; rewrite AGY9 by lia; apply AGX9; lia).
assert (AGY5 : forall x : word, S - 384 <= bv_unsigned x -> MY x = M5 x) by (intros x Hx; rewrite AGYX by lia; apply AGX5; lia).
assert (AGY5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1273440 <= bv_unsigned x < 1273456) -> ~ (1273464 <= bv_unsigned x < 1273472) -> MY x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGY9 by lia; apply AG59s; assumption).
assert (AGY0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MY x = M x) by (intros x Hx Hf; rewrite AGYW by lia; apply A0W2; assumption).
assert (MG0Y : mem_grows M MY) by (eapply mem_grows_trans; eassumption).
assert (WY : L5.writable RSEGS MY (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (DY : L5.defined MY (S - 5440) 5440) by (eapply defined_grows; eassumption).
assert (IMGY : L5.img_clear MY 65536 1261568) by (apply (imgc_ext M MY); [intros x Hx; apply AGY0; flia | lia | lia | exact HIMG]).
assert (FWY : L5.writable RSEGS MY 1273408 152) by (eapply writable_grows; eassumption).
cfeed P (doGb2_conc fx'' RY MY (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
| 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
| 118%nat => U RY 18 | 119%nat => U RY 19 | 120%nat => U RY 20 | 122%nat => U RY 22 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
exists fxF, RF, MF.
split; [exact MSF|].
split; [sc|].
split; [sc|].
split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. apply AGY0; [exact Hx | unfold filew; lia]. }
split; [eapply mem_grows_trans; [exact MG0Y | exact MGF]|].
repeat split; first [sc | (eapply (DK.u64_ext M5); [intros x Hx; rewrite FRF by lia; apply AGY5s; lia | lia | lia | eassumption]) | dk_rk].
Qed.
End SE.
Theorem open_B : ltac2:(TCodec.tc2 tcn__Ja0DiagOpenB "Z;';'Q8&Ay5'R8yR0%211%5241'8y8%611%311p061'9'Q0&Q>&Q:vQNvI&R7+\Zc4%22@1vB&Q<%119%9587431r3r2+QS\h4%:2H1r1%?554217%B3A71':&Q9&QDuA%211%C2Q31%52<1+R2%F2Q41%93Q431u:%911%J2Q:1%<2C1+2%M2Q;1%@3Q;31u;%@11%Q12QA1%C2J1&QFvQ?+QS8%3221%Q72QE1%J3QE61u<%J11%Q;2QK1%M2Q41%O3QJ1@u9%O11%Q@2R01%Q22Q91+QVkb0%QC2R11%Q63R131uB%Q611%QG2R71%Q92Q@1%Q;3R61LuC%Q;11%QL2R<1%Q>2QE1%Q@3R;1GuF%Q@11%R12RA1%QC2QJ1&QA&4vQL%22R?1%QG11+B%6221%R:2RH1%QM3RH91&Q6+^@%Q;2Q:1%34RCR4Q91+QS0%Q>2Q=1+A%@2<1%84RHR931+QRH%QC2QB1+SlU<%<4RLR=21+QR@%QG2QF1+1%@4S0RA21'5%11S7%S:11&Q;%S12S?C&=%12RBM%44S8RI31(1&2&Q2%23SA1Q3%42;1%RL3;61%S;2SIDu1%=4SAS221&Q3%:2A1%S23A31&Q5+QVkeH%24SGS81RG&Q1%13SBS:RA&Q=%12SDS<pTHT5T0&<&QB&R9%12T:SA%32RG1&QC+QR8%RM2RL1%3251%T8251%:11%SM1SLr6%11SN%SI3T?31p051pTHTF1r5%E21T3'6&Q@(3u2u3u4u8uEuGuHuIuJuK(7%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ESC1%D3F@1%E3GB1%F3HD1%G3IF1%I3JTK1%TG1TO%U82UH1%TJ2Q41r9%TL213%TN3UI31p071pT<Q21r8+QS\h@%UA2UO1r7%UF59421U>%UI3UH1U8+aH%TC2TB1%UG2V51%U:3V5TF1%UI2V7RN%U<3V7T>1%U=3V8T32%U>3V9SO5z%UN2V<1%UA3V<SM1%SD4V4UE:3+a@%TO2TN1%SG4V7UH16+b8%U22U11%R<21R:+a8%U52U41%R;2R=1%V@241%RB11p01R5pTHVJ1+QR^Y4%V?2VM1%VC5V9V81V5V;%VF3VEN1%V21R3%VC2W31%V52V<1%VE2W3UA%V83W321+5%S74VLV=U61+QVke0%T>4VNV?1M+QVkdH+Vam\H%TA4W1VB21+QVkcH%TC4W3VD1Q2+QVkc8%TE4W5VF1Q4+QVkc0%TG4W7VH1Q6+QVkb8%TI4W9VJ1Q8+QVkb@%TK4W;VL1Q:%VH1RG%W92WI1%VK2W21%VL2W<2%VN3WI21%WC261%WD291%WE2<1%WF2?1%WG2B1%WH2E1%WI2I1%WJ2L1%WK2SN1%WL2T11%WM2Q11%WN2VJ1%WO2Q81qQ>X11%X>2X21qQLX81%X@2X91qT:X@1%XB2XA1p0RB1p0SF1p0QE1pQBT;1pR0X@1pT2XG1%X<2T?1%X=2TB1%X>2TE1%X?2R61%X@2R:1%XA2R<1%XB2R@1%XC2RB1%XD2VJ1%XE2RE1%XF2RH1%XG2WC1%XH2WK1%XI2RO1qQ<XK1%Y82XL1qQJY21%Y:2Y31qT8Y:1%Y<2Y;1p0S<1p0T@1p0TC1pQ@U51pQNY:1pT0YA1%Y62U91%Y72U<1%Y82U?1%Y92UC1%Y:2UJ1%Y;2V91%Y<2V>1%Y=2VC1%Y>2VI1%Y?2VN1%Y@2W<1%YA2WB1%YB2WH1%YC2X01%YD2X61%YE2XA1%YF2XI1%YG2Y41qQ:YI1%Z62YJ1qQHZ01%Z82Z11qT6Z81%Z:2Z91").
Proof.
destruct (DOP.open_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN) as (fx5 & R5 & M5 & MS5 & INV).
destruct (open_B_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
Qed.
End UA.
End DOB.
