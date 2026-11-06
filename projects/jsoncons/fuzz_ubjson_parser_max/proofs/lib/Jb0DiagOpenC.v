(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib L5Defs L5Kn L5KnA
Jb0RegionPoisoned Jb0AsanMemcpy Jb0DiagKit Jb0DiagChk Jb0DiagMemcpy Jb0DiagStrnlen Jb0DiagGlue Jb0DiagOP Jb0DiagOpenPre.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DiagOpenC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagGlue.DG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagOpenC.DOC.UA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagOpenPre.DOP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3map"; "4Z"; "5word_to_le_bytes"; "6bvmap"]; ["0M"; "0M5"; "0ME"; "0ME2"; "0MF"; "0MX"; "0MY"; "0R"; "0R5"; "0RE"; "0RE2"; "0RF"; "0RX"; "0RY"; "7msteps"; "8agree0"]; ["9PRE17"; "9SUF1"; ":open_mid"; ";u32_at"; ";u64_at"; ";u8_at"; "<FPState"; "<getr"; "<mkst"; "<rdn"; "<seg_rom"; "=mem_grows"; ">loaded_segments"; "0S"; "?In"; "@add"]; ["@le"; "@lt"; "@of_nat"; "@pow"; "@sub"; "0a"; "0b0"; "0b1"; "0b2"; "0b3"; "0bs"; "0can"; "0fx"; "0fx'"; "0fx''"; "0fx5"]; ["0fxE"; "0fxE2"; "0fxF"; "0k"; "0p"; "AZ_to_bv"; "Abv"; "Abv_unsigned"; "0w"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module DOC.
Import DK. Import DSN. Import DG. Import AS0DIAGOP.
Lemma u8s_of_u32 : ltac2:(TCodec.tc2 tcn__Jb0DiagOpenC "R<'R6yR0%211'7y8%511%311p051'=&Q@zr6%3221&Q?r7+4%3221&QC+2+R0%3221%<251&Q3&Q<r9r8%44321<'9'4%11E&<&R7%11L&>u4&R5%12Q3;%4231%84Q1N61(2r5r4(6%11Q3%53Q431%63Q551%73Q6Q31%83Q7Q11%E3C:1'8&Q5r;r:%34N21L+1%Q:231%64Q151Q:%Q<25Q7%84Q371Q?+3%Q?281%;4Q6:1E%=241%>271%?2;1p0A1p0Q81p0Q>1p0QH1pSDQM1pSBQN1pS@QO1pS>R01pTBR11pS<R21pQ2R41").
Proof. intros M a w b0 b1 b2 b3.
intros Ha Hb C E. unfold L5.u32_at in C. unfold L5.u8_at.
destruct (word_to_le_bytes 4 (Z_to_bv 64 w)) as [|c0 [|c1 [|c2 [|c3 [|]]]]] eqn:EL; try discriminate E.
cbn [map] in E. injection E as E0 E1 E2 E3.
assert (X : forall c b, bv_unsigned c = b -> (c : byte) = Z_to_bv 8 b) by (intros c b <-; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (Jb0DiagStrlen.rdn_byte_at M a _ _ 0%nat C ltac:(lia) Ha ltac:(lia)) as R0. pose proof (Jb0DiagStrlen.rdn_byte_at M a _ _ 1%nat C ltac:(lia) Ha ltac:(lia)) as R1.
pose proof (Jb0DiagStrlen.rdn_byte_at M a _ _ 2%nat C ltac:(lia) Ha ltac:(lia)) as R2. pose proof (Jb0DiagStrlen.rdn_byte_at M a _ _ 3%nat C ltac:(lia) Ha ltac:(lia)) as R3.
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
Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 685792.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1280936.
Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 127168.
Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.
Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
Hypothesis Hal : S mod 16 = 0.
Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
Hypothesis HD : L5.defined M (S - 5440) 5440.
Hypothesis HIMG : L5.img_clear M 65536 1269760.
Hypothesis Hp : S <= p /\ p + n + 1 + 16 <= 2 ^ 47.
Hypothesis Hn : 64 <= n <= 131071.
Hypothesis HSTR : cstr M p bs t8.
Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.
Hypothesis HFMT : L5KA.zeros_at M 2147466776 8.
Hypothesis Hcan : 0 <= can < 2 ^ 64.
Hypothesis HC : diag_cells M can.
Hypothesis HSN : sn_cells M.
Hypothesis HMC : mc_icpt_globs M.
Definition PRE17 : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 127168) 17 with Some l => l | None => [] end.
Definition SUF1 : list byte := match rdn RSEGS (fun _ => None) (Z_to_bv 64 127187) 1 with Some l => l | None => [] end.
Lemma suf1_img : ltac2:(TCodec.tc2 tcn__Jb0DiagOpenC "H'9'7'4'R6y8%211%411%611&Q9&Q<yR0%811(0%118q031&R5+SlVC%2271u1%;4:521(1&Q1%22@1%G3@41"). Proof. vm_compute. reflexivity. Qed.
Lemma PRE17_eq : ltac2:(TCodec.tc2 tcn__Jb0DiagOpenC "Q<'9'4'R6y8%211%411&Q0&<'=&R5%117(2+S3+S<+S9+QJ+Q0+S1+S>+S?+SD+S@+S5(6%11@%>3A91%?3B81%@3C51%A3D71%B3E:1%C3F>1%D3G;1%E3H=1%F3I?1%G3J@1%H3KB1%I3LH1%J3ME1%K3NG1%L3OI1%M3Q0K1%N3Q1M1%Q34Q2Q6Q01%Q;3Q6Q51").
Proof. apply list_bv_eq. vm_compute. reflexivity. Qed.
Lemma SUF1_len : ltac2:(TCodec.tc2 tcn__Jb0DiagOpenC ":'9'5&3'R6y8%211&Q1%5221u1%93821"). Proof. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_open_C_tail := (ltac2:(TCodec.tc2 tcn__Jb0DiagOpenC "ZB'Q6&?y5'R6yR0%211%5241'7y8%611%311p061&Q2vGv@vQ=vR4vQKvQJr2r1%9887654321':'8'N&Q<&Q8r7r6&R5+QSkX@%22K1r5&Q:%119%9587431r3+QSdYL%92Q21%=53D1C5%@3?51'9&Q7&QBuA%211%A2Q<1%52L1+R2%D2Q=1%93Q=31u:%911%H2QC1%<2Q31+2%K2QD1%@3QD31u;%@11%O2QJ1%C2Q:1&QD+QS8%22QA1%Q42QM1%I3QM51u<%I11%Q82R31%L2QC1%N3R21?u9%N11%Q=2R81%Q12QH1+QWRm8%Q@2R91%Q53R931uB%Q511%QD2R?1%Q82QO1%Q:3R>1KuC%Q:11%QI2RD1%Q=2R41%Q?3RC1GuF%Q?11%QN2RI1%QB2R91&Q?&3%12RFR=%QE11+A%5221%R62RO1%QK3RO81&Q4+^@%Q92RH1%34R?RDQ81+QS0%Q<2RK1%64RBRG1:+QRH%Q?2RN1%94RERJ1RN+QR@%QB2S11%<4RHRM1A'4%11S:%S=11&Q9%RI2SB?%24RNS31R;(1&Q0%2271%RB3741%RO2SHS<%84S4S91N%62;S<%RF3;21&Q3+QWSQ0%24S9S>1R;&O%13SFS@SE&Q;%12SHSBpTDT2SM&;&Q@&R7%12T7SG%32R<1&QA+QR8%RA2T01%3251%SJ251%:11%S?1T0%SH1T1%S<3T;21p041pTDTB1%C2SHT5'5&Q>(2u2u3u4u8uEuGuHuIuJuK(6%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ES61%D3F@1%E3GB1%F3HD1%G3IF1%I3JTO1%T91U1%TH2UC1%T<2TJ1r9%T>213%T@3UD31p071pT8Q21r8+QSdZ8%U12UJ1%U55831U4TM%U83U71TI+b8%T42UC1%U62UO1%TK3UOT71%TL3V0S>2+1%U:2V31%TO3V3S<1%S44U@UE7S2+b0%T=2UL1%S74UCUH16+aH%T@2UO1z%S;4UGUL21+a@%TD2V31%S>4UJUO14u1%S04ULV1RO1&Q1%RO2S41%U?3S431%R@2GR>+a8%TM2V<1%R?2RA1%V6241%RF11p01R:pTDVK1+QRejL%V52VN1%V95UOV@1V?V1%V<3V;Q51%UJ1R9%V92W41%UM2VD1%V;2W4VI%V03W421+5%S;4VBVGTO1+QWSP8%T84VDVI1N+QWSP0+VbTfH%T;4VGVL21+QWRo0%T=4VIVN1Q3+QWRn@%T?4VKW01Q5+QWRn8%TA4VMW21Q7+QWRm@%TC4VOW41Q9+QWRmH%TE4W1W61Q;%V@1RM%VO2WJ1%VC2W:1%VD2WA2%VF3WJ21%W9261%W:291%W;2<1%W<2?1%W=2B1%W>2E1%W?2I1%W@2L1%WA2T21%WB2T51%WC2Q11%WD2VB1%WE2Q81qQ:X21%WH2X31qQHX91%WJ2X:1qT6XA1%WL2XB1p0RH1p0SL1p0QE1pQ>T?1pQLXA1pSNXH1%X22TC1%X32TF1%X42TI1%X52R41%X62R:1%X72R>1%X82RC1%X92RG1%X:2RI1%X;2RM1%X<2V@1%X=2VF1%X>2VN1%X?2S21%X@2W>1%XA2WF1%XB2S91qQ8XO1%XE2Y01qQFY61%XG2Y71qT4Y>1%XI2Y?1p0SE1p0TI1p0TK1pQ<U<1pQJY>1pSLYE1%XO2U@1%Y02UC1%Y12UF1%Y22UJ1%Y32UO1%Y42V:1%Y52V>1%Y62VB1%Y72VF1%Y82VK1%Y92W81%Y:2W>1%Y;2WD1%Y<2WL1%Y=2X21%Y>2X<1%Y?2XD1%Y@2XO1qQ6YM1%YC2YN1qQDZ41%YE2Z51qT2Z<1%YG2Z=1p0YI1pQ4Z41pQBZ:1pT0ZA1")) (only parsing).
Variable fx5 : ltac:(sec_ty2 constr:(SEC_T_open_C_tail) 0%nat 0%nat).
Variable R5 : ltac:(sec_ty2 constr:(SEC_T_open_C_tail) 1%nat 0%nat).
Variable M5 : ltac:(sec_ty2 constr:(SEC_T_open_C_tail) 2%nat 0%nat).
Theorem open_C_tail : ltac:(sec_stmt2 constr:(SEC_T_open_C_tail) 3%nat 0%nat).
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
assert (IMG5 : L5.img_clear M5 65536 1269760) by (apply (imgc_ext M M5); [intros x Hx; apply A05; flia | lia | lia | exact HIMG]).
cfeed P (doDl_conc fx5 R5 M5 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | 40%nat => can | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.
assert (AG58 : forall x : word, bv_unsigned x < S - 1136 \/ S - 1024 <= bv_unsigned x -> M8 x = M5 x) by (intros x Hx; apply FR8; lia).
assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG58 by lia; apply A05; assumption).
assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (NE : Z.eqb (S - 447) (S - 464) = false) by (apply Z.eqb_neq; lia).
destruct (wv_entry_stage fx8 R8 M8 1280936 (S - 1136) p n (S - 447) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG8W & MGW);
[ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
rewrite NE in W11, W12, W18, W19.
assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG8W by lia; apply A08; assumption).
assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
assert (AG5W : forall x : word, S - 1024 <= bv_unsigned x -> MW x = M5 x) by (intros x Hx; rewrite AG8W by lia; apply AG58; lia).
assert (P17_5 : rdn RSEGS M5 (Z_to_bv 64 (S - 464)) 17 = Some PRE17).
{ rewrite PRE17_eq. cbn [map].
destruct (u8s_of_u32 M5 (S - 464) 979987555 99 108 105 58) as (B0 & B1 & B2 & B3); [lia | lia | assumption | vm_compute; reflexivity|].
destruct (u8s_of_u32 M5 (S - 460) 1851876128 32 99 97 110) as (B4 & B5 & B6 & B7); [lia | lia | assumption | vm_compute; reflexivity|].
destruct (u8s_of_u32 M5 (S - 456) 544501614 110 111 116 32) as (B8 & B9 & B10 & B11); [lia | lia | assumption | vm_compute; reflexivity|].
destruct (u8s_of_u32 M5 (S - 452) 1852141679 111 112 101 110) as (B12 & B13 & B14 & B15); [lia | lia | assumption | vm_compute; reflexivity|].
ring_simplify (S - 464 + 1) in B1. ring_simplify (S - 464 + 2) in B2. ring_simplify (S - 464 + 3) in B3.
ring_simplify (S - 460 + 1) in B5. ring_simplify (S - 460 + 2) in B6. ring_simplify (S - 460 + 3) in B7.
ring_simplify (S - 456 + 1) in B9. ring_simplify (S - 456 + 2) in B10. ring_simplify (S - 456 + 3) in B11.
ring_simplify (S - 452 + 1) in B13. ring_simplify (S - 452 + 2) in B14. ring_simplify (S - 452 + 3) in B15.
rdn_bytes. }
assert (P7W : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 17 = Some PRE17) by (apply (rdn_xfer M5 MW); [intros x Hx; apply AG5W; cbn in Hx; lia | lia | cbn; lia | exact P17_5]).
assert (STRW : cstr MW p bs t8) by (apply (cstr_ext M MW); [lia | lia | intros x Hx; apply A0W; flia | exact HSTR]).
assert (RDSW : rdn RSEGS MW (Z_to_bv 64 p) (length bs) = Some bs).
{ destruct STRW as [A _ _]. rewrite (SeqExec.rdn_firstn RSEGS MW _ _ _ (length bs) A) by lia. f_equal. rewrite firstn_app, firstn_all2 by lia. rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
exists fx8, RW, MW.
split. { eapply msteps_trans; [exact MS8|]. exact MSW. }
split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
split; [replace (S - 1128) with (S - 1136 + 8) by lia; exact I0|]. split; [replace (S - 447 - (S - 464)) with 17 in I1 by lia; replace (S - 1120) with (S - 1136 + 16) by lia; exact I1|].
split; [replace (S - 1112) with (S - 1136 + 24) by lia; exact I2|]. split; [replace (S - 1104) with (S - 1136 + 32) by lia; exact I3|].
split; [exact P7W|]. split; [exact RDSW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
intros fx' RX MX AGXW MGXW KXW.
assert (AGX8 : forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = M8 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG8W; lia).
assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R8 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
assert (AGX5 : forall x : word, S - 1024 <= bv_unsigned x -> MX x = M5 x) by (intros x Hx; rewrite AGX8 by lia; apply AG58; lia).
assert (AGX5s : forall x : word, bv_unsigned x < 2 ^ 32 -> MX x = M5 x) by (intros x Hx; rewrite AGX8 by lia; apply AG58; lia).
assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
assert (IMGX : L5.img_clear MX 65536 1269760) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
assert (FWX : L5.writable RSEGS MX 1280936 152) by (eapply writable_grows; eassumption).
assert (SKX : L5KA.zeros_at MX (SB + S / 8 - 680) 688).
{ apply (zeros_ext M MX); [intros x Hx; apply AGX0; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
assert (F8X : L5.u8_at RSEGS MX 1280936 5) by (apply u8_of_u32_5; [lia | lia|]; scc).
cfeed P (doEc_conc fx' RX MX (fun j => match j with 2%nat => S - 1136 | 33%nat => p | 34%nat => n | 40%nat => can
| 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
| 122%nat => U RX 22 | 123%nat => U RX 23 | 125%nat => U RX 25 | 127%nat => U RX 27 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fx9 R9 M9 MG9 FR9 FZ9 MS9 KS9.
assert (AGX9 : forall x : word, bv_unsigned x < S - 3248 \/ S - 448 <= bv_unsigned x -> ~ (1280968 <= bv_unsigned x < 1280984) -> ~ (1280992 <= bv_unsigned x < 1281000) -> M9 x = MX x) by (intros x Hx Hf1 Hf2; apply FR9; lia).
assert (A09 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M9 x = M x) by (intros x Hx Hf; rewrite AGX9 by (unfold filew in Hf; lia); apply AGX0; assumption).
assert (MG09 : mem_grows M M9) by (eapply mem_grows_trans; eassumption).
assert (W9 : L5.writable RSEGS M9 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (AG59s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1280968 <= bv_unsigned x < 1280984) -> ~ (1280992 <= bv_unsigned x < 1281000) -> M9 x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGX9 by lia; apply AGX5s; lia).
assert (NE2 : Z.eqb (S - 463) (S - 464) = false) by (apply Z.eqb_neq; lia).
destruct (wv_entry_stage fx9 R9 M9 1280936 (S - 592) 0 0 (S - 463) (S - 464) 2) as (RW2 & MW2 & MSW2 & X17 & X10 & X11 & X12 & X18 & X19 & X22 & KSW2 & J0 & J1 & J2 & J3 & AG9W & MGW2);
[ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
rewrite NE2 in X11, X12, X18, X19.
assert (A0W2 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW2 x = M x) by (intros x Hx Hf; rewrite AG9W by lia; apply A09; assumption).
assert (MG0W2 : mem_grows M MW2) by (eapply mem_grows_trans; eassumption).
assert (SUFW : rdn RSEGS MW2 (Z_to_bv 64 (S - 464)) 1 = Some SUF1).
{ replace SUF1 with [Z_to_bv 8 10 : byte] by (symmetry; apply list_bv_eq; vm_compute; reflexivity).
assert (C10 : L5.u8_at RSEGS MW2 (S - 464) 10) by (eapply (u8_ext M9); [intros x Hx; apply AG9W; lia | lia | lia |]; match goal with |- _ _ _ ?a _ => try (progress (ring_simplify a)) end; assumption).
exact C10. }
exists fx9, RW2, MW2.
split. { eapply msteps_trans; [exact MS9|]. exact MSW2. }
split; [exact X17|]. split; [exact X10|]. split; [rewrite X11; f_equal; lia|]. split; [exact X12|].
split; [rewrite (KSW2 9%nat) by (cbn; tauto); sc|]. split; [exact X18|]. split; [rewrite X19; f_equal; lia|]. split; [rewrite X22; f_equal; lia|].
split; [replace (S - 584) with (S - 592 + 8) by lia; exact J0|]. split; [replace (S - 463 - (S - 464)) with 1 in J1 by lia; replace (S - 576) with (S - 592 + 16) by lia; exact J1|].
split; [replace (S - 568) with (S - 592 + 24) by lia; exact J2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact J3|].
split; [exact SUFW|]. split; [scc|]. split; [exact A0W2|]. split; [exact MG0W2|].
intros fx'' RY MY AGYW MGYW KYW.
assert (AGY9 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = M9 x) by (intros x Hx; rewrite AGYW by exact Hx; apply AG9W; lia).
assert (KY : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr R9 (reg k)) by (intros k Hk; rewrite (KYW k Hk); apply KSW2; cbn in Hk |- *; tauto).
assert (AGYX : forall x : word, S - 448 <= bv_unsigned x -> MY x = MX x) by (intros x Hx; rewrite AGY9 by lia; apply AGX9; lia).
assert (AGY5 : forall x : word, S - 448 <= bv_unsigned x -> MY x = M5 x) by (intros x Hx; rewrite AGYX by lia; apply AGX5; lia).
assert (AGY5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1280968 <= bv_unsigned x < 1280984) -> ~ (1280992 <= bv_unsigned x < 1281000) -> MY x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGY9 by lia; apply AG59s; assumption).
assert (AGY0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MY x = M x) by (intros x Hx Hf; rewrite AGYW by lia; apply A0W2; assumption).
assert (MG0Y : mem_grows M MY) by (eapply mem_grows_trans; eassumption).
assert (WY : L5.writable RSEGS MY (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (DY : L5.defined MY (S - 5440) 5440) by (eapply defined_grows; eassumption).
assert (IMGY : L5.img_clear MY 65536 1269760) by (apply (imgc_ext M MY); [intros x Hx; apply AGY0; flia | lia | lia | exact HIMG]).
assert (FWY : L5.writable RSEGS MY 1280936 152) by (eapply writable_grows; eassumption).
cfeed P (doGc_conc fx'' RY MY (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
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
Theorem open_C : ltac2:(TCodec.tc2 tcn__Jb0DiagOpenC "Z<':'Q6&?y5'R6yR0%211%5241'7y8%611%311p061'8'N&Q<&Q8vQLvG&R5+\[YD%22@1v@&Q:%119%9587431r3r2+QSdYL%:2H1r1%?554217%B3A71'9&Q7&QBuA%211%C2Q31%52<1+R2%F2Q41%93Q431u:%911%J2Q:1%<2C1+2%M2Q;1%@3Q;31u;%@11%Q12QA1%C2J1&QDvQ=+QS8%3221%Q72QE1%J3QE61u<%J11%Q;2QK1%M2Q41%O3QJ1@u9%O11%Q@2R01%Q22Q91+QWRm8%QC2R11%Q63R131uB%Q611%QG2R71%Q92Q@1%Q;3R61LuC%Q;11%QL2R<1%Q>2QE1%Q@3R;1GuF%Q@11%R12RA1%QC2QJ1&Q?&3vQJ%22R?1%QG11+A%6221%R:2RH1%QM3RH91&Q4+^@%Q;2Q:1%34RCR4Q91+QS0%Q>2Q=1%64RFR71:+QRH%QA2Q@1vR4%:4RJR;21+QR@%QE2QD1%=4RMR>1B'4%11S4%S711&Q9%RN2S<@%24S3RD1R>(1&Q0%2271%RE3741%S42SB?%84S9RJ1O%62;Q1%RI3;21&Q3+QWSQ0%24S>RO1R>&O%13S9S1R8&Q;%12S;S3pTDSLSG&;&Q@&R7%12T1S8%32R>1&QA+QR8%RD2RC1%3251%SO251%:11%SD1SCr6%11SE%S@3T631p051pTDT=1r5%E21SJ'5&Q>(2u2u3u4u8uEuGuHuIuJuK(6%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ES:1%D3F@1%E3GB1%F3HD1%G3IF1%I3JTB1%T>1TF%TO2U?1%TA2Q41r9%TC213%TE3U@31p071pT8Q21r8+QSdZ8%U82UF1r7%U=59421U5%U@3U?1TO+b8%T:2T91%U>2UL1%U13ULT=1%U23UMSC2+1%UB2V01%U53V0SA1%S84UHU97S6+b0%TC2TB1%S;4UKU<16+aH%TF2TE1z%S?4UOU@21+a@%TJ2TI1%SB4V2UC14u1%S34V4UES21&Q1%S22S71%UE3S731%RC2GRA+a8%U32U21%RB2RD1%V>241%RI11p01R<pTDVH1+QRejL%V=2VK1%VA5V7V61V3V9%VD3VCQ51%V01R:%VA2W11%V32V:1%VC2W1U?%V63W121+5%S>4VJV;U41+QWSP8%T<4VLV=1N+QWSP0+VbTfH%T?4VOV@21+QWRo0%TA4W1VB1Q3+QWRn@%TC4W3VD1Q5+QWRn8%TE4W5VF1Q7+QWRm@%TG4W7VH1Q9+QWRmH%TI4W9VJ1Q;%VF1RN%W72WG1%VI2W01%VJ2W:2%VL3WG21%WA261%WB291%WC2<1%WD2?1%WE2B1%WF2E1%WG2I1%WH2L1%WI2T51%WJ2T81%WK2Q11%WL2VH1%WM2Q81qQ:WO1%X<2X01qQHX61%X>2X71qT6X>1%X@2X?1p0RI1p0SM1p0QE1pQ>TB1pQLX>1pSNXE1%X:2TF1%X;2TI1%X<2TL1%X=2R41%X>2R:1%X?2R>1%X@2RC1%XA2RG1%XB2RI1%XC2RM1%XD2VE1%XE2VK1%XF2W31%XG2S21%XH2WD1%XI2WL1%XJ2S91qQ8XL1%Y92XM1qQFY31%Y;2Y41qT4Y;1%Y=2Y<1p0SF1p0TJ1p0TM1pQ<U?1pQJY;1pSLYB1%Y72UC1%Y82UF1%Y92UI1%Y:2UM1%Y;2V21%Y<2V=1%Y=2VA1%Y>2VF1%Y?2VJ1%Y@2VO1%YA2W=1%YB2WC1%YC2WI1%YD2X11%YE2X71%YF2XB1%YG2XJ1%YH2Y51qQ6YJ1%Z72YK1qQDZ11%Z92Z21qT2Z91%Z;2Z:1").
Proof.
destruct (DOP.open_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN) as (fx5 & R5 & M5 & MS5 & INV).
destruct (open_C_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
Qed.
End UA.
End DOC.
