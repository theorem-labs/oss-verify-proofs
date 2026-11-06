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
Ltac2 tcn__Jb0DiagOpenA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagGlue.DG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagOpenA.DOA.UA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagOpenPre.DOP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3add"; "4map"; "5Z"]; ["6word_to_le_bytes"; "7bvmap"; "0M"; "0M5"; "0ME"; "0MF"; "0MX"; "0R"; "0R5"; "0RE"; "0RF"; "0RX"; "8msteps"; "9agree0"; ":PRE17"; ":SUF1"]; [";open_mid"; "<u32_at"; "<u64_at"; "<u8_at"; "=FPState"; "=getr"; "=mkst"; "=rdn"; "=seg_rom"; ">mem_grows"; "?loaded_segments"; "0S"; "@In"; "Aadd"; "Ale"; "Alt"]; ["Aof_nat"; "Apow"; "Asub"; "0a"; "0b0"; "0b1"; "0b2"; "0b3"; "0bs"; "0can"; "0fx"; "0fx'"; "0fx5"; "0fxE"; "0fxF"; "0k"]; ["0p"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0w"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module DOA.
Import DK. Import DSN. Import DG. Import AS0DIAGOP.
Lemma u8s_of_u32 : ltac2:(TCodec.tc2 tcn__Jb0DiagOpenA "R<'R2yR0%211'8y8%511%311p051'?&Q>zr6%3221&Q=r7+4%3221&QA+2+R0%3221%<251&Q1&Q:r9r8%44321<':'5%11E&>&R3%11L&@u4&R1%12Q3;%4231%84Q1N61(3r5r4(7%11Q3%53Q431%63Q551%73Q6Q31%83Q7Q11%E3C:1'9&Q3r;r:%34N21L+1%Q:231%64Q151Q:%Q<25Q7%84Q371Q?+3%Q?281%;4Q6:1E%=241%>271%?2;1p0A1p0Q81p0Q>1p0QH1pS@QM1pS>QN1pS<QO1pS:R01pT:R11pS8R21pQ6R41").
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
Hypothesis Hn : n <= 62.
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
Lemma suf1_img : ltac2:(TCodec.tc2 tcn__Jb0DiagOpenA "H':'8'5'R2y8%211%411%611&Q7&Q:yR0%811(0%118q031&R1+SlVC%2271u1%;4:521(1&O%22@1%G3@41"). Proof. vm_compute. reflexivity. Qed.
Lemma PRE17_eq : ltac2:(TCodec.tc2 tcn__Jb0DiagOpenA "Q<':'5'R2y8%211%411&N&>'?&R1%117(3+S3+S<+S9+QJ+Q0+S1+S>+S?+SD+S@+S5(7%11@%>3A91%?3B81%@3C51%A3D71%B3E:1%C3F>1%D3G;1%E3H=1%F3I?1%G3J@1%H3KB1%I3LH1%J3ME1%K3NG1%L3OI1%M3Q0K1%N3Q1M1%Q34Q2Q6Q01%Q;3Q6Q51").
Proof. apply list_bv_eq. vm_compute. reflexivity. Qed.
Lemma SUF1_len : ltac2:(TCodec.tc2 tcn__Jb0DiagOpenA ":':'6&4'R2y8%211&O%5221u1%93821"). Proof. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_open_A_tail := (ltac2:(TCodec.tc2 tcn__Jb0DiagOpenA "XH'Q4&Ay5'R2yR0%211%5241'8y8%611%311p061&Q0vGvBvQ;vR0vQIvQHr2r1%9887654321';'9'L&Q:&Q6r7r6&R1+QSkX@%22K1r5&Q8%119%9587431r3+QSdYL%92Q21%=53D1C5%@3?51':&Q5&Q@uA%211%A2Q<1%52L1+R2%D2Q=1%93Q=31u:%911%H2QC1%<2Q31+2%K2QD1%@3QD31u;%@11%O2QJ1%C2Q:1&QB+b8%22QA1%Q42QM1%I3QM51u<%I11%Q82R31%L2QC1%N3R21?u9%N11%Q=2R81%Q12QH1+QWRm8%Q@2R91%Q53R931uB%Q511%QD2R?1%Q82QO1%Q:3R>1KuC%Q:11%QI2RD1%Q=2R41%Q?3RC1GuF%Q?11%QN2RI1%QB2R91&Q=&4%12RFR=%QE11+B%5221%R62RO1%QK3RO81&Q2+^@%Q92RH1%34R?RDQ81+b0%Q<2RK1%64RBRG19+aH%Q?2RN1z%:4RFRK21+a@%QC2S21%=4RIRN14'5%11S;%S>11&Q7%RJ2SC@&=u1%22K1%32R?1%64S3S851(1&2&N&O%33SHS?1%43SI31%62?1%RK3?81&Q1+QWSQ0%24S>SC1R@&M%13SKSESJ&Q9%12SMSGpT<T7T2&<&Q>&R3%12T<SL%32RA1&Q?+a8%RF2T51%3251%SO251%:11%SD1T5%SM1T6%SA3T@21p041pT<TG1%C2SMT:'6&Q<(3u2u3u4u8uEuGuHuIuJuK(7%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ES;1%D3F@1%E3GB1%F3HD1%G3IF1%I3JU41%T>1U6%TM2UH1%TA2TO1r9%TC213%TE3UI31p071pT0Q21r8+QSdZ8%U62UO1%U:5831U9U2+QRejL%U92V21%U=5U3UD1UCU5%U@3U?41%TN1Q8%U=2V81%U12UH1%U?2V8UM%U43V821+5%R:4UFUKT31+QWSP8%S<4UHUM1S3+QWSP0+VbTfH%S?4UKV021+QWRo0%SA4UMV21S8+QWRn@%SC4UOV41S:+QWRn8%SE4V1V61S<+QWRm@%SG4V3V81S>+QWRmH%SI4V5V:1S@%UD1QL%V32VN1%UG2V>1%UH2VE2%UJ3VN21%V=261%V>291%V?2<1%V@2?1%VA2B1%VB2E1%VC2I1%VD2L1%VE2S11%VF2S41%VG2Q11%VH2UF1%VI2Q81qQ<W61%VL2W71qQFW=1%VN2W>1qSNWE1%W02WF1p0QG1p0RK1p0RM1pQ>S>1pQHWE1pSHWL1%W62SB1%W72SE1%W82SH1%W92SL1%W:2T?1%W;2TC1%W<2TH1%W=2TL1%W>2U11%W?2U>1%W@2UD1%WA2UJ1%WB2V21%WC2V81%WD2VB1%WE2VJ1%WF2W51qQ:X31%WI2X41qQDX:1%WK2X;1qSLXB1%WM2XC1p0WO1pQ8X:1pQBX@1pSJXG1")) (only parsing).
Variable fx5 : ltac:(sec_ty2 constr:(SEC_T_open_A_tail) 0%nat 0%nat).
Variable R5 : ltac:(sec_ty2 constr:(SEC_T_open_A_tail) 1%nat 0%nat).
Variable M5 : ltac:(sec_ty2 constr:(SEC_T_open_A_tail) 2%nat 0%nat).
Theorem open_A_tail : ltac:(sec_stmt2 constr:(SEC_T_open_A_tail) 3%nat 0%nat).
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
assert (IMG7 : L5.img_clear M7 65536 1269760) by (apply (imgc_ext M M7); [intros x Hx; apply A07; flia | lia | lia | exact HIMG]).
assert (FW7 : L5.writable RSEGS M7 1280936 152) by (eapply writable_grows; eassumption).
assert (AG67' : forall x : word, S - 1088 <= bv_unsigned x -> ~ (S - 447 <= bv_unsigned x < S - 447 + n) -> M7 x = M6 x) by (intros x Hx Hd; apply AG67; [lia | exact Hd]).
assert (AG57 : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 447 <= bv_unsigned x < S - 447 + n) -> M7 x = M5 x) by (intros x Hx Hd; rewrite AG67' by (first [exact Hd | lia]); apply AG56; lia).
assert (AG57s : forall x : word, bv_unsigned x < 2 ^ 32 -> M7 x = M5 x) by (intros x Hx; rewrite AG67 by lia; apply AG56; lia).
assert (F87 : L5.u8_at RSEGS M7 1280936 5).
{ apply u8_of_u32_5; [lia | lia|]. scc. }
cfeed P (doEa_conc fx6 R7 M7 (fun j => match j with 2%nat => S - 1088 | 33%nat => p | 34%nat => n | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.
assert (AG78 : forall x : word, bv_unsigned x < S - 1104 \/ S - 1024 <= bv_unsigned x -> ~ (1280976 <= bv_unsigned x < 1280984) -> M8 x = M7 x) by (intros x Hx Hf; apply FR8; lia).
assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG78 by (unfold filew in Hf; lia); apply A07; assumption).
assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (IMG8 : L5.img_clear M8 65536 1269760) by (apply (imgc_ext M M8); [intros x Hx; apply A08; flia | lia | lia | exact HIMG]).
assert (HSN8 : sn_cells M8) by (apply (sn_cells_agree M M8 S); [lia | exact A08 | exact HSN]).
assert (HMC8 : mc_icpt_globs M8) by (apply (mc_globs_agree M M8 S); [lia | exact A08 | exact HMC]).
assert (SK8 : L5KA.zeros_at M8 (SB + S / 8 - 680) 688).
{ apply (zeros_ext M M8); [intros x Hx; apply A08; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
assert (FMT8 : L5KA.zeros_at M8 2147466776 8) by (apply (zeros_ext M M8); [intros x Hx; apply A08; flia | lia | lia | exact HFMT]).
assert (RDF8 : rdn RSEGS M8 (Z_to_bv 64 127187) (length SUF1) = Some SUF1).
{ rewrite SUF1_len. rewrite (rdn_img M8 65536 1269760) by (first [exact IMG8 | cbn; lia | lia]). exact suf1_img. }
destruct (memcpy_stage fx8 R8 M8 (S - 1088) (S - 447 + n) 127187 1 SUF1) as (R9 & M9 & MS9 & V9 & KS9 & AG89 & MG9 & RD9);
[ sc | sc | sc | sc | sc | reflexivity | lia | lia | lia | (left; unfold LOWEND; lia) | (right; unfold HIGHBEG, HIGHEND; lia) | lia | lia | lia | lia | lia
| dk_gmem | (apply (L5.writable_sub RSEGS M8 (S - 5440) 5440); [exact W8 | lia | lia]) | exact RDF8 | (destruct HSN8 as (_ & _ & _ & G & _); exact G) | exact HMC8
| | (apply (stk_zsh M8 S); [exact Hal | lia | exact SK8 | lia | lia | lia]) | ].
{ intros x Hx. unfold SB in Hx. change ((2147450880 + 127187 / 8) - (2147450880 + 127187 / 8) mod 8) with 2147466776 in Hx.
change ((2147450880 + (127187 + 1 - 1) / 8) - (2147450880 + (127187 + 1 - 1) / 8) mod 8 + 8) with 2147466784 in Hx.
specialize (FMT8 (bv_unsigned x - 2147466776) ltac:(lia)). replace (2147466776 + (bv_unsigned x - 2147466776)) with (bv_unsigned x) in FMT8 by lia.
rewrite Z_to_bv_bv_unsigned in FMT8. exact FMT8. }
assert (A09 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M9 x = M x) by (intros x Hx Hf; rewrite AG89 by lia; apply A08; assumption).
assert (MG09 : mem_grows M M9) by (eapply mem_grows_trans; eassumption).
assert (W9 : L5.writable RSEGS M9 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (D9 : L5.defined M9 (S - 5440) 5440) by (eapply defined_grows; eassumption).
assert (IMG9 : L5.img_clear M9 65536 1269760) by (apply (imgc_ext M M9); [intros x Hx; apply A09; flia | lia | lia | exact HIMG]).
assert (FW9 : L5.writable RSEGS M9 1280936 152) by (eapply writable_grows; eassumption).
assert (AG89h : forall x : word, S - 1088 <= bv_unsigned x -> ~ (S - 447 + n <= bv_unsigned x < S - 446 + n) -> M9 x = M8 x) by (intros x Hx Hd; apply AG89; lia).
assert (AG89s : forall x : word, bv_unsigned x < 2 ^ 32 -> M9 x = M8 x) by (intros x Hx; apply AG89; lia).
assert (AG79h : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 447 + n <= bv_unsigned x < S - 446 + n) -> M9 x = M7 x) by (intros x Hx Hd; rewrite AG89h by (first [exact Hd | lia]); apply AG78; lia).
assert (AG59h : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 447 <= bv_unsigned x < S - 446 + n) -> M9 x = M5 x) by (intros x Hx Hd; rewrite AG79h by lia; apply AG57; lia).
assert (AG59s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1280976 <= bv_unsigned x < 1280984) -> M9 x = M5 x).
{ intros x Hx Hf. rewrite AG89s by lia. rewrite AG78 by lia. apply AG57s; lia. }
cfeed P (doFa_conc fx8 R9 M9 (fun j => match j with 2%nat => S - 1088 | 33%nat => p | 34%nat => n | 40%nat => can
| 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
| 123%nat => U R9 23 | 124%nat => U R9 24 | 125%nat => U R9 25 | 127%nat => U R9 27 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fxE RE ME MGE FRE FZE MSE KSE.
assert (AG9E : forall x : word, bv_unsigned x < S - 1104 \/ S - 464 <= bv_unsigned x -> ~ (1280976 <= bv_unsigned x < 1280984) -> ME x = M9 x) by (intros x Hx Hf; apply FRE; lia).
assert (A0E : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> ME x = M x) by (intros x Hx Hf; rewrite AG9E by (unfold filew in Hf; lia); apply A09; assumption).
assert (MG0E : mem_grows M ME) by (eapply mem_grows_trans; eassumption).
assert (BUF : rdn RSEGS ME (Z_to_bv 64 (S - 464)) (17 + (length bs + 1)) = Some (PRE17 ++ bs ++ SUF1)).
{ assert (AG7Eb : forall x : word, S - 447 <= bv_unsigned x < S - 447 + n -> ME x = M7 x) by (intros x Hx; rewrite AG9E by lia; apply AG79h; lia).
assert (AG9Eb : forall x : word, S - 447 + n <= bv_unsigned x < S - 446 + n -> ME x = M9 x) by (intros x Hx; apply AG9E; lia).
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
assert (AG5Eb17 : forall x : word, S - 464 <= bv_unsigned x < S - 447 -> ME x = M5 x) by (intros x Hx; rewrite AG9E by lia; apply AG59h; lia).
assert (P7 : rdn RSEGS ME (Z_to_bv 64 (S - 464)) 17 = Some PRE17) by (apply (rdn_xfer M5 ME); [intros x Hx; apply AG5Eb17; cbn in Hx; lia | lia | cbn; lia | exact P17_5]).
assert (PB : rdn RSEGS ME (Z_to_bv 64 (S - 447)) (length bs) = Some bs) by (apply (rdn_xfer M7 ME); [intros x Hx; apply AG7Eb; lia | lia | lia | exact RD7]).
assert (PS : rdn RSEGS ME (Z_to_bv 64 (S - 447 + n)) 1 = Some SUF1).
{ apply (rdn_xfer M9 ME); [intros x Hx; apply AG9Eb; cbn in Hx; lia | lia | cbn; lia | rewrite SUF1_len in RD9; exact RD9]. }
apply rdn_app_Z; [lia | lia | exact P7|]. replace (S - 464 + Z.of_nat 17) with (S - 447) by lia.
apply rdn_app_Z; [lia | lia | exact PB | exact PS]. }
assert (WE : L5.writable RSEGS ME (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (AG5Es : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1280976 <= bv_unsigned x < 1280984) -> ME x = M5 x) by (intros x Hx Hf; rewrite AG9E by lia; apply AG59s; assumption).
assert (NE : Z.eqb (S - 446 + n) (S - 464) = false) by (apply Z.eqb_neq; lia).
destruct (wv_entry_stage fxE RE ME 1280936 (S - 592) 0 0 (S - 446 + n) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AGEW & MGW);
[ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
rewrite NE in W11, W12, W18, W19.
assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AGEW by lia; apply A0E; assumption).
assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
assert (BUFW : rdn RSEGS MW (Z_to_bv 64 (S - 464)) (17 + (length bs + 1)) = Some (PRE17 ++ bs ++ SUF1)).
{ apply (rdn_xfer ME MW); [intros x Hx; apply AGEW; lia | lia | lia | exact BUF]. }
exists fxE, RW, MW.
split. { eapply msteps_trans; [exact MS6|]. eapply msteps_trans; [exact MS7|]. eapply msteps_trans; [exact MS8|].
eapply msteps_trans; [exact MS9|]. eapply msteps_trans; [exact MSE|]. exact MSW. }
split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
split; [replace (S - 584) with (S - 592 + 8) by lia; exact I0|]. split; [replace (S - 576) with (S - 592 + 16) by lia; replace (n + 18) with (S - 446 + n - (S - 464)) by lia; exact I1|].
split; [replace (S - 568) with (S - 592 + 24) by lia; exact I2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact I3|].
split; [exact BUFW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
intros fx' RX MX AGXW MGXW KXW.
assert (AGX : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = ME x) by (intros x Hx; rewrite AGXW by exact Hx; apply AGEW; lia).
assert (MGX : mem_grows ME MX) by (eapply mem_grows_trans; eassumption).
assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
assert (AGX9 : forall x : word, S - 464 <= bv_unsigned x -> ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = M9 x) by (intros x Hx Hd; rewrite AGX by exact Hd; apply AG9E; lia).
assert (AGX5 : forall x : word, S - 384 <= bv_unsigned x -> MX x = M5 x) by (intros x Hx; rewrite AGX9 by lia; apply AG59h; lia).
assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGX by lia; apply A0E; assumption).
assert (AGX5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1280976 <= bv_unsigned x < 1280984) -> MX x = M5 x).
{ intros x Hx Hf. rewrite AGX by lia. rewrite AG9E by lia. apply AG59s; assumption. }
assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
assert (IMGX : L5.img_clear MX 65536 1269760) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
assert (FWX : L5.writable RSEGS MX 1280936 152) by (eapply writable_grows; eassumption).
cfeed P (doGa_conc fx' RX MX (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
| 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
| 118%nat => U RX 18 | 119%nat => U RX 19 | 120%nat => U RX 20 | 122%nat => U RX 22 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc]).
dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
exists fxF, RF, MF.
split; [exact MSF|].
split; [sc|].
split; [sc|].
split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. rewrite AGX by lia. apply A0E; [exact Hx | unfold filew; lia]. }
split; [eapply mem_grows_trans; [exact MG0E|]; eapply mem_grows_trans; [exact MGX | exact MGF]|].
repeat split; first [sc | (eapply (DK.u64_ext M5); [intros x Hx; rewrite FRF by lia; apply AGX5s; lia | lia | lia | eassumption]) | dk_rk].
Qed.
End SE.
Theorem open_A : ltac2:(TCodec.tc2 tcn__Jb0DiagOpenA "XA';'Q4&Ay5'R2yR0%211%5241'8y8%611%311p061'9'L&Q:&Q6vQJvG&R1+\[YD%22@1vB&Q8%119%9587431r3r2+QSdYL%:2H1r1%?554217%B3A71':&Q5&Q@uA%211%C2Q31%52<1+R2%F2Q41%93Q431u:%911%J2Q:1%<2C1+2%M2Q;1%@3Q;31u;%@11%Q12QA1%C2J1&QBvQ;+b8%3221%Q72QE1%J3QE61u<%J11%Q;2QK1%M2Q41%O3QJ1@u9%O11%Q@2R01%Q22Q91+QWRm8%QC2R11%Q63R131uB%Q611%QG2R71%Q92Q@1%Q;3R61LuC%Q;11%QL2R<1%Q>2QE1%Q@3R;1GuF%Q@11%R12RA1%QC2QJ1&Q=&4vQH%22R?1%QG11+B%6221%R:2RH1%QM3RH91&Q2+^@%Q;2Q:1%34RCR4Q91+b0%Q>2Q=1%64RFR719+aH%QA2Q@1z%:4RJR;21+a@%QE2QD1%=4RMR>14'5%11S4%S711&Q7%RN2S<@&=u1%22K1%32RA1%64S7RH51(1&2&N&O%33SAQ31%43SB31%62?1%RM3?81&Q1+QWSQ0%24SBS31RB&M%13S=S5R<&Q9%12S?S7pT<T0SK&<&Q>&R3%12T5S<%32RB1&Q?+a8%RH2RG1%3251%T3251%:11%SH1SGr6%11SI%SD3T:31p051pT<TA1r5%E21SN'6&Q<(3u2u3u4u8uEuGuHuIuJuK(7%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ES>1%D3F@1%E3GB1%F3HD1%G3IF1%I3JTF1%TB1TJ%U32UC1%TE2Q41r9%TG213%TI3UD31p071pT0Q21r8+QSdZ8%U<2UJ1r7%UA59421U9+QRejL%U@2UN1%UD5U:U91U6U<%UG3UF41%U31Q9%UD2V41%U62U=1%UF2V4TB%U93V421+5%R=4UMU>T71+QWSP8%S?4UOU@1S6+QWSP0+VbTfH%SB4V2UC21+QWRo0%SD4V4UE1S;+QWRn@%SF4V6UG1S=+QWRn8%SH4V8UI1S?+QWRm@%SJ4V:UK1SA+QWRmH%SL4V<UM1SC%UI1QM%V:2VJ1%UL2V31%UM2V=2%UO3VJ21%VD261%VE291%VF2<1%VG2?1%VH2B1%VI2E1%VJ2I1%VK2L1%VL2S41%VM2S71%VN2Q11%VO2UK1%W02Q81qQ<W21%W?2W31qQFW91%WA2W:1qSNWA1%WC2WB1p0QH1p0RL1p0RO1pQ>SA1pQHWA1pSHWH1%W=2SE1%W>2SH1%W?2SK1%W@2SO1%WA2TB1%WB2TF1%WC2TK1%WD2TO1%WE2U41%WF2UB1%WG2UH1%WH2UN1%WI2V61%WJ2V<1%WK2VG1%WL2VO1%WM2W:1qQ:WO1%X<2X01qQDX61%X>2X71qSLX>1%X@2X?1").
Proof.
destruct (DOP.open_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN) as (fx5 & R5 & M5 & MS5 & INV).
destruct (open_A_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
Qed.
End UA.
End DOA.
