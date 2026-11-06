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
Ja0RegionPoisoned Ja0AsanMemcpy Ja0DiagKit Ja0DiagChk Ja0DiagMemcpy Ja0DiagStrnlen Ja0DiagGlue Ja0DiagUP Ja0DiagUsagePre.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DiagUsageC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagGlue.DG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagUsagePre.DUP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3map"; "4Z"; "5bvmap"; "0M"; "0M5"]; ["0ME"; "0ME2"; "0MF"; "0MX"; "0MY"; "0R"; "0R5"; "0RE"; "0RE2"; "0RF"; "0RX"; "0RY"; "6msteps"; "7PRE7"; "7SUF7"; "7agree0"]; ["8usage_mid"; "9u32_at"; "9u64_at"; ":FPState"; ":getr"; ":mkst"; ":rdn"; ":seg_rom"; ";mem_grows"; "<loaded_segments"; "0S"; "=In"; ">add"; ">le"; ">lt"; ">of_nat"]; [">sub"; "0bs"; "0can"; "0fx"; "0fx'"; "0fx''"; "0fx5"; "0fxE"; "0fxE2"; "0fxF"; "0k"; "0m1"; "0m2"; "0m3"; "0m4"; "0m5"]; ["0m6"; "0m7"; "0m8"; "0p"; "?Z_to_bv"; "?bv"; "?bv_unsigned"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module DUC.
Import DK. Import DSN. Import DG. Import AS0DIAGUP.
Lemma SUF7_eqJ : ltac2:(TCodec.tc2 tcn__Ja0DiagUsageC "N'8'3'R5y8%211%411&N&;'<&R4%117(1+Q0+R9+R>+R@+RE+RD+:(5%11<%:3=31%;3>51%<3?71%=3@91%>3A;1%?3B=1%@3C?1%E4DHB1%M3HG1").
Proof. apply list_bv_eq. vm_compute. reflexivity. Qed.
Section UA.
Context (fx : FPState).
Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
#[local] Notation n := (Z.of_nat (length bs)).
Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 684896.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1273408.
Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 90549.
Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.
Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
Hypothesis Hal : S mod 16 = 0.
Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
Hypothesis HD : L5.defined M (S - 5440) 5440.
Hypothesis HIMG : L5.img_clear M 65536 1261568.
Hypothesis Hp : S <= p /\ p + n + 1 + 16 <= 2 ^ 47.
Hypothesis Hn : 74 <= n <= 131071.
Hypothesis HSTR : cstr M p bs t8.
Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.
Hypothesis HFMT : L5KA.zeros_at M 2147462192 16.
Hypothesis Hcan : 0 <= can < 2 ^ 64.
Hypothesis HC : diag_cells M can.
Hypothesis HSN : sn_cells M.
Hypothesis HMC : mc_icpt_globs M.
Variables m1 m2 m3 m4 m5 m6 m7 m8 : Z.
Hypothesis Hm : (0 <= m1 < 2 ^ 64 /\ 0 <= m2 < 2 ^ 64 /\ 0 <= m3 < 2 ^ 64 /\ 0 <= m4 < 2 ^ 64) /\ (0 <= m5 < 2 ^ 64 /\ 0 <= m6 < 2 ^ 64 /\ 0 <= m7 < 2 ^ 64 /\ 0 <= m8 < 2 ^ 64).
Hypothesis HMF : L5.u64_at RSEGS M (S + 72) 1126748 /\ L5.u64_at RSEGS M (S + 64) m1 /\ L5.u64_at RSEGS M (S + 56) m2 /\ L5.u64_at RSEGS M (S + 48) m3 /\ L5.u64_at RSEGS M (S + 40) m4
/\ L5.u64_at RSEGS M (S + 32) m5 /\ L5.u64_at RSEGS M (S + 24) m6 /\ L5.u64_at RSEGS M (S + 16) m7 /\ L5.u64_at RSEGS M (S + 8) m8.
Section SE.
Local Abbreviation SEC_T_usage_C_tail := (ltac2:(TCodec.tc2 tcn__Ja0DiagUsageC "ZN'Q3&=y5'R5yR0%211%5241'6y8%611%311p061&Q0vEv>vQ:vR3vQBvQAvQKvQLvQMvQNvQOvR0vR1vR2r2r1%A@@?>=<;:987654321'9'7'L&Q9&Q5r7r6&R4+QScfH%22Q31r5&Q7%119%9587431r3+QS\h4%92Q:1%=53D1C5%@3?51'8&Q4&Q?uA%211%A2QD1%52L1+R2%D2QE1%93QE31u:%911%H2QK1%<2Q31+2%K2QL1%@3QL31u;%@11%O2R21%C2Q:1&Q@+QS8%22QI1%Q42R51%I3R551u<%I11%Q82R;1%L2QC1%N3R:1?u9%N11%Q=2R@1%Q12QH1+QVkb0%Q@2RA1%Q53RA31uB%Q511%QD2RG1%Q82QO1%Q:3RF1KuC%Q:11%QI2RL1%Q=2R41%Q?3RK1GuF%Q?11%QN2S11%QB2R91&Q<&2%12RNRE%QE11+7%5221%R62S71%QK3S781&Q2+^@%Q92S01%34R?RDQ81+QS0%Q<2S31%64RBRG1:+QRH%Q?2S61%94RERJ1S6+QR@%QB2S91%<4RHRM1A'3%11SB%SE11&Q6%RI2SJ?u7%34ROS421(0&M%2281%RC3841%S02T1SE%94S5S:1O%62<SE%RG3<21&Q1+QVkeH%24S:S?1R<&O%13SOSASN&Q8%12T1SCpT@T;T6&:&Q=&R6%12T@SH%32R=1&Q>+QR8%RB2T91%3251%SK251%:11%S@1T1%SI1T2%S=3TD21p041pT@TK1%C2SIT6'4&Q;(1u2u3u4u8uEuGuHuIuJuK(5%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ES71%D3F@1%E3GB1%F3HD1%G3IF1%I3JU01%T:1U2%TI2UL1%T=2TK1r9%T?213%TA3UM31p071pSFQ21r8+QS\h@%U22V31%U65831U5TN%U93U81TJ+b8%T52UL1%U72V81%TL3V8T81%TM3V9S?2%U:2V;S6%TO3V;S<1%S44U@UE6S2+b0%T=2V41%S74UCUH1S;+aH%T@2V71z%S;4UGUL21+a@%TD2V;1%S>4UJUO14&N%RL2S21%U=3S2RN1%R=2DR;+a8%TK2VB1%R<2R>1%V4241%RC11p01R7pT@W11+QR^Y4%V32W41%V75UMV>1V=UO%V:3V9Q21%UH1R3%V72W:1%UK2W01%UM3W9U@1%UL1R:%V;2W>1%UO2VF1+R@%T>2W41%V?2W@1%V43W@41+5%S>4VFVKU31+QVke0%T<4VHVM1Q2+QVkdH+Vam\H%T?4VKW021+QVkcH%TA4VMW21Q7+QVkc8%TC4VOW41Q9+QVkc0%TE4W1W61Q;+QVkb8%TG4W3W81Q=+QVkb@%TI4W5W:1Q?%VD1S0%W32X61%VG2W>1%VH2WM2%VJ3X621%W=261%W>291%W?2<1%W@2?1%WA2B1%WB2E1%WC2I1%WD2L1%WE2T51%WF2T81%WG2Q11%WH2Q91%WI2Q>1qQ6X>1%WL2X?1qQDXE1%WN2XF1qSDXM1%X02XN1p0RK1p0SO1p0QK1pQ:TB1pQHXM1pS<Y41%X62TF1%X72TI1%X82TL1%X92R:1%X:2R>1%X;2RB1%X<2RG1%X=2RK1%X>2RM1%X?2S01%X@2VD1%XA2VJ1%XB2W21%XC2S51%XD2WB1%XE2WJ1%XF2S<1qQ4Y;1%XI2Y<1qQBYB1%XK2YC1qSBYJ1%XM2YK1p0SH1p0TL1p0TN1pQ8U?1pQFYJ1pS:Z11%Y32UC1%Y42UF1%Y52UI1%Y62UM1%Y72V21%Y82V>1%Y92VB1%Y:2VF1%Y;2VJ1%Y<2VO1%Y=2W<1%Y>2WB1%Y?2WH1%Y@2X01%YA2X61%YB2X@1%YC2XH1%YD2Y31qQ2Z91%YG2Z:1qQ@Z@1%YI2ZA1qS@ZH1%YK2ZI1p0YM1pQ0Z@1pQ>ZF1pS>ZM1")) (only parsing).
Variable fx5 : ltac:(sec_ty2 constr:(SEC_T_usage_C_tail) 0%nat 0%nat).
Variable R5 : ltac:(sec_ty2 constr:(SEC_T_usage_C_tail) 1%nat 0%nat).
Variable M5 : ltac:(sec_ty2 constr:(SEC_T_usage_C_tail) 2%nat 0%nat).
Theorem usage_C_tail : ltac:(sec_stmt2 constr:(SEC_T_usage_C_tail) 3%nat 0%nat).
Proof.
intros INV.
destruct Hm as ((Hm1 & Hm2 & Hm3 & Hm4) & (Hm5 & Hm6 & Hm7 & Hm8)).
pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
assert (Pr : 140735332552704 <= p <= 140737488355311) by lia.
assert (Nr : 0 <= n <= 131071) by lia.
assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
destruct INV as (A05 & MG05 & T). dk_split T.
assert (W5 : L5.writable RSEGS M5 (S - 5440) 5440) by (eapply writable_grows; [exact MG05 | exact HW]).
assert (D5 : L5.defined M5 (S - 5440) 5440) by (eapply defined_grows; [exact MG05 | exact HD]).
assert (IMG5 : L5.img_clear M5 65536 1261568) by (apply (imgc_ext M M5); [intros x Hx; apply A05; flia | lia | lia | exact HIMG]).
cfeed P (duDl_conc fx5 R5 M5 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | 40%nat => can | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.
assert (AG58 : forall x : word, bv_unsigned x < S - 1136 \/ S - 1024 <= bv_unsigned x -> M8 x = M5 x) by (intros x Hx; apply FR8; lia).
assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG58 by lia; apply A05; assumption).
assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (NE : Z.eqb (S - 457) (S - 464) = false) by (apply Z.eqb_neq; lia).
destruct (wv_entry_stage fx8 R8 M8 1273408 (S - 1136) p n (S - 457) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG8W & MGW);
[ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
rewrite NE in W11, W12, W18, W19.
assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG8W by lia; apply A08; assumption).
assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
assert (AG5W : forall x : word, S - 1024 <= bv_unsigned x -> MW x = M5 x) by (intros x Hx; rewrite AG8W by lia; apply AG58; lia).
assert (P7W : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 7 = Some PRE7).
{ rewrite PRE7_eq. apply rdn_7; [lia | lia | ..];
(eapply (u8_ext M5); [intros x Hx; apply AG5W; lia | lia | lia |]); match goal with |- L5.u8_at _ _ ?a _ => ring_simplify a end; assumption. }
assert (STRW : cstr MW p bs t8) by (apply (cstr_ext M MW); [lia | lia | intros x Hx; apply A0W; flia | exact HSTR]).
assert (RDSW : rdn RSEGS MW (Z_to_bv 64 p) (length bs) = Some bs).
{ destruct STRW as [A _ _]. rewrite (SeqExec.rdn_firstn RSEGS MW _ _ _ (length bs) A) by lia. f_equal. rewrite firstn_app, firstn_all2 by lia. rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
exists fx8, RW, MW.
split. { eapply msteps_trans; [exact MS8|]. exact MSW. }
split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
split; [replace (S - 1128) with (S - 1136 + 8) by lia; exact I0|]. split; [replace (S - 457 - (S - 464)) with 7 in I1 by lia; replace (S - 1120) with (S - 1136 + 16) by lia; exact I1|].
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
assert (IMGX : L5.img_clear MX 65536 1261568) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
assert (FWX : L5.writable RSEGS MX 1273408 152) by (eapply writable_grows; eassumption).
assert (SKX : L5KA.zeros_at MX (SB + S / 8 - 680) 688).
{ apply (zeros_ext M MX); [intros x Hx; apply AGX0; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
assert (F8X : L5.u8_at RSEGS MX 1273408 5) by (apply u8_of_u32_5; [lia | lia|]; scc).
assert (FMTX : L5KA.zeros_at MX 2147462192 16) by (apply (zeros_ext M MX); [intros x Hx; apply AGX0; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HFMT]).
pose proof (u64_of_zeros MX 2147462192 (L5KA.zeros_at_sub MX 2147462192 16 2147462192 8 FMTX ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as FMT64X1.
pose proof (u64_of_zeros MX 2147462200 (L5KA.zeros_at_sub MX 2147462192 16 2147462200 8 FMTX ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as FMT64X2.
cfeed P (duEc_conc fx' RX MX (fun j => match j with 2%nat => S - 1136 | 33%nat => p | 34%nat => n | 40%nat => can
| 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
| 122%nat => U RX 22 | 123%nat => U RX 23 | 125%nat => U RX 25 | 127%nat => U RX 27 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fx9 R9 M9 MG9 FR9 FZ9 MS9 KS9.
assert (AGX9 : forall x : word, bv_unsigned x < S - 3248 \/ S - 448 <= bv_unsigned x -> ~ (1273440 <= bv_unsigned x < 1273456) -> ~ (1273464 <= bv_unsigned x < 1273472) -> M9 x = MX x) by (intros x Hx Hf1 Hf2; apply FR9; lia).
assert (A09 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M9 x = M x) by (intros x Hx Hf; rewrite AGX9 by (unfold filew in Hf; lia); apply AGX0; assumption).
assert (MG09 : mem_grows M M9) by (eapply mem_grows_trans; eassumption).
assert (W9 : L5.writable RSEGS M9 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (AG59s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1273440 <= bv_unsigned x < 1273456) -> ~ (1273464 <= bv_unsigned x < 1273472) -> M9 x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGX9 by lia; apply AGX5s; lia).
assert (NE2 : Z.eqb (S - 457) (S - 464) = false) by (apply Z.eqb_neq; lia).
destruct (wv_entry_stage fx9 R9 M9 1273408 (S - 592) 0 0 (S - 457) (S - 464) 2) as (RW2 & MW2 & MSW2 & X17 & X10 & X11 & X12 & X18 & X19 & X22 & KSW2 & J0 & J1 & J2 & J3 & AG9W & MGW2);
[ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
rewrite NE2 in X11, X12, X18, X19.
assert (A0W2 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW2 x = M x) by (intros x Hx Hf; rewrite AG9W by lia; apply A09; assumption).
assert (MG0W2 : mem_grows M MW2) by (eapply mem_grows_trans; eassumption).
assert (SUFW : rdn RSEGS MW2 (Z_to_bv 64 (S - 464)) 7 = Some SUF7).
{ rewrite SUF7_eqJ. cbn [map].
repeat (apply rdn_cons; [lia | cbn; lia | (change (rdn RSEGS MW2 (Z_to_bv 64 ?a) 1 = Some [Z_to_bv 8 ?v]) with (L5.u8_at RSEGS MW2 a v);
eapply (u8_ext M9); [intros x Hx; apply AG9W; lia | lia | lia | match goal with |- _ _ _ ?a _ => ring_simplify a end; assumption]) | ]);
reflexivity. }
exists fx9, RW2, MW2.
split. { eapply msteps_trans; [exact MS9|]. exact MSW2. }
split; [exact X17|]. split; [exact X10|]. split; [rewrite X11; f_equal; lia|]. split; [exact X12|].
split; [rewrite (KSW2 9%nat) by (cbn; tauto); sc|]. split; [exact X18|]. split; [rewrite X19; f_equal; lia|]. split; [rewrite X22; f_equal; lia|].
split; [replace (S - 584) with (S - 592 + 8) by lia; exact J0|]. split; [replace (S - 457 - (S - 464)) with 7 in J1 by lia; replace (S - 576) with (S - 592 + 16) by lia; exact J1|].
split; [replace (S - 568) with (S - 592 + 24) by lia; exact J2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact J3|].
split; [exact SUFW|]. split; [scc|]. split; [exact A0W2|]. split; [exact MG0W2|].
intros fx'' RY MY AGYW MGYW KYW.
assert (AGY9 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = M9 x) by (intros x Hx; rewrite AGYW by exact Hx; apply AG9W; lia).
assert (KY : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr R9 (reg k)) by (intros k Hk; rewrite (KYW k Hk); apply KSW2; cbn in Hk |- *; tauto).
assert (AGYX : forall x : word, S - 448 <= bv_unsigned x -> MY x = MX x) by (intros x Hx; rewrite AGY9 by lia; apply AGX9; lia).
assert (AGY5 : forall x : word, S - 448 <= bv_unsigned x -> MY x = M5 x) by (intros x Hx; rewrite AGYX by lia; apply AGX5; lia).
assert (AGY5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1273440 <= bv_unsigned x < 1273456) -> ~ (1273464 <= bv_unsigned x < 1273472) -> MY x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGY9 by lia; apply AG59s; assumption).
assert (AGY0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MY x = M x) by (intros x Hx Hf; rewrite AGYW by lia; apply A0W2; assumption).
assert (MG0Y : mem_grows M MY) by (eapply mem_grows_trans; eassumption).
assert (WY : L5.writable RSEGS MY (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (DY : L5.defined MY (S - 5440) 5440) by (eapply defined_grows; eassumption).
assert (IMGY : L5.img_clear MY 65536 1261568) by (apply (imgc_ext M MY); [intros x Hx; apply AGY0; flia | lia | lia | exact HIMG]).
assert (FWY : L5.writable RSEGS MY 1273408 152) by (eapply writable_grows; eassumption).
cfeed P (duGc_conc fx'' RY MY (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
| 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
| 41%nat => m1 | 42%nat => m2 | 43%nat => m3 | 44%nat => m4 | 45%nat => m5 | 46%nat => m6 | 47%nat => m7 | 48%nat => m8
| 118%nat => U RY 18 | 119%nat => U RY 19 | 120%nat => U RY 20 | 122%nat => U RY 22 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
exists fxF, RF, MF.
split; [exact MSF|].
split. { match goal with H : getr RF (reg 10) = Z_to_bv 64 (U R 8) |- _ => rewrite H end. symmetry. apply U_to. }
split; [sc|].
split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. apply AGY0; [exact Hx | unfold filew; lia]. }
split; [eapply mem_grows_trans; [exact MG0Y | exact MGF]|].
repeat split; first [sc | (eapply (DK.u64_ext M5); [intros x Hx; rewrite FRF by lia; apply AGY5s; lia | lia | lia | eassumption]) | dk_rk].
Qed.
End SE.
Theorem usage_C : ltac2:(TCodec.tc2 tcn__Ja0DiagUsageC "Z@'9'Q3&=y5'R5yR0%211%5241'6y8%611%311p061'7'L&Q9&Q5vQCvE&R4+\Zc4%22@1v>&Q7%119%9587431r3r2+QS\h4%:2H1r1%?554217%B3A71'8&Q4&Q?uA%211%C2Q31%52<1+R2%F2Q41%93Q431u:%911%J2Q:1%<2C1+2%M2Q;1%@3Q;31u;%@11%Q12QA1%C2J1&Q@vQ:+QS8%3221%Q72QE1%J3QE61u<%J11%Q;2QK1%M2Q41%O3QJ1@u9%O11%Q@2R01%Q22Q91+QVkb0%QC2R11%Q63R131uB%Q611%QG2R71%Q92Q@1%Q;3R61LuC%Q;11%QL2R<1%Q>2QE1%Q@3R;1GuF%Q@11%R12RA1%QC2QJ1&Q<&2vQA%22R?1%QG11+7%6221%R:2RH1%QM3RH91&Q2+^@%Q;2Q:1%34RCR4Q91+QS0%Q>2Q=1%64RFR71:+QRH%QA2Q@1vR3%:4RJR;21+QR@%QE2QD1%=4RMR>1B'3%11S4%S711&Q6%RN2S<@u7%34S4RE21(0&M%2281%RF3841%S52SC@%94S:RK1Q0%62<Q2%RJ3<21&Q1+QVkeH%24S?S01R?&O%13S:S2R9&Q8%12S<S4pT@SMSH&:&Q=&R6%12T2S9%32R?1&Q>+QR8%RE2RD1%3251%T0251%:11%SE1SDr6%11SF%SA3T731p051pT@T>1r5%E21SK'4&Q;(1u2u3u4u8uEuGuHuIuJuK(5%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ES;1%D3F@1%E3GB1%F3HD1%G3IF1%I3JTC1%T?1TG%U02U@1%TB2Q41r9%TD213%TF3UA31p071pSFQ21r8+QS\h@%U92UG1r7%U>59421U6%UA3U@1U0+b8%T;2T:1%U?2UM1%U23UMT>1%U33UNSD2%UB2V0S:%U53V0SA1%S84UHU96S6+b0%TC2TB1%S;4UKU<1S?+aH%TF2TE1z%S?4UOU@21+a@%TJ2TI1%SB4V2UC14&N%RO2S51%UC3S5S11%R@2DR>+a8%U12U01%R?2RA1%V<241%RF11p01R9pT@VF1+QR^Y4%V;2VI1%V?5V5V41V1V7%VB3VAQ21%UN1R4%V?2VO1%V12VA1%V33VNUF1%V21R;%VC2W31%V52V<1+R@%TC2UB1%VG2W51%V:3W541+5%SA4VNV?U81+QVke0%T@4W0VA1Q2+QVkdH+Vam\H%TC4W3VD21+QVkcH%TE4W5VF1Q7+QVkc8%TG4W7VH1Q9+QVkc0%TI4W9VJ1Q;+QVkb8%TK4W;VL1Q=+QVkb@%TM4W=VN1Q?%VJ1S1%W;2WK1%VM2W41%VN2W>2%W03WK21%WE261%WF291%WG2<1%WH2?1%WI2B1%WJ2E1%WK2I1%WL2L1%WM2T81%WN2T;1%WO2Q11%X02Q91%X12Q>1qQ6X31%X@2X41qQDX:1%XB2X;1qSDXB1%XD2XC1p0RL1p0T01p0QK1pQ:TE1pQHXB1pS<XI1%X>2TI1%X?2TL1%X@2TO1%XA2R:1%XB2R>1%XC2RB1%XD2RG1%XE2RK1%XF2RM1%XG2S01%XH2VI1%XI2VO1%XJ2W71%XK2S51%XL2WH1%XM2X01%XN2S<1qQ4Y01%Y=2Y11qQBY71%Y?2Y81qSBY?1%YA2Y@1p0SI1p0TM1p0U01pQ8UB1pQFY?1pS:YF1%Y;2UF1%Y<2UI1%Y=2UL1%Y>2V01%Y?2V51%Y@2VA1%YA2VE1%YB2VJ1%YC2VN1%YD2W31%YE2WA1%YF2WG1%YG2WM1%YH2X51%YI2X;1%YJ2XF1%YK2XN1%YL2Y91qQ2YN1%Z;2YO1qQ@Z51%Z=2Z61qS@Z=1%Z?2Z>1").
Proof.
destruct (DUP.usage_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF) as (fx5 & R5 & M5 & MS5 & INV).
destruct (usage_C_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
Qed.
End UA.
End DUC.
