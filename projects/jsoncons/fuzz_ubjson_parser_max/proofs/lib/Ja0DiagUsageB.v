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
Ltac2 tcn__Ja0DiagUsageB () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagGlue.DG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagUsagePre.DUP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3add"; "4bvmap"; "0M"; "0M5"]; ["0ME"; "0ME2"; "0MF"; "0MX"; "0MY"; "0R"; "0R5"; "0RE"; "0RE2"; "0RF"; "0RX"; "0RY"; "5msteps"; "6PRE7"; "6SUF7"; "6agree0"]; ["7usage_mid"; "8u32_at"; "8u64_at"; "9FPState"; "9getr"; "9mkst"; "9rdn"; "9seg_rom"; ":mem_grows"; ";loaded_segments"; "0S"; "<In"; "=add"; "=le"; "=lt"; "=of_nat"]; ["=sub"; "0bs"; "0can"; "0fx"; "0fx'"; "0fx''"; "0fx5"; "0fxE"; "0fxE2"; "0fxF"; "0k"; "0m1"; "0m2"; "0m3"; "0m4"; "0m5"]; ["0m6"; "0m7"; "0m8"; "0p"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module DUB.
Import DK. Import DSN. Import DG. Import AS0DIAGUP.
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
Hypothesis Hn : 67 <= n <= 73.
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
Local Abbreviation SEC_T_usage_B_tail := (ltac2:(TCodec.tc2 tcn__Ja0DiagUsageB "[0'Q3&=y5'R5yR0%211%5241'7y8%611%311p061&Q0vEv>vQ:vR3vQBvQAvQKvQLvQMvQNvQOvR0vR1vR2r2r1%A@@?>=<;:987654321':'8'L&Q9&Q5r7r6&R4+QScfH%22Q31r5&Q7%119%9587431r3+QS\h4%92Q:1%=53D1C5%@3?51'9&Q4&Q?uA%211%A2QD1%52L1+R2%D2QE1%93QE31u:%911%H2QK1%<2Q31+2%K2QL1%@3QL31u;%@11%O2R21%C2Q:1&Q@+QS8%22QI1%Q42R51%I3R551u<%I11%Q82R;1%L2QC1%N3R:1?u9%N11%Q=2R@1%Q12QH1+QVkb0%Q@2RA1%Q53RA31uB%Q511%QD2RG1%Q82QO1%Q:3RF1KuC%Q:11%QI2RL1%Q=2R41%Q?3RK1GuF%Q?11%QN2S11%QB2R91&Q<&3%12RNRE%QE11+>%5221%R62S71%QK3S781&Q2+^@%Q92S01%34R?RDQ81+QS0%Q<2S31+7%?2<1%84RDRI31+QRH%QA2S81+Rh]N%<4RHRM21+QR@%QE2S<1%?4RKS019'4%11SE%SH11&Q6%RL2SMB&<u7%221M%54S4S941(0&1&M%23T01SG%42<1%RJ3<61%S72T8D%=4S<SA1:&N%92A1%RO3A31&Q1+QVkeH%24SBSG1RD&O%13T7SIT6&Q8%12T9SKpT@TCT>&;&Q=&R6%12THT0%32RE1&Q>+QR8%RJ2TA1%3251%T3251%:11%SH1T9%T11T:%SE3TL21p041pT@U31%C2T1T>'5&Q;(2u2u3u4u8uEuGuHuIuJuK(6%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ES?1%D3F@1%E3GB1%F3HD1%G3IF1%I3JU81%TB1U:%U12V41%TE2U31r9%TG213%TI3V531p071pSFQ21r8+QS\h@%U:2V;1%U>5831U=U6%UA3U@1U2+aH%T=2V41%U?2V@1%U43V@T@1+1%UB2VC1%U73VCT:1%U83VDSO2%U93VESK6z%UG2VH1%U<3VHSI1%SA4UMV2;3+a@%TJ2VA1%SD4V0V516+b8%TM2VD1%R:21R8+a8%U02VG1%R92R;1%V9241%R@11p01R4pT@W61+QR^Y4%V82W91%V<5V2VC1VBV4%V?3V>O1%UM1R0%V<2W?1%V02W51%V23W>UE1%V11R7%V@2WC1%V42VK1+R@%TC2W91%VD2WE1%V93WE41+5%S;4VKW0U81+QVke0%TA4VMW21Q3+QVkdH+Vam\H%TD4W0W521+QVkcH%TF4W2W71Q8+QVkc8%TH4W4W91Q:+QVkc0%TJ4W6W;1Q<+QVkb8%TL4W8W=1Q>+QVkb@%TN4W:W?1Q@%VI1RM%W82X;1%VL2WC1%VM2X22%VO3X;21%WB261%WC291%WD2<1%WE2?1%WF2B1%WG2E1%WH2I1%WI2L1%WJ2T21%WK2T51%WL2Q11%WM2Q91%WN2Q>1qQ6XC1%X12XD1qQDXJ1%X32XK1qSDY21%X52Y31p0RH1p0SL1p0QK1pQ:T?1pQHY21pS<Y91%X;2TC1%X<2TF1%X=2TI1%X>2R<1%X?2R@1%X@2RB1%XA2RF1%XB2RH1%XC2VL1%XD2RK1%XE2RO1%XF2WD1%XG2WL1%XH2S61qQ4Y=1%XK2Y>1qQBYD1%XM2YE1qSBYL1%XO2YM1p0SB1p0TF1p0TH1pQ8U91pQFYL1pS:Z31%Y52U=1%Y62U@1%Y72UC1%Y82UG1%Y92UM1%Y:2V=1%Y;2VA1%Y<2VF1%Y=2VL1%Y>2W11%Y?2W>1%Y@2WD1%YA2WJ1%YB2X21%YC2X81%YD2XB1%YE2XJ1%YF2Y51qQ2Z;1%YI2Z<1qQ@ZB1%YK2ZC1qS@ZJ1%YM2ZK1p0YO1pQ0ZB1pQ>ZH1pS>ZO1")) (only parsing).
Variable fx5 : ltac:(sec_ty2 constr:(SEC_T_usage_B_tail) 0%nat 0%nat).
Variable R5 : ltac:(sec_ty2 constr:(SEC_T_usage_B_tail) 1%nat 0%nat).
Variable M5 : ltac:(sec_ty2 constr:(SEC_T_usage_B_tail) 2%nat 0%nat).
Theorem usage_B_tail : ltac:(sec_stmt2 constr:(SEC_T_usage_B_tail) 3%nat 0%nat).
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
cfeed P (duDs_conc fx5 R5 M5 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
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
destruct (memcpy_stage fx6 R6 M6 (S - 1088) (S - 457) p n bs) as (R7 & M7 & MS7 & V7 & KS7 & AG67 & MG7 & RD7);
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
assert (AG67' : forall x : word, S - 1088 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 457 + n) -> M7 x = M6 x) by (intros x Hx Hd; apply AG67; [lia | exact Hd]).
assert (AG57 : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 457 + n) -> M7 x = M5 x) by (intros x Hx Hd; rewrite AG67' by (first [exact Hd | lia]); apply AG56; lia).
assert (AG57s : forall x : word, bv_unsigned x < 2 ^ 32 -> M7 x = M5 x) by (intros x Hx; rewrite AG67 by lia; apply AG56; lia).
assert (F87 : L5.u8_at RSEGS M7 1273408 5).
{ apply u8_of_u32_5; [lia | lia|]. scc. }
cfeed P (duEb_conc fx6 R7 M7 (fun j => match j with 2%nat => S - 1088 | 33%nat => p | 34%nat => n | 40%nat => can | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.
assert (AG78 : forall x : word, bv_unsigned x < S - 1136 \/ S - 1024 <= bv_unsigned x -> ~ (1273448 <= bv_unsigned x < 1273456) -> M8 x = M7 x) by (intros x Hx Hf; apply FR8; lia).
assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG78 by (unfold filew in Hf; lia); apply A07; assumption).
assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (AG58s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1273448 <= bv_unsigned x < 1273456) -> M8 x = M5 x) by (intros x Hx Hf; rewrite AG78 by lia; apply AG57s; lia).
assert (AG58h : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 457 + n) -> M8 x = M5 x) by (intros x Hx Hd; rewrite AG78 by lia; apply AG57; lia).
assert (NE : Z.eqb (S - 457 + n) (S - 464) = false) by (apply Z.eqb_neq; lia).
destruct (wv_entry_stage fx8 R8 M8 1273408 (S - 1136) 90558 7 (S - 457 + n) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG8W & MGW);
[ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
rewrite NE in W11, W12, W18, W19.
assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG8W by lia; apply A08; assumption).
assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
assert (IMGW : L5.img_clear MW 65536 1261568) by (apply (imgc_ext M MW); [intros x Hx; apply A0W; flia | lia | lia | exact HIMG]).
assert (BUFW : rdn RSEGS MW (Z_to_bv 64 (S - 464)) (7 + length bs) = Some (PRE7 ++ bs)).
{ assert (AG5Wb : forall x : word, S - 464 <= bv_unsigned x < S - 457 -> MW x = M5 x) by (intros x Hx; rewrite AG8W by lia; apply AG58h; lia).
assert (AG7Wb : forall x : word, S - 457 <= bv_unsigned x < S - 457 + n -> MW x = M7 x) by (intros x Hx; rewrite AG8W by lia; apply AG78; lia).
assert (P7 : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 7 = Some PRE7).
{ rewrite PRE7_eq. apply rdn_7; [lia | lia | ..];
(eapply (u8_ext M5); [intros x Hx; apply AG5Wb; lia | lia | lia |]); match goal with |- L5.u8_at _ _ ?a _ => ring_simplify a end; assumption. }
assert (PB : rdn RSEGS MW (Z_to_bv 64 (S - 457)) (length bs) = Some bs) by (apply (rdn_xfer M7 MW); [intros x Hx; apply AG7Wb; lia | lia | lia | exact RD7]).
apply rdn_app_Z; [lia | lia | exact P7|]. replace (S - 464 + Z.of_nat 7) with (S - 457) by lia. exact PB. }
assert (SUFW : rdn RSEGS MW (Z_to_bv 64 90558) 7 = Some SUF7).
{ rewrite (rdn_img MW 65536 1261568) by (first [exact IMGW | cbn; lia | lia]). exact suf7_img. }
exists fx8, RW, MW.
split. { eapply msteps_trans; [exact MS6|]. eapply msteps_trans; [exact MS7|]. eapply msteps_trans; [exact MS8|]. exact MSW. }
split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
split; [replace (S - 1128) with (S - 1136 + 8) by lia; exact I0|]. split; [replace (S - 1120) with (S - 1136 + 16) by lia; replace (n + 7) with (S - 457 + n - (S - 464)) by lia; exact I1|].
split; [replace (S - 1112) with (S - 1136 + 24) by lia; exact I2|]. split; [replace (S - 1104) with (S - 1136 + 32) by lia; exact I3|].
split; [exact BUFW|]. split; [exact SUFW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
intros fx' RX MX AGXW MGXW KXW.
assert (AGX8 : forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = M8 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG8W; lia).
assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R8 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
assert (AGX7 : forall x : word, S - 1024 <= bv_unsigned x -> MX x = M7 x) by (intros x Hx; rewrite AGX8 by lia; apply AG78; lia).
assert (AGX5 : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 457 + n) -> MX x = M5 x) by (intros x Hx Hd; rewrite AGX7 by lia; apply AG57; lia).
assert (AGX5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1273448 <= bv_unsigned x < 1273456) -> MX x = M5 x) by (intros x Hx Hf; rewrite AGX8 by lia; apply AG58s; assumption).
assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
assert (IMGX : L5.img_clear MX 65536 1261568) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
assert (FWX : L5.writable RSEGS MX 1273408 152) by (eapply writable_grows; eassumption).
cfeed P (duGb1_conc fx' RX MX (fun j => match j with 2%nat => S - 1136 | 33%nat => p | 34%nat => n | 40%nat => can
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
cfeed P (duGb2_conc fx'' RY MY (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
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
Theorem usage_B : ltac2:(TCodec.tc2 tcn__Ja0DiagUsageB "ZA':'Q3&=y5'R5yR0%211%5241'7y8%611%311p061'8'L&Q9&Q5vQCvE&R4+\Zc4%22@1v>&Q7%119%9587431r3r2+QS\h4%:2H1r1%?554217%B3A71'9&Q4&Q?uA%211%C2Q31%52<1+R2%F2Q41%93Q431u:%911%J2Q:1%<2C1+2%M2Q;1%@3Q;31u;%@11%Q12QA1%C2J1&Q@vQ:+QS8%3221%Q72QE1%J3QE61u<%J11%Q;2QK1%M2Q41%O3QJ1@u9%O11%Q@2R01%Q22Q91+QVkb0%QC2R11%Q63R131uB%Q611%QG2R71%Q92Q@1%Q;3R61LuC%Q;11%QL2R<1%Q>2QE1%Q@3R;1GuF%Q@11%R12RA1%QC2QJ1&Q<&3vQA%22R?1%QG11+>%6221%R:2RH1%QM3RH91&Q2+^@%Q;2Q:1%34RCR4Q91+QS0%Q>2Q=1+7%@2<1%84RHR931+QRH%QC2QB1+Rh]N%<4RLR=21+QR@%QG2QF1%?4ROR@19'4%11S6%S911&Q6%S02S>B&<u7%221M%54S8RI41(0&1&M%23SA1Q3%42<1%RL3<61%S;2SID%=4S@S11:&N%92A1%S13A31&Q1+QVkeH%24SFS71RF&O%13SAS9R@&Q8%12SCS;pT@T4SO&;&Q=&R6%12T9S@%32RF1&Q>+QR8%RL2RK1%3251%T7251%:11%SL1SKr6%11SM%SH3T>31p051pT@TE1r5%E21T2'5&Q;(2u2u3u4u8uEuGuHuIuJuK(6%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ESB1%D3F@1%E3GB1%F3HD1%G3IF1%I3JTJ1%TF1TN%U72UG1%TI2Q41r9%TK213%TM3UH31p071pSFQ21r8+QS\h@%U@2UN1r7%UE59421U=%UH3UG1U7+aH%TB2TA1%UF2V41%U93V4TE1+1%UI2V71%U<3V7T>1%U=3V8T32%U>3V9SO6z%UN2V<1%UA3V<SM1%SD4V4UE;3+a@%TO2TN1%SG4V7UH16+b8%U22U11%R=21R;+a8%U52U41%R<2R>1%V@241%RC11p01R6pT@VJ1+QR^Y4%V?2VM1%VC5V9V81V5V;%VF3VEO1%V21R1%VC2W31%V52VE1%V73W2UJ1%V61R8%VG2W71%V92V@1+R@%TG2UF1%VK2W91%V>3W941+5%S>4W2VCU<1+QVke0%TD4W4VE1Q3+QVkdH+Vam\H%TG4W7VH21+QVkcH%TI4W9VJ1Q8+QVkc8%TK4W;VL1Q:+QVkc0%TM4W=VN1Q<+QVkb8%TO4W?W01Q>+QVkb@%U14WAW21Q@%VN1RN%W?2WO1%W12W81%W22WB2%W43WO21%WI261%WJ291%WK2<1%WL2?1%WM2B1%WN2E1%WO2I1%X02L1%X12T51%X22T81%X32Q11%X42Q91%X52Q>1qQ6X71%XD2X81qQDX>1%XF2X?1qSDXF1%XH2XG1p0RI1p0SM1p0QK1pQ:TB1pQHXF1pS<XM1%XB2TF1%XC2TI1%XD2TL1%XE2R<1%XF2R@1%XG2RB1%XH2RF1%XI2RH1%XJ2W01%XK2RK1%XL2RO1%XM2WI1%XN2X11%XO2S61qQ4Y11%Y>2Y21qQBY81%Y@2Y91qSBY@1%YB2YA1p0SC1p0TG1p0TJ1pQ8U<1pQFY@1pS:YG1%Y<2U@1%Y=2UC1%Y>2UF1%Y?2UJ1%Y@2V01%YA2V@1%YB2VD1%YC2VI1%YD2VO1%YE2W41%YF2WB1%YG2WH1%YH2WN1%YI2X61%YJ2X<1%YK2XG1%YL2XO1%YM2Y:1qQ2YO1%Z<2Z01qQ@Z61%Z>2Z71qS@Z>1%Z@2Z?1").
Proof.
destruct (DUP.usage_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF) as (fx5 & R5 & M5 & MS5 & INV).
destruct (usage_B_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
Qed.
End UA.
End DUB.
