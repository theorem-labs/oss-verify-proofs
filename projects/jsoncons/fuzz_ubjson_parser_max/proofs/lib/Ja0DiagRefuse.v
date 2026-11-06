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
Ja0RegionPoisoned Ja0AsanMemcpy Ja0DiagKit Ja0DiagChk Ja0DiagMemcpy Ja0DiagStrnlen Ja0DiagGlue Ja0DiagRP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DiagRefuse () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagGlue.DG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagRefuse.DRF."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3map"; "4Z"; "5word_to_le_bytes"; "6bvmap"; "0M"; "0ME"]; ["0MF"; "0MX"; "0R"; "0RE"; "0RF"; "0RX"; "7msteps"; "8agree0"; "9MSGR"; ":u32_at"; ":u64_at"; ":u8_at"; ";FPState"; ";getr"; ";mkst"; ";rdn"]; [";seg_rom"; "<mem_grows"; "=loaded_segments"; "0S"; ">In"; "?add"; "?le"; "?lt"; "?of_nat"; "?pow"; "?sub"; "0a"; "0b0"; "0b1"; "0b2"; "0b3"]; ["0fx"; "0fx'"; "0fxE"; "0fxF"; "0k"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0w"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module DRF.
Import DK. Import DSN. Import DG. Import AS0DIAGRP.
Definition MSGR : list byte := map (Z_to_bv 8)
[99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].
Ltac rdn_bytes :=
repeat (apply rdn_cons; [lia | cbn; lia | (match goal with |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => try (progress (ring_simplify a)) end; match goal with H : L5.u8_at _ _ ?a _ |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => exact H end) | ]);
reflexivity.
Lemma u8s_of_u32 : ltac2:(TCodec.tc2 tcn__Ja0DiagRefuse "R<'QFyR0%211'5y8%511%311p051';&Q6zr6%3221&Q5r7+4%3221&Q9+2+R0%3221%<251&I&Q2r9r8%44321<'7'2%11E&:&QG%11L&<u4&QE%12Q3;%4231%84Q1N61(1r5r4(4%11Q3%53Q431%63Q551%73Q6Q31%83Q7Q11%E3C:1'6&Kr;r:%34N21L+1%Q:231%64Q151Q:%Q<25Q7%84Q371Q?+3%Q?281%;4Q6:1E%=241%>271%?2;1p0A1p0Q81p0Q>1p0QH1pS0QM1pRNQN1pRLQO1pRJR01pSBR11pRHR21pNR41").
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
Ltac shz0 := lazymatch goal with |- L5KA.zeros_at ?M (?S / 8 + ?d) ?l => unfold SB in *; dk_gmem end.
Section RF.
Context (fx : FPState).
Variables (R : bvmap 5 word) (M : word -> option byte) (S can : Z).
Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 685072.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1273408.
Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 108938.
Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 67108864.
Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
Hypothesis Hal : S mod 16 = 0.
Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
Hypothesis HD : L5.defined M (S - 5440) 5440.
Hypothesis HIMG : L5.img_clear M 65536 1261568.
Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.
Hypothesis HFMT : L5KA.zeros_at M 2147464496 8.
Hypothesis Hcan : 0 <= can < 2 ^ 64.
Hypothesis HC : diag_cells M can.
Theorem refuse_run : ltac2:(TCodec.tc2 tcn__Ja0DiagRefuse "X4'8'L&=y5'QFyR0%211%5241'5y8%611%311p061'6'F&Q2&NvQ@vB&QE+\Zc4%22@1v>&Q0%119%9587431r3r2+QS\h4%:2H1r1%?554217%B3A71'7&M&Q8uA%211%C2Q31%52<1+R2%F2Q41%93Q431u:%911%J2Q:1%<2C1+2%M2Q;1%@3Q;31u;%@11%Q12QA1%C2J1&Q:vQ3+b8%3221%Q72QE1%J3QE61u<%J11%Q;2QK1%M2Q41%O3QJ1@u9%O11%Q@2R01%Q22Q91+QVkb0%QC2R11%Q63R131uB%Q611%QG2R71%Q92Q@1%Q;3R61LuC%Q;11%QL2R<1%Q>2QE1%Q@3R;1GuF%Q@11%R12RA1%QC2QJ1+Q6%R42RB1%QG3RB31&J+^@%Q52Q41%34R=QNQ31+b0%Q82Q71%64R@R119+aH%Q;2Q:1z%:4RDR521+a@%Q?2Q>1%=4RGR814'2%11RN%S111&O%RH2S6@uQ6%34RNR?21(0&H%2281%R@3841&I+QVkeH%24S5RF1R5&G%13S0RHQO&Q1%12S2RJpSDSCS>&9&Q6&QG%12SHRO%32R51&Q7+a8%R;2R:1%3251%SF251%:11%S;1S:r6%11S<%S73SM31p051pSDT41r5%E21SA'3&Q4(1u2u3u4u8uEuGuHuIuJuK(4%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ES11%D3F@1%E3GB1%F3HD1%G3IF1%I3JT91%T51T=%TF2U61%T82Q41r9%T:213%T<3U731p071pS:Q21r8+QS\h@%TO2U=1r7%U459421TL+QR^Y4%U32UA1%U75TMTL1TITO%U:3U941%TF1Q9%U72UG1%TI2U01%U92UGT5%TL3UG21+5%R=4U@U1SJ1+QVke0%S84UBU31RO+QVkdH+Vam\H%S;4UEU621+QVkcH%S=4UGU81S4+QVkc8%S?4UIU:1S6+QVkc0%SA4UKU<1S8+QVkb8%SC4UMU>1S:+QVkb@%SE4UOU@1S<%U<1QM%UM2V=1%U?2UF1%U@2V02%UB3V=21%V7261%V8291%V92<1%V:2?1%V;2B1%V<2E1%V=2I1%V>2L1%V?2S41%V@2S71%VA2Q11%VB2U>1%VC2Q81qQ2VE1%W22VF1qQ:VL1%W42VM1qS8W41%W62W51p0QH1p0RL1p0RO1pQ4SA1pQ<W41pS4W;1%W02SE1%W12SH1%W22SK1%W32SO1%W42T;1%W52T?1%W62TD1%W72TH1%W82TM1%W92U51%W:2U;1%W;2UA1%W<2UI1%W=2UO1%W>2V:1%W?2VB1%W@2VM1qQ0WB1%WO2WC1qQ8WI1%X12WJ1qS6X11%X32X21").
Proof.
pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
pose proof (u64_of_zeros M 2147464496 HFMT ltac:(lia) ltac:(lia)) as HFMT64.
assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
cfeed P (dfA_conc fx R M (fun j => match j with 2%nat => S | 40%nat => can | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz | shz0]).
dk_open P as fx1 R1 M1 MG1 FR1 FZ1 MS1 KS1.
assert (A01 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M1 x = M x) by (intros x Hx Hf; unfold filew in Hf; apply FR1; lia).
assert (W1 : L5.writable RSEGS M1 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (NE : Z.eqb (S - 426) (S - 464) = false) by (apply Z.eqb_neq; lia).
destruct (wv_entry_stage fx1 R1 M1 1273408 (S - 592) 0 0 (S - 426) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG1W & MGW);
[ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
rewrite NE in W11, W12, W18, W19.
assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG1W by lia; apply A01; assumption).
assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
destruct (u8s_of_u32 M1 (S - 440) 1936028793 121 116 101 115) as (Y0 & Y1 & Y2 & Y3); [lia | lia | assumption | vm_compute; reflexivity|].
destruct (u8s_of_u32 M1 (S - 436) 1701978156 44 32 114 101) as (Y4 & Y5 & Y6 & Y7); [lia | lia | assumption | vm_compute; reflexivity|].
destruct (u8s_of_u32 M1 (S - 432) 1702065510 102 117 115 101) as (Y8 & Y9 & Y10 & Y11); [lia | lia | assumption | vm_compute; reflexivity|].
replace (S - 440 + 1) with (S - 439) in Y1 by (clear; lia).
replace (S - 440 + 2) with (S - 438) in Y2 by (clear; lia).
replace (S - 440 + 3) with (S - 437) in Y3 by (clear; lia).
replace (S - 436 + 1) with (S - 435) in Y5 by (clear; lia).
replace (S - 436 + 2) with (S - 434) in Y6 by (clear; lia).
replace (S - 436 + 3) with (S - 433) in Y7 by (clear; lia).
replace (S - 432 + 1) with (S - 431) in Y9 by (clear; lia).
replace (S - 432 + 2) with (S - 430) in Y10 by (clear; lia).
replace (S - 432 + 3) with (S - 429) in Y11 by (clear; lia).
assert (BUF1 : rdn RSEGS M1 (Z_to_bv 64 (S - 464)) 38 = Some MSGR) by (unfold MSGR; cbn [map]; rdn_bytes).
assert (BUFW : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 38 = Some MSGR) by (apply (rdn_xfer M1 MW); [intros x Hx; apply AG1W; cbn in Hx; lia | lia | cbn; lia | exact BUF1]).
exists fx1, RW, MW.
split. { eapply msteps_trans; [exact MS1|]. exact MSW. }
split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
split; [replace (S - 584) with (S - 592 + 8) by lia; exact I0|]. split; [replace (S - 426 - (S - 464)) with 38 in I1 by lia; replace (S - 576) with (S - 592 + 16) by lia; exact I1|].
split; [replace (S - 568) with (S - 592 + 24) by lia; exact I2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact I3|].
split; [exact BUFW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
intros fx' RX MX AGXW MGXW KXW.
assert (AGX1 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = M1 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG1W; lia).
assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R1 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
assert (IMGX : L5.img_clear MX 65536 1261568) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
assert (FWX : L5.writable RSEGS MX 1273408 152) by (eapply writable_grows; eassumption).
cfeed P (dfG_conc fx' RX MX (fun j => match j with 2%nat => S - 592 | 40%nat => can
| 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
| 118%nat => U RX 18 | 119%nat => U RX 19 | 120%nat => U RX 20 | 122%nat => U RX 22 | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz]).
dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
exists fxF, RF, MF.
split; [exact MSF|]. split; [sc|]. split; [sc|].
split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. apply AGX0; [exact Hx | unfold filew; lia]. }
split; [eapply mem_grows_trans; [exact MG0X | exact MGF]|].
repeat split; first [sc | (eapply (DK.u64_ext M1); [intros x Hx; rewrite FRF by lia; apply AGX1; lia | lia | lia | eassumption])
| (rewrite (KSF 4%nat), (KX 4%nat), (KS1 4%nat) by (first [apply L5K.in_b; vm_compute; reflexivity | cbn; tauto]); reflexivity)].
Qed.
End RF.
End DRF.
