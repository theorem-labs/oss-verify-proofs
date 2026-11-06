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
Jb0RegionPoisoned Jb0AsanMemcpy Jb0DiagKit Jb0DiagChk Jb0DiagMemcpy Jb0DiagStrnlen Jb0DiagGlue Jb0DiagRP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DiagRefuse () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagGlue.DG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DiagRefuse.DRF."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3bvmap"; "0M"; "0ME"; "0MF"; "0MX"; "0R"]; ["0RE"; "0RF"; "0RX"; "4msteps"; "5agree0"; "6MSGR"; "7u32_at"; "7u64_at"; "8FPState"; "8getr"; "8mkst"; "8rdn"; "8seg_rom"; "9mem_grows"; ":loaded_segments"; "0S"]; [";In"; "<le"; "<lt"; "<of_nat"; "<sub"; "0fx"; "0fx'"; "0fxE"; "0fxF"; "0k"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module DRF.
Import DK. Import DSN. Import DG. Import AS0DIAGRP.
Definition MSGR : list byte := map (Z_to_bv 8)
[99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].
Ltac rdn_bytes :=
repeat (apply rdn_cons; [lia | cbn; lia | (match goal with |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => try (progress (ring_simplify a)) end; match goal with H : L5.u8_at _ _ ?a _ |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ => exact H end) | ]);
reflexivity.
Ltac shz0 := lazymatch goal with |- L5KA.zeros_at ?M (?S / 8 + ?d) ?l => unfold SB in *; dk_gmem end.
Section RF.
Context (fx : FPState).
Variables (R : bvmap 5 word) (M : word -> option byte) (S can : Z).
Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 685792.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1280936.
Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 109065.
Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 67108864.
Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
Hypothesis Hal : S mod 16 = 0.
Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
Hypothesis HD : L5.defined M (S - 5440) 5440.
Hypothesis HIMG : L5.img_clear M 65536 1269760.
Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.
Hypothesis HFMT : L5KA.zeros_at M 2147464512 8.
Hypothesis Hcan : 0 <= can < 2 ^ 64.
Hypothesis HC : diag_cells M can.
Theorem refuse_run : ltac2:(TCodec.tc2 tcn__Jb0DiagRefuse "X4'8'H&:y5'Q;yR0%211%5241'5y8%611%311p061'6'C&N&JvQ5v?&Q:+\[YD%22@1v;&L%119%9587431r3r2+QSdYL%:2H1r1%?554217%B3A71'7&I&Q3uA%211%C2Q31%52<1+R2%F2Q41%93Q431u:%911%J2Q:1%<2C1+2%M2Q;1%@3Q;31u;%@11%Q12QA1%C2J1&Q4vO+b8%3221%Q72QE1%J3QE61u<%J11%Q;2QK1%M2Q41%O3QJ1@u9%O11%Q@2R01%Q22Q91+QWRm8%QC2R11%Q63R131uB%Q611%QG2R71%Q92Q@1%Q;3R61LuC%Q;11%QL2R<1%Q>2QE1%Q@3R;1GuF%Q@11%R12RA1%QC2QJ1+Q6%R42RB1%QG3RB31&G+^@%Q52Q41%34R=QNQ31+b0%Q82Q71%64R@R119+aH%Q;2Q:1z%:4RDR521+a@%Q?2Q>1%=4RGR814'2%11RN%S111&K%RH2S6@uQ6%34RNR?21(0&E%2281%R@3841&F+QWSQ0%24S5RF1R5&D%13S0RHQO&M%12S2RJpRLSCS>&9&Q1&Q<%12SHRO%32R51&Q2+a8%R;2R:1%3251%SF251%:11%S;1S:r6%11S<%S73SM31p051pRLT41r5%E21SA'3&Q0(1u2u3u4u8uEuGuHuIuJuK(4%11>%=3?31%>3@51%?3A71%@3B91%A3C;1%B3D=1%C3ES11%D3F@1%E3GB1%F3HD1%G3IF1%I3JT91%T51T=%TF2U61%T82Q41r9%T:213%T<3U731p071pRDQ21r8+QSdZ8%TO2U=1r7%U459421TL+QRejL%U32UA1%U75TMTL1TITO%U:3U941%TF1Q9%U72UG1%TI2U01%U92UGT5%TL3UG21+5%R=4U@U1SJ1+QWSP8%S84UBU31RO+QWSP0+VbTfH%S;4UEU621+QWRo0%S=4UGU81S4+QWRn@%S?4UIU:1S6+QWRn8%SA4UKU<1S8+QWRm@%SC4UMU>1S:+QWRmH%SE4UOU@1S<%U<1QM%UM2V=1%U?2UF1%U@2V02%UB3V=21%V7261%V8291%V92<1%V:2?1%V;2B1%V<2E1%V=2I1%V>2L1%V?2S41%V@2S71%VA2Q11%VB2U>1%VC2Q81qLVE1%W22VF1qQ4VL1%W42VM1qRBW41%W62W51p0QH1p0RL1p0RO1pNSA1pQ6W41pR>W;1%W02SE1%W12SH1%W22SK1%W32SO1%W42T;1%W52T?1%W62TD1%W72TH1%W82TM1%W92U51%W:2U;1%W;2UA1%W<2UI1%W=2UO1%W>2V:1%W?2VB1%W@2VM1qJWB1%WO2WC1qQ2WI1%X12WJ1qR@X11%X32X21").
Proof.
pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
pose proof (u64_of_zeros M 2147464512 HFMT ltac:(lia) ltac:(lia)) as HFMT64.
assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
cfeed P (dfA_conc fx R M (fun j => match j with 2%nat => S | 40%nat => can | _ => 0 end)) ltac:(first [apply UR | apply U_to | scc | shz | shz0]).
dk_open P as fx1 R1 M1 MG1 FR1 FZ1 MS1 KS1.
assert (A01 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M1 x = M x) by (intros x Hx Hf; unfold filew in Hf; apply FR1; lia).
assert (W1 : L5.writable RSEGS M1 (S - 5440) 5440) by (eapply writable_grows; eassumption).
assert (NE : Z.eqb (S - 426) (S - 464) = false) by (apply Z.eqb_neq; lia).
destruct (wv_entry_stage fx1 R1 M1 1280936 (S - 592) 0 0 (S - 426) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG1W & MGW);
[ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
rewrite NE in W11, W12, W18, W19.
assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG1W by lia; apply A01; assumption).
assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
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
assert (IMGX : L5.img_clear MX 65536 1269760) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
assert (FWX : L5.writable RSEGS MX 1280936 152) by (eapply writable_grows; eassumption).
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
