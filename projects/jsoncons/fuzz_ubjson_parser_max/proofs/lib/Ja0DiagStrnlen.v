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
Ja0RegionPoisoned Ja0AsanMemcpy Ja0Memchr Ja0DiagKit Ja0DiagChk Ja0DiagSP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DiagStrnlen () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DiagStrnlen.DSN."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4bvmap"; "0M"; "0M'"; "0R"]; ["0R'"; "5msteps"; "6cstr"; "6sn_cells"; "7FPState"; "7getr"; "7mkst"; "7seg_rom"; "8mem_grows"; "9loaded_segments"; ":In"; ";add"; ";le"; ";lt"; ";of_nat"; ";pow"]; [";sub"; "0a"; "0bs"; "0fx"; "0fx'"; "0hi"; "0k"; "0lo"; "0p"; "0s"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0t8"; "0w"; "0x"]; ["0z"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module DSN.
Import DK. Import AS0DIAGSP.
Local Ltac alia := first [ lia | match goal with H : _ \/ _ |- _ => destruct H; lia end ].
Local Ltac sc := first [ assumption | reflexivity | dk_gmem | (dk_arith_goal; alia) ].
Record cstr (M : word -> option byte) (p : Z) (bs t8 : list byte) : Prop := CSTR {
cs_rd : rdn RSEGS M (Z_to_bv 64 p) (length bs + 9) = Some (bs ++ Z_to_bv 8 0 :: t8);
cs_t8 : length t8 = 8%nat;
cs_nz : forall j, (j < length bs)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) <> 0 }.
Lemma cstr_ext : ltac2:(TCodec.tc2 tcn__Ja0DiagStrnlen "R1'Q;yR0%211'6y8%511%311pS051';'3%115&Lzr3%3221&Kr4&N&2%12>6%311%6251+9%8221&O+2+R0%3221%A251'7r6&Q<r1%22Q01%G241&Mr5%C2Q01%E11%H291%I21B%6281%=281'8r8r2%211r9%113%63Q;31p081pS0QA1'B%149GAQ5r7%34;1ICp031p061p0N1p0Q=1pRLQB1pR6QC1pRBQF1pNQH1pLQI1").
Proof. intros M M' p bs t8.
intros Hp Hn AG [A B C]. constructor; [|exact B|exact C].
apply (rdn_xfer M M'); [intros x Hx; apply AG; lia | lia | lia | exact A].
Qed.
Definition sn_cells (M : word -> option byte) : Prop :=
L5.u8_at RSEGS M 1292760 1
/\ L5.u64_at RSEGS M 1263088 1201360
/\ L5.u64_at RSEGS M 1262720 1198256
/\ rt_layout_globs M
/\ rdn RSEGS M (0x132628 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1cc828))
/\ rdn RSEGS M (0x1cc923 : word) 1%nat = Some [Z_to_bv 8 1].
Lemma lit_word : ltac2:(TCodec.tc2 tcn__Ja0DiagStrnlen "A';'Q;yR0%211'8&Q<r1%2251r2%53921&Q:r3%22:1%93:51p051pRN<1pS2@1").
Proof. intros z w. intros <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma sn_cells_ext : ltac2:(TCodec.tc2 tcn__Ja0DiagStrnlen "M'Q;yR0%211'6y8%511%311pS051&M&Q<r1%22:1+`PPP0%5221'8r3r2%211r4%113%63>31p081pS0D1&C%119p011p041pND1pLE1").
Proof. intros M M'.
intros AG (C1 & C2 & C3 & (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & C5 & C6).
assert (X : forall (w : word) k bs, bv_unsigned w + Z.of_nat k <= 0x1000000 -> rdn RSEGS M w k = Some bs -> rdn RSEGS M' w k = Some bs).
{ intros w k bs Hw H. rewrite <- H. pose proof (bv_unsigned_in_range _ w) as Rw. apply rdn_ext; [lia|]. intros x Hx. apply AG. lia. }
unfold sn_cells, rt_layout_globs.
repeat split; first [ (eapply u8_ext; [intros x Hx; apply AG; lia | lia | lia | eassumption])
| (eapply u64_ext; [intros x Hx; apply AG; lia | lia | lia | eassumption])
| (apply X; [vm_compute; intros Q; discriminate Q | assumption]) ].
Qed.
Lemma shadow_ext : ltac2:(TCodec.tc2 tcn__Ja0DiagStrnlen "QE'Q;yR0%211'6y8%511%311p051';'7&Lr3&Q<r1%22=1%5241&Mr2%2241%:241'8r5%115r6%117%53C31p071pS0I1r4%C21?%>2@C%F221r7%11@(0&Q:z%22Q11%42Q11%C3Q161p091pS0Q71%Q02EL%K2M?%Q3221p016pS0Q<1p061p0E1pR<Q91pR@Q:1pNQ<1pLQ=1").
Proof. intros M M' lo hi. intros AG H x Hx. rewrite AG by exact Hx. apply H. exact Hx. Qed.
Ltac xf Ms AG :=
first [ dk_gmem
| (eapply (u64_ext Ms); [intros ? ?; apply AG; alia | alia | alia | dk_gmem])
| (eapply (u32_ext Ms); [intros ? ?; apply AG; alia | alia | alia | dk_gmem])
| (eapply (u8_ext Ms); [intros ? ?; apply AG; alia | alia | alia | dk_gmem]) ].
Section SN.
Context (fx : FPState).
Variables (R : bvmap 5 word) (M : word -> option byte) (s p : Z) (bs t8 : list byte).
#[local] Notation n := (Z.of_nat (length bs)).
Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 1165708.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 s.
Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 p.
Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 2147483647.
Hypothesis Hs : 140735332552704 + 4400 <= s <= 140737488355328.
Hypothesis Hal : s mod 16 = 0.
Hypothesis HW : L5.writable RSEGS M (s - 4400) 4400.
Hypothesis HD : L5.defined M (s - 4400) 4400.
Hypothesis HIMG : L5.img_clear M 65536 1261568.
Hypothesis Hp : s <= p /\ p + n + 1 + 16 <= 2 ^ 47.
Hypothesis Hn : n <= 131071.
Hypothesis HSTR : cstr M p bs t8.
Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
Hypothesis HC : sn_cells M.
Theorem wrap_strnlen_run : ltac2:(TCodec.tc2 tcn__Ja0DiagStrnlen "SH'9'D&<y5'Q;yR0%211%5241'6y8%611%311p061'7'A&I&FvQ3v?&Q:+\Z`H%22@1v=&G%119%9587431r3r2+QSb\<%:2H1r1%?554217%B3A71'8&E&Nu:%211%C2Q31%52<1&2vQ2%22Q01%811%I2Q71%<3Q761'4&J(1u2u3u4u8u9uBuCuDuEuFuGuHuIuJuK(5%11C%B3D31%C3E51%D3F71%E3G91%F3H;1%G3I=1%H3J?1%I3KA1%J3LC1%K3ME1%L3NG1%M3OI1%N3Q0K1%O3Q1M1%Q03Q2O1%Q23Q3QC1r4%Q@1QH%R12RA1%QC231%QD2R42%QF3RA21p071pR>Q;1&:&L&Q0vQ9+TY@%3221&Q<%12RLR3%7231&M%1237%RH231%<11%R=1R<%RB1R=%R83RN21p041pR4S51&H%12RGR?%S1231%S22F1%S32R31%S42RA1qNS61%SC2S71qQ2S=1%SE2S>1qR:SE1%SG2SF1").
Proof.
pose proof HC as (C1 & C2 & C3 & CG & C5 & C6).
assert (Pr : 140735332552704 <= p <= 140737488355311) by lia.
assert (Nr : 0 <= n <= 131071) by lia.
cfeed P (sC1_conc fx R M (fun j => match j with 2%nat => s | 33%nat => p | 34%nat => n | _ => 0 end)) ltac:(first [apply UR | apply U_to | sc]).
destruct P as (fx1 & R1 & M1 & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR11 & aR12 & aR13 & aR18 & aR19 & aR20 & aC1 & aC2 & aC3 & aC4 & aC5 & aC6 & aC7 & aC8 & aC9 & aC10 & aC11 & aC12 & aC13 & aC14 & aC15 & aC16 & aC17 & aC18 & aD1 & aD2 & aD3)).
assert (AG1 : forall x : word, bv_unsigned x < s - 4320 \/ s <= bv_unsigned x -> M1 x = M x) by (intros x Hx; apply aFR; lia).
assert (STR1 : cstr M1 p bs t8) by (apply (cstr_ext M M1); [lia | lia | intros x Hx; apply AG1; lia | exact HSTR]).
assert (HC1 : sn_cells M1) by (apply (sn_cells_ext M M1); [intros x Hx; apply AG1; lia | exact HC]).
assert (HSH1 : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M1 x = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite AG1; [apply HSH; exact Hx|]. left. unfold SB in Hx. assert ((p + n) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
assert (IMG1 : L5.img_clear M1 65536 1261568) by (apply (imgc_ext M M1); [intros x Hx; apply AG1; lia | lia | lia | exact HIMG]).
assert (MH : mchrH M1 (Z_to_bv 64 p) (bs ++ Z_to_bv 8 0 :: t8) n 2147483647).
{ destruct STR1 as [SA SB' SC']. constructor.
- rewrite length_app. cbn [length]. rewrite SB'. replace (length bs + 9)%nat with (length bs + 9)%nat in SA by lia. exact SA.
- rewrite L5.unsigned_lit by lia. rewrite length_app. cbn [length]. rewrite SB'. pose proof (Z.mul_div_le (p + n) 8 ltac:(lia)). lia.
- rewrite L5.unsigned_lit by lia. rewrite length_app. cbn [length]. rewrite SB'. lia.
- lia.
- rewrite Nat2Z.id. rewrite app_nth2 by lia. replace (length bs - length bs)%nat with 0%nat by lia. reflexivity.
- intros j Hj. rewrite Nat2Z.id in Hj. rewrite app_nth1 by lia. apply SC'. exact Hj.
- lia.
- lia.
- intros i Hi. apply IMG1. lia. }
assert (RET1 : ret_ok (Z_to_bv 64 411432)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
pose proof aR1 as bR1. pose proof aR11 as bR11. pose proof aR12 as bR12. dk_fpreg_in bR1. dk_fpreg_in bR11. dk_fpreg_in bR12.
assert (bR10 : getr R1 10%bv = Z_to_bv 64 p).
{ rewrite <- (getr_reg R1 10 10%bv eq_refl). rewrite (aKS 10%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact G10. }
destruct (ref_memchr0 M1 (Z_to_bv 64 p) _ n 2147483647 (seg_rom RSEGS) R1 (Z_to_bv 64 411432) MH RET1 bR1 bR10 bR11 bR12) as (R2 & RUN2 & K2 & V2).
rewrite L5.unsigned_lit in V2 by lia.
assert (W1 : L5.writable RSEGS M1 (s - 4400) 4400) by (eapply writable_grows; eassumption).
assert (D1 : L5.defined M1 (s - 4400) 4400) by (eapply defined_grows; eassumption).
assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (CP2 : chk_pre M1 p (n + 1) (s - 4304)).
{ destruct HC1 as (_ & _ & _ & CG1 & _). unfold chk_pre. replace (p + (n + 1) - 1) with (p + n) by lia. unfold SB in *.
split; [lia|]. split; [right; unfold HIGHBEG, HIGHEND; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [apply (store_ok_of_writable_sub M1 (s - 4400) 4400); [exact W1 | lia | cbn; lia]|]. split; [exact CG1 | exact HSH1]. }
assert (bR18 : getr R2 18%bv = Z_to_bv 64 p) by (rewrite (K2 18%bv) by (cbv; tauto); rewrite <- (getr_reg R1 18 18%bv eq_refl); exact aR18).
assert (bR20 : getr R2 20%bv = Z_to_bv 64 1) by (rewrite (K2 20%bv) by (cbv; tauto); rewrite <- (getr_reg R1 20 20%bv eq_refl); exact aR20).
assert (bR2 : getr R2 2%bv = Z_to_bv 64 (s - 4304)) by (rewrite (K2 2%bv) by (cbv; tauto); rewrite <- (getr_reg R1 2 2%bv eq_refl); exact aR2).
destruct (chk2 M1 (seg_rom RSEGS) p (n + 1) (s - 4304) R2 CP2 ltac:(replace (p + (n + 1) - 1) with (p + n) by lia; exact V2) bR18 bR20 bR2)
as (R3 & M3 & RUN3 & V3 & K3 & (AG3 & MG3)).
replace (p + (n + 1) - 1) with (p + n) in V3 by lia.
assert (W3 : L5.writable RSEGS M3 (s - 4400) 4400) by (eapply writable_grows; eassumption).
assert (D3 : L5.defined M3 (s - 4400) 4400) by (eapply defined_grows; eassumption).
assert (AG3' : forall x : word, bv_unsigned x < s - 4376 \/ s - 4304 <= bv_unsigned x -> M3 x = M1 x) by (intros x Hx; apply AG3; lia).
assert (IMG3 : L5.img_clear M3 65536 1261568) by (apply (imgc_ext M1 M3); [intros x Hx; apply AG3'; lia | lia | lia | exact IMG1]).
assert (cR2 : getr R3 (reg 2) = Z_to_bv 64 (s - 4304)).
{ transitivity (getr R2 (reg 2)); [dk_kb K3|]. rewrite (keeps_cs_reg R1 R2 2 K2) by (cbn; tauto). exact aR2. }
assert (cR10 : getr R3 (reg 10) = Z_to_bv 64 (p + n)) by (rewrite (getr_reg R3 10 10%bv eq_refl); exact V3).
cfeed P (sC3_conc fx1 R3 M3 (fun j => match j with 2%nat => s - 4304 | 33%nat => p | 34%nat => n | 20%nat => U R 20 | 21%nat => U R 21
| 120%nat => U R3 20 | 121%nat => U R3 21 | _ => 0 end)) ltac:(first [apply UR | apply U_to | sc | xf M1 AG3']).
destruct P as (fx4 & R4 & M4 & MG4 & dFR & dFZ & (dMS & dKS & dR1 & dR2 & dR8 & dR9 & dR10 & dR18 & dR19 & dR20 & dR21)).
assert (AG4 : forall x : word, bv_unsigned x < s - 4320 \/ s - 4304 <= bv_unsigned x -> M4 x = M3 x) by (intros x Hx; apply dFR; lia).
assert (AG41 : forall x : word, bv_unsigned x < s - 4376 \/ s - 4304 <= bv_unsigned x -> M4 x = M1 x) by (intros x Hx; rewrite AG4 by lia; apply AG3'; lia).
assert (W4 : L5.writable RSEGS M4 (s - 4400) 4400) by (eapply writable_grows; eassumption).
assert (HC4 : sn_cells M4) by (apply (sn_cells_ext M1 M4); [intros x Hx; apply AG41; lia | exact HC1]).
assert (CP3 : chk_pre M4 p (n + 1) (s - 2144)).
{ destruct HC4 as (_ & _ & _ & CG4 & _). unfold chk_pre. replace (p + (n + 1) - 1) with (p + n) by lia. unfold SB in *.
split; [lia|]. split; [right; unfold HIGHBEG, HIGHEND; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [apply (store_ok_of_writable_sub M4 (s - 4400) 4400); [exact W4 | lia | cbn; lia]|]. split; [exact CG4|].
intros x Hx. rewrite AG41 by lia. apply HSH1. exact Hx. }
pose proof dR10 as eR10. pose proof dR9 as eR9. pose proof dR18 as eR18. pose proof dR19 as eR19. pose proof dR2 as eR2.
dk_fpreg_in eR10. dk_fpreg_in eR9. dk_fpreg_in eR18. dk_fpreg_in eR19. dk_fpreg_in eR2. replace (s - 4304 + 2160) with (s - 2144) in eR2 by lia.
destruct HC4 as (_ & _ & _ & _ & C45 & C46).
destruct (chk3 M4 (seg_rom RSEGS) p (n + 1) (s - 2144) 2147483647 R4 CP3 ltac:(lia) C45 C46
ltac:(replace (n + 1 - 1) with n by lia; exact eR10) eR9 eR18 eR19 eR2) as (R5 & M5 & RUN5 & V5 & K5 & (AG5 & MG5)).
replace (n + 1 - 1) with n in V5 by lia.
assert (W5 : L5.writable RSEGS M5 (s - 4400) 4400) by (eapply writable_grows; eassumption).
assert (D5 : L5.defined M5 (s - 4400) 4400) by (eapply defined_grows; [exact MG5 | eapply defined_grows; [exact MG4 | exact D3]]).
assert (AG51 : forall x : word, s - 2144 <= bv_unsigned x -> M5 x = M1 x) by (intros x Hx; rewrite AG5 by lia; apply AG41; lia).
assert (IMG5 : L5.img_clear M5 65536 1261568).
{ apply (imgc_ext M1 M5); [intros x Hx; rewrite AG5 by lia; apply AG41; lia | lia | lia | exact IMG1]. }
assert (fR2 : getr R5 (reg 2) = Z_to_bv 64 (s - 2144)) by (transitivity (getr R4 (reg 2)); [dk_kb K5 | rewrite dR2; f_equal; lia]).
cfeed P (sC4_conc fx4 R5 M5 (fun j => match j with 2%nat => s - 2144 | 33%nat => p | 34%nat => n
| 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
| 108%nat => U R5 8 | 109%nat => U R5 9 | 118%nat => U R5 18 | 119%nat => U R5 19 | 120%nat => U R5 20 | 121%nat => U R5 21 | 122%nat => U R5 22
| _ => 0 end)) ltac:(first [apply UR | apply U_to | sc | xf M1 AG51]).
destruct P as (fx6 & R6 & M6 & MG6 & gFR & gFZ & (gMS & gKS & gR1 & gR2 & gR8 & gR9 & gR18 & gR19 & gR20 & gR21 & gR22)).
replace (0x1248b0%bv : word) with (Z_to_bv 64 0x1248b0) in RUN2 by (apply bv_eq; reflexivity).
replace (0x64728%bv : word) with (Z_to_bv 64 411432) in RUN3 by (apply bv_eq; reflexivity).
replace (0x64788%bv : word) with (Z_to_bv 64 0x64788) in RUN3 by (apply bv_eq; reflexivity).
replace (0x62ddc%bv : word) with (Z_to_bv 64 0x62ddc) in RUN5 by (apply bv_eq; reflexivity).
replace (0x62e50%bv : word) with (Z_to_bv 64 0x62e50) in RUN5 by (apply bv_eq; reflexivity).
assert (KK : forall k, In k [3; 4; 23; 24; 25; 26; 27]%nat -> getr R6 (reg k) = getr R (reg k)).
{ intros k Hk.
rewrite (gKS k) by (revert Hk; apply (L5K.incl_b [3; 4; 23; 24; 25; 26; 27]%nat KS_sC4); vm_compute; reflexivity).
transitivity (getr R4 (reg k)).
{ cbn in Hk. repeat (destruct Hk as [<-|Hk]; [dk_kb K5|]). destruct Hk. }
rewrite (dKS k) by (revert Hk; apply (L5K.incl_b [3; 4; 23; 24; 25; 26; 27]%nat KS_sC3); vm_compute; reflexivity).
transitivity (getr R2 (reg k)).
{ cbn in Hk. repeat (destruct Hk as [<-|Hk]; [dk_kb K3|]). destruct Hk. }
rewrite (keeps_cs_reg R1 R2 k K2) by (cbn in Hk |- *; tauto).
apply aKS. revert Hk; apply (L5K.incl_b [3; 4; 23; 24; 25; 26; 27]%nat KS_sC1); vm_compute; reflexivity. }
exists fx6, R6, M6. split; [|split; [|split; [|split]]].
- eapply msteps_trans; [exact aMS|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
eapply msteps_trans; [exact dMS|]. eapply msteps_trans; [exact RUN5|]. exact gMS.
- rewrite (gKS 10%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (getr_reg R5 10 10%bv eq_refl). exact V5.
- intros k Hk. cbn in Hk.
destruct Hk as [<-|Hk]; [rewrite gR2, G2; f_equal; lia|].
destruct Hk as [<-|Hk]; [apply KK; cbn; tauto|]. destruct Hk as [<-|Hk]; [apply KK; cbn; tauto|].
destruct Hk as [<-|Hk]; [rewrite gR8; symmetry; apply U_to|]. destruct Hk as [<-|Hk]; [rewrite gR9; symmetry; apply U_to|].
destruct Hk as [<-|Hk]; [rewrite gR18; symmetry; apply U_to|]. destruct Hk as [<-|Hk]; [rewrite gR19; symmetry; apply U_to|].
destruct Hk as [<-|Hk]; [rewrite gR20; symmetry; apply U_to|]. destruct Hk as [<-|Hk]; [rewrite gR21; symmetry; apply U_to|].
destruct Hk as [<-|Hk]; [rewrite gR22; symmetry; apply U_to|].
apply KK. cbn. tauto.
- intros a Ha. rewrite gFR by lia. rewrite AG5 by lia. rewrite AG41 by lia. apply AG1. lia.
- eapply mem_grows_trans; [exact MG1|]. eapply mem_grows_trans; [exact MG3|]. eapply mem_grows_trans; [exact MG4|]. eapply mem_grows_trans; [exact MG5|]. exact MG6.
Qed.
End SN.
End DSN.
