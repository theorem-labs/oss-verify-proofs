(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem JatPoison JatInitCache JatPopulate1 ArtRuns JatCls JatFp JatClsRep JatSecAllocPost
JatRecycle2C JatRecycle3L JatRecycle4P JatRecycle4S JatRecycle5A JatRecycle5I.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatRecycle5G () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5G.Gap."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle5I."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1fst"; "1option"; "1snd"; "2and"; "3Z"; "0G"; "0HI"; "0M"; "4apart"; "5art_gap"; "6art_rel"; "6art_rel_zone"; "6art_rg"; "7art_bl_geo"; "7art_rel_geo"; "8art_rcy_inv"]; ["8art_rcy_prot"; "8art_rel_fp"; "8art_rel_pre"; "9add"; "9le"; "9lt"; "9pow"; "9sub"; "0a"; "0ctx"; "0e"; "0key"; "0n"; "0nt"; "0parr"; "0qs"]; ["0ris"; "0sp1"; "0spb"; ":bv"; "0t"; "0tp"; "0tsd"; "0zlen"; "0zlo"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section Gap.
Variables (HI t ctx tp key tsd spb ris qs parr : Z).
Hypothesis GEO : art_geo HI t ctx tp tsd spb ris qs.
Definition art_rel_geo (G : art_rg) (e : art_rel) : Prop :=
match e with
| REP c w d b1 n =>
1 <= c <= 30 /\ 0 <= w /\ 16 * w + AsanTab.class_size c <= 3758096384 /\ 0 <= d /\ d mod 16 = 0 /\ d + 16 + (n + 7) / 8 * 8 <= AsanTab.class_size c /\ 0 <= n
/\ 4 * Z.of_nat (length (cl_free (rg_cls G c))) + 32 <= 2 ^ 29
| RES mb ms m b1 n =>
In (mb, ms) (rg_bl G)
| REB wb => 0 <= wb /\ 16 * wb + 8192 <= 3758096384 /\ 4 * Z.of_nat (length (cl_free (rg_cls G 24))) + 32 <= 2 ^ 29
end.
Definition art_bl_geo (G : art_rg) : Prop :=
art_sec_geo HI t ctx parr (rg_bl G) /\ (forall b, In b (rg_bl G) -> apart (fst b) (snd b) spb (2 ^ 37 + 4096)) /\ apart parr (8 * Z.of_nat (length (rg_bl G))) spb (2 ^ 37 + 4096).
Section SE.
Local Abbreviation SEC_T_art_rel_geo_of_inv := (ltac2:(TCodec.tc2 tcn__JatRecycle5G "Q='4'<'Q3yR0%211'1y8%511%311p051':&Dzr4%3221&?v6vQ4vIvQ5vKvQ6vQ2vQ0vOvNr5r3%==<;:98765432?1&B%1243'3&>r6%221E&=%113%6231p081p0;1p0J1pQFO1p@Q11p<Q:1pQLQ<1")) (only parsing).
Variable nt : ltac:(sec_ty2 constr:(SEC_T_art_rel_geo_of_inv) 0%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_rel_geo_of_inv) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rel_geo_of_inv) 2%nat 0%nat).
Lemma art_rel_geo_of_inv : ltac:(sec_stmt2 constr:(SEC_T_art_rel_geo_of_inv) 3%nat 0%nat).
Proof using Type nt G M.
intros e Hnt (ICLS & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG & IBK & IPK) PRE.
split; [|split; [exact ISG|split; [exact IBK|exact IPK]]].
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_geo art_rel_pre] in *.
- destruct PRE as (Hc & (Hw0 & Hwsz & _) & _ & Hd & Hd16 & Hdsz & _ & Hn). destruct (ICLS c Hc) as (_ & OK & _ & Rm).
destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _ & (_ & Hmfa1) & Hnf4 & _ & _). pose proof (art_class_size_facts c Hc) as (Hsz & _).
specialize (Rm ltac:(lia)). repeat split; try assumption; lia.
- destruct PRE as (Hin & _). exact Hin.
- destruct PRE as ((Hw0 & Hwsz & _) & _). destruct (ICLS 24 ltac:(lia)) as (_ & OK & _ & Rm).
destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _ & (_ & Hmfa1) & Hnf4 & _ & _).
specialize (Rm ltac:(lia)). repeat split; try assumption; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rel_fp_above := (ltac2:(TCodec.tc2 tcn__JatRecycle5G "QB'4'<':&>r4r3%3221&=r5%211&Dv6&Gr7+Z0%3221%6251&Er8&F+2+Q?%3221%6251r9r6%@221z%B213&9&AvQ4vQ2vQ0vNr;r:%77654321=%931DIp0;1p0>1p0B1p0J1p0Q21p0Q61pQJQ=1pQBQ>1pQFQ=1p<Q?1pR4QA1")) (only parsing).
Variable sp1 : ltac:(sec_ty2 constr:(SEC_T_art_rel_fp_above) 0%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_rel_fp_above) 1%nat 0%nat).
Lemma art_rel_fp_above : ltac:(sec_stmt2 constr:(SEC_T_art_rel_fp_above) 2%nat 0%nat).
Proof using tp tsd qs GEO sp1 G.
intros e a n RG BG HHI Hsp' Ha Hn0.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & _ & _ & _ & _ & G13 & G14 & _ & _ & _ & _ & G19 & G20 & G21 & G22).
destruct BG as (ISG & IBK & IPK). pose proof ISG as (Gp1 & Gp2 & Gp3 & Gp4 & Apt & Apc & GB & GD).
destruct e as [c w d b1 n'|mb ms m b1 n'|wb]; cbn [art_rel_geo art_rel_fp] in *.
- destruct RG as (Hc & Hw0 & Hwsz & Hd & Hd16 & Hdsz & Hn' & Hnf).
pose proof (art_class_size_facts c Hc) as (Hsz & _).
set (rs := (n' + 7) / 8 * 8) in *. set (m := spb + c * 2 ^ 32 + 16 * w + d) in *.
assert (Hrs : 0 <= rs /\ rs mod 8 = 0).
{ unfold rs. pose proof (Z.div_mod (n' + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n' + 7) 8 ltac:(lia)) as B. split; [lia|apply Z_mod_mult]. }
destruct Hrs as (Hrs0 & Hrs8).
pose proof (Z.div_mod (m + 16) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (m + 16) 8 ltac:(lia)) as Bq.
pose proof (Z.div_mod rs 8 ltac:(lia)) as Dr. rewrite Hrs8 in Dr.
assert (Em : m = spb + c * 2 ^ 32 + 16 * w + d) by reflexivity.
unfold art_cbr_prim_fp, art_lcd_fp. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hn0 Hc Hw0 Hwsz Hd Hdsz Hsz Hrs0 Dq Bq Dr Em Hnf; unfold apart in *; cbn in *; lia)].
- pose proof RG as Hin. destruct (GB _ Hin) as (Hmb4k & Hms4k & Hmb0 & Hmb1 & Hmb2 & _). cbn [fst snd] in *.
assert (Hidx : (art_bl_idx mb (rg_bl G) < length (rg_bl G))%nat).
{ apply nth_error_Some. rewrite (art_bl_idx_nth (rg_bl G) mb ms Hin (art_sec_geo_inj HI t ctx parr (rg_bl G) ISG)). discriminate. }
pose proof (proj1 (Nat2Z.inj_lt _ _) Hidx) as Hidx'.
assert (Hlastin : In (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)) (rg_bl G)) by (apply nth_In; lia).
destruct (GB _ Hlastin) as (_ & _ & Hl0 & Hl1 & Hl2 & _).
pose proof (Z.div_mod mb 8 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound mb 8 ltac:(lia)) as Bm.
pose proof (Z.div_mod ms 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound ms 8 ltac:(lia)) as Bs.
unfold art_cbr_sec_fp, art_secd_fp. cbn [art_gap app fst snd]. unfold SB. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hn0 Hmb0 Hmb1 Hmb2 Hidx' Hl0 Hl1 Hl2 Gp1 Gp2 Dm Bm Ds Bs; unfold apart in *; cbn in *; lia)].
- destruct RG as (Hw0 & Hwsz & Hnf).
unfold art_lcd_fp. cbn [art_gap app fst snd]. repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hn0 Hw0 Hwsz Hnf; unfold apart in *; cbn in *; lia)].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rel_fp_prot := (ltac2:(TCodec.tc2 tcn__JatRecycle5G "R9'4'<':&>r6r5%3221&=r7%211&Dv6&Gr9+Z0%3221%6251&Er:&F+2+Q?%3221%6251z%821A&@vQ2r;r8%4432A1&8&0&;%1276%33Q3Q31&2%13Q5Q53%7431DI%M2;J&C%12GLr<%321?%Q2231%Q32EK&9&AvQ4vQ0vNrAr@r?%776K54321%931=Kp0;1p0=1p0C1p0E1p0N1p0Q41p0Q71p0Q?1p0QG1p0QK1pQJR21pQBR31pR@R41pRBR51pQFR41p<R61pR4R81")) (only parsing).
Variable sp1 : ltac:(sec_ty2 constr:(SEC_T_art_rel_fp_prot) 0%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_rel_fp_prot) 1%nat 0%nat).
Lemma art_rel_fp_prot : ltac:(sec_stmt2 constr:(SEC_T_art_rel_fp_prot) 2%nat 0%nat).
Proof using tp tsd qs GEO sp1 G.
intros e zlo zlen a n RG BG HHI Hsp' Hz PROT AP Ha Hk Hn0.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & _ & Gts & Atk & _ & G13 & G14 & _ & _ & _ & _ & G19 & G20 & G21 & G22).
destruct BG as (ISG & IBK & IPK). pose proof ISG as (Gp1 & Gp2 & Gp3 & Gp4 & Apt & Apc & GB & GD).
destruct e as [c w d b1 n'|mb ms m b1 n'|wb]; cbn [art_rel_geo art_rel_fp art_rel_zone fst snd] in *.
-
destruct RG as (Hc & Hw0 & Hwsz & Hd & Hd16 & Hdsz & Hn' & Hnf).
pose proof (art_class_size_facts c Hc) as (Hsz & _).
set (rs := (n' + 7) / 8 * 8) in *. set (m := spb + c * 2 ^ 32 + 16 * w + d) in *.
assert (Hrs : 0 <= rs /\ rs mod 8 = 0).
{ unfold rs. pose proof (Z.div_mod (n' + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n' + 7) 8 ltac:(lia)) as B. split; [lia|apply Z_mod_mult]. }
destruct Hrs as (Hrs0 & Hrs8).
pose proof (Z.div_mod (m + 16) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (m + 16) 8 ltac:(lia)) as Bq.
pose proof (Z.div_mod rs 8 ltac:(lia)) as Dr. rewrite Hrs8 in Dr.
assert (Em : m = spb + c * 2 ^ 32 + 16 * w + d) by reflexivity.
unfold art_cbr_prim_fp, art_lcd_fp. cbn [art_gap app fst snd]. unfold SB.
destruct PROT as [(c' & Hc' & Z1 & Z2)|(b & Hb & Z1 & Z2)].
+ repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hc Hw0 Hwsz Hd Hdsz Hsz Em; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 AP Hc Hw0 Hwsz Hd Hdsz Hsz Hrs0 Em; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hc Hw0 Hwsz Hd Hdsz Hsz Hrs0 Dq Bq Dr Em; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hc Atk; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hc Hnf; unfold apart in *; cbn in *; lia)].
+ destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & Hbapp & _ & Hbt & _). pose proof (IBK _ Hb) as Hbk. unfold appmem, SB, kHighMemBeg in Hbapp.
repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbk Hc Hw0 Hwsz Hd Hdsz Hsz Hrs0 Em Hnf; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbapp Hc Hw0 Hwsz Hd Hdsz Hsz Hrs0 Dq Bq Dr Em; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbt Hc; unfold apart in *; cbn in *; lia)].
-
pose proof RG as Hin. destruct (GB _ Hin) as (Hmb4k & Hms4k & Hmb0 & Hmb1 & Hmb2 & Hmbapp & Abp & Abt & Abc). cbn [fst snd] in *.
pose proof (IBK _ Hin) as Abk. cbn [fst snd] in Abk. unfold appmem, SB, kHighMemBeg in Hmbapp.
pose proof (art_bl_idx_nth (rg_bl G) mb ms Hin (art_sec_geo_inj HI t ctx parr (rg_bl G) ISG)) as Hnth.
assert (Hidx : (art_bl_idx mb (rg_bl G) < length (rg_bl G))%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
pose proof (proj1 (Nat2Z.inj_lt _ _) Hidx) as Hidx'.
assert (Hlastin : In (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)) (rg_bl G)) by (apply nth_In; lia).
destruct (GB _ Hlastin) as (_ & _ & Hl0 & Hl1 & Hl2 & Hlapp & _ & Hlt & Hlc). pose proof (IBK _ Hlastin) as Hlk.
pose proof (Z.div_mod mb 8 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound mb 8 ltac:(lia)) as Bm.
pose proof (Z.div_mod ms 8 ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound ms 8 ltac:(lia)) as Bs.
unfold art_cbr_sec_fp, art_secd_fp. cbn [art_gap app fst snd]. unfold SB.
destruct PROT as [(c' & Hc' & Z1 & Z2)|(b & Hb & Z1 & Z2)].
+ repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Atk; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 IPK Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hlk Hl0; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hmb0 Hmb1 Hmb2 Dm Bm Ds Bs; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Abk; unfold apart in *; cbn in *; lia)].
+ destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & Hbapp & Hbp & Hbt & _). unfold appmem, SB, kHighMemBeg in Hbapp.
assert (Hlast : fst (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0)) + 32 <= zlo \/ zlo + zlen <= fst (nth (length (rg_bl G) - 1) (rg_bl G) (0, 0))).
{ destruct (In_nth_error _ _ Hb) as (j & Hj).
assert (Hjl : (j < length (rg_bl G))%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
destruct (Nat.eq_dec j (length (rg_bl G) - 1)) as [->|NE].
- rewrite (nth_error_nth _ _ (0, 0) Hj). left. clear - Z1. lia.
- assert (Hll : (length (rg_bl G) - 1 < length (rg_bl G))%nat) by lia.
pose proof (GD j (length (rg_bl G) - 1)%nat b _ Hj (nth_error_nth' (rg_bl G) (0, 0) Hll) NE) as Ap. unfold apart in Ap. clear - Ap Z1 Z2 Hl0 Hs. lia. }
repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbt; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbp Hidx'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hlast; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbapp Hmb0 Hmb1 Hmb2 Dm Bm Ds Bs; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 AP; unfold apart in *; cbn in *; lia)].
-
destruct RG as (Hw0 & Hwsz & Hnf).
unfold art_lcd_fp. cbn [art_gap app fst snd].
destruct PROT as [(c' & Hc' & Z1 & Z2)|(b & Hb & Z1 & Z2)].
+ repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Atk; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Hc' Z1 Z2 Hnf; unfold apart in *; cbn in *; lia)].
+ destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & Hbapp & _ & Hbt & _). pose proof (IBK _ Hb) as Hbk.
repeat split; first [exact I|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1'; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbk Hnf; unfold apart in *; cbn in *; lia)|(clear - G1 G2 Espb G4 Eris G6 G7 G8 G13 G14 G19 G20 G21 G22 HHI Hsp' Ha Hk Hz Z1 Z2 Hs Hb0 Hb1' Hbt; unfold apart in *; cbn in *; lia)].
Qed.
End SE.
End Gap.
