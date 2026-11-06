(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmSReset PmUResetP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUReset () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmUReset.PMURS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0HI"; "0L"; "4bvmap"; "0M"; "0R"; "0R'"; "5msteps"; "6reset_spec"; "7KSL"]; ["8FPState"; "8getr"; "8mkst"; "8seg_rom"; "9loaded_segments"; "0SCFG_P"; ":In"; ";add"; ";le"; ";mul"; ";of_nat"; ";sub"; "0b"; "0fx"; "0fx'"; "0j"]; ["0p"; "0sq"; "<Z_to_bv"; "<bv"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMURS.
Import PMU.
Local Ltac lia := PMK.alia.
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Definition KSL : list nat := [1; 2; 3; 4; 8; 9; 10; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Section Loop.
Variable M : word -> option byte.
Variables (sq b : Z).
Hypothesis Hsq : 140735332483136 <= sq <= 140737488355328.
Hypothesis Asq : sq mod 16 = 0.
Hypothesis WR : L5.writable RSEGS M (sq - 64) 64.
Hypothesis Hb : 4096 <= b.
Lemma round : ltac2:(TCodec.tc2 tcn__PmUReset "S>'@&9y5'Q3yR0%211%5241'6'2&Ar2&Q2&Ju2%211%42=1%7261vQ1%72>1%;3>31r3u:%:11%<2E1%?241vL%?2F1%C3F31r4u;%B11%D2M1%G241%F2M=%J3M21r5u<%I11%K2Q41%N241+Q0%N2Q51%Q23Q531&H&G%12D5%321;r6+TPPPPPPPP0%6221'3'1'0&Fr1&?%33421%Q=1Q?%Q?2QH1%QB2Q71r<%QD213%QF3QI31p071pR:<1'5'=&D&Br;r:+ViRH%QM2R41v:&C%118%8576431%95R3G542%<3;21%R62IQ@&Kr9%221Q:%R82R?1%R<3R?51&4%R>3R?4QM%211%Q5241%Q62;1+ViS8%R@2RG1%H5RBQ61CA%K3JA1%Q;218%N261%Q=2Q01qJRK1%Q@2RL1qQNS31%QB2S41p0QD1p0QH1p0QM1p0R61p0R>1p0RG1pR2S41pHS61pQLS=1").
Proof. intros fx R p.
intros R2 R10 R11 R12 Hp1 Hp2.
cfeed PL (PMURSP.urLp_conc fx R M (fun j => match j with 2%nat => sq | 34%nat => b | 35%nat => p | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PL as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & L11).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 sq) by (rewrite (KS1 2%nat) by PMK.inl; exact R2).
assert (R1_10 : getr R1 (reg 10) = Z_to_bv 64 b) by (rewrite (KS1 10%nat) by PMK.inl; exact R10).
cfeed PM (PMURSP.urM_conc fx1 R1 M (fun j => match j with 2%nat => sq | 34%nat => b | 35%nat => p - 32 | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PM as (fx2 & R2' & M2 & MG2 & FR2 & _ & EX).
assert (EM : M2 = M) by (apply functional_extensionality; exact FR2). subst M2.
assert (MODE : (p - 32 - b) mod 2 ^ 64 = p - 32 - b) by (apply Z.mod_small; lia).
exists fx2, R2'. destruct EX as [(MS2 & KS2 & F)|(MS2 & KS2 & F)]; rewrite MODE in F.
- split. { intros x Hx. rewrite (KS2 x) by (revert x Hx; apply (PMSRS.sub_in _ KSL); vm_compute; reflexivity). apply KS1. revert x Hx. apply (PMSRS.sub_in _ KSL). vm_compute. reflexivity. }
left. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [rewrite (KS2 11%nat) by PMK.inl; exact L11|]. lia.
- split. { intros x Hx. rewrite (KS2 x) by (revert x Hx; apply (PMSRS.sub_in _ KSL); vm_compute; reflexivity). apply KS1. revert x Hx. apply (PMSRS.sub_in _ KSL). vm_compute. reflexivity. }
right. split; [eapply msteps_trans; [exact MS1| exact MS2]| lia].
Qed.
Lemma loop_ms : ltac2:(TCodec.tc2 tcn__PmUReset "S4'0'@&9y5'Q3yR0%211%5241'2&Ar1&Q2&Ju2%211%42<1%7261vQ1%72=1%;3=31r2u:%:11%<2D1%?241vL%?2E1%C3E31r3u;%B11%D2L1%G241&G&I+Q0r5%I11+1%6221%6251%82@1%O2Q51%Q33Q5;1r4u<%Q211%Q42Q<1%Q7241%Q62Q<>%Q:3Q<21&Hr7%Q911%E21@%E2D1%G2O1+TPPPPPPPP0%7221'3'1'=&D&Br9r8+ViRH%QH2QN1v:&C%118%8576431+ViS8%QN2R41%;5QFR0164%>3=41&F&?%23R>R41%R31QK%R52R=1%R82QE1r:%R:213%R<3R>31p071pR:RF1%K2<1qJRA1%N2RB1qQNRI1%Q02RJ1p0Q21p0Q;1p0QC1p0R41p0R=1pHRJ1pQLS11pR0S31").
Proof. intros j.
induction j as [|j IH]; intros fx R R2 R10 R11 R12 HB.
- destruct (round fx R (b + 32 * (Z.of_nat 0 + 1)) R2 R10 R11 R12 ltac:(lia) HB) as (fx1 & R1 & KS1 & [(MS & _ & X)|(MS & _)]); [exfalso; lia|].
exists fx1, R1. split; [exact MS| exact KS1].
- destruct (round fx R (b + 32 * (Z.of_nat (S j) + 1)) R2 R10 R11 R12 ltac:(lia) HB) as (fx1 & R1 & KS1 & [(MS & L11 & X)|(MS & X)]); [|exfalso; lia].
destruct (IH fx1 R1) as (fx2 & R2' & MS2 & KS2).
+ rewrite (KS1 2%nat) by PMK.inl. exact R2.
+ rewrite (KS1 10%nat) by PMK.inl. exact R10.
+ rewrite L11. f_equal. lia.
+ rewrite (KS1 12%nat) by PMK.inl. exact R12.
+ lia.
+ exists fx2, R2'. split; [eapply msteps_trans; [exact MS| exact MS2]|]. intros x Hx. rewrite (KS2 x Hx). apply KS1. exact Hx.
Qed.
End Loop.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Theorem reset_ok : ltac2:(TCodec.tc2 tcn__PmUReset "5&>vEv8v7%43321").
Proof.
unfold PMU.reset_spec, PMSP.reset_spec.
intros fx R M model K LBX cr sp r fb s HH MOK K0 ENT FR A10 PA LEN KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
change (PMSP.pm_scr 1) with 14336 in *.
destruct FR as (Fsp & Ftop & Fal). change (pa_frame AD) with 752 in Ftop.
set (op := PMSP.o_p AD fb) in *. assert (Eop : op = fb + 40) by reflexivity.
set (ois := PMSP.o_is AD fb) in *.
assert (HO : bv_unsigned (getr R (reg 10)) = op) by (rewrite A10; apply L5.unsigned_lit; lia).
assert (INO : incl (PM.parser_own s) (PM.parser_own s ++ LBX)) by (intros x Hx; apply in_or_app; left; exact Hx).
pose proof (PMFR.brange_of_heap L HI HIok _ _ cr M _ HH INO) as BR.
assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s)) by (unfold PM.parser_own; left; reflexivity).
assert (Ib : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s)) by (unfold PM.parser_own; right; left; reflexivity).
destruct (BR _ _ Iq) as (Q0 & Q1 & Q4). destruct (BR _ _ Ib) as (Pb0 & Pb1 & Pb4).
pose proof (PMSRS.heap_nodup L HI HIok _ _ _ _ HH) as ND.
destruct (PMSRS.own_nodup s LBX ND) as (Nqb & Ntb).
pose proof (PMSRS.blocks_apart_heap L HI HIok _ _ _ _ _ _ _ _ HH (INO _ Iq) (INO _ Ib) Nqb) as Aqb.
pose proof PA as (P0 & PD & _ & P8 & P9 & P12 & P16 & P20 & PNI & PSRC & P320 & P328 & _ & PTB & PVEC & PB1 & PB2 & PB3).
pose proof PVEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
set (src := PM.p_src s) in *. set (b := PM.p_b s) in *. set (k := PM.p_k s) in *.
pose proof (PM.pow2_pos k ltac:(lia)) as P2k.
assert (P2kh : 2 ^ k <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia). change (2 ^ 11) with 2048 in P2kh.
assert (Cb : forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> ~ (b <= i < b + 32)) by (intros i Hi X; destruct Aqb; lia).
set (len := Z.of_nat (length (PM.p_stk s))) in *. assert (Hlen1 : 1 <= len) by (unfold len; lia).
assert (Hlen32 : 32 <= 32 * len <= 65536) by (clear - Hlen1 Hlen P2kh; lia). assert (Hlenk : 32 * len <= 32 * 2 ^ k) by (clear - Hlen; lia).
pose proof (L5C.stk_writable RSEGS _ M sp 14336 STK) as WR.
assert (WRop : L5.writable RSEGS M op 384) by (apply (L5C.writable_of_defined RSEGS M op 384 PD); lia).
assert (WRb : L5.writable RSEGS M b 32) by (apply (L5C.writable_of_defined RSEGS M b 32); [apply (L5.defined_sub M b (32 * 2 ^ k) b 32 DB); lia|lia|lia]).
assert (BRX : PMFR.brange L LBX) by (apply (PMFR.brange_of_heap L HI HIok _ LBX cr M _ HH); intros x Hx; apply in_or_app; right; exact Hx).
pose proof (ly_img_hi L LY) as Himg.
assert (HSP : 0x7fff80000000 <= hl_sptop L) by (destruct STOP as [STOP1 _]; exact STOP1).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as Hs1. change (bv_modulus 64) with (2 ^ 64) in Hs1.
pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as Hs8. change (bv_modulus 64) with (2 ^ 64) in Hs8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as Hs9. change (bv_modulus 64) with (2 ^ 64) in Hs9.
destruct (PM.p_tb s) as [n|c n p] eqn:TB.
-
destruct PTB as (TD & _ & Hn & T0).
pose proof (PMF.even_byte n) as EVB.
pose proof (PMURSP.urS_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => 2 * n | 34%nat => b | 36%nat => 32 * len | _ => 0 end)) as PP.
cbn beta iota in PP. rewrite HO in PP.
PMK.feed PP ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG1 & _ & FRZ1a & MS1 & KS1 & R1_2 & R1_8 & R1_10 & R1_11 & R1_12 & (C336 & _) & (C8 & C9) & S24 & S16 & S8)); PMK.pvz_clrT.
set (P1 := fun a => (sp - 24 <= a < sp - 24 + 24) \/ (op + 8 <= a < op + 8 + 8) \/ (op + 336 <= a < op + 336 + 2)).
assert (FRZ1 : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ1a; [exact Ha|intro X; apply N; unfold P1; lia|intro X; apply N; unfold P1; lia|intro X; apply N; unfold P1; lia]. }
unfold PMSP.cfg. cbn [pa_reset AD].
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M model fx fx1 R 0x36408 R1 0x36458 M1 P1 K HH Mh Ml HSP MS1 MG1 FRZ1).
{ intros a Pa. unfold P1 in Pa. destruct Pa as [X|[X|X]]; apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M sp 14336 a STK); lia. }
{ intros a. unfold P1. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
pose proof (PMK.stk_grows L M M1 sp 14336 MG1 STK) as STK1.
pose proof (L5C.stk_writable RSEGS _ M1 sp 14336 STK1) as WR1.
assert (WRq : L5.writable RSEGS M1 (sp - 64 - 64) 64).
{ apply (L5.writable_sub RSEGS M1 (sp - 14336) 14336); [apply (L5C.stk_writable RSEGS _ M1 sp 14336 STK1)|lia|lia]. }
destruct (loop_ms M1 (sp - 64) b ltac:(lia) ltac:(lia) WRq ltac:(lia) (Z.to_nat (len - 1)) fx1 R1 R1_2 R1_10) as (fxL & RL & MSL & KSLr).
{ rewrite R1_11. f_equal. rewrite Z2Nat.id by lia. lia. }
{ exact R1_12. }
{ rewrite Z2Nat.id by lia. lia. }
apply (PMK.spiece_ro RSEGS model fx1 fxL R1 0x36458 RL 0x36468 M1 K Mh Ml MSL).
assert (RL2 : getr RL (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (KSLr 2%nat) by PMK.inl; exact R1_2).
assert (RL8 : getr RL (reg 8) = Z_to_bv 64 op) by (rewrite (KSLr 8%nat) by PMK.inl; rewrite R1_8, A10; reflexivity).
assert (RL10 : getr RL (reg 10) = Z_to_bv 64 b) by (rewrite (KSLr 10%nat) by PMK.inl; exact R1_10).
assert (AG1 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P1 i) -> L5C.agree_on M M1 a n).
{ intros a0 n0 Ha0 Hn0 X i Hi. apply FRZ1; [lia| apply X; exact Hi]. }
assert (V16' : L5.u64_at RSEGS M1 (op + 376) (b + 32 * 2 ^ k)).
{ apply (L5C.u64_at_agree RSEGS M M1); [apply AG1; [lia|lia| intros i Hi X; unfold P1 in X; destruct X as [X|[X|X]]; cdisj; lia]|lia|lia|].
replace (op + 376) with (op + 360 + 16) by lia. exact V16. }
assert (WRop1 : L5.writable RSEGS M1 op 384) by (apply (L5C.writable_of_defined RSEGS M1 op 384); [intros i Hi; apply MG1; apply PD; exact Hi|lia|lia]).
assert (WRb1 : L5.writable RSEGS M1 b 32) by (apply (L5C.writable_of_defined RSEGS M1 b 32); [intros i Hi; apply MG1; apply DB; lia|lia|lia]).
cfeed PZ (PMURSP.urZ_conc fxL RL M1 (fun j => match j with 2%nat => sp | 10%nat => op | 34%nat => b | 35%nat => 32 * 2 ^ k
| 38%nat => bv_unsigned (getr R (reg 1)) | 39%nat => bv_unsigned (getr R (reg 8)) | 40%nat => bv_unsigned (getr R (reg 9)) | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PZ as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG2 & _ & FRZ2a & MS2 & KS2 & R2_1 & R2_2 & R2_8 & R2_9 & _ & _ & C12 & C368 & E24 & E16 & E8 & E0)); PMK.pvz_clrT.
set (P2 := fun a => (op + 12 <= a < op + 12 + 4) \/ (op + 368 <= a < op + 368 + 8) \/ (b <= a < b + 32)).
assert (FRZ2 : forall a, 0 <= a < 2 ^ 64 -> ~ P2 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ2a; [exact Ha|intro X; apply N; unfold P2; lia|intro X; apply N; unfold P2; lia|intro X; apply N; unfold P2; lia]. }
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M1 model fxL fx2 RL 0x36468 R2 0x36558 M2 P2 K HH1 Mh Ml HSP MS2 MG2 FRZ2).
{ intros a Pa. unfold P2 in Pa. destruct Pa as [X|[X|X]];
[apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M sp 14336 a STK); lia ..
|apply (PMK.cwr_block L (PM.parser_own s ++ LBX) b (32 * 2 ^ k) a (INO _ Ib)); lia]. }
{ intros a. unfold P2. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH2.
assert (RA2 : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite R2_1, Z_to_bv_bv_unsigned; exact Rra).
unfold PMK.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx2 R2 M2 0x36558 (ltac:(oW' 0x36558%Z)) r (ltac:(oF' 0x36558%Z)) ltac:(reflexivity) (ltac:(oD' 0x36558%Z)) RA2 Hr1 Hr2)|].
assert (AG2 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P2 i) -> L5C.agree_on M1 M2 a n).
{ intros a0 n0 Ha0 Hn0 X i Hi. apply FRZ2; [lia| apply X; exact Hi]. }
set (P := fun a => P1 a \/ P2 a).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. rewrite FRZ2 by (exact Ha || (intro X; apply N; right; exact X)). apply FRZ1; [exact Ha| intro X; apply N; left; exact X]. }
assert (MG : mem_grows M M2) by (intros x Dx; apply MG2; apply MG1; exact Dx).
apply (KONT fx2 R2 M2); [| | |exact HH2].
+ apply PMK.preserved_by_index. intros x Hx. unfold PMK.cs_all in Hx. cbn in Hx.
assert (CH : forall y, In y [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg y) = getr R (reg y)).
{ intros y Hy. rewrite (KS2 y) by (revert y Hy; apply PMSRS.sub_in; vm_compute; reflexivity).
rewrite (KSLr y) by (revert y Hy; apply PMSRS.sub_in; vm_compute; reflexivity). apply KS1. revert y Hy. apply PMSRS.sub_in. vm_compute. reflexivity. }
destruct Hx as [<-|Hx]; [rewrite R2_2, Rsp; reflexivity|].
destruct Hx as [<-|Hx]; [apply CH; cbn; auto|].
destruct Hx as [<-|Hx]; [apply CH; cbn; auto|].
destruct Hx as [<-|Hx]; [rewrite R2_8; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite R2_9; apply Z_to_bv_bv_unsigned|].
apply CH. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn; auto 20.
+ apply (PMSRS.reset_post RSEGS AD M M2 op ois s P PA LEN).
all: try change (PM.p_src s) with src; try change (PM.p_b s) with b.
1-4: lia. 1: exact FRZ. 1: exact MG.
* intros i Hi X. unfold P, P1, P2 in X. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]]; [destruct X as [[X|[X|X]]|[X|[X|X]]]; cdisj; lia ..|].
destruct X as [[X|[X|X]]|[X|[X|X]]]; [cdisj; lia|cdisj; lia|cdisj; lia|cdisj; lia|cdisj; lia| exact (Cb i Hi X)].
* apply (L5C.u8_at_agree RSEGS M1 M2); [apply AG2; [lia|lia| intros i Hi X; unfold P2 in X; destruct X as [X|[X|X]]; cdisj; lia]|lia|lia|exact C8].
* apply (L5C.u8_at_agree RSEGS M1 M2); [apply AG2; [lia|lia| intros i Hi X; unfold P2 in X; destruct X as [X|[X|X]]; cdisj; lia]|lia|lia|exact C9].
* exact C12. * exact C368. * exact E0. * exact E8. * exact E16. * exact E24.
* unfold PMSP.pst_reset. cbn [PM.p_tb]. rewrite TB. split; [intros i Hi; apply MG; apply TD; exact Hi|]. split; [exact I|].
split; [lia|]. apply (L5C.u8_at_agree RSEGS M1 M2); [apply AG2; [lia|lia| intros i Hi X; unfold P2 in X; destruct X as [X|[X|X]]; cdisj; lia]|lia|lia|exact C336].
+ change (PMSP.o_tb AD fb) with (op + 336). change (PMSP.o_vec AD fb) with (op + 360).
apply (PMK.hpres_of L LBX sp 14336 _ M M2).
* apply (PMK.ek_trans L LBX sp 14336 _ M M1 M2).
-- apply (PMK.ek_piece L LBX sp 14336 _ M M1 P1 FRZ1). intros a Ha CA NE OW Pa. unfold P1 in Pa. destruct Pa as [X|[X|X]].
++ destruct CA as [((bb & mm) & Hbb & Hr)|[[S1 S2]|[IM _]]]; [destruct (BRX bb mm Hbb) as (_ & _ & Y); cbn [fst snd] in Hr; lia| lia| lia].
++ apply (OW (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
++ apply (OW (op + 336, 24)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
-- apply (PMK.ek_piece L LBX sp 14336 _ M1 M2 P2 FRZ2). intros a Ha CA NE OW Pa. unfold P2 in Pa. destruct Pa as [X|[X|X]].
++ apply (OW (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
++ apply (OW (op + 360, 24)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
++ exact (PMSRS.own_not_client L HI HIok (PM.parser_own s) LBX cr M _ b (32 * 2 ^ k) a sp 14336 HH Ib ltac:(lia) CA).
* destruct (PMK.stk_grows L M M2 sp 14336 MG STK) as (_ & _ & _ & _ & D2). exact D2.
* apply PMK.dk_grows. exact MG.
-
destruct PTB as (TD & _ & T0 & T8 & T16 & Hnc & Hc & Hce & TDp & _).
assert (Ip : In (p, c) (PM.parser_own s)) by (unfold PM.parser_own; rewrite TB; right; right; left; reflexivity).
destruct (BR _ _ Ip) as (Pp0 & Pp1 & Pp4). destruct (Ntb c n p eq_refl) as (Nqp & Nbp).
pose proof (PMSRS.blocks_apart_heap L HI HIok _ _ _ _ _ _ _ _ HH (INO _ Iq) (INO _ Ip) Nqp) as Aqp.
assert (Cp : forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> ~ (p <= i < p + 1)) by (intros i Hi X; destruct Aqp; lia).
pose proof (PMSRS.blocks_apart_heap L HI HIok _ _ _ _ _ _ _ _ HH (INO _ Ib) (INO _ Ip) Nbp) as Abp.
assert (Cbp : forall i, p <= i < p + 1 -> ~ (b <= i < b + 32)) by (intros i Hi X; destruct Abp; lia).
pose proof (PMF.u8_of_u64 RSEGS M (op + 336) (c + 1) ltac:(lia) T0) as T0b.
pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
assert (Dpf : (sp - 64) + 64 <= p \/ p + 1 <= sp - 64) by (right; lia).
assert (Dpo : p + 1 <= op \/ op + 384 <= p) by (left; lia).
assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
assert (WRp : L5.writable RSEGS M p 1) by (apply (L5C.writable_of_defined RSEGS M p 1); [apply (L5.defined_sub M p c p 1 TDp); lia|lia|lia]).
pose proof (PMURSP.urL_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => (c + 1) mod 256 | 34%nat => b | 36%nat => 32 * len
| 37%nat => p | _ => 0 end)) as PP.
cbn beta iota in PP. rewrite HO in PP.
PMK.feed PP ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG1 & _ & FRZ1a & MS1 & KS1 & R1_2 & R1_8 & R1_10 & R1_11 & R1_12 & C344 & Cp0 & (C8 & C9) & S24 & S16 & S8)); PMK.pvz_clrT.
set (P1 := fun a => (sp - 24 <= a < sp - 24 + 24) \/ (op + 8 <= a < op + 8 + 8) \/ (op + 344 <= a < op + 344 + 8) \/ (p <= a < p + 1)).
assert (FRZ1 : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ1a; [exact Ha|intro X; apply N; unfold P1; lia|intro X; apply N; unfold P1; lia|intro X; apply N; unfold P1; lia
|intro X; apply N; unfold P1; lia]. }
unfold PMSP.cfg. cbn [pa_reset AD].
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M model fx fx1 R 0x36408 R1 0x36458 M1 P1 K HH Mh Ml HSP MS1 MG1 FRZ1).
{ intros a Pa. unfold P1 in Pa. destruct Pa as [X|[X|[X|X]]];
[apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M sp 14336 a STK); lia ..
|apply (PMK.cwr_block L (PM.parser_own s ++ LBX) p c a (INO _ Ip)); lia]. }
{ intros a. unfold P1. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
pose proof (PMK.stk_grows L M M1 sp 14336 MG1 STK) as STK1.
pose proof (L5C.stk_writable RSEGS _ M1 sp 14336 STK1) as WR1.
assert (WRq : L5.writable RSEGS M1 (sp - 64 - 64) 64).
{ apply (L5.writable_sub RSEGS M1 (sp - 14336) 14336); [apply (L5C.stk_writable RSEGS _ M1 sp 14336 STK1)|lia|lia]. }
destruct (loop_ms M1 (sp - 64) b ltac:(lia) ltac:(lia) WRq ltac:(lia) (Z.to_nat (len - 1)) fx1 R1 R1_2 R1_10) as (fxL & RL & MSL & KSLr).
{ rewrite R1_11. f_equal. rewrite Z2Nat.id by lia. lia. }
{ exact R1_12. }
{ rewrite Z2Nat.id by lia. lia. }
apply (PMK.spiece_ro RSEGS model fx1 fxL R1 0x36458 RL 0x36468 M1 K Mh Ml MSL).
assert (RL2 : getr RL (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (KSLr 2%nat) by PMK.inl; exact R1_2).
assert (RL8 : getr RL (reg 8) = Z_to_bv 64 op) by (rewrite (KSLr 8%nat) by PMK.inl; rewrite R1_8, A10; reflexivity).
assert (RL10 : getr RL (reg 10) = Z_to_bv 64 b) by (rewrite (KSLr 10%nat) by PMK.inl; exact R1_10).
assert (AG1 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P1 i) -> L5C.agree_on M M1 a n).
{ intros a0 n0 Ha0 Hn0 X i Hi. apply FRZ1; [lia| apply X; exact Hi]. }
assert (V16' : L5.u64_at RSEGS M1 (op + 376) (b + 32 * 2 ^ k)).
{ apply (L5C.u64_at_agree RSEGS M M1); [apply AG1; [lia|lia| intros i Hi X; unfold P1 in X; destruct X as [X|[X|[X|X]]]; cdisj; lia]|lia|lia|].
replace (op + 376) with (op + 360 + 16) by lia. exact V16. }
assert (WRop1 : L5.writable RSEGS M1 op 384) by (apply (L5C.writable_of_defined RSEGS M1 op 384); [intros i Hi; apply MG1; apply PD; exact Hi|lia|lia]).
assert (WRb1 : L5.writable RSEGS M1 b 32) by (apply (L5C.writable_of_defined RSEGS M1 b 32); [intros i Hi; apply MG1; apply DB; lia|lia|lia]).
cfeed PZ (PMURSP.urZ_conc fxL RL M1 (fun j => match j with 2%nat => sp | 10%nat => op | 34%nat => b | 35%nat => 32 * 2 ^ k
| 38%nat => bv_unsigned (getr R (reg 1)) | 39%nat => bv_unsigned (getr R (reg 8)) | 40%nat => bv_unsigned (getr R (reg 9)) | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PZ as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG2 & _ & FRZ2a & MS2 & KS2 & R2_1 & R2_2 & R2_8 & R2_9 & _ & _ & C12 & C368 & E24 & E16 & E8 & E0)); PMK.pvz_clrT.
set (P2 := fun a => (op + 12 <= a < op + 12 + 4) \/ (op + 368 <= a < op + 368 + 8) \/ (b <= a < b + 32)).
assert (FRZ2 : forall a, 0 <= a < 2 ^ 64 -> ~ P2 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ2a; [exact Ha|intro X; apply N; unfold P2; lia|intro X; apply N; unfold P2; lia|intro X; apply N; unfold P2; lia]. }
apply (PMK.spiece RSEGS L HI KL HIok (PM.parser_own s ++ LBX) cr M1 model fxL fx2 RL 0x36468 R2 0x36558 M2 P2 K HH1 Mh Ml HSP MS2 MG2 FRZ2).
{ intros a Pa. unfold P2 in Pa. destruct Pa as [X|[X|X]];
[apply (PMK.cwr_stack L (PM.parser_own s ++ LBX) M sp 14336 a STK); lia ..
|apply (PMK.cwr_block L (PM.parser_own s ++ LBX) b (32 * 2 ^ k) a (INO _ Ib)); lia]. }
{ intros a. unfold P2. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH2.
assert (RA2 : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite R2_1, Z_to_bv_bv_unsigned; exact Rra).
unfold PMK.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx2 R2 M2 0x36558 (ltac:(oW' 0x36558%Z)) r (ltac:(oF' 0x36558%Z)) ltac:(reflexivity) (ltac:(oD' 0x36558%Z)) RA2 Hr1 Hr2)|].
assert (AG2 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P2 i) -> L5C.agree_on M1 M2 a n).
{ intros a0 n0 Ha0 Hn0 X i Hi. apply FRZ2; [lia| apply X; exact Hi]. }
set (P := fun a => P1 a \/ P2 a).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. rewrite FRZ2 by (exact Ha || (intro X; apply N; right; exact X)). apply FRZ1; [exact Ha| intro X; apply N; left; exact X]. }
assert (MG : mem_grows M M2) by (intros x Dx; apply MG2; apply MG1; exact Dx).
apply (KONT fx2 R2 M2); [| | |exact HH2].
+ apply PMK.preserved_by_index. intros x Hx. unfold PMK.cs_all in Hx. cbn in Hx.
assert (CH : forall y, In y [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg y) = getr R (reg y)).
{ intros y Hy. rewrite (KS2 y) by (revert y Hy; apply PMSRS.sub_in; vm_compute; reflexivity).
rewrite (KSLr y) by (revert y Hy; apply PMSRS.sub_in; vm_compute; reflexivity). apply KS1. revert y Hy. apply PMSRS.sub_in. vm_compute. reflexivity. }
destruct Hx as [<-|Hx]; [rewrite R2_2, Rsp; reflexivity|].
destruct Hx as [<-|Hx]; [apply CH; cbn; auto|].
destruct Hx as [<-|Hx]; [apply CH; cbn; auto|].
destruct Hx as [<-|Hx]; [rewrite R2_8; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite R2_9; apply Z_to_bv_bv_unsigned|].
apply CH. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn; auto 20.
+ apply (PMSRS.reset_post RSEGS AD M M2 op ois s P PA LEN).
all: try change (PM.p_src s) with src; try change (PM.p_b s) with b.
1-4: lia. 1: exact FRZ. 1: exact MG.
* intros i Hi X. unfold P, P1, P2 in X. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]]; [destruct X as [[X|[X|[X|X]]]|[X|[X|X]]]; cdisj; lia ..|].
destruct X as [[X|[X|[X|X]]]|[X|[X|X]]]; [cdisj; lia|cdisj; lia|cdisj; lia| exact (Cp i Hi X)|cdisj; lia|cdisj; lia| exact (Cb i Hi X)].
* apply (L5C.u8_at_agree RSEGS M1 M2); [apply AG2; [lia|lia| intros i Hi X; unfold P2 in X; destruct X as [X|[X|X]]; cdisj; lia]|lia|lia|exact C8].
* apply (L5C.u8_at_agree RSEGS M1 M2); [apply AG2; [lia|lia| intros i Hi X; unfold P2 in X; destruct X as [X|[X|X]]; cdisj; lia]|lia|lia|exact C9].
* exact C12. * exact C368. * exact E0. * exact E8. * exact E16. * exact E24.
* unfold PMSP.pst_reset. cbn [PM.p_tb]. rewrite TB. split; [intros i Hi; apply MG; apply TD; exact Hi|]. split; [exact I|].
assert (AGt : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M2 a n).
{ intros a0 n0 Ha0 Hn0 X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
split; [apply (L5C.u64_at_agree RSEGS M M2); [apply AGt; [lia|lia| intros i Hi X; unfold P, P1, P2 in X; destruct X as [[X|[X|[X|X]]]|[X|[X|X]]]; cdisj; lia]|lia|lia|exact T0]|].
split; [replace (op + 336 + 8) with (op + 344) by lia;
apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG2; [lia|lia| intros i Hi X; unfold P2 in X; destruct X as [X|[X|X]]; cdisj; lia]|lia|lia|exact C344]|].
split; [apply (L5C.u64_at_agree RSEGS M M2); [apply AGt; [lia|lia| intros i Hi X; unfold P, P1, P2 in X; destruct X as [[X|[X|[X|X]]]|[X|[X|X]]]; cdisj; lia]|lia|lia|exact T16]|].
split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MG; apply TDp; exact Hi| exact I].
+ change (PMSP.o_tb AD fb) with (op + 336). change (PMSP.o_vec AD fb) with (op + 360).
apply (PMK.hpres_of L LBX sp 14336 _ M M2).
* apply (PMK.ek_trans L LBX sp 14336 _ M M1 M2).
-- apply (PMK.ek_piece L LBX sp 14336 _ M M1 P1 FRZ1). intros a Ha CA NE OW Pa. unfold P1 in Pa. destruct Pa as [X|[X|[X|X]]].
++ destruct CA as [((bb & mm) & Hbb & Hr)|[[S1 S2]|[IM _]]]; [destruct (BRX bb mm Hbb) as (_ & _ & Y); cbn [fst snd] in Hr; lia| lia| lia].
++ apply (OW (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
++ apply (OW (op + 336, 24)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
++ exact (PMSRS.own_not_client L HI HIok (PM.parser_own s) LBX cr M _ p c a sp 14336 HH Ip ltac:(lia) CA).
-- apply (PMK.ek_piece L LBX sp 14336 _ M1 M2 P2 FRZ2). intros a Ha CA NE OW Pa. unfold P2 in Pa. destruct Pa as [X|[X|X]].
++ apply (OW (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
++ apply (OW (op + 360, 24)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
++ exact (PMSRS.own_not_client L HI HIok (PM.parser_own s) LBX cr M _ b (32 * 2 ^ k) a sp 14336 HH Ib ltac:(lia) CA).
* destruct (PMK.stk_grows L M M2 sp 14336 MG STK) as (_ & _ & _ & _ & D2). exact D2.
* apply PMK.dk_grows. exact MG.
Qed.
End WithHeap.
End PMURS.
