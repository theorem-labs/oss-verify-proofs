(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsX PmSpecsU PmStep PmKeep PmKitU PmFrame PmUOutlinedP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUVecDtor () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmUVecDtor.PMUVD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nat"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0HI"; "0KS"; "0L"; "4bvmap"; "0M"; "0R"]; ["0R'"; "5msteps"; "6opdel_spec"; "6vec_dtor_spec"; "7KSL"; "8FPState"; "8getr"; "8mkst"; "8seg_rom"; "9loaded_segments"; "0SCFG_P"; ":eqb"; ";In"; ";existsb"; ";forallb"; "<add"]; ["<le"; "<mul"; "<of_nat"; "<sub"; "0b"; "0fx"; "0fx'"; "0j"; "0k"; "0l"; "0p"; "0sp"; "=Z_to_bv"; "=bv"; "0x"]]).
Module PMUVD.
Import PMU.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Definition KSL : list nat := [1; 2; 3; 4; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmUVecDtor "J'1'2%211'5'0&N&M&Kr1%211r3%53:21qRB;1%83<15(3%<3;21&L%13@97r2r5%43C21p041pRBE1p081pRDF1pHG1").
Proof. intros KS l.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Section Loop.
Variable M : word -> option byte.
Variables (sp b : Z).
Hypothesis Hsp : 140735332483088 <= sp <= 140737488355328.
Hypothesis Asp : sp mod 16 = 0.
Hypothesis WR : L5.writable RSEGS M (sp - 16) 16.
Hypothesis Hb : 4096 <= b.
Lemma round : ltac2:(TCodec.tc2 tcn__PmUVecDtor "S>'E&=y5'Q=yR0%211%5241'9'5&Fr2&Q<&Q2u2%211%42=1%7261vQ;%72>1%;3>31r3u:%:11%<2E1%?241vQ4%?2F1%C3F31r4u;%B11%D2M1%G241%F2M=%J3M21r5u=%I11%K2Q41%N241+Q0%N2Q51%Q23Q531&Q0&O%12D5%321;r6+TPPPPPPPP0%6221'6'4'2&Lr1&D%33421%Q=1Q?%Q?2QH1%QB2Q71r<%QD213%QF3QI31p071pRN<1'8'A&I&Gr;r:+VfZ<%QM2R41v>&H%118%8576431%95R3G542%<3;21%R62IQ@&Q3r9%221Q:%R82R?1%R<3R?51&7%R>3R?4QM%211%Q5241%Q62;1+VfZL%R@2RG1%H5RBQ61CA%K3JA1%Q;218%N261%Q=2Q01qQ2RK1%Q@2RL1qR>S31%QB2S41p0QD1p0QH1p0QM1p0R61p0R>1p0RG1pRFS41pQ0S61pR<S=1").
Proof. intros fx R p.
intros R2 R10 R11 R13 Hp1 Hp2.
cfeed PL (PMUOP.uvdL_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => b | 35%nat => p | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PL as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & L11).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 sp) by (rewrite (KS1 2%nat) by PMK.inl; exact R2).
assert (R1_10 : getr R1 (reg 10) = Z_to_bv 64 b) by (rewrite (KS1 10%nat) by PMK.inl; exact R10).
cfeed PM (PMUOP.uvdM_conc fx1 R1 M (fun j => match j with 2%nat => sp | 34%nat => b | 35%nat => p - 32 | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PM as (fx2 & R2' & M2 & MG2 & FR2 & _ & EX).
assert (EM : M2 = M) by (apply functional_extensionality; exact FR2). subst M2.
assert (MODE : (p - 32 - b) mod 2 ^ 64 = p - 32 - b) by (apply Z.mod_small; lia).
exists fx2, R2'. destruct EX as [(MS2 & KS2 & F)|(MS2 & KS2 & F)]; rewrite MODE in F.
- split. { intros x Hx. rewrite (KS2 x) by (revert x Hx; apply (sub_in _ KSL); vm_compute; reflexivity). apply KS1. revert x Hx. apply (sub_in _ KSL). vm_compute. reflexivity. }
left. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [rewrite (KS2 11%nat) by PMK.inl; exact L11|].
lia.
- split. { intros x Hx. rewrite (KS2 x) by (revert x Hx; apply (sub_in _ KSL); vm_compute; reflexivity). apply KS1. revert x Hx. apply (sub_in _ KSL). vm_compute. reflexivity. }
right. split; [eapply msteps_trans; [exact MS1| exact MS2]| lia].
Qed.
Lemma loop_ms : ltac2:(TCodec.tc2 tcn__PmUVecDtor "S4'2'E&=y5'Q=yR0%211%5241'5&Fr1&Q<&Q2u2%211%42<1%7261vQ;%72=1%;3=31r2u:%:11%<2D1%?241vQ4%?2E1%C3E31r3u;%B11%D2L1%G241&O&Q1+Q0r5%I11+1%6221%6251%82@1%O2Q51%Q33Q5;1r4u=%Q211%Q42Q<1%Q7241%Q62Q<>%Q:3Q<21&Q0r7%Q911%E21@%E2D1%G2O1+TPPPPPPPP0%7221'6'4'A&I&Gr9r8+VfZ<%QH2QN1v>&H%118%8576431+VfZL%QN2R41%;5QFR0164%>3=41&L&D%23R>R41%R31QK%R52R=1%R82QE1r:%R:213%R<3R>31p071pRNRF1%K2<1qQ2RA1%N2RB1qR>RI1%Q02RJ1p0Q21p0Q;1p0QC1p0R41p0R=1pQ0RJ1pR<S11pR@S31").
Proof. intros j.
induction j as [|j IH]; intros fx R R2 R10 R11 R13 HB.
- destruct (round fx R (b + 32 * (Z.of_nat 0 + 1)) R2 R10 R11 R13 ltac:(lia) HB) as (fx1 & R1 & KS1 & [(MS & _ & X)|(MS & _)]); [exfalso; lia|].
exists fx1, R1. split; [exact MS| exact KS1].
- destruct (round fx R (b + 32 * (Z.of_nat (S j) + 1)) R2 R10 R11 R13 ltac:(lia) HB) as (fx1 & R1 & KS1 & [(MS & L11 & X)|(MS & X)]); [|exfalso; lia].
destruct (IH fx1 R1) as (fx2 & R2' & MS2 & KS2).
+ rewrite (KS1 2%nat) by PMK.inl. exact R2.
+ rewrite (KS1 10%nat) by PMK.inl. exact R10.
+ rewrite L11. f_equal. lia.
+ rewrite (KS1 13%nat) by PMK.inl. exact R13.
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
Theorem vec_dtor_ok : ltac2:(TCodec.tc2 tcn__PmUVecDtor "8&BvJv<v:%43321&C%13543p031").
Proof.
intros OPD. unfold PMU.vec_dtor_spec, PMSX.vec_dtor_spec.
intros fx R M model K LB cr t v b k sp r stk HH MOK K0 ENT A10 T1 T2 TV V1 V2 V3 VD VEC Bv KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
change (PMSP.pm_scr 0) with 12288 in *.
destruct VEC as (C0 & C8 & C16 & Hk & Hlen & Hal & DB & _ & _ & EL).
pose proof (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH (incl_refl _)) as BR.
destruct (BR _ _ Bv) as (Pb0 & Pb1 & Pb4). pose proof (PM.pow2_pos k ltac:(lia)) as P2k.
set (len := Z.of_nat (length stk)) in *. assert (Hlen0 : 0 <= len) by (unfold len; lia).
pose proof (L5C.stk_writable RSEGS _ M sp 12288 STK) as WR.
assert (WR16 : L5.writable RSEGS M (sp - 16) 16) by (apply (L5.writable_sub RSEGS M (sp - 12288) 12288 (sp - 16) 16 WR); lia).
assert (HT : bv_unsigned (getr R (reg 10)) = t) by (rewrite A10; apply L5.unsigned_lit; lia).
pose proof (PMUOP.uvdA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => b | 35%nat => b + 32 * len | _ => 0 end)) as PA. cbn beta iota in PA.
rewrite HT in PA.
PMK.feed PA ltac:(first [PMK.sc]).
destruct PA as (fx1 & R1 & M1 & MG1 & FR1 & _ & EX).
assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
assert (TAILED : exists fxT RT, msteps RSEGS (st fx R 0x35928 M) (st fxT RT 0x3595c M) /\ getr RT (reg 10) = Z_to_bv 64 b /\ getr RT (reg 12) = Z_to_bv 64 v
/\ (forall x, In x [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr RT (reg x) = getr R (reg x))).
{ destruct EX as [(MS & KS & E10 & E11 & E12 & E13 & F)|(MS & KS & E10 & E11 & E12 & F)].
- assert (MODE : (b - (b + 32 * len)) mod 2 ^ 64 = (if Z.eqb len 0 then 0 else 2 ^ 64 - 32 * len)).
{ destruct (Z.eqb_spec len 0) as [->|N]; [replace (b - (b + 32 * 0)) with 0 by lia; reflexivity|].
replace (b - (b + 32 * len)) with (- (32 * len)) by lia. rewrite Z.mod_opp_l_nz; [rewrite Z.mod_small by lia; reflexivity|lia| rewrite Z.mod_small by lia; lia]. }
rewrite MODE in F. destruct (Z.eqb_spec len 0) as [E0|N0]; [exfalso; lia|].
assert (HJ : len = Z.of_nat (Nat.pred (length stk)) + 1) by (unfold len in *; lia).
destruct (loop_ms M sp b ltac:(lia) A16 WR16 Pb0 (Nat.pred (length stk)) fx1 R1) as (fx2 & R2 & MS2 & KS2).
+ rewrite (KS 2%nat) by PMK.inl. exact Rsp.
+ exact E10.
+ rewrite E11. f_equal. lia.
+ exact E13.
+ lia.
+ exists fx2, R2. split; [eapply msteps_trans; [exact MS| exact MS2]|]. split; [rewrite (KS2 10%nat) by PMK.inl; exact E10|].
split; [rewrite (KS2 12%nat) by PMK.inl; exact E12|]. intros x Hx. rewrite (KS2 x); [apply KS|].
* revert x Hx. apply sub_in. vm_compute. reflexivity.
* revert x Hx. apply sub_in. vm_compute. reflexivity.
- exists fx1, R1. split; [exact MS|]. split; [exact E10|]. split; [exact E12|]. intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity. }
clear EX. destruct TAILED as (fxT & RT & MST & T10 & T12 & KST).
unfold PMSP.cfg. cbn [pa_vec_dtor AD].
apply (PMK.spiece_ro RSEGS model fx fxT R 0x35928 RT 0x3595c M K Mh Ml MST).
assert (WRV : L5.writable RSEGS M v 24) by (apply (L5C.writable_of_defined RSEGS M v 24 VD); lia).
pose proof (PMUOP.uvdZ_conc fxT RT M (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => b | 36%nat => b + 32 * 2 ^ k | _ => 0 end)) as PZ. cbn beta iota in PZ.
assert (RT2 : getr RT (reg 2) = Z_to_bv 64 sp) by (rewrite (KST 2%nat) by (cbn; auto 20); exact Rsp).
PMK.feed PZ ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PZ as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & Z11 & CZ8)); PMK.pvz_clrT.
set (P := fun a => v + 8 <= a < v + 8 + 8).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fxT fx3 RT 0x3595c R3 0x55454 M3 P K HH Mh Ml ltac:(lia) MS3 MG3 FRZ3).
{ intros a Pa. unfold P in Pa. left. lia. }
{ intros a. apply PMK.rng_dec. }
intros HH3.
assert (STK3 : L5C.stk (hl_sptop L) M3 sp PMSP.OPDEL_SCR).
{ apply (PMK.stk_call L M3 sp 12288 sp PMSP.OPDEL_SCR (PMK.stk_grows L M M3 sp 12288 MG3 STK)); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16]. }
assert (CH : forall x, In x [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg x) = getr R (reg x)).
{ intros x Hx. rewrite (KS3 x); [apply KST; exact Hx|]. revert x Hx. apply sub_in. vm_compute. reflexivity. }
unfold PMU.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD. cbn [pa_opdel AD] in OPD.
apply (OPD fx3 R3 M3 model K LB cr b (32 * 2 ^ k) sp r HH3 MOK K0 Bv).
{ rewrite L5K.rl10. rewrite (KS3 10%nat) by PMK.inl. exact T10. }
{ rewrite L5K.rl1. rewrite (CH 1%nat) by (cbn; auto 20). exact Rra. }
{ exact RAok. }
{ rewrite L5K.rl2. rewrite (CH 2%nat) by (cbn; auto 20). exact Rsp. }
{ rewrite L5K.rl4. rewrite (CH 4%nat) by (cbn; auto 20). exact Rtp. }
{ exact STK3. }
intros fx4 R4 M4 model4 RP4 HP4 MB4 HH4.
apply (KONT fx4 R4 M4 model4); [| |exact MB4|exact HH4].
- apply (PMK.regs_preserved_trans R R3 R4); [|exact RP4]. apply PMK.preserved_by_index. intros x Hx. apply CH. unfold PMK.cs_all in Hx. cbn in Hx |- *. tauto.
- set (LB' := lb_remove b LB) in *.
assert (INC : incl LB' LB) by (intros x Hx; apply (L5C.in_lb_remove b x LB); exact Hx).
assert (BR' : PMFR.brange L LB') by (apply (PMFR.brange_incl L LB' LB BR INC)).
assert (EK03 : PMK.ek L LB' sp 12288 [(v, 24)] M M3).
{ apply (PMK.ek_piece_in' RSEGS L KL LB' sp 12288 [(v, 24)] M M3 P FRZ3); [lia|lia| exact (PMFR.brange_hi L LB' BR')|].
intros a Pa. right. exists (v, 24). split; [left; reflexivity| unfold L5.in_rng, P in *; cbn [fst snd]; lia]. }
assert (EK34 : PMK.ek L LB' sp 12288 [(v, 24)] M3 M4).
{ apply (PMK.ek_callee_in' RSEGS L KL LB' LB' sp 12288 sp PMSP.OPDEL_SCR [(v, 24)] [] M3 M4 HP4 (incl_refl _)); [unfold PMSP.OPDEL_SCR; lia|lia|lia|lia| exact (PMFR.brange_hi L LB' BR')|].
intros a I. destruct (PMFR.inW_nil a I). }
apply (PMK.hpres_of L LB' sp 12288 [(v, 24)] M M4).
+ apply (PMK.ek_trans L LB' sp 12288 [(v, 24)] M M3 M4 EK03 EK34).
+ assert (STK4 : L5C.stk (hl_sptop L) M4 sp 12288).
{ apply (PMK.stk_after RSEGS L KL LB' M3 M4 sp 12288 sp PMSP.OPDEL_SCR [] (PMK.stk_grows L M M3 sp 12288 MG3 STK) HP4); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia]. }
destruct STK4 as (_ & _ & _ & _ & D4). exact D4.
+ apply (PMK.dk_trans L LB' sp 12288 M M3 M4); [apply PMK.dk_grows; exact MG3|].
apply (PMK.dk_callee L LB' LB' sp 12288 sp PMSP.OPDEL_SCR [] M3 M4 HP4 (incl_refl _)); [unfold PMSP.OPDEL_SCR; lia|lia].
Qed.
End WithHeap.
End PMUVD.
