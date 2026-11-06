(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmSIosDtorP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSIosDtor () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSIosDtor.PMSID."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2eq"; "3Z"; "0HI"; "0K"; "0KS"; "0L"; "4Model"]; ["4event"; "4m_halted"; "4m_vm_lazy"; "5bvmap"; "0M"; "0R"; "0R'"; "0Rk"; "0Rk'"; "6regs_preserved"; "8ra_ok"; "7SCFG"; "9CS0"; "9rinv"; ":cfg"; ";ios_dtor_spec"]; [";locale_dtor_spec"; "<FPState"; "<getr"; "=srealizes"; ">loaded_segments"; "0SCFG_P"; "?eqb"; "@In"; "@existsb"; "@forallb"; "Aof_nat"; "0fx"; "0k"; "0l"; "0model"; "0o"]; ["0r"; "0sp"; "BZ_to_bv"; "Bbv"; "0x"]]).
Module PMSID.
Import PMS.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition CS0 : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition rinv (R Rk : bvmap 5 word) (sp o : Z) : Prop :=
getr Rk (reg 2) = Z_to_bv 64 (sp - 48) /\ getr Rk (reg 8) = Z_to_bv 64 o /\ (forall x, In x CS0 -> getr Rk (reg x) = getr R (reg x)).
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmSIosDtor "J'3'4%211'9'1&Q9&Q8&Q6r1%211r3%53:21qRJ;1%83<15(8%<3;21&Q7%13@97r2r5%43C21p041pRJE1p081pRLF1pLG1").
Proof. intros KS l.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma rinv_pres : ltac2:(TCodec.tc2 tcn__PmSIosDtor "I&Cy5'QCyR0%211%5241':&Mr5r4r2r1%544321&I%1265r7r3%:42981p041p071pS0>1pS4?1pQBA1pQ@B1pQ<C1").
Proof. intros R Rk Rk' sp o.
intros (H2 & H8 & HC) RP. split; [rewrite (PMK.cs_of_preserved Rk Rk' 2 RP ltac:(PMK.inl)); exact H2|].
split; [rewrite (PMK.cs_of_preserved Rk Rk' 8 RP ltac:(PMK.inl)); exact H8|].
intros x Hx. rewrite <- (HC x Hx). apply (PMK.cs_of_preserved Rk Rk' x RP). revert x Hx. apply sub_in. vm_compute. reflexivity.
Qed.
Lemma rinv_ks : ltac2:(TCodec.tc2 tcn__PmSIosDtor "QL&Cy5'QCyR0%211%5241':'3'4%211&Mr6r5r3r2%544321&Q7r1%23:15'9&Q2r7&QB&Q:%11:%32H1%6251r8%8213%:3I31p0<1pS:G1'1&Q9&Q8&Q6%11Cr4%43N21qRJO1(2u2u8&L%43Q421%53Q541%=3Q671(8%M3@21r9%Q841MQ7Q6p031p0E1p0Q61pLQ=1pS0QA1pS4QB1pQBQD1pQ@QE1pQ<QF1").
Proof. intros R Rk Rk' sp o KS.
intros (H2 & H8 & HC) HK SUB. pose proof (sub_in KS _ SUB) as IN.
split; [rewrite (HK 2%nat) by (apply IN; cbn; auto); exact H2|]. split; [rewrite (HK 8%nat) by (apply IN; cbn; auto); exact H8|].
intros x Hx. rewrite (HK x) by (apply IN; right; right; exact Hx). apply HC. exact Hx.
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Lemma free_null_at : ltac2:(TCodec.tc2 tcn__PmSIosDtor "RO'Q1&Cy5'QCyR0%211%5241'6y8%611%311p061'?'3'@%211!pS:21':'9%=1?&Ar3%211(0%11D%73631'7%12GG%@11&Br4%211(5%116%@3631&Q2r7&QB&Q:u:%211%42Q81%7261z%72Q91%K3Q931r8u1%:11%<2Q@1%?241%>2Q@E%Q23Q@21&Jr5%211%H1Q;%E11&Ir<r1%3221'Q3&Q4&KvQ5%211&Nr>r2r9r;%569432=1r:%<4;821p0>1pQ>R71r=+cZ[D%<6@2D186%B4A>1:p051p0I1p0L1p0Q01p0Q81p0QD1p0QN1pS2R71pJR91pRNR?1pQ:RA1pQ<RG1pRHRN1").
Proof. intros fx R M model K r.
intros Mh Ml A10 A1 RA K0 KONT. pose proof (hio_free_null L SCFG HI HIok) as FN. unfold free_null_spec in FN.
rewrite (ly_segs L LY), (ly_free L LY) in FN. unfold PMSP.cfg.
apply (FN fx R M model K Mh Ml); [rewrite <- L5K.rl10 in A10; exact A10| rewrite <- L5K.rl1 in A1; rewrite A1; apply L5K.ret_ok_lit; exact RA| exact K0|].
intros R' RP. rewrite <- L5K.rl1 in A1. rewrite A1. apply KONT. exact RP.
Qed.
Theorem ios_dtor_ok : ltac2:(TCodec.tc2 tcn__PmSIosDtor "8&Q0vQ5v>%3221&Ov;%23541p041").
Proof.
intros LDT. unfold PMS.ios_dtor_spec, PMSP.ios_dtor_spec.
intros fx R M model K LB cr o vp rdb st sp r HH MOK K0 ENT A10 O1 O2 O3 IOS BASE KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
change (PMSP.pm_scr 1) with 14336 in *.
destruct IOS as (I0 & I32 & I36 & I40 & I48 & ZB & ID & _ & ST). change (pa_classic_imp AD) with 0xc6aa0 in I48.
pose proof (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH (incl_refl _)) as BR.
pose proof (L5C.stk_writable RSEGS _ M sp 14336 STK) as WR.
assert (WRO : L5.writable RSEGS M o 8) by (apply (L5C.writable_of_defined RSEGS M o 8); [apply (L5.defined_sub M o 152 o 8 ID); lia|lia|lia]).
assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
pose proof (PMSIDP.idA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => 0xc6aa0 | _ => 0 end)) as P. cbn beta iota in P. rewrite HO in P.
PMK.feed P ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A2 & A8 & A9 & B10 & B11 & C0 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
set (P := fun a => (sp - 40 <= a < sp - 40 + 40) \/ (o + 0 <= a < o + 0 + 8)).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
unfold PMSP.cfg. cbn [pa_ios_dtor AD].
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x5b1b0 R1 0x7f994 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
{ intros a Pa. apply (PMK.cwr_stack L LB M sp 14336 a STK). destruct Pa as [X|X]; lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 14336) by (apply (PMK.stk_grows L M M1 sp 14336 MG STK)).
assert (AG : forall a n, o + 8 <= a -> a + n <= o + 152 -> L5C.agree_on M M1 a n).
{ intros a n X Y i Hi. apply FRZ; [lia|]. intros [Q|Q]; lia. }
assert (I48b : L5.u64_at RSEGS M1 (o + 48) 0xc6aa0) by (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia|lia|lia|exact I48]).
assert (ZB1 : PM.zeros_at M1 (o + 56) 80) by (apply (PMF.zeros_at_agree M M1); [apply AG; lia| exact ZB]).
assert (INV1 : rinv R R1 sp o).
{ split; [exact A2|]. split; [rewrite A8; exact A10|]. intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity. }
pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as Hs0. change (bv_modulus 64) with (2 ^ 64) in Hs0.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as Hs1. change (bv_modulus 64) with (2 ^ 64) in Hs1.
pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as Hs2. change (bv_modulus 64) with (2 ^ 64) in Hs2.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as Hs3. change (bv_modulus 64) with (2 ^ 64) in Hs3.
assert (ES0 : Z_to_bv 64 (bv_unsigned (getr R (reg 8))) = getr R (reg 8)) by (apply Z_to_bv_bv_unsigned).
assert (ES1 : Z_to_bv 64 (bv_unsigned (getr R (reg 9))) = getr R (reg 9)) by (apply Z_to_bv_bv_unsigned).
assert (ES2 : Z_to_bv 64 (bv_unsigned (getr R (reg 18))) = getr R (reg 18)) by (apply Z_to_bv_bv_unsigned).
assert (ES3 : Z_to_bv 64 (bv_unsigned (getr R (reg 19))) = getr R (reg 19)) by (apply Z_to_bv_bv_unsigned).
set (s0v := bv_unsigned (getr R (reg 8))) in *. set (s1v := bv_unsigned (getr R (reg 9))) in *.
set (s2v := bv_unsigned (getr R (reg 18))) in *. set (s3v := bv_unsigned (getr R (reg 19))) in *.
rewrite Rra, L5.unsigned_lit in C8 by lia.
pose proof (L5C.stk_writable RSEGS _ M1 sp 14336 STK1) as WR1.
assert (STKl : L5C.stk (hl_sptop L) M1 (sp - 48) (PMSP.pm_scr 0)).
{ apply (PMK.stk_call L M1 sp 14336 (sp - 48) (PMSP.pm_scr 0) STK1); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMS.locale_dtor_spec, PMSP.locale_dtor_spec in LDT.
apply (LDT fx1 R1 M1 model K (o + 48) (sp - 48) 371848 Mh Ml K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact A2|].
split; [rewrite (KS 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS 4%nat) by PMK.inl; exact Rtp|]. exact STKl. }
{ rewrite L5K.rl10. exact B10. }
{ lia. }
{ lia. }
{ exact I48b. }
intros fx2 R2 RP2. pose proof (rinv_pres R R1 R2 sp o INV1 RP2) as INV2.
pose proof INV2 as (R2_2 & R2_8 & _).
cfeed PB (PMSIDP.idB_conc fx2 R2 M1 (fun j => match j with 2%nat => sp | 40%nat => o | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PB as (fx3 & R3 & M3 & _ & FR3 & _ & MS3 & KS3 & B1 & B10b).
assert (EM : M3 = M1) by (apply functional_extensionality; exact FR3). subst M3.
apply (PMK.spiece_ro RSEGS model fx2 fx3 R2 0x5ac88 R3 0x9a974 M1 K Mh Ml MS3).
apply (free_null_at fx3 R3 M1 model K 371856 Mh Ml B10b B1 ltac:(split; [lia| reflexivity]) K0). intros R4 RP4.
pose proof (rinv_pres R R3 R4 sp o (rinv_ks R R2 R3 sp o _ INV2 KS3 ltac:(vm_compute; reflexivity)) RP4) as INV4. pose proof INV4 as (R4_2 & R4_8 & _).
cfeed PC (PMSIDP.idC_conc fx3 R4 M1 (fun j => match j with 2%nat => sp | 40%nat => o | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PC as (fx5 & R5 & M5 & _ & FR5 & _ & MS5 & KS5 & C1 & C10).
assert (EM : M5 = M1) by (apply functional_extensionality; exact FR5). subst M5.
apply (PMK.spiece_ro RSEGS model fx3 fx5 R4 0x5ac90 R5 0x9a974 M1 K Mh Ml MS5).
apply (free_null_at fx5 R5 M1 model K 371864 Mh Ml C10 C1 ltac:(split; [lia| reflexivity]) K0). intros R6 RP6.
pose proof (rinv_pres R R5 R6 sp o (rinv_ks R R4 R5 sp o _ INV4 KS5 ltac:(vm_compute; reflexivity)) RP6) as INV6. pose proof INV6 as (R6_2 & R6_8 & _).
cfeed PD (PMSIDP.idD_conc fx5 R6 M1 (fun j => match j with 2%nat => sp | 40%nat => o | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PD as (fx7 & R7 & M7 & _ & FR7 & _ & MS7 & KS7 & D1 & D10).
assert (EM : M7 = M1) by (apply functional_extensionality; exact FR7). subst M7.
apply (PMK.spiece_ro RSEGS model fx5 fx7 R6 0x5ac98 R7 0x9a974 M1 K Mh Ml MS7).
apply (free_null_at fx7 R7 M1 model K 371872 Mh Ml D10 D1 ltac:(split; [lia| reflexivity]) K0). intros R8 RP8.
pose proof (rinv_pres R R7 R8 sp o (rinv_ks R R6 R7 sp o _ INV6 KS7 ltac:(vm_compute; reflexivity)) RP8) as INV8. pose proof INV8 as (R8_2 & R8_8 & HC8).
cfeed PE (PMSIDP.idE_conc fx7 R8 M1 (fun j => match j with 2%nat => sp | 36%nat => s2v | 37%nat => s1v | 38%nat => r | 39%nat => s0v | 40%nat => o | 41%nat => s3v | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PE as (fx9 & R9 & M9 & _ & FR9 & _ & MS9 & KS9 & E1 & E2 & E8 & E9 & E10 & E18 & E19).
assert (EM : M9 = M1) by (apply functional_extensionality; exact FR9). subst M9.
apply (PMK.spiece_ro RSEGS model fx7 fx9 R8 0x5aca0 R9 0x9a974 M1 K Mh Ml MS9).
apply (free_null_at fx9 R9 M1 model K r Mh Ml E10 E1 RAok K0). intros R10 RP10.
apply (KONT fx9 R10 M1); [| |exact HH1].
- apply (PMK.regs_preserved_trans R R9 R10); [|exact RP10]. apply PMK.preserved_by_index. intros x Hx. unfold PMK.cs_all in Hx. cbn in Hx.
assert (CH : forall y, In y [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg y) = getr R (reg y)).
{ intros y Hy. rewrite (KS9 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply HC8. revert y Hy. apply sub_in. vm_compute. reflexivity. }
destruct Hx as [<-|Hx]; [rewrite E2, Rsp; reflexivity|].
destruct Hx as [<-|Hx]; [apply CH; cbn; auto|].
destruct Hx as [<-|Hx]; [apply CH; cbn; auto|].
destruct Hx as [<-|Hx]; [rewrite E8; exact ES0|].
destruct Hx as [<-|Hx]; [rewrite E9; exact ES1|].
destruct Hx as [<-|Hx]; [rewrite E18; exact ES2|].
destruct Hx as [<-|Hx]; [rewrite E19; exact ES3|].
apply CH. cbn. tauto.
- apply (PMK.hpres_of L LB sp 14336 [(o, 152)] M M1).
+ apply (PMK.ek_piece_in RSEGS L KL LB sp 14336 [(o, 152)] M M1 P FRZ STK (PMFR.brange_hi L LB BR)).
intros a [X|X]; [left; lia| right; exists (o, 152); split; [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]].
+ destruct STK1 as (_ & _ & _ & _ & D1'). exact D1'.
+ apply PMK.dk_grows. exact MG.
Qed.
End WithHeap.
End PMSID.
