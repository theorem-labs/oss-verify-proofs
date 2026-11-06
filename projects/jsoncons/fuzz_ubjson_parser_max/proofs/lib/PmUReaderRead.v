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
Ltac2 tcn__PmUReaderRead () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "Stdlib.ZArith.BinInt.Z."], [["1list"; "1prod"; "2eq"; "3Z"; "0HI"; "0L"; "4inv"; "4p_tb"; "4p_tg"; "4parser_own"; "4pst"; "4tb_ok"; "5pst_reset"; "6parse_spec"; "6reader_read_spec"; "6reset_spec"]; ["0SCFG_P"; "7modulo"; "0s"; "0x"]]).
Module PMURR.
Import PMU.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Lemma m16_8 : ltac2:(TCodec.tc2 tcn__PmUReaderRead ">'3'2&Ar1+@%3221z%63721r2+8%8221%:3;15p051pQ8=1").
Proof. intros x. intros H. apply Z.mod_divide in H; [|lia]. destruct H as (q & ->). replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia. Qed.
Lemma own_reset : ltac2:(TCodec.tc2 tcn__PmUReaderRead "?':'2'0'1'3%2211%411&9&<r1%211%411%513%<3721pQ6>1").
Proof. intros s. destruct s as [m d dp src tb tg b k stk]. unfold PM.parser_own, PMSP.pst_reset. cbn. destruct tb; reflexivity. Qed.
Lemma tb_ok_reset : ltac2:(TCodec.tc2 tcn__PmUReaderRead "@':&;&7r1%211&8%113%6231&<r2%211%911%712%<221p071pQ6?1").
Proof. intros s. destruct s as [m d dp src tb tg b k stk]. cbn. destruct tb; intros H; exact H. Qed.
Lemma inv_reset : ltac2:(TCodec.tc2 tcn__PmUReaderRead "?':&;&7r1%211&8%113%6231&6&<r2%211%411p061pQ6>1").
Proof. intros s.
intros TB. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|apply tb_ok_reset; exact TB].
unfold PM.stack_shape. cbn [PMSP.pst_reset PM.p_stk length nth]. split; [lia|]. split; [unfold PM.MAX_DEPTH; lia|]. split; [left; reflexivity|].
split; [intros i Hi; lia|]. intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [nth]. unfold PM.pstate_ok, PM.ps_root. cbn. split; [lia|]. right. right. split; [left; reflexivity| split; reflexivity].
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Theorem reader_read_ok : ltac2:(TCodec.tc2 tcn__PmUReaderRead ";&?v@v5v4%43321&=%13543&>%13765p031p061").
Proof.
intros RST PARSE. unfold PMU.reader_read_spec, PMSX.reader_read_spec.
intros fx R M model K LBX cr sp r fb cat s str sm e HH MOK K0 ENT FOK A10 A11 RPRE INCS LEN EC UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame AD] in F2.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
destruct RPRE as (PA & IA & VV & VR & BASE & ERR & TBOK).
unfold PMSP.o_p, PMSP.o_ec, PMSP.o_is, PMSP.o_v in *. cbn [pa_off_p pa_off_ec pa_off_is pa_off_v AD] in *.
change (PMSP.pm_scr 11) with 34816 in *.
assert (SC0 : 0 <= 34816) by lia.
set (LBc := PM.parser_own s ++ LBX) in *.
assert (BRc : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok LBc LBc cr M _ HH); apply incl_refl).
assert (BRx : PMFR.brange L LBX) by (apply (PMFR.brange_incl L LBX LBc BRc); unfold LBc; apply incl_appr; apply incl_refl).
pose proof (L5C.stk_writable RSEGS _ M sp 34816 STK) as WR.
cfeed P (PMUOP.urrA_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A2 & A8 & A9 & C24 & C16 & C8)); PMK.pvz_clrT.
set (P := fun a => sp - 24 <= a < sp - 24 + 24).
assert (PF : forall a, P a -> sp - 34816 <= a < sp) by (intros a X; unfold P in X; lia).
unfold PMSP.cfg. cbn [pa_reader_read AD].
apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34664 R1 0x36408 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
{ intros a Pa. apply (PMK.cwr_stack L LBc M sp 34816 a STK). apply PF in Pa. lia. }
{ intros a. apply PMK.rng_dec. }
intros HH1.
assert (STK1 : L5C.stk (hl_sptop L) M1 sp 34816) by (apply (PMK.stk_grows L M M1 sp 34816 MG STK)).
assert (EK01c : PMK.ek L LBc sp 34816 [] M M1) by (apply (PMFR.ek_of_piece RSEGS L KL LBc sp 34816 M M1 P FRZ STK (PMFR.brange_hi L LBc BRc) PF)).
assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (PA1 : PM.parser_at RSEGS AD PMSP.T3 PMSP.T4 M1 (fb + 40) (fb + 440) s).
{ apply (PMFR.parser_keep RSEGS AD L KL LBc sp 34816 [] M M1 EK01c STK SC0 BRc WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| unfold LBc; apply incl_appl; apply incl_refl| exact PA]. }
assert (SC1 : 0 <= PMSP.pm_scr 1) by (unfold PMSP.pm_scr; lia).
assert (STKr : L5C.stk (hl_sptop L) M1 (sp - 32) (PMSP.pm_scr 1)).
{ apply (PMK.stk_call L M1 sp 34816 (sp - 32) (PMSP.pm_scr 1) STK1); [lia| unfold PMSP.pm_scr; lia| exact SC1|].
replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.reset_spec, PMSP.reset_spec in RST.
apply (RST fx1 R1 M1 model K LBX cr (sp - 32) 214656 fb s HH1 MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact A2|].
split; [rewrite (KS 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS 4%nat) by PMK.inl; exact Rtp|]. exact STKr. }
{ unfold PMSP.frame_ok. cbn [pa_frame AD]. split; [lia|]. split; [lia| exact F3]. }
{ rewrite L5K.rl10. unfold PMSP.o_p. cbn [pa_off_p AD]. rewrite (KS 10%nat) by PMK.inl. exact A10. }
{ unfold PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD]. exact PA1. }
{ exact LEN. }
intros fx2 R2 M2 RP2 PA2 HP2 HH2.
unfold PMSP.o_p, PMSP.o_is, PMSP.o_tb, PMSP.o_vec in PA2, HP2. cbn [pa_off_p pa_off_is AD] in PA2, HP2.
set (W4 := [(fb + 40 + 8, 8); (fb + 40 + 336, 24); (fb + 40 + 360, 24)] : list L5.range) in *.
assert (WC4 : forall a, PMK.inW W4 a -> fb + 48 <= a < fb + 424).
{ intros a (r0 & Hin & Hr). unfold W4 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hr; lia. }
assert (WHI4 : forall a, PMK.inW W4 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC4 in I; left; lia).
assert (EK01 : PMK.ek L LBX sp 34816 W4 M M1).
{ apply (PMK.ek_piece_in RSEGS L KL LBX sp 34816 W4 M M1 P FRZ STK (PMFR.brange_hi L LBX BRx)). intros a Pa. left. apply PF. exact Pa. }
assert (EK12 : PMK.ek L LBX sp 34816 W4 M1 M2).
{ apply (PMK.ek_callee_in' RSEGS L KL LBX LBX sp 34816 (sp - 32) (PMSP.pm_scr 1) W4 W4 M1 M2 HP2 (incl_refl _)); [unfold PMSP.pm_scr; lia|lia|lia|lia| exact (PMFR.brange_hi L LBX BRx)|].
intros a I. right. exact I. }
assert (EK02 : PMK.ek L LBX sp 34816 W4 M M2) by (apply (PMK.ek_trans L LBX sp 34816 W4 M M1 M2 EK01 EK12)).
assert (STK2 : L5C.stk (hl_sptop L) M2 sp 34816).
{ apply (PMK.stk_after RSEGS L KL LBX M1 M2 sp 34816 (sp - 32) (PMSP.pm_scr 1) W4 STK1 HP2); [lia| unfold PMSP.pm_scr; lia| exact SC1]. }
assert (IA2 : PM.iss_at RSEGS AD PMSP.T3 M2 (fb + 440) str sm).
{ apply (PMFR.iss_keep RSEGS AD L KL LBX sp 34816 W4 M M2 EK02 STK SC0 BRx WHI4); [lia|lia| intros i Hi I; apply WC4 in I; lia| exact INCS| exact IA]. }
assert (VV2 : PMSP.visitor_at RSEGS AD M2 (fb + 432)).
{ apply (PMFR.visitor_keep RSEGS AD L KL LBX sp 34816 W4 M M2 EK02 STK SC0); [lia|lia| intros i Hi I; apply WC4 in I; lia| exact VV]. }
assert (VR2 : L5.u64_at RSEGS M2 (fb + 40 + 384) (fb + 432)).
{ apply (PMFR.u64_keep RSEGS L KL LBX sp 34816 W4 M M2 EK02 STK SC0); [lia|lia| intros i Hi I; apply WC4 in I; lia| exact VR]. }
assert (EC2 : PMSP.ec_at RSEGS M2 (fb + 8) 0 cat).
{ apply (PMFR.ec_keep RSEGS L KL LBX sp 34816 W4 M M2 EK02 STK SC0); [lia|lia| intros i Hi I; apply WC4 in I; lia| exact EC]. }
assert (OUT4 : forall a, a < sp -> L5.outside W4 a) by (intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WC4 in I; lia).
assert (BASE2 : PMST.base_ok RSEGS AD M2).
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LBX sp 34816 W4 M M2 EK02); first [exact BASE | intros a Ha; apply OUT4; cbn in Ha; lia]. }
assert (ERR2 : PMST.err_ok RSEGS AD M2 e).
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LBX sp 34816 W4 M M2 EK02); first [exact ERR | intros a Ha; apply OUT4; cbn in Ha; lia]. }
assert (EKr : PMK.ek L LBX (sp - 32) (PMSP.pm_scr 1) W4 M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (WHIr : forall a, PMK.inW W4 a -> sp - 32 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC4 in I; left; lia).
pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as Hs0. change (bv_modulus 64) with (2 ^ 64) in Hs0.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as Hs1. change (bv_modulus 64) with (2 ^ 64) in Hs1.
assert (ES0 : Z_to_bv 64 (bv_unsigned (getr R (reg 8))) = getr R (reg 8)) by (apply Z_to_bv_bv_unsigned).
assert (ES1 : Z_to_bv 64 (bv_unsigned (getr R (reg 9))) = getr R (reg 9)) by (apply Z_to_bv_bv_unsigned).
set (s0v := bv_unsigned (getr R (reg 8))) in *. set (s1v := bv_unsigned (getr R (reg 9))) in *.
rewrite Rra, L5.unsigned_lit in C8 by lia.
assert (C8b : L5.u64_at RSEGS M2 (sp - 8) r).
{ apply (PMFR.u64_keep RSEGS L KL LBX (sp - 32) (PMSP.pm_scr 1) W4 M1 M2 EKr STKr SC1); [lia|lia| intros i Hi I; apply WC4 in I; lia| exact C8]. }
assert (C16b : L5.u64_at RSEGS M2 (sp - 16) s0v).
{ apply (PMFR.u64_keep RSEGS L KL LBX (sp - 32) (PMSP.pm_scr 1) W4 M1 M2 EKr STKr SC1); [lia|lia| intros i Hi I; apply WC4 in I; lia| exact C16]. }
assert (C24b : L5.u64_at RSEGS M2 (sp - 24) s1v).
{ apply (PMFR.u64_keep RSEGS L KL LBX (sp - 32) (PMSP.pm_scr 1) W4 M1 M2 EKr STKr SC1); [lia|lia| intros i Hi I; apply WC4 in I; lia| exact C24]. }
pose proof (L5C.stk_writable RSEGS _ M2 sp 34816 STK2) as WR2.
assert (R2sp : getr R2 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (PMK.cs_of_preserved R1 R2 2 RP2 ltac:(PMK.inl)); exact A2).
assert (R2s0 : getr R2 (reg 8) = Z_to_bv 64 (fb + 8)) by (rewrite (PMK.cs_of_preserved R1 R2 8 RP2 ltac:(PMK.inl)); rewrite A8; exact A11).
assert (R2s1 : getr R2 (reg 9) = Z_to_bv 64 (fb + 40)) by (rewrite (PMK.cs_of_preserved R1 R2 9 RP2 ltac:(PMK.inl)); rewrite A9; exact A10).
assert (AL432 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 54 * 8) by lia; rewrite Z.mod_add by lia; apply m16_8; exact F3).
cfeed PB (PMUOP.urrB_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 37%nat => s1v | 38%nat => r | 39%nat => s0v | 40%nat => fb + 8 | 41%nat => fb + 40 | 42%nat => fb + 432 | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PB as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & B1 & B2 & B8 & B9 & B10 & B11 & B12)); PMK.pvz_clrT.
assert (EM : M3 = M2) by (apply functional_extensionality; exact FR3). subst M3.
apply (PMK.spiece_ro RSEGS model fx2 fx3 R2 0x34680 R3 0x36574 M2 K Mh Ml MS3).
assert (SC10 : 0 <= PMSP.pm_scr 10) by (unfold PMSP.pm_scr; lia).
assert (STKp : L5C.stk (hl_sptop L) M2 sp (PMSP.pm_scr 10)).
{ apply (PMK.stk_call L M2 sp 34816 sp (PMSP.pm_scr 10) STK2); [lia| unfold PMSP.pm_scr; lia| exact SC10| exact A16]. }
assert (CH : forall k, In k PMUOP.KS_urrA -> In k PMUOP.KS_urrB -> In k PMK.cs_all -> getr R3 (reg k) = getr R (reg k)).
{ intros k K1 K2 K3. rewrite (KS3 k K2). rewrite (PMK.cs_of_preserved R1 R2 k RP2 K3). apply KS. exact K1. }
unfold PMU.parse_spec, PMSP.parse_spec in PARSE. rewrite <- (own_reset s) in HH2.
apply (PARSE fx3 R3 M2 model K LBX cr sp r fb cat (PMSP.pst_reset s) str sm e HH2 MOK K0).
- unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact B1|]. split; [exact RAok|]. split; [exact B2|].
split; [rewrite (CH 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (CH 4%nat) by PMK.inl; exact Rtp|]. exact STKp.
- unfold PMSP.frame_ok. cbn [pa_frame AD]. split; [exact F1|]. split; [exact F2| exact F3].
- unfold PMSP.args3, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD]. rewrite L5K.rl10, L5K.rl11, L5K.rl12.
split; [exact B10|]. split; [exact B11| exact B12].
- unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD].
split; [exact PA2|]. split; [exact IA2|]. split; [exact VV2|]. split; [exact VR2|]. split; [exact BASE2|]. split; [exact ERR2|]. apply tb_ok_reset. exact TBOK.
- exact INCS.
- apply inv_reset. exact TBOK.
- unfold PMSP.o_ec. cbn [pa_off_ec AD]. exact EC2.
- destruct s; exact UNR.
- exact CRED.
- intros fx4 R4 M4 model4 s' sm' e' cr' RP4 PPOST HP4 CK4 MB4 HH4.
apply (KONT fx4 R4 M4 model4 s' sm' e' cr'); [|exact PPOST| |exact CK4|exact MB4|exact HH4].
+ apply (PMK.regs_preserved_trans R R3 R4); [|exact RP4]. apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
destruct Hk as [<-|Hk]; [rewrite B2, Rsp; reflexivity|].
destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
destruct Hk as [<-|Hk]; [rewrite B8; exact ES0|].
destruct Hk as [<-|Hk]; [rewrite B9; exact ES1|].
repeat (destruct Hk as [<-|Hk]; [apply CH; PMK.inl|]). destruct Hk.
+ set (WR4 := PMSP.W_run AD fb) in *.
assert (SUB : forall a, L5.outside WR4 a -> L5.outside W4 a).
{ intros a O r0 Hin. apply O. unfold WR4, PMSP.W_run, PMSP.W_srcf, PMSP.o_p, PMSP.o_tb, PMSP.o_vec. cbn [pa_off_p AD app]. unfold W4 in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; cbn; auto 8. }
assert (EK02r : PMK.ek L LBX sp 34816 WR4 M M2).
{ apply (PMK.ek_weaken L LBX LBX sp 34816 sp 34816 WR4 W4 M M2 EK02 (incl_refl _)); [intros x Hx; exact Hx| exact SUB]. }
assert (EK24 : PMK.ek L LBX sp 34816 WR4 M2 M4).
{ apply (PMK.ek_callee_in' RSEGS L KL LBX LBX sp 34816 sp (PMSP.pm_scr 10) WR4 WR4 M2 M4 HP4 (incl_refl _)); [unfold PMSP.pm_scr; lia|lia|lia|lia| exact (PMFR.brange_hi L LBX BRx)|].
intros a I. right. exact I. }
assert (STK4 : L5C.stk (hl_sptop L) M4 sp 34816).
{ apply (PMK.stk_after RSEGS L KL LBX M2 M4 sp 34816 sp (PMSP.pm_scr 10) WR4 STK2 HP4); [lia| unfold PMSP.pm_scr; lia| exact SC10]. }
apply (PMK.hpres_of L LBX sp 34816 WR4 M M4).
* apply (PMK.ek_trans L LBX sp 34816 WR4 M M2 M4 EK02r EK24).
* destruct STK4 as (_ & _ & _ & _ & D4). exact D4.
* apply (PMK.dk_trans L LBX sp 34816 M M1 M4); [apply PMK.dk_grows; exact MG|].
apply (PMK.dk_trans L LBX sp 34816 M1 M2 M4).
-- apply (PMK.dk_callee L LBX LBX sp 34816 (sp - 32) (PMSP.pm_scr 1) W4 M1 M2 HP2 (incl_refl _)); [unfold PMSP.pm_scr; lia|lia].
-- apply (PMK.dk_callee L LBX LBX sp 34816 sp (PMSP.pm_scr 10) WR4 M2 M4 HP4 (incl_refl _)); [unfold PMSP.pm_scr; lia|lia].
Qed.
End WithHeap.
End PMURR.
