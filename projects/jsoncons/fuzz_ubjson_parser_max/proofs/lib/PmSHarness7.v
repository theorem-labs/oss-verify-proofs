(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmTopS PmSHarnessStmts PmSHarnessKit PmSHarnessP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSHarness7 () := ([""; "Corelib.Init.Datatypes."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSHarness7.PMH7.Stage."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSHarnessStmts.PMH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nil"; "1option"; "0HI"; "0K"; "0L"; "0LB0"; "2Model"; "2event"; "3bvmap"; "0M"; "0M0"; "0M1"; "0R"; "0R0"]; ["0R1"; "4credit"; "5SCFG"; "6srcst"; "6strm"; "6vstr"; "7H6b"; "8H6"; "8H7"; "9cfg"; ":opdel_spec"; ":src_dtor_spec"; ";FPState"; "<srealizes"; "=loaded_segments"; "0SCFG_P"]; ["0be"; "0cr"; "0cr0"; "0fx"; "0fx1"; "0g"; "0model"; "0model0"; "0model1"; "0n"; "0ra"; "0s"; "0s2"; "0sm"; "0sp"; "0src"]; [">bv"; "0tb"; "0x"]]).
Module PMH7.
Import PMS. Import PMH.
Local Ltac lia := PMK.alia.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ra n : Z).
Variable LB0 : list (Z * Z).
Variable cr0 : credit.
Variable g : PMST.st.
Hypothesis Hn : 0 <= n < 2 ^ 26.
Hypothesis Hcr0 : PMSP.credit_le (512, 2 ^ 29 + 8 * n) cr0.
Hypothesis Hgp : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Htp : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Definition H6b (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s s2 : PM.vstr) (src : PM.srcst) (sm : PM.strm) (be : bool) : Prop :=
PMH.hcore L R0 M0 model0 sp ra LB0 R M model /\ PMHK.vstr_at M (PMH.fb sp + 712) s /\ PM.vs_size s = n
/\ PMHK.iss_at M (PMH.fb sp + 440) s2 sm
/\ PM.src_fields_at RSEGS PMH.T3 M (PMH.fb sp + 64) (PMH.fb sp + 440) (PMH.fb sp + 456) src /\ PM.nullis_at RSEGS AD PMH.T3 M (PMH.fb sp + 72)
/\ PMH.hstat M true true be /\ (PMST.st_err g = true -> be = true)
/\ hi_heap HI (PM.src_own src ++ PM.vs_own s2 ++ PM.vs_own s ++ LB0) cr M (m_vmmaps model)
/\ PMSP.credit_keep cr0 cr (PMH.P0 L n) PMSP.cr0
/\ getr R (reg 1) = Z_to_bv 64 213304 /\ getr R (reg 10) = Z_to_bv 64 (sp - 688).
Lemma text_gone : ltac2:(TCodec.tc2 tcn__PmSHarness7 "RK&JvOv6v4%43321'L&:y5'Q@yR0%211%5241'3y8%611%311p061'8&A'E'C'D'0'1'9%211!pS621&Gv?v<vQ7vQ>vQ:vQ9v7vQ2vQ5r;r:r9r8r7r6r5r4r3r2%DEQ>Q=CBA@?>=<;:987654321(2%11J%411&Fr1r>r=r<%59;:4321BA@'M&N&B%11QL&I+Vcn<%265DC1BA%74641Hp091pRBQB1pLQD1pQ2QJ1pR:R11r?+V`XD%;6>2C1BA%@4?=1Mp051p0I1p0M1p<QC1pR2QI1pRLQK1pS0QM1pS4QO1pRJR01pRHR11pR4R31pR>R51pHR71pNR=1pR8RD1p0RF1").
Proof using All.
intros OPD fx R M model cr s s2 tb src sm be K (CORE & VS & SZ & IA & TB & SRC & NI & HST & EMONO & HH & CK) K0 KONT.
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (A16f & SLO & SHI & STOP & _).
pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
unfold PMH.fb, FRAME in TB.
destruct tb as [nt | c nt p].
-
destruct TB as (TBD & _ & (Hnt & TB0)).
pose proof (PMF.even_byte nt) as EVB.
cfeed P (PMSHP.hnHs_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => 2 * nt | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A10)); PMK.pvz_clrT.
assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x34114 R1 0x34fcc M K Mh Ml MS).
apply (KONT fx1 R1 M model). unfold H6b.
split. { apply (PMHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M (fun _ => False) CORE MG); [intros a Ha _; reflexivity| intros a []| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
intros k Hk. apply KS. revert k Hk. apply PMH.CSK_in. vm_compute. reflexivity. }
cbn [PM.vs_own app] in HH.
do 9 (split; [assumption|]). split; [exact A1| exact A10].
-
destruct TB as (TBD & _ & (TW0 & TW8 & TW16 & Hnt & Hc & Hc2 & TBP & _)).
set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
set (LBc := PM.src_own src ++ PM.vs_own (PM.VLong c nt p) ++ LBX) in *.
set (LB7 := PM.src_own src ++ LBX).
assert (Bt : In (p, c) LBc) by (unfold LBc, PM.src_own, PM.vs_own; cbn; auto).
assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by lia.
pose proof (PMF.u8_of_u64 RSEGS M _ _ Hc64 TW0) as TB0.
pose proof (PMF.odd_byte c Hc2 ltac:(lia)) as ODB.
pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)) as HVB.
set (vb := (c + 1) mod 256) in *.
assert (BRc : PMHK.brange L LBc) by (apply (PMHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
destruct (BRc _ _ Bt) as (Pb0 & Pb1 & Pb4).
assert (Hp47 : p < 2 ^ 47) by lia.
cfeed P (PMSHP.hnHl_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => vb | 37%nat => p | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A10)); PMK.pvz_clrT.
assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x34114 R1 0x54400 M K Mh Ml MS).
assert (CORE1 : PMH.hcore L R0 M0 model0 sp ra LB0 R1 M model).
{ apply (PMHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M (fun _ => False) CORE MG); [intros a Ha _; reflexivity| intros a []| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
intros k Hk. apply KS. revert k Hk. apply PMH.CSK_in. vm_compute. reflexivity. }
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
pose proof CORE1 as (_ & Hcs1 & _).
assert (STKd : L5C.stk (hl_sptop L) M (sp - 752) PMSP.OPDEL_SCR).
{ apply (PMK.stk_call L M (sp - 752) (65536 - 752) (sp - 752) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16f]. }
unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD.
apply (OPD fx1 R1 M model K LBc cr p c (sp - 752) 213296 HH).
{ repeat split; assumption. }
{ exact K0. }
{ exact Bt. }
{ rewrite L5K.rl10. exact A10. }
{ rewrite L5K.rl1. exact A1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. exact Rsp1. }
{ rewrite L5K.rl4. rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto). exact Htp. }
{ exact STKd. }
intros fx2 R2 M2 model2 RP HP MB HH2.
assert (ELB : lb_remove p LBc = LB7).
{ pose proof (proj1 (proj2 (hio_wf L SCFG HI HIok LBc cr M _ HH))) as ND.
unfold LBc, LB7, PM.src_own, PM.vs_own in *. cbn [app map fst] in *.
cbn [lb_remove fst]. inversion ND as [|x0 l0 NI0 ND0].
destruct (Z.eqb (PM.sr_qc src) p) eqn:EQ; [apply Z.eqb_eq in EQ; exfalso; apply NI0; rewrite EQ; constructor|].
rewrite Z.eqb_refl. reflexivity. }
rewrite ELB in HP, HH2.
assert (EKd : PMK.ek L LB7 (sp - 752) PMSP.OPDEL_SCR [] M M2) by (apply (PMK.ek_of_hpres L); exact HP).
assert (SCd : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
assert (BR7 : PMHK.brange L LB7) by (apply (PMHK.brange_of_heap L HI LY HIok LB7 LB7 cr M2 _ HH2); apply incl_refl).
assert (WSTD : forall a, PMK.inW [] a -> PMH.fb sp <= a \/ 65536 <= a < 954368) by (intros a (r & [] & _)).
assert (N0 : forall a, ~ PMK.inW [] a) by (intros a (r & [] & _)).
assert (CORE2 : PMH.hcore L R0 M0 model0 sp ra LB0 R2 M2 model2).
{ apply (PMHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M model R2 M2 model2 LB7 PMSP.OPDEL_SCR [] CORE1 RP HP);
[unfold LB7, LBX; apply incl_appr; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.OPDEL_SCR, SCR, FRAME; lia| |exact MB].
intros a I. destruct (N0 a I). }
assert (VS2 : PMHK.vstr_at M2 (PMH.fb sp + 712) s).
{ eapply (PMHK.vstr_keep L LY sp LB7 PMSP.OPDEL_SCR [] M M2 EKd STKd SCd BR7 WSTD); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact VS].
- intros i _. apply N0.
- unfold LB7, LBX. apply incl_appr. apply incl_appr. apply incl_appl. apply incl_refl. }
assert (IA2 : PMHK.iss_at M2 (PMH.fb sp + 440) s2 sm).
{ eapply (PMHK.iss_keep L LY sp LB7 PMSP.OPDEL_SCR [] M M2 EKd STKd SCd BR7 WSTD); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact IA].
- intros i _. apply N0.
- unfold LB7, LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
assert (SRC2 : PM.src_fields_at RSEGS PMH.T3 M2 (PMH.fb sp + 64) (PMH.fb sp + 440) (PMH.fb sp + 456) src).
{ eapply (PMHK.src_keep L LY sp LB7 PMSP.OPDEL_SCR [] M M2 EKd STKd SCd BR7 WSTD); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact SRC].
- intros i _. apply N0.
- unfold LB7, PM.src_own. cbn. auto. }
assert (NI2 : PM.nullis_at RSEGS AD PMH.T3 M2 (PMH.fb sp + 72)).
{ eapply (PMHK.nullis_keep L LY sp LB7 PMSP.OPDEL_SCR [] M M2 EKd STKd SCd); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| |exact NI]. intros i _. apply N0. }
assert (HST2 : PMH.hstat M2 true true be).
{ apply (PMHK.hstat_keep L LY LB7 (sp - 752) PMSP.OPDEL_SCR [] M M2 EKd); [|exact HST]. intros a I. destruct (N0 a I). }
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R2 M2 model2 CORE2) as (_ & Rsp2 & _ & _ & WR2 & _).
pose proof CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Mh2 & Ml2 & Mm2)).
cfeed PI (PMSHP.hnI_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PI as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & A1i & A10i)); PMK.pvz_clrT.
assert (EM : M3 = M2) by (apply functional_extensionality; exact FR3). subst M3.
apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x34130 R3 0x34fcc M2 K Mh2 Ml2 MS3).
apply (KONT fx3 R3 M2 model2). unfold H6b.
split. { apply (PMHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R2 M2 model2 R3 M2 (fun _ => False) CORE2 MG3); [intros a Ha _; reflexivity| intros a []| rewrite (KS3 2%nat) by PMK.inl; exact Rsp2|].
intros k Hk. apply KS3. revert k Hk. apply PMH.CSK_in. vm_compute. reflexivity. }
fold LBX. fold LB7.
do 9 (split; [assumption|]). split; [exact A1i| exact A10i].
Qed.
Lemma stage7 : ltac2:(TCodec.tc2 tcn__PmSHarness7 "RN&JvOv6v4%43321&K%13543'L&:y5'Q@yR0%211%5241'3y8%611%311p061'8&A'E'C'D'0'1'9%211!pS621&Gv?v<vQ7vQ>vQ:vQ9v7vQ2vQ5r;r:r9r8r7r6r5r4r3r2%DEQ@Q?CBA@?>=<;:987654321(2%11J%411&Hr1r>r=r<%5CQIQHLKJIHGFED;:4321A@'M&N&B%11QN&I+V`YH%265DC1BA%74641Hp091pRBQB1pLQD1pQ2QJ1pR:R11r?+V`XD%;6>2C1BA%@4?=1Mp051p0I1p0M1p<QC1pR2QI1pRLQK1pS0QM1pS4QO1pRJR01pRHR11pR4R31pR>R51pHR71pNR=1pR8RD1p0RF1p0RI1").
Proof using All.
intros OPD SDT fx R M model cr s s2 tb src sm be K H6 K0 KONT.
apply (text_gone OPD fx R M model cr s s2 tb src sm be K H6 K0).
clear fx R M model H6. intros fx R M model (CORE & VS & SZ & IA & SRC & NI & HST & EMONO & HH & CK & A1 & A10).
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (A16f & SLO & SHI & STOP & _).
pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & MOK).
set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
set (LBc := PM.src_own src ++ LBX) in *.
assert (Bq : In (PM.sr_qc src, PM.CHUNK) LBc) by (unfold LBc, PM.src_own; cbn; auto).
assert (SC2 : 0 <= PMSP.pm_scr 2) by (unfold PMSP.pm_scr; lia).
assert (STKc : L5C.stk (hl_sptop L) M (sp - 752) (PMSP.pm_scr 2)).
{ apply (PMK.stk_call L M (sp - 752) (65536 - 752) (sp - 752) (PMSP.pm_scr 2) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
unfold PMH.fb, FRAME in SRC, NI.
unfold PMS.src_dtor_spec, PMSP.src_dtor_spec in SDT.
apply (SDT fx R M model K LBc cr (sp - 752 + 64) (sp - 752 + 440) (sp - 752 + 456) (sp - 752) 213304 src HH MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp|].
split; [rewrite (Hcs 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc. }
{ rewrite L5K.rl10. rewrite A10. f_equal. lia. }
{ lia. }
{ lia. }
{ replace (sp - 752 + 64) with (sp - 752 + 8 * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_divide in A16f; [|lia]. destruct A16f as (q & ->). replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia. }
{ exact SRC. }
{ replace (sp - 752 + 64 + 8) with (sp - 752 + 72) by lia. exact NI. }
{ exact Bq. }
{ exact BASE. }
intros fx2 R2 M2 model2 RP HP MB HH2.
assert (ELB : lb_remove (PM.sr_qc src) LBc = LBX).
{ unfold LBc, PM.src_own. cbn [app lb_remove fst]. rewrite Z.eqb_refl. reflexivity. }
rewrite ELB in HP, HH2.
set (W2 := [(sp - 752 + 64, 296)] : list L5.range) in *.
assert (WC2 : forall a, PMK.inW W2 a -> sp - 752 + 64 <= a < sp - 752 + 360).
{ intros a (r & Hin & Hr). destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (EK2 : PMK.ek L LBX (sp - 752) (PMSP.pm_scr 2) W2 M M2) by (apply (PMK.ek_of_hpres L); exact HP).
assert (BRX : PMHK.brange L LBX) by (apply (PMHK.brange_of_heap L HI LY HIok LBX LBX cr M2 _ HH2); apply incl_refl).
assert (WSTD : forall a, PMK.inW W2 a -> PMH.fb sp <= a \/ 65536 <= a < 954368) by (intros a I; apply WC2 in I; left; unfold PMH.fb, FRAME; lia).
apply (KONT fx2 R2 M2 model2). unfold PMH.H7.
split. { apply (PMHK.hcore_call L LY R0 M0 model0 sp ra LB0 R M model R2 M2 model2 LBX (PMSP.pm_scr 2) W2 CORE RP HP);
[unfold LBX; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
intros a I. left. apply WC2 in I. unfold PMH.fb, FRAME. lia. }
split. { eapply (PMHK.vstr_keep L LY sp LBX (PMSP.pm_scr 2) W2 M M2 EK2 STKc SC2 BRX WSTD); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact VS].
- intros i Hi I. apply WC2 in I. unfold PMH.fb, FRAME in Hi. lia.
- unfold LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
split; [exact SZ|].
split. { eapply (PMHK.iss_keep L LY sp LBX (PMSP.pm_scr 2) W2 M M2 EK2 STKc SC2 BRX WSTD); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact IA].
- intros i Hi I. apply WC2 in I. unfold PMH.fb, FRAME in Hi. lia.
- unfold LBX. apply incl_appl. apply incl_refl. }
split. { apply (PMHK.hstat_keep L LY LBX (sp - 752) (PMSP.pm_scr 2) W2 M M2 EK2); [|exact HST]. intros a I. apply WC2 in I. left. lia. }
split; [exact EMONO|]. split; [exact HH2| exact CK].
Qed.
End Stage.
End PMH7.
