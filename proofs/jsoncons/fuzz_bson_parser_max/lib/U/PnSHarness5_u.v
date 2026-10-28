(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8 PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnTopS_u PnSHarnessStmts_u PnSHarnessKit_u PnSHarnessP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNH5.
Import PMS. Import PNH.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
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
Variable g : PNST.st.
Hypothesis Hn : 0 <= n < 2 ^ 26.
Hypothesis Hcr0 : PMSP.credit_le (PNTS.TOPK, PNTS.TOPB n) cr0.
Hypothesis Hgp : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Htp : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).

Lemma ek_widen LB (sc : Z) W Ma Mb : PMK.ek L LB (sp - 816) sc W Ma Mb -> PMK.ek L LB (sp - 784) (sc + 32) W Ma Mb.
Proof.
  intros E a (Ha & CA & NE & OW). apply E. split; [exact Ha|]. split; [|split; [exact NE|exact OW]].
  apply (PMK.client_mono L LB LB (sp - 784) (sc + 32) (sp - 816) sc a CA (incl_refl LB)). intros x Hx. lia.
Qed.
Lemma dk_widen LB (sc : Z) Ma Mb : PMK.dk L LB (sp - 816) sc Ma Mb -> PMK.dk L LB (sp - 784) (sc + 32) Ma Mb.
Proof.
  intros D a Ha CA NE DA.
  pose proof (PMK.client_mono L LB LB (sp - 784) (sc + 32) (sp - 816) sc a CA (incl_refl LB) ltac:(intros x Hx; lia)) as CA'.
  exact (D a Ha CA' NE DA).
Qed.

Lemma stage5 :
  PNRS.reset_spec L HI -> PNRS.parse_spec L HI ->
  forall (fx : FPState) R M model cr s s2 sm qc b K,
    PNH.H4 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s s2 sm qc b -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1 cr1 p sm1 ax,
        PNH.H5 L HI R0 M0 model0 sp ra n LB0 cr0 g R1 M1 model1 cr1 s s2 p sm1 ax ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x347ac M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x347a0 M model) K.
Proof using All.
  intros RST PARSE fx R M model cr s s2 sm qc b K (CORE & VS & SZ & IA & SZ2 & SG & ST0 & PA & VV & HST & HH & CK & EC & VREF) K0 KONT.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (A16f & SLO & SHI & STOP & _).
  pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
  set (p0 := PNR.bparser_init qc b) in *.
  set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
  set (LBc := PNM.bparser_own p0 ++ LBX) in *.
  assert (VREF' : L5.u64_at RSEGS M (sp - 328) (sp - 320)).
  { unfold PNH.fb, FRAME in VREF. replace (sp - 784 + 456) with (sp - 328) in VREF by lia. replace (sp - 784 + 464) with (sp - 320) in VREF by lia. exact VREF. }
  assert (BRc : PNHK.brange L LBc) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
  assert (LBhic : forall x, In x LBc -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BRc B m Hx) as (_ & _ & Q); exact Q).
  assert (BRx : PNHK.brange L LBX) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBX cr M _ HH); unfold LBc; apply incl_appr; apply incl_refl).
  assert (INCo : incl (PNM.bparser_own p0 ++ PM.vs_own s2 ++ PM.vs_own s) LBc).
  { unfold LBc, LBX. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx|]. apply in_or_app. right.
    apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply in_or_app; left; exact Hx| apply in_or_app; right; apply in_or_app; left; exact Hx]. }
  assert (OB : PNHK.hobjs sp M s s2 sm p0) by (split; [exact VS| split; [exact IA| split; [exact PA| exact VV]]]).
  assert (SC1 : 0 <= PMSP.pm_scr 1) by (unfold PMSP.pm_scr; lia).
  assert (SCt : 0 <= PMSP.pm_scr 1 + 32) by (unfold PMSP.pm_scr; lia).
  assert (STKt : L5C.stk (hl_sptop L) M (sp - 784) (PMSP.pm_scr 1 + 32)).
  { apply (PMK.stk_call L M (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 1 + 32) STK); [lia| unfold PMSP.pm_scr; lia| exact SCt| exact A16f]. }
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as V8. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as V9. change (bv_modulus 64) with (2 ^ 64) in V8, V9.
  assert (WR1 : L5.writable RSEGS M (sp - 816) 32).
  { pose proof (L5C.stk_writable RSEGS _ M _ _ STK) as WRs. apply (L5.writable_sub RSEGS M _ _ _ _ WRs); lia. }
  LeanFeed.pfeed P (PNSHP.bhnEr_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGe & FRe & FRZe & MSe & KSe & A1 & A2 & A8 & A9 & A10 & A11 & C808 & C800 & C792)); PMK.pvz_clrT.
  set (P1 := fun a => sp - 816 <= a < sp - 816 + 32).
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x347a0 R1 0x36a90 M1 P1 K HH Mh Ml ltac:(lia) MSe MGe FRZe).
  { intros a Pa. unfold P1 in Pa. left. lia. }
  { intros a. apply PMK.rng_dec. }
  intros HH1.
  assert (STK1 : L5C.stk (hl_sptop L) M1 (sp - 784) (65536 - 784)) by exact (PMK.stk_grows L M M1 _ _ MGe STK).
  assert (STKr : L5C.stk (hl_sptop L) M1 (sp - 816) (PMSP.pm_scr 1)).
  { apply (PMK.stk_call L M1 (sp - 784) (65536 - 784) (sp - 816) (PMSP.pm_scr 1) STK1); [lia| unfold PMSP.pm_scr; lia| exact SC1| lia]. }
  assert (EK1n : PMK.ek L LBc (sp - 784) (PMSP.pm_scr 1 + 32) [] M M1).
  { apply (PMK.ek_piece_in RSEGS L KL LBc (sp - 784) (PMSP.pm_scr 1 + 32) [] M M1 P1); [exact FRZe| exact STKt| exact LBhic|].
    intros a Pa. left. unfold P1 in Pa. unfold PMSP.pm_scr. lia. }
  assert (WSTD0 : forall a, PMK.inW [] a -> PNH.fb sp <= a \/ 65536 <= a < 962560) by (intros a (r & Hin & _); destruct Hin).
  assert (OB1 : PNHK.hobjs sp M1 s s2 sm p0).
  { apply (PNHK.hobjs_call L LY sp LBc (PMSP.pm_scr 1 + 32) [] M M1 EK1n STKt SCt BRc WSTD0 s s2 sm p0); [|exact INCo|exact OB].
    intros a (r & Hin & _). destruct Hin. }
  destruct OB1 as (VS1 & IA1 & PA1 & VV1).
  unfold PNRS.reset_spec in RST.
  apply (RST fx1 R1 M1 model K LBX cr (sp - 816) 215812 (sp - 784) p0 HH1).
  { repeat split; assumption. }
  { exact K0. }
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact A2|].
    split; [rewrite (KSe 3%nat) by PMK.inl; rewrite (Hcs 3%nat) by (unfold CSK; cbn; auto); exact Hgp|].
    split; [rewrite (KSe 4%nat) by PMK.inl; rewrite (Hcs 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKr. }
  { unfold PMSP.frame_ok. cbn [pa_frame AD]. split; [lia|]. split; [lia| exact A16f]. }
  { rewrite L5K.rl10. unfold PNR.o_p, PMSP.o_p. cbn [pa_off_p AD]. replace (sp - 784 + 40) with (sp - 744) by lia. exact A10. }
  { unfold PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD]. exact PA1. }
  { reflexivity. }
  { reflexivity. }
  intros fxr Rr Mr RPr PAr HPr HHr.
  unfold PNR.o_bb, PNR.o_nb, PNR.o_tb, PNR.o_stk, PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in HPr, PAr. cbn [pa_off_p pa_off_is AD] in HPr, PAr.
  match type of HPr with L5C.hpres _ _ _ _ ?W _ _ => set (W4 := W) in * end.
  assert (WC4 : forall a, PMK.inW W4 a -> sp - 744 <= a < sp - 328).
  { intros a (r & Hin & Hr). unfold W4 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia. }
  assert (EKr : PMK.ek L LBX (sp - 816) (PMSP.pm_scr 1) W4 M1 Mr) by (apply (PMK.ek_of_hpres L); exact HPr).
  assert (AGc : L5C.agree_on M1 Mr (sp - 816) 32).
  { apply (PMKP.ek_agree_stack RSEGS L KL LBX (sp - 816) (PMSP.pm_scr 1) W4 M1 Mr (sp - 816) 32 EKr STKr SC1); [lia|lia|].
    intros i Hi. apply PNHK.outside_of_not_inW. intros I. apply WC4 in I. lia. }
  assert (C808r : L5.u64_at RSEGS Mr (sp - 808) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1 Mr); [intros i Hi; apply AGc; lia|lia|lia|exact C808]).
  assert (C800r : L5.u64_at RSEGS Mr (sp - 800) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1 Mr); [intros i Hi; apply AGc; lia|lia|lia|exact C800]).
  assert (C792r : L5.u64_at RSEGS Mr (sp - 792) 214956) by (apply (L5C.u64_at_agree RSEGS M1 Mr); [intros i Hi; apply AGc; lia|lia|lia|exact C792]).
  assert (EK1w : PMK.ek L LBX (sp - 784) (PMSP.pm_scr 1 + 32) W4 M M1).
  { apply (PMK.ek_piece_in RSEGS L KL LBX (sp - 784) (PMSP.pm_scr 1 + 32) W4 M M1 P1); [exact FRZe| exact STKt| |].
    - intros x Hx. apply LBhic. unfold LBc. apply in_or_app. right. exact Hx.
    - intros a Pa. left. unfold P1 in Pa. unfold PMSP.pm_scr. lia. }
  assert (EKt : PMK.ek L LBX (sp - 784) (PMSP.pm_scr 1 + 32) W4 M Mr)
    by exact (PMK.ek_trans L LBX (sp - 784) (PMSP.pm_scr 1 + 32) W4 M M1 Mr EK1w (ek_widen LBX (PMSP.pm_scr 1) W4 M1 Mr EKr)).
  assert (WSTDt : forall a, PMK.inW W4 a -> PNH.fb sp <= a \/ 65536 <= a < 962560) by (intros a I; apply WC4 in I; left; unfold PNH.fb, FRAME; lia).
  assert (C328r : L5.u64_at RSEGS Mr (sp - 328) (sp - 320)).
  { eapply (PNHK.u64_keep L LY sp LBX (PMSP.pm_scr 1 + 32) W4 M Mr EKt STKt SCt); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact VREF'].
    intros i Hi I. apply WC4 in I. lia. }
  LeanFeed.pfeed PF (PNSHP.bhnF_conc fxr Rr Mr (fun j => match j with 2%nat => sp | 8%nat => bv_unsigned (getr R (PMK.reg 8)) | 9%nat => bv_unsigned (getr R (PMK.reg 9)) | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PF as (fxf & Rf & Mf & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MGf & FRf & FRZf & MSf & KSf & F1 & F2 & F8 & F9 & F10 & F11 & F12)); PMK.pvz_clrT.
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LBc cr Mr model fxr fxf Rr 0x34b04 Rf 0x36bc0 Mf (fun _ => False) K HHr Mh Ml ltac:(lia) MSf MGf).
  { intros a Ha _. apply FRZf. exact Ha. }
  { intros a []. }
  { intros a. right. tauto. }
  intros HHf.
  assert (EM : Mf = Mr) by (apply functional_extensionality; exact FRf). subst Mf.
  assert (RPf : regs_preserved R Rf).
  { apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
    destruct Hk as [<-|Hk]; [rewrite F2, Rsp; reflexivity|].
    destruct Hk as [<-|Hk]; [PMK.rk|]. destruct Hk as [<-|Hk]; [PMK.rk|].
    destruct Hk as [<-|Hk]; [rewrite F8; apply Z_to_bv_bv_unsigned|]. destruct Hk as [<-|Hk]; [rewrite F9; apply Z_to_bv_bv_unsigned|].
    repeat (destruct Hk as [<-|Hk]; [PMK.rk|]). destruct Hk. }
  assert (DEFt : L5.defined Mr (sp - 784 - (PMSP.pm_scr 1 + 32)) (PMSP.pm_scr 1 + 32)).
  { destruct HPr as (_ & D2 & _). destruct STK1 as (_ & _ & _ & _ & DS1).
    pose proof (L5.defined_sub M1 _ _ (sp - 816) 32 DS1 ltac:(lia) ltac:(lia)) as D1m.
    assert (D1 : L5.defined Mr (sp - 816) 32) by (eapply L5C.defined_agree; [intros i Hi; apply AGc; lia| exact D1m]).
    replace (sp - 784 - (PMSP.pm_scr 1 + 32)) with (sp - 816 - PMSP.pm_scr 1) by lia.
    apply (L5C.defined_app Mr (sp - 816 - PMSP.pm_scr 1) (PMSP.pm_scr 1) 32 D2); [replace (sp - 816 - PMSP.pm_scr 1 + PMSP.pm_scr 1) with (sp - 816) by lia; exact D1| exact SC1]. }
  assert (DKt : PMK.dk L LBX (sp - 784) (PMSP.pm_scr 1 + 32) M Mr).
  { apply (PMK.dk_trans L LBX (sp - 784) (PMSP.pm_scr 1 + 32) M M1 Mr); [apply PMK.dk_grows; exact MGe|].
    exact (dk_widen LBX (PMSP.pm_scr 1) M1 Mr (PMK.dk_of_hpres L LBX (sp - 816) (PMSP.pm_scr 1) W4 M1 Mr HPr)). }
  assert (HPt : L5C.hpres L LBX (sp - 784) (PMSP.pm_scr 1 + 32) W4 M Mr) by exact (PMK.hpres_of L LBX (sp - 784) (PMSP.pm_scr 1 + 32) W4 M Mr EKt DEFt DKt).
  assert (COREf : PNH.hcore L R0 M0 model0 sp ra LB0 Rf Mr model).
  { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R M model Rf Mr model LBX (PMSP.pm_scr 1 + 32) W4 CORE RPf HPt);
      [unfold LBX; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |apply L5C.model_but_vm_refl].
    intros a I. apply WC4 in I. left. unfold PNH.fb, FRAME. lia. }
  assert (VSf : PM.vstr_at RSEGS PMSP.T3 Mr (sp - 784 + 744) s).
  { eapply (PNHK.vstr_keep L LY sp LBX (PMSP.pm_scr 1 + 32) W4 M Mr EKt STKt SCt BRx WSTDt); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS].
    - intros i Hi I. apply WC4 in I. unfold PNH.fb, FRAME in Hi. lia.
    - unfold LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
  assert (IAf : PM.iss_at RSEGS AD PMSP.T3 Mr (sp - 784 + 472) s2 sm).
  { eapply (PNHK.iss_keep L LY sp LBX (PMSP.pm_scr 1 + 32) W4 M Mr EKt STKt SCt BRx WSTDt); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact IA].
    - intros i Hi I. apply WC4 in I. unfold PNH.fb, FRAME in Hi. lia.
    - unfold LBX. apply incl_appl. apply incl_refl. }
  assert (VVf : L5.u64_at RSEGS Mr (sp - 784 + 464) (pa_vp_visitor AD)).
  { eapply (PNHK.u64_keep L LY sp LBX (PMSP.pm_scr 1 + 32) W4 M Mr EKt STKt SCt); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact VV].
    intros i Hi I. apply WC4 in I. unfold PNH.fb, FRAME in Hi. lia. }
  assert (HSTf : PNH.hstat Mr true true (PNST.st_ax g)).
  { apply (PNHK.hstat_keep L LY LBX (sp - 784) (PMSP.pm_scr 1 + 32) W4 M Mr EKt); [|exact HST]. intros a I. apply WC4 in I. left. lia. }
  assert (ECf : PMSP.ec_at RSEGS Mr (sp - 784 + 16) 0 (pa_syscat_obj AD)).
  { unfold PMSP.ec_at in EC |- *. destruct EC as (EC0 & EC1 & _). split; [|split].
    - eapply (PNHK.u32_keep L LY sp LBX (PMSP.pm_scr 1 + 32) W4 M Mr EKt STKt SCt); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact EC0].
      intros i Hi I. apply WC4 in I. lia.
    - eapply (PNHK.u64_keep L LY sp LBX (PMSP.pm_scr 1 + 32) W4 M Mr EKt STKt SCt); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| |exact EC1].
      intros i Hi I. apply WC4 in I. lia.
    - pose proof COREf as (_ & _ & _ & _ & _ & DFR & _). unfold PNH.fb, FRAME in DFR. apply (L5.defined_sub Mr (sp - 784) 784); [exact DFR|lia|lia]. }
  assert (VREFf : L5.u64_at RSEGS Mr (sp - 784 + 456) (sp - 784 + 464)).
  { replace (sp - 784 + 456) with (sp - 328) by lia. replace (sp - 784 + 464) with (sp - 320) by lia. exact C328r. }
  assert (PAf : PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD) Mr (sp - 784 + 40) (sp - 784 + 472) p0) by exact PAr.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 Rf Mr model COREf) as (_ & Rspf & _ & _ & _ & STKf).
  pose proof COREf as (_ & Hcsf & _ & _ & _ & _ & _ & _ & _ & BASEf & _).
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB. pose proof (PNTS.pot_callB_le L n LY Hn) as (PC1 & PC2).
  assert (SC10 : 0 <= PMSP.pm_scr 10) by (unfold PMSP.pm_scr; lia).
  assert (STKc : L5C.stk (hl_sptop L) Mr (sp - 784) (PMSP.pm_scr 10)).
  { apply (PMK.stk_call L Mr (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 10) STKf); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
  destruct HSTf as (SLOC & SSYS & SERR).
  pose proof IAf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IAE & _).
  unfold PNRS.parse_spec, PNR.parse_spec in PARSE.
  apply (PARSE fxf Rf Mr model K LBX cr (sp - 784) 214956 (sp - 784) (pa_syscat_obj AD) 0 p0 s2 sm (PNST.st_ax g) HHf).
  - repeat split; assumption.
  - exact K0.
  - unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact F1|]. split; [split; [lia| reflexivity]|]. split; [exact Rspf|].
    split; [rewrite (Hcsf 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcsf 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc.
  - unfold PMSP.frame_ok. cbn [pa_frame AD]. split; [lia|]. split; [lia| exact A16f].
  - unfold PNR.bargs3, PNR.o_p, PNR.o_v, PNR.o_ec, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD]. rewrite L5K.rl10, L5K.rl11, L5K.rl12.
    split; [replace (sp - 784 + 40) with (sp - 744) by lia; exact F10|]. split; [replace (sp - 784 + 464) with (sp - 320) by lia; exact F11|].
    replace (sp - 784 + 16) with (sp - 768) by lia. exact F12.
  - unfold PNR.brun_pre, PMSP.visitor_at, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PNM.PSIZE. cbn [pa_off_p pa_off_is pa_off_v AD].
    split; [exact PAf|]. split; [exact IAf|]. split; [exact VVf|].
    split; [replace (sp - 784 + 40 + 416) with (sp - 784 + 456) by lia; exact VREFf|].
    split; [exact BASEf|]. split; [exact SERR|].
    unfold PNM.bgrow_ok, PM.tb_ok, PGV8.v8_ok. cbn. repeat split; lia.
  - unfold LBX. apply incl_appl. apply incl_refl.
  - unfold PNR.binv, p0, PNR.bparser_init. cbn [PNM.b_done PNM.b_stk].
    split; [reflexivity|].
    unfold PNR.bstack_shape. cbn [length nth]. split; [lia|]. split; [unfold PNM.MAX_DEPTH; lia|]. split; [left; reflexivity|].
    split; [intros i Hi; lia|]. intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [nth]. unfold PNM.bstate_ok, PNM.bs_root. cbn. lia.
  - unfold PNR.o_ec, PMSP.o_ec. cbn [pa_off_ec AD]. exact ECf.
  - lia.
  - unfold PM.unread, p0, PNR.bparser_init. cbn [PNM.b_src PM.sr_rem]. unfold PNH.fb, FRAME in IAE, SG. rewrite IAE, SG, SZ2.
    replace (sp - 784 + 472 + 80) with (sp - 784 + 552) by lia. lia.
  - unfold PNR.bb_room, p0, PNR.bparser_init. cbn [PNM.b_bb PGV8.v8_room]. exact I.
  - destruct CK as (CK1 & CK2). destruct Hcr0 as (C6 & C7). unfold p0, PNR.bparser_init. cbn [PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg].
    clear - CK1 CK2 C6 C7 PC1 PC2 HK HB Hn. PNHK.cred_norm. lia.
  - intros fx2 R2 M2 model2 p sm2 ax cr2 RP (RPRE & SSTEP & EMONO & ECD) HP CK2 MB HH2.
    destruct RPRE as (PA2 & IA2 & _ & _ & _ & SERR2 & _).
    set (W' := PNR.W_brun AD AN (sp - 784)) in *.
    unfold PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is in PA2, IA2. cbn [pa_off_p pa_off_is AD] in PA2, IA2.
    apply (KONT fx2 R2 M2 model2 cr2 p sm2 ax). unfold PNH.H5.
    assert (WC : forall a, PMK.inW W' a -> (sp - 784 + 16 <= a < sp - 784 + 664) \/ (PMK.inW WF a /\ PNHK.err_dom a)).
    { intros a (r & Hin & Hr). unfold W', PNR.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNR.o_src, PNR.o_bb, PNR.o_nb, PNR.o_tb, PNR.o_stk, PNR.o_ec, PNR.o_is, PNR.o_p,
        PMSP.o_is, PMSP.o_ec, PMSP.o_p, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in Hin.
      cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AD AN app] in Hin.
      unfold L5.in_rng in Hr. unfold PNHK.err_dom.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]; cbn [fst snd] in Hr;
        first [left; lia
              | right; split; [|lia]; match type of Hr with ?lo <= _ < ?lo + ?len => exists (lo, len) end;
                split; [unfold WF, PNST.pn_foot, pm_foot; cbn; auto 12| unfold L5.in_rng; cbn [fst snd]; lia]]. }
    assert (EKc : PMK.ek L LBX (sp - 784) (PMSP.pm_scr 10) W' Mr M2) by (apply (PMK.ek_of_hpres L); exact HP).
    assert (WSTD : forall a, PMK.inW W' a -> PNH.fb sp <= a \/ 65536 <= a < 962560).
    { intros a I. destruct (WC a I) as [F|(_ & F)]; [left; unfold PNH.fb, FRAME; lia| right; unfold PNHK.err_dom in F; lia]. }
    split. { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 Rf Mr model R2 M2 model2 LBX (PMSP.pm_scr 10) W' COREf RP HP);
               [unfold LBX; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
             intros a I. destruct (WC a I) as [F|(F & _)]; [left; unfold PNH.fb, FRAME; lia| right; exact F]. }
    split. { eapply (PNHK.vstr_keep L LY sp LBX (PMSP.pm_scr 10) W' Mr M2 EKc STKc SC10 BRx WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VSf].
             - intros i Hi I. unfold PNH.fb, FRAME in Hi. destruct (WC i I) as [F|(_ & F)]; [lia| unfold PNHK.err_dom in F; lia].
             - unfold LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
    split; [exact SZ|].
    split; [unfold PNH.fb, FRAME; exact IA2|].
    split; [unfold PNH.fb, FRAME; exact PA2|].
    split. { split; [|split; [|exact SERR2]].
             - apply (PNHK.loc_keep L LY LBX (sp - 784) (PMSP.pm_scr 10) W' Mr M2 EKc); [|exact SLOC].
               intros a I D. unfold PNHK.loc_dom in D. destruct (WC a I) as [F|(_ & F)]; [lia| unfold PNHK.err_dom in F; lia].
             - apply (PNHK.sys_keep L LY LBX (sp - 784) (PMSP.pm_scr 10) W' Mr M2 EKc); [|exact SSYS].
               intros a I D. unfold PNHK.sys_dom in D. destruct (WC a I) as [F|(_ & F)]; [lia| unfold PNHK.err_dom in F; lia]. }
    split; [exact EMONO|].
    split; [exact HH2|].
    destruct CK as (CKa & CKb). destruct CK2 as (CK3 & CK4). unfold p0, PNR.bparser_init in CK3, CK4. cbn [PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg] in CK3, CK4.
    clear - CKa CKb CK3 CK4 HK HB Hn. PNHK.cred_norm. lia.
Qed.

End Stage.
End PNH5.
