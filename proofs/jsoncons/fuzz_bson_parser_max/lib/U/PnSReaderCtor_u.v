(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u PnCertKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5KnA_u.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnModel PnStatics PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnSReaderCtorP_u Bs0_code_35a7c_35a80_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRC.
Import PMS.

(* [comment removed for export] *)
Definition CSR : list nat := [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma CSR_in (KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) CSR = true -> forall k, In k CSR -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma csr_rcA : forall k, In k CSR -> In k PNSRCP.KS_brcA. Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Lemma csr_rcB : forall k, In k CSR -> In k PNSRCP.KS_brcB. Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Lemma csr_rcC : forall k, In k CSR -> In k PNSRCP.KS_brcC. Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Lemma csr_rcD : forall k, In k CSR -> In k PNSRCP.KS_brcD. Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Lemma csr_rcE : forall k, In k CSR -> In k PNSRCP.KS_brcE. Proof. apply CSR_in. vm_compute. reflexivity. Qed.
Lemma csr_cs : forall k, In k CSR -> In k PMK.cs_all. Proof. apply CSR_in. vm_compute. reflexivity. Qed.

Ltac t14 AG C := lazymatch type of C with
  | L5.u64_at _ ?Ms _ _ => apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
  | L5.u32_at _ ?Ms _ _ => apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
  | L5.u8_at _ ?Ms _ _ => apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | first [exact C | PMK.gmem]]
  | L5.defined ?Ms _ _ => apply (L5C.defined_agree Ms); [intros i Hi; apply AG; lia | first [exact C | PMK.gmem]]
  | L5KA.zeros_at ?Ms ?b _ => lazymatch goal with |- PM.zeros_at _ ?a _ => first [constr_eq a b | replace a with b by (clear; lia)] end;
                               apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
  | PM.zeros_at ?Ms ?b _ => lazymatch goal with |- PM.zeros_at _ ?a _ => first [constr_eq a b | replace a with b by (clear; lia)] end;
                            apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
  end.
Ltac gx AG :=
  lazymatch goal with
  | |- L5.u64_at ?sg ?M2 ?a ?v => match goal with H : L5.u64_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
        (first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
         apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
  | |- L5.u32_at ?sg ?M2 ?a ?v => match goal with H : L5.u32_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
        (first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
         apply (PMF.u32_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
  | |- L5.u8_at ?sg ?M2 ?a ?v => match goal with H : L5.u8_at sg ?M1 ?b ?v' |- _ => tryif constr_eq M1 M2 then fail else
        (first [constr_eq a b | replace a with b by (clear; lia)]; first [constr_eq v v' | replace v with v' by (clear; lia)];
         apply (L5C.u8_at_agree RSEGS M1); [intros i Hi; apply AG; lia | lia | lia | exact H]) end
  end.

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Lemma callee_ag LBc sp' scr' W' M M' : L5C.hpres L LBc sp' scr' W' M M' -> L5C.stk (hl_sptop L) M sp' scr' -> 0 <= scr' ->
  forall a, sp' <= a < 2 ^ 64 -> ~ PMK.inW W' a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros HP STK S0 a Ha N. apply (L5C.hpres_kept L LBc sp' scr' W' M M' a HP).
  apply (PMKP.kept_stack RSEGS L KL LBc M sp' scr' W' a STK S0 Ha). apply PMFR.outside_of_not_inW. exact N.
Qed.
Lemma defined_dk LB sp scr M M' a n : PMK.dk L LB sp scr M M' -> L5C.stk (hl_sptop L) M sp scr -> 0 <= scr -> sp <= a -> a + n <= 2 ^ 64 ->
  L5.defined M a n -> L5.defined M' a n.
Proof.
  intros DK (S16 & SB & SC & SD & SW) S0 Ha Hn D i Hi. pose proof (PMK.kl_img RSEGS L KL) as KI. pose proof (PMK.kl_errno RSEGS L KL) as KE.
  apply DK; [lia| | unfold in_errno; lia| apply D; exact Hi]. right. left. unfold hl_ceil. split; lia.
Qed.

(* [comment removed for export] *)
Lemma ek_piece_blk LB sp scr W M M' (P : Z -> Prop) B n :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> L5C.stk (hl_sptop L) M sp scr ->
  (forall b, In b LB -> fst b + snd b <= hl_ceil L) -> blocks_apart B n LB -> (B + n <= hl_img_lo L \/ hl_img_hi L <= B) -> B + n <= hl_ceil L ->
  (forall a, P a -> (sp - scr <= a < sp) \/ PMK.inW W a \/ (B <= a < B + n)) -> PMK.ek L LB sp scr W M M'.
Proof.
  intros E STK HLB FAP FBH FBC FP a KA. pose proof KA as (Ha & CA & NE & OW). apply E; [exact Ha|]. intros Pa.
  destruct (FP a Pa) as [S|[I|Bk]].
  - pose proof STK as (_ & Hc & _ & Hw & _). pose proof (PMK.kl_img RSEGS L KL) as KI.
    destruct CA as [(b & Hb & Hr)|[[S1 S2]|[IM _]]]; [pose proof (HLB b Hb); unfold hl_ceil in *; lia| exact (S2 S)| lia].
  - exact (PMK.inW_not_outside W a I OW).
  - exact (L5C.kept_not_fresh L LB sp scr W a B n KA FAP FBH FBC HLB Bk).
Qed.
Lemma apart_tl B n b LB : blocks_apart B n (b :: LB) -> blocks_apart B n LB.
Proof. intros H x Hx. apply H. right. exact Hx. Qed.


Theorem reader_ctor_ok : PMS.locale_ctor_spec L HI -> PMS.opnew_spec L HI -> PNRS.reader_ctor_spec L HI.
Proof.
  intros LOC OPNEW. unfold PNRS.reader_ctor_spec, PNR.reader_ctor_spec.
  intros fx R0 M0 model0 K LB cr sp r fb oo oa str sm HH MOK K0 ENT FRM A10 A11 A12 A13 Hfo Hop Hoo8 DEFO OVP ODP ISS BASE LOC0 CRED KONT.
  unfold PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is, PMSP.frame_ok in *. cbn [pa_off_p pa_off_is pa_frame pa_vp_opts AD PnLayoutS_u.ADDR_S] in *.
  unfold PNM.PSIZE in *.
  set (op := fb + 40) in *. assert (Eis : fb + 472 = op + 432) by (unfold op; lia). rewrite Eis in *.
  destruct FRM as (Hspfb & Hfbtop & Hfb16).
  pose proof MOK as (Mh & Ml & Mm).
  destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  rewrite L5K.rl12 in A12. cbn [pa_gp pa_tp AD PnLayoutS_u.ADDR_S] in Rgp, Rtp.
  pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M0 sp _ STK) as WR0.
  pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *. change (12288 + 2048 * 6) with 24576 in *.
  assert (Hop8 : op mod 8 = 0) by (unfold op; lia).
  assert (WRO : L5.writable RSEGS M0 op 416) by (apply (L5C.writable_of_defined RSEGS M0 op 416 DEFO); lia).
  pose proof (PMCK.lb_hi L HI HIok LB cr M0 _ HH) as LBhi.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M0 _ HH (incl_refl _))).
  pose proof BASE as (RO0 & _ & _ & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in RO0.
  assert (CEIL : hl_ceil L <= sp - 24576) by (unfold hl_ceil; lia).
  destruct ISS as (I0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _).
  destruct IOS as (_ & _ & _ & I160 & _). cbn [pa_vp_iss AD PnLayoutS_u.ADDR_S] in I0.
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB.
  LeanFeed.pfeed P (PNSRCP.brcA_conc fx R0 M0 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => oo | _ => 0 end)) ltac:(first [ PMK.sc | exact RO0 ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10' & A18
                      & Z160 & C136 & C128 & C120 & C112 & C144 & C140 & C32 & C24 & C152 & C104 & S120 & S112 & S104 & S96 & S88 & S80 & S72
                      & C12 & C10 & (C8 & C9) & C0 & S48 & S40 & S32 & S24 & S16b & S8)); PMK.pvz_clrT.
  clear FR1 C128 C120 C112 C32 C24 C152 C104.
  unfold PMSP.cfg.
  set (P1 := fun a => sp - 160 <= a < sp \/ op <= a < op + 16 \/ op + 24 <= a < op + 40 \/ op + 104 <= a < op + 240).
  assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P1 in NP. apply FRZ1; [exact Ha| | | |]; intros X; apply NP; lia. }
  assert (CW1 : forall a, P1 a -> PMK.cwr L LB a).
  { intros a Ha. apply (PMK.cwr_stack L LB M0 sp 24576 a STK). unfold P1 in Ha. lia. }
  assert (DEC1 : forall a, {P1 a} + {~ P1 a}) by (intros a; unfold P1; repeat apply PMK.or_dec; apply PMK.rng_dec).
  cbn [PNL.pn_reader_ctor PnLayoutS_u.NADDR_S].
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M0 model0 fx fx1 R0 0x36410 R1 0x81bdc M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 AG1 CW1 DEC1).
  intros HH1.
  assert (STK1 : L5C.stk (hl_sptop L) M1 sp 24576) by (apply (L5C.stk_grows _ M0 M1 _ _ MG1 STK)).
  assert (EK01 : PMK.ek L LB sp 24576 [(op, 416)] M0 M1).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 24576 [(op, 416)] M0 M1 P1 AG1 STK LBhi). intros a X. unfold P1 in X.
    destruct X as [X|X]; [left; lia| right; apply PMK.inW_here; lia]. }
  assert (BASE1 : PMST.base_ok RSEGS AD M1).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 416)] M0 M1 EK01); [..| exact BASE]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S];
    intros a Ha; PMKP.outW. }
  assert (LOC1 : PMST.loc_ok RSEGS AD M1 true).
  { apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 416)] M0 M1 EK01 true); [|exact LOC0].
    intros iv a Hin Ha. cbn [pa_loc_foot AD PnLayoutS_u.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW. }
  (* [comment removed for export] *)
  unfold PMS.locale_ctor_spec, PMSP.locale_ctor_spec in LOC. cbn [pa_locale_ctor AD PnLayoutS_u.ADDR_S] in LOC.
  assert (STKl1 : L5C.stk (hl_sptop L) M1 (sp - 128) (PMSP.pm_scr 2)).
  { apply (PMK.stk_call L M1 sp 24576 (sp - 128) (PMSP.pm_scr 2) STK1); unfold PMSP.pm_scr; lia. }
  apply (LOC fx1 R1 M1 model0 K LB cr (op + 152) (sp - 128) 222804 true HH1 MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact A2|].
    cbn [pa_gp pa_tp AD PnLayoutS_u.ADDR_S]. split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKl1. }
  { rewrite L5K.rl10. exact A10'. } { lia. } { lia. } { lia. }
  { apply (L5.defined_grows M0 M1 _ _ MG1). apply (L5.defined_sub M0 op 416); [exact DEFO| lia| lia]. }
  { exact BASE1. } { exact LOC1. }
  intros fx2 R2 M2 RP2 L152 LOC2 HP2 HH2. change ((op + 152, 8) :: (if true then [] else PMSP.loc_W AD)) with [(op + 152, 8)] in HP2.
  assert (AG2 : forall a, sp - 128 <= a < 2 ^ 64 -> ~ (op + 152 <= a < op + 160) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N. apply (callee_ag LB (sp - 128) (PMSP.pm_scr 2) [(op + 152, 8)] M1 M2 HP2 STKl1 ltac:(unfold PMSP.pm_scr; lia) a Ha).
    intros (rg & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp 24576).
  { apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 24576 (sp - 128) (PMSP.pm_scr 2) [(op + 152, 8)] STK1 HP2); unfold PMSP.pm_scr; lia. }
  assert (EK12 : PMK.ek L LB sp 24576 [(op, 416)] M1 M2).
  { apply (PMK.ek_callee_in RSEGS L KL LB LB sp 24576 (sp - 128) (PMSP.pm_scr 2) [(op, 416)] [(op + 152, 8)] M1 M1 M2 HP2 (incl_refl _));
      [unfold PMSP.pm_scr; lia| lia| exact STK1| exact LBhi|].
    intros a (rg & [<-|[]] & Hr). right. apply PMK.inW_here. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (DK12 : PMK.dk L LB sp 24576 M1 M2).
  { apply (PMK.dk_callee L LB LB sp 24576 (sp - 128) (PMSP.pm_scr 2) [(op + 152, 8)] M1 M2 HP2 (incl_refl _)); unfold PMSP.pm_scr; lia. }
  assert (BASE2 : PMST.base_ok RSEGS AD M2).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 416)] M1 M2 EK12); [..| exact BASE1]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S];
    intros a Ha; PMKP.outW. }
  assert (LOC2' : PMST.loc_ok RSEGS AD M2 true) by exact LOC2.
  (* [comment removed for export] *)
  assert (DEFO2 : L5.defined M2 op 416).
  { apply (defined_dk LB sp 24576 M1 M2 op 416 DK12 STK1); [lia| lia| lia|]. apply (L5.defined_grows M0 M1 _ _ MG1). exact DEFO. }
  assert (WRO2 : L5.writable RSEGS M2 op 416) by (apply (L5C.writable_of_defined RSEGS M2 op 416 DEFO2); lia).
  pose proof (L5C.stk_writable RSEGS _ M2 sp _ STK2) as WR2.
  pose proof BASE2 as (RO2 & _ & _ & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in RO2.
  LeanFeed.pfeed P (PNSRCP.brcB_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => op | _ => 0 end)) ltac:(first [ PMK.sc | exact RO2 ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & B1 & B10 & B11 & B12 & D40 & D24 & D104 & D248 & D240)); PMK.pvz_clrT.
  clear FR3 B11 B12 D40 D248 D240.
  set (P3 := fun a => op + 24 <= a < op + 32 \/ op + 40 <= a < op + 48 \/ op + 104 <= a < op + 112 \/ op + 240 <= a < op + 252).
  assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P3 in NP. apply FRZ3; [exact Ha| | | |]; intros X; apply NP; lia. }
  assert (CW3 : forall a, P3 a -> PMK.cwr L LB a).
  { intros a Ha. apply (PMK.cwr_stack L LB M2 sp 24576 a STK2). unfold P3 in Ha. lia. }
  assert (DEC3 : forall a, {P3 a} + {~ P3 a}) by (intros a; unfold P3; repeat apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model0 fx2 fx3 R2 0x36654 R3 0x81bdc M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 AG3 CW3 DEC3).
  intros HH3.
  assert (STK3 : L5C.stk (hl_sptop L) M3 sp 24576) by (apply (L5C.stk_grows _ M2 M3 _ _ MG3 STK2)).
  assert (EK23 : PMK.ek L LB sp 24576 [(op, 416)] M2 M3).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 24576 [(op, 416)] M2 M3 P3 AG3 STK2 LBhi). intros a X. unfold P3 in X. right; apply PMK.inW_here; lia. }
  assert (BASE3 : PMST.base_ok RSEGS AD M3).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 416)] M2 M3 EK23); [..| exact BASE2]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S];
    intros a Ha; PMKP.outW. }
  assert (LOC3 : PMST.loc_ok RSEGS AD M3 true).
  { apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 416)] M2 M3 EK23 true); [|exact LOC2].
    intros iv a Hin Ha. cbn [pa_loc_foot AD PnLayoutS_u.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW. }
  (* [comment removed for export] *)
  assert (STKl2 : L5C.stk (hl_sptop L) M3 (sp - 128) (PMSP.pm_scr 2)).
  { apply (PMK.stk_call L M3 sp 24576 (sp - 128) (PMSP.pm_scr 2) STK3); unfold PMSP.pm_scr; lia. }
  assert (R3sp : getr R3 (PMK.reg 2) = Z_to_bv 64 (sp - 128)).
  { rewrite (KS3 2%nat) by PMK.inl. rewrite (PMK.cs_of_preserved R1 R2 2 RP2 ltac:(PMK.inl)). exact A2. }
  apply (LOC fx3 R3 M3 model0 K LB cr (op + 48) (sp - 128) 222864 true HH3 MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact B1|]. split; [split; [lia| reflexivity]|]. split; [exact R3sp|].
    cbn [pa_gp pa_tp AD PnLayoutS_u.ADDR_S].
    split; [rewrite (KS3 3%nat) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 3 RP2 ltac:(PMK.inl)); rewrite (KS1 3%nat) by PMK.inl; exact Rgp|].
    split; [rewrite (KS3 4%nat) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 4 RP2 ltac:(PMK.inl)); rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKl2. }
  { rewrite L5K.rl10. exact B10. } { lia. } { lia. } { lia. }
  { apply (L5.defined_grows M2 M3 _ _ MG3). apply (L5.defined_sub M2 op 416); [exact DEFO2| lia| lia]. }
  { exact BASE3. } { exact LOC3. }
  intros fx4 R4 M4 RP4 L48 LOC4 HP4 HH4. change ((op + 48, 8) :: (if true then [] else PMSP.loc_W AD)) with [(op + 48, 8)] in HP4.
  assert (AG4 : forall a, sp - 128 <= a < 2 ^ 64 -> ~ (op + 48 <= a < op + 56) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha N. apply (callee_ag LB (sp - 128) (PMSP.pm_scr 2) [(op + 48, 8)] M3 M4 HP4 STKl2 ltac:(unfold PMSP.pm_scr; lia) a Ha).
    intros (rg & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (STK4 : L5C.stk (hl_sptop L) M4 sp 24576).
  { apply (PMK.stk_after RSEGS L KL LB M3 M4 sp 24576 (sp - 128) (PMSP.pm_scr 2) [(op + 48, 8)] STK3 HP4); unfold PMSP.pm_scr; lia. }
  assert (EK34 : PMK.ek L LB sp 24576 [(op, 416)] M3 M4).
  { apply (PMK.ek_callee_in RSEGS L KL LB LB sp 24576 (sp - 128) (PMSP.pm_scr 2) [(op, 416)] [(op + 48, 8)] M3 M3 M4 HP4 (incl_refl _));
      [unfold PMSP.pm_scr; lia| lia| exact STK3| exact LBhi|].
    intros a (rg & [<-|[]] & Hr). right. apply PMK.inW_here. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (DK34 : PMK.dk L LB sp 24576 M3 M4).
  { apply (PMK.dk_callee L LB LB sp 24576 (sp - 128) (PMSP.pm_scr 2) [(op + 48, 8)] M3 M4 HP4 (incl_refl _)); unfold PMSP.pm_scr; lia. }
  assert (BASE4 : PMST.base_ok RSEGS AD M4).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 416)] M3 M4 EK34); [..| exact BASE3]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S];
    intros a Ha; PMKP.outW. }
  (* [comment removed for export] *)
  assert (DEFO4 : L5.defined M4 op 416).
  { apply (defined_dk LB sp 24576 M3 M4 op 416 DK34 STK3); [lia| lia| lia|]. apply (L5.defined_grows M2 M3 _ _ MG3). exact DEFO2. }
  assert (WRO4 : L5.writable RSEGS M4 op 416) by (apply (L5C.writable_of_defined RSEGS M4 op 416 DEFO4); lia).
  pose proof (L5C.stk_writable RSEGS _ M4 sp _ STK4) as WR4.
  pose proof BASE4 as (RO4 & _ & _ & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in RO4.
  assert (AG14 : forall a, sp - 128 <= a < 2 ^ 64 -> ~ (op + 152 <= a < op + 160) -> ~ P3 a -> ~ (op + 48 <= a < op + 56) -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N1 N3 N4. rewrite (AG4 a Ha N4). rewrite (AG3 a ltac:(lia) N3). apply AG2; assumption. }
  assert (AG14r : forall a, sp - 128 <= a < 2 ^ 64 -> ~ (op + 24 <= a < op + 56) -> ~ (op + 104 <= a < op + 112) -> ~ (op + 152 <= a < op + 160)
                   -> ~ (op + 240 <= a < op + 252) -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3 N4. apply AG14; [exact Ha| exact N3| unfold P3; lia| lia]. }
  assert (AG04 : forall a, sp <= a < 2 ^ 64 -> ~ (op <= a < op + 416) -> M4 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha N. rewrite (AG14r a) by lia. apply AG1; [lia| unfold P1; lia]. }
  assert (I0' : L5.u64_at RSEGS M4 (op + 432) 740792) by t14 AG04 I0.
  assert (I160' : L5.u64_at RSEGS M4 (op + 592) (op + 448)).
  { apply (L5C.u64_at_agree RSEGS M0); [intros i Hi; apply AG04; lia| lia| lia|]. PMK.gmem. }
  assert (R4sp : getr R4 (PMK.reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (PMK.cs_of_preserved R3 R4 2 RP4 ltac:(PMK.inl)); exact R3sp).
  LeanFeed.pfeed P (PNSRCP.brcC_conc fx4 R4 M4 (fun j => match j with 2%nat => sp | 33%nat => op | _ => 0 end)) ltac:(first [ PMK.sc | exact RO4 | gx AG14r ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx5 & R5 & M5 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG5 & FR5 & FRZ5 & MS5 & KS5 & E1 & E2 & E9 & E10 & E11 & E18 & F304 & F296 & F288 & F280 & F272 & F264 & F256 & F40 & Z56)); PMK.pvz_clrT.
  clear FR5 E11 F296 F280.
  set (P5 := fun a => op + 40 <= a < op + 48 \/ op + 56 <= a < op + 104 \/ op + 256 <= a < op + 312).
  assert (AG5 : forall a, 0 <= a < 2 ^ 64 -> ~ P5 a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P5 in NP. apply FRZ5; [exact Ha| | |]; intros X; apply NP; lia. }
  assert (CW5 : forall a, P5 a -> PMK.cwr L LB a).
  { intros a Ha. apply (PMK.cwr_stack L LB M4 sp 24576 a STK4). unfold P5 in Ha. lia. }
  assert (DEC5 : forall a, {P5 a} + {~ P5 a}) by (intros a; unfold P5; repeat apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M4 model0 fx4 fx5 R4 0x36690 R5 0xb03b8 M5 P5 K HH4 Mh Ml ltac:(lia) MS5 MG5 AG5 CW5 DEC5).
  intros HH5.
  assert (STK5 : L5C.stk (hl_sptop L) M5 sp 24576) by (apply (L5C.stk_grows _ M4 M5 _ _ MG5 STK4)).
  assert (EK45 : PMK.ek L LB sp 24576 [(op, 416)] M4 M5).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 24576 [(op, 416)] M4 M5 P5 AG5 STK4 LBhi). intros a X. unfold P5 in X. right; apply PMK.inW_here; lia. }
  (* [comment removed for export] *)
  assert (SCn : 0 <= PMSP.OPNEW_SCR) by (unfold PMSP.OPNEW_SCR; lia).
  assert (STKn1 : L5C.stk (hl_sptop L) M5 (sp - 96) PMSP.OPNEW_SCR).
  { apply (PMK.stk_call L M5 sp 24576 (sp - 96) PMSP.OPNEW_SCR STK5); unfold PMSP.OPNEW_SCR; lia. }
  unfold PMS.opnew_spec, PMSP.opnew_spec in OPNEW. cbn [pa_opnew pa_tp AD PnLayoutS_u.ADDR_S] in OPNEW.
  assert (R5tp : getr R5 (PMK.reg 4) = Z_to_bv 64 0xc9fc0).
  { rewrite (KS5 4%nat) by PMK.inl. rewrite (PMK.cs_of_preserved R3 R4 4 RP4 ltac:(PMK.inl)). rewrite (KS3 4%nat) by PMK.inl.
    rewrite (PMK.cs_of_preserved R1 R2 4 RP2 ltac:(PMK.inl)). rewrite (KS1 4%nat) by PMK.inl. exact Rtp. }
  destruct CRED as (CR1 & CR2). unfold PM.credit_add, PM.cost1, PM.CHUNK, PNM.BSZ in CR1, CR2. cbn [fst snd] in CR1, CR2.
  apply (OPNEW fx5 R5 M5 model0 K LB cr 16384 (sp - 96) 222680 HH5 MOK K0).
  { rewrite L5K.rl10. exact E10. } { lia. } { unfold credit_ok. lia. }
  { rewrite L5K.rl1. exact E1. } { split; [lia| reflexivity]. } { rewrite L5K.rl2. exact E2. }
  { rewrite L5K.rl4. exact R5tp. } { exact STKn1. }
  intros fx6 R6 M6 model6 qc A10q RP6 FRESHq HP6 MB6 HH6. rewrite L5K.rl10 in A10q.
  destruct (L5C.fresh_block_bounds L LB M6 qc 16384 FRESHq) as (FQ0 & FQH & FQ16 & _ & FQC).
  destruct FRESHq as (_ & FAPq & FDEFq).
  pose proof (PMFR.model_ok_but_vm model0 model6 MOK MB6) as MOK6. pose proof MOK6 as (Mh6 & Ml6 & Mm6).
  assert (AG6 : forall a, sp - 96 <= a < 2 ^ 64 -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Ha. apply (L5C.hpres_kept L LB (sp - 96) PMSP.OPNEW_SCR [] M5 M6 a HP6).
    apply (PMKP.kept_stack RSEGS L KL LB M5 (sp - 96) PMSP.OPNEW_SCR [] a STKn1 SCn Ha). apply L5C.outside_nil. }
  assert (STK6 : L5C.stk (hl_sptop L) M6 sp 24576).
  { apply (PMK.stk_after RSEGS L KL LB M5 M6 sp 24576 (sp - 96) PMSP.OPNEW_SCR [] STK5 HP6); unfold PMSP.OPNEW_SCR; lia. }
  assert (EK56 : PMK.ek L LB sp 24576 [(op, 416)] M5 M6).
  { apply (PMK.ek_callee_in RSEGS L KL LB LB sp 24576 (sp - 96) PMSP.OPNEW_SCR [(op, 416)] [] M5 M5 M6 HP6 (incl_refl _)); [unfold PMSP.OPNEW_SCR; lia| lia| exact STK5| exact LBhi|].
    intros a X. destruct (PMFR.inW_nil a X). }
  assert (DK56 : PMK.dk L LB sp 24576 M5 M6).
  { apply (PMK.dk_callee L LB LB sp 24576 (sp - 96) PMSP.OPNEW_SCR [] M5 M6 HP6 (incl_refl _)); unfold PMSP.OPNEW_SCR; lia. }
  set (LB6 := (qc, 16384) :: LB) in *.
  (* [comment removed for export] *)
  assert (BASE5 : PMST.base_ok RSEGS AD M5).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 416)] M4 M5 EK45); [..| exact BASE4]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S];
    intros a Ha; PMKP.outW. }
  assert (BASE6 : PMST.base_ok RSEGS AD M6).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 416)] M5 M6 EK56); [..| exact BASE5]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S];
    intros a Ha; PMKP.outW. }
  pose proof BASE6 as (RO6 & _ & _ & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in RO6.
  assert (AG16 : forall a, sp - 96 <= a < 2 ^ 64 -> ~ (op + 24 <= a < op + 112) -> ~ (op + 152 <= a < op + 160) -> ~ (op + 240 <= a < op + 312) ->
            M6 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. rewrite (AG6 a) by lia. rewrite (AG5 a) by (unfold P5; lia). apply AG14r; lia. }
  assert (AG06 : forall a, sp <= a < 2 ^ 64 -> ~ (op <= a < op + 416) -> M6 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha N. rewrite (AG6 a) by lia. rewrite (AG5 a) by (unfold P5; lia). apply AG04; lia. }
  assert (DK46 : PMK.dk L LB sp 24576 M4 M6) by (apply (PMK.dk_trans L LB sp 24576 M4 M5 M6); [apply PMK.dk_grows; exact MG5| exact DK56]).
  assert (DEFO6 : L5.defined M6 op 416) by (apply (defined_dk LB sp 24576 M4 M6 op 416 DK46 STK4); [lia| lia| lia| exact DEFO4]).
  assert (WRO6 : L5.writable RSEGS M6 op 416) by (apply (L5C.writable_of_defined RSEGS M6 op 416 DEFO6); lia).
  pose proof (L5C.stk_writable RSEGS _ M6 sp _ STK6) as WR6.
  unfold PNM.MAX_DEPTH in ODP.
  LeanFeed.pfeed P (PNSRCP.brcD_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => oo | 35%nat => qc | _ => 0 end)) ltac:(first [ PMK.sc | exact RO6 | gx AG16 | gx AG06 ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx7 & R7 & M7 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG7 & FR7 & FRZ7 & MS7 & KS7 & G1 & G2 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G18 & G19 & G20
                      & H192 & H184 & H112 & H120 & H168 & H160 & H152 & H104 & H96 & H88 & H80 & H72 & H64 & H60 & H56
                      & Y408 & Y400 & Y392 & Y384 & Y376 & Y368 & Z320 & H312 & H296 & H280)); PMK.pvz_clrT.
  clear FR7 G11 G12 G13 G14 G15 H104.
  set (P7 := fun a => sp - 192 <= a < sp - 176 \/ sp - 168 <= a < sp - 144 \/ sp - 120 <= a < sp - 52 \/ op + 280 <= a < op + 288
                      \/ op + 296 <= a < op + 304 \/ op + 312 <= a < op + 316 \/ op + 320 <= a < op + 416).
  assert (AG7 : forall a, 0 <= a < 2 ^ 64 -> ~ P7 a -> M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P7 in NP. apply FRZ7; [exact Ha| | | | | | |]; intros X; apply NP; lia. }
  assert (CW7 : forall a, P7 a -> PMK.cwr L LB6 a).
  { intros a Ha. apply (PMK.cwr_stack L LB6 M6 sp 24576 a STK6). unfold P7 in Ha. lia. }
  assert (DEC7 : forall a, {P7 a} + {~ P7 a}) by (intros a; unfold P7; repeat apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB6 (debit L cr 16384) M6 model6 fx6 fx7 R6 0x365d8 R7 0xb03b8 M7 P7 K HH6 Mh6 Ml6 ltac:(lia) MS7 MG7 AG7 CW7 DEC7).
  intros HH7.
  assert (STK7 : L5C.stk (hl_sptop L) M7 sp 24576) by (apply (L5C.stk_grows _ M6 M7 _ _ MG7 STK6)).
  assert (EK67 : PMK.ek L LB sp 24576 [(op, 416)] M6 M7).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 24576 [(op, 416)] M6 M7 P7 AG7 STK6 LBhi). intros a X. unfold P7 in X.
    destruct X as [X|[X|[X|X]]]; [left; lia| left; lia| left; lia| right; apply PMK.inW_here; lia]. }
  (* [comment removed for export] *)
  assert (STKn2 : L5C.stk (hl_sptop L) M7 (sp - 192) PMSP.OPNEW_SCR).
  { apply (PMK.stk_call L M7 sp 24576 (sp - 192) PMSP.OPNEW_SCR STK7); unfold PMSP.OPNEW_SCR; lia. }
  assert (R7tp : getr R7 (PMK.reg 4) = Z_to_bv 64 0xc9fc0).
  { rewrite (KS7 4%nat) by PMK.inl. rewrite (PMK.cs_of_preserved R5 R6 4 RP6 ltac:(PMK.inl)). exact R5tp. }
  apply (OPNEW fx7 R7 M7 model6 K LB6 (debit L cr 16384) 40 (sp - 192) 223860 HH7 MOK6 K0).
  { rewrite L5K.rl10. exact G10. } { lia. } { unfold credit_ok, debit. cbn [fst snd]. lia. }
  { rewrite L5K.rl1. exact G1. } { split; [lia| reflexivity]. } { rewrite L5K.rl2. exact G2. }
  { rewrite L5K.rl4. exact R7tp. } { exact STKn2. }
  intros fx8 R8 M8 model8 bb A10bb RP8 FRESHb HP8 MB8 HH8. rewrite L5K.rl10 in A10bb.
  destruct (L5C.fresh_block_bounds L LB6 M8 bb 40 FRESHb) as (FB0 & FBH & FB16 & _ & FBC).
  destruct FRESHb as (_ & FAPb & FDEFb).
  pose proof (PMFR.model_ok_but_vm model6 model8 MOK6 MB8) as MOK8. pose proof MOK8 as (Mh8 & Ml8 & Mm8).
  assert (AG8 : forall a, sp - 192 <= a < 2 ^ 64 -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha. apply (L5C.hpres_kept L LB6 (sp - 192) PMSP.OPNEW_SCR [] M7 M8 a HP8).
    apply (PMKP.kept_stack RSEGS L KL LB6 M7 (sp - 192) PMSP.OPNEW_SCR [] a STKn2 SCn Ha). apply L5C.outside_nil. }
  assert (LBhi6 : forall b, In b LB6 -> fst b + snd b <= hl_ceil L) by (intros b0 [<-|Hb0]; [cbn; lia| apply LBhi; exact Hb0]).
  assert (BR6 : PMFR.brange L LB6) by (intros B0 m0 [E0|Hin]; [injection E0 as <- <-; lia| apply BR; exact Hin]).
  assert (AGq : L5C.agree_on M7 M8 qc 16384).
  { apply (PMFR.ag_block RSEGS L KL LB6 (sp - 192) PMSP.OPNEW_SCR [] M7 M8 (PMK.ek_of_hpres L LB6 _ _ _ M7 M8 HP8) STKn2 SCn BR6); [| left; reflexivity].
    intros a X. destruct (PMFR.inW_nil a X). }
  assert (STK8 : L5C.stk (hl_sptop L) M8 sp 24576).
  { apply (PMK.stk_after RSEGS L KL LB6 M7 M8 sp 24576 (sp - 192) PMSP.OPNEW_SCR [] STK7 HP8); unfold PMSP.OPNEW_SCR; lia. }
  assert (INC6 : incl LB LB6) by (intros x Hx; right; exact Hx).
  assert (EK78 : PMK.ek L LB sp 24576 [(op, 416)] M7 M8).
  { apply (PMK.ek_callee_in RSEGS L KL LB LB6 sp 24576 (sp - 192) PMSP.OPNEW_SCR [(op, 416)] [] M7 M7 M8 HP8 INC6); [unfold PMSP.OPNEW_SCR; lia| lia| exact STK7| exact LBhi|].
    intros a X. destruct (PMFR.inW_nil a X). }
  assert (DK78 : PMK.dk L LB sp 24576 M7 M8).
  { apply (PMK.dk_callee L LB LB6 sp 24576 (sp - 192) PMSP.OPNEW_SCR [] M7 M8 HP8 INC6); unfold PMSP.OPNEW_SCR; lia. }
  set (LB8 := (bb, 40) :: LB6) in *.
  (* [comment removed for export] *)
  assert (V1 : 0 <= bv_unsigned (getr R0 (PMK.reg 1)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V8 : 0 <= bv_unsigned (getr R0 (PMK.reg 8)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V9 : 0 <= bv_unsigned (getr R0 (PMK.reg 9)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V18 : 0 <= bv_unsigned (getr R0 (PMK.reg 18)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V19 : 0 <= bv_unsigned (getr R0 (PMK.reg 19)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  assert (V20 : 0 <= bv_unsigned (getr R0 (PMK.reg 20)) < 2 ^ 64) by (apply (bv_unsigned_in_range 64)).
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (AG18 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (op + 24 <= a < op + 112) -> ~ (op + 152 <= a < op + 160) -> ~ (op + 240 <= a < op + 416) ->
            ~ (sp - 192 <= a < sp - 52) -> M8 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3 N4. rewrite (AG8 a) by lia. rewrite (AG7 a) by (unfold P7; lia). apply AG16; lia. }
  pose proof (ly_img_lo L LY) as LYlo. pose proof (ly_img_hi L LY) as LYhi.
  assert (DEFO8 : L5.defined M8 op 416).
  { apply (defined_dk LB sp 24576 M6 M8 op 416); [apply (PMK.dk_trans L LB sp 24576 M6 M7 M8); [apply PMK.dk_grows; exact MG7| exact DK78]| exact STK6| lia| lia| lia| exact DEFO6]. }
  assert (WRO8 : L5.writable RSEGS M8 op 416) by (apply (L5C.writable_of_defined RSEGS M8 op 416 DEFO8); lia).
  pose proof (L5C.stk_writable RSEGS _ M8 sp _ STK8) as WR8.
  assert (BASE8 : PMST.base_ok RSEGS AD M8).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 24576 [(op, 416)] M6 M8 (PMK.ek_trans L LB sp 24576 _ M6 M7 M8 EK67 EK78)); [..| exact BASE6];
    cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S]; intros a Ha; PMKP.outW. }
  pose proof BASE8 as (RO8 & _ & _ & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in RO8.
  LeanFeed.pfeed P (PNSRCP.brcE_conc fx8 R8 M8 (fun j => match j with 2%nat => sp | 33%nat => op | 36%nat => bb
      | 43%nat => bv_unsigned (getr R0 (PMK.reg 1)) | 44%nat => bv_unsigned (getr R0 (PMK.reg 8)) | 45%nat => bv_unsigned (getr R0 (PMK.reg 9))
      | 46%nat => bv_unsigned (getr R0 (PMK.reg 18)) | 47%nat => bv_unsigned (getr R0 (PMK.reg 19)) | 48%nat => bv_unsigned (getr R0 (PMK.reg 20))
      | _ => 0 end)) ltac:(first [ PMK.sc | exact RO8 | gx AG18 | gx AG8 | (apply (L5C.writable_of_defined RSEGS M8 bb 40); [exact FDEFb|lia|lia]) ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx9 & R9 & M9 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG9 & FR9 & FRZ9 & MS9 & KS9 & H1 & H2 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20
                      & V400 & V408 & V392 & Q32 & Q24 & Q16 & Q8 & Q0)); PMK.pvz_clrT.
  clear FR9 H10 H11 H12 H13 H14 H15 H16 H17.
  set (P9 := fun a => sp - 176 <= a < sp - 112 \/ op + 392 <= a < op + 416 \/ bb <= a < bb + 40).
  assert (AG9 : forall a, 0 <= a < 2 ^ 64 -> ~ P9 a -> M9 (Z_to_bv 64 a) = M8 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P9 in NP. apply FRZ9; [exact Ha| | |]; intros X; apply NP; lia. }
  assert (CW9 : forall a, P9 a -> PMK.cwr L LB8 a).
  { intros a Ha. unfold P9 in Ha. destruct Ha as [X|[X|X]]; [apply (PMK.cwr_stack L LB8 M8 sp 24576 a STK8); lia| apply (PMK.cwr_stack L LB8 M8 sp 24576 a STK8); lia|].
    apply (PMK.cwr_block L LB8 bb 40 a); [left; reflexivity| lia]. }
  assert (DEC9 : forall a, {P9 a} + {~ P9 a}) by (intros a; unfold P9; repeat apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB8 (debit L (debit L cr 16384) 40) M8 model8 fx8 fx9 R8 0x36a74 R9 0x36504 M9 P9 K HH8 Mh8 Ml8 ltac:(lia) MS9 MG9 AG9 CW9 DEC9).
  intros HH9.
  (* [comment removed for export] *)
  eapply (L5.cps_of_msteps RSEGS); [exact Mh8| exact Ml8| apply (PMK.ret_to RSEGS fx9 R9 M9 0x36504 W_35b20 r F_35b20 ltac:(reflexivity) D_35b20)|].
  { rewrite H1, Z_to_bv_bv_unsigned. exact Rra. } { exact RA1. } { exact RA2. }
  assert (STK9 : L5C.stk (hl_sptop L) M9 sp 24576) by (apply (L5C.stk_grows _ M8 M9 _ _ MG9 STK8)).
  assert (EK89 : PMK.ek L LB sp 24576 [(op, 416)] M8 M9).
  { apply (ek_piece_blk LB sp 24576 [(op, 416)] M8 M9 P9 bb 40 AG9 STK8 LBhi (apart_tl bb 40 _ LB FAPb) FBH FBC).
    intros a X. unfold P9 in X. destruct X as [X|[X|X]]; [left; lia| right; left; apply PMK.inW_here; lia| right; right; lia]. }
  (* [comment removed for export] *)
  assert (AG19 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (op + 24 <= a < op + 112) -> ~ (op + 152 <= a < op + 160) -> ~ (op + 240 <= a < op + 416) ->
            ~ (sp - 192 <= a < sp - 52) -> M9 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3 N4. rewrite (AG9 a) by (unfold P9; lia). apply AG18; lia. }
  assert (AG29 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (op + 24 <= a < op + 112) -> ~ (op + 240 <= a < op + 416) -> ~ (sp - 192 <= a < sp - 52) ->
            M9 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. rewrite (AG9 a) by (unfold P9; lia). rewrite (AG8 a) by lia. rewrite (AG7 a) by (unfold P7; lia). rewrite (AG6 a) by lia.
    rewrite (AG5 a) by (unfold P5; lia). rewrite (AG4 a) by lia. apply AG3; [lia| unfold P3; lia]. }
  assert (AG39 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (op + 40 <= a < op + 104) -> ~ (op + 256 <= a < op + 416) -> ~ (sp - 192 <= a < sp - 52) ->
            M9 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3. rewrite (AG9 a) by (unfold P9; lia). rewrite (AG8 a) by lia. rewrite (AG7 a) by (unfold P7; lia). rewrite (AG6 a) by lia.
    rewrite (AG5 a) by (unfold P5; lia). apply AG4; lia. }
  assert (AG49 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (op + 40 <= a < op + 48) -> ~ (op + 56 <= a < op + 104) -> ~ (op + 256 <= a < op + 416) ->
            ~ (sp - 192 <= a < sp - 52) -> M9 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3 N4. rewrite (AG9 a) by (unfold P9; lia). rewrite (AG8 a) by lia. rewrite (AG7 a) by (unfold P7; lia). rewrite (AG6 a) by lia.
    apply AG5; [lia| unfold P5; lia]. }
  assert (AG59 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (op + 280 <= a < op + 288) -> ~ (op + 296 <= a < op + 304) -> ~ (op + 312 <= a < op + 416) ->
            ~ (sp - 192 <= a < sp - 52) -> M9 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3 N4. rewrite (AG9 a) by (unfold P9; lia). rewrite (AG8 a) by lia. rewrite (AG7 a) by (unfold P7; lia). apply AG6; lia. }
  assert (AG79 : forall a, sp - 192 <= a < 2 ^ 64 -> ~ (sp - 176 <= a < sp - 112) -> ~ (op + 392 <= a < op + 416) -> M9 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha N1 N2. rewrite (AG9 a) by (unfold P9; lia). apply AG8; lia. }
  (* [comment removed for export] *)
  assert (EK09 : PMK.ek L LB sp 24576 [(op, 416)] M0 M9).
  { apply (PMK.ek_trans L LB sp 24576 _ M0 M1 M9 EK01). apply (PMK.ek_trans L LB sp 24576 _ M1 M2 M9 EK12).
    apply (PMK.ek_trans L LB sp 24576 _ M2 M3 M9 EK23). apply (PMK.ek_trans L LB sp 24576 _ M3 M4 M9 EK34).
    apply (PMK.ek_trans L LB sp 24576 _ M4 M5 M9 EK45). apply (PMK.ek_trans L LB sp 24576 _ M5 M6 M9 EK56).
    apply (PMK.ek_trans L LB sp 24576 _ M6 M7 M9 EK67). apply (PMK.ek_trans L LB sp 24576 _ M7 M8 M9 EK78 EK89). }
  assert (DK09 : PMK.dk L LB sp 24576 M0 M9).
  { apply (PMK.dk_trans L LB sp 24576 M0 M1 M9); [apply PMK.dk_grows; exact MG1|].
    apply (PMK.dk_trans L LB sp 24576 M1 M2 M9 DK12). apply (PMK.dk_trans L LB sp 24576 M2 M3 M9); [apply PMK.dk_grows; exact MG3|].
    apply (PMK.dk_trans L LB sp 24576 M3 M4 M9 DK34). apply (PMK.dk_trans L LB sp 24576 M4 M6 M9 DK46).
    apply (PMK.dk_trans L LB sp 24576 M6 M7 M9); [apply PMK.dk_grows; exact MG7|].
    apply (PMK.dk_trans L LB sp 24576 M7 M8 M9 DK78). apply PMK.dk_grows. exact MG9. }
  assert (DEFO9 : L5.defined M9 op 416) by (apply (defined_dk LB sp 24576 M0 M9 op 416 DK09 STK); [lia|lia|lia|exact DEFO]).
  assert (DEFQ9 : L5.defined M9 qc 16384).
  { apply (L5.defined_grows M8 M9 _ _ MG9). apply (L5C.defined_agree M7 M8 qc 16384 AGq). apply (L5.defined_grows M6 M7 _ _ MG7). exact FDEFq. }
  assert (DEFB9 : L5.defined M9 bb 40) by (apply (L5.defined_grows M8 M9 _ _ MG9); exact FDEFb).
  cbn [pa_vp_parser pa_vp_nullis pa_vp_nullbuf pa_vp_nullis_ios pa_classic_imp AD PnLayoutS_u.ADDR_S] in *.
  (* [comment removed for export] *)
  assert (ZB : forall a, op + 320 <= a -> a + 8 <= op + 368 -> L5.u64_at RSEGS M9 a 0).
  { intros a H1a H2a. apply (L5C.u64_at_agree RSEGS M7); [intros i Hi; apply AG79; lia| lia| lia|]. apply (PMCG.u64_of_zeros RSEGS M7); [|lia|lia].
    apply (PMCG.zeros_sub M7 (op + 320) 48); [exact Z320|lia|lia]. }
  assert (ZB1 : forall a, op + 320 <= a < op + 368 -> L5.u8_at RSEGS M9 a 0).
  { intros a H1a. apply (L5C.u8_at_agree RSEGS M7); [intros i Hi; apply AG79; lia| lia| lia|]. apply (PMCG.u8_of_zeros RSEGS M7); [|lia|lia].
    apply (PMCG.zeros_sub M7 (op + 320) 48); [exact Z320|lia|lia]. }
  assert (T368 : L5.u8_at RSEGS M9 (op + 368) 0).
  { apply (L5C.u8_at_agree RSEGS M7); [intros i Hi; apply AG79; lia| lia| lia|]. exact (PMF.u8_of_u64 RSEGS M7 (op + 368) 0 ltac:(lia) Y368). }
  apply (KONT fx9 R9 M9 model8 qc bb (debit L (debit L cr 16384) 40)).
  - apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
    assert (CH : forall j, In j CSR -> getr R9 (PMK.reg j) = getr R0 (PMK.reg j)).
    { intros j Hj. rewrite (KS9 j (csr_rcE j Hj)), (PMK.cs_of_preserved R7 R8 j RP8 (csr_cs j Hj)), (KS7 j (csr_rcD j Hj)).
      rewrite (PMK.cs_of_preserved R5 R6 j RP6 (csr_cs j Hj)), (KS5 j (csr_rcC j Hj)), (PMK.cs_of_preserved R3 R4 j RP4 (csr_cs j Hj)).
      rewrite (KS3 j (csr_rcB j Hj)), (PMK.cs_of_preserved R1 R2 j RP2 (csr_cs j Hj)). apply KS1. apply csr_rcA. exact Hj. }
    destruct Hk as [<-|Hk]; [rewrite H2, Rsp; reflexivity|].
    destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
    destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
    destruct Hk as [<-|Hk]; [rewrite H8; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite H9; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite H18; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite H19; apply Z_to_bv_bv_unsigned|].
    destruct Hk as [<-|Hk]; [rewrite H20; apply Z_to_bv_bv_unsigned|].
    repeat (destruct Hk as [<-|Hk]; [apply CH; PMK.inl|]). destruct Hk.
  - unfold PNM.bparser_at, PNR.bparser_init. cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk PM.sr_qc PM.sr_de PM.sr_rem].
    unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    split; [t14 AG19 C0|]. split; [exact DEFO9|]. split; [exact I|].
    split; [t14 AG19 C8|]. split; [t14 AG19 C9|]. split; [t14 AG19 C10|]. split; [t14 AG19 C12|].
    split.
    { unfold PM.nullis_at. split; [t14 AG39 D24|]. split; [apply (L5.defined_sub M9 op 416); [exact DEFO9|lia|lia]|]. split; [exact I|].
      split; [t14 AG59 F40|]. split; [t14 AG49 L48|].
      unfold PM.iosb_at. split; [t14 AG39 D104|]. split; [t14 AG19 C136|]. split; [t14 AG19 C140|]. split; [t14 AG19 C144|].
      split; [t14 AG29 L152|]. split; [t14 AG19 Z160|]. split; [apply (L5.defined_sub M9 op 416); [exact DEFO9|lia|lia]|]. split; [exact I| left; reflexivity]. }
    split.
    { unfold PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem].
      split; [t14 AG59 F256|]. split; [t14 AG59 F264|]. split; [apply (L5.defined_sub M9 op 416); [exact DEFO9|lia|lia]|].
      split; [t14 AG79 H280|]. split; [unfold PM.CHUNK; t14 AG59 F288|]. split; [t14 AG79 H296|]. split; [t14 AG59 F304|].
      split; [lia|]. split; [lia|]. split; [unfold PM.CHUNK; lia|]. split; [exact FQ16|]. split; [unfold PM.CHUNK; exact DEFQ9|]. split; exact I. }
    split; [unfold PNM.MAX_DEPTH; t14 AG79 H312|]. split; [exact I|].
    split.
    { unfold PGV8.v8_at. split; [apply (L5.defined_sub M9 op 416); [exact DEFO9|lia|lia]|]. split; [exact I|].
      split; [apply ZB; lia|]. split; [apply ZB; lia| apply ZB; lia]. }
    split.
    { unfold PM.vstr_at. split; [apply (L5.defined_sub M9 op 416); [exact DEFO9|lia|lia]|]. split; [exact I|]. split; [lia|]. first [apply ZB1; lia | exact T368]. }
    split.
    { unfold PM.vstr_at. split; [apply (L5.defined_sub M9 op 416); [exact DEFO9|lia|lia]|]. split; [exact I|]. split; [lia|]. first [apply ZB1; lia | exact T368]. }
    split.
    { unfold PNM.bvec_at, PNM.BSZ. cbn [length Z.of_nat Pos.of_succ_nat]. change (2 ^ 0) with 1.
      split; [PMK.gmem|]. split; [PMK.gmem|]. split; [PMK.gmem|]. split; [lia|]. split; [lia|]. split; [exact FB16|].
      split; [replace (40 * 1) with 40 by lia; exact DEFB9|]. split; [exact I|]. split; [exact I|].
      intros i Hi. destruct i as [|i]; [|cbn in Hi; lia]. cbn [nth PNM.bs_root PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]. unfold PNM.bstate_at.
      cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
      split; [PMK.gmem|]. split; [PMK.gmem|]. split; [PMK.gmem|]. split; [PMK.gmem| PMK.gmem]. }
    split; [right; reflexivity| left; reflexivity].
  - apply PMK.hpres_of; [exact EK09| destruct STK9 as (_ & _ & _ & _ & X); exact X| exact DK09].
  - unfold PMSP.credit_keep, PMSP.cr0, PM.credit_add, PM.cost1, PM.CHUNK, PNM.BSZ, debit. cbn [fst snd]. lia.
  - apply (L5C.model_but_vm_trans _ _ _ MB6 MB8).
  - unfold PNM.bparser_own, PNM.brest_own, PNR.bparser_init, PM.src_own, PNM.bvec_own. cbn [PNM.b_src PNM.b_sb PNM.b_sk PNM.b_bb PNM.b_nb PNM.b_tb PM.sr_qc PGV8.v8_own PM.vs_own app].
    unfold PNM.BSZ. change (40 * 2 ^ 0) with 40.
    apply (hio_perm L SCFG HI HIok LB8 _ _ M9 _ HH9).
    + intros x. unfold LB8, LB6. cbn [In]. split; (intros [E|[E|E]]; [right; left; exact E| left; exact E| right; right; exact E]).
    + pose proof (proj1 (proj2 (hio_wf L SCFG HI HIok LB8 _ M9 _ HH9))) as ND. unfold LB8, LB6 in ND. cbn [map fst] in ND |- *.
      apply PMCG.nodup_swap. exact ND.
Qed.

End Stage.
End PNSRC.
