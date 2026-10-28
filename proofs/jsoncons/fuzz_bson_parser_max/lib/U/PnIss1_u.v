(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u PnCertKitS_u L5KnA_u PnIssStmts_u PnIssSP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMIS1.
Import PMS.

Lemma csk_icA : forall k, In k PMIS.CSK -> In k PMISP.KS_icA. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_icB : forall k, In k PMIS.CSK -> In k PMISP.KS_icB. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.
Lemma csk_cs : forall k, In k PMIS.CSK -> In k PMK.cs_all. Proof. apply PMIS.CSK_in. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma locW_low (b : bool) a : PMK.inW (if b then [] else PMSP.loc_W AD) a -> 0xc87f2 <= a < 0xc96b0.
Proof.
  destruct b; intros (rg & Hin & Hr); [destruct Hin|]. unfold PMSP.loc_W in Hin. cbn [map pa_loc_foot AD PnLayoutS_u.ADDR_S fst snd] in Hin.
  unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma WF_inv ois b a : PMK.inW (PMIS.WF ois b) a -> (ois <= a < ois + 272) \/ 0xc87f2 <= a < 0xc96b0.
Proof.
  unfold PMIS.WF. intros (rg & [<-|Hin] & Hr); [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
  right. apply (locW_low b a). exists rg. split; assumption.
Qed.
Lemma W1_inv (o : Z) (b : bool) (a : Z) : PMK.inW ((o, 8) :: (if b then [] else PMSP.loc_W AD)) a -> (o <= a < o + 8) \/ 0xc87f2 <= a < 0xc96b0.
Proof.
  intros (rg & [<-|Hin] & Hr); [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
  right. apply (locW_low b a). exists rg. split; assumption.
Qed.
Lemma outside_WF ois b a : (a < ois \/ ois + 272 <= a) -> (a < 0xc87f2 \/ 0xc96b0 <= a) -> L5.outside (PMIS.WF ois b) a.
Proof.
  intros H1 H2. apply PMFR.outside_of_not_inW. intros I. destruct (WF_inv ois b a I); lia.
Qed.
Lemma outside_WF_ois ois b a : L5.outside (PMIS.WF ois b) a -> L5.outside [(ois, 272)] a.
Proof.
  intros O. unfold PMIS.WF in O. apply L5C.outside_cons_inv in O. apply L5C.outside_cons; [exact (proj1 O)| apply L5C.outside_nil].
Qed.

(* [comment removed for export] *)
Ltac t14 AG C := lazymatch type of C with
  | L5.u64_at _ ?Ms _ _ => apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | exact C]
  | L5.u32_at _ ?Ms _ _ => apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | exact C]
  | L5.u8_at _ ?Ms _ _ => apply (L5C.u8_at_agree RSEGS Ms); [intros i Hi; apply AG; lia | lia | lia | exact C]
  | L5.defined ?Ms _ _ => apply (L5C.defined_agree Ms); [intros i Hi; apply AG; lia | exact C]
  | L5KA.zeros_at ?Ms _ _ => apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
  | PM.zeros_at ?Ms _ _ => apply (PMF.zeros_at_agree Ms); [intros i Hi; apply AG; lia | exact C]
  end.

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

(* [comment removed for export] *)
Lemma callee_ag LBc sp' scr' W' M M' : L5C.hpres L LBc sp' scr' W' M M' -> L5C.stk (hl_sptop L) M sp' scr' -> 0 <= scr' ->
  forall a, sp' <= a < 2 ^ 64 -> ~ PMK.inW W' a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros HP STK S0 a Ha N. apply (L5C.hpres_kept L LBc sp' scr' W' M M' a HP).
  apply (PMKP.kept_stack RSEGS L KL LBc M sp' scr' W' a STK S0 Ha). apply PMFR.outside_of_not_inW. exact N.
Qed.
(* [comment removed for export] *)
Lemma defined_dk LB sp scr M M' a n : PMK.dk L LB sp scr M M' -> L5C.stk (hl_sptop L) M sp scr -> 0 <= scr -> sp <= a -> a + n <= 2 ^ 64 ->
  L5.defined M a n -> L5.defined M' a n.
Proof.
  intros DK (S16 & SB & SC & SD & SW) S0 Ha Hn D i Hi. pose proof (PMK.kl_img RSEGS L KL) as KI. pose proof (PMK.kl_errno RSEGS L KL) as KE.
  apply DK; [lia| | unfold in_errno; lia| apply D; exact Hi]. right. left. unfold hl_ceil. split; lia.
Qed.

Lemma head : PMS.locale_ctor_spec L HI ->
  forall (fx : FPState) R0 M0 model0 K LB cr ois os sp r s b,
    PMIS.pre L HI R0 M0 model0 K LB cr ois os sp r s b ->
    (forall (fx1 : FPState) R1 M1 model1, PMIS.mid L HI R0 M0 model0 LB cr ois os sp s b R1 M1 model1 ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36204 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x349d4 M0 model0) K.
Proof.
  intros LOC fx R0 M0 model0 K LB cr ois os sp r s b PRE KONT.
  destruct PRE as (HH & MOK & K0 & ENT & A10 & A11 & A12 & Hspo & Hoos & Hostop & Ho8 & Hos8 & DEFO & VS & INCL & SZ & LNG & BASE & LOCb & CRED).
  pose proof MOK as (Mh & Ml & Mm).
  destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  cbn [pa_gp pa_tp AD PnLayoutS_u.ADDR_S] in Rgp, Rtp.
  pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M0 sp _ STK) as WR0.
  pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *. change (12288 + 2048 * 4) with 20480 in *.
  assert (WRO : L5.writable RSEGS M0 ois 272) by (apply (L5C.writable_of_defined RSEGS M0 ois 272 DEFO); lia).
  pose proof (PMCK.lb_hi L HI HIok LB cr M0 _ HH) as LBhi.
  pose proof BASE as (RO0 & _ & _ & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in RO0.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M0 _ HH (incl_refl _))).
  LeanFeed.pfeed P (PMISP.icA_conc fx R0 M0 (fun j => match j with 2%nat => sp | 33%nat => ois | 39%nat => os - ois | _ => 0 end)) ltac:(first [ PMK.sc | exact RO0 ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & B1 & B2 & B8 & B9 & B10 & B18 & B19 & B20 & B21 & B22 & B23
                      & Z176 & C152 & C144 & C136 & C128 & C160 & C156 & C8 & C120 & C0 & C168 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16b & S8)); PMK.pvz_clrT.
  clear FR1 C144 C136 C128 C8 C120 C0 C168.
  unfold PMSP.cfg.
  set (P1 := fun a => sp - 208 <= a < sp \/ ois <= a < ois + 16 \/ ois + 120 <= a < ois + 256).
  assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P1 in NP. apply FRZ1; [exact Ha| | |]; intros X; apply NP; lia. }
  assert (CW1 : forall a, P1 a -> PMK.cwr L LB a).
  { intros a Ha. apply (PMK.cwr_stack L LB M0 sp 20480 a STK). unfold P1 in Ha. lia. }
  assert (DEC1 : forall a, {P1 a} + {~ P1 a}) by (intros a; unfold P1; repeat apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M0 model0 fx fx1 R0 0x349d4 R1 0x81bdc M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 AG1 CW1 DEC1).
  intros HH1.
  assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by (apply (L5C.stk_grows _ M0 M1 _ _ MG1 STK)).
  assert (E01n : PMK.ek L LB sp 20480 [(ois, 272)] M0 M1).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [(ois, 272)] M0 M1 P1 AG1 STK LBhi). intros a X. unfold P1 in X.
    destruct X as [X|X]; [left; lia| right; apply PMK.inW_here; lia]. }
  assert (BASE1 : PMST.base_ok RSEGS AD M1).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M0 M1 E01n); [..| exact BASE]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S];
    intros a Ha; PMKP.outW. }
  assert (LOC1 : PMST.loc_ok RSEGS AD M1 b).
  { apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M0 M1 E01n b); [|exact LOCb].
    intros iv a Hin Ha. cbn [pa_loc_foot AD PnLayoutS_u.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW. }
  (* [comment removed for export] *)
  assert (STKl1 : L5C.stk (hl_sptop L) M1 (sp - 80) (PMSP.pm_scr 2)).
  { apply (PMK.stk_call L M1 sp 20480 (sp - 80) (PMSP.pm_scr 2) STK1); unfold PMSP.pm_scr; lia. }
  unfold PMS.locale_ctor_spec, PMSP.locale_ctor_spec in LOC. cbn [pa_locale_ctor AD PnLayoutS_u.ADDR_S] in LOC.
  apply (LOC fx1 R1 M1 model0 K LB cr (ois + 168) (sp - 80) 215644 b HH1 MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact B1|]. split; [split; [lia| reflexivity]|]. split; [exact B2|].
    cbn [pa_gp pa_tp AD PnLayoutS_u.ADDR_S]. split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKl1. }
  { rewrite L5K.rl10. exact B10. } { lia. } { lia. } { lia. }
  { apply (L5.defined_grows M0 M1 _ _ MG1). apply (L5.defined_sub M0 ois 272); [exact DEFO| lia| lia]. }
  { exact BASE1. } { exact LOC1. }
  intros fx2 R2 M2 RP2 C168 LOC2 HP2 HH2.
  set (W2 := (ois + 168, 8) :: (if b then [] else PMSP.loc_W AD)) in HP2.
  assert (AG2 : forall a, sp - 80 <= a < 2 ^ 64 -> ~ (ois + 168 <= a < ois + 176) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N. apply (callee_ag LB (sp - 80) (PMSP.pm_scr 2) W2 M1 M2 HP2 STKl1 ltac:(unfold PMSP.pm_scr; lia) a Ha).
    intros I. destruct (W1_inv (ois + 168) b a I); lia. }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480).
  { apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 80) (PMSP.pm_scr 2) W2 STK1 HP2); unfold PMSP.pm_scr; lia. }
  assert (E12 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M1 M2).
  { apply (PMK.ek_callee_in RSEGS L KL LB LB sp 20480 (sp - 80) (PMSP.pm_scr 2) (PMIS.WF ois b) W2 M1 M1 M2 HP2 (incl_refl _));
      [unfold PMSP.pm_scr; lia| lia| exact STK1| exact LBhi|].
    intros a I. right. unfold W2 in I. destruct I as (rg & [<-|Hin] & Hr).
    - unfold PMIS.WF. apply PMK.inW_here. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia.
    - unfold PMIS.WF. apply PMK.inW_next. exists rg. split; assumption. }
  assert (DK12 : PMK.dk L LB sp 20480 M1 M2).
  { apply (PMK.dk_callee L LB LB sp 20480 (sp - 80) (PMSP.pm_scr 2) W2 M1 M2 HP2 (incl_refl _)); unfold PMSP.pm_scr; lia. }
  assert (BASE2 : PMST.base_ok RSEGS AD M2).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 (PMIS.WF ois b) M1 M2 E12); [..| exact BASE1];
    cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S]; intros a Ha; apply outside_WF; lia. }
  (* [comment removed for export] *)
  assert (SP80 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 80)) by (rewrite (PMK.cs_of_preserved R1 R2 2 RP2 ltac:(PMK.inl)); exact B2).
  assert (WR2 : L5.writable RSEGS M2 (sp - 20480) 20480) by (apply (L5C.stk_writable RSEGS _ M2 sp _ STK2)).
  assert (DEFO2 : L5.defined M2 ois 272).
  { apply (defined_dk LB sp 20480 M1 M2 ois 272 DK12 STK1); [lia| lia| lia|]. apply (L5.defined_grows M0 M1 _ _ MG1). exact DEFO. }
  assert (WRO2 : L5.writable RSEGS M2 ois 272) by (apply (L5C.writable_of_defined RSEGS M2 ois 272 DEFO2); lia).
  pose proof BASE2 as (RO2 & _ & _ & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in RO2.
  LeanFeed.pfeed P (PMISP.icB_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => ois | 39%nat => os - ois | _ => 0 end)) ltac:(first [ PMK.sc | exact RO2 ]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & D1 & D2 & D8 & D9 & D10 & D11 & D12 & D19 & D20 & D21 & D23
                      & E16 & T136 & T128 & T120 & T112 & T104 & T96 & T88 & E120 & E0 & F266 & F265 & F264 & F256 & F267)); PMK.pvz_clrT.
  clear FR3 F266 F265 F264 F256 F267 E16.
  set (P3 := fun a => sp - 144 <= a < sp - 80 \/ ois <= a < ois + 8 \/ ois + 16 <= a < ois + 24 \/ ois + 120 <= a < ois + 128 \/ ois + 256 <= a < ois + 268).
  assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha NP. unfold P3 in NP. apply FRZ3; [exact Ha| | | | |]; intros X; apply NP; lia. }
  assert (CW3 : forall a, P3 a -> PMK.cwr L LB a).
  { intros a Ha. apply (PMK.cwr_stack L LB M2 sp 20480 a STK2). unfold P3 in Ha. lia. }
  assert (DEC3 : forall a, {P3 a} + {~ P3 a}) by (intros a; unfold P3; repeat apply PMK.or_dec; apply PMK.rng_dec).
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model0 fx2 fx3 R2 0x34a5c R3 0x81bdc M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 AG3 CW3 DEC3).
  intros HH3.
  assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480) by (apply (L5C.stk_grows _ M2 M3 _ _ MG3 STK2)).
  assert (E23n : PMK.ek L LB sp 20480 [(ois, 272)] M2 M3).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [(ois, 272)] M2 M3 P3 AG3 STK2 LBhi). intros a X. unfold P3 in X.
    destruct X as [X|X]; [left; lia| right; apply PMK.inW_here; lia]. }
  assert (E23 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M2 M3).
  { apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 (PMIS.WF ois b) [(ois, 272)] M2 M3 E23n (incl_refl _)); [intros x Hx; exact Hx|].
    apply outside_WF_ois. }
  assert (BASE3 : PMST.base_ok RSEGS AD M3).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M2 M3 E23n); [..| exact BASE2]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S];
    intros a Ha; PMKP.outW. }
  assert (LOC3 : PMST.loc_ok RSEGS AD M3 true).
  { apply (PMKP.loc_ok_keep RSEGS AD L KL SF LB sp 20480 [(ois, 272)] M2 M3 E23n true); [|exact LOC2].
    intros iv a Hin Ha. cbn [pa_loc_foot AD PnLayoutS_u.ADDR_S] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Ha; PMKP.outW. }
  (* [comment removed for export] *)
  assert (STKl2 : L5C.stk (hl_sptop L) M3 (sp - 144) (PMSP.pm_scr 2)).
  { apply (PMK.stk_call L M3 sp 20480 (sp - 144) (PMSP.pm_scr 2) STK3); unfold PMSP.pm_scr; lia. }
  apply (LOC fx3 R3 M3 model0 K LB cr (ois + 24) (sp - 144) 221700 true HH3 MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact D1|]. split; [split; [lia| reflexivity]|]. split; [exact D2|].
    cbn [pa_gp pa_tp AD PnLayoutS_u.ADDR_S].
    split; [rewrite (KS3 3%nat) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 3 RP2 ltac:(PMK.inl)); rewrite (KS1 3%nat) by PMK.inl; exact Rgp|].
    split; [rewrite (KS3 4%nat) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 4 RP2 ltac:(PMK.inl)); rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKl2. }
  { rewrite L5K.rl10. exact D10. } { lia. } { lia. } { lia. }
  { apply (L5.defined_grows M2 M3 _ _ MG3). apply (L5.defined_sub M2 ois 272); [exact DEFO2| lia| lia]. }
  { exact BASE3. } { exact LOC3. }
  intros fx4 R4 M4 RP4 C24 LOC4 HP4 HH4. change ((ois + 24, 8) :: (if true then [] else PMSP.loc_W AD)) with [(ois + 24, 8)] in HP4.
  assert (AG4 : forall a, sp - 144 <= a < 2 ^ 64 -> ~ (ois + 24 <= a < ois + 32) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha N. apply (callee_ag LB (sp - 144) (PMSP.pm_scr 2) [(ois + 24, 8)] M3 M4 HP4 STKl2 ltac:(unfold PMSP.pm_scr; lia) a Ha).
    intros (rg & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (STK4 : L5C.stk (hl_sptop L) M4 sp 20480).
  { apply (PMK.stk_after RSEGS L KL LB M3 M4 sp 20480 (sp - 144) (PMSP.pm_scr 2) [(ois + 24, 8)] STK3 HP4); unfold PMSP.pm_scr; lia. }
  assert (E34 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M3 M4).
  { apply (PMK.ek_callee_in RSEGS L KL LB LB sp 20480 (sp - 144) (PMSP.pm_scr 2) (PMIS.WF ois b) [(ois + 24, 8)] M3 M3 M4 HP4 (incl_refl _));
      [unfold PMSP.pm_scr; lia| lia| exact STK3| exact LBhi|].
    intros a (rg & [<-|[]] & Hr). right. unfold PMIS.WF. apply PMK.inW_here. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (DK34 : PMK.dk L LB sp 20480 M3 M4).
  { apply (PMK.dk_callee L LB LB sp 20480 (sp - 144) (PMSP.pm_scr 2) [(ois + 24, 8)] M3 M4 HP4 (incl_refl _)); unfold PMSP.pm_scr; lia. }
  (* [comment removed for export] *)
  assert (E01 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M0 M1).
  { apply (PMK.ek_weaken L LB LB sp 20480 sp 20480 (PMIS.WF ois b) [(ois, 272)] M0 M1 E01n (incl_refl _)); [intros x Hx; exact Hx|].
    apply outside_WF_ois. }
  assert (E04 : PMK.ek L LB sp 20480 (PMIS.WF ois b) M0 M4).
  { apply (PMK.ek_trans L LB sp 20480 _ M0 M1 M4 E01). apply (PMK.ek_trans L LB sp 20480 _ M1 M2 M4 E12).
    apply (PMK.ek_trans L LB sp 20480 _ M2 M3 M4 E23 E34). }
  assert (DK04 : PMK.dk L LB sp 20480 M0 M4).
  { apply (PMK.dk_trans L LB sp 20480 M0 M1 M4); [apply PMK.dk_grows; exact MG1|].
    apply (PMK.dk_trans L LB sp 20480 M1 M2 M4 DK12). apply (PMK.dk_trans L LB sp 20480 M2 M3 M4); [apply PMK.dk_grows; exact MG3| exact DK34]. }
  assert (AG14 : forall a, sp - 80 <= a < 2 ^ 64 -> ~ (ois + 168 <= a < ois + 176) -> ~ (sp - 144 <= a < sp - 80) -> ~ (ois <= a < ois + 8)
            -> ~ (ois + 16 <= a < ois + 32) -> ~ (ois + 120 <= a < ois + 128) -> ~ (ois + 256 <= a < ois + 268) -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. rewrite (AG4 a) by lia. rewrite (AG3 a) by (unfold P3; lia). apply AG2; lia. }
  assert (AG24 : forall a, sp - 144 <= a < 2 ^ 64 -> ~ (sp - 144 <= a < sp - 80) -> ~ (ois <= a < ois + 8)
            -> ~ (ois + 16 <= a < ois + 32) -> ~ (ois + 120 <= a < ois + 128) -> ~ (ois + 256 <= a < ois + 268) -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha N2 N3 N4 N5 N6. rewrite (AG4 a) by lia. apply AG3; [lia|]. unfold P3; lia. }
  apply (KONT fx4 R4 M4 model0).
  unfold PMIS.mid.
  assert (V1 : 0 <= bv_unsigned (getr R0 (PMK.reg 1)) < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (getr R0 (PMK.reg 1))) as X; exact X).
  split; [rewrite (PMK.cs_of_preserved R3 R4 2 RP4 ltac:(PMK.inl)); exact D2|].
  split; [rewrite (PMK.cs_of_preserved R3 R4 8 RP4 ltac:(PMK.inl)); exact D8|].
  split; [rewrite (PMK.cs_of_preserved R3 R4 9 RP4 ltac:(PMK.inl)); exact D9|].
  split; [rewrite (PMK.cs_of_preserved R3 R4 19 RP4 ltac:(PMK.inl)); exact D19|].
  split; [rewrite (PMK.cs_of_preserved R3 R4 20 RP4 ltac:(PMK.inl)); rewrite D20; f_equal; lia|].
  split; [rewrite (PMK.cs_of_preserved R3 R4 21 RP4 ltac:(PMK.inl)); exact D21|].
  split.
  { intros k Hk. rewrite (PMK.cs_of_preserved R3 R4 k RP4 (csk_cs k Hk)). rewrite (KS3 k (csk_icB k Hk)).
    rewrite (PMK.cs_of_preserved R1 R2 k RP2 (csk_cs k Hk)). apply KS1. apply csk_icA. exact Hk. }
  split.
  { unfold PMIS.saves_iss. split; [t14 AG14 S8|]. split; [t14 AG14 S16b|]. split; [t14 AG14 S24|]. split; [t14 AG14 S32|].
    split; [t14 AG14 S40|]. split; [t14 AG14 S48|]. split; [t14 AG14 S56|]. split; [t14 AG14 S64| t14 AG14 S72]. }
  split.
  { unfold PMIS.saves_sb. split; [t14 AG4 T88|]. split; [t14 AG4 T96|].
    split; [replace os with (ois + (os - ois)) by lia; t14 AG4 T104|]. split; [t14 AG4 T112|]. split; [t14 AG4 T120|].
    split; [t14 AG4 T128| t14 AG4 T136]. }
  split.
  { unfold PMIS.head_cells. cbn [pa_vp_iss pa_classic_imp pa_vp_iss_ios AD PnLayoutS_u.ADDR_S].
    split; [t14 AG4 E0|]. split; [exact C24|]. split; [t14 AG4 E120|].
    split; [t14 AG14 C152|]. split; [t14 AG14 C156|]. split; [t14 AG14 C160|].
    split; [cbn [pa_classic_imp AD PnLayoutS_u.ADDR_S] in C168; t14 AG24 C168| t14 AG14 Z176]. }
  split; [apply (defined_dk LB sp 20480 M0 M4 ois 272 DK04 STK); [lia|lia|lia|exact DEFO]|].
  split.
  { apply (PMFR.vstr_keep RSEGS L KL LB sp 20480 (PMIS.WF ois b) M0 M4 E04 STK ltac:(lia) BR); [| lia| lia| | exact INCL| exact VS].
    - intros a I. destruct (WF_inv ois b a I); [left; lia| right; pose proof (ly_img_lo L LY); pose proof (ly_img_hi L LY); lia].
    - intros i Hi I. destruct (WF_inv ois b i I); lia. }
  split; [exact STK4|].
  split.
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 20480 (PMIS.WF ois b) M3 M4 E34); [..| exact BASE3];
    cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S]; intros a Ha; apply outside_WF; lia. }
  split; [exact LOC4|].
  split; [exact HH4|]. split; [exact MOK|]. split; [apply L5C.model_but_vm_refl|].
  split; [exact E04| exact DK04].
Qed.

End Stage.
End PMIS1.
