(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrcDtorP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMSSD.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

(* [comment removed for export] *)
Definition CS0 : list nat := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition rinv (R Rk : bvmap 5 word) (sp os : Z) : Prop :=
  getr Rk (reg 2) = Z_to_bv 64 (sp - 32) /\ getr Rk (reg 8) = Z_to_bv 64 os /\ (forall x, In x CS0 -> getr Rk (reg x) = getr R (reg x)).
Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma rinv_pres R Rk Rk' sp os : rinv R Rk sp os -> regs_preserved Rk Rk' -> rinv R Rk' sp os.
Proof.
  intros (H2 & H8 & HC) RP. split; [rewrite (PMK.cs_of_preserved Rk Rk' 2 RP ltac:(PMK.inl)); exact H2|].
  split; [rewrite (PMK.cs_of_preserved Rk Rk' 8 RP ltac:(PMK.inl)); exact H8|].
  intros x Hx. rewrite <- (HC x Hx). apply (PMK.cs_of_preserved Rk Rk' x RP). revert x Hx. apply sub_in. vm_compute. reflexivity.
Qed.
Lemma rinv_ks R Rk Rk' sp os (KS : list nat) : rinv R Rk sp os -> (forall x, In x KS -> getr Rk' (reg x) = getr Rk (reg x)) ->
  forallb (fun k => existsb (Nat.eqb k) KS) (2 :: 8 :: CS0)%nat = true -> rinv R Rk' sp os.
Proof.
  intros (H2 & H8 & HC) HK SUB. pose proof (sub_in KS _ SUB) as IN.
  split; [rewrite (HK 2%nat) by (apply IN; cbn; auto); exact H2|]. split; [rewrite (HK 8%nat) by (apply IN; cbn; auto); exact H8|].
  intros x Hx. rewrite (HK x) by (apply IN; right; right; exact Hx). apply HC. exact Hx.
Qed.
Lemma m16_8 x : x mod 16 = 0 -> x mod 8 = 0.
Proof. intros H. apply Z.mod_divide in H; [|lia]. destruct H as (q & ->). replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Theorem src_dtor_ok : PMS.opdel_spec L HI -> PMS.locale_dtor_spec L -> PMS.ios_dtor_spec L HI -> PMS.src_dtor_spec L HI.
Proof.
  intros OPD LDT IDT. unfold PMS.src_dtor_spec, PMSP.src_dtor_spec.
  intros fx R M model K LB cr os isp sbp sp r src HH MOK K0 ENT A10 O1 O2 O3 SRC NI Bq BASE KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  change (PMSP.pm_scr 2) with 16384 in *.
  destruct SRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & Hq1 & Hq2 & Hq3 & Hq16 & QD & _ & _).
  destruct NI as (N0 & ND & _ & N16 & N24 & NIOS). change (pa_classic_imp AD) with 0xc8e00 in N24.
  set (qc := PM.sr_qc src) in *. unfold PM.CHUNK in *.
  pose proof (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH (incl_refl _)) as BR.
  destruct (BR _ _ Bq) as (Q0 & Q1 & Q4).
  pose proof (L5C.stk_writable RSEGS _ M sp 16384 STK) as WR.
  assert (HO : bv_unsigned (getr R (reg 10)) = os) by (rewrite A10; apply L5.unsigned_lit; lia).
  (* [comment removed for export] *)
  pose proof (PMSSDP.sdA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => qc | 34%nat => 16384 | _ => 0 end)) as P. cbn beta iota in P. rewrite HO in P.
  PMK.feed P ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A2 & A8 & B10 & B11 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
  set (P := fun a => sp - 32 <= a < sp - 32 + 32).
  unfold PMSP.cfg. cbn [pa_src_dtor AD].
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x35cd0 R1 0x56720 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
  { intros a Pa. apply (PMK.cwr_stack L LB M sp 16384 a STK). unfold P in Pa. lia. }
  { intros a. apply PMK.rng_dec. }
  intros HH1.
  assert (STK1 : L5C.stk (hl_sptop L) M1 sp 16384) by (apply (PMK.stk_grows L M M1 sp 16384 MG STK)).
  assert (INV1 : rinv R R1 sp os).
  { split; [exact A2|]. split; [rewrite A8; exact A10|]. intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity. }
  pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as Hs0. change (bv_modulus 64) with (2 ^ 64) in Hs0.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as Hs1. change (bv_modulus 64) with (2 ^ 64) in Hs1.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as Hs2. change (bv_modulus 64) with (2 ^ 64) in Hs2.
  assert (ES0 : Z_to_bv 64 (bv_unsigned (getr R (reg 8))) = getr R (reg 8)) by (apply Z_to_bv_bv_unsigned).
  assert (ES1 : Z_to_bv 64 (bv_unsigned (getr R (reg 9))) = getr R (reg 9)) by (apply Z_to_bv_bv_unsigned).
  assert (ES2 : Z_to_bv 64 (bv_unsigned (getr R (reg 18))) = getr R (reg 18)) by (apply Z_to_bv_bv_unsigned).
  set (s0v := bv_unsigned (getr R (reg 8))) in *. set (s1v := bv_unsigned (getr R (reg 9))) in *. set (s2v := bv_unsigned (getr R (reg 18))) in *.
  rewrite Rra, L5.unsigned_lit in C8 by lia.
  (* [comment removed for export] *)
  assert (A16s : (sp - 32) mod 16 = 0) by (replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact A16).
  assert (STKd : L5C.stk (hl_sptop L) M1 (sp - 32) PMSP.OPDEL_SCR).
  { apply (PMK.stk_call L M1 sp 16384 (sp - 32) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16s]. }
  assert (SCd : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
  unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD. cbn [pa_opdel AD] in OPD.
  apply (OPD fx1 R1 M1 model K LB cr qc 16384 (sp - 32) 220408 HH1 MOK K0 Bq).
  { rewrite L5K.rl10. exact B10. }
  { rewrite L5K.rl1. exact A1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact A2. }
  { rewrite L5K.rl4. rewrite (KS 4%nat) by PMK.inl. exact Rtp. }
  { exact STKd. }
  intros fx2 R2 M2 model2 RP2 HP2 MB2 HH2.
  set (LB' := lb_remove qc LB) in *.
  assert (INC : incl LB' LB) by (intros x Hx; apply (L5C.in_lb_remove qc x LB); exact Hx).
  assert (BR' : PMFR.brange L LB') by (apply (PMFR.brange_incl L LB' LB BR INC)).
  pose proof (PMFR.model_ok_but_vm model model2 MOK MB2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & Mm2).
  pose proof (rinv_pres R R1 R2 sp os INV1 RP2) as INV2. pose proof INV2 as (R2_2 & R2_8 & HC2).
  assert (EK01 : PMK.ek L LB' sp 16384 [] M M1).
  { apply (PMK.ek_piece_in RSEGS L KL LB' sp 16384 [] M M1 P FRZ STK (PMFR.brange_hi L LB' BR')). intros a Pa. left. unfold P in Pa. lia. }
  assert (EK12 : PMK.ek L LB' sp 16384 [] M1 M2).
  { apply (PMK.ek_callee_in' RSEGS L KL LB' LB' sp 16384 (sp - 32) PMSP.OPDEL_SCR [] [] M1 M2 HP2 (incl_refl _)); [unfold PMSP.OPDEL_SCR; lia|lia|lia|lia| exact (PMFR.brange_hi L LB' BR')|].
    intros a I. destruct (PMFR.inW_nil a I). }
  assert (EK02 : PMK.ek L LB' sp 16384 [] M M2) by (apply (PMK.ek_trans L LB' sp 16384 [] M M1 M2 EK01 EK12)).
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp 16384).
  { apply (PMK.stk_after RSEGS L KL LB' M1 M2 sp 16384 (sp - 32) PMSP.OPDEL_SCR [] STK1 HP2); [lia| unfold PMSP.OPDEL_SCR; lia| exact SCd]. }
  assert (SC0 : 0 <= 16384) by lia.
  assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
  assert (N24b : L5.u64_at RSEGS M2 (os + 8 + 24) 0xc8e00).
  { apply (PMFR.u64_keep RSEGS L KL LB' sp 16384 [] M M2 EK02 STK SC0); [lia|lia| intros i _; apply PMFR.inW_nil| exact N24]. }
  assert (NIOS2 : PM.iosb_at RSEGS AD PMSP.T3 M2 (os + 8 + 80) (pa_vp_nullis_ios AD) (os + 8 + 16) 0).
  { apply (PMF.iosb_at_agree RSEGS AD M M2); [lia|lia| |exact NIOS].
    apply (PMFR.ag_hi RSEGS L KL LB' sp 16384 [] M M2 EK02 STK SC0); [lia|lia| intros i _; apply PMFR.inW_nil]. }
  assert (ND2 : L5.defined M2 (os + 8) 80).
  { apply (PMFR.defined_keep RSEGS L KL LB' sp 16384 [] M M2 EK02 STK SC0); [lia|lia| intros i _; apply PMFR.inW_nil| exact ND]. }
  assert (BASE2 : PMST.base_ok RSEGS AD M2).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB' sp 16384 [] M M2 EK02); first [exact BASE | intros a _; apply L5C.outside_nil]. }
  assert (WHId : forall a, PMK.inW [] a -> sp - 32 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
  assert (EKd : PMK.ek L LB' (sp - 32) PMSP.OPDEL_SCR [] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  assert (C8b : L5.u64_at RSEGS M2 (sp - 8) r).
  { apply (PMFR.u64_keep RSEGS L KL LB' (sp - 32) PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [lia|lia| intros i _; apply PMFR.inW_nil| exact C8]. }
  assert (C16b : L5.u64_at RSEGS M2 (sp - 16) s0v).
  { apply (PMFR.u64_keep RSEGS L KL LB' (sp - 32) PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [lia|lia| intros i _; apply PMFR.inW_nil| exact C16]. }
  assert (C24b : L5.u64_at RSEGS M2 (sp - 24) s1v).
  { apply (PMFR.u64_keep RSEGS L KL LB' (sp - 32) PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [lia|lia| intros i _; apply PMFR.inW_nil| exact C24]. }
  assert (C32b : L5.u64_at RSEGS M2 (sp - 32) s2v).
  { apply (PMFR.u64_keep RSEGS L KL LB' (sp - 32) PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [lia|lia| intros i _; apply PMFR.inW_nil| exact C32]. }
  (* [comment removed for export] *)
  pose proof (L5C.stk_writable RSEGS _ M2 sp 16384 STK2) as WR2.
  pose proof BASE2 as (IMG2 & _). change (L5.img_clear M2 65536 754672) in IMG2.
  destruct NIOS2 as (J0 & J32 & J36 & J40 & J48 & JZ & JD & JX).
  assert (W88 : L5.writable RSEGS M2 (os + 88) 8) by (apply (L5C.writable_of_defined RSEGS M2 (os + 88) 8); [apply (L5.defined_sub M2 (os + 8 + 80) 152 (os + 88) 8 JD); lia|lia|lia]).
  assert (W8 : L5.writable RSEGS M2 (os + 8) 8) by (apply (L5C.writable_of_defined RSEGS M2 (os + 8) 8); [apply (L5.defined_sub M2 (os + 8) 80 (os + 8) 8 ND2); lia|lia|lia]).
  assert (W24 : L5.writable RSEGS M2 (os + 24) 8) by (apply (L5C.writable_of_defined RSEGS M2 (os + 24) 8); [apply (L5.defined_sub M2 (os + 8) 80 (os + 24) 8 ND2); lia|lia|lia]).
  LeanFeed.pfeed PB (PMSSDP.sdB_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 40%nat => os | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct PB as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ30 & MS3 & KS3 & B1 & B9 & B10b & B11b & B12 & B18 & D24 & D8 & D88)); PMK.pvz_clrT.
  set (P3 := fun a => (os + 88 <= a < os + 88 + 8) \/ (os + 8 <= a < os + 8 + 8) \/ (os + 24 <= a < os + 24 + 8)).
  assert (FRZ3 : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ30; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; left; exact X| intro X; apply N; right; right; exact X]. }
  apply (PMK.spiece RSEGS L HI KL HIok LB' cr M2 model2 fx2 fx3 R2 0x35cf8 R3 0x81cb4 M3 P3 K HH2 Mh2 Ml2 ltac:(lia) MS3 MG3 FRZ3).
  { intros a Pa. apply (PMK.cwr_stack L LB' M2 sp 16384 a STK2). destruct Pa as [X|[X|X]]; lia. }
  { intros a. apply PMK.or_dec; [apply PMK.rng_dec| apply PMK.or_dec; apply PMK.rng_dec]. }
  intros HH3.
  assert (STK3 : L5C.stk (hl_sptop L) M3 sp 16384) by (apply (PMK.stk_grows L M2 M3 sp 16384 MG3 STK2)).
  assert (AG3 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 8 \/ (os + 16 <= a /\ a + n <= os + 24) \/ (os + 32 <= a /\ a + n <= os + 88) \/ os + 96 <= a) -> L5C.agree_on M2 M3 a n).
  { intros a n X0 X1 X i Hi. apply FRZ3; [lia|]. intros [Q|[Q|Q]]; destruct X as [X|[X|[X|X]]]; lia. }     (* [comment removed for export] *)
  assert (N24c : L5.u64_at RSEGS M3 (os + 32) 0xc8e00).
  { apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; lia|lia|lia| replace (os + 32) with (os + 8 + 24) by lia; exact N24b]. }
  assert (IOS3 : PM.iosb_at RSEGS AD PMSP.T3 M3 (os + 88) 726912 (os + 8 + 16) 0).
  { replace (os + 88) with (os + 8 + 80) by lia.
    apply (PMFR.iosb_revptr RSEGS AD M2 M3 (os + 8 + 80) (pa_vp_nullis_ios AD) 726912 (os + 8 + 16) 0); [lia|lia| apply AG3; lia| replace (os + 8 + 80) with (os + 88) by lia; exact D88| |].
    - intros i Hi. apply MG3. apply JD. exact Hi.
    - split; [exact J0|]. split; [exact J32|]. split; [exact J36|]. split; [exact J40|]. split; [exact J48|]. split; [exact JZ|]. split; [exact JD| exact JX]. }
  assert (C8c : L5.u64_at RSEGS M3 (sp - 8) r) by (apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; lia|lia|lia|exact C8b]).
  assert (C16c : L5.u64_at RSEGS M3 (sp - 16) s0v) by (apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; lia|lia|lia|exact C16b]).
  assert (C24c : L5.u64_at RSEGS M3 (sp - 24) s1v) by (apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; lia|lia|lia|exact C24b]).
  assert (C32c : L5.u64_at RSEGS M3 (sp - 32) s2v) by (apply (L5C.u64_at_agree RSEGS M2 M3); [apply AG3; lia|lia|lia|exact C32b]).
  pose proof (rinv_ks R R2 R3 sp os _ INV2 KS3 ltac:(vm_compute; reflexivity)) as INV3. pose proof INV3 as (R3_2 & R3_8 & HC3).
  (* [comment removed for export] *)
  assert (STKl : L5C.stk (hl_sptop L) M3 (sp - 32) (PMSP.pm_scr 0)).
  { apply (PMK.stk_call L M3 sp 16384 (sp - 32) (PMSP.pm_scr 0) STK3); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16s]. }
  unfold PMS.locale_dtor_spec, PMSP.locale_dtor_spec in LDT.
  apply (LDT fx3 R3 M3 model2 K (os + 32) (sp - 32) 220464 Mh2 Ml2 K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact B1|]. split; [split; [lia| reflexivity]|]. split; [exact R3_2|].
    split; [rewrite (HC3 3%nat) by (cbn; auto); exact Rgp|]. split; [rewrite (HC3 4%nat) by (cbn; auto); exact Rtp|]. exact STKl. }
  { rewrite L5K.rl10. exact B10b. }
  { lia. }
  { lia. }
  { exact N24c. }
  intros fx4 R4 RP4. pose proof (rinv_pres R R3 R4 sp os INV3 RP4) as INV4. pose proof INV4 as (R4_2 & R4_8 & HC4).
  assert (R4_9 : getr R4 (reg 9) = Z_to_bv 64 (os + 8)) by (rewrite (PMK.cs_of_preserved R3 R4 9 RP4 ltac:(PMK.inl)); exact B9).
  assert (R4_18 : getr R4 (reg 18) = Z_to_bv 64 (os + 88)) by (rewrite (PMK.cs_of_preserved R3 R4 18 RP4 ltac:(PMK.inl)); exact B18).
  (* [comment removed for export] *)
  pose proof (L5C.stk_writable RSEGS _ M3 sp 16384 STK3) as WR3.
  LeanFeed.pfeed PC (PMSSDP.sdC_conc fx4 R4 M3 (fun j => match j with 2%nat => sp | 36%nat => s2v | 37%nat => s1v | 38%nat => r | 39%nat => s0v | 41%nat => os + 8 | 42%nat => os + 88 | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PC as (fx5 & R5 & M5 & _ & FR5 & _ & MS5 & KS5 & E1 & E2 & E8 & E9 & E10 & E11 & E18).
  assert (EM : M5 = M3) by (apply functional_extensionality; exact FR5). subst M5.
  apply (PMK.spiece_ro RSEGS model2 fx4 fx5 R4 0x35d30 R5 0x5d4d0 M3 K Mh2 Ml2 MS5).
  assert (CH : forall y, In y CS0 -> getr R5 (reg y) = getr R (reg y)).
  { intros y Hy. rewrite (KS5 y) by (revert y Hy; apply sub_in; vm_compute; reflexivity). apply HC4. exact Hy. }
  (* [comment removed for export] *)
  assert (EK23 : PMK.ek L LB' sp 16384 [(os, 296)] M2 M3).
  { apply (PMK.ek_piece_in RSEGS L KL LB' sp 16384 [(os, 296)] M2 M3 P3 FRZ3 STK2 (PMFR.brange_hi L LB' BR')).
    intros a Pa. right. exists (os, 296). split; [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; destruct Pa as [X|[X|X]]; lia]. }
  assert (OUTW : forall a, a < sp -> L5.outside [(os, 296)] a).
  { intros a Ha. apply PMFR.outside_of_not_inW. intros I. apply PMFR.inW_inv1 in I. lia. }
  assert (BASE3 : PMST.base_ok RSEGS AD M3).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB' sp 16384 [(os, 296)] M2 M3 EK23); first [exact BASE2 | intros a Ha; apply OUTW; cbn in Ha; lia]. }
  assert (SC1 : 0 <= PMSP.pm_scr 1) by (unfold PMSP.pm_scr; lia).
  assert (STKi : L5C.stk (hl_sptop L) M3 sp (PMSP.pm_scr 1)).
  { apply (PMK.stk_call L M3 sp 16384 sp (PMSP.pm_scr 1) STK3); [lia| unfold PMSP.pm_scr; lia| exact SC1| exact A16]. }
  unfold PMS.ios_dtor_spec, PMSP.ios_dtor_spec in IDT. cbn [pa_ios_dtor AD] in IDT.
  apply (IDT fx5 R5 M3 model2 K LB' cr (os + 88) 726912 (os + 8 + 16) 0 sp r HH3 MOK2 K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact E1|]. split; [exact RAok|]. split; [exact E2|].
    split; [rewrite (CH 3%nat) by (cbn; auto); exact Rgp|]. split; [rewrite (CH 4%nat) by (cbn; auto); exact Rtp|]. exact STKi. }
  { rewrite L5K.rl10. exact E10. }
  { lia. }
  { lia. }
  { replace (os + 88) with (os + 11 * 8) by lia. rewrite Z.mod_add by lia. exact O3. }
  { exact IOS3. }
  { exact BASE3. }
  intros fx6 R6 M6 RP6 HP6 HH6.
  apply (KONT fx6 R6 M6 model2); [| |exact MB2|exact HH6].
  - apply (PMK.regs_preserved_trans R R5 R6); [|exact RP6]. apply PMK.preserved_by_index. intros x Hx. unfold PMK.cs_all in Hx. cbn in Hx.
    destruct Hx as [<-|Hx]; [rewrite E2, Rsp; reflexivity|].
    destruct Hx as [<-|Hx]; [apply CH; cbn; auto|].
    destruct Hx as [<-|Hx]; [apply CH; cbn; auto|].
    destruct Hx as [<-|Hx]; [rewrite E8; exact ES0|].
    destruct Hx as [<-|Hx]; [rewrite E9; exact ES1|].
    destruct Hx as [<-|Hx]; [rewrite E18; exact ES2|].
    apply CH. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn; auto 20.     (* [comment removed for export] *)
  - assert (SUBW : forall a, L5.outside [(os, 296)] a -> L5.outside [] a) by (intros a _; apply L5C.outside_nil).
    assert (EK02w : PMK.ek L LB' sp 16384 [(os, 296)] M M2).
    { apply (PMK.ek_weaken L LB' LB' sp 16384 sp 16384 [(os, 296)] [] M M2 EK02 (incl_refl _)); [intros x Hx; exact Hx| exact SUBW]. }
    assert (EK36 : PMK.ek L LB' sp 16384 [(os, 296)] M3 M6).
    { apply (PMK.ek_callee_in' RSEGS L KL LB' LB' sp 16384 sp (PMSP.pm_scr 1) [(os, 296)] [(os + 88, 152)] M3 M6 HP6 (incl_refl _)); [unfold PMSP.pm_scr; lia|lia|lia|lia| exact (PMFR.brange_hi L LB' BR')|].
      intros a I. right. apply PMFR.inW_inv1 in I. exists (os, 296). split; [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (STK6 : L5C.stk (hl_sptop L) M6 sp 16384).
    { apply (PMK.stk_after RSEGS L KL LB' M3 M6 sp 16384 sp (PMSP.pm_scr 1) [(os + 88, 152)] STK3 HP6); [lia| unfold PMSP.pm_scr; lia| exact SC1]. }
    apply (PMK.hpres_of L LB' sp 16384 [(os, 296)] M M6).
    + apply (PMK.ek_trans L LB' sp 16384 [(os, 296)] M M2 M6 EK02w). apply (PMK.ek_trans L LB' sp 16384 [(os, 296)] M2 M3 M6 EK23 EK36).
    + destruct STK6 as (_ & _ & _ & _ & D6). exact D6.
    + apply (PMK.dk_trans L LB' sp 16384 M M1 M6); [apply PMK.dk_grows; exact MG|].
      apply (PMK.dk_trans L LB' sp 16384 M1 M2 M6).
      { apply (PMK.dk_callee L LB' LB' sp 16384 (sp - 32) PMSP.OPDEL_SCR [] M1 M2 HP2 (incl_refl _)); [unfold PMSP.OPDEL_SCR; lia|lia]. }
      apply (PMK.dk_trans L LB' sp 16384 M2 M3 M6); [apply PMK.dk_grows; exact MG3|].
      apply (PMK.dk_callee L LB' LB' sp 16384 sp (PMSP.pm_scr 1) [(os + 88, 152)] M3 M6 HP6 (incl_refl _)); [unfold PMSP.pm_scr; lia|lia].
Qed.

End WithHeap.
End PMSSD.
