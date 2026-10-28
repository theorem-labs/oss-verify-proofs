(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParKit PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnSFgSP_u
     Bs0_code_57384_57388_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSPBS.
Import PMS.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). rewrite existsb_exists in H. destruct H as (x & Hx & E).
  apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.

Theorem str_push_back_short_ok : PNRS.str_push_back_short_spec L HI.
Proof.
  unfold PNRS.str_push_back_short_spec, PNR.str_push_back_short_spec.
  intros fx R0 M0 model0 K LB cr0 o S r n0 HH MOK K0 ENT A10 Ho1 Ho2 Ho3 VS Hn KONT.
  destruct ENT as (Rra0 & RAok & Rsp0 & Rgp0 & Rtp0 & STK0).
  rewrite L5K.rl1 in Rra0. rewrite L5K.rl2 in Rsp0. rewrite L5K.rl4 in Rtp0. rewrite L5K.rl10 in A10.
  change (PMSP.pm_scr 1) with 14336 in *.
  cbn [PNL.pn_str_push_back PnLayoutS_u.NADDR_S] in *.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK0 as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  pose proof VS as (DO & _ & Hn0 & B0).
  assert (BRLB : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok _ LB cr0 M0 _ HH); intros y Hy; exact Hy).
  pose proof (L5C.stk_writable RSEGS _ M0 S 14336 STK0) as WR.
  assert (WRo : L5.writable RSEGS M0 o 24) by (apply (L5C.writable_of_defined RSEGS M0 o 24 DO); lia).
  assert (HO : bv_unsigned (getr R0 (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  unfold PMSP.cfg.
  pose proof (PNSFGSP.fgS_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | _ => 0 end)) as PP.
  cbn beta iota in PP. rewrite HO in PP.
  PMK.feed PP ltac:(first [PMK.sc | apply PMF.even_byte]).
  PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & _ & FRZ0 & MS1 & KS1 & _ & _ & C2 & C1 & C0 & _)); PMK.pvz_clrT.
  replace (2 * n0 / 2) with n0 in C2, C1 by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  set (P := fun a => (S - 64 <= a < S - 64 + 64) \/ (o <= a < o + 24)).
  assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia]. }
  apply (PMK.spiece RSEGS L HI KL HIok LB cr0 M0 model0 fx fx1 R0 0x58938 R1 0x58a68 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
  { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LB M0 S 14336 a STK0); lia. }
  { intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH1.
  assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by PMK.inl; exact Rra0).
  unfold PMK.cfg.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x58a68 W_57428 r F_57428 ltac:(reflexivity) D_57428 RA1 Hr1 Hr2)|].
  apply (KONT fx1 R1 M1).
  - apply PMK.preserved_by_index. intros y Hy. apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity.
  - split; [intros i Hi; apply MG1; apply DO; exact Hi|]. split; [exact I|]. split; [lia|]. replace (2 * (n0 + 1)) with (2 * n0 + 2) by lia. exact C0.
  - apply (PMK.hpres_of L LB S 14336 _ M0 M1).
    + apply (PMK.ek_piece_in RSEGS L KL LB S 14336 _ M0 M1 P FRZ STK0 (PMFR.brange_hi L LB BRLB)). intros a [X|X]; [left; lia| right].
      apply PMK.inW_here. lia.
    + destruct (PMK.stk_grows L M0 M1 S 14336 MG1 STK0) as (_ & _ & _ & _ & D1). exact D1.
    + apply PMK.dk_grows. exact MG1.
  - exact HH1.
Qed.

End WithHeap.
End PNSPBS.
