(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnARzKit_b PnAFgSP_b PnAReset1_b PnRunA_b PnRunAa_b Ba0_code_d36f8_d36fc_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.

Module PNAPBS.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation vstr_at := (PM.vstr_at RSEGS PMSPA.accA).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (y & Hy & E). apply Nat.eqb_eq in E. subst y. exact Hy.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Theorem str_push_back_short_ok : PNRAa.str_push_back_short_spec L ar HI.
Proof using All.
  unfold PNRAa.str_push_back_short_spec, PNRA.str_push_back_short_spec.
  intros fx R0 M0 model0 K LB FF LK0 Aw0 cr0 o S r n0 HH AM0 K0 ENT FRM FRS A10 AO Ho3 VS Hn KONT.
  destruct ENT as (Rra0 & RAok & Rsp0 & Rgp0 & Rtp0 & STK0 & STKSH). change (PMSPA.pm_scr 1) with 14336 in STK0.
  rewrite L5K.rl1 in Rra0. rewrite L5K.rl2 in Rsp0. rewrite L5K.rl4 in Rtp0. rewrite L5K.rl10 in A10.
  cbn [PNL.pn_str_push_back PMA.AN NADDR_A].
  pose proof STK0 as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  pose proof VS as (DO & ACO & Hn0 & B0).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK0 cr0 Aw0 M0 model0 HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (PMKA.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK0 cr0 Aw0 M0 model0 o 24 S 14336 HH AOB ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & _).
  assert (VSTK : forall a m, S - 14336 <= a -> a + m <= 2 ^ 47 -> L5A.avis (ahid Aw0 model0) a m) by (intros a m X1 X2; apply VIS; lia).
  set (H := ahid Aw0 model0) in *. set (MV := mrestrict H M0) in *.
  assert (WST : L5.writable RSEGS MV (S - 64) 64).
  { apply (proj2 (L5A.writable_vis H M0 (S - 64) 64 (VSTK (S - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M0 S 14336); [exact STK0| lia| lia| lia]. }
  assert (WOV : L5.writable RSEGS MV o 24).
  { apply (proj2 (L5A.writable_vis H M0 o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (Dof : S - 64 + 64 <= o \/ o + 24 <= S - 64) by lia.
  assert (HO : bv_unsigned (getr R0 (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (B0v : L5.u8_at RSEGS MV o (2 * n0)).
  { apply (proj2 (L5A.u8_at_vis H M0 o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
  assert (R2 : getr R0 (reg 2) = Z_to_bv 64 S) by exact Rsp0.
  unfold PMSPA.cfg.
  pose proof (PNAFGSP.afgS_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | _ => 0 end)) as PP.
  cbn beta iota in PP. rewrite HO in PP.
  L5SAR.feed PP ltac:(first [assumption | unfold PNAFGSP.aligned; lia | lia | apply PMF.even_byte]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & _ & _ & C2 & C1 & C0 & _).
  assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra0).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xd5cf4 W_d36f8 r F_d36f8 eq_refl D_d36f8 RA1 ltac:(lia) Hr2) as MS2.
  set (W1 := fun a => (S - 64 <= a < S - 64 + 64) \/ (o + 0 <= a < o + 0 + 24)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xd5bc4 R1 r M1v W1 K HH AM0).
  { eapply msteps_trans; [exact MS1| exact MS2]. }
  { exact MG1. }
  { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha [Wa|Wa]; split.
    - apply (L5SAR.stack_client L ar LB FF 0 0 a); lia.
    - lia.
    - apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia.
    - lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (NSH : forall y, W1 y -> y < BIGSHADOW_LO \/ BIGSHADOW_HI <= y) by (intros y [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
  apply (KONT fx1 R1 M1 model1 LK0 Aw0).
  - apply L5SAR.preserved_by_index. intros y Hy. apply KS1. revert y Hy. apply sub_in. vm_compute. reflexivity.
  - split; [intros i Hi; apply MGM1; apply DO; exact Hi|].
    split; [exact (PMFA.accA_agree M0 M1 o 24 (PMARZK.agsh_frame M0 M1 W1 o 24 FR1 NSH ltac:(lia) ltac:(lia)) ACO)|].
    split; [lia|]. replace (2 * (n0 + 1)) with (2 * n0 + 2) by Lia.lia.
    rewrite <- VIS1 in C0. exact (proj1 (L5A.u8_at_vis _ M1 o _ (L5A.avis_sub _ o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) C0).
  - change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M1).
    + apply (L5SAR.ek_piece L ar LB FF S 14336 _ M0 M1 W1 FR1). intros a Ha CA OW Wa. destruct Wa as [X|X].
      * destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 14336 a HH SPT CA) as [Z1|Z1]; lia.
      * apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
    + pose proof (L5SAR.astk_grows ar M0 M1 S 14336 STK0 MGM1) as (_ & _ & _ & _ & D2 & _). exact D2.
    + apply (L5SAR.dk_grows L ar LB FF S 14336 M0 M1 MGM1).
  - exact MRT1.
  - apply incl_refl.
  - apply incl_refl.
  - exact AM1.
  - exact HH1.
Qed.
End WithHeap.
End PNAPBS.
