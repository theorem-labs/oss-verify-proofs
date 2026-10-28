(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b PnASysP_b Ba0_code_rd4274_d4278_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMASY.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Lemma writable_img M a n : wseg_ok RSEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 < n -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof.
  intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
  eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (Datatypes.S k)).
  - rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
  - apply store_ok_wseg. exact W.
  - rewrite !L5.unsigned_lit by lia. lia.
  - rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.

Theorem syscat_ok : PMA.syscat_spec L ar HI.
Proof.
  unfold PMA.syscat_spec, PMSPA.syscat_spec.
  intros fx R M model K LB FF LK Aw cr sp r b HH AM K0 ENT FRM FRS BASE SYS KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof RAok as (Hr1 & Hr2). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  change (PMSPA.pm_scr 1) with 14336 in *.
  assert (SP0 : 0 <= sp) by (unfold app_mem, FS_BYTES in *; lia).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  unfold PMSPA.cfg. cbn [pa_syscat PMA.AD ADDR_A].
  cbn [pa_syscat_guard PMA.AD ADDR_A] in SYS.
  destruct b.
  - (* [comment removed for export] *)
    cbn in SYS.
    assert (VG : L5.u8_at RSEGS MV 6759728 1).
    { apply (proj2 (L5A.u8_at_vis H M 6759728 1 (VIMG 6759728 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact SYS. }
    LeanFeed.pfeed P (PMASYP.asyA_conc fx R MV (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [assumption | exact Rsp | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & FR1 & _ & MS1 & KS1 & A10).
    assert (E1 : M1v = MV) by (apply functional_extensionality; exact FR1). subst M1v.
    assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    pose proof (PMK.ret_to RSEGS fx1 R1 MV 0xd9524 W_d6f28 r F_d6f28 eq_refl D_d6f28 R1ra ltac:(lia) Hr2) as MS2.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xd950c R1 r MV K HH AM).
    { eapply msteps_trans; [exact MS1| exact MS2]. }
    { intros a Ha. exact Ha. }
    { intros a Ha. reflexivity. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1'.
    apply (KONT fx1 R1 M1 model1 LK Aw).
    + apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
    + exact A10.
    + unfold PMST.sys_ok. cbn [pa_syscat_guard PMA.AD ADDR_A]. apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1'; lia | lia | lia | exact SYS].
    + change (PMSPA.pm_scr 1) with 14336. split; [intros a (Ha & _); apply FR1'; exact Ha|]. split.
      * eapply L5C.defined_agree; [intros i Hi; apply FR1'; lia| exact SDEF].
      * intros a Ha _ Hn. rewrite FR1' by exact Ha. exact Hn.
    + exact MRT1.
    + intros x Hx. exact Hx.
    + intros x Hx. exact Hx.
    + exact AM1.
    + exact HH1.
  - (* [comment removed for export] *)
    cbn in SYS.
    assert (V0 : L5.img_clear MV 6759728 6759730) by (apply L5A.img_clear_mrestrict; exact SYS).
    assert (V1 : L5.writable RSEGS MV 6759728 2) by (apply writable_img; [vm_compute; reflexivity| lia| lia| lia]).
    assert (V2 : L5.writable RSEGS MV (sp - 16) 16).
    { apply (proj2 (L5A.writable_vis H M (sp - 16) 16 (VIS (sp - 16) 16 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]. lia. lia. }
    LeanFeed.pfeed P (PMASYP.asyB_conc fx R MV (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [assumption | exact Rsp | unfold PMASYP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A10 & _ & _ & G1 & G0).
    assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xd9524 W_d6f28 r F_d6f28 eq_refl D_d6f28 R1ra ltac:(lia) Hr2) as MS2.
    apply (PMKA2.apiece_img L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xd950c R1 r M1v
             (fun a => sp - 16 <= a < sp - 16 + 16 \/ 0 + 6759728 <= a < 0 + 6759728 + 2) K HH AM).
    { eapply msteps_trans; [exact MS1| exact MS2]. }
    { exact MG1. }
    { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha [Wa|Wa].
      - split; [|intros X; pose proof (PMA.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - split; [|apply (PMKA2.rt_ro_bss L C a LY); lia]. unfold aclientw, aclient_g. right; right; left.
        rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
        intros [X|X].
        + apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)); [|exact X]. unfold PMST.dep, pm_foot, pm_initc. left.
          exists (0x672530, 0x672532). split; [cbn; tauto| cbn [fst snd]; lia].
        + pose proof (PMA.ly_ro L C LY a X). lia. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    apply (KONT fx1 R1 M1 model1 LK Aw).
    + apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
    + exact A10.
    + unfold PMST.sys_ok. cbn [pa_syscat_guard PMA.AD ADDR_A].
      rewrite <- VIS1 in G0.
      apply (proj1 (L5A.u8_at_vis H M1 6759728 1 (VIMG 6759728 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact G0.
    + change (PMSPA.pm_scr 1) with 14336. cbn [pa_syscat_guard PMA.AD ADDR_A].
      assert (EK : L5SAR.ek L ar LB FF sp 14336 [(6759728, 2)] M M1).
      { apply (L5SAR.ek_piece L ar LB FF sp 14336 [(6759728, 2)] M M1 (fun a => (sp - 16 <= a < sp - 16 + 16) \/ (0 + 6759728 <= a < 0 + 6759728 + 2))).
        { intros a Ha N. apply FR1; [exact Ha| exact N]. }
        intros a Ha Hc Ho [X|X].
        - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 14336 a HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| exfalso; lia].
        - apply (Ho (6759728, 2)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
      apply (L5SAR.ahpres_of L ar LB FF sp 14336 [(6759728, 2)] M M1 EK).
      * intros i Hi. apply MGM1. apply SDEF. exact Hi.
      * apply (L5SAR.dk_grows L ar LB FF sp 14336 M M1 MGM1).
    + exact MRT1.
    + intros x Hx. exact Hx.
    + intros x Hx. exact Hx.
    + exact AM1.
    + exact HH1.
Qed.
End WithHeap.
End PMASY.
