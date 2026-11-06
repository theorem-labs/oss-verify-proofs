(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BAllocP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5BALC.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5BALCP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

Definition ALLOC : Z := 0x90c88.
Definition alloc_spec (L : asan_layout) (ar : asan_run) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (m sp r : Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 11%bv = Z_to_bv 64 m -> 0 < m -> 8 * m <= 2 ^ 27 -> acredit_ok L cr (8 * m) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)) (q : Z),
        getr R' 10%bv = Z_to_bv 64 q -> regs_preserved R R' ->
        afresh L ar LB (FF ++ LK) M' q (8 * m) ->
        ahpres L ar LB FF sp OPNEW_SCR [] M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI ((q, 8 * m) :: LB) FF LK (adebit L cr (8 * m)) A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R ALLOC M model) K.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Theorem alloc_ok : opnew_spec L ar HI -> alloc_spec L ar HI.
Proof.
  intros NEW fx R M model K LB FF LK cr A m sp r HH AM HK G11 Hm Hm8 CR G1 RA G2 G4 STK KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold OPNEW_SCR, MALLOC_SCR in SLO, DSCR.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & _).
  set (H := ahid A model) in *. set (MV := mrestrict H M).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487184 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (W8 : L5.writable RSEGS MV (sp - 8) 8).
  { apply (proj2 (writable_vis H M (sp - 8) 8 (VIS (sp - 8) 8 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. unfold OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
  pose proof (alcA_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => m | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P (proj1 SPR) ltac:(clear - Hm Hm8; lia) ltac:(rewrite <- r2; exact G2) ltac:(rewrite <- r11; exact G11) (proj2 SPR) A16 W8 ltac:(clear - Hm Hm8; lia))
    as (fx1 & R1 & M1v & MG1 & FR1 & FZ1 & (MS1 & KS1 & A10 & C8)). clear P.
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R ALLOC R1 OPNEW M1v (fun a => sp - 8 <= a < sp) K HH AM MS1 MG1).
  { intros a Ha Hna. apply FZ1. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  apply (NEW fx1 R1 M1 model1 K LB FF LK cr A (8 * m) sp r HH1 AM1 HK).
  - rewrite r10. exact A10.
  - clear - Hm Hm8; lia.
  - exact CR.
  - rewrite r1, (KS1 1%nat) by inl. rewrite <- r1. exact G1.
  - exact RA.
  - rewrite r2, (KS1 2%nat) by inl. rewrite <- r2. exact G2.
  - rewrite r4, (KS1 4%nat) by inl. rewrite <- r4. exact G4.
  - eapply astk_grows. exact STK. exact MGM1.
  - intros fx' R' M' model' A' q Q10 RP FRq AHP RT IA AM' HH'.
    apply (KONT fx' R' M' model' A' q Q10).
    + apply preserved_by_index. intros k Hk. rewrite (cs_of_preserved R1 R' k RP Hk). apply KS1. revert k Hk. apply (L5K.incl_b _ KS_alcA); vm_compute; reflexivity.
    + exact FRq.
    + destruct AHP as (E & D & Kd). apply ahpres_of.
      * eapply ek_trans. 2: exact E. apply (ek_piece L ar LB FF sp OPNEW_SCR [] M M1 _ FRM1). intros a Ha Hc _ X.
        destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp OPNEW_SCR a HH SPT Hc) as [Y|Y].
        unfold OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia.
      * exact D.
      * eapply dk_trans. apply dk_grows. exact MGM1. exact Kd.
    + eapply L5LZ.model_rt_trans. exact RT1. exact RT.
    + exact IA.
    + exact AM'.
    + exact HH'.
Qed.

End WithIface.
End SCFG_1.
End L5BALC.
