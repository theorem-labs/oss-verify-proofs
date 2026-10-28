(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA HeapIfaceABx
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_rd0c8c_d0cd4_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnAOpnewP_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PMAOPN.
Import L5A. Import L5CA. Import L5CSA. Import L5SAR. Import PMANEWP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Theorem opnew_ok0 : opnew_spec L ar HI.
Proof.
  intros fx R M model K LB FF LK cr A n sp r HH AM HK G10 Hn CR G1 RA G2 G4 STK KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold OPNEW_SCR, MALLOC_SCR in SLO, DSCR.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & _).
  set (H := ahid A model) in *. set (MV := mrestrict H M).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487184 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (Un : U R 10 = n). { apply (U_of R 10 n). rewrite <- r10. exact G10. clear - Hn; lia. }
  assert (W16 : L5.writable RSEGS MV (sp - 16) 16).
  { apply (proj2 (writable_vis H M (sp - 16) 16 (VIS (sp - 16) 16 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. unfold OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (anewA_conc fx R MV (fun j => match j with 2%nat => sp | _ => 0 end)) as P. cbn beta iota in P.
  destruct (P (proj1 SPR) ltac:(rewrite <- r2; exact G2) (proj2 SPR) A16 W16 ltac:(unfold U in Un; rewrite Un; clear - Hn; lia))
    as (fx1 & R1 & M1v & MG1 & FR1 & FZ1 & (MS1 & KS1 & A1 & A2 & A8 & C16 & C8)). clear P.
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R OPNEW R1 0x79818 M1v (fun a => sp - 16 <= a < sp) K HH AM MS1 MG1).
  { intros a Ha Hna. apply FZ1. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  (* [comment removed for export] *)
  pose proof (HAJ.aior_malloc _ _ _ _ _ HIok) as HM. unfold amalloc_spec, amalloc_post in HM. rewrite (aly_segs L C LY), (aly_malloc L C LY), (aly_scr_malloc L C LY) in HM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = sp - 16). { rewrite r2, A2. apply L5.unsigned_lit. clear - SPR; lia. }
  eapply (HM fx1 R1 M1 model1 LB FF LK cr A n K HH1 (proj1 AM1) (proj2 AM1)); clear HM.
  - rewrite r10, (KS1 10%nat) by inl. rewrite <- r10. exact G10.
  - exact Hn.
  - exact CR.
  - rewrite r4, (KS1 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite r1, A1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U2. apply (astack_ok_of_astk L ar C LY M M1 sp OPNEW_SCR 16 4096 STK MGM1). clear; lia. clear; lia. unfold OPNEW_SCR, MALLOC_SCR; clear; lia.
    clear - A16. replace (sp - 16) with (sp + (-1) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
  - exact HK.
  - (* [comment removed for export] *)
    intros R2 M2 model2 A' u HU RP BR BA FA DEFU SHU PRES RT2 IA MI2 HH2.
    rewrite r1, A1. rewrite U2 in PRES.
    pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4 & BR5). unfold app_mem in BR5.
    pose proof (vis_pack L ar C HI LY HIok _ FF LK _ A' M2 model2 HH2) as (HOFF2 & VIS2 & _).
    set (H2 := ahid A' model2) in *. set (MV2 := mrestrict H2 M2).
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    (* [comment removed for export] *)
    assert (CL : forall a, sp - 16 <= a < sp -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ha. unfold MV2. rewrite (mrestrict_visible H2 M2). 2:{ replace a with ((sp - 16) + (a - (sp - 16))) by (clear; lia). apply (VIS2 (sp - 16) 16). clear - SLO; lia. clear - SPR; lia. clear - Ha; lia. }
      rewrite (proj1 PRES a). 2:{ clear - Ha SPR SLO; lia. } 2:{ apply stack_client. clear - Ha SLO SHI SPT; lia. clear - Ha; lia. }
      rewrite <- VIS1. symmetry. apply mrestrict_visible. replace a with ((sp - 16) + (a - (sp - 16))) by (clear; lia). apply (VIS (sp - 16) 16). clear - SLO; lia. clear - SPR; lia. clear - Ha; lia. }
    assert (C8' : L5.u64_at RSEGS MV2 (sp - 8) (U R 1)). { eapply L5C.u64_at_agree. 4: exact C8. intros j Hj. apply CL. clear - Hj; lia. clear - SPR; lia. clear - SPR; lia. }
    assert (C16' : L5.u64_at RSEGS MV2 (sp - 16) (U R 8)). { eapply L5C.u64_at_agree. 4: exact C16. intros j Hj. apply CL. clear - Hj; lia. clear - SPR; lia. clear - SPR; lia. }
    assert (W16' : L5.writable RSEGS MV2 (sp - 16) 16).
    { eapply (L5C.writable_agree RSEGS M1v MV2). intros j Hj. apply CL. clear - Hj; lia. clear - SPR; lia. clear - SPR; lia. eapply L5.writable_grows. exact MG1. exact W16. }
    assert (Uu : U R2 10 = u). { apply (U_of R2 10 u). rewrite <- r10. exact HU. clear - BR0 BR5 Hn; lia. }
    (* [comment removed for export] *)
    pose proof (anewB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 40%nat => U R 1 | 41%nat => U R 8 | _ => 0 end)) as P. cbn beta iota in P.
    destruct (P (proj1 SPR) (UR R 1) (UR R 8) ltac:(rewrite (cs_of_preserved R1 R2 2 RP ltac:(inl)); exact A2) (proj2 SPR) A16 W16'
                ltac:(unfold U in Uu; rewrite Uu; clear - BR0 BR5 Hn; lia) C8' C16')
      as (fx3 & R3 & M3v & MG3 & FR3 & FZ3 & (MS3 & KS3 & B1 & B2 & B8)). clear P.
    assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
    pose proof (ret_to fx3 R3 M3v 0x13037c W_12dd8c r F_12dd8c eq_refl D_12dd8c ltac:(rewrite B1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
    pose proof (msteps_trans _ _ _ _ MS3 RET) as MS4. clear MS3 RET.
    apply (apiece_ro L ar C HI LY HIok _ FF LK _ A' M2 model2 fx1 fx3 R2 0x130354 R3 r M3v K HH2 (conj Hh2 MI2) MS4 MG3 FZ3).
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 EQ3.
    pose proof (mem_eq_of_agree M2 M3 EQ3) as EM. subst M3.
    apply (KONT fx3 R3 M2 model3 A' u).
    + rewrite r10, (KS3 10%nat) by inl. rewrite <- r10. exact HU.
    + apply preserved_by_index. intros k Hk. cbn in Hk.
      destruct Hk as [<-|Hk]. { rewrite B2. rewrite <- r2. symmetry; exact G2. }
      destruct Hk as [<-|Hk]. { rewrite (KS3 3%nat ltac:(inl)), (cs_of_preserved R1 R2 3 RP ltac:(inl)), (KS1 3%nat ltac:(inl)). reflexivity. }
      destruct Hk as [<-|Hk]. { rewrite (KS3 4%nat ltac:(inl)), (cs_of_preserved R1 R2 4 RP ltac:(inl)), (KS1 4%nat ltac:(inl)). reflexivity. }
      destruct Hk as [<-|Hk]. { rewrite B8. unfold U. apply Z_to_bv_bv_unsigned. }
      repeat (destruct Hk as [<-|Hk]; [rewrite KS3 by inl; rewrite (cs_of_preserved R1 R2 _ RP) by inl; rewrite KS1 by inl; reflexivity|]). destruct Hk.
    + (* [comment removed for export] *)
      split. exact BR. split. exact BA. split. exact FA. split. exact DEFU. exact SHU.
    + (* [comment removed for export] *)
      split.
      * intros a (Ha & Hc & _).
        assert (N1 : ~ (sp - 16 <= a < sp)). { destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp OPNEW_SCR a HH SPT Hc) as [X|X]. unfold OPNEW_SCR, MALLOC_SCR in X. clear - X; lia. clear - X SLO; lia. }
        rewrite (proj1 PRES a Ha). apply FRM1. exact Ha. exact N1. eapply aclient_mono. exact Hc. unfold OPNEW_SCR, MALLOC_SCR. clear; intros x Hx; lia.
      * split.
        { unfold OPNEW_SCR, MALLOC_SCR. intros j Hj. destruct (Z_lt_le_dec j 4096) as [Hl|Hg].
          - apply (proj2 PRES). clear - Hj Hl; lia.
          - rewrite (proj1 PRES). apply MGM1. apply DSCR. exact Hj. clear - Hj SPR; lia. apply stack_client. clear - Hj Hg SLO SHI SPT; lia. clear - Hg; lia. }
        intros a Ha Hc D0. destruct (rng_dec a (sp - 16 - 4096) (sp - 16)) as [I|O].
        { apply (proj2 PRES). exact I. }
        rewrite (proj1 PRES a Ha). apply MGM1. exact D0. eapply aclient_mono. exact Hc. unfold OPNEW_SCR, MALLOC_SCR. clear; intros x Hx; lia.
    + eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT3.
    + exact IA.
    + exact AM3.
    + exact HH3.
Qed.

End WithIface.

(* [comment removed for export] *)
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Theorem opnew_ok : PMA.opnew_spec L ar HI.
Proof.
  intros fx R M model K LB FF LK Aw cr n sp r HH AM HK G10 Hn CR G1 RA G2 G4 STK KONT.
  exact (opnew_ok0 L ar C HI (PMA.ly_as0 L C LY) HIok fx R M model K LB FF LK cr Aw n sp r HH AM HK G10 Hn CR G1 RA G2 G4 STK KONT).
Qed.
End WithHeap.
End SCFG_1.
End PMAOPN.
