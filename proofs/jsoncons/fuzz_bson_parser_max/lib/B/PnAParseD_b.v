(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation Zwf.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcKitA_b PnBrKitA_b PnAParseP_b PnAParseP2_b Ba0_code_ad390_ad394_b PnAParseK_b PnAParseA_b PnAParseB_b PnAParseC_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.


Module PNAPAD.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNAPAK. Import PNAPAA. Import PNAPAB. Import PNAPAC.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pa_arr_end K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (n : Z) M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 :
  PNRAa.end_array_spec L ar HI ->
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  PNAPAA.pa_IH L ar HI K R M model LBX FF LK Aw cr sp fb s str sm ax F (n) ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  lregs R R6 sp fb F -> spill M6 sp F (fb + 464) (fb + 432) (fb + 1024) -> ec_some M6 fb -> PNRA.binv s6 -> PNRA.bb_room s6 sm6 ->
  (2 <= length (PNM.b_stk s6))%nat -> 2 * PM.unread (PNM.b_src s6) sm6 + 1 < n ->
  getr R6 (reg 10) = Z_to_bv 64 1 -> getr R6 (reg 13) = Z_to_bv 64 (F + 48) -> L5.u8_at RSEGS M6 (F + 48) 0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xae2d8 M6 model6) K.
Proof.
  intros ED CTX G IH LM ER SPL ECS INV6 BBR6 LEN6 MU6 X10 X13 LB6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNAPAB.unread_le L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 LM) as (UN0 & UNL).
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (PF & _).
  pose proof (PNAPAA.mfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q36 & Q34 & Q37).
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM SPL) as SPv.
  pose proof (PNAPAC.lbyte_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 48 0 CTX G LM ltac:(clear; lia) LB6) as LBv.
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  pfx PF. spx SPv. pose proof ER as ER'. lrx ER'.
  assert (Q45 : 0 <= 0 < 2 ^ 64) by (clear; lia). assert (Q45r : 0 <= 0 <= 0) by (clear; lia).
  (* [comment removed for export] *)
  pose proof (PNAPAP.apaY4z_conc fx6 R6 MV6 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & Y12 & Y23 & Y24).
  apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xae2d8 0xb1c9c M7v CTX G LM MS7 MG7 FRZ7).
  intros model7 LM7 HID7.
  assert (K7 : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)).
  { intros k Hk. apply KS7. revert k Hk. apply L5K.incl_b. vm_compute. reflexivity. }
  destruct ECS as (e1 & c1 & He1 & EC1).
  change 0xb1c9c with (PNL.pn_end_array PMA.AN).
  apply (PNAPAK.pa_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 0xae3e0 e1 c1 false (PNL.pn_end_array PMA.AN) 3 (PNRA.bargs_end PMA.AD) PNRA.bprog_pop
           ED ltac:(clear; lia) CTX G LM7 INV6 EC1 He1).
  { clear - UNL UNR; lia. }
  { unfold PNRA.bargs_end, PNRA.bargs3, PNRA.o_p, PMSP.o_p, PNRA.o_v, PMSP.o_v, PNRA.o_ec, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [split; [exact Y10|]; split; [exact Y11| exact Y12]| exact LEN6]. }
  { exact Y1. } { unfold L5.ra_ok; clear; lia. } { rewrite (KS7 2%nat) by inl. exact E2. }
  { rewrite (KS7 3%nat) by inl. rewrite E3. exact Rgp. } { rewrite (KS7 4%nat) by inl. rewrite E4. exact Rtp. }
  intros fx8 R8 M8 model8 LK8 Aw8 s8 sm8 ax8 cr8 RP8 LM8 STEP8 AXL8 RES8 BBP8 AG8 AGF8.
  assert (C8 : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R8 (reg k) = getr R7 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R7 R8 k RP8). revert k Hk. apply L5K.incl_b. vm_compute. reflexivity. }
  pose proof E2 as G2. rewrite <- (K7 2%nat), <- (C8 2%nat) in G2 by inl.
  pose proof E3 as G3. rewrite <- (K7 3%nat), <- (C8 3%nat) in G3 by inl.
  pose proof E4 as G4. rewrite <- (K7 4%nat), <- (C8 4%nat) in G4 by inl.
  pose proof E8 as G8. rewrite <- (K7 8%nat), <- (C8 8%nat) in G8 by inl.
  pose proof E9 as G9. rewrite <- (K7 9%nat), <- (C8 9%nat) in G9 by inl.
  pose proof E18 as G18. rewrite <- (K7 18%nat), <- (C8 18%nat) in G18 by inl.
  pose proof E19 as G19. rewrite <- (K7 19%nat), <- (C8 19%nat) in G19 by inl.
  pose proof E20 as G20. rewrite <- (K7 20%nat), <- (C8 20%nat) in G20 by inl.
  pose proof E21 as G21. rewrite <- (K7 21%nat), <- (C8 21%nat) in G21 by inl.
  pose proof E22 as G22. rewrite <- (K7 22%nat), <- (C8 22%nat) in G22 by inl.
  pose proof E25 as G25. rewrite <- (K7 25%nat), <- (C8 25%nat) in G25 by inl.
  pose proof E26 as G26. rewrite <- (K7 26%nat), <- (C8 26%nat) in G26 by inl.
  pose proof E27 as G27. rewrite <- (K7 27%nat), <- (C8 27%nat) in G27 by inl.
  pose proof Y23 as G23. rewrite <- (C8 23%nat) in G23 by inl.
  pose proof Y24 as G24. rewrite <- (C8 24%nat) in G24 by inl.
  assert (SPL8 : spill M8 sp F (fb + 464) (fb + 432) (fb + 1024)).
  { apply (PNAPAK.spill_agree M6 M8 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL|].
    intros a Ha. apply AG8. clear - Ha; lia. }
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 pf33 pf34. clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. clear sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 sv12 sv13. clear Y1 Y10 Y11 Y12 Y23 Y24.
  (* [comment removed for export] *)
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm8 ax8 cr8 CTX G LM8) as (PF & _).
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm8 ax8 cr8 CTX G LM8 SPL8) as SPv.
  set (MV8 := mrestrict (ahid Aw8 model8) M8) in *.
  pfx PF. spx SPv.
  pose proof (PNAPAP.apaYZ_conc fx8 R8 MV8 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _ & _ & Z17 & Z23 & Z24 & _).
  assert (ER9 : lregs R R9 sp fb F).
  { unfold lregs. split; [rewrite (KS9 2%nat) by inl; exact G2|]. split; [rewrite (KS9 3%nat) by inl; exact G3|]. split; [rewrite (KS9 4%nat) by inl; exact G4|]. split; [rewrite (KS9 8%nat) by inl; exact G8|]. split; [rewrite (KS9 9%nat) by inl; exact G9|]. split; [rewrite (KS9 18%nat) by inl; exact G18|]. split; [rewrite (KS9 19%nat) by inl; exact G19|]. split; [rewrite (KS9 20%nat) by inl; exact G20|]. split; [rewrite (KS9 21%nat) by inl; exact G21|]. split; [rewrite (KS9 22%nat) by inl; exact G22|]. split; [exact Z23|]. split; [exact Z24|]. split; [rewrite (KS9 25%nat) by inl; exact G25|]. split; [rewrite (KS9 26%nat) by inl; exact G26|]. rewrite (KS9 27%nat) by inl; exact G27. }
  apply (PNAPAK.pa_piece_sh L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm8 ax8 cr8 fx8 fx9 R8 R9 0xae3e0 0xae3fc M9v
           (fun a => F / 8 + 2147450880 + 6 <= a < F / 8 + 2147450880 + 6 + 1) CTX G LM8 MS9 MG9).
  { intros a Ha N. apply FRZ9; [exact Ha| exact N]. }
  { intros a X. clear - X. lia. }
  intros M10 model10 LM10 HID10 VIS10 FR10 MGM10 ECK10.
  assert (DF1 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - pf15; lia).
  apply (PNAPAA.pa_tail L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 n M10 model10 LK8 Aw8 s8 sm8 ax8 cr8 fx9 R9 CTX G IH LM10); [exact ER9| exact Z17| | |].
  - apply (PNAPAK.spill_agree M8 M10 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL8|].
    intros a Ha. apply FR10; [clear - Ha pf4; lia| clear - Ha pf4 DF1; lia].
  - destruct RES8 as [(v & Hv & Ev & _)|(Ee & _)]; [exists v, (pa_errcat_obj PMA.AD); split; [clear - Hv; lia| exact (ECK10 _ _ Ev)]| exists e1, c1; split; [exact He1| exact (ECK10 _ _ Ee)]].
  - right. destruct STEP8 as (_ & _ & _ & _ & LE8). unfold PNRA.bb_post in BBP8.
    pose proof (PNAPAB.unread_le L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M10 model10 LK8 Aw8 s8 sm8 ax8 cr8 LM10) as (UN8 & _).
    split; [destruct RES8 as [(v & _ & _ & _ & _ & _ & X)|(_ & X & _)]; exact X|].
    split; [intros _; exact (bb_room_keep s6 s8 sm6 sm8 BBP8 LE8 BBR6)|].
    intros MO8. destruct RES8 as [(v & _ & _ & MOv8 & _)|(_ & INV8 & PROG)]; [rewrite MOv8 in MO8; discriminate|].
    destruct PROG as (_ & UEQ). unfold PNRA.bmu. pose proof (bflag_range (PNM.b_stk s8)) as FR8. clear - UEQ FR8 UN8 MU6 UN0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pa_arr_name K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (n : Z) M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 (t : Z) :
  PNRAa.read_e_name_spec L ar HI -> PNRAa.read_value_spec L ar HI ->
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  PNAPAA.pa_IH L ar HI K R M model LBX FF LK Aw cr sp fb s str sm ax F (n) ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  lregs R R6 sp fb F -> spill M6 sp F (fb + 464) (fb + 432) (fb + 1024) -> ec_some M6 fb -> PNRA.binv s6 -> PNRA.bb_room s6 sm6 ->
  (2 <= length (PNM.b_stk s6))%nat -> 2 * PM.unread (PNM.b_src s6) sm6 + 1 < n ->
  getr R6 (reg 10) = Z_to_bv 64 1 -> getr R6 (reg 13) = Z_to_bv 64 (F + 48) -> L5.u8_at RSEGS M6 (F + 48) t -> 1 <= t <= 255 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xae2d8 M6 model6) K.
Proof.
  intros REN RV CTX G IH LM ER SPL ECS INV6 BBR6 LEN6 MU6 X10 X13 LB6 Ht.
  pose proof CTX as (_ & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNAPAB.unread_le L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 LM) as (UN0 & UNL).
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (PF & _).
  pose proof (PNAPAA.mfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q36 & Q34 & Q37).
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM SPL) as SPv.
  pose proof (PNAPAC.lbyte_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 48 t CTX G LM ltac:(clear; lia) LB6) as LBv.
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  pfx PF. spx SPv. pose proof ER as ER'. lrx ER'.
  assert (Q45 : 0 <= t < 2 ^ 64) by (clear - Ht; lia).
  (* [comment removed for export] *)
  pose proof (PNAPAP.apaY4n_conc fx6 R6 MV6 (vmx R sp fb F fl 0 0 0 0 0 t 0 0)) as P.
  pfeed P.
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & Y12 & Y13 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27).
  apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xae2d8 0xaf548 M7v CTX G LM MS7 MG7 FRZ7).
  intros model7 LM7 HID7.
  assert (K7 : forall k, In k [2; 3; 4; 8; 9; 18; 20; 21; 25; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)).
  { intros k Hk. apply KS7. revert k Hk. apply L5K.incl_b. vm_compute. reflexivity. }
  destruct ECS as (e1 & c1 & He1 & EC1).
  change 0xaf548 with (PNL.pn_read_e_name PMA.AN).
  apply (PNAPAK.pa_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 0xae310 e1 c1 false (PNL.pn_read_e_name PMA.AN) 6 (PNRA.bargs_en PMA.AD) PNRA.bprog_name
           REN ltac:(clear; lia) CTX G LM7 INV6 EC1 He1).
  { clear - UNL UNR; lia. }
  { unfold PNRA.bargs_en, PNRA.o_p, PMSP.o_p, PNRA.o_v, PMSP.o_v, PNRA.o_ec, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12, L5K.rl13. split; [exact Y10|]. split; [exact Y11|]. split; [exact Y13|]. right. exact Y12. }
  { exact Y1. } { unfold L5.ra_ok; clear; lia. } { rewrite (K7 2%nat) by inl. exact E2. }
  { rewrite (K7 3%nat) by inl. rewrite E3. exact Rgp. } { rewrite (K7 4%nat) by inl. rewrite E4. exact Rtp. }
  intros fx8 R8 M8 model8 LK8 Aw8 s8 sm8 ax8 cr8 RP8 LM8 STEP8 AXL8 RES8 BBP8 AG8 AGF8.
  assert (C8 : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R8 (reg k) = getr R7 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R7 R8 k RP8). revert k Hk. apply L5K.incl_b. vm_compute. reflexivity. }
  assert (SPL8 : spill M8 sp F (fb + 464) (fb + 432) (fb + 1024)).
  { apply (PNAPAK.spill_agree M6 M8 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL|].
    intros a Ha. apply AG8. clear - Ha; lia. }
  assert (LB8 : L5.u8_at RSEGS M8 (F + 48) t).
  { apply (L5C.u8_at_agree RSEGS M6 M8); [| clear - pf15; lia| clear - pf15; lia| exact LB6]. intros j Hj. apply AGF8. clear - Hj; lia. }
  destruct STEP8 as (_ & _ & _ & _ & LE8). unfold PNRA.bb_post in BBP8.
  assert (INV8 : PNRA.binv s8) by (destruct RES8 as [(v & _ & _ & _ & _ & _ & X)|(_ & X & _)]; exact X).
  assert (ECS8 : ec_some M8 fb).
  { destruct RES8 as [(v & Hv & Ev & _)|(Ee & _)]; [exists v, (pa_errcat_obj PMA.AD); split; [clear - Hv; lia| exact Ev]| exists e1, c1; split; [exact He1| exact Ee]]. }
  clear RES8.
  pose proof (bb_room_keep s6 s8 sm6 sm8 BBP8 LE8 BBR6) as BBR8.
  (* [comment removed for export] *)
  assert (G2 : getr R8 (reg 2) = Z_to_bv 64 (sp - 256)) by (rewrite (C8 2%nat) by inl; rewrite (K7 2%nat) by inl; exact E2).
  assert (G3 : getr R8 (reg 3) = getr R (reg 3)) by (rewrite (C8 3%nat) by inl; rewrite (K7 3%nat) by inl; exact E3).
  assert (G4 : getr R8 (reg 4) = getr R (reg 4)) by (rewrite (C8 4%nat) by inl; rewrite (K7 4%nat) by inl; exact E4).
  assert (G8 : getr R8 (reg 8) = Z_to_bv 64 sp) by (rewrite (C8 8%nat) by inl; rewrite (K7 8%nat) by inl; exact E8).
  assert (G9 : getr R8 (reg 9) = Z_to_bv 64 (sp - 256)) by (rewrite (C8 9%nat) by inl; rewrite (K7 9%nat) by inl; exact E9).
  pose proof E18 as G18. rewrite <- (K7 18%nat), <- (C8 18%nat) in G18 by inl.
  pose proof Y19 as G19. rewrite <- (C8 19%nat) in G19 by inl.
  pose proof Y20 as G20. rewrite <- (C8 20%nat) in G20 by inl.
  pose proof Y21 as G21. rewrite <- (C8 21%nat) in G21 by inl.
  pose proof Y22 as G22. rewrite <- (C8 22%nat) in G22 by inl.
  pose proof Y23 as G23. rewrite <- (C8 23%nat) in G23 by inl.
  pose proof Y24 as G24. rewrite <- (C8 24%nat) in G24 by inl.
  pose proof Y25 as G25. rewrite <- (C8 25%nat) in G25 by inl.
  pose proof Y26 as G26. rewrite <- (C8 26%nat) in G26 by inl.
  pose proof Y27 as G27. rewrite <- (C8 27%nat) in G27 by inl.
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 pf33 pf34. clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. clear sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 sv12 sv13.
  clear Y1 Y10 Y11 Y12 Y13 Y19 Y20 Y21 Y22 Y23 Y24 Y25 Y26 Y27.
  (* [comment removed for export] *)
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm8 ax8 cr8 CTX G LM8) as (PF & _).
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm8 ax8 cr8 CTX G LM8 SPL8) as SPv.
  pose proof (PNAPAC.lbyte_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm8 ax8 cr8 48 t CTX G LM8 ltac:(clear; lia) LB8) as LBv8.
  set (MV8 := mrestrict (ahid Aw8 model8) M8) in *.
  pfx PF. spx SPv.
  assert (Q45r : 0 <= t <= 255) by (clear - Ht; lia).
  pose proof (PNAPAP.apaY5_conc fx8 R8 MV8 (vmx R sp fb F fl 0 0 0 0 0 t 0 0)) as P.
  pfeed P.
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z1 & Z10 & Z11 & Z12 & Z13 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
  apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm8 ax8 cr8 fx8 fx9 R8 R9 0xae310 0xaff88 M9v CTX G LM8 MS9 MG9 FRZ9).
  intros model9 LM9 HID9.
  assert (K9 : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 27]%nat -> getr R9 (reg k) = getr R8 (reg k)).
  { intros k Hk. apply KS9. revert k Hk. apply L5K.incl_b. vm_compute. reflexivity. }
  destruct ECS8 as (e8 & k8 & He8 & EC8).
  pose proof (PNAPAB.unread_le L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M8 model9 LK8 Aw8 s8 sm8 ax8 cr8 LM9) as (UN8 & UNL8).
  change 0xaff88 with (PNL.pn_read_value PMA.AN).
  apply (PNAPAK.pa_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model9 LK8 Aw8 s8 sm8 ax8 cr8 fx9 R9 0xae32c e8 k8 true (PNL.pn_read_value PMA.AN) 8 (PNRA.bargs_rv PMA.AD) PNRA.bprog_value
           RV ltac:(clear; lia) CTX G LM9 INV8 EC8 He8).
  { clear - UNL8 UNR; lia. }
  { unfold PNRA.bargs_rv, PNRA.o_p, PMSP.o_p, PNRA.o_v, PMSP.o_v, PNRA.o_ec, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12, L5K.rl13. split; [exact Z10|]. split; [exact Z11|]. split; [exact Z13|].
    split; [exists t; split; [clear - Ht; lia| exact Z12]| exact BBR8]. }
  { exact Z1. } { unfold L5.ra_ok; clear; lia. } { rewrite (K9 2%nat) by inl. exact G2. }
  { rewrite (K9 3%nat) by inl. rewrite G3. exact Rgp. } { rewrite (K9 4%nat) by inl. rewrite G4. exact Rtp. }
  intros fx10 R10 M10 model10 LK10 Aw10 s10 sm10 ax10 cr10 RP10 LM10 STEP10 AXL10 RES10 BBP10 AG10 AGF10.
  assert (C10 : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R10 (reg k) = getr R9 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R9 R10 k RP10). revert k Hk. apply L5K.incl_b. vm_compute. reflexivity. }
  pose proof G2 as H2. rewrite <- (K9 2%nat), <- (C10 2%nat) in H2 by inl.
  pose proof G3 as H3. rewrite <- (K9 3%nat), <- (C10 3%nat) in H3 by inl.
  pose proof G4 as H4. rewrite <- (K9 4%nat), <- (C10 4%nat) in H4 by inl.
  pose proof G8 as H8. rewrite <- (K9 8%nat), <- (C10 8%nat) in H8 by inl.
  pose proof G9 as H9. rewrite <- (K9 9%nat), <- (C10 9%nat) in H9 by inl.
  pose proof G18 as H18. rewrite <- (K9 18%nat), <- (C10 18%nat) in H18 by inl.
  pose proof Z19 as H19. rewrite <- (C10 19%nat) in H19 by inl.
  pose proof Z20 as H20. rewrite <- (C10 20%nat) in H20 by inl.
  pose proof Z21 as H21. rewrite <- (C10 21%nat) in H21 by inl.
  pose proof Z22 as H22. rewrite <- (C10 22%nat) in H22 by inl.
  pose proof Z23 as H23. rewrite <- (C10 23%nat) in H23 by inl.
  pose proof Z24 as H24. rewrite <- (C10 24%nat) in H24 by inl.
  pose proof Z25 as H25. rewrite <- (C10 25%nat) in H25 by inl.
  pose proof Z26 as H26. rewrite <- (C10 26%nat) in H26 by inl.
  pose proof Z27 as H27. rewrite <- (C10 27%nat) in H27 by inl.
  assert (SPL10 : spill M10 sp F (fb + 464) (fb + 432) (fb + 1024)).
  { apply (PNAPAK.spill_agree M8 M10 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL8|].
    intros a Ha. apply AG10. clear - Ha; lia. }
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 pf33 pf34. clear sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 sv12 sv13. clear G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27. clear Z1 Z10 Z11 Z12 Z13 Z19 Z20 Z21 Z22 Z23 Z24 Z25 Z26 Z27.
  (* [comment removed for export] *)
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M10 model10 LK10 Aw10 s10 sm10 ax10 cr10 CTX G LM10) as (PF & _).
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M10 model10 LK10 Aw10 s10 sm10 ax10 cr10 CTX G LM10 SPL10) as SPv.
  set (MV10 := mrestrict (ahid Aw10 model10) M10) in *.
  pfx PF. spx SPv.
  pose proof (PNAPAP.apaY6_conc fx10 R10 MV10 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx11 & R11 & M11v & MG11 & _ & FRZ11 & MS11 & KS11 & _ & _ & V17 & V19 & V23 & V24 & _).
  assert (ER11 : lregs R R11 sp fb F).
  { unfold lregs. split; [rewrite (KS11 2%nat) by inl; exact H2|]. split; [rewrite (KS11 3%nat) by inl; exact H3|]. split; [rewrite (KS11 4%nat) by inl; exact H4|]. split; [rewrite (KS11 8%nat) by inl; exact H8|]. split; [rewrite (KS11 9%nat) by inl; exact H9|]. split; [rewrite (KS11 18%nat) by inl; exact H18|]. split; [exact V19|]. split; [rewrite (KS11 20%nat) by inl; exact H20|]. split; [rewrite (KS11 21%nat) by inl; exact H21|]. split; [rewrite (KS11 22%nat) by inl; exact H22|]. split; [exact V23|]. split; [exact V24|]. split; [rewrite (KS11 25%nat) by inl; exact H25|]. split; [rewrite (KS11 26%nat) by inl; exact H26|]. rewrite (KS11 27%nat) by inl; exact H27. }
  apply (PNAPAK.pa_piece_sh L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M10 model10 LK10 Aw10 s10 sm10 ax10 cr10 fx10 fx11 R10 R11 0xae32c 0xae3fc M11v
           (fun a => F / 8 + 2147450880 + 6 <= a < F / 8 + 2147450880 + 6 + 1) CTX G LM10 MS11 MG11).
  { intros a Ha N. apply FRZ11; [exact Ha| exact N]. }
  { intros a X. clear - X. lia. }
  intros M12 model12 LM12 HID12 VIS12 FR12 MGM12 ECK12.
  assert (DF1 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - pf15; lia).
  apply (PNAPAA.pa_tail L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 n M12 model12 LK10 Aw10 s10 sm10 ax10 cr10 fx11 R11 CTX G IH LM12); [exact ER11| exact V17| | |].
  - apply (PNAPAK.spill_agree M10 M12 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL10|].
    intros a Ha. apply FR12; [clear - Ha pf4; lia| clear - Ha pf4 DF1; lia].
  - destruct RES10 as [(v & Hv & Ev & _)|(Ee & _)]; [exists v, (pa_errcat_obj PMA.AD); split; [clear - Hv; lia| exact (ECK12 _ _ Ev)]| exists e8, k8; split; [exact He8| exact (ECK12 _ _ Ee)]].
  - right. destruct STEP10 as (_ & _ & _ & _ & LE10). unfold PNRA.bb_post in BBP10.
    pose proof (PNAPAB.unread_le L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M12 model12 LK10 Aw10 s10 sm10 ax10 cr10 LM12) as (UN10 & _).
    split; [destruct RES10 as [(v & _ & _ & _ & _ & _ & X)|(_ & X & _)]; exact X|].
    split; [intros MO10; exact (BBP10 BBR8 MO10)|].
    intros MO10. unfold PNRA.bmu. pose proof (bflag_range (PNM.b_stk s10)) as FR10. clear - LE10 LE8 FR10 UN10 MU6. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pa_arr K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 l c :
  PNRAa.src_read_spec L ar HI -> PNRAa.make_ec_spec L ar HI -> PNRAa.end_array_spec L ar HI -> PNRAa.read_e_name_spec L ar HI -> PNRAa.read_value_spec L ar HI ->
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  PNAPAA.pa_IH L ar HI K R M model LBX FF LK Aw cr sp fb s str sm ax F (PNRA.bmu s1 sm1) ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  lregs R R1 sp fb F -> getr R1 (reg 17) = Z_to_bv 64 (fb + 464 + 8) -> spill M1 sp F (fb + 464) (fb + 432) (fb + 1024) -> ec_some M1 fb -> PNRA.binv s1 ->
  PNRA.bb_room s1 sm1 -> PNM.b_more s1 = 1 -> PNM.b_stk s1 = l ++ [c] -> PNM.bs_mode c = 3 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xae0cc M1 model1) K.
Proof.
  intros SR MKE ED REN RV CTX G IH LM ER X17 SPL ECS INV1 BBR1 MO1 ES Hm.
  pose proof CTX as (_ & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof G as G'. unfold pa_frame in G'. destruct G' as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GF8 _ _ _ _ _ _ _].
  change (ff_bytes 1) with 128 in GF8.
  pose proof (PNAPAB.unread_le L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 LM) as (UN0 & UNL).
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (PF & _).
  pose proof (PNAPAA.mfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (MOv & _ & _ & _ & _ & _ & _ & _ & _ & Q36 & Q34 & Q37).
  rewrite MO1 in MOv.
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM SPL) as SPv.
  pose proof (PNAPAK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 l c CTX G LM INV1 ES) as (TF & PT & OKc & VIN & TB1 & TB2 & TB3 & TB4).
  pose proof (PNAPAA.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 l c CTX G LM INV1 ES) as HF.
  rewrite Hm in HF.
  pose proof INV1 as (DN1 & SH1). rewrite ES in SH1.
  pose proof (shape_cont_cons l c SH1 ltac:(right; left; exact Hm)) as NNIL.
  assert (LEN1 : (2 <= length (l ++ [c]))%nat) by (rewrite length_app; cbn [length]; destruct l; [destruct (NNIL eq_refl)| cbn [length]; clear; lia]).
  set (MV1 := mrestrict (ahid Aw1 model1) M1) in *.
  set (b := PNM.b_sb s1) in *. set (n := Z.of_nat (length l)) in *.
  pfx PF. spx SPv. tfx TF. hfx HF. pose proof ER as ER'. lrx ER'.
  assert (Q40r : 3 <= 3 <= 3) by (clear; lia).
  assert (DF1 : 863232 <= F / 8) by (apply Z.div_le_lower_bound; clear - pf15; lia).
  assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - pf15; lia).
  (* [comment removed for export] *)
  pose proof (PNAPAP.apaH3_conc fx1 R1 MV1 (vmx R sp fb F fl 3 0 (b + 40 * n + 40) 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _ & _ & H12 & _ & H14 & H15).
  apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 fx2 R1 R2 0xae0cc 0xae27c M2v CTX G LM MS2 MG2 FRZ2).
  intros model2' LM2 HID2.
  assert (ER2 : lregs R R2 sp fb F) by (lrk ER KS2).
  assert (X17b : getr R2 (reg 17) = Z_to_bv 64 (fb + 464 + 8)) by (rewrite (KS2 17%nat) by inl; exact X17).
  assert (MVE : mrestrict (ahid Aw1 model2') M1 = MV1) by (unfold MV1; rewrite HID2; reflexivity).
  clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. pose proof ER2 as ER2'. lrx ER2'.
  (* [comment removed for export] *)
  pose proof (PNAPAP.apaY1_conc fx2 R2 MV1 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
  pfeed P.
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10 & Z11 & Z12 & SH3).
  rewrite <- MVE in MS3, MG3, FRZ3.
  apply (PNAPAK.pa_piece_sh L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model2' LK1 Aw1 s1 sm1 ax1 cr1 fx2 fx3 R2 R3 0xae27c 0xaed4c M3v
           (fun a => F / 8 + 2147450880 + 6 <= a < F / 8 + 2147450880 + 6 + 1) CTX G LM2 MS3 MG3).
  { intros a Ha N. apply FRZ3; [exact Ha| exact N]. }
  { intros a X. clear - X. lia. }
  intros M3 model3 LM3 HID3 VIS3 FR3 MGM3 ECK3.
  assert (SH3m : L5.u8_at RSEGS M3 (F / 8 + 2147450880 + 48 / 8) 1).
  { change (48 / 8) with 6. apply (PNAPAC.shbyte_of_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK1 Aw1 s1 sm1 ax1 cr1 6 1 CTX G LM3 ltac:(clear; lia)).
    rewrite HID3, VIS3. replace (F / 8 + 2147450880 + 6) with (F / 8 + 2147450886) by (clear; lia). exact SH3. }
  pose proof (aacc_sh M3 F 48 1 (proj1 GF8) pf15 ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia) SH3m) as ACC32.
  assert (ER3 : lregs R R3 sp fb F) by (lrk ER2 KS3).
  assert (SPL3 : spill M3 sp F (fb + 464) (fb + 432) (fb + 1024)).
  { apply (PNAPAK.spill_agree M1 M3 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL|].
    intros a Ha. apply FR3; [clear - Ha pf4; lia| clear - Ha pf4 DF2; lia]. }
  change 0xaed4c with (pa_src_read PMA.AD).
  apply (PNAPAK.pa_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK1 Aw1 s1 sm1 ax1 cr1 fx3 R3 0xae294 48 1 SR CTX G LM3
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ACC32 Z1).
  { unfold L5.ra_ok; clear; lia. } { rewrite (KS3 2%nat) by inl. exact E2. }
  { rewrite (KS3 3%nat) by inl. rewrite E3. exact Rgp. } { rewrite (KS3 4%nat) by inl. rewrite E4. exact Rtp. }
  { exact Z10. } { exact Z11. } { exact Z12. }
  intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 d RP4 Y10d Hd UNR4 RD1 RD0 DEF4 QC4 LM4 AG4 ECK4 DKB4.
  set (s4 := PNM.with_srcB s1 src4) in *.
  assert (INV4 : PNRA.binv s4) by exact INV1.
  assert (ES4 : PNM.b_stk s4 = l ++ [c]) by exact ES.
  pose proof (lregs_pres R R3 R4 sp fb F ER3 RP4) as ER4.
  assert (SPL4 : spill M4 sp F (fb + 464) (fb + 432) (fb + 1024)).
  { apply (PNAPAK.spill_agree M3 M4 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL3|].
    intros a Ha. apply AG4. clear - Ha; lia. }
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 pf33 pf34. clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. clear sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 sv12 sv13. clear tf1 tf2 tf3 tf4 tf5 tf6 tf7 tf8 tf9 tf10 tf11 tf12 tf13 tf14. clear hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9.
  clear PT TB1 TB2 TB3 TB4 VIN.
  (* [comment removed for export] *)
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm4 ax1 cr1 CTX G LM4) as (PF & _).
  pose proof (PNAPAA.spill_vis L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm4 ax1 cr1 CTX G LM4 SPL4) as SPv.
  pose proof (PNAPAK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm4 ax1 cr1 l c CTX G LM4 INV4 ES4) as (TF & PT & _ & VIN & TB1 & TB2 & TB3 & TB4).
  pose proof (PNAPAA.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm4 ax1 cr1 l c CTX G LM4 INV4 ES4) as HF.
  unfold s4 in TF, HF, PT, TB1, TB2, TB3, TB4. cbn [PNM.with_srcB PNM.b_sb PNM.b_sk] in TF, HF, PT, TB1, TB2, TB3, TB4. fold b n in TF, HF, PT, TB1, TB2, TB3, TB4.
  set (MV4 := mrestrict (ahid Aw4 model4) M4) in *.
  pfx PF. spx SPv. tfx TF. hfx HF. pose proof ER4 as ER4'. lrx ER4'.
  assert (Q46 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  pose proof (PNAPAP.apaY2_conc fx4 R4 MV4 (vmx R sp fb F fl (PNM.bs_mode c) 0 (b + 40 * n + 40) (PNM.bs_pos c) 0 0 d 0)) as P.
  pfeed P.
  destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & W11 & W12 & W13).
  apply (PNAPAA.pa_piece_reg L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm4 ax1 cr1 fx4 fx5 R4 R5 0xae294 0xae2d4 M5v CTX G LM4 MS5 MG5 FRZ5).
  intros model5 LM5 HID5.
  assert (ER5 : lregs R R5 sp fb F) by (lrk ER4 KS5).
  assert (MVE5 : mrestrict (ahid Aw4 model5) M4 = MV4) by (unfold MV4; rewrite HID5; reflexivity).
  assert (W10 : getr R5 (reg 10) = Z_to_bv 64 d) by (rewrite (KS5 10%nat) by inl; exact Y10d).
  clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. pose proof ER5 as ER5'. lrx ER5'.
  (* [comment removed for export] *)
  set (pos' := (PNM.bs_pos c + d) mod 2 ^ 64).
  assert (Hp' : 0 <= pos' < 2 ^ 64) by (unfold pos'; apply Z.mod_pos_bound; clear; lia).
  assert (Q49 : 0 <= pos' <= 18446744073709551615) by (clear - Hp'; lia).
  assert (W12' : getr R5 (reg 12) = Z_to_bv 64 pos') by (unfold pos'; rewrite zb_mod64; exact W12).
  pose proof (PNAPAP.apaY3_conc fx5 R5 MV4 (vmx R sp fb F fl (PNM.bs_mode c) 0 (b + 40 * n + 40) (PNM.bs_pos c) 0 0 d pos')) as P.
  pfeed P.
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & U6).
  rewrite <- MVE5 in MS6, MG6, FRZ6.
  apply (PNAPAK.pa_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model5 LK4 Aw4 s4 sm4 ax1 cr1 fx5 fx6 R5 R6 0xae2d4 0xae2d8 M6v l c pos' CTX G LM5 INV4 ES4 MS6 MG6).
  { unfold s4. cbn [PNM.with_srcB PNM.b_sb]. fold b n. exact FRZ6. }
  { unfold s4. cbn [PNM.with_srcB PNM.b_sb]. fold b n. exact U6. }
  { exact Hp'. }
  intros M6 model6 LM6 HID6 VIS6 FR6 MGM6 ECK6.
  unfold s4 in FR6. cbn [PNM.with_srcB PNM.b_sb] in FR6. fold b n in FR6.
  set (c' := PNM.BS (PNM.bs_mode c) (PNM.bs_len c) pos' (PNM.bs_type c) (PNM.bs_idx c)) in *.
  set (s6 := PNBO.set_stk s4 (l ++ [c'])) in *.
  pose proof OKc as (OKm & OKl & OKp & OKt & OKi).
  assert (OKc' : PNM.bstate_ok c') by (unfold PNM.bstate_ok, c'; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; repeat split; first [apply OKm | apply OKl | apply Hp' | apply OKt | apply OKi]).
  assert (INV6 : PNRA.binv s6) by (apply (PNBKA.binv_set_stk_top s4 l c c' INV4 ES4 OKc' eq_refl)).
  assert (ER6 : lregs R R6 sp fb F) by (lrk ER5 KS6).
  assert (X10 : getr R6 (reg 10) = Z_to_bv 64 d) by (rewrite (KS6 10%nat) by inl; exact W10).
  assert (X13 : getr R6 (reg 13) = Z_to_bv 64 (F + 48)) by (rewrite (KS6 13%nat) by inl; exact W13).
  assert (SPL6 : spill M6 sp F (fb + 464) (fb + 432) (fb + 1024)).
  { apply (PNAPAK.spill_agree M4 M6 sp F (fb + 464) (fb + 432) (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL4|].
    intros a Ha. apply FR6; [clear - Ha pf4; lia| clear - Ha tf9; lia]. }
  assert (ECS6 : ec_some M6 fb) by (destruct ECS as (e1 & c1 & He1 & EC1); exists e1, c1; split; [exact He1| exact (ECK6 _ _ (ECK4 _ _ (ECK3 _ _ EC1)))]).
  assert (UN6 : PM.unread (PNM.b_src s6) sm4 = PM.unread (PNM.b_src s1) sm1 - d) by exact UNR4.
  assert (BBR6 : PNRA.bb_room s6 sm4) by (apply (bb_room_keep s1 s6 sm1 sm4); [reflexivity| rewrite UN6; clear - Hd; lia| exact BBR1]).
  assert (LEN6 : (2 <= length (PNM.b_stk s6))%nat) by (unfold s6; cbn [PNBO.set_stk PNM.b_stk]; rewrite length_app in *; exact LEN1).
  assert (BMU1 : PNRA.bmu s1 sm1 = 2 * PM.unread (PNM.b_src s1) sm1) by (unfold PNRA.bmu; rewrite ES, bflag_app, Hm; cbn [Z.eqb Pos.eqb orb]; clear; lia).
  destruct (Z.eq_dec d 0) as [D0|DN0].
  - (* [comment removed for export] *)
    rewrite D0 in X10.
    apply (PNAPAC.pa_err_arm L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK4 Aw4 s6 sm4 ax1 cr1 fx6 R6 0xae2d8 0xae4c8 6 MKE CTX G LM6 ER6 SPL6 ECS6 ltac:(unfold L5.ra_ok; clear; lia) ltac:(right; reflexivity)); [| | exact X10].
    + clear - X13. intros fx Rx Mx ERx X13x PFx SPx Q36 Q34 X10. rewrite X13 in X13x. pfx PFx. spx SPx. lrx ERx.
      pose proof (PNAPAP.apaY4e_conc fx Rx Mx (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
      pfeed P.
      destruct P as (fx' & R' & M' & MG & _ & FRZ & MS & KS & Y1 & Y10 & Y11).
      exists fx', R', M'. split; [exact MG|]. split; [exact FRZ|]. split; [exact MS|].
      split; [intros x Hx; apply KS; revert x Hx; apply L5K.incl_b; vm_compute; reflexivity|]. split; [exact Y1|]. split; [exact Y10| exact Y11].
    + clear. intros fx Rx Mx ERx PFx SPx Q36 Q34 WR1. pfx PFx. spx SPx. lrx ERx.
      pose proof (PNAPAP.apaYE_conc fx Rx Mx (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) as P.
      pfeed P.
      destruct P as (fx' & R' & M' & MG & _ & FRZ & MS & KS & _ & _ & MO).
      exists fx', R', M'. split; [exact MG|]. split; [exact FRZ|]. split; [exact MS|].
      split; [intros x Hx; apply KS; revert x Hx; apply L5K.incl_b; vm_compute; reflexivity| exact MO].
  - (* [comment removed for export] *)
    assert (D1 : d = 1) by (clear - Hd DN0; lia). subst d.
    destruct (PMCG.u8_of_defined RSEGS M4 (F + 48) ltac:(clear - pf15; lia) ltac:(clear - pf15; lia) DEF4) as (t & Ht & LB4).
    assert (LB6 : L5.u8_at RSEGS M6 (F + 48) t).
    { apply (L5C.u8_at_agree RSEGS M4 M6); [| clear - pf15; lia| clear - pf15; lia| exact LB4]. intros j Hj. apply FR6; [clear - Hj pf15; lia| clear - Hj tf11; lia]. }
    assert (MU6 : 2 * PM.unread (PNM.b_src s6) sm4 + 1 < PNRA.bmu s1 sm1) by (rewrite BMU1, UN6; clear; lia).
    destruct (Z.eq_dec t 0) as [T0|TN0].
    + rewrite T0 in LB6.
      exact (pa_arr_end K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (PNRA.bmu s1 sm1) M6 model6 LK4 Aw4 s6 sm4 ax1 cr1 fx6 R6 ED CTX G IH LM6 ER6 SPL6 ECS6 INV6 BBR6 LEN6 MU6 X10 X13 LB6).
    + exact (pa_arr_name K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (PNRA.bmu s1 sm1) M6 model6 LK4 Aw4 s6 sm4 ax1 cr1 fx6 R6 t REN RV CTX G IH LM6 ER6 SPL6 ECS6 INV6 BBR6 LEN6 MU6 X10 X13 LB6 ltac:(clear - Ht TN0; lia)).
Qed.
End WithHeap.
End PNAPAD.
