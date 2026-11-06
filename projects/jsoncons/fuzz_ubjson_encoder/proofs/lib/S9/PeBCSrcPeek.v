(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PeStepAB0 PmStep PmParStep PeBSrcKitJ PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeBCBytes PeBPeekP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_b8704_b8708 Eb0_code_b8720_b8724.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PECPEEKB.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.

Lemma peek_tail (fx1 : FPState) R1 M1 model1 K LB FF LK cr Aw (sp scr a : Z) (w1 w8 w9 w18 w19 : word) :
  ri_inv HI LB FF LK cr Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> PMSTA.base_okA RSEGS PeCLayoutB.CADDR_B M1 ->
  L5CA.astk ar M1 sp scr -> 48 <= scr ->
  getr R1 (reg 2) = Z_to_bv 64 (sp - 48) -> getr R1 (reg 10) = Z_to_bv 64 a -> 0 <= a < 2 ^ 63 ->
  L5.defined (mrestrict (ahid Aw model1) M1) a 1 ->
  L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned w1) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned w8) -> L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned w9) ->
  L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned w18) -> L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned w19) ->
  (forall (fx3 : FPState) R3 model3 b, 0 <= b < 256 -> getr R3 (reg 10) = Z_to_bv 64 b -> L5.u8_at RSEGS M1 a b ->
      getr R3 (reg 1) = w1 -> getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 8) = w8 -> getr R3 (reg 9) = w9 -> getr R3 (reg 18) = w18 -> getr R3 (reg 19) = w19 ->
      (forall k, In k [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k) = getr R1 (reg k)) ->
      model_rt model1 model3 -> L5CA.amodel_ok Aw model3 -> ri_inv HI LB FF LK cr Aw M1 (vml_of model3) -> ahid Aw model3 = ahid Aw model1 ->
      srealizes RSEGS SCFG (L5A.cfg (fx := fx3) R3 0xb8770 M1 model3) K) ->
  srealizes RSEGS SCFG (L5A.cfg (fx := fx1) R1 0xb8754 M1 model1) K.
Proof.
  intros HH AM BASE ASTK Hscr R2 R10 Ha D C8 C16 C24 C32 C40 KONT.
  set (MV := mrestrict (ahid Aw model1) M1) in *.
  destruct (PMPX.lbu_run RSEGS fx1 R1 MV 0xb8754 W_b8704 10%bv 10%bv 0%bv a F_b8704 eq_refl D_b8704) as (b & Hb & U8 & MSb).
  { intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate E. }
  { lia. } { lia. } { rewrite L5K.rl10. exact R10. } { lia. }
  { change (bv_signed (0%bv : bv 12)) with 0. lia. } { change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. exact D. }
  change (0xb8754 + 4) with 0xb8758 in MSb. rewrite L5K.rl10 in MSb.
  assert (U8M : L5.u8_at RSEGS M1 a b).
  { change (bv_signed (0%bv : bv 12)) with 0 in U8. rewrite Z.add_0_r in U8.
    assert (NZ : MV (Z_to_bv 64 a) <> None) by (pose proof (D 0 ltac:(lia)) as D0; rewrite Z.add_0_r in D0; exact D0).
    apply (PECBB.u8_copy MV M1 a a b); [| exact NZ| exact U8].
    unfold MV, mrestrict in NZ |- *. destruct (ahid Aw model1 (Z_to_bv 64 a)); [exfalso; apply NZ; reflexivity| reflexivity]. }
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw M1 model1 fx1 fx1 R1 0xb8754 _ 0xb8758 MV K HH AM MSb (fun _ X => X) (fun _ _ => eq_refl)).
  intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2.
  assert (E21 : M2 = M1) by (apply L5SAR.mem_eq_of_agree; exact FR2). subst M2.
  set (R2' := regupd R1 (reg 10) (Z_to_bv 64 b)) in *.
  assert (O : forall k, k <> 10%nat -> (k < 32)%nat -> getr R2' (reg k) = getr R1 (reg k)) by (intros k N Hk; apply PMPX.regupd_other_idx; lia).
  pose proof (bv_unsigned_in_range 64 w1) as B1. pose proof (bv_unsigned_in_range 64 w8) as B8. pose proof (bv_unsigned_in_range 64 w9) as B9.
  pose proof (bv_unsigned_in_range 64 w18) as B18. pose proof (bv_unsigned_in_range 64 w19) as B19. change (bv_modulus 64) with (2 ^ 64) in *.
  pose proof (PMBSKJ.mach_vis L ar C HI LY HIok LB FF LK cr Aw M1 model2 HH2 BASE) as (V0 & V1 & V2).
  pose proof (PMBSKJ.stk_vis L ar C HI LY HIok LB FF LK cr Aw M1 model2 sp scr 48 HH2 ASTK ltac:(lia)) as (SLO & SHI & V3).
  pose proof ASTK as (A16 & SLO0 & SHI0 & SPT & _).
  rewrite HID2 in *. fold MV in V0, V1, V2, V3.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model2 HH2) as (_ & VIS & _).
  rewrite HID2 in VIS.
  assert (TV : forall k v, 8 <= k <= 40 -> L5.u64_at RSEGS M1 (sp - k) v -> L5.u64_at RSEGS MV (sp - k) v).
  { intros k v Hk X. apply (proj2 (L5A.u64_at_vis _ M1 (sp - k) v (VIS (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  pose proof (PMBPKP.apkT_conc fx1 R2' MV (fun j => match j with 2%nat => sp | 40%nat => bv_unsigned w1 | 41%nat => bv_unsigned w8 | 42%nat => bv_unsigned w9
                                           | 43%nat => bv_unsigned w18 | 44%nat => bv_unsigned w19 | _ => 0 end)) as P. cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | apply TV; [lia| assumption] | unfold PMBPKP.aligned; exact A16 | rewrite O by lia; exact R2 | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T18 & T19).
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw M1 model2 fx1 fx3 R2' 0xb8758 R3 0xb8770 M3v K HH2 AM2).
  { rewrite HID2. exact MS3. } { rewrite HID2. exact MG3. } { intros i Hi. rewrite HID2. apply FRZ3. exact Hi. }
  intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4.
  assert (E41 : M4 = M1) by (apply L5SAR.mem_eq_of_agree; exact FR4). subst M4.
  apply (KONT fx3 R3 model4 b Hb).
  - rewrite (KS3 10%nat) by inl. apply PMPX.regupd_same_idx. lia.
  - exact U8M.
  - rewrite T1. apply Z_to_bv_bv_unsigned.
  - exact T2.
  - rewrite T8. apply Z_to_bv_bv_unsigned.
  - rewrite T9. apply Z_to_bv_bv_unsigned.
  - rewrite T18. apply Z_to_bv_bv_unsigned.
  - rewrite T19. apply Z_to_bv_bv_unsigned.
  - intros k Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (KS3 _) by inl; apply O; lia|]). destruct Hk.
  - eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT4].
  - exact AM4.
  - exact HH4.
  - rewrite HID4. exact HID2.
Qed.

Ltac vis64 OAV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.

Theorem peek_ok : PECSB.fill_buffer_spec L ar HI -> PECSB.peek_spec L ar HI.
Proof.
  intros FB. unfold PECSB.peek_spec, PECSPA.peek_spec, PECSPA.csrc_spec.
  intros fx R M model K LBX FF LK Aw cr sp r fb pl s str sm Wextra HH AM K0 ENT FRM FRS FOK ALN A10 _ WX PA IA BASE ACCP INCS POK CONT KONT.
  pose proof CONT as (CSZ & CBS & CPOS & CBW & CST2). unfold PEC.pos_of, PM.unread in CPOS, CBW.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  unfold PMSPA.no_W in WX. subst Wextra. rewrite app_nil_r in KONT.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  change (PMSPA.pm_scr 4) with 20480 in *. pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  set (LB := PM.parser_own s ++ LBX) in *.
  pose proof (PMBSKJ.src_vis L ar C HI LY HIok LB FF LK cr Aw M model fb (PMSPA.o_is PeCLayoutB.CADDR_B fb) s sp 20480 HH FOK PA ASTK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
  set (os := PMSPA.o_src PeCLayoutB.CADDR_B fb) in *.
  pose proof (PMBSKJ.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMBSKJ.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 20480 48 HH ASTK ltac:(lia)) as (SL48 & SH48 & V3).
  destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg st].
  cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st PM.p_more PM.p_done PM.p_depth PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EGD & IE2). cbn [PM.sm_g PM.sm_eg] in EGD, IE2.
  pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & PSRC & _).
  destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  fold os in S240, S248, SD256, S264, S272, S280, S288.
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4.
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (HO : bv_unsigned (getr R (reg 10)) = os) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (VD256 : L5.defined MV (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M (os + 256) 8 ltac:(apply OAV; lia))); exact SD256).
  destruct (Z_le_gt_dec 1 rem) as [REM1|REM0].
  -
    pose proof (PMBSKJ.blk_byte_vis L ar C HI LY HIok LB FF LK cr Aw M model qc 16384 de HH QIN DCH ACH ltac:(reflexivity) ltac:(split; lia))
      as (D0 & D1 & DV & DBIG & DZ & DFS).
    pose proof (PMBPKP.apkA1_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | _ => 0 end)) as P.
    cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | exact Rsp | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
        | |- PMBPKP.aligned _ _ => unfold PMBPKP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & C40 & C32 & C24 & C16 & C8).
    unfold PMSPA.cfg. cbn [pa_peek PeCLayoutB.CADDR_B ADDR_A].
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb8690 R1 0xb8754 M1v (fun a => sp - 48 <= a < sp - 48 + 48) K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
    { intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [] M M1).
    { apply (PMKB.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 20480 [] (sp - 48) (sp - 48 + 48) HH SPT); [lia|lia|lia|].
      intros a Ha Hn. apply FR1; [exact Ha| exact Hn]. }
    assert (BASE1 : PMSTA.base_okA RSEGS PeCLayoutB.CADDR_B M1) by (apply (PMBSKJ.base_keep L ar C LY LB FF sp 20480 [] M M1 EK01); [intros a _ r0 []| exact BASE]).
    assert (ASTK1 : L5CA.astk ar M1 sp 20480) by (apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1)).
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
    assert (TM1 : forall k v, 8 <= k <= 40 -> L5.u64_at RSEGS M1v (sp - k) v -> L5.u64_at RSEGS M1 (sp - k) v).
    { intros k v Hk X. rewrite <- VIS1 in X. rewrite <- HID1 in X.
      apply (proj1 (L5A.u64_at_vis _ M1 (sp - k) v (VIS1s (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
    pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. change (bv_modulus 64) with (2 ^ 64) in *.
    apply (peek_tail fx1 R1 M1 model1 K LB FF LK cr Aw sp 20480 de (getr R (reg 1)) (getr R (reg 8)) (getr R (reg 9)) (getr R (reg 18)) (getr R (reg 19))
             HH1 AM1 BASE1 ASTK1 ltac:(lia) T2 T10 ltac:(lia)).
    { rewrite HID1, VIS1. apply (L5C.defined_agree MV M1v de 1); [intros i Hi; apply FRZ1; lia| exact DV]. }
    { apply TM1; [lia| exact C8]. } { apply TM1; [lia| exact C16]. } { apply TM1; [lia| exact C24]. } { apply TM1; [lia| exact C32]. } { apply TM1; [lia| exact C40]. }
    intros fx3 R3 model3 b Hb U10 U8b U1 U2 U8 U9 U18 U19 UO MRT3 AM3 HH3 HID3.
    assert (Rr : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite U1; exact Rra).
    apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw M1 model3 fx3 fx3 R3 0xb8770 R3 r (mrestrict (ahid Aw model3) M1) K HH3 AM3
             (PMK.ret_to RSEGS fx3 R3 _ 0xb8770 W_b8720 r F_b8720 eq_refl D_b8720 Rr ltac:(lia) Hr2) (fun _ X => X) (fun _ _ => eq_refl)).
    intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4.
    assert (E41 : M4 = M1) by (apply L5SAR.mem_eq_of_agree; exact FR4). subst M4.
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as (WB4 & WF4 & _).
    assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
    { intros f Hf. destruct (WF4 f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
    assert (BRB : forall b0, In b0 LB -> 0 <= fst b0 /\ fst b0 + snd b0 <= 2 ^ 47).
    { intros b0 Hb0. destruct (proj1 (WB4 b0 Hb0)) as (X0 & _ & _ & _ & X4 & _). lia. }
    destruct FOK as ((rs & Hfb) & F1024).
    assert (AOP : PMSPA.aobjA FF (PMSPA.o_p PeCLayoutB.CADDR_B fb) 384).
    { exists (fb, 5, rs). split; [exact Hfb|]. unfold PMSPA.o_p. cbn [ff_addr ff_class pa_off_p PeCLayoutB.CADDR_B ADDR_A]. unfold ff_bytes. cbn. lia. }
    assert (AOI : PMSPA.aobjA FF (PMSPA.o_is PeCLayoutB.CADDR_B fb) 272).
    { exists (fb, 5, rs). split; [exact Hfb|]. unfold PMSPA.o_is. cbn [ff_addr ff_class pa_off_is PeCLayoutB.CADDR_B ADDR_A]. unfold ff_bytes. cbn. lia. }
    apply (KONT fx3 R3 M1 model4 LK Aw (PM.SRC qc de rem) (PM.STRM g eg st)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk];
        [ first [ rewrite U2; exact (eq_sym Rsp) | rewrite U8; reflexivity | rewrite U9; reflexivity | rewrite U18; reflexivity | rewrite U19; reflexivity
                | rewrite (UO _) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
      destruct Hk.
    + apply (PMKB.parser_keepA RSEGS PeCLayoutB.CADDR_B L ar LB FF sp 20480 [] M M1 EK01 PMKB.wapp_nil FRB BRB _ _ _ AOP); [| intros i _ r0 []| | | |exact PA].
      * unfold LB. apply incl_appl, incl_refl.
      * intros i _ r0 []. * intros i _ r0 []. * intros c0 n0 p0 _ i _ r0 [].
    + apply (PMKB.iss_keepA RSEGS PeCLayoutB.CADDR_B L ar LB FF sp 20480 [] M M1 EK01 PMKB.wapp_nil FRB BRB _ _ _ AOI); [| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
      unfold LB. apply incl_appr. exact INCS.
    + unfold PMSPA.src_step, PM.unread. cbn. lia.
    +
      assert (W3 : L5.bytes_at RSEGS M1 de (UbjRef.slice pl (blen pl - (rem + (eg - g))) rem)).
      { apply (PECSD.bytes_agree RSEGS M M1 de rem); [apply PECF.slice_length_le; clear - REM1; lia| clear - Q0 G1; lia| clear - Q4 G3 SLO SHI SPT; lia| | exact CBW].
        intros i Hi. apply FR1; [clear - Hi Q0 Q4 G1 G3 SLO SHI SPT; lia| clear - Hi Q4 G3 SLO; lia]. }
      assert (EB : b = bat pl (blen pl - (rem + (eg - g)))).
      { apply (PECSD.u8_at_inj RSEGS M1 de b); [exact U8b| | exact Hb| apply UbjRefFactsS9.bat_range; exact (proj1 POK)].
        apply (PECSD.window_byte RSEGS M1 pl de (blen pl - (rem + (eg - g))) rem); [clear - CPOS; lia| exact REM1| clear - IE2; lia| exact W3]. }
      unfold PECSPA.cpeek_res, PECSPA.cwin, PMSPA.consumed, PEC.pos_of, PM.unread. cbn [PM.sr_rem PM.sr_de PM.sm_eg PM.sm_g PM.sm_st]. split; [clear; lia|].
      split. { split; [clear - CPOS IE2 REM1; lia|]. split; [exact W3| exact CST2]. }
      right. split; [clear - REM1 IE2; lia|]. split; [rewrite L5K.rl10, U10, EB; reflexivity| exact REM1].
    + apply (L5SAR.ahpres_of L ar LB FF sp 20480 _ M M1).
      * apply (L5SAR.ek_W L ar LB FF sp 20480 _ [] M M1 EK01). intros a _ r0 [].
      * pose proof ASTK1 as (_ & _ & _ & _ & DS1 & _). exact DS1.
      * apply (L5SAR.dk_grows L ar LB FF sp 20480 M M1 MGM1).
    + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + apply incl_refl.
    + apply incl_refl.
    + exact AM4.
    + exact HH4.
  -
    assert (REMZ : rem = 0) by lia. subst rem.
    pose proof (PMBPKP.apkA0_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | _ => 0 end)) as P.
    cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | exact Rsp | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
        | |- PMBPKP.aligned _ _ => unfold PMBPKP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T11 & T12 & T13 & T18 & T19 & C280 & C40 & C32 & C24 & C16 & C8
                   & C264 & C272 & C288 & CD256).
    unfold PMSPA.cfg. cbn [pa_peek PeCLayoutB.CADDR_B ADDR_A].
    set (W1 := fun a => (sp - 48 <= a < sp - 48 + 48) \/ (os + 256 <= a < os + 256 + 40)).
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb8690 R1 0xb9944 M1v W1 K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha Wa. split; [|unfold W1 in Wa; intros X; lia]. destruct Wa as [Wa|Wa].
      - unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - unfold aclientw, aclient_g. do 3 right. left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    set (op := PMSPA.o_p PeCLayoutB.CADDR_B fb) in *. set (ois := PMSPA.o_is PeCLayoutB.CADDR_B fb) in *.
    assert (OSP : os = op + 24) by reflexivity.
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF0 & _).
    change (PMSP.o_is PeCLayoutB.CADDR_B fb) with ois in CBS.

    assert (DLOC : (PM.vs_data (ois + 80) str = ois + 81 /\ blen pl <= 22 /\ 0 <= ois /\ ois + 272 <= ahl_ceil ar)
                \/ (exists c1 n1 q1, str = PM.VLong c1 n1 q1 /\ PM.vs_data (ois + 80) str = q1 /\ 4096 <= q1 /\ q1 + c1 <= ahl_ceil ar /\ blen pl < c1
                                     /\ (q1 + c1 <= os \/ os + 296 <= q1))).
    { pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). destruct VS as (_ & _ & VSF).
      destruct str as [n0|c1 n1 q1]; cbn [PM.vs_data PM.vs_size] in VSF, CSZ |- *.
      - left. pose proof FOK as ((rs0 & Hfb0) & F2048). destruct (WF0 (fb, 5, rs0) Hfb0) as (Yw1 & Yw2 & _). unfold ff_addr, ff_class in Yw1, Yw2. cbn [fst snd] in Yw1, Yw2.
        pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & FSAPP' & FSCEIL' & _). unfold app_mem, FS_BYTES, ff_bytes in FSAPP', FSCEIL', Yw1, Yw2.
        unfold ois, PMSPA.o_is. cbn [pa_off_is PeCLayoutB.CADDR_B]. split; [clear; lia|]. split; [clear - VSF CSZ; lia| clear - Yw1 Yw2 FSAPP' FSCEIL'; lia].
      - right. exists c1, n1, q1. assert (SIN : In (q1, c1) LB) by (unfold LB; apply in_or_app; right; apply INCS; cbn; left; reflexivity).
        destruct (WB _ SIN) as ((B0 & _ & _ & _ & B4 & _) & _). cbn [fst snd] in B0, B4.
        destruct VSF as (_ & _ & _ & Hn1 & _). split; [reflexivity|]. split; [reflexivity|]. split; [clear - B0; lia|]. split; [clear - B4; lia|]. split; [clear - Hn1 CSZ; lia|].
        destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 os 296 HH SIN AO) as [X|X]; clear - X; lia. }
    assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
    { intros f Hf. destruct (WF0 f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
    assert (BRB : forall b0, In b0 LB -> 0 <= fst b0 /\ fst b0 + snd b0 <= 2 ^ 47).
    { intros b0 Hb0. destruct (proj1 (WB b0 Hb0)) as (X0 & _ & _ & _ & X4 & _). lia. }
    pose proof FOK as ((rs & Hfb) & F1024).
    assert (AOP : PMSPA.aobjA FF op 384).
    { exists (fb, 5, rs). split; [exact Hfb|]. unfold op, PMSPA.o_p. cbn [ff_addr ff_class pa_off_p PeCLayoutB.CADDR_B ADDR_A]. unfold ff_bytes. cbn. lia. }
    assert (AOI : PMSPA.aobjA FF ois 272).
    { exists (fb, 5, rs). split; [exact Hfb|]. unfold ois, PMSPA.o_is. cbn [ff_addr ff_class pa_off_is PeCLayoutB.CADDR_B ADDR_A]. unfold ff_bytes. cbn. lia. }
    assert (WS1 : PMKB.wapp [(os + 256, 40)]).
    { apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG as [X|X]; [right; lia| left; lia]| apply PMKB.wapp_nil]. }
    assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M M1).
    { apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M M1 W1 FR1). intros a Ha CL O [X|X].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 20480 a HH SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
      - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }

    assert (TO1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb X. rewrite <- VIS1 in X. apply (proj1 (L5A.u64_at_vis _ M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). exact X. }
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
    assert (TS1 : forall k v, 8 <= k <= 40 -> L5.u64_at RSEGS M1v (sp - k) v -> L5.u64_at RSEGS M1 (sp - k) v).
    { intros k v Hk X. rewrite <- VIS1, <- HID1 in X.
      apply (proj1 (L5A.u64_at_vis _ M1 (sp - k) v (VIS1s (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
    assert (AOP280 : PMSPA.aobjA FF op 280) by (destruct AOP as (f & Hf & X1 & X2); exists f; split; [exact Hf| lia]).
    assert (AOP320 : PMSPA.aobjA FF (op + 320) 64) by (destruct AOP as (f & Hf & X1 & X2); exists f; split; [exact Hf| lia]).
    assert (AOP280' : PMSPA.aobjA FF (op + 280) 40) by (destruct AOP as (f & Hf & X1 & X2); exists f; split; [exact Hf| lia]).
    assert (OUTO : forall i, ~ (os + 256 <= i < os + 296) -> L5.outside [(os + 256, 40)] i).
    { intros i N r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
    assert (BOWN : incl (PM.parser_own (PM.PST mo dn dp (PM.SRC qc de 0) tb tg vb vk stk)) LB) by (unfold LB; apply incl_appl, incl_refl).
    assert (QIN' := QIN).
    assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (apply BOWN; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity).
    pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PTB & PVEC & _).
    pose proof PVEC as (_ & _ & _ & VK & _ & VB16 & _).
    assert (OUTQ : forall i, qc <= i < qc + 16384 -> L5.outside [(os + 256, 40)] i).
    { intros i Hi. apply OUTO. destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 os 296 HH QIN AO) as [X|X]; lia. }
    assert (OUTV : forall i, vb <= i < vb + 32 * 2 ^ vk -> L5.outside [(os + 256, 40)] i).
    { intros i Hi. apply OUTO. destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) os 296 HH VIN AO) as [X|X]; lia. }
    assert (OUTT : forall c0 n0 p0, tb = PM.VLong c0 n0 p0 -> forall i, p0 <= i < p0 + c0 -> L5.outside [(os + 256, 40)] i).
    { intros c0 n0 p0 E i Hi. subst tb. apply OUTO.
      assert (TIN : In (p0, c0) LB) by (apply BOWN; unfold PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own; cbn; right; right; left; reflexivity).
      destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ p0 c0 os 296 HH TIN AO) as [X|X]; lia. }
    assert (PA1 : PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M1 op ois (PMSPA.with_src (PM.PST mo dn dp (PM.SRC qc de 0) tb tg vb vk stk) (PM.SRC qc qc 0))).
    { apply (PMBSKJ.parser_src_fieldsA M M1 op ois _ qc 0 PA).
      - lia. - lia.
      - apply (PMKB.agA_obj L ar LB FF sp 20480 _ M M1 EK01 WS1 FRB op 280 AOP280). intros i Hi. apply OUTO. lia.
      - apply (PMKB.agA_obj L ar LB FF sp 20480 _ M M1 EK01 WS1 FRB (op + 320) 64 AOP320). intros i Hi. apply OUTO. lia.
      - apply (PMKB.agsh_obj L ar LB FF sp 20480 _ M M1 EK01 WS1 FRB (op + 280) 40 AOP280').
      - cbn. lia. - cbn. unfold PM.CHUNK. lia.
      - cbn. apply (PMKB.agA_blk L ar LB FF sp 20480 _ M M1 EK01 WS1 BRB qc PM.CHUNK QIN). exact OUTQ.
      - cbn. destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
      - cbn. destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
      - cbn. apply (PMKB.agA_blk L ar LB FF sp 20480 _ M M1 EK01 WS1 BRB vb _ VIN). exact OUTV.
      - cbn. intros c0 n0 p0 E. subst tb.
        assert (TIN : In (p0, c0) LB) by (apply BOWN; unfold PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own; cbn; right; right; left; reflexivity).
        apply (PMKB.agA_blk L ar LB FF sp 20480 _ M M1 EK01 WS1 BRB p0 c0 TIN). exact (OUTT c0 n0 p0 eq_refl).
      - exact MGM1.
      - cbn. replace (op + 288) with (os + 264) by lia. apply TO1; [lia|lia|exact C264].
      - replace (op + 296) with (os + 272) by lia. apply TO1; [lia|lia|exact C272].
      - replace (op + 304) with (os + 280) by lia. apply TO1; [lia|lia|exact C280].
      - replace (op + 312) with (os + 288) by lia. apply TO1; [lia|lia|exact C288].
      - cbn. lia. - lia. - cbn. unfold PM.CHUNK. lia. }
    cbn [PMSPA.with_src PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in PA1.
    set (s1 := PM.PST mo dn dp (PM.SRC qc qc 0) tb tg vb vk stk) in PA1.
    assert (ASTK1 : L5CA.astk ar M1 sp 20480) by (apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1)).
    assert (BASE1 : PMSTA.base_okA RSEGS PeCLayoutB.CADDR_B M1).
    { apply (PMBSKJ.base_keep L ar C LY LB FF sp 20480 _ M M1 EK01); [intros a Ha; apply OUTO; lia| exact BASE]. }
    assert (IA1 : PM.iss_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA M1 ois str (PM.STRM g eg st)).
    { apply (PMKB.iss_keepA RSEGS PeCLayoutB.CADDR_B L ar LB FF sp 20480 _ M M1 EK01 WS1 FRB BRB ois str _ AOI); [unfold LB; apply incl_appr; exact INCS| | |exact IA].
      - intros i Hi. apply OUTO. unfold ois, PMSPA.o_is in *. unfold os, PMSPA.o_src, op, PMSPA.o_p in *. cbn [pa_off_is pa_off_p PeCLayoutB.CADDR_B ADDR_A] in *. lia.
      - intros c0 n0 p0 E i Hi. apply OUTO. subst str.
        assert (TIN : In (p0, c0) LB) by (unfold LB; apply in_or_app; right; apply INCS; cbn; left; reflexivity).
        destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ p0 c0 os 296 HH TIN AO) as [X|X]; lia. }
    assert (STK1 : shadow_zero M1 (sp - 48 - 18432) (18432 / 8)).
    { change (18432 / 8) with 2304. change (20480 / 8) with 2560 in STKSH.
      assert (M8a : (sp - 20480) mod 8 = 0) by (apply PMKB.mod16_8'; replace (sp - 20480) with (sp + (-1280) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
      assert (M8b : (sp - 48 - 18432) mod 8 = 0) by (apply PMKB.mod16_8'; replace (sp - 48 - 18432) with (sp + (-1155) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
      apply (PMKB.shadow_zero_sub M1 (sp - 20480) 2560); [exact M8a| exact M8b| lia| lia| lia|].
      apply (PMKB.stksh_keepA L ar LB FF sp 20480 _ M M1 EK01 WS1 (sp - 20480) 2560); [lia|lia|lia| exact M8a| lia| exact STKSH]. }

    unfold PECSB.fill_buffer_spec, PECSPA.fill_buffer_spec, PECSPA.csrc_spec in FB.
    apply (FB fx1 R1 M1 model1 K LBX FF LK Aw cr (sp - 48) 0xb871c fb pl s1 str (PM.STRM g eg st) [] HH1 AM1 K0).
    { split; [rewrite L5K.rl1; exact T1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact T2|].
      split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
      change (PMSPA.pm_scr 3) with 18432. split; [|exact STK1].
      apply (L5SAR.astk_sub ar M1 M1 sp 20480 48 18432 ASTK1 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    { intros k Hk. specialize (FRM k Hk). lia. }
    { intros f Hf. specialize (FRS f Hf). lia. }
    { exact FOK. }
    { replace (sp - 48) with (sp + (-3) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
    { rewrite L5K.rl10. rewrite (KS1 10%nat) by inl. rewrite A10. reflexivity. }
    { split; [rewrite L5SAR.r12; exact T12|]. exists os, qc. split; [rewrite L5K.rl10; rewrite (KS1 10%nat) by inl; exact A10|]. split; [clear - O1; lia|].
      split; [rewrite L5SAR.r11; exact T11|]. split; [clear - Q0 Q4 SLO SHI SPT; lia|]. apply TO1; [clear; lia| clear; lia| exact C264]. }
    { reflexivity. }
    { exact PA1. }
    { exact IA1. }
    { exact BASE1. }
    {
      pose proof FOK as ((rs0 & Hfb0) & F2048). destruct (FRB (fb, 5, rs0) Hfb0) as (Yf1 & Yf2). unfold ff_addr, ff_class, ff_bytes in Yf1, Yf2. cbn in Yf1, Yf2.
      apply (PMFA.accA_agree M M1 op PECA.RDR_BYTES); [| exact ACCP]. unfold PECA.RDR_BYTES.
      intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(unfold op, PMSPA.o_p in Hx; cbn [pa_off_p PeCLayoutB.CADDR_B] in Hx; clear - Hx Yf1 Yf2; lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
      apply FR1; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; clear - SX; lia| unfold W1; unfold HeapIfaceA.S, HeapIfaceA.SB in *; clear - SX OBIG SLO SHI SPT O1; lia]. }
    { exact INCS. }
    { exact POK. }
    {
      unfold PEC.content_ok. change (PMSP.o_is PeCLayoutB.CADDR_B fb) with ois. unfold s1. cbn [PM.p_src PM.sr_de PM.sr_rem PM.sm_st PM.sm_g PM.sm_eg].
      split; [exact CSZ|]. split.
      { apply (PECSD.bytes_agree RSEGS M M1 (PM.vs_data (ois + 80) str) (blen pl)); [unfold blen; clear; lia| | | | exact CBS].
        - destruct DLOC as [(-> & _ & Y0 & _)|(c1 & n1 & q1 & _ & -> & B0 & _)]; [clear - Y0; lia| clear - B0; lia].
        - destruct DLOC as [(-> & Hn & _ & Yc)|(c1 & n1 & q1 & _ & -> & _ & B4 & Hc & _)]; [clear - Hn Yc SLO SHI SPT; lia| clear - B4 Hc SLO SHI SPT; lia].
        - intros i Hi. destruct DLOC as [(E & Hn & Y0 & Yc)|(c1 & n1 & q1 & Es & E & B0 & B4 & Hc & AP)]; rewrite E in Hi.
          + apply FR1; [clear - Hi Hn Y0 Yc SLO SHI SPT; lia| unfold W1; unfold ois, os, PMSPA.o_is, PMSPA.o_src, PMSPA.o_p in *; cbn [pa_off_is pa_off_p PeCLayoutB.CADDR_B] in *; clear - Hi Hn Yc SLO; lia].
          + apply FR1; [clear - Hi B0 B4 Hc SLO SHI SPT; lia| unfold W1; clear - Hi B4 Hc AP SLO; lia]. }
      split; [unfold PEC.pos_of, PM.unread; cbn [PM.sr_rem PM.sm_eg PM.sm_g]; clear - CPOS; lia|].
      split; [unfold UbjRef.slice; cbn [PM.sr_de PM.sr_rem Z.to_nat firstn]; apply PECSD.bytes_at_nil| cbn [PM.sm_st PM.sm_g PM.sm_eg]; exact CST2]. }
    intros fx2 R2 M2 model2 LK2 Aw2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 MRT2 INC2 INCA2 AM2 HH2. clear FB.
    destruct RES2 as (E2 & c & A10c & Hc & G2c & RSC & RS2 & CHK2 & ST2c). subst src2. unfold PM.CHUNK in Hc, RSC.
    destruct sm2 as [g2 eg2 st2]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in *. unfold s1 in CHK2. cbn [PM.p_src PM.sr_qc] in CHK2.
    pose proof IA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KEG2 & KE2). cbn [PM.sm_g PM.sm_eg] in KEG2, KE2.
    cbn [PMSPA.with_src PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in PA2. fold s1 in PA2.
    change (PM.parser_own s1 ++ LBX) with LB in HH2, HP2. rewrite app_nil_r in HP2. change (PMSPA.pm_scr 3) with 18432 in HP2.

    assert (EK12 : L5SAR.ek L ar LB FF sp 20480 (PMSPA.W_src PeCLayoutB.CADDR_B fb (PM.SRC qc qc 0)) M1 M2).
    { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 48) 18432 _ _ M1 M2 HP2); [lia|lia|]. intros a _ O. exact O. }
    assert (DK12 : L5SAR.dk L ar LB FF sp 20480 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 48) 18432 _ M1 M2 HP2); lia).
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP2 & _).
    assert (ASTK2 : L5CA.astk ar M2 sp 20480).
    { apply (PMKB.astk_after_ahpres L ar LB FF M1 M2 sp 20480 (sp - 48) 18432 _ ASTK1 HP2); lia. }
    pose proof (PMBSKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
    assert (FBI : ar_fs ar <= fb) by (destruct (WF0 (fb, 5, rs) Hfb) as (Y1 & _); unfold ff_addr in Y1; cbn in Y1; exact Y1).
    pose proof (PMBSKJ.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ qc 16384 HH QIN) as QIMG.
    assert (OUTW : forall a, 65536 <= a < 6930432 -> L5.outside (PMSPA.W_src PeCLayoutB.CADDR_B fb (PM.SRC qc qc 0)) a).
    { intros a Ha r0 Hr. unfold PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
      unfold ois, os, op, PMSPA.o_is, PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_is pa_off_p PeCLayoutB.CADDR_B ADDR_A] in *.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; unfold s1 in *; cbn [fst snd PM.p_src PM.sr_qc] in *; unfold PM.CHUNK; lia. }
    assert (BASE2 : PMSTA.base_okA RSEGS PeCLayoutB.CADDR_B M2) by (apply (PMBSKJ.base_keep L ar C LY LB FF sp 20480 _ M1 M2 EK12 OUTW BASE1)).
    assert (KF2 : forall a, sp - 48 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. destruct HP2 as (E & _). apply E. split; [lia|]. split.
      - apply (L5SAR.stack_client L ar LB FF (sp - 48) 18432 a); [lia| lia].
      - intros r0 Hr. unfold PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
        unfold ois, os, op, PMSPA.o_is, PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_is pa_off_p PeCLayoutB.CADDR_B ADDR_A] in *.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; unfold s1 in *; cbn [fst snd PM.p_src PM.sr_qc] in *; unfold PM.CHUNK; lia. }
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2s & _).
    set (MV2 := mrestrict (ahid Aw2 model2) M2) in *.
    assert (TS2 : forall k v, 8 <= k <= 40 -> L5.u64_at RSEGS M1 (sp - k) v -> L5.u64_at RSEGS MV2 (sp - k) v).
    { intros k v Hk X. apply (proj2 (L5A.u64_at_vis _ M2 (sp - k) v (VIS2s (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply KF2; lia| lia| lia| exact X]. }
    pose proof (PMBSKJ.src_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 fb ois s1 sp 20480 HH2 FOK PA2 ASTK2)
      as ((P1 & P8 & PBIG) & PZ & PW & PCE & PAV & _ & _).
    fold os in P1, P8, PBIG, PZ, PW, PCE, PAV.
    pose proof (PMBSKJ.mach_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 HH2 BASE2) as (W0 & W1' & W2').
    pose proof (PMBSKJ.stk_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 sp 20480 48 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3).
    fold MV2 in W0, W1', W2', W3.
    pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _).
    destruct PSRC2 as (_ & _ & SD2 & S264b & S272b & S280b & S288b & _ & _ & _ & _ & DCH2 & ACH2 & _). cbn [PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
    fold os in SD2, S264b, S272b, S280b, S288b.
    assert (VD2 : L5.defined MV2 (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M2 (os + 256) 8 ltac:(apply PAV; lia))); exact SD2).
    assert (RG8 : getr R2 (reg 8) = Z_to_bv 64 (os + 280)) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; exact T8).
    assert (RG9 : getr R2 (reg 9) = Z_to_bv 64 (os + 288)) by (rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl; exact T9).
    assert (RG18 : getr R2 (reg 18) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 18 RP2) by inl; exact T18).
    assert (RG19 : getr R2 (reg 19) = Z_to_bv 64 ((os + 288) / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R1 R2 19 RP2) by inl; exact T19).
    assert (RG2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact T2).
    rewrite L5K.rl10 in A10c.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. change (bv_modulus 64) with (2 ^ 64) in *.
    set (VS := fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => os | 40%nat => bv_unsigned (getr R (reg 1))
                                  | 41%nat => bv_unsigned (getr R (reg 8)) | 42%nat => bv_unsigned (getr R (reg 9)) | 43%nat => bv_unsigned (getr R (reg 18))
                                  | 44%nat => bv_unsigned (getr R (reg 19)) | _ => 0 end).
    assert (WS3 := WS1).

    assert (EK02 : L5SAR.ek L ar LB FF sp 20480 (PMSPA.W_src PeCLayoutB.CADDR_B fb (PM.SRC qc de 0)) M M2).
    { apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M M1 M2); [|exact EK12].
      apply (L5SAR.ek_W L ar LB FF sp 20480 _ [(os + 256, 40)] M M1 EK01). intros a O r0 [<-|[]] X. apply (O (os + 256, 40)); [left; reflexivity| exact X]. }
    assert (DK02 : L5SAR.dk L ar LB FF sp 20480 M M2) by (apply (L5SAR.dk_trans L ar LB FF sp 20480 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12]).
    destruct (Z.eq_dec c 0) as [C0|C1].
    +
      subst c.
      pose proof (PMBPKP.apkB0_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| apply TS1; [lia| assumption]]
        | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
        | |- PMBPKP.aligned _ _ => unfold PMBPKP.aligned; lia
        | |- _ => lia end]).
      destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & V1' & V2' & V8' & V9' & V10' & V11' & V18' & V19' & D288 & D264 & D272 & D280 & DD256 & _).
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb871c R3 0xb8770 M3v W1 K HH2 AM2 MS3 MG3).
      { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { intros a Ha Wa. split; [|unfold W1 in Wa; intros X; lia]. destruct Wa as [Wa|Wa].
        - unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
        - unfold aclientw, aclient_g. do 3 right. left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
      intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3).
      { apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M2 M3 W1 FR3). intros a Ha CL O [X|X].
        - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 20480 a HH2 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
        - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
      assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      assert (Rr : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite V1', Z_to_bv_bv_unsigned; exact Rra).
      apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK2 cr Aw2 M3 model3 fx3 fx3 R3 0xb8770 R3 r (mrestrict (ahid Aw2 model3) M3) K HH3 AM3
               (PMK.ret_to RSEGS fx3 R3 _ 0xb8770 W_b8720 r F_b8720 eq_refl D_b8720 Rr ltac:(lia) Hr2) (fun _ X => X) (fun _ _ => eq_refl)).
      intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4.
      assert (E43 : M4 = M3) by (apply L5SAR.mem_eq_of_agree; exact FR4). subst M4.
      apply (KONT fx3 R3 M3 model4 LK2 Aw2 (PM.SRC qc qc 0) (PM.STRM g2 eg2 st2)).
      * apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
        repeat (destruct Hk as [<-|Hk];
          [ first [ rewrite V2'; exact (eq_sym Rsp) | rewrite V8', Z_to_bv_bv_unsigned; reflexivity | rewrite V9', Z_to_bv_bv_unsigned; reflexivity
                  | rewrite V18', Z_to_bv_bv_unsigned; reflexivity | rewrite V19', Z_to_bv_bv_unsigned; reflexivity
                  | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
        destruct Hk.
      * apply (PMBSKJ.parser_src_fieldsA M2 M3 op ois s1 qc 0 PA2).
        -- lia. -- lia.
        -- apply (PMKB.agA_obj L ar LB FF sp 20480 _ M2 M3 EK23 WS1 FRB op 280 AOP280). intros i Hi. apply OUTO. lia.
        -- apply (PMKB.agA_obj L ar LB FF sp 20480 _ M2 M3 EK23 WS1 FRB (op + 320) 64 AOP320). intros i Hi. apply OUTO. lia.
        -- apply (PMKB.agsh_obj L ar LB FF sp 20480 _ M2 M3 EK23 WS1 FRB (op + 280) 40 AOP280').
        -- unfold s1. cbn. lia. -- unfold s1. cbn. unfold PM.CHUNK. lia.
        -- unfold s1. cbn. apply (PMKB.agA_blk L ar LB FF sp 20480 _ M2 M3 EK23 WS1 BRB qc PM.CHUNK QIN). exact OUTQ.
        -- unfold s1. cbn. destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
        -- unfold s1. cbn. destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
        -- unfold s1. cbn. apply (PMKB.agA_blk L ar LB FF sp 20480 _ M2 M3 EK23 WS1 BRB vb _ VIN). exact OUTV.
        -- unfold s1. cbn. intros c0 n0 p0 E. subst tb.
           assert (TIN : In (p0, c0) LB) by (apply BOWN; unfold PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own; cbn; right; right; left; reflexivity).
           apply (PMKB.agA_blk L ar LB FF sp 20480 _ M2 M3 EK23 WS1 BRB p0 c0 TIN). exact (OUTT c0 n0 p0 eq_refl).
        -- exact MGM3.
        -- unfold s1. cbn. replace (op + 288) with (os + 264) by lia. apply TO3; [lia|lia|exact D264].
        -- replace (op + 296) with (os + 272) by lia. apply TO3; [lia|lia|exact D272].
        -- replace (op + 304) with (os + 280) by lia. apply TO3; [lia|lia|exact D280].
        -- replace (op + 312) with (os + 288) by lia. apply TO3; [lia|lia|exact D288].
        -- unfold s1. cbn. lia. -- lia. -- unfold s1. cbn. unfold PM.CHUNK. lia.
      * apply (PMKB.iss_keepA RSEGS PeCLayoutB.CADDR_B L ar LB FF sp 20480 _ M2 M3 EK23 WS1 FRB BRB ois str _ AOI); [unfold LB; apply incl_appr; exact INCS| | |exact IA2].
        -- intros i Hi. apply OUTO. unfold ois, PMSPA.o_is in *. unfold os, PMSPA.o_src, op, PMSPA.o_p in *. cbn [pa_off_is pa_off_p PeCLayoutB.CADDR_B ADDR_A] in *. lia.
        -- intros c0 n0 p0 E i Hi. apply OUTO. subst str.
           assert (TIN : In (p0, c0) LB) by (unfold LB; apply in_or_app; right; apply INCS; cbn; left; reflexivity).
           destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ p0 c0 os 296 HH TIN AO) as [X|X]; lia.
      * clear - STEP2 G2c. unfold PMSPA.src_step, PM.unread in *. cbn in *. lia.
      * pose proof (RSC ltac:(clear; lia)) as (GE2 & SE2).
        unfold PMSPA.src_step in STEP2. cbn [PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st PM.unread PM.sr_rem] in STEP2. destruct STEP2 as (_ & EE2 & _).
        unfold PECSPA.cpeek_res, PECSPA.cwin, PMSPA.consumed, PEC.pos_of, PM.unread. cbn [PM.sr_rem PM.sr_de PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st].
        split; [clear - G2c EE2; lia|]. split. { split; [clear - GE2 G2c EE2 CPOS; lia|]. split; [unfold UbjRef.slice; cbn [Z.to_nat firstn]; apply PECSD.bytes_at_nil| exact ST2c]. }
        left. split; [rewrite L5K.rl10; exact V10'| clear - GE2 G2c EE2; lia].
      * apply (L5SAR.ahpres_of L ar LB FF sp 20480 _ M M3).
        -- apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M M2 M3 EK02).
           apply (L5SAR.ek_W L ar LB FF sp 20480 _ [(os + 256, 40)] M2 M3 EK23). intros a O r0 [<-|[]] X. apply (O (os + 256, 40)); [left; reflexivity| exact X].
        -- pose proof (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3) as (_ & _ & _ & _ & DS3 & _). exact DS3.
        -- apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02). apply L5SAR.dk_grows. exact MGM3.
      * eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
      * exact INC2.
      * exact INCA2.
      * exact AM4.
      * exact HH4.
    +
      assert (QIN2 : In (qc, 16384) LB) by exact QIN.
      pose proof (PMBSKJ.blk_byte_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 qc 16384 qc HH2 QIN2 DCH2 ACH2 ltac:(reflexivity) ltac:(split; lia))
        as (E0 & E1 & EV & EBIG & EZ & EFS).
      fold MV2 in EV, EZ.
      pose proof (PMBPKP.apkB1_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| apply TS1; [lia| assumption]]
        | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
        | |- PMBPKP.aligned _ _ => unfold PMBPKP.aligned; lia
        | |- _ => lia end]).
      destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & V10' & V11' & D288 & D264 & D272 & D280 & DD256 & D8 & D16 & D24 & D32 & D40).
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb871c R3 0xb8754 M3v W1 K HH2 AM2 MS3 MG3).
      { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { intros a Ha Wa. split; [|unfold W1 in Wa; intros X; lia]. destruct Wa as [Wa|Wa].
        - unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
        - unfold aclientw, aclient_g. do 3 right. left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
      intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3).
      { apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M2 M3 W1 FR3). intros a Ha CL O [X|X].
        - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 20480 a HH2 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
        - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
      assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M3 model3 HH3) as (_ & VIS3s & _).
      assert (TS3 : forall k v, 8 <= k <= 40 -> L5.u64_at RSEGS M3v (sp - k) v -> L5.u64_at RSEGS M3 (sp - k) v).
      { intros k v Hk X. rewrite <- VIS3, <- HID3 in X.
        apply (proj1 (L5A.u64_at_vis _ M3 (sp - k) v (VIS3s (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
      assert (ASTK3 : L5CA.astk ar M3 sp 20480) by (apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3)).
      assert (BASE3 : PMSTA.base_okA RSEGS PeCLayoutB.CADDR_B M3).
      { apply (PMBSKJ.base_keep L ar C LY LB FF sp 20480 _ M2 M3 EK23); [intros a Ha; apply OUTO; lia| exact BASE2]. }
      assert (R32 : getr R3 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (KS3 2%nat) by inl; exact RG2).
      apply (peek_tail fx3 R3 M3 model3 K LB FF LK2 cr Aw2 sp 20480 qc (getr R (reg 1)) (getr R (reg 8)) (getr R (reg 9)) (getr R (reg 18)) (getr R (reg 19))
               HH3 AM3 BASE3 ASTK3 ltac:(lia) R32 V10' ltac:(lia)).
      { rewrite HID3, VIS3. apply (L5C.defined_agree MV2 M3v qc 1); [intros i Hi; apply FRZ3; lia| exact EV]. }
      { apply TS3; [lia| exact D8]. } { apply TS3; [lia| exact D16]. } { apply TS3; [lia| exact D24]. } { apply TS3; [lia| exact D32]. } { apply TS3; [lia| exact D40]. }
      intros fx4 R4 model4 b Hb U10 U8b U1 U2 U8 U9 U18 U19 UO MRT4 AM4 HH4 HID4.
      assert (Rr : getr R4 (reg 1) = Z_to_bv 64 r) by (rewrite U1; exact Rra).
      apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK2 cr Aw2 M3 model4 fx4 fx4 R4 0xb8770 R4 r (mrestrict (ahid Aw2 model4) M3) K HH4 AM4
               (PMK.ret_to RSEGS fx4 R4 _ 0xb8770 W_b8720 r F_b8720 eq_refl D_b8720 Rr ltac:(lia) Hr2) (fun _ X => X) (fun _ _ => eq_refl)).
      intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
      assert (E53 : M5 = M3) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
      apply (KONT fx4 R4 M3 model5 LK2 Aw2 (PM.SRC qc qc c) (PM.STRM g2 eg2 st2)).
      * apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
        repeat (destruct Hk as [<-|Hk];
          [ first [ rewrite U2; exact (eq_sym Rsp) | rewrite U8; reflexivity | rewrite U9; reflexivity | rewrite U18; reflexivity | rewrite U19; reflexivity
                  | rewrite (UO _) by inl; rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
        destruct Hk.
      * apply (PMBSKJ.parser_src_fieldsA M2 M3 op ois s1 qc c PA2).
        -- lia. -- lia.
        -- apply (PMKB.agA_obj L ar LB FF sp 20480 _ M2 M3 EK23 WS1 FRB op 280 AOP280). intros i Hi. apply OUTO. lia.
        -- apply (PMKB.agA_obj L ar LB FF sp 20480 _ M2 M3 EK23 WS1 FRB (op + 320) 64 AOP320). intros i Hi. apply OUTO. lia.
        -- apply (PMKB.agsh_obj L ar LB FF sp 20480 _ M2 M3 EK23 WS1 FRB (op + 280) 40 AOP280').
        -- unfold s1. cbn. lia. -- unfold s1. cbn. unfold PM.CHUNK. lia.
        -- unfold s1. cbn. apply (PMKB.agA_blk L ar LB FF sp 20480 _ M2 M3 EK23 WS1 BRB qc PM.CHUNK QIN). exact OUTQ.
        -- unfold s1. cbn. destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
        -- unfold s1. cbn. destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
        -- unfold s1. cbn. apply (PMKB.agA_blk L ar LB FF sp 20480 _ M2 M3 EK23 WS1 BRB vb _ VIN). exact OUTV.
        -- unfold s1. cbn. intros c0 n0 p0 E. subst tb.
           assert (TIN : In (p0, c0) LB) by (apply BOWN; unfold PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own; cbn; right; right; left; reflexivity).
           apply (PMKB.agA_blk L ar LB FF sp 20480 _ M2 M3 EK23 WS1 BRB p0 c0 TIN). exact (OUTT c0 n0 p0 eq_refl).
        -- exact MGM3.
        -- unfold s1. cbn. replace (op + 288) with (os + 264) by lia. apply TO3; [lia|lia|exact D264].
        -- replace (op + 296) with (os + 272) by lia. apply TO3; [lia|lia|exact D272].
        -- replace (op + 304) with (os + 280) by lia. apply TO3; [lia|lia|exact D280].
        -- replace (op + 312) with (os + 288) by lia. apply TO3; [lia|lia|exact D288].
        -- unfold s1. cbn. lia. -- lia. -- unfold s1. cbn. unfold PM.CHUNK. lia.
      * apply (PMKB.iss_keepA RSEGS PeCLayoutB.CADDR_B L ar LB FF sp 20480 _ M2 M3 EK23 WS1 FRB BRB ois str _ AOI); [unfold LB; apply incl_appr; exact INCS| | |exact IA2].
        -- intros i Hi. apply OUTO. unfold ois, PMSPA.o_is in *. unfold os, PMSPA.o_src, op, PMSPA.o_p in *. cbn [pa_off_is pa_off_p PeCLayoutB.CADDR_B ADDR_A] in *. lia.
        -- intros c0 n0 p0 E i Hi. apply OUTO. subst str.
           assert (TIN : In (p0, c0) LB) by (unfold LB; apply in_or_app; right; apply INCS; cbn; left; reflexivity).
           destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ p0 c0 os 296 HH TIN AO) as [X|X]; lia.
      * clear - STEP2 G2c. unfold PMSPA.src_step, PM.unread in *. cbn in *. lia.
      *
        unfold PMSPA.src_step in STEP2. cbn [PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st PM.unread PM.sr_rem] in STEP2. destruct STEP2 as (_ & EE2 & _). subst eg2.
        assert (W4 : L5.bytes_at RSEGS M3 qc (UbjRef.slice pl (blen pl - (eg - g)) c)).
        { apply (PECSD.bytes_agree RSEGS M2 M3 qc c); [apply PECF.slice_length_le; clear - Hc; lia| clear - Q0; lia| clear - Q4 SLO SHI SPT Hc; lia| | exact CHK2].
          intros i Hi. apply FR3; [clear - Hi Q0 Q4 SLO SHI SPT Hc; lia|]. unfold W1.
          destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 os 296 HH QIN AO) as [X|X]; clear - X Hi Q0 Q4 SLO SHI SPT Hc; lia. }
        assert (EB : b = bat pl (blen pl - (eg - g))).
        { apply (PECSD.u8_at_inj RSEGS M3 qc b); [exact U8b| | exact Hb| apply UbjRefFactsS9.bat_range; exact (proj1 POK)].
          apply (PECSD.window_byte RSEGS M3 pl qc (blen pl - (eg - g)) c); [clear - CPOS; lia| clear - C1 Hc; lia| clear - KE2 G2c; lia| exact W4]. }
        unfold PECSPA.cpeek_res, PECSPA.cwin, PMSPA.consumed, PEC.pos_of, PM.unread. cbn [PM.sr_rem PM.sr_de PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st].
        split; [clear - G2c; lia|]. split. { split; [clear - CPOS G2c KE2 IE2 Hc C1; lia|]. split; [replace (blen pl - (c + (eg - g2))) with (blen pl - (eg - g)) by (clear - G2c; lia); exact W4| exact ST2c]. }
        right. split; [clear - G2c KE2 C1 Hc; lia|]. split; [rewrite L5K.rl10, U10, EB; f_equal; f_equal; clear - G2c; lia| clear - C1 Hc; lia].
      * apply (L5SAR.ahpres_of L ar LB FF sp 20480 _ M M3).
        -- apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M M2 M3 EK02).
           apply (L5SAR.ek_W L ar LB FF sp 20480 _ [(os + 256, 40)] M2 M3 EK23). intros a O r0 [<-|[]] X. apply (O (os + 256, 40)); [left; reflexivity| exact X].
        -- pose proof ASTK3 as (_ & _ & _ & _ & DS3 & _). exact DS3.
        -- apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02). apply L5SAR.dk_grows. exact MGM3.
      * eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3|].
        eapply L5LZ.model_rt_trans; [exact MRT4| exact MRT5].
      * exact INC2.
      * exact INCA2.
      * exact AM5.
      * exact HH5.
Qed.

End WithHeap.
End PECPEEKB.
