(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnAEndDocP_b Ba0_code_ae750_ae754_b PnAEndDocK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAED.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNAEDK.

(* [comment removed for export] *)
Definition eregs (R R4 : bvmap 5 word) (sp fb F : Z) : Prop :=
  getr R4 (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R4 (reg 3) = getr R (reg 3) /\ getr R4 (reg 4) = getr R (reg 4)
  /\ getr R4 (reg 8) = Z_to_bv 64 sp /\ getr R4 (reg 9) = Z_to_bv 64 (sp - 160)
  /\ getr R4 (reg 20) = Z_to_bv 64 (fb + 464 + 400) /\ getr R4 (reg 21) = Z_to_bv 64 (fb + 464)
  /\ getr R4 (reg 24) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R4 (reg 25) = Z_to_bv 64 F /\ getr R4 (reg 26) = Z_to_bv 64 2147450880
  /\ getr R4 (reg 27) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880).
Lemma eregs_keep R R4 R5 sp fb F :
  eregs R R4 sp fb F -> (forall k, In k [2; 3; 4; 8; 9; 20; 21; 24; 25; 26; 27]%nat -> getr R5 (reg k) = getr R4 (reg k)) -> eregs R R5 sp fb F.
Proof.
  intros (E2 & E3 & E4 & E8 & E9 & E20 & E21 & E24 & E25 & E26 & E27) RK. unfold eregs.
  rewrite (RK 2%nat) by inl. rewrite (RK 3%nat) by inl. rewrite (RK 4%nat) by inl. rewrite (RK 8%nat) by inl. rewrite (RK 9%nat) by inl.
  rewrite (RK 20%nat) by inl. rewrite (RK 21%nat) by inl. rewrite (RK 24%nat) by inl. rewrite (RK 25%nat) by inl. rewrite (RK 26%nat) by inl. rewrite (RK 27%nat) by inl.
  repeat split; assumption.
Qed.
Lemma eregs_pres R R4 R5 sp fb F : eregs R R4 sp fb F -> regs_preserved R4 R5 -> eregs R R5 sp fb F.
Proof. intros ER RP. apply (eregs_keep R R4 R5 sp fb F ER). intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP). revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bstack_shape_pop l c top c' :
  PNRA.bstack_shape (l ++ [c; top]) -> PNM.bstate_ok c' -> PNM.bs_mode c' = PNM.bs_mode c -> PNRA.bstack_shape (l ++ [c']).
Proof.
  intros (L1 & L2 & B0 & CT & OK) OK' Hm. unfold PNRA.bstack_shape. rewrite length_app in *. cbn [length] in *.
  split; [lia|]. split; [lia|].
  split.
  { destruct l as [|x l']; cbn in B0 |- *; [rewrite Hm; exact B0| exact B0]. }
  split.
  { intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
    - rewrite nth_middle. rewrite Hm. pose proof (CT (length l) ltac:(lia)) as X. rewrite app_nth2 in X by lia. rewrite Nat.sub_diag in X. exact X.
    - rewrite app_nth1 by lia. pose proof (CT i ltac:(lia)) as X. rewrite app_nth1 in X by lia. exact X. }
  intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
  - rewrite nth_middle. exact OK'.
  - rewrite app_nth1 by lia. pose proof (OK i ltac:(lia)) as X. rewrite app_nth1 in X by lia. exact X.
Qed.
Lemma stack_two (stk : list PNM.bstate) : (2 <= length stk)%nat -> exists l c top, stk = l ++ [c; top].
Proof.
  intros H. destruct (exists_last (l := stk)) as (l1 & top & E1); [intros ->; cbn in H; lia|]. subst stk.
  rewrite length_app in H. cbn [length] in H.
  destruct (exists_last (l := l1)) as (l & c & E2); [intros ->; cbn in H; lia|]. subst l1.
  exists l, c, top. rewrite <- app_assoc. reflexivity.
Qed.
Lemma stack_ok l c top : PNRA.bstack_shape (l ++ [c; top]) -> PNM.bstate_ok c /\ PNM.bstate_ok top /\ Z.of_nat (length l) + 2 <= 1025.
Proof.
  intros (L1 & L2 & _ & _ & OKs). unfold PNM.MAX_DEPTH in L2. rewrite length_app in L2, OKs. cbn [length] in L2, OKs.
  pose proof (OKs (length l) ltac:(lia)) as OKc. rewrite nth_middle in OKc.
  pose proof (OKs (length l + 1)%nat ltac:(lia)) as OKt. rewrite app_nth2 in OKt by lia. rewrite Nat.add_comm, Nat.add_sub in OKt. cbn [nth] in OKt.
  split; [exact OKc|]. split; [exact OKt| lia].
Qed.

Lemma sh_le a b : a mod 8 = 0 -> b mod 8 = 0 -> a + 8 <= b -> a / 8 + 1 <= b / 8.
Proof.
  intros Ha Hb H. pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Ha in Da. rewrite Hb in Db. lia.
Qed.
Lemma sh_le128 a b : a mod 8 = 0 -> b mod 8 = 0 -> a + 128 <= b -> a / 8 + 16 <= b / 8.
Proof.
  intros Ha Hb H. pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Ha in Da. rewrite Hb in Db. lia.
Qed.
Lemma m32_8 a : a mod 32 = 0 -> a mod 8 = 0.
Proof. intros H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 32) with ((q * 4) * 8) by lia. apply Z_mod_mult. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma ed_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall model3,
      ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M1 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ KR.
  apply (PNAEDK.ed_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
           fx1 fx2 R1 R2 pc1 pc2 M2v (fun _ => False) CTX G LM MS MG).
  - intros a Ha _. exact (FRZ a Ha).
  - intros a [].
  - intros M3 model3 LM3 HID3 VIS3 FR3 MG3 ECK3.
    assert (EM31 : M3 = M1) by (apply PNBKA.mem_eq_of_agree; exact FR3). subst M3.
    exact (KR model3 LM3 HID3).
Qed.

(* [comment removed for export] *)
Lemma vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  6905856 <= fb + 432 <= 140737488355320 /\ (fb + 432) mod 8 = 0 /\ (2147446784 + 17592186048512 <= fb + 432 \/ (fb + 432) + 8 <= 2147446784)
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 432) / 8) + 2147450880) 1
  /\ ((sp - 160) + 160 <= fb + 432 \/ (fb + 432) + 8 <= (sp - 160)) /\ ((fb + 464) + 416 <= fb + 432 \/ (fb + 432) + 8 <= fb + 464)
  /\ (F + 128 <= fb + 432 \/ (fb + 432) + 8 <= F) /\ (fl + 1 <= fb + 432 \/ (fb + 432) + 8 <= fl)
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 432) 1251456
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) 2147607322 1
  /\ ((((fb + 432) / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= (((fb + 432) / 8) + 2147450880)).
Proof.
  intros CTX G LM.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold ed_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1.
  pose proof (PNAPAR.ov_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb HH1 FOK' VIS1) as VV. cbv zeta in VV.
  destruct VV as ((V1 & V8 & VNS) & VZ & VW & VCE & VU & _).
  assert (CLh : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 18432 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (APF : F + 128 <= fb + 432 \/ (fb + 432) + 8 <= F).
  { apply iv_apart; [clear; lia| clear; lia|]. intros a Ha X. apply (GNCF a); [left; exact Ha| apply CLh; clear - X; lia]. }
  pose proof (m32_8 F GF32) as F8.
  split; [exact V1|]. split; [exact V8|]. split; [exact VNS|]. split; [exact VZ|].
  split; [clear - VCE GSLO; lia|]. split; [right; clear; lia|].
  split; [exact APF|].
  split. { destruct (Z_lt_le_dec fl (fb + 432)) as [X|X]; [left; clear - X; lia|]. destruct (Z_lt_le_dec fl (fb + 432 + 8)) as [Y|Y]; [| right; clear - Y; lia].
           exfalso. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 18432). apply CLh. clear - X Y; lia. }
  split; [exact VU|].
  split; [exact (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LK1 cr1 Aw1 M1 model1 0x1318d0 1 HH1 ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia))|].
  destruct APF as [X|X].
  - right. pose proof (sh_le128 F (fb + 432) F8 V8 X) as Y. clear - Y. lia.
  - left. pose proof (sh_le (fb + 432) F V8 F8 X) as Y. clear - Y. lia.
Qed.

(* [comment removed for export] *)
Lemma mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 8) 1 /\ L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 10) 0
  /\ L5.u32_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 12) 0 /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 400) 8
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 392) (PNM.b_sb s1)
  /\ L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 8) (PNM.b_more s1).
Proof.
  intros CTX G LM.
  pose proof (PNAEDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM)
    as (PF & _ & _ & _ & WRop & U8op & _).
  unfold pfacts in PF. destruct PF as (_ & _ & _ & _ & _ & _ & pf7 & _).
  pose proof CTX as (_ & _ & _ & _ & _ & _ & _ & FOK & _).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof LM as (BI & RP1 & _).
  pose proof BI as (HH1 & _).
  pose proof RP1 as (PA1 & _ & _ & _ & OACC1 & _).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1. change (PNM.PSIZE + 8) with 424 in OACC1.
  assert (FOK' : PNRA.frame_okB ((F, 1, sp - 160 + 32) :: FF) fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as OPV. cbv zeta in OPV.
  destruct OPV as (_ & _ & _ & _ & OVIS & _).
  pose proof PA1 as (_ & _ & _ & MORE & _ & CM & ML & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
  destruct PVEC as (VC0 & _).
  split; [apply (L5.writable_sub RSEGS _ (fb + 464) 424); [exact WRop| clear; lia| clear; lia]|].
  split; [apply (proj2 (L5A.u8_at_vis _ M1 (fb + 464 + 10) 0 (OVIS (fb + 464 + 10) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia))); exact CM|].
  split; [apply (proj2 (L5A.u32_at_vis _ M1 (fb + 464 + 12) 0 (OVIS (fb + 464 + 12) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia))); exact ML|].
  split; [apply (L5.writable_sub RSEGS _ (fb + 464) 424); [exact WRop| clear; lia| clear; lia]|].
  split; [apply (proj2 (L5A.u64_at_vis _ M1 (fb + 464 + 392) _ (OVIS (fb + 464 + 392) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia))); exact VC0|].
  exact (proj2 (U8op _) MORE).
Qed.

(* [comment removed for export] *)
Lemma szfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 l c top :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNRA.binv s1 -> PNM.b_stk s1 = l ++ [c; top] ->
  L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 400) (PNM.b_sb s1 + 40 * (Z.of_nat (length l) + 2))
  /\ 4096 <= PNM.b_sb s1 <= 140737488355328 /\ (PNM.b_sb s1) mod 8 = 0
  /\ 80 <= 40 * (Z.of_nat (length l) + 2) <= 41000 /\ (40 * (Z.of_nat (length l) + 2)) mod 8 = 0
  /\ 2 <= sz64 (40 * (Z.of_nat (length l) + 2)) <= 1025 /\ 2 <= sz32 (40 * (Z.of_nat (length l) + 2)) <= 1025
  /\ sz64 (40 * (Z.of_nat (length l) + 2)) = Z.of_nat (length l) + 2.
Proof.
  intros CTX G LM INV1 ES.
  assert (ES' : PNM.b_stk s1 = (l ++ [c]) ++ [top]) by (rewrite ES, <- app_assoc; reflexivity).
  pose proof (PNAEDK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (l ++ [c]) top CTX G LM INV1 ES')
    as (TF & PT & OKt & VIN & TB1 & TB2 & TB3 & TB4).
  rewrite length_app in TF, TB1, TB2. cbn [length] in TF, TB1, TB2.
  replace (Z.of_nat (length l + 1)) with (Z.of_nat (length l) + 1) in TF, TB1, TB2 by (clear; lia).
  unfold tfacts in TF. destruct TF as (tf1 & tf2 & _ & tf4 & _).
  pose proof INV1 as (_ & SHAPE). rewrite ES in SHAPE. pose proof (stack_ok l c top SHAPE) as (_ & _ & LEN).
  set (n := Z.of_nat (length l)) in *. assert (Hn : 0 <= n) by (unfold n; clear; lia).
  pose proof (sz_ok (n + 2) ltac:(clear - Hn LEN; lia)) as (S64 & S32).
  pose proof LM as (_ & RP1 & _). pose proof RP1 as (PA1 & _). pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
  destruct PVEC as (_ & _ & _ & _ & _ & Hal & _).
  split; [replace (PNM.b_sb s1 + 40 * (n + 2)) with (PNM.b_sb s1 + 40 * (n + 1) + 40) by (clear; lia); exact tf1|].
  split; [clear - TB4 tf2 Hn; lia|].
  split; [apply PMKA.mod16_8'; exact Hal|].
  split; [clear - Hn LEN; lia|].
  split; [replace (40 * (n + 2)) with ((5 * (n + 2)) * 8) by (clear; lia); apply Z_mod_mult|].
  split; [rewrite S64; clear - Hn LEN; lia|]. split; [rewrite S32; clear - Hn LEN; lia| exact S64].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ed_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 :
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  eregs R R6 sp fb F -> getr R6 (reg 11) = Z_to_bv 64 F ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.bprog_pop R6 M6 s s6 sm sm6 -> PNRA.binv s6 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xafcb0 M6 model6) K.
Proof.
  intros CTX G LM ER X11 EC6 PROG INV6.
  pose proof (PNAEDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  destruct ER as (E2 & E3 & E4 & E8 & E9 & E20 & E21 & E24 & E25 & E26 & E27).
  unfold own in OWN6. destruct OWN6 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  pose proof (bvu_rng (getr R (reg 1))) as Q60.
  pose proof (bvu_rng (getr R (reg 8))) as Q61.
  pose proof (bvu_rng (getr R (reg 9))) as Q62.
  pose proof (bvu_rng (getr R (reg 18))) as Q63.
  pose proof (bvu_rng (getr R (reg 19))) as Q64.
  pose proof (bvu_rng (getr R (reg 20))) as Q65.
  pose proof (bvu_rng (getr R (reg 21))) as Q66.
  pose proof (bvu_rng (getr R (reg 22))) as Q67.
  pose proof (bvu_rng (getr R (reg 23))) as Q68.
  pose proof (bvu_rng (getr R (reg 24))) as Q69.
  pose proof (bvu_rng (getr R (reg 25))) as Q70.
  pose proof (bvu_rng (getr R (reg 26))) as Q71.
  pose proof (bvu_rng (getr R (reg 27))) as Q72.
  LeanFeed.pfeed P (PNAEDP.aedT_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNAEDP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _).
  assert (DF1 : 863232 <= F / 8) by (apply Z.div_le_lower_bound; clear - pf15; lia).
  assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - pf15; lia).
  pose proof LM as (_ & RP6 & _). pose proof RP6 as (PA6 & _). change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA6.
  pose proof PA6 as (_ & _ & _ & MORE6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MB6 & _).
  apply (PNAEDK.ed_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6
           fx6 fx9 R6 R9 0xafcb0 (PNM.b_more s6) M9v CTX G LM MS9 MG9).
  - intros a Ha N. apply FRZ9; [exact Ha| | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 1 / 8) with 16; unfold SB.
    + left; left; left. clear - X; lia.
    + left; left; right. clear - X; lia.
    + left; right. clear - X; lia.
  - exact FL0.
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia).
    apply (L5C.u8_at_agree RSEGS MV6 M9v); [| clear - pf7; lia| clear - pf7; lia| exact (proj2 (U8op6 _) MORE6)].
    intros j Hj. apply FRZ9; [clear - Hj pf7; lia| clear - Hj pf28; lia| clear - Hj pf9 DF1 DF2; lia| clear - Hj pf29; lia].
  - exact MB6.
  - exact Y2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - right. split; [exact EC6| exact PROG].
  - exact INV6.
Qed.

(* [comment removed for export] *)
Lemma ed_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ev ec :
  PNRAa.make_ec_spec L ar HI ->
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  eregs R R6 sp fb F -> spill M6 sp F (fb + 1024) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) ev ec ->
  getr R6 (reg 1) = Z_to_bv 64 0xafd90 ->
  getr R6 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R6 (reg 11) = Z_to_bv 64 13 ->
  getr R6 (reg 18) = Z_to_bv 64 (fb + 464 + 8) -> getr R6 (reg 23) = Z_to_bv 64 ((fb + 464 + 8) / 8 + 2147450880) ->
  PNRA.binv s6 -> (length (PNM.b_stk s) <= length (PNM.b_stk s6))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 (pa_make_ec PMA.AD) M6 model6) K.
Proof.
  intros MKE CTX G LM ER SPL EC6 X1 X10 X11 X18 X23 INV6 LEN6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof ER as (E2 & E3 & E4 & _).
  apply (PNAEDK.ed_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 R6 0xafd90 13 ev ec MKE CTX G LM EC6).
  { exact X1. } { unfold L5.ra_ok; clear; lia. } { exact E2. } { rewrite E3. exact Rgp. } { rewrite E4. exact Rtp. } { exact X10. } { exact X11. } { clear; lia. }
  intros fx7 R7 M7 model7 LK7 Aw7 RP7 EC7 LM7 AG7.
  pose proof (eregs_pres R R6 R7 sp fb F ER RP7) as ER7.
  pose proof (PNAEDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7)
    as (PF & OWN7 & SV7 & U8v7 & WRop7 & U8op7 & SVr7).
  set (MV7 := mrestrict (ahid Aw7 model7) M7) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  assert (SPL7 : spill M7 sp F (fb + 1024)) by (apply (PNAEDK.spill_agree M6 M7 sp F (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL| intros a Ha; apply AG7; clear - Ha; lia]).
  destruct SPL7 as (SPF7 & SPE7 & SPG7).
  pose proof (SV7 (sp - 144) F ltac:(clear; lia) ltac:(clear; lia) SPG7) as SPGv.
  assert (WRmo : L5.writable RSEGS MV7 (fb + 464 + 8) 1) by (apply (L5.writable_sub RSEGS MV7 (fb + 464) 424); [exact WRop7| clear; lia| clear; lia]).
  destruct ER7 as (E2' & E3' & E4' & E8 & E9 & E20 & E21 & E24 & E25 & E26 & E27).
  assert (E18 : getr R7 (reg 18) = Z_to_bv 64 (fb + 464 + 8)).
  { rewrite <- X18. apply (L5SAR.cs_of_preserved R6 R7 18%nat RP7). inl. }
  assert (E23 : getr R7 (reg 23) = Z_to_bv 64 ((fb + 464 + 8) / 8 + 2147450880)).
  { rewrite <- X23. apply (L5SAR.cs_of_preserved R6 R7 23%nat RP7). inl. }
  unfold own in OWN7. destruct OWN7 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  pose proof (bvu_rng (getr R (reg 1))) as Q60.
  pose proof (bvu_rng (getr R (reg 8))) as Q61.
  pose proof (bvu_rng (getr R (reg 9))) as Q62.
  pose proof (bvu_rng (getr R (reg 18))) as Q63.
  pose proof (bvu_rng (getr R (reg 19))) as Q64.
  pose proof (bvu_rng (getr R (reg 20))) as Q65.
  pose proof (bvu_rng (getr R (reg 21))) as Q66.
  pose proof (bvu_rng (getr R (reg 22))) as Q67.
  pose proof (bvu_rng (getr R (reg 23))) as Q68.
  pose proof (bvu_rng (getr R (reg 24))) as Q69.
  pose proof (bvu_rng (getr R (reg 25))) as Q70.
  pose proof (bvu_rng (getr R (reg 26))) as Q71.
  pose proof (bvu_rng (getr R (reg 27))) as Q72.
  LeanFeed.pfeed P (PNAEDP.aedE_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNAEDP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
  apply (PNAEDK.ed_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6
           fx7 fx9 R7 R9 0xafd90 0 M9v CTX G LM7 MS9 MG9).
  - intros a Ha N. apply FRZ9; [exact Ha| | | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 1 / 8) with 16; unfold SB.
    + right. clear - X; lia.
    + left; left; left. clear - X; lia.
    + left; left; right. clear - X; lia.
    + left; right. clear - X; lia.
  - exact FL0.
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO0.
  - left; reflexivity.
  - exact Y2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3'.
    + rewrite (KS9 4%nat) by inl. exact E4'.
  - left. exists 13. split; [clear; lia|]. split; [exact EC7|]. split; [reflexivity|]. split; [apply bax_cat_add| exact LEN6].
  - exact INV6.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ed_pop K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 l c top :
  PNSAX.ann_shrink_spec RSEGS PMA.AD L ar HI 0xab89c ->
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  eregs R R6 sp fb F -> spill M6 sp F (fb + 1024) ->
  getr R6 (reg 11) = Z_to_bv 64 (PNM.b_sb s6 + 40 * (Z.of_nat (length l) + 2) - 40) -> getr R6 (reg 12) = Z_to_bv 64 (PNM.b_sb s6 + 40 * (Z.of_nat (length l) + 2)) ->
  getr R6 (reg 18) = Z_to_bv 64 (PNM.bs_pos top) -> getr R6 (reg 19) = Z_to_bv 64 ((fb + 464 + 392) / 8 + 2147450880) -> getr R6 (reg 22) = Z_to_bv 64 (fb + 464 + 392) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat ->
  PNRA.binv s6 -> PNM.b_stk s6 = l ++ [c; top] -> PNM.b_stk s = l ++ [c; top] -> PM.unread (PNM.b_src s6) sm6 = PM.unread (PNM.b_src s) sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xafc60 M6 model6) K.
Proof.
  intros ASH CTX G LM ER SPL X11 X12 X18 X19 X22 EC6 INV6 ES6 ES UN6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNAEDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (_ & _ & _ & WR400 & B392 & _).
  pose proof (szfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 l c top CTX G LM INV6 ES6)
    as (B400 & SZb & SZal & SZm & SZm8 & _ & _ & SZE).
  pose proof (PNAEDK.pstk176_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (WR176 & D176o & D176F & D176l).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  set (b := PNM.b_sb s6) in *. set (n := Z.of_nat (length l)) in *. assert (Hn : 0 <= n) by (unfold n; clear; lia).
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E20 & E21 & E24 & E25 & E26 & E27).
  pose proof INV6 as (DN6 & SHAPE6). rewrite ES6 in SHAPE6. pose proof (stack_ok l c top SHAPE6) as (OKc & OKtop & LEN).
  assert (Q41 : 0 <= b < 2 ^ 64) by (clear - SZb; lia).
  assert (Q42 : 0 <= 40 * (n + 2) < 2 ^ 64) by (clear - SZm; lia).
  assert (Q41r : 4096 <= b <= 140737488355328) by exact SZb.
  LeanFeed.pfeed P (PNAEDP.aedP_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 41%nat => b | 42%nat => 40 * (n + 2) | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAEDP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & _ & U64).
  assert (Y11' : getr R7 (reg 11) = Z_to_bv 64 (n + 2)).
  { rewrite Y11. change (AX2.edenot _ _) with (mul_div Instr.M_MUL (Z_to_bv 64 (-3689348814741910323)) (alu64 Instr.ALU_SRA (Z_to_bv 64 (40 * (n + 2))) (Z_to_bv 64 3))).
    transitivity (Z_to_bv 64 (sz64 (40 * (n + 2)))); [| rewrite SZE; reflexivity]. unfold sz64. symmetry. apply Z_to_bv_bv_unsigned. }
  clear Y11.
  apply (PNAEDK.ed_call_shrink L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6
           fx6 fx7 R6 R7 0xafc60 0xafc68 M7v l c top ASH CTX G LM INV6 ES6 MS7 MG7).
  { intros a Ha N N2. apply FRZ7; [exact Ha| intros X; apply N; clear - X; lia| intros X; apply N2; clear - X; lia]. }
  { replace (fb + 864) with (fb + 464 + 400) by (clear; lia). fold b n. replace (b + 40 * (n + 1)) with (b + 40 * (n + 2) - 40) by (clear; lia). exact U64. }
  { exact Y1. } { unfold L5.ra_ok; clear; lia. } { rewrite (KS7 2%nat) by inl. exact E2. }
  { rewrite (KS7 3%nat) by inl. rewrite E3. exact Rgp. } { rewrite (KS7 4%nat) by inl. rewrite E4. exact Rtp. }
  { replace (fb + 856) with (fb + 464 + 392) by (clear; lia). exact Y10. }
  { fold n. exact Y11'. }
  intros fx8 R8 M8 model8 LK8 Aw8 RP8 LM8 AG8 ECK8.
  set (s8 := PNBO.set_stk s6 (l ++ [c])) in *.
  assert (INV8 : PNRA.binv s8).
  { unfold PNRA.binv, s8. cbn [PNBO.set_stk PNM.b_done PNM.b_stk]. split; [exact DN6|]. apply (bstack_shape_pop l c top c SHAPE6 OKc eq_refl). }
  assert (ES8 : PNM.b_stk s8 = l ++ [c]) by reflexivity.
  assert (R7k : forall k, In k [2; 3; 4; 8; 9; 18; 20; 21; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)).
  { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
  assert (ER7 : eregs R R7 sp fb F).
  { apply (eregs_keep R R6 R7 sp fb F ER). intros k Hk. apply R7k. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
  pose proof (eregs_pres R R7 R8 sp fb F ER7 RP8) as ER8.
  assert (X18' : getr R8 (reg 18) = Z_to_bv 64 (PNM.bs_pos top)).
  { rewrite (L5SAR.cs_of_preserved R7 R8 18%nat RP8) by inl. rewrite (R7k 18%nat) by inl. exact X18. }
  assert (SPL8 : spill M8 sp F (fb + 1024)) by (apply (PNAEDK.spill_agree M6 M8 sp F (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL| intros a Ha; apply AG8; clear - Ha; lia]).
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 pf33 pf34 OWN6 SV6 U8v6 WRop6 U8op6 SVr6 WR400.
  (* [comment removed for export] *)
  pose proof (PNAEDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm6 ax6 cr6 CTX G LM8)
    as (PF & OWN8 & SV8 & U8v8 & WRop8 & U8op8 & SVr8).
  pose proof (PNAEDK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm6 ax6 cr6 l c CTX G LM8 INV8 ES8)
    as (TF & PT8 & _ & _ & TB1 & TB2 & TB3 & TB4).
  unfold s8 in TF, TB1, TB2, TB3, TB4. cbn [PNBO.set_stk PNM.b_sb PNM.b_sk] in TF, TB1, TB2, TB3, TB4. fold b n in TF, TB1, TB2, TB3, TB4.
  set (MV8 := mrestrict (ahid Aw8 model8) M8) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  unfold tfacts in TF. destruct TF as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  destruct SPL8 as (SPF8 & SPE8 & SPG8).
  pose proof (SV8 (sp - 144) F ltac:(clear; lia) ltac:(clear; lia) SPG8) as SPGv.
  pose proof ER8 as (E2' & E3' & E4' & E8' & E9' & E20' & E21' & E24' & E25' & E26' & E27').
  pose proof OKtop as (_ & _ & POSt & _). pose proof OKc as (MODc & LENc & POSc & TYc & IDXc).
  assert (Q44 : 0 <= PNM.bs_pos top < 2 ^ 64) by exact POSt.
  LeanFeed.pfeed P (PNAEDP.aedQ1_conc fx8 R8 MV8 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 42%nat => b + 40 * n + 40 | 43%nat => PNM.bs_pos c | 44%nat => PNM.bs_pos top | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAEDP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z10 & Z11).
  apply (ed_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm6 ax6 cr6 fx8 fx9 R8 R9 0xafc68 0xafca8 M9v CTX G LM8 MS9 MG9 FRZ9).
  intros model9 LM9 HID9.
  assert (ER9 : eregs R R9 sp fb F).
  { apply (eregs_keep R R8 R9 sp fb F ER8). intros k Hk. apply KS9. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
  (* [comment removed for export] *)
  set (pos' := (PNM.bs_pos c + PNM.bs_pos top) mod 2 ^ 64).
  assert (Hp' : 0 <= pos' < 2 ^ 64) by (unfold pos'; apply Z.mod_pos_bound; clear; lia).
  assert (Q49 : 0 <= pos' <= 18446744073709551615) by (clear - Hp'; lia).
  assert (Z11' : getr R9 (reg 11) = Z_to_bv 64 pos') by (unfold pos'; rewrite zb_mod64; exact Z11).
  pose proof ER9 as (E2'' & E3'' & E4'' & E8'' & E9'' & E20'' & E21'' & E24'' & E25'' & E26'' & E27'').
  assert (MVE : mrestrict (ahid Aw8 model9) M8 = MV8) by (unfold MV8; rewrite HID9; reflexivity).
  LeanFeed.pfeed P (PNAEDP.aedQ2_conc fx9 R9 MV8 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 42%nat => b + 40 * n + 40 | 43%nat => PNM.bs_pos c | 49%nat => pos' | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAEDP.aligned; assumption]).
  destruct P as (fx10 & R10 & M10v & MG10 & _ & FRZ10 & MS10 & KS10 & X11F & U10).
  rewrite <- MVE in MS10, MG10, FRZ10.
  apply (PNAEDK.ed_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model9 LK8 Aw8 s8 sm6 ax6 cr6
           fx9 fx10 R9 R10 0xafca8 0xafcb0 M10v l c pos' CTX G LM9 INV8 ES8 MS10 MG10).
  { unfold s8. cbn [PNBO.set_stk PNM.b_sb]. fold b n. exact FRZ10. }
  { unfold s8. cbn [PNBO.set_stk PNM.b_sb]. fold b n. exact U10. }
  { exact Hp'. }
  intros M11 model11 LM11 HID11 VIS11 FR11 MG11 ECK11.
  set (c' := PNM.BS (PNM.bs_mode c) (PNM.bs_len c) pos' (PNM.bs_type c) (PNM.bs_idx c)) in *.
  set (s11 := PNBO.set_stk s8 (l ++ [c'])) in *.
  assert (OKc' : PNM.bstate_ok c') by (unfold PNM.bstate_ok, c'; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; repeat split; first [apply MODc | apply LENc | apply Hp' | apply TYc | apply IDXc]).
  apply (ed_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M11 model11 LK8 Aw8 s11 sm6 ax6 cr6 fx10 R10 CTX G LM11).
  - apply (eregs_keep R R9 R10 sp fb F ER9). intros k Hk. apply KS10. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity.
  - exact X11F.
  - exact (ECK11 _ _ (ECK8 _ _ EC6)).
  - unfold PNRA.bprog_pop. split.
    + exists l, c, top, c'. split; [exact ES|]. split; [reflexivity|]. split; [exact OKc'|]. unfold c'. cbn [PNM.bs_mode PNM.bs_len PNM.bs_type PNM.bs_idx]. repeat split.
    + unfold s11, s8. cbn [PNBO.set_stk PNM.b_src]. exact UN6.
  - unfold PNRA.binv, s11, s8. cbn [PNBO.set_stk PNM.b_done PNM.b_stk]. split; [exact DN6|]. apply (bstack_shape_pop l c top c' SHAPE6 OKc' eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ed_body K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 ax5 cr5 (fx5 : FPState) R5 :
  PNSAX.ann_shrink_spec RSEGS PMA.AD L ar HI 0xab89c -> PNRAa.make_ec_spec L ar HI ->
  ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  ed_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s sm ax5 cr5 ->
  eregs R R5 sp fb F -> getr R5 (reg 10) = Z_to_bv 64 F -> getr R5 (reg 23) = Z_to_bv 64 (fb + 432) ->
  L5.u64_at RSEGS M5 (sp - 136) (fb + 1024) ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xafaf8 M5 model5) K.
Proof.
  intros ASH MKE CTX G LM ER X10 X23 SPE5 EC5.
  pose proof CTX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ARGS & _ & _ & INV & _).
  destruct ARGS as (_ & LEN2).
  destruct (stack_two (PNM.b_stk s) LEN2) as (l & c & top & ES).
  pose proof INV as (DN & SHAPE). rewrite ES in SHAPE. pose proof (stack_ok l c top SHAPE) as (OKc & OKtop & LEN).
  pose proof (PNAEDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s sm ax5 cr5 CTX G LM)
    as (PF & OWN5 & SV5 & U8v5 & WRop5 & U8op5 & SVr5).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s sm ax5 cr5 CTX G LM)
    as (vf1 & vf2 & vf3 & vf4 & vf5 & vf6 & vf7 & vf8 & _).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s sm ax5 cr5 CTX G LM) as (_ & _ & _ & _ & B392 & _).
  pose proof (szfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s sm ax5 cr5 l c top CTX G LM INV ES)
    as (B400 & SZb & SZal & SZm & SZm8 & SZ64 & _ & _).
  unfold sz64 in SZ64.
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  set (b := PNM.b_sb s) in *. set (n := Z.of_nat (length l)) in *. assert (Hn : 0 <= n) by (unfold n; clear; lia).
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E20 & E21 & E24 & E25 & E26 & E27).
  assert (Q34 : 0 <= fb + 432 < 2 ^ 64) by (clear - vf1; lia).
  assert (Q41 : 0 <= b < 2 ^ 64) by (clear - SZb; lia).
  assert (Q42 : 0 <= 40 * (n + 2) < 2 ^ 64) by (clear - SZm; lia).
  LeanFeed.pfeed P (PNAEDP.aedC1_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 41%nat => b | 42%nat => 40 * (n + 2) | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAEDP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & _ & _ & _ & Y18 & Y19 & Y22 & S144 & S112).
  apply (PNAEDK.ed_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s sm ax5 cr5 fx5 fx6 R5 R6 0xafaf8 0xafb50 M6v
           (fun a => (sp - 112 <= a < sp - 112 + 8) \/ (sp - 144 <= a < sp - 144 + 8)) CTX G LM MS6 MG6).
  { intros a Ha N. apply FRZ6; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a [X|X]; clear - X; lia. }
  intros M6 model6 LM6 HID6 VIS6 FR6 MGM6 ECK6.
  pose proof (PNAEDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK5 Aw5 s sm ax5 cr5 CTX G LM6) as (_ & _ & SV6 & _ & _ & _ & SVr6).
  assert (SPL6 : spill M6 sp F (fb + 1024)).
  { unfold spill. pose proof SVr6 as SVr6'. rewrite HID6, VIS6 in SVr6'.
    split; [apply (SVr6' (sp - 112) F ltac:(clear; lia) ltac:(clear; lia)); exact S112|]. split; [| apply (SVr6' (sp - 144) F ltac:(clear; lia) ltac:(clear; lia)); exact S144].
    apply (L5C.u64_at_agree RSEGS M5 M6); [| clear - pf4; lia| clear - pf4; lia| exact SPE5].
    intros j Hj. apply FR6; [clear - Hj pf4; lia| clear - Hj; lia]. }
  assert (ER6 : eregs R R6 sp fb F).
  { apply (eregs_keep R R5 R6 sp fb F ER). intros k Hk. apply KS6. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
  assert (X23' : getr R6 (reg 23) = Z_to_bv 64 (fb + 432)) by (rewrite (KS6 23%nat) by inl; exact X23).
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 pf33 pf34 OWN5 SV5 U8v5 WRop5 U8op5 SVr5.
  clear vf1 vf2 vf3 vf4 vf5 vf6 vf7 vf8 B392 B400 SZ64 E2 E3 E4 E8 E9 E20 E21 E24 E25 E26 E27.
  (* [comment removed for export] *)
  pose proof (PNAEDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK5 Aw5 s sm ax5 cr5 CTX G LM6)
    as (PF & _).
  pose proof (vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK5 Aw5 s sm ax5 cr5 CTX G LM6)
    as (vf1 & vf2 & vf3 & vf4 & vf5 & vf6 & vf7 & vf8 & vf9 & vf10 & vf11).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK5 Aw5 s sm ax5 cr5 CTX G LM6) as (WRmo & CM0 & ML0 & _ & B392 & _).
  pose proof (szfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK5 Aw5 s sm ax5 cr5 l c top CTX G LM6 INV ES)
    as (B400 & _ & _ & _ & _ & _ & SZ32 & _).
  unfold sz32 in SZ32. fold b n in B392, B400, SZ32.
  set (MV6 := mrestrict (ahid Aw5 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  pose proof ER6 as (E2 & E3 & E4 & E8 & E9 & E20 & E21 & E24 & E25 & E26 & E27).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  pose proof SPL6 as (SPF6 & SPE6 & SPG6).
  pose proof (SV6 (sp - 136) (fb + 1024) ltac:(clear; lia) ltac:(clear; lia) SPE6) as SPEv.
  LeanFeed.pfeed P (PNAEDP.aedV_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 41%nat => b | 42%nat => 40 * (n + 2) | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAEDP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _ & _ & _ & Y15 & Y23 & MO7).
  apply (PNAEDK.ed_piece_more L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK5 Aw5 s sm ax5 cr5 fx6 fx7 R6 R7 0xafb50 0xafc08 M7v 1
           CTX G LM6 MS7 MG7).
  { intros a Ha N. apply FRZ7; [exact Ha|]. intros X. apply N. clear - X; lia. }
  { replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO7. }
  { right; reflexivity. }
  intros M7 model7 LM7 HID7 VIS7 FR7 MGM7 ECK7.
  set (s7 := PNBO.set_more s 1) in *.
  assert (INV7 : PNRA.binv s7) by (unfold PNRA.binv, s7; cbn [PNBO.set_more PNM.b_done PNM.b_stk]; exact INV).
  assert (ES7 : PNM.b_stk s7 = l ++ [c; top]) by (unfold s7; cbn [PNBO.set_more PNM.b_stk]; exact ES).
  assert (ES7' : PNM.b_stk s7 = (l ++ [c]) ++ [top]) by (rewrite ES7, <- app_assoc; reflexivity).
  assert (SPL7 : spill M7 sp F (fb + 1024)).
  { apply (PNAEDK.spill_agree M6 M7 sp F (fb + 1024)); [clear - pf4; lia| clear - pf4; lia| exact SPL6|]. intros a Ha. apply FR7; [clear - Ha pf4; lia| clear - Ha pf14; lia]. }
  assert (R7k : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)).
  { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
  assert (ER7 : eregs R R7 sp fb F).
  { apply (eregs_keep R R6 R7 sp fb F ER6). intros k Hk. apply R7k. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
  assert (X19 : getr R7 (reg 19) = Z_to_bv 64 ((fb + 464 + 392) / 8 + 2147450880)) by (rewrite (R7k 19%nat) by inl; exact Y19).
  assert (X18 : getr R7 (reg 18) = Z_to_bv 64 14757395258967641293) by (rewrite (R7k 18%nat) by inl; exact Y18).
  assert (X22 : getr R7 (reg 22) = Z_to_bv 64 (fb + 464 + 392)) by (rewrite (R7k 22%nat) by inl; exact Y22).
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 pf33 pf34 SV6 SVr6.
  clear vf1 vf2 vf3 vf4 vf5 vf6 vf7 vf8 vf9 vf10 vf11 B392 B400 SZ32 E2 E3 E4 E8 E9 E20 E21 E24 E25 E26 E27 WRmo CM0 ML0 SPF6 SPE6 SPG6 SPEv.
  (* [comment removed for export] *)
  pose proof (PNAEDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm ax5 cr5 CTX G LM7)
    as (PF & _ & SV7 & _).
  pose proof (PNAEDK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm ax5 cr5 (l ++ [c]) top CTX G LM7 INV7 ES7')
    as (TF & _).
  pose proof (PNAEDK.tlen_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm ax5 cr5 (l ++ [c]) top CTX G LM7 INV7 ES7')
    as (TL1 & TL2 & TL3).
  rewrite length_app in TF, TL1, TL2. cbn [length] in TF, TL1, TL2.
  replace (Z.of_nat (length l + 1)) with (n + 1) in TF, TL1, TL2 by (unfold n; clear; lia).
  unfold s7 in TF, TL1, TL2. cbn [PNBO.set_more PNM.b_sb] in TF, TL1, TL2. fold b in TF, TL1, TL2.
  set (MV7 := mrestrict (ahid Aw5 model7) M7) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
  unfold tfacts in TF. destruct TF as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  pose proof ER7 as (E2 & E3 & E4 & E8 & E9 & E20 & E21 & E24 & E25 & E26 & E27).
  pose proof SPL7 as (SPF7 & SPE7 & SPG7).
  pose proof (SV7 (sp - 136) (fb + 1024) ltac:(clear; lia) ltac:(clear; lia) SPE7) as SPEv.
  LeanFeed.pfeed P (PNAEDP.aedC_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 36%nat => fb + 1024 | 41%nat => b | 42%nat => b + 40 * (n + 1) + 40 | 43%nat => PNM.bs_pos top | 44%nat => PNM.bs_len top | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAEDP.aligned; assumption]).
  destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & [(MS8 & KS8 & Z1 & Z10 & Z11 & _ & _ & Z18 & CND)|(MS8 & KS8 & _ & Z11 & Z12 & _ & Z18 & CND)]).
  - (* [comment removed for export] *)
    apply (ed_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm ax5 cr5 fx7 fx8 R7 R8 0xafc08 (pa_make_ec PMA.AD) M8v CTX G LM7 MS8 MG8 FRZ8).
    intros model8 LM8 HID8.
    apply (ed_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model8 LK5 Aw5 s7 sm ax5 cr5 fx8 R8 e cat MKE CTX G LM8).
    + apply (eregs_keep R R7 R8 sp fb F ER7). intros k Hk. apply KS8. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity.
    + exact SPL7.
    + exact (ECK7 _ _ (ECK6 _ _ EC5)).
    + exact Z1.
    + exact Z10.
    + exact Z11.
    + exact Z18.
    + rewrite (KS8 23%nat) by inl. exact Y23.
    + exact INV7.
    + rewrite ES7, ES. apply Nat.le_refl.
  - (* [comment removed for export] *)
    apply (ed_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm ax5 cr5 fx7 fx8 R7 R8 0xafc08 0xafc60 M8v CTX G LM7 MS8 MG8 FRZ8).
    intros model8 LM8 HID8.
    apply (ed_pop K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model8 LK5 Aw5 s7 sm ax5 cr5 fx8 R8 l c top ASH CTX G LM8).
    + apply (eregs_keep R R7 R8 sp fb F ER7). intros k Hk. apply KS8. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity.
    + exact SPL7.
    + unfold s7. cbn [PNBO.set_more PNM.b_sb]. fold b n. replace (b + 40 * (n + 2) - 40) with (b + 40 * (n + 1) + 40 - 40) by (clear; lia). exact Z11.
    + unfold s7. cbn [PNBO.set_more PNM.b_sb]. fold b n. replace (b + 40 * (n + 2)) with (b + 40 * (n + 1) + 40) by (clear; lia). exact Z12.
    + exact Z18.
    + rewrite (KS8 19%nat) by inl. exact X19.
    + rewrite (KS8 22%nat) by inl. exact X22.
    + exact (ECK7 _ _ (ECK6 _ _ EC5)).
    + exact INV7.
    + exact ES7.
    + exact ES.
    + reflexivity.
Qed.


(* [comment removed for export] *)
Theorem end_document_ok : PNSAX.ann_shrink_spec RSEGS PMA.AD L ar HI 0xab89c -> PNRAa.make_ec_spec L ar HI -> PNRAa.end_document_spec L ar HI.
Proof.
  intros ASH MKE. unfold PNRAa.end_document_spec, PNRA.end_document_spec, PNRA.brun_spec.
  set (w := 0). assert (Hw : w = 0 \/ w = 1) by (left; reflexivity).
  intros fx R M model K LBX FF LK Aw cr sp r fb cat e s str sm ax HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC HE UNR CRED KONT.
  assert (CTX : ed_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w).
  { exact (conj Hw (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj FOK (conj SP32 (conj ARGS (conj RPRE (conj INCS (conj INV (conj EC (conj HE (conj UNR (conj CRED KONT))))))))))))))))). }
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *. change (18432 / 8) with 2304 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct ARGS as ((A10 & A11 & A12) & LEN2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  pose proof RPRE as (PA & IA & VIS & VREF & OACC & BASE & ERR & GROW).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_ec PMA.AD fb) with (fb + 1024) in *.
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA OACC) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm sp 18432 HH) as ISV.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 18432 160 HH ASTK ltac:(lia)) as (SL160 & SH160 & SWR).
  set (op := fb + 464) in *. set (ov := fb + 432) in *. set (oec := fb + 1024) in *. set (ois := fb + 96) in *.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
  LeanFeed.pfeed P (PNAEDP.aedA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 36%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PNAEDP.aligned; assumption | clear - SL160 SHI SPT; lia | clear - O1; lia | unfold oec, ov, op in *; clear - O1; lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T21 & T23 & T26
                 & SPEv & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C160).
  unfold PMSP.cfg. change (PNL.pn_end_document PMA.AN) with 0xaf9e0.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xaf9e0 R1 0x5dda0 M1v (fun a => sp - 160 <= a < sp - 160 + 160) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X; clear - X Wa SL160 FSAPP FSCEIL; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL160 SHI SPT; lia| intros X; clear - X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  set (LB := PNM.bparser_own s ++ LBX) in *.
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (NCS0 : forall a, sp - 160 <= a < sp -> ~ aclient L ar LB FF sp 18432 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 18432 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL160; lia. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 18432 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 18432 [] M M1 (fun a => sp - 160 <= a < sp - 160 + 160) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 18432 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 18432 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 18432 M M1 INCX DK01f) as DK01.
  (* [comment removed for export] *)
  assert (SV1 : forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X. }
  assert (OWN1 : own sp R M1).
  { unfold own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  assert (SPE1 : L5.u64_at RSEGS M1 (sp - 136) oec) by (apply SV1; [clear; lia| clear; lia| exact SPEv]).
  clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 SV1.
  (* [comment removed for export] *)
  assert (FRk0 : ff_room 1 FF LK) by (apply (PMAUAR.ff_room_ofB PNRA.FCB 3 FF LK 1 FRM); [clear; lia| right; left; reflexivity]).
  change 0x5dda0 with (PMA.SM_PC 1).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 1 LBX (PNM.bparser_own s) FF LK cr Aw sp 18432 (sp - 160) (sp - 104) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xafa58 ltac:(right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 160) with (sp + (-10) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk0. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. change (128 - 8) with 120 in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *.
  pose proof (L5SAR.ek_trans L ar LB FF sp 18432 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 18432 M M1 M2 DK01f DK12f) as DK02f.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (HH2 : ri_inv HI LB ((F, 1, sp - 160 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 1, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 18432 160 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
  (* [comment removed for export] *)
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B21R : getr R2 (reg 21) = Z_to_bv 64 op) by (rewrite (R2c 21%nat) by inl; exact T21).
  assert (B23R : getr R2 (reg 23) = Z_to_bv 64 ov) by (rewrite (R2c 23%nat) by inl; exact T23).
  assert (B26R : getr R2 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R2c 26%nat) by inl; exact T26).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 120) fl) by (replace (F + 120) with (F + 128 - 8) by (clear; lia); exact FLC).
  assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
    by (clear - SL160 SHI SPT O1 GFR GFLR; unfold ov, op in *; lia).
  destruct Q0 as (Q0a & Q0b & Q0d & Q0f & Q0g).
  assert (Q1 : 140735332487328 <= sp <= 140737488355328) by (clear - SL160 SHI SPT; lia).
  assert (Qop : 6905856 <= op <= 140737488354912) by (clear - O1; lia).
  assert (Q3 : 6905856 <= F <= 140737488355200) by (clear - GFR; lia).
  assert (Q4 : (sp - 160) + 160 <= F \/ F + 128 <= (sp - 160)) by (clear - GFCEIL SL160; lia).
  assert (Q5 : (sp - 160) + 160 <= fl \/ fl + 1 <= (sp - 160)) by (clear - GFLR SL160; lia).
  assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
  LeanFeed.pfeed P (PNAEDP.aedB0_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => ov | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNAEDP.aligned; assumption]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y10 & _ & _ & _ & _ & _ & _ & Y20 & Y24 & Y25 & Y27
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SH0 & _).
  set (W3 := fun a => (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 12)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xafa58 R3 0xafaf8 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; clear - X; lia| intros X; apply Hn; right; clear - X; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|X].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 1 (sp - 160 + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - X; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 1 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
    - destruct Wa as [X|X]; clear - X GFR SL160 SPT FSAPP FSCEIL; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23f : L5SAR.ek L ar LB FF sp 18432 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 18432 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|X].
    - destruct (APART a 1 sp 18432 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
    - destruct (APART a 1 sp 18432 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 18432 [] M M2 M3 EK02f EK23f) as EK03f.
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M1 M3 ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL160 SHI SPT; lia| intros [X|X]; clear - X Ha GFCEIL GFR SL160 SPT; unfold SB in *; lia]. }
  assert (SPE3 : L5.u64_at RSEGS M3 (sp - 136) oec).
  { apply (L5C.u64_at_agree RSEGS M1 M3); [| clear - SL160 SPT; lia| clear - SHI SPT; lia| exact SPE1]. intros a Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL160 SHI SPT; lia| intros [X|X]; clear - X Ha GFCEIL GFR SL160 SPT; unfold SB in *; lia]. }
  assert (WAPPR : PMKA.wapp (PNRA.W_brun PMA.AD PMA.AN fb)).
  { unfold PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 18432 (sp - 160) (own sp R) F 1 WR (PNM.bparser_own s) M3 model3 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 18432 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 18432 WR [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 18432 [] M M3 INCX EK03f)); intros a _ r0 []|].
    split; [apply (L5SAR.dk_trans L ar LBX FF sp 18432 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
    split; [exact OWN3|].
    change (ff_bytes 1 / 8) with 16. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 16 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (R1c : forall j, In j [3; 4]%nat -> getr R1 (reg j) = getr R (reg j)).
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
  (* [comment removed for export] *)
  assert (AOPp : PMSPA.aobjA FF op PNM.PSIZE) by (apply (PNAPAR.aobj_fbB FF fb op PNM.PSIZE FOK); unfold op, PNM.PSIZE; clear; lia).
  assert (PA3 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M3 op ois s).
  { apply (PNAPAR.bparser_keepA L ar C HI HIok LB FF LK cr Aw (vml_of model) [] sp 18432 M M3 op ois s HH EK03f PMKA.wapp_nil AOPp);
      [unfold LB; apply incl_appl; apply incl_refl| intros i _ r0 []| intros B m _ i _ r0 []| exact PA]. }
  assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 18432 [] M M3 EK03f PMKA.wapp_nil FRB BRB ois str sm); [| | intros i _ r0 []| intros c n p _ i _ r0 []| exact IA].
    - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - unfold LB. apply incl_appr. exact INCS. }
  assert (EC3 : PMSPA.ec_at RSEGS M3 oec e cat).
  { apply (PMKA.ec_keepA RSEGS L ar LB FF sp 18432 [] M M3 EK03f PMKA.wapp_nil FRB oec e cat); [| intros i _ r0 []| exact EC].
    apply (PNAPAR.aobj_fbB FF fb oec 16 FOK); unfold oec; clear; lia. }
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3) by (apply (PMASK.base_keep L ar C LY LB FF sp 18432 [] M M3 EK03f); [intros a _ r0 []| exact BASE]).
  assert (ERR3 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M3 ax).
  { apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M M3); [| exact ERR].
    intros a Ha D. apply EK03f. split; [exact Ha|]. split; [| intros r0 []]. unfold aclient, aclient_g. right; right; left.
    pose proof (depA_img a D). rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| exact (PMA.ly_static L C LY a D)]. }
  assert (AV0 : avis H2 (F / 8 + 2147450880) 1) by (apply (L5A.avis_sub H2 (F / 8 + SB) 16); [exact VSH| unfold SB; clear; lia| unfold SB; clear; lia]).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - Q3; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - Q3; pose proof (Z.div_le_upper_bound F 8 17592186044400 ltac:(lia) ltac:(lia)); lia).
  pose proof (L5A.u8_at_vis H2 M3 (F / 8 + 2147450880) 241 AV0 R4a R4b) as UV. rewrite VIS3 in UV.
  assert (U8c : L5.u8_at RSEGS M3 (F / 8 + 2147450880) 241) by (apply (proj1 UV); exact SH0). clear UV.
  (* [comment removed for export] *)
  assert (PRE3 : PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M3 fb s str sm ax).
  { refine (PNBKA.pre_after_call L ar LB FF sp 18432 [] M M3 fb s s str sm sm ax ax FRB EK03f PMKA.wapp_nil FOK _ RPRE PA3 IA3 GROW BASE3 ERR3). intros i _ rr []. }
  assert (LM3 : ed_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK2 Aw s sm ax cr).
  { unfold ed_mem. split; [exact BI3|]. split; [exact PRE3|]. split; [apply PNBKA.src_step_refl|]. split; [apply PNST.bax_le_refl|].
    split; [apply PNBKA.credit_keep_refl|]. split; [exact U8c| reflexivity]. }
  unfold op, ov, oec, ois in *. clear op ov oec ois.
  assert (R3gp : getr R3 (reg 3) = getr R (reg 3)) by (rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply R1c; inl).
  assert (R3tp : getr R3 (reg 4) = getr R (reg 4)) by (rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply R1c; inl).
  apply (ed_body K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw ax cr fx3 R3 ASH MKE CTX G LM3).
  - unfold eregs.
    split; [rewrite (KS3 2%nat) by inl; exact B2R|]. split; [exact R3gp|]. split; [exact R3tp|].
    split; [rewrite (KS3 8%nat) by inl; exact B8R|]. split; [rewrite (KS3 9%nat) by inl; exact B9R|].
    split; [exact Y20|]. split; [rewrite (KS3 21%nat) by inl; exact B21R|]. split; [exact Y24|]. split; [exact Y25|].
    split; [rewrite (KS3 26%nat) by inl; exact B26R| exact Y27].
  - exact Y10.
  - rewrite (KS3 23%nat) by inl. exact B23R.
  - exact SPE3.
  - exact EC3.
Qed.
End WithHeap.
End PNAED.
