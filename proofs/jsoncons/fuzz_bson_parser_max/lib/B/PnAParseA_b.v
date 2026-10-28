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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcKitA_b PnBrKitA_b PnAParseP_b PnAParseP2_b Ba0_code_ad390_ad394_b PnAParseK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAPAA.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNAPAK.

(* [comment removed for export] *)
Definition lregs (R R4 : bvmap 5 word) (sp fb F : Z) : Prop :=
  getr R4 (reg 2) = Z_to_bv 64 (sp - 256) /\ getr R4 (reg 3) = getr R (reg 3) /\ getr R4 (reg 4) = getr R (reg 4)
  /\ getr R4 (reg 8) = Z_to_bv 64 sp /\ getr R4 (reg 9) = Z_to_bv 64 (sp - 256)
  /\ getr R4 (reg 18) = Z_to_bv 64 2147450880 /\ getr R4 (reg 19) = Z_to_bv 64 (fb + 464 + 392)
  /\ getr R4 (reg 20) = Z_to_bv 64 40 /\ getr R4 (reg 21) = Z_to_bv 64 143316 /\ getr R4 (reg 22) = Z_to_bv 64 (fb + 432)
  /\ getr R4 (reg 23) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R4 (reg 24) = Z_to_bv 64 (fb + 464 + 9) /\ getr R4 (reg 25) = Z_to_bv 64 (fb + 464 + 400)
  /\ getr R4 (reg 26) = Z_to_bv 64 (fb + 464) /\ getr R4 (reg 27) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880).
Definition LREGS : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma lregs_keep R R4 R5 sp fb F :
  lregs R R4 sp fb F -> (forall k, In k LREGS -> getr R5 (reg k) = getr R4 (reg k)) -> lregs R R5 sp fb F.
Proof.
  intros (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) RK. unfold lregs, LREGS in *.
  rewrite (RK 2%nat) by inl. rewrite (RK 3%nat) by inl. rewrite (RK 4%nat) by inl. rewrite (RK 8%nat) by inl. rewrite (RK 9%nat) by inl.
  rewrite (RK 18%nat) by inl. rewrite (RK 19%nat) by inl. rewrite (RK 20%nat) by inl. rewrite (RK 21%nat) by inl. rewrite (RK 22%nat) by inl.
  rewrite (RK 23%nat) by inl. rewrite (RK 24%nat) by inl. rewrite (RK 25%nat) by inl. rewrite (RK 26%nat) by inl. rewrite (RK 27%nat) by inl.
  repeat split; assumption.
Qed.
Lemma lregs_pres R R4 R5 sp fb F : lregs R R4 sp fb F -> regs_preserved R4 R5 -> lregs R R5 sp fb F.
Proof. intros ER RP. apply (lregs_keep R R4 R5 sp fb F ER). intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP). revert k Hk. apply (L5K.incl_b LREGS). vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma lregs_ks R R4 R5 sp fb F (KS : list nat) :
  lregs R R4 sp fb F -> (forall k, In k KS -> getr R5 (reg k) = getr R4 (reg k)) -> forallb (fun i => existsb (Nat.eqb i) KS) LREGS = true -> lregs R R5 sp fb F.
Proof. intros ER RK IB. apply (lregs_keep R R4 R5 sp fb F ER). intros k Hk. apply RK. revert k Hk. apply (L5K.incl_b LREGS KS). exact IB. Qed.

(* [comment removed for export] *)
Lemma bflag_app l c : PNRA.bflag (l ++ [c]) = (if (Z.eqb (PNM.bs_mode c) 0 || Z.eqb (PNM.bs_mode c) 4)%bool then 1 else 0).
Proof. unfold PNRA.bflag. rewrite last_last. reflexivity. Qed.
Lemma bflag_range stk : 0 <= PNRA.bflag stk <= 1.
Proof. unfold PNRA.bflag. destruct (_ || _)%bool; lia. Qed.
Lemma shape_bottom_nil l c : PNRA.bstack_shape (l ++ [c]) -> PNRA.bmode_bottom (PNM.bs_mode c) -> l = [].
Proof.
  intros (L1 & L2 & B0 & CT & OK) Hm. destruct l as [|x l']; [reflexivity|]. exfalso.
  pose proof (CT (length (x :: l')) ltac:(rewrite length_app; cbn; lia)) as X. rewrite nth_middle in X.
  unfold PNRA.bmode_bottom in Hm. unfold PNRA.bmode_cont in X. lia.
Qed.
Lemma shape_cont_cons l c : PNRA.bstack_shape (l ++ [c]) -> PNRA.bmode_cont (PNM.bs_mode c) -> l <> [].
Proof.
  intros (L1 & L2 & B0 & CT & OK) Hm E. subst l. cbn in B0. unfold PNRA.bmode_bottom in B0. unfold PNRA.bmode_cont in Hm. lia.
Qed.
Lemma shape_top_mode l c c' :
  PNRA.bstack_shape (l ++ [c]) -> PNM.bstate_ok c' ->
  (l = [] -> PNRA.bmode_bottom (PNM.bs_mode c')) -> (l <> [] -> PNRA.bmode_cont (PNM.bs_mode c')) -> PNRA.bstack_shape (l ++ [c']).
Proof.
  intros (L1 & L2 & B0 & CT & OK) OK' HB HC. unfold PNRA.bstack_shape. rewrite length_app in *. cbn [length] in *.
  split; [lia|]. split; [lia|].
  split.
  { destruct l as [|x l']; cbn in B0 |- *; [apply HB; reflexivity| exact B0]. }
  split.
  { intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
    - rewrite nth_middle. apply HC. intros E. subst l. cbn in Hi. lia.
    - rewrite app_nth1 by lia. pose proof (CT i Hi) as X. rewrite app_nth1 in X by lia. exact X. }
  intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
  - rewrite nth_middle. exact OK'.
  - rewrite app_nth1 by lia. pose proof (OK i Hi) as X. rewrite app_nth1 in X by lia. exact X.
Qed.
Lemma stack_top (stk : list PNM.bstate) : PNRA.bstack_shape stk -> exists l c, stk = l ++ [c] /\ PNM.bstate_ok c /\ Z.of_nat (length l) + 1 <= 1025.
Proof.
  intros (L1 & L2 & _ & _ & OKs). unfold PNM.MAX_DEPTH in L2.
  destruct (exists_last (l := stk)) as (l & c & E); [intros ->; cbn in L1; lia|]. subst stk.
  rewrite length_app in L2, OKs. cbn [length] in L2, OKs.
  pose proof (OKs (length l) ltac:(lia)) as OKc. rewrite nth_middle in OKc.
  exists l, c. split; [reflexivity|]. split; [exact OKc| lia].
Qed.
(* [comment removed for export] *)
Lemma bb_room_keep (s s' : PNM.bpst) sm sm' :
  PNM.b_bb s' = PNM.b_bb s -> PM.unread (PNM.b_src s') sm' <= PM.unread (PNM.b_src s) sm -> PNRA.bb_room s sm -> PNRA.bb_room s' sm'.
Proof. unfold PNRA.bb_room. intros E LE H. rewrite E. exact (PGV8.v8_room_mono _ _ _ LE H). Qed.

Lemma sh_le a b : a mod 8 = 0 -> b mod 8 = 0 -> a + 8 <= b -> a / 8 + 1 <= b / 8.
Proof.
  intros Ha Hb H. pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Ha in Da. rewrite Hb in Db. lia.
Qed.
Lemma sh_lek a b k : a mod 8 = 0 -> b mod 8 = 0 -> 0 <= k -> a + 8 * k <= b -> a / 8 + k <= b / 8.
Proof.
  intros Ha Hb Hk H. pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Ha in Da. rewrite Hb in Db. lia.
Qed.
Lemma m32_8 a : a mod 32 = 0 -> a mod 8 = 0.
Proof. intros H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 32) with ((q * 4) * 8) by lia. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
Definition hfacts (MV : mem) (e m t : Z) : Prop :=
  L5.u32_at RSEGS MV (e - 40) m /\ L5KA.zeros_at MV (((e - 40) / 8) + 2147450880) 1 /\ L5.writable RSEGS MV (e - 40) 4
  /\ L5.u8_at RSEGS MV (e - 16) t /\ L5KA.zeros_at MV (((e - 16) / 8) + 2147450880) 1 /\ L5.writable RSEGS MV (e - 16) 1
  /\ 0 <= m < 2 ^ 64 /\ 0 <= t <= 255 /\ 0 <= t < 2 ^ 64.
(* [comment removed for export] *)
Definition ec_some (M : mem) (fb : Z) : Prop := exists e c, 0 <= e <= 64 /\ PMSPA.ec_at RSEGS M (fb + 1024) e c.

(* [comment removed for export] *)
Definition vmx (R : bvmap 5 word) (sp fb F fl v40 v41 v42 v43 v44 v45 v46 v49 : Z) : nat -> Z :=
  fun j => match j with
           | 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 37%nat => fb + 96
           | 40%nat => v40 | 41%nat => v41 | 42%nat => v42 | 43%nat => v43 | 44%nat => v44 | 45%nat => v45 | 46%nat => v46 | 49%nat => v49
           | 50%nat => F | 51%nat => fl
           | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18))
           | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22))
           | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26))
           | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end.

(* [comment removed for export] *)
Ltac pfx PF :=
  unfold pfacts in PF;
  destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32 & pf33 & pf34).
Ltac tfx TF := unfold tfacts in TF; destruct TF as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
Ltac hfx HF := unfold hfacts in HF; destruct HF as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9).
Ltac spx SP := unfold spill in SP; destruct SP as (sv1 & sv2 & sv3 & sv4 & sv5 & sv6 & sv7 & sv8 & sv9 & sv10 & sv11 & sv12 & sv13).
Ltac lrx ER := destruct ER as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
Ltac owx OW := unfold own in OW; destruct OW as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
Ltac qsx R :=
  pose proof (bvu_rng (getr R (reg 1))) as Q60; pose proof (bvu_rng (getr R (reg 8))) as Q61; pose proof (bvu_rng (getr R (reg 9))) as Q62;
  pose proof (bvu_rng (getr R (reg 18))) as Q63; pose proof (bvu_rng (getr R (reg 19))) as Q64; pose proof (bvu_rng (getr R (reg 20))) as Q65;
  pose proof (bvu_rng (getr R (reg 21))) as Q66; pose proof (bvu_rng (getr R (reg 22))) as Q67; pose proof (bvu_rng (getr R (reg 23))) as Q68;
  pose proof (bvu_rng (getr R (reg 24))) as Q69; pose proof (bvu_rng (getr R (reg 25))) as Q70; pose proof (bvu_rng (getr R (reg 26))) as Q71;
  pose proof (bvu_rng (getr R (reg 27))) as Q72.
(* [comment removed for export] *)
Ltac pfeed P := unfold vmx in P; cbn beta iota in P; L5SAR.feed P ltac:(first [assumption | unfold PNAPAP.aligned, PNAPAP2.aligned; assumption]).
(* [comment removed for export] *)
Ltac lrk ER KS := apply (lregs_keep _ _ _ _ _ _ ER); intros k Hk; apply KS; revert k Hk; apply L5K.incl_b; vm_compute; reflexivity.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma pa_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) :
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall model3,
      pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M1 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ KR.
  apply (PNAPAK.pa_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
           fx1 fx2 R1 R2 pc1 pc2 M2v (fun _ => False) CTX G LM MS MG).
  - intros a Ha _. exact (FRZ a Ha).
  - intros a [].
  - intros M3 model3 LM3 HID3 VIS3 FR3 MG3 ECK3.
    assert (EM31 : M3 = M1) by (apply PNBKA.mem_eq_of_agree; exact FR3). subst M3.
    exact (KR model3 LM3 HID3).
Qed.

(* [comment removed for export] *)
Lemma vfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  6905856 <= fb + 432 <= 140737488355320 /\ (fb + 432) mod 8 = 0 /\ (2147446784 + 17592186048512 <= fb + 432 \/ (fb + 432) + 8 <= 2147446784)
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 432) / 8) + 2147450880) 1
  /\ ((sp - 256) + 256 <= fb + 432 \/ (fb + 432) + 8 <= (sp - 256)) /\ ((fb + 464) + 416 <= fb + 432 \/ (fb + 432) + 8 <= fb + 464)
  /\ (F + 128 <= fb + 432 \/ (fb + 432) + 8 <= F) /\ (fl + 1 <= fb + 432 \/ (fb + 432) + 8 <= fl)
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 432) 1251456
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) 2147607319 1
  /\ ((((fb + 432) / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= (((fb + 432) / 8) + 2147450880)).
Proof.
  intros CTX G LM.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold pa_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 256 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1.
  pose proof (PNAPAR.ov_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb HH1 FOK' VIS1) as VV. cbv zeta in VV.
  destruct VV as ((V1 & V8 & VNS) & VZ & VW & VCE & VU & _).
  assert (CLh : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 32768 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (APF : F + 128 <= fb + 432 \/ (fb + 432) + 8 <= F).
  { apply iv_apart; [clear; lia| clear; lia|]. intros a Ha X. apply (GNCF a); [left; exact Ha| apply CLh; clear - X; lia]. }
  pose proof (m32_8 F GF32) as F8.
  split; [exact V1|]. split; [exact V8|]. split; [exact VNS|]. split; [exact VZ|].
  split; [clear - VCE GSLO; lia|]. split; [right; clear; lia|].
  split; [exact APF|].
  split. { destruct (Z_lt_le_dec fl (fb + 432)) as [X|X]; [left; clear - X; lia|]. destruct (Z_lt_le_dec fl (fb + 432 + 8)) as [Y|Y]; [| right; clear - Y; lia].
           exfalso. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 32768). apply CLh. clear - X Y; lia. }
  split; [exact VU|].
  split; [exact (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LK1 cr1 Aw1 M1 model1 0x1318b8 1 HH1 ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia))|].
  destruct APF as [X|X].
  - right. pose proof (sh_lek F (fb + 432) 16 F8 V8 ltac:(clear; lia) ltac:(clear - X; lia)) as Y. clear - Y. lia.
  - left. pose proof (sh_le (fb + 432) F V8 F8 X) as Y. clear - Y. lia.
Qed.



(* [comment removed for export] *)
Lemma mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 8) (PNM.b_more s1) /\ L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 9) (PNM.b_done s1)
  /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 8) 1 /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 8) 2
  /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 400) 8
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 392) (PNM.b_sb s1)
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 256) (fb + 96)
  /\ (PNM.b_more s1 = 0 \/ PNM.b_more s1 = 1) /\ (PNM.b_done s1 = 0 \/ PNM.b_done s1 = 1)
  /\ 0 <= fb + 1024 < 2 ^ 64 /\ 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 96 < 2 ^ 64.
Proof.
  intros CTX G LM.
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM)
    as (PF & _ & _ & _ & WRop & U8op & _).
  unfold pfacts in PF. destruct PF as (_ & _ & _ & _ & _ & _ & pf7 & _).
  pose proof CTX as (_ & _ & _ & _ & _ & _ & _ & FOK & _).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof LM as (BI & RP1 & _).
  pose proof BI as (HH1 & _).
  pose proof RP1 as (PA1 & _ & _ & _ & OACC1 & _).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1. change (PNM.PSIZE + 8) with 424 in OACC1.
  assert (FOK' : PNRA.frame_okB ((F, 1, sp - 256 + 32) :: FF) fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as OPV. cbv zeta in OPV.
  destruct OPV as (_ & _ & _ & _ & OVIS & _).
  pose proof PA1 as (_ & _ & _ & MORE & DONE & _ & _ & _ & SRC & _ & _ & _ & _ & _ & PVEC & M01 & D01).
  destruct PVEC as (VC0 & _). destruct SRC as (SP0 & _). change PNM.OFF_SRC with 16 in SP0. change PNM.OFF_STK with 392 in VC0.
  split; [exact (proj2 (U8op _) MORE)|].
  split; [apply (proj2 (L5A.u8_at_vis _ M1 (fb + 464 + 9) _ (OVIS (fb + 464 + 9) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia))); exact DONE|].
  split; [apply (L5.writable_sub RSEGS _ (fb + 464) 424); [exact WRop| clear; lia| clear; lia]|].
  split; [apply (L5.writable_sub RSEGS _ (fb + 464) 424); [exact WRop| clear; lia| clear; lia]|].
  split; [apply (L5.writable_sub RSEGS _ (fb + 464) 424); [exact WRop| clear; lia| clear; lia]|].
  split; [apply (proj2 (L5A.u64_at_vis _ M1 (fb + 464 + 392) _ (OVIS (fb + 464 + 392) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia))); exact VC0|].
  split; [apply (proj2 (L5A.u64_at_vis _ M1 (fb + 464 + 256) _ (OVIS (fb + 464 + 256) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - pf7; lia) ltac:(clear - pf7; lia)));
          replace (fb + 464 + 256) with (fb + 464 + 16 + 240) by (clear; lia); exact SP0|].
  split; [exact M01|]. split; [exact D01|].
  split; [clear - pf7; lia|]. split; [clear - pf7; lia| clear - pf7; lia].
Qed.

(* [comment removed for export] *)
Lemma ifacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  6905856 <= fb + 96 <= 140737488355056 /\ (fb + 96) mod 8 = 0 /\ (2147446784 + 17592186048512 <= fb + 96 \/ (fb + 96) + 272 <= 2147446784)
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 96) / 8) + 2147450880) 34
  /\ ((sp - 256) + 256 <= fb + 96 \/ (fb + 96) + 272 <= (sp - 256)) /\ ((fb + 464) + 416 <= fb + 96 \/ (fb + 96) + 272 <= fb + 464)
  /\ (F + 128 <= fb + 96 \/ (fb + 96) + 272 <= F) /\ (fl + 1 <= fb + 96 \/ (fb + 96) + 272 <= fl)
  /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 96) 1265968
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) 2147609123 1
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 96 + 152) / 8) + 2147450880) 1
  /\ ((((fb + 96) / 8) + 2147450880) + 34 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= (((fb + 96) / 8) + 2147450880))
  /\ L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 96 + 152) (PM.sm_st sm1) /\ (PM.sm_st sm1 = 0 \/ PM.sm_st sm1 = 2).
Proof.
  intros CTX G LM.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold pa_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 1, sp - 256 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_is PMA.AD fb) with (fb + 96) in IA1.
  assert (AO : PMSPA.aobjA FF' (fb + 96) 272) by (apply (PNAPAR.aobj_fbB FF' fb (fb + 96) 272 FOK'); clear; lia).
  assert (O8 : (fb + 96) mod 8 = 0) by (replace 96 with (8 * 12) by reflexivity; apply PNAPAR.fb_mod8; exact Fal).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 (fb + 96) str sm1 sp 32768 HH1 AO O8 IA1 ASTK1) as IV. cbv zeta in IV.
  destruct IV as ((I1 & I8 & INS) & IZ & IW & ICE & IVIS & _).
  assert (CLh : forall a, fb + 32 <= a < fb + 2040 -> aclient L ar LBX FF sp 32768 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha; lia| intros Y; clear - Ha Y; lia]. }
  assert (APF : F + 128 <= fb + 96 \/ (fb + 96) + 272 <= F).
  { apply iv_apart; [clear; lia| clear; lia|]. intros a Ha X. apply (GNCF a); [left; exact Ha| apply CLh; clear - X; lia]. }
  pose proof (m32_8 F GF32) as F8.
  pose proof IA1 as (IVP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _).
  destruct IOS as (_ & IST & _ & _ & _ & _ & _ & _ & ST02).
  split; [exact I1|]. split; [exact I8|]. split; [exact INS|]. split; [exact IZ|].
  split; [clear - ICE GSLO; lia|]. split; [right; clear; lia|].
  split; [exact APF|].
  split. { destruct (Z_lt_le_dec fl (fb + 96)) as [X|X]; [left; clear - X; lia|]. destruct (Z_lt_le_dec fl (fb + 96 + 272)) as [Y|Y]; [| right; clear - Y; lia].
           exfalso. apply GFLNC. apply L5SAR.aclient_cons. apply (L5SAR.aclient_00 L ar LBX FF sp 32768). apply CLh. clear - X Y; lia. }
  split; [apply (proj2 (L5A.u64_at_vis _ M1 (fb + 96) _ (IVIS (fb + 96) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1; lia) ltac:(clear - I1; lia))); exact IVP|].
  split; [exact (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF' LK1 cr1 Aw1 M1 model1 0x135118 1 HH1 ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia))|].
  split. { intros i Hi. replace ((fb + 96 + 152) / 8 + 2147450880 + i) with ((fb + 96) / 8 + 2147450880 + (19 + i)) by (rewrite (PNAPAK.div8_add (fb + 96) 152 O8 ltac:(clear; lia)); change (152 / 8) with 19; clear; lia).
           apply IZ. clear - Hi; lia. }
  split. { destruct APF as [X|X].
           - right. pose proof (sh_lek F (fb + 96) 16 F8 O8 ltac:(clear; lia) ltac:(clear - X; lia)) as Y. clear - Y. lia.
           - left. pose proof (sh_lek (fb + 96) F 34 O8 F8 ltac:(clear; lia) ltac:(clear - X; lia)) as Y. clear - Y. lia. }
  split; [| exact ST02].
  apply (proj2 (L5A.u8_at_vis _ M1 (fb + 96 + 152) _ (IVIS (fb + 96 + 152) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1; lia) ltac:(clear - I1; lia))).
  replace (PM.sm_st sm1) with (PM.sm_st sm1 mod 256) by (destruct ST02 as [-> | ->]; reflexivity).
  apply PMTK2.u8_of_u32; [destruct ST02 as [-> | ->]; clear; lia|]. replace (fb + 96 + 152) with (fb + 96 + 120 + 32) by (clear; lia). exact IST.
Qed.

(* [comment removed for export] *)
Lemma hfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 pre top :
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNRA.binv s1 -> PNM.b_stk s1 = pre ++ [top] ->
  hfacts (mrestrict (ahid Aw1 model1) M1) (PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40) (PNM.bs_mode top) (PNM.bs_type top).
Proof.
  intros CTX G LM INV1 ES.
  pose proof (PNAPAK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 pre top CTX G LM INV1 ES)
    as (TF & PT & OKt & VIN & TB1 & TB2 & TB3 & TB4).
  destruct CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold pa_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  destruct RP1 as (PA1 & _).
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVEC & _).
  destruct PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & CB & AN & EL).
  rewrite ES in Hlen, CB. rewrite length_app in Hlen, CB. cbn [length] in Hlen, CB. rewrite Nat2Z.inj_add in Hlen, CB. cbn [Z.of_nat Pos.of_succ_nat] in Hlen, CB.
  change PNM.BSZ with 40 in *.
  set (sb1 := PNM.b_sb s1) in *. set (sk1 := PNM.b_sk s1) in *.
  assert (VINL : In (sb1, 40 * 2 ^ sk1) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact VIN).
  set (T := sb1 + 40 * Z.of_nat (length pre)) in *.
  assert (TAL : T mod 8 = 0).
  { unfold T. replace (sb1 + 40 * Z.of_nat (length pre)) with (sb1 + (Z.of_nat (length pre) * 5) * 8) by (clear; lia). rewrite Z.mod_add by lia. apply PMKA.mod16_8'. exact Hal. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & VFS & VB & _).
  assert (TV : L5A.avis (ahid Aw1 model1) T 40) by (apply (VB sb1 (40 * 2 ^ sk1) T 40 VINL); clear - TB1 TB2; lia).
  assert (TVs : forall o n, 0 <= o -> 0 < n -> o + n <= 40 -> L5A.avis (ahid Aw1 model1) (T + o) n) by (intros o n X1 X2 X3; eapply L5A.avis_sub; [exact TV| clear - X1; lia| clear - X3; lia]).
  assert (WRs : forall o n, 0 <= o -> 0 < n -> o + n <= 40 -> L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (T + o) n).
  { intros o n X1 X2 X3. apply (proj2 (L5A.writable_vis _ M1 (T + o) n (TVs o n X1 X2 X3) ltac:(clear - TB4 TB1 X1; lia) ltac:(clear - TB2 TB3 GSLO GSHI GSPT X3; lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 sb1 (40 * 2 ^ sk1)); [exact DB| clear - TB1 X1; lia| clear - TB2 X3; lia]| clear - TB4 TB1 X1; lia| clear - TB2 TB3 GSLO GSHI GSPT X3; lia]. }
  assert (SHs : forall o, 0 <= o -> o + 8 <= 40 -> o mod 8 = 0 -> L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) ((T + o) / 8 + 2147450880) 1).
  { intros o X1 X3 X8. change 2147450880 with SB. replace 1 with (8 / 8) by reflexivity.
    apply (PMKA.blk_shadow_vis L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 sb1 (40 * 2 ^ sk1) (T + o) 8 HH1 VINL); [clear - TB1 X1; lia| clear - TB2 X3; lia| | clear; lia| reflexivity|].
    - rewrite Z.add_mod by (clear; lia). rewrite TAL, X8. reflexivity.
    - intros a Ha. apply CB. clear - Ha TB1 TB2 Hlen X1 X3; unfold T in *; lia. }
  destruct PT as (PT0 & PT8 & PT16 & PT24 & PT32). pose proof OKt as (MODE & _ & _ & TYP & _).
  unfold hfacts. replace (T + 40 - 40) with (T + 0) by (clear; lia). replace (T + 40 - 16) with (T + 24) by (clear; lia).
  split; [apply (proj2 (L5A.u32_at_vis _ M1 (T + 0) _ (TVs 0 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - TB4 TB1; lia) ltac:(clear - TB2 TB3 GSLO GSHI GSPT; lia)));
          replace (T + 0) with T by (clear; lia); exact PT0|].
  split; [apply (SHs 0); [clear; lia| clear; lia| reflexivity]|].
  split; [apply WRs; clear; lia|].
  split; [apply (proj2 (L5A.u8_at_vis _ M1 (T + 24) _ (TVs 24 1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - TB4 TB1; lia) ltac:(clear - TB2 TB3 GSLO GSHI GSPT; lia))); exact PT24|].
  split; [apply (SHs 24); [clear; lia| clear; lia| reflexivity]|].
  split; [apply WRs; clear; lia|].
  split; [clear - MODE; lia|]. split; [clear - TYP; lia| clear - TYP; lia].
Qed.

(* [comment removed for export] *)
Lemma spill_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  spill M1 sp F (fb + 464) (fb + 432) (fb + 1024) -> spill (mrestrict (ahid Aw1 model1) M1) sp F (fb + 464) (fb + 432) (fb + 1024).
Proof.
  intros CTX G LM SPL.
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM)
    as (_ & _ & SV & _).
  unfold spill in *. destruct SPL as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
  repeat split; (apply SV; [clear; lia| clear; lia| assumption]).
Qed.
(* [comment removed for export] *)
Lemma spill_of_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  spill (mrestrict (ahid Aw1 model1) M1) sp F (fb + 464) (fb + 432) (fb + 1024) -> spill M1 sp F (fb + 464) (fb + 432) (fb + 1024).
Proof.
  intros CTX G LM SPL.
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM)
    as (_ & _ & _ & _ & _ & _ & SVr).
  unfold spill in *. destruct SPL as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
  repeat split; (apply SVr; [clear; lia| clear; lia| assumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pa_exit K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 :
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  lregs R R6 sp fb F -> spill M6 sp F (fb + 464) (fb + 432) (fb + 1024) -> ec_some M6 fb ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xae510 M6 model6) K.
Proof.
  intros CTX G LM ER SPL ECS.
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (MO6 & _ & _ & _ & _ & _ & _ & MO01 & _ & Q36 & Q34 & Q37).
  pose proof (spill_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM SPL) as SPv.
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  pfx PF. spx SPv. pose proof ER as ER'. lrx ER'. owx OWN6. qsx R.
  (let T := type of (PNAPAP.apaX_conc fx6 R6 MV6 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) in let T := eval unfold vmx in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PNAPAP.apaX_conc fx6 R6 MV6 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) T ltac:(try (unfold vmx); cbn beta iota) ltac:(first [assumption | unfold PNAPAP.aligned, PNAPAP2.aligned; assumption])).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & _ & _ & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _).
  assert (DF1 : 863232 <= F / 8) by (apply Z.div_le_lower_bound; clear - pf15; lia).
  assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - pf15; lia).
  apply (PNAPAK.pa_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6
           fx6 fx9 R6 R9 0xae510 (PNM.b_more s6) M9v CTX G LM MS9 MG9).
  - intros a Ha N. apply FRZ9; [exact Ha| | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 1 / 8) with 16; unfold SB.
    + left; left; left. clear - X; lia.
    + left; left; right. clear - X; lia.
    + left; right. clear - X; lia.
  - exact FL0.
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia).
    apply (L5C.u8_at_agree RSEGS MV6 M9v); [| clear - pf7; lia| clear - pf7; lia| exact MO6].
    intros j Hj. apply FRZ9; [clear - Hj pf7; lia| clear - Hj pf28; lia| clear - Hj pf9 DF1 DF2; lia| clear - Hj pf29; lia].
  - exact MO01.
  - exact Y2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - destruct ECS as (e5 & c5 & _ & EC5). exists e5, c5. exact EC5.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pa_IH (K : TSet) (R : bvmap 5 word) (M : mem) (model : Model) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
           (cr : credit) (sp fb : Z) (s : PNM.bpst) (str : PM.vstr) (sm : PM.strm) (ax : PNST.bax) (F : Z) (n : Z) : Prop :=
  forall (fx1 : FPState) R1 (M1 : mem) model1 LK1 Aw1 s1 sm1 ax1 cr1,
    pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
    lregs R R1 sp fb F -> getr R1 (reg 17) = Z_to_bv 64 (fb + 464 + 8) -> spill M1 sp F (fb + 464) (fb + 432) (fb + 1024) -> ec_some M1 fb -> PNRA.binv s1 ->
    (PNM.b_more s1 = 1 -> PNRA.bb_room s1 sm1) ->
    (PNM.b_more s1 = 1 -> 0 <= PNRA.bmu s1 sm1 < n) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xae0cc M1 model1) K.

(* [comment removed for export] *)
Lemma pa_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (n : Z) M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 :
  pa_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  pa_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  pa_IH K R M model LBX FF LK Aw cr sp fb s str sm ax F n ->
  pa_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  lregs R R6 sp fb F -> getr R6 (reg 17) = Z_to_bv 64 (fb + 464 + 8) -> spill M6 sp F (fb + 464) (fb + 432) (fb + 1024) -> ec_some M6 fb ->
  (PNM.b_done s6 = 1 \/ (PNRA.binv s6 /\ (PNM.b_more s6 = 1 -> PNRA.bb_room s6 sm6) /\ (PNM.b_more s6 = 1 -> 0 <= PNRA.bmu s6 sm6 < n))) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xae3fc M6 model6) K.
Proof.
  intros CTX G IH LM ER X17 SPL ECS ST.
  pose proof (PNAPAK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & _).
  pose proof (mfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (_ & DN6 & _ & _ & _ & _ & _ & _ & DN01 & Q36 & Q34 & Q37).
  pose proof (spill_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM SPL) as SPv.
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  pfx PF. spx SPv. pose proof ER as ER'. lrx ER'.
  destruct DN01 as [D0|D1].
  - (* [comment removed for export] *)
    rewrite D0 in DN6.
    destruct ST as [X|(INV6 & BBR6 & MU6)]; [rewrite D0 in X; discriminate|].
    (let T := type of (PNAPAP.apaT0_conc fx6 R6 MV6 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) in let T := eval unfold vmx in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PNAPAP.apaT0_conc fx6 R6 MV6 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) T ltac:(try (unfold vmx); cbn beta iota) ltac:(first [assumption | unfold PNAPAP.aligned, PNAPAP2.aligned; assumption])).
    destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _).
    apply (pa_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xae3fc 0xae0cc M7v CTX G LM MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    apply (IH fx7 R7 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 LM7); [| rewrite (KS7 17%nat) by inl; exact X17| exact SPL| exact ECS| exact INV6| exact BBR6| exact MU6].
    lrk ER KS7.
  - (* [comment removed for export] *)
    rewrite D1 in DN6.
    (let T := type of (PNAPAP.apaT1_conc fx6 R6 MV6 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) in let T := eval unfold vmx in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PNAPAP.apaT1_conc fx6 R6 MV6 (vmx R sp fb F fl 0 0 0 0 0 0 0 0)) T ltac:(try (unfold vmx); cbn beta iota) ltac:(first [assumption | unfold PNAPAP.aligned, PNAPAP2.aligned; assumption])).
    destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _).
    apply (pa_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xae3fc 0xae510 M7v CTX G LM MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    apply (pa_exit K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 CTX G LM7); [| exact SPL| exact ECS].
    lrk ER KS7.
Qed.
End WithHeap.
End PNAPAA.
