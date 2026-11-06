(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmParSpecs PmLayout PnLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PnSpecsAa
     PmModelFactsA PnStepA PmStep PgSrc PgV8 PgSrcA PnLayout PnModel PnModelFacts PnStatics PnStaticsA PnRunA PnRunAa PnASrcKit PmAUarK PmAUar PnBrObj PnBrObjA PnAParKit PnAReset1 PnOwnerOkA
     PmCertKitG AsanPlanSoundSums PnBrKitA PnARvTP PnARvOP PnARvK PnARvKX PnARvKB PnARvKT PnARvKV PnARvE PnARvF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVO.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARVK. Import PNARVKX. Import PNARVKB. Import PNARVKT.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall model3,
      rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M1 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ KR.
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
           fx1 fx2 R1 R2 pc1 pc2 M2v (fun _ => False) CTX G LM MS MG).
  - intros a Ha _. exact (FRZ a Ha).
  - intros a [].
  - intros M3 model3 LM3 HID3 VIS3 FR3 MG3 ECK3.
    assert (EM31 : M3 = M1) by (apply PNBKA.mem_eq_of_agree; exact FR3). subst M3.
    exact (KR model3 LM3 HID3).
Qed.


(* [comment removed for export] *)
Lemma tab8_all : forallb (fun i => match rdn RSEGS (fun _ => None) (Z_to_bv 64 (145760 + Z.of_nat i)) 1 with Some (x :: nil) => true | _ => false end) (seq 0 512) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma tab8_ok (M : mem) a : L5.img_clear M 65536 1269760 -> 145760 <= a < 146272 -> exists v, 0 <= v <= 255 /\ L5.u8_at RSEGS M a v.
Proof.
  intros IC Ha. pose proof tab8_all as A. rewrite forallb_forall in A.
  specialize (A (Z.to_nat (a - 145760)) ltac:(apply in_seq; clear - Ha; lia)). rewrite Z2Nat.id in A by (clear - Ha; lia).
  replace (145760 + (a - 145760)) with a in A by (clear; lia).
  assert (E : rdn RSEGS M (Z_to_bv 64 a) 1 = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) 1).
  { cbn [rdn]. rewrite (IC a) by (clear - Ha; lia). reflexivity. }
  unfold L5.u8_at. rewrite E. destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 a) 1) as [[|x [|y l]]|]; try discriminate A.
  exists (bv_unsigned x). pose proof (bv_unsigned_in_range 8 x) as RG. change (bv_modulus 8) with 256 in RG.
  split; [clear - RG; lia| rewrite Z_to_bv_bv_unsigned; reflexivity].
Qed.
Lemma u8_of_defined (M : mem) a : 0 <= a -> a + 1 <= 2 ^ 64 -> L5.defined M a 1 -> exists v, 0 <= v <= 255 /\ L5.u8_at RSEGS M a v.
Proof.
  intros Ha Hn D. destruct (PMCG.rdn_some RSEGS M 1%nat a Ha ltac:(cbn; lia) ltac:(intros i Hi; apply D; cbn in Hi; lia)) as (bs & E & Hl).
  destruct bs as [|x [|y l]]; cbn [length] in Hl; try (exfalso; clear - Hl; lia).
  exists (bv_unsigned x). pose proof (bv_unsigned_in_range 8 x) as RG. change (bv_modulus 8) with 256 in RG.
  split; [clear - RG; lia| unfold L5.u8_at; rewrite E, Z_to_bv_bv_unsigned; reflexivity].
Qed.
(* [comment removed for export] *)
Lemma tab_shz LB FF LK cr Aw M model : ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5KA.zeros_at (mrestrict (ahid Aw model) M) (145760 / 8 + 2147450880) 64.
Proof.
  intros HH. set (a := 145760). set (g := 64).
  assert (AP : Forall (fun r => a + 8 * g <= fst r \/ snd r <= a) (icl_poison IL)).
  { rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; unfold a, g; clear; lia|]). apply Forall_nil. }
  destruct (aic_img_shadow _ _ _ _ _ ICok LB FF LK cr Aw M _ HH a (8 * g) ltac:(rewrite (L5A.aly_img_lo L C LYa); unfold a; clear; lia)
              ltac:(rewrite (L5A.aly_img_hi L C LYa); unfold a, g; clear; lia) ltac:(unfold g; clear; lia) AP) as (ZB & ALW).
  assert (INS : forall j, 0 <= j < g -> in_shadow_of a (8 * g) (a / 8 + 2147450880 + j)).
  { intros j Hj. assert (SJ : a / 8 + 2147450880 + j = S (a + 8 * j)).
    { unfold S, SB. replace (a + 8 * j) with (j * 8 + a) by (clear; lia). rewrite Z.div_add_l by (clear; lia). clear; lia. }
    unfold in_shadow_of. rewrite SJ. unfold S. split; apply Z.add_le_mono_r; apply Z.div_le_mono; unfold a, g in *; clear - Hj; lia. }
  apply (proj2 (L5A.zeros_at_vis _ M _ g (L5A.avis_of_shadow_allowed Aw model a (8 * g) _ g ALW INS))).
  intros j Hj. pose proof (ZB _ (INS j Hj)) as B. unfold byte_at in B. exact B.
Qed.
Lemma tab_facts (MV : mem) b : L5.img_clear MV 65536 1269760 -> L5KA.zeros_at MV (145760 / 8 + 2147450880) 64 -> 0 <= b <= 255 ->
  exists lo hi, L5.u8_at RSEGS MV ((2 * b) + 145760) lo /\ 0 <= lo <= 255 /\ L5.u8_at RSEGS MV ((2 * b) + 145761) hi /\ 0 <= hi <= 255
                /\ L5KA.zeros_at MV ((((2 * b) + 145760) / 8) + 2147450880) 1 /\ 0 <= lo < 2 ^ 64 /\ 0 <= hi < 2 ^ 64.
Proof.
  intros IC ZT Hb.
  destruct (tab8_ok MV (2 * b + 145760) IC ltac:(clear - Hb; lia)) as (lo & Hlo & Ulo).
  destruct (tab8_ok MV (2 * b + 145761) IC ltac:(clear - Hb; lia)) as (hi & Hhi & Uhi).
  exists lo, hi. split; [exact Ulo|]. split; [exact Hlo|]. split; [exact Uhi|]. split; [exact Hhi|]. split; [| clear - Hlo Hhi; lia].
  intros i Hi. assert (E : (2 * b + 145760) / 8 = 145760 / 8 + (2 * b) / 8).
  { replace (2 * b + 145760) with (2 * b + 18220 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). change (145760 / 8) with 18220. clear; lia. }
  rewrite E. replace (145760 / 8 + 2 * b / 8 + 2147450880 + i) with (145760 / 8 + 2147450880 + (2 * b / 8 + i)) by (clear; lia). apply ZT.
  pose proof (Z.div_pos (2 * b) 8 ltac:(clear - Hb; lia) ltac:(clear; lia)) as D0.
  pose proof (Z.div_lt_upper_bound (2 * b) 8 64 ltac:(clear; lia) ltac:(clear - Hb; lia)) as D1. clear - Hi D0 D1. lia.
Qed.
Lemma set_tb_id s : set_cs 1 s (PNM.b_tb s) (PNM.b_tg s) = s.
Proof. destruct s; reflexivity. Qed.


(* [comment removed for export] *)
Definition mido (R Rc : bvmap 5 word) (sp fb F : Z) : Prop :=
  getr Rc (reg 2) = Z_to_bv 64 (sp - 224) /\ getr Rc (reg 3) = getr R (reg 3) /\ getr Rc (reg 4) = getr R (reg 4)
  /\ getr Rc (reg 8) = Z_to_bv 64 sp /\ getr Rc (reg 9) = Z_to_bv 64 (sp - 224)
  /\ getr Rc (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Rc (reg 19) = Z_to_bv 64 F /\ getr Rc (reg 20) = Z_to_bv 64 (fb + 464)
  /\ getr Rc (reg 21) = Z_to_bv 64 2147450880 /\ getr Rc (reg 22) = Z_to_bv 64 (fb + 432)
  /\ getr Rc (reg 24) = Z_to_bv 64 (fb + 1024) /\ getr Rc (reg 27) = Z_to_bv 64 F.
Definition MIDOREGS : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 27]%nat.
Lemma mido_keep R Rc R1 sp fb F : mido R Rc sp fb F -> (forall k, In k MIDOREGS -> getr R1 (reg k) = getr Rc (reg k)) -> mido R R1 sp fb F.
Proof.
  intros (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E24 & E27) KS. unfold mido.
  rewrite (KS 2%nat), (KS 3%nat), (KS 4%nat), (KS 8%nat), (KS 9%nat), (KS 18%nat), (KS 19%nat), (KS 20%nat), (KS 21%nat), (KS 22%nat), (KS 24%nat), (KS 27%nat) by (unfold MIDOREGS; cbn [In]; tauto).
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma tb24_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 c n p :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNM.b_tb s1 = PM.VLong c n p ->
  4096 <= p <= 140737488355296 /\ p mod 8 = 0 /\ (2147446784 + 17592186048512 <= p \/ p + 24 <= 2147446784) /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) p 24
  /\ ((sp - 224) + 224 <= p \/ p + 24 <= (sp - 224)) /\ (p + 24 <= fb + 464 \/ (fb + 464) + 416 <= p) /\ (65536 + 6832128 <= p \/ p + 24 <= 65536)
  /\ (p + 24 <= F \/ F + 512 <= p) /\ (p + 24 <= fl \/ fl + 1 <= p)
  /\ (L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) ((p / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 2) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 4) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 6) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 8) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 10) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 12) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 14) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 16) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 18) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 20) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((p + 22) / 8) + 2147450880) 1)
  /\ In (p, c) (PM.vs_own (PNM.b_tb s1)) /\ 26 <= c.
Proof.
  intros CTX G LM ETB0.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 8) with 28672 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6897664 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 3, sp - 224 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *.
  set (H1 := ahid Aw1 model1) in *. set (MV := mrestrict H1 M1) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & VFS & VB & VBS & VFSS & _).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 28672 224 HH1 ASTK1 ltac:(clear; lia)) as (SL224 & _ & _).
  assert (ZZ : forall o k, 0 <= o -> o / 8 = k -> k <= 52 -> L5KA.zeros_at MV ((op + o) / 8 + 2147450880) 1).
  { intros o k Ho Ek Hk i Hi. replace ((op + o) / 8 + 2147450880 + i) with (op / 8 + 2147450880 + (k + i)) by (rewrite (div8_add op o O8 Ho), Ek; clear; lia).
    apply Zop. pose proof (Z.div_pos o 8 Ho ltac:(clear; lia)) as D. rewrite Ek in D. clear - Hi Hk D; lia. }
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB1 & _). unfold PNM.OFF_TB in TB1.
  rewrite ETB0 in TB1. destruct TB1 as (D & Cc & W0 & W8 & W16 & Hn & Hc & Hev & DBp & CBp).
  assert (Ip : In (p, c) (PNM.bparser_own s1)) by (apply (PNBOA.PNM_own_tb s1 p c); rewrite ETB0; left; reflexivity).
  assert (IpL : In (p, c) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact Ip).
  pose proof (WB1 _ IpL) as ((Y0 & Y1 & Y2 & Y3 & Y4 & Y5) & _ & _ & _ & _ & _ & YFS). cbn [fst snd] in *.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Y1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y5.
  pose proof (PMKA.mod16_8' p Y2) as P8.
  destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ p c op 416 HH1 IpL (PMAUAR.aobjA_push FF _ 416 _ (PNAPAR.aobj_fbB FF fb op 416 FOK ltac:(unfold op; clear; lia) ltac:(unfold op; clear; lia)))) as [Z0|Z0].
  all: pose proof (PMKA.blk_shadow_vis L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 p c p 24 HH1 IpL ltac:(clear; lia) ltac:(clear - Hc; lia) P8 ltac:(clear; lia) ltac:(reflexivity)) as ZP;
    change (24 / 8) with 3 in ZP; specialize (ZP ltac:(intros a Ha; apply CBp; clear - Ha Hc; lia)).
  all: assert (ZQ : forall o, 0 <= o < 24 -> L5KA.zeros_at MV ((p + o) / 8 + 2147450880) 1);
    [intros o Ho i Hi; pose proof (Z.div_mod p 8 ltac:(clear; lia)) as Dm; rewrite P8, Z.add_0_r in Dm;
     replace ((p + o) / 8) with (p / 8 + o / 8) by (rewrite Dm at 2; rewrite Z.mul_comm, Z.div_add_l by (clear; lia); reflexivity);
     pose proof (Z.div_pos o 8 ltac:(clear - Ho; lia) ltac:(clear; lia)) as D0; pose proof (Z.div_lt_upper_bound o 8 3 ltac:(clear; lia) ltac:(clear - Ho; lia)) as D1;
     replace (p / 8 + o / 8 + 2147450880 + i) with (p / 8 + 2147450880 + (o / 8 + i)) by (clear; lia); apply ZP; clear - Hi D0 D1; lia|].
  all: pose proof GFLP as GFLP'; unfold FS_BYTES in GFLP', YFS, GFS1, GFS2; change (ff_bytes 3) with 512 in *.
  all: split; [clear - Y0 Y5 Hc P8; pose proof (Z.div_mod p 8 ltac:(lia)) as Dm; rewrite P8 in Dm; lia|]. all: split; [exact P8|]. all: split; [clear - Y5 Hc; lia|].
  all: split; [apply (proj2 (L5A.writable_vis H1 M1 p 24 (VB p c p 24 IpL ltac:(clear; lia) ltac:(clear - Hc; lia)) ltac:(clear - Y0; lia) ltac:(clear - Y5 Hc; lia)));
               apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 p c); [exact DBp| clear; lia| clear - Hc; lia]| clear - Y0; lia| clear - Y5 Hc; lia]|].
  all: split; [right; clear - Y4 GSLO Hc; lia|]. all: split; [unfold op in Z0; clear - Z0 Hc; lia|]. all: split; [clear - Y1 Hc; lia|].
  all: split; [clear - YFS GFS1 GFS2 Hc; lia|]. all: split; [clear - YFS GFLP' Hc; lia|].
  all: split; [repeat split; first [replace (p / 8) with ((p + 0) / 8) by (rewrite Z.add_0_r; reflexivity)| idtac]; apply ZQ; clear; lia|].
  all: split; [rewrite ETB0; left; reflexivity| clear - Hc; lia].
Qed.


(* [comment removed for export] *)
Lemma oid_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  PNRA.binv s6 -> mido R R6 sp fb F -> getr R6 (reg 23) = Z_to_bv 64 (fb + 464 + 368) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PNM.b_bb s6 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xafe88 M6 model6) K.
Proof.
  intros CTX G LM INV6 MID6 X23 EC6 TP6 BB6.
  pose proof MID6 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J24 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (U10 & WR8 & OVIS3 & VF3 & VSH3 & MO3).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6897664 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVOP.awvO7_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVOP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z1 & Z10 & Z11 & Z12 & HMAG & SH53 & SH52 & MO1 & SH57 & SH56 & D8).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx9 R6 R9 0xafe88 1 M9v CTX G LM MS9 MG9).
  - intros a Ha N1 N2 N3. apply FRZ9; [exact Ha| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia| intros X; apply N3; clear - X; lia].
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO1.
  - right; reflexivity.
  - exact Z1.
  - exact Z10.
  - exact Z11.
  - rewrite (KS9 2%nat) by inl. exact J2.
  - rewrite (KS9 8%nat) by inl. exact J8.
  - rewrite (KS9 19%nat) by inl. exact J19.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact J3.
    + rewrite (KS9 4%nat) by inl. exact J4.
  - right. split; [exact EC6|]. unfold PNRA.bprog_value, PNRA.bpush_rel. left. exact TP6.
  - exact INV6.
  - exact (btop_len s s6 TP6).
  - intros R0 _. unfold PNRA.bb_room in *. rewrite BB6. destruct LM as (_ & _ & STEP & _). destruct STEP as (_ & _ & _ & _ & LE).
    exact (PGV8.v8_room_mono _ _ _ LE R0).
Qed.

(* [comment removed for export] *)
Lemma oid_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 c n p :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  PNRA.binv s6 -> mido R R6 sp fb F -> getr R6 (reg 23) = Z_to_bv 64 (fb + 464 + 368) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PNM.b_bb s6 = PNM.b_bb s ->
  getr R6 (reg 13) = Z_to_bv 64 (((fb + 464 + 368) / 8) + 2147450880) -> PNM.b_tb s6 = PM.VLong c n p ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xafde4 M6 model6) K.
Proof.
  intros CTX G LM INV6 MID6 X23 EC6 TP6 BB6 X13 ETB.
  pose proof MID6 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J24 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (U10 & WR8 & OVIS3 & VF3 & VSH3 & MO3).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6897664 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  pose proof (PNARVKV.vfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 120 CTX G LM ltac:(reflexivity) ltac:(clear; lia)) as VFX.
  change ((1241824 + 120) / 8 + 2147450880) with 2147606123 in VFX. conj_open VFX.
  pose proof (PNARVKX.tbfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (tz1 & tz2 & tz3 & tz4 & tw1 & tw2 & TBV & TBM).
  rewrite ETB in TBM. destruct TBM as (tb1 & tb2 & tb3 & tb4 & tb5 & tb6 & tb7 & _).
  pose proof (tb24_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 c n p CTX G LM ETB) as (ta1 & ta2 & ta3 & ta4 & ta5 & ta6 & ta7 & ta8 & ta9 & taZ & _).
  fold MV6 in tz1, tz2, tz3, tz4, tb1, tb4, tb5, ta4, taZ. conj_open taZ.
  assert (Q56 : 0 <= (c + 1) mod 256 < 2 ^ 64) by (clear - tb2; lia).
  assert (Q57 : 0 <= p < 2 ^ 64) by (clear - ta1; lia).
  assert (Q58 : 0 <= n < 2 ^ 64) by (clear - tb6 tb7; lia).
  LeanFeed.pfeed P (PNARVOP.awvO6_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 56%nat => (c + 1) mod 256 | 57%nat => p | 58%nat => n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVOP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & _).
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xafde4 0xafe88 M7v
           (fun a => (F / 8 + 2147450880 + 56 <= a < F / 8 + 2147450880 + 56 + 2) \/ (F + 448 <= a < F + 448 + 16)) CTX G LM MS7 MG7).
  { intros a Ha N. apply FRZ7; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a [X|X]; [right; right| right; left]; clear - X; lia. }
  intros M8 model8 LM8 HID8 VIS8 FR8 MG8 ECK8.
  apply (oid_tail K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 CTX G LM8 INV6).
  - apply (mido_keep R R6 R7 sp fb F MID6). unfold MIDOREGS. kks KS7.
  - rewrite (KS7 23%nat) by inl. exact X23.
  - exact (ECK8 _ _ EC6).
  - exact TP6.
  - exact BB6.
Qed.


(* [comment removed for export] *)
Lemma vstr_long_keep (M1 M3 : mem) o c n p (W : Z -> Prop) :
  0 <= o -> o + 24 <= 2 ^ 47 -> 0 <= p -> p + c <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
  (forall a, W a -> p <= a < p + 24) -> (p + 24 <= o \/ o + 24 <= p) -> (2147446784 + 17592186048512 <= p \/ p + 24 <= 2147446784) ->
  PM.vstr_at RSEGS PMSPA.accA M1 o (PM.VLong c n p) -> PM.vstr_at RSEGS PMSPA.accA M3 o (PM.VLong c n p).
Proof.
  intros Ho Ho' Hp Hp' FR MG WP AP NS (D & Cc & W0 & W8 & W16 & Hn & Hc & Hev & DBp & CBp).
  assert (SHK : forall x, 0 <= x < 2 ^ 47 -> M3 (Z_to_bv 64 (S x)) = M1 (Z_to_bv 64 (S x))).
  { intros x Hx. pose proof (Z.div_pos x 8 ltac:(clear - Hx; lia) ltac:(clear; lia)) as D0.
    pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx; lia)) as D1.
    apply FR; [unfold S, SB; clear - D0 D1; lia|]. intros X. apply WP in X. unfold S, SB in X. clear - X NS D0 D1. lia. }
  assert (AGo : forall j, o <= j < o + 24 -> M3 (Z_to_bv 64 j) = M1 (Z_to_bv 64 j)).
  { intros j Hj. apply FR; [clear - Hj Ho Ho'; lia|]. intros X. apply WP in X. clear - X Hj AP. lia. }
  unfold PM.vstr_at.
  split; [exact (L5.defined_grows M1 M3 _ _ MG D)|].
  split; [apply (PMFA.accA_agree M1 M3 o 24); [intros x Hx; apply SHK; clear - Hx Ho Ho'; lia| exact Cc]|].
  split; [apply (L5C.u64_at_agree RSEGS M1 M3 o); [intros j Hj; apply AGo; clear - Hj; lia| clear - Ho; lia| clear - Ho'; lia| exact W0]|].
  split; [apply (L5C.u64_at_agree RSEGS M1 M3 (o + 8)); [intros j Hj; apply AGo; clear - Hj; lia| clear - Ho; lia| clear - Ho'; lia| exact W8]|].
  split; [apply (L5C.u64_at_agree RSEGS M1 M3 (o + 16)); [intros j Hj; apply AGo; clear - Hj; lia| clear - Ho; lia| clear - Ho'; lia| exact W16]|].
  split; [exact Hn|]. split; [exact Hc|]. split; [exact Hev|].
  split; [exact (L5.defined_grows M1 M3 _ _ MG DBp)|].
  apply (PMFA.accA_agree M1 M3 p c); [intros x Hx; apply SHK; clear - Hx Hp Hp'; lia| exact CBp].
Qed.

(* [comment removed for export] *)
Lemma oid_hex3 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 c n p (b : nat -> Z) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  PNRA.binv s6 -> mido R R6 sp fb F -> getr R6 (reg 23) = Z_to_bv 64 (fb + 464 + 368) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PNM.b_bb s6 = PNM.b_bb s ->
  getr R6 (reg 25) = Z_to_bv 64 (b 1%nat) -> getr R6 (reg 26) = Z_to_bv 64 (b 0%nat) ->
  getr R6 (reg 10) = Z_to_bv 64 p -> getr R6 (reg 17) = Z_to_bv 64 145760 -> getr R6 (reg 13) = Z_to_bv 64 (((fb + 464 + 368) / 8) + 2147450880) ->
  PNM.b_tb s6 = PM.VLong c n p ->
  (forall i, (i < 12)%nat -> 0 <= b i <= 255) ->
  (forall i, (2 <= i < 12)%nat -> L5.u64_at RSEGS M6 (sp - 224 + 8 * Z.of_nat i) (b i)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xafd04 M6 model6) K.
Proof.
  intros CTX G LM INV6 MID6 X23 EC6 TP6 BB6 X25 X26 X10 X17 X13 ETB HB HS.
  pose proof MID6 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J24 & J27).
  pose proof LM as (BI6 & RP6 & _). pose proof BI6 as (HH6 & _). pose proof RP6 as (PA6 & _ & _ & _ & _ & _ & _ & GR6). destruct GR6 as (_ & GTB6 & _).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA6. pose proof PA6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TBR6 & _). change (fb + 464 + PNM.OFF_TB) with (fb + 464 + 368) in TBR6.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6897664 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  assert (IC : L5.img_clear MV6 65536 1269760) by assumption.
  match goal with H : _ <= sp <= _ |- _ => pose proof H as RSP end.
  pose proof (tab_shz _ _ _ _ _ _ _ HH6) as ZT. fold MV6 in ZT.
  pose proof (tb24_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 c n p CTX G LM ETB) as (ta1 & ta2 & ta3 & ta4 & ta5 & ta6 & ta7 & ta8 & ta9 & taZ & taI & taC).
  fold MV6 in ta4, taZ. conj_open taZ.
  assert (Q57 : 0 <= p < 2 ^ 64) by (clear - ta1; lia).
  pose proof (HB 0%nat ltac:(clear; lia)) as RB0. assert (QB0 : 0 <= b 0%nat < 2 ^ 64) by (clear - RB0; lia).
  pose proof (HB 1%nat ltac:(clear; lia)) as RB1. assert (QB1 : 0 <= b 1%nat < 2 ^ 64) by (clear - RB1; lia).
  pose proof (HB 8%nat ltac:(clear; lia)) as RB8. assert (QB8 : 0 <= b 8%nat < 2 ^ 64) by (clear - RB8; lia).
  pose proof (HB 9%nat ltac:(clear; lia)) as RB9. assert (QB9 : 0 <= b 9%nat < 2 ^ 64) by (clear - RB9; lia).
  pose proof (HB 10%nat ltac:(clear; lia)) as RB10. assert (QB10 : 0 <= b 10%nat < 2 ^ 64) by (clear - RB10; lia).
  pose proof (HB 11%nat ltac:(clear; lia)) as RB11. assert (QB11 : 0 <= b 11%nat < 2 ^ 64) by (clear - RB11; lia).
  destruct (tab_facts MV6 (b 8%nat) IC ZT (HB 8%nat ltac:(clear; lia))) as (tl8 & th8 & T8a & T8b & T8c & T8d & T8e & QL8 & QH8).
  destruct (tab_facts MV6 (b 9%nat) IC ZT (HB 9%nat ltac:(clear; lia))) as (tl9 & th9 & T9a & T9b & T9c & T9d & T9e & QL9 & QH9).
  destruct (tab_facts MV6 (b 10%nat) IC ZT (HB 10%nat ltac:(clear; lia))) as (tl10 & th10 & T10a & T10b & T10c & T10d & T10e & QL10 & QH10).
  destruct (tab_facts MV6 (b 11%nat) IC ZT (HB 11%nat ltac:(clear; lia))) as (tl11 & th11 & T11a & T11b & T11c & T11d & T11e & QL11 & QH11).
  assert (SP8 : L5.u64_at RSEGS MV6 (sp - 160) (b 8%nat)).
  { apply (SV3 (sp - 160) (b 8%nat) ltac:(clear; lia) ltac:(clear; lia)). replace (sp - 160) with (sp - 224 + 8 * Z.of_nat 8) by (cbn; clear; lia). exact (HS 8%nat ltac:(clear; lia)). }
  assert (SP9 : L5.u64_at RSEGS MV6 (sp - 152) (b 9%nat)).
  { apply (SV3 (sp - 152) (b 9%nat) ltac:(clear; lia) ltac:(clear; lia)). replace (sp - 152) with (sp - 224 + 8 * Z.of_nat 9) by (cbn; clear; lia). exact (HS 9%nat ltac:(clear; lia)). }
  assert (SP10 : L5.u64_at RSEGS MV6 (sp - 144) (b 10%nat)).
  { apply (SV3 (sp - 144) (b 10%nat) ltac:(clear; lia) ltac:(clear; lia)). replace (sp - 144) with (sp - 224 + 8 * Z.of_nat 10) by (cbn; clear; lia). exact (HS 10%nat ltac:(clear; lia)). }
  assert (SP11 : L5.u64_at RSEGS MV6 (sp - 136) (b 11%nat)).
  { apply (SV3 (sp - 136) (b 11%nat) ltac:(clear; lia) ltac:(clear; lia)). replace (sp - 136) with (sp - 224 + 8 * Z.of_nat 11) by (cbn; clear; lia). exact (HS 11%nat ltac:(clear; lia)). }
  LeanFeed.pfeed P (PNARVOP.awvO5_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 57%nat => p | 80%nat => b 0%nat | 81%nat => b 1%nat | 88%nat => b 8%nat | 89%nat => b 9%nat | 90%nat => b 10%nat | 91%nat => b 11%nat | 108%nat => tl8 | 120%nat => th8 | 109%nat => tl9 | 121%nat => th9 | 110%nat => tl10 | 122%nat => th10 | 111%nat => tl11 | 123%nat => th11 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVOP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y10 & Y12 & Y15).
  assert (PB : In (p, c) (PNM.bparser_own s6 ++ LBX)) by (apply in_or_app; left; apply (PNBOA.PNM_own_tb s6 p c); exact taI).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH6 _ PB) as (PB0 & PB1). cbn [fst snd] in PB0, PB1.
  apply (PNARVKX.rv_piece_tb L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xafd04 0xafde4 M7v (fun a => p + 16 <= a < p + 16 + 8) (PM.VLong c n p) CTX G LM MS7 MG7).
  { intros a Ha N. apply FRZ7; [exact Ha| intros X; apply N; clear - X; lia]. }
  { intros a X. right; left. exists p, c. split; [exact taI| clear - X taC; lia]. }
  { rewrite ETB. reflexivity. }
  { rewrite <- ETB. exact GTB6. }
  { rewrite ETB. reflexivity. }
  { intros M3 FR3 MG3 VIS3. rewrite ETB in TBR6.
    apply (vstr_long_keep M6 M3 (fb + 464 + 368) c n p (fun a => p + 16 <= a < p + 16 + 8) ltac:(clear - pf5; lia) ltac:(clear - pf5; lia) PB0 PB1 FR3 MG3);
      [intros a X; clear - X; lia| clear - ta6; lia| exact ta3| exact TBR6]. }
  intros M8 model8 LM8 HID8 VIS8 FR8 MG8 ECK8.
  rewrite <- ETB in LM8. rewrite set_tb_id in LM8.
  apply (oid_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 c n p CTX G LM8 INV6).
  - apply (mido_keep R R6 R7 sp fb F MID6). unfold MIDOREGS. kks KS7.
  - rewrite (KS7 23%nat) by inl. exact X23.
  - exact (ECK8 _ _ EC6).
  - exact TP6.
  - exact BB6.
  - rewrite (KS7 13%nat) by inl; exact X13.
  - exact ETB.
Qed.

(* [comment removed for export] *)
Lemma oid_hex2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 c n p (b : nat -> Z) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  PNRA.binv s6 -> mido R R6 sp fb F -> getr R6 (reg 23) = Z_to_bv 64 (fb + 464 + 368) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PNM.b_bb s6 = PNM.b_bb s ->
  getr R6 (reg 25) = Z_to_bv 64 (b 1%nat) -> getr R6 (reg 26) = Z_to_bv 64 (b 0%nat) ->
  getr R6 (reg 10) = Z_to_bv 64 p -> getr R6 (reg 17) = Z_to_bv 64 145760 -> getr R6 (reg 13) = Z_to_bv 64 (((fb + 464 + 368) / 8) + 2147450880) ->
  PNM.b_tb s6 = PM.VLong c n p ->
  (forall i, (i < 12)%nat -> 0 <= b i <= 255) ->
  (forall i, (2 <= i < 12)%nat -> L5.u64_at RSEGS M6 (sp - 224 + 8 * Z.of_nat i) (b i)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xafc24 M6 model6) K.
Proof.
  intros CTX G LM INV6 MID6 X23 EC6 TP6 BB6 X25 X26 X10 X17 X13 ETB HB HS.
  pose proof MID6 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J24 & J27).
  pose proof LM as (BI6 & RP6 & _). pose proof BI6 as (HH6 & _). pose proof RP6 as (PA6 & _ & _ & _ & _ & _ & _ & GR6). destruct GR6 as (_ & GTB6 & _).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA6. pose proof PA6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TBR6 & _). change (fb + 464 + PNM.OFF_TB) with (fb + 464 + 368) in TBR6.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6897664 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  assert (IC : L5.img_clear MV6 65536 1269760) by assumption.
  match goal with H : _ <= sp <= _ |- _ => pose proof H as RSP end.
  pose proof (tab_shz _ _ _ _ _ _ _ HH6) as ZT. fold MV6 in ZT.
  pose proof (tb24_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 c n p CTX G LM ETB) as (ta1 & ta2 & ta3 & ta4 & ta5 & ta6 & ta7 & ta8 & ta9 & taZ & taI & taC).
  fold MV6 in ta4, taZ. conj_open taZ.
  assert (Q57 : 0 <= p < 2 ^ 64) by (clear - ta1; lia).
  pose proof (HB 0%nat ltac:(clear; lia)) as RB0. assert (QB0 : 0 <= b 0%nat < 2 ^ 64) by (clear - RB0; lia).
  pose proof (HB 1%nat ltac:(clear; lia)) as RB1. assert (QB1 : 0 <= b 1%nat < 2 ^ 64) by (clear - RB1; lia).
  pose proof (HB 4%nat ltac:(clear; lia)) as RB4. assert (QB4 : 0 <= b 4%nat < 2 ^ 64) by (clear - RB4; lia).
  pose proof (HB 5%nat ltac:(clear; lia)) as RB5. assert (QB5 : 0 <= b 5%nat < 2 ^ 64) by (clear - RB5; lia).
  pose proof (HB 6%nat ltac:(clear; lia)) as RB6. assert (QB6 : 0 <= b 6%nat < 2 ^ 64) by (clear - RB6; lia).
  pose proof (HB 7%nat ltac:(clear; lia)) as RB7. assert (QB7 : 0 <= b 7%nat < 2 ^ 64) by (clear - RB7; lia).
  destruct (tab_facts MV6 (b 4%nat) IC ZT (HB 4%nat ltac:(clear; lia))) as (tl4 & th4 & T4a & T4b & T4c & T4d & T4e & QL4 & QH4).
  destruct (tab_facts MV6 (b 5%nat) IC ZT (HB 5%nat ltac:(clear; lia))) as (tl5 & th5 & T5a & T5b & T5c & T5d & T5e & QL5 & QH5).
  destruct (tab_facts MV6 (b 6%nat) IC ZT (HB 6%nat ltac:(clear; lia))) as (tl6 & th6 & T6a & T6b & T6c & T6d & T6e & QL6 & QH6).
  destruct (tab_facts MV6 (b 7%nat) IC ZT (HB 7%nat ltac:(clear; lia))) as (tl7 & th7 & T7a & T7b & T7c & T7d & T7e & QL7 & QH7).
  assert (SP4 : L5.u64_at RSEGS MV6 (sp - 192) (b 4%nat)).
  { apply (SV3 (sp - 192) (b 4%nat) ltac:(clear; lia) ltac:(clear; lia)). replace (sp - 192) with (sp - 224 + 8 * Z.of_nat 4) by (cbn; clear; lia). exact (HS 4%nat ltac:(clear; lia)). }
  assert (SP5 : L5.u64_at RSEGS MV6 (sp - 184) (b 5%nat)).
  { apply (SV3 (sp - 184) (b 5%nat) ltac:(clear; lia) ltac:(clear; lia)). replace (sp - 184) with (sp - 224 + 8 * Z.of_nat 5) by (cbn; clear; lia). exact (HS 5%nat ltac:(clear; lia)). }
  assert (SP6 : L5.u64_at RSEGS MV6 (sp - 176) (b 6%nat)).
  { apply (SV3 (sp - 176) (b 6%nat) ltac:(clear; lia) ltac:(clear; lia)). replace (sp - 176) with (sp - 224 + 8 * Z.of_nat 6) by (cbn; clear; lia). exact (HS 6%nat ltac:(clear; lia)). }
  assert (SP7 : L5.u64_at RSEGS MV6 (sp - 168) (b 7%nat)).
  { apply (SV3 (sp - 168) (b 7%nat) ltac:(clear; lia) ltac:(clear; lia)). replace (sp - 168) with (sp - 224 + 8 * Z.of_nat 7) by (cbn; clear; lia). exact (HS 7%nat ltac:(clear; lia)). }
  LeanFeed.pfeed P (PNARVOP.awvO4_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 57%nat => p | 80%nat => b 0%nat | 81%nat => b 1%nat | 84%nat => b 4%nat | 85%nat => b 5%nat | 86%nat => b 6%nat | 87%nat => b 7%nat | 104%nat => tl4 | 116%nat => th4 | 105%nat => tl5 | 117%nat => th5 | 106%nat => tl6 | 118%nat => th6 | 107%nat => tl7 | 119%nat => th7 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVOP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y12 & Y15).
  assert (PB : In (p, c) (PNM.bparser_own s6 ++ LBX)) by (apply in_or_app; left; apply (PNBOA.PNM_own_tb s6 p c); exact taI).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH6 _ PB) as (PB0 & PB1). cbn [fst snd] in PB0, PB1.
  apply (PNARVKX.rv_piece_tb L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xafc24 0xafd04 M7v (fun a => p + 8 <= a < p + 8 + 8) (PM.VLong c n p) CTX G LM MS7 MG7).
  { intros a Ha N. apply FRZ7; [exact Ha| intros X; apply N; clear - X; lia]. }
  { intros a X. right; left. exists p, c. split; [exact taI| clear - X taC; lia]. }
  { rewrite ETB. reflexivity. }
  { rewrite <- ETB. exact GTB6. }
  { rewrite ETB. reflexivity. }
  { intros M3 FR3 MG3 VIS3. rewrite ETB in TBR6.
    apply (vstr_long_keep M6 M3 (fb + 464 + 368) c n p (fun a => p + 8 <= a < p + 8 + 8) ltac:(clear - pf5; lia) ltac:(clear - pf5; lia) PB0 PB1 FR3 MG3);
      [intros a X; clear - X; lia| clear - ta6; lia| exact ta3| exact TBR6]. }
  intros M8 model8 LM8 HID8 VIS8 FR8 MG8 ECK8.
  rewrite <- ETB in LM8. rewrite set_tb_id in LM8.
  apply (oid_hex3 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 c n p b CTX G LM8 INV6).
  - apply (mido_keep R R6 R7 sp fb F MID6). unfold MIDOREGS. kks KS7.
  - rewrite (KS7 23%nat) by inl. exact X23.
  - exact (ECK8 _ _ EC6).
  - exact TP6.
  - exact BB6.
  - rewrite (KS7 25%nat) by inl. exact X25.
  - rewrite (KS7 26%nat) by inl. exact X26.
  - rewrite (KS7 10%nat) by inl; exact X10.
  - rewrite (KS7 17%nat) by inl; exact X17.
  - rewrite (KS7 13%nat) by inl; exact X13.
  - exact ETB.
  - exact HB.
  - intros i Hi. apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 224 + 8 * Z.of_nat i)); [| clear - Hi RSP; lia| clear - Hi RSP; lia| exact (HS i Hi)].
    intros j Hj. apply FR8; [clear - Hj Hi RSP; lia|]. intros X. clear - X Hj Hi ta5. lia.
Qed.

(* [comment removed for export] *)
Lemma oid_hex1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 c n p (b : nat -> Z) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  PNRA.binv s6 -> mido R R6 sp fb F -> getr R6 (reg 23) = Z_to_bv 64 (fb + 464 + 368) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PNM.b_bb s6 = PNM.b_bb s ->
  getr R6 (reg 25) = Z_to_bv 64 (b 1%nat) -> getr R6 (reg 26) = Z_to_bv 64 (b 0%nat) ->
  PNM.b_tb s6 = PM.VLong c n p ->
  (forall i, (i < 12)%nat -> 0 <= b i <= 255) ->
  (forall i, (2 <= i < 12)%nat -> L5.u64_at RSEGS M6 (sp - 224 + 8 * Z.of_nat i) (b i)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaf4ac M6 model6) K.
Proof.
  intros CTX G LM INV6 MID6 X23 EC6 TP6 BB6 X25 X26 ETB HB HS.
  pose proof MID6 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J24 & J27).
  pose proof LM as (BI6 & RP6 & _). pose proof BI6 as (HH6 & _). pose proof RP6 as (PA6 & _ & _ & _ & _ & _ & _ & GR6). destruct GR6 as (_ & GTB6 & _).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA6. pose proof PA6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TBR6 & _). change (fb + 464 + PNM.OFF_TB) with (fb + 464 + 368) in TBR6.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6897664 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  assert (IC : L5.img_clear MV6 65536 1269760) by assumption.
  match goal with H : _ <= sp <= _ |- _ => pose proof H as RSP end.
  pose proof (tab_shz _ _ _ _ _ _ _ HH6) as ZT. fold MV6 in ZT.
  pose proof (PNARVKX.tbfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (tz1 & tz2 & tz3 & tz4 & tw1 & tw2 & TBV & TBM).
  rewrite ETB in TBM. destruct TBM as (tb1 & tb2 & tb3 & tb4 & tb5 & tb6 & tb7 & _). fold MV6 in tz1, tz2, tz3, tz4, tb1, tb4, tb5.
  assert (Q56 : 0 <= (c + 1) mod 256 < 2 ^ 64) by (clear - tb2; lia).
  assert (Q58 : 0 <= n < 2 ^ 64) by (clear - tb6 tb7; lia).
  pose proof (tb24_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 c n p CTX G LM ETB) as (ta1 & ta2 & ta3 & ta4 & ta5 & ta6 & ta7 & ta8 & ta9 & taZ & taI & taC).
  fold MV6 in ta4, taZ. conj_open taZ.
  assert (Q57 : 0 <= p < 2 ^ 64) by (clear - ta1; lia).
  pose proof (HB 0%nat ltac:(clear; lia)) as RB0. assert (QB0 : 0 <= b 0%nat < 2 ^ 64) by (clear - RB0; lia).
  pose proof (HB 1%nat ltac:(clear; lia)) as RB1. assert (QB1 : 0 <= b 1%nat < 2 ^ 64) by (clear - RB1; lia).
  pose proof (HB 2%nat ltac:(clear; lia)) as RB2. assert (QB2 : 0 <= b 2%nat < 2 ^ 64) by (clear - RB2; lia).
  pose proof (HB 3%nat ltac:(clear; lia)) as RB3. assert (QB3 : 0 <= b 3%nat < 2 ^ 64) by (clear - RB3; lia).
  destruct (tab_facts MV6 (b 0%nat) IC ZT (HB 0%nat ltac:(clear; lia))) as (tl0 & th0 & T0a & T0b & T0c & T0d & T0e & QL0 & QH0).
  destruct (tab_facts MV6 (b 1%nat) IC ZT (HB 1%nat ltac:(clear; lia))) as (tl1 & th1 & T1a & T1b & T1c & T1d & T1e & QL1 & QH1).
  destruct (tab_facts MV6 (b 2%nat) IC ZT (HB 2%nat ltac:(clear; lia))) as (tl2 & th2 & T2a & T2b & T2c & T2d & T2e & QL2 & QH2).
  destruct (tab_facts MV6 (b 3%nat) IC ZT (HB 3%nat ltac:(clear; lia))) as (tl3 & th3 & T3a & T3b & T3c & T3d & T3e & QL3 & QH3).
  assert (SP2 : L5.u64_at RSEGS MV6 (sp - 208) (b 2%nat)).
  { apply (SV3 (sp - 208) (b 2%nat) ltac:(clear; lia) ltac:(clear; lia)). replace (sp - 208) with (sp - 224 + 8 * Z.of_nat 2) by (cbn; clear; lia). exact (HS 2%nat ltac:(clear; lia)). }
  assert (SP3 : L5.u64_at RSEGS MV6 (sp - 200) (b 3%nat)).
  { apply (SV3 (sp - 200) (b 3%nat) ltac:(clear; lia) ltac:(clear; lia)). replace (sp - 200) with (sp - 224 + 8 * Z.of_nat 3) by (cbn; clear; lia). exact (HS 3%nat ltac:(clear; lia)). }
  LeanFeed.pfeed P (PNARVOP.awvO3_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 56%nat => (c + 1) mod 256 | 57%nat => p | 58%nat => n | 80%nat => b 0%nat | 81%nat => b 1%nat | 82%nat => b 2%nat | 83%nat => b 3%nat | 100%nat => tl0 | 112%nat => th0 | 101%nat => tl1 | 113%nat => th1 | 102%nat => tl2 | 114%nat => th2 | 103%nat => tl3 | 115%nat => th3 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVOP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y10 & Y12 & Y13 & Y15 & Y17).
  assert (PB : In (p, c) (PNM.bparser_own s6 ++ LBX)) by (apply in_or_app; left; apply (PNBOA.PNM_own_tb s6 p c); exact taI).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH6 _ PB) as (PB0 & PB1). cbn [fst snd] in PB0, PB1.
  apply (PNARVKX.rv_piece_tb L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaf4ac 0xafc24 M7v (fun a => p + 0 <= a < p + 0 + 8) (PM.VLong c n p) CTX G LM MS7 MG7).
  { intros a Ha N. apply FRZ7; [exact Ha| intros X; apply N; clear - X; lia]. }
  { intros a X. right; left. exists p, c. split; [exact taI| clear - X taC; lia]. }
  { rewrite ETB. reflexivity. }
  { rewrite <- ETB. exact GTB6. }
  { rewrite ETB. reflexivity. }
  { intros M3 FR3 MG3 VIS3. rewrite ETB in TBR6.
    apply (vstr_long_keep M6 M3 (fb + 464 + 368) c n p (fun a => p + 0 <= a < p + 0 + 8) ltac:(clear - pf5; lia) ltac:(clear - pf5; lia) PB0 PB1 FR3 MG3);
      [intros a X; clear - X; lia| clear - ta6; lia| exact ta3| exact TBR6]. }
  intros M8 model8 LM8 HID8 VIS8 FR8 MG8 ECK8.
  rewrite <- ETB in LM8. rewrite set_tb_id in LM8.
  apply (oid_hex2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 c n p b CTX G LM8 INV6).
  - apply (mido_keep R R6 R7 sp fb F MID6). unfold MIDOREGS. kks KS7.
  - rewrite (KS7 23%nat) by inl. exact X23.
  - exact (ECK8 _ _ EC6).
  - exact TP6.
  - exact BB6.
  - rewrite (KS7 25%nat) by inl. exact X25.
  - rewrite (KS7 26%nat) by inl. exact X26.
  - exact Y10.
  - exact Y17.
  - exact Y13.
  - exact ETB.
  - exact HB.
  - intros i Hi. apply (L5C.u64_at_agree RSEGS M6 M8 (sp - 224 + 8 * Z.of_nat i)); [| clear - Hi RSP; lia| clear - Hi RSP; lia| exact (HS i Hi)].
    intros j Hj. apply FR8; [clear - Hj Hi RSP; lia|]. intros X. clear - X Hj Hi ta5. lia.
Qed.


(* [comment removed for export] *)
Lemma oid_rsz K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 :
  PMA.str_resize_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  PNRA.binv s6 -> mid R R6 sp fb F -> getr R6 (reg 23) = Z_to_bv 64 (F + 416) -> getr R6 (reg 24) = Z_to_bv 64 (fb + 1024) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PNM.b_bb s6 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xaf440 M6 model6) K.
Proof.
  intros RSZ CTX G LM INV6 MID6 X23 X24 EC6 TP6 BB6.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID6 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6897664 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  match goal with H : _ <= sp <= _ |- _ => pose proof H as RSP end.
  match goal with H : 6897664 <= F <= _ |- _ => pose proof H as RF end.
  assert (DF : L5.defined MV6 F 512) by assumption.
  destruct (u8_of_defined MV6 (F + 416) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v0 & Hv0 & U0). assert (Q80 : 0 <= v0 < 2 ^ 64) by (clear - Hv0; lia).
  destruct (u8_of_defined MV6 (F + 417) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v1 & Hv1 & U1). assert (Q81 : 0 <= v1 < 2 ^ 64) by (clear - Hv1; lia).
  destruct (u8_of_defined MV6 (F + 418) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v2 & Hv2 & U2). assert (Q82 : 0 <= v2 < 2 ^ 64) by (clear - Hv2; lia).
  destruct (u8_of_defined MV6 (F + 419) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v3 & Hv3 & U3). assert (Q83 : 0 <= v3 < 2 ^ 64) by (clear - Hv3; lia).
  destruct (u8_of_defined MV6 (F + 420) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v4 & Hv4 & U4). assert (Q84 : 0 <= v4 < 2 ^ 64) by (clear - Hv4; lia).
  destruct (u8_of_defined MV6 (F + 421) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v5 & Hv5 & U5). assert (Q85 : 0 <= v5 < 2 ^ 64) by (clear - Hv5; lia).
  destruct (u8_of_defined MV6 (F + 422) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v6 & Hv6 & U6). assert (Q86 : 0 <= v6 < 2 ^ 64) by (clear - Hv6; lia).
  destruct (u8_of_defined MV6 (F + 423) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v7 & Hv7 & U7). assert (Q87 : 0 <= v7 < 2 ^ 64) by (clear - Hv7; lia).
  destruct (u8_of_defined MV6 (F + 424) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v8 & Hv8 & U8). assert (Q88 : 0 <= v8 < 2 ^ 64) by (clear - Hv8; lia).
  destruct (u8_of_defined MV6 (F + 425) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v9 & Hv9 & U9). assert (Q89 : 0 <= v9 < 2 ^ 64) by (clear - Hv9; lia).
  destruct (u8_of_defined MV6 (F + 426) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v10 & Hv10 & U10). assert (Q90 : 0 <= v10 < 2 ^ 64) by (clear - Hv10; lia).
  destruct (u8_of_defined MV6 (F + 427) ltac:(clear - RF; lia) ltac:(clear - RF; lia) ltac:(apply (L5.defined_sub MV6 F 512); [exact DF| clear; lia| clear; lia])) as (v11 & Hv11 & U11). assert (Q91 : 0 <= v11 < 2 ^ 64) by (clear - Hv11; lia).
  set (b := fun i : nat => nth i [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11] 0).
  LeanFeed.pfeed P (PNARVOP.awvO2_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 80%nat => v0 | 81%nat => v1 | 82%nat => v2 | 83%nat => v3 | 84%nat => v4 | 85%nat => v5 | 86%nat => v6 | 87%nat => v7 | 88%nat => v8 | 89%nat => v9 | 90%nat => v10 | 91%nat => v11 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVOP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & Y12 & Y23 & Y25 & Y26 & C11 & C10 & C9 & C8 & C7 & C6 & C5 & C4 & C3 & C2).
  apply (PNARVK.rv_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xaf440 0xd3ce0 M7v (fun a => sp - 208 <= a < sp - 208 + 80) CTX G LM MS7 MG7).
  { intros a Ha N. apply FRZ7; [exact Ha| exact N]. }
  { intros a X. clear - X; lia. }
  intros M8 model8 LM8 HID8 VIS8 FR8 MG8 ECK8.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM8) as (_ & _ & _ & _ & _ & _ & SVr8).
  pose proof (PNARVKX.tbfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM8) as (_ & _ & _ & _ & _ & _ & _ & TBM).
  assert (SZ0 : 0 <= PM.vs_size (PNM.b_tb s6)) by (destruct (PNM.b_tb s6) as [n0|c0 n0 p0]; cbn [PM.vs_size]; [destruct TBM as (X & _); clear - X; lia| destruct TBM as (_ & _ & _ & _ & _ & X & _); clear - X; lia]).
  assert (S2 : L5.u64_at RSEGS M8 (sp - 208) v2) by (apply (SVr8 (sp - 208) v2 ltac:(clear; lia) ltac:(clear; lia)); rewrite HID8, VIS8; exact C2).
  assert (S3 : L5.u64_at RSEGS M8 (sp - 200) v3) by (apply (SVr8 (sp - 200) v3 ltac:(clear; lia) ltac:(clear; lia)); rewrite HID8, VIS8; exact C3).
  assert (S4 : L5.u64_at RSEGS M8 (sp - 192) v4) by (apply (SVr8 (sp - 192) v4 ltac:(clear; lia) ltac:(clear; lia)); rewrite HID8, VIS8; exact C4).
  assert (S5 : L5.u64_at RSEGS M8 (sp - 184) v5) by (apply (SVr8 (sp - 184) v5 ltac:(clear; lia) ltac:(clear; lia)); rewrite HID8, VIS8; exact C5).
  assert (S6 : L5.u64_at RSEGS M8 (sp - 176) v6) by (apply (SVr8 (sp - 176) v6 ltac:(clear; lia) ltac:(clear; lia)); rewrite HID8, VIS8; exact C6).
  assert (S7 : L5.u64_at RSEGS M8 (sp - 168) v7) by (apply (SVr8 (sp - 168) v7 ltac:(clear; lia) ltac:(clear; lia)); rewrite HID8, VIS8; exact C7).
  assert (S8 : L5.u64_at RSEGS M8 (sp - 160) v8) by (apply (SVr8 (sp - 160) v8 ltac:(clear; lia) ltac:(clear; lia)); rewrite HID8, VIS8; exact C8).
  assert (S9 : L5.u64_at RSEGS M8 (sp - 152) v9) by (apply (SVr8 (sp - 152) v9 ltac:(clear; lia) ltac:(clear; lia)); rewrite HID8, VIS8; exact C9).
  assert (S10 : L5.u64_at RSEGS M8 (sp - 144) v10) by (apply (SVr8 (sp - 144) v10 ltac:(clear; lia) ltac:(clear; lia)); rewrite HID8, VIS8; exact C10).
  assert (S11 : L5.u64_at RSEGS M8 (sp - 136) v11) by (apply (SVr8 (sp - 136) v11 ltac:(clear; lia) ltac:(clear; lia)); rewrite HID8, VIS8; exact C11).
  assert (HS8 : forall i, (2 <= i < 12)%nat -> L5.u64_at RSEGS M8 (sp - 224 + 8 * Z.of_nat i) (b i)).
  { intros i Hi. assert (Ei : (i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11)%nat) by (clear - Hi; lia). destruct Ei as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ] ] ] ] ] ] ] ] ]; cbn [b nth]; [replace (sp - 224 + 8 * Z.of_nat 2) with (sp - 208) by (cbn; clear; lia); exact S2 | replace (sp - 224 + 8 * Z.of_nat 3) with (sp - 200) by (cbn; clear; lia); exact S3 | replace (sp - 224 + 8 * Z.of_nat 4) with (sp - 192) by (cbn; clear; lia); exact S4 | replace (sp - 224 + 8 * Z.of_nat 5) with (sp - 184) by (cbn; clear; lia); exact S5 | replace (sp - 224 + 8 * Z.of_nat 6) with (sp - 176) by (cbn; clear; lia); exact S6 | replace (sp - 224 + 8 * Z.of_nat 7) with (sp - 168) by (cbn; clear; lia); exact S7 | replace (sp - 224 + 8 * Z.of_nat 8) with (sp - 160) by (cbn; clear; lia); exact S8 | replace (sp - 224 + 8 * Z.of_nat 9) with (sp - 152) by (cbn; clear; lia); exact S9 | replace (sp - 224 + 8 * Z.of_nat 10) with (sp - 144) by (cbn; clear; lia); exact S10 | replace (sp - 224 + 8 * Z.of_nat 11) with (sp - 136) by (cbn; clear; lia); exact S11]. }
  assert (HB : forall i, (i < 12)%nat -> 0 <= b i <= 255).
  { intros i Hi. assert (Ei : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11)%nat) by (clear - Hi; lia). destruct Ei as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ] ] ] ] ] ] ] ] ] ] ]; cbn [b nth]; [exact Hv0 | exact Hv1 | exact Hv2 | exact Hv3 | exact Hv4 | exact Hv5 | exact Hv6 | exact Hv7 | exact Hv8 | exact Hv9 | exact Hv10 | exact Hv11]. }
  assert (MO7 : mido R R7 sp fb F).
  { unfold mido. rewrite (KS7 2%nat), (KS7 3%nat), (KS7 4%nat), (KS7 8%nat), (KS7 9%nat), (KS7 18%nat), (KS7 19%nat), (KS7 20%nat), (KS7 21%nat), (KS7 22%nat), (KS7 24%nat), (KS7 27%nat) by inl.
    repeat split; assumption. }
  pose proof MO7 as (E2 & E3 & E4 & _).
  apply (PNARVKT.rv_call_resize L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 0xaf4ac 24 1 RSZ ltac:(right; reflexivity) CTX G LM8 Y1).
  { unfold L5.ra_ok; clear; lia. }
  { exact E2. }
  { rewrite E3. exact Rgp. }
  { rewrite E4. exact Rtp. }
  { change (PNRA.bcs_off 1) with 368. exact Y10. }
  { exact Y11. }
  { change (PNRA.bcs_str 1 s6) with (PNM.b_tb s6). unfold PM.CHUNK. clear - SZ0. lia. }
  { unfold PM.CHUNK. clear. lia. }
  intros fx9 R9 M9 model9 LK9 Aw9 x' g' cr9 RP9 SZ9 LM9 FRC9 ECK9.
  pose proof LM9 as (_ & RP9' & _). pose proof RP9' as (PA9 & _). change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA9.
  pose proof PA9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB9 & _).
  assert (ETB9 : PNM.b_tb (set_cs 1 s6 x' g') = x') by (exact (PNBKA.set_cs_str 1 s6 x' g')).
  rewrite ETB9 in TB9.
  destruct x' as [n'|c' n' p'].
  { exfalso. destruct TB9 as (_ & _ & Hn' & _). cbn [PM.vs_size] in SZ9. clear - Hn' SZ9. lia. }
  assert (CS : forall k, In k L5SAR.cs_all -> getr R9 (reg k) = getr R7 (reg k)) by (intros k Hk; exact (L5SAR.cs_of_preserved R7 R9 k RP9 Hk)).
  apply (oid_hex1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M9 model9 LK9 Aw9 (set_cs 1 s6 (PM.VLong c' n' p') g') sm6 ax6 cr9 fx9 R9 c' n' p' b CTX G LM9).
  - unfold PNRA.binv. rewrite PNBKA.set_cs_done, PNBKA.set_cs_stk. exact INV6.
  - apply (mido_keep R R7 R9 sp fb F MO7). intros k Hk. apply CS. revert k Hk. unfold MIDOREGS. kin.
  - rewrite (CS 23%nat) by inl. exact Y23.
  - exact (ECK9 _ _ (ECK8 _ _ EC6)).
  - destruct TP6 as (l0 & c0 & c0' & TS1 & TS2 & REST). exists l0, c0, c0'. rewrite PNBKA.set_cs_stk. split; [exact TS1|]. split; [exact TS2| exact REST].
  - rewrite PNBKA.set_cs_bb. exact BB6.
  - rewrite (CS 25%nat) by inl. exact Y25.
  - rewrite (CS 26%nat) by inl. exact Y26.
  - exact ETB9.
  - exact HB.
  - intros i Hi. apply (L5C.u64_at_agree RSEGS M8 M9 (sp - 224 + 8 * Z.of_nat i)); [| clear - Hi RSP; lia| clear - Hi RSP; lia| exact (HS8 i Hi)].
    intros j Hj. apply FRC9. clear - Hj Hi. lia.
Qed.


(* [comment removed for export] *)
Lemma oid_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2
      M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx4 : FPState) R4 :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> mid R R4 sp fb F ->
  getr R4 (reg 1) = Z_to_bv 64 0xb01b8 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R4 (reg 11) = Z_to_bv 64 1 -> getr R4 (reg 23) = Z_to_bv 64 (F + 416) -> getr R4 (reg 24) = Z_to_bv 64 (fb + 1024) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xad694 M3 model3) K.
Proof.
  intros MKE CTX G LM INV3 MID4 X1 X10 X11 X23 X24 EC3 LEN3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID4 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  change 0xad694 with (pa_make_ec PMA.AD).
  apply (PNARVK.rv_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 0xb01b8 1 e cat MKE CTX G LM EC3 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5)
    as (PF5 & OWN5 & SV5 & U8v5 & WRop5 & U8op5 & SVr5).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5)
    as (U10 & WR8 & OVIS5 & VF5 & VSH5 & MO5).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (F + 416)) by (rewrite (L5SAR.cs_of_preserved R4 R5 23%nat RP5) by inl; exact X23).
  assert (E24 : getr R5 (reg 24) = Z_to_bv 64 (fb + 1024)) by (rewrite (L5SAR.cs_of_preserved R4 R5 24%nat RP5) by inl; exact X24).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (clear - pf5; lia).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVOP.awvOc_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVOP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z1 & Z10 & Z11 & HMAG & SH53 & SH52 & MO0 & D8).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3
           fx5 fx9 R5 R9 0xb01b8 0 M9v CTX G LM5 MS9 MG9).
  - intros a Ha N1 N2 N3. apply FRZ9; [exact Ha| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia| intros X; apply N3; clear - X; lia].
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO0.
  - left; reflexivity.
  - exact Z1.
  - exact Z10.
  - exact Z11.
  - rewrite (KS9 2%nat) by inl. exact E2.
  - rewrite (KS9 8%nat) by inl. exact E8.
  - rewrite (KS9 19%nat) by inl. exact E19.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - left. exists 1. split; [clear; lia|]. split; [exact EC5|]. split; [reflexivity| apply bax_cat_add].
  - exact INV3.
  - exact LEN3.
  - intros _ X. exfalso. clear - X. lia.
Qed.


Lemma sh_apart e F : e mod 8 = 0 -> F / 8 * 8 = F -> ((e - 40) + 40 <= F \/ F + 512 <= (e - 40)) ->
  ((((e - 24) / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= (((e - 24) / 8) + 2147450880)).
Proof.
  intros He HF [X|X].
  - left. assert ((e - 24) / 8 < F / 8) by (apply Z.div_lt_upper_bound; [Lia.lia| rewrite Z.mul_comm, HF; Lia.lia]). Lia.lia.
  - right. assert (F / 8 + 64 <= (e - 24) / 8) by (apply Z.div_le_lower_bound; [Lia.lia| Lia.lia]). Lia.lia.
Qed.

(* [comment removed for export] *)
Lemma arm_oid K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  PNRAa.src_read_spec L ar HI -> PNRAa.make_ec_spec L ar HI -> PMA.str_resize_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 7 F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xaeb88 M3 model3) K.
Proof.
  intros SR MKE RSZ CTX G LM DR EC3.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (7 - 1)) with (Z_to_bv 64 6) in D13.
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof GFR as (GF1 & GF2 & GF3 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  (* [comment removed for export] *)
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM)
    as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (clear - pf5; lia).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ7_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xaeb88 0xaf3d4 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  pose proof (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)) as MIDj.
  (* [comment removed for export] *)
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M3 modelj LK3 Aw3 s sm ax cr CTX G LMj)
    as (PFj & _).
  unfold pfacts in PFj. conj_open PFj.
  pose proof MIDj as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  LeanFeed.pfeed P (PNARVOP.awvO0_conc fxj Rj (mrestrict (ahid Aw3 modelj) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVOP.aligned; assumption]).
  destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & A1 & A10 & A11 & A12 & A23 & SHZ4 & SHZ0).
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M3 modelj LK3 Aw3 s sm ax cr
           fxj fxa Rj Ra 0xaf3d4 0xadae0 Mav (fun a => F / 8 + 2147450880 + 52 <= a < F / 8 + 2147450880 + 52 + 2) CTX G LMj MSa MGa).
  { intros a Ha N. apply FRZa; [exact Ha| intros X; apply N; clear - X; lia]. }
  { intros a X. right; right. clear - X; lia. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MG4 ECK4.
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr CTX G LM4)
    as (_ & _ & _ & _ & VSH4 & _).
  assert (SHB : forall k v, (k = 52 \/ k = 53) -> L5.u8_at RSEGS Mav (F / 8 + 2147450880 + k) v -> byte_at M4 (F / 8 + k + 2147450880) v).
  { intros k v Hk U. assert (SHR : 0 <= F / 8 + 2147450880 + k /\ F / 8 + 2147450880 + k + 1 <= 2 ^ 64) by (clear - DF1 DF2 Hk; lia).
    assert (U4 : L5.u8_at RSEGS M4 (F / 8 + 2147450880 + k) v).
    { apply (proj1 (L5A.u8_at_vis (ahid Aw3 model4) M4 (F / 8 + 2147450880 + k) v (L5A.avis_sub _ (F / 8 + 2147450880) 64 (F / 8 + 2147450880 + k) 1 VSH4 ltac:(clear - Hk; lia) ltac:(clear - Hk; lia)) (proj1 SHR) (proj2 SHR))).
      rewrite HID4, VIS4. exact U. }
    unfold byte_at. replace (F / 8 + k + 2147450880) with (F / 8 + 2147450880 + k) by (clear; lia).
    exact (L5ADHR.byte_of_u8 M4 (F / 8 + 2147450880 + k) v U4 ltac:(right; clear - DF1 Hk; lia) ltac:(clear - SHR; lia)). }
  assert (HF0 : 0 <= F) by (clear - GF1; lia).
  assert (ACC : aacc M4 (F + 416) 12).
  { pose proof (aacc_local M4 F 416 8 0 (proj1 GF8) ltac:(reflexivity) ltac:(clear; lia) HF0 ltac:(left; split; reflexivity)
                  ltac:(change (416 / 8) with 52; apply (SHB 52 0 ltac:(left; reflexivity)); replace (F / 8 + 2147450880 + 52) with (F / 8 + 2147450932) by (clear; lia); exact SHZ0)) as A1'.
    pose proof (aacc_local M4 F 424 4 4 (proj1 GF8) ltac:(reflexivity) ltac:(clear; lia) HF0 ltac:(right; split; [clear; lia| reflexivity])
                  ltac:(change (424 / 8) with 53; apply (SHB 53 4 ltac:(right; reflexivity)); replace (F / 8 + 2147450880 + 53) with (F / 8 + 2147450933) by (clear; lia); exact SHZ4)) as A2'.
    intros a Ha. destruct (Z_lt_le_dec a (F + 424)) as [X|X]; [apply A1'; clear - Ha X; lia| apply A2'; clear - Ha X; lia]. }
  assert (MIDa : mid R Ra sp fb F) by (apply (mid_keep R Rj Ra sp fb F MIDj); unfold MIDREGS; kks KSa).
  pose proof MIDa as (B2 & B3 & B4 & _).
  change 0xadae0 with (pa_src_read PMA.AD).
  apply (PNARVK.rv_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr fxa Ra 0xaf3f4 416 12 SR CTX G LM4
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ACC A1).
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  { exact A10. }
  { exact A11. }
  { exact A12. }
  intros fx5 R5 M5 model5 LK5 Aw5 src5 sm5 d RP5 Y10d Hd UNR5 RD1 RD0 DEF5 QC5 LM5 AG5 ECK5.
  set (s5 := PNM.with_srcB s src5) in *.
  assert (INV5 : PNRA.binv s5) by exact INV.
  pose proof (PNBKA.btop_pos_refl s INV) as TP0.
  pose proof TP0 as (pre & top & c0 & ES & _).
  assert (ES5 : PNM.b_stk s5 = pre ++ [top]) by exact ES.
  assert (TP5 : PNRA.btop_pos s s5) by exact TP0.
  assert (EC5 : PMSPA.ec_at RSEGS M5 (fb + 1024) e cat) by (apply ECK5; apply ECK4; exact EC3).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax cr CTX G LM5)
    as (PF5 & _).
  pose proof (PNARVK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax cr pre top CTX G LM5 INV5 ES5)
    as (TF5 & PT5 & OKt5 & VIN5 & TB15 & TB25 & TB35 & TB45).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  set (e5 := PNM.b_sb s5 + 40 * Z.of_nat (length pre) + 40) in *.
  set (p5 := (d + PNM.bs_pos top) mod 2 ^ 64).
  unfold pfacts in PF5. conj_open PF5.
  unfold tfacts in TF5. destruct TF5 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  pose proof (sh_apart e5 F tf4 (proj1 GF8) tf11) as SHAP.
  assert (MID5 : mid R R5 sp fb F).
  { apply (mid_keep R Ra R5 sp fb F MIDa). intros k Hk. apply (L5SAR.cs_of_preserved Ra R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (F + 416)) by (rewrite (L5SAR.cs_of_preserved Ra R5 23%nat RP5) by inl; exact A23).
  assert (E10 : getr R5 (reg 10) = Z_to_bv 64 d) by exact Y10d.
  assert (Q37 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (QP5 : 0 <= p5 < 2 ^ 64) by (unfold p5; apply Z.mod_pos_bound; clear; lia).
  assert (QVb : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6897664 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QVb as (QVb1 & QVb2).
  LeanFeed.pfeed P (PNARVOP.awvO1_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 37%nat => d | 38%nat => e5 | 39%nat => PNM.bs_pos top | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVOP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [X0|X1]).
  - (* [comment removed for export] *)
    destruct X0 as (MS6 & KS6 & Y11 & Y12 & Y13 & Y24 & CND & CP6).
    apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax cr fx5 fx6 R5 R6 0xaf3f4 0xaf440 M6v pre top p5
             CTX G LM5 INV5 ES5 MS6 MG6 FRZ6 CP6 QP5).
    intros M7 model7 LM7 HID7 VIS7 FR7 MGM7 ECK7.
    set (top' := PNM.BS (PNM.bs_mode top) (PNM.bs_len top) p5 (PNM.bs_type top) (PNM.bs_idx top)) in *.
    set (s7 := PNBO.set_stk s5 (pre ++ [top'])) in *.
    assert (OK' : PNM.bstate_ok top').
    { destruct OKt5 as (X1 & X2 & X3 & X4 & X5). unfold PNM.bstate_ok, top'. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      split; [exact X1|]. split; [exact X2|]. split; [exact QP5|]. split; [exact X4| exact X5]. }
    assert (INV7 : PNRA.binv s7) by (apply (PNBKA.binv_set_stk_top s5 pre top top' INV5 ES5 OK'); reflexivity).
    assert (TP7 : PNRA.btop_pos s s7).
    { apply (PNBKA.btop_pos_trans s s5 s7 TP5). apply (PNBKA.btop_pos_set_stk s5 pre top top' ES5 OK'); reflexivity. }
    apply (oid_rsz K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax cr fx6 R6 RSZ CTX G LM7 INV7).
    + apply (mid_keep R R5 R6 sp fb F MID5). unfold MIDREGS. kks KS6.
    + rewrite (KS6 23%nat) by inl. exact E23.
    + exact Y24.
    + apply ECK7. exact EC5.
    + exact TP7.
    + reflexivity.
  - (* [comment removed for export] *)
    destruct X1 as (MS6 & KS6 & Y1 & Y10 & Y11 & Y12 & Y13 & Y24 & CND & CP6).
    apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax cr fx5 fx6 R5 R6 0xaf3f4 0xad694 M6v pre top p5
             CTX G LM5 INV5 ES5 MS6 MG6 FRZ6 CP6 QP5).
    intros M7 model7 LM7 HID7 VIS7 FR7 MGM7 ECK7.
    set (top' := PNM.BS (PNM.bs_mode top) (PNM.bs_len top) p5 (PNM.bs_type top) (PNM.bs_idx top)) in *.
    set (s7 := PNBO.set_stk s5 (pre ++ [top'])) in *.
    assert (OK' : PNM.bstate_ok top').
    { destruct OKt5 as (X1 & X2 & X3 & X4 & X5). unfold PNM.bstate_ok, top'. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      split; [exact X1|]. split; [exact X2|]. split; [exact QP5|]. split; [exact X4| exact X5]. }
    assert (INV7 : PNRA.binv s7) by (apply (PNBKA.binv_set_stk_top s5 pre top top' INV5 ES5 OK'); reflexivity).
    assert (TP7 : PNRA.btop_pos s s7).
    { apply (PNBKA.btop_pos_trans s s5 s7 TP5). apply (PNBKA.btop_pos_set_stk s5 pre top top' ES5 OK'); reflexivity. }
    apply (oid_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 7 F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax cr fx6 R6 MKE CTX G LM7 INV7).
    + apply (mid_keep R R5 R6 sp fb F MID5). unfold MIDREGS. kks KS6.
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + rewrite (KS6 23%nat) by inl. exact E23.
    + exact Y24.
    + apply ECK7. exact EC5.
    + exact (btop_len s s7 TP7).
Qed.


End WithHeap.
End PNARVO.
