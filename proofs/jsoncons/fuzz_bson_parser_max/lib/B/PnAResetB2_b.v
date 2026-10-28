(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PnModel PmModelFacts PmStatics PmStaticsA PnStatics PnStaticsA
     PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAIss1_b PnAEmbKit_b PnBrObjA_b PnAResetBStmts_b PnAResetBGlue_b PnAResetBP_b PnAResetBKit_b PnAVu8Dtor_b PnAVecDtor_b PnAHarnessKit3_b PnAReset1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNARB2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Lemma zsub (M : word -> option byte) a n a' n' : L5KA.zeros_at M a n -> a <= a' -> a' + n' <= a + n -> L5KA.zeros_at M a' n'.
Proof. intros Z H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply Z. lia. Qed.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Theorem mids : PNARBG.mids_stmt L ar HI.
Proof.
  unfold PNARBG.mids_stmt. intros ASH fx R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s R M model LK Aw PRE MID KONT.
  destruct PRE as (_ & _ & K0 & ENT & FRM & FRS & FOK & _ & _ & _ & _).
  unfold PNARBS.smid1, PNARBS.smid in MID. unfold PNARBS.op, PNARBS.SCR in *. set (op := fb + 464) in *. change (14336 / 8) with 1792 in MID.
  destruct MID as (G2 & G8 & G18 & G19 & GCS & SV & PA & ACC & BASE & ASTK & STKSH & HH & AM & MRT & INCLK & INCAw & EK0 & DK0).
  destruct ENT as (_ & RAok & _ & Rgp & Rtp & _ & _).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct FOK as ((rs & Hfb) & FB8).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & ND & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn in F1, F2. change (ff_bytes 5) with 2048 in F2.
  assert (AOP : PMSPA.aobjA FF op 416) by (exists (fb, 5, rs); split; [exact Hfb| cbn; unfold op; change (ff_bytes 5) with 2048; clear; lia]).
  assert (FB16 : fb mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply (Z.divide_trans 16 2048 fb); [exists 128; reflexivity| apply Z.mod_divide; [lia| exact FB8]]).
  assert (O8 : op mod 8 = 0) by (unfold op; replace (fb + 464) with (fb - (-464)) by lia; apply PMAIS1.sub8; [exact FB16| reflexivity]).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMKA.aobj_of_aobjA FF op 416 AOP O8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model op 416 sp 14336 HH AOB ltac:(lia) ltac:(reflexivity))
    as ((Ov1 & Ov2 & Ov3 & Ov4 & Ov5) & OBIG & ODEF & OVIS & OVSH & OCL & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  pose proof BASE as (ICB & _). cbn [pa_rw_lo PMA.AD ADDR_A] in ICB.
  assert (OPS : op + 416 + 4096 + 14336 <= sp) by (clear - Ov2 SLO; lia).
  pose proof PA as (P0 & PD & PC0 & P8 & P9 & P10 & P12 & PNI & PSRC & P312 & PC312 & PBB & PNB & PTB & PSTK & PM01 & PD01).
  unfold PNARBS.st1 in PBB, PNB, PTB, PSTK. cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk] in PBB, PNB, PTB, PSTK.
  unfold PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  assert (ZOP : L5KA.zeros_at MV (op / 8 + 2147450880) 52)
    by exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model op 416 HH AOP O8 ltac:(lia) ltac:(reflexivity) ACC).
  assert (VSW : L5.writable RSEGS MV (sp - 64) 64).
  { apply (proj2 (L5A.writable_vis H M (sp - 64) 64 (VIS (sp - 64) 64 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]| lia| lia]. }
  assert (IC1 : L5.img_clear MV 65536 1282048) by (apply L5A.img_clear_mrestrict; exact ICB).
  assert (CSBv : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (OVs : forall a n, op <= a -> a + n <= op + 416 -> L5A.avis H a n) by (intros a n X1 X2; eapply L5A.avis_sub; [exact OVIS| lia| lia]).
  assert (OWs : forall a n, op <= a -> a + n <= op + 416 -> 0 < n -> L5.writable RSEGS MV a n).
  { intros a n X1 X2 X3. apply (proj2 (L5A.writable_vis H M a n (OVs a n X1 X2) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M op 416); [exact ODEF| lia| lia]| lia| lia]. }
  assert (Q1 : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia).
  assert (Q2 : 0 <= op < 2 ^ 64) by (clear - Ov1 Ov3; lia).
  assert (Q3 : 140735332487216 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (Q4 : 6905856 <= op <= 140737488354912) by (clear - Ov1 Ov3; lia).
  assert (Q5 : PNARBP.aligned op 8) by exact O8.
  assert (Q6 : PNARBP.aligned sp 16) by exact A16.
  assert (Q7 : L5KA.zeros_at MV (op / 8 + 2147450881) 1) by (apply (zsub MV (op / 8 + 2147450880) 52); [exact ZOP| lia| lia]).
  assert (Q8 : L5KA.zeros_at MV (op / 8 + 2147450920) 12) by (apply (zsub MV (op / 8 + 2147450880) 52); [exact ZOP| lia| lia]).
  assert (DV : forall d, 0 <= d < 416 -> (op + d) / 8 = op / 8 + d / 8).
  { intros d Hd. rewrite <- Ov5. replace (op / 8 * 8 + d) with (d + op / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (Q9 : L5KA.zeros_at MV ((op + 9) / 8 + 2147450880) 1) by (rewrite (DV 9) by lia; change (9 / 8) with 1; apply (zsub MV (op / 8 + 2147450880) 52); [exact ZOP| lia| lia]).
  assert (Q10 : L5KA.zeros_at MV ((op + 345) / 8 + 2147450880) 1) by (rewrite (DV 345) by lia; change (345 / 8) with 43; apply (zsub MV (op / 8 + 2147450880) 52); [exact ZOP| lia| lia]).
  assert (Q11 : L5KA.zeros_at MV ((op + 369) / 8 + 2147450880) 1) by (rewrite (DV 369) by lia; change (369 / 8) with 46; apply (zsub MV (op / 8 + 2147450880) 52); [exact ZOP| lia| lia]).
  assert (Q12 : (sp - 64) + 64 <= op \/ op + 416 <= sp - 64) by (right; clear - OPS; lia).
  set (nb := PNM.b_nb s) in *. set (tb := PNM.b_tb s) in *. set (sb := PNM.b_sb s) in *. set (sk := PNM.b_sk s) in *. set (stk := PNM.b_stk s) in *.
  set (OWN := PNM.bparser_own s) in *.
  pose proof PSTK as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AB & EL). unfold PNM.BSZ in V8, V16, DB, CB, AB.
  set (len := Z.of_nat (length stk)) in *.
  assert (P2k : 1 <= 2 ^ sk <= 2048) by (clear - Hk; split; [apply (Z.pow_le_mono_r 2 0 sk); lia| apply (Z.pow_le_mono_r 2 sk 11); lia]).
  assert (ISB : In (sb, 40 * 2 ^ sk) (OWN ++ LBX)) by (apply in_or_app; left; exact (PNBOA.PNM_own_stk s)).
  pose proof (WB _ ISB) as ((Sb0 & Sb1 & Sb2 & Sb3 & Sb4 & Sb5) & _). cbn [fst snd] in Sb0, Sb5. unfold app_mem in Sb5. destruct Sb5 as (_ & _ & Sb47).
  set (inW := fun (W : list L5.range) (a : Z) => exists rg, In rg W /\ L5.in_rng rg a).
  set (wcell := fun rg : L5.range => 0 < snd rg /\ ((op + 344 <= fst rg /\ fst rg + snd rg <= op + 392)
                                       \/ (exists B m, In (B, m) (PM.vs_own nb ++ PM.vs_own tb) /\ B <= fst rg /\ fst rg + snd rg <= B + m))).
  assert (TAIL : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1v : word -> option byte) (W2 : list L5.range),
     mem_grows MV M1v ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ inW W2 a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
     msteps RSEGS (st fx R 0xadbd0 MV) (st fx1 R1 0xab740 M1v) ->
     (forall x, In x [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x)) ->
     getr R1 (reg 1) = Z_to_bv 64 711932 -> getr R1 (reg 10) = Z_to_bv 64 (op + 392) -> getr R1 (reg 18) = Z_to_bv 64 (op + 392) ->
     (forall rg, In rg W2 -> wcell rg) ->
     match nb with PM.VShort _ => L5.u8_at RSEGS M1v (op + 344) 0 | PM.VLong c _ p => L5.u64_at RSEGS M1v (op + 344) (c + 1) /\ L5.u64_at RSEGS M1v (op + 352) 0 /\ L5.u64_at RSEGS M1v (op + 360) p end ->
     match tb with PM.VShort _ => L5.u8_at RSEGS M1v (op + 368) 0 | PM.VLong c _ p => L5.u64_at RSEGS M1v (op + 368) (c + 1) /\ L5.u64_at RSEGS M1v (op + 376) 0 /\ L5.u64_at RSEGS M1v (op + 384) p end ->
     srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xadbd0 M model) K).
  { intros fx1 R1 M1v W2 MG1 FRZ1 MS1 KS1 A11 A110 A118 WC CNB CTB.
    (* [comment removed for export] *)
    unfold PMSPA.cfg.
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xadbd0 R1 0xab740 M1v
             (fun a => inW W2 a \/ (op + 400 <= a < op + 400 + 8)) K HH AM MS1 MG1).
    { intros a Ha Hnw. apply FRZ1; [exact Ha| intros X; apply Hnw; left; exact X]. }
    { intros a Ha [(rg & Hin & Hr)|X].
      - destruct (WC rg Hin) as (Hpos & [(Y1 & Y2)|(B & m & HB & Y1 & Y2)]); unfold L5.in_rng in Hr.
        + split; [apply (L5SAR.obj_client L ar _ FF 0 0 op 416 a AOB); clear - Hr Y1 Y2; lia| clear - Hr Y1 Y2 Ov1; lia].
        + assert (HB' : In (B, m) (OWN ++ LBX)).
          { apply in_or_app; left. apply in_app_or in HB as [HB|HB]; [exact (PNBOA.PNM_own_nb s B m HB)| exact (PNBOA.PNM_own_tb s B m HB)]. }
          pose proof (WB _ HB') as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _). cbn [fst snd] in *.
          rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Bb1.
          split; [left; exists (B, m); split; [exact HB'| cbn [fst snd]; clear - Hr Y1 Y2; lia]| clear - Hr Y1 Y2 Bb1 Bb0; lia].
      - split; [apply (L5SAR.obj_client L ar _ FF 0 0 op 416 a AOB); clear - X; lia| clear - X Ov1; lia]. }
    intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4 VV4. change (mrestrict H M4 = M1v) in VIS4.
    (* [comment removed for export] *)
    assert (OPN : PNAV8D.nsh op 416) by (unfold PNAV8D.nsh; clear - OBIG; lia).
    set (P4 := fun a => inW W2 a \/ (op + 400 <= a < op + 400 + 8)) in FR4.
    assert (P4sh : forall x, BIGSHADOW_LO <= x < BIGSHADOW_HI -> ~ P4 x).
    { intros x Hx [(rg & Hin & Hr)|Y]; [|exact (PNAV8D.nsh_not op 416 x OPN ltac:(clear - Y; lia) Hx)].
      destruct (WC rg Hin) as (Hpos & [(Y1 & Y2)|(B & m & HB & Y1 & Y2)]); unfold L5.in_rng in Hr.
      - exact (PNAV8D.nsh_not op 416 x OPN ltac:(clear - Hr Y1 Y2; lia) Hx).
      - assert (HB' : In (B, m) (OWN ++ LBX)).
        { apply in_or_app; left. apply in_app_or in HB as [HB|HB]; [exact (PNBOA.PNM_own_nb s B m HB)| exact (PNBOA.PNM_own_tb s B m HB)]. }
        pose proof (WB _ HB') as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _). cbn [fst snd] in *. unfold app_mem in Bb5.
        unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - Hx Hr Y1 Y2 Bb5. lia. }
    assert (SHM4 : forall a m, 0 <= a -> a + m <= 2 ^ 47 -> PMFA.agsh M M4 a m).
    { intros a m Ha Hn x Hx. pose proof (PMKA.S_in_shadow x ltac:(clear - Ha Hn Hx; lia)) as SX. apply FR4; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia| apply P4sh; exact SX]. }
    assert (SP16 : forall j, (sp - 16 * j) mod 8 = 0) by (intros j; apply PMKA.mod16_8'; replace (sp - 16 * j) with (sp + (- j) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
    assert (ASTK4 : L5CA.astk ar M4 sp 14336) by exact (L5SAR.astk_grows ar M M4 sp 14336 ASTK MGM4).
    assert (ASTK4c : L5CA.astk ar M4 (sp - 64) 12288).
    { apply (L5SAR.astk_sub ar M M4 sp 14336 64 12288 ASTK MGM4); [clear; lia|clear; lia|clear; lia|]. replace (sp - 64) with (sp + (-4) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
    assert (SZk : forall lo g, lo mod 8 = 0 -> 0 <= lo -> lo + 8 * g <= 2 ^ 47 -> 0 <= g -> shadow_zero M lo g -> shadow_zero M4 lo g).
    { intros lo g Hlo H0 H1 Hg SZ j Hj. pose proof (SZ j Hj) as Z1. unfold byte_at in *. rewrite (PMFA.S_granule lo j Hlo ltac:(clear - Hj; lia)) in *.
      pose proof (PMKA.S_in_shadow (lo + 8 * j) ltac:(clear - H0 H1 Hj; lia)) as SX. rewrite FR4; [exact Z1| unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia| apply P4sh; exact SX]. }
    assert (SZ4 : shadow_zero M4 (sp - 14336) 1792).
    { apply SZk; [replace (sp - 14336) with (sp - 16 * 896) by (clear; lia); apply SP16| clear - Q3; lia| clear - Q3; lia| clear; lia| exact STKSH]. }
    assert (SZ4c : shadow_zero M4 (sp - 64 - 12288) 1536).
    { apply (PMKA.shadow_zero_sub M4 (sp - 14336) 1792); [replace (sp - 14336) with (sp - 16 * 896) by (clear; lia); apply SP16| replace (sp - 64 - 12288) with (sp - 16 * 772) by (clear; lia); apply SP16| clear; lia| clear; lia| clear; lia| exact SZ4]. }
    assert (AG4 : forall a n, (forall i, a <= i < a + n -> ~ P4 i) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M4 a n).
    { intros a n NP Ha Hn i Hi. apply FR4; [clear - Ha Hn Hi; lia| apply NP; exact Hi]. }
    assert (NOBJ : forall i, (op <= i < op + 344 \/ op + 392 <= i < op + 400 \/ op + 408 <= i < op + 416) -> ~ P4 i).
    { intros i Hi [(rg & Hin & Hr)|Y]; [|clear - Hi Y; lia].
      destruct (WC rg Hin) as (Hpos & [(Y1 & Y2)|(B & m & HB & Y1 & Y2)]); unfold L5.in_rng in Hr; [clear - Hi Hr Y1 Y2; lia|].
      assert (HB' : In (B, m) (OWN ++ LBX)).
      { apply in_or_app; left. apply in_app_or in HB as [HB|HB]; [exact (PNBOA.PNM_own_nb s B m HB)| exact (PNBOA.PNM_own_tb s B m HB)]. }
      pose proof (WB _ HB') as (_ & _ & _ & _ & _ & _ & X). cbn [fst snd] in X. unfold op in Hi. clear - X Hi Hr Y1 Y2 F1 F2. lia. }
    assert (C400m : L5.u64_at RSEGS M4 (op + 400) (sb + 40 * len)).
    { apply (proj1 (L5A.u64_at_vis H M4 (op + 400) _ (OVs (op + 400) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))). rewrite VIS4.
      apply (L5C.u64_at_agree RSEGS MV M1v (op + 400)); [| clear - Q2; lia| clear - Ov3; lia|].
      - intros i Hi. apply FRZ1; [clear - Hi Q2 Ov3; lia|]. intros (rg & Hin & Hr).
        destruct (WC rg Hin) as (Hpos & [(Y1 & Y2)|(B & m & HB & Y1 & Y2)]); unfold L5.in_rng in Hr; [clear - Hi Hr Y1 Y2; lia|].
        assert (HB' : In (B, m) (OWN ++ LBX)).
        { apply in_or_app; left. apply in_app_or in HB as [HB|HB]; [exact (PNBOA.PNM_own_nb s B m HB)| exact (PNBOA.PNM_own_tb s B m HB)]. }
        pose proof (WB _ HB') as (_ & _ & _ & _ & _ & _ & X). cbn [fst snd] in X. unfold op in Hi. clear - X Hi Hr Y1 Y2 F1 F2. lia.
      - apply (proj2 (L5A.u64_at_vis H M (op + 400) _ (OVs (op + 400) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))). replace (op + 400) with (op + 392 + 8) by (clear; lia). exact V8. }
    assert (V0m : L5.u64_at RSEGS M4 (op + 392) sb).
    { apply (L5C.u64_at_agree RSEGS M M4 (op + 392)); [apply AG4; [intros i Hi; apply NOBJ; clear - Hi; lia| clear - Q2; lia| clear - Ov3; lia]| clear - Q2; lia| clear - Ov3; lia| exact V0]. }
    assert (V16m : L5.u64_at RSEGS M4 (op + 392 + 16) (sb + 40 * 2 ^ sk)).
    { apply (L5C.u64_at_agree RSEGS M M4 (op + 392 + 16)); [apply AG4; [intros i Hi; apply NOBJ; clear - Hi; lia| clear - Q2; lia| clear - Ov3; lia]| clear - Q2; lia| clear - Ov3; lia| exact V16]. }
    (* [comment removed for export] *)
    set (LBc := lb_remove sb (OWN ++ LBX)).
    pose proof (PNAV8D.ri_front L ar C HI HIok _ _ _ _ _ _ _ sb (40 * 2 ^ sk) HH4 ISB) as HH4s. fold LBc in HH4s.
    change ((sb, 40 * 2 ^ sk) :: LBc) with (PNM.bvec_own sb sk ++ LBc) in HH4s.
    set (Wx := W2 ++ [(op + 400, 8)]).
    assert (OUTX : forall i, ~ P4 i -> L5.outside Wx i).
    { intros i NP rg Hin Hr. apply NP. unfold Wx in Hin. apply in_app_or in Hin as [Hin|[<-|[]]]; [left; exists rg; split; [exact Hin| exact Hr]| right; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; exact Hr]. }
    assert (WBk : forall B m, In (B, m) (PM.vs_own nb ++ PM.vs_own tb) -> In (B, m) (OWN ++ LBX)).
    { intros B m HB. apply in_or_app; left. apply in_app_or in HB as [HB|HB]; [exact (PNBOA.PNM_own_nb s B m HB)| exact (PNBOA.PNM_own_tb s B m HB)]. }
    assert (AOV : PMSPA.aobjA FF (op + 392) 24) by (apply (PNAV8D.aobjA_sub FF op 416); [exact AOP| clear; lia| clear; lia]).
    assert (EK04 : L5SAR.ek L ar LBc FF sp 14336 Wx M M4).
    { intros a (Ha & Hc & Ho). apply FR4; [exact Ha|]. intros [(rg & Hin & Hr)|X].
      - apply (Ho rg); [unfold Wx; apply in_or_app; left; exact Hin| exact Hr].
      - apply (Ho (op + 400, 8)); [unfold Wx; apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; exact X]. }
    assert (V8m : (op + 392) mod 8 = 0) by (replace (op + 392) with (op + 49 * 8) by (clear; lia); rewrite Z.mod_add by (clear; lia); exact O8).
    assert (NIMG : forall i, 65536 <= i < 6905856 -> ~ P4 i).
    { intros i Hi [(rg & Hin & Hr)|Y]; [|clear - Hi Y Ov1; lia].
      destruct (WC rg Hin) as (Hpos & [(Y1 & Y2)|(B & m & HB & Y1 & Y2)]); unfold L5.in_rng in Hr; [clear - Hi Hr Y1 Y2 Ov1; lia|].
      pose proof (WB _ (WBk B m HB)) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _). cbn [fst snd] in *.
      rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Bb1. clear - Hi Hr Y1 Y2 Bb0 Bb1. lia. }
    assert (STD : forall a, PMST.dep PMA.AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside Wx a).
    { intros a D. pose proof (PMAIS1.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
      split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUTX. apply NIMG. clear - DI. lia. }
    assert (SRO : forall a, 65536 <= a < pa_rw_lo PMA.AD -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside Wx a).
    { intros a Ha. cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - Ha; lia|].
      split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X) as Y; clear - Ha Y; lia|]. apply OUTX. apply NIMG. clear - Ha. lia. }
    assert (NSB : forall i, sb <= i < sb + 40 * 2 ^ sk -> ~ P4 i).
    { pose proof (WB _ ISB) as (_ & _ & _ & _ & APs & _ & FSs). cbn [fst snd] in APs, FSs.
      intros i Hi [(rg & Hin & Hr)|Y]; [|unfold op in Y; clear - Hi Y FSs F1 F2; lia].
      destruct (WC rg Hin) as (Hpos & [(Y1 & Y2)|(B & m & HB & Y1 & Y2)]); unfold L5.in_rng in Hr; [unfold op in Y1, Y2; clear - Hi Hr Y1 Y2 FSs F1 F2; lia|].
      assert (NE : sb <> B).
      { intros E. subst B. assert (NDo : NoDup (map fst OWN)) by (rewrite map_app in ND; apply stdpp.list_relations.list.NoDup_app in ND; exact (proj1 ND)).
        change OWN with ([(PM.sr_qc (PNM.b_src s), PM.CHUNK)] ++ (sb, 40 * 2 ^ sk) :: (PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own nb ++ PM.vs_own tb)) in NDo.
        cbn [app map fst] in NDo. apply stdpp.list_relations.list.NoDup_cons in NDo as (_ & NDo). apply stdpp.list_relations.list.NoDup_cons in NDo as (N1 & _).
        apply N1. rewrite map_app. apply list_elem_of_In. apply in_or_app; right. exact (in_map fst _ _ HB). }
      pose proof (L5C.blocks_apart_in sb (40 * 2 ^ sk) _ B m APs (L5C.in_lb_remove_neq sb B m _ (WBk B m HB) (fun E => NE (eq_sym E)))) as X.
      clear - X Hi Hr Y1 Y2. lia. }
    apply (ASH fx1 R1 M4 model4 K LBc FF LK Aw cr (op + 392) sb sk stk (sp - 64) 711932 HH4s AM4 K0).
    { split; [rewrite L5K.rl1; exact A11|]. split; [split; [clear; lia| reflexivity]|].
      split; [rewrite L5K.rl2, (KS1 2%nat) by inl; exact G2|].
      split; [rewrite L5K.rl3, (KS1 3%nat) by inl; rewrite (GCS 3%nat) by inl; exact Rgp|].
      split; [rewrite L5K.rl4, (KS1 4%nat) by inl; rewrite (GCS 4%nat) by inl; exact Rtp|].
      change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK4c|]. change (12288 / 8) with 1536. exact SZ4c. }
    { intros f Hf. specialize (FRS f Hf). clear - FRS. lia. }
    { rewrite L5K.rl10. exact A110. }
    { exact AOV. }
    { exact V8m. }
    { apply (PMFA.accA_agree M M4); [apply SHM4; clear - Q2 Ov3; lia|]. intros a Ha. apply ACC. clear - Ha. lia. }
    { unfold PNM.bvec_at, PNM.BSZ. split; [exact V0m|]. split; [replace (op + 392 + 8) with (op + 400) by (clear; lia); exact C400m|].
      split; [exact V16m|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
      split; [intros i Hi; apply MGM4; apply DB; exact Hi|].
      split; [apply (PMFA.accA_agree M M4); [apply SHM4; unfold len in *; clear - Sb0 Sb47 Hlen P2k; nia| exact CB]|].
      split. { apply (PNAEK.ann_agree M M4 sb (40 * len) (40 * 2 ^ sk)); [| unfold len; clear; lia| unfold len in *; clear - Hlen; lia| exact AB].
               intros j Hj. rewrite (PNAEK.S_add8 sb j). apply (SHM4 sb (8 * ((40 * 2 ^ sk + 7) / 8))); [clear - Sb0; lia| | ].
               - clear - Sb0 Sb47 Hal P2k. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
               - clear - Hj P2k. Lia.lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      intros i Hi. apply (PnModelFacts.PNMF.bstate_at_agree RSEGS M M4); [unfold len in *; clear - Sb0 Hi; lia| unfold len in *; clear - Sb0 Sb47 Hlen P2k Hi; nia| | exact (EL i Hi)].
      apply AG4; [intros j Hj; apply NSB; unfold len in *; clear - Hj Hi Hlen P2k; nia| unfold len in *; clear - Sb0 Hi; lia| unfold len in *; clear - Sb0 Sb47 Hlen P2k Hi; nia]. }
    { exact (PMKA.base_ok_keepA RSEGS PMA.AD L ar LBc FF sp 14336 Wx M M4 EK04 PMA.addrs_wf_A STD SRO BASE). }
    intros fx5 R5 M5 model5 LK5 Aw5 RP5 VEC5 ACV5 HP5 MRT5 INCLK5 INCAw5 AM5 HH5.
    change (PMSPA.pm_scr 0) with 12288 in HP5.
    apply (KONT fx5 R5 M5 model5 LK5 Aw5).
    unfold PNARBS.smid2, PNARBS.smid. unfold PNARBS.op, PNARBS.SCR. fold op. change (14336 / 8) with 1792.
    (* [comment removed for export] *)
    set (bb0 := PNM.b_bb s) in *.
    assert (NDo : NoDup (map fst OWN)) by (rewrite map_app in ND; apply stdpp.list_relations.list.NoDup_app in ND; exact (proj1 ND)).
    assert (OWNE : OWN = [(PM.sr_qc (PNM.b_src s), PM.CHUNK)] ++ (sb, 40 * 2 ^ sk) :: (PGV8.v8_own bb0 ++ PM.vs_own nb ++ PM.vs_own tb)) by reflexivity.
    assert (BXE : LBc = ([(PM.sr_qc (PNM.b_src s), PM.CHUNK)] ++ PGV8.v8_own bb0 ++ PM.vs_own nb ++ PM.vs_own tb) ++ LBX).
    { unfold LBc. rewrite (PNARBK.lbr_app_l sb OWN LBX (in_map fst OWN (sb, 40 * 2 ^ sk) (PNBOA.PNM_own_stk s))). f_equal.
      apply (PNHAK3.lb_remove_at sb (40 * 2 ^ sk) OWN [(PM.sr_qc (PNM.b_src s), PM.CHUNK)] (PGV8.v8_own bb0 ++ PM.vs_own nb ++ PM.vs_own tb) OWNE NDo). }
    assert (INC : forall x, In x LBc -> In x (OWN ++ LBX)) by (intros x Hx; exact (L5C.in_lb_remove _ x _ Hx)).
    assert (IQC : In (PM.sr_qc (PNM.b_src s), PM.CHUNK) LBc) by (rewrite BXE; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
    assert (IBB : forall B m, In (B, m) (PGV8.v8_own bb0) -> In (B, m) LBc).
    { intros B m Hin. rewrite BXE. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hin. }
    assert (INB : forall B m, In (B, m) (PM.vs_own nb) -> In (B, m) LBc).
    { intros B m Hin. rewrite BXE. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. exact Hin. }
    assert (ITB : forall B m, In (B, m) (PM.vs_own tb) -> In (B, m) LBc).
    { intros B m Hin. rewrite BXE. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hin. }
    (* [comment removed for export] *)
    assert (NSTR : forall q m', (In (q, m') [(PM.sr_qc (PNM.b_src s), PM.CHUNK)] \/ In (q, m') (PGV8.v8_own bb0)) -> forall B m, In (B, m) (PM.vs_own nb ++ PM.vs_own tb) -> q <> B).
    { intros q m' Hq B m HB E. subst B. rewrite OWNE in NDo. cbn [app map fst] in NDo.
      apply stdpp.list_relations.list.NoDup_cons in NDo as (N1 & NDo). apply stdpp.list_relations.list.NoDup_cons in NDo as (_ & NDo).
      rewrite map_app in NDo. destruct Hq as [[Hq|[]]|Hq].
      - injection Hq as <- <-. apply N1. right. rewrite map_app. apply list_elem_of_In. apply in_or_app; right. exact (in_map fst _ _ HB).
      - apply stdpp.list_relations.list.NoDup_app in NDo as (_ & NX & _). apply (NX q); apply list_elem_of_In; [exact (in_map fst _ _ Hq)| exact (in_map fst _ _ HB)]. }
    assert (WAPPx : PMKA.wapp Wx).
    { intros rg Hin. unfold Wx in Hin. apply in_app_or in Hin as [Hin|[<-|[]]].
      - destruct (WC rg Hin) as (Hpos & [(Y1 & Y2)|(B & m & HB & Y1 & Y2)]).
        + unfold PNAV8D.nsh in OPN. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OPN Y1 Y2 Hpos. lia.
        + pose proof (WB _ (WBk B m HB)) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _). cbn [fst snd] in *. unfold app_mem in Bb5.
          unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - Hpos Y1 Y2 Bb5. lia.
      - cbn [fst snd]. unfold PNAV8D.nsh in OPN. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OPN. lia. }
    assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
    { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). clear - X1 X2 FSAPP. unfold app_mem, FS_BYTES in *. lia. }
    assert (BRB : forall b0, In b0 LBc -> 0 <= fst b0 /\ fst b0 + snd b0 <= 2 ^ 47).
    { intros b0 Hb0. destruct (proj1 (WB b0 (INC b0 Hb0))) as (X0 & _ & _ & _ & _ & X5). clear - X0 X5. unfold app_mem in X5. lia. }
    assert (EK45 : L5SAR.ek L ar LBc FF sp 14336 Wx M4 M5).
    { apply (L5SAR.ek_callee L ar LBc [] FF [] sp 14336 (sp - 64) 12288 Wx [(op + 392 + 8, 8)] M4 M5 HP5); [clear; lia| clear; lia|].
      intros a _ Ho rg [<-|[]] Hr. apply (Ho (op + 400, 8)); [unfold Wx; apply in_or_app; right; left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; clear - Hr; lia]. }
    pose proof (L5SAR.ek_trans L ar LBc FF sp 14336 Wx M M4 M5 EK04 EK45) as EK05.
    assert (EK45n : L5SAR.ek L ar LBc FF sp 14336 [(op + 392 + 8, 8)] M4 M5).
    { apply (L5SAR.ek_callee L ar LBc [] FF [] sp 14336 (sp - 64) 12288 [(op + 392 + 8, 8)] [(op + 392 + 8, 8)] M4 M5 HP5); [clear; lia| clear; lia| intros a _ Ho; exact Ho]. }
    assert (WX1 : PMKA.wapp [(op + 392 + 8, 8)]) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold PNAV8D.nsh in OPN; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OPN; lia| exact PMKA.wapp_nil]).
    assert (DK05 : L5SAR.dk L ar LBc FF sp 14336 M M5).
    { apply (L5SAR.dk_trans L ar LBc FF sp 14336 M M4 M5); [exact (L5SAR.dk_grows L ar LBc FF sp 14336 M M4 MGM4)|].
      apply (L5SAR.dk_callee L ar LBc [] FF [] sp 14336 (sp - 64) 12288 [(op + 392 + 8, 8)] M4 M5 HP5); clear; lia. }
    assert (ASTK5 : L5CA.astk ar M5 sp 14336) by (apply (PMKA.astk_after_ahpres L ar LBc FF M4 M5 sp 14336 (sp - 64) 12288 [(op + 392 + 8, 8)] ASTK4 HP5); [clear; lia| clear; lia| clear; lia| exact STOP]).
    assert (SZ5 : shadow_zero M5 (sp - 14336) 1792).
    { apply (PMKA.stksh_keepA L ar LBc FF sp 14336 Wx M4 M5 EK45 WAPPx (sp - 14336) 1792); [clear - Q3; lia| clear - SLO; lia| clear - Q3; lia| replace (sp - 14336) with (sp - 16 * 896) by (clear; lia); apply SP16| clear; lia| exact SZ4]. }
    assert (ACC5 : PMSPA.accA M5 op 416) by exact (PMKA.acc_keepA' L ar LBc FF sp 14336 Wx M M5 EK05 WAPPx FRB op 416 AOP ACC).
    assert (NSTK : forall i, sp - 14336 <= i -> ~ P4 i).
    { intros i Hi [(rg & Hin & Hr)|Y]; [|clear - Hi Y OPS; lia].
      destruct (WC rg Hin) as (Hpos & [(Y1 & Y2)|(B & m & HB & Y1 & Y2)]); unfold L5.in_rng in Hr; [clear - Hi Hr Y1 Y2 OPS; lia|].
      pose proof (WB _ (WBk B m HB)) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _). cbn [fst snd] in *. clear - Hi Hr Y1 Y2 Bb0 Bb1 Bb2 Bb3 Bb4 SLO. lia. }
    assert (BASE5 : PMSTA.base_okA RSEGS PMA.AD M5) by (apply (PMKA.base_ok_keepA RSEGS PMA.AD L ar LBc FF sp 14336 Wx M M5 EK05 PMA.addrs_wf_A STD SRO BASE)).
    assert (SV5 : PNARBS.saves R0 sp M5).
    { destruct HP5 as (P5 & _ & _). destruct SV as (X8 & X16 & X24 & X32 & X40 & X48).
      assert (AGS : forall a, sp - 48 <= a < sp -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. rewrite P5; [apply FR4; [clear - Ha Q3; lia| apply NSTK; clear - Ha; lia]|]. split; [clear - Ha Q3; lia|].
        split; [| intros r0 [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Ha Hr OPS; lia].
        unfold aclient, aclient_g. right; left. split; [clear - Ha SLO SHI SPT; lia| intros Z; clear - Ha Z; lia]. }
      unfold PNARBS.saves. split; [|split; [|split; [|split; [|split]]]].
      - apply (L5C.u64_at_agree RSEGS M M5 (sp - 8)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X8].
      - apply (L5C.u64_at_agree RSEGS M M5 (sp - 16)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X16].
      - apply (L5C.u64_at_agree RSEGS M M5 (sp - 24)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X24].
      - apply (L5C.u64_at_agree RSEGS M M5 (sp - 32)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X32].
      - apply (L5C.u64_at_agree RSEGS M M5 (sp - 40)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X40].
      - apply (L5C.u64_at_agree RSEGS M M5 (sp - 48)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X48]. }
    assert (REG5 : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg j) = getr R1 (reg j))
      by (intros j Hj; exact (L5SAR.cs_of_preserved R1 R5 j RP5 Hj)).
    (* [comment removed for export] *)
    assert (BNP : forall q m', In (q, m') LBc -> (forall B m, In (B, m) (PM.vs_own nb ++ PM.vs_own tb) -> q <> B) -> forall i, q <= i < q + m' -> ~ P4 i).
    { intros q m' Hq NE i Hi. pose proof (WB _ (INC _ Hq)) as (_ & _ & _ & _ & AP & _ & FSA). cbn [fst snd] in AP, FSA.
      intros [(rg & Hin & Hr)|Y]; [|unfold op in Y; clear - Hi Y FSA F1 F2; lia].
      destruct (WC rg Hin) as (Hpos & [(Y1 & Y2)|(B & m & HB & Y1 & Y2)]); unfold L5.in_rng in Hr; [unfold op in Y1, Y2; clear - Hi Hr Y1 Y2 FSA F1 F2; lia|].
      pose proof (L5C.blocks_apart_in q m' _ B m AP (L5C.in_lb_remove_neq q B m _ (WBk B m HB) (fun E => NE B m HB (eq_sym E)))) as X.
      clear - X Hi Hr Y1 Y2. lia. }
    set (NT := fun i : Z => M5 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    set (YY := fun i : Z => M (Z_to_bv 64 i) <> None -> M5 (Z_to_bv 64 i) <> None).
    set (NS := fun i : Z => M5 (Z_to_bv 64 (S i)) = M (Z_to_bv 64 (S i))).
    assert (AGXl : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> NT i) -> L5C.agree_on M M5 a n) by (intros a n _ _ X i Hi; exact (X i Hi)).
    assert (DKYl : forall i, YY i -> M (Z_to_bv 64 i) <> None -> M5 (Z_to_bv 64 i) <> None) by (intros i X; exact X).
    assert (SHXl : forall a n, (forall i, a <= i < a + n -> NS i) -> PMFA.agsh M M5 a n) by (intros a n X x Hx; exact (X x Hx)).
    assert (NTO : forall a n, op <= a -> a + n <= op + 416 -> (a + n <= op + 344 \/ (op + 392 <= a /\ a + n <= op + 400) \/ op + 408 <= a) -> forall i, a <= i < a + n -> NT i).
    { intros a n X1 X2 X3 i Hi.
      refine (proj1 (PMKA.agA_obj L ar LBc FF sp 14336 Wx M M5 EK05 WAPPx FRB a n (PNAV8D.aobjA_sub FF op 416 a n AOP X1 X2) _) i Hi).
      intros j Hj. apply OUTX. apply NOBJ. clear - Hj X1 X2 X3. lia. }
    pose proof (PMKA.agsh_obj L ar LBc FF sp 14336 Wx M M5 EK05 WAPPx FRB op 416 AOP) as OSH.
    assert (NSO : forall i, op <= i < op + 416 -> NS i) by (intros i Hi; exact (OSH i Hi)).
    assert (YO : forall i, op <= i < op + 416 -> YY i).
    { intros i Hi. unfold YY. apply DK05; [clear - Hi Q2 Ov3; lia|]. exact (L5SAR.obj_client L ar LBc FF sp 14336 op 416 i AOB Hi). }
    assert (BLKA : forall q m', In (q, m') LBc -> (forall B m, In (B, m) (PM.vs_own nb ++ PM.vs_own tb) -> q <> B) -> PMFA.agA M M5 q m').
    { intros q m' Hq NE. apply (PMKA.agA_blk L ar LBc FF sp 14336 Wx M M5 EK05 WAPPx BRB q m' Hq). intros i Hi. apply OUTX. exact (BNP q m' Hq NE i Hi). }
    assert (AQC : PMFA.agA M M5 (PM.sr_qc (PNM.b_src s)) PM.CHUNK) by (apply (BLKA _ _ IQC); intros B m HB; exact (NSTR _ _ (or_introl (or_introl eq_refl)) B m HB)).
    assert (ABB : forall B m, In (B, m) (PGV8.v8_own bb0) -> PMFA.agA M M5 B m) by (intros B m HB; apply (BLKA _ _ (IBB B m HB)); intros B' m'' HB'; exact (NSTR _ _ (or_intror HB) B' m'' HB')).
    (* [comment removed for export] *)
    assert (VW4 : forall a v, op <= a -> a + 8 <= op + 400 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M4 a v).
    { intros a v X1 X2 U. apply (proj1 (L5A.u64_at_vis H M4 a v (OVs a 8 X1 ltac:(clear - X2; lia)) ltac:(clear - X1 Q2; lia) ltac:(clear - X2 Ov3; lia))). rewrite VIS4. exact U. }
    assert (VB4 : forall a v, op <= a -> a + 1 <= op + 400 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M4 a v).
    { intros a v X1 X2 U. apply (proj1 (L5A.u8_at_vis H M4 a v (OVs a 1 X1 ltac:(clear - X2; lia)) ltac:(clear - X1 Q2; lia) ltac:(clear - X2 Ov3; lia))). rewrite VIS4. exact U. }
    assert (STR4 : forall o x, (o = op + 344 \/ o = op + 368) -> incl (PM.vs_own x) (PM.vs_own nb ++ PM.vs_own tb) -> PM.vstr_at RSEGS PMSPA.accA M o x ->
                   match x with PM.VShort _ => L5.u8_at RSEGS M1v o 0 | PM.VLong c _ p => L5.u64_at RSEGS M1v o (c + 1) /\ L5.u64_at RSEGS M1v (o + 8) 0 /\ L5.u64_at RSEGS M1v (o + 16) p end ->
                   PM.vstr_at RSEGS PMSPA.accA M4 o (PNRA.vs_clear x)).
    { intros o x Ho IX (D & Cc & Rr) CX. split; [intros i Hi; apply MGM4; apply D; exact Hi|].
      split; [apply (PMFA.accA_agree M M4); [apply SHM4; clear - Ho Q2 Ov3; lia| exact Cc]|].
      destruct x as [n|c n p]; cbn [PNRA.vs_clear].
      - split; [clear; lia|]. change (2 * 0) with 0. apply VB4; [clear - Ho; lia| clear - Ho; lia| exact CX].
      - destruct Rr as (W0 & W8 & W16 & Hn & Hc & Hev & DBp & CBp). destruct CX as (X0 & X8 & X16).
        split; [apply VW4; [clear - Ho; lia| clear - Ho; lia| exact X0]|]. split; [apply VW4; [clear - Ho; lia| clear - Ho; lia| exact X8]|].
        split; [apply VW4; [clear - Ho; lia| clear - Ho; lia| exact X16]|]. split; [clear - Hn Hc; lia|]. split; [exact Hc|]. split; [exact Hev|].
        pose proof (WB _ (WBk p c (IX (p, c) ltac:(left; reflexivity)))) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _). cbn [fst snd] in *. unfold app_mem in Bb5.
        split; [intros i Hi; apply MGM4; apply DBp; exact Hi|]. apply (PMFA.accA_agree M M4); [apply SHM4; clear - Bb5; lia| exact CBp]. }
    assert (NB4 : PM.vstr_at RSEGS PMSPA.accA M4 (op + 344) (PNRA.vs_clear nb)).
    { apply (STR4 (op + 344) nb); [left; reflexivity| intros y Hy; apply in_or_app; left; exact Hy| exact PNB|].
      destruct nb; [exact CNB|]. replace (op + 344 + 8) with (op + 352) by (clear; lia). replace (op + 344 + 16) with (op + 360) by (clear; lia). exact CNB. }
    assert (TB4 : PM.vstr_at RSEGS PMSPA.accA M4 (op + 368) (PNRA.vs_clear tb)).
    { apply (STR4 (op + 368) tb); [right; reflexivity| intros y Hy; apply in_or_app; right; exact Hy| exact PTB|].
      destruct tb; [exact CTB|]. replace (op + 368 + 8) with (op + 376) by (clear; lia). replace (op + 368 + 16) with (op + 384) by (clear; lia). exact CTB. }
    assert (STR5 : forall o x, (o = op + 344 \/ o = op + 368) -> (forall B m, In (B, m) (PM.vs_own x) -> In (B, m) LBc) ->
                   PM.vstr_at RSEGS PMSPA.accA M4 o x -> PM.vstr_at RSEGS PMSPA.accA M5 o x).
    { intros o x Ho IX V4.
      assert (AO : PMFA.agA M4 M5 o 24).
      { apply (PMKA.agA_obj L ar LBc FF sp 14336 [(op + 392 + 8, 8)] M4 M5 EK45n WX1 FRB o 24 (PNAV8D.aobjA_sub FF op 416 o 24 AOP ltac:(clear - Ho; lia) ltac:(clear - Ho; lia))).
        intros i Hi r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ho Hi Hr. lia. }
      assert (AB5 : forall B m, In (B, m) (PM.vs_own x) -> PMFA.agA M4 M5 B m).
      { intros B m HB. apply (PMKA.agA_blk L ar LBc FF sp 14336 [(op + 392 + 8, 8)] M4 M5 EK45n WX1 BRB B m (IX B m HB)).
        intros i Hi r0 [<-|[]] Hr. pose proof (WB _ (INC _ (IX B m HB))) as (_ & _ & _ & _ & _ & _ & FSA). cbn [fst snd] in FSA.
        unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold op in Hr. clear - FSA Hi Hr F1 F2. lia. }
      apply (PNBOA.vstr_keep_x RSEGS M4 M5 (fun i => M5 (Z_to_bv 64 i) = M4 (Z_to_bv 64 i)) (fun i => M5 (Z_to_bv 64 i) = M4 (Z_to_bv 64 i))
               (fun i => M5 (Z_to_bv 64 (S i)) = M4 (Z_to_bv 64 (S i)))); [| | | clear - Ho Q2; lia| clear - Ho Ov3; lia| | | | | | exact V4].
      - intros a n _ _ X i Hi. exact (X i Hi).
      - intros i E D. rewrite E. exact D.
      - intros a n X y Hy. exact (X y Hy).
      - exact (proj1 AO).
      - exact (proj1 AO).
      - exact (proj2 AO).
      - intros B m HB. exact (proj1 (AB5 B m HB)).
      - intros B m HB. exact (proj2 (AB5 B m HB)). }
    assert (OWC : forall x B m, In (B, m) (PM.vs_own (PNRA.vs_clear x)) -> In (B, m) (PM.vs_own x)) by (intros x B m; destruct x; cbn; tauto).
    assert (NB5 : PM.vstr_at RSEGS PMSPA.accA M5 (op + 344) (PNRA.vs_clear nb)) by (apply STR5; [left; reflexivity| intros B m HB; exact (INB B m (OWC nb B m HB))| exact NB4]).
    assert (TB5 : PM.vstr_at RSEGS PMSPA.accA M5 (op + 368) (PNRA.vs_clear tb)) by (apply STR5; [right; reflexivity| intros B m HB; exact (ITB B m (OWC tb B m HB))| exact TB4]).
    assert (PA5 : PNARBS.bparser_at M5 op (fb + 96) (PNARBS.st2 s)).
    { unfold PNARBS.bparser_at.
      apply (PNBOA.bparser_at_xfer RSEGS PMA.AD (pa_vp_parser PMA.AD) M M5 NT YY NS AGXl DKYl SHXl op (fb + 96) (PNARBS.st1 s) (PNARBS.st2 s));
        unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNARBS.st1, PNARBS.st2;
        cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk]; fold bb0 nb tb sb sk.
      - clear - Q2; lia.
      - clear - Ov3; lia.
      - exact PA.
      - exact YO.
      - exact NSO.
      - intros i Hi. apply (NTO op 8); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
      - intros i Hi. apply (NTO (op + 10) 6); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
      - intros i Hi. apply (NTO (op + 24) 232); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
      - intros i Hi. apply (NTO (op + 312) 8); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
      - apply (L5C.u8_at_agree RSEGS M M5 (op + 8)); [intros i Hi; apply (NTO (op + 8) 1); [clear; lia| clear; lia| clear; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact P8].
      - apply (L5C.u8_at_agree RSEGS M M5 (op + 9)); [intros i Hi; apply (NTO (op + 9) 1); [clear; lia| clear; lia| clear; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact P9].
      - right; reflexivity.
      - left; reflexivity.
      - destruct (BRB _ IQC) as (X0 & X1). cbn [fst snd] in X0, X1.
        apply (PNBOA.src_keep_x RSEGS M M5 NT NS AGXl SHXl (op + 16) (fb + 96) (fb + 96 + 16) (PNM.b_src s)); [clear - Q2; lia| clear - Ov3; lia| exact X0| clear - X1; lia| | | | | exact PSRC].
        + intros i Hi. apply (NTO (op + 256) 56); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
        + exact (proj1 AQC).
        + intros i Hi. apply NSO. clear - Hi; lia.
        + exact (proj2 AQC).
      - apply (PNBOA.v8_keep_x RSEGS M M5 NT YY NS AGXl DKYl SHXl (op + 320) (PGV8.v8_clear bb0)); [clear - Q2; lia| clear - Ov3; lia| | | | | exact PBB].
        + intros i Hi. apply (NTO (op + 320) 24); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
        + intros i Hi. apply NSO. clear - Hi; lia.
        + intros B m HB i Hi. assert (HB' : In (B, m) (PGV8.v8_own bb0)) by (destruct bb0; exact HB). unfold YY. rewrite (proj1 (ABB B m HB') i Hi). exact (fun D => D).
        + intros B m HB. assert (HB' : In (B, m) (PGV8.v8_own bb0)) by (destruct bb0; exact HB).
          destruct PBB as (_ & _ & PR). destruct bb0 as [|b8 n8 c8]; [destruct HB'|]. destruct HB' as [E|[]]. injection E as <- <-. cbn [PGV8.v8_clear] in PR. destruct PR as (_ & _ & _ & _ & Hc8 & _ & Hal8 & _).
          exact (PNBOA.agsh_gspan M M5 b8 c8 (PMFA.mod16_8 _ Hal8) ltac:(clear - Hc8; lia) (proj2 (ABB b8 c8 ltac:(left; reflexivity)))).
      - exact NB5.
      - exact TB5.
      - exact VEC5. }
    split; [rewrite (REG5 2%nat) by inl; rewrite (KS1 2%nat) by inl; exact G2|].
    split; [rewrite (REG5 8%nat) by inl; rewrite (KS1 8%nat) by inl; exact G8|].
    split; [rewrite (REG5 18%nat) by inl; exact A118|].
    split; [rewrite (REG5 19%nat) by inl; rewrite (KS1 19%nat) by inl; exact G19|].
    split. { intros k Hk'. assert (Hk2 : In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat) by (cbn in Hk'; decompose [or] Hk'; subst; try contradiction; inl).
             assert (Hk3 : In k [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat) by (cbn in Hk'; decompose [or] Hk'; subst; try contradiction; inl).
             rewrite (REG5 k Hk2), (KS1 k Hk3). exact (GCS k Hk'). }
    split; [exact SV5|]. split; [exact PA5|]. split; [exact ACC5|]. split; [exact BASE5|]. split; [exact ASTK5|]. split; [exact SZ5|].
    split; [exact (PNARBK.ri_back L ar C HI HIok _ _ _ _ _ _ _ sb (40 * 2 ^ sk) ND ISB HH5)|]. split; [exact AM5|].
    split; [exact (L5LZ.model_rt_trans model0 model model5 MRT (L5LZ.model_rt_trans model model4 model5 MRT4 MRT5))|].
    split; [exact (incl_tran INCLK5 INCLK)|]. split; [exact (incl_tran INCAw INCAw5)|].
    split.
    - apply (L5SAR.ek_trans L ar LBX FF sp 14336 (PNARBS.W fb) M0 M M5 EK0).
      intros a (Ha & Hc & Ho). apply EK05. split; [exact Ha|]. split; [rewrite BXE; apply L5SAR.aclient_appb; exact Hc|].
      intros rg Hin Hr. unfold Wx in Hin. apply in_app_or in Hin as [Hin|[<-|[]]].
      + destruct (WC rg Hin) as (Hpos & [(Y1 & Y2)|(B & m & HB & Y1 & Y2)]); unfold L5.in_rng in Hr.
        * destruct (Z_lt_le_dec a (op + 368)) as [X|X].
          -- apply (Ho (op + 344, 24)); [unfold PNARBS.W, PNARBS.op; fold op; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Hr Y1 Y2 X; lia].
          -- apply (Ho (op + 368, 24)); [unfold PNARBS.W, PNARBS.op; fold op; right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Hr Y1 Y2 X; lia].
        * assert (HBo : In (B, m) OWN) by (apply in_app_or in HB as [HB|HB]; [exact (PNBOA.PNM_own_nb s B m HB)| exact (PNBOA.PNM_own_tb s B m HB)]).
          exact (PMARS1.own_not_aclient L ar C HI HIok OWN LBX FF LK cr Aw M (vml_of model) B m a sp 14336 HH HBo ltac:(clear - Hr Y1 Y2; lia) Hc).
      + apply (Ho (op + 392, 24)); [unfold PNARBS.W, PNARBS.op; fold op; do 4 right; left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; clear - Hr; lia].
    - apply (L5SAR.dk_trans L ar LBX FF sp 14336 M0 M M5 DK0).
      intros a Ha Hc D. apply DK05; [exact Ha| rewrite BXE; apply L5SAR.aclient_appb; exact Hc| exact D]. }
  (* [comment removed for export] *)
  assert (SHORTF : forall o n, (o = op + 344 \/ o = op + 368) -> PM.vstr_at RSEGS PMSPA.accA M o (PM.VShort n) ->
            L5.u8_at RSEGS MV o (2 * n) /\ 0 <= 2 * n <= 255 /\ Z.testbit (2 * n) 0 = false /\ L5.writable RSEGS MV o 2).
  { intros o n Ho (D & Cc & Hn & U). split; [|split; [clear - Hn; lia| split]].
    - apply (proj2 (L5A.u8_at_vis H M o _ (OVs o 1 ltac:(clear - Ho; lia) ltac:(clear - Ho; lia)) ltac:(clear - Ho Q2; lia) ltac:(clear - Ho Ov3; lia))). exact U.
    - rewrite Z.bit0_odd. rewrite Z.odd_mul. reflexivity.
    - apply OWs; clear - Ho; lia. }
  assert (LONGF : forall o c n p, (o = op + 344 \/ o = op + 368) -> PM.vstr_at RSEGS PMSPA.accA M o (PM.VLong c n p) -> In (p, c) (OWN ++ LBX) ->
            L5.u8_at RSEGS MV o ((c + 1) mod 256) /\ 0 <= (c + 1) mod 256 <= 255 /\ Z.testbit ((c + 1) mod 256) 0 = true
            /\ L5.u64_at RSEGS MV o (c + 1) /\ L5.u64_at RSEGS MV (o + 16) p /\ 4096 <= p <= 140737488355320 /\ PNARBP.aligned p 8
            /\ (2147446784 + 17592186048512 <= p \/ p + 1 <= 2147446784) /\ L5KA.zeros_at MV (p / 8 + 2147450880) 1 /\ L5.writable RSEGS MV p 1
            /\ ((sp - 64) + 64 <= p \/ p + 1 <= sp - 64) /\ (p + 1 <= op \/ op + 416 <= p) /\ (65536 + 6840320 <= p \/ p + 1 <= 65536)
            /\ L5.writable RSEGS MV (o + 8) 8 /\ 26 <= c).
  { intros o c n p Ho (D & Cc & W0 & W8 & W16 & Hn & Hc & Hev & DBp & CBp) Ip.
    pose proof (WB _ Ip) as ((Y0 & Y1 & Y2 & Y3 & Y4 & Y5) & _ & _ & _ & _ & _ & YFS). cbn [fst snd] in *.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Y1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y5.
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(clear; lia)) as HVB.
    split. { apply (proj2 (L5A.u8_at_vis H M o _ (OVs o 1 ltac:(clear - Ho; lia) ltac:(clear - Ho; lia)) ltac:(clear - Ho Q2; lia) ltac:(clear - Ho Ov3; lia))).
             exact (PMF.u8_of_u64 RSEGS M o (c + 1) ltac:(clear - Hc; lia) W0). }
    split; [clear - HVB; lia|]. split; [exact (PMF.odd_byte c Hev ltac:(clear - Hc; lia))|].
    split. { apply (proj2 (L5A.u64_at_vis H M o _ (OVs o 8 ltac:(clear - Ho; lia) ltac:(clear - Ho; lia)) ltac:(clear - Ho Q2; lia) ltac:(clear - Ho Ov3; lia))). exact W0. }
    split. { apply (proj2 (L5A.u64_at_vis H M (o + 16) _ (OVs (o + 16) 8 ltac:(clear - Ho; lia) ltac:(clear - Ho; lia)) ltac:(clear - Ho Q2; lia) ltac:(clear - Ho Ov3; lia))). exact W16. }
    split; [clear - Y0 Y5 Hc; lia|]. split; [unfold PNARBP.aligned; apply PMKA.mod16_8'; exact Y2|]. split; [clear - Y5 Hc; lia|].
    split. { pose proof (PMKA.blk_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model p c p 8 HH Ip ltac:(clear; lia) ltac:(clear - Hc; lia) (PMKA.mod16_8' p Y2) ltac:(clear; lia) ltac:(reflexivity)) as ZP.
             change (8 / 8) with 1 in ZP. apply ZP. intros a Ha. apply CBp. clear - Ha Hc. lia. }
    split. { apply (proj2 (L5A.writable_vis H M p 1 (VBLK p c p 1 Ip ltac:(clear; lia) ltac:(clear - Hc; lia)) ltac:(clear - Y0; lia) ltac:(clear - Y5 Hc; lia))).
             apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M p c); [exact DBp| clear; lia| clear - Hc; lia]| clear - Y0; lia| clear - Y5 Hc; lia]. }
    split; [right; clear - Y4 SLO Hc; lia|]. split; [unfold op; clear - YFS F1 F2 Hc; lia|]. split; [clear - Y1 Hc; lia|].
    split; [apply OWs; clear - Ho; lia| clear - Hc; lia]. }
  assert (WBk : forall B m, In (B, m) (PM.vs_own nb ++ PM.vs_own tb) -> In (B, m) (OWN ++ LBX)).
  { intros B m HB. apply in_or_app; left. apply in_app_or in HB as [HB|HB]; [exact (PNBOA.PNM_own_nb s B m HB)| exact (PNBOA.PNM_own_tb s B m HB)]. }
  assert (NSTRB : forall cn nn pn ct nt pt, nb = PM.VLong cn nn pn -> tb = PM.VLong ct nt pt -> pn <> pt).
  { intros cn nn pn ct nt pt E1 E2 E. assert (NDo : NoDup (map fst OWN)) by (rewrite map_app in ND; apply stdpp.list_relations.list.NoDup_app in ND; exact (proj1 ND)).
    change OWN with ([(PM.sr_qc (PNM.b_src s), PM.CHUNK)] ++ (sb, 40 * 2 ^ sk) :: (PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own nb ++ PM.vs_own tb)) in NDo.
    rewrite E1, E2 in NDo. cbn [PM.vs_own app map fst] in NDo. rewrite map_app in NDo. cbn [map fst] in NDo.
    apply stdpp.list_relations.list.NoDup_cons in NDo as (_ & NDo). apply stdpp.list_relations.list.NoDup_cons in NDo as (_ & NDo).
    apply stdpp.list_relations.list.NoDup_app in NDo as (_ & _ & NDo). apply stdpp.list_relations.list.NoDup_cons in NDo as (N1 & _).
    apply N1. rewrite E. left. }
  assert (U46 : L5.u64_at RSEGS MV (op + 392) sb).
  { apply (proj2 (L5A.u64_at_vis H M (op + 392) _ (OVs (op + 392) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))). exact V0. }
  assert (U47 : L5.u64_at RSEGS MV (op + 400) (sb + 40 * len)).
  { apply (proj2 (L5A.u64_at_vis H M (op + 400) _ (OVs (op + 400) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))). replace (op + 400) with (op + 392 + 8) by (clear; lia). exact V8. }
  assert (R46 : 0 <= sb < 2 ^ 64) by (clear - Sb0 Sb47 P2k; lia).
  assert (R47 : 0 <= sb + 40 * len < 2 ^ 64) by (unfold len in *; clear - Sb0 Sb47 P2k Hlen; lia).
  subst inW wcell. clearbody nb tb.
  destruct nb as [nn|cn nn pn]; destruct tb as [nt|ct nt pt].
  - (* [comment removed for export] *)
    destruct (SHORTF (op + 344) nn ltac:(left; reflexivity) PNB) as (NA & NR & NB0 & NWr).
    destruct (SHORTF (op + 368) nt ltac:(right; reflexivity) PTB) as (TA & TR & TB0 & TWr).
    assert (X33 : 0 <= 2 * nn < 2 ^ 64) by (clear - NR; lia). assert (X43 : 0 <= 2 * nt < 2 ^ 64) by (clear - TR; lia).
    LeanFeed.pfeed P (PNARBP.abrsSS_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => 2 * nn | 40%nat => op | 43%nat => 2 * nt | 46%nat => sb | 47%nat => sb + 40 * len | _ => 0 end)) ltac:(first [assumption | unfold PNARBP.aligned; assumption]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A11 & A110 & A111 & A112 & A113 & A118 & C368 & C369 & C344 & C345).
    apply (TAIL fx1 R1 M1v [(op + 344, 2); (op + 368, 2)] MG1); [| exact MS1| | exact A11| exact A110| exact A118| | exact C344| exact C368].
    + intros a Ha NW. apply FRZ1; [exact Ha| |]; intros X; apply NW.
      * exists (op + 344, 2). split; [left; reflexivity| exact X].
      * exists (op + 368, 2). split; [right; left; reflexivity| exact X].
    + intros x Hx. apply KS1. cbn in Hx. decompose [or] Hx; subst; try contradiction; inl.
    + intros rg [<-|[<-|[]]]; cbn [fst snd]; (split; [clear; lia| left; clear; lia]).
  - (* [comment removed for export] *)
    destruct (SHORTF (op + 344) nn ltac:(left; reflexivity) PNB) as (NA & NR & NB0 & NWr).
    assert (Ipt : In (pt, ct) (OWN ++ LBX)) by (apply WBk; apply in_or_app; right; left; reflexivity).
    destruct (LONGF (op + 368) ct nt pt ltac:(right; reflexivity) PTB Ipt) as (TA & TR & TB0 & TW0 & TW16 & TP & TAl & TNS & TZ & TWr & TSK & TOB & TIM & TWr8 & Tc).
    replace (op + 368 + 16) with (op + 384) in TW16 by (clear; lia). replace (op + 368 + 8) with (op + 376) in TWr8 by (clear; lia).
    assert (X33 : 0 <= 2 * nn < 2 ^ 64) by (clear - NR; lia). assert (X43 : 0 <= (ct + 1) mod 256 < 2 ^ 64) by (clear - TR; lia). assert (X45 : 0 <= pt < 2 ^ 64) by (clear - TP; lia).
    LeanFeed.pfeed P (PNARBP.abrsSL_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => 2 * nn | 40%nat => op | 43%nat => (ct + 1) mod 256 | 45%nat => pt | 46%nat => sb | 47%nat => sb + 40 * len | _ => 0 end)) ltac:(first [assumption | unfold PNARBP.aligned; assumption]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A11 & A110 & A111 & A112 & A113 & A118 & C376 & Cpt & C344 & C345).
    apply (TAIL fx1 R1 M1v [(op + 344, 2); (pt, 1); (op + 376, 8)] MG1); [| exact MS1| | exact A11| exact A110| exact A118| | exact C344| ].
    + intros a Ha NW. apply FRZ1; [exact Ha| | |]; intros X; apply NW.
      * exists (op + 344, 2). split; [left; reflexivity| exact X].
      * exists (pt, 1). split; [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
      * exists (op + 376, 8). split; [right; right; left; reflexivity| exact X].
    + intros x Hx. apply KS1. cbn in Hx. decompose [or] Hx; subst; try contradiction; inl.
    + intros rg [<-|[<-|[<-|[]]]]; cbn [fst snd]; (split; [clear; lia|]); [left; clear; lia| | left; clear; lia].
      right. exists pt, ct. split; [apply in_or_app; right; left; reflexivity| clear - Tc; lia].
    + split; [|split; [exact C376|]].
      * apply (L5C.u64_at_agree RSEGS MV M1v (op + 368)); [intros i Hi; apply FRZ1; [clear - Hi Q2 Ov3; lia| clear - Hi; lia| clear - Hi TOB; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact TW0].
      * apply (L5C.u64_at_agree RSEGS MV M1v (op + 384)); [intros i Hi; apply FRZ1; [clear - Hi Q2 Ov3; lia| clear - Hi; lia| clear - Hi TOB; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact TW16].
  - (* [comment removed for export] *)
    assert (Ipn : In (pn, cn) (OWN ++ LBX)) by (apply WBk; apply in_or_app; left; left; reflexivity).
    destruct (LONGF (op + 344) cn nn pn ltac:(left; reflexivity) PNB Ipn) as (NA & NR & NB0 & NW0 & NW16 & NP & NAl & NNS & NZ & NWr & NSK & NOB & NIM & NWr8 & Nc).
    replace (op + 344 + 16) with (op + 360) in NW16 by (clear; lia). replace (op + 344 + 8) with (op + 352) in NWr8 by (clear; lia).
    destruct (SHORTF (op + 368) nt ltac:(right; reflexivity) PTB) as (TA & TR & TB0 & TWr).
    assert (X33 : 0 <= (cn + 1) mod 256 < 2 ^ 64) by (clear - NR; lia). assert (X43 : 0 <= 2 * nt < 2 ^ 64) by (clear - TR; lia). assert (X37 : 0 <= pn < 2 ^ 64) by (clear - NP; lia).
    LeanFeed.pfeed P (PNARBP.abrsLS_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => (cn + 1) mod 256 | 37%nat => pn | 40%nat => op | 43%nat => 2 * nt | 46%nat => sb | 47%nat => sb + 40 * len | _ => 0 end)) ltac:(first [assumption | unfold PNARBP.aligned; assumption]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A11 & A110 & A111 & A112 & A113 & A118 & C368 & C369 & C352 & Cpn).
    apply (TAIL fx1 R1 M1v [(pn, 1); (op + 352, 8); (op + 368, 2)] MG1); [| exact MS1| | exact A11| exact A110| exact A118| | | exact C368].
    + intros a Ha NW. apply FRZ1; [exact Ha| | |]; intros X; apply NW.
      * exists (pn, 1). split; [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
      * exists (op + 352, 8). split; [right; left; reflexivity| exact X].
      * exists (op + 368, 2). split; [right; right; left; reflexivity| exact X].
    + intros x Hx. apply KS1. cbn in Hx. decompose [or] Hx; subst; try contradiction; inl.
    + intros rg [<-|[<-|[<-|[]]]]; cbn [fst snd]; (split; [clear; lia|]); [| left; clear; lia| left; clear; lia].
      right. exists pn, cn. split; [apply in_or_app; left; left; reflexivity| clear - Nc; lia].
    + split; [|split; [exact C352|]].
      * apply (L5C.u64_at_agree RSEGS MV M1v (op + 344)); [intros i Hi; apply FRZ1; [clear - Hi Q2 Ov3; lia| clear - Hi NOB; lia| clear - Hi; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact NW0].
      * apply (L5C.u64_at_agree RSEGS MV M1v (op + 360)); [intros i Hi; apply FRZ1; [clear - Hi Q2 Ov3; lia| clear - Hi NOB; lia| clear - Hi; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact NW16].
  - (* [comment removed for export] *)
    assert (Ipn : In (pn, cn) (OWN ++ LBX)) by (apply WBk; apply in_or_app; left; left; reflexivity).
    assert (Ipt : In (pt, ct) (OWN ++ LBX)) by (apply WBk; apply in_or_app; right; left; reflexivity).
    destruct (LONGF (op + 344) cn nn pn ltac:(left; reflexivity) PNB Ipn) as (NA & NR & NB0 & NW0 & NW16 & NP & NAl & NNS & NZ & NWr & NSK & NOB & NIM & NWr8 & Nc).
    replace (op + 344 + 16) with (op + 360) in NW16 by (clear; lia). replace (op + 344 + 8) with (op + 352) in NWr8 by (clear; lia).
    destruct (LONGF (op + 368) ct nt pt ltac:(right; reflexivity) PTB Ipt) as (TA & TR & TB0 & TW0 & TW16 & TP & TAl & TNS & TZ & TWr & TSK & TOB & TIM & TWr8 & Tc).
    replace (op + 368 + 16) with (op + 384) in TW16 by (clear; lia). replace (op + 368 + 8) with (op + 376) in TWr8 by (clear; lia).
    pose proof (NSTRB cn nn pn ct nt pt eq_refl eq_refl) as NEP.
    assert (PAP : pn + 1 <= pt \/ pt + 1 <= pn) by (clear - NEP; lia).
    assert (X33 : 0 <= (cn + 1) mod 256 < 2 ^ 64) by (clear - NR; lia). assert (X43 : 0 <= (ct + 1) mod 256 < 2 ^ 64) by (clear - TR; lia).
    assert (X37 : 0 <= pn < 2 ^ 64) by (clear - NP; lia). assert (X45 : 0 <= pt < 2 ^ 64) by (clear - TP; lia).
    LeanFeed.pfeed P (PNARBP.abrsLL_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => (cn + 1) mod 256 | 37%nat => pn | 40%nat => op | 43%nat => (ct + 1) mod 256 | 45%nat => pt
                                                          | 46%nat => sb | 47%nat => sb + 40 * len | _ => 0 end)) ltac:(first [assumption | unfold PNARBP.aligned; assumption]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A11 & A110 & A111 & A112 & A118 & C376 & Cpt & C352 & Cpn).
    apply (TAIL fx1 R1 M1v [(pn, 1); (op + 352, 8); (pt, 1); (op + 376, 8)] MG1); [| exact MS1| | exact A11| exact A110| exact A118| | | ].
    + intros a Ha NW. apply FRZ1; [exact Ha| | | |]; intros X; apply NW.
      * exists (pn, 1). split; [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
      * exists (op + 352, 8). split; [right; left; reflexivity| exact X].
      * exists (pt, 1). split; [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
      * exists (op + 376, 8). split; [do 3 right; left; reflexivity| exact X].
    + intros x Hx. apply KS1. cbn in Hx. decompose [or] Hx; subst; try contradiction; inl.
    + intros rg [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; (split; [clear; lia|]); [| left; clear; lia| | left; clear; lia].
      * right. exists pn, cn. split; [apply in_or_app; left; left; reflexivity| clear - Nc; lia].
      * right. exists pt, ct. split; [apply in_or_app; right; left; reflexivity| clear - Tc; lia].
    + split; [|split; [exact C352|]].
      * apply (L5C.u64_at_agree RSEGS MV M1v (op + 344)); [intros i Hi; apply FRZ1; [clear - Hi Q2 Ov3; lia| clear - Hi NOB; lia| clear - Hi; lia| clear - Hi TOB; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact NW0].
      * apply (L5C.u64_at_agree RSEGS MV M1v (op + 360)); [intros i Hi; apply FRZ1; [clear - Hi Q2 Ov3; lia| clear - Hi NOB; lia| clear - Hi; lia| clear - Hi TOB; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact NW16].
    + split; [|split; [exact C376|]].
      * apply (L5C.u64_at_agree RSEGS MV M1v (op + 368)); [intros i Hi; apply FRZ1; [clear - Hi Q2 Ov3; lia| clear - Hi NOB; lia| clear - Hi; lia| clear - Hi TOB; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact TW0].
      * apply (L5C.u64_at_agree RSEGS MV M1v (op + 384)); [intros i Hi; apply FRZ1; [clear - Hi Q2 Ov3; lia| clear - Hi NOB; lia| clear - Hi; lia| clear - Hi TOB; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact TW16].
Qed.
End Stage.
End PNARB2.
