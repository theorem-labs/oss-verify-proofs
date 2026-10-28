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
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAIss1_b PnAEmbKit_b PnBrObjA_b PnAResetBStmts_b PnAResetBGlue_b PnAResetBP_b PnAResetBKit_b PnAVu8Dtor_b PnAHarnessKit3_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNARB1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition bbb (x : PGV8.v8) : Z := match x with PGV8.V8Null => 0 | PGV8.V8Blk b _ _ => b end.
Definition bbe (x : PGV8.v8) : Z := match x with PGV8.V8Null => 0 | PGV8.V8Blk b n _ => b + n end.
Lemma zsub (M : word -> option byte) a n a' n' : L5KA.zeros_at M a n -> a <= a' -> a' + n' <= a + n -> L5KA.zeros_at M a' n'.
Proof. intros Z H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply Z. lia. Qed.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Theorem head : PNARBG.head_stmt L ar HI.
Proof.
  unfold PNARBG.head_stmt. intros ASH fx R M model K LBX FF LK Aw cr sp r fb s PRE KONT.
  destruct PRE as (HH & AM & K0 & ENT & FRM & FRS & FOK & A10 & PA & ACC & BASE).
  unfold PNARBS.op in *. set (op := fb + 464) in *.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 1) with 14336 in *. change (14336 / 8) with 1792 in STKSH.
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
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
  (* [comment removed for export] *)
  pose proof PA as (P0 & PD & PC0 & P8 & P9 & P10 & P12 & PNI & PSRC & P312 & PC312 & PBB & PNB & PTB & PSTK & PM01 & PD01).
  unfold PNM.OFF_BB in PBB.
  assert (BBW : L5.u64_at RSEGS M (op + 320) (bbb (PNM.b_bb s)) /\ L5.u64_at RSEGS M (op + 328) (bbe (PNM.b_bb s))
                /\ 0 <= bbb (PNM.b_bb s) < 2 ^ 64 /\ 0 <= bbe (PNM.b_bb s) < 2 ^ 64).
  { destruct PBB as (_ & _ & X). replace (op + 328) with (op + 320 + 8) by lia. destruct (PNM.b_bb s) as [|b n c] eqn:EBB; cbn [bbb bbe].
    - destruct X as (X0 & X8 & _). split; [exact X0|]. split; [exact X8|]. clear; lia.
    - destruct X as (X0 & X8 & X16 & NC & C27 & B4096 & _). split; [exact X0|]. split; [exact X8|].
      assert (Ib : In (b, c) (PNM.bparser_own s ++ LBX)).
      { apply in_or_app; left. unfold PNM.bparser_own, PNM.brest_own. rewrite EBB. cbn [PGV8.v8_own].
        apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. left; reflexivity. }
      pose proof (WB _ Ib) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _). cbn [fst snd] in Bb0, Bb5. unfold app_mem in Bb5. destruct Bb5 as (_ & _ & X47).
      clear - NC C27 B4096 Bb0 X47; lia. }
  destruct BBW as (BB0 & BB8 & BBr0 & BBr8).
  (* [comment removed for export] *)
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
  assert (BB0v : L5.u64_at RSEGS MV (op + 320) (bbb (PNM.b_bb s))) by (apply (proj2 (L5A.u64_at_vis H M (op + 320) _ (OVs (op + 320) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(lia) ltac:(lia))); exact BB0).
  assert (BB8v : L5.u64_at RSEGS MV (op + 328) (bbe (PNM.b_bb s))) by (apply (proj2 (L5A.u64_at_vis H M (op + 328) _ (OVs (op + 328) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(lia) ltac:(lia))); exact BB8).
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
  assert (Q13 : L5.writable RSEGS MV (op + 8) 2) by (apply OWs; lia).
  assert (Q14 : L5.writable RSEGS MV (op + 328) 8) by (apply OWs; lia).
  LeanFeed.pfeed P (PNARBP.abrsA_conc fx R MV (fun j => match j with 2%nat => sp | 40%nat => op | 34%nat => bbb (PNM.b_bb s) | 36%nat => bbe (PNM.b_bb s) | _ => 0 end)) ltac:(first [assumption | unfold PNARBP.aligned; assumption]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & aR1 & aR2 & aR8 & aR10 & aR11 & aR19 & C9 & C8 & S48 & S40 & S32 & S24 & S16 & S8 & C328).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xadb68 R1 0xabb00 M1v
           (fun a => (sp - 48 <= a < sp - 48 + 48) \/ (op + 8 <= a < op + 8 + 2) \/ (op + 328 <= a < op + 328 + 8)) K HH AM MS1 MG1).
  { intros a Ha Hnw. apply FRZ1; [exact Ha| intros X; apply Hnw; left; exact X| intros X; apply Hnw; right; left; exact X| intros X; apply Hnw; right; right; exact X]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|[X|X]].
      + unfold aclientw, aclient_g. right; left. split; [lia| intros Y; lia].
      + apply (L5SAR.obj_client L ar _ FF 0 0 op 416 a AOB); lia.
      + apply (L5SAR.obj_client L ar _ FF 0 0 op 416 a AOB); lia.
    - destruct Wa as [X|[X|X]]; lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  set (P1 := fun a => (sp - 48 <= a < sp - 48 + 48) \/ (op + 8 <= a < op + 8 + 2) \/ (op + 328 <= a < op + 328 + 8)) in FR1.
  assert (OPN : PNAV8D.nsh op 416) by (unfold PNAV8D.nsh; clear - OBIG; lia).
  assert (P1sh : forall x, BIGSHADOW_LO <= x < BIGSHADOW_HI -> ~ P1 x).
  { intros x Hx [Y|[Y|Y]]; [clear - Hx Y SLO SPT SHI; unfold BIGSHADOW_LO, BIGSHADOW_HI in Hx; lia| exact (PNAV8D.nsh_not op 416 x OPN ltac:(clear - Y; lia) Hx)| exact (PNAV8D.nsh_not op 416 x OPN ltac:(clear - Y; lia) Hx)]. }
  assert (SHM1 : forall a m, 0 <= a -> a + m <= 2 ^ 47 -> PMFA.agsh M M1 a m).
  { intros a m Ha Hn x Hx. pose proof (PMKA.S_in_shadow x ltac:(clear - Ha Hn Hx; lia)) as SX. apply FR1; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia| apply P1sh; exact SX]. }
  assert (SP16 : forall j, (sp - 16 * j) mod 8 = 0) by (intros j; apply PMKA.mod16_8'; replace (sp - 16 * j) with (sp + (- j) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
  assert (ASTK1 : L5CA.astk ar M1 sp 14336) by exact (L5SAR.astk_grows ar M M1 sp 14336 ASTK MGM1).
  assert (ASTK1c : L5CA.astk ar M1 (sp - 64) 12288).
  { apply (L5SAR.astk_sub ar M M1 sp 14336 64 12288 ASTK MGM1); [clear; lia|clear; lia|clear; lia|]. replace (sp - 64) with (sp + (-4) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
  assert (SZk : forall lo g, lo mod 8 = 0 -> 0 <= lo -> lo + 8 * g <= 2 ^ 47 -> 0 <= g -> shadow_zero M lo g -> shadow_zero M1 lo g).
  { intros lo g Hlo H0 H1 Hg SZ j Hj. pose proof (SZ j Hj) as Z1. unfold byte_at in *. rewrite (PMFA.S_granule lo j Hlo ltac:(clear - Hj; lia)) in *.
    pose proof (PMKA.S_in_shadow (lo + 8 * j) ltac:(clear - H0 H1 Hj; lia)) as SX. rewrite FR1; [exact Z1| unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia| apply P1sh; exact SX]. }
  assert (SZ1 : shadow_zero M1 (sp - 14336) 1792).
  { apply SZk; [replace (sp - 14336) with (sp - 16 * 896) by (clear; lia); apply SP16| clear - SLO SPT SHI; lia| clear - SLO SPT SHI; lia| clear; lia| exact STKSH]. }
  assert (SZ1c : shadow_zero M1 (sp - 64 - 12288) 1536).
  { apply (PMKA.shadow_zero_sub M1 (sp - 14336) 1792); [replace (sp - 14336) with (sp - 16 * 896) by (clear; lia); apply SP16| replace (sp - 64 - 12288) with (sp - 16 * 772) by (clear; lia); apply SP16| clear; lia| clear; lia| clear; lia| exact SZ1]. }
  assert (C328m : L5.u64_at RSEGS M1 (op + 328) (bbe (PNM.b_bb s))).
  { apply (proj1 (L5A.u64_at_vis H M1 (op + 328) _ (OVs (op + 328) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))). rewrite VIS1. exact C328. }
  assert (C8m : L5.u8_at RSEGS M1 (op + 8) 1).
  { apply (proj1 (L5A.u8_at_vis H M1 (op + 8) _ (OVs (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))). rewrite VIS1. exact C8. }
  assert (C9m : L5.u8_at RSEGS M1 (op + 9) 0).
  { apply (proj1 (L5A.u8_at_vis H M1 (op + 9) _ (OVs (op + 9) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))). rewrite VIS1. exact C9. }
  assert (SV1 : PNARBS.saves R sp M1).
  { unfold PNARBS.saves. split; [|split; [|split; [|split; [|split]]]].
    - apply (proj1 (L5A.u64_at_vis H M1 (sp - 8) _ (VIS (sp - 8) 8 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SLO SPT SHI; lia) ltac:(clear - SHI SPT; lia))). rewrite VIS1. exact S8.
    - apply (proj1 (L5A.u64_at_vis H M1 (sp - 16) _ (VIS (sp - 16) 8 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SLO SPT SHI; lia) ltac:(clear - SHI SPT; lia))). rewrite VIS1. exact S16.
    - apply (proj1 (L5A.u64_at_vis H M1 (sp - 24) _ (VIS (sp - 24) 8 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SLO SPT SHI; lia) ltac:(clear - SHI SPT; lia))). rewrite VIS1. exact S24.
    - apply (proj1 (L5A.u64_at_vis H M1 (sp - 32) _ (VIS (sp - 32) 8 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SLO SPT SHI; lia) ltac:(clear - SHI SPT; lia))). rewrite VIS1. exact S32.
    - apply (proj1 (L5A.u64_at_vis H M1 (sp - 40) _ (VIS (sp - 40) 8 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SLO SPT SHI; lia) ltac:(clear - SHI SPT; lia))). rewrite VIS1. exact S40.
    - apply (proj1 (L5A.u64_at_vis H M1 (sp - 48) _ (VIS (sp - 48) 8 ltac:(clear - SLO; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SLO SPT SHI; lia) ltac:(clear - SHI SPT; lia))). rewrite VIS1. exact S48. }
  assert (AG1 : forall a n, (forall i, a <= i < a + n -> ~ P1 i) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n).
  { intros a n NP Ha Hn i Hi. apply FR1; [clear - Ha Hn Hi; lia| apply NP; exact Hi]. }
  set (bb := PNM.b_bb s) in *.
  set (OWN := PNM.bparser_own s) in *.
  set (x' := PGV8.v8_clear bb).
  set (BXc := match bb with PGV8.V8Null => OWN | PGV8.V8Blk b _ _ => lb_remove b OWN end).
  assert (OWNc : forall B m, In (B, m) OWN -> In (B, m) (PGV8.v8_own bb) \/ In (B, m) BXc).
  { intros B m Hin. unfold BXc. destruct bb as [|b n c] eqn:EBB; [right; exact Hin|].
    assert (Ib : In (b, c) OWN) by (apply PNBOA.PNM_own_bb; fold bb; rewrite EBB; left; reflexivity).
    assert (NDo : NoDup (map fst OWN)) by (rewrite map_app in ND; apply stdpp.list_relations.list.NoDup_app in ND; exact (proj1 ND)).
    destruct (proj1 (PNAV8D.lbr_iff b c OWN NDo Ib (B, m)) Hin) as [X|X]; [left; left; exact X| right; exact X]. }
  assert (HHs : ri_inv HI (PGV8.v8_own bb ++ (BXc ++ LBX)) FF LK cr Aw M1 (vml_of model1)
                /\ (forall LK' Aw' M' V', ri_inv HI (PGV8.v8_own bb ++ (BXc ++ LBX)) FF LK' cr Aw' M' V' -> ri_inv HI (OWN ++ LBX) FF LK' cr Aw' M' V')).
  { unfold BXc. destruct bb as [|b n c] eqn:EBB; cbn [PGV8.v8_own app].
    - split; [exact HH1| intros LK' Aw' M' V' X; exact X].
    - assert (Ib : In (b, c) OWN) by (apply PNBOA.PNM_own_bb; fold bb; rewrite EBB; left; reflexivity).
      assert (Ib' : In (b, c) (OWN ++ LBX)) by (apply in_or_app; left; exact Ib).
      rewrite <- (PNARBK.lbr_app_l b OWN LBX (in_map fst OWN (b, c) Ib)).
      split; [exact (PNAV8D.ri_front L ar C HI HIok _ _ _ _ _ _ _ b c HH1 Ib')|].
      intros LK' Aw' M' V' X. exact (PNARBK.ri_back L ar C HI HIok _ _ _ _ _ _ _ b c ND Ib' X). }
  destruct HHs as (HHs & BACK).
  assert (AOV : PMSPA.aobjA FF (op + 320) 24) by (apply (PNAV8D.aobjA_sub FF op 416); [exact AOP| clear; lia| clear; lia]).
  assert (V8m : (op + 320) mod 8 = 0) by (replace (op + 320) with (op + 40 * 8) by (clear; lia); rewrite Z.mod_add by (clear; lia); exact O8).
  pose proof PBB as (VD & VC & VR).
  assert (VAT1 : PGV8.v8_at RSEGS PMSPA.accA PMSPA.annA M1 (op + 320) bb).
  { unfold PGV8.v8_at. split; [intros i Hi; apply MGM1; apply VD; exact Hi|].
    split; [apply (PMFA.accA_agree M M1); [apply SHM1; clear - Q2 Ov3; lia| exact VC]|].
    destruct bb as [|b n c] eqn:EBB; cbn [bbb bbe] in *.
    - destruct VR as (W0 & W8 & W16).
      split; [apply (L5C.u64_at_agree RSEGS M M1 (op + 320)); [apply AG1; [intros i Hi [Y|[Y|Y]]; clear - Hi Y OPS; lia| clear - Q2; lia| clear - Ov3; lia]| clear - Q2; lia| clear - Ov3; lia| exact W0]|].
      split; [replace (op + 320 + 8) with (op + 328) by (clear; lia); exact C328m|].
      apply (L5C.u64_at_agree RSEGS M M1 (op + 320 + 16)); [apply AG1; [intros i Hi [Y|[Y|Y]]; clear - Hi Y OPS; lia| clear - Q2; lia| clear - Ov3; lia]| clear - Q2; lia| clear - Ov3; lia| exact W16].
    - destruct VR as (W0 & W8 & W16 & Hn & Hc & Hb & Hal & DB & CB & AB).
      split; [apply (L5C.u64_at_agree RSEGS M M1 (op + 320)); [apply AG1; [intros i Hi [Y|[Y|Y]]; clear - Hi Y OPS; lia| clear - Q2; lia| clear - Ov3; lia]| clear - Q2; lia| clear - Ov3; lia| exact W0]|].
      split; [replace (op + 320 + 8) with (op + 328) by (clear; lia); exact C328m|].
      split; [apply (L5C.u64_at_agree RSEGS M M1 (op + 320 + 16)); [apply AG1; [intros i Hi [Y|[Y|Y]]; clear - Hi Y OPS; lia| clear - Q2; lia| clear - Ov3; lia]| clear - Q2; lia| clear - Ov3; lia| exact W16]|].
      split; [exact Hn|]. split; [exact Hc|]. split; [exact Hb|]. split; [exact Hal|].
      split; [intros i Hi; apply MGM1; apply DB; exact Hi|].
      assert (Ib : In (b, c) (OWN ++ LBX)) by (apply in_or_app; left; apply PNBOA.PNM_own_bb; fold bb; rewrite EBB; left; reflexivity).
      pose proof (WB _ Ib) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _). cbn [fst snd] in Bb0, Bb5. unfold app_mem in Bb5. destruct Bb5 as (_ & _ & Bb47).
      split.
      + apply (PMFA.accA_agree M M1); [apply SHM1; clear - Bb0 Bb47 Hn Hc Hb; lia| exact CB].
      + apply (PNAEK.ann_agree M M1 b n c); [| clear - Hn; lia| clear - Hn Hc; lia| exact AB]. intros j Hj. rewrite (PNAEK.S_add8 b j).
        apply (SHM1 b (8 * ((c + 7) / 8))); [clear - Hb; lia| | ].
        * clear - Bb0 Bb47 Hal Hc. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
        * clear - Hj Hc. Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  unfold PnSpecsAXC_b.PNSAXC.clear_v8_spec in ASH.
  apply (ASH fx1 R1 M1 model1 K (BXc ++ LBX) FF LK Aw cr (op + 320) bb (sp - 64) 711632 HHs AM1 K0).
  { split; [rewrite L5K.rl1; exact aR1|]. split; [split; [clear; lia| reflexivity]|].
    split; [rewrite L5K.rl2; exact aR2|].
    split; [rewrite L5K.rl3, (KS1 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK1c|]. change (12288 / 8) with 1536. exact SZ1c. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS. lia. }
  { rewrite L5K.rl10. exact aR10. }
  { exact AOV. }
  { exact V8m. }
  { apply (PMFA.accA_agree M M1); [apply SHM1; clear - Q2 Ov3; lia| exact VC]. }
  { exact VAT1. }
  intros fx3 R3 M3 model3 LK3 Aw3 RP3 VEC3 BLK3 HP3 MRT3 INCLK3 INCAw3 AM3 HH3.
  change (PMSPA.pm_scr 0) with 12288 in HP3. replace (op + 320 + 8) with (op + 328) in HP3 by (clear; lia).
  apply (KONT fx3 R3 M3 model3 LK3 Aw3).
  unfold PNARBS.smid1, PNARBS.smid. fold op.
  set (LBc := BXc ++ LBX) in *.
  set (W1 := [(op + 8, 2); (op + 328, 8)]).
  assert (WAPP1 : PMKA.wapp W1).
  { unfold W1. apply PMKA.wapp_cons; [cbn [fst snd]; unfold PNAV8D.nsh in OPN; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OPN; lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold PNAV8D.nsh in OPN; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OPN; lia| apply PMKA.wapp_nil]. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). clear - X1 X2 FSAPP. unfold app_mem, FS_BYTES in *. lia. }
  assert (EK01 : L5SAR.ek L ar LBc FF sp 14336 W1 M M1).
  { apply (L5SAR.ek_piece L ar LBc FF sp 14336 W1 M M1 P1 FR1). intros a Ha Hc Ho [X|[X|X]].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M1 _ sp 14336 a HHs SPT (L5SAR.aclient_appb L ar LBc (PGV8.v8_own bb) FF sp 14336 a Hc))
        as [(_ & Z2)|Z2]; [apply Z2; clear - X; lia| clear - X Z2 SLO; lia].
    - apply (Ho (op + 8, 2)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
    - apply (Ho (op + 328, 8)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
  assert (EK13 : L5SAR.ek L ar LBc FF sp 14336 W1 M1 M3).
  { apply (L5SAR.ek_callee L ar LBc [] FF [] sp 14336 (sp - 64) 12288 W1 [(op + 328, 8)] M1 M3 HP3); [clear; lia| clear; lia| intros a _ Ho rg [<-|[]] Hr; apply (Ho (op + 328, 8)); [right; left; reflexivity| exact Hr]]. }
  pose proof (L5SAR.ek_trans L ar LBc FF sp 14336 W1 M M1 M3 EK01 EK13) as EK03.
  assert (DK03 : L5SAR.dk L ar LBc FF sp 14336 M M3).
  { apply (L5SAR.dk_trans L ar LBc FF sp 14336 M M1 M3); [exact (L5SAR.dk_grows L ar LBc FF sp 14336 M M1 MGM1)|].
    apply (L5SAR.dk_callee L ar LBc [] FF [] sp 14336 (sp - 64) 12288 [(op + 328, 8)] M1 M3 HP3); clear; lia. }
  assert (ASTK3 : L5CA.astk ar M3 sp 14336) by (apply (PMKA.astk_after_ahpres L ar LBc FF M1 M3 sp 14336 (sp - 64) 12288 [(op + 328, 8)] ASTK1 HP3); [clear; lia| clear; lia| clear; lia| exact STOP]).
  assert (SZ3 : shadow_zero M3 (sp - 14336) 1792).
  { apply (PMKA.stksh_keepA L ar LBc FF sp 14336 W1 M1 M3 EK13 WAPP1 (sp - 14336) 1792); [clear - SLO SPT SHI; lia| clear - SLO; lia| clear - SPT SHI; lia| replace (sp - 14336) with (sp - 16 * 896) by (clear; lia); apply SP16| clear; lia| exact SZ1]. }
  assert (ACC3 : PMSPA.accA M3 op 416) by exact (PMKA.acc_keepA' L ar LBc FF sp 14336 W1 M M3 EK03 WAPP1 FRB op 416 AOP ACC).
  assert (STD : forall a, PMST.dep PMA.AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W1 a).
  { intros a D. pose proof (PMAIS1.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
    split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. intros rg [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr DI Ov1; lia. }
  assert (SRO : forall a, 65536 <= a < pa_rw_lo PMA.AD -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W1 a).
  { intros a Ha. cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - Ha; lia|].
    split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X) as Y; clear - Ha Y; lia|]. intros rg [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Ov1; lia. }
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3) by (apply (PMKA.base_ok_keepA RSEGS PMA.AD L ar LBc FF sp 14336 W1 M M3 EK03 PMA.addrs_wf_A STD SRO BASE)).
  (* [comment removed for export] *)
  assert (BXE : BXc = [(PM.sr_qc (PNM.b_src s), PM.CHUNK); (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s)] ++ PM.vs_own (PNM.b_nb s) ++ PM.vs_own (PNM.b_tb s)).
  { assert (NDo : NoDup (map fst OWN)) by (rewrite map_app in ND; apply stdpp.list_relations.list.NoDup_app in ND; exact (proj1 ND)).
    unfold BXc. unfold OWN, PNM.bparser_own, PNM.brest_own, PM.src_own, PNM.bvec_own in *. fold bb in NDo |- *.
    destruct bb as [|b n c]; cbn [PGV8.v8_own app] in *; [reflexivity|].
    apply (PNHAK3.lb_remove_at b c _ [(PM.sr_qc (PNM.b_src s), PM.CHUNK); (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s)] (PM.vs_own (PNM.b_nb s) ++ PM.vs_own (PNM.b_tb s))); [reflexivity| exact NDo]. }
  assert (INC : forall x, In x LBc -> In x (OWN ++ LBX)).
  { intros x Hx. unfold LBc in Hx. apply in_app_or in Hx as [Hx|Hx]; [|apply in_or_app; right; exact Hx]. apply in_or_app; left.
    unfold BXc in Hx. destruct bb; [exact Hx| exact (L5C.in_lb_remove _ x OWN Hx)]. }
  assert (BRB : forall b0, In b0 LBc -> 0 <= fst b0 /\ fst b0 + snd b0 <= 2 ^ 47).
  { intros b0 Hb0. destruct (proj1 (WB b0 (INC b0 Hb0))) as (X0 & _ & _ & _ & _ & X5). clear - X0 X5. unfold app_mem in X5. lia. }
  assert (BOUT : forall b0, In b0 LBc -> forall i, fst b0 <= i < fst b0 + snd b0 -> L5.outside W1 i).
  { intros b0 Hb0 i Hi. destruct (WB b0 (INC b0 Hb0)) as (_ & _ & _ & _ & _ & _ & X).
    intros rg [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold op in Hr; clear - X Hi Hr F1 F2; lia. }
  assert (BLKA : forall q m, In (q, m) LBc -> PMFA.agA M M3 q m).
  { intros q m Hin. apply (PMKA.agA_blk L ar LBc FF sp 14336 W1 M M3 EK03 WAPP1 BRB q m Hin). exact (BOUT (q, m) Hin). }
  assert (OBJA : forall a n, op <= a -> a + n <= op + 416 -> (a + n <= op + 8 \/ (op + 10 <= a /\ a + n <= op + 328) \/ op + 336 <= a) -> PMFA.agA M M3 a n).
  { intros a n X1 X2 X3. apply (PMKA.agA_obj L ar LBc FF sp 14336 W1 M M3 EK03 WAPP1 FRB a n (PNAV8D.aobjA_sub FF op 416 a n AOP X1 X2)).
    intros i Hi rg [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hi Hr X3; lia. }
  pose proof (PMKA.agsh_obj L ar LBc FF sp 14336 W1 M M3 EK03 WAPP1 FRB op 416 AOP) as OSH.
  assert (ODK : forall i, op <= i < op + 416 -> M (Z_to_bv 64 i) <> None -> M3 (Z_to_bv 64 i) <> None).
  { intros i Hi. apply DK03; [clear - Hi Q2 Ov3; lia|]. exact (L5SAR.obj_client L ar LBc FF sp 14336 op 416 i AOB Hi). }
  assert (EK13n : L5SAR.ek L ar LBc FF sp 14336 [(op + 328, 8)] M1 M3).
  { apply (L5SAR.ek_callee L ar LBc [] FF [] sp 14336 (sp - 64) 12288 [(op + 328, 8)] [(op + 328, 8)] M1 M3 HP3); [clear; lia| clear; lia| intros a _ Ho; exact Ho]. }
  assert (WAPP2 : PMKA.wapp [(op + 328, 8)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold PNAV8D.nsh in OPN; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OPN; lia| apply PMKA.wapp_nil]. }
  assert (C8k : L5.u8_at RSEGS M3 (op + 8) 1).
  { apply (PMKA.u8_keepA RSEGS L ar LBc FF sp 14336 [(op + 328, 8)] M1 M3 EK13n WAPP2 FRB (op + 8) 1 (PNAV8D.aobjA_sub FF op 416 (op + 8) 1 AOP ltac:(clear; lia) ltac:(clear; lia))); [intros ii Hii r0 [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hii Hr; lia| exact C8m]. }
  assert (C9k : L5.u8_at RSEGS M3 (op + 9) 0).
  { apply (PMKA.u8_keepA RSEGS L ar LBc FF sp 14336 [(op + 328, 8)] M1 M3 EK13n WAPP2 FRB (op + 9) 0 (PNAV8D.aobjA_sub FF op 416 (op + 9) 1 AOP ltac:(clear; lia) ltac:(clear; lia))); [intros ii Hii r0 [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hii Hr; lia| exact C9m]. }
  (* [comment removed for export] *)
  set (NT := fun i : Z => M3 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  set (YY := fun i : Z => M (Z_to_bv 64 i) <> None -> M3 (Z_to_bv 64 i) <> None).
  set (NS := fun i : Z => M3 (Z_to_bv 64 (S i)) = M (Z_to_bv 64 (S i))).
  assert (AGXl : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> NT i) -> L5C.agree_on M M3 a n) by (intros a n _ _ X i Hi; exact (X i Hi)).
  assert (DKYl : forall i, YY i -> M (Z_to_bv 64 i) <> None -> M3 (Z_to_bv 64 i) <> None) by (intros i X; exact X).
  assert (SHXl : forall a n, (forall i, a <= i < a + n -> NS i) -> PMFA.agsh M M3 a n) by (intros a n X x Hx; exact (X x Hx)).
  assert (NTO : forall a n, op <= a -> a + n <= op + 416 -> (a + n <= op + 8 \/ (op + 10 <= a /\ a + n <= op + 328) \/ op + 336 <= a) -> forall i, a <= i < a + n -> NT i).
  { intros a n X1 X2 X3 i Hi. exact (proj1 (OBJA a n X1 X2 X3) i Hi). }
  assert (NSO : forall i, op <= i < op + 416 -> NS i) by (intros i Hi; exact (OSH i Hi)).
  assert (YO : forall i, op <= i < op + 416 -> YY i) by (intros i Hi; exact (ODK i Hi)).
  assert (NTB : forall q m, In (q, m) LBc -> forall i, q <= i < q + m -> NT i) by (intros q m Hin i Hi; exact (proj1 (BLKA q m Hin) i Hi)).
  assert (NSB : forall q m, In (q, m) LBc -> forall i, q <= i < q + m -> NS i) by (intros q m Hin i Hi; exact (proj2 (BLKA q m Hin) i Hi)).
  assert (YB : forall q m, In (q, m) LBc -> forall i, q <= i < q + m -> YY i) by (intros q m Hin i Hi D; unfold NT in NTB; rewrite (NTB q m Hin i Hi); exact D).
  assert (IQC : In (PM.sr_qc (PNM.b_src s), PM.CHUNK) LBc) by (unfold LBc; rewrite BXE; apply in_or_app; left; left; reflexivity).
  assert (ISB : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) LBc) by (unfold LBc; rewrite BXE; apply in_or_app; left; right; left; reflexivity).
  assert (INB : forall B m, In (B, m) (PM.vs_own (PNM.b_nb s)) -> In (B, m) LBc).
  { intros B m Hin. unfold LBc. rewrite BXE. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hin. }
  assert (ITB : forall B m, In (B, m) (PM.vs_own (PNM.b_tb s)) -> In (B, m) LBc).
  { intros B m Hin. unfold LBc. rewrite BXE. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. exact Hin. }
  assert (PA3 : PNARBS.bparser_at M3 op (fb + 96) (PNARBS.st1 s)).
  { unfold PNARBS.bparser_at.
    apply (PNBOA.bparser_at_xfer RSEGS PMA.AD (pa_vp_parser PMA.AD) M M3 NT YY NS AGXl DKYl SHXl op (fb + 96) s (PNARBS.st1 s));
      unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNARBS.st1;
      cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
    - clear - Q2; lia.
    - clear - Ov3; lia.
    - exact PA.
    - exact YO.
    - exact NSO.
    - intros i Hi. apply (NTO op 8); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
    - intros i Hi. apply (NTO (op + 10) 6); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
    - intros i Hi. apply (NTO (op + 24) 232); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
    - intros i Hi. apply (NTO (op + 312) 8); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
    - exact C8k.
    - exact C9k.
    - right; reflexivity.
    - left; reflexivity.
    - destruct (BRB _ IQC) as (X0 & X1). cbn [fst snd] in X0, X1.
      apply (PNBOA.src_keep_x RSEGS M M3 NT NS AGXl SHXl (op + 16) (fb + 96) (fb + 96 + 16) (PNM.b_src s)); [clear - Q2; lia| clear - Ov3; lia| exact X0| clear - X1; lia| | | | | exact PSRC].
      + intros i Hi. apply (NTO (op + 256) 56); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
      + exact (NTB _ _ IQC).
      + intros i Hi. apply NSO. clear - Hi; lia.
      + exact (NSB _ _ IQC).
    - fold bb. fold x'. exact VEC3.
    - apply (PNBOA.vstr_keep_x RSEGS M M3 NT YY NS AGXl DKYl SHXl (op + 344) (PNM.b_nb s)); [clear - Q2; lia| clear - Ov3; lia| | | | | | exact PNB].
      + intros i Hi. apply (NTO (op + 344) 24); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
      + intros i Hi. apply YO. clear - Hi; lia.
      + intros i Hi. apply NSO. clear - Hi; lia.
      + intros B m Hin. exact (YB B m (INB B m Hin)).
      + intros B m Hin. exact (NSB B m (INB B m Hin)).
    - apply (PNBOA.vstr_keep_x RSEGS M M3 NT YY NS AGXl DKYl SHXl (op + 368) (PNM.b_tb s)); [clear - Q2; lia| clear - Ov3; lia| | | | | | exact PTB].
      + intros i Hi. apply (NTO (op + 368) 24); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
      + intros i Hi. apply YO. clear - Hi; lia.
      + intros i Hi. apply NSO. clear - Hi; lia.
      + intros B m Hin. exact (YB B m (ITB B m Hin)).
      + intros B m Hin. exact (NSB B m (ITB B m Hin)).
    - destruct (BRB _ ISB) as (X0 & X1). cbn [fst snd] in X0, X1.
      apply (PNBOA.bvec_keep_x RSEGS M M3 NT NS AGXl SHXl (op + 392) (PNM.b_sb s) (PNM.b_sk s) (PNM.b_stk s)); [clear - Q2; lia| clear - Ov3; lia| exact X0| clear - X1; lia| | | | exact PSTK].
      + intros i Hi. apply (NTO (op + 392) 24); [clear; lia| clear; lia| clear; lia| clear - Hi; lia].
      + exact (NTB _ _ ISB).
      + exact (NSB _ _ ISB). }
  assert (SV3 : PNARBS.saves R sp M3).
  { destruct HP3 as (P3 & _ & _). destruct SV1 as (X8 & X16 & X24 & X32 & X40 & X48).
    assert (AGS : forall a, sp - 48 <= a < sp -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. apply P3. split; [clear - Ha Q3; lia|]. split; [| intros r0 [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Ha Hr OPS; lia].
      unfold aclient, aclient_g. right; left. split; [clear - Ha SLO SHI SPT; lia| intros Z; clear - Ha Z; lia]. }
    unfold PNARBS.saves. split; [|split; [|split; [|split; [|split]]]].
    - apply (L5C.u64_at_agree RSEGS M1 M3 (sp - 8)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X8].
    - apply (L5C.u64_at_agree RSEGS M1 M3 (sp - 16)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X16].
    - apply (L5C.u64_at_agree RSEGS M1 M3 (sp - 24)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X24].
    - apply (L5C.u64_at_agree RSEGS M1 M3 (sp - 32)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X32].
    - apply (L5C.u64_at_agree RSEGS M1 M3 (sp - 40)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X40].
    - apply (L5C.u64_at_agree RSEGS M1 M3 (sp - 48)); [intros i Hi; apply AGS; clear - Hi; lia| clear - Q3; lia| clear - Q3; lia| exact X48]. }
  unfold PNARBS.op, PNARBS.SCR. fold op. change (14336 / 8) with 1792.
  split; [rewrite (L5SAR.cs_of_preserved R1 R3 2 RP3) by inl; exact aR2|].
  split; [rewrite (L5SAR.cs_of_preserved R1 R3 8 RP3) by inl; exact aR8|].
  split; [rewrite (L5SAR.cs_of_preserved R1 R3 18 RP3) by inl; apply KS1; inl|].
  split; [rewrite (L5SAR.cs_of_preserved R1 R3 19 RP3) by inl; exact aR19|].
  split. { intros k Hk. assert (Hk' : In k PNARBP.KS_abrsA) by (cbn in Hk; decompose [or] Hk; subst; try contradiction; inl).
           cbn in Hk. decompose [or] Hk; subst; try contradiction; (rewrite (L5SAR.cs_of_preserved R1 R3 _ RP3) by inl; apply KS1; exact Hk'). }
  split; [exact SV3|]. split; [exact PA3|]. split; [exact ACC3|]. split; [exact BASE3|]. split; [exact ASTK3|]. split; [exact SZ3|].
  split; [exact (BACK _ _ _ _ HH3)|]. split; [exact AM3|].
  split; [exact (L5LZ.model_rt_trans model model1 model3 MRT1 MRT3)|]. split; [exact INCLK3|]. split; [exact INCAw3|].
  split.
  - intros a (Ha & Hc & Ho). apply EK03. split; [exact Ha|]. split; [unfold LBc; apply L5SAR.aclient_appb; exact Hc|].
    intros rg [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr.
    + apply (Ho (op + 8, 8)); [unfold PNARBS.W, PNARBS.op; fold op; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Hr; lia].
    + apply (Ho (op + 320, 24)); [unfold PNARBS.W, PNARBS.op; fold op; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Hr; lia].
  - intros a Ha Hc D. apply DK03; [exact Ha| unfold LBc; apply L5SAR.aclient_appb; exact Hc| exact D].
Qed.
End Stage.
End PNARB1.
