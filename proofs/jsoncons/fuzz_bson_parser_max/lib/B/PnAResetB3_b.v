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
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAIss1_b PnAEmbKit_b PnBrObjA_b PnAResetBStmts_b PnAResetBGlue_b PnAResetBP_b PnAResetBKit_b PnAVu8Dtor_b PnAVecDtor_b PnAHarnessKit3_b PnAReset1_b Ba0_code_acc38_acc3c_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreB_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNARB3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma shz_at (M : word -> option byte) lo g p : shadow_zero M lo g -> lo mod 8 = 0 -> lo <= p -> p < lo + 8 * g -> byte_at M (S p) 0.
Proof.
  intros SZ L8 H1 H2. pose proof (SZ ((p - lo) / 8) ltac:(Lia.lia)) as X. replace (S p) with (S lo + (p - lo) / 8) by (unfold S, SB; Lia.lia). exact X.
Qed.
Lemma mod4_of16 sp d : sp mod 16 = 0 -> d mod 4 = 0 -> (sp - d) mod 4 = 0.
Proof. intros A D. Lia.lia. Qed.
Lemma rdn_nth_def (M : word -> option byte) : forall (n : nat) a bs, rdn RSEGS M (Z_to_bv 64 a) n = Some bs ->
  forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) <> None -> M (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a bs E i Hi D; [lia|].
  cbn [rdn] in E. destruct (M (Z_to_bv 64 a)) as [x|] eqn:Ea.
  - rewrite L5C.add1_lit in E. destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    injection E as <-. destruct i as [|i].
    + cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. exact Ea.
    + cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
  - destruct i as [|i]; [cbn [Z.of_nat] in D; rewrite Z.add_0_r in D; exfalso; apply D; exact Ea|].
    destruct (seg_rom RSEGS (Z_to_bv 64 a)) as [y|]; [|discriminate E]. rewrite L5C.add1_lit in E.
    destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    injection E as <-. cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
    replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
Qed.
Lemma u64_same (M M' : word -> option byte) a v i : L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v -> a <= i < a + 8 ->
  M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof.
  intros U U' Hi D D'. unfold L5.u64_at in U, U'.
  assert (Hj : (Z.to_nat (i - a) < 8)%nat) by lia.
  assert (E : i = a + Z.of_nat (Z.to_nat (i - a))) by lia.
  rewrite E in D, D' |- *. rewrite (rdn_nth_def M' _ a _ U' _ Hj D'), (rdn_nth_def M _ a _ U _ Hj D). reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Theorem tail : PNARBG.tail_stmt L ar HI.
Proof.
  unfold PNARBG.tail_stmt. intros PSH fx R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s R M model LK Aw PRE MID KONT.
  destruct PRE as (_ & _ & K0 & ENT & FRM & FRS & FOK & _ & _ & _ & _).
  unfold PNARBS.smid2, PNARBS.smid in MID. unfold PNARBS.op, PNARBS.SCR in *. set (op := fb + 464) in *. change (14336 / 8) with 1792 in MID.
  destruct MID as (G2 & G8 & G18 & G19 & GCS & SV & PA & ACC & BASE & ASTK & STKSH & HH & AM & MRT & INCLK & INCAw & EK0 & DK0).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & _ & _). rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
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
  unfold PNARBS.st2 in PBB, PNB, PTB, PSTK. cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk] in PBB, PNB, PTB, PSTK.
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
  assert (DV : forall d, 0 <= d < 416 -> (op + d) / 8 = op / 8 + d / 8).
  { intros d Hd. rewrite <- Ov5. replace (op / 8 * 8 + d) with (d + op / 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (Q12 : (sp - 64) + 64 <= op \/ op + 416 <= sp - 64) by (right; clear - OPS; lia).
  set (sb := PNM.b_sb s) in *. set (sk := PNM.b_sk s) in *. set (OWN := PNM.bparser_own s) in *.
  pose proof PSTK as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AB & EL). unfold PNM.BSZ in V8, V16, DB, CB, AB. cbn [length] in V8, Hlen, CB, AB. change (Z.of_nat 0) with 0 in V8, Hlen, CB, AB.
  assert (P2k : 1 <= 2 ^ sk <= 2048) by (clear - Hk; split; [apply (Z.pow_le_mono_r 2 0 sk); lia| apply (Z.pow_le_mono_r 2 sk 11); lia]).
  assert (ISB : In (sb, 40 * 2 ^ sk) (OWN ++ LBX)) by (apply in_or_app; left; exact (PNBOA.PNM_own_stk s)).
  pose proof (WB _ ISB) as ((Sb0 & Sb1 & Sb2 & Sb3 & Sb4 & Sb5) & _). cbn [fst snd] in Sb0, Sb5. unfold app_mem in Sb5. destruct Sb5 as (_ & _ & Sb47).
  assert (ZS : forall (Mx : word -> option byte) a n a' n', L5KA.zeros_at Mx a n -> a <= a' -> a' + n' <= a + n -> L5KA.zeros_at Mx a' n') by (intros Mx a n a' n' Z X1 X2 i Hi; replace (a' + i) with (a + (a' - a + i)) by lia; apply Z; lia).
  assert (Z400 : L5KA.zeros_at MV ((op + 400) / 8 + 2147450880) 1) by (rewrite (DV 400) by lia; change (400 / 8) with 50; apply (ZS MV (op / 8 + 2147450880) 52); [exact ZOP| lia| lia]).
  assert (Z408 : L5KA.zeros_at MV ((op + 408) / 8 + 2147450880) 1) by (rewrite (DV 408) by lia; change (408 / 8) with 51; apply (ZS MV (op / 8 + 2147450880) 52); [exact ZOP| lia| lia]).
  pose proof V8 as V8s. rewrite ?Z.mul_0_r, ?Z.add_0_r in V8s. replace (op + 392 + 8) with (op + 400) in V8s by (clear; lia).
  pose proof V16 as V16s. replace (op + 392 + 16) with (op + 408) in V16s by (clear; lia).
  assert (U392 : L5.u64_at RSEGS MV (op + 392) sb) by (apply (proj2 (L5A.u64_at_vis H M (op + 392) _ (OVs (op + 392) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))); exact V0).
  assert (U400 : L5.u64_at RSEGS MV (op + 400) sb) by (apply (proj2 (L5A.u64_at_vis H M (op + 400) _ (OVs (op + 400) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))); exact V8s).
  assert (U408 : L5.u64_at RSEGS MV (op + 408) (sb + 40 * 2 ^ sk)) by (apply (proj2 (L5A.u64_at_vis H M (op + 408) _ (OVs (op + 408) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))); exact V16s).
  assert (A36 : sb mod 16 = 0) by exact Sb2.
  assert (R36 : 0 <= sb < 2 ^ 64) by (clear - Sb0 Sb47 P2k; lia).
  assert (R50 : 0 <= sb + 40 * 2 ^ sk < 2 ^ 64) by (clear - Sb0 Sb47 P2k; lia).
  assert (B36 : 4096 <= sb <= 140737488355288) by (clear - Sb0 Sb47 P2k; lia).
  assert (B50 : 4136 <= sb + 40 * 2 ^ sk <= 140737488355327) by (cbn [fst snd] in Sb4; clear - Sb0 Sb4 SLO SHI SPT P2k; lia).
  assert (D50 : 40 <= sb + 40 * 2 ^ sk - sb <= 81920) by (clear - P2k; lia).
  LeanFeed.pfeed P (PNARBP.abrsT_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => sb | 40%nat => op | 50%nat => sb + 40 * 2 ^ sk | _ => 0 end)) ltac:(first [assumption | unfold PNARBP.aligned; assumption]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & aR1 & aR8 & aR9 & aR10 & aR11 & aR12 & aR13 & aR20 & C60 & C56 & C52).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xadcfc R1 0xacf40 M1v (fun a => sp - 60 <= a < sp - 60 + 12) K HH AM MS1 MG1).
  { intros a Ha Hnw. apply FRZ1; [exact Ha| exact Hnw]. }
  { intros a Ha Wa. split; [unfold aclientw, aclient_g; right; left; split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Wa Y; lia]| clear - Wa Q3; lia]. }
  intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4 VV4. change (mrestrict H M4 = M1v) in VIS4.
  set (P4 := fun a => sp - 60 <= a < sp - 60 + 12) in FR4.
  assert (P4sh : forall x, BIGSHADOW_LO <= x < BIGSHADOW_HI -> ~ P4 x) by (intros x Hx Y; unfold P4, BIGSHADOW_LO, BIGSHADOW_HI in *; clear - Hx Y Q3; lia).
  assert (SHM4 : forall a m, 0 <= a -> a + m <= 2 ^ 47 -> PMFA.agsh M M4 a m).
  { intros a m Ha Hn x Hx. pose proof (PMKA.S_in_shadow x ltac:(clear - Ha Hn Hx; lia)) as SX. apply FR4; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia| apply P4sh; exact SX]. }
  assert (SP16 : forall j, (sp - 16 * j) mod 8 = 0) by (intros j; apply PMKA.mod16_8'; replace (sp - 16 * j) with (sp + (- j) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
  assert (ASTK4 : L5CA.astk ar M4 sp 14336) by exact (L5SAR.astk_grows ar M M4 sp 14336 ASTK MGM4).
  assert (ASTK4c : L5CA.astk ar M4 (sp - 64) 12288).
  { apply (L5SAR.astk_sub ar M M4 sp 14336 64 12288 ASTK MGM4); [clear; lia|clear; lia|clear; lia|]. replace (sp - 64) with (sp + (-4) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
  assert (SZ4 : shadow_zero M4 (sp - 14336) 1792).
  { intros j Hj. pose proof (STKSH j Hj) as Z1. unfold byte_at in *. assert (L8 : (sp - 14336) mod 8 = 0) by (replace (sp - 14336) with (sp - 16 * 896) by (clear; lia); apply SP16).
    rewrite (PMFA.S_granule (sp - 14336) j L8 ltac:(clear - Hj; lia)) in *.
    pose proof (PMKA.S_in_shadow (sp - 14336 + 8 * j) ltac:(clear - Q3 Hj; lia)) as SX. rewrite FR4; [exact Z1| unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; clear - SX; lia| apply P4sh; exact SX]. }
  assert (SZ4c : shadow_zero M4 (sp - 64 - 12288) 1536).
  { apply (PMKA.shadow_zero_sub M4 (sp - 14336) 1792); [replace (sp - 14336) with (sp - 16 * 896) by (clear; lia); apply SP16| replace (sp - 64 - 12288) with (sp - 16 * 772) by (clear; lia); apply SP16| clear; lia| clear; lia| clear; lia| exact SZ4]. }
  assert (AG4 : forall a n, (a + n <= sp - 60 \/ sp - 48 <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M4 a n).
  { intros a n NP Ha Hn i Hi. apply FR4; [clear - Ha Hn Hi; lia| unfold P4; clear - NP Hi; lia]. }
  assert (CW4 : forall p, sp - 60 <= p -> p + 4 <= sp - 48 -> L5.u32_at RSEGS M1v p 0 -> L5.u32_at RSEGS M4 p 0).
  { intros p X1 X2 U. apply (proj1 (L5A.u32_at_vis H M4 p 0 (VIS p 4 ltac:(clear - X1 SLO; lia) ltac:(clear - X2 Q3; lia)) ltac:(clear - X1 Q3; lia) ltac:(clear - X2 Q3; lia))). rewrite VIS4. exact U. }
  (* [comment removed for export] *)
  set (LBc := lb_remove sb (OWN ++ LBX)).
  pose proof (PNAV8D.ri_front L ar C HI HIok _ _ _ _ _ _ _ sb (40 * 2 ^ sk) HH4 ISB) as HH4s. fold LBc in HH4s.
  change ((sb, 40 * 2 ^ sk) :: LBc) with (PNM.bvec_own sb sk ++ LBc) in HH4s.
  assert (AOV : PMSPA.aobjA FF (op + 392) 24) by (apply (PNAV8D.aobjA_sub FF op 416); [exact AOP| clear; lia| clear; lia]).
  assert (V8m : (op + 392) mod 8 = 0) by (replace (op + 392) with (op + 49 * 8) by (clear; lia); rewrite Z.mod_add by (clear; lia); exact O8).
  assert (VEC4 : PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M4 (op + 392) sb sk []).
  { unfold PNM.bvec_at, PNM.BSZ. cbn [length]. change (Z.of_nat 0) with 0.
    split; [apply (L5C.u64_at_agree RSEGS M M4 (op + 392)); [apply AG4; [left; clear - OPS; lia| clear - Q2; lia| clear - Ov3; lia]| clear - Q2; lia| clear - Ov3; lia| exact V0]|].
    split; [apply (L5C.u64_at_agree RSEGS M M4 (op + 392 + 8)); [apply AG4; [left; clear - OPS; lia| clear - Q2; lia| clear - Ov3; lia]| clear - Q2; lia| clear - Ov3; lia| exact V8]|].
    split; [apply (L5C.u64_at_agree RSEGS M M4 (op + 392 + 16)); [apply AG4; [left; clear - OPS; lia| clear - Q2; lia| clear - Ov3; lia]| clear - Q2; lia| clear - Ov3; lia| exact V16]|].
    split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|]. split; [intros i Hi; apply MGM4; apply DB; exact Hi|].
    split; [apply (PMFA.accA_agree M M4); [apply SHM4; clear - Sb0 Sb47 P2k; lia| exact CB]|].
    split. { apply (PNAEK.ann_agree M M4 sb (40 * 0) (40 * 2 ^ sk)); [| clear; lia| clear - P2k; lia| exact AB].
             intros j Hj. rewrite (PNAEK.S_add8 sb j). apply (SHM4 sb (8 * ((40 * 2 ^ sk + 7) / 8))); [clear - Sb0; lia| | ].
             - clear - Sb0 Sb47 Hal P2k. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
             - clear - Hj P2k. Lia.lia. }
    intros i Hi. cbn [length] in Hi. clear - Hi. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (BASE4 : PMSTA.base_okA RSEGS PMA.AD M4).
  { assert (EK04s : L5SAR.ek L ar LBX FF sp 14336 [] M M4).
    { intros a (Ha & Hc & _). apply FR4; [exact Ha|]. unfold P4. intros X.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 14336 a HH SPT (L5SAR.aclient_appb L ar LBX OWN FF sp 14336 a Hc)) as [(_ & Z2)|Z2]; [apply Z2; clear - X; lia| clear - X Z2 SLO; lia]. }
    apply (PMKA.base_ok_keepA RSEGS PMA.AD L ar LBX FF sp 14336 [] M M4 EK04s PMA.addrs_wf_A); [| | exact BASE].
    - intros a D. pose proof (PMAIS1.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
      split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))| intros r0 []].
    - intros a Ha. cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - Ha; lia|].
      split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X) as Y; clear - Ha Y; lia| intros r0 []]. }
  unfold PnSpecsAXR_b.PNSAXR.push_root_fast_spec in PSH.
  apply (PSH fx1 R1 M4 model4 K LBc FF LK Aw cr (op + 392) sb sk [] (0, 0, 0) (sp - 64) 0xadd50 HH4s AM4 K0).
  { split; [rewrite L5K.rl1; exact aR1|]. split; [split; [clear; lia| reflexivity]|].
    split; [rewrite L5K.rl2, (KS1 2%nat) by inl; exact G2|].
    split; [rewrite L5K.rl3, (KS1 3%nat) by inl; rewrite (GCS 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS1 4%nat) by inl; rewrite (GCS 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK4c|]. change (12288 / 8) with 1536. exact SZ4c. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS. lia. }
  { rewrite L5K.rl10. exact aR10. }
  { exact AOV. }
  { exact V8m. }
  { apply (PMFA.accA_agree M M4); [apply SHM4; clear - Q2 Ov3; lia|]. intros a Ha. apply ACC. clear - Ha. lia. }
  { exact VEC4. }
  { cbn [length]. change (Z.of_nat 0) with 0. clear - P2k. lia. }
  { exact BASE4. }
  { unfold PNSAX.cells_root. exists (sp - 52), (sp - 56), (sp - 60). cbn [fst snd].
    split; [rewrite L5K.rl11; exact aR11|]. split; [rewrite L5K.rl12; exact aR12|]. split; [rewrite L5K.rl13; exact aR13|].
    assert (AC : forall p, sp - 64 <= p -> p + 4 <= sp -> p mod 4 = 0 -> PNSAX.arg_cell ar M4 FF (sp - 64) (op + 392) p 4).
    { intros p P1 P2 P4'. unfold PNSAX.arg_cell, PNSAX.arg_ok. split; [exact P4'|].
      split; [unfold PMSPA.accA; apply (L5CB.aacc_of_zero M4 (sp - 14336) 1792 p 4 SZ4); [replace (sp - 14336) with (sp - 16 * 896) by (clear; lia); apply SP16| clear - Q3; lia| clear - P1; lia| clear - P2; lia]|].
      split; [split; [right; clear - P1 P2 SLO SHI SPT; lia| right; clear - P1 OPS; lia]|].
      apply (shz_at M4 (sp - 14336) 1792); [exact SZ4| replace (sp - 14336) with (sp - 16 * 896) by (clear; lia); apply SP16| clear - P1; lia| clear - P2; lia]. }
    split; [apply AC; [clear; lia| clear; lia| apply mod4_of16; [exact A16| reflexivity]]|].
    split; [apply AC; [clear; lia| clear; lia| apply mod4_of16; [exact A16| reflexivity]]|].
    split; [apply AC; [clear; lia| clear; lia| apply mod4_of16; [exact A16| reflexivity]]|].
    split; [apply CW4; [clear; lia| clear; lia| exact C52]|]. split; [apply CW4; [clear; lia| clear; lia| exact C56]|]. split; [apply CW4; [clear; lia| clear; lia| exact C60]|].
    split; [clear; lia|]. split; clear; lia. }
  intros fx7 R7 M7 model7 LK7 Aw7 RP7 VEC7 DJ7 ACCV7 BASE7 HP7 MRT7 INC7 IA7 AM7 HH7.
  change (PMSPA.pm_scr 0) with 12288 in HP7. cbn [app] in VEC7.
  (* [comment removed for export] *)
  pose proof (PNARBK.ri_back L ar C HI HIok _ _ _ _ _ _ _ sb (40 * 2 ^ sk) ND ISB HH7) as HH7o.
  assert (ASTK7 : L5CA.astk ar M7 sp 14336) by (apply (PMKA.astk_after_ahpres L ar LBc FF M4 M7 sp 14336 (sp - 64) 12288 [(op + 392, 24)] ASTK4 HP7); [clear; lia| clear; lia| clear; lia| exact STOP]).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK7 cr Aw7 M7 model7 HH7o) as (_ & VIS7 & _ & _ & _ & _ & _ & _).
  set (H7 := ahid Aw7 model7) in *. set (MV7 := mrestrict H7 M7) in *.
  assert (STK7 : forall a, sp - 48 <= a < sp -> M7 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha. apply (proj1 HP7). split; [clear - Ha Q3; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha SLO SHI SPT; lia| intros Z; clear - Ha Z; lia].
    - intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr OPS. lia. }
  assert (SV7 : PNARBS.saves R0 sp MV7).
  { destruct SV as (X8 & X16 & X24 & X32 & X40 & X48). unfold PNARBS.saves.
    assert (SW : forall a v, sp - 48 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV7 a v).
    { intros a v Y1 Y2 U. apply (proj2 (L5A.u64_at_vis H7 M7 a v (VIS7 a 8 ltac:(clear - Y1 SLO; lia) ltac:(clear - Y2 Q3; lia)) ltac:(clear - Y1 Q3; lia) ltac:(clear - Y2 Q3; lia))).
      apply (L5C.u64_at_agree RSEGS M4 M7 a); [intros i Hi; apply STK7; clear - Hi Y1 Y2; lia| clear - Y1 Q3; lia| clear - Y2 Q3; lia|].
      apply (L5C.u64_at_agree RSEGS M M4 a); [apply AG4; [right; exact Y1| clear - Y1 Q3; lia| clear - Y2 Q3; lia]| clear - Y1 Q3; lia| clear - Y2 Q3; lia| exact U]. }
    split; [apply SW; [clear; lia| clear; lia| exact X8]|]. split; [apply SW; [clear; lia| clear; lia| exact X16]|]. split; [apply SW; [clear; lia| clear; lia| exact X24]|].
    split; [apply SW; [clear; lia| clear; lia| exact X32]|]. split; [apply SW; [clear; lia| clear; lia| exact X40]| apply SW; [clear; lia| clear; lia| exact X48]]. }
  destruct SV7 as (S8v & S16v & S24v & S32v & S40v & S48v).
  assert (VSW7 : L5.writable RSEGS MV7 (sp - 64) 64).
  { pose proof ASTK7 as (_ & _ & _ & _ & SDEF7 & _).
    apply (proj2 (L5A.writable_vis H7 M7 (sp - 64) 64 (VIS7 (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - Q3; lia)) ltac:(clear - Q3; lia) ltac:(clear - Q3; lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M7 (sp - 14336) 14336); [exact SDEF7| clear; lia| clear; lia]| clear - Q3; lia| clear - Q3; lia]. }
  assert (REG7 : forall j, In j [2; 3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr R (reg j)).
  { intros j Hj. assert (Hj' : In j PNARBP.KS_abrsT) by (cbn in Hj; decompose [or] Hj; subst; try contradiction; inl).
    cbn in Hj. decompose [or] Hj; subst; try contradiction; (rewrite (L5SAR.cs_of_preserved R1 R7 _ RP7) by inl; apply KS1; exact Hj'). }
  assert (RP17 : forall j, In j L5SAR.cs_all -> getr R7 (reg j) = getr R1 (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R1 R7 j RP7 Hj)).
  (* [comment removed for export] *)
  idtac.
  set (Wx := [(op + 392, 24)]).
  assert (WAPPx : PMKA.wapp Wx).
  { unfold Wx. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OBIG; lia| apply PMKA.wapp_nil]. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). clear - X1 X2 FSAPP. unfold app_mem, FS_BYTES in *. lia. }
  assert (EK04 : L5SAR.ek L ar LBc FF sp 14336 Wx M M4).
  { intros a (Ha & Hc & _). apply FR4; [exact Ha|]. unfold P4. intros X.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M4 _ sp 14336 a HH4s SPT (L5SAR.aclient_appb L ar LBc (PNM.bvec_own sb sk) FF sp 14336 a Hc)) as [(_ & Z2)|Z2]; [apply Z2; clear - X; lia| clear - X Z2 SLO; lia]. }
  assert (EK47 : L5SAR.ek L ar LBc FF sp 14336 Wx M4 M7).
  { apply (L5SAR.ek_callee L ar LBc [] FF [] sp 14336 (sp - 64) 12288 Wx [(op + 392, 24)] M4 M7 HP7); [clear; lia| clear; lia| intros a _ Ho; exact Ho]. }
  pose proof (L5SAR.ek_trans L ar LBc FF sp 14336 Wx M M4 M7 EK04 EK47) as EK07.
  assert (ACC7 : PMSPA.accA M7 op 416) by exact (PMKA.acc_keepA' L ar LBc FF sp 14336 Wx M M7 EK07 WAPPx FRB op 416 AOP ACC).
  assert (ZOP7 : L5KA.zeros_at MV7 (op / 8 + 2147450880) 52) by exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK7 cr Aw7 M7 model7 op 416 HH7o AOP O8 ltac:(clear; lia) ltac:(reflexivity) ACC7).
  assert (Z7 : L5KA.zeros_at MV7 ((op + 400) / 8 + 2147450880) 1) by (rewrite (DV 400) by lia; change (400 / 8) with 50; apply (ZS MV7 (op / 8 + 2147450880) 52); [exact ZOP7| lia| lia]).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK7 cr Aw7 M7 model7 op 416 sp 14336 HH7o AOB ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF7 & OVIS7 & _).
  assert (DV7 : L5.defined MV7 op 416) by exact (proj2 (L5A.defined_vis H7 M7 op 416 OVIS7) ODEF7).
  assert (W7 : L5.writable RSEGS MV7 (op + 400) 8).
  { apply (proj2 (L5A.writable_vis H7 M7 (op + 400) 8 (L5A.avis_sub _ op 416 (op + 400) 8 OVIS7 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M7 op 416); [exact ODEF7| clear; lia| clear; lia]| lia| lia]. }
  assert (U7 : L5.u64_at RSEGS MV7 (op + 400) (sb + 40)).
  { pose proof VEC7 as (_ & W8 & _).
    apply (proj2 (L5A.u64_at_vis H7 M7 (op + 400) _ (L5A.avis_sub _ op 416 (op + 400) 8 OVIS7 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - Q2; lia) ltac:(clear - Ov3; lia))).
    replace (op + 400) with (op + 392 + 8) by (clear; lia). exact W8. }
  assert (B38 : 0 <= bv_unsigned (getr R0 (reg 1)) < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ (getr R0 (reg 1))) as X; unfold bv_modulus in X; exact X).
  assert (B39 : 0 <= bv_unsigned (getr R0 (reg 8)) < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ (getr R0 (reg 8))) as X; unfold bv_modulus in X; exact X).
  assert (B41 : 0 <= bv_unsigned (getr R0 (reg 9)) < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ (getr R0 (reg 9))) as X; unfold bv_modulus in X; exact X).
  assert (B42 : 0 <= bv_unsigned (getr R0 (reg 18)) < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ (getr R0 (reg 18))) as X; unfold bv_modulus in X; exact X).
  assert (B43 : 0 <= bv_unsigned (getr R0 (reg 19)) < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ (getr R0 (reg 19))) as X; unfold bv_modulus in X; exact X).
  assert (B44 : 0 <= bv_unsigned (getr R0 (reg 20)) < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ (getr R0 (reg 20))) as X; unfold bv_modulus in X; exact X).
  assert (G72 : getr R7 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (REG7 2%nat) by inl; exact G2).
  assert (G78 : getr R7 (reg 8) = Z_to_bv 64 sb) by (rewrite (RP17 8%nat) by inl; exact aR8).
  assert (G79 : getr R7 (reg 9) = Z_to_bv 64 (op + 400)) by (rewrite (RP17 9%nat) by inl; exact aR9).
  assert (G718 : getr R7 (reg 18) = Z_to_bv 64 (op + 392)) by (rewrite (REG7 18%nat) by inl; exact G18).
  assert (G719 : getr R7 (reg 19) = Z_to_bv 64 2147450880) by (rewrite (REG7 19%nat) by inl; exact G19).
  assert (G720 : getr R7 (reg 20) = Z_to_bv 64 ((op + 400) / 8 + 2147450880)) by (rewrite (RP17 20%nat) by inl; exact aR20).
  LeanFeed.pfeed P (PNARBP.abrsZ_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => sb | 38%nat => bv_unsigned (getr R0 (reg 1)) | 39%nat => bv_unsigned (getr R0 (reg 8)) | 40%nat => op
                                                         | 41%nat => bv_unsigned (getr R0 (reg 9)) | 42%nat => bv_unsigned (getr R0 (reg 18)) | 43%nat => bv_unsigned (getr R0 (reg 19))
                                                         | 44%nat => bv_unsigned (getr R0 (reg 20)) | _ => 0 end)) ltac:(first [assumption | unfold PNARBP.aligned; assumption]).
  destruct P as (fx8 & R8 & M8v & MG8 & _ & FZ8 & MS8 & KS8 & zR1 & zR2 & zR8 & zR9 & zR10 & zR11 & zR18 & zR19 & zR20 & zU).
  assert (E8 : M8v = MV7).
  { apply L5SAR.mem_eq_of_agree. intros i Hi.
    destruct (Z_lt_le_dec i (op + 400)) as [Hl|Hl]; [apply FZ8; [exact Hi| clear - Hl; lia]|].
    destruct (Z_lt_le_dec i (op + 408)) as [Hh|Hh]; [|apply FZ8; [exact Hi| clear - Hh; lia]].
    assert (D7 : MV7 (Z_to_bv 64 i) <> None) by (pose proof (DV7 (i - op) ltac:(clear - Hl Hh; lia)) as X; replace (op + (i - op)) with i in X by (clear; lia); exact X).
    exact (u64_same MV7 M8v (op + 400) (sb + 40) i U7 zU ltac:(clear - Hl Hh; lia) D7 (MG8 _ D7)). }
  subst M8v.
  assert (R8ra : getr R8 (reg 1) = Z_to_bv 64 r) by (rewrite zR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx8 R8 MV7 0xaddb8 W_acc38 r F_acc38 eq_refl D_acc38 R8ra ltac:(clear - Hr1; lia) Hr2) as MS9.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK7 _ Aw7 M7 model7 fx7 fx8 R7 0xadd50 R8 r _ K HH7o AM7 ltac:(eapply msteps_trans; [exact MS8| exact MS9]) MG8 ltac:(intros a _; reflexivity)).
  intros M7' model7' HH7' AM7' MRT7' HID7' VIS7' MGM7' FR7'.
  assert (E7' : M7' = M7) by (apply L5SAR.mem_eq_of_agree; exact FR7'). subst M7'.
  apply (KONT fx8 R8 M7 model7' LK7 Aw7).
  - (* [comment removed for export] *)
    apply L5SAR.preserved_by_index. intros k Hk'.
    assert (CH : forall k', In k' [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R8 (reg k') = getr R0 (reg k')).
    { intros k' Hk2. assert (Y : In k' PNARBP.KS_abrsZ /\ In k' [2; 3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat)
        by (cbn in Hk2; decompose [or] Hk2; subst; try contradiction; (split; inl)).
      destruct Y as (Y1 & Y2). rewrite (KS8 k' Y1), (REG7 k' Y2). apply GCS. cbn in Hk2. decompose [or] Hk2; subst; try contradiction; inl. }
    unfold L5SAR.cs_all in Hk'. destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hk']]]]]]]].
    + rewrite zR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite zR8, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR9, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR18, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR19, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite zR20, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH; right; right; exact Hk'.
  - (* [comment removed for export] *)
    set (bb0 := PNM.b_bb s) in *. set (nb := PNM.b_nb s) in *. set (tb := PNM.b_tb s) in *.
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
    assert (BRB : forall b0, In b0 LBc -> 0 <= fst b0 /\ fst b0 + snd b0 <= 2 ^ 47).
    { intros b0 Hb0. destruct (proj1 (WB b0 (INC b0 Hb0))) as (X0 & _ & _ & _ & _ & X5). clear - X0 X5. unfold app_mem in X5. lia. }
    assert (DK07 : L5SAR.dk L ar LBc FF sp 14336 M M7).
    { apply (L5SAR.dk_trans L ar LBc FF sp 14336 M M4 M7); [exact (L5SAR.dk_grows L ar LBc FF sp 14336 M M4 MGM4)|].
      apply (L5SAR.dk_callee L ar LBc [] FF [] sp 14336 (sp - 64) 12288 [(op + 392, 24)] M4 M7 HP7); clear; lia. }
    assert (BOUT : forall b0, In b0 LBc -> forall i, fst b0 <= i < fst b0 + snd b0 -> L5.outside Wx i).
    { intros b0 Hb0 i Hi. destruct (WB b0 (INC b0 Hb0)) as (_ & _ & _ & _ & _ & _ & X).
      intros rg [<-|[]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold op in Hr; clear - X Hi Hr F1 F2; lia. }
    assert (BLKA : forall q m, In (q, m) LBc -> PMFA.agA M M7 q m).
    { intros q m Hin. apply (PMKA.agA_blk L ar LBc FF sp 14336 Wx M M7 EK07 WAPPx BRB q m Hin). exact (BOUT (q, m) Hin). }
    set (NT := fun i : Z => M7 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    set (YY := fun i : Z => M (Z_to_bv 64 i) <> None -> M7 (Z_to_bv 64 i) <> None).
    set (NS := fun i : Z => M7 (Z_to_bv 64 (S i)) = M (Z_to_bv 64 (S i))).
    assert (AGXl : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> NT i) -> L5C.agree_on M M7 a n) by (intros a n _ _ X i Hi; exact (X i Hi)).
    assert (DKYl : forall i, YY i -> M (Z_to_bv 64 i) <> None -> M7 (Z_to_bv 64 i) <> None) by (intros i X; exact X).
    assert (SHXl : forall a n, (forall i, a <= i < a + n -> NS i) -> PMFA.agsh M M7 a n) by (intros a n X x Hx; exact (X x Hx)).
    assert (NTO : forall a n, op <= a -> a + n <= op + 392 -> forall i, a <= i < a + n -> NT i).
    { intros a n X1 X2 i Hi.
      refine (proj1 (PMKA.agA_obj L ar LBc FF sp 14336 Wx M M7 EK07 WAPPx FRB a n (PNAV8D.aobjA_sub FF op 416 a n AOP X1 ltac:(clear - X2; lia)) _) i Hi).
      intros j Hj rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hj Hr X2. lia. }
    pose proof (PMKA.agsh_obj L ar LBc FF sp 14336 Wx M M7 EK07 WAPPx FRB op 416 AOP) as OSH.
    assert (NSO : forall i, op <= i < op + 416 -> NS i) by (intros i Hi; exact (OSH i Hi)).
    assert (YO : forall i, op <= i < op + 416 -> YY i).
    { intros i Hi. unfold YY. apply DK07; [clear - Hi Q2 Ov3; lia|]. exact (L5SAR.obj_client L ar LBc FF sp 14336 op 416 i AOB Hi). }
    assert (NTB : forall q m, In (q, m) LBc -> forall i, q <= i < q + m -> NT i) by (intros q m Hin i Hi; exact (proj1 (BLKA q m Hin) i Hi)).
    assert (NSB : forall q m, In (q, m) LBc -> forall i, q <= i < q + m -> NS i) by (intros q m Hin i Hi; exact (proj2 (BLKA q m Hin) i Hi)).
    assert (YB : forall q m, In (q, m) LBc -> forall i, q <= i < q + m -> YY i) by (intros q m Hin i Hi D; unfold NT in NTB; rewrite (NTB q m Hin i Hi); exact D).
    unfold PNARBS.op. fold op. unfold PNARBS.bparser_at.
    apply (PNBOA.bparser_at_xfer RSEGS PMA.AD (pa_vp_parser PMA.AD) M M7 NT YY NS AGXl DKYl SHXl op (fb + 96) (PNARBS.st2 s) (PNRA.bpst_reset s));
      unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNARBS.st2, PNRA.bpst_reset;
      cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk]; fold bb0 nb tb sb sk.
    + clear - Q2; lia.
    + clear - Ov3; lia.
    + exact PA.
    + exact YO.
    + exact NSO.
    + intros i Hi. apply (NTO op 8); [clear; lia| clear; lia| clear - Hi; lia].
    + intros i Hi. apply (NTO (op + 10) 6); [clear; lia| clear; lia| clear - Hi; lia].
    + intros i Hi. apply (NTO (op + 24) 232); [clear; lia| clear; lia| clear - Hi; lia].
    + intros i Hi. apply (NTO (op + 312) 8); [clear; lia| clear; lia| clear - Hi; lia].
    + apply (L5C.u8_at_agree RSEGS M M7 (op + 8)); [intros i Hi; apply (NTO (op + 8) 1); [clear; lia| clear; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact P8].
    + apply (L5C.u8_at_agree RSEGS M M7 (op + 9)); [intros i Hi; apply (NTO (op + 9) 1); [clear; lia| clear; lia| clear - Hi; lia]| clear - Q2; lia| clear - Ov3; lia| exact P9].
    + right; reflexivity.
    + left; reflexivity.
    + destruct (BRB _ IQC) as (X0 & X1). cbn [fst snd] in X0, X1.
      apply (PNBOA.src_keep_x RSEGS M M7 NT NS AGXl SHXl (op + 16) (fb + 96) (fb + 96 + 16) (PNM.b_src s)); [clear - Q2; lia| clear - Ov3; lia| exact X0| clear - X1; lia| | | | | exact PSRC].
      * intros i Hi. apply (NTO (op + 256) 56); [clear; lia| clear; lia| clear - Hi; lia].
      * exact (NTB _ _ IQC).
      * intros i Hi. apply NSO. clear - Hi; lia.
      * exact (NSB _ _ IQC).
    + apply (PNBOA.v8_keep_x RSEGS M M7 NT YY NS AGXl DKYl SHXl (op + 320) (PGV8.v8_clear bb0)); [clear - Q2; lia| clear - Ov3; lia| | | | | exact PBB].
      * intros i Hi. apply (NTO (op + 320) 24); [clear; lia| clear; lia| clear - Hi; lia].
      * intros i Hi. apply NSO. clear - Hi; lia.
      * intros B m HB. assert (HB' : In (B, m) (PGV8.v8_own bb0)) by (destruct bb0; exact HB). exact (YB B m (IBB B m HB')).
      * intros B m HB. assert (HB' : In (B, m) (PGV8.v8_own bb0)) by (destruct bb0; exact HB).
        destruct PBB as (_ & _ & PR). destruct bb0 as [|b8 n8 c8]; [destruct HB'|]. destruct HB' as [E|[]]. injection E as <- <-. cbn [PGV8.v8_clear] in PR. destruct PR as (_ & _ & _ & _ & Hc8 & _ & Hal8 & _).
        exact (PNBOA.agsh_gspan M M7 b8 c8 (PMFA.mod16_8 _ Hal8) ltac:(clear - Hc8; lia) (proj2 (BLKA b8 c8 (IBB b8 c8 ltac:(left; reflexivity))))).
    + assert (OWC : forall x B m, In (B, m) (PM.vs_own (PNRA.vs_clear x)) -> In (B, m) (PM.vs_own x)) by (intros x B m; destruct x; cbn; tauto).
      apply (PNBOA.vstr_keep_x RSEGS M M7 NT YY NS AGXl DKYl SHXl (op + 344) (PNRA.vs_clear nb)); [clear - Q2; lia| clear - Ov3; lia| | | | | | exact PNB].
      * intros i Hi. apply (NTO (op + 344) 24); [clear; lia| clear; lia| clear - Hi; lia].
      * intros i Hi. apply YO. clear - Hi; lia.
      * intros i Hi. apply NSO. clear - Hi; lia.
      * intros B m Hin. exact (YB B m (INB B m (OWC nb B m Hin))).
      * intros B m Hin. exact (NSB B m (INB B m (OWC nb B m Hin))).
    + assert (OWC : forall x B m, In (B, m) (PM.vs_own (PNRA.vs_clear x)) -> In (B, m) (PM.vs_own x)) by (intros x B m; destruct x; cbn; tauto).
      apply (PNBOA.vstr_keep_x RSEGS M M7 NT YY NS AGXl DKYl SHXl (op + 368) (PNRA.vs_clear tb)); [clear - Q2; lia| clear - Ov3; lia| | | | | | exact PTB].
      * intros i Hi. apply (NTO (op + 368) 24); [clear; lia| clear; lia| clear - Hi; lia].
      * intros i Hi. apply YO. clear - Hi; lia.
      * intros i Hi. apply NSO. clear - Hi; lia.
      * intros B m Hin. exact (YB B m (ITB B m (OWC tb B m Hin))).
      * intros B m Hin. exact (NSB B m (ITB B m (OWC tb B m Hin))).
    + exact VEC7.
  - (* [comment removed for export] *)
    change (PMSPA.pm_scr 1) with 14336.
    assert (EKM7 : L5SAR.ek L ar LBX FF sp 14336 (PNARBS.W fb) M M7).
    { intros a (Ha & Hc & Ho).
      assert (Hc' : aclient L ar LBc FF sp 14336 a).
      { unfold LBc. rewrite (PNARBK.lbr_app_l sb OWN LBX (in_map fst OWN (sb, 40 * 2 ^ sk) (PNBOA.PNM_own_stk s))). apply L5SAR.aclient_appb. exact Hc. }
      rewrite (proj1 HP7).
      - apply FR4; [exact Ha|]. unfold P4. intros X.
        destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M4 _ sp 14336 a HH4s SPT (L5SAR.aclient_appb L ar LBc (PNM.bvec_own sb sk) FF sp 14336 a Hc')) as [(_ & Z2)|Z2]; [apply Z2; clear - X; lia| clear - X Z2 SLO; lia].
      - split; [exact Ha|]. split; [eapply L5SAR.aclient_mono; [exact Hc'| intros x Hx; clear - Hx; lia]|].
        intros rg [<-|[]] Hr. apply (Ho (op + 392, 24)); [unfold PNARBS.W, PNARBS.op; fold op; do 4 right; left; reflexivity| exact Hr]. }
    assert (DKM7 : L5SAR.dk L ar LBX FF sp 14336 M M7).
    { intros a Ha Hc D.
      assert (Hc' : aclient L ar LBc FF sp 14336 a).
      { unfold LBc. rewrite (PNARBK.lbr_app_l sb OWN LBX (in_map fst OWN (sb, 40 * 2 ^ sk) (PNBOA.PNM_own_stk s))). apply L5SAR.aclient_appb. exact Hc. }
      refine (L5SAR.dk_callee L ar LBc [] FF [] sp 14336 (sp - 64) 12288 [(op + 392, 24)] M4 M7 HP7 ltac:(clear; lia) ltac:(clear; lia) a Ha Hc' _). apply MGM4. exact D. }
    apply (L5SAR.ahpres_of L ar LBX FF sp 14336 (PNARBS.W fb) M0 M7).
    + exact (L5SAR.ek_trans L ar LBX FF sp 14336 (PNARBS.W fb) M0 M M7 EK0 EKM7).
    + pose proof ASTK7 as (_ & _ & _ & _ & D7 & _). exact D7.
    + exact (L5SAR.dk_trans L ar LBX FF sp 14336 M0 M M7 DK0 DKM7).
  - exact (L5LZ.model_rt_trans model0 model model7' MRT (L5LZ.model_rt_trans model model4 model7' MRT4 (L5LZ.model_rt_trans model4 model7 model7' MRT7 MRT7'))).
  - exact (incl_tran INC7 INCLK).
  - exact (incl_tran INCAw IA7).
  - exact AM7'.
  - exact HH7'.
Qed.
End Stage.
End PNARB3.
