(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PmStep PeStepAB0 PeBCReset1 PeBEmbKitJ PeEmbShKit PeSpecsBXJ PeBVecClearP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_aa8a0_aa8a4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBVC.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Definition LIVE : list nat := [2; 3; 4; 8; 9; 10; 12; 13; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Lemma loop_run (Mv : word -> option byte) (s b : Z) : 0 <= s < 2 ^ 64 -> 4096 <= b <= 140737488355296 ->
  forall (n : nat) fx R, 32 * (Z.of_nat n + 1) <= 65536 ->
    getr R (reg 2) = Z_to_bv 64 s -> getr R (reg 13) = Z_to_bv 64 b -> getr R (reg 15) = Z_to_bv 64 32 ->
    getr R (reg 16) = Z_to_bv 64 (b + 32 * (Z.of_nat n + 1)) ->
    exists fx' R', msteps RSEGS (st fx R 0xaa8d4 Mv) (st fx' R' 0xaa8e4 Mv)
      /\ (forall x, In x LIVE -> getr R' (reg x) = getr R (reg x)).
Proof.
  intros Hs Hb. induction n as [|n IH]; intros fx R Hn R2 R13 R15 R16.
  - pose proof (PMBVCP.bvcL1_conc fx R Mv (fun j => match j with 2%nat => s | 36%nat => b | 45%nat => 32 | _ => 0 end)) as P. cbn beta iota in P.
    destruct (P ltac:(lia) ltac:(lia) ltac:(lia) R2 R15 ltac:(rewrite R16; f_equal; lia) ltac:(lia) ltac:(lia))
      as (fx1 & R1 & M1 & _ & FR1 & _ & MS1 & KS1 & A16). clear P.
    assert (E1 : M1 = Mv) by (apply functional_extensionality; exact FR1). subst M1.
    pose proof (PMBVCP.bvcL2x_conc fx1 R1 Mv (fun j => match j with 2%nat => s | 36%nat => b | _ => 0 end)) as P. cbn beta iota in P.
    destruct (P ltac:(lia) ltac:(lia) ltac:(rewrite (KS1 2%nat) by inl; exact R2) ltac:(rewrite (KS1 13%nat) by inl; exact R13)
                ltac:(rewrite A16; f_equal; lia) ltac:(lia)) as (fx2 & R3 & M2 & _ & FR2 & _ & MS2 & KS2). clear P.
    assert (E2 : M2 = Mv) by (apply functional_extensionality; exact FR2). subst M2.
    exists fx2, R3. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
    intros x Hx. repeat (destruct Hx as [<-|Hx]; [rewrite (KS2 _) by inl; rewrite (KS1 _) by inl; reflexivity|]). destruct Hx.
  - pose proof (PMBVCP.bvcL1_conc fx R Mv (fun j => match j with 2%nat => s | 36%nat => b | 45%nat => 32 * (Z.of_nat (Datatypes.S n) + 1) | _ => 0 end)) as P.
    cbn beta iota in P.
    destruct (P ltac:(lia) ltac:(lia) ltac:(lia) R2 R15 R16 ltac:(lia) ltac:(lia)) as (fx1 & R1 & M1 & _ & FR1 & _ & MS1 & KS1 & A16). clear P.
    assert (E1 : M1 = Mv) by (apply functional_extensionality; exact FR1). subst M1.
    pose proof (PMBVCP.bvcL2c_conc fx1 R1 Mv (fun j => match j with 2%nat => s | 36%nat => b | 45%nat => 32 * (Z.of_nat n + 1) | _ => 0 end)) as P.
    cbn beta iota in P.
    destruct (P ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite (KS1 2%nat) by inl; exact R2) ltac:(rewrite (KS1 13%nat) by inl; exact R13)
                ltac:(rewrite A16; f_equal; lia) ltac:(lia) ltac:(lia)) as (fx2 & R3 & M2 & _ & FR2 & _ & MS2 & KS2). clear P.
    assert (E2 : M2 = Mv) by (apply functional_extensionality; exact FR2). subst M2.
    destruct (IH fx2 R3 ltac:(lia) ltac:(rewrite (KS2 2%nat) by inl; rewrite (KS1 2%nat) by inl; exact R2)
                 ltac:(rewrite (KS2 13%nat) by inl; rewrite (KS1 13%nat) by inl; exact R13)
                 ltac:(rewrite (KS2 15%nat) by inl; rewrite (KS1 15%nat) by inl; exact R15)
                 ltac:(rewrite (KS2 16%nat) by inl; rewrite A16; f_equal; lia)) as (fx3 & R4 & MS3 & KS3).
    exists fx3, R4. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]|].
    intros x Hx. rewrite (KS3 x Hx). revert Hx.
    intros Hx. repeat (destruct Hx as [<-|Hx]; [rewrite (KS2 _) by inl; rewrite (KS1 _) by inl; reflexivity|]). destruct Hx.
Qed.

Definition KEEP1 : list nat := [3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition nsh (a n : Z) : Prop := a + n <= 2147446784 \/ 17594333495296 <= a.
Lemma nsh_not a n x : nsh a n -> a <= x < a + n -> ~ (BIGSHADOW_LO <= x < BIGSHADOW_HI).
Proof. unfold nsh, BIGSHADOW_LO, BIGSHADOW_HI. intros [X|X] H Y; lia. Qed.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.

Theorem vec_clear_ok : PMBX.ann_shrink_spec L ar HI -> PMBX.vec_clear_spec L ar HI.
Proof.
  intros ASH. unfold PMBX.vec_clear_spec, PMSBX.vec_clear_spec_at.
  intros fx R M model K LBX FF LK Aw cr v b k stk sp r HH AM K0 ENT FRS A10 AOV V8 ACCV VEC KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  pose proof VEC as (VB & VE & VC & Kr & LENk & B16 & BDEF & BACC & BANN & BST).
  set (len := Z.of_nat (length stk)) in *.
  set (LB := PM.vec_own b k ++ LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  assert (BIN : In (b, 32 * 2 ^ k) LB) by (left; reflexivity).
  destruct (PMBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (32 * 2 ^ k) HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & Bq5 & Bq6 & _ & Bq8).
  pose proof (PMESHK.pow2k k Kr) as P2K.
  pose proof (PMKB.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity))
    as ((Ov1 & Ov2 & Ov3 & Ov4 & Ov5) & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (OVN : nsh v 24) by (unfold nsh; destruct OBIG as [X|X]; [right| left]; lia).
  assert (OPS : v + 24 + 12288 <= sp - 4096) by (clear - Ov2 SLO; lia).
  assert (X0 : L5.img_clear MV 1273856 1306624) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1335544 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1335544 2147450880 (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1335552 1) by (apply (proj2 (L5A.u32_at_vis H M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) (b + 32 * len)) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) (b + 32 * 2 ^ k)) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).
  assert (X9 : L5.writable RSEGS MV (v + 8) 8).
  { apply (proj2 (L5A.writable_vis H M (v + 8) 8 (L5A.avis_sub H v 24 (v + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M v 24); [exact ODEF| lia| lia]| lia| lia]. }
  assert (Q1 : 0 <= sp < 2 ^ 64) by lia.
  assert (Q2 : 0 <= v < 2 ^ 64) by lia.
  assert (Q3 : 0 <= b < 2 ^ 64) by lia.
  assert (Q4 : 0 <= b + 32 * 2 ^ k < 2 ^ 64) by lia.
  assert (Q5 : 0 <= 32 * len <= 65536) by lia.

  assert (RUN1 : exists fx1 R1 M1v, mem_grows MV M1v
     /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 16 <= i < sp - 16 + 16) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
     /\ msteps RSEGS (st fx R 0xaa888 MV) (st fx1 R1 0xaa8e4 M1v)
     /\ (forall x, In x KEEP1 -> getr R1 (reg x) = getr R (reg x))
     /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 16) /\ getr R1 (reg 12) = Z_to_bv 64 (((v + 8) / 8) + 2147450880)
     /\ getr R1 (reg 13) = Z_to_bv 64 b /\ getr R1 (reg 14) = Z_to_bv 64 (b + 32 * len)
     /\ L5.u64_at RSEGS M1v (sp - 8) (bv_unsigned (getr R (reg 1)))).
  { destruct (Nat.eq_dec (length stk) 0) as [L0|L0].
    - assert (E0 : len = 0) by (unfold len; rewrite L0; reflexivity). rewrite E0 in X7 |- *. replace (b + 32 * 0) with b in X7 |- * by lia.
      pose proof (PMBVCP.bvcA0_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 41%nat => b + 32 * 2 ^ k | _ => 0 end)) as P.
      cbn beta iota in P.
      L5SAR.feed P ltac:(first [assumption | unfold PMBVCP.aligned; lia | lia]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR2 & fR11 & fR12 & fR13 & fR14 & SV8).
      exists fx1, R1, M1v. split; [exact MG1|]. split; [exact FZ1|]. split; [exact MS1|]. split.
      + intros x Hx. repeat (destruct Hx as [<-|Hx]; [apply KS1; inl|]). destruct Hx.
      + split; [exact fR2|]. split; [exact fR12|]. split; [exact fR13|]. split; [exact fR14| exact SV8].
    - assert (LP : (0 < length stk)%nat) by lia.
      pose proof (PMBVCP.bvcAn_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 37%nat => 32 * len
                                                  | 41%nat => b + 32 * 2 ^ k | _ => 0 end)) as P.
      cbn beta iota in P.
      L5SAR.feed P ltac:(first [assumption | unfold PMBVCP.aligned; lia | lia]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR2 & fR11 & fR12 & fR13 & fR14 & fR15 & fR16 & SV8).
      destruct (length stk) as [|n] eqn:EL; [lia|].
      destruct (loop_run M1v (sp - 16) b ltac:(lia) ltac:(lia) n fx1 R1 ltac:(unfold len in *; lia) fR2 fR13 fR15
                  ltac:(rewrite fR16; f_equal; unfold len; lia)) as (fx2 & R2 & MS2 & KS2).
      exists fx2, R2, M1v. split; [exact MG1|]. split; [exact FZ1|]. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split.
      + intros x Hx. rewrite (KS2 x) by (revert Hx; clear; intros Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx).
        repeat (destruct Hx as [<-|Hx]; [apply KS1; inl|]). destruct Hx.
      + split; [rewrite (KS2 2%nat) by inl; exact fR2|]. split; [rewrite (KS2 12%nat) by inl; exact fR12|].
        split; [rewrite (KS2 13%nat) by inl; exact fR13|]. split; [rewrite (KS2 14%nat) by inl; exact fR14| exact SV8]. }
  destruct RUN1 as (fx1 & R1 & M1v & MG1 & FZ1 & MS1 & KS1 & R1_2 & R1_12 & R1_13 & R1_14 & SV8).

  assert (ZV1 : L5KA.zeros_at M1v (v / 8 + 2147450880) 3).
  { intros i Hi. rewrite FZ1 by lia. apply X5. exact Hi. }
  pose proof (PMBVCP.bvcZ1_conc fx1 R1 M1v (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 37%nat => 32 * len | _ => 0 end)) as P.
  cbn beta iota in P.
  assert (Y10 : getr R1 (reg 10) = Z_to_bv 64 v) by (rewrite (KS1 10%nat) by inl; exact A10).
  L5SAR.feed P ltac:(first [assumption | unfold PMBVCP.aligned; lia | lia]).
  destruct P as (fx2 & R2 & M2v & _ & FR2w & _ & MS2 & KS2 & fZ11 & fZ12).
  assert (E2 : M2v = M1v) by (apply functional_extensionality; exact FR2w). subst M2v.
  pose proof (PMBRS1.srai_to fx2 R2 M1v 0xaa8f0 W_aa8a0 _ _ _ F_aa8a0 eq_refl D_aa8a0 eq_refl ltac:(lia) ltac:(lia)) as MSR.
  set (R2t := regupd R2 11%bv (v_srai (getr R2 11%bv) (bv_unsigned (5%bv : bv 6)))) in MSR.
  assert (R11 : (11%bv : bv 5) <> 0%bv) by (intros X; discriminate X).
  assert (E11 : getr R2 11%bv = Z_to_bv 64 (32 * len)) by (rewrite L5K.rl11, fZ11; reflexivity).
  assert (T11 : getr R2t (reg 11) = Z_to_bv 64 len).
  { unfold R2t. rewrite <- L5K.rl11. rewrite (getr_same R2 11%bv _ R11). rewrite E11. change (bv_unsigned (5%bv : bv 6)) with 5.
    rewrite PMBRS1.v_srai5_small by lia. f_equal. rewrite Z.mul_comm. apply Z.div_mul. lia. }
  assert (TO : forall j, j <> 11%nat -> (j < 32)%nat -> getr R2t (reg j) = getr R2 (reg j)).
  { intros j Hj Hl. unfold R2t. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
    rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (11%bv : bv 5)) with 11 in E.
    rewrite Z.mod_small in E by lia. lia. }
  pose proof (PMBVCP.bvcZ2_conc fx2 R2t M1v (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 43%nat => bv_unsigned (getr R (reg 1)) | _ => 0 end)) as P.
  cbn beta iota in P.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as Hs1. change (bv_modulus 64) with (2 ^ 64) in Hs1.
  assert (U2 : getr R2t (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite (TO 2%nat) by lia; rewrite (KS2 2%nat) by inl; exact R1_2).
  assert (U10 : getr R2t (reg 10) = Z_to_bv 64 v) by (rewrite (TO 10%nat) by lia; rewrite (KS2 10%nat) by inl; exact Y10).
  assert (U13 : getr R2t (reg 13) = Z_to_bv 64 b) by (rewrite (TO 13%nat) by lia; rewrite (KS2 13%nat) by inl; exact R1_13).
  assert (U3 : L5.writable RSEGS M1v (sp - 4096) 4096) by exact (L5.writable_grows RSEGS MV M1v (sp - 4096) 4096 MG1 X3).
  assert (U9 : L5.writable RSEGS M1v (v + 8) 8) by exact (L5.writable_grows RSEGS MV M1v (v + 8) 8 MG1 X9).
  L5SAR.feed P ltac:(first [assumption | unfold PMBVCP.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & fR1 & fR2 & C8).
  unfold PMSPA.cfg.
  set (P1 := fun a => (sp - 16 <= a < sp - 16 + 16) \/ (v + 8 <= a < v + 8 + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx3 R 0xaa888 R3 0xaa9d8 M3v P1 K HH AM).
  { eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MSR| exact MS3]]]. }
  { exact (mem_grows_trans _ _ _ MG1 MG3). }
  { intros a Ha Hnw. rewrite FZ3; [| exact Ha| intros X; apply Hnw; right; exact X]. apply FZ1; [exact Ha| intros X; apply Hnw; left; exact X]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|X]; unfold aclientw, aclient_g.
      + right; left. split; [lia| intros Y; lia].
      + do 3 right; left. destruct AOV as (f & Hf & Y1 & Y2). exists f. split; [exact Hf|]. split; [lia| intros Y; lia].
    - destruct Wa as [X|X]; lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M3v) in VIS1.

  assert (P1sh : forall x, BIGSHADOW_LO <= x < BIGSHADOW_HI -> ~ P1 x).
  { intros x Hx [Y|Y]; [clear - Hx Y SLO SPT; unfold BIGSHADOW_LO, BIGSHADOW_HI in Hx; lia| exact (nsh_not v 24 x OVN ltac:(lia) Hx)]. }
  assert (SHM1 : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
  { intros a n Ha Hn x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. apply FR1; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| apply P1sh; exact SX]. }
  assert (SZ1 : shadow_zero M1 (sp - 12288) 1536).
  { intros j Hj. pose proof (STKSH j Hj) as Z1. unfold byte_at in *. rewrite (PMFA.S_granule (sp - 12288) j ltac:(apply PMKB.mod16_8'; replace (sp - 12288) with (sp + (-768) * 16) by lia; rewrite Z_mod_plus_full; exact A16) ltac:(lia)) in *.
    pose proof (PMKB.S_in_shadow (sp - 12288 + 8 * j) ltac:(lia)) as SX. rewrite FR1; [exact Z1| unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| apply P1sh; exact SX]. }
  assert (ASTK1 : L5CA.astk ar M1 sp 12288) by exact (L5SAR.astk_grows ar M M1 sp 12288 ASTK MGM1).

  unfold PMBX.ann_shrink_spec, PMSBX.ann_shrink_spec_at in ASH.
  apply (ASH fx3 R3 M1 model1 K LBX FF LK Aw cr v b k len [] sp r HH1 AM1 K0).
  { split; [rewrite L5K.rl1, fR1, Z_to_bv_bv_unsigned; exact Rra|]. split; [exact RAok|].
    split; [rewrite L5K.rl2; exact fR2|].
    split; [rewrite L5K.rl3, (KS3 3%nat) by inl; rewrite (TO 3%nat) by lia; rewrite (KS2 3%nat) by inl; rewrite (KS1 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS3 4%nat) by inl; rewrite (TO 4%nat) by lia; rewrite (KS2 4%nat) by inl; rewrite (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK1|]. change (12288 / 8) with 1536. exact SZ1. }
  { exact FRS. }
  { rewrite L5K.rl10, (KS3 10%nat) by inl. exact U10. }
  { rewrite L5K.rl11, (KS3 11%nat) by inl. exact T11. }
  { exact AOV. }
  { exact V8. }
  { apply (PMFA.accA_agree M M1); [apply SHM1; lia| exact ACCV]. }
  { cbn [length]. lia. }
  { apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; [lia| intros [Y|Y]; lia]| lia| lia| exact VB]. }
  { cbn [length]. replace (b + 32 * Z.of_nat 0) with b by lia.
    apply (proj1 (L5A.u64_at_vis H M1 (v + 8) b (L5A.avis_sub H v 24 (v + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact C8. }
  { apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; [lia| intros [Y|Y]; lia]| lia| lia| exact VC]. }
  { lia. }
  { exact B16. }
  { intros i Hi. apply MGM1. apply BDEF. exact Hi. }
  { apply (PMFA.accA_agree M M1); [apply SHM1; lia| exact BACC]. }
  { apply (PMFA.annA_agree M M1); [apply PMKB.mod16_8'; exact B16| lia| |apply SHM1; lia| exact BANN].
    replace (32 * 2 ^ k) with ((4 * 2 ^ k) * 8) by lia. apply Z_mod_mult. }
  { intros i Hi. cbn [length] in Hi. lia. }
  intros fx4 R4 M4 model4 LK4 Aw4 RP4 VEC4 ACC4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
  change (PMSPA.pm_scr 0) with 12288 in HP4.
  set (Wv8 := [(v + 8, 8)]).
  assert (EK01 : L5SAR.ek L ar LBX FF sp 12288 Wv8 M M1).
  { apply (L5SAR.ek_piece L ar LBX FF sp 12288 Wv8 M M1 P1 FR1). intros a Ha Hc Ho [X|X].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M1 _ sp 12288 a HH1 SPT (L5SAR.aclient_appb L ar LBX (PM.vec_own b k) FF sp 12288 a Hc))
        as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
    - apply (Ho (v + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (EK14 : L5SAR.ek L ar LBX FF sp 12288 Wv8 M1 M4).
  { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 12288 sp 12288 Wv8 [] M1 M4 HP4); [lia| lia| intros a _ _ r0 []]. }
  apply (KONT fx4 R4 M4 model4 LK4 Aw4).
  - apply (L5SAR.regs_preserved_trans R R3 R4); [| exact RP4].
    apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj];
      [ first [ rewrite fR2; exact (eq_sym Rsp)
              | rewrite (KS3 _) by inl; rewrite TO by lia; rewrite (KS2 _) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
    destruct Hj.
  - exact VEC4.
  - exact ACC4.
  - change (PMSPA.pm_scr 0) with 12288.
    apply (L5SAR.ahpres_of L ar LBX FF sp 12288 Wv8 M M4).
    + exact (L5SAR.ek_trans L ar LBX FF sp 12288 Wv8 M M1 M4 EK01 EK14).
    + pose proof (PMKB.astk_after_ahpres L ar LBX FF M1 M4 sp 12288 sp 12288 [] ASTK1 HP4 ltac:(lia) ltac:(lia) ltac:(lia) STOP) as (_ & _ & _ & _ & D4 & _). exact D4.
    + apply (L5SAR.dk_trans L ar LBX FF sp 12288 M M1 M4); [apply L5SAR.dk_grows; exact MGM1|].
      apply (L5SAR.dk_callee L ar LBX [] FF [] sp 12288 sp 12288 [] M1 M4 HP4); lia.
  - apply (L5LZ.model_rt_trans model model1 model4); [exact MRT1| exact MRT4].
  - exact INCLK4.
  - exact INCAw4.
  - exact AM4.
  - exact HH4.
Qed.
End Stage.
End PMBVC.
