(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRecs LeptSel LeptRoom LeptExec LeptExecW LeptExecT LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptDilW V23LeptCloseIface V23LeptSelDA V23LeptSelDC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptCloseIface O23LeptSelDW.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SelDW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma sdw_bounds : forall C A m md sel sv, Cok C -> W C A m md -> sel_at (alloc_top (c_vm C)) A m sel sv ->
  (0 <= sel < 2 ^ 64)%Z /\ (0 <= v_data sv < 2 ^ 64)%Z /\
  rdn SEGS m (Z_to_bv 64 (sel + 0)) 4 = Some (Z_to_le_bytes 4 (v_sy sv)) /\
  rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 (v_data sv)) /\
  rdn SEGS m (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 (v_name sv)).
Proof.
  intros C A m md sel sv CK HW SA.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as Usp. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct SA as (Hsy & Hsx & Bs & Ls & RC & Bd & Ld & NEds & HR & HD).
  destruct Bs as (Bs1 & Bs2 & Bs3). destruct Bd as (Bd1 & Bd2 & Bd3).
  split; [lia|]. split; [lia|].
  split; [exact (REC_rd' SEGS _ sel _ 0 4 (Z_to_bv 64 (sel + 0)) (v_sy sv) RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl)|].
  split; [exact (REC_rd' SEGS _ sel _ 4 8 (Z_to_bv 64 (sel + 16)) (v_data sv) RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl)|].
  exact (REC_rd' SEGS _ sel _ 5 8 (Z_to_bv 64 (sel + 24)) (v_name sv) RC ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl).
Qed.

Lemma sdw_row : forall C A m md sel sv i, Cok C -> W C A m md -> sel_at (alloc_top (c_vm C)) A m sel sv -> (0 <= i < v_sy sv)%Z ->
  rdn SEGS m (Z_to_bv 64 (v_data sv + 8 * i)) 8 = Some (Z_to_le_bytes 8 (v_rows sv i)) /\
  live A (Z_to_bv 64 (v_rows sv i)) = Some (4 * v_sx sv)%Z /\ (0 <= v_rows sv i < 2 ^ 64)%Z /\
  Z_to_bv 64 sel <> Z_to_bv 64 (v_rows sv i) /\ Z_to_bv 64 (v_data sv) <> Z_to_bv 64 (v_rows sv i).
Proof.
  intros C A m md sel sv i CK HW SA Hi.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof (u64_range (c_sp0 C)) as Usp. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct SA as (Hsy & Hsx & Bs & Ls & RC & Bd & Ld & NEds & HR & HD).
  destruct Bs as (Bs1 & Bs2 & Bs3). destruct Bd as (Bd1 & Bd2 & Bd3).
  destruct (HR i Hi) as (Br & Lr & NErd & NErs & BA). destruct Br as (Br1 & Br2 & Br3).
  split; [|split; [exact Lr|split; [lia|split]]].
  - pose proof (bytes_at_rdn SEGS m (v_data sv + 8 * i) (Z_to_le_bytes 8 (v_rows sv i)) ltac:(lia)
      ltac:(rewrite length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) BA) as R.
    rewrite length_Z_to_le_bytes in R. exact R.
  - apply O23LeptSelDW.sd_zne; [lia | lia | intros E; apply NErs; symmetry; exact E].
  - apply O23LeptSelDW.sd_zne; [lia | lia | intros E; apply NErd; symmetry; exact E].
Qed.

Lemma sdw_only : forall (A A' : AS) sel sv (l : list word),
  (forall q, ~ In q l -> live A' q = live A q) ->
  (forall q, In q l -> exists p, sel_blk sel sv p /\ q = Z_to_bv 64 p) ->
  forall q, (forall p, sel_blk sel sv p -> q <> Z_to_bv 64 p) -> live A' q = live A q.
Proof.
  intros A A' sel sv l H1 H2 q Hq. apply H1. intros Hin. destruct (H2 q Hin) as (p & Hp & ->). exact (Hq p Hp eq_refl).
Qed.

Theorem selDestroy_W : selDestroy_contract.
Proof.
  unfold selDestroy_contract.
  intros C A m md regs s psel sel sv ret S CK HW H2 Hs16 Hlo Hsp Hph Hpal H1 Hret H4 H10 Mp SA Hnm Hsy F0 HC.
  assert (HloW : (c_top C - LSTK + O23LeptSelDC.SELD_WIN <= s)%Z) by (unfold O23LeptSelDC.SELD_WIN, O23LeptCloseIface.SELD_STACK, ALLOC_STACK in *; lia).
  assert (Mp0 : rdn SEGS m (Z_to_bv 64 (psel + 0)) 8 = Some (Z_to_le_bytes 8 sel)) by (rewrite Z.add_0_r; exact Mp).
  destruct (sdw_bounds C A m md sel sv CK HW SA) as (Rs & Rd & Msy & Mdat & Mnm). rewrite Hnm in Mnm.
  pose proof SA as (_ & _ & _ & Lsel & _ & _ & Ldat & NEds & _ & HD).
  pose proof (F0 sel (or_introl eq_refl)) as F0s.
  pose proof (F0 (v_data sv) (or_intror (or_introl eq_refl))) as F0d.
  assert (NE_sd : Z_to_bv 64 sel <> Z_to_bv 64 (v_data sv)) by (apply O23LeptSelDW.sd_zne; [lia | lia | intros E; apply NEds; symmetry; exact E]).
  lazymatch goal with |- realizes _ (mkCfg (@mkst _ _ ?pc _ _) _) _ => replace pc with (Z_to_bv 64 0xa4c74) by (apply bv_eq; reflexivity) end.
  destruct Hsy as [Hk | [Hk | [Hk | Hk]]].
  - rewrite Hk in Msy, Ldat.
    destruct (sdw_row C A m md sel sv 0%Z CK HW SA ltac:(lia)) as (Mr0 & Lr0 & Rr0 & NEsr0 & NEdr0).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 0%Z 1%Z Hk ltac:(lia))) as F0r0.
    apply (seld_chain1 fx C A m md regs s psel sel (v_data sv) (v_rows sv 0%Z) (4 * v_sx sv) ret S CK HW H2 Hs16 HloW Hsp Hph Hpal H1 Hret H4 H10
             Mp0 Msy Mdat Mnm Mr0 Lsel F0s Rs Ldat F0d Rd Lr0 F0r0 Rr0
             NE_sd NEsr0 NEdr0).
    intros A' m' vm' regs' HW' CS Dsel Ddat Dr0 LDEL PM Cp BET RT.
    apply (HC A' m' vm' regs' HW' CS).
    + intros p Hp. destruct Hp as [-> | [-> | (i & Hi & ->)]]; [exact Dsel | exact Ddat |]. rewrite Hk in Hi.
      assert (Ei : i = 0%Z) by lia. subst i. assumption.
    + apply (sdw_only A A' sel sv _ LDEL). intros q Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [first [exists sel; split; [left; reflexivity | reflexivity] | exists (v_data sv); split; [right; left; reflexivity | reflexivity] | exists (v_rows sv 0%Z); split; [right; right; exists 0%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity]] |]). destruct Hin.
    + exact PM.
    + rewrite Z.add_0_r in Cp. exact Cp.
    + exact BET.
    + exact RT.
  - rewrite Hk in Msy, Ldat.
    destruct (sdw_row C A m md sel sv 0%Z CK HW SA ltac:(lia)) as (Mr0 & Lr0 & Rr0 & NEsr0 & NEdr0).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 0%Z 4%Z Hk ltac:(lia))) as F0r0.
    destruct (sdw_row C A m md sel sv 1%Z CK HW SA ltac:(lia)) as (Mr1 & Lr1 & Rr1 & NEsr1 & NEdr1).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 1%Z 4%Z Hk ltac:(lia))) as F0r1.
    destruct (sdw_row C A m md sel sv 2%Z CK HW SA ltac:(lia)) as (Mr2 & Lr2 & Rr2 & NEsr2 & NEdr2).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 2%Z 4%Z Hk ltac:(lia))) as F0r2.
    destruct (sdw_row C A m md sel sv 3%Z CK HW SA ltac:(lia)) as (Mr3 & Lr3 & Rr3 & NEsr3 & NEdr3).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 3%Z 4%Z Hk ltac:(lia))) as F0r3.
    assert (NErr0_1 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 1%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 1%Z); lia]).
    assert (NErr0_2 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 2%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 2%Z); lia]).
    assert (NErr1_2 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 2%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 2%Z); lia]).
    assert (NErr0_3 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 3%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 3%Z); lia]).
    assert (NErr1_3 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 3%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 3%Z); lia]).
    assert (NErr2_3 : Z_to_bv 64 (v_rows sv 2%Z) <> Z_to_bv 64 (v_rows sv 3%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 2%Z 3%Z); lia]).
    apply (seld_chain4 fx C A m md regs s psel sel (v_data sv) (v_rows sv 0%Z) (v_rows sv 1%Z) (v_rows sv 2%Z) (v_rows sv 3%Z) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) ret S CK HW H2 Hs16 HloW Hsp Hph Hpal H1 Hret H4 H10
             Mp0 Msy Mdat Mnm Mr0 Mr1 Mr2 Mr3 Lsel F0s Rs Ldat F0d Rd Lr0 F0r0 Rr0 Lr1 F0r1 Rr1 Lr2 F0r2 Rr2 Lr3 F0r3 Rr3
             NE_sd NEsr0 NEdr0 NEsr1 NEdr1 NErr0_1 NEsr2 NEdr2 NErr0_2 NErr1_2 NEsr3 NEdr3 NErr0_3 NErr1_3 NErr2_3).
    intros A' m' vm' regs' HW' CS Dsel Ddat Dr0 Dr1 Dr2 Dr3 LDEL PM Cp BET RT.
    apply (HC A' m' vm' regs' HW' CS).
    + intros p Hp. destruct Hp as [-> | [-> | (i & Hi & ->)]]; [exact Dsel | exact Ddat |]. rewrite Hk in Hi.
      assert (Ei : i = 0%Z \/ i = 1%Z \/ i = 2%Z \/ i = 3%Z) by lia. destruct Ei as [->|[->|[->| ->]]]; assumption.
    + apply (sdw_only A A' sel sv _ LDEL). intros q Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [first [exists sel; split; [left; reflexivity | reflexivity] | exists (v_data sv); split; [right; left; reflexivity | reflexivity] | exists (v_rows sv 0%Z); split; [right; right; exists 0%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 1%Z); split; [right; right; exists 1%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 2%Z); split; [right; right; exists 2%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 3%Z); split; [right; right; exists 3%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity]] |]). destruct Hin.
    + exact PM.
    + rewrite Z.add_0_r in Cp. exact Cp.
    + exact BET.
    + exact RT.
  - rewrite Hk in Msy, Ldat.
    destruct (sdw_row C A m md sel sv 0%Z CK HW SA ltac:(lia)) as (Mr0 & Lr0 & Rr0 & NEsr0 & NEdr0).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 0%Z 5%Z Hk ltac:(lia))) as F0r0.
    destruct (sdw_row C A m md sel sv 1%Z CK HW SA ltac:(lia)) as (Mr1 & Lr1 & Rr1 & NEsr1 & NEdr1).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 1%Z 5%Z Hk ltac:(lia))) as F0r1.
    destruct (sdw_row C A m md sel sv 2%Z CK HW SA ltac:(lia)) as (Mr2 & Lr2 & Rr2 & NEsr2 & NEdr2).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 2%Z 5%Z Hk ltac:(lia))) as F0r2.
    destruct (sdw_row C A m md sel sv 3%Z CK HW SA ltac:(lia)) as (Mr3 & Lr3 & Rr3 & NEsr3 & NEdr3).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 3%Z 5%Z Hk ltac:(lia))) as F0r3.
    destruct (sdw_row C A m md sel sv 4%Z CK HW SA ltac:(lia)) as (Mr4 & Lr4 & Rr4 & NEsr4 & NEdr4).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 4%Z 5%Z Hk ltac:(lia))) as F0r4.
    assert (NErr0_1 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 1%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 1%Z); lia]).
    assert (NErr0_2 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 2%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 2%Z); lia]).
    assert (NErr1_2 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 2%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 2%Z); lia]).
    assert (NErr0_3 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 3%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 3%Z); lia]).
    assert (NErr1_3 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 3%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 3%Z); lia]).
    assert (NErr2_3 : Z_to_bv 64 (v_rows sv 2%Z) <> Z_to_bv 64 (v_rows sv 3%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 2%Z 3%Z); lia]).
    assert (NErr0_4 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 4%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 4%Z); lia]).
    assert (NErr1_4 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 4%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 4%Z); lia]).
    assert (NErr2_4 : Z_to_bv 64 (v_rows sv 2%Z) <> Z_to_bv 64 (v_rows sv 4%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 2%Z 4%Z); lia]).
    assert (NErr3_4 : Z_to_bv 64 (v_rows sv 3%Z) <> Z_to_bv 64 (v_rows sv 4%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 3%Z 4%Z); lia]).
    apply (seld_chain5 fx C A m md regs s psel sel (v_data sv) (v_rows sv 0%Z) (v_rows sv 1%Z) (v_rows sv 2%Z) (v_rows sv 3%Z) (v_rows sv 4%Z) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) ret S CK HW H2 Hs16 HloW Hsp Hph Hpal H1 Hret H4 H10
             Mp0 Msy Mdat Mnm Mr0 Mr1 Mr2 Mr3 Mr4 Lsel F0s Rs Ldat F0d Rd Lr0 F0r0 Rr0 Lr1 F0r1 Rr1 Lr2 F0r2 Rr2 Lr3 F0r3 Rr3 Lr4 F0r4 Rr4
             NE_sd NEsr0 NEdr0 NEsr1 NEdr1 NErr0_1 NEsr2 NEdr2 NErr0_2 NErr1_2 NEsr3 NEdr3 NErr0_3 NErr1_3 NErr2_3 NEsr4 NEdr4 NErr0_4 NErr1_4 NErr2_4 NErr3_4).
    intros A' m' vm' regs' HW' CS Dsel Ddat Dr0 Dr1 Dr2 Dr3 Dr4 LDEL PM Cp BET RT.
    apply (HC A' m' vm' regs' HW' CS).
    + intros p Hp. destruct Hp as [-> | [-> | (i & Hi & ->)]]; [exact Dsel | exact Ddat |]. rewrite Hk in Hi.
      assert (Ei : i = 0%Z \/ i = 1%Z \/ i = 2%Z \/ i = 3%Z \/ i = 4%Z) by lia. destruct Ei as [->|[->|[->|[->| ->]]]]; assumption.
    + apply (sdw_only A A' sel sv _ LDEL). intros q Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [first [exists sel; split; [left; reflexivity | reflexivity] | exists (v_data sv); split; [right; left; reflexivity | reflexivity] | exists (v_rows sv 0%Z); split; [right; right; exists 0%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 1%Z); split; [right; right; exists 1%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 2%Z); split; [right; right; exists 2%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 3%Z); split; [right; right; exists 3%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 4%Z); split; [right; right; exists 4%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity]] |]). destruct Hin.
    + exact PM.
    + rewrite Z.add_0_r in Cp. exact Cp.
    + exact BET.
    + exact RT.
  - rewrite Hk in Msy, Ldat.
    destruct (sdw_row C A m md sel sv 0%Z CK HW SA ltac:(lia)) as (Mr0 & Lr0 & Rr0 & NEsr0 & NEdr0).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 0%Z 8%Z Hk ltac:(lia))) as F0r0.
    destruct (sdw_row C A m md sel sv 1%Z CK HW SA ltac:(lia)) as (Mr1 & Lr1 & Rr1 & NEsr1 & NEdr1).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 1%Z 8%Z Hk ltac:(lia))) as F0r1.
    destruct (sdw_row C A m md sel sv 2%Z CK HW SA ltac:(lia)) as (Mr2 & Lr2 & Rr2 & NEsr2 & NEdr2).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 2%Z 8%Z Hk ltac:(lia))) as F0r2.
    destruct (sdw_row C A m md sel sv 3%Z CK HW SA ltac:(lia)) as (Mr3 & Lr3 & Rr3 & NEsr3 & NEdr3).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 3%Z 8%Z Hk ltac:(lia))) as F0r3.
    destruct (sdw_row C A m md sel sv 4%Z CK HW SA ltac:(lia)) as (Mr4 & Lr4 & Rr4 & NEsr4 & NEdr4).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 4%Z 8%Z Hk ltac:(lia))) as F0r4.
    destruct (sdw_row C A m md sel sv 5%Z CK HW SA ltac:(lia)) as (Mr5 & Lr5 & Rr5 & NEsr5 & NEdr5).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 5%Z 8%Z Hk ltac:(lia))) as F0r5.
    destruct (sdw_row C A m md sel sv 6%Z CK HW SA ltac:(lia)) as (Mr6 & Lr6 & Rr6 & NEsr6 & NEdr6).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 6%Z 8%Z Hk ltac:(lia))) as F0r6.
    destruct (sdw_row C A m md sel sv 7%Z CK HW SA ltac:(lia)) as (Mr7 & Lr7 & Rr7 & NEsr7 & NEdr7).
    pose proof (F0 _ (O23LeptSelDW.sd_row sel sv 7%Z 8%Z Hk ltac:(lia))) as F0r7.
    assert (NErr0_1 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 1%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 1%Z); lia]).
    assert (NErr0_2 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 2%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 2%Z); lia]).
    assert (NErr1_2 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 2%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 2%Z); lia]).
    assert (NErr0_3 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 3%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 3%Z); lia]).
    assert (NErr1_3 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 3%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 3%Z); lia]).
    assert (NErr2_3 : Z_to_bv 64 (v_rows sv 2%Z) <> Z_to_bv 64 (v_rows sv 3%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 2%Z 3%Z); lia]).
    assert (NErr0_4 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 4%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 4%Z); lia]).
    assert (NErr1_4 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 4%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 4%Z); lia]).
    assert (NErr2_4 : Z_to_bv 64 (v_rows sv 2%Z) <> Z_to_bv 64 (v_rows sv 4%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 2%Z 4%Z); lia]).
    assert (NErr3_4 : Z_to_bv 64 (v_rows sv 3%Z) <> Z_to_bv 64 (v_rows sv 4%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 3%Z 4%Z); lia]).
    assert (NErr0_5 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 5%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 5%Z); lia]).
    assert (NErr1_5 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 5%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 5%Z); lia]).
    assert (NErr2_5 : Z_to_bv 64 (v_rows sv 2%Z) <> Z_to_bv 64 (v_rows sv 5%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 2%Z 5%Z); lia]).
    assert (NErr3_5 : Z_to_bv 64 (v_rows sv 3%Z) <> Z_to_bv 64 (v_rows sv 5%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 3%Z 5%Z); lia]).
    assert (NErr4_5 : Z_to_bv 64 (v_rows sv 4%Z) <> Z_to_bv 64 (v_rows sv 5%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 4%Z 5%Z); lia]).
    assert (NErr0_6 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 6%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 6%Z); lia]).
    assert (NErr1_6 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 6%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 6%Z); lia]).
    assert (NErr2_6 : Z_to_bv 64 (v_rows sv 2%Z) <> Z_to_bv 64 (v_rows sv 6%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 2%Z 6%Z); lia]).
    assert (NErr3_6 : Z_to_bv 64 (v_rows sv 3%Z) <> Z_to_bv 64 (v_rows sv 6%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 3%Z 6%Z); lia]).
    assert (NErr4_6 : Z_to_bv 64 (v_rows sv 4%Z) <> Z_to_bv 64 (v_rows sv 6%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 4%Z 6%Z); lia]).
    assert (NErr5_6 : Z_to_bv 64 (v_rows sv 5%Z) <> Z_to_bv 64 (v_rows sv 6%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 5%Z 6%Z); lia]).
    assert (NErr0_7 : Z_to_bv 64 (v_rows sv 0%Z) <> Z_to_bv 64 (v_rows sv 7%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 0%Z 7%Z); lia]).
    assert (NErr1_7 : Z_to_bv 64 (v_rows sv 1%Z) <> Z_to_bv 64 (v_rows sv 7%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 1%Z 7%Z); lia]).
    assert (NErr2_7 : Z_to_bv 64 (v_rows sv 2%Z) <> Z_to_bv 64 (v_rows sv 7%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 2%Z 7%Z); lia]).
    assert (NErr3_7 : Z_to_bv 64 (v_rows sv 3%Z) <> Z_to_bv 64 (v_rows sv 7%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 3%Z 7%Z); lia]).
    assert (NErr4_7 : Z_to_bv 64 (v_rows sv 4%Z) <> Z_to_bv 64 (v_rows sv 7%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 4%Z 7%Z); lia]).
    assert (NErr5_7 : Z_to_bv 64 (v_rows sv 5%Z) <> Z_to_bv 64 (v_rows sv 7%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 5%Z 7%Z); lia]).
    assert (NErr6_7 : Z_to_bv 64 (v_rows sv 6%Z) <> Z_to_bv 64 (v_rows sv 7%Z)) by (apply O23LeptSelDW.sd_zne; [lia | lia | apply (HD 6%Z 7%Z); lia]).
    apply (seld_chain8 fx C A m md regs s psel sel (v_data sv) (v_rows sv 0%Z) (v_rows sv 1%Z) (v_rows sv 2%Z) (v_rows sv 3%Z) (v_rows sv 4%Z) (v_rows sv 5%Z) (v_rows sv 6%Z) (v_rows sv 7%Z) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) (4 * v_sx sv) ret S CK HW H2 Hs16 HloW Hsp Hph Hpal H1 Hret H4 H10
             Mp0 Msy Mdat Mnm Mr0 Mr1 Mr2 Mr3 Mr4 Mr5 Mr6 Mr7 Lsel F0s Rs Ldat F0d Rd Lr0 F0r0 Rr0 Lr1 F0r1 Rr1 Lr2 F0r2 Rr2 Lr3 F0r3 Rr3 Lr4 F0r4 Rr4 Lr5 F0r5 Rr5 Lr6 F0r6 Rr6 Lr7 F0r7 Rr7
             NE_sd NEsr0 NEdr0 NEsr1 NEdr1 NErr0_1 NEsr2 NEdr2 NErr0_2 NErr1_2 NEsr3 NEdr3 NErr0_3 NErr1_3 NErr2_3 NEsr4 NEdr4 NErr0_4 NErr1_4 NErr2_4 NErr3_4 NEsr5 NEdr5 NErr0_5 NErr1_5 NErr2_5 NErr3_5 NErr4_5 NEsr6 NEdr6 NErr0_6 NErr1_6 NErr2_6 NErr3_6 NErr4_6 NErr5_6 NEsr7 NEdr7 NErr0_7 NErr1_7 NErr2_7 NErr3_7 NErr4_7 NErr5_7 NErr6_7).
    intros A' m' vm' regs' HW' CS Dsel Ddat Dr0 Dr1 Dr2 Dr3 Dr4 Dr5 Dr6 Dr7 LDEL PM Cp BET RT.
    apply (HC A' m' vm' regs' HW' CS).
    + intros p Hp. destruct Hp as [-> | [-> | (i & Hi & ->)]]; [exact Dsel | exact Ddat |]. rewrite Hk in Hi.
      assert (Ei : i = 0%Z \/ i = 1%Z \/ i = 2%Z \/ i = 3%Z \/ i = 4%Z \/ i = 5%Z \/ i = 6%Z \/ i = 7%Z) by lia. destruct Ei as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; assumption.
    + apply (sdw_only A A' sel sv _ LDEL). intros q Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [first [exists sel; split; [left; reflexivity | reflexivity] | exists (v_data sv); split; [right; left; reflexivity | reflexivity] | exists (v_rows sv 0%Z); split; [right; right; exists 0%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 1%Z); split; [right; right; exists 1%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 2%Z); split; [right; right; exists 2%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 3%Z); split; [right; right; exists 3%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 4%Z); split; [right; right; exists 4%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 5%Z); split; [right; right; exists 5%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 6%Z); split; [right; right; exists 6%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity] | exists (v_rows sv 7%Z); split; [right; right; exists 7%Z; split; [rewrite Hk; lia | reflexivity] | reflexivity]] |]). destruct Hin.
    + exact PM.
    + rewrite Z.add_0_r in Cp. exact Cp.
    + exact BET.
    + exact RT.
Qed.

Theorem selDestroy_null_W : selDestroy_null_contract.
Proof.
  unfold selDestroy_null_contract.
  intros C A m md regs s psel ret S CK HW H2 Hs16 Hlo Hsp Hph Hpal H1 Hret H10 Mp HC.
  lazymatch goal with |- realizes _ (mkCfg (@mkst _ _ ?pc _ _) _) _ => replace pc with (Z_to_bv 64 0xa4c74) by (apply bv_eq; reflexivity) end.
  apply (seld_null fx C A m md regs s psel ret S CK HW H2 Hs16 ltac:(unfold O23LeptSelDC.SELD_WIN, O23LeptCloseIface.SELD_STACK, ALLOC_STACK in *; lia) Hsp Hph Hpal H1 Hret H10 ltac:(rewrite Z.add_0_r; exact Mp) HC).
Qed.
End SelDW.
