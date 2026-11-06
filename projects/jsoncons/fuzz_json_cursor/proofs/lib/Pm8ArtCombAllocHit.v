(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac
     As0StepLib As0Tables ArtMem ArtAtomics ArtTac Pm8ArtClassId Pm8ArtCachePop Pm8ArtCombAlloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_ca_hit_mem (M : word -> option byte) (sp ra s0 s1 s2 s3 s4 ca c cnt st csz : Z) : word -> option byte :=
  Wn 8 (Wn 4 (art_ca_frame M sp ra s0 s1 s2 s3 s4) (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz).

Definition art_ca_kept (r : reg) : Prop :=
  r <> 5%bv /\ r <> 6%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv.

Lemma class_id_small : forall s, 1 <= s <= 512 -> AsanTab.class_id s = (s + 31) / 32.
Proof. intros s Hs. unfold AsanTab.class_id. replace (s <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Section FPX. Context {fx : PropExec.FPState}.

Theorem art_comb_alloc_hit8 :
  forall regs (M rom : word -> option byte) (raw : word) (sp s ca ia cnt csz ch st spb : Z),
  let c := AsanTab.class_id s in
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 ca ->
  getr regs 12 = Z_to_bv 64 s -> getr regs 13 = Z_to_bv 64 8 ->
  48 <= sp -> sp < 2 ^ 64 -> 1 <= s <= 65536 -> s mod 8 = 0 ->
  0 <= ca -> ca + 4096 < 2 ^ 64 -> ca mod 8 = 0 -> 0 <= ia -> ia + 4096 < 2 ^ 64 ->
  1 <= cnt <= 16 -> 0 <= csz < 2 ^ 64 -> 0 <= ch < 2 ^ 32 -> 0 <= st < 2 ^ 64 -> 0 <= spb < 2 ^ 64 ->
  wrA M (sp - 48) 48 ->
  cellA M (ca + 80 * c) 4 cnt -> cellA M (ca + 80 * c + 8) 8 csz -> cellA M (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch ->
  cellA M (ca + 2576) 8 st -> cellA M (ia + 32) 8 spb ->
  wokA M (ca + 80 * c) 4 -> wokA M (ca + 2576) 8 ->
  apart (sp - 48) 48 ca 2640 -> apart (sp - 48) 48 (ia + 32) 8 -> apart (ca + 80 * c) 4 (ia + 32) 8 -> apart (ca + 2576) 8 (ia + 32) 8 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5dbb4 : word) M rom)
                 (mkst regs' raw (art_ca_hit_mem M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18))
                                                    (U (getr regs 19)) (U (getr regs 20)) ca c cnt st csz) rom)
    /\ getr regs' 10 = Z_to_bv 64 (spb + c * 2 ^ 32 + ch * 16)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20
    /\ (forall r : reg, art_ca_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp s ca ia cnt csz ch st spb c H1 Hret H2 H10 H11 H12 H13 Hsp Hsp' Hs Hs8 Hca Hca' Hca8 Hia Hia'
         Hcnt Hcsz Hch Hst Hspb W Ccnt Ccsz Cch Cst Cspb Wcnt Wst ApF ApF2 Ap1 Ap2.
  pose proof (AsanTab.class_id_ok s ltac:(lia)) as (Hc & _ & _). fold c in Hc.

  destruct (art_ca_entry8 regs M rom sp s H2 H12 H13 Hsp Hsp' Hs W) as (r1 & RUN1 & Q2 & Q14 & Q12 & Q15 & K1).
  set (M1 := art_ca_frame M sp (U (getr regs 1)) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))) in RUN1.

  assert (STEP2 : exists r2, msteps ASEGS (mkst r1 (0x5dc38 : word) M1 rom) (mkst r2 (0x5dd48 : word) M1 rom)
            /\ getr r2 8 = Z_to_bv 64 c
            /\ (forall r : reg, r <> 8%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 5%bv -> r <> 6%bv ->
                  getr r2 r = getr r1 r)).
  { destruct (Z.le_gt_cases s 512) as [Hsm|Hbg].
    - destruct (art_ca_small r1 M1 rom s Q14 Q12 ltac:(lia)) as (r2 & RUN2 & P8 & _ & K2).
      exists r2. split; [exact RUN2|]. split.
      + rewrite P8. unfold c. rewrite class_id_small by lia. reflexivity.
      + intros r N8 N12 N14 N15 N16 N17 N5 N6. apply K2; assumption.
    - pose proof (art_ca_big r1 M1 rom s Q14 Q12 ltac:(lia)) as RUN2a.
      destruct (art_classid_hi_run r1 M1 rom (Z_to_bv 64 s) Q14) as (r2 & RUN2b & P8 & K2).
      exists r2. split; [eapply msteps_trans; [exact RUN2a | exact RUN2b]|]. split.
      + rewrite P8. rewrite art_cid_w_ok by lia. reflexivity.
      + intros r N8 N12 N14 N15 N16 N17 N5 N6. apply K2. unfold art_cid_kept. repeat split; assumption. }
  destruct STEP2 as (r2 & RUN2 & P8 & K2).

  assert (R2_11 : getr r2 11 = Z_to_bv 64 ca). { rewrite K2 by (intros E; discriminate E). rewrite K1 by (unfold art_ca_entry_kept; repeat split; intros E; discriminate E). exact H11. }
  assert (R2_10 : getr r2 10 = Z_to_bv 64 ia). { rewrite K2 by (intros E; discriminate E). rewrite K1 by (unfold art_ca_entry_kept; repeat split; intros E; discriminate E). exact H10. }
  assert (R2_13 : getr r2 13 = Z_to_bv 64 8). { rewrite K2 by (intros E; discriminate E). rewrite K1 by (unfold art_ca_entry_kept; repeat split; intros E; discriminate E). exact H13. }
  assert (R2_2 : getr r2 2 = Z_to_bv 64 (sp - 48)). { rewrite K2 by (intros E; discriminate E). exact Q2. }
  assert (R2_1 : getr r2 1 = raw). { rewrite K2 by (intros E; discriminate E). rewrite K1 by (unfold art_ca_entry_kept; repeat split; intros E; discriminate E). exact H1. }

  assert (Hc80 : 80 <= 80 * c <= 2480) by lia.
  assert (C1cnt : cellA M1 (ca + 80 * c) 4 cnt) by (unfold M1, art_ca_frame; unfold apart in *; recell Ccnt).
  assert (C1csz : cellA M1 (ca + 80 * c + 8) 8 csz) by (unfold M1, art_ca_frame; unfold apart in *; recell Ccsz).
  assert (C1ch : cellA M1 (ca + 80 * c + 16 + 4 * (cnt - 1)) 4 ch) by (unfold M1, art_ca_frame; unfold apart in *; recell Cch).
  assert (C1st : cellA M1 (ca + 2576) 8 st) by (unfold M1, art_ca_frame; unfold apart in *; recell Cst).
  assert (C1spb : cellA M1 (ia + 32) 8 spb) by (unfold M1, art_ca_frame; unfold apart in *; recell Cspb).
  assert (W1cnt : wokA M1 (ca + 80 * c) 4) by (unfold M1, art_ca_frame; rewok Wcnt).
  assert (W1st : wokA M1 (ca + 2576) 8) by (unfold M1, art_ca_frame; rewok Wst).

  destruct (art_cache_pop_core r2 M1 rom c ca ia cnt csz ch st spb P8 R2_11 R2_10 ltac:(lia) Hca Hca' Hca8 Hia Hia' Hcnt Hcsz Hch Hst Hspb
              C1cnt C1csz C1ch C1st C1spb W1cnt W1st Ap1 Ap2) as (r3 & RUN3 & P10 & K3).
  set (M3 := Wn 8 (Wn 4 M1 (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz)) in RUN3.
  assert (R3_13 : getr r3 13 = Z_to_bv 64 8) by (rewrite K3 by (intros E; discriminate E); exact R2_13).
  assert (R3_2 : getr r3 2 = Z_to_bv 64 (sp - 48)) by (rewrite K3 by (intros E; discriminate E); exact R2_2).

  assert (F40 : cellA M3 (sp - 48 + 40) 8 (U raw)).
  { unfold M3, M1, art_ca_frame. rewrite <- H1. replace (sp - 48 + 40) with (sp - 8) by lia. unfold apart in *.
    do 7 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]). apply cell_Wn_hit; lia. }
  assert (F32 : cellA M3 (sp - 48 + 32) 8 (U (getr regs 8))).
  { unfold M3, M1, art_ca_frame. replace (sp - 48 + 32) with (sp - 16) by lia. unfold apart in *.
    do 6 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]). apply cell_Wn_hit; lia. }
  assert (F24 : cellA M3 (sp - 48 + 24) 8 (U (getr regs 9))).
  { unfold M3, M1, art_ca_frame. replace (sp - 48 + 24) with (sp - 24) by lia. unfold apart in *.
    do 5 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]). apply cell_Wn_hit; lia. }
  assert (F16 : cellA M3 (sp - 48 + 16) 8 (U (getr regs 18))).
  { unfold M3, M1, art_ca_frame. replace (sp - 48 + 16) with (sp - 32) by lia. unfold apart in *.
    do 4 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]). apply cell_Wn_hit; lia. }
  assert (F8 : cellA M3 (sp - 48 + 8) 8 (U (getr regs 19))).
  { unfold M3, M1, art_ca_frame. replace (sp - 48 + 8) with (sp - 40) by lia. unfold apart in *.
    do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]). apply cell_Wn_hit; lia. }
  assert (F0 : cellA M3 (sp - 48) 8 (U (getr regs 20))).
  { unfold M3, M1, art_ca_frame. unfold apart in *.
    do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]). apply cell_Wn_hit; lia. }

  destruct (art_cache_pop_tail8 r3 M3 rom (sp - 48) raw (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))
              R3_13 R3_2 ltac:(lia) ltac:(lia) F40 Hret F32 F24 F16 F8 F0) as (r4 & RUN4 & T10 & T2 & T1 & T8 & T9 & T18 & T19 & T20 & K4).
  exists r4. split.
  { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4. }
  split. { rewrite T10. exact P10. }
  split. { rewrite T2. f_equal. lia. }
  split. { exact T1. }
  split. { rewrite T8. apply Z_to_bv_bv_unsigned. }
  split. { rewrite T9. apply Z_to_bv_bv_unsigned. }
  split. { rewrite T18. apply Z_to_bv_bv_unsigned. }
  split. { rewrite T19. apply Z_to_bv_bv_unsigned. }
  split. { rewrite T20. apply Z_to_bv_bv_unsigned. }
  intros r Hr. unfold art_ca_kept in Hr. destruct Hr as (N5 & N6 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17).
  destruct (decide (r = 1%bv)) as [->|N1]; [rewrite T1, H1; reflexivity|].
  destruct (decide (r = 2%bv)) as [->|N2]; [rewrite T2, H2; f_equal; lia|].
  destruct (decide (r = 8%bv)) as [->|N8]; [rewrite T8; apply Z_to_bv_bv_unsigned|].
  destruct (decide (r = 9%bv)) as [->|N9]; [rewrite T9; apply Z_to_bv_bv_unsigned|].
  destruct (decide (r = 18%bv)) as [->|N18]; [rewrite T18; apply Z_to_bv_bv_unsigned|].
  destruct (decide (r = 19%bv)) as [->|N19]; [rewrite T19; apply Z_to_bv_bv_unsigned|].
  destruct (decide (r = 20%bv)) as [->|N20]; [rewrite T20; apply Z_to_bv_bv_unsigned|].
  rewrite K4 by (unfold art_pop_kept; repeat split; assumption).
  rewrite K3 by assumption. rewrite K2 by assumption. apply K1. unfold art_ca_entry_kept; repeat split; assumption.
Qed.
End FPX.
