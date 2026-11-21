(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Tac Image ZBridge Walk Arr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import PImg FlKit FlSeg1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section SEG.
Context {rc : runConstT}.
Variable usp : Z.
Hypothesis USP : 0x7fff7f800000 <= usp < 2^64.
Hypothesis USP16 : usp mod 16 = 0.

Definition TSV (v19 : word) (up cp n : Z) : list cell :=
  [C8 v19; C8 (Z_to_bv 64 cp); C8 (Z_to_bv 64 up); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0x1635c)].

Lemma fl_seg_d1 : forall (Q : machine_state -> Prop) (D n cp cl lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -288 -> 0 <= lo -> 0 <= D < 2^64 -> 0 < cp < 2^64 -> 0 <= cl < 2^64 ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M ->
  OP.rdn psegs M (Z_to_bv 64 0x3d6a8) 8 = Some (Z_to_le_bytes 8 D) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -40)) 8 = Some (Z_to_le_bytes 8 cl) ->
  (forall (M1 : word -> option byte),
     munch [(usp + -200, usp + -188); (usp + -176, usp + -164)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -48) ->
     OP.rdn psegs M1 (Z_to_bv 64 (usp + -200)) 8 = Some (Z_to_le_bytes 8 D) ->
     OP.rdn psegs M1 (Z_to_bv 64 (usp + -192)) 4 = Some (Z_to_le_bytes 4 3) ->
     OP.rdn psegs M1 (Z_to_bv 64 (usp + -176)) 8 = Some (Z_to_le_bytes 8 cp) ->
     OP.rdn psegs M1 (Z_to_bv 64 (usp + -168)) 4 = Some (Z_to_le_bytes 4 cl) ->
     Q (MS (mkR (Z_to_bv 64 0x16064) (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp)
                (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 3) x12 x13 x14 x15 x16 x17
                x18 (Z_to_bv 64 3) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x16f84) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                       x18 (Z_to_bv 64 0x3d6a0) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16028) fc None M (seg_rom psegs)).
Proof.
  intros Q D n cp cl lo M F fc x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 DR CP CL ST MI RD RC HK.
  change (2^64) with 18446744073709551616 in DR, CP, CL.
  pose proof (munch_refl [(usp + -200, usp + -188); (usp + -176, usp + -164)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  pose proof (ro_C8_of_rdn_Z M _ _ RD ltac:(lia) ltac:(lia) ltac:(lia)) as RCD.
  pose proof (ro_C8_of_rdn_Z M _ _ RC ltac:(lia) ltac:(lia) ltac:(lia)) as RCC. clear RD RC.
  destruct (stk_split psegs M lo (usp + -164) (usp + -48) ST ltac:(lia)) as [STa STb].
  destruct (stk_split psegs M lo (usp + -188) (usp + -164) STa ltac:(lia)) as [STc STd].
  carve_frame 12%nat STd. carve_frame 12%nat STc.
  step. if_false. do 2 step. do 3 step. step. br_false. do 2 step. br_align8. do 2 step. do 4 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (R1 : OP.rdn psegs m1 (Z_to_bv 64 (usp + -200)) 8 = Some (Z_to_le_bytes 8 D)) by (cell_fact FR0 0%nat);
    assert (R2 : OP.rdn psegs m1 (Z_to_bv 64 (usp + -192)) 4 = Some (Z_to_le_bytes 4 3)) by (cell_fact FR0 8%nat);
    assert (R3 : OP.rdn psegs m1 (Z_to_bv 64 (usp + -176)) 8 = Some (Z_to_le_bytes 8 cp)) by (cell_fact FR 0%nat);
    assert (R4 : OP.rdn psegs m1 (Z_to_bv 64 (usp + -168)) 4 = Some (Z_to_le_bytes 4 cl)) by (cell_fact FR 8%nat)
  end.
  release_frame FR0 STc (usp + -188). release_frame FR STd (usp + -164).
  pose proof (stk_merge psegs _ _ _ _ STc STd ltac:(lia)) as STa'.
  pose proof (stk_merge psegs _ _ _ _ STa' STb ltac:(lia)) as ST'.
  apply evt_done. eapply HK; try eassumption.
Qed.

Lemma fl_seg_d2 : forall (Q : machine_state -> Prop) (n cp cl b lo : Z) (c012 : list byte) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -288 -> 0 <= lo -> 4 <= n <= 2^20 -> 0 < cp -> cp + cl <= lo -> 4 <= cl -> 0 <= b < 256 ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M ->
  rw_cells psegs M cp [CB 3 c012; C1 (Z_to_bv 8 b)] ->
  (forall (M1 : word -> option byte),
     munch [(cp + 3, cp + 4); (usp + -192, usp + -188)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -48) ->
     rw_cells psegs M1 cp [CB 3 c012; C1 (Z_to_bv 8 (b + 1))] ->
     OP.rdn psegs M1 (Z_to_bv 64 (usp + -192)) 4 = Some (Z_to_le_bytes 4 (n - 3)) ->
     Q (MS (mkR (Z_to_bv 64 0x16090) (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp)
                (Z_to_bv 64 (usp + -200)) (Z_to_bv 64 4) x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 (n - 3)) (Z_to_bv 64 3) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x16f84) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 n) (Z_to_bv 64 3) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16064) fc None M (seg_rom psegs)).
Proof.
  intros Q n cp cl b lo c012 M F fc x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 NR CP CPL CL4 BR ST MI BC HK.
  change (2^20) with 1048576 in NR.
  pose proof (munch_refl [(cp + 3, cp + 4); (usp + -192, usp + -188)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  destruct (stk_split psegs M lo (usp + -188) (usp + -48) ST ltac:(lia)) as [STa STb].
  carve_frame 4%nat STa.
  step. if_false. do 2 step. brw_false. do 3 step.
  replace (bv_unsigned (zxb (Z_to_bv 8 b))) with b in *
    by (unfold zxb; rewrite (Z_to_bv_unsigned 8 b); change (bv_wrap 8 b) with (b mod 256); rewrite Z.mod_small by lia;
        rewrite unsigned_lit by lia; reflexivity).
  step.
  replace (le1 (Z_to_bv 64 (b + 1))) with [Z_to_bv 8 (b + 1)] by (unfold le1; rewrite unsigned_lit by lia; reflexivity).
  mem_after_store.
  do 4 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (R2 : OP.rdn psegs m1 (Z_to_bv 64 (usp + -192)) 4 = Some (Z_to_le_bytes 4 (n - 3))) by (cell_fact FR 0%nat)
  end.
  release_frame FR STa (usp + -188).
  pose proof (stk_merge psegs _ _ _ _ STa STb ltac:(lia)) as ST'.
  apply evt_done. eapply HK; try eassumption.
Qed.

Lemma fl_seg_de : forall (Q : machine_state -> Prop) (cp s pb st rc2 lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -288 -> 0 <= lo -> 0 < cp < 2^64 -> 0 < s -> s + 5968 <= usp + -16384 -> s mod 16 = 0 -> 0 < pb < 2^64 ->
  (st = 113 \/ st = 666) -> (rc2 = 0 \/ rc2 = 1) ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -144)) 8 = Some (Z_to_le_bytes 8 s) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -136)) 8 = Some (Z_to_le_bytes 8 0x1a9f4) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -128)) 8 = Some (Z_to_le_bytes 8 0x1aa04) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -120)) 8 = Some (Z_to_le_bytes 8 0) ->
  OP.rdn psegs M (Z_to_bv 64 s) 8 = Some (Z_to_le_bytes 8 (usp + -200)) ->
  OP.rdn psegs M (Z_to_bv 64 (s + 8)) 4 = Some (Z_to_le_bytes 4 st) ->
  OP.rdn psegs M (Z_to_bv 64 (s + 16)) 8 = Some (Z_to_le_bytes 8 pb) ->
  (forall (M1 : word -> option byte) (y14 y15 : word) (pad : list byte),
     munch [(usp + -240, usp + -208)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -240) ->
     rw_cells psegs M1 (usp + -240) [CB 8 pad; C8 (Z_to_bv 64 cp); C8 (Z_to_bv 64 (usp + -40)); C8 (Z_to_bv 64 0x160a0)] ->
     Q (MS (mkR (Z_to_bv 64 0x167a0) (Z_to_bv 64 (usp + -240)) x3 x4 x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 (usp + -200))
                (Z_to_bv 64 pb) (Z_to_bv 64 pb) (Z_to_bv 64 s) (Z_to_bv 64 0x1aa04) y14 y15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x2397c) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp) (Z_to_bv 64 rc2) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16090) fc None M (seg_rom psegs)).
Proof.
  intros Q cp s pb st rc2 lo M F fc x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 CP S0 SHI S16 PB ST2 RC ST MI R1 R2 R3 R4 R5 R6 R7 HK.
  change (2^64) with 18446744073709551616 in CP, PB.
  pose proof (munch_refl [(usp + -240, usp + -208)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  pose proof (ro_C8_of_rdn_Z M _ _ R1 ltac:(lia) ltac:(lia) ltac:(lia)) as RC1.
  pose proof (ro_C8_of_rdn_Z M _ _ R2 ltac:(lia) ltac:(lia) ltac:(lia)) as RC2.
  pose proof (ro_C8_of_rdn_Z M _ _ R3 ltac:(lia) ltac:(lia) ltac:(lia)) as RC3.
  pose proof (ro_C8_of_rdn_Z M _ _ R4 ltac:(lia) ltac:(lia) ltac:(lia)) as RC4.
  pose proof (ro_C8_of_rdn_Z M _ _ R5 ltac:(lia) ltac:(lia) ltac:(lia)) as RC5.
  pose proof (ro_C4_of_rdn_Z M _ _ R6 ltac:(lia) ltac:(lia) ltac:(lia)) as RC6.
  pose proof (ro_C8_of_rdn_Z M _ _ R7 ltac:(lia) ltac:(lia) ltac:(lia)) as RC7.
  clear R1 R2 R3 R4 R5 R6 R7.
  destruct (stk_split psegs M lo (usp + -208) (usp + -48) ST ltac:(lia)) as [STa STb].
  step. step.
  match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota|] end.
  2:{ symmetry. unfold bv_leu, bv_ltu. rewrite !unsigned_lit_wrap. change (2^64) with 18446744073709551616.
      apply negb_false_iff. apply Z.ltb_lt. lia. }
  do 2 step.
  step. carve_frame 32%nat STa. replace (usp + -208 + -32) with (usp + -240) in * by lia.
  do 3 step.
  do 2 step. br_false. do 2 step. br_align8. do 2 step. if_false. do 2 step. if_false. do 2 step. br_false. do 2 step. br_align8.
  do 2 step. br_true. do 4 step.
  destruct ST2 as [-> | ->].
  -
    if_false. do 5 step. if_false.
    replace (sx32 (Z_to_bv 64 113)) with (Z_to_bv 64 113) in * by (vm_compute; reflexivity).
    do 3 step. br_false. do 4 step.
    apply evt_done. eapply HK; eassumption.
  -
    if_true. do 2 step. if_false. do 2 step. if_false. step.
    replace (sx32 (Z_to_bv 64 666)) with (Z_to_bv 64 666) in * by (vm_compute; reflexivity).
    do 3 step. br_false. do 4 step.
    apply evt_done. eapply HK; eassumption.
Qed.

Lemma fl_de_station : forall (pc0 pc1 : Z) (off : Z), 
  (pc0 = 0x167a0 /\ off = 120) \/ (pc0 = 0x167c8 /\ off = 112) \/ (pc0 = 0x167f0 /\ off = 96) -> pc1 = pc0 + 0x28 ->
  forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (s blk : Z)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 < s -> s + 5968 <= usp - 16384 -> s mod 16 = 0 -> 0 < blk < 2^64 ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -144)) 8 = Some (Z_to_le_bytes 8 s) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -128)) 8 = Some (Z_to_le_bytes 8 0x1aa04) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -120)) 8 = Some (Z_to_le_bytes 8 0) ->
  OP.rdn psegs M (Z_to_bv 64 (s + off)) 8 = Some (Z_to_le_bytes 8 blk) ->
  Q (MS (mkR (Z_to_bv 64 pc1) (Z_to_bv 64 (usp + -240)) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (usp + -200))
             (Z_to_bv 64 blk) (Z_to_bv 64 blk) (Z_to_bv 64 0x1aa04) x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x2397c) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -240)) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (usp + -200)) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 pc0) fc None M (seg_rom psegs)).
Proof.
  intros pc0 pc1 off HPC -> Q M F fc s blk x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         S0 SHI S16 BR R1 R2 R3 R4 HK.
  change (2^64) with 18446744073709551616 in BR.
  pose proof (ovr_of_rdn_Z M _ (usp + -200 + 56) _ R1 ltac:(lia) ltac:(lia)) as HR1.
  pose proof (ovr_of_rdn_Z M _ (usp + -200 + 72) _ R2 ltac:(lia) ltac:(lia)) as HR2.
  pose proof (ovr_of_rdn_Z M _ (usp + -200 + 80) _ R3 ltac:(lia) ltac:(lia)) as HR3.
  pose proof (ovr_of_rdn_Z M _ (s + off) _ R4 ltac:(lia) ltac:(lia)) as HR4.
  destruct HPC as [[-> ->]|[[-> ->]|[-> ->]]]; (do 3 step; br_false; do 2 step; br_align8; do 2 step; br_false; do 3 step; do 2 step; apply evt_done; exact HK).
Qed.

Lemma fl_de5 : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (s : Z)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  0 < s < 2^64 ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -144)) 8 = Some (Z_to_le_bytes 8 s) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -128)) 8 = Some (Z_to_le_bytes 8 0x1aa04) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -120)) 8 = Some (Z_to_le_bytes 8 0) ->
  Q (MS (mkR (Z_to_bv 64 0x16834) (Z_to_bv 64 (usp + -240)) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (usp + -200))
             (Z_to_bv 64 s) (Z_to_bv 64 s) (Z_to_bv 64 0) (Z_to_bv 64 0x1aa04) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x2397c) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -240)) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (usp + -200)) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16818) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc s x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         SR R1 R2 R3 HK.
  change (2^64) with 18446744073709551616 in SR.
  pose proof (ovr_of_rdn_Z M _ (usp + -200 + 56) _ R1 ltac:(lia) ltac:(lia)) as HR1.
  pose proof (ovr_of_rdn_Z M _ (usp + -200 + 72) _ R2 ltac:(lia) ltac:(lia)) as HR2.
  pose proof (ovr_of_rdn_Z M _ (usp + -200 + 80) _ R3 ltac:(lia) ltac:(lia)) as HR3.
  do 9 step. apply evt_done. exact HK.
Qed.

Lemma fl_seg_de_tail : forall (Q : machine_state -> Prop) (cp st r lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp + -288 -> 0 <= lo -> 0 < cp < 2^64 ->
  ((st = 666 /\ r = 0) \/ (st = 113 /\ r = -3)) ->
  stk psegs M lo (usp + -48) -> mem_inv psegs M ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -216)) 8 = Some (Z_to_le_bytes 8 0x160a0) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -224)) 8 = Some (Z_to_le_bytes 8 (usp + -40)) ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -232)) 8 = Some (Z_to_le_bytes 8 cp) ->
  (forall (M1 : word -> option byte),
     munch [(usp + -144, usp + -136)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     stk psegs M1 lo (usp + -48) ->
     OP.rdn psegs M1 (Z_to_bv 64 (usp + -144)) 8 = Some (Z_to_le_bytes 8 0) ->
     Q (MS (mkR (Z_to_bv 64 0x160a0) (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -40)) (Z_to_bv 64 cp)
                (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x160a0) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -240)) x3 x4 x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 (usp + -200)) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16834) fc None M (seg_rom psegs)).
Proof.
  intros Q cp st r lo M F fc x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 CP STR ST MI R1 R2 R3 HK.
  change (2^64) with 18446744073709551616 in CP.
  pose proof (munch_refl [(usp + -144, usp + -136)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  pose proof (ro_C8_of_rdn_Z M _ _ R1 ltac:(lia) ltac:(lia) ltac:(lia)) as RC1.
  pose proof (ro_C8_of_rdn_Z M _ _ R2 ltac:(lia) ltac:(lia) ltac:(lia)) as RC2.
  pose proof (ro_C8_of_rdn_Z M _ _ R3 ltac:(lia) ltac:(lia) ltac:(lia)) as RC3.
  clear R1 R2 R3.
  destruct (stk_split psegs M lo (usp + -136) (usp + -48) ST ltac:(lia)) as [STa STb].
  carve_frame 8%nat STa.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (RZ : OP.rdn psegs m1 (Z_to_bv 64 (usp + -144)) 8 = Some (Z_to_le_bytes 8 0)) by (cell_fact FR 0%nat)
  end.
  release_frame FR STa (usp + -136).
  pose proof (stk_merge psegs _ _ _ _ STa STb ltac:(lia)) as ST'.
  destruct STR as [[-> ->]|[-> ->]]; do 4 step.
  - replace (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 553)) + -1))) 18446744073709551613)
      with 0 in * by (vm_compute; reflexivity).
    do 5 step. apply evt_done. eapply HK; eassumption.
  - replace (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) + -1))) 18446744073709551613))
      with (Z_to_bv 64 (-3)) in * by (apply bv_eq; vm_compute; reflexivity).
    do 5 step. apply evt_done. eapply HK; eassumption.
Qed.

Lemma fl_seg_tf_ok : forall (Q : machine_state -> Prop) (n tot : Z) (pad : list byte) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v18 v9 v8 v1 : word),
  0 <= tot < 2^64 ->
  rw_cells psegs M (usp + -48) (LFC pad (fl_cl n) v18 v9 v8 v1) -> mem_inv psegs M ->
  OP.rdn psegs M (Z_to_bv 64 (usp + -160)) 8 = Some (Z_to_le_bytes 8 tot) ->
  (forall (M1 : word -> option byte),
     munch [(usp + -40, usp + -32)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     rw_cells psegs M1 (usp + -48) (LFC pad tot v18 v9 v8 v1) ->
     Q (MS (mkR x1 (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -40)) x9
                (Z_to_bv 64 tot) x11 x12 x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x16140) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp + -40)) x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x160a0) fc None M (seg_rom psegs)).
Proof.
  intros Q n tot pad M F fc x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v18 v9 v8 v1
         TR LF MI R1 HK.
  change (2^64) with 18446744073709551616 in TR.
  pose proof (munch_refl [(usp + -40, usp + -32)] M) as MU. pose proof (wmono_refl psegs M) as WM.
  pose proof (ovr_of_rdn_Z M _ (usp + -208 + 48) _ R1 ltac:(lia) ltac:(lia)) as HR1.
  unfold LFC in *.
  step. br_false. do 3 step.
  apply evt_done. eapply HK; eassumption.
Qed.

Lemma fl_seg_tf_dE : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  mem_inv psegs M -> relro_pristine M ->
  Q (MS (mkR (Z_to_bv 64 0x16140) (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 x8 x9
             (Z_to_bv 64 0x2d438) (Z_to_bv 64 0x102f2) (Z_to_bv 64 0x1030b) (Z_to_bv 64 (-3)) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x25774) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (-3)) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x160a0) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 MI RP HK.
  relro_cells RP.
  step. if_true. do 8 step. step.
  apply evt_done. exact HK.
Qed.

Lemma fl_seg_tf_ret : forall (Q : machine_state -> Prop) (n cp up : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v19 : word),
  0 <= n < 2^64 -> 0 < cp < 2^64 -> 0 < up < 2^64 ->
  rw_cells psegs M (usp + -88) (TSV v19 up cp n) -> mem_inv psegs M ->
  Q (MS (mkR (Z_to_bv 64 0x1635c) (Z_to_bv 64 (usp + -48)) x3 x4 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 up)
             (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 cp) v19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1635c) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp + -208)) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x16140) fc None M (seg_rom psegs)).
Proof.
  intros Q n cp up M F fc x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v19
         NR CP UP SA MI HK.
  change (2^64) with 18446744073709551616 in NR, CP, UP.
  unfold TSV in SA.
  do 6 step. do 2 step.
  apply evt_done. exact HK.
Qed.

End SEG.
