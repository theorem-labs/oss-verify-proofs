(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, module names, addresses and numbers changed; 573 of its 789 lines of code are new or changed and 332 lines of the source are left out. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecStub rec_shape_of_c RecGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecTail RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import rec_calls_free_c xstrdup_c arg_i_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import sup_after_reply_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sar_pre_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n))
                     a1 b0 b1 b2 a3 a4 a5 a6 a7 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16db0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16d54) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 12 step.
  rewrite sx32_lit by lia.
  assert (C1 : negb (bv_eqb (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 16)) = true).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia. }
  rewrite C1. cbv iota.
  do 7 step.
  rewrite da_addr by lia.
  apply evt_done.
  do 4 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma sar_rec :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (jk : list byte),
  rw_cells rsegs m e [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16dc4) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1
                     (Z_to_bv 64 e) s2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b1c) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16db0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e jk EW.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  do 3 step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; eassumption.
Qed.

Lemma sar_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat) (jk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 jk] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x16dc4) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a1 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n))
                     a0 b2 a3 a4 a5 a6 a7 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b1c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16d54) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n jk ST LO LO2 NC Hn EW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply sar_pre_lt; [exact ST | exact LO | exact LO2 | exact NC | exact Hn] |].
  intros ms1 (b0 & b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1).
  assert (EW1 : rw_cells rsegs m1 (0x33d58 + 56 * Z.of_nat n) [CB 8 jk]).
  { apply (rw_cells_transport rsegs [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m1 _ _ EW MU1 WM1).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  eapply evt_cut; [eapply sar_rec; exact EW1 |].
  intros ms2 (m2 & -> & MU2 & WM2 & EN2).
  apply evt_done. exists b2, m2. split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m2).
    - apply (munch_weaken [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)]); [|exact MU1].
      intros x (H1 & H2 & H3 & _). split; [exact H1 | split; [exact H2 | exact I]].
    - apply (munch_weaken [(0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)]); [|exact MU2].
      intros x (H1 & H2 & H3 & _). split; [exact H3 | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM1 WM2)|].
  split.
  { apply (stk_transport_disjoint rsegs _ m1 m2 _ _ ST1 MU2 WM2). cbn [disjoint_from]. repeat split; lia. }
  split.
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  split; [|exact EN2].
  apply (rw_cells_transport rsegs _ m1 m2 _ _ NC1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
  repeat split; lia.
Qed.

Lemma sar_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x16d90) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     a1 (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) b2 a3 a4 a5 a6 a7
                     a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16d54) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 12 step.
  rewrite sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  do 2 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma sar_ret16 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (jk : list byte),
  rw_cells rsegs m 0x33d10 [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16dc4) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1
                     (Z_to_bv 64 0x33d10) s2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b1c) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16d90) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m jk EW.
  step.
  eapply sar_rec. exact EW.
Qed.

Lemma sar_guard :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 1)] ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16de4) sp gp tp t0 t1 t2 (Z_to_bv 64 e) (sel_null s1) (sel_null s1)
                                    (Z_to_bv 64 5) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15780) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16dc4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e EN.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  do 2 step.
  rewrite sx32_lit by lia.
  step. if_false.
  step.
  destruct (Z.eq_dec (bv_unsigned s1) 0) as [Z2|Z2].
  - if_false. do 4 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_eq _ _) Z2).
    apply evt_done. reflexivity.
  - if_true. do 2 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_neq _ _) Z2).
    apply evt_done. reflexivity.
Qed.

Lemma sar_st :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 1)] ->
  rw_cells rsegs m (e + 16) [CB 8 junk] ->
  evt rsegs (fun ms' => exists b1 b2 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 b1 b2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16dfc) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 16, e + 24)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 2)]
       /\ rw_cells rsegs m' (e + 16) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16de4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EN EA.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 16, e + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  rewrite sx32_lit by lia.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 1)) 3) with 8 by reflexivity.
  replace (bv_unsigned (Z_to_bv 64 1) + 1) with 2 by reflexivity.
  do 2 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma sar_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' s20 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' a0 a1 a2 a3 a4 a5 a6 a7
                                    s20 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16dfc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' s20 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 6 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma sar_fin :
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte) (sp0 ra0 s00 s10' s20 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 1)] -> rw_cells rsegs m (e + 16) [CB 8 junk] ->
  e + 24 <= bv_unsigned sp0 - 32 ->
  evt rsegs (fun ms' => exists b1 b2 m',
       ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' a0 b1 b2 a3 a4 a5 a6 a7
                     s20 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra0) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 16, e + 24)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 2)]
       /\ rw_cells rsegs m' (e + 16) [C8 a0])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16de4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk sp0 ra0 s00 s10' s20 FR SPR EN EA SEP.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  eapply evt_cut; [eapply sar_st; [exact EN | exact EA] |].
  intros ms1 (b1 & b2 & m1 & -> & MU1 & WM1 & NA1 & EA1).
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0]).
  { apply (rw_cells_transport rsegs _ m m1 _ _ FR MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply sar_tail; [exact FR1 | exact SPR] |].
  intros ms2 ->. apply evt_done. exists b1, b2, m1. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact NA1 | exact EA1].
Qed.

Ltac pres_ex X :=
  intros rr Hrr N2 N8 N9 N18; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
               rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr N2 N8 N9 N18;
  repeat (destruct CC as [CC|CC]; [subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
    simp_regs; first [reflexivity | unfold getr; reflexivity]|]);
  subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Ltac ex_cases :=
  intros rr Hrr N2 N8 N9 N18; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
               rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr N2 N8 N9 N18;
  repeat (destruct CC as [CC|CC]; [subst rr; (try split); simp_regs; reflexivity|]);
  subst rr; (try split); simp_regs; reflexivity.

Lemma sar_pres_mid : forall regs R1 R2 R3 M1 M3,
  Regs6ss.xregs_eqv M1 R1 -> regs_preserved R1 R2 -> Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
     reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r) /\ reg_get M1 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr R3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
  intros regs R1 R2 R3 M1 M3 X1 P X3 K r Hr N2 N8 N9 N18.
  pose proof (RecStub.getr_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ.
  destruct (K r Hr N2 N8 N9 N18) as [E1 E2]. rewrite E1, <- E2.
  pose proof (P r Hr) as E3. unfold getr in E3. rewrite NZ in E3. rewrite E3. symmetry. apply X1. exact NZ.
Qed.

Lemma sar_pres_step9 : forall R2 R3 M3,
  Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> r <> 9 -> reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r)) ->
  forall r, callee_saved r -> r <> 9 -> getr R3 (Z_to_bv 5 r) = getr R2 (Z_to_bv 5 r).
Proof.
  intros R2 R3 M3 X3 K r Hr N9. pose proof (RecStub.getr_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ. exact (K r Hr N9).
Qed.

Lemma sar_pres_fin : forall regs R1 R4 R5 M5,
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (forall r, callee_saved r -> r <> 9 -> getr R4 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r)) ->
  Regs6ss.xregs_eqv M5 R5 ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
     reg_get M5 (Z_to_bv 5 r) = reg_get R4 (Z_to_bv 5 r)) ->
  (forall r, callee_saved r -> r = 2 \/ r = 8 \/ r = 9 \/ r = 18 -> reg_get M5 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  regs_preserved regs R5.
Proof.
  intros regs R1 R4 R5 M5 P1 P X5 K1 K2 r Hr.
  pose proof (RecStub.getr_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X5 NZ). unfold getr. rewrite NZ.
  destruct (Z.eq_dec r 2) as [E|N2]; [exact (K2 r Hr (or_introl E))|].
  destruct (Z.eq_dec r 8) as [E|N8]; [exact (K2 r Hr (or_intror (or_introl E)))|].
  destruct (Z.eq_dec r 9) as [E|N9]; [exact (K2 r Hr (or_intror (or_intror (or_introl E))))|].
  destruct (Z.eq_dec r 18) as [E|N18]; [exact (K2 r Hr (or_intror (or_intror (or_intror E))))|].
  rewrite (K1 r Hr N2 N8 N9 N18).
  pose proof (P r Hr N9) as E3. unfold getr in E3. rewrite NZ in E3. rewrite E3.
  pose proof (P1 r Hr N2 N8 N9 N18) as E4. unfold getr in E4. rewrite NZ in E4. exact E4.
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis CTX : ctx_owned B API.

Lemma sinv_ret : forall K L A regs mem md O Lc Ac regs1 mc mdc Rc Oc bc,
  call_pre_t B API K L A regs mem md ->
  sinv B API K (spZ regs) L A mem md O Lc Ac mc mdc Rc Oc bc ->
  regs_preserved regs regs1 ->
  call_post_rec B (aa_MR API) K L A regs mem md rec_area (fun a => In a (map fst O)) Lc Ac regs1 mc mdc /\
  g_rec_rep rsegs Lc Ac mc Rc Oc /\ owns_new L A O Oc /\
  (forall pn, In pn (blocks Lc Ac) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn Oc) /\
  others_kept (ms_segs B) L A mem Lc Ac mc O /\
  ro_agree rsegs mc /\ f18_words rsegs mc /\ res_ok_slots Ac (sb_shift bc A Ac).
Proof using CTX.
  intros K L A regs mem md O Lc Ac regs1 mc mdc Rc Oc bc PRE SI RP.
  destruct SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof PRE as (PRK & _).
  split.
  { apply (rjr_final B (aa_MR API) CTX K rec_area (fun pn => In pn O) _ L A regs mem md Lc Ac regs1 mc mdc PRK RJ RP).
    intros a n G. apply in_map_iff. exists (a, n). split; [reflexivity | exact G]. }
  split; [exact GR|]. split; [exact ON|]. split; [exact B1|].
  split; [exact (rjr_others_kept B (aa_MR API) K (spZ regs) rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc O RJ
                   (fun pn G => G))|].
  split; [exact RA|]. split; [exact F18 | exact RS].
Qed.

Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis SLACK : block_slack_present B API.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis XSD : forall fx0 : YK11.FPState, xstrdup_contract (fx := fx0) B API.
Hypothesis ARGI : arg_i_contract B API.

Lemma sar_arg : forall L A regs mem md id pv verb R O b Lc Ac R1 m1 md1 Oc,
  call_pre_t B API 8288 L A regs mem md -> getr regs 10 = Z_to_bv 64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
  getr regs 11 = Z_to_bv 64 pv ->
  str_arg B L A O (spZ regs) 8288 mem pv verb -> ro_agree rsegs mem -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_after_reply_sizes id verb)) (LMAX + 1) ->
  sinv B API 8288 (spZ regs) L A mem md O Lc Ac m1 md1 (rec_record R REC_AFTER_REPLY []) Oc b ->
  sb_le (sb_shift b A Ac) b ->
  getr R1 1 = Z_to_bv 64 0x16dc4 -> getr R1 2 = Z_to_bv 64 (spZ regs - 32) -> getr R1 4 = getr regs 4 ->
  getr R1 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R1 9 = getr regs 11 ->
  getr R1 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R1 11 = getr regs 10 ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
     getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells rsegs m1 (spZ regs - 32) [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs m1 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 0)) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15b1c) m1 (seg_rom rsegs)) md1)
    (sup_after_reply_ret B API L A regs mem md id verb R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK XSD ARGI.
  intros L A regs mem md id pv verb R O b Lc Ac R1 m1 md1 Oc PRE A0 HID A1 SA RA FRM ROOM SI1 BLE1
    E1 E2 E4 E8 E9 E10 E11 PR1 FR1 NA1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold sup_after_reply_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  pose proof (dec_length id HID) as DL.
  assert (ER : rec_entry G_REC REC_SC R mod 8 = 0 /\ REC_SC <= rec_entry G_REC REC_SC R /\
               rec_entry G_REC REC_SC R + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE, REC_SC, REC_SIZE.
      split; [|lia]. apply Z.mod_divide; [lia|]. exists (26539 + 7 * Z.of_nat (length (r_calls R))). lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. split; [reflexivity | lia]. }
  set (e := rec_entry G_REC REC_SC R) in *.
  assert (EE : e = rec_entry G_REC REC_SC R) by reflexivity.
  assert (EB : 0x33d10 <= e /\ e + 56 <= 0x34108) by (unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE in ER; lia).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI1 as (RJ1 & _ & _ & _ & _ & RA1 & F181 & RS1).
  pose proof RJ1 as (HM1 & _).
  pose proof ARGI as AI. unfold arg_i_contract in AI. rewrite SEGS in AI.
  eapply SR_bind.
  { apply (AI Lc Ac R1 m1 md1 e id 0 (sb_shift b A Ac)).
    - split; [|rewrite SP1; lia].
      apply (call_pre_k_of_rjr B _ 8288 (bv_unsigned sp) rec_area _ L A mem md Lc Ac m1 md1 ARG_I_K R1 RJ1).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP1. unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP1. lia.
      + rewrite E4. exact HTP.
    - exact E10.
    - rewrite E11. exact A0.
    - exact HID.
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - exact (proj2 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact NA1.
    - lia.
    - exact F181.
    - exact FRM.
    - exact RS1.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE1|].
        apply sb_le_malloc; lia.
      + unfold LMAX; lia.
    - exact RA1. }
  intros c2 (fx' & L2 & A2 & R2 & m2 & md2 & -> & FK & BK2 & UB2 & _ & RA2 & _ & F182 & RGN2 & ALT).
  destruct ALT as [(H06 & _)|(_ & p1 & POST2 & Hp1 & _ & FB2 & BLK2 & BN2 & BS2 & BX2 & INI2 & RS2)]; [lia|].
  rewrite SEGS in RA2, F182, BN2, BS2, BX2 |- *.
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 8288 (bv_unsigned sp) L A mem md O Lc Ac m1 md1 R
                REC_AFTER_REPLY [] Oc b ARG_I_K R1 _ L2 A2 R2 m2 md2 (dec id) p1 (Z.of_nat (length (dec id)) + 1)
                SI1 ltac:(cbn; lia) ltac:(rewrite SP1; unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK; lia)
                ltac:(rewrite SP1; lia) POST2
                ltac:(intros a Ha; cbv beta in Ha; try rewrite <- EE; cbn [length Z.of_nat]; lia)
                Hp1 FB2 BLK2 UB2 BK2 RGN2 BN2 BS2 BX2 (dec_no0 id) ltac:(unfold LMAX; lia) ltac:(unfold LMAX; lia)
                INI2 RS2 RA2 F182) as SI2.
  cbn [app] in SI2.
  pose proof POST2 as (PM2 & _ & _ & _ & _ & RP2 & _).
  assert (R2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E2).
  assert (R2_8 : getr R2 8 = Z_to_bv 64 e) by exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E8).
  assert (R2_8' : reg_get R2 8 = Z_to_bv 64 e) by exact R2_8.
  assert (R2_9 : reg_get R2 9 = Z_to_bv 64 pv)
    by exact (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) (eq_trans E9 A1)).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct FB2 as (_ & FBb2 & _).
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_I_K Lc Ac R1 m1 md1 _ L2 A2 R2 m2 md2 (bv_unsigned sp - 32 + i)
                HM1 POST2 ltac:(lia) ltac:(rewrite SP1; lia)) as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  destruct (mr_model B _ LAWS L2 A2 m2 md2 PM2) as (Hh2 & Hl2 & _).
  assert (NAn : rw_cells rsegs (normalize rsegs m2) (e + 4) [C4 (Z_to_bv 64 1)]).
  { apply rw_cells_normalize; [exact RA2 | |].
    - apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact BN2].
    - intros i Hi. cbn in Hi. apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  rewrite E1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R2_8'.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply sar_guard. exact NAn. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  subst s3n.
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3
                (munch_refl [] (normalize rsegs m2))) as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3
                (wmono_refl rsegs (normalize rsegs m2))) as WM3.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR3r NAn) as NA3.
  clear MR3r.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  pose proof (sinv_stack B API SEGS GOWN AX 8288 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 _ _ b m3 [] SI2 MU3 WM3
                ltac:(intros a Ra Hm; exfalso; apply Hm; exact I)) as SI3.
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 8288 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 _ _ b pv verb
              SI3 RA ltac:(unfold NULL_LIT; lia) SA)
    as (s & slack & PW & SEL & S0 & BS & N0 & LX & AL & DJ & HOME & NRA).
  assert (SELW : sel_null (reg_get R2 9) = Z_to_bv 64 s)
    by (rewrite R2_9; unfold sel_null; rewrite unsigned_lit by lia; rewrite <- SEL; destruct (pv =? 0); reflexivity).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x16de4) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 s) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact SELW).
  assert (P23 : forall r, callee_saved r -> r <> 9 -> getr R3 (Z_to_bv 5 r) = getr R2 (Z_to_bv 5 r)).
  { apply (sar_pres_step9 R2 R3 _ X3). intros rr Hrr N9. unfold callee_saved in Hrr.
    assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
                 rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    clear Hrr N9.
    repeat (destruct CC as [CC|CC]; [subst rr; simp_regs; first [reflexivity | symmetry; exact R2_8']|]).
    subst rr; simp_regs; reflexivity. }
  assert (R3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (P23 2 ltac:(unfold callee_saved; lia) ltac:(lia)) R2_2).
  assert (R3_4 : getr R3 4 = getr regs 4)
    by exact (eq_trans (P23 4 ltac:(unfold callee_saved; lia) ltac:(lia))
                (eq_trans (RP2 4 ltac:(unfold callee_saved; lia)) E4)).
  assert (R3_8 : getr R3 8 = Z_to_bv 64 e) by exact (eq_trans (P23 8 ltac:(unfold callee_saved; lia) ltac:(lia)) R2_8).
  assert (SP3 : spZ R3 = bv_unsigned sp - 32) by (unfold spZ; rewrite R3_2; apply unsigned_lit; lia).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3). cbn [disjoint_from]. exact I. }
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & RA3 & F183 & RS3).
  pose proof RJ3 as (HM3 & _).
  set (x := sarg verb) in *.
  assert (BLE2 : sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length (dec id)) + 1))).
  { destruct BLK2 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A Ac A2).
    rewrite <- (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2 bl1 bl2 p1 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE1. }
  pose proof (XSD fx') as XS. unfold xstrdup_contract in XS. rewrite SEGS in XS.
  eapply SR_bind.
  { apply (XS L2 A2 R3 m3 md2 s x slack (sb_shift b A A2)).
    - apply (call_pre_k_of_rjr B _ 8288 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m3 md2 XSTRDUP_K R3 RJ3).
      + rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP3. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. lia.
      + rewrite R3_4. exact HTP.
    - exact E3_10.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact AL.
    - rewrite SP3. unfold XSTRDUP_K, ALLOC_STACK. destruct DJ as [D|D]; [left; lia | right; lia].
    - rewrite SP3. unfold str_home in HOME |- *.
      destruct HOME as [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H].
    - exact RS3.
    - eapply room_slots_mono; [| | exact ROOM].
      + apply sb_malloc_mono. exact BLE2.
      + lia.
    - exact RA3. }
  intros c4 RET.
  destruct RET as (L4 & A4 & R4 & m4 & md4 & p2 & -> & POST4 & A0' & NZ & AL16 & FB4 & BLK4 & BK4 & UB4 & BYT4 & SRC4
    & RA4 & GK4 & INI4 & RGN4 & RS4).
  rewrite SEGS in RA4, BYT4 |- *.
  pose proof POST4 as (PM4 & _ & _ & _ & _ & RP4 & _ & PF4 & _).
  pose proof FB4 as (FBa & FBb & FBc).
  assert (Q4 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) R3_2).
  assert (R4_8' : reg_get R4 8 = Z_to_bv 64 e) by exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) R3_8).
  assert (POST4' : call_post_k B (aa_MR API) XSTRDUP_K L2 A2 R3 m3 md2 (fun a => p2 <= a < p2 + (Z.of_nat (length x) + 1))
                     L4 A4 R4 m4 md4).
  { pose proof POST4 as (Q1 & Q2 & Q3 & Q4' & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4'|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
    intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; lia]. }
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K L2 A2 R3 m3 md2 _ L4 A4 R4 m4 md4 (bv_unsigned sp - 32 + i)
                HM3 POST4 ltac:(lia) ltac:(rewrite SP3; unfold XSTRDUP_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (GK : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> mbyte rsegs m4 a = mbyte rsegs m3 a).
  { intros a Ha. destruct (GFACT a (glob_in a Ha)) as (Gi & _ & _ & Ge).
    rewrite SEGS in PF4.
    refine (proj1 (PF4 a (or_intror Gi) (GOWN L2 A2 m3 md2 a HM3 (glob_in a Ha)) (GOWN L4 A4 m4 md4 a PM4 (glob_in a Ha))
                    _ _)).
    - unfold scratch_k. rewrite SP3. unfold XSTRDUP_K, ALLOC_STACK.
      intros [H|H]; [unfold GLOB_LO, GLOB_N in Ha; lia | exact (Ge H)].
    - cbv beta. intros H. apply (FBc (a - p2)); [lia|]. replace (p2 + (a - p2)) with a by ring. exact Gi. }
  assert (NA4 : rw_cells rsegs m4 (e + 4) [C4 (Z_to_bv 64 1)]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|].
    apply cells_bytes_at in NA3. cbn [cells_bytes cbytes] in NA3. rewrite app_nil_r in NA3.
    apply (bytes_at_transfer rsegs m3); [exact NA3|]. intros i Hi. rewrite length_le4 in Hi.
    apply GK. unfold GLOB_LO, GLOB_N; lia. }
  destruct (glob_rw_cells m4 (e + 16) 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW4].
  assert (NAn4 : rw_cells rsegs (normalize rsegs m4) (e + 4) [C4 (Z_to_bv 64 1)]).
  { apply rw_cells_normalize; [exact RA4 | exact NA4 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  assert (EWn4 : rw_cells rsegs (normalize rsegs m4) (e + 16) [CB 8 junk]).
  { apply rw_cells_normalize; [exact RA4 | exact EW4 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  assert (FRn4 : rw_cells rsegs (normalize rsegs m4) (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply rw_cells_normalize; [exact RA4 | exact FR4 |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  destruct (ax_statics AX L4 A4 m4 md4 PM4) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F184 : f18_words rsegs m4).
  { apply (f18_words_after m3 m4 g F183); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK4 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  destruct (mr_model B _ LAWS L4 A4 m4 md4 PM4) as (Hh4 & Hl4 & _).
  rewrite E3_1.
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q4, R4_8'.
    eapply (evt_normalize rsegs); [exact WX | exact RA4 |].
    eapply sar_fin; [exact FRn4 | lia | exact NAn4 | exact EWn4 | lia]. }
  intros ms5 (can5 & (s5n & Q5 & REL5 & RO5) & EQ5).
  destruct Q5 as (b1' & b2' & m5n & -> & MU5n & WM5n & NA5n & EA5n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL5) as [EC5 MR5r].
  revert EC5 MR5r RO5 EQ5. generalize (ms_mem can5) as m5. intros m5 EC5 MR5r RO5 EQ5. subst can5.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR5r RO5 MU5n) as MU5.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR5r RO5 WM5n) as WM5.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR5r NA5n) as NA5.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR5r EA5n) as EA5.
  clear MU5n WM5n NA5n EA5n MR5r.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  assert (BN5 : bytes_at rsegs m5 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS)
                  (le4 (Z_to_bv 64 (Z.of_nat (length [dec id]) + 1)))).
  { apply cells_bytes_at in NA5. cbn [cells_bytes cbytes] in NA5. rewrite app_nil_r in NA5. exact NA5. }
  assert (BS5 : bytes_at rsegs m5 (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [dec id]))
                  (le8 (Z_to_bv 64 p2))).
  { apply cells_bytes_at in EA5. cbn [cells_bytes cbytes] in EA5. rewrite app_nil_r in EA5.
    replace (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [dec id])) with (e + 16)
      by (rewrite EE; unfold CALL_OFF_ARGS; cbn [length Z.of_nat]; lia).
    assert (Q : reg_get R4 10 = Z_to_bv 64 p2) by exact A0'. rewrite Q in EA5. exact EA5. }
  pose proof (sinv_sarg B API SEGS ERRNO_LOW GFACT GOWN AX 8288 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 R
                REC_AFTER_REPLY [dec id] _ b XSTRDUP_K R3 L4 A4 R4 m4 md4 m5 [(e + 4, e + 8); (e + 16, e + 24)] x p2
                (Z.of_nat (length x) + 1)
                SI3 ltac:(cbn; lia) ltac:(rewrite SP3; unfold XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SP3; lia)
                POST4' MU5 WM5
                ltac:(intros a Ra Hm; cbn in Hm; rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS; cbn [length Z.of_nat]; lia)
                NZ FB4 BLK4 UB4 BK4 RGN4 BN5 BS5 BYT4 N0 LX ltac:(unfold LMAX in *; lia) INI4 RS4 RA4 F184) as SI5.
  cbn [app] in SI5.
  assert (P14 : forall r, callee_saved r -> r <> 9 -> getr R4 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r))
    by (intros r Hr N9; rewrite (RP4 r Hr), (P23 r Hr N9); exact (RP2 r Hr)).
  assert (RP5 : regs_preserved regs R5).
  { apply (sar_pres_fin regs R1 R4 R5 _ PR1 P14 X5).
    - intros rr Hrr N2 N8 N9 N18. unfold callee_saved in Hrr.
      assert (CC : rr = 3 \/ rr = 4 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
                   rr = 25 \/ rr = 26 \/ rr = 27) by lia.
      clear Hrr N2 N8 N9 N18.
      repeat (destruct CC as [CC|CC]; [subst rr; simp_regs; reflexivity|]). subst rr; simp_regs; reflexivity.
    - intros rr _ CC. repeat (destruct CC as [CC|CC]; [subst rr; simp_regs; reflexivity|]).
      subst rr; simp_regs; reflexivity. }
  assert (BLE3 : sb_le (sb_shift b A A4) (sb_mallocs b (sup_after_reply_sizes id verb))).
  { unfold sup_after_reply_sizes, sb_mallocs. cbn [fold_left].
    destruct BLK4 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A2 A4).
    rewrite <- (sb_shift_add (sb_shift b A A2) L2 A2 L4 A4 bl1 bl2 p2 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE2. }
  assert (RPC : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RPC.
  apply SR_ret.
  destruct (sinv_ret 8288 L A regs mem md O L4 A4 R5 m5 md4 _ _ b PRE SI5 RP5)
    as (POST' & GR' & ON' & BL' & OK' & RA' & F18' & RS').
  pose proof SI5 as (RJ5 & _).
  pose proof RJ5 as (_ & _ & _ & _ & _ & RG5 & _).
  unfold sup_after_reply_ret. rewrite SEGS. rewrite SEGS in OK'.
  exists fx', L4, A4, R5, m5, md4. eexists.
  split; [reflexivity|]. split; [exact FK|]. split; [exact POST'|].
  split; [unfold sup_after_reply_m; exact GR'|].
  split; [exact ON'|]. split; [exact BL'|]. split; [exact OK'|]. split; [exact RA'|]. split; [exact F18'|].
  split; [exact INI4|]. split; [exact RG5|]. split; [exact BLE3 | exact RS'].
Qed.

Theorem sup_after_reply_holds : sup_after_reply_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK RCF XSD ARGI.
  unfold sup_after_reply_contract.
  intros L A regs mem md id pv verb R O b PRE A0 HID A1 SA GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_AFTER_REPLY_K in PRE, PRK, HCEIL, HWS, SA.
  rewrite SEGS in GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API 8288 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8288) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  set (n := length (r_calls R)) in *.
  assert (NC : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact G3]).
  destruct (Nat.lt_ge_cases n 16) as [Hn|Hn].
  - destruct (glob_rw_cells mem (0x33d58 + 56 * Z.of_nat n) 8 ltac:(unfold GLOB_LO; lia)
                ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply sar_seg_lt; [exact ST | lia | lia | exact NC | exact Hn | exact EW]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1 & EN1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    pose proof (sinv_record_lt B API SEGS GOWN AX 8288 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                  REC_AFTER_REPLY SI0 Hn ltac:(unfold REC_FN_COUNT, REC_AFTER_REPLY; lia) MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EN1) as SI1.
    pose proof EN1 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
    apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
    apply (sar_arg L A regs mem md id pv verb R O b L A R1 m1 md O PRE A0 HID A1 SA RA FRM ROOM SI1
             ltac:(rewrite sb_shift_refl; apply sb_le_refl)).
    + rewrite (getr_of_eqv _ _ 1 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 4 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 8 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 9 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 10 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 11 X1 eq_refl). simp_regs. reflexivity.
    + pres_ex X1.
    + exact FR1.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn).
      replace (G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n + CALL_OFF_NARGS) with (0x33d58 + 56 * Z.of_nat n + Z.of_nat 4)
        by (unfold G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS; lia).
      exact EA.
  - assert (H16 : n = 16%nat) by lia.
    assert (NC16 : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 16)]) by (rewrite H16 in NC; exact NC).
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply sar_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16d90) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_9 : getr R1 9 = getr regs 11) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_18 : getr R1 18 = getr regs 10) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 0x33d10)
      by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
    assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    pose proof (sinv_stack B API SEGS GOWN AX 8288 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
    apply (sinv_rcf B API SEGS ERRNO_LOW GOTG GRD GOWN AX RCF 8288 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 _
             SI1 H16 E1_10 E1_11).
    + rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    + rewrite SP1. unfold RCF_K, ALLOC_STACK. lia.
    + rewrite SP1. lia.
    + rewrite E1_4. exact HTP.
    + intros L' A' regs' m' md' RP' POST FRK.
      rewrite E1_1.
      pose proof POST as (RJ' & _ & _ & _ & _ & RA' & _ & _ & BLE & _).
      destruct (mr_model B _ LAWS L' A' m' md' (proj1 RJ')) as (Hh' & Hl' & _).
      assert (R8' : getr regs' 8 = Z_to_bv 64 0x33d10) by exact (eq_trans (RP' 8 ltac:(unfold callee_saved; lia)) E1_8).
      assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 32)
                      [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
        apply FRK. rewrite SP1. lia. }
      destruct (glob_rw_cells m' 0x33d10 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
      eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of.
        assert (Q8 : reg_get regs' 8 = Z_to_bv 64 0x33d10) by exact R8'.
        rewrite Q8.
        eapply sar_ret16. exact EW. }
      intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX 8288 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                  _ REC_AFTER_REPLY POST ltac:(unfold REC_FN_COUNT, REC_AFTER_REPLY; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                      [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply (rw_cells_transport rsegs _ m' m2 _ _ FR' MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
        repeat split; lia. }
      pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
      apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
      rewrite sb_shift_refl in BLE.
      apply (sar_arg L A regs mem md id pv verb R O b L' A' R2 m2 md' Oc' PRE A0 HID A1 SA RA FRM ROOM SI2 BLE).
      * rewrite (getr_of_eqv _ _ 1 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 2 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
      * rewrite (getr_of_eqv _ _ 4 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 4 ltac:(unfold callee_saved; lia)) E1_4).
      * rewrite (rec_entry_full G_REC REC_SC R H16). rewrite (getr_of_eqv _ _ 8 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 9 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 9 ltac:(unfold callee_saved; lia)) E1_9).
      * rewrite (rec_entry_full G_REC REC_SC R H16). rewrite (getr_of_eqv _ _ 10 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 11 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 18 ltac:(unfold callee_saved; lia)) E1_18).
      * apply (sar_pres_mid regs R1 regs' R2 _ _ X1 RP' X2). ex_cases.
      * exact FR2.
      * rewrite (rec_entry_full G_REC REC_SC R H16).
        replace (REC_SC + CALL_OFF_NARGS) with (0x33d10 + Z.of_nat 4) by (unfold REC_SC, CALL_OFF_NARGS; lia).
        exact EA.
Qed.

End P.
