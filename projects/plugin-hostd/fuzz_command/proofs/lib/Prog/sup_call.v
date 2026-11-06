(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module names, addresses and numbers changed; 444 of its 663 lines of code are new or changed and 329 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecStub.
Import ListNotations.
Open Scope Z_scope.

Lemma sc_pre_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n))
                     a1 b0 b1 b2 a3 a4 a5 a6 a7 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15e1c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15dc0) fc None m (seg_rom rsegs)).
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

Lemma sc_rec :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (jk : list byte),
  rw_cells rsegs m e [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x15e30) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1
                     (Z_to_bv 64 e) s2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b1c) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15e1c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e jk EW.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  do 3 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma sc_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat) (jk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 jk] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x15e30) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a1 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a0
                     b2 a3 a4 a5 a6 a7 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b1c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15dc0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n jk ST LO LO2 NC Hn EW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply sc_pre_lt; [exact ST | exact LO | exact LO2 | exact NC | exact Hn] |].
  intros ms1 (b0 & b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1).
  assert (EW1 : rw_cells rsegs m1 (0x33d58 + 56 * Z.of_nat n) [CB 8 jk]).
  { apply (rw_cells_transport rsegs [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m1 _ _ EW MU1 WM1).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  eapply evt_cut; [eapply sc_rec; exact EW1 |].
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

Lemma sc_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x15dfc) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     a1 (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) b2 a3 a4 a5 a6 a7
                     a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15dc0) fc None m (seg_rom rsegs)).
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

Lemma sc_ret16 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (jk : list byte),
  rw_cells rsegs m 0x33d10 [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x15e30) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1
                     (Z_to_bv 64 0x33d10) s2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b1c) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15dfc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m jk EW.
  step.
  eapply sc_rec. exact EW.
Qed.

Lemma sc_mid :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x15e3c) sp gp tp t0 t1 t2 s0 s1 s0 s1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15e64) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15e30) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step.
  apply evt_done. reflexivity.
Qed.

Lemma sc_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' s20 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' s0 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                                    a3 a4 a5 a6 a7 s20 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15bc8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15e3c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' s20 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 10 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecTail RecAnsB RecCore.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import answer_c rec_calls_free_c arg_i_c arg_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import rec_canonical_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import sup_call_c.

Lemma sc_nra_apart : forall s Ln lo hi, (forall a, s <= a < s + Ln -> ~ rec_area a) ->
  REC_SC <= lo -> hi <= G_REC + REC_SIZE -> lo < hi -> 0 < Ln -> s + Ln <= lo \/ hi <= s.
Proof.
  intros s Ln lo hi H H1 H2 H3 H4. destruct (Z_le_gt_dec (s + Ln) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi s) as [D'|D']; [right; exact D'|]. exfalso.
  unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in *.
  destruct (Z_le_gt_dec s lo) as [D1|D1].
  - apply (H lo); [lia|]. destruct (Z_lt_ge_dec lo 212296); [left | right]; lia.
  - apply (H s); [lia|]. destruct (Z_lt_ge_dec s 212296); [left | right]; lia.
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis ANSF : forall fx0 : YK11.FPState, answer_contract (fx := fx0) B API.
Hypothesis ARGI : arg_i_contract B API.
Hypothesis ARGL : forall fx0 : YK11.FPState, arg_line_contract (fx := fx0) B API.

Lemma sc_home_lower : forall L A sp1 sp2 s n, sp2 <= sp1 -> str_home B L A sp1 s n -> str_home B L A sp2 s n.
Proof.
  intros L A sp1 sp2 s n H [H1|[H1|H1]]; [left; lia | right; left; exact H1 | right; right; exact H1].
Qed.

Lemma sc_line : forall (fx' : YK11.FPState) L A regs mem md id pl line R O b L2 A2 R2 m2 md2 Oc2,
  call_pre_t B API 12384 L A regs mem md ->
  str_arg B L A O (spZ regs) 12384 mem pl (Some line) -> ro_agree rsegs mem ->
  room_slots (sb_mallocs b (sup_call_sizes id line (snd (sup_call_m R id line)))) (LMAX + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O L2 A2 m2 md2 (rec_record R REC_CALL [dec id]) Oc2 b ->
  sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length (dec id)) + 1)) ->
  (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  fp_kept fx fx' ->
  getr R2 2 = Z_to_bv 64 (spZ regs - 32) -> getr R2 4 = getr regs 4 ->
  getr R2 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R2 9 = Z_to_bv 64 pl ->
  kept_ex [2; 8; 9; 18] regs R2 ->
  rw_cells rsegs m2 (spZ regs - 32)
    [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs m2 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 1)) ->
  SR rsegs (mkCfg (@mkst fx' R2 (Z_to_bv 64 0x15e30) m2 (seg_rom rsegs)) md2)
    (sup_call_ret (fx := fx) B API L A regs mem md id line R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK ANSF ARGL.
  intros fx' L A regs mem md id pl line R O b L2 A2 R2 m2 md2 Oc2 PRE SA RA ROOM SI2 BLE2 HN HCODE FK
    R2_2 R2_4 R2_8 R2_9 KE2 FR2 NA2.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  change (snd (sup_call_m R id line)) with
    (snd (rec_answer (rec_record R REC_CALL [dec id; canon line]) (REC_CALL, [dec id; canon line])
           REC_MOD_HOST_SHAPE true)) in ROOM.
  unfold sup_call_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_CALL [dec id; canon line]) (REC_CALL, [dec id; canon line])
                  REC_MOD_HOST_SHAPE true)) <= 16)%nat).
  { pose proof (stub_len R REC_CALL [dec id; canon line] REC_MOD_HOST_SHAPE true HCODE) as H.
    assert (LX6 : length REC_MOD_HOST_SHAPE = 6%nat) by (vm_compute; reflexivity).
    rewrite LX6 in H. exact H. }
  assert (ER : rec_entry G_REC REC_SC R mod 8 = 0 /\ REC_SC <= rec_entry G_REC REC_SC R /\
               rec_entry G_REC REC_SC R + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE, REC_SC, REC_SIZE.
      split; [|lia]. apply Z.mod_divide; [lia|]. exists (26539 + 7 * Z.of_nat (length (r_calls R))). lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. split; [reflexivity | lia]. }
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof SI2 as (RJ2 & _ & _ & _ & _ & RA2 & F182 & RS2).
  pose proof RJ2 as (HM2 & _).
  assert (Hp0 : pl <> 0) by exact (proj1 SA).
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 _ Oc2 b pl (Some line)
              SI2 RA ltac:(unfold NULL_LIT; lia) SA)
    as (s & slack & P0 & PS & S0 & BS & N0 & LX & ALN & DJ & HOME & NRA).
  change (sarg (Some line)) with line in BS, N0, LX, ALN, DJ, HOME, NRA.
  assert (ES : s = pl) by (rewrite <- PS; destruct (Z.eqb_spec pl 0); [contradiction | reflexivity]).
  clear PS. subst s.
  destruct (mr_model B _ LAWS L2 A2 m2 md2 HM2) as (Hh2 & Hl2 & _).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply sc_mid. }
  intros ms3 (can3 & -> & EQ3).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x15e3c) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; exact R2_2).
  assert (E3_4 : getr R3 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; exact R2_4).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs; exact R2_8).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact R2_8).
  assert (E3_11 : getr R3 11 = Z_to_bv 64 pl) by (rewrite (getr_of_eqv _ _ 11 X3 eq_refl); simp_regs; exact R2_9).
  assert (SP3 : spZ R3 = bv_unsigned sp - 32) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  pose proof (ARGL fx') as AL. unfold arg_line_contract in AL. rewrite SEGS in AL.
  eapply SR_bind.
  { apply (AL L2 A2 R3 m2 md2 e pl 1 line slack (sb_shift b A A2)).
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m2 md2 ARG_LINE_K R3 RJ2).
      + rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP3. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
      + rewrite SP3. unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
      + rewrite SP3. lia.
      + rewrite E3_4. exact HTP.
    - exact E3_10.
    - exact E3_11.
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - exact (proj2 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact NA2.
    - lia.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact ALN.
    - rewrite SP3. unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
    - rewrite SP3. apply (sc_home_lower L2 A2 (bv_unsigned sp)); [lia | exact HOME].
    - unfold iv_apart. apply (sc_nra_apart pl _ e (e + CALL_SIZE)).
      + intros a Ha. apply NRA. rewrite length_app. cbn [length]. lia.
      + exact (proj1 (proj2 ER)).
      + exact (proj2 (proj2 ER)).
      + unfold CALL_SIZE. lia.
      + lia.
    - exact RS2.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE2|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + unfold LMAX in *. lia.
    - exact RA2. }
  intros c3 (L3 & A3 & R4 & m3 & md3 & -> & BK3 & UB3 & _ & RA3 & GK3 & RGN3 & ALT3).
  destruct ALT3 as [(H6 & _)|(_ & p2 & POST3 & Hp2 & _ & FB3 & BLK3 & BN3 & BS3 & BX3 & INI3 & RS3)]; [lia|].
  rewrite SEGS in RA3, BN3, BS3, BX3 |- *.
  pose proof POST3 as (PM3 & _ & _ & _ & _ & RP4 & _).
  destruct (ax_statics AX L3 A3 m3 md3 PM3) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F183 : f18_words rsegs m3).
  { apply (f18_words_after m2 m3 g F182); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK3 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 R
                REC_CALL [dec id] Oc2 b ARG_LINE_K R3 _ L3 A3 R4 m3 md3 (canon line) p2 (Z.of_nat (length line) + 1)
                SI2 ltac:(cbn; lia) ltac:(rewrite SP3; unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK; lia)
                ltac:(rewrite SP3; lia) POST3
                ltac:(intros a Ha; cbv beta in Ha; change (Z.of_nat (length [dec id])) with 1; lia)
                Hp2 FB3 BLK3 UB3 BK3 RGN3 BN3 BS3 BX3 (canon_no0 line N0)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                INI3 RS3 RA3 F183) as SI3.
  cbn [app] in SI3.
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi.
    destruct FB3 as (_ & FBb & _).
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_LINE_K L2 A2 R3 m2 md2 _ L3 A3 R4 m3 md3 (bv_unsigned sp - 32 + i)
                HM2 POST3 ltac:(lia) ltac:(rewrite SP3; unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK; lia))
      as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (R4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (R4_8 : getr R4 8 = Z_to_bv 64 e) by exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) E3_8).
  assert (BLE3 : sb_le (sb_shift b A A3)
                   (sb_malloc (sb_malloc b (Z.of_nat (length (dec id)) + 1)) (Z.of_nat (length line) + 1))).
  { destruct BLK3 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A2 A3).
    rewrite <- (sb_shift_add (sb_shift b A A2) L2 A2 L3 A3 bl1 bl2 p2 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE2. }
  destruct (mr_model B _ LAWS L3 A3 m3 md3 PM3) as (Hh3 & Hl3 & _).
  rewrite E3_1.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 32)) by exact R4_2.
    rewrite Q2.
    eapply sc_tail; [exact FR3 | lia]. }
  intros ms5 (can5 & -> & EQ5).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  assert (E5_1 : getr R5 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_2 : getr R5 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_10 : getr R5 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; exact R4_8).
  assert (E5_11 : getr R5 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_12 : getr R5 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X5 eq_refl); simp_regs; reflexivity).
  assert (RP5 : regs_preserved regs R5).
  { apply (kept_ex_pres [2; 8; 9; 18]).
    - apply (kept_ex_trans _ regs R2 R5 KE2).
      apply (kept_ex_trans _ R2 R3 R5); [kept_ex_tac X3|].
      apply (kept_ex_trans _ R3 R4 R5 (kept_ex_of_pres _ _ _ RP4)).
      kept_ex_tac X5.
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X5 eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  eapply SR_mono.
  { apply (sinv_answer (fx := fx') B API SEGS ERRNO_LOW AX CTX (ANSF fx') SLACK 12384 L A regs mem md O L3 A3 R5 m3 md3
             (rec_record R REC_CALL [dec id; canon line]) (Oc2 ++ [(p2, Z.of_nat (length line) + 1)]) b
             (sb_malloc (sb_malloc b (Z.of_nat (length (dec id)) + 1)) (Z.of_nat (length line) + 1)) e 0x10417
             (REC_CALL, [dec id; canon line]) REC_MOD_HOST_SHAPE true PRE AK SI3 E5_1
             ltac:(unfold spZ; rewrite E5_2; reflexivity) RP5 E5_10 E5_11 ltac:(rewrite E5_12; reflexivity)).
    - intros _. apply mod_host_shape. exact RA3.
    - intros _ _. exact (ans_entry_record R REC_CALL [dec id; canon line] HN).
    - exact (proj1 FK).
    - exact BLE3.
    - eapply room_slots_mono; [| | exact ROOM].
      + apply sb_malloc_mono, sb_malloc_mono. exact BLE3.
      + unfold LMAX. lia. }
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  exists fx'', L', A', regs', mem', md', (fst (sup_call_m R id line)), O', (snd (sup_call_m R id line)), q.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact (fpk_trans _ _ _ FK FK')|].
  split; [exact POST'|].
  repeat (split; [assumption|]). exact RES'.
Qed.

Lemma sc_arg : forall L A regs mem md id pl line R O b Lc Ac R1 m1 md1 Oc,
  call_pre_t B API 12384 L A regs mem md -> getr regs 10 = Z_to_bv 64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
  getr regs 11 = Z_to_bv 64 pl -> str_arg B L A O (spZ regs) 12384 mem pl (Some line) -> ro_agree rsegs mem ->
  frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_call_sizes id line (snd (sup_call_m R id line)))) (LMAX + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O Lc Ac m1 md1 (rec_record R REC_CALL []) Oc b ->
  sb_le (sb_shift b A Ac) b -> (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  getr R1 1 = Z_to_bv 64 0x15e30 -> getr R1 2 = Z_to_bv 64 (spZ regs - 32) -> getr R1 4 = getr regs 4 ->
  getr R1 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R1 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R1 11 = getr regs 10 -> getr R1 9 = getr regs 11 ->
  kept_ex [2; 8; 9; 18] regs R1 ->
  rw_cells rsegs m1 (spZ regs - 32)
    [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs m1 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 0)) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15b1c) m1 (seg_rom rsegs)) md1)
    (sup_call_ret B API L A regs mem md id line R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK ANSF ARGI ARGL.
  intros L A regs mem md id pl line R O b Lc Ac R1 m1 md1 Oc PRE A0 HID A1 SA RA FRM ROOM SI1 BLE1 HN HCODE
    E1 E2 E4 E8 E10 E11 E9 KE1 FR1 NA1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof ROOM as ROOM0.
  change (snd (sup_call_m R id line)) with
    (snd (rec_answer (rec_record R REC_CALL [dec id; canon line]) (REC_CALL, [dec id; canon line])
           REC_MOD_HOST_SHAPE true)) in ROOM0.
  unfold sup_call_sizes, sb_mallocs in ROOM0. cbn [fold_left] in ROOM0.
  pose proof (dec_length id HID) as DL.
  assert (ER : rec_entry G_REC REC_SC R mod 8 = 0 /\ REC_SC <= rec_entry G_REC REC_SC R /\
               rec_entry G_REC REC_SC R + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE, REC_SC, REC_SIZE.
      split; [|lia]. apply Z.mod_divide; [lia|]. exists (26539 + 7 * Z.of_nat (length (r_calls R))). lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. split; [reflexivity | lia]. }
  set (e := rec_entry G_REC REC_SC R) in *.
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
      apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md Lc Ac m1 md1 ARG_I_K R1 RJ1).
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
    - eapply room_slots_mono; [| | exact ROOM0].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE1|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + unfold LMAX. lia.
    - exact RA1. }
  intros c2 (fx' & L2 & A2 & R2 & m2 & md2 & -> & FK & BK2 & UB2 & _ & RA2 & _ & F182 & RGN2 & ALT).
  destruct ALT as [(H06 & _)|(_ & p & POST2 & Hp0 & _ & FB2 & BLK2 & BN2 & BS2 & BX2 & INI2 & RS2)]; [lia|].
  rewrite SEGS in RA2, F182, BN2, BS2, BX2 |- *.
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O Lc Ac m1 md1 R
                REC_CALL [] Oc b ARG_I_K R1 _ L2 A2 R2 m2 md2 (dec id) p (Z.of_nat (length (dec id)) + 1)
                SI1 ltac:(cbn; lia) ltac:(rewrite SP1; unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK; lia)
                ltac:(rewrite SP1; lia) POST2 ltac:(intros a Ha; cbv beta in Ha; cbn [length Z.of_nat]; lia)
                Hp0 FB2 BLK2 UB2 BK2 RGN2 BN2 BS2 BX2 (dec_no0 id) ltac:(unfold LMAX; lia) ltac:(unfold LMAX; lia)
                INI2 RS2 RA2 F182) as SI2.
  cbn [app] in SI2.
  pose proof POST2 as (PM2 & _ & _ & _ & _ & RP2 & _).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct FB2 as (_ & FBb & _).
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_I_K Lc Ac R1 m1 md1 _ L2 A2 R2 m2 md2 (bv_unsigned sp - 32 + i)
                HM1 POST2 ltac:(lia) ltac:(rewrite SP1; lia)) as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (BLE2 : sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length (dec id)) + 1))).
  { destruct BLK2 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A Ac A2).
    rewrite <- (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2 bl1 bl2 p _ EB1 EB2).
    apply sb_malloc_mono. exact BLE1. }
  rewrite E1.
  apply (sc_line fx' L A regs mem md id pl line R O b L2 A2 R2 m2 md2 _ PRE SA RA ROOM SI2 BLE2 HN HCODE FK).
  - exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E2).
  - exact (eq_trans (RP2 4 ltac:(unfold callee_saved; lia)) E4).
  - exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E8).
  - exact (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) (eq_trans E9 A1)).
  - exact (kept_ex_trans _ regs R1 R2 KE1 (kept_ex_of_pres _ _ _ RP2)).
  - exact FR2.
  - exact BN2.
Qed.

Theorem sup_call_holds : sup_call_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK RCF ANSF ARGI ARGL.
  unfold sup_call_contract.
  intros L A regs mem md id pl line R O b PRE A0 HID A1 SA GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_CALL_K in PRE, PRK, HCEIL, HWS, SA.
  rewrite SEGS in GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API 12384 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 12384) (bv_unsigned sp)).
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
      eapply sc_seg_lt; [exact ST | lia | lia | exact NC | exact Hn | exact EW]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1 & EN1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    pose proof (sinv_record_lt B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                  REC_CALL SI0 Hn ltac:(unfold REC_FN_COUNT, REC_CALL; lia) MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EN1) as SI1.
    pose proof EN1 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
    apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
    apply (sc_arg L A regs mem md id pl line R O b L A R1 m1 md O PRE A0 HID A1 SA RA FRM ROOM SI1
             ltac:(rewrite sb_shift_refl; apply sb_le_refl) ltac:(lia) HCODE).
    + rewrite (getr_of_eqv _ _ 1 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 4 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 8 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 10 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 11 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 9 X1 eq_refl). simp_regs. reflexivity.
    + kept_ex_tac X1.
    + exact FR1.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn).
      replace (G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n + CALL_OFF_NARGS) with (0x33d58 + 56 * Z.of_nat n + Z.of_nat 4)
        by (unfold G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS; lia).
      exact EA.
  - assert (H16 : n = 16%nat) by lia.
    assert (NC16 : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 16)]) by (rewrite H16 in NC; exact NC).
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply sc_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x15dfc) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
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
    pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
    apply (sinv_rcf B API SEGS ERRNO_LOW GOTG GRD GOWN AX RCF 12384 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 _
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
        eapply sc_ret16. exact EW. }
      intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                  _ REC_CALL POST ltac:(unfold REC_FN_COUNT, REC_CALL; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                      [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply (rw_cells_transport rsegs _ m' m2 _ _ FR' MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
        repeat split; lia. }
      pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
      apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
      rewrite sb_shift_refl in BLE.
      apply (sc_arg L A regs mem md id pl line R O b L' A' R2 m2 md' Oc' PRE A0 HID A1 SA RA FRM ROOM SI2 BLE
               ltac:(lia) HCODE).
      * rewrite (getr_of_eqv _ _ 1 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 2 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
      * rewrite (getr_of_eqv _ _ 4 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 4 ltac:(unfold callee_saved; lia)) E1_4).
      * rewrite (rec_entry_full G_REC REC_SC R H16). rewrite (getr_of_eqv _ _ 8 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (rec_entry_full G_REC REC_SC R H16). rewrite (getr_of_eqv _ _ 10 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 11 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 18 ltac:(unfold callee_saved; lia)) E1_18).
      * rewrite (getr_of_eqv _ _ 9 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 9 ltac:(unfold callee_saved; lia)) E1_9).
      * apply (kept_ex_trans _ regs R1 R2); [kept_ex_tac X1|].
        apply (kept_ex_trans _ R1 regs' R2 (kept_ex_of_pres _ _ _ RP')). kept_ex_tac X2.
      * exact FR2.
      * rewrite (rec_entry_full G_REC REC_SC R H16).
        replace (REC_SC + CALL_OFF_NARGS) with (0x33d10 + Z.of_nat 4) by (unfold REC_SC, CALL_OFF_NARGS; lia).
        exact EA.
Qed.

End P.
