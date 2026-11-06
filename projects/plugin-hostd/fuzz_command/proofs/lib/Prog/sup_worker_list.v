(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecStub rec_shape_of_c.
Import ListNotations.
Open Scope Z_scope.

Lemma swl_pre_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists b0 b1 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n))
                     s1 b0 b1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1644c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp - 16)
       /\ rw_cells rsegs m' (bv_unsigned sp - 16) [C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16400) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 16%nat junk [] [8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 8 step.
  rewrite sx32_lit by lia.
  assert (C1 : negb (bv_eqb (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 16)) = true).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia. }
  rewrite C1. cbv iota.
  do 7 step.
  rewrite da_addr by lia.
  apply evt_done.
  do 3 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma swl_tail8 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (jk : list byte),
  rw_cells rsegs m e [CB 8 jk] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16464) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1
                     (Z_to_bv 64 0x1060b) (Z_to_bv 64 11) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1540c) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1644c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e jk EW MI.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  do 4 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma swl_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat) (jk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 jk] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16464) (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) s1 (Z_to_bv 64 0x1060b) (Z_to_bv 64 11)
                     a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1540c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ stk rsegs m' lo (bv_unsigned sp - 16)
       /\ rw_cells rsegs m' (bv_unsigned sp - 16) [C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16400) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n jk ST LO LO2 NC Hn EW MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply swl_pre_lt; [exact ST | exact LO | exact LO2 | exact NC | exact Hn | exact MI] |].
  intros ms1 (b0 & b1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & NC1).
  assert (EW1 : rw_cells rsegs m1 (0x33d58 + 56 * Z.of_nat n) [CB 8 jk]).
  { apply (rw_cells_transport rsegs [(bv_unsigned sp - 16, bv_unsigned sp); (0x33d50, 0x33d54)] m m1 _ _ EW MU1 WM1).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  eapply evt_cut; [eapply swl_tail8; [exact EW1 | exact MI1] |].
  intros ms2 (m2 & -> & MU2 & WM2 & MI2 & EN2).
  apply evt_done. exists m2. split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m2).
    - apply (munch_weaken [(bv_unsigned sp - 16, bv_unsigned sp); (0x33d50, 0x33d54)]); [|exact MU1].
      intros x (H1 & H2 & H3 & _). split; [exact H1 | split; [exact H2 | exact I]].
    - apply (munch_weaken [(0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)]); [|exact MU2].
      intros x (H1 & H2 & H3 & _). split; [exact H3 | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM1 WM2)|].
  split; [exact MI2|].
  split.
  { apply (stk_transport_disjoint rsegs _ m1 m2 _ _ ST1 MU2 WM2). cbn [disjoint_from]. repeat split; lia. }
  split.
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  split; [|exact EN2].
  apply (rw_cells_transport rsegs _ m1 m2 _ _ NC1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
  repeat split; lia.
Qed.

Lemma swl_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x1642c) (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     s1 (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 16)
       /\ rw_cells rsegs m' (bv_unsigned sp - 16) [C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16400) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 16%nat junk [] [8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 8 step.
  rewrite sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma swl_ret16 :
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 : word) (jk : list byte),
  rw_cells rsegs m 0x33d10 [CB 8 jk] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16464) (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1
                     (Z_to_bv 64 0x1060b) (Z_to_bv 64 11) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1540c) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 0)])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1642c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 jk EW MI.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(0x33d10, 0x33d10 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  do 4 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma swl_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 16) [C8 s00; C8 ra0] -> 16 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s1 s0 a0 (Z_to_bv 64 0) a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15bc8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16464) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 7 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 16 + 16)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma swl_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1060b (str_bytes "worker_list"%string).
Proof.
  intros m MI. apply rom_chk_bytes; [exact (ro_agree_of_inv m MI) | lia | cbn; lia | vm_compute; reflexivity].
Qed.

Lemma swl_shape : shape_find shape_rows (str_bytes "worker_list"%string) = 0x10384.
Proof. vm_compute. reflexivity. Qed.

Lemma swl_run_lt : rec_shape_of_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat) (jk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 jk] ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) (Z_to_bv 64 0x10384)
                     (Z_to_bv 64 0) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x15bc8) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16400) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n jk ST LO LO2 NC Hn EW GS MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  eapply evt_cut; [eapply swl_seg_lt; [exact ST | lia | lia | exact NC | exact Hn | exact EW | exact MI] |].
  intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & NC1 & EN1).
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 16)) = bv_unsigned sp - 16) by (apply unsigned_lit; lia).
  assert (GS1 : bytes_at rsegs m1 G_SHAPES g_shapes_bytes).
  { apply (bytes_at_transport rsegs _ m m1 _ _ GS MU1). rewrite GL. cbn [disjoint_from]. unfold G_SHAPES.
    repeat split; lia. }
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "worker_list"%string).
    - exact MI1.
    - rewrite SPU. exact ST1.
    - rewrite SPU. unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS1.
    - left. rewrite SPU. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (swl_verb m1 MI1)|].
      left. rewrite SPU. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  rewrite SPU in MU2. unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x16464) by lia. rewrite swl_shape.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply swl_tail; [exact FR2 | lia] |].
  intros ms3 ->. apply evt_done.
  exists m2, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m2).
    - apply (munch_weaken [(bv_unsigned sp - 16, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)]); [|exact MU1].
      intros x Hx. cbn in Hx |- *. repeat split; lia.
    - apply (munch_weaken [(bv_unsigned sp - 16 - 64, bv_unsigned sp - 16)]); [|exact MU2].
      intros x Hx. cbn in Hx |- *. repeat split; lia. }
  split; [exact (wmono_trans rsegs _ _ _ WM1 WM2)|].
  split.
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ NC1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  apply (rw_cells_transport rsegs _ m1 m2 _ _ EN1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
  repeat split; lia.
Qed.

Lemma swl_run16 : rec_shape_of_contract ->
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sp0 ra0 s00 : word) (jk : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 16) [C8 s00; C8 ra0] -> rw_cells rsegs m 0x33d10 [CB 8 jk] ->
  stk rsegs m lo (bv_unsigned sp0 - 16) -> lo + 80 <= bv_unsigned sp0 -> 0x34100 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s00 s1 (Z_to_bv 64 0x33d10) (Z_to_bv 64 0x10384)
                     (Z_to_bv 64 0) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x15bc8) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp0 - 80, bv_unsigned sp0 - 16); (0x33d10, 0x33d10 + 8)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 0)])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1642c) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sp0 ra0 s00 jk FR EW ST LO LO2 GS MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP.
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  eapply evt_cut; [eapply swl_ret16; [exact EW | exact MI] |].
  intros ms1 (m1 & -> & MU1 & WM1 & MI1 & EN1).
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 16)) = bv_unsigned sp0 - 16) by (apply unsigned_lit; lia).
  assert (GS1 : bytes_at rsegs m1 G_SHAPES g_shapes_bytes).
  { apply (bytes_at_transport rsegs _ m m1 _ _ GS MU1). rewrite GL. cbn [disjoint_from]. unfold G_SHAPES.
    repeat split; lia. }
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp0 - 16)).
  { apply (stk_transport_disjoint rsegs _ m m1 _ _ ST MU1 WM1). cbn [disjoint_from]. repeat split; lia. }
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp0 - 16) [C8 s00; C8 ra0]).
  { apply (rw_cells_transport rsegs _ m m1 _ _ FR MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "worker_list"%string).
    - exact MI1.
    - rewrite SPU. exact ST1.
    - rewrite SPU. unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS1.
    - left. rewrite SPU. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (swl_verb m1 MI1)|].
      left. rewrite SPU. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  rewrite SPU in MU2. unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x16464) by lia. rewrite swl_shape.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 16) [C8 s00; C8 ra0]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply swl_tail; [exact FR2 | lia] |].
  intros ms3 ->. apply evt_done.
  exists m2, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m2).
    - apply (munch_weaken [(0x33d10, 0x33d10 + 8)]); [|exact MU1].
      intros x Hx. cbn in Hx |- *. repeat split; lia.
    - apply (munch_weaken [(bv_unsigned sp0 - 16 - 64, bv_unsigned sp0 - 16)]); [|exact MU2].
      intros x Hx. cbn in Hx |- *. repeat split; lia. }
  split; [exact (wmono_trans rsegs _ _ _ WM1 WM2)|].
  apply (rw_cells_transport rsegs _ m1 m2 _ _ EN1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
  repeat split; lia.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecTail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import answer_c rec_calls_free_c sup_worker_list_c.

Lemma swl_ans_shape : forall m, ro_agree rsegs m -> ans_shape rsegs m 0x10384 (daemon_shape "worker_list").
Proof.
  intros m RA. change (daemon_shape "worker_list") with (shape_of (bstr "worker_list")).
  destruct (shape_of_facts (bstr "worker_list")) as (FT & _ & L78 & N0).
  apply ans_shape_chk; [exact RA | lia | lia | vm_compute; reflexivity | exact N0 | unfold LMAX; lia | exact FT].
Qed.

Lemma swl_inst_len : (length (inst (daemon_shape "worker_list")) <= 24)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis ANS : answer_contract B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Theorem sup_worker_list_holds : sup_worker_list_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GOWN AX CTX SLACK RCF ANS RSO RIMG RFREE.
  unfold sup_worker_list_contract.
  intros L A regs mem md R O b PRE GS GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_WORKER_LIST_K in HCEIL, HWS.
  rewrite SEGS in GS, GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API SUP_WORKER_LIST_K L A regs mem md R O b PRK ltac:(unfold SUP_WORKER_LIST_K; lia)
                GR RA F18 RES) as SI0.
  unfold SUP_WORKER_LIST_K in SI0.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 12384) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  assert (STn : stk rsegs (normalize rsegs mem) (bv_unsigned sp - 12384) (bv_unsigned sp))
    by (apply stk_norm; [lia | lia | intros a Ha; apply HWS; lia]).
  pose proof (bytes_at_normalize rsegs mem _ _ RA GS) as GSn.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  assert (LT : (length (snd (rec_answer (rec_record R REC_WORKER_LIST []) (REC_WORKER_LIST, [])
                  (daemon_shape "worker_list") false)) <= 24)%nat).
  { pose proof (stub_len2 R REC_WORKER_LIST [] (daemon_shape "worker_list") false HCODE) as H.
    pose proof swl_inst_len. lia. }
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  set (n := length (r_calls R)) in *.
  assert (NC : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact G3]).
  destruct (Nat.lt_ge_cases n 16) as [Hn|Hn].
  - assert (NCn : rw_cells rsegs (normalize rsegs mem) 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))]).
    { apply rw_cells_normalize; [exact RA | exact NC |]. intros i Hi. cbn in Hi.
      apply glob_ro_false. unfold GLOB_LO, GLOB_N. lia. }
    destruct (glob_rw_cells (normalize rsegs mem) (0x33d58 + 56 * Z.of_nat n) 8 ltac:(unfold GLOB_LO; lia)
                ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply (evt_normalize rsegs); [exact WX | exact RA |].
      eapply (swl_run_lt RSO); [exact STn | lia | lia | exact NCn | exact Hn | exact EW | exact GSn |
        apply mem_inv_normalize]. }
    intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
    destruct Q1 as (m1n & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU1n & WM1n
      & NC1n & EN1n).
    destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
    revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
    pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
    pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
    pose proof (rw_cells_rel rsegs _ _ _ _ MR1r NC1n) as NC1.
    pose proof (rw_cells_rel rsegs _ _ _ _ MR1r EN1n) as EN1.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    pose proof (sinv_record_lt B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                  REC_WORKER_LIST SI0 Hn ltac:(unfold REC_FN_COUNT, REC_WORKER_LIST; lia) MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EN1) as SI1.
    assert (E1 : getr R1 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E2 : getr R1 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E10 : getr R1 10 = Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n))
      by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (E11 : getr R1 11 = Z_to_bv 64 0x10384) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
    assert (E12 : getr R1 12 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 12 X1 eq_refl); simp_regs; reflexivity).
    assert (RP1 : regs_preserved regs R1) by pres_tac X1.
    eapply SR_mono.
    { apply (sinv_answer B API SEGS ERRNO_LOW AX CTX ANS SLACK 12384 L A regs mem md O L A R1 m1 md
               (rec_record R REC_WORKER_LIST []) O b b (0x33d58 + 56 * Z.of_nat n) 0x10384 (REC_WORKER_LIST, [])
               (daemon_shape "worker_list") false PRE AK SI1 E1 ltac:(unfold spZ; rewrite E2; reflexivity) RP1 E10 E11
               ltac:(rewrite E12; reflexivity)).
      - intros _. apply swl_ans_shape. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 SI1)))))).
      - intros _ H. discriminate H.
      - exact FRM.
      - rewrite sb_shift_refl. apply sb_le_refl.
      - rewrite sb_shift_refl. apply (room_down b b _ 25 (sb_le_refl b)); [lia | exact ROOM]. }
    intros c' TR.
    destruct TR as (fx' & L' & A' & regs' & mem' & md' & O' & q & -> & FK & POST & A10' & GR' & ON' & BL' & IN' & FB'
      & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
    exists fx', L', A', regs', mem', md', (fst (sup_worker_list_m R)), O', (snd (sup_worker_list_m R)), q.
    split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK|]. split; [exact POST|].
    do 10 (split; [assumption|]).
    split.
    { rewrite SEGS. apply (shapes_kept B API SEGS RIMG RFREE _ L A regs mem md _ _ L' A' regs' mem' md' PRK POST);
        [|exact GS]. intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
    repeat (split; [assumption|]). exact RES'.
  - assert (H16 : n = 16%nat) by lia.
    assert (NC16 : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 16)]) by (rewrite H16 in NC; exact NC).
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply swl_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x1642c) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 16))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 0x33d10)
      by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
    assert (SP1 : spZ R1 = bv_unsigned sp - 16) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
    apply (sinv_rcf B API SEGS ERRNO_LOW GOTG GRD GOWN AX RCF 12384 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 _
             SI1 H16 E1_10 E1_11).
    + rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP1. replace (bv_unsigned sp - 16) with (bv_unsigned sp + (-1) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    + rewrite SP1. unfold RCF_K, ALLOC_STACK. lia.
    + rewrite SP1. lia.
    + rewrite E1_4. exact HTP.
    + intros L' A' regs' m' md' RP' POST FRK.
      rewrite E1_1.
      pose proof POST as (RJ' & _ & _ & _ & _ & RA' & _ & _ & BLE & _).
      pose proof RJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC' & _).
      destruct (mr_model B _ LAWS L' A' m' md' (proj1 RJ')) as (Hh' & Hl' & _).
      assert (R2' : getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16))
        by exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
      assert (R8' : getr regs' 8 = Z_to_bv 64 0x33d10) by exact (eq_trans (RP' 8 ltac:(unfold callee_saved; lia)) E1_8).
      assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
        apply FRK. rewrite SP1. lia. }
      assert (FRn : rw_cells rsegs (normalize rsegs m') (bv_unsigned sp - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply rw_cells_normalize; [exact RA' | exact FR' |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
      assert (STn' : stk rsegs (normalize rsegs m') (bv_unsigned sp - 12384) (bv_unsigned sp - 16)).
      { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC'. left. lia. }
      pose proof (bytes_at_normalize rsegs m' _ _ RA'
                    (rjr_shapes B API SEGS RIMG 12384 (bv_unsigned sp) O L A mem md L' A' m' md' RJ' GS)) as GSn'.
      destruct (glob_rw_cells (normalize rsegs m') 0x33d10 8 ltac:(unfold GLOB_LO; lia)
                  ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
      eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of.
        assert (Q2 : reg_get regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)) by exact R2'.
        assert (Q8 : reg_get regs' 8 = Z_to_bv 64 0x33d10) by exact R8'.
        rewrite Q2, Q8.
        eapply (evt_normalize rsegs); [exact WX | exact RA' |].
        eapply (swl_run16 RSO); [exact FRn | exact EW | exact STn' | lia | lia | exact GSn' | apply mem_inv_normalize]. }
      intros ms2 (can2 & (s2n & Q2 & REL2 & RO2) & EQ2).
      destruct Q2 as (m2n & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU2n & WM2n
        & EN2n).
      destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL2) as [EC2 MR2r].
      revert EC2 MR2r RO2 EQ2. generalize (ms_mem can2) as m2. intros m2 EC2 MR2r RO2 EQ2. subst can2.
      pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m' RA') MR2r RO2 MU2n) as MU2.
      pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m' RA') MR2r RO2 WM2n) as WM2.
      pose proof (rw_cells_rel rsegs _ _ _ _ MR2r EN2n) as EN2.
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                  _ REC_WORKER_LIST POST ltac:(unfold REC_FN_COUNT, REC_WORKER_LIST; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      assert (E2_1 : getr R2 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
      assert (E2_2 : getr R2 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; reflexivity).
      assert (E2_10 : getr R2 10 = Z_to_bv 64 0x33d10)
        by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; reflexivity).
      assert (E2_11 : getr R2 11 = Z_to_bv 64 0x10384)
        by (rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs; reflexivity).
      assert (E2_12 : getr R2 12 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 12 X2 eq_refl); simp_regs; reflexivity).
      assert (RP2 : regs_preserved regs R2).
      { apply (preserved_chain (fun r => orb (r =? 2) (r =? 8)) regs R1 regs' R2 _ _ X1 RP' X2); chain_tac. }
      eapply SR_mono.
      { apply (sinv_answer B API SEGS ERRNO_LOW AX CTX ANS SLACK 12384 L A regs mem md O L' A' R2 m2 md'
                 (rec_record R REC_WORKER_LIST []) Oc' b b 0x33d10 0x10384 (REC_WORKER_LIST, [])
                 (daemon_shape "worker_list") false
                 PRE AK SI2 E2_1 ltac:(unfold spZ; rewrite E2_2; reflexivity) RP2 E2_10 E2_11
                 ltac:(rewrite E2_12; reflexivity)).
        - intros _. apply swl_ans_shape. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 SI2)))))).
        - intros _ H. discriminate H.
        - exact FRM.
        - rewrite sb_shift_refl in BLE. exact BLE.
        - rewrite sb_shift_refl in BLE. apply (room_down _ b _ 25 BLE); [lia | exact ROOM]. }
      intros c' TR.
      destruct TR as (fx' & L'' & A'' & regs'' & mem'' & md'' & O'' & q & -> & FK & POST' & A10' & GR' & ON' & BL'
        & IN' & FB' & NQ' & BY' & OK' & AP' & RA'' & F18' & INI' & REG' & BLE' & RES').
      exists fx', L'', A'', regs'', mem'', md'', (fst (sup_worker_list_m R)), O'', (snd (sup_worker_list_m R)), q.
      split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK|]. split; [exact POST'|].
      do 10 (split; [assumption|]).
      split.
      { rewrite SEGS. apply (shapes_kept B API SEGS RIMG RFREE _ L A regs mem md _ _ L'' A'' regs'' mem'' md'' PRK POST');
          [|exact GS]. intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
      repeat (split; [assumption|]). exact RES'.
Qed.

End P.
