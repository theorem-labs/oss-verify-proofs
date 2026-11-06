(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module names, addresses and numbers changed; 1760 of its 2082 lines of code are new or changed and 2420 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecCore.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts printf_facts_c snprintf_c mix_call_c RecAns.
Import ListNotations.
Open Scope Z_scope.

Definition sa_sel (p d : Z) : Z := if p =? 0 then d else p.

Ltac sa_lits :=
  fold_lit_ux;
  repeat match goal with
  | |- context [Z.shiftl ?a ?b] => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  end;
  rewrite ?Z.add_0_r.

Lemma sa_nz_true : forall p, 0 <= p < 2 ^ 64 -> p <> 0 -> negb (bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0)) = true.
Proof.
  intros p Hp N. unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia.
Qed.

Lemma sa_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 a1 (Z_to_bv 64 0x33d10)
                     b0 b1 b2 a3 a4 a5 a6 a7 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a3 a2 a0
                     s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x159c0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 96)
       /\ rw_cells rsegs m' (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1594c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 56%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 56%nat junk [] [8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  carve_frame 40%nat ST.
  clear FR0.
  do 17 step.
  rewrite rc_sx32_lit by lia.
  assert (C1 : negb (bv_eqb (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 16)) = true).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia. }
  rewrite C1. cbv iota.
  do 7 step.
  rewrite rc_slot_addr by lia.
  apply evt_done.
  do 4 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma sa_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x1599c) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 a1 (Z_to_bv 64 0x33d10)
                     (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) (Z_to_bv 64 16) a3 a4 a5 a6 a7 s2 a3 a2 a0
                     s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 96)
       /\ rw_cells rsegs m' (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1594c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 56%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 56%nat junk [] [8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  carve_frame 40%nat ST.
  clear FR0.
  do 17 step.
  rewrite rc_sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma sa_seg_rec :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e pu : Z) (junk : list byte),
  rw_cells rsegs m e [CB 8 junk] -> 0 <= pu < 2 ^ 64 ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x159d8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sa_sel pu 0x10a19)) a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 e) s3 s4 (Z_to_bv 64 (sa_sel pu 0x10a19)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) s3 s4 (Z_to_bv 64 pu)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x159c0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e pu junk EW Hpu.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  apply (rc_cells_rebytes _ _ _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  step.
  unfold sa_sel. destruct (Z.eqb_spec pu 0) as [E0|E0].
  - subst pu. if_false. do 4 step.
    apply evt_done. eexists. split; [reflexivity|]. split; [eassumption|]. split; eassumption.
  - rewrite (sa_nz_true pu Hpu E0). cbv iota. do 2 step.
    apply evt_done. eexists. split; [reflexivity|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma sa_seg_jrec :
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (pu : Z) (junk : list byte),
  rw_cells rsegs m 0x33d10 [CB 8 junk] -> 0 <= pu < 2 ^ 64 ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x159d8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x33d10) (Z_to_bv 64 (sa_sel pu 0x10a19))
                     a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x33d10) s3 s4 (Z_to_bv 64 (sa_sel pu 0x10a19))
                     s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x33d10) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 pu)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1599c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pu junk EW Hpu.
  do 2 step. eapply sa_seg_rec; [exact EW | exact Hpu].
Qed.

Lemma sa_seg_a0 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e p : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 0)] -> rw_cells rsegs m (e + 8) [CB 8 junk] ->
  0 <= p < 2 ^ 64 ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x15a00) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) s0 b2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 e) s3 s4 (Z_to_bv 64 (e + 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b1c) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 16)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 1)]
       /\ rw_cells rsegs m' (e + 8) [C8 (Z_to_bv 64 p)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) s3 s4 s5
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x159d8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e p junk EN EA Hp.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. try (rewrite rc_sx32_lit by lia).
  do 4 step. sa_lits.
  do 5 step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma sa_seg_a1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e pl : Z),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 2)] -> 0 <= pl < 2 ^ 64 ->
  evt rsegs (fun ms' => exists b1,
       ms' = MS (mkR (Z_to_bv 64 0x15a20) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sa_sel pl 0x108b0)) b1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 e) s3 (Z_to_bv 64 (sa_sel pl 0x108b0)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) s3 (Z_to_bv 64 pl) s5
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a00) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e pl EN Hpl.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  step. rewrite rc_sx32_lit by lia.
  do 2 step. if_false.
  step.
  unfold sa_sel. destruct (Z.eqb_spec pl 0) as [E0|E0].
  - subst pl. if_false. do 4 step.
    apply evt_done. eexists. reflexivity.
  - rewrite (sa_nz_true pl Hpl E0). cbv iota. do 2 step.
    apply evt_done. eexists. reflexivity.
Qed.

Lemma sa_seg_a2 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e p pc : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 2)] -> rw_cells rsegs m (e + 24) [CB 8 junk] ->
  0 <= p < 2 ^ 64 -> 0 <= pc < 2 ^ 64 ->
  evt rsegs (fun ms' => exists b1 b2 b3 b4 m',
       ms' = MS (mkR (Z_to_bv 64 0x15a54) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sa_sel pc 0x108b0)) b1 b2 b3 b4 a5 a6 a7
                     (Z_to_bv 64 e) (Z_to_bv 64 (sa_sel pc 0x108b0)) s4 (Z_to_bv 64 (e + 8))
                     s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 24, e + 32)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 3)]
       /\ rw_cells rsegs m' (e + 24) [C8 (Z_to_bv 64 p)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) (Z_to_bv 64 pc) s4
             (Z_to_bv 64 (e + 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a20) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e p pc junk EN EA Hp Hpc.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 24, e + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite rc_sx32_lit by lia.
  do 4 step. sa_lits.
  do 3 step. if_false.
  step.
  unfold sa_sel. destruct (Z.eqb_spec pc 0) as [E0|E0].
  - subst pc. if_false. do 4 step.
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - rewrite (sa_nz_true pc Hpc E0). cbv iota. do 2 step.
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma sa_seg_a3 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e p : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 3)] -> rw_cells rsegs m (e + 32) [CB 8 junk] ->
  0 <= p < 2 ^ 64 ->
  evt rsegs (fun ms' => exists b1 b2 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) b1 b2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 e) s3 s4 (Z_to_bv 64 (e + 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15a6c) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 32, e + 40)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 4)]
       /\ rw_cells rsegs m' (e + 32) [C8 (Z_to_bv 64 p)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) s3 s4
             (Z_to_bv 64 (e + 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a54) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e p junk EN EA Hp.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 32, e + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite rc_sx32_lit by lia.
  do 3 step. sa_lits.
  do 2 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma sa_srl : forall id, -2^31 <= id < 2^31 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 id))) 4) = (id mod 2^32) / 16.
Proof.
  intros id H. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). change (bv_modulus 64) with (2^64).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sa_seg_rng :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (id : Z),
  0 <= id < 10000 ->
  evt rsegs (fun ms' => exists b0 b1,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 id) s1 b0 b1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15a90) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 id) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m id HI.
  do 2 step.
  rewrite (sa_srl id) by lia.
  replace ((id mod 2^32) / 16) with (id / 16) by (rewrite Z.mod_small by lia; reflexivity).
  assert (Q : 0 <= id / 16 < 625) by (Z.div_mod_to_equations; lia).
  step.
  unfold bv_ltu. rewrite (unsigned_lit (id / 16)) by lia.
  if_true.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

Lemma sa_seg_oor :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (id : Z),
  -2^31 <= id < 2^31 -> ~ (0 <= id < 10000) ->
  evt rsegs (fun ms' =>
       ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 id) s1 (Z_to_bv 64 (bv_unsigned sp + 8)) (Z_to_bv 64 32)
                     (Z_to_bv 64 0x10982) (Z_to_bv 64 (-1)) a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15aec) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 id) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m id HB HI.
  do 2 step.
  rewrite (sa_srl id) by lia.
  assert (Q : 625 <= (id mod 2^32) / 16 < 2^28) by (Z.div_mod_to_equations; lia).
  step.
  unfold bv_ltu. rewrite (unsigned_lit ((id mod 2^32) / 16)) by lia.
  if_false.
  do 6 step.
  apply evt_done. reflexivity.
Qed.

Lemma sa_seg_epi :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 s05 : word),
  rw_cells rsegs m (bv_unsigned sp0 + -56) [C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  96 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                     s02 s03 s04 s05 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15af8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 s05 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 9 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -96 + 96)) with sp0
    by (replace (bv_unsigned sp0 + -96 + 96) with (bv_unsigned sp0) by ring; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma sa_seg_epiA :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 s05 : word),
  rw_cells rsegs m (bv_unsigned sp0 + -56) [C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  96 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                     s02 s03 s04 s05 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15bc8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15aa4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 s05 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 9 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -96 + 96)) with sp0
    by (replace (bv_unsigned sp0 + -96 + 96) with (bv_unsigned sp0) by ring; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma sa_rf_nz : forall rf, -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 -> bv_eqb (Z_to_bv 64 rf) (Z_to_bv 64 0) = false.
Proof.
  intros rf Hr N. unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616. rewrite Zmod_0_l. intros H.
  apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. lia.
Qed.

Lemma sa_seg_ref :
  forall ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 s05 s0 : word) (rf : Z),
  rw_cells rsegs m (bv_unsigned sp0 + -56) [C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  96 <= bv_unsigned sp0 ->
  rw_cells rsegs m 0x33d48 [C4 (Z_to_bv 64 rf)] -> -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 s2 (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                     s02 s03 s04 s05 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15bc8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x33d10) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a90) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 s05 s0 rf FR SPR RC Hrf Nrf.
  do 2 step. rewrite rc_sx32_lit by lia. rewrite (sa_rf_nz rf Hrf Nrf). cbv iota.
  do 3 step.
  eapply evt_cut; [eapply sa_seg_epiA; [exact FR | exact SPR] |].
  intros ms' ->. apply evt_done. reflexivity.
Qed.

Lemma sa_run_mix : mix_call_contract ->
  forall ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e h : Z) (args : list (word * list byte)) (sp1 : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 80 <= bv_unsigned sp1 -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d48 [C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m e (le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) ->
  0x33d10 <= e -> e + 56 <= 0x340f8 -> (length args <= 6)%nat ->
  (forall k p, nth_error args k = Some p -> mc_arg m (bv_unsigned sp1 - 80) (bv_unsigned sp1) e k p) ->
  rw_cells rsegs m 0x340f8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  evt rsegs (fun ms' => exists t0' t1' t2' b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR (Z_to_bv 64 0x15ad4) sp1 gp tp t0' t1' t2' s0 (Z_to_bv 64 0x33d10)
                     (Z_to_bv 64 (bv_unsigned sp1 + 8)) (Z_to_bv 64 32) (Z_to_bv 64 0x10982) s0 b4 b5 b6 b7
                     (Z_to_bv 64 e) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x15aec) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 80, bv_unsigned sp1); (0x340f8, 0x34100)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x340f8 [C8 (Z_to_bv 64 (mixcall h 0 (map snd args)))])
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 0x33d10) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 e) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a90) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e h args sp1 MI ST LO LO2 RC EF E0 E1 LA HARG ES Hh.
  assert (MIX' := MIX). unfold mix_call_contract, MIX_CALL_FRAME in MIX'.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp1 - 80, bv_unsigned sp1); (0x340f8, 0x34100)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step. try (rewrite rc_sx32_lit by lia). if_true.
  do 3 step.
  call (MIX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0 args).
  - exact MI.
  - exact ST.
  - lia.
  - lia.
  - exact LA.
  - rewrite unsigned_lit by lia. exact EF.
  - rewrite unsigned_lit by lia. lia.
  - intros k p Hk. rewrite unsigned_lit by lia. exact (HARG k p Hk).
  - eapply ro_bytes_at; [exact MI | unfold FNV_B0_ADDR; lia | rewrite length_le8; unfold FNV_B0_ADDR; lia |].
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  - unfold FNV_B0_ADDR. lia.
  - rewrite (unsigned_lit h) by lia.
    do 6 step.
    apply evt_done. do 12 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition sa_mid (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x15af8) sp gp tp t0 t1 t2 s0 s1
                  (Z_to_bv 64 (bv_unsigned sp + 8)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x15b80) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp + 40)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ length slack = (31 - length (resp v))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp + 8) (resp v ++ Z_to_bv 8 0 :: slack).

Lemma sa_run_snp : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v : Z) (canary : word),
  -2^31 <= v < 2^31 ->
  stk rsegs m lo (bv_unsigned sp + 40) -> lo + SNPRINTF_K <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bv_unsigned sp + 40 <= TASK_SIZE ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (sa_mid sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo v m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 8)) (Z_to_bv 64 32) (Z_to_bv 64 0x10982)
             (Z_to_bv 64 v) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15aec) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v canary HV ST LO IE HTS FRM MI TM GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, TASK_SIZE in *.
  pose proof (munch_refl [(lo, bv_unsigned sp + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  carve_frame 8%nat ST.
  clear FR0.
  rewrite Z.add_0_r in ST.
  pose proof (resp_len v HV) as RL.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp + 8) junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  assert (JL : length junk = 32%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  step.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary RESP_FMT RESP_PS
              [AInt v] (RESP_HEAD ++ pf_dec v) junk).
    - rewrite unsigned_lit by lia. apply resp_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, RESP_FMT. cbn [length]. lia.
    - exact resp_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply lit_mod32].
    - exact (resp_text v).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
    - exact ST.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - lia.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  change (Z.to_nat (32 - 1)) with 31%nat in BT, MU2.
  rewrite (firstn_all2 (n := 31%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 0x15af0)) with (Z_to_bv 64 0x15af0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (RESP_HEAD ++ pf_dec v))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + 8 + Z.of_nat (S (length (RESP_HEAD ++ pf_dec v))))
                   (skipn (S (length (RESP_HEAD ++ pf_dec v))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes ((RESP_HEAD ++ pf_dec v) ++ [0%Z]) = resp v ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (RESP_HEAD ++ pf_dec v)) with
      (pf_bytes (RESP_HEAD ++ pf_dec v)). rewrite pf_resp by exact HV. reflexivity. }
  assert (LR : length (resp v) = length (RESP_HEAD ++ pf_dec v)).
  { rewrite <- (pf_resp v HV). unfold pf_bytes. apply length_map. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp + 8)
                  (resp v ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec v))) junk)).
  { replace (resp v ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec v))) junk) with
      ((resp v ++ [Z_to_bv 8 0]) ++ skipn (S (length (RESP_HEAD ++ pf_dec v))) junk)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, LR. cbn [length].
    replace (Z.of_nat (length (RESP_HEAD ++ pf_dec v) + 1))
      with (Z.of_nat (S (length (RESP_HEAD ++ pf_dec v)))) by lia. exact BJT2. }
  clear BT BJT BJT2 BJ BJL FR.
  do 2 step.
  apply evt_done. unfold sa_mid.
  do 17 eexists. exists (skipn (S (length (RESP_HEAD ++ pf_dec v))) junk). split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx |- *. lia. }
  split; [exact WM2|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, LR; lia|]. exact BUF.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecTail RecStub.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import xstrdup_c arg_i_c hand_back_c answer_c
rec_calls_free_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require hand_back RecAnsB.
Local Open Scope Z_scope.

Lemma sa_bytes_some : forall segs m a bs (i : nat), bytes_at segs m a bs -> (i < length bs)%nat ->
  mbyte segs m (a + Z.of_nat i) <> None.
Proof.
  intros segs m a bs i (_ & _ & H) Hi. specialize (H i Hi).
  change (mrd segs m (wa (a + Z.of_nat i))) with (mbyte segs m (a + Z.of_nat i)) in H.
  rewrite H. apply nth_error_Some. exact Hi.
Qed.

Lemma sa_bytes_someZ : forall segs m a bs x, bytes_at segs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  mbyte segs m x <> None.
Proof.
  intros segs m a bs x H Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
  apply (sa_bytes_some segs m a bs); [exact H | lia].
Qed.

Lemma sa_pad_le : forall e c a, e <= c -> a < e + (- e) mod 8 -> a < 8 * ((c + 7) / 8).
Proof.
  intros e c a H1 H2.
  pose proof (Z.div_mod (- e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (- e) 8 ltac:(lia)).
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)).
  lia.
Qed.

Lemma sa_present : forall segs m a, present m a -> mbyte segs m a <> None.
Proof. intros segs m a [b E]. unfold mbyte. rewrite E. discriminate. Qed.

Lemma sa_combine_snd : forall (X Y : Type) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H |- *;
    [reflexivity | discriminate | discriminate | rewrite (IH l2 ltac:(lia)); reflexivity].
Qed.

Lemma sa_nth_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y) k a b,
  nth_error (combine l1 l2) k = Some (a, b) -> nth_error l1 k = Some a /\ nth_error l2 k = Some b.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] [|k] a b H; cbn in H |- *; try discriminate.
  - injection H as -> ->. split; reflexivity.
  - exact (IH l2 k a b H).
Qed.

Lemma sa_glob : forall a, 0x33d10 <= a < 0x34108 -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N.
Proof. intros a H. unfold GLOB_LO. change (Z.of_nat GLOB_N) with 1020. lia. Qed.

Lemma sa_entry_bounds : forall R, 0x33d10 <= rec_entry G_REC REC_SC R /\ rec_entry G_REC REC_SC R + 56 <= 0x340f8.
Proof.
  intros R. unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
  - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE. lia.
  - unfold REC_SC. lia.
Qed.

Lemma sa_cells_n : forall mk m2 e k off, 0x33d10 <= e -> e + 56 <= 0x340f8 -> 8 <= off <= 40 ->
  ro_agree rsegs m2 -> (forall a, 0x33d10 <= a < 0x34108 -> mbyte rsegs m2 a = mbyte rsegs mk a) ->
  bytes_at rsegs mk (e + 4) (le4 k) ->
  rw_cells rsegs (normalize rsegs m2) (e + 4) [C4 k] /\
  exists junk, rw_cells rsegs (normalize rsegs m2) (e + off) [CB 8 junk].
Proof.
  intros mk m2 e k off E1 E2 HO RA2 KG NA.
  assert (NA2 : rw_cells rsegs m2 (e + 4) [C4 k]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|].
    apply (bytes_at_transfer rsegs mk); [exact NA|]. intros i Hi. rewrite length_le4 in Hi. apply KG. lia. }
  destruct (glob_rw_cells m2 (e + off) 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW2].
  split.
  - apply rw_cells_normalize; [exact RA2 | exact NA2 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia.
  - exists junk. apply rw_cells_normalize; [exact RA2 | exact EW2 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia.
Qed.

Definition sa_m (R : rstate) (As : list (list byte)) (id : Z) : rstate * list byte :=
  let R1 := rec_record R REC_ADD As in
  if (id <? 0) || (10000 <=? id) then hand_back R1 (resp (-1))
  else if negb (r_refuse R1 =? 0) then hand_back R1 (resp (r_code R1))
  else hand_back (rec_mix R1 (REC_ADD, As)) (resp id).

Lemma sa_m_eq : forall R uri id pl cl,
  sup_add_m R uri id pl cl = sa_m R [sarg uri; dec id; darg pl (bstr "-"%string); darg cl (bstr "-"%string)] id.
Proof. reflexivity. Qed.

Lemma sa_m_len : forall R As id, -2^31 <= id < 2^31 -> -2^31 <= r_code R < 2^31 ->
  (6 <= length (snd (sa_m R As id)) <= 16)%nat.
Proof.
  intros R As id H HC. unfold sa_m. cbv zeta.
  assert (HC1 : -2^31 <= r_code (rec_record R REC_ADD As) < 2^31) by (rewrite rec_code_record; exact HC).
  destruct ((id <? 0) || (10000 <=? id)); [exact (resp_length (-1) ltac:(lia))|].
  destruct (negb (r_refuse (rec_record R REC_ADD As) =? 0));
    [exact (resp_length _ HC1) | exact (resp_length id H)].
Qed.

Ltac sa_reg X :=
  match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end; simp_regs.

Ltac sa_back m2 RA2 can REL RO EQ MUn WMn NAn EAn m MU WM NA EA Rn X :=
  let EC := fresh "EC" in let MR := fresh "MR" in
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR];
  revert EC MR RO EQ; generalize (ms_mem can) as m; intros m EC MR RO EQ; subst can;
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR RO MUn) as MU;
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR RO WMn) as WM;
  pose proof (rw_cells_rel rsegs _ _ _ _ MR NAn) as NA;
  pose proof (rw_cells_rel rsegs _ _ _ _ MR EAn) as EA;
  clear MUn WMn NAn EAn MR;
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (Rn & -> & X).

Ltac sa_hw EE :=
  let a := fresh "a" in let Ra := fresh "Ra" in let Hm := fresh "Hm" in
  intros a Ra Hm; cbn [outside] in Hm; try rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS;
  cbn [length]; lia.

Ltac sa_na NA :=
  apply cells_bytes_at in NA; cbn [cells_bytes cbytes] in NA; rewrite app_nil_r in NA; exact NA.

Ltac sa_ar EE EA e k :=
  apply cells_bytes_at in EA; cbn [cells_bytes cbytes] in EA; rewrite app_nil_r in EA;
  match goal with |- bytes_at _ _ ?ad _ => replace ad with (e + k)
    by (try rewrite <- EE; unfold CALL_OFF_ARGS; cbn [length]; lia) end;
  exact EA.

Section H.
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
Hypothesis XSD : forall fx0 : YK11.FPState, @xstrdup_contract fx0 rc B API.
Hypothesis SNP : snprintf_contract.
Hypothesis HB : forall fx0 : YK11.FPState, @hand_back_contract fx0 rc B API.
Hypothesis MIX : mix_call_contract.
Hypothesis ANSF : forall fx0 : YK11.FPState, @answer_contract fx0 rc B API.

Definition xsrc (L : layout) (A : astate) (m : word -> option byte) (sp s : Z) (y : list byte) : Prop :=
  no0 y /\ Z.of_nat (length y) <= LMAX /\
  exists slack, bytes_at rsegs m s (y ++ Z_to_bv 8 0 :: slack) /\
    (- (s + Z.of_nat (length y) + 1)) mod 8 <= Z.of_nat (length slack) /\
    (s + Z.of_nat (length (y ++ Z_to_bv 8 0 :: slack)) <= sp - XSTRDUP_K \/ sp <= s) /\
    str_home B L A sp s (Z.of_nat (length y) + 1).

Lemma xsrc_build : forall L A m sp s y,
  no0 y -> Z.of_nat (length y) <= LMAX ->
  bytes_at rsegs m s (y ++ [Z_to_bv 8 0]) ->
  (forall a, s + Z.of_nat (length y) + 1 <= a < s + Z.of_nat (length y) + 1 + (- (s + Z.of_nat (length y) + 1)) mod 8 ->
     mbyte rsegs m a <> None) ->
  s + Z.of_nat (length y) + 1 + (- (s + Z.of_nat (length y) + 1)) mod 8 <= 2 ^ 64 ->
  (s + Z.of_nat (length y) + 1 + (- (s + Z.of_nat (length y) + 1)) mod 8 <= sp - XSTRDUP_K \/ sp <= s) ->
  str_home B L A sp s (Z.of_nat (length y) + 1) ->
  xsrc L A m sp s y.
Proof.
  intros L A m sp s y N0 LX BS PR HB0 DJ HOME. unfold xsrc.
  pose proof (Z.mod_pos_bound (- (s + Z.of_nat (length y) + 1)) 8 ltac:(lia)) as Hpad.
  destruct (hand_back.hb_bytes_pad rsegs m s (y ++ [Z_to_bv 8 0])
              (Z.to_nat ((- (s + Z.of_nat (length y) + 1)) mod 8)) BS) as (sl & LS & BS2).
  - rewrite length_app. cbn [length]. lia.
  - intros j Hj. apply PR. rewrite length_app. cbn [length]. lia.
  - split; [exact N0|]. split; [exact LX|]. exists sl.
    rewrite <- app_assoc in BS2. cbn [app] in BS2.
    split; [exact BS2|]. rewrite LS, Z2Nat.id by lia.
    split; [lia|]. split; [|exact HOME].
    rewrite length_app. cbn [length]. rewrite LS. lia.
Qed.

Lemma xsrc_null : forall L A m sp, ro_agree rsegs m -> 0x10a20 <= sp - XSTRDUP_K ->
  xsrc L A m sp 0x10a19 (bstr "(null)"%string).
Proof using SEGS.
  intros L A m sp RA HS.
  assert (C : rom_chk 0x10a19 (bstr "(null)"%string ++ [Z_to_bv 8 0]) = true) by (vm_compute; reflexivity).
  assert (LN : Z.of_nat (length (bstr "(null)"%string)) = 6) by reflexivity.
  assert (PD : (- (0x10a19 + 6 + 1)) mod 8 = 0) by reflexivity.
  apply xsrc_build.
  - apply no0_nz. vm_compute. reflexivity.
  - rewrite LN. unfold LMAX. lia.
  - apply rom_chk_bytes; [exact RA | lia | rewrite length_app, Nat2Z.inj_add, LN; cbn; lia | exact C].
  - rewrite LN, PD. intros a Ha. lia.
  - rewrite LN, PD. lia.
  - rewrite LN, PD. left. lia.
  - right. right. rewrite LN. split; [lia|]. split; [lia|]. intros i Hi. rewrite SEGS.
    destruct (rom_chk_at 0x10a19 _ (Z.to_nat i) C) as [H _].
    + rewrite length_app. change (length [Z_to_bv 8 0]) with 1%nat. lia.
    + rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma xsrc_dash : forall L A m sp, ro_agree rsegs m -> 0x108b8 <= sp - XSTRDUP_K ->
  xsrc L A m sp 0x108b0 (bstr "-"%string).
Proof using SEGS.
  intros L A m sp RA HS.
  assert (C : rom_chk 0x108b0 (bstr "-"%string ++ [Z_to_bv 8 0]) = true) by (vm_compute; reflexivity).
  assert (LN : Z.of_nat (length (bstr "-"%string)) = 1) by reflexivity.
  assert (PD : (- (0x108b0 + 1 + 1)) mod 8 = 6) by reflexivity.
  apply xsrc_build.
  - apply no0_nz. vm_compute. reflexivity.
  - rewrite LN. unfold LMAX. lia.
  - apply rom_chk_bytes; [exact RA | lia | rewrite length_app, Nat2Z.inj_add, LN; cbn; lia | exact C].
  - rewrite LN, PD. intros a Ha.
    assert (CA : a = 0x108b2 \/ a = 0x108b3 \/ a = 0x108b4 \/ a = 0x108b5 \/ a = 0x108b6 \/ a = 0x108b7) by lia.
    repeat (destruct CA as [CA|CA]; [subst a; rewrite (mbyte_ro_agree _ _ _ RA) by (vm_compute; reflexivity);
      let H := fresh in intro H; vm_compute in H; discriminate H|]).
    subst a. rewrite (mbyte_ro_agree _ _ _ RA) by (vm_compute; reflexivity).
    let H := fresh in intro H; vm_compute in H; discriminate H.
  - rewrite LN, PD. lia.
  - rewrite LN, PD. left. lia.
  - right. right. rewrite LN. split; [lia|]. split; [lia|]. intros i Hi. rewrite SEGS.
    destruct (rom_chk_at 0x108b0 _ (Z.to_nat i) C) as [H _].
    + rewrite length_app. change (length [Z_to_bv 8 0]) with 1%nat. lia.
    + rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma xsrc_of : forall K S L A mem md O Lc Ac mc mdc p v lit d,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  ro_agree rsegs mem -> ro_agree rsegs mc -> 96 + XSTRDUP_K <= K ->
  str_arg B L A O S K mem p v ->
  xsrc Lc Ac mc (S - 96) lit d ->
  0 <= p < 2 ^ 64 /\ xsrc Lc Ac mc (S - 96) (sa_sel p lit) (match v with Some x => x | None => d end).
Proof using SEGS ERRNO_LOW SLACK.
  intros K S L A mem md O Lc Ac mc mdc p v lit d R RA RAc HK SA XL.
  destruct v as [x|].
  2: { cbn in SA. subst p. split; [lia|]. replace (sa_sel 0 lit) with lit by reflexivity. exact XL. }
  destruct SA as (NZ & N0 & LX & slack & BS & PAD & DJ & HOME & NRA).
  rewrite SEGS in BS.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  split; [lia|].
  unfold sa_sel. rewrite (proj2 (Z.eqb_neq p 0) NZ).
  pose proof R as (HM1 & HWA & HW1 & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  rewrite SEGS in HF, HKP.
  pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length x) + 1)) 8 ltac:(lia)) as Hpad.
  assert (BS0 : bytes_at rsegs mem p (x ++ [Z_to_bv 8 0])).
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) in BS by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  assert (MSOME : forall a, p <= a < p + Z.of_nat (length x) + 1 + (- (p + Z.of_nat (length x) + 1)) mod 8 ->
            mbyte rsegs mem a <> None).
  { intros a Ha. apply (sa_bytes_someZ rsegs mem p (x ++ Z_to_bv 8 0 :: slack)); [exact BS|].
    rewrite length_app. cbn [length]. lia. }
  assert (FREE : forall a, S <= a ->
            p <= a < p + Z.of_nat (length x) + 1 + (- (p + Z.of_nat (length x) + 1)) mod 8 ->
            mbyte rsegs mc a = mbyte rsegs mem a).
  { intros a H1 H2. refine (proj1 (HF a _ _ _ _)).
    - left. lia.
    - lia.
    - lia.
    - apply NRA. rewrite length_app. cbn [length]. lia. }
  assert (KS : (forall a, p <= a < p + Z.of_nat (length x) + 1 -> mbyte rsegs mc a = mbyte rsegs mem a) /\
               (forall a, p + Z.of_nat (length x) + 1 <= a <
                          p + Z.of_nat (length x) + 1 + (- (p + Z.of_nat (length x) + 1)) mod 8 ->
                  mbyte rsegs mc a <> None) /\
               str_home B Lc Ac (S - 96) p (Z.of_nat (length x) + 1)).
  { destruct HOME as [(HS & _) | [(q & k & Hqk & Nq & Hq1 & Hq2) | (H0 & H1 & HRO)]].
    - split; [intros a Ha; apply FREE; lia|].
      split; [intros a Ha; rewrite FREE by lia; apply MSOME; lia|].
      left. split; lia.
    - unfold blocks in Hqk. apply in_map_iff in Hqk as ([u k'] & Eu & Hu). cbn in Eu. injection Eu as E0 E2. subst k'.
      assert (E1 : ptr_addr L u = q) by (rewrite <- E0; reflexivity). clear E0.
      assert (Ng : ~ In (ptr_addr L u, k) O) by (rewrite E1; intros Hin; apply Nq; exact (in_map fst O (q, k) Hin)).
      pose proof (rjr_in_cur B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc u k R Hu Ng) as Hu1.
      pose proof (ptr_addr_stable A L Lc u k HWA Hu HL) as Ep.
      assert (Hb1 : In (q, k) (blocks Lc Ac)) by (rewrite <- E1, <- Ep; exact (user_in_blocks Lc Ac u k Hu1)).
      assert (KB : forall a, q <= a < q + k -> mbyte rsegs mc a = mbyte rsegs mem a).
      { intros a Ha. replace a with (ptr_addr L u + (a - q)) by lia. apply (HKP u k (a - q) Hu Ng). lia. }
      split; [intros a Ha; apply KB; lia|].
      split.
      + intros a Ha. destruct (Z_lt_le_dec a (q + k)) as [Hl|Hl].
        * rewrite KB by lia. apply MSOME. lia.
        * apply sa_present. apply (SLACK Lc Ac mc mdc q k a HM1 Hb1). split; [exact Hl|].
          apply (sa_pad_le (p + Z.of_nat (length x) + 1) (q + k) a); lia.
      + right. left. exists q, k. split; [exact Hb1|]. split; lia.
    - rewrite SEGS in HRO.
      assert (RO0 : 65536 <= p < 139264).
      { apply (hand_back.hb_ro_rsegs p); [lia|]. replace p with (p + 0) by lia. apply HRO. lia. }
      assert (RO1 : 65536 <= p + Z.of_nat (length x) < 139264).
      { apply (hand_back.hb_ro_rsegs (p + Z.of_nat (length x))); [lia|]. apply HRO. lia. }
      assert (ROa : forall a, p <= a < p + Z.of_nat (length x) + 1 + (- (p + Z.of_nat (length x) + 1)) mod 8 ->
                mbyte rsegs mc a = mbyte rsegs mem a).
      { intros a Ha. assert (Hro : ro_addr rsegs (Z_to_bv 64 a) = true).
        { apply hand_back.hb_ro_rsegs; [lia|]. split; [lia|].
          pose proof (sa_pad_le (p + Z.of_nat (length x) + 1) 139264 a ltac:(lia) ltac:(lia)) as X.
          change (8 * ((139264 + 7) / 8)) with 139264 in X. lia. }
        rewrite (mbyte_ro_agree _ _ _ RAc Hro), (mbyte_ro_agree _ _ _ RA Hro). reflexivity. }
      split; [intros a Ha; apply ROa; lia|].
      split; [intros a Ha; rewrite ROa by lia; apply MSOME; lia|].
      right. right. split; [lia|]. split; [lia|]. rewrite SEGS. exact HRO. }
  destruct KS as (KS1 & KS2 & HOME').
  apply xsrc_build; [exact N0 | exact LX | | exact KS2 | lia | | exact HOME'].
  - apply (bytes_at_keep_in rsegs mem mc p (p + Z.of_nat (length x) + 1));
      [exact BS0 | lia | rewrite length_app; cbn [length]; lia |].
    intros a Ha. apply KS1. exact Ha.
  - destruct DJ as [D|D]; [left | right]; rewrite ?length_app in D; cbn [length] in D; lia.
Qed.

Lemma sa_mc_arg : forall Lc Ac mc mdc e k pn s lo hi,
  aa_MR API Lc Ac mc mdc -> ro_agree rsegs mc ->
  bytes_at rsegs mc (e + CALL_OFF_ARGS + 8 * Z.of_nat k) (le8 (Z_to_bv 64 (fst pn))) ->
  In pn (blocks Lc Ac) -> Z.of_nat (length s) + 1 <= snd pn ->
  bytes_at rsegs mc (fst pn) (s ++ [Z_to_bv 8 0]) -> no0 s -> Z.of_nat (length s) <= LMAX ->
  alloc_ceiling <= lo ->
  mc_arg (normalize rsegs mc) lo hi e k (Z_to_bv 64 (fst pn), s).
Proof using SEGS SLACK.
  intros Lc Ac mc mdc e k [q n] s lo hi HM RA BP Hb Hn BS N0 LX HLO. cbn [fst snd] in *.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_value as ACV.
  pose proof Hb as Hb0.
  unfold blocks in Hb. apply in_map_iff in Hb as ([u n'] & Eu & Hu). cbn in Eu. injection Eu as E0 E2. subst n'.
  assert (E1 : ptr_addr Lc u = q) by (rewrite <- E0; reflexivity). clear E0.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  destruct (mr_blocks B _ LAWS Lc Ac mc mdc u n 0 HM Hu ltac:(lia)) as (_ & HQ1 & HQ2 & _). rewrite E1 in HQ1, HQ2.
  pose proof (Z.mod_pos_bound (- (q + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hpad.
  assert (CE : forall a, a < q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 ->
            a < alloc_ceiling).
  { intros a Ha. pose proof (sa_pad_le (q + Z.of_nat (length s) + 1) (q + n) a ltac:(lia) Ha) as X.
    pose proof (Z.div_mod (q + n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)). destruct ACV as (_ & ACM). lia. }
  destruct (hand_back.hb_bytes_pad rsegs mc q (s ++ [Z_to_bv 8 0])
              (Z.to_nat ((- (q + Z.of_nat (length s) + 1)) mod 8)) BS) as (sl & LS & BS2).
  - rewrite length_app. cbn [length].
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
  - intros j Hj. rewrite length_app. cbn [length].
    destruct (Z_lt_le_dec (q + Z.of_nat (length s + 1) + Z.of_nat j) (q + n)) as [Hl|Hl].
    + destruct (mr_blocks B _ LAWS Lc Ac mc mdc u n (Z.of_nat (length s + 1) + Z.of_nat j) HM Hu ltac:(lia))
        as (Hp & _).
      rewrite E1 in Hp. apply sa_present. replace (q + Z.of_nat (length s + 1) + Z.of_nat j)
        with (q + (Z.of_nat (length s + 1) + Z.of_nat j)) by ring. exact Hp.
    + apply sa_present. apply (SLACK Lc Ac mc mdc q n _ HM Hb0). split; [exact Hl|].
      apply (sa_pad_le (q + Z.of_nat (length s) + 1) (q + n)); lia.
  - unfold mc_arg. cbn [fst snd]. rewrite unsigned_lit by lia.
    split; [apply bytes_at_normalize; [exact RA | unfold CALL_OFF_ARGS in BP; exact BP]|].
    split; [exact N0|]. split; [exact LX|].
    exists sl. rewrite <- app_assoc in BS2. cbn [app] in BS2.
    split; [apply bytes_at_normalize; [exact RA | exact BS2]|].
    rewrite LS, Z2Nat.id by lia. split; [lia|]. left.
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
Qed.

Lemma sa_arg : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre R1 s y (Q : config -> Prop),
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  (length As < 6)%nat -> sb_le (sb_shift b A Ac) bpre ->
  room_slots (sb_malloc bpre (Z.of_nat (length y) + 1)) (LMAX + 1) ->
  YK0s.ret_ok (getr R1 1) -> getr R1 2 = Z_to_bv 64 (spZ regs - 96) -> getr R1 4 = getr regs 4 ->
  getr R1 10 = Z_to_bv 64 s -> xsrc Lc Ac mc (spZ regs - 96) s y ->
  rw_cells rsegs mc (spZ regs - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)] ->
  (forall L2 A2 R2 m2 md2 p,
     regs_preserved R1 R2 -> getr R2 10 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
     aa_MR API L2 A2 m2 md2 -> ro_agree rsegs m2 ->
     rw_cells rsegs m2 (spZ regs - 56)
       [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
        C8 (getr regs 1)] ->
     (forall a, 0x33d10 <= a < 0x34108 -> mbyte rsegs m2 a = mbyte rsegs mc a) ->
     sb_le (sb_shift b A A2) (sb_malloc bpre (Z.of_nat (length y) + 1)) ->
     (forall m3 W, munch W m2 m3 -> wmono rsegs m2 m3 ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
           (rec_entry G_REC REC_SC R + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC R + CALL_OFF_NARGS + 4) \/
           (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
            rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8)) ->
        bytes_at rsegs m3 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
        bytes_at rsegs m3 (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
        sinv B API SUP_ADD_K (spZ regs) L A mem md O L2 A2 m3 md2 (rec_record R REC_ADD (As ++ [y]))
          (Oc ++ [(p, Z.of_nat (length y) + 1)]) b) ->
     SR rsegs (mkCfg (mkst R2 (getr R1 1) m2 (seg_rom rsegs)) md2) Q) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15780) mc (seg_rom rsegs)) mdc) Q.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX XSD.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre R1 s y Q PRE SI H6 BLE ROOM RET E2 E4 E10 XS FR K.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SP1 : spZ R1 = bv_unsigned sp - 96) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  destruct XS as (N0 & LX & slack & BS & PAD & DJ & HOME).
  pose proof (XSD fx) as XC. unfold xstrdup_contract in XC. rewrite SEGS in XC.
  eapply SR_bind.
  { apply (XC Lc Ac R1 mc mdc s y slack (sb_shift b A Ac)).
    - apply (call_pre_k_of_rjr B _ SUP_ADD_K (bv_unsigned sp) rec_area _ L A mem md Lc Ac mc mdc XSTRDUP_K R1 RJ).
      + exact RET.
      + rewrite SP1. replace (bv_unsigned sp - 96) with (bv_unsigned sp + (-6) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP1. unfold SUP_ADD_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP1. lia.
      + rewrite E4. exact HTP.
    - exact E10.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact PAD.
    - rewrite SP1. exact DJ.
    - rewrite SP1. exact HOME.
    - exact RS.
    - eapply room_slots_mono; [| | exact ROOM].
      + apply sb_malloc_mono. exact BLE.
      + lia.
    - exact RA. }
  intros c2 RET2.
  destruct RET2 as (L2 & A2 & R2 & m2 & md2 & p & -> & POST2 & A0' & NZ & AL16 & FB2 & BLK2 & BK2 & UB2 & BYT2 & SRC2
    & RA2 & GK2 & INI2 & RGN2 & RS2).
  rewrite SEGS in RA2, BYT2 |- *.
  pose proof POST2 as (PM2 & _ & _ & _ & _ & RP2 & _ & PF2 & _).
  pose proof FB2 as (FBa & FBb & FBc).
  assert (POST2' : call_post_k B (aa_MR API) XSTRDUP_K Lc Ac R1 mc mdc
                     (fun a => p <= a < p + (Z.of_nat (length y) + 1)) L2 A2 R2 m2 md2).
  { pose proof POST2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
    intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; lia]. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs mc); [exact FR|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K Lc Ac R1 mc mdc _ L2 A2 R2 m2 md2 (bv_unsigned sp - 56 + i)
                HM POST2 ltac:(lia) ltac:(rewrite SP1; unfold XSTRDUP_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (KG : forall a, 0x33d10 <= a < 0x34108 -> mbyte rsegs m2 a = mbyte rsegs mc a).
  { intros a Ha. assert (GA : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N) by (apply sa_glob; exact Ha).
    destruct (GFACT a (glob_in a GA)) as (Gi & _ & _ & Ge).
    rewrite SEGS in PF2. apply PF2.
    - right. exact Gi.
    - exact (GOWN _ _ _ _ a HM (glob_in a GA)).
    - exact (GOWN _ _ _ _ a PM2 (glob_in a GA)).
    - unfold scratch_k. rewrite SP1. unfold XSTRDUP_K, ALLOC_STACK. intros [Hs|He]; [lia | exact (Ge He)].
    - intros Hp. cbv beta in Hp. apply (FBc (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
  assert (F182 : f18_words rsegs m2).
  { destruct (ax_statics AX L2 A2 m2 md2 PM2) as (_ & (g & Hg & HWg) & _).
    rewrite GRD, SEGS in HWg.
    apply (RecAnsB.f18_words_after mc m2 g F18); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK2 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  apply (K L2 A2 R2 m2 md2 p RP2 A0' ltac:(lia) PM2 RA2 FR2 KG).
  - pose proof BLK2 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A Ac A2).
    rewrite <- (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2 bl1 bl2 p _ EB1 EB2).
    apply sb_malloc_mono. exact BLE.
  - intros m3 W MU WM HW NA AR.
    exact (sinv_sarg B API SEGS ERRNO_LOW GFACT GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc R
             REC_ADD As Oc b XSTRDUP_K R1 L2 A2 R2 m2 md2 m3 W y p (Z.of_nat (length y) + 1)
             SI H6 ltac:(rewrite SP1; unfold SUP_ADD_K, XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SP1; lia)
             POST2' MU WM HW NZ FB2 BLK2 UB2 BK2 RGN2 NA AR BYT2 N0 LX ltac:(unfold LMAX in *; lia) INI2 RS2 RA2 F182).
Qed.

Definition sa_tret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (O : list (Z * Z)) (R' : rstate) (t : list byte) (b bpre : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' O' q,
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    fp_kept fx fx' /\
    call_post_rec B (aa_MR API) SUP_ADD_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep (ms_segs B) L' A' mem' R' O' /\ owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
    In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
    ~ In q (map fst O') /\
    Mem.bytes_at (ms_segs B) mem' q (t ++ [Z_to_bv 8 0]) /\
    others_kept (ms_segs B) L A mem L' A' mem' O /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
    ro_agree (ms_segs B) mem' /\ f18_words (ms_segs B) mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_malloc (sb_malloc bpre (Z.of_nat (length t) + 1)) (Z.of_nat (length t) + 1)) /\
    res_ok_slots A' (sb_shift b A A').

Ltac sa_pres X5 PR2 X1 KT R1 :=
  match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X5 eq_refl); simp_regs;
    first [ reflexivity
          | transitivity (getr R1 (Z_to_bv 5 k)); [exact (PR2 k ltac:(unfold callee_saved; lia))|];
            rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X1 eq_refl); simp_regs;
            exact (KT k ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)) ]
  end.

Lemma sa_resp : forall L A regs mem md O Lc Ac mc mdc Rc Oc bc bpre regs1 v,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc Rc Oc bc ->
  getr regs1 2 = Z_to_bv 64 (spZ regs - 96) -> getr regs1 10 = Z_to_bv 64 (spZ regs - 88) ->
  getr regs1 11 = Z_to_bv 64 32 -> getr regs1 12 = Z_to_bv 64 0x10982 -> getr regs1 13 = Z_to_bv 64 v ->
  -2^31 <= v < 2^31 ->
  kept_ex [2; 8; 9; 18; 19; 20; 21] regs regs1 ->
  rw_cells rsegs mc (spZ regs - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)] ->
  frm_zero fp_csr -> sb_le (sb_shift bc A Ac) bpre ->
  room_slots (sb_malloc (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (resp v)) + 1))
                (Z.of_nat (length (resp v)) + 1)) (Z.of_nat (length (resp v)) + 1) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 0x15aec) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (hand_back Rc (resp v))) (resp v) bc bpre).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN AX CTX SNP HB.
  intros L A regs mem md O Lc Ac mc mdc Rc Oc bc bpre regs1 v PRE SI E2 E10 E11 E12 E13 HV KT FR FRM BLE ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & HTS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS. unfold TASK_SIZE in HTS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (resp_length v HV) as RL.
  pose proof F18 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs mc snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs mc snprintf_c.GUARD (le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (ST0 : stk rsegs (normalize_cj rsegs mc) (bv_unsigned sp - 12384)
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 96)) + 40)).
  { rewrite unsigned_lit by lia. apply stk_normalize_cj; [lia | unfold TASK_SIZE; lia |].
    intros a Ha. rewrite <- SEGS. apply HSC. left. unfold SUP_ADD_K. lia. }
  pose proof (bytes_at_normalize_cj_low rsegs mc snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) RA
    ltac:(rewrite length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs mc snprintf_c.GUARD (le8 canary) RA
    ltac:(rewrite length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  assert (Q2 : reg_get regs1 2 = Z_to_bv 64 (bv_unsigned sp - 96)) by exact E2.
  assert (Q10 : reg_get regs1 10 = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 96)) + 8)).
  { rewrite unsigned_lit by lia. replace (bv_unsigned sp - 96 + 8) with (bv_unsigned sp - 88) by ring. exact E10. }
  assert (Q11 : reg_get regs1 11 = Z_to_bv 64 32) by exact E11.
  assert (Q12 : reg_get regs1 12 = Z_to_bv 64 0x10982) by exact E12.
  assert (Q13 : reg_get regs1 13 = Z_to_bv 64 v) by exact E13.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2, Q10, Q11, Q12, Q13.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    eapply (sa_run_snp SNP) with (lo := bv_unsigned sp - 12384) (canary := canary);
      [exact HV | exact ST0 | rewrite unsigned_lit by lia; unfold SNPRINTF_K; lia | lia
      | rewrite unsigned_lit by lia; unfold TASK_SIZE; lia | exact FRM
      | exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mc))
      | exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mc)) | exact GGn | exact GWn]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m1n
    & slack & -> & MU1n & WM1n & MI1n & FRM1 & FK1 & SL & BUF1n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs mc RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs mc RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same_cj rsegs _ _ RA RO1) as RA1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r BUF1n) as BUF1.
  destruct (RecAnsB.eqv_mkst_fx _ _ _ _ _ _ _ EQ1) as (R1 & -> & X1).
  clear MU1n WM1n MI1n BUF1n EQ1 MR1r.
  rewrite (unsigned_lit (bv_unsigned sp - 96)) in MU1, BUF1 by lia.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x15af8) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 96))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X1 eq_refl). simp_regs. exact (KT 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)). }
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (bv_unsigned sp - 88)).
  { rewrite (getr_of_eqv _ _ 10 X1 eq_refl). simp_regs. rewrite unsigned_lit by lia. f_equal. lia. }
  assert (SP1 : spZ R1 = bv_unsigned sp - 96) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (HWm : forall a, 0 <= a < 2 ^ 64 -> ~ outside [(bv_unsigned sp - 12384, bv_unsigned sp - 96 + 40)] a ->
                bv_unsigned sp - SUP_ADD_K <= a < bv_unsigned sp).
  { intros a Ra Hm. cbn [outside] in Hm. unfold SUP_ADD_K. lia. }
  pose proof (sinv_stack B API SEGS GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc Rc Oc bc m1 _
                SI MU1 WM1 HWm) as SI1.
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ mc m1 _ _ FR MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof SI1 as (RJ1 & GR1 & _ & _ & _ & _ & F181 & RS1).
  pose proof RJ1 as RJ1x.
  destruct RJ1x as (HM1 & HWA & HW1 & HBd & HL & HLen & HV1 & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC1 & HAX).
  assert (BRNG : forall q k, In (q, k) (blocks Lc Ac) -> 4096 <= q /\ q + k <= alloc_ceiling).
  { intros q k Hq. unfold blocks in Hq. apply in_map_iff in Hq as ([p k'] & E & Hp). cbn in E. injection E as <- <-.
    exact (mr_blocks_range B _ LAWS Lc Ac m1 mdc p k' HM1 Hp). }
  rewrite <- SEGS.
  eapply SR_bind.
  { eapply (HB (mkFP F1 fc1) Lc Ac R1 m1 mdc (bv_unsigned sp - 88) (resp v) slack Rc Oc (sb_shift bc A Ac)).
    - apply (call_pre_k_of_rjr B _ SUP_ADD_K (bv_unsigned sp) rec_area _ L A mem md Lc Ac m1 mdc HAND_BACK_K R1 RJ1).
      + rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP1. replace (bv_unsigned sp - 96) with (bv_unsigned sp + (-6) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold HAND_BACK_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP1. unfold SUP_ADD_K, HAND_BACK_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP1. lia.
      + rewrite E1_4. exact HTP.
    - exact E1_10.
    - rewrite SEGS. replace (bv_unsigned sp - 88) with (bv_unsigned sp - 96 + 8) by ring. exact BUF1.
    - exact (resp_no0 v).
    - unfold LMAX. lia.
    - rewrite SL. pose proof (Z.mod_pos_bound (- (bv_unsigned sp - 88 + Z.of_nat (length (resp v)) + 1)) 8
        ltac:(lia)). lia.
    - right. rewrite SP1. lia.
    - left. rewrite SP1. lia.
    - rewrite SEGS. exact GR1.
    - intros [q k] Hin. pose proof (BRNG q k (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR1 Hin)).
      unfold iv_apart. cbn [fst snd]. rewrite length_app. cbn [length]. lia.
    - exact RS1.
    - exact ROOM.
    - rewrite SEGS. exact RA1. }
  intros cf2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p1 & p2 & old & O2 & -> & OLDB & POST2 & A0' & P12 & AL1 & AL2 & FR1h
    & FR2h & (c1 & c2 & HBk & HIFF & NI1 & NI2) & BK & UBK & GREP' & HO' & HO2 & HBC & BY1 & BY2 & BYS & RA2 & GK2
    & INIT2 & REG2 & GR2 & RES2).
  pose proof POST2 as (PM2 & PW2 & PB2 & PL2 & PA2 & PR2 & PV2 & PF2 & PK2 & PS2).
  destruct (mr_model B _ LAWS L2 A2 m2 md2 PM2) as (Hh2 & Hl2 & _).
  set (n := Z.of_nat (length (resp v)) + 1) in *.
  assert (HF12 : forall a, alloc_ceiling <= a < 2 ^ 64 ->
     ~ (bv_unsigned sp - 96 - HAND_BACK_K <= a < bv_unsigned sp - 96) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs. apply PF2.
    - left. exact Ha.
    - intro Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HM1 Ho). lia.
    - intro Ho. destruct (owned_low B _ LAWS _ _ _ _ _ PM2 Ho). lia.
    - unfold scratch_k. rewrite SP1. intros [H|H]; [lia | pose proof ERRNO_LOW; lia].
    - intros HE. cbv beta in HE. destruct HE as [H|[(k & Hk & H)|[H|H]]].
      + unfold G_REC, OFF_ANSWER in H. lia.
      + pose proof (BRNG old k Hk). lia.
      + destruct FR1h as (F1a & F1b & F1c). lia.
      + destruct FR2h as (F2a & F2b & F2c). lia. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HF12 (bv_unsigned sp - 56 + i) ltac:(lia) ltac:(unfold HAND_BACK_K, XSTRDUP_K, ALLOC_STACK; lia))
      as [Q12m Q12w].
    split; [exact Q12m | tauto]. }
  rewrite E1_1, SEGS.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of.
    assert (Q2' : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -96)).
    { replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) by ring.
      exact (eq_trans (PR2 2 ltac:(unfold callee_saved; lia)) E1_2). }
    rewrite Q2'.
    eapply sa_seg_epi; [ | lia].
    replace (bv_unsigned sp + -56) with (bv_unsigned sp - 56) by ring. exact FR2. }
  intros ms5 (can5 & Q5 & EQ5). subst can5.
  destruct (RecAnsB.eqv_mkst_fx _ _ _ _ _ _ _ EQ5) as (R5 & -> & X5). clear EQ5.
  assert (HB' : exists kold, (old = 0 /\ blocks Lc Ac = c1 ++ c2) \/
                             (old <> 0 /\ In (old, kold) Oc /\ blocks Lc Ac = c1 ++ (old, kold) :: c2)).
  { destruct HBk as [H|(k & H)]; [exists 0; left; exact H | exists k; right; exact H]. }
  destruct HB' as [kold HB'].
  assert (STAB : forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
            In (p, k) (user_blocks Ac) /\ ptr_addr Lc p = ptr_addr L p).
  { intros p k Hu Hno.
    split; [exact (rjr_in_cur B (aa_MR API) SUP_ADD_K (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md
                     Lc Ac m1 mdc p k RJ1 Hu Hno)|].
    exact (ptr_addr_stable A L Lc p k HWA Hu HL). }
  assert (R2r : rjr B (aa_MR API) SUP_ADD_K (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md L2 A2 m2 md2).
  { apply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW SUP_ADD_K (bv_unsigned sp) rec_area (fun pn => In pn O)
             L A mem md Lc Ac m1 mdc HAND_BACK_K R1 _ (fun a => a = old) L2 A2 R2 m2 md2 RJ1 POST2).
    - rewrite SP1. unfold SUP_ADD_K, HAND_BACK_K, XSTRDUP_K, ALLOC_STACK. lia.
    - rewrite SP1. lia.
    - intros a Ha Hf. cbv beta in Ha.
      destruct Ha as [H|[(k & Hk & H)|[H|H]]].
      + unfold rec_area, G_REC, REC_SC, OFF_ANSWER, SC_SIZE, REC_SIZE, SUP_ADD_K in *. split; [lia|]. lia.
      + exfalso. unfold blocks in Hk. apply in_map_iff in Hk as ([pq kq] & Eq & Uq). cbn [fst snd] in Eq.
        injection Eq as Eo Ek. subst kq.
        pose proof (mr_blocks_range B _ LAWS Lc Ac m1 mdc pq k HM1 Uq).
        pose proof (ax_blocks_img AX Lc Ac m1 mdc pq k (a - ptr_addr Lc pq) HM1 Uq ltac:(lia)) as NI.
        replace (ptr_addr Lc pq + (a - ptr_addr Lc pq)) with a in NI by ring.
        destruct Hf as [Hf|(Hf & _)]; [lia | exact (NI Hf)].
      + exfalso. destruct FR1h as (F1a & F1b & F1c).
        destruct Hf as [Hf|(Hf & _)]; [lia|].
        apply (F1c (a - p1)); [lia|]. replace (p1 + (a - p1)) with a by ring. exact Hf.
      + exfalso. destruct FR2h as (F2a & F2b & F2c).
        destruct Hf as [Hf|(Hf & _)]; [lia|].
        apply (F2c (a - p2)); [lia|]. replace (p2 + (a - p2)) with a by ring. exact Hf.
    - intros p k Hu Hno Hk E.
      destruct (STAB p k Hu Hno) as [Hu1 Ep].
      pose proof (mr_blocks_range B (aa_MR API) LAWS L A mem md p k HMR Hu) as Hr.
      destruct HB' as [(E0 & _)|(NZ & Ho & EB)]; [lia|].
      assert (Hob : In (old, kold) (blocks Lc Ac)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
      pose proof (user_in_blocks Lc Ac p k Hu1) as Hb. rewrite Ep, E in Hb.
      pose proof (rec_rep_pos rsegs G_REC REC_SC Lc Ac m1 Rc Oc (old, kold) GR1 Ho) as Hk0. cbn [snd] in Hk0.
      assert (Ek : k = kold) by exact (blocks_same_addr B (aa_MR API) LAWS Lc Ac m1 mdc old k kold HM1 Hb Hob Hk Hk0).
      subst k. rewrite E in Hno.
      destruct (ON _ Ho) as [H|H]; [exact (Hno H)|]. apply H. rewrite <- E. exact (user_in_blocks L A p kold Hu).
    - intros p k Hu Hu1 Hu'.
      destruct (in_dec pair_dec (ptr_addr L p, k) O) as [H|H]; [exact H|]. exfalso. apply Hu'. apply UBK; [exact Hu1|].
      rewrite (ptr_addr_stable A L Lc p k HWA Hu HL). intros Ho.
      destruct (ON _ Ho) as [H'|H']; [exact (H H') | exact (H' (user_in_blocks L A p k Hu))].
    - exact REG2.
    - rewrite INIT2. discriminate. }
  assert (RP : regs_preserved regs R5).
  { intros r Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia).
    repeat (destruct C as [C|C]; [subst r; sa_pres X5 PR2 X1 KT R1|]).
    subst r. sa_pres X5 PR2 X1 KT R1. }
  pose proof (rjr_final B (aa_MR API) CTX SUP_ADD_K rec_area (fun pn => In pn O) (fun a => In a (map fst O))
                L A regs mem md L2 A2 R5 m2 md2 PRK R2r RP ltac:(intros a k G; exact (in_map fst O (a, k) G))) as FIN.
  pose proof (rjr_others_kept B (aa_MR API) SUP_ADD_K (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md
                L2 A2 m2 md2 O R2r (fun pn H => H)) as OK.
  destruct (tail_owns_blocks (blocks L A) (blocks Lc Ac) (blocks L2 A2) O Oc O2 c1 c2 old kold p1 p2 n
              ON B1 B2 HB' NI1 HO' HBC) as [OWN BLK].
  assert (Hq : In (p2, n) (blocks L2 A2)) by (apply HIFF; right; right; reflexivity).
  assert (RPC : ret_pc (getr regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  apply SR_ret. unfold sa_tret.
  exists (mkFP F1 fc1), L2, A2, R5, m2, md2, O2, p2.
  split; [rewrite SEGS, RPC; reflexivity|].
  split.
  { unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
    intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split; [exact FIN|].
  split; [rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; exact A0'|].
  split; [exact GREP'|].
  split; [exact OWN|].
  split; [exact BLK|].
  split; [exact Hq|].
  split; [exact FR2h|].
  split; [intros Hin; apply in_map_iff in Hin as (pn & Epn & Hpn); exact (HO2 pn Hpn Epn)|].
  split; [exact BY2|].
  split; [exact OK|].
  split.
  { intros p0 k0 Hu0 Hno0.
    enough (D : ptr_addr L p0 + k0 <= p2 \/ p2 + n <= ptr_addr L p0) by (unfold n in D; lia).
    revert p0 k0 Hu0 Hno0.
    apply (q_apart_tail B (aa_MR API) LAWS (ms_segs B) L A mem L2 A2 m2 md2 O p2 n PM2 OK Hq).
    intros p k Hu Hno. destruct (STAB p k Hu Hno) as [Hu1 Ep].
    apply (tail_q_distinct (blocks L A) (blocks Lc Ac) O Oc c1 c2 old kold p2 n (ptr_addr L p, k) ON HB' NI2).
    - exact (user_in_blocks L A p k Hu).
    - exact Hno.
    - rewrite <- Ep. exact (user_in_blocks Lc Ac p k Hu1). }
  split; [exact RA2|].
  split.
  { destruct (ax_statics AX L2 A2 m2 md2 PM2) as (_ & (g & Hg & HGW) & _).
    rewrite SEGS. apply (RecAnsB.f18_words_after m1 m2 g F181); [| exact Hg | rewrite SEGS, GRD in HGW; exact HGW].
    intros i Hi. unfold snprintf_c.GOT_GUARD. rewrite <- GOTG, <- SEGS. exact (GK2 i Hi). }
  split; [exact INIT2|]. split; [lia|].
  rewrite <- (sb_shift_trans bc A Ac A2).
  split; [eapply sb_le_trans; [exact GR2 | apply sb_malloc_mono; apply sb_malloc_mono; exact BLE] | exact RES2].
Qed.

Lemma sa_oor : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  -2^31 <= id < 2^31 -> ~ (0 <= id < 10000) ->
  sb_le (sb_shift b A Ac) bpre ->
  room_slots (sb_malloc (sb_malloc bpre (Z.of_nat (length (resp (-1))) + 1)) (Z.of_nat (length (resp (-1))) + 1))
    (Z.of_nat (length (resp (-1))) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 96) -> getr regs_t 8 = Z_to_bv 64 id ->
  kept_ex [2; 8; 9; 18; 19; 20; 21] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x15a6c) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (hand_back (rec_record R REC_ADD As) (resp (-1)))) (resp (-1)) b bpre).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN AX CTX SNP HB.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id PRE SI HID OR BLE ROOM FRM FR T2 T8 KT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _).
  pose proof RJ as (HM & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  destruct (rjr_bounds B _ SUP_ADD_K (spZ regs) rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  unfold SUP_ADD_K in HK1.
  assert (Q8 : reg_get regs_t 8 = Z_to_bv 64 id) by exact T8.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8. eapply sa_seg_oor; [exact HID | exact OR]. }
  intros ms1 (can1 & E1 & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  assert (U2 : bv_unsigned (reg_get regs_t 2) = bv_unsigned sp - 96).
  { change (reg_get regs_t 2) with (getr regs_t 2). rewrite T2. apply unsigned_lit. lia. }
  apply (sa_resp L A regs mem md O Lc Ac mc mdc _ Oc b bpre R2 (-1) PRE SI).
  - rewrite (getr_of_eqv _ _ 2 X2 eq_refl). simp_regs. exact T2.
  - rewrite (getr_of_eqv _ _ 10 X2 eq_refl). simp_regs. rewrite U2. change (spZ regs) with (bv_unsigned sp). f_equal. lia.
  - rewrite (getr_of_eqv _ _ 11 X2 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 12 X2 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 13 X2 eq_refl). simp_regs. reflexivity.
  - lia.
  - apply (kept_ex_trans _ regs regs_t R2 KT). kept_ex_tac X2.
  - exact FR.
  - exact FRM.
  - exact BLE.
  - eapply room_slots_mono; [| | exact ROOM]; [apply sb_malloc_mono, sb_malloc_mono; exact BLE | lia].
Qed.

Lemma sa_ref : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  (length (r_calls R) <= 16)%nat -> r_refuse (rec_record R REC_ADD As) <> 0 ->
  sb_le (sb_shift b A Ac) bpre ->
  room_slots (sb_malloc (sb_malloc bpre (Z.of_nat (length (resp (r_code (rec_record R REC_ADD As)))) + 1))
                (Z.of_nat (length (resp (r_code (rec_record R REC_ADD As)))) + 1))
    (Z.of_nat (length (resp (r_code (rec_record R REC_ADD As)))) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 96) -> getr regs_t 9 = Z_to_bv 64 0x33d10 ->
  getr regs_t 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  kept_ex [2; 8; 9; 18; 19; 20; 21] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x15a90) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (hand_back (rec_record R REC_ADD As) (resp (r_code (rec_record R REC_ADD As)))))
       (resp (r_code (rec_record R REC_ADD As))) b bpre).
Proof using SEGS ERRNO_LOW AX CTX SLACK ANSF.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t PRE SI H16 RNZ BLE ROOM FRM FR T2 T9 T18 KT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  set (R1 := rec_record R REC_ADD As) in *.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & HC & HA & HP & HX & HW).
  pose proof HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (RC1 : rw_cells rsegs mc 0x33d48 [C4 (Z_to_bv 64 (r_refuse R1))]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x33d48 with (G_REC + OFF_REFUSE) by (unfold G_REC, OFF_REFUSE; lia). exact X1. }
  assert (Q2 : reg_get regs_t 2 = Z_to_bv 64 (bv_unsigned sp + -96)).
  { replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) by ring. exact T2. }
  assert (Q9 : reg_get regs_t 9 = Z_to_bv 64 0x33d10) by exact T9.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2, Q9.
    eapply sa_seg_ref; [ | lia | exact RC1 | exact X6 | exact RNZ].
    replace (bv_unsigned sp + -56) with (bv_unsigned sp - 56) by ring. exact FR. }
  intros ms1 (can1 & E1 & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2r).
  assert (E2_1 : getr R2 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X2r eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X2r eq_refl); simp_regs; reflexivity).
  assert (E2_10 : getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R)).
  { rewrite (getr_of_eqv _ _ 10 X2r eq_refl). simp_regs. exact T18. }
  assert (E2_11 : getr R2 11 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 11 X2r eq_refl); simp_regs; reflexivity).
  assert (E2_12 : getr R2 12 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 12 X2r eq_refl); simp_regs; reflexivity).
  assert (RP2 : regs_preserved regs R2).
  { apply (kept_ex_pres [2; 8; 9; 18; 19; 20; 21]).
    - apply (kept_ex_trans _ regs regs_t R2 KT). kept_ex_tac X2r.
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X2r eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (AK : ANSWER_K <= SUP_ADD_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (ESA : rec_answer R1 (REC_ADD, As) [] false = hand_back R1 (resp (r_code R1))).
  { unfold rec_answer. rewrite (proj2 (Z.eqb_neq _ _) RNZ). reflexivity. }
  eapply SR_mono.
  { apply (sinv_answer B API SEGS ERRNO_LOW AX CTX (ANSF fx) SLACK SUP_ADD_K L A regs mem md O Lc Ac R2 mc mdc
             R1 Oc b bpre (rec_entry G_REC REC_SC R) 0 (REC_ADD, As) [] false PRE AK SI E2_1
             ltac:(unfold spZ; rewrite E2_2; reflexivity) RP2 E2_10 E2_11 ltac:(rewrite E2_12; reflexivity)).
    - intros H. exfalso. exact (RNZ H).
    - intros H. exfalso. exact (RNZ H).
    - exact FRM.
    - exact BLE.
    - rewrite ESA. cbn [snd hand_back].
      eapply room_slots_mono; [| | exact ROOM]; [apply sb_malloc_mono, sb_malloc_mono; exact BLE | lia]. }
  intros c' TR. unfold tail_ret in TR. rewrite ESA in TR. exact TR.
Qed.

Lemma sa_mixarm : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  (length (r_calls R) <= 16)%nat -> length As = 4%nat ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) As -> r_refuse (rec_record R REC_ADD As) = 0 ->
  -2^31 <= id < 2^31 ->
  sb_le (sb_shift b A Ac) bpre ->
  room_slots (sb_malloc (sb_malloc bpre (Z.of_nat (length (resp id)) + 1)) (Z.of_nat (length (resp id)) + 1))
    (Z.of_nat (length (resp id)) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 96) -> getr regs_t 8 = Z_to_bv 64 id ->
  getr regs_t 9 = Z_to_bv 64 0x33d10 -> getr regs_t 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  kept_ex [2; 8; 9; 18; 19; 20; 21] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x15a90) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (hand_back (rec_mix (rec_record R REC_ADD As) (REC_ADD, As)) (resp id)))
       (resp id) b bpre).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN AX CTX SLACK SNP HB MIX.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id PRE SI H16 LA4 LXA RZ HID BLE ROOM FRM FR
    T2 T8 T9 T18 KT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (sa_entry_bounds R) as (EB1 & EB2).
  set (R1 := rec_record R REC_ADD As) in *.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & HC & HA & HP & HX & HW).
  pose proof HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (RC1 : rw_cells rsegs mc 0x33d48 [C4 (Z_to_bv 64 (r_refuse R1))]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x33d48 with (G_REC + OFF_REFUSE) by (unfold G_REC, OFF_REFUSE; lia). exact X1. }
  destruct (rec_rep_entry _ _ _ _ _ _ _ _ _ _ GR H16) as (P & CA).
  destruct CA as (CF1 & CF2 & CLP & CFN & CNA & CND & CKA). cbn [fst snd] in *.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (args := combine (map (fun pn => Z_to_bv 64 (fst pn)) P) As).
  assert (LP : length (map (fun pn => Z_to_bv 64 (fst pn)) P) = length As) by (rewrite length_map; exact CLP).
  assert (LA : length args = length As) by (unfold args; rewrite length_combine, LP; lia).
  assert (U2 : bv_unsigned (reg_get regs_t 2) = bv_unsigned sp - 96).
  { change (reg_get regs_t 2) with (getr regs_t 2). rewrite T2. apply unsigned_lit. lia. }
  assert (ARGS : forall k p, nth_error args k = Some p ->
            mc_arg (normalize rsegs mc) (bv_unsigned sp - 96 - 80) (bv_unsigned sp - 96) e k p).
  { intros k [w s] Hk. destruct (sa_nth_combine _ _ _ _ k w s Hk) as (Hw & Hs).
    rewrite nth_error_map in Hw. destruct (nth_error P k) as [pn|] eqn:EP; cbn in Hw; [|discriminate].
    injection Hw as <-.
    destruct (CKA k s pn Hs EP) as (BP & PNZ & PIN & PSZ & PBS & PN0).
    apply (sa_mc_arg Lc Ac mc mdc e k pn s); [exact HM | exact RA | exact BP | exact PIN | lia | exact PBS | exact PN0 | | lia].
    rewrite Forall_forall in LXA. apply LXA. exact (nth_error_In _ _ Hs). }
  assert (EF : bytes_at rsegs (normalize rsegs mc) e
                 (le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 (Z.of_nat (length args))))).
  { apply bytes_at_normalize; [exact RA|]. apply bytes_at_app. split.
    - unfold CALL_OFF_FN in CFN. rewrite Z.add_0_r in CFN. exact CFN.
    - rewrite LA. replace (e + Z.of_nat (length (le4 (Z_to_bv 64 0)))) with (e + CALL_OFF_NARGS)
        by (rewrite length_le4; unfold CALL_OFF_NARGS; reflexivity). exact CNA. }
  assert (STn : stk rsegs (normalize rsegs mc) (bv_unsigned sp - 12384) (bv_unsigned sp - 96)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC. left. unfold SUP_ADD_K. lia. }
  assert (RC1n : rw_cells rsegs (normalize rsegs mc) 0x33d48 [C4 (Z_to_bv 64 0)]).
  { rewrite RZ in RC1. apply rw_cells_normalize; [exact RA | exact RC1 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N. lia. }
  assert (ESn : rw_cells rsegs (normalize rsegs mc) 0x340f8 [C8 (Z_to_bv 64 (r_state R1))]).
  { apply rw_cells_normalize; [exact RA | | intros i Hi; cbn in Hi; apply glob_ro_false; unfold GLOB_LO, GLOB_N; lia].
    apply rc_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x340f8 with (G_REC + OFF_STATE) by (unfold G_REC, OFF_STATE; lia). exact X4. }
  assert (Q9 : reg_get regs_t 9 = Z_to_bv 64 0x33d10) by exact T9.
  assert (Q18 : reg_get regs_t 18 = Z_to_bv 64 e) by exact T18.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q9, Q18.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply (sa_run_mix MIX) with (lo := bv_unsigned sp - 12384);
      [apply mem_inv_normalize | rewrite U2; exact STn | rewrite U2; lia | lia | exact RC1n
      | exact EF | lia | lia | rewrite LA, LA4; lia | | exact ESn | exact X9].
    intros k p Hk. rewrite U2. exact (ARGS k p Hk). }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m1n & -> & MU1n & WM1n & ES1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mc RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mc RA) MR1r RO1 WM1n) as WM1.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR1r ES1n) as ES1.
  rewrite U2 in MU1. unfold args in ES1. rewrite (sa_combine_snd _ _ _ _ LP) in ES1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2r).
  assert (HWW : forall a, 0 <= a < 2 ^ 64 ->
            ~ outside [(bv_unsigned sp - 96 - 80, bv_unsigned sp - 96); (0x340f8, 0x34100)] a ->
            bv_unsigned sp - SUP_ADD_K <= a < bv_unsigned sp \/ rec_area a).
  { intros a Ra Hm. cbn in Hm. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, SUP_ADD_K. lia. }
  assert (SI2 : sinv B API SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac m1 mdc (rec_mix R1 (REC_ADD, As)) Oc b).
  { apply (sinv_munch_core B API SEGS GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc R1 Oc b m1 _
             (rec_mix R1 (REC_ADD, As)) SI MU1 WM1 HWW).
    unfold g_rec_rep in *.
    apply (rec_rep_set_state rsegs G_REC REC_SC Lc Ac mc m1 R1 Oc (mixcall (r_state R1) REC_ADD As) GR).
    - apply mixcall_range. exact X9.
    - replace (G_REC + OFF_STATE) with 0x340f8 by (unfold G_REC, OFF_STATE; lia). exact (rc_c8_bytes m1 0x340f8 _ ES1).
    - intros a Ha N. apply (munch_mbyte rsegs _ mc m1 a MU1); [unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia|].
      match goal with |- outside ?W a => destruct (outside_dec W a) as [H|H]; [exact H|] end. exfalso.
      cbn in H. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, OFF_STATE in *. lia.
    - intros a Ha _. apply glob_writable. apply sa_glob. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha. lia.
    - exact (sinv_kept B API SEGS AX SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc R1 Oc b m1 _ SI MU1 HWW). }
  assert (FR2 : rw_cells rsegs m1 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ mc m1 _ _ FR MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  apply (sa_resp L A regs mem md O Lc Ac m1 mdc (rec_mix R1 (REC_ADD, As)) Oc b bpre R2 id PRE SI2).
  - rewrite (getr_of_eqv _ _ 2 X2r eq_refl). simp_regs. exact T2.
  - rewrite (getr_of_eqv _ _ 10 X2r eq_refl). simp_regs. rewrite U2. change (spZ regs) with (bv_unsigned sp). f_equal. lia.
  - rewrite (getr_of_eqv _ _ 11 X2r eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 12 X2r eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 13 X2r eq_refl). simp_regs. exact T8.
  - exact HID.
  - apply (kept_ex_trans _ regs regs_t R2 KT). kept_ex_tac X2r.
  - exact FR2.
  - exact FRM.
  - exact BLE.
  - eapply room_slots_mono; [| | exact ROOM]; [apply sb_malloc_mono, sb_malloc_mono; exact BLE | lia].
Qed.

Lemma sa_tail : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  (length (r_calls R) <= 16)%nat -> length As = 4%nat ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) As -> -2^31 <= id < 2^31 ->
  sb_le (sb_shift b A Ac) bpre ->
  room_slots (sb_malloc (sb_malloc bpre (Z.of_nat (length (snd (sa_m R As id))) + 1))
                (Z.of_nat (length (snd (sa_m R As id))) + 1)) (Z.of_nat (length (snd (sa_m R As id))) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 96) -> getr regs_t 8 = Z_to_bv 64 id ->
  getr regs_t 9 = Z_to_bv 64 0x33d10 -> getr regs_t 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  kept_ex [2; 8; 9; 18; 19; 20; 21] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x15a6c) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (sa_m R As id)) (snd (sa_m R As id)) b bpre).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN AX CTX SLACK SNP HB MIX ANSF.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id PRE SI H16 LA4 LXA HID BLE ROOM FRM FR
    T2 T8 T9 T18 KT.
  unfold sa_m in ROOM |- *. cbv zeta in ROOM |- *.
  destruct (Z_lt_le_dec id 0) as [N0|P0].
  1: { assert (RG : ((id <? 0) || (10000 <=? id)) = true) by (apply orb_true_iff; left; apply Z.ltb_lt; lia).
       rewrite RG in ROOM |- *.
       exact (sa_oor L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id PRE SI HID ltac:(lia) BLE ROOM FRM FR
                T2 T8 KT). }
  destruct (Z_lt_le_dec id 10000) as [P1|N1].
  2: { assert (RG : ((id <? 0) || (10000 <=? id)) = true) by (apply orb_true_iff; right; apply Z.leb_le; lia).
       rewrite RG in ROOM |- *.
       exact (sa_oor L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id PRE SI HID ltac:(lia) BLE ROOM FRM FR
                T2 T8 KT). }
  assert (RG : ((id <? 0) || (10000 <=? id)) = false)
    by (apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
  rewrite RG in ROOM |- *.
  pose proof (aa_laws API) as LAWS.
  pose proof SI as (RJ & _). pose proof RJ as (HM & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  assert (Q8 : reg_get regs_t 8 = Z_to_bv 64 id) by exact T8.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8. eapply sa_seg_rng. lia. }
  intros ms1 (can1 & (b0 & b1 & E1) & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  assert (KT2 : kept_ex [2; 8; 9; 18; 19; 20; 21] regs R2)
    by (apply (kept_ex_trans _ regs regs_t R2 KT); kept_ex_tac X2).
  assert (U2 : getr R2 2 = Z_to_bv 64 (spZ regs - 96))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; exact T2).
  assert (U8 : getr R2 8 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; reflexivity).
  assert (U9 : getr R2 9 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; exact T9).
  assert (U18 : getr R2 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 18 X2 eq_refl); simp_regs; exact T18).
  destruct (Z.eq_dec (r_refuse (rec_record R REC_ADD As)) 0) as [RZ|RNZ].
  - rewrite (proj2 (Z.eqb_eq _ _) RZ) in ROOM |- *. cbn [negb] in ROOM |- *.
    exact (sa_mixarm L A regs mem md O Lc Ac mc mdc R As Oc b bpre R2 id PRE SI H16 LA4 LXA RZ HID BLE ROOM FRM FR
             U2 U8 U9 U18 KT2).
  - rewrite (proj2 (Z.eqb_neq _ _) RNZ) in ROOM |- *. cbn [negb] in ROOM |- *.
    exact (sa_ref L A regs mem md O Lc Ac mc mdc R As Oc b bpre R2 PRE SI H16 RNZ BLE ROOM FRM FR U2 U9 U18 KT2).
Qed.

Lemma sa_room : forall b n0 n1 n2 n3 nr x, 0 <= n0 -> 0 <= n1 -> 0 <= n2 -> 0 <= n3 -> 0 <= nr -> 0 <= x ->
  room_slots (sb_malloc (sb_malloc (sb_malloc (sb_malloc (sb_malloc (sb_malloc b n0) n1) n2) n3) nr) nr) x ->
  room_slots (sb_malloc b n0) x /\ room_slots (sb_malloc (sb_malloc b n0) n1) x /\
  room_slots (sb_malloc (sb_malloc (sb_malloc b n0) n1) n2) x /\
  room_slots (sb_malloc (sb_malloc (sb_malloc (sb_malloc b n0) n1) n2) n3) x.
Proof.
  intros b n0 n1 n2 n3 nr x H0 H1 H2 H3 H4 H5 RM.
  split; [|split; [|split]];
    (eapply room_slots_mono; [| | exact RM]; [unfold sb_le, sb_malloc; cbn; lia | lia]).
Qed.

Lemma sa_body2 : forall L A regs mem md O Lc Ac mc mdc R uri id pl cl (ppl pcl : Z) Oc b R4,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  getr regs 12 = Z_to_bv 64 ppl -> getr regs 13 = Z_to_bv 64 pcl ->
  str_arg B L A O (spZ regs) SUP_ADD_K mem ppl pl -> str_arg B L A O (spZ regs) SUP_ADD_K mem pcl cl ->
  ro_agree rsegs mem -> frm_zero fp_csr -> -2^31 <= r_code R < 2^31 -> -2^31 <= id < 2^31 ->
  Z.of_nat (length (sarg uri)) <= LMAX ->
  room_slots (sb_mallocs b (sup_add_sizes uri id pl cl (snd (sup_add_m R uri id pl cl)))) (LMAX + 1) ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD [sarg uri; dec id]) Oc b ->
  sb_le (sb_shift b A Ac)
    (sb_malloc (sb_malloc b (Z.of_nat (length (sarg uri)) + 1)) (Z.of_nat (length (dec id)) + 1)) ->
  (length (r_calls R) <= 16)%nat ->
  getr R4 2 = Z_to_bv 64 (spZ regs - 96) -> getr R4 8 = Z_to_bv 64 id -> getr R4 9 = Z_to_bv 64 0x33d10 ->
  getr R4 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R4 19 = getr regs 13 -> getr R4 20 = getr regs 12 ->
  getr R4 21 = Z_to_bv 64 (rec_entry G_REC REC_SC R + 8) ->
  kept_ex [2; 8; 9; 18; 19; 20; 21] regs R4 ->
  rw_cells rsegs mc (spZ regs - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)] ->
  bytes_at rsegs mc (rec_entry G_REC REC_SC R + 4) (le4 (Z_to_bv 64 2)) ->
  SR rsegs (mkCfg (mkst R4 (Z_to_bv 64 0x15a00) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (sup_add_m R uri id pl cl)) (snd (sup_add_m R uri id pl cl)) b
       (sb_malloc (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length (sarg uri)) + 1)) (Z.of_nat (length (dec id)) + 1))
          (Z.of_nat (length (darg pl (bstr "-"%string))) + 1)) (Z.of_nat (length (darg cl (bstr "-"%string))) + 1))).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK XSD SNP HB MIX ANSF.
  intros L A regs mem md O Lc Ac mc mdc R uri id pl cl ppl pcl Oc b R4 PRE APL ACL SPL SCL RA FRM HCODE HID LXU ROOM
    SI BLE HN E2 E8 E9 E18 E19 E20 E21 KT FR NA.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS.
  pose proof (sa_entry_bounds R) as (EB1 & EB2).
  set (e := rec_entry G_REC REC_SC R) in *.
  assert (EE : e = rec_entry G_REC REC_SC R) by reflexivity.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (dec_length id HID) as DL.
  pose proof (sa_m_len R [sarg uri; dec id; darg pl (bstr "-"%string); darg cl (bstr "-"%string)] id HID HCODE) as TL.
  rewrite sa_m_eq in ROOM |- *.
  set (As4 := [sarg uri; dec id; darg pl (bstr "-"%string); darg cl (bstr "-"%string)]) in *.
  set (nt := Z.of_nat (length (snd (sa_m R As4 id))) + 1) in *.
  unfold sup_add_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  pose proof (sa_room b (Z.of_nat (length (sarg uri)) + 1) (Z.of_nat (length (dec id)) + 1)
                (Z.of_nat (length (darg pl (bstr "-"%string))) + 1) (Z.of_nat (length (darg cl (bstr "-"%string))) + 1)
                nt (LMAX + 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold nt; lia) ltac:(unfold LMAX; lia)
                ROOM) as (_ & _ & RM2 & RM3).
  pose proof SI as (RJ & _ & _ & _ & _ & RA1 & _).
  assert (XK : 96 + XSTRDUP_K <= SUP_ADD_K) by (unfold SUP_ADD_K, XSTRDUP_K, ALLOC_STACK; lia).
  assert (XD : forall Lx Ax mx, ro_agree rsegs mx -> xsrc Lx Ax mx (bv_unsigned sp - 96) 0x108b0 (bstr "-"%string)).
  { intros Lx Ax mx RX. apply xsrc_dash; [exact RX | unfold XSTRDUP_K, ALLOC_STACK; lia]. }
  destruct (xsrc_of SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc ppl pl _ _ RJ RA RA1 XK SPL (XD _ _ _ RA1))
    as (PPL & XPL).
  destruct (xsrc_of SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc pcl cl _ _ RJ RA RA1 XK SCL (XD _ _ _ RA1))
    as (PCL & _).
  assert (LXL : Z.of_nat (length (darg pl (bstr "-"%string))) <= LMAX) by exact (proj1 (proj2 XPL)).
  destruct (mr_model B _ LAWS Lc Ac mc mdc (proj1 RJ)) as (Hh & Hl & _).
  assert (NAc : rw_cells rsegs mc (e + 4) [C4 (Z_to_bv 64 2)]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact NA]. }
  assert (Q18 : reg_get R4 18 = Z_to_bv 64 e) by exact E18.
  assert (Q20 : reg_get R4 20 = Z_to_bv 64 ppl) by exact (eq_trans E20 APL).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q18, Q20.
    eapply sa_seg_a1; [exact NAc | exact PPL]. }
  intros ms1 (can1 & (b1 & E1) & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R5 & -> & X5).
  assert (KT5 : kept_ex [2; 8; 9; 18; 19; 20; 21] regs R5)
    by (apply (kept_ex_trans _ regs R4 R5 KT); kept_ex_tac X5).
  assert (E5_1 : getr R5 1 = Z_to_bv 64 0x15a20) by (sa_reg X5; reflexivity).
  assert (E5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 96)) by (sa_reg X5; exact E2).
  assert (E5_8 : getr R5 8 = Z_to_bv 64 id) by (sa_reg X5; exact E8).
  assert (E5_9 : getr R5 9 = Z_to_bv 64 0x33d10) by (sa_reg X5; exact E9).
  assert (E5_10 : getr R5 10 = Z_to_bv 64 (sa_sel ppl 0x108b0)) by (sa_reg X5; reflexivity).
  assert (E5_18 : getr R5 18 = Z_to_bv 64 e) by (sa_reg X5; reflexivity).
  assert (E5_19 : getr R5 19 = Z_to_bv 64 pcl) by (sa_reg X5; exact (eq_trans E19 ACL)).
  assert (E5_21 : getr R5 21 = Z_to_bv 64 (e + 8)) by (sa_reg X5; exact E21).
  assert (T5 : getr R5 4 = getr regs 4) by exact (KT5 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)).
  apply (sa_arg L A regs mem md O Lc Ac mc mdc R [sarg uri; dec id] Oc b _ R5 _ (darg pl (bstr "-"%string)) _ PRE SI
           ltac:(cbn; lia) BLE RM2 ltac:(rewrite E5_1; apply bv_eq; vm_compute; reflexivity) E5_2 T5 E5_10 XPL FR).
  intros L6 A6 R6 m6 md6 p2 RP6 A06 P2 PM6 RA6 FR6 KG6 BLE6 CL6. change (spZ regs) with (bv_unsigned sp) in *.
  destruct (sa_cells_n mc m6 e (Z_to_bv 64 2) 24 EB1 EB2 ltac:(lia) RA6 KG6 NA) as (NAn6 & junk2 & EWn6).
  destruct (mr_model B _ LAWS L6 A6 m6 md6 PM6) as (Hh6 & Hl6 & _).
  assert (R6_10 : reg_get R6 10 = Z_to_bv 64 p2) by exact A06.
  assert (R6_18 : reg_get R6 18 = Z_to_bv 64 e) by exact (eq_trans (RP6 18 ltac:(unfold callee_saved; lia)) E5_18).
  assert (R6_19 : reg_get R6 19 = Z_to_bv 64 pcl) by exact (eq_trans (RP6 19 ltac:(unfold callee_saved; lia)) E5_19).
  assert (R6_21 : reg_get R6 21 = Z_to_bv 64 (e + 8))
    by exact (eq_trans (RP6 21 ltac:(unfold callee_saved; lia)) E5_21).
  rewrite E5_1.
  eapply evt_SR_canon; [ | exact Hh6 | exact Hl6 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R6_10, R6_18, R6_19, R6_21.
    eapply (evt_normalize rsegs); [exact WX | exact RA6 |].
    eapply sa_seg_a2; [exact NAn6 | exact EWn6 | lia | exact PCL]. }
  intros ms7 (can7 & (s7n & Q7 & REL7 & RO7) & EQ7).
  destruct Q7 as (d1' & d2' & d3' & d4' & m7n & -> & MU7n & WM7n & NA7n & EA7n).
  sa_back m6 RA6 can7 REL7 RO7 EQ7 MU7n WM7n NA7n EA7n m7 MU7 WM7 NA7 EA7 R7 X7.
  pose proof NA7 as NB7. apply cells_bytes_at in NB7. cbn [cells_bytes cbytes] in NB7. rewrite app_nil_r in NB7.
  pose proof (CL6 m7 _ MU7 WM7 ltac:(sa_hw EE) ltac:(sa_na NA7) ltac:(sa_ar EE EA7 e 24)) as SI7.
  cbn [app] in SI7.
  assert (KT7 : kept_ex [2; 8; 9; 18; 19; 20; 21] regs R7).
  { apply (kept_ex_trans _ regs R6 R7); [apply (kept_ex_trans _ regs R5 R6 KT5); apply kept_ex_of_pres; exact RP6|].
    kept_ex_tac X7. }
  assert (E7_1 : getr R7 1 = Z_to_bv 64 0x15a54) by (sa_reg X7; reflexivity).
  assert (E7_2 : getr R7 2 = Z_to_bv 64 (bv_unsigned sp - 96))
    by (sa_reg X7; exact (eq_trans (RP6 2 ltac:(unfold callee_saved; lia)) E5_2)).
  assert (E7_8 : getr R7 8 = Z_to_bv 64 id)
    by (sa_reg X7; exact (eq_trans (RP6 8 ltac:(unfold callee_saved; lia)) E5_8)).
  assert (E7_9 : getr R7 9 = Z_to_bv 64 0x33d10)
    by (sa_reg X7; exact (eq_trans (RP6 9 ltac:(unfold callee_saved; lia)) E5_9)).
  assert (E7_10 : getr R7 10 = Z_to_bv 64 (sa_sel pcl 0x108b0)) by (sa_reg X7; reflexivity).
  assert (E7_18 : getr R7 18 = Z_to_bv 64 e) by (sa_reg X7; reflexivity).
  assert (E7_21 : getr R7 21 = Z_to_bv 64 (e + 8)) by (sa_reg X7; reflexivity).
  assert (T7 : getr R7 4 = getr regs 4) by exact (KT7 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)).
  assert (FR7 : rw_cells rsegs m7 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m6 m7 _ _ FR6 MU7 WM7). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof SI7 as (RJ7 & _ & _ & _ & _ & RA7 & _).
  destruct (xsrc_of SUP_ADD_K (bv_unsigned sp) L A mem md O L6 A6 m7 md6 pcl cl _ _ RJ7 RA RA7 XK SCL (XD _ _ _ RA7))
    as (_ & XCL).
  assert (LXC : Z.of_nat (length (darg cl (bstr "-"%string))) <= LMAX) by exact (proj1 (proj2 XCL)).
  apply (sa_arg L A regs mem md O L6 A6 m7 md6 R [sarg uri; dec id; darg pl (bstr "-"%string)] _ b _ R7 _
           (darg cl (bstr "-"%string)) _ PRE SI7 ltac:(cbn; lia) BLE6 RM3
           ltac:(rewrite E7_1; apply bv_eq; vm_compute; reflexivity) E7_2 T7 E7_10 XCL FR7).
  intros L8 A8 R8 m8 md8 p3 RP8 A08 P3 PM8 RA8 FR8 KG8 BLE8 CL8. change (spZ regs) with (bv_unsigned sp) in *.
  destruct (sa_cells_n m7 m8 e (Z_to_bv 64 3) 32 EB1 EB2 ltac:(lia) RA8 KG8 NB7) as (NAn8 & junk3 & EWn8).
  destruct (mr_model B _ LAWS L8 A8 m8 md8 PM8) as (Hh8 & Hl8 & _).
  assert (R8_10 : reg_get R8 10 = Z_to_bv 64 p3) by exact A08.
  assert (R8_18 : reg_get R8 18 = Z_to_bv 64 e) by exact (eq_trans (RP8 18 ltac:(unfold callee_saved; lia)) E7_18).
  assert (R8_21 : reg_get R8 21 = Z_to_bv 64 (e + 8))
    by exact (eq_trans (RP8 21 ltac:(unfold callee_saved; lia)) E7_21).
  rewrite E7_1.
  eapply evt_SR_canon; [ | exact Hh8 | exact Hl8 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R8_10, R8_18, R8_21.
    eapply (evt_normalize rsegs); [exact WX | exact RA8 |].
    eapply sa_seg_a3; [exact NAn8 | exact EWn8 | lia]. }
  intros ms9 (can9 & (s9n & Q9 & REL9 & RO9) & EQ9).
  destruct Q9 as (f1' & f2' & m9n & -> & MU9n & WM9n & NA9n & EA9n).
  sa_back m8 RA8 can9 REL9 RO9 EQ9 MU9n WM9n NA9n EA9n m9 MU9 WM9 NA9 EA9 R9 X9.
  pose proof (CL8 m9 _ MU9 WM9 ltac:(sa_hw EE) ltac:(sa_na NA9) ltac:(sa_ar EE EA9 e 32)) as SI9.
  cbn [app] in SI9.
  assert (KT9 : kept_ex [2; 8; 9; 18; 19; 20; 21] regs R9).
  { apply (kept_ex_trans _ regs R8 R9); [apply (kept_ex_trans _ regs R7 R8 KT7); apply kept_ex_of_pres; exact RP8|].
    kept_ex_tac X9. }
  assert (E9_2 : getr R9 2 = Z_to_bv 64 (bv_unsigned sp - 96))
    by (sa_reg X9; exact (eq_trans (RP8 2 ltac:(unfold callee_saved; lia)) E7_2)).
  assert (E9_8 : getr R9 8 = Z_to_bv 64 id)
    by (sa_reg X9; exact (eq_trans (RP8 8 ltac:(unfold callee_saved; lia)) E7_8)).
  assert (E9_9 : getr R9 9 = Z_to_bv 64 0x33d10)
    by (sa_reg X9; exact (eq_trans (RP8 9 ltac:(unfold callee_saved; lia)) E7_9)).
  assert (E9_18 : getr R9 18 = Z_to_bv 64 e) by (sa_reg X9; reflexivity).
  assert (FR9 : rw_cells rsegs m9 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m8 m9 _ _ FR8 MU9 WM9). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  apply (sa_tail L A regs mem md O L8 A8 m9 md8 R As4 _ b _ R9 id PRE SI9 HN eq_refl).
  - unfold As4. apply Forall_cons; [exact LXU|]. apply Forall_cons; [cbv beta; unfold LMAX; lia|].
    apply Forall_cons; [exact LXL|]. apply Forall_cons; [exact LXC|]. apply Forall_nil.
  - exact HID.
  - exact BLE8.
  - eapply room_slots_mono; [| | exact ROOM]; [apply sb_le_refl | unfold nt in TL |- *; unfold LMAX; lia].
  - exact FRM.
  - exact FR9.
  - exact E9_2.
  - exact E9_8.
  - exact E9_9.
  - exact E9_18.
  - exact KT9.
Qed.

End H.

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
Hypothesis XSD : forall fx0 : YK11.FPState, @xstrdup_contract fx0 rc B API.
Hypothesis ARGI : arg_i_contract B API.
Hypothesis SNP : snprintf_contract.
Hypothesis HB : forall fx0 : YK11.FPState, @hand_back_contract fx0 rc B API.
Hypothesis MIX : mix_call_contract.
Hypothesis ANSF : forall fx0 : YK11.FPState, @answer_contract fx0 rc B API.

Lemma sa_body1 : forall L A regs mem md (pu ppl pcl : Z) uri id pl cl R O b Lc Ac R1 m1 md1 Oc,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  getr regs 10 = Z_to_bv 64 pu -> getr regs 11 = Z_to_bv 64 id -> -2^31 <= id < 2^31 ->
  getr regs 12 = Z_to_bv 64 ppl -> getr regs 13 = Z_to_bv 64 pcl ->
  str_arg B L A O (spZ regs) SUP_ADD_K mem pu uri -> str_arg B L A O (spZ regs) SUP_ADD_K mem ppl pl ->
  str_arg B L A O (spZ regs) SUP_ADD_K mem pcl cl ->
  ro_agree rsegs mem -> frm_zero fp_csr -> -2^31 <= r_code R < 2^31 ->
  room_slots (sb_mallocs b (sup_add_sizes uri id pl cl (snd (sup_add_m R uri id pl cl)))) (LMAX + 1) ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac m1 md1 (rec_record R REC_ADD []) Oc b ->
  sb_le (sb_shift b A Ac) b -> (length (r_calls R) <= 16)%nat ->
  getr R1 1 = Z_to_bv 64 0x159d8 -> getr R1 2 = Z_to_bv 64 (spZ regs - 96) ->
  getr R1 8 = getr regs 11 -> getr R1 9 = Z_to_bv 64 0x33d10 -> getr R1 10 = Z_to_bv 64 (sa_sel pu 0x10a19) ->
  getr R1 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R1 19 = getr regs 13 -> getr R1 20 = getr regs 12 ->
  kept_ex [2; 8; 9; 18; 19; 20; 21] regs R1 ->
  rw_cells rsegs m1 (spZ regs - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)] ->
  bytes_at rsegs m1 (rec_entry G_REC REC_SC R + 4) (le4 (Z_to_bv 64 0)) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15780) m1 (seg_rom rsegs)) md1)
    (sup_add_ret B API L A regs mem md uri id pl cl R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK XSD ARGI SNP HB MIX ANSF.
  intros L A regs mem md pu ppl pcl uri id pl cl R O b Lc Ac R1 m1 md1 Oc PRE AU AI HID APL ACL SU SPL SCL RA FRM HCODE
    ROOM SI1 BLE1 HN E1_1 E1_2 E1_8 E1_9 E1_10 E1_18 E1_19 E1_20 KT1 FR1 NA1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS.
  pose proof (sa_entry_bounds R) as (EB1 & EB2).
  pose proof (dec_length id HID) as DL.
  pose proof (sa_m_len R [sarg uri; dec id; darg pl (bstr "-"%string); darg cl (bstr "-"%string)] id HID HCODE) as TL.
  pose proof ROOM as ROOM0. rewrite sa_m_eq in ROOM0.
  unfold sup_add_sizes, sb_mallocs in ROOM0. cbn [fold_left] in ROOM0.
  pose proof (sa_room b (Z.of_nat (length (sarg uri)) + 1) (Z.of_nat (length (dec id)) + 1)
                (Z.of_nat (length (darg pl (bstr "-"%string))) + 1) (Z.of_nat (length (darg cl (bstr "-"%string))) + 1)
                (Z.of_nat (length (snd (sa_m R [sarg uri; dec id; darg pl (bstr "-"%string);
                   darg cl (bstr "-"%string)] id))) + 1) (LMAX + 1)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold LMAX; lia) ROOM0)
    as (RM0 & RM1 & _ & _).
  set (e := rec_entry G_REC REC_SC R) in *.
  assert (EE : e = rec_entry G_REC REC_SC R) by reflexivity.
  assert (ER : e mod 8 = 0 /\ REC_SC <= e /\ e + CALL_SIZE <= G_REC + REC_SIZE).
  { rewrite EE. unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE, REC_SC, REC_SIZE.
      split; [|lia]. apply Z.mod_divide; [lia|]. exists (26539 + 7 * Z.of_nat (length (r_calls R))). lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. split; [reflexivity | lia]. }
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof SI1 as (RJ1 & _ & _ & _ & _ & RA1 & _).
  assert (XK : 96 + XSTRDUP_K <= SUP_ADD_K) by (unfold SUP_ADD_K, XSTRDUP_K, ALLOC_STACK; lia).
  destruct (xsrc_of B API SEGS ERRNO_LOW SLACK SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac m1 md1 pu uri _ _ RJ1 RA
              RA1 XK SU (xsrc_null B SEGS Lc Ac m1 (bv_unsigned sp - 96) RA1 ltac:(unfold XSTRDUP_K, ALLOC_STACK; lia)))
    as (PU & XU).
  assert (LXU : Z.of_nat (length (sarg uri)) <= LMAX) by exact (proj1 (proj2 XU)).
  assert (T1 : getr R1 4 = getr regs 4) by exact (KT1 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)).
  apply (sa_arg B API SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX XSD L A regs mem md O Lc Ac m1 md1 R [] Oc b b R1 _
           (sarg uri) _ PRE SI1 ltac:(cbn; lia) BLE1 RM0 ltac:(rewrite E1_1; apply bv_eq; vm_compute; reflexivity)
           E1_2 T1 E1_10 XU FR1).
  intros L2 A2 R2 m2 md2 p0 RP2 A02 P0 PM2 RA2 FR2 KG2 BLE2 CL2. change (spZ regs) with (bv_unsigned sp) in *.
  destruct (sa_cells_n m1 m2 e (Z_to_bv 64 0) 8 EB1 EB2 ltac:(lia) RA2 KG2 NA1) as (NAn & junk0 & EWn).
  destruct (mr_model B _ LAWS L2 A2 m2 md2 PM2) as (Hh2 & Hl2 & _).
  assert (R2_10 : reg_get R2 10 = Z_to_bv 64 p0) by exact A02.
  assert (R2_18 : reg_get R2 18 = Z_to_bv 64 e) by exact (eq_trans (RP2 18 ltac:(unfold callee_saved; lia)) E1_18).
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R2_10, R2_18.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply sa_seg_a0; [exact NAn | exact EWn | lia]. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (b2' & m3n & -> & MU3n & WM3n & NA3n & EA3n).
  sa_back m2 RA2 can3 REL3 RO3 EQ3 MU3n WM3n NA3n EA3n m3 MU3 WM3 NA3 EA3 R3 X3.
  pose proof (CL2 m3 _ MU3 WM3 ltac:(sa_hw EE) ltac:(sa_na NA3) ltac:(sa_ar EE EA3 e 8)) as SI3.
  cbn [app] in SI3.
  assert (KT3 : kept_ex [2; 8; 9; 18; 19; 20; 21] regs R3).
  { apply (kept_ex_trans _ regs R2 R3); [apply (kept_ex_trans _ regs R1 R2 KT1); apply kept_ex_of_pres; exact RP2|].
    kept_ex_tac X3. }
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x15a00) by (sa_reg X3; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 96))
    by (sa_reg X3; exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E1_2)).
  assert (E3_4 : getr R3 4 = getr regs 4)
    by (sa_reg X3; exact (eq_trans (RP2 4 ltac:(unfold callee_saved; lia)) T1)).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 id)
    by (sa_reg X3; exact (eq_trans (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E1_8) AI)).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 0x33d10)
    by (sa_reg X3; exact (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) E1_9)).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 e) by (sa_reg X3; reflexivity).
  assert (E3_11 : getr R3 11 = Z_to_bv 64 id)
    by (sa_reg X3; exact (eq_trans (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E1_8) AI)).
  assert (E3_18 : getr R3 18 = Z_to_bv 64 e) by (sa_reg X3; reflexivity).
  assert (E3_19 : getr R3 19 = getr regs 13)
    by (sa_reg X3; exact (eq_trans (RP2 19 ltac:(unfold callee_saved; lia)) E1_19)).
  assert (E3_20 : getr R3 20 = getr regs 12)
    by (sa_reg X3; exact (eq_trans (RP2 20 ltac:(unfold callee_saved; lia)) E1_20)).
  assert (E3_21 : getr R3 21 = Z_to_bv 64 (e + 8)) by (sa_reg X3; reflexivity).
  assert (SP3 : spZ R3 = bv_unsigned sp - 96) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & RA3 & F183 & RS3).
  pose proof RJ3 as (HM3 & _).
  assert (BN3 : bytes_at rsegs m3 (e + CALL_OFF_NARGS) (le4 (Z_to_bv 64 1))).
  { pose proof NA3 as NB3. apply cells_bytes_at in NB3. cbn [cells_bytes cbytes] in NB3. rewrite app_nil_r in NB3.
    exact NB3. }
  pose proof ARGI as AIc. unfold arg_i_contract in AIc. rewrite SEGS in AIc.
  eapply SR_bind.
  { apply (AIc L2 A2 R3 m3 md2 e id 1 (sb_shift b A A2)).
    - split; [|rewrite SP3; lia].
      apply (call_pre_k_of_rjr B _ SUP_ADD_K (bv_unsigned sp) rec_area _ L A mem md L2 A2 m3 md2 ARG_I_K R3 RJ3).
      + rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP3. replace (bv_unsigned sp - 96) with (bv_unsigned sp + (-6) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. unfold SUP_ADD_K, ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. lia.
      + rewrite E3_4. exact HTP.
    - exact E3_10.
    - exact E3_11.
    - exact HID.
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - exact (proj2 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact BN3.
    - lia.
    - exact F183.
    - exact FRM.
    - exact RS3.
    - eapply room_slots_mono; [| | exact RM1]; [apply sb_malloc_mono; exact BLE2 | unfold LMAX; lia].
    - exact RA3. }
  intros c4 (fx' & L4 & A4 & R4 & m4 & md4 & -> & FK & BK4 & UB4 & _ & RA4 & _ & F184 & RGN4 & ALT).
  destruct ALT as [(H06 & _)|(_ & p2 & POST4 & Hp0 & _ & FB4 & BLK4 & BN4 & BS4 & BX4 & INI4 & RS4)]; [lia|].
  rewrite SEGS in RA4, F184, BN4, BS4, BX4 |- *.
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O L2 A2 m3 md2 R
                REC_ADD [sarg uri] _ b ARG_I_K R3 _ L4 A4 R4 m4 md4 (dec id) p2 (Z.of_nat (length (dec id)) + 1)
                SI3 ltac:(cbn; lia) ltac:(rewrite SP3; unfold SUP_ADD_K, ARG_I_K, XSTRDUP_K, ALLOC_STACK; lia)
                ltac:(rewrite SP3; lia) POST4
                ltac:(intros a Ha; cbv beta in Ha; try rewrite <- EE; cbn [length Z.of_nat]; lia)
                Hp0 FB4 BLK4 UB4 BK4 RGN4 BN4 BS4 BX4 (dec_no0 id) ltac:(unfold LMAX; lia) ltac:(unfold LMAX; lia)
                INI4 RS4 RA4 F184) as SI4.
  cbn [app] in SI4.
  pose proof POST4 as (PM4 & _ & _ & _ & _ & RP4 & _).
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct FB4 as (_ & FBb4 & _).
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_I_K L2 A2 R3 m3 md2 _ L4 A4 R4 m4 md4 (bv_unsigned sp - 56 + i)
                HM3 POST4 ltac:(lia) ltac:(rewrite SP3; lia)) as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (BLE4 : sb_le (sb_shift b A A4)
                   (sb_malloc (sb_malloc b (Z.of_nat (length (sarg uri)) + 1)) (Z.of_nat (length (dec id)) + 1))).
  { destruct BLK4 as (bl1 & bl2 & EBa & EBb).
    rewrite <- (sb_shift_trans b A A2 A4).
    rewrite <- (sb_shift_add (sb_shift b A A2) L2 A2 L4 A4 bl1 bl2 p2 _ EBa EBb).
    apply sb_malloc_mono. exact BLE2. }
  assert (KT4 : kept_ex [2; 8; 9; 18; 19; 20; 21] regs R4).
  { apply (kept_ex_trans _ regs R3 R4 KT3). apply kept_ex_of_pres. exact RP4. }
  rewrite E3_1.
  eapply SR_mono.
  { apply (sa_body2 (fx := fx') B API SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK XSD SNP HB MIX ANSF
             L A regs mem md O L4 A4 m4 md4 R uri id pl cl ppl pcl _ b R4 PRE APL ACL SPL SCL RA (proj1 FK) HCODE HID
             LXU ROOM SI4 BLE4 HN).
    - exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E3_2).
    - exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) E3_8).
    - exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E3_9).
    - exact (eq_trans (RP4 18 ltac:(unfold callee_saved; lia)) E3_18).
    - exact (eq_trans (RP4 19 ltac:(unfold callee_saved; lia)) E3_19).
    - exact (eq_trans (RP4 20 ltac:(unfold callee_saved; lia)) E3_20).
    - exact (eq_trans (RP4 21 ltac:(unfold callee_saved; lia)) E3_21).
    - exact KT4.
    - exact FR4.
    - exact BN4. }
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  unfold sup_add_ret.
  exists fx'', L', A', regs', mem', md', (fst (sup_add_m R uri id pl cl)), O', (snd (sup_add_m R uri id pl cl)), q.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact (fpk_trans _ _ _ FK FK')|].
  split; [exact POST'|]. split; [exact A10'|]. split; [exact GR'|]. split; [exact ON'|]. split; [exact BL'|].
  split; [exact IN'|]. split; [exact FB'|]. split; [exact NQ'|]. split; [exact BY'|]. split; [exact OK'|].
  split; [exact AP'|]. split; [exact RA'|]. split; [exact F18'|]. split; [exact INI'|]. split; [exact REG'|].
  split; [exact BLE'|]. exact RES'.
Qed.

Theorem sup_add_holds : sup_add_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK RCF XSD ARGI SNP HB MIX ANSF.
  unfold sup_add_contract.
  intros L A regs mem md pu pp pc uri id pl cl R O b PRE AU AI HID APL ACL SU SPL SCL GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_ADD_K in HCEIL, HWS.
  rewrite SEGS in GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API SUP_ADD_K L A regs mem md R O b PRK ltac:(unfold SUP_ADD_K; lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof SI0 as (RJ0 & _).
  destruct (xsrc_of B API SEGS ERRNO_LOW SLACK SUP_ADD_K (bv_unsigned sp) L A mem md O L A mem md pu uri _ _ RJ0 RA RA
              ltac:(unfold SUP_ADD_K, XSTRDUP_K, ALLOC_STACK; lia) SU
              (xsrc_null B SEGS L A mem (bv_unsigned sp - 96) RA ltac:(unfold XSTRDUP_K, ALLOC_STACK; lia)))
    as (PU & _).
  assert (ST : stk rsegs mem (bv_unsigned sp - 12384) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  set (n := length (r_calls R)) in *.
  assert (NC : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact G3]).
  destruct (Nat.lt_ge_cases n 16) as [Hn|Hn].
  - eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply sa_seg_lt; [exact ST | lia | lia | exact NC | exact Hn]. }
    intros ms1 (can1 & (c0 & c1 & c2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    destruct (glob_rw_cells m1 (0x33d58 + 56 * Z.of_nat n) 8 ltac:(unfold GLOB_LO; lia)
                ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
    assert (E1_18 : getr R1 18 = Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) by (sa_reg X1; reflexivity).
    assert (E1_21 : getr R1 21 = Z_to_bv 64 pu) by (sa_reg X1; exact AU).
    assert (Q18 : reg_get R1 18 = Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) by exact E1_18.
    assert (Q21 : reg_get R1 21 = Z_to_bv 64 pu) by exact E1_21.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q18, Q21.
      eapply sa_seg_rec; [exact EW | exact PU]. }
    intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
    assert (MU : munch [(bv_unsigned sp - 96, bv_unsigned sp); (0x33d50, 0x33d54);
                        (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] mem m2).
    { apply (munch_trans _ mem m1 m2).
      - eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in Hx |- *. tauto.
      - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx |- *. tauto. }
    assert (NC2 : rw_cells rsegs m2 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]).
    { apply (rw_cells_transport rsegs _ m1 m2 _ _ NC1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
      repeat split; lia. }
    pose proof (sinv_record_lt B API SEGS GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O L A mem md R O b m2 _
                  REC_ADD SI0 Hn ltac:(unfold REC_FN_COUNT, REC_ADD; lia) MU (wmono_trans _ _ _ _ WM1 WM2)
                  ltac:(intros a Ra Hm; cbn [outside] in Hm; unfold n in *; unfold SUP_ADD_K; lia) NC2 EN2) as SI1.
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 56)
      [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
       C8 (getr regs 1)]).
    { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
      repeat split; lia. }
    pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
    apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
    apply (sa_body1 L A regs mem md pu pp pc uri id pl cl R O b L A R2 m2 md O PRE AU AI HID APL ACL SU SPL SCL RA FRM
             HCODE ROOM SI1 ltac:(rewrite sb_shift_refl; apply sb_le_refl) ltac:(lia)).
    + sa_reg X2. reflexivity.
    + sa_reg X2. change (reg_get R1 2) with (getr R1 2). sa_reg X1. reflexivity.
    + sa_reg X2. change (reg_get R1 8) with (getr R1 8). sa_reg X1. reflexivity.
    + sa_reg X2. change (reg_get R1 9) with (getr R1 9). sa_reg X1. reflexivity.
    + sa_reg X2. reflexivity.
    + sa_reg X2. rewrite (rec_entry_lt G_REC REC_SC R Hn). fold n. unfold G_REC, OFF_CALLS, CALL_SIZE. f_equal; lia.
    + sa_reg X2. change (reg_get R1 19) with (getr R1 19). sa_reg X1. reflexivity.
    + sa_reg X2. change (reg_get R1 20) with (getr R1 20). sa_reg X1. reflexivity.
    + apply (kept_ex_trans _ regs R1 R2); [kept_ex_tac X1 | kept_ex_tac X2].
    + exact FR2.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). fold n.
      replace (G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n + 4) with (0x33d58 + 56 * Z.of_nat n + Z.of_nat 4)
        by (unfold G_REC, OFF_CALLS, CALL_SIZE; lia).
      exact EA.
  - assert (H16 : n = 16%nat) by lia.
    assert (NC16 : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 16)]) by (rewrite H16 in NC; exact NC).
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply sa_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x1599c) by (sa_reg X1; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 96)) by (sa_reg X1; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (sa_reg X1; reflexivity).
    assert (E1_8 : getr R1 8 = getr regs 11) by (sa_reg X1; reflexivity).
    assert (E1_9 : getr R1 9 = Z_to_bv 64 0x33d10) by (sa_reg X1; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 0x33d10) by (sa_reg X1; reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 1) by (sa_reg X1; reflexivity).
    assert (E1_19 : getr R1 19 = getr regs 13) by (sa_reg X1; reflexivity).
    assert (E1_20 : getr R1 20 = getr regs 12) by (sa_reg X1; reflexivity).
    assert (E1_21 : getr R1 21 = Z_to_bv 64 pu) by (sa_reg X1; exact AU).
    assert (SP1 : spZ R1 = bv_unsigned sp - 96) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    pose proof (sinv_stack B API SEGS GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                  ltac:(intros a Ra Hm; cbn [outside] in Hm; unfold SUP_ADD_K; lia)) as SI1.
    apply (sinv_rcf B API SEGS ERRNO_LOW GOTG GRD GOWN AX RCF SUP_ADD_K (bv_unsigned sp) L A mem md O L A m1 md R O b
             R1 _ SI1 H16 E1_10 E1_11).
    + rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP1. replace (bv_unsigned sp - 96) with (bv_unsigned sp + (-6) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    + rewrite SP1. unfold SUP_ADD_K, RCF_K, ALLOC_STACK. lia.
    + rewrite SP1. lia.
    + rewrite E1_4. exact HTP.
    + intros L' A' regs' m' md' RP' POST FRK.
      rewrite E1_1.
      pose proof POST as (RJ' & _ & _ & _ & _ & RA' & _ & _ & BLE & _).
      destruct (mr_model B _ LAWS L' A' m' md' (proj1 RJ')) as (Hh' & Hl' & _).
      assert (Q9 : reg_get regs' 9 = Z_to_bv 64 0x33d10)
        by exact (eq_trans (RP' 9 ltac:(unfold callee_saved; lia)) E1_9).
      assert (Q21 : reg_get regs' 21 = Z_to_bv 64 pu)
        by exact (eq_trans (RP' 21 ltac:(unfold callee_saved; lia)) E1_21).
      assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 56)
        [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
         C8 (getr regs 8); C8 (getr regs 1)]).
      { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
        apply FRK. rewrite SP1. lia. }
      destruct (glob_rw_cells m' 0x33d10 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
      eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q9, Q21.
        eapply sa_seg_jrec; [exact EW | exact PU]. }
      intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md'
                  m2 _ REC_ADD POST ltac:(unfold REC_FN_COUNT, REC_ADD; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn [outside] in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 56)
        [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
         C8 (getr regs 8); C8 (getr regs 1)]).
      { apply (rw_cells_transport rsegs _ m' m2 _ _ FR' MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
        repeat split; lia. }
      pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
      apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
      rewrite sb_shift_refl in BLE.
      apply (sa_body1 L A regs mem md pu pp pc uri id pl cl R O b L' A' R2 m2 md' Oc' PRE AU AI HID APL ACL SU SPL SCL
               RA FRM HCODE ROOM SI2 BLE ltac:(lia)).
      * sa_reg X2. reflexivity.
      * sa_reg X2. exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
      * sa_reg X2. exact (eq_trans (RP' 8 ltac:(unfold callee_saved; lia)) E1_8).
      * sa_reg X2. reflexivity.
      * sa_reg X2. reflexivity.
      * sa_reg X2. rewrite (rec_entry_full G_REC REC_SC R H16). reflexivity.
      * sa_reg X2. exact (eq_trans (RP' 19 ltac:(unfold callee_saved; lia)) E1_19).
      * sa_reg X2. exact (eq_trans (RP' 20 ltac:(unfold callee_saved; lia)) E1_20).
      * apply (kept_ex_trans _ regs regs' R2); [|kept_ex_tac X2].
        apply (kept_ex_trans _ regs R1 regs'); [kept_ex_tac X1 | apply kept_ex_of_pres; exact RP'].
      * exact FR2.
      * rewrite (rec_entry_full G_REC REC_SC R H16).
        replace (REC_SC + 4) with (0x33d10 + Z.of_nat 4) by (unfold REC_SC; lia).
        exact EA.
Qed.

End P.
