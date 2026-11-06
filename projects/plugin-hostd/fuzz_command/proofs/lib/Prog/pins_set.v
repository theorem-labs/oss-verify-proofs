(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its addresses and numbers changed; 1534 of its 1682 lines of code are new or changed and 400 lines of the source are left out. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecCore.
Import ListNotations.
Open Scope Z_scope.

Definition psel (p d : Z) : Z := if p =? 0 then d else p.

Ltac ps_lits :=
  fold_lit_ux;
  repeat match goal with
  | |- context [Z.shiftl ?a ?b] => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  end;
  rewrite ?Z.add_0_r.

Lemma ps_nz_true : forall p, 0 <= p < 2 ^ 64 -> p <> 0 -> negb (bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0)) = true.
Proof.
  intros p Hp N. unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia.
Qed.

Lemma ps_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) a3
                     b0 b1 b2 a3 a4 a5 a6 a7 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a2 a1 a0
                     s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16e88) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 64)
       /\ rw_cells rsegs m' (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16e14) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 56%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 56%nat junk [] [8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  carve_frame 8%nat ST.
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

Lemma ps_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16e64) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) a3
                     (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) (Z_to_bv 64 16) a3 a4 a5 a6 a7 s2 a2 a1 a0
                     s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 64)
       /\ rw_cells rsegs m' (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16e14) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 56%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 56%nat junk [] [8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  carve_frame 8%nat ST.
  clear FR0.
  do 17 step.
  rewrite rc_sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma ps_seg_rec :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e pu : Z) (junk : list byte),
  rw_cells rsegs m e [CB 8 junk] -> 0 <= pu < 2 ^ 64 ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16ea4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (psel pu 0x10a19)) a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 e) s3 s4 (Z_to_bv 64 (psel pu 0x10a19)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 20); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) s3 s4 (Z_to_bv 64 pu)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16e88) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e pu junk EW Hpu.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rc_cells_rebytes _ _ _ [C4 (Z_to_bv 64 20); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  step.
  unfold psel. destruct (Z.eqb_spec pu 0) as [E0|E0].
  - subst pu. if_false. do 4 step.
    apply evt_done. eexists. split; [reflexivity|]. split; [eassumption|]. split; eassumption.
  - rewrite (ps_nz_true pu Hpu E0). cbv iota. do 2 step.
    apply evt_done. eexists. split; [reflexivity|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma ps_seg_jrec :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (pu : Z) (junk : list byte),
  rw_cells rsegs m 0x33d10 [CB 8 junk] -> 0 <= pu < 2 ^ 64 ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16ea4) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 (Z_to_bv 64 (psel pu 0x10a19))
                     a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x33d10) s3 s4 (Z_to_bv 64 (psel pu 0x10a19))
                     s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 20); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 pu)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16e64) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pu junk EW Hpu.
  do 2 step. eapply ps_seg_rec; [exact EW | exact Hpu].
Qed.

Lemma ps_seg_a0 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e p pf : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 0)] -> rw_cells rsegs m (e + 8) [CB 8 junk] ->
  0 <= p < 2 ^ 64 -> 0 <= pf < 2 ^ 64 ->
  evt rsegs (fun ms' => exists b1 b2 b3 b4 m',
       ms' = MS (mkR (Z_to_bv 64 0x16edc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (psel pf 0x10a19)) b1 b2 b3 b4 a5 a6 a7
                     (Z_to_bv 64 e) s3 (Z_to_bv 64 (psel pf 0x10a19)) (Z_to_bv 64 (e + 8))
                     s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 16)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 1)]
       /\ rw_cells rsegs m' (e + 8) [C8 (Z_to_bv 64 p)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) s3 (Z_to_bv 64 pf) s5
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16ea4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e p pf junk EN EA Hp Hpf.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. try (rewrite rc_sx32_lit by lia).
  do 5 step. ps_lits.
  do 3 step. if_false.
  step.
  unfold psel. destruct (Z.eqb_spec pf 0) as [E0|E0].
  - subst pf. if_false. do 4 step.
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - rewrite (ps_nz_true pf Hpf E0). cbv iota. do 2 step.
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma ps_seg_a1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e p pl : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 1)] -> rw_cells rsegs m (e + 16) [CB 8 junk] ->
  0 <= p < 2 ^ 64 -> 0 <= pl < 2 ^ 64 ->
  evt rsegs (fun ms' => exists b1 b2 b3 b4 m',
       ms' = MS (mkR (Z_to_bv 64 0x16f10) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (psel pl 0x10a19)) b1 b2 b3 b4 a5 a6 a7
                     (Z_to_bv 64 e) (Z_to_bv 64 (psel pl 0x10a19)) s4 (Z_to_bv 64 (e + 8))
                     s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 16, e + 24)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 2)]
       /\ rw_cells rsegs m' (e + 16) [C8 (Z_to_bv 64 p)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) (Z_to_bv 64 pl) s4
             (Z_to_bv 64 (e + 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16edc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e p pl junk EN EA Hp Hpl.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 16, e + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite rc_sx32_lit by lia.
  do 4 step. ps_lits.
  do 3 step. if_false.
  step.
  unfold psel. destruct (Z.eqb_spec pl 0) as [E0|E0].
  - subst pl. if_false. do 4 step.
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - rewrite (ps_nz_true pl Hpl E0). cbv iota. do 2 step.
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma ps_seg_a2 :
  forall ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e p pv : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 2)] -> rw_cells rsegs m (e + 24) [CB 8 junk] ->
  0 <= p < 2 ^ 64 -> 0 <= pv < 2 ^ 64 ->
  evt rsegs (fun ms' => exists b1 b2 b3 b4 m',
       ms' = MS (mkR (Z_to_bv 64 0x16f44) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (psel pv 0x108b0))
                     (Z_to_bv 64 (psel pv 0x108b0)) b1 b2 b3 b4 a5 a6 a7
                     (Z_to_bv 64 e) s3 s4 (Z_to_bv 64 (e + 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 24, e + 32)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 3)]
       /\ rw_cells rsegs m' (e + 24) [C8 (Z_to_bv 64 p)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pv) (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) s3 s4
             (Z_to_bv 64 (e + 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f10) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e p pv junk EN EA Hp Hpv.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 24, e + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite rc_sx32_lit by lia.
  do 4 step. ps_lits.
  do 3 step. if_false.
  step.
  unfold psel. destruct (Z.eqb_spec pv 0) as [E0|E0].
  - subst pv. if_false. do 4 step.
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - rewrite (ps_nz_true pv Hpv E0). cbv iota. do 2 step.
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma ps_seg_a3 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e p : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 3)] -> rw_cells rsegs m (e + 32) [CB 8 junk] ->
  0 <= p < 2 ^ 64 ->
  evt rsegs (fun ms' => exists b1 b2 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) b1 b2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 e) s3 s4 (Z_to_bv 64 (e + 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16f5c) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 32, e + 40)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 4)]
       /\ rw_cells rsegs m' (e + 32) [C8 (Z_to_bv 64 p)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) s3 s4
             (Z_to_bv 64 (e + 8)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f44) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e p junk EN EA Hp.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 32, e + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite rc_sx32_lit by lia.
  do 3 step. ps_lits.
  do 2 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma ps_seg_epi :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 s05 : word),
  rw_cells rsegs m (bv_unsigned sp0 + -56) [C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  64 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                     s02 s03 s04 s05 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16fa8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f84) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 s05 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 9 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -64 + 64)) with sp0
    by (replace (bv_unsigned sp0 + -64 + 64) with (bv_unsigned sp0) by ring; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma ps_rf_nz : forall rf, -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 -> bv_eqb (Z_to_bv 64 rf) (Z_to_bv 64 0) = false.
Proof.
  intros rf Hr N. unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616. rewrite Zmod_0_l. intros H.
  apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. lia.
Qed.

Lemma ps_seg_ref :
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 s05 : word) (rf cd : Z),
  rw_cells rsegs m (bv_unsigned sp0 + -56) [C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  64 <= bv_unsigned sp0 ->
  rw_cells rsegs m 0x33d48 [C4 (Z_to_bv 64 rf)] -> rw_cells rsegs m 0x33d4c [C4 (Z_to_bv 64 cd)] ->
  -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 -> -2 ^ 31 <= cd < 2 ^ 31 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 (Z_to_bv 64 cd) a1 a2 a3 a4 a5 a6 a7
                     s02 s03 s04 s05 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16fa8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -64)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f5c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 s05 rf cd FR SPR RC RC2 Hrf Nrf Hcd.
  do 2 step. rewrite rc_sx32_lit by lia. rewrite (ps_rf_nz rf Hrf Nrf). cbv iota.
  do 2 step. rewrite rc_sx32_lit by lia.
  eapply ps_seg_epi; [exact FR | exact SPR].
Qed.

Lemma ps_seg_mix :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (cd : Z) (st : word),
  rw_cells rsegs m 0x33d48 [C4 (Z_to_bv 64 0)] -> -2 ^ 31 <= cd < 2 ^ 31 ->
  rw_cells rsegs m 0x340f8 [C8 st] ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16f78) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 st
                     (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15ccc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e)
             s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f5c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e cd st RC Hcd ES.
  do 2 step. try (rewrite rc_sx32_lit by lia). if_true.
  do 3 step.
  apply evt_done. reflexivity.
Qed.

Lemma ps_seg_mret :
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 s05 : word) (st : word),
  rw_cells rsegs m (bv_unsigned sp0 + -56) [C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  0x34140 <= bv_unsigned sp0 ->
  rw_cells rsegs m 0x340f8 [C8 st] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 (Z_to_bv 64 0) a0 a2 a3 a4 a5 a6 a7
                     s02 s03 s04 s05 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16fa8) fc None m' (seg_rom rsegs)
       /\ munch [(0x340f8, 0x34100)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x340f8 [C8 a0])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -64)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f78) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 s05 st FR SPR ES.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(0x340f8, 0x34100)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step.
  eapply evt_cut; [eapply ps_seg_epi; [eassumption | lia] |].
  intros ms' ->. apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecTail RecStub.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import rec_calls_free_c xstrdup_c mix_call_c
answer_code_c pins_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require hand_back RecAnsB.

Lemma ps_bytes_some : forall segs m a bs (i : nat), bytes_at segs m a bs -> (i < length bs)%nat ->
  mbyte segs m (a + Z.of_nat i) <> None.
Proof.
  intros segs m a bs i (_ & _ & H) Hi. specialize (H i Hi).
  change (mrd segs m (wa (a + Z.of_nat i))) with (mbyte segs m (a + Z.of_nat i)) in H.
  rewrite H. apply nth_error_Some. exact Hi.
Qed.

Lemma ps_bytes_someZ : forall segs m a bs x, bytes_at segs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  mbyte segs m x <> None.
Proof.
  intros segs m a bs x H Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
  apply (ps_bytes_some segs m a bs); [exact H | lia].
Qed.

Lemma ps_pad_le : forall e c a, e <= c -> a < e + (- e) mod 8 -> a < 8 * ((c + 7) / 8).
Proof.
  intros e c a H1 H2.
  pose proof (Z.div_mod (- e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (- e) 8 ltac:(lia)).
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)).
  lia.
Qed.

Lemma ps_present : forall segs m a, present m a -> mbyte segs m a <> None.
Proof. intros segs m a [b E]. unfold mbyte. rewrite E. discriminate. Qed.

Lemma ps_combine_snd : forall (X Y : Type) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H |- *;
    [reflexivity | discriminate | discriminate | rewrite (IH l2 ltac:(lia)); reflexivity].
Qed.

Lemma ps_nth_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y) k a b,
  nth_error (combine l1 l2) k = Some (a, b) -> nth_error l1 k = Some a /\ nth_error l2 k = Some b.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] [|k] a b H; cbn in H |- *; try discriminate.
  - injection H as -> ->. split; reflexivity.
  - exact (IH l2 k a b H).
Qed.

Lemma ps_run_mix : mix_call_contract ->
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e h cd : Z) (args : list (word * list byte))
    (sp1 ra0 s00 s01 s02 s03 s04 s05 : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 80 <= bv_unsigned sp1 -> 0x34100 <= lo ->
  rw_cells rsegs m (bv_unsigned sp1 + 8) [C8 s05; C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  rw_cells rsegs m 0x33d48 [C4 (Z_to_bv 64 0)] -> -2 ^ 31 <= cd < 2 ^ 31 ->
  bytes_at rsegs m e (le4 (Z_to_bv 64 20) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) ->
  0x33d10 <= e -> e + 56 <= 0x340f8 -> (length args <= 6)%nat ->
  (forall k p, nth_error args k = Some p -> mc_arg m (bv_unsigned sp1 - 80) (bv_unsigned sp1) e k p) ->
  rw_cells rsegs m 0x340f8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  evt rsegs (fun ms' => exists t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp1 + 64)) gp tp t0' t1' t2' s00 s01 (Z_to_bv 64 0)
                     b1 b2 b3 b4 b5 b6 b7 s02 s03 s04 s05 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16fa8) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 80, bv_unsigned sp1); (0x340f8, 0x34100)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x340f8 [C8 (Z_to_bv 64 (mixcall h 20 (map snd args)))])
    (MS (mkR ra sp1 gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 e) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f5c) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e h cd args sp1 ra0 s00 s01 s02 s03 s04 s05 MI ST LO LO2 FR RC Hcd EF E0 E1 LA HARG ES Hh.
  assert (MIX' := MIX). unfold mix_call_contract, MIX_CALL_FRAME in MIX'.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned sp1 - 80, bv_unsigned sp1); (0x340f8, 0x34100)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step. try (rewrite rc_sx32_lit by lia). if_true.
  do 3 step.
  call (MIX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 20 args).
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
    do 12 step.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.


Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis GERR : forall a, in_globals frame_G a -> ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis XSTRDUP : xstrdup_contract B API.
Hypothesis MIX : mix_call_contract.
Hypothesis ANSC : answer_code_contract B API.

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
  intros L A m sp s y N0 LX BS PR HB DJ HOME. unfold xsrc.
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
  ro_agree rsegs mem -> ro_agree rsegs mc -> 64 + XSTRDUP_K <= K ->
  str_arg B L A O S K mem p v ->
  xsrc Lc Ac mc (S - 64) lit d ->
  0 <= p < 2 ^ 64 /\ xsrc Lc Ac mc (S - 64) (psel p lit) (match v with Some x => x | None => d end).
Proof using SEGS ERRNO_LOW SLACK.
  intros K S L A mem md O Lc Ac mc mdc p v lit d R RA RAc HK SA XL.
  destruct v as [x|].
  2: { cbn in SA. subst p. split; [lia|]. replace (psel 0 lit) with lit by reflexivity. exact XL. }
  destruct SA as (NZ & N0 & LX & slack & BS & PAD & DJ & HOME & NRA).
  rewrite SEGS in BS.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  split; [lia|].
  unfold psel. rewrite (proj2 (Z.eqb_neq p 0) NZ).
  pose proof R as (HM1 & HWA & HW1 & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  rewrite SEGS in HF, HKP.
  pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length x) + 1)) 8 ltac:(lia)) as Hpad.
  assert (BS0 : bytes_at rsegs mem p (x ++ [Z_to_bv 8 0])).
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) in BS by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  assert (MSOME : forall a, p <= a < p + Z.of_nat (length x) + 1 + (- (p + Z.of_nat (length x) + 1)) mod 8 ->
            mbyte rsegs mem a <> None).
  { intros a Ha. apply (ps_bytes_someZ rsegs mem p (x ++ Z_to_bv 8 0 :: slack)); [exact BS|].
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
               str_home B Lc Ac (S - 64) p (Z.of_nat (length x) + 1)).
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
        * apply ps_present. apply (SLACK Lc Ac mc mdc q k a HM1 Hb1). split; [exact Hl|].
          apply (ps_pad_le (p + Z.of_nat (length x) + 1) (q + k) a); lia.
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
          pose proof (ps_pad_le (p + Z.of_nat (length x) + 1) 139264 a ltac:(lia) ltac:(lia)) as X.
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

Lemma ps_glob : forall a, 0x33d10 <= a < 0x34108 -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N.
Proof. intros a H. unfold GLOB_LO. change (Z.of_nat GLOB_N) with 1020. lia. Qed.

Lemma ps_apart : forall q n lo len, (forall i, 0 <= i < n -> ~ in_img B (q + i)) -> 0 < n ->
  0x33d10 <= lo -> lo + len <= 0x34108 -> 0 < len -> iv_apart q n lo len.
Proof using SEGS.
  intros q n lo len H Hn H1 H2 H3. unfold iv_apart.
  destruct (Z_le_gt_dec (q + n) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec (lo + len) q) as [D'|D']; [right; exact D'|]. exfalso.
  apply (H (Z.max q lo - q)); [lia|]. replace (q + (Z.max q lo - q)) with (Z.max q lo) by lia.
  apply (glob_in_img B SEGS). apply ps_glob. lia.
Qed.

Lemma ps_entry_bounds : forall R, 0x33d10 <= rec_entry G_REC REC_SC R /\ rec_entry G_REC REC_SC R + 56 <= 0x340f8.
Proof.
  intros R. unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
  - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE. lia.
  - unfold REC_SC. lia.
Qed.

Lemma arg_post : forall S L A mem md O Lc Ac mc mdc R As Oc b regs_c L2 A2 regs2 m2 md2 p y m3 W,
  sinv B API PINS_SET_K S L A mem md O Lc Ac mc mdc (rec_record R REC_PINS_SET As) Oc b ->
  (length As < 6)%nat ->
  S - PINS_SET_K <= spZ regs_c - XSTRDUP_K -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) XSTRDUP_K Lc Ac regs_c mc mdc (fun a => p <= a < p + Z.of_nat (length y) + 1)
    L2 A2 regs2 m2 md2 ->
  p <> 0 -> fresh_block B p (Z.of_nat (length y) + 1) ->
  (exists b1 b2, blocks L2 A2 = b1 ++ (p, Z.of_nat (length y) + 1) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  blocks_kept B Lc Ac mc m2 (fun _ => False) ->
  (forall q k, In (q, k) (user_blocks Ac) -> In (q, k) (user_blocks A2)) ->
  bytes_at rsegs m2 p (y ++ [Z_to_bv 8 0]) -> ro_agree rsegs m2 -> guard_kept B mc m2 ->
  st_init_done A2 = true -> (length (st_regions Ac) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_malloc (sb_shift b A Ac) (Z.of_nat (length y) + 1)) ->
  no0 y -> Z.of_nat (length y) <= LMAX ->
  munch W m2 m3 -> wmono rsegs m2 m3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     (rec_entry G_REC REC_SC R + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC R + CALL_OFF_NARGS + 4) \/
     (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
      rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8)) ->
  bytes_at rsegs m3 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at rsegs m3 (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  sinv B API PINS_SET_K S L A mem md O L2 A2 m3 md2 (rec_record R REC_PINS_SET (As ++ [y]))
    (Oc ++ [(p, Z.of_nat (length y) + 1)]) b /\
  sb_shift b A A2 = sb_malloc (sb_shift b A Ac) (Z.of_nat (length y) + 1).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN GERR AX.
  intros S L A mem md O Lc Ac mc mdc R As Oc b regs_c L2 A2 regs2 m2 md2 p y m3 W
    SI H6 LO HI POST PNZ FRESH (l1 & l2 & BL2 & BL1) BKP UB PB RA2 GK INIT RGN RES2 N0 LX MU WM HW NA AR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _).
  destruct (rjr_bounds B _ PINS_SET_K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof POST as (PM & PW & PB' & PL & PA & PR & PV & PF & PK & PS).
  rewrite SEGS in PF. unfold blocks_kept in BKP. rewrite SEGS in BKP.
  destruct FRESH as (FP1 & FP2 & FP3).
  pose proof (ps_entry_bounds R) as (EB1 & EB2).
  assert (H6Z : Z.of_nat (length As) < 6) by lia.
  assert (KREC : forall a, 0x33d10 <= a < 0x34108 -> mbyte rsegs m2 a = mbyte rsegs mc a).
  { intros a Ha. assert (GA : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N) by (apply ps_glob; exact Ha).
    apply PF.
    - right. exact (glob_in_img B SEGS a GA).
    - exact (GOWN _ _ _ _ a HM (glob_in a GA)).
    - exact (GOWN _ _ _ _ a PM (glob_in a GA)).
    - intros [Hs|He]; [lia | exact (GERR a (glob_in a GA) He)].
    - intros Hp. apply (FP3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact (glob_in_img B SEGS a GA). }
  assert (DJ : forall a k, In (a, k) (blocks Lc Ac) -> 0 < k -> a <> p).
  { intros a k Hin Hk Ea. subst a.
    pose proof (mr_blocks_disjoint B _ LAWS L2 A2 m2 md2 PM) as PD. rewrite BL2 in PD. rewrite BL1 in Hin.
    destruct (YI04.pairwise_app_mid _ _ _ _ _ PD Hin) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  assert (RJ2 : rjr B (aa_MR API) PINS_SET_K S rec_area (fun pn => In pn O) L A mem md L2 A2 m2 md2).
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW PINS_SET_K S rec_area _ L A mem md Lc Ac mc mdc XSTRDUP_K regs_c
             _ (fun _ => False) L2 A2 regs2 m2 md2 RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST)).
    - exact LO.
    - exact HI.
    - intros a Ha Hf. cbv beta in Ha. exfalso. destruct Hf as [Hf|(Hf & _)]; [lia|].
      apply (FP3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Hf.
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ H1 H2. exfalso. exact (H2 (UB p0 n0 H1)).
    - exact RGN.
    - intros Hf. rewrite INIT in Hf. discriminate. }
  assert (HW' : forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - PINS_SET_K <= a < S \/ rec_area a).
  { intros a Ra Hm. right. destruct (HW a Ra Hm) as [H|H];
      unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
  pose proof (rjr_blk_out B API SEGS AX PINS_SET_K S O L A mem md L2 A2 m2 md2 W RJ2 HW') as BO.
  assert (OUTR : forall a, 0x33d10 <= a < 0x34108 ->
            ~ (rec_entry G_REC REC_SC R + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC R + CALL_OFF_NARGS + 4) ->
            ~ (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
               rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
            mbyte rsegs m3 a = mbyte rsegs m2 a).
  { intros a Ha N1 N2. apply (munch_mbyte rsegs W m2 m3 a MU); [lia|].
    destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso.
    destruct (HW a ltac:(lia) H) as [H'|H']; contradiction. }
  assert (INB : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L2 A2)).
  { intros pn Hb. rewrite BL2. rewrite BL1 in Hb.
    apply in_app_or in Hb as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
  assert (INP : In (p, Z.of_nat (length y) + 1) (blocks L2 A2)) by (rewrite BL2; apply in_or_app; right; left; reflexivity).
  assert (GR3 : g_rec_rep rsegs L2 A2 m3 (rec_record R REC_PINS_SET (As ++ [y])) (Oc ++ [(p, Z.of_nat (length y) + 1)])).
  { unfold g_rec_rep in *.
    apply (rec_rep_arg rsegs G_REC REC_SC Lc Ac mc L2 A2 m3 R REC_PINS_SET As Oc y p (Z.of_nat (length y) + 1) GR H6).
    - exact NA.
    - exact AR.
    - intros a Ha N1 N2. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha.
      rewrite (OUTR a ltac:(lia) N1 N2). apply KREC. lia.
    - intros a Ha _. apply glob_writable. apply ps_glob. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha. lia.
    - intros [a k] Hpn. cbn [fst snd].
      pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ (a, k) GR Hpn) as Hb.
      split; [exact (INB _ Hb)|].
      intros i Hi. destruct (BO a k i (INB _ Hb) Hi) as [Rr Oo].
      rewrite (munch_mbyte rsegs W m2 m3 _ MU Rr Oo). exact (BKP a k i Hb (fun f => f) Hi).
    - intros Hin. apply in_map_iff in Hin as ([a k] & Ea & Hin). cbn [fst] in Ea.
      exact (DJ a k (rec_rep_O_in _ _ _ _ _ _ _ _ (a, k) GR Hin) (rec_rep_pos _ _ _ _ _ _ _ _ (a, k) GR Hin) Ea).
    - exact PNZ.
    - exact INP.
    - exact N0.
    - exact LX.
    - lia.
    - apply (bytes_at_keep_in rsegs m2 m3 p (p + Z.of_nat (length y) + 1));
        [exact PB | lia | rewrite length_app; cbn [length]; lia |].
      intros a Ha. destruct (BO p (Z.of_nat (length y) + 1) (a - p) INP ltac:(lia)) as [Rr Oo].
      replace a with (p + (a - p)) by ring. exact (munch_mbyte rsegs W m2 m3 _ MU Rr Oo).
    - apply ps_apart; [exact FP3 | lia | unfold G_REC; lia | unfold G_REC, REC_SIZE; lia | unfold REC_SIZE; lia].
    - apply ps_apart; [exact FP3 | lia | unfold REC_SC; lia | unfold REC_SC, SC_SIZE; lia | unfold SC_SIZE; lia]. }
  assert (ON2 : owns_new L A O (Oc ++ [(p, Z.of_nat (length y) + 1)])).
  { intros pn Hpn. apply in_app_or in Hpn as [H|[H|[]]]; [exact (ON pn H)|]. subst pn.
    destruct (in_dec pair_dec (p, Z.of_nat (length y) + 1) O) as [H|H]; [left; exact H|].
    right. intros Hb.
    destruct (in_dec pair_dec (p, Z.of_nat (length y) + 1) (blocks Lc Ac)) as [H2|H2].
    - exact (DJ _ _ H2 ltac:(lia) eq_refl).
    - exact (H (B2 _ Hb H2)). }
  assert (B12 : forall pn, In pn (blocks L2 A2) ->
            (In pn (blocks L A) /\ ~ In pn O) \/ In pn (Oc ++ [(p, Z.of_nat (length y) + 1)])).
  { intros pn Hpn. rewrite BL2 in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite BL1; apply in_or_app; left; exact H)) as [X|X];
        [left; exact X | right; apply in_or_app; left; exact X].
    - right. apply in_or_app. right. left. exact H.
    - destruct (B1 pn ltac:(rewrite BL1; apply in_or_app; right; exact H)) as [X|X];
        [left; exact X | right; apply in_or_app; left; exact X]. }
  assert (B22 : forall pn, In pn (blocks L A) -> ~ In pn (blocks L2 A2) -> In pn O).
  { intros pn H1 H2. apply B2; [exact H1|]. intros H3. exact (H2 (INB _ H3)). }
  assert (EQB : sb_shift b A A2 = sb_malloc (sb_shift b A Ac) (Z.of_nat (length y) + 1)).
  { rewrite (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2 l1 l2 p _ BL2 BL1). symmetry. apply sb_shift_trans. }
  assert (F182 : f18_words rsegs m2).
  { destruct (ax_statics AX L2 A2 m2 md2 PM) as (_ & (g & Hg & HGW) & _).
    rewrite GRD, SEGS in HGW.
    apply (RecAnsB.f18_words_after mc m2 g F18); [| exact Hg | exact HGW].
    intros i Hi. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  split; [|exact EQB].
  split; [exact (rjr_win B API SEGS GOWN AX PINS_SET_K S O L A mem md L2 A2 m2 md2 m3 W RJ2 MU WM HW')|].
  split; [exact GR3|]. split; [exact ON2|]. split; [exact B12|]. split; [exact B22|].
  split.
  { apply (ro_out W m2 m3 RA2 MU). intros a Ha Hro.
    destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso.
    destruct (HW a ltac:(lia) H) as [H'|H'];
      (pose proof (glob_ro_false a ltac:(apply ps_glob; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in H'; lia)) as G;
       unfold wa in G; rewrite G in Hro; discriminate). }
  split.
  { apply (f18_out W m2 m3 F182 MU). intros i Hi.
    split; (match goal with |- outside W ?x =>
      destruct (outside_dec W x) as [H|H]; [exact H|]; exfalso;
      destruct (HW x ltac:(unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD; lia) H) as [H'|H'];
      unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia end). }
  rewrite EQB. exact RES2.
Qed.

Definition ct_ret (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (O : list (Z * Z)) (R1 : rstate) (code : Z) (b bpre : sbound) (c' : config) : Prop :=
  let n := Z.of_nat (length (resp code)) + 1 in
  exists (fx' : YK11.FPState) L' A' regs' mem' md' O',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    fp_kept fx fx' /\
    call_post_rec B (aa_MR API) K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 (snd (rec_answer_code R1 code)) /\
    g_rec_rep (ms_segs B) L' A' mem' (fst (rec_answer_code R1 code)) O' /\ owns_new L A O O' /\
    others_kept (ms_segs B) L A mem L' A' mem' O /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    ro_agree (ms_segs B) mem' /\ f18_words (ms_segs B) mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_malloc (sb_malloc bpre n) n) /\
    res_ok_slots A' (sb_shift b A A').

Lemma code_tail : forall K L A regs mem md O Lc Ac regs1 mc mdc Rc Oc bc bpre code,
  call_pre_t B API K L A regs mem md -> ANSWER_CODE_K <= K ->
  sinv B API K (spZ regs) L A mem md O Lc Ac mc mdc Rc Oc bc ->
  getr regs1 1 = getr regs 1 -> spZ regs1 = spZ regs -> regs_preserved regs regs1 ->
  getr regs1 10 = Z_to_bv 64 code -> -2^31 <= code < 2^31 ->
  frm_zero fp_csr -> sb_le (sb_shift bc A Ac) bpre ->
  room_slots (sb_malloc (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (resp code)) + 1))
                (Z.of_nat (length (resp code)) + 1)) (Z.of_nat (length (resp code)) + 1) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 ANSWER_CODE) mc (seg_rom rsegs)) mdc)
    (ct_ret K L A regs mem md O Rc code bc bpre).
Proof using SEGS AX CTX ERRNO_LOW ANSC.
  intros K L A regs mem md O Lc Ac regs1 mc mdc Rc Oc bc bpre code PRE KA SI RA1 SP1 RP1 A10 HC FRM BLE ROOM.
  destruct SI as (R & GREP1 & P1 & P2 & P5 & RO1 & F18 & RES1).
  rewrite <- SEGS in GREP1, RO1, F18 |- *.
  pose proof (aa_laws API) as LAWS.
  pose proof R as R0.
  destruct R0 as (HM1 & HWA & HW1 & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  pose proof PRE as ((HM & _ & _ & HRA & HAL & _ & _ & _ & HTP & _) & HTS).
  assert (PRE1 : call_pre_t B API ANSWER_CODE_K Lc Ac regs1 mc mdc).
  { split; [|rewrite SP1; exact HTS].
    apply (call_pre_k_of_rjr B (aa_MR API) K (spZ regs) rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc
             ANSWER_CODE_K regs1 R).
    - rewrite RA1. exact HRA.
    - rewrite SP1. exact HAL.
    - apply Z.leb_le. vm_compute. reflexivity.
    - rewrite SP1. lia.
    - rewrite SP1. lia.
    - exact (eq_trans (RP1 4 ltac:(unfold callee_saved; lia)) HTP). }
  eapply SR_mono.
  { exact (ANSC Lc Ac regs1 mc mdc Rc Oc code (sb_shift bc A Ac) PRE1 A10 HC GREP1 FRM F18 RES1 ROOM RO1). }
  intros c' RET. unfold answer_code_ret in RET.
  destruct RET as (fx' & L' & A' & regs' & mem' & md' & p1 & old & O' & EC & FPK & OLDB & POST & A0 & PAL & FR1
    & (c1 & c2 & HB & HIFF & NI1) & BK & UBK & GREP' & HO' & HBC & BY & RA' & F18' & GK & INIT & REG & GR' & RES').
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  set (n := Z.of_nat (length (resp code)) + 1) in *.
  assert (HB' : exists kold, (old = 0 /\ blocks Lc Ac = c1 ++ c2) \/
                             (old <> 0 /\ In (old, kold) Oc /\ blocks Lc Ac = c1 ++ (old, kold) :: c2)).
  { destruct HB as [H|(k & H)]; [exists 0; left; exact H | exists k; right; exact H]. }
  destruct HB' as [kold HB'].
  assert (STAB : forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
            In (p, k) (user_blocks Ac) /\ ptr_addr Lc p = ptr_addr L p).
  { intros p k Hu Hno.
    split; [exact (rjr_in_cur B (aa_MR API) K (spZ regs) rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc p k R Hu Hno)|].
    exact (ptr_addr_stable A L Lc p k HWA Hu HL). }
  assert (R2 : rjr B (aa_MR API) K (spZ regs) rec_area (fun pn => In pn O) L A mem md L' A' mem' md').
  { apply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW K (spZ regs) rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc
             ANSWER_CODE_K regs1 ac_writes (fun a => a = old) L' A' regs' mem' md' R POST).
    - rewrite SP1. lia.
    - rewrite SP1. lia.
    - intros a Ha _. pose proof alloc_ceiling_val as AC.
      unfold ac_writes, rec_area, G_REC, REC_SC, OFF_ANSWER, SC_SIZE, REC_SIZE in *.
      split; [lia|]. lia.
    - intros p k Hu Hno Hk E.
      destruct (STAB p k Hu Hno) as [Hu1 Ep].
      pose proof (mr_blocks_range B (aa_MR API) LAWS L A mem md p k HM Hu) as Hr.
      destruct HB' as [(E0 & _)|(NZ & Ho & EB)]; [lia|].
      assert (Hob : In (old, kold) (blocks Lc Ac)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
      pose proof (user_in_blocks Lc Ac p k Hu1) as Hb. rewrite Ep, E in Hb.
      pose proof (rec_rep_pos (ms_segs B) G_REC REC_SC Lc Ac mc Rc Oc (old, kold) GREP1 Ho) as Hk0. cbn [snd] in Hk0.
      assert (Ek : k = kold) by exact (blocks_same_addr B (aa_MR API) LAWS Lc Ac mc mdc old k kold HM1 Hb Hob Hk Hk0).
      subst k. rewrite E in Hno.
      destruct (P1 _ Ho) as [H|H]; [exact (Hno H)|]. apply H. rewrite <- E. exact (user_in_blocks L A p kold Hu).
    - intros p k Hu Hu1 Hu'.
      destruct (in_dec pair_dec (ptr_addr L p, k) O) as [H|H]; [exact H|]. exfalso. apply Hu'. apply UBK; [exact Hu1|].
      rewrite (ptr_addr_stable A L Lc p k HWA Hu HL). intros Ho.
      destruct (P1 _ Ho) as [H'|H']; [exact (H H') | exact (H' (user_in_blocks L A p k Hu))].
    - exact REG.
    - rewrite INIT. discriminate. }
  assert (RP : regs_preserved regs regs').
  { intros r Hr. rewrite (PR r Hr). exact (RP1 r Hr). }
  pose proof (rjr_final B (aa_MR API) CTX K rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
                L' A' regs' mem' md' (proj1 PRE) R2 RP ltac:(intros a k G; exact (in_map fst O (a, k) G))) as FIN.
  pose proof (rjr_others_kept B (aa_MR API) K (spZ regs) rec_area (fun pn => In pn O) L A mem md L' A' mem' md' O R2
                (fun pn H => H)) as OK.
  destruct (tail_owns_blocks (blocks L A) (blocks Lc Ac) (blocks L' A') O Oc O' c1 c2 old kold p1 p1 n
              P1 P2 P5 HB' NI1 HO'
              ltac:(intros pn H; destruct (HBC pn H) as [X|X]; [left; exact X | right; left; exact X]))
    as [OWN BLK].
  exists fx', L', A', regs', mem', md', O'.
  split; [rewrite EC, RA1; reflexivity|].
  split; [exact FPK|]. split; [exact FIN|]. split; [exact A0|]. split; [exact GREP'|]. split; [exact OWN|].
  split; [exact OK|].
  split.
  { intros pn Hpn. destruct (BLK pn Hpn) as [X|[X|X]]; [left; exact X | right; exact X |].
    right. apply HO'. right. exact X. }
  split; [exact RA'|]. split; [exact F18'|]. split; [exact INIT|]. split; [lia|].
  rewrite <- (sb_shift_trans bc A Ac A').
  split; [|exact RES'].
  eapply sb_le_trans; [exact GR'|].
  eapply sb_le_trans; [apply sb_free_le; lia|].
  apply sb_malloc_mono. apply sb_malloc_mono. exact BLE.
Qed.

Lemma ps_mc_arg : forall Lc Ac mc mdc e k pn s lo hi,
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
  { intros a Ha. pose proof (ps_pad_le (q + Z.of_nat (length s) + 1) (q + n) a ltac:(lia) Ha) as X.
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
      rewrite E1 in Hp. apply ps_present. replace (q + Z.of_nat (length s + 1) + Z.of_nat j)
        with (q + (Z.of_nat (length s + 1) + Z.of_nat j)) by ring. exact Hp.
    + apply ps_present. apply (SLACK Lc Ac mc mdc q n _ HM Hb0). split; [exact Hl|].
      apply (ps_pad_le (q + Z.of_nat (length s) + 1) (q + n)); lia.
  - unfold mc_arg. cbn [fst snd]. rewrite unsigned_lit by lia.
    split; [apply bytes_at_normalize; [exact RA | unfold CALL_OFF_ARGS in BP; exact BP]|].
    split; [exact N0|]. split; [exact LX|].
    exists sl. rewrite <- app_assoc in BS2. cbn [app] in BS2.
    split; [apply bytes_at_normalize; [exact RA | exact BS2]|].
    rewrite LS, Z2Nat.id by lia. split; [lia|]. left.
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
Qed.

Definition tl_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (O : list (Z * Z)) (R : rstate) (As : list (list byte)) (b bpre : sbound) (c' : config) : Prop :=
  exists Rc code, rec_stub_code R REC_PINS_SET As = rec_answer_code Rc code /\
    ct_ret PINS_SET_K L A regs mem md O Rc code b bpre c'.

Lemma ps_tail : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t,
  call_pre_t B API PINS_SET_K L A regs mem md ->
  sinv B API PINS_SET_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_PINS_SET As) Oc b ->
  (length (r_calls R) <= 16)%nat -> length As = 4%nat ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) As ->
  sb_le (sb_shift b A Ac) bpre ->
  room_slots (sb_malloc (sb_malloc bpre (Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_SET As)))) + 1))
                (Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_SET As)))) + 1))
             (Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_SET As)))) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs_t 8 = Z_to_bv 64 0x33d10 ->
  getr regs_t 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  kept_ex [2; 8; 9; 18; 19; 20; 21] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x16f5c) mc (seg_rom rsegs)) mdc) (tl_ret L A regs mem md O R As b bpre).
Proof using SEGS ERRNO_LOW GOWN AX CTX SLACK MIX ANSC.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t PRE SI H16 LA4 LXA BLE ROOM FRM FR T2 T8 T18 KT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold PINS_SET_K in HCEIL, HWS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (ps_entry_bounds R) as (EB1 & EB2).
  set (nr := Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_SET As)))) + 1) in *.
  assert (ROOMb : room_slots (sb_malloc (sb_malloc (sb_shift b A Ac) nr) nr) nr).
  { apply (room_slots_mono _ (sb_malloc (sb_malloc bpre nr) nr) nr nr
             (sb_malloc_mono _ _ nr (sb_malloc_mono _ _ nr BLE))); [unfold nr; lia | exact ROOM]. }
  set (R1 := rec_record R REC_PINS_SET As) in *.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & HC & HA & HP & HX & HW).
  pose proof HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (RC1 : rw_cells rsegs mc 0x33d48 [C4 (Z_to_bv 64 (r_refuse R1))]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x33d48 with (G_REC + OFF_REFUSE) by (unfold G_REC, OFF_REFUSE; lia). exact X1. }
  assert (RC2 : rw_cells rsegs mc 0x33d4c [C4 (Z_to_bv 64 (r_code R1))]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x33d4c with (G_REC + OFF_CODE) by (unfold G_REC, OFF_CODE; lia). exact X2. }
  assert (CK : ANSWER_CODE_K <= PINS_SET_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (Q8 : reg_get regs_t 8 = Z_to_bv 64 0x33d10) by exact T8.
  destruct (Z.eq_dec (r_refuse R1) 0) as [RZ|RNZ].
  2: {
    assert (ESC : rec_stub_code R REC_PINS_SET As = rec_answer_code R1 (r_code R1)).
    { unfold rec_stub_code. cbv zeta. fold R1. rewrite (proj2 (Z.eqb_neq _ _) RNZ). reflexivity. }
    assert (Enr : nr = Z.of_nat (length (resp (r_code R1))) + 1) by (unfold nr; rewrite ESC; reflexivity).
    rewrite Enr in ROOMb.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      assert (Q2 : reg_get regs_t 2 = Z_to_bv 64 (bv_unsigned sp + -64)).
      { replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by ring. exact T2. }
      rewrite Q2, Q8.
      eapply ps_seg_ref; [ | lia | exact RC1 | exact RC2 | exact X6 | exact RNZ | exact X7].
      replace (bv_unsigned sp + -56) with (bv_unsigned sp - 56) by ring. exact FR. }
    intros ms1 (can1 & E1 & EQ1). subst can1.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2r).
    assert (E2_1 : getr R2 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X2r eq_refl); simp_regs; reflexivity).
    assert (E2_2 : getr R2 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X2r eq_refl); simp_regs; reflexivity).
    assert (E2_10 : getr R2 10 = Z_to_bv 64 (r_code R1))
      by (rewrite (getr_of_eqv _ _ 10 X2r eq_refl); simp_regs; reflexivity).
    assert (RP2 : regs_preserved regs R2).
    { apply (kept_ex_pres [2; 8; 9; 18; 19; 20; 21]).
      - apply (kept_ex_trans _ regs regs_t R2 KT). kept_ex_tac X2r.
      - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
          match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X2r eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity]. }
    eapply SR_mono.
    { exact (code_tail PINS_SET_K L A regs mem md O Lc Ac R2 mc mdc R1 Oc b bpre (r_code R1) PRE CK SI E2_1
               ltac:(unfold spZ; rewrite E2_2; reflexivity) RP2 E2_10 X7 FRM BLE ROOMb). }
    intros c' H. exists R1, (r_code R1). split; [exact ESC | exact H]. }
  assert (ESC : rec_stub_code R REC_PINS_SET As = rec_answer_code (rec_mix R1 (REC_PINS_SET, As)) 0).
  { unfold rec_stub_code. cbv zeta. fold R1. rewrite RZ. reflexivity. }
  assert (Enr : nr = Z.of_nat (length (resp 0)) + 1) by (unfold nr; rewrite ESC; reflexivity).
  rewrite Enr in ROOMb.
  destruct (rec_rep_entry _ _ _ _ _ _ _ _ _ _ GR H16) as (P & CA).
  destruct CA as (CF1 & CF2 & CLP & CFN & CNA & CND & CKA). cbn [fst snd] in *.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (args := combine (map (fun pn => Z_to_bv 64 (fst pn)) P) As).
  assert (LP : length (map (fun pn => Z_to_bv 64 (fst pn)) P) = length As) by (rewrite length_map; exact CLP).
  assert (LA : length args = length As) by (unfold args; rewrite length_combine, LP; lia).
  assert (U2 : bv_unsigned (reg_get regs_t 2) = bv_unsigned sp - 64).
  { change (reg_get regs_t 2) with (getr regs_t 2). rewrite T2. apply unsigned_lit. lia. }
  assert (ARGS : forall k p, nth_error args k = Some p ->
            mc_arg (normalize rsegs mc) (bv_unsigned sp - 64 - 80) (bv_unsigned sp - 64) e k p).
  { intros k [w s] Hk. destruct (ps_nth_combine _ _ _ _ k w s Hk) as (Hw & Hs).
    rewrite nth_error_map in Hw. destruct (nth_error P k) as [pn|] eqn:EP; cbn in Hw; [|discriminate].
    injection Hw as <-.
    destruct (CKA k s pn Hs EP) as (BP & PNZ & PIN & PSZ & PBS & PN0).
    apply (ps_mc_arg Lc Ac mc mdc e k pn s); [exact HM | exact RA | exact BP | exact PIN | lia | exact PBS | exact PN0 | | lia].
    rewrite Forall_forall in LXA. apply LXA. exact (nth_error_In _ _ Hs). }
  assert (EF : bytes_at rsegs (normalize rsegs mc) e
                 (le4 (Z_to_bv 64 20) ++ le4 (Z_to_bv 64 (Z.of_nat (length args))))).
  { apply bytes_at_normalize; [exact RA|]. apply bytes_at_app. split.
    - unfold CALL_OFF_FN in CFN. rewrite Z.add_0_r in CFN. exact CFN.
    - rewrite LA. replace (e + Z.of_nat (length (le4 (Z_to_bv 64 20)))) with (e + CALL_OFF_NARGS)
        by (rewrite length_le4; unfold CALL_OFF_NARGS; reflexivity). exact CNA. }
  assert (STn : stk rsegs (normalize rsegs mc) (bv_unsigned sp - 8320) (bv_unsigned sp - 64)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC. left. unfold PINS_SET_K. lia. }
  assert (FRn : rw_cells rsegs (normalize rsegs mc) (bv_unsigned sp - 64 + 8)
                  [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
                   C8 (getr regs 8); C8 (getr regs 1)]).
  { replace (bv_unsigned sp - 64 + 8) with (bv_unsigned sp - 56) by ring.
    apply rw_cells_normalize; [exact RA | exact FR |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  assert (RC1n : rw_cells rsegs (normalize rsegs mc) 0x33d48 [C4 (Z_to_bv 64 0)]).
  { rewrite RZ in RC1. apply rw_cells_normalize; [exact RA | exact RC1 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N. lia. }
  assert (ESn : rw_cells rsegs (normalize rsegs mc) 0x340f8 [C8 (Z_to_bv 64 (r_state R1))]).
  { apply rw_cells_normalize; [exact RA | | intros i Hi; cbn in Hi; apply glob_ro_false; unfold GLOB_LO, GLOB_N; lia].
    apply rc_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x340f8 with (G_REC + OFF_STATE) by (unfold G_REC, OFF_STATE; lia). exact X4. }
  assert (Q18 : reg_get regs_t 18 = Z_to_bv 64 e) by exact T18.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8, Q18.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply (ps_run_mix MIX) with (lo := bv_unsigned sp - 8320);
      [apply mem_inv_normalize | rewrite U2; exact STn | rewrite U2; lia | lia | rewrite U2; exact FRn | exact RC1n
      | exact X7 | exact EF | lia | lia | rewrite LA, LA4; lia | | exact ESn | exact X9].
    intros k p Hk. rewrite U2. exact (ARGS k p Hk). }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m1n & -> & MU1n & WM1n
    & ES1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mc RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mc RA) MR1r RO1 WM1n) as WM1.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR1r ES1n) as ES1.
  rewrite U2 in MU1. unfold args in ES1. rewrite (ps_combine_snd _ _ _ _ LP) in ES1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2r).
  assert (HWW : forall a, 0 <= a < 2 ^ 64 ->
            ~ outside [(bv_unsigned sp - 64 - 80, bv_unsigned sp - 64); (0x340f8, 0x34100)] a ->
            bv_unsigned sp - PINS_SET_K <= a < bv_unsigned sp \/ rec_area a).
  { intros a Ra Hm. cbn in Hm. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, PINS_SET_K. lia. }
  assert (SI2 : sinv B API PINS_SET_K (bv_unsigned sp) L A mem md O Lc Ac m1 mdc (rec_mix R1 (REC_PINS_SET, As)) Oc b).
  { apply (sinv_munch_core B API SEGS GOWN AX PINS_SET_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc R1 Oc b m1 _
             (rec_mix R1 (REC_PINS_SET, As)) SI MU1 WM1 HWW).
    unfold g_rec_rep in *.
    apply (rec_rep_set_state rsegs G_REC REC_SC Lc Ac mc m1 R1 Oc (mixcall (r_state R1) REC_PINS_SET As) GR).
    - apply mixcall_range. exact X9.
    - replace (G_REC + OFF_STATE) with 0x340f8 by (unfold G_REC, OFF_STATE; lia). exact (rc_c8_bytes m1 0x340f8 _ ES1).
    - intros a Ha N. apply (munch_mbyte rsegs _ mc m1 a MU1); [unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia|].
      match goal with |- outside ?W a => destruct (outside_dec W a) as [H|H]; [exact H|] end. exfalso.
      cbn in H. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, OFF_STATE in *. lia.
    - intros a Ha _. apply glob_writable. apply ps_glob. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha. lia.
    - exact (sinv_kept B API SEGS AX PINS_SET_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc R1 Oc b m1 _ SI MU1 HWW). }
  assert (E2_1 : getr R2 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X2r eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = sp).
  { rewrite (getr_of_eqv _ _ 2 X2r eq_refl). simp_regs. rewrite U2.
    replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) by ring. apply Z_to_bv_bv_unsigned. }
  assert (E2_10 : getr R2 10 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 10 X2r eq_refl); simp_regs; reflexivity).
  assert (RP2 : regs_preserved regs R2).
  { apply (kept_ex_pres [2; 8; 9; 18; 19; 20; 21]).
    - apply (kept_ex_trans _ regs regs_t R2 KT). kept_ex_tac X2r.
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|Hr]; [exact E2_2|].
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X2r eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  eapply SR_mono.
  { exact (code_tail PINS_SET_K L A regs mem md O Lc Ac R2 m1 mdc (rec_mix R1 (REC_PINS_SET, As)) Oc b bpre 0 PRE CK SI2
             E2_1 ltac:(unfold spZ; rewrite E2_2; reflexivity) RP2 E2_10 ltac:(lia) FRM BLE ROOMb). }
  intros c' H. exists (rec_mix R1 (REC_PINS_SET, As)), 0. split; [exact ESC | exact H].
Qed.

Lemma ps_arg : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre R1 s y (Q : config -> Prop),
  call_pre_t B API PINS_SET_K L A regs mem md ->
  sinv B API PINS_SET_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_PINS_SET As) Oc b ->
  (length As < 6)%nat -> sb_le (sb_shift b A Ac) bpre ->
  room_slots (sb_malloc bpre (Z.of_nat (length y) + 1)) (LMAX + 1) ->
  YK0s.ret_ok (getr R1 1) -> getr R1 2 = Z_to_bv 64 (spZ regs - 64) -> getr R1 4 = getr regs 4 ->
  getr R1 10 = Z_to_bv 64 s -> xsrc Lc Ac mc (spZ regs - 64) s y ->
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
        sinv B API PINS_SET_K (spZ regs) L A mem md O L2 A2 m3 md2 (rec_record R REC_PINS_SET (As ++ [y]))
          (Oc ++ [(p, Z.of_nat (length y) + 1)]) b) ->
     SR rsegs (mkCfg (mkst R2 (getr R1 1) m2 (seg_rom rsegs)) md2) Q) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15780) mc (seg_rom rsegs)) mdc) Q.
Proof using SEGS ERRNO_LOW GOTG GRD GOWN GERR AX XSTRDUP.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre R1 s y Q PRE SI H6 BLE ROOM RET E2 E4 E10 XS FR K.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold PINS_SET_K in HCEIL, HWS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SP1 : spZ R1 = bv_unsigned sp - 64) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  destruct XS as (N0 & LX & slack & BS & PAD & DJ & HOME).
  pose proof XSTRDUP as XC. unfold xstrdup_contract in XC. rewrite SEGS in XC.
  eapply SR_bind.
  { apply (XC Lc Ac R1 mc mdc s y slack (sb_shift b A Ac)).
    - apply (call_pre_k_of_rjr B _ PINS_SET_K (bv_unsigned sp) rec_area _ L A mem md Lc Ac mc mdc XSTRDUP_K R1 RJ).
      + exact RET.
      + rewrite SP1. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP1. unfold PINS_SET_K, XSTRDUP_K, ALLOC_STACK. lia.
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
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs mc); [exact FR|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K Lc Ac R1 mc mdc _ L2 A2 R2 m2 md2 (bv_unsigned sp - 56 + i)
                HM POST2 ltac:(lia) ltac:(rewrite SP1; unfold XSTRDUP_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (KG : forall a, 0x33d10 <= a < 0x34108 -> mbyte rsegs m2 a = mbyte rsegs mc a).
  { intros a Ha. assert (GA : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N) by (apply ps_glob; exact Ha).
    rewrite SEGS in PF2. apply PF2.
    - right. exact (glob_in_img B SEGS a GA).
    - exact (GOWN _ _ _ _ a HM (glob_in a GA)).
    - exact (GOWN _ _ _ _ a PM2 (glob_in a GA)).
    - intros [Hs|He]; [rewrite SP1 in Hs; unfold XSTRDUP_K, ALLOC_STACK in Hs; lia | exact (GERR a (glob_in a GA) He)].
    - intros Hp. cbv beta in Hp. apply (FBc (a - p)); [lia|]. replace (p + (a - p)) with a by ring.
      exact (glob_in_img B SEGS a GA). }
  apply (K L2 A2 R2 m2 md2 p RP2 A0' ltac:(lia) PM2 RA2 FR2 KG).
  - pose proof BLK2 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A Ac A2).
    rewrite <- (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2 bl1 bl2 p _ EB1 EB2).
    apply sb_malloc_mono. exact BLE.
  - intros m3 W MU WM HW NA AR.
    exact (proj1 (arg_post (bv_unsigned sp) L A mem md O Lc Ac mc mdc R As Oc b R1 L2 A2 R2 m2 md2 p y m3 W
      SI H6 ltac:(rewrite SP1; unfold PINS_SET_K, XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SP1; lia)
      POST2 NZ FB2 BLK2 BK2 UB2 BYT2 RA2 GK2 INI2 RGN2 RS2 N0 LX MU WM HW NA AR)).
Qed.

Lemma ps_room : forall b n0 n1 n2 n3 nr x, 0 <= n0 -> 0 <= n1 -> 0 <= n2 -> 0 <= n3 -> 0 <= nr -> 0 <= x ->
  room_slots (sb_malloc (sb_malloc (sb_malloc (sb_malloc (sb_malloc (sb_malloc b n0) n1) n2) n3) nr) nr) x ->
  room_slots (sb_malloc b n0) x /\ room_slots (sb_malloc (sb_malloc b n0) n1) x /\
  room_slots (sb_malloc (sb_malloc (sb_malloc b n0) n1) n2) x /\
  room_slots (sb_malloc (sb_malloc (sb_malloc (sb_malloc b n0) n1) n2) n3) x.
Proof.
  intros b n0 n1 n2 n3 nr x H0 H1 H2 H3 H4 H5 RM.
  split; [|split; [|split]];
    (eapply room_slots_mono; [| | exact RM]; [unfold sb_le, sb_malloc; cbn; lia | lia]).
Qed.

Lemma ps_nr : forall R As, -2^31 <= r_code R < 2^31 ->
  0 <= Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_SET As)))) + 1 <= LMAX + 1.
Proof.
  intros R As H. unfold rec_stub_code. cbv zeta.
  assert (HC : -2^31 <= r_code (rec_record R REC_PINS_SET As) < 2^31)
    by (unfold rec_record; destruct (Nat.ltb _ 16); exact H).
  destruct (r_refuse (rec_record R REC_PINS_SET As) =? 0); cbn [snd rec_answer_code];
    [pose proof (resp_length 0 ltac:(lia)) | pose proof (resp_length _ HC)]; unfold LMAX; lia.
Qed.

Lemma ps_cells_n : forall mk m2 e k off, 0x33d10 <= e -> e + 56 <= 0x340f8 -> 8 <= off <= 40 ->
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

Ltac ps_back m2 RA2 can REL RO EQ MUn WMn NAn EAn m MU WM NA EA Rn X :=
  let EC := fresh "EC" in let MR := fresh "MR" in
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL) as [EC MR];
  revert EC MR RO EQ; generalize (ms_mem can) as m; intros m EC MR RO EQ; subst can;
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR RO MUn) as MU;
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR RO WMn) as WM;
  pose proof (rw_cells_rel rsegs _ _ _ _ MR NAn) as NA;
  pose proof (rw_cells_rel rsegs _ _ _ _ MR EAn) as EA;
  clear MUn WMn NAn EAn MR;
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (Rn & -> & X).

Ltac ps_hw EE :=
  let a := fresh "a" in let Ra := fresh "Ra" in let Hm := fresh "Hm" in
  intros a Ra Hm; cbn [outside] in Hm; try rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS;
  cbn [length]; lia.

Ltac ps_na NA :=
  apply cells_bytes_at in NA; cbn [cells_bytes cbytes] in NA; rewrite app_nil_r in NA; exact NA.

Ltac ps_ar EE EA e k :=
  apply cells_bytes_at in EA; cbn [cells_bytes cbytes] in EA; rewrite app_nil_r in EA;
  match goal with |- bytes_at _ _ ?ad _ => replace ad with (e + k)
    by (try rewrite <- EE; unfold CALL_OFF_ARGS; cbn [length]; lia) end;
  exact EA.

Ltac ps_reg X :=
  match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end; simp_regs.

Definition ps_post (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (uri files lay verdict : option (list byte)) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' r,
    pins_set_m R uri files lay verdict = (R', r) /\
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
    fp_kept fx fx' /\
    call_post_rec B (aa_MR API) PINS_SET_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 r /\
    g_rec_rep rsegs L' A' mem' R' O' /\ owns_new L A O O' /\
    others_kept rsegs L A mem L' A' mem' O /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    ro_agree rsegs mem' /\ f18_words rsegs mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_mallocs b (pins_set_sizes uri files lay verdict r)) /\
    res_ok_slots A' (sb_shift b A A').

Lemma ps_body : forall L A regs mem md (pu pf pl pv : Z) (uri files lay verdict : option (list byte)) R O b
    Lc Ac R1 m1 md1 Oc,
  call_pre_t B API PINS_SET_K L A regs mem md ->
  getr regs 11 = Z_to_bv 64 pf -> getr regs 12 = Z_to_bv 64 pl -> getr regs 13 = Z_to_bv 64 pv ->
  str_arg B L A O (spZ regs) PINS_SET_K mem pu uri -> str_arg B L A O (spZ regs) PINS_SET_K mem pf files ->
  str_arg B L A O (spZ regs) PINS_SET_K mem pl lay -> str_arg B L A O (spZ regs) PINS_SET_K mem pv verdict ->
  ro_agree rsegs mem -> frm_zero fp_csr -> -2^31 <= r_code R < 2^31 ->
  room_slots (sb_mallocs b (pins_set_sizes uri files lay verdict (snd (pins_set_m R uri files lay verdict))))
    (LMAX + 1) ->
  sinv B API PINS_SET_K (spZ regs) L A mem md O Lc Ac m1 md1 (rec_record R REC_PINS_SET []) Oc b ->
  sb_le (sb_shift b A Ac) b -> (length (r_calls R) <= 16)%nat ->
  getr R1 1 = Z_to_bv 64 0x16ea4 -> getr R1 2 = Z_to_bv 64 (spZ regs - 64) -> getr R1 8 = Z_to_bv 64 0x33d10 ->
  getr R1 9 = getr regs 13 -> getr R1 10 = Z_to_bv 64 (psel pu 0x10a19) ->
  getr R1 18 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R1 19 = getr regs 12 -> getr R1 20 = getr regs 11 ->
  kept_ex [2; 8; 9; 18; 19; 20; 21] regs R1 ->
  rw_cells rsegs m1 (spZ regs - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)] ->
  bytes_at rsegs m1 (rec_entry G_REC REC_SC R + 4) (le4 (Z_to_bv 64 0)) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15780) m1 (seg_rom rsegs)) md1)
    (ps_post L A regs mem md uri files lay verdict R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN GERR AX CTX SLACK XSTRDUP MIX ANSC.
  intros L A regs mem md pu pf pl pv uri files lay verdict R O b Lc Ac R1 m1 md1 Oc
    PRE AF AL AV SU SF SL SV RA FRM HCODE ROOM SI1 BLE1 HN E1_1 E1_2 E1_8 E1_9 E1_10 E1_18 E1_19 E1_20 KT1 FR1 NA1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold PINS_SET_K in HCEIL, HWS.
  pose proof (ps_entry_bounds R) as (EB1 & EB2).
  pose proof (ps_nr R [sarg uri; sarg files; sarg lay; darg verdict (bstr "-"%string)] HCODE) as NRB.
  set (e := rec_entry G_REC REC_SC R) in *.
  assert (EE : e = rec_entry G_REC REC_SC R) by reflexivity.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  unfold pins_set_sizes, sb_mallocs in ROOM. cbn [map app fold_left] in ROOM.
  set (nr := Z.of_nat (length (resp (snd (pins_set_m R uri files lay verdict))))) in *.
  change (Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_SET
    [sarg uri; sarg files; sarg lay; darg verdict (bstr "-"%string)]))))) with nr in NRB.
  pose proof (ps_room b (Z.of_nat (length (sarg uri)) + 1) (Z.of_nat (length (sarg files)) + 1)
                (Z.of_nat (length (sarg lay)) + 1) (Z.of_nat (length (darg verdict (bstr "-"%string))) + 1)
                (nr + 1) (LMAX + 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold LMAX; lia) ROOM)
    as (RM0 & RM1 & RM2 & RM3).
  pose proof SI1 as (RJ1 & _ & _ & _ & _ & RA1 & _).
  assert (XK : 64 + XSTRDUP_K <= PINS_SET_K) by (unfold PINS_SET_K, XSTRDUP_K, ALLOC_STACK; lia).
  assert (XN : forall Lx Ax mx, ro_agree rsegs mx -> xsrc Lx Ax mx (bv_unsigned sp - 64) 0x10a19 (bstr "(null)"%string)).
  { intros Lx Ax mx RX. apply xsrc_null; [exact RX | unfold XSTRDUP_K, ALLOC_STACK; lia]. }
  assert (XD : forall Lx Ax mx, ro_agree rsegs mx -> xsrc Lx Ax mx (bv_unsigned sp - 64) 0x108b0 (bstr "-"%string)).
  { intros Lx Ax mx RX. apply xsrc_dash; [exact RX | unfold XSTRDUP_K, ALLOC_STACK; lia]. }
  destruct (xsrc_of PINS_SET_K (bv_unsigned sp) L A mem md O Lc Ac m1 md1 pu uri _ _ RJ1 RA RA1 XK SU (XN _ _ _ RA1))
    as (PU & XU).
  destruct (xsrc_of PINS_SET_K (bv_unsigned sp) L A mem md O Lc Ac m1 md1 pf files _ _ RJ1 RA RA1 XK SF (XN _ _ _ RA1))
    as (PF & _).
  destruct (xsrc_of PINS_SET_K (bv_unsigned sp) L A mem md O Lc Ac m1 md1 pl lay _ _ RJ1 RA RA1 XK SL (XN _ _ _ RA1))
    as (PL & _).
  destruct (xsrc_of PINS_SET_K (bv_unsigned sp) L A mem md O Lc Ac m1 md1 pv verdict _ _ RJ1 RA RA1 XK SV (XD _ _ _ RA1))
    as (PV & _).
  assert (T1 : getr R1 4 = getr regs 4) by exact (KT1 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)).
  assert (LXU : Z.of_nat (length (sarg uri)) <= LMAX) by exact (proj1 (proj2 XU)).
  apply (ps_arg L A regs mem md O Lc Ac m1 md1 R [] Oc b b R1 _ (sarg uri) _ PRE SI1 ltac:(cbn; lia) BLE1 RM0
           ltac:(rewrite E1_1; apply bv_eq; vm_compute; reflexivity) E1_2 T1 E1_10 XU FR1).
  intros L2 A2 R2 m2 md2 p0 RP2 A02 P0 PM2 RA2 FR2 KG2 BLE2 CL2. change (spZ regs) with (bv_unsigned sp) in *.
  destruct (ps_cells_n m1 m2 e (Z_to_bv 64 0) 8 EB1 EB2 ltac:(lia) RA2 KG2 NA1) as (NAn & junk0 & EWn).
  destruct (mr_model B _ LAWS L2 A2 m2 md2 PM2) as (Hh2 & Hl2 & _).
  assert (R2_10 : reg_get R2 10 = Z_to_bv 64 p0) by exact A02.
  assert (R2_18 : reg_get R2 18 = Z_to_bv 64 e) by exact (eq_trans (RP2 18 ltac:(unfold callee_saved; lia)) E1_18).
  assert (R2_20 : reg_get R2 20 = Z_to_bv 64 pf)
    by exact (eq_trans (eq_trans (RP2 20 ltac:(unfold callee_saved; lia)) E1_20) AF).
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R2_10, R2_18, R2_20.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply ps_seg_a0; [exact NAn | exact EWn | lia | lia]. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (b1' & b2' & b3' & b4' & m3n & -> & MU3n & WM3n & NA3n & EA3n).
  ps_back m2 RA2 can3 REL3 RO3 EQ3 MU3n WM3n NA3n EA3n m3 MU3 WM3 NA3 EA3 R3 X3.
  pose proof NA3 as NB3. apply cells_bytes_at in NB3. cbn [cells_bytes cbytes] in NB3. rewrite app_nil_r in NB3.
  pose proof (CL2 m3 _ MU3 WM3 ltac:(ps_hw EE) ltac:(ps_na NA3) ltac:(ps_ar EE EA3 e 8)) as SI3.
  cbn [app] in SI3.
  assert (KT3 : kept_ex [2; 8; 9; 18; 19; 20; 21] regs R3).
  { apply (kept_ex_trans _ regs R2 R3); [apply (kept_ex_trans _ regs R1 R2 KT1); apply kept_ex_of_pres; exact RP2|].
    kept_ex_tac X3. }
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x16edc) by (ps_reg X3; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by (ps_reg X3; exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E1_2)).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 0x33d10)
    by (ps_reg X3; exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E1_8)).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 pv)
    by (ps_reg X3; exact (eq_trans (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) E1_9) AV)).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 (psel pf 0x10a19)) by (ps_reg X3; reflexivity).
  assert (E3_18 : getr R3 18 = Z_to_bv 64 e) by (ps_reg X3; reflexivity).
  assert (E3_19 : getr R3 19 = Z_to_bv 64 pl)
    by (ps_reg X3; exact (eq_trans (eq_trans (RP2 19 ltac:(unfold callee_saved; lia)) E1_19) AL)).
  assert (E3_21 : getr R3 21 = Z_to_bv 64 (e + 8)) by (ps_reg X3; reflexivity).
  assert (T3 : getr R3 4 = getr regs 4) by exact (KT3 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & RA3 & _).
  destruct (xsrc_of PINS_SET_K (bv_unsigned sp) L A mem md O L2 A2 m3 md2 pf files _ _ RJ3 RA RA3 XK SF (XN _ _ _ RA3))
    as (_ & XF).
  assert (LXF : Z.of_nat (length (sarg files)) <= LMAX) by exact (proj1 (proj2 XF)).
  apply (ps_arg L A regs mem md O L2 A2 m3 md2 R [sarg uri] _ b _ R3 _ (sarg files) _ PRE SI3 ltac:(cbn; lia) BLE2 RM1
           ltac:(rewrite E3_1; apply bv_eq; vm_compute; reflexivity) E3_2 T3 E3_10 XF FR3).
  intros L4 A4 R4 m4 md4 p1 RP4 A04 P1 PM4 RA4 FR4 KG4 BLE4 CL4. change (spZ regs) with (bv_unsigned sp) in *.
  destruct (ps_cells_n m3 m4 e (Z_to_bv 64 1) 16 EB1 EB2 ltac:(lia) RA4 KG4 NB3) as (NAn4 & junk1 & EWn4).
  destruct (mr_model B _ LAWS L4 A4 m4 md4 PM4) as (Hh4 & Hl4 & _).
  assert (R4_10 : reg_get R4 10 = Z_to_bv 64 p1) by exact A04.
  assert (R4_18 : reg_get R4 18 = Z_to_bv 64 e) by exact (eq_trans (RP4 18 ltac:(unfold callee_saved; lia)) E3_18).
  assert (R4_19 : reg_get R4 19 = Z_to_bv 64 pl) by exact (eq_trans (RP4 19 ltac:(unfold callee_saved; lia)) E3_19).
  assert (R4_21 : reg_get R4 21 = Z_to_bv 64 (e + 8))
    by exact (eq_trans (RP4 21 ltac:(unfold callee_saved; lia)) E3_21).
  rewrite E3_1.
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R4_10, R4_18, R4_19, R4_21.
    eapply (evt_normalize rsegs); [exact WX | exact RA4 |].
    eapply ps_seg_a1; [exact NAn4 | exact EWn4 | lia | lia]. }
  intros ms5 (can5 & (s5n & Q5 & REL5 & RO5) & EQ5).
  destruct Q5 as (c1' & c2' & c3' & c4' & m5n & -> & MU5n & WM5n & NA5n & EA5n).
  ps_back m4 RA4 can5 REL5 RO5 EQ5 MU5n WM5n NA5n EA5n m5 MU5 WM5 NA5 EA5 R5 X5.
  pose proof NA5 as NB5. apply cells_bytes_at in NB5. cbn [cells_bytes cbytes] in NB5. rewrite app_nil_r in NB5.
  pose proof (CL4 m5 _ MU5 WM5 ltac:(ps_hw EE) ltac:(ps_na NA5) ltac:(ps_ar EE EA5 e 16)) as SI5.
  cbn [app] in SI5.
  assert (KT5 : kept_ex [2; 8; 9; 18; 19; 20; 21] regs R5).
  { apply (kept_ex_trans _ regs R4 R5); [apply (kept_ex_trans _ regs R3 R4 KT3); apply kept_ex_of_pres; exact RP4|].
    kept_ex_tac X5. }
  assert (E5_1 : getr R5 1 = Z_to_bv 64 0x16f10) by (ps_reg X5; reflexivity).
  assert (E5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by (ps_reg X5; exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E3_2)).
  assert (E5_8 : getr R5 8 = Z_to_bv 64 0x33d10)
    by (ps_reg X5; exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) E3_8)).
  assert (E5_9 : getr R5 9 = Z_to_bv 64 pv)
    by (ps_reg X5; exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E3_9)).
  assert (E5_10 : getr R5 10 = Z_to_bv 64 (psel pl 0x10a19)) by (ps_reg X5; reflexivity).
  assert (E5_18 : getr R5 18 = Z_to_bv 64 e) by (ps_reg X5; reflexivity).
  assert (E5_21 : getr R5 21 = Z_to_bv 64 (e + 8)) by (ps_reg X5; reflexivity).
  assert (T5 : getr R5 4 = getr regs 4) by exact (KT5 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)).
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m4 m5 _ _ FR4 MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof SI5 as (RJ5 & _ & _ & _ & _ & RA5 & _).
  destruct (xsrc_of PINS_SET_K (bv_unsigned sp) L A mem md O L4 A4 m5 md4 pl lay _ _ RJ5 RA RA5 XK SL (XN _ _ _ RA5))
    as (_ & XL).
  assert (LXL : Z.of_nat (length (sarg lay)) <= LMAX) by exact (proj1 (proj2 XL)).
  apply (ps_arg L A regs mem md O L4 A4 m5 md4 R [sarg uri; sarg files] _ b _ R5 _ (sarg lay) _ PRE SI5
           ltac:(cbn; lia) BLE4 RM2 ltac:(rewrite E5_1; apply bv_eq; vm_compute; reflexivity) E5_2 T5 E5_10 XL FR5).
  intros L6 A6 R6 m6 md6 p2 RP6 A06 P2 PM6 RA6 FR6 KG6 BLE6 CL6. change (spZ regs) with (bv_unsigned sp) in *.
  destruct (ps_cells_n m5 m6 e (Z_to_bv 64 2) 24 EB1 EB2 ltac:(lia) RA6 KG6 NB5) as (NAn6 & junk2 & EWn6).
  destruct (mr_model B _ LAWS L6 A6 m6 md6 PM6) as (Hh6 & Hl6 & _).
  assert (R6_9 : reg_get R6 9 = Z_to_bv 64 pv) by exact (eq_trans (RP6 9 ltac:(unfold callee_saved; lia)) E5_9).
  assert (R6_10 : reg_get R6 10 = Z_to_bv 64 p2) by exact A06.
  assert (R6_18 : reg_get R6 18 = Z_to_bv 64 e) by exact (eq_trans (RP6 18 ltac:(unfold callee_saved; lia)) E5_18).
  assert (R6_21 : reg_get R6 21 = Z_to_bv 64 (e + 8))
    by exact (eq_trans (RP6 21 ltac:(unfold callee_saved; lia)) E5_21).
  rewrite E5_1.
  eapply evt_SR_canon; [ | exact Hh6 | exact Hl6 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R6_9, R6_10, R6_18, R6_21.
    eapply (evt_normalize rsegs); [exact WX | exact RA6 |].
    eapply ps_seg_a2; [exact NAn6 | exact EWn6 | lia | lia]. }
  intros ms7 (can7 & (s7n & Q7 & REL7 & RO7) & EQ7).
  destruct Q7 as (d1' & d2' & d3' & d4' & m7n & -> & MU7n & WM7n & NA7n & EA7n).
  ps_back m6 RA6 can7 REL7 RO7 EQ7 MU7n WM7n NA7n EA7n m7 MU7 WM7 NA7 EA7 R7 X7.
  pose proof NA7 as NB7. apply cells_bytes_at in NB7. cbn [cells_bytes cbytes] in NB7. rewrite app_nil_r in NB7.
  pose proof (CL6 m7 _ MU7 WM7 ltac:(ps_hw EE) ltac:(ps_na NA7) ltac:(ps_ar EE EA7 e 24)) as SI7.
  cbn [app] in SI7.
  assert (KT7 : kept_ex [2; 8; 9; 18; 19; 20; 21] regs R7).
  { apply (kept_ex_trans _ regs R6 R7); [apply (kept_ex_trans _ regs R5 R6 KT5); apply kept_ex_of_pres; exact RP6|].
    kept_ex_tac X7. }
  assert (E7_1 : getr R7 1 = Z_to_bv 64 0x16f44) by (ps_reg X7; reflexivity).
  assert (E7_2 : getr R7 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by (ps_reg X7; exact (eq_trans (RP6 2 ltac:(unfold callee_saved; lia)) E5_2)).
  assert (E7_8 : getr R7 8 = Z_to_bv 64 0x33d10)
    by (ps_reg X7; exact (eq_trans (RP6 8 ltac:(unfold callee_saved; lia)) E5_8)).
  assert (E7_10 : getr R7 10 = Z_to_bv 64 (psel pv 0x108b0)) by (ps_reg X7; reflexivity).
  assert (E7_18 : getr R7 18 = Z_to_bv 64 e) by (ps_reg X7; reflexivity).
  assert (E7_21 : getr R7 21 = Z_to_bv 64 (e + 8)) by (ps_reg X7; reflexivity).
  assert (T7 : getr R7 4 = getr regs 4) by exact (KT7 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)).
  assert (FR7 : rw_cells rsegs m7 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m6 m7 _ _ FR6 MU7 WM7). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof SI7 as (RJ7 & _ & _ & _ & _ & RA7 & _).
  destruct (xsrc_of PINS_SET_K (bv_unsigned sp) L A mem md O L6 A6 m7 md6 pv verdict _ _ RJ7 RA RA7 XK SV
              (XD _ _ _ RA7)) as (_ & XV).
  assert (LXV : Z.of_nat (length (darg verdict (bstr "-"%string))) <= LMAX) by exact (proj1 (proj2 XV)).
  apply (ps_arg L A regs mem md O L6 A6 m7 md6 R [sarg uri; sarg files; sarg lay] _ b _ R7 _ (darg verdict (bstr "-"%string))
           _ PRE SI7 ltac:(cbn; lia) BLE6 RM3 ltac:(rewrite E7_1; apply bv_eq; vm_compute; reflexivity) E7_2 T7 E7_10 XV
           FR7).
  intros L8 A8 R8 m8 md8 p3 RP8 A08 P3 PM8 RA8 FR8 KG8 BLE8 CL8. change (spZ regs) with (bv_unsigned sp) in *.
  destruct (ps_cells_n m7 m8 e (Z_to_bv 64 3) 32 EB1 EB2 ltac:(lia) RA8 KG8 NB7) as (NAn8 & junk3 & EWn8).
  destruct (mr_model B _ LAWS L8 A8 m8 md8 PM8) as (Hh8 & Hl8 & _).
  assert (R8_10 : reg_get R8 10 = Z_to_bv 64 p3) by exact A08.
  assert (R8_18 : reg_get R8 18 = Z_to_bv 64 e) by exact (eq_trans (RP8 18 ltac:(unfold callee_saved; lia)) E7_18).
  assert (R8_21 : reg_get R8 21 = Z_to_bv 64 (e + 8))
    by exact (eq_trans (RP8 21 ltac:(unfold callee_saved; lia)) E7_21).
  rewrite E7_1.
  eapply evt_SR_canon; [ | exact Hh8 | exact Hl8 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R8_10, R8_18, R8_21.
    eapply (evt_normalize rsegs); [exact WX | exact RA8 |].
    eapply ps_seg_a3; [exact NAn8 | exact EWn8 | lia]. }
  intros ms9 (can9 & (s9n & Q9 & REL9 & RO9) & EQ9).
  destruct Q9 as (f1' & f2' & m9n & -> & MU9n & WM9n & NA9n & EA9n).
  ps_back m8 RA8 can9 REL9 RO9 EQ9 MU9n WM9n NA9n EA9n m9 MU9 WM9 NA9 EA9 R9 X9.
  pose proof (CL8 m9 _ MU9 WM9 ltac:(ps_hw EE) ltac:(ps_na NA9) ltac:(ps_ar EE EA9 e 32)) as SI9.
  cbn [app] in SI9.
  assert (KT9 : kept_ex [2; 8; 9; 18; 19; 20; 21] regs R9).
  { apply (kept_ex_trans _ regs R8 R9); [apply (kept_ex_trans _ regs R7 R8 KT7); apply kept_ex_of_pres; exact RP8|].
    kept_ex_tac X9. }
  assert (E9_2 : getr R9 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by (ps_reg X9; exact (eq_trans (RP8 2 ltac:(unfold callee_saved; lia)) E7_2)).
  assert (E9_8 : getr R9 8 = Z_to_bv 64 0x33d10)
    by (ps_reg X9; exact (eq_trans (RP8 8 ltac:(unfold callee_saved; lia)) E7_8)).
  assert (E9_18 : getr R9 18 = Z_to_bv 64 e) by (ps_reg X9; reflexivity).
  assert (FR9 : rw_cells rsegs m9 (bv_unsigned sp - 56)
    [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
     C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m8 m9 _ _ FR8 MU9 WM9). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply SR_mono.
  { eapply (ps_tail L A regs mem md O L8 A8 m9 md8 R [sarg uri; sarg files; sarg lay; darg verdict (bstr "-"%string)] _ b
             _ R9 PRE SI9 HN eq_refl).
    - repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil.
    - exact BLE8.
    - eapply room_slots_mono; [apply sb_le_refl | exact NRB | exact ROOM].
    - exact FRM.
    - exact FR9.
    - exact E9_2.
    - exact E9_8.
    - exact E9_18.
    - exact KT9. }
  intros c' (Rc & code & ESC & TR).
  destruct TR as (fx' & L' & A' & regs' & mem' & md' & O' & -> & FK & POST & A10 & GR' & ON' & OK' & BL' & RA' & F18'
    & INI' & RGN' & BLE' & RES').
  rewrite SEGS in *. unfold ps_post.
  exists fx', L', A', regs', mem', md', (fst (rec_answer_code Rc code)), O', (snd (rec_answer_code Rc code)).
  split; [transitivity (rec_answer_code Rc code); [exact ESC | apply surjective_pairing]|].
  split; [reflexivity|]. split; [exact FK|]. split; [exact POST|]. split; [exact A10|]. split; [exact GR'|].
  split; [exact ON'|]. split; [exact OK'|]. split; [exact BL'|]. split; [exact RA'|]. split; [exact F18'|].
  split; [exact INI'|]. split; [exact RGN'|]. split; [exact BLE' | exact RES'].
Qed.

Theorem pins_set_holds : pins_set_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GOWN GERR AX CTX SLACK RCF XSTRDUP MIX ANSC.
  unfold pins_set_contract.
  intros L A regs mem md pu pf pl pv uri files lay verdict R O b PRE AU AF AL AV SU SF SL SV GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold PINS_SET_K in HCEIL, HWS.
  rewrite SEGS in GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API PINS_SET_K L A regs mem md R O b PRK ltac:(unfold PINS_SET_K; lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof SI0 as (RJ0 & _).
  destruct (xsrc_of PINS_SET_K (bv_unsigned sp) L A mem md O L A mem md pu uri _ _ RJ0 RA RA
              ltac:(unfold PINS_SET_K, XSTRDUP_K, ALLOC_STACK; lia) SU
              (xsrc_null L A mem (bv_unsigned sp - 64) RA ltac:(unfold XSTRDUP_K, ALLOC_STACK; lia))) as (PU & _).
  assert (ST : stk rsegs mem (bv_unsigned sp - 8320) (bv_unsigned sp)).
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
      eapply ps_seg_lt; [exact ST | lia | lia | exact NC | exact Hn]. }
    intros ms1 (can1 & (c0 & c1 & c2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    destruct (glob_rw_cells m1 (0x33d58 + 56 * Z.of_nat n) 8 ltac:(unfold GLOB_LO; lia)
                ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
    assert (E1_18 : getr R1 18 = Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) by (ps_reg X1; reflexivity).
    assert (E1_21 : getr R1 21 = Z_to_bv 64 pu) by (ps_reg X1; exact AU).
    assert (Q18 : reg_get R1 18 = Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) by exact E1_18.
    assert (Q21 : reg_get R1 21 = Z_to_bv 64 pu) by exact E1_21.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q18, Q21.
      eapply ps_seg_rec; [exact EW | exact PU]. }
    intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
    assert (MU : munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x33d50, 0x33d54);
                        (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] mem m2).
    { apply (munch_trans _ mem m1 m2).
      - eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in Hx |- *. tauto.
      - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx |- *. tauto. }
    assert (NC2 : rw_cells rsegs m2 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]).
    { apply (rw_cells_transport rsegs _ m1 m2 _ _ NC1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
      repeat split; lia. }
    pose proof (sinv_record_lt B API SEGS GOWN AX PINS_SET_K (bv_unsigned sp) L A mem md O L A mem md R O b m2 _
                  REC_PINS_SET SI0 Hn ltac:(unfold REC_FN_COUNT, REC_PINS_SET; lia) MU (wmono_trans _ _ _ _ WM1 WM2)
                  ltac:(intros a Ra Hm; cbn [outside] in Hm; unfold n in *; unfold PINS_SET_K; lia) NC2 EN2) as SI1.
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 56)
      [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
       C8 (getr regs 1)]).
    { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
      repeat split; lia. }
    pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
    apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
    apply (ps_body L A regs mem md pu pf pl pv uri files lay verdict R O b L A R2 m2 md O PRE AF AL AV SU SF SL SV RA FRM
             HCODE ROOM SI1 ltac:(rewrite sb_shift_refl; apply sb_le_refl) ltac:(lia)).
    + ps_reg X2. reflexivity.
    + ps_reg X2. change (reg_get R1 2) with (getr R1 2). ps_reg X1. reflexivity.
    + ps_reg X2. change (reg_get R1 8) with (getr R1 8). ps_reg X1. reflexivity.
    + ps_reg X2. change (reg_get R1 9) with (getr R1 9). ps_reg X1. reflexivity.
    + ps_reg X2. reflexivity.
    + ps_reg X2. rewrite (rec_entry_lt G_REC REC_SC R Hn). fold n. unfold G_REC, OFF_CALLS, CALL_SIZE. f_equal; lia.
    + ps_reg X2. change (reg_get R1 19) with (getr R1 19). ps_reg X1. reflexivity.
    + ps_reg X2. change (reg_get R1 20) with (getr R1 20). ps_reg X1. reflexivity.
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
      eapply ps_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16e64) by (ps_reg X1; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 64)) by (ps_reg X1; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (ps_reg X1; reflexivity).
    assert (E1_9 : getr R1 9 = getr regs 13) by (ps_reg X1; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 0x33d10) by (ps_reg X1; reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 1) by (ps_reg X1; reflexivity).
    assert (E1_19 : getr R1 19 = getr regs 12) by (ps_reg X1; reflexivity).
    assert (E1_20 : getr R1 20 = getr regs 11) by (ps_reg X1; reflexivity).
    assert (E1_21 : getr R1 21 = Z_to_bv 64 pu) by (ps_reg X1; exact AU).
    assert (SP1 : spZ R1 = bv_unsigned sp - 64) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    pose proof (sinv_stack B API SEGS GOWN AX PINS_SET_K (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                  ltac:(intros a Ra Hm; cbn [outside] in Hm; unfold PINS_SET_K; lia)) as SI1.
    apply (sinv_rcf B API SEGS ERRNO_LOW GOTG GRD GOWN AX RCF PINS_SET_K (bv_unsigned sp) L A mem md O L A m1 md R O b R1 _
             SI1 H16 E1_10 E1_11).
    + rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP1. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    + rewrite SP1. unfold PINS_SET_K, RCF_K, ALLOC_STACK. lia.
    + rewrite SP1. lia.
    + rewrite E1_4. exact HTP.
    + intros L' A' regs' m' md' RP' POST FRK.
      rewrite E1_1.
      pose proof POST as (RJ' & _ & _ & _ & _ & RA' & _ & _ & BLE & _).
      destruct (mr_model B _ LAWS L' A' m' md' (proj1 RJ')) as (Hh' & Hl' & _).
      assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (ps_reg X1; reflexivity).
      assert (Q8 : reg_get regs' 8 = Z_to_bv 64 0x33d10)
        by exact (eq_trans (RP' 8 ltac:(unfold callee_saved; lia)) E1_8).
      assert (Q21 : reg_get regs' 21 = Z_to_bv 64 pu)
        by exact (eq_trans (RP' 21 ltac:(unfold callee_saved; lia)) E1_21).
      assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 56)
        [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
         C8 (getr regs 8); C8 (getr regs 1)]).
      { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
        apply FRK. rewrite SP1. lia. }
      destruct (glob_rw_cells m' 0x33d10 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
      eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8, Q21.
        eapply ps_seg_jrec; [exact EW | exact PU]. }
      intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX PINS_SET_K (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                  _ REC_PINS_SET POST ltac:(unfold REC_FN_COUNT, REC_PINS_SET; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn [outside] in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 56)
        [C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
         C8 (getr regs 8); C8 (getr regs 1)]).
      { apply (rw_cells_transport rsegs _ m' m2 _ _ FR' MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
        repeat split; lia. }
      pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
      apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
      rewrite sb_shift_refl in BLE.
      apply (ps_body L A regs mem md pu pf pl pv uri files lay verdict R O b L' A' R2 m2 md' Oc' PRE AF AL AV SU SF SL SV
               RA FRM HCODE ROOM SI2 BLE ltac:(lia)).
      * ps_reg X2. reflexivity.
      * ps_reg X2. exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
      * ps_reg X2. reflexivity.
      * ps_reg X2. exact (eq_trans (RP' 9 ltac:(unfold callee_saved; lia)) E1_9).
      * ps_reg X2. reflexivity.
      * ps_reg X2. rewrite (rec_entry_full G_REC REC_SC R H16). reflexivity.
      * ps_reg X2. exact (eq_trans (RP' 19 ltac:(unfold callee_saved; lia)) E1_19).
      * ps_reg X2. exact (eq_trans (RP' 20 ltac:(unfold callee_saved; lia)) E1_20).
      * apply (kept_ex_trans _ regs regs' R2); [|kept_ex_tac X2].
        apply (kept_ex_trans _ regs R1 regs'); [kept_ex_tac X1 | apply kept_ex_of_pres; exact RP'].
      * exact FR2.
      * rewrite (rec_entry_full G_REC REC_SC R H16).
        replace (REC_SC + 4) with (0x33d10 + Z.of_nat 4) by (unfold REC_SC; lia).
        exact EA.
Qed.

End P.
