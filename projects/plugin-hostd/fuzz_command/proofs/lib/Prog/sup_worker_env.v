(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module names, addresses and numbers changed; 841 of its 1092 lines of code are new or changed and 297 lines of the source are left out. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecStub rec_shape_of_c RecGlue.
Import ListNotations.
Open Scope Z_scope.

Lemma swe_pre_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 j0 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n))
                     a2 b0 b1 b2 a3 a4 a5 a6 a7 a1 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16a6c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 48)
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a08) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 14 step.
  rewrite sx32_lit by lia.
  assert (C1 : negb (bv_eqb (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 16)) = true).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia. }
  rewrite C1. cbv iota.
  do 7 step.
  rewrite da_addr by lia.
  apply evt_done.
  do 5 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma swe_rec :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (jk : list byte),
  rw_cells rsegs m e [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16a88) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1
                     (sel_null s3) a1 a2 a3 a4 a5 a6 a7 s2 (sel_null s3) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e jk EW.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  step.
  destruct (Z.eq_dec (bv_unsigned s3) 0) as [Z2|Z2].
  - if_false. do 4 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_eq _ _) Z2).
    apply evt_done. eexists. split; [reflexivity|].
    split; [eassumption|]. split; eassumption.
  - if_true. do 2 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_neq _ _) Z2).
    apply evt_done. eexists. split; [reflexivity|].
    split; [eassumption|]. split; eassumption.
Qed.

Lemma swe_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat) (jk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 jk] ->
  evt rsegs (fun ms' => exists b1 b2 j0 m',
       ms' = MS (mkR (Z_to_bv 64 0x16a88) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a2 (sel_null a0)
                     b1 b2 a3 a4 a5 a6 a7 a1 (sel_null a0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 48)
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a08) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n jk ST LO LO2 NC Hn EW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply swe_pre_lt; [exact ST | exact LO | exact LO2 | exact NC | exact Hn] |].
  intros ms1 (b0 & b1 & b2 & j0 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1).
  assert (EW1 : rw_cells rsegs m1 (0x33d58 + 56 * Z.of_nat n) [CB 8 jk]).
  { apply (rw_cells_transport rsegs [(bv_unsigned sp - 48, bv_unsigned sp); (0x33d50, 0x33d54)] m m1 _ _ EW MU1 WM1).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  eapply evt_cut; [eapply swe_rec; exact EW1 |].
  intros ms2 (m2 & -> & MU2 & WM2 & EN2).
  apply evt_done. exists b1, b2, j0, m2. split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m2).
    - apply (munch_weaken [(bv_unsigned sp - 48, bv_unsigned sp); (0x33d50, 0x33d54)]); [|exact MU1].
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

Lemma swe_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists b2 j0 m',
       ms' = MS (mkR (Z_to_bv 64 0x16a4c) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     a2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) b2 a3 a4 a5 a6 a7
                     a1 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 48)
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a08) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 14 step.
  rewrite sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  do 3 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma swe_ret16 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (jk : list byte),
  rw_cells rsegs m 0x33d10 [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16a88) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1
                     (sel_null s3) a1 a2 a3 a4 a5 a6 a7 s2 (sel_null s3) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a4c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m jk EW.
  step.
  eapply swe_rec. exact EW.
Qed.

Lemma swe_st1 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (e + 8) [CB 8 junk] ->
  evt rsegs (fun ms' => exists b1 b2 b3 b4 m',
       ms' = MS (mkR (Z_to_bv 64 0x16ac0) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 (sel_null s2) b1 b2 b3 b4 a5 a6 a7
                     (sel_null s2) (Z_to_bv 64 (e + 8)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 16)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 1)]
       /\ rw_cells rsegs m' (e + 8) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16a88) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EN EA.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 6 step.
  rewrite sx32_lit by lia.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 0)) 3) with 0 by reflexivity. rewrite ?Z.add_0_r.
  replace (bv_unsigned (Z_to_bv 64 0) + 1) with 1 by reflexivity.
  do 3 step.
  if_false.
  step.
  destruct (Z.eq_dec (bv_unsigned s2) 0) as [Z2|Z2].
  - if_false. do 4 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_eq _ _) Z2).
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - if_true. do 2 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_neq _ _) Z2).
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma swe_st2 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 1)] ->
  rw_cells rsegs m (e + 16) [CB 8 junk] ->
  evt rsegs (fun ms' => exists b1 b2 b3 b4 m',
       ms' = MS (mkR (Z_to_bv 64 0x16af4) sp gp tp t0 t1 t2 (Z_to_bv 64 e) (sel_null s1) (sel_null s1) b1 b2 b3 b4
                     a5 a6 a7 s2 (Z_to_bv 64 (e + 8)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 16, e + 24)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 2)]
       /\ rw_cells rsegs m' (e + 16) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (e + 8)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16ac0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EN EA.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 16, e + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 5 step.
  rewrite sx32_lit by lia.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 1)) 3) with 8 by reflexivity.
  replace (bv_unsigned (Z_to_bv 64 1) + 1) with 2 by reflexivity.
  do 3 step.
  if_false.
  step.
  destruct (Z.eq_dec (bv_unsigned s1) 0) as [Z2|Z2].
  - if_false. do 4 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_eq _ _) Z2).
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - if_true. do 2 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_neq _ _) Z2).
    apply evt_done. do 5 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma swe_st3 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 2)] ->
  rw_cells rsegs m (e + 24) [CB 8 junk] ->
  evt rsegs (fun ms' => exists b1 b2 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 b1 b2 a3 a4 a5 a6 a7
                     s2 (Z_to_bv 64 (e + 8)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16b0c) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 24, e + 32)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 3)]
       /\ rw_cells rsegs m' (e + 24) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (e + 8)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16af4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EN EA.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 24, e + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  rewrite sx32_lit by lia.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 2)) 3) with 16 by reflexivity.
  replace (bv_unsigned (Z_to_bv 64 2) + 1) with 3 by reflexivity.
  do 2 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma swe_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' s20 s30 : word) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 j0; C8 s30; C8 s20; C8 s10'; C8 s00; C8 ra0] -> 48 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' s0 a0 (Z_to_bv 64 1) a3 a4 a5 a6 a7
                                    s20 s30 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15bc8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16b1c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' s20 s30 j0 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 10 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma swe_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10705 (str_bytes "worker_env"%string).
Proof.
  intros m MI. apply rom_chk_bytes; [exact (ro_agree_of_inv m MI) | lia | cbn; lia | vm_compute; reflexivity].
Qed.

Lemma swe_shape : shape_find shape_rows (str_bytes "worker_env"%string) = 0x10417.
Proof. vm_compute. reflexivity. Qed.

Lemma swe_after : rec_shape_of_contract ->
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sp0 ra0 s00 s10' s20 s30 : word) (j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 j0; C8 s30; C8 s20; C8 s10'; C8 s00; C8 ra0] ->
  stk rsegs m lo (bv_unsigned sp0 - 48) -> lo + 112 <= bv_unsigned sp0 -> 0x34100 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s00 s10' s0 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                     a3' a4' a5' a6' a7' s20 s30 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x15bc8) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp0 - 112, bv_unsigned sp0 - 48)] m m' /\ wmono rsegs m m')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16b0c) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sp0 ra0 s00 s10' s20 s30 j0 FR ST LO LO2 GS MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP.
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 48)) = bv_unsigned sp0 - 48) by (apply unsigned_lit; lia).
  do 4 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "worker_env"%string).
    - exact MI.
    - rewrite SPU. exact ST.
    - rewrite SPU. unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS.
    - left. rewrite SPU. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (swe_verb m MI)|].
      left. rewrite SPU. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  rewrite SPU in MU2. unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x16b1c) by lia. rewrite swe_shape.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp0 - 48) [CB 8 j0; C8 s30; C8 s20; C8 s10'; C8 s00; C8 ra0]).
  { apply (rw_cells_transport rsegs _ m m2 _ _ FR MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply swe_tail; [exact FR2 | lia] |].
  intros ms3 ->. apply evt_done.
  exists m2, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [reflexivity|].
  split; [|exact WM2].
  replace (bv_unsigned sp0 - 112) with (bv_unsigned sp0 - 48 - 64) by ring. exact MU2.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import answer_c rec_calls_free_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import sup_worker_env_c.

Lemma swe_pres_step : forall R2 R3 M3,
  Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r)) ->
  regs_preserved R2 R3.
Proof.
  intros R2 R3 M3 X3 K r Hr. pose proof (RecStub.getr_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ. exact (K r Hr).
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
Hypothesis XSD : xstrdup_contract B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Lemma swe_arg : forall L A regs mem md pf pc pn format cpus nice R O b Lc Ac R1 m1 md1 Oc (j0 : list byte),
  call_pre_t B API 12384 L A regs mem md -> getr regs 10 = Z_to_bv 64 pf -> getr regs 11 = Z_to_bv 64 pc ->
  getr regs 12 = Z_to_bv 64 pn ->
  str_arg B L A O (spZ regs) 12384 mem pf format -> str_arg B L A O (spZ regs) 12384 mem pc cpus ->
  str_arg B L A O (spZ regs) 12384 mem pn nice ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> ro_agree rsegs mem -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_worker_env_sizes format cpus nice (snd (sup_worker_env_m R format cpus nice))))
    (LMAX + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O Lc Ac m1 md1 (rec_record R REC_WORKER_ENV []) Oc b ->
  sb_le (sb_shift b A Ac) b -> (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  getr R1 1 = Z_to_bv 64 0x16a88 -> getr R1 2 = Z_to_bv 64 (spZ regs - 48) -> getr R1 4 = getr regs 4 ->
  getr R1 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R1 9 = getr regs 12 -> getr R1 18 = getr regs 11 ->
  getr R1 10 = sel_null (getr regs 10) ->
  kept_ex [2; 8; 9; 18; 19] regs R1 ->
  rw_cells rsegs m1 (spZ regs - 48)
    [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
     C8 (reg_get regs 1)] ->
  bytes_at rsegs m1 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 0)) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15780) m1 (seg_rom rsegs)) md1)
    (sup_worker_env_ret B API L A regs mem md format cpus nice R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK ANSF XSD RSO RIMG RFREE.
  intros L A regs mem md pf pc pn format cpus nice R O b Lc Ac R1 m1 md1 Oc j0 PRE G10 G11 G12 SA1 SA2 SA3 GS RA FRM
    ROOM SI1 BLE1 HN HCODE E1 E2 E4 E8 E9 E18 E10 KE1 FR1 NA1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  change (snd (sup_worker_env_m R format cpus nice)) with
    (snd (rec_answer (rec_record R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice])
      (REC_WORKER_ENV, [sarg format; sarg cpus; sarg nice]) (daemon_shape "worker_env") true)) in ROOM.
  unfold sup_worker_env_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice])
                  (REC_WORKER_ENV, [sarg format; sarg cpus; sarg nice]) (daemon_shape "worker_env") true)) <= 16)%nat).
  { pose proof (stub_len R REC_WORKER_ENV [sarg format; sarg cpus; sarg nice] (daemon_shape "worker_env") true HCODE)
      as H.
    assert (LX : length (daemon_shape "worker_env") = 6%nat) by (vm_compute; reflexivity).
    rewrite LX in H. exact H. }
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
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI1 as (RJ1 & _ & _ & _ & _ & RA1 & F181 & RS1).
  pose proof RJ1 as (HM1 & _).
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O Lc Ac m1 md1 _ Oc b pf format
              SI1 RA ltac:(unfold NULL_LIT; lia) SA1)
    as (s & slack & PW & SEL & S0 & BS & N0 & LX & AL & DJ & HOME & NRA).
  assert (SELW : sel_null (getr regs 10) = Z_to_bv 64 s)
    by (rewrite G10; unfold sel_null; rewrite unsigned_lit by lia; rewrite <- SEL; destruct (pf =? 0); reflexivity).
  set (x := sarg format) in *.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof XSD as XS. unfold xstrdup_contract in XS. rewrite SEGS in XS.
  eapply SR_bind.
  { apply (XS Lc Ac R1 m1 md1 s x slack (sb_shift b A Ac)).
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md Lc Ac m1 md1 XSTRDUP_K R1 RJ1).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP1. unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP1. lia.
      + rewrite E4. exact HTP.
    - rewrite E10. exact SELW.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact AL.
    - rewrite SP1. unfold XSTRDUP_K, ALLOC_STACK. destruct DJ as [D|D]; [left; lia | right; lia].
    - rewrite SP1. unfold str_home in HOME |- *.
      destruct HOME as [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H].
    - exact RS1.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE1|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + lia.
    - exact RA1. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p & -> & POST2 & P2a & NZ & AL16 & FB2 & BLK2 & BK2 & UB2 & BYT2 & SRC2
    & RA2 & GK2 & INI2 & RGN2 & RS2).
  rewrite SEGS in RA2, BYT2 |- *.
  pose proof POST2 as (PM2 & _ & _ & _ & _ & RP2 & _ & PF2 & _).
  pose proof FB2 as (FBa & FBb & FBc).
  assert (R2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E2).
  assert (R2_8 : getr R2 8 = Z_to_bv 64 e) by exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E8).
  assert (R2_8' : reg_get R2 8 = Z_to_bv 64 e) by exact R2_8.
  assert (POST2' : call_post_k B (aa_MR API) XSTRDUP_K Lc Ac R1 m1 md1 (fun a => p <= a < p + (Z.of_nat (length x) + 1))
                     L2 A2 R2 m2 md2).
  { pose proof POST2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
    intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; lia]. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K Lc Ac R1 m1 md1 _ L2 A2 R2 m2 md2 (bv_unsigned sp - 48 + i)
                HM1 POST2 ltac:(lia) ltac:(rewrite SP1; unfold XSTRDUP_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (GK : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> mbyte rsegs m2 a = mbyte rsegs m1 a).
  { intros a Ha. destruct (GFACT a (glob_in a Ha)) as (Gi & _ & _ & Ge).
    rewrite SEGS in PF2.
    refine (proj1 (PF2 a (or_intror Gi) (GOWN Lc Ac m1 md1 a HM1 (glob_in a Ha)) (GOWN L2 A2 m2 md2 a PM2 (glob_in a Ha))
                    _ _)).
    - unfold scratch_k. rewrite SP1. unfold XSTRDUP_K, ALLOC_STACK.
      intros [H|H]; [unfold GLOB_LO, GLOB_N in Ha; lia | exact (Ge H)].
    - cbv beta. intros H. apply (FBc (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
  assert (NA2 : rw_cells rsegs m2 (e + 4) [C4 (Z_to_bv 64 0)]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|].
    apply (bytes_at_transfer rsegs m1); [exact NA1|]. intros i Hi. rewrite length_le4 in Hi.
    apply GK. unfold GLOB_LO, GLOB_N; lia. }
  destruct (glob_rw_cells m2 (e + 8) 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW2].
  assert (NAn : rw_cells rsegs (normalize rsegs m2) (e + 4) [C4 (Z_to_bv 64 0)]).
  { apply rw_cells_normalize; [exact RA2 | exact NA2 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  assert (EWn : rw_cells rsegs (normalize rsegs m2) (e + 8) [CB 8 junk]).
  { apply rw_cells_normalize; [exact RA2 | exact EW2 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  destruct (ax_statics AX L2 A2 m2 md2 PM2) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F182 : f18_words rsegs m2).
  { apply (f18_words_after m1 m2 g F181); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK2 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  destruct (mr_model B _ LAWS L2 A2 m2 md2 PM2) as (Hh2 & Hl2 & _).
  rewrite E1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite R2_8'.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply swe_st1; [exact NAn | exact EWn]. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (b31 & b32 & b33 & b34 & m3n & -> & MU3n & WM3n & NA3n & EA3n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 MU3n) as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 WM3n) as WM3.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR3r NA3n) as NA3.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR3r EA3n) as EA3.
  clear MU3n WM3n NA3n EA3n MR3r.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (BN3 : bytes_at rsegs m3 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS)
                  (le4 (Z_to_bv 64 (Z.of_nat (length (@nil (list byte))) + 1)))).
  { apply cells_bytes_at in NA3. cbn [cells_bytes cbytes] in NA3. rewrite app_nil_r in NA3. exact NA3. }
  assert (BS3 : bytes_at rsegs m3 (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))))
                  (le8 (Z_to_bv 64 p))).
  { apply cells_bytes_at in EA3. cbn [cells_bytes cbytes] in EA3. rewrite app_nil_r in EA3.
    replace (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte)))) with (e + 8)
      by (rewrite EE; unfold CALL_OFF_ARGS; cbn [length Z.of_nat]; lia).
    assert (Q : reg_get R2 10 = Z_to_bv 64 p) by exact P2a. rewrite Q in EA3. exact EA3. }
  pose proof (sinv_sarg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O Lc Ac m1 md1 R
                REC_WORKER_ENV [] Oc b XSTRDUP_K R1 L2 A2 R2 m2 md2 m3 [(e + 4, e + 16)] x p (Z.of_nat (length x) + 1)
                SI1 ltac:(cbn; lia) ltac:(rewrite SP1; unfold XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SP1; lia)
                POST2' MU3 WM3
                ltac:(intros a Ra Hm; cbn in Hm; rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS; cbn [length Z.of_nat]; lia)
                NZ FB2 BLK2 UB2 BK2 RGN2 BN3 BS3 BYT2 N0 LX ltac:(unfold LMAX in *; lia) INI2 RS2 RA2 F182) as SI3.
  cbn [app] in SI3.
  assert (RP13 : forall r, callee_saved r -> r <> 18 -> r <> 19 -> getr R3 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r)).
  { intros r Hr N18 N19. rewrite <- (RP2 r Hr). pose proof (RecStub.getr_nz r Hr) as NZr.
    rewrite (getr_of_eqv _ _ _ X3 NZr). unfold getr. rewrite NZr. unfold callee_saved in Hr.
    assert (CC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 20 \/ r = 21 \/
                 r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr N18 N19.
    repeat (destruct CC as [CC|CC]; [subst r; simp_regs; first [reflexivity | symmetry; exact R2_8']|]).
    subst r; simp_regs; reflexivity. }
  assert (R3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RP13 2 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)) E2).
  assert (R3_4 : getr R3 4 = getr regs 4)
    by exact (eq_trans (RP13 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)) E4).
  assert (R3_8 : getr R3 8 = Z_to_bv 64 e)
    by exact (eq_trans (RP13 8 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)) E8).
  assert (R3_9 : getr R3 9 = getr regs 12)
    by exact (eq_trans (RP13 9 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)) E9).
  assert (SP3 : spZ R3 = bv_unsigned sp - 48) by (unfold spZ; rewrite R3_2; apply unsigned_lit; lia).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & RA3 & F183 & RS3).
  pose proof RJ3 as (HM3 & _).
  assert (BLE2 : sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length x) + 1))).
  { destruct BLK2 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A Ac A2).
    rewrite <- (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2 bl1 bl2 p _ EB1 EB2).
    apply sb_malloc_mono. exact BLE1. }
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x16ac0) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_10 : getr R3 10 = sel_null (getr regs 11)).
  { rewrite (getr_of_eqv _ _ 10 X3 eq_refl). simp_regs. f_equal.
    exact (eq_trans (RP2 18 ltac:(unfold callee_saved; lia)) E18). }
  assert (R3_19 : reg_get R3 19 = Z_to_bv 64 (e + 8)) by (rewrite (getr_of_eqv _ _ 19 X3 eq_refl); simp_regs; reflexivity).
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 _ _ b pc cpus
              SI3 RA ltac:(unfold NULL_LIT; lia) SA2)
    as (s' & slack' & PW' & SEL' & S0' & BS' & N0' & LX' & AL' & DJ' & HOME' & NRA').
  assert (SELW' : sel_null (getr regs 11) = Z_to_bv 64 s')
    by (rewrite G11; unfold sel_null; rewrite unsigned_lit by lia; rewrite <- SEL'; destruct (pc =? 0); reflexivity).
  set (y := sarg cpus) in *.
  pose proof (bytes_at_bound _ _ _ _ BS') as SB'. rewrite length_app in SB'. cbn [length] in SB'.
  eapply SR_bind.
  { apply (XS L2 A2 R3 m3 md2 s' y slack' (sb_shift b A A2)).
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m3 md2 XSTRDUP_K R3 RJ3).
      + rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP3. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. lia.
      + rewrite R3_4. exact HTP.
    - rewrite E3_10. exact SELW'.
    - exact BS'.
    - exact N0'.
    - exact LX'.
    - exact AL'.
    - rewrite SP3. unfold XSTRDUP_K, ALLOC_STACK. destruct DJ' as [D|D]; [left; lia | right; lia].
    - rewrite SP3. unfold str_home in HOME' |- *.
      destruct HOME' as [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H].
    - exact RS3.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE2|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + lia.
    - exact RA3. }
  intros c4 RET4.
  destruct RET4 as (L4 & A4 & R4 & m4 & md4 & p2 & -> & POST4 & P4a & NZ4 & AL164 & FB4 & BLK4 & BK4 & UB4 & BYT4 & SRC4
    & RA4 & GK4 & INI4 & RGN4 & RS4).
  rewrite SEGS in RA4, BYT4 |- *.
  pose proof POST4 as (PM4 & _ & _ & _ & _ & RP4 & _ & PF4 & _).
  pose proof FB4 as (FBa4 & FBb4 & FBc4).
  assert (R4_8' : reg_get R4 8 = Z_to_bv 64 e) by exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) R3_8).
  assert (R4_19' : reg_get R4 19 = Z_to_bv 64 (e + 8))
    by exact (eq_trans (RP4 19 ltac:(unfold callee_saved; lia)) R3_19).
  assert (POST4' : call_post_k B (aa_MR API) XSTRDUP_K L2 A2 R3 m3 md2 (fun a => p2 <= a < p2 + (Z.of_nat (length y) + 1))
                     L4 A4 R4 m4 md4).
  { pose proof POST4 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
    intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; lia]. }
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K L2 A2 R3 m3 md2 _ L4 A4 R4 m4 md4 (bv_unsigned sp - 48 + i)
                HM3 POST4 ltac:(lia) ltac:(rewrite SP3; unfold XSTRDUP_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (GK' : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> mbyte rsegs m4 a = mbyte rsegs m3 a).
  { intros a Ha. destruct (GFACT a (glob_in a Ha)) as (Gi & _ & _ & Ge).
    rewrite SEGS in PF4.
    refine (proj1 (PF4 a (or_intror Gi) (GOWN L2 A2 m3 md2 a HM3 (glob_in a Ha)) (GOWN L4 A4 m4 md4 a PM4 (glob_in a Ha))
                    _ _)).
    - unfold scratch_k. rewrite SP3. unfold XSTRDUP_K, ALLOC_STACK.
      intros [H|H]; [unfold GLOB_LO, GLOB_N in Ha; lia | exact (Ge H)].
    - cbv beta. intros H. apply (FBc4 (a - p2)); [lia|]. replace (p2 + (a - p2)) with a by ring. exact Gi. }
  assert (NA4 : rw_cells rsegs m4 (e + 4) [C4 (Z_to_bv 64 1)]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|].
    apply cells_bytes_at in NA3. cbn [cells_bytes cbytes] in NA3. rewrite app_nil_r in NA3.
    apply (bytes_at_transfer rsegs m3); [exact NA3|]. intros i Hi. rewrite length_le4 in Hi.
    apply GK'. unfold GLOB_LO, GLOB_N; lia. }
  destruct (glob_rw_cells m4 (e + 16) 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk4 EW4].
  assert (NA4n : rw_cells rsegs (normalize rsegs m4) (e + 4) [C4 (Z_to_bv 64 1)]).
  { apply rw_cells_normalize; [exact RA4 | exact NA4 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  assert (EW4n : rw_cells rsegs (normalize rsegs m4) (e + 16) [CB 8 junk4]).
  { apply rw_cells_normalize; [exact RA4 | exact EW4 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  destruct (ax_statics AX L4 A4 m4 md4 PM4) as (_ & (g4 & Hg4 & HWg4) & _).
  rewrite GRD, SEGS in HWg4.
  assert (F184 : f18_words rsegs m4).
  { apply (f18_words_after m3 m4 g4 F183); [|exact Hg4 | exact HWg4].
    intros i Hi. pose proof (GK4 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  destruct (mr_model B _ LAWS L4 A4 m4 md4 PM4) as (Hh4 & Hl4 & _).
  rewrite E3_1.
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite R4_8', R4_19'.
    eapply (evt_normalize rsegs); [exact WX | exact RA4 |].
    eapply swe_st2; [exact NA4n | exact EW4n]. }
  intros ms5 (can5 & (s5n & Q5 & REL5 & RO5) & EQ5).
  destruct Q5 as (b51 & b52 & b53 & b54 & m5n & -> & MU5n & WM5n & NA5n & EA5n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL5) as [EC5 MR5r].
  revert EC5 MR5r RO5 EQ5. generalize (ms_mem can5) as m5. intros m5 EC5 MR5r RO5 EQ5. subst can5.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR5r RO5 MU5n) as MU5.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR5r RO5 WM5n) as WM5.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR5r NA5n) as NA5.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR5r EA5n) as EA5.
  clear MU5n WM5n NA5n EA5n MR5r.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  assert (BN5 : bytes_at rsegs m5 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS)
                  (le4 (Z_to_bv 64 (Z.of_nat (length [x]) + 1)))).
  { apply cells_bytes_at in NA5. cbn [cells_bytes cbytes] in NA5. rewrite app_nil_r in NA5. exact NA5. }
  assert (BS5 : bytes_at rsegs m5 (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [x]))
                  (le8 (Z_to_bv 64 p2))).
  { apply cells_bytes_at in EA5. cbn [cells_bytes cbytes] in EA5. rewrite app_nil_r in EA5.
    replace (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [x])) with (e + 16)
      by (rewrite EE; unfold CALL_OFF_ARGS; cbn [length Z.of_nat]; lia).
    assert (Q : reg_get R4 10 = Z_to_bv 64 p2) by exact P4a. rewrite Q in EA5. exact EA5. }
  pose proof (sinv_sarg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 R
                REC_WORKER_ENV [x] _ b XSTRDUP_K R3 L4 A4 R4 m4 md4 m5 [(e + 4, e + 8); (e + 16, e + 24)] y p2
                (Z.of_nat (length y) + 1)
                SI3 ltac:(cbn; lia) ltac:(rewrite SP3; unfold XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SP3; lia)
                POST4' MU5 WM5
                ltac:(intros a Ra Hm; cbn in Hm; rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS; cbn [length Z.of_nat]; lia)
                NZ4 FB4 BLK4 UB4 BK4 RGN4 BN5 BS5 BYT4 N0' LX' ltac:(unfold LMAX in *; lia) INI4 RS4 RA4 F184) as SI5.
  cbn [app] in SI5.
  assert (RP45 : forall r, callee_saved r -> r <> 9 -> getr R5 (Z_to_bv 5 r) = getr R4 (Z_to_bv 5 r)).
  { intros r Hr N9. pose proof (RecStub.getr_nz r Hr) as NZr.
    rewrite (getr_of_eqv _ _ _ X5 NZr). unfold getr. rewrite NZr. unfold callee_saved in Hr.
    assert (CC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                 r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr N9.
    repeat (destruct CC as [CC|CC];
      [subst r; simp_regs; first [reflexivity | symmetry; exact R4_8' | symmetry; exact R4_19']|]).
    subst r; simp_regs; reflexivity. }
  assert (R5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RP45 2 ltac:(unfold callee_saved; lia) ltac:(lia))
                (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) R3_2)).
  assert (R5_4 : getr R5 4 = getr regs 4)
    by exact (eq_trans (RP45 4 ltac:(unfold callee_saved; lia) ltac:(lia))
                (eq_trans (RP4 4 ltac:(unfold callee_saved; lia)) R3_4)).
  assert (R5_8 : getr R5 8 = Z_to_bv 64 e)
    by exact (eq_trans (RP45 8 ltac:(unfold callee_saved; lia) ltac:(lia)) R4_8').
  assert (R5_19 : getr R5 19 = Z_to_bv 64 (e + 8))
    by exact (eq_trans (RP45 19 ltac:(unfold callee_saved; lia) ltac:(lia)) R4_19').
  assert (SP5 : spZ R5 = bv_unsigned sp - 48) by (unfold spZ; rewrite R5_2; apply unsigned_lit; lia).
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m4 m5 _ _ FR4 MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof SI5 as (RJ5 & _ & _ & _ & _ & RA5 & F185 & RS5).
  pose proof RJ5 as (HM5 & _).
  assert (BLE3 : sb_le (sb_shift b A A4)
                   (sb_malloc (sb_malloc b (Z.of_nat (length x) + 1)) (Z.of_nat (length y) + 1))).
  { destruct BLK4 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A2 A4).
    rewrite <- (sb_shift_add (sb_shift b A A2) L2 A2 L4 A4 bl1 bl2 p2 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE2. }
  assert (E5_1 : getr R5 1 = Z_to_bv 64 0x16af4) by (rewrite (getr_of_eqv _ _ 1 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_10 : getr R5 10 = sel_null (getr regs 12)).
  { rewrite (getr_of_eqv _ _ 10 X5 eq_refl). simp_regs. f_equal.
    exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) R3_9). }
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L4 A4 m5 md4 _ _ b pn nice
              SI5 RA ltac:(unfold NULL_LIT; lia) SA3)
    as (s'' & slack'' & PW'' & SEL'' & S0'' & BS'' & N0'' & LX'' & AL'' & DJ'' & HOME'' & NRA'').
  assert (SELW'' : sel_null (getr regs 12) = Z_to_bv 64 s'')
    by (rewrite G12; unfold sel_null; rewrite unsigned_lit by lia; rewrite <- SEL''; destruct (pn =? 0); reflexivity).
  set (z := sarg nice) in *.
  pose proof (bytes_at_bound _ _ _ _ BS'') as SB''. rewrite length_app in SB''. cbn [length] in SB''.
  eapply SR_bind.
  { apply (XS L4 A4 R5 m5 md4 s'' z slack'' (sb_shift b A A4)).
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L4 A4 m5 md4 XSTRDUP_K R5 RJ5).
      + rewrite E5_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP5. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP5. unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP5. lia.
      + rewrite R5_4. exact HTP.
    - rewrite E5_10. exact SELW''.
    - exact BS''.
    - exact N0''.
    - exact LX''.
    - exact AL''.
    - rewrite SP5. unfold XSTRDUP_K, ALLOC_STACK. destruct DJ'' as [D|D]; [left; lia | right; lia].
    - rewrite SP5. unfold str_home in HOME'' |- *.
      destruct HOME'' as [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H].
    - exact RS5.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE3|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + lia.
    - exact RA5. }
  intros c6 RET6.
  destruct RET6 as (L6 & A6 & R6 & m6 & md6 & p3 & -> & POST6 & P6a & NZ6 & AL166 & FB6 & BLK6 & BK6 & UB6 & BYT6 & SRC6
    & RA6 & GK6 & INI6 & RGN6 & RS6).
  rewrite SEGS in RA6, BYT6 |- *.
  pose proof POST6 as (PM6 & _ & _ & _ & _ & RP6 & _ & PF6 & _).
  pose proof FB6 as (FBa6 & FBb6 & FBc6).
  assert (R6_8' : reg_get R6 8 = Z_to_bv 64 e) by exact (eq_trans (RP6 8 ltac:(unfold callee_saved; lia)) R5_8).
  assert (R6_19' : reg_get R6 19 = Z_to_bv 64 (e + 8))
    by exact (eq_trans (RP6 19 ltac:(unfold callee_saved; lia)) R5_19).
  assert (POST6' : call_post_k B (aa_MR API) XSTRDUP_K L4 A4 R5 m5 md4 (fun a => p3 <= a < p3 + (Z.of_nat (length z) + 1))
                     L6 A6 R6 m6 md6).
  { pose proof POST6 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
    intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; lia]. }
  assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m5); [exact FR5|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K L4 A4 R5 m5 md4 _ L6 A6 R6 m6 md6 (bv_unsigned sp - 48 + i)
                HM5 POST6 ltac:(lia) ltac:(rewrite SP5; unfold XSTRDUP_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (GK'' : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> mbyte rsegs m6 a = mbyte rsegs m5 a).
  { intros a Ha. destruct (GFACT a (glob_in a Ha)) as (Gi & _ & _ & Ge).
    rewrite SEGS in PF6.
    refine (proj1 (PF6 a (or_intror Gi) (GOWN L4 A4 m5 md4 a HM5 (glob_in a Ha)) (GOWN L6 A6 m6 md6 a PM6 (glob_in a Ha))
                    _ _)).
    - unfold scratch_k. rewrite SP5. unfold XSTRDUP_K, ALLOC_STACK.
      intros [H|H]; [unfold GLOB_LO, GLOB_N in Ha; lia | exact (Ge H)].
    - cbv beta. intros H. apply (FBc6 (a - p3)); [lia|]. replace (p3 + (a - p3)) with a by ring. exact Gi. }
  assert (NA6 : rw_cells rsegs m6 (e + 4) [C4 (Z_to_bv 64 2)]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|].
    apply cells_bytes_at in NA5. cbn [cells_bytes cbytes] in NA5. rewrite app_nil_r in NA5.
    apply (bytes_at_transfer rsegs m5); [exact NA5|]. intros i Hi. rewrite length_le4 in Hi.
    apply GK''. unfold GLOB_LO, GLOB_N; lia. }
  destruct (glob_rw_cells m6 (e + 24) 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk6 EW6].
  assert (NA6n : rw_cells rsegs (normalize rsegs m6) (e + 4) [C4 (Z_to_bv 64 2)]).
  { apply rw_cells_normalize; [exact RA6 | exact NA6 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  assert (EW6n : rw_cells rsegs (normalize rsegs m6) (e + 24) [CB 8 junk6]).
  { apply rw_cells_normalize; [exact RA6 | exact EW6 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  destruct (ax_statics AX L6 A6 m6 md6 PM6) as (_ & (g6 & Hg6 & HWg6) & _).
  rewrite GRD, SEGS in HWg6.
  assert (F186 : f18_words rsegs m6).
  { apply (f18_words_after m5 m6 g6 F185); [|exact Hg6 | exact HWg6].
    intros i Hi. pose proof (GK6 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  destruct (mr_model B _ LAWS L6 A6 m6 md6 PM6) as (Hh6 & Hl6 & _).
  rewrite E5_1.
  eapply evt_SR_canon; [ | exact Hh6 | exact Hl6 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite R6_8', R6_19'.
    eapply (evt_normalize rsegs); [exact WX | exact RA6 |].
    eapply swe_st3; [exact NA6n | exact EW6n]. }
  intros ms7 (can7 & (s7n & Q7 & REL7 & RO7) & EQ7).
  destruct Q7 as (b71 & b72 & m7n & -> & MU7n & WM7n & NA7n & EA7n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL7) as [EC7 MR7r].
  revert EC7 MR7r RO7 EQ7. generalize (ms_mem can7) as m7. intros m7 EC7 MR7r RO7 EQ7. subst can7.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m6 RA6) MR7r RO7 MU7n) as MU7.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m6 RA6) MR7r RO7 WM7n) as WM7.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR7r NA7n) as NA7.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR7r EA7n) as EA7.
  clear MU7n WM7n NA7n EA7n MR7r.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ7 eq_refl eq_refl) as (R7 & -> & X7).
  assert (BN7 : bytes_at rsegs m7 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS)
                  (le4 (Z_to_bv 64 (Z.of_nat (length [x; y]) + 1)))).
  { apply cells_bytes_at in NA7. cbn [cells_bytes cbytes] in NA7. rewrite app_nil_r in NA7. exact NA7. }
  assert (BS7 : bytes_at rsegs m7 (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [x; y]))
                  (le8 (Z_to_bv 64 p3))).
  { apply cells_bytes_at in EA7. cbn [cells_bytes cbytes] in EA7. rewrite app_nil_r in EA7.
    replace (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [x; y])) with (e + 24)
      by (rewrite EE; unfold CALL_OFF_ARGS; cbn [length Z.of_nat]; lia).
    assert (Q : reg_get R6 10 = Z_to_bv 64 p3) by exact P6a. rewrite Q in EA7. exact EA7. }
  pose proof (sinv_sarg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O L4 A4 m5 md4 R
                REC_WORKER_ENV [x; y] _ b XSTRDUP_K R5 L6 A6 R6 m6 md6 m7 [(e + 4, e + 8); (e + 24, e + 32)] z p3
                (Z.of_nat (length z) + 1)
                SI5 ltac:(cbn; lia) ltac:(rewrite SP5; unfold XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SP5; lia)
                POST6' MU7 WM7
                ltac:(intros a Ra Hm; cbn in Hm; rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS; cbn [length Z.of_nat]; lia)
                NZ6 FB6 BLK6 UB6 BK6 RGN6 BN7 BS7 BYT6 N0'' LX'' ltac:(unfold LMAX in *; lia) INI6 RS6 RA6 F186) as SI7.
  cbn [app] in SI7.
  assert (RP67 : regs_preserved R6 R7).
  { apply (swe_pres_step R6 R7 _ X7). intros rr Hrr. unfold callee_saved in Hrr.
    assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
                 rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    clear Hrr.
    repeat (destruct CC as [CC|CC];
      [subst rr; simp_regs; first [reflexivity | symmetry; exact R6_8' | symmetry; exact R6_19']|]).
    subst rr; simp_regs; reflexivity. }
  assert (R7_2 : getr R7 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RP67 2 ltac:(unfold callee_saved; lia)) (eq_trans (RP6 2 ltac:(unfold callee_saved; lia)) R5_2)).
  assert (R7_8 : getr R7 8 = Z_to_bv 64 e)
    by exact (eq_trans (RP67 8 ltac:(unfold callee_saved; lia)) R6_8').
  assert (FR7 : rw_cells rsegs m7 (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m6 m7 _ _ FR6 MU7 WM7). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (BLE4 : sb_le (sb_shift b A A6)
                   (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length x) + 1)) (Z.of_nat (length y) + 1))
                      (Z.of_nat (length z) + 1))).
  { destruct BLK6 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A4 A6).
    rewrite <- (sb_shift_add (sb_shift b A A4) L4 A4 L6 A6 bl1 bl2 p3 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE3. }
  pose proof SI7 as (RJ7 & _ & _ & _ & _ & RA7 & _).
  pose proof RJ7 as (HM7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC7 & _).
  destruct (mr_model B _ LAWS L6 A6 m7 md6 HM7) as (Hh7 & Hl7 & _).
  assert (FRn : rw_cells rsegs (normalize rsegs m7) (bv_unsigned sp - 48)
                  [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply rw_cells_normalize; [exact RA7 | exact FR7 |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  assert (STn : stk rsegs (normalize rsegs m7) (bv_unsigned sp - 12384) (bv_unsigned sp - 48)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC7. left. lia. }
  pose proof (bytes_at_normalize rsegs m7 _ _ RA7
                (rjr_shapes B API SEGS RIMG 12384 (bv_unsigned sp) O L A mem md L6 A6 m7 md6 RJ7 GS)) as GSn.
  eapply evt_SR_canon; [ | exact Hh7 | exact Hl7 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (QQ7 : reg_get R7 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by exact R7_2.
    rewrite QQ7.
    eapply (evt_normalize rsegs); [exact WX | exact RA7 |].
    eapply (swe_after RSO); [exact FRn | exact STn | lia | lia | exact GSn | apply mem_inv_normalize]. }
  intros ms8 (can8 & (s8n & Q8 & REL8 & RO8) & EQ8).
  destruct Q8 as (m8n & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU8n & WM8n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL8) as [EC8 MR8r].
  revert EC8 MR8r RO8 EQ8. generalize (ms_mem can8) as m8. intros m8 EC8 MR8r RO8 EQ8. subst can8.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m7 RA7) MR8r RO8 MU8n) as MU8.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m7 RA7) MR8r RO8 WM8n) as WM8.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ8 eq_refl eq_refl) as (R8 & -> & X8).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L6 A6 m7 md6 _ _ b m8 _ SI7 MU8 WM8
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI8.
  assert (E8_1 : getr R8 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X8 eq_refl); simp_regs; reflexivity).
  assert (E8_2 : getr R8 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X8 eq_refl); simp_regs; reflexivity).
  assert (E8_10 : getr R8 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X8 eq_refl); simp_regs; exact R7_8).
  assert (E8_11 : getr R8 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X8 eq_refl); simp_regs; reflexivity).
  assert (E8_12 : getr R8 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X8 eq_refl); simp_regs; reflexivity).
  assert (RP8 : regs_preserved regs R8).
  { apply (kept_ex_pres [2; 8; 9; 18; 19]).
    - apply (kept_ex_trans _ regs R1 R8 KE1).
      apply (kept_ex_trans _ R1 R2 R8 (kept_ex_of_pres _ _ _ RP2)).
      apply (kept_ex_trans _ R2 R3 R8); [kept_ex_tac X3|].
      apply (kept_ex_trans _ R3 R4 R8 (kept_ex_of_pres _ _ _ RP4)).
      apply (kept_ex_trans _ R4 R5 R8); [kept_ex_tac X5|].
      apply (kept_ex_trans _ R5 R6 R8 (kept_ex_of_pres _ _ _ RP6)).
      apply (kept_ex_trans _ R6 R7 R8 (kept_ex_of_pres _ _ _ RP67)).
      kept_ex_tac X8.
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X8 eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  eapply SR_mono.
  { apply (sinv_answer (fx := fx) B API SEGS ERRNO_LOW AX CTX (ANSF fx) SLACK 12384 L A regs mem md O L6 A6 R8 m8 md6
             (rec_record R REC_WORKER_ENV [x; y; z]) _ b
             (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length x) + 1)) (Z.of_nat (length y) + 1))
                (Z.of_nat (length z) + 1)) e 0x10417
             (REC_WORKER_ENV, [x; y; z])
             (daemon_shape "worker_env") true PRE AK SI8 E8_1 ltac:(unfold spZ; rewrite E8_2; reflexivity) RP8 E8_10
             E8_11 ltac:(rewrite E8_12; reflexivity)).
    - intros _. replace (daemon_shape "worker_env") with REC_MOD_HOST_SHAPE by (vm_compute; reflexivity).
      apply mod_host_shape. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 SI8)))))).
    - intros _ _. exact (ans_entry_record R REC_WORKER_ENV [x; y; z] HN).
    - exact FRM.
    - exact BLE4.
    - eapply room_slots_mono; [| | exact ROOM].
      + apply sb_malloc_mono, sb_malloc_mono. exact BLE4.
      + unfold LMAX. lia. }
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  exists fx'', L', A', regs', mem', md', (fst (sup_worker_env_m R format cpus nice)), O',
    (snd (sup_worker_env_m R format cpus nice)), q.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK'|].
  split; [exact POST'|].
  do 10 (split; [assumption|]).
  split.
  { rewrite SEGS. apply (shapes_kept B API SEGS RIMG RFREE _ L A regs mem md _ _ L' A' regs' mem' md' PRK POST');
      [|exact GS]. intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
  repeat (split; [assumption|]). exact RES'.
Qed.

Theorem sup_worker_env_holds : sup_worker_env_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK RCF ANSF XSD RSO RIMG RFREE.
  unfold sup_worker_env_contract.
  intros L A regs mem md pf pc pn format cpus nice R O b PRE G10 G11 G12 SA1 SA2 SA3 GS GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_WORKER_ENV_K in PRE, PRK, HCEIL, HWS, SA1, SA2, SA3.
  rewrite SEGS in GS, GR, RA, F18, HWS |- *.
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
      eapply swe_seg_lt; [exact ST | lia | lia | exact NC | exact Hn | exact EW]. }
    intros ms1 (can1 & (b1 & b2 & j0 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1 & EN1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    pose proof (sinv_record_lt B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                  REC_WORKER_ENV SI0 Hn ltac:(unfold REC_FN_COUNT, REC_WORKER_ENV; lia) MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EN1) as SI1.
    pose proof EN1 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
    apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
    apply (swe_arg L A regs mem md pf pc pn format cpus nice R O b L A R1 m1 md O j0 PRE G10 G11 G12 SA1 SA2 SA3 GS RA
             FRM ROOM SI1 ltac:(rewrite sb_shift_refl; apply sb_le_refl) ltac:(lia) HCODE).
    + rewrite (getr_of_eqv _ _ 1 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 4 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 8 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 9 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 18 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 10 X1 eq_refl). simp_regs. reflexivity.
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
      eapply swe_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (b2 & j0 & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16a4c) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_9 : getr R1 9 = getr regs 12) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_18 : getr R1 18 = getr regs 11) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_19 : getr R1 19 = getr regs 10) by (rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 0x33d10)
      by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
    assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
    apply (sinv_rcf B API SEGS ERRNO_LOW GOTG GRD GOWN AX RCF 12384 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 _
             SI1 H16 E1_10 E1_11).
    + rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    + rewrite SP1. unfold RCF_K, ALLOC_STACK. lia.
    + rewrite SP1. lia.
    + rewrite E1_4. exact HTP.
    + intros L' A' regs' m' md' RP' POST FRK.
      rewrite E1_1.
      pose proof POST as (RJ' & _ & _ & _ & _ & RA' & _ & _ & BLE & _).
      destruct (mr_model B _ LAWS L' A' m' md' (proj1 RJ')) as (Hh' & Hl' & _).
      assert (R8' : getr regs' 8 = Z_to_bv 64 0x33d10) by exact (eq_trans (RP' 8 ltac:(unfold callee_saved; lia)) E1_8).
      assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 48)
                      [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                       C8 (reg_get regs 1)]).
      { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
        apply FRK. rewrite SP1. lia. }
      destruct (glob_rw_cells m' 0x33d10 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
      eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of.
        assert (Q8 : reg_get regs' 8 = Z_to_bv 64 0x33d10) by exact R8'.
        rewrite Q8.
        eapply swe_ret16. exact EW. }
      intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                  _ REC_WORKER_ENV POST ltac:(unfold REC_FN_COUNT, REC_WORKER_ENV; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
                      [CB 8 j0; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                       C8 (reg_get regs 1)]).
      { apply (rw_cells_transport rsegs _ m' m2 _ _ FR' MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
        repeat split; lia. }
      pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
      apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
      rewrite sb_shift_refl in BLE.
      apply (swe_arg L A regs mem md pf pc pn format cpus nice R O b L' A' R2 m2 md' Oc' j0 PRE G10 G11 G12 SA1 SA2 SA3
               GS RA FRM ROOM SI2 BLE ltac:(lia) HCODE).
      * rewrite (getr_of_eqv _ _ 1 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 2 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
      * rewrite (getr_of_eqv _ _ 4 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 4 ltac:(unfold callee_saved; lia)) E1_4).
      * rewrite (rec_entry_full G_REC REC_SC R H16). rewrite (getr_of_eqv _ _ 8 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 9 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 9 ltac:(unfold callee_saved; lia)) E1_9).
      * rewrite (getr_of_eqv _ _ 18 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 18 ltac:(unfold callee_saved; lia)) E1_18).
      * rewrite (getr_of_eqv _ _ 10 X2 eq_refl). simp_regs. f_equal.
        exact (eq_trans (RP' 19 ltac:(unfold callee_saved; lia)) E1_19).
      * apply (kept_ex_trans _ regs R1 R2); [kept_ex_tac X1|].
        apply (kept_ex_trans _ R1 regs' R2 (kept_ex_of_pres _ _ _ RP')). kept_ex_tac X2.
      * exact FR2.
      * rewrite (rec_entry_full G_REC REC_SC R H16).
        replace (REC_SC + CALL_OFF_NARGS) with (0x33d10 + Z.of_nat 4) by (unfold REC_SC, CALL_OFF_NARGS; lia).
        exact EA.
Qed.

End P.
