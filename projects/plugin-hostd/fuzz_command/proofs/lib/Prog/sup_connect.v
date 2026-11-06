(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its addresses and numbers changed; 855 of its 1272 lines of code are new or changed and 2325 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecStub RecGlue.
Import ListNotations.
Open Scope Z_scope.

Lemma scn_pre_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n))
                     a3 b0 b1 b2 a3 a4 a5 a6 a7 a2 a1 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16034) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 48)
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15fc8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 16 step.
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

Lemma scn_rec :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (jk : list byte),
  rw_cells rsegs m e [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16050) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1
                     (sel_null s4) a1 a2 a3 a4 a5 a6 a7 s2 s3 (sel_null s4) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 4); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16034) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e jk EW.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 4); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  step.
  destruct (Z.eq_dec (bv_unsigned s4) 0) as [Z2|Z2].
  - if_false. do 4 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_eq _ _) Z2).
    apply evt_done. eexists. split; [reflexivity|].
    split; [eassumption|]. split; eassumption.
  - if_true. do 2 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_neq _ _) Z2).
    apply evt_done. eexists. split; [reflexivity|].
    split; [eassumption|]. split; eassumption.
Qed.

Lemma scn_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat) (jk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 jk] ->
  evt rsegs (fun ms' => exists b1 b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x16050) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a3 (sel_null a0)
                     b1 b2 a3 a4 a5 a6 a7 a2 a1 (sel_null a0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 48)
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 4); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15fc8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n jk ST LO LO2 NC Hn EW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply scn_pre_lt; [exact ST | exact LO | exact LO2 | exact NC | exact Hn] |].
  intros ms1 (b0 & b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1).
  assert (EW1 : rw_cells rsegs m1 (0x33d58 + 56 * Z.of_nat n) [CB 8 jk]).
  { apply (rw_cells_transport rsegs [(bv_unsigned sp - 48, bv_unsigned sp); (0x33d50, 0x33d54)] m m1 _ _ EW MU1 WM1).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  eapply evt_cut; [eapply scn_rec; exact EW1 |].
  intros ms2 (m2 & -> & MU2 & WM2 & EN2).
  apply evt_done. exists b1, b2, m2. split; [reflexivity|].
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

Lemma scn_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x16014) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     a3 (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) b2 a3 a4 a5 a6 a7
                     a2 a1 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 48)
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15fc8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 16 step.
  rewrite sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  do 2 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma scn_ret16 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (jk : list byte),
  rw_cells rsegs m 0x33d10 [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16050) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1
                     (sel_null s4) a1 a2 a3 a4 a5 a6 a7 s2 s3 (sel_null s4) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 4); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16014) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m jk EW.
  step.
  eapply scn_rec. exact EW.
Qed.

Lemma scn_st1 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (e + 8) [CB 8 junk] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x16078) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 (Z_to_bv 64 e) s3 b2 a3 a4 a5 a6 a7
                     s2 s3 (Z_to_bv 64 (e + 8)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15e64) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 16)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 1)]
       /\ rw_cells rsegs m' (e + 8) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16050) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EN EA.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 5 step.
  rewrite sx32_lit by lia.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 0)) 3) with 0 by reflexivity. rewrite ?Z.add_0_r.
  replace (bv_unsigned (Z_to_bv 64 0) + 1) with 1 by reflexivity.
  do 5 step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma scn_mid2 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 2)] ->
  evt rsegs (fun ms' => exists b1,
       ms' = MS (mkR (Z_to_bv 64 0x16098) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 (sel_null s2) b1 a2 a3 a4 a5 a6 a7
                     (sel_null s2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16078) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e EN.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  do 3 step.
  rewrite sx32_lit by lia.
  if_false.
  step.
  destruct (Z.eq_dec (bv_unsigned s2) 0) as [Z2|Z2].
  - if_false. do 4 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_eq _ _) Z2).
    apply evt_done. eexists. reflexivity.
  - if_true. do 2 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_neq _ _) Z2).
    apply evt_done. eexists. reflexivity.
Qed.

Lemma scn_st3 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 2)] ->
  rw_cells rsegs m (e + 24) [CB 8 junk] ->
  evt rsegs (fun ms' => exists b1 b2 b3 b4 m',
       ms' = MS (mkR (Z_to_bv 64 0x160cc) sp gp tp t0 t1 t2 (Z_to_bv 64 e) (sel_null s1) (sel_null s1) b1 b2 b3 b4
                     a5 a6 a7 s2 s3 (Z_to_bv 64 (e + 8)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 24, e + 32)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 3)]
       /\ rw_cells rsegs m' (e + 24) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 (e + 8)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16098) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EN EA.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 24, e + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 5 step.
  rewrite sx32_lit by lia.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 2)) 3) with 16 by reflexivity.
  replace (bv_unsigned (Z_to_bv 64 2) + 1) with 3 by reflexivity.
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

Lemma scn_st4 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 3)] ->
  rw_cells rsegs m (e + 32) [CB 8 junk] ->
  evt rsegs (fun ms' => exists b1 b2 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 b1 b2 a3 a4 a5 a6 a7
                     s2 s3 (Z_to_bv 64 (e + 8)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x160e4) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 32, e + 40)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 4)]
       /\ rw_cells rsegs m' (e + 32) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 (e + 8)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x160cc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EN EA.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 32, e + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  rewrite sx32_lit by lia.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 3)) 3) with 24 by reflexivity.
  replace (bv_unsigned (Z_to_bv 64 3) + 1) with 4 by reflexivity.
  do 2 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma scn_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' s20 s30 s40 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [C8 s40; C8 s30; C8 s20; C8 s10'; C8 s00; C8 ra0] -> 48 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' s0 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                                    a3 a4 a5 a6 a7 s20 s30 s40 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15bc8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x160e4) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' s20 s30 s40 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 12 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import answer_c rec_calls_free_c arg_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import rec_canonical_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import sup_connect_c.

Lemma scn_nra_apart : forall s Ln lo hi, (forall a, s <= a < s + Ln -> ~ rec_area a) ->
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
Hypothesis XSD : xstrdup_contract B API.
Hypothesis ARGL : arg_line_contract B API.

Lemma scn_home_lower : forall L A sp1 sp2 s n, sp2 <= sp1 -> str_home B L A sp1 s n -> str_home B L A sp2 s n.
Proof.
  intros L A sp1 sp2 s n H [H1|[H1|H1]]; [left; lia | right; left; exact H1 | right; right; exact H1].
Qed.

Lemma scn_d3 : forall L A regs mem md pb verb line port_a port_b R O b L4 A4 R4 m4 md4 Oc4,
  call_pre_t B API 12384 L A regs mem md -> getr regs 13 = Z_to_bv 64 pb ->
  str_arg B L A O (spZ regs) 12384 mem pb port_b -> ro_agree rsegs mem -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_connect_sizes verb line port_a port_b
                              (snd (sup_connect_m R verb line port_a port_b)))) (LMAX + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O L4 A4 m4 md4
    (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a]) Oc4 b ->
  sb_le (sb_shift b A A4) (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length (sarg verb)) + 1))
                             (Z.of_nat (length line) + 1)) (Z.of_nat (length (sarg port_a)) + 1)) ->
  (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  getr R4 1 = Z_to_bv 64 0x160cc -> getr R4 2 = Z_to_bv 64 (spZ regs - 48) -> getr R4 4 = getr regs 4 ->
  getr R4 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R4 20 = Z_to_bv 64 (rec_entry G_REC REC_SC R + 8) ->
  getr R4 10 = sel_null (getr regs 13) ->
  kept_ex [2; 8; 9; 18; 19; 20] regs R4 ->
  rw_cells rsegs m4 (spZ regs - 48)
    [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
     C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs m4 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 3)) ->
  SR rsegs (mkCfg (mkst R4 (Z_to_bv 64 0x15780) m4 (seg_rom rsegs)) md4)
    (sup_connect_ret B API L A regs mem md verb line port_a port_b R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK ANSF XSD.
  intros L A regs mem md pb verb line port_a port_b R O b L4 A4 R4 m4 md4 Oc4 PRE A3 SA4 RA FRM ROOM SI4 BLE4 HN HCODE
    E1 E2 E4 E8 E20 E10 KE4 FR4 NA4.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  change (snd (sup_connect_m R verb line port_a port_b)) with
    (snd (rec_answer (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b])
           (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true)) in ROOM.
  unfold sup_connect_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b])
                  (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true)) <= 16)%nat).
  { pose proof (stub_len R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b] REC_MOD_HOST_SHAPE true HCODE)
      as H.
    assert (LX6 : length REC_MOD_HOST_SHAPE = 6%nat) by (vm_compute; reflexivity).
    rewrite LX6 in H. exact H. }
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
  assert (SP4 : spZ R4 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI4 as (RJ4 & _ & _ & _ & _ & RA4 & F184 & RS4).
  pose proof RJ4 as (HM4 & _).
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L4 A4 m4 md4 _ Oc4 b pb port_b
              SI4 RA ltac:(unfold NULL_LIT; lia) SA4)
    as (s & slack & PW & SEL & S0 & BS & N0 & LX & AL & DJ & HOME & NRA).
  assert (SELW : sel_null (getr regs 13) = Z_to_bv 64 s)
    by (rewrite A3; unfold sel_null; rewrite unsigned_lit by lia; rewrite <- SEL; destruct (pb =? 0); reflexivity).
  set (x := sarg verb) in *. set (y := sarg port_a) in *. set (z := sarg port_b) in *.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof XSD as XS. unfold xstrdup_contract in XS. rewrite SEGS in XS.
  eapply SR_bind.
  { apply (XS L4 A4 R4 m4 md4 s z slack (sb_shift b A A4)).
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L4 A4 m4 md4 XSTRDUP_K R4 RJ4).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP4. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP4. unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP4. lia.
      + rewrite E4. exact HTP.
    - rewrite E10. exact SELW.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact AL.
    - rewrite SP4. unfold XSTRDUP_K, ALLOC_STACK. destruct DJ as [D|D]; [left; lia | right; lia].
    - rewrite SP4. apply (scn_home_lower L4 A4 (bv_unsigned sp)); [lia | exact HOME].
    - exact RS4.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE4|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + lia.
    - exact RA4. }
  intros c5 RET.
  destruct RET as (L5 & A5 & R5 & m5 & md5 & p & -> & POST5 & A0' & NZ & AL16 & FB5 & BLK5 & BK5 & UB5 & BYT5 & SRC5
    & RA5 & GK5 & INI5 & RGN5 & RS5).
  rewrite SEGS in RA5, BYT5 |- *.
  pose proof POST5 as (PM5 & _ & _ & _ & _ & RP5 & _ & PF5 & _).
  pose proof FB5 as (FBa & FBb & FBc).
  assert (R5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RP5 2 ltac:(unfold callee_saved; lia)) E2).
  assert (R5_8' : reg_get R5 8 = Z_to_bv 64 e) by exact (eq_trans (RP5 8 ltac:(unfold callee_saved; lia)) E8).
  assert (R5_20' : reg_get R5 20 = Z_to_bv 64 (e + 8))
    by exact (eq_trans (RP5 20 ltac:(unfold callee_saved; lia)) E20).
  assert (POST5' : call_post_k B (aa_MR API) XSTRDUP_K L4 A4 R4 m4 md4 (fun a => p <= a < p + (Z.of_nat (length z) + 1))
                     L5 A5 R5 m5 md5).
  { pose proof POST5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
    intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; lia]. }
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m4); [exact FR4|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K L4 A4 R4 m4 md4 _ L5 A5 R5 m5 md5 (bv_unsigned sp - 48 + i)
                HM4 POST5 ltac:(lia) ltac:(rewrite SP4; unfold XSTRDUP_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (GK : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> mbyte rsegs m5 a = mbyte rsegs m4 a).
  { intros a Ha. destruct (GFACT a (glob_in a Ha)) as (Gi & _ & _ & Ge).
    rewrite SEGS in PF5.
    refine (proj1 (PF5 a (or_intror Gi) (GOWN L4 A4 m4 md4 a HM4 (glob_in a Ha)) (GOWN L5 A5 m5 md5 a PM5 (glob_in a Ha))
                    _ _)).
    - unfold scratch_k. rewrite SP4. unfold XSTRDUP_K, ALLOC_STACK.
      intros [H|H]; [unfold GLOB_LO, GLOB_N in Ha; lia | exact (Ge H)].
    - cbv beta. intros H. apply (FBc (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
  assert (NA5 : rw_cells rsegs m5 (e + 4) [C4 (Z_to_bv 64 3)]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|].
    apply (bytes_at_transfer rsegs m4); [exact NA4|]. intros i Hi. rewrite length_le4 in Hi.
    apply GK. unfold GLOB_LO, GLOB_N; lia. }
  destruct (glob_rw_cells m5 (e + 32) 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk5 EW5].
  assert (NA5n : rw_cells rsegs (normalize rsegs m5) (e + 4) [C4 (Z_to_bv 64 3)]).
  { apply rw_cells_normalize; [exact RA5 | exact NA5 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  assert (EW5n : rw_cells rsegs (normalize rsegs m5) (e + 32) [CB 8 junk5]).
  { apply rw_cells_normalize; [exact RA5 | exact EW5 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  destruct (ax_statics AX L5 A5 m5 md5 PM5) as (_ & (g5 & Hg5 & HWg5) & _).
  rewrite GRD, SEGS in HWg5.
  assert (F185 : f18_words rsegs m5).
  { apply (f18_words_after m4 m5 g5 F184); [|exact Hg5 | exact HWg5].
    intros i Hi. pose proof (GK5 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  destruct (mr_model B _ LAWS L5 A5 m5 md5 PM5) as (Hh5 & Hl5 & _).
  rewrite E1.
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite R5_8', R5_20'.
    eapply (evt_normalize rsegs); [exact WX | exact RA5 |].
    eapply scn_st4; [exact NA5n | exact EW5n]. }
  intros ms6 (can6 & (s6n & Q6 & REL6 & RO6) & EQ6).
  destruct Q6 as (b61 & b62 & m6n & -> & MU6n & WM6n & NA6n & EA6n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL6) as [EC6 MR6r].
  revert EC6 MR6r RO6 EQ6. generalize (ms_mem can6) as m6. intros m6 EC6 MR6r RO6 EQ6. subst can6.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m5 RA5) MR6r RO6 MU6n) as MU6.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m5 RA5) MR6r RO6 WM6n) as WM6.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR6r NA6n) as NA6.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR6r EA6n) as EA6.
  clear MU6n WM6n NA6n EA6n MR6r.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ6 eq_refl eq_refl) as (R6 & -> & X6).
  assert (BN6 : bytes_at rsegs m6 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS)
                  (le4 (Z_to_bv 64 (Z.of_nat (length [x; canon line; y]) + 1)))).
  { apply cells_bytes_at in NA6. cbn [cells_bytes cbytes] in NA6. rewrite app_nil_r in NA6. exact NA6. }
  assert (BS6 : bytes_at rsegs m6 (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [x; canon line; y]))
                  (le8 (Z_to_bv 64 p))).
  { apply cells_bytes_at in EA6. cbn [cells_bytes cbytes] in EA6. rewrite app_nil_r in EA6.
    replace (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [x; canon line; y])) with (e + 32)
      by (rewrite EE; unfold CALL_OFF_ARGS; change (Z.of_nat (length [x; canon line; y])) with 3; lia).
    assert (Q : reg_get R5 10 = Z_to_bv 64 p) by exact A0'. rewrite Q in EA6. exact EA6. }
  pose proof (sinv_sarg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O L4 A4 m4 md4 R
                REC_CONNECT [x; canon line; y] Oc4 b XSTRDUP_K R4 L5 A5 R5 m5 md5 m6
                [(e + 4, e + 8); (e + 32, e + 40)] z p (Z.of_nat (length z) + 1)
                SI4 ltac:(cbn; lia) ltac:(rewrite SP4; unfold XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SP4; lia)
                POST5' MU6 WM6
                ltac:(intros a Ra Hm; cbn in Hm; rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS;
                      change (Z.of_nat (length [x; canon line; y])) with 3; lia)
                NZ FB5 BLK5 UB5 BK5 RGN5 BN6 BS6 BYT5 N0 LX ltac:(unfold LMAX in *; lia) INI5 RS5 RA5 F185) as SI6.
  cbn [app] in SI6.
  assert (RK6 : kept_ex [2; 8; 9; 18; 19; 20] regs R6).
  { apply (kept_ex_trans _ regs R4 R6 KE4).
    apply (kept_ex_trans _ R4 R5 R6 (kept_ex_of_pres _ _ _ RP5)).
    kept_ex_tac X6. }
  assert (R6_2 : getr R6 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X6 eq_refl); simp_regs; exact R5_2).
  assert (R6_8 : getr R6 8 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 8 X6 eq_refl); simp_regs; reflexivity).
  assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m5 m6 _ _ FR5 MU6 WM6). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (BLE6 : sb_le (sb_shift b A A5)
                   (sb_malloc (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length x) + 1)) (Z.of_nat (length line) + 1))
                      (Z.of_nat (length y) + 1)) (Z.of_nat (length z) + 1))).
  { destruct BLK5 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A4 A5).
    rewrite <- (sb_shift_add (sb_shift b A A4) L4 A4 L5 A5 bl1 bl2 p _ EB1 EB2).
    apply sb_malloc_mono. exact BLE4. }
  pose proof SI6 as (RJ6 & _ & _ & _ & _ & RA6 & _).
  pose proof RJ6 as (HM6 & _).
  destruct (mr_model B _ LAWS L5 A5 m6 md5 HM6) as (Hh6 & Hl6 & _).
  eapply evt_SR_canon; [ | exact Hh6 | exact Hl6 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q6 : reg_get R6 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by exact R6_2.
    rewrite Q6.
    eapply scn_tail; [exact FR6 | lia]. }
  intros ms7 (can7 & -> & EQ7).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ7 eq_refl eq_refl) as (R7 & -> & X7).
  assert (E7_1 : getr R7 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X7 eq_refl); simp_regs; reflexivity).
  assert (E7_2 : getr R7 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X7 eq_refl); simp_regs; reflexivity).
  assert (E7_10 : getr R7 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X7 eq_refl); simp_regs; exact R6_8).
  assert (E7_11 : getr R7 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X7 eq_refl); simp_regs; reflexivity).
  assert (E7_12 : getr R7 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X7 eq_refl); simp_regs; reflexivity).
  assert (RP7 : regs_preserved regs R7).
  { apply (kept_ex_pres [2; 8; 9; 18; 19; 20]).
    - apply (kept_ex_trans _ regs R6 R7 RK6). kept_ex_tac X7.
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X7 eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  eapply SR_mono.
  { apply (sinv_answer (fx := fx) B API SEGS ERRNO_LOW AX CTX (ANSF fx) SLACK 12384 L A regs mem md O L5 A5 R7 m6 md5
             (rec_record R REC_CONNECT [x; canon line; y; z]) _ b
             (sb_malloc (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length x) + 1)) (Z.of_nat (length line) + 1))
                (Z.of_nat (length y) + 1)) (Z.of_nat (length z) + 1)) e 0x10417
             (REC_CONNECT, [x; canon line; y; z]) REC_MOD_HOST_SHAPE true PRE AK SI6 E7_1
             ltac:(unfold spZ; rewrite E7_2; reflexivity) RP7 E7_10 E7_11 ltac:(rewrite E7_12; reflexivity)).
    - intros _. apply mod_host_shape. exact RA6.
    - intros _ _. exact (ans_entry_record R REC_CONNECT [x; canon line; y; z] HN).
    - exact FRM.
    - exact BLE6.
    - eapply room_slots_mono; [| | exact ROOM].
      + apply sb_malloc_mono, sb_malloc_mono. exact BLE6.
      + unfold LMAX. lia. }
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  exists fx'', L', A', regs', mem', md', (fst (sup_connect_m R verb line port_a port_b)), O',
    (snd (sup_connect_m R verb line port_a port_b)), q.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact FK'|].
  split; [exact POST'|].
  repeat (split; [assumption|]). exact RES'.
Qed.

Lemma scn_d2 : forall L A regs mem md pa pb verb line port_a port_b R O b L3 A3 R3 m3 md3 Oc3,
  call_pre_t B API 12384 L A regs mem md -> getr regs 12 = Z_to_bv 64 pa -> getr regs 13 = Z_to_bv 64 pb ->
  str_arg B L A O (spZ regs) 12384 mem pa port_a -> str_arg B L A O (spZ regs) 12384 mem pb port_b ->
  ro_agree rsegs mem -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_connect_sizes verb line port_a port_b
                              (snd (sup_connect_m R verb line port_a port_b)))) (LMAX + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O L3 A3 m3 md3
    (rec_record R REC_CONNECT [sarg verb; canon line]) Oc3 b ->
  sb_le (sb_shift b A A3) (sb_malloc (sb_malloc b (Z.of_nat (length (sarg verb)) + 1)) (Z.of_nat (length line) + 1)) ->
  (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  getr R3 1 = Z_to_bv 64 0x16098 -> getr R3 2 = Z_to_bv 64 (spZ regs - 48) -> getr R3 4 = getr regs 4 ->
  getr R3 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R3 20 = Z_to_bv 64 (rec_entry G_REC REC_SC R + 8) ->
  getr R3 9 = getr regs 13 -> getr R3 10 = sel_null (getr regs 12) ->
  kept_ex [2; 8; 9; 18; 19; 20] regs R3 ->
  rw_cells rsegs m3 (spZ regs - 48)
    [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
     C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs m3 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 2)) ->
  SR rsegs (mkCfg (mkst R3 (Z_to_bv 64 0x15780) m3 (seg_rom rsegs)) md3)
    (sup_connect_ret B API L A regs mem md verb line port_a port_b R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK ANSF XSD.
  intros L A regs mem md pa pb verb line port_a port_b R O b L3 A3 R3 m3 md3 Oc3 PRE A2 A3' SA3 SA4 RA FRM ROOM SI3
    BLE3 HN HCODE E1 E2 E4 E8 E20 E9 E10 KE3 FR3 NA3.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof ROOM as ROOM0.
  change (snd (sup_connect_m R verb line port_a port_b)) with
    (snd (rec_answer (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b])
           (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true)) in ROOM.
  unfold sup_connect_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
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
  assert (SP3 : spZ R3 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & RA3 & F183 & RS3).
  pose proof RJ3 as (HM3 & _).
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L3 A3 m3 md3 _ Oc3 b pa port_a
              SI3 RA ltac:(unfold NULL_LIT; lia) SA3)
    as (s & slack & PW & SEL & S0 & BS & N0 & LX & AL & DJ & HOME & NRA).
  assert (SELW : sel_null (getr regs 12) = Z_to_bv 64 s)
    by (rewrite A2; unfold sel_null; rewrite unsigned_lit by lia; rewrite <- SEL; destruct (pa =? 0); reflexivity).
  set (x := sarg verb) in *. set (y := sarg port_a) in *.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof XSD as XS. unfold xstrdup_contract in XS. rewrite SEGS in XS.
  eapply SR_bind.
  { apply (XS L3 A3 R3 m3 md3 s y slack (sb_shift b A A3)).
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L3 A3 m3 md3 XSTRDUP_K R3 RJ3).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP3. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. lia.
      + rewrite E4. exact HTP.
    - rewrite E10. exact SELW.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact AL.
    - rewrite SP3. unfold XSTRDUP_K, ALLOC_STACK. destruct DJ as [D|D]; [left; lia | right; lia].
    - rewrite SP3. apply (scn_home_lower L3 A3 (bv_unsigned sp)); [lia | exact HOME].
    - exact RS3.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE3|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + lia.
    - exact RA3. }
  intros c4 RET.
  destruct RET as (L4 & A4 & R4 & m4 & md4 & p & -> & POST4 & A0' & NZ & AL16 & FB4 & BLK4 & BK4 & UB4 & BYT4 & SRC4
    & RA4 & GK4 & INI4 & RGN4 & RS4).
  rewrite SEGS in RA4, BYT4 |- *.
  pose proof POST4 as (PM4 & _ & _ & _ & _ & RP4 & _ & PF4 & _).
  pose proof FB4 as (FBa & FBb & FBc).
  assert (R4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E2).
  assert (R4_8' : reg_get R4 8 = Z_to_bv 64 e) by exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) E8).
  assert (R4_20' : reg_get R4 20 = Z_to_bv 64 (e + 8))
    by exact (eq_trans (RP4 20 ltac:(unfold callee_saved; lia)) E20).
  assert (POST4' : call_post_k B (aa_MR API) XSTRDUP_K L3 A3 R3 m3 md3 (fun a => p <= a < p + (Z.of_nat (length y) + 1))
                     L4 A4 R4 m4 md4).
  { pose proof POST4 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
    intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; lia]. }
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K L3 A3 R3 m3 md3 _ L4 A4 R4 m4 md4 (bv_unsigned sp - 48 + i)
                HM3 POST4 ltac:(lia) ltac:(rewrite SP3; unfold XSTRDUP_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (GK : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> mbyte rsegs m4 a = mbyte rsegs m3 a).
  { intros a Ha. destruct (GFACT a (glob_in a Ha)) as (Gi & _ & _ & Ge).
    rewrite SEGS in PF4.
    refine (proj1 (PF4 a (or_intror Gi) (GOWN L3 A3 m3 md3 a HM3 (glob_in a Ha)) (GOWN L4 A4 m4 md4 a PM4 (glob_in a Ha))
                    _ _)).
    - unfold scratch_k. rewrite SP3. unfold XSTRDUP_K, ALLOC_STACK.
      intros [H|H]; [unfold GLOB_LO, GLOB_N in Ha; lia | exact (Ge H)].
    - cbv beta. intros H. apply (FBc (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
  assert (NA4 : rw_cells rsegs m4 (e + 4) [C4 (Z_to_bv 64 2)]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|].
    apply (bytes_at_transfer rsegs m3); [exact NA3|]. intros i Hi. rewrite length_le4 in Hi.
    apply GK. unfold GLOB_LO, GLOB_N; lia. }
  destruct (glob_rw_cells m4 (e + 24) 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk4 EW4].
  assert (NA4n : rw_cells rsegs (normalize rsegs m4) (e + 4) [C4 (Z_to_bv 64 2)]).
  { apply rw_cells_normalize; [exact RA4 | exact NA4 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  assert (EW4n : rw_cells rsegs (normalize rsegs m4) (e + 24) [CB 8 junk4]).
  { apply rw_cells_normalize; [exact RA4 | exact EW4 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  destruct (ax_statics AX L4 A4 m4 md4 PM4) as (_ & (g4 & Hg4 & HWg4) & _).
  rewrite GRD, SEGS in HWg4.
  assert (F184 : f18_words rsegs m4).
  { apply (f18_words_after m3 m4 g4 F183); [|exact Hg4 | exact HWg4].
    intros i Hi. pose proof (GK4 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  destruct (mr_model B _ LAWS L4 A4 m4 md4 PM4) as (Hh4 & Hl4 & _).
  rewrite E1.
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite R4_8', R4_20'.
    eapply (evt_normalize rsegs); [exact WX | exact RA4 |].
    eapply scn_st3; [exact NA4n | exact EW4n]. }
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
                  (le4 (Z_to_bv 64 (Z.of_nat (length [x; canon line]) + 1)))).
  { apply cells_bytes_at in NA5. cbn [cells_bytes cbytes] in NA5. rewrite app_nil_r in NA5. exact NA5. }
  assert (BS5 : bytes_at rsegs m5 (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [x; canon line]))
                  (le8 (Z_to_bv 64 p))).
  { apply cells_bytes_at in EA5. cbn [cells_bytes cbytes] in EA5. rewrite app_nil_r in EA5.
    replace (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [x; canon line])) with (e + 24)
      by (rewrite EE; unfold CALL_OFF_ARGS; change (Z.of_nat (length [x; canon line])) with 2; lia).
    assert (Q : reg_get R4 10 = Z_to_bv 64 p) by exact A0'. rewrite Q in EA5. exact EA5. }
  pose proof (sinv_sarg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O L3 A3 m3 md3 R
                REC_CONNECT [x; canon line] Oc3 b XSTRDUP_K R3 L4 A4 R4 m4 md4 m5
                [(e + 4, e + 8); (e + 24, e + 32)] y p (Z.of_nat (length y) + 1)
                SI3 ltac:(cbn; lia) ltac:(rewrite SP3; unfold XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SP3; lia)
                POST4' MU5 WM5
                ltac:(intros a Ra Hm; cbn in Hm; rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS;
                      change (Z.of_nat (length [x; canon line])) with 2; lia)
                NZ FB4 BLK4 UB4 BK4 RGN4 BN5 BS5 BYT4 N0 LX ltac:(unfold LMAX in *; lia) INI4 RS4 RA4 F184) as SI5.
  cbn [app] in SI5.
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m4 m5 _ _ FR4 MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (BLE5 : sb_le (sb_shift b A A4)
                   (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length x) + 1)) (Z.of_nat (length line) + 1))
                      (Z.of_nat (length y) + 1))).
  { destruct BLK4 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A3 A4).
    rewrite <- (sb_shift_add (sb_shift b A A3) L3 A3 L4 A4 bl1 bl2 p _ EB1 EB2).
    apply sb_malloc_mono. exact BLE3. }
  apply (scn_d3 L A regs mem md pb verb line port_a port_b R O b L4 A4 R5 m5 md4 _ PRE A3' SA4 RA FRM ROOM0 SI5 BLE5
           HN HCODE).
  - rewrite (getr_of_eqv _ _ 1 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 2 X5 eq_refl). simp_regs. exact R4_2.
  - rewrite (getr_of_eqv _ _ 4 X5 eq_refl). simp_regs. exact (eq_trans (RP4 4 ltac:(unfold callee_saved; lia)) E4).
  - rewrite (getr_of_eqv _ _ 8 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 20 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 10 X5 eq_refl). simp_regs. f_equal.
    exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E9).
  - apply (kept_ex_trans _ regs R3 R5 KE3).
    apply (kept_ex_trans _ R3 R4 R5 (kept_ex_of_pres _ _ _ RP4)).
    kept_ex_tac X5.
  - exact FR5.
  - exact BN5.
Qed.

Lemma scn_line : forall L A regs mem md pl pa pb verb line port_a port_b R O b L2 A2 R2 m2 md2 Oc2,
  call_pre_t B API 12384 L A regs mem md -> getr regs 12 = Z_to_bv 64 pa -> getr regs 13 = Z_to_bv 64 pb ->
  str_arg B L A O (spZ regs) 12384 mem pl (Some line) ->
  str_arg B L A O (spZ regs) 12384 mem pa port_a -> str_arg B L A O (spZ regs) 12384 mem pb port_b ->
  ro_agree rsegs mem -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_connect_sizes verb line port_a port_b
                              (snd (sup_connect_m R verb line port_a port_b)))) (LMAX + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O L2 A2 m2 md2 (rec_record R REC_CONNECT [sarg verb]) Oc2 b ->
  sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length (sarg verb)) + 1)) ->
  (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  getr R2 1 = Z_to_bv 64 0x16078 -> getr R2 2 = Z_to_bv 64 (spZ regs - 48) -> getr R2 4 = getr regs 4 ->
  getr R2 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R2 20 = Z_to_bv 64 (rec_entry G_REC REC_SC R + 8) ->
  getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R2 11 = Z_to_bv 64 pl ->
  getr R2 9 = getr regs 13 -> getr R2 18 = getr regs 12 ->
  kept_ex [2; 8; 9; 18; 19; 20] regs R2 ->
  rw_cells rsegs m2 (spZ regs - 48)
    [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
     C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs m2 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 1)) ->
  SR rsegs (mkCfg (mkst R2 (Z_to_bv 64 0x15e64) m2 (seg_rom rsegs)) md2)
    (sup_connect_ret B API L A regs mem md verb line port_a port_b R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK ANSF XSD ARGL.
  intros L A regs mem md pl pa pb verb line port_a port_b R O b L2 A2 R2 m2 md2 Oc2 PRE A2' A3' SA2 SA3 SA4 RA FRM ROOM
    SI2 BLE2 HN HCODE E1 E2 E4 E8 E20 E10 E11 E9 E18 KE2 FR2 NA2.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof ROOM as ROOM0.
  change (snd (sup_connect_m R verb line port_a port_b)) with
    (snd (rec_answer (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b])
           (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true)) in ROOM.
  unfold sup_connect_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (ER : rec_entry G_REC REC_SC R mod 8 = 0 /\ REC_SC <= rec_entry G_REC REC_SC R /\
               rec_entry G_REC REC_SC R + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE, REC_SC, REC_SIZE.
      split; [|lia]. apply Z.mod_divide; [lia|]. exists (26539 + 7 * Z.of_nat (length (r_calls R))). lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. split; [reflexivity | lia]. }
  set (e := rec_entry G_REC REC_SC R) in *.
  assert (EB : 0x33d10 <= e /\ e + 56 <= 0x34108) by (unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE in ER; lia).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SP2 : spZ R2 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI2 as (RJ2 & _ & _ & _ & _ & RA2 & F182 & RS2).
  pose proof RJ2 as (HM2 & _).
  assert (Hp0 : pl <> 0) by exact (proj1 SA2).
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 _ Oc2 b pl (Some line)
              SI2 RA ltac:(unfold NULL_LIT; lia) SA2)
    as (s & slack & P0 & PS & S0 & BS & N0 & LX & ALN & DJ & HOME & NRA).
  change (sarg (Some line)) with line in BS, N0, LX, ALN, DJ, HOME, NRA.
  assert (ES : s = pl) by (rewrite <- PS; destruct (Z.eqb_spec pl 0); [contradiction | reflexivity]).
  clear PS. subst s.
  set (x := sarg verb) in *.
  pose proof ARGL as AL. unfold arg_line_contract in AL. rewrite SEGS in AL.
  eapply SR_bind.
  { apply (AL L2 A2 R2 m2 md2 e pl 1 line slack (sb_shift b A A2)).
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m2 md2 ARG_LINE_K R2 RJ2).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP2. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
      + rewrite SP2. unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
      + rewrite SP2. lia.
      + rewrite E4. exact HTP.
    - exact E10.
    - exact E11.
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
    - rewrite SP2. unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. destruct DJ as [D|D]; [left; lia | right; lia].
    - rewrite SP2. apply (scn_home_lower L2 A2 (bv_unsigned sp)); [lia | exact HOME].
    - unfold iv_apart. apply (scn_nra_apart pl _ e (e + CALL_SIZE)).
      + intros a Ha. apply NRA. rewrite length_app. cbn [length]. lia.
      + exact (proj1 (proj2 ER)).
      + exact (proj2 (proj2 ER)).
      + unfold CALL_SIZE. lia.
      + lia.
    - exact RS2.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE2|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + unfold LMAX in *. lia.
    - exact RA2. }
  intros c3 (L3 & A3 & R3 & m3 & md3 & -> & BK3 & UB3 & _ & RA3 & GK3 & RGN3 & ALT3).
  destruct ALT3 as [(H6 & _)|(_ & p2 & POST3 & Hp2 & _ & FB3 & BLK3 & BN3 & BS3 & BX3 & INI3 & RS3)]; [lia|].
  rewrite SEGS in RA3, BN3, BS3, BX3 |- *.
  pose proof POST3 as (PM3 & _ & _ & _ & _ & RP3 & _).
  destruct (ax_statics AX L3 A3 m3 md3 PM3) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F183 : f18_words rsegs m3).
  { apply (f18_words_after m2 m3 g F182); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK3 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 R
                REC_CONNECT [x] Oc2 b ARG_LINE_K R2 _ L3 A3 R3 m3 md3 (canon line) p2 (Z.of_nat (length line) + 1)
                SI2 ltac:(cbn; lia) ltac:(rewrite SP2; unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK; lia)
                ltac:(rewrite SP2; lia) POST3
                ltac:(intros a Ha; cbv beta in Ha; change (Z.of_nat (length [x])) with 1; lia)
                Hp2 FB3 BLK3 UB3 BK3 RGN3 BN3 BS3 BX3 (canon_no0 line N0)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                INI3 RS3 RA3 F183) as SI3.
  cbn [app] in SI3.
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi.
    destruct FB3 as (_ & FBb & _).
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_LINE_K L2 A2 R2 m2 md2 _ L3 A3 R3 m3 md3 (bv_unsigned sp - 48 + i)
                HM2 POST3 ltac:(lia) ltac:(rewrite SP2; unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK; lia))
      as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (R3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) E2).
  assert (R3_8 : getr R3 8 = Z_to_bv 64 e) by exact (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) E8).
  assert (BLE3 : sb_le (sb_shift b A A3)
                   (sb_malloc (sb_malloc b (Z.of_nat (length x) + 1)) (Z.of_nat (length line) + 1))).
  { destruct BLK3 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A2 A3).
    rewrite <- (sb_shift_add (sb_shift b A A2) L2 A2 L3 A3 bl1 bl2 p2 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE2. }
  assert (NA3 : rw_cells rsegs m3 (e + 4) [C4 (Z_to_bv 64 2)]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|]. exact BN3. }
  destruct (mr_model B _ LAWS L3 A3 m3 md3 PM3) as (Hh3 & Hl3 & _).
  rewrite E1.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q8 : reg_get R3 8 = Z_to_bv 64 e) by exact R3_8.
    rewrite Q8.
    eapply scn_mid2. exact NA3. }
  intros ms4 (can4 & (b41 & ->) & EQ4).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
  apply (scn_d2 L A regs mem md pa pb verb line port_a port_b R O b L3 A3 R4 m3 md3 _ PRE A2' A3' SA3 SA4 RA FRM ROOM0
           SI3 BLE3 HN HCODE).
  - rewrite (getr_of_eqv _ _ 1 X4 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 2 X4 eq_refl). simp_regs. exact R3_2.
  - rewrite (getr_of_eqv _ _ 4 X4 eq_refl). simp_regs. exact (eq_trans (RP3 4 ltac:(unfold callee_saved; lia)) E4).
  - rewrite (getr_of_eqv _ _ 8 X4 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 20 X4 eq_refl). simp_regs. exact (eq_trans (RP3 20 ltac:(unfold callee_saved; lia)) E20).
  - rewrite (getr_of_eqv _ _ 9 X4 eq_refl). simp_regs. exact (eq_trans (RP3 9 ltac:(unfold callee_saved; lia)) E9).
  - rewrite (getr_of_eqv _ _ 10 X4 eq_refl). simp_regs. f_equal.
    exact (eq_trans (RP3 18 ltac:(unfold callee_saved; lia)) E18).
  - apply (kept_ex_trans _ regs R2 R4 KE2).
    apply (kept_ex_trans _ R2 R3 R4 (kept_ex_of_pres _ _ _ RP3)).
    kept_ex_tac X4.
  - exact FR3.
  - exact BN3.
Qed.

Lemma scn_d1 : forall L A regs mem md pv pl pa pb verb line port_a port_b R O b Lc Ac R1 m1 md1 Oc,
  call_pre_t B API 12384 L A regs mem md ->
  getr regs 10 = Z_to_bv 64 pv -> getr regs 11 = Z_to_bv 64 pl ->
  getr regs 12 = Z_to_bv 64 pa -> getr regs 13 = Z_to_bv 64 pb ->
  str_arg B L A O (spZ regs) 12384 mem pv verb -> str_arg B L A O (spZ regs) 12384 mem pl (Some line) ->
  str_arg B L A O (spZ regs) 12384 mem pa port_a -> str_arg B L A O (spZ regs) 12384 mem pb port_b ->
  ro_agree rsegs mem -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_connect_sizes verb line port_a port_b
                              (snd (sup_connect_m R verb line port_a port_b)))) (LMAX + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O Lc Ac m1 md1 (rec_record R REC_CONNECT []) Oc b ->
  sb_le (sb_shift b A Ac) b -> (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  getr R1 1 = Z_to_bv 64 0x16050 -> getr R1 2 = Z_to_bv 64 (spZ regs - 48) -> getr R1 4 = getr regs 4 ->
  getr R1 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R1 9 = getr regs 13 -> getr R1 18 = getr regs 12 -> getr R1 19 = getr regs 11 ->
  getr R1 10 = sel_null (getr regs 10) ->
  kept_ex [2; 8; 9; 18; 19; 20] regs R1 ->
  rw_cells rsegs m1 (spZ regs - 48)
    [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
     C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs m1 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 0)) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15780) m1 (seg_rom rsegs)) md1)
    (sup_connect_ret B API L A regs mem md verb line port_a port_b R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK ANSF XSD ARGL.
  intros L A regs mem md pv pl pa pb verb line port_a port_b R O b Lc Ac R1 m1 md1 Oc PRE A0 A1 A2 A3 SA1 SA2 SA3 SA4
    RA FRM ROOM SI1 BLE1 HN HCODE E1 E2 E4 E8 E9 E18 E19 E10 KE1 FR1 NA1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof ROOM as ROOM0.
  change (snd (sup_connect_m R verb line port_a port_b)) with
    (snd (rec_answer (rec_record R REC_CONNECT [sarg verb; canon line; sarg port_a; sarg port_b])
           (REC_CONNECT, [sarg verb; canon line; sarg port_a; sarg port_b]) REC_MOD_HOST_SHAPE true)) in ROOM.
  unfold sup_connect_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
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
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O Lc Ac m1 md1 _ Oc b pv verb
              SI1 RA ltac:(unfold NULL_LIT; lia) SA1)
    as (s & slack & PW & SEL & S0 & BS & N0 & LX & AL & DJ & HOME & NRA).
  assert (SELW : sel_null (getr regs 10) = Z_to_bv 64 s)
    by (rewrite A0; unfold sel_null; rewrite unsigned_lit by lia; rewrite <- SEL; destruct (pv =? 0); reflexivity).
  set (x := sarg verb) in *.
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
    - rewrite SP1. apply (scn_home_lower Lc Ac (bv_unsigned sp)); [lia | exact HOME].
    - exact RS1.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE1|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + lia.
    - exact RA1. }
  intros c2 RET.
  destruct RET as (L2 & A2' & R2 & m2 & md2 & p & -> & POST2 & A0' & NZ & AL16 & FB2 & BLK2 & BK2 & UB2 & BYT2 & SRC2
    & RA2 & GK2 & INI2 & RGN2 & RS2).
  rewrite SEGS in RA2, BYT2 |- *.
  pose proof POST2 as (PM2 & _ & _ & _ & _ & RP2 & _ & PF2 & _).
  pose proof FB2 as (FBa & FBb & FBc).
  assert (R2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E2).
  assert (R2_8' : reg_get R2 8 = Z_to_bv 64 e) by exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E8).
  assert (POST2' : call_post_k B (aa_MR API) XSTRDUP_K Lc Ac R1 m1 md1 (fun a => p <= a < p + (Z.of_nat (length x) + 1))
                     L2 A2' R2 m2 md2).
  { pose proof POST2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
    intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; lia]. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K Lc Ac R1 m1 md1 _ L2 A2' R2 m2 md2 (bv_unsigned sp - 48 + i)
                HM1 POST2 ltac:(lia) ltac:(rewrite SP1; unfold XSTRDUP_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (GK : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> mbyte rsegs m2 a = mbyte rsegs m1 a).
  { intros a Ha. destruct (GFACT a (glob_in a Ha)) as (Gi & _ & _ & Ge).
    rewrite SEGS in PF2.
    refine (proj1 (PF2 a (or_intror Gi) (GOWN Lc Ac m1 md1 a HM1 (glob_in a Ha)) (GOWN L2 A2' m2 md2 a PM2 (glob_in a Ha))
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
  destruct (ax_statics AX L2 A2' m2 md2 PM2) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F182 : f18_words rsegs m2).
  { apply (f18_words_after m1 m2 g F181); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK2 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  destruct (mr_model B _ LAWS L2 A2' m2 md2 PM2) as (Hh2 & Hl2 & _).
  rewrite E1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite R2_8'.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply scn_st1; [exact NAn | exact EWn]. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (b32 & m3n & -> & MU3n & WM3n & NA3n & EA3n).
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
    assert (Q : reg_get R2 10 = Z_to_bv 64 p) by exact A0'. rewrite Q in EA3. exact EA3. }
  pose proof (sinv_sarg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O Lc Ac m1 md1 R
                REC_CONNECT [] Oc b XSTRDUP_K R1 L2 A2' R2 m2 md2 m3 [(e + 4, e + 16)] x p (Z.of_nat (length x) + 1)
                SI1 ltac:(cbn; lia) ltac:(rewrite SP1; unfold XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SP1; lia)
                POST2' MU3 WM3
                ltac:(intros a Ra Hm; cbn in Hm; rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS; cbn [length Z.of_nat]; lia)
                NZ FB2 BLK2 UB2 BK2 RGN2 BN3 BS3 BYT2 N0 LX ltac:(unfold LMAX in *; lia) INI2 RS2 RA2 F182) as SI3.
  cbn [app] in SI3.
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 48)
                  [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                   C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (BLE2 : sb_le (sb_shift b A A2') (sb_malloc b (Z.of_nat (length x) + 1))).
  { destruct BLK2 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A Ac A2').
    rewrite <- (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2' bl1 bl2 p _ EB1 EB2).
    apply sb_malloc_mono. exact BLE1. }
  apply (scn_line L A regs mem md pl pa pb verb line port_a port_b R O b L2 A2' R3 m3 md2 _ PRE A2 A3 SA2 SA3 SA4 RA FRM
           ROOM0 SI3 BLE2 HN HCODE).
  - rewrite (getr_of_eqv _ _ 1 X3 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 2 X3 eq_refl). simp_regs. exact R2_2.
  - rewrite (getr_of_eqv _ _ 4 X3 eq_refl). simp_regs. exact (eq_trans (RP2 4 ltac:(unfold callee_saved; lia)) E4).
  - rewrite (getr_of_eqv _ _ 8 X3 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 20 X3 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 10 X3 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 11 X3 eq_refl). simp_regs.
    exact (eq_trans (RP2 19 ltac:(unfold callee_saved; lia)) (eq_trans E19 A1)).
  - rewrite (getr_of_eqv _ _ 9 X3 eq_refl). simp_regs. exact (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) E9).
  - rewrite (getr_of_eqv _ _ 18 X3 eq_refl). simp_regs. exact (eq_trans (RP2 18 ltac:(unfold callee_saved; lia)) E18).
  - apply (kept_ex_trans _ regs R1 R3 KE1).
    apply (kept_ex_trans _ R1 R2 R3 (kept_ex_of_pres _ _ _ RP2)).
    kept_ex_tac X3.
  - exact FR3.
  - exact BN3.
Qed.

Theorem sup_connect_holds : sup_connect_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK RCF ANSF XSD ARGL.
  unfold sup_connect_contract.
  intros L A regs mem md pv pl pa pb verb line port_a port_b R O b PRE A0 A1 A2 A3 SA1 SA2 SA3 SA4 GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_CONNECT_K in PRE, PRK, HCEIL, HWS, SA1, SA2, SA3, SA4.
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
      eapply scn_seg_lt; [exact ST | lia | lia | exact NC | exact Hn | exact EW]. }
    intros ms1 (can1 & (b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1 & EN1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    pose proof (sinv_record_lt B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                  REC_CONNECT SI0 Hn ltac:(unfold REC_FN_COUNT, REC_CONNECT; lia) MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EN1) as SI1.
    pose proof EN1 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
    apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
    apply (scn_d1 L A regs mem md pv pl pa pb verb line port_a port_b R O b L A R1 m1 md O PRE A0 A1 A2 A3
             SA1 SA2 SA3 SA4 RA FRM ROOM SI1 ltac:(rewrite sb_shift_refl; apply sb_le_refl) ltac:(lia) HCODE).
    + rewrite (getr_of_eqv _ _ 1 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 4 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 8 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 9 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 18 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 19 X1 eq_refl). simp_regs. reflexivity.
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
      eapply scn_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16014) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_9 : getr R1 9 = getr regs 13) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_18 : getr R1 18 = getr regs 12) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_19 : getr R1 19 = getr regs 11) by (rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_20 : getr R1 20 = getr regs 10) by (rewrite (getr_of_eqv _ _ 20 X1 eq_refl); simp_regs; reflexivity).
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
                      [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                       C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
        apply FRK. rewrite SP1. lia. }
      destruct (glob_rw_cells m' 0x33d10 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
      eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of.
        assert (Q8 : reg_get regs' 8 = Z_to_bv 64 0x33d10) by exact R8'.
        rewrite Q8.
        eapply scn_ret16. exact EW. }
      intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                  _ REC_CONNECT POST ltac:(unfold REC_FN_COUNT, REC_CONNECT; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
                      [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
                       C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply (rw_cells_transport rsegs _ m' m2 _ _ FR' MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
        repeat split; lia. }
      pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
      apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
      rewrite sb_shift_refl in BLE.
      apply (scn_d1 L A regs mem md pv pl pa pb verb line port_a port_b R O b L' A' R2 m2 md' Oc' PRE A0 A1 A2 A3
               SA1 SA2 SA3 SA4 RA FRM ROOM SI2 BLE ltac:(lia) HCODE).
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
      * rewrite (getr_of_eqv _ _ 19 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 19 ltac:(unfold callee_saved; lia)) E1_19).
      * rewrite (getr_of_eqv _ _ 10 X2 eq_refl). simp_regs. f_equal.
        exact (eq_trans (RP' 20 ltac:(unfold callee_saved; lia)) E1_20).
      * apply (kept_ex_trans _ regs R1 R2); [kept_ex_tac X1|].
        apply (kept_ex_trans _ R1 regs' R2 (kept_ex_of_pres _ _ _ RP')). kept_ex_tac X2.
      * exact FR2.
      * rewrite (rec_entry_full G_REC REC_SC R H16).
        replace (REC_SC + CALL_OFF_NARGS) with (0x33d10 + Z.of_nat 4) by (unfold REC_SC, CALL_OFF_NARGS; lia).
        exact EA.
Qed.

End P.
