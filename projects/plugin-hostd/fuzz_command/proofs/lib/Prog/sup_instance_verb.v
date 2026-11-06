(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its addresses and numbers changed; 533 of its 949 lines of code are new or changed and 2326 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecStub rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strspn_c strcspn_c.
Import ListNotations.
Open Scope Z_scope.

Lemma siv_pre_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n))
                     a0 b0 b1 b2 a3 a4 a5 a6 a7 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1638c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16330) fc None m (seg_rom rsegs)).
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

Lemma siv_rec :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (jk : list byte),
  rw_cells rsegs m e [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x163a0) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1
                     (Z_to_bv 64 e) s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15e64) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 7); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1638c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e jk EW.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 7); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  do 3 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma siv_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat) (jk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 jk] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x163a0) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a0 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a0
                     b2 a3 a4 a5 a6 a7 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15e64) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 7); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16330) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n jk ST LO LO2 NC Hn EW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply siv_pre_lt; [exact ST | exact LO | exact LO2 | exact NC | exact Hn] |].
  intros ms1 (b0 & b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1).
  assert (EW1 : rw_cells rsegs m1 (0x33d58 + 56 * Z.of_nat n) [CB 8 jk]).
  { apply (rw_cells_transport rsegs [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m1 _ _ EW MU1 WM1).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  eapply evt_cut; [eapply siv_rec; exact EW1 |].
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

Lemma siv_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x1636c) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     a0 (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) b2 a3 a4 a5 a6 a7
                     a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16330) fc None m (seg_rom rsegs)).
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

Lemma siv_ret16 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (jk : list byte),
  rw_cells rsegs m 0x33d10 [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x163a0) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1
                     (Z_to_bv 64 0x33d10) s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15e64) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 7); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1636c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m jk EW.
  step.
  eapply siv_rec. exact EW.
Qed.

Lemma siv_mid :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x163ac) sp gp tp t0 t1 t2 s0 s1 s0 s2 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15b1c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x163a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step.
  apply evt_done. reflexivity.
Qed.

Lemma siv_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' s20 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' s0 a0 (Z_to_bv 64 1)
                                    a3 a4 a5 a6 a7 s20 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15bc8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x163dc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' s20 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 9 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Definition siv_set : list byte := [Z_to_bv 8 32; Z_to_bv 8 9].

Lemma siv_set_no0 : no0 siv_set.
Proof. apply no0_nz. vm_compute. reflexivity. Qed.

Lemma siv_set_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1064c (siv_set ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. apply rom_chk_bytes; [exact (ro_agree_of_inv m MI) | lia | cbn; lia | vm_compute; reflexivity].
Qed.

Lemma siv_gl : length g_shapes_bytes = 448%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma siv_in_set : forall x, in_set siv_set x = is_sep x.
Proof.
  intros x. unfold in_set, siv_set, is_sep. cbn [existsb]. rewrite orb_false_r.
  change (bv_unsigned (Z_to_bv 8 32)) with 32. change (bv_unsigned (Z_to_bv 8 9)) with 9.
  rewrite (Z.eqb_sym 32), (Z.eqb_sym 9). reflexivity.
Qed.

Lemma siv_cspn_cons : forall x s, cspn_len siv_set (x :: s) = if is_sep x then O else S (cspn_len siv_set s).
Proof. intros x s. cbn [cspn_len]. rewrite <- siv_in_set. reflexivity. Qed.

Lemma siv_spn_le : forall s, (spn_len siv_set s <= length s)%nat.
Proof. intros s. induction s as [|x s IH]; cbn [spn_len length]; [lia|]. destruct (in_set siv_set x); lia. Qed.

Lemma siv_cspn_le : forall s, (cspn_len siv_set s <= length s)%nat.
Proof.
  intros s. induction s as [|x s IH]; [cbn [cspn_len length]; lia|].
  rewrite siv_cspn_cons. destruct (is_sep x); cbn [length]; lia.
Qed.

Lemma siv_words_skip : forall T, words_go [] T = words_go [] (skipn (spn_len siv_set T) T).
Proof.
  induction T as [|x T IH]; [reflexivity|].
  cbn [spn_len]. rewrite siv_in_set. destruct (is_sep x) eqn:E.
  - cbn [skipn]. rewrite <- IH. cbn [words_go]. rewrite E. reflexivity.
  - reflexivity.
Qed.

Lemma siv_words_head : forall T cur, cur <> [] ->
  exists rest, words_go cur T = (rev cur ++ firstn (cspn_len siv_set T) T) :: rest.
Proof.
  induction T as [|x T IH]; intros cur Hc.
  - destruct cur as [|y cur]; [exfalso; apply Hc; reflexivity|]. exists []. cbn [words_go cspn_len firstn].
    rewrite app_nil_r. reflexivity.
  - rewrite siv_cspn_cons. cbn [words_go]. destruct (is_sep x).
    + destruct cur as [|y cur]; [exfalso; apply Hc; reflexivity|]. exists (words_go [] T). cbn [firstn].
      rewrite app_nil_r. reflexivity.
    + destruct (IH (x :: cur) ltac:(discriminate)) as (rest & E). exists rest. rewrite E. cbn [rev firstn].
      rewrite <- app_assoc. reflexivity.
Qed.

Lemma siv_first_word : forall T,
  firstn (cspn_len siv_set (skipn (spn_len siv_set T) T)) (skipn (spn_len siv_set T) T) = first_word T.
Proof.
  intros T. unfold first_word, words. rewrite (siv_words_skip T).
  assert (H : skipn (spn_len siv_set T) T = [] \/
              exists x T', skipn (spn_len siv_set T) T = x :: T' /\ is_sep x = false).
  { clear. induction T as [|x T IH]; [left; reflexivity|].
    cbn [spn_len]. rewrite siv_in_set. destruct (is_sep x) eqn:E.
    - exact IH.
    - right. exists x, T. split; [reflexivity | exact E]. }
  destruct H as [H | (x & T' & H & E)]; rewrite H; [reflexivity|].
  rewrite siv_cspn_cons, E. cbn [words_go]. rewrite E.
  destruct (siv_words_head T' [x] ltac:(discriminate)) as (rest & H2). rewrite H2. reflexivity.
Qed.

Ltac siv_lits :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

Ltac siv_tr H MU :=
  apply (bytes_at_transport rsegs _ _ _ _ _ H MU); cbn [disjoint_from];
  rewrite ?length_app, ?length_skipn, ?length_le8, ?siv_gl; cbn [length];
  unfold G_SHAPES, SSP_GOT, SSP_GUARD in *; repeat split; lia.

Lemma siv_after : strspn_contract -> strcspn_contract -> rec_shape_of_contract ->
  forall ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo p : Z) (line : list byte) (sp0 ra0 s00 s10' s20 can : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0] ->
  stk rsegs m lo (bv_unsigned sp0 - 32) -> lo + 128 <= bv_unsigned sp0 -> 0x100000 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  bytes_at rsegs m SSP_GOT (le8 (Z_to_bv 64 SSP_GUARD)) -> bytes_at rsegs m SSP_GUARD (le8 can) ->
  bytes_at rsegs m p (line ++ [Z_to_bv 8 0]) -> no0 line ->
  p + Z.of_nat (length line) + 1 <= lo \/ bv_unsigned sp0 <= p ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s00 s10' s0 (Z_to_bv 64 (shape_find shape_rows (first_word line)))
                     (Z_to_bv 64 1) a3' a4' a5' a6' a7' s20 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x15bc8) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp0 - 128, bv_unsigned sp0 - 32)] m m' /\ wmono rsegs m m')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x163ac) fc None m (seg_rom rsegs)).
Proof.
  intros SSPN SCSPN RSO ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p line sp0 ra0 s00 s10' s20 can FR ST LO LO2 GS MI GOT GRD LB N0 DJ.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ LB) as PB. rewrite length_app in PB. cbn [length] in PB.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 - 32)) = bv_unsigned sp0 - 32) by (apply unsigned_lit; lia).
  do 5 step.
  eapply evt_cut.
  { eapply (SSPN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ line siv_set lo can).
    - siv_lits. exact LB.
    - exact N0.
    - siv_lits. exact (siv_set_at m MI).
    - exact siv_set_no0.
    - exact GOT.
    - exact GRD.
    - siv_lits. exact ST.
    - siv_lits. lia.
    - siv_lits. lia.
    - left. siv_lits. unfold siv_set. cbn [length]. lia.
    - left. unfold SSP_GOT. lia.
    - left. unfold SSP_GUARD. lia.
    - exact MI. }
  intros ms1 PO. unfold strspn_post in PO.
  destruct PO as (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & -> & MU1
    & WM1 & MI1 & ST1).
  rewrite SPU in MU1, ST1.
  rewrite (ret_pc_even 0x163c0) by lia.
  set (k := spn_len siv_set line) in *.
  pose proof (siv_spn_le line) as Hk. fold k in Hk.
  pose proof (length_skipn k line) as LSK.
  assert (LB1 : bytes_at rsegs m1 p (line ++ [Z_to_bv 8 0])) by siv_tr LB MU1.
  assert (GS1 : bytes_at rsegs m1 G_SHAPES g_shapes_bytes) by siv_tr GS MU1.
  assert (GOT1 : bytes_at rsegs m1 SSP_GOT (le8 (Z_to_bv 64 SSP_GUARD))) by siv_tr GOT MU1.
  assert (GRD1 : bytes_at rsegs m1 SSP_GUARD (le8 can)) by siv_tr GRD MU1.
  assert (SUF : bytes_at rsegs m1 (p + Z.of_nat k) (skipn k line ++ [Z_to_bv 8 0])).
  { pose proof LB1 as FU. rewrite <- (firstn_skipn k line), <- app_assoc in FU.
    apply bytes_at_app in FU. destruct FU as [_ FU]. rewrite firstn_length_le in FU by lia. exact FU. }
  assert (NZ2 : ~ In (Z_to_bv 8 0) (skipn k line)).
  { intros HIn. apply N0. rewrite <- (firstn_skipn k line). apply in_or_app. right. exact HIn. }
  do 4 step.
  eapply evt_cut.
  { eapply (SCSPN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (skipn k line) [] siv_set lo can).
    - siv_lits. exact SUF.
    - exact NZ2.
    - intros HL. unfold siv_set in HL. cbn [length] in HL. lia.
    - siv_lits. exact (siv_set_at m1 MI1).
    - exact siv_set_no0.
    - exact GOT1.
    - exact GRD1.
    - siv_lits. exact ST1.
    - siv_lits. lia.
    - siv_lits. cbn [length]. rewrite LSK. lia.
    - left. siv_lits. unfold siv_set. cbn [length]. lia.
    - left. unfold CSPN_SSP_GOT. lia.
    - left. unfold CSPN_SSP_GUARD. lia.
    - exact MI1. }
  intros ms2 PO. unfold strcspn_post in PO.
  destruct PO as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & -> & MU2
    & WM2 & MI2 & ST2).
  rewrite SPU in MU2, ST2.
  rewrite (ret_pc_even 0x163d0) by lia.
  set (c := cspn_len siv_set (skipn k line)) in *.
  pose proof (siv_cspn_le (skipn k line)) as Hc. fold c in Hc. rewrite LSK in Hc.
  assert (SUF2 : bytes_at rsegs m2 (p + Z.of_nat k) (skipn k line ++ [Z_to_bv 8 0])) by siv_tr SUF MU2.
  assert (GS2 : bytes_at rsegs m2 G_SHAPES g_shapes_bytes) by siv_tr GS1 MU2.
  do 3 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := firstn c (skipn k line)).
    - exact MI2.
    - siv_lits. exact ST2.
    - siv_lits. unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS2.
    - left. siv_lits. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - siv_lits. rewrite firstn_length_le by lia. reflexivity.
    - intros _. siv_lits. split.
      + pose proof SUF2 as FU. rewrite <- (firstn_skipn c (skipn k line)), <- app_assoc in FU.
        apply bytes_at_app in FU. exact (proj1 FU).
      + unfold REC_SHAPE_OF_FRAME. lia. }
  intros ms3 (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 & -> & MU3 & WM3
    & MI3 & ST3).
  rewrite SPU in MU3. unfold REC_SHAPE_OF_FRAME in MU3.
  rewrite (ret_pc_even 0x163dc) by lia.
  assert (FW : firstn c (skipn k line) = first_word line) by (unfold c, k; apply siv_first_word).
  rewrite FW.
  assert (MU : munch [(bv_unsigned sp0 - 128, bv_unsigned sp0 - 32)] m m3).
  { apply (munch_trans _ m m1 m3); [|apply (munch_trans _ m1 m2 m3)].
    - refine (munch_weaken _ _ _ _ _ MU1). intros x (H1 & _). split; [lia | exact I].
    - refine (munch_weaken _ _ _ _ _ MU2). intros x (H1 & _). split; [lia | exact I].
    - refine (munch_weaken _ _ _ _ _ MU3). intros x (H1 & _). split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM1 (wmono_trans rsegs _ _ _ WM2 WM3)) as WM.
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0]).
  { apply (rw_cells_transport rsegs _ m m3 _ _ FR MU WM). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_cut; [eapply siv_tail; [exact FR3 | lia] |].
  intros ms4 ->. apply evt_done.
  exists m3, t0c, t1c, t2c, a3c, a4c, a5c, a6c, a7c, t3c, t4c, t5c, t6c.
  split; [reflexivity|]. split; [exact MU | exact WM].
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import sup_instance_verb_c.

Fixpoint siv_rows_ok (rows : list (Z * String.string * Z)) (tab : list (list byte * list byte)) : bool :=
  match rows, tab with
  | [], [] => true
  | (_, nm, rp) :: rows', (x, y) :: tab' =>
      bl_eqb x (str_bytes nm) && (0 <=? rp) && (rp + Z.of_nat (length y) + 1 <=? 2 ^ 64) &&
      rom_chk rp (y ++ [Z_to_bv 8 0]) && siv_rows_ok rows' tab'
  | _, _ => false
  end.

Lemma siv_rows_true : siv_rows_ok shape_rows shape_table = true.
Proof. vm_compute. reflexivity. Qed.

Lemma siv_rows_find : forall v rows tab, siv_rows_ok rows tab = true ->
  (shape_find rows v = SHAPE_LIT /\ shape_lookup tab v = REC_MOD_HOST_SHAPE) \/
  (0 <= shape_find rows v /\ shape_find rows v + Z.of_nat (length (shape_lookup tab v)) + 1 <= 2 ^ 64 /\
   rom_chk (shape_find rows v) (shape_lookup tab v ++ [Z_to_bv 8 0]) = true).
Proof.
  intros v rows. induction rows as [|[[na nm] rp] rows IH]; intros tab H;
    destruct tab as [|[x y] tab]; cbn [siv_rows_ok] in H; try discriminate H.
  - left. split; reflexivity.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
    apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    cbn [shape_find shape_lookup].
    assert (E : map bv_unsigned x = map bv_unsigned (str_bytes nm)).
    { revert H0. unfold bl_eqb.
      destruct (list_eq_dec Z.eq_dec (map bv_unsigned x) (map bv_unsigned (str_bytes nm))) as [E|E];
        intros H0; [exact E | discriminate H0]. }
    assert (EQ : bl_eqb x v = bytes_eqb (str_bytes nm) v).
    { unfold bl_eqb, bytes_eqb.
      destruct (list_eq_dec Z.eq_dec (map bv_unsigned x) (map bv_unsigned v)) as [E1|E1];
        destruct (list_eq_dec Z.eq_dec (map bv_unsigned (str_bytes nm)) (map bv_unsigned v)) as [E2|E2];
        try reflexivity; exfalso; congruence. }
    rewrite EQ. destruct (bytes_eqb (str_bytes nm) v).
    + right. split; [lia|]. split; [lia | exact H3].
    + exact (IH tab H4).
Qed.

Lemma siv_ans_shape : forall m v, ro_agree rsegs m -> ans_shape rsegs m (shape_find shape_rows v) (shape_of v).
Proof.
  intros m v RA. destruct (shape_of_facts v) as (FT & _ & L78 & N0). unfold shape_of in *.
  destruct (siv_rows_find v shape_rows shape_table siv_rows_true) as [(E1 & E2) | (H0 & H1 & H2)].
  - rewrite E1, E2. exact (mod_host_shape m RA).
  - apply ans_shape_chk; [exact RA | lia | lia | exact H2 | exact N0 | unfold LMAX; lia | exact FT].
Qed.

Lemma siv_nra_apart : forall s Ln lo hi, (forall a, s <= a < s + Ln -> ~ rec_area a) ->
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
Hypothesis ARGL : arg_line_contract B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis SSPN : strspn_contract.
Hypothesis SCSPN : strcspn_contract.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Lemma siv_home_lower : forall L A sp1 sp2 s n, sp2 <= sp1 -> str_home B L A sp1 s n -> str_home B L A sp2 s n.
Proof.
  intros L A sp1 sp2 s n H [H1|[H1|H1]]; [left; lia | right; left; exact H1 | right; right; exact H1].
Qed.

Lemma siv_arg : forall L A regs mem md pl ledger line R O b L2 A2 R2 m2 md2 Oc2,
  call_pre_t B API 12384 L A regs mem md ->
  getr regs 11 = Z_to_bv 64 ledger -> -2 ^ 31 <= ledger < 2 ^ 31 ->
  str_arg B L A O (spZ regs) 12384 mem pl (Some line) -> ro_agree rsegs mem ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_instance_verb_sizes line ledger (snd (sup_instance_verb_m R line ledger))))
    (LMAX + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O L2 A2 m2 md2 (rec_record R REC_INSTANCE_VERB [canon line]) Oc2 b ->
  sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length line) + 1)) ->
  (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  getr R2 2 = Z_to_bv 64 (spZ regs - 32) -> getr R2 4 = getr regs 4 ->
  getr R2 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R2 9 = Z_to_bv 64 pl ->
  getr R2 18 = getr regs 11 ->
  kept_ex [2; 8; 9; 18] regs R2 ->
  rw_cells rsegs m2 (spZ regs - 32)
    [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs m2 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 1)) ->
  SR rsegs (mkCfg (mkst R2 (Z_to_bv 64 0x163a0) m2 (seg_rom rsegs)) md2)
    (sup_instance_verb_ret B API L A regs mem md line ledger R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK ANSF ARGI RSO SSPN SCSPN RIMG RFREE.
  intros L A regs mem md pl ledger line R O b L2 A2 R2 m2 md2 Oc2 PRE A1 HLD SA RA GS FRM ROOM SI2 BLE2 HN HCODE
    R2_2 R2_4 R2_8 R2_9 R2_18 KE2 FR2 NA2.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  change (snd (sup_instance_verb_m R line ledger)) with
    (snd (rec_answer (rec_record R REC_INSTANCE_VERB [canon line; dec ledger])
           (REC_INSTANCE_VERB, [canon line; dec ledger]) (shape_of (first_word line)) true)) in ROOM.
  unfold sup_instance_verb_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_INSTANCE_VERB [canon line; dec ledger])
                  (REC_INSTANCE_VERB, [canon line; dec ledger]) (shape_of (first_word line)) true)) <= 78)%nat).
  { pose proof (stub_len R REC_INSTANCE_VERB [canon line; dec ledger] (shape_of (first_word line)) true HCODE) as H.
    destruct (shape_of_facts (first_word line)) as (_ & _ & L78 & _). lia. }
  pose proof (dec_length ledger HLD) as DL.
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
  destruct (mr_model B _ LAWS L2 A2 m2 md2 HM2) as (Hh2 & Hl2 & _).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply siv_mid. }
  intros ms3 (can3 & -> & EQ3).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x163ac) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; exact R2_2).
  assert (E3_4 : getr R3 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; exact R2_4).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs; exact R2_8).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 pl) by (rewrite (getr_of_eqv _ _ 9 X3 eq_refl); simp_regs; exact R2_9).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact R2_8).
  assert (E3_11 : getr R3 11 = Z_to_bv 64 ledger)
    by (rewrite (getr_of_eqv _ _ 11 X3 eq_refl); simp_regs; exact (eq_trans R2_18 A1)).
  assert (SP3 : spZ R3 = bv_unsigned sp - 32) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  pose proof ARGI as AI. unfold arg_i_contract in AI. rewrite SEGS in AI.
  eapply SR_bind.
  { apply (AI L2 A2 R3 m2 md2 e ledger 1 (sb_shift b A A2)).
    - split; [|rewrite SP3; lia].
      apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m2 md2 ARG_I_K R3 RJ2).
      + rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP3. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. lia.
      + rewrite E3_4. exact HTP.
    - exact E3_10.
    - exact E3_11.
    - exact HLD.
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - exact (proj2 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact NA2.
    - lia.
    - exact F182.
    - exact FRM.
    - exact RS2.
    - eapply room_slots_mono; [| | exact ROOM].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE2|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + unfold LMAX. lia.
    - exact RA2. }
  intros c3 (fx' & L3 & A3 & R4 & m3 & md3 & -> & FK & BK3 & UB3 & _ & RA3 & _ & F183 & RGN3 & ALT).
  destruct ALT as [(H06 & _)|(_ & p3 & POST3 & Hp3 & _ & FB3 & BLK3 & BN3 & BS3 & BX3 & INI3 & RS3)]; [lia|].
  rewrite SEGS in RA3, F183, BN3, BS3, BX3 |- *.
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 R
                REC_INSTANCE_VERB [canon line] Oc2 b ARG_I_K R3 _ L3 A3 R4 m3 md3 (dec ledger) p3
                (Z.of_nat (length (dec ledger)) + 1)
                SI2 ltac:(cbn; lia) ltac:(rewrite SP3; unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK; lia)
                ltac:(rewrite SP3; lia) POST3
                ltac:(intros a Ha; cbv beta in Ha; change (Z.of_nat (length [canon line])) with 1; lia)
                Hp3 FB3 BLK3 UB3 BK3 RGN3 BN3 BS3 BX3 (dec_no0 ledger) ltac:(unfold LMAX; lia) ltac:(unfold LMAX; lia)
                INI3 RS3 RA3 F183) as SI3.
  cbn [app] in SI3.
  pose proof POST3 as (PM3 & _ & _ & _ & _ & RP4 & _).
  assert (R4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (R4_8 : getr R4 8 = Z_to_bv 64 e) by exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) E3_8).
  assert (R4_9 : getr R4 9 = Z_to_bv 64 pl) by exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E3_9).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi.
    destruct FB3 as (_ & FBb & _).
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_I_K L2 A2 R3 m2 md2 _ L3 A3 R4 m3 md3 (bv_unsigned sp - 32 + i)
                HM2 POST3 ltac:(lia) ltac:(rewrite SP3; lia)) as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (BLE3 : sb_le (sb_shift b A A3)
                   (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1)) (Z.of_nat (length (dec ledger)) + 1))).
  { destruct BLK3 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A2 A3).
    rewrite <- (sb_shift_add (sb_shift b A A2) L2 A2 L3 A3 bl1 bl2 p3 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE2. }
  assert (Hp0 : pl <> 0) by exact (proj1 SA).
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O L3 A3 m3 md3 _ _ b pl (Some line)
              SI3 RA ltac:(unfold NULL_LIT; lia) SA)
    as (s & slack & P0 & PS & S0 & BS & N0 & LX & ALN & DJ & HOME & NRA).
  change (sarg (Some line)) with line in BS, N0, LX, ALN, DJ, HOME, NRA.
  assert (ES : s = pl) by (rewrite <- PS; destruct (Z.eqb_spec pl 0); [contradiction | reflexivity]).
  clear PS. subst s.
  rewrite length_app in DJ. cbn [length] in DJ.
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & _ & F18c & _).
  pose proof RJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC3 & _).
  destruct (mr_model B _ LAWS L3 A3 m3 md3 PM3) as (Hh3 & Hl3 & _).
  assert (FRn : rw_cells rsegs (normalize rsegs m3) (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply rw_cells_normalize; [exact RA3 | exact FR3 |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  assert (STn : stk rsegs (normalize rsegs m3) (bv_unsigned sp - 12384) (bv_unsigned sp - 32)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC3. left. lia. }
  pose proof (bytes_at_normalize rsegs m3 _ _ RA3
                (rjr_shapes B API SEGS RIMG 12384 (bv_unsigned sp) O L A mem md L3 A3 m3 md3 RJ3 GS)) as GSn.
  destruct F18c as (GOTc & can & GRDc).
  apply cells_bytes_at in GOTc. apply cells_bytes_at in GRDc.
  cbn [cells_bytes cbytes] in GOTc, GRDc. rewrite app_nil_r in GOTc, GRDc.
  pose proof (bytes_at_normalize rsegs m3 _ _ RA3 GOTc) as GOTn.
  pose proof (bytes_at_normalize rsegs m3 _ _ RA3 GRDc) as GRDn.
  assert (LBn : bytes_at rsegs (normalize rsegs m3) pl (line ++ [Z_to_bv 8 0])).
  { apply (bytes_at_normalize rsegs m3 _ _ RA3).
    replace (line ++ Z_to_bv 8 0 :: slack) with ((line ++ [Z_to_bv 8 0]) ++ slack) in BS
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  rewrite E3_1.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (Q2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 32)) by exact R4_2.
    assert (Q9 : reg_get R4 9 = Z_to_bv 64 pl) by exact R4_9.
    rewrite Q2, Q9.
    eapply (evt_normalize rsegs); [exact WX | exact RA3 |].
    eapply (siv_after SSPN SCSPN RSO); [exact FRn | exact STn | lia | lia | exact GSn | apply mem_inv_normalize
      | exact GOTn | exact GRDn | exact LBn | exact N0 | lia]. }
  intros ms5 (can5 & (s5n & Q5 & REL5 & RO5) & EQ5).
  destruct Q5 as (m4n & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU4n & WM4n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL5) as [EC5 MR5r].
  revert EC5 MR5r RO5 EQ5. generalize (ms_mem can5) as m4. intros m4 EC5 MR5r RO5 EQ5. subst can5.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR5r RO5 MU4n) as MU4.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR5r RO5 WM4n) as WM4.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  pose proof (sinv_stack B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L3 A3 m3 md3 _ _ b m4 _ SI3 MU4 WM4
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI4.
  pose proof SI4 as (_ & _ & _ & _ & _ & RA4 & _).
  assert (E5_1 : getr R5 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_2 : getr R5 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_10 : getr R5 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; exact R4_8).
  assert (E5_11 : getr R5 11 = Z_to_bv 64 (shape_find shape_rows (first_word line)))
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
  { apply (sinv_answer (fx := fx') B API SEGS ERRNO_LOW AX CTX (ANSF fx') SLACK 12384 L A regs mem md O L3 A3 R5 m4 md3
             (rec_record R REC_INSTANCE_VERB [canon line; dec ledger])
             (Oc2 ++ [(p3, Z.of_nat (length (dec ledger)) + 1)]) b
             (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1)) (Z.of_nat (length (dec ledger)) + 1)) e
             (shape_find shape_rows (first_word line))
             (REC_INSTANCE_VERB, [canon line; dec ledger]) (shape_of (first_word line)) true PRE AK SI4 E5_1
             ltac:(unfold spZ; rewrite E5_2; reflexivity) RP5 E5_10 E5_11 ltac:(rewrite E5_12; reflexivity)).
    - intros _. apply siv_ans_shape. exact RA4.
    - intros _ _. exact (ans_entry_record R REC_INSTANCE_VERB [canon line; dec ledger] HN).
    - exact (proj1 FK).
    - exact BLE3.
    - eapply room_slots_mono; [| | exact ROOM].
      + apply sb_malloc_mono, sb_malloc_mono. exact BLE3.
      + unfold LMAX. lia. }
  intros c' TR.
  destruct TR as (fx'' & L' & A' & regs' & mem' & md' & O' & q & -> & FK' & POST' & A10' & GR' & ON' & BL' & IN' & FB'
    & NQ' & BY' & OK' & AP' & RA' & F18' & INI' & REG' & BLE' & RES').
  exists fx'', L', A', regs', mem', md', (fst (sup_instance_verb_m R line ledger)), O',
    (snd (sup_instance_verb_m R line ledger)), q.
  split; [apply surjective_pairing|]. split; [reflexivity|]. split; [exact (fpk_trans _ _ _ FK FK')|].
  split; [exact POST'|].
  do 10 (split; [assumption|]).
  split.
  { rewrite SEGS. apply (shapes_kept B API SEGS RIMG RFREE _ L A regs mem md _ _ L' A' regs' mem' md' PRK POST');
      [|exact GS]. intros a Ha Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES in *. lia. }
  repeat (split; [assumption|]). exact RES'.
Qed.

Lemma siv_line : forall L A regs mem md pl ledger line R O b Lc Ac R1 m1 md1 Oc,
  call_pre_t B API 12384 L A regs mem md -> getr regs 10 = Z_to_bv 64 pl ->
  getr regs 11 = Z_to_bv 64 ledger -> -2 ^ 31 <= ledger < 2 ^ 31 ->
  str_arg B L A O (spZ regs) 12384 mem pl (Some line) -> ro_agree rsegs mem ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (sup_instance_verb_sizes line ledger (snd (sup_instance_verb_m R line ledger))))
    (LMAX + 1) ->
  sinv B API 12384 (spZ regs) L A mem md O Lc Ac m1 md1 (rec_record R REC_INSTANCE_VERB []) Oc b ->
  sb_le (sb_shift b A Ac) b -> (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  getr R1 1 = Z_to_bv 64 0x163a0 -> getr R1 2 = Z_to_bv 64 (spZ regs - 32) -> getr R1 4 = getr regs 4 ->
  getr R1 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R1 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R1 11 = getr regs 10 -> getr R1 9 = getr regs 10 -> getr R1 18 = getr regs 11 ->
  kept_ex [2; 8; 9; 18] regs R1 ->
  rw_cells rsegs m1 (spZ regs - 32)
    [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs m1 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 0)) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15e64) m1 (seg_rom rsegs)) md1)
    (sup_instance_verb_ret B API L A regs mem md line ledger R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK ANSF ARGI ARGL RSO SSPN SCSPN RIMG RFREE.
  intros L A regs mem md pl ledger line R O b Lc Ac R1 m1 md1 Oc PRE A0 A1 HLD SA RA GS FRM ROOM SI1 BLE1 HN HCODE
    E1 E2 E4 E8 E10 E11 E9 E18 KE1 FR1 NA1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof ROOM as ROOM0.
  change (snd (sup_instance_verb_m R line ledger)) with
    (snd (rec_answer (rec_record R REC_INSTANCE_VERB [canon line; dec ledger])
           (REC_INSTANCE_VERB, [canon line; dec ledger]) (shape_of (first_word line)) true)) in ROOM0.
  unfold sup_instance_verb_sizes, sb_mallocs in ROOM0. cbn [fold_left] in ROOM0.
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
  assert (Hp0 : pl <> 0) by exact (proj1 SA).
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 12384 (bv_unsigned sp) L A mem md O Lc Ac m1 md1 _ Oc b pl (Some line)
              SI1 RA ltac:(unfold NULL_LIT; lia) SA)
    as (s & slack & P0 & PS & S0 & BS & N0 & LX & ALN & DJ & HOME & NRA).
  change (sarg (Some line)) with line in BS, N0, LX, ALN, DJ, HOME, NRA.
  assert (ES : s = pl) by (rewrite <- PS; destruct (Z.eqb_spec pl 0); [contradiction | reflexivity]).
  clear PS. subst s.
  pose proof ARGL as AL. unfold arg_line_contract in AL. rewrite SEGS in AL.
  eapply SR_bind.
  { apply (AL Lc Ac R1 m1 md1 e pl 0 line slack (sb_shift b A Ac)).
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md Lc Ac m1 md1 ARG_LINE_K R1 RJ1).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
      + rewrite SP1. unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
      + rewrite SP1. lia.
      + rewrite E4. exact HTP.
    - exact E10.
    - rewrite E11. exact A0.
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - exact (proj2 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact NA1.
    - lia.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact ALN.
    - rewrite SP1. unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
    - rewrite SP1. apply (siv_home_lower Lc Ac (bv_unsigned sp)); [lia | exact HOME].
    - unfold iv_apart. apply (siv_nra_apart pl _ e (e + CALL_SIZE)).
      + intros a Ha. apply NRA. rewrite length_app. cbn [length]. lia.
      + exact (proj1 (proj2 ER)).
      + exact (proj2 (proj2 ER)).
      + unfold CALL_SIZE. lia.
      + lia.
    - exact RS1.
    - eapply room_slots_mono; [| | exact ROOM0].
      + eapply sb_le_trans; [apply sb_malloc_mono; exact BLE1|].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        eapply sb_le_trans; [|apply sb_le_malloc; lia].
        apply sb_le_malloc; lia.
      + unfold LMAX in *. lia.
    - exact RA1. }
  intros c2 (L2 & A2 & R2 & m2 & md2 & -> & BK2 & UB2 & _ & RA2 & GK2 & RGN2 & ALT2).
  destruct ALT2 as [(H6 & _)|(_ & p2 & POST2 & Hp2 & _ & FB2 & BLK2 & BN2 & BS2 & BX2 & INI2 & RS2)]; [lia|].
  rewrite SEGS in RA2, BN2, BS2, BX2 |- *.
  pose proof POST2 as (PM2 & _ & _ & _ & _ & RP2 & _).
  destruct (ax_statics AX L2 A2 m2 md2 PM2) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F182 : f18_words rsegs m2).
  { apply (f18_words_after m1 m2 g F181); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK2 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 12384 (bv_unsigned sp) L A mem md O Lc Ac m1 md1 R
                REC_INSTANCE_VERB [] Oc b ARG_LINE_K R1 _ L2 A2 R2 m2 md2 (canon line) p2 (Z.of_nat (length line) + 1)
                SI1 ltac:(cbn; lia) ltac:(rewrite SP1; unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK; lia)
                ltac:(rewrite SP1; lia) POST2
                ltac:(intros a Ha; cbv beta in Ha; cbn [length Z.of_nat]; lia)
                Hp2 FB2 BLK2 UB2 BK2 RGN2 BN2 BS2 BX2 (canon_no0 line N0)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                INI2 RS2 RA2 F182) as SI2.
  cbn [app] in SI2.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct FB2 as (_ & FBb & _).
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_LINE_K Lc Ac R1 m1 md1 _ L2 A2 R2 m2 md2 (bv_unsigned sp - 32 + i)
                HM1 POST2 ltac:(lia) ltac:(rewrite SP1; unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK; lia))
      as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (BLE2 : sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length line) + 1))).
  { destruct BLK2 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A Ac A2).
    rewrite <- (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2 bl1 bl2 p2 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE1. }
  rewrite E1.
  apply (siv_arg L A regs mem md pl ledger line R O b L2 A2 R2 m2 md2 _ PRE A1 HLD SA RA GS FRM ROOM SI2 BLE2 HN HCODE).
  - exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E2).
  - exact (eq_trans (RP2 4 ltac:(unfold callee_saved; lia)) E4).
  - exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E8).
  - exact (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) (eq_trans E9 A0)).
  - exact (eq_trans (RP2 18 ltac:(unfold callee_saved; lia)) E18).
  - exact (kept_ex_trans _ regs R1 R2 KE1 (kept_ex_of_pres _ _ _ RP2)).
  - exact FR2.
  - exact BN2.
Qed.

Theorem sup_instance_verb_holds : sup_instance_verb_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK RCF ANSF ARGI ARGL RSO SSPN SCSPN RIMG RFREE.
  unfold sup_instance_verb_contract.
  intros L A regs mem md pl ledger line R O b PRE A0 A1 HLD SA GS GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_INSTANCE_VERB_K in PRE, PRK, HCEIL, HWS, SA.
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
      eapply siv_seg_lt; [exact ST | lia | lia | exact NC | exact Hn | exact EW]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1 & EN1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    pose proof (sinv_record_lt B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                  REC_INSTANCE_VERB SI0 Hn ltac:(unfold REC_FN_COUNT, REC_INSTANCE_VERB; lia) MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EN1) as SI1.
    pose proof EN1 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
    apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
    apply (siv_line L A regs mem md pl ledger line R O b L A R1 m1 md O PRE A0 A1 HLD SA RA GS FRM ROOM SI1
             ltac:(rewrite sb_shift_refl; apply sb_le_refl) ltac:(lia) HCODE).
    + rewrite (getr_of_eqv _ _ 1 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 4 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 8 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 10 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 11 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 9 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 18 X1 eq_refl). simp_regs. reflexivity.
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
      eapply siv_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x1636c) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_9 : getr R1 9 = getr regs 10) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_18 : getr R1 18 = getr regs 11) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
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
        eapply siv_ret16. exact EW. }
      intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                  _ REC_INSTANCE_VERB POST ltac:(unfold REC_FN_COUNT, REC_INSTANCE_VERB; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                      [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply (rw_cells_transport rsegs _ m' m2 _ _ FR' MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
        repeat split; lia. }
      pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
      apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
      rewrite sb_shift_refl in BLE.
      apply (siv_line L A regs mem md pl ledger line R O b L' A' R2 m2 md' Oc' PRE A0 A1 HLD SA RA GS FRM ROOM SI2 BLE
               ltac:(lia) HCODE).
      * rewrite (getr_of_eqv _ _ 1 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 2 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
      * rewrite (getr_of_eqv _ _ 4 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 4 ltac:(unfold callee_saved; lia)) E1_4).
      * rewrite (rec_entry_full G_REC REC_SC R H16). rewrite (getr_of_eqv _ _ 8 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (rec_entry_full G_REC REC_SC R H16). rewrite (getr_of_eqv _ _ 10 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 11 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 9 ltac:(unfold callee_saved; lia)) E1_9).
      * rewrite (getr_of_eqv _ _ 9 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 9 ltac:(unfold callee_saved; lia)) E1_9).
      * rewrite (getr_of_eqv _ _ 18 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 18 ltac:(unfold callee_saved; lia)) E1_18).
      * apply (kept_ex_trans _ regs R1 R2); [kept_ex_tac X1|].
        apply (kept_ex_trans _ R1 regs' R2 (kept_ex_of_pres _ _ _ RP')). kept_ex_tac X2.
      * exact FR2.
      * rewrite (rec_entry_full G_REC REC_SC R H16).
        replace (REC_SC + CALL_OFF_NARGS) with (0x33d10 + Z.of_nat 4) by (unfold REC_SC, CALL_OFF_NARGS; lia).
        exact EA.
Qed.

End P.
