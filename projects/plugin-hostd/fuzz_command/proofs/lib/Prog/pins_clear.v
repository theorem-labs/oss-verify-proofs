(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its addresses and numbers changed; 657 of its 1081 lines of code are new or changed and 2318 lines of the source are left out. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecCore RecStub RecGlue.
Import ListNotations.
Open Scope Z_scope.

Ltac pc_lits :=
  fold_lit_ux;
  repeat match goal with
  | |- context [Z.shiftl ?a ?b] => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b;
      let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  end;
  rewrite ?Z.add_0_r.

Lemma pc_rf_nz : forall rf, -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 -> bv_eqb (Z_to_bv 64 rf) (Z_to_bv 64 0) = false.
Proof.
  intros rf Hr N. unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616. rewrite Zmod_0_l. intros H.
  apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. lia.
Qed.

Lemma pc_pre_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) b0 b1 b2 a3 a4 a5 a6 a7 a0
                     s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1704c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16ff0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 11 step.
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

Lemma pc_rec :
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (jk : list byte),
  rw_cells rsegs m e [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x17068) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e)
                     (sel_null s2) a1 a2 a3 a4 a5 a6 a7 (sel_null s2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 21); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1704c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e jk EW.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 21); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  step.
  destruct (Z.eq_dec (bv_unsigned s2) 0) as [Z2|Z2].
  - if_false. do 4 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_eq _ _) Z2).
    apply evt_done. eexists. split; [reflexivity|].
    split; [eassumption|]. split; eassumption.
  - if_true. do 2 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_neq _ _) Z2).
    apply evt_done. eexists. split; [reflexivity|].
    split; [eassumption|]. split; eassumption.
Qed.

Lemma pc_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat) (jk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 jk] ->
  evt rsegs (fun ms' => exists b1 b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x17068) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) (sel_null a0)
                     b1 b2 a3 a4 a5 a6 a7 (sel_null a0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 21); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16ff0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n jk ST LO LO2 NC Hn EW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply pc_pre_lt; [exact ST | exact LO | exact LO2 | exact NC | exact Hn] |].
  intros ms1 (b0 & b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1).
  assert (EW1 : rw_cells rsegs m1 (0x33d58 + 56 * Z.of_nat n) [CB 8 jk]).
  { apply (rw_cells_transport rsegs [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m1 _ _ EW MU1 WM1).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  eapply evt_cut; [eapply pc_rec; exact EW1 |].
  intros ms2 (m2 & -> & MU2 & WM2 & EN2).
  apply evt_done. exists b1, b2, m2. split; [reflexivity|].
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

Lemma pc_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x17028) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     s1 (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) b2 a3 a4 a5 a6 a7
                     a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16ff0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 11 step.
  rewrite sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  do 2 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma pc_ret16 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (jk : list byte),
  rw_cells rsegs m 0x33d10 [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x17068) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 0x33d10)
                     (sel_null s2) a1 a2 a3 a4 a5 a6 a7 (sel_null s2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 21); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17028) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m jk EW.
  do 2 step.
  eapply pc_rec. exact EW.
Qed.

Lemma pc_st :
  forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e rf : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (e + 8) [CB 8 junk] ->
  rw_cells rsegs m 0x33d48 [C4 (Z_to_bv 64 rf)] -> -2 ^ 31 <= rf < 2 ^ 31 ->
  evt rsegs (fun ms' => exists b1 b3 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 e) a0 b1 (Z_to_bv 64 rf) b3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17084) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 16)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 1)]
       /\ rw_cells rsegs m' (e + 8) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17068) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e rf junk EN EA RC Hrf.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. try (rewrite sx32_lit by lia).
  step. try (rewrite sx32_lit by lia).
  do 3 step. try pc_lits.
  do 2 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma pc_epi :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' s20 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' a0 a1 a2 a3 a4 a5 a6 a7
                                    s20 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x16fa8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x170a8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' s20 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 6 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma pc_ref :
  forall ra gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s10' s20 : word) (rf cd : Z),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s20; C8 s10'; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  rw_cells rsegs m 0x33d4c [C4 (Z_to_bv 64 cd)] ->
  -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 -> -2 ^ 31 <= cd < 2 ^ 31 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s10' (Z_to_bv 64 cd) a1 (Z_to_bv 64 rf) a3 a4 a5 a6 a7
                     s20 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16fa8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 (Z_to_bv 64 rf)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17084) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s10' s20 rf cd FR SPR RC2 Hrf Nrf Hcd.
  step. if_false_by (pc_rf_nz rf Hrf Nrf).
  do 2 step. rewrite sx32_lit by lia.
  eapply pc_epi; [exact FR | exact SPR].
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecTail RecAnsB RecCore RecStub.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import rec_calls_free_c xstrdup_c mix_call_c
answer_code_c pins_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require hand_back.

Lemma pc_pad_le : forall e c a, e <= c -> a < e + (- e) mod 8 -> a < 8 * ((c + 7) / 8).
Proof.
  intros e c a H1 H2.
  pose proof (Z.div_mod (- e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (- e) 8 ltac:(lia)).
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)).
  lia.
Qed.

Lemma pc_present : forall segs m a, present m a -> mbyte segs m a <> None.
Proof. intros segs m a [b E]. unfold mbyte. rewrite E. discriminate. Qed.

Lemma pc_combine_snd : forall (X Y : Type) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H |- *;
    [reflexivity | discriminate | discriminate | rewrite (IH l2 ltac:(lia)); reflexivity].
Qed.

Lemma pc_nth_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y) k a b,
  nth_error (combine l1 l2) k = Some (a, b) -> nth_error l1 k = Some a /\ nth_error l2 k = Some b.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] [|k] a b H; cbn in H |- *; try discriminate.
  - injection H as -> ->. split; reflexivity.
  - exact (IH l2 k a b H).
Qed.

Lemma pc_refuse_record : forall R fn As, r_refuse (rec_record R fn As) = r_refuse R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma pc_glob : forall a, 0x33d10 <= a < 0x34108 -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N.
Proof. intros a H. unfold GLOB_LO. change (Z.of_nat GLOB_N) with 1020. lia. Qed.

Lemma pc_entry_bounds : forall R, 0x33d10 <= rec_entry G_REC REC_SC R /\ rec_entry G_REC REC_SC R + 56 <= 0x340f8.
Proof.
  intros R. unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
  - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE. lia.
  - unfold REC_SC. lia.
Qed.

Lemma pc_run_mix : mix_call_contract ->
  forall ra gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e h : Z) (args : list (word * list byte))
    (sp1 ra0 s00 s10' s20 : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 80 <= bv_unsigned sp1 -> 0x34100 <= lo ->
  rw_cells rsegs m (bv_unsigned sp1) [C8 s20; C8 s10'; C8 s00; C8 ra0] ->
  bytes_at rsegs m e (le4 (Z_to_bv 64 21) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) ->
  0x33d10 <= e -> e + 56 <= 0x340f8 -> (length args <= 6)%nat ->
  (forall k p, nth_error args k = Some p -> mc_arg m (bv_unsigned sp1 - 80) (bv_unsigned sp1) e k p) ->
  rw_cells rsegs m 0x340f8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  evt rsegs (fun ms' => exists t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp1 + 32)) gp tp t0' t1' t2' s00 s10' (Z_to_bv 64 0)
                     b1 b2 b3 b4 b5 b6 b7 s20 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16fa8) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 80, bv_unsigned sp1); (0x340f8, 0x34100)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x340f8 [C8 (Z_to_bv 64 (mixcall h 21 (map snd args)))])
    (MS (mkR ra sp1 gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 e) a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17084) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra gp tp t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e h args sp1 ra0 s00 s10' s20 MI ST LO LO2 FR EF E0 E1 LA HARG ES Hh.
  assert (MIX' := MIX). unfold mix_call_contract, MIX_CALL_FRAME in MIX'.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned sp1 - 80, bv_unsigned sp1); (0x340f8, 0x34100)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. try if_true.
  do 3 step.
  call (MIX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 21 args).
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
    do 9 step.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. eassumption.
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

Lemma pc_pres_step : forall R2 R3 M3,
  Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r)) ->
  regs_preserved R2 R3.
Proof.
  intros R2 R3 M3 X3 K r Hr. pose proof (RecStub.getr_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ. exact (K r Hr).
Qed.

Lemma pc_pres_mid : forall regs R1 R2 R3 M1 M3,
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

Lemma pc_pres_fin : forall regs regs_t R2 M,
  Regs6ss.xregs_eqv M R2 ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
     getr regs_t (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
     reg_get M (Z_to_bv 5 r) = reg_get regs_t (Z_to_bv 5 r)) ->
  getr R2 (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) ->
  reg_get M (Z_to_bv 5 8) = reg_get regs (Z_to_bv 5 8) ->
  reg_get M (Z_to_bv 5 9) = reg_get regs (Z_to_bv 5 9) ->
  reg_get M (Z_to_bv 5 18) = reg_get regs (Z_to_bv 5 18) ->
  regs_preserved regs R2.
Proof.
  intros regs regs_t R2 M X KT K E2 E8 E9 E18.
  apply preserved_parts; [ | exact E2 | | | ].
  - intros r Hr N2 N8 N9 N18. pose proof (RecStub.getr_nz r Hr) as NZ.
    rewrite (getr_of_eqv _ _ _ X NZ), (K r Hr N2 N8 N9 N18).
    pose proof (KT r Hr N2 N8 N9 N18) as E. unfold getr in E |- *. rewrite NZ in E |- *. exact E.
  - pose proof (RecStub.getr_nz 8 ltac:(unfold callee_saved; lia)) as NZ.
    rewrite (getr_of_eqv _ _ _ X NZ). unfold getr. rewrite NZ. exact E8.
  - pose proof (RecStub.getr_nz 9 ltac:(unfold callee_saved; lia)) as NZ.
    rewrite (getr_of_eqv _ _ _ X NZ). unfold getr. rewrite NZ. exact E9.
  - pose proof (RecStub.getr_nz 18 ltac:(unfold callee_saved; lia)) as NZ.
    rewrite (getr_of_eqv _ _ _ X NZ). unfold getr. rewrite NZ. exact E18.
Qed.

Ltac fin_cases :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in
  intros rr Hrr ? ? ? ?; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
               rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  repeat (destruct CC as [CC|CC]; [subst rr; simp_regs; reflexivity|]);
  subst rr; simp_regs; reflexivity.

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
Hypothesis XSD : xstrdup_contract B API.
Hypothesis MIX : mix_call_contract.
Hypothesis ANSC : answer_code_contract B API.

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

Lemma pc_mc_arg : forall Lc Ac mc mdc e k pn s lo hi,
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
  { intros a Ha. pose proof (pc_pad_le (q + Z.of_nat (length s) + 1) (q + n) a ltac:(lia) Ha) as X.
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
      rewrite E1 in Hp. apply pc_present. replace (q + Z.of_nat (length s + 1) + Z.of_nat j)
        with (q + (Z.of_nat (length s + 1) + Z.of_nat j)) by ring. exact Hp.
    + apply pc_present. apply (SLACK Lc Ac mc mdc q n _ HM Hb0). split; [exact Hl|].
      apply (pc_pad_le (q + Z.of_nat (length s) + 1) (q + n)); lia.
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
  exists Rc code, rec_stub_code R REC_PINS_CLEAR As = rec_answer_code Rc code /\
    ct_ret 8304 L A regs mem md O Rc code b bpre c'.

Lemma pc_tail : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t,
  call_pre_t B API 8304 L A regs mem md ->
  sinv B API 8304 (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_PINS_CLEAR As) Oc b ->
  (length (r_calls R) <= 16)%nat -> length As = 1%nat ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) As ->
  sb_le (sb_shift b A Ac) bpre ->
  room_slots (sb_malloc (sb_malloc bpre (Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_CLEAR As)))) + 1))
                (Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_CLEAR As)))) + 1))
             (Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_CLEAR As)))) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 32)
    [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 32) -> getr regs_t 8 = Z_to_bv 64 0x33d10 ->
  getr regs_t 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr regs_t 12 = Z_to_bv 64 (r_refuse R) ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
     getr regs_t (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x17084) mc (seg_rom rsegs)) mdc) (tl_ret L A regs mem md O R As b bpre).
Proof using SEGS ERRNO_LOW GOWN AX CTX SLACK MIX ANSC.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t PRE SI H16 LA1 LXA BLE ROOM FRM FR T2 T8 T9 T12 KT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (pc_entry_bounds R) as (EB1 & EB2).
  set (nr := Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_CLEAR As)))) + 1) in *.
  assert (ROOMb : room_slots (sb_malloc (sb_malloc (sb_shift b A Ac) nr) nr) nr).
  { apply (room_slots_mono _ (sb_malloc (sb_malloc bpre nr) nr) nr nr
             (sb_malloc_mono _ _ nr (sb_malloc_mono _ _ nr BLE))); [unfold nr; lia | exact ROOM]. }
  set (R1 := rec_record R REC_PINS_CLEAR As) in *.
  assert (RF : r_refuse R1 = r_refuse R) by (unfold R1; apply pc_refuse_record).
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & HC & HA & HP & HX & HW).
  pose proof HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (RC2 : rw_cells rsegs mc 0x33d4c [C4 (Z_to_bv 64 (r_code R1))]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x33d4c with (G_REC + OFF_CODE) by (unfold G_REC, OFF_CODE; lia). exact X2. }
  assert (CK : ANSWER_CODE_K <= 8304) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (Q8 : reg_get regs_t 8 = Z_to_bv 64 0x33d10) by exact T8.
  assert (Q12 : reg_get regs_t 12 = Z_to_bv 64 (r_refuse R)) by exact T12.
  destruct (Z.eq_dec (r_refuse R1) 0) as [RZ|RNZ].
  2: {
    assert (ESC : rec_stub_code R REC_PINS_CLEAR As = rec_answer_code R1 (r_code R1)).
    { unfold rec_stub_code. cbv zeta. fold R1. rewrite (proj2 (Z.eqb_neq _ _) RNZ). reflexivity. }
    assert (Enr : nr = Z.of_nat (length (resp (r_code R1))) + 1) by (unfold nr; rewrite ESC; reflexivity).
    rewrite Enr in ROOMb.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      assert (Q2 : reg_get regs_t 2 = Z_to_bv 64 (bv_unsigned sp - 32)) by exact T2.
      rewrite Q2, Q8, Q12.
      eapply pc_ref; [exact FR | lia | exact RC2 | lia | lia | exact X7]. }
    intros ms1 (can1 & E1 & EQ1). subst can1.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2r).
    assert (E2_1 : getr R2 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X2r eq_refl); simp_regs; reflexivity).
    assert (E2_2 : getr R2 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X2r eq_refl); simp_regs; reflexivity).
    assert (E2_10 : getr R2 10 = Z_to_bv 64 (r_code R1))
      by (rewrite (getr_of_eqv _ _ 10 X2r eq_refl); simp_regs; reflexivity).
    assert (RP2 : regs_preserved regs R2).
    { apply (pc_pres_fin regs regs_t R2 _ X2r KT); [fin_cases | exact E2_2 | simp_regs; reflexivity
        | simp_regs; reflexivity | simp_regs; reflexivity]. }
    eapply SR_mono.
    { exact (code_tail 8304 L A regs mem md O Lc Ac R2 mc mdc R1 Oc b bpre (r_code R1) PRE CK SI E2_1
               ltac:(unfold spZ; rewrite E2_2; reflexivity) RP2 E2_10 X7 FRM BLE ROOMb). }
    intros c' H. exists R1, (r_code R1). split; [exact ESC | exact H]. }
  assert (ESC : rec_stub_code R REC_PINS_CLEAR As = rec_answer_code (rec_mix R1 (REC_PINS_CLEAR, As)) 0).
  { unfold rec_stub_code. cbv zeta. fold R1. rewrite RZ. reflexivity. }
  assert (Enr : nr = Z.of_nat (length (resp 0)) + 1) by (unfold nr; rewrite ESC; reflexivity).
  rewrite Enr in ROOMb.
  destruct (rec_rep_entry _ _ _ _ _ _ _ _ _ _ GR H16) as (P & CA).
  destruct CA as (CF1 & CF2 & CLP & CFN & CNA & CND & CKA). cbn [fst snd] in *.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (args := combine (map (fun pn => Z_to_bv 64 (fst pn)) P) As).
  assert (LP : length (map (fun pn => Z_to_bv 64 (fst pn)) P) = length As) by (rewrite length_map; exact CLP).
  assert (LA : length args = length As) by (unfold args; rewrite length_combine, LP; lia).
  assert (U2 : bv_unsigned (reg_get regs_t 2) = bv_unsigned sp - 32).
  { change (reg_get regs_t 2) with (getr regs_t 2). rewrite T2. apply unsigned_lit. lia. }
  assert (ARGS : forall k p, nth_error args k = Some p ->
            mc_arg (normalize rsegs mc) (bv_unsigned sp - 32 - 80) (bv_unsigned sp - 32) e k p).
  { intros k [w s] Hk. destruct (pc_nth_combine _ _ _ _ k w s Hk) as (Hw & Hs).
    rewrite nth_error_map in Hw. destruct (nth_error P k) as [pn|] eqn:EP; cbn in Hw; [|discriminate].
    injection Hw as <-.
    destruct (CKA k s pn Hs EP) as (BP & PNZ & PIN & PSZ & PBS & PN0).
    apply (pc_mc_arg Lc Ac mc mdc e k pn s); [exact HM | exact RA | exact BP | exact PIN | lia | exact PBS | exact PN0 | | lia].
    rewrite Forall_forall in LXA. apply LXA. exact (nth_error_In _ _ Hs). }
  assert (EF : bytes_at rsegs (normalize rsegs mc) e
                 (le4 (Z_to_bv 64 21) ++ le4 (Z_to_bv 64 (Z.of_nat (length args))))).
  { apply bytes_at_normalize; [exact RA|]. apply bytes_at_app. split.
    - unfold CALL_OFF_FN in CFN. rewrite Z.add_0_r in CFN. exact CFN.
    - rewrite LA. replace (e + Z.of_nat (length (le4 (Z_to_bv 64 21)))) with (e + CALL_OFF_NARGS)
        by (rewrite length_le4; unfold CALL_OFF_NARGS; reflexivity). exact CNA. }
  assert (STn : stk rsegs (normalize rsegs mc) (bv_unsigned sp - 8304) (bv_unsigned sp - 32)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC. left. lia. }
  assert (FRn : rw_cells rsegs (normalize rsegs mc) (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply rw_cells_normalize; [exact RA | exact FR |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  assert (ESn : rw_cells rsegs (normalize rsegs mc) 0x340f8 [C8 (Z_to_bv 64 (r_state R1))]).
  { apply rw_cells_normalize; [exact RA | | intros i Hi; cbn in Hi; apply glob_ro_false; unfold GLOB_LO, GLOB_N; lia].
    apply rc_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x340f8 with (G_REC + OFF_STATE) by (unfold G_REC, OFF_STATE; lia). exact X4. }
  assert (Q9 : reg_get regs_t 9 = Z_to_bv 64 e) by exact T9.
  assert (Q12z : reg_get regs_t 12 = Z_to_bv 64 0) by (rewrite Q12, <- RF, RZ; reflexivity).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8, Q9, Q12z.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply (pc_run_mix MIX) with (lo := bv_unsigned sp - 8304);
      [apply mem_inv_normalize | rewrite U2; exact STn | rewrite U2; lia | lia | rewrite U2; exact FRn | exact EF
      | lia | lia | rewrite LA, LA1; lia | | exact ESn | exact X9].
    intros k p Hk. rewrite U2. exact (ARGS k p Hk). }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m1n & -> & MU1n & WM1n
    & ES1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mc RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mc RA) MR1r RO1 WM1n) as WM1.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR1r ES1n) as ES1.
  rewrite U2 in MU1. unfold args in ES1. rewrite (pc_combine_snd _ _ _ _ LP) in ES1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2r).
  assert (HWW : forall a, 0 <= a < 2 ^ 64 ->
            ~ outside [(bv_unsigned sp - 32 - 80, bv_unsigned sp - 32); (0x340f8, 0x34100)] a ->
            bv_unsigned sp - 8304 <= a < bv_unsigned sp \/ rec_area a).
  { intros a Ra Hm. cbn in Hm. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE. lia. }
  assert (SI2 : sinv B API 8304 (bv_unsigned sp) L A mem md O Lc Ac m1 mdc (rec_mix R1 (REC_PINS_CLEAR, As)) Oc b).
  { apply (sinv_munch_core B API SEGS GOWN AX 8304 (bv_unsigned sp) L A mem md O Lc Ac mc mdc R1 Oc b m1 _
             (rec_mix R1 (REC_PINS_CLEAR, As)) SI MU1 WM1 HWW).
    unfold g_rec_rep in *.
    apply (rec_rep_set_state rsegs G_REC REC_SC Lc Ac mc m1 R1 Oc (mixcall (r_state R1) REC_PINS_CLEAR As) GR).
    - apply mixcall_range. exact X9.
    - replace (G_REC + OFF_STATE) with 0x340f8 by (unfold G_REC, OFF_STATE; lia). exact (rc_c8_bytes m1 0x340f8 _ ES1).
    - intros a Ha N. apply (munch_mbyte rsegs _ mc m1 a MU1); [unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia|].
      match goal with |- outside ?W a => destruct (outside_dec W a) as [H|H]; [exact H|] end. exfalso.
      cbn in H. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, OFF_STATE in *. lia.
    - intros a Ha _. apply glob_writable. apply pc_glob. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha. lia.
    - exact (sinv_kept B API SEGS AX 8304 (bv_unsigned sp) L A mem md O Lc Ac mc mdc R1 Oc b m1 _ SI MU1 HWW). }
  assert (E2_1 : getr R2 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X2r eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = sp).
  { rewrite (getr_of_eqv _ _ 2 X2r eq_refl). simp_regs. rewrite U2.
    replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by ring. apply Z_to_bv_bv_unsigned. }
  assert (E2_10 : getr R2 10 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 10 X2r eq_refl); simp_regs; reflexivity).
  assert (RP2 : regs_preserved regs R2).
  { apply (pc_pres_fin regs regs_t R2 _ X2r KT); [fin_cases | exact E2_2 | simp_regs; reflexivity
      | simp_regs; reflexivity | simp_regs; reflexivity]. }
  eapply SR_mono.
  { exact (code_tail 8304 L A regs mem md O Lc Ac R2 m1 mdc (rec_mix R1 (REC_PINS_CLEAR, As)) Oc b bpre 0 PRE CK SI2
             E2_1 ltac:(unfold spZ; rewrite E2_2; reflexivity) RP2 E2_10 ltac:(lia) FRM BLE ROOMb). }
  intros c' H. exists (rec_mix R1 (REC_PINS_CLEAR, As)), 0. split; [exact ESC | exact H].
Qed.

Lemma pc_nr : forall R As, -2^31 <= r_code R < 2^31 ->
  0 <= Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_CLEAR As)))) + 1 <= LMAX + 1.
Proof.
  intros R As H. unfold rec_stub_code. cbv zeta.
  assert (HC : -2^31 <= r_code (rec_record R REC_PINS_CLEAR As) < 2^31)
    by (unfold rec_record; destruct (Nat.ltb _ 16); exact H).
  destruct (r_refuse (rec_record R REC_PINS_CLEAR As) =? 0); cbn [snd rec_answer_code];
    [pose proof (resp_length 0 ltac:(lia)) | pose proof (resp_length _ HC)]; unfold LMAX; lia.
Qed.

Lemma pc_arg : forall L A regs mem md pu uri R O b Lc Ac R1 m1 md1 Oc,
  call_pre_t B API 8304 L A regs mem md -> getr regs 10 = Z_to_bv 64 pu ->
  str_arg B L A O (spZ regs) 8304 mem pu uri -> ro_agree rsegs mem -> frm_zero fp_csr ->
  room_slots (sb_mallocs b (pins_clear_sizes uri (snd (pins_clear_m R uri)))) (LMAX + 1) ->
  sinv B API 8304 (spZ regs) L A mem md O Lc Ac m1 md1 (rec_record R REC_PINS_CLEAR []) Oc b ->
  sb_le (sb_shift b A Ac) b -> (length (r_calls R) <= 16)%nat -> -2^31 <= r_code R < 2^31 ->
  getr R1 1 = Z_to_bv 64 0x17068 -> getr R1 2 = Z_to_bv 64 (spZ regs - 32) -> getr R1 4 = getr regs 4 ->
  getr R1 8 = Z_to_bv 64 0x33d10 -> getr R1 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R1 10 = sel_null (getr regs 10) ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
     getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  rw_cells rsegs m1 (spZ regs - 32) [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] ->
  bytes_at rsegs m1 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 0)) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15780) m1 (seg_rom rsegs)) md1)
    (pins_clear_ret B API L A regs mem md uri R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK XSD MIX ANSC.
  intros L A regs mem md pu uri R O b Lc Ac R1 m1 md1 Oc PRE A0 SA RA FRM ROOM SI1 BLE1 HN HCODE
    E1 E2 E4 E8 E9 E10 PR1 FR1 NA1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  pose proof (pc_nr R [sarg uri] HCODE) as NRB.
  unfold pins_clear_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  pose proof (pc_entry_bounds R) as (EB1 & EB2).
  set (e := rec_entry G_REC REC_SC R) in *.
  assert (EE : e = rec_entry G_REC REC_SC R) by reflexivity.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI1 as (RJ1 & GR1 & _ & _ & _ & RA1 & F181 & RS1).
  pose proof RJ1 as (HM1 & _).
  pose proof GR1 as (Q1 & HRep1 & _).
  pose proof HRep1 as (_ & _ & _ & _ & HX1 & _).
  pose proof HX1 as (X1 & _ & _ & _ & _ & X6 & _).
  rewrite pc_refuse_record in X1, X6.
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 8304 (bv_unsigned sp) L A mem md O Lc Ac m1 md1 _ Oc b pu uri
              SI1 RA ltac:(unfold NULL_LIT; lia) SA)
    as (s & slack & PW & SEL & S0 & BS & N0 & LX & AL & DJ & HOME & NRA).
  assert (SELW : sel_null (getr regs 10) = Z_to_bv 64 s)
    by (rewrite A0; unfold sel_null; rewrite unsigned_lit by lia; rewrite <- SEL; destruct (pu =? 0); reflexivity).
  set (x := sarg uri) in *.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof XSD as XS. unfold xstrdup_contract in XS. rewrite SEGS in XS.
  eapply SR_bind.
  { apply (XS Lc Ac R1 m1 md1 s x slack (sb_shift b A Ac)).
    - apply (call_pre_k_of_rjr B _ 8304 (bv_unsigned sp) rec_area _ L A mem md Lc Ac m1 md1 XSTRDUP_K R1 RJ1).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
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
        apply sb_le_malloc; lia.
      + lia.
    - exact RA1. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p & -> & POST2 & A0' & NZ & AL16 & FB2 & BLK2 & BK2 & UB2 & BYT2 & SRC2
    & RA2 & GK2 & INI2 & RGN2 & RS2).
  rewrite SEGS in RA2, BYT2 |- *.
  pose proof POST2 as (PM2 & _ & _ & _ & _ & RP2 & _ & PF2 & _).
  pose proof FB2 as (FBa & FBb & FBc).
  assert (R2_8 : getr R2 8 = Z_to_bv 64 0x33d10) by exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E8).
  assert (R2_8' : reg_get R2 8 = Z_to_bv 64 0x33d10) by exact R2_8.
  assert (R2_9 : getr R2 9 = Z_to_bv 64 e) by exact (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) E9).
  assert (R2_9' : reg_get R2 9 = Z_to_bv 64 e) by exact R2_9.
  assert (POST2' : call_post_k B (aa_MR API) XSTRDUP_K Lc Ac R1 m1 md1 (fun a => p <= a < p + (Z.of_nat (length x) + 1))
                     L2 A2 R2 m2 md2).
  { pose proof POST2 as (Q1' & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    split; [exact Q1'|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
    intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; lia]. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K Lc Ac R1 m1 md1 _ L2 A2 R2 m2 md2 (bv_unsigned sp - 32 + i)
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
  assert (RF2 : rw_cells rsegs (normalize rsegs m2) 0x33d48 [C4 (Z_to_bv 64 (r_refuse R))]).
  { apply rw_cells_normalize; [exact RA2 | | intros i Hi; cbn in Hi; apply glob_ro_false; unfold GLOB_LO, GLOB_N; lia].
    apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    apply (bytes_at_transfer rsegs m1).
    - replace 0x33d48 with (G_REC + OFF_REFUSE) by (unfold G_REC, OFF_REFUSE; lia). exact X1.
    - intros i Hi. rewrite length_le4 in Hi. apply GK. unfold GLOB_LO, GLOB_N; lia. }
  destruct (ax_statics AX L2 A2 m2 md2 PM2) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F182 : f18_words rsegs m2).
  { apply (f18_words_after m1 m2 g F181); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK2 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  destruct (mr_model B _ LAWS L2 A2 m2 md2 PM2) as (Hh2 & Hl2 & _).
  rewrite E1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite R2_8', R2_9'.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply pc_st; [exact NAn | exact EWn | exact RF2 | exact X6]. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (b1' & b3' & m3n & -> & MU3n & WM3n & NA3n & EA3n).
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
  pose proof (sinv_sarg B API SEGS ERRNO_LOW GFACT GOWN AX 8304 (bv_unsigned sp) L A mem md O Lc Ac m1 md1 R
                REC_PINS_CLEAR [] Oc b XSTRDUP_K R1 L2 A2 R2 m2 md2 m3 [(e + 4, e + 16)] x p (Z.of_nat (length x) + 1)
                SI1 ltac:(cbn; lia) ltac:(rewrite SP1; unfold XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SP1; lia)
                POST2' MU3 WM3
                ltac:(intros a Ra Hm; cbn in Hm; rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS; cbn [length Z.of_nat]; lia)
                NZ FB2 BLK2 UB2 BK2 RGN2 BN3 BS3 BYT2 N0 LX ltac:(unfold LMAX in *; lia) INI2 RS2 RA2 F182) as SI3.
  cbn [app] in SI3.
  assert (RP13 : regs_preserved R1 R3).
  { assert (RP23 : regs_preserved R2 R3).
    { apply (pc_pres_step R2 R3 _ X3). intros rr Hrr. unfold callee_saved in Hrr.
      assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
                   rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
      clear Hrr.
      repeat (destruct CC as [CC|CC];
        [subst rr; simp_regs; first [reflexivity | symmetry; exact R2_8' | symmetry; exact R2_9']|]).
      subst rr; simp_regs; reflexivity. }
    intros r Hr. rewrite (RP23 r Hr). exact (RP2 r Hr). }
  assert (R3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (RP13 2 ltac:(unfold callee_saved; lia)) E2).
  assert (R3_8 : getr R3 8 = Z_to_bv 64 0x33d10) by exact (eq_trans (RP13 8 ltac:(unfold callee_saved; lia)) E8).
  assert (R3_9 : getr R3 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by exact (eq_trans (RP13 9 ltac:(unfold callee_saved; lia)) E9).
  assert (R3_12 : getr R3 12 = Z_to_bv 64 (r_refuse R))
    by (rewrite (getr_of_eqv _ _ 12 X3 eq_refl); simp_regs; reflexivity).
  assert (PR3 : forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 ->
                  getr R3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr N2 N8 N9 N18. rewrite (RP13 r Hr). exact (PR1 r Hr N2 N8 N9 N18). }
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (BLE2 : sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length x) + 1))).
  { destruct BLK2 as (bl1 & bl2 & EB1' & EB2').
    rewrite <- (sb_shift_trans b A Ac A2).
    rewrite <- (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2 bl1 bl2 p _ EB1' EB2').
    apply sb_malloc_mono. exact BLE1. }
  eapply SR_mono.
  { apply (pc_tail L A regs mem md O L2 A2 m3 md2 R [x] _ b (sb_malloc b (Z.of_nat (length x) + 1)) R3 PRE SI3 HN
             eq_refl).
    - apply Forall_cons; [cbv beta; lia | apply Forall_nil].
    - exact BLE2.
    - eapply room_slots_mono; [apply sb_le_refl | exact NRB | exact ROOM].
    - exact FRM.
    - exact FR3.
    - exact R3_2.
    - exact R3_8.
    - exact R3_9.
    - exact R3_12.
    - exact PR3. }
  intros c' (Rc & code & ESC & TR).
  destruct TR as (fx' & L' & A' & regs' & mem' & md' & O' & -> & FK & POST & A10 & GR' & ON' & OK' & BL' & RA' & F18'
    & INI' & RGN' & BLE' & RES').
  unfold pins_clear_ret.
  exists fx', L', A', regs', mem', md', (fst (rec_answer_code Rc code)), O', (snd (rec_answer_code Rc code)).
  split; [transitivity (rec_answer_code Rc code); [exact ESC | apply surjective_pairing]|].
  split; [reflexivity|]. split; [exact FK|]. split; [exact POST|]. split; [exact A10|]. split; [exact GR'|].
  split; [exact ON'|]. split; [exact BL'|]. split; [exact OK'|]. split; [exact RA'|]. split; [exact F18'|].
  split; [exact INI'|]. split; [exact RGN'|]. split; [exact BLE' | exact RES'].
Qed.

Theorem pins_clear_holds : pins_clear_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK RCF XSD MIX ANSC.
  unfold pins_clear_contract.
  intros L A regs mem md pu uri R O b PRE A0 SA GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold PINS_CLEAR_K in PRE, PRK, HCEIL, HWS, SA.
  rewrite SEGS in GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API 8304 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8304) (bv_unsigned sp)).
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
      eapply pc_seg_lt; [exact ST | lia | lia | exact NC | exact Hn | exact EW]. }
    intros ms1 (can1 & (b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1 & EN1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    pose proof (sinv_record_lt B API SEGS GOWN AX 8304 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                  REC_PINS_CLEAR SI0 Hn ltac:(unfold REC_FN_COUNT, REC_PINS_CLEAR; lia) MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EN1) as SI1.
    pose proof EN1 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
    apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
    apply (pc_arg L A regs mem md pu uri R O b L A R1 m1 md O PRE A0 SA RA FRM ROOM SI1
             ltac:(rewrite sb_shift_refl; apply sb_le_refl) ltac:(lia) HCODE).
    + rewrite (getr_of_eqv _ _ 1 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 4 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 8 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 9 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 10 X1 eq_refl). simp_regs. reflexivity.
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
      eapply pc_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x17028) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_9 : getr R1 9 = getr regs 9) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_18 : getr R1 18 = getr regs 10) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 0x33d10)
      by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
    assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    pose proof (sinv_stack B API SEGS GOWN AX 8304 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
    apply (sinv_rcf B API SEGS ERRNO_LOW GOTG GRD GOWN AX RCF 8304 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 _
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
        eapply pc_ret16. exact EW. }
      intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX 8304 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                  _ REC_PINS_CLEAR POST ltac:(unfold REC_FN_COUNT, REC_PINS_CLEAR; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                      [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply (rw_cells_transport rsegs _ m' m2 _ _ FR' MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
        repeat split; lia. }
      pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
      apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
      rewrite sb_shift_refl in BLE.
      apply (pc_arg L A regs mem md pu uri R O b L' A' R2 m2 md' Oc' PRE A0 SA RA FRM ROOM SI2 BLE
               ltac:(lia) HCODE).
      * rewrite (getr_of_eqv _ _ 1 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 2 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
      * rewrite (getr_of_eqv _ _ 4 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 4 ltac:(unfold callee_saved; lia)) E1_4).
      * rewrite (getr_of_eqv _ _ 8 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (rec_entry_full G_REC REC_SC R H16). rewrite (getr_of_eqv _ _ 9 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 10 X2 eq_refl). simp_regs. f_equal.
        exact (eq_trans (RP' 18 ltac:(unfold callee_saved; lia)) E1_18).
      * apply (pc_pres_mid regs R1 regs' R2 _ _ X1 RP' X2). ex_cases.
      * exact FR2.
      * rewrite (rec_entry_full G_REC REC_SC R H16).
        replace (REC_SC + CALL_OFF_NARGS) with (0x33d10 + Z.of_nat 4) by (unfold REC_SC, CALL_OFF_NARGS; lia).
        exact EA.
Qed.

End P.
