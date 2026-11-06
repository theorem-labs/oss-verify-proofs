(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths, module names, addresses and numbers changed; 890 of its 1074 lines of code are new or changed and 2558 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition psel (p d : Z) : Z := if p =? 0 then d else p.

Lemma ps_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ps_nz_true : forall p, 0 <= p < 2 ^ 64 -> p <> 0 -> negb (bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0)) = true.
Proof.
  intros p Hp N. unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia.
Qed.

Lemma ps_rf_nz : forall rf, -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 -> bv_eqb (Z_to_bv 64 rf) (Z_to_bv 64 0) = false.
Proof.
  intros rf Hr N. unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616. rewrite Zmod_0_l. intros H.
  apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. lia.
Qed.

Lemma ps_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x343e0 <= lo ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x170dc) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 s0 a3
                     (Z_to_bv 64 20) a1 a2 a3 a4 a5 a6 a7 a2 a1 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x170a8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 13 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma ps_run2 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x170e8) sp gp tp t0 t1 t2 a0 s1 a0 s4 a2 a3 a4 a5 a6 a7
                                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x170dc) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma ps_run3 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x170f4) sp gp tp t0 t1 t2 s0 s1 s0 s3 a2 a3 a4 a5 a6 a7
                                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x170e8) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma ps_run4 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17100) sp gp tp t0 t1 t2 s0 s1 s0 s2 a2 a3 a4 a5 a6 a7
                                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x170f4) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma ps_run5 :
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (pv : Z),
  0 <= pv < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17118) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (psel pv 0x108b0))
                                     s0 (Z_to_bv 64 (psel pv 0x108b0)) a2 a3 a4 a5 a6 a7
                                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pv) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17100) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pv Hpv.
  unfold psel. destruct (Z.eqb_spec pv 0) as [E|N].
  - subst pv. step. if_false. do 5 step. apply evt_done. reflexivity.
  - step. rewrite (ps_nz_true pv Hpv N). cbv iota. do 3 step. apply evt_done. reflexivity.
Qed.

Lemma ps_epi :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 : word),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  0x343e0 + 48 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                                     s02 s03 s04 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17168) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17148) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 8 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma ps_run6r :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 : word) (rf cd : Z),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  0x343e0 + 48 <= bv_unsigned sp0 ->
  rw_cells rsegs m 0x34028 [C4 (Z_to_bv 64 rf)] -> rw_cells rsegs m 0x3402c [C4 (Z_to_bv 64 cd)] ->
  -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 -> -2 ^ 31 <= cd < 2 ^ 31 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 (Z_to_bv 64 cd) a1 a2 a3 a4 a5 a6 a7
                                     s02 s03 s04 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17168) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17118) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 rf cd FR SPR RC CD Hrf Nrf Hcd.
  do 4 step. try (rewrite ps_sx32 by lia). rewrite (ps_rf_nz rf Hrf Nrf). cbv iota.
  do 2 step. try (rewrite ps_sx32 by lia).
  eapply ps_epi; [exact FR | exact SPR].
Qed.

Lemma ps_run6z :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (st : word),
  rw_cells rsegs m 0x34028 [C4 (Z_to_bv 64 0)] -> rw_cells rsegs m 0x343d8 [C8 st] ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1713c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x33ff0) st
                                     s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1643c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17118) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m st RC ES.
  do 4 step. try (rewrite ps_sx32 by lia). if_true.
  do 3 step.
  apply evt_done. reflexivity.
Qed.

Lemma ps_run7 :
  forall ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 : word) (st : word),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  0x343e0 + 48 <= bv_unsigned sp0 ->
  rw_cells rsegs m 0x343d8 [C8 st] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 (Z_to_bv 64 0) a0 a2 a3 a4 a5 a6 a7
                     s02 s03 s04 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17168) fc None m' (seg_rom rsegs)
       /\ munch [(0x343d8, 0x343e0)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x343d8 [C8 a0])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x33ff0) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1713c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 st FR SPR ES.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(0x343d8, 0x343e0)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step.
  eapply evt_cut; [eapply ps_epi; [eassumption | lia] |].
  intros ms' ->. apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YO0u YO0x YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB RecSeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecStep RecGlue RecTail RecChain RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import xmalloc_c record_c arg_s_c mix_call_c
answer_code_c pins_set_c.
Local Open Scope Z_scope.

Definition kept_ex (xs : list Z) (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> ~ In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma kept_ex_trans : forall xs R1 R2 R3, kept_ex xs R1 R2 -> kept_ex xs R2 R3 -> kept_ex xs R1 R3.
Proof. intros xs R1 R2 R3 H1 H2 r Hr N. rewrite (H2 r Hr N). exact (H1 r Hr N). Qed.

Lemma kept_ex_of_pres : forall xs R R', regs_preserved R R' -> kept_ex xs R R'.
Proof. intros xs R R' H r Hr _. exact (H r Hr). Qed.

Lemma kept_ex_pres : forall xs R R', kept_ex xs R R' ->
  (forall r, In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> regs_preserved R R'.
Proof.
  intros xs R R' K E r Hr. destruct (in_dec Z.eq_dec r xs) as [H|H]; [exact (E r H) | exact (K r Hr H)].
Qed.

Ltac kept_ex_one X :=
  first [ exfalso; match goal with N : ~ In _ _ |- _ => apply N end; cbn [In]; lia
        | match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity] ].

Ltac kept_ex_tac X :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Nrr := fresh "Nrr" in
  intros rr Hrr Nrr; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; kept_ex_one X|]);
  subst rr; kept_ex_one X.

Ltac ps_reg X := match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end; simp_regs.

Lemma ps_present : forall segs m a, present m a -> mbyte segs m a <> None.
Proof. intros segs m a [b E]. unfold mbyte. rewrite E. discriminate. Qed.

Lemma ps_pad_le : forall e c a, e <= c -> a < e + (- e) mod 8 -> a < 8 * ((c + 7) / 8).
Proof.
  intros e c a H1 H2.
  pose proof (Z.div_mod (- e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (- e) 8 ltac:(lia)).
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)). lia.
Qed.

Lemma ps_combine_snd : forall (X Y : Type) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H |- *; try discriminate; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma ps_nth_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y) k a b,
  nth_error (combine l1 l2) k = Some (a, b) -> nth_error l1 k = Some a /\ nth_error l2 k = Some b.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] [|k] a b H; cbn in H |- *; try discriminate.
  - injection H as -> ->. split; reflexivity.
  - exact (IH l2 k a b H).
Qed.

Lemma ps_entry_bounds : forall R, 0x33ff0 <= rec_entry G_REC REC_SC R /\ rec_entry G_REC REC_SC R + 56 <= 0x343b8 /\
  rec_entry G_REC REC_SC R mod 8 = 0.
Proof.
  intros R. unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
  - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE.
    split; [lia|]. split; [lia|].
    apply Z.mod_divide; [lia | exists (26631 + 7 * Z.of_nat (length (r_calls R))); ring].
  - unfold REC_SC. split; [lia|]. split; [lia | reflexivity].
Qed.

Definition ps_rom (a : Z) (bs : list byte) : bool :=
  forallb (fun i => ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) &&
     match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error bs i with
     | Some b, Some c => Z.eqb (bv_unsigned b) (bv_unsigned c)
     | _, _ => false
     end) (seq 0 (length bs)).

Lemma ps_rom_at : forall a bs i, ps_rom a bs = true -> (i < length bs)%nat ->
  ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) = true /\
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros a bs i C Hi. unfold ps_rom in C.
  pose proof (proj1 (forallb_forall _ _) C i ltac:(apply in_seq; lia)) as Ci. cbv beta in Ci.
  apply andb_prop in Ci as [Cr Cv]. split; [exact Cr|].
  destruct (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [|discriminate].
  destruct (nth_error bs i) as [c|]; [|discriminate].
  apply Z.eqb_eq in Cv. f_equal. apply bv_eq. exact Cv.
Qed.

Lemma ps_rom_bytes : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ps_rom a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RA H0 H1 C. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (ps_rom_at a bs i C Hi) as [Cr Cv]. unfold wa. rewrite (RA _ Cr). exact Cv.
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

Lemma ps_run_mix : mix_call_contract ->
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e h : Z) (args : list (word * list byte))
    (sp1 ra0 s00 s01 s02 s03 s04 : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 96 <= bv_unsigned sp1 -> 0x343e0 <= lo ->
  rw_cells rsegs m (bv_unsigned sp1) [C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  rw_cells rsegs m 0x34028 [C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m e (le4 (Z_to_bv 64 20) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) ->
  0x33ff0 <= e -> e + 56 <= 0x343d8 -> e mod 8 = 0 -> (length args <= 6)%nat ->
  (forall k p, nth_error args k = Some p -> mc_arg m (bv_unsigned sp1 - 96) (bv_unsigned sp1) e k p) ->
  rw_cells rsegs m 0x343d8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  evt rsegs (fun ms' => exists t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp1 + 48)) gp tp t0' t1' t2' s00 s01 (Z_to_bv 64 0)
                     b1 b2 b3 b4 b5 b6 b7 s02 s03 s04 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x17168) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 96, bv_unsigned sp1); (0x343d8, 0x343e0)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x343d8 [C8 (Z_to_bv 64 (mixcall h 20 (map snd args)))])
    (MS (mkR ra sp1 gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17118) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e h args sp1 ra0 s00 s01 s02 s03 s04 MI ST LO LO2 FR RC EF E0 E1 E8 LA HARG ES Hh.
  assert (MIX' := MIX). unfold mix_call_contract, MIX_CALL_FRAME in MIX'.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned sp1 - 96, bv_unsigned sp1); (0x343d8, 0x343e0)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step. try (rewrite ps_sx32 by lia). if_true.
  do 3 step.
  call (MIX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 20 args).
  - exact MI.
  - exact ST.
  - lia.
  - lia.
  - exact LA.
  - rewrite unsigned_lit by lia. exact EF.
  - rewrite !unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. exact E8.
  - intros k p Hk. rewrite unsigned_lit by lia. exact (HARG k p Hk).
  - eapply ro_bytes_at; [exact MI | unfold FNV_B0_ADDR; lia | rewrite length_le8; unfold FNV_B0_ADDR; lia |].
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  - unfold FNV_B0_ADDR. lia.
  - rewrite (unsigned_lit h) by lia.
    do 11 step.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis ARGS : arg_s_contract B API.
Hypothesis MIX : mix_call_contract.
Hypothesis ANSC : answer_code_contract B API.

Lemma ps_frame : forall Kc Lc Ac regs_c mc mdc E excl L1 A1 regs1 m1 md1 hi,
  aa_MR API Lc Ac mc mdc ->
  call_post_rec B (aa_MR API) Kc Lc Ac regs_c mc mdc E excl L1 A1 regs1 m1 md1 ->
  alloc_ceiling <= spZ regs_c -> hi <= 2 ^ 64 ->
  (forall a, spZ regs_c <= a < hi -> ~ E a) ->
  forall a, spZ regs_c <= a < hi ->
    mbyte rsegs m1 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m1 a).
Proof using SEGS ERRNO_LOW.
  intros Kc Lc Ac regs_c mc mdc E excl L1 A1 regs1 m1 md1 hi HM POST HC HH HE a Ha.
  pose proof (aa_laws API) as LAWS.
  pose proof POST as (PM & _ & _ & _ & _ & _ & _ & PF & _).
  rewrite <- SEGS. apply PF.
  - left. lia.
  - intros Ho. pose proof (owned_low B _ LAWS _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (owned_low B _ LAWS _ _ _ _ a PM Ho). lia.
  - unfold scratch_k. intros [H|H]; lia.
  - exact (HE a Ha).
Qed.

Lemma ps_argc : forall K S L A mem md O Lc Ac mc mdc R fn As Oc bc regs_c s v (P : config -> Prop),
  sinv B API K S L A mem md O Lc Ac mc mdc (rec_record R fn As) Oc bc ->
  (length As < 6)%nat ->
  YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> S - K <= spZ regs_c - ARG_S_K -> spZ regs_c <= S ->
  getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  getr regs_c 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr regs_c 11 = Z_to_bv 64 s ->
  arg_s_src B Lc Ac (spZ regs_c) mc s v ->
  room_slots (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (sarg v)) + 1)) (Z.of_nat (length (sarg v)) + 1) ->
  (forall L1 A1 regs1 m1 md1 O1,
     sinv B API K S L A mem md O L1 A1 m1 md1 (rec_record R fn (As ++ [sarg v])) O1 bc ->
     sb_shift bc A A1 = sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (sarg v)) + 1) ->
     regs_preserved regs_c regs1 ->
     (forall a, spZ regs_c <= a < S ->
        mbyte rsegs m1 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m1 a)) ->
     SR rsegs (mkCfg (mkst regs1 (getr regs_c 1) m1 (seg_rom rsegs)) md1) P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 ARG_S) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS ERRNO_LOW GFACT GOWN AX ARGS.
  intros K S L A mem md O Lc Ac mc mdc R fn As Oc bc regs_c s v P SI H6 Hra Hal Hlo Hhi Htp H10 H11 SRC ROOM KONT.
  pose proof alloc_ceiling_val as AC. pose proof (aa_laws API) as LAWS.
  pose proof SI as (RJ & GR & _ & _ & _ & RA & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HMc & _).
  destruct (sarg_facts B Lc Ac (spZ regs_c) mc s v SRC) as (Hno & Hlx).
  assert (CL : (length (r_calls R) <= 16)%nat)
    by exact (rec_record_calls R fn As (rec_rep_calls_le _ _ _ _ _ _ _ _ GR)).
  destruct (rec_entry_bounds R CL) as (EB1 & EB2 & EB3).
  destruct (rec_entry_at rsegs Lc Ac mc R fn As Oc GR) as (Pk & CA).
  pose proof CA as (_ & _ & _ & _ & CNA & _). cbn [snd] in CNA.
  set (e := rec_entry G_REC REC_SC R) in *.
  pose proof ARGS as AC2. unfold arg_s_contract in AC2. rewrite SEGS in AC2.
  eapply SR_bind.
  { apply (AC2 Lc Ac regs_c mc mdc e s (Z.of_nat (length As)) v (sb_shift bc A Ac));
      [ | exact H10 | exact H11 | exact EB3 | exact EB1 | exact EB2 | | exact CNA | lia | exact SRC | exact F18 | exact RS
      | exact ROOM | exact RA].
    - apply (call_pre_k_of_rjr B _ K S rec_area _ L A mem md Lc Ac mc mdc ARG_S_K regs_c RJ Hra Hal);
        [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia | exact Hlo | exact Hhi | exact Htp].
    - apply glob_wr_at; unfold GLOB_LO, GLOB_N, REC_SC, G_REC, REC_SIZE, CALL_SIZE in *; lia. }
  intros c1 RET. unfold arg_s_ret in RET. rewrite SEGS in RET.
  destruct RET as (L1 & A1 & regs1 & m1 & md1 & -> & BK & UB & RA1 & GK & F181 & RGN & [(E6 & _) | RET]); [lia|].
  destruct RET as (Hm & p & POST & Hp0 & Hp16 & FB & (b1 & b2 & EBa & EBb) & BN & BS & BX & INI & RS1).
  set (k := Z.of_nat (length (sarg v)) + 1) in *.
  pose proof (sb_shift_add (sb_shift bc A Ac) Lc Ac L1 A1 b1 b2 p k EBa EBb) as SH.
  rewrite sb_shift_trans in SH.
  pose proof (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) as POSTr.
  pose proof POSTr as (PM & _ & _ & _ & _ & PR & _).
  assert (INP : In (p, k) (blocks L1 A1)) by (rewrite EBa; apply in_or_app; right; left; reflexivity).
  destruct (block_facts B _ LAWS L1 A1 m1 md1 p k 0 PM INP ltac:(lia)) as (_ & Q1 & Q2 & _).
  assert (SI1 : sinv B API K S L A mem md O L1 A1 m1 md1 (rec_record R fn (As ++ [sarg v])) (Oc ++ [(p, k)]) bc).
  { apply (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX K S L A mem md O Lc Ac mc mdc R fn As Oc bc ARG_S_K regs_c _
             L1 A1 regs1 m1 md1 (sarg v) p k SI H6 Hlo Hhi POST); try assumption.
    all: first [ exact (ex_intro _ b1 (ex_intro _ b2 (conj EBa EBb))) | (rewrite <- SH; exact RS1)
               | (intros a Ha; cbv beta in Ha; unfold k; lia) | (unfold k; split; lia) ]. }
  apply (KONT L1 A1 regs1 m1 md1 (Oc ++ [(p, k)]) SI1 (eq_sym SH) PR).
  intros a Ha.
  apply (ps_frame ARG_S_K Lc Ac regs_c mc mdc _ (fun _ => False) L1 A1 regs1 m1 md1 S HMc POSTr);
    [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK in Hlo; lia | lia | | exact Ha].
  intros x Hx Hr. cbv beta in Hr. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK in Hlo.
  unfold e, k in *. pose proof (rec_entry_bounds R CL) as (Q3 & Q4 & _).
  unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
Qed.

Lemma ps_dash : forall L A m sp, ro_agree rsegs m -> 0x108b8 <= sp - ARG_S_K ->
  arg_s_src B L A sp m 0x108b0 (Some (bstr "-"%string)).
Proof using SEGS.
  intros L A m sp RA HS.
  assert (C : ps_rom 0x108b0 (bstr "-"%string ++ [Z_to_bv 8 0]) = true) by (vm_compute; reflexivity).
  assert (LN0 : length (bstr "-"%string) = 1%nat) by reflexivity.
  assert (PD : (- (0x108b0 + 1 + 1)) mod 8 = 6) by reflexivity.
  assert (BS : bytes_at rsegs m 0x108b0 (bstr "-"%string ++ [Z_to_bv 8 0]))
    by (apply ps_rom_bytes; [exact RA | lia | rewrite length_app, LN0; cbn; lia | exact C]).
  destruct (rs_bytes_pad rsegs m 0x108b0 (bstr "-"%string ++ [Z_to_bv 8 0]) 6 BS) as (sl & LS & BS2).
  { rewrite length_app, LN0. cbn. lia. }
  { intros j Hj. rewrite length_app, LN0. cbn [length Nat.add].
    assert (CA : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat \/ j = 4%nat \/ j = 5%nat) by lia.
    repeat (destruct CA as [CA|CA]; [subst j; rewrite (mbyte_ro_agree _ _ _ RA) by (vm_compute; reflexivity);
      let H := fresh in intro H; vm_compute in H; discriminate H|]).
    subst j. rewrite (mbyte_ro_agree _ _ _ RA) by (vm_compute; reflexivity).
    let H := fresh in intro H; vm_compute in H; discriminate H. }
  rewrite <- app_assoc in BS2. cbn [app] in BS2.
  cbn [arg_s_src]. split; [lia|].
  split; [apply no0_nz; vm_compute; reflexivity|].
  split; [rewrite LN0; unfold LMAX; lia|].
  exists sl. split; [rewrite SEGS; exact BS2|].
  rewrite LN0. split; [rewrite LS; apply Z.leb_le; vm_compute; reflexivity|].
  split; [left; rewrite length_app, LN0; cbn [length]; rewrite LS; lia|].
  right. right. split; [lia|]. split; [lia|]. intros i Hi. rewrite SEGS.
  destruct (ps_rom_at 0x108b0 _ (Z.to_nat i) C) as [H _].
  + rewrite length_app, LN0. cbn [length]. lia.
  + rewrite Z2Nat.id in H by lia. exact H.
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
Proof using SLACK.
  intros Lc Ac mc mdc e k [q n] s lo hi HM RA BP Hb Hn BS N0 LX HLO. cbn [fst snd] in *.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_value as ACV.
  destruct (block_facts B _ LAWS Lc Ac mc mdc q n 0 HM Hb ltac:(lia)) as (_ & HQ1 & HQ2 & _).
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  pose proof (Z.mod_pos_bound (- (q + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hpad.
  assert (CE : forall a, a < q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 ->
            a < alloc_ceiling).
  { intros a Ha. pose proof (ps_pad_le (q + Z.of_nat (length s) + 1) (q + n) a ltac:(lia) Ha) as X.
    pose proof (Z.div_mod (q + n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)). destruct ACV as (_ & ACM). lia. }
  destruct (rs_bytes_pad rsegs mc q (s ++ [Z_to_bv 8 0])
              (Z.to_nat ((- (q + Z.of_nat (length s) + 1)) mod 8)) BS) as (sl & LS & BS2).
  - rewrite length_app. cbn [length].
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)).
    pose proof alloc_ceiling_val. lia.
  - intros j Hj. rewrite length_app. cbn [length].
    destruct (Z_lt_le_dec (q + Z.of_nat (length s + 1) + Z.of_nat j) (q + n)) as [Hl|Hl].
    + destruct (block_facts B _ LAWS Lc Ac mc mdc q n (Z.of_nat (length s + 1) + Z.of_nat j) HM Hb ltac:(lia))
        as (Hp & _).
      apply ps_present. replace (q + Z.of_nat (length s + 1) + Z.of_nat j)
        with (q + (Z.of_nat (length s + 1) + Z.of_nat j)) by ring. exact Hp.
    + apply ps_present. apply (SLACK Lc Ac mc mdc q n _ HM Hb). split; [exact Hl|].
      apply (ps_pad_le (q + Z.of_nat (length s) + 1) (q + n)); lia.
  - unfold mc_arg. cbn [fst snd]. rewrite unsigned_lit by (pose proof alloc_ceiling_val; lia).
    split; [apply bytes_at_normalize; [exact RA | unfold CALL_OFF_ARGS in BP; exact BP]|].
    split; [exact N0|]. split; [exact LX|]. split; [lia|]. split; [pose proof alloc_ceiling_val; lia|].
    exists sl. rewrite <- app_assoc in BS2. cbn [app] in BS2.
    split; [apply bytes_at_normalize; [exact RA | exact BS2]|].
    rewrite LS, Z2Nat.id by lia. split; [lia|]. left.
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
Qed.

Lemma ps_cell4 : forall m a v, GLOB_LO <= a -> a + 4 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le4 v) -> rw_cells rsegs m a [C4 v].
Proof.
  intros m a v H1 H2 H. apply (rw_cells_same_bytes _ _ [CB (length (le4 v)) (le4 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le4; lia | exact H].
  - cbn. split; exact I.
  - reflexivity.
  - cbn [cells_size csize]. rewrite length_le4. reflexivity.
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
  rw_cells rsegs mc (spZ regs - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs_t 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  kept_ex [2; 8; 9; 18; 19; 20] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x17118) mc (seg_rom rsegs)) mdc) (tl_ret L A regs mem md O R As b bpre).
Proof using SEGS ERRNO_LOW GOWN AX CTX SLACK MIX ANSC.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t PRE SI H16 LA4 LXA BLE ROOM FRM FR T2 T8 KT.
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
  pose proof (ps_entry_bounds R) as (EB1 & EB2 & EB3).
  set (nr := Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_SET As)))) + 1) in *.
  assert (ROOMb : room_slots (sb_malloc (sb_malloc (sb_shift b A Ac) nr) nr) nr).
  { apply (room_slots_mono _ (sb_malloc (sb_malloc bpre nr) nr) nr nr
             (sb_malloc_mono _ _ nr (sb_malloc_mono _ _ nr BLE))); [unfold nr; lia | exact ROOM]. }
  set (R1 := rec_record R REC_PINS_SET As) in *.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & HC & HA & HP & HX & HW).
  pose proof HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (RC1 : rw_cells rsegs mc 0x34028 [C4 (Z_to_bv 64 (r_refuse R1))]).
  { apply ps_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x34028 with (G_REC + OFF_REFUSE) by (unfold G_REC, OFF_REFUSE; lia). exact X1. }
  assert (RC2 : rw_cells rsegs mc 0x3402c [C4 (Z_to_bv 64 (r_code R1))]).
  { apply ps_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x3402c with (G_REC + OFF_CODE) by (unfold G_REC, OFF_CODE; lia). exact X2. }
  assert (CK : ANSWER_CODE_K <= PINS_SET_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (Q8 : reg_get regs_t 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R)) by exact T8.
  assert (Q2 : reg_get regs_t 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by exact T2.
  destruct (Z.eq_dec (r_refuse R1) 0) as [RZ|RNZ].
  2: {
    assert (ESC : rec_stub_code R REC_PINS_SET As = rec_answer_code R1 (r_code R1)).
    { unfold rec_stub_code. cbv zeta. fold R1. rewrite (proj2 (Z.eqb_neq _ _) RNZ). reflexivity. }
    assert (Enr : nr = Z.of_nat (length (resp (r_code R1))) + 1) by (unfold nr; rewrite ESC; reflexivity).
    rewrite Enr in ROOMb.
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2.
      eapply ps_run6r; [exact FR | lia | exact RC1 | exact RC2 | exact X6 | exact RNZ | exact X7]. }
    intros ms1 (can1 & E1 & EQ1). subst can1.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2r).
    assert (E2_1 : getr R2 1 = getr regs 1) by (ps_reg X2r; reflexivity).
    assert (E2_2 : getr R2 2 = sp) by (ps_reg X2r; reflexivity).
    assert (E2_10 : getr R2 10 = Z_to_bv 64 (r_code R1)) by (ps_reg X2r; reflexivity).
    assert (RP2 : regs_preserved regs R2).
    { apply (kept_ex_pres [2; 8; 9; 18; 19; 20]).
      - apply (kept_ex_trans _ regs regs_t R2 KT). kept_ex_tac X2r.
      - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
          ps_reg X2r; first [reflexivity | unfold getr; reflexivity]. }
    eapply SR_mono.
    { exact (code_tail PINS_SET_K L A regs mem md O Lc Ac R2 mc mdc R1 Oc b bpre (r_code R1) PRE CK SI E2_1
               ltac:(unfold spZ; rewrite E2_2; reflexivity) RP2 E2_10 X7 FRM BLE ROOMb). }
    intros c' H. exists R1, (r_code R1). split; [exact ESC | exact H]. }
  assert (ESC : rec_stub_code R REC_PINS_SET As = rec_answer_code (rec_mix R1 (REC_PINS_SET, As)) 0).
  { unfold rec_stub_code. cbv zeta. fold R1. rewrite RZ. reflexivity. }
  assert (Enr : nr = Z.of_nat (length (resp 0)) + 1) by (unfold nr; rewrite ESC; reflexivity).
  rewrite Enr in ROOMb.
  destruct (rec_entry_at rsegs Lc Ac mc R REC_PINS_SET As Oc GR) as (P & CA).
  destruct CA as (CF1 & CF2 & CLP & CFN & CNA & CND & CKA). cbn [fst snd] in *.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (args := combine (map (fun pn => Z_to_bv 64 (fst pn)) P) As).
  assert (LP : length (map (fun pn => Z_to_bv 64 (fst pn)) P) = length As) by (rewrite length_map; exact CLP).
  assert (LA : length args = length As) by (unfold args; rewrite length_combine, LP; lia).
  assert (U2 : bv_unsigned (reg_get regs_t 2) = bv_unsigned sp - 48) by (rewrite Q2; apply unsigned_lit; lia).
  assert (ARGS2 : forall k p, nth_error args k = Some p ->
            mc_arg (normalize rsegs mc) (bv_unsigned sp - 48 - 96) (bv_unsigned sp - 48) e k p).
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
  assert (STn : stk rsegs (normalize rsegs mc) (bv_unsigned sp - 8384) (bv_unsigned sp - 48)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC. left. unfold PINS_SET_K. lia. }
  assert (FRn : rw_cells rsegs (normalize rsegs mc) (bv_unsigned sp - 48)
                  [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
                   C8 (getr regs 1)]).
  { apply rw_cells_norm_hi; [exact RA | lia | exact FR]. }
  assert (RC1n : rw_cells rsegs (normalize rsegs mc) 0x34028 [C4 (Z_to_bv 64 0)]).
  { rewrite RZ in RC1. apply rw_cells_norm_glob; [exact RA | unfold GLOB_LO; lia | cbn; unfold GLOB_LO, GLOB_N; lia | exact RC1]. }
  assert (ESn : rw_cells rsegs (normalize rsegs mc) 0x343d8 [C8 (Z_to_bv 64 (r_state R1))]).
  { apply rw_cells_norm_glob; [exact RA | unfold GLOB_LO; lia | cbn; unfold GLOB_LO, GLOB_N; lia |].
    apply bytes_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x343d8 with (G_REC + OFF_STATE) by (unfold G_REC, OFF_STATE; lia). exact X4. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply (ps_run_mix MIX) with (lo := bv_unsigned sp - 8384);
      [apply mem_inv_normalize | rewrite U2; exact STn | rewrite U2; lia | lia | rewrite U2; exact FRn | exact RC1n
      | exact EF | lia | lia | exact EB3 | rewrite LA, LA4; lia | | exact ESn | exact X9].
    intros k p Hk. rewrite U2. exact (ARGS2 k p Hk). }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m1n & -> & MU1n & WM1n
    & ES1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mc RA) MR1r RO1 MU1n) as MU1. rewrite U2 in MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mc RA) MR1r RO1 WM1n) as WM1.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR1r ES1n) as ES1.
  unfold args in ES1. rewrite (ps_combine_snd _ _ _ _ LP) in ES1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2r).
  assert (SI2 : sinv B API PINS_SET_K (bv_unsigned sp) L A mem md O Lc Ac m1 mdc (rec_mix R1 (REC_PINS_SET, As)) Oc b).
  { exact (sinv_state B API SEGS GOWN AX PINS_SET_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc R1 Oc b m1 _
             (mixcall (r_state R1) REC_PINS_SET As) SI MU1 WM1
             ltac:(intros a Ra Hm; cbn in Hm; unfold G_REC, OFF_STATE, PINS_SET_K; lia)
             (mixcall_range _ _ _ X9)
             ltac:(replace (G_REC + OFF_STATE) with 0x343d8 by (unfold G_REC, OFF_STATE; lia); exact (cells_c8 m1 _ _ ES1))). }
  assert (E2_1 : getr R2 1 = getr regs 1) by (ps_reg X2r; reflexivity).
  assert (E2_2 : getr R2 2 = sp).
  { ps_reg X2r. rewrite U2. replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by ring.
    apply Z_to_bv_bv_unsigned. }
  assert (E2_10 : getr R2 10 = Z_to_bv 64 0) by (ps_reg X2r; reflexivity).
  assert (RP2 : regs_preserved regs R2).
  { apply (kept_ex_pres [2; 8; 9; 18; 19; 20]).
    - apply (kept_ex_trans _ regs regs_t R2 KT). kept_ex_tac X2r.
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|Hr]; [exact E2_2|].
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
        ps_reg X2r; first [reflexivity | unfold getr; reflexivity]. }
  eapply SR_mono.
  { exact (code_tail PINS_SET_K L A regs mem md O Lc Ac R2 m1 mdc (rec_mix R1 (REC_PINS_SET, As)) Oc b bpre 0 PRE CK SI2
             E2_1 ltac:(unfold spZ; rewrite E2_2; reflexivity) RP2 E2_10 ltac:(lia) FRM BLE ROOMb). }
  intros c' H. exists (rec_mix R1 (REC_PINS_SET, As)), 0. split; [exact ESC | exact H].
Qed.

Lemma ps_sarg_len : forall L A O S K mem p v, str_arg B L A O S K mem p v -> Z.of_nat (length (sarg v)) <= LMAX.
Proof.
  intros L A O S K mem p [x|] H; cbn [sarg]; [destruct H as (_ & _ & LX & _); exact LX | cbn; unfold LMAX; lia].
Qed.

Lemma ps_darg_len : forall L A O S K mem p v, str_arg B L A O S K mem p v ->
  Z.of_nat (length (darg v (bstr "-"%string))) <= LMAX.
Proof.
  intros L A O S K mem p [x|] H; cbn [darg]; [destruct H as (_ & _ & LX & _); exact LX | cbn; unfold LMAX; lia].
Qed.

Lemma ps_pbound : forall L A O S K mem p v, str_arg B L A O S K mem p v -> 0 <= p < 2 ^ 64.
Proof.
  intros L A O S K mem p [x|] H; cbn [str_arg] in H.
  - destruct H as (_ & _ & _ & slack & BS & _). pose proof (bytes_at_bound _ _ _ _ BS) as BB.
    rewrite length_app in BB. cbn [length] in BB. lia.
  - subst p. lia.
Qed.

Theorem pins_set_holds : pins_set_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN AX CTX SLACK REC ARGS MIX ANSC.
  unfold pins_set_contract.
  intros L A regs mem md pu pf pl pv uri files lay verdict R O b PRE AU AF AL AV SU SF SL SV GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & _).
  unfold PINS_SET_K in HCEIL, HWS.
  rewrite SEGS in GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API PINS_SET_K L A regs mem md R O b PRK ltac:(unfold PINS_SET_K; lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q0 & HRep0 & _).
  pose proof HRep0 as (_ & _ & _ & _ & HX0 & _).
  pose proof HX0 as (_ & _ & _ & _ & _ & _ & HCODE & _).
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as H16.
  pose proof (ps_sarg_len _ _ _ _ _ _ _ _ SU) as LU.
  pose proof (ps_sarg_len _ _ _ _ _ _ _ _ SF) as LF.
  pose proof (ps_sarg_len _ _ _ _ _ _ _ _ SL) as LL.
  pose proof (ps_darg_len _ _ _ _ _ _ _ _ SV) as LV.
  pose proof (ps_pbound _ _ _ _ _ _ _ _ SV) as HPV.
  pose proof (ps_nr R [sarg uri; sarg files; sarg lay; darg verdict (bstr "-"%string)] HCODE) as HNR.
  assert (ROOM6 : room_slots (sb_malloc (sb_malloc (sb_malloc (sb_malloc (sb_malloc (sb_malloc b
              (Z.of_nat (length (sarg uri)) + 1)) (Z.of_nat (length (sarg files)) + 1))
              (Z.of_nat (length (sarg lay)) + 1)) (Z.of_nat (length (darg verdict (bstr "-"%string))) + 1))
              (Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_SET
                 [sarg uri; sarg files; sarg lay; darg verdict (bstr "-"%string)])))) + 1))
              (Z.of_nat (length (resp (snd (rec_stub_code R REC_PINS_SET
                 [sarg uri; sarg files; sarg lay; darg verdict (bstr "-"%string)])))) + 1))
            (LMAX + 1)) by exact ROOM.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8384) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold PINS_SET.
    eapply ps_run1; [exact ST | lia | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x170dc) by (ps_reg X1; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by (ps_reg X1; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 20) by (ps_reg X1; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 pv) by (ps_reg X1; exact AV).
  assert (E1_18 : getr R1 18 = Z_to_bv 64 pl) by (ps_reg X1; exact AL).
  assert (E1_19 : getr R1 19 = Z_to_bv 64 pf) by (ps_reg X1; exact AF).
  assert (E1_20 : getr R1 20 = Z_to_bv 64 pu) by (ps_reg X1; exact AU).
  assert (KR1 : kept_ex [2; 8; 9; 18; 19; 20] regs R1) by kept_ex_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (TP1 : getr R1 4 = Z_to_bv 64 (ms_tp B))
    by exact (eq_trans (KR1 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)) HTP).
  assert (SI1 : sinv B API PINS_SET_K (bv_unsigned sp) L A mem md O L A m1 md R O b).
  { apply (sinv_stack B API SEGS GOWN AX PINS_SET_K (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1).
    intros a Ra Hm. cbn in Hm. unfold PINS_SET_K. lia. }
  apply (sinv_record B API SEGS ERRNO_LOW AX REC PINS_SET_K (bv_unsigned sp) L A mem md O L A m1 md R O b R1
           REC_PINS_SET _ SI1).
  { rewrite E1_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP1. unfold RECORD_K, ALLOC_STACK, PINS_SET_K. lia. }
  { rewrite SP1. lia. }
  { exact TP1. }
  { rewrite E1_10. reflexivity. }
  { unfold REC_FN_COUNT, REC_PINS_SET. lia. }
  intros L1 A1 regs1 m2 md1 O1 SI2 BLE1 PR1 G10 FK1.
  rewrite sb_shift_refl in BLE1.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
     [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m1 m2 _ _ FR1). intros i Hi. cbn in Hi.
    destruct (FK1 (bv_unsigned sp - 48 + i) ltac:(rewrite SP1; lia)) as [Ea Wa]. split; [exact Ea | exact (proj1 Wa)]. }
  pose proof SI2 as (RJ2 & _). pose proof RJ2 as (HM2 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply ps_run2. }
  intros ms2 (can2 & E2 & EQ2). subst can2.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x170e8) by (ps_reg X2; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (ps_reg X2; exact (eq_trans (PR1 2 ltac:(unfold callee_saved; lia)) E1_2)).
  assert (E2_4 : getr R2 4 = Z_to_bv 64 (ms_tp B))
    by (ps_reg X2; exact (eq_trans (PR1 4 ltac:(unfold callee_saved; lia)) TP1)).
  assert (E2_8 : getr R2 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R)) by (ps_reg X2; exact G10).
  assert (E2_10 : getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R)) by (ps_reg X2; exact G10).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 pu)
    by (ps_reg X2; exact (eq_trans (PR1 20 ltac:(unfold callee_saved; lia)) E1_20)).
  assert (E2_9 : getr R2 9 = Z_to_bv 64 pv)
    by (ps_reg X2; exact (eq_trans (PR1 9 ltac:(unfold callee_saved; lia)) E1_9)).
  assert (E2_18 : getr R2 18 = Z_to_bv 64 pl)
    by (ps_reg X2; exact (eq_trans (PR1 18 ltac:(unfold callee_saved; lia)) E1_18)).
  assert (E2_19 : getr R2 19 = Z_to_bv 64 pf)
    by (ps_reg X2; exact (eq_trans (PR1 19 ltac:(unfold callee_saved; lia)) E1_19)).
  assert (KR2 : kept_ex [2; 8; 9; 18; 19; 20] regs R2).
  { apply (kept_ex_trans _ regs regs1 R2);
      [apply (kept_ex_trans _ regs R1 regs1); [exact KR1 | apply kept_ex_of_pres; exact PR1] | kept_ex_tac X2]. }
  assert (SP2 : spZ R2 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  change (Z_to_bv 64 0x161c4) with (Z_to_bv 64 ARG_S).
  apply (ps_argc PINS_SET_K (bv_unsigned sp) L A mem md O L1 A1 m2 md1 R REC_PINS_SET [] O1 b R2 pu uri _ SI2).
  { cbn. lia. }
  { rewrite E2_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP2. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK, PINS_SET_K. lia. }
  { rewrite SP2. lia. }
  { exact E2_4. }
  { exact E2_10. }
  { exact E2_11. }
  { rewrite SP2. apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK PINS_SET_K (bv_unsigned sp) L A mem md O L1 A1 m2 md1
                          _ O1 b pu uri (bv_unsigned sp - 48) SI2 RA);
      [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK, PINS_SET_K; lia | lia | exact SU]. }
  { eapply room_slots_mono; [| | exact ROOM6];
      [unfold sb_le, sb_malloc in BLE1 |- *; cbn [sb_live sb_bytes sb_cap] in BLE1 |- *; lia | lia]. }
  intros L3 A3 regs3 m3 md3 O3 SI3 SH3 PR3 FK3.
  cbn [app] in SI3.
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 48)
     [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m2 m3 _ _ FR2). intros i Hi. cbn in Hi.
    destruct (FK3 (bv_unsigned sp - 48 + i) ltac:(rewrite SP2; lia)) as [Ea Wa]. split; [exact Ea | exact (proj1 Wa)]. }
  pose proof SI3 as (RJ3 & _). pose proof RJ3 as (HM3 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
  rewrite E2_1.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply ps_run3. }
  intros ms4 (can4 & E4 & EQ4). subst can4.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4).
  assert (E4_1 : getr R4 1 = Z_to_bv 64 0x170f4) by (ps_reg X4; reflexivity).
  assert (E4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (ps_reg X4; exact (eq_trans (PR3 2 ltac:(unfold callee_saved; lia)) E2_2)).
  assert (E4_4 : getr R4 4 = Z_to_bv 64 (ms_tp B))
    by (ps_reg X4; exact (eq_trans (PR3 4 ltac:(unfold callee_saved; lia)) E2_4)).
  assert (E4_8 : getr R4 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (ps_reg X4; exact (eq_trans (PR3 8 ltac:(unfold callee_saved; lia)) E2_8)).
  assert (E4_10 : getr R4 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (ps_reg X4; exact (eq_trans (PR3 8 ltac:(unfold callee_saved; lia)) E2_8)).
  assert (E4_11 : getr R4 11 = Z_to_bv 64 pf)
    by (ps_reg X4; exact (eq_trans (PR3 19 ltac:(unfold callee_saved; lia)) E2_19)).
  assert (E4_9 : getr R4 9 = Z_to_bv 64 pv)
    by (ps_reg X4; exact (eq_trans (PR3 9 ltac:(unfold callee_saved; lia)) E2_9)).
  assert (E4_18 : getr R4 18 = Z_to_bv 64 pl)
    by (ps_reg X4; exact (eq_trans (PR3 18 ltac:(unfold callee_saved; lia)) E2_18)).
  assert (KR4 : kept_ex [2; 8; 9; 18; 19; 20] regs R4).
  { apply (kept_ex_trans _ regs regs3 R4);
      [apply (kept_ex_trans _ regs R2 regs3); [exact KR2 | apply kept_ex_of_pres; exact PR3] | kept_ex_tac X4]. }
  assert (SP4 : spZ R4 = bv_unsigned sp - 48) by (unfold spZ; rewrite E4_2; apply unsigned_lit; lia).
  change (Z_to_bv 64 0x161c4) with (Z_to_bv 64 ARG_S).
  apply (ps_argc PINS_SET_K (bv_unsigned sp) L A mem md O L3 A3 m3 md3 R REC_PINS_SET [sarg uri] O3 b R4 pf files _ SI3).
  { cbn. lia. }
  { rewrite E4_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP4. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP4. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK, PINS_SET_K. lia. }
  { rewrite SP4. lia. }
  { exact E4_4. }
  { exact E4_10. }
  { exact E4_11. }
  { rewrite SP4. apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK PINS_SET_K (bv_unsigned sp) L A mem md O L3 A3 m3 md3
                          _ O3 b pf files (bv_unsigned sp - 48) SI3 RA);
      [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK, PINS_SET_K; lia | lia | exact SF]. }
  { rewrite SH3. eapply room_slots_mono; [| | exact ROOM6];
      [unfold sb_le, sb_malloc in BLE1 |- *; cbn [sb_live sb_bytes sb_cap] in BLE1 |- *; lia | lia]. }
  intros L5 A5 regs5 m5 md5 O5 SI5 SH5 PR5 FK5.
  cbn [app] in SI5.
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 48)
     [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m3 m5 _ _ FR3). intros i Hi. cbn in Hi.
    destruct (FK5 (bv_unsigned sp - 48 + i) ltac:(rewrite SP4; lia)) as [Ea Wa]. split; [exact Ea | exact (proj1 Wa)]. }
  pose proof SI5 as (RJ5 & _). pose proof RJ5 as (HM5 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM5) as (Hh5 & Hl5 & _).
  rewrite E4_1.
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply ps_run4. }
  intros ms6 (can6 & E6 & EQ6). subst can6.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ6 eq_refl eq_refl) as (R6 & -> & X6).
  assert (E6_1 : getr R6 1 = Z_to_bv 64 0x17100) by (ps_reg X6; reflexivity).
  assert (E6_2 : getr R6 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (ps_reg X6; exact (eq_trans (PR5 2 ltac:(unfold callee_saved; lia)) E4_2)).
  assert (E6_4 : getr R6 4 = Z_to_bv 64 (ms_tp B))
    by (ps_reg X6; exact (eq_trans (PR5 4 ltac:(unfold callee_saved; lia)) E4_4)).
  assert (E6_8 : getr R6 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (ps_reg X6; exact (eq_trans (PR5 8 ltac:(unfold callee_saved; lia)) E4_8)).
  assert (E6_10 : getr R6 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (ps_reg X6; exact (eq_trans (PR5 8 ltac:(unfold callee_saved; lia)) E4_8)).
  assert (E6_11 : getr R6 11 = Z_to_bv 64 pl)
    by (ps_reg X6; exact (eq_trans (PR5 18 ltac:(unfold callee_saved; lia)) E4_18)).
  assert (E6_9 : getr R6 9 = Z_to_bv 64 pv)
    by (ps_reg X6; exact (eq_trans (PR5 9 ltac:(unfold callee_saved; lia)) E4_9)).
  assert (KR6 : kept_ex [2; 8; 9; 18; 19; 20] regs R6).
  { apply (kept_ex_trans _ regs regs5 R6);
      [apply (kept_ex_trans _ regs R4 regs5); [exact KR4 | apply kept_ex_of_pres; exact PR5] | kept_ex_tac X6]. }
  assert (SP6 : spZ R6 = bv_unsigned sp - 48) by (unfold spZ; rewrite E6_2; apply unsigned_lit; lia).
  change (Z_to_bv 64 0x161c4) with (Z_to_bv 64 ARG_S).
  apply (ps_argc PINS_SET_K (bv_unsigned sp) L A mem md O L5 A5 m5 md5 R REC_PINS_SET [sarg uri; sarg files] O5 b R6
           pl lay _ SI5).
  { cbn. lia. }
  { rewrite E6_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP6. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP6. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK, PINS_SET_K. lia. }
  { rewrite SP6. lia. }
  { exact E6_4. }
  { exact E6_10. }
  { exact E6_11. }
  { rewrite SP6. apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK PINS_SET_K (bv_unsigned sp) L A mem md O L5 A5 m5 md5
                          _ O5 b pl lay (bv_unsigned sp - 48) SI5 RA);
      [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK, PINS_SET_K; lia | lia | exact SL]. }
  { rewrite SH5, SH3. eapply room_slots_mono; [| | exact ROOM6];
      [unfold sb_le, sb_malloc in BLE1 |- *; cbn [sb_live sb_bytes sb_cap] in BLE1 |- *; lia | lia]. }
  intros L7 A7 regs7 m7 md7 O7 SI7 SH7 PR7 FK7.
  cbn [app] in SI7.
  assert (FR7 : rw_cells rsegs m7 (bv_unsigned sp - 48)
     [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m5 m7 _ _ FR5). intros i Hi. cbn in Hi.
    destruct (FK7 (bv_unsigned sp - 48 + i) ltac:(rewrite SP6; lia)) as [Ea Wa]. split; [exact Ea | exact (proj1 Wa)]. }
  pose proof SI7 as (RJ7 & _ & _ & _ & _ & RA7 & _). pose proof RJ7 as (HM7 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM7) as (Hh7 & Hl7 & _).
  assert (Q9 : reg_get regs7 9 = Z_to_bv 64 pv) by exact (eq_trans (PR7 9 ltac:(unfold callee_saved; lia)) E6_9).
  rewrite E6_1.
  eapply evt_SR_canon; [ | exact Hh7 | exact Hl7 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q9. eapply ps_run5. exact HPV. }
  intros ms8 (can8 & E8 & EQ8). subst can8.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ8 eq_refl eq_refl) as (R8 & -> & X8).
  assert (E8_1 : getr R8 1 = Z_to_bv 64 0x17118) by (ps_reg X8; reflexivity).
  assert (E8_2 : getr R8 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (ps_reg X8; exact (eq_trans (PR7 2 ltac:(unfold callee_saved; lia)) E6_2)).
  assert (E8_4 : getr R8 4 = Z_to_bv 64 (ms_tp B))
    by (ps_reg X8; exact (eq_trans (PR7 4 ltac:(unfold callee_saved; lia)) E6_4)).
  assert (E8_8 : getr R8 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (ps_reg X8; exact (eq_trans (PR7 8 ltac:(unfold callee_saved; lia)) E6_8)).
  assert (E8_10 : getr R8 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (ps_reg X8; exact (eq_trans (PR7 8 ltac:(unfold callee_saved; lia)) E6_8)).
  assert (E8_11 : getr R8 11 = Z_to_bv 64 (psel pv 0x108b0)) by (ps_reg X8; reflexivity).
  assert (KR8 : kept_ex [2; 8; 9; 18; 19; 20] regs R8).
  { apply (kept_ex_trans _ regs regs7 R8);
      [apply (kept_ex_trans _ regs R6 regs7); [exact KR6 | apply kept_ex_of_pres; exact PR7] | kept_ex_tac X8]. }
  assert (SP8 : spZ R8 = bv_unsigned sp - 48) by (unfold spZ; rewrite E8_2; apply unsigned_lit; lia).
  assert (SV4 : sarg (match verdict with Some x => Some x | None => Some (bstr "-"%string) end) =
                darg verdict (bstr "-"%string)) by (destruct verdict; reflexivity).
  assert (SRC4 : arg_s_src B L7 A7 (bv_unsigned sp - 48) m7 (psel pv 0x108b0)
                   (match verdict with Some x => Some x | None => Some (bstr "-"%string) end)).
  { destruct verdict as [x|].
    - pose proof SV as SV'. cbn [str_arg] in SV'. destruct SV' as (NZ & _).
      unfold psel. rewrite (proj2 (Z.eqb_neq pv 0) NZ).
      apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK PINS_SET_K (bv_unsigned sp) L A mem md O L7 A7 m7 md7
               _ O7 b pv (Some x) (bv_unsigned sp - 48) SI7 RA);
        [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK, PINS_SET_K; lia | lia | exact SV].
    - cbn [str_arg] in SV. subst pv. unfold psel. cbn [Z.eqb].
      apply ps_dash; [exact RA7 | unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia]. }
  change (Z_to_bv 64 0x161c4) with (Z_to_bv 64 ARG_S).
  apply (ps_argc PINS_SET_K (bv_unsigned sp) L A mem md O L7 A7 m7 md7 R REC_PINS_SET [sarg uri; sarg files; sarg lay]
           O7 b R8 (psel pv 0x108b0) (match verdict with Some x => Some x | None => Some (bstr "-"%string) end) _ SI7).
  { cbn. lia. }
  { rewrite E8_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP8. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP8. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK, PINS_SET_K. lia. }
  { rewrite SP8. lia. }
  { exact E8_4. }
  { exact E8_10. }
  { exact E8_11. }
  { rewrite SP8. exact SRC4. }
  { rewrite SV4, SH7, SH5, SH3. eapply room_slots_mono; [| | exact ROOM6];
      [unfold sb_le, sb_malloc in BLE1 |- *; cbn [sb_live sb_bytes sb_cap] in BLE1 |- *; lia | lia]. }
  intros L9 A9 regs9 m9 md9 O9 SI9 SH9 PR9 FK9.
  rewrite SV4 in SI9, SH9. cbn [app] in SI9.
  assert (FR9 : rw_cells rsegs m9 (bv_unsigned sp - 48)
     [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m7 m9 _ _ FR7). intros i Hi. cbn in Hi.
    destruct (FK9 (bv_unsigned sp - 48 + i) ltac:(rewrite SP8; lia)) as [Ea Wa]. split; [exact Ea | exact (proj1 Wa)]. }
  assert (T2 : getr regs9 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (PR9 2 ltac:(unfold callee_saved; lia)) E8_2).
  assert (T8 : getr regs9 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by exact (eq_trans (PR9 8 ltac:(unfold callee_saved; lia)) E8_8).
  assert (KT9 : kept_ex [2; 8; 9; 18; 19; 20] regs regs9)
    by exact (kept_ex_trans _ regs R8 regs9 KR8 (kept_ex_of_pres _ _ _ PR9)).
  rewrite E8_1.
  eapply SR_mono.
  { apply (ps_tail L A regs mem md O L9 A9 m9 md9 R [sarg uri; sarg files; sarg lay; darg verdict (bstr "-"%string)] O9 b
             (sb_malloc (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length (sarg uri)) + 1))
                (Z.of_nat (length (sarg files)) + 1)) (Z.of_nat (length (sarg lay)) + 1))
                (Z.of_nat (length (darg verdict (bstr "-"%string))) + 1))
             regs9 PRE SI9 H16 eq_refl).
    - repeat constructor; assumption.
    - rewrite SH9, SH7, SH5, SH3.
      unfold sb_le, sb_malloc in BLE1 |- *. cbn [sb_live sb_bytes sb_cap] in BLE1 |- *. lia.
    - eapply room_slots_mono; [| | exact ROOM6];
        [unfold sb_le, sb_malloc; cbn [sb_live sb_bytes sb_cap]; lia | lia].
    - exact FRM.
    - exact FR9.
    - exact T2.
    - exact T8.
    - exact KT9. }
  intros c' (Rc & code & ESC & (fx' & L' & A' & regs' & mem' & md' & O' & EC & FPK & POST & A10' & GREP' & OWN & OK
    & BLK & RA' & F18' & INIT & REG & GR' & RES')).
  rewrite SEGS in EC, GREP', OK, RA', F18'.
  exists fx', L', A', regs', mem', md', (fst (rec_answer_code Rc code)), O', code.
  split; [exact ESC|]. split; [exact EC|]. split; [exact FPK|]. split; [exact POST|]. split; [exact A10'|].
  split; [exact GREP'|]. split; [exact OWN|]. split; [exact OK|]. split; [exact BLK|]. split; [exact RA'|].
  split; [exact F18'|]. split; [exact INIT|]. split; [exact REG|]. split; [exact GR' | exact RES'].
Qed.

End P.
