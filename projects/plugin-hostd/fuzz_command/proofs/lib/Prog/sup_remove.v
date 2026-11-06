(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module names, addresses and numbers changed; 411 of its 592 lines of code are new or changed and 367 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecCore.
Import ListNotations.
Open Scope Z_scope.

Lemma srm_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n))
                     a0 b0 b1 b2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15f1c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 24) [C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15ec8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 24%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 24%nat junk [] [8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  carve_frame 8%nat ST.
  clear FR0.
  do 10 step.
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

Lemma srm_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x15efc) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     a0 (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 24) [C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15ec8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 24%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 24%nat junk [] [8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  carve_frame 8%nat ST.
  clear FR0.
  do 10 step.
  rewrite rc_sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma srm_seg_rec :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m e [CB 8 junk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x15f30) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 (Z_to_bv 64 e) s1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b1c) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15f1c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EW.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rc_cells_rebytes _ _ _ [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  do 3 step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; eassumption.
Qed.

Lemma srm_seg_jrec :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m e [CB 8 junk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x15f30) sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 (Z_to_bv 64 e) s1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b1c) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15efc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EW.
  step. eapply srm_seg_rec. exact EW.
Qed.

Lemma srm_seg_tail :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 : word),
  rw_cells rsegs m (bv_unsigned sp0 + -24) [C8 s01; C8 s00; C8 ra0] -> 32 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 s0 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                     a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15bc8) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15f30) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 9 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -32 + 32)) with sp0
    by (replace (bv_unsigned sp0 + -32 + 32) with (bv_unsigned sp0) by ring; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma srm_run_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat) (junk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 junk] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x15f30) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a0 (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a0 b2
                     a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b1c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 24) [C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15ec8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n junk ST LO LO2 NC Hn EW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  eapply evt_cut; [eapply srm_seg_lt; [exact ST | exact LO | exact LO2 | exact NC | exact Hn] |].
  intros ms1 (b0 & b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1).
  assert (EW1 : rw_cells rsegs m1 (0x33d58 + 56 * Z.of_nat n) [CB 8 junk]).
  { apply (rw_cells_transport rsegs [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m1 _ _ EW MU1 WM1).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  eapply evt_cut; [eapply srm_seg_rec; exact EW1 |].
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
  { apply (rw_cells_transport rsegs [(0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m1 m2 _ _ FR1 MU2 WM2).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  split; [|exact EN2].
  apply (rw_cells_transport rsegs [(0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m1 m2 _ _ NC1 MU2 WM2).
  cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import answer_c rec_calls_free_c xstrdup_c arg_i_c
sup_remove_c.

Lemma srm_glob : forall a, 0x33d10 <= a < 0x34108 -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N.
Proof. intros a H. unfold GLOB_LO. change (Z.of_nat GLOB_N) with 1020. lia. Qed.

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
Hypothesis ARGI : arg_i_contract B API.
Hypothesis ANS : forall fx' : YK11.FPState, answer_contract (fx := fx') B API.

Definition srm_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (id : Z) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
    sup_remove_m R id = (R', t) /\
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    fp_kept fx fx' /\
    call_post_rec B (aa_MR API) SUP_REMOVE_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep (ms_segs B) L' A' mem' R' O' /\ owns_new L A O O' /\
    In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
    ~ In q (map fst O') /\
    Mem.bytes_at (ms_segs B) mem' q (t ++ [Z_to_bv 8 0]) /\
    others_kept (ms_segs B) L A mem L' A' mem' O /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
    ro_agree (ms_segs B) mem' /\ f18_words (ms_segs B) mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_mallocs b [Z.of_nat (length (dec id)) + 1; Z.of_nat (length t) + 1; Z.of_nat (length t) + 1]) /\
    res_ok_slots A' (sb_shift b A A').

Lemma srm_apart : forall q n lo len, (forall i, 0 <= i < n -> ~ in_img B (q + i)) -> 0 < n ->
  0x33d10 <= lo -> lo + len <= 0x34108 -> 0 < len -> iv_apart q n lo len.
Proof using SEGS.
  intros q n lo len H Hn H1 H2 H3. unfold iv_apart.
  destruct (Z_le_gt_dec (q + n) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec (lo + len) q) as [D'|D']; [right; exact D'|]. exfalso.
  apply (H (Z.max q lo - q)); [lia|]. replace (q + (Z.max q lo - q)) with (Z.max q lo) by lia.
  apply (glob_in_img B SEGS). apply srm_glob. lia.
Qed.

Lemma srm_arg : forall L A regs mem md id R O b Lc Ac mc mdc Oc regs_c,
  call_pre_t B API SUP_REMOVE_K L A regs mem md -> -2 ^ 31 <= id < 2 ^ 31 ->
  sinv B API 12384 (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_REMOVE []) Oc b ->
  (length (r_calls R) <= 16)%nat ->
  (length (snd (sup_remove_m R id)) <= 16)%nat ->
  sb_le (sb_shift b A Ac) b ->
  room_slots (sb_mallocs b [Z.of_nat (length (dec id)) + 1; 17; 17]) 17 ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 24) [C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  rw_cells rsegs mc (rec_entry G_REC REC_SC R) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 0)] ->
  getr regs_c 1 = Z_to_bv 64 0x15f30 -> getr regs_c 2 = Z_to_bv 64 (spZ regs - 32) ->
  getr regs_c 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr regs_c 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr regs_c 11 = Z_to_bv 64 id ->
  kept_ex [2; 8; 9] regs regs_c ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 ARG_I) mc (seg_rom rsegs)) mdc) (srm_ret L A regs mem md id R O b).
Proof using SEGS ERRNO_LOW GOWN GERR AX CTX SLACK ARGI ANS.
  intros L A regs mem md id R O b Lc Ac mc mdc Oc regs_c PRE HID SI H16 LT BLE ROOM FRM FR EN
    C1 C2 HC8 C10 C11 KE.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_REMOVE_K in HCEIL, HWS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  set (e := rec_entry G_REC REC_SC R) in *.
  assert (EB : 0x33d10 <= e /\ e + 56 <= 0x34108 /\ e mod 8 = 0).
  { unfold e, rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE. split; [lia|]. split; [lia|].
      replace (0x33d48 + 16 + 56 * Z.of_nat (length (r_calls R))) with ((26539 + 7 * Z.of_nat (length (r_calls R))) * 8)
        by lia.
      apply Z.mod_mul. lia.
    - unfold REC_SC. split; [lia|]. split; [lia|]. reflexivity. }
  destruct EB as (EB1 & EB2 & EB3).
  pose proof (dec_length id HID) as DL.
  assert (SPc : spZ regs_c = bv_unsigned sp - 32) by (unfold spZ; rewrite C2; apply unsigned_lit; lia).
  assert (PREc : call_pre_t B API ARG_I_K Lc Ac regs_c mc mdc).
  { split.
    - apply (call_pre_k_of_rjr B _ 12384 (bv_unsigned sp) rec_area _ L A mem md Lc Ac mc mdc ARG_I_K regs_c RJ).
      + rewrite C1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SPc. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SPc. unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SPc. lia.
      + exact (eq_trans (KE 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)) HTP).
    - rewrite SPc. lia. }
  assert (ROOMa : room_slots (sb_malloc (sb_shift b A Ac) (Z.of_nat (length (dec id)) + 1))
                    (Z.of_nat (length (dec id)) + 1)).
  { apply (room_slots_mono _ (sb_mallocs b [Z.of_nat (length (dec id)) + 1; 17; 17]) _ 17); [| lia | exact ROOM].
    unfold sb_mallocs. cbn [fold_left].
    apply (sb_le_trans _ (sb_malloc b (Z.of_nat (length (dec id)) + 1))); [exact (sb_malloc_mono _ _ _ BLE)|].
    apply (sb_le_trans _ (sb_malloc (sb_malloc b (Z.of_nat (length (dec id)) + 1)) 17)); apply sb_le_malloc; lia. }
  pose proof (rc_c44_bytes mc e _ _ EN) as (_ & NA0).
  pose proof ARGI as AI. unfold arg_i_contract in AI. rewrite SEGS in AI.
  eapply SR_bind.
  { apply (AI Lc Ac regs_c mc mdc e id 0 (sb_shift b A Ac) PREc C10 C11 HID).
    - exact EB3.
    - unfold REC_SC. lia.
    - unfold CALL_SIZE, G_REC, REC_SIZE. lia.
    - apply glob_wr_at; [unfold GLOB_LO; lia | unfold GLOB_LO, CALL_SIZE; change (Z.of_nat GLOB_N) with 1020; lia |
                         unfold CALL_SIZE; lia].
    - exact NA0.
    - lia.
    - exact F18.
    - exact FRM.
    - exact RS.
    - exact ROOMa.
    - exact RA. }
  intros c2 RET.
  destruct RET as (fx2 & L2 & A2 & R2 & m2 & md2 & -> & FPK2 & BKP & UB & BYS & RA2 & GK & F182 & RGN & ALT).
  destruct ALT as [(C6 & _) | (_ & p & POST & PNZ & PAL & FRESH & (l1 & l2 & BL2 & BL1) & NA & AR & PB & INIT & RES2)];
    [lia|].
  unfold blocks_kept in BKP.
  rewrite SEGS in BKP, RA2, F182, NA, AR, PB.
  pose proof POST as (PM & PW & PB' & PL & PA & PR & PV & PF & PK & PS).
  rewrite SEGS in PF.
  destruct FRESH as (FP1 & FP2 & FP3).
  rewrite SEGS, C1.
  assert (KREC : forall a, 0x33d10 <= a < 0x34108 ->
            ~ (e + CALL_OFF_NARGS <= a < e + CALL_OFF_NARGS + 4) ->
            ~ (e + CALL_OFF_ARGS + 8 * 0 <= a < e + CALL_OFF_ARGS + 8 * 0 + 8) ->
            mbyte rsegs m2 a = mbyte rsegs mc a).
  { intros a Ha N1 N2.
    assert (GA : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N) by (apply srm_glob; exact Ha).
    apply PF.
    - right. exact (glob_in_img B SEGS a GA).
    - exact (GOWN _ _ _ _ a HM (glob_in a GA)).
    - exact (GOWN _ _ _ _ a PM (glob_in a GA)).
    - intros [Hs|He]; [rewrite SPc in Hs; unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK in Hs; lia |
                       exact (GERR a (glob_in a GA) He)].
    - intros [Hn|[Ha'|Hp]]; [exact (N1 Hn) | exact (N2 Ha') |].
      apply (FP3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact (glob_in_img B SEGS a GA). }
  assert (KST : forall a, bv_unsigned sp - 32 <= a < bv_unsigned sp ->
            mbyte rsegs m2 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m2 a)).
  { intros a Ha. apply PF.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L2 A2 m2 md2 a PM Ho). lia.
    - intros [Hs|He]; [rewrite SPc in Hs; lia | lia].
    - intros [Hn|[Ha'|Hp]]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -24) [C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { replace (bv_unsigned sp + -24) with (bv_unsigned sp - 24) by ring.
    apply (rw_cells_transfer rsegs mc); [exact FR|]. intros i Hi. cbn in Hi.
    destruct (KST (bv_unsigned sp - 24 + i) ltac:(lia)) as [E1 E2]. split; [exact E1 | exact (proj1 E2)]. }
  assert (DJ : forall a n, In (a, n) (blocks Lc Ac) -> 0 < n -> a <> p).
  { intros a n Hin Hn Ea. subst a.
    pose proof (mr_blocks_disjoint B _ LAWS L2 A2 m2 md2 PM) as PD. rewrite BL2 in PD. rewrite BL1 in Hin.
    destruct (YI04.pairwise_app_mid _ _ _ _ _ PD Hin) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  assert (RJ2 : rjr B (aa_MR API) 12384 (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md L2 A2 m2 md2).
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW 12384 (bv_unsigned sp) rec_area _ L A mem md Lc Ac mc mdc ARG_I_K regs_c
             _ (fun _ => False) L2 A2 R2 m2 md2 RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST)).
    - rewrite SPc. unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
    - rewrite SPc. lia.
    - intros a Ha Hf. cbv beta in Ha. destruct Ha as [Hn|[Ha'|Hp]].
      + unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, CALL_OFF_NARGS in *. split; lia.
      + unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, CALL_OFF_ARGS in *. split; lia.
      + exfalso. destruct Hf as [Hf|(Hf & _)]; [lia|].
        apply (FP3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Hf.
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ H1 H2. exfalso. exact (H2 (UB p0 n0 H1)).
    - exact RGN.
    - intros Hf. rewrite INIT in Hf. discriminate. }
  assert (GR2 : g_rec_rep rsegs L2 A2 m2 (rec_record R REC_REMOVE [dec id])
                  (Oc ++ [(p, Z.of_nat (length (dec id)) + 1)])).
  { unfold g_rec_rep in *.
    apply (rec_rep_arg rsegs G_REC REC_SC Lc Ac mc L2 A2 m2 R REC_REMOVE [] Oc (dec id) p
             (Z.of_nat (length (dec id)) + 1) GR).
    - cbn. lia.
    - exact NA.
    - exact AR.
    - intros a Ha N1 N2. apply KREC; [unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia | exact N1 | exact N2].
    - intros a Ha _. apply glob_writable. apply srm_glob. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha. lia.
    - intros [a n] Hpn. cbn [fst snd].
      pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ (a, n) GR Hpn) as Hb.
      split.
      + rewrite BL2. rewrite BL1 in Hb. apply in_app_or in Hb as [H|H]; apply in_or_app; [left; exact H | right; right; exact H].
      + intros i Hi. exact (BKP a n i Hb (fun f => f) Hi).
    - intros Hin. apply in_map_iff in Hin as ([a n] & Ea & Hin). cbn [fst] in Ea.
      exact (DJ a n (rec_rep_O_in _ _ _ _ _ _ _ _ (a, n) GR Hin) (rec_rep_pos _ _ _ _ _ _ _ _ (a, n) GR Hin) Ea).
    - exact PNZ.
    - rewrite BL2. apply in_or_app. right. left. reflexivity.
    - apply dec_no0.
    - unfold LMAX. lia.
    - unfold LMAX. lia.
    - exact PB.
    - apply srm_apart; [exact FP3 | lia | unfold G_REC; lia | unfold G_REC, REC_SIZE; lia | unfold REC_SIZE; lia].
    - apply srm_apart; [exact FP3 | lia | unfold REC_SC; lia | unfold REC_SC, SC_SIZE; lia | unfold SC_SIZE; lia]. }
  assert (ON2 : owns_new L A O (Oc ++ [(p, Z.of_nat (length (dec id)) + 1)])).
  { intros pn Hpn. apply in_app_or in Hpn as [H|[H|[]]]; [exact (ON pn H)|]. subst pn.
    destruct (in_dec pair_dec (p, Z.of_nat (length (dec id)) + 1) O) as [H|H]; [left; exact H|].
    right. intros Hb.
    destruct (in_dec pair_dec (p, Z.of_nat (length (dec id)) + 1) (blocks Lc Ac)) as [H2|H2].
    - exact (DJ _ _ H2 ltac:(lia) eq_refl).
    - exact (H (B2 _ Hb H2)). }
  assert (B12 : forall pn, In pn (blocks L2 A2) ->
            (In pn (blocks L A) /\ ~ In pn O) \/ In pn (Oc ++ [(p, Z.of_nat (length (dec id)) + 1)])).
  { intros pn Hpn. rewrite BL2 in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite BL1; apply in_or_app; left; exact H)) as [X|X];
        [left; exact X | right; apply in_or_app; left; exact X].
    - right. apply in_or_app. right. left. exact H.
    - destruct (B1 pn ltac:(rewrite BL1; apply in_or_app; right; exact H)) as [X|X];
        [left; exact X | right; apply in_or_app; left; exact X]. }
  assert (B22 : forall pn, In pn (blocks L A) -> ~ In pn (blocks L2 A2) -> In pn O).
  { intros pn H1 H2. apply B2; [exact H1|]. intros H3. apply H2. rewrite BL2. rewrite BL1 in H3.
    apply in_app_or in H3 as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
  assert (EQB : sb_shift b A A2 = sb_malloc (sb_shift b A Ac) (Z.of_nat (length (dec id)) + 1)).
  { rewrite (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2 l1 l2 p _ BL2 BL1). symmetry. apply sb_shift_trans. }
  assert (SI2 : sinv B API 12384 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 (rec_record R REC_REMOVE [dec id])
                  (Oc ++ [(p, Z.of_nat (length (dec id)) + 1)]) b).
  { split; [exact RJ2|]. split; [exact GR2|]. split; [exact ON2|]. split; [exact B12|]. split; [exact B22|].
    split; [exact RA2|]. split; [exact F182|]. rewrite EQB. exact RES2. }
  destruct (mr_model B _ LAWS L2 A2 m2 md2 PM) as (Hh2 & Hl2 & _).
  assert (Q2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -32)).
  { replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by ring.
    exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) C2). }
  assert (Q8 : reg_get R2 8 = Z_to_bv 64 e) by exact (eq_trans (PR 8 ltac:(unfold callee_saved; lia)) HC8).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2, Q8.
    eapply srm_seg_tail; [exact FR2 | lia]. }
  intros ms3 (can3 & -> & EQ3).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = getr regs 1) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_11 : getr R3 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_12 : getr R3 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X3 eq_refl); simp_regs; reflexivity).
  assert (RP3 : regs_preserved regs R3).
  { apply (kept_ex_pres [2; 8; 9]).
    - apply (kept_ex_trans _ regs regs_c R3 KE).
      apply (kept_ex_trans _ regs_c R2 R3 (kept_ex_of_pres _ _ _ PR)).
      kept_ex_tac X3.
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X3 eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (AK : ANSWER_K <= 12384) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof FPK2 as (FZ2 & _).
  eapply SR_mono.
  { apply (sinv_answer (fx := fx2) B API SEGS ERRNO_LOW AX CTX (ANS fx2) SLACK 12384 L A regs mem md O L2 A2 R3 m2 md2
             (rec_record R REC_REMOVE [dec id]) (Oc ++ [(p, Z.of_nat (length (dec id)) + 1)]) b
             (sb_malloc b (Z.of_nat (length (dec id)) + 1)) e 0x10417 (REC_REMOVE, [dec id]) REC_MOD_HOST_SHAPE true
             PRE AK SI2 E3_1 ltac:(unfold spZ; rewrite E3_2; reflexivity) RP3 E3_10 E3_11
             ltac:(rewrite E3_12; reflexivity)).
    - intros _. apply mod_host_shape. exact RA2.
    - intros _ _. exact (ans_entry_record R REC_REMOVE [dec id] H16).
    - exact FZ2.
    - rewrite EQB. exact (sb_malloc_mono _ _ _ BLE).
    - unfold sup_remove_m, rec_stub in LT.
      apply (room_slots_mono _ (sb_mallocs b [Z.of_nat (length (dec id)) + 1; 17; 17]) _ 17); [| lia | exact ROOM].
      unfold sb_mallocs. cbn [fold_left]. rewrite EQB.
      apply sb_malloc_le2; [apply sb_malloc_le2; [exact (sb_malloc_mono _ _ _ BLE) | lia] | lia]. }
  intros c' TR.
  destruct TR as (fx' & L' & A' & regs' & mem' & md' & O' & q & Ec & FPK & CP & G10 & GRf & ONf & BLf & INq & FRq & NIq
    & BYq & OKf & APf & ROf & F18f & INf & RGf & SBf & RSf).
  unfold srm_ret.
  exists fx', L', A', regs', mem', md', (fst (sup_remove_m R id)), O', (snd (sup_remove_m R id)), q.
  split; [apply surjective_pairing|].
  split; [exact Ec|].
  split; [exact (fp_kept_trans _ _ _ FPK2 FPK)|].
  split; [exact CP|]. split; [exact G10|]. split; [exact GRf|]. split; [exact ONf|].
  split; [exact INq|]. split; [exact FRq|]. split; [exact NIq|]. split; [exact BYq|]. split; [exact OKf|].
  split; [exact BLf|]. split; [exact APf|]. split; [exact ROf|]. split; [exact F18f|]. split; [exact INf|].
  split; [exact RGf|]. split; [exact SBf|]. exact RSf.
Qed.

Theorem sup_remove_holds : sup_remove_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GOWN GERR AX CTX SLACK RCF ARGI ANS.
  unfold sup_remove_contract.
  intros L A regs mem md id R O b PRE GA HID GR RA FRM F18 RES ROOM.
  change (SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 SUP_REMOVE) mem (seg_rom (ms_segs B))) md)
            (srm_ret L A regs mem md id R O b)).
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_REMOVE_K in HCEIL, HWS.
  rewrite SEGS in GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API 12384 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 12384) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _ & _ & HX & _).
  pose proof HX as (_ & _ & _ & _ & _ & _ & HCODE & _).
  assert (LT : (length (snd (sup_remove_m R id)) <= 16)%nat).
  { unfold sup_remove_m, rec_stub. pose proof (stub_len R REC_REMOVE [dec id] REC_MOD_HOST_SHAPE true HCODE) as H.
    assert (LX : length REC_MOD_HOST_SHAPE = 6%nat) by reflexivity. rewrite LX in H. exact H. }
  set (n := length (r_calls R)) in *.
  assert (NC : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact G3]).
  destruct (Nat.lt_ge_cases n 16) as [Hn|Hn].
  - destruct (glob_rw_cells mem (0x33d58 + 56 * Z.of_nat n) 8 ltac:(unfold GLOB_LO; lia)
                ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
    assert (EE : rec_entry G_REC REC_SC R = 0x33d58 + 56 * Z.of_nat n)
      by (rewrite (rec_entry_lt G_REC REC_SC R Hn); fold n; unfold G_REC, OFF_CALLS, CALL_SIZE; lia).
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply srm_run_lt; [exact ST | lia | lia | exact NC | exact Hn | exact EW]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & FR1 & NC1 & EN1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    pose proof (sinv_record_lt B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                  REC_REMOVE SI0 Hn ltac:(unfold REC_FN_COUNT, REC_REMOVE; lia) MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EN1) as SI1.
    apply (srm_arg L A regs mem md id R O b L A m1 md O R1 PRE HID SI1
             ltac:(change (length (r_calls R)) with n; lia) LT
             ltac:(rewrite sb_shift_refl; apply sb_le_refl) ROOM FRM).
    + exact FR1.
    + rewrite EE. exact EN1.
    + rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity.
    + rewrite EE, (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity.
    + rewrite EE, (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity.
    + rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs. exact GA.
    + kept_ex_tac X1.
  - assert (H16 : n = 16%nat) by lia.
    assert (NC16 : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 16)]) by (rewrite H16 in NC; exact NC).
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply srm_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x15efc) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_9 : getr R1 9 = getr regs 10) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
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
      assert (R2' : getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32))
        by exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
      assert (R8' : getr regs' 8 = Z_to_bv 64 0x33d10) by exact (eq_trans (RP' 8 ltac:(unfold callee_saved; lia)) E1_8).
      assert (R9' : getr regs' 9 = getr regs 10) by exact (eq_trans (RP' 9 ltac:(unfold callee_saved; lia)) E1_9).
      assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 24) [C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
      { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
        apply FRK. rewrite SP1. lia. }
      destruct (glob_rw_cells m' 0x33d10 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
      eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of.
        assert (Q8 : reg_get regs' 8 = Z_to_bv 64 0x33d10) by exact R8'.
        rewrite Q8. eapply srm_seg_jrec. exact EW. }
      intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX 12384 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                  _ REC_REMOVE POST ltac:(unfold REC_FN_COUNT, REC_REMOVE; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      apply (srm_arg L A regs mem md id R O b L' A' m2 md' Oc' R2 PRE HID SI2
               ltac:(change (length (r_calls R)) with n; lia) LT
               ltac:(rewrite sb_shift_refl in BLE; exact BLE) ROOM FRM).
      * apply (rw_cells_transport rsegs [(0x33d10, 0x33d10 + 8)] m' m2 _ _ FR' MU2 WM2).
        cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
      * rewrite (rec_entry_full G_REC REC_SC R H16). exact EN2.
      * rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity.
      * rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs. exact R2'.
      * rewrite (rec_entry_full G_REC REC_SC R H16), (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; reflexivity.
      * rewrite (rec_entry_full G_REC REC_SC R H16), (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; reflexivity.
      * rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs. exact (eq_trans R9' GA).
      * apply (kept_ex_trans _ regs R1 R2); [kept_ex_tac X1|].
        apply (kept_ex_trans _ R1 regs' R2 (kept_ex_of_pres _ _ _ RP')). kept_ex_tac X2.
Qed.

End P.
