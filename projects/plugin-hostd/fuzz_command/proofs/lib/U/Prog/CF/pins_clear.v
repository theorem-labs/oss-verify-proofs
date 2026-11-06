(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 580 of its 637 lines of code are new or changed and 778 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import mix_call_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma pc_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma pc_nz : forall rf, -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 -> bv_eqb (Z_to_bv 64 rf) (Z_to_bv 64 0) = false.
Proof.
  intros rf Hr N. unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616. rewrite Zmod_0_l. intros H.
  apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. lia.
Qed.

Lemma pc_run0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  evt rsegs (fun ms' => exists m' junk,
      ms' = MS (mkR (Z_to_bv 64 0x171cc) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 s0 a0 (Z_to_bv 64 21)
                    a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
      rw_cells rsegs m' (bv_unsigned sp - 32) [CB 8 junk; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171b0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma pc_run1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x171d8) sp gp tp t0 t1 t2 a0 s1 a0 s1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171cc) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma pc_epi : forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp1 rav s0v s1v : word) (junk : list byte),
  rw_cells rsegs m (bv_unsigned sp1) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] -> bv_unsigned sp1 + 32 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp1 + 32)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5
                                      a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x17168) fc None m (seg_rom rsegs))
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17208) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp1 rav s0v s1v junk FR SPR.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 5 step.
  apply evt_done. reflexivity.
Qed.

Lemma pc_run_ref : forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp1 rav s0v s1v : word) (junk : list byte) (rf cd : Z),
  rw_cells rsegs m (bv_unsigned sp1) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] -> bv_unsigned sp1 + 32 < 2 ^ 64 ->
  rw_cells rsegs m 0x34028 [C4 (Z_to_bv 64 rf)] -> rw_cells rsegs m 0x3402c [C4 (Z_to_bv 64 cd)] ->
  -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 -> -2 ^ 31 <= cd < 2 ^ 31 ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp1 + 32)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 cd)
                                      a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x17168) fc None m (seg_rom rsegs))
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171d8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp1 rav s0v s1v junk rf cd FR SPR RC RC2 Hrf Nrf Hcd.
  do 4 step. rewrite pc_sx32 by lia. rewrite (pc_nz rf Hrf Nrf). cbv iota.
  do 2 step. rewrite pc_sx32 by lia.
  eapply pc_epi; [exact FR | exact SPR].
Qed.

Lemma pc_run_mix : mix_call_contract ->
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e h : Z) (args : list (word * list byte))
    (sp1 rav s0v s1v : word) (junk : list byte),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 96 <= bv_unsigned sp1 -> 0x343e8 <= lo ->
  rw_cells rsegs m (bv_unsigned sp1) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells rsegs m 0x34028 [C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m e (le4 (Z_to_bv 64 21) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) ->
  0x33ff0 <= e -> e + 56 <= 0x343e8 -> e mod 8 = 0 -> (length args <= 6)%nat ->
  (forall k p, nth_error args k = Some p -> mc_arg m (bv_unsigned sp1 - 96) (bv_unsigned sp1) e k p) ->
  rw_cells rsegs m 0x343d8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  evt rsegs (fun ms' => exists t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp1 + 32)) gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 0)
                     b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x17168) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 96, bv_unsigned sp1); (0x343d8, 0x343e0)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x343d8 [C8 (Z_to_bv 64 (mixcall h 21 (map snd args)))])
    (MS (mkR ra sp1 gp tp t0 t1 t2 (Z_to_bv 64 e) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171d8) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e h args sp1 rav s0v s1v junk MI ST LO LO2 FR RC EF E0 E1 EA LA HARG ES Hh.
  assert (MIX' := MIX). unfold mix_call_contract, MIX_CALL_FRAME in MIX'.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned sp1 - 96, bv_unsigned sp1); (0x343d8, 0x343e0)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step. try (rewrite pc_sx32 by lia). if_true.
  do 3 step.
  call (MIX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 21 args).
  - exact MI.
  - exact ST.
  - lia.
  - lia.
  - exact LA.
  - rewrite unsigned_lit by lia. exact EF.
  - rewrite unsigned_lit by lia. left. lia.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. exact EA.
  - intros k p Hk. rewrite unsigned_lit by lia. exact (HARG k p Hk).
  - eapply ro_bytes_at; [exact MI | unfold FNV_B0_ADDR; lia | rewrite length_le8; unfold FNV_B0_ADDR; lia |].
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  - unfold FNV_B0_ADDR. left. lia.
  - rewrite (unsigned_lit h) by lia.
    do 8 step.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecSeq RecStep RecGlue RecTail RecAnsB RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import xmalloc_c record_c arg_s_c answer_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import pins_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

Lemma pc_cell4 : forall m a v, GLOB_LO <= a -> a + 4 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le4 v) -> rw_cells rsegs m a [C4 v].
Proof.
  intros m a v H1 H2 H. apply (rw_cells_same_bytes _ _ [CB (length (le4 v)) (le4 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le4; lia | exact H].
  - cbn. split; exact I.
  - reflexivity.
  - cbn [cells_size csize]. rewrite length_le4. reflexivity.
Qed.

Lemma pc_pad_le : forall e c a, e <= c -> a < e + (- e) mod 8 -> a < 8 * ((c + 7) / 8).
Proof.
  intros e c a H1 H2.
  pose proof (Z.div_mod (- e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (- e) 8 ltac:(lia)).
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)).
  lia.
Qed.

Lemma pc_present : forall segs m a, present m a -> mbyte segs m a <> None.
Proof. intros segs m a [b E]. unfold mbyte. rewrite E. discriminate. Qed.

Lemma pc_frame_keep : forall m m' a junk v1 v2 v3, rw_cells rsegs m a [CB 8 junk; C8 v1; C8 v2; C8 v3] ->
  (forall x, a <= x < a + 32 -> mbyte rsegs m' x = mbyte rsegs m x /\ (writable_at rsegs m x <-> writable_at rsegs m' x)) ->
  rw_cells rsegs m' a [CB 8 junk; C8 v1; C8 v2; C8 v3].
Proof.
  intros m m' a junk v1 v2 v3 H K. apply (rw_cells_transfer rsegs m); [exact H|]. intros i Hi. cbn in Hi.
  destruct (K (a + i) ltac:(lia)) as [E W]. split; [exact E | exact (proj1 W)].
Qed.

Lemma pc_pres : forall regs R1 R2 R3 R4 R5,
  (forall r, callee_saved r -> r <> 2 -> r <> 9 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  regs_preserved R1 R2 ->
  (forall r, callee_saved r -> r <> 8 -> getr R3 (Z_to_bv 5 r) = getr R2 (Z_to_bv 5 r)) ->
  regs_preserved R3 R4 ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R5 (Z_to_bv 5 r) = getr R4 (Z_to_bv 5 r)) ->
  getr R5 (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) -> getr R5 (Z_to_bv 5 8) = getr regs (Z_to_bv 5 8) ->
  getr R5 (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9) ->
  regs_preserved regs R5.
Proof.
  intros regs R1 R2 R3 R4 R5 K1 P2 K3 P4 K5 E2 E8 E9 r Hr.
  destruct (Z.eq_dec r 2) as [->|N2]; [exact E2|].
  destruct (Z.eq_dec r 8) as [->|N8]; [exact E8|].
  destruct (Z.eq_dec r 9) as [->|N9]; [exact E9|].
  rewrite (K5 r Hr N2 N8 N9), (P4 r Hr), (K3 r Hr N8), (P2 r Hr). exact (K1 r Hr N2 N9).
Qed.

Ltac pc_one X :=
  match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Ltac pc_cases X :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in
  intros rr Hrr; intros; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; first [exfalso; lia | pc_one X] |]);
  subst rr; first [exfalso; lia | pc_one X].

Section PC.
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

Lemma pc_mc_arg : forall Lc Ac mc mdc e q n s lo hi,
  aa_MR API Lc Ac mc mdc -> ro_agree rsegs mc ->
  bytes_at rsegs mc (e + CALL_OFF_ARGS + 8 * Z.of_nat 0) (le8 (Z_to_bv 64 q)) ->
  In (q, n) (blocks Lc Ac) -> Z.of_nat (length s) + 1 <= n ->
  bytes_at rsegs mc q (s ++ [Z_to_bv 8 0]) -> no0 s -> Z.of_nat (length s) <= LMAX ->
  alloc_ceiling <= lo ->
  mc_arg (normalize rsegs mc) lo hi e 0 (Z_to_bv 64 q, s).
Proof using SEGS SLACK.
  intros Lc Ac mc mdc e q n s lo hi HM RA BP Hb Hn BS N0 LX HLO.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_value as ACV. pose proof alloc_ceiling_val as AC.
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
  destruct (rs_bytes_pad rsegs mc q (s ++ [Z_to_bv 8 0])
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
    split; [exact N0|]. split; [exact LX|]. split; [lia|]. split; [lia|].
    exists sl. rewrite <- app_assoc in BS2. cbn [app] in BS2.
    split; [apply bytes_at_normalize; [exact RA | exact BS2]|].
    rewrite LS, Z2Nat.id by lia. split; [lia|]. left.
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
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
  room_ag (sb_malloc (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (resp code)) + 1))
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

Lemma pc_fin : forall L A regs mem md uri R O b Rc code c',
  pins_clear_m R uri = rec_answer_code Rc code ->
  ct_ret PINS_CLEAR_K L A regs mem md O Rc code b (sb_malloc b (Z.of_nat (length (sarg uri)) + 1)) c' ->
  pins_clear_ret (fx := fx) B API L A regs mem md uri R O b c'.
Proof.
  intros L A regs mem md uri R O b Rc code c' ESC CT.
  destruct CT as (fx' & L' & A' & regs' & mem' & md' & O' & EC & FPK & POST & A0' & GR' & ON' & OK' & BL' & RA'
    & F18' & INIT' & RGN' & SB' & RES').
  exists fx', L', A', regs', mem', md', (fst (rec_answer_code Rc code)), O', code.
  split; [rewrite ESC; reflexivity|].
  split; [exact EC|]. split; [exact FPK|]. split; [exact POST|]. split; [exact A0'|]. split; [exact GR'|].
  split; [exact ON'|]. split; [exact BL'|]. split; [exact OK'|]. split; [exact RA'|]. split; [exact F18'|].
  split; [exact INIT'|]. split; [exact RGN'|]. split; [|exact RES'].
  unfold pins_clear_sizes, sb_mallocs. cbn [fold_left]. exact SB'.
Qed.

Theorem pins_clear_holds : pins_clear_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN AX CTX SLACK REC ARGS MIX ANSC.
  unfold pins_clear_contract.
  intros L A regs mem md pu uri R O b PRE A0 SA GR RA FZ F18 RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PREK & HTS).
  pose proof PREK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & _).
  unfold PINS_CLEAR_K in HCEIL, HWS.
  rewrite SEGS in GR, RA, F18, HWS.
  pose proof (sinv_init B API PINS_CLEAR_K L A regs mem md R O b PREK ltac:(unfold PINS_CLEAR_K; lia) GR RA F18 RES)
    as SI0.
  unfold pins_clear_sizes, sb_mallocs in ROOM. cbn [fold_left] in ROOM.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8368) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E].
    unfold wview, mrd, wa. rewrite E. split; [discriminate | exists bb; reflexivity]. }
  unfold PINS_CLEAR. rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. eapply pc_run0; [exact ST | lia]. }
  intros ms1 (can1 & Q1 & EQ1).
  destruct Q1 as (m1 & junk & -> & MU1 & WM1 & FR1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x171cc) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 pu) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; exact A0).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 21) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (K1 : forall r, callee_saved r -> r <> 2 -> r <> 9 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by pc_cases X1.
  assert (SI1 : sinv B API PINS_CLEAR_K (bv_unsigned sp) L A mem md O L A m1 md R O b).
  { apply (sinv_stack B API SEGS GOWN AX PINS_CLEAR_K (bv_unsigned sp) L A mem md O L A mem md R O b m1
             [(bv_unsigned sp - 32, bv_unsigned sp)] SI0 MU1 WM1).
    intros a Ra Hn. unfold PINS_CLEAR_K.
    destruct (Z_lt_le_dec a (bv_unsigned sp - 32)) as [D1|D1]; [exfalso; apply Hn; cbn [outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec a (bv_unsigned sp)) as [D2|D2]; [lia|].
    exfalso; apply Hn; cbn [outside]; split; [lia | exact I]. }
  assert (SRCok : forall Lc Ac mc mdc Rc Oc,
            sinv B API PINS_CLEAR_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc Rc Oc b ->
            arg_s_src B Lc Ac (bv_unsigned sp - 32) mc pu uri).
  { intros Lc Ac mc mdc Rc Oc SIc.
    apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK PINS_CLEAR_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc Rc Oc b
             pu uri (bv_unsigned sp - 32) SIc RA); [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK, PINS_CLEAR_K; lia | lia | exact SA]. }
  destruct (sarg_facts B L A (bv_unsigned sp - 32) m1 pu uri (SRCok L A m1 md R O SI1)) as (NOU & LXU).
  replace (Z_to_bv 64 0x1612c) with (Z_to_bv 64 RECORD) by reflexivity.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC PINS_CLEAR_K (bv_unsigned sp) L A mem md O L A m1 md R O b R1 21 _ SI1).
  { rewrite E1_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL. }
  { rewrite SP1. unfold RECORD_K, ALLOC_STACK, PINS_CLEAR_K. lia. }
  { rewrite SP1. lia. }
  { rewrite E1_4. exact HTP. }
  { exact E1_10. }
  { unfold REC_FN_COUNT. lia. }
  intros L1 A1 R2 m2 md1 O1 SI2 BLE1 PR2 A10' FK2.
  rewrite sb_shift_refl in BLE1.
  pose proof (pc_frame_keep m1 m2 _ _ _ _ _ FR1 ltac:(intros x Hx; apply FK2; rewrite SP1; lia)) as FR2.
  rewrite E1_1.
  pose proof SI2 as (RJ2 & _). pose proof RJ2 as (HM2 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply pc_run1. }
  intros ms3 (can3 & -> & EQ3).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x171d8) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 32)).
  { rewrite (getr_of_eqv _ _ 2 X3 eq_refl). simp_regs. exact (eq_trans (PR2 2 ltac:(unfold callee_saved; lia)) E1_2). }
  assert (E3_4 : getr R3 4 = reg_get regs 4).
  { rewrite (getr_of_eqv _ _ 4 X3 eq_refl). simp_regs. exact (eq_trans (PR2 4 ltac:(unfold callee_saved; lia)) E1_4). }
  assert (E3_8 : getr R3 8 = Z_to_bv 64 (rec_entry G_REC REC_SC R)).
  { rewrite (getr_of_eqv _ _ 8 X3 eq_refl). simp_regs. exact A10'. }
  assert (E3_10 : getr R3 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R)).
  { rewrite (getr_of_eqv _ _ 10 X3 eq_refl). simp_regs. exact A10'. }
  assert (E3_11 : getr R3 11 = Z_to_bv 64 pu).
  { rewrite (getr_of_eqv _ _ 11 X3 eq_refl). simp_regs. exact (eq_trans (PR2 9 ltac:(unfold callee_saved; lia)) E1_9). }
  assert (SP3 : spZ R3 = bv_unsigned sp - 32) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  assert (K3 : forall r, callee_saved r -> r <> 8 -> getr R3 (Z_to_bv 5 r) = getr R2 (Z_to_bv 5 r)) by pc_cases X3.
  replace (Z_to_bv 64 0x161c4) with (Z_to_bv 64 ARG_S) by reflexivity.
  apply (sinv_arg_s B API SEGS ERRNO_LOW GFACT GOWN AX ARGS PINS_CLEAR_K (bv_unsigned sp) L A mem md O L1 A1 m2 md1
           R 21 O1 b R3 pu uri _ SI2).
  { rewrite E3_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP3. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL. }
  { rewrite SP3. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK, PINS_CLEAR_K. lia. }
  { rewrite SP3. lia. }
  { rewrite E3_4. exact HTP. }
  { exact E3_10. }
  { exact E3_11. }
  { rewrite SP3. exact (SRCok L1 A1 m2 md1 _ O1 SI2). }
  { apply (room_slots_mono _ (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length (sarg uri)) + 1))
             (Z.of_nat (length (resp (snd (pins_clear_m R uri)))) + 1))
             (Z.of_nat (length (resp (snd (pins_clear_m R uri)))) + 1)) _ (LMAX + 1)); [ | lia | exact ROOM].
    eapply sb_le_trans; [apply sb_malloc_mono; exact BLE1|].
    eapply sb_le_trans; [|apply sb_le_malloc; lia]. apply sb_le_malloc. lia. }
  intros L2 A2 R4 m3 md2 p SI3 SBE INI PR4 FK4.
  pose proof (pc_frame_keep m2 m3 _ _ _ _ _ FR2 ltac:(intros x Hx; apply FK4; rewrite SP3; lia)) as FR3.
  rewrite E3_1.
  pose proof SI3 as (RJ3 & GR3 & _ & _ & _ & RA3 & _ & _).
  pose proof RJ3 as (HM3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC3 & _).
  rewrite SEGS in HSC3.
  destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
  pose proof GR3 as (Q3 & HR3 & _). pose proof HR3 as (_ & _ & _ & _ & HX3 & _).
  destruct HX3 as (SC1 & SC2 & _ & SC4 & _ & SC6 & SC7 & _ & SC9 & _).
  assert (E4_2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (PR4 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (U2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 32)) = bv_unsigned sp - 32) by (apply unsigned_lit; lia).
  assert (BLE : sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length (sarg uri)) + 1))).
  { rewrite SBE. apply sb_malloc_mono. exact BLE1. }
  assert (CK : ANSWER_CODE_K <= PINS_CLEAR_K) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof (rw_cells_norm_hi m3 (bv_unsigned sp - 32) _ RA3 ltac:(lia) FR3) as FRn.
  assert (RC1n : rw_cells rsegs (normalize rsegs m3) 0x34028 [C4 (Z_to_bv 64 (r_refuse (rec_record R 21 [sarg uri])))]).
  { apply rw_cells_norm_glob; [exact RA3 | unfold GLOB_LO; lia | cbn; unfold GLOB_LO, GLOB_N; lia |].
    apply pc_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |]. exact SC1. }
  destruct (Z.eq_dec (r_refuse (rec_record R 21 [sarg uri])) 0) as [RZ|RNZ].
  - assert (ESC : pins_clear_m R uri = rec_answer_code (rec_mix (rec_record R 21 [sarg uri]) (21, [sarg uri])) 0).
    { unfold pins_clear_m, rec_stub_code, REC_PINS_CLEAR. cbv zeta. rewrite (proj2 (Z.eqb_eq _ _) RZ). reflexivity. }
    assert (HN : (length (r_calls R) <= 16)%nat)
      by exact (rec_record_calls R 21 [sarg uri] (rec_rep_calls_le _ _ _ _ _ _ _ _ GR3)).
    destruct (rec_entry_bounds R HN) as (ER1 & ER2 & ER3).
    destruct (rec_entry_at rsegs L2 A2 m3 R 21 [sarg uri] _ GR3) as (P0 & CA).
    destruct CA as (CF1 & CF2 & CLP & CFN & CNA & CND & CKA). cbn [fst snd] in *.
    destruct P0 as [|[q nq] [|pn' P0]]; cbn [length] in CLP; try discriminate.
    destruct (CKA 0%nat (sarg uri) (q, nq) eq_refl eq_refl) as (BP & PNZ & PIN & PSZ & PBS & PN0).
    cbn [fst snd] in BP, PNZ, PIN, PSZ, PBS.
    set (e := rec_entry G_REC REC_SC R) in *.
    assert (MCA : mc_arg (normalize rsegs m3) (bv_unsigned sp - 32 - 96) (bv_unsigned sp - 32) e 0
                    (Z_to_bv 64 q, sarg uri)).
    { apply (pc_mc_arg L2 A2 m3 md2 e q nq (sarg uri)); [exact HM3 | exact RA3 | exact BP | exact PIN | lia | exact PBS
        | exact PN0 | exact LXU | unfold PINS_CLEAR_K in *; lia]. }
    assert (EF : bytes_at rsegs (normalize rsegs m3) e
                   (le4 (Z_to_bv 64 21) ++ le4 (Z_to_bv 64 (Z.of_nat (length [(Z_to_bv 64 q, sarg uri)]))))).
    { apply bytes_at_normalize; [exact RA3|]. apply bytes_at_app. split.
      - unfold CALL_OFF_FN in CFN. rewrite Z.add_0_r in CFN. exact CFN.
      - replace (e + Z.of_nat (length (le4 (Z_to_bv 64 21)))) with (e + CALL_OFF_NARGS)
          by (rewrite length_le4; unfold CALL_OFF_NARGS; reflexivity). exact CNA. }
    assert (STn : stk rsegs (normalize rsegs m3) (bv_unsigned sp - 8368) (bv_unsigned sp - 32)).
    { apply stk_norm; [lia | lia |]. intros a Ha. apply HSC3. left. unfold PINS_CLEAR_K. lia. }
    pose proof RC1n as RC0n. rewrite RZ in RC0n.
    assert (ESn : rw_cells rsegs (normalize rsegs m3) 0x343d8 [C8 (Z_to_bv 64 (r_state (rec_record R 21 [sarg uri])))]).
    { apply rw_cells_norm_glob; [exact RA3 | unfold GLOB_LO; lia | cbn; unfold GLOB_LO, GLOB_N; lia |].
      apply bytes_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |]. exact SC4. }
    assert (E4_8 : reg_get R4 8 = Z_to_bv 64 e) by exact (eq_trans (PR4 8 ltac:(unfold callee_saved; lia)) E3_8).
    eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E4_2, E4_8.
      eapply (evt_normalize rsegs); [exact WX | exact RA3 |].
      eapply (pc_run_mix MIX) with (lo := bv_unsigned sp - 8368) (args := [(Z_to_bv 64 q, sarg uri)])
        (h := r_state (rec_record R 21 [sarg uri]));
        [apply mem_inv_normalize | rewrite U2; exact STn | rewrite U2; lia | lia | rewrite U2; exact FRn | exact RC0n | exact EF
        | unfold REC_SC in ER1; lia | unfold G_REC, REC_SIZE, CALL_SIZE in ER2; lia | exact ER3 | cbn; lia | | exact ESn
        | exact SC9].
      intros k p0 Hk. rewrite U2. destruct k as [|k]; [cbn in Hk; injection Hk as <-; exact MCA|].
      destruct k; discriminate. }
    intros ms5 (can5 & (s5n & Q5 & REL5 & RO5) & EQ5).
    destruct Q5 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m5n & -> & MU5n & WM5n & ES5n).
    destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL5) as [EC5 MR5r].
    revert EC5 MR5r RO5 EQ5. generalize (ms_mem can5) as m5. intros m5 EC5 MR5r RO5 EQ5. subst can5.
    pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR5r RO5 MU5n) as MU5.
    pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR5r RO5 WM5n) as WM5.
    pose proof (rw_cells_rel rsegs _ _ _ _ MR5r ES5n) as ES5.
    rewrite U2 in MU5.
    assert (SI5 : sinv B API PINS_CLEAR_K (bv_unsigned sp) L A mem md O L2 A2 m5 md2
                    (rec_mix (rec_record R 21 [sarg uri]) (21, [sarg uri]))
                    (O1 ++ [(p, Z.of_nat (length (sarg uri)) + 1)]) b).
    { apply (sinv_state B API SEGS GOWN AX PINS_CLEAR_K (bv_unsigned sp) L A mem md O L2 A2 m3 md2 _ _ b m5 _
               (mixcall (r_state (rec_record R 21 [sarg uri])) 21 [sarg uri]) SI3 MU5 WM5).
      - intros a Ra Hn. unfold G_REC, OFF_STATE, PINS_CLEAR_K.
        destruct (Z_lt_le_dec a (bv_unsigned sp - 32 - 96)) as [D1|D1].
        + destruct (Z_lt_le_dec a 0x343d8) as [D2|D2];
            [exfalso; apply Hn; cbn [outside]; split; [lia | split; [lia | exact I]]|].
          destruct (Z_lt_le_dec a 0x343e0) as [D3|D3]; [right; lia|].
          exfalso; apply Hn; cbn [outside]; split; [lia | split; [lia | exact I]].
        + destruct (Z_lt_le_dec a (bv_unsigned sp - 32)) as [D4|D4]; [left; lia|].
          exfalso; apply Hn; cbn [outside]; split; [lia | split; [lia | exact I]].
      - apply mixcall_range. exact SC9.
      - replace (G_REC + OFF_STATE) with 0x343d8 by (unfold G_REC, OFF_STATE; lia). exact (cells_c8 m5 0x343d8 _ ES5). }
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
    assert (E5_2 : getr R5 2 = getr regs 2).
    { rewrite (getr_of_eqv _ _ 2 X5 eq_refl). simp_regs. rewrite U2.
      replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by ring. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    assert (E5_1 : getr R5 1 = getr regs 1) by pc_one X5.
    assert (E5_8 : getr R5 8 = getr regs 8) by pc_one X5.
    assert (E5_9 : getr R5 9 = getr regs 9) by pc_one X5.
    assert (E5_10 : getr R5 10 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; reflexivity).
    assert (SP5 : spZ R5 = spZ regs) by (unfold spZ; rewrite E5_2; reflexivity).
    assert (K5 : forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R5 (Z_to_bv 5 r) = getr R4 (Z_to_bv 5 r))
      by pc_cases X5.
    pose proof (pc_pres regs R1 R2 R3 R4 R5 K1 PR2 K3 PR4 K5 E5_2 E5_8 E5_9) as RP5.
    assert (ROOMb : room_ag (sb_malloc (sb_malloc (sb_shift b A A2) (Z.of_nat (length (resp 0)) + 1))
                      (Z.of_nat (length (resp 0)) + 1)) (Z.of_nat (length (resp 0)) + 1)).
    { rewrite ESC in ROOM. cbn [snd rec_answer_code] in ROOM.
      apply (room_slots_mono _ _ _ (LMAX + 1) (sb_malloc_mono _ _ _ (sb_malloc_mono _ _ _ BLE)));
        [pose proof (resp_length 0 ltac:(lia)); unfold LMAX; lia | exact ROOM]. }
    replace (Z_to_bv 64 0x17168) with (Z_to_bv 64 ANSWER_CODE) by reflexivity.
    eapply SR_mono.
    { exact (code_tail PINS_CLEAR_K L A regs mem md O L2 A2 R5 m5 md2 _ _ b _ 0 PRE CK SI5 E5_1 SP5 RP5 E5_10
               ltac:(lia) FZ BLE ROOMb). }
    intros c' CT. exact (pc_fin L A regs mem md uri R O b _ _ c' ESC CT).
  - assert (ESC : pins_clear_m R uri = rec_answer_code (rec_record R 21 [sarg uri])
                                         (r_code (rec_record R 21 [sarg uri]))).
    { unfold pins_clear_m, rec_stub_code, REC_PINS_CLEAR. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) RNZ). reflexivity. }
    assert (RC2n : rw_cells rsegs (normalize rsegs m3) 0x3402c [C4 (Z_to_bv 64 (r_code (rec_record R 21 [sarg uri])))]).
    { apply rw_cells_norm_glob; [exact RA3 | unfold GLOB_LO; lia | cbn; unfold GLOB_LO, GLOB_N; lia |].
      apply pc_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |]. exact SC2. }
    eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E4_2.
      eapply (evt_normalize rsegs); [exact WX | exact RA3 |].
      eapply pc_run_ref; [rewrite U2; exact FRn | rewrite U2; lia | exact RC1n | exact RC2n | exact SC6 | exact RNZ
                         | exact SC7]. }
    intros ms4 (can4 & (s4n & E4 & REL4 & RO4) & EQ4). subst s4n.
    destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL4) as [EC4 MR4r].
    revert EC4 MR4r RO4 EQ4. generalize (ms_mem can4) as m4. intros m4 EC4 MR4r RO4 EQ4. subst can4.
    pose proof (munch_rel rsegs [] _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR4r RO4
                  (munch_refl [] (normalize rsegs m3))) as MU4.
    pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR4r RO4
                  (wmono_refl rsegs (normalize rsegs m3))) as WM4.
    assert (SI4 : sinv B API PINS_CLEAR_K (bv_unsigned sp) L A mem md O L2 A2 m4 md2 (rec_record R 21 [sarg uri])
                    (O1 ++ [(p, Z.of_nat (length (sarg uri)) + 1)]) b).
    { apply (sinv_stack B API SEGS GOWN AX PINS_CLEAR_K (bv_unsigned sp) L A mem md O L2 A2 m3 md2 _ _ b m4 [] SI3 MU4 WM4).
      intros a Ra Hn. exfalso. exact (Hn I). }
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R5 & -> & X5).
    assert (E5_2 : getr R5 2 = getr regs 2).
    { rewrite (getr_of_eqv _ _ 2 X5 eq_refl). simp_regs. rewrite U2.
      replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by ring. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    assert (E5_1 : getr R5 1 = getr regs 1) by pc_one X5.
    assert (E5_8 : getr R5 8 = getr regs 8) by pc_one X5.
    assert (E5_9 : getr R5 9 = getr regs 9) by pc_one X5.
    assert (E5_10 : getr R5 10 = Z_to_bv 64 (r_code (rec_record R 21 [sarg uri])))
      by (rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; reflexivity).
    assert (SP5 : spZ R5 = spZ regs) by (unfold spZ; rewrite E5_2; reflexivity).
    assert (K5 : forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R5 (Z_to_bv 5 r) = getr R4 (Z_to_bv 5 r))
      by pc_cases X5.
    pose proof (pc_pres regs R1 R2 R3 R4 R5 K1 PR2 K3 PR4 K5 E5_2 E5_8 E5_9) as RP5.
    set (cd := r_code (rec_record R 21 [sarg uri])) in *.
    assert (ROOMb : room_ag (sb_malloc (sb_malloc (sb_shift b A A2) (Z.of_nat (length (resp cd)) + 1))
                      (Z.of_nat (length (resp cd)) + 1)) (Z.of_nat (length (resp cd)) + 1)).
    { rewrite ESC in ROOM. cbn [snd rec_answer_code] in ROOM.
      apply (room_slots_mono _ _ _ (LMAX + 1) (sb_malloc_mono _ _ _ (sb_malloc_mono _ _ _ BLE)));
        [pose proof (resp_length cd SC7); unfold LMAX; lia | exact ROOM]. }
    replace (Z_to_bv 64 0x17168) with (Z_to_bv 64 ANSWER_CODE) by reflexivity.
    eapply SR_mono.
    { exact (code_tail PINS_CLEAR_K L A regs mem md O L2 A2 R5 m4 md2 _ _ b _ cd PRE CK SI4 E5_1 SP5 RP5 E5_10
               SC7 FZ BLE ROOMb). }
    intros c' CT. exact (pc_fin L A regs mem md uri R O b _ _ c' ESC CT).
Qed.

End PC.
