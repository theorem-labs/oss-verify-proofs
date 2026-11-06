(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module names, addresses and numbers changed; 446 of its 699 lines of code are new or changed and 295 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/descriptors_get.v, with its module paths, module names, addresses and numbers changed; 170 of its 214 lines of code are new or changed and 655 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memmove_c ListStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lf_segA0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V CAP : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned a0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 CAP)] ->
  bv_unsigned a0 + 16 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0 ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x14bd8) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 a0 (Z_to_bv 64 0)
                    (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x15664) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
      /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells rsegs m' (bv_unsigned a0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 CAP)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo V CAP ST LO LC DJ.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  rewrite ?ls_sx32 by lia.
  step. br true.
  step. step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma lf_segA1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V N CAP q : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned a0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  rw_cells rsegs m (V + 16 * (N - 1)) [C8 (Z_to_bv 64 q)] ->
  bv_unsigned a0 + 16 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0 ->
  V + 16 * (N - 1) + 8 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= V + 16 * (N - 1) ->
  1 <= N < 2 ^ 30 -> 0 <= V -> V + 16 * N <= 2 ^ 64 ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x14ba4) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 a0 (Z_to_bv 64 N)
                    (Z_to_bv 64 q) (Z_to_bv 64 (16 * N)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (16 * (N - 1)))
                    s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x15664) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
      /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells rsegs m' (bv_unsigned a0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b6c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo V N CAP q ST LO LC RC DJ DR HN HV HVN.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  rewrite ?ls_sx32 by lia.
  step. br false.
  step. step.
  rewrite (ls_slli4 N) by lia.
  step. step.
  match goal with |- context [Z_to_bv 64 (V + ?x)] => replace (V + x) with (V + 16 * (N - 1)) by lia end.
  remember (V + 16 * (N - 1)) as P eqn:HP.
  step. step.
  subst P.
  replace (16 * N + -16) with (16 * (N - 1)) by lia.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma lf_zero : forall x, Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (x - x)))) 4) = Z_to_bv 64 0.
Proof. intros x. rewrite Z.sub_diag. reflexivity. Qed.

Lemma mm_result_0 : forall us s d, mm_result us s d 0 = us.
Proof.
  intros us s d. unfold mm_result, slice, upd_bytes. cbn [firstn length app].
  rewrite Nat.add_0_r. apply firstn_skipn.
Qed.

Lemma lf_dec : forall k, 1 <= k < 2 ^ 30 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 k) + -1)) = Z_to_bv 64 (k - 1).
Proof.
  intros k Hk. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 30) with 1073741824 in Hk.
  Z.div_mod_to_equations. lia.
Qed.

Ltac lf_mm MMC V us k :=
  step; step;
  rewrite ?ls_sx32 by lia;
  step; step; step; step;
  rewrite lf_zero;
  step;
  let U0 := fresh "U0" in let U1 := fresh "U1" in let U2 := fresh "U2" in
  assert (U0 : bv_unsigned (Z_to_bv 64 (V + 16 * (k - 1))) = V + 16 * (k - 1)) by (apply unsigned_lit; lia);
  assert (U1 : bv_unsigned (Z_to_bv 64 (V + 16 * (k - 1) + 16)) = V + 16 * (k - 1) + 16) by (apply unsigned_lit; lia);
  assert (U2 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (MMC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V us);
      [ assumption | lia | rewrite U1, U2; lia | rewrite U0, U2; lia | rewrite U2; lia | assumption ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memmove_post in PO; rewrite ?U0, ?U1, ?U2 in PO; revert ms' PO;
      post_call rsegs mm ]
  end;
  clear U0 U1 U2;
  repeat match goal with H : u8arr _ _ V (mm_result ?u _ _ _) |- _ =>
    replace (mm_result u _ _ _) with u in H by (symmetry; apply mm_result_0) end;
  step;
  rewrite ?ls_sx32 by lia;
  step;
  rewrite (lf_dec k) by lia;
  step; step.

Lemma lf_segB2 : memmove_contract -> forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (V k CAP q : Z) (us : list byte),
  rw_cells rsegs m (bv_unsigned s0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 CAP)] ->
  u8arr rsegs m V us -> Z.of_nat (length us) = 16 * CAP ->
  rw_cells rsegs m (V + 16 * (k - 1 - 1)) [C8 (Z_to_bv 64 q)] ->
  2 <= k <= CAP -> CAP < 2 ^ 30 -> 8 <= V -> V + 16 * CAP < 2 ^ 64 ->
  bv_unsigned s0 + 16 <= V \/ V + 16 * CAP <= bv_unsigned s0 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR (Z_to_bv 64 0x14ba4) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (k - 1)) (Z_to_bv 64 q)
                    (Z_to_bv 64 (16 * (k - 1))) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (16 * (k - 1 - 1)))
                    s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x15664) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned s0, bv_unsigned s0 + 16)] m m' /\ wmono rsegs m m'
      /\ rw_cells rsegs m' (bv_unsigned s0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (k - 1)); C4 (Z_to_bv 64 CAP)]
      /\ u8arr rsegs m' V us)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 k) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (16 * (k - 1)))
             s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ba4) fc None m (seg_rom rsegs)).
Proof.
  intros MMC ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m V k CAP q us LC UA LU RC HK HC HV HVC DJ MI.
  pose proof (rw_cells_bound _ _ _ _ LC) as LB. cbn [cells_size csize] in LB.
  pose proof (munch_refl [(bv_unsigned s0, bv_unsigned s0 + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  lf_mm MMC V us k.
  br true.
  step. step.
  rewrite (ls_slli4 (k - 1)) by lia.
  step. step.
  match goal with |- context [Z_to_bv 64 (V + ?x)] => replace (V + x) with (V + 16 * (k - 1 - 1)) by lia end.
  remember (V + 16 * (k - 1 - 1)) as P eqn:HP.
  step. step.
  subst P.
  replace (16 * (k - 1) + -16) with (16 * (k - 1 - 1)) by lia.
  apply evt_done. do 14 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma lf_segB1 : memmove_contract -> forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (V k CAP : Z) (us : list byte),
  rw_cells rsegs m (bv_unsigned s0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 CAP)] ->
  u8arr rsegs m V us -> Z.of_nat (length us) = 16 * CAP ->
  k = 1 -> 1 <= CAP -> CAP < 2 ^ 30 -> 8 <= V -> V + 16 * CAP < 2 ^ 64 ->
  bv_unsigned s0 + 16 <= V \/ V + 16 * CAP <= bv_unsigned s0 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR (Z_to_bv 64 0x14bd8) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (k - 1)) (Z_to_bv 64 V)
                    a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (16 * (k - 1)))
                    s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x15664) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned s0, bv_unsigned s0 + 16)] m m' /\ wmono rsegs m m'
      /\ rw_cells rsegs m' (bv_unsigned s0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (k - 1)); C4 (Z_to_bv 64 CAP)]
      /\ u8arr rsegs m' V us)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 k) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (16 * (k - 1)))
             s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ba4) fc None m (seg_rom rsegs)).
Proof.
  intros MMC ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m V k CAP us LC UA LU HK HC1 HC HV HVC DJ MI.
  pose proof (rw_cells_bound _ _ _ _ LC) as LB. cbn [cells_size csize] in LB.
  pose proof (munch_refl [(bv_unsigned s0, bv_unsigned s0 + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  lf_mm MMC V us k.
  br false.
  step. step.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma lf_segC : forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (LA V CAP : Z) (r0 v8 v9 v18 : word),
  rw_cells rsegs m (bv_unsigned sp) [C8 v18; C8 v9; C8 v8; C8 r0] ->
  rw_cells rsegs m LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 CAP)] ->
  LA + 16 <= bv_unsigned sp \/ bv_unsigned sp + 32 <= LA ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR r0 (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 v8 v9 a0 a1 a2 a3 a4 a5 a6 a7 v18
                    s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc r0) fc None m' (seg_rom rsegs)
      /\ munch [(LA, LA + 16)] m m' /\ wmono rsegs m m'
      /\ rw_cells rsegs m' LA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
      /\ rw_cells rsegs m' (bv_unsigned sp) [C8 v18; C8 v9; C8 v8; C8 r0])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 LA) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14bd8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m LA V CAP r0 v8 v9 v18 FR LC DJ.
  pose proof (rw_cells_bound _ _ _ _ LC) as LB. cbn [cells_size csize] in LB.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize] in FB.
  pose proof (munch_refl [(LA, LA + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 8 step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.
