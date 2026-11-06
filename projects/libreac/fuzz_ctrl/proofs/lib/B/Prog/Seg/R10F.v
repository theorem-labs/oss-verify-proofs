(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 3942 of its 4075 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R10.v, with its module names, addresses and numbers changed; 426 of its 656 lines of code are new or changed and 3845 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R10.v r10_cfg0 (:134), r10_sum12 (:196), r10_head_reply (:252),
     r10_head_frag6 (:301), r10_head_frag5 (:351) (no call); r10_reply_call (:401, reac_ctrl_identity_reply),
     r10_frag6_call (:534) and r10_frag5_call (:650, reac_ctrl_identity_fragment) at
     a working branch 3803efccea0 (blob 3e337604ea39d36bedf3457b924598a163623f14);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: the no-call runs each get <run>_of_F (evtF_evt + rng_all) re-deriving the source statement; the
     call runs are split at their single call into <run>_pre_F (stop at the callee entry, ra = return pc) and
     <run>_post_F (from the return pc, 0 further steps; repackages the callee post facts into the exit cut).
     Bridge inputs only to a Theorem Labs lane's cgif-form walk.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_identity_reply_c reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcReply RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R10.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module RPC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_reply_c.
Module FGC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_c.
Module RFP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module RRp := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply.
Module RFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.

(* Store hook: StepF.mem_after_store_opt plus the register-byte branch of R10.v's fix_lit_store, on evtF goals. *)
Ltac r10f_store :=
  try (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?b))) _) => idtac
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
           change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
       end);
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= r10f_store.

(* Branch tactics (evtF), and the register-add normalizer, twins of R10.v's brT/brF/r10_req. *)
Ltac brTF :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota | symmetry; first [solve_cond | vm_compute; reflexivity]]
  end.
Ltac brFF :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota | symmetry; first [solve_cond | vm_compute; reflexivity]]
  end.
Ltac r10f_req := first [reflexivity | rewrite lit_add_lit; reflexivity].
Ltac r10f_bi Hb i := eapply (R10.r10_bat_idx _ _ _ i); [exact Hb | reflexivity | cbn [Z.of_nat]; lia].

(* ---- r10_cfg0_F: b = 0 arm, 0x817a4 -> 0x818a8 (no call) ---- *)
Lemma r10_cfg0_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (junk : list byte),
    s4 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 0 -> a0 = Z_to_bv 64 9 ->
    0 <= phi -> phi + 18 < 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 12 junk] ->
    mem_inv rsegs m ->
    rng RNG (bv_unsigned s3 + 306) 12 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m1 : word -> option byte) (l12 : list byte) (c3 c4 : byte),
         ms' = MS R F (Z_to_bv 64 0x818a8) fc None m1 (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 21 = Z_to_bv 64 36 /\ getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 14 = Z_to_bv 64 32 /\
         getr R 13 = Z_to_bv 64 (- (phi + 18)) /\ getr R 18 = s2 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 318)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l12 /\ length l12 = 12%nat /\
         bytes_at rsegs m1 (bv_unsigned s3 + 316) [c3] /\ bv_signed c3 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 317) [c4] /\ bv_signed c4 = 4)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi junk -> -> -> -> Hphi0 Hphi1 HC HMI Rsh.
  pose proof (R10.r10_cb_len _ _ _ _ HC) as Hjl.
  destruct junk as [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|j7 [|j8 [|j9 [|j10 [|j11 [|? ?]]]]]]]]]]]]];
    cbn [length] in Hjl; try discriminate Hjl.
  pose proof (munch_refl [(bv_unsigned s3 + 306, bv_unsigned s3 + 318)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  do 5 step.
  step. brFF.
  do 2 step.
  step. brTF.
  step. brFF.
  do 3 step.
  step. brTF.
  do 9 step.
  apply evtF_done. do 2 eexists. eexists. do 2 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [r10f_req|]. split; [r10f_req|]. split; [r10f_req|]. split; [r10f_req|].
  split; [rewrite <- (R10.r10_room phi) by lia; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|].
  destruct HC as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb.
  split; [exact Hb|].
  split; [cbn [length]; reflexivity|].
  split; [r10f_bi Hb 10%nat|].
  split; [vm_compute; reflexivity|].
  split; [r10f_bi Hb 11%nat|].
  vm_compute; reflexivity.
Qed.

Lemma r10_cfg0_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (junk : list byte),
    s4 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 0 -> a0 = Z_to_bv 64 9 ->
    0 <= phi -> phi + 18 < 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 12 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m1 : word -> option byte) (l12 : list byte) (c3 c4 : byte),
         ms' = MS R F (Z_to_bv 64 0x818a8) fc None m1 (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 21 = Z_to_bv 64 36 /\ getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 14 = Z_to_bv 64 32 /\
         getr R 13 = Z_to_bv 64 (- (phi + 18)) /\ getr R 18 = s2 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 318)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l12 /\ length l12 = 12%nat /\
         bytes_at rsegs m1 (bv_unsigned s3 + 316) [c3] /\ bv_signed c3 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 317) [c4] /\ bv_signed c4 = 4)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi junk E4 E5 E6 E0 Hphi0 Hphi1 HC HMI.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  apply (evtF_evt rsegs RNG_all).
  apply (r10_cfg0_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m phi junk E4 E5 E6 E0 Hphi0 Hphi1 HC HMI).
  apply rng_all; lia.
Qed.
Definition r10_cfg0_src_check : ltac:(let T := type of R10.r10_cfg0 in exact T) := r10_cfg0_of_F.

(* ---- r10_sum12_F: b = 1, 2 arm, 0x817a4 -> 0x8194c (no call) ---- *)
Lemma r10_sum12_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi bz : Z) (junk : list byte),
    s4 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 bz -> a0 = Z_to_bv 64 5 ->
    (bz = 1 \/ bz = 2) ->
    0 <= phi -> phi + 18 < 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 12 junk] ->
    mem_inv rsegs m ->
    rng RNG (bv_unsigned s3 + 306) 12 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m1 : word -> option byte) (l12 : list byte),
         ms' = MS R F (Z_to_bv 64 0x8194c) fc None m1 (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 21 = Z_to_bv 64 36 /\ getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 14 = Z_to_bv 64 32 /\
         getr R 13 = Z_to_bv 64 (- (phi + 18)) /\ getr R 18 = s2 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 318)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l12 /\ length l12 = 12%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi bz junk -> -> -> -> Hbz Hphi0 Hphi1 HC HMI Rsh.
  pose proof (R10.r10_cb_len _ _ _ _ HC) as Hjl.
  destruct junk as [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|j7 [|j8 [|j9 [|j10 [|j11 [|? ?]]]]]]]]]]]]];
    cbn [length] in Hjl; try discriminate Hjl.
  pose proof (munch_refl [(bv_unsigned s3 + 306, bv_unsigned s3 + 318)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  destruct Hbz as [-> | ->].
  all: do 5 step.
  all: step; brFF.
  all: do 2 step.
  all: step; brTF.
  all: step; brTF.
  all: do 1 step.
  all: step; brTF.
  all: do 9 step.
  all: apply evtF_done; do 2 eexists; eexists.
  all: split; [reflexivity|].
  all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  all: split; [reflexivity|].
  all: split; [r10f_req|]; split; [r10f_req|]; split; [r10f_req|]; split; [r10f_req|].
  all: split; [rewrite <- (R10.r10_room phi) by lia; reflexivity|].
  all: split; [reflexivity|]; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [exact HMI|].
  all: destruct HC as ((_ & Hb) & _); cbn [cells_bytes cbytes app] in Hb.
  all: split; [exact Hb | cbn [length]; reflexivity].
Qed.

Lemma r10_sum12_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi bz : Z) (junk : list byte),
    s4 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 bz -> a0 = Z_to_bv 64 5 ->
    (bz = 1 \/ bz = 2) ->
    0 <= phi -> phi + 18 < 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 12 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m1 : word -> option byte) (l12 : list byte),
         ms' = MS R F (Z_to_bv 64 0x8194c) fc None m1 (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 21 = Z_to_bv 64 36 /\ getr R 10 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 14 = Z_to_bv 64 32 /\
         getr R 13 = Z_to_bv 64 (- (phi + 18)) /\ getr R 18 = s2 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 318)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l12 /\ length l12 = 12%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi bz junk E4 E5 E6 E0 Hbz Hphi0 Hphi1 HC HMI.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  apply (evtF_evt rsegs RNG_all).
  apply (r10_sum12_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m phi bz junk E4 E5 E6 E0 Hbz Hphi0 Hphi1 HC HMI).
  apply rng_all; lia.
Qed.
Definition r10_sum12_src_check : ltac:(let T := type of R10.r10_sum12 in exact T) := r10_sum12_of_F.

(* ---- r10_head_reply_F: b = 3, 4 head to 0x817d4 (no call) ---- *)
Lemma r10_head_reply_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z) (junk : list byte),
    s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 bz -> a0 = Z_to_bv 64 5 -> (bz = 3 \/ bz = 4) ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 7 junk] ->
    mem_inv rsegs m ->
    rng RNG (bv_unsigned s3 + 306) 7 ->
    evtF rsegs RNG
      (fun ms' => exists (m1 : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 5) (Z_to_bv 64 5) (Z_to_bv 64 4)
                       (Z_to_bv 64 2) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 36) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x817d4) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bz junk -> -> -> Hbz HC HMI Rsh.
  pose proof (R10.r10_cb_len _ _ _ _ HC) as Hjl.
  destruct junk as [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|? ?]]]]]]]]; cbn [length] in Hjl; try discriminate Hjl.
  pose proof (munch_refl [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  destruct Hbz as [-> | ->].
  all: do 5 step.
  all: step; brFF.
  all: do 2 step.
  all: step; brFF.
  all: do 1 step.
  all: step; brTF.
  all: apply evtF_done; do 5 eexists.
  all: split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [exact HMI|].
  all: destruct HC as ((_ & Hb) & _); cbn [cells_bytes cbytes app] in Hb.
  all: split; [r10f_bi Hb 0%nat|].
  all: split; [vm_compute; reflexivity|].
  all: split; [r10f_bi Hb 2%nat|].
  all: split; [vm_compute; reflexivity|].
  all: split; [r10f_bi Hb 6%nat|].
  all: split; [vm_compute; reflexivity|].
  all: split; [exact Hb | cbn [length]; reflexivity].
Qed.

Lemma r10_head_reply_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z) (junk : list byte),
    s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 bz -> a0 = Z_to_bv 64 5 -> (bz = 3 \/ bz = 4) ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 7 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (m1 : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 5) (Z_to_bv 64 5) (Z_to_bv 64 4)
                       (Z_to_bv 64 2) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 36) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x817d4) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bz junk E5 E6 E0 Hbz HC HMI.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  apply (evtF_evt rsegs RNG_all).
  apply (r10_head_reply_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m bz junk E5 E6 E0 Hbz HC HMI).
  apply rng_all; lia.
Qed.
Definition r10_head_reply_src_check : ltac:(let T := type of R10.r10_head_reply in exact T) := r10_head_reply_of_F.

(* ---- r10_head_frag6_F: b = 6 head to 0x81818 (no call) ---- *)
Lemma r10_head_frag6_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 6 -> a0 = Z_to_bv 64 11 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 7 junk] ->
    mem_inv rsegs m ->
    rng RNG (bv_unsigned s3 + 306) 7 ->
    evtF rsegs RNG
      (fun ms' => exists (m1 : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) (Z_to_bv 64 11) (Z_to_bv 64 4)
                       (Z_to_bv 64 2) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 36) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81818) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk -> -> -> HC HMI Rsh.
  pose proof (R10.r10_cb_len _ _ _ _ HC) as Hjl.
  destruct junk as [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|? ?]]]]]]]]; cbn [length] in Hjl; try discriminate Hjl.
  pose proof (munch_refl [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  do 5 step.
  step; brTF.
  do 2 step.
  step; brFF.
  step.
  step; brFF.
  step.
  step; brTF.
  apply evtF_done. do 5 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|].
  destruct HC as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb.
  split; [r10f_bi Hb 0%nat|].
  split; [vm_compute; reflexivity|].
  split; [r10f_bi Hb 2%nat|].
  split; [vm_compute; reflexivity|].
  split; [r10f_bi Hb 6%nat|].
  split; [vm_compute; reflexivity|].
  split; [exact Hb | cbn [length]; reflexivity].
Qed.

Lemma r10_head_frag6_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 6 -> a0 = Z_to_bv 64 11 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 7 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (m1 : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) (Z_to_bv 64 11) (Z_to_bv 64 4)
                       (Z_to_bv 64 2) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 36) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81818) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk E5 E6 E0 HC HMI.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  apply (evtF_evt rsegs RNG_all).
  apply (r10_head_frag6_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m junk E5 E6 E0 HC HMI).
  apply rng_all; lia.
Qed.
Definition r10_head_frag6_src_check : ltac:(let T := type of R10.r10_head_frag6 in exact T) := r10_head_frag6_of_F.

(* ---- r10_head_frag5_F: b = 5 head to 0x818f8 (no call) ---- *)
Lemma r10_head_frag5_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 5 -> a0 = Z_to_bv 64 11 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 7 junk] ->
    mem_inv rsegs m ->
    rng RNG (bv_unsigned s3 + 306) 7 ->
    evtF rsegs RNG
      (fun ms' => exists (m1 : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) (Z_to_bv 64 11) (Z_to_bv 64 4)
                       (Z_to_bv 64 2) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 36) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x818f8) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk -> -> -> HC HMI Rsh.
  pose proof (R10.r10_cb_len _ _ _ _ HC) as Hjl.
  destruct junk as [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|? ?]]]]]]]]; cbn [length] in Hjl; try discriminate Hjl.
  pose proof (munch_refl [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  do 5 step.
  step; brTF.
  do 2 step.
  step; brTF.
  step.
  step; brTF.
  apply evtF_done. do 5 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|].
  destruct HC as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb.
  split; [r10f_bi Hb 0%nat|].
  split; [vm_compute; reflexivity|].
  split; [r10f_bi Hb 2%nat|].
  split; [vm_compute; reflexivity|].
  split; [r10f_bi Hb 6%nat|].
  split; [vm_compute; reflexivity|].
  split; [exact Hb | cbn [length]; reflexivity].
Qed.

Lemma r10_head_frag5_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    s5 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 5 -> a0 = Z_to_bv 64 11 ->
    rw_cells rsegs m (bv_unsigned s3 + 306) [CB 7 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (m1 : word -> option byte) (l7 : list byte) (c0 c1 c2 : byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 11) (Z_to_bv 64 11) (Z_to_bv 64 4)
                       (Z_to_bv 64 2) a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 36) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x818f8) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 306, bv_unsigned s3 + 313)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) [c0] /\ bv_signed c0 = 2 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 308) [c1] /\ bv_signed c1 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 312) [c2] /\ bv_signed c2 = 0 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 306) l7 /\ length l7 = 7%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk E5 E6 E0 HC HMI.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  apply (evtF_evt rsegs RNG_all).
  apply (r10_head_frag5_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m junk E5 E6 E0 HC HMI).
  apply rng_all; lia.
Qed.
Definition r10_head_frag5_src_check : ltac:(let T := type of R10.r10_head_frag5 in exact T) := r10_head_frag5_of_F.

(* ================ the three call arms, split at the call ================ *)

(* ---- REPLY (reac_ctrl_identity_reply @ 0x848fc), 0x817d4-0x817e8, returning to 0x817ec ----
   0x817d4 mv a0,s4; 0x817d8 mv a1,s2; 0x817dc ld a2,240(s1); 0x817e0 ld a3,232(s1); 0x817e4 ld a4,224(s1);
   0x817e8 jal REPLY. The data accesses are the three 8-byte loads of the out-slot spills. *)
Lemma r10_reply_call_pre_F : forall (RNG : footprint)
    (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr : Z),
  ro_cells rsegs m (bv_unsigned s1 + 240) [C8 (Z_to_bv 64 (fr + 2448))] ->
  ro_cells rsegs m (bv_unsigned s1 + 232) [C8 (Z_to_bv 64 (fr + 2464))] ->
  ro_cells rsegs m (bv_unsigned s1 + 224) [C8 (Z_to_bv 64 (fr + 2496))] ->
  rng RNG (bv_unsigned s1 + 240) 8 -> rng RNG (bv_unsigned s1 + 232) 8 ->
  rng RNG (bv_unsigned s1 + 224) 8 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x817ec) sp gp tp t0 t1 t2 s0 s1 s4 s2
                             (Z_to_bv 64 (fr + 2448)) (Z_to_bv 64 (fr + 2464)) (Z_to_bv 64 (fr + 2496))
                             a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x848fc) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x817d4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m fr RO1 RO2 RO3 R240 R232 R224.
  do 6 step.
  apply evtF_done. reflexivity.
Qed.

(* From the return pc 0x817ec (= the run's exit cut): 0 further steps; the reac_ctrl_identity_reply post
   facts the proved run used, stated over the post-call state, give the run's exit Q (R10.v:438-457). *)
Lemma r10_reply_call_post_F : forall (RNG : footprint)
    (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (R : bvmap 5 word)
    (spv phi N fr FS : Z) (g50 : list byte),
  getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
  getr R 19 = s3 -> getr R 20 = s4 -> getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 ->
  getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 -> getr R 18 = s2 -> getr R 27 = s11 ->
  getr R 10 = Z_to_bv 64 (RRp.reply_ret phi N (fr + 2448) (fr + 2464) (fr + 2496) g50) ->
  munch (RPC.reac_ctrl_identity_reply_fp phi N (fr + 2448) (fr + 2464) (fr + 2496) spv g50 ++
         RFP.fp_w [1%nat] FS ++
         [(shadow_addr (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K), shadow_addr spv)]) m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) spv ->
  (RRp.reply_ok phi N (fr + 2448) (fr + 2464) (fr + 2496) g50 = true ->
     rw_cells rsegs m' (fr + 2448) [CB 2 (RRp.reply_addr g50)] /\
     rw_cells rsegs m' (fr + 2464) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
     rw_cells rsegs m' (fr + 2496) [CB 8 (le8 (Z_to_bv 64 (RRp.ir_s g50 - 13)))]) ->
  asan_cells m' -> shadow_rw m' ->
  addressable m' (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) RPC.REAC_CTRL_IDENTITY_REPLY_K ->
  RFP.fp [1%nat] m' (bv_unsigned tp) FS (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) spv
    (RPC.reac_ctrl_identity_reply_W phi (fr + 2448) (fr + 2464) (fr + 2496) spv)
    (RPC.reac_ctrl_identity_reply_D phi N (fr + 2448) (fr + 2464) (fr + 2496)) ->
  evtF rsegs RNG
    (fun ms' => exists (R0 : bvmap 5 word) (m0 : word -> option byte),
       ms' = MS R0 F (Z_to_bv 64 0x817ec) fc None m0 (seg_rom rsegs) /\
       getr R0 2 = sp /\ getr R0 3 = gp /\ getr R0 4 = tp /\ getr R0 8 = s0 /\ getr R0 9 = s1 /\
       getr R0 19 = s3 /\ getr R0 20 = s4 /\ getr R0 21 = s5 /\ getr R0 22 = s6 /\ getr R0 23 = s7 /\
       getr R0 24 = s8 /\ getr R0 25 = s9 /\ getr R0 26 = s10 /\ getr R0 18 = s2 /\ getr R0 27 = s11 /\
       getr R0 10 = Z_to_bv 64 (RRp.reply_ret phi N (fr + 2448) (fr + 2464) (fr + 2496) g50) /\
       munch (RPC.reac_ctrl_identity_reply_fp phi N (fr + 2448) (fr + 2464) (fr + 2496) spv g50 ++
              RFP.fp_w [1%nat] FS ++
              [(shadow_addr (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K), shadow_addr spv)]) m m0 /\
       wmono rsegs m m0 /\ mem_inv rsegs m0 /\
       stk rsegs m0 (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) spv /\
       (RRp.reply_ok phi N (fr + 2448) (fr + 2464) (fr + 2496) g50 = true ->
          rw_cells rsegs m0 (fr + 2448) [CB 2 (RRp.reply_addr g50)] /\
          rw_cells rsegs m0 (fr + 2464) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
          rw_cells rsegs m0 (fr + 2496) [CB 8 (le8 (Z_to_bv 64 (RRp.ir_s g50 - 13)))]) /\
       asan_cells m0 /\ shadow_rw m0 /\
       addressable m0 (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) RPC.REAC_CTRL_IDENTITY_REPLY_K /\
       RFP.fp [1%nat] m0 (bv_unsigned tp) FS (spv - RPC.REAC_CTRL_IDENTITY_REPLY_K) spv
         (RPC.reac_ctrl_identity_reply_W phi (fr + 2448) (fr + 2464) (fr + 2496) spv)
         (RPC.reac_ctrl_identity_reply_D phi N (fr + 2448) (fr + 2464) (fr + 2496)))
    (MS R F (Z_to_bv 64 0x817ec) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' R spv phi N fr FS g50
    G2 G3 G4 G8 G9 G19 G20 G21 G22 G23 G24 G25 G26 G18 G27 G10
    MU WM MI ST RW AC SW AD FP.
  apply evtF_done. exists R, m'.
  split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

(* ---- FRAG, b = 6 arm (reac_ctrl_identity_fragment @ 0x859e4), 0x81818-0x81830, returning to 0x81834 ----
   0x81818 ld a0,112(s1); 0x8181c mv a1,s4; 0x81820 mv a2,s2; 0x81824 ld a3,240(s1); 0x81828 ld a4,232(s1);
   0x8182c ld a5,224(s1); 0x81830 jal FRAG. The data accesses are the four 8-byte loads of the spills. *)
Lemma r10_frag6_call_pre_F : forall (RNG : footprint)
    (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr : Z),
  ro_cells rsegs m (bv_unsigned s1 + 112) [C8 (Z_to_bv 64 (fr + 2256))] ->
  ro_cells rsegs m (bv_unsigned s1 + 240) [C8 (Z_to_bv 64 (fr + 2448))] ->
  ro_cells rsegs m (bv_unsigned s1 + 232) [C8 (Z_to_bv 64 (fr + 2464))] ->
  ro_cells rsegs m (bv_unsigned s1 + 224) [C8 (Z_to_bv 64 (fr + 2496))] ->
  rng RNG (bv_unsigned s1 + 112) 8 -> rng RNG (bv_unsigned s1 + 240) 8 ->
  rng RNG (bv_unsigned s1 + 232) 8 -> rng RNG (bv_unsigned s1 + 224) 8 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81834) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fr + 2256)) s4 s2
                             (Z_to_bv 64 (fr + 2448)) (Z_to_bv 64 (fr + 2464)) (Z_to_bv 64 (fr + 2496))
                             a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x859e4) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81818) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m fr RO0 RO1 RO2 RO3 R112 R240 R232 R224.
  do 7 step.
  apply evtF_done. reflexivity.
Qed.

(* From the return pc 0x81834 (= the b = 6 exit cut): 0 further steps; the fragment post facts the proved run
   used, stated over the post-call state, give the run's exit Q (R10.v:567-580). *)
Lemma r10_frag6_call_post_F : forall (RNG : footprint)
    (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (R : bvmap 5 word)
    (spv phi N fr : Z) (g50 st72 : list byte),
  getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
  getr R 19 = s3 -> getr R 20 = s4 -> getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 ->
  getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 -> getr R 18 = s2 -> getr R 27 = s11 ->
  getr R 10 = Z_to_bv 64 (RFr.fg_ret (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464)
                                        (fr + 2496) N st72 g50)) ->
  munch (RFr.fg_fp FGC.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
           spv (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50)) m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K) spv ->
  FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st72 g50
    (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50) m' ->
  asan_cells m' -> shadow_rw m' ->
  evtF rsegs RNG
    (fun ms' => exists (R0 : bvmap 5 word) (m0 : word -> option byte),
       ms' = MS R0 F (Z_to_bv 64 0x81834) fc None m0 (seg_rom rsegs) /\
       getr R0 2 = sp /\ getr R0 3 = gp /\ getr R0 4 = tp /\ getr R0 8 = s0 /\ getr R0 9 = s1 /\
       getr R0 19 = s3 /\ getr R0 20 = s4 /\ getr R0 21 = s5 /\ getr R0 22 = s6 /\ getr R0 23 = s7 /\
       getr R0 24 = s8 /\ getr R0 25 = s9 /\ getr R0 26 = s10 /\ getr R0 18 = s2 /\ getr R0 27 = s11 /\
       getr R0 10 = Z_to_bv 64 (RFr.fg_ret (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464)
                                              (fr + 2496) N st72 g50)) /\
       munch (RFr.fg_fp FGC.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
                spv (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50)) m m0 /\
       wmono rsegs m m0 /\ mem_inv rsegs m0 /\
       stk rsegs m0 (spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K) spv /\
       FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st72 g50
         (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50) m0 /\
       asan_cells m0 /\ shadow_rw m0)
    (MS R F (Z_to_bv 64 0x81834) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' R spv phi N fr g50 st72
    G2 G3 G4 G8 G9 G19 G20 G21 G22 G23 G24 G25 G26 G18 G27 G10
    MU WM MI ST MEM AC SW.
  apply evtF_done. exists R, m'.
  split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

(* ---- FRAG, b = 5 arm (reac_ctrl_identity_fragment @ 0x859e4), 0x818f8-0x81910, returning to 0x81914:
   the same seven instructions at the other placement of the arm. *)
Lemma r10_frag5_call_pre_F : forall (RNG : footprint)
    (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr : Z),
  ro_cells rsegs m (bv_unsigned s1 + 112) [C8 (Z_to_bv 64 (fr + 2256))] ->
  ro_cells rsegs m (bv_unsigned s1 + 240) [C8 (Z_to_bv 64 (fr + 2448))] ->
  ro_cells rsegs m (bv_unsigned s1 + 232) [C8 (Z_to_bv 64 (fr + 2464))] ->
  ro_cells rsegs m (bv_unsigned s1 + 224) [C8 (Z_to_bv 64 (fr + 2496))] ->
  rng RNG (bv_unsigned s1 + 112) 8 -> rng RNG (bv_unsigned s1 + 240) 8 ->
  rng RNG (bv_unsigned s1 + 232) 8 -> rng RNG (bv_unsigned s1 + 224) 8 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81914) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fr + 2256)) s4 s2
                             (Z_to_bv 64 (fr + 2448)) (Z_to_bv 64 (fr + 2464)) (Z_to_bv 64 (fr + 2496))
                             a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x859e4) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x818f8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m fr RO0 RO1 RO2 RO3 R112 R240 R232 R224.
  do 7 step.
  apply evtF_done. reflexivity.
Qed.

(* From the return pc 0x81914 (= the b = 5 exit cut): 0 further steps; the fragment post facts the proved run
   used, stated over the post-call state, give the run's exit Q (R10.v:683-696). *)
Lemma r10_frag5_call_post_F : forall (RNG : footprint)
    (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (R : bvmap 5 word)
    (spv phi N fr : Z) (g50 st72 : list byte),
  getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
  getr R 19 = s3 -> getr R 20 = s4 -> getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 ->
  getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 -> getr R 18 = s2 -> getr R 27 = s11 ->
  getr R 10 = Z_to_bv 64 (RFr.fg_ret (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464)
                                        (fr + 2496) N st72 g50)) ->
  munch (RFr.fg_fp FGC.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
           spv (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50)) m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K) spv ->
  FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st72 g50
    (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50) m' ->
  asan_cells m' -> shadow_rw m' ->
  evtF rsegs RNG
    (fun ms' => exists (R0 : bvmap 5 word) (m0 : word -> option byte),
       ms' = MS R0 F (Z_to_bv 64 0x81914) fc None m0 (seg_rom rsegs) /\
       getr R0 2 = sp /\ getr R0 3 = gp /\ getr R0 4 = tp /\ getr R0 8 = s0 /\ getr R0 9 = s1 /\
       getr R0 19 = s3 /\ getr R0 20 = s4 /\ getr R0 21 = s5 /\ getr R0 22 = s6 /\ getr R0 23 = s7 /\
       getr R0 24 = s8 /\ getr R0 25 = s9 /\ getr R0 26 = s10 /\ getr R0 18 = s2 /\ getr R0 27 = s11 /\
       getr R0 10 = Z_to_bv 64 (RFr.fg_ret (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464)
                                              (fr + 2496) N st72 g50)) /\
       munch (RFr.fg_fp FGC.REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
                spv (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50)) m m0 /\
       wmono rsegs m m0 /\ mem_inv rsegs m0 /\
       stk rsegs m0 (spv - FGC.REAC_CTRL_IDENTITY_FRAGMENT_K) spv /\
       FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st72 g50
         (RFr.fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) N st72 g50) m0 /\
       asan_cells m0 /\ shadow_rw m0)
    (MS R F (Z_to_bv 64 0x81914) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' R spv phi N fr g50 st72
    G2 G3 G4 G8 G9 G19 G20 G21 G22 G23 G24 G25 G26 G18 G27 G10
    MU WM MI ST MEM AC SW.
  apply evtF_done. exists R, m'.
  split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.
