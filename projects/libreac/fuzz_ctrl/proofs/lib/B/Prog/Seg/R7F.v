(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names, addresses and numbers changed; 1202 of its 1292 lines of code are new or changed and 921 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R7.v, with its module paths and module names changed; 77 of its 119 lines of code are new or changed and 1250 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R7.v r7_evt (:144), r7_evt0 (:165) at
     a working branch 3803efccea0 (blob 0726d190dd685a9359793e49350524b0f5d90052);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r7_evt_of_F / r7_evt0_of_F re-derive the SOURCE statements (evtF_evt + rng_all, then the
     ul_evt_of_evt bridge of R5F.v, which carries a lib.Lib run into the lib.B.Tk.UL engine the source
     states its runs in); r7_evt_same / r7_evt0_same compile that those are R7.r7_evt's and R7.r7_evt0's
     own statements (`ltac:(let T := type of R7.r7_evt in exact T)`).  Both runs stop at a branch/call
     target (no callee is stepped through); each is re-stepped on the lib.Lib machine with StepF.  They
     record no cut-free twin and are bridge inputs only to a Theorem Labs lane's cgif-form walk.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R7.
(* Last: StepF's step / if_true / if_false / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* A branch whose condition is a closed term (every register it reads holds a literal here). *)
Ltac r7F_if_true :=
  first [ if_true
        | lazymatch goal with
          | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
              replace c with true; [cbv iota | symmetry; vm_compute; reflexivity]
          end ].
Ltac r7F_if_false :=
  first [ if_false
        | lazymatch goal with
          | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
              replace c with false; [cbv iota | symmetry; vm_compute; reflexivity]
          end ].

(* 0x81710 beqz a0 (not taken); 0x81714 .. 0x81720 bgeu a0,a1 (taken); 0x81728 .. 0x81734 bgeu a2,s5 (taken);
   0x8173c .. 0x81754 beqz a0 (taken); 0x8175c mv a0,s2; 0x81760 jal wrapper_malloc. *)
Ltac r7F_run :=
  step; r7F_if_false;
  do 4 step; r7F_if_true;
  do 4 step; r7F_if_true;
  do 7 step; r7F_if_true;
  do 2 step;
  finish; try simp_regs; first [reflexivity | vm_compute; reflexivity].

(* ---- the run 0x81710 .. 0x81760 (ends at the allocator's entry 0x534b8) ---- *)
Lemma r7_evt_F : forall (RNG : footprint)
    (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
  a0 = Z_to_bv 64 n -> s5 = Z_to_bv 64 36 -> R7.r7_nv n ->
  ro_cells rsegs m (bv_unsigned s1 + 128) [C8 (Z_to_bv 64 0xe38f0000)] ->
  rng RNG (bv_unsigned s1 + 128) 8 ->
  evtF rsegs RNG
    (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x534b8) fc None m (seg_rom rsegs) /\
       getr R 1 = Z_to_bv 64 0x81764 /\ getr R 10 = Z_to_bv 64 n /\ getr R 18 = Z_to_bv 64 n /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
       getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11)
    (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81710) fc None m (seg_rom rsegs)).
Proof.
  intros RNG rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m n -> -> Hn HRO Rmag.
  unfold R7.r7_nv in Hn.
  repeat match goal with Hd : _ \/ _ |- _ => destruct Hd as [Hd|Hd] end.
  all: subst n; r7F_run.
Qed.

(* 0x81710 beqz a0,0x81ac0 taken on a zero count: one instruction, every register and the memory kept. *)
Lemma r7_evt0_F : forall (RNG : footprint)
    (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 ->
  evtF rsegs RNG
    (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs) /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
       getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 18 = s2 /\ getr R 27 = s11)
    (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81710) fc None m (seg_rom rsegs)).
Proof.
  intros RNG rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step; r7F_if_true.
  finish; try simp_regs; first [reflexivity | vm_compute; reflexivity].
Qed.

(* ---- the compare lemmas (the auditor's check): the source statements back from the twins ----
   R7.r7_evt / R7.r7_evt0 state their runs on the lib.B.Tk.UL engine.  UL's [mstep] is the lib.Lib
   [mstep] (both are `ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'`), so a
   lib.Lib run of a given Q is a UL run of it; the register and memory vocabulary (mkR, MS, getr,
   ro_cells, seg_rom) is the same text in the two copies.  Same bridge as R5F.v:136-146; SmLib's
   ul_entry / mkR_ul are not Required here, because SmLib pulls its UL + AK + AW closure and its image
   numerals, which the glue-closure rule bars. *)
Module ULE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.

Lemma ul_msteps_of_msteps : forall ms ms', msteps rsegs ms ms' -> ULE.msteps rsegs ms ms'.
Proof.
  intros ms ms' H.
  induction H as [ms0|ms0 ms1 ms2 Hst Hs IH]; [apply ULE.msteps_refl|].
  eapply ULE.msteps_cons; [|exact IH]. destruct Hst as [HA HB]. split; [exact HA | exact HB].
Qed.

Lemma ul_evt_of_evt : forall (Q : machine_state -> Prop) ms, evt rsegs Q ms -> ULE.evt rsegs Q ms.
Proof.
  intros Q ms (ms1 & H & HQ). exists ms1. split; [exact (ul_msteps_of_msteps _ _ H) | exact HQ].
Qed.

Lemma r7_evt_of_F : forall (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                       : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
  a0 = Z_to_bv 64 n -> s5 = Z_to_bv 64 36 -> R7.r7_nv n ->
  ro_cells rsegs m (bv_unsigned s1 + 128) [C8 (Z_to_bv 64 0xe38f0000)] ->
  ULE.evt rsegs
    (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x534b8) fc None m (seg_rom rsegs) /\
       getr R 1 = Z_to_bv 64 0x81764 /\ getr R 10 = Z_to_bv 64 n /\ getr R 18 = Z_to_bv 64 n /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
       getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11)
    (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81710) fc None m (seg_rom rsegs)).
Proof.
  intros rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m n Ha0 Hs5 Hn HRO.
  pose proof (ro_cells_bound _ _ _ _ HRO) as HB. cbn [cells_size csize Nat.add] in HB.
  apply ul_evt_of_evt.
  apply (evtF_evt rsegs RNG_all).
  apply (r7_evt_F RNG_all rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m n Ha0 Hs5 Hn HRO).
  apply rng_all; lia.
Qed.

(* The source statement itself: this type-checks only if r7_evt_of_F has R7.r7_evt's type. *)
Definition r7_evt_same : ltac:(let T := type of R7.r7_evt in exact T) := r7_evt_of_F.

Lemma r7_evt0_of_F : forall (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                        : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 ->
  ULE.evt rsegs
    (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs) /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
       getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 18 = s2 /\ getr R 27 = s11)
    (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81710) fc None m (seg_rom rsegs)).
Proof.
  intros rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ha0.
  apply ul_evt_of_evt.
  apply (evtF_evt rsegs RNG_all).
  exact (r7_evt0_F RNG_all rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m Ha0).
Qed.

(* The source statement itself: this type-checks only if r7_evt0_of_F has R7.r7_evt0's type. *)
Definition r7_evt0_same : ltac:(let T := type of R7.r7_evt0 in exact T) := r7_evt0_of_F.
