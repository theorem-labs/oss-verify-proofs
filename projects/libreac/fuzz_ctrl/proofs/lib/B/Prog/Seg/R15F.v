(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 844 of its 926 lines of code are new or changed and 929 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R13.v, with its module paths, module names, addresses and numbers changed; 33 of its 66 lines of code are new or changed and 893 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R15.v r15_evt at a working branch 3803efccea0
     (blob 196bc0cc6cc4beb1e84291399ce9b65a8fb7ca44);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r15_evt_of_F (evtF_evt + the lib.Lib -> UL msteps bridge) re-derives the source statement, and
     r15_evt_src_check : r15_evt_stmt := R15.r15_evt checks by conversion that r15_evt_stmt IS that statement. *)
(* rule 24: no function proved. *)
(* The run 0x81914 beqz a0,0x81a98 ; 0x81a98 mv a0,s4 ; 0x81a9c jal wrapper_free stops AT the free entry 0x534b4
   with ra = 0x81aa0, so it is already the `_pre` stretch of its call: no `_F` steps through the callee and the
   source run has no stretch after it.  The three instructions read and write no memory (a branch and two register
   moves; instruction fetch is not an access), so r15_evt_F carries no rng premise. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R15.
Import ListNotations.
Import YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Open Scope Z_scope.

Module UE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.

(* ---- the footprint twin of the run 0x81914 .. 0x81a9c ---- *)

(* A branch whose condition is a closed term (every register it reads holds a literal here). *)
Ltac r15f_if_true :=
  first [ if_true
        | lazymatch goal with
          | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
              replace c with true; [cbv iota | symmetry; vm_compute; reflexivity]
          end ].

Lemma r15_evt_F : forall (RNG : footprint)
                         (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 ->
  evtF rsegs RNG
    (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x534b4) fc None m (seg_rom rsegs) /\
       getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = s4 /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 27 = s11 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
       getr R 26 = s10)
    (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81914) fc None m (seg_rom rsegs)).
Proof.
  intros RNG rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step; try r15f_if_true.
  do 2 step.
  finish; try simp_regs; first [reflexivity | vm_compute; reflexivity].
Qed.

(* ---- compare: the source statement, re-derived from r15_evt_F ----
   The library engine's steps lift into the UL engine: the two msteps are the same relation on the same step
   function (A3.v:87-94). *)

Lemma r15_lib_msteps : forall s s', msteps rsegs s s' -> UE.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UE.msteps_refl|].
  eapply UE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma r15_lib_evt : forall Q s, evt rsegs Q s -> UE.evt rsegs Q s.
Proof. intros Q s (s' & H & HQ). exists s'. split; [exact (r15_lib_msteps _ _ H) | exact HQ]. Qed.

Definition r15_evt_stmt : Prop :=
  forall (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 ->
  UE.evt rsegs
    (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x534b4) fc None m (seg_rom rsegs) /\
       getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = s4 /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 27 = s11 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
       getr R 26 = s10)
    (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81914) fc None m (seg_rom rsegs)).

Lemma r15_evt_of_F : r15_evt_stmt.
Proof.
  unfold r15_evt_stmt. intros rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m Ha0.
  apply r15_lib_evt. apply (evtF_evt rsegs RNG_all). apply r15_evt_F. exact Ha0.
Qed.

(* The source lemma R15.r15_evt has exactly the statement r15_evt_stmt (checked by conversion). *)
Definition r15_evt_src_check : r15_evt_stmt := R15.r15_evt.
