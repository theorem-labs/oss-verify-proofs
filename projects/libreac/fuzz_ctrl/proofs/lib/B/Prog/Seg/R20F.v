(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 647 of its 705 lines of code are new or changed and 953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R20.v, with its module paths and module names changed; 46 of its 89 lines of code are new or changed and 662 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R20.v r20_evt at a working branch 3803efccea0
     (blob d451605fcdbab348281e596d14c36161e86a5774);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r20_evt_of_F (evtF_evt + rng_all) re-derives the source statement of R20.v:194-226 verbatim. *)
(* rule 24: no function proved. *)
(* The footprint twin of R20.v's r20_evt, the run [0x81a68, 0x534b4) (the beqz, the six frame shadow stores
   S(fr) + 316 .. 323, the j, the mv a0,s4 and the jal wrapper_free). The run stops AT the callee entry
   0x534b4, so it steps through no callee and needs no _pre / _post split. Its only accesses are the six
   one-byte stores into [S(fr) + 316, S(fr) + 324); the range has no instrumented check and no load. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot RHelp.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R20.
(* Last: StepF's step / if_true (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

(* The store hook of R20.v (`sb s8,k(s3)`: le1 v is [Z_to_bv 8 (bv_unsigned v)] by conversion), on the four-argument
   evtF goal pattern; StepF's norm_lit_store_bytes only knows the literal stores (RECIPE pilot fix (2)). *)
Local Ltac fix_lit_storeF :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) => change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
  | _ => idtac
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::=
  fix_lit_storeF; norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

(* ---- the footprint form of the Lib-level run of [0x81a68, 0x534b4) ---- *)

Lemma r20_evt_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    a0v = Z_to_bv 64 0 ->
    rw_cells rsegs m (bv_unsigned s3v + 316) [CB 8 junk] ->
    stk rsegs m (bv_unsigned s3v + 316) (bv_unsigned s3v + 324) ->
    rng RNG (bv_unsigned s3v + 316) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x534b4) fc None m' (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = s4 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
         getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3v + 316, bv_unsigned s3v + 324)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned s3v + 316) (bv_unsigned s3v + 324))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81a68) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m junk -> RWsh ST Rsh.
  pose proof (rw_cells_bound _ _ _ _ RWsh) as HBsh. cbn [cells_size csize Nat.add] in HBsh.
  pose proof (munch_refl [(bv_unsigned s3v + 316, bv_unsigned s3v + 324)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 81a68 beqz a0 (taken) *)
  step. if_true.
  (* 81a70 .. 81a84 : the six shadow stores *)
  step. step. step. step. step. step.
  (* 81a88 j 81a98 ; 81a98 mv a0,s4 ; 81a9c jal wrapper_free *)
  step. step. step.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  do 17 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* The auditor's compare lemma: the source statement R20.v:194-226, verbatim, from r20_evt_F at RNG_all. *)
Lemma r20_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    a0v = Z_to_bv 64 0 ->
    rw_cells rsegs m (bv_unsigned s3v + 316) [CB 8 junk] ->
    stk rsegs m (bv_unsigned s3v + 316) (bv_unsigned s3v + 324) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x534b4) fc None m' (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = s4 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
         getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3v + 316, bv_unsigned s3v + 324)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned s3v + 316) (bv_unsigned s3v + 324))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81a68) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m junk Ha RWsh ST.
  pose proof (rw_cells_bound _ _ _ _ RWsh) as HBsh. cbn [cells_size csize Nat.add] in HBsh.
  eapply evtF_evt.
  eapply r20_evt_F; try eassumption.
  apply rng_all; lia.
Qed.
Definition r20_evt_src_check : ltac:(let T := type of R20.r20_evt in exact T) := r20_evt_of_F.
