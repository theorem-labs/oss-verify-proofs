(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 2439 of its 2555 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F2.v; 151 of its 248 lines of code are new or changed and 2458 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F2.v f2_head0 (:80), f2_head1 (:109), f2_st (:142), f2_pcall (:286),
     f2_mcpy_evt (:346) at a working branch 3803efccea0
     (blob 880a1ab3fc2beb3fc8f90fef3ef0a781e7287594);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f2_head0_of_F, f2_head1_of_F, f2_st_of_F (evtF_evt + rng_all) re-derive the source statements;
     f2_pcall_pre_F re-runs F2.v:339 (the four instructions at pcm, F2.v:284-285) and f2_mcpy_pre_F re-runs
     F2.v:381 (the four instructions at 0x81f68, F2.v:345), each stopping AT the callee entry.
   f2_st_noinv_F re-runs the same F2.v f2_st (:142) six steps with the mem_inv premise and the mem_inv post
     conjunct dropped on both sides; it has no _of_F (no source statement in that shape).
   F2.f2_parse_at (:174) has NO _F twin: it steps no instruction of the caller; it only applies the
   reac_ctrl_parse contract from the callee entry to the return pc.  Per the 23:50Z parent ruling a callee
   contract is never stated locally, so the walk composes that callee itself.  Neither call has a post
   stretch: in both source runs the instruction after the call site is the return pc itself. *)
(* rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_parse_c RcAsanFP asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c memcmp_c asan_memcpy_c asan_memcpy.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import F2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module PCF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_parse_c.
Module MCCF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpy_c.

(* A byte store of a register whose value is not a literal (the four `sb zero` of the record-shadow block): the
   engine's cell_of_bytes knows le8 / le4 / le2 / a singleton / le1 (zxb b), not le1 of a register.  F2.v:52-62
   overrides lib.Lib.Tac's fix_lit_store for the evt goal; here the same normalization goes into StepF's
   mem_after_store_opt (pilot fix (2)), whose other branches are StepF.v:488-497 verbatim. *)
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  (match goal with
   | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?b))) _) => idtac
   | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
       change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
   | _ => idtac
   end);
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

(* ---- the head run 0x81f50 -> 0x82020 (len = 0), with the store [A + 224] ---- *)
Lemma f2_head0_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S : Z),
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= S < 2 ^ 64 -> wr_at rsegs m (A + 224) 8 ->
    rng RNG (A + 224) 8 ->
    evtF rsegs RNG
      (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 a0 s3
                                          (Z_to_bv 64 0) (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x82020) fc None m' (seg_rom rsegs) /\
         munch [(A + 224, A + 232)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 224) (le8 (Z_to_bv 64 S)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0)
               (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f50) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A S
    HA0 HA1 HS HW Rsp.
  pose proof (munch_refl [(A + 224, A + 232)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (wr_at_store_ok rsegs m (A + 224) 8 0 8 HW ltac:(lia) ltac:(lia)) as HS1.
  replace (A + 224 + 0) with (A + 224) in HS1 by lia.
  (* 0x81f50 mv s2,a0 ; 0x81f54 beqz s4 (taken) *)
  step. step. first [if_true_by f2_eqb0 | if_true].
  (* 0x81f60 sd s5,224(s1) ; 0x81f64 beqz s4 (taken) *)
  step. step. first [if_true_by f2_eqb0 | if_true].
  apply evtF_done. eexists. split; [reflexivity|].
  split; [apply munch_write; [exact MU | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]|].
  split; [apply wmono_write; exact WM|].
  apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

(* ---- the head run 0x81f50 -> 0x81f68 (len > 0), with the store [A + 224] ---- *)
Lemma f2_head1_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S N phi : Z),
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= S < 2 ^ 64 -> 0 < N < 2 ^ 64 -> 0 < phi < 2 ^ 64 ->
    wr_at rsegs m (A + 224) 8 ->
    rng RNG (A + 224) 8 ->
    evtF rsegs RNG
      (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 phi) a1 a2 a3 a4 a5
                                          a6 a7 (Z_to_bv 64 phi) s3 (Z_to_bv 64 N) (Z_to_bv 64 S) s6 s7 s8 s9 s10
                                          s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x81f68) fc None m' (seg_rom rsegs) /\
         munch [(A + 224, A + 232)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 224) (le8 (Z_to_bv 64 S)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 N)
               (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f50) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A S N phi
    HA0 HA1 HS HN Hphi HW Rsp.
  pose proof (munch_refl [(A + 224, A + 232)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (wr_at_store_ok rsegs m (A + 224) 8 0 8 HW ltac:(lia) ltac:(lia)) as HS1.
  replace (A + 224 + 0) with (A + 224) in HS1 by lia.
  (* 0x81f50 mv s2,a0 ; 0x81f54 beqz s4 (not taken) ; 0x81f58 bnez s2 (taken) *)
  step. step. first [if_false_by (f2_eqb_nz N HN) | if_false].
  step. first [if_true_by (f2_neqb0 phi Hphi) | if_true].
  (* 0x81f60 sd s5,224(s1) ; 0x81f64 beqz s4 (not taken) *)
  step. step. first [if_false_by (f2_eqb_nz N HN) | if_false].
  apply evtF_done. eexists. split; [reflexivity|].
  split; [apply munch_write; [exact MU | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]|].
  split; [apply wmono_write; exact WM|].
  apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

(* ---- the five record-shadow stores 0x82020-0x82034 / 0x81f94-0x81fa8 ---- *)
Lemma f2_st_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (pc0 pc1 : Z),
    (pc0 = 0x82020 /\ pc1 = 0x82038) \/ (pc0 = 0x81f94 /\ pc1 = 0x81fac) ->
    rw_cells rsegs m (bv_unsigned s3 + 22) [CB 5 junk] ->
    mem_inv rsegs m ->
    rng RNG (bv_unsigned s3 + 22) 5 ->
    evtF rsegs RNG
      (fun ms' => exists (a0' : word) (m1 : word -> option byte) (b0 b1 b2 b3 b4 : byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 pc1) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 22, bv_unsigned s3 + 27)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 22) [b0; b1; b2; b3; b4] /\
         bv_signed b0 = 0 /\ bv_signed b1 = 0 /\ bv_signed b2 = 0 /\ bv_signed b3 = 0 /\ bv_signed b4 = 4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk pc0 pc1 Hpc HC HMI Rrec.
  pose proof (munch_refl [(bv_unsigned s3 + 22, bv_unsigned s3 + 27)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  destruct Hpc as [[-> ->] | [-> ->]]; do 6 step;
    (apply evtF_done; do 2 eexists; do 5 eexists;
     split; [reflexivity|];
     split; [exact MU|]; split; [exact WM|]; split; [exact HMI|];
     split; [destruct HC as ((_ & Hb) & _); cbn [cells_bytes cbytes app] in Hb; exact Hb|];
     repeat split; vm_compute; reflexivity).
Qed.

(* ---- the same five record-shadow stores without the mem_inv side carrier ----
   Same source run (F2.v f2_st, :142) and the same six steps; the `mem_inv rsegs m` premise and the
   `mem_inv rsegs m1` conjunct of the post are dropped on both sides (in f2_st_F the premise is used only to
   re-state itself in the post, as the store goals come from the rw_cells premise).  The walk needs this twin
   where the record-shadow stretch is reached with no mem_inv in hand. *)
Lemma f2_st_noinv_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (pc0 pc1 : Z),
    (pc0 = 0x82020 /\ pc1 = 0x82038) \/ (pc0 = 0x81f94 /\ pc1 = 0x81fac) ->
    rw_cells rsegs m (bv_unsigned s3 + 22) [CB 5 junk] ->
    rng RNG (bv_unsigned s3 + 22) 5 ->
    evtF rsegs RNG
      (fun ms' => exists (a0' : word) (m1 : word -> option byte) (b0 b1 b2 b3 b4 : byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 pc1) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 22, bv_unsigned s3 + 27)] m m1 /\ wmono rsegs m m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 22) [b0; b1; b2; b3; b4] /\
         bv_signed b0 = 0 /\ bv_signed b1 = 0 /\ bv_signed b2 = 0 /\ bv_signed b3 = 0 /\ bv_signed b4 = 4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk pc0 pc1 Hpc HC Rrec.
  pose proof (munch_refl [(bv_unsigned s3 + 22, bv_unsigned s3 + 27)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  destruct Hpc as [[-> ->] | [-> ->]]; do 6 step;
    (apply evtF_done; do 2 eexists; do 5 eexists;
     split; [reflexivity|];
     split; [exact MU|]; split; [exact WM|];
     split; [destruct HC as ((_ & Hb) & _); cbn [cells_bytes cbytes app] in Hb; exact Hb|];
     repeat split; vm_compute; reflexivity).
Qed.

(* ---- 0x82038 / 0x81fac up TO the reac_ctrl_parse entry: mv a0,s2 ; mv a1,s4 ; ld a2,280(s1) ; jal ---- *)
Lemma f2_pcall_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o pcm pcr A : Z),
    (pcm = 0x82038 /\ pcr = 0x82048) \/ (pcm = 0x81fac /\ pcr = 0x81fbc) ->
    s1 = Z_to_bv 64 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    rng RNG (A + 280) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 pcr) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) s2 s4 (Z_to_bv 64 o)
                                a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 PCF.REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pcm) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o pcm pcr A Hpc Hs1 HA0 HA1 HRD Rsp.
  subst s1.
  destruct Hpc as [[-> ->] | [-> ->]]; (step; step; step; step; apply evtF_done; reflexivity).
Qed.

(* ---- 0x81f68 up TO the checked memcpy entry: mv a0,s2 ; mv a1,s5 ; mv a2,s4 ; jal ---- *)
Lemma f2_mcpy_pre_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81f78) sp gp tp t0 t1 t2 s0 s1 s2 s5 s4
                                a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 MCCF.ASAN_MEMCPY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f68) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m.
  step. step. step. step. apply evtF_done. reflexivity.
Qed.

(* ---- the compare lemmas of the three call-free runs ---- *)

Lemma f2_head0_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S : Z),
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= S < 2 ^ 64 -> wr_at rsegs m (A + 224) 8 ->
    evt rsegs
      (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 a0 s3
                                          (Z_to_bv 64 0) (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x82020) fc None m' (seg_rom rsegs) /\
         munch [(A + 224, A + 232)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 224) (le8 (Z_to_bv 64 S)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0)
               (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f50) fc None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all). apply f2_head0_F; try assumption. apply rng_all; lia.
Qed.
Definition f2_head0_src_check : ltac:(let T := type of F2.f2_head0 in exact T) := f2_head0_of_F.

Lemma f2_head1_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S N phi : Z),
    0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= S < 2 ^ 64 -> 0 < N < 2 ^ 64 -> 0 < phi < 2 ^ 64 ->
    wr_at rsegs m (A + 224) 8 ->
    evt rsegs
      (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 phi) a1 a2 a3 a4 a5
                                          a6 a7 (Z_to_bv 64 phi) s3 (Z_to_bv 64 N) (Z_to_bv 64 S) s6 s7 s8 s9 s10
                                          s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x81f68) fc None m' (seg_rom rsegs) /\
         munch [(A + 224, A + 232)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 224) (le8 (Z_to_bv 64 S)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 N)
               (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f50) fc None m (seg_rom rsegs)).
Proof.
  intros. apply (evtF_evt rsegs RNG_all). apply f2_head1_F; try assumption. apply rng_all; lia.
Qed.
Definition f2_head1_src_check : ltac:(let T := type of F2.f2_head1 in exact T) := f2_head1_of_F.

Lemma f2_st_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (pc0 pc1 : Z),
    (pc0 = 0x82020 /\ pc1 = 0x82038) \/ (pc0 = 0x81f94 /\ pc1 = 0x81fac) ->
    rw_cells rsegs m (bv_unsigned s3 + 22) [CB 5 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' : word) (m1 : word -> option byte) (b0 b1 b2 b3 b4 : byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 pc1) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 22, bv_unsigned s3 + 27)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 22) [b0; b1; b2; b3; b4] /\
         bv_signed b0 = 0 /\ bv_signed b1 = 0 /\ bv_signed b2 = 0 /\ bv_signed b3 = 0 /\ bv_signed b4 = 4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk pc0 pc1 Hpc HC HMI.
  apply (evtF_evt rsegs RNG_all). apply f2_st_F with (junk := junk); try assumption.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  apply rng_all; lia.
Qed.
Definition f2_st_src_check : ltac:(let T := type of F2.f2_st in exact T) := f2_st_of_F.
