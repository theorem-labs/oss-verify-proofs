(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2004 of its 2120 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F30.v, with its module paths, addresses and numbers changed; 450 of its 544 lines of code are new or changed and 2026 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F29.v; 65 of its 145 lines of code are new or changed and 464 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F29.v f29_evt (:145), f29_evt_ro (:208) at a working branch
     3803efccea0 (blob d3a8027a51921bbae135e8e3f445db865b9f9bb6);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c),
         lib/B/MemNormF.v blob 99f8b314301ceb0f253f1a6c8165b488b23ce218 (taken by path from dba073859bd: the
         evtF twin of MemNorm.evt_normalize, which 3803efccea0 has only in Exec.evt form);
   compare: f29_evt_of_F (evtF_evt + rng_all) re-derives F29.f29_evt verbatim; f29_evt_ro_F is the same run on the
     cut's own memory (ro_agree in place of mem_inv), re-run of F29.v:226-249 with evtF_normalize_ro.
   Neither run calls anything (0x82aa4 -> 0x82abc is six straight-line instructions), so there is no _pre_F/_post_F
   split here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro F29.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* The three stores write the low byte of s11, i.e. `le1 x11` with x11 a variable, which StepF's cell_of_bytes
   does not recognise.  F29.v's own run rewrites it to the one-byte list first (F29.le1_byte); the store hook has
   to do the same before mem_after_store, as pilot fix (2) prescribes. *)
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  try (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
           lazymatch v with zxb _ => fail | _ => rewrite (F29.le1_byte v) end
       end);
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

(* The footprint twin of F29.f29_evt: 0x82aa4 -> 0x82abc, three one-byte stores into the frame's shadow at
   S3 + 16 / +17 / +20 and the spill load [A + 272, A + 280). *)
Lemma f29_evt_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 A kv : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x9 = Z_to_bv 64 A ->
    rw_cells rsegs m (S3 + 16) [CB 5 bs] -> bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 kv)) ->
    mem_inv rsegs m ->
    0 <= S3 -> S3 + 21 <= 2 ^ 64 -> S3 + 21 <= A -> 0 <= A -> A + 280 <= 2 ^ 64 ->
    rng RNG (S3 + 16) 5 -> rng RNG (A + 272) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) m',
         ms' = MS R Fr (Z_to_bv 64 0x82abc) fc None m' (seg_rom rsegs) /\
         getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
         getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
         getr R 25 = x24 /\ getr R 22 = Z_to_bv 64 1 /\ getr R 24 = Z_to_bv 64 kv /\
         munch [(S3 + 16, S3 + 21)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         exists cs, rw_cells rsegs m' (S3 + 16) cs /\ cells_size cs = 5%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82aa4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 A kv bs -> -> HRW Hspill HMI H0 H1 HSA H0A H1A RS RA.
  pose proof (munch_refl [(S3 + 16, S3 + 21)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  step.
  step.
  step. step.
  match goal with H : bytes_at rsegs ?m3 (A + 272) _ |- _ =>
    assert (Hrd : ov_read_bytes rsegs m3 (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 kv)));
    [ pose proof (bytes_at_ov_read rsegs m3 (A + 272) _ 0 8 H ltac:(rewrite length_le8; lia)) as HH;
      cbn [Z.of_nat] in HH; rewrite Z.add_0_r, skipn_O in HH;
      rewrite firstn_all2 in HH by (rewrite length_le8; lia); exact HH
    | ] end.
  step.
  apply evtF_done.
  match goal with |- context [MS ?R _ _ _ _ ?m3 _] => exists R, m3 end.
  split; [reflexivity|].
  simp_regs.
  do 13 (split; [reflexivity|]).
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  match goal with H : rw_cells rsegs ?m3 (S3 + 16) ?cs |- _ => exists cs; split; [exact H | reflexivity] end.
Qed.

(* The auditor's compare lemma: f29_evt_F at RNG_all is F29.f29_evt verbatim. *)
Lemma f29_evt_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 A kv : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x9 = Z_to_bv 64 A ->
    rw_cells rsegs m (S3 + 16) [CB 5 bs] -> bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 kv)) ->
    mem_inv rsegs m ->
    0 <= S3 -> S3 + 21 <= 2 ^ 64 -> S3 + 21 <= A -> 0 <= A -> A + 280 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) m',
         ms' = MS R Fr (Z_to_bv 64 0x82abc) fc None m' (seg_rom rsegs) /\
         getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
         getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
         getr R 25 = x24 /\ getr R 22 = Z_to_bv 64 1 /\ getr R 24 = Z_to_bv 64 kv /\
         munch [(S3 + 16, S3 + 21)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         exists cs, rw_cells rsegs m' (S3 + 16) cs /\ cells_size cs = 5%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82aa4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 A kv bs E19 E9 HRW Hspill HMI H0 H1 HSA H0A H1A.
  apply (evtF_evt rsegs RNG_all).
  apply (f29_evt_F RNG_all x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
           x26 x27 x28 x29 x30 x31 Fr fc m S3 A kv bs E19 E9 HRW Hspill HMI H0 H1 HSA H0A H1A);
    apply rng_all; lia.
Qed.
Definition f29_evt_src_check : ltac:(let T := type of F29.f29_evt in exact T) := f29_evt_of_F.

(* f29_evt_F on the cut's own memory: ro_agree in place of mem_inv (F29.f29_evt_ro's route, with the evtF
   transfer MemNormF.evtF_normalize_ro). *)
Lemma f29_evt_ro_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 A kv : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x9 = Z_to_bv 64 A ->
    rw_cells rsegs m (S3 + 16) [CB 5 bs] -> bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 kv)) ->
    ro_agree rsegs m ->
    LOWMEM_END <= S3 -> S3 + 21 <= 2 ^ 64 -> S3 + 21 <= A -> 0 <= A -> A + 280 <= 2 ^ 64 ->
    rng RNG (S3 + 16) 5 -> rng RNG (A + 272) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) m',
         ms' = MS R Fr (Z_to_bv 64 0x82abc) fc None m' (seg_rom rsegs) /\
         getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
         getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
         getr R 25 = x24 /\ getr R 22 = Z_to_bv 64 1 /\ getr R 24 = Z_to_bv 64 kv /\
         munch [(S3 + 16, S3 + 21)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         exists cs, rw_cells rsegs m' (S3 + 16) cs /\ cells_size cs = 5%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82aa4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 A kv bs E19 E9 HRW Hspill HRO HS3 H1 HSA H0A H1A RS RA.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (HL : LOWMEM_END = 2147450880) by reflexivity.
  pose proof (f29_evt_F RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc (normalize rsegs m) S3 A kv bs E19 E9
    (F29.f29_rwc_norm m _ _ HRO HRW ltac:(lia) ltac:(cbn; lia)) (bytes_at_normalize rsegs m _ _ HRO Hspill)
    (mem_inv_normalize rsegs m) ltac:(lia) H1 HSA H0A H1A RS RA) as HC.
  pose proof (MemNormF.evtF_normalize_ro RNG _ _ _ _ _ _ m (seg_rom rsegs) HRO HC) as HN.
  eapply evtF_mono; [exact HN|].
  intros ms (s0' & (R & m0' & E & F2 & F3 & F4 & F8 & F9 & F18 & F19 & F20 & F26 & F27 & F25 & F22 & F24 &
                    MU & WM & MI' & cs & Hcs & Hcsl) & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists R, memX. split; [reflexivity|].
  do 13 (split; [assumption|]).
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  exists cs. split; [exact (F29.f29_rwc_back memX m0' _ _ Hmr Hcs) | exact Hcsl].
Qed.
