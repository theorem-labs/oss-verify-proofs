(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/Tac_f17b.v f17_mc (:205-289) and the stretch F17b.v seg_F17b :1145-1174
     at a working branch 3803efccea0
     (blobs d8601d21afdf3de23b0d22a463c3f968fb2ab6dd, dc9ae8087a72de90382bb6524f59281543b429f5);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f17_post_F re-runs F17b.v lines 1145-1174 (the zero-step stretch from the memcpy return to the F18
     entry cut); f17_mc has NO _F twin, see below. *)
(* rule 24: no function proved. *)
(* The call side of segment S_F17b: `jal __asan_memcpy` at 0x82630, returning to 0x82634.
   The run is SPLIT at the call (parent, 23:50Z, binding): F17bF.v seg_F17b_pre_F stops AT the callee entry
   (pc = ASAN_MEMCPY, ra = 0x82634, a0 = fr + 2885, a1 = Phi + 27, a2 = gg[26]); this file holds the post
   stretch, which is EMPTY, because the return pc 0x82634 IS the F18 entry cut of the segment: f17_post_F takes
   the callee post facts the proved run uses there (Tac_f17b.f17_mc's post, in the segment's own vocabulary
   f17_mid / f17_cp) and concludes the segment's exit predicate with zero steps.
   `Tac_f17b.f17_mc` itself gets NO `_F` twin: it is the callee stretch (it starts at the __asan_memcpy entry
   and ends at the return), and it is proved from the Section hypothesis `asan_memcpy_contract`, a callee
   contract. The brief forbids stating a callee contract (plain or `_F`) locally; the walk (a Theorem Labs lane) composes
   the memcpy callee itself. Re-running f17_mc in evtF form would need an evtF form of that contract, which does
   not exist and which this lane must not invent. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F17b Tac_f17b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module ACPY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpy_c.

(* The post stretch of the memcpy call: from the return pc 0x82634 to the F18 entry cut 0x82634, zero steps.
   Premises: the two memory facts the proved run carries across the call at that point (F17b.v:1162-1174),
   f17_mid (the two stores of `first`, mem -> m0) and f17_cp (the copied body and the callee's write set,
   m0 -> m'). The conclusion is the run's own exit predicate. *)
Lemma f17_post_F : forall (RNG : footprint) (R Fr : bvmap 5 word) (fc : bv 32)
    (mem m0 m' : word -> option byte) (fr spz : Z) (gg : list byte),
  F17b.f17_mid fr gg mem m0 -> F17b.f17_cp fr spz gg m0 m' ->
  evtF rsegs RNG
    (fun ms' => exists (m'' : word -> option byte),
       ms' = MS R Fr (Z_to_bv 64 0x82634) fc None m'' (seg_rom rsegs) /\
       exists mm, F17b.f17_mid fr gg mem mm /\ F17b.f17_cp fr spz gg mm m'')
    (MS R Fr (Z_to_bv 64 0x82634) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R Fr fc mem m0 m' fr spz gg HMID HCP.
  apply evtF_done. exists m'. split; [reflexivity|]. exists m0. split; [exact HMID | exact HCP].
Qed.
