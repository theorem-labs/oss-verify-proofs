(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 761 of its 797 lines of code are new or changed and 360 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F29.v, with its module paths and module names changed; 33 of its 73 lines of code are new or changed and 757 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F29.v d3deb22c0e79 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f29_evt_of_F re-derives F29.f29_evt at ExecF.RNG_all; f29_evt_of_F_verbatim checks by constr_eq that its
   type is the type of F29.f29_evt. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only.
   Adopted from a working branch b8e262d898 and re-fitted to this base: F29.v d3deb22c0e79 (the blob this tree had at release c5e779efe8c)
   at the Source pin (:5) and f180975499ba on a working branch 494a11ec7af, a COMMENT-ONLY difference (the header's v1.9 status
   line), so the run and its statement are the same text; the verbatim pin below checks that in the kernel.
   F29.sl_run_lib (Appendix A's other row) concludes SR, not evt, so it has no _F form under this spec: it is the
   slot engine's evt -> SR bridge, which the ported walk replaces. *)
(* The footprint twin of F29.v f29_evt: the same run (the three one-byte stores 0x82750, 0x82754, 0x82758 of the low
   byte of s11 to S3+16, S3+17, S3+20) as an ExecF.evtF under a footprint RNG, with one rng premise for the five shadow
   bytes S3+16 .. S3+20 the run writes. The statement follows f29_evt as a Theorem Labs lane re-fitted it onto the official
   cuts (a working branch d44a36fcf9, final 5fe947ede6): no mem_inv premise and no mem_inv conjunct in the post
   (the three stores do not need it, and the official cut's FRA carries ro_agree instead, SlotInv.v:160).
   f29_evt_of_F re-derives f29_evt's exact statement from f29_evt_F with RNG_all.
   v1.9.0 (2026-10-28): moved onto a Theorem Labs lane's v1.9 f29_evt (Seg/F29.v (at head lib/A/Prog/Seg/F29.v:527; written on a working branch 6143ff020f5)); the
   run is unchanged except its pcs (v1.8 0x826a4 .. 0x826b0 -> v1.9 0x82750 .. 0x8275c); the footprint is the same
   rng (S3 + 16) 5. f29_evt_of_F_verbatim checks with constr_eq that f29_evt_of_F states F29.f29_evt's exact text. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs F29.
(* Last: StepF's step / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* As in F29.v: the plain lib/Prog files also load lib/Reusable/YK11, so the image-A one (its seg_rom) is named by
   this alias and imported last among the term-level names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---- The run under a footprint: three one-byte stores to S(fr)+16, +17, +20 (S3 = S(fr)). *)
Lemma f29_evt_F :
  forall (RNG : ExecF.footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> rw_cells rsegs m (S3 + 16) [CB 5 bs] ->
    0 <= S3 -> S3 + 21 <= 2 ^ 64 ->
    ExecF.rng RNG (S3 + 16) 5 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                                          x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x8275c) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 16, S3 + 21)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 16) cs /\ cells_size cs = 5%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82750) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 bs -> HRW H0 H1 Rsh.
  pose proof (munch_refl [(S3 + 16, S3 + 21)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite F29.le1_byte. mem_after_store.
  step. rewrite F29.le1_byte. mem_after_store.
  step. rewrite F29.le1_byte. mem_after_store.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm (S3 + 16) ?cs |- _ =>
      apply ExecF.evtF_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

(* F29.f29_evt's statement as a corollary (evtF_evt of f29_evt_F RNG_all, the rng premise by rng_all). *)
Lemma f29_evt_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> rw_cells rsegs m (S3 + 16) [CB 5 bs] ->
    0 <= S3 -> S3 + 21 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                                          x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x8275c) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 16, S3 + 21)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 16) cs /\ cells_size cs = 5%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82750) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 bs E HRW H0 H1.
  eapply ExecF.evtF_evt, (f29_evt_F ExecF.RNG_all); try eassumption.
  apply ExecF.rng_all; lia.
Qed.

(* The pin: f29_evt_of_F's statement is F29.f29_evt's, term for term (constr_eq: syntactic, not up to conversion). *)
Lemma f29_evt_of_F_verbatim : True.
Proof.
  let a := type of F29.f29_evt in let b := type of f29_evt_of_F in constr_eq a b.
  exact I.
Qed.

(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
