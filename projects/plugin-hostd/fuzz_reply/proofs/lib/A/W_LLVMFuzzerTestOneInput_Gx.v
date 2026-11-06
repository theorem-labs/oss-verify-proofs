(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the global set G_fr of fuzz_reply.asan's LLVMFuzzerTestOneInput, concretely, and
   every G_fr / errno fact that the W8 segment files (W_LLVMFuzzerTestOneInput_*.v, W_x*.v) take as a Section
   hypothesis, proved for it.  One witness that satisfies all of them at once is the check that those hypotheses do
   not contradict each other (at 45b95aa1834 SEG_EXIT's HG_SL and HG_err did); at integration these lemmas discharge
   the hypotheses.

   G_fr_c = the program's 20 objects [addr, addr + plain size) (maps/EvBound/GLOBALS.md: exactly the complement of
   AF0m's 20 redzone entries in Tfib_owned_static inside the two hulls) ++ errno's 4 bytes (send_line stores errno, and
   its G_SL names it, W_contract.v G_SL).

   Premises, each a start-up / instance fact discharged at the milestone:
     HEV  : as_errno B = 0x5d93cc      - AF0m's ts_errno (TFIB_ERRNO = TFIB_TP - 164; maps/EvBound/GLOBALS.md);
     HOWN : the bytes of G_fr_c are not in as_owned_static B - AF0m's ts_owned (as_owned_static B = Tfib_owned_static),
            by vm_compute at the milestone (AF0m is not in this tree).  Measured on cold/port-reply-startup
            56fc92fe6b0's AF0m.v: 0 of G_fr_c's 513 bytes lie in its 61 Tfib_owned_static ranges, and Tfib_zero_shadow
            has the range (0x5d88e0, 0x180) that makes `azs B (rg_s fr_RG) (4 * ASRC)` (HZS / AZS_s) true under ts_zsh
            (script and output: port-reply's w8/vac/own-zsh-check.txt). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_G.v, with its module paths changed; 347 of its 535 lines of code are new or changed and 16 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_G.v, with its module names changed; 14 of its 38 lines of code are new or changed and 511 lines of the source are left out. *)
(* G_fr witness lemmas for Section hypotheses that name a set defined in a segment file, so they cannot live in
   W_LLVMFuzzerTestOneInput_G.v (which those files' consumers import below them): proved for the same G_fr_c.
   XR_HGM / XR_ERRNO (_exit.v's source_reset piece lx_reset, at _exit.v's xr_GM): proofs by a Theorem Labs lane
   (XReset_wit.v (sha256 a4cf5df0c918; internal record), w8c rc=0), pasted unchanged; re-pointed from the superseded scratch W_xreset.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_exit.
Import ListNotations.
Open Scope Z_scope.

Section s.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HEV : as_errno B = TFIB_ERRNO_A.
(* XR_HGM at G_fr := G_fr_c *)
Lemma c_XR_HGM : forall a, inG W_LLVMFuzzerTestOneInput_exit.xr_GM a -> inG (G_fr_c B) a.
Proof.
  intros a Ha. apply obj_c. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  assert (Hb : forallb (fun r => rng_inb (fst r) (snd r) G_fr_obj) W_LLVMFuzzerTestOneInput_exit.xr_GM = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. destruct r as [lo n]. exact (rng_cover_zr lo n G_fr_obj (Hb _ Hr) a Hz).
Qed.
(* XR_ERRNO *)
Lemma c_XR_ERRNO : forall a, inG W_LLVMFuzzerTestOneInput_exit.xr_GM a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite HEV. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  assert (Hb : forallb (fun r => (fst r + snd r <=? TFIB_ERRNO_A) || (TFIB_ERRNO_A + 4 <=? fst r))
      W_LLVMFuzzerTestOneInput_exit.xr_GM = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. specialize (Hb r Hr). destruct r as [lo n]. hnf in Hz. cbn [fst snd] in Hz, Hb.
  apply orb_prop in Hb as [H|H]; apply Z.leb_le in H; lia.
Qed.
End s.
