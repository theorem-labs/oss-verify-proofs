(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths and module names changed; 717 of its 758 lines of code are new or changed and 110 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F31.v, with its module names and numbers changed; 139 of its 189 lines of code are new or changed and 708 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F33.v, with its module paths and module names changed; 30 of its 70 lines of code are new or changed and 149 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F33.v 392fed239604 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F33.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F33.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only.
   DEVIATION from the spec's "plain ExecF.rng lo len": f33_evt_F's footprint premise is `acc_in RNG (wa c, 8%nat)`,
   because F33.f33_evt puts NO bound on c, so `rng RNG c 8` (which carries 0 <= c and c + 8 <= 2^64) could not be
   discharged at RNG_all and f33_evt_of_F could not state F33.f33_evt unchanged. acc_in is the load's own access. *)
(* The footprint (ExecF.evtF) twin of the instruction run of segment F33 of fuzz_ctrl LLVMFuzzerTestOneInput (asan
   build of the patched image A): the head of row_of_block 0x8285c-0x8286c, for the cut-free twin SegCF/F33.v (not in this delivery)
   (RECIPE.md (a working note, not in this delivery): a hand re-walk with StepF).

   f33_evt_F is Seg/F33.v's f33_evt with the run an evtF under a footprint RNG and one premise for the one memory
   access the run's own instructions make.  The run calls nothing and writes no memory; its only access is the
   count-word load 0x82860 `ld s8,0(s8)`, 8 bytes at s8 = c (the frame byte range fr + 32 at the cut).  The load is
   not instrumented (no shadow check before it), and the two `beqz` and the `mv` touch no memory.

   The premise is `acc_in RNG (wa c, 8%nat)` (the load's own access in RNG), not `rng RNG c 8`: Seg/F33.v's f33_evt
   puts no bound on c, so an rng premise (which carries 0 <= c and c + 8 <= 2^64) could not be discharged at RNG_all
   by the corollary below, and the old statement could not be given back unchanged.  acc_in at RNG_all is True for
   every c.  The cut-free consumer gets the premise from its rng of the frame range by ExecF.rng_acc_lit.

   f33_evt_of_F re-derives Seg/F33.v's Exec.evt statement from f33_evt_F at RNG_all (ExecF.evtF_evt, the access
   premise by RNG_all).  v1.9.0 (libreac v1.9.0, 2026-10-28): the run is the v1.8 run at +0xac (a Theorem Labs lane's
   S_F33 (v190-segment-table.md (a working note, not in this delivery)): 0x8285c..0x82868, 4 instructions, IDENTICAL), walked by b8refit (18 pc
   literals, no refusal).  Seg/F33.v is the v1.9 halts file of a working branch (6479ee8c006) and keeps its
   own f33_evt; SegCF/F33.v (not in this delivery) checks in the kernel that f33_evt_of_F has exactly f33_evt's type, so this file states
   the same run as Seg/F33.v.

   rule 24: no function proved.  The run calls nothing, so this file assumes no callee contract: no Section
   Hypothesis, no Axiom, no Parameter.

   The branch helpers of the run (f33_eqb_lit and the tactics f33_bad / f33_nt) are here with Seg/F33.v's text and
   names (on v1.9 Seg/F33.v keeps its own copies, used by its own f33_evt); f33_nt is defined after the StepF import,
   so its if_cases is the evtF one. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts.
(* For the _of_F_verbatim pin only (Require, not Import: F33.v's own f33_eqb_lit / f33_bad / f33_nt copies must not
   shadow this file's). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F33.
(* Last (as in Seg/F38F.v): StepF's step / if_cases and ExecF's evtF_done match evtF goals and shadow Step's evt
   ones. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 may be the plain one here; the slot's
   cuts are stated with the image-A one, which this alias names (Seg/F33.v's own text). *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
(* ExecF/StepF re-open bv_scope on Import; our Z arithmetic needs Z_scope on top (as in Seg/F38F.v). *)
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ========================= branch helpers (Seg/F33.v's) ========================= *)

Lemma f33_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* A branch arm the facts in context exclude. *)
Ltac f33_bad HC :=
  exfalso;
  first [ congruence
        | discriminate HC
        | (rewrite ?f33_eqb_lit in HC by lia; apply Z.eqb_eq in HC; lia)
        | (vm_compute in HC; discriminate HC) ].
Ltac f33_nt := let H := fresh "HC" in first [ if_cases H; [f33_bad H | clear H] | idtac ].

(* ========================= the footprint run ========================= *)

(* 0x8285c -> 0x8286c with a0 <> 0 and the 8 bytes at s8 = c holding 11: both branches to 0x828bc fall through,
   s8 = 11 and s4 = a0.  The one access is the load 0x82860 `ld s8,0(s8)` of the 8 bytes at c. *)
Lemma f33_evt_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (T c : Z),
    x10 = Z_to_bv 64 T -> 0 < T < 2 ^ 64 ->
    x24 = Z_to_bv 64 c ->
    ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
    (* the load 0x82860 `ld s8,0(s8)` *)
    acc_in RNG (wa c, 8%nat) ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 T) x11 x12 x13 x14 x15 x16 x17 x18 x19
                              (Z_to_bv 64 T) x21 x22 x23 (Z_to_bv 64 11) x25 x26 x27 x28 x29 x30 x31)
                           Fr (Z_to_bv 64 0x8286c) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8285c) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m T c E10 HT E24 RD HACC.
  subst x10 x24.
  (* 0x8285c beqz a0,828bc: not taken *)
  step. f33_nt.
  (* 0x82860 ld s8,0(s8) = 11; 0x82864 beqz s8,828bc: not taken *)
  step. step. f33_nt.
  (* 0x82868 mv s4,a0 *)
  step. apply evtF_done. reflexivity.
Qed.

(* Seg/F33.v's f33_evt statement, at RNG_all (the access premise holds there for every c). *)
Lemma f33_evt_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (T c : Z),
    x10 = Z_to_bv 64 T -> 0 < T < 2 ^ 64 ->
    x24 = Z_to_bv 64 c ->
    ov_read_bytes rsegs m (wa c) 8 = Some (le8 (Z_to_bv 64 11)) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 T) x11 x12 x13 x14 x15 x16 x17 x18 x19
                              (Z_to_bv 64 T) x21 x22 x23 (Z_to_bv 64 11) x25 x26 x27 x28 x29 x30 x31)
                           Fr (Z_to_bv 64 0x8286c) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8285c) fcs None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f33_evt_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fcs m T c); try eassumption.
  exact I.
Qed.

(* The pin: f33_evt_of_F's statement is F33.f33_evt's, term for term (constr_eq: syntactic, not up to conversion). *)
Lemma f33_evt_of_F_verbatim : True.
Proof.
  let a := type of F33.f33_evt in let b := type of f33_evt_of_F in constr_eq a b.
  exact I.
Qed.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
