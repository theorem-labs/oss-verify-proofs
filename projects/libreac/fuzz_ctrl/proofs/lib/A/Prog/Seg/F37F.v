(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2962 of its 3089 lines of code are new or changed and 884 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F36.v, with its module paths, module names, addresses and numbers changed; 40 of its 88 lines of code are new or changed and 3041 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F37.v 7dd37c7d21be (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f37_evt_body_of_F re-derives F37.f37_evt_body at ExecF.RNG_all; f37_evt_body_of_F_verbatim checks by
   constr_eq that its type is the type of F37.f37_evt_body. Mechanical re-run, route (a) (lead 22:15Z); input to the
   ported walk only. *)
(* The footprint (ExecF.evtF) twin of the instruction run of segment F37 of fuzz_ctrl LLVMFuzzerTestOneInput (asan
   build of the patched image A): the frame-shadow stores and the call set-up 0x828d8-0x8293c, for the cut-free twin
   SegCF/F37.v (not in this delivery) (RECIPE.md (a working note, not in this delivery): a hand re-walk with StepF).

   f37_evt_body_F is Seg/F37.v's f37_evt_body with the run an evtF under a footprint RNG and one
   `rng RNG <addr> <len>` premise per region the run's own instructions read or write; the premise stays a premise
   (the cut-free consumer discharges it at its own footprint).  The run's accesses:
   - 0x828d8 `bne a0,s4,82bf4` (not taken, a0 = s4): no memory access;
   - 0x828dc-0x82934, the 23 one-byte stores `sb s11,o(s3)` with s3 = S3 = S(fr) and o in [22, 67): they write
     only the frame's own shadow bytes [S3 + 22, S3 + 67), so `rng RNG (S3 + 22) 45`.  They are the frame's
     (un)poisoning stores, not instrumented accesses: no shadow check runs before them, so no further premise;
   - 0x82938 `mv a0,s7` and 0x8293c `jal 53378` (the free wrapper at as_free ASYMS, ra = 0x82940): no memory
     access.
   f37_evt_body_of_F re-derives Seg/F37.v's Exec.evt statement from f37_evt_body_F at RNG_all (ExecF.evtF_evt, the
   rng premise by rng_all).  On v1.9 Seg/F37.v keeps its own run and does not import this file; that
   f37_evt_body_of_F has exactly the type of f37_evt_body is checked by SegCF/F37.v (f37cf_mirror_body), as
   SegCF/F38.v does for F38.

   The run ends AT the free wrapper's entry: the free itself is the segment's next step, outside this file.  The
   halts proof takes it through Seg/F37.v's f37_free (Contract.v aa_free with Seg/Tac_cls.v's sl_free_cls for the
   generation N.1 class premises), the cut-free twin through the free's cut-free contract (SegCF/F37.v, Section
   Hypothesis HFREEF) and the same sl_free_cls.  So this file states no class fact and leaves f37_free's
   allocator story as it is.

   v1.9.0 (libreac v1.9.0, 2026-10-28): the run of the v1.9 halts Seg/F37.v (a working branch bc157f20650): entry
   0x828d8, abort target 0x82bf4 (read off the v1.9 listing, `828d8: bne a0,s4,82bf4`), free wrapper 0x53378 (as_free
   ASYMS), return address 0x82940.  The store offsets 22 .. 66 into S(fr) are unchanged on v1.9: they are shadow bytes
   of the frame words [fr + 176, fr + 536), inside both the v1.8 and the v1.9 frame (FRAME_SHADOW = 392 on v1.9).

   rule 24: no function proved.  The run steps into no callee (its jal is its last instruction), so this file assumes
   no callee contract: no Section Hypothesis, no Axiom, no Parameter.

   The run's helper f37_le1_byte and its branch-arm tactics f37_bad / f37_nt (with f37_eqb_lit) are copies of
   Seg/F37.v's, with its text and names, so this file needs nothing of Seg/F37.v. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts.
(* For the _of_F_verbatim pin only (Require, not Import: F37.v's own helper copies must not shadow this file's). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F37.
(* Last (as in Seg/X12F.v, Seg/F31F.v and Seg/F38F.v): StepF's step / if_cases / mem_after_store and ExecF's
   evtF_done match evtF goals and shadow Step's evt ones. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 is the plain one here; the slot's
   cuts are stated with the image-A one, which this alias names (Seg/F37.v's own text). *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
(* ExecF/StepF re-open bv_scope on Import; our Z arithmetic needs Z_scope on top (as in Seg/F31F.v). *)
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ===================== helpers (Seg/F37.v's text) ===================== *)

(* A one-byte store of a register writes its low byte. *)
Lemma f37_le1_byte : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma f37_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* A branch arm the facts in context exclude. *)
Ltac f37_bad HC :=
  exfalso;
  first [ congruence
        | discriminate HC
        | (rewrite ?f37_eqb_lit in HC by lia; cbn [negb] in HC;
           first [ (apply Bool.negb_true_iff in HC; apply Z.eqb_neq in HC; lia)
                 | (apply Bool.negb_false_iff in HC; apply Z.eqb_eq in HC; lia)
                 | (apply Z.eqb_eq in HC; lia) | (apply Z.eqb_neq in HC; lia) ])
        | (unfold bv_eqb in HC; rewrite Z.eqb_refl in HC; cbn [negb] in HC; discriminate HC)
        | (vm_compute in HC; discriminate HC) ].
Ltac f37_nt := let H := fresh "HC" in first [ if_cases H; [f37_bad H | clear H] | idtac ].

(* ===================== the footprint run ===================== *)

(* 0x828d8 bne a0,s4 (not taken, a0 = s4); 0x828dc-0x82934 the 23 frame-shadow stores at S3 + 22 .. S3 + 66;
   0x82938 mv a0,s7; 0x8293c jal 0x53378 (as_free ASYMS) with ra = 0x82940. *)
Lemma f37_evt_body_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x10 = x20 ->
    rw_cells rsegs m S3 [CB 67 bs] -> 0 <= S3 -> S3 + 67 <= 2 ^ 64 ->
    (* the 23 frame-shadow stores 0x828dc-0x82934 `sb s11,o(s3)`, o in [22, 67) *)
    rng RNG (S3 + 22) 45 ->
    evtF rsegs RNG
      (fun ms' => exists m', ms' = MS (mkR (Z_to_bv 64 0x82940) x2 x3 x4 x5 x6 x7 x8 x9 x23 x11 x12 x13 x14 x15
                                          x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x53378) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 22, S3 + 67)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' S3 cs /\ cells_size cs = 67%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828d8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m S3 bs -> E1020 HRW H0 H1 RG.
  subst x10.
  pose proof (munch_refl [(S3 + 22, S3 + 67)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. f37_nt.
  do 23 (step; rewrite f37_le1_byte; mem_after_store).
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm S3 ?cs |- _ =>
      apply evtF_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

(* Seg/F37.v's f37_evt_body statement, at RNG_all (the rng premise by rng_all, from 0 <= S3, S3 + 67 <= 2^64). *)
Lemma f37_evt_body_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x10 = x20 ->
    rw_cells rsegs m S3 [CB 67 bs] -> 0 <= S3 -> S3 + 67 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR (Z_to_bv 64 0x82940) x2 x3 x4 x5 x6 x7 x8 x9 x23 x11 x12 x13 x14 x15
                                          x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x53378) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 22, S3 + 67)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' S3 cs /\ cells_size cs = 67%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828d8) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f37_evt_body_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fc m S3 bs); try eassumption; apply rng_all; lia.
Qed.

(* The pin: f37_evt_body_of_F's statement is F37.f37_evt_body's, term for term. *)
Lemma f37_evt_body_of_F_verbatim : True.
Proof.
  let a := type of F37.f37_evt_body in let b := type of f37_evt_body_of_F in constr_eq a b.
  exact I.
Qed.
