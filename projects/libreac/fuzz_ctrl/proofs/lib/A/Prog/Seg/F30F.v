(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2004 of its 2120 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F30.v; 54 of its 125 lines of code are new or changed and 2049 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F30.v acba01bfc56c (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f30_stores_of_F re-derives F30.f30_stores at ExecF.RNG_all; f30_stores_of_F_verbatim checks by constr_eq
   that its type is the type of F30.f30_stores. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk
   only.
   RE-FIT to this base: a Theorem Labs lane's 911c6aa5d2 was written against Seg/F30.v blob 5bb629fb22; the base's F30.v is
   acba01bfc56c (the blob this tree had at release c5e779efe8c). The whole difference is the file's header comment (that version's lines 3-5 say "v1.9 STATUS:
   UNVERIFIED ... waits for Tac_slot / Tac_fsfree re-fit"; acba01bfc56c lines 3-4 say "v1.9.0: moved onto
   [a Theorem Labs lane's] v1.9 cut bundle"), one line shorter, so NO statement, premise, numeral or proof of F30.v changed and
   this file's proof text is unchanged apart from the line citations below (f30_stores :290 -> :289,
   F30Call.f30_evt_call :505 -> :504, F30Call.f30_call_norm :584 -> :583). The verbatim pins checked the re-fit in
   the kernel; the call's pins now live in Seg/F30Fs.v. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
(* Footprint twin of a Theorem Labs lane's Seg/F30.v run f30_stores (segment F30, 0x8275c-0x82798, which ends in the call of
   reac_ctrl_classify_box_frame). rule 24: no function proved. The twin is the owner's run as an ExecF.evtF under a
   footprint RNG (forall RNG first), with the owner's premises unchanged and one rng premise per region the run
   reads or writes; f30_stores_of_F re-derives the owner's statement at ExecF.RNG_all (ExecF.evtF_evt, ExecF.rng_all).
   - f30_stores_F: F30.f30_stores (0x8275c -> 0x82794). The segment's own accesses: the 11 shadow bytes
     [S3 + 56, S3 + 67) (the six `sb`), the event cell [fr + 528, fr + 532) (`sw`), and the three spill reloads
     [A + 160], [A + 168], [A + 208].
   The CALL (0x82794 jal reac_ctrl_classify_box_frame, return pc 0x82798) is SPLIT in Seg/F30Fs.v (Theorem Labs split rule
   of a Theorem Labs lane with a Theorem Labs lane, 04:01Z): the of_pre_post lemmas there and their constr_eq pins are now the tie to
   F30.F30Call.f30_evt_call / f30_call_norm. This file's former module F30CallF (f30_evt_call_F, f30_call_F, their
   *_of_F corollaries and two pins, with the helpers f30_bytes_all / f30_sh_all / f30_img_all / f30_cls1_all) is
   DELETED (a Theorem Labs lane's decision 04:5xZ): it took the callee's footprint contract
   reac_ctrl_classify_box_frame_contract_F and rng_fp_cls1, which the glue base's
   lib/A/Prog/reac_ctrl_classify_box_frame_c.v (an earlier version, blob e726b412747, not in this delivery) (a working branch 5f2b9fab28a: a version not in this delivery) does not
   carry; a working branch's older version (an earlier version, blob 4ea5f8974df, not in this delivery) did. The Require of MemNormF and the Import of RngBytes, which only that
   module used, went with it. Nothing outside this file consumed F30CallF.

   v1.9.0 (2026-10-28): moved onto a Theorem Labs lane's v1.9 F30 runs (a working branch 7ecd59d267b; on this base,
   Seg/F30.v acba01bfc56c (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7, f30_stores :289). Every pc is copied from a Theorem Labs lane's text:
   v1.8 0x826b0 / 0x826e8 -> v1.9 0x8275c / 0x82794. The third spill reload is [A + 208] (v1.8 [A + 200]), the frame
   bound fr + 3136 (v1.8 fr + 3040) and S3 + 392 <= A (v1.8 S3 + 380), as in a Theorem Labs lane's text.
   The *_of_F_verbatim check pins the corollary to a Theorem Labs lane's text with constr_eq. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_parse_c bcmp_wrap_c memcmp_c
  asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs F29 F30.
(* Last: StepF's step / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
(* ExecF/StepF re-open bv_scope on Import; the Z arithmetic below needs Z_scope on top (as in F30.v). *)
Open Scope Z_scope.

(* ---- f30_stores as an evtF: six shadow stores, the event store, four register loads. *)
Lemma f30_stores_F :
  forall (RNG : ExecF.footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 A fr phi n : Z) (shb junk vb0 : list byte),
    x19 = Z_to_bv 64 S3 -> x9 = Z_to_bv 64 A -> x23 = Z_to_bv 64 phi -> x18 = Z_to_bv 64 n ->
    rw_cells rsegs m (S3 + 56) [CB 11 shb] ->
    rw_cells rsegs m (fr + 448) [CB 36 junk] ->
    rw_cells rsegs m (fr + 528) [CB 4 vb0] ->
    ro_cells rsegs m (A + 160) [C8 (Z_to_bv 64 (fr + 528))] ->
    ro_cells rsegs m (A + 168) [C8 (Z_to_bv 64 (fr + 2624))] ->
    ro_cells rsegs m (A + 208) [C8 (Z_to_bv 64 (fr + 448))] ->
    0 <= S3 -> (S3 + 67 <= fr \/ fr + 3136 <= S3) -> S3 + 392 <= A -> 0 <= fr -> fr + 3136 <= A ->
    A + 416 <= 2 ^ 64 ->
    ExecF.rng RNG (S3 + 56) 11 -> ExecF.rng RNG (fr + 528) 4 ->
    ExecF.rng RNG (A + 160) 8 -> ExecF.rng RNG (A + 168) 8 -> ExecF.rng RNG (A + 208) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m' mid,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 phi) (Z_to_bv 64 n) (Z_to_bv 64 (fr + 2624))
                       (Z_to_bv 64 (fr + 448)) (Z_to_bv 64 (fr + 528)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                       x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 0x82794) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 56, S3 + 67); (fr + 528, fr + 532)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (S3 + 56)
           [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 4);
            CB 5 mid; C1 (Z_to_bv 8 4)] /\
         rw_cells rsegs m' (fr + 448) [CB 36 junk] /\
         rw_cells rsegs m' (fr + 528) [CB 4 (le4 (Z_to_bv 64 (-1)))])
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) Fr (Z_to_bv 64 0x8275c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 Fr fc m S3 A fr phi n shb junk vb0 -> -> -> -> HRWs HRWo HRWv HR160 HR168 HR208
    HS30 HS3fr HS3A Hfr0 HfrA HA64 Rs56 Rv Ra160 Ra168 Ra208.
  pose proof (munch_refl [(S3 + 56, S3 + 67); (fr + 528, fr + 532)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound rsegs m (S3 + 56) [CB 11 shb] HRWs) as HB1.
  cbn [cells_size csize Nat.add] in HB1.
  pose proof (rw_cells_bound rsegs m (fr + 448) [CB 36 junk] HRWo) as HB2.
  cbn [cells_size csize Nat.add] in HB2.
  (* 0x8275c .. 0x82768: four zero shadow bytes *)
  step. try (rewrite le1_byte, (unsigned_lit 0) by lia; mem_after_store).
  step. try (rewrite le1_byte, (unsigned_lit 0) by lia; mem_after_store).
  step. try (rewrite le1_byte, (unsigned_lit 0) by lia; mem_after_store).
  step. try (rewrite le1_byte, (unsigned_lit 0) by lia; mem_after_store).
  (* 0x8276c li a0,4 ; 0x82770 sb a0,60(s3) ; 0x82774 sb a0,66(s3) *)
  step.
  step. try (rewrite le1_byte, (unsigned_lit 4) by lia; mem_after_store).
  step. try (rewrite le1_byte, (unsigned_lit 4) by lia; mem_after_store).
  (* 0x82778 ld a4,160(s1) ; 0x8277c li a0,-1 ; 0x82780 sw a0,0(a4) *)
  step. step. step.
  match goal with H : rw_cells rsegs ?mm (fr + 528) [C4 ?v] |- _ =>
    replace v with (Z_to_bv 64 (-1)) in H by (apply bv_eq; vm_compute; reflexivity);
    apply c4_cb in H
  end.
  (* 0x82784 mv a0,s7 ; 0x82788 mv a1,s2 ; 0x8278c ld a2,168(s1) ; 0x82790 ld a3,208(s1) *)
  step. step. step. step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with
    | Hs : rw_cells rsegs mm (S3 + 56) [_; _; _; _; _; CB 5 ?mid; _] |- _ =>
        apply ExecF.evtF_done; exists mm, mid;
        split; [reflexivity|]; split; [assumption|]; split; [assumption|];
        split; [exact Hs|]; split; assumption
    end
  end.
Qed.

Lemma f30_stores_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 A fr phi n : Z) (shb junk vb0 : list byte),
    x19 = Z_to_bv 64 S3 -> x9 = Z_to_bv 64 A -> x23 = Z_to_bv 64 phi -> x18 = Z_to_bv 64 n ->
    rw_cells rsegs m (S3 + 56) [CB 11 shb] ->
    rw_cells rsegs m (fr + 448) [CB 36 junk] ->
    rw_cells rsegs m (fr + 528) [CB 4 vb0] ->
    ro_cells rsegs m (A + 160) [C8 (Z_to_bv 64 (fr + 528))] ->
    ro_cells rsegs m (A + 168) [C8 (Z_to_bv 64 (fr + 2624))] ->
    ro_cells rsegs m (A + 208) [C8 (Z_to_bv 64 (fr + 448))] ->
    0 <= S3 -> (S3 + 67 <= fr \/ fr + 3136 <= S3) -> S3 + 392 <= A -> 0 <= fr -> fr + 3136 <= A ->
    A + 416 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m' mid,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 phi) (Z_to_bv 64 n) (Z_to_bv 64 (fr + 2624))
                       (Z_to_bv 64 (fr + 448)) (Z_to_bv 64 (fr + 528)) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                       x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 0x82794) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 56, S3 + 67); (fr + 528, fr + 532)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (S3 + 56)
           [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 4);
            CB 5 mid; C1 (Z_to_bv 8 4)] /\
         rw_cells rsegs m' (fr + 448) [CB 36 junk] /\
         rw_cells rsegs m' (fr + 528) [CB 4 (le4 (Z_to_bv 64 (-1)))])
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
               x28 x29 x30 x31) Fr (Z_to_bv 64 0x8275c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 Fr fc m S3 A fr phi n shb junk vb0 E19 E9 E23 E18 HRWs HRWo HRWv HR160 HR168 HR208
    HS30 HS3fr HS3A Hfr0 HfrA HA64.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f30_stores_F ExecF.RNG_all x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Fr fc m S3 A fr phi n shb junk vb0 E19 E9 E23 E18
           HRWs HRWo HRWv HR160 HR168 HR208 HS30 HS3fr HS3A Hfr0 HfrA HA64);
    apply ExecF.rng_all; lia.
Qed.

(* ---- The pin: f30_stores_of_F states the owner's v1.9 text, term for term (constr_eq: syntactic, not up to
   conversion). *)
Lemma f30_stores_of_F_verbatim : True.
Proof.
  let a := type of F30.f30_stores in let b := type of f30_stores_of_F in constr_eq a b.
  exact I.
Qed.
