(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2962 of its 3089 lines of code are new or changed and 884 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F36.v, with its module names and numbers changed; 315 of its 421 lines of code are new or changed and 2983 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F38.v, with its module paths and module names changed; 98 of its 187 lines of code are new or changed and 332 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F38.v 2c3fae322ce4 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F38.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F38.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)
(* The footprint (ExecF.evtF) twins of the three instruction runs of segment F38 of fuzz_ctrl
   LLVMFuzzerTestOneInput (asan build of the patched image A): the frame-loop LATCH 0x82940-0x82960, for the
   cut-free twin SegCF/F38.v (not in this delivery) (RECIPE.md (a working note, not in this delivery): a hand re-walk with StepF).

   Each f38_evt_<run>_F is Seg/F38.v's f38_evt_<run> with the run an evtF under a footprint RNG and one
   `rng RNG <addr> <len>` premise per region the run's own instructions read or write; the premises stay premises
   (the cut-free consumer discharges them at its own footprint).  The latch makes no call and writes no memory, so
   the only accesses are the two spill reloads of the entry frame:
   - f38_evt_x_F (0x82940-0x82944, j = 255): `li a0,254` then the unsigned compare takes the branch to the
     epilogue before any load.  No memory access, so no rng premise.
   - f38_evt_b_F (0x82940-0x8295c, back edge) and f38_evt_e_F (0x82940-0x82960, input exhausted): the two spill
     reloads 0x82948 `ld s6,216(s1)` and 0x82950 `ld a0,224(s1)`, so `rng RNG (A + 216) 8` and
     `rng RNG (A + 224) 8`.  Neither load is instrumented (both are frame spill reloads, no shadow check before
     them), so no shadow premise is needed; the sums, the `addiw` and the two branches touch no memory.
   f38_evt_<run>_of_F re-derives Seg/F38.v's Exec.evt statement from f38_evt_<run>_F at RNG_all (ExecF.evtF_evt,
   every rng premise by rng_all).  On v1.9 Seg/F38.v keeps its own runs and does not import this file; that each
   _of_F has exactly the type of its f38_evt_<run> is checked by SegCF/F38.v (f38cf_mirror_x / _b / _e).

   v1.9.0 WALK (2026-10-28): every pc moved by b8refit with b8refit-v190.tsv (24 pcs, no refusal; entry 0x82940,
   back edge 0x81d40, epilogue 0x82b04), against the v1.9 halts Seg/F38.v; the spill offsets 216 / 224 and the
   bound 416 are unchanged on v1.9 (the latch reads neither the moved [A + 200] nor any FLC slot).

   rule 24: no function proved.  The latch calls nothing, so this file assumes no callee contract: no Section
   Hypothesis, no Axiom, no Parameter.

   The four bit-vector helpers of the runs (f38_eqb_lit, f38_ltu_lit, f38_swrap and the branch-arm tactic
   f38_bad) are copies of Seg/F38.v's, with its text and names, so this file needs nothing of Seg/F38.v. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts.
(* For the _of_F_verbatim pins only (Require, not Import: F38.v's own helper copies must not shadow this file's). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F38.
(* Last (as in Seg/X12F.v and Seg/F31F.v): StepF's step / if_cases and ExecF's evtF_done match evtF goals and
   shadow Step's evt ones. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 is the plain one here; the slot's
   cuts are stated with the image-A one, which this alias names (Seg/F38.v's own text). *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
(* ExecF/StepF re-open bv_scope on Import; our Z arithmetic needs Z_scope on top (as in Seg/F31F.v). *)
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* The core copy an _F statement names (a Theorem Labs lane 08:56Z rule): LMS (lib.Lib's MState). *)
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

(* ===================== bit-vector helpers ===================== *)

Lemma f38_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma f38_ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* A 32-bit add of two small values keeps its value (the `addiw` of the turn counter). *)
Lemma f38_swrap : forall x, 0 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

(* A branch arm the facts in context exclude. *)
Ltac f38_bad HC :=
  exfalso;
  first [ congruence
        | (zify_cond HC; rewrite ?LMS.unsigned_lit in HC by lia; lia)
        | (rewrite ?f38_ltu_lit, ?f38_eqb_lit in HC by lia; cbn [negb] in HC;
           first [ apply Bool.negb_true_iff in HC | apply Bool.negb_false_iff in HC | idtac ];
           first [ apply Z.ltb_lt in HC | apply Z.ltb_ge in HC
                 | apply Z.eqb_eq in HC | apply Z.eqb_neq in HC ];
           lia)
        | (vm_compute in HC; discriminate HC) ].

(* ===================== the footprint runs ===================== *)

(* j = 255: `li a0,254` then the unsigned compare 254 < j takes the branch to the epilogue.  No memory access. *)
Lemma f38_evt_x_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (jv : Z),
    x21 = Z_to_bv 64 jv -> 255 <= jv < 2 ^ 64 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 254) x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            Fr (Z_to_bv 64 0x82b04) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82940) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m jv -> Hj.
  step. step. if_cases HC; [apply evtF_done; reflexivity | f38_bad HC].
Qed.

(* Seg/F38.v's f38_evt_x statement, at RNG_all. *)
Lemma f38_evt_x_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (jv : Z),
    x21 = Z_to_bv 64 jv -> 255 <= jv < 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 254) x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            Fr (Z_to_bv 64 0x82b04) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82940) fcs None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f38_evt_x_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fcs m jv); eassumption.
Qed.

(* The pin: f38_evt_x_of_F's statement is F38.f38_evt_x's, term for term. *)
Lemma f38_evt_x_of_F_verbatim : True.
Proof.
  let a := type of F38.f38_evt_x in let b := type of f38_evt_x_of_F in constr_eq a b.
  exact I.
Qed.

(* j <= 254 and the input is not exhausted (aa <> cc): the two spill loads, the two sums and the back edge. *)
Lemma f38_evt_b_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (A aa bb cc jv : Z),
    x9 = Z_to_bv 64 A -> x18 = Z_to_bv 64 cc -> x21 = Z_to_bv 64 jv ->
    0 <= jv <= 254 -> 416 <= A -> A + 416 <= 2 ^ 64 ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 bb)] ->
    ro_cells rsegs m (A + 224) [C8 (Z_to_bv 64 aa)] ->
    0 <= bb < 2 ^ 64 -> 0 <= cc <= aa -> aa < 2 ^ 64 -> aa <> cc ->
    (* the two spill reloads 0x82948 `ld s6,216(s1)` and 0x82950 `ld a0,224(s1)` *)
    rng RNG (A + 216) 8 -> rng RNG (A + 224) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 aa) x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 (Z_to_bv 64 (jv + 1)) (Z_to_bv 64 (bb + cc)) x23 x24
                                (Z_to_bv 64 (aa - cc)) x26 x27 x28 x29 x30 x31)
                            Fr (Z_to_bv 64 0x81d40) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82940) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m A aa bb cc jv -> -> -> Hj HA0 HA1 R216 R224 Hbb Hcc Haa Hne
    RG216 RG224.
  step. step. if_cases HC1; [f38_bad HC1|].
  rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit A) by lia. step.
  step.
  rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit A) by lia. step.
  step. step.
  rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. rewrite ?f38_swrap by lia.
  step. if_cases HC2; [apply evtF_done; reflexivity | f38_bad HC2].
Qed.

(* Seg/F38.v's f38_evt_b statement, at RNG_all (both rng premises by rng_all, from 416 <= A, A + 416 <= 2^64). *)
Lemma f38_evt_b_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (A aa bb cc jv : Z),
    x9 = Z_to_bv 64 A -> x18 = Z_to_bv 64 cc -> x21 = Z_to_bv 64 jv ->
    0 <= jv <= 254 -> 416 <= A -> A + 416 <= 2 ^ 64 ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 bb)] ->
    ro_cells rsegs m (A + 224) [C8 (Z_to_bv 64 aa)] ->
    0 <= bb < 2 ^ 64 -> 0 <= cc <= aa -> aa < 2 ^ 64 -> aa <> cc ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 aa) x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 (Z_to_bv 64 (jv + 1)) (Z_to_bv 64 (bb + cc)) x23 x24
                                (Z_to_bv 64 (aa - cc)) x26 x27 x28 x29 x30 x31)
                            Fr (Z_to_bv 64 0x81d40) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82940) fcs None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f38_evt_b_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fcs m A aa bb cc jv); try eassumption; apply rng_all; lia.
Qed.

(* The pin: f38_evt_b_of_F's statement is F38.f38_evt_b's, term for term. *)
Lemma f38_evt_b_of_F_verbatim : True.
Proof.
  let a := type of F38.f38_evt_b in let b := type of f38_evt_b_of_F in constr_eq a b.
  exact I.
Qed.

(* j <= 254 and the input is exhausted (aa = cc): the same loads, then the fall-through jump to the epilogue. *)
Lemma f38_evt_e_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (A aa bb cc jv : Z),
    x9 = Z_to_bv 64 A -> x18 = Z_to_bv 64 cc -> x21 = Z_to_bv 64 jv ->
    0 <= jv <= 254 -> 416 <= A -> A + 416 <= 2 ^ 64 ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 bb)] ->
    ro_cells rsegs m (A + 224) [C8 (Z_to_bv 64 aa)] ->
    0 <= bb < 2 ^ 64 -> 0 <= cc <= aa -> aa < 2 ^ 64 -> aa = cc ->
    (* the same two spill reloads *)
    rng RNG (A + 216) 8 -> rng RNG (A + 224) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 aa) x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 (Z_to_bv 64 (jv + 1)) (Z_to_bv 64 (bb + cc)) x23 x24
                                (Z_to_bv 64 (aa - cc)) x26 x27 x28 x29 x30 x31)
                            Fr (Z_to_bv 64 0x82b04) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82940) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m A aa bb cc jv -> -> -> Hj HA0 HA1 R216 R224 Hbb Hcc Haa Heq
    RG216 RG224.
  step. step. if_cases HC1; [f38_bad HC1|].
  rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit A) by lia. step.
  step.
  rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit A) by lia. step.
  step. step.
  rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. rewrite ?f38_swrap by lia.
  step. if_cases HC2; [f38_bad HC2|].
  step. apply evtF_done. reflexivity.
Qed.

(* Seg/F38.v's f38_evt_e statement, at RNG_all. *)
Lemma f38_evt_e_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (A aa bb cc jv : Z),
    x9 = Z_to_bv 64 A -> x18 = Z_to_bv 64 cc -> x21 = Z_to_bv 64 jv ->
    0 <= jv <= 254 -> 416 <= A -> A + 416 <= 2 ^ 64 ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 bb)] ->
    ro_cells rsegs m (A + 224) [C8 (Z_to_bv 64 aa)] ->
    0 <= bb < 2 ^ 64 -> 0 <= cc <= aa -> aa < 2 ^ 64 -> aa = cc ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 aa) x11 x12 x13 x14 x15 x16 x17 x18
                                x19 x20 (Z_to_bv 64 (jv + 1)) (Z_to_bv 64 (bb + cc)) x23 x24
                                (Z_to_bv 64 (aa - cc)) x26 x27 x28 x29 x30 x31)
                            Fr (Z_to_bv 64 0x82b04) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82940) fcs None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f38_evt_e_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fcs m A aa bb cc jv); try eassumption; apply rng_all; lia.
Qed.

(* The pin: f38_evt_e_of_F's statement is F38.f38_evt_e's, term for term. *)
Lemma f38_evt_e_of_F_verbatim : True.
Proof.
  let a := type of F38.f38_evt_e in let b := type of f38_evt_e_of_F in constr_eq a b.
  exact I.
Qed.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
