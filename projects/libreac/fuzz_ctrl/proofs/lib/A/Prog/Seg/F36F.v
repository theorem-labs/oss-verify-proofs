(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2962 of its 3089 lines of code are new or changed and 884 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F36.v; 429 of its 728 lines of code are new or changed and 2790 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F36.v blob 242c29c887f9 at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F36.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F36.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only.
   NOTE: the two runs of Seg/F36.v that cross the call of reac_box_catalogue_match at 0x828d4 (f36_evt_call,
   f36_call_norm) are re-run here by the callee's footprint contract of record, a Theorem Labs lane's
   reac_box_catalogue_match_c.reac_box_catalogue_match_contract_F (lib/A/Prog/reac_box_catalogue_match_c.v:152, blob
   ccd3e1f3c75), cited BY NAME in the plain contract's premise position (the R14F shape: Seg/R14F.v r14_call_F,
   r14_call_of_F, r14_call_of_F_verbatim), so their _of_F corollaries take that contract_F as their FIRST premise and
   the pins check it by name and constr_eq the rest.  The walk does NOT use these two: it takes the callee by
   a Theorem Labs lane's cgif-form spec, through the split stretches of Seg/F36Fs.v. *)
(* The footprint (ExecF.evtF) twins of the instruction runs of segment F36 of fuzz_ctrl LLVMFuzzerTestOneInput (asan
   build of the patched image A): the row-loop body and the join block 0x8289c-0x828d4 with the call of
   reac_box_catalogue_match at 0x828d4 (whose split stretches are in Seg/F36Fs.v), for the cut-free twin SegCF/F36.v (not in this delivery)
   (RECIPE.md (a working note, not in this delivery): a hand re-walk with StepF).

   Each f36_evt_<run>_F is Seg/F36.v's lemma of that name without _F, with the run an evtF
   under a footprint RNG and one `rng RNG <addr> <len>` premise per region the run's own instructions read or write;
   the premises stay premises (the cut-free consumer discharges them at its own footprint).  s3 = S3 is the frame's
   shadow base S(fr) at every use in Seg/F36.v.  The segment's own accesses are its nine one-byte shadow stores
   (four at 0x828a0-0x828ac, four at 0x82964-0x82970, one at 0x828c0); the segment makes no load, and the moves, the
   li, the adds, the jumps and the branches touch no memory:
   - f36_evt_hit_F (0x8289c beqz taken), f36_evt_miss_F (0x8289c not taken), f36_evt_82810_F (0x828bc li s4,0),
     f36_evt_8281c_F (0x828c8 li s4,0): no memory access, so no rng premise.
   - f36_evt_back_F and f36_evt_out_F (0x828a0-0x828b8): 0x828a0 `sb s11,8(s3)`, 0x828a4 `sb s11,9(s3)`,
     0x828a8 `sb s11,10(s3)`, 0x828ac `sb s11,11(s3)`: `rng RNG (S3 + 8) 4`.
   - f36_evt_828b8_F (0x82964-0x82974): the same four stores at 0x82964, 0x82968, 0x8296c, 0x82970:
     `rng RNG (S3 + 8) 4`.
   - f36_evt_82814_F (0x828c0-0x828c4): 0x828c0 `sb s11,4(s3)`: `rng RNG (S3 + 4) 1`.
   - f36_evt_call_F (0x828cc `mv a0,s7`, 0x828d0 `mv a1,s2`, 0x828d4 `jal reac_box_catalogue_match`): the moves and
     the jal touch no memory; every rng premise is the callee's own, as reac_box_catalogue_match_contract_F states
     them, at f := phi, len := len, S := S, FS := FS and in its order (rng_bytes; the image [0x10000, 0x5fe000); the
     window [S - CM_K, S); the 50 bytes at phi and their 8-aligned shadow words when 50 <= len; the 8-aligned shadow
     words of the catalogue [CM_T, CM_T + 3256) and of the 6 bytes at REAC_CTRL_PARSE_BC; the window's shadow;
     rng_fp_cm of the classes 0 / 1 / 2).
   - f36_call_norm_F: f36_evt_call_F run on the normalized memory (MemNormF.evtF_normalize_ro), the same premises,
     rng_fp_cm stated at the caller's memory (moved to the normalized one by Seg/F36.v's f36_tls_rel).
   f36_evt_<run>_of_F re-derive Seg/F36.v's Exec.evt statements from the _F lemmas at RNG_all (ExecF.evtF_evt, every
   rng premise by rng_all); each one's statement is, word for word, the statement of the lemma of that name in the v1.9
   Seg/F36.v (a working branch 7ecd59d267b), which keeps its own run lemmas; for the two call runs the first
   premise, the callee's plain contract, is replaced by its contract_F (the plain contract does not give the _F one).

   The helpers only these runs use (f36_le1_byte, f36_eqb_lit and the branch tactics f36_bad / f36_nt / f36_tk) are
   Seg/F36.v's text and names; the call runs cite Seg/F36.v's own normalization relations (F36.f36_stk_rel ..
   F36.f36_cmtls_rel) and wrapper cells by name.  rule 24: no function proved; no Section Hypothesis, Axiom or
   Parameter in this file.

   v1.9 (libreac v1.9.0): every pc is the v1.8 one + 0xac (tools/b8refit, map b8refit-v190.tsv; the marker is the
   last line).  The run lemmas change nothing else: the segment's accesses (the nine shadow stores) are the v1.8
   ones. *)
From Stdlib Require Import ZArith List Bool Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag RcMatch.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  asan_stack_malloc_c reac_box_catalogue_match_c reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs.
(* For the _of_F_verbatim pins only (Require, not Import: F36.v's own helper copies must not shadow this file's). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F36.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* Last (as in Seg/F38F.v, Seg/X12F.v and Seg/F31F.v): StepF's step / if_cases / mem_after_store and ExecF's evtF_done
   match evtF goals and shadow Step's evt ones; RngBytes names rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
(* The plain lib/Prog files the catalogue-match contract rests on also load lib/Reusable/YK11, so the short name
   YK11 is the plain one here; the slot's cuts are stated with the image-A one, which this alias names (Seg/F36.v's
   own text). *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
(* ExecF/StepF re-open bv_scope on Import; our Z arithmetic needs Z_scope on top (as in Seg/F38F.v). *)
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ===================== helpers of the runs ===================== *)

(* A one-byte store of a register writes its low byte. *)
Lemma f36_le1_byte : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma f36_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* A branch arm the facts in context exclude. *)
Ltac f36_bad HC :=
  exfalso;
  first [ congruence
        | discriminate HC
        | (rewrite ?f36_eqb_lit in HC by lia; cbn [negb] in HC;
           first [ (apply Bool.negb_true_iff in HC; apply Z.eqb_neq in HC; lia)
                 | (apply Bool.negb_false_iff in HC; apply Z.eqb_eq in HC; lia)
                 | (apply Z.eqb_eq in HC; lia) | (apply Z.eqb_neq in HC; lia) ])
        | (vm_compute in HC; discriminate HC) ].
Ltac f36_nt := let H := fresh "HC" in first [ if_cases H; [f36_bad H | clear H] | idtac ].
Ltac f36_tk := let H := fresh "HC" in first [ if_cases H; [clear H | f36_bad H] | idtac ].

(* ===================== the footprint runs without a call ===================== *)

(* 0x8289c with a0 = 0: beqz is taken to 0x82964.  No memory access. *)
Lemma f36_evt_hit_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    x10 = Z_to_bv 64 0 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                              x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82964) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8289c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m E10. subst x10.
  step. f36_tk. apply evtF_done. reflexivity.
Qed.

(* Seg/F36.v's f36_evt_hit statement, at RNG_all. *)
Lemma f36_evt_hit_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    x10 = Z_to_bv 64 0 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                              x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82964) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8289c) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f36_evt_hit_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fc m); eassumption.
Qed.

Lemma f36_evt_hit_of_F_verbatim : True.
Proof.
  let a := type of F36.f36_evt_hit in let b := type of f36_evt_hit_of_F in constr_eq a b.
  exact I.
Qed.

(* 0x8289c with a0 = v <> 0: beqz is not taken; the run is at 0x828a0.  No memory access. *)
Lemma f36_evt_miss_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
    x10 = Z_to_bv 64 v -> 0 < v < 2 ^ 64 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                              x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828a0) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8289c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m v E10 Hv. subst x10.
  step. f36_nt. apply evtF_done. reflexivity.
Qed.

(* Seg/F36.v's f36_evt_miss statement, at RNG_all. *)
Lemma f36_evt_miss_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
    x10 = Z_to_bv 64 v -> 0 < v < 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                              x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828a0) fc None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x8289c) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f36_evt_miss_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fc m v); eassumption.
Qed.

Lemma f36_evt_miss_of_F_verbatim : True.
Proof.
  let a := type of F36.f36_evt_miss in let b := type of f36_evt_miss_of_F in constr_eq a b.
  exact I.
Qed.

(* 0x828a0 -> 0x828b8: the four shadow stores to S3 + 8 .. S3 + 11, s8 = c - 1, s4 = s + 296; with c >= 2 the
   back branch is taken to 0x8286c. *)
Lemma f36_evt_back_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 c s : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x24 = Z_to_bv 64 c -> x20 = Z_to_bv 64 s ->
    2 <= c <= 11 -> 0 <= s -> s + 296 < 2 ^ 64 ->
    rw_cells rsegs m (S3 + 8) [CB 4 bs] -> 0 <= S3 -> S3 + 12 <= 2 ^ 64 ->
    (* the four shadow stores 0x828a0 `sb s11,8(s3)` .. 0x828ac `sb s11,11(s3)` *)
    rng RNG (S3 + 8) 4 ->
    evtF rsegs RNG
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                                          (Z_to_bv 64 (s + 296)) x21 x22 x23 (Z_to_bv 64 (c - 1)) x25 x26 x27 x28
                                          x29 x30 x31)
                                     Fr (Z_to_bv 64 0x8286c) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 8) cs /\ cells_size cs = 4%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828a0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m S3 c s bs -> -> -> Hc Hs0 Hs1 HRW H0 H1 RG8.
  pose proof (munch_refl [(S3 + 8, S3 + 12)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. step. step. f36_tk.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm (S3 + 8) ?cs |- _ =>
      apply evtF_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

(* Seg/F36.v's f36_evt_back statement, at RNG_all (the rng premise by rng_all, from 0 <= S3, S3 + 12 <= 2^64). *)
Lemma f36_evt_back_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 c s : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x24 = Z_to_bv 64 c -> x20 = Z_to_bv 64 s ->
    2 <= c <= 11 -> 0 <= s -> s + 296 < 2 ^ 64 ->
    rw_cells rsegs m (S3 + 8) [CB 4 bs] -> 0 <= S3 -> S3 + 12 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                                          (Z_to_bv 64 (s + 296)) x21 x22 x23 (Z_to_bv 64 (c - 1)) x25 x26 x27 x28
                                          x29 x30 x31)
                                     Fr (Z_to_bv 64 0x8286c) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 8) cs /\ cells_size cs = 4%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828a0) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f36_evt_back_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fc m S3 c s bs); try eassumption; apply rng_all; lia.
Qed.

Lemma f36_evt_back_of_F_verbatim : True.
Proof.
  let a := type of F36.f36_evt_back in let b := type of f36_evt_back_of_F in constr_eq a b.
  exact I.
Qed.

(* The same run with c = 1 (the last row): the back branch falls through to 0x828bc. *)
Lemma f36_evt_out_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 s : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x24 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 s ->
    0 <= s -> s + 296 < 2 ^ 64 ->
    rw_cells rsegs m (S3 + 8) [CB 4 bs] -> 0 <= S3 -> S3 + 12 <= 2 ^ 64 ->
    (* the four shadow stores 0x828a0 `sb s11,8(s3)` .. 0x828ac `sb s11,11(s3)` *)
    rng RNG (S3 + 8) 4 ->
    evtF rsegs RNG
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                                          (Z_to_bv 64 (s + 296)) x21 x22 x23 (Z_to_bv 64 0) x25 x26 x27 x28
                                          x29 x30 x31)
                                     Fr (Z_to_bv 64 0x828bc) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 8) cs /\ cells_size cs = 4%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828a0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m S3 s bs -> -> -> Hs0 Hs1 HRW H0 H1 RG8.
  pose proof (munch_refl [(S3 + 8, S3 + 12)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. step. step. f36_nt.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm (S3 + 8) ?cs |- _ =>
      apply evtF_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

(* Seg/F36.v's f36_evt_out statement, at RNG_all. *)
Lemma f36_evt_out_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 s : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x24 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 s ->
    0 <= s -> s + 296 < 2 ^ 64 ->
    rw_cells rsegs m (S3 + 8) [CB 4 bs] -> 0 <= S3 -> S3 + 12 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                                          (Z_to_bv 64 (s + 296)) x21 x22 x23 (Z_to_bv 64 0) x25 x26 x27 x28
                                          x29 x30 x31)
                                     Fr (Z_to_bv 64 0x828bc) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 8) cs /\ cells_size cs = 4%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828a0) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f36_evt_out_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fc m S3 s bs); try eassumption; apply rng_all; lia.
Qed.

Lemma f36_evt_out_of_F_verbatim : True.
Proof.
  let a := type of F36.f36_evt_out in let b := type of f36_evt_out_of_F in constr_eq a b.
  exact I.
Qed.

(* 0x828bc li s4,0 -> 0x828c0.  No memory access. *)
Lemma f36_evt_82810_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0)
                              x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c0) fc None m
                           (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828bc) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evtF_done. reflexivity. Qed.

(* Seg/F36.v's f36_evt_82810 statement, at RNG_all. *)
Lemma f36_evt_82810_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0)
                              x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c0) fc None m
                           (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828bc) fc None m (seg_rom rsegs)).
Proof. intros. eapply (evtF_evt rsegs RNG_all). apply (f36_evt_82810_F RNG_all). Qed.

Lemma f36_evt_82810_of_F_verbatim : True.
Proof.
  let a := type of F36.f36_evt_82810 in let b := type of f36_evt_82810_of_F in constr_eq a b.
  exact I.
Qed.

(* 0x828c8 li s4,0 -> 0x828cc.  No memory access. *)
Lemma f36_evt_8281c_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0)
                              x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828cc) fc None m
                           (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evtF_done. reflexivity. Qed.

(* Seg/F36.v's f36_evt_8281c statement, at RNG_all. *)
Lemma f36_evt_8281c_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0)
                              x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828cc) fc None m
                           (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fc None m (seg_rom rsegs)).
Proof. intros. eapply (evtF_evt rsegs RNG_all). apply (f36_evt_8281c_F RNG_all). Qed.

Lemma f36_evt_8281c_of_F_verbatim : True.
Proof.
  let a := type of F36.f36_evt_8281c in let b := type of f36_evt_8281c_of_F in constr_eq a b.
  exact I.
Qed.

(* 0x828c0 sb s11,4(s3) ; j 828cc: the shadow byte S3 + 4. *)
Lemma f36_evt_82814_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> rw_cells rsegs m (S3 + 4) [CB 1 bs] ->
    0 <= S3 -> S3 + 5 <= 2 ^ 64 ->
    (* the shadow store 0x828c0 `sb s11,4(s3)` *)
    rng RNG (S3 + 4) 1 ->
    evtF rsegs RNG
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                                          x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x828cc) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 4, S3 + 5)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 4) cs /\ cells_size cs = 1%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m S3 bs -> HRW H0 H1 RG4.
  pose proof (munch_refl [(S3 + 4, S3 + 5)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite f36_le1_byte. mem_after_store.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm (S3 + 4) ?cs |- _ =>
      apply evtF_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

(* Seg/F36.v's f36_evt_82814 statement, at RNG_all. *)
Lemma f36_evt_82814_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> rw_cells rsegs m (S3 + 4) [CB 1 bs] ->
    0 <= S3 -> S3 + 5 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                                          x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x828cc) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 4, S3 + 5)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 4) cs /\ cells_size cs = 1%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c0) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f36_evt_82814_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fc m S3 bs); try eassumption; apply rng_all; lia.
Qed.

Lemma f36_evt_82814_of_F_verbatim : True.
Proof.
  let a := type of F36.f36_evt_82814 in let b := type of f36_evt_82814_of_F in constr_eq a b.
  exact I.
Qed.

(* 0x82964 sb s11,8(s3) .. sb s11,11(s3) ; j 828c0: the row-matched arm marks the row slot's four shadow bytes
   (F38 leaves the block 0x82964-0x82974 to this segment). *)
Lemma f36_evt_828b8_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> rw_cells rsegs m (S3 + 8) [CB 4 bs] -> 0 <= S3 -> S3 + 12 <= 2 ^ 64 ->
    (* the four shadow stores 0x82964 `sb s11,8(s3)` .. 0x82970 `sb s11,11(s3)` *)
    rng RNG (S3 + 8) 4 ->
    evtF rsegs RNG
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                                          x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x828c0) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 8) cs /\ cells_size cs = 4%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82964) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m S3 bs -> HRW H0 H1 RG8.
  pose proof (munch_refl [(S3 + 8, S3 + 12)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step. rewrite f36_le1_byte. mem_after_store.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm (S3 + 8) ?cs |- _ =>
      apply evtF_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

(* Seg/F36.v's f36_evt_828b8 statement, at RNG_all. *)
Lemma f36_evt_828b8_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> rw_cells rsegs m (S3 + 8) [CB 4 bs] -> 0 <= S3 -> S3 + 12 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                                          x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x828c0) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 8, S3 + 12)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 8) cs /\ cells_size cs = 4%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82964) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f36_evt_828b8_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fc m S3 bs); try eassumption; apply rng_all; lia.
Qed.

Lemma f36_evt_828b8_of_F_verbatim : True.
Proof.
  let a := type of F36.f36_evt_828b8 in let b := type of f36_evt_828b8_of_F in constr_eq a b.
  exact I.
Qed.

(* ===================== the call of reac_box_catalogue_match at 0x828d4 ===================== *)

(* The callee's footprint contract OF RECORD: a Theorem Labs lane's reac_box_catalogue_match_contract_F
   (lib/A/Prog/reac_box_catalogue_match_c.v:152 (an earlier version, blob ccd3e1f3c75, not in this delivery), signed by the auditor a Theorem Labs lane 05:5xZ), cited by
   name.  CMC is that file; its rng_fp_cm (:131) is the side-stack / thread-cell premise, bound free in the memory,
   and MNF is the normalization lift of the second run.  Both runs take the contract in the FIRST premise position,
   where Seg/F36.v's own runs take the PLAIN contract (the R14F shape, Seg/R14F.v:136 / :267 / :323-331). *)
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module CMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_match_c.

(* Seg/F36.v's own constants, by name: the _of_F corollaries' statements name THOSE constants, so a same-valued copy
   here would make the constr_eq pins fail.  Notation, not Definition: it expands at parse time. *)
Local Notation BCMP := F36.BCMP.
Local Notation REAL_BCMP := F36.REAL_BCMP.
Local Notation REAL_MEMCMP := F36.REAL_MEMCMP.
Local Notation MEMCMP := F36.MEMCMP.
Local Notation f36_W := F36.f36_W.

(* 0x828cc mv a0,s7 ; 0x828d0 mv a1,s2 ; 0x828d4 jal reac_box_catalogue_match -> 0x828d8, by the callee's footprint
   contract.  The three instructions touch no memory; every rng premise below is the callee's own, instantiated at
   f := phi, len := len, S := S, FS := FS, in the order reac_box_catalogue_match_contract_F states them. *)
Lemma f36_evt_call_F : CMC.reac_box_catalogue_match_contract_F ->
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s7 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi fb /\ (phi + 50 <= S - CM_K \/ S <= phi)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m phi 50 /\ app_mem (phi + 50)) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    (* the callee's footprint premises at the jal 0x828d4, passed through unchanged *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (S - CM_K) CM_K ->
    (50 <= len -> rng RNG phi 50 /\
                  rng RNG (8 * (shadow_addr phi / 8))
                    (8 * (shadow_addr (phi + 49) / 8) + 8 - 8 * (shadow_addr phi / 8))) ->
    rng RNG (8 * (shadow_addr CM_T / 8))
      (8 * (shadow_addr (CM_T + 3255) / 8) + 8 - 8 * (shadow_addr CM_T / 8)) ->
    rng RNG (8 * (shadow_addr REAC_CTRL_PARSE_BC / 8))
      (8 * (shadow_addr (REAC_CTRL_PARSE_BC + 5) / 8) + 8 - 8 * (shadow_addr REAC_CTRL_PARSE_BC / 8)) ->
    rng RNG (shadow_addr (S - CM_K)) (shadow_addr S - shadow_addr (S - CM_K)) ->
    CMC.rng_fp_cm RNG m (bv_unsigned tp) FS ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x828d8) fc None m' (seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x828cc) fc None m (seg_rom rsegs)).
Proof.
  intros CMCF RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb -> -> -> Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HMI HAC HSW
    Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS
    RBY RIMG RWIN RPHI RCTS RBCS RWSH RFPCM.
  step. (* 0x828cc mv a0,s7 *)
  step. (* 0x828d0 mv a1,s2 *)
  step. (* 0x828d4 jal 84498 <reac_box_catalogue_match> *)
  pose proof CMCF as HC. unfold CMC.reac_box_catalogue_match_contract_F, REAC_BOX_CATALOGUE_MATCH in HC.
  eapply evtF_cut.
  { eapply HC with (f := phi) (len := len) (S := S) (FS := FS) (fb := fb).
    all: cbv zeta.
    all: first [ exact HST | exact HROM | exact Hfb | exact HFB | exact HROc | exact HMI | exact HAC | exact HSW
               | exact HADW | exact HADf | exact HADT | exact HADB | exact HRB | exact HRM | exact HGC
               | exact HC254 | exact HC255 | exact HFP | exact HTLS | exact Hmod
               | exact RBY | exact RIMG | exact RWIN | exact RPHI | exact RCTS | exact RBCS | exact RWSH
               | exact RFPCM
               | reflexivity | (f_equal; lia) | lia ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & AC' & SW' & AD' & FP' & TL').
  subst ms'.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evtF_done. cbv beta. do 15 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC'|]. split; [exact SW'|]. split; [exact AD' | exact FP'].
Qed.

(* Seg/F36.v's f36_evt_call statement with the callee's contract_F in the plain contract's premise position (the
   plain contract does not give the _F one): f36_evt_call_F at RNG_all, every rng premise by rng_all from the bounds
   the plain premises already carry (the window, phi, FS through fp's fs_place), and rng_fp_cm's bound-free ranges
   outright. *)
Lemma f36_evt_call_of_F : CMC.reac_box_catalogue_match_contract_F ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s7 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi fb /\ (phi + 50 <= S - CM_K \/ S <= phi)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m phi 50 /\ app_mem (phi + 50)) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x828d8) fc None m' (seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x828cc) fc None m (seg_rom rsegs)).
Proof.
  intros CMCF ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb E7 E2 Esp Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HMI HAC HSW
    Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  apply (evtF_evt rsegs RNG_all).
  apply (f36_evt_call_F CMCF RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 F fc m phi len S FS fb E7 E2 Esp Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HMI
           HAC HSW Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS).
  - (* rng_bytes *) intros b j _ _ _; exact I.
  - (* the image *) apply rng_all; lia.
  - (* the window *) apply rng_all; unfold CM_K in *; lia.
  - (* the 50 bytes at phi and their shadow words *)
    intros H50. destruct (HFB H50) as (P1 & P2 & _).
    split; apply rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* the catalogue's shadow words *)
    apply rng_all; unfold shadow_addr, ASAN_K, CM_T; Z.div_mod_to_equations; lia.
  - (* the 6 constant bytes' shadow words *)
    apply rng_all; unfold shadow_addr, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* the window's shadow *)
    apply rng_all; unfold shadow_addr, ASAN_K, CM_K in *; Z.div_mod_to_equations; lia.
  - (* rng_fp_cm: the side stack's header, the class ranges and the thread cells, bound free at RNG_all *)
    split; [apply rng_all; unfold CM_K in *; lia|].
    split; [apply Forall_forall; intros iv _ b j _ _; exact I|].
    intros DT TS C T DB k _. apply Forall_forall. intros iv _ b j _ _. exact I.
Qed.

(* The call on the normalized memory: f36_evt_call_F run there (MemNormF.evtF_normalize_ro), with every premise and
   post fact moved across mem_rel by Seg/F36.v's own relations.  rng_fp_cm is stated at the CALLER's memory and
   moved to the normalized one by F36.f36_tls_rel (its other two conjuncts do not read memory). *)
Lemma f36_call_norm_F : CMC.reac_box_catalogue_match_contract_F ->
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s7 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi fb /\ (phi + 50 <= S - CM_K \/ S <= phi)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m phi 50 /\ app_mem (phi + 50)) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    (* the callee's footprint premises at the jal 0x828d4 *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (S - CM_K) CM_K ->
    (50 <= len -> rng RNG phi 50 /\
                  rng RNG (8 * (shadow_addr phi / 8))
                    (8 * (shadow_addr (phi + 49) / 8) + 8 - 8 * (shadow_addr phi / 8))) ->
    rng RNG (8 * (shadow_addr CM_T / 8))
      (8 * (shadow_addr (CM_T + 3255) / 8) + 8 - 8 * (shadow_addr CM_T / 8)) ->
    rng RNG (8 * (shadow_addr REAC_CTRL_PARSE_BC / 8))
      (8 * (shadow_addr (REAC_CTRL_PARSE_BC + 5) / 8) + 8 - 8 * (shadow_addr REAC_CTRL_PARSE_BC / 8)) ->
    rng RNG (shadow_addr (S - CM_K)) (shadow_addr S - shadow_addr (S - CM_K)) ->
    CMC.rng_fp_cm RNG m (bv_unsigned tp) FS ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x828d8) fc None m' (seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x828cc) fc None m (seg_rom rsegs)).
Proof.
  intros CMCF RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb E7 E2 Esp Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HRO HAC HSW
    Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS
    RBY RIMG RWIN RPHI RCTS RBCS RWSH RFPCM.
  pose proof (mem_rel_normalize rsegs m HRO) as R.
  assert (BR : forall a bs, bytes_at rsegs m a bs <-> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs; exact (bytes_at_rel rsegs m (normalize rsegs m) a bs R)).
  assert (Hlo : 0x5fe000 <= S - CM_K) by (unfold HIGHMEM_BEG in Hhi; lia).
  eapply evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HRO).
    apply (f36_evt_call_F CMCF RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             s11 t3 t4 t5 t6 F fc (normalize rsegs m) phi len S FS fb E7 E2 Esp Hphi Hlen HS Hmod HKS).
    - apply (proj1 (F36.f36_stk_rel m _ _ _ R Hlo)). exact HST.
    - exact HROM.
    - exact Hfb.
    - intros H50. destruct (HFB H50) as (P1 & P2 & P3 & P4).
      split; [exact P1|]. split; [exact P2|]. split; [apply BR; exact P3 | exact P4].
    - intros a Ha. rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ R). exact (HROc a Ha).
    - exact (mem_inv_normalize rsegs m).
    - apply (proj1 (F36.f36_cells_rel m _ R)). exact HAC.
    - apply (proj1 (F36.f36_srw_rel m _ R)). exact HSW.
    - exact Hhi.
    - exact Hsp.
    - apply (proj1 (F36.f36_addr_rel m _ _ _ R)). exact HADW.
    - intros H50. destruct (HADf H50) as (P1 & P2).
      split; [apply (proj1 (F36.f36_addr_rel m _ _ _ R)); exact P1 | exact P2].
    - apply (proj1 (F36.f36_addr_rel m _ _ _ R)). exact HADT.
    - apply (proj1 (F36.f36_addr_rel m _ _ _ R)). exact HADB.
    - apply BR. exact HRB.
    - apply BR. exact HRM.
    - apply BR. exact HGC.
    - apply BR. exact HC254.
    - apply BR. exact HC255.
    - apply (proj1 (F36.f36_fp_rel _ m _ _ _ _ _ _ _ R)). exact HFP.
    - apply (proj1 (F36.f36_cmtls_rel m _ _ _ _ _ R)). exact HTLS.
    - exact RBY.
    - exact RIMG.
    - exact RWIN.
    - exact RPHI.
    - exact RCTS.
    - exact RBCS.
    - exact RWSH.
    - (* rng_fp_cm at the normalized memory: only its thread-cell conjunct reads memory *)
      destruct RFPCM as (RH & RW & RT). split; [exact RH|]. split; [exact RW|].
      intros DT TS C T DB k Hc. apply (RT DT TS C T DB k).
      apply (proj2 (F36.f36_tls_rel m _ _ _ _ _ _ _ _ R)). exact Hc. }
  intros s (s0' & HQ & REL & SAME).
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E0 & MU & WM & MI & ST & AC' & SW' & AD' & FP').
  subst s0'.
  destruct s as [R' F' pc' sv' rv' fc' m' ro'].
  unfold ms_rel, MS in REL.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in REL, SAME.
  destruct REL as (ER & EF & Epc & Esv & Erv & Efc & Erom & RM).
  subst R' F' pc' sv' rv' fc' ro'.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' R RM SAME MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m' m0' R RM SAME WM)|].
  split; [exact (ro_agree_same rsegs m m' HRO SAME)|].
  split; [apply (proj2 (F36.f36_stk_rel m' m0' _ _ RM Hlo)); exact ST|].
  split; [apply (proj2 (F36.f36_cells_rel m' m0' RM)); exact AC'|].
  split; [apply (proj2 (F36.f36_srw_rel m' m0' RM)); exact SW'|].
  split; [apply (proj2 (F36.f36_addr_rel m' m0' _ _ RM)); exact AD'|].
  apply (proj2 (F36.f36_fp_rel _ m' m0' _ _ _ _ _ _ RM)). exact FP'.
Qed.

(* Seg/F36.v's f36_call_norm statement, with the callee's contract_F in the plain contract's premise position (as
   f36_evt_call_of_F). *)
Lemma f36_call_norm_of_F : CMC.reac_box_catalogue_match_contract_F ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi len S FS : Z) (fb : list byte),
    s7 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 len -> sp = Z_to_bv 64 S ->
    0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    CM_K <= S -> stk rsegs m (S - CM_K) S ->
    (forall a, S - CM_K <= a < S -> seg_rom rsegs (wa a) = None) ->
    length fb = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= 2 ^ 64 /\ bytes_at rsegs m phi fb /\ (phi + 50 <= S - CM_K \/ S <= phi)) ->
    (forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - CM_K -> S <= APPMEM_END -> addressable m (S - CM_K) CM_K ->
    (50 <= len -> addressable m phi 50 /\ app_mem (phi + 50)) ->
    addressable m CM_T 3256 -> addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D phi len) ->
    reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - CM_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x828d8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x828d8) fc None m' (seg_rom rsegs) /\
         munch (f36_W S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' (S - CM_K) S /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - CM_K) CM_K /\
         fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - CM_K) S (reac_box_catalogue_match_W S)
            (reac_box_catalogue_match_D phi len))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x828cc) fc None m (seg_rom rsegs)).
Proof.
  intros CMCF ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi len S FS fb E7 E2 Esp Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HRO HAC HSW
    Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS.
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  apply (evtF_evt rsegs RNG_all).
  apply (f36_call_norm_F CMCF RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 F fc m phi len S FS fb E7 E2 Esp Hphi Hlen HS Hmod HKS HST HROM Hfb HFB HROc HRO
           HAC HSW Hhi Hsp HADW HADf HADT HADB HRB HRM HGC HC254 HC255 HFP HTLS).
  - (* rng_bytes *) intros b j _ _ _; exact I.
  - (* the image *) apply rng_all; lia.
  - (* the window *) apply rng_all; unfold CM_K in *; lia.
  - (* the 50 bytes at phi and their shadow words *)
    intros H50. destruct (HFB H50) as (P1 & P2 & _).
    split; apply rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* the catalogue's shadow words *)
    apply rng_all; unfold shadow_addr, ASAN_K, CM_T; Z.div_mod_to_equations; lia.
  - (* the 6 constant bytes' shadow words *)
    apply rng_all; unfold shadow_addr, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* the window's shadow *)
    apply rng_all; unfold shadow_addr, ASAN_K, CM_K in *; Z.div_mod_to_equations; lia.
  - (* rng_fp_cm, bound free at RNG_all *)
    split; [apply rng_all; unfold CM_K in *; lia|].
    split; [apply Forall_forall; intros iv _ b j _ _; exact I|].
    intros DT TS C T DB k _. apply Forall_forall. intros iv _ b j _ _. exact I.
Qed.

(* The pins of the two call corollaries: each differs from Seg/F36.v's run only in the FIRST premise, which names the
   callee's contract_F in place of the plain contract; both first premises are checked BY NAME as well, and the rest
   of the statement by constr_eq (the R14F shape, Seg/R14F.v:323-331). *)
Lemma f36_evt_call_of_F_verbatim : True.
Proof.
  lazymatch type of F36.f36_evt_call with ?P -> ?A =>
  lazymatch type of f36_evt_call_of_F with ?Q -> ?B =>
    constr_eq P CMC.reac_box_catalogue_match_contract;
    constr_eq Q CMC.reac_box_catalogue_match_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.

Lemma f36_call_norm_of_F_verbatim : True.
Proof.
  lazymatch type of F36.f36_call_norm with ?P -> ?A =>
  lazymatch type of f36_call_norm_of_F with ?Q -> ?B =>
    constr_eq P CMC.reac_box_catalogue_match_contract;
    constr_eq Q CMC.reac_box_catalogue_match_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.

(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
