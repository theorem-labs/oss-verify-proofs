(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its numbers changed; 2046 of its 2082 lines of code are new or changed and 360 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F32.v, with its addresses and numbers changed; 394 of its 724 lines of code are new or changed and 1752 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F32.v blob 2da593b3822c at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F32.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F32.<r> (for f32_evt_m, apart from the first premise, which names reac_box_catalogue_contract_F in
   place of reac_box_catalogue_contract -- both first premises are checked by name too). Mechanical re-run,
   route (a) (lead 22:15Z); input to the ported walk only. *)
(* The footprint (ExecF.evtF) twins of the five instruction runs of segment F32 of fuzz_ctrl LLVMFuzzerTestOneInput
   (asan build of the patched image A, libreac v1.9.0): 0x827d8-0x82858 with the side blocks 0x82a20 and 0x82a74, for
   the cut-free twin SegCF/F32.v, not in this delivery (RECIPE.md (a working note, not in this delivery): a hand re-walk with StepF).

   Each f32_<run>_F is Seg/F32.v's f32_<run> with the run an evtF under a footprint RNG and one `rng RNG <addr> <len>`
   premise per region the run's own instructions read or write; the premises stay premises (the cut-free consumer
   discharges them at its own footprint).  The accesses, on the v1.9 pcs:
   - f32_evt_a_F (0x827d8 -> 0x82800): the spill reloads 0x827dc `ld a0,152(s1)`, 0x827e0 `ld a1,280(s1)` and
     0x827f0 `ld a0,160(s1)`, then 0x827f4 `lw a0,0(a0)` of the classify event at EV = fr + 528.  So
     `rng RNG (A + 152) 8`, `rng RNG (A + 280) 8`, `rng RNG (A + 160) 8` and `rng RNG EV 4`.  None is instrumented.
   - f32_evt_n_F (0x82800, k <> 9): one branch, no memory access, so no rng premise.
   - f32_chk16_F / f32_chk17_F (0x82808-0x82818 / 0x82828-0x82838): the instrumented check loads ONE shadow byte,
     (phi + 16 >> 3) + ASAN_K (resp. phi + 17); the side block compares and loads nothing.  So one rng premise each.
   - f32_evt_m_F (0x82800 -> 0x8285c, k = 9): the two checks above, the two byte loads 0x8281c `lbu a0,0(a0)` (phi + 16)
     and 0x8283c (phi + 17), the shadow store 0x82848 `sb zero,4(s3)` (S(fr) + 4), the spill reload 0x8284c
     `ld s8,40(s1)` (A + 40), the count store `sd zero,0(s8)` (fr + 32, 8 bytes), and the catalogue call 0x82858,
     whose footprint contract reac_box_catalogue_c.v reac_box_catalogue_contract_F asks for its frame
     [sp - 16, sp), the runtime cells GOT_CELL_K and CELL_K, the 8 bytes at c = fr + 32 and their one shadow byte,
     which is S(fr) + 4 again (fr is 8-aligned, f32_shadow_in).
   f32_<run>_of_F re-derives Seg/F32.v's Exec.evt statement from f32_<run>_F at RNG_all (ExecF.evtF_evt, every rng
   premise by rng_all).  Seg/F32.v's code is unchanged since release c5e779efe8c (comments edited); it keeps every code line of the source blob above and adds 350. It does not use them; they show that the footprint form loses nothing.

   rule 24: no function proved.  F32 calls reac_box_catalogue at 0x82858: f32_evt_m_F takes its footprint contract as
   the Section Hypothesis CATCF, as Seg/F32.v takes the halts contract as CATC; reac_box_catalogueF.v
   reac_box_catalogue_F_holds proves it (Qed), and SegCF/F32.v passes that theorem, so the twin assumes no callee.

   Seg/F32.v's pure helpers (f32_zxb8, f32_shadow_in, f32_mrd_munch, f32_shadow_rng, the bad-arm tactic f32_bad, ...)
   are used from Seg/F32.v itself (imported); only the two branch tactics f32_nt / f32_tk are restated, with
   Seg/F32.v's text, because they name if_cases, which must be StepF's here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcClassify RcClassifyLib
  RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 F32.
(* Last (as in Seg/F38F.v and Seg/F31F.v): StepF's step / if_cases and ExecF's evtF_done match evtF goals and shadow
   Step's evt ones. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Seg/F32.v's cuts and runs are stated with the image-A YK11 (its alias AYK); import it again here. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
(* ExecF/StepF re-open bv_scope on Import; our Z arithmetic needs Z_scope on top (as in Seg/F31F.v). *)
Open Scope Z_scope.

(* ===================== the branch tactics (Seg/F32.v's text, over StepF's if_cases) ===================== *)

Ltac f32_nt := let H := fresh "HC" in first [ if_cases H; [f32_bad H | clear H] | idtac ].
Ltac f32_tk := let H := fresh "HC" in first [ if_cases H; [clear H | f32_bad H] | idtac ].

(* ===================== the footprint runs ===================== *)

(* 0x827d8 -> 0x82800: the three branches to 0x82bf4 are not taken.  Accesses: the spill reloads [A + 152],
   [A + 280], [A + 160] and the 4-byte classify event at EV. *)
Lemma f32_evt_a_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (A EV tf so ev : Z),
    x9 = Z_to_bv 64 A -> 0 <= A -> A + 288 <= 2 ^ 64 ->
    bv_eqb x10 (Z_to_bv 64 0) = false ->
    ov_read_bytes rsegs m (wa (A + 152)) 8 = Some (le8 (Z_to_bv 64 tf)) -> (tf = 0 \/ tf = 1) ->
    ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 so)) -> (so = 0 \/ so = 1) ->
    ~ (tf = 0 /\ so = 0) ->
    ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 EV)) -> 0 <= EV -> EV + 4 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa EV) 4 = Some (le4 (Z_to_bv 64 ev)) -> 0 <= ev <= 5 ->
    (* the three spill reloads and the event load *)
    rng RNG (A + 152) 8 -> rng RNG (A + 280) 8 -> rng RNG (A + 160) 8 -> rng RNG EV 4 ->
    evtF rsegs RNG
      (fun ms' => exists y10 y11,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                       x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x827d8) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m A EV tf so ev E9 HA0 HA1 Hne R152 Htf R280 Hso Hnz R160 HE0 HE1 Rev Hev
    RG152 RG280 RG160 RGev.
  subst x9.
  assert (Hev' : ev = 0 \/ ev = 1 \/ ev = 2 \/ ev = 3 \/ ev = 4 \/ ev = 5) by lia.
  destruct Htf as [->| ->]; destruct Hso as [->| ->];
    try (exfalso; apply Hnz; split; reflexivity);
    destruct Hev' as [->|[->|[->|[->|[->| ->]]]]];
    (step; f32_nt; step; step; step; step; step; f32_nt; step; step; step; step; f32_nt;
     apply evtF_done; eexists; eexists; reflexivity).
Qed.

(* Seg/F32.v's f32_evt_a statement, at RNG_all. *)
Lemma f32_evt_a_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (A EV tf so ev : Z),
    x9 = Z_to_bv 64 A -> 0 <= A -> A + 288 <= 2 ^ 64 ->
    bv_eqb x10 (Z_to_bv 64 0) = false ->
    ov_read_bytes rsegs m (wa (A + 152)) 8 = Some (le8 (Z_to_bv 64 tf)) -> (tf = 0 \/ tf = 1) ->
    ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 so)) -> (so = 0 \/ so = 1) ->
    ~ (tf = 0 /\ so = 0) ->
    ov_read_bytes rsegs m (wa (A + 160)) 8 = Some (le8 (Z_to_bv 64 EV)) -> 0 <= EV -> EV + 4 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa EV) 4 = Some (le4 (Z_to_bv 64 ev)) -> 0 <= ev <= 5 ->
    LE.evt rsegs
      (fun ms' => exists y10 y11,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                       x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x827d8) fcs None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f32_evt_a_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fcs m A EV tf so ev); try eassumption; apply rng_all; lia.
Qed.

(* The pin: f32_evt_a_of_F's statement is F32.f32_evt_a's, term for term. *)
Lemma f32_evt_a_of_F_verbatim : True.
Proof.
  let a := type of F32.f32_evt_a in let b := type of f32_evt_a_of_F in constr_eq a b.
  exact I.
Qed.

(* 0x82800 with k <> 9: the branch to 0x828c8 is taken.  No memory access. *)
Lemma f32_evt_n_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (k : Z),
    x24 = Z_to_bv 64 k -> 0 <= k <= 13 -> k <> 9 ->
    evtF rsegs RNG
      (fun ms' => exists y10,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                       x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m k E24 Hk Hk9. subst x24.
  assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/
                k = 10 \/ k = 11 \/ k = 12 \/ k = 13) by lia.
  destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
    (step; step; f32_tk; apply evtF_done; eexists; reflexivity).
Qed.

(* Seg/F32.v's f32_evt_n statement, at RNG_all. *)
Lemma f32_evt_n_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (k : Z),
    x24 = Z_to_bv 64 k -> 0 <= k <= 13 -> k <> 9 ->
    LE.evt rsegs
      (fun ms' => exists y10,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                       x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs)).
Proof.
  intros. eapply (evtF_evt rsegs RNG_all).
  eapply (f32_evt_n_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Fr fcs m k); eassumption.
Qed.

(* The pin: f32_evt_n_of_F's statement is F32.f32_evt_n's, term for term. *)
Lemma f32_evt_n_of_F_verbatim : True.
Proof.
  let a := type of F32.f32_evt_n in let b := type of f32_evt_n_of_F in constr_eq a b.
  exact I.
Qed.

(* 0x82808 -> 0x8281c: the instrumented check of the byte at phi + 16 (side block 0x82a20, error path 0x82cf4).
   Access: the one shadow byte (phi + 16 >> 3) + ASAN_K. *)
Lemma f32_chk16_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (phi : Z) (b : byte),
    x23 = Z_to_bv 64 phi -> x26 = Z_to_bv 64 ASAN_K -> 0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 16) 3 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ (phi + 16) mod 8 < bv_signed b <= 7) ->
    (* the shadow load 0x82814 *)
    rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) 1 ->
    evtF rsegs RNG
      (fun ms' => exists y11 y12,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (phi + 16)) y11 y12 x13 x14 x15 x16 x17 x18 x19
                       x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 0x8281c) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82808) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m phi b E23 E26 Hp0 Hp1 R16 Hok RG16. subst x23 x26.
  assert (HS : 0 <= Z.shiftr (phi + 16) 3 < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  pose proof (sbyte_range b) as Hsb.
  destruct Hok as [H0 | Hlt].
  - rewrite (byte_s0 b H0) in R16.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit phi) by lia.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (phi + 16)) by lia.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (Z.shiftr (phi + 16) 3))
      by lia.
    rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit ASAN_K) by (unfold ASAN_K;
      lia).
    step. step. f32_nt.
    apply evtF_done. eexists; eexists; reflexivity.
  - step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit phi) by lia.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (phi + 16)) by lia.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (Z.shiftr (phi + 16) 3))
      by lia.
    rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit ASAN_K) by (unfold ASAN_K;
      lia).
    step. step. f32_tk.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (phi + 16)) by lia.
      rewrite ?(land7 (phi + 16)) by lia.
    step. f32_nt. step.
    apply evtF_done. eexists; eexists; reflexivity.
Qed.

(* The shadow byte of phi + o is inside [0, 2^64) (the rng_all side of the _of_F corollaries). *)
Lemma f32_shr_bound : forall phi o, 0 <= phi -> phi + 50 <= 2 ^ 64 -> 0 <= o < 50 ->
  0 <= Z.shiftr (phi + o) 3 + ASAN_K /\ Z.shiftr (phi + o) 3 + ASAN_K + 1 <= 2 ^ 64.
Proof.
  intros phi o H0 H1 Ho. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASAN_K.
  Z.div_mod_to_equations. lia.
Qed.

(* Seg/F32.v's f32_chk16 statement, at RNG_all. *)
Lemma f32_chk16_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (phi : Z) (b : byte),
    x23 = Z_to_bv 64 phi -> x26 = Z_to_bv 64 ASAN_K -> 0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 16) 3 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ (phi + 16) mod 8 < bv_signed b <= 7) ->
    LE.evt rsegs
      (fun ms' => exists y11 y12,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (phi + 16)) y11 y12 x13 x14 x15 x16 x17 x18 x19
                       x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 0x8281c) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82808) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m phi b E23 E26 Hp0 Hp1 R16 Hok.
  eapply (evtF_evt rsegs RNG_all).
  pose proof (f32_shr_bound phi 16 Hp0 Hp1 ltac:(lia)) as (Hb0 & Hb1).
  exact (f32_chk16_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           Fr fcs m phi b E23 E26 Hp0 Hp1 R16 Hok (rng_all _ _ Hb0 Hb1)).
Qed.

(* 0x82828 -> 0x8283c: the same check for the byte at phi + 17 (side block 0x82a74, error path 0x82d14). *)
Lemma f32_chk17_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (phi : Z) (b : byte),
    x23 = Z_to_bv 64 phi -> x26 = Z_to_bv 64 ASAN_K -> 0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 17) 3 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ (phi + 17) mod 8 < bv_signed b <= 7) ->
    (* the shadow load 0x82834 *)
    rng RNG (Z.shiftr (phi + 17) 3 + ASAN_K) 1 ->
    evtF rsegs RNG
      (fun ms' => exists y11 y12,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (phi + 17)) y11 y12 x13 x14 x15 x16 x17 x18 x19
                       x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 0x8283c) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82828) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m phi b E23 E26 Hp0 Hp1 R17 Hok RG17. subst x23 x26.
  assert (HS : 0 <= Z.shiftr (phi + 17) 3 < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  pose proof (sbyte_range b) as Hsb.
  destruct Hok as [H0 | Hlt].
  - rewrite (byte_s0 b H0) in R17.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit phi) by lia.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (phi + 17)) by lia.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (Z.shiftr (phi + 17) 3))
      by lia.
    rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit ASAN_K) by (unfold ASAN_K;
      lia).
    step. step. f32_nt.
    apply evtF_done. eexists; eexists; reflexivity.
  - step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit phi) by lia.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (phi + 17)) by lia.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (Z.shiftr (phi + 17) 3))
      by lia.
    rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit ASAN_K) by (unfold ASAN_K;
      lia).
    step. step. f32_tk.
    step. rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (phi + 17)) by lia.
      rewrite ?(land7 (phi + 17)) by lia.
    step. f32_nt. step.
    apply evtF_done. eexists; eexists; reflexivity.
Qed.

(* Seg/F32.v's f32_chk17 statement, at RNG_all. *)
Lemma f32_chk17_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (phi : Z) (b : byte),
    x23 = Z_to_bv 64 phi -> x26 = Z_to_bv 64 ASAN_K -> 0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 17) 3 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ (phi + 17) mod 8 < bv_signed b <= 7) ->
    LE.evt rsegs
      (fun ms' => exists y11 y12,
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (phi + 17)) y11 y12 x13 x14 x15 x16 x17 x18 x19
                       x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 0x8283c) fcs None m (seg_rom rsegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82828) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m phi b E23 E26 Hp0 Hp1 R17 Hok.
  eapply (evtF_evt rsegs RNG_all).
  pose proof (f32_shr_bound phi 17 Hp0 Hp1 ltac:(lia)) as (Hb0 & Hb1).
  exact (f32_chk17_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           Fr fcs m phi b E23 E26 Hp0 Hp1 R17 Hok (rng_all _ _ Hb0 Hb1)).
Qed.

(* ===================== the catalogue path, over the callee's footprint contract ===================== *)

Section F32F.
(* reac_box_catalogue's footprint contract (reac_box_catalogue_c.v), proved by reac_box_catalogueF.v
   reac_box_catalogue_F_holds; the twin passes that theorem. *)
Hypothesis CATCF : CATc.reac_box_catalogue_contract_F.

(* 0x82800 with k = 9: the two byte tests, then either 0x828c8 or the catalogue call and 0x8285c.  Accesses: the two
   checks' shadow bytes, the two block bytes phi + 16 / phi + 17, the shadow store S(fr) + 4, the spill reload
   [A + 40], the count store [fr + 32, fr + 40), and the catalogue's own: its frame [sp - 16, sp), GOT_CELL_K, CELL_K,
   the 8 bytes at fr + 32 and their shadow byte S(fr) + 4. *)
Lemma f32_evt_m_F :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (Asp fr phi spv lo v16 v17 : Z) (b16 b17 b4 : byte) (junk : list byte),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 Asp -> x19 = Z_to_bv 64 (Sfr fr) ->
    x23 = Z_to_bv 64 phi -> x24 = Z_to_bv 64 9 -> x26 = Z_to_bv 64 ASAN_K ->
    0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 16) 3 + ASAN_K)) 1 = Some [b16] ->
    (bv_signed b16 = 0 \/ (phi + 16) mod 8 < bv_signed b16 <= 7) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 17) 3 + ASAN_K)) 1 = Some [b17] ->
    (bv_signed b17 = 0 \/ (phi + 17) mod 8 < bv_signed b17 <= 7) ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [Z_to_bv 8 v16] -> 0 <= v16 < 256 ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [Z_to_bv 8 v17] -> 0 <= v17 < 256 ->
    ro_cells rsegs m (Asp + 40) [C8 (Z_to_bv 64 (fr + 32))] ->
    rw_cells rsegs m (Sfr fr + 4) [C1 b4] -> rw_cells rsegs m (fr + 32) [CB 8 junk] ->
    0 <= fr -> fr mod 8 = 0 -> 6283264 <= fr -> fr + 3136 <= Asp -> Asp + 48 <= 2 ^ 64 ->
    ASAN_K <= Sfr fr -> Sfr fr + 5 <= lo -> 6283264 <= lo -> HIGHMEM_BEG <= lo ->
    lo + 16 <= spv -> spv <= Asp -> spv < 2 ^ 64 ->
    (fr + 3136 <= lo \/ spv <= fr) ->
    (Sfr fr + 5 <= fr + 32 \/ fr + 40 <= Sfr fr + 4) ->
    stk rsegs m lo spv ->
    (forall a, fr + 32 <= a < fr + 40 -> app_mem a) ->
    asan_cells m -> shadow_rw m ->
    (* the segment's own accesses *)
    rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) 1 -> rng RNG (phi + 16) 1 ->
    rng RNG (Z.shiftr (phi + 17) 3 + ASAN_K) 1 -> rng RNG (phi + 17) 1 ->
    rng RNG (Sfr fr + 4) 1 -> rng RNG (Asp + 40) 8 -> rng RNG (fr + 32) 8 ->
    (* the catalogue's: its frame and the two runtime cells (fr + 32 and its shadow byte are above) *)
    rng RNG (spv - 16) 16 -> rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    evtF rsegs RNG
      (fun ms' =>
         (exists y10 y11 y12,
            ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                          x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fcs None m (seg_rom rsegs)
            /\ (v16 <> 205 \/ v17 <> 234))
         \/ (exists y11 y12 m',
            ms' = MS (mkR (Z_to_bv 64 0x8285c) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 CATc.BOX_CATALOGUE) y11 y12
                          x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (fr + 32)) x25 x26 x27 x28
                          x29 x30 x31) Fr (Z_to_bv 64 0x8285c) fcs None m' (seg_rom rsegs)
            /\ v16 = 205 /\ v17 = 234
            /\ munch [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] m m'
            /\ wmono rsegs m m' /\ stk rsegs m' lo spv
            /\ bytes_at rsegs m' (fr + 32) (le8 (Z_to_bv 64 11))
            /\ mrd rsegs m' (wa (Sfr fr + 4)) = Some (Z_to_bv 8 0)))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m Asp fr phi spv lo v16 v17 b16 b17 b4 junk
    E2 E9 E19 E23 E24 E26 Hp0 Hp1 R16s Hok16 R17s Hok17 R16b Hv16 R17b Hv17
    RA40 RW4 RWfr Hfr0 Hfr8 HGT HfrA HAb HSfr0 HSlo HloG HloH Hlosp HspA HspB Hdw Hd4 HST Happ HAC HSW
    RG16s RG16 RG17s RG17 RGsh RG40 RG32 RGsp RGgot RGcell.
  subst x2 x9 x19 x23 x24 x26.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  (* the catalogue's shadow premise names the shadow span of [fr + 32, fr + 40): one byte, S(fr) + 4 *)
  assert (Esh0 : shadow_addr (fr + 32) = Sfr fr + 4).
  { pose proof (f32_shadow_in fr 0 Hfr8 ltac:(lia)) as HH. rewrite Z.add_0_r in HH. exact HH. }
  assert (Esh7 : shadow_addr (fr + 32 + 7) = Sfr fr + 4) by exact (f32_shadow_in fr 7 Hfr8 ltac:(lia)).
  step. step. f32_nt.
  eapply evtF_cut;
    [ eapply (f32_chk16_F RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi b16);
      [reflexivity | reflexivity | lia | lia | exact R16s | exact Hok16 | exact RG16s]
    | intros ms1 (y11 & y12 & ->) ].
  step. rewrite ?(f32_zxb8 v16) by lia.
  step. step.
  destruct (Z.eq_dec v16 205) as [Ev16 | Nv16].
  2: { f32_tk. apply evtF_done. left. do 3 eexists. split; [reflexivity|]. left. exact Nv16. }
  subst v16. f32_nt.
  eapply evtF_cut;
    [ eapply (f32_chk17_F RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi b17);
      [reflexivity | reflexivity | lia | lia | exact R17s | exact Hok17 | exact RG17s]
    | intros ms2 (y11' & y12' & ->) ].
  step. rewrite ?(f32_zxb8 v17) by lia.
  step. step.
  destruct (Z.eq_dec v17 234) as [Ev17 | Nv17].
  2: { f32_tk. apply evtF_done. left. do 3 eexists. split; [reflexivity|]. right. exact Nv17. }
  subst v17. f32_nt.
  (* the two stores and the catalogue call *)
  pose proof (munch_refl [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct Hd4 as [Hd4 | Hd4];
  (rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (Sfr fr)) by lia;
   step;
   try (change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]); try mem_after_store;
   rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit Asp) by lia;
   step;
   rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (fr + 32)) by lia;
   step; step; step;
   eapply evtF_cut;
   [ eapply CATCF with (c := fr + 32) (lo := lo);
     [ reflexivity
     | rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia; exact HST
     | rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; lia
     | eapply (asan_cells_kept _ m); [exact HAC | exact MU |
         unfold RT_LO, RT_HI; cbn [disjoint_from]; repeat split; try exact I; left; lia]
     | intros x Hx; pose proof (f32_shadow_rng x Hx) as Hxr;
       destruct (Z.eq_dec x (Sfr fr + 4)) as [Ex | Nx];
       [ subst x; split;
         [ apply WM; exact (proj1 (HSW _ Hx))
         | destruct RW4 as ((_ & Hb4') & _); cbn [cells_bytes cbytes] in Hb4';
           rewrite app_nil_r in Hb4'; destruct Hb4' as (_ & _ & Hb4'');
           pose proof (Hb4'' 0%nat ltac:(cbn [length]; lia)) as Hm4; cbn [Z.of_nat nth_error] in Hm4;
           rewrite Z.add_0_r in Hm4; exists (Z_to_bv 8 0); exact Hm4 ]
       | destruct (HSW x Hx) as (Hw & bx & Hbx); split; [apply WM; exact Hw|];
         exists bx; rewrite (f32_mrd_munch _ m _ x MU ltac:(unfold LOWMEM_END, HIGHMEM_BEG in Hxr; lia));
         [ exact Hbx
         | cbn [outside]; split; [lia|]; split; [lia|]; split; [|exact I];
           intros [Hc1 Hc2]; exact (app_not_shadow x (Happ x ltac:(lia)) Hx) ] ]
     | intros x Hx; rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; cbn [outside];
       destruct Hx as [Hx | [Hx | Hx]];
       [ unfold GOT_CELL_K in Hx; repeat split; try exact I; lia
       | unfold CELL_K in Hx; repeat split; try exact I; lia
       | pose proof (f32_shadow_rng x Hx) as Hxr;
         split; [lia|]; split; [|exact I];
         intros [Hc1 Hc2]; exact (app_not_shadow x (Happ x ltac:(lia)) Hx) ]
     | right; split; [Z.div_mod_to_equations; lia|];
       split; [exact (proj2 RWfr)|];
       split;
       [ rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
         unfold CATc.REAC_BOX_CATALOGUE_FRAME;
         destruct Hdw as [Hq|Hq]; [left; lia | right; lia]
       | pose proof (Happ (fr + 39) ltac:(lia)) as Hae;
         unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hae;
         split; [lia|]; split; [lia|]; split; [unfold APPMEM_END; lia|];
         intros i Hi; split; [apply Happ; lia|];
         exists (Z_to_bv 8 0); split;
         [ rewrite (f32_shadow_in fr i Hfr8 ltac:(lia));
           destruct RW4 as ((_ & Hb4') & _); cbn [cells_bytes cbytes] in Hb4';
           rewrite app_nil_r in Hb4'; destruct Hb4' as (_ & _ & Hb4'');
           pose proof (Hb4'' 0%nat ltac:(cbn [length]; lia)) as Hm4; cbn [Z.of_nat nth_error] in Hm4;
           rewrite Z.add_0_r in Hm4; exact Hm4
         | left; vm_compute; reflexivity ] ]
     (* the catalogue's footprint: its frame, the two runtime cells, the 8 bytes at fr + 32 and their shadow byte *)
     | rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; exact RGsp
     | exact RGgot
     | exact RGcell
     | intros _; split;
       [ exact RG32
       | rewrite Esh0, Esh7; replace (Sfr fr + 4 - (Sfr fr + 4) + 1) with 1 by lia; exact RGsh ] ]
   | intros ms3 Hpost; unfold CATc.reac_box_catalogue_post in Hpost;
     destruct Hpost as (a1' & a2' & m' & Ems & MUc & WMc & MIc & STc & BAc);
     subst ms3;
     replace (ret_pc (Z_to_bv 64 0x8285c)) with (Z_to_bv 64 0x8285c)
       by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]);
     replace (fr + 32 =? 0) with false in BAc by (symmetry; apply Z.eqb_neq; lia);
     apply evtF_done; right; exists a1', a2', m'; split; [reflexivity|];
     split; [reflexivity|]; split; [reflexivity|];
     split;
     [ eapply munch_trans; [exact MU|];
       eapply munch_weaken; [| exact MUc];
       unfold sub_fp; intros z Hz; cbn [outside] in *;
       rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) in Hz by lia;
       rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; repeat split; try exact I; lia
     | split; [eapply wmono_trans; [exact WM | exact WMc]|];
       split; [rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) in STc by lia;
         exact STc|];
       split; [exact BAc|];
       destruct RW4 as ((_ & Hb4') & _); cbn [cells_bytes cbytes] in Hb4';
       rewrite app_nil_r in Hb4'; destruct Hb4' as (_ & _ & Hb4'');
       pose proof (Hb4'' 0%nat ltac:(cbn [length]; lia)) as Hm4; cbn [Z.of_nat nth_error] in Hm4;
       rewrite Z.add_0_r in Hm4;
       rewrite (f32_mrd_munch _ _ m' (Sfr fr + 4) MUc ltac:(lia));
       [ exact Hm4
       | rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
         cbn [outside];
         unfold CATc.REAC_BOX_CATALOGUE_FRAME; split; [lia|]; split; [lia|exact I] ] ] ]).
Qed.

(* Seg/F32.v's f32_evt_m statement, at RNG_all, under the footprint contract (with reac_box_catalogueF.v
   reac_box_catalogue_F_holds it holds outright). *)
Lemma f32_evt_m_of_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (Asp fr phi spv lo v16 v17 : Z) (b16 b17 b4 : byte) (junk : list byte),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 Asp -> x19 = Z_to_bv 64 (Sfr fr) ->
    x23 = Z_to_bv 64 phi -> x24 = Z_to_bv 64 9 -> x26 = Z_to_bv 64 ASAN_K ->
    0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 16) 3 + ASAN_K)) 1 = Some [b16] ->
    (bv_signed b16 = 0 \/ (phi + 16) mod 8 < bv_signed b16 <= 7) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 17) 3 + ASAN_K)) 1 = Some [b17] ->
    (bv_signed b17 = 0 \/ (phi + 17) mod 8 < bv_signed b17 <= 7) ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [Z_to_bv 8 v16] -> 0 <= v16 < 256 ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [Z_to_bv 8 v17] -> 0 <= v17 < 256 ->
    ro_cells rsegs m (Asp + 40) [C8 (Z_to_bv 64 (fr + 32))] ->
    rw_cells rsegs m (Sfr fr + 4) [C1 b4] -> rw_cells rsegs m (fr + 32) [CB 8 junk] ->
    0 <= fr -> fr mod 8 = 0 -> 6283264 <= fr -> fr + 3136 <= Asp -> Asp + 48 <= 2 ^ 64 ->
    ASAN_K <= Sfr fr -> Sfr fr + 5 <= lo -> 6283264 <= lo -> HIGHMEM_BEG <= lo ->
    lo + 16 <= spv -> spv <= Asp -> spv < 2 ^ 64 ->
    (fr + 3136 <= lo \/ spv <= fr) ->
    (Sfr fr + 5 <= fr + 32 \/ fr + 40 <= Sfr fr + 4) ->
    stk rsegs m lo spv ->
    (forall a, fr + 32 <= a < fr + 40 -> app_mem a) ->
    asan_cells m -> shadow_rw m ->
    LE.evt rsegs
      (fun ms' =>
         (exists y10 y11 y12,
            ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                          x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fcs None m (seg_rom rsegs)
            /\ (v16 <> 205 \/ v17 <> 234))
         \/ (exists y11 y12 m',
            ms' = MS (mkR (Z_to_bv 64 0x8285c) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 CATc.BOX_CATALOGUE) y11 y12
                          x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (fr + 32)) x25 x26 x27 x28
                          x29 x30 x31) Fr (Z_to_bv 64 0x8285c) fcs None m' (seg_rom rsegs)
            /\ v16 = 205 /\ v17 = 234
            /\ munch [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] m m'
            /\ wmono rsegs m m' /\ stk rsegs m' lo spv
            /\ bytes_at rsegs m' (fr + 32) (le8 (Z_to_bv 64 11))
            /\ mrd rsegs m' (wa (Sfr fr + 4)) = Some (Z_to_bv 8 0)))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m Asp fr phi spv lo v16 v17 b16 b17 b4 junk
    E2 E9 E19 E23 E24 E26 Hp0 Hp1 R16s Hok16 R17s Hok17 R16b Hv16 R17b Hv17
    RA40 RW4 RWfr Hfr0 Hfr8 HGT HfrA HAb HSfr0 HSlo HloG HloH Hlosp HspA HspB Hdw Hd4 HST Happ HAC HSW.
  eapply (evtF_evt rsegs RNG_all).
  pose proof (f32_shr_bound phi 16 Hp0 Hp1 ltac:(lia)) as (Hb16a & Hb16b).
  pose proof (f32_shr_bound phi 17 Hp0 Hp1 ltac:(lia)) as (Hb17a & Hb17b).
  assert (HK0 : 0 <= ASAN_K) by (unfold ASAN_K; lia).
  apply (f32_evt_m_F RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           Fr fcs m Asp fr phi spv lo v16 v17 b16 b17 b4 junk
           E2 E9 E19 E23 E24 E26 Hp0 Hp1 R16s Hok16 R17s Hok17 R16b Hv16 R17b Hv17
           RA40 RW4 RWfr Hfr0 Hfr8 HGT HfrA HAb HSfr0 HSlo HloG HloH Hlosp HspA HspB Hdw Hd4 HST Happ HAC HSW);
    apply rng_all; unfold GOT_CELL_K, CELL_K; lia.
Qed.

End F32F.

(* The pin: f32_evt_m_of_F states F32.f32_evt_m's v1.9 text, term for term, apart from the first premise, which
   names the _F contract in place of the plain one; both first premises are checked by name too. *)
Lemma f32_evt_m_of_F_verbatim : True.
Proof.
  lazymatch type of F32.f32_evt_m with ?P -> ?A =>
  lazymatch type of f32_evt_m_of_F with ?Q -> ?B =>
    constr_eq P OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.reac_box_catalogue_contract;
    constr_eq Q OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.reac_box_catalogue_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.

(* The pins of the two instrumented checks. *)
Lemma f32_chk16_of_F_verbatim : True.
Proof.
  let a := type of F32.f32_chk16 in let b := type of f32_chk16_of_F in constr_eq a b.
  exact I.
Qed.

Lemma f32_chk17_of_F_verbatim : True.
Proof.
  let a := type of F32.f32_chk17 in let b := type of f32_chk17_of_F in constr_eq a b.
  exact I.
Qed.

(* ===================== route (C): the narrowed twins (reac_box_catalogue_contract_F_on) ===================== *)

(* Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery) and its 10:34Z amendment).  f32_evt_m_F used its
   premise `shadow_rw m` only to give the catalogue its own `shadow_rw` premise on the post-store memory (the CATCF
   bullet of its proof).  The catalogue's narrowed footprint contract (reac_box_catalogue_c.v
   reac_box_catalogue_contract_F_on, d68c95046c8) DROPS that premise (no region: the catalogue reads its one
   shadow byte through addressable and stores none).  The run itself reads its two shadow bytes (phi + 16, phi + 17)
   through its ov_read_bytes premises, stores S(fr) + 4 through rw_cells (Sfr fr + 4), and keeps asan_cells by
   asan_cells_kept.  So the twins' proofs never use the premise: it is DROPPED (no R), and no post names shadow_rw.
   The Section F32F above stays as it is (Hypothesis CATCF). *)
Section F32F_on.
(* reac_box_catalogue's narrowed footprint contract (reac_box_catalogue_c.v), proved by a Theorem Labs lane's
   reac_box_catalogueF.v reac_box_catalogue_F_holds_on (a working branch 330e60af39d). *)
Hypothesis CATCF_on : CATc.reac_box_catalogue_contract_F_on.

(* Route (C): f32_evt_m_F with `shadow_rw m ->` dropped, under the catalogue's _F_on contract; the proof is
   f32_evt_m_F's without its shadow_rw bullet.  No AsanRTInv.RT and no shadow_rw premise. *)
Lemma f32_evt_m_F_on :
  forall (RNG : footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (Asp fr phi spv lo v16 v17 : Z) (b16 b17 b4 : byte) (junk : list byte),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 Asp -> x19 = Z_to_bv 64 (Sfr fr) ->
    x23 = Z_to_bv 64 phi -> x24 = Z_to_bv 64 9 -> x26 = Z_to_bv 64 ASAN_K ->
    0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 16) 3 + ASAN_K)) 1 = Some [b16] ->
    (bv_signed b16 = 0 \/ (phi + 16) mod 8 < bv_signed b16 <= 7) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 17) 3 + ASAN_K)) 1 = Some [b17] ->
    (bv_signed b17 = 0 \/ (phi + 17) mod 8 < bv_signed b17 <= 7) ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [Z_to_bv 8 v16] -> 0 <= v16 < 256 ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [Z_to_bv 8 v17] -> 0 <= v17 < 256 ->
    ro_cells rsegs m (Asp + 40) [C8 (Z_to_bv 64 (fr + 32))] ->
    rw_cells rsegs m (Sfr fr + 4) [C1 b4] -> rw_cells rsegs m (fr + 32) [CB 8 junk] ->
    0 <= fr -> fr mod 8 = 0 -> 6283264 <= fr -> fr + 3136 <= Asp -> Asp + 48 <= 2 ^ 64 ->
    ASAN_K <= Sfr fr -> Sfr fr + 5 <= lo -> 6283264 <= lo -> HIGHMEM_BEG <= lo ->
    lo + 16 <= spv -> spv <= Asp -> spv < 2 ^ 64 ->
    (fr + 3136 <= lo \/ spv <= fr) ->
    (Sfr fr + 5 <= fr + 32 \/ fr + 40 <= Sfr fr + 4) ->
    stk rsegs m lo spv ->
    (forall a, fr + 32 <= a < fr + 40 -> app_mem a) ->
    asan_cells m ->
    (* the segment's own accesses *)
    rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) 1 -> rng RNG (phi + 16) 1 ->
    rng RNG (Z.shiftr (phi + 17) 3 + ASAN_K) 1 -> rng RNG (phi + 17) 1 ->
    rng RNG (Sfr fr + 4) 1 -> rng RNG (Asp + 40) 8 -> rng RNG (fr + 32) 8 ->
    (* the catalogue's: its frame and the two runtime cells (fr + 32 and its shadow byte are above) *)
    rng RNG (spv - 16) 16 -> rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    evtF rsegs RNG
      (fun ms' =>
         (exists y10 y11 y12,
            ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                          x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fcs None m (seg_rom rsegs)
            /\ (v16 <> 205 \/ v17 <> 234))
         \/ (exists y11 y12 m',
            ms' = MS (mkR (Z_to_bv 64 0x8285c) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 CATc.BOX_CATALOGUE) y11 y12
                          x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (fr + 32)) x25 x26 x27 x28
                          x29 x30 x31) Fr (Z_to_bv 64 0x8285c) fcs None m' (seg_rom rsegs)
            /\ v16 = 205 /\ v17 = 234
            /\ munch [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] m m'
            /\ wmono rsegs m m' /\ stk rsegs m' lo spv
            /\ bytes_at rsegs m' (fr + 32) (le8 (Z_to_bv 64 11))
            /\ mrd rsegs m' (wa (Sfr fr + 4)) = Some (Z_to_bv 8 0)))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m Asp fr phi spv lo v16 v17 b16 b17 b4 junk
    E2 E9 E19 E23 E24 E26 Hp0 Hp1 R16s Hok16 R17s Hok17 R16b Hv16 R17b Hv17
    RA40 RW4 RWfr Hfr0 Hfr8 HGT HfrA HAb HSfr0 HSlo HloG HloH Hlosp HspA HspB Hdw Hd4 HST Happ HAC
    RG16s RG16 RG17s RG17 RGsh RG40 RG32 RGsp RGgot RGcell.
  subst x2 x9 x19 x23 x24 x26.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  (* the catalogue's shadow premise names the shadow span of [fr + 32, fr + 40): one byte, S(fr) + 4 *)
  assert (Esh0 : shadow_addr (fr + 32) = Sfr fr + 4).
  { pose proof (f32_shadow_in fr 0 Hfr8 ltac:(lia)) as HH. rewrite Z.add_0_r in HH. exact HH. }
  assert (Esh7 : shadow_addr (fr + 32 + 7) = Sfr fr + 4) by exact (f32_shadow_in fr 7 Hfr8 ltac:(lia)).
  step. step. f32_nt.
  eapply evtF_cut;
    [ eapply (f32_chk16_F RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi b16);
      [reflexivity | reflexivity | lia | lia | exact R16s | exact Hok16 | exact RG16s]
    | intros ms1 (y11 & y12 & ->) ].
  step. rewrite ?(f32_zxb8 v16) by lia.
  step. step.
  destruct (Z.eq_dec v16 205) as [Ev16 | Nv16].
  2: { f32_tk. apply evtF_done. left. do 3 eexists. split; [reflexivity|]. left. exact Nv16. }
  subst v16. f32_nt.
  eapply evtF_cut;
    [ eapply (f32_chk17_F RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi b17);
      [reflexivity | reflexivity | lia | lia | exact R17s | exact Hok17 | exact RG17s]
    | intros ms2 (y11' & y12' & ->) ].
  step. rewrite ?(f32_zxb8 v17) by lia.
  step. step.
  destruct (Z.eq_dec v17 234) as [Ev17 | Nv17].
  2: { f32_tk. apply evtF_done. left. do 3 eexists. split; [reflexivity|]. right. exact Nv17. }
  subst v17. f32_nt.
  (* the two stores and the catalogue call *)
  pose proof (munch_refl [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct Hd4 as [Hd4 | Hd4];
  (rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (Sfr fr)) by lia;
   step;
   try (change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]); try mem_after_store;
   rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit Asp) by lia;
   step;
   rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (fr + 32)) by lia;
   step; step; step;
   eapply evtF_cut;
   [ eapply CATCF_on with (c := fr + 32) (lo := lo);
     [ reflexivity
     | rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia; exact HST
     | rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; lia
     | eapply (asan_cells_kept _ m); [exact HAC | exact MU |
         unfold RT_LO, RT_HI; cbn [disjoint_from]; repeat split; try exact I; left; lia]
     | intros x Hx; rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; cbn [outside];
       destruct Hx as [Hx | [Hx | Hx]];
       [ unfold GOT_CELL_K in Hx; repeat split; try exact I; lia
       | unfold CELL_K in Hx; repeat split; try exact I; lia
       | pose proof (f32_shadow_rng x Hx) as Hxr;
         split; [lia|]; split; [|exact I];
         intros [Hc1 Hc2]; exact (app_not_shadow x (Happ x ltac:(lia)) Hx) ]
     | right; split; [Z.div_mod_to_equations; lia|];
       split; [exact (proj2 RWfr)|];
       split;
       [ rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
         unfold CATc.REAC_BOX_CATALOGUE_FRAME;
         destruct Hdw as [Hq|Hq]; [left; lia | right; lia]
       | pose proof (Happ (fr + 39) ltac:(lia)) as Hae;
         unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hae;
         split; [lia|]; split; [lia|]; split; [unfold APPMEM_END; lia|];
         intros i Hi; split; [apply Happ; lia|];
         exists (Z_to_bv 8 0); split;
         [ rewrite (f32_shadow_in fr i Hfr8 ltac:(lia));
           destruct RW4 as ((_ & Hb4') & _); cbn [cells_bytes cbytes] in Hb4';
           rewrite app_nil_r in Hb4'; destruct Hb4' as (_ & _ & Hb4'');
           pose proof (Hb4'' 0%nat ltac:(cbn [length]; lia)) as Hm4; cbn [Z.of_nat nth_error] in Hm4;
           rewrite Z.add_0_r in Hm4; exact Hm4
         | left; vm_compute; reflexivity ] ]
     (* the catalogue's footprint: its frame, the two runtime cells, the 8 bytes at fr + 32 and their shadow byte *)
     | rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; exact RGsp
     | exact RGgot
     | exact RGcell
     | intros _; split;
       [ exact RG32
       | rewrite Esh0, Esh7; replace (Sfr fr + 4 - (Sfr fr + 4) + 1) with 1 by lia; exact RGsh ] ]
   | intros ms3 Hpost; unfold CATc.reac_box_catalogue_post in Hpost;
     destruct Hpost as (a1' & a2' & m' & Ems & MUc & WMc & MIc & STc & BAc);
     subst ms3;
     replace (ret_pc (Z_to_bv 64 0x8285c)) with (Z_to_bv 64 0x8285c)
       by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]);
     replace (fr + 32 =? 0) with false in BAc by (symmetry; apply Z.eqb_neq; lia);
     apply evtF_done; right; exists a1', a2', m'; split; [reflexivity|];
     split; [reflexivity|]; split; [reflexivity|];
     split;
     [ eapply munch_trans; [exact MU|];
       eapply munch_weaken; [| exact MUc];
       unfold sub_fp; intros z Hz; cbn [outside] in *;
       rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) in Hz by lia;
       rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
       unfold CATc.REAC_BOX_CATALOGUE_FRAME; repeat split; try exact I; lia
     | split; [eapply wmono_trans; [exact WM | exact WMc]|];
       split; [rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) in STc by lia;
         exact STc|];
       split; [exact BAc|];
       destruct RW4 as ((_ & Hb4') & _); cbn [cells_bytes cbytes] in Hb4';
       rewrite app_nil_r in Hb4'; destruct Hb4' as (_ & _ & Hb4'');
       pose proof (Hb4'' 0%nat ltac:(cbn [length]; lia)) as Hm4; cbn [Z.of_nat nth_error] in Hm4;
       rewrite Z.add_0_r in Hm4;
       rewrite (f32_mrd_munch _ _ m' (Sfr fr + 4) MUc ltac:(lia));
       [ exact Hm4
       | rewrite ?(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia;
         cbn [outside];
         unfold CATc.REAC_BOX_CATALOGUE_FRAME; split; [lia|]; split; [lia|exact I] ] ] ]).
Qed.

(* Route (C): F32.f32_evt_m_on's statement (Seg/F32.v), at RNG_all, under the catalogue's _F_on contract. *)
Lemma f32_evt_m_of_F_on :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (Asp fr phi spv lo v16 v17 : Z) (b16 b17 b4 : byte) (junk : list byte),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 Asp -> x19 = Z_to_bv 64 (Sfr fr) ->
    x23 = Z_to_bv 64 phi -> x24 = Z_to_bv 64 9 -> x26 = Z_to_bv 64 ASAN_K ->
    0 <= phi -> phi + 50 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 16) 3 + ASAN_K)) 1 = Some [b16] ->
    (bv_signed b16 = 0 \/ (phi + 16) mod 8 < bv_signed b16 <= 7) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (phi + 17) 3 + ASAN_K)) 1 = Some [b17] ->
    (bv_signed b17 = 0 \/ (phi + 17) mod 8 < bv_signed b17 <= 7) ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [Z_to_bv 8 v16] -> 0 <= v16 < 256 ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [Z_to_bv 8 v17] -> 0 <= v17 < 256 ->
    ro_cells rsegs m (Asp + 40) [C8 (Z_to_bv 64 (fr + 32))] ->
    rw_cells rsegs m (Sfr fr + 4) [C1 b4] -> rw_cells rsegs m (fr + 32) [CB 8 junk] ->
    0 <= fr -> fr mod 8 = 0 -> 6283264 <= fr -> fr + 3136 <= Asp -> Asp + 48 <= 2 ^ 64 ->
    ASAN_K <= Sfr fr -> Sfr fr + 5 <= lo -> 6283264 <= lo -> HIGHMEM_BEG <= lo ->
    lo + 16 <= spv -> spv <= Asp -> spv < 2 ^ 64 ->
    (fr + 3136 <= lo \/ spv <= fr) ->
    (Sfr fr + 5 <= fr + 32 \/ fr + 40 <= Sfr fr + 4) ->
    stk rsegs m lo spv ->
    (forall a, fr + 32 <= a < fr + 40 -> app_mem a) ->
    asan_cells m ->
    LE.evt rsegs
      (fun ms' =>
         (exists y10 y11 y12,
            ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                          x24 x25 x26 x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828c8) fcs None m (seg_rom rsegs)
            /\ (v16 <> 205 \/ v17 <> 234))
         \/ (exists y11 y12 m',
            ms' = MS (mkR (Z_to_bv 64 0x8285c) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 CATc.BOX_CATALOGUE) y11 y12
                          x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (fr + 32)) x25 x26 x27 x28
                          x29 x30 x31) Fr (Z_to_bv 64 0x8285c) fcs None m' (seg_rom rsegs)
            /\ v16 = 205 /\ v17 = 234
            /\ munch [(spv - 16, spv); (Sfr fr + 4, Sfr fr + 5); (fr + 32, fr + 40)] m m'
            /\ wmono rsegs m m' /\ stk rsegs m' lo spv
            /\ bytes_at rsegs m' (fr + 32) (le8 (Z_to_bv 64 11))
            /\ mrd rsegs m' (wa (Sfr fr + 4)) = Some (Z_to_bv 8 0)))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82800) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m Asp fr phi spv lo v16 v17 b16 b17 b4 junk
    E2 E9 E19 E23 E24 E26 Hp0 Hp1 R16s Hok16 R17s Hok17 R16b Hv16 R17b Hv17
    RA40 RW4 RWfr Hfr0 Hfr8 HGT HfrA HAb HSfr0 HSlo HloG HloH Hlosp HspA HspB Hdw Hd4 HST Happ HAC.
  eapply (evtF_evt rsegs RNG_all).
  pose proof (f32_shr_bound phi 16 Hp0 Hp1 ltac:(lia)) as (Hb16a & Hb16b).
  pose proof (f32_shr_bound phi 17 Hp0 Hp1 ltac:(lia)) as (Hb17a & Hb17b).
  assert (HK0 : 0 <= ASAN_K) by (unfold ASAN_K; lia).
  apply (f32_evt_m_F_on RNG_all _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           Fr fcs m Asp fr phi spv lo v16 v17 b16 b17 b4 junk
           E2 E9 E19 E23 E24 E26 Hp0 Hp1 R16s Hok16 R17s Hok17 R16b Hv16 R17b Hv17
           RA40 RW4 RWfr Hfr0 Hfr8 HGT HfrA HAb HSfr0 HSlo HloG HloH Hlosp HspA HspB Hdw Hd4 HST Happ HAC);
    apply rng_all; unfold GOT_CELL_K, CELL_K; lia.
Qed.

End F32F_on.

(* The pin: f32_evt_m_of_F_on states F32.f32_evt_m_on's text, term for term (constr_eq), apart from the first premise,
   which names the _F_on contract in place of the plain _on one; both first premises are checked by name too. *)
Lemma f32_evt_m_of_F_on_verbatim : True.
Proof.
  lazymatch type of F32.f32_evt_m_on with ?P -> ?A =>
  lazymatch type of f32_evt_m_of_F_on with ?Q -> ?B =>
    constr_eq P OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.reac_box_catalogue_contract_on;
    constr_eq Q OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.reac_box_catalogue_contract_F_on;
    constr_eq A B
  end end.
  exact I.
Qed.
