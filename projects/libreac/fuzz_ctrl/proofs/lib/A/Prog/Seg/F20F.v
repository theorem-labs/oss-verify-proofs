(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 540 of its 622 lines of code are new or changed and 2475 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F20.v; 61 of its 118 lines of code are new or changed and 565 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F20.v blob 1cf48b422ebf (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f20_call_evt_of_F re-derives F20.f20_call_evt at ExecF.RNG_all; f20_call_evt_of_F_verbatim checks by
   constr_eq that its type is the type of F20.f20_call_evt after F20's own first premise (the plain checksum
   contract). Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only.
   Callee _F cited: reac_ctrl_checksum_verify_contract_F (lib/A/Prog/reac_ctrl_checksum_verify_c.v on the base),
   proved by lib/A/Prog/reac_ctrl_checksum_verify_F.v (base blob, Theorem reac_ctrl_checksum_verify_F_holds), so
   the twin takes no contract premise. *)
(* The footprint twin of F20.v f20_call_evt: the same run (0x824ac `mv a0,s7` ; 0x824b0
   `jal reac_ctrl_checksum_verify@0x834a8`, return to 0x824b4) as an ExecF.evtF under a footprint RNG. The two
   instructions touch no data; every access of the run is the callee's, so the footprint premises are exactly the
   five of reac_ctrl_checksum_verify_contract_F: its 16-byte frame [sp - 16, sp), the GOT cell of the shadow-offset
   cell and that cell, the 32 record bytes [phi + 18, phi + 50), and the shadow bytes of those bytes. F20.v is
   unchanged. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_checksum_verify_c.
(* The checksum verifier's owner proof; not imported, so its helper names shadow nothing here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_checksum_verify_F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState Regs6ss RegisterBridge Exec Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F20.
(* StepF after the old engine: its step / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* YK11 last, as in F20.v (its seg_rom). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11.
Import ListNotations.
Open Scope Z_scope.

Module CKVF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_checksum_verify_F.

(* ---- The call, 0x824ac -> 0x824b4, under the callee's footprint contract. This is the file's one use of that
   contract: its owner's proof reac_ctrl_checksum_verify_F_holds. ---- *)
Lemma f20_call_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi A lo sp : Z) (blk : list byte),
    0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    length blk = 32%nat -> bytes_at rsegs m (phi + 18) blk ->
    stk rsegs m lo sp ->
    asan_cells m -> shadow_rw m -> addressable m (phi + 18) 32 ->
    ExecF.rng RNG (sp - 16) 16 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (phi + 18) 32 ->
    ExecF.rng RNG ((phi + 18) / 8 + ASAN_K) ((phi + 49) / 8 - (phi + 18) / 8 + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (if blocksum blk =? 0 then 0 else -1)) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x824b4) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp)
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x824ac) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi A lo sp blk Rsp Hp0 HpE Hpsp Hlo Hlo16 Lblk Hblk Hstk HAC HSW Hadr RFr RGOT RCK RDAT RSH.
  assert (Esp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  (* 0x824ac mv a0,s7 ; 0x824b0 jal reac_ctrl_checksum_verify *)
  step. step.
  eapply ExecF.evtF_cut.
  { eapply CKVF.reac_ctrl_checksum_verify_F_holds with (p := phi) (lo := lo) (bs := blk);
      unfold REAC_CTRL_CHECKSUM_VERIFY_FRAME; rewrite ?Esp.
    - lia.
    - unfold APPMEM_END in HpE. lia.
    - reflexivity.
    - exact Lblk.
    - exact Hblk.
    - exact Hstk.
    - lia.
    - left. lia.
    - exact HAC.
    - exact HSW.
    - exact Hadr.
    - outW. unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
    - exact RFr.
    - exact RGOT.
    - exact RCK.
    - exact RDAT.
    - exact RSH. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & _ & ST'). subst ms'.
  unfold REAC_CTRL_CHECKSUM_VERIFY_FRAME in MU, ST'. rewrite Esp in MU, ST'.
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
  apply ExecF.evtF_done.
  do 7 eexists. exists m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

(* ---- F20.f20_call_evt restated: evtF_evt of the twin at RNG_all, each rng premise by rng_all. ---- *)
Ltac f20_rng_all :=
  apply ExecF.rng_all;
  unfold GOT_CELL_K, CELL_K, ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia.

Lemma f20_call_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi A lo sp : Z) (blk : list byte),
    0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    length blk = 32%nat -> bytes_at rsegs m (phi + 18) blk ->
    stk rsegs m lo sp ->
    asan_cells m -> shadow_rw m -> addressable m (phi + 18) 32 ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (if blocksum blk =? 0 then 0 else -1)) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x824b4) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp)
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x824ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi A lo sp blk Rsp Hp0 HpE Hpsp Hlo Hlo16 Lblk Hblk Hstk HAC HSW Hadr.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f20_call_evt_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m phi A lo sp blk); try assumption; f20_rng_all.
Qed.

(* The pin: f20_call_evt_of_F states F20's text after F20's own first premise, the plain checksum contract
   (F20.v Section S, Hypothesis CKV), term for term (constr_eq: syntactic, not up to conversion). The corollary
   needs no premise in its place: the callee is proved (reac_ctrl_checksum_verify_F_holds). *)
Example f20_call_evt_of_F_verbatim : True.
Proof.
  lazymatch type of F20.f20_call_evt with ?P -> ?A =>
    constr_eq P reac_ctrl_checksum_verify_contract;
    let B := type of f20_call_evt_of_F in constr_eq A B
  end.
  exact I.
Qed.
