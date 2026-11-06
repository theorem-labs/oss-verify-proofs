(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its numbers changed; 495 of its 533 lines of code are new or changed and 358 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F22.v, with its module paths and module names changed; 29 of its 89 lines of code are new or changed and 473 lines of the source are left out. *)
(* lib/A/Prog/Seg/F22Fon.v -- route (C) twin of Seg/F22F.v's f22_tail_F, WITHOUT the universal `shadow_rw m`
   premise.  ADDITIVE beside-file (a Theorem Labs lane 12:52Z twin rule): Seg/F22F.v stays unchanged apart from comment text.
   Writer: a Theorem Labs lane for a Theorem Labs lane.  proves no function (kind: segment lemma).

   BASE: a Theorem Labs lane's fold blob of Seg/F22F.v, a working branch 4bae33fdf54, blob 677b7bc7239;
   a working branch 1899bed1aee carries the SAME blob (an earlier version, blob 677b7bc7239, not in this delivery) (diffed: empty), so the base is both.

   MEASURED (why the premise is removed, not narrowed): in F22F.v's f22_tail_F the premise `shadow_rw m` (named HSW)
   is never read and never stored through; its only use is `exact HSW` at the record verifier's contract
   (F22F.v:209).  The tail 0x8258c -> 0x825a0 loads no shadow byte itself and stores none.  The other run the stage
   lifts, f22_loop_F (0x82554 -> 0x8258c), has no shadow_rw premise (its six shadow loads come from its byte premise
   on the six shadow bytes), so it needs no twin and is cited from F22F.v as it is.

   CALLEE FORM: reac_ctrl_headamp_record_verify_contract_F_on (premise DROPPED; LANDED.md (a working note, not in this delivery), a Theorem Labs lane
   a working branch 9509908083d, statement blob reac_ctrl_headamp_record_verify_c.v 86718f5a3d6), discharged
   by reac_ctrl_headamp_record_verify_holds_F_on (LANDED.md (a working note, not in this delivery), a Theorem Labs lane 36bfd511da3, in a working branch
   330e60af39d, blob reac_ctrl_headamp_record_verify_F.v 67d0e3dc3d4).

   THE TWIN: f22_tail_F_on <- f22_tail_F (same statement minus the one premise; the proof is F22F.v's text minus the
   hand-on), in a Section with F22F.v's own Context.  No pin back to the old lemma.  No unproved step, no Axiom. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcFrag RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_headamp_record_verify_c.
(* The record verifier's owner proof; not imported, so its helper names shadow nothing here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_headamp_record_verify_F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState Regs6ss RegisterBridge Exec Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F22.
(* StepF after the old engine: its step / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* YK11 last, as in F22.v (its seg_rom). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11.
Import ListNotations.
Local Open Scope Z_scope.

Section SFon.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.

Lemma f22_tail_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi lo sp : Z) (b0 b1 : byte) (rec : list byte),
    0 <= sp < 2 ^ 64 -> 0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    bytes_at rsegs m (phi + 18) [b0; b1] -> length rec = 6%nat -> bytes_at rsegs m (phi + 34) rec ->
    stk rsegs m lo sp -> asan_cells m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    ExecF.rng RNG (phi + 18) 2 -> ExecF.rng RNG (phi + 34) 6 ->
    ExecF.rng RNG (shadow_addr (phi + 18)) (shadow_addr (phi + 19) - shadow_addr (phi + 18) + 1) ->
    ExecF.rng RNG (shadow_addr (phi + 34)) (shadow_addr (phi + 39) - shadow_addr (phi + 34) + 1) ->
    ExecF.rng RNG (sp - 16) 16 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if hv b0 b1 rec then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (if psum rec 6 mod 128 =? 0 then 0 else -1)) s5 s6 (Z_to_bv 64 phi)
                       s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x825a0) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\ stk rsegs m' lo sp)
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (psum rec 6)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8258c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi lo sp b0 b1 rec Rsp Hp0 HpE Hpsp Hlo Hlo16 H18 Lrec Hrec Hstk HAC Had2 Had6
    R18 R34 RS18 RS34 RFr RGOT RCK.
  assert (Esp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  pose proof (f22_psum_range rec 6) as PR. change (Z.of_nat 6) with 6 in PR.
  (* 0x8258c andi a0,a1,127 ; 0x82590 seqz s4,a0 ; 0x82594 addi s4,s4,-1 *)
  step. step. step.
  rewrite (f22_s0 (psum rec 6)) by lia.
  (* 0x82598 mv a0,s7 ; 0x8259c jal reac_ctrl_headamp_record_verify *)
  step. step.
  eapply ExecF.evtF_cut.
  { eapply reac_ctrl_headamp_record_verify_F.reac_ctrl_headamp_record_verify_holds_F_on with (p := phi) (lo := lo) (b0 := b0) (b1 := b1) (rec := rec);
      unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME; rewrite ?Esp.
    - first [reflexivity | f_equal; lia].
    - lia.
    - unfold APPMEM_END in HpE. lia.
    - exact H18.
    - exact Lrec.
    - exact Hrec.
    - exact Hstk.
    - lia.
    - left. lia.
    - left. lia.
    - exact HAC.
    - exact Had2.
    - exact Had6.
    - outW. unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
      lia.
    - exact RFr.
    - exact RGOT.
    - exact RCK.
    - exact R18.
    - exact R34.
    - exact RS18.
    - exact RS34. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & _ & ST'). subst ms'.
  unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME in MU, ST'. rewrite Esp in MU, ST'.
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
  apply ExecF.evtF_done.
  do 7 eexists. exists m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

End SFon.
