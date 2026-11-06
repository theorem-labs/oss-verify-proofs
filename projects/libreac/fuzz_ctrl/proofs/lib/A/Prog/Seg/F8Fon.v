(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 688 of its 728 lines of code are new or changed and 356 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F7.v, with its module names and addresses changed; 174 of its 732 lines of code are new or changed and 170 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F8.v, with its module paths and module names changed; 24 of its 71 lines of code are new or changed and 685 lines of the source are left out. *)
(* lib/A/Prog/Seg/F8Fon.v -- route (C) twin of the F8 footprint run (lib/A/Prog/Seg/F8F.v f8_evt_F), ADDITIVE beside-file.
   Written by a Theorem Labs lane under the Seg *F.v twin rule (a Theorem Labs lane 12:52Z, agreed; L3 brief
   L3-brief.md (a working note, not in this delivery)).  rule 24: no function proved (kind: segment run).

   BASE: a Theorem Labs lane's fold blob of F8F.v (an earlier version, blob 7901c571efe, not in this delivery), a working branch 4bae33fdf54.  It is the
   SAME blob a working branch 1502cba0417 / 1899bed1aee carries (diff empty), so the twin is based on both.  F8F.v (not in this delivery) stays
   byte-identical.

   WHAT CHANGES, and nothing else
   - the callee premise is reac_ctrl_kind_name_contract_F_on (lib/A/Prog/reac_ctrl_kind_name_c.v, a Theorem Labs lane's
     statements on a working branch, LANDED 11:24Z / 12:00Z; proved as reac_ctrl_kind_name_holds_F_on in
     lib/A/Prog/reac_ctrl_kind_nameF.v, a Theorem Labs lane 330e60af39d, a Theorem Labs lane SIGNED 12:04Z), in place of
     reac_ctrl_kind_name_contract_F;
   - the premise `shadow_rw m` is REMOVED.  The segment itself (beqz a0, mv a0,s8, the jal) touches no memory, and
     the callee's _on form has no shadow_rw premise (its region is empty: the one shadow byte it reads comes from
     `addressable m KIND_NAME 112`, its only stores are its frame [sp - 16, sp)).
   The binders, every other premise, the footprint premises and the post are f8_evt_F's, in the same order; the
   proof is f8_evt_F's with the one premise gone.  No pin back to f8_evt_F: its callee premise is the weaker
   reac_ctrl_kind_name_contract_F, so the twin is not a corollary of it. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F8.
(* Last but YK11: StepF's step / finish work on evtF goals and must shadow lib.Lib Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11's register reads (the names F8's statements are written over). *)
Import YK11.
Open Scope Z_scope.

(* The three instructions in footprint form, callee in its route (C) form: beqz a0 not taken (a0 <> 0), mv a0,s8,
   and the call composed with reac_ctrl_kind_name_contract_F_on, landing at 0x81f88 with a0 = kind_name_addr v. *)
Lemma f8_evt_F_on :
    reac_ctrl_kind_name_contract_F_on ->
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v lo : Z),
    bv_eqb a0 (Z_to_bv 64 0) = false -> s8 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m -> addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME) REAC_CTRL_KIND_NAME_FRAME ->
    rng RNG (shadow_addr KIND_NAME) 14 ->
    evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (kind_name_addr v))
                       a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81f88) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (kind_name_addr v) (cstr_bytes (kind_name v)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f7c) fc None m (seg_rom rsegs)).
Proof.
  intros HKNF RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m v lo Hnz -> Hv HKB HKS HST Hlo Hkn HAC HAD HOUT RIMG RSTK RSH.
  (* 0x81f7c beqz a0 : a0 <> 0, not taken *)
  step. rewrite Hnz. cbv iota.
  (* 0x81f80 mv a0,s8 ; 0x81f84 jal reac_ctrl_kind_name *)
  step. step.
  pose proof HKNF as HK.
  unfold reac_ctrl_kind_name_contract_F_on, REAC_CTRL_KIND_NAME in HK.
  assert (Ev : bv_unsigned (Z_to_bv 64 v) = v)
    by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; exact Hv).
  eapply evtF_cut.
  { eapply HK with (lo := lo).
    - exact HKB.
    - exact HKS.
    - exact HST.
    - exact Hlo.
    - exact Hkn.
    - exact HAC.
    - exact HAD.
    - exact HOUT.
    - exact RIMG.
    - exact RSTK.
    - exact RSH. }
  intros ms' (a1' & a2' & m' & E & MU & WM & MI & ST & HN).
  subst ms'. rewrite Ev in HN |- *.
  replace (ret_pc (Z_to_bv 64 532360)) with (Z_to_bv 64 532360)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evtF_done.
  exists (Z_to_bv 64 532360), a1', a2', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST | exact HN].
Qed.
