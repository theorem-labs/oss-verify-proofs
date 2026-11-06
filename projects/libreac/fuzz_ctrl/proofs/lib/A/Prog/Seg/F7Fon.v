(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 688 of its 728 lines of code are new or changed and 356 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F7.v, with its module paths and module names changed; 25 of its 83 lines of code are new or changed and 670 lines of the source are left out. *)
(* lib/A/Prog/Seg/F7Fon.v -- route (C) twin of the F7 footprint run (lib/A/Prog/Seg/F7F.v f7_evt_F), ADDITIVE beside-file.
   Written by a Theorem Labs lane under the Seg *F.v twin rule (a Theorem Labs lane 12:52Z, agreed; L3 brief
   L3-brief.md (a working note, not in this delivery)).  rule 24: no function proved (kind: segment run).

   BASE: a Theorem Labs lane's fold blob of F7F.v (an earlier version, blob ddafea9e330, not in this delivery), a working branch 4bae33fdf54.  It is the
   SAME blob a working branch 1502cba0417 / 1899bed1aee carries (diff empty), so the twin is based on both.  F7F.v (not in this delivery) stays
   byte-identical.

   WHAT CHANGES, and nothing else
   - the callee premise is reac_ctrl_kind_name_contract_F_on (lib/A/Prog/reac_ctrl_kind_name_c.v, a Theorem Labs lane's
     statements on a working branch, LANDED 11:24Z / 12:00Z; proved as reac_ctrl_kind_name_holds_F_on in
     lib/A/Prog/reac_ctrl_kind_nameF.v, a Theorem Labs lane 330e60af39d, a Theorem Labs lane SIGNED 12:04Z), in place of
     reac_ctrl_kind_name_contract_F;
   - the premise `shadow_rw m` is REMOVED.  The segment itself (two compares, two loads, the jal) reads and stores no
     shadow byte, and the callee's _on form has no shadow_rw premise (its region is empty: the one shadow byte it
     reads comes from `addressable m KIND_NAME 112`, its only stores are its frame [sp - 16, sp)).  So the run needs
     no shadow byte present through a shadow_rw premise.
   The binders, every other premise, the footprint premises and the post are f7_evt_F's, in the same order; the
   proof is f7_evt_F's with the one premise gone.  No pin back to f7_evt_F: its callee premise is the weaker
   reac_ctrl_kind_name_contract_F, so the twin is not a corollary of it. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F7.
(* Last but YK11: StepF's step / finish work on evtF goals and must shadow lib.Lib Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11's register reads (the names F7's statements are written over). *)
Import YK11.
Open Scope Z_scope.

(* The run 0x81f64 -> 0x81f7c in footprint form, callee in its route (C) form: the two compares not taken, the two
   record loads, and the call composed with reac_ctrl_kind_name_contract_F_on (window [sp-16, sp)). *)
Lemma f7_evt_F_on :
    reac_ctrl_kind_name_contract_F_on ->
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A kp v lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 v -> s8v = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
    bytes_at rsegs m (A + 248) (le8 (Z_to_bv 64 kp)) ->
    bytes_at rsegs m kp (le4 (Z_to_bv 64 v)) ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m -> addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    rng RNG (A + 248) 8 ->
    rng RNG kp 4 ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME) REAC_CTRL_KIND_NAME_FRAME ->
    rng RNG (shadow_addr KIND_NAME) 14 ->
    evtF rsegs RNG
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81f7c) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (kind_name_addr v))
                       a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81f7c) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f64) fc None m (seg_rom rsegs)).
Proof.
  intros HKNF RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m A kp v lo -> -> -> Hv H248 Hkp HKB HKS HST Hlo Hkn HAC HAD Hout R248 Rkp RIMG RSTK RSH.
  assert (HL248 : ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 kp))).
  { pose proof (bytes_at_ov_read rsegs m (A + 248) (le8 (Z_to_bv 64 kp)) 0 8 H248 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HLkp : ov_read_bytes rsegs m (wa kp) 4 = Some (le4 (Z_to_bv 64 v))).
  { pose proof (bytes_at_ov_read rsegs m kp (le4 (Z_to_bv 64 v)) 0 4 Hkp ltac:(rewrite length_le4; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le4; lia). exact HH. }
  (* 0x81f64 bne a0,s8 : a0 = s8, not taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x81f68 ld a0,248(s1) ; 0x81f6c lw a0,0(a0) *)
  step. step. rewrite (sx32_small v Hv).
  (* 0x81f70 bne s8,a0 : equal, not taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x81f74 mv a0,s8 ; 0x81f78 jal reac_ctrl_kind_name *)
  step. step.
  pose proof HKNF as HK.
  unfold reac_ctrl_kind_name_contract_F_on, REAC_CTRL_KIND_NAME in HK.
  eapply evtF_cut.
  { eapply HK with (lo := lo).
    - exact HKB.
    - exact HKS.
    - exact HST.
    - exact Hlo.
    - exact Hkn.
    - exact HAC.
    - exact HAD.
    - exact Hout.
    - exact RIMG.
    - exact RSTK.
    - exact RSH. }
  intros ms' (a1' & a2' & m' & E & MU & WM & MI & ST' & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81f7c)) with (Z_to_bv 64 0x81f7c)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit v) by lia.
  apply evtF_done.
  exists a1', a2', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST'].
Qed.
