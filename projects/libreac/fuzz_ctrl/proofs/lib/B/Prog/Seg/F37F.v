(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 2169 of its 2293 lines of code are new or changed and 887 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F30.v, with its module names and numbers changed; 924 of its 1033 lines of code are new or changed and 2184 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F37.v; 72 of its 149 lines of code are new or changed and 956 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F37.v f37_evt (:292-355) (from a working branch 3803efccea0)
     (blob 64ecf6778ae2ff7c03bcc34ebaf76801084f3701);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f37_evt_of_F_bounded (evtF_evt + rng_all + f37F_lu_evt) re-derives the source statement of
     F37.f37_evt plus two address bounds (0 <= A + 224 for the read at 0x82ca8, F37.v:299; A + 248 <= 2 ^ 64
     for the read at 0x82ca0, F37.v:298; an Exec.evt records no addresses, so the source run states no bound on
     its spill base A), and f37_evt_of_F_bounded_shape compiles that it is the source statement plus exactly
     those bounds. *)
(* rule 24: no function proved. *)
(* Footprint twin of segment F37's machine run 0x82ca0 -> 0x534b4 (the wrapper_free entry, ra = 0x82d1c).
   It is the pre-call stretch of S_F37: the source run f37_evt itself steps no callee (its last step is the
   `jal wrapper_free` at 0x82d18), so there is no _post_F here; seg_F37 composes the allocator's own contract.
   Accesses, all of them data accesses (instruction fetch is not an access):
     read  [A + 240, A + 248)   ld s5,240(s1)   the frame index j
     read  [A + 224, A + 232)   ld s7,224(s1)   p + body_j
     read  [A + 232, A + 240)   ld a0,232(s1)   left_j - h_j
     write [S(fr) + 22, S(fr) + 67)             23 x sb s11,off(s3), the out-of-scope marks of the frame's
                                                local variables (offsets 22..26, 32, 34, 38, 42..50, 56..60, 66)
   so two rng premises: rng RNG (A + 224) 24 (the three spilled words, one adjacent block) and
   rng RNG (Sf + 22) 45 (the marked shadow bytes). No instrumented check is in this range: the 23 stores are
   the runtime's marks, not checks, and they read no shadow byte. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F37.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Exec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Image B's registers, mkst and FPState (the short name YK11 may resolve to lib/Reusable/YK11.v). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module UEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.

(* The start register map of sl_run, in the stepping engine's mkR (F37.v's f37_mkR_of, over lib.Lib's mkR). *)
Lemma f37F_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (Sem.reg_get regs 1) (Sem.reg_get regs 2) (Sem.reg_get regs 3) (Sem.reg_get regs 4) (Sem.reg_get regs 5)
      (Sem.reg_get regs 6) (Sem.reg_get regs 7) (Sem.reg_get regs 8) (Sem.reg_get regs 9) (Sem.reg_get regs 10)
      (Sem.reg_get regs 11) (Sem.reg_get regs 12) (Sem.reg_get regs 13) (Sem.reg_get regs 14) (Sem.reg_get regs 15)
      (Sem.reg_get regs 16) (Sem.reg_get regs 17) (Sem.reg_get regs 18) (Sem.reg_get regs 19) (Sem.reg_get regs 20)
      (Sem.reg_get regs 21) (Sem.reg_get regs 22) (Sem.reg_get regs 23) (Sem.reg_get regs 24) (Sem.reg_get regs 25)
      (Sem.reg_get regs 26) (Sem.reg_get regs 27) (Sem.reg_get regs 28) (Sem.reg_get regs 29) (Sem.reg_get regs 30)
      (Sem.reg_get regs 31).
Proof. intros regs. reflexivity. Qed.

(* The literal length of a stored byte list (F37.v's f37_len). *)
Ltac f37F_len :=
  repeat match goal with
  | |- context [@length byte ?bs] =>
      let n := eval vm_compute in (@length byte bs) in change (@length byte bs) with n
  end.

(* One out-of-scope mark `sb s11,off(s3)`: the shadow byte S(fr) + off is writable in every memory the run has
   reached (wr_at of [S(fr) + 22, S(fr) + 67) survives the earlier stores). *)
Ltac f37F_sb Sf off HWR :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HSo" in
      assert (H : store_ok rsegs mm (wa (Sf + off)) 1 = true)
        by (replace (Sf + off) with (Sf + 22 + (off - 22)) by lia;
            apply (wr_at_store_ok rsegs mm (Sf + 22) 45 (off - 22) 1);
            [repeat apply wr_at_write; exact HWR | lia | lia])
  end; step.

(* The footprint twin of F37.f37_evt: 0x82ca0 -> 0x534b4 (the free entry, through the jal at 0x82d18). *)
Lemma f37_evt_F : forall (RNG : footprint) (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (A Sf W J v224 v232 len phi : Z),
  getr regs 9 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 W -> getr regs 23 = Z_to_bv 64 W ->
  getr regs 18 = Z_to_bv 64 phi -> getr regs 19 = Z_to_bv 64 Sf -> getr regs 20 = Z_to_bv 64 len ->
  getr regs 27 = Z_to_bv 64 (-8) ->
  0 <= Sf -> Sf + FRAME_SHADOW <= 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (A + 240)) 8 = Some (le8 (Z_to_bv 64 J)) ->
  ov_read_bytes rsegs m (wa (A + 224)) 8 = Some (le8 (Z_to_bv 64 v224)) ->
  ov_read_bytes rsegs m (wa (A + 232)) 8 = Some (le8 (Z_to_bv 64 v232)) ->
  wr_at rsegs m (Sf + 22) 45 ->
  rng RNG (A + 224) 24 -> rng RNG (Sf + 22) 45 ->
  evtF rsegs RNG (fun ms' => exists R m', ms' = MS R F (Z_to_bv 64 0x534b4) fc None m' (seg_rom rsegs) /\
      getr R 1 = Z_to_bv 64 0x82d1c /\ getr R 10 = Z_to_bv 64 phi /\
      getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
      getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
      getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 26 = getr regs 26 /\
      getr R 27 = getr regs 27 /\ getr R 22 = getr regs 22 /\
      getr R 23 = Z_to_bv 64 (v224 + len) /\ getr R 25 = Z_to_bv 64 (v232 - len) /\
      getr R 21 = Z_to_bv 64 J /\
      munch [(Sf + 22, Sf + 67)] m m' /\ wmono rsegs m m' /\
      (forall q, 0 <= q < 2 ^ 64 -> (exists b, mrd rsegs m (wa q) = Some b) ->
         exists b, mrd rsegs m' (wa q) = Some b))
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x82ca0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG regs F fc m A Sf W J v224 v232 len phi E9 E10 E23 E18 E19 E20 E27 HS0 HS1 L240 L224 L232 HWR
    RA RSh.
  pose proof FRAME_SHADOW_val as HFSv.
  pose proof (rng_bounds RNG (A + 224) 24 RA) as HAb.
  pose proof (rng_bounds RNG (Sf + 22) 45 RSh) as HShb.
  rewrite f37F_mkR_of.
  assert (R9 : Sem.reg_get regs 9 = Z_to_bv 64 A) by exact E9.
  assert (R10 : Sem.reg_get regs 10 = Z_to_bv 64 W) by exact E10.
  assert (R23 : Sem.reg_get regs 23 = Z_to_bv 64 W) by exact E23.
  assert (R18 : Sem.reg_get regs 18 = Z_to_bv 64 phi) by exact E18.
  assert (R19 : Sem.reg_get regs 19 = Z_to_bv 64 Sf) by exact E19.
  assert (R20 : Sem.reg_get regs 20 = Z_to_bv 64 len) by exact E20.
  assert (R27 : Sem.reg_get regs 27 = Z_to_bv 64 (-8)) by exact E27.
  rewrite R9, R10, R23, R18, R19, R20, R27.
  (* 0x82ca0 ld s5,240(s1) *)
  step.
  (* 0x82ca4 bne a0,s7,82fa4 (both W): not taken *)
  step. if_false.
  (* 0x82ca8 ld s7,224(s1); 0x82cac add s7,s7,s4; 0x82cb0 ld a0,232(s1); 0x82cb4 sub s9,a0,s4 *)
  step. step. step. step.
  (* 0x82cb8 .. 0x82d10: the 23 out-of-scope marks, shadow offsets 22 .. 66 of the frame *)
  f37F_sb Sf 59 HWR. f37F_sb Sf 60 HWR. f37F_sb Sf 66 HWR. f37F_sb Sf 50 HWR. f37F_sb Sf 56 HWR.
  f37F_sb Sf 57 HWR. f37F_sb Sf 58 HWR. f37F_sb Sf 46 HWR. f37F_sb Sf 47 HWR. f37F_sb Sf 48 HWR.
  f37F_sb Sf 49 HWR. f37F_sb Sf 42 HWR. f37F_sb Sf 43 HWR. f37F_sb Sf 44 HWR. f37F_sb Sf 45 HWR.
  f37F_sb Sf 26 HWR. f37F_sb Sf 32 HWR. f37F_sb Sf 34 HWR. f37F_sb Sf 38 HWR. f37F_sb Sf 22 HWR.
  f37F_sb Sf 23 HWR. f37F_sb Sf 24 HWR. f37F_sb Sf 25 HWR.
  (* 0x82d14 mv a0,s2; 0x82d18 jal wrapper_free *)
  step. step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm)
  end.
  assert (MU : munch [(Sf + 22, Sf + 67)] m m1).
  { unfold m1.
    do 23 (apply munch_write; [| lia | f37F_len; lia | cbn [inside]; left; f37F_len; split; lia]).
    apply munch_refl. }
  assert (WM : wmono rsegs m m1) by (unfold m1; do 23 (apply wmono_write); apply wmono_refl).
  assert (HPR : forall q, 0 <= q < 2 ^ 64 -> (exists b, mrd rsegs m (wa q) = Some b) ->
            exists b, mrd rsegs m1 (wa q) = Some b).
  { intros q Hq Hb. unfold m1.
    do 23 (apply F37.f37_pres_write; [lia | f37F_len; lia | lia |]). exact Hb. }
  finish.
  all: first [ reflexivity | apply F37.f37_bv_add | apply F37.f37_bv_sub | assumption
             | (rewrite ?E9, ?E10, ?E23, ?E18, ?E19, ?E20, ?E27; reflexivity) ].
Qed.

(* A lib.Lib run is a UL run: the two step relations have the same body (F17b.v's f17_lu_msteps). *)
Lemma f37F_lu_msteps : forall s s', msteps rsegs s s' -> UEx.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UEx.msteps_refl|].
  eapply UEx.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma f37F_lu_evt : forall Q ms, evt rsegs Q ms -> UEx.evt rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (f37F_lu_msteps _ _ H) | exact HQ]. Qed.

(* The compare lemma (auditor a Theorem Labs lane): the source statement of F37.f37_evt, re-derived from f37_evt_F at
   RNG := RNG_all with every rng premise by rng_all. It is NOT the source statement verbatim: it adds the two
   address bounds 0 <= A + 224 (the read at 0x82ca8, `ld s7,224(s1)`, F37.v:299) and A + 248 <= 2 ^ 64 (the
   read at 0x82ca0, `ld s5,240(s1)`, F37.v:298), which rng_all needs and which an Exec.evt, recording no
   address, never states. Hence the name _bounded, and the shape lemma below, which compiles that the bounded
   statement is the source statement plus those two bounds and nothing else. *)
Lemma f37_evt_of_F_bounded : forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (A Sf W J v224 v232 len phi : Z),
  getr regs 9 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 W -> getr regs 23 = Z_to_bv 64 W ->
  getr regs 18 = Z_to_bv 64 phi -> getr regs 19 = Z_to_bv 64 Sf -> getr regs 20 = Z_to_bv 64 len ->
  getr regs 27 = Z_to_bv 64 (-8) ->
  0 <= Sf -> Sf + FRAME_SHADOW <= 2 ^ 64 ->
  0 <= A + 224 -> A + 248 <= 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (A + 240)) 8 = Some (le8 (Z_to_bv 64 J)) ->
  ov_read_bytes rsegs m (wa (A + 224)) 8 = Some (le8 (Z_to_bv 64 v224)) ->
  ov_read_bytes rsegs m (wa (A + 232)) 8 = Some (le8 (Z_to_bv 64 v232)) ->
  wr_at rsegs m (Sf + 22) 45 ->
  UEx.evt rsegs (fun ms' => exists R m', ms' = MS R F (Z_to_bv 64 0x534b4) fc None m' (seg_rom rsegs) /\
      getr R 1 = Z_to_bv 64 0x82d1c /\ getr R 10 = Z_to_bv 64 phi /\
      getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
      getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
      getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 26 = getr regs 26 /\
      getr R 27 = getr regs 27 /\ getr R 22 = getr regs 22 /\
      getr R 23 = Z_to_bv 64 (v224 + len) /\ getr R 25 = Z_to_bv 64 (v232 - len) /\
      getr R 21 = Z_to_bv 64 J /\
      munch [(Sf + 22, Sf + 67)] m m' /\ wmono rsegs m m' /\
      (forall q, 0 <= q < 2 ^ 64 -> (exists b, mrd rsegs m (wa q) = Some b) ->
         exists b, mrd rsegs m' (wa q) = Some b))
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x82ca0) fc None m (seg_rom rsegs)).
Proof.
  intros regs F fc m A Sf W J v224 v232 len phi E9 E10 E23 E18 E19 E20 E27 HS0 HS1 HA0 HA1 L240 L224 L232 HWR.
  pose proof FRAME_SHADOW_val as HFSv.
  apply f37F_lu_evt. apply (evtF_evt rsegs RNG_all).
  apply (f37_evt_F RNG_all regs F fc m A Sf W J v224 v232 len phi); try assumption.
  - apply rng_all; lia.
  - apply rng_all; lia.
Qed.

(* The bounded compare statement is the source statement plus the two address bounds: the source lemma's own
   type implies it. *)
Lemma f37_evt_of_F_bounded_shape :
  ltac:(let T := type of F37.f37_evt in let U := type of f37_evt_of_F_bounded in exact (T -> U)).
Proof.
  intro H.
  intros regs F fc m A Sf W J v224 v232 len phi E9 E10 E23 E18 E19 E20 E27 HS0 HS1 HA0 HA1 L240 L224 L232 HWR.
  apply (H regs F fc m A Sf W J v224 v232 len phi); assumption.
Qed.
