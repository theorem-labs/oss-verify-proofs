(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 232 of its 267 lines of code are new or changed and 361 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P11.v, with its module paths and module names changed; 127 of its 198 lines of code are new or changed and 196 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/P11.v f0a39ffef74b (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: p11_evt_of_F re-derives P11.p11_evt at ExecF.RNG_all; p11_evt_of_F_verbatim checks by constr_eq that
   its type is the type of P11.p11_evt. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only.
   Source comment P11.v:14 names 0xa1000 (the end of the v1.9 GNU_RELRO range); no statement and no proof step of
   P11.v or of this file uses it. *)
(* The footprint twin of P11.v p11_evt (0x81c60-0x81c80, nine instructions and the call of reac_ctrl_kind_name with
   x = 14, which returns QMARK and writes only its 16-byte window [sp - 16, sp)). The footprint premises: the spill
   the run loads at 0x81c6c (`ld a0,280(s1)`, the 8 bytes at A + 280 the premise bytes_at names) and the code byte
   it loads at 0x81c70 (`lbu a0,0(a0)`, the byte at c the premise bytes_at names, no instrumented check), plus the
   three regions the callee's footprint contract reac_ctrl_kind_name_contract_F names: the image range, its frame
   window and the 14 shadow bytes of the kind-name table. The callee premise sits where P11.v's Section Hypothesis
   HKN sits, with the footprint contract in place of the plain one. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot P7 P11.
(* Last: StepF's step / if_true / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

Section CallF.
(* The callee's footprint contract, in the position of P11.v's Section Hypothesis HKN. *)
Hypothesis HKNF : reac_ctrl_kind_name_contract_F.

Lemma p11_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c lo : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 (-1) -> 0 <= c < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 c)) ->
    bytes_at rsegs m c [Z_to_bv 8 0] ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m -> shadow_rw m ->
    addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    ExecF.rng RNG (A + 280) 8 ->
    ExecF.rng RNG c 1 ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME) REAC_CTRL_KIND_NAME_FRAME ->
    ExecF.rng RNG (shadow_addr KIND_NAME) 14 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c84) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QMARK)
                       a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81c84) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c lo -> -> Hc H280 Hcb HT HS HST Hlo Hkt HAC HSW HAD Hout R280 Rc RIMG RFR RSH.
  assert (HL280 : ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 c))).
  { pose proof (bytes_at_ov_read rsegs m (A + 280) (le8 (Z_to_bv 64 c)) 0 8 H280
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HLc : ov_read_bytes rsegs m (wa c) 1 = Some [Z_to_bv 8 0]).
  { pose proof (bytes_at_ov_read rsegs m c [Z_to_bv 8 0] 0 1 Hcb ltac:(cbn; lia)) as HH.
    cbn [Z.of_nat firstn skipn] in HH. rewrite Z.add_0_r in HH. exact HH. }
  (* v1.9: two taken branches where v1.8 had two not-taken ones (81c64 `beq a0,a1` with a0 = a1 = -1, 81c74
     `beqz a0` with a0 = 0); the NEW-only `j 82bf4` at 81c68 / 81c78 are not reached. *)
  step. (* 81c60 li a1,-1 *)
  step. (* 81c64 beq a0,a1,81c6c (NEW-only) *)
  if_true.
  step. (* 81c6c ld a0,280(s1) *)
  step. (* 81c70 lbu a0,0(a0) *)
  step. (* 81c74 beqz a0,81c7c (NEW-only) *)
  if_true.
  step. (* 81c7c li a0,14 *)
  step. (* 81c80 jal reac_ctrl_kind_name *)
  pose proof HKNF as HP. unfold reac_ctrl_kind_name_contract_F, REAC_CTRL_KIND_NAME in HP.
  eapply ExecF.evtF_cut.
  { eapply HP with (lo := lo).
    all: assumption. }
  intros ms' (a1' & a2' & m' & E & MU & WM & MIi & ST' & _).
  subst ms'.
  match goal with |- context [kind_name_addr (bv_unsigned ?w)] =>
    replace (kind_name_addr (bv_unsigned w)) with QMARK by (vm_compute; reflexivity) end.
  replace (ret_pc (Z_to_bv 64 0x81c84)) with (Z_to_bv 64 0x81c84)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  exists a1', a2', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

(* P11.p11_evt's statement (after its callee premise) as a corollary: p11_evt_F at RNG_all, every rng premise by
   rng_all. *)
Lemma p11_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c lo : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 (-1) -> 0 <= c < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 c)) ->
    bytes_at rsegs m c [Z_to_bv 8 0] ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m -> shadow_rw m ->
    addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    LE.evt rsegs
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c84) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QMARK)
                       a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81c84) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c lo E1 E0 Hc H280 Hcb HT HS HST Hlo Hkt HAC HSW HAD Hout.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof HST as (ST0 & _ & _).
  pose proof (bytes_at_bound rsegs m (A + 280) (le8 (Z_to_bv 64 c)) H280) as HA280.
  rewrite length_le8 in HA280.
  eapply ExecF.evtF_evt.
  apply (p11_evt_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 Fr fc m A c lo); try assumption.
  - apply ExecF.rng_all; lia.                                            (* [A + 280, A + 288) *)
  - apply ExecF.rng_all; lia.                                            (* the code byte at c *)
  - apply ExecF.rng_all; lia.                                            (* the image range *)
  - unfold REAC_CTRL_KIND_NAME_FRAME in *. apply ExecF.rng_all; lia.     (* the callee window *)
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K, KIND_NAME; Z.div_mod_to_equations; lia.
Qed.

End CallF.

(* The pin: p11_evt_of_F states P11.p11_evt's text after its first premise, term for term (constr_eq: syntactic,
   not up to conversion); the two first premises are the plain and the footprint contract of
   reac_ctrl_kind_name. *)
Example p11_evt_of_F_verbatim : True.
Proof.
  lazymatch type of P11.p11_evt with ?P -> ?A =>
  lazymatch type of p11_evt_of_F with ?Q -> ?B =>
    constr_eq P reac_ctrl_kind_name_contract;
    constr_eq Q reac_ctrl_kind_name_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.

(* ---- route (C): p11_evt_F_on, the _on twin of p11_evt_F (additive; p11_evt_F above is unchanged). ----
   The callee premise is a Theorem Labs lane's reac_ctrl_kind_name_contract_F_on (lib/A/Prog/reac_ctrl_kind_name_c.v, blob
   b4ceb15d813 at 74f16d5f8e7), cited by name in the position of HKNF. The run's R (the shadow bytes it reads or
   stores THROUGH its shadow_rw premise, form rule R amended 10:33Z) is EMPTY, so the premise shadow_rw m is DROPPED
   (no fun _ => False region), as the callee's own _on statements do. How R was derived:
   - the run's own steps, 0x81c60-0x81c80 (li, beq, ld a0,280(s1), lbu a0,0(a0), beqz, li, jal): no instrumented
     check, so no shadow read; the two loads read the spill A + 280 and the code byte c (P11F.rng.tsv:2-3), outside
     the shadow; the run stores nothing;
   - the callee's R at the call: EMPTY (reac_ctrl_kind_name_c.v route (C) comment: the one shadow byte of the table
     entry it may read comes from addressable m KIND_NAME 112 through rt_shadow_rd, not from shadow_rw; it stores
     only its frame [sp - 16, sp), outside the shadow).
   P11F.rng.tsv:6, the 14 shadow bytes of the kind-name table at shadow_addr KIND_NAME, is the callee's RNG footprint
   row. It stays here as the premise ExecF.rng RNG (shadow_addr KIND_NAME) 14. It is not a shadow_rw region. The post
   is p11_evt_F's: it names no shadow_rw m', so it has no transport. Same script as p11_evt_F, without HSW. The plain
   twin P11.p11_evt_on (not in this delivery; written on a working branch b1e8eb09299) drops the premise for the same reasons. *)
Section CallF_on.
Hypothesis HKNF_on : reac_ctrl_kind_name_contract_F_on.

Lemma p11_evt_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c lo : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 (-1) -> 0 <= c < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 c)) ->
    bytes_at rsegs m c [Z_to_bv 8 0] ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m ->
    addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    ExecF.rng RNG (A + 280) 8 ->
    ExecF.rng RNG c 1 ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME) REAC_CTRL_KIND_NAME_FRAME ->
    ExecF.rng RNG (shadow_addr KIND_NAME) 14 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c84) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QMARK)
                       a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81c84) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c lo -> -> Hc H280 Hcb HT HS HST Hlo Hkt HAC HAD Hout R280 Rc RIMG RFR RSH.
  assert (HL280 : ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 c))).
  { pose proof (bytes_at_ov_read rsegs m (A + 280) (le8 (Z_to_bv 64 c)) 0 8 H280
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HLc : ov_read_bytes rsegs m (wa c) 1 = Some [Z_to_bv 8 0]).
  { pose proof (bytes_at_ov_read rsegs m c [Z_to_bv 8 0] 0 1 Hcb ltac:(cbn; lia)) as HH.
    cbn [Z.of_nat firstn skipn] in HH. rewrite Z.add_0_r in HH. exact HH. }
  step. (* 81c60 li a1,-1 *)
  step. (* 81c64 beq a0,a1,81c6c (NEW-only) *)
  if_true.
  step. (* 81c6c ld a0,280(s1) *)
  step. (* 81c70 lbu a0,0(a0) *)
  step. (* 81c74 beqz a0,81c7c (NEW-only) *)
  if_true.
  step. (* 81c7c li a0,14 *)
  step. (* 81c80 jal reac_ctrl_kind_name *)
  pose proof HKNF_on as HP. unfold reac_ctrl_kind_name_contract_F_on, REAC_CTRL_KIND_NAME in HP.
  eapply ExecF.evtF_cut.
  { eapply HP with (lo := lo).
    all: assumption. }
  intros ms' (a1' & a2' & m' & E & MU & WM & MIi & ST' & _).
  subst ms'.
  match goal with |- context [kind_name_addr (bv_unsigned ?w)] =>
    replace (kind_name_addr (bv_unsigned w)) with QMARK by (vm_compute; reflexivity) end.
  replace (ret_pc (Z_to_bv 64 0x81c84)) with (Z_to_bv 64 0x81c84)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  exists a1', a2', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

End CallF_on.
