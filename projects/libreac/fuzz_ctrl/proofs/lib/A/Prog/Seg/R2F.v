(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 462 of its 587 lines of code are new or changed and 1077 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R2.v, with its module paths and module names changed; 78 of its 151 lines of code are new or changed and 514 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R2.v blob 85d74a72941b (the blob this tree had at release c5e779efe8c) at 6a74d5929d2.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: r2_evt_of_F re-derives R2.r2_evt at ExecF.RNG_all; r2_evt_of_F_verbatim checks by constr_eq that its
   type is the type of R2.r2_evt after the callee premise. Mechanical re-run, route (a) (lead 22:15Z); input to the
   ported walk only. *)

(* The footprint (ExecF.evtF) twin of R2.v's one run lemma r2_evt (segment-runs-A.tsv row S_R2, r2_evt:196):
   0x814f8-0x8152c, the two non-taken abort tests, the catalogue row arithmetic, and the call of meta_fill_00
   (__asan_set_shadow_00 at 0x54ee8) by its contract.
   r2_evt_F is r2_evt with the footprint RNG bound FIRST, the same binders and premises in the same order, and the
   footprint premises appended; the FIRST premise is the callee's footprint contract
   asan_set_shadow_c F.asan_set_shadow_00_contract_F in the place of R2.r2_evt's plain
   SSH.asan_set_shadow_00_contract (the Seg/R3F.v shape).
   Appended premises:
     - RngBytes.rng_bytes RNG: a premise of the callee contract itself (the route-1 proof needs the footprint
       byte-wise, since an access may straddle two adjacent rng ranges). It is PASSED THROUGH unchanged, as the
       spec directs for a callee premise that is itself a forall-memory form.
     - ExecF.rng RNG c 8: the count cell [s2] the test at 0x81504 loads (premise ro_cells rsegs m c [C8 ...]).
     - ExecF.rng RNG (A + 152) 8: the spill [A + 152] = S(fr) + 68 that 0x81520 loads (premise
       ro_cells rsegs m (A + 152) [C8 (Z_to_bv 64 Q)]).
     - the three regions the callee needs by its own contract_F: the image [IMG_LO, IMG_HI) (its code, its GOT
       cell GOT_REAL_MEMSET and the runtime cell REAL_MEMSET), its own stack window
       [sp - ASAN_SET_SHADOW_K, sp) with ASAN_SET_SHADOW_K = 0 (EXACT; the helper and musl memset have no frame),
       and the written range [Q, Q + 186) (premise rw_cells rsegs m Q [CB 186 junk]).
   The call runs on the normalized memory, as in R2.v; the lift is lib/A/MemNormF.v evtF_normalize_ro, the evtF
   form of MemNorm.evt_normalize. R2.v is unchanged. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_set_shadow_c asan_set_shadow_cF ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R2.
(* Last: StepF's step / if_true / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module SSH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_set_shadow_c.
Module IMGB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module SSHF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_set_shadow_cF.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module RBY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.

Lemma r2_evt_F : SSHF.asan_set_shadow_00_contract_F ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c Q md : Z) (junk : list byte),
    a0 = Z_to_bv 64 0x9e800 -> s1 = Z_to_bv 64 A -> s2 = Z_to_bv 64 c ->
    s7 = Z_to_bv 64 md -> 0 <= md < 256 ->
    0 <= Q -> Q + 186 <= 2 ^ 64 ->
    ro_cells rsegs m c [C8 (Z_to_bv 64 11)] ->
    ro_cells rsegs m (A + 152) [C8 (Z_to_bv 64 Q)] ->
    (forall i, 0 <= i < 186 -> in_shadow (Q + i)) ->
    rw_cells rsegs m Q [CB 186 junk] ->
    asan_cells m -> ro_agree rsegs m ->
    RBY.rng_bytes RNG ->
    ExecF.rng RNG c 8 ->
    ExecF.rng RNG (A + 152) 8 ->
    ExecF.rng RNG IMGB.IMG_LO (IMGB.IMG_HI - IMGB.IMG_LO) ->
    ExecF.rng RNG (bv_unsigned sp - SSHF.ASAN_SET_SHADOW_K) SSHF.ASAN_SET_SHADOW_K ->
    ExecF.rng RNG Q 186 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x8152c) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 18 = Z_to_bv 64 (0x9e800 + 296 * ((md / 2) mod 11)) /\
         munch [(Q, Q + 186)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         rw_cells rsegs m' Q [CB 186 (repeat (Z_to_bv 8 0) 186)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814f8) fc None m (seg_rom rsegs)).
Proof.
  intros SH0 RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A c Q md junk -> -> -> -> Hmd HQ0 HQb RC R152 HQsh CHQ HAC HRO RBYT Rc R152r Rimg Rsp RQ.
  unfold SSHF.asan_set_shadow_00_contract_F, SSHF.asan_set_shadow_contract_F, SSH.ASAN_SET_SHADOW_00 in SH0.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  (* the 186 written bytes are shadow bytes, so none of them is at a read-only address *)
  assert (NR : forall i, 0 <= i < 186 -> ro_addr rsegs (wa (Q + i)) = false)
    by (intros i Hi; apply r2_shadow_not_ro; apply HQsh; lia).
  assert (CHQn : rw_cells rsegs (normalize rsegs m) Q [CB 186 junk]).
  { destruct CHQ as ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
    - exact (bytes_at_normalize rsegs m _ _ HRO Hb).
    - cbn [cells_size csize] in Hw |- *. rewrite Nat.add_0_r in Hw |- *.
      exact (wr_at_norm rsegs m _ Q (Z.of_nat 186) REL Hw (fun i Hi => NR i ltac:(cbn in Hi; lia))). }
  step. try if_true.
  step. step. try if_true.
  step. step. step. step. step.
  match goal with
  | |- context [Z_to_bv 64 (649216 + bv_unsigned (LinuxProcessSemantics.Riscv.Sem.mul_div ?o ?u ?v) * 296)] =>
      replace (Z_to_bv 64 (649216 + bv_unsigned (LinuxProcessSemantics.Riscv.Sem.mul_div o u v) * 296))
        with (Z_to_bv 64 (0x9e800 + 296 * ((md / 2) mod 11))) by r2_row_tac
  end.
  step. step.
  step.
  eapply ExecF.evtF_cut.
  { eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HRO).
    eapply SH0 with (junk := junk) (RNG := RNG); cbv zeta.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. intros i Hi.
      apply HQsh. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact CHQn.
    - exact (r2_ac_norm m HRO HAC).
    - apply mem_inv_normalize.
    - exact RBYT.
    - exact Rimg.
    - exact Rsp.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RQ. }
  intros ms' (s0' & PO & MR & RS). unfold SSH.asan_set_shadow_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MU & WM & MI' & RW').
  subst s0'.
  rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in MU, RW' by lia.
  replace (ret_pc (Z_to_bv 64 0x8152c)) with (Z_to_bv 64 0x8152c) in MR
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct ms' as [R' F' pc' svc' resv' fc' mem' rom'].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
  cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  assert (RO' : ro_agree rsegs mem') by exact (ro_agree_same rsegs m mem' HRO RS).
  apply ExecF.evtF_done. exists R', mem'.
  split; [unfold MS; subst; reflexivity|].
  subst R'.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m _ mem' m0' REL Hmem RS MU)|].
  split; [exact (wmono_rel rsegs m _ mem' m0' REL Hmem RS WM)|].
  split; [exact RO'|].
  destruct RW' as ((Hwf' & Hb') & Hw'). split; [split; [exact Hwf'|]|].
  - exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ Hmem) Hb').
  - exact (wr_at_rel rsegs mem' m0' _ _ Hmem Hw').
Qed.

(* R2.r2_evt's statement, with the callee's FOOTPRINT contract in the place of the plain one (the first premise);
   every rng premise of the twin is discharged by ExecF.rng_all, and rng_bytes holds of RNG_all. *)
Lemma r2_evt_of_F : SSHF.asan_set_shadow_00_contract_F ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c Q md : Z) (junk : list byte),
    a0 = Z_to_bv 64 0x9e800 -> s1 = Z_to_bv 64 A -> s2 = Z_to_bv 64 c ->
    s7 = Z_to_bv 64 md -> 0 <= md < 256 ->
    0 <= Q -> Q + 186 <= 2 ^ 64 ->
    ro_cells rsegs m c [C8 (Z_to_bv 64 11)] ->
    ro_cells rsegs m (A + 152) [C8 (Z_to_bv 64 Q)] ->
    (forall i, 0 <= i < 186 -> in_shadow (Q + i)) ->
    rw_cells rsegs m Q [CB 186 junk] ->
    asan_cells m -> ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x8152c) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 18 = Z_to_bv 64 (0x9e800 + 296 * ((md / 2) mod 11)) /\
         munch [(Q, Q + 186)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         rw_cells rsegs m' Q [CB 186 (repeat (Z_to_bv 8 0) 186)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814f8) fc None m (seg_rom rsegs)).
Proof.
  intros SH0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A c Q md junk E0 E1 E2 E7 Hmd HQ0 HQb RC R152 HQsh CHQ HAC HRO.
  pose proof (ro_cells_bound rsegs m c _ RC) as Hcb.
  pose proof (ro_cells_bound rsegs m (A + 152) _ R152) as HAb.
  cbn [cells_size csize Nat.add] in Hcb, HAb.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp0.
  unfold bv_modulus in Rsp0. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp0.
  eapply ExecF.evtF_evt, (r2_evt_F SH0 ExecF.RNG_all); try eassumption.
  - (* RNG_all is byte-wise (the one-line proof of asan_set_shadow_cF.v's own corollary) *)
    intros ? ? _ _ _. exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; cbv [IMGB.IMG_LO IMGB.IMG_HI]; lia.
  - apply ExecF.rng_all; unfold SSHF.ASAN_SET_SHADOW_K; lia.
  - apply ExecF.rng_all; lia.
Qed.

(* The pin: r2_evt_of_F differs from R2.r2_evt only in the first premise, which names the _F contract in place of
   the plain one; both are checked by name, the rest term for term. *)
Example r2_evt_of_F_verbatim : True.
Proof.
  lazymatch type of R2.r2_evt with ?P -> ?A =>
  lazymatch type of r2_evt_of_F with ?Q -> ?B =>
    constr_eq P SSH.asan_set_shadow_00_contract;
    constr_eq Q SSHF.asan_set_shadow_00_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.
