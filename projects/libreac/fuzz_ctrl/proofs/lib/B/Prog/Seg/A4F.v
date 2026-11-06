(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/LibA/StepF0.v; 216 of its 233 lines of code are new or changed and 578 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/A4.v a4_evt (:128) at a working branch 3803efccea0
     (blob 5a3c42be8171de7d0abe8490e256eb0ac138b2ed);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: a4_evt_of_F (evtF_evt + rng_all) re-derives the source statement in the lib.Lib vocabulary;
     a4_evt_of_F_is_source (type of A4.a4_evt, re-derived from a4_evt_of_F through the shared cell
     bridge lib/B/Tk/UL/CellBridge.v and the UL engine bridge ul_evt_of_evt) is the source statement
     itself.
   The run (v1.9 [0x81220, 0x81544], 201 instructions, two exits) has NO call, so it is one `_F`.
   Bridge input only: no top, no W_cutfree_ok, no cut-free twin, no LSCPS join.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require A4.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require CellBridge.
(* Last: StepF's step / if_true_by / if_false_by / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* A4.v's store hook, on the evtF goal (pilot fix (2)): a byte store of a register whose value is not a
   literal (the shadow stores `sb s4/s5,k(s3)`). le1 v is [Z_to_bv 8 (bv_unsigned v)] by conversion, so one
   branch serves both a register value and a literal. *)
Local Ltac norm_lit_store_bytes ::=
  try (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
           change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
       end).

(* One cell of a block of cells, read as a byte block at its own offset (A4.a4_cell_bytes over lib.Lib cells). *)
Lemma a4F_cell_bytes : forall m A cs k c bs,
  rw_cells rsegs m A cs -> cell_at cs k = Some c -> cbytes c = bs ->
  bytes_at rsegs m (A + Z.of_nat k) bs.
Proof.
  intros m A cs k c bs [[Hwf Hb] _] Hat <-.
  destruct (cell_at_split cs k c c Hat) as (pre & post & -> & Hsz & _).
  apply cells_wf_app in Hwf. destruct Hwf as [Hwfp Hwfc]. cbn in Hwfc. destruct Hwfc as [Hwfc Hwfs].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite (cells_bytes_length pre Hwfp), Hsz in Hb.
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Local Ltac a4F_bv :=
  first [ reflexivity
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn; Z.div_mod_to_equations; lia ].

Local Ltac a4F_spill FR k :=
  apply (a4F_cell_bytes _ _ _ k _ _ FR ltac:(cells_cbv; reflexivity));
  first [ reflexivity
        | cbn [cbytes]; f_equal; apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn; lia
        | cbn [cbytes]; f_equal; apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn;
          Z.div_mod_to_equations; lia ].

Local Ltac a4F_at FR base :=
  lazymatch goal with
  | |- bytes_at _ _ (bv_unsigned ?s + ?off) _ =>
      let k := eval vm_compute in (Z.to_nat (off - base)) in
      let kz := eval vm_compute in (Z.of_nat k) in
      replace (bv_unsigned s + off) with (bv_unsigned s + base + Z.of_nat k)
        by (change (Z.of_nat k) with kz; lia);
      a4F_spill FR k
  end.

(* The footprint twin of A4.a4_evt. The write set is the whole access set: the 137 shadow bytes
   [s3 + 255, s3 + 392) and the 264 spill bytes [s1 + 56, s1 + 320); the run reads no data and has no
   instrumented check. *)
Lemma a4_evt_F : forall (RNG : footprint)
  (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk1 junk2 : list byte),
    rw_cells rsegs m (bv_unsigned s3 + 255) [CB 137 junk1] ->
    rw_cells rsegs m (bv_unsigned s1 + 56) [CB 264 junk2] ->
    bv_unsigned s3 + 392 <= bv_unsigned s1 + 56 ->
    rng RNG (bv_unsigned s3 + 255) 137 ->
    rng RNG (bv_unsigned s1 + 56) 264 ->
    evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' a6' a7' s4' pc' : word) (m' : word -> option byte) (cs1 cs2 : list cell),
         ms' = MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6' a7' s2 s3 s4' s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F pc' fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 255, bv_unsigned s3 + 392); (bv_unsigned s1 + 56, bv_unsigned s1 + 320)] m m' /\
         wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned s3 + 255) cs1 /\ cells_size cs1 = 137%nat /\
         rw_cells rsegs m' (bv_unsigned s1 + 56) cs2 /\ cells_size cs2 = 264%nat /\
         ((pc' = Z_to_bv 64 0x82f2c /\ 2 ^ 26 <= bv_unsigned s2) \/
          (pc' = Z_to_bv 64 0x81548 /\ bv_unsigned s2 < 2 ^ 26 /\
           bytes_at rsegs m' (bv_unsigned s3 + 328) [Z_to_bv 8 6] /\
           s4' = Z_to_bv 64 (bv_unsigned s9 + 2656) /\
           a0' = Z_to_bv 64 6 /\ a1' = Z_to_bv 64 1 /\ a2' = Z_to_bv 64 (bv_unsigned s9 + 2624) /\
           a6' = Z_to_bv 64 (bv_unsigned s9 + 32) /\ a7' = Z_to_bv 64 (bv_unsigned s9 + 64) /\
           bytes_at rsegs m' (bv_unsigned s1 + 144) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2176))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 112) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2256))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 312) (le8 (Z_to_bv 64 (bv_unsigned s9 + 544))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 264) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2624))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 56) (le8 (Z_to_bv 64 (bv_unsigned s9 + 3040))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 184) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2368))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 176) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2688))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 208) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2768))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 96) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2560))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 120) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2528))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 240) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2448))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 232) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2464))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 224) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2496))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 64) (le8 (Z_to_bv 64 (bv_unsigned s9 + 3056))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 136) (le8 (Z_to_bv 64 (bv_unsigned s9 + 160))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 280) (le8 (Z_to_bv 64 (bv_unsigned s9 + 176))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 168) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2880))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 192) (le8 (Z_to_bv 64 (bv_unsigned s9 + 528))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 200) (le8 (Z_to_bv 64 (bv_unsigned s9 + 336))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 216) (le8 (Z_to_bv 64 (bv_unsigned s9 + 448))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 104) (le8 (Z_to_bv 64 (bv_unsigned s9 + 128))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 288) (le8 (Z_to_bv 64 (bv_unsigned s9 + 256))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 296) (le8 (Z_to_bv 64 (bv_unsigned s9 + 304))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 304) (le8 (Z_to_bv 64 (bv_unsigned s9 + 272))))))
      (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81220) fc None m (seg_rom rsegs)).
Proof.
  intros RNG rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk1 junk2 FRsh FRsp HD Gsh Gsp.
  pose proof (munch_refl [(bv_unsigned s3 + 255, bv_unsigned s3 + 392);
                          (bv_unsigned s1 + 56, bv_unsigned s1 + 320)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2^64) in R3.
  pose proof (bv_unsigned_in_range 64 s1) as R1. change (bv_modulus 64) with (2^64) in R1.
  pose proof (bv_unsigned_in_range 64 s2) as R2. change (bv_modulus 64) with (2^64) in R2.
  pose proof (rw_cells_bound _ _ _ _ FRsh) as HBsh. cbn [cells_size csize Nat.add] in HBsh.
  pose proof (rw_cells_bound _ _ _ _ FRsp) as HBsp. cbn [cells_size csize Nat.add] in HBsp.
  (* 0x81220-0x8141c: 128 shadow stores; 0x81420 li a0,-13; 0x81424 srli a1,s2,26; 0x81428-0x81448: 9 more *)
  do 139 step.
  destruct (Z_lt_ge_dec (bv_unsigned s2) (2 ^ 26)) as [Hlt|Hge].
  - (* 0x8144c beqz a1 taken; 0x81454-0x81544 *)
    step. if_true_by (A4.a4_cond_lt (bv_unsigned s2) ltac:(lia)).
    do 61 step.
    apply evtF_done. cbn beta.
    eexists _, _, _, _, _, _, _, _, _, _, _.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [exact FRsh|]. split; [cbn [cells_size csize]; reflexivity|].
    split; [exact FRsp|]. split; [cbn [cells_size csize]; reflexivity|].
    right. split; [reflexivity|]. split; [exact Hlt|].
    split; [a4F_at FRsh 255|].
    do 6 (split; [a4F_bv|]).
    do 23 (split; [a4F_at FRsp 56|]).
    a4F_at FRsp 56.
  - (* 0x8144c beqz a1 not taken; 0x81450 j 0x82f2c *)
    step. if_false_by (A4.a4_cond_ge (bv_unsigned s2) ltac:(lia)).
    step.
    apply evtF_done. cbn beta.
    eexists _, _, _, _, _, _, _, _, _, _, _.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [exact FRsh|]. split; [cbn [cells_size csize]; reflexivity|].
    split; [exact FRsp|]. split; [cbn [cells_size csize]; reflexivity|].
    left. split; [reflexivity | lia].
Qed.

(* ---- the compare lemma (the auditor's check) ----
   A4.a4_evt states the run with the lib.B.Tk.UL copies of the engine and of the memory words (A4.v
   imports lib.B.Tk.UL Exec / Step / Cells after lib.Lib Mem / Frame, and its statement is before the
   lib.Lib re-import that R5.v has): UL.Cells.cell is a separate inductive copy of lib.Lib's, so the two
   statements are not convertible and the identity needs a cell translation (lib/B/Tk/UL/CellBridge.v).
   a4_evt_of_F is the SAME statement in the lib.Lib copies (which is what the cgif-form walk consumes):
   the UL engine and the lib.Lib engine have the same [mstep]
   (`ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'`), and the memory words
   (munch, wmono, bytes_at, rw_cells, cells_size) are the same definitions in the two copies.
   The footprint is erased with RNG_all: evtF_evt, both rng premises by rng_all. *)
Lemma a4_evt_of_F : forall
  (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk1 junk2 : list byte),
    rw_cells rsegs m (bv_unsigned s3 + 255) [CB 137 junk1] ->
    rw_cells rsegs m (bv_unsigned s1 + 56) [CB 264 junk2] ->
    bv_unsigned s3 + 392 <= bv_unsigned s1 + 56 ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a6' a7' s4' pc' : word) (m' : word -> option byte) (cs1 cs2 : list cell),
         ms' = MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6' a7' s2 s3 s4' s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F pc' fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 255, bv_unsigned s3 + 392); (bv_unsigned s1 + 56, bv_unsigned s1 + 320)] m m' /\
         wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned s3 + 255) cs1 /\ cells_size cs1 = 137%nat /\
         rw_cells rsegs m' (bv_unsigned s1 + 56) cs2 /\ cells_size cs2 = 264%nat /\
         ((pc' = Z_to_bv 64 0x82f2c /\ 2 ^ 26 <= bv_unsigned s2) \/
          (pc' = Z_to_bv 64 0x81548 /\ bv_unsigned s2 < 2 ^ 26 /\
           bytes_at rsegs m' (bv_unsigned s3 + 328) [Z_to_bv 8 6] /\
           s4' = Z_to_bv 64 (bv_unsigned s9 + 2656) /\
           a0' = Z_to_bv 64 6 /\ a1' = Z_to_bv 64 1 /\ a2' = Z_to_bv 64 (bv_unsigned s9 + 2624) /\
           a6' = Z_to_bv 64 (bv_unsigned s9 + 32) /\ a7' = Z_to_bv 64 (bv_unsigned s9 + 64) /\
           bytes_at rsegs m' (bv_unsigned s1 + 144) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2176))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 112) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2256))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 312) (le8 (Z_to_bv 64 (bv_unsigned s9 + 544))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 264) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2624))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 56) (le8 (Z_to_bv 64 (bv_unsigned s9 + 3040))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 184) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2368))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 176) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2688))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 208) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2768))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 96) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2560))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 120) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2528))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 240) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2448))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 232) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2464))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 224) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2496))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 64) (le8 (Z_to_bv 64 (bv_unsigned s9 + 3056))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 136) (le8 (Z_to_bv 64 (bv_unsigned s9 + 160))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 280) (le8 (Z_to_bv 64 (bv_unsigned s9 + 176))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 168) (le8 (Z_to_bv 64 (bv_unsigned s9 + 2880))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 192) (le8 (Z_to_bv 64 (bv_unsigned s9 + 528))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 200) (le8 (Z_to_bv 64 (bv_unsigned s9 + 336))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 216) (le8 (Z_to_bv 64 (bv_unsigned s9 + 448))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 104) (le8 (Z_to_bv 64 (bv_unsigned s9 + 128))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 288) (le8 (Z_to_bv 64 (bv_unsigned s9 + 256))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 296) (le8 (Z_to_bv 64 (bv_unsigned s9 + 304))) /\
           bytes_at rsegs m' (bv_unsigned s1 + 304) (le8 (Z_to_bv 64 (bv_unsigned s9 + 272))))))
      (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81220) fc None m (seg_rom rsegs)).
Proof.
  intros rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk1 junk2 FRsh FRsp HD.
  pose proof (rw_cells_bound _ _ _ _ FRsh) as HBsh. cbn [cells_size csize Nat.add] in HBsh.
  pose proof (rw_cells_bound _ _ _ _ FRsp) as HBsp. cbn [cells_size csize Nat.add] in HBsp.
  (* the lib.Lib copy of the run; the UL copy is A4.a4_evt itself *)
  apply (evtF_evt rsegs RNG_all).
  apply (a4_evt_F RNG_all rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m junk1 junk2 FRsh FRsp HD);
    apply rng_all; lia.
Qed.


(* ---- the UL bridge: the source statement A4.a4_evt itself ----
   Everything in A4.a4_evt except the cells is the same definition in the two copies (MS, mkR, munch,
   wmono, bytes_at, cells_at, wr_at, seg_rom, mstep: identical bodies, so convertible). The cells are
   two distinct inductives with the same five constructors; the shared file lib/B/Tk/UL/CellBridge.v
   translates them (ul_cell_lib / lib_cell_ul) and carries cells_size and rw_cells across. *)
Module CBR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.CellBridge.
Module ULE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.
(* The engine bridge, as in R5F.v: the two [mstep]s are the same definition. *)
Lemma ul_msteps_of_msteps : forall ms ms', msteps rsegs ms ms' -> ULE.msteps rsegs ms ms'.
Proof.
  intros ms ms' H.
  induction H as [ms0|ms0 ms1 ms2 Hst Hs IH]; [apply ULE.msteps_refl|].
  eapply ULE.msteps_cons; [|exact IH]. destruct Hst as [HA HB]. split; [exact HA | exact HB].
Qed.

Lemma ul_evt_of_evt : forall (Q : machine_state -> Prop) ms, evt rsegs Q ms -> ULE.evt rsegs Q ms.
Proof.
  intros Q ms (ms1 & H & HQ). exists ms1. split; [exact (ul_msteps_of_msteps _ _ H) | exact HQ].
Qed.

(* The source statement itself: the type is A4.a4_evt's, taken from A4.a4_evt. *)
Lemma a4_evt_of_F_is_source : ltac:(let T := type of A4.a4_evt in exact T).
Proof.
  intros rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk1 junk2 FRsh FRsp HD.
  apply ul_evt_of_evt.
  eapply evt_mono.
  - apply (a4_evt_of_F rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m junk1 junk2).
    + exact (CBR.rw_cells_ul_lib _ _ _ _ FRsh).
    + exact (CBR.rw_cells_ul_lib _ _ _ _ FRsp).
    + exact HD.
  - intros ms' HQ.
    destruct HQ as (a0' & a1' & a2' & a3' & a6' & a7' & s4' & pc' & m' & cs1 & cs2 &
                    Hms & HMU & HWM & HR1 & HS1 & HR2 & HS2 & Hex).
    exists a0', a1', a2', a3', a6', a7', s4', pc', m',
      (map CBR.lib_cell_ul cs1), (map CBR.lib_cell_ul cs2).
    split; [exact Hms|].
    split; [exact HMU|]. split; [exact HWM|].
    split; [exact (CBR.rw_cells_lib_ul _ _ _ _ HR1)|].
    split; [rewrite CBR.cells_size_lib_cell_ul; exact HS1|].
    split; [exact (CBR.rw_cells_lib_ul _ _ _ _ HR2)|].
    split; [rewrite CBR.cells_size_lib_cell_ul; exact HS2|].
    exact Hex.
Qed.
