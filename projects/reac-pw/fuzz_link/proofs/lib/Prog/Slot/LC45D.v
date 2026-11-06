(* Piece d of the C45 brief: op_decide's segments without a leaf call (fuzz_link.c:744-752, plain image,
   link/ct/dis/plain/LLVMFuzzerTestOneInput.s lines 150-172).

     c45_d0  0x13a9c addi a0, sp, 0x40 ; addi a1, sp, 0x78 ; jal text_of     -> c45_13aa4
     c45_d1  0x13aa8 mv s2, a0 ; addi a0, sp, 0x40 ; addi a1, sp, 0x50 ; jal text_of -> c45_13ab4
     c45_d3  0x13aec ld a0, 0x50(sp) ; jal free                          -> c45_13af0
     c45_d4  0x13af4 (no instruction): the buffers merged back, c45_kmg at i + 1 -> c45_end C45_END_D

   None of them writes memory, so each post carries `seg_fp` with the empty window (d_fp_refl). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC45Defs LC45Call LC45DLib.
Local Open Scope Z_scope.

Lemma c45_d0 : forall E i gp ms, lenv_ok E -> c45_disp E i gp 4 ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_13aa4 E i gp))) ms.
Proof.
  intros E i gp ms OK H.
  destruct H as (ra & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc & m & P & N
    & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & HI & HN & FR & CU & B1 & B2 & KMG & KEEP & MACH).
  subst ms. cbn [ms_mem].
  destruct (d_split8 m (c45_sp E + FO_B256) 256 j2 ltac:(lia) B2) as (w2 & j2' & W2 & B3).
  change (op_pc 4) with L_OP4. unfold c45_R, wz, L_OP4.
  do 3 step.
  apply evt_done. apply c45_eqv_cl_of. unfold c45_post. split; [|apply d_fp_refl].
  exists t0, t1, t2, (wz P), a3, a4, a5, a6, a7, (wz N), s3, s4, t3, t4, t5, t6, F, fc, m, (P + 1), (N - 1),
    kbs, mbs, gbs, j0, j1, j2', w2.
  split; [reflexivity|].
  split; [exact FC|]. split; [exact HI|]. split; [exact FR|]. split; [apply d_cur_next; assumption|].
  split; [exact B1|]. split; [exact W2|]. split; [exact B3|].
  split; [exact KMG|]. split; [exact KEEP|]. exact MACH.
Qed.

Lemma c45_d1 : forall E i gp own1 ms, lenv_ok E -> c45_13aa8 E i gp own1 ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_13ab4 E i gp own1))) ms.
Proof.
  intros E i gp own1 ms OK H.
  destruct H as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc
    & m & P & N & s1 & kbs & mbs & gbs & j0 & j1 & j2 & t1v & EQ & FC & HI & FR & CU & B1 & B2 & B3
    & N1 & C1 & L1 & KMG & KEEP & MACH).
  subst ms. cbn [ms_mem].
  destruct (d_split8 m (c45_sp E + FO_B40) 40 j1 ltac:(lia) B1) as (w1 & j1' & W1 & B4).
  unfold c45_R, wz, C45_TO1_RA.
  do 4 step.
  apply evt_done. apply c45_eqv_cl_of. unfold c45_post. split; [|apply d_fp_refl].
  exists t0, t1, t2, a2, a3, a4, a5, a6, a7, s3, s4, t3, t4, t5, t6, F, fc, m, P, N, s1,
    kbs, mbs, gbs, j0, j1', j2, t1v, w1.
  split; [reflexivity|].
  split; [exact FC|]. split; [exact HI|]. split; [exact FR|]. split; [exact CU|].
  split; [exact W1|]. split; [exact B4|]. split; [exact B2|]. split; [exact B3|].
  split; [exact N1|]. split; [exact C1|]. split; [exact L1|].
  split; [exact KMG|]. split; [exact KEEP|]. exact MACH.
Qed.

Lemma c45_d3 : forall E i gp own1 own2 ms, lenv_ok E -> c45_13aec E i gp own1 own2 ms ->
  evt rsegs (eqv_cl (c45_post E (ms_mem ms) (c45_13af0 E i gp own1 own2))) ms.
Proof.
  intros E i gp own1 own2 ms OK H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6
    & F & fc & m & P & N & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & HI & FR & CU & B1 & B2 & B3 & B4
    & KMG & KEEP & MACH).
  subst ms. cbn [ms_mem].
  assert (B1x : rw_cells rsegs m (c45_sp E + 80) [C8 (wz own2)]) by exact B1.
  unfold c45_R, wz, C45_FR1_RA.
  do 2 step.
  apply evt_done. apply c45_eqv_cl_of. unfold c45_post. split; [|apply d_fp_refl].
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, t3, t4, t5, t6, F, fc, m, P, N,
    kbs, mbs, gbs, j0, j1, j2.
  split; [reflexivity|].
  split; [exact FC|]. split; [exact HI|]. split; [exact FR|]. split; [exact CU|].
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
  split; [exact KMG|]. split; [exact KEEP|]. exact MACH.
Qed.

Lemma c45_d4 : forall E i gp own1 own2 ms, lenv_ok E -> c45_13af4 E i gp own1 own2 ms ->
  c45_end E i gp C45_END_D ms.
Proof.
  intros E i gp own1 own2 ms OK H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6
    & F & fc & m & P & N & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & HI & FR & CU & B1 & B2 & B3 & B4
    & KMG & KEEP & MACH).
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, t3, t4, t5, t6, F, fc, m, P, N,
    kbs, mbs, gbs, j0, (le8 (wz own2) ++ j1), (le8 (wz own1) ++ j2).
  split; [exact EQ|].
  split; [exact FC|]. split; [lia|]. split; [exact FR|]. split; [exact CU|].
  split; [exact (d_join8 _ _ _ _ _ B1 B2)|]. split; [exact (d_join8 _ _ _ _ _ B3 B4)|].
  split; [apply d_kmg_next; [lia | exact KMG]|]. split; [exact KEEP|]. exact MACH.
Qed.

Print Assumptions c45_d0.
Print Assumptions c45_d1.
Print Assumptions c45_d3.
Print Assumptions c45_d4.
