(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk D_iface D_defs Bi_fktw Bi_fkweak Bi_iface2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Po_rows Po_iface Po_csels_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CSELS_CUT.
Variable RT : rt_sig.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
          (usp lo : Z) (m : mem) (size dir p1 p2 : Z) (ras : list Z).

(* [comment removed for export] *)
Definition csels_PF : Z -> Prop :=
  fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(p1, p1 + 8); (p2, p2 + 8)] a.

(* [comment removed for export] *)
Definition csels_ctx : Prop :=
  fdfs_only PMc /\ mat_stable PMc /\ ART RT Σ m
  /\ rt_sp0 RT Σ - 8388608 <= lo /\ lo + (65536 + 1024 * 6) <= usp /\ 0 <= lo
  /\ usp + 16 <= 140737488355328 /\ usp mod 16 = 0 /\ usp <= rt_sp0 RT Σ
  /\ Z.of_nat (length (rt_frames RT Σ)) + 2 <= Z.of_nat FRAMES_MAX /\ Z.of_nat (length (rt_live RT Σ)) + 16 <= LIVE_MAX
  /\ 2 <= rt_credit RT Σ /\ (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n)
  /\ ((size = 30 /\ dir = L_HORIZ) \/ (size = 8 /\ dir = L_VERT))
  /\ optrF RT Σ m p1 8 /\ optrF RT Σ m p2 8 /\ (p1 + 8 <= p2 \/ p2 + 8 <= p1)
  /\ po_rows e_selectComposableSels ra ras.

(* [comment removed for export] *)
Definition csels_Q : config -> Prop :=
  fun c => exists (Σ' : rts RT) (sel1 sel2 : Z) (sv1 sv2 : selv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' (Z_to_bv 64 usp) lo /\ keepsL RT (rt_live RT Σ) Σ (Z_to_bv 64 usp) [(p1, p1 + 8); (p2, p2 + 8)] m m'
          /\ rw_cells asegs m' p1 [C8 (Z_to_bv 64 sel1)] /\ rw_cells asegs m' p2 [C8 (Z_to_bv 64 sel2)]
          /\ sel_obj (rt_live RT Σ') m' sel1 sv1 /\ sel_obj (rt_live RT Σ') m' sel2 sv2
          /\ (size = 30 -> brick_h6 sv1 /\ comb_h30 sv2) /\ (size = 8 -> brick_v4 sv1 /\ comb_v8 sv2)
          /\ List.NoDup (sel_chunks sel1 sv1 ++ sel_chunks sel2 sv2)) c
       /\ rt_live RT Σ' = sel_new_live sel2 sv2 (sel_new_live sel1 sv1 (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ'.

(* [comment removed for export] *)
Definition csels_sh00 (mc : mem) (fr : Z) : Prop :=
  rw_cells asegs mc (fr / 8 + 2147450884) [CB 128 (repeat (Z_to_bv 8 0) 128)]
  /\ rw_cells asegs mc (fr / 8 + 2147451028) [CB 128 (repeat (Z_to_bv 8 0) 128)]
  /\ rw_cells asegs mc (fr / 8 + 2147451172) [CB 128 (repeat (Z_to_bv 8 0) 128)]
  /\ rw_cells asegs mc (fr / 8 + 2147451316) [CB 128 (repeat (Z_to_bv 8 0) 128)].

(* [comment removed for export] *)
Definition csels_cut1_0 (QF : config -> Prop) : Prop :=
  forall (S1 : rts RT) (mc : mem) (fr : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (j0 j1 j2 j3 jh : list byte)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ART RT S1 mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -256) -> LIBH mc -> io_ssp mc ->
    rt_frames RT S1 = (fr, 7%nat) :: rt_frames RT Σ -> rt_live RT S1 = rt_live RT Σ -> rt_sp0 RT S1 = rt_sp0 RT Σ ->
    rt_credit RT S1 = rt_credit RT Σ - 1 ->
    wmono asegs m mc -> agree_on csels_PF m mc -> fs_agree F F1 ->
    accok [] (rt_frames RT Σ) mc p1 8 -> accok [] (rt_frames RT Σ) mc p2 8 ->
    rw_cells asegs mc p1 [C8 (Z_to_bv 64 0)] -> rw_cells asegs mc p2 [C8 (Z_to_bv 64 0)] ->
    rw_cells asegs mc (usp + -256)
      [CB 16 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (usp + -44)); C8 (Z_to_bv 64 (usp + -48));
       C8 (Z_to_bv 64 (fr / 8 + 2147451028)); C8 (Z_to_bv 64 (fr / 8 + 2147450884)); C8 (Z_to_bv 64 fr); CB 16 j1; C8 (Z_to_bv 64 fr); CB 16 j2;
       C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 (Z_to_bv 64 p1); C8 (Z_to_bv 64 dir); C8 (Z_to_bv 64 p2);
       C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 1408308); CB 8 j3; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mc fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 184636); C8 (Z_to_bv 64 1408796); CB 8 jh] ->
    wr_at asegs mc (fr + 32) 4608 -> csels_sh00 mc fr ->
    cps asegs (ASTA RT S1 PMc (eq (entry_st (Z_to_bv 64 1409436) (Z_to_bv 64 (usp + -256)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 (usp + -48)) (Z_to_bv 64 (usp + -256)) a0 a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 (fr / 8 + 2147450884)) (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 (fr / 8 + 2147451028)) s5
                                    (Z_to_bv 64 2147450880) (Z_to_bv 64 (fr / 8 + 2147451172)) s8 (Z_to_bv 64 (fr / 8 + 2147451316))
                                    (Z_to_bv 64 size) (Z_to_bv 64 fr) t3 t4 t5 t6 F1 fc1 1409436 mc))) QF.

(* [comment removed for export] *)
Definition csels_cut1_16 (QF : config -> Prop) : Prop :=
  forall (S1 : rts RT) (mc : mem) (fr : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (j0 j1 j3 jh : list byte)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ART RT S1 mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -240) -> LIBH mc -> io_ssp mc ->
    rt_frames RT S1 = (fr, 7%nat) :: rt_frames RT Σ -> rt_live RT S1 = rt_live RT Σ -> rt_sp0 RT S1 = rt_sp0 RT Σ ->
    rt_credit RT S1 = rt_credit RT Σ - 1 ->
    wmono asegs m mc -> agree_on csels_PF m mc -> fs_agree F F1 ->
    accok [] (rt_frames RT Σ) mc p1 8 -> accok [] (rt_frames RT Σ) mc p2 8 ->
    rw_cells asegs mc p1 [C8 (Z_to_bv 64 0)] -> rw_cells asegs mc p2 [C8 (Z_to_bv 64 0)] ->
    rw_cells asegs mc (usp + -240)
      [C8 (Z_to_bv 64 0); CB 16 j0; C8 (Z_to_bv 64 (usp + -44)); C8 (Z_to_bv 64 (usp + -48));
       C8 (Z_to_bv 64 (fr / 8 + 2147451028)); C8 (Z_to_bv 64 (fr / 8 + 2147450884)); C8 (Z_to_bv 64 fr); CB 16 j1; C8 (Z_to_bv 64 fr);
       C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 (Z_to_bv 64 p1); C8 (Z_to_bv 64 dir); C8 (Z_to_bv 64 p2);
       C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 1408308); CB 8 j3; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mc fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 184636); C8 (Z_to_bv 64 1408796); CB 8 jh] ->
    wr_at asegs mc (fr + 32) 4608 -> csels_sh00 mc fr ->
    cps asegs (ASTA RT S1 PMc (eq (entry_st (Z_to_bv 64 1409436) (Z_to_bv 64 (usp + -240)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 (usp + -48)) (Z_to_bv 64 (usp + -240)) a0 a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 (fr / 8 + 2147450884)) (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 (fr / 8 + 2147451028)) s5
                                    (Z_to_bv 64 2147450880) (Z_to_bv 64 (fr / 8 + 2147451172)) s8 (Z_to_bv 64 (fr / 8 + 2147451316))
                                    (Z_to_bv 64 size) (Z_to_bv 64 fr) t3 t4 t5 t6 F1 fc1 1409436 mc))) QF.

(* [comment removed for export] *)
Definition csels_cut3 (QF : config -> Prop) : Prop :=
  forall (S3 : rts RT) (m3 : mem) (F3 : bvmap 5 word) (fc3 : bv 32) (f1 f2 : Z)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ART RT S3 m3 -> mem_inv asegs m3 -> stk asegs m3 lo (usp + -48) -> LIBH m3 -> io_ssp m3 ->
    rt_frames RT S3 = rt_frames RT Σ -> rt_live RT S3 = rt_live RT Σ -> rt_sp0 RT S3 = rt_sp0 RT Σ ->
    rt_credit RT Σ - 1 <= rt_credit RT S3 ->
    wmono asegs m m3 -> agree_on csels_PF m m3 -> fs_agree F F3 ->
    accok [] (rt_frames RT Σ) m3 p1 8 -> accok [] (rt_frames RT Σ) m3 p2 8 ->
    rw_cells asegs m3 p1 [C8 (Z_to_bv 64 0)] -> rw_cells asegs m3 p2 [C8 (Z_to_bv 64 0)] ->
    ((size = 30 /\ f1 = 6 /\ f2 = 5) \/ (size = 8 /\ f1 = 4 /\ f2 = 2)) ->
    rw_cells asegs m3 (usp + -48) [C4 (Z_to_bv 64 f2); C4 (Z_to_bv 64 f1); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    cps asegs (ASTA RT S3 PMc (eq (entry_st (Z_to_bv 64 1408308) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 2147450880) (Z_to_bv 64 p2) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 dir) (Z_to_bv 64 p1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F3 fc3 1408308 m3))) QF.
End CSELS_CUT.
