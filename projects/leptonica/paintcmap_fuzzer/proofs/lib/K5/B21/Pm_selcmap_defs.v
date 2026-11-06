(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Pm_iface D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

Section SELC_DEFS.
Variable RT : rt_sig.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (pix b : Z) (v : pixv) (cv : cmapv) (fr : Z).

(* [comment removed for export] *)
Definition selc_PFW : Z -> Prop := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside (pm_fp v cv) a.

(* [comment removed for export] *)
Definition selc_post : config -> Prop :=
  fun c => exists (Σ' : rts RT) (rv : word) (cv' : cmapv),
     ASTA RT Σ' PMc (fun ms => exists m', ret_st ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
        /\ ((ART RT Σ' m' /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo usp) /\ LIBH m' /\ io_ssp m')
        /\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) usp (pm_fp v cv) m m'
        /\ pix_obj (rt_live RT Σ') m' pix v cv' /\ c_arr cv' = c_arr cv /\ c_depth cv' = c_depth cv /\ c_nalloc cv' = c_nalloc cv) c
     /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
     /\ rt_credit RT Σ - 4 <= rt_credit RT Σ'.

(* [comment removed for export] *)
Definition selc_ctx : Prop :=
  fdfs_only PMc /\ mat_stable PMc /\ ART RT Σ m
  /\ rt_sp0 RT Σ - 8388608 <= lo /\ lo + (65536 + 1024 * 6) <= usp /\ 0 <= lo
  /\ usp + 16 <= 140737488355328 /\ usp mod 16 = 0 /\ usp <= rt_sp0 RT Σ
  /\ (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n)
  /\ p_cmap v <> 0 /\ p_data v <> 0 /\ (p_d v = 1 \/ p_d v = 2 \/ p_d v = 4 \/ p_d v = 8) /\ b <> pix.

(* [comment removed for export] *)
Definition selc_fshadow (js : list byte) : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); CB 12 js].


(* [comment removed for export] *)
Definition selc_cut_stmt_0 : Prop :=
  forall (S : rts RT) (mc : mem) (cvx : cmapv) (idx : Z) (j0 j1 j2 f0 f1 js : list byte)
         (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r21 r22 r23 r24 r27 r28 r29 r30 r31 : word) F' fc',
    ART RT S mc -> mem_inv asegs mc -> wmono asegs m mc -> stk asegs mc lo (usp + -192) ->
    rw_cells asegs mc (usp + -192)
      [C8 (Z_to_bv 64 0); CB 16 j0;
       C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 fr); CB 8 j1; C8 (Z_to_bv 64 (fr + 128)); C8 (Z_to_bv 64 2); CB 16 j2;
       C8 (Z_to_bv 64 fr);
       C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mc fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 118145); C8 (Z_to_bv 64 604940); CB 104 f0] ->
    rw_cells asegs mc (fr + 128) [C4 (Z_to_bv 64 idx)] -> rw_cells asegs mc (fr + 132) [CB 116 f1] ->
    rw_cells asegs mc (fr / 8 + 2147450880) (selc_fshadow js) ->
    LIBH mc -> io_ssp mc -> agree_on selc_PFW m mc ->
    rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_live RT S = rt_live RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_credit RT Σ - 2 <= rt_credit RT S ->
    pix_obj (rt_live RT Σ) mc pix v cvx -> c_arr cvx = c_arr cv -> c_depth cvx = c_depth cv -> c_nalloc cvx = c_nalloc cv ->
    box_obj (rt_live RT Σ) mc b 278 35 122 50 -> 0 <= idx <= 256 ->
    cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
                                    r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 (p_d v)) r21 r22
                                    (Z_to_bv 64 2147450880) r23 r24 (Z_to_bv 64 pix) r27 r28 r29 r30 r31 F' fc' 0x93e14 mc)))
        selc_post.

(* [comment removed for export] *)
Definition selc_cut_stmt_16 : Prop :=
  forall (S : rts RT) (mc : mem) (cvx : cmapv) (idx : Z) (j0 j1 j2 j3 f0 f1 js : list byte)
         (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r21 r22 r23 r24 r27 r28 r29 r30 r31 : word) F' fc',
    ART RT S mc -> mem_inv asegs mc -> wmono asegs m mc -> stk asegs mc lo (usp + -208) ->
    rw_cells asegs mc (usp + -208)
      [CB 16 j0; C8 (Z_to_bv 64 0);
       C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 fr); CB 8 j1; C8 (Z_to_bv 64 (fr + 128)); C8 (Z_to_bv 64 2); CB 16 j2;
       C8 (Z_to_bv 64 fr);
       CB 16 j3;
       C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mc fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 118145); C8 (Z_to_bv 64 604940); CB 104 f0] ->
    rw_cells asegs mc (fr + 128) [C4 (Z_to_bv 64 idx)] -> rw_cells asegs mc (fr + 132) [CB 116 f1] ->
    rw_cells asegs mc (fr / 8 + 2147450880) (selc_fshadow js) ->
    LIBH mc -> io_ssp mc -> agree_on selc_PFW m mc ->
    rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_live RT S = rt_live RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_credit RT Σ - 2 <= rt_credit RT S ->
    pix_obj (rt_live RT Σ) mc pix v cvx -> c_arr cvx = c_arr cv -> c_depth cvx = c_depth cv -> c_nalloc cvx = c_nalloc cv ->
    box_obj (rt_live RT Σ) mc b 278 35 122 50 -> 0 <= idx <= 256 ->
    cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208))
                                    r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 (p_d v)) r21 r22
                                    (Z_to_bv 64 2147450880) r23 r24 (Z_to_bv 64 pix) r27 r28 r29 r30 r31 F' fc' 0x93e14 mc)))
        selc_post.
End SELC_DEFS.
