(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Km_setelem Km_iface D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section KFP_DEFS.
Variable RT : rt_sig.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (pix : Z) (v : pixv) (cv : cmapv) (fr : Z).

(* [comment removed for export] *)
Definition kfp_post : config -> Prop :=
  fun c => exists (Σ' : rts RT) (kel : Z),
     ASTA RT Σ' PMc (fun ms => exists m', ret_st ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 kel) m' ms
        /\ ((ART RT Σ' m' /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo usp) /\ LIBH m' /\ io_ssp m')
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [] m m'
        /\ pix_obj (rt_live RT Σ') m' pix v cv
        /\ (kel = 0 \/ exists data rows, p_d v = 8 /\ kel_obj (rt_live RT Σ') m' kel (p_h v) (p_w v) 2 2 data rows
                                       /\ rt_live RT Σ' = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ))) c
     /\ (kel = 0 -> rt_live RT Σ' = rt_live RT Σ)
     /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 ^ 30 <= rt_credit RT Σ'.

(* [comment removed for export] *)
Definition kfp_PF : Z -> Prop := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a.

(* [comment removed for export] *)
Definition kfp_ctx : Prop :=
  fdfs_only PMc /\ mat_stable PMc /\ ART RT Σ m /\ pix_obj (rt_live RT Σ) m pix v cv
  /\ rt_sp0 RT Σ - 8388608 <= lo /\ lo + (65536 + 1024 * 5) <= usp /\ 0 <= lo
  /\ usp + 16 <= 140737488355328 /\ usp mod 16 = 0 /\ usp <= rt_sp0 RT Σ
  /\ (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) /\ Z.of_nat (length (rt_frames RT Σ)) + 2 <= Z.of_nat FRAMES_MAX
  /\ p_data v <> 0 /\ 0 < fr /\ fr mod 64 = 0
  /\ (forall a, kfp_PF a -> (a < fr \/ fr + 128 <= a) /\ (a < fr / 8 + 2147450880 \/ fr / 8 + 16 + 2147450880 <= a)).

(* [comment removed for export] *)
Definition kfp_fshadow (js : list byte) : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13)); CB 4 js].

(* [comment removed for export] *)
Definition kfp_frame_lo (f0 f1 f2 f3 : list byte) : list cell :=
  [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 133699); C8 (Z_to_bv 64 595528); CB 8 f0;
   C4 (Z_to_bv 64 (p_w v)); CB 12 f1; C4 (Z_to_bv 64 (p_h v)); CB 12 f2; C4 (Z_to_bv 64 8); CB 12 f3].

(* [comment removed for export] *)
Definition kfp_lctx : Prop :=
  kfp_ctx /\ p_d v = 8 /\ pix_hdr_ok v /\ 3 <= p_h v /\ 3 <= p_w v /\ p_w v * p_h v <= 2 ^ 26
  /\ Z.of_nat (length (rt_live RT Σ)) + (p_h v + 2) <= LIVE_MAX /\ 2 ^ 30 <= rt_credit RT Σ.


(* [comment removed for export] *)
Definition kfp_stack_0 (j0 : list byte) : list cell :=
  [C8 (Z_to_bv 64 0); CB 8 j0; C8 (Z_to_bv 64 fr);
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition kfp_exit_stmt_0 : Prop :=
  forall (S : rts RT) (mc : mem) (kel : Z) (hv : word) (js j0 : list byte)
         (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r19 r21 r22 r23 r24 r25 r28 r29 r30 r31 : word) F' fc',
    kfp_ctx ->
    ART RT S mc -> mem_inv asegs mc -> wmono asegs m mc -> stk asegs mc lo (usp + -128) ->
    rw_cells asegs mc (usp + -128) (kfp_stack_0 j0) ->
    rw_cells asegs mc fr [C8 hv] -> rw_cells asegs mc (fr / 8 + 2147450880) (kfp_fshadow js) ->
    LIBH mc -> io_ssp mc -> agree_on kfp_PF m mc ->
    rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 2 ^ 30 <= rt_credit RT S ->
    pix_obj (rt_live RT S) mc pix v cv ->
    ((kel = 0 /\ rt_live RT S = rt_live RT Σ)
     \/ (exists data rows, p_d v = 8 /\ kel_obj (rt_live RT S) mc kel (p_h v) (p_w v) 2 2 data rows
                          /\ rt_live RT S = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ))) ->
    cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
                                    r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 (Z_to_bv 64 kel) r21 r22 r23 r24 r25
                                    (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) r28 r29 r30 r31 F' fc' 0x918a8 mc)))
        kfp_post.
(* [comment removed for export] *)
Definition kfp_head_0 (k : Z) (c : config) : Prop :=
  exists (S : rts RT) (mc : mem) (i j kel data : Z) (rows : list Z) (x0 : word) (f0 f1 f2 f3 f4 js j0 : list byte)
         (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
    ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -128)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -128))
                         r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 pix) (Z_to_bv 64 kel) (Z_to_bv 64 i)
                         (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 (fr + 80)) (Z_to_bv 64 j)
                         (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) r28 r29 r30 r31 F' fc' 0x919f8 mc)) c
    /\ k = i * p_w v + j /\ 0 <= i < p_h v /\ 0 <= j < p_w v /\ kfp_lctx
    /\ ART RT S mc /\ mem_inv asegs mc /\ wmono asegs m mc /\ stk asegs mc lo (usp + -128)
    /\ rw_cells asegs mc (usp + -128) (kfp_stack_0 j0)
    /\ rw_cells asegs mc fr (kfp_frame_lo f0 f1 f2 f3) /\ rw_cells asegs mc (fr + 80) [C4 x0] /\ rw_cells asegs mc (fr + 84) [CB 36 f4]
    /\ rw_cells asegs mc (fr / 8 + 2147450880) (kfp_fshadow js)
    /\ LIBH mc /\ io_ssp mc /\ agree_on kfp_PF m mc
    /\ pix_obj (rt_live RT Σ) mc pix v cv /\ kel_obj (rt_live RT S) mc kel (p_h v) (p_w v) 2 2 data rows
    /\ rt_live RT S = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ)
    /\ rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ /\ rt_sp0 RT S = rt_sp0 RT Σ
    /\ rt_credit RT Σ - 1 - km_cost (p_h v) (p_w v) - k <= rt_credit RT S.

(* [comment removed for export] *)
Definition kfp_stack_16 (j0 j1 : list byte) : list cell :=
  [CB 16 j0; C8 (Z_to_bv 64 fr); CB 16 j1;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition kfp_exit_stmt_16 : Prop :=
  forall (S : rts RT) (mc : mem) (kel : Z) (hv : word) (js j0 j1 : list byte)
         (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r19 r21 r22 r23 r24 r25 r28 r29 r30 r31 : word) F' fc',
    kfp_ctx ->
    ART RT S mc -> mem_inv asegs mc -> wmono asegs m mc -> stk asegs mc lo (usp + -144) ->
    rw_cells asegs mc (usp + -144) (kfp_stack_16 j0 j1) ->
    rw_cells asegs mc fr [C8 hv] -> rw_cells asegs mc (fr / 8 + 2147450880) (kfp_fshadow js) ->
    LIBH mc -> io_ssp mc -> agree_on kfp_PF m mc ->
    rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ -> rt_credit RT Σ - 2 ^ 30 <= rt_credit RT S ->
    pix_obj (rt_live RT S) mc pix v cv ->
    ((kel = 0 /\ rt_live RT S = rt_live RT Σ)
     \/ (exists data rows, p_d v = 8 /\ kel_obj (rt_live RT S) mc kel (p_h v) (p_w v) 2 2 data rows
                          /\ rt_live RT S = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ))) ->
    cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -144)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -144))
                                    r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 (Z_to_bv 64 kel) r21 r22 r23 r24 r25
                                    (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) r28 r29 r30 r31 F' fc' 0x918a8 mc)))
        kfp_post.
(* [comment removed for export] *)
Definition kfp_head_16 (k : Z) (c : config) : Prop :=
  exists (S : rts RT) (mc : mem) (i j kel data : Z) (rows : list Z) (x0 : word) (f0 f1 f2 f3 f4 js j0 j1 : list byte)
         (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) F' fc',
    ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -144)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -144))
                         r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 pix) (Z_to_bv 64 kel) (Z_to_bv 64 i)
                         (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 (fr + 80)) (Z_to_bv 64 j)
                         (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 fr) r28 r29 r30 r31 F' fc' 0x919f8 mc)) c
    /\ k = i * p_w v + j /\ 0 <= i < p_h v /\ 0 <= j < p_w v /\ kfp_lctx
    /\ ART RT S mc /\ mem_inv asegs mc /\ wmono asegs m mc /\ stk asegs mc lo (usp + -144)
    /\ rw_cells asegs mc (usp + -144) (kfp_stack_16 j0 j1)
    /\ rw_cells asegs mc fr (kfp_frame_lo f0 f1 f2 f3) /\ rw_cells asegs mc (fr + 80) [C4 x0] /\ rw_cells asegs mc (fr + 84) [CB 36 f4]
    /\ rw_cells asegs mc (fr / 8 + 2147450880) (kfp_fshadow js)
    /\ LIBH mc /\ io_ssp mc /\ agree_on kfp_PF m mc
    /\ pix_obj (rt_live RT Σ) mc pix v cv /\ kel_obj (rt_live RT S) mc kel (p_h v) (p_w v) 2 2 data rows
    /\ rt_live RT S = km_live kel data (p_h v) (p_w v) rows (rt_live RT Σ)
    /\ rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ /\ rt_sp0 RT S = rt_sp0 RT Σ
    /\ rt_credit RT Σ - 1 - km_cost (p_h v) (p_w v) - k <= rt_credit RT S.
End KFP_DEFS.
