(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface D_iface D_defs LeptB_guard.
Import ListNotations.
Open Scope Z_scope.

Section DESER2_DEFS.
Variable RT : rt_sig.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (QF : config -> Prop) (fr : Z).

(* [comment removed for export] *)
Definition deser_PF : Z -> Prop := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a.

(* [comment removed for export] *)
Definition deser_ctx (dp n : Z) (ras : list Z) (rdes : Z) : Prop :=
  fdfs_only PMc /\ mat_stable PMc /\ ART RT Σ m
  /\ rt_sp0 RT Σ - 8388608 <= lo /\ lo + (65536 + 1024 * 8) <= usp /\ 0 <= lo
  /\ usp + 16 <= 140737488355328 /\ usp mod 16 = 0 /\ usp <= rt_sp0 RT Σ
  /\ Z.of_nat (length (rt_frames RT Σ)) + 6 <= Z.of_nat FRAMES_MAX /\ Z.of_nat (length (rt_live RT Σ)) + 5 <= LIVE_MAX
  /\ 2 * 67108864 + 16384 + 64 <= rt_credit RT Σ
  /\ 28 <= n < 2^26 /\ 0 < dp /\ dp mod 8 = 0 /\ own_live (rt_live RT Σ) dp n
  /\ chain_ok m usp (bv_unsigned s0) ras /\ 4096 <= bv_unsigned ra
  /\ Forall (fun f => In (f :: rdes :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS.

(* [comment removed for export] *)
Definition deser_fshadow : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13));
   C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].

(* [comment removed for export] *)
Definition deser_epi_stmt_0 : Prop :=
  forall (S : rts RT) (mE : mem) (pixr : Z) (v : pixv) (cv : cmapv) (jE : list byte)
         (r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r28 r29 r30 r31 : word) F' fc',
    ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -160) ->
    rw_cells asegs mE (usp + -160) (CB 56 jE :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
    wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
    LIBH mE -> io_ssp mE -> agree_on deser_PF m mE ->
    rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_credit RT Σ - (2 * 67108864 + 16384 + 64) <= rt_credit RT S ->
    (forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)) ->
    (pixr = 0 \/ (pix_obj (rt_live RT S) mE pixr v cv /\ p_data v <> 0)) ->
    (pixr = 0 -> rt_live RT S = rt_live RT Σ) -> (pixr <> 0 -> live_destroy pixr v cv (rt_live RT S) = rt_live RT Σ) ->
    (forall p k, In (p, k) (rt_live RT S) -> 0 < k) ->
    Z.of_nat (length (rt_live RT S)) <= Z.of_nat (length (rt_live RT Σ)) + 4 ->
    cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -160)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                    (Z_to_bv 64 pixr) r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 (Z_to_bv 64 fr) r22 r23
                                    r24 r25 r26 (Z_to_bv 64 (fr / 8 + 2147450880)) r28 r29 r30 r31 F' fc' 0xae240 mE))) QF.
(* [comment removed for export] *)
Definition deser_cut2_stmt_0 (dp n : Z) : Prop :=
  forall (S : rts RT) (mc : mem) (pixd cm nc : Z) (v : pixv) (cv : cmapv)
         (j0 j1 f0 f1 f2 : list byte) (c16 vx : word)
         (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r24 r25 r28 r29 r30 r31 : word) F' fc',
    ART RT S mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -160) ->
    rw_cells asegs mc (usp + -160)
      [CB 8 j0; C8 (Z_to_bv 64 (4 * (p_wpl v * p_h v))); C8 c16; C8 (Z_to_bv 64 nc); CB 16 j1; C8 (Z_to_bv 64 fr);
       C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mc fr [CB 32 f0; C4 vx; CB 44 f1; C8 (Z_to_bv 64 pixd); CB 32 f2] ->
    rw_cells asegs mc (fr / 8 + 2147450880) deser_fshadow ->
    LIBH mc -> io_ssp mc -> agree_on (deser_PF) m mc ->
    rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_credit RT Σ - (2 * 67108864 + 16384 + 64) + 6 <= rt_credit RT S ->
    (forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)) ->
    pix_obj (rt_live RT S) mc pixd v cv -> p_data v <> 0 ->
    0 <= nc <= 256 -> (0 < nc -> cm <> 0 /\ p_cmap v = cm) -> (nc = 0 -> cm = 0 /\ p_cmap v = 0) ->
    4 * (p_wpl v * p_h v) = n - 28 - 4 * nc ->
    live_destroy pixd v cv (rt_live RT S) = rt_live RT Σ ->
    (forall p k, In (p, k) (rt_live RT S) -> 0 < k) ->
    Z.of_nat (length (rt_live RT S)) <= Z.of_nat (length (rt_live RT Σ)) + 4 ->
    cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -160)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -160))
                                    r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 dp) (Z_to_bv 64 (fr + 80)) (Z_to_bv 64 fr)
                                    (Z_to_bv 64 cm) (Z_to_bv 64 nc) r24 r25 (Z_to_bv 64 2147450880) (Z_to_bv 64 (fr / 8 + 2147450880))
                                    r28 r29 r30 r31 F' fc' 0xae158 mc))) QF.
(* [comment removed for export] *)
Definition deser_epi_stmt_16 : Prop :=
  forall (S : rts RT) (mE : mem) (pixr : Z) (v : pixv) (cv : cmapv) (jE : list byte)
         (r1 r5 r6 r7 r9 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r26 r28 r29 r30 r31 : word) F' fc',
    ART RT S mE -> mem_inv asegs mE -> stk asegs mE lo (usp + -176) ->
    rw_cells asegs mE (usp + -176) (CB 72 jE :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
    wr_at asegs mE fr 120 -> wr_at asegs mE (fr / 8 + 2147450880) 16 ->
    LIBH mE -> io_ssp mE -> agree_on deser_PF m mE ->
    rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_credit RT Σ - (2 * 67108864 + 16384 + 64) <= rt_credit RT S ->
    (forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)) ->
    (pixr = 0 \/ (pix_obj (rt_live RT S) mE pixr v cv /\ p_data v <> 0)) ->
    (pixr = 0 -> rt_live RT S = rt_live RT Σ) -> (pixr <> 0 -> live_destroy pixr v cv (rt_live RT S) = rt_live RT Σ) ->
    (forall p k, In (p, k) (rt_live RT S) -> 0 < k) ->
    Z.of_nat (length (rt_live RT S)) <= Z.of_nat (length (rt_live RT Σ)) + 4 ->
    cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -176)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) r9
                                    (Z_to_bv 64 pixr) r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 r20 (Z_to_bv 64 fr) r22 r23
                                    r24 r25 r26 (Z_to_bv 64 (fr / 8 + 2147450880)) r28 r29 r30 r31 F' fc' 0xae240 mE))) QF.
(* [comment removed for export] *)
Definition deser_cut2_stmt_16 (dp n : Z) : Prop :=
  forall (S : rts RT) (mc : mem) (pixd cm nc : Z) (v : pixv) (cv : cmapv)
         (j0 j1 jp f0 f1 f2 : list byte) (c16 vx : word)
         (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r24 r25 r28 r29 r30 r31 : word) F' fc',
    ART RT S mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -176) ->
    rw_cells asegs mc (usp + -176)
      [CB 8 j0; C8 (Z_to_bv 64 (4 * (p_wpl v * p_h v))); C8 c16; C8 (Z_to_bv 64 nc); CB 16 j1; C8 (Z_to_bv 64 fr); CB 16 jp;
       C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mc fr [CB 32 f0; C4 vx; CB 44 f1; C8 (Z_to_bv 64 pixd); CB 32 f2] ->
    rw_cells asegs mc (fr / 8 + 2147450880) deser_fshadow ->
    LIBH mc -> io_ssp mc -> agree_on (deser_PF) m mc ->
    rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_credit RT Σ - (2 * 67108864 + 16384 + 64) + 6 <= rt_credit RT S ->
    (forall e, In e (rt_live RT Σ) -> In e (rt_live RT S)) ->
    pix_obj (rt_live RT S) mc pixd v cv -> p_data v <> 0 ->
    0 <= nc <= 256 -> (0 < nc -> cm <> 0 /\ p_cmap v = cm) -> (nc = 0 -> cm = 0 /\ p_cmap v = 0) ->
    4 * (p_wpl v * p_h v) = n - 28 - 4 * nc ->
    live_destroy pixd v cv (rt_live RT S) = rt_live RT Σ ->
    (forall p k, In (p, k) (rt_live RT S) -> 0 < k) ->
    Z.of_nat (length (rt_live RT S)) <= Z.of_nat (length (rt_live RT Σ)) + 4 ->
    cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -176)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -176))
                                    r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) (Z_to_bv 64 dp) (Z_to_bv 64 (fr + 80)) (Z_to_bv 64 fr)
                                    (Z_to_bv 64 cm) (Z_to_bv 64 nc) r24 r25 (Z_to_bv 64 2147450880) (Z_to_bv 64 (fr / 8 + 2147450880))
                                    r28 r29 r30 r31 F' fc' 0xae158 mc))) QF.
End DESER2_DEFS.
