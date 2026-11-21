(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Tac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Walk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require ITree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Common Require SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM11.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM13.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM12.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM04.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM03.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require RMallocRep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require RMallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require PM21.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require PM22.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require PM02.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require PM03.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require RF_enframe.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require PM18.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require PM20.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require RASlot_W2.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require RASlot_W4.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require PM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM07.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM05.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require F_ntf_H.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require RF_free_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RASlot_W13.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_malloc_entry. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM04. Import MM04. Import MM04.ASlot_W13. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM03. Import MM03. Import MM03.ASlot_W14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import RF_enframe. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. Import PM18. Import PM18.RMallocKit_A3. Import PM20. Import PM20.RF_ntf_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import RASlot_W2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import RASlot_W4.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

Lemma rnenf_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc,
  0 <= c_mmap_counter (ctx st) < 2^32 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m1 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x1725c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 (RSIZE_CLASSES + j * 2)) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x1725c) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ munch [(P - 3, P)]%Z m1 m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m1 m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
      /\ rmrep (enf0_st st g b idx) m' /\ ticks_ok (enf0_st st g b idx))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 j) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17230) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until fc. intros CTR MI.
  pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  pose proof (size_class_range j J) as SZR.
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  assert (NR : 12 <= N < 2^18) by (unfold N, UNIT, IB; lia).
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  destruct (rslot_facts st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0)
    as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND. fold B in CB, Y, WRs, PEND. 
  pose proof (rmeta_chunk_facts st m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
  atop_facts.
  set (G := conc st g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM. fold B in MM.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  pose proof (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  pose proof MW as (LI0 & FB0 & SCR0 & ML0).
  pose proof MR as (WF' & CX & GL & _). destruct CX as (CH & _). unfold rctx_head_cells, rsecw in CH.
  unfold RSIZE_CLASSES, RMLOCK, RCTX in *. atop_facts.
  step. step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  step. step.
  pose proof (rsize_classes_read m1 j MI J) as SCRD. unfold RSIZE_CLASSES in SCRD.
  replace (72364 + 2 * j) with (72364 + j * 2) in SCRD by lia.
  step. rewrite zx16_wz by lia. clear SCRD.
  pose proof (rmrep_active_read st m1 j (wa (327816 + 80 + 8 * j)) MR J eq_refl) as RDA. rewrite HA in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA. fold G in RDA.
  replace (wa (327816 + 80 + 8 * j)) with (Z_to_bv 64 (327808 + j * 8 + 88)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  step. rewrite sx32_wz_sxv by lia.
  step. rewrite (wz_unsigned (size_class j)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  step.
  step.
  eapply evt_mono.
  { eapply (renframe_walk (Z_to_bv 64 0x1725c) sp gp tp _ _ _ s0 s1 _ _ _ _ _ s3 s4 s5 _ s7 s8 _ s10 s11 _ _ _ _ (Z_to_bv 64 G) _
              (pw st (m_prev mr)) (pw st (m_next mr)) F fc m1 B stride N idx (c_mmap_counter (ctx st)) (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned _) _ => rewrite (unsigned_lit G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by lia; unfold N, UNIT, IB; lia
         | |- _ => idtac end.
    all: try (rewrite (unsigned_lit G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia.
    - exact (so_maplen _ _ _ _ _ _ SO). }
  intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
  destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
  set (off0 := if bv_unsigned x3 =? 0 then Z.land (c_mmap_counter (ctx st)) 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) in EM |- *.
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  replace ((stride - 4 - N) / 16) with 0 in EM |- * by (rewrite STN; replace (N + 4 - 4 - N) with 0 by lia; reflexivity).
  pose proof (fold_off_le_slack off0 0 OFF0 ltac:(lia)) as OFF.
  replace (fold_off off0 0) with 0 in EM |- * by lia.
  rewrite Z.mul_0_r, Z.add_0_r in EM |- *.
  replace (ret_pc (Z_to_bv 64 0x1725c)) with (Z_to_bv 64 0x1725c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  assert (S31n : stride - 4 - N < 2^31) by lia.
  assert (SPAN2 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; exact SPAN1).
  assert (T1 : 0 <= idx < 32) by lia. assert (T3 : 16 * 0 + N + 4 <= stride) by lia. assert (T0 : 0 <= 0) by lia. assert (TN : 0 <= N) by lia.
  assert (T4 : (stride * idx + 16 * 0) / 16 < 65536) by (apply (Q16 0); lia).
  destruct (renframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4)
    as (MRr & TKr & CONCr & FSTr & SNDr). clear T1 T3 T0 TN T4.
  rewrite Z.mul_0_r, Z.add_0_r in MRr.
  change (conc st b) with B in MRr. change (get_stride (get_meta_rec st g)) with stride in MRr.
  fold P in MRr, EM. rewrite <- EM in MRr.
  destruct (enf0_st_eq st g b r idx j STR SO) as [E1st _]. fold N in E1st. rewrite E1st in MRr, TKr.
  assert (EM' : m' = write_to_mem (write_to_mem (write_to_mem m1 (wa (P - 3)) [b8 idx]) (wa (P - 2)) (le2 (wz ((P - B - 16) / 16)))) (wa (P - 3)) [b8 (Z.land idx 31 + Z.shiftl 0 5)]).
  { rewrite EM. unfold renframe_tail_mem, renframe_off_mem. cbn [Z.eqb].
    replace (P + stride - 4 - P - N) with 0 by lia. cbn [Z.eqb Z.leb]. reflexivity. }
  assert (MU : munch [(P - 3, P)]%Z m1 m').
  { rewrite EM'. apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
  assert (WM : wmono (run_segments psegs rc_inp rc_sp rc_mb) m1 m').
  { rewrite EM'. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl. }
  do 14 eexists. exists m'.
  split; [unfold P, G; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact MRr| exact TKr].
Qed.
Lemma lor_192 a : 0 <= a < 32 -> Z.lor a 192 = a + 192.
Proof. intros Ha. change 192 with (3 * 2 ^ 6). rewrite (lor_small_shl 3 6 a) by lia. lia. Qed.

Lemma renfD_walk :
  forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mt : aptr) (cnt : Z) mC,
  meta_slot st mt -> mw_ok (get_meta_rec st mt) -> 1 <= cnt <= 32 ->
  rmrep (enf0_st st g b idx) mC -> ticks_ok (enf0_st st g b idx) -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mC ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (P + 12)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17284) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ munch [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) mC m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
      /\ rmrep (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
                 (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))) m'
      /\ ticks_ok (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
                 (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1725c) fc None mC (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until mC. intros MST MWT CR MRC TKC MIC.
  pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). atop_facts.
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  set (st0' := enf0_st st g b idx) in *.
  assert (MST0 : meta_slot st0' mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  pose proof (rmeta_slot_bounds st0' mC mt MRC MST0) as (Tpos & TC & TI & _ & _).
  change (conc st0' mt) with (conc st mt) in Tpos, TC, TI.
  pose proof (rmeta_chunk_facts st0' mC mt MRC MST0) as (_ & _ & _ & _ & _ & GDJ & _).
  assert (RG0 : s_regions st0' = s_regions st) by (unfold st0', enf0_st, wr16; rewrite !s_regions_wr8; reflexivity).
  assert (GR0 : s_groups st0' = s_groups st) by (unfold st0', enf0_st, wr16; rewrite !s_groups_wr8; reflexivity).
  rewrite RG0 in GDJ. pose proof (GDJ (fst b) r Hr Hk) as TDJ. change (conc st0' mt) with (conc st mt) in TDJ.
  pose proof (munch_refl [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC) as MU. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mC) as WM.
  pose proof MWT as (LI0 & FB0 & SCR0 & ML0). pose proof (meta_word_range _ MWT) as MWR.
  atop_facts.
  rmchunk MRC MST0 CH. change (conc st0' mt) with (conc st mt) in CH. change (get_meta_rec st0' mt) with (get_meta_rec st mt) in CH.
  rmeta_open (conc st mt) MUt WMt.
  step.
  step. step. rewrite ?(unsigned_lit (meta_word (get_meta_rec st mt))) by lia.
  set (w := meta_word (get_meta_rec st mt)) in *.
  rewrite (Z_to_bv_unsigned 64 (Z.shiftl w 52)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (zb_shl_shr w 52) by lia. change (2 ^ (64 - 52)) with 4096.
  rewrite (meta_word_mod4096 st g b idx j _ MWT).
  step.
  lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (conc st mt) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR5 : rmrep (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') mX);
    [ eapply rmrep_put_meta_frame; [exact MRC| exact MST0| exact MUt| exact WMt|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
      unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen oconc]; reflexivity
    | clear MUt WMt H ] end.
  set (st5 := put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') in *.
  assert (TK5 : ticks_ok st5) by (exact (ticks_ok_upd_meta st0' mt (fun _ => m_set_maplen 0 (get_meta_rec st mt)) TKC)).
  pose proof (land31_range idx) as L31.
  assert (K3 : cell_read (get_shadow st5 (fst b)) (snd b + (16 + stride * idx) + -3) = Known (Z.land idx 31)).
  { change (get_shadow st5 (fst b)) with (get_shadow st0' (fst b)). unfold st0', enf0_st.
    rewrite (cell_read_wr8_same (wr8 _ _ (wr16 _ _ st)) (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5));
      [| apply ticks_ok_wr8, ticks_ok_wr16; exact TK | change (Z.shiftl 0 5) with 0; lia].
    change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity. }
  destruct (rmrep_shadow_read st5 _ (fst b) r (snd b + (16 + stride * idx) + -3) (Z.land idx 31) MR5 Hr Hk ltac:(lia) K3) as [RDK _].
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in RDK
    by (unfold wa; f_equal; unfold P; lia).
  step. rewrite zxb_b8 by lia. clear RDK. rewrite ?(unsigned_lit P) by (unfold P; lia).
  step. rewrite (unsigned_lit cnt), swrap32_small by lia.
  step. rewrite (wz_unsigned (Z.land idx 31)) by lia. rewrite <- (Z.land_assoc idx 31 31). change (Z.land 31 31) with 31.
  step. rewrite ?(unsigned_lit (Z.land idx 31)) by lia.
  pose proof MR5 as (_ & _ & _ & _ & _ & SH5). destruct (SH5 (fst b) r Hr Hk) as [WR5 _]. clear SH5.
  pose proof (wr_at_store_ok (run_segments psegs rc_inp rc_sp rc_mb) _ _ _ (snd b + (16 + stride * idx) + -3) 1 WR5 ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  assert (RG5 : s_regions st5 = s_regions st) by (unfold st5; exact RG0).
  assert (GR5 : s_groups st5 = s_groups st) by (unfold st5; exact GR0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_wr8 st5 mX (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192) r MR5 TK5) as MR6 end.
  cbn [fst snd] in MR6. rewrite RG5, GR5 in MR6.
  assert (LOR : 0 <= Z.lor (Z.land idx 31) 192 < 256) by (rewrite lor_192 by lia; lia).
  specialize (MR6 Hr Hk ltac:(lia) ltac:(intros b' gh' Hb' Hf'; destruct (NOGRP b' gh' Hb' Hf'); lia) ltac:(lia)).
  replace (r_base r + (snd b + (16 + stride * idx) + -3)) with (P - 3) in MR6 by (unfold P; lia).
  rewrite <- (lor_192 (Z.land idx 31)) by lia.
  rraw_store_finish0 (P - 3) [b8 (Z.lor (Z.land idx 31) 192)] MU WM SOK.
  step. rewrite ?(unsigned_lit P) by (unfold P; lia).
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MR6| apply ticks_ok_wr8; exact TK5].
Qed.
Lemma rzero_loop_walk : forall k (i szc cnt : Z) stz mC0 mC
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  Z.of_nat k = cnt + 1 - i -> 0 <= i <= cnt -> 1 <= szc -> 0 <= cnt < 4096 -> 16 + 16 * szc * cnt <= stride ->
  s_regions stz = s_regions st -> s_groups stz = s_groups st ->
  rmrep stz mC -> ticks_ok stz -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mC ->
  munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 mC -> wmono (run_segments psegs rc_inp rc_sp rc_mb) mC0 mC ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (cnt - 1)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17554) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) mC0 m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
      /\ rmrep (zero_hdrs (pp st g b idx) (16 * szc) i k stz) m' /\ ticks_ok (zero_hdrs (pp st g b idx) (16 * szc) i k stz)
      /\ s_regions (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_regions st /\ s_groups (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_groups st
      /\ (forall x, (forall j, i <= j <= cnt -> bv_unsigned x <> P + 12 + 16 * szc * j) -> m' x = mC x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt + 1 - i)) (Z_to_bv 64 (P + 12 + 16 * szc * i)) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17284) fc None mC (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  induction k as [|k IH]; intros until fc; intros HK HI SZC CNT FIT RGz GRz MRz TKz MIz MU WM.
  { exfalso. lia. }
  pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SZI : 0 <= 16 * szc * i <= 16 * szc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia]).
  pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). atop_facts.
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  assert (Hr' : (s_regions stz) !! (fst b) = Some r) by (rewrite RGz; exact Hr).
  pose proof MRz as (WFz & _ & _ & _ & _ & SHz). destruct (SHz (fst b) r Hr' Hk) as [WRz _]. clear SHz.
  pose proof (wr_at_store_ok (run_segments psegs rc_inp rc_sp rc_mb) _ _ _ (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)) 1 WRz ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)))) with (Z_to_bv 64 (P + 12 + 16 * szc * i)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_wr8 stz mX (aadd (pp st g b idx) (UNIT + i * (16 * szc) - 4)) 0 r MRz TKz) as MR2 end.
  unfold aadd, pp, UNIT in MR2. cbn [fst snd] in MR2. fold mr in MR2. fold stride in MR2. rewrite GRz in MR2.
  specialize (MR2 Hr' Hk ltac:(lia)).
  assert (NOG : forall b0 gh, (s_groups st) !! b0 = Some gh -> fst b0 = fst b ->
            ~ snd b0 <= snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4) < snd b0 + 9).
  { intros b0 gh Hb0 Hf0 CONTRA. pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & _ & GWF).
    destruct (GWF b0 gh Hb0) as (r0 & _ & _ & _ & _ & M16).
    destruct (NOGRP b0 gh Hb0 Hf0) as [LE|GE]; [lia|].
    assert (E0 : snd b0 = 16 * (snd b0 / 16)) by (pose proof (Z.div_mod (snd b0) 16 ltac:(lia)); lia).
    assert (E1 : snd b = 16 * (snd b / 16)) by (pose proof (Z.div_mod (snd b) 16 ltac:(lia)); lia).
    assert (E2 : stride = 16 * (stride / 16)) by (pose proof (Z.div_mod stride 16 ltac:(lia)); lia).
    clear - E0 E1 E2 CONTRA. nia. }
  specialize (MR2 NOG ltac:(lia)). clear NOG.
  replace (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4))) with (P + 12 + 16 * szc * i) in MR2 by (unfold P; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0])
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa; f_equal; lia);
    assert (PW0 : forall u, 0 <= u < 2^64 -> u <> P + 12 + 16 * szc * i -> write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0] (wa u) = mX (wa u));
    [ intros u Hu Hux;
      rewrite write_to_mem_spec by (cbn; lia); rewrite wa_unsigned by lia; cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity;
      destruct (Z.leb_spec0 (P + 12 + 16 * szc * i) u); destruct (Z.ltb_spec0 u (P + 12 + 16 * szc * i + 1)); cbn [andb]; try reflexivity;
      exfalso; lia
    | apply (munch_write _ _ mX (P + 12 + 16 * szc * i) [b8 0]) in MU; [| lia | cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity; lia | cbn [length inside]; replace (Z.of_nat 1) with 1 by reflexivity; lia];
      apply (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) _ mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in WM;
      lazymatch goal with HI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mX |- _ =>
        apply (mem_inv_store (run_segments psegs rc_inp rc_sp rc_mb) mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in HI;
        [| first [ exact SOK | replace (wa (P + 12 + 16 * szc * i)) with a by (unfold wa; f_equal; lia); exact SOK ] ]
      end;
      clear SOK;
      let m' := fresh "m" in remember (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0]) as m' eqn:Em'; clear Em' ]
  end.
  step. rewrite ?(unsigned_lit (cnt + 1 - i)) by lia.
  step. rewrite ?unsigned_lit by lia.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    replace (cnt + 1 - i + -1) with (cnt + 1 - (i + 1)) by lia.
    replace (P + 12 + 16 * szc * i + 16 * szc) with (P + 12 + 16 * szc * (i + 1)) by lia.
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    eapply evt_mono.
    { (eapply (IH (i + 1) szc cnt);
      [ lia | lia | exact SZC | exact CNT | exact FIT
      | rewrite s_regions_wr8; exact RGz
      | rewrite s_groups_wr8; exact GRz
      | exact MR2
      | apply ticks_ok_wr8; exact TKz
      | assumption | exact MU | exact WM ]). }
    cbv beta. intros ms' (m' & -> & X1 & X2 & X3 & X4 & X5 & X6 & X7 & PW).
    eexists. split; [reflexivity|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
    split; [exact X6|]. split; [exact X7|].
    intros x Hx. rewrite (PW x) by (intros jj Hjj; apply Hx; lia).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
  -
    assert (Ei : i = cnt) by lia. destruct k; [| exfalso; lia].
    step. rewrite ?(unsigned_lit cnt) by lia. replace (cnt + -1) with (cnt - 1) by lia. step. step. step.
    apply evt_done. eexists. split; [reflexivity|].
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR2|]. split; [apply ticks_ok_wr8; exact TKz|].
    split; [rewrite s_regions_wr8; exact RGz|]. split; [rewrite s_groups_wr8; exact GRz|].
    intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
Qed.
End ENF.
End CANSEC1.
End RASlot_W13.

Module RF_ntf_H.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM05. Import MM05. Import MM05.F_ntf_F. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require Import F_ntf_H. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM14. Import MM14. Import MM14.MallocKit_B3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import RF_free_A. Import PM20. Import PM20.RF_ntf_A. Import PM20.RF_ntf_C.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation PHEAD := (Z_to_bv 64 (RCTX + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)).

Definition rentry_cases (ms' : machine_state) : Prop :=
  (ntf_cond st g i = false /\ mask <> 0 /\
   exists t0 t1 t2 a0 a2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
     RAT 0x167ac (mkR ra sp' gp tp t0 t1 t2 s0 GUARD a0 SELF a2 a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = false /\ mask = 0 /\
   exists t0 t1 t2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
     RAT 0x16590 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = true /\ m_next mr = None /\
   exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0x16654 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G a1 a2 a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
   exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0x165e8 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = true /\ sc < 48 /\
   exists nx, m_next mr = Some nx /\ nx <> g /\
   exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0x16564 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms').
End POST.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists m1 junk,
    rentry_cases ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m1 /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m1
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m1 lo (bv_unsigned sp + -96)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra)
    /\ rmrep st m1.

Lemma meta_word_sc52 mr : mw_ok mr ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr.
Proof.
  intros MW. pose proof (meta_word_range mr MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof.
  intros MW. pose proof MW as (LI & FB & SCR & ML). unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation POST := (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m.
Hypothesis LO : ATOP <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.

Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
  munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m1 /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m1
  /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m1 lo (bv_unsigned sp + -96) /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) /\ rmrep st m1.

Lemma rmaskw_zero : maskw = 0 <-> mask = 0.
Proof. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
Lemma rmaskw_range : 0 <= maskw < 2^64.
Proof. apply lor_range64; apply sxv_range. Qed.

Ltac rpost_common MU WM MI ST FR MR m1 junk :=
  apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].


Lemma rntf_notall : forall (t0 t1 t2 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> ntf_cond st g i = false ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16588) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros (MU & WM & MI & ST & FR & MR) HC.
  pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
  pose proof (rmeta_slot_bounds st m1 g MR (eh_slot _ _ _ EH)) as (GB0 & GB1 & GB2 & _). atop_facts.
  st1. rewrite ?(unsigned_lit (conc st g)) by lia.
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; unmask64 K.
  -
    rpost_common MU WM MI ST FR MR m1 junk.
    left. split; [exact HC|]. split; [intros E; apply K, MZ, E|].
    do 14 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
  -
    assert (M0 : mask = 0) by (apply MZ; lia).
    rpost_common MU WM MI ST FR MR m1 junk.
    right; left. split; [exact HC|]. split; [exact M0|].
    do 12 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

Lemma rntf_fge : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> okay_to_free st g = true ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16540) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros (MU & WM & MI & ST & FR & MR) HALL OKT.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
  unfold RCTX in *. atop_facts.
  assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
  assert (HC : ntf_cond st g i = true) by (rewrite ntf_cond_unfold, HALLb, OKT; reflexivity).
  assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
  { intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
    split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
  rmeta_chunk MR MSL CH.
  st1. clear CH.
  destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
  - destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. }
    specialize (G50 HC ltac:(congruence)).
    st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }
    st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
    pose proof (rmrep_active_read st m1 sc (wa (RCTX + 80 + 8 * sc)) MR ltac:(lia) eq_refl) as RDA. unfold RCTX in RDA.
    replace (wa (327816 + 80 + 8 * sc)) with (Z_to_bv 64 (327816 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.
    st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    + pose proof (NINJ ltac:(lia)) as ->.
      rpost_common MU WM MI ST FR MR m1 junk.
      do 3 right; left. split; [exact HC|]. split; [exact NX|]. split; [lia|].
      do 12 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
    + assert (NE : nx <> g) by (intros ->; apply K5; reflexivity).
      rpost_common MU WM MI ST FR MR m1 junk.
      do 4 right. split; [exact HC|]. split; [lia|]. exists nx. split; [exact NX|]. split; [exact NE|].
      do 11 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
  - st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
    rpost_common MU WM MI ST FR MR m1 junk.
    do 2 right; left. split; [exact HC|]. split; [exact NX|].
    do 14 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

Lemma rntf_okchk : forall (t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> m_freeable mr <> 0 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 (Z_to_bv 64 (meta_word mr)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16490) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros MC HALL FRNZ. pose proof MC as (MU & WM & MI & ST & FR & MR).
  pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range _ MW) as MWR. pose proof (meta_word_lt4096 _ MW) as M4.
  pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  atop_facts.
  assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
  assert (FRZ : (m_freeable mr =? 0) = false) by (apply Z.eqb_neq; lia).
  st1. st1. st1.
  st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  {
    eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
    rewrite okf_unfold, FRZ. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  assert (SC48 : sc < 48) by lia. clear K2.
  assert (NB48 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
  specialize (USG SC48).
  pose proof (size_class_range sc ltac:(lia)) as SZ.
  assert (RS' : ov_read_bytes (run_segments psegs rc_inp rc_sp rc_mb) m1 (Z_to_bv 64 (72364 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
  { replace (Z_to_bv 64 (72364 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
    apply rsize_classes_read; [assumption| lia]. }
  st1. rewrite (meta_word_last_idx _ MW). st1. rewrite (meta_word_maplen _ MW). st1. st1.
  assert (K690 : forall (t0' : word),
    m_maplen mr <> 0 ->
    evt (run_segments psegs rc_inp rc_sp rc_mb) POST
      (MS (mkR ra sp' gp tp t0' t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (get_stride mr)) (Z_to_bv 64 72364) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 327816) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x164e4) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
  { intros t0' MLNZ.
    assert (MLF : (m_maplen mr =? 0) = false) by (apply Z.eqb_neq; exact MLNZ).
    assert (GSR : 0 < get_stride mr < 2^64).
    { unfold get_stride. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn [andb negb]; unfold UNIT; lia. }
    st1. rewrite ?(unsigned_lit sc), ?(Z.shiftl_mul_pow2 sc 1) by lia. change (2 ^ 1) with 2. st1.
    replace (72364 + sc * 2) with (72364 + 2 * sc) by lia.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
    st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    { eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
      rewrite okf_unfold, FRZ, NB48. cbn [orb].
      replace (get_stride mr <? UNIT * size_class sc) with true by (symmetry; apply Z.ltb_lt; unfold UNIT; lia). reflexivity. }
    assert (STRF : (get_stride mr <? UNIT * size_class sc) = false) by (apply Z.ltb_ge; unfold UNIT; lia).
    assert (OKF : okay_to_free st g =
              if negb (optr_eqb (m_next mr) (Some g)) then true
              else if negb (is_bouncing sc st) then true
              else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false).
    { rewrite okf_unfold, FRZ, NB48, STRF, MLF. reflexivity. }
    rmeta_chunk MR MSL CH.
    st1. clear CH.
    assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
    { intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
      split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
    destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
    2:{ st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. 2:{ exfalso. lia. }
        eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF. reflexivity. }
    destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
    st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
    { assert (NE : nx <> g) by (intros ->; apply K6; reflexivity).
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF.
      cbn [optr_eqb]. rewrite (aptr_eqb_neq nx g NE). reflexivity. }
    pose proof (NINJ ltac:(lia)) as Enx. subst nx.
    rewrite optr_eqb_refl in OKF. cbn [negb] in OKF.
    st1. rewrite ?(unsigned_lit sc) by lia. st1.
    st1. if_cases K7; zify_cond K7.
    { assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K7).
      unfold is_bouncing in OKF. rewrite NR in OKF. cbn [andb negb] in OKF.
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
    assert (SR : sc_in_seq_range sc = true).
    { destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
    assert (SR' : 7 <= sc < 39).
    { unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
    unfold is_bouncing in OKF. rewrite SR in OKF. cbn [andb] in OKF.
    st1.
    pose proof (rmrep_bounces_read st m1 (sc - 7) (wa (RCTX + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB. unfold RCTX, wa in RDB.
    pose proof (BND (sc - 7)) as BR.
    replace (Z_to_bv 64 (327816 + 880 + (sc - 7))) with (Z_to_bv 64 (327816 + (sc + -7) + 880)) in RDB by (f_equal; lia).
    st1. clear RDB. st1.
    st1. if_cases K8; zify_cond K8; rewrite ?b8_unsigned, ?unsigned_lit in K8 by lia.
    { replace (100 <=? bounces st (sc - 7)) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [negb] in OKF.
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
    replace (100 <=? bounces st (sc - 7)) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [negb] in OKF.
    st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
    pose proof (rmrep_usage_read st m1 sc (wa (RCTX + 464 + 8 * sc)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
    replace (wa (327816 + 464 + 8 * sc)) with (Z_to_bv 64 (327816 + sc * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
    st1. clear RDU.
    st1. rewrite ?(unsigned_lit (m_last_idx mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1.
    st1. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
    { replace (9 * (m_last_idx mr + 1) <=? usage st sc) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [andb] in OKF.
      assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
      eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC). }
    replace (9 * (m_last_idx mr + 1) <=? usage st sc) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [andb] in OKF.
    st1. st1. if_cases K10; zify_cond K10; rewrite ?unsigned_lit in K10 by lia.
    - replace (m_last_idx mr + 1 <? 20) with false in OKF by (symmetry; apply Z.ltb_ge; lia).
      assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
      eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC).
    - replace (m_last_idx mr + 1 <? 20) with true in OKF by (symmetry; apply Z.ltb_lt; lia).
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
  assert (K678 :
    (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
    evt (run_segments psegs rc_inp rc_sp rc_mb) POST
      (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (meta_word mr)) (Z_to_bv 64 72364) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 327816) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x164cc) fc None m1 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
  { intros COND.
    assert (STR : get_stride mr = 16 * size_class sc).
    { unfold get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
    assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 _ MW). st1.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
    st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
    - eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
      rewrite okf_unfold, FRZ, NB48. cbn [orb].
      replace (m_maplen mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      destruct (get_stride mr <? UNIT * size_class sc); reflexivity.
    - replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 (get_stride mr)) by (rewrite STR; f_equal; lia).
      apply K690. lia. }
  st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  { apply K678. left. lia. }
  st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
  { apply K678. right. lia. }
  st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW). st1.
  st1. if_cases Km2; zify_cond Km2; rewrite ?unsigned_lit in Km2 by lia. 2:{ exfalso. lia. }
  replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 (get_stride mr)).
  2:{ unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
  apply K690. lia.
Qed.

Lemma rntf_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rmrep st m -> stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 G (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1642c) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until t6. intros MR ST.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range _ MW) as MWR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (GB0 & GB1 & GB2 & _).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof rmaskw_range as MWR'.
  pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5) & _).
  unfold RGOT_SSP, RSSP_GUARD in *. atop_facts. unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  st1. carve_frame 96%nat ST. st1. st1. st1. st1. st1.
  st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
  clear MR G4 G5.
  lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) _ (bv_unsigned sp + -96) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
  rmeta_chunk MR1 MSL CH.
  st1. st1. st1. rewrite ?sx32_wz_sxv by lia. st1.
  st1. rewrite ?(unsigned_lit i) by lia. rewrite (sllw1_word i) by lia.
  st1. rewrite ?(unsigned_lit (meta_word mr)) by lia.
  st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  st1. rewrite (meta_word_freeable _ MW).
  st1. rewrite (meta_word_sc52 _ MW).
  clear CH.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MC : rmid_ctx mX junk48) by (split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|exact MR1]) end.
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { assert (HC : ntf_cond st g i = false).
    { rewrite ntf_cond_unfold, okf_unfold. replace (m_freeable mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply andb_false_r. }
    eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC). }
  st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite ?(unsigned_lit (Z.lor _ _)) by (apply lor_range64; apply sxv_range).
  rewrite addw_word. replace (maskw + sxv (2 ^ i)) with (sxv (2 ^ i) + maskw) by lia.
  st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 _ MW).
  st1. rewrite addiw_m1_word.
  pose proof (sxv_range (sxv (2 ^ i) + maskw)) as R1. pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as R2.
  st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by (apply sxv_range).
  - assert (HC : ntf_cond st g i = false).
    { rewrite ntf_cond_unfold. replace (mask + bit i =? mask_upto (m_last_idx mr)) with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. unfold bit, mask_upto. intros E. apply K2.
      apply (proj2 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))). exact E. }
    eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC).
  -
    apply (proj1 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))) in K2.
    eapply (rntf_okchk t0 t1 t2 _ _ _ t3 t4 t5 t6 _ junk48 MC); [unfold bit, mask_upto; exact K2 | lia].
Qed.
End ENTRY.
End CANSEC1.
End RF_ntf_H.
