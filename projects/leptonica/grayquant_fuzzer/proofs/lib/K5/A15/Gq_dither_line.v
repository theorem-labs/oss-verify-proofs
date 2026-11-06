(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Gq_dither_l1 Gq_dither_l0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_ditherToBinaryLineLow : Z := 0x9ceac.

Notation DLL_W usp lined nl bufs1 bufs2 n1 := [(usp - 48, usp); (lined, lined + nl); (bufs1, bufs1 + n1); (bufs2, bufs2 + n1)]%Z (only parsing).

(* [comment removed for export] *)
Definition ditherToBinaryLineLow_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (usp lo lined nl bufs1 bufs2 n1 : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (bs1' bs2' : list byte) (wl' : list word),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (DLL_W usp lined nl bufs1 bufs2 n1) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo usp
    /\ u8arr asegs m' bufs1 bs1' /\ Z.of_nat (length bs1') = n1 /\ acc asegs m' bufs1 n1
    /\ u8arr asegs m' bufs2 bs2' /\ Z.of_nat (length bs2') = n1 /\ acc asegs m' bufs2 n1
    /\ u32arr asegs m' lined wl' /\ 4 * Z.of_nat (length wl') = nl /\ acc asegs m' lined nl.

(* [comment removed for export] *)
Lemma dll_finish : forall (ra gp tp t1 t2 s0e s1e a1 a4 a5 a6 s2e s3e s4e s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0 s1 s2 s3 s4 : word) F fc (m0 m : mem)
    (usp lo lined nl bufs1 bufs2 n1 w : Z) (bs1 bs2 : list byte) (wl : list word),
  dl_geom2 lined nl bufs1 bufs2 n1 w ->
  munch (DLL_W usp lined nl bufs1 bufs2 n1) m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  rw_cells asegs m (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
  stk asegs m lo (usp + -48) -> lo <= usp - 48 -> usp <= 2^47 -> 0x10007fff8000 <= lo ->
  lined + nl <= lo -> bufs1 + n1 <= lo -> bufs2 + n1 <= lo ->
  evt asegs (ditherToBinaryLineLow_post ra0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo lined nl bufs1 bufs2 n1)
    (MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp (Z_to_bv 64 (w - 1)) t1 t2 s0e s1e (Z_to_bv 64 lined) a1 (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) a4 a5 a6
             (Z_to_bv 64 SHB) s2e s3e s4e s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9d374) fc None m (seg_rom asegs)).
Proof.
  intros until wl. intros GEO MU WM MI UB UBL ACCB UC UCL ACCC UL ULL ACCL FR ST LO UHI LOH LLO BLO CLO.
  pose proof GEO as ((HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP)
                     & C0 & C8 & CHI & CSH & CSEG & SEP2 & SEP3).
  unfold SEGTOP_A, SHB in *.
  eapply evt_cut.
  { eapply dl0_last; eassumption. }
  intros ms' PO. unfold dl0_end in PO.
  destruct PO as (s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & s2' & s3' & s4' & m' & bs1' & bs2' & wl' & -> & MU' & WM' & MI' 
                  & UB' & UBL' & ACCB' & UC' & UCL' & ACCC' & UL' & ULL' & ACCL').
  clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL.
  lazymatch type of MU' with munch _ ?mo _ => transport_after_call asegs mo m' MU' WM' end.
  clear MU' WM'.
  idtac "MARK finish: transported".
  lwalk (@nil Z).
  idtac "MARK finish: epilogue walked".
  apply evt_done. unfold ditherToBinaryLineLow_post.
  do 15 eexists. exists m', bs1', bs2', wl'.
  split; [reflexivity|].
  repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma ditherToBinaryLineLow_evt : forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (lined nl bufs1 bufs2 n1 w : Z) (bs1 bs2 : list byte) (wl : list word),
  dl_geom2 lined nl bufs1 bufs2 n1 w ->
  mem_inv asegs m ->
  u8arr asegs m bufs1 bs1 -> Z.of_nat (length bs1) = n1 -> acc asegs m bufs1 n1 ->
  u8arr asegs m bufs2 bs2 -> Z.of_nat (length bs2) = n1 -> acc asegs m bufs2 n1 ->
  u32arr asegs m lined wl -> 4 * Z.of_nat (length wl) = nl -> acc asegs m lined nl ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo usp -> lo <= usp - 48 -> usp <= 2^47 -> 0x10007fff8000 <= lo ->
  lined + nl <= lo -> bufs1 + n1 <= lo -> bufs2 + n1 <= lo ->
  evt asegs (ditherToBinaryLineLow_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m usp lo lined nl bufs1 bufs2 n1)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lined) (Z_to_bv 64 w) (Z_to_bv 64 bufs1) (Z_to_bv 64 bufs2) a4 a5 (Z_to_bv 64 0) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_ditherToBinaryLineLow) fc None m (seg_rom asegs)).
Proof.
  intros until wl. intros GEO MI UB UBL ACCB UC UCL ACCC UL ULL ACCL G1 G2 ST LO UHI LOH LLO BLO CLO.
  pose proof GEO as ((HW & WN & N4 & NHI & WL & L4 & LHI & B0 & B8 & BHI & BSH & BSEG & L0 & LA4 & LNHI & LSH & LSEG & SEP)
                     & C0 & C8 & CHI & CSH & CSEG & SEP2 & SEP3).
  unfold e_ditherToBinaryLineLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl (DLL_W usp lined nl bufs1 bufs2 n1) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0x9d044].           (* [comment removed for export] *)
  idtac "MARK at dispatch".
  swrap32_fix. replace (w + -1) with (w - 1) by (clear; lia).
  lstep.
  destruct (Z.eq_dec w 1) as [W1|W2].
  - (* [comment removed for export] *)
    brT.
    lwalk [0x9d374].
    idtac "MARK w = 1 at 0x9d484".
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (w - 1)) by (f_equal; clear - W1; lia).
    eapply dll_finish; try eassumption; lia.
  - (* [comment removed for export] *)
    brF.
    lwalk [0x9d0a8].
    idtac "MARK at loop head".
    replace ((w - 1) * 4294967296 / 4294967296) with (w - 1) by (symmetry; apply Z.div_mul; clear; lia).
    assert (Q1 : Z.of_nat (Z.to_nat (w - 1)) = w - 1 - 0) by (clear - HW; lia).
    assert (Q3 : (1 <= Z.to_nat (w - 1))%nat) by (clear - HW W2; lia).
    eapply evt_cut.
    { eapply (dl0_pixels (Z.to_nat (w - 1)) 0); try eassumption. clear - HW; lia. }
    intros ms' PO. unfold dl0_exit in PO.
    destruct PO as (a1' & s0' & s1' & s2' & s3' & s4' & m' & bs1' & bs2' & wl' & -> & MU' & WM' & MI'
                    & UB' & UBL' & ACCB' & UC' & UCL' & ACCC' & UL' & ULL' & ACCL').
    clear MI UB UBL ACCB UC UCL ACCC UL ULL ACCL G1 G2.
    lazymatch type of MU' with munch _ ?mo _ => transport_after_call asegs mo m' MU' WM' end.
    clear MU' WM'.
    idtac "MARK after loop".
    unfold SHB. eapply dll_finish; try eassumption; lia.
Qed.
