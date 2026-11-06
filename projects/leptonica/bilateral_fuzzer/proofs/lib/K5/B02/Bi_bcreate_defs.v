(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Km_setelem Km_iface Km_kit Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk Bi_iface BiV_defs LeptB_guard LeptB_guard2 LeptB_guard3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition bc_nc_exit (nc minval : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
  : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (ncs : list word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 (Z_to_bv 64 0) s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0xcf2d0) fc None m' (seg_rom asegs)
    /\ munch [(nc, nc + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' nc ncs /\ length ncs = 10%nat /\ Forall (fun w => 0 <= bv_unsigned w <= 255) ncs
    /\ nth_error ncs 0 = Some (Z_to_bv 64 minval).

Definition bc_nc_loop_stmt : Prop :=
  forall (nc pmin pmax minval maxval : Z) (ra sp gp tp t0 t1 t2 s0 s1 a4 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  0 < nc -> nc mod 16 = 0 -> nc + 40 <= 2^47 -> (nc + 40 <= 0x7fff7000 \/ 0x10007fff8000 <= nc) ->
  0 <= minval <= 255 -> 0 <= maxval <= 255 ->
  (forall m', munch [(nc, nc + 40)] m m' -> wmono asegs m m' ->
              rw_cells asegs m' pmin [C4 (Z_to_bv 64 minval)] /\ rw_cells asegs m' pmax [C4 (Z_to_bv 64 maxval)]
              /\ rw_cells asegs m' (bv_unsigned s1 + 104) [C8 (Z_to_bv 64 nc)]) ->
  wr_at asegs m nc 40 -> acc asegs m nc 40 -> mem_inv asegs m ->
  evt asegs (bc_nc_exit nc minval ra sp gp tp s0 s1 (Z_to_bv 64 pmin) (Z_to_bv 64 2147450880) (Z_to_bv 64 pmax) (Z_to_bv 64 9) s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 nc) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1) a4 (Z_to_bv 64 nc) a6 a7
             (Z_to_bv 64 pmin) (Z_to_bv 64 2147450880) (Z_to_bv 64 pmax) (Z_to_bv 64 9) (Z_to_bv 64 10) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xcf248) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition bc_karr_ro (pmin pmax minval maxval nc : Z) (ncs : list word) (slot slotv : Z) (m : mem) : Prop :=
  rw_cells asegs m pmin [C4 (Z_to_bv 64 minval)] /\ rw_cells asegs m pmax [C4 (Z_to_bv 64 maxval)]
  /\ u32arr asegs m nc ncs /\ acc asegs m nc 40 /\ rw_cells asegs m slot [C8 (Z_to_bv 64 slotv)].
Definition bc_kidx_exit (kidx nc S1 : Z) (ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem)
  : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ks : list word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 (Z_to_bv 64 S1) (Z_to_bv 64 kidx) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0xcf368) fc' None m' (seg_rom asegs)
    /\ fs_agree F F' /\ frm0 fc' /\ munch [(kidx, kidx + 1024); (S1 + 96, S1 + 104)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' kidx ks /\ kidx_ok 10 ks /\ rw_cells asegs m' (S1 + 96) [C8 (Z_to_bv 64 (18446744073709551615 - nc))].
Definition bc_kidx_stmt : Prop :=
  forall (kidx nc pmin pmax minval maxval S1 : Z) (ncs : list word) (x96 : word)
         (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  0 < kidx -> kidx mod 16 = 0 -> kidx + 1024 <= 2^47 -> (kidx + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= kidx) ->
  0 < nc -> nc mod 16 = 0 -> nc + 40 <= 2^47 -> (nc + 40 <= 0x7fff7000 \/ 0x10007fff8000 <= nc) ->
  0 <= minval <= 255 -> 0 <= maxval <= 255 -> length ncs = 10%nat -> Forall (fun w => 0 <= bv_unsigned w <= 255) ncs ->
  0x10007fff8000 <= S1 -> S1 + 224 <= 2^47 -> (S1 + 224 <= kidx \/ kidx + 1024 <= S1) -> frm0 fc ->
  (forall m', munch [(kidx, kidx + 1024); (S1 + 96, S1 + 104)] m m' -> wmono asegs m m' ->
       bc_karr_ro pmin pmax minval maxval nc ncs (S1 + 64) 10 m' /\ rw_cells asegs m' (S1 + 104) [C8 (Z_to_bv 64 nc)]) ->
  rw_cells asegs m (S1 + 96) [C8 x96] ->
  rw_cells asegs m kidx [CB (Z.to_nat 1024) (repeat (Z_to_bv 8 0) (Z.to_nat 1024))] -> acc asegs m kidx 1024 -> mem_inv asegs m ->
  evt asegs (bc_kidx_exit kidx nc S1 ra sp gp tp s0 (Z_to_bv 64 pmin) (Z_to_bv 64 2147450880) (Z_to_bv 64 pmax) (Z_to_bv 64 9) (Z_to_bv 64 nc)
                           s7 s8 s9 s10 s11 F m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 kidx) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 pmin) (Z_to_bv 64 2147450880) (Z_to_bv 64 pmax) (Z_to_bv 64 9) (Z_to_bv 64 nc) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xcf300) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition bc_kfr_exit (kfr S1 : Z) (ra sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem)
  : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (kfs : list Z),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 (Z_to_bv 64 S1) (Z_to_bv 64 kfr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  (Z_to_bv 64 11) t4' t5' t6')
             F' (Z_to_bv 64 0xcf3f0) fc' None m' (seg_rom asegs)
    /\ fs_agree F F' /\ frm0 fc' /\ munch [(kfr, kfr + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ kfr_vals m' kfr kfs /\ wr_at asegs m' kfr 1024.
Definition bc_kfr_stmt : Prop :=
  forall (kfr nc pmin pmax minval maxval S1 : Z) (ncs : list word)
         (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  0 < kfr -> kfr mod 16 = 0 -> kfr + 1024 <= 2^47 -> (kfr + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= kfr) ->
  0 < nc -> nc mod 16 = 0 -> nc + 40 <= 2^47 -> (nc + 40 <= 0x7fff7000 \/ 0x10007fff8000 <= nc) ->
  0 <= minval <= 255 -> 0 <= maxval <= 255 -> length ncs = 10%nat -> Forall (fun w => 0 <= bv_unsigned w <= 255) ncs ->
  nth_error ncs 0 = Some (Z_to_bv 64 minval) ->
  0x10007fff8000 <= S1 -> S1 + 224 <= 2^47 -> (S1 + 224 <= kfr \/ kfr + 1024 <= S1) -> frm0 fc ->
  (forall m', munch [(kfr, kfr + 1024)] m m' -> wmono asegs m m' ->
       bc_karr_ro pmin pmax minval maxval nc ncs (S1 + 80) 11 m' /\ rw_cells asegs m' (S1 + 104) [C8 (Z_to_bv 64 nc)]
       /\ rw_cells asegs m' (S1 + 96) [C8 (Z_to_bv 64 (18446744073709551615 - nc))]) ->
  rw_cells asegs m kfr [CB (Z.to_nat 1024) (repeat (Z_to_bv 8 0) (Z.to_nat 1024))] -> acc asegs m kfr 1024 -> mem_inv asegs m ->
  evt asegs (bc_kfr_exit kfr S1 ra sp gp tp s0 (Z_to_bv 64 pmin) (Z_to_bv 64 2147450880) (Z_to_bv 64 pmax) (Z_to_bv 64 9) s6 s7 s8 s9 s10 s11 F m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 kfr) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 pmin) (Z_to_bv 64 2147450880) (Z_to_bv 64 pmax) (Z_to_bv 64 9) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xcf394) fc None m (seg_rom asegs)).
