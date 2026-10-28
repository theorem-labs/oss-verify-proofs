(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit Pj_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Export El_os_defsA El_ins_ifaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition EL_ESC_STACK_A : Z := 13056 + RT_STACK.

Definition esc_costA (L : Z) : Z := 1 + 4 * L.

Definition ESC_W (F : Z) : list (Z * Z) := [(F + 144, F + 144 + 288); (0x6abdb8, 0x6abdb8 + 8)].

Section Stmts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition esc_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (F q lo SV P L fill p n8 : Z) (bs : list byte)
         (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (F, 3%nat) (rt_frames RT Σ) ->
  OSX m (F + 144) fill -> FILLOK fill -> bytes_at bsegs m (shad (F + 144)) (repeat z8 36) -> LOCBA m -> el_tploc m -> io_ssp m -> frm0 fc ->
  rw_cells bsegs m SV [C8 (wz P); C8 (wz L)] -> q <= SV -> SV + 16 <= USTACK_TOP - 16 -> SV mod 8 = 0 ->
  bytes_at bsegs m P bs -> Z.of_nat (length bs) = L -> 0 <= L ->
  In (p, n8) (rt_live RT Σ) -> p mod 8 = 0 -> n8 mod 8 = 0 -> p <= P -> P + L <= p + n8 ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo -> lo + EL_ESC_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 32 = 0 ->
  (length (rt_frames RT Σ) + 4 <= FRAMES_MAX)%nat -> esc_costA L <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (FR' : bvmap 5 word) (fc' : bv 32) m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> (exists fill', OSX m' (F + 144) fill' /\ FILLOK fill') ->
     bytes_at bsegs m' (shad (F + 144)) (repeat z8 36) -> LOCBA m' -> el_tploc m' -> frm0 fc' ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - esc_costA L <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q (ESC_W F) m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (F + 272)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                FR' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (F + 272)) (wz SV) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            FR (wz 0xb0da0) fc None m (seg_rom bsegs)).
End Stmts.
