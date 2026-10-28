(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_iface D_defs X_aexdefs X_vecxdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition X_DEPTH : Z := 64 + 4864.

Definition aexX (v : option Z) (m : mem) : Prop :=
  match v with None => aex_main m \/ aex_reg m | Some _ => aex_lib m end.

Definition locx3A (m : mem) : Prop :=
  rw_cells bsegs m 0x6bcf40 [C8 (Z_to_bv 64 0x17e0b0)]
  /\ rw_cells bsegs m 0x6bd0d0 [C8 (Z_to_bv 64 0x17de00)]
  /\ rw_cells bsegs m (0x6bd0d0 + 16) [C8 (Z_to_bv 64 0x37998)].
Definition tplocA (m : mem) : Prop := rw_cells bsegs m (TP_A - 48) [C8 (Z_to_bv 64 (0x6de678 + 56))].
Definition libx (v : option Z) (m : mem) : Prop :=
  locx3A m /\ tplocA m
  /\ match v with
     | None => True
     | Some A8 => rw_cells bsegs m AEX_VEC_OBJ [C8 (Z_to_bv 64 A8); C8 (Z_to_bv 64 (A8 + 8)); C8 (Z_to_bv 64 (A8 + 8))] /\ A8 mod 16 = 0
     end.

Definition clean_file_cellsA (j0 : list byte) (rp : Z) (j1 : list byte) (wp : Z) (j2 : list byte) (j3 : list byte) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 rp); CB 16 j1; C8 (Z_to_bv 64 wp); CB 8 j2; C8 (Z_to_bv 64 wp); CB 76 j3; C4 (Z_to_bv 64 0xffffffff)].
Definition stdio_exit0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
         (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : list byte) (irp iwp orp owp erp ewp : Z) (cdt thr sec : byte) (tm1 : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32) -> (SEGTOP_A <= lo) ->
  rw_cells bsegs m 0x6de678 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  rw_cells bsegs m 0x6debe8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x184cc8 [C8 (Z_to_bv 64 0x184be0)] -> rw_cells bsegs m 0x184be0 (clean_file_cellsA i0 irp i1 iwp i2 i3) ->
  rw_cells bsegs m 0x184db8 [C8 (Z_to_bv 64 0x184cd0)] -> rw_cells bsegs m 0x184cd0 (clean_file_cellsA o0 orp o1 owp o2 o3) ->
  rw_cells bsegs m 0x184bd8 [C8 (Z_to_bv 64 0x184af0)] -> rw_cells bsegs m 0x184af0 (clean_file_cellsA e0 erp e1 ewp e2 e3) ->
  (0 <= irp < 2^64) -> (0 <= iwp < 2^64) -> (0 <= orp < 2^64) -> (0 <= owp < 2^64) -> (0 <= erp < 2^64) -> (0 <= ewp < 2^64) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x168690) fc None m (seg_rom bsegs)).

Section XIface.
Variable RT : rt_sig.
Variable XENV : mem -> Prop.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable LIBv : option Z -> mem -> Prop.

Definition exit_contract_imp : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (so : stdout_st) (code lo : Z) (v : option Z),
  a0 = Z_to_bv 64 code -> 0 <= code < 256 -> tp = Z_to_bv 64 TP_A ->
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  OUT_rep so m -> ERR_rep m -> XENV m ->
  aexX v m -> LIBv v m -> (forall A8, v = Some A8 -> In (A8, 8) (rt_live RT Σ)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + X_DEPTH <= bv_unsigned sp -> io_ssp m ->
  cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_exit m)))
    (evw 1 (so_buf so)) (EXITc fs0 code).
End XIface.
