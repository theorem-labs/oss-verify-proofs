(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Export El_os_defsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition EL_PUT_STACK_A : Z := 4096 + RT_STACK.
Definition EL_INS_STACK_A : Z := 12288 + RT_STACK.
Definition EL_INSD_STACK_A : Z := 12288 + RT_STACK.
Definition EL_SETFILL_STACK_A : Z := 160 + RT_STACK.

Definition el_tploc (m : mem) : Prop := rw_cells bsegs m 0x6ab338 [C8 (Z_to_bv 64 0x6cb630)].

Definition OSXW (m : mem) (OS FL W fill : Z) : Prop :=
  exists pb pp ep dum j148 j284,
    rw_cells bsegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) FL W fill dum j148 j284) /\ PUTINV OS pp ep.
Lemma OSX_W : forall m OS fill, OSX m OS fill <-> OSXW m OS 0x1002 0 fill.
Proof. intros. reflexivity. Qed.
Lemma OSXW_agree : forall m m' OS FL W fill, OSXW m OS FL W fill -> agree_on (fun a => OS <= a < OS + 288) m m' -> wmono bsegs m m' -> OSXW m' OS FL W fill.
Proof.
  intros m m' OS FL W fill (pb & pp & ep & dum & j148 & j284 & H & PI) AG WM. exists pb, pp, ep, dum, j148, j284.
  split; [| exact PI]. apply (rw_cells_agree bsegs m m' _ _ H); [| exact WM]. intros a Ha. apply AG. rewrite os_cellsX_size in Ha. lia.
Qed.

Definition dword_fin (w : Z) : Prop := Z.land (Z.shiftr w 52) 2047 <> 2047.

Section Stmts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition os_put_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS BUF N CAP q lo fO fill : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (bs : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  OSX m OS fill -> FILLOK fill -> os_hullA m OS -> LOCBA m ->
  bytes_at bsegs m BUF bs -> Z.of_nat (length bs) = CAP -> 0 <= N <= CAP -> CAP <= 2^40 -> 0 < BUF -> acc bsegs m BUF N -> srcA RT Σ q BUF CAP bs ->
  (BUF + CAP <= OS \/ OS + 288 <= BUF) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + EL_PUT_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  Z.of_nat (length (rt_frames RT Σ)) + 2 <= FRAMES_TOT -> 2 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> OSX m' OS (fill_after fill) -> os_hullA m' OS -> LOCBA m' ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 2 <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS, OS + 288)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (OS + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (OS + 128)) (wz BUF) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0xb13cc) fc None m (seg_rom bsegs)).

Definition ins_cpsA (ENTRY : Z) (VOKP : Z -> Prop) (FL W : Z) (fills : Z -> Prop) (DEPTH : Z) : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS q lo fO fill v : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  OSXW m OS FL W fill -> fills fill -> os_hullA m OS -> LOCBA m -> el_tploc m -> io_ssp m -> VOKP v -> frm0 fc ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + DEPTH <= q ->
  q + 16 <= USTACK_TOP -> q mod 32 = 0 ->
  Z.of_nat (length (rt_frames RT Σ)) + 1 <= FRAMES_TOT -> 1 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> OSXW m' OS FL 0 (fill_after fill) -> os_hullA m' OS -> LOCBA m' -> el_tploc m' ->
     frm0 fc' ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS, OS + 288); (0x6ab338, 0x6ab338 + 8)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (OS + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (OS + 128)) (wz v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ENTRY) fc None m (seg_rom bsegs)).

Definition ins_ul_cpsA : Prop := ins_cpsA 0x111dd8 (fun v => 0 <= v < 2^64) 0x1002 0 FILLOK EL_INS_STACK_A.
Definition ins_u_cpsA : Prop := ins_cpsA 0x112950 (fun v => 0 <= v < 2^64) 0x1002 0 FILLOK EL_INS_STACK_A.
Definition ins_l_cpsA : Prop := ins_cpsA 0x111c0c (fun v => -2^63 <= v < 2^63) 0x1002 0 FILLOK EL_INS_STACK_A.
Definition ins_i_cpsA : Prop := ins_cpsA 0x11274c (fun v => 0 <= v < 256) 0x1008 4 (fun f => f = 0x30) EL_INS_STACK_A.

Definition ins_d_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS q lo fO fill : Z) (kO : nat) (dw : word)
         (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  OSXW m OS 0x1002 0 fill -> FILLOK fill -> os_hullA m OS -> LOCBA m -> el_tploc m -> io_ssp m -> reg_get F (Z_to_bv 5 10) = dw -> frm0 fc ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + EL_INSD_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 32 = 0 ->
  Z.of_nat (length (rt_frames RT Σ)) + 1 <= FRAMES_TOT -> 1 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> OSXW m' OS 0x1002 0 (fill_after fill) -> os_hullA m' OS -> LOCBA m' -> el_tploc m' ->
     frm0 fc' ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS, OS + 288); (0x6ab338, 0x6ab338 + 8)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (OS + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (OS + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x111fa4) fc None m (seg_rom bsegs)).

Definition setfill_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS q lo fO CP FL W fill c : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  OSXW m OS FL W fill -> (fill = 0x20 \/ fill = 0x30) -> os_hullA m OS ->
  bytes_at bsegs m CP [Z_to_bv 8 c] -> 0 <= c < 256 -> q <= CP -> CP + 1 <= USTACK_TOP - 16 ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + EL_SETFILL_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 32 = 0 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> OSXW m' OS FL W c -> os_hullA m' OS ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS + 280, OS + 284)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (OS + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (OS + 128)) (wz CP) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0xb2004) fc None m (seg_rom bsegs)).
End Stmts.
