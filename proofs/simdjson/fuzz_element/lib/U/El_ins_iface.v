(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout El_os_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation INS_DEPTH := 6192%Z (only parsing).
Notation INSD_DEPTH := 6288%Z (only parsing).

Definition fill_after (fill : Z) : Z := if (fill =? 0xffffffff)%Z then 0x20%Z else fill.

Definition dword_fin (w : Z) : Prop := (Z.land (Z.shiftr w 52) 2047 <> 2047)%Z.

Definition os_putX_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo OS fill : Z) (j148 j284 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 pb (pp ep : Z) dum m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - PJ_OS_PUT_STACK, bv_unsigned sp); (OS, OS + 288)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 (fill_after fill) dum j148 j284) /\ PUTINV OS pp ep
    /\ LOCB m'.

Definition os_putX_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS BUF N CAP fill pp ep : Z) (pb : word) (dum bs j148 j284 : list byte),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PJ_OS_PUT_STACK)%Z -> (0x111000 <= lo)%Z ->
  rw_cells usegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) -> PUTINV OS pp ep -> FILLOK fill ->
  LOCB m -> (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z -> (OS mod 8 = 0)%Z ->
  bytes_at usegs m BUF bs -> Z.of_nat (length bs) = CAP -> (0 <= N <= CAP)%Z -> (0 < BUF)%Z -> (BUF + CAP < 2^62)%Z ->
  (BUF + CAP <= lo \/ OS + 288 <= BUF \/ (bv_unsigned sp <= BUF /\ BUF + CAP <= OS))%Z ->
  el_dcc m -> mem_inv usegs m ->
  evt usegs (os_putX_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS fill j148 j284 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 BUF) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_OS_PUT) fc None m (seg_rom usegs)).

Definition ins_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo OS FL fill' : Z) (j148 j284 : list byte) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) pb (pp ep : Z) dum m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (OS, OS + 288); (0xef558, 0xef558 + 8)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k)
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells usegs m' OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) FL 0 fill' dum j148 j284) /\ PUTINV OS pp ep
    /\ rw_cells usegs m' 0xef558 [C8 (Z_to_bv 64 0x10f850)]
    /\ LOCB m'.

Definition ins_pre (ENTRY : Z) (VOKP : Z -> Prop) (FL W : Z) (fills : Z -> Prop) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill v pp ep : Z) (pb : word) (dum j148 j284 : list byte) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - INS_DEPTH)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  tp = Z_to_bv 64 (0xef558 + 48) ->
  rw_cells usegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) FL W fill dum j148 j284) -> PUTINV OS pp ep -> fills fill ->
  (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z -> (OS mod 8 = 0)%Z -> VOKP v ->
  rw_cells usegs m 0xef558 [C8 (Z_to_bv 64 0x10f850)] -> ssp_cells m canary -> frm0 fc ->
  LOCB m -> el_dcc m -> mem_inv usegs m ->
  evt usegs (ins_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS FL (fill_after fill) j148 j284 canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition ins_ul_stmt : Prop := ins_pre EL_INS_UL (fun v => 0 <= v < 2^64)%Z 0x1002 0 FILLOK.
Definition ins_u_stmt : Prop := ins_pre EL_INS_U (fun v => 0 <= v < 2^64)%Z 0x1002 0 FILLOK.
Definition ins_l_stmt : Prop := ins_pre EL_INS_L (fun v => -2^63 <= v < 2^63)%Z 0x1002 0 FILLOK.
Definition ins_i_stmt : Prop := ins_pre EL_INS_I (fun v => 0 <= v < 2^32)%Z 0x1008 4 (fun f => f = 0x30)%Z.

Definition ins_d_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill pp ep : Z) (dw pb : word) (dum j148 j284 : list byte) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - INSD_DEPTH)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  tp = Z_to_bv 64 (0xef558 + 48) ->
  rw_cells usegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) -> PUTINV OS pp ep -> FILLOK fill ->
  (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z -> (OS mod 8 = 0)%Z ->
  reg_get F (Z_to_bv 5 10) = dw ->
  rw_cells usegs m 0xef558 [C8 (Z_to_bv 64 0x10f850)] -> ssp_cells m canary -> frm0 fc ->
  LOCB m -> el_dcc m -> mem_inv usegs m ->
  evt usegs (ins_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS 0x1002 (fill_after fill) j148 j284 canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_INS_D) fc None m (seg_rom usegs)).

Definition setfill_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo OS : Z) (pb pp ep : word) (FL W c : Z) (dum j148 j284 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (OS + 280, OS + 284)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' OS (os_cellsX OS pb pp ep FL W c dum j148 j284).

Definition setfill_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS CP FL W fill c : Z) (pb pp ep : word) (dum j148 j284 : list byte),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (0x111000 <= lo)%Z ->
  rw_cells usegs m OS (os_cellsX OS pb pp ep FL W fill dum j148 j284) -> (fill = 0x20 \/ fill = 0x30)%Z ->
  (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z -> (OS mod 8 = 0)%Z ->
  rw_cells usegs m CP [C1 (Z_to_bv 8 c)] -> (0 <= c < 256)%Z -> (bv_unsigned sp <= CP)%Z -> (CP + 1 < 2^62)%Z -> (CP + 1 <= OS \/ OS + 288 <= CP)%Z ->
  el_dcc m -> mem_inv usegs m ->
  evt usegs (setfill_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS pb pp ep FL W c dum j148 j284 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 CP) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_SETFILL) fc None m (seg_rom usegs)).
