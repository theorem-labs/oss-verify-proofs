(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Pj_loc_defs Pj_os_defs El_os_defs El_ins_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition EL_ESC : Z := 0x404f4.
Definition ESC_DEPTH : Z := 6336.

Definition esc_post (ra : word) (sp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo OS : Z) (j148 j284 : list byte) (canary : word) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (pb : word) (pp ep fill' : Z) (dum : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 sp) gp (Z_to_bv 64 0xef588) t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ frm0 fc'
    /\ munch [(lo, sp); (OS, OS + 288); (0xef558, 0xef558 + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo sp
    /\ rw_cells usegs m' OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill' dum j148 j284) /\ PUTINV OS pp ep /\ FILLOK fill'
    /\ rw_cells usegs m' 0xef558 [C8 (Z_to_bv 64 0x10f850)] /\ ssp_cells m' canary /\ LOCB m'.

Definition esc_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (sp lo OS SV P L fill pp ep : Z) (pb : word) (dum j148 j284 : list byte) (bs : list byte) (canary : word),
    stk usegs m lo sp -> lo <= sp - ESC_DEPTH -> 0x111000 <= lo -> sp mod 16 = 0 ->
    rw_cells usegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) -> PUTINV OS pp ep -> FILLOK fill ->
    sp <= OS -> OS + 288 < 2 ^ 62 -> OS mod 8 = 0 ->
    rw_cells usegs m SV [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 L)] -> sp <= SV -> SV + 16 < 2 ^ 62 -> (SV + 16 <= OS \/ OS + 288 <= SV) ->
    bytes_at usegs m P bs -> Z.of_nat (length bs) = L -> 0 < P -> P + L <= lo -> (P + L <= 0x10000 \/ 0x111000 <= P) ->
    rw_cells usegs m 0xef558 [C8 (Z_to_bv 64 0x10f850)] -> ssp_cells m canary -> frm0 fc -> LOCB m -> el_dcc m -> mem_inv usegs m ->
    evt usegs (esc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo OS j148 j284 canary m)
      (MS (mkR ra (Z_to_bv 64 sp) gp (Z_to_bv 64 0xef588) t0 t1 t2 s0 s1 (Z_to_bv 64 (OS + 128)) (Z_to_bv 64 SV) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_ESC) fc None m (seg_rom usegs)).
