(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Pj_loc_defs Pj_os_defs El_defs.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition EL_DUMP_STACK : Z := 8192.

Definition dump_W (lo q OS : Z) : list (Z * Z) := [(lo, q); (OS, OS + 288); (EL_TPLOC, EL_TPLOC + 8); (LX_ERRNO, LX_ERRNO + 4)].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition dump_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo OS : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ frm0 fc'
    /\ munch (dump_W lo q OS) m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ (exists (pb pp ep : word) (fill : Z) (dum j148 j284 : list byte), rw_cells usegs m' OS (os_cells OS pb pp ep fill dum j148 j284))
    /\ rw_cells usegs m' EL_TPLOC [C8 (wz EL_GLOC)]
    /\ (exists errv' : word, rw_cells usegs m' LX_ERRNO [C4 errv'])
    /\ LOCB m'.

Definition dump_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (q lo OS DOC TAPE SBUF : Z) (tws sbs : list Z) (canary errv : word),

    tape_wf (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) ck_any (Z.of_nat (length tws)) -> Forall (fun c => 0 <= c < 256) sbs ->
    rw_cells usegs m DOC [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF)] -> q <= DOC -> (DOC + 16 <= OS \/ OS + 288 <= DOC) -> DOC + 16 < 2 ^ 62 ->
    bytes_at usegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 < TAPE -> TAPE mod 8 = 0 -> TAPE + 8 * Z.of_nat (length tws) <= lo ->
    (TAPE + 8 * Z.of_nat (length tws) <= 0x10000 \/ 0x111000 <= TAPE) ->
    bytes_at usegs m SBUF (map (Z_to_bv 8) sbs) -> 0 < SBUF -> SBUF + Z.of_nat (length sbs) <= lo ->
    (SBUF + Z.of_nat (length sbs) <= 0x10000 \/ 0x111000 <= SBUF) ->

    OSFRESH m OS -> q <= OS -> OS + 288 < 2 ^ 62 -> OS mod 8 = 0 -> LOCB m -> pj_consts m -> ssp_cells m canary ->
    rw_cells usegs m EL_TPLOC [C8 (wz EL_GLOC)] -> rw_cells usegs m LX_ERRNO [C4 errv] ->

    stk usegs m lo q -> lo <= q - EL_DUMP_STACK -> GLOBALS_TOP <= lo -> q mod 16 = 0 -> mem_inv usegs m -> frm0 fc ->
    evt usegs (dump_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo OS m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 DOC) (Z_to_bv 64 (OS + 128)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_DUMP) fc None m (seg_rom usegs)).
End WithCeiling0.
