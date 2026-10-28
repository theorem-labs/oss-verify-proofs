(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import FX_Layout FX_Stdio_iface.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation bsegs := ImageA.bsegs.
Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0).

Definition F_IFWRITE : Z := 0x6fe28.
Definition F_IFFLUSH : Z := 0x6fe88.
Definition F_IWCRTOMB : Z := 0x6fe6c.
Definition ICPT_DEPTH : Z := 4608.
Definition XTPLOC : Z := 0x6be3b8.

Definition XWI (lo hi : Z) : list (Z * Z) := [(lo, hi); (RSTDOUT, RSTDOUT + 232); (RSTDERR, RSTDERR + 232); (XTPLOC, XTPLOC + 8)].

Section Stmts.
  Variable IX : mem -> Prop.

  Variable XLO : Z.

  Definition IX_frame_stmt : Prop :=
    forall W lo hi m m', IX m -> munch W m m' -> wmono bsegs m m' -> XLO <= lo -> sub_fp W (XWI lo hi) -> IX m'.

  Definition ifwrite0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp : Z) (flags : word) (WP wfn bufp bufsize fd lbf : Z) (tail : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' Fp (file_cells flags (bufp + bufsize) WP bufp wfn bufp bufsize fd mode' lbf tail)
      /\ IX m'.
  Definition ifwrite0_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (Fp S : Z) (flags mode : word) (wend wpos wbase wfn bufp bufsize fd lbf : Z) (tail : list byte) (lo : Z),
      rw_cells bsegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
      ((wend = 0 /\ Z.land (bv_unsigned flags) 8 = 0) \/ (wend = bufp + bufsize /\ wbase = bufp /\ bufp <= wpos <= bufp + bufsize)) ->
      (lbf = 10 \/ lbf = 0xffffffff) ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 Fp -> (Fp = RSTDOUT \/ Fp = RSTDERR) ->
      (0 <= bufp) -> (0 <= bufsize) -> (0 < bufp + bufsize) -> (bufp + bufsize <= lo) ->
      (0 <= Fp) -> (Fp + 232 <= bufp) ->
      (bv_unsigned sp <= S < 2^64) ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - ICPT_DEPTH) -> (GLOBALS_TOP <= lo) -> (XLO <= lo) -> (bv_unsigned sp < 2^63) ->
      IX m -> mem_inv bsegs m ->
      evt bsegs (ifwrite0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags (if wend =? 0 then bufp else wpos) wfn bufp bufsize fd lbf tail lo m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 F_IFWRITE) fc None m (seg_rom bsegs)).

  Definition ifflush_idle_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp : Z) (flags mode : word) (wfn bufp bufsize fd lbf : Z) (tail : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' Fp (file_cells flags 0 0 0 wfn bufp bufsize fd mode lbf tail)
      /\ IX m'.
  Definition ifflush_idle_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (Fp : Z) (flags mode : word) (wend wpos wfn bufp bufsize fd lbf : Z) (tail : list byte) (lo : Z),
      rw_cells bsegs m Fp (file_cells flags wend wpos wpos wfn bufp bufsize fd mode lbf tail) ->
      a0 = Z_to_bv 64 Fp -> (Fp = RSTDOUT \/ Fp = RSTDERR) -> (0 < Fp) -> (Fp + 232 <= lo) -> (0 <= wpos < 2^64) ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - ICPT_DEPTH) -> (GLOBALS_TOP <= lo) -> (XLO <= lo) -> (bv_unsigned sp < 2^63) ->
      IX m -> mem_inv bsegs m ->
      evt bsegs (ifflush_idle_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags mode wfn bufp bufsize fd lbf tail lo m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 F_IFFLUSH) fc None m (seg_rom bsegs)).

  Definition iwcrtomb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (D lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (D, D + 4)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' D [CB 4 j']
      /\ IX m'.
  Definition iwcrtomb_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (D PS lo : Z) (j : list byte),
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 PS ->
      rw_cells bsegs m D [CB 4 j] -> (bv_unsigned sp <= D) -> (D + 4 < 2^63) ->
      rw_cells bsegs m PS [C8 z64] -> (0x6bc488 <= PS) -> (PS + 8 <= 0x6bcc28) ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - ICPT_DEPTH) -> (GLOBALS_TOP <= lo) -> (XLO <= lo) -> (bv_unsigned sp < 2^63) ->
      IX m -> mem_inv bsegs m ->
      evt bsegs (iwcrtomb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D lo m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 F_IWCRTOMB) fc None m (seg_rom bsegs)).

  Section Ev.
    Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
    Definition ifflush_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
        (flags : word) (tail : list byte) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
      fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem) (so' : stdout_st),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo (bv_unsigned sp)
        /\ so' = (if 0 <? zlength (so_buf (get_so st)) then so_after (get_so st) else get_so st)
        /\ st' = set_so so' st
        /\ rw_cells bsegs m' RSTDOUT (file_cells flags 0 0 0 (wfn_of so') RSTDOUT_BUF 1024 1 mode' (lbf_of so') tail)
        /\ ssp_cells m' canary
        /\ IX m'.
    Definition ifflush_stdout_stmt : Prop :=
      forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
             (flags mode : word) (tail : list byte) (bufbytes : list byte) (lo : Z) (canary : word),
        let so := get_so st in
        (so_active so = false -> so_buf so = []) ->
        rw_cells bsegs m RSTDOUT (stdout_cells so flags mode tail) ->
        Z.land (bv_unsigned flags) 72 = 0 ->
        rw_cells bsegs m RSTDOUT_BUF [CB 1024 bufbytes] -> firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so) -> (zlength (so_buf so) <= 1024) ->
        a0 = Z_to_bv 64 RSTDOUT ->
        stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - ICPT_DEPTH) -> (GLOBALS_TOP <= lo) -> (XLO <= lo) -> (bv_unsigned sp < 2^63) ->
        ssp_cells m canary -> IX m -> mem_inv bsegs m ->
        implM bsegs (stdout_exit_flush get_so set_so) st
              (ifflush_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags tail lo canary m st)
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 F_IFFLUSH) fc None m (seg_rom bsegs)).
  End Ev.
End Stmts.
