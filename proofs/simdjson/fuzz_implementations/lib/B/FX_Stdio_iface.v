(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Export FX_Exit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Section StdioRules.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Lemma implM_rdso : forall {A} (f : stdout_st -> M St A) (s : St) Q ms,
    implM bsegs (f (get_so s)) s Q ms -> implM bsegs (Monad.mbind (rd_so get_so) f) s Q ms.
  Proof. intros A f s Q ms H. exact H. Qed.
  Lemma implM_updso : forall {A} (g : stdout_st -> stdout_st) (f : unit -> M St A) (s : St) Q ms,
    implM bsegs (f tt) (set_so (g (get_so s)) s) Q ms -> implM bsegs (Monad.mbind (upd_so get_so set_so g) f) s Q ms.
  Proof. intros A g f s Q ms H. exact H. Qed.
  Lemma implM_updso_last : forall (g : stdout_st -> stdout_st) (s : St) (Q : unit -> St -> machine_state -> Prop) ms,
    Q tt (set_so (g (get_so s)) s) ms -> implM bsegs (upd_so get_so set_so g) s Q ms.
  Proof. intros g s Q ms H. apply implM_upd. apply evt_done. exact H. Qed.
End StdioRules.

Definition STDIO_WRITE : Z := 0x1680b0.
Definition STDIO_WRITE_DEPTH : Z := 112.

Section StdioWrite.
  Context {St : Type}.

  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
      (l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
      /\ ssp_cells m' canary
      /\ st' = st.

  Definition stdio_write_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (buf s : list Z) (S lo : Z) (canary : word),
      rw_cells bsegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      bytes_at bsegs m B (to_bytes buf) ->
      bytes_at bsegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (fd = 1 \/ fd = 2) ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      ssp_cells m canary -> mem_inv bsegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize < 2^64) ->
      (zlength buf + zlength s <= 2^26) -> (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (S = 0 \/ 0 < zlength s) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      (B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
      implM bsegs (stdio_writev (St:=St) fd buf s) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1680b0) fc None m (seg_rom bsegs)).
End StdioWrite.

Definition wfn_of (so : stdout_st) : Z := if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (so : stdout_st) : Z := if so_lbf_nl so then 10 else 0xffffffff.
Definition stdout_cells (so : stdout_st) (flags mode : word) (tail : list byte) : list cell :=
  file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF (wfn_of so) RSTDOUT_BUF 1024 1 mode (lbf_of so) tail.

Definition STDOUT_WRITE_DEPTH : Z := 144.

Section StdoutWrite.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition so_after (so : stdout_st) : stdout_st :=
    mkStdout true [] (if so_first so then false else so_lbf_nl so) false.

  Definition stdout_writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (flags mode : word) (tail : list byte) (l : Z) (lo : Z) (canary : word) (m : mem) (st : St)
      : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - STDOUT_WRITE_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' RSTDOUT (stdout_cells (so_after (get_so st)) flags mode tail)
      /\ ssp_cells m' canary
      /\ st' = set_so (so_after (get_so st)) st.

  Definition stdout_writefn_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (flags mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      let so := get_so st in
      so_active so = true ->
      rw_cells bsegs m RSTDOUT (stdout_cells so flags mode tail) ->
      Z.land (bv_unsigned flags) 64 = 0 ->
      bytes_at bsegs m RSTDOUT_BUF (to_bytes (so_buf so)) -> (zlength (so_buf so) <= 1024) ->
      bytes_at bsegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDOUT_WRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      ssp_cells m canary -> mem_inv bsegs m ->
      (zlength s <= 2^26 - 1024) -> (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (S = 0 \/ 0 < zlength s) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= RSTDOUT \/ RSTDOUT + 232 <= S))) ->
      implM bsegs (stdout_writefn get_so set_so s) st
            (stdout_writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (wfn_of so)) fc None m (seg_rom bsegs)).
End StdoutWrite.

Definition stderr_wfile (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells bsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x6dec00 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0.
Lemma stderr_wfile_file : forall m, stderr_wfile m -> stderr_file m.
Proof. intros m (flags & mode & e & wend & tail & H & _). exists flags, mode, e, wend, tail. exact H. Qed.

Definition stderr_wfile0 (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells bsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x6dec00 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0
    /\ (wend = 0 \/ (wend = 0x6dec00 /\ e = 0x6dec00))
    /\ 0 <= e < 2^63.
Lemma stderr_wfile0_wfile : forall m, stderr_wfile0 m -> stderr_wfile m.
Proof. intros m (flags & mode & e & wend & tail & H & FL & _ & _). exists flags, mode, e, wend, tail. split; [exact H| exact FL]. Qed.
Lemma stderr_wfile0_file : forall m, stderr_wfile0 m -> stderr_file m.
Proof. intros m H. apply stderr_wfile_file, stderr_wfile0_wfile, H. Qed.

Definition FWRITE_DEPTH : Z := 240.

Section Fwrite.
  Context {St : Type}.

  Definition fwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.

  Definition fwrite_diag_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      stderr_wfile0 m ->
      bytes_at bsegs m (bv_unsigned a0) (map (fun z => Z_to_bv 8 z) s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^25 ->
      a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv bsegs m ->
      implM bsegs (stderr_fwrite s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x168e70) fc None m (seg_rom bsegs)).
End Fwrite.
