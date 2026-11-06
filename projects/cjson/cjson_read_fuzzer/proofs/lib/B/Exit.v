(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASTDOUT      : Z := 0xa5e18.   (* [comment removed for export] *)
Definition ASTDOUT_BUF  : Z := 0x5fd080.   (* [comment removed for export] *)
Definition ASTDERR      : Z := 0xa5d28.   (* [comment removed for export] *)
Definition ASTDERR_BUF  : Z := 0x5fd078.   (* [comment removed for export] *)
Definition ASTDIN       : Z := 0xa5f08.   (* [comment removed for export] *)
Definition ASTDIN_BUF   : Z := 0x5fd488.
Definition ASTDOUT_USED : Z := 0xa5f00.   (* [comment removed for export] *)
Definition ASTDERR_USED : Z := 0xa5e10.   (* [comment removed for export] *)
Definition ASTDIN_USED  : Z := 0xa5ff0.   (* [comment removed for export] *)
Definition AF_STDIO_CLOSE : Z := 0x93154.
Definition AF_STDIO_SEEK  : Z := 0x93298.
Definition AF_STDOUT_WRITE : Z := 0x93ca4.
Definition AF_STDIO_WRITE  : Z := 0x932a0.
Definition AF_STDIO_READ   : Z := 0x93180.  (* [comment removed for export] *)
Definition AF_STDIO_EXIT   : Z := 0x93880.  (* [comment removed for export] *)
Definition AEXIT     : Z := 0x8d998.      (* [comment removed for export] *)
Definition A_EXIT    : Z := 0x8d768.      (* [comment removed for export] *)
Definition AOFL_LOCK : Z := 0x5fd060.
Definition AOFL_HEAD : Z := 0x5fd068.
Definition AGOT_GUARD : Z := 0xa2388.     (* [comment removed for export] *)
Definition AGUARD     : Z := 0x5fc9b0.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_ATEXIT      : Z := 0x5fc9c0.   (* [comment removed for export] *)
Definition A_ATEXIT_CALL : Z := 0x8d944.    (* [comment removed for export] *)
Definition A_COVDUMP     : Z := 0x71944.    (* [comment removed for export] *)
Definition A_AEF_GUARD   : Z := 0x8230c.    (* [comment removed for export] *)
Definition A_ATEXITF     : Z := 0x8d880.    (* [comment removed for export] *)
Definition A_AEF_INIT    : Z := 0x5dc010.   (* [comment removed for export] *)
Definition AINCB         : Z := 0x5dc014.   (* [comment removed for export] *)
Definition A_LIBC        : Z := 0x5fcc00.   (* [comment removed for export] *)

Definition atex_cells (slot : Z) (fin f1 f2 f3 : bv 8) (pad : word) (fs : list cell) : list cell :=
  [C1 fin; C1 f1; C1 f2; C1 f3; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); C4 pad;
   C8 (Z_to_bv 64 (A_ATEXIT + 24)); C8 (Z_to_bv 64 0)] ++ fs.

Definition ATEX1 (m : mem) : Prop :=
  (exists (f1 f2 f3 : bv 8) (pad j1 : word),
      rw_cells bsegs m A_ATEXIT (atex_cells 1 (Z_to_bv 8 0) f1 f2 f3 pad [C8 (Z_to_bv 64 A_ATEXIT_CALL); C8 j1]))
  /\ (exists j2 : word, rw_cells bsegs m (A_ATEXIT + 296) [C8 j2])
  /\ rw_cells bsegs m AINCB [C1 (Z_to_bv 8 0)].
Definition ATEX2 (m : mem) : Prop :=
  (exists (f1 f2 f3 : bv 8) (pad : word),
      rw_cells bsegs m A_ATEXIT (atex_cells 2 (Z_to_bv 8 0) f1 f2 f3 pad [C8 (Z_to_bv 64 A_ATEXIT_CALL); C8 (Z_to_bv 64 A_ATEXIT_CALL)]))
  /\ rw_cells bsegs m (A_ATEXIT + 296) [C8 (Z_to_bv 64 A_AEF_GUARD)]
  /\ rw_cells bsegs m A_AEF_INIT [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m AINCB [C1 (Z_to_bv 8 0)].
Definition ATEX (m : mem) : Prop := ATEX1 m \/ ATEX2 m.

(* [comment removed for export] *)
Definition atex_addr (a : Z) : Prop :=
  (A_ATEXIT <= a < A_ATEXIT + 48) \/ (A_ATEXIT + 296 <= a < A_ATEXIT + 304) \/ (A_AEF_INIT <= a < A_AEF_INIT + 1) \/ (AINCB <= a < AINCB + 1).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells_r (flags : word) (wend wpos wbase readfn writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 AF_STDIO_CLOSE);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 readfn);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 AF_STDIO_SEEK); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 z64;
   CB 80 tail].
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  file_cells_r flags wend wpos wbase 0 writefn buf bufsize fd mode lbf tail.

(* [comment removed for export] *)
Definition stdout_file (m : mem) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells bsegs m ASTDOUT
      (file_cells flags
         (if so_active so then ASTDOUT_BUF + 1024 else 0)
         (if so_active so then ASTDOUT_BUF + zlength (so_buf so) else 0)
         (if so_active so then ASTDOUT_BUF else 0)
         (if so_first so then AF_STDOUT_WRITE else AF_STDIO_WRITE)
         ASTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff) tail)
    /\ Z.land (bv_unsigned flags) 72 = 0
    /\ rw_cells bsegs m ASTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ zlength (so_buf so) <= 1024
    /\ (so_active so = false -> so_buf so = []).

(* [comment removed for export] *)
Definition stdout_init : stdout_st := mkStdout false [] true true.

(* [comment removed for export] *)
Definition stderr_file (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells bsegs m ASTDERR (file_cells flags wend e e AF_STDIO_WRITE ASTDERR_BUF 0 2 mode 0xffffffff tail).

(* [comment removed for export] *)
Definition stderr_wfile (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells bsegs m ASTDERR (file_cells flags wend e e AF_STDIO_WRITE ASTDERR_BUF 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0.

Lemma stderr_wfile_file : forall m, stderr_wfile m -> stderr_file m.
Proof. intros m (flags & mode & e & wend & tail & H & _). exists flags, mode, e, wend, tail. exact H. Qed.

(* [comment removed for export] *)
Definition stdin_file (m : mem) : Prop :=
  exists tail : list byte,
    rw_cells bsegs m ASTDIN (file_cells_r (Z_to_bv 64 9) 0 0 0 AF_STDIO_READ 0 ASTDIN_BUF 1024 0 (Z_to_bv 64 0) 0 tail).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : mem) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (ASTDOUT, ASTDOUT + 232); (ASTDOUT_BUF, ASTDOUT_BUF + 1024)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = []
      /\ stderr_file m' /\ stdin_file m'
      /\ rw_cells bsegs m' AGOT_GUARD [C8 (Z_to_bv 64 AGUARD)] /\ rw_cells bsegs m' AGUARD [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk bsegs m lo (bv_unsigned sp) ->
      rw_cells bsegs m 0x5fcc00 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells bsegs m AOFL_HEAD [C8 z64] ->                                             (* [comment removed for export] *)
      rw_cells bsegs m ASTDIN_USED [C8 (Z_to_bv 64 ASTDIN)] ->
      rw_cells bsegs m ASTDOUT_USED [C8 (Z_to_bv 64 ASTDOUT)] ->
      rw_cells bsegs m ASTDERR_USED [C8 (Z_to_bv 64 ASTDERR)] ->
      stdout_file m (get_so s) -> stderr_file m -> stdin_file m ->
      rw_cells bsegs m AGOT_GUARD [C8 (Z_to_bv 64 AGUARD)] -> rw_cells bsegs m AGUARD [C8 guard] ->   (* [comment removed for export] *)
      mem_inv bsegs m ->
      (lo <= bv_unsigned sp - 160) -> (alloc_ceiling <= lo) ->
      implM bsegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 AF_STDIO_EXIT) fc None m (seg_rom bsegs)).
End StdioExitStatement.


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0) (only parsing).
