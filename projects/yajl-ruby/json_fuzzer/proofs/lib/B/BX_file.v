(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BM_syscalls.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation z64 := (Z_to_bv 64 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x97f68);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x980ac); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 z64;
   CB 80 tail].

End RC__1.
Notation A_STDOUT := 0xa9d58%Z (only parsing).       (* [comment removed for export] *)
Notation A_STDOUT_BUF := 0x601c60%Z (only parsing).   (* [comment removed for export] *)
Notation A_STDERR := 0xa9c68%Z (only parsing).       (* [comment removed for export] *)
Notation A_STDERR_BUF := 0x601c58%Z (only parsing).   (* [comment removed for export] *)
Notation A_STDIN := 0xa9e48%Z (only parsing).        (* [comment removed for export] *)
Notation A_STDOUT_USED := 0xa9e40%Z (only parsing).
Notation A_STDERR_USED := 0xa9d50%Z (only parsing).
Notation A_STDIN_USED := 0xa9f30%Z (only parsing).
Notation A_OFL_HEAD := 0x601c48%Z (only parsing).
Notation A_LIBC := 0x6017e0%Z (only parsing).         (* [comment removed for export] *)
Notation A_TP := 0x5e1550%Z (only parsing).           (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x98ab8%Z (only parsing).
Notation F_STDIO_WRITE := 0x980b4%Z (only parsing).
Notation A_STDIO_EXIT := 0x98694%Z (only parsing).

Notation RSTDOUT := 0xa9d58%Z (only parsing).
Notation RSTDOUT_BUF := 0x601c60%Z (only parsing).
Notation RSTDERR := 0xa9c68%Z (only parsing).

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells bsegs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells bsegs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

(* [comment removed for export] *)
Definition stderr_file (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells bsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE A_STDERR_BUF 0 2 mode 0xffffffff tail).

(* [comment removed for export] *)
Definition stdin_cells : list cell :=
  [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x97f68);
   C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x97f94);
   C8 z64; C8 (Z_to_bv 64 0x980ac); C8 (Z_to_bv 64 0x602068); C8 (Z_to_bv 64 1024);
   C8 z64; C8 z64; C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff); C4 z64; C4 z64;
   CB 80 (repeat (Z_to_bv 8 0) 80)].
Definition stdin_file (m : word -> option byte) : Prop := rw_cells bsegs m A_STDIN stdin_cells.

(* [comment removed for export] *)
Definition stderr_wfile (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells bsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE A_STDERR_BUF 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0%Z.
Lemma stderr_wfile_file : forall m, stderr_wfile m -> stderr_file m.
Proof. intros m (flags & mode & e & wend & tail & H & _). exists flags, mode, e, wend, tail. exact H. Qed.

Definition stderr_wfile0 (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells bsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE A_STDERR_BUF 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0%Z
    /\ (wend = 0 \/ (wend = A_STDERR_BUF /\ e = A_STDERR_BUF))%Z
    /\ (0 <= e < 2^63)%Z.
Lemma stderr_wfile0_wfile : forall m, stderr_wfile0 m -> stderr_wfile m.
Proof. intros m (flags & mode & e & wend & tail & H & FL & _ & _). exists flags, mode, e, wend, tail. split; [exact H| exact FL]. Qed.
Lemma stderr_wfile0_file : forall m, stderr_wfile0 m -> stderr_file m.
Proof. intros m H. apply stderr_wfile_file, stderr_wfile0_wfile, H. Qed.

(* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells bsegs m ssp_guard [C8 canary].

(* [comment removed for export] *)
Definition stdio_statics (m : word -> option byte) (cdt thr sec : byte) (tm1 : word) : Prop :=
     rw_cells bsegs m A_LIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]    (* [comment removed for export] *)
  /\ rw_cells bsegs m A_OFL_HEAD [C8 z64]                                          (* [comment removed for export] *)
  /\ rw_cells bsegs m A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)]
  /\ rw_cells bsegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)]
  /\ rw_cells bsegs m A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (A_STDOUT, A_STDOUT_USED); (A_STDOUT_BUF, A_STDOUT_BUF + 1024)]%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = []
      /\ stderr_file m'
      /\ ssp_cells m' guard.

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word) (P : acc -> Prop),
      (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k))%Z ->
      (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k))%Z ->
      (forall a, P (Z_to_bv 64 a, 0%nat)) ->                                   (* [comment removed for export] *)
      stk bsegs m lo (bv_unsigned sp) ->
      stdio_statics m cdt thr sec tm1 ->
      stdin_file m -> stdout_file m (get_so s) -> stderr_file m ->
      ssp_cells m guard ->
      mem_inv bsegs m ->
      (lo <= bv_unsigned sp - 160)%Z -> (0x603000 <= lo)%Z ->
      (bv_unsigned sp < 0x800000000000)%Z (* [comment removed for export] *) ->
      implMA bsegs P (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 A_STDIO_EXIT) fc None m (seg_rom bsegs)).
End StdioExitStatement.
End RC__2.
