(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_STDERR_USED : Z := 0xa9b98.
Definition A_STDIN_USED : Z := 0xa9c88.
Definition A_STDOUT_USED : Z := 0xa9d78.
(* [comment removed for export] *)
Definition stdio_static (a : Z) : Prop := (0xa9ab0 <= a < 0xa9d80) \/ (0x601ca8 <= a < 0x6024d0).

(* [comment removed for export] *)
Definition stdin_cells : list cell :=
  file_cells (Z_to_bv 64 9) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ 0 F_STDIO_SEEK A_STDIN_BUF 1024 0 0 0 (Z_to_bv 64 0) 0 (repeat (Z_to_bv 8 0) 80).

(* [comment removed for export] *)
Definition wfn_of (f : file_st) : Z := if f_stdoutw f then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (f : file_st) : Z := if f_lbf_nl f then 10 else 0xffffffff.

(* [comment removed for export] *)
Definition flags_ok (f : file_st) (flags : word) : Prop :=
  Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0)
  /\ Z.land (bv_unsigned flags) F_NOWR = (if f_nowr f then F_NOWR else 0)
  /\ Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0)
  /\ Z.land (bv_unsigned flags) F_ERR = 0
  /\ Z.land (bv_unsigned flags) F_SVB = 0
  /\ Z.land (bv_unsigned flags) F_PERM = (if f_chan f then F_PERM else 0).   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FILE_R (m : mem) (f : file_st) (Fp BA closefn readfn seekfn prev next : Z) : Prop :=
  exists (flags mode : word) (rp : Z) (tail bufbytes : list byte),
     rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
          (if f_wactive f then BA + f_bufsize f else 0) (if f_wactive f then BA + zlength (f_wbuf f) else 0) (if f_wactive f then BA else 0)
          readfn (wfn_of f) seekfn BA (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)
  /\ flags_ok f flags
  /\ rw_cells asegs m BA [CB (Z.to_nat (f_bufsize f)) bufbytes]
  /\ firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f)
  /\ (f_wactive f = false -> f_wbuf f = [])
  /\ zlength (f_wbuf f) <= f_bufsize f
  /\ (f_rbuf f <> [] -> BA <= rp /\ rp + zlength (f_rbuf f) <= BA + f_bufsize f
                       /\ firstn (length (f_rbuf f)) (skipn (Z.to_nat (rp - BA)) bufbytes) = to_bytes (f_rbuf f))
  /\ 0 <= rp /\ rp + zlength (f_rbuf f) < 2^63
  /\ firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition heap_file_inv (f : file_st) : Prop :=
  f_chan f = false /\ 3 <= f_fd f < 2^31 /\ f_bufsize f = BUFSIZ
  /\ f_nord f = negb (f_nowr f) /\ (f_nowr f = true -> f_wactive f = false /\ f_wbuf f = []) /\ (f_nord f = true -> f_rbuf f = [])
  /\ Forall (fun z => 0 <= z < 256) (f_rbuf f).
Definition stdout_inv (f : file_st) : Prop :=
  f_chan f = true /\ f_fd f = 1 /\ f_bufsize f = BUFSIZ /\ f_nord f = true /\ f_nowr f = false /\ f_eof f = false /\ f_rbuf f = []
  /\ (f_stdoutw f = true -> f_lbf_nl f = true).
Definition stderr_inv (f : file_st) : Prop :=
  f_chan f = true /\ f_fd f = 2 /\ f_bufsize f = 0 /\ f_nord f = true /\ f_nowr f = false /\ f_eof f = false /\ f_rbuf f = []
  /\ f_stdoutw f = false /\ f_lbf_nl f = false.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithPtr.
  Context {hptr : Type}.
  Notation cblk := (hptr * Z * Z)%type.
  Definition hd_addr (FB : list cblk) : Z := match FB with [] => 0 | (_, A, _) :: _ => A end.

  (* [comment removed for export] *)
  Fixpoint files_R (m : mem) (prev : Z) (fs : list (hptr * file_st)) (FB : list cblk) : Prop :=
    match fs, FB with
    | [], [] => True
    | (q, f) :: fs', (q', A, n) :: FB' =>
        q' = q /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
        /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK prev (hd_addr FB')
        /\ heap_file_inv f
        /\ files_R m A fs' FB'
    | _, _ => False
    end.

  Definition STDIOR (l : @libc_st hptr) (FB : list cblk) (m : mem) : Prop :=
       FILE_R m (lc_stdout l) A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 /\ stdout_inv (lc_stdout l)
    /\ FILE_R m (lc_stderr l) A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 /\ stderr_inv (lc_stderr l)
    /\ rw_cells asegs m A_STDIN stdin_cells
    /\ rw_cells asegs m A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)]
    /\ rw_cells asegs m A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)]
    /\ rw_cells asegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)]
    /\ rw_cells asegs m A_OFL_LOCK [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr FB))]
    /\ files_R m 0 (lc_files l) FB
    /\ List.NoDup (map fst (lc_files l)).

  (* [comment removed for export] *)
  Definition stdio_init_stmt : Prop :=
    forall m,
      rw_cells asegs m A_STDOUT (file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDOUT_WRITE F_STDIO_SEEK A_STDOUT_BUF 1024 0 0 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells asegs m A_STDERR (file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDIO_WRITE F_STDIO_SEEK A_STDERR_BUF 0 0 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells asegs m A_STDIN stdin_cells ->
      (exists bb, rw_cells asegs m A_STDOUT_BUF [CB 1024 bb]) -> rw_cells asegs m A_STDERR_BUF [CB 0 []] ->
      rw_cells asegs m A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)] -> rw_cells asegs m A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)] ->
      rw_cells asegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)] ->
      rw_cells asegs m A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells asegs m A_OFL_HEAD [C8 (Z_to_bv 64 0)] ->
      STDIOR libc_init [] m.

  (* [comment removed for export] *)
  Definition stdio_frame_stmt : Prop :=
    forall l FB m m' W,
      STDIOR l FB m -> munch W m m' -> wmono asegs m m' ->
      Forall (fun iv => (snd iv <= 0xa9ab0 \/ 0xa9d80 <= fst iv) /\ (snd iv <= 0x601ca8 \/ 0x6024d0 <= fst iv)) W ->
      Forall (fun iv => Forall (fun b => snd iv <= snd (fst b) \/ snd (fst b) + snd b <= fst iv) FB) W ->
      STDIOR l FB m'.
End WithPtr.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_STDERR_USED : Z := 0xa9f78.
Definition A_STDIN_USED : Z := 0xaa068.
Definition A_STDOUT_USED : Z := 0xaa158.
(* [comment removed for export] *)
Definition stdio_static (a : Z) : Prop := (0xa9e90 <= a < 0xaa160) \/ (0x6020a8 <= a < 0x6028d0).

(* [comment removed for export] *)
Definition stdin_cells : list cell :=
  file_cells (Z_to_bv 64 9) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ 0 F_STDIO_SEEK A_STDIN_BUF 1024 0 0 0 (Z_to_bv 64 0) 0 (repeat (Z_to_bv 8 0) 80).

(* [comment removed for export] *)
Definition wfn_of (f : file_st) : Z := if f_stdoutw f then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (f : file_st) : Z := if f_lbf_nl f then 10 else 0xffffffff.

(* [comment removed for export] *)
Definition flags_ok (f : file_st) (flags : word) : Prop :=
  Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0)
  /\ Z.land (bv_unsigned flags) F_NOWR = (if f_nowr f then F_NOWR else 0)
  /\ Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0)
  /\ Z.land (bv_unsigned flags) F_ERR = 0
  /\ Z.land (bv_unsigned flags) F_SVB = 0
  /\ Z.land (bv_unsigned flags) F_PERM = (if f_chan f then F_PERM else 0).   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FILE_R (m : mem) (f : file_st) (Fp BA closefn readfn seekfn prev next : Z) : Prop :=
  exists (flags mode : word) (rp : Z) (tail bufbytes : list byte),
     rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
          (if f_wactive f then BA + f_bufsize f else 0) (if f_wactive f then BA + zlength (f_wbuf f) else 0) (if f_wactive f then BA else 0)
          readfn (wfn_of f) seekfn BA (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)
  /\ flags_ok f flags
  /\ rw_cells asegs m BA [CB (Z.to_nat (f_bufsize f)) bufbytes]
  /\ firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f)
  /\ (f_wactive f = false -> f_wbuf f = [])
  /\ zlength (f_wbuf f) <= f_bufsize f
  /\ (f_rbuf f <> [] -> BA <= rp /\ rp + zlength (f_rbuf f) <= BA + f_bufsize f
                       /\ firstn (length (f_rbuf f)) (skipn (Z.to_nat (rp - BA)) bufbytes) = to_bytes (f_rbuf f))
  /\ 0 <= rp /\ rp + zlength (f_rbuf f) < 2^63
  /\ firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition heap_file_inv (f : file_st) : Prop :=
  f_chan f = false /\ 3 <= f_fd f < 2^31 /\ f_bufsize f = BUFSIZ
  /\ f_nord f = negb (f_nowr f) /\ (f_nowr f = true -> f_wactive f = false /\ f_wbuf f = []) /\ (f_nord f = true -> f_rbuf f = [])
  /\ Forall (fun z => 0 <= z < 256) (f_rbuf f).
Definition stdout_inv (f : file_st) : Prop :=
  f_chan f = true /\ f_fd f = 1 /\ f_bufsize f = BUFSIZ /\ f_nord f = true /\ f_nowr f = false /\ f_eof f = false /\ f_rbuf f = []
  /\ (f_stdoutw f = true -> f_lbf_nl f = true).
Definition stderr_inv (f : file_st) : Prop :=
  f_chan f = true /\ f_fd f = 2 /\ f_bufsize f = 0 /\ f_nord f = true /\ f_nowr f = false /\ f_eof f = false /\ f_rbuf f = []
  /\ f_stdoutw f = false /\ f_lbf_nl f = false.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithPtr.
  Context {hptr : Type}.
  Notation cblk := (hptr * Z * Z)%type.
  Definition hd_addr (FB : list cblk) : Z := match FB with [] => 0 | (_, A, _) :: _ => A end.

  (* [comment removed for export] *)
  Fixpoint files_R (m : mem) (prev : Z) (fs : list (hptr * file_st)) (FB : list cblk) : Prop :=
    match fs, FB with
    | [], [] => True
    | (q, f) :: fs', (q', A, n) :: FB' =>
        q' = q /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
        /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK prev (hd_addr FB')
        /\ heap_file_inv f
        /\ files_R m A fs' FB'
    | _, _ => False
    end.

  Definition STDIOR (l : @libc_st hptr) (FB : list cblk) (m : mem) : Prop :=
       FILE_R m (lc_stdout l) A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 /\ stdout_inv (lc_stdout l)
    /\ FILE_R m (lc_stderr l) A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 /\ stderr_inv (lc_stderr l)
    /\ rw_cells asegs m A_STDIN stdin_cells
    /\ rw_cells asegs m A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)]
    /\ rw_cells asegs m A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)]
    /\ rw_cells asegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)]
    /\ rw_cells asegs m A_OFL_LOCK [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr FB))]
    /\ files_R m 0 (lc_files l) FB
    /\ List.NoDup (map fst (lc_files l)).

  (* [comment removed for export] *)
  Definition stdio_init_stmt : Prop :=
    forall m,
      rw_cells asegs m A_STDOUT (file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDOUT_WRITE F_STDIO_SEEK A_STDOUT_BUF 1024 0 0 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells asegs m A_STDERR (file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDIO_WRITE F_STDIO_SEEK A_STDERR_BUF 0 0 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells asegs m A_STDIN stdin_cells ->
      (exists bb, rw_cells asegs m A_STDOUT_BUF [CB 1024 bb]) -> rw_cells asegs m A_STDERR_BUF [CB 0 []] ->
      rw_cells asegs m A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)] -> rw_cells asegs m A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)] ->
      rw_cells asegs m A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)] ->
      rw_cells asegs m A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells asegs m A_OFL_HEAD [C8 (Z_to_bv 64 0)] ->
      STDIOR libc_init [] m.

  (* [comment removed for export] *)
  Definition stdio_frame_stmt : Prop :=
    forall l FB m m' W,
      STDIOR l FB m -> munch W m m' -> wmono asegs m m' ->
      Forall (fun iv => (snd iv <= 0xa9e90 \/ 0xaa160 <= fst iv) /\ (snd iv <= 0x6020a8 \/ 0x6028d0 <= fst iv)) W ->
      Forall (fun iv => Forall (fun b => snd iv <= snd (fst b) \/ snd (fst b) + snd b <= fst iv) FB) W ->
      STDIOR l FB m'.
End WithPtr.
End TwB.
