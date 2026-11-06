(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Ey6n DA_Eg3i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition STDERR_BUFP : Z := 0x6082e0.
Definition STDERR_CELL : Z := 0xa8a68.     (* [comment removed for export] *)
Definition GOT_STDERR : Z := 0xa97d8.
Definition GOT_WEAKINIT : Z := 0xa97e0.    (* [comment removed for export] *)
Definition TR_INITIALIZED : Z := 0x5e7210.  (* [comment removed for export] *)
Definition TR_EMPTY : Z := 0x5e7220.        (* [comment removed for export] *)
Definition ERRNO_CELL : Z := 0x5e7b34.      (* [comment removed for export] *)
Definition READ_STAGE : Z := 0x5d7210.      (* [comment removed for export] *)
Definition STDOUT_WRITE : Z := 0x9e288.    (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record mfile := MFILE {
  mf_flags : Z;  mf_rpos : word; mf_rend : word; mf_close : word;
  mf_wend : word; mf_wpos : word; mf_mbz1 : word; mf_wbase : word;
  mf_read : word; mf_write : Z; mf_seek : word;
  mf_buf : Z; mf_bufsize : Z; mf_prev : word; mf_next : word;
  mf_fd : Z; mf_pipepid : word; mf_lockcount : word; mf_mode : Z; mf_lock : Z; mf_lbf : Z; mf_pad148 : word }.

Definition file_cells (f : mfile) : list cell :=
  [ C4 (Z_to_bv 64 (mf_flags f)); C4 (Z_to_bv 64 0) (* [comment removed for export] *);
    C8 (mf_rpos f); C8 (mf_rend f); C8 (mf_close f);
    C8 (mf_wend f); C8 (mf_wpos f); C8 (mf_mbz1 f); C8 (mf_wbase f);
    C8 (mf_read f); C8 (Z_to_bv 64 (mf_write f)); C8 (mf_seek f);
    C8 (Z_to_bv 64 (mf_buf f)); C8 (Z_to_bv 64 (mf_bufsize f)); C8 (mf_prev f); C8 (mf_next f);
    C4 (Z_to_bv 64 (mf_fd f)); C4 (mf_pipepid f); C8 (mf_lockcount f);
    C4 (Z_to_bv 64 (mf_mode f)); C4 (Z_to_bv 64 (mf_lock f)); C4 (Z_to_bv 64 (mf_lbf f)); C4 (mf_pad148 f) ].
(* [comment removed for export] *)
Lemma file_cells_size : forall f, cells_size (file_cells f) = 152%nat.
Proof. reflexivity. Qed.

Definition file_at (v : word -> option byte) (F : Z) (f : mfile) : Prop := rw_cells rsegs v F (file_cells f).

(* [comment removed for export] *)
Definition mf_set_w (f : mfile) (wpos wbase wend : word) : mfile :=
  MFILE (mf_flags f) (mf_rpos f) (mf_rend f) (mf_close f) wend wpos (mf_mbz1 f) wbase (mf_read f) (mf_write f) (mf_seek f)
        (mf_buf f) (mf_bufsize f) (mf_prev f) (mf_next f) (mf_fd f) (mf_pipepid f) (mf_lockcount f) (mf_mode f) (mf_lock f) (mf_lbf f) (mf_pad148 f).
Definition mf_set_rp (f : mfile) (rpos rend : word) : mfile :=
  MFILE (mf_flags f) rpos rend (mf_close f) (mf_wend f) (mf_wpos f) (mf_mbz1 f) (mf_wbase f) (mf_read f) (mf_write f) (mf_seek f)
        (mf_buf f) (mf_bufsize f) (mf_prev f) (mf_next f) (mf_fd f) (mf_pipepid f) (mf_lockcount f) (mf_mode f) (mf_lock f) (mf_lbf f) (mf_pad148 f).
Definition mf_set_mode (f : mfile) (mode : Z) : mfile :=
  MFILE (mf_flags f) (mf_rpos f) (mf_rend f) (mf_close f) (mf_wend f) (mf_wpos f) (mf_mbz1 f) (mf_wbase f) (mf_read f) (mf_write f) (mf_seek f)
        (mf_buf f) (mf_bufsize f) (mf_prev f) (mf_next f) (mf_fd f) (mf_pipepid f) (mf_lockcount f) mode (mf_lock f) (mf_lbf f) (mf_pad148 f).
Definition mf_set_flags (f : mfile) (fl : Z) : mfile :=
  MFILE fl (mf_rpos f) (mf_rend f) (mf_close f) (mf_wend f) (mf_wpos f) (mf_mbz1 f) (mf_wbase f) (mf_read f) (mf_write f) (mf_seek f)
        (mf_buf f) (mf_bufsize f) (mf_prev f) (mf_next f) (mf_fd f) (mf_pipepid f) (mf_lockcount f) (mf_mode f) (mf_lock f) (mf_lbf f) (mf_pad148 f).
Definition mf_set_buf (f : mfile) (buf bsz : Z) : mfile :=
  MFILE (mf_flags f) (mf_rpos f) (mf_rend f) (mf_close f) (mf_wend f) (mf_wpos f) (mf_mbz1 f) (mf_wbase f) (mf_read f) (mf_write f) (mf_seek f)
        buf bsz (mf_prev f) (mf_next f) (mf_fd f) (mf_pipepid f) (mf_lockcount f) (mf_mode f) (mf_lock f) (mf_lbf f) (mf_pad148 f).
Definition mf_set_write_lbf (f : mfile) (wr lbf : Z) : mfile :=
  MFILE (mf_flags f) (mf_rpos f) (mf_rend f) (mf_close f) (mf_wend f) (mf_wpos f) (mf_mbz1 f) (mf_wbase f) (mf_read f) wr (mf_seek f)
        (mf_buf f) (mf_bufsize f) (mf_prev f) (mf_next f) (mf_fd f) (mf_pipepid f) (mf_lockcount f) (mf_mode f) (mf_lock f) lbf (mf_pad148 f).

(* [comment removed for export] *)
Definition w0 : word := Z_to_bv 64 0.
Definition stderr0 : mfile :=
  MFILE 5 w0 w0 (Z_to_bv 64 0x9d738) w0 w0 w0 w0 w0 STDIO_WRITE (Z_to_bv 64 0x9d87c) STDERR_BUFP 0 w0 w0 2 w0 w0 0 (-1) (-1) w0.
Definition stdout0 : mfile :=
  MFILE 5 w0 w0 (Z_to_bv 64 0x9d738) w0 w0 w0 w0 w0 STDOUT_WRITE (Z_to_bv 64 0x9d87c) STDOUT_BUF 1024 w0 w0 1 w0 w0 0 (-1) 10 w0.
Definition stdin0 : mfile :=
  MFILE 9 w0 w0 (Z_to_bv 64 0x9d738) w0 w0 w0 w0 (Z_to_bv 64 0x9d764) 0 (Z_to_bv 64 0x9d87c) 0x6086f0 1024 w0 w0 0 w0 w0 0 (-1) 0 w0.
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive stdout_form := SO_pristine | SO_buffered (pending : list byte).

(* [comment removed for export] *)
Definition stdout_buffered (mo : Z) (pending : list byte) : mfile :=
  MFILE 5 w0 w0 (Z_to_bv 64 0x9d738) (Z_to_bv 64 (STDOUT_BUF + 1024)) (Z_to_bv 64 (STDOUT_BUF + Z.of_nat (length pending))) w0 (Z_to_bv 64 STDOUT_BUF)
        w0 STDIO_WRITE (Z_to_bv 64 0x9d87c) STDOUT_BUF 1024 w0 w0 1 w0 w0 mo (-1) (-1) w0.

Definition stdout_at (v : word -> option byte) (sof : stdout_form) : Prop :=
  match sof with
  | SO_pristine => file_at v STDOUT_F stdout0 /\ exists junk, rw_cells rsegs v STDOUT_BUF [CB 1024 junk]
  | SO_buffered p => exists mo junk, file_at v STDOUT_F (stdout_buffered mo p)
                     /\ rw_cells rsegs v STDOUT_BUF [CB (length p) p; CB (1024 - length p) junk]
                     /\ (Z.of_nat (length p) <= 1016)%Z
  end.
Definition pending_of (sof : stdout_form) : list byte := match sof with SO_pristine => [] | SO_buffered p => p end.

(* [comment removed for export] *)
Record mcells (v : word -> option byte) (tid : Z) : Prop := {
  mc_tid   : ro_cells rsegs v TID_CELL [C4 (Z_to_bv 64 tid)];
  mc_tidr  : 0 < tid < 2^22;
  mc_lock  : rw_cells rsegs v EXIT_LOCK [C4 (Z_to_bv 64 0)];
  mc_fin   : rw_cells rsegs v ATEXIT [C1 (Z_to_bv 8 0)];       (* [comment removed for export] *)
  mc_alock : ro_cells rsegs v (ATEXIT + 4) [C4 (Z_to_bv 64 0)];
  (* [comment removed for export] *)
  mc_head  : rw_cells rsegs v (ATEXIT + 16) [C8 (Z_to_bv 64 (ATEXIT + 24))];
  mc_bnext : ro_cells rsegs v (ATEXIT + 24) [C8 (Z_to_bv 64 0)];
  mc_bf0   : ro_cells rsegs v (ATEXIT + 32) [C8 (Z_to_bv 64 0x98320)];
  mc_ba0   : ro_cells rsegs v (ATEXIT + 288) [C8 (Z_to_bv 64 0x76258)];
  mc_nlock : ro_cells rsegs v NEED_LOCKS [C1 (Z_to_bv 8 0)];
  mc_ofl   : ro_cells rsegs v OFL_HEAD [C8 (Z_to_bv 64 0)];
  mc_uin   : ro_cells rsegs v 0xad5d0 [C8 (Z_to_bv 64 STDIN_F)];
  mc_uout  : ro_cells rsegs v 0xad4e0 [C8 (Z_to_bv 64 STDOUT_F)];
  mc_uerr  : ro_cells rsegs v 0xad3f0 [C8 (Z_to_bv 64 STDERR_F)];
  mc_in    : exists wp rp, file_clean v STDIN_F wp rp;
  mc_stderrp : ro_cells rsegs v STDERR_CELL [C8 (Z_to_bv 64 STDERR_F)];
  mc_canary : exists g, ro_cells rsegs v SSP_GUARD [C8 g];
  mc_sspgot : ro_cells rsegs v SSP_GOT [C8 (Z_to_bv 64 SSP_GUARD)];
  mc_errbuf : exists j8, rw_cells rsegs v STDERR_BUFP [CB 8 j8];
  mc_empty  : exists j16, ro_cells rsegs v TR_EMPTY [CB 16 j16]
}.

(* [comment removed for export] *)
Definition trcells (v : word -> option byte) (ini : Z) : Prop :=
  (ini = 0 \/ ini = 1)
  /\ rw_cells rsegs v TR_INITIALIZED [C1 (Z_to_bv 8 ini)]
  /\ rw_cells rsegs v TR_INCB [C1 (Z_to_bv 8 0)]
  /\ rw_cells rsegs v (ATEXIT + 8) [C4 (Z_to_bv 64 (1 + ini))]
  /\ rw_cells rsegs v (ATEXIT + 40) [C8 (Z_to_bv 64 (ini * CALL_TRAMP))]
  /\ rw_cells rsegs v (ATEXIT + 296) [C8 (Z_to_bv 64 (ini * AEF_GUARD))].

(* [comment removed for export] *)
Definition dcells (v : word -> option byte) (tid : Z) (sof : stdout_form) (ini : Z) : Prop :=
  mcells v tid /\ file_at v STDERR_F stderr0 /\ stdout_at v sof /\ trcells v ini.

(* [comment removed for export] *)
Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
Definition fds3 (e : FdEntry) : list (word * FdEntry) := (Z_to_bv 64 3, e) :: fds_std.

(* [comment removed for export] *)
Definition DCELLS_RANGES : list (Z * Z) :=
  [(STDERR_F, STDERR_F + 152); (STDOUT_F, STDOUT_F + 152); (STDIN_F, STDIN_F + 152);
   (0xad3f0, 0xad3f8); (0xad4e0, 0xad5d8); (0xad5d0, 0xad600); (STDERR_CELL, STDERR_CELL + 8);
   (TR_INITIALIZED, TR_INITIALIZED + 1); (TR_INCB, TR_INCB + 1); (TR_EMPTY, TR_EMPTY + 16);
   (TID_CELL, TID_CELL + 4); (SSP_GUARD, SSP_GUARD + 8); (ATEXIT, ATEXIT + 304); (EXIT_LOCK, EXIT_LOCK + 4);
   (NEED_LOCKS, NEED_LOCKS + 1); (OFL_HEAD, OFL_HEAD + 8); (STDERR_BUFP, STDERR_BUFP + 8); (STDOUT_BUF, STDOUT_BUF + 1024)].
