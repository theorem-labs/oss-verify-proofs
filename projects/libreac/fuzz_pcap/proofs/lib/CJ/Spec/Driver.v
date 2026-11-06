(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.Spec Require Import Prelim Monad Stdio.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition MAX_INPUT : Z := 67108864.   (* [comment removed for export] *)
Definition HDR_MIN : Z := 6.
Definition COUNT_MAX : Z := 251.

(* [comment removed for export] *)
Inductive diag_msg : Type :=
| DUsage (argv0 : list Z)
| DCannotOpen (path : list Z)
| DReadError (path : list Z)
| DOom
| DTooBig
| DShortHdr
| DCfgOverrun.

Record IOStyle (St : Type) := mkIO {
  io_diag : diag_msg -> M St unit;     (* [comment removed for export] *)
  io_emit : list Z -> M St unit;       (* [comment removed for export] *)
  io_exit : M St unit                  (* [comment removed for export] *)
}.
Arguments io_diag {St} _.
Arguments io_emit {St} _.
Arguments io_exit {St} _.

Section Driver.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable ptr_addr : St -> ptr -> Z.            (* [comment removed for export] *)
Variable alloc_init : Z -> M St unit.          (* [comment removed for export] *)
Variable run : Z -> list Z -> M St Z.          (* [comment removed for export] *)
Variable alloc_count : M St Z.                 (* [comment removed for export] *)

Inductive rd_result : Type :=
| RdExit                                   (* [comment removed for export] *)
| RdDone (buf : ptr) (content : list Z).   (* [comment removed for export] *)

(* [comment removed for export] *)
Record rd_st := mkRd { rd_buf : ptr; rd_cap : Z; rd_content : list Z }.

Definition u8s_of_bytes (bs : list byte) : list Z := map bv_unsigned bs.

(* [comment removed for export] *)
Definition read_loop_body (fd : Z) (path : list Z) (st : rd_st) : M St (rd_st + rd_result) :=
  let len := zlength (rd_content st) in
  (* [comment removed for export] *)
  g <- (if len =? rd_cap st then
          if MAX_INPUT <=? rd_cap st then
            io_diag io DTooBig ;;; mret None
          else
            nb <- drv_malloc (rd_cap st * 2) ;;
            match nb with
            | None => io_diag io DOom ;;; mret None
            | Some nb' => drv_free (rd_buf st) ;;;                 (* [comment removed for export] *)
                          mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
            end
        else mret (Some st)) ;;
  match g with
  | None => mret (inr RdExit)
  | Some st1 =>
      s <- mget ;;
      let buf := ptr_addr s (rd_buf st1) + len in
      let cnt := rd_cap st1 - len in
      a <- msys (NRead fd buf cnt) (dec_read buf cnt) ;;
      match a with
      | RdErr _ => io_diag io (DReadError path) ;;; mret (inr RdExit)
      | RdData bs =>
          if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
          else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
      end
  end.

(* [comment removed for export] *)
Definition READ_FUEL : nat := Z.to_nat (MAX_INPUT + 16).

Definition read_all (path : list Z) : M St rd_result :=
  r <- msys (NOpen (map (Z_to_bv 8) path)) dec_open ;;
  match r with
  | SErr _ => io_diag io (DCannotOpen path) ;;; mret RdExit
  | SVal fd =>
      b <- drv_malloc 65536 ;;
      match b with
      | None => io_diag io DOom ;;; mret RdExit
      | Some buf =>
          res <- mloop READ_FUEL (read_loop_body fd path) (mkRd buf 65536 []) ;;
          match res with
          | RdExit => mret RdExit
          | RdDone buf' content => _ <- msys (NClose fd) dec_close ;; mret (RdDone buf' content)
          end
      end
  end.

Definition le16 (l : list Z) : Z := znth l 0 + znth l 1 * 256.
Definition le32 (l : list Z) : Z := znth l 0 + znth l 1 * 2^8 + znth l 2 * 2^16 + znth l 3 * 2^24.

(* [comment removed for export] *)
Definition main_model (argv : list (list Z)) : M St Z :=
  if negb (Z.of_nat (length argv) =? 2) then
    io_diag io (DUsage (nth 0 argv [])) ;;; mret 2
  else
    ra <- read_all (nth 1 argv []) ;;
    match ra with
    | RdExit => mret 2
    | RdDone buf content =>
        let len := zlength content in
        if len <? HDR_MIN then io_diag io DShortHdr ;;; drv_free buf ;;; mret 2
        else
          let cfg_word := le16 content in
          let count_allocs := Z.testbit cfg_word 15 in
          let config_len := Z.land cfg_word 0x7fff in
          if len <? HDR_MIN + config_len then io_diag io DCfgOverrun ;;; drv_free buf ;;; mret 2
          else
            let bitmap := le32 (skipn (Z.to_nat (2 + config_len)) content) in
            let payload := skipn (Z.to_nat (6 + config_len)) content in
            let cfg := if 0 <? config_len then znth content 2 else 0 in
            alloc_init bitmap ;;;
            status <- run cfg payload ;;
            status' <- (if count_allocs then
                          n <- alloc_count ;; mret (if n <? COUNT_MAX then n else COUNT_MAX)
                        else mret status) ;;
            drv_free buf ;;;
            mret status'
    end.

(* [comment removed for export] *)
Definition exit_model (code : Z) : M St Empty_set :=
  io_exit io ;;;                                   (* [comment removed for export] *)
  msys (NExit code) dec_exit.                       (* [comment removed for export] *)

End Driver.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section IO_T.
Local Open Scope string_scope. Local Open Scope list_scope. Local Open Scope Z_scope. Local Open Scope mspec_scope.
Context {St : Type}.
Definition t_write (fd : Z) (s : list Z) : M St unit :=
  _ <- msys (NWrite fd (to_bytes s)) (dec_write (zlength s)) ;; mret tt.
Definition t_diag (d : diag_msg) : M St unit :=
  match d with
  | DUsage argv0 => t_write 2 (str "usage: ") ;;; t_write 2 argv0 ;;; t_write 2 (str " INPUT" ++ [10])
  | DCannotOpen p => t_write 2 (str "cli: cannot open ") ;;; t_write 2 p ;;; t_write 2 [10]
  | DReadError p => t_write 2 (str "cli: read error on ") ;;; t_write 2 p ;;; t_write 2 [10]
  | DOom => t_write 2 (str "cli: out of memory" ++ [10])
  | DTooBig => t_write 2 (str "cli: input >= 67108864 bytes, refused" ++ [10])
  | DShortHdr => t_write 2 (str "cli: input shorter than header" ++ [10])
  | DCfgOverrun => t_write 2 (str "cli: config_len overruns input" ++ [10])
  end.
Definition t_emit (s : list Z) : M St unit := t_write 1 s ;;; t_write 1 [10].
(* [comment removed for export] *)
Definition io_T : IOStyle St := mkIO St t_diag t_emit (fun s => mret tt s).
End IO_T.

(* [comment removed for export] *)
Section IO_S.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
(* [comment removed for export] *)
Definition s_diag (d : diag_msg) : M St unit :=
  match d with
  | DUsage argv0 => stderr_fprintf (pieces_usage argv0)
  | DCannotOpen p => stderr_fprintf (pieces_cannot_open p)
  | DReadError p => stderr_fprintf (pieces_read_error p)
  | DOom => stderr_fwrite (concat pieces_oom)
  | DTooBig => stderr_fprintf pieces_too_big
  | DShortHdr => stderr_fwrite (concat pieces_short_hdr)
  | DCfgOverrun => stderr_fwrite (concat pieces_cfg_overrun)
  end.
Definition s_emit (s : list Z) : M St unit := stdout_vprintf get_so set_so (pieces_emit s).
Definition io_S : IOStyle St := mkIO St s_diag s_emit (stdout_exit_flush get_so set_so).
End IO_S.
