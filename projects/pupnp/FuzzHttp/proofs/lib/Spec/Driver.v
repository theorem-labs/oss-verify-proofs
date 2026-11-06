(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition MAX_INPUT : Z := 67108864.
Definition HDR_MIN : Z := 6.
Definition COUNT_MAX : Z := 251.
Definition READ_CHUNK : Z := 65536.

Inductive diag_msg : Type :=
| DUsage (argv0 : list Z)
| DCannotOpen (path : list Z)
| DReadError (path : list Z)
| DOom
| DTooBig
| DShortHdr
| DCfgOverrun.

Record IOStyle (St : Type) := mkIO {
  io_diag : diag_msg -> M St unit;
  io_emit : M St unit;
  io_exit : M St unit
}.
Arguments io_diag {St} _.
Arguments io_emit {St} _.
Arguments io_exit {St} _.

Section Driver.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable rs_addr : Z.

Inductive rd_result : Type :=
| RdExit
| RdDone (buf : ptr) (content : list Z).

Record rd_st := mkRd { rd_buf : ptr; rd_cap : Z; rd_content : list Z }.

Definition u8s_of_bytes (bs : list byte) : list Z := map bv_unsigned bs.

Definition read_loop_body (fd : Z) (path : list Z) (st : rd_st) : M St (rd_st + rd_result) :=
  let len := zlength (rd_content st) in

  g <- (if len =? rd_cap st then
          if MAX_INPUT <=? rd_cap st then
            io_diag io DTooBig ;;; mret None
          else
            nb <- drv_malloc (rd_cap st * 2) ;;
            match nb with
            | None => io_diag io DOom ;;; mret None
            | Some nb' => drv_free (rd_buf st) ;;;
                          mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
            end
        else mret (Some st)) ;;
  match g with
  | None => mret (inr RdExit)
  | Some st1 =>
      let buf := rs_addr in
      let cnt := Z.min (rd_cap st1 - len) READ_CHUNK in
      a <- msys (NRead fd buf cnt) (dec_read buf cnt) ;;
      match a with
      | RdErr _ => io_diag io (DReadError path) ;;; mret (inr RdExit)
      | RdData bs =>
          if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
          else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
      end
  end.

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

Definition exit_model (code : Z) : M St Empty_set :=
  io_exit io ;;;
  msys (NExit code) dec_exit.

Definition exit_k {A} (code : Z) : M St A :=
  e <- exit_model code ;; match (e : Empty_set) with end.

Record at_parser := mkAP {
  ap_buf : ptr;
  ap_content : list Z;
  ap_count : bool;
  ap_config_len : Z;
  ap_calls : Z;
  ap_owned : option ptr
}.
Definition ap_payload (ap : at_parser) : list Z := skipn (Z.to_nat (HDR_MIN + ap_config_len ap)) (ap_content ap).
Definition ap_payload_len (ap : at_parser) : Z := zlength (ap_content ap) - HDR_MIN - ap_config_len ap.

Definition main_status (count : bool) (r : Z) : Z := if count then 0 else r.

Definition drv_pre (argv : list (list Z)) : M St at_parser :=
  if negb (Z.of_nat (length argv) =? 2) then
    io_diag io (DUsage (nth 0 argv [])) ;;; exit_k 2
  else
    ra <- read_all (nth 1 argv []) ;;
    match ra with
    | RdExit => exit_k 2
    | RdDone buf content =>
        let len := zlength content in
        if len <? HDR_MIN then io_diag io DShortHdr ;;; drv_free buf ;;; exit_k 2
        else
          let cfg_word := le16 content in
          let count := Z.testbit cfg_word 15 in
          let config_len := Z.land cfg_word 0x7fff in
          if len <? HDR_MIN + config_len then io_diag io DCfgOverrun ;;; drv_free buf ;;; exit_k 2
          else

            let payload_len := len - HDR_MIN - config_len in
            let c := (if 0 <? config_len then znth content 2 else 0) in
            let calls := 1 + Z.land c 3 in
            copy <- (if 0 <? payload_len then
                       p <- drv_malloc payload_len ;;
                       mret (match p with None => None | Some p' => Some (Some p') end)
                     else mret (Some None)) ;;
            match copy with
            | None =>
                drv_free buf ;;; exit_k (main_status count 2)
            | Some owned => mret (mkAP buf content count config_len calls owned)
            end
    end.

End Driver.

Section IO_S.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

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
Definition s_emit : M St unit := stdout_vprintf get_so set_so pieces_emit.
Definition io_S : IOStyle St := mkIO St s_diag s_emit (stdout_exit_flush get_so set_so).
End IO_S.
