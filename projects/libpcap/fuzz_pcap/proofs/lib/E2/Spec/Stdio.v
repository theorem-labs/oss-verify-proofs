(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition ENOENT : Z := 2.
Definition ENOMEM : Z := 12.
Definition EISDIR : Z := 21.

Section Stdio.
Context {St ptr : Type}.

(* [comment removed for export] *)
Record libc_st := mkLibc {
  lc_stdout : file_st;
  lc_stderr : file_st;
  lc_files : list (ptr * file_st);   (* [comment removed for export] *)
  lc_errno : Z
}.

(* [comment removed for export] *)
Definition libc_init : libc_st := mkLibc stdout_init stderr_init [] 0.

Context (get_lc : St -> libc_st) (set_lc : libc_st -> St -> St).
Variable ptr_eqb : ptr -> ptr -> bool.      (* [comment removed for export] *)
Variable malloc : Z -> M St (option ptr).
Variable free : ptr -> M St unit.
Variable buf_addr : St -> ptr -> Z.        (* [comment removed for export] *)

Let M := @M St.

Definition rd_lc : M libc_st := s <- mget ;; mret (get_lc s).
Definition upd_lc (g : libc_st -> libc_st) : M unit := mupd (fun s => set_lc (g (get_lc s)) s).

Definition set_stdout (f : file_st) (l : libc_st) := mkLibc f (lc_stderr l) (lc_files l) (lc_errno l).
Definition set_stderr (f : file_st) (l : libc_st) := mkLibc (lc_stdout l) f (lc_files l) (lc_errno l).
Definition set_files (fs : list (ptr * file_st)) (l : libc_st) := mkLibc (lc_stdout l) (lc_stderr l) fs (lc_errno l).
Definition set_errno_lc (e : Z) (l : libc_st) := mkLibc (lc_stdout l) (lc_stderr l) (lc_files l) e.

Definition set_errno (e : Z) : M unit := upd_lc (set_errno_lc e).
Definition get_errno : M Z := l <- rd_lc ;; mret (lc_errno l).

(* [comment removed for export] *)
Fixpoint files_lookup (fs : list (ptr * file_st)) (h : ptr) : option file_st :=
  match fs with
  | [] => None
  | (k, v) :: fs' => if ptr_eqb k h then Some v else files_lookup fs' h
  end.
Fixpoint files_update (fs : list (ptr * file_st)) (h : ptr) (f : file_st) : list (ptr * file_st) :=
  match fs with
  | [] => []
  | (k, g) :: fs' => if ptr_eqb k h then (k, f) :: fs' else (k, g) :: files_update fs' h f
  end.
Fixpoint files_remove (fs : list (ptr * file_st)) (h : ptr) : list (ptr * file_st) :=
  match fs with
  | [] => []
  | (k, v) :: fs' => if ptr_eqb k h then fs' else (k, v) :: files_remove fs' h
  end.

Definition lookup_file (h : ptr) : M file_st :=
  l <- rd_lc ;;
  match files_lookup (lc_files l) h with
  | Some v => mret v
  | None => munr          (* [comment removed for export] *)
  end.
Definition store_file (h : ptr) (f : file_st) : M unit :=
  upd_lc (fun l => set_files (files_update (lc_files l) h f) l).

(* [comment removed for export] *)
Definition with_file {A} (h : ptr) (op : file_st -> M (A * file_st)) : M A :=
  f <- lookup_file h ;;
  r <- op f ;;
  store_file h (snd r) ;;;
  mret (fst r).
Definition with_file_ (h : ptr) (op : file_st -> M file_st) : M unit :=
  f <- lookup_file h ;;
  f' <- op f ;;
  store_file h f'.

(* [comment removed for export] *)
Definition fopen (name : list Z) (wr : bool) : M (option ptr) :=
  r <- msys (if wr then NOpenW (to_bytes name) FOPEN_MODE else NOpen (to_bytes name)) (if wr then dec_openw else dec_open) ;;
  match r with
  | SErr e => set_errno e ;;; mret None
  | SVal fd =>
      po <- malloc FILE_ALLOC ;;
      match po with
      | None =>
          (* [comment removed for export] *)
          set_errno ENOMEM ;;;
          _ <- msys (NClose fd) dec_close ;;
          mret None
      | Some p =>
          (if wr then
             r <- msys (NIoctl fd TIOCGWINSZ) dec_ioctl ;;
             match r with SErr _ => mret tt | SVal _ => munr end
           else mret tt) ;;;
          upd_lc (fun l => set_files ((p, fdopen_file fd wr) :: lc_files l) l) ;;;
          mret (Some p)
      end
  end.

(* [comment removed for export] *)
Definition fclose (h : ptr) : M unit :=
  f <- lookup_file h ;;
  fclose_file f ;;;
  upd_lc (fun l => set_files (files_remove (lc_files l) h) l) ;;;
  free h.

(* [comment removed for export] *)
Definition fwrite (h : ptr) (s : list Z) : M Z :=
  with_file_ h (fun f => fwrite_file f s) ;;; mret (zlength s).

(* [comment removed for export] *)
Definition fread (h : ptr) (dest n : Z) : M (list Z) :=
  s <- mget ;;
  with_file h (fun f => fread_file f (buf_addr s h) dest n).

(* [comment removed for export] *)
Definition ferror (h : ptr) : M bool := _ <- lookup_file h ;; mret false.
Definition fileno (h : ptr) : M Z := f <- lookup_file h ;; mret (f_fd f).
Definition feof (h : ptr) : M bool := f <- lookup_file h ;; mret (f_eof f).

(* [comment removed for export] *)
Definition fprintf (h : ptr) (ps : list (list Z)) : M unit :=
  with_file_ h (fun f => vfprintf f ps).

(* [comment removed for export] *)
Definition printf (ps : list (list Z)) : M unit :=
  l <- rd_lc ;;
  f' <- vfprintf (lc_stdout l) ps ;;
  upd_lc (set_stdout f').

(* [comment removed for export] *)
Definition eprintf (ps : list (list Z)) : M unit :=
  l <- rd_lc ;;
  f' <- vfprintf (lc_stderr l) ps ;;
  upd_lc (set_stderr f').
Definition efwrite (s : list Z) : M unit :=
  l <- rd_lc ;;
  f' <- fwrite_file (lc_stderr l) s ;;
  upd_lc (set_stderr f').

(* [comment removed for export] *)
Definition remove (path : list Z) : M Z :=
  r <- msys (NUnlink (to_bytes path) false) dec_unlink ;;
  r2 <- (match r with
         | SErr e => if e =? EISDIR then msys (NUnlink (to_bytes path) true) dec_unlink else mret r
         | SVal _ => mret r
         end) ;;
  match r2 with
  | SErr e => set_errno e ;;; mret (-1)
  | SVal _ => mret 0
  end.

(* [comment removed for export] *)
Definition unlink (path : list Z) : M Z :=
  r <- msys (NUnlink (to_bytes path) false) dec_unlink ;;
  match r with
  | SErr e => set_errno e ;;; mret (-1)
  | SVal _ => mret 0
  end.

(* [comment removed for export] *)
Definition SEAL : list Z := str "000000".

Fixpoint last_slash_suffix (s : list Z) (cur : list Z) : list Z :=
  (* [comment removed for export] *)
  match s with
  | [] => cur
  | c :: s' => if c =? 47 then last_slash_suffix s' s' else last_slash_suffix s' cur
  end.

Definition seal_name (template : list Z) : option (list Z) :=
  let len := zlength template in
  if len <? 6 then None
  else
    let stem := firstn (Z.to_nat (len - 6)) template in
    let xs := skipn (Z.to_nat (len - 6)) template in
    if forallb (fun c => c =? 88) xs then
      let t := stem ++ SEAL in
      Some (last_slash_suffix t t)
    else None.

Definition mkstemp (template : list Z) : M (list Z * Z) :=
  match seal_name template with
  | None => mret (template, -1)
  | Some name =>
      r <- msys (NOpenW (to_bytes name) MKSTEMP_MODE) dec_openw ;;
      match r with
      | SErr e => set_errno e ;;; mret (name, -1)
      | SVal fd => mret (name, fd)
      end
  end.

(* [comment removed for export] *)
Definition close (fd : Z) : M Z :=
  _ <- msys (NClose fd) dec_close_ok ;; mret 0.

(* [comment removed for export] *)
Fixpoint close_files (fs : list (ptr * file_st)) : M unit :=
  match fs with
  | [] => mret tt
  | (_, f) :: fs' => close_file f ;;; close_files fs'
  end.

Definition stdio_exit : M unit :=
  l <- rd_lc ;;
  close_files (lc_files l) ;;;
  close_file (lc_stdout l) ;;;
  close_file (lc_stderr l).

(* [comment removed for export] *)
Definition exit_process (code : Z) : M Empty_set :=
  stdio_exit ;;; msys (NExit code) dec_exit.

(* [comment removed for export] *)
Definition diag_usage (argv0 : list Z) : M unit := eprintf (pieces_usage argv0).
Definition diag_cannot_open (path : list Z) : M unit := eprintf (pieces_cannot_open path).
Definition diag_read_error (path : list Z) : M unit := eprintf (pieces_read_error path).
Definition diag_oom : M unit := efwrite (List.concat pieces_oom).
Definition diag_too_big : M unit := eprintf pieces_too_big.
Definition diag_short_hdr : M unit := efwrite (List.concat pieces_short_hdr).
Definition diag_cfg_overrun : M unit := efwrite (List.concat pieces_cfg_overrun).
Definition emit_d (rc : Z) : M unit := printf (pieces_emit_d rc).

End Stdio.
End WithCeil.


Arguments libc_st : clear implicits.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Example seal_name_ex :
  seal_name (str "/tmp/libpcap_fuzz_pcap.XXXXXX") = Some (str "libpcap_fuzz_pcap.000000").
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example seal_name_noslash : seal_name (str "abcXXXXXX") = Some (str "abc000000").
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example seal_name_bad : seal_name (str "abcXXXXX") = None.
Proof. vm_compute. reflexivity. Qed.

End WithCeil.
