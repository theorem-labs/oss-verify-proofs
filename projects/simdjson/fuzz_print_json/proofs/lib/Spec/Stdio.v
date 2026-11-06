(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition to_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition TIOCGWINSZ : Z := 21523.
Definition STDOUT_BUFSIZ : Z := 1024.
Definition INTERNAL_BUFSIZ : Z := 80.

Record stdout_st := mkStdout {
  so_active : bool;
  so_buf : list Z;
  so_lbf_nl : bool;
  so_first : bool
}.
Definition stdout_init : stdout_st := mkStdout false [] true true.

Definition iov_total (iovs : list (list Z)) : Z := zlength (concat iovs).

Definition iov_start (buf s : list Z) : list (list Z) :=
  match buf with [] => [s] | _ => [buf; s] end.

Definition iov_advance (iovs : list (list Z)) (cnt : Z) : list (list Z) :=
  match iovs with
  | [] => []
  | a :: rest =>
      if zlength a <? cnt
      then match rest with
           | [] => []
           | b :: rest' => zdrop (cnt - zlength a) b :: rest'
           end
      else zdrop cnt a :: rest
  end.

Section Stdio.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Let M := @M St.
Definition upd_so (f : stdout_st -> stdout_st) : M unit := mupd (fun s => set_so (f (get_so s)) s).
Definition rd_so : M stdout_st := mbind mget (fun s => mret (get_so s)).

Definition wv_body (fd : Z) (iovs : list (list Z)) : M (list (list Z) + unit) :=
  k <- msys (NWritev fd (map to_bytes iovs)) (dec_writev (iov_total iovs)) ;;
  if k =? iov_total iovs then mret (inr tt)
  else mret (inl (iov_advance iovs k)).

Definition WV_FUEL (iovs : list (list Z)) : nat := S (Z.to_nat (iov_total iovs)).

Definition stdio_writev (fd : Z) (buf s : list Z) : M unit :=
  mloop (WV_FUEL (iov_start buf s)) (wv_body fd) (iov_start buf s).

Definition stdout_stdio_write (s : list Z) : M unit :=
  so <- rd_so ;;
  stdio_writev 1 (so_buf so) s ;;;
  upd_so (fun so => mkStdout true [] (so_lbf_nl so) (so_first so)).

Definition stdout_writefn (s : list Z) : M unit :=
  so <- rd_so ;;
  (if so_first so then
     upd_so (fun so => mkStdout (so_active so) (so_buf so) (so_lbf_nl so) false) ;;;
     r <- msys (NIoctl 1 TIOCGWINSZ) dec_ioctl ;;
     match r with
     | SErr _ => upd_so (fun so => mkStdout (so_active so) (so_buf so) false (so_first so))
     | SVal _ => munr
     end
   else mret tt) ;;;
  stdout_stdio_write s.

Definition after_last_nl (s : list Z) : Z :=
  fold_left (fun acc ib => if snd ib =? 10 then fst ib + 1 else acc)
            (combine (map Z.of_nat (seq 0 (length s))) s) 0.

Definition stdout_towrite : M unit :=
  upd_so (fun so => if so_active so then so else mkStdout true [] (so_lbf_nl so) (so_first so)).

Definition stdout_fwritex (s : list Z) : M unit :=
  stdout_towrite ;;;
  so <- rd_so ;;
  if STDOUT_BUFSIZ - zlength (so_buf so) <? zlength s
  then stdout_writefn s
  else if so_lbf_nl so then
    let i := after_last_nl s in
    (if 0 <? i then stdout_writefn (firstn (Z.to_nat i) s) else mret tt) ;;;
    upd_so (fun so => mkStdout (so_active so) (so_buf so ++ skipn (Z.to_nat i) s) (so_lbf_nl so) (so_first so))
  else
    upd_so (fun so => mkStdout (so_active so) (so_buf so ++ s) (so_lbf_nl so) (so_first so)).

Fixpoint out_pieces (ps : list (list Z)) : M unit :=
  match ps with
  | [] => mret tt
  | p :: ps' => stdout_fwritex p ;;; out_pieces ps'
  end.
Definition stdout_vprintf (pieces : list (list Z)) : M unit :=
  stdout_towrite ;;; out_pieces pieces.

Definition stdout_exit_flush : M unit :=
  so <- rd_so ;;
  if (0 <? zlength (so_buf so)) then stdout_writefn [] else mret tt.

Fixpoint stderr_pieces (buf : list Z) (ps : list (list Z)) : M (list Z) :=
  match ps with
  | [] => mret buf
  | p :: ps' =>
      if INTERNAL_BUFSIZ - zlength buf <? zlength p
      then (stdio_writev 2 buf p ;;; stderr_pieces [] ps')
      else stderr_pieces (buf ++ p) ps'
  end.
Definition stderr_fprintf (pieces : list (list Z)) : M unit :=
  buf <- stderr_pieces [] pieces ;;
  stdio_writev 2 buf [].

Definition stderr_fwrite (s : list Z) : M unit :=
  if 0 <? zlength s then stdio_writev 2 [] s else mret tt.

End Stdio.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition pieces_emit_0 : list (list Z) := [ []; []; [48]; []; [10] ].

Definition pieces_usage (argv0 : list Z) : list (list Z) :=
  [ str "usage: "; []; []; argv0; str " INPUT" ++ [10] ].

Definition pieces_cannot_open (path : list Z) : list (list Z) :=
  [ str "cli: cannot open "; []; []; path; [10] ].

Definition pieces_read_error (path : list Z) : list (list Z) :=
  [ str "cli: read error on "; []; []; path; [10] ].

Definition pieces_oom : list (list Z) := [ str "cli: out of memory" ++ [10] ].

Definition pieces_too_big : list (list Z) :=
  [ str "cli: input >= "; []; []; str "67108864"; str " bytes, refused" ++ [10] ].

Definition pieces_short_hdr : list (list Z) := [ str "cli: input shorter than header" ++ [10] ].

Definition pieces_cfg_overrun : list (list Z) := [ str "cli: config_len overruns input" ++ [10] ].

Definition pieces_precond_fail (x fn : list Z) : list (list Z) :=
  [ str "p11-kit: '"; []; []; x; str "' not true at "; []; []; fn; [10] ].
Definition pieces_precond_reached (fn : list Z) : list (list Z) :=
  [ str "p11-kit: shouldn't be reached at "; []; []; fn; [10] ].

Example pieces_usage_concat :
  concat (pieces_usage (str "prog")) = str "usage: prog INPUT" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example pieces_precond_concat :
  concat (pieces_precond_fail (str "lexer->filename != NULL") (str "p11_lexer_init"))
  = str "p11-kit: 'lexer->filename != NULL' not true at p11_lexer_init" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example after_last_nl_ex1 : after_last_nl (str "ab" ++ [10] ++ str "cd") = 3.
Proof. vm_compute. reflexivity. Qed.
Example after_last_nl_ex2 : after_last_nl (str "abc") = 0.
Proof. vm_compute. reflexivity. Qed.
Example iov_advance_ex1 : iov_advance [[48]; [10]] 1 = [[]; [10]].
Proof. vm_compute. reflexivity. Qed.
Example iov_advance_ex2 : iov_advance [[48;48]; [10;10]] 3 = [[10]].
Proof. vm_compute. reflexivity. Qed.
