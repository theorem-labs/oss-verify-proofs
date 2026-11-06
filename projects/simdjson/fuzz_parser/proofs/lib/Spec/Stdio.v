(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition to_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition TIOCGWINSZ : Z := 21523.
Definition STDOUT_BUFSIZ : Z := 1024.   (* [comment removed for export] *)
Definition INTERNAL_BUFSIZ : Z := 80.  (* [comment removed for export] *)

(* [comment removed for export] *)
Record stdout_st := mkStdout {
  so_active : bool;      (* [comment removed for export] *)
  so_buf : list Z;        (* [comment removed for export] *)
  so_lbf_nl : bool;      (* [comment removed for export] *)
  so_first : bool         (* [comment removed for export] *)
}.
Definition stdout_init : stdout_st := mkStdout false [] true true.

(* [comment removed for export] *)
Section StdioWrite.
Context {St : Type}.
Let M := @M St.

(* [comment removed for export] *)
Definition iov_total (iov : list (list Z)) : Z := zlength (concat iov).

(* [comment removed for export] *)
Definition iov_advance (iov : list (list Z)) (cnt : Z) : list (list Z) :=
  match iov with
  | [] => []
  | [a] => [skipn (Z.to_nat cnt) a]
  | a :: b :: _ =>
      if zlength a <? cnt then [skipn (Z.to_nat (cnt - zlength a)) b]   (* [comment removed for export] *)
      else [skipn (Z.to_nat cnt) a; b]
  end.

Fixpoint stdio_write_loop (fuel : nat) (fd : Z) (iov : list (list Z)) : M unit :=
  match fuel with
  | O => munr
  | S fuel' =>
      cnt <- msys (NWritev fd (map to_bytes iov)) (dec_writev (iov_total iov)) ;;
      if cnt =? iov_total iov then mret tt                                 (* [comment removed for export] *)
      else stdio_write_loop fuel' fd (iov_advance iov cnt)
  end.

(* [comment removed for export] *)
Definition WRITE_MAX : Z := 67108864.   (* [comment removed for export] *)
Definition stdio_write (fd : Z) (buf s : list Z) : M unit :=
  if WRITE_MAX <? zlength buf + zlength s then munr
  else stdio_write_loop (S (Z.to_nat (zlength buf + zlength s))) fd
                        (match buf with [] => [s] | _ => [buf; s] end).
End StdioWrite.

Section Stdio.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Let M := @M St.
Definition upd_so (f : stdout_st -> stdout_st) : M unit := mupd (fun s => set_so (f (get_so s)) s).
Definition rd_so : M stdout_st := mbind mget (fun s => mret (get_so s)).

(* [comment removed for export] *)
Definition stdout_stdio_write (s : list Z) : M unit :=
  so <- rd_so ;;
  stdio_write 1 (so_buf so) s ;;;
  upd_so (fun so => mkStdout true [] (so_lbf_nl so) (so_first so)).

(* [comment removed for export] *)
Definition stdout_writefn (s : list Z) : M unit :=
  so <- rd_so ;;
  (if so_first so then
     upd_so (fun so => mkStdout (so_active so) (so_buf so) (so_lbf_nl so) false) ;;;
     r <- msys (NIoctl 1 TIOCGWINSZ) dec_ioctl ;;
     match r with
     | SErr _ => upd_so (fun so => mkStdout (so_active so) (so_buf so) false (so_first so))
     | SVal _ => munr   (* [comment removed for export] *)
     end
   else mret tt) ;;;
  stdout_stdio_write s.

(* [comment removed for export] *)
Definition after_last_nl (s : list Z) : Z :=
  fold_left (fun acc ib => if snd ib =? 10 then fst ib + 1 else acc)
            (combine (map Z.of_nat (seq 0 (length s))) s) 0.

(* [comment removed for export] *)
Definition stdout_towrite : M unit :=
  upd_so (fun so => if so_active so then so else mkStdout true [] (so_lbf_nl so) (so_first so)).

(* [comment removed for export] *)
Definition stdout_fwritex (s : list Z) : M unit :=
  stdout_towrite ;;;
  so <- rd_so ;;
  if STDOUT_BUFSIZ - zlength (so_buf so) <? zlength s                    (* [comment removed for export] *)
  then stdout_writefn s
  else if so_lbf_nl so then                                                (* [comment removed for export] *)
    let i := after_last_nl s in
    (if 0 <? i then stdout_writefn (firstn (Z.to_nat i) s) else mret tt) ;;;
    upd_so (fun so => mkStdout (so_active so) (so_buf so ++ skipn (Z.to_nat i) s) (so_lbf_nl so) (so_first so))
  else
    upd_so (fun so => mkStdout (so_active so) (so_buf so ++ s) (so_lbf_nl so) (so_first so)).

(* [comment removed for export] *)
Fixpoint out_pieces (ps : list (list Z)) : M unit :=
  match ps with
  | [] => mret tt
  | p :: ps' => stdout_fwritex p ;;; out_pieces ps'
  end.
Definition stdout_vprintf (pieces : list (list Z)) : M unit :=
  stdout_towrite ;;; out_pieces pieces.

(* [comment removed for export] *)
Definition stdout_exit_flush : M unit :=
  so <- rd_so ;;
  if (0 <? zlength (so_buf so)) then stdout_writefn [] else mret tt.

(* [comment removed for export] *)
Fixpoint stderr_pieces (buf : list Z) (ps : list (list Z)) : M (list Z) :=
  match ps with
  | [] => mret buf
  | p :: ps' =>
      if INTERNAL_BUFSIZ - zlength buf <? zlength p
      then (stdio_write 2 buf p ;;; stderr_pieces [] ps')
      else stderr_pieces (buf ++ p) ps'
  end.
Definition stderr_fprintf (pieces : list (list Z)) : M unit :=
  buf <- stderr_pieces [] pieces ;;
  stdio_write 2 buf [].

(* [comment removed for export] *)
Definition stderr_fwrite (s : list Z) : M unit :=
  if 0 <? zlength s then stdio_write 2 [] s else mret tt.
Definition stderr_fputs (s : list Z) : M unit := stderr_fwrite s.

End Stdio.

(* [comment removed for export] *)
Definition str (s : string) : list Z :=
  map (fun a => Z.of_N (N_of_ascii a)) (list_ascii_of_string s).

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint digits_aux (fuel : nat) (n : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => if n =? 0 then acc else digits_aux f (n / 10) (48 + n mod 10 :: acc)
  end.
Definition fmt_u (n : Z) : list Z := digits_aux 20 n [].

(* [comment removed for export] *)
Definition pieces_pct_d (v : Z) : list (list Z) :=
  if v =? 0 then [ []; []; [48]; []; [10] ]
  else if v <? 0 then [ []; [45]; fmt_u (- v); [10] ]
  else [ []; []; fmt_u v; [10] ].
(* [comment removed for export] *)
Definition pieces_usage (argv0 : list Z) : list (list Z) :=
  [ str "usage: "; []; []; argv0; str " INPUT" ++ [10] ].
(* [comment removed for export] *)
Definition pieces_cannot_open (path : list Z) : list (list Z) :=
  [ str "cli: cannot open "; []; []; path; [10] ].
(* [comment removed for export] *)
Definition pieces_read_error (path : list Z) : list (list Z) :=
  [ str "cli: read error on "; []; []; path; [10] ].
(* [comment removed for export] *)
Definition pieces_oom : list (list Z) := [ str "cli: out of memory" ++ [10] ].
(* [comment removed for export] *)
Definition pieces_too_big : list (list Z) :=
  [ str "cli: input >= "; []; []; str "67108864"; str " bytes, refused" ++ [10] ].
(* [comment removed for export] *)
Definition pieces_short_hdr : list (list Z) := [ str "cli: input shorter than header" ++ [10] ].
(* [comment removed for export] *)
Definition pieces_cfg_overrun : list (list Z) := [ str "cli: config_len overruns input" ++ [10] ].
(* [comment removed for export] *)
Definition msg_new_handler : list Z := str "DissectQueryMallocFuzzer: out of memory" ++ [10].

(* [comment removed for export] *)
Example pieces_usage_concat :
  concat (pieces_usage (str "prog")) = str "usage: prog INPUT" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example pieces_pct_d_0 : concat (pieces_pct_d 0) = str "0" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example pieces_pct_d_m120 : concat (pieces_pct_d (-120)) = str "-120" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example after_last_nl_ex1 : after_last_nl (str "ab" ++ [10] ++ str "cd") = 3.
Proof. vm_compute. reflexivity. Qed.
Example after_last_nl_ex2 : after_last_nl (str "abc") = 0.
Proof. vm_compute. reflexivity. Qed.
Example iov_advance_ex1 : iov_advance [[1;2;3];[4;5]] 3 = [[];[4;5]].
Proof. vm_compute. reflexivity. Qed.
Example iov_advance_ex2 : iov_advance [[1;2;3];[4;5]] 4 = [[5]].
Proof. vm_compute. reflexivity. Qed.
Example iov_advance_ex3 : iov_advance [[];[4;5]] 1 = [[5]].
Proof. vm_compute. reflexivity. Qed.
