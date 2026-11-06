(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition to_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition of_bytes (l : list byte) : list Z := map bv_unsigned l.

(* [comment removed for export] *)
Definition FILE_SIZEOF : Z := 232.        (* [comment removed for export] *)
Definition FILE_ALLOC : Z := 1264.        (* [comment removed for export] *)
Definition FILE_BUF_OFF : Z := 240.       (* [comment removed for export] *)
Definition BUFSIZ : Z := 1024.
Definition INTERNAL_BUFSIZ : Z := 80.     (* [comment removed for export] *)
Definition FOPEN_MODE : Z := 438.         (* [comment removed for export] *)
Definition MKSTEMP_MODE : Z := 384.       (* [comment removed for export] *)
Definition TIOCGWINSZ : Z := 21523.       (* [comment removed for export] *)
Definition SEEK_CUR : Z := 1.

(* [comment removed for export] *)
Record file_st := mkFile {
  f_fd : Z;
  f_chan : bool;
  f_bufsize : Z;
  f_nord : bool;
  f_nowr : bool;
  f_eof : bool;
  f_wactive : bool;
  f_wbuf : list Z;
  f_rbuf : list Z;
  f_lbf_nl : bool;
  f_stdoutw : bool
}.

(* [comment removed for export] *)
Definition set_w (act : bool) (wb : list Z) (f : file_st) : file_st :=
  mkFile (f_fd f) (f_chan f) (f_bufsize f) (f_nord f) (f_nowr f) (f_eof f)
         act wb (f_rbuf f) (f_lbf_nl f) (f_stdoutw f).
Definition set_rbuf (rb : list Z) (f : file_st) : file_st :=
  mkFile (f_fd f) (f_chan f) (f_bufsize f) (f_nord f) (f_nowr f) (f_eof f)
         (f_wactive f) (f_wbuf f) rb (f_lbf_nl f) (f_stdoutw f).
Definition set_eof (f : file_st) : file_st :=
  mkFile (f_fd f) (f_chan f) (f_bufsize f) (f_nord f) (f_nowr f) true
         (f_wactive f) (f_wbuf f) (f_rbuf f) (f_lbf_nl f) (f_stdoutw f).
Definition set_bufsize (n : Z) (f : file_st) : file_st :=
  mkFile (f_fd f) (f_chan f) n (f_nord f) (f_nowr f) (f_eof f)
         (f_wactive f) (f_wbuf f) (f_rbuf f) (f_lbf_nl f) (f_stdoutw f).
Definition after_ioctl (f : file_st) : file_st :=   (* [comment removed for export] *)
  mkFile (f_fd f) (f_chan f) (f_bufsize f) (f_nord f) (f_nowr f) (f_eof f)
         (f_wactive f) (f_wbuf f) (f_rbuf f) false false.

(* [comment removed for export] *)
Definition fdopen_file (fd : Z) (wr : bool) : file_st :=
  mkFile fd false BUFSIZ wr (negb wr) false false [] [] false false.

(* [comment removed for export] *)
Definition stdout_init : file_st :=
  mkFile 1 true BUFSIZ true false false false [] [] true true.
Definition stderr_init : file_st :=
  mkFile 2 true 0 true false false false [] [] false false.

(* [comment removed for export] *)
Definition dec_close_ok (rsp : resp) : option unit :=
  match dec_close rsp with Some (SVal _) => Some tt | _ => None end.
Definition dec_lseek_ok (rsp : resp) : option Z :=
  match dec_lseek rsp with Some (SVal v) => Some v | _ => None end.
Definition dec_writevf_ok (total : Z) (rsp : resp) : option Z :=
  match dec_writevf total rsp with Some (SVal v) => Some v | _ => None end.

Section Core.
Context {St : Type}.
Let M := @M St.

(* [comment removed for export] *)
Definition after_last_nl (s : list Z) : Z :=
  fold_left (fun acc ib => if snd ib =? 10 then fst ib + 1 else acc)
            (combine (map Z.of_nat (seq 0 (length s))) s) 0.

(* [comment removed for export] *)
Definition towrite (f : file_st) : M file_st :=
  if f_nowr f then munr else mret (set_w true [] (set_rbuf [] f)).

(* [comment removed for export] *)
Definition ensure_w (f : file_st) : M file_st :=
  if f_wactive f then mret f else towrite f.

(* [comment removed for export] *)
Definition wnode (f : file_st) (iovs : list (list Z)) : node :=
  if f_chan f then NWritev (f_fd f) (map to_bytes iovs) else NWritevF (f_fd f) (map to_bytes iovs).
(* [comment removed for export] *)
Definition wdec (f : file_st) (rem : Z) : resp -> option Z :=
  if f_chan f then dec_writev rem else dec_writevf_ok rem.

Definition advance_iovs (iovs : list (list Z)) (cnt : Z) : list (list Z) :=
  match iovs with
  | [] => []
  | b0 :: rest =>
      if zlength b0 <? cnt
      then match rest with
           | [] => []
           | b1 :: rest' => skipn (Z.to_nat (cnt - zlength b0)) b1 :: rest'
           end
      else skipn (Z.to_nat cnt) b0 :: rest
  end.

Fixpoint writev_loop (fuel : nat) (f : file_st) (iovs : list (list Z)) (rem : Z) : M unit :=
  match fuel with
  | O => munr
  | S fuel' =>
      cnt <- msys (wnode f iovs) (wdec f rem) ;;
      if cnt =? rem then mret tt
      else writev_loop fuel' f (advance_iovs iovs cnt) (rem - cnt)
  end.

Definition stdio_write (f : file_st) (s : list Z) : M file_st :=
  let B := f_wbuf f in
  let iovs := match B with [] => [s] | _ => [B; s] end in
  let rem := zlength B + zlength s in
  writev_loop (S (Z.to_nat rem)) f iovs rem ;;;
  mret (set_w true [] f).

(* [comment removed for export] *)
Definition file_writefn (f : file_st) (s : list Z) : M file_st :=
  if f_stdoutw f then
    r <- msys (NIoctl (f_fd f) TIOCGWINSZ) dec_ioctl ;;
    match r with
    | SErr _ => stdio_write (after_ioctl f) s
    | SVal _ => munr
    end
  else stdio_write f s.

(* [comment removed for export] *)
Definition fwritex (f : file_st) (s : list Z) : M file_st :=
  f1 <- ensure_w f ;;
  if f_bufsize f1 - zlength (f_wbuf f1) <? zlength s
  then file_writefn f1 s
  else if f_lbf_nl f1 then
    let i := after_last_nl s in
    f2 <- (if 0 <? i then file_writefn f1 (firstn (Z.to_nat i) s) else mret f1) ;;
    mret (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2)
  else mret (set_w true (f_wbuf f1 ++ s) f1).

(* [comment removed for export] *)
Definition fwrite_file (f : file_st) (s : list Z) : M file_st := fwritex f s.

(* [comment removed for export] *)
Fixpoint out_pieces (f : file_st) (ps : list (list Z)) : M file_st :=
  match ps with
  | [] => mret f
  | p :: ps' => f' <- fwritex f p ;; out_pieces f' ps'
  end.

Definition vfprintf (f : file_st) (ps : list (list Z)) : M file_st :=
  if f_bufsize f =? 0 then
    f1 <- towrite (set_w false [] (set_bufsize INTERNAL_BUFSIZ f)) ;;
    f2 <- out_pieces f1 ps ;;
    f3 <- file_writefn f2 [] ;;
    mret (set_w false [] (set_bufsize 0 f3))
  else
    f1 <- ensure_w f ;;
    out_pieces f1 ps.

(* [comment removed for export] *)
Definition toread (f : file_st) : M (bool * file_st) :=
  f1 <- (match f_wbuf f with [] => mret f | _ => file_writefn f [] end) ;;
  let f2 := set_w false [] f1 in
  if f_nord f2 then munr else mret (f_eof f2, set_rbuf [] f2).

(* [comment removed for export] *)
Definition stdio_read (f : file_st) (bufaddr dest len : Z) : M (list Z * file_st) :=
  let len0 := len - (if f_bufsize f =? 0 then 0 else 1) in
  let iovs := [(dest, len0); (bufaddr, f_bufsize f)] in
  a <- (if len0 =? 0
        then msys (NRead (f_fd f) bufaddr (f_bufsize f)) (dec_read bufaddr (f_bufsize f))
        else msys (NReadv (f_fd f) iovs) (dec_readv iovs)) ;;
  match a with
  | RdErr _ => munr
  | RdData bs =>
      let bs := of_bytes bs in
      let cnt := zlength bs in
      if cnt =? 0 then mret ([], set_eof f)
      else if cnt <=? len0 then mret (bs, f)
      else
        let tobuf := skipn (Z.to_nat len0) bs in
        if f_bufsize f =? 0 then mret (bs, set_rbuf tobuf f)   (* [comment removed for export] *)
        else mret (firstn (Z.to_nat len0) bs ++ firstn 1 tobuf, set_rbuf (skipn 1 tobuf) f)
  end.

(* [comment removed for export] *)
Fixpoint fread_loop (fuel : nat) (f : file_st) (bufaddr dest l : Z) (acc : list Z) : M (list Z * file_st) :=
  match fuel with
  | O => munr
  | S fuel' =>
      if l <=? 0 then mret (acc, f)
      else
        ef <- toread f ;;
        bf <- (if fst ef then mret ([], snd ef) else stdio_read (snd ef) bufaddr dest l) ;;
        match fst bf with
        | [] => mret (acc, snd bf)
        | _ => fread_loop fuel' (snd bf) bufaddr (dest + zlength (fst bf)) (l - zlength (fst bf)) (acc ++ fst bf)
        end
  end.

Definition fread_file (f : file_st) (bufaddr dest n : Z) : M (list Z * file_st) :=
  let k := Z.min (zlength (f_rbuf f)) n in
  let pre := firstn (Z.to_nat k) (f_rbuf f) in
  fread_loop (S (Z.to_nat n)) (set_rbuf (skipn (Z.to_nat k) (f_rbuf f)) f) bufaddr (dest + k) (n - k) pre.

(* [comment removed for export] *)
Definition sync_read_pos (f : file_st) : M unit :=
  match f_rbuf f with
  | [] => mret tt
  | _ => _ <- msys (NLseek (f_fd f) (- zlength (f_rbuf f)) SEEK_CUR) dec_lseek_ok ;; mret tt
  end.

Definition fflush_file (f : file_st) : M file_st :=
  f1 <- (match f_wbuf f with [] => mret f | _ => file_writefn f [] end) ;;
  sync_read_pos f1 ;;;
  mret (set_rbuf [] (set_w false [] f1)).

(* [comment removed for export] *)
Definition close_file (f : file_st) : M unit :=
  f1 <- (match f_wbuf f with [] => mret f | _ => file_writefn f [] end) ;;
  sync_read_pos f1.

(* [comment removed for export] *)
Definition fclose_file (f : file_st) : M unit :=
  f1 <- fflush_file f ;;
  msys (NClose (f_fd f1)) dec_close_ok.

End Core.

(* [comment removed for export] *)
#[using="Type"] Example advance_ex1 : advance_iovs [[1;2;3];[4;5]] 2 = [[3];[4;5]].
Proof. reflexivity. Qed.
#[using="Type"] Example advance_ex2 : advance_iovs [[1;2;3];[4;5]] 3 = [[];[4;5]].   (* [comment removed for export] *)
Proof. reflexivity. Qed.
#[using="Type"] Example advance_ex3 : advance_iovs [[1;2;3];[4;5]] 4 = [[5]].
Proof. reflexivity. Qed.
#[using="Type"] Example advance_ex4 : advance_iovs [[];[4;5]] 1 = [[5]].
Proof. reflexivity. Qed.
#[using="Type"] Example after_last_nl_ex1 : after_last_nl (str "ab"%string ++ [10] ++ str "cd"%string) = 3.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Example after_last_nl_ex2 : after_last_nl (str "abc"%string) = 0.
Proof. vm_compute. reflexivity. Qed.

End WithCeil.
