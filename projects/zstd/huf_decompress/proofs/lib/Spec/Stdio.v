(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Stdio () := "C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List9fold_leftc59OSSVerify5KrLib4Spec5Stdio6upd_soC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5Stdio@stdio_write_loopC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K46Stdlib7Strings5Ascii5ascii01c59OSSVerify5KrLib4Spec5Stdio3strC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5Stdio<pieces_usageC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatK46Stdlib7Strings6String6string02C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01K46Stdlib7Strings6String6string01c59OSSVerify5KrLib4Spec5Stdio<pieces_pct_dC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums1Z03c59OSSVerify5KrLib4Spec5Stdio=after_last_nlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5Stdio;iov_advanceC1?~~~~~~~~~~~~~~~".
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
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;2p;8p;3p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Mp4p7210p8p1000kp4p710p1001ap4p710p8g002aj1ATg003Aj11Tg003fj10Tg004Kj16Tg004ij1>Tg005Ij2<Tg005cj82Tg006Bj1:Tg0075j1;Tg0081j2@Tg008Lj25Tg008mj3?Tg009Jj3=Tg009dj38Tf0R0#1#6p=9g00:DR1f1R2#6;80p=3f2R3A8120581p=7f4f31520,53'5'5p=4%A1R3g00:bR2#1R0#1#0R4#1#0R5#1%04R4#1R6#1%00R0#0R7#0#0#1%17R7#1#9R8%07#9%02R2#0R7#0#0#0#6R9%04#0#6%06%10#1#1#1%17R7#0#0#1%17#1#0%12#0R2#0#0#0%12#0R7#1%07%>1,32R2'3'3'3'3'39789'3'337,3537'3'3'3'<g00;GR5P5P5P5g00;gR9P9P9P5G2R8P5P9P5P5P9P9P9P5G2R7P9P9P9P9P5P9P9P5G2R0P9P9P9P5P5P9P9P5G2R6g00<GR4D4#:#;,@1P9P5P9P5P9P9P9P5G2P9P9P5P5P9P9P9P5G2P9P5P5P5P5P9P9P5G2P6P9P5P9P5P5P9P9P5G2P5P9P5P9P9P9P5P5G2P5P5P5P5P5P9P5P5G2R:P8P7P0P6P:P9P5P5P9P5P5P9P5G2P5P9P9P9P5P5P9P5G2P5P5P5P5P9P5P9P5G2P9P5P9P5P9P5P9P5G2P5P5P9P5P9P5P9P5G2/54D4D4D4D4#:=?125=3do"). Qed.
Example pieces_pct_d_0 : concat (pieces_pct_d 0) = str "0" ++ [10].
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;3p;2p;8g002aj1=Tg003Aj13Tg003fj10Tg004Kj12Tg004ij1<Tg009dj31Tg005Ij2:Tg00<hj15Tg0081j26Tg005cj87Tg008Lj24Tg006Bj18Tg008mj39Tg009Jj3;Tg00:DR0#=R1g00:bR2#3#0#0#0#0#2%02#3#0#2%<0510R2510':g00=d#5,60g00;GR3P3P3P3g00;gR4P4P3P3G7g00<G'4#8=9025;1do"). Qed.
Example pieces_pct_d_m120 : concat (pieces_pct_d (-120)) = str "-120" ++ [10].
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;3p;2p;8g002aj1>Tg003fj10Tg003Aj11Tg004Kj12Tg004ij1=Tg009dj33Tg005Ij2:Tg00>Bj19Tg00<hj18Tg0081j27Tg005cj84Tg008Lj25Tg006Bj16Tg008mj3<Tg009Jj3;Tg00:DR0#>R1g00:bR2#0#1R3#1#0#1#2%12R2#0#0R4#0R5#1#2%14#0#2%05#2%03#2%=0530R3530530530530':%12#1#0#0#0#9#8,70g00;gR2g00;GR5P2P2P5P2P5P5G4P2P5P5P5P2P2P5P5G4P5P2P5P5P2P2P5P5G4P5P5P5P5P2P2P5P5G4g00<G'5'5'5'5#6=<035;1do"). Qed.
Example after_last_nl_ex1 : after_last_nl (str "ab" ++ [10] ++ str "cd") = 3.
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;2p;8p;3g003Aj12Tg004Kj16Tg005Ij2;Tg005cj80Tg008Lj21Tg006Bj15Tg003fj13Tg004ij1:Tg009dj39Tg008mj34Tg00>`j17Tg009Jj38Tg00:DR0g00:bR1#2#6R2';g00;gR3g00;GR4P4P4P4P3P3P4G0P4P3P4P4P4P3P3P4G0g00<GR5'1'1#5%31#2#3#6%:0590P3P3P4P4P4P3P3P4G0P4P4P3P4P4P3P3P4G0/15'1#5540540#7=802do"). Qed.
Example after_last_nl_ex2 : after_last_nl (str "abc") = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;2p;8p;1p;3g005Ij25Tg005cj81Tg008Lj20Tg006Bj12Tg00>`j14Tg009Jj33Tg00:DR0g00=dR1'5g00;gR2g00;GR3P3P3P3P2P2P3G1P3P2P3P3P3P2P2P3G1P2P2P3P3P3P2P2P3G1g00<G'0'0'0#2#4=301do"). Qed.
Example iov_advance_ex1 : iov_advance [[1;2;3];[4;5]] 3 = [[];[4;5]].
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;3p;2g002aj15Tg004ij13Tg003fj12Tg004Kj11Tg003Aj14Tg009dj30Tg005Ij28Tg00?]j27Tg009Jj36Tg00:DR0#5R1#5R2%30R3g00:bR4#2R5#2#1%45#1=003500%31501R6501R7'8%14%15%44#1R4=003500500=016/74=627do"). Qed.
Example iov_advance_ex2 : iov_advance [[1;2;3];[4;5]] 4 = [[5]].
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;3p;2g002aj15Tg003fj13Tg003Aj12Tg004Kj11Tg004ij14Tg009dj30Tg005Ij28Tg00?]j27Tg009Jj36Tg00:DR0#5R1#5R2g00:bR3#3R4#2#1%40R5500R6%41R7501R8'8%13%14%23#1=005500500%34#1R4=006=017501/74=628do"). Qed.
Example iov_advance_ex3 : iov_advance [[];[4;5]] 1 = [[5]].
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;3p;2g002aj14Tg003fj12Tg003Aj17Tg004Kj11Tg004ij13Tg009dj30Tg005Ij28Tg00?]j26Tg009Jj35Tg00:DR0#4R1#4R2g00:bR3#2R4#7#1%30R5500R6%31R7501R8'8%24#1=006=0179015%13'6=528do"). Qed.
