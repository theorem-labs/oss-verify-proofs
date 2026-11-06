(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Stdio () := "C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List9fold_leftI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K46Stdlib7Strings5Ascii5ascii01C69OSSVerify5KrLib2K54Spec6Prelim3strC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec5Stdio<pieces_usageC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatK46Stdlib7Strings6String6string02C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01K46Stdlib7Strings6String6string01c69OSSVerify5KrLib2K54Spec5StdioCpieces_precond_failC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54Spec5Stdio=after_last_nlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib2K54Spec5Stdio;iov_advanceC1?~~~~~~~~~~~~~~~".
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

(* [comment removed for export] *)
Definition iov_total (iovs : list (list Z)) : Z := zlength (concat iovs).

(* [comment removed for export] *)
Definition iov_start (buf s : list Z) : list (list Z) :=
  match buf with [] => [s] | _ => [buf; s] end.

(* [comment removed for export] *)
Definition iov_advance (iovs : list (list Z)) (cnt : Z) : list (list Z) :=
  match iovs with
  | [] => []
  | a :: rest =>
      if zlength a <? cnt
      then match rest with
           | [] => []                                  (* [comment removed for export] *)
           | b :: rest' => zdrop (cnt - zlength a) b :: rest'
           end
      else zdrop cnt a :: rest
  end.

Section Stdio.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Let M := @M St.
Definition upd_so (f : stdout_st -> stdout_st) : M unit := mupd (fun s => set_so (f (get_so s)) s).
Definition rd_so : M stdout_st := mbind mget (fun s => mret (get_so s)).

(* [comment removed for export] *)
Definition wv_body (fd : Z) (iovs : list (list Z)) : M (list (list Z) + unit) :=
  k <- msys (NWritev fd (map to_bytes iovs)) (dec_writev (iov_total iovs)) ;;
  if k =? iov_total iovs then mret (inr tt)
  else mret (inl (iov_advance iovs k)).

(* [comment removed for export] *)
Definition WV_FUEL (iovs : list (list Z)) : nat := S (Z.to_nat (iov_total iovs)).

(* [comment removed for export] *)
Definition stdio_writev (fd : Z) (buf s : list Z) : M unit :=
  mloop (WV_FUEL (iov_start buf s)) (wv_body fd) (iov_start buf s).

(* [comment removed for export] *)
Definition stdout_stdio_write (s : list Z) : M unit :=
  so <- rd_so ;;
  stdio_writev 1 (so_buf so) s ;;;
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
  if STDOUT_BUFSIZ - zlength (so_buf so) <? zlength s
  then stdout_writefn s
  else if so_lbf_nl so then
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
      then (stdio_writev 2 buf p ;;; stderr_pieces [] ps')
      else stderr_pieces (buf ++ p) ps'
  end.
Definition stderr_fprintf (pieces : list (list Z)) : M unit :=
  buf <- stderr_pieces [] pieces ;;
  stdio_writev 2 buf [].

(* [comment removed for export] *)
Definition stderr_fwrite (s : list Z) : M unit :=
  if 0 <? zlength s then stdio_writev 2 [] s else mret tt.

End Stdio.

(* [comment removed for export] *)

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition pieces_emit_0 : list (list Z) := [ []; []; [48]; []; [10] ].
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
Definition pieces_precond_fail (x fn : list Z) : list (list Z) :=
  [ str "p11-kit: '"; []; []; x; str "' not true at "; []; []; fn; [10] ].
Definition pieces_precond_reached (fn : list Z) : list (list Z) :=
  [ str "p11-kit: shouldn't be reached at "; []; []; fn; [10] ].

(* [comment removed for export] *)
Example pieces_usage_concat :
  concat (pieces_usage (str "prog")) = str "usage: prog INPUT" ++ [10].
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;2p;8p;3p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Mp4p7210p8g000kj1ATg001Kj11Tg0020j10Tg002Uj16Tg0033j1>Tg003Sj2<Tg003mj82Tg004Lj1:Tg005Cj1;Tg006Bj2@Tg006]j25Tg007>j3?Tg007[j3=Tg0085j38Tf0R0#1#6p=9g008UR1f1R2#6;80p=3f2R3A8120581p=7f4f31520,53'5'5p=4%A1R3g0093R2#1R0#1#0R4#1#0R5#1%04R4#1R6#1%00R0#0R7#0#0#1%17R7#1#9R8%07#9%02R2#0R7#0#0#0#6R9%04#0#6%06%10#1#1#1%17R7#0#0#1%17#1#0%12#0R2#0#0#0%12#0R7#1%07%>1,32R2'3'3'3'3'39789'3'337,3537'3'3'3'<g009XR5P5P5P5g00:8R9P9P9P5G2R8P5P9P5P5P9P9P9P5G2R7P9P9P9P9P5P9P9P5G2R0P9P9P9P5P5P9P9P5G2R6g00:XR4D4#:#;,@1P9P5P9P5P9P9P9P5G2P9P9P5P5P9P9P9P5G2P9P5P5P5P5P9P9P5G2P6P9P5P9P5P5P9P9P5G2P5P9P5P9P9P9P5P5G2P5P5P5P5P5P9P5P5G2R:P8P7P0P6P:P9P5P5P9P5P5P9P5G2P5P9P9P9P5P5P9P5G2P5P5P5P5P9P5P9P5G2P9P5P9P5P9P5P9P5G2P5P5P9P5P9P5P9P5G2/54D4D4D4D4#:=?125=3do"). Qed.
Example pieces_precond_concat :
  concat (pieces_precond_fail (str "lexer->filename != NULL") (str "p11_lexer_init"))
  = str "p11-kit: 'lexer->filename != NULL' not true at p11_lexer_init" ++ [10].
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;2p;8p;3g000kj1ETg001Kj10Tg0020j12Tg002Uj1;Tg0033j1BTg003Sj2>Tg003mj81Tg006]j29Tg004Lj1<Tg00;9j2DTg006Bj2CTg007>j3ATg007[j3@Tg0085j37Tf0R0#2#;p=5%00#;p=8g008UR1f1R2#;;70p=6A7120p=?f2R3A7120571p=:f4R4f3R5A71209713571571p=41920,93p==1920,93,95,94p=3%E1R4g0093R5#0R3#0R2#2R0#2R6#2#5R7%23R3#2R8#2R9#8R:P:%25R5#0R;#0R<#2#8R=%03R3#2R>#0#0%2>#8R>%00#2R0#5R?%25R5#2#2R@#5RA%05#0R5#0RB#;RC%03R3#2RD#5RE%08R8#2#8RF%02R2#2RG#2#5RHPF%06#5R6P=%02#2%08#2P>PEPF%03R3#5R8%29#8R9%8DPFPA%0@%0G%5B%2;R;#0#2#0%25#5R5P5PCPAP8%83P?PA%00PFPAP9P?PAP7P:P:%0<#0#8R<PEPFPHPFP6P<P>%B1,6;R;,??9:8>D4D4D4D4'69:?6D4D4'65:A'6'6D4D4'6'6D4D4,603:'6D4'>g009XR0P0g00:8RAPAP0PAPAP0G1R6PAP0PAP0P0PAPAP0G1R?P0P0P0PAPAPAPAP0G1R8P?P0PAP0P0PAPAPAP0G1R>PAP0PAPAP0PAP0P0G1R<P0PAPAPAPAPAP0P0G1RFP0PAPAP0P0PAPAP0G1RHPAP0P0PAP0PAPAP0G1REP6P?P0PAPAPAP0PAPAP0G1R:PAP0P0P0P0PAPAP0G1R7PAP0PAPAP0PAPAP0G1R9P?P0P0P0P0P0PAP0P0G1R3PAP0P0P0P0PAP0P0G1RCPAP0PAPAPAPAP0P0G1R5P3P0PAPAPAP0P0PAP0G1RBPAP0PAP0PAP0PAP0G1RGP0P0PAPAP0P0PAP0G1R@g00:XRD,9@3=D3D3D3D3D3#<P0P0P0P0PAPAPAP0G1R2PAP0P0P0PAPAP0P0G1R=P=PAPAPAPAPAP0PAP0G1RIP6P?P8P?P>PIPEP:P0P0PAP0PAPAPAP0G1RI==EDD3D3D3RD#<'D,C1P2P=P=P<PAPAP0PAP0PAPAP0G1PEPIP0PAP0PAPAPAP0P0G1P3PAPAPAP0P0PAP0P0G1R=P6P?P8P?P>P<PFPHPEP6P?P:P7P9P?P3PCP5P3PBPGP@P@P=P3P:PAPAPAPAP0PAPAP0G1PIP3PIP>PAP0PAP0PAPAPAP0G1P?P3193D9=7ID3D3D3D3D3D3D3D3D3D3D3#<=A1;5@4do"). Qed.
Example after_last_nl_ex1 : after_last_nl (str "ab" ++ [10] ++ str "cd") = 3.
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;2p;8p;3g001Kj12Tg002Uj16Tg003Sj2;Tg003mj80Tg006]j21Tg004Lj15Tg0020j13Tg0033j1:Tg0085j39Tg007>j34Tg00<?j17Tg007[j38Tg008UR0g0093R1#2#6R2';g00:8R3g009XR4P4P4P4P3P3P4G0P4P3P4P4P4P3P3P4G0g00:XR5'1'1#5%31#2#3#6%:0590P3P3P4P4P4P3P3P4G0P4P4P3P4P4P3P3P4G0/15'1#5540540#7=802do"). Qed.
Example after_last_nl_ex2 : after_last_nl (str "abc") = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;2p;8p;1p;3g003Sj25Tg003mj81Tg006]j20Tg004Lj12Tg00<?j14Tg007[j33Tg008UR0g00=?R1'5g00:8R2g009XR3P3P3P3P2P2P3G1P3P2P3P3P3P2P2P3G1P2P2P3P3P3P2P2P3G1g00:X'0'0'0#2#4=301do"). Qed.
Example iov_advance_ex1 : iov_advance [[48]; [10]] 1 = [[]; [10]].
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;3p;2g000kj15Tg0033j14Tg0020j10Tg001Kj13Tg002Uj12Tg0085j31Tg003Sj28Tg00=]j27Tg007[j36Tg008UR0#5R1#5R2%40R3g0093R4#0#3#0#2=103%41511R5511R6'8%34#0#0#0#0#2=103=115%24'7=626do"). Qed.
Example iov_advance_ex2 : iov_advance [[48;48]; [10;10]] 3 = [[10]].
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio ()) [] "p;1p;3p;2g000kj15Tg0020j11Tg001Kj13Tg002Uj12Tg0033j14Tg0085j30Tg003Sj28Tg00=]j27Tg007[j36Tg008UR0#5R1#5R2g0093R3#1#3#1#2R4%40R5500R6%41R7501R8'8%33R3#1#1#1#1#2R9A0095500A0046=017501%23'7=628do"). Qed.
