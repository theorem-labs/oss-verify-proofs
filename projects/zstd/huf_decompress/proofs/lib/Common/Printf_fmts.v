(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp Printf_model.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Printf_fmts () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01K46Stdlib7Strings5Ascii5ascii01K46Stdlib7Strings6String6string02C59OSSVerify5KrLib4Spec5Stdio3strC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model=printf_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_usageC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib6Common;Printf_fmts9FMT_usageC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01K46Stdlib7Strings6String6string01C59OSSVerify5KrLib4Spec5StdioBpieces_cannot_openC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;Printf_fmts?FMT_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioApieces_read_errorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;Printf_fmts>FMT_read_errorC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;Printf_fmts;FMT_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>pieces_too_bigC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib6Common<Printf_model4parg02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_pct_dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;Printf_fmts9FMT_pct_dC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef6repeatI47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib6Common<Printf_model8pass1_okC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition FMT_pct_d : list Z := [37; 100; 10; 0].                                 (* [comment removed for export] *)
Definition FMT_usage : list Z := str "usage: %s INPUT" ++ [10; 0].                  (* [comment removed for export] *)
Definition FMT_too_big : list Z := str "cli: input >= %u bytes, refused" ++ [10; 0]. (* [comment removed for export] *)
Definition FMT_cannot_open : list Z := str "cli: cannot open %s" ++ [10; 0].       (* [comment removed for export] *)
Definition FMT_read_error : list Z := str "cli: read error on %s" ++ [10; 0].      (* [comment removed for export] *)
Definition A_FMT_pct_d : Z := 0x10300.
Definition A_FMT_usage : Z := 0x1030d.
Definition A_FMT_too_big : Z := 0x103a7.
Definition A_FMT_cannot_open : Z := 0x103c8.
Definition A_FMT_read_error : Z := 0x103dd.
(* [comment removed for export] *)
Definition A_MSG_oom : Z := 0x102ec.          (* [comment removed for export] *)
Definition A_MSG_short_hdr : Z := 0x103fc.    (* [comment removed for export] *)
Definition A_MSG_cfg_overrun : Z := 0x1031e.  (* [comment removed for export] *)
Definition A_MSG_new_handler : Z := 0x12ed7.  (* [comment removed for export] *)

(* [comment removed for export] *)
Example pieces_usage_ex : printf_pieces FMT_usage [PA_s (str "prog")] = Some (pieces_usage (str "prog"), 18).
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_fmts ()) [] "p;1p;2p;3p;4p;8g0000j1>Tg000Pj2FTg0010j1@Tg001Rj11Tg0027j10Tg002\j13Tg003:j19Tg003Zj32Tg004:j4=Tg004Zj2<Tg005<j2ETg005Vj86Tg0065j25Tg006Vj1DTg007Ij1CTg008Hj2BTg009Nj1ATg00:Jj3?Tf0R0#1#3p=8g00:dR1f1R2;20p=;%32=210p=7f2R3A2120521p=:%33%32=210521p=4%>1R0#>R2/F1R3#@R4P2P1g00;BR5#1R6#1#0R7#1#0R8#1%07R7#1R9#1%06R6#0R:#0#0#1%1:R:#1#8R;%0:#8%05R5#0R:#0#0#0#3R<%91R=';,783:'734%07#0%09%16#1#1#11;;='734%1:R:#0R;#0#8%1:#1#0%15#0R5#0#0#0%15#0R:#1%0:175=34345:<%90520520920=920=520%3;R;C=,<3'Eg00;gg00<hR0g00=gR=P=P=P=g00>GR<P<P<P=G6P=P<P=P=P<P<P<P=G6P<P<P<P<P=P<P<P=G6P<P<P<P=P=P<P<P=G6g00>g'5'5'5'5#DR=#C%9032'BP2P1%A=P;C=,<35?4do"). Qed.
Example pieces_cannot_open_ex : printf_pieces FMT_cannot_open [PA_s (str "f")] = Some (pieces_cannot_open (str "f"), 19).
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_fmts ()) [] "p;1p;2p;3p;4p;8g0000j19Tg000Pj2CTg0010j1;Tg001Rj11Tg0027j10Tg002\j13Tg003:j16Tg003Zj32Tg004:j47Tg004Zj28Tg005<j2:Tg005Vj8BTg0065j2ATg006Vj1@Tg007Ij1=Tg008Hj2>Tg00?Hj1?Tg00:Jj3<Tg00:dR0f2f1R1f0R252032p=5%31=202p=4%90R2#9R1/C0R3#;R4P1P0g00;BR5#1R6#0R7#0R8#0R9#1#1#3R:%17R7#1R;#0#0#3%07#0#1%16#0R6#1#0R7%05R5#0R<#0#0#0#3R=%09#1%1;R;#0#3R9%1;#3R;%07#3%06#0#0%18R8#0#1%60R6959='4'495=;35759'475:'4'435%18#0/46%15#0/46%6252252292269226522%1<#1#3R<C7,83':g00@Jg00<hR2g00=gR6g00>GR5P5P6P6P5P5P6GBg00>g'A#@R6#=%6232'>P1P0%?6P<C7,835<4do"). Qed.
Example pieces_read_error_ex : printf_pieces FMT_read_error [PA_s (str "f")] = Some (pieces_read_error (str "f"), 21).
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_fmts ()) [] "p;1p;2p;3p;4p;8g0000j19Tg000Pj2DTg0010j1;Tg001Rj11Tg0027j10Tg002\j14Tg003:j16Tg003Zj32Tg004:j47Tg004Zj28Tg005<j2CTg005Vj8BTg0065j2ATg006Vj1=Tg007Ij1>Tg008Hj2?Tg00AQj1<Tg00:Jj3@Tg00:dR0f1R1f0R232p=:%41=202p=3f2A2012520p=5%90R2#9R1/D0R3#;R4P1P0g00;BR5#1R6#0R7#0R8#0R9#1#1%17R7#1R:#0#0%07#0#1%16#0R6#1#0%05R5#0#0#0#0#4R7%06#1#0#4R6%18R8#0R;#1#4R<%09#1#4%0;%1:R:#1#4R;%0:%60R:,:7'3957;7569566957<'33535'3'3'3'3%18#0/3:%15#0R5/3:%62522522922:922:522%15#4R5C7,83'Cg00BRg00<hR2g00=gR:g00>GR8P8P:P:P8P8P:GBg00>g'A#=R:#>%6232'?P1P0%<:P5C7,835@4do"). Qed.
Example pieces_too_big_ex : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_fmts ()) [] "p;1p;2p;3p;4g0000j1:Tg000Pj2DTg0010j1?Tg001Rj11Tg0027j10Tg002\j13Tg003:j18Tg003Zj32Tg004:j4=Tg004Zj2<Tg005<j2CTg00CXj1BTg008Hj2@Tg00:Jj3ATf0R0#0#0p=;%00#3p=5g00:dR1f1R2;20p=>%32=210p=4f4f3f2R3A2120521521521p=6A21209213p=9%00#0#0#0p=7%:1R0#:R3/D1R2#?R4P3P1g00;BR5#1R6#0R7#0R8#0R9#1R:#1%17R7#1R;#0R<#0%;7R7#1#3R=%16R6#0R>#1#0R?#3%05R5#0R@#0#;RA#3RBP=%1;R;#0%0>R>#0R=#0%1?#3RC%5?R?PB%16R6#1#5%06R6#1%81RD,>B'4D6'4'4D6'4'4%3<R<%3;%09%3=R=P=P<%37PDD6'4,4:39%5:%06#1P?%18R8#0R?#1#3R6%1>R>#1#3R:%15R5#1#0#5PB%5>P6%18#5PCP:P6%5?%05/4DD6D6D6'459B%80520520920D920D520%1@#1#5R@C=,<2'Cg00DWg00<hR0%7A#7#7#7#7#5#B%8032'@P3P1g00EZP@C=,<25A4do"). Qed.
Example pieces_pct_d_ex1 : printf_pieces FMT_pct_d [PA_i (-2147483648)] = Some (pieces_pct_d (-2147483648), 12).
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_fmts ()) [] "p;1p;2p;3p;4g0000j1;Tg000Pj2CTg0010j1<Tg003:j17Tg0027j10Tg001Rj11Tg002\j12Tg003Zj33Tg004:j48Tg004Zj2:Tg005<j2BTg00FXj1ATg00G6j1@Tg008Hj2?Tg00H5j1>Tg00:Jj3=Tg00:dR0f1R1f0R233p=9%02#0p=6f2A3012530p=5%02#0#0#0p=4%;0R2#;R1/C0R3#<R4P1P0%70R5g00;BR6#0R7#1R8#1#0#1#2/95%16R6#0R9#0R:#1R;#0#2%0:#1#2%19R9#6#2R<%19R9#1#2%16#0#6#2R6%1;#2%09#2A5<653555<3535%08#2/95%72532532532532%2:R:C8,:3'Bg00I1g00<hR2%67#4#4#4#4#4#4#4#AR7#@%7233'?P1P0%>7P:C8,:35=4do"). Qed.
Example pieces_pct_d_ex2 : printf_pieces FMT_pct_d [PA_i 0] = Some (pieces_pct_d 0, 2).
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_fmts ()) [] "p;1p;2p;3p;4g0000j16Tg000Pj2>Tg0010j1;Tg003:j13Tg001Rj17Tg0027j11Tg002\j12Tg003Zj30Tg004:j45Tg004Zj24Tg005<j28Tg00G6j19Tg008Hj2:Tg00H5j1=Tg00:Jj3<Tg00:dR0#6R1#6R2/>0R3#;R4P2P0%30R5g00;BR6#7#1#1#1#1#2=005%16R6#7#1#2=005%3150190155019015501%26R6C5,43'8g00I1g00<hR1g00J2R5#9%3130':P2P0%=5P6C5,435<4do"). Qed.
Example pieces_pct_d_ex3 : printf_pieces FMT_pct_d [PA_i 7] = Some (pieces_pct_d 7, 2).
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_fmts ()) [] "p;1p;2p;3p;4g0000j17Tg000Pj2>Tg0010j1;Tg003:j13Tg001Rj11Tg0027j14Tg002\j12Tg003Zj30Tg004:j46Tg004Zj25Tg005<j28Tg00G6j19Tg008Hj2:Tg00H5j1=Tg00:Jj3<Tg00:dR0#7R1#7R2/>0R3#;R4P2P0%30R5g00;BR6#1R7#4#1#1#1#2=005%46R6#1#4#2=005%315015019015501%26R6C6,53'8g00I1g00<hR1%17#2R7#9%3130':P2P0%=7P6C6,535<4do"). Qed.
Example fp_calls_pct_d_ex : fp_calls 4 FMT_pct_d [PA_i 5] = [].
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_fmts ()) [] "p;2p;1p;3g000Pj20Tg0000j1;Tg003:j12Tg005<j23Tg00JPj11Tg0027j1:Tg001Rj19Tg002\j14Tg00G6j15Tg003Zj36Tg00Joj37Tg00:Jj38Tg00:dR0/00/00/00/00R0#;R1%20R0'3g00L0#1#1#1#1g00I1g00<hR2g00;B#:#9#4#5%223637=810do"). Qed.
Example pass1_ok_ex : map pass1_ok [FMT_pct_d; FMT_usage; FMT_too_big; FMT_cannot_open; FMT_read_error] = repeat true 5.
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_fmts ()) [] "p;1p;2p;3p;4g0000j14Tg003:j13Tg005<j25Tg003Zj30Tg00LOj48Tg00JPj11Tg00Lkj37Tg00:Jj36Tg00MJR0g00>GR1f030p=2%40R2%30#2#2#2#2#2'5g00:d#4R3P0g00Mjg00I1g00;gg00DWg00@Jg00BR%33503503503503503C8g00L0#1#1#1#1#19701562do"). Qed.
