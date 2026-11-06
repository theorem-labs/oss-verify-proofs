(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Stdio Canon.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_ProgDetDriver () := "C46Stdlib5Lists4List9app_nil_rC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K46Stdlib7Strings5Ascii5ascii01C69OSSVerify5KrLib2K54Spec6Prelim3strC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list02K46Stdlib7Strings6String6string02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C46Stdlib5Lists4List9app_nil_lC46Stdlib5Lists4List6concatC69OSSVerify5KrLib2K54Spec5Stdio<pieces_usageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon9msg_usageC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01K46Stdlib7Strings6String6string01K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K54Spec5StdioBpieces_cannot_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon?msg_cannot_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5StdioApieces_read_errorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Canon>msg_read_errorC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma concat_pieces_usage : forall a, concat (pieces_usage a) = msg_usage a.
Proof.
ltac2:(KReplay.run1 (kr_t_ProgDetDriver ()) [] "h01lh11ap;1p;8p;3p;2p;6g0000R0p4p710g000NR1p4p710p8g000lj1CTg001Lj1;Tg001lj81Tg002Kj1:Tg003Bj18Tg003gj1>Tg004Lj1=Tg004jj32Tg005Jj26Tg005kj34Tg006Ej2<TP0j2BTP1j65Tg006_j27Tg007=j29Tg007Xj1ATg008Wj1@Tg009Sj3?Tf2f1R1f0R0'6'6p=3g00:0R2??10p=0%C2R3P3%;2R4g00:NR5P5P5P5P5g00:nR6P5P5G1R7P6P5P5P6P5P5P6P5G1P5P6P6P6P5P5P6P5G1P5P5P5P5P6P5P6P5G1P6P5P6P5P6P5P6P5G1P5P5P6P5P6P5P6P5G1g00;NR8333333#:g00;o#8#>#8#==224'0R9/04R:,00R;'0R<P6P5P6P5P6P6P6P5G1P6P6P5P5P6P6P6P5G1P6P5P5P5P5P6P6P5G1P6P6P6P5P5P6P6P5G1P6P5P6P5P5P6P6P5G1P5P6P5P6P6P6P5P5G11678333333#:R8/001019,08R7543X03R5P3P;P5P3P91010,08=437X031009,08R7,<3P:1B29E5P<172;E5104<172<E5%;392399230923492349238,92=437e%A0,92%@0543eW1o"). Qed.
Lemma concat_pieces_cannot_open : forall a, concat (pieces_cannot_open a) = msg_cannot_open a.
Proof.
ltac2:(KReplay.run1 (kr_t_ProgDetDriver ()) [] "h01ah11lp;1p;3p;8p;2p;6g000lj1BTg001Lj1:Tg003Bj17Tg003gj1=Tg004Lj1ATg004jj33Tg001lj80Tg005Jj24Tg002Kj1<Tg005kj35Tg006Ej2;Tg006_j29Tg000Nj66Tg007=j28Tg00<Tj1@Tg00=Yj1?Tg009Sj3>Tg00:0R0f1R1f0R23>p=1f21412'4p=2%B0R3P3%:0R4g00;o#7#=#7#A=304R5/14,12R6'1R7g00:nR8P8g00:NR9P9P9P8P8P9G0R:P9P9P8P8P9P8P8P9G0P8P9P9P8P9P8P8P9G0P9P8P9P8P8P8P9P9G0P9P9P9P9P9P8P9P9G0R;P8P9P9P9P9P8P8P9G0P9P8P8P8P9P8P8P9G0R<P8P8P8P8P9P8P8P9G0R=P9P9P8P9P8P8P8P9G0P9P9P9P9P8P8P8P9G0P8P9P8P9P9P8P8P9G0g00;N,4;72<52=72;52<3272:3232#<R:/121115,1:553X13R1P3P6P11125,1:R1,;3P71906E611471907E6%:39335933293349334933:,80=531e%@2,80%?2553eW0o"). Qed.
Lemma concat_pieces_read_error : forall a, concat (pieces_read_error a) = msg_read_error a.
Proof.
ltac2:(KReplay.run1 (kr_t_ProgDetDriver ()) [] "h01ah11lp;1p;3p;8p;2p;6g000lj1CTg001Lj1:Tg003Bj16Tg003gj1<Tg004Lj1BTg004jj33Tg001lj80Tg005Jj22Tg002Kj1;Tg005kj35Tg006Ej2ATg006_j29Tg000Nj67Tg007=j28Tg00>[j1@Tg00?_j1?Tg009Sj3>Tg00:0R0f1R1f0R23>p=1f2R31212'2p==f4f31212,23'2'2p=4%C0R3P3%:0R4g00;o#6#<#6#B=304R5/14,12R6'1R7g00:nR8P8g00:NR9P9P9P8P8P9G0P9P9P8P8P9P8P8P9G0P8P9P9P8P9P8P8P9G0P9P8P9P8P8P8P9P9G0P9P9P9P9P9P8P9P9G0R:P9P8P9P9P8P8P8P9G0R;P8P9P8P9P9P8P8P9G0R<P8P9P9P9P9P8P8P9G0P9P9P8P9P9P8P8P9G0P:P<P;P;P8P8P8P8P9P8P8P9G0R<P;P:P9P8P8P8P9P8P8P9G0g00;N,2:5=<D4D4D4D4#;R</121115,1<553X13R1P3P6P11125,1<R1,A3P71906E711471907E7%:39335933293349334933<,80=531e%@2,80%?2553eW0o"). Qed.
