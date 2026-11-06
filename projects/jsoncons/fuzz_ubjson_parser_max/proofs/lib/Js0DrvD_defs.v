(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Js0MainEntry Js0LibStdioCall
HeapIface DrvKit Js0Drv_defs Js0DrvG_defs Js0DrvC_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0DrvD_defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvD_defs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0LibStdioCall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2I"; "2and"; "2eq"]; ["3map"; "4Z"; "5BC_NE"; "6ksubl_b"; "7dec_x"; "7flagsK"; "7keep_pf"; "7knLH1"; "7knLH2"; "7knLc2"; "7knQ"; "7knR"; "7knR2"; "7knTc"; "7knTe"; "7knU0"]; ["7knV0"; "7knX0"; "7rLB1"; "7rLB2"; "7rLc1"; "7rLc2"; "7rP"; "7rQ"; "7rR"; "7rS_ft"; "7rS_tk"; "7rT00"; "7rT01"; "7rT10"; "7rT11"; "7rU"]; ["7rV"; "7rX"; "7rY"; "7rZ"; "7relay_ok_b"; "7scP"; "7sr00"; "7sr01"; "7sr10"; "7srLB"; "7srP0"; "7srQ"; "7srR"; "7srS_tk"; "7srTm0"; "7srV"]; ["7wposK"; "8keep_alloc"; "8kn_after"; "9sc_f"; "9sc_fd"; "9sc_l"; "9sc_ret"; "9sc_s"; "9sc_wb"; "9sc_wp"; "9stdio_call"; "9stdio_res"; ":callee_saved"; ";sr_after_call_j"; "<ELit"; "<EVar"]; ["<KRange"; "<SA"; "<SCBr"; "<SE"; "<expr"; "<kentry"; "<ridx"; "<s_log"; "<s_pc"; "<s_regs"; "<scripts"; "<sentry"; "<sidecond"; "<sr_upd"; "<sym_state"; "=kn_vars_lt"]; ["=sr_vars_lt"; ">BV"; ">bv"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition STOPS_T : list Z := (0x33f34 :: 0x33d20 :: STOPS)%Z.
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_T scr ss [].
Definition STOPS_P : list Z := [0x98ad0; 0x9dc38; 0x9aab4; 0x9a974; 0x3404c]%Z.
Definition STOPS_R : list Z := (0x33f58 :: STOPS_P)%Z.
Definition runP (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_P scr ss [].
Definition runR (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_R scr ss [].
Definition knTc (clo chi plo phi : Z) : list kentry := KRange (EVar 73) clo chi :: KRange (EVar 79) plo phi :: knT0.
Definition rT00 := Eval vm_compute in runT scr0 (SS 0x33e7c srT0 [] (knTc 0 0 0 0) 81).
Definition rT01 := Eval vm_compute in runT scr0 (SS 0x33e7c srT0 [] (knTc 0 0 1 67108857) 81).
Definition rT10 := Eval vm_compute in runT scr0 (SS 0x33e7c srT0 [] (knTc 1 32767 0 0) 81).
Definition rT11 := Eval vm_compute in runT scr0 (SS 0x33e7c srT0 [] (knTc 1 32767 1 67108857) 81).
Definition sr00 : list expr := Eval vm_compute in s_regs (fst (fst rT00)).
Definition sr01 : list expr := Eval vm_compute in s_regs (fst (fst rT01)).
Definition sr10 : list expr := Eval vm_compute in s_regs (fst (fst rT10)).
Definition sr11 : list expr := Eval vm_compute in s_regs (fst (fst rT11)).
Definition calls_x : expr := Eval vm_compute in nth 21 sr11 (ELit 0).
Definition is_case_entry (K : kentry) : bool :=
existsb (kentry_eqb K) [KRange (EVar 73) 0 0; KRange (EVar 73) 1 32767; KRange (EVar 79) 0 0; KRange (EVar 79) 1 67108857].
Definition uncase (kn : list kentry) : list kentry := List.filter (fun K => negb (is_case_entry K)) kn.
Definition knTe : list kentry := Eval vm_compute in uncase (kn_after rT11 (knTc 1 32767 1 67108857)).
Definition knTk : list kentry := Eval vm_compute in keep_alloc (-208) [(48%nat, 65536%Z)] [] knTe.
Definition srTm0 : list expr := Eval vm_compute in sr_upd sr11 (ridx 21) (EVar 81).
Definition srU0 : list expr := Eval vm_compute in sr_after_call_j srTm0 (map ridx c_kept) 82.
Definition knU0 : list kentry := Eval vm_compute in kn_blk2 92 ++ knTk.
Definition rU := Eval vm_compute in runT scr0 (SS 0x33ee0 srU0 [] knU0 114).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
Definition srV0 : list expr := Eval vm_compute in sr_after_call_j srU (map ridx callee_kept) 114.
Definition knV0 : list kentry := Eval vm_compute in keep_rd knU0.
Definition rV := Eval vm_compute in runT scr0 (SS 0x33ef4 srV0 [] knV0 146).
Definition srV : list expr := Eval vm_compute in s_regs (fst (fst rV)).
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition srLH : list expr :=
[ELit 0; EVar 85; spx (-208); ELit 67584; ELit 818272; EVar 86; EVar 87; EVar 88;
EVar 79; EVar 82; EVar 89; EVar 90; EVar 91; EVar 92; EVar 93; EVar 94; EVar 95; EVar 96;
EVar 83; EVar 84; ELit 811568; EVar 81; ELit 0; ELit 18446744073709551614; EVar 30; EVar 31; EVar 32; EVar 33;
EVar 97; EVar 98; EVar 99; EVar 100].
Definition knLH1 : list kentry := Eval vm_compute in keep_rd knTk.
Definition shared_pos : list nat := [2; 3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition relay_ok_b (sr : list expr) : bool :=
forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLH (ELit 0)) && expr_vars_lt 82 (nth i sr (ELit 0))) shared_pos.
Definition IMG_LIB : list (Z * Z) := [(0x10000, 0xc6250); (0xc73d8, 0xc7b88); (0xc7b90, 0xc7bbc); (0xc7bc0, 0xe7ca8); (0xe7ec8, 0xe8068); (0xe8410, 0xe9000)]%Z.
Definition keep_lib (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
kn_keep 0 so 65536 bls vbnd [3%nat; 4%nat] IMG_LIB IMG_RW kn.
Definition rLB1 := Eval vm_compute in runT scr0 (SS 0x33f34 srLH [] knLH1 102).
Definition srLB : list expr := Eval vm_compute in s_regs (fst (fst rLB1)).
Definition knLB1 : list kentry := Eval vm_compute in kn_after rLB1 knLH1.
Definition srLr0 : list expr := Eval vm_compute in sr_upd (sr_after_call_j srLB (map ridx c_kept) 102) (ridx 10) (ELit 0).
Definition knLr1 : list kentry := Eval vm_compute in keep_lib (-208) [(48%nat, 65536%Z)] [] knLB1.
Definition rLc1 := Eval vm_compute in runT scr0 (SS 0x33f48 srLr0 [] knLr1 134).
Definition srP0 : list expr := Eval vm_compute in s_regs (fst (fst rLc1)).
Definition knLc1 : list kentry := Eval vm_compute in kn_after rLc1 knLr1.
Definition rP := Eval vm_compute in runP scr0 (SS 0x34004 srP0 [] knLc1 134).
Definition srP : list expr := Eval vm_compute in s_regs (fst (fst rP)).
Definition knP : list kentry := Eval vm_compute in kn_after rP knLc1.
Definition srQ0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) (ELit 18446744073709551591).
Definition rQ := Eval vm_compute in runP scr0 (SS 0x9e660 srQ0 [] knP 134).
Definition srQ : list expr := Eval vm_compute in s_regs (fst (fst rQ)).
Definition knQ : list kentry := Eval vm_compute in kn_after rQ knP.
Definition scP : stdio_res := Eval vm_compute in the_sc (stdio_call 134 srQ knQ).
Definition srR0 : list expr := Eval vm_compute in sc_sr scP.
Definition knR0 : list kentry := Eval vm_compute in sc_kn scP.
Definition rR := Eval vm_compute in runR scr0 (SS (sc_ret scP) srR0 [] knR0 166).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition knR : list kentry := Eval vm_compute in kn_after rR knR0.
Definition IMG_PF : list (Z * Z) := [(0x10000, 0xb60d0); (0xb60d4, 0xb60f8); (0xb6100, 0xc6250); (0xc7b90, 0xc7bbc); (0xc7bc0, 0xe8068); (0xe8410, 0xe8450); (0xe8850, 0xe9000)]%Z.
Definition keep_pf (kn : list kentry) : list kentry := kn_keep 0 (-208) 1056 [(48%nat, 65536%Z)] [] [3%nat; 4%nat] IMG_PF IMG_RW kn.
Definition wposK (e : expr) : kentry := KWord (SA (ELit 0) 0xb60f8) 8 e.
Definition flagsK : kentry := KWord (SA (ELit 0) 0xb60d0) 4 (ELit 5).
Definition knR2 : list kentry := Eval vm_compute in keep_pf (keep_lib (-208) [(48%nat, 65536%Z)] [] knR).
Definition knLH2 : list kentry := wposK (EVar 101) :: KRange (EVar 101) 0xe8450 0xe8456 :: flagsK :: knR2.
Definition rLB2 := Eval vm_compute in runT scr0 (SS 0x33f34 srLH [] knLH2 102).
Definition knLB2 : list kentry := Eval vm_compute in kn_after rLB2 knLH2.
Definition knLr2 : list kentry := Eval vm_compute in keep_lib (-208) [(48%nat, 65536%Z)] [] knLB2.
Definition rLc2 := Eval vm_compute in runT scr0 (SS 0x33f48 srLr0 [] knLr2 134).
Definition knLc2 : list kentry := Eval vm_compute in kn_after rLc2 knLr2.
Definition srS : list expr := sr_upd srLH (ridx 19) (ELit 0).
Definition rS_tk := Eval vm_compute in runT (SCR [true] [] []) (SS 0x33f58 srS [] knLH2 102).
Definition rS_ft := Eval vm_compute in runT (SCR [false] [] []) (SS 0x33f58 srS [] knLH2 102).
Definition srS_tk : list expr := Eval vm_compute in s_regs (fst (fst rS_tk)).
Definition srS_ft : list expr := Eval vm_compute in s_regs (fst (fst rS_ft)).
Definition dec_x : expr := EAluw ALU_ADD (EVar 81) (ELit (-1)).
Definition srX0 : list expr := Eval vm_compute in sr_after_call_j srS_ft (map ridx c_kept) 102.
Definition knX0 : list kentry := Eval vm_compute in keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2.
Definition rX := Eval vm_compute in runT scr0 (SS 0x33f74 srX0 [] knX0 134).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).
Definition srY0 : list expr :=
Eval vm_compute in sr_upd (sr_upd (sr_upd (sr_upd srX (ridx 8) (ELit 0)) (ridx 10) (ELit 0)) (ridx 1) (EVar 134)) (ridx 11) (EVar 135).
Definition rY := Eval vm_compute in runT scr0 (SS 0x33da0 srY0 [] knX0 136).
Definition srY : list expr := Eval vm_compute in s_regs (fst (fst rY)).
Definition srZ0 : list expr := Eval vm_compute in sr_after_call_j srY (map ridx c_kept) 136.
Definition knZ0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knX0.
Definition rZ := Eval vm_compute in runT scr0 (SS 0x33da8 srZ0 [] knZ0 168).
Definition srZ : list expr := Eval vm_compute in s_regs (fst (fst rZ)).
Definition knZ : list kentry := Eval vm_compute in kn_after rZ knZ0.
Lemma tgt_itinerary_ok : ltac2:(TCodec.tc2 tcn__Js0DrvD_defs "^C'>'?':'A'5'RL%211%5241(9&RH&4'RN%:216'RJ&Q;%53321%635:1%811&;%138=4%<4A>31+V_iD(7%11B%@4EB31%H3B51&Q=%A3?>1%B3AF1%D11%<3CH3%G4LI21%O3I18&Q<%H3FE1%I3HM1%K11%C3JO3%N4Q3Q021+cZeD%Q04Q5Q21A%Q83Q231&Q>%Q13ON1%Q23Q1Q61%Q411%L3Q3Q83%Q74Q<Q921%Q?3Q918'1&C&R2&Mz%241111%42Q91&N%7221(<%QJ3:21+1+QooooI%:49921%<2N1%>218%R03@17+ooO%?471>>%A2Q:1%C21=%R53E1<%C4;5;:%E2N1%G21A%R93I1@'RD%R811&RM&QG&RF(S1y5+E(=%43321%611(R?uRA%211%<3;41&QN%RJ3?21&G%Q;2Q51%RM3Q=1Q4&Q0%Q>214%S03Q@1Q7'RE%RO11&Q@%QB216%S53317&Q?&O%QF221%S93712&QD&QF%Q031HE%311%S>3QN1QE&QH%Q431LI%711%SB3R21QI&QO%:11%SE3R51QL&QL%=11%SH3R81QO&QM%Q>31Q6Q3%A11%SL3R<1R3&ROuRB%221Q4%T03R@1R7&S0%124Q9%T33RC1R:'RK%T211%T52T01%SN3SLSKQ1%SO3SNT31%T111%SI3T0T53%T44T9T621&RG%115%T74T8931+eT[0%T94T>T;1SJ%SL1=%T;4T<=21%TC3=51%T;3T9T8QA%T<3T;T@1%T>11%T63T=TB3%TA4TFTC21%=14%TC4TDE21%TD4TEFT4:%TL3F21&Q2%TE3TCTB1%TF3TETJ1%TH11%T@3TGTL3%TK4U0TM21+V`R<%TM4U2TO1T>%U53TO31%U52U0RK&Q3%TO3TMTL1%U03TOU41%U211%TJ3U1U63%U54U:U721&RI%115%U84U9S431&QI%U:4U;S6=1%UB3<31&Q4%U;3U9U81%U<3U;U@1%U>11%U63U=UB3%UA4UFUC21+V`P4%UC4UHUE1U4%UK3UE31&Q5%UD3UBUA1%UE3UDUI1%UG11%U?3UFUK3%UJ4UOUL21%E14%UL4UMSH21&QJ%UN4UOSJ;1%V63Q031%QK1Q8(2(RC(RA(R>%11TH+hhaD%4221u1%51TE%83321%:3R>1R1%VC3R><1%R81Q;%VE3R@13%R:1Q1%>398;%@3RD1R7%VI3RD31%R>1L%VK3RF13&H&I%U=221%VO3U?1U6%U?234%W13UA1U8&K&R0+mQR@%J11%311&E&L%Q13T821%Q23T941%UJ291%W<3UL1UC&F%11B(R@uS5%TL11+mQRF%432?1%Q<3TC1<%WE3TC71uS6%SJ21K%WH3V81UO%SL2U3A%WJ3V:1V1&R=&@'S2%11U>'6&R<%5432UC1uT6%83QO21%TJ11%X53VE1V<&Q1%VF2Q;1%X83VH1V?&R1-V@%X:2<X9uQ@+RPP0%X74?X<21%WJ14%R83521%84712QE%XB3U@1<&Q6%X;3X9X81%X<3X;X@1%X>11%X63X=XB3%XA4XFXC21+cibL%XC4XHXE1X4%XK3XE31&Q7%XD3XBXA1%XE3XDXI1%XG11%X?3XFXK3%XJ4XOXL21+cgQH%XL4Y1XN1X=%Y43XN31'8'R;%211&R:&QK&J%33Q921(0&QE%2281%Y?3841%Y?2Y>Y>%Y@21Y?%YA21W8%YB21W9%YC21W:%YD21W;&R6%11:&R3%11<%YC4YHYH31&R4%11?%YF4=YK31&R8%11B%YI4?WF31&R9%11E%YL4AWI31&R7%11H%YO4CWL31&R5%11K%Z24EWO31+cid0+fhV@%Z54Z:Z:21%Z64MZ;1XB%Z74MX41S9+mQRA%T511%Z:4OX731+RSW3%T811%Z=4Q1X:31%Z>4Q1X;1T5%ZF3Q1=1&Q8%Z?3Z=Z<1%Z@3Z?ZD1%ZB11%Z:3ZAZF3%ZE4ZJZG21+V_jH%ZG4ZLZI1Z8%ZO3ZI31&Q:%ZH3ZFZE1%ZI3ZHZM1%ZK11%ZC3ZJZO3%ZN4[3[021%VJ14%[04[1W221(RB(B&D%34YB21TO%U43[81ZF%[64[;[8ZI1%[74[8W91VM%[?3W981&Q9%[83[6[51%[93[8[=1%[;11%[33[:[?3%[>4[C[@21%W:14%[@4[AWB21+cZ[D(3%B41A@U>%UC3[G1[5%[E4[J[G41%[F4[GWH1W<%[N3WH71&QA%[G3[E[D1%[H3[G[L1%[J11%[B3[I[N3%[M4\2[O21%WI14%[O4\0X121+V_Y0%\14\6\31[B%\24\3X41WH%\:3X441&QB%\33\1\01%\43\3\81%\611%[N3\5\:3%\94\>\;21%X514%\;4\<X=21%\<4\A\>K[M%\=4\>X?1X3%\E3X?31&QC%\>3\<\;1%\?3\>\C1%\A11%\93\@\E3%\D4\I\F21%X@14%\F4\GXH21+cRf@%\H4\M\J1\9%\I4\JXK1X?%]13XK41%]32=1%]42I1%]52Q61%]62QF1%]72R71%]82RA1%]92SI1%]:2T51%];2T?1%]<2TI1%]=2U41%]>2U81%]?2UD1%]@2UG1%]A2UK1%]B2V51%]C2VA1%]D2VD1%]E2VI1%]F2VL1%]G2W11%]H2W41%]I2WB1%]J2WN1%]K2X81%]L2XF1%]M2Y01%]N2Y:1%]O2YK1%^02YO1%^12Z41%^22Z91%^32Z=1%^42ZA1%^52ZF1%^62ZL1%^72[11%^82[71%^92[;1%^:2[?1%^;2\11%^<2\61%^=2\<1%^>2\C1%^?2\O1%^@2]71%^A2]A1%^B2]I1").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX_1.
