(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_PortLib () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List2InI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00C47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib6Common8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01".
Import ListNotations.
Open Scope bv_scope.

Lemma in_regs_dec : forall (r : reg) (l : list reg),
  existsb (fun x => bv_eqb x r) l = true -> In r l.
Proof.
ltac2:(KReplay.run1 (kr_t_PortLib ()) [] "p'0h01xi001xh11Hh21nh31Eh42Hxh51lh61Ah72b1h82b2h91fh:1mh;2H0h<1rp;1p;3p;2p;7g0000j1BTg000Uj1ATg001:j1=Tg001Xj16Tg002;j1;Tg002[j32Tg003HR0j39Tg003dj31Tg004;R1j23Tg004VR2j28Tg0050j3<Tg005Sj2:Tg0060j2@Tg006Pj24Tg007:j35Tg007Tj3>Tg0088j7?Tg008VR3f0R4g009635p=0g009VR5f1R6;54p=7g00:4#B#A#=R7#6R8%;8f2R99274X08=984#0P0p4p710R0P3\4R3%;6R:P1A9964#0f3R;f4R<?149P;P4O1#0'3X0;'8[R=A1;46P9P4O1#0'3X09,89A9;96#0R>[f5R??14;P<P4O1#0'3X0<,8<\>A<964P6n2001000000120000000W5W9W6P=^5:^93^60P4P8A274<R0X08P9P6O4A184;%00'3X08,88P2P8A184<A274?#0'3X08A18?<P4f6R29184f7R09274#0'3P1A1860f8R09276#0f9R3=180P4A18;3f;927<#0P11:64#01796[R:17641:96#0R=[17;9\=1@64P6n2001000000120000000X:5X25P:^:5^25P41472R2f=,47R5P6O31725g00:YR5%64R2%66R:P1%69?56414;914;6'7R1[14961494'7%6;?596[R=%6<?5;9\1A>964P4n2001000000120000000W8W7W2P=^8:^72^25P4P7P0f?R7P6O4A5807P8f@R0A1840fBfA518]4X08A1807P4W4P3P4P?F?b3b1b3b1W3W4P6P4O2n2001000000121000000W1X08P6P4O2n2001000000121100000b1b;W1W5W<o"). Qed.
Lemma not_in_regs_dec : forall (r : reg) (l : list reg),
  forallb (fun x => negb (bv_eqb x r)) l = true -> ~ In r l.
Proof.
ltac2:(KReplay.run1 (kr_t_PortLib ()) [] "p'0h01xh12H'h21Hh32H0h43Hinh51bi001bh61eh71lh81rp;1p;3p;6p;2g0000j1@Tg000Uj1?Tg001:j17Tg001Xj16Tg002;j1>Tg002[j32Tg00;7j11Tg00;Uj33Tg003dj34Tg00<1j38Tg00<Tj69Tg00<oj2:Tg00=oj65Tg00>Kj2=Tg00>jj1<Tg007:j3;Tg008VR0f0R1g0096R23;p=0g00:4#@#?#7R3#6R4%>4f2R59231#1X04=341#0f1R69445R7f4R89231#1X04R9=345#0A4418f79231#1X04P6O1#0[^04[f3R:9441f69231#1X04P6O1#0[^04f59231#1X04=34:#0[A8495P6P:P1E9P9P:O1#0P0A2388%11#0X50P1P21:38E5%12R8#0P0P8P0p-0P1g00?CR8g00?`n0110000020000X60g00@<P2P1E5P81=81b3b1b1W4%<7eW2W7W8o"). Qed.
Ltac RefMemcpyLib.kept_reg ::= first [ apply in_regs_dec; reflexivity | cbv [callee_kept In]; intuition congruence ].
Ltac RefMemcpyLib.not_kept ::= first [ apply not_in_regs_dec; reflexivity | cbv; intuition discriminate ].
Ltac kept_reg := RefMemcpyLib.kept_reg.
Ltac not_kept := RefMemcpyLib.not_kept.
