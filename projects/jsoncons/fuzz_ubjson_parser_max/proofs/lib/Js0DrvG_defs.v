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
HeapIface DrvKit Js0Drv_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0DrvG_defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0DrvG_defs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Drv_defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0LibStdioCall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "stdpp.bitvector.definitions."], [["1O"; "1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"]; ["3nth"; "4Z"; "5ALU_ADD"; "5BC_EQ"; "5BC_LTU"; "5M_MUL"; "6cap2_x"; "6cellC"; "6cellR"; "6kdiff"; "6keep_rd"; "6knGb0"; "6knGc0"; "6knLP"; "6knLP6"; "6knLPg"]; ["6knLPp"; "6knRDp"; "6knRa"; "6knRe0"; "6knRe_ft"; "6len_x"; "6rC0L"; "6rGa"; "6rGb"; "6rGc"; "6rGd"; "6rPa"; "6rPb"; "6rRa"; "6rRb"; "6rRe_ft"]; ["6rRe_tk"; "6rRm"; "6scR"; "6srC0L"; "6srGL"; "6srGa"; "6srGb"; "6srGc"; "6srGd"; "6srPa"; "6srPb"; "6srRD"; "6srRa"; "6srRb"; "6srRe_ft"; "6srRe_tk"]; ["6srRm"; "6summG"; "6want_x"; "7MSO"; "7knC0"; "7kn_after"; "8sc_f"; "8sc_fd"; "8sc_l"; "8sc_ret"; "8sc_s"; "8sc_sp"; "8sc_wb"; "8sc_wp"; "8stdio_call"; "8stdio_res"]; ["9EAlu"; "9ELit"; "9EMd"; "9EVar"; "9SA"; "9SCBr"; "9SE"; "9expr"; "9kentry"; "9ridx"; "9s_log"; "9s_next"; "9s_pc"; "9scripts"; "9sentry"; "9sidecond"]; ["9sr_upd"; "9sym_state"; ":kn_vars_lt"; ":sr_vars_lt"; ";BV"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition STOPS_L : list Z := (0x33c34 :: STOPS)%Z.
Definition runL (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_L scr ss [].
Definition STOPS_Q : list Z := [0x98ad0; 0x9dc38; 0x9aab4; 0x9a974; 0x3404c]%Z.
Definition runQ (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_Q scr ss [].
Definition no_sc : stdio_res := SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [].
Definition the_sc (o : option stdio_res) : stdio_res := match o with Some r => r | None => no_sc end.
Definition kn_blk2 (v : nat) : list kentry := [KRange (EVar v) 4096 (2 ^ 47); KAlign (EVar v) 16]%Z.
Definition keep_rd (kn : list kentry) : list kentry := kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.
Definition below_frame (K : kentry) : bool :=
match K with KWord (SA (EVar 0) off) _ _ => (off <? -128)%Z | _ => false end.
Definition knLP6 : list kentry := Eval vm_compute in List.filter (fun K => negb (below_frame K)) keepB.
Definition knLP : list kentry := kn_blk 48 65536 ++ knLP6.
Definition cellR : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x33c94).
Definition cellC : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x33ca8).
Definition knRD : list kentry := cellR :: knLP.
Definition srLP : list expr :=
[ELit 0; EVar 7; EAlu ALU_ADD (EVar 0) (ELit (-128)); ELit 67584; ELit 818272; EVar 11; EVar 12; EVar 13;
ELit 2; EVar 48; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
EVar 2; EVar 70; ELit 3; EVar 38; ELit 746025; EVar 48; EVar 30; EVar 31; EVar 32; EVar 33;
EVar 34; EVar 35; EVar 36; EVar 37]%Z.
Definition srRD : list expr :=
[ELit 0; ELit 712844; EAlu ALU_ADD (EVar 0) (ELit (-144)); ELit 67584; ELit 818272; EVar 11; EVar 12; EVar 13;
ELit 2; EVar 48; ELit 3; ELit 746025; EVar 71; ELit 0; ELit 0; ELit 0; ELit 0; ELit 63;
EVar 2; EVar 70; ELit 3; EVar 38; ELit 746025; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33;
EVar 34; EVar 35; EVar 36; EVar 37]%Z.
Definition rC0L := Eval vm_compute in runL scr0 (SS 0x33c00 srC0 [] knC0 70).
Definition srC0L : list expr := Eval vm_compute in s_regs (fst (fst rC0L)).
Definition knLPp : list kentry := KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLP.
Definition rPa := Eval vm_compute in runL (SCR [false; false] [] []) (SS 0x33c34 srLP [] knLPp 71).
Definition srPa : list expr := Eval vm_compute in s_regs (fst (fst rPa)).
Definition knRDp : list kentry := Eval vm_compute in kn_after rPa knLPp.
Definition rPb := Eval vm_compute in runL (SCR [false; true] [] []) (SS 0x33c34 srLP [] knLPp 71).
Definition srPb : list expr := Eval vm_compute in s_regs (fst (fst rPb)).
Definition want_x : expr := Eval vm_compute in nth 12 srPb (ELit 0).
Definition srRe0 : list expr := sr_upd srRD (ridx 10) (EVar 72).
Definition knRe0 : list kentry := KRange (EVar 72) 1 65536 :: knRD.
Definition rRe_tk := Eval vm_compute in runL scr0 (SS 0xaa10c srRe0 [] knRe0 73).
Definition srRe_tk : list expr := Eval vm_compute in s_regs (fst (fst rRe_tk)).
Definition knRe_tk : list kentry := Eval vm_compute in kn_after rRe_tk knRe0.
Definition srRm0 : list expr := Eval vm_compute in sr_after_call_j srRe_tk (map ridx callee_kept) 73.
Definition rRm := Eval vm_compute in runL scr0 (SS 0x33c2c srRm0 [] knRe_tk 105).
Definition srRm : list expr := Eval vm_compute in s_regs (fst (fst rRm)).
Definition len_x : expr := Eval vm_compute in nth 19 srRm (ELit 0).
Definition srRf0 : list expr := sr_upd srRD (ridx 10) (ELit 0).
Definition rRe_ft := Eval vm_compute in runL scr0 (SS 0xaa10c srRf0 [] knRD 73).
Definition srRe_ft : list expr := Eval vm_compute in s_regs (fst (fst rRe_ft)).
Definition knRe_ft : list kentry := Eval vm_compute in kn_after rRe_ft knRD.
Definition srGL : list expr := Eval vm_compute in sr_upd srRe_ft (ridx 10) (ELit 0).
Definition knGbase : list kentry := cellC :: knLP.
Definition knG (lo hi : Z) : list kentry := KRange (EVar 70) lo hi :: knGbase.
Definition knLPg : list kentry := KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLP.
Definition rGa := Eval vm_compute in runL (SCR [true] [] []) (SS 0x33c34 srLP [] knLPg 71).
Definition srGa : list expr := Eval vm_compute in s_regs (fst (fst rGa)).
Definition knGa : list kentry := Eval vm_compute in kn_after rGa knLPg.
Definition cap2_x : expr := Eval vm_compute in nth 10 srGa (ELit 0).
Definition srGb0 : list expr := Eval vm_compute in sr_after_call_j srGa (map ridx c_kept) 71.
Definition knGb0 : list kentry := Eval vm_compute in kn_blk2 81 ++ keep_alloc MSO [(48%nat, 65536%Z)] [] knGa.
Definition rGb := Eval vm_compute in runL scr0 (SS 0x33c54 srGb0 [] knGb0 103).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
Definition srGc0 : list expr := Eval vm_compute in sr_after_call_j srGb (map ridx callee_kept) 103.
Definition knGc0 : list kentry := Eval vm_compute in keep_rd knGb0.
Definition rGc := Eval vm_compute in runL scr0 (SS 0x33c70 srGc0 [] knGc0 135).
Definition srGc : list expr := Eval vm_compute in s_regs (fst (fst rGc)).
Definition srGd0 : list expr := Eval vm_compute in sr_after_call_j srGc (map ridx c_kept) 135.
Definition knGd0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knGc0.
Definition rGd := Eval vm_compute in runL scr0 (SS 0x33c78 srGd0 [] knGd0 167).
Definition srGd : list expr := Eval vm_compute in s_regs (fst (fst rGd)).
Definition knGd : list kentry := Eval vm_compute in kn_after rGd knGd0.
Definition knLPr : list kentry := KRange (EVar 70) 67108864 67108864 :: KRange (EVar 38) 67108864 67108864 :: knLP.
Definition scr_refuse : scripts := SCR [false; false; false; true; false] [] [].
Definition rRa := Eval vm_compute in runQ scr_refuse (SS 0x33c34 srLP [] knLPr 71).
Definition srRa : list expr := Eval vm_compute in s_regs (fst (fst rRa)).
Definition knRa : list kentry := Eval vm_compute in kn_after rRa knLPr.
Definition scR : stdio_res := Eval vm_compute in the_sc (stdio_call 71 srRa knRa).
Definition srRb0 : list expr := Eval vm_compute in sc_sr scR.
Definition knRb0 : list kentry := Eval vm_compute in sc_kn scR.
Definition rRb := Eval vm_compute in runQ scr0 (SS (sc_ret scR) srRb0 [] knRb0 103).
Definition srRb : list expr := Eval vm_compute in s_regs (fst (fst rRb)).
Definition knRb : list kentry := Eval vm_compute in kn_after rRb knRb0.
Definition summG (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
Definition kdiff (a b : list kentry) := List.filter (fun K => negb (existsb (kentry_eqb K) b)) a.
Lemma loop_itinerary_ok : ltac2:(TCodec.tc2 tcn__Js0DrvG_defs "_D'>'?';'A'6'RO%211%5241'7%7221'RN%711%:231&R1&Q6%211(:+eXX8(8%11>%44A>31uR6%64?>21(3(RF(RD(RC(0%211-T8%5221u8(RA+V_TD%211%;3541%B1J%>3K21%F4MK@1%Q63KH1'RH%Q511&R5&R4%22N1&H%G3613%Q>3631&I&M%2217%Q11;%QC3;21'2&S2u6&N%3221(<%QJ3621'RG%QK211%QL212%QM213%QN214%QO215%R0216&@uE&QCz%Q711%54<431u9%74>153%QK4??31uC%:4A186%QN4AB31u<%=4D1;9%R14CE31u;%@4G1><%R44EH31u:%C4J1A?%R74GK31uA%F4M1DB%R:4IN31+RPP0%QL11uQ@%R411%R?4Q3Q331%R@4Q3Q41I%RA4Q3Q515+fha9%R311%RD4Q5Q831+3%R611%RG4Q7Q;31+QO%R911%RJ4Q9Q>31%S:3Q9A1&Q;%S011(RE(4(D&R2%44321F(C%RJ1ROuQ6%RL11%948431%S13SC1S5%S23SD71%S:4SGSDS91uR7%S<4SESD21%S=4SDSB1RH%SM3SBA1&Q<%SC11%C4R7A@Q5%S;3SM1:%SC4T0SMSB1%SD4SMSL19%SE4SLSJ1S0%T53SJ61&Q0%RN291&Q1%T93S121%SD3S3RN4%T;3S331%T91RA&QJ&S0&QI&RI(S4y5+<(=%43321%611%9381Q7%TH3<;1&QK%<314QO+G%;3:18%=11%@341R1%TO3C@1(R@(B(RB(E-1%T611%4331QC%736QB1%U83S=QH1&Q@%TN11+eT[0%TM4U:U71TJuR9%TO4U8U721%U04U7U51T<%U@3U561&Q3%T9291%UC3T;12&J%114%UF3T>15&QO%SF4SMS41SB%SG4SNS82SC%U;4SOSO21%SI4T0S=4SE%U=4T0T121u1%SL4T317SH%U@4T2T431u2%SO4T61:SK%UC4T4T731%Q33Q2S6R@%UE4T9T91S2uR8%U=11%UH4T;T<31+V_Q<%U:11%UK4T=T?31-T0%U=11%Q=3Q<UB1%UO4T@TC41%V?3T@=1&QA%V511+V_QD%V44VAV>1V1uS9%V64V?V>21%V74V>V<1UC%VG3V<61&Q5%QI3QHS6C%VJ3TO21&R0%TJ4U1TD1TFuG%TL4U313TH%V@4U4U431%TN4U5TM5TJ%VB4U5U621uB%U14U818TM%VE4U7U931%U34U:Q5:TO%VG4U8U;21%VH4U<U<T:T:%VI4U<U=1SC%V@1Q9%VK4U=U?21%VL4U=U@1N%W<3U=61&Q?%W211%W04W9W8VLR2+V_U8%VB11%VK3VEVD1%VM3W:1V@%W54W<W:51%WE3W:71&Q4&G%W23VA1V8%WI3VA31&QN%UI4V0U71UE%UJ4V1U52UF%W>4V2V221+QI%W011%WA4V5V5TK1%X13V541&S3&QD%22T:1%X53VA1V<&Q7%WK11+cZeD%TL4V@TGTFTD%WD3X61WH%WL4X9X631%WM4X6X51TB%WN4X5X31W:%X>3X371&O%W72:1%XA3W912&QE%VA4VHUO1V=&F%XE3VJ21%VD4VKVC4V@%XG3VL13+2%WJ11%SH3SG1U7%XK3W071%VJ4W1RO:VF+V_RD%WO11%XO3W431%VN4W5S0>VJ&R3%X311%T33T2X81%Y43W941&Q8%XJ11uS7%XI4Y2Y1SL1%XJ4Y1XO1X6%Y:3XO41&K%X3271%Y=3X512&QF%W=4WDVK1W9%W>4WEVO2W:%Y24WFWF21%W@4WGW44W<%Y44WGWH21%WB4WISG6W>%Y64WHWJ21uRA%XN11%Y94WMWM1VK%Y:4WMWN1V6+V_S@%XL11%Y=4WOX131%YM3WO81&L%X@2D1%Z03XH1X>&Q9%YF11+cZ[D%YE4Z2YO1YBuT7%YG4Z0YO21%YH4YOYM1Y4%Z83YM61%Y028;%Z:3Y21<&QG%X:4XAWH1X6%Z=3XB1W@%X<4XCTA3X8+V_SH%YA11%ZA3XF31%X@4XGTB7X<%ZC3XH1Q@&Q:%Z911uU7%Z84ZAZ@Z41%Z94Z@Z>1YD%ZI3Z>41&QH%XI4Y0X71XE%XJ4Y1X;2XF%Z>4Y2Y221%XL4Y3X@4XH%Z@4Y3Y421%XN4Y5X96XJ%ZB4Y4Y621%Y04Y7XJ8XL%ZD4Y5Y821%Y24Y9Y1:XN%ZF4Y6Y:21%Y44Y;XK<Y0%ZH4Y7Y<21%ZI4Y=Y=X3X6%ZJ4Y=Y>1X>%ZK4Y=Y?1X2%ZL4Y=Y@1QD%ZM4Y=YA1RH%ZN4Y=YB1WJ%[>3Y=71%[>2[=[8&RL&5'S1%[B21[>'RM&Q=%53321%635[B1%811&RK%113%[<4[I[D31+cgQH%[>4[K[F1X3%[N3?31'9'R?%211&R>&QL&Q2%33X;21(1&QB%2281%\93841%\92\8\8%\:21\9%\;21ZA%\<21ZB&R9%118&R6%11:%\34\@\@31&R7%11=%\64;\C31&R:%11@%\94=ZM31&R8%11C%\<4?[031+cjW4+fgo0%\?4\L\L21%\@4E\M1T7%\A4E[51ZJ%\B4E[61ZK%]23E71&R<%11M&R=%11O%\H4[<[<31&R;%11Q2%\K4[>[?31-a@%\=11%X=3X<\B1-`:%\@11%X@3X?\E1%]24[F[F41-b0%\D11%XD3XC\I1%]64[I[J41%]F3[I<1&Q>%]<11+cRf@%];4]H]E1]8%]<4]E]D1TD&RJ%R<3R:R96%R=3R<]I1%311%]A4]H]F51%^13]F91&QM%\14\8[?1[M%^43\91U;%^6241%^72@1%^82Q51%^92QO1%^:2R;1%^;2RL1%^<2SB1%^=2SI1%^>2SL1%^?2T11%^@2T51%^A2T81%^B2TA1%^C2TE1%^D2U61%^E2U:1%^F2UA1%^G2UG1%^H2UL1%^I2V11%^J2V41%^K2V91%^L2V=1%^M2VG1%^N2VL1%^O2W51%_02W:1%_12WD1%_22X71%_32X;1%_42XD1%_52Y>1%_62YB1%_72YF1%_82YO1%_92Z91%_:2ZA1%_;2ZO1%_<2[21%_=2[71%_>2[@1%_?2\41%_@2]E1%_A2]M1%_B2^31%_C2^<1").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX_1.
