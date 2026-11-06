(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes HaltsTreeB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree Malloc Stdio Adapter Driver Harness Prog MExits.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ProgExits () := "C59OSSVerify5KrLib4Spec6MExits=mexits_bind_PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits9mexits_ifC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeB;texits_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExitsFstdio_write_loop_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits?run_calls_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExitsDread_loop_body_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness;fuzz_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits6mexitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits:mexits_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits;mexits_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits<mpost_bind_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits@target_run_exitsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3ltbK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes9Empty_set00C59OSSVerify5KrLib4Spec7Harness8free_optC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec7Harness7dt_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9dbuf_sizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExitsAfuzz_malloc_exitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExits>free_opt_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness8fuzz_oneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness=PRODUCER_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9WKSP_SIZEC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6MExits9mpost_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits5mpostC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib4Spec6MExits;mexits_munrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog;new_handlerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits@raw_malloc_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits>raw_free_exitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExitsAnew_handler_exitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExits>fuzz_one_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog8fuzz_oneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExits=fuzz_one_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_emitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExitsCprog_fuzz_one_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits?io_S_emit_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog3runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog2ioC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState9set_so_psC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4Spec6MExits?target_run_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExitsBprog_fuzz_one_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits;mexits_msysC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode;dec_set_tidC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec4Prog7startupC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions6bv_andK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List2InC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2or01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4Spec6Driver:exit_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExits=startup_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver4io_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits?io_S_diag_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExitsGtarget_alloc_init_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog:alloc_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExits>prog_run_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExitsHtarget_alloc_count_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExitsGtarget_alloc_count_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits?io_S_exit_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits@exit_model_exitsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec4Prog9prog_withC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:main_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits@main_model_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MExits?main_model_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog;alloc_countC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExits7EXITS02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver8diag_msg00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExits=prog_run_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExits8mask0_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9ProgExits8mask2_inC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC59OSSVerify5KrLib4Spec4Prog6argv_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7InitMem:entry_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState7ps_initC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib4Spec9ProgExits?prog_with_exitsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec4Prog4progC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeB6texitsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition EXITS02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HarnessX.
Context {St ptr : Type}.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable new_handler : Monad.M St Empty_set.
Variable S : list word.
Hypothesis MAL : forall n, mexits S (raw_malloc n).
Hypothesis FRE : forall p, mexits S (raw_free p).
Hypothesis NH : mexits S new_handler.

Lemma fuzz_malloc_exits : forall sz, mexits S (Harness.fuzz_malloc raw_malloc new_handler sz).
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["HarnessX"] "p'0h01ah11ei001eh21pi011ph31ri021rh42szi031oi041xp;1p;2p;3p;5p;4p;8p-1p10000p4p73110p8p1000np4p70R0g001cR1p4p710R2p8P0p,2StR3p4p300R4p8P0p1002]p4p741110R5p8P0p1003\p4p710R6p8P0p1004cp4p710R7p8P0p1005cR0p4p710R8p8p1006hp4p70R9P2p8P9P4p8P9P5p8P9P6p8P9P7p8P9P8p8P4P2p8P4g007]R2p4p710p8P4g008RR4p4p710p8p,3ptrR8p4p300R9g009OR7p4p7210p8P9g00:@R6p4p73110p8P9P4p4p7210p8P9g00;7R5p4p73110p8P9g00<2R:p4p73110p8P9P:p4p741110p8P9P1p4p73110p8P9p100<np4p7210p8p100=kp4p70R;P9p8P;p100>dp4p7210p8P;P0p4p7210p8g00?eR0j1;Tg00@Gj2:TP7j26Tg00@dj25Tg00AFj34TP2j52Tg00B:j19TP6j40TP5j43TP:j81TP1j87TP4j58Tg00B\P3p,1SR4%;8R1g00C:f0R:':P3P1P1p,:raw_mallocR5P:O1R6P0P81631R2P:158:R79431P3g00CXR;P1p,;new_handlerR9P;P2P:n011040000R2X1;R<D2n10110200021010100R=X31R>D2%98R?9431P3P4P1P1P6P>p,3MALP:O1P0P8P3P4P1P=C0P:P3P4P1P7C3X28P:O1P3P4P;P1P9P<p,2NHP;P3P4P1P2C0P:n011000000X0;G1n10110300021010100X01G1P3P4P1P?C3G7P3P4P1P3P8P5P9P:D8C0eW4o"). Qed.

Lemma free_opt_exits : forall p, mexits S (Harness.free_opt raw_free p).
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["HarnessX"] "p'0h01pi001pi011oi021qp;1p;2p;3p;4g00?eR0j15Tg009Oj24Tg00AFj31Tg00:@j40Tg00;7j43Tg00D=j42Tp,3ptrR1#5P0P1p,2StR2p,1SR3g00E7R4P0P11424f0R0p,8raw_freeR5P0O1g00EWR69124n10110000021010200C0P0p,3FREP0O1X01P0O1P2P3P4P6C3n10110100021010000P2P3P4P2P1P5P0C2C0eW0o"). Qed.

Local Hint Resolve fuzz_malloc_exits free_opt_exits : mexits.

Lemma fuzz_one_exits : forall data, mexits S (Harness.fuzz_one raw_malloc raw_free new_handler data).
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["HarnessX"] "h01ah12a0h22a1h32a2h42a3h52a4h62a5h72a6h84dBufh94datah:2dth;8producerh<4wkspp;1p;5p;4p;3p;8p;6g00F7j1?Tg00?ej1>Tg008Rj52Tg00FWj18Tg00GPj1=Tg00D=j47Tg00AFj3:Tg007]j55Tg00HKj11Tg00IPj16Tg00;7j49Tg00<2j80Tg00JRj6<Tg00:@j4;Tf2R0g00E7R1g00B\R2f1R3f0R4D5p=4f5f4P1P2f3R5P0P3P4G0p=3%?2p,2StR6p,1SR7p,3ptrR8#>R9P2P6P8p,:raw_mallocR:p,;new_handlerR;g00KLR<D2P6P9P2P6P8P:P;%83R3D2R=P6P9P2P6P8P:P;g00LKR>D2R?P6P9P2P6P8P:P;%=5R5D2R@P6P8p,8raw_freeRAP0C7RBP6P8PAf6RCC7RDg00C:RE9:62V1RF546V1RG946BV1RH946BV1RI546X89RJD5X<9RKD5X:9RLD5X;9%1<P6P7P9P2P=PL%13P6P7P9P2P?PK%1>P6P7P9P2P@PJ%15P6P7PBPI%60R0P6P7PBPHP0P6P7PBPGP0P6P7PDPF%6CP6P7P2PEC9X71E3X61E3X51E3X41E3X39G0X29G0X19G0X09G0P6P7P2P6P8P:PAP;P4E<C;eW9o"). Qed.

Lemma fuzz_one_post : forall data, mpost (fun rc => rc = 0) (Harness.fuzz_one raw_malloc raw_free new_handler data).
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["HarnessX"] "h01ah12a0h22a1h32a2h42a3h52a4h62a5h72a6h84dBufh94datah:2dth;8producerh<2rch=4wkspp;1p;3p;5p;4p;2p;7p;6g00F7j1?Tg00?ej1>Tg00MFj38Tg008Rj53Tg00FWj1=Tg00GPj1:Tg00D=j45Tg00AFj37Tg007]j52Tg00M`j26Tg00N:j59Tg00<nj70Tg00JRj6<Tg00O4j4;Tf2R0g00E7R1g00B\R2f1R3f0R4D2p=1f4P1P2f3R5P0P3P4F0p=4%?2p,2StR6p,3ptrR7#>R8P2g00C:R99824X<2R:P6P7p,:raw_mallocR;p,;new_handlerR<g00KLD3P6P8P2P6P7P;P<%=3D3R3P6P8P2P6P7P;P<g00LKD3R=P6P8P2P6P7P;P<%:5D3R5P6P7p,8raw_freeR>P0C5R0P6P7P>f6C5R?A7629V1R@516V1RA9160V1RB9160V1RC516X88RDD2X=8RED2X:8RFD2X;8P6P8P2P:P3PFP6P8P2P:P=PEP6P8P2P:P5PDP6P:P0PCP6P:P0PBP6P:P0PAP6P:P?P@P6P2P:P91629D9X71D4X61D4X51D4X41D4X38F0X28F0X18F0X08F0P6P2P:P6P7P;P>P<P4E<C;eW9o"). Qed.
End HarnessX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ProgX.
Context {rc : RunConst.runConstT}.

Lemma new_handler_exits : forall S, mexits S Prog.new_handler.
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["ProgX"] "h01Sp;1p;3p;4g00Ojj10Tg00POj15Tg00Pmj12Tg00F7j11Tg00QPj34Tg00:@j43Tg00RL#0#0#0#0#0#0#5#2#1g00S1R0f0R1g00CXR234P0P1P2g00SjC3eW0o"). Qed.

Lemma prog_fuzz_one_exits : forall S data, mexits S (Prog.fuzz_one data).
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["ProgX"] "h01Sh14datap;1p;:p;4g00Ojj10Tg00POj19Tg00Pmj12Tg00F7j11Tg00Tdj18Tg00Uej17Tg00Vdj13Tg00Wil:4Tg00Xkj15Tg00:@j46Tg00RL#0#0#0#0#0#0#9#2#1g00B\R0#1g00S1R1g00=kg00Ybg00Zag00Sjf1R2%82%72%32f0R3M:4P1P2P0%53C6eW1W0o"). Qed.

Lemma prog_fuzz_one_post : forall data, mpost (fun r => r = 0) (Prog.fuzz_one data).
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["ProgX"] "h04datah11rp;1p;6p;3p;4g00F7j14Tg00[^j63Tg00MFj30Tg00Xkj11Tg00O4j42Tg00B\R0#4g00S1R1g00=kg00Ybg00Zag00Sjf0R2E3P1P0g00C:9002X10%12C2eW0o"). Qed.

Lemma prog_run_exits : forall S c p, mexits S (Prog.run c p).
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["ProgX"] "h01Sh11ch21ph31vp;1p;2p;5p;3p;4p;=g00Ojj10Tg00POj1<Tg00Pmj14Tg00F7j12Tg00\_j2;j37Tg00Tdj1:Tg00Uej18Tg00]Wj15Tg00^^j56Tg00:@j41Tg00>dl=3Tg00_^j29Tg00RL#0#0#0#0#0#0#<#4#2g00B\R0%20g00S1R1g00=kg00Ybg00Zag00Xkg00`PR2,;1f2R3%:3%83%53P1g00aAg00b7f3R4f0R5D6P1P4g00E7A7125C1eX30f1R2P5M=3P1P3P01925C1eW2W1W0o"). Qed.

Lemma prog_run_post : forall c p, mpost (fun x => x = 0 \/ x = 2) (Prog.run c p).
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["ProgX"] "h01ch11ph21xp;1p;2p;3p;4p;9g00F7j19Tg00\_j28Tg00MFj30Tg00Ojj17Tg00c1j12Tg00cOj23Tg00_^j24Tg00O4j45Tg00cil96Tg00S1R0g00=kg00Ybg00Zag00Xkf2g00dif1R1f0R2M96p=1g00B\R3%93g00`P,80?112P0P3g00C:9032g00RL#7#29032'3X231412C5eW1W0o"). Qed.

Lemma startup_exits : forall S, mexits S Prog.startup.
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["ProgX"] "h01Sh11ap;1p;4p;3p;6p;8g00Ojj10Tg00POj19Tg00Pmj12Tg00F7j11Tg00eoj48Tg00AFj37Tg00fcj63Tg00;7j44Tg00<2j85Tg00:@j46Tg00RL#0#0#0#0#0#0#9#2#1g00S1R0f0R1g00B\R2g00E7R3P0P2g00g_R4g00hTR5C8g00EWR69703V2P0P1P2P4P5g00iOE3P0f1P3P6C4X12G5P0P1P3g00ikC6eW0o"). Qed.

Lemma mask0_in : In (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255)) EXITS02.
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["ProgX"] "h02b1h12b2h21nh31Hp;1p;2p;3g00Ojj14Tg00POj1>Tg00Pmj12Tg00jaj25Tg00kGj10Tg00c1j16Tg00klj3;Tg00MFj31Tg00lQj19Tg00m1j38Tg00mQj37Tg00mhj23Tg00nRj3:Tg00M`j2=Tg00o6j3<Tg00RLR0#4R1#4#4#4#4#4#>R2#2R3g00C:R4,52R5%00#0#0#0#0#0#0#6,529;25R031%61,52%935839730g00oPR3f0R1#2R6f1R7#2R8g00onf2R9#2?171g00B\R:f3R;/3913;731R<[1397139151:%2;?197[R=f4#2?1;9\<A:971P1n2001000000120000000W1W0W2P=^18^06^23P1P2P5P01=:41325132051:dO4b33<o"). Qed.
Lemma mask2_in : In (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) EXITS02.
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["ProgX"] "h02b1h12b2h21nh31Hp;1p;2p;3g00Ojj13Tg00POj1?Tg00Pmj14Tg00jaj25Tg00c1j17Tg00kGj11Tg00klj3;Tg00MFj30Tg00lQj1:Tg00m1j39Tg00mQj36Tg00mhj22Tg00nRj38Tg00M`j2>Tg00o6j3=Tg010Ij3<Tg00RLR0#3R1#3#3#3#3#3#?R2#4R3g00C:,52%71R1,52R4%10#1#1#1#1#1#1#7,525;2R030%:3R599349630A0340A6305g00oPR5f0R3#4R6f1R7#4R8g00onf2R9#4?073g00B\R:f3R;/2912;730R<[1297129350:%4;?097[R=f4#4?0;9\<A8973P3n2001000000120000000W1W0W2P=^18^06^25P3P2P4P01>:11224122050:dO4b33=3<o"). Qed.

Lemma prog_with_exits : forall rs argv, mexits EXITS02 (Prog.prog_with rs argv).
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["ProgX"] "h01Hh11ch24codeh31ph41nh52_Hh64argvh71bh81dh92rsh:1xp;1p;3p;5p;2p;4p;6p;:p;8p;Ap;<g00F7j1:Tg010cj38Tg007]j5>Tg011^j1VTg00Ojj1HTg00c1j1BTg00MFj31Tg00cOR0j2?Tg012_j3=Tg013Tj4<Tg014Tj3;Tg00Tdj1UTg00?ej1TTg00YbR1j1MTg00:@j40Tg00Uej1LTg00ZaR2j1GTg015Lj2ETg016TR3j1DTg017Mj1ATg00_^R4j2CTg018Oj2@Tg00O4j44Tg019Xj1ITg01:`j4KTg01;`j69Tg01<aj66Tg0000l:NTg00<2j8OTg01=?j2PTg01>7l:QTg01?2lARTg01@3l<STg00S1R5g00=kR6g00`PR7P1P2f1R8P3P4g01A3R9f0R:M:Qp=Wg00B\R;g00C:R<71:p=3P5g01AmR=g00E7R>P:C0p=5P5P=P;P:C0p=7P5P6P:P1P2P8P3P4P9P=f2R?f3R@f4RAf5f6f7f8MARp=FP5P6PAP1P2P@P3P4P9P?P8P:M<Sp=JP5P=g00CXR4P:C0p=2%:;R3#:P5P=P>P4g00ikP5P;P41W?8R2A857:R1X2;RAD>V>%V=P5P=P;P4%3:R4g00RL#H#BRB91;:'?RCX1;RDP2PAg00aARAg00b7RE5=5RFP?P5PAPEP=C<g01BhA;5F:#5]8e%U=P5P=%T6%M:C0^4;e%L=%G:#5^36e1E5=%D:#5^7;e%A=1C8:R6#7^33^1;e1@5=P5P=P;P9C0eP8M9F%72ePFP?g01CcP5P;PCX:;P6C4^33^1;e%I5P5P;P4X4;P9C4eP8DJP5P;PDP2C4eP0%38A1;8BA857?#2P:%3?P;P<%21X2;R1P5P7P=P5PAPEP=CKREP<g01DdE9P@P:E6W0P:O1A1;?BP;PBP1P5P7P=PEPBg01E`E9P@P:E6W0P:O1n200100000021000010000X0CX2;M:NX5>GO1P8:#2eW6X9;o"). Qed.

(* [comment removed for export] *)
Theorem prog_texits : forall segs rs inp en, texits nexit EXITS02 (Prog.prog segs rs inp en).
Proof.
ltac2:(KReplay.run1 (kr_t_ProgExits ()) ["ProgX"] "p'0h01ai001ah11ei011eh22enh33inph41ri021rh52rsh62s'h74segsi031pi041xp;1p;2p;3p;4p;9p;5g00F7j1BTg01F\R0j2ATg01G<R1j11Tg01H4j13Tg01Hjj1@Tg01I_j1:Tg01JWj19Tg01KRj24Tg01=?j35Tg01LJj26Tg01M@j17Tg01N8j38Tg01Nnj32Tg01OKj3?Tg01PNj4;Tg002]l9<Tg01Pnj4=Tg01Qaj5>Tg01R[R2g01SPR3g01AmR4f1R5f0R6D>p=0g01TD#Bg00B\g01UCg01V=P2P3P4g00CXR4g00S1R3'AR7#1R8g00E7R9#1R:f2R;%35#@R<f3R=#:%96'4R>35P1P7162:R?P6%79982:P4P?A2436n011040000R2n10110200020010100R9X48A?;<>P1P710:9P6g00iOP0P4P310:2P6P4P4P?P4P3P6P5C;9243n011040000,0:P5n011010000X63X14P5P6O2n2001103000120101103X07P6O1n10110100020010100X08M9<P=P;P5P6C=,0:eW2W3W5W7o"). Qed.
End ProgX.
