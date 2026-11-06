(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes HaltsTreeB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree Malloc Stdio Adapter Driver.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MExits () := "c59OSSVerify5KrLib4Spec6MExits5mpostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits6mexitsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits3okPC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib3Lib:HaltsTreeB6texitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeB;texits_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeB7tleavesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeB<tleaves_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeB<tleaves_trueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeB<tleaves_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeB=texits_bind_PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeBAtexits_vis_noexitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib4Spec6MExits;mexits_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits:mexits_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits;mexits_munrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01c59OSSVerify5KrLib4Spec6MExits:mpost_bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits:mpost_trueC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits9mpost_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits:mpost_munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState:set_brk_psC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode7dec_brkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init9Datatypes4negbK59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps>dec_mmap_fixedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps9neg_errnoC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib3Lib6Decode=dec_mmap_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_mmapC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode:dec_munmapC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps?dec_mprotect_rwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits;mexits_msysC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits:mexits_updC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits:mexits_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps7ev_stepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits9mexits_ifC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib3Lib6Decode8mmap_ans00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode9range_ans00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib3Lib6Decode8dec_brk0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode7brk_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps;MAP_FIXED_ZC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc8ProgDeps9fixed_ans00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree9stree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps6membedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits=ev_step_exitsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7cmallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5set_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps9fresh_offC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits<membed_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5cfreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio@stdio_write_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6upd_soC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapK59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9iov_totalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode:dec_writevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;iov_advanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib4Spec6MExitsFstdio_write_loop_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdio_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9WRITE_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio5rd_soC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9so_lbf_nlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8so_firstC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5Stdio9stdout_st01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExitsAstdio_write_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBstdout_stdio_writeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib4Spec6MExits;rd_so_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9so_activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExitsHstdout_stdio_write_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_writefnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib3Lib6Decode4sret00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:TIOCGWINSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9dec_ioctlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_towriteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec5Stdio=after_last_nlC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes3appc59OSSVerify5KrLib4Spec6MExitsDstdout_writefn_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_fwritexC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=STDOUT_BUFSIZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExitsDstdout_towrite_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:out_piecesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExitsDstdout_fwritex_exitsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib4Spec6MExits@out_pieces_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_vprintfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioAstdout_exit_flushC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=stderr_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio?INTERNAL_BUFSIZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExitsCstderr_pieces_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stderr_fprintfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=stderr_fwriteC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver7IOStyle00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver9rd_result00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits<mexits_mloopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits<mpost_bind_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBpieces_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioApieces_read_errorC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatc59OSSVerify5KrLib4Spec6MExitsDstderr_fprintf_exitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExitsCstderr_fwrite_exitsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver8diag_msg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:pieces_oomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>pieces_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio@pieces_short_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBpieces_cfg_overrunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_pct_dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExitsDstdout_vprintf_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_emitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits<s_diag_exitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExits<s_emit_exitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExitsGstdout_exit_flush_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Adapter9run_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Adapter:target_runC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib4Spec6MExits?run_calls_exitsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00c59OSSVerify5KrLib4Spec6MExits>run_calls_postC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2or02C59OSSVerify5KrLib4Spec6Driver7io_diagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver>read_loop_bodyC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver5rd_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:rd_contentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6rd_capC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Driver6rd_bufC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver5rd_st01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver9rd_result01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum02C47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat3eqbK59OSSVerify5KrLib4Spec6Driver9rd_result02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver<u8s_of_bytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3sum01C59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg04C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode8read_ans00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MExitsDread_loop_body_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver8read_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9dec_closeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8dec_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9READ_FUELC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib5Lists7ListDef3nthK59OSSVerify5KrLib4Spec6Driver8diag_msg01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver4le16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver4le32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim4znthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitc59OSSVerify5KrLib4Spec6MExits>read_all_exitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver:main_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7HDR_MINC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Driver8diag_msg07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9COUNT_MAXC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_andC46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Driver7io_exitC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Driver:exit_modelC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes9Empty_set00C59OSSVerify5KrLib3Lib6Decode8dec_exitC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MExits.
Context {St : Type}.

Definition mexits (S : list word) {A} (m : Monad.M St A) : Prop := forall s, texits nexit S (m s).

Definition okP {A} (P : A -> Prop) (x : exc (A * St)) : Prop :=
  match x with Unr => True | Ok p => P (fst p) end.

Definition mpost {A} (P : A -> Prop) (m : Monad.M St A) : Prop := forall s, tleaves (okP P) (m s).

(* [comment removed for export] *)
Lemma mexits_ret S {A} (a : A) : mexits S (mret a).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "h01Ah11Sh21ah31sp;1p;3p-1p10000p60521002R0p8p,2StR1p4p300R2g000fR3p4p710p8P2g001ZR4p605311001R5p8P2P0p8P2p1002QR2p4p7210p8P5p1002np4p7210R6p8p1003_p60521002R7P2p4p710p8P0P6p8P0P7p8p200R7P5p8P7P3p4p7210p8g004Sj10Tg0058j15Tg005Vj12Tg0069j11TP3j34TP4j33Tg006Y#0#0#0#0#0#0#5#2#1f0R4g007>X31f2f1R3A413433eW2X07W1o"). Qed.
Lemma mexits_munr S {A} : mexits S (@munr St A).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "h01Ah11Sh21sp;1p;2p;3p200R0g001ZR1p605311001p8P0g007ZR2p4p7210p8g004Sj10Tg0058j15Tg005Vj12Tg0069j11TP2j24TP1j33Tg006Y#0#0#0#0#0#0#5#2#1p,2StR1g007>W2f1f0R2141233eX00W1o"). Qed.
Lemma mexits_get S : mexits S (@mget St).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "h01Sh11sp;1p;3g004Sj10Tg0058j15Tg005Vj12Tg0069j11Tg008Nj14Tg001Zj33Tg006Y#0#0#0#0#0#0#5#2#1p,2StR0g007>W1f0%40730eW0o"). Qed.
Lemma mexits_upd S (f : St -> St) : mexits S (mupd f).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "h01Sh11fh21sp;1p;2p;3g004Sj10Tg0058j15Tg005Vj12Tg0069j11Tg009Bj24Tg001Zj33Tg006Y#0#0#0#0#0#0#5#2#1p,2StR0P0[g007>X20f1g00:6f0,4033eW1W0o"). Qed.

Lemma mexits_msys S {A} n (dec : resp -> option A) :
  match n with NExit _ => False | _ => True end -> mexits S (msys n dec).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h01Ah12Hnh21Sh31ai001ah43dech51ni011nh61oi021oh71rh83rsph91si034addri042bsi053bufi064bufsi074codei085counti092fdi0:5flagsi0;3leni0<4pathi0=4proti0>3reqi0?1xp;1p;2p;4p;3p;5p;6p,2StR0p4p300R1g00:VR2p4p741110R3p8P1p100;PR4p4p741110p8P1P4p4p7511110p8P1p100<Op4p7210R4p8P1p100=Jp4p7210p8P1p100>Jp4p7210p8P1p100?JR5p4p7210p8P1P5p4p73110p8P1p100@JR5p4p741110p8P1P5p4p7511110p8P1g00AKR1p4p73110R5p8g001ZR6p605311001R7P3p8p10000p60521002P4p8p200R4P7p8P4g00BPR7p4p7210p8P4P5p8g004Sj10Tg0058j1BTg005Vj1=Tg0069j1<Tg00CDR5j13Tg00Cfj22Tg00DFj11Tg00E>j28Tg00F4j47Tg00FTj26Tg00G6j15Tg00GXj29Tg00HPj34Tg00IFj1;TP2j5:TP1j6ATP7j5@j4?TP6j3>Tg006Y#0#0#0#0#0#0#B#=#<g00J>R6g00K3R7f2R1#3[P6p-0f1R2g00KfR3P3P3P3P3P3P3g00LBP3P3P3P3P3n01101000=20109104201091061010<30109105108101092010910>00101071010>4010310;10=10:2010310;3010310;10=2010310;f5R3f3R8f4R9/20#1R:P51230R;f6R</20R=#1R>,86P5P3%3=P8f0R?O1R@P<P0P?P1C7,6=%5;n10110?0002101000019=?946>%1;%;;546n10110?00021010000X87P2P@%33P5P<P6g00L_R<f8R@f7R;/20R>#1R=P5P>12@0RA#1RB,86P5P;%3AP?P@P0P?P9C7,6A%5>n10110?0002101000019A?946B%;>946=n10110?00021010000D:P?g007>R=X3;P?O1P=n10110200021010000b6X77EAP6P<P3P:P0P9P8P1P?D@D:eX90P0P8P1P2C?9>98eW1W4W5X04W2o"). Qed.

Lemma mexits_bind S {A B} (m : Monad.M St A) (f : A -> Monad.M St B) :
  mexits S m -> (forall a, mexits S (f a)) -> mexits S (mbind m f).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h01ai001ah12a0h21Ah31Bh42Hfh52Hmh61Sh71fh81mh91ri011rh:1si021sh;2s'i031ei041pp;1p;2p;3p;4p;9p;6p;5p200R0g002nR1p4p7210R2p8P0g001ZR3p605311001R4p8P0g00MSR5p4p7210p8P0g00;PR6p4p741110p8p201R7P2p8P7P4p8P7P5p4p73110p8P7P6p4p7511110p8g004Sj10Tg0058j1BTg005Vj1<Tg0069j1;TP1j2:TP3j36Tg00CfR3j21Tg00DFR1j12Tg00E>j29Tg00IFj18Tg00HPj37Tg002Qj35Tg00NHj34Tg00F4j4ATP6l9@TP5j6=j5>Tg00:Vj5?Tg00J>R5g00L_R6f2R4f1R2f0R8D?p=3g006Y#0#0#0#0#0#0#B#<#;p,2StR9/:21:94\4f4R:f3R;;62f6R<P4P8O1R=76:^0:P5P6f7R611<9R>#2R?f5R@/19#2RAP:P8O1P11169RB%2BRC,95P8%8>975?R>P@f8RD?598A4D98O2n10110100020010100X9?P=P1PBf9R=P111D9R1%21,95P8%8B975CP<A5=98A4=98O2n1011010002001010073CP8g007>A3D?>eP3P=P9f;R311=9#2P6f:R=?598A4=98O233P8PDP2P8O2f>f</19#2P=f=R=P=P9P2P8CARD759A4=9DO233eX;9X03P2P8O2n2001104000120100102X11P8O1n10110300020010100X1?M9@P9P<P@P:P;P8E=936AeX:9P9P@P:P;P4D>96<:eW4W5W7W8X37X20W6o"). Qed.

Lemma mexits_bind_P S {A B} (P : A -> Prop) (m : Monad.M St A) (f : A -> Monad.M St B) :
  mexits S m -> mpost P m -> (forall a, P a -> mexits S (f a)) -> mexits S (mbind m f).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h01Hh11ai001ah22a0h31Ah41Bh52Hfh62Hmh72Hph81Ph91Sh:1fh;1mh<1ri011rh=1si021sh>2s'i031ei041pp;1p;2p;3p;4p;;p;6p;5p200R0g002nR1p4p7210R2p8P0g001ZR3p605311001R4p8P0g003_R5p60521002p8P0g0000R6p60521002p8P0g00MSR7p4p7210p8P0g002QR8p4p710p8P0g00@JR9p4p741110p8p201R:P2p8P:P4p8P:P7p4p73110p8P:g00:VR4p4p741110p8P:P9p4p7511110p8g004Sj12Tg0058j1FTg005Vj1ATg0069j1>TP1j2=TP3j39TP6j3ETg00CfR6j21Tg00DFR3j10TP5j2?j34Tg00E>j2:Tg00IFj17Tg00HPj38TP8j36Tg00NHj35Tg00GXj2<Tg00F4j4;TP9l;DTP7j6Cj5BTP4j5@Tg00J>R4g00L_R7f2R9f1R8f0R5D@p=3g006Y#2#2#2#2#2#2#F#A#>p-0\8p,2StR1/=9f3R21=12[f5R;f4R<;98AE;29f6R=P;P5O1R>f9R?f7R@P<P8O139[]1P4P7P?f8R7/11RA#0RB11@1#0RC1?7=P>P311?1R>%0>RD,:4P5%7A984BP=f:RA?615A5A15O2n10110100020010100X<BP2P5O1P9P5O1P3P>A4A75f<RE11A1RF#0RGP3f;R3/11RH%0H,:4P8%7F984GP7A6E15A5E15O2n1011010002001010033[P5%7>R>94?@g007>A84D>933DeW0P6P3P111E1R3/<594EAf>%03P?f=R3?618A5318O233[P5f?RA11A1R6PAP1P8P5C;'<743P?P9P5P8O3fA%06PEf@REPEP1P9P8C;R9761A5E19O233eW0X>1X13P8P5O2n2001104000120100102X2FP5O1n10110300020010100X2BM;DP1P7P@P;P<P5EC93?CeX=1P1P@P=P<P2DB997=eW5W7W6W:W;W8X4:X30W9o"). Qed.

Lemma mexits_mloop S {X R} (body : X -> Monad.M St (X + R)) :
  (forall x, mexits S (body x)) -> forall fuel x, mexits S (mloop fuel body x).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h01xi001xh14fuelh22Hbh32IHh41Rh51Sh61Xh71ah84bodyh91ri011rh:1si021sh;2x'i032x'p;1p;2p;3p;6p;7p;4p200R0g002nR1p4p7210R2p8P0g001ZR3p605311001R4p8P0g00NeR5p605311001R6p8P0g00OaR7p4p7210p8p201R8P2p8P8P4p8P8g00PVR4p605311000p8P8g00QQR2p605311000p8P8P6p8P8P5p6054111000p8P8P7p4p73110p8g004Sj10Tg0058j1=Tg005Vj1;Tg0069j16Tg00RMR6j24TP1j23TP3j32TP7j61TP2j2:Tg000fj35TP4j37TP5j78Tg00Rlj19Tg00SKj4<Tg006Y#0#0#0#0#0#0#=#;#6f1R5p,2StR4f2R2/45'3[f4R7f3R3/42P5f0R1O132^02g00SlR9f5R:f7R;P4f6R<P:P5P7P1E172:]0R5X191:<7P4P:P7g00TKP3P1E192<7eX07f8R314;<R=P<P:P1O1P6P3P;1343P1P4f9R>P3P7P;P1E1A5431n200110200021010310101X:=P7P1O1R7P6P3P;f:R?P6P>P3134>P1P4P?P>P:P3P1E1A54>1n200110200021010310101723P1P7X;>P1O1f;?7>1X93P1O1n200110200021010010101X7=F8P4P;P<%92P:P1E1923<eX0<X35X19P1C<W1W2W8X48X60W5o"). Qed.

Lemma mexits_if S {A} (b : bool) (m1 m2 : Monad.M St A) : mexits S m1 -> mexits S m2 -> mexits S (if b then m1 else m2).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h01Ah11Sh21bi001bh32m1h42m2p;1p;2p;3p200R0g002nR1p4p7210p8P0g001ZR2p605311001p8g004Sj10Tg0058j15Tg005Vj14Tg0069j13TP1j22TP2j31Tg006Y#0#0#0#0#0#0#5#4#3g00TjR2p,2StR1f1R3'2f2,21f4R4f3R5;13f5?143P2f7R6f6P21216f0R6P4P5n011000002000031P4P3P6n0110000020000UUW4W3W2X00W1o"). Qed.

(* [comment removed for export] *)
Lemma mpost_ret {A} (P : A -> Prop) (a : A) : P a -> mpost P (mret a).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "h01Ah11Hh21Ph31ah41sp;3p200R0g000fR1p4p7210p8P0g0000R2p60521002p8P1j31TP2j30Tf0R2p-0[f1R1P1P2O1p,2StR2P1W4f3R3f2A123130eW1W3W2X00o"). Qed.
Lemma mpost_munr {A} (P : A -> Prop) : mpost P (@munr St A).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "h01Ah11Ph21sp;2p;3p200R0g0000R1p60521002p8P0g007ZR2p4p7210p8P2j21TP1j30Tf0R1p-0[p,2StR2g007>W2f1R31123701eW1X00o"). Qed.
Lemma mpost_get (P : St -> Prop) : (forall s, P s) -> mpost P (@mget St).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "h01sh11Hh21Pp;4p;3p;1g00F4j43Tg002Qj32Tg008Nj10Tg0000j31Tp,2StR0p-0[f1R1f0R2O1^00P1P0P0P2P2C39200O1X00%009101eW1W2o"). Qed.
Lemma mpost_upd (P : unit -> Prop) f : P tt -> mpost P (@mupd St f).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "h01Hh11Ph21fh31sp;2p;3g009Bj21Tg0000j30Tg00:6R0p-0[p,2StR1P1[f1R2g00UJO1P2X31f21112500eW0W2W1o"). Qed.

Lemma mpost_true {A} (m : Monad.M St A) : mpost (fun _ => True) m.
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h01Ah12_Hh21mh31ph41rh51si001ai011ep;2p;1p;3p;7p200R0g002nR1p4p7210p8P0g003_R2p60521002p8P0g0000R3p60521002p8P0g00=JR4p4p7210p8P0g00>JR5p4p7210p8P1j27Tg00Cfj20Tg00DFR1j12TP2j21j35TP5j36TP4j73TP3j34Tp,2StR3f0R4'7g00J>R5f2R2/03#2R6g00KfR7V6P7V2,12f1R2P4O1R8A6568P1f3/03f5R1P7V1;52\7P4g007>X17R1f4/03P1W3P4O1n10110100020010100X46F3X53P7V2=424eW2X00o"). Qed.

Lemma mpost_mono {A} (P P' : A -> Prop) (m : Monad.M St A) : mpost P m -> (forall a, P a -> P' a) -> mpost P' m.
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h01Hh11Ah22HPh32Hmh41Ph52P'h61ai001ah71mh81ph91rh:1si011ep;2p;3p;1p;7p200R0g002nR1p4p7210p8P0g003_R2p60521002p8P0g0000R3p60521002p8P0g00=JR4p4p7210p8P1j29TP3j36Tg00Cfj21Tg00DFR3j17TP2j25j30Tg00IFj14Tg002Qj33Tg00GXj22TP4j78Tf0R4p-0R2[f1R1P2[p,2StR2f2R5'9f3R6?654f4R7P7P4O1P7P1O1[]6g00J>f6R8/12#7R9f5R:,581587P6P4O1P5P4O1P3f7R3/12R7f8R;?034f9R<?031[P4g00KfP4W0%47903811;2R3#490;8[eP;A3<24O1P:f:R8?321P4O2W011<2/2490<;1182/21908;[eX83P4O1n10110100020010100X99F8X:2A6:65eW2W3W7W5W4X10o"). Qed.

Lemma mpost_msys {A} (P : A -> Prop) n (dec : resp -> option A) :
  (forall r a, dec r = Some a -> P a) -> mpost P (msys n dec).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h01Eh11ai001ah21rh31Ah41Hh51Ph63dech71nh81oi011oh91si021xp;1p;2p;3p;4p;5p200R0g003_R1p60521002p8P0g0000R2p60521002p8P0g00BPR3p4p7210p8P0g00<OR4p4p7210p8g00CDR5j10Tg00FTj27Tg00Ujj31Tg00VDj2<Tg00Cfj23Tg00DFj15TP1j24Tg00E>j2=Tg00F4j4;Tg00G6j1:Tg00GXj28Tg00HPj32Tg00IFj19TP4j46TP3j5@j4?TP2j3>Tf0R2p-0[g00J>R3g00K3R4f3R1#0[f4R6f5R7#0f2R8f1R9O1177231P7P9O1[]1^24p,2StR:P1P2O1f6R;#0f7R<#0R=/<2P6P9O1=1=2P5f8R=f9R>#0P;P1O1;12P3f:R?/3:R@#5RA14?>P5P@f;RB/3:RC#5RD,=3P5P?%0CP9PBP:P2P;C;,7C%:@n1011020002101000018C2923D%9@923An10110200021010000C6]0P9%0?P<P6O117?231P<P7P9P2O3P3PD14B?PBP:P9P;C;,8C923DC6eW0X1>P2O1%0=P7P8O1%:=31g007>P313>:RD#5RC14>=%9D923CC6eW0n10110100021010000P2O1b0b8X24P3137:#51476P:P7P1P8P2D@C6eW9P:P6P8P9C?9>61eW4W6W7W5X30o"). Qed.

Lemma mpost_bind {A B} (P1 : A -> Prop) (P : B -> Prop) (m : Monad.M St A) (f : A -> Monad.M St B) :
  mpost P1 m -> (forall a, P1 a -> mpost P (f a)) -> mpost P (mbind m f).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h02H1h11ai001ah22a0h31Ah41Bh52Hfh62Hmh71Ph82P1h91fh:1mh;1ri011rh<1si021sh=2s'i031ei041pp;2p;3p;1p;4p;9p;6p;5p-1p200R0p8P0g002nR1p4p7210R2p8P0g003_R3p60521002R4p8P0g0000R5p60521002R6p8P0g00MSR7p4p7210p8P0g002QR8p4p710p8P0g00?JR9p4p7210p8p201R:P2p8P:P4p8P:P6p8P:P7p4p73110p8P:g00<OR6p4p7210p8P:P9p4p73110p8P1j2=TP5j39Tg00CfR5j20Tg00DFR1j11TP3j22j34Tg00E>j2;Tg00IFj18Tg00HPj37TP8j35Tg00NHj36TP6j43Tg00GXj2:Tg00F4j4<TP9l9@TP7j6?j5>Tf1R7p-0[R9p,2StR6f3R8'=f4R31=63[f5R4?987f6R2P4f0R;O1f7R<P8P7O1794[]1g00J>R=f8R>/06R?#1R@10<6#1RA12>212<4RBP3P;O1P1f9RC/06RD%1DRE,;=P;%8?97=@P4f:R4?56;A646;O2n10110100020010100X;@f2R?P;O1P1PDA44>;P=1046RF#1RG124>P1f;R1/06RH%1H,;=P7%8F97=GP<f<RG?56;A6G6;O2n10110100020010100C3[P;%8DRD94C<g007>P=PE12C<A7=EDC3eW0P5P1P610G6R5/:;94G4P=%1512G4P>f=RG?567A6G67O2C3[P;f?R41046R5P4P6P7P;C<':74GPCP?P;P7O3P=%15124GP1f@R1P1P6P?P7C<R4756A6164O2C3eW0X=6X1GP7P;O2n2001104000120100102X2FP;O1n10110300020010100X2@M9@P=PAPBP6P>P<P3P8P;E?C3eX<6P6P<P2P8P?D>9923eW5W6W9W:X79W8X4:X30o"). Qed.

Lemma mpost_bind_t {A B} (P : B -> Prop) (m : Monad.M St A) (f : A -> Monad.M St B) :
  (forall a, mpost P (f a)) -> mpost P (mbind m f).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "h01ah11Ah21Bh32Hfh41Ph52_Hh61fh71mp;2p;3p;8p201R0g002nR1p4p7210R2p8P0g0000R3p60521002p8P0p100MSR4p4p73110p8P0g00V^R5p605311002p8p200R6P2p8P6P4p4p7210p8P6g00WYR4p60521000p8P6P5p60521003p8P1j20TP3j33TP4j22TP5j81Tf0R5p-0[p,2StR4f2R3'0f3R11041[f4R4f1R2P5O19341]0f5R7P4g00KfR4V7P1P3P21273f6P4UP5O1P3P2O1W5X07G1W3W6W7W4X20X16o"). Qed.

Lemma mpost_mloop {X R} (P : R -> Prop) (body : X -> Monad.M St (X + R)) :
  (forall x, mpost (fun y => match y with inl _ => True | inr r => P r end) (body x)) ->
  forall fuel x, mpost P (mloop fuel body x).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h01xi001xh14fuelh22Hyh31yi011yh42Hbh52IHh61Ph71Rh81Xh91ah:4bodyh;1ri021rh<1si031sh=2x'i042x'i052y0p;2p;3p;6p;4p;8p;1p201R0g002nR1p4p7210R2p8P0g000fR3p4p7210p8P0g0000R4p60521002R5p8P0g00OaR6p4p73110p8P0g00XTR7p60521001p8P0g00YNR8p60521001p8P0g00V^R9p60521003R:p8P0P9p605311002p8p200R;P2p8P;P5p8P;P6p4p7210p8P;P:p8g00RMR:j22TP1j23TP4j31TP6j60TP8j29TP3j34TP7j48TP9j85Tg00Rlj16Tg00SKj47Tf0R9p-0R7[f2R3p,2StR8f3R6/23'3[f4R4/26R1P:f5R5P4P7P9g00KfR2P4P9O1R<n200110100021010510102X31f1R1P9O131^06g00SlR=f6R>P8f7R?P>P1P4P9E091>5]0R@X1=1954P8P>P5g00TKP6P9E09154eX05f8R6/2?RAP?P:f9RBP6P7P9P2P6P9O1n200110100021010510102X3AP>P5P9O1P:PBP6138BP9P8f:RCPBP4P?P9E0A48B9n200110300021010410102X<AP<P:PBP6P:PCPBP7P9P2PBP9O1R7n200110100021010510102P:f;R:PC138:P1P8f<P:P>PBP9E0A48:9n20011030002101041010291CB[P9P5P1O1X22X=CP9O1P:PCP1P9C8X27X;BP9O1n200110300021010010102X9AG5P8P6P?%63P5P9E091?>eX0?X5@X1=P9C7W1W4W:W6X70X8;o"). Qed.

Lemma mpost_if {A} (P : A -> Prop) (b : bool) (m1 m2 : Monad.M St A) : mpost P m1 -> mpost P m2 -> mpost P (if b then m1 else m2).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["MExits"] "p'0h01Ah11Ph21bi001bh32m1h42m2p;2p;3p200R0g002nR1p4p7210p8P0g0000R2p60521002p8P1j21TP2j30Tf0R2p-0[g00TjR1p,2StR3f2'1f3R4,13f4R5f1R6704f5?056P1f7f6P1f8,13P2P5P4n011000002000030P5P6P2n0110000020000UUW4W3W2W1X00o"). Qed.
End MExits.

Create HintDb mexits.
#[export] Hint Resolve mexits_ret mexits_munr mexits_get mexits_upd : mexits.
#[export] Hint Resolve mpost_munr mpost_true : mexits.

(* [comment removed for export] *)
Ltac mex :=
  lazymatch goal with
  | |- mexits _ (mret _) => apply mexits_ret
  | |- mexits _ munr => apply mexits_munr
  | |- mexits _ mget => apply mexits_get
  | |- mexits _ (mupd _) => apply mexits_upd
  | |- mexits _ (msys _ _) => apply mexits_msys; exact I
  | |- mexits _ (mbind _ _) => apply mexits_bind; [mex | intros ?; mex]
  | |- mexits _ (mloop _ _ _) => apply mexits_mloop; intros ?; mex
  | |- mexits _ (if ?b then _ else _) => first [apply mexits_if | destruct b]; mex
  | |- mexits _ (match ?x with _ => _ end) => destruct x; mex
  | |- mexits _ (let _ := ?x in _) => cbv zeta; mex
  | |- mexits _ _ => first [ assumption | solve [eauto 2 with mexits] | idtac ]
  | |- forall _, _ => intros ?; mex
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Ltac mpo :=
  lazymatch goal with
  | |- mpost _ (mret _) => apply mpost_ret
  | |- mpost _ munr => apply mpost_munr
  | |- mpost _ (mbind _ _) =>
      first [ eapply mpost_bind; [ solve [ eauto 2 ] | intros ? Hp; mpo ]
            | apply mpost_bind_t; intros ?; mpo ]
  | |- mpost _ (if ?b then _ else _) => first [apply mpost_if | destruct b]; mpo
  | |- mpost _ (match ?x with _ => _ end) => destruct x; mpo
  | |- mpost _ (let _ := ?x in _) => cbv zeta; mpo
  | |- mpost _ _ => first [ assumption | solve [eauto 2 with mexits] | idtac ]
  | |- forall _, _ => intros ?; mpo
  | |- _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Alloc.
Variable S : list word.

Lemma ev_step_exits : forall atop e, mexits S (ev_step atop e).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["Alloc"] "p'0h01ai001ah14addri014addrh22a0h33leni023lenh44proti034proth54atoph65caddri045caddrh71ei051eh85flagsi065flagsh94hinti074hinth:1pi081ph;1rh<1sh=3whyi093whyi0:1bi0;7changedi0<3reqi0=1xp;2p;1p;4p;5p;3p;6p;8g00ZIR0p4p70R1p100[>p4p710p8P1g001ZR2p6051002R3p8P1g00NeR1p605311001R4p8p100\5p4p70R5P3p8P5P4p8p100\jp4p70R5P2p605311001p8P5P1p6054111000R5p8p100]cp4p70R3g00PVR6p605311000p8P3P4p8P3P5p8g002nj2^Tg00^Xj2=Tg00_5j1BTg00BPj44Tg00_jj1>Tg009Bj2<Tg00MSj51Tg008Nj1MTg00`ej1;Tg00a\j2KTg00bSj2ITg00c1j1]Tg00cOj4VTg00dDj2UTg00eGj1TTg00Cfj2STg00fEj1RTg00fej3DTg00gbj3CTg00hZj2QTg00iOj2PTg00jIj3OTg00k>j2NTg007Zj2LTg00lBj65Tg00m>j3@TP1j82Tg00n9j2JTg00QQj3\Tg00o4j2[Tg000fj3WTP2j4XTP6j4YTg0100j8ZTg010jR6g011cR2f0R13Wp=0P6g00:6R5P2f1R3P1D1p=9P6g012AR4P3P1C4p=6P6P4P2P3P1D1p=7P6g013;R7P2P3P1D1p=AP6P3P2P1CXp=:P6P3P2P1CYp=3P6f4R8P5P2f3R9f2R:P3P1G2p=?P6f5P2P8P9P:P3P1GZp=8P6P:P4P3P1g007>R;E5p=EP6P8P4P2P9P:P3P1G2p=FP6P:P7P3P1P;E5p=GP6P8P7P2P9P:P3P1G2p=Hg0146R<P<p,1SR=P<1^62R<P1g00TjR>P<g014kR?,=1R@P6P2P2P6P2%B?RAg015IRBC4RC%>1RD,<6RE%03V5RF'9X;2RGD1RHP6P6P2%M6RIP6g016ARJP2P6PJ%B3RK%;1/K3RLC4RMPJP<P1%>:RN,<6RO%09V5RP'9%;3RQ#0n0110000020000X0JRRD1X<6RSD1RTn0100000020000P>P<g017:,I1/=?#]RUP6g018:RVP2P6PVP9P:P3P1CVRW1U9:RXC4RYPVP2P1%T1RZP8PZn011000003101050010105R[#0X0VR\D1R]P>P<1=3?R^f6R_1S22#RR`7D:,6WP4P2P1PZP1n011000002101051010=Ra#0X04Rb'7AC_:`,6W/7bn0100000020000n0100000020000P6P71Q31R_1P31RcC4RdP7P2P1PZP?n011000002101051010;R?#0X07RZ'AP6P7AO:31Re1N:3RfC4Rg/AZ1L62RhPhn0110500061010<4010110210310620101102301011021033010810410710109':P1P=P@PHPTP6P=P2P2PCPGP6P=P2PAPBP;E5P=PEPFA@6=D13=3X25D?X02G2P6P=P6P2PIPS1J6=P6P=PJP2PMPRP6P=PJPKPLP;E5PJPJP<P1%>9,<6%08V5'9%;:#0n0110000020000,:=P1P=POPPA@6=N13=9X25D?13=Qn0110:00020000X2JG2X06G2E8X12P1O1P=PUP]P>P<P^f9R<?D:`R>,6WR]/7bRUAC<:`R<,6WR`/7bRJn0100000020000P6P=PVP2PYP\P6P=PVPWPXP;E513=[X0VG2P=P^PUPJP=P]PbAE=W>13=aX04R4DFP=P`PbAE=W<P4DFE8E8X82X42X32X12P9P:P3P1O4P=PdPZAG=_c13=?X07R7DHX32X12P3P1O2P=PgPZAG=efP7DHX42X32X12P:P3P1O3A\6=2R6X92X62X:0P:P3P1O3g019:P6W=P1O1n0110501061110141101102103106201011023010110210330108104107101091[31,:=eW7X52o"). Qed.

Lemma membed_exits : forall {R} atop (t : stree ev Z R), mexits S (membed atop t).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["Alloc"] "h01th12IHh21Rh34atoph41eh51kh61rh71zp;3p;4p;2p;8p;5p;7p100ZIp4p70R0g001ZR1p6051002R2p8P0p200R0p8p100\5p4p70R3P2p8P3P0p8P0g01:9R3p4p73110p8P0P1p605311001p8P0g00PVR2p605311000p8P0g00NeR4p6054111000p8P0g01;2R5p4p710p8p100]cp4p70P0p8P5j30TP1j41TP2j43Tg01;mj4:Tg00o4j29Tg01<dj28TP4j84Tg01=bj55TP3j76Tg00[>j37Tg0146R3g011cR4f0R237p=2f1R1#2P3P4f2R5%25g010jR6p,1SR7f3R8A0852C1W0P6P7P8P2C3P6P7P8P3P4P8P2C:9085C1eX65f4R8#2\4P6P7f5R9P1P2O19098C1\4P6P7P4P91985f6P5P2O1709X741885P2G4P6P7P9P3P4P9P5P1D59098C1eW1W5X43P2F6W0X34X20o"). Qed.

Lemma raw_malloc_exits : forall n, mexits S (raw_malloc n).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["Alloc"] "p'0h02a0h11ah21mi001mh31nh41oi011oh51sh61xi021pi034sloti043st'i052x0p;2p;1p;3p;5p;4p;8p100ZIp4p70g00NeR0p6051002R1p8p100\5p4p70P1p8g00CfR1j28Tg00CDR2j16Tg008Nj1=Tg01>Yj19Tg01?Nj1GTg01@Ej2ETg01;2j3>Tg002nj2<Tg01A=j1;Tg009Bj2:Tg01B3j31Tg00FTj22Tg00G6j1FTg000fj30Tg00MSj55Tg00n9j2DTg01C1j3ATg001Zj47Tg00m>j3?Tg00PVj4@TP0j83Tg01Cnj1BTg00F4j4CTg00]cR0g011cR3f1R4f0R5CCp=4g010jR6p,1SR7P61803R8#6R9%=6P6g01DmR:%60R;'8R<P9%95R=#GR>1E=4R=5><R?P1P:P;1<69R@P5P6g00:6RAP9%;4RB,:6RCP2P0P9P4f3RDf6715,45,28%F8REn101102000210103009069VAD5n2001105000120104102X6<RFD5X561D67P6P7P<P9P?PFAA<>=P1P:P;P6P7P9P1P:P;P@P5P6PAP9PCP2P0P9P4f791D5,45,28PEn101102000210103009069VAD5n2001105000120104102C7P5P6P7PAP9PCP2P0P9P4f891D5,45,28PEn10110200021010300RE9069VAA?67BP6P7P9PEC@X0AG3X4;X2:P4P5O2n2001102000120100101X0<G3X16G3P6P7g00\j#6%B5C7eX33o"). Qed.

Lemma raw_free_exits : forall p, mexits S (raw_free p).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["Alloc"] "h01ah12a0h21ph31sh43st'p;1p;3p;2p;5p;8p;4p100ZIp4p70g00NeR0p6051002R1p8p100\5p4p70P1p8g008Nj1?Tg01>Yj1>Tg01?Nj12Tg002Qj31Tg00FTj2=Tg01Efj2:Tg01;2j33Tg01A=j14Tg009Bj25Tg00MSj56Tg00n9j27Tg01C1j38Tg00m>j39TP0j80Tg01F\j1<Tg001Zj4;Tg00\jg010jR0p,1SR1P0g00:6R2%?0P0g01DmR3P2f0R4#>R5#2R6g00]cR7g011cf1517'=,:5R5533R7%44R8,50X43R9D6X301701P0P1P3P2P7P9A8365A9018X13G0X00G0P0P1P2%<4C;eW2o"). Qed.
End Alloc.
#[export] Hint Resolve raw_malloc_exits raw_free_exits membed_exits ev_step_exits : mexits.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StdioX.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Variable S : list word.

Lemma stdio_write_loop_exits : forall fuel fd iov, mexits S (stdio_write_loop (St:=St) fuel fd iov).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h02fdh14fuelh23iovh32IHh41ah53cntp;1p;4p;3p;2p;6p;8p100ZIp4p70g001ZR0p6051002R1p8p100\5p4p70P1p8p,2StR2p4p300R3P1p8P3g01GYR1p4p710p8P3p101HYp4p710p8P3g00NeR3p605311001p8g0069j11TP1j40TP0j42Tg00QQj35Tg004Sj13Tg0058j1<Tg005Vj1;Tg01IOj47Tg01Ikj26Tg01J`j14Tg01KYj18Tg00BPj49Tg002nj2:Tg00^Xj2ETg000fj3DTg01LSj2CTg00lBj6=Tg00PVj4>Tg0100j8?TP3j8@Tg00Rlj1ATg00SKj4BTg00SlR3g011cR0%10R1#1R4P2p,1SR5g00:6R6P2f2R7f1R8f0R9C0C2]2]0R:X13A5256P2P5P6P2g00TKP8P9C0C2eX24X00P2P5P0P6P2P0P1g006Y#3#3#3#<#;#1g01MNP9C7,68R1%49#8R;C9g00Tj1:26%48,E9R<g00UJR=9D26R>P2f4P71C89R?C0R@n0100000020000X50P2P5P0P1P;g007>E=P2P5P6P<P>P@P2P5P6P=C>f3R=P7P?O2G?X40G@P2P5P6P2%A=P8P9C0C2eX24X00X3:X13P9CBW1o"). Qed.

Lemma stdio_write_exits : forall fd buf s, mexits S (stdio_write (St:=St) fd buf s).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "p'0h03bufi003bufh12fdh21si011li021zp;1p;2p;3p;4p;8p100ZIp4p70g0100R0p6051001R1p8p100\5p4p70P1p8p,2StR2p4p300P1p8g0069R1j11Tg01NFj22Tg01O>j24Tg01O[j23Tg007Zj2>Tg01P8j1;Tg00Rlj1:Tg00fEj15Tg01PXj30Tg01GYj46Tg00QQj37Tg01Q8j38TP0j89Tg01R?j4=Tg001Zj4<Tg011cR0%10R3P2p,1SR4g00:6R5g01S:f1R6,20f0R7,20'4R8'31>25P2%;8#:R8f2R9P1P0%13P6%53R09037f3A0390503n10110000020020102101R0C6A7245A8890G9P2P4P5P2P9P6P7C=C<eX23W0W1o"). Qed.

Lemma upd_so_exits : forall f, mexits S (upd_so get_so set_so f).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h01fh11sp;3p;4g00m>j32Tg01HYj41Tg001Zj40Tg01T3R0P0[p,2StR0p,1SR1p,6set_soR2f1p,6get_soR3f0R4O1O1P4O2X1032P0P1g00:6P0P3P2P4C1C0eW0o"). Qed.

Lemma rd_so_exits : mexits S (rd_so get_so).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h01ah11sp;1p;3p;2p;4p;8g008Nj16Tg000fj35Tg00n9j20Tg00PVj41Tg00Nej84Tg01Tnj22Tg001Zj43Tp,2StR0p,1SR1P0g01T3R2%60p,6get_soR3f0O1R49502X101001P0P1P2P4C1X00G4P0P1P21203C3eo"). Qed.

Local Hint Resolve stdio_write_loop_exits stdio_write_exits upd_so_exits rd_so_exits : mexits.

Lemma stdout_stdio_write_exits : forall l, mexits S (stdout_stdio_write get_so set_so l).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h02soh11ah22a0h31lp;1p;2p;4p;5p;3p;8g0069j1>Tg01Tnj2=Tg01Ucj12Tg01VAj11Tg01R?j4<Tg00fEj19Tg01W7j13Tg01X0j14Tg01Xhj45Tg01HYj46Tg00MSj57Tg01Ycj38Tg00Nej80Tg01Zej4;Tg001Zj4:Tg011cR0#>p,2StR1p,1SR2g01T3R3g00:6R4p,6get_soR5,=1P1P4P4P1g006Y#2R6f0R7#1R8f1R9C<R:P1P5p,6set_soR;g01[g%90%37%47C5X03C6V4R0D7X03g01\GR<P1P2P4P4P:P0A8689P<X24G0X13G0P1P2P4P1P5P;P7C;C:eW3o"). Qed.
Local Hint Resolve stdout_stdio_write_exits : mexits.

Lemma stdout_writefn_exits : forall l, mexits S (stdout_writefn get_so set_so l).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "p'0h02soh12a0h21ah32a1h41ei001eh51lh61ri011rh71vi021vi031sp;1p;2p;4p;5p;3p;6p;8g0069j1GTg01Tnj2FTg002nj2;Tg01X0j15Tg01]Cj1ETg01VAj1>Tg01W7j1<Tg01Xhj44Tg01HYj43Tg01Ucj16Tg01^<j27Tg00BPj48Tg007Zj29Tg00MSj51Tg000fj3DTg01Zej4BTg00lBj6=Tg001Zj42Tg00QQj3?Tg00Nej80Tg00PVj4@Tg0100j8ATg01_1j1:Tg01`:j4CTg011cR0#Gp,2StR1p,1SR2g01T3R3g00:6R4p,6get_soR5,F1P1P4P4g00Tj1;14R6f0R7#5R8P1P4P4P1P5p,6set_soR9%E7R:%>7R;%<7g01a8R<C4X03C3R=P1g01aXR>P4P1P>g006Y#6g01bN'7R?g01cHR@C8RAP>P6P7P1P5P9P:P;P<P8C4X03C31914n0110100021010010102R<X6>R;D1V4R:D1R6g00UJRB9D14RCn0100000020000RDP1P5P9f2RECBV4RFD1X03g01\GRGP1P2P4P4PDPFP1P2P4P8P6PCP1P2P4P4P=P:PGP1P2P>P4PAP;P1P2P>P?P@g007>E=P>P1P2P4P<C2P7PGX40P7O1A?124X70P7O1n0110300021010010102X3>G0X14G0P1P2P4PBC@GA%:EX14G0X23G0P1P2P4P1P5P9P7CCC2eW5o"). Qed.
Local Hint Resolve stdout_writefn_exits : mexits.

Lemma stdout_towrite_exits : mexits S (stdout_towrite get_so set_so).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "p;3p;4g01dAj31Tg001Zj40Tg01\Gp,2StR0p,1Sg00:6p,6get_sop,6set_so510C0eo"). Qed.
Local Hint Resolve stdout_towrite_exits : mexits.

Lemma stdout_fwritex_exits : forall l, mexits S (stdout_fwritex get_so set_so l).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h02soh11ah22a0h32a1h41lp;1p;3p;2p;4p;5p;8g0069j1JTg01dAj3ITg01Tnj2ATg002nj2=Tg01VAj1HTg01NFj25Tg01e?j2BTg01O[j2:Tg01`:j4;Tg01W7j1>Tg01e\j12Tg01P8j18Tg01fYj3<Tg000fj3GTg01]Cj1ETg01g8j3DTg01gVj39Tg01X0j1CTg01Xhj43Tg01HYj44Tg00MSj57Tg01h3j16Tg00PVj4@Tg0100j80Tg00Nej81Tg01i8j4?Tg001Zj4FTg011cR0#Jp,2StR1p,1SR2g00:6R3P3p,6get_soR4p,6set_soR55I1P1g01T3R6P31A14R7g00TjR81=13R9g01j6f0R:#HR;,50'Bf2R<,50':R=P1P4P5P<C;R>P8P9%>:R?P1P3P3P8P9g014k%2<R9':R8P1P4P5%89=<0<R9C;R@g00UJRA9G13RBn0100000020000RCP1P4P5%E:RDf4RE#2#8=D0E990;P?%C:REC3X06C4V3RFD7RGP1P4P5PDf3990;P?PEC3X06C4REn0100000020000R;n0100000020000X06R0D7V3g01k3RDP1P2P6P3P7P0PDP1P2P3P=P>P;%6<P1P2P3P?PGPEP1P2P3P3PCPFP1P2P3P8P@PB%69P1P2P3PAC@G0PDX33G1PDG0G0X26G1X13G1P1P2P3P1P4P5P:C?CFeW4o"). Qed.
Local Hint Resolve stdout_fwritex_exits : mexits.

Lemma out_pieces_exits : forall ps, mexits S (out_pieces get_so set_so ps).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h02psh12IHh21ah31pp;1p;4p;8p;3p;5g0069j12Tg01l8j40Tg001Zj41Tg00PVj43Tg00fEj19Tg01i8j48Tg01m2j17Tg00Nej84Tg01PXj35Tg01n7j56Tg011c#2R0#2R1P0p,2StR2p,1SR3g00:6R4P2p,6get_soR5p,6set_soR6f0R7C0C1R8X01P2P3P4g00UJC3P2P3P4P2P5P6%90C0C1eP2P3P4P4P2P5P6f2R9C8P2P5P6P9C0V4%79f1R:X24G4P2P3P4P2P5P6A509:C0C1eX18X01X30P7D6W0o"). Qed.
Local Hint Resolve out_pieces_exits : mexits.

Lemma stdout_vprintf_exits : forall ps, mexits S (stdout_vprintf get_so set_so ps).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h01ah12psp;1p;3p;4p;8g0069j10Tg01dAj36Tg01l8j42Tg01nYj11Tg00Nej85Tg01oZj44Tg001Zj43Tg011c#0#0p,2StR0p,1SR1g00:6R2P2p,6get_soR3p,6set_soR4560P0P3P4f1R5C2V2g01k3%15X02G5P0P1P2P0P3P4f0C4C3eW1o"). Qed.

Lemma stdout_exit_flush_exits : mexits S (stdout_exit_flush get_so set_so).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h01ah12sop;2p;1p;4p;3p;8g01Tnj2=Tg002nj2<Tg01VAj10Tg01NFj21Tg01O[j2;Tg00fEj12Tg01`:j43Tg000fj34Tg01h3j15Tg00PVj46Tg0100j87Tg00Nej88Tg020Xj39Tg001Zj4:Tp,2StR0p,1SR1g01T3R2g00:6R3p,6get_soR4,=0g00Tj1<03g014kg011cR5f0#0'1';R6P0P4p,6set_soR7%25R5C3R8g00UJR99403R:n0100000020000X12g01k3P0P1P3P6P8P:%55P0P1P3P9C6G7X02G8P0P1P3A9047C:eo"). Qed.

Lemma stderr_pieces_exits : forall ps buf, mexits S (stderr_pieces (St:=St) buf ps).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h03bufh12psh22IHh31ah41pp;1p;3p;4p;2p;5p;8g0069j12Tg021Yj30Tg001Zj41Tg00PVj45Tg00fEj14Tg01NFj23Tg01e?j2<Tg01O[j2;Tg004Sj1:Tg01Ucj16Tg01R?j47Tg00MSj58Tg01gVj39Tg01Ycj3ATg00Nej8@Tg0100j8?Tg01PXj3=Tg01n7j5>Tg011cR0#2R1#2R2P1p,2StR3p,1SR4P1f0R5f1R6503C1^01R7X12P3P4P1P5C5P3P4P1%419035C1eX01P3P4P1g022V1305'<f3R8,30';P3g00:6R9P1P3g006Y#:#6R:P5P8C7R;%40R<=038V9R=D8A9058R0f2R>503P3P4P9P1P;P=AA:58P>P<O1X39G@P6P0O1G?P3P4P1A=18>9035C1eX01X27X12X41P5D>W1o"). Qed.
Local Hint Resolve stderr_pieces_exits : mexits.

Lemma stderr_fprintf_exits : forall ps, mexits S (stderr_fprintf (St:=St) ps).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h01ah13bufh22psp;1p;3p;4p;2p;8g0069j10Tg00fEj1:Tg021Yj32Tg004Sj11Tg01Ucj19Tg01R?j48Tg023Uj23Tg01Ycj34Tg00Nej85Tg024Yj26Tg001Zj47Tg011cR0#0R1#0p,2StR2p,1SR3P1g00:6R4%:0R0f0R5522P2g006Y#1#9R6P5P0C8X111350A4650X01G5P2P3P41625C7eW2o"). Qed.

Lemma stderr_fwrite_exits : forall l, mexits S (stderr_fwrite (St:=St) l).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h01lp;1p;2p;4p;3p;8g0069j1<Tg01NFj2;Tg01O[j20Tg004Sj11Tg01Ucj1:Tg00fEj12Tg01R?j43Tg000fj34Tg01Ycj35Tg00PVj46Tg0100j87Tg025Wj28Tg001Zj49Tg011cR0#<p,2StR1p,1SR2g00:6R3g014kf0R4,;0'0P1g006Y#1#:R5%20R0P4C3g00UJR69413A5504P1P2P3P6C6G7P1P2P31814C9eW0o"). Qed.

(* [comment removed for export] *)
Lemma s_diag_exits : forall d, mexits S (s_diag (St:=St) d).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "p'0h04pathi004pathh15argv0i015argv0h21di021di031pp;2p;1p;4p1026Tp4p710R0g002nR1p4p710p8p1027Np4p710R2g001ZR3p605311001p8P2p100PVp605311000p8P2p100NeR4p605311001p8P2P4p6054111000p8P2p1028JR4p605311001p8P2P4p6054111000p8P2p10100p605311000p8P2p1029Gp60521002p8p,2StR2p4p300R4P0p8P4g02:DR4p4p710p8P1j2;Tg02;;j1:Tg024Yj20Tg02<7j16Tg02=9j19Tg02>:j23Tg025Wj22TP3j45Tg0069j17Tg02>Uj11Tg02?Zj14TP4j28Tg02@^R4P4P2p,1SR3g00:6R1P41;21f0R4%:4R0,02%64R5,02%94R6,02g011cR7g02AY'3R8,22g02BSR9,02g02CQ,37R:,22g02DQ,37R;,22n01102000710101101031010300000000C5P4%77R7%10W1P4O1%15X07P4O1%16X07P4O1%48%19%4:%4;n01102000710101101001010000000000P2P3P11824C5eW2o"). Qed.

Lemma s_emit_exits : forall v, mexits S (s_emit get_so set_so v).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "h01vp;1p;4g02ESj13Tg02FOj12Tg02GTj40Tg001Zj41Tg011cf0R0#3#2p,2StR1p,1Sg00:6P1p,6get_sop,6set_soP0C0C1eW0o"). Qed.

Lemma io_S_diag_exits : forall d, mexits S (io_diag (io_S get_so set_so) d).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "g02HKo"). Qed.
Lemma io_S_emit_exits : forall v, mexits S (io_emit (io_S get_so set_so) v).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "g02IHo"). Qed.
Lemma io_S_exit_exits : mexits S (io_exit (io_S get_so set_so)).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["StdioX"] "g02JEo"). Qed.
End StdioX.
#[export] Hint Resolve stdio_write_loop_exits stdio_write_exits upd_so_exits rd_so_exits stdout_stdio_write_exits
  stdout_writefn_exits stdout_towrite_exits stdout_fwritex_exits out_pieces_exits stdout_vprintf_exits
  stdout_exit_flush_exits stderr_pieces_exits stderr_fprintf_exits stderr_fwrite_exits
  s_diag_exits s_emit_exits io_S_diag_exits io_S_emit_exits io_S_exit_exits : mexits.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AdapterX.
Context {St ptr : Type}.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable fuzz_one : list Z -> Monad.M St Z.
Variable emit : Z -> Monad.M St unit.
Variable S : list word.
Hypothesis MAL : forall n, mexits S (drv_malloc n).
Hypothesis FRE : forall p, mexits S (drv_free p).
Hypothesis FUZ : forall d, mexits S (fuzz_one d).
Hypothesis EMI : forall v, mexits S (emit v).
(* [comment removed for export] *)
Hypothesis FUZ0 : forall d, mpost (fun rc => rc = 0) (fuzz_one d).

Lemma run_calls_exits : forall n payload rc, mexits S (run_calls fuzz_one emit n payload rc).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["AdapterX"] "h01nh17payloadh22rch32IHh41ah52a0h63rc'p;1p;6p;4p;5p;8p,2StR0p4p300R1g02KMR2p4p710p8P1g001ZR3p6051002p8P1g00MSR1p4p710p8g0069j17TP2j60TP3j41Tg00PVj43TP1j56Tg00Nej82Tg00Rlj15Tg00SKj44Tg00SlR1g011cR3#7R2P0p,1SR4P3P0p,8fuzz_oneR5p,4emitR6f2f1R7f0R8E0C1^23]1R9X01P0P4P3P8C3P0P4P3P0P5P6g00TKP7P8E0C1eX23X12P0P4P3P3P5P7O1P0g00:6R:P3P6P8O1R;P0P5P6f5f3R<P7E0V:R=D6X63p,3FUZP7O1P0P4P:P3P;P=p,3EMIP8O1f4P<P7O2X5:G2X43G2P0P4P3P0P5P6%5<P7P8E0C1eX23X12X39X01P8C4W0o"). Qed.

Lemma run_calls_post : forall n payload rc, rc = 0 -> mpost (fun rc' => rc' = 0) (run_calls fuzz_one emit n payload rc).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["AdapterX"] "h02rch11nh27payloadh33rc'h43Hrch54Hrc'h62IHh71ap;1p;3p;6p;4p;5p;7p;9p,2StR0p4p300g0000R1p6051003p8g0069j19Tg00Ujj38Tg02KMj60TP1j41Tg00XTj57Tg00MSj54Tg029Gj73Tg00V^l92Tg00Rlj15Tg00SKj46Tg00SlR1g011cR2#9R3f0R4g014k582R5P0P2P5X32R6P0p,8fuzz_oneR7p,4emitR8f3f2R9f1R:E0C1[^02]2R;X11P0P2P6P:P4D7P0P2P6P0P7P8g00TKP9P:E0C1eX45X02X23P0P2P2P5X02R<P6P7P9O1P0g00:6R=P2P8P4O1P0P7P8f6R>f4R?P:E0V=D4X32p,4FUZ0P9O1P<P4O1P0P=P2P6P8P:O1P0P7P8f7f5R<P9E0V=P>P<P9P:O3X7=F3W5X32M92P0P2P6P0P7P8%5?P9P:E0C1eX45X02X23X6;X11P4C6W1o"). Qed.

Lemma target_run_exits : forall cfg payload, mexits S (target_run drv_malloc drv_free fuzz_one emit cfg payload).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["AdapterX"] "p'0h01ai001ah12a0h23cfgh31oi011oh41pi021ph57payloadh61ri031rh72rci045ownedp;1p;2p;3p;5p;6p;4p;8p,2StR0p4p300g00NeR1p6051002p8p,3ptrR2p4p300R3g02LHR4p4p7210p8P3g002nR5p4p7210p8P3g001ZR6p605311001p8P3g00PVR7p605311000p8P3P1p605311001p8P3P1p6054111000p8P3g0100R8p605311000p8P3p1029Gp60521002p8g0069j1ETg00CDR3j1>TP5j25Tg01NFj2@Tg00^Xj2;Tg00G6j1:Tg00FTj27Tg000fj31Tg00MSj52Tg01Ucj14Tg02MDj1?Tg00bSj28Tg01O>j29Tg01P8j1=Tg02KMj6<Tg004Sj1DTP7j40TP1j83TP8j8CTP6j46Tg02Mij3ATP4j8BTg011cR4%E4P0p,1SR6%>2R8#>R1P4g00TjR71501f0R5,@4R9g014kR:';R;%:2,78R<9101R=P0P8P1p,:drv_mallocR>P9O1R?P3P2P1P51725,78%:8n10110300021010200R@9101X68RAD2RBn0100000020000P3P81504RCP5P0P4P4P0p,8fuzz_oneRDp,4emitREg006YRF#4RGf3RH%?F#4RI'8'9#=f2P:E<P0g00:6RJP4P3P2150JRKf1RLp,8drv_freeRMP5O1RNg00UJRO910JRPn10110400021010200RQP7P41;L:P:PGn0100000020000R79104VJRRD2X74RSD2%DF#4RF9104RTn10110000021010400X01P0P6P1P;P=PBP0P6P1P<C0P0P6P8P1P?PAp,3MALP9O1P0P6P1P@C0X08G3GCP3P8P0P6P4P3P8PCP5P0P4P4P0PDPEf4/8I,9G#=RGPHP:E<RIPSD2PTn10110000021010400C6P5P0P6P4P4PIPSAAGH:P0P6PJP4PQPRP3P2P0P6PJP3P2PKP5PNPPn10110400021010200C6PLp,3FREP5O1X42P5O1P0P6PJPOC0n10110100021010200P0P6P4P7C0X1JG3X04G3X38P5O1P0P6P4PFC0n10110100021010100X01G3P0P6P4P0P2P>PMPDPEPLP5GBC6eW5W2o"). Qed.

Lemma target_run_post : forall cfg payload,
  mpost (fun c => c = 0 \/ c = 2) (target_run drv_malloc drv_free fuzz_one emit cfg payload).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["AdapterX"] "p'0h01ai001ah12rch21Hh31ch43cfgh55ownedi015ownedh67payloadh71ri021rh83rc'i031oi041pp;1p;3p;2p;5p;6p;4p;7p;9p;8g0069j1LTg00CDR0j1ATg004Sj1BTg01Ucj18Tg00Ujj33Tg02Nij2JTg002nj24Tg01NFj2DTg00^Xj26Tg00G6j19Tg00FTj25Tg000fj30Tg00MSj51Tg02MDj1KTg00bSj2@Tg01O>j2=Tg01P8j1>Tg02KMj6?Tg0000j42Tg00VDj2<Tg02OCj4ITg02PBj3ETg00XTj5;Tg029Gj7:Tg02P\j6FTg00V^l9GTg02Q:j3HTg02LHj8CTg011cR1f0R2g014kR333p=7%L1p,2StR4p,3ptrR5#AR6#AR7P1%72R8g006YR9#B#8R:9312'JX31R;g00TjR<14471D12R=/63%95,569047P4P6P7p,:drv_mallocR>P=O1P0P5P7P21552,56%96n101102000210104009047X76D1n0100000020000R=P0P61441R?P2P4P1P1P4p,8fuzz_oneR@p,4emitRA%89RBf3RC%K9#8R9'@'=#>f2RDP3E?P4g00:6REP1P0P5144ERFf1RGp,8drv_freeRHP2O1RIg00UJ904ERJn10110100021010400P<P116G3P3PBn01000000200009041VERKD1X11RLD1A041:RMn10110000021010100X07RNP0P6P4P1P;P0P6P?P2P4P1P1P4P@PAf4/@9,=B#>R9PCP3E?R?PLD1PMn10110000021010100C2P2P4P1P1P8X81R8P;P?PLP9PCP31<13R9CIP8P2O1P1P3P4P1P;P4PEP1P0P5PFPCPIPJn10110100021010400PKD1C2X11P4PEP1P;P0P5PFPDPIPJn10110100021010400P<P11633P3PBn0100000020000RB9041VEP4P1P;PB%7BA31B:;E9D;X0EF:PGP2EFW2X11M9GX56P2O1P4P1P;P:%7:A31::1<1:3HD;n10110300021110300X07F:P4P1P;P4P7P1P=PND1C2eP4P1P;P4P5P>PHP@PAPGP2GCC2eW6X41o"). Qed.

Lemma target_alloc_init_exits : forall b, mexits S (target_alloc_init (St:=St) b).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["AdapterX"] "h01bp;4g00PVj40Tg011cp,2Stp,1Sg00:6g00UJC0W0o"). Qed.
Lemma target_alloc_count_exits : mexits S (target_alloc_count (St:=St)).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["AdapterX"] "p;4g00PVj40Tp,2Stp,1Sg011cg014kC0o"). Qed.
Lemma target_alloc_count_post : mpost (fun n => n = 0) (target_alloc_count (St:=St)).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["AdapterX"] "h01np;3p;2p;5g00Ujj32Tg00VDj21Tg00XTj50Tp,2Stg011cR0f0g014kR1520X00P11101D0o"). Qed.
End AdapterX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DriverX.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> Monad.M St unit.
Variable run : Z -> list Z -> Monad.M St Z.
Variable alloc_count : Monad.M St Z.
Variable S : list word.
Hypothesis DIAG : forall d, mexits S (io_diag io d).
Hypothesis EMIT : forall v, mexits S (io_emit io v).
Hypothesis EXIT : mexits S (io_exit io).
Hypothesis MAL : forall n, mexits S (drv_malloc n).
Hypothesis FRE : forall p, mexits S (drv_free p).
Hypothesis AINIT : forall b, mexits S (alloc_init b).
Hypothesis RUN : forall c p, mexits S (run c p).
Hypothesis CNT : mexits S alloc_count.
Hypothesis RUN02 : forall c p, mpost (fun x => x = 0 \/ x = 2) (run c p).
Hypothesis CNT0 : mpost (fun n => n = 0) alloc_count.

Lemma read_loop_body_exits : forall fd path st, mexits S (read_loop_body io drv_malloc drv_free read_stage fd path st).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["DriverX"] "p'0h01ai001ah12bsi012bsh21ei021eh32fdh41gi031gh52nbi042nbh61pi051ph74pathh81ri061rh92sti073nb'i081oi093st1p;1p;2p;3p;4p;5p;8p;6p;9p,2StR0p4p300R1g00NeR2p6051002p8P1g002nR3p4p710p8P1g02QTR4p4p710p8P1g02RLR5p4p710p8P1p100;PR6p4p741110p8P1P6p4p7511110p8p,3ptrR6p4p300R1P3p4p7210p8P1g001ZR7p605311001p8P1g02SKR8p4p710p8P1P2p605311001p8g0069j1NTP8j1\Tg00CDR8j1ETg027Nj1VTg00RMj2[TP3j2MTg02TCj29Tg01NFj2<Tg02U>j27Tg00^Xj2XTg02V5j2UTP4j35Tg00G6j1OTg000fj30Tg004Sj1:Tg01Ucj1LTg02VRj2>Tg02Voj2KTg02Wfj48Tg00FTj2=Tg00MSj56Tg01e?j2JTg01O[j2ITg02X^j3FTg02YSj2GTg00BPj4HTg02ZKj1@Tg02[Fj1WTg02\Bj3?Tg0058j1TTg005Vj1STg02\aj2RTg02]Aj2PTg02]aj3CTg02^]j1QTg01gVj3BTg02_Zj3DTg00PVj44TP2j81TP7j4;Tg0100j8ATg00lBj6ZTP5l9YTf3R5g00:6R7f2R2f1R4f0R3D6p=3%:3#:p=2g011cR1%N1%\6R9P0p,1SR:%E9R;%V6R<,[9R=g00TjR>1M0;R?1963,<11763R@'XRAP>P?g02`9/U@RBP0P;p,2ioRCg02a3RD550RE%O9RF900;V7RGC3RHP0%E6RIP;p,:drv_mallocRJg006Y#:RK#LRL,>@RMO1RNP8P6P?P3P0P;p,8drv_freeRO1K62RPO1P6P41765RQ/>L1965RRC8,=9900;V7C3P0P;g02anRS950CRTPGC3RUn10110400021010700X5IRVD6RWn0100000020000RX1=93RY900;RZn0100000020000P8P91M0=R[P3P0g02biR\P=P0P\f4R]p,:read_stageR^P>P1%2KRK#:#2#2#2#2#2#2#LR_1962R`,<1,J@Ra'IP_Pan0100000020000Ra3F1G^aCHP\P[P3P0P=f5Ra#@950C%W69?9<Rb900=RcV7RdC3P>P[%TK#SRK/R3g00TK'PReAC6P`9?9<900=P6PP1762%Q3RP9B1`C89D9<900=n0100000020000R`n0110000021010210101X0\D6Pcn10110300021110900X4;P0P:P;PAPXPZP0P:P;PBPHPWP0P:P7P;PEPGp,4DIAGREPDO1P0P:P;PFC4X07RFG1P0P:PIP;PNPVp,3MALPMO1P8P6P0P:P;P8P6P?P3P0P;PO1K65R5O1R?P6P4176]/>L196]C8,=9R]900;V7RLC3PUn10110400021010700C;P3P0P:P7P;P?PLp,3FREP5O1P0P:P;P]C4X07G1X66P3O1P0P:P7P;PTPGPEPSO1PFG1n10110800021010500X0IG1GAP0P:P;PYC4GAP8P9P0P:P=P8P9P[P3P0P\P=P0P\P>P11<1R,J@R@,I_P_P@n0100000020000R@9Fa^Ra1G^@R@CHR_P\P[P3P0P=f6#@950CPdC3P`n0110000021010210101X0\R`D6Pcn10110300021110900C;P3P0P:P\P=P_P`P0P:P\PaP@g007>EZP\P0P:P=P\P[P3P0P=f7#@R@950CRaPdC3P>P[PeAC65R9?9<R[900=R>P6P5PQAB1RPC89D9<R<900=RPn0100000020000n0110000021010210101C;P3P0P:P7P=PaPdPEP@O1P0P:P=PbC4RbX07G1X21P3O1%NKP0P:P=PeP>PPP0P:P=P[C4P0P:P=P<C4GAW1P3O1n0110600021010210101X0\G1X89P3O1Pbn10110801021110600X0;G1P0P:P=P0P6PCPJPOP^P2P4P3M9YC;eW9W7W3o"). Qed.

Lemma read_all_exits : forall path, mexits S (read_all io drv_malloc drv_free read_stage path).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["DriverX"] "p'0h01ah11bi001bh23resi013resh33bufi023bufh47contenti037contenth51ei041eh61pi051ph74pathh81ri061rh91vi071vh:1xi084buf'i092fdi0:1oi0;1sp;1p;4p;2p;3p;5p;8p;6p;7g0069j1PTg027NR0j1OTg004Sj15Tg0058j1NTg005Vj1KTg02ccj1GTg01IOj4CTg02dIj1BTg00BPj4=Tg002nj2@Tg02e>j1:Tg02QTj37Tg02[Fj1MTg000fj3>Tg00MSj50Tg00CDR1j1JTg01Ucj1ITg02SKj1HTg02RLj89Tg00fEj1FTg02Wfj4DTg00Oaj68Tg02f9j16Tg02]aj3ETg00lBj6;Tg001Zj44Tg00PVj4<Tg00Nej82Tg02fnj3ATg028Jj8?Tg02h3j7LTf0R2#5#5p=1f1R3g01aXR4P2g02hlR5C=p=3g011cR6#PR7p,2StR8p,1SR9P4p,3ptrR:#OR;P8P4P6g006Y#5#1R<#NR=#K%G=P2CC#BR=g02ieR>C=P41@8;R?P2P8g00:6R@P;p,2ioRAf2RB#:578%M:RC9>8;RDV@RED0P8%J:RFP;p,:drv_mallocRG%5<#1#1#1#1#1#1#IR<O1RHP1P:P?P2P8P;P;P8%H:RIP;g02j]RJP8P:PAPGp,8drv_freeRKp,:read_stageRLPBf4RMG9P:P2P<%F6CDRNE8P0P:P?P2PDP8P4P;f5RO#6,38AE:B3RP9>8;V4RQD0n10110100020020108103X2;RRD0P8P@P;g02anRS978ARTPED0RUn10110000021010200X1FD0n0110600021010410109X84P8P9P4P=P>g007>R>E;P4P8P9P;P4P?P2P8P@P;f3R=#:RV978ARWPED0P8PFP;PHP1P:P?P2P8P;P;P8PIP;PJP8P:PAPGPKPLPBPOG9PNE8PRD0PUn10110000021010200X1FRRD0n0110600021010410109C4P2P8P9P@P;PWPEp,4DIAGRWPVO1P8P9P;PCC<RCX0@RVG2X56P2O1P8P9PFP;PHPRp,3MALP<O1P1P:P8P9P;P1P:P?P2P8P;P;P8PIP;PJP8P:PAPGPKPLP=f6R=G9R1PNE8R<P0P:P?P2PDP8P4P;%6=,38PQD0n10110100020020108103X2;R=D0PUn10110000021010200C4P2P8P9P;P;P<P=P8P9PIP;P1f7R1=AM2X:IPJPNG?P0P:P8P9P;P0P:P?P2PDP8P4P;%61,38PQD0n10110100020020108103C4P2PCP8P9P4P;f8#6RC,38PQP8P9P4PCP5P>E;P8P9P;PPC<X04G2X47X3:P3P2O2n10110600020020102103X0;G2X6:P2O1P8P9P@P;PTPEPWPSO1PVG2n10110:00021110500X0FG2X96P2O1n0110;00021010411107X04G2P8P9P;P8P:PAPGPKPLP2FLC4eW7o"). Qed.

Lemma main_model_exits : forall argv, mexits S (main_model io drv_malloc drv_free read_stage alloc_init run alloc_count argv).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["DriverX"] "p'0h01ah12a0h22a1h32a2h44argvh53bufi003bufh67contenti017contenth71nh82rai022rah96statush:7status'i03<count_allocsi041rp;1p;2p;4p;3p;7p;5p;8p;:g0069j1FTg02\aj2VTg02kWj1NTg004Sj1BTg01Ucj18Tg00^Xj2RTg00c1j1OTg00fEj1MTg02l7j4ATg02lSj1JTg02QTj39Tg000fj33Tg027NR0j1UTg00Rlj1TTg02h3j7STg002nj2QTg01NFj2PTg01O[j25Tg02mNj1<Tg02MDj16Tg00bSj2ETg01O>j2>Tg01P8j1DTg01g8j3CTg02nCj1LTg02o8j2KTg02omj2ITg00MSj5;Tg00PVj44Tg030Nj1HTg001Zj4@Tg0100j87Tg00Nej8?Tg031Ml:GTf2R1g00:6R2g011cR3f1R4f0R5D;p=0%65#6p=2P1P3P3P4P5D;p=:f5R6f4R7P2P3f3R8P1P4P5G?p=1P6P7P3P3P8P1P4P5G?p==%F3R8#Fp,2StR6p,1SR9P31V85#Ng006YR:#B#8R;'R#Op,2ioR<P8g00TKR=P5%M3R>CA#JR?596R@A363;RAV2RB506P6p,3ptrRC#URDP3P6PCP<p,:drv_mallocREp,8drv_freeRFp,:read_stageRGP8%T=P5P>CAR>FSR=P0PC1Q63RHP5PAg00TjRAPH1P35RIg032HRJ'5RKg033@RL996<RMPFP1O1RN=06BV2RO506RPPAPH%<5%6:R:#2RQ#6#2#2#2#2#2#8RR'ERS,>J,5IRIg034;RJ996<RT=06ORUp,:alloc_initRV1>;S#D=C35#LRSO1RWp,3runRXPAP3g014kRY%<4/ERRR'51K4;PYn0100000020000RY%B:#8/>R#D=C34RRO2R:PAPH%<1%8Q'IRQp,;alloc_countRHPAP3g0356RA,55P5PAn0100000020000RA9363X73RZ5:6R[A3635R\n0110300020000R]PFP7O1R^A3634V2R_506X:3R`5:6X93Ra5:6V2Rb506Rcn0100000020000Rdn0100000020001n10110200020021100101ReX8DRfD;P6P9P@PBp,4DIAGR@P?O1P6P9P3P;C4R;X02E1P6P9PDP3P=Pf%H>P0PCP6P9P3PeC@P5P;P6P9P3PKPPPdP6P9PMPOP@PLO1P6P9PNPBp,3FRERBP1O1P;X12E1X02R;E1P6P9P3PIPUPcP6P9PTPOP@PJO1P;E1P6P9PWPbp,5AINITPSO1P6P9P:Pap,3RUNPYPRO2P6P9P]P`P6P9P3PQP[P\P6P9PHPZp,3CNTP6P9P3PAC4X23E=P6P9P3P5C4G7P6P9P^P_PBP7O1P6P9P3P4C4X32E1X23E=X13E=X02E1G7G7X68X5CP4P5O2n10110401020021100101X0DG?G7P6P9P3P6PCP<PEPFPGPVPXPHP5M:GC@eW4o"). Qed.

Lemma main_model_post : forall argv,
  mpost (fun c => c = 0 \/ c = 2) (main_model io drv_malloc drv_free read_stage alloc_init run alloc_count argv).
Proof.
Local Ltac caseb := lazymatch goal with |- mpost _ (if ?b then _ else _) => destruct b end.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["DriverX"] "p'0h01ah11bi001bh21nh36statush47status'h52_Hh61Hh73Hsth84Hst'h92a0h:4argvh;3bufi013bufh<1ch=7contenti027contenth>2rai032rah?2s'h@3st'hA1xi04<count_allocsi051rp;1p;2p;3p;4p;7p;5p;6p;:p;9g0069j1MTg02\aj2_Tg02kWj1TTg004Sj1JTg01Ucj1?Tg00^Xj2XTg00c1j1UTg00Ujj39Tg02Nij2KTg002nj2STg00fEj1RTg02l7j4>Tg02lSj1OTg02QTj3@Tg027NR0j1WTg00Rlj1VTg02h3j7LTg01NFj2FTg01O[j22Tg02mNj1:Tg02MDj1=Tg00bSj2<Tg01O>j21Tg01P8j16Tg02nCj1CTg02o8j2ETg02omj2BTg00MSj5HTg00VDj2ITg02Q:j3QTg00XTj5ATg02PBj3PTg02P\j6^Tg029Gj7NTg031Ml:]Tg000fj3\Tg01g8j3[Tg0000j4YTg00V^l9ZTg011cR1f0R2g014kR339p=Df1R4?\12p=;f2R5g00:6R6P1P4P2DHp=0%=2#=p=7A[142p=8P5P1P1P4P2DHp=4P5P1P4P2CYp=3f4R7P6P1f3R8P5P4P2FNp=5f6R9P1P1f5R:P7P8P5P4P2M9Zp=G%M1R;#M1_;2#Tg006YR<#J#?R='X#Ug00TjR>P>p,2StR?%D2R@A912='KRAX<1RBP>1S?1RCP2p,2ioRDP;g00TKREP5%R1RFC>#O5@?1;?=RGV6RH50?P?p,3ptrRI#WRJP1P?PIPDp,:drv_mallocRKp,8drv_freeRLp,:read_stageRMP;%VERNP5PFC>FLP0PIPCP2PGP>PC1F12RGg032HRO'2RPg033@9@?DRQPLP5O1=0?HV6RR50?P>PC%:2%=<R<#7RS#=#7#7#7#7#7#?RT'<RU,1O,2Gg034;9@?DRG=0?Rp,:alloc_initRR11=U#6/82#CO1p,3runRUP>P1%:4/<TRV,231E4=P3n0100000020000%J<#?R</1V#6/84O2P>PC%:5RW%?SRS'Bp,;alloc_countRXP>P1g0356RY,22P2PYn0100000020000,;?RZX21R[54?R\1;?2R]n0110400020000PLP7O1R^1;?4R_V6R`50?X4154?X3154?V650?n0100000020000n0100000020001Ran10110300020021101102RbX>JRcDHn010000002000133P2P?PBP;PEP4PFC>#O9@?DPHP?P1PBP=%D=A91==1I1=3QDAREX06D5P?PJP1PBP?PIPDPKPLPMP;PNP4PFC>FLPcP0PIA3?BbP2PEPPP>P>P>PCP2A0?^HV6RP90?QP>PC1F151<WTRW,1O'2A0?GPPR11=W#6/85#CO1RWPUP>P1%:8/<TRb,231E8=P3n0100000020000R011<b#6/88RcO2RFP>PC%:7RN/BSP\P]n0110400020000PLP9O1=0?`X4154?X31R954?V6Rd50?n0100000020000n010000002000193?BP2P?PBPQPLP8O1RQ=0?HV6P?PBPQPHPEX96RED5X06D51F1411OV'2P>P>P>PCP2PLP:O1=0?HV690?GPR11=b#6/88#CO1PUP>P11<NTRN,231E7=P3n010000002000011<N#6/87O2P>PC%::/BSRSP\P]n0110400020000PLf7O1=0?`X41R`54?X3154?V650?n010000002000093?BP2P?PBPGPPP?PBP^PHPED5X06D5P?PBPWPdP?PAXA1RdPBPFP9p,5RUN02P0PcO2PdP2O1P?PAX?1RdPBP>PCPSP\P_n0110400020000P`PSP>P>P>PCP2P\1;?8n011040002000093?dP2P?P@X21R@PdPXP[p,4CNT0P@P2O1P1P3A3?dZX21P?P1PdP>P1123YP3PYn0100000020000RYA9133A913=1I133P%DYA91Y='KeDAP4P2E^W6X21FGP?P1PdP5P4DAn0110000020000b1P?PBPLf8O11;?5V6P?P1PBP5P4DAX56D5X8AX@1FGW7X31FGX56D5n0110000020001b1n0110001020001b1A3?BaeX=;X;IP4P2O2n10110501020021101102X0JFNn0110001020001b1P?PIPDPKPLPMPRPUPXP2M:]93?BeW:o"). Qed.

(* [comment removed for export] *)
Lemma exit_model_exits : forall code,
  In (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) S -> mexits S (exit_model io code).
Proof.
ltac2:(KReplay.run1 (kr_t_MExits ()) ["DriverX"] "p'0h01ri001rh11Hh21ai011ah31ch44codeh52moh63mo'h73Hinh82_Hh91si021sh:2s'h;1ui031ui041ei051pp;1p;2p;3p;6p;4p;9p;5g004Sj12Tg0058j1MTg005Vj1CTg02ccj23Tg02MDj10Tg01Ucj1KTg0360j34Tg036Uj38Tg00CfR0j2:Tg00DFR1j1;Tg036lj3?Tg00E>j2>Tg00IFj1=Tg00HPj3LTg037dj19Tg00NHj3<Tg00Ujj31Tg038Yj27Tg039SR2j2ITg02P\j6HTg039nj4BTg00F4j4DTg00;Pl9ETg03:Ij4Aj3FTg001Zj4GTg00BPj5@Tg00:Vj5JTf2R3g03;DR4f1R5g03;if0R6D@p=5g00J>R7g00L_R8P3P5P6DJp=6g011cg006YR9#2#2#2#2#2#2#MR:#CR;13:6%09#0#0#0#0#0#0#K,3:R954:p,1SR<38p,2StR=P7P8P<g00:6R8/:=R>#;R?1:4=R@#;RAp,2ioRB=?=6P1P>1>7ARCP6%=@9L7AR7f4R@#9A<8=6RD55=n10110000020010101X0?p,4EXITP6O1P1P>P1P>PCP6P7f5R7#9=5=Dn1011000002001010196<AP6g007>RCP0P8P=f6R0#9=5=D96<AP6g03<aRDf<,3:=4:991;5175391D6'IR1A8;3<[^6D^4;]5g00K3REg00Kf]0P2f=,3:=4:991;3f3R2,7391D5A8;2<P6f?,3:=4:991;@P;f@R2,3:=4:9R9f7,7691D7A8;5<[X3;179091D@P2W8P7P6EHW1P5P6O2n2001000000121000000X11X6DX3;X5DPCX0ECBf9#9P8P=P5P6CD9<8=55=96<AeX:=X;8P5P6O2n2001105000121103102X2>P6O1n10110400020011101X2?M9EP=PBP3P6CA96<AeW9P=P<P4AF=B5CGeW7W4o"). Qed.
End DriverX.
