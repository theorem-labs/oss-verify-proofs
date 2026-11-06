(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Km_kit KmF_kit Pm_iface Pm_iface2 Pm_iface4 PmF_kit Cf_iface Cf_kit Lept_objkit RT_fk D_kit Bi_iface Bi_fktw Bi_iface2 Bi_iface3 Bi_bexact_kit Bi_bexact_kit2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_bexact_kit3 () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53B02=Bi_bexact_kit4OPTXC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List2InC69OSSVerify5KrLib2K53B02:Lept_iface6p_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:Lept_iface5rsizeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53B02>Bi_bexact_kit27optx_inC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2K53B02>Bi_bexact_kit22vwC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K53B02:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K69OSSVerify5KrLib2K53B02:Lept_iface5cmapv01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:Lept_iface7pix_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:Lept_iface6p_cmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;Lept_objkit:keeps_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027PmF_kit:pix_chunksC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib2K53B02:Lept_iface5c_arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:Lept_iface8c_nallocC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53B026Cf_kit>keeps_live_subC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib2K53B027PmF_kit<pix_obj_moveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma optx_in_vw : forall p u d (X L : list (Z * Z)), p <> 0 ->
  In (p, 64) (X ++ OPTX p u ++ L) /\ In (p_data (vw p u d), rsize (vw p u d)) (X ++ OPTX p u ++ L).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bexact_kit3 ()) [] "h01Hh11xh21yh31Lh42PNh51Xh61bh71dh81ph91up;2p;1p;3p;4p;5p;6g0000j2DTg000Pj1CTg0010j32Tg001Jj17Tg001cj21Tg002@j2>Tg002aj4=Tg003=j10Tg003bj1<Tg004@j28Tg005>j35Tg005[j33Tg0062j1;Tg006oj1:Tg007kR0j29Tg008Fj5BTg009Hj6ATg009dj3?Tg00:aj4@Tg00;AR1f0R2g00;aR332p=6g00<AR4P4f1R5P2C@p=4g00<_R61D44R7#CR8f4R9g00=\R:524#7P1f5R;/1:R<P3P01152#6f2R0=245#7R=[A2452#71105#6[R>f3R?/10#6\=1>52P2n2001000000120000000X24X14P>^24^14P2f6R>P:P5O3b0C=A213<P1P3f7R3g00>:#0#0#0#0#0#0#<R<'4183>=57?9579R3537P1P6P2P;P>n0100000020000R=#;%:='4=373'9X61P>P;P?P0P5DB11>:P2EAb014;<18;9=5759570R0537A?;9?R?#;%:?'4=370'9eW4X38W5X76W9X84o"). Qed.

Lemma pix_obj8_move : forall L L' (m m' : mem) p v, pix_obj L m p v (mkCmapv 0 0 0 0) -> p_cmap v = 0 -> p_data v <> 0 ->
  In (p, 64) L' -> In (p_data v, rsize v) L' -> keeps_live L' m m' -> pix_obj L' m' p v (mkCmapv 0 0 0 0).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_bexact_kit3 ()) [] "h01Hh11eh22Heh31xh41yh52CMh62DNh72I1h82I2h91Kh:1Lh;2L'h<2POh=1Xh>1bh?1mh@2m'hA1phB1vhC1zp;2p;1p;4p;5p;3p;6p;;g0000j2VTg000Pj1UTg003=j13Tg00>_j1BTg00?=j1ETg00?`j1TTg00@Bj4PTg00A@j5NTg00B>j1;Tg0062j12Tg001Jj1=Tg003bj1ATg005[j30Tg00C;j3DTg00D=j3STg001cj25Tg00E;j1OTg006oj1>Tg00E[j1MTg00F@j1LTg00G<j1KTg00H;j2JTg005>j3:Tg00HXj36Tg009Hj69Tg00:aj4<Tg0010j31Tg002@j2ITg002aj4HTg00I8j6GTg00IVR0j2CTg00J0j6QTg00K1j2FTg00KPl;RTg00<AR1f0R2g00=\R331p=?P1P1f1R4P2C<p=7P1P1P4%>2C<p=8f3R5P1P1f2R6P4C<;62p=4g00;AR7g00;aR8712p=@1V11R9#UR:g00>:R;#3#3R<#3R=#3#3#3R>#B#E%B=#E#T[R=g00<_f5R?P5P4P2P3P3P3P3CPR@DN%;4#?%26#?#=f4RA%A>R>'7f7RB509%2A/8Af8RC509f9RD?DCBf;REf:RFPDPCPBf6RGP@P?ASCB@9092P1%;C17F>RHP7P:%2DRI/53RJ%O9RKP9PI%>DPKC4n0100000020000P7P:1523PKP9P2%M;#3#3#3#AR;P9%L@%A<%K@'JPKC4R@C4n01000000200005:95699096XC1P2P3PGE917D>R<P7P:%2CRI/53PKP9PI%>CPKC4n0100000020000P7P:1533PKP1P1P3P;C<=69@n01000000200005:95699094P7PJP8g007k1542#@A1164#=R@[A1142#=1564#@[RI1556#@\@1I42P2n2001000000120000000X41X31PI^41^31P2%2FRIP3PBO3b0CHA178JP715I3f<R3/7>RJP7P:P2PK%2E/8ER@=69Kn0100000020000=:9K569909AX>7P4P8P2EG17E>REP9PI%>FPKC4=:9K5699095P0A19JAA19@Ag00LPR@'Cf@909?P2f=RJ/7>=19?P9f>RI/7>fBR89092X19PDPGP2E9W0P2O1%23/83=19?/C@P0%2J/8J=19GP@A09B8P2%2I/8I=19BP9f?RI#2/8IfDR89092X19PFPCP2E9W0P2O1P@A09D8P2n010000000X0@P2O1n200100000021000010000W0P2O1n200100000021000010000b2b0b2W2X19PFP9PBP>PKC4PDPCP2P9PCP>PKC49092P0A19<4A094KA096JP2A19H6P9PEA092IX19PGP5P2E9W0P2O1A096KP@A09AIP2n010000000W0P2O1n200100000021000010000W0X19EQ%;G#?#=P9%;BP;PKC4?DFDP2P?O1'FW=M;RW9W8W7W6W5W<WBXA1X@=W?X;:W:o"). Qed.

(* [comment removed for export] *)
Definition ohid (P : Prop) : Prop := P.
Ltac hide_opts :=
  repeat match goal with
  | H : optpix8 _ _ _ _ |- _ => let T := type of H in change (ohid T) in H
  | H : ?p <> 0 -> _ |- _ => let T := type of H in change (ohid T) in H
  end.
