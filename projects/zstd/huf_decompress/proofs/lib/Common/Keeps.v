(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio Driver PState.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Keeps () := "c59OSSVerify5KrLib6Common5Keeps4tallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9tall_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps:tall_ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps5keepsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps:keeps_bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9keeps_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9keeps_unrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec5Monad5mwhenC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib6Common5Keeps9impl_tallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree?impl_epost_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio@stdio_write_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9keeps_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6upd_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState9set_so_psC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9keeps_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio5rd_soC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib5Lists7ListDef3mapK59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9iov_totalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode:dec_writevC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec5Stdio;iov_advanceC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps9keeps_sysC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps8keeps_ifC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib4Spec5Stdio;stdio_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5KeepsBstdio_write_loop_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9WRITE_MAXC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec5Stdio6so_bufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9so_lbf_nlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio8so_firstC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5Stdio9stdout_st01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioBstdout_stdio_writeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps7rd_so_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps8upd_so_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps=stdio_write_kC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec5Stdio9so_activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_writefnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5KeepsDstdout_stdio_write_kC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib3Lib6Decode4sret00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:TIOCGWINSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode9dec_ioctlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_towriteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec5Stdio=after_last_nlC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec5Stdio>stdout_fwritexC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps@stdout_writefn_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps@stdout_towrite_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio=STDOUT_BUFSIZC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4Spec5Stdio:out_piecesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps@stdout_fwritex_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>stdout_vprintfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps<out_pieces_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver6s_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio<pieces_pct_dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps@stdout_vprintf_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioAstdout_exit_flushC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps7ps_heapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5Keeps8s_emit_kC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tall {R} (P : R -> Prop) (t : itree node (exc R)) : Prop :=
  match t with
  | Ret Unr => True
  | Ret (Ok r) => P r
  | Vis _ k => forall rsp, tall P (k rsp)
  end.

Lemma tall_mono : forall {R} (P P' : R -> Prop) t, tall P t -> (forall r, P r -> P' r) -> tall P' t.
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) [] "p'0h01rh11Hh22HPh33rsph41th52IHh61Ph72P'h81Rh91kh:1nh;2r0i001ai011ep;1p;2p;3p;4p;6p200R0g0000R1p4p710p8P0g000fR2p4p7210p8g001^R3j11Tg002Vj23TP1j30Tg003Lj16Tg004Dj25Tg005<j44TP2j68Tg0062j37Tg006hR2f1R1f0R437p=2p-0R5\4P5\1f2R5#1,32P2f3R6#1R71327f4R8?064f5R9P9P4O1R:P9P1O1[]0R;f6R<?085[[W4P3P8%19R3/249098P<P4O1P<P1O1[^0<f7R=%1=/25709[[P4g007]g0089X2;W1%18%68'29086%1<R>%6<'290<8\;[eP=P4O1P=P1O1[^0=R;P4P5P1O2W2X1:15<4,2>90<9f8R:%1:R?15:5'270<\;[eX09P4O1n10110100020010100X;7g008UR71323[P1P4O190<9P6P5O190:<\;[\7P5P4O1R390=<^37P6P4P3P1O3X37X2;W1P2P>P5P1C490<9P2P?P8P6C490:<\;[eW5W9X:2P4E8W4W7W6X80o"). Qed.

Lemma tall_ebind : forall {A B} (P : A -> Prop) (Q : B -> Prop) (t : itree node (exc A)) (f : A -> itree node (exc B)),
  tall P t -> (forall a, P a -> tall Q (f a)) -> tall Q (ebind t f).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) [] "p'0h01fh11ai001ah21Hh32HFh43rsph51th61Ah71Bh82IHh91Ph:1Qh;1kh<1nh=1ri011ep;1p;2p;3p;4p;6p;5p200R0g0000R1p4p710R2p8P0g000fR3p4p7210p8P0g009HR4p4p7210p8p201R5P2p8P5P4p4p73110p8g001^R2j11Tg002Vj24TP1j30Tg003Lj17Tg004Dj26Tg005<j45TP3j6:TP4j59Tg0062j38Tg006hR4f3R3f2R1f1R6f0R7D9p=2A8467p=3p-0\6R8%13,44P4f4R9#1R:144:f5R;%1;,44[R<f6R=?096f7R>P=P7O1f8R?P3P6O1R@70=[]1RAP?P>P3P1C290>;[[]0W5P2P;%1=R2,44RB\=%1>RC/3690>;P>P7O1f9RD?0>@[^1?PDP?%1D/33P1C290?=[[]0P7g007]g0089X3AW2X0<%7=,3290=9P?P>%1?R2%7?'3P1C290>;\A[^0<e144C\>RCP=P6O1P?P7O1f:R<?0?@[^1DR@P7P3P6O2W3W2W016?6,3290?=P<PD%1<RA16<3'3P1C290D>\@[^0CeX1=P7O1n10110100020010100X=:g008UR:PB[P1P6O190?=P<PDP9P3O1P1C290D>\@[^0C\:P3P7O190D>^4:P9P7P3P1P7O1P6O4X4:X3@W2X0CP4P2P3P1C590?=P<PDP4PAP;P9C5P1C290D>\@[^0CeW8W;X<4P7E:W5X:8W9X75X60o"). Qed.

(* [comment removed for export] *)
Lemma impl_tall : forall segs {R} (t : itree node (exc R)) (P : R -> Prop) (Q : R -> machine_state -> Prop) ms,
  impl segs (at_node segs) t (epost Q) ms -> tall P t ->
  impl segs (at_node segs) t (epost (fun r ms' => Q r ms' /\ P r)) ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) [] "p'0h03rsph11Ph21Qh32msh41rh53ms'h63ms1h71Hh82HPh91th:2H0h;2HQh<3Hath=2Hkh>2IHh?1Rh@1khA1nhB2r0hC4segsi001ai011ep;1p;2p;3p;4p;6p;7p200R0g0000R1p4p710p8P0g000fR2p4p7210p8P0g00:<R3p4p741110p8P0g00:oR4p4p710p8g00;cj1FTg001^R5j10Tg002Vj2>Tg00<Cj12j37TP4j28j3;j4BTP1j36Tg00=9R1j24Tg003Lj1=Tg00=Tj3<Tg004Dj2:Tg00>Ej4CTg00>`j6ATg00?Vj29Tg005<j4?TP2j6ETP3j7@Tg0062j3DTg006hR3f5R2f4R4f3R6f2R7f1R8f0R9F@p=1AD389p=3P3f6R:P2P4P61878P9F@p=5g00@I#F%09,>3P3%08R;1>3;p-0R<\7R=g00AHR>P<[R?\6R@P:%2:RA%02RBP61828RCP9E1A6:64f8RD%2DREf7RF#0RGP2P2P8P9O2P:P8O1'4X5>RHX4F,8FRIP7E1[[^3>]2]1W9P5P7P<\6P?\4PF%2F%0:R51356P:P8P9F513G496F6f9RJ%2J%0DRK13K2PDPHX4DP7F5[[^3>]2]1P9%=2RL9;28=<:9g007]P8W8W7X3>X2@X1=P:PAPB13BLPCP9E1%=:,3596:6PDPEPG%=F,3GPIP7E1[[^3>^2@^1=eP<\4R<P?\2R?1:F6R=9;F8=<D9P6P4O1f:R@1:J2RI9;J6PHX4JRH=;JIP7P8P4P:P9O2P2PFP8O2P:PFO1P9P7CCW;X5>P@P41:@:P9CBf;R5PFP8P9O2PDP8O1'4X5>X45RC1:5FP8CB[^5>eEAW8W7X3>W2W1PDPEPG13G=18F8R=P9E11:D4,3K96D6P@%2@RL%0JRB13BI18JHRHP7E1[[^3>^2?^1<eX46P9O1n10110100020010100XB;g008UR;%06,>3[PDPEPGP4P6O1P=P9E1P2P4O196D6P@PLPBP:P2O1PHP7E1[[^3>^2?^1<\;A7J:9P@PLPBP:P9O1RIPJP61989RAF5^0;'4X6>=<D9A6J4I^0;P@A75D9RIf<RM%2MRN%05ROPDP9O1RPP5P2PAF5^0;'4X6>PMPNPOPPP5PCPAF5^0;,4IX6>P7P8A7MJ9f=RI%2IRC%0MRPPJP9O1RO18M:RNPAE1^0;'4X6>P9O1P1A7MJ8PIPCPPPOPN1979E1^0;A7I@7f>RN%2N%0IP@P9O1PIPJP8P9O2P@P8O1'4X5>X4I1969F5^0;'4P9A7N56f@RN%2Nf?RO#0PMP9O1POPJ1929F5^0;A7NI2fARJ%2J%0NPIP9O1PNPMP8P9O2PIP8O1'4X5>X4N19:9RNF5^0;P8PMP9P5P@PNP8P9O1PFP9O1O6X0;CCW=W<P8P9O2n2001000000120000000W:X6>EAW8W7X3>X2?X1<PDPEPGP3PGP2P4C?P=P9E1P3PKP:P2C?96D6P@PLPBP3PBPFP:C?PHP7E1[[^3>^2?^1<eW>W@XA3P9EEW9X?0WCo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Keeps.
  Context {St B : Type} (f : St -> B).
  Local Notation M := (@Monad.M St).

  Definition keeps {A} (c : M A) : Prop := forall s : St, tall (fun p => f (snd p) = f s) (c s).

  Lemma keeps_ret : forall {A} (a : A), keeps (mret a).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["Keeps"] "h01Ah11ah21sp;2p;3p,2StR0p4p300R1g00BOR2p4p710p8P1p10000p6051002R3p8P1p100CCp6051002p8P1p100D>R4p6051003p8P1P4p60521002p8P1p100E:p4p7210p8P1g00EoR4p6054111001R5p8P1p100FfR1p4p7210p8p,1BR6p4p300p100GCp4p710p8P5P3p8P5p100Gap4p7210p8P5P1p4p710p8p200R1P2p4p7210p8P1P5p8g00HRj22TP2j31TP4j20Tf0R4p,1fP4O1,26X20f1R6A1064'0eW1X01o"). Qed.
  Lemma keeps_unr : forall {A}, keeps (munr (A:=A)).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["Keeps"] "h01Ah11sp;2p200R0g00HlR1p4p7210p8P0g00EoR2p6054111001p8P1j21TP2j20Tp,2StR2g0089W1f0R11121'0eX00o"). Qed.
  Lemma keeps_get : keeps mget.
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["Keeps"] "h01sp;2p;1g00HRj22Tg00I`j11Tg00Eoj20Tp,2StR0p,1Bp,1ff0O1'2W0%10,00eo"). Qed.
  Lemma keeps_upd : forall g, (forall s, f (g s) = f s) -> keeps (mupd g).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["Keeps"] "h01sh12Hgh21gh31ph41xp;3p;2g00JTj30Tg00Jnj26Tg00KNj32Tg00Kkj31j24Tg0000j35Tg00Eoj23Tp,2StR0P0]4p,1BR1p,1fR2f1R3f0R4O1R5O1P2P4O130^00P5g00L_R5/60R6P2A2504O1P2P3O1501X36f2=10435eX001403,35eW1W2o"). Qed.
  Lemma keeps_sys : forall {A} n (dec : resp -> option A), keeps (msys n dec).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["Keeps"] "p'0h01ph11Ah21ai001ah33dech41nh51oi011oh63rsph71si021xp;1p;2p;3p;4p;5p200R0g00EoR1p6054111001p8P0g00M?R2p4p7210p8g00N3R3j15Tg00Jnj22Tg00KNj30Tg00JTj31Tg001^j16Tg002Vj2<Tg00NUj4;Tg00O5j2:Tg00OWj19Tg004Dj28Tg0062j33Tg003Lj17Tg0000j34Tg00HRj2@TP2j5?j4>TP1j2=Tg006hR1g008UR2f2R4#5[p,2StR5P4f0R6O1f4R7#5P3f5R8f6R9/25R:p,1BR;p,1fR<f7R=?056O1P<P7O1R>31X0:P3P:12=5R?#6R@,<1P3P9%5?P6P=P5P6P7C;R=,:?%9:n1011020002101000018?6931@%6:%7:531n1011020002101000034P61@;>P<f8?056O1P<P8O151;X0?18?=931@54?eX29P6O1g00891285R8P<A0956O1P<f3R9O151;X08%68%7853134en10110100021010000b5X621295R2P<A0756O1P<f1R<O151;X02P5P9P4P<P6D?34eW7P5P4P<P6C>,=4eW3W4X10o"). Qed.
  Lemma keeps_bind : forall {A C} (m : M A) (k : A -> M C), keeps m -> (forall a, keeps (k a)) -> keeps (mbind m k).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["Keeps"] "p'0h01pi001ph11ai011ah21rh31Ah41Ch51Eh62E2h72Hkh82Hmh92a0h:1ci021ch;1kh<1mh=1si031sh>2s1h?2s2p;2p;3p;4p;6p;8p;5p200R0g00GaR1p4p7210R2p8P0g00D>R3p6051003p8P0g00E:R4p4p7210p8P0g00EoR5p6054111001R6p8P0g00KNR7p4p710R8p8p201R9g0000R:p6051002p8P9P2p8P9g00CCR2p6051002p8P9P3p60521002p8P9P4p4p73110p8P9P6p8P9P8p8P1j27TP5j26Tg00JnR5j23TP7j30Tg00JTj31Tg00Ffj34TP:j35Tg00NUj42Tg00GCj6<TP2j6;TP3j88TP4j69j5:Tp,2StR4f1R3'7f2R21742[f3R:/63f4R7P2f0R1O1R8,67]1f6R6/34R;f5R</34R=p,1BR>p,1fR?f7R@?041RAO1P?P3O1RB31X0;P?A0641O1=1>BX0=RCP7P1O1P7A4@41PAO2X0;P8P5P@P4P?f8R8?041O1RAP?P2O151>RD1384REP?f9RF?041O1P?P7O151>X0EP6A4F43A0F43O235[P1P?f;REPEP4P3P1C2704O1P?P<O151>13E4REP?f<RG?041O1RHP?f=RIPIP4P:P2C2704O151>X0EP?P@O1RJ91>HX0EPFPGP4P2P3C2RH94G4RKA0G4HRHO2P@PKPHO2P5PGP4P?A0I41O1R5P?P:O1RH51>P?f>RK?043O1P?PFO151>[P1P?f@RLPLP4P3P1C2704O1P?P6O151>P>PBPJP?PGO1RJP1P6E<P?fARBPBP4P2P3C2704O1=1>JeW6X?4X:KP3P1O2n2001100000120102103X2E13G4P?PKP4P7P:C290K4O191>5W0P1O1P?A0I43O1P?P8O151>[^2EeE;W5X>4X1FP3P1O2n2001100000120101103X9;13@4R@PDW0P1O1A1>AHX0@P<A4843A0843O255@[^1;eG8P4P6P<P7P:P1E995=CeX=4P4P<P7P:P2D:,67eW7W8W;W<X49X30o"). Qed.
  (* [comment removed for export] *)
  Lemma keeps_getk : forall {C} (k : St -> M C), (forall s0, keeps (k s0)) -> keeps (mbind mget k).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["Keeps"] "h01ph11Ch22Hkh31kh41sh52s0p;2p;3p;1p;4p;5p;6p200R0g00GaR1p4p7210p8P0g00E:R2p4p73110p8P0g00EoR3p6054111001p8P1j2>TP3j23Tg00Jnj22Tg00KNj30Tg00JTj3=Tg001^j1:Tg00NUj48Tg004Dj25Tg0062j36Tg00Ffj37Tg009Hj54Tg0000j31Tg00I`j19TP2j6<j5;Tp,2StR2f1R3,>2[f2R1P3f0R4O1'3^52P3P4P4O2f3R5/22R6p,1Bp,1fR7f4?024O1P7P3O13=X06R7g006hR81222R9P6%:9P2P2P4P4C8,59568P5A7224A0224O2X09D431eP2P2P5%92R5P1P4E<9167eX42P2P2P1P5P3D;,31eW2W3X10o"). Qed.
  Lemma keeps_loop : forall {X R} fuel (body : X -> M (X + R)), (forall x, keeps (body x)) -> forall x, keeps (mloop fuel body x).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["Keeps"] "p'0h01xi001xh14bodyh24fuelh32HBh42IHh51Rh61Xh71ah81ri011rh91si021sh:2x'i032x'p;2p;6p;1p;3p;4p200R0g00GaR1p4p7210R2p8P0g00EoR3p6054111001R4p8P0g00P9R5p4p7210p8P0g00PnR6p6054111001R7p8p201R8P2p8P8P4p8P8g00QjR4p6054111000p8P8g00ReR2p6054111000p8P8P5p4p73110p8P8P7p8P8P6p60551111000p8g00S`R7j22TP1j23TP3j20TP5j61TP2j19Tg00BOj34TP4j28TP6j65Tg00T?j16Tg00T^j47Tg00U?R6f3R4p,2StR2f4R5/24R3'3[f5R1/25R9f1f0R:O1R;'0^05P2f6R<P1P4f2R=P:E1,01^01[]1R>X26124=,32\=103;^04%95P2P1P5g00U^P=P:E1,05eX05W3W11329\512<1/0;^01f7R9/2<R4P<P=P:O1P7f8R3P91323P:P2f9R?P3P<P5P:E1A423:n200110200021010310101X94P;P7P3P9P7P?P3132?P:P2f:P?P9P1P:E1A42?:n200110200021010310101,03P:P<P1P5P:O3X:?P:O118?:X83P:O1n200110200021010010101X74E5P2P9P<%65P=P:E1,0<eX0<W3W1X4>X26P:C7W2X58X60o"). Qed.
  Lemma keeps_if : forall {A} (b : bool) (m1 m2 : M A), keeps m1 -> keeps m2 -> keeps (if b then m1 else m2).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["Keeps"] "p'0h02m1h12m2h22H1h32H2h41Ah51bi001bp;2p200R0g00GaR1p4p7210p8P0g00EoR2p6054111001p8P1j21TP2j20Tg00V=R2P2p,2StR1f2R3'1R4f3R5,11f4R6f1R7'0R8f5/07f6P2f7,11P6P5P3n0110000020000'0[[]1]0f0R31117R11057R5P7X38W2X14W0P3X38X25X14X01n0110000020000W5X40o"). Qed.
  Lemma keeps_when : forall (b : bool) (m1 : M unit), keeps m1 -> keeps (mwhen b m1).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["Keeps"] "p'0h02m1h12H1h21bi001bp;2p;3g00Gaj23Tg00Eoj20Tg00V]j32Tg00Qjj21Tg00V=R0P0p,2StR0g00L_R1'3R2f0R3,01R4f2f1520,01[]0P3P3X14X02g00WR,11X14X02n0110000020000W2o"). Qed.
End Keeps.
Arguments keeps {St B} f {A} c.

Ltac keeps_step :=
  first [ apply keeps_ret | apply keeps_unr | apply keeps_sys | apply keeps_get
        | apply keeps_getk | apply keeps_bind | apply keeps_if | apply keeps_when
        | apply keeps_upd; [intros; reflexivity] ].
(* [comment removed for export] *)
Ltac keeps_tac :=
  repeat (intros; cbn beta;
          first [ solve [auto]
                | keeps_step
                | lazymatch goal with
                  | |- keeps _ (match ?x with _ => _ end) => destruct x
                  end ]).

(* [comment removed for export] *)
Lemma implM_keeps : forall segs {St B A} (f : St -> B) (c : @Monad.M St A) s Q ms,
  implM segs c s Q ms -> keeps f c -> implM segs c s (fun r s' ms' => Q r s' ms' /\ f s' = f s) ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) [] "p'0h03ms'h11pi001ph21rh31ai011ah42s'h51Ah61Bh71Eh81Hh92H0h:2HQh;1Kh<1Qh=2Sth>2a0h?1ch@1fhA2mshB1si021shC4segsp;1p;2p;7p;5p;3p;8p;4p;:p200R0g00GaR1p4p710p8P0g00X2R2p4p7210R3p8P0g00EoR4p4p710p8P0g00FfR5p4p7210p8P0g00XmR6p4p741110R7p8p201R8P4p4p7210p8p202R9P1p4p7210p8P9P3p8P9P4p4p741110p8P9P5p4p710p8P9g00YkR3p4p73110p8P9P7p8g00;cj1=TP1j2<TP3j76TP4j57Tg00<Cj1;Tg00JnR4j25TP5j32Tg00KNj30Tg00JTj31Tg00=9R5j23TP2j88Tg00NUj44Tg00>Ej49TP6l::Tg00@I#=f2R6P6[f3R2f1R3'<f4R1f6R7g00AHR:p-0[[\2f7R;f8R<f5R=P2P6P3f0R>F6P<P;P=P7P1D7g006hf:R?%;?f9R@,5;RAP=P1O1RBf;RC,5@RDP7f<RE=2?>A0?E>RFO2W1P3P>O2P@PFO1P@P;O1RF51CX1DP3O1'3X0:X2AP=A2@C3A0@C3RGP>O3P<PGO1P<P7O151?'3X0:X1AP6P?PAPBP;A0<?>RBO1P;P=O151@X1AP1A2<?>PBO2X1AP6P3P>P1O1G8P4P<P?P7A2?E3A0?E3R4P>O3P@P4O1=1CF'3P;f=R4=2C6A0C46RBP3O3P?PBO1P?P<O151E'3[^0:P>P@f?RBP4PBP6P3C4RG524A04BGRGP>O3f>RHPEPGO1PEP?O131'3P5P?f@R5PHP5P2P6C4RG52HA0H5GRGP3O3P4PGO1P4PCO151BPCfARGPBPGP1P2C4RI52BA0BGIRIP6O3PHPIO1PHPEO1515'3P>PEfBRIP5PIP=P1C4RJ525A05IJP2O3P5fCR2PGP2P7P=C450GO1P5PHO151IPHfDR5PIP5P;P7C4RJ52IA0I5JRJP=O3PGPJO1PGPBO1512P3P>C9W7W:P3P>O2n2001000000120000000W9X0:X44X3?P3P>O2n2001100000120101102X>A15C4R2P<A2EH>A0EH>RHO2W1P3P>O2PCPHO1PCP@O1514X12P3O1'3X0:X2DP3P>O2P7A2?E6A0?E6REP3O3P@PEO1=1CF'3[^0:^3AeM::P@P?P;P=P1P7P6P3P>O3P@P3O1=1CF'3X0:X4?X2;P6F6eW;W8XA:W<WBW?W@X59X68X=0WCo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ps_heap (s : PState) : _ := (ps_m s, ps_brk s, ps_fa s).

Section StdoutKeeps.
  Context {B : Type} (f : PState -> B).
  Hypothesis FSO : forall v s, f (set_so_ps v s) = f s.

  Lemma upd_so_k : forall g, keeps f (upd_so ps_so set_so_ps g).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "h01sh11gp;1p;2p;5p;4p100Z`p4p70R0p100[Up4p710R1p8P0g00\UR2p6051001R3p8P0P2p60521000R4p8P0g00]PR5p4p710R6p8P0p,1BR0p4p300R7p8p100^Fp4p70R8P1p8P8P3p8P8P4p8P8P6p8P8P7p8P7P4p8g00_;R4j14Tg00`1R7j23TP2j50TP5j41Tg00Eoj52Tg00`kR5P5[g00afR5P0p,1fR2f1f0R8#4O1R6/38X05p,3FSOP6P8O2X05D0P5P0P2g00L_P5P4P7P8C1D2eW1o"). Qed.
  Lemma rd_so_k : keeps f (rd_so (St:=PState) ps_so).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "h01sp;3p;1p;5p;2g00b_j36Tg00I`j15Tg00_;R0j12Tg00BOj31Tg00E:j54Tg00Eoj50Tg00cZj23Tg00afR1p,1BR2p,1fR336P1P2P3g00`kR4P1P1P4%51f0#29114X01D4D0eP1P2P3P41310D0eo"). Qed.
  Lemma stdio_write_loop_k : forall fuel fd iov, keeps f (stdio_write_loop (St:=PState) fuel fd iov).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "h02fdh14fuelh23iovh32IHh41ah53cntp;1p;4p;2p;3p;6p;5p;9g00;cj13Tg00[Uj41Tg00Rej46Tg00Hlj2HTg00dOj12Tg00e4j1=Tg00eRj1<Tg00f5j4:Tg00fQj27Tg00gFj14Tg00h?j18Tg00M?j49Tg00Gaj2GTg00i9j2FTg00BOj3ETg00iVj2?Tg00jQj6>Tg00Eoj55Tg00Qjj5@Tg00kLl9ATg00Pnl9BTg00E:j5;Tg00T?j1CTg00T^j4DTg00afR0f2R1f1R2g00L_R3f0R4D5p=0g00U?R5g00lFR6%36R7#3R8p,1BR9p,1fR:P0P1P2P4C130]2]0R;X15P0P9P:P3C61H03909:eP0g00U^P2P4C1909:eX28X06P0P9P:P6P3P0P6P7g00ld#2#2#2#=#<#3g00mIP4C:,72R7%44#8R<C9R=g00V=1G03%42,F4R>g00WRR?9E03R@P0f4P11?24RAC1RBn0100000020000RCX56RDP0P9P:P6P7P<E>P0P9P:P6P=D5eP0P9P:P3P>P@PBP0P9P:P3P?D@A09:@ef3R@P1PAO2A09:BeM9AA09:CeX46M9BP0P6P3P=PDD;909:eP0%C@P2P4C1909:eX28X06X3;X15P4CDW1o"). Qed.
  Lemma stdio_write_k : forall fd buf s, keeps f (stdio_write (St:=PState) fd buf s).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "p'0h02fdh11Hh23bufi003bufh34fuelh43iovh51si011li021zp;1p;4p;2p;3p;9p;5g00;cR0j13Tg00[Uj44Tg00nAj22Tg00o9j2?Tg00oVj2;Tg00Hlj2:Tg0103j18Tg00T?j17Tg010Sj16Tg0113j31Tg00Rej45Tg00kLl99Tg00Gaj2>Tg011Sj4=Tg00Eoj5<Tg00afR1f2R2f1R3g00L_R4f0R5D<p=0g00lFR6%36R7g012Ng00U?%37R8p,1BR9p,1fR:P1P2P3P5C430]4^06]3P1P9P:P4g013R12621263'?R;';R<1:14R=P1%8;#7R;f3R>P0P6P8P2%67R89173f4A17>8517n10110000020020102101R8C4R6P1P9P:P4C5A09:=eP5P;P>P8O3A09:6eM99g00V=1>14P<P=P6n0100000020000909:eb1P1P2P3P5C=909:eX57W2W0o"). Qed.
  Lemma stdout_stdio_write_k : forall s, keeps f (stdout_stdio_write ps_so set_so_ps s).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "h01ah11sh22soh31Hh42H0h52H1h63bufh72fdh81gp;1p;2p;5p;4p;9g00;cj1?Tg00cZj2>Tg00Eoj52Tg011Sj43Tg014Kj1;Tg014ij1:Tg010Sj19Tg015_j17Tg016Xj16Tg017Pj48Tg00E:j54Tg00Pnl95Tg018Kj4=Tg00]Pj4<Tg00afR0g00_;R1g00`1R2f0R3C<p=1P0f2R4f1R5g00L_R6P3D2p=0g00lFR7#?R8g019MP0p,1BR9p,1fR:g00`kR;1>01R<D2R=g01:FP;\;%13909:]8g01;@P0P4P5P3C3909:^18^68^77P0P9P:P;P6P<P0P6P6P0g00ld#;R8%:3R>f4R?C3R@g01<?%97%73%63C8X2;R7#1RAV6RBD4RCX2;RDP4P=eP0P9P:P6P6P@PBP5P8P>P?O3A09:@ef3P7O1A09:AeX06M95A09:CeX0;M95P0P;P6P<PDD4909:eb5b4b3P0P1P2P3C=909:eW1o"). Qed.
  Lemma stdout_writefn_k : forall s, keeps f (stdout_writefn ps_so set_so_ps s).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "p'0h01ah12soh21si001sh31Hh42H0h52H1h61ei011eh71gh81ri021rh91vi031vp;1p;2p;5p;4p;3p;6p;9g00;cj1JTg00cZj2ITg00Eoj54Tg00Gaj2?Tg016Xj1>Tg01<_j1<Tg014ij1;Tg015_j19Tg017Pj45Tg014Kj1:Tg01=Xj2HTg00M?j4GTg00Hlj2CTg00E:j52Tg00BOj3BTg00jQj6@Tg00Rej4ATg00Pnl93Tg00kLl9=Tg01>Mj4DTg00]Pj4ETg018Kj4FTg00afR0g00_;R1g00`1R2f0R3CEp=1P0f2R4f1R5g00L_R6P3D4p=0P0P1P2P3CFp=6P0P6P6P5P3D2p=7P0f5R7f4P6P6f3R8P4P5P3M93p=8g00lFR5#JR9g019MP0p,1BR:p,1fR;g00`kR<1I01R=D4R>g01:FP<\<%1390:;]7g01?K%6390:;^29P0P:P;P<P6P=g00V=1?06R9%>3R?%<3R@%;3RA%93g01@QRBC5X1<RC#1RDP0g01A1REP6P0PEg00ld#:g01Ag'HRFg01BaRGCGRHPEP9P3P@PAPBP?C5X1<RB#1RA1C06R@n0110200021010110103R9X8ERID2RJV6RK'7RLg00WR9B06RMn0100000020000RN%67ROV6RP'7RQX1<RRP4P>eP:P;PNPPP0P:P;P6P?PLPMP:P;PDPKP4PCO1A0:;DeP0P:P;PEP6PHPIP0P:P;PEPFPGE@P0P:P;PEPHD4ePEA0:;9R9P3f6PBO1A0:;AeX65P3O1P0P:P;P6CAA0:;@eX95P3O1n0110000021010110103P9eX0EM93A0:;JeX06E8A0:;LeP8A0:;MeM9=A0:;NeP4P7O1A0:;OeX06E8A0:;QeX0<M93P0P<P6P=PRD290:;eb5b4b3P0P1P2P3CD90:;eW2o"). Qed.
  Lemma stdout_towrite_k : keeps f (stdout_towrite ps_so set_so_ps).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "h02sop;1p;4p;3p;5g01<_j17Tg010Sj16Tg015_j10Tg016Xj11Tg017Pj45Tg01:Fj12Tg01CZj33Tg00Eoj54Tg00`kR0g00V=P0f0R0#7P0g01<?g00lF#6%00%10C5n0100000020000W0#2g00afR0p,1Bp,1fg00L_g00_;g00`1530D4eo"). Qed.
  Lemma stdout_fwritex_k : forall s, keeps f (stdout_fwritex ps_so set_so_ps s).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "h01ah12soh21sh31Hh42H0h52H1h62H2h71gp;1p;2p;5p;3p;4p;9g00;cj1NTg00cZj2MTg00Eoj58Tg01CZj3ETg00Gaj2CTg014ij1BTg00nAj2=Tg01DXj2@Tg00oVj24Tg015_j1?Tg01E5j1>Tg0103j1;Tg01F2j3LTg00BOj3ITg01<_j1HTg01FQj3FTg01Foj39Tg016Xj1DTg017Pj4<Tg00E:j55Tg00Pnl9:Tg01GLj4GTg00]Pj4ATg01>Mj4JTg00kLl9KTg00afR0g00_;R1g00`1R2f0R3CAp=1P0f2R4f1R5g00L_R6P3D8p=0P0P1P2P3CJp=2P0P6P6P5P3D5p=6P0f6R7f5R8P6f4R9f3R:P4P5P3M9Kp=3P0P8P9P6P6P:P4P5P3M9:p=7g00lFR5#NR4g019MP0p,1BR;p,1fR<g00`kR=1M01R>D8R?g01:FP=\=%1390;<]7g01HJ%2390;<^24g01ILAE012R490;<R@P;P<P4P0P=P6P>g00V=RA1C06RBg01JN%B3RC,=5'@1=57'4RD%27REPAPB%?3RFPAPBg01KK%>7RB'4RA%;B=L57RB#2RGg00WR9I06RHn0100000020000RI%H3RJf8RK#>#;=F5K995CPF%D3RKC<X1=RL#1RMV6RN'6ROPJf7995CPFPKC<X1=RK#1RCn0100000020000R5n0100000020000RJX1=RPD5RQV6RRP3P@eP0P;P<P=P6P>PPP9P?eP;P<PDPEP5P:P7O1A0;<EeP;P<PFPOPCP;P<PIPNP;P<PAPGPHP:PBO1A0;<GeP8A0;<HeF3A0;<IeP8PLO1A0;<MeX06E7A0;<OeP9PKO1A0;<CeF3A0;<5eF3A0;<JeX0=M9:A0;<QeX06E7164R90;<eb6b5b4b3P0P1P2P3CG90;<eW2o"). Qed.
  Lemma out_pieces_k : forall ps, keeps f (out_pieces ps_so set_so_ps ps).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "h02psh11Hh22IHh31ah41ph51sp;1p;5p;9p;3p;4g00;cj12Tg00Qjj54Tg010Sj1<Tg00Pnl9;Tg00E:j55Tg0113j36Tg01Kij57Tg01LKj48Tg00Eoj59Tg01GLj4:Tg00afR0g00_;R1g00`1R2f0R3C8p=1P0f2R4f1R5g00L_R6P3D9p=0P0P1P2P3C:p=3g00lF#2R2#2R1P2p,1BR7p,1fR8%1330R9X01P0P7P8P6g00WRD4%<2#19078eg01ME%339078^52P0P7P8P6P6f3R:#3R;%1:R<V6R=P3P:O1A078;eP4A078<eX36M9;P0P6P6P;P=D59078eb1A6245#19078eX29X01X42P3D7W0o"). Qed.
  Lemma stdout_vprintf_k : forall ps, keeps f (stdout_vprintf ps_so set_so_ps ps).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "h02psh11Hh22H0h31ap;1p;3p;9p;5p;4g00;cj12Tg01CZj38Tg00Pnl97Tg00E:j56Tg01NGj44Tg00Eoj53Tg01LKj45Tg00afR0f2f1R1g00L_R2f0R3D3p=0P0g00_;R4g00`1R5P3C5p=1g00lF#2#2R6g01ILp,1BR7p,1fR8A8045R930R:g01OE%139078^06P0P7P8P2P2P9f3R6#1R;V2R<P1P:eP1P6O1A078;eX32M97P0P2P2P9P<D69078eb2b1P0P4P5P3C49078eW0o"). Qed.
  Lemma s_emit_k : forall v, keeps f (s_emit ps_so set_so_ps v).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "h01vp;1p;4p;5p100Z`p4p70g01PCR0p4p710R1p8p100^Fp4p70P1p8g01Q:j13Tg01R6j12TP0j40Tg00Eoj51Tg00lFf0R0#3#2g00afR1p,1Bp,1fg00L_P1g00_;g00`1P0C0D1eW0o"). Qed.
  Lemma stdout_exit_flush_k : keeps f (stdout_exit_flush ps_so set_so_ps).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) ["StdoutKeeps"] "h01Hh12H0h21ah31sh42sop;2p;5p;1p;3p;9p;4g00cZj2?Tg00Eoj52Tg00;cj14Tg00Gaj2;Tg014ij1:Tg00nAj25Tg00oVj26Tg010Sj17Tg00BOj33Tg00kLl98Tg00Pnl99Tg00E:j5>Tg01S8j3=Tg01>Mj4<Tg00afR0g00_;R1g00`1R2f0R3C<p=1P0f2R4f1R5g00L_R6P3D2p=0g019MP0p,1BR7p,1fR8g00`kR91?01R:D2R;g01HJg00lFR<#4%139078]3P0P7P8P9P6P:g00V=1;06g01KK%:3,5<'6R3%7<R<#1R=g00WR9306R>n0100000020000R?X49R@P5P;eP0P7P8P6P3P=P>P5P<O1A078=eP4A078>eM98A078?eX29M99P0P9P6P:P@D>9078eb1b0A=0129078eo"). Qed.
End StdoutKeeps.

Lemma s_emit_heap : forall v, keeps ps_heap (s_emit ps_so set_so_ps v).
Proof.
ltac2:(KReplay.run1 (kr_t_Keeps ()) [] "h01vh11sp;2p;1p;4g00Jnj20Tg01T9R0j13Tg00HRj22Tg01U2j41Tg00lFR1g01Ul/01g00L_'0R1P0g00`kg00aff0R0#3,21W1W0P0C1W0o"). Qed.
