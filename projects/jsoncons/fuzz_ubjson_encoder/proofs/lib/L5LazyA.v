(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct AsanAcctShape HeapIface HeapIfaceA L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_L5LazyA () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct9mrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~K47Corelib4Init5Logic2eq01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct;munrestrictC13~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic6eq_symC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>H_off_segmentsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>wx_segs_nowrapC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct:lazy_coverC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4A_wfC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4MInv00C13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctEsame_but_materializedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct8restrictC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5LazyA4L5LZ=restrict_mkstC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct6hcleanC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct:unrestrictC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5LazyA4L5LZ?unrestrict_mkstC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanAcctShapeGsrz_msteps_restricted_TC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List4inclC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>lazy_cover_mkHC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA4ahidC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct<segs_below_bC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct=page_allowedbC13~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes9andb_propK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctHfind_segment1_none_aboveC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct3mkHC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5LazyA4L5LZ8sbm_lazyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8model_rtC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_time".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5LZ.
Section WithSegs.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Lemma restrict_mkst (fx : FPState) H R pc M :
  restrict H (@mkst fx R pc M (seg_rom segs)) = @mkst fx R pc (mrestrict H M) (seg_rom segs).
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "h01Hh11Mh21Rh32fxh42pcp;1p;2p;5p10000p4p70p1000`p4p710R0p8p1001>p4p70P0p8g001lR1p4p7210P0p8p1002Xp4p70P0p8g003Nj10Tg0043j11Tg004Qj12Tg0054j13TP1j29Tg005Yj18Tg006;j27Tg007Hj14Tg008Sj55Tg009[j26Tg00:5R1g00;B#0R0#0#0R2#0#0#0#1#2R3g00;g[R4%30#1/93R0%12#2#8\3R2g00<Gf4R5f2R6f1R7f3R8f0R9'7p,4segs#4D5'6X12X43X20X04X31P5P8P6P7P9O5W1X43W2W0W3o"). Qed.
Lemma unrestrict_mkst (fx fx' : FPState) H R pc M R' pc' M' :
  unrestrict H (ms_mem (@mkst fx R pc M (seg_rom segs))) (@mkst fx' R' pc' M' (seg_rom segs))
  = @mkst fx' R' pc' (munrestrict H M M') (seg_rom segs).
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "h01Hh11Mh22M'h31Rh42R'h52fxh63fx'h72pch83pc'p;1p;2p;3p;5g003Nj10Tg0043j11Tg004Qj12Tg0054j13Tg001lj29Tg005Yj18Tg00=Nj37Tg007Hj14Tg008Sj55Tg009[j26Tg00:5R0g00;B#0R1#0#0R2#0#0#0#1#2R3g00;g[R4%31#1/93R1%12#2#8\3R2g00<Gf7R5f2R6f1R7f6R8f3R9f0R:37p,4segs#4D5'6X22X83X41X12X73X31X04X60X50f8P5P8f5f4P9P6P7P:O9X22X83X41W1X73W3W0X60W5o"). Qed.


(* [comment removed for export] *)
Lemma mrestrict_of_munrestrict H M M' :
  (forall a, H a = true -> M' a = None) -> mrestrict H (munrestrict H M M') = M'.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "p'0h01Eh11Hh21Mh32M'h41ah51xh62Hch71bi001bp;1p;3p;2p;4p;5g003Nj11Tg0043j15Tg004Qj13Tg005Yj16Tg00>]j30Tg00?7j1;Tg00=Nj34Tg006;j2:j37Tg009[j22Tg00?Yj49Tg00@5j58Tg00;B#1#1#1R0#1#1#1#5#3R1g00;gR2]5R3%50#3R0#6R4\1R5P4^51R6f3R7f0R8O1g00A7R9502f2R:f1R;O1%;0R0504[^41P1P4A47:;,:7P;f4R<P8O1P21228f5R=P;O1=028P2f7R>P7O1=028P2P4P;P0P2P4P;P>P<O1f6R>P<O1R?n0100000020000n0100000020000=04?]0P;P>P:O1R>=029P4P=P7O1R=P0P<P7P8O2C9W0g00AW902>124=W0n0110000020000P8O1b0b7A4<7:=7<8P:P8O1504eX41D8W6X36X25X13P:P;P8O3W3W2W1o"). Qed.
Lemma munrestrict_hidden H M M' a : H a = true -> munrestrict H M M' a = M a.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "h01Hh11Mh22M'h31ah41Eh51bh61xp;1p;3p;2p;6p;4g003Nj10Tg0043j13Tg004Qj12Tg005Yj14Tg00>]j31Tg009[j27Tg000`j66Tg00=Nj45Tg00;B#0#0#0R0#0#0#0#3#2R1g00;gR2]6R3%30#2#4R0\1R4f3R5f0R6O1g00A7R7512P2P7P2P0P6f4R7f2R8O1R9P5P8O1n0100000020000=109X52P5f1R2O1R9,70P7P2O1P6E6P7P5P8P2C5=109eW4X31X24X14X03P5P8P2P6O4X31X24W1W0o"). Qed.
Lemma munrestrict_visible H M M' a : H a = false -> munrestrict H M M' a = M' a.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "h01Hh11Mh22M'h31ah41Eh51bh61xp;1p;3p;2p;6p;4g003Nj10Tg0043j13Tg004Qj12Tg005Yj14Tg00>]j31Tg009[j27Tg000`j66Tg00=Nj45Tg00;B#0#0#0R0#0#0#0#3#2R1g00;gR2]6R3%30#2#4R0\1R4f3R5f0R6O1g00AWR7512P2P7P2P0P6f4R7f2R8O1P5P8O1R9n0100000020000=109X52P8f1R2O1R9,70P7P2O1P6E6P7P5P8P2C5=109eW4X31X24X14X03P5P8P2P6O4X31X24W1W0o"). Qed.
Lemma mrestrict_visible' H M a : H a = false -> mrestrict H M a = M a.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "h01Hh11Mh21ah31Eh41bh51xp;1p;3p;2p;6g003Nj10Tg0043j13Tg004Qj12Tg005Yj14Tg00>]j31Tg00?7j18Tg009[j27Tg000`j65Tg006;j36Tg00;B#0#0#0R0#0#0#0#3#2R1g00;gR2]5R3%30#2R0#4R4\1R5f2R6f0R7O1g00AWR8512P2P8P2P4P7%80f3R0P6O1R8n0100000020000=148X42P6f1R2O1R8,74P0P2O1P7E5A6062=148eW3X21X15X03P6P2P7O3X21W1W0o"). Qed.
(* [comment removed for export] *)
Lemma mrestrict_agree_on (H H' : word -> bool) (M M' : word -> option byte) (P : Z -> Prop) :
  (forall a, P a -> H (Z_to_bv 64 a) = false /\ H' (Z_to_bv 64 a) = false) ->
  (forall a, P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  forall a, P a -> mrestrict H' M' (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a).
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "h01ah11Hh22H'h31Mh42M'h51Ph61bh71Eh82E'h92HMh:2HVh;2Hah<2a0p;1p;2p;3p;6g003Nj12Tg0043j18Tg004Qj16Tg005Yj19Tg00B7j21Tg00B]R0j27Tg00>]j33Tg006;j34Tg00?7j1:Tg000`j65Tg00;gR1f0R2g00AWR333p=0g00;B#2#2#2R4#2#2#2#8R5#6R6P1[R7%84#6R4#9R8\6R6g00C8R9p-0[R:f1R;P2O1f6R<115;R=O1#0f5R>P=O1R?#0'7[^09f2R@P2O1f4RAP=O1=38?[^09f3R?P2O1P?P;P2O2f8RBP=O1#0f7RCP=O1#0'7P0f9R0115@R=O1#0PBP=O1#0115?R=940Cf:R0?4B=538P2f;R=115AO1#0P=115>O1#0P1P3P1P8f=RB115CRDO1%:4R4P=PDO1REn0100000020000P1P8P2P4f<RFPDO1RDn0100000020000538X61P1P3P1P8P2P4PEn0100000020000=38DX61PCP<P>O2PF115<R<O1P2E5PBP<O1P;E5A4F0<A4B=<538eW8W7P;P2O2n2001000000121000000b<W;X09W9W:X5:X46X36X27X17PAP?P@P;P2O5W5X46W3X27W1o"). Qed.

(* [comment removed for export] *)
Theorem cps_of_msteps_lazy (H : word -> bool) (A : list (Z * Z))
        (fx fx' : FPState) R pc M R' pc' (M1v : word -> option byte) (model : Model) K :
  H_off_segments segs H -> wx_segs_nowrap segs ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  msteps segs (@mkst fx R pc (mrestrict H M) (seg_rom segs)) (@mkst fx' R' pc' M1v (seg_rom segs)) ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
       (forall a, H a = true -> M1v a = None) ->
       srealizes segs SCFG (mkCfg (@mkst fx' R' pc' (munrestrict H M M1v) (seg_rom segs)) model') K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R pc M (seg_rom segs)) model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "h01Ah11Hh21Kh31Mh43M1vh52MSh61Rh72R'h81ah92fxh:3fx'h;1mh<5modelh=6model'h>2pch?3pc'h@2HAhA2HChB2HHhC2HIhD3HI'hE2HKhF2HLhG2HShH2HahI2HhhJ3Hwxp;1p;2p;3p;5p;6p;9p;Ag003Nj11Tg0043j14Tg004Qj19Tg00CVj2BTg00D6j1QTg0054j1OTg001lj2FTg005Yj18Tg00DVj2DTg00Ehj1CTg00G:j1ATg00H2j3@Tg00I@j1?Tg00JHj25Tg00KRj1PTg00?7j1>Tg00>]j32Tg006;j2<Tg007Hj1NTg008Sj50Tg00LIj33Tg00MSj2;Tg00Nlj1ETg00=Nj3=Tg00P2j27Tg00Pgj5:Tg00R3j2GTg00S?j5HTg000`j66Tg00TTj2ITg00U^j1JTg00V\j3KTg00Wjl9LTg00YAlAMTg00;B#1R0#1#1R1#1#1#1#4#9R2g00;gR3[R4g00C8R5/B5#QR5g00:5R6%O0#4/F2R0%41#9R1#8R7\2R8g00ZaR9g00[WR:p,4segsR;f;R<'D%C;f=R=f3R>#Af<R?3@%?=f>R@f5RA'5%82f6RB#P%>232f?RCP=P?fARD/<<%N;RED0P@f:RFf9RGf8RHPED053;fBRIf0RJ'5f1RK,;FfFRLPJO1g00A7RM523P@PKO1%>1527[^82g00\_R7P;p,6SCFG_P#ER1fCRNPCP@f@RO==L=PED0/7>P<D:[[[^=9g00<GRPPDPCP@1<N=PED0PDP=P?P<PED0RQ93;JX;PPKPDPCP@P=PED0,GNRRPDPNPCP@P=DHE6POP?P<PFPED093;RP7P;P1fDRRPHf7R=PNPIPOPCP@PED0PQPFPGPBPAf4RQP>PJ15RJ1;?KfGPRPOPCP@PED0'IPPfER?PDPOfHRS?=ICPED0P7P;P117JQP@D:X;PPAP>f2RPPKfIPJO1=23MPPPKPJO2WHX82O4PLPRPNPIPED0#JP?PDPOPCPED05KSPLP?PSPRPNPIPDPOPCM9LE6WAWGWDX=9MAMb5WEW5WIWCW@WFWJWBX2:X<9X48X?2X70X38X>2X60X:6X96X05X14P<PFPGPHP=PBPAPQP>PPPKPJO<W2W<X48X?2X70W3X>2W6X:6W9W0W1o"). Qed.

(* [comment removed for export] *)
Lemma lazy_cover_ahid A model : lazy_cover (ahid A model) (m_vm_lazy model) A.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "h01Ah15modelh22Hrh31rp;2p;1p;3p;4g00CVj22Tg00D6j1:Tg00G:j11Tg003Nj10Tg0043j19Tg004Qj18Tg00]kj37Tg00^Bj34Tg00^[j45Tg00_mj26Tg00H2j33Tg00C8R0/20#:R0g00ZaR1f0R2#1R3f1R4P3g00;B#0#0#0#0#0#0#9#8R5/25R5%149752P2W2W3A4533eC51642?334eX11X00P4P2O2W1W0o"). Qed.

(* [comment removed for export] *)
Lemma H_off_segments_ahid A model top :
  segs_below_b segs top = true ->
  (forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true -> top <= bv_unsigned w) ->
  H_off_segments segs (ahid A model).
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "h01Ah12Hah25modelh33toph42Hbh53Hhih62Hph72_Hh81ah91wp;2p;1p;3p;5g00CVj2HTg00D6j1GTg00a7j2<Tg003Nj11Tg0043j1CTg004Qj1=Tg00bGj12Tg00G:j13Tg00c?j24Tg00d<j25Tg00dfj29Tg00_mj3:j2DTg00eBj27Tg00fSj16Tg00g1j3FTg00B]R0j2BTg005Yj1ATg00gTj1>Tg00h2j3?Tg00?7j1@Tg00>]j38Tg00i6j5;Tg00DVj2ETg00;gf0R1g00A738p=0g00C8R2/H2#GR3g00ZaR4p,4segsR5/<1#0g00;BR6#1#1#1#1#1#1#CR7#=R8%21f3R9#3'4#0f1R:,57,99[]9f5R;f4R<;:1#0%2:R=%3;'4R>f6R?/7=#6R=;F1%0>%0='BP0f2R0#2R=%3?'4#0f7R>/7=#6#0g00jRR=#A1579%>65?5%@=38P1%2<f8R=#3'4#0f:%2;'7#6#0P5f9157?P=P>P?P:O2D;W7W6P:P1O2n2001000000120000000b1W1X881D<9,E5eW5W4X32X24X03P0P:P1O3X32W2W0o"). Qed.

(* [comment removed for export] *)
Lemma sbm_halted m m' : same_but_materialized m m' -> m_halted m' = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "p'0h02m'h11mi001mh21Hh32fdh42fsh52ioh64lazyh73limh86m_fsysi016m_fsysh94m_ioi024m_ioh:5m_limi035m_limh;6m_proci046m_proch<6m_timei056m_timeh=4m_vmi064m_vmh>4mapsh?3math@4prochA2tmi074m_fdi081vi099vmst_lazyi0:9vmst_mapsi0;Avmst_materializedp;2p;1p;3p;7p;6g00MSj2?Tg00G:j15Tg00kQj13Tg00lQj34Tg003Nj10Tg0043j1;Tg004Qj1:Tg005Yj19Tg00KRj11Tg00>]j32Tg00mOj76Tg00CVj28Tg00D6j17Tg00nEj3>Tg009[j2=Tg000`j6<Tg00ZaR0f1R1f0R2'?P0f2R3#5%31;43g00;B#0#0#0#0#0#0#;#:R4#9R5%12R6f3R7#132X00P0%52%33;42#1=256P3g00o=g0105R6P6g010mR6g011eR8g012]R9g013WR:g014PR;f7R<f5R=f4R>P7P3P1P2F6R?#5f@#3;4?#1%1?525]<]:];]8]9P2g015J1844#7%74f<f6R4=><=P>P7P3P1P2F6#1,=5XA;X7:X@9X48X56W?W6W>P3P1P2O3n0110800013010:10910;W=W3P4P=P>P7P3P1P2O7n01100000170107106102101104103105P1P2E<W2X00X10P1P2O2X00W1o"). Qed.
Lemma sbm_lazy m m' : same_but_materialized m m' -> m_vm_lazy m' = m_vm_lazy m.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "p'0h02m'h11mi001mh21Hh32fdh42fsh52ioh64lazyh73limh86m_fsysi016m_fsysh94m_ioi024m_ioh:5m_limi035m_limh;6m_proci046m_proch<6m_timei056m_timeh=4m_vmi064m_vmh>4mapsh?3math@4prochA2tmi074m_fdi081vi099vmst_lazyi0:9vmst_mapsi0;Avmst_materializedp;2p;1p;3p;7p;6g00MSj2=Tg00G:j10Tg00kQj13Tg00lQj34Tg003Nj11Tg0043j1;Tg004Qj1:Tg00CVj28Tg00D6j15Tg00>]j32Tg00mOj76Tg00nEj37Tg009[j29Tg000`j6<Tg00ZaR0f1R1f0R2'=P0f2R3#0%31;43g00;B#1#1#1#1#1#1#;#:R4/84#5R5%02R6f3R7#032X00P0%33=462#0=256P3g00o=g0105R6P6g010mR6g011eR8g012]R9g013WR:g014PR;f7R<f5R=f4R>P7P3P1P2F6R?#0R@f@#3;4?#0=25@]<]:];]8]9P2g015J%54f<f6R4=7<=P>P7P3P1P2F6#0,95XA;X7:X@9X48X56W?X65W>P3P1P2O3n0110800013010:10910;W=W3P4P=P>P7P3P1P2O7n01100000170107106102101104103105P1P2E<W2X00X10P1P2O2X00W1o"). Qed.
Lemma sbm_vmmaps m m' : same_but_materialized m m' -> m_vmmaps m' = m_vmmaps m.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "p'0h02m'h11mi001mh21Hh32fdh42fsh52ioh64lazyh73limh86m_fsysi016m_fsysh94m_ioi024m_ioh:5m_limi035m_limh;6m_proci046m_proch<6m_timei056m_timeh=4m_vmi064m_vmh>4mapsh?3math@4prochA2tmi074m_fdi081vi099vmst_lazyi0:9vmst_mapsi0;Avmst_materializedp;2p;1p;3p;7p;6g00MSj2>Tg00G:j15Tg00kQj14Tg00lQj32Tg016Aj11Tg00>]j33Tg00mOj77Tg003Nj10Tg0043j1;Tg004Qj1:Tg00CVj28Tg00D6j16Tg00nEj39Tg009[j2=Tg000`j6<Tg00ZaR0f1R1f0R2'>P0f2R3#5%41;23g015JR4%12R5f3R6#133X00P0%52%43;22#1=345P3g00o=g0105R5P5g010mR5g011eR7g012]R8g013WR9g014PR:f7R;f5R<f4R=P6P3P1P2F7R>#5f@#4;2>#1%1>534]<]:];]8]9P2g00;B#0#0#0#0#0#0#;#:R>/8>#6%6>f<f6R>=9;<P=P6P3P1P2F7#1,=4XA:X79X@8X47X55W?W6X>4P3P1P2O3n0110800013010:10910;W=W3P>P<P=P6P3P1P2O7n01100000170107106102101104103105P1P2E<W2X00X10P1P2O2X00W1o"). Qed.
Lemma sbm_ahid A m m' : same_but_materialized m m' -> ahid A m' = ahid A m.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "h01Ah11mh22m'h32Hsh41lp;2p;1p;3p;6g00CVj24Tg00D6j16Tg00MSj2:Tg003Nj10Tg0043j1<Tg004Qj1;Tg00G:j11Tg0178j22Tg00>]j33Tg009[j29Tg018?j37Tg000`j68Tg00_mj25Tg00C8R0/40#6R0g00ZaR1f1R2f0R3':g00;B#0#0#0#0#0#0#<#;R4/44#6R5f2R6#1R7g00;g\4R4f4R8,23f3R9#1/2833X451279,94%12A7623E815921596534eW3X21X11X00P6P2P3O3X21W1W0o"). Qed.
Lemma sbm_model_rt m m' : same_but_materialized m m' -> model_rt m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "p'0h02m'h11mi001mh21Hh32fdh42fsh52ioh64lazyh73limh86m_fsysi016m_fsysh94m_ioi024m_ioh:5m_limi035m_limh;6m_proci046m_proch<6m_timei056m_timeh=4m_vmi064m_vmh>4mapsh?3math@4prochA2tmi074m_fdi081vi099vmst_lazyi0:9vmst_mapsi0;Avmst_materializedp;2p;1p;3p;7p;6g00MSj2DTg00G:j13Tg00kQj12Tg00lQj31Tg019Oj25Tg00mOj74Tg003Nj10Tg0043j1;Tg004Qj1:Tg00CVj28Tg00D6j16Tg00nEj37Tg01:]j19Tg01;Pj1CTg01<Cj1BTg01=6j1ATg01=kj1=Tg01>`j1>Tg01?Tj1?Tg009[j2<Tg000`j6@Tg00ZaR0f1R1f0R2'DP0f2R3#3%21;13f3R4/52X00P0%32%23;12,52P3g00o=g0105R5P5g010mR5g011eR6g012]R7g013WR8g014PR9f7R:f5R;f4R<P4P3P1P2F4R=%3=f@#2;1='5]<]:];]8]9P2g015Jg00;B#0#0#0#0#0#0#;#:R=/8=#6%6=f<f6R==7:;P<P4P3P1P2F4R:#9%3:fE#2;1:#C%B:%A:%=:%>:%?:F4,<0XA9X78X@7X46X55W?W6W>P3P1P2O3n0110800013010:10910;W=W3P=P;P<P4P3P1P2O7n01100000170107106102101104103105P1P2E@W2X00X10P1P2O2X00W1o"). Qed.
Lemma model_rt_trans m1 m2 m3 : model_rt m1 m2 -> model_rt m2 m3 -> model_rt m1 m3.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "p'0h02m2h12m3h21Hh32m1h44m_fdi004m_fdh56m_fsysi016m_fsysh64m_ioi024m_ioh75m_limi035m_limh86m_proci046m_proch96m_timei056m_timeh:4m_vmi064m_vmi071mp;1p;7p;2p;6p;3g01:]j12Tg01;Pj17Tg01<Cj15Tg01=6j11Tg01=kj16Tg01>`j14Tg01?Tj13Tg00mOj70Tg009[j2<Tg000`j6:Tg019Oj29Tg00>]j3;Tg00ZaR0f1R1f0R23;p=8f2R3#2%71R4%53%13%63%43%33F0,81P0f3R5#2%73R6%55%15%65%45%35F0R7%22R8P6%52R9%12R:%62R;%42R<%32R=F0,83f5R>#2R?%75R@%5>RA%1>RB%6>RC%4>RD%3>REF0,85[X00%27P4%57%17%67%47%37F0,81P0f4R7#2P@%57%17%67%47%37F0R4#2P6%54%14%64%44%34F0P?%72PAPBPCPDPEF0,82X10P0P8%77P9P:P;P<P=F0RE#2P@%5E%1E%6E%4E%3EF0REP8%7EP9P:P;P<P=F0'8P7g00o=g0105g010mg011eg012]g013Wg014Pf6R=P>P7P5P3P1P2F0R<#2R;P;fA#7%5<R;%1<R:%6<R9%4<RE%3<R<F0R8#2f@#7%58%18%68%48%38F0#7P;P:P9PEP<F0,<0W9W7W8W5W6W:W4P=P>P7P5P3P1P2O7n01107010171100106102101104103105P3P2E:W2P3P2E:W21931R51973\5[eX10X00X30P3P1P2O3X10X00X30o"). Qed.
Lemma model_rt_halted m m' : model_rt m m' -> m_halted m' = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_L5LazyA ()) ["WithSegs"] "p'0h02m'h11mi001mh21Hh34m_fdi014m_fdh46m_fsysi026m_fsysh54m_ioi034m_ioh65m_limi045m_limh76m_proci056m_proch86m_timei066m_timeh94m_vmi074m_vmp;2p;1p;7p;3p;6g019Oj2@Tg01:]j1:Tg01;Pj14Tg01<Cj13Tg01=6j18Tg01=kj17Tg01>`j16Tg01?Tj15Tg00mOj72Tg003Nj10Tg0043j1=Tg004Qj1<Tg005Yj1;Tg00KRj11Tg00>]j39Tg009[j2?Tg000`j6>Tg00ZaR0f1R1f0R2'@P0f2R3#:%41%33%83%73%63%53F2g00;B#0#0#0#0#0#0#=#<#;R4%12R5f3R6#139X00P0%:2%43%32%82%72%62%52F2#1=945P3g00o=g0105g010mg011eg012]g013Wg014Pf6R5f5R7f4R8P6P3P1P2F2#1,?4W8W6W7W4W5W9W3P5P7P8P6P3P1P2O7n01100000170101107103102105104106P1P2E>W2X00X10P1P2O2X00W1o"). Qed.

End WithSegs.
End L5LZ.
