(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (18 recorded proofs replaced by written proofs (rw_cells_bytes_at', ashenv_transport, ashenv_core and 15 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Export Stdio_pure.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Stdio_kit () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00c59OSSVerify5KrLib5BothW9Stdio_kit6ashenvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums8positive01K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kit7ashsafeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic3and01K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init5Logic4True01c59OSSVerify5KrLib5BothW9Stdio_kit7shcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kit6hull64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow7app_blkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4LibA6Shadow>unpoisoned_subC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02C59OSSVerify5KrLib4LibA6Shadow;app_blk_subC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4LibA6Shadow9shad_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib4LibA6Shadow8shad_divC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4LibA6Shadow@unpoisoned_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4LibA6Shadow>unpoisoned_nilC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef:Forall_indC47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib5BothW9Stdio_kit4appWC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib4LibA6Shadow4KLOWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5KHIGHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kit<shclean_hullC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kitDappW_shadow_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kitAshclean_transportC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02K47Corelib5Lists7ListDef6Forall01c59OSSVerify5KrLib5BothW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kit5r_rloC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kit5r_rhiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kitEshclean_transport_appC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib5BothW9Stdio_kit6region00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9Stdio_kit5inregC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition FMT_FP_DEPTH : Z := 4640.
Definition fmt_fp_entry : Z := 0xa8e80.

(* [comment removed for export] *)
Definition ICPT_DEPTH : Z := 2240.

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ashenv (m : word -> option byte) : Prop :=
  rt_got m /\ rt_got_ric m /\ rt_shbase m /\ rt_inited m /\ rt_layout m /\ rt_real_mem m
  (* [comment removed for export] *)
  /\ rt_real_printf m /\ rt_real_wcslen m /\ rt_real_read m
  /\ rw_cells bsegs m 0xb3e80 [C8 (Z_to_bv 64 0xa7a10)]
  /\ rw_cells bsegs m 0xb3f50 [C8 (Z_to_bv 64 0xabce4)]
  /\ rw_cells bsegs m 0xb3e68 [C8 (Z_to_bv 64 0xab35c)]
  /\ rw_cells bsegs m 0x14be78 [C8 (Z_to_bv 64 4294967296)]
  /\ rw_cells bsegs m 0x14bf20 [C8 (Z_to_bv 64 0x101010101010101)].

(* [comment removed for export] *)
Definition ashsafe (W : list (Z * Z)) : Prop :=
  disjoint_from W 0xb2118 48 /\ disjoint_from W 0xb2c90 8 /\ disjoint_from W 0xb3fa0 16
  /\ disjoint_from W 0xba2f8 8 /\ disjoint_from W 0xbafd8 2 /\ disjoint_from W 0xbafe0 24
  /\ disjoint_from W 0xb3e98 16 /\ disjoint_from W 0xb3f50 8 /\ disjoint_from W 0xb3e78 8
  /\ disjoint_from W 0xb3e80 8 /\ disjoint_from W 0xb3f50 8 /\ disjoint_from W 0xb3e68 8
  /\ disjoint_from W 0x14be78 8 /\ disjoint_from W 0x14bf20 8.

Lemma ashenv_transport : forall W m m', ashenv m -> munch W m m' -> wmono bsegs m m' -> ashsafe W -> ashenv m'.
Proof.
  intros W m m' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14) MU WM
         (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
  unfold ashenv. repeat lazymatch goal with |- _ /\ _ => split; [eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; assumption] |] end.
  eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; assumption].
Qed.

(* [comment removed for export] *)
Lemma ashenv_core : forall m, ashenv m -> rt_got m /\ rt_got_ric m /\ rt_shbase m /\ rt_inited m /\ rt_layout m /\ rt_real_mem m.
Proof. intros m (A1 & A2 & A3 & A4 & A5 & A6 & _). exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 A6))))). Qed.

(* [comment removed for export] *)
Lemma ashsafe_cons_high : forall lo hi W, 0x14bf28 <= lo -> ashsafe W -> ashsafe ((lo, hi) :: W).
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio_kit ()) ["CANSEC1"] "h04__p1h14__x1h22H0h37__arithh44__ffh58__varmaph65__with72H1h82H2h92H3h:2H4h;2H5h<2H6h=2H7h>2H8h?2H9h@3H10hA3H11hB3H12hC1DhD1HhE1WhF2hihG2lop%0p;2p;1p;3p;6p;4p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8g00IUj2jTg000nj1STg001Nj12Tg00J5j24Tg00AUj1OTg00JQj2;Tg00BQj30Tg00<kR1j21Tg00CMj1ITg00>gj1dTg00Jnj2cTg00KLj1bTg00Kjj1aTg00LUj2`Tg00M8j1^Tg00MZj6]Tg00N>j2\Tg00N`j2[Tg00O:j2ZTg00Ofj3YTg00P@j3XTg00P_j4WTg00Ckj4ATg00QQj4iTg00E;j3hTg00?Gj13Tg00R1j2RTg00RKj2PTg00Rnj4TTg00SYj7QTg00T=j3gTg00T`j7fTg00UDj8eTf0R0#3#2p==%20#3#2#3p=F%30#3#3#3p=<%20#2#2#Ip=5%20#3#3#2p=H%20#3#2#2p=B%20#2p=G%30#3p=L%20#Ip=Vf3R2f2R3'4f1R4/40'Rp=9%20#3p=K%30#2#2#3p=J%20#3#3#3p=C%30#3#2#2p=Mg00;XR5/P0p=EP3g00UhR6g00VGR7P7g00VgR8P5P4g00WGR9P0CTg00WnR:FQp=_1P54=g50p=:f7R;P6P7P7P8f6R<f5R=f4R>P6P7P7P8P2P6P7P7P8P5P3P9P4CTP:FQP0FfGep=71434/R0p=81140,13p=DA0=>2A0340'1p=?A0;<=A0234/10,1>'1p=>A0<=>A0234/10'1p=6A0234/10,1>p=NP<P=P>P2P3P4CAP0CAp=@P<P=P>P2P3P4P0CACAp=U1j55R:#Sg00;3R9#2#=#F#<#=#F#5R?/43%O4%H9#B#G#=#G#L#5R@%=9#GRA#VRB';RCP>P2P@C9RDA03@BRE'1%K9#J#H#B#=#5RF%29RG#GRH#IRI';RJP>P2PFC9RKA03FIRL'1RM%H9#C#<#B#5RN%VHRH';ROP>P2PNC9RPA03NHRQ'1RR%C9#B#F#<#5RS/;IRTP>P2PSC9S00A03SIRU'1RV%C9#F#<#=#L#5RW%IGRG';RXP>P2PWC9S01A03WGRY'1S02%C9#F#<#M#5RZ%IARA';R[P>P2PZC9S03A03ZAR\'1S04%K9#J#<#B#L#5R]/;HR^P>P2P]C9S05A03]HR_'1S06%K9#J#<#=#=#=#5R`/;IRaP>P2P`C9S07A03`IRb'1Rc%H9#C#M#<#5Rd/;IReP>P2PdC9S08A03dIRf'1S09%K9#J#<#B#G#5Rg/;IRhP>P2PgC9S0:A03gIRi'1S0;%H9#C#M#L#K#5Rj/;IRkP>P2PjC9S0<A03jIRl'1S0=%29#J#C#M#<#5Rm/;IRnP>P2PmC9S0>A03mIRo'1S0?%29#=#F#<#=#B#5Rp/;IRqP>P2PpC9S0@A03pIRr'1S0A'1S0B'1S0C,1cS0D'1S0E'1S0F'1S0G'1S0H'1Rs'1Rt'1Ru'1Rv'1PDPEp-0RDg00XNRw#dRx%SwRw1c54Ry%b5Rz%a5R{%E?1`59R95_{R|%^7R}P{P{%EB,:@P9P{P6P7P7P8P2E]R7G71\{8R8P0P3g00Y:R6g00YZR~'[1Z03=Y6~dg00I7=X54CWR~b4b5b6X15W014?0R?A8C43[^15^0DP014>@P=P3O3b3P1PEADlor9Dib9Dbf9D\_9DUY9DLQRCA02@BP0P4n2011000000120000000PEP0b2PMPvPKPLPxPwPyPzP{P|P}P{P{%EIRL,:FP9P7G7P8P~b4b5b6X15X0DA8J43\?^15^0DP014>FP=P3O3b3P1PEPCA02FIREP2PNPHP2PSPIP2PWPGP2PZPAP2P]PHA02`IRJP2PdPIP2PgPIPJP2PjPIP2PmPIP2PpPIE?G>G>F6F6RJ'1P0P0n2011000010120000000RKPCP1PEPJA0>FIP0P4n2011000000120000000PEP0b7b2PRPuPPPQPxPwPyPzP{P|P}P{P{%EHRQ,:NP9P7G7P8P~b4b5b6X15X0DA8O43\?^15^0DP014>NP=P3O3b3PKPCP1PEPJA0>NHREP>PSPIP>PWPGP>PZPAP>P]PHA0>`IROP>PdPIP>PgPIPOP>PjPIP>PmPIP>PpPIE?G>DNF6F6RO'1P0P0n2011000010120000000RPPJP1PEPOA0=NHP0P4n2011000000120000000PEP0b8b7b2PVPtQ00PUPxPwPyPzP{P|P}P{P{1:SLP9P7G7P8P~b4b5b6X15X0DA8T43\?^15^0DP014>SP=P3O3b3PKPCPPPJP1PEPOA0=SIREP=PWPGP=PZPAP=P]PHA0=`IRTP=PdPIP=PgPIPTP=PjPIP=PmPIP=PpPIE?G>G>F6RT'1P0P0n2011000010120000000RUPOP1PEPTA0<SIP0P4n2011000000120000000PEP0b9b8b7b2Q02PsQ01PYPxPwPyPzP{P|P}P{P{%EG,:WP9P7G7P8P~b4b5b6X15X0DA8X43\?^15^0DP014>WP=P3O3b3PKPCPPPJPUPOP1PEPTA0<WGREP<PZPAP<P]PHA0<`IRXP<PdPIP<PgPIPXP<PjPIP<PmPIP<PpPIE?G>DNF6R<'1P0P0n2011000010120000000RXPTP1PEP<A0;WGP0P4n2011000000120000000PEP0b:b9b8b7b2Q04Q0HQ03P\PxPwPyPzP{P|P}P{P{%EA,:ZP9P7G7P8P~b4b5b6X15X0DA8[43\?^15^0DP014>ZP=P3O3b3PKPCPPPJPUPOPXPTP1PEP<A0;ZAREP;P]PHA0;`IR[P;PdPIP;PgPIP[P;PjPIP;PmPIP;PpPIE?G>G>R;'1P0P0n2011000010120000000R[P<P1PEP;f8R\?0ZAP0P4n2011000000120000000PEP0b;b:b9b8b7b2Q06Q0GQ05P_PxPwPyPzP{P|P}P{P{1:]QP9P7G7P8P~b4b5b6X15X0DA8^43\?^15^0DP014>]P=P3O3b3PKPCPPPJPUPOPXPTP[P<P1PEP;A0\]HREA0\`IR^P\PdPIP\PgPIP^P\PjPIP\PmPIP\PpPIE?G>DNR\'1P0P0n2011000010120000000R^P;P1PEP\f9RQ?0]HP0P4n2011000000120000000PEP0b<b;b:b9b8b7b2PcQ0FQ07PbPxPwPyPzP{P|P}P{P{1:`LP9P7G7P8P~b4b5b6X15X0DA8a43\?^15^0DP014>`P=P3O3b3PKPCPPPJPUPOPXPTP[P<P^P;P1PEP\A0Q`IREPQPdPIPQPgPIPEPQPjPIPQPmPIPQPpPIE?DNF6RQ'1P0P0n2011000010120000000RaP\P1PEPQf:RE?0dIRbPEPgPIPEP`PIPEPjPIPEPmPIA0EpIF6F6RE'1P0P0n2011000010120000000R_PQP1PbPEf;RY?0gIRsPYP`PIPYPjPIPYPmPIPYPpPIE?F6Rt'1P0P0n2001000000120000000RVPEP1PsPtf<Ru?0`IRRPuPjPIPuPmPIA0upIF6Rv'1P0P0n2001000000120000000RMPtP1PRPvf=R6?0`IP0P4n2001000000120000000PRP0b@b?b>b=b<b;b:b9b8b7b2CAS07Q09Q0EQ08PfPxPwPyPzP{P|P}P{P{1:dLP9P7G7P8P~b4b5b6X15X0DA8e43\?^15^0DP014>dP=P3O3b3PKPCPPPJPUPOPXPTP[P<P^P;PaP\P_PQP1PbPEA0YdIP0P4n2001000000120000000PbP0b>b=b<b;b:b9b8b7b2CAQ0;Q0DQ0:PiPxPwPyPzP{P|P}P{P{1:gLP9P7G7P8P~b4b5b6X15X0DA8h43\?^15^0DP014>gP=P3O3b3PKPCPPPJPUPOPXPTP[P<P^P;PaP\P_PQPVPEP1PsPtA0ugIP0P4n2001000000120000000PsP0b?b>b=b<b;b:b9b8b7b2PcQ0CQ07Q0=Q0BQ0<PlPxPwPyPzP{P|P}P{P{1:jLP9P7G7P8P~b4b5b6X15X0DA8k43\?^15^0DP014>jP=P3O3b3PKPCPPPJPUPOPXPTP[P<P^P;PaP\P_PQPVPEPMPtP1PRPvA06jIRRP6PmPIP6PpPIE?R6'1P0P0n2001000000120000000RkPvP1PRP6f>Rl?0jIP0P4n2001000000120000000PRP0bAb@b?b>b=b<b;b:b9b8b7b2CAQ0?Q0AQ0>PoPxPwPyPzP{P|P}P{P{1:mLP9P7G7P8P~b4b5b6X15X0DA8n43\?^15^0DP014>mP=P3O3b3PKPCPPPJPUPOPXPTP[P<P^P;PaP\P_PQPVPEPMPtPkPvP1PRP6A0lmIRRA0lpIRl'1P0P0n2001000000120000000RnP6P1PRPlf?Ro?0mIP0P4n2001000000120000000PRP0bBbAb@b?b>b=b<b;b:b9b8b7b2Q0@PrPxPwPyPzP{P|P}P{P{1:pLP9P7G7P8P~b4b5b6X15X0DA8q43\?^15^0DP014>pP=P3O3b3PKPCPPPJPUPOPXPTP[P<P^P;PaP\P_PQPVPEPMPtPkPvPnP6P1PRPlA0opIP0P0n2001000000120000000PlP0bBbAb@b?b>b=b<b;b:b9b8b7b2CAF@FUF@FUF@F@F@F@F@F@F@P5P5P>P2Ci=h:3R:P@PBP:PFPIP:PNPHP:PSPIP:PWPGP:PZPAP:P]PHA0:`IR`P:PdPIP:PgPIP`P:PjPIP:PmPIP:PpPIE?G>G>F6F6F6e%O:eWCWDWEXF5XG5o"). Qed.
Lemma ashsafe_cons_file : forall lo hi W, 0xb3fb0 <= lo -> hi <= 0xba2f8 -> ashsafe W -> ashsafe ((lo, hi) :: W).
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio_kit ()) ["CANSEC1"] "h04__p1h14__x1h21Hh37__arithh44__ffh58__varmaph65__with72H0h82H3h92H4h:2H5h;2H6h<2H7h=2H8h>2H9h?3H10h@3H11hA3H12hB3H13hC1DhD2H1hE2H2hF1WhG2hihH2lop%0p;2p;1p;3p;6p;4p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8g00IUj2nTg000nj1ZTg00J5j24Tg00AUj1STg00JQj27Tg00BQj30Tg00<kR1j21Tg001Nj12Tg00CMj1LTg00>gj1hTg00Jnj2gTg00KLj1fTg00Kjj1eTg00LUj2TTg00M8j1dTg00MZj6cTg00N>j2bTg00N`j2aTg00O:j2`Tg00Ofj3_Tg00P@j3^Tg00P_j4]Tg00Z:j1mTg00ZXj4lTg00Ckj4ATg00QQj4kTg00E;j3jTg00?Gj13Tg00R1j2QTg00RKj2XTg00Rnj4WTg00SYj7VTg00T=j3iTg00T`j7UTg00UDj8[Tf0R0#2#3#3#2p=D%20#3#3#3p=F%30#3#3#3p=9%20#2#2#Lp=5%20#3#2#2p=E%20#3p=:%20#2p=K%30#2p=@%30#3p=P%20#Lp=\f3R2f2R3'4f1R4/40'Qp=8%30#2#2#3p=H%30#3#2#3p=R%30#3#2#2p=Ng00;XR5/X0p=>P3g00UhR6g00VGR7P7g00VgR8P5P4g00WGR9P0CWg00WnR:FVp=G1X54=i50p=?f7R;P6P7P7P8f6R<f5R=f4R>P6P7P7P8P2P6P7P7P8P5P3P9P4CWP:FVP0FUG[p=C1434/Q0p=B1140,13p=IA0=>2A0340'1p=<A0;<=A0234/10,1>'1p=;A0<=>A0234/10'1p=6A0234/10,1>p=OP=P6P7P7P8P>P2P3P6P7P7P8P4P0FUG[p=J1440,Q3p=MP<P=P>P2P3P4CAP0CAp==P<P=P>P2P3P4P0CACAp=Y1n55S00#Zg00;3R:#D#F#9#D#5R9/43%F:#E#:#:#9#5R?,43%S3%D:#E#K#@#K#P#5R@%@:#KRA#\RB'7RCP=P>P@C8RDA02@BRE'1%::#H#D#E#@#5RF%2:RG#KRH#LRI'7RJP=P>PFC8RKA02FIRL'1RM%D:#F#9#E#5RN%\HRH'7ROP=P>PNC8RPA02NHRQ'1RR17?IRSP=P>P?C8RTA02?IRU'1RV%::#R#:#9#@#P#5RW%LGRX'7RYP=P>PWC8RZA02WXR['1R\%::#R#:#9#N#5R]%LARA'7R^P=P>P]C8S01A02]AR_'1S02%::#H#9#E#P#5R`/7HRaP=P>P`C8S03A02`HRb'1S04%::#H#9#@#@#@#5Rc/7IRdP=P>PcC8S05A02cIRe'1Rf%D:#F#N#9#5Rg/7IRhP=P>PgC8S06A02gIRi'1S07%::#H#9#E#K#5Rj/7IS08P=P>PjC8S09A02jIRk'1S0:%D:#F#N#R#5Rl/7IS0;P=P>PlC8S0<A02lIRm'1S0=%2:#H#F#N#9#5Rn/7IS0>P=P>PnC8S0?A02nIRo'1S0@%2:#H#:#9#@#E#5Rp/7IS0AP=P>PpC8S0BA02pIRq'1S0C'1S0D'1S0E,1fS0F'1S0G'1S0H'1S0I'1Rr'1Rs'1Rt'1Ru'1Rv'1PDPEp-0RDg00XNRw#hRx%ZwRw1g54Ry%f5Rz%e5R{%>91T5:R:5G{R|%d7R}P{P{%>B,?@P:P{P6P7P7P8P2EcR7GC1b{8R8P0P3g00Y:R6g00YZR~'a1`03=_6~dg00I7=^54C]R~b4b5b6X15W01490R9ABC43[^15^0DP014=@P<P2O3b3P1PEAImoq9Ike9Iei9I_b9IU[9ILQRCA0>@BP0P4n2011000000120000000PEP0b2PMPvPKPLPxPwPyPzP{P|P}P{P{%>IRL,?FP:P7GCP8P~b4b5b6X15X0DABJ43\9^15^0DP014=FP<P2O3b3P1PEPCA0>FIREP>PNPHP>P?PIP>PWPXP>P]PAP>P`PHA0>cIRJP>PgPIP>PjPIPJP>PlPIP>PnPIP>PpPIE<G;G;F6F6RJ'1P0P0n2011000010120000000RKPCP1PEPJA0=FIP0P4n2011000000120000000PEP0b7b2PRPuPPPQPxPwPyPzP{P|P}P{P{%>HRQ,?NP:P7GCP8P~b4b5b6X15X0DABO43\9^15^0DP014=NP<P2O3b3PKPCP1PEPJA0=NHREP=P?PIP=PWPXP=P]PAP=P`PHA0=cIROP=PgPIP=PjPIPOP=PlPIP=PnPIP=PpPIE<G;DOF6F6RO'1P0P0n2011000010120000000RPPJP1PEPOA0<NHP0P4n2011000000120000000PEP0b8b7b2PVPtPTPUPxPwP5PyP4%m5ClRUPzP{1T5GRG%>?5G{RTP}P{P7PTEJP8P~b4b5b6X15X0D140?RtAM34?[^15^0DP014S<P=P3O3b3PKPCPPPJP1PEPOA0<?IREP<PWPXP<P]PAP<P`PHA0<cIRSP<PgPIP<PjPIPSP<PlPIP<PnPIP<PpPIE<G;G;F6RS'1P0P0n2011000010120000000RVPOP1PEPSA0;?IP0P4n2011000000120000000PEP0b9b8b7b2P\PsPZP[PxPwPUPzP{PTP}P{P7%>W9G{GEJP8P~b4b5b6X15X0DAM34W\t^15^0DP014Y<P=P3O3b3PKPCPPPJPVPOP1PEPSA0;WXREP;P]PAP;P`PHA0;cIRYP;PgPIP;PjPIPYP;PlPIP;PnPIP;PpPIE<G;DOF6R;'1P0P0n2011000010120000000RYPSP1PEP;f8R[?0WXP0P4n2011000000120000000PEP0b:b9b8b7b2Q02PrQ01P_PxPwPUPzP{PTP}P{P7%>]9G{GEJP8P~b4b5b6X15X0DAM34]\t^15^0DP014^<P=P3O3b3PKPCPPPJPVPOPYPSP1PEP;A0[]AREP[P`PHA0[cIR^P[PgPIP[PjPIP^P[PlPIP[PnPIP[PpPIE<G;G;R['1P0P0n2011000010120000000R^P;P1PEP[f9R_?0]AP0P4n2011000000120000000PEP0b;b:b9b8b7b2Q04Q0IQ03PbPxPwPyPzP{P|P}P{P{1?`QP:P7GCP8P~b4b5b6X15X0DABa43\9^15^0DP014=`P<P2O3b3PKPCPPPJPVPOPYPSP^P;P1PEP[A0_`HREA0_cIRaP_PgPIP_PjPIPaP_PlPIP_PnPIP_PpPIE<G;DOR_'1P0P0n2011000010120000000RaP[P1PEP_f:RQ?0`HP0P4n2011000000120000000PEP0b<b;b:b9b8b7b2PfQ0HQ05PePxPwPyPzP{P|P}P{P{1?cLP:P7GCP8P~b4b5b6X15X0DABd43\9^15^0DP014=cP<P2O3b3PKPCPPPJPVPOPYPSP^P;PaP[P1PEP_A0QcIREPQPgPIPQPjPIPEPQPlPIPQPnPIPQPpPIE<DOF6RQ'1P0P0n2011000010120000000RdP_P1PEPQf;RE?0gIRePEPjPIPEPcPIPEPlPIPEPnPIA0EpIF6F6RE'1P0P0n2011000010120000000RbPQP1PePEf<Rr?0jIRZPrPcPIPrPlPIPrPnPIPrPpPIE<F6Rs'1P0P0n2001000000120000000R\PEP1PZPsf=Ru?0cIRRPuPlPIPuPnPIA0upIF6Rv'1P0P0n2001000000120000000RMPsP1PRPvf>R6?0cIP0P4n2001000000120000000PRP0b@b?b>b=b<b;b:b9b8b7b2CAS05Q07Q0GQ06PiPxPwPyPzP{P|P}P{P{1?gLP:P7GCP8P~b4b5b6X15X0DABh43\9^15^0DP014=gP<P2O3b3PKPCPPPJPVPOPYPSP^P;PaP[PdP_PbPQP1PePEA0rgIP0P4n2001000000120000000PeP0b>b=b<b;b:b9b8b7b2CAQ0:Q0FQ09PkPxPwPyPzP{P|P}P{P{1?jLP:P7GCP8P~b4b5b6X15X0DQ08?B43\9^15^0DP014=jP<P2O3b3PKPCPPPJPVPOPYPSP^P;PaP[PdP_PbPQP\PEP1PZPsA0ujIP0P4n2001000000120000000PZP0b?b>b=b<b;b:b9b8b7b2PfQ0EQ05Q0=Q0DQ0<PmPxPwPyPzP{P|P}P{P{1?lLP:P7GCP8P~b4b5b6X15X0DQ0;?B43\9^15^0DP014=lP<P2O3b3PKPCPPPJPVPOPYPSP^P;PaP[PdP_PbPQP\PEPMPsP1PRPvA06lIRRP6PnPIP6PpPIE<R6'1P0P0n2001000000120000000R9PvP1PRP6f?R:?0lIP0P4n2001000000120000000PRP0bAb@b?b>b=b<b;b:b9b8b7b2CAQ0@Q0CQ0?PoPxPwPUPzP{PTP}P{P7%>n9G{GEJP8P~b4b5b6X15X0DAM34n\t^15^0DP0Q0>/4<P=P3O3b3PKPCPPPJPVPOPYPSP^P;PaP[PdP_PbPQP\PEPMPsP9PvP1PRP6A0:nIRRA0:pIR:'1P0P0n2001000000120000000RoP6P1PRP:f@RL?0nIP0P4n2001000000120000000PRP0bBbAb@b?b>b=b<b;b:b9b8b7b2Q0BPqPxPwPUPzP{PTP}P{P7%>p9G{GEJP8P~b4b5b6X15X0DAM34p\t^15^0DP0Q0A/4<P=P3O3b3PKPCPPPJPVPOPYPSP^P;PaP[PdP_PbPQP\PEPMPsP9PvPoP6P1PRP:A0LpIP0P0n2001000000120000000P:P0bBbAb@b?b>b=b<b;b:b9b8b7b2CAF=FYF=FYF=F=F=F=F=F=F=Q00P5P5P=P>Ck;j2R2P@PBP2PFPIP2PNPHP2P?PIP2PWPXP2P]PAP2P`PHA02cIRcP2PgPIP2PjPIPcP2PlPIP2PnPIP2PpPIE<G;G;F6F6F6e%S2eWCWEWDWFXG5XH5o"). Qed.
Lemma ashsafe_nil : ashsafe [].
Proof. repeat split. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hull64 (lo hi RLO RHI : Z) : Prop :=
  RLO <= lo /\ hi <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND.

Definition shclean (m : word -> option byte) (lo hi RLO RHI : Z) : Prop :=
  unpoisoned m lo hi /\ hull64 lo hi RLO RHI /\ wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ app_blk lo hi.

Lemma shclean_sub : forall m lo hi RLO RHI lo' hi',
  shclean m lo hi RLO RHI -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> shclean m lo' hi' RLO RHI.
Proof.
  intros m lo hi RLO RHI lo' hi' (U & (H1 & H2 & H3) & W & AB) Hlo Hm Hhi. split; [| split; [| split; [exact W|]]].
  - eapply unpoisoned_sub; [exact U| lia| lia].
  - unfold hull64 in *. lia.
  - eapply app_blk_sub; eauto.
Qed.

Lemma shclean_hull : forall m lo hi RLO RHI, shclean m lo hi RLO RHI ->
  RLO <= lo /\ hi <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND.
Proof. intros m lo hi RLO RHI (_ & H & _). exact H. Qed.
Lemma shclean_unpoisoned : forall m lo hi RLO RHI, shclean m lo hi RLO RHI -> unpoisoned m lo hi.
Proof. intros m lo hi RLO RHI (H & _). exact H. Qed.
Lemma shclean_wr : forall m lo hi RLO RHI, shclean m lo hi RLO RHI -> wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
Proof. intros m lo hi RLO RHI (_ & _ & H & _). exact H. Qed.
Lemma shclean_app_blk : forall m lo hi RLO RHI, shclean m lo hi RLO RHI -> app_blk lo hi.
Proof. intros m lo hi RLO RHI (_ & _ & _ & H). exact H. Qed.

(* [comment removed for export] *)
Lemma shclean_transport : forall W m m' lo hi RLO RHI,
  shclean m lo hi RLO RHI -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W (shad RLO) (shad RHI - shad RLO) -> lo < hi ->
  shclean m' lo hi RLO RHI.
Proof.
  intros W m m' lo hi RLO RHI (U & H & WR & AB) MU WM D LT. split; [| split; [exact H| split; [eapply wr_at_transport; eauto| exact AB]]].
  eapply unpoisoned_munch; [exact U| exact MU|].
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
  assert (S1 : shad RLO <= shad lo) by (apply shad_mono; lia).
  assert (S2 : shad (hi - 1) + 1 <= shad RHI).
  { rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
  revert D. clear - S1 S2. induction W as [|[a b] W IH]; cbn [disjoint_from]; [auto|].
  intros [D1 D2]. split; [lia| apply IH; exact D2].
Qed.

(* [comment removed for export] *)
Lemma shclean_empty : forall m lo RLO RHI,
  hull64 lo lo RLO RHI -> wr_at bsegs m (shad RLO) (shad RHI - shad RLO) -> app_blk lo lo -> shclean m lo lo RLO RHI.
Proof.
  intros m lo RLO RHI H W AB. split; [| split; [exact H| split; [exact W| exact AB]]].
  destruct H as (H1 & H2 & _ & _ & H5 & H6). unfold KEND in H6.
  apply unpoisoned_nil. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition appW (W : list (Z * Z)) : Prop := Forall (fun iv => snd iv <= KLOW \/ KHIGH <= fst iv) W.

Lemma appW_shadow_disjoint : forall W RLO RHI, appW W -> 0 <= RLO -> RHI <= KEND ->
  disjoint_from W (shad RLO) (shad RHI - shad RLO).
Proof.
  intros W RLO RHI HW H0 H1. induction HW as [|[a b] W Hab HW IH]; cbn [disjoint_from]; [exact I|].
  cbn [fst snd] in Hab. split; [| exact IH].
  rewrite !shad_div. unfold ASHOFF, KLOW, KHIGH, KEND in *. Z.div_mod_to_equations. lia.
Qed.

Lemma shclean_transport_app : forall W m m' lo hi RLO RHI,
  shclean m lo hi RLO RHI -> munch W m m' -> wmono bsegs m m' -> appW W -> lo < hi -> shclean m' lo hi RLO RHI.
Proof.
  intros W m m' lo hi RLO RHI SH MU WM HW LT. pose proof (shclean_hull _ _ _ _ _ SH) as (_ & _ & _ & _ & H0 & H1).
  eapply shclean_transport; eauto. apply appW_shadow_disjoint; auto.
Qed.

Lemma appW_cons : forall a b W, (b <= KLOW \/ KHIGH <= a) -> appW W -> appW ((a, b) :: W).
Proof. intros a b W H HW. constructor; [exact H| exact HW]. Qed.
Lemma appW_nil : appW [].
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio_kit ()) ["CANSEC1"] "h02ivp;2p;3p-1R0g01BnR1p4p710p8P0g01:jR2p4p710p8P0P2p4p7210p8g00IUj25TP2j34Tg00J5j20Tg000Qj31Tg00R1j23TP1j22Tg00;XR1/51R2f0R09411g01=R'0g01>GA1110'0'3X02'2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region := mkRegion { r_lo : Z; r_hi : Z; r_rlo : Z; r_rhi : Z }.

(* [comment removed for export] *)
Definition rclean (m : word -> option byte) (r : region) : Prop :=
  shclean m (r_lo r) (r_hi r) (r_rlo r) (r_rhi r) /\ r_lo r < r_hi r.
(* [comment removed for export] *)
Definition rrng (RNG : footprint) (r : region) : Prop := rng RNG (shad (r_rlo r)) (shad (r_rhi r) - shad (r_rlo r)).
(* [comment removed for export] *)
Definition inreg (r : region) (a n : Z) : Prop := r_lo r <= a /\ a + n <= r_hi r.

Lemma rclean_transport : forall W m m' r,
  rclean m r -> munch W m m' -> wmono bsegs m m' -> appW W -> rclean m' r.
Proof. intros W m m' r [SH LT] MU WM HW. split; [| exact LT]. eapply shclean_transport_app; eauto. Qed.

Lemma rclean_shclean : forall m r, rclean m r -> shclean m (r_lo r) (r_hi r) (r_rlo r) (r_rhi r).
Proof. intros m r [H _]; exact H. Qed.
Lemma rclean_lt : forall m r, rclean m r -> r_lo r < r_hi r.
Proof. intros m r [_ H]; exact H. Qed.
Lemma inreg_sub : forall r a n a' n', inreg r a n -> a <= a' -> a' + n' <= a + n -> inreg r a' n'.
Proof. unfold inreg. intros. lia. Qed.

(* [comment removed for export] *)
Definition RBstdout : region := mkRegion 0x60d9a0 0x60dda0 0x60d980 0x60ddc0.
Example RBstdout_hull64 : 0x60d980 mod 64 = 0 /\ 0x60ddc0 mod 64 = 0 /\ 0x60d980 <= 0x60d9a0 /\ 0x60dda0 <= 0x60ddc0.
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio_kit ()) ["CANSEC1"] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;3p;4p;7p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8g00CMj15Tg00`4j2>Tg00Ofj39Tg00J5j2@Tg00<kj2=Tg00N`j2<Tg00>gj1BTg000nj1ATg00Z:j1JTg00KLj1ITg00Kjj1HTg00RKj27Tg00Rnj4?Tg00N>j2GTg00O:j2FTg00P@j3ETg00P_j4DTg00Ckj48Tg00?Gj16Tg001Nj12Tg00SYj7CTf0R1#6#2p=0%21#2#2#2p=1%61#6p=4%21#6p=3%21#2p=:f1R0g00Uhg00VGR2P2g00VgR2P1g00WnFCp=;g00;XR3g00;3R4#0#1#4#3#0#3#0#:#1#5R5%:4#1#5R6'>g00I7R739%04#1#4#3#4#3#4#:#1#5R8/>6=937R6%04#1#4#3#0#3#0#0#1#5R9,@5R:%04#1#4#3#4#3#0#0#1#5R4/@8R;'=R<'=1<37R=P6P<P=P:P;g00XNR=#BR<%A=R=%J3R6%I3R>%H3R?P31735g00WGR51739C?';1G?2R2P1f2R9g00Y:R@g00YZRA'<1F19=9@AdAE370CDR7b1b2b3P:P1b0P<P=P6P>P31734P51738C?,;?P2P7b1b2b3P;P1b0C8C8C8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End CANSEC1.
Ltac solve_ashsafe :=
  repeat first [ apply ashsafe_nil
               | apply ashsafe_cons_high; [unfold KHIGH in *; lia|]
               | apply ashsafe_cons_file; [lia| lia|]
               | (* [comment removed for export] *)
                 unfold ashsafe; cbn [disjoint_from]; unfold KHIGH in *; repeat split; lia ].
Ltac solve_appW :=
  repeat first [ apply appW_nil
               | apply appW_cons; [unfold KLOW, KHIGH in *; cbn [fst snd]; first [lia | left; lia | right; lia] |] ].

(* [comment removed for export] *)
Tactic Notation "xport_env" constr(ENV) constr(MU) constr(WM) "as" ident(X) :=
  pose proof (ashenv_transport _ _ _ ENV MU WM ltac:(solve_ashsafe)) as X.
(* [comment removed for export] *)
Tactic Notation "xport_reg" constr(RC) constr(MU) constr(WM) "as" ident(X) :=
  pose proof (rclean_transport _ _ _ _ RC MU WM ltac:(solve_appW)) as X.
