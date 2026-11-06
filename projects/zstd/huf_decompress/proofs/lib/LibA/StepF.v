(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export PropExec MState Mem Cells Exec Step Frame Arr Image Tac Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export StoreFast Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Export ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_StepF () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesc59OSSVerify5KrLib4LibA5StepF<lift_resultFC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib4Init5Logic4True01I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem5is_x0C4ELinuxProcessSemantics5Riscv3Sem7reg_getC59OSSVerify5KrLib3Lib6MState5MSsvcC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib4LibA5ExecF<rng_acc_litZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List9nth_errorC56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesC47Corelib4Init5Peano2ltI47Corelib4Init5Peano2le00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List>nth_error_NoneC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00c59OSSVerify5KrLib4LibA5StepF?stepF_ecall_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF=evtF_step_accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lift_resultF (ro : word -> option byte)
    (r : machine_result (access_report (core * (word -> option byte))))
  : machine_result (access_report machine_state) :=
  match r with
  | MachineOk (mkAccessReport _ (c, m') accs) => MachineOk (mkAccessReport _ (MS_of_core c m' ro) accs)
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

Lemma stepF_gen : forall segs R F pc fc rv m ro w i sz,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  RiscvSemantics.step_accesses segs (MS R F pc fc rv m ro) =
  lift_resultF ro (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m).
Proof.
ltac2:(KReplay.run1 (kr_t_StepF ()) [] "p'0h01oi001oh11Fh22Hdh32Heh42Hfh51Rh63acch7<access_valuei01<access_valueh8?accessed_rangesi02?accessed_rangesh91bh:1ci031ch;2fch<1ii041ih=1mi051mh>2m'i062m'h?2m0h@2pchA6resulti076resulthB2rohC2rvhD4segshE2szhF1wi081wi091ai0:3iszi0;1pi0<6reporti0=3st'i0>1xp;1p;2p;3p;4p;7p;5p;8p;6g0000R0p4p7210g000\R1p4p710p8g001:j1XTg001Zj16Tg002?j1QTg002dj1<Tg003Bj1DTP0j2aTg003eR0j1:Tg004Gj2BTg005Ij27Tg005kj30Tg006Ej1NTg007ER2j2MTg007ej1>Tg008Vj4JTg0096R3j1WTg00:=R4j1VTg00;Ej75Tg00<7j3ITg00=Cj1CTg00>Aj3TTg00?Fj3STg00@Lj3RTg00AQj1]Tg00B1j21Tg00C9j1PTg00DAj1OTg00EIj2GTg00Eoj59Tg00FXj3=Tg00G?j38Tg00HJj22Tg00IFj1?Tg00JEj1FTg00KEj1@Tg00LFj1\Tg00Ldj3[Tg00MGj2ZTg00NEj1ETg00ODj1HTg00PCj1LTg00QAj84Tg00RHj2YTg00SLj1gTg00T5j1fTg00T_j1eTg00UFj1dTg00Uhj1cTg00VQj1bTg00W:j2UTg00XAj1`Tg00Y:j3;Tg00ZAj2KTP1j6ATg00Z[j1_Tg00[Xj2^Tg00\]R1f1R5f0R63;p=3g00]d#Xg00^c#6R7#Q#<R8%67#6R7#6#6R9#6#<R:#DR;'aR<%<9#DR9%:;%<7#D#:\;R=g00_HR>g00`4R?%:9R@f:RAf7RB'Bf2RC,7930g00`RRDf3RE#Ng00a2RF301M>?RG#:RHf4RI#>P>P?PEPCCJ,7G30P@f5RJ,79%W1RK#VRLP0P9PLP6f?RMf>RNf=ROf<RPf;RQPAf9RRf8RSF5;I6RTP0P9PLPOPPPQPAPRPSPBF5RU#CRV=TNQPTP0P9PLASNVQPTP4P1PLARNVQg00aRRT#]RW,36,1KRX%PKRY%OKRZn10110>00031010=0000n10110>00021010800n10110>00021010800n10110>000210108001G:IPOPPPQPAPRD97=J=8NS,2BR[30X0@PDPFPDPLP6%?U%FU%@U%Q7#\g00bW5[8,ZU,7;%EU%HUPV%LUG4/3W,1KP0PGPLf6RW#>P2P>P?PLP6P4g00c3RV/M=R8#WR7PLfARF1G:6f@R@PMPNPOPPPQPAF5R\#?%F\%@\%H\%E\D97=5%C\38P2PVP=PL1Y86R\%g5R]%f5R^%e5R_%d;R`%c5Ra%b5RbP6fCfBPFP@PMPNPOF5#LG41U8CRc'3,1Kn200110>000120103106PYPZn10110>00031010<0000n200110;00012110410:RdPDPL%`WPYPZn0100000020000Ren10110>00021110;00n0100000020001=0L[X9DPHP>P?PIPECJ,7GP0PGPLP6PdPen10110>00021110;00=0L[X0H1G:ER:PPPQPAPRPSD97=I=8OBRH%V7P4P7P4P7PLP6P2PVP=PLP\P]P^P_P`PaPbP6PQG4/3c,1Kn200110>000120103106PYPZn10110>00031010<000012S650LP6P3P8P2PVP=PLP\P]P^P_P`PaPbP6PPG4/3c,1Kn200110>0001201031061176,2A50LP6P2PVP=%XTRTP2PVP=PLA;856R3,Y8P]P^P_P`PaPbP6P@G4A;8EC,U8'3,1Kn200110>0001201031061173,2N50L]8P6PVP=PCP5CJ=;86,17,2F,KLX6TX>=X:VP5P6O2n200110;010120103100X78P5P6O2n101109000121101102XA7P6O1%P7,2B,KL%O7,2B,KLn1011050003111070000b?P4P7PLPPPQPAPRPSPBPWF5RB#?%FB%@B%HB%EBD99=:I%CBR:58OP2PVP=PLP\P]P^P_P`PaPbP6PMPNPOPPPQPAPRF5#LG4/3c,1Kn200110>000120103106PYPZn10110>00031010<000012WHRH50Le%>JP6EA%NJP5EAAIOBJ=0LHe1BOAPCEAP0P9PL%_BRC,BOAINU6RUP0P9PLATO:CPUP0P9PLASO:CPUP4P1PLARO:CPXPYPZn10110>00031010=0000n10110>00021010800n10110>00021010800n10110>00021010800=0LHe1^OB=0LHeW2W3W4WEW<XF9XB=W=WCW;X@;X1<W5WDo"). Qed.

(* [comment removed for export] *)
Lemma stepF_ecall_gen : forall segs R F pc fc rv m ro w,
  fetch_word segs pc = Some w ->
  is_ecall w = true ->
  RiscvSemantics.step_accesses segs (MS R F pc fc rv m ro) =
  MachineOk (mkAccessReport _ (MSsvc R F pc (if is_x0 17 then w0 else reg_get R 17) fc rv m ro) []).
Proof.
ltac2:(KReplay.run1 (kr_t_StepF ()) [] "p'0h01Fh12Heh22Hfh31Rh41bh52fch61mh71oh82pch92roh:2rvh;4segsh<1wi001wi011ci021ii033iszi042m'i051pi066reporti073st'i081xp;1p;2p;3p;7p;8p;5p;6g001:j1iTg001Zj12Tg002?j1GTg002dj15Tg003Bj1;Tg0000j2ZTg003eR0j1:Tg004Gj27Tg005Ij28Tg005kj30Tg006Ej1@Tg0096j1?Tg00:=R1j1OTg00;Ej74Tg00<7j36Tg00=Cj1=Tg00>Aj3ITg00?Fj3MTg00@Lj3NTg00AQj1VTg00B1j21Tg00C9j1STg00DAj1RTg00LFj1QTg00Ldj3CTg00c\j1HTg00dDj29Tg00dnj8<Tg00IFj1BTg00JEj1JTg00KEj1ATg00MGj2PTg00NEj1>Tg00ODj1ETg00PCj1FTg00QAj8DTg007ER2j2LTg007ej1TTg00EIj2UTg00Eoj5hTg00FXj3gTg00G?j3fTg00RHj2cTg00SLj1bTg00T5j1`Tg00T_j1]Tg00UFj1\Tg00Uhj1[Tg00VQj1YTg00W:j2^Tg00XAj1_Tg00ZAj2XTg000\j6KTg00Z[j1aTg00[Xj2WTg00ecj2dTg00Y:j3eTg00\]R3f1R4f0R53ep=3g00]d#ig00^c#2R6#G#5R7%26#2R6#2#2R8#2#5R9#;R:'ZR;%58#;R8%::%56#;#:\:R<%:8R=f8R>f5R?'7188530g00`RR@%@4g00fFRA30P=f2RB,88%?3RC#ORDP0P8PDP5f<REf;RFf:RGf9RHP>f7RIf6RJP?F4;65RKP0P8PDPGPHP>PIPJP?f4RLF4RM#=RN=IF>PKP0P8PDAMFN>PKP1P3PDANFN>g00aR#VRK,35,1CRO%SCRP%RCRQn1011080003101070000n10110800021010000n10110800021010000n10110800021010000PGPHP>P@P:%G6#QR6g00bWRR5C7RS#HRTg00ffRU19GSn0100000020000PIPJP?PLG</3K,1CRV30X7=P@PAP@PDP5%BM%JM%AM1PMS,8:%>M%EMPN%FMGD/3K,1CP0g00_HRNg00`4RA'LPDf3R=#TP2PNPAPDP5P1g00c3RA/L<RN#?PDf>RW1U95f=R9PEPFPGPHP>PIF4RX#B%JX%AX%EX%>XDh7g4%=X3fP2PAP<PD1cN5%b4%`4%]4%\:%[4%Y4P5f@f?PWP9PEPFPGF4#FGD1^NB'3,1Cn2001108000120101104PPPQn1011080003101060000n2001105000121102103P@PD%_=PPPQn0100000020000n10110800021110500n0100000020001=0DVX4@PHP>PIP@P:PTPU19HSn0100000020000PJP?PLP=G</3K,1CRS,XD%@BP5EKPHP>PIPJP?PLP=F4RT=6GB=0DSe17GIP4EKP0P8PD%aTR4,7GA6FM5RMP0P8PD%=TRF=IG4PMP0P8PDAMGF4PMP1P3PDANGF4POPPPQn1011080003101070000n10110800021010000n10110800021010000n10110800021010000=0DSe1WGTPHP>PIP@P:PR1d76d9C76R6#HPU19H6n0100000020000PJP?PLP=G</3K,1C50DeW1W2X<8X9<W6W:W5X8:X0;W3W;o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rng_acc_litZ' : forall RNG lo len E (n : nat) (nz : Z),
  rng RNG lo len -> Z.of_nat n = nz -> (1 <=? nz)%Z = true -> (lo <= E /\ E + nz <= lo + len)%Z ->
  acc_in RNG (Z_to_bv 64 E, n).
Proof.
ltac2:(KReplay.run1 (kr_t_StepF ()) [] "h01nh11mh21Eh31Hh42H0h52HEh62Hnh72Hzh83RNGh93lenh:2loh;2nzp;3p;1p;2p;:g00gKj3:Tg00h>j19Tg005kj34Tg00LFj15Tg00h^j22Tg00i;j20Tg00iWj23Tg00j4R0j26Tg00jOj27Tg00jol:8Tg00`Rf0R1g00fF34p=1g00kkg00`4R2g00ldf5R3f4R4f3R53:f2R6#9f1R7542g00^c#5R8/26#1f7R9/031335f6R:,39'0'6f9f8P9P:P3P4P5P6P01271#11067[R010711267#1R4[1056\41771P7n2001000000120000000X12X02P0^12^02P1P8P3P6O3b4P1M:8W5W7W6W3X;2W0X22X92W:W8o"). Qed.

(* [comment removed for export] *)
Ltac acc_hint := fail.

(* [comment removed for export] *)
Lemma nth_error_some_bound : forall {A} (l : list A) k x, nth_error l k = Some x -> (k < length l)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_StepF ()) [] "p'0h01Ah11Lh21lh32H0h41nh51Hh63Heqh71eh81kh91oi001oh:1xp;1p;3p;2p;4p;6p200R0g005kR1p4p710p8P0g00mCR2p4p710p8P0g00m_R3p4p710p8P0g00n=R4p4p710p8P0g00n]p4p710R5p8g001:j1?Tg003eR6j12Tg00o8j34Tg005Ij27TP1j33TP4j21Tg00oVj2;Tg010>j26Tg010Vj25Tg0110R4j29Tg00UFj10Tg011Jj38Tg011mj4:TP3j6>TP2j6=Tg012Ij2<Tf0R2#?R3g00ldR1f2R7f3R8#2R9f1R:9487R;178233f4R</18R=,;7167=15=7'9P4f5R4/1<R=,6815=8f6R=/14R>,6<R?P2P2X1?P2O115><g00j4%27A47:2%07331187/5:R>[117:/52%08939;[R;%2<A4<87%0<33\>A87:2P2n2001000000120000000X41X23X05P;^41^23^05P2f8R5f7R3P=P:O4%25A453=%0533f9R:#2R1%0:R;A4:53R517:=R=P1P5P;P2C:P4E>A31;=f:R=#2R;%0=P6f;R6p-0P2g012hR1g013En10110000021000000X7;g00bW17=3P2E=P1116=,6:/<2b3b6b1b3W1P2O1n200100000021000010000b9W5W:W8W2X00o"). Qed.

Ltac acc_enrich :=
  repeat match goal with
  | H : nth_error ?l ?k = Some ?x |- _ =>
      lazymatch goal with
      | _ : (k < length l)%nat |- _ => fail
      | _ => pose proof (nth_error_some_bound l k x H)
      end
  end;
  rewrite ?u32s_length, ?u64s_length, ?length_app, ?repeat_length in *;
  cbn [length] in *.

Ltac alia := first [ lia | acc_enrich; lia ].

(* [comment removed for export] *)
Ltac solve_acc_with H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia
      end
  end.

(* [comment removed for export] *)
Ltac leftmost E := lazymatch E with Z.add ?X _ => leftmost X | Z.sub ?X _ => leftmost X | _ => E end.

(* [comment removed for export] *)
Ltac is_closed_lits E :=      (* [comment removed for export] *)
  lazymatch E with
  | Z.add ?a ?b => is_closed_lits a; is_closed_lits b
  | Z.sub ?a ?b => is_closed_lits a; is_closed_lits b
  | _ => is_Zlit E
  end.
Ltac decide_lit_bounds :=      (* [comment removed for export] *)
  lazymatch goal with
  | |- (?a <= ?b /\ ?c <= ?d)%Z => split; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity
  end.
(* [comment removed for export] *)
Ltac solve_acc_lit H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); decide_lit_bounds
      end
  end.
(* [comment removed for export] *)
Ltac mentions T X := lazymatch T with context [X] => idtac end.

Ltac solve_acc1 :=
  first [ acc_hint
        | assumption
        | (* [comment removed for export] *)
          lazymatch goal with
          | |- acc_in ?RNG (Z_to_bv 64 ?E, _) =>
              is_closed_lits E;
              match goal with
              | H : rng RNG ?lo ?len |- _ => is_closed_lits lo; is_closed_lits len; solve_acc_lit H
              end
          end
        | (* [comment removed for export] *)
          lazymatch goal with
          | |- acc_in ?RNG (?a, _) =>
              let E := addr_expr a in let X := leftmost E in
              first [ match goal with
                      | H : rng RNG ?lo _ |- _ => let Y := leftmost lo in constr_eq X Y; solve_acc_with H
                      end
                    | is_var X;
                      match goal with
                      | H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X]; solve_acc_with H
                      end
                    | lazymatch X with bv_unsigned ?r => is_var r;
                        match goal with
                        | H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X]; solve_acc_with H
                        end
                      end ]
          end
        | lazymatch goal with
          | |- acc_in ?RNG _ =>
              match goal with
              | H : rng RNG _ _ |- _ => solve_acc_with H
              end
          end
        | (* [comment removed for export] *)
          lazymatch goal with
          | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
              let nz := eval cbv in (Z.of_nat n) in
              match goal with
              | H : rng RNG ?lo ?len |- _ => apply (rng_acc_wrapZ RNG lo len E n nz H (@eq_refl Z nz)); alia
              end
          end
        | lazymatch goal with |- acc_in _ (?a, ?n) => fail 0 "footprint: access" a "width" n "not covered by any [rng] hypothesis" end ].

Ltac solve_accs :=
  lazymatch goal with
  | |- Forall _ nil => apply Forall_nil
  | |- Forall _ (cons _ _) => apply Forall_cons; [ solve_acc1 | solve_accs ]
  | |- ?G => fail 0 "solve_accs: unexpected access side goal" G
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac reglia :=
  first [ lia
        | rewrite ?unsigned_lit by lia; lia
        | rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

Ltac solve_rng :=
  lazymatch goal with
  | |- rng ?RNG ?lo' ?len' =>
      first [ assumption
            | eassumption
            | tryif match goal with |- ?G => has_evar G end
              then fail 0 "solve_rng: goal has evars:" lo' len'
              else first [ (* [comment removed for export] *)
                           is_closed_lits lo'; is_closed_lits len';
                           match goal with
                           | H : rng RNG ?lo ?len |- _ =>
                               is_closed_lits lo; is_closed_lits len; apply (rng_sub' RNG lo len lo' len' H); decide_lit_bounds
                           end
                         | (* [comment removed for export] *)
                           let X := leftmost lo' in
                           first [ match goal with
                                   | H : rng RNG ?lo ?len |- _ => let Y := leftmost lo in constr_eq X Y; apply (rng_sub' RNG lo len lo' len' H); reglia
                                   end
                                 | first [ is_var X | lazymatch X with bv_unsigned ?r => is_var r end ];
                                   match goal with
                                   | H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X]; apply (rng_sub' RNG lo len lo' len' H); reglia
                                   end ]
                         | match goal with
                           | H : rng RNG ?lo ?len |- _ =>
                               apply (rng_sub' RNG lo len lo' len' H); reglia
                           end
                         | fail 0 "solve_rng: no [rng] hypothesis covers" lo' len' ] ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac exec_cbv :=
  cbv beta iota zeta delta [lift_resultF lift_result interp_eff interp_eff_accesses drop_access_report access_value accessed_ranges
     exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s].

(* [comment removed for export] *)
Ltac mem_after_store :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Ltac mem_after_store_fast :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; literal_cell_sizes_in HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          store_facts (A + Z.of_nat kn)%Z (cbytes c') ltac:(fun n' Hn Ha Hl =>
            transport_chunks_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl;
            footprint_after_store_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl);
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Ltac norm_lit_store_bytes :=
  try (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           is_Zlit z; change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]
       end).

Ltac mem_after_store_opt :=
  norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac   (* [comment removed for export] *)
      end
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac norm_fcsr :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ ?fce _ _ _) =>
      tryif is_var fce then idtac else
      (let fcn := fresh "fc" in
       let E := fresh "Efc" in
       tryif (let H := fresh "FRM" in
              assert (H : frm0 fce) by prove_frm0;
              repeat match goal with
              | H' : frm0 ?f |- _ => lazymatch f with fce => fail | _ => clear H' end
              end;
              remember fce as fcn eqn:E; clear E;
              try rename H into FRM)
       then idtac
       else (remember fce as fcn eqn:E; clear E))
  | _ => idtac
  end.

Ltac post_step i :=
  lazymatch i with
  | Fari _ _ _ _ _ _ => norm_fcsr
  | Fcmp _ _ _ _ _ => norm_fcsr
  | Fcvt _ _ _ _ _ => norm_fcsr
  | Fsqrt _ _ _ _ => norm_fcsr
  | Fminmax _ _ _ _ _ => norm_fcsr
  | Fma _ _ _ _ _ _ _ => norm_fcsr
  | Csr _ _ _ _ => norm_fcsr
  | CsrI _ _ _ _ => norm_fcsr
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac step_core segs RNG R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply (evtF_step_acc segs RNG);
        [ reflexivity
        | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | solve_accs
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

Ltac step :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs RNG R F pc fc rv m ro
  | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

(* [comment removed for export] *)
Ltac if_true :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; solve_cond]
  end.
Ltac if_false :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; solve_cond]
  end.
Ltac if_true_by H :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; exact H]
  end.
Ltac if_false_by H :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; exact H]
  end.
Ltac if_cases H :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      destruct c eqn:H; [ | ]
  end.

Ltac concretize_regs :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      let t := eval vm_compute in R in change R with t
  end.

Ltac zstep := step; zsimp.
Ltac fstep := step.
Ltac fsteps n :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; fsteps n'
      | _ => idtac
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  (* [comment removed for export] *)
  try (lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

(* [comment removed for export] *)
Tactic Notation "call" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      eapply evtF_cut; [ eapply SPEC | post_call segs m ];
      try (lazymatch goal with |- rng _ _ _ => solve_rng end)
  end.

(* [comment removed for export] *)
Ltac is_fp_clause A :=
  lazymatch A with
  | ?A1 /\ _ => is_fp_clause A1
  | @eq ?T _ _ => lazymatch eval hnf in T with machine_state => fail | _ => idtac end
  | rng _ _ _ => idtac
  | _ => let A' := eval hnf in A in      (* [comment removed for export] *)
         lazymatch A' with
         | ?A1 /\ _ => is_fp_clause A1
         | @eq ?T _ _ => lazymatch eval hnf in T with machine_state => fail | _ => idtac end
         | forall (b : Z) (j : nat), _ => idtac
         | _ -> _ => idtac
         end
  end.

Ltac fp_clause_solve :=
  first [ reflexivity | assumption | solve_rng
        | lazymatch goal with |- _ /\ _ => split; [fp_clause_solve | fp_clause_solve] end
        | idtac ].

Ltac finish_body :=
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac finish_split_fp body :=
  lazymatch goal with
  | |- ?A /\ ex _ => tryif is_fp_clause A then (split; [ fp_clause_solve | hnf; body ]) else body
  | |- ?A /\ (@eq ?T _ _ /\ _) =>
      tryif (lazymatch eval hnf in T with machine_state => is_fp_clause A end)
      then (split; [ fp_clause_solve | hnf; body ]) else body
  | _ => body
  end.

Ltac finish :=
  (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  finish_split_fp finish_body.

(* [comment removed for export] *)
Ltac finish2_body :=
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac finish2 :=
  (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  finish_split_fp finish2_body.

(* [comment removed for export] *)
Ltac store_done :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (* [comment removed for export] *)
    try (lazymatch goal with
    | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
    end);
    let HBa := fresh "HBarr" in
    try (let X := lazymatch E with Z.add (Z.add ?X _) _ => X | Z.add ?X _ => X | _ => E end in
         first [ lazymatch goal with
                 | H : u32arr segs m X ?xs |- _ => pose proof (u32arr_bound segs m X xs H) as HBa
                 | H : u8arr segs m X ?xs |- _ => pose proof (u8arr_bound segs m X xs H) as HBa
                 | H : u64arr segs m X ?xs |- _ => pose proof (u64arr_bound segs m X xs H) as HBa
                 end
               | lazymatch E with Z.add (Z.add ?X2 _) _ =>
                   lazymatch goal with
                   | H : u32arr segs m X2 ?xs |- _ => pose proof (u32arr_bound segs m X2 xs H) as HBa
                   | H : u8arr segs m X2 ?xs |- _ => pose proof (u8arr_bound segs m X2 xs H) as HBa
                   | H : u64arr segs m X2 ?xs |- _ => pose proof (u64arr_bound segs m X2 xs H) as HBa
                   end
                 end ]);
    transport_chunks segs m E bs;
    footprint_after_store segs m E bs;
    try clear HBa;
    let m' := fresh "m" in
    remember (write_to_mem m (wa E) bs) as m' eqn:Heqm;
    clear Heqm;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    try clear m
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac getreg n :=
  lazymatch goal with
  | |- evtF _ _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
      let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
      lazymatch v with
      | Some ?w => w
      | _ => fail "getreg: register" n "not concrete"
      end
  end.

Ltac name_reg_tac n X :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e => name_as_tac X e
  | _ => fail "name_reg: register" n "holds" w
  end.
Tactic Notation "name_reg" constr(n) ident(X) := name_reg_tac n X.

Ltac model_reg_tac n X mexpr :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      first [ constr_eq e mexpr
            | replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
                by (first [ f_equal; zeq_fast
                          | rewrite Z_to_bv_land64; f_equal; zeq_fast
                          | f_equal; zeq
                          | rewrite Z_to_bv_land64; f_equal; zeq
                          | apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq
                          | apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
                          | apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
      name_as_tac X mexpr
  | _ => fail "model_reg: register" n "holds" w
  end.
Tactic Notation "model_reg" constr(n) ident(X) constr(mexpr) := model_reg_tac n X mexpr.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac amo_decide :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let b := eval vm_compute in (amo_aligned wd a) in
      replace (amo_aligned wd a) with b by (vm_compute; reflexivity); cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      let b := eval vm_compute in (Z.eqb (bv_unsigned x) (bv_unsigned y)) in
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with b by (vm_compute; reflexivity); cbv iota
  end.

Ltac amo_step :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma evtF_ecall : forall segs RNG (Q : machine_state -> Prop) R F pc fc rv m ro w,
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true ->
  Q (MSsvc R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro) ->
  evtF segs RNG Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
ltac2:(KReplay.run1 (kr_t_StepF ()) [] "h01mh11Fh22HQh32Heh42Hfh51Qh61Rh73RNGh82fch92pch:2roh;2rvh<4segsh=1wp;1p;2p;3p;8p;7p;;p;6p;5p;:g001:j1QTg001Zj10Tg002?j1<Tg002dj13Tg003Bj19Tg0000j2OTg003ej17Tg00EIj22Tg004Gj2CTg005Ij2BTg005kj38Tg006Ej1?Tg00LFj1>Tg00ecj2PTg00Ldj3=Tg00dDj24Tg00dnj81Tg00;Ej7NTg007Ej2LTg00AQj1;Tg00UFj1GTg00ZAj2:Tg0096j1ETg00:=j1DTg00c\j1FTg00Y:j36Tg00B1j25Tg00[Xj2HTg013al;ITg000\j6JTg014`j1KTg015Vj2ATg0167j5@Tg0170l:MTg00]d#Qg00kkg00\]R0p-0[g00^c#0R1#<#3R2%01#0R1#0#0R3#0#3R4#9R5'OR6g00`4%33#9R3%75R7%31#9#7\5R8%73f:R9f5R:,24'Cf0R;,B338g00`RR<f1R=#?g00fF38P9f9R>f8R?f7R@,24%<1#>R1g00bWRA1P21d5=2RB,4>f6RCP:f4RDf3REG1O1f=RFf<RGf;RHP9P>124?RIP@PCP:PDFNRJP9P>PI149BP@PCP:PDG1RBg00ld,L5RK#;RL%G5,:7%E0R7#DRMP9P>PIP<P5A=21ARA#Fg00ff149AR1n0100000020000P@PCP:PDG1g00aR#;560,57PHP9124>14HAP?P@PCP:G1=60L,5798M;X0MP9P>PIP1P@PCP:PDG1=60L,57,:M1HFJPFP9P>PIP@PCP:PDPEf2P=M;IEJ%KG,AKPFPGPHPBP;D@M:MW2W3W4X=3X:8W0W;W8W9X16W6W5W7W<o"). Qed.

(* [comment removed for export] *)
Ltac step_ecall :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          apply (evtF_ecall segs RNG Q R F pc fc rv m ro w);
          [ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
      | None => fail "no instruction at" pc
      end
  end.

(* [comment removed for export] *)
Lemma stk_lo_nonneg : forall segs m lo hi, stk segs m lo hi -> (0 <= lo)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_StepF ()) [] "h01ah11bh21Hh32H0h42_Hh52hih62loh71mh84segsp;1p;4p;2p;3g001:j1BTg001Zj12Tg002dj16Tg003Bj14Tg003ej1ATg017mj4?Tg00i;j20Tg00LFj15Tg018_j2=Tg019<j27Tg00j4R0j21Tg019Xj18Tg01:Gj39Tg00UFj1@Tg005kj33Tg01;Dj1<Tg01;]j3:Tg005Ij2>Tg01<Mj2;Tg00]d#Bg00^c#2R1#2#2R2#2#2#2R3#6#4%62#4R2#AR4[g00`4R5f3R6f2R7f1R8f0R9C?P0g01<gR0/07%51%53'=R3,0810691797'1f6R1f5R:%88R;39%@2R<534#<f7%87R77:11>29R=534X12,;2'1[^05'11006P9f4R6,0010631019179:'1f9R:f8;9;=34<#<f:?::7=34=X12,;2'1[^05'1P8W4W2P8P9O2n2001000000120000000W3X55W6W7W8o"). Qed.

Ltac name_sp sp k :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
    by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
        try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg _ _ _ _ ST) end;
        apply unsigned_lit; lia).

Ltac unname_sp :=
  match goal with
  | H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
      constr_eq sp1 sp1';
      (* [comment removed for export] *)
      repeat match goal with K : context [bv_unsigned sp1] |- _ => tryif constr_eq K H then fail else rewrite H in K end;
      try rewrite H; clear H; subst sp1
  end.

Tactic Notation "call_sp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evtF _ _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | |- evtF _ _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp sp k; call SPEC; unname_sp
  | _ => call SPEC
  end.

Ltac sys_finish :=
  (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  finish_split_fp finish2_body.
