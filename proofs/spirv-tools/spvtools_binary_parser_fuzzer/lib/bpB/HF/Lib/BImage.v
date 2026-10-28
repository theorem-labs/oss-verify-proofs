(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BMem BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BImage () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00c7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BImage:ro_bytes_bC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem8ro_bytesK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romI47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7ro_addrC47Corelib4Init9Datatypes4andbK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7ro_byteI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell05C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells8cells_wfC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells;cells_bytesC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem8bytes_atc7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BImage@ro_bytes_b_soundC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem;ro_bytes_atC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rK47Corelib7Numbers7BinNums1Z01I7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00I47Corelib4Init9Datatypes3nat00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Fixpoint ro_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom segs (wa A) with
      | Some b' => bv_eqb b b' && ro_addr segs (wa A) && ro_bytes_b (A + 1) bs'
      | None => false
      end
  end.

Lemma ro_bytes_b_sound : forall bs A, ro_bytes_b A bs = true -> ro_bytes segs A bs.
Proof.
ltac2:(KReplay.run1 (kr_t_BImage ()) ["WithSegs"] "p'0h01Hh11Eh22H1h31nh41Ah52bsh62b'i002b'h72b1h82b2h91mh:2H0h;2H2h<2H3h=2IHh>1bi011bh?1eh@1oi021oi031xp;1p;2p;3p;4p;7p;6p;5p10000p4p710p1000Mp4p710p8g000kj1@Tg001Pj1QTg001nj1<Tg002Qj1HTg0031j29Tg0042j34Tg004oj1MTg005Oj3BTg005oj11Tg006fj28Tg007hR0j1FTg008Jj2ETg008dj32Tg009>j35Tg009kj26Tg00:gj27Tg00;Ej1PTg00;cj23Tg00<@j3>Tg00=<R1j2=Tg00=Wj2?Tg00>9j3DTg00>\j2CTg00?9j2LTg00?Yj2:Tg00@Cj3KTg00@gj4ATg00ABj7Ij6GTg00A^j1JTg00B@j2NTg00B_j5OTg00CAR2f0R3g00CaR432p=0g00DAR5f1R6;23p=;g00D_R7#@#@#@#QR8#<R9#HR:P91936#0p,4segsR;f2R<746[^45R=X5:%M9R>,93#0g00EDR?A4;6>eW0X45f3R>=B9<,93#0%16,8;%F9R@1E@3%1<,8;=2@3P0P9f4RA#1,8;=2@3P0P9P2P6f9R0=583f6RB#1,6;RC'7%P7R7,3BRDf8RE'9RF'7g00E`RGn10110300021010000#0A>;B0A4;DE'=RD]0]1P6f5RB#1,8;1?93RH52@A5806/7C/7F#0f:RF=58<f7RC#1,6;'7RI13C7/90RJ;D3%0I%0J'=P1f;RJ=58>%1E,6;'7#013E7/9F#0f<RI9>;01307=4;J'=P3f=R0=58B%1F,6;'7#013J7/90#0f?RJ=58CRC%1I,6;RI;D6%0C%0I'=P1f@RI=58E#0%10,6;#0f>REfA5>;13E7=4;I'=P3fB=58F#0%1I,6;#0P11C63#01;<6[RE1;631C<6#0RC[1;><\C1L63P6n2001000000120000000X95X35PE^95^35P3fERE,:8RC1:80R0P<O31;C0g00F@R0%<3RC%<6RKP1%<<?2631:><1:>6';R1[1:<61:<3';%<>?2<6[RL%<A?2><\1AK<63P3n2001000000120000000W8W7W3PL^8K^7C^30P3P8fGR8PJP6O4A298JP9fHR0fFRC#1RK,8;RL=2@HfJ9>;81387fIRH54;'=]1X69%1E,8;1?9052@A>;CH13C7RC=4;01?9H92@L16;K#0P3PBCAP8PCPFO2CAW1PIP3PJFIb2b0b2b0W;W2P6P3O2n2001000000121000000b2W<W2P6P3O2n2001000000121000000b0W0W1X69P3O1%1>,8;%J952@A22G4P2PGP2p-0P3g00F^RGg00G;n0110100020000X?2P?P4P3EGPG1ND3b:W0W1n10110200021110100P3P<O2b1b@AB9A>94;6eW0X45X==X5:X>9P3DOW5o"). Qed.

Lemma ro_cells_image : forall m A bs,
  mem_inv segs m -> ro_bytes_b A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  ro_cells segs m A [CB (length bs) bs].
Proof.
ltac2:(KReplay.run1 (kr_t_BImage ()) ["WithSegs"] "h01Ah12HAh22Hbh34Hinvh42Hlh52bsh61lh71mp;1p;2p;3p;4p;8p;6g000kj10Tg001Pj19Tg001nj14Tg007hj1<Tg002Qj1JTg00GWj2FTg0031j2@Tg008dj31Tg00HSj28Tg00Hoj26Tg00IOj1;Tg00;cj2:Tg00;Ej17Tg00Ioj2ITg00JLj2HTg004oj15Tg005Oj3ETg00KIj1CTg00LHj1BTg00MJj42Tg008Jj2ATg00@gj43Tg00NGj3?Tg00ONj8>Tg00PNj3DTg00Pkj2=Tg000Mj6GTg00D_#0R0#0#0R1#0#0#0R2#9#4%91#4R1#<[g00DA%J1R3p,4segsR4f2R5'Fg00CAf1R6,@5g00Ca31g00QIf3R7'8f4R81617#;':%70%72'I'8g00QgR21618R0/H8%523ER2#CR9P4f6R:f5R;%B2C2R2g00RdR<?100g00G;1A<0g00EDC3P9eP3P8P4f7P:f0R9C2X63P4P:P;P8P7P6P9A?8;5G>%519D181=18EGP2eC3W4W1W2W3W5W0W7o"). Qed.

Fixpoint image_bytes (A : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' => match seg_rom segs (wa A), image_bytes (A + 1) n' with
            | Some b, Some bs => Some (b :: bs)
            | _, _ => None
            end
  end.

End WithSegs.

