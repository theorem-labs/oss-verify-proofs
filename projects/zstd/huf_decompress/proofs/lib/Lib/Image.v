(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Image () := "C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8ro_bytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib3Lib3Mem7ro_addrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem7ro_byteC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib5Image@ro_bytes_b_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;ro_bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rK47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib3Lib5Image;image_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalK47Corelib4Init9Datatypes3nat02C35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes7nat_indK47Corelib4Init9Datatypes3nat01".
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
ltac2:(KReplay.run1 (kr_t_Image ()) ["WithSegs"] "p'0h01Hh11Eh22H1h31nh41Ah52bsh62b'i002b'h72b1h82b2h91mh:2H0h;2H2h<2H3h=2IHh>1bi011bh?1eh@1oi021oi031xp;1p;2p;3p;4p;7p;6p;5p-1R0p10000p4p710p8P0p1000LR1p4p710p8P0P1p4p7210p8p1000ip4p710p1001Fp4p710p8g001dj1@Tg002Ij1QTg002gj1<Tg003Jj1HTg003jj29Tg004cj34Tg005Xj1MTg0068j3BTg006Xj11Tg007Gj28Tg008@R1j1FTg008bj2ETg009<j32Tg009Vj35Tg00:Cj26Tg00;7j27Tg00;Uj1PTg00<3j23Tg00<Pj3>Tg00=DR0j2=Tg00=_j2?Tg00>Aj3DTg00>dj2CTg00?Aj2LTg00?aj2:Tg00@Kj3KTg00@oj4ATg00AJj7Ij6GTg00Afj1JTg00BHj2NTg00Bgj5OTg00CIR2f0R3g00CiR432p=0g00DIR5f1R6;23p=;g00DgR7#@#@#@#QR8#<R9#HR:P91936#0p,4segsR;f2R<746[^45R=X5:%M9R>,93#0g00ELR?A4;6>eW0X45f3R>=B9<,93#0%16,8;%F9R@1E@3%1<,8;=2@3P1P9f4RA#1,8;=2@3P1P9P2P6f9R1=583f6RB#1,6;RC'7%P7R7,3BRDf8RE'9RF'7g00EhRGn10110300021010000#0A>;B1A4;DE'=RD]0]1P6f5RB#1,8;1?93RH52@A5816/7C/7F#0f:RF=58<f7RC#1,6;'7RI13C7/91RJ;D3%0I%0J'=P0f;RJ=58>%1E,6;'7#013E7/9F#0f<RI9>;11317=4;J'=P3f=R1=58B%1F,6;'7#013J7/91#0f?RJ=58CRC%1I,6;RI;D6%0C%0I'=P0f@RI=58E#0%11,6;#0f>REfA5>;13E7=4;I'=P3fB=58F#0%1I,6;#0P01C63#01;<6[RE1;631C<6#0RC[1;><\C1L63P6n2001000000120000000X95X35PE^95^35P3fERE,:8RC1:81R1P<O31;C1g00FHR1%<3RC%<6RKP0%<<?2631:><1:>6';R0[1:<61:<3';%<>?2<6[RL%<A?2><\0AK<63P3n2001000000120000000W8W7W3PL^8K^7C^31P3P8fGR8PJP6O4A298JP9fHR1fFRC#1RK,8;RL=2@HfJ9>;81387fIRH54;'=]1X69%1E,8;1?9152@A>;CH13C7RC=4;11?9H92@L16;K#0P3PBCAP8PCPFO2CAW1PIP3PJFIb2b0b2b0W;W2P6P3O2n2001000000121000000b2W<W2P6P3O2n2001000000121000000b0W0W1X69P3O1%1>,8;%J952@A22G4P2PGP2p-0P3g00FfRGg00GCn0110100020000X?2P?P4P3EGPG1ND3b:W0W1n10110200021110100P3P<O2b1b@AB9A>94;6eW0X45X==X5:X>9P3DOW5o"). Qed.

Lemma ro_cells_image : forall m A bs,
  mem_inv segs m -> ro_bytes_b A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  ro_cells segs m A [CB (length bs) bs].
Proof.
ltac2:(KReplay.run1 (kr_t_Image ()) ["WithSegs"] "h01Ah12HAh22Hbh34Hinvh42Hlh52bsh61lh71mp;1p;2p;3p;4p;8p;6g001dj10Tg002Ij19Tg002gj14Tg008@j1<Tg003Jj1JTg00G_j2FTg003jj2@Tg009<j31Tg00HSj28Tg00Hoj26Tg00IOj1;Tg00<3j2:Tg00;Uj17Tg00Ioj2ITg00JLj2HTg005Xj15Tg0068j3ETg00KAj1CTg00L8j1BTg00M2j42Tg008bj2ATg00@oj43Tg00Mgj3?Tg00Nfj8>Tg00O^j3DTg00P;j2=Tg001Fj6GTg00Dg#0R0#0#0R1#0#0#0R2#9#4%91#4R1#<[g00DI%J1R3p,4segsR4f2R5'Fg00CIf1R6,@5g00Ci31g00PYf3R7'8f4R81617#;':%70%72'I'8g00Q7R21618R0/H8%523ER2#CR9P4f6R:f5R;%B2C2R2g00QlR<?100g00GC1A<0g00ELC3P9eP3P8P4f7P:f0R9C2X63P4P:P;P8P7P6P9A?8;5G>%519D181=18EGP2eC3W4W1W2W3W5W0W7o"). Qed.

(* [comment removed for export] *)
Fixpoint image_bytes (A : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' => match seg_rom segs (wa A), image_bytes (A + 1) n' with
            | Some b, Some bs => Some (b :: bs)
            | _, _ => None
            end
  end.

Lemma image_bytes_length : forall n A bs, image_bytes A n = Some bs -> length bs = n.
Proof.
ltac2:(KReplay.run1 (kr_t_Image ()) ["WithSegs"] "p'0h01Hh12H0h21Eh32H1h41oi001oh51Ah62bsi012bsh71eh81li021lh91nh:2H2h;2IHh<1bi031bi041xp;1p;2p;3p;6p;8p;4g001dj1;Tg002Ij1HTg002gj1BTg003Jj1@Tg008@R0j1>Tg00RKj24Tg00=_j21Tg009<R1j30Tg00Hoj23Tg005Xj1?Tg00SEj6<Tg008bj28Tg00AJj69Tg00SbR2j17Tg006Xj1GTg007Gj2FTg00;Uj1ETg00<3j26Tg0068j32Tg00Afj1CTg00TAj8ATg00BHj2=Tg00T^j4DTg00QlR3f1R4f0R530p=5g00U?R69035p=:g00DIR7g00DgR8#;#;#;#H#BR9#@R:%>:R;f2R<,4411:5R=301394f3R>'5[]6]5R?X931446=0;=P1P;%?9R@,1:RA11:>RB90;4f4RC,39RD#:[P511:4RE90;A11:<RF90;AP;P:P0P:P:P5P5P@n10110000021010200X7;PAPBP5E<A0:@>A0:@CP5f5RA90:@P:P@1395R@#:X8:1836f6R6P5E9b:W3P5O1b3W1P5O1W1n2002100000000101A0;5F139>#:[X4;PEO1P518;FO1b1W0X6:X57%7>,44=0;=p,4segs%G<'F%>9P0P9P0P9P;P5P0P:P;%E8R8,6Af7RE'4A2945,1:%C:RGn10110400021010100RHPGn10110400021010300=0;B%7E,5DRD]0P511:C90;H1668f8RH'4P;18;516E8f9RI'4=0;5P0P:16I8f;RJ'4=0;5P0P:P;P4A2965,1:PGn1011040002101010011:IRK50;f:RL,39f=RM#7'5RN]0]2P416L8f<RO'4=0;=A2964,1:11:L50;P1P;A29E<,1:R111:MR=90;4f>RP,39fARQ#7'5[P511:JRR90;1A29H>,1:11:OR>50;P;P:P0P:P:P5P5A29LARAn10110000021010200X7;A29ICRI,1:P=P5E<A0:IMA0:APP5A29J6f?50:P:A29OEROfD#7,5@X8:P3P3P2P2139EfCR@P3\3/82fB16Q8PEP6O3GA139O%7@'5ef@R@P5E9b:W3P5O1b3W1P5O1W1n2002100000000101A0;5>139M%7@'5[X4;PRO1P518;>O1b1W0W2X8:P5O116H8/4L=0;G11:H90;GP;PGP0P:p-0P5g00FfR0g00GCn10110000021000000X7;RHg00ELRLPKP5E9P01=N5b1W0W2n10110000021110200P5P<O2b2b4W0X<9P5O1A0;GFP;PGPHPLPBP5E9P01=D5b1W0n10110000021110300P4O1b4W0X6:X57X;?X93P5CDX93o"). Qed.

End WithSegs.

(* [comment removed for export] *)
Definition reservedZ (segs : list Segment) : list (Z * Z) :=
  map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (segments_reserved segs).

(* [comment removed for export] *)
