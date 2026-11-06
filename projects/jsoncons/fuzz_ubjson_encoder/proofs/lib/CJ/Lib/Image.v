(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Image () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Image:ro_bytes_bC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8ro_bytesC13~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7ro_addrC13~~~C47Corelib4Init9Datatypes4andbK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7ro_byteC13~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem7mem_invC13~~~C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Image@ro_bytes_b_soundC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem;ro_bytes_atC13~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rK47Corelib7Numbers7BinNums1Z01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~I47Corelib4Init9Datatypes3nat00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Image;image_bytesC13~~~C47Corelib4Init5Logic7f_equalK47Corelib4Init9Datatypes3nat02C35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes7nat_indK47Corelib4Init9Datatypes3nat01".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

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
ltac2:(KReplay.run1 (kr_t_Image ()) ["WithSegs"] "p'0h01Hh11Eh22H1h31nh41Ah52bsh62b'i002b'h72b1h82b2h91mh:2H0h;2H2h<2H3h=2IHh>1bi011bh?1eh@1oi021oi031xp;1p;2p;3p;4p;7p;6p;5p10000p4p710p1000Mp4p710p8g000kj1@Tg001Pj1QTg001nj1<Tg002Qj1HTg0031j29Tg004Cj34Tg005Qj1MTg0061j3BTg006Qj11Tg007Yj28Tg008dR0j1FTg009Fj2ETg009`j32Tg00::j35Tg00:gj26Tg00<4j27Tg00<Rj1PTg00=0j23Tg00=Mj3>Tg00>ZR1j2=Tg00?5j2?Tg00?Wj3DTg00@:j2CTg00@Wj2LTg00A7j2:Tg00Aaj3KTg00BEj4ATg00B`j7Ij6GTg00C<j1JTg00C^j2NTg00D=j5OTg00D_R2f0R3g00E?R432p=0g00E_R5f1R6;23p=;g00F=R7#@#@#@#QR8#<R9#HR:P91936#0p,4segsR;f2R<746[^45R=X5:%M9R>,93#0g00FbR?A4;6>eW0X45f3R>=B9<,93#0%16,8;%F9R@1E@3%1<,8;=2@3P0P9f4RA#1,8;=2@3P0P9P2P6f9R0=583f6RB#1,6;RC'7%P7R7,3BRDf8RE'9RF'7g00G>RGn10110300021010000#0A>;B0A4;DE'=RD]0]1P6f5RB#1,8;1?93RH52@A5806/7C/7F#0f:RF=58<f7RC#1,6;'7RI13C7/90RJ;D3%0I%0J'=P1f;RJ=58>%1E,6;'7#013E7/9F#0f<RI9>;01307=4;J'=P3f=R0=58B%1F,6;'7#013J7/90#0f?RJ=58CRC%1I,6;RI;D6%0C%0I'=P1f@RI=58E#0%10,6;#0f>REfA5>;13E7=4;I'=P3fB=58F#0%1I,6;#0P11C63#01;<6[RE1;631C<6#0RC[1;><\C1L63P6n2001000000120000000X95X35PE^95^35P3fERE,:8RC1:80R0P<O31;C0g00G^R0%<3RC%<6RKP1%<<?2631:><1:>6';R1[1:<61:<3';%<>?2<6[RL%<A?2><\1AK<63P3n2001000000120000000W8W7W3PL^8K^7C^30P3P8fGR8PJP6O4A298JP9fHR0fFRC#1RK,8;RL=2@HfJ9>;81387fIRH54;'=]1X69%1E,8;1?9052@A>;CH13C7RC=4;01?9H92@L16;K#0P3PBCAP8PCPFO2CAW1PIP3PJFIb2b0b2b0W;W2P6P3O2n2001000000121000000b2W<W2P6P3O2n2001000000121000000b0W0W1X69P3O1%1>,8;%J952@A22G4P2PGP2p-0P3g00H<RGg00HYn0110100020000X?2P?P4P3EGPG1ND3b:W0W1n10110200021110100P3P<O2b1b@AB9A>94;6eW0X45X==X5:X>9P3DOW5o"). Qed.

Lemma ro_cells_image : forall m A bs,
  mem_inv segs m -> ro_bytes_b A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  ro_cells segs m A [CB (length bs) bs].
Proof.
ltac2:(KReplay.run1 (kr_t_Image ()) ["WithSegs"] "h01Ah12HAh22Hbh34Hinvh42Hlh52bsh61lh71mp;1p;2p;3p;4p;8p;6g000kj10Tg001Pj19Tg001nj14Tg008dj1<Tg002Qj1JTg00I5j2FTg0031j2@Tg009`j31Tg00JBj28Tg00J^j26Tg00K>j1;Tg00=0j2:Tg00<Rj17Tg00K^j2ITg00L;j2HTg005Qj15Tg0061j3ETg00MIj1CTg00NYj1BTg00Olj42Tg009Fj2ATg00BEj43Tg00Q:j3?Tg00RRj8>Tg00Scj3DTg00T@j2=Tg000Mj6GTg00F=#0R0#0#0R1#0#0#0R2#9#4%91#4R1#<[g00E_%J1R3p,4segsR4f2R5'Fg00D_f1R6,@5g00E?31g00T^f3R7'8f4R81617#;':%70%72'I'8g00U<R21618R0/H8%523ER2#CR9P4f6R:f5R;%B2C2R2g00VJR<?100g00HY1A<0g00FbC3P9eP3P8P4f7P:f0R9C2X63P4P:P;P8P7P6P9A?8;5G>%519D181=18EGP2eC3W4W1W2W3W5W0W7o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_Image ()) ["WithSegs"] "p'0h01Hh12H0h21Eh32H1h41oi001oh51Ah62bsi012bsh71eh81li021lh91nh:2H2h;2IHh<1bi031bi041xp;1p;2p;3p;6p;8p;4g000kj1;Tg001Pj1HTg001nj1BTg002Qj1@Tg008dR0j1>Tg00Vij24Tg00?5j21Tg009`R1j30Tg00J^j23Tg005Qj1?Tg00X<j6<Tg009Fj28Tg00B`j69Tg00XYR2j17Tg006Qj1GTg007Yj2FTg00<Rj1ETg00=0j26Tg0061j32Tg00C<j1CTg00Y8j8ATg00C^j2=Tg00YUj4DTg00VJR3f1R4f0R530p=5g00Z6R69035p=:g00E_R7g00F=R8#;#;#;#H#BR9#@R:%>:R;f2R<,4411:5R=301394f3R>'5[]6]5R?X931446=0;=P1P;%?9R@,1:RA11:>RB90;4f4RC,39RD#:[P511:4RE90;A11:<RF90;AP;P:P0P:P:P5P5P@n10110000021010200X7;PAPBP5E<A0:@>A0:@CP5f5RA90:@P:P@1395R@#:X8:1836f6R6P5E9b:W3P5O1b3W1P5O1W1n2002100000000101A0;5F139>#:[X4;PEO1P518;FO1b1W0X6:X57%7>,44=0;=p,4segs%G<'F%>9P0P9P0P9P;P5P0P:P;%E8R8,6Af7RE'4A2945,1:%C:RGn10110400021010100RHPGn10110400021010300=0;B%7E,5DRD]0P511:C90;H1668f8RH'4P;18;516E8f9RI'4=0;5P0P:16I8f;RJ'4=0;5P0P:P;P4A2965,1:PGn1011040002101010011:IRK50;f:RL,39f=RM#7'5RN]0]2P416L8f<RO'4=0;=A2964,1:11:L50;P1P;A29E<,1:R111:MR=90;4f>RP,39fARQ#7'5[P511:JRR90;1A29H>,1:11:OR>50;P;P:P0P:P:P5P5A29LARAn10110000021010200X7;A29ICRI,1:P=P5E<A0:IMA0:APP5A29J6f?50:P:A29OEROfD#7,5@X8:P3P3P2P2139EfCR@P3\3/82fB16Q8PEP6O3GA139O%7@'5ef@R@P5E9b:W3P5O1b3W1P5O1W1n2002100000000101A0;5>139M%7@'5[X4;PRO1P518;>O1b1W0W2X8:P5O116H8/4L=0;G11:H90;GP;PGP0P:p-0P5g00H<R0g00HYn10110000021000000X7;RHg00FbRLPKP5E9P01=N5b1W0W2n10110000021110200P5P<O2b2b4W0X<9P5O1A0;GFP;PGPHPLPBP5E9P01=D5b1W0n10110000021110300P4O1b4W0X6:X57X;?X93P5CDX93o"). Qed.

End WithSegs.

(* [comment removed for export] *)
