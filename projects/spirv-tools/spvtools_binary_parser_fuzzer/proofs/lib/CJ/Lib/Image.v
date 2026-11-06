(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_Image () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00c69OSSVerify5KrLib2CJ3Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib3Mem8ro_bytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2CJ3Lib3Mem2waC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC69OSSVerify5KrLib2CJ3Lib3Mem7ro_addrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2CJ3Lib3Mem7ro_byteC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic3and01C47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C69OSSVerify5KrLib2CJ3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powK69OSSVerify5KrLib2CJ3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ3Lib5Image@ro_bytes_b_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib3Mem;ro_bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rK47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib2CJ3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

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
ltac2:(KReplay.run1 (kr_t_Image ()) ["AC_1"; "WithSegs"] "p'0h01Hh11Eh22H1h31nh41Ah52bsh62b'i002b'h72b1h82b2h91mh:2H0h;2H2h<2H3h=2IHh>1bi011bh?1eh@1oi021oi031xp;1p;2p;3p;4p;7p;6p;5p10000p4p710p1000Mp4p710p8g000kj1@Tg001Pj1QTg001nj1<Tg002Qj1HTg0031j29Tg003mj34Tg004ej1MTg005Ej3BTg005ej11Tg006Wj28Tg007SR0j1FTg0085j2ETg008Oj32Tg008ij35Tg009Vj26Tg00:Mj27Tg00:kj1PTg00;Ij23Tg00;fj3>Tg00<]R1j2=Tg00=8j2?Tg00=Zj3DTg00>=j2CTg00>Zj2LTg00?:j2:Tg00?dj3KTg00@Hj4ATg00@cj7Ij6GTg00A?j1JTg00Aaj2NTg00B@j5OTg00BbR2f0R3g00CBR432p=0g00CbR5f1R6;23p=;g00D@R7#@#@#@#QR8#<R9#HR:P91936#0p,4segsR;f2R<746[^45R=X5:%M9R>,93#0g00DeR?A4;6>eW0X45f3R>=B9<,93#0%16,8;%F9R@1E@3%1<,8;=2@3P0P9f4RA#1,8;=2@3P0P9P2P6f9R0=583f6RB#1,6;RC'7%P7R7,3BRDf8RE'9RF'7g00EARGn10110300021010000#0A>;B0A4;DE'=RD]0]1P6f5RB#1,8;1?93RH52@A5806/7C/7F#0f:RF=58<f7RC#1,6;'7RI13C7/90RJ;D3%0I%0J'=P1f;RJ=58>%1E,6;'7#013E7/9F#0f<RI9>;01307=4;J'=P3f=R0=58B%1F,6;'7#013J7/90#0f?RJ=58CRC%1I,6;RI;D6%0C%0I'=P1f@RI=58E#0%10,6;#0f>REfA5>;13E7=4;I'=P3fB=58F#0%1I,6;#0P11C63#01;<6[RE1;631C<6#0RC[1;><\C1L63P6n2001000000120000000X95X35PE^95^35P3fERE,:8RC1:80R0P<O31;C0g00EaR0%<3RC%<6RKP1%<<?2631:><1:>6';R1[1:<61:<3';%<>?2<6[RL%<A?2><\1AK<63P3n2001000000120000000W8W7W3PL^8K^7C^30P3P8fGR8PJP6O4A298JP9fHR0fFRC#1RK,8;RL=2@HfJ9>;81387fIRH54;'=]1X69%1E,8;1?9052@A>;CH13C7RC=4;01?9H92@L16;K#0P3PBCAP8PCPFO2CAW1PIP3PJFIb2b0b2b0W;W2P6P3O2n2001000000121000000b2W<W2P6P3O2n2001000000121000000b0W0W1X69P3O1%1>,8;%J952@A22G4P2PGP2p-0P3g00F?RGg00F\n0110100020000X?2P?P4P3EGPG1ND3b:W0W1n10110200021110100P3P<O2b1b@AB9A>94;6eW0X45X==X5:X>9P3DOW5o"). Qed.

Lemma ro_cells_image : forall m A bs,
  mem_inv segs m -> ro_bytes_b A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  ro_cells segs m A [CB (length bs) bs].
Proof.
ltac2:(KReplay.run1 (kr_t_Image ()) ["AC_1"; "WithSegs"] "h01Ah12HAh22Hbh34Hinvh42Hlh52bsh61lh71mp;1p;2p;3p;4p;8p;6g000kj10Tg001Pj19Tg001nj14Tg007Sj1<Tg002Qj1JTg00G8j2FTg0031j2@Tg008Oj31Tg00Goj28Tg00HKj26Tg00Hkj1;Tg00;Ij2:Tg00:kj17Tg00IKj2ITg00Ihj2HTg004ej15Tg005Ej3ETg00J`j1CTg00KZj1BTg00LWj42Tg0085j2ATg00@Hj43Tg00MOj3?Tg00NQj8>Tg00OLj3DTg00Oij2=Tg000Mj6GTg00D@#0R0#0#0R1#0#0#0R2#9#4%91#4R1#<[g00Cb%J1R3p,4segsR4f2R5'Fg00Bbf1R6,@5g00CB31g00PGf3R7'8f4R81617#;':%70%72'I'8g00PeR21618R0/H8%523ER2#CR9P4f6R:f5R;%B2C2R2g00Q]R<?100g00F\1A<0g00DeC3P9eP3P8P4f7P:f0R9C2X63P4P:P;P8P7P6P9A?8;5G>%519D181=18EGP2eC3W4W1W2W3W5W0W7o"). Qed.

Fixpoint image_bytes (A : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' => match seg_rom segs (wa A), image_bytes (A + 1) n' with
            | Some b, Some bs => Some (b :: bs)
            | _, _ => None
            end
  end.

End WithSegs.

End AC_1.
