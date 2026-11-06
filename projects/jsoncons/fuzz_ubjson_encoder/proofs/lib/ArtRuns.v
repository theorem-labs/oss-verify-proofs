(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ArtRuns () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes?andb_true_introC47Corelib4Init5Logic6eq_symI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic6eq_indc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns:art_revealC13~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums8positive01C47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4bool02C47Corelib4Init5Logic8eq_ind_rc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns=art_reveal_inC13~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns9art_zfillC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns9art_unmapC13~~~i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns5aruns00C13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns5aruns01C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns5aruns02C13~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns<art_at_ecallC13~~~K47Corelib7Numbers7BinNums1Z02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns=art_mmap_argsC13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns3aev01C13~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6regupdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns5aruns03C13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns3aev02C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns8art_shloC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns8art_shhiC13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns5aruns04C13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns3aev03C13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns5aruns05C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns?art_munmap_argsC13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns3aev04C13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns5aruns06C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns@art_madvise_argsC13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns3aev05C13~~~k79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns5aruns07C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns9aruns_indC13~~~K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appi79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRuns3aev00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive aev : Type :=
| AMmapFixed (addr len : Z)      (* [comment removed for export] *)
| AMmapNull (len r : Z)          (* [comment removed for export] *)
| AMmapFixedNR (addr len : Z)    (* [comment removed for export] *)
| AMunmap (addr len : Z)         (* [comment removed for export] *)
| AMadvise (addr len : Z).       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition art_zfill (M : word -> option byte) (r len : Z) : word -> option byte :=
  fun a => if (r <=? bv_unsigned a) && (bv_unsigned a <? r + len) then Some (Z_to_bv 8 0) else M a.
Definition art_unmap (M : word -> option byte) (r len : Z) : word -> option byte :=
  fun a => if (r <=? bv_unsigned a) && (bv_unsigned a <? r + len) then None else M a.

(* [comment removed for export] *)
Definition art_shlo (r : Z) : Z := (r / 8 + 0x7fff8000) / 4096 * 4096.
Definition art_shhi (r len : Z) : Z := ((r + len) / 8 + 0x7fff8000 + 4095) / 4096 * 4096.
Definition art_reveal (M : word -> option byte) (lo hi : Z) : word -> option byte :=
  fun a => if (lo <=? bv_unsigned a) && (bv_unsigned a <? hi) then (match M a with Some b => Some b | None => Some (Z_to_bv 8 0) end) else M a.

Lemma art_reveal_in : forall M lo hi a, lo <= bv_unsigned a < hi -> art_reveal M lo hi a = match M a with Some b => Some b | None => Some (Z_to_bv 8 0) end.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) [] "p'0h04__p1h14__x1h24__x2h31mh41nh52H0h61Mh77__arithh84__ffh98__varmaph:5__with;1Hh<1ah=1bi001bh>2hih?2loi011xp;1p;2p;4p;6p;3p;7p;8g0000j12Tg000Uj1BTg0013j1=Tg001VR0j1FTg0028j27Tg002bj21Tg003>j23Tg003ZR1j28Tg0045j25Tg004Rj24Tg004oj2?Tg005Mj2CTg005mj1[Tg006Mj1VTg006mj2UTg007Kj1RTg007ij4QTg008Gj1PTg008ej1LTg009Pj2>Tg00:3j4:Tg00:^j6JTg00;Bj1ITg00;dj2HTg00<Fj2@Tg00<`j2GTg00=Lj3KTg00=kj4ETg00>]j2MTg00?=j4NTg00?Xj3DTg00@Aj4OTg00@]j36Tg00A7j2ATg00AYj2STg00B?j6TTg00B[j4ZTg00Chj7YTg00DLj7XTg00E0j8WTg00ETR2f0R3g00F4R436p=0f1R5g00FTR6g00G3R7P7g00GSR8P3g00H3FYp=<f2R9P6P7P7P8P5P3FXp=9f3R:P6P7P7P8P9P5P3GWp=;g00HSR;#2R<#2#2R=#2#2#2#BR>#=R?%B=R=#=R@#FRA[g00I8RB17>3RC,1913C5'8P217>5RC,5:RD14C9RC'?REP4%0D%0CP11553#01195RF[11531595#0[RG15:9#0\F1C53P3n2001000000120000000X3BX4BPG^3B^4BP3f4RG17>9RFf5RHP9O1RIPAp-0RJg00IVRK#[RL%VKRKPB1UB9P5%RBCQRM%PBRN%LBROPB1>B;R;g00JB1>B<R<C:,<ORPPOP6P7P7P8PGEJR659O%I7R7PPC;1HO8R8P3P91@241G39#0dg00JiRP=KB5CERQb8b9b:X1BX2BW01135/891159[^1B^2B^0JP317>GR>/3HP>f6RRP:O4b7b6O3b5P11453#01395R1[13531495#0[RS14:9#0\11M53P3n2001000000120000000X3BX4BPS^3B^4BP3PFP:PIPAPLPKPMPNPOPBP;g00KGP<C:,<OR<99O6P7P<C;P8PQb8b9b:X1BX2BX0J1335,891359[^1B^2B^0JP311R>PHP>P:O4b7b6O3b5CN9DDCCOA624EP2P4P2PAP3P0P@PAPRP:O1RR1A@3R41S=P,A@RPn10110100021010000R=PRn0100000020000=6A=X=2P0P@PAPIP4PPn10110100021010000,@A15GF14F:'?P3ETb5PGP:P9P5CZP0P@PAPGP5O1P4PPn1011010002101000056AeW;X<?X>BW?W6o"). Qed.
Lemma art_reveal_out : forall M lo hi a, ~ (lo <= bv_unsigned a < hi) -> art_reveal M lo hi a = M a.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) [] "p'0h02E1h12E2h21mh31nh42H0h51Mh64__x1h74__x2h84__x3h91bi001bh:1Hh;7__arithh<4__ffh=8__varmaph>5__with?1ah@2hihA2loi011xp;1p;2p;3p;4p;7p;8g0000j15Tg000Uj1BTg0013j1;Tg001VR0j1FTg0028j20Tg002bj24Tg003>j23Tg003ZR1j2>Tg00Knj1ITg0045j26Tg00<Fj28Tg00@]j31Tg004Rj27Tg004oj2:Tg00A7j2ATg00AYj2WTg005Mj2VTg00>]j2UTg005mj1RTg006Mj1QTg006mj2?Tg007ij4MTg008Gj1LTg008ej1KTg009Pj29Tg00LGj1HTg00:3j4<Tg00;Bj1GTg00DLj7JTg00;dj2ETg00<`j2NTg00=Lj3DTg00=kj4OTg00Llj2PTg00B[j4CTg00Chj7STg00E0j8TTg00ETR2f0R3g00F4R431p=2f1R5g00FTR6g00G3R7P7g00GSR8P3g00H3FSp==f3R9P6P7P7P8f2R:P5P3GTp=@g00HSR;#5R<#5#5R=#5#5#5#BR>#;R?%B=R=#;R@#FRA[g00I8RB10>3RC,4:13C5'>#I10>5,69P21823RCf4RD10>:'6=123P2f6RE10>DRF'6=123P2PAf5RG,0>/7ERH,:5P0P@PAf8RIPGO1RJ1A@3RKg00JiRL,W=,A@R=n10110100021010000PJn0100000020000=1AJ]0P510>9,6GRJ#217FGP2PCA12H3P2f7RH,0>/7I=123P2PA1:45P0P@PAf;RCPIO1RGPKP=n10110100021010000PGn0100000020000=1AG]1P510>E/7HRE#2P11653#214:5[RG145316:5#2RF[149:\F1V53P5n2001000000120000000X2BX3BPG^2B^3BP3f:RG10>IRIPDO314GIP11753#213:5[R1135317:5#2RI[139:\I1U53P5n2001000000120000000X2BX3BP1^2B^3BP310>GR1PCP9O3131CP2PA1:44P0P@PAf>R@PCO1RCPKP=n10110100021010000PCn0100000020000=1ACPGPCPAg00IVRC#R%QCPB1?B:P51?B9CM%LB%KBRCPB19B<R<g00KG%H;,9BC<,=CR=%G7RKPCPB19B;g00JBP<C<,=CR<PKPCP6P7P7P8P<P=FJC@C@1EC8P3P:18241N3:#2dADBL5COb<b=b>X6BX7BX8B135:145:14:9139D'>[[^6B^7B^8BP3P@f=,0>f?P:PDO5b;b5O1'Pb1b4b0b4W1g00MKR>912EPGPHO1,8AW1n0110000020100P3O1b1b9W0A12J>PHPDO1,8AW0n0110000020100P3O1b0b9PDP9P:P5CCPDP5O151AeW:X??X@BWAW5o"). Qed.
Lemma art_reveal_some : forall M lo hi a b, M a = Some b -> art_reveal M lo hi a = Some b.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) [] "p'0h01Hh11Mh21ah31bi001bh42b0h52hih62loh71oh81xi011xp;1p;2p;3p;6p;4g0000j10Tg000Uj18Tg0013j13Tg001VR0j1<Tg00A7j21Tg00@]j32Tg0028j27Tg0045j24Tg004Rj25Tg004oj26Tg00AYj2;Tg00<Fj2:Tg00Mkj69Tg00B[j4=Tg00HS#0#0#0R1#0#0#0#8R2#3R3%81R1#3R4#<R5]8g00I8R6f4R7f1R8O1f0R9,14R:525P51148R8g00ETR;P5f5R<f3R=,72R>'415>7'6P0P4P5P9P:g00Ji,;1,14n10110100021010000P9n0100000020000f2R1,14R:525X751721R2,47152='6P;P;P;P5P9114=R;P;n0100000020000=25;P91:5:R:P:n0110000020000b4P<P1O1P9E9P<P7P=P1C==258eW0X34X23X56W6W1o"). Qed.
Lemma art_reveal_defined : forall M lo hi a, lo <= bv_unsigned a < hi -> art_reveal M lo hi a <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) [] "p'0h02H0h12H1h21oi001oh31Hh41Mh51ah61bi011bh71eh82hih92loi021xp;1p;2p;3p;6p;4p;5g0000j10Tg000Uj15Tg0013j14Tg001VR0j17Tg0028j2ATg002bj2<Tg003>j2;Tg003Zj2:Tg00A7j23Tg00AYj29Tg00;Bj18Tg00@]j31Tg00Knj12Tg00B?j66Tg00Llj2@Tg00B[j4?Tg00NIj5=Tg00Mkj6>Tg00HS#0#0#0R1#0#0#0#5R2#4R3%51R1#4R4#7R5[g00I8R6f2R7f0R8,A2R2'<f1R9,;2':P5P0P4P5f4R2P9O1R:1348R;g00Ji,91,34R1n10110200021010100%84R<9158#2X25P:P5P0P4P0P4P5P8P;P1n10110200021010100=15<#2P8A15;<R;P51349P0P4p-0P8g00OYg00P5R0n10110000021000000X75R:g00PRR=P<P8E6P01@08R>b1W0%2;eX64P8O1A151<R4P5P1P:P=P<P8E6P0P>b1W0%24en10110000021010100b2P2f3R4P7P9C?P2P4P7P9P8D=E>W3X53X86W9W4o"). Qed.

Lemma art_zfill_in : forall M r len a, r <= bv_unsigned a < r + len -> art_zfill M r len a = Some (Z_to_bv 8 0).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) [] "h04__p1h14__x1h24__x2h31mh41nh52H0h61Mh77__arithh84__ffh98__varmaph:5__with;4__x3h<1Hh=1ah>1bh?3lenh@1rp;1p;2p;4p;3p;6p;7p;8g0000j14Tg000Uj1ETg0013j1>Tg001Vj1ITg0028j27Tg002bj22Tg00Pnj23Tg003>j21Tg003ZR0j29Tg0045j25Tg004Rj26Tg004oj2ATg005Mj2_Tg005mj1VTg006Mj1UTg006mj2CTg007Kj1TTg007ij4BTg008Gj1RTg008ej1QTg009Pj2:Tg00:3j4@Tg00;Bj1KTg00;dj2JTg00<Fj2DTg00<`j2LTg00=Lj3HTg00=kj4MTg00>]j2NTg00LGj1GTg00QKj3OTg00?=j4PTg00?Xj3FTg00@Aj4STg00@]j38Tg00AYj2^Tg00A7j2]Tg00B?j6\Tg00Qnj4WTg00Chj7XTg00:^j6YTg00DLj7ZTg00E0j8[Tg00ETR1f0R2g00F4R338p=0f1R4g00FTR5g00G3R6P6g00GSR7P2g00H3FXp=?P4P5P6P6P7P2EYp=;f2R8P5P6P6P7P4P2FZp==f3R9P5P6P6P7P8P4P2G[p=<g00HSR5#4R:#4#4R;#4#4#4#ER<#>R=%E;R;#>R>#IR?[g00I8R@17<2RA,281384,1A'9P117<4RA,59RB1398,6ARA'ARCP3%0B%0AP01542#01284RD[12421584#0[RE1598#0\D1_42P2n2001000000120000000X3@X4@PE^3@^4@P2f4RE17<8RDf5RFP8O1RGP?p-0RHg00IVRI#VRJ%UIRIP@1C@8RKP4%T@CB%R@RL%Q@RMP@1:@5RNg00JB1:@:R:C@,?MRO1;ME5=M%K6R6POC<1JM7R7P2P81D131L28#0dg00JiRO=H@4CMRPb8b9b:X1@X2@W01224/981248[^1@^2@^0HP217<ER<f6RQ/3F'1P<PQP9O4b7b6O3b5P01642#01184R0[11421684#0[RR1698#0\01N42P2n2001000000120000000X3@X4@PR^3@^4@P2PD13E9RRPGP?PJPIP@PKP41C@9CBPLPM1;MFP@PNg00KG%G5,:@9O@:C@,?MR:5=MP6P:C<P7PPb8b9b:X1@X2@X;@X0H1348,12,991389,14[^1@^2@^;@^0HP212Q<PFPQP<P9O5b7b6O3b5CP9FBACSA813CP1P3P1P?P21^;O,]>R>PQP9O1n0100000020000=8?>X>11D?>15ED16DR'AP2E\b5PEP9P8P4CW=8?>eW<X==X?@W@W6o"). Qed.
Lemma art_zfill_out : forall M r len a, ~ (r <= bv_unsigned a < r + len) -> art_zfill M r len a = M a.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) [] "p'0h02E1h12E2h21mh31nh42H0h51Mh64__x1h74__x2h84__x3h91bi001bh:1Hh;7__arithh<4__ffh=8__varmaph>5__with?1ah@3lenhA1rp;1p;2p;3p;4p;7p;8g0000j16Tg000Uj1BTg0013j1<Tg001Vj1FTg0028j21Tg002bj25Tg00Pnj22Tg003>j23Tg003ZR0j2=Tg00Knj1GTg0045j27Tg00<Fj29Tg00@]j30Tg004Rj28Tg004oj2;Tg00AYj2WTg00A7j2VTg005Mj2UTg00>]j2RTg005mj1QTg006Mj1NTg006mj2?Tg007ij4LTg008Gj1KTg008ej1JTg009Pj2:Tg00LGj1ITg00QKj3HTg00:3j4>Tg00;Bj1ETg00DLj7MTg00;dj2DTg00<`j2OTg00=Lj3PTg00=kj4CTg00Llj2STg00Qnj4TTg00Chj7YTg00E0j8XTg00ETR1f0R2g00F4R330p=4f1R4g00FTR5g00G3R6P6g00GSR7P2g00H3FYp=Af3R8P5P6P6P7f2R9P4P2GXp=@g00HSR:#6R;#6#6R<#6#6#6#BR=#<R>%B<R<#<R?#FR@[g00I8RA11=2RB,591294,3B'=#G11=4,78P11912RBf4RC11=9'7=012P1f6RD11=CRE'7=012P1P@f5RF,1=f7RG/2D'8RH,;4g00JiRI,W<,V?R?f8R<PFO1RJn0100000020000=0@J]0P411=8,7FRJ#412DF,8EP1PBA01H2P111=Gf9/2<'8=012P1P@1;34P?f;RHP<O1RBn0100000020000=0@B]1P411=D12<G'8RD#4P01742#41594[RB15421794#4RE[1589\E1U42P4n2001000000120000000X2AX3APB^2A^3AP2f:RB11=<R<PCO315B<P01842#41394[R013421894#4R<[1389\<1R42P4n2001000000120000000X2AX3AP0^2A^3AP211=BR0f</2HR<P8O3130<P1P@1;33P?f>R?PHO1RHn0100000020000=0@HPBPHP@g00IVRH#Q%NHPA1?A9P41?A8CL%KA%JARHPA1:A;R;g00KG1:A:R<%I:,:A5HAC>,AHR:%E6R0PHPAP<g00JBP;C>,AHR;P0PHP5P6P6P7P;P:FMC@C@1DH7P2P919131O29#4dAPAI4CCb<b=b>X6AX7AX8A1229,3415491598129C,38'=[[^6A^7A^8AP2P?f=,1=f?P9PCO5b;b5O1'Sb1b4b0b4W1g00MKR=901DPBPGO1,9@W1n0110000020100P2O1b1b9W0A01J=PGPCO1,9@W0n0110000020100P2O1b0b9PCP8P9P4CTPCP4O150@eW:X?>X@AWAW5o"). Qed.
Lemma art_unmap_in : forall M r len a, r <= bv_unsigned a < r + len -> art_unmap M r len a = None.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) [] "h04__p1h14__x1h24__x2h31mh41nh52H0h61Mh77__arithh84__ffh98__varmaph:5__with;4__x3h<1Hh=1ah>1bh?3lenh@1rp;1p;2p;4p;3p;6p;7p;8g0000j11Tg000Uj1FTg0013j1ETg001Vj1JTg0028j27Tg002bj24Tg00Pnj23Tg003>j22Tg003ZR0j29Tg0045j26Tg004Rj25Tg004oj2BTg005Mj2]Tg005mj1VTg006Mj1UTg006mj2DTg007Kj1TTg007ij4CTg008Gj1RTg008ej1QTg009Pj2:Tg00:3j4ATg00;Bj1;Tg00;dj2LTg00<Fj2>Tg00<`j2KTg00=Lj3ITg00=kj4MTg00>]j2NTg00LGj1HTg00QKj3OTg00?=j4PTg00?Xj3GTg00@Aj4STg00@]j38Tg00B?j6\Tg00S:j4[Tg00Chj7ZTg00:^j6WTg00DLj7XTg00E0j8YTg00ETR1f0R2g00F4R338p=0f1R4g00FTR5g00G3R6P6g00GSR7P2g00H3FZp=@P4P5P6P6P7P2EWp=<f2R8P5P6P6P7P4P2FXp=?f3R9P5P6P6P7P8P4P2GYp==g00HSR5#1R:#1#1R;#1#1#1#FR<#ER=%F;#ER;#JR>[g00I8R?17<2R@,481384,2@'9P117<4R@,69RA1398,5@R@'BRBP3%0A%0@P01642#01484RC[14421684#0[RD1698#0\C1]42P2n2001000000120000000X3?X4?PD^3?^4?P2f4RD17<8RCf5REP8O1RFP>p-0RGg00IVRH#VRI%UHRHP?1D?8RJP4%T?CC%R?RK%Q?RLP?1:?5RMg00JB1:?:R:CA,@LRN1<LD5?L%;6R6PNC=1LL7R7P2P81>131K28#0dg00Ji=I?4CMRNb8b9b:X1?X2?W01424/981448[^1?^2?^0GP217<DR<f6RO/3E'2P<POP9O4b7b6O3b5P01542#01284R0[12421584#0[RP1598#0\01N42P2n2001000000120000000X3?X4?PP^3?^4?P2PC13D9RPPFP>PIPHP?PJP41D?9CCPKPL1<LEP?PMg00KG%H5,:?9O?:CA,@LR:5?LP6P:C=P7PNb8b9b:X1?X2?X;?X0G1348,22,991389,24[^1?^2?^;?^0GP214O<PEPOP<P9O5b7b6O3b5CP9GA@CSA813BP1P3P1P>P2%;;R;POP9O1n0100000020000=8>;X>11>>;16DC15CP'BP2E\b5PDP9P8P4C[=8>;eW<X==X??W@W6o"). Qed.
Lemma art_unmap_out : forall M r len a, ~ (r <= bv_unsigned a < r + len) -> art_unmap M r len a = M a.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) [] "p'0h02E1h12E2h21mh31nh42H0h51Mh64__x1h74__x2h84__x3h91bi001bh:1Hh;7__arithh<4__ffh=8__varmaph>5__with?1ah@3lenhA1rp;1p;2p;3p;4p;7p;8g0000j17Tg000Uj1BTg0013j1@Tg001Vj1GTg0028j20Tg002bj23Tg00Pnj22Tg003>j25Tg003ZR0j2>Tg00Knj1HTg0045j26Tg00<Fj29Tg00@]j31Tg004Rj28Tg004oj2;Tg00;Bj1CTg005Mj2WTg00>]j2VTg005mj1UTg006Mj1TTg006mj2ATg007ij4NTg008Gj1MTg008ej1LTg009Pj2:Tg00LGj1JTg00QKj3ITg00:3j4=Tg00DLj7KTg00;dj2FTg00<`j2OTg00=Lj3ETg00=kj4PTg00Llj2QTg00S:j4DTg00Chj7RTg00E0j8STg00ETR1f0R2g00F4R331p=4f1R4g00FTR5g00G3R6P6g00GSR7P2g00H3FRp=?f3R8P5P6P6P7f2R9P4P2GSp=<g00HSR:#7R;#7#7R<#7#7#7#BR=#@R>%B<#@R<#GR?[g00I8R@10=2RA,391294,5A'>#H10=4,68P11912RAf4RB10=9'6=112P1f6RC10=BRD'6=112P1P?f5RE,0=f7RF/2C'8RG,;4%C<R<f8RHPEO1RIn0100000020000=1?I]0P410=8,6ERI#412CE,8DP1PAA11G2P110=Ff9/2H'8=112P1P?1;34P<f;RGPHO1RAn0100000020000=1?A]1P410=C12HF'8RC#4P01642#41394[RA13421694#4RD[1389\D1W42P4n2001000000120000000X2@X3@PA^2@^3@P2f:RA10=HRHPBO313AHP01842#41594[R015421894#4RH[1589\H1V42P4n2001000000120000000X2@X3@P0^2@^3@P210=AR0f</2GRHP8O3150HP1P?1;33P<f>R<PGO1RGn0100000020000=1?GPAPGP?g00IVRG#U%TGP@1A@9P41A@8CN%M@%L@RGP@1:@;R;g00KG1:@:RH%J:,:@5I@C=,?GR:%C6R0PGP@PHg00JBP;C=,?GR;P0PGP5P6P6P7P;P:FKC<C<1FG7P2P919131O29#4dg00Ji=E@4CPb<b=b>X6@X7@X8@1229,5413491398129B,58'>[[^6@^7@^8@P2P<f=,0=f?P9PBO5b;b5O1'Qb1b4b0b4W1g00MKR=911CPAPFO1,9?W1n0110000020100P2O1b1b9W0A11I=PFPBO1,9?W0n0110000020100P2O1b0b9PBP8P9P4CDPBP4O151?eW:X?>X@@WAW5o"). Qed.

Section Runs.
Variable segs : list Segment.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

Definition art_at_ecall (pc : word) : Prop := exists w, fetch_word segs pc = Some w /\ is_ecall w = true.

(* [comment removed for export] *)
Definition art_mmap_args (regs : bvmap 5 word) (addr len flags : Z) : Prop :=
  getr regs 17 = Z_to_bv 64 222 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len /\ getr regs 12 = Z_to_bv 64 3
  /\ getr regs 13 = Z_to_bv 64 flags /\ getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1) /\ getr regs 15 = Z_to_bv 64 0.
Definition art_munmap_args (regs : bvmap 5 word) (addr len : Z) : Prop :=
  getr regs 17 = Z_to_bv 64 215 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len.
Definition art_madvise_args (regs : bvmap 5 word) (addr len : Z) : Prop :=
  getr regs 17 = Z_to_bv 64 233 /\ getr regs 10 = Z_to_bv 64 addr /\ getr regs 11 = Z_to_bv 64 len /\ getr regs 12 = Z_to_bv 64 4.

Inductive aruns (Q : list aev -> machine_state -> Prop) : list aev -> machine_state -> Prop :=
| ar_done : forall log s, Q log s -> aruns Q log s
| ar_steps : forall log s s', msteps segs s s' -> aruns Q log s' -> aruns Q log s
| ar_mmap_fixed : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs addr len 50 -> EVOK log (AMmapFixed addr len) ->
    aruns Q (log ++ [AMmapFixed addr len]) (mkst (regupd regs 10 (Z_to_bv 64 addr)) pc' (art_zfill M addr len) rom) ->
    aruns Q log (mkst regs pc M rom)
| ar_mmap_null : forall log regs (pc pc' : word) M rom len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs 0 len 34 -> EVOK log (AMmapNull len 0) ->
    (forall r, GR log M len r ->
       aruns Q (log ++ [AMmapNull len r]) (mkst (regupd regs 10 (Z_to_bv 64 r)) pc' (art_reveal (art_zfill M r len) (art_shlo r) (art_shhi r len)) rom)) ->
    aruns Q log (mkst regs pc M rom)
| ar_mmap_fixed_nr : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_mmap_args regs addr len 16434 -> EVOK log (AMmapFixedNR addr len) ->
    aruns Q (log ++ [AMmapFixedNR addr len]) (mkst (regupd regs 10 (Z_to_bv 64 addr)) pc' (art_zfill M addr len) rom) ->
    aruns Q log (mkst regs pc M rom)
| ar_munmap : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_munmap_args regs addr len -> EVOK log (AMunmap addr len) ->
    aruns Q (log ++ [AMunmap addr len]) (mkst (regupd regs 10 (Z_to_bv 64 0)) pc' (art_unmap M addr len) rom) ->
    aruns Q log (mkst regs pc M rom)
| ar_madvise : forall log regs (pc pc' : word) M rom addr len,
    art_at_ecall pc -> pc' = Z_to_bv 64 (bv_unsigned pc + 4) -> art_madvise_args regs addr len -> EVOK log (AMadvise addr len) ->
    aruns Q (log ++ [AMadvise addr len]) (mkst (regupd regs 10 (Z_to_bv 64 0)) pc' (art_zfill M addr len) rom) ->
    aruns Q log (mkst regs pc M rom).

Lemma aruns_mono : forall (Q Q' : list aev -> machine_state -> Prop) log s,
  aruns Q log s -> (forall log' s', Q log' s' -> Q' log' s') -> aruns Q' log s.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) ["Runs"] "h03logh11Hh22H0h32H1h42H2h52H3h67IHarunsh71Mh83lenh92pch:3pc'h;4regsh<3romh=4addrh>1sh?1rh@2s'hA2H4hB2HQhC1QhD2Q'hE4log'p;1p;3p;4p;6p;2p;5p;>p;=p;<g006Mj1ZTg00TFj36Tg00UPj4RTg00VZj3KTg00Wdj6YTg0000j10Tg00LGj13Tg000Uj1<Tg0013j1CTg00Xnj2OTg001Vj1JTg00YZj1FTg0028j2DTg00Zij17Tg00Pnj2GTg00AYj25Tg00@]j3ETg00[Gj4?Tg00\Wj2>Tg005mj1UTg00]_j3TTg00^Bj34Tg00Qnj38Tg00_Lj52Tg00`Tl>QTg00a^j29Tg00bfj1PTg00d1j2ATg00B[j3@Tg00e<l=NTg00fFj2;Tg00gNl>LTg00hXj3MTg00ijj2:Tg00S:j3BTg00k2l>ITg00l<j3HTg00mOj2=Tg00nWl>STg00oal<XTg010mj3WTg011Mj3VTf4R0g011jR1f3R2f2R3f1R45W13Vf0R536p=1%Z1R6g0132R7p-0[[R8A6245f6R9P4P5O2P9P3P4O2[^@7^E6f5R:A6945X>7X06f7R;P4P5O2P;P3P4P2P3P4P5O3CRW1X>7X06p,4segs?K45f9R<?624A6<03f:R=P:P0P2P3P5EYW6W2W1X@7X>7X06g00HSR>#0R?#3R@#<RA%0?R?#0RB#0#0#0RC#<RD#CRE'ORF%<B#C#J\ERGg00I8RH%F:RI1DD9%7?R?'G,5D9EE:RJf8RKP2P3%3>#0#0#3#0#7C?p,4EVOKR>P=1>02O2fARLf;RM1>:0%U1R1p,2fxRN%0@#7g00PR5TARA15D:54=PKA8;:0R@P9D2ROD1PLf<RP1>9:P1PN15D994MAP<A8K9:RQP;D2RRD1fBRSf=RTPPPMP=P<PKP;P9P:P0P2P3P5M>QW6W5W4W3W2W1X8HW=X<GW7X:EX9EW;X06%F01DD:/G?,5D9EE0P;g00JiR?P3%3B#0#7C?P>P<192?O2p,2GRRBPMP;P:P5O4PSPP1994P1PN15D4RU94MAP<A8K49%P4RV1A493@P;D2D1[^?HPBPPPKP9P5O4PSPT19;4P1PNA4PAUP=A8<4;1A4;7@VPKD2D1[^?HPLPPPMP=P<PKP;P9P:P0P2P3P5M=NWAW5W4W3W2W1X8HX<GX7GX:EX9EX;FX06PKP2P3%0C#0#3#3#0#0#3#0#7C?P>P=1;02O2PLPM1;:0P1POD1PLPP1;9:P1PRD1PSPTPPPMP=P<PKP;P9P:P0P2P3P5M>LW6W5W4W3X2JX1IX8HX=HX<GX7GX:EX9EX;FX06AMK23P>P=1:02O2PLPM1::0P1PN15D?R?94=ARDPKAB;:0P9D2D1PLPP1:9:P1PNA4MA?R?P<ABK9:P;D2D1PSPTPPPMP=P<PKP;P9P:P0P2P3P5M>IW6W5W4W3X2JX1IX8HX=HX<GX7GX:EX9EX;FX06AHK23P>P=1=02O2PLPM1=:0P1PNPDPKP@P9D2D1PLPP1=9:P1PNP?P<PQP;D2D1PSPTPPPMP=P<PKP;P9P:P0P2P3P5M>SW6W5W4W3X2JX1IX8HX=HX<GX7GX:EX9EX;FX06P2P3P4M<XWBW1X>7X06XD8WCo"). Qed.

(* [comment removed for export] *)
Lemma aruns_bind : forall (Q1 Q2 : list aev -> machine_state -> Prop) log s,
  aruns Q1 log s -> (forall log' s', Q1 log' s' -> aruns Q2 log' s') -> aruns Q2 log s.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) ["Runs"] "h03logh11Hh22H0h32H1h42H2h52H3h67IHarunsh71Mh83lenh92pch:3pc'h;4regsh<3romh=4addrh>1sh?1rh@2s'hA2H4hB2HQhC2Q1hD2Q2hE4log'p;1p;3p;6p;2p;4p;5p;>p;=p;<g006Mj1YTg00TFj36Tg00VZj3STg00Wdj6KTg0000j10Tg00LGj13Tg000Uj1=Tg0013j1DTg00Xnj2PTg001Vj1NTg00YZj1ETg0028j2CTg00Zij17Tg00Pnj2GTg00AYj25Tg00@]j3FTg00[Gj4>Tg00\Wj2;Tg005mj1VTg00]_j3UTg00^Bj34Tg00Qnj38Tg00_Lj52Tg00`Tl>RTg00a^j2:Tg00bfj1OTg00d1j2@Tg00B[j3ATg00e<l=MTg00fFj2<Tg00gNl>JTg00hXj3LTg00ijj29Tg00S:j3BTg00k2l>ITg00l<j3QTg00mOj2?Tg00nWl>HTg00oal<TTg010mj3XTg011Mj3WTf4R0g011jR1f3R2f2R3f1R45X13Wf0R536p=1%Y1R6g0132R7p-0[[R8A6245f6R9P4P5O2A6934[^@7^E6f5R:A6945X>7X06f7R;P4P5O2P2P3P4P5O3W1X>7X06p,4segs?S45f9R<?624A6<03f:R=P:P0P2P3P5EKW6W2W1X@7X>7X06g00HSR>#0R?#3R@#=RA%0?R?#0RB#0#0#0RC#=RD#DRE'PRF%=B#D#N\ERGg00I8RH%E:RI1CD9%7?R?'G,5D9FE:RJf8RKP2P3%3>#0#0#3#0#7C>p,4EVOKR>P=1;02O2fARLf;RM1;:0%V1R1p,2fxRN%0@#7g00PR5UARA15D:54=PKA8;:0R@P9D2ROD1PLf<RP1;9:P1PN15D994MAP<A8K9:RQP;D2RRD1fBRSf=RTPPPMP=P<PKP;P9P:P0P2P3P5M>RW6W5W4W3W2W1X8HW=X<GW7X:EX9EW;X06%E01CD:/G?,5D9FE0P;g00JiR?P3%3B#0#7C>P>P<1:2?O2p,2GRRBPMP;P:P5O4PSPP1:94P1PN15D4RU94MAP<A8K49%O4RV1@493AP;D2D1[^?HPBPPPKP9P5O4PSPT1:;4P1PNA4PAUP=A8<4;1@4;7AVPKD2D1[^?HPLPPPMP=P<PKP;P9P:P0P2P3P5M=MWAW5W4W3W2W1X8HX<GX7GX:EX9EX;FX06PKP2P3%0C#0#3#3#0#0#3#0#7C>P>P=1<02O2PLPM1<:0P1POD1PLPP1<9:P1PRD1PSPTPPPMP=P<PKP;P9P:P0P2P3P5M>JW6W5W4W3X2JX1IX8HX=HX<GX7GX:EX9EX;FX06ALK23P>P=1902O2PLPM19:0P1PN15D?R?94=ARDPKAB;:0P9D2D1PLPP199:P1PNA4MA?R?P<ABK9:P;D2D1PSPTPPPMP=P<PKP;P9P:P0P2P3P5M>IW6W5W4W3X2JX1IX8HX=HX<GX7GX:EX9EX;FX06AQK23P>P=1?02O2PLPM1?:0P1PNPDPKP@P9D2D1PLPP1?9:P1PNP?P<PQP;D2D1PSPTPPPMP=P<PKP;P9P:P0P2P3P5M>HW6W5W4W3X2JX1IX8HX=HX<GX7GX:EX9EX;FX06P2P3P4M<TWBW1X>7X06XD8WCo"). Qed.

Lemma aruns_msteps_done : forall (Q : list aev -> machine_state -> Prop) log s s', msteps segs s s' -> Q log s' -> aruns Q log s.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) ["Runs"] "h01Hh12HQh21Qh33logh41sh52s'p;1p;3p;4p;6g006Mj13Tg00VZj32Tg00UPj40Tg00Wdj61Tg011j#3R0g0132R1p-0[[p,4segsf1R2f0R332f4R4f3R5P2O2f5R6P4P5f2R5P2P6P4P5P3C0E1W1W0X51X41X30W2o"). Qed.

(* [comment removed for export] *)
Lemma aruns_of_msteps : forall (Q : list aev -> machine_state -> Prop) log s s',
  msteps segs s s' -> aruns Q log s' -> aruns Q log s.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRuns ()) ["Runs"] "h01Qh13logh21sh32s'p;1p;3p;6g006Mj13Tg00VZj32Tg00TFj30Tg00Wdj61Tg011j#3R0g0132R1p-0[[p,4segsf1R2f0R332f4R4f3R5;02f5P4P5f2P2P3E1UUX31X21X10W0o"). Qed.

End Runs.
Arguments aruns segs EVOK GR {fx} Q log s.
