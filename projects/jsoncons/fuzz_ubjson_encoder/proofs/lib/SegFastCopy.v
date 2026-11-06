(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore SegFastLoad.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SegFastCopy () := "I47Corelib4Init9Datatypes4list00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3B4AX2B4mkbcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3B4AX2B>know_lookupA0BC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX24lres01C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3B4AX2B5bc_fkC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX2>know_bytes_litC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX2<lit_of_bytesC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX24lres02C13~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3B4AX2B6mk_kixC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastLoad4AX2L7mk_kix2C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastLoad4AX2L?know_lookupA0I2C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastLoad4AX2LBknow_lookupA0I2_eqC13~~~C47Corelib4Init5Logic8eq_ind_rc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastCopy4AX2Y=know_lookupB2C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3B4AX2B<know_lookupBC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX24expr00C13~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX28sidecond00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX24lres00C13~~~I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX24lres03C13~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastCopy4AX2Y@know_lookupB2_eqC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastCopy4AX2Y8kread8e2C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<AsanPlanCore3APC8kread8eBC13~~~K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastCopy4AX2Y;copy_facts2C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<AsanPlanCore3APC;copy_factsBC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3lebC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<AsanPlanCore3APC<kread_bytesBC13~~~C47Corelib4Init9Datatypes4andbC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX2>zbytes_le_to_ZC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX24expr01C13~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymExec33AX26kentry01C13~~~K47Corelib4Init9Datatypes4list02c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastCopy4AX2Y;kread8e2_eqC13~~~C47Corelib4Init9Datatypes7nat_indK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastCopy4AX2Y;copy_facts3C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastCopy4AX2Y<copy_factsM2C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<AsanPlanCore3APC:copy_factsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<AsanPlanCore3APC@copy_factsB_eqf'C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastCopy4AX2Y>copy_facts2_eqC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;SegFastCopy4AX2Y>copy_facts3_eqC13~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00".
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module AX2Y.
Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Section Ctx.
Variable bc : bctx. Variable kx : kix. Variable kx2 : AX2L.kix2.

Definition know_lookupB2 (rb : expr) (rk : Z) (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match AX2L.know_lookupA0I2 bc kx kx2 segs rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs (bc_fk bc) rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.
Definition kread8e2 (b : expr) (off : Z) : option expr :=
  match know_lookupB2 b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.
Fixpoint copy_facts2 (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z) : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8e2 sb sk with Some _ => true | None => match APC.kread_bytesB segs bc 8 sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8e2 sb sk with
               | Some v => Some v
               | None => match APC.kread_bytesB segs bc 8 sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_facts2 f sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then
        match know_lookupB2 sb sk 1 false [] [], copy_facts2 f sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.
End Ctx.

Lemma know_lookupB2_eq : forall kn rb rk n sx hints acc,
  know_lookupB2 (mkbc kn) (mk_kix kn) (AX2L.mk_kix2 kn) rb rk n sx hints acc = know_lookupB segs (mkbc kn) rb rk n sx hints acc.
Proof.
ltac2:(KReplay.run1 (kr_t_SegFastCopy ()) ["WithSegs"] "p'0h03acch15hintsh22knh31lh41nh52rbh62rkh72sxi004acc'i012bsi026hints'i036hints0i043scsi051vi061xp;1p;9p;3p;5p;2p;:p;6p;8g0000j10Tg000Pj11Tg001`l93Tg003:j34Tg004Jj12Tg005[j57Tg0073j36Tg008Ij2<Tg009Yj35Tg00:3j2;Tg00:Mj18Tg00;_j19Tg00=2l::Tg00>Ml9@Tg00?kj6?Tg00@Il9>Tg00Abj8=Tg00C:#0g00DLg00E\R0g00F:g00FYR1%01g00G9#0g00HMR1f6R2#1R3p,4segsR4P2f5R5f4R6f3R7f2R8f1R9f0R:M93P1P1P:A489:R;g00I]R<%00R0P1P4f9#1#2f8R=f7R>P2D7A62>:?4891<9:R?n10110600021010100R@g00J?RAn011060003301051041032010010200P1P1%1>RBP4%2BP2P5P6P7P8P9M93P;P@PAn011060003301051041032010010200551X31P1P1P3P4%23P5P6P7P8P9P:M93P;P<P0P1P4%1=#2P>P2P5D7A652:?489P?n10110600021010100PAn011060003301051041032010010200,;1P3%82RA%92R?P4P5P6P7P8P9P:M::P3P2P4P5P6P7P8P9P:M9@E?P3PAP?P5P6P7P8P9P:M9>P4P3P5P6P7P8P9P:G=551eW0W1W7W4W6W5W2o"). Qed.
Lemma kread8e2_eq : forall kn b off, kread8e2 (mkbc kn) (mk_kix kn) (AX2L.mk_kix2 kn) b off = APC.kread8eB segs (mkbc kn) b off.
Proof.
ltac2:(KReplay.run1 (kr_t_SegFastCopy ()) ["WithSegs"] "p'0h01bh12knh21li001lh33offi015hintsi021si033scsi041vi051xp;1p;8p;2p;3p;9p;7p;6p;5p;4g0000R0j1@Tg000Pj12Tg00KOj10Tg00Knj11Tg00Abj84Tg00I]j1;Tg00LNj2:Tg00M0j16Tg009Yj33Tg00:3j27Tg00:Mj15Tg00;_j18Tg00@Il99Tg00MRj7?Tg00?kj6>Tg00Nnj5=Tg00PBj4<Tg00C:#@g00DLR1g00E\g00HMR2p,4segsR3f2R4#2R5f1R6f0R7g00QV#0#0#0#0#0#0#0#0R8g00R5R9g00FY#1R:g00G9R;#1R<G4R=%;1R>P2P>P7P0P;P>P61:14%61R1n10110300020020102100R;P1P1n011050003301041031012010310100P2P>P3f3#2P4P6P8P9P:P<G4P;P1P1n01105000330104103101201031010033X22P2P>P=P;P1P1n011050003301041031012010310100,7>P5%54R1%84R;P6P7P8P9P:P<M99P4P6P7P8P9P:P<F?E>P5P1P;P6P7D=P3P5P6P7C<53>eW3W0W1o"). Qed.
Lemma copy_facts2_eq : forall kn fuel sb sk db dk n,
  copy_facts2 (mkbc kn) (mk_kix kn) (AX2L.mk_kix2 kn) fuel sb sk db dk n = APC.copy_factsB segs (mkbc kn) fuel sb sk db dk n.
Proof.
ltac2:(KReplay.run1 (kr_t_SegFastCopy ()) ["WithSegs"] "p'0h02dbh12dkh21nh31oh42sbh52skh64fuelh72IHh81fh92knh:1li001li012bsi021ei035hintsi044resti051si063scsi071vi081xp;1p;9p;8p;3p;2p;4p;5p;6p;7g0000R0j1ITg00I]R1j1HTg000Pj14Tg00:Mj18Tg00;_j19Tg00RUl97Tg00Slj81Tg009Yj35Tg00:3j2ETg00PBj4CTg00UCj1?Tg00Uhj1BTg00VFj2:Tg00KOj12Tg00Vcj5JTg00X;j2ATg00LNj23Tg00XYj1PTg00Z1j1OTg00M0j1FTg00[Aj20Tg00[^j26Tg00\;j2<Tg00]Lj3>Tg00^^j3=Tg00Knj1@Tg00@Il9DTg00Abj8GTg00?kj6;Tg00MRj7NTg00Nnj5MTg00_>j3LTg00`Uj4KTg00C:R2#IR3g00F:R4g00DLR5g00E\R6%H3R7f7R8#4R9%88%98f5R:f4R;f3R<f2R=f1R>f0R?M97p,4segsR@P9P:P;P<P=P>P?G135^26^16^05]5]4R9X64P@f6RA#4g00QVRBP;P<P=P>P?G1,E7X26X16X05X56X45%H5RCP@f8RD#4REP;P<CCRFg00FYRGP7g00a6RH#?#?#?#BRI/:>RJP1P5PGP?g00a[RKP1%I6RLPGP@f9RM#4RN%2BRB#2#2#2#2#2#2#2ROP:P;DJRPPKg00R5RQn10110800021010000RRn10110800021010200'AP1P5P7P1P5PCP?135?RSP1PLPCPP%P?#O,35RP%F5RTn10110800021010100RUn10110800021010700P1P3P7f:RV#4RW%8V%9VPDPA10:IRXP;10<IRY16=IRZM971<:;?>O>==2?,33R[%F3R\n10110800021010400R]P\n10110800021010700PGP7%BHRH/:>R^g00HMR_P7PN%8M%9MP:P;PBPQ%@GR`g00G9Ra#@RbM9DP0PaP7P>P1P3P7f<Rc#4Rd%8c%9cPVPD108HRcPA10:HRe16;HRfM971<8A?>B<==2?,33RgP\n10110800021010400P\n10110600020020105100RhP\P\n011080003301071061032010610300%@2,33Rin0100000020000n0100000020000PGP7P1P5PGP@PNP:P;CCRjPKPRn10110800021010200,AJRJP1P5P7P1P5PCPjPSPUn10110800021010700RUP1P3P7P@PWPDPAPXP;PYPZG1P[P\n10110800021010400P\n10110800021010700RZPGP7P^P_P7P@PNP:P;PBPQP`PbGGRXP0PaP7P>P1P3P7P@PdPVPDPcPAPePfG1PgP\n10110800021010400P\n10110600020020105100P\P\n011080003301071061032010610300Pin0100000020000n0100000020000Rf557X3CP_P@PEP;P<PBPQP`PbGGRePGP7PJP1P5P7PUP]P\n10110800021010700PGP7P^P_P7P?PhP\P\n011080003301071061032010610300Pin0100000020000n0100000020000=57fX:_P7P@PEPAP;PYP=10>IR]16?IRcG1PGP7PJP1P5P7PUP1P3P7P>P[P\n10110800021010400P\n10110800021010700PGP7P^P_P7PXPhP\P\n011080003301071061032010610300Pin0100000020000n0100000020000=57fX37P7P@PEPAP;10<HRhP=10>HR[16?HRUG1PGP7PJPZPGP7P^P_P7PXP0PaP7P>P1P3P7P<PgP\n10110800021010400P\n10110600020020105100P\P\n011080003301071061032010610300Pin0100000020000n0100000020000=57fX37PGP71:I?P1P5PGPFPKP1PLPGP@PEPOP;P<DJRfPKPQn10110800021010000n10110800021010200'AP1P5P7P1P5PCPFPSP1PLPCPfPPPTn10110800021010100n10110800021010700P1P3P7P@PNP8P:10;IP<10=I16>IG11<;<?>O>==2?,33P\n10110800021010400P\n10110800021010700PGP71:H?P_P7PeP0PaP7P>P1P3P7P@f;#4PMP810AHP:10;H16<HG11<A:?>B<==2?,33P\n10110800021010400P\n10110600020020105100P\P\n011080003301071061032010610300Pin0100000020000n0100000020000,E7PE%8DRi%9DR\PAP;PhP=P[PUM97P:P;PhP=P[PUO5E;PEPiP\PAP;PYP=P]PcM97P:P;PYP=P]PcO5E;PEPiP\P;P<PBPQP`PbM9DPDP;P<PBPQP`PbFNE;PEPiP\P;P<DMALD;<E;PEPiP\%2ARAP;P<P=P>P?M97P@PEPAP;P<P=P>P?G1557eX26X16X05X56X45X79X84P?CKW6W9o"). Qed.
End WithSegs.

(* [comment removed for export] *)
Section Ctx3.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable bc : bctx. Variable kx : kix. Variable kx2 : AX2L.kix2.
Fixpoint copy_facts3 (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z) : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      let bytewise (u : unit) :=
        if Z.leb 1 n then
          match know_lookupB2 segs bc kx kx2 sb sk 1 false [] [], copy_facts3 f sb (sk + 1) db (dk + 1) (n - 1) with
          | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
          | _, _ => None
          end
        else Some [] in
      if Z.leb 8 n then
        match (match kread8e2 segs bc kx kx2 sb sk with
               | Some v => Some v
               | None => match APC.kread_bytesB segs bc 8 sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end) with
        | Some v => match copy_facts3 f sb (sk + 8) db (dk + 8) (n - 8) with Some rest => Some (KWord (SA db dk) 8 v :: rest) | None => None end
        | None => bytewise tt
        end
      else bytewise tt
  end.
Lemma copy_facts3_eq : forall fuel sb sk db dk n, copy_facts3 fuel sb sk db dk n = copy_facts2 segs bc kx kx2 fuel sb sk db dk n.
Proof.
ltac2:(KReplay.run1 (kr_t_SegFastCopy ()) ["Ctx3"] "p'0h01oi001oh12dbh22dkh31nh42sbh52skh64fuelh72IHh81bi011bh92bsi022bsh:1fh;1vi031vi041ei055hintsi061li074resti081si093scsi0:1xp;1p;6p;:p;3p;2p;5p;4g0000R0j1BTg00I]R1j1ATg00b;j67Tg00RUl:1Tg009Yj34Tg00:3j2:Tg00UCj1@Tg00Uhj1CTg00[Aj20Tg00[^j22Tg00VFj26Tg00Nnj6>Tg00LNj2<Tg00KOj15Tg00Vcj5=Tg00XYj1GTg00Z1j1FTg00M0j1ETg00\;j28Tg00Knj1?Tg00@Il:9Tg00X;j2;Tg00?kj6DTg00`Uj4JTg00]Lj3ITg00^^j3HTf4R2g00C:R3f3R4f2R5f1R63If0R73H'<p=3g00F:R8g00DLR9g00E\R:%B3R;#AR<f5R=P2P4P5P6P7E7p,4segsR>p,2bcR?p,2kxR@p,3kx2RAP=P2P4P5P6P7M:134^3:^2:^19]5]4RBX68P>P?P@PAg00QVRCP2P4P5P6P7M:1,:<X3:X2:X19X5:X49P<P>P?P@PAf6RDP2g00a6RE#@#@#@#CRF,04RGP5106FRH127FRIM:1g00FYRJP<16F6RKP1P9P<P1P9%A9RLP>P?P@PAP=P2E>RM1<97RNP1%B:ROPLP>P?%5CRC#5#5#5#5#5#5#5RPP=P2D=RQ%G7#F,<9RR%E9RSn10110:00021010200n10110:00021010300RTP1P;P<P6P;18=2PPP6P7D3RU%E;RVn10110:00021010700PJP<%CERE/66RWg00HMRXP<P>P?P@PAP=P2PCg00R5RY%?JRZg00G9R[#?R\M:9R]P0P[P<P6P1P;P<f:R^f8R_f7R`/0ERaPD10=ERb122ERcE7P;18`DRdPCP4P7D3RePVn10110:00021010700PVn10110900020020108106PVPVn0110:0003301031091052010910500%?3,<;R3n0100000020000Rfn10110:00021010300Pfn0100000020000PJP<P1P9PJPMg00a[RfP1POPJPQPfPYn10110:00021010600n10110:00021010400RQ,;KP1P9P<PTP1P;P<P>P?P@PAP_PD10=FRgP2PG125FM:1PUPVn10110:00021010700RUPVn10110:00021010300RhPJP<PWPXP<P]P0P[P<P6P1P;P<P>P?P@PAP^P_PaPDPbPcM:1PePVn10110:00021010700PVn10110900020020108106PVPVn0110:0003301031091052010910500P3n0100000020000Rcn0100000020000Rb54<X0<P<P>P?P@PAPDP2104ERiP5106ERj127ERkM:1PJP<PKP1P9P<PTPUPJP<PWPXP<P]P0P[P<P6P1P;P<P4PePVn10110:00021010700PVn10110900020020108106PVPVn0110:0003301031091052010910500P3n0100000020000Ren10110:00021010300Pen0100000020000=4<bX0<16F7RbPJPJPJP<P7P1P9P<P1P9PLP>P?P@PAPDP=E>RePNP1POPLP>P?PPPDP=D=R]PRPSn10110:00021010200n10110:00021010300RWP1P;P<P>P?P@PAf9RKP`10DFRlP=102FRm124FM:1P;18D=RnPPP6P7D3PVn10110:00021010700RoPJP<16E5PXP<P>P?P@PAPDP=PCPYPZP\M:9P0P[P<P6P1P;P<P>P?P@PAf;RpPK10_ERqP`10DERr12=EM:1P;18_`RsPCP4P7D3PVn10110:00021010700PVn10110900020020108106PVPVn0110:0003301031091052010910500P3n0100000020000Rtn10110:00021010300Ptn0100000020000PJP<P1P9PJPePfP1POPJP]PfPYn10110:00021010600n10110:00021010400,;7P1P9P<PWPoPVn10110:00021010300Ptn010000002000054<P7PMPLP1P9P1P9P<P1P9PLP7PNP1POPLP>P?PPP`PDD=RMPRPSn10110:00021010200n10110:00021010300RtP1P;P<P>P?P@PAP^P_10`FPDPg122FM:1P;PdPPP6P7D3PVn10110:00021010700RdPJP<16E4PXP<P>P?P@PAP`PDPCPYPZP\M:9P0P[P<P6P1P;P<P>P?P@PAf<P^10KEP_Pa12DEM:1P;18K_PCP4P7D3PVn10110:00021010700PVn10110900020020108106PVPVn0110:0003301031091052010910500P3n0100000020000Ran10110:00021010300PJP<P1P9PJP7PfP1POPJPMPfPYn10110:00021010600n10110:00021010400P1P9P<PtPdPVn10110:00021010300Pan010000002000054<P71:<dX;9P7O1P]%AOP1POP1P9P<P1POPLP7PRPSn10110:00021010200R]P1P;P<P>P?P@PAPpPK10_FP`Pl12=FM:1RlP;PsPPP6P7D3PVn10110:00021010700RdPJP<16E2PXP<P>P?P@PAP_P`PCPYPZP\M:9P0P[P<P6P1P;P<P>P?P@PAf=Pp10^EPKPq12`EM:1P;18^KPCP4P7D3PVn10110:00021010700PVn10110900020020108106PVPVn0110:0003301031091052010910500P3n0100000020000R^n10110:00021010300PJP<P1POPJP7PfPYn10110:00021010600P1P9P<P]PdPVn10110:00021010300P^n010000002000054<P7P1P;P<PlP;PsPP%G6#FP7D3PVn10110:00021010700,:<X9OP7O11:<an10110001021010600b0n10110001021010401b0P1P9P<PTPUPcn10110:00021010300PJP<1;fQPhPcn010000002000054<e1:<cPJP<1;YQPhPcn010000002000094<cen0110101020101b8PDP2PiP5PjPkE7P=P2PiP5PjPkO5EDPDP2PGP5PHPIE7P=P2PGP5PHPIO5EDPJP<PbP1P9P<P1P9PLP>P?P@PAP2P4E>RIPNP1POPLP>P?PPP2P4D=RLPRPSn10110:00021010200n10110:00021010300RSP1P;P<P`P=PmP4105FRR126FRFE7P;1824PPP6P7D3RPPVn10110:00021010700PJP<16E7RNPXP<P>P?P@PAP2P4PCPYPZP\M:9R\P0P[P<P6P1P;P<PKP`PrP=102ERZ124EREE7P;PnPCP4P7D3RCPVn10110:00021010700PVn10110900020020108106PVPVn0110:0003301031091052010910500P3n0100000020000Rnn10110:00021010300Pnn0100000020000PJP<P1P9PJPIPfP1POPJPLPfPYn10110:00021010600n10110:00021010400,;bP1P9P<PSP1P;P<P>P?P@PAP`P=PmP4PRPFM:1PPPVn10110:00021010700PVn10110:00021010300PJP<PNPXP<P\P0P[P<P6P1P;P<P>P?P@PAPKP`PrP=PZPEM:1PCPVn10110:00021010700PVn10110900020020108106PVPVn0110:0003301031091052010910500P3n0100000020000n010000002000054<e%5DRDP2P4P5P6P7E7P>P?P@PAPDP2P4P5P6P7M:154<eX3:X2:X19X5:X49X7BX:8P7CJW6o"). Qed.
End Ctx3.

Definition copy_factsM2 (segs : list Segment) (fuel : nat) (k : list kentry) :=
  copy_facts3 segs (mkbc k) (mk_kix k) (AX2L.mk_kix2 k) fuel.
Lemma copy_factsM2_eq : copy_factsM2 = @APC.copy_facts.
Proof.
ltac2:(KReplay.run1 (kr_t_SegFastCopy ()) [] "h04fuelh11kh21oh32dbh42dkh51nh62sbh74segsh82skh91xh:2x0h;2x1h<2x2h=2x3p;1p;2p;5p;3p;6p;4p;7p;8p;9p;:g0000j18Tg00I]j1OTg00cRR0j1@j2Nj3;Tg00djR1j1<j2Gj37j49j5Lj6Fj7Bj86Tg000Pj12Tg00:Mj11Tg00;_j13Tg00b;j5=j6:j7Mj8Kl9El:ITg00RUl:ATg009Yj35Tg00Slj8?j3DTg00:3j2CTg00f@j3>Tg00?kj64Tg00g\j8HTg00i6l:JTg00jPj50Tg00kR#8R2g00F:R3g00C:#8R4g00DLR5g00E\R6%O4R7^56R8^46R9^35R:]8R;]6R<]1R=]0P0P1P3P=f0R=#@%<=P4P<f1R1/N=1G1=P5P;f2R;%2=%1=%3=P1D=A7;1=R0P6P:f3R:%21%11%31P;P=E:P:P;P1P=C9P5P9f4R9%2;%1;%3;P:P1P=FMP9P:P;P1P=DLP6P8f5R8%2:%1:%3:P9P;P1P=GKP8P9P:P;P1P=EFP6P7f6R>%29%19%39P8P:P;P1P=M9EP>P8P9P:P;P1P=FBP7f7R?%28R@%18RA%38RBP>P9P:P;P1P=M:ARCf8P?P>P8P9P:P;P1G6RD957=X27REP7P?P@P>P9P:P;P1P=G?PEP<A7?>8P=P8P9P:P;P1O5=57DX2<P?P>P8P9P:P;P1P=G6,C7AD?@>A>?8>E4PCP?P8P>P9P:P;P1P=GHE4P?P@PAPBP>P9P:P;P1P=M:IP?P@PAPBP>P9P:P;P1P=M:JE4X=6D0X<6D0X;5D0X:6D0X95D0A;;1==5<0eX14D0X03D0X72D0o"). Qed.
End AX2Y.
