(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ArtRegs () := "C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List:fold_rightC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude4tsetC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init5Logic2eq00I4ELinuxProcessSemantics5Riscv7Prelude4tree00K47Corelib7Numbers7BinNums8positive01K4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option02K4ELinuxProcessSemantics5Riscv7Prelude4tree02K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes6option01C47Corelib7Numbers7BinNums<positive_indK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums8positive00C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude6bv_keyc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRegs>tset_tset_sameC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6regupdC13~~~C4ELinuxProcessSemantics5Riscv7Prelude:bv_key_injc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRegs>tset_tset_commC13~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRegs4rinsC13~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z:compare_eqC45stdpp9bitvector;definitions5bv_eqc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRegs6rchainC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRegs=regupd_shadowC13~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z<compare_reflC47Corelib4Init5Logic6eq_indc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRegs;regupd_commC13~~~C47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes:comparison01I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes:comparison02I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRegs6rcanonC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ArtRegs7rins_okC13~~~C47Corelib4Init9Datatypes3snd".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma tset_tset_same {A} : forall (p : positive) (x y : A) t, tset p y (tset p x t) = tset p y t.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRegs ()) [] "p'0h01ti001th11ph21xh31yh41li011lh51ri021rh61vi031vh71Ah83IHpp;1p;4p;3p;2p;6p;5p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Mp4p7210p8p200R0g000lR1p4p710R2p8P0g001JR3p4p710p8p10025p4p7210R4g002aR5p4p710p8P4P2p8g003;R2j13TP3j41TP5j32Tg003hj1:Tg004Mj19Tg005:j1<Tg005\j40Tg006Ij26TP1j67Tg006cj1;Tg007Ej18Tg007jj2=Tg008Lj5>Tf6R1f5R5f4R3f3R4f2R6f1R7f0R8C1C1p=4P6g0093P7P8C1p=5g009XR9%33R:%35R;P5P4P7P5P4P6P8F4P5P4P7P8C132]0^34^26R<X19P2P1f7R=#3R>P=%:5R?P6P=P?P4P8F4P=P?P6P8C132P8%31R?P1P3P7%91R@C1RAP=%9=RB%<=RCP8C0P=PBPCP=P5P6PBC1RDC052>X0?P1P@%<1REPAC0,6?P1P3P7P1P3P6P@F4RFP4P6P7P@O3RGE7P1%:3RHP7P1PHP6P@F4P1PHP7P@C152?ef9RH#3RIf:RJ#;RKf;RL#3RMf<RN#3ROPNPJP=P8C1RPf=RQ#3RRPQP4P6P8C0PQP4P6PQPLf8RSP7C1C032X0OPNP6P7PPC0,6OPNPJP=PNPJPSP8F4PHPSP=P8O3E7PN%:JRPP=PNPPPSPNP6P7P8C0RTF4PNPPP=PTC152OeW5W6W4P6P7P8O3n10110000020030101103102X0;X33X24X8<X19P2P1P=%85RPP6P=PPP4P8F4P=PPP6P8C152>P8P?PAP=P8PCPBC0P=PDPCPBC052>X0?P1PAPEP@C0,6?PFPGE7P1%83RGP7P1PGP6P@F4P1PGP7P@C152?ePOPNPJP=P6C1R?PQP8P6P7C0PQPQPLPSP4C1P6P7C052RX0OPNP?P7P8C0,6OPNPJP=PNPJPSP6F4PHPSP=P6O3E7PN%8JRHP=PNPHPSPTF4PNPHP=PTC152OeX5MX6KX4IP6P7P8O3n10110000020030101103102X0;X33X24X8<X19%34P2P3A55489556A556852;P8P3%93R;1=37P;C0,6:A536;9537A537;52:e%;S%3JR:PJP61=J=P8C0'6PJP6P7P8C0R;95JS95J=A5J=;52:eX5IW6X4>P6P7P8O3n10110000020030101103102W0X36X27P8D>W1X70P8O1X70o"). Qed.

Lemma tset_tset_comm {A} : forall (p q : positive) (x y : A) t, p <> q -> tset p x (tset q y t) = tset q y (tset p x t).
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRegs ()) [] "p'0h03Hneh11qh21li001lh31ri011rh41vi021vh51ti031th63Heqh71Hh81pi041ph91xh:1yh;1Ah<3IHph=1fp%0p;1p;4p;3p;2p;6p;5p200R0g000lR1p4p710p8P0g001JR2p4p710p8g003;R3j15TP2j40Tg003hR2j17Tg004Mj1?Tg005:j1JTg005\j44Tg002aj36Tg006Ij2@Tg00:=j6ETg00:[j2DTg00;:j19TP1j6CTg006cj1FTg007ER1j18Tg007jj2<Tg008Lj5LTg00;Sj6ATg009XR4f1R5f0R636#9p=;f5R7f4R8f3R9f2R:P5C0;66p=1P9P:P5P6C4,@8p=2A6456p==P:P4P5P2P2P6EAp=GP4P4P2P:P5P6EAp=KP:g0093R;P5P6C0p=3P7P;P8P9P:P5P6C0C0p=>P:P4P5P1P1P6EAp=IP4P4P1P:P5P6EAp=HA64;6p=BP9P;P:P5C0=686p=:%571;89f7R<#5S00P<P7P9P<P8P:P5C0P<P8P:P<P7P9P5C0C0E1[]5^:8^99^14R=X84f6R>#5R?%77/;9P4%7<R@/;6f:RA#5RBPAf8RC#7RDP7PAP5P8P9C0REPAP5P8PAPDP7P9C0C0E1]0P8%76RF,;DP3f;RGf<RH#5RIPH%7ARJP<PH%7:RKP>P6C0RLPHPKP>PHPJP<P6C0RMC0E1P8%5GRNPGP5P7PGf9ROP>%?GRPC0RQC0RRPH%?HRS%JHRTP6C4PHPSPTPHP:P>PHPAP<PSC0C0S01C456IX5NPNPGPP%JGRUPRD2PGPOP>PGP5P7PPC0RVC0S02PCP5P>P7PP1=O5RWP4PJPJPKP4\4RXP6PGO1X=XRY1@X2R23GAKA:6EE1=JKg00<0RZP:P6O1'DS03b6W7%9WR[eO5ECPNPG%7OR\P>PG%75R]P7PPC0R^PGP]P7PGP\P>PPC0R_C0E1ef>R`#5Raf?Rb#FRcf@Rd#5RefARf#5RgPfP<PGPfPbPHP6C0RhC0RifBRj#5RkPjP9P:P6C4PjP9P:PjPCPHPjPdf=RlP5C0C0C436X5gPgPfP:P5PiD2PfPbPHPfP<PGP6C0RiC0P`P<PHPGP61=b<RmP4%7dRnPnPDP6PfO1X=XRo=GX2AKdC6EE1=nDPCP6O1,DZRZb6W7%9mRneO5ECPgPf%7bR2PHPfP@PGPfP:P5P6C4RpC0RqPfP@PGPfP2PHPpC0RrC0E1eW3W4W2P:P5P6O3n10110300020030100102101W0X14P6O1%86Rs,;DP3PGPIPHPJP<PH%8:RJP>P6C0RtPHPJP>PMC0E1P8PNPGPVPUPQD2PNPGP\P>PG%85R\P7PPC0RMPGP\P7P_C0E1ePgPfPfP<PGP:C0R_P5PhD2PgPfP2PHPf%8<R2PGPpC0RhPfP2PGPrC0E1eX3eX4cX2aP:P5P6O3n10110300020030100102101W0X14P6O1%7>=64;#9P3POPBPAPDP7A3A86RrPAP8PAPDP7P6E>E1P:%5ORDPO%?ORu1<O9RvPOP<P8PuC0RwD2PDPOP@P8A3O9uRxPOP9POP@P8PuE>E1e%FlRy%5bRzPbP:1<bOR{PbPlPAP6C0D2PzPb%7lR|PAPbP:P5P6C4R}93bOR~PbPOPbP|PAP}E>E1eX3aW4X2IP:P5P6O3n10110300020030100102101W0n011040003111041010400P6O1W0W5X:7X98X14X<=X84%87/;9P41;26PBPA%8CR|P7PEPAP5P8PAP|P7P9C0C0E1]0P81;|FP3PGPIPH%8AREP<PLPHPKP>PHPEP<P6C0RLC0E1P8PNPGPQPUPVD2PNPG%8ORVP>P^PGP]P7PGPVP>PPC0R^C0E1ePgPfPfPbPHP:C0RQP5PiD2PgPf%8bRiPHPqPfP@PGPfPiPHPpC0RpC0E1eX3eX4cX2aP:P5P6O3n10110300020030100102101W0X14P6O11;|sP3PGPIPHPEP<PtPHPJP>PLC0E1P8PNPRPHP6PTPSC4PHQ01PTPSC456IX5NPNPGPRPUPPD2Q02PCP5P>P7PPP4PEPEPJ1@X1R19IXYAHA:6EE1=EJQ03b6X7WP[eO5ECPNPGPVP>PMPGP\P7P^C0E1ePgPfP<PGPQC0RQPjP6P:P5C4PjPjPCPHPjPdPlP9C0C0P:P5C456kX5gPgPfPQP5P6D2PfPbPHP_C0P`P<PHPGP:P4%8dR_P_P|AIXo1AHdC6EE1=_|PZb6X7mPneO5ECPgPfPiPHPhPfP2PGPpC0E1eX3eX4cX2aP:P5P6O3n10110300020030100102101W0X14P6O1%8>=64;#9P3POPBPAP|P7PrPAP8PAP|P7P6E>E1P:PDPOPwPvPuD2PDPOP2P8PxPOP9POP2P8PuE>E1ePzPbPbPlPAP:C0P{P6D2PzPb%8lR{PAP~PbPOPbP{PAP}E>E1eX3aX4yX2IP:P5P6O3n10110300020030100102101W0n011040003101041110400P6O1W0X5?X:7X98X14X<=X84%58%B9#9P4%B6#9%5CR=PCP7PCP5P8P9C0PCP5P8A3C79C0D:]0P8%BF#9P3POPBPAP<PAPKP>P6C0PAPKP>A3A<6RKC0D:P8PDPOPu1<O>RFPOP5P7PuC0R?D2PDPOP>POP]P7PuC0POP]P7A3O>uR]C0D:ePzPbP:1<bHR{PbP<PGP6C0D2PzPbPHPbP@PGP}C0PbP@PGA3bH}R@C0D:eX3aX4yX2IP:P5P6O3n10110300020030100102101W0X14P6O1%Bs#9P3POPBPAP<PAPJP>P6C0PAPJP>PKC0D:P8PDPOP?PFPuD2PDPOP>POP\P7PuC0POP\P7P]C0D:ePzPbPbP<PGP:C0P{P6D2PzPbPHPbP2PGP}C0PbP2PGP@C0D:eX3aX4yX2IP:P5P6O3n10110300020030100102101W0X14P6O1A64;;Ry#9P3P<P=PCP7A3C86A3C7693C8D:P:1@4;R;PyPC%?CR31<C7P3C4PCP31<C8P3C456=P5P6O1'Db6Q00P<P8%?<R=93<9A3<8=93<9D:e%FGP;PyP`P91<`GP5C4P`P91<`AP5C456aP<P6O1'Db6%5lPlPAPlP:P5P6C4R<93lOA3lA<93lOD:eX3IW4X2BP:P5P6O3n10110300020030100102101W0n011040003101041010400P6O1W0W5X:9X9:X14P6DLX84X;0P6O1X;0o"). Qed.

Lemma regupd_shadow : forall regs (r : reg) x y, regupd (regupd regs r x) r y = regupd regs r y.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRegs ()) [] "h01rh14regsh21xh31yp;1p;2p;5p;3g007Ej10Tg003hj18Tg00<Mj13Tg00<kj12Tg0025j27Tg00=Nj26Tg00>;j55Tg00?Lj31Tg002aj34Tg0093#0R0#8#3R1%00#0#0#0#0#3#2R0'7R2%21P0f2R3,61f1R1f0R4f3R5D5A1531?134A1534542eX30X20W0W1o"). Qed.

Lemma regupd_comm : forall regs (r s : reg) x y, r <> s -> regupd (regupd regs s y) r x = regupd (regupd regs r x) s y.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRegs ()) [] "h01Eh13Hneh21rh34regsh41sh51xh61yp;1p;2p;3p;4p;7g007Ej10Tg003hj1:Tg00<Mj15Tg00<kj13Tg0025j29Tg002aj32Tg00;:j16Tg00=Nj24Tg00@Vj48Tg00AGj77Tg00?Lj31Tg0093#0R0#:#5R1%00#0#0#0#0#5#3R0'9R2%31R3f3R4f2R5523#6P0f4R6,41R71414R8P5f1R9f5R:g009X?278R8P9P1P:P6f0C8O1W0%68eF7A1:49?165A1:65?149522eW1X60X50X43W2W3o"). Qed.

Lemma regupd_eq3 : forall rg rg' (i : reg) v v', rg = rg' -> v = v' -> regupd rg i v = regupd rg' i v'.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRegs ()) [] "h02rgh11vh21ih33rg'h42v'p;1p;2p;3p;6g007Ej10Tg003hj18Tg00<Mj14Tg00<kj13Tg0025j27Tg002aj32Tg00?Lj31Tg006Ij26Tg000lj65Tg0093#0R0#8#4R1%00#0#0#0#0#4#3R0'7R2%31f4R1f3R3522f2R4f1R5520P2f5R6f0R7?161f6R8?163R9522X02P0P4A1867=229X10A1614,62P3P7E5P8P5E5UUX40X10W2X32W0o"). Qed.

(* [comment removed for export] *)
Ltac reg_index r := lazymatch r with Z_to_bv 5 ?z => z | @BV 5 ?z _ => z | _ => constr:(100%Z) end.
Ltac rnorm_raw :=
  repeat match goal with
  | |- context [regupd (regupd ?rg ?s ?y) ?r ?x] =>
      first [ constr_eq r s; rewrite (regupd_shadow rg r y x)
            | let zr := eval cbv in (bv_unsigned r) in
              let zs := eval cbv in (bv_unsigned s) in
              lazymatch (eval cbv in (Z.ltb zr zs)) with
              | true => rewrite (regupd_comm rg r s x y) by (let E := fresh in intros E; discriminate E)
              end ]
  end.

(* [comment removed for export] *)
Ltac rnorm_old :=
  lazymatch goal with
  | |- ?REL ?segs (?mk ?R ?pc ?M ?rom) ?B =>
      let mx := fresh "mx" in let bx := fresh "bx" in
      set (mx := M); set (bx := B); rnorm_raw; subst mx bx
  | |- _ => rnorm_raw
  end.

(* [comment removed for export] *)
Fixpoint rchain (base : bvmap 5 word) (l : list (reg * word)) : bvmap 5 word :=
  match l with nil => base | (r, v) :: l' => regupd (rchain base l') r v end.
(* [comment removed for export] *)
Fixpoint rins (r : reg) (v : word) (s : list (reg * word)) : list (reg * word) :=
  match s with
  | nil => (cons (r, v) nil)
  | (r', v') :: tl =>
      match Z.compare (bv_unsigned r') (bv_unsigned r) with
      | Lt => (r, v) :: s
      | Eq => (r, v) :: tl
      | Gt => (r', v') :: rins r v tl
      end
  end.
Definition rcanon (l : list (reg * word)) : list (reg * word) := fold_right (fun rv s => rins (fst rv) (snd rv) s) nil l.

Lemma rins_ok : forall base r v s, rchain base (rins r v s) = regupd (rchain base s) r v.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRegs ()) [] "p'0h01Eh11Hh22IHh32b1h42b2h51ci001ch61nh71rh82r'h91sh:1ah;1bi011bh<4baseh=1eh>1lh?2tlh@1vhA2v'i021pi031xp;1p;2p;3p;4p;6p;8p;5g007Ej1:Tg003hj1QTg00<Mj1@Tg00<kj18Tg0025j2PTg00BXR0j2OTg00C8j1ITg00CXj34Tg00D_j1ETg006Ij2<Tg00E?j33Tg00E_j21Tg00FIj29Tg002aj30Tg00Fjj47Tg00GJj3NTg00Gnj3LTg00HRj26Tg00?Lj32Tg00I[j4HTg00Jkj4?Tg000lj6>j8KTg00KGj1FTg00Kmj6ATg00:[j2JTg00;:j1DTg00LIj6CTg00MWj5MTf6R1f5R2f4R3'6f3R4f2R5'6f1R6f0R73230p=51645?267p=Bg00N9R8g00N_R9707p=;A25679034p=G1656=047p==g0093#:R:#Q#@R;%::#:#:#:#:#@#8R:'PR<%8;R=1O=:R>#IR?P>P<P3A4457P3P7P4P5F5X9?P4%E>P5P6CB,<<P0P=P:P<P1A4237P1P7P2P3F5P<f7R0A3>56R@9412P0P@P1P2F5[^>?P7P<f9R@f8RA?407P@P7PAP0F511;411;@RB'9P81<8711;3f:RC,1;'9=087P811;1RDf<RE,1;RF'9=087P<f>RGP8P?P6P=P:f=RHPEC7RI=3>2P=P:P0P1C7RJ=3>2RK93>IA4HE293>Jn011030003000000PGPKPHPEF5]0P611;2f;RK,1;'9RJg00OERI508ANDF7g00OkRL?0DFg00PIRF%87RD%86RMg00Pg%85?0671145114650LRN[1156115750L%84?056[RL%83?045\NAL567P7n2001000000120000000W4W3W6PL^4M^3D^6FP7P;PAPGP6O4A0=AGP=f?RFP<fARDP=P:f@RMPFC7=3>APDP=P:P7P@C7=3>APMPFF5X8=P<16M0RD?2FA?2FGA2DFGPDPFPAPGCHC?P<PMP=P:PFPGC7=3>0PMP=P:PFPAC7=3>0PFPGF5eP@P7E>b0b1b0W0g00QB908JPHP=P:P1P2C7RM=3>3PEPKCBRD,<<W0%;JP<16H3RJ?2EKRLP<A270116G2RN?201PHPEDGX;<P<A2J12?2EKA2L12PJPEP1PKP2A0=E1RJP=P0P<PFA47H1PFP1P7PHF511;6,9B#;g00<0R1]0]2X7=P<PGA40E2A2N0EC=11;AR;/9;#;P819BB%;7X58P7PI%FBEAA08I9P8PIP8p-0P7g00QhP1P1n011000003000000X=8g00RDP9P7EAP11J17b1b0W0W2PHP7P3P6GKW1%DJeECC?A4EK3RK,6HP4E>P<PHA3>MKPDC=eW0n011000103010001P7O1b0b5P<PCP=P:P4P5C7=3>6R594@APCP5P@PAF5eW2X??XA:X8=P6P7O2n2001102000121101101X:>P7DMW9X@:W7W<o"). Qed.
Lemma rchain_canon : forall base l, rchain base (rcanon l) = rchain base l.
Proof.
ltac2:(KReplay.run1 (kr_t_ArtRegs ()) [] "p'0h01lh11bi001bh22IHh31ah44baseh51rh62rvh71sh81vi011pp;1p;2p;3p;4p;6p;5g007Ej12Tg003hj1ETg00<Mj17Tg00<kj16Tg0025j2DTg00BXR0j2CTg00C8j1>Tg00R`j13Tg00HRj20Tg002aj31Tg00D_j1=Tg006Ij29Tg00E?j35Tg00?Lj3<Tg00Fjj4;Tg000lj68Tg00CXj34Tg00Sij4BTg0000j3@Tg00U3j3?Tg000Mj5:Tg00MWj5ATg0093#2R1#E#7R2%21#2#2#2#2#7#6R1'DR3%62R2/C1R4#>R5P4f2R6f0R7#3R8'01067513X05f1R9%=4R:'0,93P0P2P1f4R0/081007513f5R;A5469R<#3'010;<513[^05P7f7R</0810<7513P3f8R<%39R8'0R;f3R=;<6f9P2P1P0P=C;=546'0R>9137X13P310<9A<70==13>X13P2P1P=P6C;=549R>,0<R0,93P;P7E8A4=68,0<P<P=P6P8CBE8P5P4A@219A?219;47X75X64R8P:P9D:94=6,0<=130eP5P4P8P:P>D:,0<=130e%3>,0<=130eW2X05X81X52P9P7O2n2001101000121100100X34P7DAW0W4o"). Qed.

Ltac zr_plit p := lazymatch p with xH => idtac | xO ?q => zr_plit q | xI ?q => zr_plit q end.
Ltac zr_idx r :=
  lazymatch r with
  | @BV 5 ?z _ => lazymatch z with Z0 => constr:(z) | Zpos ?p => let _ := constr:(ltac:(zr_plit p; exact tt)) in constr:(z) end
  | Z_to_bv 5 ?z => lazymatch z with Z0 => constr:(z) | Zpos ?p => let _ := constr:(ltac:(zr_plit p; exact tt)) in let z' := eval cbv in (bv_unsigned r) in constr:(z') end
  end.
Ltac zr_ins r v z l :=
  lazymatch l with
  | nil => constr:(cons (z, (r, v)) nil)
  | cons (?z', (?r', ?v')) ?tl =>
      let c := eval cbv in (Z.compare z' z) in
      lazymatch c with
      | Lt => constr:(cons (z, (r, v)) l)
      | Eq => lazymatch r with r' => constr:(cons (z, (r, v)) tl) end
      | Gt => let tl' := zr_ins r v z tl in constr:(cons (z', (r', v')) tl')
      end
  end.
Ltac zr_sort R :=
  lazymatch R with
  | regupd ?R' ?r ?v => let l := zr_sort R' in let z := zr_idx r in zr_ins r v z l
  | _ => constr:(@nil (Z * (reg * word)))
  end.
Ltac zr_list R := lazymatch R with regupd ?R' ?r ?v => let l := zr_list R' in constr:(cons (r, v) l) | _ => constr:(@nil (reg * word)) end.
Ltac zr_base R := lazymatch R with regupd ?R' _ _ => zr_base R' | _ => R end.
Ltac zr_build base l := lazymatch l with nil => base | cons (_, (?r, ?v)) ?tl => let R0 := zr_build base tl in constr:(regupd R0 r v) end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rnorm_one R :=
  let base := zr_base R in
  let ls := zr_sort R in
  let R' := zr_build base ls in
  lazymatch R' with
  | R => fail
  | _ => let l0 := zr_list R in
         let e := constr:(rchain_canon base l0 : R' = R) in
         rewrite <- e
  end.
(* [comment removed for export] *)
Ltac rnorm_bad :=
  match goal with
  | |- context [regupd (regupd _ ?s _) ?r _] =>
      first [ let zr := zr_idx r in let zs := zr_idx s in
              let c := eval cbv in (Z.ltb zs zr) in
              lazymatch c with true => fail 1 | false => idtac end
            | idtac ]
  end.
(* [comment removed for export] *)
Ltac rnorm_all :=
  repeat match goal with
         | |- context [regupd (regupd ?rg ?s ?y) ?r ?x] =>
             let zr := zr_idx r in let zs := zr_idx s in
             let c := eval cbv in (Z.leb zr zs) in
             lazymatch c with true => rnorm_one constr:(regupd (regupd rg s y) r x) end
         end.
Ltac rnorm_new R := try rnorm_one R; rnorm_all; tryif rnorm_bad then rnorm_raw else idtac.
Ltac rnorm :=
  lazymatch goal with
  | |- ?REL ?segs (?mk ?R ?pc ?M ?rom) ?B =>
      let mx := fresh "mx" in let bx := fresh "bx" in
      set (mx := M); set (bx := B); rnorm_new R; subst mx bx
  | |- _ => rnorm_all; tryif rnorm_bad then rnorm_raw else idtac
  end.
