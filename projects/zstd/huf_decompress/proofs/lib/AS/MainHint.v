(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AsanPlan MainExport.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MainHint () := "I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib2AS8MainHint3mj1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbK47Corelib4Init5Logic2eq01I69OSSVerify5KrLib2AS:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport7vrangesC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib2AS:MainExport5mfact00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib2AS:MainExport8mjustifyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01c59OSSVerify5KrLib2AS8MainHint;mjust_hintsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes4list02C56Stdlib6NArith6BinNat1N6to_natC46Stdlib5Lists4List9nth_errorI47Corelib4Init9Datatypes6option00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List2InI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC46Stdlib5Lists4List<nth_error_InK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib2AS8MainHint<mjustify_mj1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC46Stdlib4Bool4Bool;andb_true_rK47Corelib4Init9Datatypes6option02C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbK47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib2AS8MainHint3pj1C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS:MainExport5pfact00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport8pjustifyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8MainHint;pjust_hintsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8MainHint<pjustify_pj1C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition mj1 (kn : list kentry) (VR : vranges) (HLO HHI : Z) (f : mfact) (K : kentry) : bool :=
    match f, K with
    | MCell a w v, KWord sa w' e =>
        if Nat.eqb w w' && is_cellw w && addr_match VR sa a && val_match e v then covered kn sa (Z.of_nat w) else false
    | MZeroC a n, KZero sa ne => if lit_len ne n && addr_match VR sa a then covered kn sa n else false
    | MZeroC a n, KWord sa w (ELit 0) => if Z.eqb n (Z.of_nat w) && addr_match VR sa a then covered kn sa n else false
    | MRo a w v, KWord sa w' e => Nat.eqb w w' && addr_match VR sa a && val_match e v
    | MZero a n, KZero sa ne => lit_len ne n && addr_match VR sa a
    | MFill a n c, KFill sa ne c' => Z.eqb c c' && lit_len ne n && addr_match VR sa a
    | MImg lo hi, KImg lo' hi' => Z.eqb lo lo' && Z.eqb hi hi' && (HLO <=? lo) && (hi <=? HHI)
    | MWr a n, KWr sa ne => lit_len ne n && addr_match VR sa a
    | MZeroS a n, KZero sa ne => sym_len VR ne n && addr_match VR sa a
    | MWrS a n, KWr sa ne => sym_len VR ne n && addr_match VR sa a
    | _, _ => false
    end.

Lemma mjustify_mj1 : forall kn VR HLO HHI f, mjustify kn VR HLO HHI f = existsb (mj1 kn VR HLO HHI f) kn.
Proof.
ltac2:(KReplay.run1 (kr_t_MainHint ()) [] "h03HHIh13HLOh22VRh31fh42knp;1p;5p;3p;2g0000j13Tg000Pj52Tg001Dj30Tg001`j21Tg002:R0#3g0039g0043R1g004Qg005Kf4R2f3f2f1f0D2=002'1W3X01W1W2W4o"). Qed.

(* [comment removed for export] *)
Fixpoint mjust_hints (kn : list kentry) (VR : vranges) (HLO HHI : Z) (fs : list mfact) (hs : list N) : bool :=
  match fs, hs with
  | [], _ => true
  | f :: fs', h :: hs' =>
      match nth_error kn (N.to_nat h) with
      | Some K => if mj1 kn VR HLO HHI f K then mjust_hints kn VR HLO HHI fs' hs' else false
      | None => false
      end
  | _ :: _, [] => false
  end.

Lemma mjust_hints_sound : forall kn VR HLO HHI fs hs,
  mjust_hints kn VR HLO HHI fs hs = true -> forallb (mjustify kn VR HLO HHI) fs = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MainHint ()) [] "p'0h01Hh12hsh22EJh32EKh42H0h51bi001bh61fh72fsh81xi011xh91Ah:1li021lh;3HHIh<3HLOh=2IHh>1Ki031Kh?2VRh@1ehA1hhB2knhC1oi041oi051ki061np;1p;4p;2p;6p;3p;5g0000R0j1<Tg005kj46j5FTg006fj1GTg001`j2?Tg007Fj69Tg008Bj6ATg008^j2=Tg009=j3ETg009]j17Tg00:=j38Tg00:[R1j1RTg00;=j31Tg000Pj64j5CTg00;Wj2QTg00<9j2DTg001DR2j3:Tg00<Wj3;Tg00<nR3j2>Tg00=Ij2BTg00=cj3PTg00>Fj5OTg00>gj4NTg00?Bj4LTg00?\j5KTg00@Yj6@Tg00A7j1JTg00AVj1ITg00B8j5MTg00BZj3HTg005KR4f5R5f4R6f3R7f2R8f1R9f0R:E9g00C6R;31p=2g004QR<?H9:p=5A14:;p=0AE<9:p=3g002:R=#<g0039g0043R>%<<R?P<g00CVR@#<RAf6RBP5P6P7P9P:E2f7RCPBP5P6C6/58#0[]1X7?P5P6P7P8%G<P:E21?4;W0X1APCPBP5P6P9P:E2f8RDPCPBP5C6/58#0[^1APDPCPBP51378P:E2P0P@f:R0f9REPDPC1356RFP:E2f;RGP0PEPDC613B5'5#0RH]0P9PEPDPCPB1367%G@RIE2P4P0PEPDPCPFPIE9P4p-0P:g00D4RIg00DQn0110000020000X@4RFg00DmREP;P:EAPI1=H:b4W0f=RHf<PGP013DCAE@9:E2f>RD%7858=%R=RJ1?J:f?RK%7758==1J:P1P=fARL%7558==1J:P1P=P4P9P4P4fCR1fBRMPLf@RNPDP:E4P1PMPLPNPHPBE9ROg00EIRPn0100000020000PPn10110100021010300#0P1PMPLPNC613DH'5#0RQ]0]3P9%7B98=M1Q=:51JP4P4P1PMPLPNPDP9E4POPPn0100000020000#0fDROP1PMPLPKP8E4P41?4:fERKPOP1PMPNP7E4=14:P4fGRDfFRRPKPOPMP5E4=14:P4P4P9fHR5PDPRPKPMPGE9PPn0100000020000#0fIRSP5PDPRC613O1'5#0RT]0]2P9PRPKPOP1PLP6E4RU#0PDPRPKPOPLP0E2P4P;PSP5PDPRPODF/D:#0X54P4P5PDPRPKP1DFR0%0:X54RVP4P5PDPRPKP1DC=:=5PVP2p4p710R2P4\:RV%<9RWP3A:89:#0A;6:8P7P:O1#0'>X87,B7R3[A;7:9P8P:O1#0'>X88,B8A:789#0[RXA:678#0\3AP89:P:n2001000000120000000W:W6W9PX^:W^6V^92P:P=PSP5PDPRPODCPSP=fJR29;=:P2PSP5PDPKP:E4#0'>X8=PCA;=CSPSP5PDPRPOPCE4#0P=PS%7HPCPBDOP8CNCLO4b4P0P5PDPRPKP1DKE@1D0;%J0E@P5PDPRPKC6RK/5MPLPGP:O2E@131M,5K#0eW0W2A14UPA14P;RUP4PPPFPEP;P:EAR;PI1=T:b4W0W2n0110000020100P:P8O2b2b5W0W3X>=P:O1%7698=N%I=51JP;PI1=Q:b4X0UW3n10110400021110500P:P8O2b3bCW0X1AXA@P9P:O2n10110200020021106102P:O1W0X1AW=X7?X6<P:DMW7X;>W<W?WBo"). Qed.

(* [comment removed for export] *)
Definition pj1 (VR : vranges) (f : pfact) (K : kentry) : bool :=
    match f, K with
    | PVar n lo hi, KRange (EVar n') lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
    | PRange e lo hi, KRange e' lo' hi' => val_match e' e && Z.eqb lo lo' && Z.eqb hi hi'
    | PDisj a1 n1 a2 n2, KDisj sa1 ne1 sa2 ne2 =>
        lit_len ne1 n1 && lit_len ne2 n2 && addr_match VR sa1 a1 && addr_match VR sa2 a2
    | PDisjS a1 n1 a2 n2, KDisj sa1 ne1 sa2 ne2 =>
        sym_len VR ne1 n1 && sym_len VR ne2 n2 && addr_match VR sa1 a1 && addr_match VR sa2 a2
    | _, _ => false
    end.

Lemma pjustify_pj1 : forall kn VR f, pjustify kn VR f = existsb (pj1 VR f) kn.
Proof.
ltac2:(KReplay.run1 (kr_t_MainHint ()) [] "h02VRh11fh22knp;1p;2p;3g0000j13Tg00Eij22Tg001Dj30Tg001`j21Tg002:R0#3g0039g00F]g005Kf1f0'2f2500'1W1W0W2o"). Qed.

Fixpoint pjust_hints (kn : list kentry) (VR : vranges) (fs : list pfact) (hs : list N) : bool :=
  match fs, hs with
  | [], _ => true
  | f :: fs', h :: hs' =>
      match nth_error kn (N.to_nat h) with
      | Some K => if pj1 VR f K then pjust_hints kn VR fs' hs' else false
      | None => false
      end
  | _ :: _, [] => false
  end.

Lemma pjust_hints_sound : forall kn VR fs hs,
  pjust_hints kn VR fs hs = true -> forallb (pjustify kn VR) fs = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MainHint ()) [] "p'0h01Hh12hsh22EJh32EKh42H0h51bi001bh61fh72fsh81xi011xh91Ah:1li021lh;2IHh<1Ki031Kh=2VRh>1eh?1hh@2knhA1oi041oi051ki061np;1p;2p;4p;6p;3p;5g0000R0j1<Tg00GWj26j3FTg006fj1GTg001`j2?Tg00HRj49Tg008Bj6ATg008^j2=Tg009=j3ETg009]j17Tg00:=j38Tg00:[R1j1RTg00;=j31Tg00Eij34j2CTg00;Wj2QTg00<9j2DTg001DR2j3:Tg00<Wj3;Tg00<nR3j2>Tg00=Ij2BTg00=cj3PTg00>Fj5OTg00>gj4NTg00?Bj4LTg00INj3KTg00@Yj6@Tg00A7j1JTg00AVj1ITg00B8j5MTg00BZj3HTg005KR4f3R5f2R6f1R7f0R8C9g00C6R931p=2g00F]R:?H78p=5A1489p=0AE:78p=3g002:R;#<g0039%<:R<P:g00CVR=#<R>f4R?P5P7P8C2f5R@/6?/56#0[]1X7<P5P6%G:P8C21?49W0X1>P@P?P7P8C2f6RA/6@/56#0[^1>PAP@1356P8C2P0P=f8R0f7RB13@?RCP8C2f9/6013A@'5#0RD]0P7PBPA13?5%G=REC2P4P0PBPCPEC9P4p-0P8g00D4REg00DQn0110000020000X>4RCg00DmRFP9P8EAPE1=D8b4W0f;RDf:RG130BAE=78C2f<%7658;%R;R01?08f=RH%7558;=108P1P;f?RI%7@58;=108P1P;P4P7P4P4f@R1f>RJ;48fARKP1PHPAC9RLg00EIRMn0100000020000PMn10110100021010300#016K113JH'5#0RN]0]3P7%7A98;11Q;8510P4P4A41J7PLPMn0100000020000#0A4KI6P41?48fBRI?415=148P4fDR1?4I@=148P4P4P7fFR@fERLPIPDC9PMn0100000020000#0fGRO/6@fCRP,31'5#0RQ]0]2P7A4PK?RR#0PLP1PKPGC2P4P9AFO@1/D8#0X54P4AF@LPRG%08X54RSP41CLP=:;@PSP2p4p710R2P4\8RS%<7RTP3A:678#0A;?86P5P8O1#0'>X85,B5R3[A;587P6P8O1#0'>X86,B6A:567#0[RUA:?56#0\3AP678P8n2001000000120000000W:W6W9PU^:T^6S^92P8P;1C@1POP;fH9;;8A4OL8#0'>X8;PBA;;BOA4@1B#0P;PO%7HPBPADOP6CNCLO4b4PGAK@LPE@1DG9%JGE@16@LRL/5IPKPDP8O2E@13PI,5L#0eW0W2A14RMA14M9RRP4PMPCPFP9P8EAR9PE1=Q8b4W0W2n0110000020100P8P6O2b2b5W0W3X<;P8O1%7?98;J%I;510P9PE1=N8b4X0RW3n10110400021110500P8P6O2b3bAW0X1>X?=P7P8O2n10110200020021106102P8O1W0X1>W;X7<X6:P8DMW7W=W@o"). Qed.

