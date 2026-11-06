(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocInv_defs MallocInv_tables.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocInv_hints () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common8Mallocng@MallocInv_tables4ZseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib6Common8Mallocng?MallocInv_hints8chk_nestC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00c69OSSVerify5KrLib6Common8Mallocng?MallocInv_hints9cnt_candsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib6Common8Mallocng?MallocInv_hints;nest_targetC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib6Common8Mallocng@MallocInv_tables7Zseq_InC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c69OSSVerify5KrLib6Common8Mallocng?MallocInv_hints9nest_rankC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib4Bool4Bool8orb_propI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init9Datatypes3orbK47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03c69OSSVerify5KrLib6Common8Mallocng?MallocInv_hints9chk_nestsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01c69OSSVerify5KrLib6Common8Mallocng?MallocInv_hints=chk_cnt_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng?MallocInv_hints<chk_cnt_spanC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
Definition size_to_class_z (n : Z) : Z :=
  let m := (n + 3) / 16 in
  if m <? 10 then m else
  let m1 := m + 1 in
  let i := (Z.log2 m1 - 3) * 4 + 8 in
  let i1 := if size_class (i + 1) <? m1 then i + 2 else i in
  if size_class i1 <? m1 then i1 + 1 else i1.

(* [comment removed for export] *)
Fixpoint halvings (k : nat) (c : Z) : list Z :=
  match k with
  | O => [c]
  | S k' => if Z.even c then c :: halvings k' (c / 2) else [c]
  end.

(* [comment removed for export] *)
Fixpoint shrink (k : nat) (size c : Z) : Z :=
  match k with
  | O => c
  | S k' => if size * c <? 2^20 then c else shrink k' size (c / 2)
  end.

Definition cnt_base (sc : Z) : list Z :=
  if sc <? 9 then [small_cnt (3 * sc); small_cnt (3 * sc + 1); small_cnt (3 * sc + 2)]
  else halvings 8 (med_cnt (Z.land sc 3)).

Definition cnt_cands (sc : Z) : list Z :=
  map (shrink 40 (16 * size_class sc)) (cnt_base sc).

(* [comment removed for export] *)
Definition cnt1_of (size c : Z) : Z :=
  if c =? 1 then (if 2048 <? size + 16 then 1 else 2) else c.

(* [comment removed for export] *)
Definition nest_target (sc c : Z) : option Z :=
  let size := 16 * size_class sc in
  let c1 := cnt1_of size c in
  if size * c1 + 16 <=? 2048 then Some (size_to_class_z (size * c1 + 12)) else None.

Definition nest_rank (sc : Z) : Z :=
  if sc =? 15 then 1 else if sc =? 19 then 2 else if sc =? 23 then 3 else 0.

Definition chk_nest (sc : Z) : bool :=
  forallb (fun c => match nest_target sc c with
                    | None => true
                    | Some j => (nest_rank sc <? nest_rank j) && ((j =? 15) || (j =? 19) || (j =? 23))
                    end) (cnt_cands sc).

Lemma chk_nests : forallb chk_nest (Zseq 0 48) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_hints ()) ["WithLayout"] "p;2p;3p;1g0000j25Tg000Jj23Tg001Tj32Tg0020j34Tg002Jj10Tf0#0#0#0#0#0#0#0#0p=1g002iR0g003IR1'5g003ig004Gg005Tg0062#1#1#1#1#1#1'332=401do"). Qed.

Theorem nest_rank_ok : forall sc c j, 0 <= sc < 48 -> In c (cnt_cands sc) ->
  nest_target sc c = Some j -> nest_rank sc < nest_rank j /\ (j = 15 \/ j = 19 \/ j = 23).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_hints ()) ["WithLayout"] "p'0h01Hh12H2h24__x1h31xi001xh41mh51nh62H0h77__arithh84__ffh98__varmaph:5__with;1ch<2H1h=2Hch>2Hjh?3Hsch@1ji011jhA1ohB2schC1yp&0p;1p;2p;3p;4p;<p;6p;7p;Bp;8g006Qj18Tg0076j1ATg007[j1ITg0089R0j21Tg008UR1j2=Tg0090j1JTg00:>j3LTg00:UR2j1gTg00;7j2<Tg00<Gj2STg0020j3BTg002Jj13Tg000Jj2tTg001Tj3QTg004GR3j1WTg00<ij3VTg00=LR4j1TTg00=lR5j2MTg0000j2;Tg00>Ij3iTg00>oj1hTg00?Mj4fTg00@0l<cTg00@Uj6bTg00A>j1aTg00A^j1`Tg00B>j2_Tg00B\j1^Tg00C:j1]Tg00Cej2\Tg00DHj2CTg00Dkj4HTg00EVj1[Tg00F8k302Tg00F[k701Tg00G?k200Tg00Gaj2~Tg00HMj3{Tg00Hlj4sTg00I^j4rTg00JIj4qTg00KVj6XTg00L1j15Tg00M?j26Tg00M\j2DTg00N:j6pTg00NVj3oTg00O9j2lTg00OYj2>Tg00P6j3UTg00PRR6j2PTg00Plj2kTg00QLj1mTg00Qjj2nTg00RKj2KTg00S4j3jTg00S]j3OTg00TFj2NTg00U2j4uTg00UMj2vTg00Uil<wTg00VNlBxTg00W4j7yTg00WXj8zTg00X<j2ZTg00XYj3|Tg00Y9j7}Tg005TR7f0R8'vp=7%38#3#3#3p>03%38#3#3#3#3#3#3#3p=Fg002iR9g003IR:7B8p=0g00Y]R;g003iR<P<P<P4P4f5R4f4R=f3R>f2R?f1R@P8M<wp=eP<P<P<P<P<P<P5f7RAf6RBP4P5P=P7P7P>P?P@P8MBxp=dP@g00Z<R5g00Z[RCPCg00[;RDP8g00[[Fyp=@P>P5PCPCPDP?P@P8Gzp=G1>>?1>@8'Zp=91>@8,Z?p=EAB<@8p=2AB<?@/P8p=41>@8=B9:p=:g00\;RE?|@8p=?P<P@g00\gP8CHp=RP?P5PCPCPDP@P8F}p=Y%7?RFg00]NRG#8RH#A#A#A#A#IRI,1?'=%J>9L<?%g<RJ1<=>1S<?3Bg0062R=#3RK#3RL#3RM#3$03#F#F#F#F#FRN,t7RO9Q<3#0RPAL<8O%W@#0[^3<RQ[PP\QAV<3Og00^3P4PNP7P4%74RO%TNR3,M7RQ,14RP'=1M7IRR,14RS,=OPOPPPOPSp-0/;O9iOOP<P<P0P8X3<RSP011@8R0#hXC<X3<P4P41;<4PQPRPSPSPSP<P<g00_A1M@8Cf,;<X4<X5<1;<7P3PIPSPS%T8,;<X3;PNPI1;<IEeGdM<cEbP1PO114I%7B11BR'=P?%7Af8RO/1I%aERN%`ERE1_<@R;%^<RS%]<R3P<1\<GRQg00_eRP1C<IRTCH,@3%[CRUP3P<1C<7RVg00`LPQCH,@3RWPUP3P5PCPCPDPWP<PQPPB02<VTCH,@3K01CGCG2003DRDP8P?1;9:1~8?#0dA{<7@CsR7b8b9b:X2<118I%7@11?R,=F[[^2<P8f:RFP@P?O3b7W6W0P@P8O2n2001000000120000000CrCqEX%W4#0P2P<P91<A8%5ORR%58RV'6P8%8H#8#IRHP8%AGRT#A#8#8#IRPC9%8T#8#8#IRT7E8RW'DP:n10110000021010100X;<RC%JBR55Q<#0%JO9L<8P2P<P9f9RX/<@%5FRY/6V/DWP:n10110000021010100#0[^3<[%JARZ9L<8P2P<P91<O@%5XRX/6V/DWR[P:n10110000021010100#0[^3<P2P<P91<O8P[P:n10110000021010100X;<=Q<Z#0[AV<C5P8P4P?EXP2P<P91<B4%5AR5/6V/DWP:n10110000021010100#0PJ1<ABP2P<P9P8P[P:n10110000021010100#0XAJP81S<4P?Ep%54,65P4PHP4PPC9?E4T'D#0%5B,6RRJPBPHPBPPC9?EBTRB;o8%0J%0B'=P116X5#0PAPHPAPPC9?EAT#011YR12OT94OP94OH'=P8f;#5/6X#0PFPHPFPPC9?EFT#0P116@8#011?@[RF16?@#0RX\011>?\X1l@8P@n2001000000120000000X4<X5<PF^4<^5<P8f>RF#5RXf<#5R0P?O311X0f?R0#5f=RX#5'112XT94XP94XHP8PXPHPXPPC9RO1>XTRX;U?%0O%0X'PP6PFPHPFPPC9#01:FT120T940P940HP8P0PHP0PPC9#0f@RF/>HRX1>FPRF;U8%0X%0F'PP6fAR6/:H1:6PfBRF12FT94FP74HP81:FHP11:@812?@[RX12@81:?@RO[12>?\O1k@8P@n2001000000120000000X4<X5<ROPX^4<^5<RXP8fDR?PHP@O312?HP1fGR>#7RY11>IRRfFRA12AT94AP74HR5P?fI#7RBfJRJ/1IR:%mG,n<1K<M5j<RM1K<L5O<g00a3RL'N/?NPEP;PSP31C<H,RQ,@3RGPU1C<P,RQ,@3R[1C<T,RQ,@3RQ5Y39Y3GRGCGPDP7b8b9b:X2<128H12@T94@P94@HR9[^2<P8PJP4O2RJb7W6W0P@P8O2n2001000000121000000b1b0W1P8O11:FPPOPXP8P?PPP@O312?PP1PYPRP5P?1K<K9O<M/NLRK1?KN'?PEP;PSP3P[PUPGCGPDP7b8b9b:X2<128PP9[^2<PJb7X6:X0BP@P8O2n2001000000121000000b1b0W1P8O1n200100000021100011000b1W1P8O11:0TPOPXP8P6PTP@O3126TP1%7?11?IfCR?12?T94?P74HP6%7A1K<=9O<M/NLRL1?LN,?L'?PEP;PSP3PQPUPGCGPDP7b8b9b:X2<128TP9[^2<P8P>P4O2b7X6RW0P@P8O2n2001000000121000000b1b0W1P8O1n200100000021100011000b1Cub<b0W1W<P@P8O2n2001000000121000000b0b0b0b0W>W=W?X@<X;<XB<o"). Qed.

(* [comment removed for export] *)
Definition chk_cnt_range (sc : Z) : bool := forallb (fun c => (1 <=? c) && (c <=? 32)) (cnt_cands sc).
Lemma chk_cnt_ranges : forallb chk_cnt_range (Zseq 0 48) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_hints ()) ["WithLayout"] "p;2p;3p;1g0000j25Tg000Jj23Tg001Tj32Tg0020j34Tg002Jj10Tf0#0#0#0#0#0#0#0#0p=1g002iR0g003IR1'5g003ig00a_g005Tg0062#1#1#1#1#1#1'332=401do"). Qed.

(* [comment removed for export] *)
Definition chk_cnt_span (sc : Z) : bool :=
  forallb (fun c => 16 * size_class sc * cnt1_of (16 * size_class sc) c <? 2^20) (cnt_cands sc).
Lemma chk_cnt_spans : forallb chk_cnt_span (Zseq 0 48) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_hints ()) ["WithLayout"] "p;2p;3p;1g0000j25Tg000Jj23Tg001Tj32Tg0020j34Tg002Jj10Tf0#0#0#0#0#0#0#0#0p=1g002iR0g003IR1'5g003ig00c1g005Tg0062#1#1#1#1#1#1'332=401do"). Qed.

End WithLayout.
