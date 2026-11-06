(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import MState.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_traces Po_rows Po_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_rowkit () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3eqbc69OSSVerify5KrLib2K53A239Po_rowkit6zl_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00c69OSSVerify5KrLib2K53A239Po_rowkit7row_eqbC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbc69OSSVerify5KrLib2K53A239Po_rowkit9zl_eqb_eqC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eqb_eqK47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes3nat00c69OSSVerify5KrLib2K53A239Po_rowkit7in_rowsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool<orb_true_iffc69OSSVerify5KrLib2K53A239Po_rowkit:row_eqb_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c69OSSVerify5KrLib2K53A239Po_rowkit9in_tracesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib2K53A238Po_iface7po_rowsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface5PO_TRC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib2K53A238Po_iface6po_rowC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List=Forall_forallc69OSSVerify5KrLib2K53A239Po_rowkit:in_rows_InC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53A239RT_traces=CLIENT_TRACESC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A239Po_rowkit;po_rows_rowC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes3nat02c69OSSVerify5KrLib2K53A239Po_rowkit8sub_rowsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallI46Stdlib5Lists4List6Exists00c69OSSVerify5KrLib2K53A239Po_rowkit5liftAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A239Po_rowkit<po_rows_liftC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib2K53A239Po_rowkit5liftBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A239Po_rowkit5liftCC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rc69OSSVerify5KrLib2K53A239Po_rowkit:rows_mode0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A239Po_rowkit<in_traces_InC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A239Po_rowkit7po_rowZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A239Po_rowkit>po_rows_top_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A239Po_rowkit:po_rowZ_eqC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint zl_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 => Z.eqb a b && zl_eqb r1 r2
  | _, _ => false
  end.

Lemma zl_eqb_eq : forall l1 l2, zl_eqb l1 l2 = true -> l1 = l2.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h01Hh12H0h22l2h32H1h41ah51bi001bh62b1h72b2h82l1h91mh:1nh;2r2h<2H2h=2IHh>1eh?2r1i011li021zp;1p;3p;2p;6p;8p;5p-1R0p10000p4p710p9P0p1000\R1p4p710p8P0P1p4p7210p8P0p10019p4p710p8p1001Up4p710R0g0022R1p4p710p8P0g002NR0p4p710p8g002lR2j1CTg003Lj30Tg003fj1:Tg004Fj29TP1j6<Tg004`j28Tg005?j24Tg005\j27Tg006Xj26Tg0076R1j25Tg007Qj2BTg0082j2ATg008Rj2@j3;Tg0092j8=TP0j6>Tg009Oj5?Tg00:1R0f1R3f0R4'7g00:QR530p=3g00;1R6?;34p=2A0045p=1%C6R7P61334f2R8=073[^27R9X87P2P6%:6R:/34A07:3[P4A0055197:U13::A07::[eg00;OR;=005R<P0P;P0p-0P4g00;oR;g00<Ln0110000020000X>0g00<hP5P4E<R5P;f3R=/28R>907:/84b1W01234R?,3:1283R@907:[eX;7X56P3P4O2n10110100020020102101X27P2P6f4R2/2=RA/34f5/22RB=073[P4P5P;A07B:/84b1X0<13>:A07A:[ef7RA/43f6R:/74'6#1P11634#1%18R>%13R<'5[R;%14,5<1683#1R<[%1=/5>\<1B34P3n2001000000120000000X70X60P;^70^60P4f9R0/4=R;f8R</78R>P3O3%1;%1>'5P1f:R>/42#1130=f;/2>R2=07BP4f<RB/4:#113B:P11434#1A0683[R1A06341483#1RB[A06=8\B1A34P3n2001000000120000000X96X:6P1^96^:6P4f?R1P0P8O3A0610P6P>f@RB,24=072X46P7P71@6>R>P>P1P0P7\7/9>f>P0P8O2G=PBP4E>b3b0W<W3P3P4O2n2001000000120000000b0b1W012A:/3?12<A=07@[eX;7X56P3P4O2n10110100020021102101X27X=9X?7X46P4D?W8o"). Qed.

Definition row_eqb (r1 r2 : list Z * nat) : bool := zl_eqb (fst r1) (fst r2) && Nat.eqb (snd r1) (snd r2).

Lemma row_eqb_eq : forall r1 r2, row_eqb r1 r2 = true -> r1 = r2.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h01Hh12H1h22H2h32b1h42b2h51mh62m1h71ni001nh82r2h92t1h:2H0h;2m2h<2r1h=2t2i011li021pp;1p;2p;3p;6p;4g002lj1?Tg00=DR0j2>Tg00=dj25Tg003Lj31Tg006Xj27Tg0076R1j24Tg007Qj2;Tg005\j26Tg00>aj23Tg00?Aj39Tg00@@j2:Tg004Fj2=Tg002Nj68Tg00@cj4<Tg00:1R2f0R3g00:Q31p=0f2R4g00ACR5f1R6P3C<p=2g00;1#?R7/>5R8P0P7P51563#0A1846[^88P3P0P7P5f3R0=274/53#0f4R9=270=186[P3f6R:f5R;527A2763'5#0P11763#0%04R<%06R='4[R>%03,4=1746#0R=[%00/4<\=1;63P6n2001000000120000000X42X32P>^42^32P3f8R2/60R>f7/34R=P6O3%0>%0='4P1f9R=/69#01320#0f:R>=27=A27;9518P3f;R;/6:#013;:#0f=R:?926A17:2P11363#0A1546[R1A15631346#0R:[A1504\:1:63P6n2001000000120000000X55X75P1^55^75P3f>R1P=P4O3A151=P7P;f@R19273f<R==27;R:518X97P5P>A27=3=18:X65A27;>,=8f?P3E8P1P4E8b2b0b1W2W1P6P3O2n2001000000120000000b0b:W0X;5X=7P6P3O2n2001102000121101100X88X65X97P6P3O2n2001102000121101100W<o"). Qed.

Definition in_rows (r : list Z * nat) (T : list (list Z * nat)) : bool := existsb (row_eqb r) T.

Lemma in_rows_In : forall r T, in_rows r T = true -> In r T.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h01Hh11Th22H0h32b1h42b2h52IHh61eh71rh81xi001bp;1p;2p;3p;6p;4p;5g002lj1:Tg00=Dj2DTg00Abj24Tg00B_j31Tg003Lj37Tg0022j6=Tg004`j2<Tg003fj1;Tg00=dj23j16Tg0019j35Tg00C6j28Tg00CSR0j22Tg00Cmj2CTg00DMj3BTg00EMj4@Tg00Eij3?Tg00FCj3>Tg008Rj39Tg009Oj5ATg00:1R1f0R2g00:QR337p=0g00;1#:g00AC'DR4%:4R5P4f2R6/42#0f3R7f1R8514[X15g00;OR9=713P1P9P1p-0P2g00;oR9g00<Ln0110000020000X61g00<hP3P2E=P91<92b2W0%;4R9,48#0A1469[e1472#0f4R9=148[1396%69=548'8#0g00761882#0%06R3%08R:'2[R;%02,2:1868#0R:[%07/23\:1C82P8n2001000000120000000X41X31P;^41^31P2f6R1/39R;%61=547R:P8O3%0;%0:'2P0f7R0f5R:'3#0%60=549#0f8R;9741A14;:'2P213;1#0f9R39740R<A1431R1P4P3P0AB302C@3?W0P2O1%6;=54:#0P:P2O19><1W0P2O1n200100000021000010000b0b2W0A9468,49#0A9476914:[eW5X15X84P2DAW1W7o"). Qed.

(* [comment removed for export] *)
Definition in_traces (t : list Z) (T : list (list Z)) : bool := existsb (zl_eqb t) T.

Lemma in_traces_In : forall t T, in_traces t T = true -> In t T.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h01Hh11Th22H0h32b1h42b2h52IHh61eh71th81xi001bp;1p;2p;3p;6p;4p;5g002lj1:Tg00F]j25Tg00B_j31Tg003Lj37Tg0022j6?Tg004`j2<Tg003fj1;Tg005\j24j13Tg0019j36Tg00C6j28Tg00CSR0j22Tg00Cmj2CTg00?Aj3BTg00EMj4ATg00Eij3>Tg00FCj3=Tg008Rj39Tg009Oj5@Tg00:1R1f0R2g00:QR337p=0g00;1#:R4%:4R5P4f2R6/52#0f3R7f1R8514[X15g00;OR9=713P1P9P1p-0P2g00;oR9g00<Ln0110000020000X61g00<hP3P2E?P91<92b2W0%;4R9,58#0A1469[e1572#0f4R9=148[1496%39=648'8#0g00761882#0%06R3%08R:'2[R;%02,2:1868#0R:[%07/23\:1C82P8n2001000000120000000X41X31P;^41^31P2f6R1/49R;%31=647R:P8O3%0;%0:'2P0f7R0f5R:'4#0%30=649#0f8R;9741A14;:'2P214;1#0f9R39740R<A1431R1P4P3P0AB302CA3>W0P2O1%3;=64:#0P:P2O19=<1W0P2O1n200100000021000010000b0b2W0A9468,59#0A9476914:[eW5X15X84P2D@W1W7o"). Qed.

(* [comment removed for export] *)
Lemma po_rows_row : forall fn ra ras t mode, po_rows fn ra ras -> in_rows (t, mode) (PO_TR fn) = true ->
  In (po_row t mode ra ras) CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "h02tmh11Hh21xh32Hbh42fnh55lemmah64modeh72rah83rash91tp;1p;3p;4p;2g00G\j11Tg00HAj1BTg00H_j1<Tg002lj16Tg00IBj3ATg00@cj44Tg00J>j13Tg00Abj2;Tg003Lj3:Tg00=Dj29Tg000\j37Tg00K8j38Tg00KUj42Tg00B_j30Tg00LPj35Tg00M1j2@Tg00MJj3=Tg00N;j3>Tg00N]j3?Tg00;1R0g00O]#1#1#1#1#1#1#B#<%60R0g00ACR1f4R2f3R3f2R43Ag00:1P0P1P4f1R4C4f5R5#3';g00:Q3:1901R6f0R79701R8A8017R9f6R:P5C2g00PBR5500X06R;%3:R<35f7R=#3R>9067P8P9f8R?P=C2=005X06P4O1[^26R@'@P8P9P=P:C2=005X06=56>%3?9067P8P9f9P?C2=005X06P4O1[^26;=7W5A>6;<P4O2P@P7P0P1P2P3C4R3A?3>4O2b1W3W1W6X90W8W7W4o"). Qed.

Lemma po_row0 : forall fn ra ras t, po_rows fn ra ras -> in_rows (t, 0%nat) (PO_TR fn) = true -> In t CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "h01Hh12Hbh22fnh32rah43rash51tp;1p;3p;4p;2p;7g00G\j10Tg00HAj19Tg00H_j12Tg002lj11Tg00IBj38Tg00@cj47Tg00J>j13Tg00Abj24Tg003Lj35Tg00QEj76Tg00;1R0g00O]#0#0#0#0#0#0#9#2%10R0f3R1f2R2f1R338g00:1P0g00ACP3g00RFR4C7f4R5#3'4g00:Q35f5P5P1P2P4P3f0F6W1W0X50W4W3W2o"). Qed.

Lemma po_row1 : forall fn ra ras t, po_rows fn ra ras -> in_rows (t, 1%nat) (PO_TR fn) = true -> In (t ++ ras) CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "h01Hh12Hbh22fnh32rah43rash51tp;1p;3p;4p;2p;7g00G\j10Tg00HAj1:Tg00H_j12Tg002lj11Tg00IBj39Tg00Rej18Tg00@cj43Tg00J>j14Tg00Abj25Tg003Lj36Tg00QEj77Tg00;1R0g00O]#0#0#0#0#0#0#:#2%10R0f3R1f2R2f1R339g00:1P0g00ACP3g00RF#8R4C3f4R5#4'5g00:Q36f5P5P1P2P4P3f0F7W1W0X50W4W3W2o"). Qed.

Lemma po_row2 : forall fn ra ras t, po_rows fn ra ras -> in_rows (t, 2%nat) (PO_TR fn) = true ->
  In (t ++ bv_unsigned ra :: ras) CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "h01Hh12Hbh22fnh32rah43rash51tp;1p;3p;4p;2p;7g00G\j10Tg00HAj1:Tg00H_j13Tg002lj12Tg00IBj39Tg00Rej11Tg00@cj48Tg00J>j14Tg00Abj25Tg003Lj36Tg00QEj77Tg00;1R0g00O]#0#0#0#0#0#0#:#3%20R0f3R1f2R2f1R339g00:1P0g00ACP3g00RF#1#1R4C8f4R5#4'5g00:Q36f5P5P1P2P4P3f0F7W1W0X50W4W3W2o"). Qed.

(* [comment removed for export] *)
Definition liftA (raC : Z) (tm : list Z * nat) : list Z * nat :=
  match snd tm with 0%nat => tm | 1%nat => (fst tm, 2%nat) | _ => (fst tm ++ [raC], 2%nat) end.
Definition liftB (raC : Z) (tm : list Z * nat) : list Z * nat :=
  match snd tm with 0%nat => tm | 1%nat => tm | _ => (fst tm ++ [raC], 1%nat) end.
Definition liftC (raC : Z) (tm : list Z * nat) : list Z * nat :=
  match snd tm with 0%nat => tm | 1%nat => (fst tm, 0%nat) | _ => (fst tm ++ [raC], 0%nat) end.

Definition sub_rows (f : list Z * nat -> list Z * nat) (callee caller : Z) : bool :=
  forallb (fun tm => in_rows (f tm) (PO_TR caller)) (PO_TR callee).
Definition rows_mode0 (callee : Z) : bool := forallb (fun tm => Nat.eqb (snd tm) 0%nat) (PO_TR callee).

Lemma po_rows_lift : forall (f : list Z * nat -> list Z * nat) callee caller ra ras ra' ras',
  sub_rows f callee caller = true -> po_rows caller ra ras ->
  (forall t mode, In (t, mode) (PO_TR callee) -> po_row t mode ra' ras' = po_row (fst (f (t, mode))) (snd (f (t, mode))) ra ras) ->
  po_rows callee ra' ras'.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h02Hsh12tmh21xh31Eh41li001lh51Ah61Ph74modeh81th91Hh:2H0h;2Hfh<3Hinh=6calleeh>6callerh?1fh@5lemmahA5mode'hB1pi011phC2rahD3ra'hE3rashF4ras'hG2t'i021np;1p;2p;3p;4p;7p;6g002lj1>Tg00=DR0j2LTg00G\j18Tg00HAj1?Tg00H_j1KTg00SDj3JTg00IBj3<Tg00J>j11Tg00B_j33Tg00KUj40Tg003Lj3:Tg00LPj3;Tg00N;j3ITg00Abj27Tg00TBj3=Tg00M1j2FTg00MJj3ETg00T^j3CTg004Fj2BTg00QEj7DTg002Nj6ATg00@cj4GTg000\j3HTg00K8j3@Tg00:1f0R1g00:Q3:p=2f2R2g00ACR3f1R4P1CGp=5AH431p=4A@431p=6g00PB9341p=9g00;1R5#>R6/L3R7P7[g00O]#8#8#8#8#8#8#?#KR8f6R9f5R:f4R;3J#2f3R<9<:;A5641R=f9R>#1R?537P2P4P9P:C0f;R@A5624RAO1RB,46166Bf8RBf7RCC05:6[^73^86g00UAp4p710RDp-0\1RE%>4RFg0076A;241A3;12P;P4O1[^2<RG[A3<14P<P4O1[^22A;<24[RHA;;<2\GAI241P1n2001000000120000000W4W6W5PH^4F^6E^5DP1P714611661P9P:C0,96X17P?P0P6P3%1@937114641664PBPCC0,96[P1f>#1937=P6f@R?PAO1RD,46166Df=f<C01961X46fARDP1O1f?#1RE'7X17RF==7E#2%1?R?9371fCRHP1O1%1DRG'7X17P4O1#2[^27RI'FfBRJP1O1/7?X17==7?#2A371GfDRGP1O1%1J'7X17P4O1#2[^27;E1W@AC7FEP>O2PIP1A56<2RIP4O2PDPIO1/7E#2PJA56;<O1P71B71PHA56:;O1=:71P0P6P3fEA56C9O1=:71%1G,74#214621662PGPHC0,96]0]3P4fHRHf:RG=56>O1=:7=fGR=#1,7A#2PHP=fFRHP<P2PJP1FD146I166IP=PHC0,96eW0W3XA3XG6P4P1O2n2001101000120100102P1P2O2b3bBb0b0P2P4P@PGC0PCP2P4P1O3EA146A166AP@PGC0,96eW<X73X86P4P1O2n2001101000121100102X27O4b:A<B;<eW;W9W0XF6XD8XE6WCX>5X=5W?o"). Qed.

(* [comment removed for export] *)
Lemma po_rows_callA : forall callee caller raC ra ras, sub_rows (liftA raC) callee caller = true -> 0 <= raC < 2 ^ 64 ->
  po_rows caller ra ras -> po_rows callee (Z_to_bv 64 raC) (bv_unsigned ra :: ras).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h02_Hh11Hh22HRh32Hsh46calleeh56callerh61lh74modeh85mode0h91ni001nh:2rah;3raCh<3rash=1th>1zp;1p;3p;2p;4p;6p;:g00G\j16Tg00HAj1STg00H_j1HTg002lj1ETg00U^j1Aj29Tg00SDj3RTg003Lj33Tg00VYj2GTg00W5j1@Tg00WSj2FTg00X0j2DTg0076j2CTg00IBj3BTg00XLj27Tg00Y2j25Tg00=Dj2QTg00J>j1<Tg00B_j3;Tg00KUj41Tg000\j38Tg00K8j3:Tg00@cj4?Tg004Fj2>Tg00Rej1=Tg003fj1ITg00Y\j4JTg0022j6KTg00Z:j2LTg002Nj6MTg00[9l:NTg008Rj3OTg00\;j3PTg00;1R0f1R1f0R23Op=0f2R3g00ACR4P1P2C?p=4AP012p=2g00O]#6R5#6#6#6#6#6R6#SR7#H%E0R8g00:1%A3f4R9f3R:3Rg00:Q33g00\X/G:%@5%@6'F,D:'Cf5R6?B:3%A6f7R5f6R;P9P:17761579/0:P3P2P41Q84R<A4832f:R=#<3;P:P1f9R>,77f8R?,57/05C1A48:1,9>R@9884A:84@P?P5C1538[P2P8P4P1g00RFR@C?%<>5;<1>83P3P@177?1575/0;C1P8P4P3P@C?,9?R39884A:843P5P;C1538eW0P4%=2R39489f<RA#<5;<P6%=1R1f;RB,77157=/0>C1A4861,9BRC9884A:84CP=P>C1538[P2%=@R@948:%<B5;<157>/0?R:,29,>8P9P@177=P:C1A489@,9=R@9884A:84@P>P?C1538eW0%=39486f=R6#<5;<P0PA157A/0BR<,02,25%I0R3,06,25/2<538X>0P810A3R3157B/0=R>'2,2;R@106<,25=382X681>8@12;3/2>P0P;P3P>CJEK177AR3,571LA?EMP;%=1R1P3P>C1A48;1,9ARA9884A:84APBP=C1538eW0X74P2O1n0110000020011100X94P2O1n0110000020011100X84X=8M:NW1W2W3W<W:X;0X50X40o"). Qed.

(* [comment removed for export] *)
Lemma po_rows_callB : forall callee caller raC ra ras, sub_rows (liftB raC) callee caller = true -> 0 <= raC < 2 ^ 64 ->
  po_rows caller ra ras -> po_rows callee (Z_to_bv 64 raC) ras.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h02_Hh11Hh22HRh32Hsh46calleeh56callerh61lh74modeh85mode0h91ni001nh:2rah;3raCh<3rash=1th>1zp;1p;3p;2p;4p;6p;:g00G\j14Tg00HAj1RTg00H_j1HTg002lj1DTg00]6j1@j29Tg00SDj3PTg003Lj32Tg00VYj2GTg00W5j1?Tg00WSj2ETg00X0j2CTg0076j2BTg00IBj3ATg00XLj25Tg00=Dj2QTg00J>j1:Tg00B_j3;Tg00KUj40Tg000\j38Tg00K8j36Tg00@cj4>Tg004Fj2=Tg00Rej17Tg008Rj3<Tg003fj1FTg00Y\j4ITg0022j6JTg00Y2j2KTg00Z:j2LTg002Nj6MTg00[9l:NTg00\;j3OTf2R0g00ACR1f1R2f0R3C>p=3g00;1R4?O23p=1g00O]#4R5#4#4#4#4#4R6#RR7#H%D4R8g00:1%@0f4R9f3R:3Pg00:Q32g00\X/G:%?5%?6'E,C:'Bf5R6?A:0%@6f7R5f6R;P9P:1576P:P0P3P11Q81R<A3803f:R=#:3;P:P2f9R>,57P5C0A38:2,9>R?9881A681?f8R?P5C0528[P3P8P1P2g00RFR@C>%:>5;<1=80P0P@157?P;C0P8P1P0P@C>,9?R09881A6810P5P;C0528eW0P1%73R09389f<RA#:5;<P6%72R2f;RB,57P>C0A3862,9BRC9881A681CP=P>C0528[P3%7@R@938:%:B5;<119?,=8P9P@157=P?C0A389@,9=R@9881A681@P>P?C0528eW0%709386f=R6#:5;<P4PAA<43B,15%F4R<9<46,15/1B528X>4P8A<4A<R</1=,1;R0A<46B,15=283X681=8011;</1=P4P;P<P=CIEJ157AR<,K71LA?EMP;%72R2P<P=C0A38;2,9ARA9881A681APBP=C0528eW0X71P3O1n0110000020010100X91P3O1n0110000020011100X81X=8M:NW1W2W3W<W:X;4X54X44o"). Qed.

(* [comment removed for export] *)
Lemma po_rows_callC : forall callee caller raC ra ras, sub_rows (liftC raC) callee caller = true -> 0 <= raC < 2 ^ 64 ->
  po_rows caller ra ras -> po_rows callee (Z_to_bv 64 raC) [].
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h02_Hh11Hh22HRh32Hsh46calleeh56callerh61lh74modeh85mode0h91ni001nh:2rah;3raCh<3rash=1th>1zp;1p;3p;2p;4p;6p;:g00G\j13Tg00HAj1PTg00H_j1ITg002lj1ETg00^1j1Aj27Tg00SDj3JTg003Lj32Tg00VYj2HTg00W5j1@Tg00WSj2FTg00X0j2DTg0076j2CTg00IBj3BTg00XLj24Tg003fj1OTg00=Dj2NTg00J>j19Tg00B_j3:Tg00KUj40Tg000\j38Tg00K8j35Tg00@cj4=Tg004Fj2<Tg00Rej16Tg00\;j3;Tg00^lj2GTg002Nj6?Tg008Rj3>Tg00Y2j2KTg00Z:j2LTg00[9l:MTf2R0g00ACR1f1R2f0R3C=p=1g00;1R4g00O]#3R5#3#3#3#3#3R6#PR7#I%E4R8g00:1%A0f4R9f3R:3Jg00:Q32g00\X/H:%@5%@6'F,D:'Cf5R6?B:0%A6f7R5f6R;P9P:1476%O4R<P0P3P11N81R=A1803f:R>#93:P:P2f9R?,47P<C0A18:2,7?R@9881A581@f8R@P5C0528[P3P8P1P2g00RFRAC=%9?5:=1<80P0PA147@P<C0P8P1P0PAC=,7@R09881A5810P5P;C0528eW0P1%63R09189f<RB#95:=P6%62R2f;RC,47P<C0A1862,7CRD9881A581DP>P?C0528[P3%6ARA918:%9C5:=P8P9A2836X681<89A;49<1G49E?P9PA147>P<C0A189A,7>RA9881A581AP?P@C0528eW0%609186f=R6#95:=P4PBA>43<9;45A>46<9;45528X>4A>4B<9;4;,<8147BR5,K71LB@E?P;%62R2P5P<C0A18;2,7BRB9881A581BPCP>C0528eW0X71P3O1n0110000020010100X91P3O1n0110000020011100X81X=8M:MW1W2W3W<W:X;4X54W4o"). Qed.

(* [comment removed for export] *)
Lemma po_rows_tail : forall callee caller ra ras, sub_rows (fun tm => tm) callee caller = true ->
  po_rows caller ra ras -> po_rows callee ra ras.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "h01Hh12Hsh22_Hh36calleeh46callerh54modeh62rah73rash81th92tmp;1p;2p;3p;4p;:g00G\j10Tg00HAj1?Tg00H_j13Tg002lj12Tg00=Dj2>Tg00SDj3:Tg003Lj35Tg00IBj34Tg00@cj41Tg00J>j16Tg00B_j37Tg000\j38Tg00K8j39Tg00KUj4=Tg004Fj2<Tg00[9l:;Tg00;1R0g00O]#0#0#0#0#0#0#?#3%20R1g00:1g00ACR2,>1R3f0R4W9R5f3R6f2R73:g00:Q35f1R89467P5f5R5f4P6P7P6P7P8P4P1P2P8P4C1f7#6573P1P2P7P8C1R89812A9128f6P5C=,<1W2X52X81M:;W0W1W7W6X40W3o"). Qed.

(* [comment removed for export] *)
Lemma po_rows_any : forall callee caller ra ras ra' ras', rows_mode0 callee = true -> sub_rows (fun tm => tm) callee caller = true ->
  po_rows caller ra ras -> po_rows callee ra' ras'.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "h02H0h13Hinh21mh34modeh41nh52tmh61xh71Hh82H1h92Hsh:6calleeh;6callerh<5lemmah=2rah>3ra'h?3rash@4ras'hA1tp;1p;2p;3p;4p;7p;:g00G\j11Tg00HAj1HTg00H_j1>Tg002lj1;Tg00_Jj1GTg00=Dj2?Tg00SDj3=Tg00IBj3<Tg00@cj44Tg00J>j12Tg00B_j35Tg00K8j36Tg00>aj27Tg00TBj3:Tg00M1j2FTg00MJj3BTg00T^j3ATg003Lj33Tg00@@j2@Tg00KUj48Tg000\j39Tg004Fj2CTg002Nj7DTg00[9l:ETg00:1f0R0g00:Q33p=0g00;1R1g00O]#1#1#1#1#1#1#H#>R2%;1R3f5R4#G#0g00ACR5,?3R6P0W5R7f6R8;=4#0f4R99<84P7f8R7f7R:P8P4P9f3R;f1R<P0P3P5P<P0C4f:#2556A6350g00RFR='7X56R>f;#2R?5:6#0f<R@#2RA9560P>P<O1#0RB[^66RC'FA:6>A#0f=RA#29560PB[^66;B0W<AA6>?P4O2PCP0P3P5P;f2RCC4R?P<O2A635?/7=#0g007617<0#0A35C<[R?A35<017C<#0R>[A35;C\>1@<0P<n2001000000120000000X25X45P?^25^45P0P9P=P<O3A359=P5P=P3P5P:P0C4f@#2556P7P<PAP@C8P3P5P7P<C4R<9935A635<f?R<f>R7C8533]1X35P3P5P8P=C4%2<556P3P5P:P=C4R=9935A635=P7PAC8,C3W1P4P0P9FDb0b8b0b0W1X35XA3M:EW7W9W0X@3X>2W?W=X;1W:o"). Qed.

(* [comment removed for export] *)
Lemma po_rows_of_traces : forall fn ra ras, rows_mode0 fn = true ->
  forallb (fun tm => in_traces (fst tm) CLIENT_TRACES) (PO_TR fn) = true -> po_rows fn ra ras.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h01xh12HTh23Hinh32tmh41Ah51Hh62H0h71Mh81Ph91li001lh:5lemmah;1mh<4modeh=1ni011nh>2fnh?2rah@3rashA1ti021pp;1p;2p;3p;4p;7g00G\j14Tg00HAj1ITg00H_j1CTg002lj1<Tg00_Jj1HTg00=DR0j2FTg000\j38Tg00F]j2@Tg00J>j12Tg00TBj35Tg00LPj3;Tg00B_j30Tg00N;j3GTg00K8j3:Tg00KUj46Tg00@cj43Tg00>aj29Tg00M1j2?Tg00MJj3>Tg00T^j3=Tg003Lj37Tg00@@j2BTg00`Jj3DTg002Nj7ETg00IBj3ATg00:1f0R1g00:Q37p=1g00;1R2g00O]#4#4#4#4#4#4#I#C%<2R2f2R3#H#1g00ACR4,F2R5A8241R6g00PBR7'@X35R8f3R9#235#1g00UAp4p710R:p-0\1R;f1R<#<R=g0076R>A;3<1f4R??013P?P<O1[^09R@[A091<P9P<O1[^03A;93<[RAA;?93\@AG3<1P1n2001000000120000000W9W8W4PA^9=^8;^4:P1P5P6A:241R6f5R:P?C6=027X35%2:P0P2P4f7R0#29051A824<A:24<P0f6R;C6=027[P1P2P4P<P1C3f:R=#2505g00RFRA,96X35R6f;#2R@555#1f<RB#2RC9051P6P<O1#1RD[^05RE'?A556C#1f=#29051PD[^05;>1W:A=56@f8R@O2PEP1P2P4P9P3C3REP<O2A:24E/9A#1P>19<1#1A743<[R>A74<1193<#1RE[A7493\E1B<1P<n2001000000120000000X;4X=4P>^;4^=4P1P?PAP<O3A74?AP4PAP2P4P0P1C3f@R0#2R>505P@P<P0f?REC6=027]2X<4P2P4P;PAC3%2E505A558>#1fARE#2R;9051P8P<O1#1R6[^05RD'?A558;#1fB#29051P6[^05;>1W:A=58>PBO2PDP1P2P4P@PAC3R@P<O2A824@/@7#1f9R@?D71P@PAPEP0C6=027eb1b1W2P:P1P?FEb7b5b7b6P2P4P3P<C3R:9824A:24:P=P@C6=027eW2X<4XA2P<P1O2n2001102000121100101X05O4b5AA?93eW1W6W@W?W>o"). Qed.

(* [comment removed for export] *)
Definition po_rowZ (t : list Z) (mode : nat) (ra : Z) (ras : list Z) : list Z :=
  match mode with 0%nat => t | 1%nat => t ++ ras | _ => t ++ ra :: ras end.

Lemma po_rowZ_eq : forall t mode ra ras, 0 <= ra < 2 ^ 64 -> po_row t mode (Z_to_bv 64 ra) ras = po_rowZ t mode ra ras.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h02rah13rash22HRh34modeh45mode0h51ni001nh61th71zp;1p;2p;4p;3p;6g002lj1BTg00VYj2ATg00G\j10Tg00W5j18Tg00WSj2@Tg00X0j2<Tg0076j2;Tg00HAj1:Tg00XLj29Tg00KUj43Tg00aLj42Tg003Lj31Tg004Fj26Tg00Rej17Tg00\;j34Tg008Rj35Tg00Y2j2=Tg00Z:j2>Tg002Nj6?Tg00;1R0#BR1g00ACR2P2g00\Xf1R3'Ag00O]#0R4#8%04#0#0#0#0R4#8'@,<3';R5f5R6f3R7%:4R4f2R8'9R9P3C3P6P7P8P3C2511[^11^00f0R6f4R:,61P:g00RFR;P9P3C3P:P;P8P3C2511eX25X11X00P2f7R:%77R<P9P3C3P:P<P8P3C2511\5^11^00P6f6R:=403,61P:%7;R;P9P3C3P:P;P8P3C2511eX25X11X00P0P8f9R;A5068540A5078940;511X70f8R;A5083540,611=491>86E?P;%7<R<P9P3C3P;P<P8P3C2511eX25X11X00X32P6O1n0110000020010100X52P6O1n0110000020011100W4W6o"). Qed.

Definition po_rows_top_ok (fn ra : Z) : bool :=
  forallb (fun tm => in_traces (po_rowZ (fst tm) (snd tm) ra []) CLIENT_TRACES) (PO_TR fn).

Lemma po_rows_top : forall fn ra, 0 <= ra < 2 ^ 64 -> po_rows_top_ok fn ra = true -> po_rows fn (Z_to_bv 64 ra) [].
Proof.
ltac2:(KReplay.run1 (kr_t_Po_rowkit ()) [] "p'0h02tmh11xh21Hh31li001lh41Ah51Ph62H0h72HRh83Hinh92fnh:5lemmah;4modeh<2rah=1ti011ni021pp;2p;1p;3p;4p;5p;6g00VYj2OTg00G\j12Tg00W5j1<Tg00WSj2BTg00X0j2NTg0076R0j2LTg00bIj2FTg002lj1>Tg00LPj3:Tg00B_j30Tg00N;j3@Tg00=DR1j2?Tg000\j39Tg00K8j38Tg00HAj1MTg00XLj26Tg003fj1KTg00KUj47Tg00J>j11Tg00@cj4;Tg00aLj44Tg00F]j25Tg00TBj3=Tg00M1j2ETg00MJj3DTg00T^j3GTg00`Jj3HTg00cMj5CTg002Nj6ITg00IBj3JTg003Lj3ATg00:1f0R2g00:Q3Ap=3g00;1R3g00\X/O2g00O]#2R4#<%24#2#2#2#2R4#<'B,N2'Lf2R5f1R6'F#3g00UAp4p710R7p-0\2R8%>6R9P0A:562f3R0f4R:?025P:P6O1[]1R;[A0026P0P6O1[^15A:056[R<A::05\;A@562P2n2001000000120000000W3W5W4P<^39^58^47P2%>3R7g00ACR8'?R9A9782R<A8782R;%M4R4/6:%K3R=C7g00PBR>507X09%1:P1P7P8f6R1#19092A9786A87861641P=C7=07>[P2P7P8P6P2C;f9R1#1509P<P;f:R?P=C4/5>X09R@%1?RA5=9#3f;RB#1RC9092P<P;f<RDP=C4/5>X09P6O1#3[^19RE'EP<P;PBP=C4/5>X09==9C#3%1D9092P<P;f=P=C4/5>X09P6O1#3[^19;D2W:AG9@Af7O2PEP2P7P8P0P5C;REP6O2A978EA878EP?P=C4/5>#3P7P:P0PBP=C4REA072>X37AHE>2P:P0164BP=C7P:P0PBP=P?DCEIb2b2P7P8P5P6C;R?9978A878?1641P=C7=07>eW8X;8X=7P6P2O2n2001102000121100101X19O4b61645=J0=eW2W7X<3W9o"). Qed.
