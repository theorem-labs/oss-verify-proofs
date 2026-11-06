(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Monad () := "C47Corelib4Init5Logic6eq_indc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad1MC13~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4implC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree8impl_evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5ebindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5epostC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree<impl_ret_unrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree:impl_ebindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree?impl_epost_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree;impl_ret_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5enodeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree:impl_enodeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad4mretC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad5mbindC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad4munrC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5itree00C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad4msysC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad5mloopC13~~~I47Corelib4Init9Datatypes4prod00I:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree3Exc3exc00C13~~~K47Corelib4Init5Logic2eq01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes4node00C13~~~K:9OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree3Exc3exc01C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree5itree01C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad5implMC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Nodes7at_nodeC13~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4nretC13~~~I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5ITree4respC13~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad4mgetC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad4mputC13~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad4mupdC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad:implM_bindC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad9implM_retC13~~~I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes3nat00".
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Monad.
Context {St : Type}.

Definition M (A : Type) : Type := St -> itree node (exc (A * St)).

Definition mret {A} (a : A) : M A := fun s => Ret (Ok (a, s)).
Definition mbind {A B} (m : M A) (f : A -> M B) : M B :=
  fun s => ebind (m s) (fun p => f (fst p) (snd p)).
Definition munr {A} : M A := fun _ => Ret Unr.
Definition mget : M St := fun s => Ret (Ok (s, s)).
Definition mput (s : St) : M unit := fun _ => Ret (Ok (tt, s)).
Definition mupd (f : St -> St) : M unit := fun s => Ret (Ok (tt, f s)).
Definition msys {A} (n : node) (dec : resp -> option A) : M A :=
  fun s => enode n (fun r => match dec r with Some a => Some (a, s) | None => None end).
Definition mwhen (b : bool) (m : M unit) : M unit := if b then m else mret tt.
Definition massert (b : bool) : M unit := if b then mret tt else munr.

(* [comment removed for export] *)
Fixpoint mloop {X R} (fuel : nat) (body : X -> M (X + R)) (x : X) : M R :=
  match fuel with
  | O => munr
  | S fuel' => mbind (body x) (fun s => match s with
                                        | inl x' => mloop fuel' body x'
                                        | inr r => mret r
                                        end)
  end.

(* [comment removed for export] *)
Lemma mbind_mret : forall {A B} (a : A) (f : A -> M B) s, mbind (mret a) f s = f a s.
Proof.
ltac2:(KReplay.run1 (kr_t_Monad ()) ["Monad"] "h01Ah11Bh21ah31fh41sp;1p;2p,2StR0p4p300R1p10000p4p710p8P1g000LR2p60921001R3p8P1P2p60921100R4p8P1p1001Vp4p710p8P1p10024p4p7210p8P1p1002Qp4p710p8P1p1002oR5p4p7210p8P1p1003Lp4p741110p8P1p1004Xp4p741110p8P1p1005hR6p4p7210R7p8P1P6p4p73110R6p8P1p10075p4p710p8P1p1008Bp4p741110p8P1p1009VR8p4p741110p8P1P8p4p7511110p8P1p100:hp4p741110p8P1p100<?p4p741110p8P1p100=Rp4p7210R8p8P1p100>_p4p741110p8P3P4p8p100@1p60921000R1P3p8p100A>R9p60921001R:P3p8P:P5p4p710p8P:P7p8P9p609311000R9P3p8P9P6p8p100BLp60921000R6P3p8g00CYR7p4p710P4p8p100Dhp60921000R4P3p8P4P8p8p100F5R8p60921001R4P3p8P4P:p8P8p609311000R8P3p8P8P1p8P8P:p8P8P9p8P8P6p8p200R6P1p8P6P:p8p201R:P3p8P:P9p8P2j14Tg00GCj23Tg00Gcj10TP7j21Tg00I4j22Tf1R7f2R2%42[g00INf3/30#0'1P7P2f0O2'2X40W3W2X1:X06o"). Qed.
Lemma mbind_munr : forall {A B} (f : A -> M B) s, mbind (munr (A:=A)) f s = Ret Unr.
Proof.
ltac2:(KReplay.run1 (kr_t_Monad ()) ["Monad"] "h01Ah11Bh21fh31sp;1p;2p;3p200R0p100A>R1p60921001p8P0p100BLp60921000p8p201R2g000LR3p60921001p8P2P1p609311000p8P3j16Tg00GCj25Tg00Gcj10Tg00CYj21Tg00J\j14Tg00Kmj32Tg00I4j23Tf1R3%63[p,2StR3g00INR1f2/53R3#0R4'1%439214'3W3W2X12X00o"). Qed.

(* [comment removed for export] *)
Section Machine.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

Definition implM {A} (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
  impl segs (at_node segs) (c s) (epost (fun p => Q (fst p) (snd p))) ms.

Lemma implM_ret : forall {A} (a : A) s Q ms, evt segs (Q a s) ms -> implM (mret a) s Q ms.
Proof.
ltac2:(KReplay.run1_chk (kr_t_Monad ()) ["Monad"; "Machine"] "h01Ah11Hh21Qh31ah42msh51ph61sh71xh82x0p;3p;1p;2p;4p;8p;5p,2StR0p4p300g00M<R1p609311002R2p8P2p1000Lp60921001p8P2g002oR3p4p710R4p8P2p1003Lp4p741110p8P2p10075p4p710p8p200R5g00@1R6p60921000p8P5P4p8P5P2p8P5g00<?R2p4p741110p8g00NJj38Tg00OTj17Tg00GCj20TP3j31Tg00Pcj36Tg00Q@j42TP2j83TP6j24TP1j55Tf0R1f2R6g00Q`R2p-0[^80]7p,4segsR3f1R4f3R7P6O2;81g00INP3%73f5R3/00R8P7f6R9?101A6901O2X58P3P0f4R8P7C2P4P1G3P31438P7P6P4D5eW1X42W2X60W3X05o"). Qed.

Lemma implM_unr : forall {A} s (Q : A -> St -> machine_state -> Prop) ms, implM munr s Q ms.
Proof.
ltac2:(KReplay.run1_chk (kr_t_Monad ()) ["Monad"; "Machine"] "h01Ah11Qh22msh31ph41sp;1p;2p;3p;6p;5p200R0g00BLR1p60921000p8P0g002oR2p4p710p8P0g00M<R3p609311002p8P0g008BR4p4p741110p8g00OTj16Tg00GCj25TP2j30Tg00Pcj31TP4j64TP1j12TP3j53Tp,2StR3f1R1g00Q`R4p-0[\3[g00INp,4segsR2%62f3R2/53R5f2R6f4R7f0R8703A1738O2X35P8E4P2%22P6P1P8D3eX24W1W4X00o"). Qed.

Lemma implM_bind : forall {A B} (m : M A) (f : A -> M B) s Q1 Q ms,
  implM m s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implM (f a) s' Q ms') ->
  implM (mbind m f) s Q ms.
Proof.
ltac2:(KReplay.run1_chk (kr_t_Monad ()) ["Monad"; "Machine"] "p'0h01pi001ph13ms'h21ai011ah32s'h41Ah51Bh61Hh72Hfh82Hmh91Qh:2Q1h;2a0h<1fh=1mh>2msh?1si021sp;1p;5p;2p;3p;7p;4p;<p200R0g000LR1p60921001R2p8P0g00A>R3p60921001p8P0g002oR4p4p710R5p8P0g00M<R6p609311002R7p8P0g009VR8p4p741110p8p201R9P2p8P9P3p609311000p8P9P5p8P9P7p8P9g003LR7p4p741110p8P9g0075R5p4p710p8P9P8p4p7511110p8P1j14TP6j53Tg00OTj1;Tg00GCR6j22TP4j31Tg00Pcj30Tg00Gcj18TP5j25TP7j76Tg00Q@j47TP8l<:TP3j49Tf1R3#4f2R8%48[p,2StR7f4R5g00Q`R4p-0[\7[R1f7R2f5R:f3R;P8f0R<D3f8R=f6R>P8P3P<O3f;R?f9R@P;O1P8P>P3D3[^14^37]2g00INRAp,4segsRB%;BRC12@7RD12=7REP2P:O1P2f:RF?17<RGA0F7<RHO2X0DP:PGPHO2X0DP5A1@7<A0@7<O2X0EP8P3P6PFP7P2f<R6?173A0673P<O3PAPBPC1267RE#8PFf=R5?178A0578O2P=A157<A057<O2X0E,5EP3F6[^14P<PFf?RFPFP7P8P3C7RE717A0F7EP<O3P2P;P8P3P<O4PAPBPC12F7RF#8P5f@R5P5P7P;P8C7RC717A057CO2P?A157<A057<O2X0F,5FP3F6eW6X14X37X26P3P<O2n2001100000120101102X;DM<:P=P@P=P2P>C9P:P;P8D3eW7W8X>4X91W:W?W<W=X59X40o"). Qed.

Lemma implM_mono : forall {A} (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  implM m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implM m s Q' ms.
Proof.
ltac2:(KReplay.run1_chk (kr_t_Monad ()) ["Monad"; "Machine"] "p'0h03ms'h11ai001ah21pi011ph32s'h41Ah51Hh62H0h72HQh81Qh92Q'h:2a0h;1mh<2msh=1si021sp;1p;5p;2p;3p;4p;:p200R0g000LR1p60921001p8P0g002oR2p4p710p8P0g00M<R3p609311002p8P0g00:hR4p4p741110p8P1j17TP3j53Tg00OTj16Tg00GCR3j24TP2j31Tg00Pcj30Tg00Q@j42TP4l:5Tf0R4#7p,2StR2f2R1g00Q`R5p-0[\2R6[f3R7P6[f5R6f4R8P7P1P4D3f6R9P9P1f1R:P4O3P9P7P1P:O3[^05^32]1g00INp,4segsR;%6;f7R;/42R<P9P6O1P6f8R=?124R>A0=24R?O2X2<P8P>P?O2X2<P1P:P3P=P2P;f:R=?12:A0=2:P4O3P;f;R3?121A0321P:O3[^05P4P=P1P:P4O3P;P7P1P:P4O4W6P=f=R3P3P2P1P:C2R?712A032?P4O3P=f>R?P?P2P7P1C2R3712A0?23P:O3[eX05X32X1=P:P4O2n2001101000120100102X:<M:5P;P9P6P7P1D3eW7W5X<5W9W8W=W;X40o"). Qed.

Lemma implM_sys : forall {A} n (dec : resp -> option A) s Q ms,
  evt segs (fun ms1 => at_node segs n ms1 /\
                       forall rsp a, dec rsp = Some a -> evt segs (Q a s) (nret ms1 rsp)) ms ->
  implM (msys n dec) s Q ms.
Proof.
ltac2:(KReplay.run1_chk (kr_t_Monad ()) ["Monad"; "Machine"] "p'0h01ai001ah13rsph22Hkh31Eh43ms1h52H0h61Hh72H1h81eh91si011sh:2H2h;2a'h<1oi021oh=1Ah>2H3h?3Hath@1QhA2a0hB3dechC2mshD1nhE1pi031phF1rhG2s'hH1xi041xhI2x0p;1p;3p;2p;4p;6p;9p;8p;5p200R0g0000R1p4p710p8P0g0024R2p4p710p8P0P2p4p7210p8P0g002QR3p4p710p8P0g00DhR4p60921000p8P0g002oR5p4p710p8P0g00M<R6p609311002p8P0g00>_R7p4p741110p8g00RgR8j12Tg00OTj38j1NTg00SIj2>Tg00NJj34Tg00TUR9j2:Tg00GCR:j20Tg00U0j19TP5j3<Tg00Pcj3;Tg00URR5j33Tg00Ulj27Tg00Q@j4?TP2j6BTg00I4j2ATP3l9Mj8Jj6@TP1j6ITg00VNj2FTg00Vmj4GTg00WHj6HTP7l9ETP4j3KTP6j5LTf3R6#2f2R4f1R7f0R1'733p=6f4R3P6P4P7P1C?'7p=11>719464p=517719364p=D%24?371p==1747=361p=Cg00INR2g00XWR;%24[p,2StR<g00Q`R=p-0R>[^I<^H6p,4segsR?f5R@=8?1f7RAf8RBf6RCP7O1PBP1C6P@P7PCO21>64RD54?[]0^1;':X4=;41P2P?%N?10C<R2P@P8PA10B<RE#2P@P1O1PEPBP<P1P@D110A<#9n10110400021010000XF;P6A<A<1A;A<1O2XE2P7P?A8?C1R2f9RFPAP7O1RGPFP1C6PCP7PAO2=4?D[^0B^1;':X4=10F<RHP8PFf:RI/0<RJ#2PGPJPIP<P1PAD1%9Hn10110400021010000PHP1C6PCA<I<7A;I<7O2=4?D[^0E^1;,:2X4=P7P1A8?A1PIPBP7O1PIP1C6R2PAP7PBO2RE=4?D[^0F^1;':X4=P1O1P9A8?A7P?PEP3P4C5\2^0F^1;A8?B4f;R2/0<REP8P2f<R9/0<RH#2PFP7O1PHP9P<P1PFD1%9En10110400021010000PEP1C6P?PBA<9<7A;9<7O2P@P4C5[^0J^1;':P1A8?F6f=RJP2P7O1PJP1C6P?PIP7P2O2PAP4C5[^09^1;A8?2@10J<REf>RH/0<RGP8PHf?RK/0<RL#2RMP9P7O1PLPKP<P1P9D1%9Gn10110400021010000PGP1C6P?P2A<K<7A;K<7O2PBP4C5[]0^1;P7P:PHP<PMP8PKf@RM/0<RG#2PJP4O1PGPMP<P1PJD1%9Ln10110400021010000PLP1CDP?P9A<M<7A;M<7O2PFP6C5[P1fBRL/0<RGP8PLfCRN/0<RO#2PMP@O1POPNP<P1PMD1%9Gn10110400021010000PGPLP<P7P1D13=PAPCO1fDRG#2ROPLPAO1RPPGP1CDP?fARQP7PLO2PHPBC5[^0NPPPOP8fEROfFRPfGRRP7PRP1C6PGP7POO21>Q2RS54?[]010R<RT#2RUP8PRfHRV/0<RW#2RXP7PWPVP<P1POD1%9TRYn10110400021010000PTPRP<PCP@D1RT33PGPAPCO2=4?SRS]3]2P1PV17V7PVP1C6P?POP7PPO2PLP9C5[^0RPXPWPVP<P7POC?PWPVP<PAPCD1CCP5fIR5/0<RX#2RZPXP5P<P4PPD1R[fKR\/0<R]#2R^P]P\P<PIPFD1R_737P?PVP2PIO2POPKC5[P1PXP5P<PBPAD1RX93Z[fJR[/0<R`#2RaP`P[P<P6PRC?P`P[P<PFPBD1R`CCP^P<P8fLRb/0<RcP<P1P:fMRdP<P<P1P1n2001103000120100101P5n10110200021010300X8^P]P\P<P3PVD1P_P1EBA3<VF%2cRVPbP810d<fNR_P1P:P_P<fOR:P1P7n2001103000120100101PCn10110200021010300X8VPcPbP<P@P5D1PcPbP<P2PID1P7EBA3b@2A3dC9P1A3_AJP:PHA3<dHRAP?PdPMPKO2P[PGC5[X0:A3<bJP1PAP<PKP?P_PQPMO2P\POC5X9<fQR\PMfRRAfSRJ17J7PJP1C6fPR2P7P\O21>dRRc54?[]010J<RVPVPJP<P7P2D1PVPJP<PLPQD13=P2PNPLO2=4?c]3]2X;\PA17AQPAP1C6P?P:P7P2O2PbPPC5[^0\10A<R\P\PAP<PQP:D1P\PAP<PQPMD13=P<PQfTRQ=8?1fVR\fWRbfURcP7O1PbP1C6PQP7P3O2=4?D[]0^1;':X4==4?:%2\Rb17\ORL17\1RV33PJP7P6O21>2[R[54?[^0c10\<R]P]P\P<POP4D1P]P\P<POPGD13=PJPPPOO2=4?[]3]2]6X9<A8?J1PQP7O1=3bVPJP7POO2=4?D[^0c^1;':X4==4?_Pc17cGPcP1C6P?PAP7PGO2P:P5C5[^0Q10c<RQPQPcP<PGPND1Rc;=cP7PO1AbLO2W3W2W6P2P6PdP7P1M9MW3W2PIP6PFPBGJP_P1E@b>W:PBP1E@b:W7P1O1b7P1O1b7W5P1O1W5n2002102000000101A3a1`P?PRPIPFO2PGPHC5[X<ZPXO1P11Aa`O1b5W3W2X;PP1O1PP%9PPPP1C6P?PNP7PGO2PMPIC5[^0O10P<RO%9OPOPPP<P@P3D13=PUPYP8PWP>P1g00YcR>g00Z@n10110200021000000X8Ug00Z\PTP1EIP>1FS1b5W3W2n10110200021110000P7P4O2b<b2P?PKPNP<P4P7C?RK9<N<A;N<KO2P9PCC5eW3XG<X0MP7P1O2n2001103000121100101XAEX1;CGW2W?P7P1O2n2001000000121000000W5X4=EHM9EPCAKC@3P6P4P7DLeW6XC=W@W9WBWDX=0o"). Qed.

Lemma implM_get : forall s Q ms, evt segs (Q s s) ms -> implM mget s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Monad ()) ["Monad"; "Machine"] "h01Qh12msh21ph31sh41xh52x0p;3p;1p;2p;4p;8p;5g00NJj37Tg00OTj16Tg00GCj20Tg002oj31Tg00Pcj35Tg00Q@j42Tg00<?j83Tg00M<j54Tp,2StR0g00Q`R1p-0[^50^40p,4segsR2f1R3f2R4P4O2f0R537g00INP2%621000R2f3R6A1005A5005O2X22P0P0P6P6C2P3P5G3P0g00[8P6P4P3D4eUX11W0W3o"). Qed.
Lemma implM_put : forall s s' Q ms, evt segs (Q tt s') ms -> implM (mput s') s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Monad ()) ["Monad"; "Machine"] "h01Qh12msh21ph31sh42s'h51xh62x0p;3p;1p;2p;4p;8p;5g00NJj38Tg00OTj17Tg00GCj20Tg002oj31Tg00Pcj36Tg00Q@j42Tg00<?j83Tg00\Ej14Tg00M<j55Tp,2StR0g00]RR1g00Q`R2p-0[^60]5p,4segsR3f1R4g00^2R5f2R6O2f0R738g00INP3%731010R3f3R8A1107A6107O2X23P1P0P5P8C2P4P7G3P1%48f4P6P4D5eUX12W0X40W3o"). Qed.
Lemma implM_upd : forall f s Q ms, evt segs (Q tt (f s)) ms -> implM (mupd f) s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Monad ()) ["Monad"; "Machine"] "h01xh11Qh21fh32msh41ph51sh62x0p;3p;1p;2p;4p;8p;5g00NJj38Tg00OTj17Tg00GCj20Tg002oj31Tg00Pcj36Tg00Q@j42Tg00<?j83Tg00^Rj14Tg00M<j55Tp,2StR0P0]0g00]RR1g00Q`R2p-0[^60]0p,4segsR3f1R4g00^2R5f3R6f2R7O1O2f0R838g00INP3%731010R3P6A1108A6108O2X43P1P0P5f4R5P6O1C2P4P8G3P1%45P6P7P4D5eUX32W1X50W2o"). Qed.

(* [comment removed for export] *)
Lemma implM_evt : forall {A} (c : M A) s Q P ms,
  evt segs P ms -> (forall ms', P ms' -> implM c s Q ms') -> implM c s Q ms.
Proof.
ltac2:(KReplay.run1_chk (kr_t_Monad ()) ["Monad"; "Machine"] "h01Ah11Hh21Kh31Ph41Qh51ch62msh73ms'h81ph91sp;1p;3p;5p;2p;:p200R0g000LR1p60921001p8P0g002oR2p4p710p8P0g00M<R3p609311002p8P0g004XR4p4p741110p8P0g0075R5p4p710p8P1j19Tg00NJj38TP3j50Tg00OTj11Tg00GCj27Tg00Gcj14TP2j33Tg00Pcj32TP5j25TP4l:6Tf0R4#9p,2StR5f2R2g00Q`R3p-0[R1\5[p,4segsR6f1R7;84f3R8P4O1f8R9f7R:f6R;f5R<P7D0[^73g00INP6%1617:5R6#4P;P<O1P<A3954A2954O2X86,56P8P2P7P4M:6P:P;P<f4P2D0eW2W1X63X31W4W9W5X00o"). Qed.

Lemma implM_loop_S : forall {X R} fuel (body : X -> M (X + R)) x s Q ms,
  implM (body x) s (fun r s' ms' => match r with
                                   | inl x' => implM (mloop fuel body x') s' Q ms'
                                   | inr v => evt segs (Q v s') ms'
                                   end) ms ->
  implM (mloop (S fuel) body x) s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Monad ()) ["Monad"; "Machine"] "p'0h03ms'h12s'h22H'h31ri001rh41si011sh51Hh61Qh71Rh81Xh91ah:4bodyh;4fuelh<2msh=1vi021vh>1xi031xh?2x'i042x'p;2p;1p;5p;3p;6p;:p200R0g000LR1p60921001R2p8P0g00F5R3p60921001p8P0g00M<R4p609311002R5p8P0g00__R6p609311003R7p8p201R8P2p8P8g00@1R2p60921000p8P8P3p609311000p8P8P5p8P8g00a2R5p609311001p8P8P7p8P8P6p6094111002p8g00bDR7j24TP1j13TP3j50TP4j51Tg00NJj32TP2j25TP5j68TP6l:7Tg00bcj16Tg00cBf2R6f3R5/46#3[p,2StR2f4R4g00Q`R3p-0R1[\2[f7R9f6R:'4R;P4P5O1P6P7f:R<f9R=P1P6P<f;R>P<P=f8R?f0R@D0P6f5RAf1RBD1p,4segsRCPAP@P6O2;2Bn200110000021010410102X03X12X3;P@D114?9R;P9PAP4O1P7P=P?%3=P@P<P=P?P9P@D015=@n200110100021010410100X4;P5P7P>P<P1P6P>f<RDP>P<P=P@D0P6P:PBD1P:P@P6O2=2CBn200110000021010410102X03X12X3;P6PBP@P7P=P?P7PDP>P1P6PDf=R1PDP>P<P@D0P6P9PBD1P9P@P6O2=2CBn200110000021010410102PDP7P1PD%31P5f>P1PDP>P@D0151@n200110100021010410100P6P9PBD1[^03^12P@PDP1PDP>P<P6D0PBP9P@D1P@W2X03X12X?<P@O1P9P6PBO2=2C@P1P5P6P?PBP@E8W2X03X12X==P@O1n200110100021010310100X9;M:7P9P?P9%6:PAP4D0P5P6PBD1eW5X<3W6W4X>5W:W;X78X80o"). Qed.

End Machine.
End Monad.

Arguments M St A : clear implicits.

Declare Scope mspec_scope.
Notation "x <- m ;; k" := (mbind m (fun x => k)) (at level 100, m at next level, right associativity) : mspec_scope.
Notation "m ;;; k" := (mbind m (fun _ => k)) (at level 100, right associativity) : mspec_scope.
Notation "' p <- m ;; k" := (mbind m (fun x => let 'p := x in k)) (at level 100, p pattern, m at next level, right associativity) : mspec_scope.
