(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanEmbed () := "I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib4Spec9AsanEmbed<adec_madviseC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib3Lib6Decode;dec_madviseC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00K59OSSVerify5KrLib3Lib6Decode9range_ans01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK59OSSVerify5KrLib3Lib6Decode9range_ans02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib3Lib6Decode@dec_madvise_SomeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode9range_ans00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec9AsanEmbed8aev_treeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl3aev00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aundef00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aundef_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ASHOFF : Z := 0x7fff8000.
Definition shad (a : Z) : Z := ASHOFF + Z.shiftr a 3.
(* [comment removed for export] *)
Definition shlen (L : Z) : Z := Z.shiftr L 3.

(* [comment removed for export] *)
Definition adec_mmap (atop len prot : Z) (rsp : resp) : option Z :=
  match (if prot =? 0 then dec_mmap_none atop len [] rsp else dec_mmap atop len [] rsp) with
  | Some (MmOk x) => Some x
  | _ => None
  end.
Definition adec_munmap (addr len : Z) (rsp : resp) : option Z :=
  match dec_munmap addr len rsp with Some (RgDone _) => Some 0 | _ => None end.
Definition adec_mprotect (addr len : Z) (rsp : resp) : option Z :=
  match dec_mprotect addr len rsp with Some (RgDone _) => Some 0 | _ => None end.
(* [comment removed for export] *)
Definition adec_madvise (addr len : Z) (rsp : resp) : option Z :=
  match dec_madvise addr len rsp with Some (RgDone true) => Some 0 | _ => None end.
Definition adec_raw (rsp : resp) : option Z := Some (bv_unsigned (eff_ret rsp)).

Lemma adec_madvise_Some : forall addr len rsp z, adec_madvise addr len rsp = Some z ->
  z = 0 /\ exists ci, rsp = mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] [] ci.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanEmbed ()) [] "p'0h01Hh11Eh22cih32H0h41ei001eh51zi011zh64addrh77changedi027changedh82e0h93lenh:1oi031oh;1ri041rh<3rspi051bi061xp;1p;3p;2p;4p;6p;5g0000R0j1GTg000Rj3LTg001Rj30Tg001lj32Tg002gj2ETg003Aj1DTg003cj23Tg004Ej14Tg004jj1BTg005Hj1ATg005kj2>Tg006Kj1FTg006kj21Tg007Qj1@Tg0081j1:Tg008ij49Tg009Ij37Tg009ij66Tg00:gj28Tg00;Aj2=Tg00;\j1KTg00<Wj6<Tg00=3j2CTg00=Rj1?Tg00>Mj6JTg00>jj5ITg00?jj4HTg00@ER1f0R2'3p=5g00@cR39012p=;g00AAR4%G1R5f3R6f2R7f1R83L%5230f4R9?267g00B4R:#GR;1E;2f5R<?296=0;2P0P:f7R=f6R>;2<=0;2P0P:P5P8P:P5P2%D1R?g00BoR@P5P21313RAP?n0110200020000RBn0110400021010010102P?n10110600021010400%5<RC505%;>g00CO#4#4#4RD#4#4#4#BRE#ARFg00D4'>#FRGf8RH11E3RI%BD#A#F,>F#@RD1>FFRJPFPFf:RK,1Ef9RL#:,1EC9%@JRM37PMg00DS#@RNP2E6504X2G'8'=RO]0]1P8P:A2LH=13:250;P:P5P8P?PBn0110400021010010102%5=505%;HPIPDPFPFf<R=,1Ef;RB#:,1EC9=7JMPMPNP2E6904KX2G,8G'=]0]1P2A2KLHRP%K2,3:50;%5HRH905?RQP5P?P0P1p-0P2g00EKRRg00Ehn10110300021000000RSX85g00FDRT%5LRUP2E<PR%;KPIPDPFPFf>RV,1Ef=RW#:,1EC9=7JMPMPNP2E6904=X2G,8G'=RX/C2RYb3W0W1X41P2O1P@A2BKL%?2,3:50;P@P5P8PAP?n0110200020000=05UPX]0]1P2g00F`#?RX,3:90;PA05AHP5P1P0P1P1P2P2P3n10110300021010100X45PAPUP2EJA013LA013KP1P3%;2PIPDPFPFf@,1Ef?RK#:,1EC9=7JMPMPNP2E6904VX2G,8G'=X51A0133PIPDPFPF11EK%:V,1EC9=7JMPMPNP2E6904WX2G,8G1E13PVPWP=PXP6DICHPBP2E<W0P2O1b3W0W1g00G@#?,3:90;PP5P?PSX45RSPTPUP2E<PRPYb3X0QW1n0110501020101X7@P2O1n0110401021110011102X;:P2O1A2><9%D:50;%59905?P5P?PSPTPCP2E<PR1CO2b3W0W1n10110301021110401P2P7O2b1b:W0X51W<X91X61o"). Qed.

(* [comment removed for export] *)
Definition aev_tree (atop : Z) (e : aev) : itree node (exc Z) :=
  match e with
  | AMmap a l p f => enode (NMmap a l p f) (adec_mmap atop l p)
  | AMunmap a l => enode (NMunmap a l) (adec_munmap a l)
  | AMprotect a l p => enode (NMprotect a l p) (adec_mprotect a l)     (* [comment removed for export] *)
  | AMadvise a l => enode (NMadvise a l) (adec_madvise a l)             (* [comment removed for export] *)
  | ABrk req => enode (NBrk req) adec_raw                               (* [comment removed for export] *)
  | ASetTid _ => enode NSetTid adec_raw                                 (* [comment removed for export] *)
  | AUndef _ => Ret Unr                                                 (* [comment removed for export] *)
  end.

Fixpoint aembed (atop : Z) {R} (t : AM R) : itree node (exc R) :=
  match t with
  | SRet r => Ret (Ok r)
  | SVis e k => ebind (aev_tree atop e) (fun z => aembed atop (k z))
  end.

(* [comment removed for export] *)
Lemma aembed_ret : forall atop {R} (r : R), aembed atop (SRet r) = Ret (Ok r).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanEmbed ()) [] "h01Rh14atoph21rp;1p;2p;3p100G`p4p7210R0p100HZp4p73110p8p200R1P0p8g00INj14Tg00JFj23Tg00K<j20Tg00L4j31Tg002gj22Tg00@Ef0R0g00LjR2f1R3#4R4'310309124'2W2X01W1o"). Qed.
Lemma aembed_vis : forall atop {R} e (k : Z -> AM R), aembed atop (SVis e k) = ebind (aev_tree atop e) (fun z => aembed atop (k z)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanEmbed ()) [] "h01Rh14atoph21eh31kh41zp;1p;2p;3p;5g00G`R0p4p7210R1g00M_R2p4p710R3p8p200R4P3p8P4P1p8P4g00HZR1p4p73110p8P2j16Tg00INj15Tg00JFj20Tg00NTj21TP0j34TP1j52Tg002gj23Tg00@ER1g00OPf2R0#6\1g00LjR2%50'0P2P1P0f3R0f1R2'1f4P2f0O1740X41D2'3W3W2X04W1o"). Qed.
Lemma aembed_undef : forall atop {R} w (k : Z -> AM R), aembed atop (SVis (AUndef w) k) = Ret Unr.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanEmbed ()) [] "h01Rh14atoph21kh31wp;1p;2p;3p200R0g00M_R1p4p710p8P0p100G`p4p7210p8P1j15Tg00INj14Tg00JFj20Tg00PHj11Tg00L4j33Tg002gj22Tg00@ER1g00Q@f2R2#5\1g00LjR1%42R3'0%129313'2W2W3X00W1o"). Qed.
Lemma aembed_aundef_ : forall atop {R} w (k : AM R), aembed atop (aundef_ w k) = Ret Unr.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanEmbed ()) [] "h01Rh14atoph21kh31wp;1p;2p;3p200R0g00M_R1p4p710p8P0p100R;p4p710p8P0p100G`p4p7210p8P1j15Tg00INj14Tg00JFj20Tg00PHj11Tg00L4j33Tg002gj22Tg00@Eg00Q@f1#5g00LjR1f2R2#4R3'0%129313'2W2W3X00W1o"). Qed.

(* [comment removed for export] *)
Lemma aembed_sbind_ret : forall atop {A B} (a : A) (f : A -> AM B), aembed atop (sbind (SRet a) f) = aembed atop (f a).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanEmbed ()) [] "h01Ah11Bh21ah34atoph41fp;1p;2p;3p200R0p100S5R1p4p73110p8p201R2P1p4p741110p8P2g00M_R1p4p710p8P2g00G`R3p4p7210p8P1j14Tg00INj13Tg00JFj20TP3j31Tg002gj22Tg00@Ef1R3f2R1%41[g00Lj%31'0f4f0P3O1711'2W4W2X12X00W3o"). Qed.
Lemma aembed_sbind_vis : forall atop {A B} e (k : Z -> AM A) (f : A -> AM B),
  aembed atop (sbind (SVis e k) f) = ebind (aev_tree atop e) (fun z => aembed atop (sbind (k z) f)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanEmbed ()) [] "h01Ah11Bh24atoph31eh41fh51kh61zp;1p;2p;6p;3p;5p200R0g00S5R1p4p73110p8P0g00M_R2p4p710R3p8p201R4P1p4p741110p8P4P3p8P4g00G`R3p4p7210p8P4g00HZR5p4p73110p8P2j17Tg00INj16Tg00JFj20Tg00NTj21TP1j65TP3j32TP5j53Tg002gj24Tg00@ER5g00OPR3f3R1#7R2\5P2\1g00LjR2%61'0P2P5P1f5R1f2R2'1f6f4R6P3P5P1P6P2f0O1f1E532X65D3'4W4W5W3X14X00W2o"). Qed.
