(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_GresFast () := "I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions9bv_eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib6Common8PropExec:bv_eqb_neqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indI47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01c59OSSVerify5KrLib6Common8GresFast5rlookC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8GresFast9regs_updsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib6Common8GresFast>bv_eqb_true_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Common8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec:getr_otherC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indK47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7forallbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00".
Import ListNotations.
Local Open Scope bv_scope.

Section GresFast.
Context {fx : FPState}.

Fixpoint regs_upds (base : bvmap 5 word) (l : list (reg * word)) : bvmap 5 word :=
  match l with [] => base | (r, v) :: t => regupd (regs_upds base t) r v end.

Fixpoint rlook (l : list (reg * word)) (r : reg) : option word :=
  match l with [] => None | (r', v) :: t => if bv_eqb r' r then Some v else rlook t r end.

Lemma bv_eqb_true_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_GresFast ()) ["GresFast"] "p'0h01Eh11Hh21bi001bh32H0h41ah51dh61ei011eh71ni021ni031sp;1p;3p;2p;4p;6g0000j11Tg000Sj34Tg001@j30Tg001Zj35Tg002Bj12Tg002[R0j28Tg003;j47Tg004:j63Tg004Vj26Tg0055f0R1#1f1R2#1g005SR3f2R4?421g0063R530f3R6?542%16?042R2%22'8P0f4R0#1?064R4%24f5R4#1?006R2P1P1X02P1O1%22P3f6R2?440A0315X23P6g006SR6P2P4P0P1C7E3A0365P3P6P3p-0P1g0073R6g007Pn0110000020000X63g007lP5P1E3P6f8#1f7;02/61b3b1W0P1O1n200110300021010110102b5W1W2W4W7o"). Qed.

Lemma getr_upds_found : forall base l r v, bv_eqb r 0 = false -> rlook l r = Some v -> getr (regs_upds base l) r = v.
Proof.
ltac2:(KReplay.run1 (kr_t_GresFast ()) ["GresFast"] "p'0h01Eh11Hh22IHh32H0h42Hlh51bi001bh61eh71lh81rh92r'h:1vh;2H1h<1ah=4baseh>1th?2v'i011oi021pp;1p;2p;3p;6p;4p;8p;7p;:p;5g008Hj19Tg008mj1WTg009Rj1ATg0000j1BTg00:0j2VTg00:\R0j2STg00;<j1RTg00;\j2NTg00<?j3?Tg000Sj31Tg00<bR1j1GTg00=Dj25Tg00=fj1UTg001@j30Tg004:j6<j7HTg004Vj2CTg00>Hj1QTg00>hj3=Tg00?Hj2MTg00?bj2>Tg00@\j28Tg00AZj3:Tg00BUj6LTg00C2j4KTg00D5j8Jj6Dl:PTg002Bj1@Tg00DSj4ITg00EQj2;Tg00FJj2OTg00GJj5FTg00HIj4ETg00Hij5TTg005SR2f0R3g006SR430p=6f3R5f2R6f1R7'>;03p=7f4R81856/;7;03p=41;67=053p=21>561573508p=3g00IK#9R9#W#AR:%99#9#9#9#9#A#BR9'V%B:R;/S9R<#RR=g00J0R>g007lR?1N:>d5?:91:7#6P<%G9R@P3P51596RAC7P9f6RBP7P8P5D4[X7=%U9RC1597RD50@P@PCP1P9p-0RCP3g0073REg007PRFn10110100021000000X6@P?PAP3E<PEP9PBP8P5C2/C3b;W1P@%Q<RAP6PDC7P9f5RDPAP5P6D4[eP0P;P9P@P3PDP9P8D3P9f8R0P7PBPDD4[P@A=<67PB159DRAC7P9f9RGA=<56f7RHPBD4[[^7=P3P@P3P0P9PHD3P9f;RIP7PGP0D4[A1:5GP21M23f:RJ91:8=023P2f<RK91:B=023P2P@P7159BRLf=RM,>Dn0100000020000159KRN50@P9f@RO/8B?:0Hf>RPPMC2[]0P7A1:DIRQg0063RR502159IRS90@AP@P9P1P9P9P3P3PHn10110100021010000X6@PLPNP3ELA09BKA09HMP9P0P@P0POP9P3D3P9fC/8GRLfAR1P7C2[P9A:LIJP1P7C2]2X:9P@PHf?RA1590RTC7P9fBRU/80RVPOPGC2[P:PJPOP8CKA0;JOP;P1P9fD/8J?:3IPUPIC2X9;PLP1PJA?:>?R>90;1RWP;P>A1:3>#6RXP@PKP7P9PMD3P9fGPMP6PPD4[PE]2]3X8;A1:>>RY#6P@PIP>PNC7P9fFPKP>PMD4[P2PYP2PCP3PFPEn0110000020000X62RFP?P4P7E<PE1CE3RCb1W2W3PUP3POP6GJW1%@WeCIPIP3EDb0W2PPP3PBFHW1P3O1b1W4W0%6QP@P8PKPSC7P918ADRS/;MA093MX59P8P3O1A:SHB/;MPSPHPBPMA0;MHRMP;P0P@P0P7P9PAD3P9PLP6POC2[A1:I6#6P@PJP5P9P1D3PE]4]0]2^3XX8;A1:0>#6P@PHPGP9PPD3P9PVPJPAC2[A1:JJ#6P@PGPIP9POD3P2A1:KK%63X52P7PR1O:KE<A02R4P2PRPFP?P4P3E<PEPCb1b0W4W0W2W3PPP3PKPDP6P7M:PW1%@MeDFEDW4W0n0110000020101P3O1b0b5P@P;P9P5P6CE==<7PGPTC7P9PKP;P9P8P5CE==<6PJPGD4[eW2X>=X?9X9;P7P3O2n2001102000121100100X<<P5DTW3X:9X8;W7W=o"). Qed.

Lemma getr_upds_base : forall base l r, rlook l r = None -> getr (regs_upds base l) r = getr base r.
Proof.
ltac2:(KReplay.run1 (kr_t_GresFast ()) ["GresFast"] "p'0h01Eh12Hlh21Hh32IHh41bi001bh51lh61eh71rh81ah94baseh:2r'h;1th<2v'i011oi021pp;1p;2p;3p;6p;9p;5p;4g008Hj15Tg008mj1OTg009Rj1;Tg0000j1:Tg00:0j2NTg00:\R0j2LTg00;<j1KTg00<bR1j1ETg00=fj1DTg00EQj21Tg001@j30Tg00?Hj2ATg00>Hj1MTg00>hj37Tg000Sj34Tg00=Dj2=Tg00?bj2?Tg00@\j28Tg00AZj3<Tg004:j69Tg004Vj2@Tg00FJj2FTg00D5l9Gj6ITg002Bj1HTg00GJj5CTg00HIj4>Tg00Hij5BTf3R2f2R3f1R4'?f0R530p=2f4R61823/14;05p=31134=025p=Jg005SR7g006SR8705p=6g00IK#5R9#O#;R:%59#5#5#5#5#;#:R9'N%::R;/L9R<#KR=P<%E9R>P5P4%D9R?C2P9P6P4P31163D3[X5=A0>??1124R@,A9UP>%M<RAP5P?C2P9P2PAP4P@D3[eP0P;P9P>P5P2P?C2P9f6R0P4P61106D3[P>A7<34P6P?C2P9f7R@A7<23f5RA11@AD3[[^5=P5P>P5P0P?C2P9f9RBP4P@11B@D3[A4:2@P71A75f8RC94:6=075P7f:RD94:0=075P7P>P41=90REf;RF,?An0100000020000=0>?P9f>RG/80?<C@f<RH11GHRGCJRI[]0P4A4:ABRJg0063RK5071=9A=0>?P>PEP1P9p-0R1P5g007PREg0073RLn10110100021000000X6>g007lRMP?P5E9PL1@I5b2W1W0%6JP>P6PDP?C2P9f=/8ARJ/1FA095GX49P6P5O1A<J@0/1FPJP@P0PFA0;F@RJP;PCP>P@P5P?C2P9f@RGPCP411G4D3[A4:D4#6P>PBP3P?C2PL]1]0]3X7;P>P0PCP?C2P9f?R0P@PB110BD3[A4:BB#6P>PCPDP?C2P7A4:FF%65X47P4PK1F:FE9A07K8P7PKP7P1P5PEPLn0110000020000X67PMP8P5E9PL1@L5b2b0W1W0W3PHP5PAP3P4M9GW2%HJeDCEIW1W0n0110000020001P5O1b0b4P>P;P9P2P3C>=7<4P@P?C2P9PDP;P9P6P2C>=7<3PC11DCD3[eW3X;=X<9X:;P4P5O2n2001102000121100100X8<P4DBX7;W5W9o"). Qed.

(* [comment removed for export] *)
Lemma getr_upds_test : forall (t : reg -> bool) base l r,
  forallb (fun p => t (fst p)) l = true -> t r = false -> getr (regs_upds base l) r = getr base r.
Proof.
ltac2:(KReplay.run1 (kr_t_GresFast ()) ["GresFast"] "p'0h01pi001ph12Hrh22IHh31lh41Hh52Hlh61bi011bh71rh82H1h92H2h:1ah;4baseh<1eh=2r'h>1th?2tlh@2v'p;1p;2p;3p;6p;8p;5p;4g008Hj15Tg008mj1PTg009Rj1<Tg0000j1:Tg00:0j2OTg00:\R0j2LTg00;<j1GTg00JNj3CTg00EQj20Tg001@j33Tg00?Hj2NTg00>Hj1MTg00>hj37Tg00Jkj38Tg00KGj2KTg00Kej3FTg00LHR1j2ETg00@\j29Tg00AZj3;Tg004:j6=Tg004Vj2ATg00D5j8Hj6JTg002Bj1@Tg00GJj5ITg00HIj4>Tg00Hij5?Tg005SR2f2R3f1R4f0R538g0063R633p=1g006SR79325p=2f4R8f3R9/93/04;35p=4A3256p=610931045538p=B10459393p=Dg00IK#5R:#P#<R;#:R<P2[%5:#5#5#5#5#<#:R:,O;1L<:R;#GR=P;f5R>AC<:5R?O1X0;=1;5P>P3O1#2P:P>P3P910>9D4[[X3=A3266P8P4O1#2R@1083RA,N:UUP8P?O1X0;%M;RB51;P:P8PBP3PAD4\@[eP0P<P:f7R0P?O1X0;=1;5P0P8O1#2P:P0P3P>100>D4[[f8R@P?O1X0;A7;3451;P@P>O1#2P:P@A7;89f6RA10@AD4[[[^3=P5f:RBP?O1X0;=1;5PBP0O1#2P:PBP3P@10B@D4[[PBP9O1f;RCP?O1X0;RD=8;4'K#6PCP@O1#2REf<RFP>O1RGf=RHP?O1X0;=8;9RI;F4%6G%6I'EP1PHPAO1#6f>R1P?O1X0;=1;8P:19H>?;0APCPHPCDBP5f?RIP@O1#6fARGP?O1X0;=1;0P:f@/9@RJ/01P:P5PGPICDX6:P0P5P>O2f9R09;JB/01PJPBP0P1A3<1BR1P<PCfDRJP?O1X0;=1;BPJP4O1#2RBP:PJPFP310J3D4[[g0073RG^1B]2X7<fCRBP?O1X0;=1;0PBPFO1#2RFP:PBPCPH10BHD4[[P2PJPHO1%25X62P5P6P8E=A3267P2P6P2p-0P5g007PPGn0110100020000X<2g007lP7P5E=PG1AG5b4b1X1FW2PIP5P@PAGHW4%@1eDIEJW9W8P4P5O2n2001000000121000000b5W1W5P<P:P9P3C>=7;491;DP:PCP<P:P>P8C>=7;9P010C0D4\E[eW2X?=X@:X=<P4P5O2n2001100010121101101X:;P4D?X7<W3W;W>o"). Qed.
End GresFast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac gf_reify R :=
  lazymatch R with
  | regupd ?R' ?r ?v => let t := gf_reify R' in lazymatch t with (?base, ?l) => constr:((base, (r, v) :: l)) end
  | _ => constr:((R, @nil (reg * word)))
  end.

(* [comment removed for export] *)
Ltac gf_find l r :=
  lazymatch l with
  | nil => constr:(@None word)
  | (?r', ?v) :: ?t => lazymatch constr:((r', r)) with (?x, ?x) => constr:(Some v) | _ => gf_find t r end
  end.

(* [comment removed for export] *)
Ltac gres_chain :=
  match goal with
  | |- context [getr (regupd ?R0 ?r0 ?v0) _] =>
      let R := constr:(regupd R0 r0 v0) in
      tryif has_evar R then fail else
      let bl := gf_reify R in
      lazymatch bl with
      | (?base, ?l) =>
          let RR := fresh "GRES_R" in let LL := fresh "GRES_L" in
          set (RR := R); pose (LL := l);
          repeat match goal with
                 | |- context [getr RR ?r] =>
                     let f := gf_find l r in
                     lazymatch f with
                     | Some ?v => rewrite (getr_upds_found base LL r v eq_refl eq_refl : getr RR r = v)
                     | None => rewrite (getr_upds_base base LL r eq_refl : getr RR r = getr base r)
                     end
                 end;
          clear LL; subst RR
      end
  end.

(* [comment removed for export] *)
Ltac gres_chain_in T :=
  match type of T with
  | context [getr (regupd ?R0 ?r0 ?v0) _] =>
      let R := constr:(regupd R0 r0 v0) in
      tryif has_evar R then fail else
      let bl := gf_reify R in
      lazymatch bl with
      | (?base, ?l) =>
          let RR := fresh "GRES_R" in let LL := fresh "GRES_L" in
          set (RR := R) in T; pose (LL := l);
          repeat match type of T with
                 | context [getr RR ?r] =>
                     let f := gf_find l r in
                     lazymatch f with
                     | Some ?v => rewrite (getr_upds_found base LL r v eq_refl eq_refl : getr RR r = v) in T
                     | None => rewrite (getr_upds_base base LL r eq_refl : getr RR r = getr base r) in T
                     end
                 end;
          clear LL; subst RR
      end
  end.

(* [comment removed for export] *)
Ltac gf_reg_neq := let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.

(* [comment removed for export] *)
Ltac gres_loop_old := repeat first [ rewrite getr_same by gf_reg_neq | rewrite getr_other by gf_reg_neq ].
Ltac gres_loop_new := repeat first [ progress gres_chain | rewrite getr_same by gf_reg_neq | rewrite getr_other by gf_reg_neq ].
Ltac gres_loop_old_in T := repeat first [ rewrite getr_same in T by gf_reg_neq | rewrite getr_other in T by gf_reg_neq ].
Ltac gres_loop_new_in T :=
  repeat first [ progress (gres_chain_in T) | rewrite getr_same in T by gf_reg_neq | rewrite getr_other in T by gf_reg_neq ].

(* [comment removed for export] *)
Ltac gres_dual_flag := constr:(false).
Ltac gres_loop :=
  lazymatch gres_dual_flag with
  | true =>
      lazymatch goal with
      | |- ?G0 =>
          assert_succeeds (
            gres_loop_new;
            lazymatch goal with
            | |- ?Gn => assert_succeeds (cut G0; [ | gres_loop_old;
                           lazymatch goal with |- ?Go => first [ constr_eq Go Gn | fail 100 "GRES DUAL MODE: goals differ" ] end ])
            end)
      end;
      gres_loop_new
  | _ => gres_loop_new
  end.
Ltac gres_loop_in T := gres_loop_new_in T.
