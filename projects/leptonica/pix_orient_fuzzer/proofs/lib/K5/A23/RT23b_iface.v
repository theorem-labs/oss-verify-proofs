(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_gaps_iface D_iface D_defs Pm_gaps_iface RT_fk RT_fk_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT23b_iface () := "C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53A238RT_iface9fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:mat_stableC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7call_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;RT_fk_iface:icpt_postFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9icpt_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235RT_fk7ret_stFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A238RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235RT_fk>ret_stF_ret_stC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53A236D_defs;ASTA_conseqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:cps_conseqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;RT23b_iface9strchr_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface:rt_pres_exC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00c69OSSVerify5KrLib2K53A23;RT23b_ifaceAstrchr_icontractFC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib2K53A23;RT23b_iface;STRCHR_LITSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c69OSSVerify5KrLib2K53A23;RT23b_iface8e_strchrC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00c69OSSVerify5KrLib2K53A23;RT23b_iface@strchr_icontractC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53A238RT_iface;checked_srcC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K53A238RT_iface6io_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface;checked_dstC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53A238RT_iface:rt_pres_fpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;RT23b_ifaceDsscanf_dd_icontractFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs4TP_AC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;RT23b_iface:SSCANF_FMTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;RT23b_iface=SSCANF_TOKENSC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib2K53A23;RT23b_iface8A_CANARYC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;RT23b_iface8e_sscanfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23;RT23b_ifaceCsscanf_dd_icontractC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition e_strchr : Z := 0xb1d00.

(* [comment removed for export] *)
Fixpoint strchr_of (s c : Z) (zs : list Z) : Z :=
  match zs with [] => 0 | b :: r => if b =? c then s else if b =? 0 then 0 else strchr_of (s + 1) c r end.

(* [comment removed for export] *)
Definition STRCHR_LITS : list (Z * list Z) := [(0x410c0, [43; 0]); (0x41120, [32; 10; 9; 0])].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_sscanf : Z := 0xb1d40.
Definition SSCANF_FMT : Z := 0x41140.
Definition SSCANF_FMT_BYTES : list Z := [37; 100; 46; 37; 100; 0].                                  (* [comment removed for export] *)
Definition SSCANF_TOKENS : list (list Z * (Z * Z)) := [([49; 46; 56; 0], (1, 8)); ([51; 48; 46; 49; 0], (30, 1))].   (* [comment removed for export] *)
Definition SSCANF_DEPTH : Z := 3584.
(* [comment removed for export] *)
Definition A_CANARY : Z := 0x783758.

Section RT23b.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition strchr_icontractF : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s c : Z) (zs : list Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> (bv_unsigned a1) mod 256 = c -> 0 < c ->
  In (s, zs) STRCHR_LITS -> acc asegs m s (Z.of_nat (length zs)) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strchr m)))
    (icpt_postF RT Σ PMc F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strchr_of s c zs)) lo 0 0 m
               (fun _ => True)).

Definition strchr_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s c : Z) (zs : list Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> (bv_unsigned a1) mod 256 = c -> 0 < c ->
  In (s, zs) STRCHR_LITS -> acc asegs m s (Z.of_nat (length zs)) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strchr m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strchr_of s c zs)) lo 0 0 m
               (fun _ => True)).

Lemma strchr_icontract_of_F : strchr_icontractF -> strchr_icontract.
Proof.
ltac2:(KReplay.run1 (kr_t_RT23b_iface ()) ["RT23b"] "p'0h02m'h12msh22H0h32H1h42H2h52Hch61ch71Hh82H3h93Hmsh:2v1h;3v10h<3v11h=3v12h>3v13h?3v14h@3v15hA3v16hB3v17hC3v18hD3v19hE2v2hF3v20hG3v21hH3v22hI3v23hJ3v24hK3v25hL3v26hM3v27hN3v28hO3v29hP2v3hQ3v30hR3v31hS3v32hT3v33hU3v34hV3v35hW3v36hX3v37hY3v38hZ3v39h[2v4h\3v40h]3v41h^3v42h_3v43h`3v44ha3v45hb3v46hc3v47hd3v48he3v49hf2v5hg3v50hh2v6hi2v7hj2v8hk2v9hl1xi001xp;1p;2p;3p;4p;5p;Sp;Jp;Ip;Kp;Dp;Cp;6p;Ep;8p;7g0000j1eTg000hj15Tg001Mj1<Tg001kj1=Tg002Nj1dTg0033j2WTg003_j1STg004Aj1OTg004aj1ITg005_j1GTg006[j2DTg007Aj3@j2BTg007[j21Tg008Ej1cTg008cj2bTg009Cj2XTg009_j2VTg00:?j4UTg00:_j3TTg00;6j2RTg00;Vj1QTg00<6j4PTg00<kj3NTg00=cj2MTg00>Zj5LTg00?VlSCTg00@Sj4Hj5ATg00ALlJJlKFTg00BNlIKlJ]Tg00CLlD8Tg00DER0j20Tg00D`R1j26Tg00E:lC7Tg00F5j69Tg00G2j2:Tg00H0j2?Tg00HllEYTg00Ilj4>Tg00JGj4[Tg00Jaj8\Tg00K_j8^Tg00L[j3_Tg00M\j7;Tf3R2f2R3f1R4f0R53_'Dp=2f6R6f5R7'?f4R8/:2P3g00N[R9P9P4P5F;g00O9R:'0p=3P6P7P8P2P3P4E9/05p=41?78P2P3P9P9P4P5F;p=EP8P2P3P9P9P4P5F;/0:p=aP8P2P3P9P9P4P5F;p=`105:p=Zg00OUp,2RTR;#eg00P^p-0[g00QT#5R<#5#5R=#5#5R>#5R?#<R@#=RA%d<#</WA%<>#=%<=#=#S\AR=g00R9R>%O>R<fVRB#IfWRC#GfNRD1D@75@A11@D%5?#5#c'b=@>71X961V><P>P<f8R<P6CUg00RW3Tg00SZR?f:REf9RFf7RG,R>#QCPf^RHf;RI5N;f<RJ,M?P;f`RKf=RLf]RMPFDLP?P;faR?PKg00TRRNf_ROPHPMf\RPf[RQfZRRfYRSfXRTPCPBfURUfTRVfSRWfRRXfQRYfPRZfOR[PDfMR\fLR]fKR^fJR_fIR`fHRafGRbfFRcfERdfDRefCRffBRgfARhf@Rif?Rjg00UYRkf>RlMSC'BCHRmPmP;P?PKPiPOPHPMPPPTPCPDP\P]P^P_P`PaPbPcPdP@PLPJPIC2RmPEP9P9PlP:V=RnMJJP;P?PKPOPHPMPPPTPCPDP\P]P^P_P`PaPbPcPdPmPEP9P9PlPnMIKfbRmP?PKPOPHPMPPPQPRPSPTPCPBPUPVPWPXPYPZP[PDP\P]P^P_P`PaPbPcPdPePfPgPhPiPjPlPLPJPIPEPFP<PGP6P7P8P2P3P4P5Obg00VYR6P;PmP?PKPOPHPMPPPQPRPSPTPCPBPUPVPWPXPYPZP[PDP\P]P^P_P`PaPbPcPdPePfPgPhPiPkPjMSC,BNP5DAP5W5W6P;PmP?PhPKPOPHPMPSPTP[PDP\P]P^P_P`PaPbPcP@PlPLPJC2PIP9P9PjPnP5MKFP;fcRkPmPkPmP?PKPPPQPXPYPZP[PDP\P]P^P_P`P@PhPiPjC2REPeP5P4MD8P;feRo11@mRpPlPgP5P;PoP;PoPpPgP5F3F4Rp'0X0=,6=X1NPkPmP?PKPPPQPXPYPZP[PDP\P]P^P_P`PEP5P4MC7/0pX0=,6=X1NRpP4P5fdREPkPmP?PMPPPWPXPYPZP[PDP\P]P^P_P@PgPhPiC2RqPdP5P4MD8P;ffRr11@kRsPjPfP5P;PrP;PrPsPfP5F3F4Rs'0X0=,6=X1NP5O1P1P=PEPkPmP?PMPPPWPXPYPZP[PDP\P]P^P_PqPdP5P3MD8/0sX0=PoPEPkPmPHPMPVPWPXPYPZP[PDP\P]P^P@PfPgPhC2P5P2MC7P;fgR111@ERtPiPeP5P;P1P;P1PtPeP5F3F4'0X0=,6=P5PrPoPEPkPOPHPUPVPWPXPYPZP[PDP\P]P@PePfPgC2PbP5P8MD8P;fhRt11@oRuPhPdP5P;PtP;PtPuPdP5F3F4'0P0P1PrPoPEPKPOPBPUPVPWPXPYPZP[PDP\P@PdPePfC2PaP4P7MD8P;fiRf11@rRuPgPcP4P;PfP;PfPuPcP4F3F4PfPtP1PrPmP?PTPCPBPUPVPWPXPYPZP[P@PbPcPdC2RuP5PGMC7P;fkRv11@tRwPePaP5P;PvP;PvPwPaP5F3F4'0X0=,6=P5PfPtP1PrPmP?PTPCPBPUPVPWPXPYPZP[PuP_P2PGMD8P;flR211@fRuPdP`P8P;P2P;P2PuP`P8F3F4P0P;fmR8fjRu,1@RdPcP_P7E9P;P8P;P8PdP_P7F3P8P2PvPuPrPoPPPQPRPSPTPCPBPUPVPWP@P^P_P`C2P5PIMC7P;foRU11@2RBPaP]P5P;PUP;PUPBP]P5F3F4'0X0=,6=P5P;PUPBPaP]PGE9P;fpRGP;PG11@8P\P<F3P0P;fqR01:;0fnR<,1@PDPFEEP:P0PGPUP<PuPfPKPOPHPMPPPQPRPSPTPCP@P[PDP\C2P5PjMC7P;fsRC11@GRTP]PZP51?;CRf1:;CRuPTPZP5DaF4'0X0=,6=P5PfPuPTPZPID`P=ftPCfrRIP0P8P2PkPmP?PKPOPHPMPPPQPRP@PXPYPZC2P5PgMC7P;fvRg11@CR8P[PWP5P;PgP;PgP8PWP5F3F4'0X0=PLPCPIP0PGP2PvPmP?PKPOPHPMPPPQPRPSP@PYPZP[C2R8PLPhMC7P;fuRg11@IRTPDPXPLE9RuP;Pg1:;gPTPXPLEERT#ZRg'0PCPIP0PGP2PvPmP?PKPOPHPMPPPQPRPSP8PVPLPhPFMEYPuPgP7PTP:P4P5C>C>C>C[X8:W4P4P5O2n2001000000121000000W4W3P4P5O2n2001000000121000000W3W2P4P5O2n2001000000121000000W2Xl=P4P5O2n2001000000121100000PEPkPmP?PMPPPWPXPYPZP[PDP\P]P^P_PqP5P3MC7/0sX0=,6=eW9X1NG\P;PkPmPpP4DAeP;PkPmP?PKPOPHPRPSPZP[PDP\P]P^P_P`PaPbP@PjPlPLC2PJP9P9PiPnP4MJ]eW5X66G^WgWeWdWcWbWaW`W_W^W]X\>WZXY>WXWWWVWUXTAXSAXRAXQAXOAXNAXMAXLAXKAXJAXIAXHAXGAXFAXDAXCAXBAXAAX@AX?AX>AX=AX<AX;AXkAXjAXiAXhAXfAX[AWPWEW:g00WNeW7o"). Qed.

(* [comment removed for export] *)
Definition sscanf_dd_icontractF : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s p1 p2 : Z) (tok : list Z) (extra : list byte) (d1 d2 : Z) (j1 j2 : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 SSCANF_FMT -> a2 = Z_to_bv 64 p1 -> a3 = Z_to_bv 64 p2 ->
  In (tok, (d1, d2)) SSCANF_TOKENS -> bytes_at asegs m s (map (Z_to_bv 8) tok ++ extra) -> s mod 16 = 1 ->
  Z.of_nat (length tok) + Z.of_nat (length extra) = 7 ->
  checked_src RT Σ m sp lo s (Z.of_nat (length tok)) -> s + 7 <= lo ->   (* [comment removed for export] *)
  acc asegs m SSCANF_FMT 6 -> io_ssp m ->
  checked_dst RT Σ m sp p1 4 -> checked_dst RT Σ m sp p2 4 -> p1 mod 8 = 0 -> p2 mod 8 = 0 ->
  rw_cells asegs m p1 [CB 4 j1] -> rw_cells asegs m p2 [CB 4 j2] ->
  (p1 + 4 <= p2 \/ p2 + 4 <= p1) -> p1 + 4 <= lo -> p2 + 4 <= lo ->
  (s + 7 <= p1 \/ p1 + 4 <= s) -> (s + 7 <= p2 \/ p2 + 4 <= s) ->
  (p1 + 4 <= A_CANARY \/ A_CANARY + 8 <= p1) -> (p2 + 4 <= A_CANARY \/ A_CANARY + 8 <= p2) ->   (* [comment removed for export] *)
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_sscanf m)))
    (ASTA RT Σ PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 2) F m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m'
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(p1, p1 + 4); (p2, p2 + 4)] m m'
        /\ rw_cells asegs m' p1 [C4 (Z_to_bv 64 d1)] /\ rw_cells asegs m' p2 [C4 (Z_to_bv 64 d2)])).

Definition sscanf_dd_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s p1 p2 : Z) (tok : list Z) (extra : list byte) (d1 d2 : Z) (j1 j2 : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 SSCANF_FMT -> a2 = Z_to_bv 64 p1 -> a3 = Z_to_bv 64 p2 ->
  In (tok, (d1, d2)) SSCANF_TOKENS -> bytes_at asegs m s (map (Z_to_bv 8) tok ++ extra) -> s mod 16 = 1 ->
  Z.of_nat (length tok) + Z.of_nat (length extra) = 7 ->
  checked_src RT Σ m sp lo s (Z.of_nat (length tok)) -> s + 7 <= lo ->   (* [comment removed for export] *)
  acc asegs m SSCANF_FMT 6 -> io_ssp m ->
  checked_dst RT Σ m sp p1 4 -> checked_dst RT Σ m sp p2 4 -> p1 mod 8 = 0 -> p2 mod 8 = 0 ->
  rw_cells asegs m p1 [CB 4 j1] -> rw_cells asegs m p2 [CB 4 j2] ->
  (p1 + 4 <= p2 \/ p2 + 4 <= p1) -> p1 + 4 <= lo -> p2 + 4 <= lo ->
  (s + 7 <= p1 \/ p1 + 4 <= s) -> (s + 7 <= p2 \/ p2 + 4 <= s) ->
  (p1 + 4 <= A_CANARY \/ A_CANARY + 8 <= p1) -> (p2 + 4 <= A_CANARY \/ A_CANARY + 8 <= p2) ->   (* [comment removed for export] *)
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_sscanf m)))
    (ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 2) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m'
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(p1, p1 + 4); (p2, p2 + 4)] m m'
        /\ rw_cells asegs m' p1 [C4 (Z_to_bv 64 d1)] /\ rw_cells asegs m' p2 [C4 (Z_to_bv 64 d2)])).

Lemma sscanf_dd_icontract_of_F : sscanf_dd_icontractF -> sscanf_dd_icontract.
Proof.
ltac2:(KReplay.run1 (kr_t_RT23b_iface ()) ["RT23b"] "p'0h02m'h12msh22H0h33H32h43H33h53H34h62Hch71ch81Fh91Hh:2H1h;3H10h<3H11h=3H12h>3H13h?3H14h@3H15hA3H16hB3H17hC3H18hD3H19hE2H2hF3H20hG3H21hH3H22hI3H23hJ3H24hK3H25hL3H26hM3H27hN3H28hO3H29hP2H3hQ3H30hR3H31hS3H35hT2H4hU2H5hV2H6hW2H7hX2H8hY2H9hZ3Hmsh[3PMch\2a0h]2a1h^2a2h_2a3h`2a4ha2a5hb2a6hc2a7hd2d1he2d2hf5extrahg2fchh2gphi2j1hj2j2hk2lohl1mhm2p1hn2p2ho2rahp1shq2s0hr2s1hs3s10ht3s11hu2s2hv2s3hw2s4hx2s5hy2s6hz2s7h{2s8h|2s9h}2sph~2t0i002t1i012t2i022t3i032t4i042t5i052t6i063toki072tpi081xi092Σp%0p;1p;2p;3p;4p;7p;6p;5p;Sp;Dp;Cp;Ep;8g0000j1wTg000hj1ETg001Mj1HTg001kj1OTg002Nj1UTg0033j2tTg003_j1oTg004Aj1]Tg004aj1hTg005_j1eTg006[j2Bj1sTg007Aj3Dj2^Tg009_j2WTg00:?j4NTg00:_j3uTg00XVj4qTg00Y2j3pTg00YOj4nTg008Ej1CTg008cj2\Tg00;6j2PTg00;Vj1TTg00ZGj29Tg00Zdj7gTg00[dj2:Tg00<6j4fTg00\@j1dTg00];j6YTg00^;j1JTg00^Zj2cTg00_Rj1XTg00`2j2ITg00<kj3aTg00=cj2`Tg00>Zj5_Tg00?VlSVTg00@Sj4Sj5RTg00CLlD?Tg007[j21Tg00G2j22Tg00DER0j20Tg00D`S00j28Tg00E:lC>Tg00`Lj3=Tg00F5j6FTg00H0j2QTg00`lj6MTg00HllElTg00Ilj4KTg00JGj4kTg00Jaj8jTg00K_j8iTg00akj4LTg00bdj1ZTg00R9R1P1f1R2f0R3CNp=vg00c\R4?=23p=bg00SZR5f2R6P2P3CLp=6P1P1P61923CNp=3f4R7f3R8A=6233=p=;P5P7P81B62#Z==43CLp=<1B62#Z==43p=4P5P6P2P3CL,08p=rf7R9f6R:'Qf5R;P7P8P6P2EM/03p=5P:P;P7P8P6P2EF/03p=GP:P;P7P8P6P2EF/03,09p=@P5P8P6P2CL/03p=7P1P1P81962CN==73p=A1Q:;P7P8P6P2P3EMp=[P:P;P7P8P6P2EM/03p=mg00dTp,2RTR<#wg00P^p-0[g00QTR=#ER>#ER?#ER@#ERA#ERB#E#HRC#ORD%U>#H/tD%HB#O%H@RB#ORE#o\DRF%]1RG%]ERHf\RI#hf]RJ#efZRKg00e`,BC5DDfURLf<RM,BC5DDg00fWRN,BC9DDLf=RO,BC9DDLS01Q011W11RP,WGPGPPPOf;RGf:S02'vCNg00gY3uP5fBRQfARRP1PE%sBf>S03Cq=pEOCn%CA,\Q%C=5D1f@S04,P1#Tf?RA,PE#T'9%U=R=#U#CRE5D1P<fhRBfERSfeRTPGfDS051P1R#TFg19SE/:MP5fGRUPN%E=#CCffHS06#dP<flR=fIRNfiRVPU%C?R?EYP<fmRWfJS07fjRXPUP?EY%C@R@,\Ng00N[5D1S08Q08fMRYfKRZg00h^#J#J#J#J/cS%X4R4'bR[36fNR\?6Z[19Y?fLR[':19[?/:Y'I19\?R]fFS09':1:]UfQR]/9EfPR^':19^?R_/:]'IfRR`/9E/:^1:_`'I19`?g00i=R_':19_@/:`'IS0:Q0:fyR_fVR@5a<fWRE,`5P<f{RafXRbfxRcP\D_P5P<f|R5Pag00TRRdfzReP_PcfwRffvRgfuRhftRifsRjfrRkfqRlfpRmfoRnfnRoPWP=fkRpPXPVPBfgRqffRrPTfdRsfcRtfbRufaRvf`Rwf_Rxf^RyPJPIf[RzPKg00j=S0;fYR{MSV'^CSR|P|P<P5PaP5PaPeP_PhPiPpPXPVPBPqPrPTPsPtPu%C>,BCR>PJP3P2MD?P<f~R|11CaR}P]PzP3P<P|12<|P}PPA3{{?S0<PPA3bb?%XPR}D;PzP3P3P{PCPLP4D<S0=P3PbfTS0>=4C4CrG5FGR~'0X0F,8FX1dCSP<P5PaP5PaPeP_PhPiPpPXPVPBPqPrPTPsPtPuP>P3P2MC>/0~X0F,8FX1dCSf}R~P5PaPeP_PcPfPgPhPiPjPkPlPmPnPoPWP=PpPXPVPBPqPrPTPsPtPuPvPwPxPyPJPIPzPKP{PbPEP@PLQ0>fSS0?P`P]P^fOP\PYP[PZQ07PNQ06PUQ09PSQ05fCRUPQPRQ04PAQ03POPMPGQ02f9RQf8RNP9P:P;P7P8P6P2P3O}g00VYR:P<P~P5PaPeP_PcPfPgPhPiPjPkPlPmPnPoPWP=PpPXPVPBPqPrPTPsPtPuPvPwPxPyPJPIPzQ0;PKMSV,^dP3DRP3W6W7P<P~P5P~P5PaPePgPhP=PpPXPVPBPqPrPTPsPtP>PyP3P2MD?P<p+01@RZ11C5R[P`PIP3P<PZ12<ZP[PPA3KK?R[PPQ0<P}D;PIP3P3PKPCP@P4D<R`Q0='0G5G@X0F,8FX1dP3DRP<P|P~P|P~P5PaPfPgPWP=PpPXPVPBPqPrPTPsP>PxP3P2MD?P<p+01ARY11C~R\Q0?PJP3P<PY12<YP\PPA3zz?R\PPP[P}D;PJP3P3PzPCPEP4D<R[/0`G5FGR`'0X0F,8FX1dP|P~P5PaPfPgPWP=PpPXPVPBPqPrPTPsP>P3P2MC>/0`X0F,8FX1dS0?P2P3PZP|P~P5PcPfPoPWP=PpPXPVPBPqPrPTP>PwP3P2MD?P<p+01BR`11C|R^Q0>PyP3P<P`12<`P^PPA3II?R^PPP\P}D;PyP3P3PIPCPbP4D<Rb/0[G5FGR['0X0F,8FX1dP3O1Q00PFPZP|P~P5PcPfPoPWP=PpPXPVPBPqPrPTP>PwP3P6MD?/0[X0FPYPZP|P~P_PcPnPoPWP=PpPXPVPBPqPrP>P3P8MC>P<p+01CR\11CZR]PLPxP3P<P\12<\P]PPA3JJ?R]PPP^P}D;PxP3P3PJPCP{P4D<R^/0bG5G@X0F,8FP3P`PYPZP|PeP_PmPnPoPWP=PpPXPVPBPqP>PuP3P7MD?P<p+01DRb11CYRLP@PwP3P<Pb12<bPLPPA3yy?RLPPP]P}D;PwP3P3PyA4CK4R]P^C7G5G@P0P\P`PYPZPaPePlPmPnPoPWP=PpPXPVPBP>PtP2P;MD?P<p+01ER^11C`R@PEPvP2P<P^12<^P@PPPxPxP?A=PL}DAPvP2P2PxA4Cz4A62y]C7G5FGP^PbP\P`P~P5PjPkPlPmPnPoPWP=PpPXP>P3P9MC>P<p+01GR]11CbRLP{PtP3P<P]12<]PLPPA3vv?RLPPA3ww?P}D;PtP3P3PvA4CJ4R{P3PwPCPIP4D<C7G5G@X0F,8FP3P^PbP\P`P~P5PjPkPlPmPnPoPWP=PpPXP>PTP8P9MD?P<p+01HR811C^RbPKPsP7P<P812<8PbPPA3uu?RbPPPLP}D;PsP7P7PuA4Cy4RyA67v{C7G5FGP0P<p+01IR{p+01FR7,1CRLPzPTP;EFP<P{12<{PLPPPtPtP?A=Pb}DAPTP;P;PtA4Cx4A6;uyC7G5P{P8P]P7P`PYPfPgPhPiPjPkPlPmPnPoP>P3PGMC>P<p+01KR]11C8R8PJPqP3P<P]12<]P8PPA3TT?RyPPA3ss?P}D;PqP3P3PTA4Cv4RxP3PsPCPwP4D<C7G5G@X0F,8FP3P<P]P8PJPqP9EFP<p+01LR912<911C{PPA3rr?RJPPPyP}D;PBPNPNPrA4Cu4RuA6NTxC7G5P0P<p+01MRx12<xp+01JRN,1CPPPqPqP?A=PJ}DAPVPQF[PQPqA4Ct4A6QruC7PxP9P]PNP7P^PaPeP_PcPfPgPhPiPjPkP>P3PAMC>P<p+01ORi11C9RhPvPpP31Q<iRv12<iR^PhPPPVPVP?PPPBPBP?P}DADAR7PpP3P3PVA4CT4RuP3PBPCPsP4D<C7FmG@X0F,8FP3PvP^PhP7PpPGEMPMPXA4Cr4RGA6MVuC7P0POPpPCPqP4D<A6OXGp+01QRGp+01PR0Pip+01NPNP{PZP|P~P5PaPeP_PcPfPgP>P3PUMC>P<p+01SRU11C0RgPTPnP3P<PU12<UPgPPPWPWP?PPP=P=P?P}DADAPnP3P3PWA4CV4RgP3P=PCPBP4D<C7G5G@X0F,8FP3A6AWgQ04?6WgPFp+01TPUp+01RRgPGPxP9P\P`PYPZP|P~P5PaPeP_P>P3Q09MC>P<p+01VR\11CURxPBPkP3P<P\12<\PxPPPmPmP?A3nn?Rx==P}DAPkP3P3PmA4C=4A4Cp4Rm963nC7G5G@X0FPRPUPgPGP0P9P]P`PYPZP|P~P5PaPeP_PcP>PRPSMC>P<p+01URk11CgR\PqPlPREFRAP<Pk12<kP\PPPxPPA3oo?P}D;PlPRF[RlA6RnmRmPRPoPCPXP4D<R4'0RC'0Rn'0PUPgPGP0P9P]P`PYPZP|P~P5PaPeP_PcP>PjPRPSPOMElPAPnPQPlPCP;PmP4P2P3CKCKCKCKCkWSW5P2P3O2n2001000000121000000W5W4P2P3O2n2001000000121000000W4W3P2P3O2n2001000000121000000W3W2P2P3O2n2001000000121000000W2Z08FP2P3O2n2001000000121108000PZP|P~P5PcPfPoPWP=PpPXPVPBPqPrPTP>P3P6MC>/0[X0F,8FeWZX1dGjP<P|P~Q0?P2DRR2eP2eW6X7:GiWRWQWOWNWMWLWKWJWIWHWGWFWDWCWBWAW@W?W>W=W<W;WYWXWWWVWUWTWPWEW:Xk1XjHXiHXe1Xd1WfY06Xn1Xm1Xp1WlWgW8Z05DZ04DZ03DZ02DXtDXsDX|DX{DXzDXyDXxDXwDXvDXuDXcDXbDXaDX`DX_DX^DX]DX\DXrDXqDZ01DZ00DX~DZ07DXhDX}DWoW[Y09g00k=eW9o"). Qed.

End RT23b.
