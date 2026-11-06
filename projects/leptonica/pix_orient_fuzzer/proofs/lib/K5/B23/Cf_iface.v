(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface D_iface D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Cf_iface () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53B23:Lept_iface9pix_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I69OSSVerify5KrLib2K53B23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53B23:Lept_iface6p_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface6p_cmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface5c_arrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC69OSSVerify5KrLib2K53B23:Lept_iface5chunkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface:pix_hdr_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53B23:Lept_iface8cmap_objC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or02C47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6or_indK47Corelib4Init5Logic3and01c69OSSVerify5KrLib2K53B238Cf_iface<pix_cells_rcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238Cf_iface>pix_cells_rc_1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rc69OSSVerify5KrLib2K53B238Cf_iface:pix_obj_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface7pix_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface5rsizeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib2K53B23:Lept_iface5cmapv00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_cf_fuzz : Z := 0xf9fb8.            (* [comment removed for export] *)
Definition e_l_dnaaCreate : Z := 0xf111c.
Definition e_l_dnaaDestroy : Z := 0xf1280.
Definition e_numaaCreate : Z := 0xf15e8.
Definition e_numaaDestroy : Z := 0xf174c.
Definition e_pixaCreate : Z := 0x108394.
Definition e_pixaDestroy : Z := 0x108588.
Definition e_boxCreate : Z := 0xf218c.
Definition e_boxaCreate : Z := 0x109ee4.
Definition e_boxaDestroy : Z := 0x10a07c.
Definition e_boxaAddBox : Z := 0xf2960.
Definition e_pixClone : Z := 0x110994.
Definition e_colorfillCreate : Z := 0xf71cc.
Definition e_colorfillDestroy : Z := 0xf7754.

(* [comment removed for export] *)
Definition RA_CF_CREATE : Z := 0xf0a94.         (* [comment removed for export] *)
Definition RA_CF_DESTROY : Z := 0xf0aa0.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CF_TRACES : list (list Z) :=
  [ [0xf21f8]; [0x109f10]; [0x109f94]; [0xf1630]; [0xf1644]; [0xf1164]; [0xf1178]; [0x108444];
    [0x109f10; RA_CF_CREATE; RA_TOP]; [0x1083d8; RA_CF_CREATE; RA_TOP]; [0xf74e0; RA_CF_CREATE; RA_TOP];
    [0x10a1fc]; [0x10a300]; [0x10a308]; [0x108718]; [0x108728]; [0xf1978]; [0xf1980]; [0xf14b0]; [0xf14b8]; [0xf77ec] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pix_cells_rc (v : pixv) (rc : Z) : list cell :=
  [C4 (Z_to_bv 64 (p_w v)); C4 (Z_to_bv 64 (p_h v)); C4 (Z_to_bv 64 (p_d v)); C4 (Z_to_bv 64 (p_spp v)); C4 (Z_to_bv 64 (p_wpl v));
   C4 (Z_to_bv 64 rc); C4 (Z_to_bv 64 (p_xres v)); C4 (Z_to_bv 64 (p_yres v)); C4 (Z_to_bv 64 (p_inf v)); C4 (Z_to_bv 64 (p_spec v));
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (p_cmap v)); C8 (Z_to_bv 64 (p_data v))].
Lemma pix_cells_rc_1 : forall v, pix_cells_rc v 1 = pix_cells v.
Proof.
ltac2:(KReplay.run1 (kr_t_Cf_iface ()) [] "h01vp;1p;2p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cp4p710p8P0p1001DR1p4p710p8P0P1p4p7210p8g001aj12Tg002Aj11Tg003Aj20Tg003[g004X#2f0#1'0W0o"). Qed.
Definition pix_obj_rc (live : list (Z * Z)) (m : mem) (pix : Z) (v : pixv) (cv : cmapv) (rc : Z) : Prop :=
  rw_cells asegs m pix (pix_cells_rc v rc) /\ chunk live pix 64 /\ pix_hdr_ok v
  /\ (p_data v = 0 \/ (chunk live (p_data v) (rsize v) /\ p_data v <> pix))
  /\ (p_cmap v = 0 \/ (cmap_obj live m (p_cmap v) cv /\ p_cmap v <> pix /\ c_arr cv <> pix
                        /\ p_cmap v <> p_data v /\ c_arr cv <> p_data v)).
Lemma pix_obj_rc_1 : forall live m pix v cv, pix_obj_rc live m pix v cv 1 <-> pix_obj live m pix v cv.
Proof.
ltac2:(KReplay.run1 (kr_t_Cf_iface ()) [] "h02H7h12H8h22H2h32H3h43H10h52H6h62H9h72H4h82H5h91Hh:2H1h;2H0h<2cvh=1lh>4liveh?1mh@3pixhA1vp%0p;2p;1p;3p;4p;5p;6g005Pj2hTg001aj1XTg0060j1ETg006Uj1STg0073j1WTg007Vj1dTg002Aj1NTg0088j1UTg008Vj12Tg009Sj14Tg00:Pj13Tg00;Lj20Tg00;gj2VTg00<@j3=Tg00=<j1DTg00>=j26Tg00>Wj4ATg00?Vj3ITg00@0j11Tg00@Ij2fTg00@hj3JTg00ABj58Tg00A_j6QTg00B;j4GTg00BVj2bTg00CWj1aTg00DZj6_Tg00E8j6^Tg00F7j5`Tg00G5j1OTg00H1j35Tg00HKj4KTf4R0f3R1f2R2#O3=g00IDR3f1R4f0R535#1'0p=:f5R6=530#1A5312#1A5345#1'0'0p=9f7R7g00IbR8553f6R9P6P0P1CAA5324#1/05'0'6p=?A5328/64/05p=@A=012%D4/05'0p=Bg00J@R:P1P2P4CK/05p=cP:P2P4%N5CKp=FA5358p=7%D11624/05'0p=MP:P9P6P0CKA=124/05'0p=]P:P1P2%N4CK/05p=CA=124/05p=\A5348/65p=[A5345p=<P6P0P1P2CA%14/05'0p=T1612A5348/65'0p=Z%O59=24p=LA5345#1p=>%O49=12/05p=YA5312#1A5345#1'0p=HA5301#1A5324#1/05'0p=RP9P6P0P1P2P4P5CGCGp=;A5368P0P1P2P4CA/05'6p=gP0P1P2P4CA/05p=eA5324#1/05p=P1h33#Xg00K8R8#E#E#ER:#E#E#ER;#S#W%S:#W#d[g003[g00K]g004X#XR:%N4R<P0P1P5P6P1%U;R;P2%22R=P6P=P2P=P1D:%42R>P6P0P>P4P>P1%34R?P1P>P=P?P=E9G?3@DBR=CcAF012R?/0=R>'VX=:P1P2P<P0P2P;P4%24R<#7P0P<P4P<P2D:%44R:P0P1P:P5P:P2%35R@P2P:P<P@P<E9G?CMF]R<P>[R@P@P?P=P>P9P0P;P1%21R>P9P>P1P>P0D:%41R=P9P6P=P2P=P0%32R@P0P=P>P@P>E9G?3@DBA=76;R>P0%20R@#7P7P@P0P@P6D:%40R=P7P9P=P1P=P6%31R:P6P=P@P:P@E9G?CMR@P9P6P010>@CCP6%26R@#7f8R:P@P6P@P9D:%46R=P:P7P=P0P=P9%30RAP9P=P@PAP@E9G?CM%D9R@%29RAf9R=PAP9PAP7D:%49RBP=P:PBP6PBP7%36RCP7PBPAPCPAE9G?3@RAP:P7P9P=P7P;10@AC\CC%27RAf:RCPAP7PAP:D:%47RBPCP=PBP9PBP:%39RDP:PBPAPDPAE9G?3@%2:RAf;RDPAP:PAP=D:'[RB%4:REPDPCPEP7PEP=%37RFP=PEPAPFPAE9G?RAPCP=P:PDP=P;P:10BADBCC%4=RAf<RFPDPAP:PAPC%3:R:PCPA%2=RAP:PAE9G?%2CRA#7R:f=REPAPCPAPDD:RGPFPDPCPEPDP;PCP:PG%4CRHPEPFPHP=1<HD%3=RIPDPHPAPIPAE9ETCZDBCC%4DRA#7RIf>RHPEPAPC1<AF%3CRJPFPA%2DRAPJPAE9ETRJPEPFPDPHPFP;PDALHADRK1>AFS00'016IJ5@ADBCCS01AFHEFRAf?RL?=E;RM%DFRN%2FRO#7RPPLPOPF1>OERQCYRR'6RS%4FRT#7RUPLPHPTPDCARVPTPE%3DRWPEPTPOPWPOCHDRRO'0RW'6RT'0RX'0RY'0RZP=PMPYP7PNPXP6PSPTAIPR4AIUW5F;F;X2IPVPO10AZ%4ERZPH%3FRAPHPZ%2EROPAPOCHDRS02%4HRA/>LRI%3ERWPLPA%2HRUPWPUE9RWf@RR?FLHS03fARP?=L;S04%DHS05%7URTALPUHS061<ULRU#1RS'0R6'6S07%7ARXPPPRPAPECARA10IWS08'0RW'6S09'0S0:'0S0;'0S0<'0S0=%3HRNPR%4LRY%2LRMPNPME9RM%3LRN/>PR[%4RR\%2RR]PNP]CHRNfBR^PPPRfCR_PPP;PRP_P]PRP]PPD:P\P_P^P\PL1>\PR\10[NS0>'0Eg5@]DBCCS0?%4P%2PR]%3RRNP]CHR]%4^R`%2^Ra'>Rb%3PRc/>aRdfDReP_P^fERfP_P;P^PfPaP^PaP_D:P`PfPeP`PPP`P_1>c_Rc10bdS0@'0G?5@aDBCCS0A%3^%2_Ra'>RdfFR`?FfeRgfGRh?=f;S0B%DeRi%2eRj#7RkPhPjPePjPfD:Rl'6Rm%4eRn#7RoPhP`PnP_CARp1<nfRq#1Rr%3_Rs/<fRt#1Ru1<njRn#1Rv1<sjRs#1Rj'0Rw'0Rx'0Ry'0Rz'6R{'0R|'0R}'0R~PPQ0BP}PLPiP|PEPmP{AIkl=PpPyP7PrPxP9P5O1R9g00L[Rx1fx5Ryb6X0qPrePuPwP0P5O1RwPxPyb6X0tPuePvPjP2P5O1RuPxPyb6X0nPveP4P5O1RnPxPyb6X0sPjeF;F;9JozF;F;W1X5bP5D8W0X8[P5D8W5X2IP5D8W8X7VP5D8X2JP4EQX3:PKQ00Q01%7ZR:PRPLPZPFQ02DeRFPLPHPEPRPHP;PEPRPOPEPOPHD:16:F5@ODBCCQ03Q0<PDQ04Q0;P=Q05Q0:P7Q07Q09Q06PSP2PuPxPyb5X7UPSeCG9JT6AIXW5F;F;X3:PAQ08Q0=APYRMP\Q0>Q0?APN^]PcQ0@Q0A%4_?PadPvPj10g~%3e%2f'>fHRe?Fh`fIR~?=h;R;%D`Rg%2`Rj#7RdAL~j`Ra1<jhR]#1RN'0R^'6RM%4`R`#7RYP~PeP`PfCARe1<`hR~#1RR%3fRf/<hRh#1R:1<`jR`#1RW1<fjRf#1Rj'0RX'0R6'0RT'0RS'6RU'0R='0RD'0P_P;PDPPPgP=PLPMPUPaPNPCPCP5O1PxPyb4X1]PNeCG9Jd^PePTP7PRP6P9PxPyb4X1~PReP:PXPwPxPyb4X1hP:ePWPjPuPxPyb4X1`PWePnPxPyb4X1fPjeF;F;9JYSF;F;W6X0vP5D8W1X5cP5D8W0X3\P5D8W5X7AP5D8X3FP1EQX8QX2KP5D8X3GP4EQW7X2BP5D8W3X:@P5D8W2X9>P5D8W:X;?P5D8X9<R<P<CG%U8R8,b4%a4E_P0P1P2P4P5P8E^P0P1P2P4P5D`'VeW<WAX@3W?W>o"). Qed.

(* [comment removed for export] *)
Definition box_cells (x y w h : Z) : list cell :=
  [C4 (Z_to_bv 64 x); C4 (Z_to_bv 64 y); C4 (Z_to_bv 64 w); C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 1)].
Definition box_obj (live : list (Z * Z)) (m : mem) (b x y w h : Z) : Prop :=
  rw_cells asegs m b (box_cells x y w h) /\ chunk live b 20.

(* [comment removed for export] *)
Definition boxa_cells (n nalloc arr : Z) (pad : list byte) : list cell :=
  [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 nalloc); C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 arr)].
(* [comment removed for export] *)
Definition boxa_empty (live : list (Z * Z)) (m : mem) (ba nalloc arr : Z) : Prop :=
  (exists pad, rw_cells asegs m ba (boxa_cells 0 nalloc arr pad)) /\ chunk live ba 24 /\ chunk live arr (8 * nalloc)
  /\ 1 <= nalloc <= 20 /\ arr <> ba.
(* [comment removed for export] *)
Definition boxa_new (live : list (Z * Z)) (m : mem) (ba nalloc arr : Z) : Prop :=
  boxa_empty live m ba nalloc arr
  /\ rw_cells asegs m arr [CB (Z.to_nat (nalloc * 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (nalloc * 8)))].
(* [comment removed for export] *)
Definition boxa_one (live : list (Z * Z)) (m : mem) (ba arr b x y w h : Z) : Prop :=
  (exists pad, rw_cells asegs m ba (boxa_cells 1 1 arr pad)) /\ chunk live ba 24 /\ chunk live arr 8
  /\ rw_cells asegs m arr [C8 (Z_to_bv 64 b)] /\ box_obj live m b x y w h /\ arr <> ba /\ b <> ba /\ b <> arr.

(* [comment removed for export] *)
Definition parr16_cells (nalloc arr : Z) : list cell := [C4 (Z_to_bv 64 nalloc); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 arr)].
Definition parr16_obj (live : list (Z * Z)) (m : mem) (o nalloc arr : Z) : Prop :=
  rw_cells asegs m o (parr16_cells nalloc arr) /\ chunk live o 16 /\ chunk live arr (8 * nalloc) /\ 1 <= nalloc <= 50 /\ arr <> o.

(* [comment removed for export] *)
Definition pixa_cells (nalloc parr ba : Z) (pad : list byte) : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 nalloc); C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 parr); C8 (Z_to_bv 64 ba)].
Definition pixa_obj (live : list (Z * Z)) (m : mem) (pa nalloc parr ba barr : Z) : Prop :=
  (exists pad, rw_cells asegs m pa (pixa_cells nalloc parr ba pad)) /\ chunk live pa 32 /\ chunk live parr (8 * nalloc)
  /\ boxa_empty live m ba nalloc barr /\ 1 <= nalloc <= 20
  /\ List.NoDup [pa; parr; ba; barr].

(* [comment removed for export] *)
Record cfv : Type := mkCfv { cf_pix : Z; cf_tw : Z; cf_th : Z; cf_boxas : Z; cf_barr : Z; cf_box : Z;
                             cf_naa : Z; cf_naarr : Z; cf_dnaa : Z; cf_dnarr : Z;
                             cf_pixa : Z; cf_parr : Z; cf_pba : Z; cf_pbarr : Z }.
Definition cf_cells (c : cfv) (pad : list byte) : list cell :=
  [C8 (Z_to_bv 64 (cf_pix c)); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 (cf_tw c)); C4 (Z_to_bv 64 (cf_th c));
   C4 (Z_to_bv 64 0); CB 4 pad; C8 (Z_to_bv 64 (cf_boxas c)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 (cf_naa c)); C8 (Z_to_bv 64 (cf_dnaa c)); C8 (Z_to_bv 64 (cf_pixa c))].
(* [comment removed for export] *)
Definition cf_chunks (c : cfv) : list (Z * Z) :=
  [(cf_boxas c, 24); (cf_barr c, 8); (cf_box c, 20); (* [comment removed for export] *)
   (cf_naa c, 16); (cf_naarr c, 8); (cf_dnaa c, 16); (cf_dnarr c, 8);
   (cf_pixa c, 32); (cf_parr c, 160); (cf_pba c, 24); (cf_pbarr c, 160)].
(* [comment removed for export] *)
Definition cf_live (cf : Z) (c : cfv) (live : list (Z * Z)) : list (Z * Z) :=
  (cf_pbarr c, 160) :: (cf_pba c, 24) :: (cf_parr c, 160) :: (cf_pixa c, 32) :: (cf_dnarr c, 8) :: (cf_dnaa c, 16)
  :: (cf_naarr c, 8) :: (cf_naa c, 16) :: (cf, 88) :: (cf_box c, 20) :: (cf_barr c, 8) :: (cf_boxas c, 24) :: live.

Definition cf_obj (live : list (Z * Z)) (m : mem) (cf : Z) (c : cfv) : Prop :=
  (exists pad, rw_cells asegs m cf (cf_cells c pad)) /\ chunk live cf 88
  /\ boxa_one live m (cf_boxas c) (cf_barr c) (cf_box c) 0 0 (cf_tw c) (cf_th c)
  /\ parr16_obj live m (cf_naa c) 1 (cf_naarr c) /\ parr16_obj live m (cf_dnaa c) 1 (cf_dnarr c)
  /\ pixa_obj live m (cf_pixa c) 20 (cf_parr c) (cf_pba c) (cf_pbarr c)
  /\ List.NoDup (map fst (cf_live cf c [])).
Section CfIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixClone_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (rc : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> pix_obj_rc (rt_live RT Σ) m pix v cv rc -> 1 <= rc < 2^31 - 1 ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixClone m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pix + 20, pix + 24)] m m'
          /\ rw_cells asegs m' pix (pix_cells_rc v (rc + 1))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixDestroy_rc_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp pix : Z) (v : pixv) (cv : cmapv) (rc : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optr RT Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 pix)] ->
  pix_obj_rc (rt_live RT Σ) m pix v cv rc -> 2 <= rc < 2^31 -> (pp + 8 <= pix \/ pix + 64 <= pp) ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8); (pix + 20, pix + 24)] m m'
          /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' pix (pix_cells_rc v (rc - 1))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixDestroy_null_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optr RT Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 0)] ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition boxCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (x y w h : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 y -> a2 = Z_to_bv 64 w -> a3 = Z_to_bv 64 h ->
  0 <= x < 2^31 -> 0 <= y < 2^31 -> 0 <= w < 2^31 -> 0 <= h < 2^31 ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 1 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxCreate m)))
    (fun c => exists (Σ' : rts RT) (b : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 b) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ box_obj (rt_live RT Σ') m' b x y w h) c
       /\ rt_live RT Σ' = (b, 20) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition boxaCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (n : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 n -> 1 <= n <= 20 ->
  uctx m sp s0 ras -> In (0x109f10 :: ras) CLIENT_TRACES ->
  (ras = [] -> bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 2 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxaCreate m)))
    (fun c => exists (Σ' : rts RT) (ba arr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ba) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ boxa_new (rt_live RT Σ') m' ba n arr) c
       /\ rt_live RT Σ' = (arr, n * 8) :: (ba, 24) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition boxaAddBox_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (ba arr b x y w h : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 ba -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 0 ->
  boxa_new (rt_live RT Σ) m ba 1 arr -> box_obj (rt_live RT Σ) m b x y w h -> b <> ba -> b <> arr ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxaAddBox m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(ba, ba + 4); (arr, arr + 8)] m m'
          /\ boxa_one (rt_live RT Σ') m' ba arr b x y w h) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition parr16Create_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (n : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 n -> 1 <= n <= 50 ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 2 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (o arr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 o) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ parr16_obj (rt_live RT Σ') m' o n arr) c
       /\ rt_live RT Σ' = (arr, n * 8) :: (o, 16) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).
Definition numaaCreate_cps : Prop := parr16Create_cps e_numaaCreate.
Definition l_dnaaCreate_cps : Prop := parr16Create_cps e_l_dnaaCreate.

(* [comment removed for export] *)
Definition pixaCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 ->
  uctx m sp s0 ras -> In (0x1083d8 :: ras) CLIENT_TRACES ->
  (ras = [] -> bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 4 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaCreate m)))
    (fun c => exists (Σ' : rts RT) (pa parr ba barr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pa) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ pixa_obj (rt_live RT Σ') m' pa 20 parr ba barr) c
       /\ rt_live RT Σ' = (barr, 160) :: (ba, 24) :: (parr, 160) :: (pa, 32) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition boxaDestroy_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp ba arr b x y w h : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (live_remove ba (live_remove arr (live_remove b (rt_live RT Σ)))) Σ m pp 8 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 ba)] -> boxa_one (rt_live RT Σ) m ba arr b x y w h ->
  lenv RT Σ m sp lo (LSTK 1) -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove ba (live_remove arr (live_remove b (rt_live RT Σ)))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition boxaDestroy_empty_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp ba nalloc arr : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (live_remove ba (live_remove arr (rt_live RT Σ))) Σ m pp 8 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 ba)] -> boxa_empty (rt_live RT Σ) m ba nalloc arr ->
  lenv RT Σ m sp lo (LSTK 1) -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_boxaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove ba (live_remove arr (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition parr16Destroy_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp o nalloc arr : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (live_remove o (live_remove arr (rt_live RT Σ))) Σ m pp 8 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 o)] -> parr16_obj (rt_live RT Σ) m o nalloc arr ->
  lenv RT Σ m sp lo (LSTK 1) -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove o (live_remove arr (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).
Definition numaaDestroy_cps : Prop := parr16Destroy_cps e_numaaDestroy.
Definition l_dnaaDestroy_cps : Prop := parr16Destroy_cps e_l_dnaaDestroy.

(* [comment removed for export] *)
Definition pixaDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp pa nalloc parr ba barr : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp ->
  optrL RT (live_remove pa (live_remove ba (live_remove barr (live_remove parr (rt_live RT Σ))))) Σ m pp 8 ->
  rw_cells asegs m pp [C8 (Z_to_bv 64 pa)] -> pixa_obj (rt_live RT Σ) m pa nalloc parr ba barr ->
  lenv RT Σ m sp lo (LSTK 2) -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove pa (live_remove ba (live_remove barr (live_remove parr (rt_live RT Σ))))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixaDestroy_null_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optr RT Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 0)] ->
  lenv RT Σ m sp lo (LSTK 2) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixaDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition l_colorfillCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 1 -> pix_obj (rt_live RT Σ) m pix v cv ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES) [0x109f10; 0x1083d8; 0xf74e0] ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 2 12 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_colorfillCreate m)))
    (fun c => exists (Σ' : rts RT) (cf : Z) (cv' : cfv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cf) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pix + 20, pix + 24)] m m'
          /\ (cf = 0 -> rw_cells asegs m' pix (pix_cells_rc v 1))
          /\ (cf <> 0 -> cf_obj (rt_live RT Σ') m' cf cv' /\ cf_pix cv' = pix /\ rw_cells asegs m' pix (pix_cells_rc v 2))) c
       /\ rt_live RT Σ' = (if cf =? 0 then rt_live RT Σ else cf_live cf cv' (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cf_live_destroy (cf : Z) (c : cfv) (live : list (Z * Z)) : list (Z * Z) :=
  live_remove cf
   (live_remove (cf_pixa c) (live_remove (cf_pba c) (live_remove (cf_pbarr c) (live_remove (cf_parr c)
     (live_remove (cf_dnaa c) (live_remove (cf_dnarr c)
       (live_remove (cf_naa c) (live_remove (cf_naarr c)
         (live_remove (cf_boxas c) (live_remove (cf_barr c) (live_remove (cf_box c) live))))))))))).
Definition l_colorfillDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp cf pix : Z) (c : cfv) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrF RT Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 cf)] ->
  (cf = 0 \/ (cf_obj (rt_live RT Σ) m cf c /\ cf_pix c = pix /\ pix_obj_rc (rt_live RT Σ) m pix v cv 2
              /\ ~ In pix (map fst (cf_live cf c [])))) ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 1 0 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_colorfillDestroy m)))
    (fun c' => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ (cf = 0 -> keeps RT Σ Σ' sp [] m m')
          /\ (cf <> 0 -> keeps RT Σ Σ' sp [(pp, pp + 8); (pix + 20, pix + 24)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]
                         /\ rw_cells asegs m' pix (pix_cells_rc v 1))) c'
       /\ rt_live RT Σ' = (if cf =? 0 then rt_live RT Σ else cf_live_destroy cf c (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition CF_FUZZ_LIVE : Z := 24.
Definition cf_fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 TP_A -> bv_unsigned ra = RA_TOP ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n /\ d mod 8 = 0) \/ bs = []) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + CF_FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_cf_fuzz m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) LIB_FP m m' /\ LIB m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ').

End CfIface.
