(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg Hoare AsanAcct HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_HeapIfaceA () := "C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C45stdpp;list_basics4list;list_filterC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC35stdpp4base6FilterC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List4inclI35stdpp4base5NoDup00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9aclient_gC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8in_blockC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic3notc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9in_fframeC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7ff_addrC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8ff_classC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8ff_bytesC13~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8ar_sptopC13~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2lec79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9hl_img_loC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9hl_img_hiC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA<in_shadow_ofC13~~~C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA;asan_layout00C13~~~i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8asan_run00C13~~~K47Corelib7Numbers7BinNums8positive03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA<hl_rt_staticC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8hl_rt_roC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA>aclient_g_monoC13~~~I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition SB : Z := 0x7fff8000.                       (* [comment removed for export] *)
Definition S (a : Z) : Z := a / 8 + SB.                (* [comment removed for export] *)
Definition BIGSHADOW_LO : Z := 0x7fff7000.             (* [comment removed for export] *)
Definition BIGSHADOW_HI : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition app_mem (a n : Z) : Prop := 0 <= a /\ (a + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= a) /\ a + n <= 2 ^ 47.

(* [comment removed for export] *)
Record asan_layout : Type := AL {
  hl_segs      : list Segment;        (* [comment removed for export] *)
  hl_malloc    : Z;                   (* [comment removed for export] *)
  hl_free      : Z;                   (* [comment removed for export] *)
  hl_aligned_alloc : Z;               (* [comment removed for export] *)
  hl_stack_malloc : Z -> Z;           (* [comment removed for export] *)
  hl_handle_no_return : Z;            (* [comment removed for export] *)
  hl_asan_memset : Z; hl_asan_memcpy : Z; hl_asan_memmove : Z;   (* [comment removed for export] *)
  hl_tp        : Z;                   (* [comment removed for export] *)
  hl_img_lo    : Z; hl_img_hi : Z;    (* [comment removed for export] *)
  hl_rt_static : Z -> Prop;           (* [comment removed for export] *)
  hl_rt_ro     : Z -> Prop;           (* [comment removed for export] *)
  hl_scr_malloc : Z; hl_scr_free : Z; hl_scr_aligned : Z;        (* [comment removed for export] *)
  hl_scr_stack_malloc : Z; hl_scr_no_return : Z; hl_scr_mem : Z; (* [comment removed for export] *)
  hl_k_per_malloc : Z; hl_b_lin : Z; hl_b_overhead : Z;         (* [comment removed for export] *)
  hl_K0 : Z; hl_B0 : Z                (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Record asan_run : Type := AR {
  ar_sptop : Z;                       (* [comment removed for export] *)
  ar_stack_top : Z; ar_stack_bottom : Z;   (* [comment removed for export] *)
  ar_fs : Z;                          (* [comment removed for export] *)
  ar_space_beg : Z                    (* [comment removed for export] *)
}.
Abbreviation ahl_ceil ar := (ar_sptop ar - 8388608).
(* [comment removed for export] *)
Definition app_rng (ar : asan_run) (a n : Z) : Prop :=
  0 <= a /\                                                                                       (* [comment removed for export] *)
  (a + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= a) /\ (a + n <= ar_sptop ar \/ a + n + 16 <= 2 ^ 47).     (* [comment removed for export] *)
Definition FS_BYTES : Z := 0xb09000.

(* [comment removed for export] *)
Definition acredit_ok (L : asan_layout) (cr : credit) (n : Z) : Prop :=
  hl_k_per_malloc L <= fst cr /\ hl_b_lin L * n + hl_b_overhead L <= snd cr.
Definition adebit (L : asan_layout) (cr : credit) (n : Z) : credit :=
  (fst cr - hl_k_per_malloc L, snd cr - (hl_b_lin L * n + hl_b_overhead L)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fframe : Type := (Z * Z * Z)%type.
Definition ff_addr (f : fframe) : Z := fst (fst f).
Definition ff_class (f : fframe) : Z := snd (fst f).
Definition ff_rs (f : fframe) : Z := snd f.
Definition ff_bytes (k : Z) : Z := 64 * 2 ^ k.
(* [comment removed for export] *)
Definition ff_owned (FF : list fframe) (a : Z) : Prop :=
  exists f, In f FF /\ (ff_addr f + 24 <= a < ff_addr f + 32
                        \/ ff_addr f + ff_bytes (ff_class f) - 8 <= a < ff_addr f + ff_bytes (ff_class f)).
Definition in_fframe (FF : list fframe) (a : Z) : Prop :=
  exists f, In f FF /\ ff_addr f <= a < ff_addr f + ff_bytes (ff_class f) - 8 /\ ~ (ff_addr f + 24 <= a < ff_addr f + 32).
Fixpoint ff_remove (F : Z) (FF : list fframe) : list fframe :=
  match FF with
  | [] => []
  | f :: r => if Z.eqb (ff_addr f) F then r else f :: ff_remove F r
  end.
Definition ff_count (k : Z) (FF : list fframe) : nat := length (filter (fun f => Z.eqb (ff_class f) k) FF).
(* [comment removed for export] *)
Definition ff_cap (k : Z) : Z := 2 ^ 20 / ff_bytes k.

(* [comment removed for export] *)
Definition byte_at (M : word -> option byte) (a v : Z) : Prop := M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Definition shadow_zero (M : word -> option byte) (a g : Z) : Prop :=
  forall j, 0 <= j < g -> byte_at M (S a + j) 0.
(* [comment removed for export] *)
Definition shadow_blk (M : word -> option byte) (u n : Z) : Prop :=
  shadow_zero M u (n / 8) /\ (n mod 8 <> 0 -> byte_at M (S u + n / 8) (n mod 8)).
(* [comment removed for export] *)
Definition aacc (M : word -> option byte) (p n : Z) : Prop :=
  forall a, p <= a < p + n -> byte_at M (S a) 0 \/ (exists v, byte_at M (S a) v /\ 1 <= v <= 7 /\ a mod 8 < v).
(* [comment removed for export] *)
Definition in_shadow_of (a n x : Z) : Prop := S a <= x <= S (a + n - 1).

(* [comment removed for export] *)
Definition ablock_range (L : asan_layout) (ar : asan_run) (u n : Z) : Prop :=
  4096 <= u /\ (u + n <= hl_img_lo L \/ hl_img_hi L <= u) /\ u mod 16 = 0 /\ 0 < n /\ u + n <= ahl_ceil ar /\ app_mem u n.
Definition fframes_apart (a n : Z) (FF : list fframe) : Prop :=
  forall f, In f FF -> a + n <= ff_addr f \/ ff_addr f + ff_bytes (ff_class f) <= a.

(* [comment removed for export] *)
Definition block_shadow (LB : list (Z * Z)) (a : Z) : Prop := exists b, In b LB /\ in_shadow_of (fst b) (snd b) a.
Definition aclient_g (BS : Z -> Z -> Z -> Prop) (ST : Z -> Prop) (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scratch : Z) (a : Z) : Prop :=
  in_block LB a
  \/ (ahl_ceil ar <= a < 2 ^ 47 /\ ~ (sp - scratch <= a < sp))
  \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ ST a)
  \/ in_fframe FF a
  \/ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a                            (* [comment removed for export] *)
  \/ (exists f, In f FF /\ in_shadow_of (ff_addr f) (ff_bytes (ff_class f)) a)     (* [comment removed for export] *)
  \/ (exists b, In b LB /\ BS (fst b) (snd b) a).                                  (* [comment removed for export] *)
Definition aclient (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scratch a : Z) : Prop :=
  aclient_g in_shadow_of (hl_rt_static L) L ar LB FF sp scratch a.
Definition aclientw (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scratch a : Z) : Prop :=
  aclient_g (fun _ _ _ => False) (fun x => hl_rt_static L x \/ hl_rt_ro L x) L ar LB FF sp scratch a.
Lemma aclient_g_mono (BS BS' : Z -> Z -> Z -> Prop) (ST ST' : Z -> Prop) L ar LB FF sp scratch a :
  (forall q n x, BS q n x -> BS' q n x) -> (forall x, ST' x -> ST x) -> aclient_g BS ST L ar LB FF sp scratch a -> aclient_g BS' ST' L ar LB FF sp scratch a.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceA ()) [] "p'0h01bh11fh21Xh32H0h42BSh53BS'h62FFh71Lh82LBh92STh:3ST'h;1ah<2arh=7scratchh>2sph?1xi001xh@1HhA2HShB2HbhC1YhD1nhE1qp;2p;1p;9p;3p;4p-1R0g0000R1p4p710R2p8P0p1000GR3p4p710R4p8P0P3p4p7210p8P0p1000cp4p710p8P0g001DR3p4p710p8P0P3p4p7210p8P0p1001aR5p4p710R6p8P0P5p4p7210R5p8P0p10025p4p710R0p8g002QR7p4p70R8P2p8P8P4p8P8p1003]p4p710p8P8p1004Bp4p710p8P8p1004bp4p710p8P8p1005?R4p4p710p8P8P4p4p7210p8P8p1005Sp4p710p8P8p1005op4p710p8p1006Hp4p710R8P6p8P8P5p8P8P0p8g006]j2eTg007=j1YTg007]l99Tg008lj2=Tg00:9j1ETg00:^j1QTg00;<j1NTg00;aj2ZTg00<>j2FTg00<Zj13Tg00=3j28Tg00>Bj1]Tg00?Oj1\Tg00@]j1[Tg00AkR0j24TP1j3<Tg00BER1j21Tg00B`j3GTg00C:R8j20Tg00CTj3HTg00Cnj3dTg00DIj4cTg00Ddj4WTg00E?j4bTg00EYj1`Tg00Fgj2RTg00GDj2JTg00G`j1UTg00Hoj1XTg00J>j3VTP3j3^Tg00KPj3aTf0R3#E#Ep=_%E3#E#E#Ep=If1R5#`/R3p=6f2R6/J5/13p=Sf4R4f3R2'R/J61F53'1#3p=:%U2/J6%X3,F5'1p=A1R65=V23p=7A<742AV653'1p=5g00KmR9?^93p=PAa993p=OA<265/13p=;1475/03p=C1053,06p=21165/03p=@1J421F65'1/13p=>%33,15p=T1473p=?1453,06p=D%U5/J3p=K%X3,F5p=L1165/13p=MAH6539H42p=Bp-0\9R:\9\9R;g00LKR<g00M^R=1e99R>#YR?%Y7R@f=RAP6P5P3O3PAP2P6P5O3[^?9^D9^E9f9RBP3O1f;RCP5O1[^?9f<RDf:REf8RFf7RGf6RHf5RIP4P2P6M99P81=G2g00Nn#ERJ#_#I#I#I#I#I#QRK,6FRL%QJ%NJ#N#N#N#Q'ZRJ,F27S2PIP4P2P2PID:PBP2P2PBCAPCP2O1#318H2PLPJPLP2C7P3PG%]3RL%\3#[RMP4D5X17P>P3PFf>RN%P3RO%O3RPP4O3C;X0>,4>'C323@3@PAPCPEPBPFPGPHPIP4M99P31=F41=BI16EKRQPIPIPJPGPHPIPIPGD:D>RRPCPIPIPCCARSPDPIO1'T18FIRTPQPJPQPIC7RQP3PBPLPMPHD5X17#?RUA<>3ERVf?RWPOPPPHO3'1X0>7D>3232;G3PNPDPCPEPBPFPGPHPIM99eW2P3O116BKRX1F4J7S4PHPIP4P4PHD:PEP4P4PECAPDP4O1#318G4PXPJPXP4C7P3PFPLPMPID5X17P>P3PBPWPOPPPIO3C;X0>,4>'C323@3@P8PRPAPIO1#3f@RRPOPPPHO3,1VX0>9DU>92TQ5@SPWPAPDPCPEPBPFPGPHM99P316CKRSPHPHPJPFPGPHPHPFD:D>1=CG16DKRQPGPGPJPBPFPGPGPBD:D>RTPAPGPGPACARUPNPGO1#318EGRVPQPJPQPGC7RQP3PCPLPMPFD5X17#?RXA<>3DRYfARZPOPPPFO3'1X0>7D>323@R['0AGT[33HPRPNPAPDPCPEPBPFPGM99eW2P3O1PDPHPHPDCAPNPHO1#318BHPSPJPSPHC7P3PEPLPMPGD5X17P>P3PCPZPOPPPGO3C;X0>,4>'C323@P8PWPGO1,TUfBRUPOPPPFO3,1YX0>9DX>92VQPZPWPNPAPDPCPEPBPFM99P31KNF1LFNPRPFO1#33M1=AB16NKRQPBPBPJPCPEPBPBPCD:D>RVPWPBPBPWCARXPRPBO1RY#3RS'1R[18DBRTPQPJPQPBC7RQP3PAPLPMPED5X17#?R\A<>3NR]fCR^POPPPEO3'1X0>7D>32R_'0R`'0PVP`PXPSPZPBO1#3=dX3PRPEPEPRCAPUPEO1#3P5PFPEP3O2CcXCYPSeCW9G[_DBPUPRPWPNPAPDPCPEPBM99eW2P3O118CF16AKR_PJP_PFC7P3PDPLPMPBD5X17P>P3PAP^POPPPBO3C;X0>,4>'C32P8PTfDRTPOPPPEO3,1]X0>,4>92Q\P^PZPRPWPNPAPDPCPEM99P318AE1=WC16RKR\PCPCPJPAPDPCPCPAD:D>RQ1KZC1LCZPUPCO1#33MR]18NCR_P\PJP\PCC7R\P3PWPLPMPDD5X17#?R[A<>3RRSfERYPOPPPDO3'1X0>,4>32RX'0R`'0RV'0PQPVAG_X39H]`DBPTPUPZPRPWPNPAPDPCM99eW2P3O116WKR`PJP`PEC7P3PNPLPMPCD5X17#?P>P3PWPYPOPPPCO3C;X0>,4>32P8P\fFR\POPPPDO3,1SX0>9D[>PYP^PUPZPRPWPNPAPDM99P316ZKR[PJP[PDC71=ZA16UKRDPAPAPJPWPNPAPAPWD:D>R[1K^A1LA^PTPAO1#33MRS18RARCPDPJPDPAC7RDP3PZPLPMPND5X17#?R`A<>3UR]fGRXPOPPPNO3'1X0>7D>R_'0RV'0RQ'0Ra'0P[PaPSPQPCPVAGD_3DBDBP\PTP^PUPZPRPWPNPAM99eW2P3O1P3PRPLPMPAD5X17P>P3PZPXPOPPPAO3C;X0>,4>'CP8P`fHR`POPPPNO3,1]X0>,4>PXPYPTP^PUPZPRPWPNM99P3P3PUPLPMPWD5X17#?1=^W16TKRNPWPWPJPZPRPWPWPZD:D>R]1KYW1LWYP\PWO1#33MR818UWRAPNPJPNPWC7RNP3P^PLPMPRD5X17#?R_A<>3TRDfIRVPOPPPRO3'1X0>,4>RC'0RQ'0RS'0Ra'0R['0P]P[P8PaPAPSAG_C39HNQDBDBP`P\PYPTP^PUPZPRPWM99RQeW2P3O1P>P3P^PVPOPPPWO3C;X0>,4>P0P>fJR0POPPPRO3,1DX0>1=TR16YKRDPRPRPJPUPZPRPRPUD:D>P\PRPRP\CAPXPRO1#318^RPDPJPDPRC7P3PTPLPMPZD5X17P>P3PYP0POPPPZO3C;X0>,4>'C323@32P3P>P3P\fLRZPOPPPUO3C;P1A<>5XfMR1%P5%O5P^O31=`T16VKR^PTPTPJP\PYPTPTP\D:D>P0PTPTP0CAfKRUPTO1#318XTP^PJP^PTC7P3P`PLPMPYD5X17P>P3PVfNRTPOPPPYO3C;X0>,4>'C323@32P3A<>2VfPRY%P4%O4P\O31=UX16ZKRKPXPXPJPVP`PXPXPVD:D>RV1K1X1LX1PTPXO1#33MRT180XR0PKPJPKPXC7RKP3PUPLPMP`D5X17#?R7P>P3PZfQPOPPP`O3C;X0>R`,4>RP'0RO'0RZ'0RM'0RL'0PVPLPTPMP0PZPKPOP7PPP>P`PIA<>IUPY%PIRY%OIRUPXO3P5P\PYPUPXP3O4CWCbDBDBDBW2WBP5P3O2n2001000010121000000W3X0>P5P3O2n2001000010121100000PQeW2P3O1n200100000021100011000W3P3O1n200100000021100011000W3P3O1n200100000021100011000W3P3O1n200100000021100011000W3P3O1n200100000021100011000W3P3O1n201100000021100011000W3WAW@X;9X=9X>9X6@X8?X<=X7<X::X9:X5;X4;PEPBPFPGPHPIP4P2P6P5P3O;X;9X=9X>9W6W8W<W7X::X9:X5;W4o"). Qed.
Lemma aclientw_client L ar LB FF sp scratch a : aclientw L ar LB FF sp scratch a -> aclient L ar LB FF sp scratch a.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceA ()) [] "h01xh12FFh21Lh32LBh41ah52arh67scratchh72sph81Hh91Xh:1nh;1qp;2p;1p;3p;=g006]j28Tg007=j12Tg00OSj20j16Tg00Pej21Tg00C:j27Tg00J>R0j34Tg00B`j33Tg00R3l=5Tg00LKR1g00M^R2g00KmR3/83#2R4g002Q#2R5g00SGR6V3V3V3P0f7R0f0R7'0R81107'7X03f6R0#6P0f5R9f4R:f3R;f2R<f1R=P7P6A4:;<P7n010000000X86X03X:3X;3f8R6/0=116=;37X98X03M=5X43X63X73X15X34X52X21P0P9P:P;P<P=P7O7X43X63X73W1W3W5W2o"). Qed.

Definition aheap_pres (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scratch : Z)
           (M M' : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scratch a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall a, sp - scratch <= a < sp -> M' (Z_to_bv 64 a) <> None).

(* [comment removed for export] *)
Definition astack_ok (L : asan_layout) (ar : asan_run) (M : word -> option byte) (scratch sp : Z) : Prop :=
  sp mod 16 = 0 /\ ahl_ceil ar + 4096 + scratch <= sp /\ sp <= ar_sptop ar /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\
  (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= scratch -> store_ok (hl_segs L) M (Z_to_bv 64 (sp - scratch + d)) m = true) /\
  defined M sp (ar_stack_top ar - sp).

(* [comment removed for export] *)
Definition model_rt (m m' : Model) : Prop :=
  m' = mkModelOf (m_fd m) (m_vm m') (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
(* [comment removed for export] *)
Definition vml : Type := (VmMaps * list (word * word))%type.
Definition vml_of (m : Model) : vml := (m_vmmaps m, m_vm_lazy m).

(* [comment removed for export] *)
Definition shadow_allowed (A : list (Z * Z)) (a n : Z) : Prop :=
  forall x, in_shadow_of a n x -> page_allowedb A (page_base (Z_to_bv 64 x)) = true.
(* [comment removed for export] *)
Definition ahid (A : list (Z * Z)) (m : Model) : word -> bool := mkH (m_vm_lazy m) A.

(* [comment removed for export] *)
Record asan_statics_cells : Type := ASC {
  asc_got_lo : Z; asc_got_hi : Z;     (* [comment removed for export] *)
  asc_cells : list (Z * Z * Z)        (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition cell_is (segs : list Segment) (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Definition asan_statics (segs : list Segment) (C : asan_statics_cells) (M : word -> option byte) : Prop :=
  (forall a, asc_got_lo C <= a < asc_got_hi C -> M (Z_to_bv 64 a) = None)
  /\ Forall (fun c => cell_is segs M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) (asc_cells C).

(* [comment removed for export] *)
Section AIface.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.       (* [comment removed for export] *)

Record asan_iface : Type := AI {
  ri_inv : list (Z * Z) -> list fframe -> list fframe -> credit -> list (Z * Z) -> (word -> option byte) -> vml -> Prop
}.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

(* [comment removed for export] *)
Definition amalloc_post (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet) : Prop :=
  forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)) (u : Z),
    getr R' 10%bv = Z_to_bv 64 u ->
    regs_preserved R R' ->
    ablock_range L ar u n -> blocks_apart u n LB -> fframes_apart u n (FF ++ LK) ->
    defined M' u n -> shadow_blk M' u n ->
    aheap_pres L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_malloc L) M M' ->
    model_rt model model' -> incl A A' -> MInv A' model' ->
    ri_inv HI ((u, n) :: LB) FF LK (adebit L cr n) A' M' (vml_of model') ->
    srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K.

Definition amalloc_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> acredit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_malloc L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    amalloc_post fx R M model LB FF LK cr A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.

Definition aaligned16_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= 4096 -> n mod 16 = 0 -> acredit_ok L cr n ->       (* [comment removed for export] *)
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_aligned L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)) (u : Z),
        getr R' 10%bv = Z_to_bv 64 u ->
        regs_preserved R R' ->
        ablock_range L ar u n -> blocks_apart u n LB -> fframes_apart u n (FF ++ LK) ->
        defined M' u n -> shadow_blk M' u n ->
        aheap_pres L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_aligned L) M M' ->
        model_rt model model' -> incl A A' -> MInv A' model' ->
        ri_inv HI ((u, n) :: LB) FF LK (adebit L cr n) A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_aligned_alloc L)) M model) K.

Definition afree_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (u n : Z) (K : ShapeAlg.TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    In (u, n) LB -> getr R 10%bv = Z_to_bv 64 u ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_free L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
        regs_preserved R R' ->
        aheap_pres L ar (lb_remove u LB) FF (bv_unsigned (getr R 2%bv)) (hl_scr_free L) M M' ->
        model_rt model model' -> incl A A' -> MInv A' model' ->
        ri_inv HI (lb_remove u LB) FF LK cr A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_free L)) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ff_room (k : Z) (FF LK : list fframe) : Prop := Z.of_nat (ff_count k (FF ++ LK)) + 2 <= ff_cap k.

Definition astack_malloc_spec (k : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_stack_malloc L) sp ->
    ff_room k FF LK ->
    (forall f, In f FF -> sp + 32 <= ff_rs f) ->                    (* [comment removed for export] *)
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (F fl : Z) (LK' : list fframe),
        getr R' 10%bv = Z_to_bv 64 F ->
        regs_preserved R R' ->
        ar_fs ar <= F /\ F + ff_bytes k <= ar_fs ar + FS_BYTES /\ F mod ff_bytes k = 0 /\ app_mem F (ff_bytes k) /\ F + ff_bytes k <= ahl_ceil ar ->
        (F + ff_bytes k <= hl_img_lo L \/ hl_img_hi L <= F) ->
        fframes_apart F (ff_bytes k) (FF ++ LK') -> (forall b, In b LB -> F + ff_bytes k <= fst b \/ fst b + snd b <= F) ->
        incl LK' LK ->                                              (* [comment removed for export] *)
        defined M' F (ff_bytes k) ->
        cell_is (hl_segs L) M' (F + ff_bytes k - 8) 8 fl ->                 (* [comment removed for export] *)
        ar_fs ar <= fl < ar_fs ar + FS_BYTES -> ~ aclient L ar LB ((F, k, sp + 32) :: FF) 0 0 fl ->          (* [comment removed for export] *)
        (F + ff_bytes k <= fl \/ fl + 1 <= F) ->                   (* [comment removed for export] *)
        store_ok (hl_segs L) M' (Z_to_bv 64 fl) 1 = true ->
        shadow_zero M' F (ff_bytes k / 8) ->                        (* [comment removed for export] *)
        aheap_pres L ar LB FF sp (hl_scr_stack_malloc L) M M' ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB ((F, k, sp + 32) :: FF) LK' cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_stack_malloc L k)) M model) K.

(* [comment removed for export] *)
Definition rt_release_frame : Prop :=
  forall LB FF LK cr A M M' V F k rs fl,
    ri_inv HI LB FF LK cr A M V -> In (F, k, rs) FF -> cell_is (hl_segs L) M (F + ff_bytes k - 8) 8 fl ->
    (forall a, 0 <= a < 2 ^ 64 -> a <> fl -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) \/ aclientw L ar LB FF 0 0 a) ->      (* [comment removed for export] *)
    cell_is (hl_segs L) M' fl 1 0 -> (forall a : word, M a <> None -> M' a <> None) ->
    ri_inv HI LB (ff_remove F FF) LK cr A M' V.
(* [comment removed for export] *)
Definition rt_flagptr : Prop :=
  forall LB FF LK cr A M V LB' FF' LK' cr' A' M' V' F k rs rs' fl,
    ri_inv HI LB FF LK cr A M V -> ri_inv HI LB' FF' LK' cr' A' M' V' ->
    In (F, k, rs) FF -> In (F, k, rs') FF' ->
    cell_is (hl_segs L) M (F + ff_bytes k - 8) 8 fl -> cell_is (hl_segs L) M' (F + ff_bytes k - 8) 8 fl.
(* [comment removed for export] *)
Definition rt_leak_frames : Prop :=
  forall LB FF LK cr A M V FX,
    ri_inv HI LB FF LK cr A M V -> incl FX FF -> NoDup (map ff_addr FX) ->
    ri_inv HI LB (filter (fun f => negb (existsb (fun g => Z.eqb (ff_addr g) (ff_addr f)) FX)) FF) (FX ++ LK) cr A M V.

(* [comment removed for export] *)
Definition ahandle_no_return_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_no_return L) sp ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (lo : Z),
        regs_preserved R R' ->
        sp - hl_scr_no_return L - 4096 <= lo <= sp -> lo mod 4096 = 0 ->       (* [comment removed for export] *)
        shadow_zero M' lo ((ar_stack_top ar - lo) / 8) ->          (* [comment removed for export] *)
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp (hl_scr_no_return L) a ->
                   ~ in_shadow_of lo (ar_stack_top ar - lo) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - hl_scr_no_return L <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_handle_no_return L)) M model) K.

(* [comment removed for export] *)
Definition amem_post (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dst n : Z)
           (NEWB : Z -> Z -> Prop) (K : ShapeAlg.TSet) : Prop :=
  forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
    getr R' 10%bv = Z_to_bv 64 dst -> regs_preserved R R' ->
    (forall i, 0 <= i < n -> exists v, NEWB i v /\ byte_at M' (dst + i) v) ->
    (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) a ->
               ~ (dst <= a < dst + n) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a, bv_unsigned (getr R 2%bv) - hl_scr_mem L <= a < bv_unsigned (getr R 2%bv) -> M' (Z_to_bv 64 a) <> None) ->
    model_rt model model' -> MInv A model' ->
    ri_inv HI LB FF LK cr A M' (vml_of model') ->
    srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K.

Definition amem_pre (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dst n : Z) (K : ShapeAlg.TSet) : Prop :=
  ri_inv HI LB FF LK cr A M (vml_of model) /\ m_halted model = None /\ MInv A model /\
  getr R 10%bv = Z_to_bv 64 dst /\ getr R 12%bv = Z_to_bv 64 n /\ 0 <= n <= 2 ^ 27 /\
  getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ Hoare.ret_ok (getr R 1%bv) /\
  astack_ok L ar M (hl_scr_mem L) (bv_unsigned (getr R 2%bv)) /\
  aacc M dst n /\ (forall i, 0 <= i < n -> aclientw L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (dst + i)) /\   (* [comment removed for export] *)
  (forall i (m : nat), 0 <= i -> i + Z.of_nat m <= n -> store_ok (hl_segs L) M (Z_to_bv 64 (dst + i)) m = true) /\
  K [] /\ app_rng ar dst n.                                            (* [comment removed for export] *)

Definition amemset_spec : Prop :=
  forall fx R M model LB FF LK cr A dst c n K,
    amem_pre fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 c ->
    amem_post fx R M model LB FF LK cr A dst n (fun _ v => v = c mod 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_asan_memset L)) M model) K.

Definition amemcpy_spec_at (pc : Z) (may_overlap : bool) : Prop :=
  forall fx R M model LB FF LK cr A dst src n (bs : list byte) K,
    amem_pre fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 src ->
    aacc M src n -> 0 <= src /\ src + n <= 2 ^ 47 -> app_rng ar src n ->       (* [comment removed for export] *)
    (forall i, 0 <= i < n -> hl_img_lo L <= src + i < hl_img_hi L \/ aclient L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (src + i)) ->
                                                                          (* [comment removed for export] *)
    rdn (hl_segs L) M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->          (* [comment removed for export] *)
    (may_overlap = false -> dst + n <= src \/ src + n <= dst) ->
    amem_post fx R M model LB FF LK cr A dst n (fun i v => nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.
Definition amemcpy_spec : Prop := amemcpy_spec_at (hl_asan_memcpy L) false.
Definition amemmove_spec : Prop := amemcpy_spec_at (hl_asan_memmove L) false.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_private (LB : list (Z * Z)) (FF : list fframe) (a : Z) : Prop :=
  ~ aclient L ar LB FF 0 0 a \/ hl_rt_ro L a \/ block_shadow LB a.        (* [comment removed for export] *)

Definition rt_frame : Prop :=
  forall LB FF LK cr A M M' V,
    ri_inv HI LB FF LK cr A M V ->
    (forall a, 0 <= a < 2 ^ 64 -> art_private LB FF a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    ri_inv HI LB FF LK cr A M' V.

Definition rt_wf : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    (forall b, In b LB -> ablock_range L ar (fst b) (snd b) /\ defined M (fst b) (snd b) /\ shadow_blk M (fst b) (snd b)
                       /\ shadow_allowed A (fst b) (snd b)
                       /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB) /\ fframes_apart (fst b) (snd b) (FF ++ LK)
                       /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b))         (* [comment removed for export] *)
    /\ (forall f, In f FF -> ar_fs ar <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs ar + FS_BYTES
                       /\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) [1; 2; 3]
                       /\ defined M (ff_addr f) (ff_bytes (ff_class f))
                       /\ fframes_apart (ff_addr f) (ff_bytes (ff_class f)) (ff_remove (ff_addr f) FF ++ LK))
    /\ app_mem (ar_fs ar) FS_BYTES /\ ar_fs ar + FS_BYTES <= ahl_ceil ar /\ (ar_fs ar + FS_BYTES <= hl_img_lo L \/ hl_img_hi L <= ar_fs ar)
    /\ shadow_allowed A (ar_fs ar) FS_BYTES
    /\ shadow_allowed A (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar)
    /\ (ahl_ceil ar <= ar_stack_bottom ar + 4096 /\ ar_stack_bottom ar <= ahl_ceil ar + 4096)   (* [comment removed for export] *)
    /\ (ar_stack_bottom ar mod 4096 = 0 /\ ar_stack_top ar = ar_stack_bottom ar + 8388608
        /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\ ar_sptop ar mod 16 = 0)     (* [comment removed for export] *)
    /\ ar_stack_top ar <= 2 ^ 47
    /\ NoDup (map fst LB) /\ NoDup (map ff_addr (FF ++ LK)) /\ 0 <= fst cr /\ 0 <= snd cr
    /\ defined M (ar_fs ar) FS_BYTES.                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_lazy : Prop :=
  forall LB FF LK cr A M model, ri_inv HI LB FF LK cr A M (vml_of model) ->
    A_wf A
    /\ (forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
          let a := bv_unsigned w in
          hl_img_hi L <= a /\ a < ahl_ceil ar /\ ~ in_block LB a /\ ~ (ar_fs ar <= a < ar_fs ar + FS_BYTES)).

Definition rt_perm : Prop :=
  forall LB LB' FF FF' LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    (forall b, In b LB <-> In b LB') -> NoDup (map fst LB') -> (forall f, In f FF <-> In f FF') -> NoDup (map ff_addr FF') ->
    ri_inv HI LB' FF' LK cr A M V.

(* [comment removed for export] *)
Definition rt_small_high : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V -> forall b, In b LB -> snd b <= 4096 -> BIGSHADOW_HI <= fst b.

Definition rt_statics : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V -> asan_statics (hl_segs L) C M.

(* [comment removed for export] *)
Record asan_iface_ok : Prop := AIOK {
  aio_malloc : amalloc_spec;
  aio_aligned : aaligned16_spec;
  aio_free : afree_spec;
  aio_stack_malloc : forall k, In k [1; 2; 3] -> astack_malloc_spec k;
  aio_release : rt_release_frame;
  aio_leak : rt_leak_frames;
  aio_no_return : ahandle_no_return_spec;
  aio_memset : amemset_spec;
  aio_memcpy : amemcpy_spec;
  aio_memmove : amemmove_spec;
  aio_frame : rt_frame;
  aio_wf : rt_wf;
  aio_lazy : rt_lazy;
  aio_perm : rt_perm;
  aio_statics : rt_statics;
  aio_flagptr : rt_flagptr;         (* [comment removed for export] *)
  aio_small_high : rt_small_high    (* [comment removed for export] *)
}.
End AIface.

(* [comment removed for export] *)
