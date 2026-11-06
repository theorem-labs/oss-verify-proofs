(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep MallocHINV MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Malloc_iface () := "C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC45stdpp;list_basics4list;list_filterC35stdpp4base6FilterC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstI47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib6Malloc<Malloc_iface<client_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib6Malloc<Malloc_iface8in_blockC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula07K47Corelib4Init5Logic2or02K46Stdlib9micromega6VarMap1t01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib6Malloc<Malloc_iface;client_addrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic5False00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition AGP : Z := 0x1a800.          (* [comment removed for export] *)
Definition ATP : Z := 0x1a620.          (* [comment removed for export] *)
Definition ERRNO : Z := ATP - 164.      (* [comment removed for export] *)
Definition MALLOC_SYM : Z := 0x1596c.   (* [comment removed for export] *)
Definition FREE_SYM : Z := 0x156e0.     (* [comment removed for export] *)
Definition MALLOC_STACK : Z := 8192.    (* [comment removed for export] *)
Definition FREE_STACK : Z := 8192.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition MEDTAB : Z := 0x1a060.        (* [comment removed for export] *)
Definition alloc_static (a : Z) : Prop :=
  (MLOCK <= a < MLOCK + 4) \/ (LIBC <= a < CTX + 928) \/ (ERRNO <= a < ERRNO + 4) \/ (MEDTAB <= a < MEDTAB + 4).
(* [comment removed for export] *)
Definition medtab_cells : list cell := [C1 (Z_to_bv 8 28); C1 (Z_to_bv 8 24); C1 (Z_to_bv 8 20); C1 (Z_to_bv 8 32)].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition in_block (LB : list block) (a : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

(* [comment removed for export] *)
Definition client_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x19000 <= a < 0x1b000 /\ ~ alloc_static a) \/ in_block LB a.

(* [comment removed for export] *)
Definition client_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0x19000 <= A /\ A + n <= 0x1b000 /\ (A + n <= MLOCK \/ MLOCK + 4 <= A) /\ (A + n <= LIBC \/ CTX + 928 <= A)
      /\ (A + n <= ERRNO \/ ERRNO + 4 <= A) /\ (A + n <= MEDTAB \/ MEDTAB + 4 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

Lemma client_range_addr : forall LB SP A n a,
  client_range LB SP A n -> A <= a < A + n -> client_addr LB SP a.
Proof.
ltac2:(KReplay.run1 (kr_t_Malloc_iface ()) ["CANSEC1"] "p'0h01bh14__x1h24__x2h34__x3h42H0h57__arithh64__ffh78__varmaph85__with91Hh:4__p1h;4__x4h<4__x5h=1Ah>2H1h?2H2h@2HRhA2HahB2HbhC2LBhD2SPhE1ahF1ni001xp&0p;1p;4p;2p;6p;3p;7p;8g0000R0p4p70R1g000nR2p4p710p8P1p1001Ep4p710p8P1p1001jR3p4p710p8P1P3p4p7210p8p1002>p4p70p10033p4p710p8g003Pj1jTg0040k407Tg0055j20Tg005Qj22Tg005nj18Tg006Sj14Tg0078j1aTg007Vk203Tg0083j1JTg0094j1MTg00:5R3j2\Tg00:Oj2FTg00;Pj1BTg00;oj2gTg00<Xj1mTg00=8j2ZTg00=Vj4YTg00>4j1lTg00>Rj1kTg00?=j2UTg00?`k605Tg00@Dk104Tg00@fk202Tg00AHk200Tg00Abj2~Tg00BNj3}Tg00Bhj3|Tg00CGj4{Tg00D9j2:Tg00DUj3iTg00DoR1j2KTg00EIj3zTg00Elj6yTg00FPj3cTg00Fjj1wTg00GHj4tTg00Gcj4sTg00H=j3rTg00IAR4j27TP2j3xTg00I\j1qTg00J5j3^Tg00J^j2hTg00KJj3QTg00Kjj4[Tg00LUj7`Tg00M9j7fTg00M]j8pTg00NAk301Tg00Ndj2oTg00OGj7nTf2R2f1R5f0R6':'7p=X%86#4p=V%46#4#4#4p=_%46#4#4#ap=E%46#4p=A%46#8p=S%46#ap>061025/K6p=@f4R7f3R8'01025'K/76p=61025/76p=WAx056p=?1025/76,78p=<1725/K6p=G10821:56'7p=Rf7R9f6R:'0f5R;/:7'710821:56'7'Kp=C10781:25'7/K6p==10781:25'7/K6#qp=Hg00OkR</g6p=DA^<56p=5g00PIR=g00Q5R>,h5;Q6p=TP7g00QaR?g00R@R@P@g00R`RAP8P?P@P@PAP<P2g00S@RBP5C[g00SgRCF`P6Ffp=>P2P?P@P@PAP<P5PBP6C[PCF`p=9P8P?P@P@PAP2P5P6Gpp=P1725/76p=eA^<56/h>p=3A^<569^<2p=dAQ=569Q=2p=bAQ=569Q=29Q=89Q=7p=1B01<56p=OP2P?P@P@PAP<P5g00TGR>P6C[PCF`p=L1o<6p=;P2P?P@P@PAP5P6Fnp=NP2P?P@P@PAP5P6Ffp=]1225/06p=IP<P5P>P6C[p=vP8P?P@P@PAP2P5P?P@P@PAP6PCF`Ffp=u%j0P7P8P2P5H071085RC12827X5P110;7g00TnR>#8RB#4RD#4#V#_#_#ERE/07RF1278RG%8DRD#V#_#_#ERHPG%ADRD#ARI#4RJ#8#V#V#ERK%4>RL#4RM#aRN,2KROP7PG%8IRI#4#S#A#ERP%8I#A#S#ERI%8B#S#A#ERQ'2RRP7PG%8D#8#A#S#A#ERD%8LRS#A#V$06RT+03RU12UNRVP7%SJ#8#A#ERJ12JNRW/075@GD6D6D63W1?69%J6RGP;12;7RX%M6,2GRY'0C<X00,\03GPEP8P8PHCRPKP8P8POPPP8P8PRPUP8P8PVPJP8P8PWGCD=DH1F983G9@:8P510:;1097AXF7HPKP7P7POPPP7P7PRPUP7P7PVPJP7P7PWGCD=DHf8RF/F73Gp-0RZg00USR[#BR\#BR]#DR^%D\R\1g<[R['5R_'5%m=R`'T%j=R=P<1Z<2P51Z<8CYRa%l<Rb%k<RcPcPc1U<BRB1U<LRLPcP?P@P@PAP;J05D>&04@RdPc1U<>R>=9cBPdA9c>LReCPCP202cARfP6P2g00V2Rgg00VRRh+001~62=}ghdg00W2=|<5C{Rhb6b7b8X1<X2<X3<W:AW25810581028[[^1<^2<^3<^:ZP6129:RZ,:;P9P;PFP8P5O6b53iW9P6O110E;RgPXPKPOP;PXPPPRP;PXPUPVP;10W;9@XJD6D6D69WXH1?6FPGP:12:;RX/0YC<X00,\03GP110E:R1PXPHPXPKPOP:PXPPPRP:PXPUPVP:10W:9@XJD6D6D6C<f9RX,?6PGP910ZYC<X00,\0AXg;HPKP;P;POPPP;P;PRPUP;P;PVPJP;P;PWGCD=DH1FX;3G9@F;P610E9RgPZPHPZPKPOP9PZPPPRP9PZPUPVP910W99@ZJD6D6D6C<10X:1::HPKP:P:POPPP:P:PRPUP:P:PVPJP:P:PWGCD=DH5e1R1f:RZ/F:Ri'K%B]R]#BRj#BRk#BRl#BRm#DRn/3_Ro%BmRm#DRp15^[Rq'3Rr%Bm#DRm%D]R]=dp^'3RsPsPsPs13nqRt15][Ru,3pRv%DjRj/5[Rw,3mRxPx15]\,3pRyPxPo13pwRz%DkRk=dp^,3mR{P{PyP{13nuR{Pr13muRuAdpj],3mR|P|P|PoPrPsPsPsPsPt13p_15k\,3pR}P}Py13mqR~PoPvPxPx15nwPrPxPxP}PxPsPsPsPsPrPoPxPyPxPxPvPt15^\,3pR^PyP^P}%Dl/5[,3pPoP|P|P|PuPrP{PsPsPsPsPrPoP~15j\,3p15k[Rk,5mPzPtPxPyPxPxPvPoPxPuPxPx13nk=br`D1D1D1'T5byD1D1D1D1D1D1D1D1D1'T9byxD1D1D1D1D1D1D1D1D1D1P=PaPbPcPcPcPLP>1OLBRa9Lc>D>PdPcPcPc%;ERyPLPcPcPa%;HRx%;KRr99ca%;NRN,OrRk=9cL5Nc%;PRn99ca%;I%;Q'ORQ=9cL5Nc%;D%;T5z<RT99ca1OTNRD=9cL5Nc%;JRI99ca1OINRN=9cL5Nc5]c5]c5]cD>D>PdPcPcPyP>ALc>xD>PcP?P@P@PAPcPcPrP>ALc>kD>PcPcPnP>ALc>QD>PcPcPTP>ALc>DD>PcPcPIP>ALc>ND>5Nc5Nc5NcEy5]cCPCPPfPhb6b7b8X1<X2<X3<P5P6P61252CR10E2RN1228RIPHPIPKPOP2PIPPPRP2PIPUPVP210W29@IJD6D6D6C<1:2HPKP2P2POPPP2P2PRPUP2P2PVPJP2P2PWGCD=D=g00WP[5eN[[^1<^2<^3<P6PFPXP9P;P5O5b59i1i3cW9P6O11?6ZPGPFAIF9YC<X00,\0P3P0f;R3,?6PGPXAIXFYC<X00AXg9HPKP9P9POPPP9P9PRPUP9P9PVPJP9P9PWGCD=DH1F393G9@Z9P6f=,?6PGP3AI3ZYC<P4f>Rg,?5%J5Rif<R1%M5,2i9I133WPEP3P3PHCRPKP3P3POPPP3P3PRPUP3P3PVPJP3P3PWGCD=DHf?R1/F33G9@g3P6f@R3,?8%J7Ri%M7,2i9I1g7W1P4%J;R4/03%M;,249I31fBR3PEP1P1PHCRPKP1P1POPPP1P1PRPUP1P1PVPJP1P1PWGCD=DHfCR4/F13G7@1P6%J9/03%JF%MF'29I43fERF/0310E31:3HPKP3P3POPPP3P3PRPUP3P3PVPJP3P3PWGCD=DH3eRWfFRJ/F3RV'KP0fG,?6PGP41:4YC<X00PX1?XJ%JXRJP3P3%MX,2JCRP;15]q15j_/T`'TP=P<P<1Z<7P2%w<R=CYP5P<1Z<;P8P=CYCYPbPcPcPc1U<MRMPL1U<S,OMRS9LcLD>PdPc1O>BRB99cSPdPcA9c>MPdPcPePc1vLBCuCPCPCPPfPhb6b7b8X1<X2<X3<X;<X<<12879XC512589I7;102;P8P7P7128;CR[[[^1<^2<^3<^;<^<<P6fDPF%MZP4%JZfAP5P2O8b5CtCs9cWV3cW?W>P5P6O2n2001000010121000000W4WBP5P6O2n2001000010121000000W4X00P5P6O2n2001000010121100000W4P6O1n210100001021100011000W4P6O1n201100001021100011000Ar:;2eWAW@XE<XF<X=<XD<WCo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition block_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= ATOP /\ (A + n <= 0x10000 \/ 0x1b000 <= A).

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition client_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  ATOP <= fst iv
  \/ (0x19000 <= fst iv /\ snd iv <= 0x1b000 /\ (snd iv <= MLOCK \/ MLOCK + 4 <= fst iv) /\ (snd iv <= LIBC \/ CTX + 928 <= fst iv)
      /\ (snd iv <= ERRNO \/ ERRNO + 4 <= fst iv) /\ (snd iv <= MEDTAB \/ MEDTAB + 4 <= fst iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bptr_eqb (p q : bptr) : bool :=
  aptr_eqb (fst p) (fst q) && Z.eqb (snd p) (snd q).
(* [comment removed for export] *)
Definition lb_remove (p : bptr) (LB : list block) : list block :=
  filter (fun b => negb (bptr_eqb (blk_id b) p)) LB.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


End CANSEC1.
