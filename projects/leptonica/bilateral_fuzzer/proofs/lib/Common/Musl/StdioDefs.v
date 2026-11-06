(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Export ExitBase.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_StdioDefs () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00i69OSSVerify5KrLib6Common4Musl9StdioDefs7sw_post00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc69OSSVerify5KrLib6Common4Musl9StdioDefs9swp_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc69OSSVerify5KrLib6Common4Musl9StdioDefs9swp_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common4Musl9StdioDefs8foe_post00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl9StdioDefs9foe_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl9StdioDefs9foe_growsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section G.
  Context {RL : Reloc}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
  swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
  swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

(* [comment removed for export] *)
Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
  rdn RSEGS mem (rl dA_1e3b8 0x1e3e0) 8%nat = Some (word_to_le_bytes 8 (rl dA_2f848 0x2f848))
  /\ rdn RSEGS mem (rl dA_2f848 0x2f848) 8%nat = Some (word_to_le_bytes 8 can).

(* [comment removed for export] *)
Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
       (mem' : word -> option byte) : Prop := {
  swp_agree : forall x : word,
      ~ (su - 112 <= bv_unsigned x < su)%Z ->
      ~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
      ~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
      mem' x = mem x;
  swp_grows : mem_grows mem mem';
  swp_wend  : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
  swp_wpos  : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.

(* [comment removed for export] *)
Lemma sw_post_rdn : forall mem su f bufp bufsz mem' (a : word) n bs,
  sw_post mem su f bufp bufsz mem' ->
  rdn RSEGS mem a n = Some bs ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= su - 112 \/ su <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 32 \/ f + 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 56 \/ f + 64 <= bv_unsigned a)%Z ->
  rdn RSEGS mem' a n = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_StdioDefs ()) ["G"] "h04__x1h14__x2h24__x3h34__x4h47__arithh54__ffh66__sat4h76__sat5h88__varmaph95__with:4cstrh;2Hah<2D1h=2D2h>2D3h?1Hh@3HnwhA2HxhB1PhC1ahD2bshE4bufphF5bufszhG1fhH3memhI4mem'hJ1nhK1ohL2suhM1xp;1p;6p;4p;2p;3p;;p;7p;8g0000j10Tg000Uj1UTg0013j1PTg001Vj1LTg0028j1TTg002Xj6gTg003\j1_Tg004[j4GTg005Sj2OTg0065j3FTg006Oj27Tg0079j18Tg007Yj1;Tg0087j2mTg008Tj1STg0099j2HTg009Vj21Tg00:2j2<Tg00:Lj24Tg00:ij25Tg00;Ej2:Tg00;`j1\Tg00<Ej2[Tg00<mj3ZTg00=Qj1ATg00>0j2=Tg00>Yj3ETg00?Bj2MTg00?nj1YTg00@Nj3BTg00@nj2KTg00ALj1XTg00Ajj4NTg00BHj1WTg00Bfj1VTg00CQj2CTg00D4j3>Tg00DWj1lTg00E9j29Tg00E\j3kTg00F?j2jTg00Faj2fTg00G;j2eTg00Ggj3dTg00HFj4cTg00I8l;bTg00J<j7aTg00K8j6`Tg00KVj4QTg00LAj7RTg00Lej7^Tg00MIj7hTg00Mmj6iTg00NQj8]Tf2R0f1R1'4f0R2'1p=2P0g00O5R3g00OTR4P4g00P4R5g00PTR6P1g00Q2P2CQg00QYR7FRp=3P6P1g00R9P2CQp=?P1P3P4P4P5P2P7FRp=DP0P3P4P4P5P1P2F^p=@P0P3P4P4P5P1P2Fhp=IP1P3P4P4P5P2Eip=Jf3R7P3P4P4P5P0P1P2G]p=6g00R`R3#0R8#0R9#0R:#0#0R;#0R<#UR=#PR>%U:#PR:#L[R?g00SE%T:R:f8R@f7RAf6RBf5RCf4RDP7Eg%L:REp,2RL#_RFf9RGP7P0CG1O:13F17=D%87%;8RH%;<R<'mRI3217=CRJ%8Df:RK%S3RL#S#0#0#0RM#0#;RN'H3211KJ'<17=BRO%8C%;;R;,4K32%0L#0#0#0#;RP=2KO'<17=ARO%8Bf;RK%;MRM'432A2K<O'<PEPFf>ROP@PACG1O:A9FE2XKEPDPFPGP@PACGPFPAPGPOP@P717=GRF17=2RE'1%8@,4F,5E':f@f?POf=REf<PKPAP1%\GRKg00SdRF%8G'1RG1[H<R:15FH11F<15FI[[RQ11FHRRg00TBRSAZH<1UW;RH11FI\S^;RRRg00T^RSg00UJRI#ART#ARU#ARV,=61=6URU1=6T5E65E6g00UiRT'MRW%AV,=61=6I9E6U5E6/MTRT%YSRU5BS3BRI%TSRVP6P61K6DP0%X6CNP11K67CNRX%W6RY%V6RZ1C6LRL1C68R853Z1C69R99>6LR[,?8,DZ5@ZR\%l4R4PZ1C63R3196N5k6R]93Z[A3Z3L5IZP4A3Z]81?83,DZ5@Z,JZC6C61jZ5R5P2P0g00VUR]g00W5R^'f1e20=F]^dAd6F1CcR^b5b8b9X06X16X26X3611011407,51':R]147DR_1H1N'11117'<1H0N/171570':g00WURN[[[^06^16^26^36P2%8ERE17=OROPJfCPDP@O6b4b6b7b:PKPGP:PQPHPRABSWU9BSTPVPXPYPZ196F=3Z9P4PZP\P4PZ196;9>63R993Z[196P9>63RT=3ZL5IZP4A3Z981?8T,DZ5@Z,JZC6C6C6P5P^b5b8b9X06X16X26X3611F71170150_':140;92DCA20PD'<A27;D147P,5D':PN[[[[^06^16^26^36P2PEPOPJfBRPP7PDPAO7b4b6b7b:PKPGP:PQPHPRPIPVPXPYPZP\P4PZ196M9>63R\93Z[196<9>63R3=3ZL5IZP4A3Z\81?83,DZ5@Z,JZC6C6P5P^b5b8b9X06X16X26X36141M,1_A21<7'<A20M7140<,57':PN[[\]^06^16^26^36P2PEPOPJPPPDPBO6b4b6b7b:M;bWAXM>FaE`W>W=W<W@W?WBWDWJXC>XI?XF>XE>XG6XL6WHo"). Qed.

Lemma sw_post_store_ok : forall mem su f bufp bufsz mem' (a : word) n,
  sw_post mem su f bufp bufsz mem' ->
  store_ok RSEGS mem a n = true -> store_ok RSEGS mem' a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_StdioDefs ()) ["G"] "h01Hh11Ph21ah34bufph45bufszh51fh63memh74mem'h81nh92sup;1p;6p;4p;3p;7g0000j10Tg000Uj12Tg0013j11Tg001Vj13Tg002Xj69Tg003\j18Tg00X2j47Tg0065j34Tg00Y2j75Tg00Z6j76Tg00R`#0#0#0R0#0#0#0#2#1R1%20#1#3[R0g00PTR2g00SEf7R3f6R4f5R5f4R6f3R7f2R8E9g00VUp,2RL#8R9f8R:P8f1R;C7g00W534P9P8f9R8P6P7P8P:P3P4P5P6P;F5f0F6W0W1W8X21X70X41X31X52W9W6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_CALL_TRAMP : word := rl dE___funcs_on_exit 0x15940.      (* [comment removed for export] *)
Definition A_EXIT_GUARD : word := rl dE_target_run 0x135f8.          (* [comment removed for export] *)
Definition A_IN_CALLBACK : word := rl dA_1f630 0x2f684.

Inductive foe_variant := FOE_none | FOE_one.

(* [comment removed for export] *)
Definition atexit_state (mem : word -> option byte) (v : foe_variant) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x2f620 + dA_2f840 + 4)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))          (* [comment removed for export] *)
  /\ match v with
     | FOE_none =>                                                                                     (* [comment removed for export] *)
         rdn RSEGS mem (Z_to_bv 64 (0x2f620 + dA_2f840 + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
     | FOE_one =>                                                                                      (* [comment removed for export] *)
         rdn RSEGS mem (Z_to_bv 64 (0x2f620 + dA_2f840 + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x2f620 + dA_2f840 + 24)))
         /\ rdn RSEGS mem (Z_to_bv 64 (0x2f620 + dA_2f840 + 8)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
         /\ rdn RSEGS mem (Z_to_bv 64 (0x2f620 + dA_2f840 + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 (0x2f620 + dA_2f840 + 32)) 8%nat = Some (word_to_le_bytes 8 A_CALL_TRAMP)
         /\ rdn RSEGS mem (Z_to_bv 64 (0x2f620 + dA_2f840 + 288)) 8%nat = Some (word_to_le_bytes 8 A_EXIT_GUARD)
         /\ rdn RSEGS mem A_IN_CALLBACK 1%nat = Some [Z_to_bv 8 0]
     end.

(* [comment removed for export] *)
Record foe_post (mem : word -> option byte) (su : Z) (mem' : word -> option byte) : Prop := {
  foe_agree : forall x : word,
      ~ (su - 64 <= bv_unsigned x < su - 16)%Z ->
      ~ (0x2f620 + dA_2f840 <= bv_unsigned x < 0x2f620 + dA_2f840 + 24)%Z ->
      mem' x = mem x;
  foe_grows : mem_grows mem mem'
}.

Lemma foe_post_rdn : forall mem su mem' (a : word) n bs,
  foe_post mem su mem' ->
  rdn RSEGS mem a n = Some bs ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= su - 64 \/ su - 16 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x2f620 + dA_2f840 \/ 0x2f620 + dA_2f840 + 24 <= bv_unsigned a)%Z ->
  rdn RSEGS mem' a n = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_StdioDefs ()) ["G"] "h04__x1h14__x2h24__x3h34__x4h42Hah57__arithh64__ffh76__sat3h86__sat4h98__varmaph:5__with;4cstrh<2D1h=2D2h>1Hh?3Hnwh@2HxhA1PhB1ahC2bshD3memhE4mem'hF1nhG1ohH2suhI1xp;1p;3p;4p;2p;7p;6p;8g0000j12Tg000Uj1OTg0013j1KTg001Vj1UTg0028j1QTg00[7j3`Tg003\j1]Tg004[j4DTg005Sj2MTg0065j3FTg006Oj28Tg0079j19Tg00:Lj23Tg007Yj1<Tg0087j2mTg009Vj20Tg0099j26Tg00:2j2BTg008Tj11Tg00\<j2^Tg00:ij27Tg00;Ej2@Tg00;`j1\Tg00<Ej2[Tg00<mj3ZTg00=Qj1=Tg00>0j2;Tg00>Yj3?Tg00?Bj2NTg00?nj1YTg00@Nj3JTg00@nj2LTg00ALj1XTg00Ajj4ITg00BHj1WTg00Bfj1VTg00CQj2>Tg00D4j3HTg00DWj1nTg00E9j2CTg00E\j3TTg00F?j2lTg00Faj2kTg00G;j2jTg00Ggj3eTg00HFj4dTg00]<j7bTg00J<j7aTg00K8j6cTg00KVj4PTg00LAj7_Tg00Lej7fTg00MIj7gTg00Mmj6hTg00NQj8iTf0R0#2#2p=:g00PTR1f1R2g00Q2P0CPp=5P2g00O5R3g00OTR4P4g00P4R5P0g00QYF_p=4P1P2g00R9P0CPp=Gf2R6P3P4P4P5P2P0Ffp=EP6P3P4P4P5P2P0Fgp=RP2P3P4P4P5P0Ehp=Sf3R7P3P4P4P5P6P2P0Gip=Ag00R`R3#2R8#2R9#2R:#2R;#:R<#OR=#KR>%O:#KR:#U[R?g00SE%Q:R:f5R@f4RA;`7%U:RBp,2RLRC#]RDf6REP7P6CD1M:23F18=A%97'3%<8RF%<<R<'mRG'018=@RH%9A'3f7RI/6<'0%<;R;,6I/0H'B18=ERJ%9@'3%18#1#1#1#2#1#1#2#:#1#2#:#:#<R@%19#1#1#2#1#:#1#1#2,^CRC'3RK'0%13RL#2#:#<RM,3K/0J'BPBPDf:RJPIPECD1M:E9FB0XGBP7PDf8RBPIPECDPDPEPBPJPIP618=BRD18=0R:'0%9I,3D,7:'@f<R:f;PJPEP2%\BRJg00SdRD%9B'0RB1[F<RK17DF10D<17DG[[RN10DFROg00TBRPAZF<2UW4RF10DG\P^4OROg00T^RPg00UJRG#=RQ#=RR#=RS,;11;1RRR1;1Q5?15?1g00UiRQ'N%=S,;11;1G9?1R5?1/NQ%YP5JP3JRQ%QPRPP1P11L1AP6%X1CIP21L17CIRR%W1RG%V1RS1>1LRL1>18R8'5,4S1>199H1LR9,G8,4S5ESRT%n4R4PS1>13R31C1<5T1RU,59,4S1C1;9T13RV/5L,4S5RSP415U8,4S1G8V,4S5ES,SSCACA1lS5R5P0P6g00VURVg00W5RU'k1j06=FVUdAe1D2CdRDb6b9b:X01X11X21X3110621367,72'@RU137ARV162<'0162;/07'B166</07166;,77'@g00WUR;[[[^01^11^21^31P0%9:R:f=,8=R=PHf?PAPIO6b5b7b8b;PJPBPKPNPFPOPQPPPRPGPSPTP4PS1C1@=H13R3,59,4S1C1M9H13R9/5L,4S5RSP41538,4S1G89,4S5ES,SSCACAP5PDb6b9b:X01X11X21X3113@2R2,0V132M/07'B13@6R@/0713@M,77'@P;[[\U^01^11^21^31P0P:P=PHPCPAPEO6b5b7b8b;FbW@XI>FaEcW=W<W?W>WAWCWFXB>XE?XH1WDo"). Qed.

Lemma foe_post_store_ok : forall mem su mem' (a : word) n,
  foe_post mem su mem' -> store_ok RSEGS mem a n = true -> store_ok RSEGS mem' a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_StdioDefs ()) ["G"] "h01Hh11Ph21ah33memh44mem'h51nh62sup;1p;3p;4p;7g0000j10Tg000Uj12Tg0013j11Tg001Vj13Tg00[7j39Tg003\j18Tg00X2j47Tg0065j34Tg00^@j45Tg00Z6j76Tg00R`#0#0#0R0#0#0#0#2#1R1%20#1#3[R0g00PTg00SEf4R2f3R3f2R439g00VUp,2RL#8R5f5R6P4f1R7C7g00W534P5P4f6R4P2P3P4P6P2P7C5f0F6W0W1W5X21X40W6W3o"). Qed.

(* [comment removed for export] *)
Definition funcs_on_exit_spec {fx : FPState} : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (rom : word -> option byte) (su : Z) (v : foe_variant),
    rom = seg_rom RSEGS ->
    getr regs 2 = Z_to_bv 64 (su - 16) ->
    getr regs 1 = rl dF_15800 0x15864 ->
    (4294967296 <= su - 144)%Z -> (su <= 0x800000000000)%Z ->
    store_ok RSEGS mem (Z_to_bv 64 (su - 144)) 144%nat = true ->
    rdn RSEGS mem (rl dA_2f848 0x2f86b) 1%nat = Some [Z_to_bv 8 0] ->
    atexit_state mem v ->
    exists regs' mem',
      msteps RSEGS (mkst regs (rl dE___funcs_on_exit 0x157b0) mem rom)
                   (mkst regs' (rl dF_15800 0x15864) mem' rom)
      /\ getr regs' 2 = Z_to_bv 64 (su - 16)
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3
      /\ foe_post mem su mem'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record exit_common (regs : bvmap 5 word) (mem : word -> option byte)
       (sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
  ec_sp   : getr regs 2 = sp;
  ec_tp   : getr regs 4 = tp;
  ec_a0   : getr regs 10 = code;
  ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  ec_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  ec_tplo : (168 <= bv_unsigned tp)%Z;
  ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
  ec_tid  : (0 < tid < 2147483648)%Z;
  (* [comment removed for export] *)
  ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  (* [comment removed for export] *)
  ec_lock : rdn RSEGS mem (rl dA_2f840 0x2f840) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (rl dA_1e3b8 0x1e3e8) 8%nat = Some (word_to_le_bytes 8 (rl dA_1e348 0x1e358));
  ec_fs   : rdn RSEGS mem (rl dA_1e3b8 0x1e3f0) 8%nat = Some (word_to_le_bytes 8 (rl dA_1e348 0x1e350));
  ec_fa   : rdn RSEGS mem (rl dA_1e348 0x1e350) 8%nat = Some (word_to_le_bytes 8 (rl dF_13140 0x13140));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (rl dA_1f630 0x1f678) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (rl dA_1e368 0x1e390) 8%nat = Some (word_to_le_bytes 8 (rl dE___cxa_finalize 0x13198));
  ec_g2   : rdn RSEGS mem (rl dA_1e368 0x1e398) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_dso  : exists dso : word, rdn RSEGS mem (rl dA_1f3f8 0x1f3f8) 8%nat = Some (word_to_le_bytes 8 dso);
  (* [comment removed for export] *)
  ec_atexit : exists v : foe_variant, atexit_state mem v;
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem (0x1f440 + dA_1f440) wp2 rp2
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 72)) 8%nat = Some (word_to_le_bytes 8 (rl dF_178c0 0x178c0));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x1f530 + dA_1f440 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x2f850 + dA_2f848 <= wb < wp /\ wp <= rl_img_hi)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= 2 ^ 30)%Z;
  sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.

(* [comment removed for export] *)
Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
           (code : word) (pending : list byte) : Prop :=
  exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
    exit_common regs mem sp tp code tid wp2 rp2
    /\ m_halted model = None /\ m_vm_lazy model = []
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem (0x1f530 + dA_1f440) wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).

End G.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
