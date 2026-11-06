(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptExecB.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptStderr O23LeptBase O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyT O23LeptMbc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23LeptCloseSpec () := "C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z8abs_specC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3absC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3oppI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z3minK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega5Tauto8GFormula09C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib3O23@O23LeptCloseSpec;RK_csc_selsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common9Leptonica9LeptArith6wpl_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica:LeptRoomBL7RB_pixTC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib3O23@O23LeptCloseSpec6RB_cscC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib6Common9Leptonica:LeptRoomPC;RB_cmapcopyC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition CSC_STACK : Z := 112 + 48 + 4112 + 16.

(* [comment removed for export] *)
Definition RK_csc_sels (vs : Z) : Z := if (vs =? 1)%Z then 6 else 16.
Definition RK_csc (vs : Z) : Z := RK_csc_sels vs + 4 * RK_pixcopy + RK_cmapcopy.
Definition RB_csc (vs w h cm : Z) : Z :=
  RK_csc_sels vs * 2 ^ 17
  + 3 * (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cm)
  + (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)
  + RB_cmapT cm.

Section CloseSpec.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition csc_cm (C : lctx) (Ar A : AS) (m : word -> option byte) (pix datas cm : Z) (cv : cmapv) : Prop :=
  cm = 0%Z \/
  (cm <> 0%Z /\ CMAPat m cm cv /\ cmap_ok cv /\
   live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
   live Ar (Z_to_bv 64 cm) = None /\ live Ar (Z_to_bv 64 (c_arr cv)) = None /\
   live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
   cm <> c_arr cv /\ cm <> pix /\ cm <> datas /\ c_arr cv <> pix /\ c_arr cv <> datas).

Definition pix1_at (C : lctx) (Ar A : AS) (m : word -> option byte) (pix w h cm datas : Z) (cv : cmapv) : Prop :=
  PIXat m pix (hdv w h 1 cm datas) /\
  live A (Z_to_bv 64 pix) = Some 64%Z /\ live Ar (Z_to_bv 64 pix) = None /\ live (c_A0 C) (Z_to_bv 64 pix) = None /\
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z /\ live Ar (Z_to_bv 64 datas) = None /\
  live (c_A0 C) (Z_to_bv 64 datas) = None /\
  csc_cm C Ar A m pix datas cm cv.

(* [comment removed for export] *)
Definition csc_live (A A' : AS) (cm : Z) (cv : cmapv) (cm' : Z) (cv' : cmapv) : Prop :=
  (cm = 0%Z /\ cm' = 0%Z /\ forall q, live A' q = live A q)
  \/ (cm <> 0%Z /\ cm' <> 0%Z /\
      c_d cv' = c_d cv /\ c_nalloc cv' = c_nalloc cv /\ c_n cv' = c_n cv /\
      (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 (c_arr cv) -> q <> Z_to_bv 64 cm' -> q <> Z_to_bv 64 (c_arr cv') ->
                 live A' q = live A q) /\
      (forall q, (q = Z_to_bv 64 cm \/ q = Z_to_bv 64 (c_arr cv)) -> q <> Z_to_bv 64 cm' -> q <> Z_to_bv 64 (c_arr cv') ->
                 live A' q = None) /\
      (forall q k, live A q = Some k -> q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 (c_arr cv) -> live A' q = Some k))
  \/ (cm <> 0%Z /\ cm' = 0%Z /\
      (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 (c_arr cv) -> live A' q = live A q) /\
      live A' (Z_to_bv 64 cm) = None /\ live A' (Z_to_bv 64 (c_arr cv)) = None).

(* [comment removed for export] *)
Definition csc_K (fr : bvmap 5 word) C Ar A m md regs (s pix1 vs w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall (fr' : bvmap 5 word) (cs' : bv 32) A' m' vm' regs' (cm' : Z) (cv' : cmapv),
     frm_zero cs' -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 pix1 ->
     sub_live Ar A' -> POSTM C Ar s m m' ->
     pix1_at C Ar A' m' pix1 w h cm' datas cv' -> csc_live A A' cm cv cm' cv' ->
     aroom A' vm' (kR - RK_csc vs) (bR - RB_csc vs w h cm) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S.

Definition pixCloseSafeCompBrick_inplace_contract : Prop :=
  forall (fr : bvmap 5 word) (cs : bv 32) C Ar A m md regs (s pix1 hs vs w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> MBC C -> W C A m md -> sub_live Ar A -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x123d20 ->
  getr regs 10 = Z_to_bv 64 pix1 -> getr regs 11 = Z_to_bv 64 pix1 -> getr regs 12 = Z_to_bv 64 hs -> getr regs 13 = Z_to_bv 64 vs ->
  ((hs = 1 /\ vs = 8) \/ (hs = 30 /\ vs = 1))%Z ->
  pix1_at C Ar A m pix1 w h cm datas cv -> pix1 <> datas -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_csc vs <= kR)%Z -> (RB_csc vs w h cm <= bR)%Z ->
  csc_K fr C Ar A m md regs s pix1 vs w h cm datas cv ret S kR bR ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0x91ff4 : word) m al_rom) md) S.


(* [comment removed for export] *)
Lemma RB_csc_cm : forall vs w h cm cm', (cm = 0 <-> cm' = 0)%Z -> RB_csc vs w h cm' = RB_csc vs w h cm.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptCloseSpec ()) ["CloseSpec"] "h04__x1h14__x2h24__x3h34__x4h44__x5h54__x6h61Eh71Hh83H17h93H18h:3H19h;3H20h<7__arithh=4__ffh>8__varmaph?5__with@2cmhA3cm'hB1hhC2vshD1whE1zhF3z17hG3z18hH3z19hI3z20p;2p;1p;4p;7p;3p;6p;8g0000j2^Tg000Ij1XTg000kj2=Tg001Gj1BTg001dj2ATg002@j1TTg002]j2;Tg0037j1>Tg003Uj2aTg0047j2?Tg004Tj1`Tg0052j2sTg005Sj17Tg0062j2[Tg006[j1gTg007;j1eTg007[j2RTg0089j4QTg008Wj1dTg0095j1cTg009Sj1bTg00:>j2WTg00:aj1PTg00;Fj1:Tg00;kj2<Tg00<Nj1_Tg00=0j2VTg00=Sj7rTg00>7j2qTg00>Yj2]Tg00?3j2pTg00?_j3ITg00@9j3oTg00@Xj4nTg00AJj1\Tg00BOj2lTg00Blj23Tg00CIj22Tg00Cfj2ETg00Dlj1FTg00F4j6kTg00FRj4ZTg00GRj2jTg00Gmj3iTg00HVj3GTg00I?j2YTg00Ikj3JTg00JKj4NTg00K6j7OTg00KZj7hTg00L>j7mTg00Lbj8fTg00MFR0f0R1g00MdR23Ip=Hf2R3f1R4=I01'jp=51[01p=8Ai041p=@AG041p=4AG041g00NBR5'Yp=1AG0419G03p=61Y15p=Sg00NnR5f4R6f3R7AJ5419J535J53Jp=0P0P4g00OZP1CNp=Df5R8g00PAR9g00P`R:P:g00Q@R;P6P9P:P:P;P7g00Q`R<FOP3P9P:P:P;P0P4g00R@R=P1CNP<FOFhp=9P0P4g00RgP1CNp=LP3P9P:P:P;P4P1Fmp=MP3P9P:P:P;P0P4P=P1CNP<FOp=UP7P9P:P:P;P3P4P1Gfp=CAI041p=K%H4%H1'^%X31=23%B3R<;531A32%T375<';%B7R=P0g00SNR>#>R?/a1R@1A?11??1RA;5?1=1??5A1';RA1??4RBP0%X81=28RC%B8RD;581A82RE%T8RF75D';f6RD#BP0P@PAPBP0%`>,s0RBg00T3RA#7R@#7RG#7RH#7RI#7RJ#7RK#7RL#7RM#7RN#8RO'@RP%8@R@%8LRL,@BRQ%8KRK%8JRJ1[0ARA'4RR'4RS'4RT'4'1RU%7N#8RN1@BJRV%8GRG%8HRH,@BRW/4ARX'456ORY'1RZPU%8IRI/4X96OV,1NRXPX%8MRM/4T,1PRTPZPTPT1@BGRT,1MRMPUA6WGA96OVR[,1NR\11@TR]PUP]P]A6OVARU,1NR^A6@QR,1PR_PMPM1@B@RB,1GR`P`PMPMP]P]P^P_11IBRIPIP^14@AR_,4JRa,4Q,1PRbP`P`14H@,1KR@P^P^PbA6QKa,1PRaP\14BA96WG96LV,1OA6HT_96QJ,1PP`PZPaPZPIPXPIPI%SYRY11PSRSP`P`14LG,1NRNPN%S[R[PS11PRRR%SURUP@P@P`P`PRPUPIPIPRPUP]P]PMPMP`P`PMPMPRPUP]P]P]P]P[PSPMPMP`P`PMPMP]P]PYPS%g5D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0%e5P0P01R06P31R0DCQP4P01R08P7%d0CQCQ%c0%b0R5P5P51W0?RS%P>RY#:,<0R]'DP51<0>RMPSE9P5P51L]SP5PMP]E95M5%_:R`P5P5P51W02R[%:>R>#:RU,<0RR'LP5P]PRE9P5P51DR[P5P]1V0RE95M5P`P5P5P5%P>,<0R],DSP51<0>RIPSE9P5P51L]SP5PIP]E95M5P`P5P5P51<0YRS,L[P5P]PSE9P5P51DS[P5P]1V0SE95M5P`P5P5P9P:P:P;AU5S[AU5R[FrP`AU5MICCCCCCCCCC1q5;P1P3g00TRR5g00U2R;']1p13=I5;dAo024Cnb=b>b?X00X10X20X30X40X501A?8?51?1=8??518';1=26?5D61A62%T675D';1A?D?57?1=D??57D';f7R2=5C8A5E2F';%HD%H2'^1K8D[[[[[^00^10^20^30^40^50P1P7P2f:f;P8P4P3P6PDf8f9O;b<bIb;bHb:bGb9bFb8%B4,??1??<R<'KP01??=R=%\2%>>%:UR>#P#>'lR2'3RF%>YRY%>URU%:>#:#:#>R>,2D/E?128>RE'3'3#FRCg00URR;/31R5'2'3'21ED?/38,3U#FRI/25'2/25%B6,??,3;R5,2C,3Y,2F12I5'2/25'KXE0%\D/321EE?126>'3,3U#F13;=R;'2,3Y'21E8?/36,3U#F/2;'2/2;,]0P<P1Ekb6P8P6P7P4CZP8P6P7P3CZ'KeW7XA0X@0XB0XD0XC0o"). Qed.

End CloseSpec.
