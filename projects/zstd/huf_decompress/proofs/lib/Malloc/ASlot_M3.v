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
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_I ASlot_M0.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv4.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_M3 () := "K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma halve_big_pos F : forall cnt sz, 1 <= cnt -> 0 <= sz < 2^18 -> 1 <= halve_big F cnt sz.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_M3 ()) ["CANSEC1"] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with51Fh64__x2h73cnth82szh92H1h:2Hah;2Hch<2Hsh=4__p1h>6__sat1h?6__sat6h@4__x3hA2GThB1HhC2H0hD2H2hE2H3hF2H4hG2IHhH2LEhI6__sat0hJ6__sat5hK1bi001bhL2b0hM1qhN1rhO1zp;1p;2p;3p;4p;5p;6p;7p;8g0000j17Tg000Nj21Tg000jj10Tg001Oj15Tg0024j2UTg002Qj23Tg002mj2<Tg003Hj3FTg004Bj1`Tg004bj1^Tg005Bj2HTg005`j1XTg006>j1~Tg006ij2DTg007Lj2NTg007oj1xTg008Qj2lTg0093j2PTg009Mj2hTg00:9j3=Tg00:Sj3eTg00;2j4dTg00;dj29Tg00<Aj2_Tg00<cj2QTg00=@R0j3]Tg00=dj2\Tg00>Dj2ETg00>aj2[Tg00?Ij3ZTg00?mj2YTg00@Nj2@Tg00A7j2OTg00AXj4WTg00B9j3}Tg00BZj2|Tg00CCj2?Tg00Clj1>Tg00DKj2VTg00E7j3TTg00EWj1yTg00F5j4ITg00FSj5wTg00G7j1uTg00GUj3pTg00H8j3LTg00H[j2kTg00I<j1jTg00IUj2CTg00J5j2RTg00JRj2iTg00K9j2mTg00K`j2nTg00LFj2oTg00Llj6gTg00MPj4GTg00N;j6fTg00N_j3qTg00OBj3rTg00Okj6sTg00PIj4tTg00Pjj7STg00QNj8vTg00R2j3cTg00R[j3bTg00SDj7zTg00ShR1f0R2'1p=8f2R3g00TFR4g00TeR5P5g00UER6g00UeR7f1R8g00VCP2CGg00VjR9FSp=6f3R:P4P5P5P6P3P8P2Gvp=4%02#0p=M%02#0#0#0p=a%02#0#0#0#0#0#0#0p=AAc782p=2%52#5#5#5p=;%52#5p={Ab782p=:P7P8g00WJP2CGp=JP8P4P5P5P6P2P9FSp=BP3P4P5P5P6P8P2Fzp=Kg00X1R9g00XPR;#7R</18R=%88%0;R>#7R?%0>R@#5#0RA#7RB'URC,38'<RDf4RE?F:3,1<[[^87^77RFX59g00Y5RG#`RH%^GRI1H78RJ%X7RK%~7RL1D7<RM1N7;RN56LRO%x5RPPOC41lL6RQP2P3g00YaRRg00ZARS'P1h23==RSdAe718CdRSb2b3b4X07RT11<2RUP=[^07RVP2PEP3O2b1g00ZaRW?F:3,1<eX<DX;=X87X77%M@RX#a#ARY#7RZg00[@'9R[193:R\'_11[\13\[1Q[\3]19:E,Q[PRP0f5R0,9ER\,1[13\[PRP7P8f9RRf7R\/\<R]f6R^3FP\n0100000020000,1<P8190^R_,1[f8R`P]P^P71U?<,E\PUXO71[?BRU131?Ra%8B131C[Rb[Rc%8?Rdg00\5ReAZ?B8UW:RB%8C\eRe^:dRfP8g00\Q1Y1?'PPaeRgO1RhPb%MY#7,@7RYP71O7<P;1O71CW9}7;,|71?7WRi'2'2%5;#0#A#A#5R;#7,@7%>WRW#>Rj#>Rk#>Rl#>,?7Rm1?7lRl'2'2%;>#;#;#;#0#5#{#;#;#;#;#7,@712mi'21?7kRk/2l,2Y1?7jRj,2k,2Y%M;#A#A#7,@71?7WRW,2j'2':':':':':g00]7R;'V=TGHPIP71H73P8%y7RYCIPKPLPL1D71Rl1D7?Rm56LPPPLPLP4P5P5P6DwPP%uA9p7mRA96LlC4C4PPPL1D7Z%7XRX,D75L71N7>R>=L7N56LPPPLA6Ll>1J>A,BL5KLPPPLPOPPA6LmNC4C4C4C4PQPSb2b3b4X07X67Pe\d19ZX1938'1%8:13:C'<11<:RX11?E[[[[^07^67P2f:RZf;RdP3PEP`PRO6b1b>bIb>11?\1k`?A=7?1Re#j1ER?,9?1CR?'R9=7R[1iR?1CZ?RR#813R?'<\a1mZ?13?11Cd?RZ,3?11Z1'<[1nd?f<RZ/E?==71\e1oZ?f=R1/C?==71\e1E1?P7f>/C?P7P0PgO1%82Rg132?'<PUPcPBPfPhPbp-0Rb1@7?/2i,:W,:j,:k/V;=TGHPIP7P71H7:P3PYCIP8PYCIPKPLPLP4P5P5P6P0Eg1N7@R@/Jm,BL5KLPPPLPLPLP4P5P5P6P7Pmg00]cR6PlCG,BLEfPPP7P>P6AL7mN=q7@CG,BLC4PPPLA6Lm>PPPOC4C4C4PQPSb2b3b4X07X67X@7W=133?,<:g00^J\e19?3/RE9=7:[11?:PX[[[^07^67^@7^=bP2%80P0fDP^PEPdPZO7b1b?bJb?b9bNbMbFbEbDb9bCbBP]PHPIPYPKA6LlMPQPSb2b3b4%8<P2b19r\<EsPHPIPJPKPLA6LlN1JNA,BL5KLRLPPPLC4PQPSb2b3b4X07132C,<gPD[^07P2P\P0O2b1O4WHP2O113_[PTPVP2P`P^O2b1WAP2O1n200210000000021100010000bLbK%>0?F:3,1<eX<DX;=X87X77XGFX59P2CtX59P2O1W5o"). Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.
End LEVEL.


End CANSEC1.
