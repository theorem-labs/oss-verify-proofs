(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W13 ASlot_W14 ASlot_I ASlot_M0 ASlot_M4P ASlot_M4 ASlot_M5P ASlot_M5D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RASlot_W2 HP_RASlot_W4 HP_RASlot_W13 HP_RASlot_W14 HP_RASlot_W18 HP_RASlot_W19 HP_RASlot_M0 HP_RASlot_M2 HP_RASlot_M5D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_M5S () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_I.ras_post2"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"].


Section RP_1. Context {hRP : run_params}.
#[using="hRP"] Lemma rgrp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. rceilb. (intros EG dd_H; ddestruct dd_H as (b & gh & Hb & Hf & Ho)). dexists b, gh. rewrite EG. auto. Qed.

#[using="Type"] Lemma rmrep_st_model stT sc cnt ai ml mt p (SC : 0 <= sc < 48) (CNT : 1 <= cnt <= 32)
      (REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml) (P0 : 0 <= snd p) m :
  rmrep (stFin stT sc cnt ai ml mt p) m -> rmrep (st_model stT sc cnt ai mt p) m.
Proof. rceilb.
  intros MR. eapply (rmrep_extW _ _ _ MR); try reflexivity.
  intros q. apply (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : rceil <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M5S ()) "Pst1,$0.Pidx,$1.Ps',$2.Pms',$3.P,(4.VhRP,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vo,Vm,Vst0,Vst,Vs,Vlo,Vsc,Vreq,R4.R3.R2.R1.)(5.VR,Vo,A2.Vk,R5.R4.R3.VQ,R2.)")
(* [comment removed for export] *).
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Local Ltac2 Set LiaOrc.tbl := fun () => "01V0@L10222171050.178L10709410338.311L10718172952.311L10771292899.243L11860823241.310L12651479035.310L14314876778.244L15032710663.310L16276704104.329L16337774845.310L17272821851.253L17352935383.244L17665811825.244L19082669660.305L19245567059.303L19444982572.244L2035146023.309 L2037357579.313 L20616311222.253L21603075004.274L21603075004.277L22123507426.270L22700200437.331L22704494580.326L24101743277.261L24448665443.316L25532691231.178L25825676587.150L26526893275.190L26735879336.321L26879324105.310L26918923434.261L27295541390.189L27295802899.188L27617988134.312L28705875682.151L28706286690.154L28720654419.190L28764220798.313L29163219501.261L30261587516.305L30686516359.196L30686518931.314L32051967300.313L33442364885.303L33442364885.309L33695688793.244L34463406065.316L35592087510.326L35969748569.311L36873205714.172L37541694237.261L40111252101.271L42626676250.244L42633168187.313L42633240268.303L42633240268.312L42633502412.311L44154907436.305L4509351693.322 L46578520388.275L47920118821.261L48656324308.316L50526621565.190L53090300186.244L53189684194.272L54276406284.314L5457607147.312 L5523554882.272 L56765630349.310L57445773353.270L57458322680.271L57622606836.331L57626703349.326L57877235140.315L59854431987.272L6022571149.305 L60681863623.311L6085192344.304 L61003338047.244L6165290959.176 L61822229209.150L6272674743.311 L63754872735.312L6428506379.326 L6432603914.331 L64848175850.317L64848595642.316L66148297143.203L67571066342.309L67573118597.196L68022400404.315L68026379571.305L7383459552.317 L8534397502.188 L8540670068.189 L8799929019.331 L8804287674.326 L907123884.310  L9278711168.235 L9725462813.261 L985489107.323  00000Q02903H04C05T07107l0930:H0;Z0<U0=Y0>Y0@F0AP0BU0Cj0E?0FC0GV0IY0Jm0M40OW0QW0S<0T10T?0Td0V80WB0YB0ZF0[J0]O0][0]g0^R0_c0aZ0cB0ck0eN0fk0h50i?0jJ0km0m;0nY0ne0om11312713Z14f16H18819`1:n1<91>91?I1@U1AP1BK1D51EO1FJ1GV1HT1IR1LF1Ni1PO1QJ1RQ1S[1Tj1V11VV1Vc1Wj1Y;1ZX1\g1^>1_N1`K1aU1b;1d=1f11gH1gn1hV1kQ1n51oC20<21Q22lS2sc3szc4cnt13st32g37strideg4STR3S2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3ENR4FIT34SZC11p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc2mm3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF61a2XaS2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3szc4cnt13st33idx2g32b32r37strideg1X4FITN1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc2mm3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF61a2Ha3rr02L03H0'S2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P2EP3stF3PF53PF63off1j1ES2sc3req3szc3FIT3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3szc4cnt13st33idx2g32b32r33C1R7strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3szc4cnt13st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3ENR4FIT34STR34SZC11p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF62rqS2sc3szc4cnt13st33idx2g32b32r37strideg1X4FITg1p3stT3TP03TTK3TPT3TPN1PS2sc3req2RQ3szc3FIT3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3req2RQ3szc3FIT3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc4cnt13st33idx2g32b32r33C1R7strideg1X1p3stT3TP03TTK3TPT3TPN1PS3hRP2sc3szc3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P1A1n2HA3lo'3hi'1HS2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3B304FITg4SZC11p2R43RI13RI22SK4XEND3stT3TP03TTK3TPT3TPN1P1A1n2H12H22H33lo'3hi'1HS3hRP2sp2lo2sc3szc2LO3st33idx2g32b32r37strideg1X3ASG4CLO'1p2R43stT3TP03TTK3TPT3TPN1PS2sc3szc4cnt13st33idx2g32b32r37strideg1X4FITg1p2R44XEND3stT3TP03TTK3TPT3TPN1P2EP3stF3PF53PF62rr3off2Ho3LR11D3B302SK3LR23req2RQ3FIT4SZC1S2sc3req2RQ3szc3FIT2mm4cnt13st33idx2g32b32r37strideg1X2GI3B304FITg4SZC11p2R43RI13RI22SK4XEND3stT3TP05TPEND3TTK3TPT3TPN1P2EP3stF3PF53PF63off2Ho4RI2r4RI1r3GRr2NH3NHCS3hRP2sc3req2RQ3szc3FIT3RCB4cnt13st33idx2g32b32r37strideg1X3B304FITg4SZC11p2R42RC3RI13RI22SK4XEND3stT3TP05TPEND3TTK3TPT3TPN1P2EPS2sc3szc4cnt13st33idx2g32b32r37strideg1X4FITg1p2R43stT3TP03TTK3TPT3TPN1P2EP3stF3PF53PF61a1j2Ea3Ea'2EJS2sc3req2RQ3szc3FIT4cnt13st32g37strideg3ENR4NFIT4SZC1S2sc4cnt14NFITS2sc3szc3st33idx2g32b32r37strideg1X1HS2sc3szc3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF62rr3off2HoS2sp2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S3hRP2sc3req2RQ3szc3FIT3RCB4cnt13st33idx2g32b32r37strideg1X3B304FITg4SZC11p2R42RC3RI13RI22SK4XEND3stT3TP05TPEND3TTK3TPT3TPN1P2EPS2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3ENR4FIT34SZC12R4S2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3ENR4FIT34SZC12R4S2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3B304FITg4SZC11p2R43RI13RI22SK4XEND3stT3TP05TPEND3TTK3TPT3TPN1P3stF3PF53PF61a1j2NAS2sc4cnt12JRS2sc4cnt12JRS2sc3szc4cnt13st33idx2g32b32r37strideg1X2JRS2sc3szc4cnt13st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF61j2HjS3hRP2sc3req2RQ3szc3FIT3RCB4cnt13st33idx2g32b32r37strideg1X3B304FITg4SZC11p2R42RC3RI13RI22SK4XEND3stT3TP03TTK3TPT3TPN1PS2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3ENR4FIT34SZC11p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc3st33idx2g32b32r37strideg1X2o'2HoS2sc3szc4cnt13st33idx2g32b32r37strideg1X3ENR4FIT34SZC11p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF62o'2HoS2st2sc3szc3st13st23st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF61H2H02H1S2sp2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sp2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc4cnt13st33idx2g32b32r33C1R7strideg1X3SZR1p2R43stT3TP03TTK3TPT3TPN1PS2sc3szc4cnt13st33idx2g32b32r37strideg1X3ENR4FIT34SZC11p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF62o'2HoS2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF63off2HxS2sc2SC3szc4cnt13st33idx2g32b32r37strideg1X2JR3SCJ1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF61a2XaS2sc4cnt12JRS3hRP2sc3szc2mm3st33idx2g32b32r37strideg1X2GC2GI1p3stT3TP03TTK3TPT3TPN1PS3hRP2lo2sc3szc3CLO3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3szc4cnt13st33idx2g32b32r33C1R7strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3szc4cnt13st33idx2g32b32r37strideg1X3SZR1p2R43stT3TP03TTK3TPT3TPN1P2EP3stF3PF53PF61a1j2Hj2Ea2LTS2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF61a2HaS2sc3szc4cnt13st33idx2g32b32r37strideg1X3ENR4FIT34SZC11p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF61a2HaS2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3ENR4FIT34SZC11p2R43stT3TP03TTK3TPT3TPN1P2EP3stF3PF53PF61a2XaS2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3ENR4FIT34SZC11p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF63off2HoS2sp2lo2sc3szc2LO3st33idx2g32b32r37strideg1X3ASG1p2R43stT3TP03TTK3TPT3TPN1PS3hRP2sc3req2RQ3szc3FIT3RCB4cnt13st33idx2g32b32r37strideg1X3B304FITg4SZC11p2R42RC3RI13RI22SK4XEND3stT3TP05TPEND3TTK3TPT3TPN1P2EPS2sc3szc4cnt13st33idx2g32b32r33C1R7strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3B304FITg4SZC12R42SK4XENDS2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3szc4cnt13st33idx2g32b32r37strideg1X3ENR4FIT31p2R43stT3TP03TTK3TPT3TPN1P2EP3stF3PF53PF61a1j2Ea3GE'3J16S2sc3szc4cnt13st33idx2g32b32r37strideg1X3SCJ1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF62c'3Hc'S2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF61a2HaS2sp2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sp2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3req2RQ3szc3FIT2mm4cnt13st33idx2g32b32r37strideg1X2GI3B304FITg4SZC11p2R43RI13RI22SK4XEND3stT3TP05TPEND3TTK3TPT3TPN1P2EP3stF3PF53PF63rid2rr3off2Ho4RI1r4RI2r3GRr2NE3LR13NE'1D3LR2S2sc3req2RQ3szc3FIT2mm4cnt13st33idx2g32b32r37strideg1X2GI3B304FITg4SZC11p2R43RI13RI22SK4XEND3stT3TP05TPEND3TTK3TPT3TPN1P2EP3stF3PF53PF63off2Ho4RI2r4RI1r3GRr2NH3NHCS2sc3szc4cnt13st33idx2g32b32r37strideg1X4FITg1p2R43stT3TP03TTK3TPT3TPN1P2EP3stF3PF53PF61a1j2Ea3J163Ea'S2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1PS2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc2SC3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc3st33idx2g32b32r32I07strideg1X4IDX31p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc4cnt13st33idx2g32b32r33C1R7strideg1X1p2R43stT3TP03TTK3TPT3TPN1PS2sc3szc4cnt13st32g37strideg3ENR4FIT3S2sc4cnt13NRRS2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF62c'3Hc'S3hRP2sc3szc3RCB3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF63off2Ho3RCrS3hRP2sc3req2RQ3szc3FIT3RCB4cnt13st33idx2g32b32r37strideg1X3B304FITg4SZC11p2R42SK4XEND3stT3TP03TTK3TPT3TPN1P3stF3PF53PF62rr3off2Ho3RCr3LR11D2R0S2sc3szc3st33idx2g32b32r37strideg1X3B301p2R42SK3stT3TP03TTK3TPT3TPN1P3stF3PF53PF62o'2HoS2sc3szc3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF62o'2HoS2sc2SC3szc4cnt13st33idx2g32b32r37strideg1X3SCJ1p3stT3TP03TTKS2sc3szc3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc3st33idx2g32b32r37strideg1X2R4S2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3ENR4FIT33B304SZC11p2R42SK4XEND3stT3TP03TTK3TPT3TPN1P2EP3stF3PF53PF61a1j2Ea3Ea'S2sc3req2RQ3szc3FIT4cnt13st33idx2g32b32r37strideg1X3ENR4FIT33B304SZC11p2R42SK4XEND3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc3st33idx2g32b32r37strideg1X3B301p2R42SK3stT3TP03TTK3TPT3TPN1P3stF3PF53PF62o'2HoS2sc3szc3st33idx2g32b32r32I07strideg1XS2sc3szc3st33idx2g32b32r37strideg1X4IDX3S2sc3req2SC2RQ3szc3FIT2mm4cnt13st33idx2g32b32r37strideg1X2JR3SCJ2GI3B304FITg4SZC11p2R43RI13RI22SK4XEND3stT3TP05TPEND3TTK3TPT3TPN1P3stF3PF53PF63rid2rr3off2Ho4RI1r4RI2r3GRr2NE3LR13NE'1D3LR2S2sc3req2SC2RQ3szc3FIT2mm4cnt13st33idx2g32b32r37strideg1X2JR3SCJ2GI3B304FITg4SZC11p2R43RI13RI22SK4XEND3stT3TP03TTK3TPT3TPN1P3stF3PF53PF63off2Ho4RI2r4RI1r3GRr2NH3NHCS2sc3req2RQ3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPN1P3stF3PF53PF6S2sc3szc3st33idx2g32b32r37strideg1X1p3stT3TP03TTK3TPT3TPNS3hRP2sc2SC3szc3RCB4cnt13st33idx2g32b32r37strideg1X2JR3SCJ1p2R43stT3TP03TTK3TPT3TPN1PS2sc3szc3st33idx2g32b32r37strideg1X1p2R43stT3TP03TTK3TPT3TPN1P3stF3PF53PF62rq2r'2L'3r''3L''". (* [comment removed for export] *)
#[using="LB req errv AR IS ER SC RQ FIT MR AUX CLO LO ERR TP HK"] Lemma rnsucc_ok : rNSUCC_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof. rceilb.
  intros st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC I0 HA3 SO3 SPAN3 RDV3.
  ddestruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA''
                  & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. rceilb.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (size_class_range sc SC) as SZR.
  ddestruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
  (* [comment removed for export] *)
  assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
  assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), idx; split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
  pose proof (MallocFacts_inv4.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
  pose proof (MallocFacts_inv4.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 idx AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
  assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
  assert (GE : conc st3 mm = conc st2 mm) by (apply (rconc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
  dpose (rmeta_slot_bounds st3 m'' mm MR'' MS3) as (Gpos & GC & GI & _).
  (* [comment removed for export] *)
  pose proof (so_mem _ _ _ _ _ _ SO3) as Hmem3. pose proof (so_reg _ _ _ _ _ _ SO3) as Hr3. pose proof (so_kind _ _ _ _ _ _ SO3) as Hk3.
  pose proof (so_mslot _ _ _ _ _ _ SO3) as MSLg. pose proof (so_fit _ _ _ _ _ _ SO3) as FIT3. pose proof (so_idx _ _ _ _ _ _ SO3) as IDX3.
  pose proof (so_b0 _ _ _ _ _ _ SO3) as B30. pose proof (so_span _ _ _ _ _ _ SO3) as SP3. pose proof (so_li _ _ _ _ _ _ SO3) as LI3.
  pose proof (mf_active _ _ MF3) as FA3. change (fact_active (strip st3)) with (fact_active st3) in FA3.
  ddestruct (FA3 (ncls sc cnt1) g3 HA3) as (_ & GSC3 & _).
  pose proof (lf_host_stride _ (isf_lf _ _ F3) g3 b3 Hmem3 ltac:(change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3); rewrite GSC3; lia)) as STR3.
  change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3) in STR3. rewrite GSC3 in STR3.
  pose proof (lf_mw _ (isf_lf _ _ F3) g3) as (MW3 & _ & _). change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3) in MW3.
  set (strideg := get_stride (get_meta_rec st3 g3)) in *.
  set (szc := size_class sc) in *.
  assert (FITg : 16 * szc * cnt1 + 16 <= strideg) by lia.
  assert (SZC1 : 16 * szc <= 16 * szc * cnt1) by nia.
  assert (SO_N : slot_ok st3 g3 b3 r3 idx (UNIT * size_class (ncls sc cnt1) - IB)) by (eapply slot_ok_N; [exact SO3| unfold IB; lia| unfold UNIT, IB; lia]).
  set (X := snd b3 + (16 + strideg * idx)) in *.
  set (p := (fst b3, X) : aptr).
  dpose (rregion_facts st3 m'' (fst b3) r3 MR'' Hr3) as (R4 & RAL & RC & RI1 & RI2). rceilb.
  assert (CB3 : conc st3 b3 = r_base r3 + snd b3) by (apply conc_region'; exact Hr3).
  assert (CP : conc st3 p = r_base r3 + X) by (apply conc_region'; exact Hr3).
  assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (XEND : X + strideg <= round_up_pg (r_len r3)).
  { unfold X. eapply Z.le_trans; [| exact SP3]. fold strideg.
    assert (strideg * idx + strideg <= strideg * (m_last_idx (get_meta_rec st3 g3) + 1)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    lia. }
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  assert (JR' : 0 <= ncls sc cnt1 < 48) by lia.
  assert (FRESH3 : forall o' v t, X <= o' < X + strideg - 4 -> (r_cells (get_shadow st3 (fst b3))) !! o' = Some (v, t) -> (t < s_tick st3)%N).
  { intros o' v t Ho Hc. eapply (ai_fresh _ _ _ _ _ AI'' I0 (fst b3) X (strideg - 4)); [| | exact Hc]; [| lia].
    dexists g3, b3. split; [exact HA3|]. split; [exact Hmem3|]. split; [reflexivity|]. split; [unfold X; lia| reflexivity]. }
  (* [comment removed for export] *)
  rewrite (nest_model_eq st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SO_N STR3).
  replace (slot_of st3 g3 idx) with p by (unfold slot_of, slot_start'; rewrite Hmem3; reflexivity).
  ddestruct (nt_tail_hyps st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3)
    as (TMS & TREC & TREG & TP0 & TP16 & TPEND & TGN & TNOG & TOLD & TTK).
  fold strideg X p in TMS, TREC, TREG, TP0, TP16, TPEND, TGN, TNOG, TOLD, TTK.
  set (stT := nt_stT st3 g3 b3 idx sc cnt1 mm) in *.
  assert (ACT3 : active st3 sc = None).
  { rewrite (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). exact ACT0. }
  assert (ACTT : active stT sc = None) by (unfold stT; rewrite ntT_active; exact ACT3).
  rewrite (ag_tail_kq_eq sc k bail stT mm p cnt1 (cnt1 - 1)); [| rewrite TREC; reflexivity| rewrite TREC; reflexivity| exact ACTT].
  ddestruct (ntT_proj st3 g3 b3 idx sc cnt1 mm) as (TPR & TPG & TPA & TPT & TPN & TPRS & TPC & TPS). fold stT in TPR, TPG, TPA, TPT, TPN, TPRS, TPC, TPS.
  assert (URT : 0 <= usage stT sc < 2^60).
  { unfold stT. rewrite ntT_usage. pose proof (mf_usage _ _ MF3 sc) as U. exact U. }
  assert (TCONC : forall q, conc stT q = conc st3 q) by (intros q; unfold stT; apply ntT_conc).
  (* [comment removed for export] *)
  riprefixT. unfold rnest_regs. rewrite <- GE.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rnenf_walk st3 m'' o g3 b3 r3 idx (ncls sc cnt1) MR'' UA'' JR' HA3 MSLg MW3 GSC3 STR3 SO_N TK''); [exact CTR''| exact MI'']. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m5 & -> & MU5 & WM5 & MI5 & MR5 & TK5)).
  fold strideg.
  (* [comment removed for export] *)
  assert (MWmm : mw_ok (get_meta_rec st3 mm)) by (rewrite G3; unfold mw_ok, meta0; cbn; lia).
  eapply evt_cut.
  { change (wz cnt1) with (Z_to_bv 64 cnt1).
    eapply (renfD_walk st3 m'' g3 b3 r3 idx (ncls sc cnt1) MR'' JR' SO_N TK''); [exact MS3| exact MWmm| exact C1R| exact MR5| exact TK5| exact MI5]. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (m6 & -> & MU6 & WM6 & MI6 & MR6 & TK6)).
  fold strideg in MU5, MU6, MR6, TK6 |- *.
  change (wr8 (fst b3, snd b3 + (16 + strideg * idx) + -3) (Z.lor (Z.land idx 31) 192) (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g3 b3 idx)))
    with (nt_stW st3 g3 b3 idx mm) in MR6, TK6.
  (* [comment removed for export] *)
  set (P := conc st3 b3 + 16 + strideg * idx) in *.
  assert (EP : P = r_base r3 + X) by (unfold P, X; rewrite CB3; lia).
  eapply evt_cut.
  { replace (wz (size_class sc * UNIT)) with (Z_to_bv 64 (16 * szc)) by (unfold wz, szc, UNIT; f_equal; lia).
    replace (Z_to_bv 64 (P + 12)) with (Z_to_bv 64 (P + 12 + 16 * szc * 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (cnt1 + 1)) with (Z_to_bv 64 (cnt1 + 1 - 0)) by (f_equal; lia).
    eapply (rzero_loop_walk st3 m'' g3 b3 r3 idx (ncls sc cnt1) MR'' STR3 SO_N (Z.to_nat (cnt1 + 1)) 0 szc cnt1 (nt_stW st3 g3 b3 idx mm) m6 m6);
      [lia| lia| unfold szc; lia| lia| unfold strideg in FITg; lia
      | apply (proj1 (ntW_proj st3 g3 b3 idx mm))| apply (proj1 (proj2 (ntW_proj st3 g3 b3 idx mm)))
      | exact MR6| exact TK6| exact MI6| apply munch_refl| apply wmono_refl]. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (m7 & -> & MU7 & WM7 & MI7 & MR7 & TK7 & RG7 & GR7 & PW7)).
  change (zero_hdrs (pp st3 g3 b3 idx) (16 * szc) 0 (Z.to_nat (cnt1 + 1)) (nt_stW st3 g3 b3 idx mm)) with stT in MR7, TK7, RG7, GR7.
  fold P in MU7, PW7.
  (* [comment removed for export] *)
  eapply evt_cut.
  { replace (Z_to_bv 64 P) with (Z_to_bv 64 (conc stT p)) by (rewrite TCONC, CP, EP; reflexivity).
    replace (Z_to_bv 64 (conc st3 mm)) with (Z_to_bv 64 (conc stT mm)) by (rewrite TCONC; reflexivity).
    eapply (rtail_walk stT sc cnt1 (cnt1 - 1) 0 mm p r3 SC C1R ltac:(lia) ltac:(lia) TMS TREC TREG Hk3 TP0 TP16 TPEND TGN TNOG TOLD URT ACTT TK7);
      [exact MR7| exact MI7]. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (s0x & a1x & a2y & a3x & a4z & m8 & -> & MU8 & WM8 & MI8 & MR8 & TK8)).
  (* [comment removed for export] *)
  set (W58 := ([(P - 3, P); (conc st3 mm, conc st3 mm + 40); (P - 3, P - 2); (P + 12, P + 12 + 16 * szc * cnt1 + 1)]%Z ++ rtailW stT sc mm p)).
  assert (LOWW : Forall (fun iv : Z * Z => snd iv <= rceil /\ (snd iv <= 0x10000 \/ 0x7e000 <= fst iv \/ (RCTX <= fst iv /\ snd iv <= RCTX + 928))) W58).
  { apply Forall_forall. intros [lo' hi'] HI. cbn [fst snd]. unfold W58, rtailW in HI. rewrite !TCONC, CP in HI. cbn [app In] in HI.
    pose proof (round_up_pg_ge (r_len r3)).
    destruct HI as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; inversion E; subst; unfold RCTX; lia. }
  assert (MU58 : munch W58 m'' m8).
  { intros x Hx. unfold W58 in Hx. rewrite outside_app' in Hx. destruct Hx as [H4x H8].
    rewrite (MU8 x H8). cbn [outside] in H4x. ddestruct H4x as (H5 & H6a & H6b & H7 & _).
    rewrite (MU7 x) by (cbn; auto). rewrite (MU6 x) by (cbn; auto). rewrite (MU5 x) by (cbn; auto). reflexivity. }
  assert (WM58 : wmono rsegs m'' m8).
  { eapply wmono_trans; [exact WM5|]. eapply wmono_trans; [exact WM6|]. eapply wmono_trans; [exact WM7| exact WM8]. }
  assert (DJhigh : forall A n, rceil <= A -> disjoint_from W58 A n).
  { intros A n HA. eapply Forall_disjoint_from; [exact LOWW|]. cbn. intros lo' hi' [H _]. lia. }
  assert (DJimg : forall A n, 0x10000 <= A -> A + n <= 0x7e000 -> (A + n <= RCTX \/ RCTX + 928 <= A) -> disjoint_from W58 A n).
  { intros A n H1 H2 H3. eapply Forall_disjoint_from; [exact LOWW|]. cbn. intros lo' hi' [_ H]. unfold RCTX in *. lia. }
  assert (FR8 : rw_cells rsegs m8 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [| exact MU58| exact WM58| apply DJhigh; lia]. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact FR''. }
  assert (ST8 : stk rsegs m8 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [| exact MU58| exact WM58| apply DJhigh; lia]. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
  assert (ERR8 : rw_cells rsegs m8 (errno_addr tp) [C4 errv'']).
  { eapply rw_cells_transport; [exact ERR''| exact MU58| exact WM58|]. rewrite EA. apply DJimg; [lia| cbn; lia| unfold RCTX; cbn; lia]. }
  set (stF := st_model stT sc cnt1 (cnt1 - 1) mm p).
  assert (MRF : rmrep stF m8) by (exact (rmrep_st_model stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 m8 MR8)).
  eapply evt_cut. { unfold rFRM in FR8. eapply (ras_ret0 sp gp tp); [exact MRF| exact MI8| exact FR8| exact ST8| exact CLO| lia]. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1w & a2w & -> & ST9)). apply evt_done.
  apply HK.
  (* [comment removed for export] *)
  fold strideg in MU7, PW7. fold P in MU7, PW7.
  ddestruct (smg_proj stT sc cnt1 (cnt1 - 1) mm p) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10).
  fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
  rewrite TPR in PF1. rewrite TPA in PF4. rewrite TPT in PF5. rewrite TPN in PF6. rewrite TPRS in PF7.
  assert (CTXT : ctx stT = ctx st3) by (unfold stT; apply ntT_ctx).
  rewrite CTXT in PF8, PF9, PF10.
  assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK8]; reflexivity).
  assert (MSF : meta_slot stF mm) by (apply (proj1 (smg_meta_slot stT sc cnt1 (cnt1 - 1) mm p mm)); exact TMS).
  assert (CF : forall q, conc stF q = conc st3 q) by (intros q; unfold stF; rewrite (smg_conc stT sc cnt1 (cnt1 - 1) mm p q); apply TCONC).
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR'' as (WF3 & _). dpose WF3 as ((RS3 & RPRS3) & WR3 & DJ3 & _).
  assert (STRF : get_stride (get_meta_rec stF mm) = 16 * szc) by (exact (ntF_stride st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3)).
  (* [comment removed for export] *)
  assert (HOLD2 : forall q rq, (s_regions st2) !! q = Some rq -> exists r', (s_regions stF) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
  { intros q rq Hq. destruct (mrel_regions _ _ MREL'' q rq Hq) as (r' & Hr' & K' & B' & L'). exists r'. rewrite PF1. auto. }
  assert (HOLD3 : forall q rq, (s_regions st3) !! q = Some rq -> exists r', (s_regions stF) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
  { intros q rq Hq. exists rq. rewrite PF1. repeat split; auto. lia. }
  assert (INSPAN : forall a, r_base r3 + X - 4 <= a < r_base r3 + X + strideg - 4 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia) HOLD3). apply SPAN3. unfold X in Ha. lia. }
  assert (INMETA : forall a, conc st3 mm <= a < conc st3 mm + 40 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
  { intros a Ha. left. do 3 right. ddestruct (rmeta_chunk_facts stF m8 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
    dexists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite CF in L0, H0'. lia. }
  assert (INCTX : forall a, RCTX <= a < RCTX + 928 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a) by (intros a Ha; left; right; right; left; exact Ha).
  (* [comment removed for export] *)
  assert (HDR0N : cell_read (get_shadow st3 (fst b3)) (X + strideg - 4) = Known 0).
  { pose proof (mf_hdr0 _ _ MF3 g3 b3 (idx + 1) Hmem3 ltac:(lia)) as H.
    unfold sstart_of in H. rewrite Hmem3 in H. cbn [default from_option id snd] in H. fold strideg in H. unfold IB, UNIT in H.
    replace (X + strideg - 4) with (snd b3 + 16 + strideg * (idx + 1) - 4) by (unfold X; lia). exact H. }
  assert (M6A : m6 (wa (r_base r3 + (X + strideg - 4))) = Some (b8 0)).
  { apply (rregion_byte_raw (nt_stW st3 g3 b3 idx mm) m6 (fst b3) r3 (X + strideg - 4) 0 MR6).
    - rewrite (proj1 (ntW_proj st3 g3 b3 idx mm)). exact Hr3.
    - exact Hk3.
    - lia.
    - rewrite (ntW_cell_read_other st3 g3 b3 idx (ncls sc cnt1) sc mm SC JR' (X + strideg - 4)) by (unfold X; lia). exact HDR0N. }
  assert (PE67 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m6 m7).
  { intros a Ha NC. split; [| intros W; apply WM7; exact W].
    destruct (arith_prog_dec a (P + 12) (16 * szc) cnt1 ltac:(lia)) as [(j & Hj & Ea)|NA].
    - destruct (Z_lt_le_dec a (P + strideg - 4)) as [LT|GE'].
      + exfalso. apply NC. apply INSPAN. lia.
      + assert (J16 : 16 * szc * j <= 16 * szc * cnt1) by (apply Z.mul_le_mono_nonneg_l; lia).
        assert (Ea' : a = r_base r3 + (X + strideg - 4)) by lia.
        rewrite Ea', M6A.
        apply (rregion_byte_raw stT m7 (fst b3) r3 (X + strideg - 4) 0 MR7); [rewrite TPR; exact Hr3| exact Hk3| lia|].
        assert (EJ : 16 * szc * j = 16 * szc * cnt1) by lia.
        replace (X + strideg - 4) with (X + 12 + cnt1 * (16 * szc)) by lia.
        unfold stT. apply (ntT_cell_read_zero st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R TK''). lia.
    - apply PW7. rewrite wa_unsigned by lia. intros j Hj. specialize (NA j Hj). lia. }
  assert (PE08 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m8).
  { eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE04|]. intros a Ha. exact (rmalloc_fp_mono st0 st2 stF lo (bv_unsigned sp) a HOLD2 Ha). }
    eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE''|]. intros a Ha. exact (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia) HOLD3 Ha). }
    eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU5| exact WM5|]. intros a Ha NC. cbn. split; [|exact I]. intros Xa; apply NC. apply INSPAN. lia. }
    eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros Xa; apply NC; [apply INMETA; lia| apply INSPAN; lia]. }
    eapply rpres_except_trans. { exact PE67. }
    eapply rpres_except_of_munch; [exact MU8| exact WM8|]. intros a Ha NC. unfold rtailW. rewrite !TCONC, CP. cbn.
    split; [|split; [|split; [|split; [|exact I]]]]; intros Xa; apply NC; [apply INCTX; unfold RCTX in *; lia| apply INMETA; lia| apply INSPAN; lia| apply INCTX; unfold RCTX in *; lia]. }
  (* [comment removed for export] *)
  assert (UAF : unk_agree stF o m8).
  { intros rid rr off h Hrr Kr Ho Hc NG. rewrite PF1 in Hrr.
    destruct (WR3 _ _ Hrr) as (R0 & _ & _ & RCr & _). rceilb.
    ddestruct (rregion_facts st3 m'' rid rr MR'' Hrr) as (_ & _ & _ & RI1r & RI2r). specialize (RI1r ltac:(lia)). specialize (RI2r ltac:(lia)).
    ddestruct (rmeta_chunk_facts st3 m'' mm MR'' MS3) as (_ & _ & _ & _ & _ & GRG & _). pose proof (GRG rid rr Hrr Kr) as GRr.
    assert (NG3 : ~ grp_hdr_cov st3 rid off).
    { intros CV. apply NG. unfold stF. apply (smg_grp_hdr_cov_old stT sc cnt1 (cnt1 - 1) mm p TP0 rid off TGN).
      eapply rgrp_hdr_cov_same; [exact TPG| exact CV]. }
    destruct (N.eq_dec rid (fst b3)) as [->|NE].
    - rewrite Hr3 in Hrr. inversion Hrr; subst rr.
      destruct (ntF_unknown st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N TK'' off h ltac:(lia) Hc) as [CV|(Hc3 & NH & NZ)].
      { exfalso. apply NG. exact CV. }
      rewrite <- (UA'' (fst b3) r3 off h Hr3 Kr Ho Hc3 NG3).
      assert (NHC : ~ (X <= off < X + 12)).
      { intros Hx. apply NG. unfold stF. change (fst b3) with (fst p). apply (smg_grp_hdr_cov stT sc cnt1 (cnt1 - 1) mm p SC). unfold p. cbn [snd]. lia. }
      transitivity (m7 (wa (r_base r3 + off))). { apply MU8. rewrite wa_unsigned by lia. unfold rtailW. rewrite !TCONC, CP. cbn. unfold RCTX. lia. }
      transitivity (m6 (wa (r_base r3 + off))). { apply PW7. rewrite wa_unsigned by lia. intros j Hj E. apply NZ. exists j. split; [exact Hj|]. lia. }
      transitivity (m5 (wa (r_base r3 + off))). { apply MU6. rewrite wa_unsigned by lia. cbn. lia. }
      apply MU5. rewrite wa_unsigned by lia. cbn. lia.
    - assert (Hc3 : cell_read (get_shadow st3 rid) off = Unknown h).
      { rewrite <- (ntF_shadow_other st3 g3 b3 idx sc cnt1 mm rid NE). exact Hc. }
      rewrite <- (UA'' rid rr off h Hrr Kr Ho Hc3 NG3).
      pose proof (lr_lo_group rr Kr) as LR1. pose proof (lr_lo_group r3 Hk3) as LR2.
      assert (NE' : fst b3 <> rid) by (intros E; apply NE; symmetry; exact E).
      pose proof (round_up_pg_ge (r_len r3)) as RU3.
      destruct (DJ3 _ _ _ _ Hr3 Hrr NE') as [D|D].
      all: transitivity (m7 (wa (r_base rr + off))); [apply MU8; rewrite wa_unsigned by lia; unfold rtailW; rewrite !TCONC, CP; cbn [outside]; unfold RCTX; lia|].
      all: transitivity (m6 (wa (r_base rr + off))); [apply MU7; rewrite wa_unsigned by lia; cbn [outside]; lia|].
      all: transitivity (m5 (wa (r_base rr + off))); [apply MU6; rewrite wa_unsigned by lia; cbn [outside]; lia|].
      all: apply MU5; rewrite wa_unsigned by lia; cbn [outside]; lia. }
  assert (RSP3 : ret_span st3 (ncls sc cnt1) idx (fst b3) X (strideg - 4)).
  { dexists g3, b3. split; [exact HA3|]. split; [exact Hmem3|]. split; [reflexivity|]. split; [unfold X; lia| reflexivity]. }
  unfold ras_post2.
  deexists 14. dexists m8, errv''. split; [reflexivity|].
  split; [exact MI8|]. split; [exact ST9|]. split; [exact ERR8|].
  split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m8); [exact MRF| exact AUX| exact PE08| exact CLO| lia]|].
  split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE08|].
  split. { split.
    - intros q rq Hq. rewrite <- REG1 in Hq. destruct (amr_regions _ _ _ REL q rq Hq) as (r' & H' & K' & B' & L' & _).
      ddestruct (HOLD2 q r' H') as (r'' & H'' & K'' & B'' & L''). exists r''. split; [exact H''|]. split; [rewrite K''; exact K'|]. split; [rewrite B''; exact B'|]. lia.
    - rewrite PF6. pose proof (amr_next_rid _ _ _ REL). pose proof (tr_next _ _ _ TR). pose proof (mrel_next _ _ MREL''). lia.
    - rewrite PF7, (mrel_reserved _ _ MREL''), (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
  split. { unfold brk_link_ps in BL'' |- *. rewrite PF8. destruct (c_brk (ctx st3)) as [| |brid boff]; auto. rewrite CF. exact BL''. }
  split; [exact PSM''|]. split; [exact PSF''|]. split; [exact PSO''|].
  split. { constructor.
    - intros c' Hc'. unfold stF. rewrite (smg_active stT sc cnt1 (cnt1 - 1) mm p c'). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold stT. rewrite ntT_active. rewrite (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
    - intros a Ha. rewrite PF4. apply (ai_areas _ _ _ _ _ AI''). apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
    - rewrite PF5, (ai_tick _ _ _ _ _ AI''), (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
    - intros _ rid' S len RSP o' v t Ho Hc.
      ddestruct (smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP) as (-> & -> & ->).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R) in Ho. rewrite andb_false_r in Ho.
      unfold p in Hc, Ho. cbn [fst snd] in Hc, Ho. rewrite PF5.
      unfold stF, stT, p in Hc. rewrite (ntF_span_cells st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R o') in Hc by (fold szc; lia).
      eapply FRESH3; [| exact Hc]. lia.
    - intros E0 _ rid' S len RSP o' Ho.
      ddestruct (smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP) as (-> & -> & ->).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R) in Ho. rewrite andb_false_r in Ho. unfold p in Ho. cbn [snd] in Ho.
      destruct (ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 o' ltac:(lia)) as (V1 & V2 & V3).
      unfold p. cbn [fst]. unfold stF, stT, p. split; [| split].
      + rewrite (ntF_span_cells st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R o') by (fold szc; lia). exact V1.
      + rewrite (ntF_span_hav st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' SO_N o') by lia. exact V2.
      + rewrite (ntF_havp st3 g3 b3 idx sc cnt1 mm). exact V3.
    - (* [comment removed for export] *)
      intros _ g' b' HA' _ UND. exfalso.
      unfold stF in HA'. rewrite (smg_active stT sc cnt1 (cnt1 - 1) mm p sc), Z.eqb_refl in HA'. injection HA' as <-.
      revert UND. unfold undersized, stF. rewrite (smg_rec_mt stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R), andb_false_r. cbn [m_sizeclass sm_rec]. unfold UNIT. lia. }
  split. { rewrite PF9. exact CTR''. }
  right. split; [lia|]. dexists mm, p, r3.
  split; [unfold stF; rewrite (smg_active stT sc cnt1 (cnt1 - 1) mm p sc), Z.eqb_refl; reflexivity|].
  split; [unfold stF, stT, p, X; apply (nt_slot_ok st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N STR3 ltac:(fold szc; lia) G3 MS3 TK'' FRESH3 req); lia|].
  rewrite STRF. unfold p. cbn [fst snd]. split.
  + intros a Ha. apply INSPAN. lia.
  + intros E0. replace (X + (16 + 16 * szc * 0) + -3) with (X + 13) by lia.
    destruct (ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 (X + 13) ltac:(lia)) as (V1 & V2 & V3).
    unfold stF, stT. apply (ntF_rdv13 st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N o V1 V2 V3).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End LEVEL.

End RP_1.
