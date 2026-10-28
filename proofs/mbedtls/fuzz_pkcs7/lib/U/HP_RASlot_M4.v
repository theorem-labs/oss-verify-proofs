(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W11 ASlot_W14 ASlot_W15 ASlot_W16 ASlot_W17 ASlot_W18 ASlot_I ASlot_M0 ASlot_M4P ASlot_M4 F_malloc_bigw F_malloc_big.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RMallocKit_A HP_RMallocKit_A2 HP_RMallocKit_A3 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RASlot_W2 HP_RASlot_W4 HP_RASlot_W11 HP_RASlot_W14 HP_RASlot_W15 HP_RASlot_W16 HP_RASlot_W17 HP_RASlot_W18 HP_RASlot_W19 HP_RASlot_M0 HP_RASlot_M2 HP_RASlot_M3 HP_RASlot_M5D HP_RASlot_M5F HP_RASlot_M5S HP_RF_malloc_big.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_M4 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_I.ras_post2"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_M3.rHMM_stmt"].


Section RP_1. Context {hRP : run_params}.
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
Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M4 ()) "Pst1,$0.Pidx,$1.Ps',$2.Pms',$3.P,(4.VhRP,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vo,Vm,Vst0,Vst,Vs,Vlo,Vsc,Vreq,R4.R3.R2.R1.)(5.VR,Vo,A2.Vk,R5.R4.R3.VQ,R2.)")
(* [comment removed for export] *).
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Local Ltac2 Set LiaOrc.tbl := fun () => "02:0@L11224761418.222L11803064104.156L11805748486.217L12302351600.247L12417435287.280L12651479035.338L13243977942.272L1358829691.280 L13768873754.211L14647732902.238L14647997396.242L14647998428.232L14648000206.232L14650174167.239L15032465161.330L15032665986.309L15047080864.266L16324977614.128L16774216550.119L17197803622.257L17212582873.216L19245567059.330L21191982056.119L21910439335.351L22377064377.241L22529801704.294L22529942807.133L22704559683.258L22704559683.5  L22706655604.13 L24466302780.331L2475888842.242 L2482955243.166 L24979050708.297L25069580847.209L25071877387.279L2584864590.246 L2591027350.301 L26559857697.160L2656158617.336 L26879287237.242L26879471303.330L26923924055.129L2740263016.258 L28096043745.245L2958490549.7   L30951416750.334L30953513974.332L31080994974.332L31087543653.232L31087543653.332L32203255141.266L32927694867.239L34171357086.237L34222453132.248L34222503474.209L35963458466.163L35963458466.332L36124670346.210L36479984805.247L36480082873.266L36480262335.265L36480842797.287L36799878203.254L37401788492.191L37792503789.232L37792504567.242L37792505599.232L37792760709.238L38717783282.245L38717783282.332L39052302351.225L39833727353.232L40113514276.222L40815512389.238L42015153612.295L42050817685.326L42977979586.289L44461986533.137L44483185898.157L45081068754.259L4511410525.333 L46464323579.238L46466555801.231L46468226850.191L46468453023.211L46578553465.281L46584680827.224L46640763165.158L47028999851.166L47033307802.245L4901852192.329 L4911059597.164 L49262164228.166L52219958642.243L52300761199.238L52507718435.326L52566919671.279L52676866268.297L53189684195.223L53476759721.223L5360065225.166 L54385471899.242L54385472915.232L54385474689.232L54385731817.238L54800954316.329L5523554883.223 L56765667309.232L56765669119.232L56807657374.334L57589765843.166L57626851459.8  L57627030594.258L59110733593.337L59308587409.225L59314873579.243L59314873579.265L59314955108.257L59854431986.223L61088316994.259L62986095911.330L63037048800.119L63754872735.244L63754872735.332L63922430156.223L63924841721.212L6426476427.7   L6428571836.258 L65537848319.278L65540045945.266L67442659576.240L6755913069.326 L68292987392.241L68478600214.326L8804124108.27  L8826444249.241 L919885727.129  00000b01c02U03L04_06L08909]0:N0;S0<X0=]0>b0?g0A;0BF0C90C\0Ce0DX0EG0F^0Ff0H<0I90J;0Je0Kn0L=0Ld0NJ0NK0O20P40Q>0RX0SR0TQ0UR0W<0X70YN0Z10[60\20\G0]e0_C0`m0ae0cL0dC0e90f;0fn0gZ0hA0ic0ji0kl0lo0n20o;10H11812H13X14h16817E19119`1:X1;O1;P1<V1=o1?51@61A01Ac1CA1D81Do1E_1FO1GV1HS1I61IY1JQ1LF1MK1N?1O51O61PO1R:1S81Sd1U01V11Vh1W_1XV1YM1Zg1[S1\]1]U1_51_X1`21aX1c=1co1di1f51gZ1hF1i<1jS1jW1kZ1m<1nB1oH1oa21421g22Z23\25026C27j2922:@2:gS2sp2lo2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRSS3hRP2sp2lo2sc2LO3RCB3st24cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDBS2sp2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRSS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS3ridS3hRP2sp2lo2sc3RCB3st22mm4cnt14CLO'4size3stS3nos2u12cR2nd3NDB2GC2xa4TKS'3NRS2X03ridS2sc3st22mm4cnt14size3stS3nos2u12cR1c2nd3NDB2xa4TKS'3NRS2X03rid3stT2ml2ai3stF3PF53PF64TKT'3NRT1a1X3rr02L03H0'S3hRP2sc3req2RQ3RCB3st24cnt14size2SZ3stS3nos2u12cR1c2nd2CR1r3NDM3NDR2xa4TKS'3NRS2X02r12XA2XC3rid2XI1q1H2q02H4S3hRP2sp2lo2sc3req2SC2RQ3RCB3st22mm4cnt14CLO'4size3stS3nos2u12cR2nd3NDR3NDB2GC2xa4TKS'3NRS2X02XC3ridS2sp2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRS1yS3hRP2sc3RCB3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS2X02XC3ridS3hRP2sc3RCB3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS2X02XC3ridS3hRP2sc3RCB3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS2X02XC3ridS3hRP2sc3RCB3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS2X02XC3ridS3hRP2sc3RCB3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS2X02XC3ridS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRTS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF6S2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3ridS2sc3req3FIT3st24cnt13stS3nos2u12cRS2sc4cnt1S2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRSS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRT2rqS2sc3SZRS2sc3st24cnt14size3stS3nos2u12cR1c2nd4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRT1r2H0S2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRS3stF3PF63PF71x2HxS2sc3req2RQ3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid2ml2aiS2sc3req2RQ3st24cnt14size3stS3nos2u12cR2ndS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB4TKS'3NRS3stF3PF63PF71r3off2Ho3RI2S2rq3off2Ho3RI2S3hRP2sp2lo2sc2LO3ASG4CLO'2rq3off2Ho2RCS2st2sc3st13st24cnt14size3stS3nos2u12cR1c2nd3NDB2xa4TKS'3NRS2X03stT2ml2ai3stF3PF53PF64TKT'3NRT3NX13NX0FS2sc3st24cnt14size3stS3nos2u12cR2nd3NDBS2sc3req3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid2ml2ai2R1S3hRP2sp2lo2sc2LO3RCB3st24cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDB4TKS'3NRSS3hRP2sp2lo2sc2LO3RCB3st22mm4cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDB2GC2xa4TKS'3NRS2X03ridS2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRS3stF3PF63PF71rS2sc3st24cnt14size3stS3nos2u12cR1c2nd1r3NDM4TKS'3NRS3rid1q2ai1HS3hRP2sp2lo2sc2LO3RCB3st24cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDBS2sc3st24cnt14size3stS3nos2u12cR1c2nd3NDB2xa4TKS'3NRS2X03rid3stT2ml2ai3stF3PF53PF64TKT'3NRT2rq2r12L12r22L2S2sp2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRS3stF3PF63PF7S2sp2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRTS2sc3st24cnt14size2SZ3stS3nos2u12cRS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB4TKS'3NRS3stF3PF63PF71r3off2HoS2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRS3stF3PF63PF71a1XS2nd2xa2rq3off2Ho3DJqS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRT3len2o'2HoS2sc3st22mm4cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRT2o'3Ho'S2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRT1a1X2mm3NDB2X03S163SNDS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3rid1a2HaS2sc3st22mm4cnt14size3stS3nos2u12cR1c2nd3NDB2xa4TKS'3NRS2X03rid3stT2ml2ai3stF3SND3PF53PF64TKT'3NRT1a2HaS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS2X03ridS2sc3st24cnt14size3stS3nos2u12cR2nd2r13NDM4TKS'3NRS1q1r1H2H02q12H9S2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRSS2sc3st24cnt14size3stS3nos2u12cR2nd1a1XS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRT1a1X2SC3NDB2X0S3hRP2sp2lo2sc2LO3st24cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDB4TKS'3NRSS2sc3st24cnt14size3stS3nos2u12cR3CRR1c2nd2CR3NDB2xa4TKS'3NRS2X03ridS2sc3st24cnt14size3stS3nos2u12cR3CRR1c2nd2CR3NDB2xa4TKS'3NRS2X03ridS2sc3st24cnt14size3stS3nos2u12cR3CRR1c2nd2CR3NDB2xa4TKS'3NRS2X03ridS2sc3st24cnt14size3stS3nos2u12cR3CRR1c2nd2CR3NDB2xa4TKS'3NRS2X03rid2ml2aiS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB4TKS'3NRS3stF3PF63PF71q1x2Hx2r02L03H0'S3hRP2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRSS3hRP2sc3req2RQ3RCB3st24cnt14size3stS3nos2u12cR2nd3NDR3NDB2xa4TKS'3NRS2X02XC3ridS3hRP2sc3req2RQ3RCB3st24cnt14size3stS3nos2u12cR2nd3NDR3NDB2xa4TKS'3NRS2X02XC3ridS3hRP2sc3req2RQ3RCB3st24cnt14size3stS3nos2u12cR2nd3NDR3NDB2xa4TKS'3NRS2X02XC3ridS3hRP2sc3req2RQ3RCB3st24cnt14size3stS3nos2u12cR2nd3NDR3NDB2xa4TKS'3NRS2X02XC3ridS2sp2lo2sc2LO3st24cnt13ASG4size3stS3nos2u12cR2nd3NDB4TKS'3NRS3stF3PF63PF71a1XS2sp2lo2sc2LO3st24cnt13ASG4size3stS3nos2u12cR1c2nd3NDB2xa4TKS'3NRS2X03rid3stT2ml2ai3stF3PF53PF64TKT'3NRT1a1XS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRSS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3rid1a2HoS3hRP2lo2sc3CLO3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRSFS2sc3st24cnt13SZR4size3stS3nos2u12cR1c2nd3NDB2xa4TKS'3NRS2X03rid2ml2aiS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRT1a2HaS2sc3st24cnt14size3stS3nos2u12cR1c2nd3NDB2xa4TKS'3NRS2X03rid2ml2ai3EMLS2sc3req2RQ3st24cnt14size2SZ3stS3nos2u12cR1c2nd2CR2En1H2H03NDR2H1S3hRP2sp2lo2sc3RCB3st24cnt14CLO'4size3stS3nos2u12cR2nd3NDBS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid2r03stT2ml2ai3stF3PF53PF64TKT'3NRT3off2HoS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB4TKS'3NRSS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB4TKS'3NRSS2sp2lo2sc2LO3st24cnt13ASG4size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS2X03ridS2sp2lo2sc2LO3st24cnt13ASG4size3stS3nos2u12cR2nd3NDB4TKS'3NRSS2sc3st24cnt14size3stS3nos2u12cR2ndS2sc3st24cnt14size3stS3nos2u12cR2ndS2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRS3stF3PF63PF7S2sc3req2SC2RQ3st22mm4cnt14size3stS3nos2u12cR1c2nd3NDR3NDB2GI2xa4TKS'3NRS2X02XA3rid2XI3stT2ml2ai3stF3PF53PF64TKT'3NRTS3hRP2sp2lo2sc2LO3RCB3st24cnt13SPR3ASG4CLO'4size3stS3nos2u12cR2nd3NDBS2sp2lo2sc2LO3st24cnt13ASG4size3stS3nos2u12cR2nd3NDBS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3rid2XIFS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRT1a2HaS3hRP2sp2lo2sc3req2SC2RQ2LO3RCB3st22mm4cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDR3NDB2GC2xa4TKS'3NRS2X02XC3ridS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid2ml2ai2N1S2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRSS3hRP2sp2lo2sc2LO3st24cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS2X0S3hRP2sp2lo2sc2LO3RCB3st24cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDBS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS3ridS2sc3st22mm4cnt14size3stS3nos2u12cR1c2nd2GI2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRTS2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRSS3hRP2sc3RCB3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS2X02XC3rid1a2HaS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3rid1a2HaS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid2r03stT2ml2ai3stF3PF53PF64TKT'3NRT3off2Ho1TS2sc3st24cnt14size3stS3nos2u12cR2ndS3st22mm2rq3off2Ho3RI23GRqS3hRP2sp2lo2sc2LO3RCB3st24cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDB4TKS'3NRS3stF3PF63PF71r3off2Ho2RC3RI2S2sc3st24cnt14size3stS3nos2u12cR1c2nd3NDB2xa4TKS'3NRS2X03rid3stT2ml2ai3stF3PF53PF64TKT'3NRT2rq3off2HoS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS2HrS2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRS3stF3PF63PF71HS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB4TKS'3NRS3stF3PF63PF71r3off2Ho1q2Ha1HS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB4TKS'3NRS3stF3PF63PF71r3off2Ho3RI22Ha3hRP2sp2lo2LO3ASG4CLO'2RCS2sc3st24cnt14size3stS3nos2u12cR2nd4TKS'3NRSS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3rid2MLS2sc3st22mm4cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRTS2scS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB4TKS'3NRS3stF3PF63PF72c'3Hc'S2sc3st24cnt14size3stS3nos2u12cR1c2nd3NDB2xa4TKS'3NRS2X03rid3stT2ml2ai3stF3PF53PF64TKT'3NRT2c'3Hc'S3hRP2sp2lo2sc2LO3st24cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDB4TKS'3NRSS3hRP2sp2lo2sc2LO3st24cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDB4TKS'3NRSS3hRP3RCB2rq3off2Ho2R02RCS3hRP2sc3RCB3st24cnt14size3stS3nos2u12cR2nd3NDB4TKS'3NRS3stF3PF63PF71r3off2Ho2R02RCS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR2nd2xa4TKS'3NRS3ridS2sc3st24cnt14size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS2X03rid2XI1w2HwS2sc3st24cnt14size3stS3nos2u12cR1c2nd2xa4TKS'3NRS3rid3stT2ml2ai3stF3PF53PF64TKT'3NRTS3hRP2sp2lo2sc2LO3st24cnt13ASG4CLO'4size3stS3nos2u12cR2nd3NDB2xa4TKS'3NRS2X02XC3ridS3hRP2sc3st24cnt14size3stS3nos2u12cR1c2nd3NDB2xa4TKS'3NRS2X02XC3rid3stT2ml2ai3stF3PF53PF64TKT'3NRT1a2HaS2sc2SC3st22mm4size3stS1c2nd2xa3rid2ai3stF3S163SND2rq3off2Ho3RI23GRq3DJqS2sp2lo2sc2LO3st24cnt13ASG4size3stS3nos2u12cR2nd3NDB4TKS'3NRS3stF3PF63PF71x2HxS2sc3req2RQ3st24cnt14size3stS3nos2u12cR". (* [comment removed for export] *)
Lemma rhmm_ok : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M4 ()) "(6.VhRP,VR,Vk,Vbail,Vo,Vs,VQ,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Va1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vst0,Vst,Vlo,Vsc,Vreq,)")
(* [comment removed for export] *).
Proof using A1 AR AUX CLO ER FIT HK LO MR RQ SC TP. rceilb.
  clear A0 F0 IS AC TK UA BL ST MI ERR.
  intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R BIGc.
  ddestruct CT as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & MR3 & TK3 & UA3 & MI3 & ST3 & FR3 & ERR3 & AUX3 & PE03 & BL2 & PSM & PSF & PSO).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. rceilb.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
  pose proof (mf_usage _ _ MF2) as URall. change (fact_usage (strip st2)) with (fact_usage st2) in URall.
  pose proof (mf_ctx _ _ MF2) as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
  change (ctx (strip st2)) with (ctx st2) in FC1, FC2, FC3, FC4. change (bounces (strip st2)) with (bounces st2) in FC5. change (unmap_seq (strip st2)) with (unmap_seq st2) in FC6.
  pose proof (size_class_range sc SC) as SZR.
  unfold rcnt_state.
  replace (size_class sc * UNIT * cnt1) with (UNIT * size_class sc * cnt1) by lia.
  replace (size_class sc * UNIT) with (UNIT * size_class sc) by lia.
  set (size := UNIT * size_class sc) in *.
  assert (SZ : 16 <= size < 2^18) by (subst size; unfold UNIT; lia).
  rewrite A1. rewrite (ag_mmap_eq sc req k bail st2 mm cnt1).
  set (stS := step_seq (account_bounce sc st2)).
  set (nos := is_bouncing sc st2).
  set (u1 := mm_usage1 stS sc (usage st2 sc)).
  set (cR := mm_cnt_red sc size cnt1 u1 nos).
  assert (CRR : 1 <= cR <= 32) by (subst cR; apply mm_cnt_red_range; exact C1R).
  destruct (mm_final size req u1 cR nos) as [c nd] eqn:EF.
  ddestruct (mm_final_props size req u1 cR nos c nd CRR ltac:(lia) ltac:(lia) ltac:(subst size; unfold UNIT; lia) EF) as (CR & NDM & NDR & NDC).
  assert (NDB : 16 <= nd < 2^40).
  { pose proof (round_up_pg_props (req + 20) ltac:(lia)). pose proof (round_up_pg_props (size * c + 16) ltac:(nia)).
    assert (size * c <= 2^18 * 32) by nia. destruct NDC as [[Ec En]|[LE En]]; rewrite En; lia. }
  cbv beta iota.
  (* [comment removed for export] *)
  riprefixT.
  eapply evt_cut. { eapply (rmm_seq_walk sc SC); [exact MR3| exact FC4| exact FC5| exact FC6| exact MI3]. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (u0 & u1' & wa3 & wa6 & wa7 & m4 & -> & -> & MU4 & WM4 & MI4 & MR4)).
  fold nos stS in MR4 |- *.
  (* [comment removed for export] *)
  ddestruct (stS_shape sc st2) as (fS & ES & HS). fold stS in ES.
  assert (US : forall i, usage stS i = usage st2 i) by (intros i; unfold usage; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (proj2 (HS _))); reflexivity).
  eapply evt_cut.
  { replace (wz (size + 16)) with (wz (size + 16)) by reflexivity.
    eapply (rmmc_walk sc size req nos SC SZ RQ) with (st := stS) (m := m4); [exact MR4| exact C1R| apply URall| intros i; rewrite US; apply URall]. }
  cbv beta. unfold rmmc_post. (intros ms' dd_H; ddestruct dd_H as (v0 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & ->)).
  fold u1. fold cR. rewrite ?EF. cbn [fst snd].
  (* [comment removed for export] *)
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [exact FR3| exact MU4| exact WM4|]. unfold rseqW, RCTX. cbn. lia. }
  assert (ST4 : stk rsegs m4 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [exact ST3| exact MU4| exact WM4|]. unfold rseqW, RCTX. cbn. lia. }
  assert (ERR4 : rw_cells rsegs m4 (errno_addr tp) [C4 errv']).
  { eapply rw_cells_transport; [exact ERR3| exact MU4| exact WM4|]. rewrite EA. unfold rseqW, RCTX. cbn. lia. }
  assert (PE04 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4).
  { eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_of_munch; [exact MU4| exact WM4|].
    intros a Ha NC. unfold rseqW. cbn. split; [|exact I]. intros X. apply NC. left. right. right. left. unfold RCTX in *. lia. }
  assert (AUX4 : rauxv_ok m4 (bv_unsigned sp)).
  { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. unfold rseqW, RAUXV_CELL, RCTX, RLIBC. constructor; [cbn; lia| constructor]. }
  dpose (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & GI & _).
  (* [comment removed for export] *)
  eapply evt_cut. { eapply rmm_call_walk. }
  cbv beta. intros ms' ->.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -144) by (subst sp'; apply unsigned_lit; lia).
  eapply rimplT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST4 | exact ERR4 | exact MI4 | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | lia | rewrite SP'; lia | exact CLO
    | rewrite SP', EA; lia | rewrite TP; unfold RATP; rewrite unsigned_lit by lia; lia ]. }
  intros ans ms' PO.
  (* [comment removed for export] *)
  assert (REGS : s_regions stS = s_regions st2) by (rewrite ES; reflexivity).
  assert (SHS : s_shadow stS = s_shadow st2) by (rewrite ES; reflexivity).
  assert (GRS : s_groups stS = s_groups st2) by (rewrite ES; reflexivity).
  assert (ARS : s_areas stS = s_areas st2) by (rewrite ES; reflexivity).
  assert (TKS' : s_tick stS = s_tick st2) by (rewrite ES; reflexivity).
  assert (NRS : s_next_rid stS = s_next_rid st2) by (rewrite ES; reflexivity).
  assert (RSS : s_reserved stS = s_reserved st2) by (rewrite ES; reflexivity).
  assert (RECS : forall q, get_meta_rec stS q = get_meta_rec st2 q) by (intros q; rewrite ES; reflexivity).
  assert (ACTS : forall c', active stS c' = active st2 c') by (intros c'; unfold active; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (HS _)); reflexivity).
  assert (BRKS : c_brk (ctx stS) = c_brk (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (HS _))))).
  assert (CTRS : c_mmap_counter (ctx stS) = c_mmap_counter (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (HS _)))))).
  assert (FMHS : c_free_meta_head (ctx stS) = c_free_meta_head (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (proj2 (HS _))))))).
  assert (CONCS : forall q, conc stS q = conc st2 q) by (intros q; unfold conc, get_region; rewrite REGS; reflexivity).
  assert (MSLS : meta_slot stS mm) by (eapply meta_slot_same_areas; [exact ARS| exact MSL]).
  assert (TKS : ticks_ok stS) by (eapply ticks_ok_same; [exact SHS| exact TKS'| exact TK3]).
  (* [comment removed for export] *)
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR as (WF & _). dpose WF as ((RS0 & RPRS0) & WR0 & DJ0 & _).
  destruct ans as [e|xa].
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    ddestruct PO as (v0' & v1 & v2 & v3 & v4' & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He).
    cbn [mmap_val]. unfold mm_after. fold stS. destruct (mmap_answer_ok_err (s_ceil stS) (live_ranges stS) nd e He) as [-> ->]. cbn [negb].
    rewrite as_free_meta_eq. cbn [as_kq].
    rewrite SP' in MU6, ST6. rewrite EA in MU6.
    replace (ret_pc (Z_to_bv 64 0x40f88)) with (Z_to_bv 64 0x40f88) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : rmrep stS m6).
    { eapply (rwrapper_munch_keeps stS m4 m6 (bv_unsigned sp - 144) lo MR4); [| exact WM6| rceilb; lia].
      eapply munch_weaken; [| exact MU6]. intros y; cbn; lia. }
    (* [comment removed for export] *)
    pose proof (lf_freelist _ (isf_lf _ _ F2)) as FFL. change (fact_freelist (strip st2)) with (fact_freelist st2) in FFL.
    assert (FL : forall h, c_free_meta_head (ctx stS) = Some h ->
              meta_slot stS h /\ h <> mm /\ exists p, m_prev (get_meta_rec stS h) = Some p /\ meta_slot stS p /\ p <> mm).
    { intros h Hh. rewrite FMHS in Hh. ddestruct (FFL h Hh) as (MSh & MEMh & NXh & p & HP & MSp & MEMp & NXp).
      change (meta_slot (strip st2) h) in MSh. change (get_meta_rec (strip st2) h) with (get_meta_rec st2 h) in MEMh, NXh, HP.
      change (meta_slot (strip st2) p) in MSp. change (get_meta_rec (strip st2) p) with (get_meta_rec st2 p) in MEMp, NXp.
      split; [eapply meta_slot_same_areas; [exact ARS| exact MSh]|].
      split; [intros ->; rewrite G0 in NXh; apply NXh; reflexivity|].
      exists p. rewrite RECS. split; [exact HP|]. split; [eapply meta_slot_same_areas; [exact ARS| exact MSp]|].
      intros ->. rewrite G0 in NXp. apply NXp. reflexivity. }
    riprefixT.
    eapply evt_cut. { eapply rmm_ret_fail_walk. }
    cbv beta. intros ms' ->.
    eapply evt_cut. { rewrite <- (CONCS mm). subst sp'. unfold rFRM in FR6. eapply (rfailm2_walk stS mm MSLS FL); [exact MR6| exact MI6| exact FR6| lia]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (s6x & m7 & junk' & -> & FR7 & MU7 & WM7 & MI7 & MR7)).
    assert (LW : Forall (rlowW (bv_unsigned sp)) (rfailW stS mm (bv_unsigned sp))).
    { eapply (rfailW_low stS mm m6 _ MR6 MSLS). intros h Hh. ddestruct (FL h Hh) as (MSh & _ & p & HP & MSp & _).
      split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
    assert (ST7 : stk rsegs m7 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [exact ST6| exact MU7| exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]]. }
    assert (ERR7 : rw_cells rsegs m7 (errno_addr tp) [C4 (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e))]).
    { eapply rw_cells_transport; [exact ERR6| exact MU7| exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold RCTX; cbn; lia| lia]. }
    eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1y & a2y & -> & ST8)). apply evt_done.
    (* [comment removed for export] *)
    set (stF := as_fm_st stS mm) in *.
    ddestruct (fm_proj stS mm) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10 & PF11 & PF12 & _). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
    assert (FS : Forall (rmetaW (bv_unsigned sp) stS) (rfailW stS mm (bv_unsigned sp))).
    { apply (rfailW_shape stS mm _ MSLS). intros h Hh; ddestruct (FL h Hh) as (MSh & _ & p & HP & MSp & _); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
    assert (PE07 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m7).
    { eapply rpres_except_trans.
      - eapply rpres_except_mono; [exact PE04|]. intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros rid r Hr. exists r. rewrite PF1, REGS. repeat split; auto; lia.
      - eapply rpres_except_trans.
        + eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros X; apply NC; left; [left; lia| right; left; rewrite unsigned_lit by lia; lia].
        + eapply rpres_except_of_munch'; [exact MU7| exact WM7|].
          intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          * cbn in E1, E2. subst lo' hi'. left. do 3 right.
            assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
            ddestruct (rmeta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
            dexists rid0, r0. split; [exact H0|]. split; [exact K0|].
            assert (EC : conc stF q = conc stS q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
          * inversion E; subst. left. right. right. left. unfold RCTX in *. lia.
          * inversion E; subst. left. left. lia. }
    apply HK. unfold ras_post2.
    deexists 14. dexists m7, (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e)). split; [reflexivity|].
    split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
    split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
    split; [exact MR7|].
    split; [eapply ticks_ok_same; [rewrite PF2; exact SHS| rewrite PF6; exact TKS'| exact TK3]|].
    split. { eapply (unk_agree_xfer o st2 m3 stF m7 UA3).
      - rewrite PF2. exact SHS.
      - intros rid r Hk Hr. rewrite PF1, REGS in Hr. exact Hr.
      - intros b. rewrite PF3, GRS. split; intros X; exact X.
      - intros rid r off h Hr Hk Ho Hc NG.
        pose proof MR3 as (WF3 & _). dpose WF3 as (_ & WR3 & DJ3 & _). destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _). rceilb.
        ddestruct (rregion_facts st2 m3 rid r MR3 Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
        transitivity (m6 (wa (r_base r + off))).
        { apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
          pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          - cbn in E1, E2. subst lo' hi'. rewrite CONCS in Ha.
            assert (MSq2 : meta_slot st2 q) by (eapply meta_slot_same_areas; [symmetry; exact ARS| exact MSq]).
            ddestruct (rmeta_chunk_facts st2 m3 q MR3 MSq2) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
          - inversion E; subst. unfold RCTX in Ha. lia.
          - inversion E; subst. lia. }
        transitivity (m4 (wa (r_base r + off))).
        { apply MU6. rewrite wa_unsigned by lia. cbn. lia. }
        apply MU4. rewrite wa_unsigned by lia. unfold rseqW, RCTX. cbn. lia. }
    split; [exact PE07|].
    split. { split; [| rewrite PF7, NRS, <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite PF8, RSS, (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
             intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. rewrite PF1, REGS. auto. }
    split. { unfold brk_link_ps in *. rewrite PF11, BRKS. destruct (c_brk (ctx st2)) as [| |rid off]; auto.
             unfold conc, get_region. rewrite PF1, REGS. exact BL2. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite PF9, ACTS, (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ARS. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF6, TKS', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia.
      - intros H; exfalso; lia. }
    split; [rewrite PF12, CTRS; exact FC1|].
    left. reflexivity.
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    destruct PO as [AOK [BAD|PO]].
    { (* [comment removed for export] *)
      cbn [mmap_val]. unfold mm_after. fold stS.
      erewrite (rmmap_rejects_high (s_ceil stS)); [cbn [negb]; apply rimplT_undef| lia| rewrite (rmrep_ceil _ _ MR4); lia| exact AOK| exact BAD]. }
    ddestruct PO as (v0' & v1 & v2 & v3 & v4' & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & XR6).
    cbn [mmap_val]. unfold mm_after. fold stS.
    destruct (mmap_answer_ok (s_ceil stS) (live_ranges stS) nd xa) eqn:VOK. 2:{ cbn [negb]. apply rimplT_undef. }
    cbn [negb].
    ddestruct (mmap_answer_ok_addr (s_ceil stS) (live_ranges stS) nd xa ltac:(lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
    rewrite (rmrep_ceil _ _ MR4) in XC.
    rewrite SP' in MU6, ST6.
    assert (RU : round_up_pg nd = nd) by (unfold round_up_pg; change (PGSZ - 1) with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia).
    rewrite RU in XC, XRF.
    assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : rmrep stS m6).
    { eapply (rmrep_transport_high stS m4 m6); [exact MR4| exact MU6| exact WM6| intros lo' hi' [E|[]]; inversion E; rceilb; lia]. }
    (* [comment removed for export] *)
    unfold new_region.
    set (rid := s_next_rid stS). set (r0 := {| r_kind := RKGroup; r_base := xa; r_len := nd |}).
    set (stN := set_next_rid (N.succ rid) (set_regions (<[rid:=r0]> (s_regions stS)) stS)).
    assert (EstN : stN = fst (new_region RKGroup xa nd stS)) by reflexivity.
    pose proof (mf_ptrs _ _ MF2) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) stS).
    { rewrite ES. apply ptrs_in_upd_ctx_scalar; try (intros cc; dpose (HS cc) as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); assumption).
      eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. rewrite NRS. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; rewrite NRS; lia)) as [FRr FRs].
    unfold F_mm_syscalls.mmap_raw in ST6 |- *. cbn [negb] in ST6 |- *. rewrite mmap_len_round_up, RU in ST6 |- *.
    rceilb.
    set (mz := apply_zeros m6 [(wa xa, Z_to_bv 64 nd)]) in *.
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + nd <= a) -> mz (wa a) = m6 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + nd -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (MRz : rmrep stN mz).
    { rewrite EstN. eapply (rmrep_new_region stS m6 mz xa nd RKGroup MR6 PT1 ltac:(rewrite SHS; exact FRs) X0 XA ltac:(lia));
        rewrite ?mmap_len_round_up, ?RU; [rceilb; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    pose proof MR6 as (WF6 & _). dpose WF6 as ((RS6 & RPRS6) & WR6 & DJ6 & _).
    assert (XI : xa + nd <= 0x10000 \/ 0x7e000 <= xa).
    { assert (RFimg : ranges_free ref_reserved xa nd = true).
      { apply ranges_free_intro. intros b kk HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS6. exact HI. }
      apply (rreserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv rsegs mz).
    { unfold mz. apply (mem_inv_zeros rsegs m6 xa nd); try lia; [exact MI6|]. intros w Hw. apply ref_ro_addr_false. lia. }
    assert (MUz : munch [(xa, xa + nd)] m6 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono rsegs m6 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono rsegs m6 xa nd); try lia; exact Hw).
    assert (FRz : rw_cells rsegs mz (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR6| exact MUz| exact WMz|]. cbn. lia. }
    assert (STz : stk rsegs mz lo (bv_unsigned sp + -144)) by exact ST6.
    assert (ERRz : rw_cells rsegs mz (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [exact ERR6| exact MUz| exact WMz|]. rewrite EA. cbn. lia. }
    (* [comment removed for export] *)
    assert (MSLN : meta_slot stN mm) by (eapply meta_slot_same_areas; [| exact MSLS]; rewrite EstN; reflexivity).
    assert (RECN : get_meta_rec stN mm = meta0) by (rewrite EstN; change (get_meta_rec (fst (new_region RKGroup xa nd stS)) mm) with (get_meta_rec stS mm); rewrite RECS; exact G0).
    assert (CTRN : c_mmap_counter (ctx stN) = c_mmap_counter (ctx st2)) by (rewrite EstN; change (ctx (fst (new_region RKGroup xa nd stS))) with (ctx stS); exact CTRS).
    assert (GCN : conc stN mm = conc st2 mm).
    { rewrite <- CONCS. rewrite EstN. apply nr_conc. cbn [fst].
      ddestruct MSLS as (ar & arr & kk & Ha & Hk & ->). unfold aadd. cbn [fst]. intros E.
      ddestruct PT1 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ Ha) as [X _]. exact (X E). }
    replace (ret_pc (Z_to_bv 64 0x40f88)) with (Z_to_bv 64 0x40f88) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    riprefixT.
    eapply evt_cut.
    { rewrite <- GCN. subst sp'.
      eapply (rmm_ret_ok_walk stN sc c size nd xa (c_mmap_counter (ctx st2)) mm SC ltac:(lia) SZ ltac:(lia) NDM X0 XC MSLN RECN CTRN FC1);
        [exact MRz| exact MIz]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (xa3 & xa4 & m8 & -> & MU8 & WM8 & MI8 & MR8 & CTR8)).
    set (stT := mm_st4 stN nd mm) in *.
    (* [comment removed for export] *)
    assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (ML : 0 <= Z.shiftr nd 12 < 2^52) by (rewrite ND12; Z.div_mod_to_equations; lia).
    assert (RECT : get_meta_rec stT mm = {| m_prev := None; m_next := None; m_mem := None; m_avail := 0; m_freed := 0; m_last_idx := 0; m_freeable := 0; m_sizeclass := 0; m_maplen := Z.shiftr nd 12 |}).
    { unfold stT, mm_st4. rewrite rec_upd_ctx. unfold upd_meta. rewrite get_meta_rec_put_same, RECN. unfold m_set_maplen, meta0. cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass].
      f_equal. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    assert (HrT : (s_regions stT) !! rid = Some r0) by (unfold stT, mm_st4, upd_meta; cbn; first [apply lookup_insert_eq | rewrite EstN; apply nr_lookup_new]).
    assert (GNT : forall off, (s_groups stT) !! (rid, off) = None).
    { intros off. change (s_groups stT) with (s_groups stS). destruct ((s_groups stS) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
      ddestruct PT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
    assert (SHT : (s_shadow stT) !! rid = None) by (change (s_shadow stT) with (s_shadow stS); rewrite SHS; exact FRs).
    assert (ACTT : active stT sc = None).
    { unfold stT, mm_st4. unfold active, ctx, upd_ctx, upd_meta. cbn. change (c_active (s_ctx stS) !! sc) with (active stS sc). rewrite ACTS, (amr_active _ _ _ REL). exact ACT0. }
    assert (TKT : ticks_ok stT).
    { eapply ticks_ok_same; [| | exact TK3]; [change (s_shadow stT) with (s_shadow stS); exact SHS| change (s_tick stT) with (s_tick stS); exact TKS']. }
    pose proof (mm_ai_range stN c size nd mm ltac:(lia) SZ) as AIR.
    eapply evt_cut.
    { replace (Z_to_bv 64 xa) with (Z_to_bv 64 (conc stT (rid, 0))) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; f_equal; lia).
      change (conc stN mm) with (conc stT mm).
      eapply (rtail_walk stT sc c (mm_ai c size) (Z.shiftr nd 12) mm (rid, 0) r0 SC ltac:(lia) AIR ML);
        [eapply meta_slot_same_areas; [| exact MSLN]; reflexivity| exact RECT| exact HrT| reflexivity| cbn; lia| cbn; reflexivity
        | cbn [snd r_len r0]; rewrite RU; lia| apply GNT
        | intros b' gh Hb' Hf'; exfalso; destruct b' as [b1 b2]; cbn in Hf'; subst b1; rewrite GNT in Hb'; discriminate
        | intros o' v t Ho Hc; exfalso; unfold get_shadow in Hc; rewrite SHT in Hc; cbn in Hc; rewrite lookup_empty in Hc; discriminate
        | change (usage stT sc) with (usage stS sc); rewrite US; apply URall
        | exact ACTT| exact TKT| exact MR8| exact MI8]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (s0x & a1x & a2x & a3x & a4x & m9 & -> & MU9 & WM9 & MI9 & MR9 & TK9)).
    assert (GT : conc stT mm = conc st2 mm) by (change (conc stT mm) with (conc stN mm); exact GCN).
    assert (PT : conc stT (rid, 0) = xa) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; lia).
    (* [comment removed for export] *)
    assert (FR9 : rw_cells rsegs m9 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [| exact MU9| exact WM9| unfold rtailW; rewrite GT, PT; unfold RCTX; cbn; rceilb; lia].
      eapply rw_cells_transport; [exact FRz| exact MU8| exact WM8|]. rewrite GCN. unfold RCTX. cbn. rceilb. lia. }
    assert (ST9 : stk rsegs m9 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [| exact MU9| exact WM9| unfold rtailW; rewrite GT, PT; unfold RCTX; cbn; rceilb; lia].
      eapply stk_transport_disjoint; [exact STz| exact MU8| exact WM8| rewrite GCN; unfold RCTX; cbn; rceilb; lia]. }
    eapply evt_cut. { unfold rFRM in FR9. eapply (ras_ret0 sp gp tp); [exact MR9| exact MI9| exact FR9| exact ST9| exact CLO| lia]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1y & a2y & -> & ST10)). apply evt_done.
    rewrite (ag_tail_kq_eq sc k bail stT mm (rid, 0) c (mm_ai c size)); [| rewrite RECT; reflexivity| rewrite RECT; reflexivity| exact ACTT].
    apply HK.
    (* [comment removed for export] *)
    set (ai := mm_ai c size) in *. set (ml := Z.shiftr nd 12) in *.
    set (stF := st_model stT sc c ai mm (rid, 0)).
    assert (C32 : 1 <= c <= 32) by lia.
    assert (EML : nd = 4096 * ml) by (subst ml; rewrite ND12; Z.div_mod_to_equations; lia).
    assert (ML28 : 1 <= ml < 2^28) by lia.
    assert (Hk0 : r_kind r0 = RKGroup) by reflexivity.
    assert (LEN0 : r_len r0 = nd) by reflexivity.
    assert (MST : meta_slot stT mm) by (eapply meta_slot_same_areas; [| exact MSLN]; reflexivity).
    assert (Esz : size = 16 * size_class sc) by reflexivity.
    assert (NDC' : c = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * c + 16 <= nd /\ nd < 16 * size_class sc * c + 16 + 4096).
    { pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 _]. pose proof (round_up_pg_props (size * c + 16) ltac:(nia)) as [N1 _].
      rewrite <- Esz. destruct NDC as [[Ec En]|[LE En]]; [left; split; [exact Ec| rewrite En; lia] | right; split; [exact LE| rewrite En at 1; lia]]. }
    ddestruct (sm_slot_ok stT sc c ai ml mm rid r0 SC C32 AIR ML28 RECT HrT Hk0 SHT GNT req nd RQ FIT LEN0 EML NDR ltac:(lia) NDC' MST) as (SO & STR & S16 & SND).
    fold stF in SO, STR, S16, SND.
    dpose (sm_proj stT sc c ai mm rid) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10).
    fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
    assert (MRF : rmrep stF m9) by (exact (rmrep_st_model stT sc c ai ml mm (rid, 0) SC C32 RECT ltac:(cbn; lia) m9 MR9)).
    assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK9]; reflexivity).
    assert (MSF : meta_slot stF mm) by (apply (proj1 (sm_meta_slot stT sc c ai mm rid mm)); exact MST).
    (* [comment removed for export] *)
    assert (REGT : s_regions stT = <[rid:=r0]> (s_regions stS)) by reflexivity.
    assert (SHT' : s_shadow stT = s_shadow st2) by (transitivity (s_shadow stS); [reflexivity| exact SHS]).
    assert (GRT : s_groups stT = s_groups st2) by (transitivity (s_groups stS); [reflexivity| exact GRS]).
    assert (ART : s_areas stT = s_areas st2) by (transitivity (s_areas stS); [reflexivity| exact ARS]).
    assert (TKT' : s_tick stT = s_tick st2) by (transitivity (s_tick stS); [reflexivity| exact TKS']).
    assert (NRT : s_next_rid stT = N.succ rid) by reflexivity.
    assert (RST : s_reserved stT = s_reserved st2) by (transitivity (s_reserved stS); [reflexivity| exact RSS]).
    assert (BRKT : c_brk (ctx stT) = c_brk (ctx st2)) by (transitivity (c_brk (ctx stS)); [reflexivity| exact BRKS]).
    assert (ACTT' : forall c', active stT c' = active st2 c') by (intros c'; transitivity (active stS c'); [reflexivity| apply ACTS]).
    assert (GF : conc stF mm = conc st2 mm) by (rewrite (sm_conc stT sc c ai mm rid); exact GT).
    assert (HOLD : forall q rq, (s_regions st2) !! q = Some rq -> (s_regions stF) !! q = Some rq /\ q <> rid).
    { intros q rq Hq. assert (NE : q <> rid) by (intros ->; rewrite FRr in Hq; discriminate).
      split; [| exact NE]. rewrite PF1, REGT, lookup_insert_ne, REGS by congruence. exact Hq. }
    assert (MREL0S : forall q rq, (s_regions st0) !! q = Some rq ->
              exists r', (s_regions stS) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
    { intros q rq Hq. destruct (mrel_regions _ _ (er_mrel _ _ ER) q rq Hq) as (r1 & H1 & K1 & B1 & L1). rewrite <- REG1 in H1.
      destruct (amr_regions _ _ _ REL q r1 H1) as (r2 & H2 & K2 & B2 & L2 & _). exists r2. rewrite REGS. repeat split; auto; try congruence. lia. }
    assert (FRESH : forall a, xa <= a < xa + nd -> rfresh_addr st0 a).
    { intros a Ha. eapply (rfresh_addr_anti st0 stS); [| exact MREL0S|].
      - rewrite RS6, <- RS0. exact (mrel_reserved _ _ (er_mrel _ _ ER)).
      - split; [rceilb; lia|]. eapply (ranges_free_sub _ xa nd); [exact XRF| lia| lia| lia]. }
    assert (HFP2 : forall a, rmalloc_fp st0 st2 lo (bv_unsigned sp) a -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
    { intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros q rq Hq. exists rq. split; [apply (proj1 (HOLD q rq Hq))|]. repeat split; auto. lia. }
    (* [comment removed for export] *)
    assert (OLDW : forall q rq off, (s_regions st2) !! q = Some rq -> r_kind rq = RKGroup -> 0 <= off < round_up_pg (r_len rq) ->
              m9 (wa (r_base rq + off)) = m3 (wa (r_base rq + off))).
    { intros q rq off Hq Hk Ho.
      assert (HqS : (s_regions stS) !! q = Some rq) by (rewrite REGS; exact Hq).
      destruct (WR6 _ _ HqS) as (R0 & _ & _ & RC & _). rceilb.
      ddestruct (rregion_facts st2 m3 q rq MR3 Hq) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
      ddestruct (rmeta_chunk_facts st2 m3 mm MR3 MSL) as (_ & _ & _ & _ & _ & GRG & _). pose proof (GRG q rq Hq Hk) as GRq.
      pose proof (In_live_ranges stS q rq HqS) as HIq. unfold region_live_range in HIq. rewrite Hk in HIq.
      pose proof (ranges_free_In _ _ _ _ _ XRF HIq) as DJq.
      pose proof (lr_lo_group rq Hk) as LRq.
      (* [comment removed for export] *)
      transitivity (m8 (wa (r_base rq + off))). { apply MU9. rewrite wa_unsigned by (clear - Ho R0 RC RCB; lia). unfold rtailW. rewrite GT, PT. cbn. unfold RCTX. clear - Ho R0 RC RI2 GRq DJq SC SND S16 RCB; lia. }
      transitivity (mz (wa (r_base rq + off))). { apply MU8. rewrite wa_unsigned by (clear - Ho R0 RC RCB; lia). rewrite GCN. cbn. unfold RCTX. clear - Ho R0 RI2 GRq; lia. }
      transitivity (m6 (wa (r_base rq + off))). { apply ZO; [clear - Ho R0 RC RCB; lia | clear - Ho R0 DJq; lia]. }
      transitivity (m4 (wa (r_base rq + off))). { apply MU6. rewrite wa_unsigned by (clear - Ho R0 RC RCB; lia). cbn. clear - Ho R0 RC CLO' LO ASG RCB; lia. }
      apply MU4. rewrite wa_unsigned by (clear - Ho R0 RC RCB; lia). unfold rseqW, RCTX. cbn. clear - Ho R0 RI2; lia. }
    assert (UAF : unk_agree stF o m9).
    { eapply (unk_agree_transfer st2 stF o m3 m9 UA3). intros q rq Hq Hk.
      rewrite PF1, REGT, REGS in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      - right. rewrite lookup_insert_eq in Hq. inversion Hq; subst rq. cbn [r_len r_base]. intros off h Ho Hc.
        rewrite (sm_cell_read stT sc c ai mm rid SHT off ltac:(lia)) in Hc.
        destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T. apply (sm_grp_hdr_cov stT sc c ai mm rid SC). lia.
      - left. rewrite lookup_insert_ne in Hq by congruence.
        split; [exact Hq|].
        split. { rewrite (sm_shadow_other stT sc c ai mm rid q NE). unfold get_shadow. rewrite SHT'. reflexivity. }
        split. { intros off X. apply (sm_grp_hdr_cov_old stT sc c ai mm rid GNT). eapply rgrp_hdr_cov_same; [exact GRT| exact X]. }
        intros off h Ho Hc NG. exact (OLDW q rq off Hq Hk Ho). }
    assert (PE09 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m9).
    { eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE04| exact HFP2]. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. left. left. lia. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. do 4 right. apply FRESH. lia. }
      eapply rpres_except_trans.
      { eapply rpres_except_of_munch; [exact MU8| exact WM8|]. intros a Ha NC. rewrite GCN. cbn. split; [|split; [|exact I]]; intros X; apply NC.
        - left. do 3 right. ddestruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
          dexists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
        - left. right. right. left. unfold RCTX in *. lia. }
      eapply rpres_except_of_munch; [exact MU9| exact WM9|]. intros a Ha NC. unfold rtailW. rewrite GT, PT. cbn.
      split; [|split; [|split; [|split; [|exact I]]]]; intros X; apply NC.
      - left. right. right. left. unfold RCTX in *. lia.
      - left. do 3 right. ddestruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
        dexists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
      - do 4 right. apply FRESH. lia.
      - left. right. right. left. unfold RCTX in *. lia. }
    assert (ERR9 : rw_cells rsegs m9 (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [| exact MU9| exact WM9|].
      - eapply rw_cells_transport; [exact ERRz| exact MU8| exact WM8|]. rewrite EA, GCN. cbn. unfold RCTX. lia.
      - unfold rtailW. rewrite GT, PT, EA. cbn. unfold RCTX. lia. }
    unfold ras_post2.
    deexists 14. dexists m9, errv'. split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST10|]. split; [exact ERR9|].
    split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m9); [exact MRF| exact AUX| exact PE09| exact CLO| lia]|].
    split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE09|].
    split. { split.
      - intros q rq Hq. rewrite <- REG1 in Hq. destruct (amr_regions _ _ _ REL q rq Hq) as (r' & H' & K' & B' & L' & _).
        exists r'. split; [apply (proj1 (HOLD q r' H'))|]. repeat split; auto.
      - rewrite PF6, NRT. pose proof (amr_next_rid _ _ _ REL) as NX1. pose proof (tr_next _ _ _ TR) as NX0. subst rid. rewrite NRS. lia.
      - rewrite PF7, RST, (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
    split. { unfold brk_link_ps in BL2 |- *. rewrite PF8, BRKT. destruct (c_brk (ctx st2)) as [| |brid boff] eqn:EB; auto.
             rewrite (sm_conc stT sc c ai mm rid). rewrite <- (CONCS (brid, boff)) in BL2.
             replace (conc stT (brid, boff)) with (conc stS (brid, boff)); [exact BL2|].
             change (conc stT (brid, boff)) with (conc stN (brid, boff)). rewrite EstN. symmetry. apply nr_conc. cbn [fst].
             ddestruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite BRKS in P7. first [rewrite EB in P7; exact P7 | exact P7]. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite (sm_active stT sc c ai mm rid). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite ACTT', (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ART. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF5, TKT', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros _ rid' S len RS o' v t Ho Hc. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        rewrite (sm_cells_none stT sc c ai mm rid SHT) in Hc. discriminate.
      - intros _ _ rid' S len RS o' Ho. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        split; [apply (sm_cells_none stT sc c ai mm rid SHT)|].
        split; [apply (sm_hav_none stT sc c ai mm rid SHT); lia| apply (sm_havp_none stT sc c ai mm rid SHT)].
      - (* [comment removed for export] *)
        intros _ g' b' HA' Hmem' _. rewrite (sm_active stT sc c ai mm rid), Z.eqb_refl in HA'. injection HA' as <-.
        rewrite (sm_rec_mt stT sc c ai ml mm rid SC C32 RECT) in Hmem' |- *.
        cbn [m_mem sm_rec] in Hmem'. injection Hmem' as <-. cbn [fst snd].
        intros o' Ho'. split; [apply (sm_cells_none stT sc c ai mm rid SHT)|].
        split; [apply (sm_hav_none stT sc c ai mm rid SHT); lia| apply (sm_havp_none stT sc c ai mm rid SHT)]. }
    split. { rewrite PF9, CTR8. unfold u32. Z.div_mod_to_equations. lia. }
    right. split; [lia|]. dexists mm, (rid, 0), r0.
    split; [rewrite (sm_active stT sc c ai mm rid), Z.eqb_refl; reflexivity|]. split; [exact SO|]. split.
    + intros a Ha. replace (r_base r0) with xa in Ha by reflexivity. cbn [fst snd] in Ha. do 4 right. apply FRESH. rewrite Z.mul_0_r in Ha. lia.
    + intros _. cbn [fst snd]. replace (0 + (16 + get_stride (get_meta_rec stF mm) * 0) + -3) with 13 by lia.
      apply (sm_rdv stT sc c ai mm rid SHT).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End LEVEL.

End RP_1.
