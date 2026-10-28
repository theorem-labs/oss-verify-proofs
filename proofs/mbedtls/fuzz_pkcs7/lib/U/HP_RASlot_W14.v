(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W3 ASlot_W14.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3 HP_RF_ntf_A HP_RASlot_W2 HP_RASlot_W4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_W14 () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.lxor"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_cells"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.pair"; "Stdlib.NArith.BinNat.N.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_tick"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RP_1.TAIL.rtailW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W14.stFin"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L11607865080.5000005S1a1b". (* [comment removed for export] *)
#[using="hRP"] Lemma sx32_congr (a : word) (b : Z) : bv_unsigned a mod 2^32 = b mod 2^32 -> sx32 a = wz (sxv b).
Proof. rceilb.
  intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia.
  f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L2592056153.3000001S". (* [comment removed for export] *)
#[using="hRP"] Lemma unsigned_mod32_pred_sxv y : bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv y)) + -1)) mod 2^32 = (y - 1) mod 2^32.
Proof. rceilb.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
  rewrite (mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal. 
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L20913760734.5L2592056153.4 L38715876989.5L39165928090.500000500600700=S1a1bSSS1b2RB". (* [comment removed for export] *)
#[using="hRP"] Lemma unsigned_mod32_swrap_add_not a b : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W14 ()) "(0.$1.(2.(3.&40.(4.&40.(5.(6.&20.O2.)(7.(3.&40.(8.(9.O1.)))+????????????????.))))(:.+2.+20.))(2.(;.(;.O2.+1.)O1.)(:.+2.+20.)))")
(* [comment removed for export] *).
Proof. rceilb.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (mod_mod_pow2 _ 32 64) by lia.
  pose proof (sxv_range b) as RB.
  rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
  replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
  rewrite Z.mod_add by lia.
  unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
  assert (Hx : x = (a + 2^31) mod 2^32) by reflexivity. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by reflexivity.
  clearbody x y. Z.div_mod_to_equations. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L14880337059.4L63368323942.4000006007S1x2HxS". (* [comment removed for export] *)
#[using="hRP"] Lemma land224_m32 x : 0 <= x < 256 -> Z.land x 224 = Z.land x 18446744073709551584.
Proof. rceilb.
  intros Hx. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
  rewrite <- !Z.land_assoc. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W14 ()) "Pb',(<.$=.$1.)Pgh,$>.P,(0.(?.$>.)(10.(<.$=.$1.)$>.(11.$12.(13.$=.$14.$1.$15.)(16.$=.$14.$17.$1.$15.$18.)$>.)(19.$12.(13.$=.$14.$1.$15.)(16.$=.$14.$17.$1.$15.$18.)$>.)R2.(1:.VstT,))(1;.$>.R1.))P,(0.$=.(1<.$=.$1.R3.)(1<.$=.$1.Vp,))(1=.(1>.(5.(1?.$=.$1.R4.)+9.)(1?.$=.$1.Vp,))(1>.(5.(1?.$=.$1.Vp,)+9.)(1?.$=.$1.R4.)))")
(* [comment removed for export] *).
Hypothesis OLD12 : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W14 ()) "Po,$1.Pv,$1.Pt,$=.P,(20.(1>.(1?.$=.$1.Vp,)R3.)(21.R3.(5.(1?.$=.$1.Vp,)+<.)))P,(0.(?.(<.$1.$=.))(10.$1.(<.$1.$=.)(11.$1.$15.$18.(<.$1.$=.))(19.$1.$15.$18.(<.$1.$=.))R4.(22.(23.VstT,(1<.$=.$1.Vp,))))(1;.(<.$1.$=.)(24.$1.$=.R3.R2.)))(25.R3.(26.VstT,))")
(* [comment removed for export] *).
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

(* [comment removed for export] *)
Definition rtailW : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W14 ()) "(27.(<.$1.$1.)(24.$1.$1.(5.(5.$28.+1=0.)(29.+8.Vsc,))(5.(5.(5.$28.+1=0.)(29.+8.Vsc,))+8.))(27.(<.$1.$1.)(24.$1.$1.VG,(5.VG,+28.))(27.(<.$1.$1.)(24.$1.$1.VP,(5.VP,+9.))(27.(<.$1.$1.)(24.$1.$1.(5.(5.$28.+50.)(29.+8.Vsc,))(5.(5.(5.$28.+50.)(29.+8.Vsc,))+8.))(2:.(<.$1.$1.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "01I0@L10248308338.111L10250732959.111L10350858658.113L10350858658.114L10423411451.111L12578249668.88 L12578657236.99 L12942117097.111L13733556894.111L14285882357.111L15272293356.108L15278696208.109L17212679867.111L17684931484.104L17687372726.103L17699624332.78 L17723711466.80 L17723711466.86 L19387628895.108L19387628895.113L19704384439.111L20545844496.79 L21016498704.104L21016498704.110L22067004187.111L25381642938.88 L2589713875.111 L26794244518.103L2740098216.112 L28900772779.108L2912153760.104 L29317317366.103L29321854076.108L29330713501.99 L2939895369.108 L2950332137.107 L29749124343.107L29749137657.77 L30163643147.181L30267903917.84 L31220622482.84 L32152749536.111L33178051695.111L34126991106.79 L34127416987.77 L34127430657.77 L38480705517.119L42333700063.104L42360909120.88 L43835677707.111L44732114796.108L44744366566.103L45083264315.111L46495093594.111L47701757476.78 L48052304414.111L48817211143.111L49702840724.109L49702840724.79 L49962465963.111L51271146707.103L51860072732.88 L52163693840.109L52530479858.118L52564885613.109L52564885613.79 L52567164907.108L56275666029.107L56275685091.112L56284736507.84 L56284884342.103L56286811819.111L56945583962.86 L57862605606.103L58652168863.114L58915522346.86 L59148686920.103L59310614929.112L59314873579.122L59314938599.121L59314938599.124L60246374218.107L61389063540.107L6231855609.116 L63353258869.104L63363773797.78 L63964887643.111L7442899475.111 L8927523831.111 00000k01f03?04X05d06Y07m08e09a0:h0;X0<N0=F0>?0?80?g0@J0A30Ak0Bc0Cn0D`0FB0Go0Hg0Ia0JY0K?0L=0Lm0Mi0NO0O<0PU0QF0R70S20SX0UE0Uh0VO0WG0XB0Xi0YL0Yo0[00[\0\f0]b0^b0_[0`S0aK0an0c70d20e=0eo0g60gb0hH0iS0jB0k>0ke0lX0mP0nH0no0oY10U11K12512612`13L14n16<17P19G1:?1;71<81=11=`1>X1?S1@^S3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2SC2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2SC2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P04PEND2v32v42y83nbv2GI2G42R43AVR4LACT2HB5Ha_st5Hl_stS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P04PEND2v32v42y83nbv2GI2G42R43AVR4LACT2HB5Ha_st5Hl_stS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2ML2P02v32v42y83nbv4Gpos2R43AVR4LACT1W2EWS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v44Gpos2R42CP3AVRS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v44Gpos2R42CP3AVR2y02y12y22y32y42y52y62y72y83LHBS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv3AVR4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2SC2P02v32v42y83nbv4Gpos2R43AVR4LACTS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv2HBS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv2HB5Ha_stS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2AI2P02v32v44Gpos2R43AVRS3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2AI2P02v32v44Gpos2R43AVRS3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2AI2P04Gpos2R4S3stT3cnt2ai2ml2mt1p1r1G1P2AV2FR2P0S3stT3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v4S3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2SC3CNT2P02v32v42y83nbv4Gpos2R43AVR4LACTS3stT2sc3cnt2ai2mt1p1r1G1P2AV2FR2SC2P04Gpos2R43LENS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P03P164PEND2v32v44Gpos2GI2G42R43RAL3RI13RI22CP3AVR2GX2HB5Ha_st5Hl_stS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P03P164PEND2v32v42y83nbv4Gpos2GI2G42R43RAL3RI13RI22CP3AVR2GX3W8R2HB5Ha_st5Hl_stS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P04PEND2v32v44Gpos2R42CP3AVRS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v4S3stT3cnt2ai2mt1p1r1G1P2AV2FR2P04PEND2v32v42y83nbv4Gpos2R43AVRS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv2HBS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v44Gpos2R43AVR2y82Y83L8RS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v4S3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbvS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P04PEND2v32v44Gpos2R42CP3AVR2y02y12y22y32y42y52y62y72y83LHBS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv3W8RS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv3W8RS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2SC2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2mt1p1r1G1P2AV2FR2SC2P0S3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P04PEND2y83nbv2GI3RI13RI23AVR4AV1R2GX4LACT1q2r02r21H2H02q02r12H42H52q12H9S3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v3S3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2P02v3S3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2ML2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2mt1p1r1G1P2AV2FR2P03LENS3stT2sc3cnt2ai2mt1p1r1G1P2AV2FR2P0S3stT2sc3cnt2ai2mt1p1r1G1P2AV2FR2P0S3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4Gpos2R42CP3AVR1a2HaS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y82Y8S3stT3cnt2ai2mt1p1r1G1P2AV2FR2P03P164PEND2v32v44Gpos2R43RAL3RI13RI22CP3AVRS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR3CNT2P02v32v42y83nbv4LACTS3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2AI2P02v32v42y83nbv4Gpos2R43AVRS3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2AI2P02v32v44Gpos2R43AVRS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2mt1p1r1G1P2AV2FR2P0S3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4Gpos2R43AVR4AV1R4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2ML2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2SC2P02v32v42y83nbv4Gpos2R43AVR4LACT3LENS3stT2sc3cnt2ai2mt1p1r1G1P2AV2FR2SC2P04Gpos2R43LENS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2ML2P02v32v42y83nbv4Gpos2R43AVR4LACTS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y82Y8S3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v4S3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2SC2P02v32v42y83nbv4Gpos2R43AVR4LACT3LENS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv1aS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACT3LENS3stT2sc3cnt2ai2mt1p1r1G1P2AV2FR2P03LENS3stT2sc3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv2HBS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2P02v3S3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2P02v32v4S3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR3CNT2P02v32v42y83nbv4LACTS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v44Gpos2R43AVR3FRRS3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2P02v32v4FS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v43AVRS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y82Y8S3stT3cnt2ai2mt1p1r1G1P2AV2FR2P04PEND2v32v42y83nbv4Gpos2GI2R43RI22CP3AVR2GX1a2Ha2X12X22X32X42X52X6S3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4Gpos2R42CP3AVR1a2Ha1b2Rb2Cb2EQ1HS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4Gpos2R42CP3AVR1a2Ha2rq2Rq3LRr1D4PEND1HS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4Gpos2R42CP3AVR3FRR1a2Ha2ak3Rak3LRr3rga2Ca3Sa11D4PEND1H1b2Rb2rb2Cb3Sb13Sb0S3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT3cnt2ai2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4Gpos2R42CP3AVR1a2HaS3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2AI2P02v32v44Gpos2R43AVRS3stT3cnt2ai2mt1p1r1G1P2AV2FR3CNT2AI2P04Gpos2R4S3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2SC2P02v32v42y83nbv4LACTS3stT2sc3cnt2ai2ml2mt1p1r1G1P2AV2FR2SC3CNT2P02v32v42y83nbv4Gpos2R43AVR4LACT". (* [comment removed for export] *)
#[using="r AV FR SC CNT AI ML MST REC Hr Hk P0 P16 PEND GNONE NOGRP OLD12 UR ACT TK"] Lemma rtail_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W14 ()) "Pra,(2;.&40.)Psp,(2;.&40.)Pgp,(2;.&40.)Ptp,(2;.&40.)Pt0,(2;.&40.)Pt1,(2;.&40.)Pt2,(2;.&40.)Pa3,(2;.&40.)Pa4,(2;.&40.)Pa5,(2;.&40.)Pa6,(2;.&40.)Pa7,(2;.&40.)Ps2,(2;.&40.)Ps3,(2;.&40.)Ps4,(2;.&40.)Ps6,(2;.&40.)Ps8,(2;.&40.)Ps10,(2;.&40.)Ps11,(2;.&40.)Pt3,(2;.&40.)Pt4,(2;.&40.)Pt5,(2;.&40.)Pt6,(2;.&40.)PF,(2<.&5.(2;.&40.))Pfc,(2;.&20.)PmC,P,(2;.&40.)(?.(2;.&8.))P,(2=.VhRP,VstT,R1.)P,(2>.$2?.R2.)(30.$2?.Lms',$31.(32.(2;.&40.)Ls0',(2;.&40.)(32.(2;.&40.)La1',(2;.&40.)(32.(2;.&40.)La2',(2;.&40.)(32.(2;.&40.)La3',(2;.&40.)(32.(2;.&40.)La4',(2;.&40.)(32.P,(2;.&40.)(?.(2;.&8.))Lm',P,(2;.&40.)(?.(2;.&8.))(20.(0.$31.R7.(33.(34.R23.R22.R21.R20.R1?.R1>.R1=.R6.(4.&40.VG,)(4.&40.=)R5.R4.R3.R2.R1:.R19.R18.R17.R16.R15.(4.&40.(5.(5.$28.+50.)(29.+8.Vsc,)))R14.(4.&40.(5.$35.(29.+8.Vsc,)))R13.(4.&40.Vcnt,)R12.R11.R10.R?.R>.R=.)R<.(4.&40.+41138.)R;.(36.(2;.&40.))R1.(37.$2?.)))(20.(38.$39.R:.R1.)(20.(3:.$2?.R:.R1.)(20.(2>.$2?.R1.)(20.(2=.VhRP,(3;.VstT,Vsc,Vcnt,Vai,Vml,Vmt,Vp,)R1.)(3<.(3;.VstT,Vsc,Vcnt,Vai,Vml,Vmt,Vp,)))))))))))))(33.(34.R1<.R1;.R1:.R19.R18.R17.R16.(4.&40.Vsc,)(4.&40.VG,)(4.&40.VP,)(4.&40.(;.Vcnt,+1.))(4.&40.Vai,)R15.R14.R13.R12.R11.R10.R?.R>.(4.&40.(5.(5.$28.+50.)(29.+8.Vsc,)))R=.(4.&40.(5.$35.(29.+8.Vsc,)))R<.(4.&40.Vcnt,)R;.R:.R9.R8.R7.R6.)R5.(4.&40.+40?>0.)R4.(36.(2;.&40.))R3.(37.$2?.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until mC. intros MR MI.
  pose proof (munch_refl rtailW mC) as MU. pose proof (wmono_refl rsegs mC) as WM. unfold rtailW in MU.
  dpose (rmeta_slot_bounds stT mC mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  dpose (rregion_facts stT mC (fst p) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). rceilb.
  assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; exact Hr).
  dpose (AV_FR_range stT cnt ai mt p CNT AI P0) as (AVR & FRR & AV1R). fold AV in AVR, AV1R. fold AV FR in FRR.
  (* [comment removed for export] *)
  destruct (rmrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold (stA stT p) in MRA, TKA.
  rceilb; unfold RCTX, RMLOCK in *.
  (* [comment removed for export] *)
  pose proof (rmrep_usage_read (stA stT p) mC sc (wa (512968 + 464 + 8 * sc)) MRA SC eq_refl) as RDU.
  change (usage (stA stT p) sc) with (usage stT sc) in RDU.
  replace (wa (512968 + 464 + 8 * sc)) with (Z_to_bv 64 (512960 + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
  step. clear RDU.
  (* [comment removed for export] *)
  step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.
  (* [comment removed for export] *)
  dpose MRA as (_ & (_ & _ & USG & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (usages (stA stT p)) sc (wa (512968 + 464 + 8 * sc)) USG
                ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
  replace (wa (512968 + 464 + 8 * sc)) with (Z_to_bv 64 (512960 + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_usage (stA stT p) mX sc (usage stT sc + cnt) MRA SC) as MRB; unfold RCTX in MRB; fold (stB stT sc cnt p) in MRB end.
  rraw_store_finish0 (512968 + 464 + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
  assert (TKB : ticks_ok (stB stT sc cnt p)) by exact TKA.
  assert (MSTB : meta_slot (stB stT sc cnt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRA TKA.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit ai) by lia. rewrite ASlot_W14.sllw2_word by lia.
  step.
  set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
  rmchunk MRB MSTB CH. change (conc (stB stT sc cnt p) mt) with G in CH. change (get_meta_rec (stB stT sc cnt p) mt) with (get_meta_rec stT mt) in CH.
  rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
  replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
  rmeta_open G MUa WMa.
  (* [comment removed for export] *)
  step. step.
  assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
  { subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
  rewrite (sx32_congr v3 AV V3).
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite ASlot_W14.sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
  step. step.
  set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
  assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
  { subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }
  (* [comment removed for export] *)
  step. step.
  lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRC : rmrep (stC stT sc cnt ai ml mt p) mX);
    [ eapply rmrep_put_meta_frame; [exact MRB| exact MSTB| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
      unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
      change (conc (stB stT sc cnt p) p) with P; unfold wz at 3 4;
      rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
      rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
      replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
    | clear MUa WMa; rename H into CH1 ] end.
  assert (TKC : ticks_ok (stC stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stB stT sc cnt p) mt (fun _ => recA cnt ai ml p) TKB)).
  assert (MSTC : meta_slot (stC stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRB TKB MSTB.
  (* [comment removed for export] *)
  dpose MRC as (WFC & _ & _ & _ & _ & SHC). dpose WFC as (_ & _ & DJ & _ & WG).
  destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    destruct (rwr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia)) as (hb & LHB & HB) end.
  destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (HDR : rw_cells rsegs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
    [ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| exact HB| cbn; eapply wr_at_sub; [exact WR| lia| lia]]
    | clear HB LHB ] end.
  pose proof (rmeta_chunk_facts (stC stT sc cnt ai ml mt p) _ mt MRC MSTC) as (_ & _ & _ & _ & _ & GRG & _).
  pose proof (GRG (fst p) r Hr Hk) as GX. change (conc (stC stT sc cnt ai ml mt p) mt) with G in GX. clear GRG.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.
  (* [comment removed for export] *)
  step.
  (* [comment removed for export] *)
  step.
  pose proof (byte_range y8) as Y8.
  step. unfold zxb.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit ai) by lia.
  replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
  replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
  step.
  pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
  rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
  rewrite (land224_m32 (bv_unsigned y8)) by lia.
  pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].
  (* [comment removed for export] *)
  set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
  step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells rsegs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    rename H into HDR2;
    assert (MRC2 : rmrep (stC stT sc cnt ai ml mt p) mX);
    [ eapply (rmrep_transport_unowned _ _ _ _ MRC MUb WMb)
    | assert (MRD : rmrep (stD stT sc cnt ai ml mt p) mX);
      [ eapply (rmrep_put_group_new (stC stT sc cnt ai ml mt p) mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
        [ change (conc (stC stT sc cnt ai ml mt p) p) with P; unfold pw, wz; cbn [oconc]; change (conc (stC stT sc cnt ai ml mt p) mt) with G; exact HDR2
        | rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
      | ] ] end.
  { (* [comment removed for export] *)
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
    destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
    - unfold RCTX in X1. lia.
    - unfold RMLOCK in X2. lia.
    - unfold RNEED_LOCKS in X3. lia.
    - unfold RPAGE_SIZE in X4. lia.
    - change (s_areas (stC stT sc cnt ai ml mt p)) with (s_areas stT) in Hak. change (conc (stC stT sc cnt ai ml mt p) ak) with (conc stT ak) in Rak.
      ddestruct (rarea_conc stT ak ar WFC Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; exact Hk).
      pose proof (rarea_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
    - change (s_groups (stC stT sc cnt ai ml mt p)) with (s_groups stT) in Hb. change (conc (stC stT sc cnt ai ml mt p) b) with (conc stT b) in Rb.
      ddestruct (rgroup_conc stT b gh WFC Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
      + rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
      + pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
    - change (s_regions (stC stT sc cnt ai ml mt p)) with (s_regions stT) in Hq. change (get_shadow (stC stT sc cnt ai ml mt p) q) with (get_shadow (hdr_havoc p stT) q) in Cq.
      destruct (N.eq_dec q (fst p)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
                    ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| exact Hc])) as [h Hh].
        replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
    - unfold RGOT_SSP in X5. lia.
    - unfold RSSP_GUARD in X6. lia. }
  clear MRC MRC2 MUb WMb HDR2.
  assert (TKD : ticks_ok (stD stT sc cnt ai ml mt p)) by exact TKC.
  assert (MSTD : meta_slot (stD stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear TKC MSTC.
  (* [comment removed for export] *)
  dpose MRD as (_ & (_ & ACTS & _) & _). pose proof (actives_length (stD stT sc cnt ai ml mt p)) as LACT. unfold RCTX in ACTS.
  rmchunk MRD MSTD CH.
  change (get_meta_rec (stD stT sc cnt ai ml mt p) mt) with (get_meta_rec (put_meta mt (recA cnt ai ml p) (stB stT sc cnt p)) mt) in CH. rewrite get_meta_rec_put_same in CH.
  unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
  change (conc (stD stT sc cnt ai ml mt p) mt) with G in CH. change (conc (stD stT sc cnt ai ml mt p) p) with P in CH. unfold wz in CH.
  set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
  rmeta_open G MUc WMc.
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (unsigned_lit sc), Z.shiftl_mul_pow2, (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
  replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
  rewrite (unsigned_lit W), EW, land_pg_mask by lia.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
  replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
  step. rewrite ?unsigned_lit by lia.
  (* [comment removed for export] *)
  step. step. step. step.
  rewrite ?(unsigned_lit (mask_upto ai)) by lia.
  (* [comment removed for export] *)
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  lazymatch goal with H : u64arr rsegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read rsegs mX (512968 + 80) (actives (stD stT sc cnt ai ml mt p)) sc (pw (stD stT sc cnt ai ml mt p) (active (stD stT sc cnt ai ml mt p) sc)) (wa (512968 + 80 + 8 * sc)) H
                  (actives_nth (stD stT sc cnt ai ml mt p) sc SC) ltac:(lia) eq_refl) as RDA end.
  change (active (stD stT sc cnt ai ml mt p) sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
  replace (wa (512968 + 80 + 8 * sc)) with (Z_to_bv 64 (513048 + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  step. step. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRE : rmrep (stE stT sc cnt ai ml mt p) mX);
    [ eapply rmrep_put_meta_frame; [exact MRD| exact MSTD| exact MUc| exact WMc|];
      eapply rw_cells_congr; [| | | exact H]
    | clear MUc WMc; rename H into CH3 ] end.
  { unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
    change (conc (stD stT sc cnt ai ml mt p) mt) with G. change (conc (stD stT sc cnt ai ml mt p) p) with P.
    unfold wz. rewrite !app_nil_r.
    rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
    2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
        rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
        fold AV. Z.div_mod_to_equations. lia. }
    do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
  { reflexivity. }
  { cbn. tauto. }
  assert (TKE : ticks_ok (stE stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stD stT sc cnt ai ml mt p) mt (fun _ => recF sc cnt ai ml mt p) TKD)).
  clear MRD TKD MSTD.
  (* [comment removed for export] *)
  clear CH3.
  lazymatch goal with H : u64arr rsegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_store_ok rsegs _ _ (actives (stD stT sc cnt ai ml mt p)) sc (wa (512968 + 80 + 8 * sc)) H
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
  replace (wa (512968 + 80 + 8 * sc)) with (Z_to_bv 64 (513048 + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
  st1.
  replace (Z_to_bv 64 (513048 + 8 * sc + 0)) with (Z_to_bv 64 (513048 + 8 * sc)) in SOK by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active (stE stT sc cnt ai ml mt p) mX sc (Some mt) MRE SC) as MRF; unfold RCTX in MRF; fold (stFin stT sc cnt ai ml mt p) in MRF end.
  unfold pw in MRF. cbn [oconc] in MRF. change (conc (stE stT sc cnt ai ml mt p) mt) with G in MRF.
  rraw_store_finish0 (512968 + 80 + 8 * sc) (le8 (wz G)) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. deexists 6. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MRF| exact TKE].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End TAIL.

End RP_1.
