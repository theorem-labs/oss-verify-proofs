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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W13 ASlot_W14.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RF_enframe HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3 HP_RF_ntf_A HP_RASlot_W2 HP_RASlot_W4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_W13 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_mmap_counter"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSIZE_CLASSES"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W13.enf0_st"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B3.mw_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.wr8"; "Corelib.Numbers.BinNums.N"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.put_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_set_maplen"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "Stdlib.ZArith.BinInt.Z.of_nat"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.zero_hdrs"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W13.pp"; "Corelib.Init.Logic.not"; "stdpp.bitvector.definitions.bv_unsigned"].


Section RP_1. Context {hRP : run_params}.
Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0140@L10111032552.138L11001238666.109L11346227496.126L12386942782.137L12469719428.102L12500281287.109L13420867460.110L13741319058.109L14441175308.110L15032630530.128L15045277887.99 L15045313671.133L15045327164.135L15924110264.72 L16075640310.109L18430873143.126L18586226854.98 L18586460167.72 L19115144436.129L19117371902.109L19791315888.71 L25502962731.109L26490969648.109L266030272.134  L266318588.109  L26914067086.101L29058364952.138L29784349922.109L32293007892.109L32954866046.109L33541783213.138L3368132505.109 L33963241778.128L39324933350.132L40585632617.131L40599985367.109L40825494482.109L41363450870.109L41417922635.101L42780602088.138L48873143625.109L49240332307.109L5074042873.113 L51040854222.109L51845217405.70 L52442112502.109L53282644823.99 L55254191693.135L59221213243.109L5923435527.102 L59850646544.109L60596971681.102L63201948033.110L63370345143.126L65035251716.129L65099046073.109L6533306074.100 L65655732996.102L66572798628.109L66862733303.126L6753459898.100 L6755768962.109 L68406318709.129L68569706905.109L7568758333.138 L8528370589.73  L8534778781.98  L9967737798.109 00000f01Q02403203U04M05005e06H07907\08M09>09a0:H0;10;X0<;0=00=W0>>0>g0?d0@X0A>0Aa0Bf0CI0CJ0Co0EF0En0F_0G[0H[0IJ0Im0JT0K70L<0Lm0N:0Nh0Ni0OH0P30PV0QR0QS0R<0Rk0ST0T;0Td0UU0V<0V_0WB0Wi0XR0Y50YX0ZM0[90\P0]30]Z0^=S2st1g1b3idx1j2mr6stride1B1P1N2B02x32x22x11G4off04FSTrS2st1g1b3idx1j2mr6stride1B1P1N2B03S163SZR1GS2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b3idx1j2mr6stride1B1P1N2B03S163STN2x32x22x11G4off04FSTrS2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1o1g1b3idx1j2mr6stride1B1P1N2B03S162x22x12E11G2X22X1S2st1g1b3idx1j2mr6stride1B1P1N2B01GS3hRP2st1g1b3idx1j2mr6stride1B1P1N3RCB2B03S161G2G02GCS2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b3idx1j2mr6stride1B1P1N2B02x32x22x11G4off0S2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b3idx1j2mr6stride1B1P1N2B02x32x22x11G4off0S2st1g1b3idx1j2mr6stride1B1P1N2B02x32x22x11G4off0S2st1b3idx1j2mr6stride1B1P1N2B03IDXS2st1g1b3idx1j2mr6stride1B1P1N3CTR2B01GS2st1g1b3idx1j2mr6stride1B1P1N2B01G2x22x1S2st1g1b3idx1j2mr6stride1B1P1N2B03S161GS2st1b3idx1j2mr6stride1B1P1N2B03S16S2st1g1b3idx1j2mr6stride1B1P1N2B03STN2x32x22x11G4off0S2st1g1b3idx1j2mr6stride1B1P1N2B03STN1GS2st1b3idx1j2mr6stride1B1P1N2B03S163SZRS2st1g1b3idx1j2mr6stride1B1P1N2B02x31G2X3S3hRP2st1g1b1r3idx1j2mr6stride1B1P1N3RCB2B03S165SPAN12CB2RC1GS2st1g1b3idx1j2mr6stride1B1P1N2B02NR2x32x22x11G4off0S2st1g1b3idx1j2mr6stride1B1P1N2B02NR1GS2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b1r3idx1j2mr6stride1B1P1N2B03S162x32x22x12CB2R41G2SK4off04FSTrS2st1g1b3idx1j2mr6stride1B1P1N2B01GFS2st1g1b3idx1j2mr6stride1B1P1N1J2B01GS3hRP2st1g1b1r3idx1j2mr6stride1B1P1N3RCB2B03S163STN2NR2x32x22x12CB2RC1G4off05SPAN24FSTrS2st1g1b3idx1j2mr6stride1B1P1N2B01G4SCR0S2st1g1b3idx1j2mr6stride1B1P1N2B02x32x22x11G4off0S2st1g1b3idx1j2mr6stride1B1P1N2B03S163STN2x32x22x11G2SK4off0S2st1g1b3idx1j2mr6stride1B1P1N2B03IDX3S162x32x22x11G2SK3LI04off0S2st1g1b3idx1j2mr6stride1B1P1N2B03IDX3S161G3LI0S2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b3idx1j2mr6stride1B1P1N3CTR2B01GS2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b1r3idx1j2mr6stride1B1P1N2B03S162x32x22x12CB2R41G2SK4off04FSTrS2st1g1b3idx1j2mr6stride1B1P1N1J3SCg2B03S161G3LI0S2st1g1b1r3idx1j2mr6stride1B1P1N2B04SPAN3S165SPAN12CB3RI11G3GI13GI22GR2SK3LI0S2st1g1b3idx1j2mr6stride1B1P1N2B03S161G4off'1HFS2st1b3idx1j2mr6stride1B1P1N2B0S2st1g1b3idx1j2mr6stride1B1P1N2B03S163STN1GS2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b3idx1j2mr6stride1B1P1N2B03S163STN2x32x22x11G2SK4off0FS2st1g1b3idx1j2mr6stride1B1P1N2B02x21G2X2S2st1g1b1r3idx1j2mr6stride1B1P1N2B03S162CB2R41GS2st1g1b3idx1j2mr6stride1B1P1N2B02x11G2X1S2st1g1b3idx1j2mr6stride1B1P1N2B03SZR1GS2st1g1b3idx1j2mr6stride1B1P1N2B01G2x22x1S2st1g1b3idx1j2mr6stride1B1P1N2B02x32x22x11G4off0S2st1g1b3idx1j2mr6stride1B1P1N2B01G3FB0S2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b3idx1j2mr6stride1B1P1N2B03SZR1GS2st1g1b3idx1j2mr6stride1B1P1N2B02x22x11GS2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b3idx1j2mr6stride1B1P1N2B01GS2st1g1b3idx1j2mr6stride1B1P1N2B02x32x22x11G4off03OFFS2st1g1b3idx1j2mr6stride1B1P1N2B04LI321G3LI0S3hRP2st1g1b1r3idx1j2mr6stride1B1P1N3RCB2B03S163STN2NR2x32x22x12CB2RC1G4off05SPAN24FSTrS2st1b3idx1j2mr6stride1B1P1N2B03IDXS2st1g1b3idx1j2mr6stride1B1P1N2B03IDX1GS2st1g1b3idx1j2mr6stride1B1P1N2B01G". (* [comment removed for export] *)
#[using="o r N MR UA J HA MSL MW SCg STR SO TK"] Lemma rnenf_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W13 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)P,(2.(3.=(4.(5.Vst,)))(6.(4.(5.Vst,))(7.+2.+20.)))P,(8.$9.Vm1,)(:.$9.Lms',$;.(<.(0.&40.)Lt0',(0.&40.)(<.(0.&40.)Lt1',(0.&40.)(<.(0.&40.)Lt2',(0.&40.)(<.(0.&40.)La1',(0.&40.)(<.(0.&40.)La2',(0.&40.)(<.(0.&40.)La3',(0.&40.)(<.(0.&40.)La4',(0.&40.)(<.(0.&40.)La5',(0.&40.)(<.(0.&40.)La6',(0.&40.)(<.(0.&40.)La7',(0.&40.)(<.(0.&40.)Lt3',(0.&40.)(<.(0.&40.)Lt4',(0.&40.)(<.(0.&40.)Lt5',(0.&40.)(<.(0.&40.)Lt6',(0.&40.)(<.P,(0.&40.)(=.(0.&8.))Lm',P,(0.&40.)(=.(0.&8.))(2.(>.$;.R10.(?.(10.(11.&40.+40<>8.)R2>.R2=.R2<.R?.R>.R=.R28.R27.(11.&40.VP,)R<.R;.R:.R9.R8.R7.R6.(11.&40.(12.$13.(14.Vj,+2.)))R1?.R1>.R1=.(11.&40.$15.)R1<.R1;.(11.&40.$13.)R1:.R19.R5.R4.R3.R2.)R14.(11.&40.+40<>8.)R13.(16.(0.&40.))R1.(17.$9.)))(2.(18.(19.(1:.$1;.$1;.)(1<.$1;.$1;.(1=.VP,+3.)VP,)(1>.(1:.$1;.$1;.)))Vm1,R1.)(2.(1?.$9.Vm1,R1.)(2.(8.$9.R1.)(2.(20.VhRP,(21.Vst,Vg,Vb,Vidx,)R1.)(22.(21.Vst,Vg,Vb,Vidx,))))))))))))))))))))))(?.(10.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.(11.&40.Vidx,)R16.R15.R14.R13.R12.R11.R10.(11.&40.Vj,)R?.R>.R=.(11.&40.$15.)R<.R;.(11.&40.$13.)R:.R9.R8.R7.R6.R5.)R4.(11.&40.+40<;<.)R3.(16.(0.&40.))Vm1,(17.$9.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until fc. intros CTR MI.
  dpose (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  pose proof (size_class_range j J) as SZR.
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  assert (NR : 12 <= N < 2^18) by (unfold N, UNIT, IB; lia).
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  ddestruct (rslot_facts st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0)
    as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND. fold B in CB, Y, WRs, PEND. 
  dpose (rmeta_chunk_facts st m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
  rceilb.
  set (G := conc st g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM. fold B in MM.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  pose proof (bytes_at_read rsegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read rsegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read rsegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  dpose MW as (LI0 & FB0 & SCR0 & ML0).
  dpose MR as (WF' & CX & GL & _). destruct CX as (CH & _). unfold ctx_head_cells in CH.
  unfold RSIZE_CLASSES, RMLOCK, RCTX in *.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  step. step.
  (* [comment removed for export] *)
  pose proof (rsize_classes_read m1 j MI J) as SCRD. unfold RSIZE_CLASSES in SCRD.
  replace (94460 + 2 * j) with (94460 + j * 2) in SCRD by lia.
  step. rewrite zx16_wz by lia. clear SCRD.
  (* [comment removed for export] *)
  pose proof (rmrep_active_read st m1 j (wa (512968 + 80 + 8 * j)) MR J eq_refl) as RDA. rewrite HA in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA. fold G in RDA.
  replace (wa (512968 + 80 + 8 * j)) with (Z_to_bv 64 (512960 + j * 8 + 88)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (size_class j)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  step.
  (* [comment removed for export] *)
  step.
  eapply evt_mono.
  { eapply (renframe_walk (Z_to_bv 64 0x40ce8) sp gp tp _ _ _ s0 s1 _ _ _ _ _ s3 s4 s5 _ s7 s8 _ s10 s11 _ _ _ _ (Z_to_bv 64 G) _
              (pw st (m_prev mr)) (pw st (m_next mr)) F fc m1 B stride N idx (c_mmap_counter (ctx st)) (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned _) _ => rewrite (unsigned_lit G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by lia; unfold N, UNIT, IB; lia
         | |- _ => idtac end.
    all: try (rewrite (unsigned_lit G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia.
    - exact (so_maplen _ _ _ _ _ _ SO). }
  (* [comment removed for export] *)
  intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
  ddestruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
  set (off0 := if bv_unsigned x3 =? 0 then Z.land (c_mmap_counter (ctx st)) 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) in EM |- *.
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  replace ((stride - 4 - N) / 16) with 0 in EM |- * by (rewrite STN; replace (N + 4 - 4 - N) with 0 by lia; reflexivity).
  pose proof (fold_off_le_slack off0 0 OFF0 ltac:(lia)) as OFF.
  replace (fold_off off0 0) with 0 in EM |- * by lia.
  rewrite Z.mul_0_r, Z.add_0_r in EM |- *.
  replace (ret_pc (Z_to_bv 64 0x40ce8)) with (Z_to_bv 64 0x40ce8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (S31n : stride - 4 - N < 2^31) by lia.
  assert (SPAN2 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; exact SPAN1).
  assert (T1 : 0 <= idx < 32) by lia. assert (T3 : 16 * 0 + N + 4 <= stride) by lia. assert (T0 : 0 <= 0) by lia. assert (TN : 0 <= N) by lia.
  assert (T4 : (stride * idx + 16 * 0) / 16 < 65536) by (apply (Q16 0); lia).
  ddestruct (renframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4)
    as (MRr & TKr & CONCr & FSTr & SNDr). clear T1 T3 T0 TN T4.
  rewrite Z.mul_0_r, Z.add_0_r in MRr.
  change (conc st b) with B in MRr. change (get_stride (get_meta_rec st g)) with stride in MRr.
  fold P in MRr, EM. rewrite <- EM in MRr.
  destruct (enf0_st_eq st g b r idx j STR SO) as [E1st _]. fold N in E1st. rewrite E1st in MRr, TKr.
  (* [comment removed for export] *)
  assert (EM' : m' = write_to_mem (write_to_mem (write_to_mem m1 (wa (P - 3)) [b8 idx]) (wa (P - 2)) (le2 (wz ((P - B - 16) / 16)))) (wa (P - 3)) [b8 (Z.land idx 31 + Z.shiftl 0 5)]).
  { rewrite EM. unfold renframe_tail_mem, renframe_off_mem. cbn [Z.eqb].
    replace (P + stride - 4 - P - N) with 0 by lia. cbn [Z.eqb Z.leb]. reflexivity. }
  assert (MU : munch [(P - 3, P)]%Z m1 m').
  { rewrite EM'. apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
  assert (WM : wmono rsegs m1 m').
  { rewrite EM'. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl. }
  deexists 14. exists m'.
  split; [unfold P, G; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact MRr| exact TKr].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L29784460045.27L33458121165.27L63967161437.27L64230354945.2700000L00m01I01gS2st1b3idx1j2mr6stride1B1P1NS2st1b3idx1j2mr6stride1B1P1N1a2HaS2st1b3idx1j2mr6stride1B1P1NS2st1b3idx1j2mr6stride1B1P1N1a". (* [comment removed for export] *)
#[using="hRP st g b idx j mr stride B P N"] Lemma lor_192 a : 0 <= a < 32 -> Z.lor a 192 = a + 192.
Proof. rceilb. intros Ha. change 192 with (3 * 2 ^ 6). rewrite (lor_small_shl 3 6 a) by lia. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00K0@L15921664796.77 L16073280526.104L18575632550.78 L18588176547.77 L24936352533.114L24936368817.113L25069450385.115L26852692537.114L26852709277.113L29058216511.115L33835680171.110L33835698987.109L34308191119.119L35475270538.109L36848258738.114L37836719.105   L41352056151.108L43069462285.108L4477642075.108 L48283793512.107L57819194832.109L60742230087.105L6154849081.109 L6431022483.114 L6433042356.108 L7568642586.115 L8528370589.78  00000S01;01^02A02k03U04?04i05S06J07:07j08`09J0::0:`0;M0<:0<d0=N0>A0>k0?[0@Q0AG0BL0BoS2st1b3idx1j2mr6stride1B1P1N2B03IDXS2st1b1r3idx1j2mr6stride1B1P1N2mt2B03MWRS2st1b3idx1j2mr6stride1B1P1N2B03S16S2st1b3idx1j2mr6stride1B1P1N2B03S16S2st1b1r3idx1j2mr6stride1B1P1N2mt2B01w3L31S2st1b1r3idx1j2mr6stride1B1P1N2mt2B01w3L31S2st1b1r3idx1j2mr6stride1B1P1N2mt2B01w3LENS2st1b1r3idx1j2mr6stride1B1P1N2mt2B01w3LORS2st1b1r3idx1j2mr6stride1B1P1N2mt2B01w3L31S2st1b1r3idx1j2mr6stride1B1P1N2mt2B03S162SK2R42CB1w3LENS2st1b1r3idx1j2mr6stride1B1P1N2mt2B03S162R42CB1wS2st1b1r3idx1j2mr6stride1B1P1N2mt2B03S162R42CB1wS2st1b1r3idx1j2mr6stride1B1P1N2mt2B01w2b'3Hf'1H3S162R4S2st1b1r3idx1j2mr6stride1B1P1N2mt2B01w3L31S2st1b1r3idx1j2mr6stride1B1P1N2mt2B03S162R42CB1wS2st1b1r3idx1j2mr6stride1B1P1N2mt2B01wS2st1b1r3idx1j2mr6stride1B1P1N2mt3cnt2CR2B01wS2st1b1r3idx1j2mr6stride1B1P1N2mt3cnt2CR2B01wS2st1b1r3idx1j2mr6stride1B1P1N2mt2B01w3L31S2st1b1r3idx1j2mr6stride1B1P1N2mt2B01w3L31S2st1b1r3idx1j2mr6stride1B1P1N2mt2B03S165SPAN12R41wS2st1b1r3idx1j2mr6stride1B1P1N2mt2B01w3MWRS2st1b1r3idx1j2mr6stride1B1P1N2mt2B03S162SK2R41wS2st1b1r3idx1j2mr6stride1B1P1N2mt2B03S165SPAN12SK2R41wS2st1b1r3idx1j2mr6stride1B1P1N2mt2B03S165SPAN12SK2R41wS3hRP2st1b1r3idx1j2mr6stride1B1P1N3RCB2mt2B03S165SPAN12R42RC2CB1w3LENS2st1b3idx1j2mr6stride1B1P1N2B03IDX". (* [comment removed for export] *)
#[using="m1 r j N MR J SO TK"] Lemma renfD_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W13 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pmt,$23.Pcnt,$1;.PmC,P,(0.&40.)(=.(0.&8.))P,(24.Vst,R3.)P,(25.(26.Vst,R4.))P,(2.(3.+1.R4.)(3.R4.+20.))P,(20.VhRP,(21.Vst,Vg,Vb,Vidx,)R4.)P,(22.(21.Vst,Vg,Vb,Vidx,))P,(8.$9.R6.)(:.$9.Lms',$;.(<.P,(0.&40.)(=.(0.&8.))Lm',P,(0.&40.)(=.(0.&8.))(2.(>.$;.R2.(?.(10.R29.R28.R27.R26.R25.R24.R23.R22.(11.&40.(27.Vst,R;.))(11.&40.VP,)(11.&40.(12.R:.+1.))(11.&40.(12.VP,+<.))R1?.R1>.R1=.R1<.R1;.R1:.(11.&40.R:.)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(11.&40.+40=10.)R<.(16.(0.&40.))R1.(17.$9.)))(2.(18.(19.(1:.$1;.$1;.)(1<.$1;.$1;.(27.Vst,R;.)(12.(27.Vst,R;.)+28.))(19.(1:.$1;.$1;.)(1<.$1;.$1;.(1=.VP,+3.)(1=.VP,+2.))(1>.(1:.$1;.$1;.))))R9.R1.)(2.(1?.$9.R9.R1.)(2.(8.$9.R1.)(2.(20.VhRP,(28.(1<.$29.$1;.(2:.$29.$1;.Vb,)(12.(12.(2;.$29.$1;.Vb,)(12.+10.(14.Vstride,Vidx,)))-3.))(2<.(2=.Vidx,+1?.)+<0.)(2>.R;.(2?.=(26.Vst,R;.))(21.Vst,Vg,Vb,Vidx,)))R1.)(22.(28.(1<.$29.$1;.(2:.$29.$1;.Vb,)(12.(12.(2;.$29.$1;.Vb,)(12.+10.(14.Vstride,Vidx,)))-3.))(2<.(2=.Vidx,+1?.)+<0.)(2>.R;.(2?.=(26.Vst,R;.))(21.Vst,Vg,Vb,Vidx,))))))))))(?.(10.R27.R26.R25.R24.R23.R22.R21.R20.(11.&40.(27.Vst,R9.))(11.&40.VP,)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(11.&40.R8.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)R;.(11.&40.+40<>8.)R:.(16.(0.&40.))R7.(17.$9.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until mC. intros MST MWT CR MRC TKC MIC.
  dpose (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  dpose (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). rceilb.
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  set (st0' := enf0_st st g b idx) in *.
  assert (MST0 : meta_slot st0' mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  dpose (rmeta_slot_bounds st0' mC mt MRC MST0) as (Tpos & TC & TI & _ & _).
  change (conc st0' mt) with (conc st mt) in Tpos, TC, TI.
  dpose (rmeta_chunk_facts st0' mC mt MRC MST0) as (_ & _ & _ & _ & _ & GDJ & _).
  assert (RG0 : s_regions st0' = s_regions st) by (unfold st0', enf0_st, wr16; rewrite !s_regions_wr8; reflexivity).
  assert (GR0 : s_groups st0' = s_groups st) by (unfold st0', enf0_st, wr16; rewrite !s_groups_wr8; reflexivity).
  rewrite RG0 in GDJ. pose proof (GDJ (fst b) r Hr Hk) as TDJ. change (conc st0' mt) with (conc st mt) in TDJ.
  pose proof (munch_refl [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC) as MU. pose proof (wmono_refl rsegs mC) as WM.
  dpose MWT as (LI0 & FB0 & SCR0 & ML0). pose proof (meta_word_range _ MWT) as MWR.
  rceilb.
  (* [comment removed for export] *)
  rmchunk MRC MST0 CH. change (conc st0' mt) with (conc st mt) in CH. change (get_meta_rec st0' mt) with (get_meta_rec st mt) in CH.
  rmeta_open (conc st mt) MUt WMt.
  step.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit (meta_word (get_meta_rec st mt))) by lia.
  set (w := meta_word (get_meta_rec st mt)) in *.
  rewrite (Z_to_bv_unsigned 64 (Z.shiftl w 52)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (zb_shl_shr w 52) by lia. change (2 ^ (64 - 52)) with 4096.
  rewrite (meta_word_mod4096 st g b idx j _ MWT).
  step.
  lazymatch goal with H : rw_cells rsegs ?mX (conc st mt) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR5 : rmrep (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') mX);
    [ eapply rmrep_put_meta_frame; [exact MRC| exact MST0| exact MUt| exact WMt|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
      unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen oconc]; reflexivity
    | clear MUt WMt H ] end.
  set (st5 := put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') in *.
  assert (TK5 : ticks_ok st5) by (exact (ticks_ok_upd_meta st0' mt (fun _ => m_set_maplen 0 (get_meta_rec st mt)) TKC)).
  (* [comment removed for export] *)
  pose proof (land31_range idx) as L31.
  assert (K3 : cell_read (get_shadow st5 (fst b)) (snd b + (16 + stride * idx) + -3) = Known (Z.land idx 31)).
  { change (get_shadow st5 (fst b)) with (get_shadow st0' (fst b)). unfold st0', enf0_st.
    rewrite (cell_read_wr8_same (wr8 _ _ (wr16 _ _ st)) (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5));
      [| apply ticks_ok_wr8, ticks_ok_wr16; exact TK | change (Z.shiftl 0 5) with 0; lia].
    change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity. }
  destruct (rmrep_shadow_read st5 _ (fst b) r (snd b + (16 + stride * idx) + -3) (Z.land idx 31) MR5 Hr Hk ltac:(lia) K3) as [RDK _].
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in RDK
    by (unfold wa; f_equal; unfold P; lia).
  step. rewrite zxb_b8 by lia. clear RDK. rewrite ?(unsigned_lit P) by (unfold P; lia).
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit cnt), swrap32_small by lia.
  step. rewrite (wz_unsigned (Z.land idx 31)) by lia. rewrite <- (Z.land_assoc idx 31 31). change (Z.land 31 31) with 31.
  step. rewrite ?(unsigned_lit (Z.land idx 31)) by lia.
  (* [comment removed for export] *)
  dpose MR5 as (_ & _ & _ & _ & _ & SH5). destruct (SH5 (fst b) r Hr Hk) as [WR5 _]. clear SH5.
  pose proof (wr_at_store_ok rsegs _ _ _ (snd b + (16 + stride * idx) + -3) 1 WR5 ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  assert (RG5 : s_regions st5 = s_regions st) by (unfold st5; exact RG0).
  assert (GR5 : s_groups st5 = s_groups st) by (unfold st5; exact GR0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_wr8 st5 mX (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192) r MR5 TK5) as MR6 end.
  cbn [fst snd] in MR6. rewrite RG5, GR5 in MR6.
  assert (LOR : 0 <= Z.lor (Z.land idx 31) 192 < 256) by (rewrite lor_192 by lia; lia).
  specialize (MR6 Hr Hk ltac:(lia) ltac:(intros b' gh' Hb' Hf'; destruct (NOGRP b' gh' Hb' Hf'); lia) ltac:(lia)).
  replace (r_base r + (snd b + (16 + stride * idx) + -3)) with (P - 3) in MR6 by (unfold P; lia).
  rewrite <- (lor_192 (Z.land idx 31)) by lia.
  rraw_store_finish0 (P - 3) [b8 (Z.lor (Z.land idx 31) 192)] MU WM SOK.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit P) by (unfold P; lia).
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MR6| apply ticks_ok_wr8; exact TK5].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0@L10351936332.88 L11803683361.102L14965057634.103L15921664796.86 L18575632550.87 L18588176547.86 L19596063794.103L2034932015.88  L24891047031.113L24891047412.112L24891065923.111L25470998676.116L2690964734.104 L27052086882.106L27052086882.115L28154514572.112L29005648011.103L29206049723.99 L32337321010.113L34774477999.101L3504444630.114 L35838155016.106L35838155016.115L49702777314.104L50963114204.101L50963212643.100L52061149739.103L54859230692.103L56458578519.102L56684737218.103L57017996466.102L57323541894.103L59308516196.111L59308668168.104L59308959596.71 L59309037779.106L60526527523.99 L64612942972.102L64613077812.104L66052242638.88 L8528370589.87  00000]01Q02D03203`04N05:06006c07V08I09<09m0:\0;M0<S0==0>;0?D0@L0AM0B:0Bi0D<0E60F00G<0Gm0I@0J10J]0KM0L\0MR0N:0O50P:0Q;0R<0Ri0SWS2st1b3idx1j2mr6stride1B1P1N1k1i3cnt2HK2HI2B0S2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK2B03SZIS2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B03S162R4S2st1b3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B03IDXS2st1b3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B03S16S2st1b3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B03S16S2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B0S2st1b3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK3SZC2B03S16S2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B02b03Hf0S2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B02b03Hf0S2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B02b03Hf0S2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B02jj3HjjS2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B01u2HuS2st1b1r3idx1j2mr6stride1B1P1N1i3cnt2HK2B01x2XRS2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B01x2XRS2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B03S162SK2R42b03Hf03M162GE1HS2st1b1r3idx1j2mr6stride1B1P1N1i3cnt2HK2B0S2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK2B03S162SK3SZI2R4S2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B03B163S162SK2R42b03Hf02GE2E01HS2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK3FIT2B03S165SPAN12SK3SZI2R4S2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B03S164SMOD2R42b03Hf01HS2st1b1r3idx1j2mr6stride1B1P1N1i3cnt2HK2HI2B0S2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2HI2B0S3hRP2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK3FIT2B03S165SPAN13SZI2R42RC3RCB2CBS2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK2B03S162R42CBS2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK2B03S162R42CBS3hRP1b1r3idx6stride1k1i3szc3cnt2HK2HI3SZC3FIT2B03S165SPAN12SK3SZI2R42RC3RCBS2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2HI2B01KS3hRP2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK3FIT2B03S165SPAN13SZI2R42RC3RCB2CBS2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2HI2B01KS2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B0S2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK2B0S2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK2B03S162SK3SZI2R42b03Hf06CONTRA2LES2st1b1r3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B03S162R42EiS2st1b3idx1j2mr6stride1B1P1N1i3cnt2HK2HIS2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK2B01u3Hux1l2l0S2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK3FIT2B03S165SPAN13SZI2R4S2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK2B03S162SK3SZI2R42CBS2st1b1r3idx1j2mr6stride1B1P1N1k1i3szc3cnt2HK2B03S162SK3SZI2R42CBS2st1b3idx1j2mr6stride1B1P1N1k1i3cnt2HK2HI2B0S2st1b3idx1j2mr6stride1B1P1N1k1i3cnt2HK2B03IDX". (* [comment removed for export] *)
Lemma rzero_loop_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W13 ()) "Pk,$30.Pi,$1;.Pszc,$1;.Pcnt,$1;.Pstz,$31.PmC0,P,(0.&40.)(=.(0.&8.))PmC,P,(0.&40.)(=.(0.&8.))Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)P,(>.$1;.(32.R24.)(1=.(12.R21.+1.)R23.))P,(2.(3.=R24.)(3.R24.R22.))P,(3.+1.R24.)P,(2.(3.=R24.)(6.R24.+1000.))P,(3.(12.+10.(14.(14.+10.R26.)R25.))Vstride,)P,(>.(33.$29.$34.$35.$36.)(37.R25.)(37.Vst,))P,(>.(33.$23.(38.$29.$34.$1;.$39.)(3:.$29.$34.$35.$1;.$39.$3;.)$3<.)(3=.R26.)(3=.Vst,))P,(20.VhRP,R27.R25.)P,(22.R28.)P,(8.$9.R27.)P,(18.(19.(1:.$1;.$1;.)(1<.$1;.$1;.(12.VP,+<.)(12.(12.(12.VP,+<.)(14.(14.+10.R2<.)R2;.))+1.))(1>.(1:.$1;.$1;.)))R29.R28.)P,(1?.$9.R2:.R29.)(:.$9.Lms',$;.(<.P,(0.&40.)(=.(0.&8.))Lm',P,(0.&40.)(=.(0.&8.))(2.(>.$;.R2.(?.(10.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.(11.&40.(1=.R2?.+1.))(11.&40.(1=.R2?.+1.))R21.R20.R1?.R1>.R1=.R1<.(11.&40.R2?.)R1;.R1:.R19.R18.(11.&40.(14.+10.R30.))(11.&40.R2?.)R16.R15.R14.R13.R12.R11.)R10.(11.&40.+40?>0.)R?.(16.(0.&40.))R1.(17.$9.)))(2.(18.(19.(1:.$1;.$1;.)(1<.$1;.$1;.(12.VP,+<.)(12.(12.(12.VP,+<.)(14.(14.+10.R30.)R2?.))+1.))(1>.(1:.$1;.$1;.)))R2=.R1.)(2.(1?.$9.R2=.R1.)(2.(8.$9.R1.)(2.(20.VhRP,(3>.(3?.Vst,Vg,Vb,Vidx,)(14.+10.R30.)R31.R32.R2>.)R1.)(2.(22.(3>.(3?.Vst,Vg,Vb,Vidx,)(14.+10.R30.)R31.R32.R2>.))(2.(>.(33.$29.$34.$35.$36.)(37.(3>.(3?.Vst,Vg,Vb,Vidx,)(14.+10.R30.)R31.R32.R2>.))(37.Vst,))(2.(>.(33.$23.(38.$29.$34.$1;.$39.)(3:.$29.$34.$35.$1;.$39.$3;.)$3<.)(3=.(3>.(3?.Vst,Vg,Vb,Vidx,)(14.+10.R30.)R31.R32.R2>.))(3=.Vst,))Px,(0.&40.)P,Pj,$1;.P,(2.(3.R33.R1.)(3.R1.R31.))(40.(>.$1;.(41.&40.R3.)(12.(12.VP,+<.)(14.(14.+10.R33.)R2.))))(>.(=.(0.&8.))A1.R3.R2.A1.R2>.R2.))))))))))(?.(10.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.(11.&40.(1=.(12.R2=.+1.)R2?.))(11.&40.(12.(12.VP,+<.)(14.(14.+10.R2>.)R2?.)))R1?.R1>.R1=.R1<.R1;.R1:.(11.&40.R2=.)R19.R18.R17.R16.(11.&40.(14.+10.R2>.))R15.R14.R13.R12.R11.R10.R?.)R>.(11.&40.+40=10.)R=.(16.(0.&40.))R2:.(17.$9.)))")
(* [comment removed for export] *).
Proof using MR STR SO.
  induction k as [|k IH]; intros until fc; intros HK HI SZC CNT FIT RGz GRz MRz TKz MIz MU WM.
  { exfalso. lia. }
  dpose (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SZI : 0 <= 16 * szc * i <= 16 * szc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia]).
  dpose (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). rceilb.
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  (* [comment removed for export] *)
  assert (Hr' : (s_regions stz) !! (fst b) = Some r) by (rewrite RGz; exact Hr).
  dpose MRz as (WFz & _ & _ & _ & _ & SHz). destruct (SHz (fst b) r Hr' Hk) as [WRz _]. clear SHz.
  pose proof (wr_at_store_ok rsegs _ _ _ (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)) 1 WRz ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)))) with (Z_to_bv 64 (P + 12 + 16 * szc * i)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_wr8 stz mX (aadd (pp st g b idx) (UNIT + i * (16 * szc) - 4)) 0 r MRz TKz) as MR2 end.
  unfold aadd, pp, UNIT in MR2. cbn [fst snd] in MR2. fold mr in MR2. fold stride in MR2. rewrite GRz in MR2.
  specialize (MR2 Hr' Hk ltac:(lia)).
  assert (NOG : forall b0 gh, (s_groups st) !! b0 = Some gh -> fst b0 = fst b ->
            ~ snd b0 <= snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4) < snd b0 + 9).
  { intros b0 gh Hb0 Hf0 CONTRA. pose proof MR as (WF & _). dpose WF as (_ & _ & _ & _ & GWF).
    ddestruct (GWF b0 gh Hb0) as (r0 & _ & _ & _ & _ & M16).
    destruct (NOGRP b0 gh Hb0 Hf0) as [LE|GE]; [lia|].
    assert (E0 : snd b0 = 16 * (snd b0 / 16)) by (pose proof (Z.div_mod (snd b0) 16 ltac:(lia)); lia).
    assert (E1 : snd b = 16 * (snd b / 16)) by (pose proof (Z.div_mod (snd b) 16 ltac:(lia)); lia).
    assert (E2 : stride = 16 * (stride / 16)) by (pose proof (Z.div_mod stride 16 ltac:(lia)); lia).
    clear - CONTRA E0 E1 E2. nia. }
  specialize (MR2 NOG ltac:(lia)). clear NOG.
  replace (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4))) with (P + 12 + 16 * szc * i) in MR2 by (unfold P; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0])
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa; f_equal; lia);
    assert (PW0 : forall u, 0 <= u < 2^64 -> u <> P + 12 + 16 * szc * i -> write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0] (wa u) = mX (wa u));
    [ intros u Hu Hux;
      rewrite write_to_mem_spec by (cbn; lia); rewrite wa_unsigned by lia; cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity;
      destruct (Z.leb_spec0 (P + 12 + 16 * szc * i) u); destruct (Z.ltb_spec0 u (P + 12 + 16 * szc * i + 1)); cbn [andb]; try reflexivity;
      exfalso; lia
    | apply (munch_write _ _ mX (P + 12 + 16 * szc * i) [b8 0]) in MU; [| lia | cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity; lia | cbn [length inside]; replace (Z.of_nat 1) with 1 by reflexivity; lia];
      apply (wmono_write rsegs _ mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in WM;
      lazymatch goal with HI : mem_inv rsegs mX |- _ =>
        apply (mem_inv_store rsegs mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in HI;
        [| first [ exact SOK | replace (wa (P + 12 + 16 * szc * i)) with a by (unfold wa; f_equal; lia); exact SOK ] ]
      end;
      clear SOK;
      let m' := fresh "m" in remember (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0]) as m' eqn:Em'; clear Em' ]
  end.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (cnt + 1 - i)) by lia.
  step. rewrite ?unsigned_lit by lia.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    replace (cnt + 1 - i + -1) with (cnt + 1 - (i + 1)) by lia.
    replace (P + 12 + 16 * szc * i + 16 * szc) with (P + 12 + 16 * szc * (i + 1)) by lia.
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    eapply evt_mono.
    { (eapply (IH (i + 1) szc cnt);
      [ lia | lia | exact SZC | exact CNT | exact FIT
      | rewrite s_regions_wr8; exact RGz
      | rewrite s_groups_wr8; exact GRz
      | exact MR2
      | apply ticks_ok_wr8; exact TKz
      | assumption | exact MU | exact WM ]). }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (m' & -> & X1 & X2 & X3 & X4 & X5 & X6 & X7 & PW)).
    eexists. split; [reflexivity|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
    split; [exact X6|]. split; [exact X7|].
    intros x Hx. rewrite (PW x) by (intros jj Hjj; apply Hx; lia).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
  - (* [comment removed for export] *)
    assert (Ei : i = cnt) by lia. destruct k; [| exfalso; lia].
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit cnt) by lia. replace (cnt + -1) with (cnt - 1) by lia. step. step. step.
    apply evt_done. eexists. split; [reflexivity|].
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR2|]. split; [apply ticks_ok_wr8; exact TKz|].
    split; [rewrite s_regions_wr8; exact RGz|]. split; [rewrite s_groups_wr8; exact GRz|].
    intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End ENF.

End RP_1.
