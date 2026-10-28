(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_free_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_get_meta.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := rceilb; unfold UNIT, IB in *; lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_free_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rfree_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "Corelib.Init.Datatypes.snd"; "Corelib.Numbers.BinNums.N"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.wr16"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aadd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.wr8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Known"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_last_idx"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freeable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_sizeclass"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_maplen"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rfhead_post"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_word"].


Section RP_1. Context {hRP : run_params}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L12853367178.4L5738539914.4 00000500:S1x1HS1x1H". (* [comment removed for export] *)
#[using="hRP"] Lemma zx32_wz x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. rceilb. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00=0>L16307678836.8L22701701582.8L29311237449.8L35560185155.8L39539102563.8L46611986243.8L52257470722.8L52335558569.8L61162877165.8L65101109554.8L6757834505.8 L68575966226.8L9982888524.8 00000400800900:00;00<00@00A00E00L00M00T00_S2mrS2mrSSSSS2mrSS2mrS2mr2FBSS2mr2LIS2mr2FB3SCR". (* [comment removed for export] *)
#[using="hRP"] Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof. rceilb.
  (intros dd_H; ddestruct dd_H as (LI & FB & SCR & ML)).
  assert (E : 126 = Z.ldiff (Z.ones 7) (Z.ones 1)) by reflexivity. rewrite E, land_ldiff_distr.
  rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change (2^7) with 128. change (2^1) with 2. change (2^5) with 32. unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.div_add, (Z.div_small (m_last_idx mr)) by lia.
  replace (0 + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr)) with ((m_freeable mr + 2 * m_sizeclass mr) + m_maplen mr * 128) by lia.
  rewrite Z.mod_add, Z.mod_small by lia.
  replace (m_freeable mr + 2 * m_sizeclass mr) with (m_freeable mr + m_sizeclass mr * 2) by lia.
  rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L12500182983.7L18926670024.7L57504004860.7L68257150872.700000>00?00C00GS2mr2LI2FB3SCRSS2mrS2mr". (* [comment removed for export] *)
#[using="hRP"] Lemma meta_word_pg mr : mw_ok mr -> meta_word mr - meta_word mr mod 4096 = 4096 * m_maplen mr.
Proof. rceilb.
  (intros dd_H; ddestruct dd_H as (LI & FB & SCR & ML)). unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
  rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rfhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st1 : mstate) (g : aptr) (idx li : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_A ()) "Lms',$0.(1.(2.&40.)Lx1,(2.&40.)(1.(2.&40.)Lx5,(2.&40.)(1.(2.&40.)Lx6,(2.&40.)(1.(2.&40.)Lx7,(2.&40.)(1.(3.(2.&8.))Ljunk,(3.(2.&8.))(1.P,(2.&40.)(4.(2.&8.))Lm',P,(2.&40.)(4.(2.&8.))(5.(6.$0.R7.(7.(8.R6.(9.&40.(:.(;.&40.O20.)-30.))O1?.O1>.O11.O10.O?.(9.&40.O2.)O:.(<.(=.O6.O3.))(9.&40.(:.(=.O6.O3.)+1<.))(<.(>.(?.+2.O2.)))(<.(>.(10.(?.+2.(:.O1.+1.))+1.)))(9.&40.+7<<=<.)R5.R4.R3.O1;.O1:.O19.O18.O17.O16.O15.O14.O13.O12.O>.O=.O<.O;.)O9.(9.&40.+3?<>0.)O8.(11.(2.&40.))R1.(12.$13.)))(5.(14.(15.O6.O7.(;.&40.O20.))O5.R1.)(5.(16.$13.O5.R1.)(5.(17.$13.R1.)(5.(18.$13.R1.O7.(:.(;.&40.O20.)-30.))(5.(19.$13.R1.(:.(;.&40.O20.)-30.)(1:.$1;.(1<.#8.R2.)(1:.$1;.(1=.O1:.)(1:.$1;.(1=.O1;.)(1:.$1;.(1=.O1<.)(1:.$1;.(1=.O1=.)(1:.$1;.(1=.O21.)(1>.$1;.))))))))(1?.VhRP,O4.R1.)))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@L10052459652.123L11284053051.119L11803471779.117L13776223718.115L13794057816.117L14946198807.115L15045343677.109L15047392320.110L15450407813.118L16407571081.118L1730476540.117 L17680713856.119L2061316626.117 L20739542891.113L25316211135.119L29315069660.100L30163642374.148L31706190871.117L33021745617.112L33246259908.118L34219699462.105L34308191119.121L35189674350.119L35189674350.121L36032650285.114L36940382882.110L36942432095.109L3864950422.117 L39850144431.113L40599920750.114L41246720063.117L44282350701.112L45710826623.112L47443082127.119L47443082127.121L49698585326.118L49698585326.120L49702855464.117L49702855471.119L49712579895.114L51845331698.115L52448723318.119L52448723318.121L54854631278.116L56756951631.118L57020048649.113L57020048776.112L57979857178.117L59308628304.112L63070133766.115L63152162437.101L6437622708.116 L66752045130.115L6959603832.143 L8929152679.114 00000W01<01P01h02M02N02b03603U03i04N04m05R05S06806G06H06g07_08B08m09T09n0:H0:I0:]0;10;I0;J0;b0<;0<U0=F0>=0?40?b0@P0A>0Al0BD0Bi0CG0Ce0D90Da0E50EI0Ea0FS0GB0G[0H>0HV0IE0J4S2st1p1r1g2b32po3idx3P162B03GB01b3Hfb1HS2a02st1p1r1g2b32po3idx2HP3P162B03GB0S2st1p1r1g2b32po3idxS2st1p1r1g2b32po3idx3P16S2a02st1p1r1g2b32po3idx2HP3P162B03GB0FS2st1p1r1g2b32po3idxS2st1p1r1g2b32po3idxS2st1p1r1g2b32po3idx3P162B03GB0S2st1p1r1g2b32po3idxS2a02st1p1r1g2b32po3idx2HP3P162B03GB0S2st1p1r1g2b32po3idx3P162B03GB0S2a02st1p1r1g2b32po3idx2HP3P162B03GB0FS2a02st1p1r1g2b32po3idx2HP3P162B03GB0S1p1r2b32po3idxFS2st1p1r1g2b32po3idx3P162B03GB0S3hRP3RCB2st1p1r1g2b31E3rsv2po3idx3P163EHI3RSV2B02BC3GB0S2st1p1r1g2b32po3idx3P163PHI2B03GB0S3hRP3RCB2st1p1r1g2b32po3idx3P162B03GB03GB1S2st1p1r1g2b32po3idx3P162B03GB01b3Hfb1HS2st1p1r1g2b31E2po3idx3ELOS2st1p1r1g2b31E2po3idx3ELOFS2st1p1r1g2b32po3idxS2st1p1r1g2b32po3idxS2st1p1r1g2b32po3idx3P16FS2st1p1r1g2b32po3idx3IDXS2st1p1r1g2b32po3idx1x2HxS2st1p1r1g2b31E3rsv2po3idxS3hRP3RCB2a02st1r1g1E2po2HP3P163ELO3EHI2B02BC3GB0S3hRP2sp2lo2st1p1r1g2b32po3idx2LO3SLO3P163PHI2B02BC3GB0S3hRP2sp2lo2st1p1r1g2b32po3idx2LO3SLO3P163PHI2B02BC3GB0S3hRP3RCB2st1p1r1g2b32po3idx3P163PHI2B02BC3GB0S3hRP3RCB2st1p1r1g2b32po3idx3P163PHI2B02BC3GB0S3hRP3RCB2st1p1r1g2b32po3idx3P163PHI2B02BC3GB0S3hRP3RCB2st1p1r1g2b32po3idx3P163PHI2B02BC3GB0S2st1p1r1g2b32po3idx3IDXS2a02st1p1r1g2b32po3idx2HP3P162B03GB0S2st1p1r1g2b31E3rsv2po3idx3RSVS2st1p1r1g2b31E3rsv2po3idx3RSVS2st1p1r1g2b32po3idxS2st1p1r1g2b32po3idx3P163PHI2B03GB01x2E1S2st1p1r1g2b32po3idxS2st1p1r1g2b32po3idxS2st1p1r1g2b32po3idx3PHIS2a02st1p1r1g2b31E3rsv2po3idx2HP3P163RSV2B03GB02K1S2st1p1r1g2b32po3idx2mr3P162LI3FBL2SC2ML2B03GB0S1p1r2b32po3idx3P162B32B0S2st1p1r1g2b32po3idx3P163PHI2B03GB0S2st1p1r1g2b32po3idx3PHIS1p1r2b32po3idx2mr3P163PHI2LI3DR13DR21q2r01H2H0S2st1p1r1g2b32po3idx2mr3P162LI3FBL2SC2ML2B03GB0". (* [comment removed for export] *)
#[using="Type"] Lemma rfree_head3 : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_A ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa3,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Px1,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(4.(2.&8.))Pm0,P,(2.&40.)(4.(2.&8.))Pjunk,(3.(2.&8.))Plo,$21.Pst,$22.Pp,$23.Pr,$24.Pg,$23.Pb3,$21.Plo8,$21.Phi,$21.PE,$21.Prsv,$21.Zpo,$21.(25.$26.$21.R8.)Zidx,$21.(27.R6.+1?.)Zmr,$28.(29.R;.R8.)Zst1,$22.(2:.(2;.R;.-2.)=(2<.(2;.R;.-3.)+??.R<.))P,(1?.VhRP,R=.R10.)P,(17.$13.R11.)P,(2=.R?.)P,(18.$13.R13.R11.(:.(;.&40.R32.)-30.))P,(2>.(2?.VhRP,)R12.)P,(2>.R13.(10.(;.&40.R34.)+30.))P,(19.$13.R16.(:.(;.&40.R35.)-30.)(1:.$1;.(1<.#8.R15.)(1:.$1;.(1=.R27.)(1:.$1;.(1=.R28.)(1:.$1;.(1=.R2>.)(1:.$1;.(1=.R2?.)(1:.$1;.(1=.R36.)(1>.$1;.))))))))P,(14.(15.R14.R15.(;.&40.R36.))R18.R17.)P,(16.$13.R19.R18.)P,(6.(4.$24.)(30.$26.$24.(31.$26.$32.$33.$24.)(34.$26.$32.$33.$24.)(35.$26.$21.R15.)(36.R16.))(37.$24.R14.))P,(6.$38.(39.R15.)$3:.)P,(6.$21.(;.&40.R32.)(:.(3;.R16.)R?.))P,(6.$21.(3<.R10.+10.)=)P,(2>.+10.R11.)P,(2>.(:.R12.+10.)(3=.(3>.R19.)))P,(3?.R1<.R19.)P,(6.$40.(41.(42.R1=.(35.$26.$21.R1<.))(10.R14.+3.))(43.R19.))P,(6.$40.(41.(42.R1>.(35.$26.$21.R1=.))(10.R15.+2.))(43.R19.))P,(6.$40.(41.(42.R1?.(35.$26.$21.R1>.))(10.R16.+1.))(43.R19.))P,(5.(2>.=(44.R15.))(45.(44.R15.)+20.))P,(5.(2>.=(46.R16.))(45.(46.R16.)+2.))P,(5.(2>.=(47.R17.))(45.(47.R17.)+40.))P,(5.(2>.=(48.R18.))(45.(48.R18.)(?.+2.+28.)))P,(5.(2>.=R20.)(45.R20.+100.))P,(2>.(:.(3;.R23.)R1<.)R1>.)P,(2>.(:.R1?.+1.)(:.(3;.R24.)(3=.(3>.R24.))))P,(5.(2>.=R1?.)(2>.R1?.(10.R20.(:.(3;.R25.)R1>.))))P,(49.$13.R2;.(10.R21.R20.)(1:.(2.&8.)(4:.=)(1>.(2.&8.))))P,(49.$13.R2<.R22.(1:.(2.&8.)(4:.=)(1>.(2.&8.))))P,Pb,(4;.$26.$21.)Pgh',$4<.P,(6.(4.$4<.)(30.(4;.$26.$21.)$4<.(31.$23.(4=.$26.$32.$21.$4>.)(4?.$26.$32.$33.$21.$4>.$50.)$4<.)(34.$23.(4=.$26.$32.$21.$4>.)(4?.$26.$32.$33.$21.$4>.$50.)$4<.)R2.(51.R2<.))(37.$4<.R1.))P,(6.$26.(35.$26.$21.R3.)(35.$26.$21.R2<.))(52.(2>.R25.(25.$26.$21.R4.))(2>.(:.(25.$26.$21.R4.)+10.)R25.))(53.$13.(54.R4>.R4=.R4<.R4;.R47.R46.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R4:.R49.R48.R36.R35.R34.R33.R45.R31.R30.R2<.R2;.R2?.R1?.R28.R21.(44.R20.))(7.(8.R32.(9.&40.(:.(;.&40.R4=.)-30.))R4<.R4;.R4:.R49.R48.(9.&40.R21.)R45.(<.(=.R2;.R28.))(<.(55.R20.))(9.&40.R24.)R44.(<.R23.)R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.)R31.(9.&40.+3?<90.)R30.(11.(2.&40.))R2>.(12.$13.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until rsv. intros po idx mr st1 MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL HK3 HK2 HK1 LI FBL SC ML B3 ELO EHI RSV RB0r RE0 HCLR.
  dpose MR1 as (WF & CX & GL & AR & GR & SH). dpose WF as ((Hres & RPHres) & WR & DISJ & WA & WG).
  ddestruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  rceilb; unfold UNIT, IB in *.
  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  pose proof (munch_refl [(r_base r + po - 3, r_base r + po)]%Z m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  pose proof (bytes_at_read rsegs m0 _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read rsegs m0 _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.
  (* [comment removed for export] *)
  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
  st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
  (* [comment removed for export] *)
  change (Z_to_bv 64 E) with (wa E).
  st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1.
  rewrite (unsigned_lit idx) by lia. rewrite sllw1_word' by lia. rewrite (wz_unsigned (meta_word mr)) by (unfold meta_word; lia).
  (* [comment removed for export] *)
  dpose MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (SOK3 : store_ok rsegs mX (wa (bv_unsigned a0 + -3)) 1 = true)
      by (replace (bv_unsigned a0 + -3) with (r_base r + (po - 3)) by lia; apply (wr_at_store_ok rsegs mX _ _ (po - 3) 1 HWr); cbn; lia) end.
  st1.
  pose proof (rmrep_wr8 st _ (aadd p (-3)) 255 r MR1 TK Hr Hk ltac:(cbn; lia)
                ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR2.
  cbn [aadd snd] in MR2. fold po in MR2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -3))) [b8 255])
      by (rewrite le1_neg1; f_equal; unfold wa; f_equal; lia) end.
  store_done.
  pose proof (ticks_ok_wr8 st (aadd p (-3)) 255 TK) as TK2.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    dpose MR2 as (_ & _ & _ & _ & _ & SH2); destruct (SH2 (fst p) r Hr Hk) as [HWr2 _]; clear SH2;
    assert (SOK2 : store_ok rsegs mX (wa (bv_unsigned a0 + -2)) 2 = true)
      by (replace (bv_unsigned a0 + -2) with (r_base r + (po - 2)) by lia; apply (wr_at_store_ok rsegs mX _ _ (po - 2) 2 HWr2); cbn; lia) end.
  st1.
  pose proof (rmrep_wr16 _ _ (aadd p (-2)) 0 r MR2 TK2 Hr Hk ltac:(cbn; lia) ltac:(cbn; lia)
                ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR3.
  cbn [aadd snd] in MR3. fold po in MR3. fold st1 in MR3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -2))) (le2 (wz 0)))
      by (f_equal; unfold wa; f_equal; lia) end.
  store_done. clear MR2 TK2 HWr HWr2.
  (* [comment removed for export] *)
  st1. rewrite (all_word (meta_word mr)) by (unfold meta_word; lia).
  replace (meta_word mr mod 32) with (m_last_idx mr) by (unfold meta_word; Z.div_mod_to_equations; lia).
  st1.
  (* [comment removed for export] *)
  apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|exact I].
      intros x Hx. right. right. dexists (fst p), r.
      assert (CASES : x - r_base r = po - 3 \/ x - r_base r = po - 2 \/ x - r_base r = po - 1) by lia.
      destruct CASES as [E1|[E1|E1]]; [exists b3| exists lo8| exists hi]; rewrite E1; (split; [exact Hr|]); (split; [exact Hk|]); (split; [lia|]); assumption. }
  apply evt_done. unfold rfhead_post.
  assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
  deexists 6.
  split; [reflexivity|].
  split; [eapply rpres_except_trans; [exact PE0| exact MU]|]. split; [exact WM0|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. exact MR3.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00i0@L11114081108.125L11114102463.124L12249741094.124L14258741666.116L14258790949.132L15047392262.130L15047393029.129L18586494999.116L18643397249.131L22023279967.113L24377480565.135L25274333651.130L29315069660.112L29315497174.113L29524243131.125L29524243131.134L30317230969.125L30317230969.134L30496653699.125L30496653699.134L32050077487.124L33474526376.125L33474526376.134L33781014569.125L33787327811.115L34217503677.122L36940382948.130L38140572854.125L38140572854.134L40111308612.125L40111308612.134L44017281926.113L44420404170.125L44420404170.134L46304757610.126L47938239946.125L47938239946.134L49081362890.115L49712544523.124L51220585756.125L51220585756.134L5632717941.132 L57020049165.133L57702632612.133L59308628820.132L59308628949.133L59591509826.130L61113290026.113L63152162437.113L63730766366.125L63730766366.134L65158813098.125L65158813098.134L66120358059.125L66120358059.134L68058897448.129L8534514476.116 00000h01`02U03K04D05905n06e07Z08P09J0:?0;20;e0<a0=]0>Z0?W0@L0AA0B_0C`0Da0EY0FN0GZ0HO0ID0J90K50L10Ld0MY0NN0OH0P=0Q20Qf0R_0Sg0To0UN0VC0W<0XX0YT0ZI0[?0\<0]20]h0^^0_T0`\0ad0bY0cPS2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB2B3S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB2B3S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB2H0S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB3R32S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB3S16S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB2B3S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB2Kb1HS2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2sp2lo2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv3SLO2FBS2sp2lo2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv3SLO2FBS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv3P162FB2B03GB0S2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv3P162FB2B03GB0S2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB2MLS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB2MLS3hRP3RCB2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv3P162FB3SB03S163EHI2B02BC2HB3SI03GB0S2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv3P163PHI2FB2B03GB0S2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv3P163PHI2FB2B03GB0S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB2KbS2st1p1r4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB1HS3hRP3RCB2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv3P162FB2B03GB03GB1S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB2B3S2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB2B3S3hRP2lo2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2LO2FBS3hRP2lo2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2LO2FBS2st1p1r4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB2SCS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB2SCS2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB2Kb1HS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB2LIS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB2LIS2st1p1r4base2b32po3idx2mr6stride1E4rsv03rsv2FB4RSV0S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB3IDXS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv3P162FB5RSVLE2B04RSVR3GB0S2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv3P162FB5RSVLE2B04RSVR3GB0S2st1p1r1g4base2po4rsv02FB4RSV0S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB3R32S2m02st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv3P163PHI2FB3BIG2B03DR13DR23GB02Kb2R52K5S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB3R322K6S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB2B3S2st1p1r4base2b33r322po3idx2mr6stride1E4rsv03rsv3P162FB2B32B0S2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB3EHIS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB3EHIS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB3FBLS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv2FB3FBLS2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv3P162FB5RSVLE2B04RSVR3GB0S2st1p1r1g4base2b33r322po3idx6stride1E4rsv03rsv3P162FB5RSVLE2B04RSVR3GB0S2st1p1r1g4base2b33r322po3idx2mr6stride1E4rsv03rsv2FBS2st1p1r4base2b33r322po3idx2mr6stride1E4rsv03rsv2FB3IDX". (* [comment removed for export] *)
#[using="Type"] Lemma rfree_head2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
    (m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (base : aptr) (b3 lo8 hi r32 : Z),
  let po := snd p in
  let idx := Z.land b3 31 in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  let stride := get_stride mr in
  let E := conc st base + UNIT + stride * idx + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  rmrep st m0 -> mem_inv rsegs m0 -> ticks_ok st ->
  stk rsegs m0 lo (bv_unsigned sp + -48) -> rceil <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells rsegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono rsegs m m0 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  meta_slot st g -> m_mem mr = Some base -> fst base = fst p -> 0 <= snd base ->
  cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  0 <= b3 < 256 -> idx <= m_last_idx mr ->
  UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m0 (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m0 (E - 5) [b8 0]) ->
  rsv <= E - (r_base r + po) -> bytes_at rsegs m0 (E - rsv) [b8 0] -> bytes_at rsegs m0 E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 stride) (wz b3) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3fc48) fc None m0 (seg_rom rsegs)).
Proof. rceilb.
  intros until r32. intros po idx mr st1 stride E rsv0 rsv MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL Hmem FB SB0 HK3 HK2 HK1
         AV FRD LI FBL SC ML B3 Hidx S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
  dpose MR1 as (WF & CX & GL & AR & GR & SH). dpose WF as ((Hres & RPHres) & WR & DISJ & WA & WG).
  ddestruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [ddestruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  rceilb; unfold UNIT, IB in *.
  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  pose proof (rmrep_meta_chunk st m0 g MR1 MSL) as MM.
  fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. cbn [oconc].
  replace (conc st base + stride + stride * idx + 12) with E by (unfold E; lia).
  fold rsv0.
  (* [comment removed for export] *)
  st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
  - (* [comment removed for export] *)
    replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
    assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
    subst mr.
    eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
      [exact MR1| exact MI| exact TK| exact ST| rceilb; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
      | exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
  - (* [comment removed for export] *)
    ddestruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
    pose proof (bytes_at_read rsegs m0 _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
    cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
    replace (E - 4) with (conc st base + stride + stride * idx + 8) in RD4 by (unfold E; lia).
    pose proof (bytes_at_read rsegs m0 _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
    replace (E - 5) with (conc st base + stride + stride * idx + 7) in RD5 by (unfold E; lia).
    (* [comment removed for export] *)
    st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }
    (* [comment removed for export] *)
    st1.
    rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }
    (* [comment removed for export] *)
    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
    replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
    assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
    subst mr.
    eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
      [exact MR1| exact MI| exact TK| exact ST| rceilb; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
      | exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00o0@L1023186998.161 L11114070788.157L11882686727.163L11889055804.164L13204087972.161L14258741666.131L16075441888.165L22021303794.128L23186217653.142L27823659829.156L28212591088.156L28227477070.162L28372211924.161L29315069148.162L29317232961.126L29317399675.128L29524583922.156L29713772808.165L30317046832.156L30496478922.156L31378308326.136L33474341857.156L33773558382.156L33787327811.130L34217285255.148L34705803648.163L35189674350.139L35189674350.140L36028488970.163L36032651178.157L36032655604.161L36032655735.160L37855283162.147L37857313357.127L38140879871.156L38142564733.157L39171200184.138L40111482893.156L40281870821.148L40825688260.165L41361206858.156L42048681435.162L42310664924.132L42875510527.156L43059739913.134L44015063851.128L44279994491.162L44420613251.156L47937890947.156L49081362890.130L52448723318.139L52448723318.140L56368389193.162L59308628179.134L59600687366.163L61111022983.128L63152162437.127L63624026922.161L65158628067.156L67509714473.165L8832910886.162 L8871789335.156 L8990858532.150 00001202703A04K05T06T07Y08Y09Y0:U0;R0<X0=a0>c0?`0@]0AP0BR0CJ0D60E90F50Fb0Ga0I:0JA0L30Mn0O40P:0QC0RL0SV0T[0UG0VL0Wd0XW0Yj0Zl0[\0\^0]i0_00`:0a70bY0cE0d10do0ff0hf0il0k<0l>0m>0nB0oO10<11A12a13c152S2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FBS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2B32FBS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2SC4SC482FBS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2SC4SC482FBS3hRP2lo2st1p1r1g2b33lo82hi2po5off163idx4base2LO3P163EHI2B02BC2FB3GB03MWRS2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2H0S2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FB2SZS2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2B3S2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FBS2st1p1r1g2b33lo82hi2po5off163idx4base3P163EHI2B02FB3GB03MWRS2st1p1r1g2b33lo82hi2po5off163idx4base3P164Hidx2B02FB3GB03MWRS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FB3MWRS3hRP2lo2st1p1r1g2b33lo82hi2po5off163idx4base2LO3P163EHI2B02BC2FB3GB03MWRS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FBS2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsvS2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsvS2sp2lo2st1p1r1g2b33lo82hi2po5off163idx4base3SLO2FBS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FBS2st1p1r1g2b33lo82hi2po5off163idx4base3P162B02FB3GB03MWRS2st1p1r1g2b33lo82hi2po5off163idx4base2ML2FBS2sp2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FBS2st1p1r1g2b33lo82hi2po5off163idx4base3P163PHI2B02FB3GB03MWRS2st1p1r1g2b33lo82hi2po5off163idx4base3S162FBS2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv1HS3hRP3RCB2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv3P162B02FB3GB03GB1S2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FB4MW5RS3hRP2ra2sp2lo2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2LO3SLO3P163EHI2B02BC2FB3HB05Ha_st5Hl_stS3hRP2sp2s02lo2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2LO3SLO3P163EHI2B02BC2FB3HB05Ha_st5Hl_st2s12s22s3S2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FB3MWRS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FB3MWRS2st1p1r1g2po4base2mr2LI2FB2b33lo82hi3r325off163idx6stride1E4rsv03rsv3MWRS2st1p1r1g2po4base2mr2ML2FB2b33lo82hi3r325off163idx6stride1E4rsv03rsv3MWRS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv3P163PHI2FBS2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv3P163PHIS2st1p1r1g2b33lo82hi2po5off163idx4base2B32FBS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2B32FBS3hRP2sp2lo2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2LO3SLO3P162B02FBS3hRP2lo2st1p1r1g2b33lo82hi2po5off163idx4base2LO2FBS2a02st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2HP3P162B02FB3GB0S2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FBS2st1p1r1g2b33lo82hi2po5off163idx4base2AV2FB3FRDS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FBS2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv3P163PLO2B02FBS2st1p1r1g2b33lo82hi3r322po5off163idx4base3P165RSVLE2B04RSVR2FB3GB03MWRS2sp2lo2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv3SLO2FBS2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsvS2sp2lo2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv3SLO3P162B02FB3GB03MWR1A1n2HAS2st1p1r1g2b33lo82hi2po5off163idx4base2SC2FBS2st1p1r1g2b33lo82hi2po5off163idx4base2LI2FBS2st1p1r2b33lo82hi2po5off163idx4base2mr6stride1E4rsv03rsv4RSV0S3hRP2ra2sp2lo2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2LO3SLO3P163EHI2B02BC4RSVR2FB3HB05Ha_st5Hl_stS3hRP2sp2s02lo2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2LO3SLO3P163EHI2B02BC4RSVR2FB3HB05Ha_st5Hl_st2s12s22s3S2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FB3MWRS2a02st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2HP3P162B02FB2K0S2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FBS2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2B3S2st1p1r2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv3P162B0S2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2ML4SC482FB2KmS2st1p1r1g2b33lo82hi2po5off163idx4base3FBL2FBS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2FB2SZS2sp2lo2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv3SLO3P162B02FB3GB03MWR1x2HxS2st1p1r1g2b33lo82hi3r322po5off163idx4base3P165RSVLE2B02FB3GB03MWRS2st1p1r1g2b33lo82hi3r322po5off163idx4base2mr6stride1E4rsv03rsv2LI3FBL2SC2ML2FB". (* [comment removed for export] *)
#[using="Type"] Lemma rfree_head : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (lo : Z) st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo8 + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  let stride := get_stride mr in
  let E := conc st base + UNIT + stride * idx + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  rmrep st m -> mem_inv rsegs m -> ticks_ok st ->
  stk rsegs m lo (bv_unsigned sp) -> rceil <= lo -> lo <= bv_unsigned sp - 48 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
  16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
  (* [comment removed for export] *)
  (m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
  UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m (E - 5) [b8 0]) ->
  rsv <= E - (r_base r + po) -> bytes_at rsegs m (E - rsv) [b8 0] -> bytes_at rsegs m E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs)).
Proof. rceilb.
  intros until r32. intros sh po off16 idx base mr st1 stride E rsv0 rsv MR MI TK ST LO SLO Hr Hk HP AL P16 PLO PHI HK4 HK3 HK2 HK1 Hgh Hg MSL G0 Hmem Har Hchk
         AV FRD SE LI FBL SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
  dpose MR as (WF & CX & GL & AR & GR & SH). dpose WF as ((Hres & RPHres) & WR & DISJ & WA & WG).
  ddestruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
  pose proof (wmono_refl rsegs m) as WM.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) HK3) as [_ B3].
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [ddestruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  assert (FB : fst base = fst p) by reflexivity.
  assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
  assert (SB0 : 0 <= snd base) by (unfold base; cbn; unfold UNIT; lia).
  (* [comment removed for export] *)
  revert BIG RB0r RE0.
  rceilb; unfold rfree_entry, UNIT, IB in *. intros BIG RB0r RE0.
  (* [comment removed for export] *)
  st1. if_cases K0; zify_cond K0. { exfalso. lia. }
  carve_frame 48%nat ST.
  st1. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; rceilb; lia) end.
  eapply evt_cut.
  { eapply rget_meta_spec with (st := st) (p := p) (r := r) (g := g) (gh := gh) (ar := ar) (b3 := b3) (lo := lo8) (hi := hi).
    all: try eassumption. all: try lia. }
  (intros ms' dd_H; ddestruct dd_H as (ga2 & ga3 & ga4 & ga5 & ->)).
  replace (ret_pc (Z_to_bv 64 0x3fc00)) with (Z_to_bv 64 0x3fc00) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rmrep_meta_chunk st mX g MR1 MSL) as MM;
    destruct (rmrep_shadow_read st mX (fst p) r (po - 3) b3 MR1 Hr Hk ltac:(lia) HK3) as [R3 _] end.
  fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  replace (r_base r + (po - 3)) with (bv_unsigned a0 + -3) in R3 by lia.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (MW : mw_ok mr) by (unfold mw_ok; lia).
  pose proof (meta_word_range mr MW) as MWR. pose proof (meta_word_maplen mr MW) as MW12.
  pose proof (meta_word_last_idx mr MW) as MW31. pose proof (meta_word_sc2 mr MW) as MWS. pose proof (meta_word_pg mr MW) as MWP.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (K2 : forall a4v a5v a6v, evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR (Z_to_bv 64 0x3fc00) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 stride) (wz b3) a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3fc48) fc None mX (seg_rom rsegs))) end.
  { intros a4v a5v a6v.
    lazymatch type of MUs with munch ?W _ _ => assert (DJ : forall A n, A + n <= lo -> disjoint_from W A n) by (intros A n HA; cbn; lia) end.
    lazymatch type of MUs with munch ?W m ?mY =>
      assert (PE0 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m mY)
        by (apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp)) W); [exact MUs| exact WM|];
            cbn [ivs_covered]; split; [|exact I]; intros x Hx; apply rfree_fp_stack; lia) end.
    subst rsv rsv0 E stride mr.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    eapply (rfree_head2 ra sp gp tp t0 t1 t2 s0 s1 a0 a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc m mX _ lo st p r g base b3 lo8 hi r32) end;
      [exact MR1| assumption| exact TK| exact ST| ulia| ulia| exact FR| exact PE0| exact WM| exact Hr| exact Hk| exact HP| exact AL| ulia| ulia
      | exact MSL| exact Hmem| exact FB| exact SB0| exact HK3| exact HK2| exact HK1| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia
      | intros Hb3; ddestruct (BIG Hb3) as (X1 & X2 & X3 & X4); split; [exact X1|]; split; [exact X2|]; split;
          (eapply bytes_at_transport; [eassumption| exact MUs| apply DJ; cbn; try rewrite length_le4; ulia])
      | ulia
      | exact RB0r
      | exact RE0
      | exact HCLR]. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. fold idx. rewrite MW12.
  assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (KS : forall a2v a4v, (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
    evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR (Z_to_bv 64 0x3fc00) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 gw (wz (meta_word mr))
                a2v (wz b3) a4v ga5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3fc2c) fc None mX (seg_rom rsegs))) end.
  { intros a2v a4v COND. specialize (SC48 COND).
    assert (STR : stride = 16 * size_class (m_sizeclass mr)).
    { unfold stride, get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
    (* [comment removed for export] *)
    assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    st1. st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite MWS. st1. st1.
    replace (94460 + m_sizeclass mr * 2) with (94460 + 2 * m_sizeclass mr) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (RS' : ov_read_bytes rsegs mX (Z_to_bv 64 (94460 + 2 * m_sizeclass mr)) 2 = Some (le2 (wz (size_class (m_sizeclass mr))))) end.
    { replace (Z_to_bv 64 (94460 + 2 * m_sizeclass mr)) with (wa (RSIZE_CLASSES + 2 * m_sizeclass mr)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
      apply rsize_classes_read; [assumption| lia]. }
    pose proof (size_class_range (m_sizeclass mr) ltac:(lia)) as SZ.
    st1. try rewrite (Z.mod_small (size_class (m_sizeclass mr))) by lia.
    st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class (m_sizeclass mr) * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
    rewrite Egw. apply K2. }
  (* [comment removed for export] *)
  st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  - apply KS. left. exact Km.
  - (* [comment removed for export] *)
    st1. rewrite MW31. st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    + apply KS. right. exact Kl.
    + (* [comment removed for export] *)
      st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 stride).
      2:{ unfold stride, get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
      rewrite Egw. apply K2.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
