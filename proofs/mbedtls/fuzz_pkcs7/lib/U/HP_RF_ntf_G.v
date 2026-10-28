(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B MallocKit_A3 MallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_get_meta HP_RF_ntf_A HP_RF_ntf_E.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_ntf_G () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rfree_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B3.mw_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_maplen"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_mem"; "Corelib.Init.Datatypes.Some"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Unknown"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aadd"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.UNIT"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.g_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_avail"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freed"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_last_idx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freeable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_sizeclass"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area_of"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.a_check"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_secret"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.testbit"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rnest_call_post"; "RocqVerifyHarness.AgentSubmission.Heap.MallocModel_B.grp_del"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_word"; "RocqVerifyHarness.AgentSubmission.Heap.F_ntf_B.fm_facts"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_ntf_A.rntf_frame"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rntf_ret_post"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B.fm_st"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Definition rnest_call_post (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (fr : list cell) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_G ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R?.(6.(7.(8.&40.+40140.)(8.&40.(9.(:.&40.O17.)-60.))O16.O15.R>.R=.R<.(8.&40.(;.O8.O4.))O14.(8.&40.O3.)(8.&40.O2.)R;.R:.R9.R8.R7.R6.(8.&40.$<.)(8.&40.(;.O8.O5.))O13.O12.O11.O10.O?.O>.O=.O<.R5.R4.R3.R2.)O;.(8.&40.+3?>;8.)O:.(=.(2.&40.))R1.(>.$?.)))(4.(10.(11.O8.O9.(:.&40.O17.))O7.R1.)(4.(12.$?.O7.R1.)(4.(13.$?.R1.)(4.(14.$?.R1.O9.(9.(:.&40.O17.)-60.))(4.(15.$?.R1.(9.(:.&40.O17.)-60.)O1.)(16.VhRP,O6.R1.)))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00\0@L11111953156.159L1277867789.163 L15045295287.156L16075377781.151L16075436744.159L19441889481.159L1990565974.148 L22682493304.159L24177407718.160L25069450385.160L2525201769.159 L25449201753.158L25960005708.150L26911975950.158L30494420040.159L31276474185.159L34756806822.147L35503748457.159L38140015096.163L38142941565.159L39792877254.159L40376485778.159L40638190098.159L41363264712.159L41415827659.158L43735502700.159L44418498049.159L45761382066.159L47371166144.159L47940014081.159L5157727464.159 L52153965877.163L53282662239.156L54111550491.160L59974406727.160L64451981311.159L64491195648.128L64862093566.159L65160706145.159L6531215066.157 L6755559098.157 L67654633047.161L7909878667.160 L8832910886.161 00000G00`01401Q01l02X03R03S04E04e05A05Z06`07407R08@09109M09d0:;0:d0;=0;\0<>0<R0=H0=f0>?0>X0?60?]0@10@E0@o0AQ0B?0Bn0CG0Ce0D90DM0Dk0Eg0FKS2fr2b34idx12B33FRL3LFRS2fr2st1p2b34idx13FRL3LFRS2fr2b34idx13FRL3LFRS2fr2st1g2b34idx13FRL3MWR3LFRS2fr2st2b34idx13SEC3FRL3LFRS2fr2st1p2b35off164idx13FRL3LFR1r2Cp3RB03Bb0S2fr1p5base12b34idx13FRL3LFR1r3Sp03RB01a1k3Hkk2rg3Sa04RgB0FS3hRP3RCB2fr2st1p2b34idx13FRL3LFR1r2Cp3Sp13RBC3LENS2sp2fr2st1p2b34idx13FRL3LFR3LENS2fr2b33hi84idx13HI83FRL3LFRS2fr2st1p2b34idx13FRL3LFRS2fr2st1p5base12g12b34idx13FRL3LFR1r2Cp3Sp03RB01a1k2rg3Sa04RgB02HG3HGmS2fr2b34idx13FRL3LFRS2fr2st2g12b34idx13ML13FRL3LFRS2fr2b33lo83hi85off164idx13LO83HI83O163FRL3LFRS2fr1p5base12b34idx13FRL3LFR1r3Sp01a1k3Hkk2rg3Sa0S2fr2b33lo84idx13LO83FRL3LFRS2fr2b34idx12B33FRL3LFRS2fr2b34idx12B33FRL3LFRS2fr2st1p5base12b35off164idx13FRL3LFR3HBcS2fr2st1p2b34idx13FRL3LFRS2fr2st2g12b34idx13FRL4G1B03LFRS2fr2st2g12b34idx13AV13FRL3LFR3FR1S2fr2b34idx13FRL3LFRS3hRP3RCB2fr2st1p2b34idx13FRL3LFR1r2Cp3Sp03Sp13RB03RBCS2fr2st2g12b34idx13SC13FRL3LFRS2fr2st1p2b34idx13FRL3LFRS2fr2st1p2b34idx13FRL3LFRS2fr2st2g12b34idx13LI13FRL3LFRS3hRP3RCB2fr2st2g12b34idx13FRL4G1B13LFRS2fr2b34idx13FRL3LFRS2fr2b34idx13FRL3LFRS2fr2st1p2b34idx13FRL3LFR1r2Cp3Sp03RB03LENS2fr2st2g12b34idx13SC13FRL3LFR3HltS3hRP3RCB2fr2st1p2b34idx13FRL3LFR1r2Cp3Sp13RBCS2fr2st1p5base12b35off164idx13FRL3LFR1r3Sp03Bb0S2fr2st1p2b34idx13FRL3LFRS2fr2st2g12b34idx13FB13FRL3LFRS2fr2b34idx13FRL3LFRS2fr2b34idx13FRL3LFRS2fr2st1p2b34idx13FRL3LFR1x2HxS3hRP2sp2fr2st1p2b32lo4idx13FRL2LO4LOLE3LFR1r2Cp3Sp13RBC3LENS2sp2fr2b32lo4idx13FRL4LOLE3LFR1x2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma rntf_nest_call : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_G ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pfr,(18.$19.)Pst,$1:.Pg,$1;.Pp,$1;.Pbase1,$1;.Pg1,$1;.Pghp,$1<.Pgh1,$1<.Par1,$1=.Pb3,$1>.Plo8,$1>.Phi8,$1>.Poff16,$1>.Plo,$1>.Zmr,$1?.(20.R=.R<.)Zmr1,$1?.(20.R>.R:.)Zidx1,$1>.(21.R7.+1?.)P,(16.VhRP,R10.R12.)P,(13.$?.R13.)P,(22.R12.R11.)P,(23.R6.)P,(5.$1>.(24.R7.)=)P,(5.$25.(26.R8.)(27.$1;.R13.))P,(5.(3.$1<.)(28.$1;.$1<.(29.$1;.(2:.$2;.$2<.$1>.$2=.)(2>.$2;.$2<.$2?.$1>.$2=.$30.)$1<.)(31.$1;.(2:.$2;.$2<.$1>.$2=.)(2>.$2;.$2<.$2?.$1>.$2=.$30.)$1<.)R14.(32.R16.))(27.$1<.R11.))P,Po,$1>.P,(4.(33.=R1.)(34.R1.+<.))(1.$1>.Lh,$1>.(5.$35.(36.(37.R1:.(38.$2;.$1>.R18.))(9.(39.$2;.$1>.R18.)R3.))(3:.R1.)))P,(3;.$?.R1:.(3<.(;.R18.R16.)+4.)(3=.(2.&8.)(3>.=)(3=.(2.&8.)(3>.R10.)(3=.(2.&8.)(3>.R?.)(3=.(2.&8.)(3>.R>.)(3?.(2.&8.)))))))P,(4.(33.=R11.)(34.R11.+100.))P,(4.(33.=R11.)(34.R11.+100.))P,(4.(33.=R11.)(34.R11.+100.))P,(5.$1>.R11.(9.R13.(40.+100.R12.)))P,(5.$1;.R1:.(41.R1;.(3<.(42.(40.$43.R12.))$43.)))P,(5.(3.$1<.)(28.$1;.$1<.(29.$1;.(2:.$2;.$2<.$1>.$2=.)(2>.$2;.$2<.$2?.$1>.$2=.$30.)$1<.)(31.$1;.(2:.$2;.$2<.$1>.$2=.)(2>.$2;.$2<.$2?.$1>.$2=.$30.)$1<.)R1;.(32.R1>.))(27.$1<.R18.))P,(5.$25.(44.R19.)(27.$1;.R1;.))P,(22.R20.R1<.)P,(5.$25.(26.R13.)(27.$1;.R1>.))P,(4.(33.=(45.R14.))(34.(45.R14.)(46.+2.+20.)))P,(4.(33.=(47.R15.))(34.(47.R15.)(46.+2.+20.)))P,(4.(33.=(48.R16.))(34.(48.R16.)+20.))P,(4.(33.=(49.R17.))(34.(49.R17.)+2.))P,(4.(33.=(4:.R18.))(34.(4:.R18.)+40.))P,(4.(33.=(24.R19.))(34.(24.R19.)(46.+2.+28.)))P,(5.(3.$1=.)(28.$1;.$1=.(29.$1;.(2:.$2;.$2<.$1>.$2=.)(2>.$2;.$2<.$2?.$1>.$2=.$30.)$1=.)(31.$1;.(2:.$2;.$2<.$1>.$2=.)(2>.$2;.$2<.$2?.$1>.$2=.$30.)$1=.)(4;.R24.)(4<.R28.))(27.$1=.R21.))P,(5.$1>.(4=.R22.)(4>.(4?.R29.)))P,(4.(33.=(4>.(4?.R2:.)))(34.(4>.(4?.R2:.))(46.+2.+40.)))P,(33.R1<.(48.R1=.))P,(5.$50.(51.(45.R1>.)R1=.)$52.)P,(5.$50.(51.(47.R1?.)R1>.)$52.)P,P,(34.(4:.R20.)+30.)(4.(33.(40.(53.(4:.R21.))R20.)R24.)(34.R24.(40.(53.(4:.R21.))(9.R20.+1.))))P,P,(33.+30.(4:.R21.))(5.$1>.(4:.R22.)+3?.)P,P,(54.(5.$1>.(24.R22.)=))(33.R26.(3<.(40.(24.R23.)+100.)+1.))P,(15.$?.R33.(9.(:.&40.R50.)-60.)R32.)P,(5.$55.(56.R33.)#60.)P,(14.$?.R35.R27.(9.(:.&40.R52.)-60.))P,(33.(57.VhRP,)R28.)P,(33.R29.(3<.(:.&40.R54.)+60.))(58.$?.(59.R55.R54.R53.R4>.R46.R45.R44.R43.R42.R41.R40.R3?.R3:.R39.R2:.R36.R38.(5:.R36.R35.R34.)R35.R34.(;.R36.R32.)R27.R37.)(6.(7.R56.(8.&40.(9.(:.&40.R55.)-60.))R54.R53.R52.R51.R50.R4?.R4>.(8.&40.(;.R36.R35.))R4=.(5;.(5<.R29.))R4<.R4;.R4:.R49.R48.(8.&40.$<.)R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.)R3:.(8.&40.+40114.)R39.(=.(2.&40.))R38.(>.$?.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until lo. intros mr mr1 idx1 MR MI MSL MW HML Hmem Hp UNK HDR B3 LO8 HI8 O16 Hb1 Hgh1 Hg1 MS1 Hmem1
         AV1 FR1 LI1 FB1 SC1 ML1 Har1 Hchk SEC Hidx Hav Hfr Hsc Hsc63 Hml FR FRL ST LO LOLE. subst mr mr1.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (meta_word_range _ MW) as MWR. dpose MW as (LI & FB & SCR & ML).
  pose proof (meta_word_maplen _ MW) as M12.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose proof (rmeta_slot_bounds st m g1 MR MS1) as G1B.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  dpose MR as (WF & CX & GL & AR & GR & SH). dpose WF as ((Hres & RPHres) & WR & DISJ & WA & WG).
  ddestruct (rgroup_conc st p ghp WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
  destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RFr). pose proof (round_up_pg_ge (r_len r)) as RU.
  pose proof (rreserved_disjoint _ _ RFr) as (Dr1 & Dr2 & Dr3 & Dr4).
  (* [comment removed for export] *)
  ddestruct (WG base1 gh1 Hgh1) as (rb & Hrb & _ & Bb0 & Bb1 & BbA). rewrite Hb1 in Hrb. cbn [aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
  assert (HBc : conc st base1 = conc st p - 16 * off16 - 16).
  { rewrite Hb1. rewrite conc_aadd by (cbn; rewrite Hr; eauto). unfold UNIT. lia. }
  rewrite Hb1 in Bb0. cbn [aadd snd] in Bb0.
  dpose MS1 as (a & ara & k & Ha & Hkk & Eg).
  ddestruct (WA a ara Ha) as (rg & Hrg & Sa0 & Sa1 & AAL & ANG & ALR).
  ddestruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & RFa).
  assert (HG : conc st g1 = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  assert (Hao : area_of g1 = a).
  { rewrite Eg. unfold AREA_HDR, META_SIZE. apply area_of_slot; [exact AAL | unfold NSLOTS in Hkk; lia]. }
  assert (HGm : conc st g1 mod 4096 = AREA_HDR + META_SIZE * k).
  { rewrite HG. apply page_off_mod; [exact RgBAL | exact AAL | unfold AREA_HDR, META_SIZE, NSLOTS in *; lia]. }
  assert (P16m : conc st p mod 16 = 0) by (rewrite Cp; apply base16_mod; assumption).
  rceilb; unfold RCTX, AREA_HDR, META_SIZE, NSLOTS in *.
  assert (HAeq : r_base rg + snd a = conc st g1 - conc st g1 mod 4096) by lia.
  (* [comment removed for export] *)
  change (frozen (conc st p mod 16 = 0)) in P16m.
  change (frozen (r_base rg + snd a = conc st g1 - conc st g1 mod 4096)) in HAeq.
  clear HGm AAL RBAL RgBAL SpA BbA.
  ddestruct GB as (GB0 & GB1 & GB2 & _). ddestruct G1B as (G1B0 & G1B1 & G1B2 & _).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st p, conc st p + 8)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  st1. rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite M12, HML. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  rmeta_chunk MR MSL CH. rewrite Hmem in CH. cbn [oconc] in CH.
  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rmrep_group_read st mX base1 gh1 MR Hgh1) as [RG _];
    pose proof (rmrep_meta_chunk st mX g1 MR MS1) as MM;
    pose proof (rmrep_area_check_read st mX (area_of g1) ar1 MR Har1) as RA;
    pose proof (rmrep_ctx_secret_read st mX MR) as RC;
    pose proof (bytes_at_read rsegs mX _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4;
    pose proof (bytes_at_read rsegs mX _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3;
    pose proof (bytes_at_read rsegs mX _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2
  end.
  rewrite Hg1 in RG. unfold pw in RG. cbn [oconc] in RG.
  unfold meta_cells in MM. rewrite Hmem1 in MM. unfold pw in MM. cbn [oconc] in MM. unfold meta_word in MM.
  rewrite Hchk in RA. rewrite Hao, (conc_region' st a rg Hrg) in RA. unfold RCTX in RC.
  change (firstn 1 (skipn (Z.to_nat 0) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 0] in R4.
  change (firstn 1 (skipn (Z.to_nat 1) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 b3] in R3.
  change (firstn 2 (skipn (Z.to_nat 2) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 lo8; b8 hi8] in R2.
  replace (conc st p - 4 + 0) with (conc st p - 4) in R4 by lia.
  replace (conc st p - 4 + 1) with (conc st p - 3) in R3 by lia.
  replace (conc st p - 4 + 2) with (conc st p - 2) in R2 by lia.
  rewrite <- (le2_lohi lo8 hi8) in R2 by lia. rewrite <- O16 in R2.
  (* [comment removed for export] *)
  st1.
  eapply evt_cut.
  { eapply (rget_meta_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (conc st p) (conc st g1) (conc st base1) (r_base rg + snd a) b3 off16
            (m_avail (get_meta_rec st g1)) (m_freed (get_meta_rec st g1)) (m_last_idx (get_meta_rec st g1)) (m_freeable (get_meta_rec st g1))
            (m_sizeclass (get_meta_rec st g1)) (m_maplen (get_meta_rec st g1)) (c_secret (ctx st))).
    all: lazymatch goal with
         | |- ov_read_bytes _ _ (wa (_ - 4)) 1 = _ => exact R4
         | |- ov_read_bytes _ _ (wa (_ - 3)) 1 = _ => exact R3
         | |- ov_read_bytes _ _ (wa (_ - 2)) 2 = _ => exact R2
         | |- ov_read_bytes _ _ (wa (conc _ _)) 8 = _ => exact RG
         | |- ov_read_bytes _ _ (wa 512968) 8 = _ => exact RC
         | |- ov_read_bytes _ _ (wa RCTX) 8 = _ => exact RC
         | |- ov_read_bytes _ _ (wa (r_base _ + snd _)) 8 = _ => exact RA
         | |- rw_cells _ _ (conc _ _) _ => exact MM
         | |- _ -> ov_read_bytes _ _ _ 2 = _ => intros Hlt; apply rsize_classes_read; [assumption | lia]
         | |- _ => idtac
         end.
    all: first [ exact P16m | exact HAeq | exact Hidx | exact Hav | exact Hfr | exact Hsc | exact Hsc63 | exact Hml
               | lia | unfold wz; rewrite ?unsigned_lit by lia; lia | unfold UNIT in *; lia ]. }
  (intros ms' dd_H; ddestruct dd_H as (ga2 & ga3 & ga4 & ga5 & ->)).
  replace (ret_pc (Z_to_bv 64 0x4012c)) with (Z_to_bv 64 0x4012c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* [comment removed for export] *)
  st1.
  unfold wa in R3. unfold wz. replace (conc st p - 3) with (conc st p + -3) in R3 by lia.
  st1.
  (* [comment removed for export] *)
  clear CH MM RG RA RC R4 R2.
  dpose MR as (_ & _ & _ & _ & GR0 & _). ddestruct (GR0 p ghp Hp) as (w8 & RWp & _). clear GR0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rw_cells_store_ok_at rsegs mX _ _ 0 (C8 (pw st (g_meta ghp))) 8 (Z_to_bv 64 (conc st p)) RWp eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK end.
  clear RWp.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_group_hdr_zero st mX p ghp (le8 (Z_to_bv 64 0)) MR Hp UNK (length_le8 _)) as MR2
  end.
  rraw_store_finish (conc st p) (le8 (Z_to_bv 64 0)) FR ST MU WM SOK.
  apply (rmrep_grp_del_eq st _ g p) in MR2.
  (* [comment removed for export] *)
  st1. st1.
  apply evt_done. unfold rnest_call_post. deexists 14.
  split. { unfold idx1. rewrite ?zxb_b8 by lia. unfold wz. rewrite ?(wz_unsigned b3), ?(unsigned_lit b3) by lia.
           cbv delta [mkR]. unfold RCTX. reflexivity. }
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + eapply rfree_fp_group; [exact Hp | lia]. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rntf_nest_ret : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_G ()) "Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pjunk,(18.(2.&8.))Praw,(2.&40.)Ps0o,(2.&40.)Ps1o,(2.&40.)Ps2o,(2.&40.)Ps3o,(2.&40.)Pst0,$1:.Pst,$1:.Pg,$1;.Plo,$1>.P,(16.VhRP,R3.R;.)P,(13.$?.R<.)P,(22.R5.R4.)P,(5=.R6.R5.)P,(5.$1>.(;.R7.R6.)(;.R8.R6.))P,(5.(2.&40.)R27.(8.&40.$5>.))P,(15.$?.R11.(9.(:.&40.R2?.)-60.)(5?.VhRP,R10.R;.R<.R=.R>.R?.))P,(14.$?.R12.R8.(9.(:.&40.R30.)-60.))P,(33.(57.VhRP,)R9.)P,(33.R:.(3<.(:.&40.R32.)+60.))(58.$?.(60.VhRP,R13.R33.R32.R31.R12.R11.R10.R?.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R;.R=.R15.(61.R=.R<.)R2;.R2:.)(6.(7.(8.&40.+40140.)(8.&40.(9.(:.&40.R33.)-60.))R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.(8.&40.$<.)(8.&40.(;.R>.R<.))R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(8.&40.+40140.)R16.(=.(2.&40.))R15.(>.$?.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until lo. intros MR MI MSL FMF Hcg S1 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  rceilb.
  st1. st1. st1.
  rewrite <- Hcg.
  eapply (rntf_fm _ sp gp tp _ _ _ s0 s1 a1 a0 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m junk raw s0o s1o s2o s3o st g lo);
    first [exact MR | assumption | exact MSL | exact FMF | exact S1 | exact FR | exact ST | rceilb; lia].
Qed.

End RP_1.
