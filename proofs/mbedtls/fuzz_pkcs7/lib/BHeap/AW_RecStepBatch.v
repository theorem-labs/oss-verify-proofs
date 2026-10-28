(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR AW_FreeRB AW_FreeFam.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_Poison AW_Populate
     AW_DepotA AW_DepotB AW_DepotC AW_DepotInv AW_DepotTop AW_MallocA AW_AllocA AW_AllocB AW_MallocB AW_MallocC AW_ClassId AW_Combined AW_Refill AW_Large
     AW_CfgS AW_CfgDefs AW_PopulateCfgS AW_PoisonBig AW_SMalloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_QPut AW_Enqueue AW_CbRecycle AW_LCDealloc AW_RTA AW_RecLC AW_RecChunk AW_RecStep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs AW_FakeRep HMLib HM HMFrame AW_FreeHM AImgW.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ahx.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ahx. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_RecStepBatch () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "Corelib.Init.Datatypes.nat"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.RIq"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.qcache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "Stdlib.Lists.List.tl"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_recb"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.WFR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.HMq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_K"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_CS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.fkeep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_elems"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_1.RecStepBatch.batch_step_post"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.A_LC_DEALLOC"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

(* [comment removed for export] *)
#[using="Type"] Lemma bwf_drop_mid : forall l1 b l2, bwf (l1 ++ b :: l2) -> bwf (l1 ++ l2).
Proof.
  intros l1 b l2 W. pose proof W as [F A].
  assert (W' : bwf (b :: l1 ++ l2)).
  { apply (bwf_of_perm (l1 ++ b :: l2)); [exact W| cbn [map]; rewrite !map_app; cbn [map]; apply Permutation_sym; apply Permutation_middle|].
    apply Forall_app in F as [F1 F2]. inversion F2; subst. constructor; [assumption| apply Forall_app; split; assumption]. }
  exact (bwf_tail _ _ W').
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma RIq_popb : ltac2:(CDefT.buildp (gd_tbl_AW_RecStepBatch ()) "Ph,$0.Ph',$0.PC,$1.Pbc,$2.Pi,$3.Pm,P,(4.&40.)(5.(4.&8.))P,(6.VhAR,R6.R4.(7.(8.$2.$3.)(9.$2.$3.R3.R2.))R1.)P,(:.$;.(<.R6.)(<.R7.))P,(:.$=.(>.R7.)(>.R8.))P,(:.(?.$10.)(11.(12.R8.))(13.$10.(11.(12.R9.))))(6.VhAR,R9.R8.(14.(8.$2.$3.))R5.)")
(* [comment removed for export] *).
Proof.
  intros h h' C bc i m R EL EG ET. unfold RIq in *. cbn zeta in *. rewrite EL, EG, ET.
  ddestruct R as (QT & QG & BLG & MTX & QC & BLT & (N & BWF & REST)).
  split; [exact QT|]. split; [exact QG|]. split; [exact BLG|]. split; [exact MTX|]. split; [exact QC|]. split; [exact BLT|].
  exact (bwf_drop_mid _ _ _ BWF).
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L66879158937.5000006S1A2HA". (* [comment removed for export] *)
#[using="Type"] Lemma wr_at_off_C8 : ltac2:(CDefT.buildp (gd_tbl_AW_RecStepBatch ()) "Pm,P,(4.&40.)(5.(4.&8.))PA,$1.P,(15.$16.R2.R1.+8.)P,(17.(18.(19.R2.+8.)+10000.)(18.+65?000.R2.))(1:.(4.&40.)Lw0,(4.&40.)(1;.$16.R5.R4.(1<.$1=.(1>.R1.)(1?.$1=.))))")
(* [comment removed for export] *).
Proof.
  intros m A W HA. ddestruct (wr_at_off_u64arr m A 1 ltac:(exact W) ltac:(cbn; lia)) as (ws & U & L).
  destruct ws as [|w0 [|]]; try discriminate L. exists w0. apply u64arr_cells in U. exact U.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section RecStepBatch.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Variable FF : ffam AL.

  (* [comment removed for export] *)
  Definition batch_step_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : ahst) (LF : list (Z * Z)) (C lo : Z) (QS : list (Z * Z)) (m : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecStepBatch ()) "Lcf,$20.(1:.$21.Lms',$21.(1:.$22.Lmo',$22.(1:.(4.&40.)Lt0,(4.&40.)(1:.(4.&40.)Lt1,(4.&40.)(1:.(4.&40.)Lt2,(4.&40.)(1:.(4.&40.)La0,(4.&40.)(1:.(4.&40.)La1,(4.&40.)(1:.(4.&40.)La2,(4.&40.)(1:.(4.&40.)La3,(4.&40.)(1:.(4.&40.)La4,(4.&40.)(1:.(4.&40.)La5,(4.&40.)(1:.(4.&40.)La6,(4.&40.)(1:.(4.&40.)La7,(4.&40.)(1:.(4.&40.)Lt3,(4.&40.)(1:.(4.&40.)Lt4,(4.&40.)(1:.(4.&40.)Lt5,(4.&40.)(1:.(4.&40.)Lt6,(4.&40.)(1:.P,(4.&40.)(5.(4.&8.))Lm',P,(4.&40.)(5.(4.&8.))(1:.$23.Ldr,$23.(1:.$3.Lcnt,$3.(1:.(5.$23.)Lf,(5.$23.)Zh',$0.(24.O6.R3.R2.R1.)(25.(:.$20.R17.(26.R16.R15.))(25.(:.$21.R16.(27.(28.O18.(29.&40.O17.)O16.O15.R14.R13.R12.O14.O13.R11.R10.R?.R>.R=.R<.R;.R:.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R9.R8.R7.R6.)O8.(2:.O18.)O7.(14.(4.&40.))R5.(2;.$16.)))(25.(2<.VhAR,R1.)(25.(2=.VhAR,R1.O5.R5.)(25.(6.VhAR,R1.O4.(14.(8.$2.$3.))R5.)(25.(2>.VhAR,VAL,VFF,R1.R15.)(25.(2?.R5.R15.)(25.Px,$1.P,(30.VhAR,VAL,VFF,O6.R1.)(30.VhAR,VAL,VFF,R3.R2.)(25.(31.(<.O6.)(32.O6.)O2.(33.(34.O6.))(35.(34.O6.))O3.O17.O1.R5.)(25.(36.$16.O1.R5.)(25.(37.$16.R5.)(38.$16.R5.O3.O17.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0430?L10344898345.3 L10447018765.9 L10447018892.9 L10967500938.6 L10996078549.8 L11027764026.5 L12227744722.3 L12403725915.9 L12533453626.6 L12556558205.3 L13016709440.21L13016856771.17L13016856771.18L13016856771.22L13016856896.20L13016858319.18L13019054197.31L13237742829.3 L13385894424.4 L13980663862.12L13980663862.9 L13982857217.9 L14150857017.3 L14736408896.1 L14866252223.6 L14880938372.2 L14880938373.2 L15203606842.11L15274682276.6 L15539138780.2 L15555298854.20L15702086826.2 L15990724489.3 L16098078423.0 L16487879084.21L16527847552.20L16545396873.3 L16644912580.4 L1708726497.4  L17120848823.0 L18137758790.3 L18155035033.31L18156988195.18L18484489143.16L18486530567.20L18572467734.16L19325175423.2 L19327300958.7 L19345011936.5 L19346787921.6 L19346787921.7 L19346787921.8 L19346787921.9 L19505738506.9 L19505738635.9 L19987118970.6 L2024163583.1  L20896290651.10L21438023802.5 L21623724490.2 L21640453532.6 L22583788388.2 L22889257155.4 L23143738535.14L23277142323.2 L2464680509.3  L25003717198.2 L25070469102.3 L25553707153.6 L25659078307.2 L25752540516.7 L25787593781.2 L26940997473.11L26940997473.12L26940997473.13L26940997473.3 L26940997473.5 L26975107951.4 L26975108078.4 L27177693897.6 L2728726238.2  L27697239754.6 L2803598120.4  L28089937842.7 L28891174338.0 L28956411306.1 L29198200741.4 L29705728350.2 L2978961816.0  L30458420453.9 L31228701566.21L31229111037.17L31229111037.18L31229111037.22L31229111166.20L31677218851.2 L31902476267.31L31904717137.18L31904718558.20L31904718685.17L31904718685.18L31904718685.22L32251262617.31L32253233187.18L32335806250.16L32337938074.20L32931146339.2 L33061060028.8 L3308849698.8  L33470790221.10L33470790221.13L35035954062.10L35267160734.4 L35269483449.1 L35389966226.6 L35521637653.22L36270066207.3 L36303819675.13L36407217492.7 L3668345764.2  L37099668332.5 L37151698158.5 L37637199976.0 L37695499683.2 L37804114501.3 L38019136925.20L38021170221.16L38356265165.7 L38651962962.2 L38692635477.0 L38948636245.0 L39172636981.0 L39268637205.0 L39332637397.0 L39371954277.8 L39476823582.2 L39531535603.2 L39684650846.2 L39742210159.20L40091481971.2 L40166712592.10L40385129652.20L40401253682.0 L40923505818.0 L41008919275.5 L41372190655.2 L41416057805.7 L42141700319.5 L42165362595.22L43158424701.7 L43432397626.6 L43685329970.20L43713642275.2 L43998702901.3 L43998703028.3 L44013154193.7 L44033660401.18L44035877707.31L4485118374.9  L45656573195.31L45658831793.18L45860656981.0 L46247061573.9 L46467458831.3 L46636570196.18L46638819566.31L46649821521.22L47814975085.4 L48096899947.2 L48672541977.31L48674796451.18L48802774710.7 L49200958430.2 L4969361213.3  L50209480639.9 L50852671957.0 L51025133614.10L51025534038.3 L51143253299.2 L51322266494.2 L51518163375.1 L51818430760.6 L5215044130.5  L52877522074.0 L53216299775.12L53537163620.3 L53710725399.7 L54159793143.6 L54237170457.3 L5429687541.20 L54470327665.9 L54582041019.3 L55099840819.3 L55195728159.3 L55588686165.0 L55651815964.31L55653771819.10L55653771946.17L55653771946.19L55653771946.23L55653772073.21L55653772454.18L5713963340.2  L57169543802.8 L57169543931.6 L5721498072.16 L57694037283.18L57696279449.31L57747755130.6 L58038212413.7 L58559626927.17L58559626927.18L58559626927.22L58559627052.20L58565236830.2 L58643601785.6 L59135868495.7 L59136380947.4 L59308857809.9 L59315137787.11L59315137787.6 L59315137787.9 L59514603121.3 L59551301595.5 L59588422338.2 L59651323709.3 L59727773228.2 L60070416074.5 L6025098890.3  L6028618793.12 L6028750508.14 L60542002201.21L60785358792.0 L60837792237.3 L6110676881.3  L61519252226.3 L61975288227.18L61977241369.31L62441692029.4 L62947420491.3 L63181313848.2 L6336436530.6  L63380764809.6 L64327673430.7 L64612082378.0 L65364830649.3 L65522324618.4 L65621996669.17L65621996669.18L65621996669.22L65621997054.20L65627227280.4 L6646336923.2  L66469708956.3 L66583644397.2 L66750448085.22L67559118284.3 L7603473955.2  L8118647786.0  00000500S01101:01L01T01Y01o02>02N03A03h04O05J05i06I07<07E07S08508O08k09609:09Q09Y09a0:E0:Y0:`0;J0;Q0;V0;W0<10<L0<Q0<\0<g0<h0<m0>80>O0?20?N0@10@80@A0@P0@f0AI0A`0B=0BZ0C70C@0CD0Ca0Cn0D50DE0DL0DT0EA0EG0EL0ES0E^0F20F70FF0FJ0G10GY0HH0HP0H^0Hj0I60IB0IG0IP0I\0In0Io0J30J;0J@0JA0J^0KF0Ki0LL0MC0Mb0Mg0NY0O00OO0Oj0PH0Q00R;0RR0Rh0S;0S@0S[0S\0TA0Tl0UM0U]0Ua0Um0VH0VM0W;0WQ0WW0Wf0X50X60X;0XF0Xo0Y@0YX0Y^0Y_0Y`0Ya0Yb0Yc0Z>0ZC0ZK0ZP0Zk0[10[P0\50\60\70\J0\Q0\T0\`0]H0]e0]n0^X0^]0^e0^m0_80_O0_l0`L0aW0an0ao0bO0bX0c80cc0d@0dN0dU0e`0f70f@0fE0fJ0fj0fk0gD0gI0gO0gW0g[0h10h@0hA0hk0i00i@0iO0iX0j30jO0jX0jb0jg0jh0ka0l;0l\0mB0mk0nU0o20o80oJ0oV10T10k11H11W11o12J12k13M14314814K14V14^15:15]15m16H16Q16a16i16n17517=17F18118d19K19L19U19Z19b1:91:V1:d1:i1;11;=1;H1;`1;a1;k1<31<N1<o1=Q1>71>E1>L1>Q1>V1?81?=1?B1?CS1h1cS1h2SP1C2lo3CB03CHI3LOL3SPL2Y2S1h2SP1C2lo3CB03CHI3LOL3SPL2Y1S1h5Zctx4S3hAR1h2T03ACB3B6cS1h4Zdt3S1h1cS3hAR1h2SP2lo3LOL4STK0S1h5Zctx15Zctx2S1h4Zpa12S44Zpa2S1h1c3C301r3mfa3NF02k'3RL'3RH'1A2n'2HA3HB'5AUMU'2Q5S1h1c3C303B6a3B6e1r3mfa3SFB3NF01A2n'2H3S3hAR1h1c3C303B6a3B6c1r3mfa3NF01A2n'2H2S3hAR1h1c3C302T03B6a3B6e3ZTH1r3mfa3SFB3NF01A2n'2H12H22H32H4S3hAR1h1c3C301r3mfa3SFB1A2n'2H5S1h1c1r3mfa3NF44ROOM3MCR1A2n'2H6S3hAR1h1c3HRI1r2mu2au3mfa3NF44ROOM3MCR4FARI1A2n'2H1S1h1c3C30S1c3MCR2Dm3Dm'S3hAR1h1c3RI11r2mu2au3URI2D12D22D3S3hAR1h3RI12c'2Q12D12D22D3S3hAR2k'2F32F64NFX'2D12D22D3S1h4Zpa42S4S2k'S1h3B6a3B6e3ZTH3ZTC3ZCHS1h4Zfs1S1h4Zfs2S1h1c1a2kb2Xb2c'3RL'3RH'5AUMU'2Q12Q5S1h1c3C302c13Hc13NE1S2k'2F3S1h1c3C301r2mu2au4AUMU5MULIM3mfa4FARI1b2S2S2k'2C'S1h1cSS1h1c1r3mfa2k'3RL'1A2HA2Q2S1h1c1r2mu2au3mfa4B6RB1b2S1S1h1cS1h1c1r3mfaS1h1c1r3mfaSS1c1pS3hAR1h1c3C303HRI3ZTH1r2mu2au4AUMU3mfa3MCR3SFB4B6RB4FARI3RIH1A2n'2H12H23ACBS1h1c1r3mfa3MCR1A2n'2H3S1h1c3C301r2mu2au3mfa3NF44ROOM4FARIS1h1c3C301r2mu2au2c'4MFB'2Q3S1h1c1r2mu2au3mfa3NF44ROOM4FARI3RIHS1c3CSRS1c1p3MCRS1h1c1r3mfa3SFBS2k'3RZ'2F53XAB3UIN2D1S1h1c3C303SB02k02S12D12c'3Hc'5AUMU'S1h3SB02c'3Hc'2k02S12D1S1h1c3C303SB01r2mu2au4AUMU2D1S1h2k'3EL'3EH'1A2n'2HA3HB'2Y2S1h2k'3EL'3EH'1A2n'2HA3HB'2Y1S1h5Zctx3S2kbS1h1c1r3mfa2kb1X2F12F22F33NFbS1h4Zdt14Zdt2S2c'2C'S1c1r2mu2au4AUMUS1c3CSRS1c1p2D1S3hAR1h1c3C303SB03HRI3RI11r3mfa3MFB4ROOM1H2H0S1h2T0S1h1cS2k'2C'S2k'2F43UINS1h1c1r3mfa4CARB3MFXS1h1cS1c1r2mu2au3CSRS2k'S1h1c1r3mfa3MFB4ROOM4B6RB4FARI3RIH1a2HaS1h1c3C301r2mu2au4AUMU3URI4B6RB3RIH1a2HaS1h1c1r3mfa3NF44ROOM3MCR3NF04B6RB4FARI3RIH1a2HaS1h1a2HaS1h1c3C301a2HaS1h2sh2SZ2Y2S1h2sh2SZ2Y1S1h1c2c13Hc1S1h1cS1h5Zctx4S1h2sh2SZ2Y3S1c1p3MCR2dn2D12D2SS2kbS1c1p2dnS1h1cSS1h2k'3EL'3EH'1A2n'2HA3HB'2Y3S1h1c3C301r3mfa2k'3RH'1A2n'3HB'5AUMU'2Q1S1h1c3C303B6a3B6e1r3mfa3SFB1A2n'2H3S3hAR1h1c3C303B6a3B6c1r3mfa1A2n'2H2S3hAR1h1c3C302T03B6a3B6e3ZTH1r3mfa3SFB1A2n'2H12H22H32H4S3hAR1h1c3C301r3mfa3SFB1A2n'2H4S1h1cS3hAR1h1c3SB03HRI1r2mu2au3mfa3SFB4B6RB3RIH1A2n'2H1S1h1c1r3mfa3MCR1A2n'2H8S3hAR1h1c3B6c1r3mfa3SFB1A2n'2H1S1h1c3C301r3mfa3SFB1A2n'2H4S3hAR1h1c3C302T01r3mfa1A2n'2H4S3hAR1h1c3C302T01r3mfa3SFB1A2n'2H12H22H4S3hAR1h1c3C303HRI3ZTH1r2mu2au4AUMU3mfa3MCR3SFB4B6RB4FARI3RIH1A2n'2H12H23ACBS1h1c1r3mfa3MCR1A2n'2H2S1h1c1r2mu2au3mfa4B6RBS1h1c1r2mu2au2c'2Q2S1h1cS2k'3EL'3EH'1A2n'2HA3HB'2Y4SS3hAR1h3RI12c'5AUMU'2Q12k02S24CSR'2D1S3hAR1h1c3RI11r2mu2au4AUMU3CSR3URI2k02S22D1S1h1c1r3mfa2k'2F12F22F34NFX'4APf0S2k'3RZ'3XAB3UINS2k'S1h1c2c13Hc1S1h1c1r2mu2au3mfa2c'3Hc'2Q4S1h1cS1h1c1r3mfa3MFB4ROOM2c'5AUMU'2Q52k02S12S24CSR'S1c1r2mu2au4AUMU5MULIMS1h2T0S1c1p5CNT163MCRS1h1c1r3mfa3SFBSS1h1cS1h4Zpa32S4S1h1c3C301r2mu2au4AUMU3NF02c'3Hc'4MFB'2Q8S1h1c1r2mu2au3mfaS1h4Zfs42kk2ii2I12I23SZ1S1h2S3SSSSSS1h1c1r2mu2au5MULIM3mfa3MFBS1h1cS1h4Zfs4S1h1cS1h1c1r2mu2au2c'4MFB'2Q32Q4S1b2Y4S1c1r3mfa1f3nf'3js'4JSL42dn3HNFS1h1c1r2mu2au4AUMU5MULIM3mfa3NF01b2S2SSS3hAR1h2lo3LOL4STK0S1c3C30S1cS1c1p2dn3DNBS1h1c3C301r2mu2au4AUMU3mfa3MCR2c'3Hc'2NES1h4Zfs12kk2ii2I12I23SZ14Zfs2S1h5Zctx3S1h1c1r2mu2au4AUMU5MULIM3mfa4FARI3RIH1b2S2S1h1cS1h1b2Y2S1h1b2Y1S1c1r2mu2auS1h1c1r3mfa3MCR1A2n'2H5S3hAR1h1c1r2mu2au3mfa1A2n'2H1S3hAR1h2SP1C2lo3CB03LOL3SPL4STK0S3hAR1h1c3C303HRI3ZTH1r2mu2au4AUMU3mfa3MCR3SFB4B6RB4FARI3RIH1A2n'2H12H23ACBS1h1c1r3mfa3MCR1A2n'2H2SS1h2b01c1r2mu2au4AUMU5MULIM4KSL2S1h1c3C30S1h1c1r3mfa3NF44ROOM3MCR1A2n'2H6S3hAR1h1c3HRI1r2mu2au3mfa4ROOM4FARI1A2n'2H1S1h1c1r2mu2au3mfa4FARI2c'3Hc'S1c3MCR2Dm3Dm'S1c3C30S3hAR1h1c3C303HRI3ZTH1r2mu2au4AUMU3mfa3MCR3SFB4B6RB4FARI3RIH1A2n'2H12H23ACBS1h1c1r3mfa3MCR1A2n'2H3S1c1p3MCRS1h1cS1h1cS1h1c1r3mfa3MFB4ROOM2c'5AUMU'2Q5SS1c1p4PMAX3MCR2dn2D12D21HS1c1pS1h2T0S2c'3Hc'S2kbS3hAR1h2lo3LOL2T14STK0S1h1c1r3mfa3SFBSS1h1c1r2mu2au4AUMU5MULIM3mfa3MFB3CSR2k02S2S1h1cS1c1r2mu2au4AUMUS1c1p2dn2D13HdnS1c2c'2NES3hAR1h2SP1C3CB03CHI1c4STKHS2c02kb2Ra2D12D22D32D42D52NFS1A2n'2H4S2SP1C3CB0S1h1cSS3hAR1h2SP2lo3LOL1c3HRI3RI14STK01r2mu2au3mfa4FARI1A2n'2H2S1h2SP2lo3LOL4SPHI1A2n'2H3S1h2SP2lo1c3C301r3mfa3SFB1A2n'2H1S3hAR1h2SP2lo3LOL1c4STK01r3mfa1A2n'2H2S3hAR1h2SP2lo3LOL1c2T14STK01r3mfa1A2n'2H2S3hAR1h2SP2lo3LOL1c3B6d4STK01r3mfa1A2n'2H2S1h2SP2lo1c1r3mfa3MCR1A2n'2H1S1x2HxS1c1p3MCR2dn2D12D2S1c1p3MCR2D1S1h1c1r3mfa3MFB4ROOM4B6RB4FARI3RIH3Dhe4Dhe'3Db64Db6'4Dfaa1a2HaS1h1c1r3mfa3MCR1A2n'2H5S3hAR1h1c1r2mu2au3mfa1A2n'2H1S1h5Zctx15Zctx2S1h4Zfs32kk2ii2I12I23SZ1S1h1c3C301r3mfa3SFB1A2n'2H2S3hAR1h1c3C302T01r3mfa1A2n'2H12H2S3hAR1h1c3C302T01r3mfa3SFB1A2n'2H4S3hAR1h1c3C303ZTH1r3mfa3SFB1A2n'2H12H2S1h1cS1h2SP1C2lo3CB03CHIS1c1p2dn2D2S1c1p2dnS1h1a2kb2Ha2Xb2sh3EL'3EH'2Y2S1h1c1r3mfa3NF44ROOM3MCR3NF01a2Ha1XS1h1c3C301a2Ha1XS1h1c1r3mfa3MFB4ROOM1a2Ha1XS1c2dn2D2S1h2SP1C3CB03CHIS1h4Zfs3S1h1cS1h3FS0S1h4Zdt4S1h1c3C30S1h1c1r3mfa3MFB4ROOM2kb2c'3RL'3RH'5AUMU'2Q5S1h1c1r3mfa3MFB4ROOM4B6RB4FARI3RIH2kb2sh3EL'3EH'2Y2S1h1c1r3mfa2k'3RH'1A2n'3HB'5AUMU'2Q12Q4SS1h1c3C30S1c1pS1h1b2Y3S1h1c1r3mfa3MCR1A2n'2H5S3hAR1h1c1r2mu2au3mfa1A2n'2H2S1c3MCR2Dm3Dm'S1c1rS2k'3RZ'S1h1c2c13Hc1S1c1r2mu2auS1h1c1r3mfa3NF44CARB3MFXSS2sh2SZ2Y4S1c1r2dnS1h1c3C301r3mfa3SFB1A2n'2H2S3hAR1h1c3C302T01r3mfa1A2n'2H12H2S3hAR1h1c3C302T01r3mfa3SFB1A2n'2H3S3hAR1h1c3C303ZTH1r3mfa3SFB1A2n'2H12H2S1c3MCR2Dm3Dm'S1c3C30S1h1cS1h1jS1h1c1r2mu2au3mfa4B6RB4FARI2c'3Hc'S1h1cS1h1cS". (* [comment removed for export] *)
  #[using="IMG ALWF ASB"] Theorem rec_batch_step : ltac2:(CDefT.buildp (gd_tbl_AW_RecStepBatch ()) "PQ,P,$20.SpPra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ph,$0.PLF,(?.(8.$1.$1.))PQS,(?.(8.$1.$1.))Pbc,$2.Pi,$3.Pb0,$10.Ptb,(?.$10.)PSP,$1.PC,$1.Plo,$1.PF,(39.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(5.(4.&8.))Pmo,$22.ZL,$;.(<.R>.)ZT,$1.(3:.R1.)P,(2<.VhAR,R10.)P,(18.(3;.R11.)$3<.)P,(:.$23.(3=.R12.)$3>.)P,(:.(?.$10.)(11.(12.R13.))(1<.$10.R>.R=.))P,(:.(?.$1.)(3?.R?.)(1?.$1.))P,(2=.VhAR,R15.R14.R9.)P,(6.VhAR,R16.R>.(7.(8.$2.$3.)(9.$2.$3.R13.R12.))R:.)P,(18.R10.R?.)P,(18.(19.R10.+20.)(40.R:.))P,(38.$16.R=.R10.R12.)P,(18.(41.R<.)R11.)P,(18.R12.(42.R14.+2<0.))P,(:.$1.(43.R15.+10.)=)P,(37.$16.R11.)P,(:.(4.&40.)R36.(29.&40.$44.))P,(2>.VhAR,VAL,VFF,R1?.R12.)P,(2?.R14.R13.)P,Pc',$20.P,(45.R3<.R1;.R3;.R3:.R36.R35.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R18.R17.R22.R21.R1:.R19.R20.R16.R1.)(46.$16.R3>.R2.)(46.$16.R3=.(26.(27.(28.R3<.(29.&40.R1;.)R3;.R3:.R39.R38.R37.R36.R35.(29.&40.(19.R13.+=0.))(29.&40.$47.)(29.&40.+18.)(29.&40.(48.R1=.))R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R18.(29.&40.$49.)R17.(14.(4.&40.))R16.(2;.$16.))R15.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 h LF QS bc i b0 tb SP C lo F fc m mo L T
      WF HV CI HB HE HMQ RQ CB0 CHI ST LOL SPL SPA MI TP HK HJ HC.
    subst T L.
    dpose WF as (WL' & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG). dpose WL' as (WL & WL24 & WLD).
    pose proof (WFK_of_WFR h WF HV) as W0.
    dpose WK as (WKF & NDK & WKSEC).
    set (c := kBatchClass) in *. assert (C24 : c = 24) by reflexivity.
    assert (GC31 : 1 <= c <= 31) by (rewrite C24; clear; lia). assert (C30 : 1 <= c <= 30) by (rewrite C24; clear; lia).
    ddestruct (L_GSB (h_L h) WL) as (SB0 & SBAL & HRI & RI1). ddestruct (L_GT (h_L h) WL) as (T0 & T1 & TAL). ddestruct (L_GCTX (h_L h) WL) as (CX0 & CX1 & CXL).
    dpose WL as (_ & B6a & B6b & _ & B6c & B6d & B6e & _ & _ & _ & _ & _ & STK1 & _ & _ & _ & STK0 & STKH & _).
    pose proof (ff_geom AL FF h mo W0 HK) as GEO.
    pose proof (z_T_hull h GEO) as ZTH. pose proof (z_T_ctx h GEO) as ZTC. pose proof (z_ctx_hull h GEO) as ZCH.
    unfold zapart in ZTH, ZTC, ZCH. cbn [fst snd] in ZTH, ZTC, ZCH. rewrite CXL in ZTC, ZCH.
    assert (GSEP : (l_T (h_L h) + 4096 <= l_sb (h_L h) \/ l_sb (h_L h) + 2^37 + 4096 <= l_T (h_L h)) /\ (l_ctx (h_L h) + 0x10000 <= l_T (h_L h) \/ l_T (h_L h) + 4096 <= l_ctx (h_L h))
                   /\ (l_ctx (h_L h) + 0x10000 <= l_sb (h_L h) \/ l_sb (h_L h) + 2^37 + 4096 <= l_ctx (h_L h))).
    { unfold ri_base, space_end, kSpaceSize in *. clear - ZTH ZTC ZCH B6a B6e. repeat split; lia. }
    pose proof (WR c ltac:(unfold kNumClasses; clear -C30; lia)) as WRc. cbn zeta in WRc.
    ddestruct WRc as (_ & AUMU & AUCS & MUAL & MULIM & MUAU & MFAL & MFB & NF4 & FAOK & NDO & PART).
    set (r := h_reg h c) in *. set (mfa := r_mapped_fa r) in *. set (mu := r_mapped_user r) in *. set (au := r_alloc_user r) in *.
    pose proof (class_size_range c GC31) as CSR.
    assert (CARB : carved h c <= 117440512).
    { unfold carved. fold r au. unfold kUserLimit in MULIM.
      apply Z.le_trans with (m := au / 32); [apply Z.div_le_compat_l; clear -AUMU CSR; lia|].
      change 117440512 with (3758096384 / 32). apply Z.div_le_mono; clear -AUMU MULIM; lia. }
    dpose WX as (WX1 & WX2 & WX3). pose proof (WX1 c ltac:(unfold kNumClasses; clear -C30; lia)) as MFX. fold r mfa in MFX.
    assert (ROOM : mfa + kFreeArrayMapSize <= kFreeArraySize) by (unfold kFreeArrayMapSize, kFreeArraySize in *; clear - MFX CARB; lia).
    assert (NFB : r_nfreed r + 16 < 2^27) by (unfold kFreeArrayMapSize in *; clear - MFX CARB NF4; fold mfa in NF4; lia).
    (* [comment removed for export] *)
    pose proof (WC c ltac:(unfold kNumClasses; clear -C30; lia)) as WCc. cbn zeta in WCc. rewrite CI in WCc. ddestruct WCc as (PMC & _ & CNT16 & CNTM & CKOK).
    set (p := h_cache h c) in *. destruct (PMC ltac:(clear -C30; lia)) as [PMAX PCSZ].
    pose proof (max_count_range c GC31) as MCR.
    (* [comment removed for export] *)
    dpose WQ as (WT & WGQ & NDA & UQ). rewrite HB in WT. ddestruct WT as [(BC1 & BC2 & (j & Hj & EAB)) WTB]. change kBatchClass with c in Hj, EAB.
    assert (HB0 : In b0 (q_batches (h_tq h) ++ q_batches (h_gq h))) by (rewrite HB; left; reflexivity).
    destruct (slot_le h c j WR GC31 Hj) as [KSL1 KSL2]. rewrite <- EAB in KSL1, KSL2. fold r in KSL2. fold au in KSL2. unfold region_beg, kRegionSize in KSL1, KSL2.
    change (class_size c) with 8192 in KSL2.
    assert (AB16 : (b_addr b0 - (l_sb (h_L h) + c * 2^32)) mod 16 = 0).
    { rewrite EAB. unfold chunk_at, region_beg, kRegionSize. rewrite C24. change (class_size 24) with 8192.
      replace (l_sb (h_L h) + 24 * 2 ^ 32 + j * 8192 - (l_sb (h_L h) + 24 * 2 ^ 32)) with ((j * 512) * 16) by (clear; lia). apply Z_mod_mult. }
    (* [comment removed for export] *)
    ddestruct HMQ as (G0 & G1 & G2 & G3 & G4 & G5 & G7 & G8 & G9 & GE). pose proof G2 as THR.
    ddestruct G2 as (UNW & (ds & PCLS) & (j0 & j1 & J27) & TSTS).
    dpose (PCLS c ltac:(clear -C30; lia)) as (PCL & CKS & LCK & FST & PMC'). fold p in PCL, CKS, FST.
    rewrite PMAX, PCSZ in PCL.
    pose proof (G5 c ltac:(clear -C30; lia)) as RG. unfold hm_region in RG. cbn zeta in RG. fold r in RG.
    ddestruct RG as (RMX & RNF & RMFA & RAU & R40 & RMU & R56 & R68 & (stw & R72) & (s80 & s88 & RST) & RFA & (js & RJS & JSL) & WRU & SHT & SHF1).
    set (exb := Z_to_bv 8 (if a_exh (h_acct h) c then 1 else 0)) in *.   (* [comment removed for export] *)
    destruct G1 as [RO RW]. ddestruct (hm_ro_free (h_L h) m RO) as ([RLS _] & (can & dd & madv & RSM) & LST).
    dpose G0 as (_ & WHS & _ & WT4 & _).
    (* [comment removed for export] *)
    destruct (wr_at_off_C8 m (l_T (h_L h) + 2784) ltac:(eapply wr_at_sub; [exact WT4| clear; lia| clear; lia| clear; lia]) ltac:(clear -T0; lia)) as [stj STJ].
    ddestruct (wr_at_off_C8C8 m (l_T (h_L h) + 2872) ltac:(eapply wr_at_sub; [exact WT4| clear; lia| clear; lia| clear; lia]) ltac:(clear -T0; lia)) as (tj1 & tj2 & TJ).
    (* [comment removed for export] *)
    assert (SFB : 0x2008fff7000 <= 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 /\ 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 + 32768 <= 0x10007fff0000).
    { pose proof (Z.div_mod (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) 8 ltac:(clear; lia)).
      unfold kFreeArrayMapSize, kFreeArraySize in *. pose proof aceil_bounds as ACB.
      clear - H H0 SB0 HRI RI1 C30 ROOM MFB ACB. lia. }
    destruct (wr_at_high_CB m (0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8) 32768
                ltac:(replace (0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8) with (0x2008fff7000 + (0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 - 0x2008fff7000)) by (clear; lia);
                      eapply wr_at_sub; [exact WHS| clear -SFB; lia| clear; lia| clear -SFB; lia])
                ltac:(clear -SFB; lia) ltac:(clear; lia)) as [shF SHF].
    change (Z.to_nat 32768) with (Z.to_nat 32768) in SHF.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 24) with (Z_to_bv 64 c) by (rewrite C24; reflexivity).
    eapply (lc_dealloc_cfgS AL IMG ALWF (CSp AL FF h c) (fam_CSOK AL FF h c) (fam_mono AL FF h c) ASB (l_T (h_L h)) (l_ctx (h_L h)) (l_sb (h_L h)) (ri_base (h_L h)) c
              (conj SB0 (conj SBAL (conj HRI RI1))) C30 (conj T0 (conj T1 TAL)) (conj CX0 CX1) GSEP
              (fam_T AL FF h c W0 GC31 ROOM) ltac:(intros u f; rewrite <- CXL; exact (fam_ctx AL FF h c W0 GC31 ROOM u f)) (fam_ri AL FF h c W0 GC31 ROOM)
              (Kp AL FF h c) (fam_KL AL FF h c) mfa
              (fam_ledger AL FF h c W0 GC31 ROOM) (fam_commit AL FF h c W0 GC31 ROOM) (fam_fresh AL FF h c W0 GC31 ROOM)
              (fam_GMFA h c W0 GC31 ROOM) (fam_faz AL FF h c W0 GC31 ROOM) (fam_room AL FF h c W0 GC31 ROOM) (fam_scar AL FF h c W0 GC31 ROOM) (fam_fa AL FF h c W0 GC31 ROOM) Q)
      with (AB := b_addr b0) (count := pc_count p) (csz := class_size c) (nf := r_nfreed r) (lo := lo)
           (cks := ds c) (js := js) (shF := shF) (st80 := s80) (st88 := s88) (stj := stj) (j1 := tj1) (j2 := tj2).
    all: lazymatch goal with
         | |- aevtS _ _ _ => idtac
         | |- forall c', _ -> aevtS _ _ _ => idtac
         | |- _ <= b_addr _ => exact KSL1
         | |- b_addr _ < _ => unfold kUserLimit in MULIM; clear - KSL2 AUMU MULIM; lia
         | |- (b_addr _ - _) mod 16 = 0 => exact AB16
         | |- 0 <= pc_count _ <= _ => unfold pc_count in *; rewrite PMAX in CNT16; clear -CNT16 MCR; lia
         | |- 0 <= class_size _ < _ => clear -CSR; lia
         | |- 0 <= r_nfreed _ => unfold r_nfreed; clear; lia
         | |- ACEIL <= _ => clear -STK0 LOL; lia
         | |- _ <= _ \/ _ + 4096 <= _ => right; clear -T1 STK0 LOL; lia
         | |- crange _ _ (_ - _) => apply (fam_stack AL FF h c W0 GC31 ROOM); [exact LOL| clear -CB0 CHI; lia]
         | |- _ => first [ sassumption | cassumption (* [comment removed for export] *) | exact PCL | exact CKS | exact LCK | exact STJ | exact TJ | exact NFB | exact JSL | exact RMX | exact RNF | exact RMFA | exact RST
                        | exact RJS | exact SHF | exact RLS | exact ST | exact SPL | exact SPA | exact MI | exact TP | exact HK | exact HJ
                        | clear - SB0 HRI RI1 C30 T0 T1 CX0 CX1 STK0 STKH LOL SPL CB0 CHI; lia
                        | match goal with |- ?G => idtac "RB-LEFTOVER" G end ]
         end.
    (* [comment removed for export] *)
    intros c4 P4. unfold rl_post in P4.
    ddestruct P4 as (ms4 & mo4 & f & count' & nf' & cks' & js' & stj' & j1' & j2' & st80' & y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m4
                    & -> & -> & HK4 & HJ4 & HF2 & MU & WM & MI4 & ST4 & RLS4 & PCL4 & CKS4 & LCK4 & STJ4 & TJ4 & RMX4 & RNF4 & RMFA4 & RST4 & FAJ4 & JSL4
                    & SHN & SHO & ZLT & (dr & dn & DRC & HC4 & HNF & HCKS & DRT & DRF & LJS)).
    assert (DR : if dr then pc_count p = max_count c /\ dn = Z.to_nat (max_count c / 2) else pc_count p < max_count c).
    { destruct dr; [destruct DRC as [D1 D2]; split; [exact D1| clear -D2; lia]| destruct DRC as (D1 & _); exact D1]. }
    assert (UFZ : unit_if f = funit f) by (destruct f as [[|]|]; reflexivity).
    assert (NF4' : dr = true -> 4 * (r_nfreed r + Z.of_nat dn) <= r_mapped_fa r + funit f).
    { intros ->. rewrite <- UFZ. fold mfa. clear - JSL4 HNF. lia. }
    assert (FX : f = Some true -> dr = true /\ r_mapped_fa r < 4 * (r_nfreed r + Z.of_nat dn)).
    { intros Ef. destruct dr; [| ddestruct DRC as (_ & D2 & _); rewrite Ef in D2; discriminate D2]. destruct DRC as [D1 D2].
      split; [reflexivity|]. fold mfa. rewrite D2. exact (ZLT Ef). }
    set (h' := h_recb h dr dn f).
    pose proof (WFR_recb h dr dn f b0 tb WF CI HB HE DR HF2 NF4' FX) as WF'.
    (* [comment removed for export] *)
    assert (NF0 : 0 <= r_nfreed r) by (unfold r_nfreed; clear; lia).
    set (W := [(lo, SP); (l_T (h_L h) + 208 + 80 * c, l_T (h_L h) + 208 + 80 * c + 4); (l_T (h_L h) + 208 + 80 * c + 16, l_T (h_L h) + 208 + 80 * c + 80);
               (l_T (h_L h) + 2784, l_T (h_L h) + 2792); (l_T (h_L h) + 2872, l_T (h_L h) + 2888);
               (ri_base (h_L h) + 128 * c, ri_base (h_L h) + 128 * c + 8); (ri_base (h_L h) + 128 * c + 16, ri_base (h_L h) + 128 * c + 32);
               (ri_base (h_L h) + 128 * c + 80, ri_base (h_L h) + 128 * c + 88);
               (l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + 4 * r_nfreed r, l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + 4 * r_nfreed r + 4 * (max_count c / 2));
               (l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + mfa, l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + mfa + 2 ^ 18);
               (2147450880 + (l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + mfa) / 8, 2147450880 + (l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + mfa) / 8 + 32768)]) in MU.
    assert (DJz : forall A n', (A + n' <= lo \/ SP <= A) ->
                  (A + n' <= l_T (h_L h) + 208 + 80 * c \/ l_T (h_L h) + 208 + 80 * c + 80 <= A) -> (A + n' <= l_T (h_L h) + 2784 \/ l_T (h_L h) + 2904 <= A) ->
                  (A + n' <= ri_base (h_L h) + 128 * c \/ ri_base (h_L h) + 128 * c + 88 <= A) ->
                  (A + n' <= l_sb (h_L h) + c * 2^32 + 3758096384 + 4 * r_nfreed r \/ l_sb (h_L h) + c * 2^32 + 3758096384 + 2^29 <= A) ->
                  (A + n' <= 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 \/ 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 + 32768 <= A) ->
                  disjoint_from W A n').
    { intros A n' H1 H2 H3 H5 H6 H8. subst W. cbn [disjoint_from]. fold mfa in NF4, ROOM. unfold kFreeArrayMapSize, kFreeArraySize in ROOM.
      clear - H1 H2 H3 H5 H6 H8 NF4 ROOM NFB MCR. repeat split; lia. }
    assert (DJfar : forall A n', (A + n' <= lo \/ SP <= A) -> (A + n' <= l_T (h_L h) \/ l_T (h_L h) + 4096 <= A) ->
                  (A + n' <= l_b6 (h_L h) \/ l_b6 (h_L h) + 0x2000011000 <= A) -> (A + n' <= 0x7fff7000 \/ 0x10007fff8000 <= A) -> disjoint_from W A n').
    { intros A n' H1 H2 H3 H4. apply DJz; unfold ri_base, space_end, kSpaceSize in *; clear - H1 H2 H3 H4 B6a B6e C30 SFB NF0; lia. }
    assert (DJT : forall A n', l_T (h_L h) <= A -> A + n' <= l_T (h_L h) + 4096 ->
                  (A + n' <= l_T (h_L h) + 208 + 80 * c \/ l_T (h_L h) + 208 + 80 * c + 80 <= A) -> (A + n' <= l_T (h_L h) + 2784 \/ l_T (h_L h) + 2904 <= A) ->
                  disjoint_from W A n').
    { intros A n' H1 H2 H3 H4. apply DJz; unfold ri_base, space_end, kSpaceSize in *; clear - H1 H2 H3 H4 ZTH B6a B6e C30 SFB T0 T1 STK0 LOL NF0; lia. }
    assert (DJhull : forall A n', l_b6 (h_L h) <= A -> A + n' <= l_b6 (h_L h) + 0x2000011000 ->
                  (A + n' <= ri_base (h_L h) + 128 * c \/ ri_base (h_L h) + 128 * c + 88 <= A) ->
                  (A + n' <= l_sb (h_L h) + c * 2^32 + 3758096384 + 4 * r_nfreed r \/ l_sb (h_L h) + c * 2^32 + 3758096384 + 2^29 <= A) ->
                  disjoint_from W A n').
    { intros A n' H1 H2 H4 H5. apply DJz; unfold ri_base, space_end, kSpaceSize, kHighMemBeg in *; clear - H1 H2 H4 H5 ZTH B6c B6d SFB STK0 LOL NF0 C30; lia. }
    assert (DJband : forall A n', 0x7fff7000 <= A -> A + n' <= 0x10007fff8000 ->
                  (A + n' <= 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 \/ 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 + 32768 <= A) ->
                  disjoint_from W A n').
    { intros A n' H1 H2 H4. apply DJz; unfold ri_base, space_end, kSpaceSize, kHighMemBeg in *; clear - H1 H2 H4 B6a B6c T0 STK0 LOL NF0 C30; lia. }
    assert (KOM : forall A n', disjoint_from W A n' -> kept m m4 A n') by (intros A n' D; exact (kept_of_munch W m m4 A n' MU D)).
    assert (IMGK : forall x : word, 0x10000 <= bv_unsigned x < 0x65f000 -> m4 x = m x).
    { intros x Hx. apply (KOM 0x10000 (0x65f000 - 0x10000)); [| clear -Hx; lia]. pose proof aceil_bounds as ACB.
      apply DJfar; unfold kHighMemBeg in *; clear - STK0 LOL T0 B6c ACB; lia. }
    assert (IAG : forall RS, ranges_within_b RS 0x10000 0x65f000 = true -> iagree RS m m4).
    { intros RS HRS x Hx. apply IMGK. exact (ranges_within_b_sound RS 0x10000 0x65f000 _ HRS Hx). }
    (* [comment removed for export] *)
    pose proof (z_T_ctx h GEO) as Zctx1. pose proof (z_ctx_hull h GEO) as Zctx2. pose proof (z_ctx_stk h GEO) as Zctx3. pose proof (z_ctx_band h GEO) as Zctx4.
    pose proof (z_T_dtls h GEO) as Zdt1. pose proof (z_hull_dtls h GEO) as Zdt2. pose proof (z_stk_dtls h GEO) as Zdt3. pose proof (z_band_dtls h GEO) as Zdt4.
    pose proof (z_T_fs h GEO) as Zfs1. pose proof (z_fs_hull h GEO) as Zfs2. pose proof (z_fs_stk h GEO) as Zfs3. pose proof (z_fs_band h GEO) as Zfs4.
    pose proof (z_T_pa h GEO) as Zpa1. pose proof (z_pa_hull h GEO) as Zpa2. pose proof (z_pa_stk h GEO) as Zpa3. pose proof (z_pa_band h GEO) as Zpa4.
    unfold zapart in Zctx1, Zctx2, Zctx3, Zctx4, Zdt1, Zdt2, Zdt3, Zdt4, Zfs1, Zfs2, Zfs3, Zfs4, Zpa1, Zpa2, Zpa3, Zpa4.
    cbn [fst snd] in Zctx1, Zctx2, Zctx3, Zctx4, Zdt1, Zdt2, Zdt3, Zdt4, Zfs1, Zfs2, Zfs3, Zfs4, Zpa1, Zpa2, Zpa3, Zpa4.
    assert (SPHI : SP <= l_stk_hi (h_L h)) by (clear -CB0 CHI; lia).
    assert (DJzone : forall A n', 0 <= n' ->
              (A + n' <= l_T (h_L h) \/ l_T (h_L h) + 4096 <= A) -> (A + n' <= l_b6 (h_L h) \/ l_b6 (h_L h) + 0x2000011000 <= A) ->
              (A + n' <= l_stk_lo (h_L h) \/ l_stk_lo (h_L h) + (l_stk_hi (h_L h) - l_stk_lo (h_L h)) <= A) ->
              (A + n' <= 0x7fff7000 \/ 0x7fff7000 + (0x10007fff8000 - 0x7fff7000) <= A) -> disjoint_from W A n').
    { intros A n' N0' H1 H2 H3 H4. apply DJfar; [clear -H3 LOL SPHI SPL N0'; lia| exact H1| exact H2| clear -H4; lia]. }
    (* [comment removed for export] *)
    assert (G0' : hm_maps (h_L h) m4) by (exact (hm_maps_frame _ _ _ G0 WM)).
    assert (G1' : hm_statics (h_L h) m4).
    { apply (hm_statics_frame m m4 WM (h_L h) (conj RO RW)); [apply IAG; vm_compute; reflexivity| apply IAG; vm_compute; reflexivity| | | |]; apply KOM.
      - apply DJT; clear -C30; lia.
      - apply DJzone; [clear; lia| | | |]; rewrite ?CXL in *; clear -Zctx1 Zctx2 Zctx3 Zctx4 CXL; lia.
      - apply DJzone; [clear; lia| | | |]; rewrite ?CXL in *; clear -Zctx1 Zctx2 Zctx3 Zctx4 CXL; lia.
      - apply DJzone; [clear; lia| | | |]; clear -Zdt1 Zdt2 Zdt3 Zdt4; lia. }
    (* [comment removed for export] *)
    assert (PCL' : hm_pclass m4 (l_T (h_L h)) (h_cinit h) c (pc_push (if dr then pc_dropn p dn else p) (compact (h_L h) c (b_addr b0))) cks').
    { rewrite CI. unfold hm_pclass.
      assert (LENP : length (pc_chunks (if dr then pc_dropn p dn else p)) = Z.to_nat (pc_count p - Z.of_nat dn)).
      { unfold pc_count. destruct dr; cbn [pc_chunks pc_dropn];
          [destruct DR as [D1 D2]; unfold pc_count in D1; rewrite firstn_length_le by (clear -D1 D2 MCR; lia); clear -D1 D2 MCR; lia| ddestruct DRC as (_ & _ & ->); clear; lia]. }
      assert (CNTP : pc_count (pc_push (if dr then pc_dropn p dn else p) (compact (h_L h) c (b_addr b0))) = count').
      { unfold pc_count. cbn [pc_chunks pc_push]. rewrite length_app, LENP. cbn [length]. rewrite HC4. unfold pc_count in *.
        destruct dr; [destruct DR as [D1 D2]| ddestruct DRC as (_ & _ & ->); clear; lia].
        clear -D1 D2 CNT16 PMAX MCR.
        assert (Z.of_nat dn <= max_count c) by (subst dn; rewrite Z2Nat.id; [apply Z.div_le_upper_bound| apply Z.div_pos]; lia). lia. }
      split. { rewrite CNTP. replace (pc_max (pc_push (if dr then pc_dropn p dn else p) (compact (h_L h) c (b_addr b0)))) with (max_count c) by (destruct dr; cbn; symmetry; exact PMAX).
               replace (pc_csize (pc_push (if dr then pc_dropn p dn else p) (compact (h_L h) c (b_addr b0)))) with (class_size c) by (destruct dr; cbn; symmetry; exact PCSZ).
               exact PCL4. }
      split; [exact CKS4|]. split; [exact LCK4|].
      split. { cbn [pc_chunks pc_push]. rewrite length_app, LENP. cbn [length]. rewrite Nat.add_1_r, HCKS.
               rewrite firstn_upd_snoc by (rewrite LCK; unfold pc_count in *; rewrite PMAX in CNT16; destruct dr;
                                            [destruct DR as [D1 D2]; clear -D1 D2 CNT16 MCR; lia| ddestruct DRC as (D1 & _ & ->); clear -D1 CNT16 MCR; lia]).
               rewrite map_app. cbn [map]. f_equal. all: try (f_equal; f_equal; unfold compact, region_beg, kRegionSize; reflexivity).
               unfold pc_count. destruct dr; cbn [pc_chunks pc_dropn].
               + destruct DR as [D1 D2]. replace (Z.to_nat (Z.of_nat (length (pc_chunks p)) - Z.of_nat dn)) with (length (pc_chunks p) - dn)%nat by (clear; lia).
                 rewrite <- firstn_map, <- FST, firstn_firstn. f_equal. clear; lia.
               + ddestruct DRC as (_ & _ & ->). rewrite Z.sub_0_r, Nat2Z.id. exact FST. }
      cbn [pc_max pc_csize pc_push]. destruct dr; cbn [pc_max pc_csize pc_dropn]; exact (conj PMAX PCSZ). }
    assert (G2' : hm_thread h' m4).
    { eapply (hm_thread_frame_but m m4 WM h c _ cks' THR GC31); [ | | | | | exact PCL' | intros; reflexivity | apply recb_L | apply recb_cinit | ].
      - eapply keep_rw; [exact UNW| apply KOM; cbn [cells_size csize Nat.add]; apply DJT; clear -C30; lia| exact WM].
      - intros c1 Hc1 NE1. apply KOM. apply DJT; clear -C30 Hc1 NE1; lia.
      - apply KOM. apply DJT; clear -C30; lia.
      - exact WT4.
      - clear -T0; lia.
      - intros c1. exact (recb_cache h dr dn f b0 tb HB c1). }
    (* [comment removed for export] *)
    assert (G3' : hm_depot h' m4).
    { unfold hm_depot. replace (h_dep h') with (h_dep h) by (symmetry; apply recb_dep). apply (hm_depot_frame h m m4 G3 WM); [apply IAG; vm_compute; reflexivity| |].
      - intros b Hb. destruct (In_nth_error _ _ Hb) as [jb Hjb].
        pose proof (z_node_T h GEO jb b Hjb) as Y1. pose proof (z_node_hull h GEO jb b Hjb) as Y2. pose proof (z_node_stk h GEO jb b Hjb) as Y3. pose proof (z_node_band h GEO jb b Hjb) as Y4.
        unfold zapart in Y1, Y2, Y3, Y4. cbn [fst snd] in Y1, Y2, Y3, Y4. apply KOM. apply DJzone; [clear; lia| clear -Y1; lia| clear -Y2; lia| clear -Y3; lia| clear -Y4; lia].
      - intros b Hb. destruct (In_nth_error _ _ Hb) as [jb Hjb].
        pose proof (z_store_T h GEO jb b Hjb) as Y1. pose proof (z_store_hull h GEO jb b Hjb) as Y2. pose proof (z_store_stk h GEO jb b Hjb) as Y3. pose proof (z_store_band h GEO jb b Hjb) as Y4.
        unfold zapart in Y1, Y2, Y3, Y4. cbn [fst snd] in Y1, Y2, Y3, Y4. apply KOM. apply DJzone; [clear; lia| clear -Y1; lia| clear -Y2; lia| clear -Y3; lia| clear -Y4; lia]. }
    assert (FAA8 : (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) mod 8 = 0).
    { pose proof WL as (M16 & _). pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(clear; lia)) as D. rewrite M16, Z.add_0_r in D.
      pose proof (Z.div_mod mfa (2^18) ltac:(clear; lia)) as D2. pose proof MFAL as MFAL'. fold mfa in MFAL'. unfold kFreeArrayMapSize in MFAL'. rewrite MFAL', Z.add_0_r in D2.
      rewrite D, D2. replace (2 ^ 16 * (l_sb (h_L h) / 2 ^ 16) + c * 2 ^ 32 + 3758096384 + 2 ^ 18 * (mfa / 2 ^ 18))
        with (8 * (2^13 * (l_sb (h_L h) / 2 ^ 16) + c * 2^29 + 469762048 + 2^15 * (mfa / 2^18))) by (clear; lia). rewrite Z.mul_comm. apply Z_mod_mult. }
    (* [comment removed for export] *)
    unfold kFreeArrayMapSize, kFreeArraySize in ROOM. unfold kUserLimit in MULIM. unfold kFreeArraySize in MFB.
    ddestruct (user_vs_ri h c WL WR GC31) as (URI & B6RB & FARI & RIH). fold r in URI. fold mu in URI.
    unfold region_beg, kRegionSize in URI, B6RB. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize in FARI.
    pose proof (carve_end8 h c WL WR GC31) as CE8. fold r in CE8. fold au in CE8. unfold region_beg, kRegionSize in CE8.
    (* [comment removed for export] *)
    assert (APF : forall kb, In kb (h_chunks h) ->
              ext_hi kb <= l_sb (h_L h) + c * 2^32 + 3758096384 + mfa \/ l_sb (h_L h) + c * 2^32 + 3758096384 + mfa + 2^18 <= ext_lo kb).
    { intros kb Hkb. destruct (ext_cases h kb WL WR WK Hkb) as [(c' & P' & EC' & C' & RL' & RH' & AUMU')|(i' & sh & P' & N' & EL' & EH')].
      - pose proof (user_vs_fa h c c' WR GC31 ltac:(clear -C'; lia)) as Q5. unfold fa_beg, kFreeArrayOffset, kFreeArraySize, region_beg, kRegionSize in Q5, RL', RH'.
        fold r in Q5. fold mfa in Q5. clear - Q5 RL' RH' AUMU' MFB ROOM; lia.
      - pose proof (z_sec_hull h GEO i' _ N') as Y2. unfold zapart in Y2. cbn [fst snd] in Y2. clear - Y2 EL' EH' B6RB FARI RIH MFB ROOM; lia. }
    (* [comment removed for export] *)
    assert (DJri : forall A n', ri_base (h_L h) + 128 * c + 32 <= A -> A + n' <= ri_base (h_L h) + 128 * c + 80 -> disjoint_from W A n').
    { intros A n' H1 H2. subst W. cbn [disjoint_from]. pose proof aceil_bounds as ACB.
      clear - H1 H2 RI1 STK0 LOL URI SFB ZTH HRI SB0 B6RB RIH FARI NF4 NF0 ROOM MCR C30 AUMU ACB. repeat split; lia. }
    (* [comment removed for export] *)
    assert (K32 : rw_cells asegs m4 (ri_addr (h_L h) c + 32) [C8 (Z_to_bv 64 au)]).
    { eapply keep_rw; [exact RAU| apply KOM; apply DJri; unfold ri_addr; cbn [cells_size csize Nat.add]; clear; lia| exact WM]. }
    assert (K40 : rw_cells asegs m4 (ri_addr (h_L h) c + 40) [C8 (Z_to_bv 64 0)]).
    { eapply keep_rw; [exact R40| apply KOM; apply DJri; unfold ri_addr; cbn [cells_size csize Nat.add]; clear; lia| exact WM]. }
    assert (K56 : rw_cells asegs m4 (ri_addr (h_L h) c + 56) [C8 (Z_to_bv 64 0)]).
    { eapply keep_rw; [exact R56| apply KOM; apply DJri; unfold ri_addr; cbn [cells_size csize Nat.add]; clear; lia| exact WM]. }
    assert (K68 : rw_cells asegs m4 (ri_addr (h_L h) c + 68) [C1 exb]).
    { eapply keep_rw; [exact R68| apply KOM; apply DJri; unfold ri_addr; cbn [cells_size csize Nat.add]; clear; lia| exact WM]. }
    assert (K72 : rw_cells asegs m4 (ri_addr (h_L h) c + 72) [C8 stw]).
    { eapply keep_rw; [exact R72| apply KOM; apply DJri; unfold ri_addr; cbn [cells_size csize Nat.add]; clear; lia| exact WM]. }
    assert (KFA : u32arr asegs m4 (fa_beg (h_L h) c) (map (Z_to_bv 64) (r_fa r))).
    { eapply keep_u32arr; [exact RFA| | exact WM]. rewrite length_map. change (Z.of_nat (length (r_fa r))) with (r_nfreed r).
      apply KOM. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset. apply DJhull; clear - B6RB FARI RIH URI AUMU MULIM NF0 NF4 ROOM C30; lia. }
    assert (KWRU : wr_at asegs m4 (region_beg (h_L h) c) mu) by (eapply wr_at_transport; [exact WRU| exact WM]).
    assert (KSHT : rw_cells asegs m4 (shad (region_beg (h_L h) c + au)) [CB (Z.to_nat ((mu - au) / 8)) (fill 0xfa ((mu - au) / 8))]).
    { eapply keep_rw; [exact SHT| | exact WM]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear - AUMU; lia).
      pose proof (shad_disj_gen (l_sb (h_L h) + c * 2^32 + au) (mu - au) (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) CE8 FAA8 ltac:(clear; lia) ltac:(left; clear - MULIM MFB; lia)) as SD2.
      change ((2 ^ 18 + 7) / 8) with 32768 in SD2. unfold AW_FreeG.shad in SD2. unfold shad, region_beg, kRegionSize.
      pose proof (Z.div_mod (l_sb (h_L h) + c * 2^32 + au) 8 ltac:(clear; lia)) as D1. rewrite CE8, Z.add_0_r in D1.
      pose proof (Z.div_mod (mu - au) 8 ltac:(clear; lia)) as D2. pose proof (Z.mod_pos_bound (mu - au) 8 ltac:(clear; lia)) as D3.
      apply KOM. apply DJband; [clear - D1 SB0 C30 AUMU; lia| clear - D1 D2 D3 AUMU URI RI1; lia| exact SD2 || (clear -SD2; lia)]. }
    assert (KSHF : forall k0, 0 <= k0 < au / class_size c -> rw_cells asegs m4 (shad (chunk_at (h_L h) c k0)) [C1 (Z_to_bv 8 0xfa)]).
    { intros k0 Hk0. eapply keep_rw; [exact (SHF1 k0 Hk0)| | exact WM]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
      assert (Hk0' : 0 <= k0 < carved h c) by (unfold carved; fold r; fold au; exact Hk0).
      destruct (slot_le h c k0 WR GC31 Hk0') as [S1 S2]. fold r in S2. fold au in S2. unfold region_beg, kRegionSize in S1, S2.
      pose proof (chunk_at8 (h_L h) c k0 WL GC31) as A8.
      pose proof (shad_disj_gen (chunk_at (h_L h) c k0) 8 (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) A8 FAA8 ltac:(clear; lia) ltac:(left; clear - S2 AUMU MULIM MFB CSR; lia)) as SD2.
      change ((2 ^ 18 + 7) / 8) with 32768 in SD2. change (8 / 8) with 1 in SD2. unfold AW_FreeG.shad in SD2. unfold shad.
      pose proof (Z.div_mod (chunk_at (h_L h) c k0) 8 ltac:(clear; lia)) as D1. rewrite A8, Z.add_0_r in D1.
      apply KOM. apply DJband; [clear - D1 S1 SB0 C30; lia| clear - D1 S2 AUMU URI RI1 CSR; lia| exact SD2 || (clear -SD2; lia)]. }
    (* [comment removed for export] *)
    assert (TOPH : dr = true -> map sx32 (top_half (ds c) (max_count c) (max_count c / 2)) = map (Z_to_bv 64) (pc_lastn p dn)).
    { intros Hdr. rewrite Hdr in DR. destruct DR as [D1 D2]. unfold top_half, pc_lastn. unfold pc_count in D1.
      pose proof (Z.div_mod (max_count c) 2 ltac:(clear; lia)) as Dm. pose proof (Z.mod_pos_bound (max_count c) 2 ltac:(clear; lia)) as Dm'.
      assert (LEN : length (pc_chunks p) = Z.to_nat (max_count c)) by (clear - D1; lia).
      assert (DNB : (dn <= length (pc_chunks p))%nat) by (rewrite LEN, D2; clear - Dm Dm' MCR; lia).
      replace (Z.to_nat (max_count c - max_count c / 2)) with (length (pc_chunks p) - dn)%nat by (rewrite LEN, D2; clear - Dm Dm' MCR; lia).
      replace (Z.to_nat (max_count c / 2)) with dn by (rewrite D2; reflexivity).
      rewrite firstn_skipn_comm. replace (length (pc_chunks p) - dn + dn)%nat with (length (pc_chunks p)) by (clear -DNB; lia).
      rewrite FST, skipn_map, map_map. apply map_ext_in. intros q Hq. apply In_skipn_In in Hq.
      destruct (proj1 (Forall_forall _ _) CKOK q Hq) as (Q0 & k0 & Hk0 & E16).
      apply sx32_small. pose proof (proj1 (Z.mul_lt_mono_pos_r (class_size c) k0 (carved h c) ltac:(clear -CSR; lia)) (proj2 Hk0)) as X.
      unfold carved in X, AUCS. fold r in X. fold au in X. fold r in AUCS. fold au in AUCS. pose proof (Z.mul_div_le au (class_size c) ltac:(clear -CSR; lia)) as Y.
      clear - X Y Q0 E16 AUMU MULIM CSR. nia. }
    assert (LENL : length (pc_lastn p dn) = dn /\ (dr = false -> pc_lastn p dn = [])).
    { unfold pc_lastn. rewrite length_skipn. unfold pc_count in DR, CNT16. destruct dr.
      - destruct DR as [D1 D2]. split; [| intros X; discriminate X].
        pose proof (Z.div_mod (max_count c) 2 ltac:(clear; lia)) as Dm. pose proof (Z.mod_pos_bound (max_count c) 2 ltac:(clear; lia)) as Dm'.
        assert (Hdn : Z.of_nat dn <= max_count c) by (rewrite D2, Z2Nat.id by (clear -Dm Dm' MCR; lia); clear -Dm Dm' MCR; lia).
        clear - Hdn D1. lia.
      - ddestruct DRC as (_ & _ & DN). split; [rewrite DN; clear; lia| intros _; rewrite DN, Nat.sub_0_r; apply skipn_all]. }
    (* [comment removed for export] *)
    assert (G5c : hm_region m4 (h_L h) c (if dr then RG mu au (mfa + funit f) (r_fa r ++ pc_lastn p dn) else r) (a_exh (h_acct h) c)).
    { unfold hm_region. cbn zeta. destruct dr.
      - destruct (DRT eq_refl) as [_ CPY]. destruct LENL as [LENL _].
        cbn [r_mapped_user r_alloc_user r_mapped_fa r_fa].
        assert (NFE : r_nfreed (RG mu au (mfa + funit f) (r_fa r ++ pc_lastn p dn)) = r_nfreed r + Z.of_nat dn).
        { unfold r_nfreed. cbn [r_fa]. rewrite length_app, LENL. clear; lia. }
        rewrite NFE, <- HNF, <- UFZ.
        split; [exact RMX4|]. split; [exact RNF4|]. split; [exact RMFA4|]. split; [exact K32|]. split; [exact K40|]. split; [exact RMU4 || (fold mu in RMU; eapply keep_rw; [exact RMU| apply KOM; apply DJri; unfold ri_addr; cbn [cells_size csize Nat.add]; clear; lia| exact WM])|].
        split; [exact K56|]. split; [exact K68|]. split; [exists stw; exact K72|]. split; [dexists st80', s88; exact RST4|].
        split. { rewrite map_app. apply u32arr_app. split; [exact KFA|]. rewrite length_map. change (Z.of_nat (length (r_fa r))) with (r_nfreed r).
                 rewrite <- (TOPH eq_refl). exact CPY. }
        split. { exists js'. split; [exact FAJ4| exact JSL4]. }
        split; [exact KWRU|]. split; [exact KSHT|]. exact KSHF.
      - ddestruct DRC as (D1 & DF & DN). subst f. rewrite DN in HNF. cbn [Z.of_nat unit_if] in HNF, RMFA4, JSL4. rewrite Z.add_0_r in HNF, RMFA4, JSL4. subst nf'.
        split; [exact RMX4|]. split; [exact RNF4|]. split; [exact RMFA4|].
        split; [exact K32|]. split; [exact K40|]. split; [exact RMU4 || (fold mu in RMU; eapply keep_rw; [exact RMU| apply KOM; apply DJri; unfold ri_addr; cbn [cells_size csize Nat.add]; clear; lia| exact WM])|]. split; [exact K56|]. split; [exact K68|]. split; [exists stw; exact K72|].
        split; [dexists st80', s88; exact RST4|]. split; [exact KFA|].
        split. { exists js'. split; [exact FAJ4| exact JSL4]. }
        split; [exact KWRU|]. split; [exact KSHT|]. exact KSHF. }
    (* [comment removed for export] *)
    assert (G4' : hm_chunks h' m4).
    { unfold hm_chunks. replace (h_chunks h') with (h_chunks h) by (symmetry; apply (recb_chunks h dr dn f)). apply Forall_forall. intros k' Hk'.
      ddestruct (chunk_geom' h k' WL WR WK Hk') as (RZ' & N0' & U8').
      apply (hm_chunk_frame m m4 WM k' (proj1 (Forall_forall _ _) G4 k' Hk') RZ' N0' U8').
      ddestruct (chunk_ext' h k' WL WR WK Hk') as (_ & F1 & F2 & F3 & F4 & F5 & F6 & FC).
      assert (XAB : ext_lo k' <= ck_ab k') by (unfold ext_lo, ck_map_beg; destruct (ck_prim k'); clear; lia).
      assert (UIN : ck_ab k' + ck_rz k' = ck_user k') by reflexivity.
      assert (NFX' : 0 <= nfix (ck_n k') /\ nfix (ck_n k') <= Z.max (ck_n k') 8) by (unfold nfix; clear -N0'; lia).
      assert (KX : forall A n', 0 <= n' -> ext_lo k' <= A -> A + n' <= ext_hi k' -> kept m m4 A n').
      { intros A n' N0'' HA HB'. apply KOM. destruct FC as [(P' & C' & RL' & RH' & _)|(P' & i' & N' & EL' & EH')].
        - pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear -C'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
          dpose (user_vs_ri h (ck_cls k') WL WR ltac:(clear -C'; lia)) as (Q1 & Q2 & Q3 & Q4).
          pose proof (user_vs_fa h c (ck_cls k') WR GC31 ltac:(clear -C'; lia)) as Q5.
          unfold fa_beg, kFreeArrayOffset, kFreeArraySize in Q3, Q5. unfold region_beg, kRegionSize in Q1, Q2, Q3, Q5, RL', RH'. fold r in Q5. fold mfa in Q5.
          apply DJhull; clear - HA HB' N0'' Q1 Q2 Q3 Q4 Q5 AUMU' RL' RH' NF0 NF4 C30; lia.
        - pose proof (z_sec_T h GEO i' _ N') as Y1. pose proof (z_sec_hull h GEO i' _ N') as Y2. pose proof (z_sec_stk h GEO i' _ N') as Y3. pose proof (z_sec_band h GEO i' _ N') as Y4.
          unfold zapart in Y1, Y2, Y3, Y4. cbn [fst snd s_map_beg s_map_size] in Y1, Y2, Y3, Y4.
          apply DJzone; [exact N0''| clear -Y1 HA HB' EL' EH'; lia| clear -Y2 HA HB' EL' EH'; lia| clear -Y3 HA HB' EL' EH'; lia| clear -Y4 HA HB' EL' EH'; lia]. }
      unfold chunk_kept. split; [apply KX; [clear -RZ'; lia| exact XAB| clear - UIN F4; lia]|].
      split.
      - (* [comment removed for export] *)
        intros AK.
        pose proof (Z.div_mod (ck_user k') 8 ltac:(clear; lia)) as D1. rewrite U8', Z.add_0_r in D1.
        pose proof (Z.div_mod (nfix (ck_n k') + 7) 8 ltac:(clear; lia)) as D2. pose proof (Z.mod_pos_bound (nfix (ck_n k') + 7) 8 ltac:(clear; lia)) as D3.
        pose proof (APF k' Hk') as APf0.
        assert (APf : ck_user k' + nfix (ck_n k') <= l_sb (h_L h) + c * 2^32 + 3758096384 + mfa \/ l_sb (h_L h) + c * 2^32 + 3758096384 + mfa + 2^18 <= ck_user k')
          by (clear - APf0 F1 F2 F3 NFX'; lia).
        pose proof (shad_disj (ck_user k') (nfix (ck_n k')) (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) U8' FAA8 (proj1 NFX') ltac:(clear; lia) APf) as SD2.
        change ((2 ^ 18 + 7) / 8) with 32768 in SD2. unfold AW_FreeG.shad in SD2. unfold shad. pose proof aceil_bounds as ACB.
        apply KOM. apply DJband; [clear - D1 F5 XAB UIN RZ'; unfold kHighMemBeg in F5; lia| clear - D1 D2 D3 F3 F6 NFX' ACB; lia| exact SD2 || (clear -SD2; lia)].
      - (* [comment removed for export] *)
        intros NAK. apply KX; [clear; lia| clear - XAB UIN RZ'; lia| clear - F3; lia]. }
    (* [comment removed for export] *)
    assert (G5' : hm_regions h' m4).
    { intros c' Hc'. unfold h'. rewrite (recb_L h dr dn f), (recb_reg h dr dn f b0 tb HB c'), (recb_acct h dr dn f). fold c.
      destruct (Z.eqb_spec c' c) as [->|NE].
      - rewrite ?Z.eqb_refl. cbn [andb]. exact G5c.
      - rewrite ?(proj2 (Z.eqb_neq c' c) NE). cbn [andb].
        pose proof (WR c' ltac:(unfold kNumClasses; clear -Hc'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & AUCS' & MUAL' & MULIM' & MUAU' & MFAL' & MFB' & NF4c & _).
        apply (hm_region_frame m m4 WM (h_L h) c' (h_reg h c') _ (G5 c' Hc') AUMU' NF4c).
        dpose (user_vs_ri h c' WL WR Hc') as (Q1 & Q2 & Q3 & Q4). pose proof (user_vs_fa h c c' WR GC31 Hc') as Q5. pose proof (user_vs_fa h c' c WR Hc' GC31) as Q6.
        pose proof (user_vs_user h c c' WR GC31 Hc' ltac:(clear -NE; lia)) as Q7. pose proof (fa_vs_fa (h_L h) c c' ltac:(clear -NE; lia)) as Q8.
        fold r in Q5, Q6, Q7. fold mu in Q5, Q6, Q7. fold au in Q5, Q6, Q7. fold mfa in Q5, Q6, Q7.
        unfold fa_beg, kFreeArrayOffset, kFreeArraySize, region_beg, kRegionSize in Q1, Q2, Q3, Q5, Q6, Q7, Q8. unfold kUserLimit in MULIM'. unfold kFreeArraySize in MFB'.
        unfold region_kept. split; [| split; [| split]].
        + apply KOM. unfold ri_addr. apply DJhull; clear - Hc' NE Q1 Q2 Q4 B6RB URI RIH AUMU FARI C30 NF0 NF4 ROOM MCR; lia.
        + apply KOM. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset. apply DJhull; clear - Hc' NE Q2 Q3 Q4 Q6 Q8 MFB' AUMU MULIM C30 NF0 URI RIH; lia.
        + pose proof (carve_end8 h c' WL WR Hc') as A8. unfold region_beg, kRegionSize in A8. unfold region_beg, kRegionSize, shad.
          pose proof (Z.div_mod (l_sb (h_L h) + c' * 2^32 + r_alloc_user (h_reg h c')) 8 ltac:(clear; lia)) as D1. rewrite A8, Z.add_0_r in D1.
          pose proof (Z.div_mod (r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) 8 ltac:(clear; lia)) as D2.
          pose proof (Z.mod_pos_bound (r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) 8 ltac:(clear; lia)) as D3.
          pose proof (shad_disj_gen _ (r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) A8 FAA8
                        ltac:(clear; lia) ltac:(clear - Q5 AUMU' MFB ROOM; lia)) as SD2.
          change ((2 ^ 18 + 7) / 8) with 32768 in SD2. unfold AW_FreeG.shad in SD2.
          apply KOM. apply DJband; [clear - D1 Q2 AUMU' SB0 Hc'; lia| clear - D1 D2 D3 Q1 AUMU' RI1; lia| exact SD2 || (clear -SD2; lia)].
        + intros k0 Hk0. assert (Hk0' : 0 <= k0 < carved h c') by (unfold carved; exact Hk0).
          destruct (slot_le h c' k0 WR Hc' Hk0') as [S1 S2]. unfold region_beg, kRegionSize in S1, S2.
          pose proof (chunk_at8 (h_L h) c' k0 WL Hc') as A8. pose proof (class_size_range c' Hc') as CSR'.
          pose proof (shad_disj_gen (chunk_at (h_L h) c' k0) 8 (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) A8 FAA8 ltac:(clear; lia)
                        ltac:(unfold chunk_at, region_beg, kRegionSize in *; clear - Q5 S1 S2 CSR' AUMU' MFB ROOM; lia)) as SD2.
          change ((2 ^ 18 + 7) / 8) with 32768 in SD2. change (8 / 8) with 1 in SD2. unfold AW_FreeG.shad in SD2. unfold shad.
          pose proof (Z.div_mod (chunk_at (h_L h) c' k0) 8 ltac:(clear; lia)) as D1. rewrite A8, Z.add_0_r in D1.
          apply KOM. apply DJband; [unfold chunk_at, region_beg, kRegionSize in *; clear - D1 S1 Q2 SB0 Hc'; lia| unfold chunk_at, region_beg, kRegionSize in *; clear - D1 S2 AUMU' Q1 RI1 CSR'; lia
                                  | exact SD2 || (clear -SD2; lia)]. }
    (* [comment removed for export] *)
    assert (G7' : hm_sec h' m4).
    { unfold hm_sec. unfold h'. rewrite (recb_sec h dr dn f), (recb_L h dr dn f), (recb_pa h dr dn f). change (hm_sec h m4).
      dpose WS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
      apply (hm_sec_frame m m4 WM h G7 WS); [apply IAG; vm_compute; reflexivity| |].
      - apply KOM. rewrite S5. apply DJzone; [clear -S3; lia| clear -Zpa1 S4; lia| clear -Zpa2 S4; lia| clear -Zpa3 S4; lia| clear -Zpa4 S4; lia].
      - intros sh Hsh. destruct (In_nth_error _ _ Hsh) as [i' N']. apply KOM.
        pose proof (proj1 (Forall_forall _ _) S8 sh Hsh) as (_ & SZ & _).
        pose proof (z_sec_T h GEO i' _ N') as Y1. pose proof (z_sec_hull h GEO i' _ N') as Y2. pose proof (z_sec_stk h GEO i' _ N') as Y3. pose proof (z_sec_band h GEO i' _ N') as Y4.
        unfold zapart in Y1, Y2, Y3, Y4. cbn [fst snd] in Y1, Y2, Y3, Y4.
        apply DJzone; [clear; lia| clear -Y1 SZ; lia| clear -Y2 SZ; lia| clear -Y3 SZ; lia| clear -Y4 SZ; lia]. }
    assert (G8' : hm_fake h' LF m4).
    { unfold hm_fake. unfold h'. rewrite (recb_L h dr dn f). replace (h_fake (h_recb h dr dn f)) with (h_fake h) by (symmetry; apply recb_fake).
      dpose WL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS0 & FS1 & _).
      pose proof G8 as G8v. unfold hm_fake in G8v.
      apply (fake_rep_frame m m4 WM (l_fs (h_L h)) LF G8v) || apply (fake_rep_frame m m4 WM (l_fs (h_L h)) LF G8); [unfold lowhigh, kHighMemBeg in FS0; clear -FS0; lia| |].
      - apply KOM. unfold kFakeBytes in Zfs1, Zfs2, Zfs3, Zfs4. apply DJzone; [clear; lia| clear -Zfs1; lia| clear -Zfs2; lia| clear -Zfs3; lia| clear -Zfs4; lia].
      - intros FB nB HFB. pose proof G8 as G8u. unfold hm_fake in G8u. ddestruct G8u as (_ & _ & _ & LFW & _). destruct (LFW _ HFB) as (kk & ii & Hkk & Hii & EFB).
        pose proof (fsk_frame_inside (l_fs (h_L h)) kk ii Hkk Hii) as [I1 I2]. pose proof (fsk_sizes kk Hkk) as (SZ1 & _).
        assert (EF1 : FB = fsk_frame (l_fs (h_L h)) kk ii) by (clear -EFB; congruence). assert (EF2 : nB = fsk_bytes kk) by (clear -EFB; congruence).
        rewrite EF1, EF2. apply KOM. unfold kFakeBytes in Zfs1, Zfs2, Zfs3, Zfs4, I2.
        apply DJzone; [clear; lia| clear -Zfs1 I1 I2 SZ1; lia| clear -Zfs2 I1 I2 SZ1; lia| clear -Zfs3 I1 I2 SZ1; lia| clear -Zfs4 I1 I2 SZ1; lia]. }
    assert (G9' : hm_ia h' m4).
    { unfold hm_ia. unfold h'. rewrite (recb_ia h dr dn f). change (hm_ia h m4). apply (hm_ia_frame m m4 WM h G9). apply IAG. vm_compute. reflexivity. }
    assert (GE' : hm_emb h' m4).   (* [comment removed for export] *)
    { apply (hm_emb_frame_i m m4 WM h h' GE); [unfold h'; rewrite (recb_acct h dr dn f); reflexivity| unfold h'; rewrite (recb_acct h dr dn f); reflexivity| apply IAG; vm_compute; reflexivity]. }
    (* [comment removed for export] *)
    assert (KB : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> kept m m4 (b_addr b) 8192).
    { intros b Hb. apply KOM. ddestruct (batch_slot h b WF Hb) as (ib & Hib & EBb). change kBatchClass with c in Hib, EBb.
      destruct (slot_le h c ib WR GC31 Hib) as [S1 S2]. rewrite <- EBb in S1, S2. fold r in S2. fold au in S2. change (class_size c) with 8192 in S2.
      unfold region_beg, kRegionSize in S1, S2.
      apply DJhull; clear - S1 S2 B6RB URI RIH FARI AUMU MULIM NF0 NF4 ROOM MCR C30; lia. }
    assert (RQ' : RIq h' C None m4).
    { apply (RIq_popb h h' C bc i m4).
      - apply (RIq_frame m m4 WM h C (Some (bc, i)) RQ).
        + apply KOM. apply DJT; clear -C30; lia.
        + apply IAG. vm_compute. reflexivity.
        + apply KOM. pose proof (z_T_stk h GEO) as Y1. pose proof (z_hull_stk h GEO) as Y2. unfold zapart in Y1, Y2. cbn [fst snd] in Y1, Y2.
          apply DJfar; [right; clear -CB0; lia| clear - Y1 LOL SPL CB0 CHI; lia| clear - Y2 LOL SPL CB0 CHI; lia| clear - STK0 LOL SPL CB0; lia].
        + exact KB.
        + cbn beta iota. pose proof RQ as RQ0. unfold RIq in RQ0. cbn zeta in RQ0. ddestruct RQ0 as (_ & _ & _ & _ & _ & _ & (_ & _ & b0' & all & E0 & EA & _)).
          rewrite HB in E0. assert (Eb : b0' = b0) by (clear - E0; congruence). rewrite <- EA, Eb. apply KB. exact HB0.
      - exact (recb_L h dr dn f).
      - exact (recb_gq h dr dn f).
      - unfold h'. rewrite (recb_tq h dr dn f b0 tb HB), HB. reflexivity. }
    (* [comment removed for export] *)
    pose proof (ff_view_K AL FF (fsel h c f) h' mo4 (kview_recb h dr dn f b0 tb HB HF2 FX) HK4) as HK'.
    assert (CSM : forall x, ff_CS AL FF h x -> ff_CS AL FF h' x).
    { intros x Hx. apply (ff_view_CS AL FF (fsel h c f) h' x (kview_recb h dr dn f b0 tb HB HF2 FX)).
      destruct HF2 as [Ef|Ef]; rewrite Ef; cbn [fsel]; [exact Hx| exact (ff_cs_mono_fa AL FF h c x Hx)]. }
    (* [comment removed for export] *)
    assert (NB2 : forall a, in_blk (blocks h) a -> l_b6 (h_L h) <= a < l_b6 (h_L h) + 0x2000011000 ->
                    a < ri_base (h_L h) /\ (a < l_sb (h_L h) + c * 2^32 + 3758096384 \/ l_sb (h_L h) + c * 2^32 + 3758096384 + 2^29 <= a)).
    { (intros a dd_H; ddestruct dd_H as (bk & Hbk & Ra); intros Ha). destruct bk as [B N]. cbn [fst snd] in Ra.
      ddestruct (in_blk_chunk h a B N WL WR WK Hbk Ra) as (kb & Hkb & STb & -> & -> & Xb & _).
      destruct (ext_cases h kb WL WR WK Hkb) as [(c' & P' & EC' & C' & RL' & RH' & AUMU')|(i' & sh & P' & N' & EL' & EH')].
      - pose proof (user_vs_ri h c' WL WR ltac:(clear -C'; lia)) as (Q1 & _). pose proof (user_vs_fa h c c' WR GC31 ltac:(clear -C'; lia)) as Q5.
        unfold fa_beg, kFreeArrayOffset, kFreeArraySize, region_beg, kRegionSize in Q1, Q5, RL', RH'. clear - Q1 Q5 RL' RH' AUMU' Xb; lia.
      - exfalso. pose proof (z_sec_hull h GEO i' _ N') as Y2. unfold zapart in Y2. cbn [fst snd] in Y2. clear - Y2 EL' EH' Xb Ha; lia. }
    assert (NB3 : forall c0 A N, in_blk (blocks h) c0 -> A mod 8 = 0 -> 0 <= N ->
                    (forall kb, In kb (h_chunks h) -> ck_st kb = CHUNK_ALLOCATED -> ck_user kb + nfix (ck_n kb) <= A \/ A + N <= ck_user kb) ->
                    ~ (shad A <= shad c0 < shad A + (N + 7) / 8)).
    { (intros c0 A N dd_H; ddestruct dd_H as (bk & Hbk & Ra); intros A8 N0' AP). destruct bk as [B N'']. cbn [fst snd] in Ra.
      ddestruct (in_blk_chunk h c0 B N'' WL WR WK Hbk Ra) as (kb & Hkb & STb & -> & -> & Xb & U8b & LOb & HIb).
      apply (shad_apart (ck_user kb) (nfix (ck_n kb)) A N (shad c0) U8b A8 ltac:(unfold nfix; clear; lia) N0' (AP kb Hkb STb)).
      unfold AW_FreeG.shad, shad. pose proof (Z.div_mod (ck_user kb) 8 ltac:(clear; lia)) as D1. rewrite U8b, Z.add_0_r in D1.
      pose proof (Z.div_mod c0 8 ltac:(clear; lia)) as D2. pose proof (Z.mod_pos_bound c0 8 ltac:(clear; lia)) as D3.
      pose proof (Z.div_mod (nfix (ck_n kb) + 7) 8 ltac:(clear; lia)) as D4. pose proof (Z.mod_pos_bound (nfix (ck_n kb) + 7) 8 ltac:(clear; lia)) as D5.
      assert (NF : ck_n kb <= nfix (ck_n kb)) by (unfold nfix; clear; lia). clear - D1 D2 D3 D4 D5 NF Ra. lia. }
    pose proof (Z.div_mod (l_b6 (h_L h) + 0x2000011000) 8 ltac:(clear; lia)) as Dhe. pose proof (Z.mod_pos_bound (l_b6 (h_L h) + 0x2000011000) 8 ltac:(clear; lia)) as Dhe'.
    pose proof (Z.div_mod (l_b6 (h_L h)) 8 ltac:(clear; lia)) as Db6. pose proof (Z.mod_pos_bound (l_b6 (h_L h)) 8 ltac:(clear; lia)) as Db6'.
    pose proof (Z.div_mod (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) 8 ltac:(clear; lia)) as Dfaa. rewrite FAA8, Z.add_0_r in Dfaa.
    assert (FK : fkeep (h_L h) (blocks h) QS (d_nb (h_dep h)) (d_bl (h_dep h)) lo SP m m4).
    { apply (fkeep_of_munch _ _ _ _ _ _ _ W m m4 MU). subst W.
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. left. exact Ha. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. right; left. clear - Ha C30; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. right; left. clear - Ha C30; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. right; left. clear - Ha; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. right; left. clear - Ha; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 2 right; left. split; [unfold in_hull; clear - Ha B6RB URI AUMU RIH C30; lia| intros IB; destruct (NB2 a IB ltac:(clear - Ha B6RB URI AUMU RIH C30; lia)) as [X _]; clear - X Ha C30; lia]. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 2 right; left. split; [unfold in_hull; clear - Ha B6RB URI AUMU RIH C30; lia| intros IB; destruct (NB2 a IB ltac:(clear - Ha B6RB URI AUMU RIH C30; lia)) as [X _]; clear - X Ha C30; lia]. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 2 right; left. split; [unfold in_hull; clear - Ha B6RB URI AUMU RIH C30; lia| intros IB; destruct (NB2 a IB ltac:(clear - Ha B6RB URI AUMU RIH C30; lia)) as [X _]; clear - X Ha C30; lia]. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 2 right; left. split; [unfold in_hull; clear - Ha B6RB FARI RIH NF0 NF4 ROOM MCR; lia| intros IB; destruct (NB2 a IB ltac:(clear - Ha B6RB FARI RIH NF0 NF4 ROOM MCR; lia)) as [_ X]; clear - X Ha NF0 NF4 ROOM MCR; lia]. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 2 right; left. split; [unfold in_hull; clear - Ha B6RB FARI RIH MFB ROOM; lia| intros IB; destruct (NB2 a IB ltac:(clear - Ha B6RB FARI RIH MFB ROOM; lia)) as [_ X]; clear - X Ha MFB ROOM; lia]. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 3 right; left. split.
        - unfold shad, in_hull. clear - Ha Dfaa Dhe Dhe' Db6 Db6' B6RB FARI RIH MFB ROOM. lia.
        - (intros dd_H; ddestruct dd_H as (c0 & IB & Ea)). refine (NB3 c0 (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) IB FAA8 ltac:(clear; lia) _ _).
          + intros kb Hkb _. pose proof (APF kb Hkb) as X. ddestruct (chunk_ext' h kb WL WR WK Hkb) as (_ & F1 & F2 & F3 & _).
            assert (NFb : nfix (ck_n kb) <= Z.max (ck_n kb) 8) by (unfold nfix; clear; lia). clear - X F1 F2 F3 NFb; lia.
          + rewrite <- Ea. change ((2 ^ 18 + 7) / 8) with 32768. exact Ha || (unfold shad; clear -Ha; lia). }
      apply Forall_nil. }
    (* [comment removed for export] *)
    apply HC. unfold batch_step_post.
    eexists. dexists mo4, y0, y1, y2, ya0, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m4, dr, dn, f.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact WF'|].
    split. { unfold HMq. unfold h'. rewrite (recb_L h dr dn f). exact (conj G0' (conj G1' (conj G2' (conj G3' (conj G4' (conj G5' (conj G7' (conj G8' (conj G9' GE'))))))))). }
    split; [exact RQ'|]. split; [exact HK'|]. split; [exact HJ4|]. split; [exact CSM|]. split; [exact FK|]. exact (conj WM (conj MI4 ST4)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RecStepBatch.

End ARUN_1.
