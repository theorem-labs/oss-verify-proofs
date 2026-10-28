(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux SysStep ITree Nodes CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_MallocA AW_DepotA AW_DepotB AW_Poison AKinv AKinvS.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_IMemset AW_IAInit AW_Dealloc AW_FreeA AW_QPut AW_Enqueue AW_FreeC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_FreeTop () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA_INIT"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeC.fsegA_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.A_MFHOOKS"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_Q_MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMax"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMin"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineCache"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.A_GOT_FLAGS_"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kMaxMallocFill"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kMallocFillByte"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "ARUN_1.free_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "ARUN_1.img_dj"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.A_QC_RA1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_STACK_DEPOT_PUT"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "ARUN_1.FreeTop.fsegQ_W"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_w0"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_rest"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_PC_FREE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeA.A_FREE_RA2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_IAInit.ia_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.max"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.FreeTop.fsegPC_W"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.qc_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.batch_hdr"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.FreeTop.fsegPC_post"].

Section ARUN_1. Context {hAR : arun}.
Definition img_dj (W : list (Z * Z)) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeTop ()) "PA,$0.Pn,$0.P,(1.(2.(3.+10000.R2.)(3.(4.R2.R1.)$5.))(1.(2.(3.(4.$5.+81030.)R2.)(3.(4.R2.R1.)$6.))(2.(3.(4.$6.+4.)R2.)(3.(4.R2.R1.)+65?000.))))(7.O1.R3.R2.)")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00=0>L15473608403.7L24694995923.7L24903987155.7L26629652627.7L29493141715.7L31663767507.7L38705866195.7L43159775571.7L47582725459.7L52380885587.7L63461281875.7L66066524883.7L8414730451.7 00000100200300400500600700800900:00;00<00=SSSSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma poison_statics_transport_ia : forall W m m', poison_statics m -> munch W m m' -> img_dj W -> poison_statics m'.
Proof.
  intros W m m' PS MU DJ. unfold poison_statics, img_dj in *.
  unfold A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND,
    A_GOT_RMEMSET, A_RMEMSET, A_GOT_CFLAGS, A_CF_CSMT, A_IA, A_IA_INIT in *.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- ro_cells _ _ ?A ?cs => eapply (ro_cells_transport asegs W m m' A cs); [tauto| exact MU| apply DJ; cbn; lia] end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition free_statics (m : mem) (T CTX : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeTop ()) "(2.(8.O3.O2.O1.)(2.(9.$:.O3.(4.$;.+8.)(<.$=.(>.(?.&40.=))(10.$=.)))(2.(9.$:.O3.O2.(<.$=.(>.(?.&40.O1.))(10.$=.)))(2.(9.$:.O3.(4.O1.+8.)(<.$=.(11.(?.&40.=))(10.$=.)))(2.(9.$:.O3.$12.(<.$=.(>.(?.&40.$13.))(<.$=.(>.(?.&40.$14.))(<.$=.(>.(?.&40.$15.))(10.$=.)))))(2.(9.$:.O3.$16.(<.$=.(>.(?.&40.$17.))(10.$=.)))(2.(9.$:.O3.(4.$17.+2<.)(<.$=.(11.(?.&40.$18.))(<.$=.(11.(?.&40.=))(<.$=.(11.(?.&40.$19.))(10.$=.)))))(1:.O3.))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L11228961004.19L21632375596.19000001002SS". (* [comment removed for export] *)
#[using="Type"] Lemma free_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_FreeTop ()) "PW,(1;.$1<.)Pm,P,(1=.&40.)(1>.(1=.&8.))Pm',P,(1=.&40.)(1>.(1=.&8.))PT,$0.PCTX,$0.P,(1?.R4.R2.R1.)P,(20.R6.R5.R4.)P,(21.R7.)P,(7.R8.(4.R4.+98.)+8.)P,(7.R9.R6.+8.)P,(7.R:.(4.R6.+8.)+4.)(1?.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  (intros W m m' T CTX dd_H; ddestruct dd_H as (FS & MF & TT & C8 & QM & GF & FL & PS); intros MU DJ D1 D2 D3).
  split; [eapply fsegA_statics_transport; [exact FS| exact MU| exact DJ| exact D1]|].
  unfold img_dj, A_MFHOOKS, A_Q_MAX, A_GOT_FLAGS_, A_FLAGS, A_INSTANCE, A_IA, A_IA_INIT in *.
  split; [eapply ro_cells_transport; [exact MF| exact MU| apply DJ; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact TT| exact MU| exact D2]|].
  split; [eapply ro_cells_transport; [exact C8| exact MU| exact D3]|].
  split; [eapply ro_cells_transport; [exact QM| exact MU| apply DJ; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact GF| exact MU| apply DJ; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact FL| exact MU| apply DJ; cbn; lia]|].
  eapply poison_statics_transport_ia; [exact PS| exact MU| exact DJ].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section FreeTop.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  (* [comment removed for export] *)
  Definition fsegQ_W (p lo SP T : Z) : list (Z * Z) :=
    ((T + 3168, T + 3169) :: ia_W lo SP) ++ [(p + -16, p + -12); (p, p + 8); (T + 2824, T + 2840)].

  Definition fsegQ_post (SP : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (p b1 n ctx lo T CTX TOP d : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeTop ()) "Lms',$22.(23.(1=.&40.)Lt0,(1=.&40.)(23.(1=.&40.)Lt1,(1=.&40.)(23.(1=.&40.)Lt2,(1=.&40.)(23.(1=.&40.)La4,(1=.&40.)(23.(1=.&40.)La5,(1=.&40.)(23.(1=.&40.)La6,(1=.&40.)(23.(1=.&40.)La7,(1=.&40.)(23.(1=.&40.)Lt3,(1=.&40.)(23.(1=.&40.)Lt4,(1=.&40.)(23.(1=.&40.)Lt5,(1=.&40.)(23.(1=.&40.)Lt6,(1=.&40.)(23.P,(1=.&40.)(1>.(1=.&8.))Lm',P,(1=.&40.)(1>.(1=.&8.))(23.(1;.(1=.&40.))Lws,(1;.(1=.&40.))(23.$0.Lsize,$0.(23.(1;.(1=.&8.))Lfr1,(1;.(1=.&8.))(23.(1;.(1=.&8.))Lfr2,(1;.(1=.&8.))(23.(1=.&40.)Lfr,(1=.&40.)(23.(1=.&40.)Lfd,(1=.&40.)ZSTK,$0.(4.O1;.-850.)(2.(24.$22.R14.(25.(26.(?.&40.$27.)(?.&40.(4.R1.-30.))O19.(?.&40.$28.)R13.R12.R11.(?.&40.(4.O:.-10.))(?.&40.R1.)(?.&40.(4.R1.+10.))(?.&40.R6.)(?.&40.(4.R1.+10.))(?.&40.O4.)R10.R?.R>.R=.(?.&40.$29.)(?.&40.=)(?.&40.O5.)(?.&40.(4.O1;.-51.))O12.O11.O10.O?.O>.O=.R<.R;.R:.R9.)O<.(?.&40.$2:.)O;.(2;.(1=.&40.))R8.(2<.$:.)))(2.(20.(2=.O:.O6.O1;.O5.)O1.R8.)(2.(2>.$:.O1.R8.)(2.(2?.$:.R8.)(2.(30.$:.R8.(4.O1;.-38.)(<.$=.(>.O13.)(<.$=.(>.O14.)(<.$=.(>.O15.)(<.$=.(>.O16.)(<.$=.(>.O17.)(<.$=.(>.O18.)(<.$=.(>.O1:.)(10.$=.)))))))))(2.(30.$:.R8.R1.(<.$=.(>.(?.&40.(4.R1.+10.)))(<.$=.(>.(?.&40.R6.))(10.$=.))))(2.(31.$:.R8.(4.R1.+10.)R7.)(2.(24.$32.(33.(1=.&40.)R7.)#1>.)(2.(2.(3.+1.R6.)(3.R6.+1>.))(2.(3.R6.(4.O2.+2.))(2.(30.$:.R8.(4.R1.+100.)(<.$=.(34.#708.R5.)(10.$=.)))(2.(30.$:.R8.(4.R1.+808.)(<.$=.(>.(?.&40.O1;.))(10.$=.)))(2.(30.$:.R8.(4.R1.+810.)(<.$=.(34.#8.R4.)(10.$=.)))(2.(30.$:.R8.(4.O5.+<60.)(<.$=.(35.(?.&8.=))(10.$=.)))(2.(30.$:.R8.(4.O:.-10.)(36.O9.+3.))(2.(30.$:.R8.(4.O:.-<.)(37.O8.O7.))(2.(38.$:.R8.O:.+8.)(2.(30.$:.R8.(4.O5.+;08.)(<.$=.(>.R3.)(<.$=.(>.R2.)(10.$=.))))(2.(30.$:.R8.(4.R1.-30.)(<.$=.(>.(?.&40.R1.))(<.$=.(>.(?.&40.+1.))(<.$=.(>.(?.&40.$39.))(<.$=.(>.(?.&40.O:.))(<.$=.(>.(?.&40.O1;.))(<.$=.(>.(?.&40.$3:.))(10.$=.))))))))(2.(1?.R8.O5.O4.)(2.(3;.R8.)(2.(3<.$:.R8.O6.(4.R1.-30.))(3<.$:.R8.(4.O1;.-10.)(3=.O3.O1;.))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "03H0?L11252016963.9 L12137652708.2 L12137653216.3 L12169257239.4 L12169257747.3 L12171406611.5 L1228554110.19 L12614429683.15L13714063045.9 L13715933518.15L15517902650.6 L15521740303.7 L15525134526.3 L15525135034.4 L15527186106.6 L15527186110.5 L15819090975.15L16624624865.12L16767249459.15L17094374179.11L19165751674.6 L19169325603.9 L19605101200.9 L20220576419.15L20385946170.15L20748283235.11L21576793635.9 L21907814743.5 L21907815251.4 L21909894487.6 L2195478707.4  L2195479223.3  L2197591219.6  L2197591223.5  L22059881836.19L22438916261.9 L22706556426.6 L2423008602.3  L24561943877.9 L24694079737.6 L25590112999.11L25590112999.7 L25613424335.9 L25675297475.11L2602137446.8  L2602398557.5  L2602432378.3  L2604173021.4  L2604251490.3  L2604252006.4  L26201078681.11L26786268256.9 L27347316357.4 L27347374394.3 L27347374910.4 L27349162757.4 L27349196578.4 L27349196595.4 L27349424692.3 L27349425978.3 L27349425978.5 L27349425982.2 L27349425982.6 L2772891094.11 L27846297964.3 L27848808849.2 L28488998551.3 L28489580650.5 L28489581166.6 L28489662421.6 L28491401813.6 L28491435619.6 L28491435634.6 L28491664228.5 L28491665002.4 L28491665002.6 L28491665002.8 L28491665006.4 L28491665006.7 L28875318293.10L29464870597.9 L29691702255.10L29953127800.6 L29953128316.5 L29953181891.6 L29955242360.4 L29955242360.7 L29955242364.4 L29955242364.6 L29955242364.7 L29955242364.8 L29955243122.5 L29955471716.6 L29955471733.5 L29955505475.5 L31270000677.9 L31431235571.12L31725289494.11L33053115497.4 L3370308569.19 L33911934729.9 L35611846426.15L36841451887.5 L38235734261.1 L38237949960.3 L39127898626.11L39197273516.19L40624223513.9 L41379960527.9 L41596004140.3 L42627504130.3 L42627504646.4 L42629649922.5 L42629649926.6 L43031687449.9 L44899268207.19L44917553221.6 L44917553236.5 L44917587059.6 L44917848136.4 L44917848136.7 L44917848140.4 L44917848140.6 L44917848140.7 L44917848140.8 L44917849410.5 L44919818739.5 L44919895112.6 L44919895628.5 L45983256612.5 L45983277447.2 L45983329695.5 L45983330203.4 L45985374619.4 L45985374619.6 L45985374619.8 L45985374623.3 L45985374623.7 L45985375381.4 L45985637796.5 L46046034755.9 L46047259582.2 L46532565131.2 L46620446287.7 L47463206778.4 L48084361125.9 L48340869950.19L4855641044.9  L50733006842.15L51273545167.9 L5242678351.9  L5429770831.4  L55125122501.9 L55308827811.11L56720822472.7 L56720822476.6 L56720823746.3 L56721085683.3 L56722907507.4 L56722971848.4 L56722972364.3 L57016548215.8 L60041308855.8 L60805037525.2 L61745013164.6 L61745046923.5 L61745046938.5 L61745275037.5 L61745276307.4 L61745276307.6 L61745276307.7 L61745276311.4 L61745276311.7 L61747423639.5 L61747424147.4 L61747483692.6 L62381144262.12L62381144262.19L6283222205.4  L6283253899.3  L6283253914.4  L6283483270.8  L6285595782.4  L6285596290.3  L6285666621.5  L63851028389.9 L64148687487.12L64148687487.19L64179286662.12L64179286662.19L64467341121.12L65102646465.3 L65102646465.4 L65102646465.6 L65102646465.7 L65104223396.2 L66552381779.4 L66552382295.5 L66554433363.5 L66714871430.9 L66721159227.8 L66765950734.15L67172748439.3 L67172823340.4 L67172823848.3 L67174873126.3 L67174874408.6 L67174874412.7 L67384873697.7 L68055692866.11L68512002721.7 L8806423876.6  L8873338536.3  L9265737838.6  L9267788910.4  L9267789418.3  00000;00<00F00G00H00]01501N01U01m02>02H02I02J02c02d02k03M03f04;04L04a05905J05W05l06A06B06C06R06S06T06`06a07<07Q07a07h07o08@08\09309H09S09T09U09^09_09`09a0::0:K0:L0:M0:N0:O0:P0:Q0:R0:S0:T0:U0:V0:j0;10;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;Z0;a0<10<20<30<40<50<60<70<80<K0<L0<M0<N0<O0<P0<e0=<0=P0=W0=n0>L0>b0>o0?30?70?A0?\0@10@F0@Q0@R0@S0@T0@`0A50A<0A=0A>0A?0A@0AA0AB0AC0AT0AU0AV0AW0AX0AY0AZ0A[0A\0A]0A^0A_0A`0Aa0Ab0Ac0Ad0Ak0B20B80BB0BO0Bd0C<0CC0CP0Ce0D:0DC0DJ0Dc0Dd0De0Df0E30E40E50E60EG0EX0E`0Ea0Eb0Ec0Ed0Ee0Ef0F70F80F90F:0F;0F<0F^0G70G80GC0GD0GE0GF0GG0GH0G]0H;0HQ0I30IL0IS0IT0IU0IV0IW0Ia0Ib0Ic0J20JN0Jd0K<0KF0KG0KH0KI0KJ0KK0KU0K_0Ki0L90LD0L]0L^0L_S2SP2lo3TOPFS3hAR1p2PHFFS3hAR2SP2lo5LOIMG3SPLS3hAR2SP1T3CTX3TOP2T02TCS3hAR2SP2lo3CTX3CX15LOIMGS2SP2loS3hAR2SP1T3CTX3TOP2T02TCS2SP1p2lo3TOP3APSS3hAR1T2T0FFS3hAR2SP2lo5LOIMG3SPL3SPHFS3hAR1TS3hAR2SP2lo1T3TOP2T03AST5LOIMG3SPLS3hAR2SP2lo3CTX3CX15LOIMGS3hAR2SP1p2lo3TOP3APSS2SP1p2lo3TOP3APSS2SP2lo1T3TOP3AST3SPLS2SP1p2lo1T1A1k2H12H22H3S3hAR2SP1T3TOP2T0S3hAR3CTX3CX0S3hAR2SP1p2lo3TOP3APSS2SP2lo1T3TOP3AST3SPLFFS3hAR2SP2lo3SPLFFS3hAR2SP3SPHFS3hAR2SP1p1T3CTX3TOP2T03APCS2SP2lo1T3TOP3AST3SPLS2SP1p2lo1T1y2HyS2SP2loS2SP2loS2SP2lo1T3TOP3ASTS3hAR2SP2lo1T2T05LOIMG1A1k1HS3hAR2SP2lo5LOIMG1A1k1HS2SP1p2lo3TOP3APS3SPLS3hAR2SP2loFFS1p1T3APTFFFS3hAR2SP1p2lo3TOP3APS3SPLS3hAR2SP1T3TOP2T0FFFFFFFFFFFS3hAR2SP1p1T3TOP3APTS2SP2loS2SP2loFFFFFFFFFFFFFS3hAR1p1T2PL2T01A1k1HS2SP2loS3hAR1T2T01A1k1HFFFFFFFS2SP2lo3CTX3TOP3ASCFFFFFS2SP2lo1T3TOP3AST3SPLS3hAR2SP1p1T3TOP2T03APTS3hAR2SP1p1T3TOP3APTS2SP2loS3hAR2SP1p1T3TOP2T03APTS3hAR2SP2lo1T3TOP2T03AST5LOIMGS3hAR2SP2lo1T2T15LOIMGS2SP2lo1A1k1HS2loS2loS3hAR1p2PLS3hAR2SP1p1T3CTX3TOP2T03APCS2SP1p2lo3TOP3APS3SPLS2SP1p2lo3TOP3APS3SPLS2SP2lo3TOPFFFS3hAR2SP3SPHS2SP1p2lo3TOP3APS3SPLS3hAR1TFFFFFFFS2SP2lo1T3TOP3ASTFFFFFFFFFFFFFFFFS2SP2loS2SP2loS1p2PLS3hAR1T2T0S3hAR1p2PL2PHS2SP2lo1T3TOP3AST3SPLS3hAR2SP1T3CTX3TOP2T02TCS3hAR1TS3hAR3CTX3CX0S2SP1p2lo3TOP3APS3SPLS2SP1p2lo3TOP3APS3SPLS2SP4TOP2S2SP2loS3hAR2SP2lo1T3TOP3AST3SPLFFFS3hAR3CTX3CX1FFFS3hAR2SP2lo5LOIMGS3hAR2SP2lo5LOIMGS2SP3TOPFFFFFFS2SP1p2lo3TOP3APSFFFFFS3hAR2SP2lo1T3CTX3TOP2T03ASC5LOIMGS3hAR2SP2lo3CTX3CX15LOIMGFS1p3CTX3APCFFFFFS2SP2lo1T3TOP3AST3SPLS3hAR2SP2lo1T3TOP2T03AST5LOIMGS3hAR2SP2lo1T2T15LOIMGS3hAR2SP2lo1T3CTX3TOP2T03ASC5LOIMGS3hAR2SP2lo3CTX3CX15LOIMGS3hAR1TFFFFS4size3SZBFFS3hAR2SP2lo3SPLS3hAR2SP2lo1T2T05LOIMG1A1k1HS2SP2lo1T1A1k2H12H22H3S3hAR2SP1T3CTX3TOP2T02TCS3hAR1T2T1FFFFFS3hAR1p2PLS3hAR1p2PLS3hAR1p2PLS2SP1p2lo1T1y2HyS2SP2lo3SPLS3hAR2SP2lo5LOIMG3SPL3SPHFF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma fsegQ : forall
      (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (SP p b1 n ctx lo T CTX TOP LO TOPU d : Z) (fr fd : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ia : bool) (cs2 cs4 cs5 : list cell) (p0 p1 : word),
      0x65f000 + 16 <= p -> p + 8 <= ACEIL -> p mod 16 = 0 -> 0 <= n < 2^32 -> 0 <= ctx < 2^32 -> 0 <= b1 < 256 -> Z.land b1 3 = 1 ->
      (* [comment removed for export] *)
      rw_cells asegs m A_IA_INIT [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)] ->
      rw_cells asegs m A_IA [C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m (A_IA + 8) [CB (Z.to_nat 0x40000) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))] ->
      rw_cells asegs m (A_IA + 0x40040) cs2 -> Z.of_nat (cells_size cs2) = 0xd80 ->
      rw_cells asegs m (A_IA + 0x40dc0) [C8 p0; C8 p1] ->
      (ia = true -> p0 = Z_to_bv 64 4096 /\ p1 = Z_to_bv 64 (A_IA + 0x40dd0)) ->
      rw_cells asegs m (A_IA + 0x40dd0) cs4 -> Z.of_nat (cells_size cs4) = 0x40248 - 16 ->
      rw_cells asegs m (A_IA + 0x81008) cs5 -> Z.of_nat (cells_size cs5) = 40 ->
      (* [comment removed for export] *)
      free_statics m T CTX ->
      ro_cells asegs m (T + 8) [C8 (Z_to_bv 64 TOP); C8 (Z_to_bv 64 (TOP - 2^23))] -> ro_cells asegs m (T + 40) [C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (T + 2824) [C8 fr; C8 fd] ->
      2^23 <= TOP -> TOP <= 2^47 -> SP + 16 <= 2^47 ->
      Timg T -> T + 4096 <= ACEIL -> 0x65f000 <= CTX -> CTX + 0x10000 <= ACEIL ->
      (T + 4096 <= CTX \/ CTX + 0x10000 <= T) -> crange CS T 4096 -> crange CS CTX 0x10000 ->
      (* [comment removed for export] *)
      rw_cells asegs m (p + -16) (hdr_w0 b1 2) -> rw_cells asegs m (p + -12) (hdr_rest n ctx) -> wr_at asegs m p 8 -> crange CS (p + -16) 24 ->
      (T + 4096 <= p - 16 \/ p + 8 <= T) -> (CTX + 0x10000 <= p - 16 \/ p + 8 <= CTX) -> (Z.max TOP SP <= p - 16 \/ p + 8 <= lo) ->
      (* [comment removed for export] *)
      (Z.max TOP SP <= T \/ T + 4096 <= lo) -> (Z.max TOP SP <= CTX \/ CTX + 0x10000 <= lo) ->
      stk asegs m SP TOP -> crange CS SP (TOP - SP) ->
      LO <= lo -> TOP <= TOPU <= 2^64 -> uwc asegs m LO TOPU (bv_unsigned s0) SP d ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 4096 -> SP mod 16 = 0 ->
      crange CS lo (SP - lo) -> mem_inv asegs m ->
      evtA asegs AL CS (fsegQ_post SP ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p b1 n ctx lo T CTX TOP d m)
        (MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_FREE) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p b1 n ctx lo T CTX TOP LO TOPU d fr fd F fc m ia cs2 cs4 cs5 p0 p1
      PL PH PA NB CB B1B B13 IA1 IA2 IA3 IA4 IS4 IA5 IP IA6 IS6 IA7 IS7 FST THR TSW UNW TST TOP0 TOP1 TOP2 T0 T1 CX0 CX1 TC TCS CTXCS
      HW0 HW1 WR PCS APT APC APS AST ASC STT STCS LOB TOPUB UWC ST LOIMG SPL SPA SCS MI.
    dpose FST as (MS8 & MF & TT & C8' & QM & GF & FL & PS).
    assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (fsegA AL IMG ALWF CS CSOK ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p lo T CTX TOP LO TOPU d F fc m ia cs2 cs4 cs5 p0 p1);
        [clear -PL PH; lia | exact IA1 | exact IA2 | exact IA3 | exact IA4 | exact IS4 | exact IA5 | exact IP | exact IA6 | exact IS6 | exact IA7 | exact IS7
        | exact MS8 | exact THR | exact TSW | exact UNW | exact TOP0 | exact TOP1 | exact TOP2 | exact T0 | exact T1 | exact CX0 | exact CX1 | exact TC
        | exact TCS | exact CTXCS | exact STT | exact STCS | exact LOB | exact TOPUB | exact UWC | exact ST | exact LOIMG | exact SPL | exact SPA | exact SCS | exact MI]. }
    clear IA1 IA2 IA3 IA4 IS4 IA5 IP IA6 IS6 IA7 IS7 THR TSW STT ST MI.
    cbv beta zeta. (intros ms1 dd_H; ddestruct dd_H as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & ws & size & fr1 & fr2 & -> &
                              MU1 & WM1 & MI1 & FR7 & STKC & HTR & HL & SZB & SZD & F1800 & TFB & F8 & UNW1 & ST1 & SR1 & IAC1)).
    assert (DJ1 : forall A k, A + k <= lo \/ SP <= A -> (A + k <= 0x10000 \/ 0x65f000 <= A) -> (A + k <= T + 3168 \/ T + 3169 <= A) -> disjoint_from ((T + 3168, T + 3169) :: ia_W lo SP) A k).   (* [comment removed for export] *)
    { intros A k H1 H2 H3. unfold ia_W, A_IA, A_IA_INIT. cbn. clear -H1 H2 H3. lia. }
    assert (IMG1 : img_dj ((T + 3168, T + 3169) :: ia_W lo SP)).
    { intros A k H. unfold ia_W, A_IA, A_IA_INIT in *. cbn. clear -H LOIMG T0. lia. }
    assert (FST1 : free_statics m1 T CTX).
    { eapply free_statics_transport; [exact FST| exact MU1| exact IMG1| | |]; apply DJ1; clear -CX0 CX1 T0 T1 TC ASC AST LOIMG TOP2; lia. }
    dpose FST1 as (MS81 & MF1 & TT1 & C81 & QM1 & GF1 & FL1 & PS1).
    assert (DS1 : dealloc_statics m1 T CTX).
    { dpose MS81 as (_ & _ & _ & _ & _ & _ & TSI & TSP & TSA & TCX). exact (conj MF1 (conj TSI (conj TSP (conj TSA TCX)))). }
    assert (HW01 : rw_cells asegs m1 (p + -16) (hdr_w0 b1 2)) by (eapply rw_cells_transport; [exact HW0| exact MU1| exact WM1| apply DJ1; cbn; clear -APS APT PL LOIMG TOP2; lia]).
    assert (HW11 : rw_cells asegs m1 (p + -12) (hdr_rest n ctx)) by (eapply rw_cells_transport; [exact HW1| exact MU1| exact WM1| apply DJ1; cbn; clear -APS APT PL LOIMG TOP2; lia]).
    assert (WR1 : wr_at asegs m1 p 8) by (eapply wr_at_transport; [exact WR| exact WM1]).
    assert (TST1 : rw_cells asegs m1 (T + 2824) [C8 fr; C8 fd]) by (eapply rw_cells_transport; [exact TST| exact MU1| exact WM1| apply DJ1; cbn; clear -AST T0 LOIMG TOP2; lia]).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (dealloc_spec AL IMG ALWF CS CSOK) with (p := p) (b1 := b1) (n := n) (ctx := ctx) (T := T) (CTX := CTX) (lo := lo) (STK := SP + -2128);
        first [exact HW01 | exact HW11 | exact WR1 | exact PCS | exact TST1 | exact DS1 | exact TCS | exact CTXCS | exact ST1 | exact LOIMG | exact MI1 | exact B1B | exact B13
              | exact PA | exact NB | exact CB | exact T0 | exact CX0 | exact TC | reflexivity
              | clear -PL; lia | clear -PH; lia | clear -SPL LOIMG SPH; lia | clear -T1; lia | clear -CX1; lia | clear -APT; lia | clear -APC; lia
              | clear -SPL; lia | clear -SPH; lia | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
              | clear -APS SPL TOP2; lia | clear -AST SPL TOP2; lia | clear -ASC SPL TOP2; lia
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| clear; lia] ]. }
    cbv beta. (intros ms2 dd_H; ddestruct dd_H as (y14 & y15 & y16 & y17 & m2 & fr' & fd' & -> & MU2 & WM2 & MI2 & HW02 & HW12 & WR2 & TST2 & DS2 & ST2)).
    assert (DJ2 : forall A k, (A + k <= lo \/ SP + -2128 <= A) -> (A + k <= p + -16 \/ p + 8 <= A) -> (A + k <= T + 2824 \/ T + 2840 <= A) ->
                  disjoint_from [(lo, SP + -2128); (p + -16, p + -12); (p, p + 8); (T + 2824, T + 2840)] A k).
    { intros A k H1 H2 H3. cbn. clear -H1 H2 H3. lia. }
    assert (FST2 : free_statics m2 T CTX).
    { eapply free_statics_transport; [exact FST1| exact MU2| | | |];
        [intros A k H; unfold A_IA, A_IA_INIT in H; apply DJ2; clear -H PL T0 LOIMG; lia| | |]; apply DJ2; clear -CX0 CX1 T0 T1 TC APT APC PL AST ASC LOIMG TOP2; lia. }
    dpose FST2 as (MS82 & MF2 & TT2 & C82 & _).
    assert (STKC2 : rw_cells asegs m2 (SP + -2128) [C8 (Z_to_bv 64 (SP + -2128 + 16)); C8 (Z_to_bv 64 size)])
      by (eapply rw_cells_transport; [exact STKC| exact MU2| exact WM2| apply DJ2; cbn; clear -APS AST SPL TOP2; lia]).
    (* [comment removed for export] *)
    eapply evtA_mono.
    { eapply (qc_A AL IMG ALWF CS CSOK) with (p := p) (b1 := b1) (n := n) (ctx := ctx) (T := T) (CTX := CTX) (lo := lo) (TR := SP + -2128 + 16) (size := size);
        first [exact HW02 | exact PCS | exact STKC2 | exact TT2 | exact C82 | exact DS2 | exact TCS | exact CTXCS | exact ST2 | exact LOIMG | exact MI2 | exact T0 | exact CX0 | reflexivity
              | clear -PL; lia | clear -PH; lia | clear -SPL LOIMG; lia | clear -SPL LOIMG SPH; lia | clear -SZB; lia | clear -T1; lia | clear -CX1; lia
              | clear -SPL; lia | clear -SPH; lia | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
              | clear -APS SPL TOP2; lia | clear -AST SPL TOP2; lia | clear -ASC SPL TOP2; lia | clear; lia
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia] ]. }
    cbv beta. (intros ms3 dd_H; ddestruct dd_H as (z14 & z15 & z16 & z17 & m3 & -> & MU3 & WM3 & MI3 & QFR & DS3 & ST3)).
    unfold fsegQ_post, fsegQ_W. cbv zeta.
    assert (DJ3 : forall A k, (A + k <= lo \/ SP + -2128 <= A) -> disjoint_from [(lo, SP + -2128)] A k) by (intros A k H; cbn; clear -H; lia).
    dexists t0', t1', t2', z14, z15, z16, z17, t3', t4', t5', t6', m3, ws, size, fr1, fr2, fr', fd'.
    split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]|].
             2: eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]].
             all: unfold sub_fp, ia_W; cbn [outside app]; clear; intros y Hy; lia. }
    split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|]. split; [exact MI3|].
    Ltac tr23 H MU2 WM2 MU3 WM3 DJ2 DJ3 := eapply rw_cells_transport; [eapply rw_cells_transport; [exact H| exact MU2| exact WM2| apply DJ2]| exact MU3| exact WM3| apply DJ3].
    split. { tr23 FR7 MU2 WM2 MU3 WM3 DJ2 DJ3; cbn; clear -APS AST SPL LOIMG TOP2; lia. }
    split. { eapply rw_cells_transport; [exact STKC2| exact MU3| exact WM3| apply DJ3; cbn; clear; lia]. }
    split. { eapply u64arr_transport; [eapply u64arr_transport; [exact HTR| exact MU2| exact WM2| rewrite HL; apply DJ2]| exact MU3| exact WM3| rewrite HL; apply DJ3]; cbn; clear -APS AST SPL TOP2; lia. }
    split; [exact HL|]. split; [exact SZB|]. split; [exact SZD|].
    split. { tr23 F1800 MU2 WM2 MU3 WM3 DJ2 DJ3; cbn; clear -APS AST SPL TOP2; lia. }
    split. { tr23 TFB MU2 WM2 MU3 WM3 DJ2 DJ3; cbn; clear -APS AST SPL TOP2; lia. }
    split. { tr23 F8 MU2 WM2 MU3 WM3 DJ2 DJ3; cbn; clear -APS AST SPL TOP2; lia. }
    split. { tr23 UNW1 MU2 WM2 MU3 WM3 DJ2 DJ3; cbn; clear -APT AST T0 SPL LOIMG TOP2; lia. }
    split. { eapply rw_cells_transport; [exact HW02| exact MU3| exact WM3| apply DJ3; cbn; clear -APS TOP2; lia]. }
    split. { eapply rw_cells_transport; [exact HW12| exact MU3| exact WM3| apply DJ3; cbn; clear -APS TOP2; lia]. }
    split. { eapply wr_at_transport; [exact WR2| exact WM3]. }
    split. { eapply rw_cells_transport; [exact TST2| exact MU3| exact WM3| apply DJ3; cbn; clear -AST TOP2; lia]. }
    split; [exact QFR|].
    split. { eapply free_statics_transport; [exact FST2| exact MU3| intros A k H; unfold A_IA, A_IA_INIT in H; apply DJ3; clear -H LOIMG; lia| | |]; apply DJ3; clear -CX0 T0 LOIMG AST ASC TOP2; lia. }
    split. { eapply (ia_cells_transport [(lo, SP + -2128); (p + -16, p + -12); (p, p + 8); (T + 2824, T + 2840)] _ _ IAC1); [| eapply wmono_trans; [exact WM2| exact WM3]| |].
             - eapply munch_trans; [exact MU2| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros y Hy; lia.
             - apply DJ2; unfold A_IA; clear -LOIMG PL T0; lia.
             - apply DJ2; unfold A_IA_INIT; clear -LOIMG PL T0; lia. }
    split; [exact ST3|].
    destruct (stk_split asegs m1 (SP + -16) SP (Z.max TOP SP) SR1 ltac:(clear; lia)) as [_ SR1b].
    eapply stk_transport_disjoint; [| exact MU3| exact WM3| cbn; clear; lia].
    eapply stk_transport_disjoint; [exact SR1| exact MU2| exact WM2| apply DJ2; clear -APS AST SPL TOP2; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fsegPC_W (p lo SP T last n : Z) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AW_FreeTop ()) "(<.(3>.$0.$0.)(3?.$0.$0.O5.O4.)(<.(3>.$0.$0.)(3?.$0.$0.O6.(4.O6.+8.))(<.(3>.$0.$0.)(3?.$0.$0.(4.+7???8000.(40.O6.+8.))(4.(4.+7???8000.(40.O6.+8.))(40.(4.O1.+7.)+8.)))(<.(3>.$0.$0.)(3?.$0.$0.(4.O3.+50.)(4.O3.+70.))(<.(3>.$0.$0.)(3?.$0.$0.O2.(4.O2.+2000.))(10.(3>.$0.$0.)))))))")
(* [comment removed for export] *).

  Definition fsegPC_post (SP : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (p n lo T len first last bytes bsize : Z) (elems : list word) (mC : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeTop ()) "Lms',$22.(23.(1=.&40.)Lt0,(1=.&40.)(23.(1=.&40.)Lt1,(1=.&40.)(23.(1=.&40.)Lt2,(1=.&40.)(23.(1=.&40.)La0,(1=.&40.)(23.(1=.&40.)La1,(1=.&40.)(23.(1=.&40.)La2,(1=.&40.)(23.(1=.&40.)La3,(1=.&40.)(23.(1=.&40.)La4,(1=.&40.)(23.(1=.&40.)La5,(1=.&40.)(23.(1=.&40.)La6,(1=.&40.)(23.(1=.&40.)La7,(1=.&40.)(23.(1=.&40.)Lt3,(1=.&40.)(23.(1=.&40.)Lt4,(1=.&40.)(23.(1=.&40.)Lt5,(1=.&40.)(23.(1=.&40.)Lt6,(1=.&40.)(23.P,(1=.&40.)(1>.(1=.&8.))Lm',P,(1=.&40.)(1>.(1=.&8.))(2.(24.$22.R11.(25.(26.O1;.(?.&40.O1<.)O1:.(?.&40.$28.)R10.R?.R>.O19.O18.R=.R<.R;.R:.R9.R8.R7.R6.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.R5.R4.R3.R2.)O=.(41.O1;.)O<.(2;.(1=.&40.))R1.(2<.$:.)))(2.(20.(42.O;.O9.O1<.O8.O5.O:.)O1.R1.)(2.(2>.$:.O1.R1.)(2.(2?.$:.R1.)(2.(3<.$:.R1.O9.O1<.)(2.(38.$:.R1.O;.+8.)(2.(30.$:.R1.(4.+7???8000.(40.O;.+8.))(<.$=.(34.(43.(40.(4.O:.+7.)+8.))(44.(1=.&8.)(?.&8.+?=.)(43.(40.(4.O:.+7.)+8.))))(10.$=.)))(2.(30.$:.R1.(4.O8.+50.)(45.O7.O6.O5.(4.O4.O:.)))(2.(30.$:.R1.O5.(46.=(4.O3.O:.)(4.(47.(33.(1=.&40.)O2.))+1.)))(2.(31.$:.R1.(4.O5.+18.)(48.(1=.&40.)O2.(<.(1=.&40.)(?.&40.(4.O;.-10.))(10.(1=.&40.)))))(38.$:.R1.O5.+2000.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "04V0@L10303239597.1  L11367354891.4  L11367568812.3  L11367586056.4  L11367586059.5  L11367587336.4  L11367587339.7  L11369327115.4  L11369327496.3  L11369458568.4  L11369484986.4  L11369566906.9  L11369622408.4  L12137473770.6  L12137652708.2  L1214218871.3   L1216166900.3   L1216330740.3   L12297272267.21 L13266555807.5  L15515971117.8  L1603916885.4   L1603950677.6   L1603950678.3   L1603952469.4   L1603952470.3   L1605899492.7   L1605981412.3   L1606020566.3   L1606118870.3   L16440599499.13 L16919524597.8  L17410157662.2  L18186559577.6  L18188948954.2  L18641020606.11 L19167748205.8  L19605100823.19 L20526482804.10 L21049500170.6  L22206244445.3  L22206275439.3  L22206324591.8  L22206408285.3  L22206637661.2  L22206638046.3  L22208339934.4  L22208566237.3  L22208566238.6  L22208566493.3  L22208566494.4  L22406284478.4  L22706556426.8  L23062806686.7  L23072471841.0  L24242186978.5  L24481248685.1  L24893985869.10 L25426245911.7  L25426245911.9  L26870639355.8  L26880640045.2  L27695573260.11 L27846297964.3  L28573891711.8  L29026778367.1  L29479579215.7  L29949905540.9  L30523802039.2  L30524034484.4  L30525977655.3  L30526141495.3  L3104208067.4   L31735977102.21 L32165073889.1  L33621614939.7  L33686401973.1  L33948242119.1  L34477945389.1  L34654488613.6  L34654717497.5  L34654767773.4  L34654767774.5  L34654768541.4  L34654768542.7  L34654798238.5  L34656516125.4  L34656516510.5  L34656811037.4  L34656909341.4  L34656928047.4  L34656977199.9  L35442361799.1  L35787266409.5  L35787266409.8  L35787266413.5  L35788968035.8  L35789379437.5  L35789449426.7  L36641975057.5  L36641975058.3  L36642203409.4  L36644134546.3  L36644218784.6  L36644267936.2  L36644298386.3  L36644364462.3  L36684221871.9  L37304452263.1  L38237949960.3  L38313267327.1  L39485528716.6  L39485528719.4  L39485529484.3  L39485529487.3  L39485625996.5  L39487565583.4  L39487729423.4  L40301039690.9  L40440761484.1  L40938924652.1  L41067049570.5  L41596053424.7  L41598150318.7  L42149467270.1  L42155231742.3  L42476413511.1  L42627424012.7  L42627473164.3  L42627504130.3  L42627573310.3  L42627573693.4  L42629370813.6  L42629649922.3  L42629649926.2  L42629649926.6  L42726802815.2  L43865612567.8  L43867762451.3  L43867820204.5  L43868104733.6  L4487909479.8   L4487991399.3   L4488030549.3   L4488128853.3   L4488423638.4   L4488423765.3   L4490121430.4   L4490157013.3   L4490157014.4   L4490157269.3   L4490157270.6   L4490172273.4   L4490402157.6   L4491675308.13  L45142673505.1  L45450656780.1  L45708238342.11 L46532565131.2  L46730492011.7  L47281398381.4  L47886762873.1  L48372115314.4  L48489320647.1  L49182591458.4  L49182591458.5  L49182591458.6  L49182591462.3  L49182591462.7  L49182736477.4  L49182820346.3  L49182837597.4  L49182837598.3  L49182837853.6  L49182837854.3  L49184716893.3  L49184716893.4  L49184717278.2  L49184817388.8  L49184848350.3  L49184866540.3  L49185012190.3  L50097029659.7  L51794544653.3  L52002496404.4  L52412055292.5  L52412068440.5  L52412068443.6  L52412069208.5  L52412069211.8  L52412234075.5  L52412346592.4  L52412346592.7  L52412346596.4  L52412346596.5  L52412346596.6  L52414218456.5  L52414314986.10 L52414316760.5  L52414364138.5  L52414447832.5  L52414447963.6  L54389223275.11 L54500844627.3  L54501089772.7  L54502954095.4  L54502954476.5  L56786826630.8  L57039675053.1  L57628699659.8  L59731263574.3  L59731376359.3  L59731395029.3  L59731425511.8  L59731493333.3  L59733506134.4  L59733668693.3  L59733668694.4  L59733668949.3  L59733668950.6  L59960381164.6  L61028792521.115L61031298166.160L61045092046.21 L61123023741.9  L61536368211.4  L61538482263.6  L61745276307.4  L61745276311.4  L61745276311.7  L61746982045.8  L61747063965.5  L61747424147.4  L61747483692.6  L62391680077.21 L63374621462.116L63374621462.161L63995254982.8  L64146542324.21 L64181499405.21 L65337180824.10 L66552202845.8  L66552284765.4  L66552381779.4  L66554433367.6  L66774298937.3  L67172332582.3  L67172381734.7  L67172748439.3  L67172748564.2  L67172823848.3  L67174627479.6  L67174874412.7  L67267330474.11 L6744778266.5   L67448774383.11 L6744877593.3   L6744877594.5   L6746873753.4   L6747037593.4   L68242401234.3  L68242565074.2  L68354050849.0  L6967678271.0   L7064433807.13  L8658659494.4   L8658822053.2   L8658822309.3   L8658822310.6   L8660750629.3   L8660848933.3   L8746354175.1   L8806423876.8   L902536667.4    L902536667.7    L902536671.4    L902536671.5    L902583392.6    L902763463.5    L902813792.8    L902813795.5    L902815584.6    L902815587.5    L904555616.5    L904556003.4    L904687075.5    L904713425.5    L904762577.10   L904850915.5    L9173359281.11  L9265737838.6   L9267362148.3   L9267444068.7   L9267789418.3   00000400500A00B00C00D00E00F00G00H00I00J00K00\00]00k00l00m01g02402H02I02J02K02L02M02a02b02c02d03703803@03A03G03_04305105C05O05P05Q05R05S05Y05Z05[05\05]05^05_05j06A06U06V06j06n07C07V07n08>08?08S08Z09109509M09d09o0:00:10:20:<0:W0:[0;00;30;70;;0;J0;K0;L0;M0;N0;O0;P0;Q0;R0;S0;T0;U0;V0;Z0;[0;\0;]0<10<20<30<90<:0<;0<<0<=0<C0<D0<E0<`0<d0<h0<l0<m0<n0=;0=<0==0=>0=?0=T0=X0=[0=k0>D0>\0>]0>k0>o0?00?10?20?30?40?50?60?>0?J0?K0?L0?M0?N0?O0?P0?Q0?R0?S0?T0?U0?V0?W0?X0?Y0?Z0?[0?g0@C0@G0@K0@b0@h0@o0A?0AB0AL0AP0AQ0AR0AS0AT0AU0AV0AW0AX0AY0AZ0A[0A\0Ai0Aj0Ak0Al0Am0An0B?0BG0BT0BU0BV0BW0BX0BY0BZ0B[0B\0B]0Bm0Bn0Bo0C00C10C20C30C40CB0CM0CN0CO0CP0CS0CW0Cn0D80D90D:0D;0D<0D=0D>0D?0D@0DA0DZ0E50EP0Ek0F;0F<0FK0FL0FM0FN0Fb0Fc0Fd0Fe0G>0GY0H40H70HM0Hf0I>0I?0I@0IA0IP0IQ0IR0IS0I]0I^0I_0I`0Ia0Ik0Il0JD0JE0JR0JS0JT0JU0J_0J`0Ja0KA0KB0KM0KN0KO0KP0KQ0KU0Kl0Km0Kn0Ko0L<0L=0L>0L?0L@0LA0LB0LC0LD0LE0LF0LG0LH0L[0M40M50M60M7S2SPFS1T4last3ALTFFFFFFFFFFS3hAR1p1n1k2PH2KBFS3hAR4last3LA1FFS3hAR2SP1p1n2lo1T3CTX1k3PHI2T02T13CX13APT3APC5LOIMG3SPL2KBS2SP2lo1A1j1HS2SP1p1n2lo1k3APS2KBFFFFFS3hAR1p1n1k2PL2PH2KBFFFS4last5elems3LHI2ELFS3len2L0FS1T2T0S3hAR2SP1p2lo1k5LOIMG2SRS2SP1p1n2lo1k3APS2KBS3hAR2SP1p1n2lo1T4last1k3APS3AST3ASL5LOIMG3SPL2KB2SR1A1j2H12H2S3hAR1p1T1k3THI2SRS3hAR1p1k2PHFFFFS1T2T0FFFFFFS1n2NB1H2H0S2SP1p2lo1T4last1k1y2HyS2SP2lo4last3ASL3SPLSS1n5bytes2NB3BY03BY1S2SPS3hAR1p4last1k3LHI2SRS2SP1p2lo1A1j2H12H2S2SP1p2lo1k2SR1A1j2H12H2S3hAR1p2PL1A1j1HFS1p1n1T1k3THI3APT2KBS2SP2loS2SP1p2lo1T4last1k1y2HyS2SPS3hAR2SP1p2lo1k5LOIMG2SRS3hAR2SP2lo5LOIMG1A1j1HS5bytes3BY0FFFS1p1n1k2KBS3hAR1p1n1T3CTX1k2T03APC2KBS2SPS3hAR1p1n1k2PH3PHI2KBS1TS2SPS2SPS3hAR2SP2lo3SPLFFFFFFFFFFFFS2SPFFFS2SP1p1n2lo1k3APS2KBFFS1n2NBFFFFS1n2NBFFS2SP2lo1T4last1A1j2H12H22H3S2SPS2loS2SPFFS1n5bsize3BS1FFFFS3hAR1p1k2PH3PHI1H2H0S2SPS1pS2SP2lo4last3ASLS2SP2lo4last5elems2EL3ASLS3hAR2SP1p2lo1k5LOIMG2SRFS3hAR2lo5LOIMGS2SPFFFFFFFS2SP3SPHS3hAR2SP3SPHFFFFFFFFFFFFFFFFFS3hAR2SP3SPHS1p1n4last5elems1k2EL3ALP2KBS2SPS2SPS2SP1n2lo4last1k3ASL2KBS1p2PLS2SP2loS2SP2lo4last3ASLS1TS1p1n1k2KBS2SPFFFFFFFFFFFFS3hAR1T2T02T1FFFFFS2SP2lo1T3AST3SPLS1n1k2KBS2SP2lo1T3ASTFFFFFFFFFS2SP2lo4last3ASLFFFFFFFS1n1T1k3THI2KBS2SP2lo3SPLFFFS1pS2SPS2SP1p2lo1T4last1k1y2HyS3hAR1T2T1FFFFFFFFFS2SP2lo4last5elems2EL3ASLS3hAR2SP1p1n5elems2ws2EL2HLS3hAR2SP1p1n5elems2ws2EL2HLS3hAR1p1n1T3CTX1k2T03APC2KBS3hAR1p1k2PH3PHIFS3hAR2SP2lo3SPLFFFS2SP1p1n2lo1k3APS2KBFFFS3hAR2SP2lo3CTX3CX15LOIMGS3hAR2SP1p1n5elems2ws2EL2HLS3hAR2SP1p1n5elems2ws2EL2HLS1pS3hAR2SP2lo1T2T15LOIMGS3hAR2SP2lo3CTX3CX15LOIMGS3hAR2SP1p2lo1k2PH5LOIMGFFFS3hAR2SP2lo3SPLFFFS3hAR1T2T1FFFFS4last3LHIFS2SP1n2lo1T1k3THI3AST2KBFS1n5bytes3BY1FFFS5first2F0SSS2SP1n2lo4last5elems1k2EL3ASL2KBFS5bsize3BS0FFFFS2SPS2SP1p2lo1T4last1k1y2HyFFFS2SP2lo1T3ASTFFFFFFFFFFFFS1p1n4last1k3ALP2KBS3hAR2SP2lo5LOIMG3SPL3SPHFFF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma fsegPC : ltac2:(CDefT.buildp (gd_tbl_AW_FreeTop ()) "Pgp,(1=.&40.)Pt0,(1=.&40.)Pt1,(1=.&40.)Pt2,(1=.&40.)Pidw,(1=.&40.)Pa1,(1=.&40.)Pa2,(1=.&40.)Pa3,(1=.&40.)Pa4,(1=.&40.)Pa5,(1=.&40.)Pa6,(1=.&40.)Pa7,(1=.&40.)Ps6,(1=.&40.)Ps7,(1=.&40.)Ps8,(1=.&40.)Ps9,(1=.&40.)Ps10,(1=.&40.)Ps11,(1=.&40.)Pt3,(1=.&40.)Pt4,(1=.&40.)Pt5,(1=.&40.)Pt6,(1=.&40.)Pra,(1=.&40.)Ps0,(1=.&40.)Ps1,(1=.&40.)Ps2,(1=.&40.)Ps3,(1=.&40.)Ps4,(1=.&40.)Ps5,(1=.&40.)PSP,$0.Pp,$0.Pb1,$0.Pn,$0.Pctx,$0.Plo,$0.PT,$0.PCTX,$0.Plen,$0.Pfirst,$0.Plast,$0.Pbytes,$0.Pbsize,$0.Psize,$0.Pelems,(1;.(1=.&40.))Pws,(1;.(1=.&40.))Pjunk,(1;.(1=.&8.))Pfr1,(1;.(1=.&8.))Pfr2,(1;.(1=.&8.))PF,(49.&5.(1=.&40.))Pfc,(1=.&20.)PmC,P,(1=.&40.)(1>.(1=.&8.))ZSTK,$0.(4.R16.-850.)Zk,$0.(40.(4.R14.+7.)+8.)P,(3.(4.+65?000.+10.)R17.)P,(3.(4.R18.(4:.+8.R2.))(4;.VhAR,))P,(24.$0.(4<.R19.+10.)=)P,(2.(3.=R18.)(3.R18.(4=.+2.+1<.)))P,(3.+10007???8008.R1;.)P,(2.(2.(3.+1000.R17.)(1.(3.(4.R17.+1000.)+10000.)(3.+65?000.R17.)))(1.(3.(4.R17.+1000.)+7???7000.)(3.+10007???8000.R17.)))P,(3.+10007???8000.R14.)P,(2.(3.+1000.R19.)(1.(3.(4.R19.+1000.)+10000.)(3.+65?000.R19.)))P,(3.(4.R1:.+1000.)(4;.VhAR,))P,(3.+65?000.R1:.)P,(3.(4.R1;.+10000.)(4;.VhAR,))P,(30.$:.R>.(4.R22.-10.)(36.R21.+3.))P,(30.$:.R?.(4.R23.-<.)(37.R21.R20.))P,(38.$:.R10.R24.+8.)P,(4>.VCS,(4.R25.-10.)(4.+18.(4:.+8.R?.)))P,(30.$:.R12.(4.+7???8000.(40.R26.+8.))(<.$=.(34.(43.R10.)R17.)(10.$=.)))P,(30.$:.R13.(4.R12.-30.)(<.$=.(>.(?.&40.R12.))(<.$=.(>.(?.&40.+1.))(<.$=.(>.(?.&40.$39.))(<.$=.(>.(?.&40.R27.))(<.$=.(>.(?.&40.R28.))(<.$=.(>.(?.&40.$3:.))(10.$=.))))))))P,(1?.R14.R23.R22.)P,(4>.VCS,R24.+1000.)P,(2.(3.+1.R23.)(4?.R23.(4=.+2.+3?.)))P,(2.(3.=R23.)(4?.R23.(4=.+2.+40.)))P,(3.+65?000.R23.)P,(3.(4.R24.+2000.)(4;.VhAR,))P,(3.=R24.)P,(3.(4.R25.R2=.)$15.)P,(3.=R25.)P,(4?.(4.R26.R2?.)(4=.+2.+3?.))P,(50.(33.(1=.&40.)R25.)#3?=.)P,(30.$:.R1?.(4.R2>.+50.)(45.R2<.R2;.R2:.R29.))P,(30.$:.R20.R2;.(46.=R29.(47.(33.(1=.&40.)R27.))))P,(31.$:.R21.(4.R2<.+18.)R28.)P,(38.$:.R22.R2=.+2000.)P,(4>.VCS,R2>.+2000.)P,(1.(3.(4.R33.+1000.)R2?.)(3.(4.R2?.+2000.)R33.))P,(1.(3.(4.(4.R39.+8.)(4:.+8.R23.))R30.)(3.(4.R30.+2000.)(51.R39.+10.)))P,(1.(3.(4.R35.+1000.)(51.R3:.+10.))(3.(4.(4.R3:.+8.)(4:.+8.R24.))R35.))P,(1.(3.(4.R35.+10000.)(51.R3;.+10.))(3.(4.R3;.+8.)R35.))P,(1.(3.R3=.R36.)(3.(4.R36.+10000.)R38.))P,(30.$:.R29.(4.R3>.-38.)(<.$=.(>.R3?.)(<.$=.(>.R40.)(<.$=.(>.R41.)(<.$=.(>.R42.)(<.$=.(>.R43.)(<.$=.(>.R44.)(<.$=.(>.R45.)(10.$=.)))))))))P,(30.$:.R2:.R29.(<.$=.(>.(?.&40.(4.R29.+10.)))(<.$=.(>.(?.&40.R32.))(10.$=.))))P,(31.$:.R2;.(4.R2:.+10.)R31.)P,(24.$32.(33.(1=.&40.)R32.)#1>.)P,(30.$:.R2=.(4.R2<.+100.)(<.$=.(34.#708.R31.)(10.$=.)))P,(30.$:.R2>.(4.R2=.+808.)(<.$=.(>.(?.&40.R43.))(10.$=.)))P,(30.$:.R2?.(4.R2>.+810.)(<.$=.(34.#8.R32.)(10.$=.)))P,(1.(3.R45.(51.R44.+10.))(3.(4.(4.R44.+8.)(4:.+8.R2>.))R40.))P,(1.(3.R46.R40.)(3.(4.R40.+1000.)R41.))P,(1.(3.R47.R3=.)(3.(4.R3=.+2000.)R42.))P,(3<.$:.R33.R43.(4.R32.-30.))P,(3.(4;.VhAR,)R44.)P,(3.R45.(51.R4:.+1000.))P,(3.R4;.(4=.+2.+3>.))P,(24.$0.(4<.R4<.+10.)=)P,(4>.VCS,R48.(51.R4=.R48.))P,(2?.$:.R39.)(52.$:.VAL,VCS,(53.R4?.R56.R6<.R55.R54.R53.R52.R51.R50.R60.R5?.R5>.R5=.R5<.R5;.R3<.R3;.R4>.R4<.R4:.R49.R47.R46.R45.R44.R43.R41.R3:.)(25.(26.(?.&40.$27.)(?.&40.(4.R39.-30.))R6<.(?.&40.$28.)R6;.R6:.R69.(?.&40.(4.R4>.-10.))(?.&40.R39.)R68.R67.R66.R65.R64.R63.R62.R61.(?.&40.$29.)(?.&40.=)(?.&40.R49.)(?.&40.(4.R4?.-51.))R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.)R3<.(?.&40.$27.)R3;.(2;.(1=.&40.))R3:.(2<.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros gp t0 t1 t2 idw a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 SP p b1 n ctx lo T CTX len first last bytes bsize size elems ws junk fr1 fr2
      F fc mC STK k PL PH PA NB PHI THI LHI T0 T1 CX0 CX1 HW0 HW1 WR PCS SH QFR FST TCS L0 F0 LA0 LA1 BY0 BY1 BS0 BS1 EL QC BH BE BW BCS ALT ALP APT APC ASC
      FR7 STKC HTR HL F1800 TFB F8 APS AST ASL ST LOIMG SPL SPH SPA SCS MI.
    assert (HK : k = (n + 7) / 8) by reflexivity. clearbody k. subst STK.
    assert (KB : 0 <= k /\ 8 * k < n + 8 + 8) by (rewrite HK; pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); clear -H H0 NB; lia).
    dpose FST as (MS8 & MF & TT & C8' & QM & GF & FL & PS).
    assert (STAL : (SP + -2128) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, SPA; reflexivity).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (qc_B AL IMG ALWF CS CSOK) with (p := p) (b1 := b1) (n := n) (ctx := ctx) (T := T) (lo := lo) (STK := SP + -2128) (m0 := mC);
        first [exact HW0 | exact HW1 | exact WR | exact QFR | exact ST | exact LOIMG | exact MI | exact T0 | apply munch_refl | apply wmono_refl
              | eapply crange_sub; [exact PCS| clear; lia| clear -KB; lia]
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -PL; lia | clear -PH KB; lia | clear -NB; lia | clear -SPL LOIMG SPH; lia | clear -T1; lia | clear -SPL; lia | clear -SPH; lia
              | clear -APS SPL KB; lia ]. }
    cbv beta. (intros ms1 dd_H; ddestruct dd_H as (y16 & y17 & m1 & -> & MU1 & WM1 & MI1 & WR1 & ST1)).
    assert (DJ1 : forall A j, (A + j <= lo \/ SP + -2128 <= A) -> (A + j <= p \/ p + 8 <= A) -> disjoint_from [(lo, SP + -2128); (p, p + 8)] A j) by (intros A j H1 H2; cbn; clear -H1 H2; lia).
    assert (FST1 : free_statics m1 T CTX).
    { eapply free_statics_transport; [exact FST| exact MU1| intros A j H; unfold A_IA, A_IA_INIT in H; apply DJ1; clear -H LOIMG PL; lia| | |]; apply DJ1; clear -CX0 CX1 T0 T1 AST ASC APT APC SPL LOIMG PL PHI KB; lia. }
    dpose FST1 as (_ & _ & _ & _ & QM1 & GF1 & FL1 & PS1).
    Ltac tr1 H MU WM DJ := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ].
    assert (HW01 : rw_cells asegs m1 (p + -16) (hdr_w0 b1 3)) by (tr1 HW0 MU1 WM1 DJ1; cbn; clear -APS SPL KB; lia).
    assert (HW11 : rw_cells asegs m1 (p + -12) (hdr_rest n ctx)) by (tr1 HW1 MU1 WM1 DJ1; cbn; clear -APS SPL KB; lia).
    assert (SH1 : rw_cells asegs m1 (0x7fff8000 + p / 8) [CB (Z.to_nat k) junk]).
    { tr1 SH MU1 WM1 DJ1; cbn; rewrite ?Nat.add_0_r; rewrite Z2Nat.id by (clear -KB; lia); clear -PHI PH KB LOIMG; lia. }
    (* [comment removed for export] *)
    eapply evtA_cut.
    { rewrite HK in SH1.
      eapply (put_A AL IMG ALWF CS CSOK ASB) with (p := p) (b1 := b1) (n := n) (ctx := ctx) (T := T) (lo := lo) (STK := SP + -2128) (junk := junk);
        first [exact HW01 | exact HW11 | exact SH1 | exact QM1 | exact GF1 | exact FL1 | exact PS1 | exact ST1 | exact LOIMG | exact MI1 | exact PA | exact NB | exact T0 | exact STAL
              | rewrite <- HK; eapply crange_sub; [exact PCS| clear; lia| clear -KB; lia]
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -PL; lia | rewrite <- HK; clear -PH KB; lia | clear -SPL LOIMG SPH; lia | clear -T1; lia
              | right; clear -PHI PH KB; lia | clear -SPL; lia | clear -SPH; lia | rewrite <- HK; clear -APS SPL KB; lia ]. }
    cbv beta zeta. (intros ms2 dd_H; ddestruct dd_H as (x5 & x6 & x7 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & -> & MU2 & WM2 & MI2 & PFR2 & SHF2 & PS2 & ST2)).
    rewrite <- HK in MU2, SHF2.
    assert (SR : 0x20008fff001 <= 0x7fff8000 + p / 8 /\ 0x7fff8000 + p / 8 + k <= 0x10007fff0000).
    { pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). clear -H H0 PHI PH KB. lia. }
    assert (DJ2 : forall A j, (A + j <= lo \/ SP + -2128 <= A) -> (A + j <= 0x7fff7000 \/ 0x10007fff0000 <= A) -> disjoint_from [(lo, SP + -2128); (0x7fff8000 + p / 8, 0x7fff8000 + p / 8 + k)] A j)
      by (intros A j H1 H2; cbn; clear -H1 H2 SR; lia).   (* [comment removed for export] *)
    assert (DJ12 : forall A j, (A + j <= lo \/ SP + -2128 <= A) -> (A + j <= p \/ p + 8 <= A) -> (A + j <= 0x7fff7000 \/ 0x10007fff0000 <= A) ->
                   disjoint_from [(lo, SP + -2128); (p, p + 8)] A j /\ disjoint_from [(lo, SP + -2128); (0x7fff8000 + p / 8, 0x7fff8000 + p / 8 + k)] A j).
    { intros A j H1 H2 H3. split; [apply DJ1; assumption| apply DJ2; assumption]. }
    Ltac tr12 H MU1 WM1 MU2 WM2 DJ12 tac :=
      let D := fresh "D" in
      unshelve (epose proof (DJ12 _ _ _ _ _) as D); [| | | | | destruct D as [?D1 ?D2];
        eapply rw_cells_transport; [eapply rw_cells_transport; [exact H| exact MU1| exact WM1| exact D1]| exact MU2| exact WM2| exact D2]]; tac.
    assert (QC2 : rw_cells asegs m2 (T + 80) (qc_cells len first last bytes)).
    { eapply rw_cells_transport; [eapply rw_cells_transport; [exact QC| exact MU1| exact WM1|]| exact MU2| exact WM2|];
        [apply DJ1| apply DJ2]; cbn; clear -AST APT SPL THI KB; lia. }
    assert (BH2 : rw_cells asegs m2 last (batch_hdr 0 bsize (Z.of_nat (length elems)))).
    { eapply rw_cells_transport; [eapply rw_cells_transport; [exact BH| exact MU1| exact WM1|]| exact MU2| exact WM2|];
        [apply DJ1| apply DJ2]; cbn; clear -ASL ALP SPL LHI KB; lia. }
    assert (BE2 : u64arr asegs m2 (last + 24) elems).
    { eapply u64arr_transport; [eapply u64arr_transport; [exact BE| exact MU1| exact WM1|]| exact MU2| exact WM2|];
        [apply DJ1| apply DJ2]; cbn; clear -ASL ALP SPL LHI KB EL; lia. }
    assert (BW2 : wr_at asegs m2 last 8192) by (eapply wr_at_transport; [eapply wr_at_transport; [exact BW| exact WM1]| exact WM2]).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (enq_append AL IMG ALWF CS CSOK) with (C := T + 80) (len := len) (first := first) (last := last) (bytes := bytes) (bsize := bsize) (n := n) (cb := p + -16) (lo := lo) (elems := elems) (CACHE := T + 208);
        first [exact QC2 | exact BH2 | exact BE2 | exact BW2 | exact BCS | exact EL | exact ST2 | exact LOIMG | exact MI2 | exact LA0
              | eapply crange_sub; [exact TCS| clear; lia| clear; lia]
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -L0; lia | clear -F0; lia | clear -LA1; lia | clear -BY0; lia | unfold kQuarantineCache in BY1; clear -BY0 BY1 NB; lia | clear -BS0; lia | clear -BS1; lia | clear -NB; lia
              | clear -PL PH KB; lia | clear -T1; lia | clear -T0; lia | clear -ALT; lia | clear -SPL LOIMG SPH; lia | clear -SPL; lia | clear -SPH; lia
              | clear -AST SPL; lia | clear -ASL SPL; lia | clear -T0 T1; lia ]. }
    cbv beta. (intros ms3 dd_H; ddestruct dd_H as (z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & m3 & -> & MU3 & WM3 & MI3 & QC3 & BH3 & BE3 & BW3 & ST3)).
    replace (ret_pc (Z_to_bv 64 A_QPUT_RA1)) with (Z_to_bv 64 A_QPUT_RA1) by (unfold A_QPUT_RA1; symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    assert (DJ3 : forall A j, (A + j <= lo \/ SP + -2128 + -80 <= A) -> (A + j <= T + 80 \/ T + 112 <= A) -> (A + j <= last \/ last + 8192 <= A) ->
                  disjoint_from [(lo, SP + -2128 + -80); (T + 80, T + 80 + 32); (last, last + 8192)] A j) by (intros A j H1 H2 H3; cbn; clear -H1 H2 H3; lia).
    assert (PFR3 : put_frame m3 (SP + -2128) T (SP + -2128) s6 (Z_to_bv 64 (SP + -81)) (Z_to_bv 64 (SP + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 A_PC_FREE) (Z_to_bv 64 p) (Z_to_bv 64 SP) (Z_to_bv 64 A_FREE_RA2)).
    { unfold put_frame in *. eapply rw_cells_transport; [exact PFR2| exact MU3| exact WM3| apply DJ3; cbn; clear -AST ASL SPL; lia]. }
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (put_B_ret AL IMG ALWF CS CSOK) with (T := T) (bytes := bytes + n) (lo := lo) (m0 := m3) (W := []) (p := p) (n := n) (STK := SP + -2128);
        first [exact QC3 | exact TCS | exact PFR3 | exact ST3 | exact LOIMG | exact MI3 | apply munch_refl | apply wmono_refl
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -BY0 BY1 NB; lia | clear -T0; lia | clear -T1; lia | clear -SPL; lia | clear -SPH; lia ]. }
    cbv beta. (intros ms4 dd_H; ddestruct dd_H as (w10 & m4 & -> & MU4 & WM4 & MI4 & QC4 & ST4)).
    replace (ret_pc (Z_to_bv 64 A_FREE_RA2)) with (Z_to_bv 64 A_FREE_RA2) by (unfold A_FREE_RA2; symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    (* [comment removed for export] *)
    assert (MU14 : munch [(lo, SP + -2128); (p, p + 8); (0x7fff8000 + p / 8, 0x7fff8000 + p / 8 + k); (T + 80, T + 112); (last, last + 8192)] mC m4).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]|]. 2: eapply munch_trans; [eapply munch_weaken; [| exact MU2]|].
      3: eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU4]].
      all: unfold sub_fp; cbn [outside]; clear; intros y Hy; lia. }
    pose proof (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 WM4))) as WM14.
    assert (DJ4 : forall A j, SP + -2128 <= A -> A + j <= SP -> disjoint_from [(lo, SP + -2128); (p, p + 8); (0x7fff8000 + p / 8, 0x7fff8000 + p / 8 + k); (T + 80, T + 112); (last, last + 8192)] A j).
    { intros A j H1 H2. cbn. clear -H1 H2 APS AST ASL SR SPL LOIMG KB. lia. }
    assert (CSJ : rw_cells asegs m4 (SP + -2128) ([C8 (Z_to_bv 64 (SP + -2128 + 16)); C8 (Z_to_bv 64 size)] ++ [CB 240 (u64s ws)] ++ [CB 1800 fr1] ++ [C8 (Z_to_bv 64 SP)] ++ [CB 8 fr2])).
    { apply (proj2 (rw_cells_app asegs m4 _ _ _)). split; [eapply rw_cells_transport; [exact STKC| exact MU14| exact WM14| apply DJ4; cbn; clear; lia]|].
      cbn [cells_size csize Nat.add]. apply (proj2 (rw_cells_app asegs m4 _ _ _)). split.
      { replace (SP + -2128 + Z.of_nat 16) with (SP + -2128 + 16) by (clear; lia).
        replace 240%nat with (length (u64s ws)) by (rewrite u64s_length, HL; reflexivity).
        apply rw_cells_of_u8arr. destruct HTR as [HB HW']. split.
        - eapply bytes_at_transport; [exact HB| exact MU14| apply DJ4; [cbn; clear; lia| rewrite u64s_length, HL; cbn; clear; lia]].
        - rewrite u64s_length, HL. cbn [Nat.mul Z.of_nat]. eapply wr_at_transport; [| exact WM14]. rewrite HL in HW'. exact HW'. }
      cbn [cells_size csize Nat.add]. apply (proj2 (rw_cells_app asegs m4 _ _ _)). split.
      { replace (SP + -2128 + Z.of_nat 16 + Z.of_nat 240) with (SP + -2128 + 256) by (clear; lia).
        eapply rw_cells_transport; [exact F1800| exact MU14| exact WM14| apply DJ4; cbn; clear; lia]. }
      cbn [cells_size csize Nat.add]. apply (proj2 (rw_cells_app asegs m4 _ _ _)). split.
      { replace (SP + -2128 + Z.of_nat 16 + Z.of_nat 240 + Z.of_nat 1800) with (SP + -2128 + 2056) by (clear; lia).
        eapply rw_cells_transport; [exact TFB| exact MU14| exact WM14| apply DJ4; cbn; clear; lia]. }
      cbn [cells_size csize Nat.add].
      replace (SP + -2128 + Z.of_nat 16 + Z.of_nat 240 + Z.of_nat 1800 + Z.of_nat 8) with (SP + -2128 + 2064) by (clear; lia).
      eapply rw_cells_transport; [exact F8| exact MU14| exact WM14| apply DJ4; cbn; clear; lia]. }
    cbn [app] in CSJ.
    assert (FR7' : rw_cells asegs m4 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FR7| exact MU14| exact WM14| apply DJ4; cbn; clear; lia]).
    (* [comment removed for export] *)
    eapply evtA_mono.
    { eapply (free_epi AL IMG ALWF CS CSOK) with (lo := lo) (m0 := m4) (W := []) (csj := _);
        first [exact CSJ | exact FR7' | exact ST4 | exact MI4 | exact SPL | exact SPH | exact SCS | apply munch_refl | apply wmono_refl | cbn; clear; lia | clear -LOIMG; lia]. }
    cbv beta. (intros ms5 dd_H; ddestruct dd_H as (m5 & -> & MU5 & WM5 & MI5 & ST5)).
    unfold fsegPC_post, fsegPC_W. rewrite <- HK.
    assert (DJ5 : forall A j, (A + j <= lo \/ SP <= A) -> disjoint_from [(lo, SP)] A j) by (intros A j H; cbn; clear -H; lia).
    deexists 16. split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU14]| eapply munch_weaken; [| exact MU5]]; unfold sub_fp; cbn [outside]; clear; intros y Hy; lia. }
    split; [eapply wmono_trans; [exact WM14| exact WM5]|]. split; [exact MI5|]. split; [exact ST5|].
    split. { eapply wr_at_transport; [exact WR1| eapply wmono_trans; [exact WM2| eapply wmono_trans; [exact WM3| eapply wmono_trans; [exact WM4| exact WM5]]]]. }
    split. { eapply rw_cells_transport; [| exact MU5| exact WM5| apply DJ5; cbn; rewrite ?Nat.add_0_r; rewrite Z2Nat.id by (clear -KB; lia); clear -SR LOIMG; lia].
             eapply rw_cells_transport; [| exact MU4| exact WM4| cbn; rewrite ?Nat.add_0_r; rewrite Z2Nat.id by (clear -KB; lia); clear -SR LOIMG; lia].
             eapply rw_cells_transport; [exact SHF2| exact MU3| exact WM3| apply DJ3; cbn; rewrite ?Nat.add_0_r; rewrite Z2Nat.id by (clear -KB; lia); clear -SR LOIMG THI LHI; lia]. }
    split. { eapply rw_cells_transport; [exact QC4| exact MU5| exact WM5| apply DJ5; cbn; clear -AST; lia]. }
    split. { eapply rw_cells_transport; [| exact MU5| exact WM5| apply DJ5; cbn; clear -ASL; lia]. eapply rw_cells_transport; [exact BH3| exact MU4| exact WM4| cbn; clear -ASL SPL; lia]. }
    split. { eapply u64arr_transport; [| exact MU5| exact WM5| apply DJ5; rewrite app_length; cbn; clear -ASL EL; lia]. eapply u64arr_transport; [exact BE3| exact MU4| exact WM4| rewrite app_length; cbn; clear -ASL SPL EL; lia]. }
    eapply wr_at_transport; [exact BW3| eapply wmono_trans; [exact WM4| exact WM5]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End FreeTop.

End ARUN_1.
