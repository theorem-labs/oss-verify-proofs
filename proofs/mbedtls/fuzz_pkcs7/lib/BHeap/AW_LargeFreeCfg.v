(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux SysStep ITree Nodes CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_Munmap AW_Poison AKinv AJ AKinvS.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_LargeFree AW_MunmapCfg AW_PoisonBig AW_PoisonBigCfg.
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
Ltac2 gd_tbl_AW_LargeFreeCfg () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PoisonBig.rsmr_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "ARUN_1.fine_dj"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.dealloc_statics"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_ok"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "ARUN_1.LargeFreeS.lfree_W"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MunmapCfg.wmono_out"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_LargeFree.sec_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "ARUN_1.LargeFreeS.lfree_postS"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_SECONDARY"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_GSTATS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_LargeFree.A_LARGE_DEALLOC"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
Definition fine_dj (W : list (Z * Z)) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_LargeFreeCfg ()) "PA,$0.Pn,$0.P,(1.(2.+10000.R2.)(2.(3.R2.R1.)+65?000.))P,(4.(2.(3.R3.R2.)$5.)(2.(3.$5.+400.)R3.))(6.O1.R4.R3.)")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00J0>L17549674556.7L17777781185.7L20583978428.7L2264976833.7 L22761163201.7L2512799164.7 L2744849857.7 L31337033148.7L35381852865.7L35609843644.7L38607238588.7L42691365057.7L46296054972.7L47860165057.7L4881649852.7 L49858367676.7L50493781948.7L51175578817.7L51457123260.7L53929369025.7L55367386044.7L60516989633.7L60606824897.7L61032755649.7L6572142529.7 L66318469308.700000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00H00I00JSSSSSSSSSSSSSSSSSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma poison_statics_transport_fine : forall W m m', poison_statics m -> munch W m m' -> fine_dj W -> poison_statics m'.
Proof.
  intros W m m' PS MU DJ. unfold poison_statics, fine_dj in *.
  unfold A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND,
    A_GOT_RMEMSET, A_RMEMSET, A_GOT_CFLAGS, A_CF_CSMT, A_INSTANCE in *.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- ro_cells _ _ ?A ?cs => eapply (ro_cells_transport asegs W m m' A cs); [tauto| exact MU| apply DJ; cbn; lia] end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00H0?L10579418300.10L10929582012.10L11719062972.10L14671900604.10L16698408897.10L17191430593.10L18528503233.10L19398363745.10L2512799164.10 L27343969340.10L2744849857.10 L29548733889.10L31156355521.10L35514826684.10L39440686273.10L49471825340.10L50406959553.10L55756488764.10L6057522108.10 L61360268737.10L62348091585.10L67892477889.10L67982786620.10L8345721020.10 00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00HSSSSSSSSSSSSSSSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma rsmr_statics_transport_fine : ltac2:(CDefT.buildp (gd_tbl_AW_LargeFreeCfg ()) "PW,(7.$8.)Pm,P,(9.&40.)(:.(9.&8.))Pm',P,(9.&40.)(:.(9.&8.))Pcan,(9.&40.)Pdd,(9.&8.)Pmadv,(9.&8.)P,(;.R5.R3.R2.R1.)P,(<.R7.R6.R5.)P,(=.R8.)(;.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' can dd madv RS MU DJ. unfold rsmr_statics, fine_dj in *.
  unfold A_GOT_CANARY, A_CANARY, A_LIBC_PAGESZ, A_GOT_CFLAGS, A_MMAP_LIMIT, A_CF_DONTDUMP, A_GOT_SEALED2, A_GOT_PAGESZ, A_PAGESZ_CELL,
    A_GOT_DYING, A_DYING, A_MADV_FLAG, A_INSTANCE in *.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- ro_cells _ _ ?A ?cs => eapply (ro_cells_transport asegs W m m' A cs); [tauto| exact MU| apply DJ; cbn; lia] end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section LargeFreeS.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L11775733171.20L14352582248.20L29413246008.20L31158452686.20L39118842533.20L40827225943.20L4438116814.20 L49370938574.20L6059619251.20 L65985263795.2000000100200300400900:00;00<00=00>SSFSS3CTXSSSSS". (* [comment removed for export] *)
  #[using="Type"] Lemma dealloc_statics_transport_fine : ltac2:(CDefT.buildp (gd_tbl_AW_LargeFreeCfg ()) "PW,(7.$8.)Pm,P,(9.&40.)(:.(9.&8.))Pm',P,(9.&40.)(:.(9.&8.))PT,$0.PCTX,$0.P,(>.R4.R2.R1.)P,(<.R6.R5.R4.)P,(=.R7.)P,PA,$0.Pn,$0.P,(1.(2.R6.R2.)(2.(3.R2.R1.)(3.R6.+10000.)))(6.R;.R3.R2.)(>.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    (intros W m m' T CTX dd_H; ddestruct dd_H as (H1 & H2 & H3 & H4 & H5); intros MU DJ DJC). unfold dealloc_statics, fine_dj in *.
    unfold A_MFHOOKS, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_INSTANCE in *.
    repeat split; (eapply ro_cells_transport; [eassumption| exact MU| first [apply DJ; cbn; lia | apply DJC; cbn; lia]]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (h ms sz idx : Z).
  Let p := h + 4096.
  Let S := 0x7fff8000 + h / 8.
  Let k := ms / 8.
  Variables (K Kd : Model -> Prop).
  Hypothesis KL : kinv AL CS K.
  (* [comment removed for export] *)
  Variable CS' : Z -> Prop.
  Hypothesis CSOK' : cs_ok AL CS'.
  Hypothesis KdL : kinv AL CS' Kd.
  Hypothesis HAS : ltac2:(CDefT.buildp (gd_tbl_AW_LargeFreeCfg ()) "Pmo,$?.P,A1.VK,R1.(10.$11.(12.(13.(14.R2.))(15.&40.Vh,)(15.&40.(16.Vms,)))$17.)")
(* [comment removed for export] *).
  Hypothesis T_unmap : forall mo, K mo -> Kd (munmap_model h (page_round_up_Z ms) mo).
  (* [comment removed for export] *)
  Variables (can : word) (dd madv : byte).
  Hypothesis POISON : poison0_siteS CS K h ms can dd madv.
  (* [comment removed for export] *)
  Let PB := rmp_PB S.
  Let PE := rmp_PE (S + k).
  Hypothesis HASM : ltac2:(CDefT.buildp (gd_tbl_AW_LargeFreeCfg ()) "Pmo,$?.P,A1.VK,R1.P,(18.VPB,VPE,)(10.$11.(19.(14.R3.)(15.&40.VPB,)(15.&40.(1:.VPE,VPB,)))$17.)")
(* [comment removed for export] *).
  Hypothesis T_madv : forall mo, K mo -> PB < PE -> K (madvise_model PB (PE - PB) mo).
  (* [comment removed for export] *)
  Hypothesis NOROM : forall x : word, PB <= bv_unsigned x < PE -> ro_addr asegs x = false.

  Definition lfree_W (lo SP PA last T : Z) : list (Z * Z) :=
    ldA_W lo SP PA idx last ++ [(T + 2888, T + 2904); (S, S + k); (h, h + ms)].

  Definition lfree_postS (SP : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (PA nres n last lms lsz T lo : Z) (bases : list Z) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_LargeFreeCfg ()) "Lc,$1;.(1<.$1=.Lms',$1=.(1<.$?.Lmo',$?.(1<.(9.&40.)Lt0,(9.&40.)(1<.(9.&40.)Lt1,(9.&40.)(1<.(9.&40.)Lt2,(9.&40.)(1<.(9.&40.)La0,(9.&40.)(1<.(9.&40.)La1,(9.&40.)(1<.(9.&40.)La2,(9.&40.)(1<.(9.&40.)La3,(9.&40.)(1<.(9.&40.)La4,(9.&40.)(1<.(9.&40.)La5,(9.&40.)(1<.(9.&40.)La6,(9.&40.)(1<.(9.&40.)La7,(9.&40.)(1<.(9.&40.)Lt3,(9.&40.)(1<.(9.&40.)Lt4,(9.&40.)(1<.(9.&40.)Lt5,(9.&40.)(1<.(9.&40.)Lt6,(9.&40.)(1<.(9.&40.)Lnfr',(9.&40.)(1<.(9.&40.)Lcal',(9.&40.)(1<.(9.&40.)Lg2,(9.&40.)(1<.(9.&40.)Lg3,(9.&40.)(1<.P,(9.&40.)(:.(9.&8.))Lmm,P,(9.&40.)(:.(9.&8.))(1.(10.$1;.R17.(1>.R16.R15.))(1.(10.$1=.R16.(1?.(20.O1:.(15.&40.O1;.)O19.(15.&40.$21.)R14.R13.R12.O18.O17.R11.R10.R?.R>.R=.R<.R;.R:.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R9.R8.R7.R6.)O<.(22.O1:.)O;.(23.(9.&40.))R1.(24.$25.)))(1.(<.(26.O3.O1;.O:.O7.O4.)O1.R1.)(1.(27.Vh,Vms,O1.R1.)(1.(28.$25.R1.)(1.(29.$25.R1.O3.O1;.)(1.(2:.R1.O:.O9.(1:.O8.+1.)(15.&8.=)R5.R4.R3.R2.=)(1.(2;.$25.R1.O:.(2<.$0.(9.&40.)(15.&40.)(2=.$0.O2.(2>.Vidx,)O7.)))(1.P,(18.Vidx,(1:.O8.+1.))(2?.$25.R2.O7.(30.$31.(32.(15.&40.O7.))(30.$31.(32.(15.&40.O6.))(30.$31.(32.(15.&40.O5.))(30.$31.(32.(15.&40.Vidx,))(33.$31.))))))(1.(1<.(9.&40.)Lmun',(9.&40.)(1<.(9.&40.)Lmuned',(9.&40.)(2?.$25.R3.(3.O4.+;48.)(30.$31.(32.R2.)(30.$31.(32.R1.)(33.$31.))))))(1.(2?.$25.R1.VS,(30.$31.(34.(2>.Vk,)(35.(9.&8.)(15.&8.=)(2>.Vk,)))(33.$31.)))(1.Px,(9.&40.)P,(1.(2.Vh,(36.&40.R1.))(18.(36.&40.R1.)(3.Vh,Vms,)))(10.(:.(9.&8.))A1.R3.R2.(23.(9.&8.)))(1.A1.VKd,R15.(37.R1.R15.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04?0@L10093078636.16 L10093079023.17 L12159038182.1  L12550999780.7  L13310444603.8  L13623533429.5  L13716440558.4  L14469552914.3  L15370085287.5  L15370085287.6  L15383077036.8  L17120848823.0  L17824949718.5  L18188954598.2  L18613391422.3  L18617520572.6  L18848261086.11 L18848261086.9  L18928472134.140L18928659628.134L18928848928.133L19255986154.5  L19748471079.8  L20079800912.2  L20258349674.6  L21160730262.3  L21164859156.6  L21917325657.10 L22151086780.6  L22155346750.3  L22260897511.17 L22260897636.16 L22706556426.12 L22706556426.16 L22796755902.2  L22895822921.2  L22986082834.4  L22986214684.8  L22986230290.4  L22988063762.3  L22988245899.7  L22988293788.4  L23072108830.5  L23238517969.9  L23238519114.7  L23533865030.3  L23534209094.2  L23604116437.3  L2416475157.5   L2416521884.4   L2416521884.7   L2416586774.8   L2416867730.4   L2416867734.6   L2416881682.3   L2418106607.2   L24428337845.4  L25453895696.1  L25539230355.2  L25612823620.10 L25612823620.12 L25707216828.6  L25711476286.3  L25908502102.10 L25908502102.8  L25932379246.9  L25996207898.7  L25996207898.8  L26000057361.11 L26238224510.5  L2667604873.2   L2667652766.5   L2669930247.3   L2670077703.3   L26738019667.3  L27848808849.2  L27950577173.201L27965418526.8  L27965418655.6  L28534791522.8  L28563114161.8  L28565141260.4  L28689790780.6  L28702308030.3  L28935824803.5  L28935824803.8  L29503674659.5  L29503674659.8  L30041702656.4  L33249560973.7  L33303540959.17 L33600451072.4  L34326450181.2  L35178439080.3  L36050161571.5  L36050161571.8  L36727783669.7  L37505258080.5  L381367295.4    L38235734261.1  L38591267909.7  L39548162518.5  L39843024695.5  L39843024822.7  L40457341356.8  L40461781671.5  L40461781671.6  L40596013857.0  L41168977507.1  L41170546196.5  L41170624669.3  L41934814366.5  L42032386519.11 L42032386519.9  L44158764132.16 L45322678814.17 L45322679197.16 L45475196676.4  L45475540740.4  L45475588106.8  L45477357696.6  L45477357700.4  L45477667722.4  L45477667722.6  L45477752067.4  L45477752477.6  L45481426272.2  L45795594935.17 L45795595060.16 L46102519042.2  L46305128815.5  L46305128815.7  L46305214438.5  L46305326053.6  L46305606241.4  L46305606245.5  L46318477592.3  L46964839509.4  L48771339175.8  L4892321280.4   L4892371081.5   L4895995491.2   L49112554109.16 L49112554494.17 L49712479872.6  L49712724366.3  L49712871822.3  L49714590976.3  L49714640919.6  L49826756303.17 L49826756428.16 L50152996865.9  L50842786409.3  L5145849408.4   L51792580493.5  L51804990182.5  L51807234943.5  L51807415167.5  L51811960886.11 L51815438289.14 L51815554002.13 L51815634267.13 L51815634267.14 L51815667669.14 L51815685713.12 L51815685717.12 L52588515520.1  L52629124457.7  L52629124457.8  L52659109638.5  L53333867221.10 L53519162060.8  L53612820716.10 L53671397630.0  L54047258197.4  L5423397489.3   L5423412209.3   L5423412213.5   L5423543784.6   L5423543926.4   L5423626495.3   L5423626495.6   L5423692405.7   L5425494637.1   L5425575025.3   L5425705855.7   L5425755249.3   L55444754773.10 L55588686165.0  L55872349312.4  L56238214112.5  L57628699659.12 L57665049639.5  L57665049639.6  L57677780780.8  L57794074386.8  L58134804943.8  L58698505970.1  L58703220369.3  L58807235472.10 L58854513664.4  L59284742411.9  L59308759376.4  L59314955108.8  L59794326752.5  L60048577758.12 L60061079509.8  L60061079509.9  L60299333669.2  L60415448949.5  L61028858444.138L61030793771.137L61654443324.8  L62881207689.4  L62893611528.8  L63025434126.10 L63025434126.8  L63025434126.9  L63030476754.1  L63350976992.5  L63381424381.9  L63480898753.2  L63481245647.3  L63481245647.6  L63481291078.4  L63482995918.1  L63489361093.11 L63489362270.8  L63489362399.6  L63577253031.5  L63577253031.6  L63580940204.8  L63879378933.10 L64364588651.5  L64364588651.8  L64368569696.11 L64512487732.2  L6452728242.10  L6496494112.5   L65170773033.5  L65170773033.6  L65175082786.8  L65271643703.0  L65433968558.200L65506203399.6  L65506203526.9  L66263467192.7  L66364520471.11 L66470645914.7  L66976243464.3  L66988458486.6  L66988511103.5  L66988511103.7  L66988590193.4  L66988590197.4  L67115905654.8  L68022485664.7  L68716811741.5  L7182676615.5   L7220523683.5   L7220523683.8   L7709035635.5   L7709035635.8   L839402745.11   L839402745.13   L839403874.11   L839403874.8    L8806423876.12  L9223405980.8   L9448615686.2   L9575919189.9   00000J00d00g01=01[01e02502@02N02\03303403B03H03R03`04:04T05305R06106?06W06_07107;07I07e08308=08W09109T0:E0:L0:R0:S0:T0:U0:`0:a0:b0;00;Q0;k0;l0<40<>0<?0<@0<A0<B0<C0<D0<O0<P0<\0<_0<g0=J0=m0>;0>E0>_0?90?Q0?g0@=0@\0@l0A40A50A60A70AB0AI0B10BO0Bf0C>0CP0C^0Cl0D60DD0DV0Dd0E60EG0E`0F?0FP0FX0Fc0G10GC0GR0G\0Gg0Gk0H>0HL0H^0I70IN0I\0Ij0Ik0Il0J80J90JG0J^0K50KQ0L10LT0LU0LV0LW0LX0LY0LZ0L[0L\0L]0L^0M80MR0MX0MY0MZ0M[0N20N30N40N50NF0Nb0Nc0O50O60OL0Ob0P90P:0P;0P<0P=0PW0Q10QG0QP0Qa0Qo0RA0RB0RC0RD0RE0RF0RG0RH0RI0RJ0RK0RO0Rd0S<0SL0Sn0TA0T`0Ta0U20U30U40U50U60U70U80U90U:0U;0U<0U=0U>0UU0UV0Ug0V10VT0Vb0W00WG0W_0X50X60X@0Xb0Y30YN0Y[0Z00Z:0Z^0[90[T0[\0[f0\E0\d0]:0]F0]V0^60^Q0_00_30_=0_[0_c0_d0_e0_f0_g0`G0`e0a<0aJ0aX0ao0bR0be0c80cT0c]0d@0dJ0dX0df0e=0e>0ef0f90fW0fk0gL0gb0gc0gd0ge0gf0gg0h90hN0hc0i50iF0iT0if0j40jF0jg0kL0kg0l>0la0m70m?0m]S3idx1n5bases3IDX2A'2n'2H2S3idx1n5bases3IDX2A'2n'2H2S1hS3hAR2SP1T2lo2TH5LOIMGS3hAR2SP2PA2lo5bases3PAH5LOIMGS3hAR1T2TLS2PA1T5bases3ATPS2SP2lo3SPLS3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR1h2ms1S1k2lo5LOIMGSS1h2ms1S1k3SKBS1T2TLS1h2ms3HHIS3hAR1h2ms3HHIS3hAR1h2ms1S1k4last2C23SKBS3hAR1h2ms1S1k4last2C23SKBS3hAR1h2ms1p1S1k2PB2PE2SP5basesS3hAR1h2ms1p1S1k2PB2PE2SP5basesS3hAR1h2ms1p1S1k2PB2PE2SP5basesS1h2ms1S1k3SKBS3hAR2PA1T5bases3PAH3ATPS2ms3D4mS1h2ms1S1k3HHI3SKBS1h2ms3HHIS3hAR1h2ms3HHIS1h2ms1S1k2SP2lo2A'2n'2H12H2S3hAR1h2ms3HHIS1h2ms3HHIS3idx1n5bases3IDX2A'2n'2H2S3idx1n5bases3IDX2A'2n'2H2S1h2ms3idx1S1k2SP2PA4last1T2lo1y2HyS1h2ms3idx1S1k2PB2PE2SP2PA4last1T2lo3PBR3PER1y2HyS2SP2loS1h2msFFFS2SP2lo3SPLFFS3hAR2lo5LOIMGS3hAR2SP3CTX2lo2CH5LOIMG2A'2n'2H2S3hAR2SP2lo5LOIMG2A'2n'2H'FS3CTX2CLS1h2ms3MSBFFFFFFS2SP2lo3SPLFS1h1S2PB3PBRS1hS2ms3D4mS3hAR1h2ms1S1k2PA5bases3PAL3PAH3SKBS3hAR1h2ms1S1k2PA5bases3PAL3PAH3SKBS3hAR1h2ms3HHIS1h2ms3HHIS3hAR1h2ms1S1k3HHI3HMS3SKBS3hAR1h2ms1S1k3HHI3HMS3SKBS1h2ms1S1k2PB2PE2nZ1x2HxS3hAR4last2lo2C35LOIMGS3hAR4last2lo2C35LOIMGS3hAR1h2ms1S1k4last2lo2C35LOIMGS2SP2lo2A'2n'2H1S2ms3MSBFFFS2SP2lo3SPLS2SP2loS3hAR1h2ms1p1S1k2PB2PE2SP5bases3LB81H2H0S2PA3CTX5bases3ACP2A'2n'2H12H2S2PA5bases3PAL2A'2n'2H1S1h2ms1S1k2PB2PE3SKB3PERS3hAR1h2ms4last2C4S1h2ms4last2C4S3hAR1h2ms3HHIS1h2ms3HHIS1h2ms1S1k3SKBS3hAR1h2ms1S1k3SKBS1h2ms1S1k3SKBS3hAR1h2ms1S1k3SKBS3hAR2SP2lo5LOIMGS3hAR2SP4last2lo2C35LOIMGS3idx1n4last5bases3IDX2A'2n'2H4S3hAR2SP2lo5LOIMGS2ms3MSBS4last1T2C6S1h2ms1S1k3SKBS3hAR1h2ms1S1k3SKBS3hAR4last1T2C6S3hAR1T2TLS1h1S2PB2HaS2loS1h2ms1S1k2PB2PE2PGS1h2ms1S1k3SKBS4last2C22A'2n'2H1S4last3CTX2C72A'2n'2H12H2S3hAR1h2ms1S1k2lo5LOIMGS3hAR2lo5LOIMGS3hAR2lo5LOIMGSFS3hAR2ms3MSBFS3hAR2lo5LOIMGS3hAR1h2ms1S1k1T2TL3SKBS3hAR1h2ms1S1k1T2TL3SKBS1h3idx1n5bases3IDX2A'2n'2H5S3idx2PA1n5bases3IDX2NB2A'2n'2H3S3idx2PA1n5bases3IDX2NB2E12A'2n'2H3FFFFFFFFFFS3idx1n5bases3IDX2A'2n'2H2S3idx1n5bases3IDX2A'2n'2H2S1T2TLFFFS1h2ms2PA5bases3MSB3APHFFFS3hAR2SP2lo5LOIMGS3hAR1h2ms3HHI3HMS3MSB2DH2DMFS3hAR1h2ms3HMS3MSBFS2SP2lo5bases2A'2n'2H1S2SP2lo5bases2A'2n'2H1S3idx1n5bases3IDX2NB2LBFFFFS3idx1n5bases3IDX2A'2n'2H2S3idx1n5bases3IDX2A'2n'2H2S3hAR1h2ms1S1k3HHI3SKBS1h2ms2DMS3hAR2SP2lo5LOIMGS1h2ms1S1k3SKBS3hAR1h2ms3HHI3HMSFFFFFFFFFFS2msS2SP1T2lo2A'2n'2H12H2S1h2ms2SP2lo2A'2n'2H12H2S1h2ms1T3MSB3ATHS3hAR1h2ms1S1k2SP2lo5LOIMG3SPL3SKBS1h2ms1S1k2PB2PE2nZS1h2ms1S1k2PB2PE3SKB2PG3PBR3PERSS3hAR2SP2lo5LOIMGFFFFFFFFFFFFS3hAR1h2ms1S1k1T2TL3SKBSS3hAR2SP2lo5LOIMGS3hAR1T2TLS1h2ms3idx1S1k2SP2PA4last1T2lo1y2HyS3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR1h2ms1S1k2lo5LOIMGS1h2ms1S1k2PB2PE3SKB3PERS1h2ms1S1k2PB2PE2nZ2D1FS1h2ms3HHIS3hAR1h2ms1S1k2SP2lo5LOIMG3SPL3SKBS3hAR2SP2lo5LOIMGS3hAR1h2ms2PA5bases3PAH3APHS3idx1n2E12C1S1h2ms1S1k2PB2PE2PG1ES3hAR1T2TLS3hAR1h2ms1S1k2PA2lo5bases3PAH5LOIMGS3hAR2PA2lo5bases3PAH5LOIMGS3hAR2PA2lo5bases3PAH5LOIMGS2SP3SPHS3hAR1T2TLS3hAR1h2ms1p1S1k2PB2PE2SP5basesS3hAR1h2ms1p1S1k2PB2PE2SP5basesS1h2ms1S1k2PB2PE2nZ2HnS1h2ms1T3ATHS3hAR1h2ms1T3ATHS3hAR1h2ms1S1k1T2lo2TL5LOIMG3SKBS3hAR1h2ms1S1k2lo5LOIMG3SKBS3hAR1h2ms1S1k2lo3HHI5LOIMG3SKBS1hS3hAR1T2TLS3hAR1h2ms1S1k2SP2lo5LOIMG3SKBS2PA3PALFFFFS3hAR1h2ms1S1k2lo5LOIMG2A'2n'2H'S3hAR3CTX2lo2CH5LOIMG2A'2n'2H2S3hAR2lo5LOIMG2A'2n'2H1S3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR1h2ms1S1k2lo5LOIMGS3hAR1h2ms1S1k2lo3HHI3HMS5LOIMG3SKBS3hAR1T2lo2TH5LOIMGS3hAR1T2lo2TH5LOIMGS3hAR1h2ms1S1k1T2lo2TH5LOIMGS4last2C2S3hAR1h2ms1S1k2PA5bases3PAL3PAH3SKBS3hAR1T2TLS3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR1h2ms1S1k2lo5LOIMGSS3hAR1h2ms1p1S1k2PB2PE2SP5bases3LB81H2H0S1h2ms3HHI2A'2n'2H1S1h2ms3CTX3MSB3ACH2A'2n'2H12H2S1h2ms1S1k2PB2PE3PERS1h2ms1S1k2PB2PE3PBR3PER2A'2n'2H1S1h2ms1S1k4last2C23SKBFFFFFS3hAR2PA5bases3PAHS1h2ms1S1k2PB2PE1x2HxS1h2ms1S1k2PB3SKB3PBRS1h2ms4last3MSB2C4S3CTX2CL2A'2n'2H1S1h2ms1S1k3SKBS3hAR1h2ms1S1k3SKBS1h2ms1S1k3SKBS3hAR1h2ms1S1k3SKBS1h2ms1S1k3CTX2CL3SKB2A'2n'2H12H2S3hAR1h2ms1S1k3CTX2CL3SKB2A'2n'2H12H2S3hAR1h2ms1S1k3SKB2A'2n'2H'S1h2ms1S1k3SKB2A'2n'2H'S1h2ms3idx1S1k2SP2PA4last1T2lo1y2HyS1h2ms1S1k2PB2PE2nZ2D1S2SP3SPHS3hAR1h2ms2SP2lo3HMS3MSB5LOIMG". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOK KL CSOK' KdL HAS T_unmap POISON PB PE HASM T_madv NOROM"] Lemma large_free_cfgS : ltac2:(CDefT.buildp (gd_tbl_AW_LargeFreeCfg ()) "PQ,P,$1;.SpPra,(9.&40.)Pgp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Psorted,(9.&8.)Pg2,(9.&40.)Pg3,(9.&40.)Pmun,(9.&40.)Pmuned,(9.&40.)Pnfr,(9.&40.)Pcal,(9.&40.)PSP,$0.PPA,$0.Pnres,$0.Pn,$0.Plast,$0.Plms,$0.Plsz,$0.PT,$0.PCTX,$0.Plo,$0.Pbases,(7.$0.)Pjunk,(7.(9.&8.))PF,(38.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(:.(9.&8.))Pmo,$?.P,(10.$0.(39.Vh,+1000.)=)P,(1.(2.+65?000.Vh,)(4.(2.(3.Vh,Vms,)+7???7000.)(2.+10007???8000.Vh,)))P,(2.(3.Vh,Vms,)(3:.VhAR,))P,(1.(2.+1000.Vms,)(18.Vms,(3;.+2.+2;.)))P,(10.$0.(39.Vms,+1000.)=)P,(1.(2.=Vsz,)(18.Vsz,(3;.+2.+40.)))P,(1.(2.=Vidx,)(18.Vidx,R13.))P,(2.R14.(3<.(3=.$0.R=.)))P,(18.(3<.(3=.$0.R>.))(3;.+2.+28.))P,(10.(:.$0.)(3>.$0.R?.(2>.Vidx,))(3?.$0.Vh,))P,(10.(:.$0.)(3>.$0.R10.(2>.(1:.R17.+1.)))(3?.$0.R16.))P,(1.(2.+65?000.R1:.)(4.(2.(3.R1:.+800000.)+7???7000.)(2.+10007???8000.R1:.)))P,(1.(2.(40.+8.(3<.(3=.$0.R12.)))+800000.)(2.(3.R1;.+800000.)(3:.VhAR,)))P,(1.(2.=R1;.)(18.R1;.(3;.+2.+40.)))P,(2:.R10.R1=.R1<.R1;.R25.R20.R1?.R24.R23.=)P,(2;.$25.R11.R1>.(2<.$0.(9.&40.)(15.&40.)R15.))P,(41.VCS,R1?.(40.+8.(3<.(3=.$0.R16.))))P,(2?.$25.R13.Vh,(30.$31.(32.(15.&40.Vh,))(30.$31.(32.(15.&40.Vms,))(30.$31.(32.(15.&40.Vsz,))(30.$31.(32.(15.&40.Vidx,))(33.$31.))))))P,(41.VCS,Vh,Vms,)P,(4.(2.(3.R22.(40.+8.(3<.(3=.$0.R19.))))Vh,)(2.(3.Vh,Vms,)R22.))P,(4.(1.(10.$0.Vidx,(1:.R21.+1.))(10.$0.R20.Vh,))(1.(18.Vidx,(1:.R21.+1.))(1.(1.(2.+65?000.R20.)(4.(2.(3.R20.+1000.)+7???7000.)(2.+10007???8000.R20.)))(1.(2.(3.R20.+1000.)(3:.VhAR,))(1.(4.(2.(3.R20.+1000.)Vh,)(2.(3.Vh,Vms,)R20.))(1.(4.(2.(3.R23.(40.+8.(3<.(3=.$0.R1:.))))R20.)(2.(3.R20.+1000.)R23.))(1.(4.(2.(3.R1=.+1000.)R20.)(2.(3.R20.+1000.)R1=.))(1.(4.(2.(3.R1<.+10000.)R20.)(2.(3.R20.+1000.)R1<.))(1.(2?.$25.R16.R20.(30.$31.(32.(15.&40.R20.))(30.$31.(32.(15.&40.R1?.))(30.$31.(32.(15.&40.R1>.))(30.$31.(32.(15.&40.(1:.R21.+1.)))(33.$31.))))))(41.VCS,R20.+20.))))))))))P,(1.(1.(2.+1000.R1>.)(4.(2.(3.R1>.+1000.)+10000.)(2.+65?000.R1>.)))(4.(2.(3.R1>.+1000.)+7???7000.)(2.+10007???8000.R1>.)))P,(2.(3.R1?.+1000.)(3:.VhAR,))P,(1.(2.+65?000.R1?.)(4.(2.(3.R1?.+10000.)+7???7000.)(2.+10007???8000.R1?.)))P,(2.(3.R20.+10000.)(3:.VhAR,))P,(4.(2.(3.R22.+1000.)Vh,)(2.(3.Vh,Vms,)R22.))P,(4.(2.(3.R23.+1000.)R29.)(2.(3.R29.(40.+8.(3<.(3=.$0.R20.))))R23.))P,(4.(2.(3.R23.+10000.)Vh,)(2.(3.Vh,Vms,)R23.))P,(4.(2.(3.R24.+10000.)R2;.)(2.(3.R2;.(40.+8.(3<.(3=.$0.R22.))))R24.))P,(4.(2.(3.R25.+10000.)R26.)(2.(3.R26.+1000.)R25.))P,(2?.$25.R20.(3.R27.+;48.)(30.$31.(32.R32.)(30.$31.(32.R31.)(33.$31.))))P,(41.VCS,R28.+1000.)P,(>.R22.R29.R28.)P,(41.VCS,R29.+10000.)P,(42.R24.)P,(;.R25.Vcan,Vdd,Vmadv,)P,(2?.$25.R26.VS,(30.$31.(34.(2>.Vk,)R29.)(33.$31.)))P,(29.$25.R27.R2<.R35.)P,(2.(3:.VhAR,)R2=.)P,(2.R2>.(1:.R37.+2;0.))P,(2.R38.(3;.+2.+3>.))P,(10.$0.(39.R39.+10.)=)P,(41.VCS,R31.(1:.R3:.R31.))P,(41.VCS',R32.(1:.R3;.R32.))P,(28.$25.R2>.)P,A1.VK,R2>.P,(37.R30.R2?.)P,Pc',$1;.P,(43.R40.R61.R60.R5<.R5;.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R34.R33.R3?.R3>.R3=.R3<.R3;.R3:.R39.R37.R36.R32.R1.)(44.$25.R63.R2.)(44.$25.R62.(1>.(1?.(20.R61.(15.&40.R40.)R60.(15.&40.$21.)R5?.R5>.R5=.R5<.R5;.(15.&40.$45.)(15.&40.$46.)(15.&40.Vp,)R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.)R34.(15.&40.$47.)R33.(23.(9.&40.))R32.(24.$25.))R31.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sorted g2 g3
      mun muned nfr cal SP PA nres n last lms lsz T CTX lo bases junk F fc m mo
      HAL HHI HMS MSB MSA SZB IDX NB LB NI NL PAL PAH NRB SEC ARR PACS HDR HCS APH CASES
      TL TH CL CH ATH ATP ACH ACP ACT TST TCS DS CCS PS RS SH ST LOIMG SPL SPH SPA SCS SCS' MI HK HJ HS.
    pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    assert (HSd : S = 0x7fff8000 + h / 8) by reflexivity. assert (HKd : k = ms / 8) by reflexivity.
    pose proof (Z.div_mod h 4096 ltac:(lia)) as D4h. rewrite HAL, Z.add_0_r in D4h.
    pose proof (Z.div_mod ms 4096 ltac:(lia)) as D4m. rewrite MSA, Z.add_0_r in D4m.
    assert (M8h : h mod 8 = 0) by (rewrite D4h; replace (4096 * (h / 4096)) with (512 * (h / 4096) * 8) by (clear; lia); apply Z_mod_mult).
    assert (M8m : ms mod 8 = 0) by (rewrite D4m; replace (4096 * (ms / 4096)) with (512 * (ms / 4096) * 8) by (clear; lia); apply Z_mod_mult).
    pose proof (Z.div_mod h 8 ltac:(lia)) as DH. rewrite M8h, Z.add_0_r in DH.
    pose proof (Z.div_mod ms 8 ltac:(lia)) as DM. rewrite M8m, Z.add_0_r in DM.
    assert (SKB : ((h + ms <= 0x7fff7000 /\ 0x800c3e00 <= S /\ S + k <= 0x8fff7000) \/ (0x10007fff8000 <= h /\ 0x20008fff000 <= S /\ S + k <= 0x10007fff0000)) /\ 512 <= k)
      by (rewrite HSd, HKd; clear -DH DM HHI HMS MSB; lia).   (* [comment removed for export] *)
    assert (NZ : page_round_up_Z ms = ms).
    { unfold page_round_up_Z, page_size.
      replace (ms + 4096 - 1) with (4095 + ms / 4096 * 4096) by (clear -D4m; lia). rewrite Z.div_add, Z.mul_add_distr_r by lia. change (4095 / 4096) with 0. clear -D4m; lia. }
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL CS K _ Q _ mo KL HK); [exact HJ| |].
    { eapply (ld_A AL IMG ALWF CS CSOK) with (p := p) (h := h) (ms := ms) (sz := sz) (idx := idx) (n := n) (PA := PA) (bases := bases)
                                            (last := last) (lms := lms) (lsz := lsz) (sorted := sorted) (g2 := g2) (g3 := g3) (nres := nres) (nfr := nfr) (cal := cal) (lo := lo);
        first [ exact HAL | exact IDX | exact NB | exact LB | exact NI | exact NL | exact NRB | exact SEC | exact ARR | exact PACS | exact HDR
              | exact ST | exact LOIMG | exact SCS | exact MI | exact SZB
              | unfold p; clear; lia | clear -HHI; lia | clear -HMS MSB; lia | clear -MSB; lia | clear -PAL; lia | clear -PAH; lia
              | eapply crange_sub; [exact HCS| clear; lia| clear -MSB; lia]
              | clear -APH MSB; lia | clear -SPL; lia | exact SPH
              | destruct CASES as [C1|(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9)];
                [left; exact C1| right; split; [exact C1|]; split; [clear -C2; lia|]; split; [exact C3|]; split; [clear -C4 MSB; lia|]; split; [exact C5|]; split; [exact C8| exact C9]] ]. }
    cbn beta. intros ms1 mo1 [P1 LH1] HK1 MM1 HJ1.
    ddestruct P1 as (m1 & nfr' & cal' & g2' & g3' & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & MU1 & WM1 & MI1 & SEC1 & ARR1 & HDR1 & FR1 & ST1 & ->).
    cbn [ms_mem] in LH1. cbn [ms_mem MS MSsvc] in HJ1.
    (* [comment removed for export] *)
    assert (LB8 : length (map (Z_to_bv 64) bases) = length bases) by apply map_length.
    assert (DJ1 : forall A' n', A' + n' <= lo -> (A' + n' <= A_INSTANCE \/ A_INSTANCE + 1024 <= A') -> (A' + n' <= PA \/ PA + 8 * Z.of_nat (length bases) <= A') ->
                  (A' + n' <= h \/ h + 4096 <= A') -> (idx < n - 1 -> A' + n' <= last \/ last + 4096 <= A') -> disjoint_from (ldA_W lo SP PA idx last) A' n').
    { intros A' n' H1 H2 H3 H5 H4. unfold ldA_W, A_SECONDARY, A_SEC_MUTEX, A_GSTATS, A_INSTANCE in *. cbn.
      destruct CASES as [[E1 E2]|(C1 & _)].
      - subst last. clear -H1 H2 H3 H5 IDX NB E1. repeat split; try lia.
      - specialize (H4 C1). clear -H1 H2 H3 H4 H5 IDX NB. repeat split; lia. }
    assert (FD1 : fine_dj (ldA_W lo SP PA idx last)).
    { intros A' n' H1 H2. apply DJ1; [clear -H1 LOIMG; lia| exact H2| clear -H1 PAL; lia| clear -H1 HHI; lia|]. intros C1.
      destruct CASES as [[E1 _]|(_ & C2 & _)]; [exfalso; clear -E1 C1; lia| clear -H1 C2; lia]. }
    assert (SH1 : rw_cells asegs m1 S [CB (Z.to_nat k) junk]).
    { eapply rw_cells_transport; [exact SH| exact MU1| exact WM1|]. cbn. rewrite ?Nat.add_0_r. rewrite Z2Nat.id by (clear -SKB; lia).
      apply DJ1; [clear -SKB LOIMG; lia| unfold A_INSTANCE; clear -SKB; lia| clear -SKB PAL PAH; lia| clear -SKB HHI; lia|].
      intros C1. destruct CASES as [[E1 _]|(_ & C2 & _)]; [exfalso; clear -E1 C1; lia| clear -SKB C2; lia]. }
    assert (TST1 : rw_cells asegs m1 (T + 2888) [C8 mun; C8 muned]).
    { eapply rw_cells_transport; [exact TST| exact MU1| exact WM1|]. cbn.
      apply DJ1; [clear -TH LOIMG; lia| unfold A_INSTANCE; clear -TL; lia| clear -ATP; lia| clear -ATH MSB; lia|].
      intros C1. destruct CASES as [[E1 _]|(_ & _ & _ & _ & _ & C6 & _)]; [exfalso; clear -E1 C1; lia| clear -C6; lia]. }
    assert (PS1 : poison_statics m1) by (eapply poison_statics_transport_fine; [exact PS| exact MU1| exact FD1]).
    assert (RS1 : rsmr_statics m1 can dd madv) by (eapply rsmr_statics_transport_fine; [exact RS| exact MU1| exact FD1]).
    assert (DS1 : dealloc_statics m1 T CTX).
    { eapply dealloc_statics_transport_fine; [exact DS| exact MU1| exact FD1|]. intros A' n' [H1 H2].
      apply DJ1; [clear -H2 CH LOIMG; lia| unfold A_INSTANCE; clear -H1 CL; lia| clear -H1 H2 ACP; lia| clear -H1 H2 ACH MSB; lia|].
      intros C1. destruct CASES as [[E1 _]|(_ & _ & _ & _ & _ & _ & C7 & _)]; [exfalso; clear -E1 C1; lia| clear -H1 H2 C7; lia]. }
    clear SH TST PS RS DS SEC ARR HDR ST MI.
    (* [comment removed for export] *)
    unfold A_LD_B.
    eapply (POISON Q) with (lo := lo) (junk := junk); try first [exact SH1 | exact PS1 | exact RS1 | exact ST1 | exact LOIMG | exact MI1 | exact HK1 | exact HJ1 | exact HCS].
    { clear -SPL; lia. } { clear -SPH; lia. } { rewrite <- Zplus_mod_idemp_l, SPA. reflexivity. }
    { eapply crange_sub; [exact SCS| clear; lia| clear; lia]. }
    intros c2 P2. ddestruct P2 as (ms2 & mo2 & y5 & y6 & y7 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & m2 & -> & -> & MU2 & WM2 & MI2 & SHZ2 & ST2 & HK2 & HJ2).
    change (0x7fff8000 + h / 8) with S in MU2, SHZ2. change (ms / 8) with k in MU2, SHZ2.
    replace (ret_pc (Z_to_bv 64 0x4a280)) with (Z_to_bv 64 0x4a280) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    assert (DJ2 : forall A' n', A' + n' <= lo -> (A' + n' <= S \/ S + k <= A') -> disjoint_from [(lo, SP + -32); (S, S + k)] A' n') by (intros A' n' H1 H2; cbn; clear -H1 H2; lia).
    assert (FR2 : rw_cells asegs m2 (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| cbn; clear -SKB LOIMG SPL; lia]).
    assert (HDR2 : rw_cells asegs m2 h [C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 idx)])
      by (eapply rw_cells_transport; [exact HDR1| exact MU2| exact WM2| apply DJ2; cbn; clear -SKB HHI HMS LOIMG; lia]).
    assert (TST2 : rw_cells asegs m2 (T + 2888) [C8 mun; C8 muned])
      by (eapply rw_cells_transport; [exact TST1| exact MU2| exact WM2| apply DJ2; cbn; clear -SKB TL TH LOIMG; lia]).
    assert (ARR2 : u64arr asegs m2 PA (map (Z_to_bv 64) (upd bases (Z.to_nat idx) last)))
      by (eapply u64arr_transport; [exact ARR1| exact MU2| exact WM2| rewrite map_length, upd_length; apply DJ2; clear -SKB PAL PAH LOIMG; lia]).
    assert (LH2 : idx < n - 1 -> rw_cells asegs m2 last [C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 lsz); C8 (Z_to_bv 64 idx)]).
    { intros C1. eapply rw_cells_transport; [exact (LH1 C1)| exact MU2| exact WM2|].
      destruct CASES as [[E1 _]|(_ & C2 & C3 & _)]; [exfalso; clear -E1 C1; lia|]. apply DJ2; cbn; clear -SKB C2 C3 LOIMG; lia. }
    assert (SEC2 : sec_cells m2 PA nres (n - 1) (Z_to_bv 8 0) nfr' cal' g2' g3' 0).
    { unfold sec_cells, A_SECONDARY, A_SEC_MUTEX, A_GSTATS, A_INSTANCE in *. ddestruct SEC1 as (Q1 & Q2 & Q3 & Q4 & Q5).
      repeat split; (eapply rw_cells_transport; [eassumption| exact MU2| exact WM2| apply DJ2; cbn; clear -SKB LOIMG; lia]). }
    assert (PS2 : poison_statics m2) by (eapply (poison_statics_transport _ _ _ PS1 MU2); intros A' n' H'; apply DJ2; clear -H' SKB LOIMG; lia).
    assert (RS2 : rsmr_statics m2 can dd madv) by (eapply (rsmr_statics_transport _ _ _ _ _ _ RS1 MU2); intros A' n' H'; apply DJ2; clear -H' SKB LOIMG; lia).
    assert (DS2 : dealloc_statics m2 T CTX).
    { eapply (dealloc_statics_transport _ _ _ _ _ DS1 MU2). intros A' n' [H'|[H1 H2]]; apply DJ2; [clear -H' SKB LOIMG; lia| clear -H' SKB; lia| clear -H2 CH LOIMG; lia| clear -H1 H2 CL SKB; lia]. }
    dpose RS2 as (_ & _ & _ & GOTF2 & LIM2 & _ & SEAL2 & GPZ2 & PZC2 & _).
    assert (RMP2 : rmp_statics m2) by (exact (conj GPZ2 (conj PZC2 SEAL2))).
    clear SH1 TST1 PS1 RS1 DS1 SEC1 ARR1 HDR1 FR1 ST1 MI1 LH1.
    (* [comment removed for export] *)
    assert (MU02 : munch (ldA_W lo SP PA idx last ++ [(T + 2888, T + 2904); (S, S + k)]) m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]];
        unfold sub_fp, ldA_W; cbn [outside app]; clear; intros y Hy; lia. }
    assert (WM02 : wmono asegs m m2) by (eapply wmono_trans; [exact WM1| exact WM2]).
    clear MU1 MU2 WM1 WM2.
    (* [comment removed for export] *)
    assert (TAIL : forall (ms3s : machine_state) (m2' : mem) (mo2' : Model),
      munch (ldA_W lo SP PA idx last ++ [(T + 2888, T + 2904); (S, S + k)]) m m2' -> wmono asegs m m2' ->
      u64arr asegs m2' PA (map (Z_to_bv 64) (upd bases (Z.to_nat idx) last)) ->
      (idx < n - 1 -> rw_cells asegs m2' last [C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 lsz); C8 (Z_to_bv 64 idx)]) ->
      sec_cells m2' PA nres (n - 1) (Z_to_bv 8 0) nfr' cal' g2' g3' 0 ->
      rw_cells asegs m2' S [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))] ->
      ro_cells asegs m2' A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)] -> ro_cells asegs m2' A_MMAP_LIMIT [C8 (Z_to_bv 64 0)] ->
      K mo2' -> J (ms_mem ms3s) mo2' ->
      evtA asegs AL CS (ldB2_post SP gp s2 s1 s0 ra s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 F fc T h ms sz idx lo m2') ms3s ->
      aevtS asegs Q (mkCfg ms3s mo2')).
    { clear ARR2 LH2 SEC2 SHZ2 HDR2 TST2 FR2 ST2 MI2 PS2 RS2 DS2 RMP2 GOTF2 LIM2 SEAL2 GPZ2 PZC2 MU02 WM02 HK2.
      intros ms3s m2' mo2' MU02 WM02 ARR2 LH2 SEC2 SHZ2 GOTF2 LIM2 HK2' HJ2' EV.
      eapply (evtA_aevtS_KJ AL CS K _ Q _ mo2' KL HK2'); [exact HJ2'| exact EV|].
      cbn beta. intros ms3 mo3 P3 HK3 MM3 HJ3.
      ddestruct P3 as (m3 & z5 & z6 & z7 & z13 & z14 & z15 & z16 & z17 & MU3 & WM3 & MI3 & HDR3 & (mw1 & mw2 & TST3) & ST3 & ->).
    assert (DJ3 : forall A' n', A' + n' <= lo -> (A' + n' <= T + 2888 \/ T + 2904 <= A') -> disjoint_from [(lo, SP); (T + 2888, T + 2904)] A' n') by (intros A' n' H1 H2; cbn; clear -H1 H2; lia).
    assert (ARR3 : u64arr asegs m3 PA (map (Z_to_bv 64) (upd bases (Z.to_nat idx) last)))
      by (eapply u64arr_transport; [exact ARR2| exact MU3| exact WM3| rewrite map_length, upd_length; apply DJ3; clear -ATP PAH LOIMG; lia]).
    assert (LH3 : idx < n - 1 -> rw_cells asegs m3 last [C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 lsz); C8 (Z_to_bv 64 idx)]).
    { intros C1. eapply rw_cells_transport; [exact (LH2 C1)| exact MU3| exact WM3|].
      destruct CASES as [[E1 _]|(_ & C2 & C3 & _ & _ & C6 & _)]; [exfalso; clear -E1 C1; lia|]. apply DJ3; cbn; clear -C3 C6 LOIMG; lia. }
    assert (SEC3 : sec_cells m3 PA nres (n - 1) (Z_to_bv 8 0) nfr' cal' g2' g3' 0).
    { unfold sec_cells, A_SECONDARY, A_SEC_MUTEX, A_GSTATS, A_INSTANCE in *. ddestruct SEC2 as (Q1 & Q2 & Q3 & Q4 & Q5).
      repeat split; (eapply rw_cells_transport; [eassumption| exact MU3| exact WM3| apply DJ3; cbn; clear -TL LOIMG; lia]). }
    assert (SHZ3 : rw_cells asegs m3 S [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))]).
    { eapply rw_cells_transport; [exact SHZ2| exact MU3| exact WM3|]. cbn. rewrite ?Nat.add_0_r. rewrite Z2Nat.id by (clear -SKB; lia). apply DJ3; clear -SKB TL LOIMG; lia. }
    assert (GOTF3 : ro_cells asegs m3 A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)])
      by (eapply ro_cells_transport; [exact GOTF2| exact MU3| apply DJ3; cbn; unfold A_GOT_CFLAGS; clear -TL LOIMG; lia]).
    assert (LIM3 : ro_cells asegs m3 A_MMAP_LIMIT [C8 (Z_to_bv 64 0)])
      by (eapply ro_cells_transport; [exact LIM2| exact MU3| apply DJ3; cbn; unfold A_MMAP_LIMIT; clear -TL LOIMG; lia]).
    assert (MU03 : munch (ldA_W lo SP PA idx last ++ [(T + 2888, T + 2904); (S, S + k)]) m m3).
    { eapply munch_trans; [exact MU02|]. eapply munch_weaken; [| exact MU3]. unfold sub_fp, ldA_W; cbn [outside app]; clear; intros y Hy; lia. }
    assert (WM03 : wmono asegs m m3) by (eapply wmono_trans; [exact WM02| exact WM3]).
    clear ARR2 LH2 SEC2 SHZ2 GOTF2 LIM2 MU02 MU3 WM02 WM3.
    (* [comment removed for export] *)
    eapply (unmap_or_die_cfgS AL IMG ALWF CS CSOK h ms K Kd KL CS' CSOK' KdL HAS T_unmap Q) with (lo := lo);
      try first [exact GOTF3 | exact LIM3 | exact ST3 | exact LOIMG | exact SCS | exact SCS' | exact MI3 | exact HK3 | exact HJ3 | exact HAL].
    { clear -HHI; lia. } { clear -MSB; lia. } { rewrite NZ. exact HMS. } { clear; lia. } { clear -SPL; lia. } { clear -SPH; lia. }
    intros c4 P4. ddestruct P4 as (ms4 & mo4 & w5 & w6 & w7 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w28 & w29 & w30 & w31 & m4 & -> & -> & MU4 & WMO4 & MI4 & ST4 & NONE4 & HKd4 & HJ4).
    rewrite NZ in MU4, WMO4, NONE4.
    apply HS. unfold lfree_postS. deexists 17. dexists nfr', cal', g2', g3', m4. split; [reflexivity|]. split; [reflexivity|].
    assert (DJ4 : forall A' n', A' + n' <= lo -> (A' + n' <= h \/ h + ms <= A') -> disjoint_from [(lo, SP); (h, h + ms)] A' n') by (intros A' n' H1 H2; cbn; clear -H1 H2; lia).
    split. { unfold lfree_W. eapply munch_trans; [eapply munch_weaken; [| exact MU03]| eapply munch_weaken; [| exact MU4]];
             unfold sub_fp, ldA_W; cbn [outside app]; clear; intros y Hy; lia. }
    split. { eapply wmono_out_trans; [apply wmono_out_of_wmono; exact WM03| exact WMO4]. }
    split; [exact MI4|]. split; [exact ST4|].
    split. { unfold sec_cells, A_SECONDARY, A_SEC_MUTEX, A_GSTATS, A_INSTANCE in *. ddestruct SEC3 as (Q1 & Q2 & Q3 & Q4 & Q5).
             repeat split; (eapply rw_cells_transport_out; [eassumption| exact MU4| exact WMO4| apply DJ4; cbn; clear -HHI LOIMG; lia| cbn; clear -HHI; lia]). }
    split. { eapply u64arr_transport_out; [exact ARR3| exact MU4| exact WMO4| rewrite map_length, upd_length; apply DJ4; clear -APH PAH LOIMG; lia| rewrite map_length, upd_length; exact APH]. }
    split. { intros C1. destruct CASES as [[E1 _]|(_ & C2 & C3 & C4 & _)]; [exfalso; clear -E1 C1; lia|].
             eapply rw_cells_transport_out; [exact (LH3 C1)| exact MU4| exact WMO4| apply DJ4; cbn; clear -C3 C4 LOIMG; lia| cbn; clear -C4; lia]. }
    split. { dexists mw1, mw2. eapply rw_cells_transport_out; [exact TST3| exact MU4| exact WMO4| apply DJ4; cbn; clear -TH ATH LOIMG; lia| cbn; clear -ATH; lia]. }
    split. { eapply rw_cells_transport_out; [exact SHZ3| exact MU4| exact WMO4| | ]; cbn; rewrite ?Nat.add_0_r; rewrite Z2Nat.id by (clear -SKB; lia); [apply DJ4|]; clear -SKB HHI LOIMG; lia. }
    split; [exact NONE4|]. split; [exact HKd4| exact HJ4].
    }
    (* [comment removed for export] *)
    assert (EQE : 0x7fff8000 + (h + ms) / 8 = S + k).
    { rewrite HSd, HKd. replace (h + ms) with (h + ms / 8 * 8) by (clear -DM; lia). rewrite Z.div_add by (clear; lia). clear; lia. }
    eapply (evtA_aevtS_KJ AL CS K _ Q _ mo2 KL HK2); [exact HJ2| |].
    { eapply (ld_B1 AL IMG ALWF CS CSOK) with (h := h) (ms := ms) (lo := lo);
        first [ exact PS2 | exact RMP2 | exact ST2 | exact LOIMG | exact SCS | exact MI2 | clear -HHI HMS; lia | clear -MSB; lia | clear -SPL; lia | exact SPH ]. }
    cbn beta. intros ms3 mo3 P3 HK3 MM3 HJ3.
    ddestruct P3 as (m3 & z5 & z14 & z15 & z16 & MU3 & WM3 & MI3 & ST3 & ARMS).
    rewrite EQE in ARMS. change (0x7fff8000 + h / 8) with S in ARMS. fold PB PE in ARMS.
    (* [comment removed for export] *)
    assert (DJ3f : forall A' n', A' + n' <= lo \/ SP + -32 <= A' -> disjoint_from [(lo, SP + -32)] A' n') by (intros A' n' H1; cbn; clear -H1; lia).
    assert (FR3 : rw_cells asegs m3 (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3| apply DJ3f; cbn; clear; lia]).
    assert (HDR3 : rw_cells asegs m3 h [C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 idx)])
      by (eapply rw_cells_transport; [exact HDR2| exact MU3| exact WM3| apply DJ3f; cbn; clear -HHI HMS LOIMG MSB; lia]).
    assert (TST3 : rw_cells asegs m3 (T + 2888) [C8 mun; C8 muned])
      by (eapply rw_cells_transport; [exact TST2| exact MU3| exact WM3| apply DJ3f; cbn; clear -TL TH LOIMG; lia]).
    assert (ARR3 : u64arr asegs m3 PA (map (Z_to_bv 64) (upd bases (Z.to_nat idx) last)))
      by (eapply u64arr_transport; [exact ARR2| exact MU3| exact WM3| rewrite map_length, upd_length; apply DJ3f; clear -PAL PAH LOIMG; lia]).
    assert (LH3 : idx < n - 1 -> rw_cells asegs m3 last [C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 lsz); C8 (Z_to_bv 64 idx)]).
    { intros C1. eapply rw_cells_transport; [exact (LH2 C1)| exact MU3| exact WM3|].
      destruct CASES as [[E1 _]|(_ & C2 & C3 & _)]; [exfalso; clear -E1 C1; lia|]. apply DJ3f; cbn; clear -C2 C3 LOIMG; lia. }
    assert (SEC3 : sec_cells m3 PA nres (n - 1) (Z_to_bv 8 0) nfr' cal' g2' g3' 0).
    { unfold sec_cells, A_SECONDARY, A_SEC_MUTEX, A_GSTATS, A_INSTANCE in *. ddestruct SEC2 as (Q1 & Q2 & Q3 & Q4 & Q5).
      repeat split; (eapply rw_cells_transport; [eassumption| exact MU3| exact WM3| apply DJ3f; cbn; clear -LOIMG; lia]). }
    assert (SHZ3 : rw_cells asegs m3 S [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))]).
    { eapply rw_cells_transport; [exact SHZ2| exact MU3| exact WM3|]. cbn. rewrite ?Nat.add_0_r. rewrite Z2Nat.id by (clear -SKB; lia). apply DJ3f; clear -SKB LOIMG; lia. }
    assert (DS3 : dealloc_statics m3 T CTX).
    { eapply (dealloc_statics_transport _ _ _ _ _ DS2 MU3). intros A' n' [H'|[H1 H2]]; apply DJ3f; [clear -H' LOIMG; lia| clear -H2 CH LOIMG; lia]. }
    assert (GOTF3 : ro_cells asegs m3 A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)])
      by (eapply ro_cells_transport; [exact GOTF2| exact MU3| apply DJ3f; cbn; unfold A_GOT_CFLAGS; clear -LOIMG; lia]).
    assert (LIM3 : ro_cells asegs m3 A_MMAP_LIMIT [C8 (Z_to_bv 64 0)])
      by (eapply ro_cells_transport; [exact LIM2| exact MU3| apply DJ3f; cbn; unfold A_MMAP_LIMIT; clear -LOIMG; lia]).
    assert (MU03 : munch (ldA_W lo SP PA idx last ++ [(T + 2888, T + 2904); (S, S + k)]) m m3).
    { eapply munch_trans; [exact MU02|]. eapply munch_weaken; [| exact MU3]. unfold sub_fp, ldA_W; cbn [outside app]; clear; intros y Hy; lia. }
    assert (WM03 : wmono asegs m m3) by (eapply wmono_trans; [exact WM02| exact WM3]).
    clear ARR2 LH2 SEC2 SHZ2 HDR2 TST2 FR2 ST2 MI2 PS2 RS2 DS2 RMP2 GOTF2 LIM2 SEAL2 GPZ2 PZC2 MU02 WM02 MU3 WM3 HK2.
    destruct ARMS as [(NP & z10 & z11 & z12 & z13 & z17 & ->) | (PG & z13 & ->)].
    - (* [comment removed for export] *)
      apply (TAIL _ m3 mo3 MU03 WM03 ARR3 LH3 SEC3 SHZ3 GOTF3 LIM3 HK3); [exact HJ3|].
      eapply (ld_B2 AL IMG ALWF CS CSOK) with (T := T) (CTX := CTX) (h := h) (ms := ms) (sz := sz) (idx := idx) (mun := mun) (muned := muned) (lo := lo);
        first [ exact HDR3 | exact TST3 | exact TCS | exact DS3 | exact CCS | exact FR3 | exact ST3 | exact LOIMG | exact SCS | exact MI3
              | exact SZB | exact ATH | exact TH | exact CH | clear -TL; lia | clear -CL; lia
              | clear -HHI HMS; lia | clear -MSB; lia | clear -IDX NB LB; lia
              | eapply crange_sub; [exact HCS| clear; lia| clear -MSB; lia] | clear -SPL; lia | exact SPH ].
    - (* [comment removed for export] *)
      assert (PBR : S <= PB <= S + 4095 /\ PB mod 4096 = 0).
      { unfold PB, rmp_PB. pose proof (Z.div_mod (S + 4095) 4096 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (S + 4095) 4096 ltac:(clear; lia)). split; [lia| apply Z_mod_mult]. }
      assert (PER : S + k - 4095 <= PE <= S + k /\ PE mod 4096 = 0).
      { unfold PE, rmp_PE. pose proof (Z.div_mod (S + k) 4096 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (S + k) 4096 ltac:(clear; lia)). split; [lia| apply Z_mod_mult]. }
      destruct PBR as [PBR PBA]. destruct PER as [PER PEA].
      set (nZ := PE - PB) in *.
      assert (NZA : nZ mod 4096 = 0) by (unfold nZ; rewrite Zminus_mod, PBA, PEA; reflexivity).
      assert (NZR : page_round_up_Z nZ = nZ).
      { unfold page_round_up_Z, page_size. pose proof (Z.div_mod nZ 4096 ltac:(clear; lia)) as D1. rewrite NZA, Z.add_0_r in D1.
        replace (nZ + 4096 - 1) with (4095 + nZ / 4096 * 4096) by (clear -D1; lia). rewrite Z.div_add, Z.mul_add_distr_r by (clear; lia). change (4095 / 4096) with 0. clear -D1; lia. }
      assert (Ha : 0 <= PB < 2^64) by (clear -SKB PBR; lia). assert (Hn : 0 <= nZ < 2^64) by (unfold nZ; clear -SKB PBR PER PG; lia).
      assert (Han : PB + nZ <= 2^64) by (unfold nZ; clear -SKB PER; lia).
      eapply (aevtS_madvise asegs Q) with (addr := PB) (nZ := nZ).
      { exact (ki_halted KL mo3 HK3). }
      { unfold madvise_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
        repeat split; try reflexivity.
        - rewrite unsigned_lit by (clear -Hn; lia). exact NZR.
        - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by (clear -Hn; lia). unfold nZ in E. clear -E PG. lia.
        - exact PBA.
        - clear -Ha; lia.
        - unfold nZ. clear -PG. lia.
        - unfold nZ. clear -SKB PER. lia. }
      { exact (HASM mo3 HK3 PG). }
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_zeros.
      change (Z_to_bv 64 A_MADVISE_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 A_MADVISE_RET).
      change (Z_to_bv 64 PB, Z_to_bv 64 nZ) with (wa PB, Z_to_bv 64 nZ).
      (* [comment removed for export] *)
      assert (MUz : munch [(PB, PB + nZ)] m3 (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)])).
      { intros x Hx. apply (zeros_outside m3 PB nZ Ha Hn Han). cbn in Hx. clear -Hx. lia. }
      pose proof (wmono_zeros asegs m3 PB nZ Ha Hn Han _ (wmono_refl asegs m3)) as WMz.
      assert (DJz : forall A' n', (A' + n' <= S \/ S + k <= A') -> disjoint_from [(PB, PB + nZ)] A' n') by (intros A' n' H1; cbn; unfold nZ; clear -H1 PBR PER; lia).
      pose proof (cb_zeros_rezero m3 S k PB nZ Ha Hn Han ltac:(clear -PBR; lia) ltac:(unfold nZ; clear -PER; lia) SHZ3) as SHZz.
      pose proof (stk_zeros asegs m3 PB nZ Ha Hn Han _ _ ST3) as STz.
      assert (MIz : mem_inv asegs (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)])).
      { eapply (mem_inv_zeros asegs m3 PB nZ Ha Hn Han MI3). intros x Hx. apply NOROM. unfold nZ in Hx. clear -Hx. lia. }
      assert (FRz : rw_cells asegs (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)]) (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply rw_cells_transport; [exact FR3| exact MUz| exact WMz| apply DJz; cbn; clear -SKB LOIMG SPL; lia]).
      assert (HDRz : rw_cells asegs (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)]) h [C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 idx)])
        by (eapply rw_cells_transport; [exact HDR3| exact MUz| exact WMz| apply DJz; cbn; clear -SKB HHI HMS; lia]).
      assert (TSTz : rw_cells asegs (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)]) (T + 2888) [C8 mun; C8 muned])
        by (eapply rw_cells_transport; [exact TST3| exact MUz| exact WMz| apply DJz; cbn; clear -SKB TL TH; lia]).
      assert (ARRz : u64arr asegs (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)]) PA (map (Z_to_bv 64) (upd bases (Z.to_nat idx) last)))
        by (eapply u64arr_transport; [exact ARR3| exact MUz| exact WMz| rewrite map_length, upd_length; apply DJz; clear -SKB PAL PAH; lia]).
      assert (LHz : idx < n - 1 -> rw_cells asegs (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)]) last [C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 lsz); C8 (Z_to_bv 64 idx)]).
      { intros C1. eapply rw_cells_transport; [exact (LH3 C1)| exact MUz| exact WMz|].
        destruct CASES as [[E1 _]|(_ & C2 & C3 & _)]; [exfalso; clear -E1 C1; lia|]. apply DJz; cbn; clear -SKB C2 C3; lia. }
      assert (SECz : sec_cells (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)]) PA nres (n - 1) (Z_to_bv 8 0) nfr' cal' g2' g3' 0).
      { unfold sec_cells, A_SECONDARY, A_SEC_MUTEX, A_GSTATS, A_INSTANCE in *. ddestruct SEC3 as (Q1 & Q2 & Q3 & Q4 & Q5).
        repeat split; (eapply rw_cells_transport; [eassumption| exact MUz| exact WMz| apply DJz; cbn; clear -SKB; lia]). }
      assert (DSz : dealloc_statics (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)]) T CTX).
      { eapply (dealloc_statics_transport _ _ _ _ _ DS3 MUz). intros A' n' [H'|[H1 H2]]; apply DJz; [clear -H' SKB; lia| clear -H1 H2 CL CH SKB; lia]. }
      assert (GOTFz : ro_cells asegs (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)]) A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)])
        by (eapply ro_cells_transport; [exact GOTF3| exact MUz| apply DJz; cbn; unfold A_GOT_CFLAGS; clear -SKB; lia]).
      assert (LIMz : ro_cells asegs (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)]) A_MMAP_LIMIT [C8 (Z_to_bv 64 0)])
        by (eapply ro_cells_transport; [exact LIM3| exact MUz| apply DJz; cbn; unfold A_MMAP_LIMIT; clear -SKB; lia]).
      assert (MU0z : munch (ldA_W lo SP PA idx last ++ [(T + 2888, T + 2904); (S, S + k)]) m (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)])).
      { eapply munch_trans; [exact MU03|]. eapply munch_weaken; [| exact MUz]. unfold sub_fp, ldA_W; cbn [outside app]; unfold nZ; clear -PBR PER; intros y Hy; lia. }
      assert (WM0z : wmono asegs m (apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)])) by (eapply wmono_trans; [exact WM03| exact WMz]).
      pose proof (J_madvise m3 mo3 PB nZ HJ3 ltac:(clear -Ha; lia) ltac:(unfold nZ; clear -PG; lia) ltac:(unfold nZ; clear -SKB PER; lia) (HASM mo3 HK3 PG)) as HJz.
      set (mz := apply_zeros m3 [(wa PB, Z_to_bv 64 nZ)]) in *. clearbody mz.
      apply (TAIL _ mz (madvise_model PB nZ mo3) MU0z WM0z ARRz LHz SECz SHZz GOTFz LIMz (T_madv mo3 HK3 PG)); [exact HJz|].
      eapply (ld_B2m AL IMG ALWF CS CSOK) with (T := T) (CTX := CTX) (h := h) (ms := ms) (sz := sz) (idx := idx) (mun := mun) (muned := muned) (lo := lo);
        first [ exact HDRz | exact TSTz | exact TCS | exact DSz | exact CCS | exact FRz | exact STz | exact LOIMG | exact SCS | exact MIz
              | exact SZB | exact ATH | exact TH | exact CH | clear -TL; lia | clear -CL; lia
              | clear -HHI HMS; lia | clear -MSB; lia | clear -IDX NB LB; lia
              | eapply crange_sub; [exact HCS| clear; lia| clear -MSB; lia] | clear -SPL; lia | exact SPH ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End LargeFreeS.

End ARUN_1.
