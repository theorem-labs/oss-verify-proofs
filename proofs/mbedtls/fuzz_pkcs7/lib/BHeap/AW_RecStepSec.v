(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR AW_FreeFam.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_Munmap AW_Poison AW_Populate
     AW_DepotA AW_DepotB AW_DepotC AW_DepotInv AW_DepotTop AW_MallocA AW_AllocA AW_AllocB AW_MallocB AW_MallocC AW_ClassId AW_Combined AW_Refill AW_Large
     AW_CfgS AW_CfgDefs AW_PopulateCfgS AW_PoisonBig AW_PoisonBigCfg AW_SMalloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_QPut AW_Enqueue AW_CbRecycle AW_CbRecycleS AW_LargeFree AW_MunmapCfg AW_LargeFreeCfg AW_RecChunk AW_RecChunkS AW_RecStep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs AW_FakeRep HMLib HM HMFrame AW_FreeHM AW_FreeHMS AW_FreeHMX AImgW AW_DepotCfg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_RecStepSec () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_ro"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecChunkS.rs_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_sb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctx"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Large.large_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_recs"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_size"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.WFR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.HMq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.RIq"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.S"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_K"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_CS"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHMX.fkeepR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MunmapCfg.wmono_out"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_QUARANTINE"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "Corelib.Init.Datatypes.false"; "Stdlib.Lists.List.nth_error"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.SH"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_elems"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_hdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_1.RecStepSec.sec_step_post"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.A_CB_RECYCLE"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

(* [comment removed for export] *)
#[using="Type"] Lemma hm_ro_freeS : ltac2:(CDefT.buildp (gd_tbl_AW_RecStepSec ()) "PL,$0.Pm,P,(1.&40.)(2.(1.&8.))P,(3.R2.R1.)(4.(1.&40.)Lcan,(1.&40.)(4.(1.&8.)Ldd,(1.&8.)(4.(1.&8.)Lmadv,(1.&8.)(5.(6.R5.(7.R6.)(8.R6.)(9.R6.)R3.R2.R1.)(:.R5.(;.R6.))))))")
(* [comment removed for export] *).
Proof.
  intros L m RO. ddestruct (hm_ro_free L m RO) as (RPS & (can & dd & madv & RSM) & LST). dexists can, dd, madv. split; [| exact LST].
  destruct RPS as [RLS MF8]. ddestruct RLS as (PS & RIC & MW & TS & POI & GS & GD & DY).
  pose proof RO as RO'. unfold hm_ro in RO'. cbn zeta in RO'.
  ddestruct RO' as (MSEG & ALLOCA & _).
  split; [| split; [| split; [exact POI| exact RSM]]].
  - ddestruct PS as (_ & _ & SBC). exact SBC.
  - unfold dealloc_statics. split; [exact MF8| exact TS].
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L2433080580.19 L27601815734.17L30119044422.19L30119092429.17L30119176542.16L30119273798.15L37576877159.19L53267360048.16L8550158707.19 L8550257011.15 L8550292843.16 00000J00\01601K01^01n02H02X03203B03RS1A1i1j2l12l21d1D2LI2GE2DLS1A1i1j2l11D2LI2GES1A1i1j2l12l21d1D2LI2GE2DLS1A1i1j2l12l21D2LI2GES1A1i1j2l12l22LI2LTS1A1i1j2l12LI2JLS1A1i1j2l12l21d1D2LI2GE2DLS1A1i1x2l12l22LIS1A1i1j2l12l21d1D2LI2GE2DLS1A1i1j2l12LI2JLS1A1i1j2l12LI2LT". (* [comment removed for export] *)
#[using="Type"] Lemma swap_remove_nth : forall {A} (l : list A) i x lst, nth_error l i = Some x -> nth_error l (length l - 1) = Some lst ->
  forall j y, nth_error (swap_remove i l) j = Some y -> (j < length l - 1)%nat /\ ((j = i /\ y = lst) \/ (j <> i /\ nth_error l j = Some y)).
Proof.
  intros A l i x lst H HL j y Hj.
  destruct (nth_error_split_last l i x H) as [(l1 & l2 & lst' & E & LI)|(l1 & E & LI)].
  - assert (EL : lst' = lst).
    { rewrite E in HL. replace (l1 ++ x :: l2 ++ [lst']) with ((l1 ++ x :: l2) ++ [lst']) in HL by (rewrite <- app_assoc; reflexivity).
      rewrite length_app in HL. cbn [length] in HL. rewrite Nat.add_sub, nth_error_app2, Nat.sub_diag in HL by lia. cbn in HL. congruence. }
    subst lst'. rewrite E, <- LI, swap_remove_mid in Hj. rewrite E. rewrite length_app. cbn [length]. rewrite length_app. cbn [length].
    destruct (Nat.lt_ge_cases j (length l1)) as [LT|GE].
    + rewrite nth_error_app1 in Hj by exact LT. split; [lia|]. right. split; [lia|]. rewrite nth_error_app1 by exact LT. exact Hj.
    + rewrite nth_error_app2 in Hj by exact GE. destruct (j - length l1)%nat as [|d] eqn:D.
      * cbn in Hj. split; [lia|]. left. split; [lia| congruence].
      * cbn in Hj. pose proof (nth_error_Some_length _ _ _ Hj) as DL. split; [lia|]. right. split; [lia|].
        rewrite nth_error_app2 by lia. replace (j - length l1)%nat with (S d) by lia. cbn [nth_error]. rewrite nth_error_app1 by exact DL. exact Hj.
  - rewrite E, <- LI, swap_remove_last in Hj. rewrite E, length_app. cbn [length]. pose proof (nth_error_Some_length _ _ _ Hj) as JL.
    split; [lia|]. right. split; [lia|]. rewrite nth_error_app1 by exact JL. exact Hj.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma swap_remove_map : forall {A B} (f : A -> B) (l : list A) i x, nth_error l i = Some x -> swap_remove i (map f l) = map f (swap_remove i l).
Proof.
  intros A B f l i x H. destruct (nth_error_split_last l i x H) as [(l1 & l2 & lst & -> & <-)|(l1 & -> & <-)].
  - rewrite !map_app. cbn [map]. rewrite map_app. cbn [map]. rewrite <- (length_map f l1) at 1. rewrite swap_remove_mid, swap_remove_mid. rewrite map_app. reflexivity.
  - rewrite map_app. cbn [map]. rewrite <- (length_map f l1) at 1. rewrite swap_remove_last, swap_remove_last. reflexivity.
Qed.

Section RecStepSec.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Variable FF : ffam AL.

  (* [comment removed for export] *)
  Definition sec_step_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : ahst) (k : chunk) (si : nat) (LF : list (Z * Z)) (bc : bnode) (i : nat) (C lo : Z) (QS : list (Z * Z)) (m : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecStepSec ()) "Lcf,$<.(4.$=.Lms',$=.(4.$>.Lmo',$>.(4.(1.&40.)Lt0,(1.&40.)(4.(1.&40.)Lt1,(1.&40.)(4.(1.&40.)Lt2,(1.&40.)(4.(1.&40.)La0,(1.&40.)(4.(1.&40.)La1,(1.&40.)(4.(1.&40.)La2,(1.&40.)(4.(1.&40.)La3,(1.&40.)(4.(1.&40.)La4,(1.&40.)(4.(1.&40.)La5,(1.&40.)(4.(1.&40.)La6,(1.&40.)(4.(1.&40.)La7,(1.&40.)(4.(1.&40.)Lt3,(1.&40.)(4.(1.&40.)Lt4,(1.&40.)(4.(1.&40.)Lt5,(1.&40.)(4.(1.&40.)Lt6,(1.&40.)(4.P,(1.&40.)(2.(1.&8.))Lm',P,(1.&40.)(2.(1.&8.))Zh',$?.(10.O:.O9.O8.)Zhb,$11.(12.O9.)Zms,$11.(13.O9.)(5.(14.$<.R16.(15.R15.R14.))(5.(14.$=.R15.(16.(17.O1<.(18.&40.O1;.)O1:.O19.R13.R12.R11.O18.O17.R10.R?.R>.R=.R<.R;.R:.R9.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R8.R7.R6.R5.)O<.(19.O1<.)O;.(1:.(1.&40.))R4.(1;.$1<.)))(5.(1=.VhAR,R3.)(5.(1>.VhAR,R3.O7.R4.)(5.(1?.VhAR,R3.O4.(20.(21.$22.$23.)(24.$22.$23.O6.(25.O5.)))R4.)(5.(26.VhAR,VAL,VFF,R3.R14.)(5.(27.R4.R14.)(5.Px,$11.P,(28.VhAR,VAL,VFF,O:.R1.)P,(29.(5.(2:.R4.R2.)(2;.R2.(2<.R4.R3.))))(28.VhAR,VAL,VFF,R6.R3.)(5.(2=.(2>.O:.)(2?.O:.)O2.(30.$31.(21.$11.$11.)Lsh,$31.(24.$11.$11.(32.R1.)+20.)(33.(34.O:.)))(35.(36.O:.))(37.(36.O:.))O3.O1;.O1.R4.)(5.(38.R2.R1.O1.R4.)(5.(39.$1<.R4.)(3:.$1<.R4.O3.O1;.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "07B0@L10133210439.1  L10444875818.11 L10444876330.11 L1211457002.5   L12224199946.1  L12407585751.0  L1249083665.6   L12535663877.22 L12811172173.24 L13430471528.1  L13462993804.22 L13980663862.10 L13980663862.9  L14305591216.5  L14736408896.1  L14866254130.2  L14886739788.0  L15314803930.3  L15456529577.0  L1546429141.24  L15539138780.2  L15702086826.2  L15805189094.7  L15805429341.6  L15805429599.5  L15805429726.6  L15805814301.4  L15807334636.7  L15807378922.7  L15807567456.7  L15807567469.5  L15807567470.5  L15807567484.5  L15994321233.1  L16073199982.5  L16073199986.7  L16073199999.5  L16073277774.3  L16073405176.6  L16073428990.6  L16075459320.5  L16075574516.5  L16075616333.4  L16075616460.6  L16075616591.6  L16077102994.1  L16087976317.4  L16088052170.4  L16088052170.6  L16487879465.7  L16504374356.6  L16538553883.8  L16548910673.1  L16928325228.23 L16928389484.23 L17120848823.0  L17726240765.22 L177791751.9    L17844171720.7  L17844490306.7  L17846735478.6  L17846735607.5  L18074539527.3  L18507921458.18 L18507923006.25 L18507923006.31 L18507923260.5  L18928770119.3  L18928850760.3  L18980863341.6  L18982913389.9  L18985043551.5  L18985043551.6  L18985516776.6  L18986788506.10 L18986788506.4  L18986788506.7  L18986788506.8  L18986788506.9  L19346787921.10 L19346787921.6  L19346787921.9  L19348479126.24 L19505738635.10 L19505739393.10 L19505983629.23 L19505984266.28 L19505984266.6  L20568210009.24 L20850716528.4  L21156871153.340L21422566436.22 L21437879877.22 L22054880513.7  L2217282300.5   L22243997773.7  L22284614476.22 L22815167311.22 L22979086316.3  L23421840920.22 L23489289455.2  L23489707691.7  L23489707816.7  L23489707945.5  L23489807644.7  L23489921808.6  L23491951900.7  L23491969050.7  L23492087466.5  L23492265614.7  L23492267534.7  L23492271754.7  L23492271766.9  L23492271771.7  L23502405166.10 L23502405166.6  L23502405166.8  L23502587545.6  L23502635694.6  L24274040973.4  L24361222476.1  L2460148965.1   L24618242870.7  L24812922353.4  L25003717198.2  L25070469102.3  L2535255449.5   L2537155652.6   L25576084386.18 L25576084910.25 L2566926351.6   L25787593781.2  L26001732169.0  L264119316.1    L26421954657.1  L26642860061.3  L26642860061.6  L26642860061.7  L26642860061.8  L26656922348.8  L26657023978.8  L26657211488.9  L26657211501.7  L26657211516.7  L2667604927.3   L26940997473.3  L26940997473.9  L27177722825.3  L27609046281.7  L28202320067.10 L2823407829.24  L28601420974.31 L28601421609.4  L28817604516.23 L28817668260.23 L29300458413.13 L29658500002.18 L29658500526.25 L29712185554.5  L30278463682.7  L30641017874.6  L30980499594.3  L30980566273.4  L31067085492.2  L31297199676.2  L3151035517.23  L3151231869.23  L32337936534.7  L32816903344.8  L32817195580.6  L32817223482.5  L32819238029.6  L32819238158.6  L32819238287.4  L32851757565.24 L33470790221.11 L33729609334.339L34175831000.22 L34326450181.3  L35267160734.3  L35269483449.1  L35390068370.3  L35521637653.13 L3573330068.1   L3663757732.4   L3664230675.4   L3665822358.6   L3665936272.6   L3666157824.5   L3666157841.5   L3666157852.7   L3667966614.5   L3668016282.5   L3668099107.4   L3668099234.6   L3668099361.6   L3668345764.2   L3670650876.1   L37151845358.5  L37267855607.1  L37427462543.22 L37432942991.6  L37439645930.18 L37622523289.16 L37684080249.7  L38039306308.3  L38111654711.4  L38548352841.24 L39012169098.3  L39012169098.6  L39012169098.7  L39012169098.8  L39012169098.9  L39013700943.4  L39015765629.8  L39017901693.5  L39036147378.8  L39189381960.5  L39258897520.13 L39332637397.0  L39742211683.7  L39930031418.5  L39931948814.6  L39931948943.4  L40244184078.0  L40401253682.0  L40409225607.0  L4097861678.13  L4098107821.23  L4098107946.10  L4098107946.28  L41008919275.5  L41008936668.5  L41009122923.10 L41009122923.6  L41009122923.7  L41013244757.6  L41013327193.7  L41013464814.7  L41013464941.6  L41013465068.5  L41013849258.2  L41015062223.7  L41015062227.9  L41015062238.7  L41015064267.7  L41015066187.7  L41015279343.5  L41015357535.7  L41015381337.7  L42144913193.0  L42301244845.13 L43148692123.361L4345062573.3   L43675124393.8  L4368349602.25  L4368351150.18  L43917672745.5  L43917672872.5  L44000350775.23 L44000548151.23 L44033659772.25 L44033659772.31 L44033659901.10 L44033660272.18 L44516683189.5  L45117830018.6  L45156242767.4  L45838343960.10 L45848778520.12 L46361058564.4  L46530511933.22 L4689305478.0   L47736998116.22 L47934820836.14 L48426933680.12 L48706364032.12 L48706641925.28 L48706641925.9  L48706642818.23 L48706642818.25 L48706642818.31 L48706643342.18 L48727683099.5  L48834838394.5  L4921969219.0   L49331792262.0  L4966970113.4   L49720189939.14 L4973953509.1   L50508257982.2  L50569607898.18 L50625259979.7  L50625259979.8  L50673629481.12 L50752764183.5  L51322266494.2  L51353969794.3  L5151451470.25  L51992335728.23 L51992531568.23 L52590183151.5  L52595281469.4  L52629805180.18 L53340549350.13 L53853976466.2  L53874525311.23 L53874721663.23 L53915181234.3  L54056022013.22 L5423245545.6   L5423245557.8   L5423245560.6   L5423247597.6   L5423249517.6   L5423462601.4   L5423543929.6   L5423565695.6   L5425494637.1   L5425624435.5   L5425705855.6   L5425842376.6   L5425842507.6   L5425842634.4   L5429687501.6   L5429687541.8   L5429702906.5   L5429889101.5   L5429889101.7   L5429889101.9   L54693692236.22 L55099840816.5  L55588686165.0  L55653771692.11 L55653771692.28 L55653771819.24 L55653771819.25 L55653771819.31 L55653772327.18 L55654050347.15 L55850856762.4  L57098271163.5  L57098590764.9  L57100722732.8  L57103120859.6  L57103120859.7  L57103120859.8  L57103120859.9  L57104458153.9  L57104914718.7  L57104914718.8  L57104914718.9  L57694036910.25 L57694037410.18 L57735177252.22 L57749966405.22 L58002214189.4  L58282292191.6  L58493861334.25 L58643601785.8  L58709757573.24 L59046666015.0  L59127647055.22 L59308579027.11 L59314955108.4  L59351898886.0  L59551301595.7  L59581794677.8  L59582132967.5  L59582134887.5  L59583934837.5  L59585407618.3  L59585407618.5  L59585407618.6  L59585407618.7  L59585407618.8  L59585407618.9  L59588119111.4  L59588119111.6  L59588119111.8  L59588326128.6  L59646417381.1  L59656497464.15 L59727773228.2  L59750573592.22 L60478032893.24 L60539639815.9  L61962322274.5  L62098093452.2  L63063336772.1  L63181313848.2  L63209370121.5  L63209370379.4  L63209370506.5  L63211352510.6  L63211375800.6  L63211672116.7  L64190140897.28 L64190140897.6  L64190141030.23 L64190141030.31 L64190146896.6  L64281234188.3  L64477054256.1  L64607904317.7  L64778138904.7  L64778327698.6  L64778365844.5  L64780244007.3  L64780244134.5  L64801158552.5  L65271643703.0  L66081664838.10 L66158380935.0  L66465933892.1  L66509622069.4  L66509800209.6  L66509802385.6  L66509806340.6  L66509806345.8  L66509806357.6  L66510010499.6  L66510095749.6  L66511784337.1  L66512026166.4  L66512026295.6  L66512026420.6  L66512126083.6  L66512176783.5  L66515977993.8  L66515978033.6  L66515993350.5  L66516335537.5  L66516335537.7  L66516335537.9  L66518733192.4  L66520975981.3  L66796818299.3  L66920220922.4  L68165641594.9  L68505009752.362L6965376758.10  L6965376758.4   L6965376758.7   L6965376758.8   L6965376758.9   L6975171841.5   L6977230081.9   L7087565789.1   L7138864904.0   L7436297725.24  L777962750.0    L7794465351.1   L7904621526.4   L7904623431.4   L8209290301.3   L8464775655.24  L8884988880.8   L8886950629.5   L9166243046.25  L9286897360.18  L9471806705.12  L9471806705.28  L9471807350.23  L9471807350.31  L9472053239.19  00000300Z01A01P01S01T01d02F03303603T03n04J04K04O04V04W04a04b05D05K05R05S05T05U05V05W05X05Y05Z05i06806G06J06K06L06M06X06Y06Z06[06\06]06^06_06`06a06b06c07907E07P07S08708[08\09O09k0:B0:C0:D0:E0:N0:k0;X0<e0=70==0=C0=D0=E0=F0=]0=^0=_0=`0=a0=b0=c0>90>O0>e0?Q0@20@S0AJ0B?0BV0C>0CD0EA0Ek0FN0Fg0G>0GW0H50I40I:0IX0IY0IZ0I[0I\0I]0I^0I_0I`0Ia0Ib0Ic0Id0Ie0If0Ig0Ih0Ii0Ij0Ik0J70J:0J=0JO0J\0Jc0Jn0K=0KP0Ko0L`0M80M<0M=0M@0MC0MD0ME0MF0MG0MH0MI0MJ0MK0ML0MV0M^0N@0NJ0N^0O?0Oa0PU0P`0Q>0Q\0R10RP0SA0SP0Sl0TC0TL0TY0T_0Te0US0VA0VJ0VK0VL0VM0VN0VO0VP0W;0W`0Y]0Z;0ZE0ZQ0ZU0Z_0[00[30[40[@0[A0[B0[C0[D0[E0[F0[G0[H0[I0[J0[P0[Q0[h0[k0\h0]<0]Y0^I0^f0^n0_80_`0_a0_b0_c0_d0_e0`30`40`50`V0`d0aI0aJ0a[0ak0al0am0an0ao0b00ba0c]0dA0e60eI0eJ0eK0eL0eM0eN0eO0eP0eQ0eR0eS0eT0eU0eV0eW0eX0eY0eZ0e[0e\0f<0h<0hF0hZ0iB0i_0i`0j00jR0k40k_0m00mU0n40nA0nY0nl0oJ0oj10410f10g11Q12@12h13O14@14Z15N16617;17X17f18518618718F19519819@19]1:01:D1:h1;91;A1;J1;h1<E1<b1=11=71=T1=e1=n1>O1?01?:1?l1?m1?n1?o1@01@11@21@31@41@51@61@71@81@91@:1@;1@X1@Y1@Z1@[1@\1A:1AL1AM1Ao1Bo1Cd1DS1Ek1FN1G>1GK1GZ1G[1G\1G]1G^1G_1G`1Ga1Gb1H<1H=1H[1I81Ic1JE1JU1Jk1KI1Kd1LF1LG1MD1Mg1N31N41NL1NM1N_1O11O21O31O41O51O61O71O81O91O:1O;1O<1O?1P81P?1P]1Q?1Q^1R11R91R<1RD1RS1RT1RU1RV1RW1RX1SB1SQ1T51U:1UM1UY1U^1V41V51V61VI1VJ1VK1VY1VZ1W71W81W;1W<1W=1W>1W?1W@1WA1WB1WC1WD1WE1WF1WG1WH1WI1WJ1WK1WL1WM1WN1WO1WY1Wc1Wm1X71XV1ZV1ZW1ZX1ZY1ZZ1Z[1[11[21[51[61[a1[b1[e1\31\A1\K1]61]N1]Z1^?1_91_^1`l1aW1b\1cTS1hS1h2SP3CBP1C2lo3CB03CB13CHI3LOL3SPL3ZTSS1h2SP3CBP1C2lo3CB03CB13CHI3LOL3SPL3ZPSS1h1k2hb2ms3ZsHS1hSS1h2kf2ii2I13SZ1S1h1k2hb2ms3ZTC3shl4last2kk2Sh3ZCPS3hAR1h1k2hb2ms2E53shl4last4LGEO4PALH1x2Hx2NWS1hS1h1k2hb2ms3CX03shl4last2kk2ShS3hAR1h3RI12c'2Q12D12D22D3S3hAR2k'2F32F64NFX'2D12D22D3FS2k'S1h3ZTCSS1h2si3SILSS3hAR1h1k2hb2ms3shl4last4PALH1x2NWS2k'2F3S2k'2C'FFFFFFFFS1h1k2hb2ms3ZsCS1h1k2hb2ms3ZsFS1h1k2hb2ms3ZsTS1hFFFS1h3WS33WS4FFFFFFFFFFFS1h2k'3RL'3XAB1A2HA2Q2S1h2kf2ii2I2S1h1b2S12Q2S1hS1k2hb2ms3shl4last2kk2Sh3SKB1b2Y42Y5S1k2hb2ms3shl4last2kk2Sh3SKB1b2Y42Y5SS1h1k2hb2ms3shl4last2kk2Sh3SKB3LM44Zdt43ZsD3YlD3DTLS1h2SP2lo3LOL4SPHI2sh2Y33M4jS1h1k2hb2ms3B6a3B6b3ZsHFFFS1h2si2JLS1k2si2hb2ms3shl4last1A2n'2H5S3hAR1h1k2hb2ms2E53shl4last4LGEO4PALH1A2n'2H2S1h1k2si2hb2ms2T03SIL3ZsT4rest3shl4last5bases2kk2Sh3SKB3LM43YlT1A2n'2H12H22H3S3shl4last1A2n'2H5S1k2msS1k2hbFFFS3hAR1h5bases4PACE4LB40FFFFFFS1h3B6c2c'2Q22k02S12D1S2k'3RZ'2F53XAB3UIN2D1S1h3B6c2c'5AUMU'2Q22D1S3hAR1h1k2SP2lo2hb2ms3LOL4STK03shl4last1x2HxS1h2k'3EL'3EH'3XAB1A2n'2HA3HB'2Y1S1h2k'3EL'3EH'3XAB1A2n'2HA3HB'2Y7S3hAR1h1k2hb2ms2T02E53shl4last2kk2Sh4PALH1A2n'2H12H22H3S3hAR1h1k2hb2ms3B6c3ZTH3shl4last2kk2Sh1A2n'2H12H23ZPHS1h4Zfs11A2n'2H12H23ZFPS3hAR1h1k2hb2ms2E53shl4last4PALH1x2Hx2NWS1k2hbS3hAR1h1i1k2si2SP1n2hb2ms2xs2bs3LXS3LBS4ncks3WS33SIL3st03nfr3cal3st32L33bsl2L44rest3shl4last5bases2kk2Sh4LENZ3xs'4LXS43all2ILS1h1k2hb2ms3CX03ZsC3shl4last2kk2Sh3SKB3ZCBS1h1k2hb2ms3shl4last2kk2Sh4Zdt13ZPDS1k2hb2ms3shl3MSB3LM43YssS1k2hb3HB02DH3DHB5HIGHMS1h3shl5bases4LB403LM42YpS1h1k2hb2ms3shl4last2kk2Sh3DTLS1h1k2SP2lo2hb2ms3LOL3shl4last2kk2Sh3SKB4Zdt34Zdt43ZsD3DTL4SPHIS1k2hbS1h1k2hb2ms3ZsC3shl4last2kk2ShFFFFFFFFFFFFFFFFFFFS1k2hb2ms2E5S1xS1hS3hAR3shl3LHl4BIGlS1h2si3SIL2EQS2k'2C'S2k'2F43UINS1k2hb2ms2sh2Y5S1k2hb2ms2sh2Y53M4jS1h1k2si2hb2ms3shl4last1A2n'2H2S3hAR1h1k2hb2ms2T02E53shl4last4PALH1A2n'2H12H22H3S1h2si3SIL4rest5bases2LBS2k'SS1kS1hFFFFFFFFFS1k2ms3MS4S1h1a2HaS1h2si3SIL4rest5bases2LB4LB401a2HaS1h2c13Hc1S1h1k2hb2ms2c'2k02SDS1h1k2hb2ms2c'5AUMU'2Q12Q22Q43HLHS3hAR1h1k2hb2ms3shl4last4PALH1x2NWS1h1k2si2hb2ms3SIL4rest3shl4last5bases2kk2Sh1A2n'2H3S1h1A2n'2H2S1k2hb2ms3shl4last2kk2Sh1b3NB0S1k2hb2ms3shl4last2kk2Sh1b3BL0S3hAR1k2hb2ms1e2R12R2S1h1k2si2hb2ms3shl4last1A2n'2H2S3hAR1h1k2hb2ms2T02E53shl4last4PALH1A2n'2H12H22H3S1k1n2KN3RZB2R8S3hAR3shl3LM45CEILl3LHl4BIGlS3hAR3shj2M44POSj5CEILjS1h2si2JLS1h2si3SIL2NES1a2HaS1k2hbS1h1k2SP2lo2hb2ms3LOL3shl4last2kk2Sh4SPHI1b2Y3S1h1k2SP2lo2hb2ms3LOL3shl4last2kk2Sh4SPHI1b2Y3S1h2c'2Q2FFFFFFS3hAR1h1k2hb2ms2T02E53shl4last4PALH1x2Hx2NWS3hAR1h3RI12c'5AUMU'2Q12k02S24CSR'2D1S3hAR1h1i1k2si2SP1n2hb2ms2xs2bs3LXS3LBS4ncks3WS33SIL3st03nfr3cal3st32L33bsl2L44rest3shl4last5bases2kk2Sh4LENZ3xs'4LXS43all2ILS1h1k2hb2ms3ZsC3shl4last2kk2ShS1k2ms3MSBS2k'3RZ'3UINS2k'S1h2c13Hc1S3hAR1h2c'3Hc'2Q4S1hFS3hAR1h4PALHFFFFFFFFFFS1h2T0FS1k2hb3HB02DH3DHB5HIGHMS1hS1h1k2SP2lo2hb2ms3LOL3CX03ZsC3shl4last2kk2Sh3SKB3ZCS3ZCB4SPHIS1k2hb2ms3shl4last1YS1k2si2hb2ms3shl4last1A2n'2H3S1h1k2SP3CBP1C2lo2hb2ms3CB03CB13CHI3LOL3ZsS1x2HxS3hAR3shl4last4LGEO2sh2Y63M4jS1h1j2JLS1k1n2R41HS3hAR1h1k2hb2ms2E53shl4last4PALH1x2Hx2NWFFFFFS1h5bases4LB40FFS3hAR1k2hb2ms6HBCEIL4HBLH3ACB3MSBS1k2hb2ms1a2HaS3hAR1k2hb2ms2kk2Sh3SKB2sh2Y43M4j3LHjSS1h2c'4MFB'2Q32Q4S1k1n2ms3MSB3N2BFFSSSS3hAR3shl4last4LGEO2k'3EL'3EH'3XAB1A2n'2HA3HB'2Y6S3hAR1h1k2hb2ms2E53shl4last2kk2Sh4PALH3LM43YlB1A2n'2H12H22H3S3hAR1h3shl4last4LGEO3YlF1A2n'2H12H2S3hAR1h1k2hb2ms3B6c3shl4last2kk2Sh3LM43YlH1A2n'2H12H2S3hAR1h2lo3LOL4STK0FFFFFFFFFFFFFFFFFFSS3hAR1k2hb2ms2E12E22E32E52E63ACBS3hAR1h1i1k2si2SP1n2hb2ms2xs2bs3LXS3LBS4ncks3WS33SIL3st03nfr3cal3st32L33bsl2L44rest3shl4last5bases2kk2Sh4LENZ3xs'4LXS43all2IL2jbS1h2si3SILS1h1b2S22Q12Q45AUMU'S3hAR1h1k2hb2ms2E53shl4last4PALH1A2n'2H2S1k2si2hb2ms3shl4last1A2n'2H6FS3hAR1k2hb2ms2E6S1h1k2hb2ms3shl4last2kk2Sh1b2Y12Y7S1h1k2hb2ms3shl4last2kk2Sh1b2Y12Y7S3hAR1h1k2si2hb2ms2E53shl4last4PALH1A2n'2H2S1h1k2si2hb2ms2T03SIL3ZsT4rest3shl4last5bases2LB2kk2Sh4LB403ZTP3SKB1A2n'2H12H22H3S1h2si3SIL4rest5bases2LB4LB401A2n'2H4S1h1k2si2hb2ms3shl4last1A2n'2H4S1h1k2hb2ms1YS1h2si3SIL4rest5bases2LBS3hAR3shl3LM45CEILlS1k2hb2ms4LOWM2DH3DHB3DMS4DMSBS3hAR1k2hb2ms2E62DH3DHB3DMS4DMSBS1k1n1H2R8S1h1k2hb2ms3CX03ZsC3shl4last2kk2Sh3SKB3LM43ZCB3YlCSS1h1k2hb2ms3CX03ZsC3shl4last2kk2Sh3SKB3ZCBS1h1k2hb2ms2c'5AUMU'2Q12Q22Q43HLH2k02S12S24CSR'S3hAR1h2SP3CBP1C2lo3CB03CB13LOL3SPL4STK0S1k2hb2ms2k'3EL'3EH'3XAB1A2n'2HA3HB'2Y5S3hAR1h1k2hb2ms3B6c3ZsH3shl4last2kk2Sh1A2n'2H12H2S1h1k2hb2ms3ZsF1A2n'2H12H2S3hAR1h1k2hb2ms2E53shl4last2kk2Sh4PALH1A2n'2H12H22H3S3hAR1h1k2hb2ms2E53shl4last4PALH1A2n'2H2S1h1k2si2hb2ms2T03SIL3ZsT4rest3shl4last5bases2kk2Sh3SKB1A2n'2H12H22H3S1k2si2hb2ms3shl4last1A2n'2H7S1k1n2KN2N22R4S1k1n2KN3RZB2R8SSS3shl4last1a2HaS1h1k2SP3CBP1C2lo2hb2ms3CB03CB13CHI3LOL3SPL3ZsSS1hS2kl3KNlS1k2si2hb2ms3shl4last1A2n'2H3S1k2hb2ms3MS82k'2SDS1h1k2hb2ms2c'2D32SDS3hAR1k2hb2ms2E52E63DHB4DMSB3ACB3MSBS1k2hb3HAB2k'3E1'S2c'3Hc'S2si1j2NES3hAR1k2hb2ms3shl4last1A2n'2H2S1k2hb2ms3shl4last2kk2Sh1b2Y5S1k2hb2ms3shl4last2kk2Sh1b2Y5S1k2hb2ms2k'2XDS1k2msS1k2si2hb2ms3shl4last1A2n'2H3S3hAR1h3B6a2c'2Q2S3shl3LM4S1k2hb2ms3shl4last2kk2Sh3LM41b2Y6S1k2hb2ms3shl4last2kk2Sh3LM41b2Y6S1h2c13Hc1S1h1k2hb2ms3CX03ZsC3shl4last2kk2Sh3SKB3LM43ZCB3YlCFFFFFFFFFFFFFFFS1h2SP3CBP1C3CB03CB13CHI4STKHFFFFS1h1k2hb2ms3CX03shl4last2kk2ShS2SP3CBP1C3CB03CB1SS1h2SP2lo3LOL4Zfs34SPHI1A2n'2H12H2S3hAR1h1k2SP2lo2hb2ms3LOL3B6c3shl4last2kk2Sh3ZHS4SPHI1A2n'2H12H2S3hAR1h1k2SP2lo2hb2ms3LOL4STK03shl4last2kk2Sh1A2n'2H2S3hAR1h1k2SP2lo2hb2ms3LOL4STK03shl4last1A2n'2H2S1h1k2si2SP2lo2hb2ms3LOL2T03SIL3ZsT4rest3shl4last5bases2kk2Sh3SKB3ZTS4SPHI1A2n'2H12H22H3S1k2si2SP2lo2hb2ms3shl4last1A2n'2H1S1h2SP2lo3LOL4SPHI2k'3EL'3EH'3XAB1A2n'2HA3HB'2Y3S1h2si3SIL2NES1h1k2hb2ms3ZsSFFFFFFFFS1h1k2hb2ms3ZsP5bases4LB40FS3hAR1k2hb2ms3shl4last1A2n'2H2S1k2si2hb2ms3shl4last1A2n'2H3S1h1k2hb2ms3shl4last2kk2Sh3SKB4Zdt43ZsD3DTLS1h1k2hb2ms3ZTC3shl4last2kk2Sh3ZCPS1h2sh2Y13M4j2Y7S3shl4last2k'1A2HA3EL1S3hAR1k2hb2ms3shl4last1A2n'2H1S1h2SP3CBP1C2lo3CB03CB13CHIS3hAR1h1k2hb2ms3shl4last4PALH1x2NWSS1h1k2SP2lo2hb2ms3LOL3CX03ZsC3shl4last2kk2Sh3SKB3ZCS3ZCB4SPHIS1k2hb2ms5HBPOS2DH3DHB1x2Hx2LT1H2H0S1h2si3SIL1ESS1h2SP3CBP1C3CB03CB13CHIFS1h5bases4LB403ZCPS1h5bases4LB403ZTPFFFFFFFFFFFS1hS3hAR1h2SP3CBP1C2lo3CB03CB13CHI3LOL3SPL3shl4last4LGEO3YlSS1h3FS0S1h1k2hb2ms3shl4last2kk2Sh3ZsDS3hAR1h1k2hb2ms3shl4last4PALH1x2NWS1h2k'3RH'1A2n'3HB'2Q12Q45AUMU'S1k2ms3MS43DMS4DMSBS1h4restS1hS2k'3RZ'S1k2hb2ms2E22E3FFFFFS3hAR1h1k2hb2ms3B6c3shl4last2kk2Sh1A2n'2H1S1h3FS01A2n'2H1S3hAR1k2hb2ms3shl4last2kk2Sh1A2n'2H1S1h1k2si2hb2ms2T03SIL3ZsT4rest3shl4last5bases2kk2Sh3SKB1A2n'2H12H22H3S2k'2F53XAB1A2n'2HAS2sh3M4j3LHjS3shlS1k2hb2ms3MSB3shj2M41YFFS1k2hb4RZ163HAB3HHDFFS1k2hb2ms1a2HaSS1k2hb2ms2k'2F12F22F32XD4NFX'SS1hFFFFFFFFFFFFFFFFFFFFS1k1n4NS32S1h2si3SILS1h2si3SILS1k1n1H2R8S1h4ncks3WS43WS54rest3PAL5basesS3hAR1h1i1k2si2SP1n2hb2ms2xs2bs3LXS3LBS4ncks3WS33SIL3st03nfr3cal3st32L33bsl2L44rest3shl4last5bases2kk2Sh4LENZ3xs'4LXS43all2IL2jbFFFFFS1h4ncks4rest5bases2LBFS1kSS3hAR1h1k2hb2ms2T02E53shl4last4PALH1x2Hx2NWSS1hS1h3shl3LM42YcS1h3shl3LM42YtS1h2si3SILS3hAR1h1k2si2hb2ms2E53shl4last4PALH1x2Hx2NWS3hAR1k2hb2ms2E53ACB3MSBS1k2hb2ms2E5S3hAR1h1k2hb2ms3shl4last4PALH1A2n'2H3S3hAR1h1k2SP3CBP1C2lo2hb2ms3CB03CB13LOL3SPL4STK02kk2Sh3SKBS1h1k2hb2ms2kk2Sh3SKB4Zfs41A2n'2H12H2S3hAR1h1k2SP2lo2hb2ms3LOL3SPL3B6c4STK03ZsH3shl4last2kk2Sh3SKB3ZHB4SPHI1A2n'2H1S3hAR1h1k2hb2ms3shl4last2kk2Sh4PALH1A2n'2H3S1h1k2si2hb2ms2T03SIL3ZsT4rest3shl4last5bases2kk2Sh3SKB1A2n'2H12H22H3S3hAR1k2hb2ms2kk2Sh3SKB2k'2F53EL'3EH'3XAB1A2n'2HA3HB'2Y4". (* [comment removed for export] *)
  #[using="IMG ALWF ASB"] Theorem rec_sec_step : ltac2:(CDefT.buildp (gd_tbl_AW_RecStepSec ()) "PQ,P,$<.SpPra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Ph,$?.PLF,(3;.(21.$11.$11.))PQS,(3;.(21.$11.$11.))Pbc,$22.Pi,$23.Pk,$3<.Psi,$23.PSP,$11.PCBP,$11.PC,$11.Plo,$11.PF,(3=.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))Pmo,$>.ZL,$0.(2>.R?.)P,(1=.VhAR,R10.)P,(2:.(3>.R11.)$3?.)P,(40.$3<.R=.(41.R12.))P,(14.$11.(42.R>.)$43.)P,(14.$44.(45.R?.)$46.)P,(14.(2.$31.)(47.$31.(33.(34.R15.))R?.)(20.$31.(48.(12.R10.)(13.R10.)(49.(4:.R10.)))))P,(14.(2.(1.&40.))(47.(1.&40.)(4;.R13.)R12.)(20.(1.&40.)(18.&40.(4<.R11.))))P,(2;.(4=.(4:.R12.))(4>.+2.+20.))P,(40.(21.$11.$11.)(24.$11.$11.(12.R13.)(13.R13.))R16.)P,(1>.VhAR,R19.R18.R<.)P,(1?.VhAR,R1:.R11.(20.(21.$22.$23.)(24.$22.$23.R17.R16.))R=.)P,(2:.R14.R13.)P,(2:.(2<.R14.+8.)R13.)P,(2:.(2<.R14.+20.)(4?.R>.))P,(3:.$1<.R11.R14.R17.)P,(2:.(50.R10.)R15.)P,(2:.R16.(51.R19.+2>0.))P,(14.$11.(52.R1:.+10.)=)P,(39.$1<.R15.)P,(14.(1.&40.)R3=.(18.&40.$53.))P,(26.VhAR,VAL,VFF,R24.R16.)P,(27.R18.R17.)P,Pc',$<.P,(54.R43.R20.R42.R41.R3=.R3<.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R1<.R1;.R27.R22.R21.R26.R24.R23.R1>.R1=.R25.R1:.R1.)(55.$1<.R45.R2.)(55.$1<.R44.(15.(16.(17.R43.(18.&40.R20.)R42.R41.R40.R3?.R3>.R3=.R3<.(18.&40.R1?.)(18.&40.(4<.R22.))R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R1<.(18.&40.$56.)R1;.(1:.(1.&40.))R1:.(1;.$1<.))R19.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 h LF QS bc i k si SP CBP C lo F fc m mo L
      WF HV Hk STQ SEC NTHS NTH NS32 HQS HMQ RQ CB0 CB1 CHI ST LOL SPL SPA MI TP HK HJ HC.
    subst L.
    dpose WF as (WL' & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG). dpose WL' as (WL & WL24 & WLD).
    pose proof (WFK_of_WFR h WF HV) as W0.
    dpose WK as (WKF & NDK & WKSEC).
    ddestruct (L_GSB (h_L h) WL) as (SB0 & SBAL & HRI & RI1). ddestruct (L_GT (h_L h) WL) as (T0 & T1 & TAL). ddestruct (L_GCTX (h_L h) WL) as (CX0 & CX1 & CXL).
    dpose WL as (_ & B6a & B6b & _ & B6c & B6d & B6e & _ & _ & _ & _ & _ & STK1 & _ & _ & _ & STK0 & STKH & _).
    pose proof (ff_geom AL FF h mo W0 HK) as GEO.
    pose proof (z_T_hull h GEO) as ZTH. pose proof (z_T_ctx h GEO) as ZTC. pose proof (z_ctx_hull h GEO) as ZCH.
    unfold zapart in ZTH, ZTC, ZCH. cbn [fst snd] in ZTH, ZTC, ZCH. rewrite CXL in ZTC, ZCH.
    (* [comment removed for export] *)
    set (n := ck_n k) in *. set (hb := ck_map_beg k) in *. set (ms := ck_map_size k) in *.
    pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (KN & KST & KP & KX). rewrite SEC in KX.
    ddestruct (chunk_geom' h k WL WR WK Hk) as (RZ16 & N0 & UA8).
    ddestruct (chunk_ext' h k WL WR WK Hk) as (_ & E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold ext_lo, ext_hi, ck_end in E1, E3, E4, E5, E6. rewrite SEC in E1, E3, E4, E5, E6.
    fold hb in E1, E5. fold hb ms in E3, E4, E6.
    dpose WS as (WS1 & WS2 & WS3 & WS4 & WS5 & WS6 & WS7 & WS8).
    pose proof (proj1 (Forall_forall _ _) WS8 _ (nth_error_In _ _ NTHS)) as (MSA & MS4 & SZP). cbn [s_map_size s_size] in MSA, MS4, SZP. fold ms in MSA, MS4.
    assert (HAB : ck_ab k = hb + 4096) by (subst hb; unfold ck_map_beg; clear; lia).
    assert (HHD : ck_hdr k = ck_ab k + ck_rz k - 16) by (unfold ck_hdr, ck_user, kChunkHeaderSize; clear; lia).
    ddestruct KX as (i0 & NTH0 & HAL & HBPOS & HBCEIL & HBLH). fold hb in HAL, HBPOS. fold hb ms in HBCEIL, HBLH. unfold lowhigh in HBLH.
    set (ncks := Z.of_nat (length (s_chunks (h_sec h)))) in *.
    pose proof (nth_error_Some_length _ _ _ NTHS) as SIL.
    (* [comment removed for export] *)
    pose proof (z_sec_T h GEO si _ NTHS) as ZsT. pose proof (z_sec_hull h GEO si _ NTHS) as ZsH. pose proof (z_sec_stk h GEO si _ NTHS) as ZsS.
    pose proof (z_sec_band h GEO si _ NTHS) as ZsB. pose proof (z_sec_ctx h GEO si _ NTHS) as ZsC. pose proof (z_sec_fs h GEO si _ NTHS) as ZsF.
    pose proof (z_sec_pa h GEO si _ NTHS) as ZsP.
    unfold zapart in ZsT, ZsH, ZsS, ZsB, ZsC, ZsF, ZsP. cbn [fst snd s_map_beg s_map_size] in ZsT, ZsH, ZsS, ZsB, ZsC, ZsF, ZsP. fold hb ms in ZsT, ZsH, ZsS, ZsB, ZsC, ZsF, ZsP.
    rewrite CXL in ZsC.
    (* [comment removed for export] *)
    ddestruct HMQ as (G0 & G1 & G2 & G3 & G4 & G5 & G7 & G8 & G9 & GE). pose proof G2 as THR.
    ddestruct G2 as (UNW & (ds & PCLS) & (j0 & j1 & J27) & (xs & bs & TST & LXS & BST & LBS)).
    destruct G1 as [RO RW]. ddestruct (hm_ro_freeS (h_L h) m RO) as (can & dd & madv & RSS & LST).
    dpose G0 as (WLS & WHS & _ & WT4 & _).
    (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) G4 k Hk) as (HDR & MAG & QUS). rewrite STQ in QUS. cbn in QUS. ddestruct QUS as (fcw & UC & UW).
    ddestruct HDR as (b1 & id & HDC & B13 & B1R & IDR). rewrite STQ in HDC.
    change [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nfix (ck_n k))); C4 (Z_to_bv 64 id); C4 (Z_to_bv 64 0)]
      with (hdr_w0 b1 3 ++ hdr_rest (nfix n) id) in HDC.
    apply rw_cells_app in HDC as [HW0 HW1]. cbn [cells_size csize Nat.add hdr_w0] in HW1. change (Z.of_nat 4) with 4 in HW1.
    (* [comment removed for export] *)
    pose proof G7 as G7u. unfold hm_sec in G7u. cbn zeta in G7u. fold ncks in G7u.
    ddestruct G7u as (SC1 & (srt & SC2) & (st & SC3 & L3) & (bsl & SC4 & L4) & SC5 & (g0 & g1 & SC6) & PA1 & (rest & PA2 & PAL) & SHD).
    destruct st as [|st0 [|nfr [|cal [|st3 [|]]]]]; try discriminate L3. cbn [map] in SC3.
    change [C8 st0; C8 nfr; C8 cal; C8 st3] with ([C8 st0] ++ [C8 nfr; C8 cal] ++ [C8 st3]) in SC3.
    apply rw_cells_app in SC3 as [SC3a SC3]. apply rw_cells_app in SC3 as [SC3b SC3c]. cbn [cells_size csize Nat.add] in SC3b, SC3c.
    replace (A_INSTANCE + 136 + Z.of_nat 8) with (A_INSTANCE + 144) in SC3b by (clear; lia).
    destruct (SHD si _ NTHS) as [KHDR KWR]. cbn [s_map_beg s_map_size s_size] in KHDR, KWR. fold hb ms in KHDR, KWR. fold hb in KWR. fold ms in KWR.
    (* [comment removed for export] *)
    assert (NL : exists shl, nth_error (s_chunks (h_sec h)) (length (s_chunks (h_sec h)) - 1) = Some shl).
    { destruct (nth_error (s_chunks (h_sec h)) (length (s_chunks (h_sec h)) - 1)) as [shl|] eqn:E; [exists shl; reflexivity|].
      exfalso. apply nth_error_None in E. clear - E SIL. lia. }
    destruct NL as [shl NL]. destruct (SHD _ _ NL) as [LHDR LWR].
    assert (LGEO : 0x65f000 <= s_map_beg shl /\ 4096 < s_map_size shl /\ s_map_beg shl + s_map_size shl <= ACEIL /\ (s_map_beg shl + s_map_size shl <= 0x7fff7000 \/ 0x10007fff8000 <= s_map_beg shl)).
    { pose proof (proj1 (Forall_forall _ _) WS8 _ (nth_error_In _ _ NL)) as (_ & LM4 & _).
      destruct (WKSEC _ _ NL) as (kl & Hkl & Pl & MBl & MSl). pose proof (proj1 (Forall_forall _ _) WKF kl Hkl) as (KNl & _ & KPl & Xl). rewrite Pl in Xl.
      ddestruct Xl as (_ & _ & _ & POSl & CEILl & LHl). rewrite MBl, MSl in CEILl, LHl. rewrite MBl in POSl. unfold lowhigh, kHighMemBeg in LHl.
      pose proof (sec_map_big (ck_n kl) ltac:(clear -KNl; lia) ltac:(rewrite <- KPl; exact Pl)) as BIGl. unfold ck_map_size in MSl. rewrite MSl in BIGl.
      clear - LM4 POSl CEILl LHl BIGl. lia. }
    set (bases := map s_map_beg (s_chunks (h_sec h)) ++ map (fun w : word => bv_unsigned w) rest).
    assert (ARR : u64arr asegs m (l_pa (h_L h)) (map (Z_to_bv 64) bases)).
    { subst bases. rewrite map_app, !map_map. apply u64arr_app. split; [exact PA1|].
      rewrite length_map. fold ncks. replace (map (fun x : word => Z_to_bv 64 (bv_unsigned x)) rest) with rest; [exact PA2|].
      clear. induction rest as [|w r IH]; [reflexivity|]. cbn [map]. rewrite <- IH at 1. f_equal. symmetry. exact (wa_unsigned_id w). }
    assert (LB : Z.of_nat (length bases) = ncks + Z.of_nat (length rest)) by (subst bases ncks; rewrite length_app, !length_map; clear; lia).
    (* [comment removed for export] *)
    destruct LST as (LS1 & _). apply (rw_instance m) in LS1; [| unfold A_INSTANCE; clear; lia| unfold A_INSTANCE; cbn; clear; lia].
    change [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (l_pa (h_L h))); C8 (Z_to_bv 64 (l_pa (h_L h)))] with ([C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (l_pa (h_L h)))] ++ [C8 (Z_to_bv 64 (l_pa (h_L h)))]) in LS1.
    apply rw_cells_app in LS1 as [SEC64 _].
    assert (MTX : rw_cells asegs m A_SEC_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)]).
    { unfold A_SEC_MUTEX. eapply rw_cells_reshape; [exact SC5| cbn; repeat split; exact I| reflexivity]. }
    assert (SC12 : rw_cells asegs m (A_INSTANCE + 112) [C8 (Z_to_bv 64 (s_nres (h_sec h))); C8 (Z_to_bv 64 ncks); C1 srt]).
    { change [C8 (Z_to_bv 64 (s_nres (h_sec h))); C8 (Z_to_bv 64 ncks); C1 srt] with ([C8 (w64 (s_nres (h_sec h))); C8 (w64 ncks)] ++ [C1 srt]).
      apply rw_cells_app. split; [exact SC1| cbn [cells_size csize Nat.add]; replace (A_INSTANCE + 112 + Z.of_nat 16) with (A_INSTANCE + 128) by (clear; lia); exact SC2]. }
    (* [comment removed for export] *)
    pose proof (Z.div_mod hb 8 ltac:(clear; lia)) as DH. pose proof (Z.mod_pos_bound hb 8 ltac:(clear; lia)) as DHB.
    pose proof (Z.div_mod ms 8 ltac:(clear; lia)) as DMS. pose proof (Z.mod_pos_bound ms 8 ltac:(clear; lia)) as DMSB.
    pose proof aceil_bounds as ACB.
    assert (SH : exists junk, rw_cells asegs m (0x7fff8000 + hb / 8) [CB (Z.to_nat (ms / 8)) junk]).
    { destruct E5 as [HB0 [LOWM|HIGHM]].
      - destruct (wr_at_high_CB m (0x7fff8000 + hb / 8) (ms / 8)
                  ltac:(replace (0x7fff8000 + hb / 8) with (0x7fff7000 + (0x7fff8000 + hb / 8 - 0x7fff7000)) by (clear; lia);
                        eapply wr_at_sub; [exact WLS| clear -HB0 DH DHB; lia| clear -DMS DMSB MS4; lia| unfold kHighMemBeg in *; clear -HB0 LOWM DH DHB DMS DMSB MS4; lia])
                  ltac:(clear -HB0 DH DHB; lia) ltac:(clear -DMS DMSB MS4; lia)) as [junk SHj]. exists junk. exact SHj.
      - destruct (wr_at_high_CB m (0x7fff8000 + hb / 8) (ms / 8)
                  ltac:(replace (0x7fff8000 + hb / 8) with (0x2008fff7000 + (0x7fff8000 + hb / 8 - 0x2008fff7000)) by (clear; lia);
                        eapply wr_at_sub; [exact WHS| unfold kHighMemBeg in *; clear -HIGHM DH DHB; lia| clear -DMS DMSB MS4; lia| unfold kHighMemBeg in *; clear -HIGHM E6 ACB DH DHB DMS DMSB MS4; lia])
                  ltac:(unfold kHighMemBeg in *; clear -HIGHM DH DHB; lia) ltac:(clear -DMS DMSB MS4; lia)) as [junk SHj]. exists junk. exact SHj. }
    destruct SH as [junk SH].
    (* [comment removed for export] *)
    assert (MSB : 4096 <= ms < 2^43).
    { split; [clear -MS4; lia|]. subst ms. unfold ck_map_size, sec_map_size, needed2, needed, rounded. fold n.
      pose proof (rz_size_bound' n) as RZB. pose proof (round_up_spec (Z.max n 8) 8 ltac:(clear; lia)) as [R8 _].
      assert (N2 : (if from_primary n then round_up (Z.max n 8) 8 + rz_size n else round_up (Z.max n 8) 8 + rz_size n + rz_size n) <= n + 8 + 8 + 4096)
        by (destruct (from_primary n); clear -RZB R8 KN; lia).
      pose proof (round_up_spec (if from_primary n then round_up (Z.max n 8) 8 + rz_size n else round_up (Z.max n 8) 8 + rz_size n + rz_size n) 4096 ltac:(clear; lia)) as [R4 _].
      clear - N2 R4 KN. lia. }
    assert (HAL8 : hb mod 8 = 0) by (clear -HAL; pose proof (Z.div_mod hb 4096 ltac:(lia)); rewrite HAL, Z.add_0_r in H; rewrite H;
                                     replace (4096 * (hb / 4096)) with ((512 * (hb / 4096)) * 8) by lia; apply Z_mod_mult).
    assert (MS8 : ms mod 8 = 0) by (clear -MSA; pose proof (Z.div_mod ms 4096 ltac:(lia)); rewrite MSA, Z.add_0_r in H; rewrite H;
                                    replace (4096 * (ms / 4096)) with ((512 * (ms / 4096)) * 8) by lia; apply Z_mod_mult).
    assert (RNG : (8 <= hb /\ hb <= 0x7fff7ff8 /\ hb + ms <= 0x7fff8000) \/ (0x10007fff8000 <= hb /\ 0x10007fff8008 <= hb + ms /\ hb <= 0x7ffffffffff8 /\ hb + ms <= 0x800000000000)).
    { unfold kHighMemBeg in HBLH. clear - HBLH HBCEIL MSB ACB. lia. }
    (* [comment removed for export] *)
    assert (POISON : poison0_siteS (ff_CS AL FF h) (ff_K AL FF h) hb ms can dd madv).
    { apply (poison0_S AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) ASB); [apply ff_kinv| exact HAL8| exact MS8| clear -MSB; lia| exact RNG]. }
    (* [comment removed for export] *)
    assert (NOROMS : forall x : word, rmp_PB (0x7fff8000 + hb / 8) <= bv_unsigned x < rmp_PE (0x7fff8000 + hb / 8 + ms / 8) -> ro_addr asegs x = false).
    { intros x Hx. destruct (ro_addr asegs x) eqn:E; [| reflexivity]. exfalso. pose proof (asegs_ro_lt x E) as LT. unfold rmp_PB in Hx.
      pose proof (Z.div_mod (0x7fff8000 + hb / 8 + 4095) 4096 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + hb / 8 + 4095) 4096 ltac:(clear; lia)).
      clear - Hx LT H H0 DH DHB HBPOS. lia. }
    (* [comment removed for export] *)
    assert (BASES : forall j b, nth_error bases j = Some b -> (j < Z.to_nat ncks)%nat -> 0 <= b < 2^63 /\ (j <> Z.to_nat (Z.of_nat si) -> b + 4096 <= hb \/ hb + ms <= b)).
    { intros j b Hj Hjn. subst bases ncks. rewrite Nat2Z.id in Hjn |- *.
      rewrite nth_error_app1 in Hj by (rewrite length_map; exact Hjn). rewrite nth_error_map in Hj.
      destruct (nth_error (s_chunks (h_sec h)) j) as [shj|] eqn:Nj; [| discriminate Hj]. cbn in Hj. injection Hj as <-.
      pose proof (z_sec_hull h GEO j shj Nj) as Yh. unfold zapart in Yh. cbn [fst snd] in Yh.
      pose proof (proj1 (Forall_forall _ _) WS8 _ (nth_error_In _ _ Nj)) as (_ & M4 & _).
      assert (WKj : exists kj, In kj (h_chunks h) /\ ck_prim kj = false /\ ck_map_beg kj = s_map_beg shj /\ ck_map_size kj = s_map_size shj) by (exact (WKSEC j shj Nj)).
      ddestruct WKj as (kj & Hkj & Pj & MBj & MSj). pose proof (proj1 (Forall_forall _ _) WKF kj Hkj) as (_ & _ & _ & Xj). rewrite Pj in Xj.
      ddestruct Xj as (_ & _ & _ & POSj & CEILj & _). rewrite MBj, MSj in CEILj. rewrite MBj in POSj.
      split; [clear - POSj CEILj ACB M4; lia|].
      intros NE. pose proof (z_sec_sec h GEO si j _ _ NTHS Nj ltac:(clear -NE; lia)) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. fold hb ms in Y.
      clear - Y M4 MSB. lia. }
    (* [comment removed for export] *)
    dpose WL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PAA & PALH & PACE & _).
    unfold lowhigh, kHighMemBeg in PALH.
    assert (LB40 : 8 * Z.of_nat (length bases) = h_pa_committed h /\ Z.of_nat (length bases) < 2^40 /\ 8 * Z.of_nat (length bases) <= 0x800000)
      by (rewrite LB, PAL; clear - LB PAL WS4 WS5 WS6; unfold kPtrArrayChunks in *; lia).
    pose proof (GEO 1%nat 3%nat _ _ eq_refl eq_refl ltac:(discriminate)) as ZCP. pose proof (z_T_pa h GEO) as ZTP.
    unfold zapart in ZCP, ZTP. cbn [fst snd] in ZCP, ZTP. rewrite CXL in ZCP.
    assert (N2B : 0 <= needed2 n /\ needed2 n + 4096 <= ms).
    { subst ms. unfold ck_map_size, sec_map_size. fold n. pose proof (round_up_spec (needed2 n) 4096 ltac:(clear; lia)) as [R4 _].
      assert (0 <= needed2 n); [| clear -R4 H; lia]. unfold needed2, needed, rounded. pose proof (rz_size_bound' n). pose proof (round_up_spec (Z.max n 8) 8 ltac:(clear; lia)) as [R8 _].
      destruct (from_primary n); clear - H R8; lia. }
    (* [comment removed for export] *)
    assert (LENZ : Z.of_nat (length (s_chunks (h_sec h)) - 1) = ncks - 1) by (subst ncks; clear -SIL; lia).
    assert (CASES : (Z.of_nat si = ncks - 1 /\ s_map_beg shl = hb)
        \/ (Z.of_nat si < ncks - 1 /\ (0x65f000 <= s_map_beg shl /\ (s_map_beg shl + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= s_map_beg shl)) /\ s_map_beg shl + 4096 <= ACEIL /\ (s_map_beg shl + 4096 <= hb \/ hb + ms <= s_map_beg shl)
            /\ (l_pa (h_L h) + 8 * Z.of_nat (length bases) <= s_map_beg shl \/ s_map_beg shl + 4096 <= l_pa (h_L h)) /\ (l_T (h_L h) + 4096 <= s_map_beg shl \/ s_map_beg shl + 4096 <= l_T (h_L h))
            /\ (l_ctx (h_L h) + 0x10000 <= s_map_beg shl \/ s_map_beg shl + 4096 <= l_ctx (h_L h))
            /\ rw_cells asegs m (s_map_beg shl) [C8 (Z_to_bv 64 (s_map_beg shl)); C8 (Z_to_bv 64 (s_map_size shl)); C8 (Z_to_bv 64 (s_size shl)); C8 (Z_to_bv 64 (ncks - 1))] /\ crange (ff_CS AL FF h) (s_map_beg shl) 32)).
    { destruct (Z.eq_dec (Z.of_nat si) (ncks - 1)) as [EQ|NE].
      - left. split; [exact EQ|]. replace (length (s_chunks (h_sec h)) - 1)%nat with si in NL by (subst ncks; clear -EQ SIL; lia). rewrite NTHS in NL. injection NL as <-. reflexivity.
      - right. split; [subst ncks; clear -NE SIL; lia|].
        pose proof (proj1 (Forall_forall _ _) WS8 _ (nth_error_In _ _ NL)) as (_ & LM4 & _).
        destruct (WKSEC _ _ NL) as (kl & Hkl & Pl & MBl & MSl). pose proof (proj1 (Forall_forall _ _) WKF kl Hkl) as (KNl & _ & KPl & Xl). rewrite Pl in Xl.
        ddestruct Xl as (_ & _ & _ & POSl & CEILl & LHl). rewrite MBl, MSl in CEILl, LHl. rewrite MBl in POSl. unfold lowhigh, kHighMemBeg in LHl.
        pose proof (sec_map_big (ck_n kl) ltac:(clear -KNl; lia) ltac:(rewrite <- KPl; exact Pl)) as BIGl. unfold ck_map_size in MSl. rewrite MSl in BIGl.
        pose proof (z_sec_sec h GEO si (length (s_chunks (h_sec h)) - 1) _ _ NTHS NL ltac:(subst ncks; clear -NE SIL; lia)) as Yss.
        pose proof (z_sec_pa h GEO _ _ NL) as Yp. pose proof (z_sec_T h GEO _ _ NL) as Yt. pose proof (z_sec_ctx h GEO _ _ NL) as Yc.
        unfold zapart in Yss, Yp, Yt, Yc. cbn [fst snd s_map_beg s_map_size] in Yss, Yp, Yt, Yc. fold hb ms in Yss. rewrite CXL in Yc.
        split; [clear - LM4 POSl CEILl LHl BIGl; lia|]. split; [clear - LM4 CEILl; lia|]. split; [clear - Yss LM4 MSB; lia|].
        split; [clear - Yp LM4 LB40; lia|]. split; [clear - Yt LM4; lia|]. split; [clear - Yc LM4; lia|].
        split; [rewrite <- LENZ; exact LHDR|]. eapply crange_sub; [exact (ff_cs_sec AL FF h mo _ HK (nth_error_In _ _ NL))| clear; cbn; lia| cbn [s_map_beg s_map_size]; clear -LM4; lia]. }
    (* [comment removed for export] *)
    eapply (rec_sec_cfgS AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) (l_T (h_L h)) (l_ctx (h_L h)) (l_sb (h_L h))
              ltac:(split; [exact SB0| rewrite <- HRI; exact RI1]) (conj T0 T1) (conj CX0 CX1) ltac:(clear -ZTC; lia)
              (ff_cs_T AL FF h W0) ltac:(rewrite <- CXL; exact (ff_cs_ctx AL FF h W0))
              hb ms (needed2 n) (Z.of_nat si) (ff_K AL FF h) (ff_K AL FF (h_rec_sec h k si)) (ff_kinv AL FF h)
              (ff_CS AL FF (h_rec_sec h k si)) (ff_csok AL FF (h_rec_sec h k si)) (ff_kinv AL FF (h_rec_sec h k si))
              ltac:(intros mo1 K1; exact (ff_unmap_has AL FF h k si mo1 W0 NTHS K1))
              ltac:(intros mo1 K1; exact (ff_unmap AL FF h k si mo1 W0 NTHS K1))
              can dd madv POISON
              ltac:(intros mo1 K1 NE; exact (ff_madv_ok AL FF h k si mo1 W0 NTHS NE K1))
              ltac:(intros mo1 K1 NE; exact (ff_madv AL FF h k si mo1 W0 NTHS NE K1))
              NOROMS Q)
      with (HD := ck_hdr k) (n0 := nfix n) (ctx := id) (b1 := b1) (st := 3) (PA := l_pa (h_L h)) (nres := s_nres (h_sec h)) (n := ncks)
           (last := s_map_beg shl) (lms := s_map_size shl) (lsz := s_size shl) (lo := lo) (bases := bases) (xs := xs) (junk := junk)
           (nfr := nfr) (cal := cal) (g2 := g0) (g3 := g1) (sorted := srt).
    all: lazymatch goal with
         | |- aevtS _ _ _ => idtac
         | |- forall c', _ -> aevtS _ _ _ => idtac
         | |- word => exact (Z_to_bv 64 0)
         | |- bv 64 => exact (Z_to_bv 64 0)
         | |- sec_cells _ _ _ _ _ _ _ _ _ _ => split; [exact SEC64| split; [exact SC12| split; [exact SC3b| split; [exact SC6 | exact MTX]]]]
         | |- nth_error _ (Z.to_nat (Z.of_nat _)) = Some _ => subst bases; rewrite Nat2Z.id, nth_error_app1 by (rewrite length_map; exact SIL); rewrite nth_error_map, NTHS; reflexivity
         | |- nth_error _ (Z.to_nat (_ - 1)) = Some _ => subst bases ncks; replace (Z.to_nat (Z.of_nat (length (s_chunks (h_sec h))) - 1)) with (length (s_chunks (h_sec h)) - 1)%nat by (clear; lia);
                                                    rewrite nth_error_app1 by (rewrite length_map; clear -SIL; lia); rewrite nth_error_map, NL; reflexivity
         | |- crange _ (l_pa _) _ => destruct LB40 as (LBE & _); rewrite LBE; exact (ff_cs_pa AL FF h W0)
         | |- crange (ff_CS _ _ (h_rec_sec _ _ _)) _ _ => intros x Hx; apply (ff_cs_rec_sec AL FF h k si x NTHS); [apply (ff_cs_stack AL FF h lo (SP - lo) W0); [exact LOL| clear -CB0 CB1 CHI; lia| exact Hx] | clear - Hx ZsS LOL SPL CB0 CB1 CHI; lia]
         | |- crange _ _ _ => first [exact (ff_cs_sec AL FF h mo _ HK (nth_error_In _ _ NTHS)) | (apply (ff_cs_stack AL FF h lo _ W0); [exact LOL| clear -CB0 CB1 CHI; lia])]
         | |- _ => first [ exact HAL | exact HW0 | exact HW1 | exact KHDR | exact ARR | exact TST | exact LXS | exact RSS | exact SH | exact ST | exact MI | exact TP | exact HK | exact HJ
                        | exact BASES | exact MSA | exact MSB | exact CASES | exact B1R
                        | (unfold kHighMemBeg in E5; clear -E5; lia) | (clear -E6; lia) | (clear -N2B MSB; lia)
                        | (clear - ZsH B6a B6b; lia) | (clear - HHD HAB RZ16; lia) | (clear - E2 E3; lia) | (clear - NS32 KN; unfold nfix in *; lia) | (clear; lia)
                        | (clear - ZsT; lia) | (clear - ZsC; lia) | (clear - SIL; subst ncks; lia) | (clear - LB; lia) | (clear - LB40; lia)
                        | (clear - PALH PACE; lia) | (clear - LB40 PACE; lia) | (clear - WS3 WS4; lia) | (clear - ZsP LB40; lia)
                        | (clear - ZTP LB40; lia) | (clear - ZCP LB40; lia) | (clear - STK0 LOL; lia) | exact SPL | (clear - CHI STKH CB0 CB1; lia) | exact SPA
                        | match goal with |- ?G' => idtac "RSS-LEFTOVER" G' end ]
         end.
    (* [comment removed for export] *)
    intros c4 P4. unfold rs_post in P4.
    ddestruct P4 as (ms4 & mo4 & y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & nfr' & cal' & g2' & g3' & xs' & m4
                    & -> & -> & HK4 & HJ4 & MU & WMO & MI4 & ST4 & RSS4 & SEC4 & ARR4 & LHDR4 & TST4 & LXS4 & SHZ & HOLE).
    (* [comment removed for export] *)
    pose proof RQ as RQ0. unfold RIq in RQ0. cbn zeta in RQ0.
    ddestruct RQ0 as (_ & _ & _ & _ & _ & _ & (_ & BWF & b0 & all & E0 & EA & EE & EL & IL & RNGE)).
    assert (NTHZ : nth_error all i = Some (ck_hdr k)).
    { rewrite EE, nth_error_map in NTH. destruct (nth_error all i) as [e|] eqn:NA; [| discriminate NTH]. cbn in NTH.
      assert (NTH' : Z_to_bv 64 e = Z_to_bv 64 (ck_hdr k)) by (clear -NTH; congruence). clear NTH.
      f_equal. pose proof (proj1 (Forall_forall _ _) RNGE e (nth_error_In _ _ NA)) as [R1 R2].
      apply (f_equal bv_unsigned) in NTH'. rewrite !Z_to_bv_small in NTH' by (unfold bv_modulus; change (2 ^ Z.of_N 64) with 18446744073709551616; unfold kHighMemBeg in *; clear -R1 R2 E1 E2 E3 E5 E6 ACB; lia). exact NTH'. }
    assert (HE : b_elems b0 = ck_hdr k :: skipn (S i) all) by (rewrite EL; exact (skipn_cons_nth all i _ NTHZ)).
    assert (HGU : forall k', In k' (h_chunks h) -> k' <> k -> ck_hdr k' = ck_hdr k -> False).
    { intros k' Hk' NE E. apply NE. exact (hdr_unique h k' k WL WR WK GEO Hk' Hk E). }
    set (h' := h_recs h k si).
    pose proof (WFR_recs h k si b0 (tl (q_batches (h_tq h))) (skipn (S i) all) WF GEO Hk SEC NTHS E0 HE HGU) as WF'.
    (* [comment removed for export] *)
    set (Sh := 0x7fff8000 + hb / 8) in *. set (kk := ms / 8) in *.
    set (last := s_map_beg shl) in *.
    assert (SKB : 0x7fff8000 + 0x65f000 / 8 <= Sh /\ Sh + kk <= 0x10007fff8000 /\ (hb + ms <= 0x7fff7000 -> Sh + kk <= 0x8fff7000) /\ (0x10007fff8000 <= hb -> 0x2008fff7000 <= Sh))
      by (subst Sh kk; unfold kHighMemBeg in *; clear - E5 E6 ACB DH DHB DMS DMSB MSB; lia).
    set (W := rs_W (l_T (h_L h)) hb ms (Z.of_nat si) lo SP (l_pa (h_L h)) last (ck_hdr k)) in MU.
    pose proof (proj1 (Forall_forall _ _) WS8 _ (nth_error_In _ _ NL)) as (_ & LM4 & _). fold last in LM4 |- *.
    assert (DJz : forall A n', (A + n' <= lo \/ SP <= A) -> (A + n' <= l_T (h_L h) + 2840 \/ l_T (h_L h) + 2904 <= A) ->
                  (A + n' <= A_INSTANCE + 120 \/ A_INSTANCE + 720 <= A) -> (A + n' <= l_pa (h_L h) + 8 * Z.of_nat si \/ l_pa (h_L h) + 8 * Z.of_nat si + 8 <= A) ->
                  (A + n' <= last + 24 \/ last + 32 <= A) -> (A + n' <= Sh \/ Sh + kk <= A) -> (A + n' <= hb \/ hb + ms <= A) -> disjoint_from W A n').
    { intros A n' H1 H2 H3 H4 H5 H6 H7. subst W. unfold rs_W. cbn [disjoint_from]. unfold A_GSTATS, A_SEC_MUTEX. subst Sh kk. clear - H1 H2 H3 H4 H5 H6 H7. repeat split; lia. }
    (* [comment removed for export] *)
    assert (DJgen : forall A n', (A + n' <= lo \/ SP <= A) -> (A + n' <= l_T (h_L h) \/ l_T (h_L h) + 4096 <= A) ->
                  (A + n' <= A_INSTANCE + 120 \/ A_INSTANCE + 720 <= A) -> (A + n' <= l_pa (h_L h) \/ l_pa (h_L h) + 0x800000 <= A) ->
                  (A + n' <= last \/ last + 4096 <= A) -> (A + n' <= Sh \/ Sh + kk <= A) -> (A + n' <= hb \/ hb + ms <= A) -> disjoint_from W A n').
    { intros A n' H1 H2 H3 H4 H5 H6 H7. apply DJz; [exact H1| clear -H2; lia| exact H3| clear - H4 LB40 SIL LB; subst ncks; lia| clear -H5; lia| exact H6| exact H7]. }
    assert (KOM : forall A n', disjoint_from W A n' -> kept m m4 A n') by (intros A n' D; exact (kept_of_munch W m m4 A n' MU D)).
    (* [comment removed for export] *)
    pose proof (z_T_stk h GEO) as ZTS. pose proof (z_hull_stk h GEO) as ZHS. pose proof (z_hull_band h GEO) as ZHB. pose proof (z_pa_hull h GEO) as ZPH.
    pose proof (z_T_fs h GEO) as Zfs1. pose proof (z_fs_hull h GEO) as Zfs2. pose proof (z_fs_stk h GEO) as Zfs3. pose proof (z_fs_band h GEO) as Zfs4.
    pose proof (z_ctx_stk h GEO) as ZCS. pose proof (z_ctx_band h GEO) as ZCB. pose proof (z_pa_stk h GEO) as ZPS. pose proof (z_pa_band h GEO) as ZPB.
    pose proof (z_T_dtls h GEO) as Zdt1. pose proof (z_hull_dtls h GEO) as Zdt2. pose proof (z_stk_dtls h GEO) as Zdt3. pose proof (z_band_dtls h GEO) as Zdt4.
    pose proof (GEO 2%nat 3%nat _ _ eq_refl eq_refl ltac:(discriminate)) as ZFP. pose proof (GEO 3%nat 7%nat _ _ eq_refl eq_refl ltac:(discriminate)) as ZPD.
    unfold zapart in ZTS, ZHS, ZHB, ZPH, Zfs1, Zfs2, Zfs3, Zfs4, ZCS, ZCB, ZPS, ZPB, Zdt1, Zdt2, Zdt3, Zdt4, ZFP, ZPD.
    cbn [fst snd] in ZTS, ZHS, ZHB, ZPH, Zfs1, Zfs2, Zfs3, Zfs4, ZCS, ZCB, ZPS, ZPB, Zdt1, Zdt2, Zdt3, Zdt4, ZFP, ZPD. rewrite CXL in ZCS, ZCB.
    (* [comment removed for export] *)
    pose proof (z_sec_hull h GEO _ _ NL) as YlH. pose proof (z_sec_T h GEO _ _ NL) as YlT. pose proof (z_sec_stk h GEO _ _ NL) as YlS. pose proof (z_sec_ctx h GEO _ _ NL) as YlC.
    pose proof (z_sec_fs h GEO _ _ NL) as YlF. pose proof (z_sec_band h GEO _ _ NL) as YlB.
    unfold zapart in YlH, YlT, YlS, YlC, YlF, YlB. cbn [fst snd s_map_beg s_map_size] in YlH, YlT, YlS, YlC, YlF, YlB. fold last in YlH, YlT, YlS, YlC, YlF, YlB. rewrite CXL in YlC.
    pose proof (GEO 7%nat (8 + length (d_nb (h_dep h)) + length (d_bl (h_dep h)) + si)%nat _ _ eq_refl (hzones_sec h si _ NTHS) ltac:(lia)) as ZsD.
    pose proof (GEO 7%nat (8 + length (d_nb (h_dep h)) + length (d_bl (h_dep h)) + (length (s_chunks (h_sec h)) - 1))%nat _ _ eq_refl (hzones_sec h _ _ NL) ltac:(lia)) as YlD.
    unfold zapart in ZsD, YlD. cbn [fst snd s_map_beg s_map_size] in ZsD, YlD. fold hb ms in ZsD. fold last in YlD.
    dpose WL' as (_ & _ & (DTL & DTC & _)). unfold lowhigh, kHighMemBeg in DTL.
    assert (SPHI : SP <= l_stk_hi (h_L h)) by (clear -CB0 CB1 CHI; lia).
    (* [comment removed for export] *)
    assert (DJhull : forall A n', l_b6 (h_L h) <= A -> A + n' <= l_b6 (h_L h) + 0x2000011000 -> disjoint_from W A n').
    { intros A n' H1 H2. apply DJgen; unfold kHighMemBeg, A_INSTANCE in *; clear - H1 H2 ZHS LOL SPL SPHI ZTH B6c STK0 ZPH YlH LM4 ZHB SKB ZsH; lia. }
    assert (DJT : forall A n', l_T (h_L h) <= A -> A + n' <= l_T (h_L h) + 4096 -> (A + n' <= l_T (h_L h) + 2840 \/ l_T (h_L h) + 2904 <= A) -> disjoint_from W A n').
    { intros A n' H1 H2 H3. apply DJz; unfold kHighMemBeg, A_INSTANCE in *; clear - H1 H2 H3 ZTS LOL SPL SPHI T0 ZTP LB40 SIL LB YlT LM4 SKB ZsT; subst ncks; lia. }
    assert (DJband : forall A n', 0x7fff7000 <= A -> A + n' <= 0x10007fff8000 -> (A + n' <= Sh \/ Sh + kk <= A) -> disjoint_from W A n').
    { intros A n' H1 H2 H3. apply DJgen; unfold kHighMemBeg, A_INSTANCE in *; clear - H1 H2 H3 STK0 LOL T0 PALH YlB LM4 E5 ACB; lia || (destruct E5 as [_ [X|X]]; lia). }
    assert (IMGK : forall x : word, 0x10000 <= bv_unsigned x < 0x65f000 ->
              ~ in_rangesZ [(A_INSTANCE + 120, A_INSTANCE + 129); (A_INSTANCE + 144, A_INSTANCE + 160); (A_GSTATS + 16, A_GSTATS + 32); (A_SEC_MUTEX, A_SEC_MUTEX + 4)] (bv_unsigned x) -> m4 x = m x).
    { intros x Hx NW. apply (KOM (bv_unsigned x) 1); [| clear; lia]. subst W. unfold rs_W. cbn [disjoint_from]. cbn [in_rangesZ] in NW. unfold A_GSTATS, A_SEC_MUTEX, A_INSTANCE, kHighMemBeg in *.
      subst Sh kk. clear - Hx NW STK0 LOL T0 PALH LGEO E5 E1 ACB DH DHB B6c. repeat split; lia. }
    assert (IAG : forall RS, ranges_apart_b RS [(A_INSTANCE + 120, A_INSTANCE + 129); (A_INSTANCE + 144, A_INSTANCE + 160); (A_GSTATS + 16, A_GSTATS + 32); (A_SEC_MUTEX, A_SEC_MUTEX + 4)] = true ->
              ranges_within_b RS 0x10000 0x65f000 = true -> iagree RS m m4).
    { intros RS H1 H2. exact (iagree_of_windows2 RS _ 0x10000 0x65f000 m m4 H1 H2 IMGK). }
    (* [comment removed for export] *)
    assert (G0' : hm_maps (h_L h) m4).
    { apply (hm_maps_o m m4 hb ms WMO (h_L h) G0); unfold kHighMemBeg, kFakeBytes in *; [clear - E5 E1; lia| clear - E5 E6 ACB MSB; lia| clear - ZsS; lia| clear - ZsT; lia| rewrite CXL; clear - ZsC; lia| clear - ZsF; lia]. }
    assert (G1' : hm_statics (h_L h) m4).
    { apply (hm_statics_k m m4 (h_L h) (conj RO RW)); [apply IAG; vm_compute; reflexivity| apply IAG; vm_compute; reflexivity| | | |]; apply KOM.
      - apply DJT; clear; lia.
      - apply DJgen; unfold A_INSTANCE in *; clear - ZCS LOL SPL SPHI ZTC CX0 ZCP YlC LM4 ZCB SKB ZsC; lia.
      - apply DJgen; unfold A_INSTANCE in *; clear - ZCS LOL SPL SPHI ZTC CX0 ZCP YlC LM4 ZCB SKB ZsC; lia.
      - apply DJgen; unfold A_INSTANCE in *; clear - Zdt3 LOL SPL SPHI Zdt1 DTL ZPD YlD LM4 Zdt4 SKB ZsD; lia. }
    assert (G2' : hm_thread h' m4).
    { eapply (hm_thread_o m m4 hb ms WMO h THR); [ | | | exact WT4 | clear -T0; lia | clear -ZsT; lia | apply recs_L | apply recs_cinit | apply recs_cache].
      - apply KOM. apply DJT; clear; lia.
      - intros c1 Hc1. apply KOM. apply DJT; clear -Hc1; lia.
      - apply KOM. apply DJT; clear; lia. }
    assert (G3' : hm_depot h' m4).
    { apply (hm_depot_k m m4 h G3); [apply IAG; vm_compute; reflexivity| | | apply recs_dep].
      - intros b Hb. destruct (In_nth_error _ _ Hb) as [jb Hjb].
        pose proof (z_node_T h GEO jb b Hjb) as Y1. pose proof (z_node_hull h GEO jb b Hjb) as Y2. pose proof (z_node_stk h GEO jb b Hjb) as Y3. pose proof (z_node_band h GEO jb b Hjb) as Y4.
        pose proof (z_sec_node h GEO _ _ jb b NTHS Hjb) as Y5. pose proof (z_sec_node h GEO _ _ jb b NL Hjb) as Y6. pose proof (GEO 3%nat (8 + jb)%nat _ _ eq_refl (hzones_node h jb b Hjb) ltac:(lia)) as Y7.
        unfold zapart in Y1, Y2, Y3, Y4, Y5, Y6, Y7. cbn [fst snd s_map_beg s_map_size] in Y1, Y2, Y3, Y4, Y5, Y6, Y7. fold hb ms in Y5. fold last in Y6.
        dpose WD as (_ & _ & NBF & _). pose proof (proj1 (Forall_forall _ _) NBF b Hb) as (NB0 & _).
        apply KOM. apply DJgen; unfold A_INSTANCE in *; clear - Y1 Y3 Y5 Y6 Y7 Y4 NB0 LOL SPL SPHI LM4 SKB; lia.
      - intros b Hb. destruct (In_nth_error _ _ Hb) as [jb Hjb].
        pose proof (z_store_T h GEO jb b Hjb) as Y1. pose proof (z_store_stk h GEO jb b Hjb) as Y3. pose proof (z_store_band h GEO jb b Hjb) as Y4.
        pose proof (z_sec_store h GEO _ _ jb b NTHS Hjb) as Y5. pose proof (z_sec_store h GEO _ _ jb b NL Hjb) as Y6. pose proof (GEO 3%nat (8 + length (d_nb (h_dep h)) + jb)%nat _ _ eq_refl (hzones_store h jb b Hjb) ltac:(lia)) as Y7.
        unfold zapart in Y1, Y3, Y4, Y5, Y6, Y7. cbn [fst snd s_map_beg s_map_size] in Y1, Y3, Y4, Y5, Y6, Y7. fold hb ms in Y5. fold last in Y6.
        dpose WD as (_ & _ & _ & _ & _ & BLF & _). pose proof (proj1 (Forall_forall _ _) BLF b Hb) as (BL0 & _).
        apply KOM. apply DJgen; unfold A_INSTANCE in *; clear - Y1 Y3 Y5 Y6 Y7 Y4 BL0 LOL SPL SPHI LM4 SKB; lia. }
    (* [comment removed for export] *)
    assert (NAK : forall k', In k' (h_chunks h) -> ck_ab k' <> ck_ab k -> ext_hi k' <= hb \/ hb + ms <= ext_lo k').
    { intros k' Hk' NA. pose proof (ext_disj' h k' k WL WR WK GEO Hk' Hk NA) as XD.
      assert (XL : ext_lo k = hb) by (unfold ext_lo; rewrite SEC; reflexivity). assert (XH : ext_hi k = hb + ms) by (unfold ext_hi, ck_end; rewrite SEC; reflexivity).
      rewrite XL, XH in XD. clear -XD. lia. }
    assert (G4' : hm_chunks h' m4).
    { unfold hm_chunks. replace (h_chunks h') with (rm_ab (ck_ab k) (h_chunks h)) by (symmetry; apply recs_chunks). apply Forall_forall. intros k' Hk'. apply rm_ab_In in Hk' as [Hk' NA].
      ddestruct (chunk_geom' h k' WL WR WK Hk') as (RZ' & N0' & U8').
      ddestruct (chunk_ext' h k' WL WR WK Hk') as (_ & F1 & F2 & F3 & F4 & F5 & F6 & FC).
      pose proof (NAK k' Hk' NA) as XD.
      assert (XAB : ext_lo k' <= ck_ab k') by (unfold ext_lo, ck_map_beg; destruct (ck_prim k'); clear; lia).
      assert (UIN : ck_ab k' + ck_rz k' = ck_user k') by reflexivity.
      assert (NFX' : 0 <= nfix (ck_n k') /\ nfix (ck_n k') <= Z.max (ck_n k') 8) by (unfold nfix; clear -N0'; lia).
      (* [comment removed for export] *)
      assert (KX : forall A n', 0 <= n' -> ck_ab k' <= A -> A + n' <= ext_hi k' -> kept m m4 A n').
      { intros A n' N0'' HA HB'. apply KOM. destruct FC as [(P' & C' & RL' & RH' & _)|(P' & i' & N' & EL' & EH')].
        - dpose (user_vs_ri h (ck_cls k') WL WR ltac:(clear -C'; lia)) as (Q1 & Q2 & Q3' & Q4).
          pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear -C'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
          unfold region_beg, kRegionSize in Q1, Q2, RL', RH'.
          apply DJhull; [clear - HA XAB RL' Q2; lia| clear - HB' RH' Q1 Q4 AUMU'; lia].
        - pose proof (z_sec_T h GEO i' _ N') as Y1. pose proof (z_sec_stk h GEO i' _ N') as Y3. pose proof (z_sec_band h GEO i' _ N') as Y4. pose proof (z_sec_pa h GEO i' _ N') as Y7.
          unfold zapart in Y1, Y3, Y4, Y7. cbn [fst snd s_map_beg s_map_size] in Y1, Y3, Y4, Y7.
          assert (NEi : i' <> si) by (intros ->; rewrite NTHS in N'; injection N' as E1' E2' E3'; apply NA; unfold ck_map_beg in E1'; clear -E1' HAB; lia).
          pose proof (z_sec_sec h GEO i' si _ _ N' NTHS NEi) as Y5. unfold zapart in Y5. cbn [fst snd s_map_beg s_map_size] in Y5. fold hb ms in Y5.
          (* [comment removed for export] *)
          assert (YL : A + n' <= last \/ last + 4096 <= A).
          { destruct (Nat.eq_dec i' (length (s_chunks (h_sec h)) - 1)) as [->|NEl].
            - rewrite NL in N'. injection N' as E1'. right. assert (EL1 : last = ck_ab k' - 4096) by (subst last; rewrite E1'; reflexivity). clear - EL1 HA. lia.
            - pose proof (z_sec_sec h GEO i' _ _ _ N' NL NEl) as Y6. unfold zapart in Y6. cbn [fst snd s_map_beg s_map_size] in Y6. fold last in Y6. clear - Y6 HA HB' XAB EL' EH' LGEO; lia. }
          apply DJgen; unfold A_INSTANCE in *; [clear -Y3 HA HB' XAB EL' EH' LOL SPL SPHI; lia| clear -Y1 HA HB' XAB EL' EH'; lia| clear - F5 HA XAB; lia| clear -Y7 HA HB' XAB EL' EH'; lia| exact YL
                                            | clear - Y4 HA HB' XAB EL' EH' F5 F6 SKB ACB; unfold kHighMemBeg in F5; lia| clear - Y5 HA HB' XAB EL' EH'; lia]. }
      apply (hm_chunk_o m m4 hb ms WMO k' (proj1 (Forall_forall _ _) G4 k' Hk') RZ' N0' U8').
      - unfold chunk_kept. split; [apply KX; [clear -RZ'; lia| clear; lia| clear - UIN F4; lia]|].
        split.
        + (* [comment removed for export] *)
          intros AK.
          pose proof (Z.div_mod (ck_user k') 8 ltac:(clear; lia)) as D1. rewrite U8', Z.add_0_r in D1.
          pose proof (Z.div_mod (nfix (ck_n k') + 7) 8 ltac:(clear; lia)) as D2. pose proof (Z.mod_pos_bound (nfix (ck_n k') + 7) 8 ltac:(clear; lia)) as D3.
          assert (APh : ck_user k' + nfix (ck_n k') <= hb \/ hb + ms <= ck_user k') by (clear - XD F1 F2 F3 NFX' XAB; lia).
          pose proof (shad_disj (ck_user k') (nfix (ck_n k')) hb ms U8' HAL8 (proj1 NFX') ltac:(clear -MSB; lia) APh) as SD. unfold AW_FreeG.shad in SD. unfold shad. subst Sh kk.
          apply KOM. apply DJband; [clear - D1 F5 XAB UIN RZ'; unfold kHighMemBeg in F5; lia| clear - D1 D2 D3 F3 F6 NFX' ACB; lia|].
          clear - SD MS8 DMS. lia.
        + (* [comment removed for export] *)
          intros NAK'. apply KX; [clear; lia| clear - UIN RZ'; lia| clear - F3; lia].
      - intros _. clear - XD F1 F2 F3 NFX' XAB. lia. }
    (* [comment removed for export] *)
    assert (G5' : hm_regions h' m4).
    { intros c' Hc'. unfold h'. rewrite (recs_L h k si), (recs_reg h k si c').
      pose proof (WR c' ltac:(unfold kNumClasses; clear -Hc'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & AUCS' & MUAL' & MULIM' & MUAU' & MFAL' & MFB' & NF4c & _).
      dpose (user_vs_ri h c' WL WR Hc') as (Q1 & Q2 & Q3 & Q4). unfold fa_beg, kFreeArrayOffset, kFreeArraySize, region_beg, kRegionSize in Q1, Q2, Q3. unfold kUserLimit in MULIM'. unfold kFreeArraySize in MFB'.
      pose proof (user_in_hull h c') as UIH.
      assert (HLH : hb + ms <= l_b6 (h_L h) \/ l_b6 (h_L h) + 0x2000011000 <= hb) by (clear -ZsH; lia).
      apply (hm_region_o m m4 hb ms WMO (h_L h) c' (h_reg h c') _ (G5 c' Hc') AUMU' NF4c).
      - unfold region_kept. split; [| split; [| split]].
        + apply KOM. unfold ri_addr. apply DJhull; clear - Hc' Q4 Q1 Q2 AUMU' HRI SB0 B6a B6b RI1; unfold ri_base, space_end, kSpaceSize in *; lia.
        + apply KOM. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset. apply DJhull; clear - Hc' Q2 Q3 Q4 MFB'; lia.
        + unfold region_beg, kRegionSize, shad. pose proof (carve_end8 h c' WL WR Hc') as A8. unfold region_beg, kRegionSize in A8.
          pose proof (Z.div_mod (l_sb (h_L h) + c' * 2^32 + r_alloc_user (h_reg h c')) 8 ltac:(clear; lia)) as D1. rewrite A8, Z.add_0_r in D1.
          pose proof (Z.div_mod (r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) 8 ltac:(clear; lia)) as D2.
          pose proof (Z.mod_pos_bound (r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) 8 ltac:(clear; lia)) as D3.
          pose proof (shad_disj_gen _ (r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) hb ms A8 HAL8 ltac:(clear -MSB; lia) ltac:(clear - HLH Q1 Q2 Q4 AUMU'; lia)) as SD. unfold AW_FreeG.shad in SD. subst Sh kk.
          apply KOM. apply DJband; [clear - D1 Q2 AUMU' SB0 Hc' B6a B6c; unfold kHighMemBeg in B6c; lia| clear - D1 D2 D3 Q1 AUMU' RI1 ACB; lia| clear - SD D2 D3; lia].
        + intros k0 Hk0. assert (Hk0' : 0 <= k0 < carved h c') by (unfold carved; exact Hk0).
          destruct (slot_le h c' k0 WR Hc' Hk0') as [S1 S2]. unfold region_beg, kRegionSize in S1, S2.
          pose proof (chunk_at8 (h_L h) c' k0 WL Hc') as A8. pose proof (class_size_range c' Hc') as CSR'.
          pose proof (shad_disj_gen (chunk_at (h_L h) c' k0) 8 hb ms A8 HAL8 ltac:(clear -MSB; lia) ltac:(unfold chunk_at, region_beg, kRegionSize in *; clear - HLH S1 S2 CSR' Q1 Q2 Q4 AUMU'; lia)) as SD.
          change (8 / 8) with 1 in SD. unfold AW_FreeG.shad in SD. unfold shad. subst Sh kk.
          pose proof (Z.div_mod (chunk_at (h_L h) c' k0) 8 ltac:(clear; lia)) as D1. rewrite A8, Z.add_0_r in D1.
          apply KOM. apply DJband; [unfold chunk_at, region_beg, kRegionSize in *; clear - D1 S1 Q2 SB0 Hc' B6a B6c; unfold kHighMemBeg in B6c; lia| unfold chunk_at, region_beg, kRegionSize in *; clear - D1 S2 AUMU' Q1 RI1 CSR' ACB; lia| clear -SD; lia].
      - unfold region_beg, kRegionSize. clear - HLH Q1 Q2 Q4 AUMU'. lia. }
    (* [comment removed for export] *)
    pose proof (swap_remove_length (s_chunks (h_sec h)) si _ NTHS) as SRL.
    assert (KIW : forall A n', A_INSTANCE + 129 <= A -> A + n' <= A_INSTANCE + 680 -> (A + n' <= A_INSTANCE + 144 \/ A_INSTANCE + 160 <= A) -> kept m m4 A n').
    { intros A n' H1 H2 H3. apply KOM. subst W. unfold rs_W. cbn [disjoint_from]. unfold A_GSTATS, A_SEC_MUTEX, A_INSTANCE, kHighMemBeg in *. subst Sh kk.
      clear - H1 H2 H3 STK0 LOL T0 PALH LGEO E5 E1 ACB DH DHB. repeat split; lia. }
    assert (G7' : hm_sec h' m4).
    { unfold hm_sec. unfold h'. rewrite (recs_L h k si), (recs_secl h k si), (recs_nres h k si), (recs_pa h k si). cbn zeta. rewrite SRL.
      replace (Z.of_nat (length (s_chunks (h_sec h)) - 1)) with (ncks - 1) by (subst ncks; clear -SIL; lia).
      ddestruct SEC4 as (SQ1 & SQ2 & SQ3 & SQ4 & SQ5).
      change [C8 (Z_to_bv 64 (s_nres (h_sec h))); C8 (Z_to_bv 64 (ncks - 1)); C1 (Z_to_bv 8 0)] with ([C8 (w64 (s_nres (h_sec h))); C8 (w64 (ncks - 1))] ++ [C1 (Z_to_bv 8 0)]) in SQ2.
      apply rw_cells_app in SQ2 as [SQ2a SQ2b]. cbn [cells_size csize Nat.add] in SQ2b. replace (A_INSTANCE + 112 + Z.of_nat 16) with (A_INSTANCE + 128) in SQ2b by (clear; lia).
      split; [exact SQ2a|]. split; [exists (Z_to_bv 8 0); exact SQ2b|].
      split. { exists [st0; nfr'; cal'; st3]. split; [| reflexivity]. cbn [map].
               change [C8 st0; C8 nfr'; C8 cal'; C8 st3] with ([C8 st0] ++ [C8 nfr'; C8 cal'] ++ [C8 st3]).
               apply rw_cells_app. split; [eapply krw; [exact SC3a| apply KIW; cbn; clear; lia]|]. cbn [cells_size csize Nat.add].
               apply rw_cells_app. split; [replace (A_INSTANCE + 136 + Z.of_nat 8) with (A_INSTANCE + 144) by (clear; lia); exact SQ3|].
               cbn [cells_size csize Nat.add]. replace (A_INSTANCE + 136 + Z.of_nat 8 + Z.of_nat 16) with (A_INSTANCE + 136 + Z.of_nat 8 + Z.of_nat 16) by reflexivity.
               eapply krw; [exact SC3c| apply KIW; cbn; clear; lia]. }
      split. { exists bsl. split; [| exact L4]. eapply ku64; [exact SC4| rewrite L4; apply KIW; cbn; clear; lia]. }
      split. { unfold A_SEC_MUTEX in SQ5. eapply rw_cells_reshape; [exact SQ5| cbn; repeat split; exact I| reflexivity]. }
      split. { dexists g2', g3'. unfold A_GSTATS in SQ4. replace (A_INSTANCE + 688 + 16) with (A_INSTANCE + 704) in SQ4 by (clear; lia). exact SQ4. }
      (* [comment removed for export] *)
      rewrite Nat2Z.id in ARR4. rewrite <- (firstn_skipn (length (s_chunks (h_sec h)) - 1) (upd bases si last)) in ARR4. rewrite map_app in ARR4.
      apply u64arr_app in ARR4 as [AP1 AP2]. rewrite length_map, firstn_length_le in AP2 by (rewrite upd_length; clear - LB SIL; subst ncks; lia).
      assert (SRU : firstn (length (s_chunks (h_sec h)) - 1) (upd bases si last) = map s_map_beg (swap_remove si (s_chunks (h_sec h)))).
      { subst bases last. rewrite <- (length_map s_map_beg (s_chunks (h_sec h))) at 1.
        rewrite (swap_remove_upd (map s_map_beg (s_chunks (h_sec h))) (map (fun w : word => bv_unsigned w) rest) si hb (s_map_beg shl));
          [| rewrite nth_error_map, NTHS; reflexivity| rewrite length_map, nth_error_map, NL; reflexivity].
        first [exact (swap_remove_map s_map_beg (s_chunks (h_sec h)) si _ NTHS) | symmetry; exact (swap_remove_map s_map_beg (s_chunks (h_sec h)) si _ NTHS)]. }
      rewrite SRU, map_map in AP1.
      split; [exact AP1|].
      split. { exists (map (Z_to_bv 64) (skipn (length (s_chunks (h_sec h)) - 1) (upd bases si last))). split.
               - replace (8 * (ncks - 1)) with (8 * Z.of_nat (length (s_chunks (h_sec h)) - 1)) by (subst ncks; clear -SIL; lia). exact AP2.
               - rewrite length_map, length_skipn, upd_length. destruct LB40 as (LBE & _). rewrite <- LBE. subst ncks. clear - LB SIL. lia. }
      (* [comment removed for export] *)
      intros j sh Hj. destruct (swap_remove_nth (s_chunks (h_sec h)) si _ shl NTHS NL j sh Hj) as [JL [(-> & ->)|(NEj & Nj)]].
      - (* [comment removed for export] *)
        assert (SIL' : Z.of_nat si < ncks - 1) by (subst ncks; clear - JL; lia).
        split; [fold last; exact (LHDR4 SIL')|].
        apply (wro m m4 hb ms WMO); [exact LWR|]. fold last.
        pose proof (z_sec_sec h GEO _ si _ _ NL NTHS ltac:(clear -JL; lia)) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. fold last hb ms in Y. clear -Y. lia.
      - pose proof (SHD j sh Nj) as [HDj WRj].
        assert (NEl : j <> (length (s_chunks (h_sec h)) - 1)%nat) by (clear - JL; lia).
        pose proof (z_sec_sec h GEO j si _ _ Nj NTHS NEj) as Y5. pose proof (z_sec_sec h GEO j _ _ _ Nj NL NEl) as Y6.
        pose proof (z_sec_T h GEO j _ Nj) as Y1. pose proof (z_sec_stk h GEO j _ Nj) as Y3. pose proof (z_sec_band h GEO j _ Nj) as Y4. pose proof (z_sec_pa h GEO j _ Nj) as Y7.
        unfold zapart in Y1, Y3, Y4, Y5, Y6, Y7. cbn [fst snd s_map_beg s_map_size] in Y1, Y3, Y4, Y5, Y6, Y7. fold hb ms in Y5. fold last in Y6.
        pose proof (proj1 (Forall_forall _ _) WS8 _ (nth_error_In _ _ Nj)) as (_ & M4j & _).
        ddestruct (WKSEC j sh Nj) as (kj & Hkj & Pj & MBj & MSj). pose proof (proj1 (Forall_forall _ _) WKF kj Hkj) as (_ & _ & _ & Xj). rewrite Pj in Xj.
        ddestruct Xj as (_ & _ & _ & POSj & CEILj & LHj). rewrite MBj, MSj in CEILj, LHj. rewrite MBj in POSj. unfold lowhigh, kHighMemBeg in LHj.
        split.
        + eapply krw; [exact HDj|]. cbn [cells_size csize Nat.add]. apply KOM. apply DJgen; unfold A_INSTANCE in *;
            [clear - Y3 M4j LOL SPL SPHI; lia| clear - Y1 M4j; lia| clear - LHj M4j; lia| clear - Y7 M4j; lia| clear - Y6 M4j LGEO; lia| clear - Y4 M4j CEILj LHj SKB ACB; lia| clear - Y5 M4j; lia].
        + apply (wro m m4 hb ms WMO); [exact WRj| clear -Y5; lia]. }
    (* [comment removed for export] *)
    dpose WL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS0 & FS1 & _). unfold lowhigh, kHighMemBeg in FS0.
    assert (DJfs : forall A n', l_fs (h_L h) <= A -> A + n' <= l_fs (h_L h) + kFakeBytes -> kept m m4 A n').
    { intros A n' H1 H2. apply KOM. apply DJgen; unfold kFakeBytes, A_INSTANCE in *;
        [clear - H1 H2 Zfs3 LOL SPL SPHI; lia| clear - H1 H2 Zfs1; lia| clear - H1 H2 FS0; lia| clear - H1 H2 ZFP; lia| clear - H1 H2 YlF LGEO; lia| clear - H1 H2 Zfs4 SKB; lia| clear - H1 H2 ZsF; lia]. }
    assert (G8' : hm_fake h' LF m4).
    { unfold hm_fake. unfold h'. rewrite (recs_L h k si). pose proof G8 as G8u. unfold hm_fake in G8u.
      apply (fake_rep_k m m4 (l_fs (h_L h)) LF G8u); [clear -FS0; lia| apply DJfs; unfold kFakeBytes; clear; lia|].
      intros FB nB HFB. ddestruct G8u as (_ & _ & _ & LFW & _). destruct (LFW _ HFB) as (kf & ii & Hkf & Hii & EFB).
      pose proof (fsk_frame_inside (l_fs (h_L h)) kf ii Hkf Hii) as [I1 I2]. pose proof (fsk_sizes kf Hkf) as (SZ1 & _).
      assert (EF1 : FB = fsk_frame (l_fs (h_L h)) kf ii) by (clear -EFB; congruence). assert (EF2 : nB = fsk_bytes kf) by (clear -EFB; congruence).
      rewrite EF1, EF2. apply DJfs; clear - I1 I2 SZ1; lia. }
    assert (G9' : hm_ia h' m4).
    { apply (hm_ia_k m m4 h G9); [apply IAG; vm_compute; reflexivity| apply recs_ia]. }
    assert (GE' : hm_emb h' m4).   (* [comment removed for export] *)
    { apply (hm_emb_o m m4 hb ms WMO h h' GE); [reflexivity| reflexivity| apply IAG; vm_compute; reflexivity|].
      intros NZ. pose proof (z_sec_emb h GEO si _ NTHS NZ) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. fold hb ms in Y. clear - Y. lia. }
    (* [comment removed for export] *)
    assert (KB : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> kept m m4 (b_addr b) 8192).
    { intros b Hb. apply KOM. ddestruct (batch_slot h b WF Hb) as (ib & Hib & EBb).
      destruct (slot_le h kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2]. rewrite <- EBb in S1, S2.
      dpose (user_vs_ri h kBatchClass WL WR ltac:(unfold kBatchClass; clear; lia)) as (Q1 & Q2 & Q3 & Q4).
      pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
      unfold kBatchClass in S1, S2, Q1, Q2, Q3, Q4, AUMU'. change (class_size 24) with 8192 in S2.
      unfold fa_beg, kFreeArrayOffset, kFreeArraySize, region_beg, kRegionSize in Q1, Q2, Q3, S1, S2.
      apply DJhull; clear - S1 S2 Q1 Q2 Q4 AUMU'; lia. }
    assert (RQ' : RIq h' C (Some (bc, S i)) m4).
    { apply (RIq_pop h h' C bc i m4).
      - apply (RIq_k m m4 h C (Some (bc, i)) RQ).
        + apply KOM. apply DJT; clear; lia.
        + apply IAG; vm_compute; reflexivity.
        + apply KOM. apply DJgen; unfold A_INSTANCE in *; [right; clear -CB0 CB1; lia| clear - ZTS LOL SPL CB0 CB1 CHI; lia| clear - STK0 LOL SPL CB0 CB1 ACB; lia| clear - ZPS LOL SPL CB0 CB1 CHI; lia
                                                            | clear - YlS LGEO LOL SPL CB0 CB1 CHI; lia| clear - STK0 LOL SPL CB0 CB1 ACB SKB; lia| clear - ZsS LOL SPL CB0 CB1 CHI; lia].
        + exact KB.
        + cbn beta iota. rewrite <- EA. apply KB. rewrite E0. left. reflexivity.
      - exact (recs_L h k si).
      - exact (recs_gq h k si).
      - intros bq tq' Eq. exact (recs_tq h k si bq tq' Eq).
      - exists (Z_to_bv 64 (ck_hdr k)). exact NTH. }
    (* [comment removed for export] *)
    pose proof (ff_view_K AL FF (h_rec_sec h k si) h' mo4 (kview_recs h k si) HK4) as HK'.
    assert (CSM : forall x, ff_CS AL FF h x -> ~ (hb <= x < hb + ms) -> ff_CS AL FF h' x).
    { intros x Hx NH. apply (ff_view_CS AL FF (h_rec_sec h k si) h' x (kview_recs h k si)). exact (ff_cs_rec_sec AL FF h k si x NTHS Hx NH). }
    (* [comment removed for export] *)
    assert (FK : fkeepR (h_L h) (blocks h) QS (map (fun sh => (s_map_beg sh, 32)) (s_chunks (h_sec h))) (d_nb (h_dep h)) (d_bl (h_dep h)) lo SP m m4).
    { apply (fkeepR_of_munch _ _ _ _ _ _ _ _ W m m4 MU). subst W. unfold rs_W.
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. left. exact Ha. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. right; left. clear - Ha; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. right; left. clear - Ha; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 5 right; left. unfold free_img_ranges, A_INSTANCE in *. cbn. clear -Ha; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 5 right; left. unfold free_img_ranges, A_INSTANCE in *. cbn. clear -Ha; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 5 right; left. unfold free_img_ranges, A_GSTATS, A_INSTANCE in *. cbn. clear -Ha; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 5 right; left. unfold free_img_ranges, A_SEC_MUTEX, A_INSTANCE in *. cbn. clear -Ha; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 8 right; left. clear - Ha LB40 SIL LB; subst ncks; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 9 right. exists (last, 32). split; [| cbn [fst snd]; clear -Ha; lia].
                           subst last. apply (in_map (fun sh => (s_map_beg sh, 32)) _ _ (nth_error_In _ _ NL)). }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 4 right; left. exists (hb, ms). split; [exact HQS|]. right. cbn [fst snd]. unfold shad. subst Sh kk. clear -Ha; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 4 right; left. exists (hb, ms). split; [exact HQS|]. left. cbn [fst snd]. clear -Ha; lia. }
      apply Forall_nil. }
    (* [comment removed for export] *)
    apply HC. unfold sec_step_post.
    eexists. dexists mo4, y0, y1, y2, ya0, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m4.
    split; [reflexivity|]. split; [rewrite TP; reflexivity|]. split; [exact WF'|].
    split. { unfold HMq. unfold h'. rewrite (recs_L h k si). exact (conj G0' (conj G1' (conj G2' (conj G3' (conj G4' (conj G5' (conj G7' (conj G8' (conj G9' GE'))))))))). }
    split; [exact RQ'|]. split; [exact HK'|]. split; [exact HJ4|]. split; [exact CSM|]. split; [exact FK|]. exact (conj WMO (conj MI4 ST4)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RecStepSec.
End ARUN_1.
