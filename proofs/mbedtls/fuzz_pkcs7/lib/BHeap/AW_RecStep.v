(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR AW_FreeFam.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_Poison AW_Populate
     AW_DepotA AW_DepotB AW_DepotC AW_DepotInv AW_DepotTop AW_MallocA AW_AllocA AW_AllocB AW_MallocB AW_MallocC AW_ClassId AW_Combined AW_Refill AW_Large
     AW_CfgS AW_CfgDefs AW_PopulateCfgS AW_PoisonBig AW_SMalloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_QPut AW_Enqueue AW_CbRecycle AW_LCDealloc AW_RTA AW_RecLC AW_RecChunk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs AW_FakeRep HMLib HM HMFrame AW_FreeHM AImgW.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
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
Ltac2 gd_tbl_AW_RecStep () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_ro"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecChunk.rp_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_sb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_base"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctx"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PoisonBig.rsmr_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Large.large_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_L"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctxlen"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_recp"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.WFR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.HMq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.RIq"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.S"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_K"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_CS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.fkeep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "Corelib.Init.Datatypes.true"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_QUARANTINE"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "Stdlib.Lists.List.nth_error"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_elems"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_hdr"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_1.RecStep.prim_step_post"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.A_CB_RECYCLE"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

(* [comment removed for export] *)
#[using="Type"] Lemma kept_of_munch : forall W m m' A n, munch W m m' -> disjoint_from W A n -> kept m m' A n.
Proof. intros W m m' A n MU DJ x Hx. apply MU. exact (disjoint_outside W A n _ DJ Hx) || (revert x Hx; induction W as [|[u v] W IH]; intros x Hx; cbn in *; [exact I| split; [destruct DJ as [D _]; lia| apply IH; [destruct DJ; assumption| exact Hx]]]). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hm_ro_free : ltac2:(CDefT.buildp (gd_tbl_AW_RecStep ()) "PL,$0.Pm,P,(1.&40.)(2.(1.&8.))P,(3.R2.R1.)(4.(5.R2.(6.R3.)(7.R3.)(8.R3.)(9.R3.))(4.(:.(1.&40.)Lcan,(1.&40.)(:.(1.&8.)Ldd,(1.&8.)(:.(1.&8.)Lmadv,(1.&8.)(;.R5.R3.R2.R1.))))(<.R2.(=.R3.))))")
(* [comment removed for export] *).
Proof.
  intros L m RO. unfold hm_ro in RO. cbn zeta in RO.
  ddestruct RO as (MSEG & ALLOCA & POI & FIN & DEPS & THR & LARGE & GPZ & PZC & GCF & DEC & MML & INTV & PREM & SBC & RIC & PPART & MH8 & QMAX & MRN & CTX8
                  & TCTX & T8 & T40 & T72 & F88 & UARG & UARC & (can & dd & madv & RS) & SMS & F5W & TLSB & IMC & RMC).
  dpose DEPS as (_ & (_ & _ & _ & _ & _ & GS2 & DY) & _).
  dpose RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GDY & _ & _).
  split; [| split; [dexists can, dd, madv; exact RS| exact LARGE]].
  split; [| exact MH8].
  split; [exact (conj INTV (conj PREM SBC))|]. split; [exact RIC|]. split; [exact (conj GPZ (conj PZC (conj GCF (conj DEC (conj MML (conj GS2 (conj GDY DY)))))))|].   (* [comment removed for export] *)
  split; [exact THR|]. split; [exact POI|]. exact (conj GS2 (conj GDY DY)).
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L25452278944.1200000CS1X1l1i2Hi3pre4Hlen". (* [comment removed for export] *)
#[using="Type"] Lemma firstn_upd_snoc : forall {X} (l : list X) i x, (i < length l)%nat -> firstn (S i) (upd l i x) = firstn i l ++ [x].
Proof.
  intros X l i x Hi. ddestruct (upd_app_split l i x Hi) as (pre & y & post & E & Hlen & Hupd). rewrite Hupd, E.
  replace (S i) with (length pre + 1)%nat by lia. rewrite firstn_app_2. cbn. rewrite <- Hlen, firstn_app, Nat.sub_diag, firstn_all. cbn. rewrite app_nil_r. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma skipn_cons_nth : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros X l i. revert l. induction i as [|i IH]; intros l x H; destruct l as [|y l]; cbn in H; try discriminate H.
  - injection H as ->. reflexivity.
  - cbn [skipn]. exact (IH l x H).
Qed.

Section RecStep.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Variable FF : ffam AL.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L15083701775.15L25160693192.14L25163738313.14L51122693041.1400000700>00O00\S3hAR1LS3hAR1LS3hAR1L3M162B12B3S3hAR1L2B42B5". (* [comment removed for export] *)
  #[using="Type"] Lemma L_GSB : ltac2:(CDefT.buildp (gd_tbl_AW_RecStep ()) "PL,$0.P,(>.VhAR,R1.)(4.(?.+10007???9000.(6.R2.))(4.(10.$11.(12.(6.R2.)+1000.)=)(4.(10.$11.(7.R2.)(13.(6.R2.)(14.+2.+25.)))(?.(13.(7.R2.)+1000.)(15.VhAR,)))))")
(* [comment removed for export] *).
  Proof.
    intros L WL. dpose WL as (M16 & B1 & B2 & _ & B3 & B4 & B5 & _). unfold ri_base, space_end, kSpaceSize, kHighMemBeg in *.
    split; [lia|]. split; [| split; [reflexivity| lia]].
    pose proof (Z.div_mod (l_sb L) (2^16) ltac:(lia)) as D. rewrite M16, Z.add_0_r in D. rewrite D.
    replace (2^16 * (l_sb L / 2^16)) with ((16 * (l_sb L / 2^16)) * 4096) by lia. apply Z_mod_mult.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L21354196393.1100000AS3hAR1L3TAL2T02T1". (* [comment removed for export] *)
  #[using="Type"] Lemma L_GT : forall L, wf_L L -> (Timg (l_T L) /\ Tband (l_T L)) /\ l_T L + 4096 <= ACEIL /\ l_T L mod 4096 = 0.
  Proof. intros L WL. dpose WL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TAL & T0 & T1 & _). unfold lowhigh, kHighMemBeg in *. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L60164052936.1100000@S3hAR1L2C02C12CL". (* [comment removed for export] *)
  #[using="Type"] Lemma L_GCTX : ltac2:(CDefT.buildp (gd_tbl_AW_RecStep ()) "PL,$0.P,(>.VhAR,R1.)(4.(4.(?.+65?000.(8.R2.))(16.(?.(13.(8.R2.)+10000.)+7???7000.)(?.+10007???8000.(8.R2.))))(4.(?.(13.(8.R2.)+10000.)(15.VhAR,))(10.$11.(17.R2.)+10000.)))")
(* [comment removed for export] *).
  Proof. intros L WL. dpose WL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C0 & C1 & CL & _). unfold lowhigh, kHighMemBeg in *. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition prim_step_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : ahst) (k : chunk) (LF : list (Z * Z)) (bc : bnode) (i : nat) (C lo : Z) (QS : list (Z * Z)) (m : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecStep ()) "Lcf,$18.(:.$19.Lms',$19.(:.$1:.Lmo',$1:.(:.(1.&40.)Lt0,(1.&40.)(:.(1.&40.)Lt1,(1.&40.)(:.(1.&40.)Lt2,(1.&40.)(:.(1.&40.)La0,(1.&40.)(:.(1.&40.)La1,(1.&40.)(:.(1.&40.)La2,(1.&40.)(:.(1.&40.)La3,(1.&40.)(:.(1.&40.)La4,(1.&40.)(:.(1.&40.)La5,(1.&40.)(:.(1.&40.)La6,(1.&40.)(:.(1.&40.)La7,(1.&40.)(:.(1.&40.)Lt3,(1.&40.)(:.(1.&40.)Lt4,(1.&40.)(:.(1.&40.)Lt5,(1.&40.)(:.(1.&40.)Lt6,(1.&40.)(:.P,(1.&40.)(2.(1.&8.))Lm',P,(1.&40.)(2.(1.&8.))(:.$1;.Ldr,$1;.(:.$1<.Lcnt,$1<.(:.(2.$1;.)Lf,(2.$1;.)Zh',$1=.(1>.O9.O8.R3.R2.R1.)(4.(10.$18.R17.(1?.R16.R15.))(4.(10.$19.R16.(20.(21.O1;.(22.&40.O1:.)O19.O18.R14.R13.R12.O17.O16.R11.R10.R?.R>.R=.R<.R;.R:.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R9.R8.R7.R6.)O;.(23.O1;.)O:.(24.(1.&40.))R5.(25.$26.)))(4.(27.VhAR,R1.)(4.(28.VhAR,R1.O7.R5.)(4.(29.VhAR,R1.O4.(2:.(2;.$2<.$1<.)(2=.$2<.$1<.O6.(2>.O5.)))R5.)(4.(2?.VhAR,VAL,VFF,R1.R15.)(4.(30.R5.R15.)(4.Px,$11.P,(31.VhAR,VAL,VFF,O9.R1.)(31.VhAR,VAL,VFF,R3.R2.)(4.(32.(33.O9.)(34.O9.)O2.(35.(36.O9.))(37.(36.O9.))O3.O1:.O1.R5.)(4.(38.$26.O1.R5.)(4.(39.$26.R5.)(3:.$26.R5.O3.O1:.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "04a0@L10344898345.4  L10447018765.11 L10447018892.11 L10967500938.6  L10996078549.8  L11027764026.5  L1122136281.20  L12227744722.4  L12403725915.9  L12533453626.6  L12556558205.3  L13016709440.23 L13016856771.21 L13016856771.22 L13016856771.26 L13016856896.24 L13016857541.38 L13016858319.26 L13237742829.4  L13385894424.5  L13980663862.13 L13980663862.8  L13980663862.9  L14150857017.3  L14248649251.3  L14736408896.1  L14866252223.6  L14880938372.2  L14880938373.2  L15203606842.12 L15274682276.7  L15344582979.12 L15539138780.2  L15566092477.16 L15702086826.2  L15990724489.4  L16098078423.0  L1629961578.5   L16487879084.23 L16538553883.16 L16545396873.4  L16644912580.5  L1704500591.1   L1708726497.5   L17120848823.0  L17483560448.3  L18137758790.4  L18156986921.38 L18156988195.26 L18474117133.18 L18486530567.21 L18587524524.18 L19325175423.3  L19327300958.8  L19345011040.3  L19345011936.6  L19346787921.10 L19346787921.6  L19346787921.7  L19346787921.8  L19505738506.9  L19505738635.9  L19987118970.6  L2024163583.1   L2063457712.7   L20896290651.11 L21438023802.5  L21623724490.2  L21640453532.7  L22583788388.3  L22889257155.5  L23051537390.16 L23141750293.14 L2424906846.3   L2464680509.4   L25003717198.2  L25070469102.3  L25510019075.38 L25510020361.26 L25553707153.7  L25659078307.3  L25752540516.8  L25787593781.2  L26259017146.27 L26940997473.12 L26940997473.13 L26940997473.14 L26940997473.3  L26940997473.6  L26940997473.7  L26940997473.9  L26975107951.4  L26975108078.4  L27177693897.7  L2728726238.3   L27697239754.6  L2803598120.4   L28089937842.8  L28956411306.1  L28998937637.21 L29003486767.18 L29198200741.5  L29300458413.11 L29658499875.26 L29658500649.38 L29705728350.3  L2978961816.0   L30329225028.20 L30458420453.9  L30894052965.10 L31228701566.23 L31229111037.21 L31229111037.22 L31229111037.26 L31229111166.24 L31677218851.3  L31904717137.26 L31904717915.38 L31904718558.24 L31904718685.21 L31904718685.22 L31904718685.26 L32253233187.26 L32253234473.38 L32337938074.21 L32341982352.18 L32931146339.3  L33061060028.8  L3308849698.8   L33470790221.10 L33470790221.14 L34580967580.5  L35035954062.11 L35267160734.4  L35269483449.1  L35383315119.22 L35389966226.7  L35521637653.20 L36270066207.4  L36303819675.14 L36407217492.8  L3668345764.2   L37099668332.6  L37151697262.3  L37151698158.6  L37637199976.0  L37804114501.3  L38019136925.21 L38031542167.18 L38356265165.7  L38651962962.2  L38692635477.0  L39172636981.0  L39268637205.0  L39332637397.0  L39371954277.9  L39476823582.3  L39531535603.2  L39684650846.3  L39742210159.21 L40091481971.2  L40166712592.11 L40185221850.2  L40395379247.16 L40401253682.0  L41008919275.5  L41372190655.3  L41416057805.8  L42141700319.6  L42165362595.20 L42301244845.11 L43018014016.5  L43018014016.7  L43158424701.7  L43432397626.6  L43675124393.16 L4368349344.24  L4368349475.21  L4368349475.22  L4368349475.26  L4368349733.38  L4368351023.26  L43713642275.3  L43998702901.3  L43998703028.3  L44013154193.8  L44033659131.38 L44033660401.26 L4485118374.11  L45272723798.27 L45658831793.26 L45658832571.38 L46159287405.8  L46467458831.4  L46636569438.38 L46636570196.26 L46649821521.20 L47096186853.2  L477335768.24   L477335899.21   L477335899.22   L477335899.26   L477483224.23   L47814975085.5  L48096899947.3  L48147828586.13 L48188633495.16 L48674796451.26 L48674797225.38 L48802774710.8  L48964674115.38 L48964675401.26 L4969361213.4   L50209480639.10 L51025133614.11 L51025534038.4  L51322266494.2  L51518163375.1  L51539028393.160L51818430760.6  L51981969576.2  L5215044130.6   L52951741110.13 L53216299775.13 L53537163620.4  L53710725399.8  L54159793143.7  L54237170457.4  L5425673087.27  L54470327665.9  L54582041019.3  L55099840816.5  L55195728159.4  L55588686165.0  L55653771692.38 L55653771819.10 L55653771946.21 L55653771946.23 L55653771946.27 L55653772073.25 L55653772454.26 L5713963340.2   L57169543802.9  L57169543931.7  L5721498072.17  L57694036009.38 L57694037283.26 L57747755130.6  L58038212413.7  L58559626927.21 L58559626927.22 L58559626927.26 L58559627052.24 L58565236830.3  L59135868495.8  L59136380947.5  L59308857809.9  L59315137787.10 L59315137787.12 L59315137787.7  L59514603121.4  L59551301595.7  L59588422338.2  L59651323709.4  L59727773228.2  L59971791905.9  L60070416074.5  L6025098890.4   L6028618793.13  L6028750508.15  L60542002201.23 L60785358792.0  L60837792237.4  L6110676881.4   L6128467596.8   L61519252226.3  L61975288227.26 L61975289001.38 L62441692029.5  L62947420491.4  L63181313848.2  L6336436530.7   L63380764809.7  L64327673430.8  L64612082378.0  L65314923015.6  L65364830649.3  L65522324618.5  L65621996669.21 L65621996669.22 L65621996669.26 L65621997054.24 L65627227280.5  L65706468689.8  L65706664013.157L66080017260.8  L6646336923.3   L66469708956.4  L66750448085.20 L67559118284.4  L7084044322.158 L7603473955.3   L7641248013.8   L777962750.0    L8118647786.0   00000700]01C01L01^01f02J02Q02g03603F04:04o05Z06c07J08A08n09909I09m0:I0:c0:n0;70;;0;R0;Z0;b0<H0<^0=A0=H0=a0=h0=o0>00>A0>]0>l0?30?@0?C0?P0?Q0?Y0?`0@o0AF0Ak0BI0Bn0C70CB0CK0C\0D;0DQ0Dh0EG0Ec0F?0FH0FL0Fe0GD0GQ0GX0Gj0H30H=0I30Ib0Ij0J10J80JC0KE0L:0LP0LW0Lh0Ll0ML0N50N_0OP0OX0Oh0P>0PY0Pe0Q10Q?0QF0QO0Q[0Qo0R30R_0SB0SL0S]0T40UC0UJ0UK0VO0Vk0WP0X90Xj0YQ0ZV0[=0[D0[[0\Q0]40]]0^E0_;0_R0`a0a60aN0aU0ao0b40bY0cF0cU0d80dH0dL0e70eE0e^0ee0fU0fm0g30gD0gM0g^0g_0gj0hX0hk0iC0iI0iJ0iK0iL0iM0ij0j10j90j@0j]0jc0kD0kI0kk0kl0l?0lH0lO0l]0m?0mW0me0n80nU0n^0o60oY10B10j11`12V12m13413<13D13Q14214I15115C15Z16i17317>17m18V19119619]1:F1:k1;h1<P1<`1<i1=R1=h1>?1?N1?Y1@^1AS1AZ1B<1BW1B^1Bf1Bj1CL1Cf1Cl1D=1Df1ER1EY1Ek1F<1FG1Fn1GJ1GS1Ge1Gl1Gm1Hj1ID1J31J]1KJ1L81LU1L[1Lo1M=1NW1O81OO1O^1P61P_1QJ1R:1Rh1Ro1S<1SF1Sb1T?1Td1U61UA1UY1Ua1Uh1Uo1VG1VO1VZ1WG1X<1Xd1Xe1Y01Y71YN1YV1Ym1ZN1Z^1Ze1Zm1[;1[H1[b1[c1\71\A1\K1]41]_1^O1_=1_M1_T1`;1`M1`V1`]1a=1aD1ab1ai1b01b11b2S1h1k1cS1h2SP3CBP1C2lo3CB03CB13CHI3LOL3SPL2Y2S1h2SP3CBP1C2lo3CB03CB13CHI3LOL3SPL2Y1S1h5Zctx4S3hAR1h2T03ACB3B6cS1h4Zdt3S1h1k1c1r2mu2au4AUMU3URI4KSL22c'3Hc'S1h1k1cS3hAR1h2SP2lo3LOL4STK0S1h5Zctx15Zctx2S1h4Zpa12S44Zpa2S1h1k1c3C301r3mfa3NF02k'3RL'3RH'1A2n'2HA2HB5AUMU'2Q5S1h1k1n1c3C303B6a3B6e1r3mfa3SKB3SFB3NF05SLOTH1A2n'2H3S3hAR1h1k1n1c3C303B6a3B6c1r3mfa3NF01A2n'2H2S3hAR1h1k1n1c3C302T03B6a3B6e3ZTH1r3mfa3SKB3SFB3NF05SLOTH1A2n'2H12H22H32H4S3hAR1h1k1n1c3C301r3mfa3SKB3SFB1A2n'2H5S3hAR1h1k1n1c3HRI1r2mu2au3mfa3NF44ROOM3MCR4FARI1A2n'2H1S1h1k1n1c1r3mfa3NF44ROOM3MCR2NB2E11A2n'2H62H7S1h1k1c3C30S1k1c3MCR2Dm3Dm'S3hAR1h1k1c3RI11r2mu2au3URI2D12D22D3S3hAR2k'2F32F64NFX'2D12D22D3S3hAR1h3RI12c'2Q12D12D22D3S1h4Zpa42S4S1k1n3SKBS2k'S1h3B6a3B6e3ZTH3ZTC3ZCHS1h4Zfs1S1h4Zfs2S1h1k1c1a2kb2Xb2c'3RL'3RH'5AUMU'2Q12Q5S1h1k1c3C302c13Hc13NE1S1h1k1n1c1j3RZN3RZR3HHD3HAB2E22k01XS2k'2F3S1h1k1c3C301b2S22Q15AUMU'S2k'2C'S1h1k1cSS1h3CBP1C3CB13CHIS1h1k1c1r3mfa2k'3RL'1A2HA2Q2S1h1k1c1b2S12Q2S1h1k1cS1h1k1c1r3mfaS1kS1h1k1c1r3mfaSS1k1n2NBS1k1c1pS3hAR1h1k1n1c3C303HRI3ZTH1r2mu2au4AUMU3mfa3MCR3SKB3SFB4B6RB4FARI3RIH1A2n'2H12H2S1h1k1n1c1r3mfa1A2n'2H3S1h1k1c3C301r2mu2au3mfa3NF44ROOM4FARIS1h1k1c3C301r2mu2au2c'4MFB'2Q3S1h1k1c1r2mu2au3mfa3NF44ROOM4FARI3RIHS1k1c3CSRS1k1c1p3MCRS1k1n3SKBS1h1k1c1r3mfa3SFBS1h1k1c3C303SB01r2mu2au4AUMU2D1S2k'3RZ'2F53XAB3UIN2D1S1h3SB02c'3Hc'5AUMU'2D1S1h1k1c3C303SB02k02S12D12c'3Hc'S1h2k'3EL'3EH'1A2n'2HA2HB2Y2S1h2k'3EL'3EH'1A2n'2HA2HB2Y1S1h5Zctx3S2kbS1h2SP3CBP2lo3CB03LOL3SPLS1h1k1c1r3mfa2kb1X2F12F22F33NFbS1h4Zdt14Zdt2S2c'2C'S1k1c1r2mu2au4AUMUS1k1c3CSRS1k1c1p2D1S1h1k1n1c1r2mu2au4AUMU2E12E24KSL14KSL23UKE2c'5AUMU'2Q7S3hAR1h1k1c3C303SB03HRI3RI11r3mfa3MFB4ROOM1H2H0S1k1n2KNS1h1k1cS2k'2C'S2k'2F43UINS3hAR1h1k1n1c3HRI1r2mu2au4AUMU3mfa2E22E43URI4B6RB3RIH4KSL21A2n'2H1S1h1k1n1c1r3mfa3NF44ROOM2NB2E12E22E41A2n'2H42H62H72H8S1h1k1c1r3mfa4CARB3MFXS1h1k1cS1k1c1r2mu2au3CSRS2k'S3hAR1h1k3CBP1C3CB13CHI1n1c4STKHS1h1k1c1r3mfa3MFB4ROOM4B6RB4FARI3RIH1a2HaS1h1k1c3C301r2mu2au4AUMU3URI4B6RB3RIH1a2HaS1h1k1c1r3mfa3NF44ROOM3MCR3NF04B6RB4FARI3RIH1a2HaS1h1a2HaS1h1k1c3C301a2HaS1h1k1c3CSR5SLOTH1a2HaS1h1k1c2E12E22E45SLOTH1a2HaS1h2sh2SZ2Y2S1h2sh2SZ2Y1S1h1k1c2c13Hc1S1h1k1cS1h5Zctx4S1h2sh2SZ2Y3S1k1c1p3MCR2dn2D12D2S2kbS1h1k1c1r2mu2au4AUMU5MULIM4KSL14KSL22c'4MFB'S1h1k1c1r2mu2au4AUMU5MULIM3mfa4KSL2S1k1c1p2dnS3hAR1k1e1c2R12R2S1h1k1n1c1r3mfa1A2n'2H3S3hAR1h1k1n1c3C303HRI3ZTH1r2mu2au4AUMU3mfa3MCR3SKB3SFB4B6RB4FARI3RIH1A2n'2H12H2S1h1k1cSS1h1k1n1c1r2mu2au4AUMU2E12E24KSL14KSL23UKE2c'5AUMU'2Q72k02S12S24CSR'S1h2k'3EL'3EH'1A2n'2HA2HB2Y3S3hAR1h2SP3CBP2lo3CB03LOL3SPL2T14STK0S1h1k1c3C301r3mfa2k'3RH'1A2n'2HB5AUMU'2Q1S1h1k1n1c3C303B6a3B6e1r3mfa3SKB3SFB5SLOTH1A2n'2H3S3hAR1h1k1n1c3C303B6a3B6c1r3mfa1A2n'2H2S3hAR1h1k1n1c3C302T03B6a3B6e3ZTH1r3mfa3SKB3SFB5SLOTH1A2n'2H12H22H32H4S3hAR1h1k1n1c3C301r3mfa3SKB3SFB1A2n'2H4S1h1k1cS1h1k1n1c1r3mfa1A2n'2H8S3hAR1h1k1n1c3SB03HRI1r2mu2au3mfa3SFB4B6RB3RIH1A2n'2H1S3hAR1h1k1n1c3B6c1r3mfa3SFB1A2n'2H1S1h1k1n1c3C301r3mfa3SKB3SFB5SLOTH1A2n'2H4S3hAR1h1k1n1c3C302T01r3mfa5SLOTH1A2n'2H4S3hAR1h1k1n1c3C302T01r3mfa3SKB3SFB5SLOTH1A2n'2H12H22H4S1h1k1n1c1r3mfa1A2n'2H2S3hAR1h1k1n1c3C303HRI3ZTH1r2mu2au4AUMU3mfa3MCR3SKB3SFB4B6RB4FARI3RIH1A2n'2H12H2S1h1k1c1r2mu2au2c'2Q2S1h1k1c1r2mu2au3mfa4B6RBS1h1k1cS2k'3EL'3EH'1A2n'2HA2HB2Y4S3hARS3hAR1h3RI12c'5AUMU'2Q12k02S24CSR'2D1S3hAR1h1k1c3RI11r2mu2au4AUMU3CSR3URI2k02S22D1S1k1n1c2E34NFXkS1h1k1c1r3mfa2k'2F12F22F34NFX'4APf0S2k'3RZ'3XAB3UINS2k'S3hAR1h1k1n1c3C303SB03RZB3HHD2E12E62RL1H2H0S1h1k1c2c13Hc1S1h1k1c1r2mu2au2c'3Hc'2Q4S1h1k1cS1h1k1c1r3mfa3MFB4ROOM2c'5AUMU'2Q52k02S12S24CSR'S1k1c1r2mu2au4AUMU5MULIMS1h2T0S1k1c1p5CNT163MCRS1k1n3SKBS1h1k1c1r3mfa3SFBSS1h4Zpa32S4S1h1k1c3C301r2mu2au4AUMU3NF02c'3Hc'2NE4MFB'2Q8S1h1k1c1r2mu2au3mfaS1h4Zfs42kk2ii2I12I23SZ1S1h2S3SSSSS1h1k1c1r2mu2au5MULIM3mfa3MFBS1h1k1cS1h4Zfs4S1h1k1cS1h1k1c1r2mu2au2c'4MFB'2Q32Q4S1b2Y4S1k1c1r3mfa1f3nf'3js'4JSL42dn3HNFS1k1nS1h1k1c3C301r3NF01b2S12S22Q55AUMU'SS3hAR1h2lo3LOL4STK0S1k1c3C30S1k1c1pS1k1c1p2dn3DNBS1h1k1c3C301r2mu2au4AUMU2c'3Hc'2NES3hAR1k1c2E12E22E42E52E6S1k1c3CSR1a2HaS1k1c2E12E22E41a2HaS1h4Zfs12kk2ii2I12I23SZ14Zfs2S1h5Zctx3S1h1k1c1b2S22Q12Q45AUMU'S3hAR1h1k1n1c3B6c1r3mfa3SKB1A2n'2H1S1h1k1n1c3C301r3mfa3SKB3SFB5SLOTH1A2n'2H4S3hAR1h1k1n1c3C302T01r3mfa5SLOTH1A2n'2H3S3hAR1h1k1n1c3C302T01r3mfa3SKB3SFB5SLOTH1A2n'2H12H22H4S3hAR1h1k1n1c3SB03HRI1r2mu2au3mfa3SKB4B6RB3RIH1A2n'2H1S1h1k1n1c1r3mfa1A2n'2H7S1h1k1cS1h1b2Y2S1h1b2Y1S1k1c1r2mu2auS3hAR1h1k1n1c1r2mu2au3mfa1A2n'2H1S1h1k1n1c1r3mfa1A2n'2H5S3hAR1h2SP3CBP1C2lo3CB03CB13LOL3SPL4STK0S3hAR1h1k1n1c1j2HjS1h1k1n1c1r3mfa1A2n'2H2S3hAR1h1k1n1c3C303HRI3ZTH1r2mu2au4AUMU3mfa3MCR3SKB3SFB4B6RB4FARI3RIH1A2n'2H12H2S1k1n1c2U8S1h1k1c3C30S3hAR1h1k1n1c3HRI1r2mu2au3mfa4ROOM4FARI1A2n'2H1S1h1k1n1c1r3mfa3NF44ROOM2NB2E11A2n'2H62H7S1h1k1c1r2mu2au4FARI2c'3Hc'S1k1nS3hAR1h1k1n1c3C301r3mfa3SKB3SFB1A2n'2H3S1h1k1n1c3C301r3mfa3SKB3SFB5SLOTH1A2n'2H3S3hAR1h1k1n1c3B6c1r3mfa5SLOTH1A2n'2H2S3hAR1h1k1n1c3C302T03ZTH1r3mfa3SKB3SFB5SLOTH1A2n'2H12H22H32H4S1h1k1c3C301r3mfa2k'2XD1A2n'2HA2HB5AUMU'S1k1c3MCR2Dm3Dm'S1k1c3C30S1k1n1c2E12E22E34NFXk2k'2F12F22F32XD4NFX'S1h1k1c3C301b2BV5AUMU'S1h1k1n1c1r3mfa1A2n'2H3S3hAR1h1k1n1c3C303HRI3ZTH1r2mu2au4AUMU3mfa3MCR3SKB3SFB4B6RB4FARI3RIH1A2n'2H12H2S1k1c1p3MCRS3hAR1h1k1n1c3HRI1r2mu2au4AUMU3mfa2E12E22E43URI4B6RB3RIH4KSL21A2n'2H1S1h1k1n1c1r3mfa3NF44ROOM2NB2E12E22E41A2n'2H42H62H72H8S1h1k1cS1h1k1c1r3mfa3MFB4ROOM2c'5AUMU'2Q5S1k1c1p4PMAX3MCR2dn2D12D21HS1k1c1pS2c'3Hc'S2kbS3hAR1h1k2SP1n1c1r2au2mu3mfa3CSR1pS3hAR1h2lo3LOL2T14STK03CX1S1j2k0S1h1k1c1r3mfa3SFBS1k1n1c2E12E22E34NFXk2kb3XDb2F12F22F33NFbS1h1k1c1r2mu2au4AUMU5MULIM3mfa3MFB3CSR2k02S2S1h1k1cS1k1c1r2mu2au4AUMUS1k1c1p2dn2D13HdnS1k1c2c'2NES3hAR1h1k2SP3CBP1C3CB03CB13CHI1n1c4STKHS2c02kb2Ra2D12D22D32D42D52NFS1A2n'2H4S2SP3CBP1C3CB03CB1S1h1k1cSS3hAR1h1k2SP2lo3LOL1n1c3HRI3RI14STK01r2mu2au3mfa4FARI1A2n'2H2S1h2SP2lo3LOL4SPHI1A2n'2H3S1h1k2SP2lo1n1c3C301r3mfa3SKB3SFB5SLOTH1A2n'2H1S3hAR1h1k2SP2lo3LOL1n1c4STK01r3mfa1A2n'2H2S3hAR1h1k2SP2lo3LOL1n1c2T14STK01r3mfa1A2n'2H2S3hAR1h1k2SP2lo3LOL1n1c3B6d4STK01r3mfa1A2n'2H2S1h1k2SP2lo1n1c1r3mfa1A2n'2H1S1x2HxS1k1c1p3MCR2dn2D12D2S1k1c1p3MCR2D1S1h1k1n1c3RZB3HHD2E12E25SLOTH3Dhe4Dhe'3Db64Db6'3Duk1a2Ha1r3mfa3MFB4ROOM4B6RB4FARI3RIH4DfaaS3hAR1h1k1n1c1r2mu2au3mfa1A2n'2H1S1h1k1n1c1r3mfa1A2n'2H5S1h5Zctx15Zctx2S1h4Zfs32kk2ii2I12I23SZ1S1h1k1n1c3C301r3mfa3SKB3SFB5SLOTH1A2n'2H2S3hAR1h1k1n1c3C302T01r3mfa5SLOTH1A2n'2H12H2S3hAR1h1k1n1c3C302T01r3mfa3SKB3SFB5SLOTH1A2n'2H4S3hAR1h1k1n1c3C303ZTH1r3mfa3SKB3SFB1A2n'2H12H2S1h1k1cS1k1c1p2dn2D2S1k1c1p2dnS1h1a2kb2Ha2Xb2sh3EL'3EH'2Y2S1h1k1c1r3mfa3MFB4ROOM1a2Ha1XS1h1k1c1r3mfa3NF44ROOM3MCR3NF01a2Ha1XS1h1k1c3C301a2Ha1XS1k1c2dn2D2S1h2SP3CBP1C3CB03CB13CHIS1h4Zfs3S1h1k1cS1h3FS0S1h1k1n1c1j3HAB3UKE2k01XS1h4Zdt4S1h1k1c3C30S1h1k1c1r3mfa3MFB4ROOM2kb2c'3RL'3RH'5AUMU'2Q5S1h1k1c1r3mfa3MFB4ROOM4B6RB4FARI3RIH2kb2sh3EL'3EH'2Y2S1h1k1c1r3mfa2k'3RH'1A2n'2HB5AUMU'2Q12Q4SS1h1k1c3C30S1k1c1pS1h1k1n1c1r2au4KSL23UKES1h1b2Y3S1h1k1n1c1r3mfa1A2n'2H5S3hAR1h1k1n1c1r2mu2au3mfa1A2n'2H2S1k1c3MCR2Dm3Dm'S1k1c1rS2k'3RZ'S1h1k1c2c13Hc1S1k1c1r2mu2auS1h1k1c1r3mfa3NF44CARB3MFXSS1h3CBP1C2lo3CB13CHIS2sh2SZ2Y4S1k1c1r2dnS1h1k1n1c3C301r3mfa3SKB3SFB5SLOTH1A2n'2H2S3hAR1h1k1n1c3C302T01r3mfa5SLOTH1A2n'2H12H2S3hAR1h1k1n1c3C302T01r3mfa3SKB3SFB5SLOTH1A2n'2H3S3hAR1h1k1n1c3C303ZTH1r3mfa3SKB3SFB1A2n'2H12H2S1k1c3MCR2Dm3Dm'S1k1n1cS3hAR1h1k2SP1n1c1r2mu2au3mfa1p4PMAX3MCRS1k1n1c3CSR2U13RZRS1k1c3C30S1h1k1cS1h1k1c1r2mu2au4B6RB4FARI2c'3Hc'S1h1k1cS3hAR1h1k2SP1n1c1r2mu2au3mfa1pS1h1k1cS1k1n1cSS". (* [comment removed for export] *)
  #[using="IMG ALWF ASB"] Theorem rec_prim_step : ltac2:(CDefT.buildp (gd_tbl_AW_RecStep ()) "PQ,P,$18.SpPra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Ph,$1=.PLF,(3;.(2;.$11.$11.))PQS,(3;.(2;.$11.$11.))Pbc,$2<.Pi,$1<.Pk,$3<.PSP,$11.PCBP,$11.PC,$11.Plo,$11.PF,(3=.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))Pmo,$1:.ZL,$0.(33.R>.)ZT,$11.(9.R1.)P,(27.VhAR,R10.)P,(?.(3>.R11.)$3?.)P,(10.$1;.(40.R12.)$41.)P,(42.$3<.R>.(43.R13.))P,(10.$11.(44.R?.)$45.)P,(10.$1;.(46.R10.)$41.)P,(10.(2.(1.&40.))(47.(1.&40.)(48.R13.)R12.)(2:.(1.&40.)(22.&40.(49.R11.))))P,(28.VhAR,R17.R16.R;.)P,(29.VhAR,R18.R10.(2:.(2;.$2<.$1<.)(2=.$2<.$1<.R15.R14.))R<.)P,(4:.$26.R=.R12.(4;.$4<.(4=.(22.&40.(13.R:.+=0.)))(4>.$4<.)))P,(?.R14.R13.)P,(?.(13.R14.+8.)R13.)P,(?.(13.R14.+20.)(4?.R>.))P,(3:.$26.R11.R14.R17.)P,(?.(50.R10.)R15.)P,(?.R16.(51.R19.+2<0.))P,(10.$11.(12.R1:.+10.)=)P,(39.$26.R15.)P,(10.(1.&40.)R3<.(22.&40.$52.))P,(2?.VhAR,VAL,VFF,R23.R16.)P,(30.R18.R17.)P,Pc',$18.P,(53.R42.R20.R41.R40.R3<.R3;.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R1<.R1;.R26.R21.R25.R23.R22.R1>.R1=.R24.R1:.R1.)(54.$26.R44.R2.)(54.$26.R43.(1?.(20.(21.R42.(22.&40.R20.)R41.R40.R3?.R3>.R3=.R3<.R3;.(22.&40.R1?.)(22.&40.(49.R21.))R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)R1<.(22.&40.$55.)R1;.(24.(1.&40.))R1:.(25.$26.))R19.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 h LF QS bc i k SP CBP C lo F fc m mo L T
      WF HV CI Hk STQ PRIM NTH HMQ RQ CBC CB0 CB1 CHI ST LOL SPL SPA MI TP HK HJ HC.
    subst T L.
    dpose WF as (WL' & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG). dpose WL' as (WL & WL24 & WLD).
    pose proof (WFK_of_WFR h WF HV) as W0.
    (* [comment removed for export] *)
    dpose WK as (WKF & NDK & WKSEC).
    pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (KN & KST & KP & KX). rewrite PRIM in KX. ddestruct KX as (KCLS & C30 & j & Hj & EAB).
    set (c := ck_cls k) in *. set (n := ck_n k) in *.
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
    pose proof (class_size_range c ltac:(clear -C30; lia)) as CSR.
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
    pose proof (max_count_range c ltac:(clear -C30; lia)) as MCR.
    (* [comment removed for export] *)
    assert (NB : 0 <= nfix n <= 2^28 /\ 8 * ((nfix n + 7) / 8) + rz_size (nfix n) <= class_size c /\ rz_size (nfix n) = rz_size n /\ 1 <= nfix n).
    { pose proof (rz_size_nfix n ltac:(clear -KN; lia)) as RZN. rewrite RZN.
      assert (NN : needed (nfix n) = needed n).
      { unfold needed. rewrite RZN. f_equal. unfold rounded, nfix. f_equal. clear; lia. }
      assert (FP : from_primary n = true) by (rewrite <- KP; exact PRIM).
      assert (FPN : from_primary (nfix n) = true) by (unfold from_primary in FP |- *; rewrite NN; exact FP).
      pose proof (user_end_prim8 (nfix n) ltac:(unfold nfix; lia) FPN) as U8. rewrite RZN in U8. unfold pclass in U8. rewrite NN in U8. fold (pclass n) in U8. rewrite <- KCLS in U8.
      pose proof (user_end_prim n ltac:(clear -KN; lia) FP) as [U1 _]. rewrite <- KCLS in U1. fold c in U8, U1.
      pose proof (rz_size_bound' n) as RZR. unfold nfix in *. clear - U8 U1 CSR KN RZR. repeat split; lia. }
    ddestruct NB as (NB & RZB & RZN & N1).
    pose proof (rz_size_bound' n) as RZR.
    assert (HHD : ck_hdr k = ck_ab k + rz_size (nfix n) - 16) by (rewrite RZN; unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize; fold n; lia).
    assert (HAB : ck_ab k = l_sb (h_L h) + c * 2^32 + j * class_size c) by (rewrite EAB; unfold chunk_at, region_beg, kRegionSize; reflexivity).
    assert (KMU : (j + 1) * class_size c <= mu).
    { unfold carved in Hj. fold r au in Hj. rewrite AUCS in Hj. fold au in AUMU.
      replace (class_size c * (au / class_size c) / class_size c) with (au / class_size c) in Hj by (rewrite Z.mul_comm, Z.div_mul by lia; rewrite AUCS, Z.mul_comm, Z.div_mul by lia; reflexivity) || idtac.
      pose proof (Z.mul_div_le au (class_size c) ltac:(clear -CSR; lia)). clear - Hj AUMU AUCS H CSR. nia. }
    (* [comment removed for export] *)
    ddestruct HMQ as (G0 & G1 & G2 & G3 & G4 & G5 & G7 & G8 & G9 & GE). pose proof G2 as THR.
    ddestruct G2 as (UNW & (ds & PCLS) & (j0 & j1 & J27) & (xs & bs & TST & LXS & BST & LBS)).
    dpose (PCLS c ltac:(clear -C30; lia)) as (PCL & CKS & LCK & FST & PMC'). fold p in PCL, CKS, FST.
    rewrite PMAX, PCSZ in PCL.
    pose proof (G5 c ltac:(clear -C30; lia)) as RG. unfold hm_region in RG. cbn zeta in RG. fold r in RG.
    ddestruct RG as (RMX & RNF & RMFA & RAU & R40 & RMU & R56 & R68 & (stw & R72) & (s80 & s88 & RST) & RFA & (js & RJS & JSL) & WRU & SHT & SHF1).
    set (exb := Z_to_bv 8 (if a_exh (h_acct h) c then 1 else 0)) in *.   (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) G4 k Hk) as (HDR & MAG & QUS). rewrite STQ in QUS. cbn in QUS. ddestruct QUS as (fcw & UC & UW).
    ddestruct HDR as (b1 & id & HDC & B13 & B1R & IDR). rewrite STQ in HDC.
    change [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nfix (ck_n k))); C4 (Z_to_bv 64 id); C4 (Z_to_bv 64 0)]
      with (hdr_w0 b1 3 ++ hdr_rest (nfix n) id) in HDC.
    apply rw_cells_app in HDC as [HW0 HW1]. cbn [cells_size csize Nat.add hdr_w0] in HW1. change (Z.of_nat 4) with 4 in HW1.
    destruct G1 as [RO RW]. ddestruct (hm_ro_free (h_L h) m RO) as (RPS & (can & dd & madv & RSM) & LST).
    (* [comment removed for export] *)
    dpose G0 as (_ & WHS & _).
    ddestruct (chunk_ext' h k WL WR WK Hk) as (_ & E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold ext_lo, ext_hi, ck_end in E1, E3, E4, E5, E6. rewrite PRIM in E1, E3, E4, E5, E6. fold c in E3, E4, E6. fold n in E3.
    (* [comment removed for export] *)
    destruct E7 as [(_ & _ & RL & _)|(NP & _)]; [| rewrite PRIM in NP; discriminate NP].
    unfold ext_lo in RL. rewrite PRIM in RL. unfold region_beg, kRegionSize in RL. fold c in RL.
    assert (SKB : 0x2008fff7000 <= 0x7fff8000 + (ck_hdr k + 16) / 8 /\ 0x7fff8000 + (ck_hdr k + 16) / 8 + (nfix n + 7) / 8 <= 0x10007fff0000).
    { pose proof (Z.div_mod (ck_hdr k + 16) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (ck_hdr k + 16) 8 ltac:(clear; lia)).
      pose proof (Z.div_mod (nfix n + 7) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (nfix n + 7) 8 ltac:(clear; lia)).
      pose proof aceil_bounds as ACB.
      unfold kHighMemBeg in *. clear - H H0 H1 H2 E1 E2 E6 HHD RZB RZR RZN NB CSR RL SB0 C30 ACB. lia. }
    destruct (wr_at_high_CB m (0x7fff8000 + (ck_hdr k + 16) / 8) ((nfix n + 7) / 8)
                ltac:(replace (0x7fff8000 + (ck_hdr k + 16) / 8) with (0x2008fff7000 + (0x7fff8000 + (ck_hdr k + 16) / 8 - 0x2008fff7000)) by (clear; lia);
                      eapply wr_at_sub; [exact WHS| clear -SKB; lia| clear -NB; lia| clear -SKB; lia])
                ltac:(clear -SKB; lia) ltac:(clear -NB; lia)) as [junk SH].
    assert (SFB : 0x2008fff7000 <= 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 /\ 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 + 32768 <= 0x10007fff0000).
    { pose proof (Z.div_mod (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) 8 ltac:(clear; lia)).
      unfold kFreeArrayMapSize, kFreeArraySize in *.
      clear - H H0 SB0 HRI RI1 C30 ROOM MFB. lia. }
    destruct (wr_at_high_CB m (0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8) 32768
                ltac:(replace (0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8) with (0x2008fff7000 + (0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 - 0x2008fff7000)) by (clear; lia);
                      eapply wr_at_sub; [exact WHS| clear -SFB; lia| clear; lia| clear -SFB; lia])
                ltac:(clear -SFB; lia) ltac:(clear; lia)) as [shF SHF].
    change (Z.to_nat 32768) with (Z.to_nat 32768) in SHF.
    (* [comment removed for export] *)
    assert (GC31 : 1 <= c <= 31) by (clear -C30; lia).
    eapply (rec_prim_cfgS AL IMG ALWF (CSp AL FF h c) (fam_CSOK AL FF h c) (fam_mono AL FF h c) ASB (l_T (h_L h)) (l_ctx (h_L h)) (l_sb (h_L h)) (ri_base (h_L h)) c
              (conj SB0 (conj SBAL (conj HRI RI1))) C30 (conj T0 (conj T1 TAL)) (conj CX0 CX1) GSEP
              (fam_T AL FF h c W0 GC31 ROOM) ltac:(intros u f; rewrite <- CXL; exact (fam_ctx AL FF h c W0 GC31 ROOM u f)) (fam_ri AL FF h c W0 GC31 ROOM)
              (Kp AL FF h c) (fam_KL AL FF h c) mfa
              (fam_ledger AL FF h c W0 GC31 ROOM) (fam_commit AL FF h c W0 GC31 ROOM) (fam_fresh AL FF h c W0 GC31 ROOM)
              (fam_GMFA h c W0 GC31 ROOM) (fam_faz AL FF h c W0 GC31 ROOM) (fam_room AL FF h c W0 GC31 ROOM) (fam_scar AL FF h c W0 GC31 ROOM) (fam_fa AL FF h c W0 GC31 ROOM) Q)
      with (k := j) (n := nfix n) (ctx := id) (b1 := b1) (count := pc_count p) (csz := class_size c) (nf := r_nfreed r) (mu := mu) (lo := lo)
           (cks := ds c) (js := js) (xs := xs) (shF := shF) (junk := junk) (st80 := s80) (st88 := s88).
    all: lazymatch goal with
         | |- aevtS _ _ _ => idtac
         | |- forall c', _ -> aevtS _ _ _ => idtac
         | |- 16 < _ -> _ => rewrite RZN; exact MAG
         | |- forall u f, crange _ (ck_ab _) _ => intros u f; eapply crange_sub; [exact (fam_user AL FF h c W0 GC31 ROOM u f c GC31)| | ]; fold r mu;
                                                  rewrite HAB; unfold region_beg, kRegionSize; [clear -Hj CSR; nia| clear -KMU; nia]
         | |- forall u f, crange _ _ 8 => intros u f; apply (fam_stack AL FF h c W0 GC31 ROOM); [clear -LOL SPL CB0; lia| clear -CB1 CHI; lia]
         | |- _ + 4096 <= _ \/ _ + 8 <= _ => left; clear -T1 STK0 LOL SPL CB0; lia
         | |- 0 <= pc_count _ <= _ => unfold pc_count in *; rewrite PMAX in CNT16; clear -CNT16 MCR; lia
         | |- 0 <= class_size _ < _ => clear -CSR; lia
         | |- 0 <= r_nfreed _ => unfold r_nfreed; clear; lia
         | |- ACEIL <= _ => clear -STK0 LOL; lia
         | |- _ <= _ \/ _ + 4096 <= _ => right; clear -T1 STK0 LOL; lia
         | |- _ <= _ \/ _ + 65536 <= _ => right; clear -CX1 STK0 LOL; lia
         | |- crange _ _ (_ + 8 - _) => apply (fam_stack AL FF h c W0 GC31 ROOM); [exact LOL| clear -CB1 CHI; lia]
         | |- _ => first [ sassumption | cassumption (* [comment removed for export] *) | exact KMU | exact B1R | exact HAB | exact NB | exact RZB | exact HHD | exact HW0 | exact HW1 | exact SH | exact SHF | exact CBC | exact CB0
                        | exact LCK | exact PCL | exact CKS | exact TST | exact LXS | exact NFB | exact JSL | exact RMX | exact RNF | exact RMFA | exact RMU | exact RST
                        | exact RJS | exact RPS | exact ST | exact SPL | exact SPA | exact MI | exact TP | exact HK | exact HJ
                        | unfold kUserLimit in MULIM; exact MULIM
                        | clear - Hj SB0 HRI RI1 C30 T0 T1 CX0 CX1 STK0 STKH LOL SPL CB0 CB1 CHI NB; lia
                        | match goal with |- ?G => idtac "RS-LEFTOVER" G end ]
         end.
    (* [comment removed for export] *)
    intros c4 P4. unfold rp_post in P4.
    ddestruct P4 as (ms4 & mo4 & f & count' & nf' & cks' & js' & xs' & j1' & j2' & st80' & y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m4
                    & -> & -> & HK4 & HJ4 & HF2 & MU & WM & MI4 & ST4 & RPS4 & PCL4 & CKS4 & LCK4 & TST4 & LXS4 & RMX4 & RNF4 & RMFA4 & RMU4 & RST4 & FAJ4 & JSL4
                    & SHN & SHO & ZLT & (dr & dn & DRC & HC4 & HNF & HCKS & DRT & DRF & LJS)).
    (* [comment removed for export] *)
    pose proof RQ as RQ0. unfold RIq in RQ0. cbn zeta in RQ0.
    ddestruct RQ0 as (_ & _ & _ & _ & _ & _ & (_ & BWF & b0 & all & E0 & EA & EE & EL & IL & RNG)).
    assert (NTHZ : nth_error all i = Some (ck_hdr k)).
    { rewrite EE, nth_error_map in NTH. destruct (nth_error all i) as [e|] eqn:NA; [| discriminate NTH]. cbn in NTH.
      assert (NTH' : Z_to_bv 64 e = Z_to_bv 64 (ck_hdr k)) by (clear -NTH; congruence). clear NTH.
      f_equal. pose proof (proj1 (Forall_forall _ _) RNG e (nth_error_In _ _ NA)) as [R1 R2].
      apply (f_equal bv_unsigned) in NTH'. rewrite !Z_to_bv_small in NTH' by (unfold bv_modulus; change (2 ^ Z.of_N 64) with 18446744073709551616; unfold kHighMemBeg in *; clear -R1 R2 E1 E2 E4 E5 E6; lia). exact NTH'. }
    assert (HE : b_elems b0 = ck_hdr k :: skipn (S i) all) by (rewrite EL; exact (skipn_cons_nth all i _ NTHZ)).
    assert (DR : if dr then pc_count p = max_count c /\ dn = Z.to_nat (max_count c / 2) else pc_count p < max_count c).
    { destruct dr; [destruct DRC as [D1 D2]; split; [exact D1| clear -D2; lia]| destruct DRC as (D1 & _); exact D1]. }
    assert (UFZ : unit_if f = funit f) by (destruct f as [[|]|]; reflexivity).
    assert (NF4' : dr = true -> 4 * (r_nfreed r + Z.of_nat dn) <= r_mapped_fa r + funit f).
    { intros ->. rewrite <- UFZ. fold mfa. clear - JSL4 HNF. lia. }
    assert (FX : f = Some true -> dr = true /\ r_mapped_fa r < 4 * (r_nfreed r + Z.of_nat dn)).
    { intros Ef. destruct dr; [| ddestruct DRC as (_ & D2 & _); rewrite Ef in D2; discriminate D2]. destruct DRC as [D1 D2].
      split; [reflexivity|]. fold mfa. rewrite D2. exact (ZLT Ef). }
    assert (HGU : forall k', In k' (h_chunks h) -> k' <> k -> ck_hdr k' = ck_hdr k -> False).
    { intros k' Hk' NE E. apply NE. exact (hdr_unique h k' k WL WR WK GEO Hk' Hk E). }
    set (h' := h_recp h k dr dn f).
    pose proof (WFR_recp h k dr dn f b0 (tl (q_batches (h_tq h))) (skipn (S i) all) WF CI Hk PRIM E0 HE DR HF2 NF4' FX HGU) as WF'.
    (* [comment removed for export] *)
    assert (NF0 : 0 <= r_nfreed r) by (unfold r_nfreed; clear; lia).
    ddestruct (user_in_hull h c (ck_ab k) WL WR ltac:(clear -C30; lia) ltac:(fold r mu; clear -E1 E4 KMU HAB Hj CSR AUMU; unfold region_beg, kRegionSize; nia)) as (HB1 & HB2 & HB3).
    assert (SLOTH : l_b6 (h_L h) <= ck_ab k /\ ck_ab k + class_size c <= l_b6 (h_L h) + 0x2000011000).
    { fold r mu au in AUMU. unfold kUserLimit in MULIM. clear - HB1 HAB KMU Hj CSR B6a B6e MULIM AUMU C30. unfold ri_base, space_end, kSpaceSize in B6e. nia. }
    set (W := [(lo, SP); (ck_ab k, ck_ab k + 8); (ck_hdr k, ck_hdr k + 4); (0x7fff8000 + (ck_hdr k + 16) / 8, 0x7fff8000 + (ck_hdr k + 16) / 8 + (nfix n + 7) / 8);
               (l_T (h_L h) + 208 + 80 * c, l_T (h_L h) + 208 + 80 * c + 4); (l_T (h_L h) + 208 + 80 * c + 16, l_T (h_L h) + 208 + 80 * c + 80);
               (l_T (h_L h) + 2784, l_T (h_L h) + 2792); (l_T (h_L h) + 2840, l_T (h_L h) + 2856); (l_T (h_L h) + 2872, l_T (h_L h) + 2888);
               (ri_base (h_L h) + 128 * c, ri_base (h_L h) + 128 * c + 8); (ri_base (h_L h) + 128 * c + 16, ri_base (h_L h) + 128 * c + 32);
               (ri_base (h_L h) + 128 * c + 80, ri_base (h_L h) + 128 * c + 88);
               (l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + 4 * r_nfreed r, l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + 4 * r_nfreed r + 4 * (max_count c / 2));
               (l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + mfa, l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + mfa + 2 ^ 18);
               (2147450880 + (l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + mfa) / 8, 2147450880 + (l_sb (h_L h) + c * 2 ^ 32 + 3758096384 + mfa) / 8 + 32768)]) in MU.
    assert (DJz : forall A n', (A + n' <= lo \/ SP <= A) ->
                  (A + n' <= l_T (h_L h) + 208 + 80 * c \/ l_T (h_L h) + 208 + 80 * c + 80 <= A) -> (A + n' <= l_T (h_L h) + 2784 \/ l_T (h_L h) + 2904 <= A) ->
                  (A + n' <= ck_ab k \/ ck_ab k + class_size c <= A) -> (A + n' <= ri_base (h_L h) + 128 * c \/ ri_base (h_L h) + 128 * c + 88 <= A) ->
                  (A + n' <= l_sb (h_L h) + c * 2^32 + 3758096384 + 4 * r_nfreed r \/ l_sb (h_L h) + c * 2^32 + 3758096384 + 2^29 <= A) ->
                  (A + n' <= 0x7fff8000 + (ck_hdr k + 16) / 8 \/ 0x7fff8000 + (ck_hdr k + 16) / 8 + (nfix n + 7) / 8 <= A) ->
                  (A + n' <= 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 \/ 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 + 32768 <= A) ->
                  disjoint_from W A n').
    { intros A n' H1 H2 H3 H4 H5 H6 H7 H8. subst W. cbn [disjoint_from]. fold mfa in NF4, ROOM. unfold kFreeArrayMapSize, kFreeArraySize in ROOM.
      clear - H1 H2 H3 H4 H5 H6 H7 H8 E1 E2 E4 NF4 ROOM NFB MCR NB. repeat split; lia. }
    assert (DJfar : forall A n', (A + n' <= lo \/ SP <= A) -> (A + n' <= l_T (h_L h) \/ l_T (h_L h) + 4096 <= A) ->
                  (A + n' <= l_b6 (h_L h) \/ l_b6 (h_L h) + 0x2000011000 <= A) -> (A + n' <= 0x7fff7000 \/ 0x10007fff8000 <= A) -> disjoint_from W A n').
    { intros A n' H1 H2 H3 H4. apply DJz; unfold ri_base, space_end, kSpaceSize in *; clear - H1 H2 H3 H4 SLOTH B6a B6e C30 SKB SFB NF0; lia. }
    assert (DJT : forall A n', l_T (h_L h) <= A -> A + n' <= l_T (h_L h) + 4096 ->
                  (A + n' <= l_T (h_L h) + 208 + 80 * c \/ l_T (h_L h) + 208 + 80 * c + 80 <= A) -> (A + n' <= l_T (h_L h) + 2784 \/ l_T (h_L h) + 2904 <= A) ->
                  disjoint_from W A n').
    { intros A n' H1 H2 H3 H4. apply DJz; unfold ri_base, space_end, kSpaceSize in *; clear - H1 H2 H3 H4 ZTH SLOTH B6a B6e C30 SKB SFB T0 T1 STK0 LOL NF0; lia. }
    assert (DJhull : forall A n', l_b6 (h_L h) <= A -> A + n' <= l_b6 (h_L h) + 0x2000011000 ->
                  (A + n' <= ck_ab k \/ ck_ab k + class_size c <= A) -> (A + n' <= ri_base (h_L h) + 128 * c \/ ri_base (h_L h) + 128 * c + 88 <= A) ->
                  (A + n' <= l_sb (h_L h) + c * 2^32 + 3758096384 + 4 * r_nfreed r \/ l_sb (h_L h) + c * 2^32 + 3758096384 + 2^29 <= A) ->
                  disjoint_from W A n').
    { intros A n' H1 H2 H3 H4 H5. apply DJz; unfold ri_base, space_end, kSpaceSize, kHighMemBeg in *; clear - H1 H2 H3 H4 H5 ZTH B6c B6d SKB SFB STK0 LOL NF0 C30; lia. }
    assert (DJband : forall A n', 0x7fff7000 <= A -> A + n' <= 0x10007fff8000 ->
                  (A + n' <= 0x7fff8000 + (ck_hdr k + 16) / 8 \/ 0x7fff8000 + (ck_hdr k + 16) / 8 + (nfix n + 7) / 8 <= A) ->
                  (A + n' <= 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 \/ 0x7fff8000 + (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) / 8 + 32768 <= A) ->
                  disjoint_from W A n').
    { intros A n' H1 H2 H3 H4. apply DJz; unfold ri_base, space_end, kSpaceSize, kHighMemBeg in *; clear - H1 H2 H3 H4 SLOTH B6a B6c T0 STK0 LOL NF0 C30; lia. }
    assert (KOM : forall A n', disjoint_from W A n' -> kept m m4 A n') by (intros A n' D; exact (kept_of_munch W m m4 A n' MU D)).
    (* [comment removed for export] *)
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
    assert (SPHI : SP <= l_stk_hi (h_L h)) by (clear -CB0 CB1 CHI; lia).
    (* [comment removed for export] *)
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
    assert (PCL' : hm_pclass m4 (l_T (h_L h)) (h_cinit h) c (pc_push (if dr then pc_dropn p dn else p) (compact (h_L h) c (ck_ab k))) cks').
    { rewrite CI. unfold hm_pclass.
      assert (LENP : length (pc_chunks (if dr then pc_dropn p dn else p)) = Z.to_nat (pc_count p - Z.of_nat dn)).
      { unfold pc_count. destruct dr; cbn [pc_chunks pc_dropn];
          [destruct DR as [D1 D2]; unfold pc_count in D1; rewrite firstn_length_le by (clear -D1 D2 MCR; lia); clear -D1 D2 MCR; lia| ddestruct DRC as (_ & _ & ->); clear; lia]. }
      assert (CNTP : pc_count (pc_push (if dr then pc_dropn p dn else p) (compact (h_L h) c (ck_ab k))) = count').
      { unfold pc_count. cbn [pc_chunks pc_push]. rewrite length_app, LENP. cbn [length]. rewrite HC4. unfold pc_count in *.
        destruct dr; [destruct DR as [D1 D2]| ddestruct DRC as (_ & _ & ->); clear; lia].
        clear -D1 D2 CNT16 PMAX MCR.
        assert (Z.of_nat dn <= max_count c) by (subst dn; rewrite Z2Nat.id; [apply Z.div_le_upper_bound| apply Z.div_pos]; lia). lia. }
      split. { rewrite CNTP. replace (pc_max (pc_push (if dr then pc_dropn p dn else p) (compact (h_L h) c (ck_ab k)))) with (max_count c) by (destruct dr; cbn; symmetry; exact PMAX).
               replace (pc_csize (pc_push (if dr then pc_dropn p dn else p) (compact (h_L h) c (ck_ab k)))) with (class_size c) by (destruct dr; cbn; symmetry; exact PCSZ).
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
    { eapply (hm_thread_frame_but m m4 WM h c _ cks' THR GC31); [ | | | | | exact PCL' | intros; reflexivity | apply recp_L | apply recp_cinit | apply recp_cache].
      - eapply keep_rw; [exact UNW| apply KOM; cbn [cells_size csize Nat.add]; apply DJT; clear -C30; lia| exact WM].
      - intros c1 Hc1 NE1. apply KOM. apply DJT; clear -C30 Hc1 NE1; lia.
      - apply KOM. apply DJT; clear -C30; lia.
      - ddestruct G0 as (_ & _ & _ & WT & _). exact WT.
      - clear -T0; lia. }
    (* [comment removed for export] *)
    assert (G3' : hm_depot h' m4).
    { unfold hm_depot. replace (h_dep h') with (h_dep h) by (symmetry; apply recp_dep). apply (hm_depot_frame h m m4 G3 WM); [apply IAG; vm_compute; reflexivity| |].
      - intros b Hb. destruct (In_nth_error _ _ Hb) as [jb Hjb].
        pose proof (z_node_T h GEO jb b Hjb) as Y1. pose proof (z_node_hull h GEO jb b Hjb) as Y2. pose proof (z_node_stk h GEO jb b Hjb) as Y3. pose proof (z_node_band h GEO jb b Hjb) as Y4.
        unfold zapart in Y1, Y2, Y3, Y4. cbn [fst snd] in Y1, Y2, Y3, Y4. apply KOM. apply DJzone; [clear; lia| clear -Y1; lia| clear -Y2; lia| clear -Y3; lia| clear -Y4; lia].
      - intros b Hb. destruct (In_nth_error _ _ Hb) as [jb Hjb].
        pose proof (z_store_T h GEO jb b Hjb) as Y1. pose proof (z_store_hull h GEO jb b Hjb) as Y2. pose proof (z_store_stk h GEO jb b Hjb) as Y3. pose proof (z_store_band h GEO jb b Hjb) as Y4.
        unfold zapart in Y1, Y2, Y3, Y4. cbn [fst snd] in Y1, Y2, Y3, Y4. apply KOM. apply DJzone; [clear; lia| clear -Y1; lia| clear -Y2; lia| clear -Y3; lia| clear -Y4; lia]. }
    (* [comment removed for export] *)
    assert (UA8 : ck_user k mod 8 = 0) by (exact (proj2 (proj2 (chunk_geom' h k WL WR WK Hk)))).
    assert (FAA8 : (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) mod 8 = 0).
    { pose proof WL as (M16 & _). pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(clear; lia)) as D. rewrite M16, Z.add_0_r in D.
      pose proof (Z.div_mod mfa (2^18) ltac:(clear; lia)) as D2. pose proof MFAL as MFAL'. fold mfa in MFAL'. unfold kFreeArrayMapSize in MFAL'. rewrite MFAL', Z.add_0_r in D2.
      rewrite D, D2. replace (2 ^ 16 * (l_sb (h_L h) / 2 ^ 16) + c * 2 ^ 32 + 3758096384 + 2 ^ 18 * (mfa / 2 ^ 18))
        with (8 * (2^13 * (l_sb (h_L h) / 2 ^ 16) + c * 2^29 + 469762048 + 2^15 * (mfa / 2^18))) by (clear; lia). rewrite Z.mul_comm. apply Z_mod_mult. }
    (* [comment removed for export] *)
    unfold kFreeArrayMapSize, kFreeArraySize in ROOM. unfold kUserLimit in MULIM. unfold kFreeArraySize in MFB.
    ddestruct (user_vs_ri h c WL WR GC31) as (URI & B6RB & FARI & RIH). fold r in URI. fold mu in URI.
    unfold region_beg, kRegionSize in URI, B6RB. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize in FARI.
    destruct (slot_le h c j WR GC31 Hj) as [KSL1 KSL2]. rewrite <- EAB in KSL1, KSL2. fold r in KSL2. fold au in KSL2. unfold region_beg, kRegionSize in KSL1, KSL2.
    assert (XLK : ext_lo k = ck_ab k) by (unfold ext_lo; rewrite PRIM; reflexivity).
    assert (XHK : ext_hi k = ck_ab k + class_size c) by (unfold ext_hi, ck_end; rewrite PRIM; reflexivity).
    assert (NFXk : nfix n <= Z.max n 8) by (unfold nfix; clear; lia).
    assert (UKE : ck_user k + nfix n <= ck_ab k + class_size c) by (clear - E3 NFXk; lia).
    pose proof (carve_end8 h c WL WR GC31) as CE8. fold r in CE8. fold au in CE8. unfold region_beg, kRegionSize in CE8.
    (* [comment removed for export] *)
    assert (APF : forall kb, In kb (h_chunks h) ->
              ext_hi kb <= l_sb (h_L h) + c * 2^32 + 3758096384 + mfa \/ l_sb (h_L h) + c * 2^32 + 3758096384 + mfa + 2^18 <= ext_lo kb).
    { intros kb Hkb. destruct (ext_cases h kb WL WR WK Hkb) as [(c' & P' & EC' & C' & RL' & RH' & AUMU')|(i' & sh & P' & N' & EL' & EH')].
      - pose proof (user_vs_fa h c c' WR GC31 ltac:(clear -C'; lia)) as Q5. unfold fa_beg, kFreeArrayOffset, kFreeArraySize, region_beg, kRegionSize in Q5, RL', RH'.
        clear - Q5 RL' RH' AUMU' MFB ROOM; lia.
      - pose proof (z_sec_hull h GEO i' _ N') as Y2. unfold zapart in Y2. cbn [fst snd] in Y2. clear - Y2 EL' EH' B6RB FARI RIH MFB ROOM; lia. }
    (* [comment removed for export] *)
    assert (APK : forall kb, In kb (h_chunks h) -> ck_st kb = CHUNK_ALLOCATED -> ck_user kb + nfix (ck_n kb) <= ck_user k \/ ck_user k + nfix n <= ck_user kb).
    { intros kb Hkb STb.
      assert (NAb : ck_ab kb <> ck_ab k) by (intros E; pose proof (NoDup_map_inj ck_ab (h_chunks h) kb k NDK Hkb Hk E) as EK; rewrite EK, STQ in STb; cbv in STb; discriminate STb).
      pose proof (ext_disj' h kb k WL WR WK GEO Hkb Hk NAb) as XDb. rewrite XLK, XHK in XDb.
      ddestruct (chunk_ext' h kb WL WR WK Hkb) as (Nb & F1 & F2 & F3 & _). assert (NFb : nfix (ck_n kb) <= Z.max (ck_n kb) 8) by (unfold nfix; clear; lia).
      clear - XDb F1 F2 F3 NFb E1 E2 E3 NFXk. lia. }
    (* [comment removed for export] *)
    assert (DJri : forall A n', ri_base (h_L h) + 128 * c + 32 <= A -> A + n' <= ri_base (h_L h) + 128 * c + 80 -> disjoint_from W A n').
    { intros A n' H1 H2. subst W. cbn [disjoint_from].
      clear - H1 H2 RI1 STK0 LOL KSL1 KSL2 AUMU URI E1 E2 E4 SKB SFB ZTH HRI SB0 B6RB RIH FARI NF4 NF0 ROOM MCR C30. repeat split; lia. }
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
      apply KOM. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset. apply DJhull; clear - B6RB FARI RIH KSL1 KSL2 AUMU MULIM NF0 NF4 ROOM C30; lia. }
    assert (KWRU : wr_at asegs m4 (region_beg (h_L h) c) mu) by (eapply wr_at_transport; [exact WRU| exact WM]).
    assert (KSHT : rw_cells asegs m4 (shad (region_beg (h_L h) c + au)) [CB (Z.to_nat ((mu - au) / 8)) (fill 0xfa ((mu - au) / 8))]).
    { eapply keep_rw; [exact SHT| | exact WM]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; clear - AUMU; lia).
      pose proof (shad_disj_gen (l_sb (h_L h) + c * 2^32 + au) (mu - au) (ck_user k) (nfix n) CE8 UA8 (proj1 NB) ltac:(right; clear - UKE KSL2; lia)) as SD1.
      pose proof (shad_disj_gen (l_sb (h_L h) + c * 2^32 + au) (mu - au) (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) CE8 FAA8 ltac:(clear; lia) ltac:(left; clear - MULIM MFB; lia)) as SD2.
      change ((2 ^ 18 + 7) / 8) with 32768 in SD2. unfold AW_FreeG.shad in SD1, SD2. rewrite <- E2 in SD1. unfold shad, region_beg, kRegionSize.
      pose proof (Z.div_mod (l_sb (h_L h) + c * 2^32 + au) 8 ltac:(clear; lia)) as D1. rewrite CE8, Z.add_0_r in D1.
      pose proof (Z.div_mod (mu - au) 8 ltac:(clear; lia)) as D2. pose proof (Z.mod_pos_bound (mu - au) 8 ltac:(clear; lia)) as D3.
      apply KOM. apply DJband; [clear - D1 SB0 C30 AUMU; lia| clear - D1 D2 D3 AUMU URI RI1; lia| exact SD1 || (clear -SD1; lia)| exact SD2 || (clear -SD2; lia)]. }
    assert (KSHF : forall k0, 0 <= k0 < au / class_size c -> rw_cells asegs m4 (shad (chunk_at (h_L h) c k0)) [C1 (Z_to_bv 8 0xfa)]).
    { intros k0 Hk0. eapply keep_rw; [exact (SHF1 k0 Hk0)| | exact WM]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
      assert (Hk0' : 0 <= k0 < carved h c) by (unfold carved; fold r; fold au; exact Hk0).
      destruct (slot_le h c k0 WR GC31 Hk0') as [S1 S2]. fold r in S2. fold au in S2. unfold region_beg, kRegionSize in S1, S2.
      pose proof (chunk_at8 (h_L h) c k0 WL GC31) as A8.
      assert (APk : chunk_at (h_L h) c k0 + 8 <= ck_user k \/ ck_user k + nfix n <= chunk_at (h_L h) c k0).
      { assert (k0 <= j \/ j + 1 <= k0) as [LE|GT] by (clear; lia).
        - left. pose proof (Z.mul_le_mono_nonneg_r k0 j (class_size c) ltac:(clear -CSR; lia) LE) as X. unfold chunk_at, region_beg, kRegionSize.
          clear - X HAB E2 HHD RZR RZN. lia.
        - right. pose proof (Z.mul_le_mono_nonneg_r (j + 1) k0 (class_size c) ltac:(clear -CSR; lia) GT) as X. unfold chunk_at, region_beg, kRegionSize.
          clear - X HAB UKE. lia. }
      pose proof (shad_disj_gen (chunk_at (h_L h) c k0) 8 (ck_user k) (nfix n) A8 UA8 (proj1 NB) APk) as SD1.
      pose proof (shad_disj_gen (chunk_at (h_L h) c k0) 8 (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) A8 FAA8 ltac:(clear; lia) ltac:(left; clear - S2 AUMU MULIM MFB CSR; lia)) as SD2.
      change ((2 ^ 18 + 7) / 8) with 32768 in SD2. change (8 / 8) with 1 in SD1. change (8 / 8) with 1 in SD2. unfold AW_FreeG.shad in SD1, SD2. rewrite <- E2 in SD1. unfold shad.
      pose proof (Z.div_mod (chunk_at (h_L h) c k0) 8 ltac:(clear; lia)) as D1. rewrite A8, Z.add_0_r in D1.
      apply KOM. apply DJband; [clear - D1 S1 SB0 C30; lia| clear - D1 S2 AUMU URI RI1 CSR; lia| exact SD1 || (clear -SD1; lia)| exact SD2 || (clear -SD2; lia)]. }
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
      - (* [comment removed for export] *)
        destruct (DRT eq_refl) as [_ CPY]. destruct LENL as [LENL _].
        cbn [r_mapped_user r_alloc_user r_mapped_fa r_fa].
        assert (NFE : r_nfreed (RG mu au (mfa + funit f) (r_fa r ++ pc_lastn p dn)) = r_nfreed r + Z.of_nat dn).
        { unfold r_nfreed. cbn [r_fa]. rewrite length_app, LENL. clear; lia. }
        rewrite NFE, <- HNF, <- UFZ.
        split; [exact RMX4|]. split; [exact RNF4|]. split; [exact RMFA4|]. split; [exact K32|]. split; [exact K40|]. split; [exact RMU4|].
        split; [exact K56|]. split; [exact K68|]. split; [exists stw; exact K72|]. split; [dexists st80', s88; exact RST4|].
        split. { rewrite map_app. apply u32arr_app. split; [exact KFA|]. rewrite length_map. change (Z.of_nat (length (r_fa r))) with (r_nfreed r).
                 rewrite <- (TOPH eq_refl). exact CPY. }
        split. { exists js'. split; [exact FAJ4| exact JSL4]. }
        split; [exact KWRU|]. split; [exact KSHT|]. exact KSHF.
      - (* [comment removed for export] *)
        ddestruct DRC as (D1 & DF & DN). subst f. rewrite DN in HNF. cbn [Z.of_nat unit_if] in HNF, RMFA4, JSL4. rewrite Z.add_0_r in HNF, RMFA4, JSL4. subst nf'.
        split; [exact RMX4|]. split; [exact RNF4|]. split; [exact RMFA4|].
        split; [exact K32|]. split; [exact K40|]. split; [exact RMU4|]. split; [exact K56|]. split; [exact K68|]. split; [exists stw; exact K72|].
        split; [dexists st80', s88; exact RST4|]. split; [exact KFA|].
        split. { exists js'. split; [exact FAJ4| exact JSL4]. }
        split; [exact KWRU|]. split; [exact KSHT|]. exact KSHF. }
    (* [comment removed for export] *)
    assert (G4' : hm_chunks h' m4).
    { unfold hm_chunks. replace (h_chunks h') with (rm_ab (ck_ab k) (h_chunks h)) by (symmetry; apply recp_chunks). apply Forall_forall. intros k' Hk'. apply rm_ab_In in Hk' as [Hk' NA].
      ddestruct (chunk_geom' h k' WL WR WK Hk') as (RZ' & N0' & U8').
      apply (hm_chunk_frame m m4 WM k' (proj1 (Forall_forall _ _) G4 k' Hk') RZ' N0' U8').
      ddestruct (chunk_ext' h k' WL WR WK Hk') as (_ & F1 & F2 & F3 & F4 & F5 & F6 & FC).
      pose proof (ext_disj' h k' k WL WR WK GEO Hk' Hk NA) as XD. rewrite XLK, XHK in XD.
      assert (XAB : ext_lo k' <= ck_ab k') by (unfold ext_lo, ck_map_beg; destruct (ck_prim k'); clear; lia).
      assert (UIN : ck_ab k' + ck_rz k' = ck_user k') by reflexivity.
      assert (NFX' : 0 <= nfix (ck_n k') /\ nfix (ck_n k') <= Z.max (ck_n k') 8) by (unfold nfix; clear -N0'; lia).
      (* [comment removed for export] *)
      assert (KX : forall A n', 0 <= n' -> ext_lo k' <= A -> A + n' <= ext_hi k' -> kept m m4 A n').
      { intros A n' N0'' HA HB. apply KOM. destruct FC as [(P' & C' & RL' & RH' & _)|(P' & i' & N' & EL' & EH')].
        - pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear -C'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
          dpose (user_vs_ri h (ck_cls k') WL WR ltac:(clear -C'; lia)) as (Q1 & Q2 & Q3 & Q4).
          pose proof (user_vs_fa h c (ck_cls k') WR GC31 ltac:(clear -C'; lia)) as Q5.
          unfold fa_beg, kFreeArrayOffset, kFreeArraySize in Q3, Q5. unfold region_beg, kRegionSize in Q1, Q2, Q3, Q5, RL', RH'.
          apply DJhull; clear - HA HB N0'' Q1 Q2 Q3 Q4 Q5 AUMU' RL' RH' XD NF0 NF4 C30; lia.
        - pose proof (z_sec_T h GEO i' _ N') as Y1. pose proof (z_sec_hull h GEO i' _ N') as Y2. pose proof (z_sec_stk h GEO i' _ N') as Y3. pose proof (z_sec_band h GEO i' _ N') as Y4.
          unfold zapart in Y1, Y2, Y3, Y4. cbn [fst snd s_map_beg s_map_size] in Y1, Y2, Y3, Y4.
          apply DJzone; [exact N0''| clear -Y1 HA HB EL' EH'; lia| clear -Y2 HA HB EL' EH'; lia| clear -Y3 HA HB EL' EH'; lia| clear -Y4 HA HB EL' EH'; lia]. }
      unfold chunk_kept. split; [apply KX; [clear -RZ'; lia| exact XAB| clear - UIN F4; lia]|].
      split.
      - (* [comment removed for export] *)
        intros AK.
        pose proof (Z.div_mod (ck_user k') 8 ltac:(clear; lia)) as D1. rewrite U8', Z.add_0_r in D1.
        pose proof (Z.div_mod (nfix (ck_n k') + 7) 8 ltac:(clear; lia)) as D2. pose proof (Z.mod_pos_bound (nfix (ck_n k') + 7) 8 ltac:(clear; lia)) as D3.
        assert (APk : ck_user k' + nfix (ck_n k') <= ck_user k \/ ck_user k + nfix n <= ck_user k') by (clear - XD NFXk NFX' F1 F2 F3 E1 E2 E3; lia).
        pose proof (shad_disj (ck_user k') (nfix (ck_n k')) (ck_user k) (nfix n) U8' UA8 (proj1 NFX') (proj1 NB) APk) as SD1.
        pose proof (APF k' Hk') as APf0.
        assert (APf : ck_user k' + nfix (ck_n k') <= l_sb (h_L h) + c * 2^32 + 3758096384 + mfa \/ l_sb (h_L h) + c * 2^32 + 3758096384 + mfa + 2^18 <= ck_user k')
          by (clear - APf0 F1 F2 F3 NFX'; lia).
        pose proof (shad_disj (ck_user k') (nfix (ck_n k')) (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) U8' FAA8 (proj1 NFX') ltac:(clear; lia) APf) as SD2.
        change ((2 ^ 18 + 7) / 8) with 32768 in SD2. unfold AW_FreeG.shad in SD1, SD2. rewrite <- E2 in SD1. unfold shad.
        apply KOM. apply DJband; [clear - D1 F5 XAB UIN RZ'; unfold kHighMemBeg in F5; lia| clear - D1 D2 D3 F3 F6 NFX'; lia| exact SD1 || (clear -SD1; lia)| exact SD2 || (clear -SD2; lia)].
      - (* [comment removed for export] *)
        intros NAK. apply KX; [clear; lia| clear - XAB UIN RZ'; lia| clear - F3; lia]. }
    (* [comment removed for export] *)
    assert (G5' : hm_regions h' m4).
    { intros c' Hc'. unfold h'. rewrite (recp_L h k dr dn f), (recp_reg h k dr dn f c'), (recp_acct h k dr dn f). fold c.
      destruct (Z.eqb_spec c' c) as [->|NE].
      - rewrite ?Z.eqb_refl. cbn [andb]. exact G5c.
      - rewrite ?(proj2 (Z.eqb_neq c' c) NE). cbn [andb].
        pose proof (WR c' ltac:(unfold kNumClasses; clear -Hc'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & AUCS' & MUAL' & MULIM' & MUAU' & MFAL' & MFB' & NF4c & _).
        apply (hm_region_frame m m4 WM (h_L h) c' (h_reg h c') _ (G5 c' Hc') AUMU' NF4c).
        dpose (user_vs_ri h c' WL WR Hc') as (Q1 & Q2 & Q3 & Q4). pose proof (user_vs_fa h c c' WR GC31 Hc') as Q5. pose proof (user_vs_fa h c' c WR Hc' GC31) as Q6.
        pose proof (user_vs_user h c c' WR GC31 Hc' ltac:(clear -NE; lia)) as Q7. pose proof (fa_vs_fa (h_L h) c c' ltac:(clear -NE; lia)) as Q8.
        fold r in Q5, Q6, Q7. fold mu in Q5, Q6, Q7. fold au in Q5, Q6, Q7.   (* [comment removed for export] *)
        unfold fa_beg, kFreeArrayOffset, kFreeArraySize, region_beg, kRegionSize in Q1, Q2, Q3, Q5, Q6, Q7, Q8. unfold kUserLimit in MULIM'. unfold kFreeArraySize in MFB'.
        unfold region_kept. split; [| split; [| split]].
        + apply KOM. unfold ri_addr. apply DJhull; clear - Hc' NE Q1 Q2 Q4 B6RB URI RIH AUMU KSL1 KSL2 FARI C30; lia.
        + apply KOM. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset. apply DJhull; clear - Hc' NE Q2 Q3 Q4 Q6 Q8 MFB' KSL1 KSL2 AUMU MULIM C30 NF0; lia.
        + pose proof (carve_end8 h c' WL WR Hc') as A8. unfold region_beg, kRegionSize in A8. unfold region_beg, kRegionSize, shad.
          pose proof (Z.div_mod (l_sb (h_L h) + c' * 2^32 + r_alloc_user (h_reg h c')) 8 ltac:(clear; lia)) as D1. rewrite A8, Z.add_0_r in D1.
          pose proof (Z.div_mod (r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) 8 ltac:(clear; lia)) as D2.
          pose proof (Z.mod_pos_bound (r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) 8 ltac:(clear; lia)) as D3.
          pose proof (shad_disj_gen _ (r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) (ck_user k) (nfix n) A8 UA8 (proj1 NB)
                        ltac:(clear - Q7 KSL1 KSL2 UKE AUMU AUMU' E1 E2; lia)) as SD1.
          pose proof (shad_disj_gen _ (r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) A8 FAA8
                        ltac:(clear; lia) ltac:(clear - Q5 AUMU' MFB ROOM; lia)) as SD2.
          change ((2 ^ 18 + 7) / 8) with 32768 in SD2. unfold AW_FreeG.shad in SD1, SD2. rewrite <- E2 in SD1.
          apply KOM. apply DJband; [clear - D1 Q2 AUMU' SB0 Hc'; lia| clear - D1 D2 D3 Q1 AUMU' RI1; lia| exact SD1 || (clear -SD1; lia)| exact SD2 || (clear -SD2; lia)].
        + intros k0 Hk0. assert (Hk0' : 0 <= k0 < carved h c') by (unfold carved; exact Hk0).
          destruct (slot_le h c' k0 WR Hc' Hk0') as [S1 S2]. unfold region_beg, kRegionSize in S1, S2.
          pose proof (chunk_at8 (h_L h) c' k0 WL Hc') as A8. pose proof (class_size_range c' Hc') as CSR'.
          pose proof (shad_disj_gen (chunk_at (h_L h) c' k0) 8 (ck_user k) (nfix n) A8 UA8 (proj1 NB) ltac:(unfold chunk_at, region_beg, kRegionSize in *; clear - Q7 S1 S2 CSR' KSL1 KSL2 UKE AUMU AUMU' E1 E2; lia)) as SD1.
          pose proof (shad_disj_gen (chunk_at (h_L h) c' k0) 8 (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) (2^18) A8 FAA8 ltac:(clear; lia)
                        ltac:(unfold chunk_at, region_beg, kRegionSize in *; clear - Q5 S1 S2 CSR' AUMU' MFB ROOM; lia)) as SD2.
          change ((2 ^ 18 + 7) / 8) with 32768 in SD2. change (8 / 8) with 1 in SD1. change (8 / 8) with 1 in SD2. unfold AW_FreeG.shad in SD1, SD2. rewrite <- E2 in SD1. unfold shad.
          pose proof (Z.div_mod (chunk_at (h_L h) c' k0) 8 ltac:(clear; lia)) as D1. rewrite A8, Z.add_0_r in D1.
          apply KOM. apply DJband; [unfold chunk_at, region_beg, kRegionSize in *; clear - D1 S1 Q2 SB0 Hc'; lia| unfold chunk_at, region_beg, kRegionSize in *; clear - D1 S2 AUMU' Q1 RI1 CSR'; lia
                                  | exact SD1 || (clear -SD1; lia)| exact SD2 || (clear -SD2; lia)]. }
    (* [comment removed for export] *)
    assert (G7' : hm_sec h' m4).
    { unfold hm_sec. unfold h'. rewrite (recp_sec h k dr dn f), (recp_L h k dr dn f), (recp_pa h k dr dn f). change (hm_sec h m4).
      dpose WS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
      apply (hm_sec_frame m m4 WM h G7 WS); [apply IAG; vm_compute; reflexivity| |].
      - apply KOM. rewrite S5. apply DJzone; [clear -S3; lia| clear -Zpa1 S4; lia| clear -Zpa2 S4; lia| clear -Zpa3 S4; lia| clear -Zpa4 S4; lia].
      - intros sh Hsh. destruct (In_nth_error _ _ Hsh) as [i' N']. apply KOM.
        pose proof (proj1 (Forall_forall _ _) S8 sh Hsh) as (_ & SZ & _).
        pose proof (z_sec_T h GEO i' _ N') as Y1. pose proof (z_sec_hull h GEO i' _ N') as Y2. pose proof (z_sec_stk h GEO i' _ N') as Y3. pose proof (z_sec_band h GEO i' _ N') as Y4.
        unfold zapart in Y1, Y2, Y3, Y4. cbn [fst snd] in Y1, Y2, Y3, Y4.
        apply DJzone; [clear; lia| clear -Y1 SZ; lia| clear -Y2 SZ; lia| clear -Y3 SZ; lia| clear -Y4 SZ; lia]. }
    assert (G8' : hm_fake h' LF m4).
    { unfold hm_fake. unfold h'. rewrite (recp_L h k dr dn f).
      dpose WL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS0 & FS1 & _).
      apply (fake_rep_frame m m4 WM (l_fs (h_L h)) LF G8); [unfold lowhigh, kHighMemBeg in FS0; clear -FS0; lia| |].
      - apply KOM. unfold kFakeBytes in Zfs1, Zfs2, Zfs3, Zfs4. apply DJzone; [clear; lia| clear -Zfs1; lia| clear -Zfs2; lia| clear -Zfs3; lia| clear -Zfs4; lia].
      - intros FB nB HFB. pose proof G8 as G8u. unfold hm_fake in G8u. ddestruct G8u as (_ & _ & _ & LFW & _). destruct (LFW _ HFB) as (kk & ii & Hkk & Hii & EFB).
        pose proof (fsk_frame_inside (l_fs (h_L h)) kk ii Hkk Hii) as [I1 I2]. pose proof (fsk_sizes kk Hkk) as (SZ1 & _).
        assert (EF1 : FB = fsk_frame (l_fs (h_L h)) kk ii) by (clear -EFB; congruence). assert (EF2 : nB = fsk_bytes kk) by (clear -EFB; congruence).
        rewrite EF1, EF2. apply KOM. unfold kFakeBytes in Zfs1, Zfs2, Zfs3, Zfs4, I2.
        apply DJzone; [clear; lia| clear -Zfs1 I1 I2 SZ1; lia| clear -Zfs2 I1 I2 SZ1; lia| clear -Zfs3 I1 I2 SZ1; lia| clear -Zfs4 I1 I2 SZ1; lia]. }
    assert (G9' : hm_ia h' m4).
    { unfold hm_ia. unfold h'. rewrite (recp_ia h k dr dn f). change (hm_ia h m4). apply (hm_ia_frame m m4 WM h G9). apply IAG. vm_compute. reflexivity. }
    assert (GE' : hm_emb h' m4).   (* [comment removed for export] *)
    { apply (hm_emb_frame_i m m4 WM h h' GE); [unfold h'; rewrite (recp_acct h k dr dn f); reflexivity| unfold h'; rewrite (recp_acct h k dr dn f); reflexivity| apply IAG; vm_compute; reflexivity]. }
    (* [comment removed for export] *)
    assert (KB : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> kept m m4 (b_addr b) 8192).
    { intros b Hb. apply KOM. ddestruct (batch_slot h b WF Hb) as (ib & Hib & EBb). pose proof (batch_vs_chunk h k b WF Hk PRIM Hb) as BV. fold c in BV.
      destruct (slot_le h kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2]. rewrite <- EBb in S1, S2.
      dpose (user_vs_ri h kBatchClass WL WR ltac:(unfold kBatchClass; clear; lia)) as (Q1 & Q2 & Q3 & Q4).
      pose proof (user_vs_fa h c kBatchClass WR GC31 ltac:(unfold kBatchClass; clear; lia)) as Q5.
      pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
      unfold kBatchClass in S1, S2, Q1, Q2, Q3, Q4, Q5, AUMU'. change (class_size 24) with 8192 in S2.
      unfold fa_beg, kFreeArrayOffset, kFreeArraySize, region_beg, kRegionSize in Q1, Q2, Q3, Q5, S1, S2.
      apply DJhull; clear - S1 S2 Q1 Q2 Q3 Q4 Q5 AUMU' BV NF0 C30; lia. }
    assert (RQ' : RIq h' C (Some (bc, S i)) m4).
    { apply (RIq_pop h h' C bc i m4).
      - apply (RIq_frame m m4 WM h C (Some (bc, i)) RQ).
        + apply KOM. apply DJT; clear -C30; lia.
        + apply IAG. vm_compute. reflexivity.
        + apply KOM. pose proof (z_T_stk h GEO) as Y1. pose proof (z_hull_stk h GEO) as Y2. unfold zapart in Y1, Y2. cbn [fst snd] in Y1, Y2.
          apply DJfar; [right; clear -CB0 CB1; lia| clear - Y1 LOL SPL CB0 CB1 CHI; lia| clear - Y2 LOL SPL CB0 CB1 CHI; lia| clear - STK0 LOL SPL CB0 CB1; lia].
        + exact KB.
        + cbn beta iota. rewrite <- EA. apply KB. rewrite E0. left. reflexivity.
      - exact (recp_L h k dr dn f).
      - exact (recp_gq h k dr dn f).
      - intros bq tq' Eq. exact (recp_tq h k dr dn f bq tq' Eq).
      - exists (Z_to_bv 64 (ck_hdr k)). exact NTH. }
    (* [comment removed for export] *)
    pose proof (ff_view_K AL FF (fsel h c f) h' mo4 (kview_recp h k dr dn f HF2 FX) HK4) as HK'.
    assert (CSM : forall x, ff_CS AL FF h x -> ff_CS AL FF h' x).
    { intros x Hx. apply (ff_view_CS AL FF (fsel h c f) h' x (kview_recp h k dr dn f HF2 FX)).
      destruct HF2 as [Ef|Ef]; rewrite Ef; cbn [fsel]; [exact Hx| exact (ff_cs_mono_fa AL FF h c x Hx)]. }
    (* [comment removed for export] *)
    assert (NB1 : forall a, in_blk (blocks h) a -> ck_ab k <= a < ck_ab k + class_size c -> False).
    { (intros a dd_H; ddestruct dd_H as (bk & Hbk & Ra); intros Xa). destruct bk as [B N]. cbn [fst snd] in Ra.
      ddestruct (in_blk_chunk h a B N WL WR WK Hbk Ra) as (kb & Hkb & STb & -> & -> & Xb & _).
      assert (NAb : ck_ab kb <> ck_ab k) by (intros E; pose proof (NoDup_map_inj ck_ab (h_chunks h) kb k NDK Hkb Hk E) as EK; rewrite EK, STQ in STb; cbv in STb; discriminate STb).
      apply (ext_apart' h kb k a WL WR WK GEO Hkb Hk NAb Xb). rewrite XLK, XHK. exact Xa. }
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
    pose proof (Z.div_mod (ck_user k) 8 ltac:(clear; lia)) as Duk. rewrite UA8, Z.add_0_r in Duk.
    pose proof (Z.div_mod (l_sb (h_L h) + c * 2^32 + 3758096384 + mfa) 8 ltac:(clear; lia)) as Dfaa. rewrite FAA8, Z.add_0_r in Dfaa.
    assert (FK : fkeep (h_L h) (blocks h) QS (d_nb (h_dep h)) (d_bl (h_dep h)) lo SP m m4).
    { apply (fkeep_of_munch _ _ _ _ _ _ _ W m m4 MU). subst W.
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. left. exact Ha. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 2 right; left. split; [unfold in_hull; clear - Ha SLOTH CSR; lia| intros IB; exact (NB1 a IB ltac:(clear - Ha CSR; lia))]. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. do 2 right; left. split; [unfold in_hull; clear - Ha SLOTH E1 E2 E4; lia| intros IB; exact (NB1 a IB ltac:(clear - Ha E1 E2 E4; lia))]. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. rewrite E2 in Ha. do 3 right; left. split.
        - unfold shad, in_hull. clear - Ha Duk Dhe Dhe' Db6 Db6' SLOTH E1 E2 HHD RZB RZN. lia.
        - (intros dd_H; ddestruct dd_H as (c0 & IB & Ea)). refine (NB3 c0 (ck_user k) (nfix n) IB UA8 (proj1 NB) APK _). rewrite <- Ea. exact Ha || (unfold shad; clear -Ha; lia). }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. right; left. clear - Ha C30; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. right; left. clear - Ha C30; lia. }
      apply Forall_cons. { intros a Ha. cbn [fst snd] in Ha. right; left. clear - Ha; lia. }
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
    apply HC. unfold prim_step_post.
    eexists. dexists mo4, y0, y1, y2, ya0, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m4, dr, dn, f.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact WF'|].
    split. { unfold HMq. unfold h'. rewrite (recp_L h k dr dn f). exact (conj G0' (conj G1' (conj G2' (conj G3' (conj G4' (conj G5' (conj G7' (conj G8' (conj G9' GE'))))))))). }
    split; [exact RQ'|]. split; [exact HK'|]. split; [exact HJ4|]. split; [exact CSM|]. split; [exact FK|]. exact (conj WM (conj MI4 ST4)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RecStep.

End ARUN_1.
