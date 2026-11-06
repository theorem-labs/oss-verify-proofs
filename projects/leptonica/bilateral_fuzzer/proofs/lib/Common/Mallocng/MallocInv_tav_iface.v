(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf4 MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops
  MallocInv_ameta_iface MallocInv_ntfree MallocInv_ntpost MallocInv_aspieces.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocInv_tav_iface () := "C47Corelib7Classes?RelationClasses;reflexivityC46Stdlib5Lists4List2InI47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6a_liveC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7a_areasC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7a_pagesC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs9a_mblocksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7a_xmapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs:a_freelistC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8a_brk_loC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8a_activeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6cvalidC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot0>C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common8Mallocng=MallocInv_wf48ctx_heurC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5a_ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6a_metaC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7mt_roleC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5mrole04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mt_w32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mt_memC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs3domC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8MallocngCMallocInv_tav_iface6tavrel01C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6astate00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8meta_rec00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7slot_st00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5mrole00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Classes?RelationClasses=iff_Reflexivec69OSSVerify5KrLib6Common8MallocngCMallocInv_tav_iface>try_avail_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree5mbindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree5tsafeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngCMallocInv_tav_iface?try_avail_specDC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I69OSSVerify5KrLib6Common8MallocngEMallocInv_ameta_iface2II00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI69OSSVerify5KrLib6Common8Mallocng@MallocInv_ntpost7ntframe00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common8MallocngCMallocInv_tav_iface6tavrel00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes6option02C46Stdlib5Lists4List2hdC69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8mt_availC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib6Common8Mallocng=MallocInv_w323w32C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c69OSSVerify5KrLib6Common8MallocngCMallocInv_tav_iface8ring_dryC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib6Common8Mallocng:MallocTree6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
Record tavrel (A A' : astate) (sc : Z) : Prop := {
  tv_live : a_live A' = a_live A;
  tv_areas : a_areas A' = a_areas A;
  tv_pages : a_pages A' = a_pages A;
  tv_mblocks : a_mblocks A' = a_mblocks A;
  tv_xmaps : a_xmaps A' = a_xmaps A;
  tv_fl : a_freelist A' = a_freelist A;
  tv_brk_lo : a_brk_lo A' = a_brk_lo A;
  (* [comment removed for export] *)
  tv_act : forall c, c <> sc -> a_active A' c = a_active A c;
  tv_act_sub : forall x, In x (a_active A' sc) -> In x (a_active A sc);
  (* [comment removed for export] *)
  tv_ctx : forall k, cvalid k -> k <> KActive sc -> ~ ctx_heur k -> a_ctx A' k = a_ctx A k;
  (* [comment removed for export] *)
  tv_grp : forall x mtx aibx slx, a_meta A' x = Some mtx -> mt_role mtx = RGroup aibx slx ->
     exists mt0 aib0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aib0 slx /\
       mt_w32 mt0 = mt_w32 mtx /\ mt_mem mt0 = mt_mem mtx;
  tv_grp_back : forall x mt0 aib0 slx, a_meta A x = Some mt0 -> mt_role mt0 = RGroup aib0 slx ->
     exists mtx aibx, a_meta A' x = Some mtx /\ mt_role mtx = RGroup aibx slx /\
       mt_w32 mt0 = mt_w32 mtx /\ mt_mem mt0 = mt_mem mtx;
  tv_other : forall x mt0, a_meta A x = Some mt0 -> (forall aib sl, mt_role mt0 <> RGroup aib sl) -> a_meta A' x = Some mt0;
  tv_other_back : forall x mtx, a_meta A' x = Some mtx -> (forall aib sl, mt_role mtx <> RGroup aib sl) -> a_meta A x = Some mtx;
  tv_dom : forall x, dom A' x <-> dom A x
}.

Lemma tavrel_refl : forall A sc, tavrel A A sc.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_tav_iface ()) ["WithLayout"] "h01xh11Hh24aib0h34aibxh43mt0h53mtxh62H0h72Hrh82Hxh93slxh:1Ah;2H1h<3aibh=1ch>1kh?2sch@2slp;1p;2p;3p;4p;Bp-1R0g0000R1p4p710p9P0g000^R0p4p710p8g0015j1?Tg001Wj1PTg002aj21Tg003;j1=Tg003[j1OTg004fj1JTg0061j2GTg006Qj1ETg007^j1DTg008ij1CTg00:7j1BTg00;Cj19Tg00;\j2@TP0j3NTg00<hj1MTg00>2j1ITg00?=j30Tg00?Wj1HTg00@bj2FTg00Akj24Tg00C5j25Tg00CWj18Tg00Dbj26Tg00Emj17Tg00G7j1:Tg00HAj22Tg00H\j2>Tg00I6j4<Tg00IQj4;Tg00Ikj2KTP1j4ATg00K2lBLTg00LCR1f1R0f0R230p=3g00LaP0P0P2%?1\1%P0'1%=1R3%O0'1%J0,131G11#=R4%E0'1%D0,14%C0,13%B0,111320#9f3R4/@0,13W1X=1f2R3/@09N12P2W1X01g00MmR5%M2%I39050#9%H3#9f5R5/F4,11W;W6W1W>g00O8R6g00PF#=R7%?6R81454156330R9g00QSR:%84R;163030R<P6f9f7R='41560508R>%80f4R?,6250:R@%70RAf6RB#7RC'3%:0RD%:BRE'3'2'2'2X21,>1X46P?P1f8/4B1565508%85162450:%75RB/3B%:5RB/3B'2'2'2RBX21P414=5156?508%8?164350:R=%7?R5/35RF%:?RG/3GRH'2RI'2P0P=PIP2PFPH1115111GC<C<C<RGC;C;W7W8W9X31W5X01P613CA13ED'2,2@,2>X31,>1X56P?P1PBX31P4PGC;C;X7<X89X97X21X46X0114401562508160290:;#9^@7^<1P0W6W1R0X46X01P0X56X01p-0g00R^g00S71K32CAX01MBLX?1W:o"). Qed.

(* [comment removed for export] *)
Definition try_avail_spec : Prop :=
  forall (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sc : Z) (K : option (word * word) -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s -> 0 <= sc < 48 ->
    (* [comment removed for export] *)
    (forall s' A',
       II sp0 argv envp cb D A' s' -> ntframe A s s' -> tavrel A A' sc -> a_active A' sc = [] ->
       tsafe (K None s') P) ->
    (* [comment removed for export] *)
    (forall s' A' (m : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st),
       II sp0 argv envp cb D A' s' -> ntframe A s s' -> tavrel A A' sc ->
       a_active A' sc <> [] -> m = hd 0 (a_active A' sc) ->
       a_meta A' m = Some mt -> mt_role mt = RGroup aib slots -> mt_avail mt <> 0 ->
       tsafe (K (Some (Z_to_bv 64 m, w32 (mt_avail mt))) s') P) ->
    tsafe ((ta <- as_tryavail (Z_to_bv 64 (caddr (KActive sc))) (Z_to_bv 64 (a_ctx A (KActive sc))) ;; K ta) s) P.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ring_dry (A : astate) (sc : Z) : Prop :=
  a_active A sc = [] \/
  exists h mt, a_active A sc = [h] /\ a_meta A h = Some mt /\ mt_avail mt = 0 /\ mt_freed mt = 0.

(* [comment removed for export] *)
Definition try_avail_specD : Prop :=
  forall (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sc : Z) (K : option (word * word) -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s -> 0 <= sc < 48 ->
    (forall s' A',
       II sp0 argv envp cb D A' s' -> ntframe A s s' -> tavrel A A' sc -> a_active A' sc = [] ->
       ring_dry A sc ->
       tsafe (K None s') P) ->
    (forall s' A' (m : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st),
       II sp0 argv envp cb D A' s' -> ntframe A s s' -> tavrel A A' sc ->
       a_active A' sc <> [] -> m = hd 0 (a_active A' sc) ->
       a_meta A' m = Some mt -> mt_role mt = RGroup aib slots -> mt_avail mt <> 0 ->
       tsafe (K (Some (Z_to_bv 64 m, w32 (mt_avail mt))) s') P) ->
    tsafe ((ta <- as_tryavail (Z_to_bv 64 (caddr (KActive sc))) (Z_to_bv 64 (a_ctx A (KActive sc))) ;; K ta) s) P.

Lemma try_avail_specD_spec : try_avail_specD -> try_avail_spec.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_tav_iface ()) ["WithLayout"] "h02A'h12s'h21Ah31Dh42H1h52H2h62H3h72H4h83HIIh92HNh:2HSh;3Hsch<1Kh=1Ph>1Rh?2TDh@2_HhA3aibhB4argvhC2cbhD4envphE1mhF2mthG1shH2schI5slotshJ3sp0p;1p;2p;9p;4p;3g00SgR0p616311001R1g00U>R2p4p710R3p8P1p100V?p4p7210R4p8P1g00WDR5p4p710R6p8P1g00XIR7p616311001R8p8P8P3p8P8P4p8P8P6p8g00Yaj10Tg00ZFj1=Tg00Zdj1:Tg003;j12Tg0061j2NTg0015j1<TP2j1GTg00[Gl93Tg00\Vj2BTg00]2j1ATg00]Wj1@Tg00^5j2?Tg00HAj2>Tg00^Qj46Tg00_`j35Tg00;\j24Tg00a1j1MTg00?=j31Tg00aQj1LTP5j3;Tg00;Cj19Tg00b3j3FTg00Akj2DTg00C5j28Tg00CWj1CTg00Dbj2ETg00bJj17Tg00cVj2HTg00d<j1ITg00eBj4JTg00ebj2KTg00g3R5#0#0#0R2#0#0#0#=R6#:R8%=2#:#2R2#2R4g00LCR3#2R9g00LaR:g00gXR;1N88R<#<f9R=#G[p-0\;\=p,2MLR>p,2HTR?P=f8R@f7RAf6RBf5RCf4RDf3REM93g00h`RF/BE%A5#0#0#0#0#@,?E'>P>P?f=R5f<RGf;RHf:RIP=f0RJf1RKM93P>P=P@f2RLC6A5IL@14E=%M3RM519fBRNP=%L<PCO2;;@[[[[^0:^1;g00O8ROg00PF#2P>P?PNfARPf@f?RQf>RRPDPCM93P>PRP5PBC6A5QB514AR=19M#914@Q9F3F913A%<O1D=@18OA31g00QS%C@1EAB31%7==13F#9fKPNP8P81H6H%7I#ICJ,8<P5O2;;P[[[[[[[[]I^A3]F^E3^0:^1;PQPRP5PGPHPIP=P@PAPBPCPDPEPLP>P?PQPRP5PGPHPJPKM93P>PHPIPLC6A5GLI14EH=19M1KRGP@PBPCPDPEPLPKO6W@W7W6W5W4X0:X1;PJO?W:W9W;W8W=W<XH3WGW2W3XC2XD4WBWJX>1P0eX?7o"). Qed.

End WithLayout.
