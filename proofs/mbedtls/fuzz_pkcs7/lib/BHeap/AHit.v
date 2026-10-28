(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKinvS AKFrame. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AInstDepot AVst
     AW_Unwind AW_Unwind2 AW_MmapFixed AW_DepotA AW_DepotB AW_DepotC AW_DepotInv AW_DepotCfg AW_DepotTop AW_MallocA AW_AllocA AW_Poison
     AW_AllocB AW_MallocB AW_MallocC AW_MallocTop HMLib HM.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill AW_Populate AW_Large.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs HMFrame AHeapB.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AJ.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
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
Ltac2 gd_tbl_AHit () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.A_DEP_END"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.shad"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "Stdlib.ZArith.BinInt.Z.min"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.hfr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "ARUN_1.Hit.hit_keep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pclass"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "Stdlib.Lists.List.incl"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.nat"; "Corelib.Lists.ListDef.firstn"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Peano.lt"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Corelib.Lists.ListDef.nth"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_MALLOC"; "ARUN_1.A_WRAP_MALLOC"; "ARUN_1.Hit.Framed.KdF"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.CSd"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.Gn"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.Gs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocTop.malloc_hit_cfg"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.D_CSOK"; "ARUN_1.Hit.IML"; "ARUN_1.Hit.IMH"; "ARUN_1.Hit.GOT64"; "ARUN_1.Hit.GSB64"; "ARUN_1.Hit.Framed.F_KL"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.D_CSmono_n"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.D_CSmono_s"; "ARUN_1.Hit.Framed.F_apart"; "ARUN_1.Hit.Framed.F_T_node"; "ARUN_1.Hit.Framed.F_T_store"; "ARUN_1.Hit.Framed.F_ROOM_n"; "ARUN_1.Hit.Framed.F_ROOM_s"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.D_noshadow"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vwf"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.TR"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KEager"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_errno"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_htop"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.FR_MAXm"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.win24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.from_primary"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pc_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cache"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "ARUN_1.Hit.hit_fpost"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

Definition A_WRAP_MALLOC : Z := 0x69480.   (* [comment removed for export] *)

Section Hit.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L51850984632.5000001S". (* [comment removed for export] *)
  #[using="IMG"] Lemma IML : al_img_lo AL <= 0x10000. Proof. ddestruct IMG as (_ & -> & _). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG"] Lemma IMLO : al_img_lo AL = 0x10000. Proof. ddestruct IMG as (_ & E & _). exact E. Qed.
  #[using="IMG"] Lemma IMH : al_img_hi AL = 0x65f000. Proof. ddestruct IMG as (_ & _ & H & _). exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L35126631783.8L6702071143.8 000001002SS". (* [comment removed for export] *)
  #[using="IMG"] Lemma GOT64 : al_img_lo AL + 64 <= al_got AL /\ al_got AL + 128 <= al_img_hi AL /\ al_got AL mod 8 = 0. Proof. ddestruct IMG as (G & L & H & _). rewrite G, L, H. split; [cbn; lia| split; [cbn; lia| reflexivity]]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L21925994854.8L22280576870.8000001002SS". (* [comment removed for export] *)
  #[using="IMG"] Lemma GSB64 : al_img_lo AL + 64 <= al_gsb AL /\ al_gsb AL + 128 <= al_img_hi AL /\ al_gsb AL mod 8 = 0. Proof. ddestruct IMG as (_ & L & H & G). rewrite G, L, H. split; [cbn; lia| split; [cbn; lia| reflexivity]]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition hit_keep (h' : ahst) (lo SP T c AB UB n : Z) (m m' : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AHit ()) "Px,(0.&40.)Za,$1.(2.&40.R1.)P,(3.(4.(5.O9.R1.)(6.R1.O8.)))P,(3.(4.(5.$7.R2.)(6.R2.$8.)))P,Pb,$1.P,(9.$1.R1.(:.(;.O:.)))(3.(4.(5.R2.R5.)(6.R5.(<.R2.(=.+2.+14.)))))P,Pb,$1.P,(9.$1.R1.(>.(;.O:.)))(3.(4.(5.R2.R6.)(6.R6.(<.R2.(=.+2.+17.)))))P,(3.(4.(5.(<.(<.O7.+=0.)(?.+50.O6.))R5.)(6.R5.(<.(<.(<.O7.+=0.)(?.+50.O6.))+4.))))P,(3.(4.(5.(<.O7.+:>0.)R6.)(6.R6.(<.O7.+:>8.))))P,(3.(4.(5.(<.O7.+:?0.)R7.)(6.R7.(<.O7.+<61.))))P,(3.(4.(5.(10.O4.+10.)R8.)(6.R8.O4.)))P,(3.(4.(5.O5.R9.)(6.R9.(<.O5.+10.))))P,(3.(4.(5.(11.O4.)R:.)(6.R:.(<.(<.(11.O4.)(12.(13.O3.)+8.))+1.))))P,(3.(4.(5.O4.R;.)(6.R;.(<.O4.(14.(13.O3.)+1000.)))))(15.(16.(0.&8.))A1.O1.R=.A1.O2.R=.)")
(* [comment removed for export] *).

  Definition hit_fpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : ahst) (LB LF : list (Z * Z)) (n lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AHit ()) "Lcf,$17.(18.(0.&40.)Lt0,(0.&40.)(18.(0.&40.)Lt1,(0.&40.)(18.(0.&40.)Lt2,(0.&40.)(18.(0.&40.)La0,(0.&40.)(18.(0.&40.)La1,(0.&40.)(18.(0.&40.)La2,(0.&40.)(18.(0.&40.)La3,(0.&40.)(18.(0.&40.)La4,(0.&40.)(18.(0.&40.)La5,(0.&40.)(18.(0.&40.)La6,(0.&40.)(18.(0.&40.)La7,(0.&40.)(18.(0.&40.)Lt3,(0.&40.)(18.(0.&40.)Lt4,(0.&40.)(18.(0.&40.)Lt5,(0.&40.)(18.(0.&40.)Lt6,(0.&40.)(18.P,(0.&40.)(16.(0.&8.))Lm',P,(0.&40.)(16.(0.&8.))(18.$19.Lmo',$19.(18.$1:.Lh',$1:.(18.$1.LUB,$1.(18.(1;.(0.&8.))Ljunk,(1;.(0.&8.))(4.(15.$17.R15.(1<.(1=.(1>.O1:.O19.O18.O17.R14.R13.R12.O16.O15.R11.R10.R?.R>.R=.R<.R;.R:.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R9.R8.R7.R6.)O:.(1?.O1:.)O9.(20.(0.&40.))R5.(21.$22.))R4.))(4.(15.(0.&40.)R11.(23.&40.R2.))(4.(24.$22.R5.)(4.(25.$22.R5.O4.(2.&40.O19.))(4.(26.O1.R4.)(4.(27.$22.O2.R5.)(4.(28.VhAR,R3.(29.(2:.$1.$1.)(2;.$1.$1.R2.O5.)O7.)O6.R5.)(4.(2<.VhAR,VAL,R3.R4.)(4.(2=.R5.R4.)(4.(15.$2>.(2?.R3.)(2?.O8.))(4.(15.$1.(30.R3.)(30.O8.))(4.(5.(31.R3.)(<.(31.O8.)(<.O3.+3.)))(4.Px,$1.P,(32.VAL,(33.O8.)R1.)(32.VAL,(33.R5.)R2.)(4.(34.R3.O4.(2.&40.O19.)(35.(2?.O8.))(36.O5.)(10.R2.(37.O5.))R2.O5.O2.R5.)(4.(38.$1.(:.(;.O8.))(:.(;.R3.)))(4.(38.$1.(>.(;.O8.))(>.(;.R3.)))(4.(15.$1.(39.R2.+10.)=)(4.(5.+10007???8000.R2.)(4.(5.(<.R2.O5.)(3:.VhAR,))(4.PB,$1.Pj,$1.P,(9.(2:.$1.$1.)(2;.$1.$1.R2.R1.)O7.)(3;.(5.(<.R5.O5.)R3.)(5.(<.R3.R2.)R5.))(4.(3;.(5.(<.R2.O5.)(3<.(2?.O8.)))(5.(<.(3<.(2?.O8.))$3=.)R2.))(3>.$22.R5.R2.(29.$3?.(40.(41.O5.)R1.)(42.$3?.))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L62962972942.1100000=S1l2ds1i2Hi1H". (* [comment removed for export] *)
  #[using="Type"] Lemma nth_error_firstn_map : ltac2:(CDefT.buildp (gd_tbl_AHit ()) "Pl,(1;.$1.)Pds,(1;.(0.&40.))Pi,$43.P,(15.(1;.(0.&40.))(44.(0.&40.)(45.$1.R3.)R2.)(46.$1.(0.&40.)(23.&40.)R3.))P,(47.R2.(45.$1.R4.))(15.(16.(0.&40.))(48.(0.&40.)R4.R3.)(49.(0.&40.)(23.&40.(4:.$1.R3.R5.=))))")
(* [comment removed for export] *).
  Proof.
    intros l ds i E Hi. assert (X : nth_error (firstn (length l) ds) i = nth_error ds i).
    { rewrite nth_error_firstn. destruct (Nat.ltb_spec i (length l)); [reflexivity| lia]. }
    rewrite <- X, E, nth_error_map. rewrite (nth_error_nth' l 0 Hi). reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG ALWF"] Lemma wrap_step : ltac2:(CDefT.buildp (gd_tbl_AHit ()) "PCS,P,$1.SpPra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(4;.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(16.(0.&8.))P,(4<.VAL,R23.)(4=.$22.VAL,R24.Lms',$4>.(15.$4>.R1.(1=.(1>.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(23.&40.$4?.)R4.(20.(0.&40.))R3.(21.$22.)))(1=.(1>.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(23.&40.$50.)R3.(20.(0.&40.))R2.(21.$22.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold A_WRAP_MALLOC, A_MALLOC. zstep. apply evtA_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Framed.
    Variable v0 : vst. Variables nb0 bl0 : list Z. Variable mo0 : Model.
    Hypothesis VR0 : vranges_ok AL v0.
    Hypothesis VWF0 : vwf AL v0.
    Hypothesis SLACK : v_eb v0 + 4096 * vnb v0 + RES_DEPOT <= VLIMIT.
    Hypothesis CB20 : v_cb20 v0 < J20.
    Hypothesis CB23 : v_cb23 v0 + (2^20 / 2^23 + 2) < J23.
    Definition KdF (nb bl : list Z) (mo : Model) : Prop := Kd AL v0 nb0 bl0 nb bl mo /\ mo_frame mo0 mo.
    #[using="VR0"] Lemma F_KL : forall nb bl, kinv AL (CSd AL v0 nb0 bl0 nb bl) (KdF nb bl).
    Proof. intros. apply kinv_KF. apply D_KL. exact VR0. Qed.
    #[using="Type"] Lemma F_apart : ltac2:(CDefT.buildp (gd_tbl_AHit ()) "Pnb,(1;.$1.)Pbl,(1;.$1.)Pmo,$19.Pa,(0.&40.)Pn,(0.&40.)P,(51.R5.R4.R3.)P,(15.$52.(53.(54.(2:.(0.&40.)(0.&40.))(55.(56.R4.))(57.(56.R4.)))R3.R2.)$58.)P,(5.+10000.(2.&40.R3.))P,(5.(<.(2.&40.R5.)(2.&40.R4.))(3:.VhAR,))Px,$1.P,(3;.(59.VhAR,VAL,Vv0,Vnb0,Vbl0,R:.R9.R1.)(4.(5.(5:.VAL,)R1.)(6.R1.(5;.VAL,))))(3.(4.(5.(2.&40.R8.)R2.)(6.R2.(<.(2.&40.R8.)(2.&40.R7.)))))")
(* [comment removed for export] *).
    Proof. intros nb bl mo a n [K _]. apply (D_apart AL v0 nb0 bl0 nb bl mo a n K). Qed.
    #[using="IMG ASB SLACK"] Lemma F_T_node : ltac2:(CDefT.buildp (gd_tbl_AHit ()) "Pnb,(1;.$1.)Pbl,(1;.$1.)Pmo,$19.Pa,(0.&40.)P,(5<.Vnb0,Vbl0,R4.R3.)P,(51.R5.R4.R3.)P,(15.$1.(39.(2.&40.R3.)+1000.)=)P,(6.=(2.&40.R4.))P,(5.(<.(2.&40.R5.)(=.+2.+14.))(3:.VhAR,))P,(15.$52.(53.(54.(2:.(0.&40.)(0.&40.))(55.(56.R7.))(57.(56.R7.)))R6.(23.&40.(=.+2.+14.)))$58.)(4.(51.(54.$1.R:.(29.$1.(2.&40.R7.)(42.$1.)))R9.(5=.+22.R7.(=.+2.+14.)R8.))(5>.(59.VhAR,VAL,Vv0,Vnb0,Vbl0,(54.$1.R:.(29.$1.(2.&40.R7.)(42.$1.)))R9.)(2.&40.R7.)(=.+2.+14.)))")
(* [comment removed for export] *).
    Proof.
      intros nb bl mo a G [K FR] AAL A0 ACE RF.
      destruct (D_T_node AL ASB IML IMH v0 nb0 bl0 SLACK nb bl mo a G K AAL A0 ACE RF) as [K' C']. split; [| exact C'].
      split; [exact K'|]. eapply mo_frame_trans; [exact FR| apply mo_frame_anon_grant].
    Qed.
    #[using="IMG ASB SLACK"] Lemma F_T_store : ltac2:(CDefT.buildp (gd_tbl_AHit ()) "Pnb,(1;.$1.)Pbl,(1;.$1.)Pmo,$19.Pa,(0.&40.)P,(5?.Vnb0,Vbl0,R4.R3.)P,(51.R5.R4.R3.)P,(15.$1.(39.(2.&40.R3.)+1000.)=)P,(6.=(2.&40.R4.))P,(5.(<.(2.&40.R5.)(=.+2.+17.))(3:.VhAR,))P,(15.$52.(53.(54.(2:.(0.&40.)(0.&40.))(55.(56.R7.))(57.(56.R7.)))R6.(23.&40.(=.+2.+17.)))$58.)(4.(51.R:.(54.$1.R9.(29.$1.(2.&40.R7.)(42.$1.)))(5=.+4022.R7.(=.+2.+17.)R8.))(5>.(59.VhAR,VAL,Vv0,Vnb0,Vbl0,R:.(54.$1.R9.(29.$1.(2.&40.R7.)(42.$1.))))(2.&40.R7.)(=.+2.+17.)))")
(* [comment removed for export] *).
    Proof.
      intros nb bl mo a G [K FR] AAL A0 ACE RF.
      destruct (D_T_store AL ASB IML IMH v0 nb0 bl0 SLACK nb bl mo a G K AAL A0 ACE RF) as [K' C']. split; [| exact C'].
      split; [exact K'|]. eapply mo_frame_trans; [exact FR| apply mo_frame_anon_grant].
    Qed.
    #[using="VR0 SLACK CB20"] Lemma F_ROOM_n : forall nb bl mo, Gn nb0 bl0 nb bl -> KdF nb bl mo -> exists a, anon_grantable 0x22 (2^20) mo a.
    Proof. intros nb bl mo G [K _]. exact (D_ROOM_n AL v0 nb0 bl0 VR0 SLACK CB20 nb bl mo G K). Qed.
    #[using="VR0 CB23"] Lemma F_ROOM_s : forall nb bl mo, Gs nb0 bl0 nb bl -> KdF nb bl mo -> exists a, anon_grantable 0x4022 (2^23) mo a.
    Proof. intros nb bl mo G [K _]. exact (D_ROOM_s AL v0 nb0 bl0 VR0 CB23 nb bl mo G K). Qed.

    Definition malloc_hit_F := ltac2:(CDefT.buildp (gd_tbl_AHit ()) "(60.VhAR,VAL,VIMG,VALWF,(59.VhAR,VAL,Vv0,Vnb0,Vbl0,)$51.(61.VhAR,VAL,VALWF,VASB,$62.$63.$64.$65.Vv0,Vnb0,Vbl0,VVWF0,)$66.(67.VhAR,VAL,Vv0,Vnb0,Vbl0,)(68.VhAR,VAL,Vv0,Vnb0,Vbl0,)$69.(5<.Vnb0,Vbl0,)(5?.Vnb0,Vbl0,)$6:.$6;.$6<.$6=.(6>.VhAR,VAL,VALWF,$62.$63.$64.$65.Vv0,Vnb0,Vbl0,VVWF0,)VASB,)")
(* [comment removed for export] *).
  End Framed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma T_ne_dtls : ltac2:(CDefT.buildp (gd_tbl_AHit ()) "Ph,$1:.P,(6?.VhAR,VAL,(33.R1.))(3.(15.$70.(71.(35.(2?.R2.))+1000.$72.$58.$58.)(71.(73.(2?.R2.))+1000.$72.$58.$58.)))")
(* [comment removed for export] *).
  Proof.
    intros h VW E. dpose VW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).   (* [comment removed for export] *)
    cbn [vst_of v_tr] in ND. unfold tr_of in ND. do 6 apply NoDup_app_remove_l in ND. unfold fixed_of in ND. apply NoDup_app_remove_r in ND.
    inversion ND as [|? ? NI ND']; subst. apply NI. rewrite E. right; right; left; reflexivity.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0560@L10317707088.2  L10413547907.4  L10426738122.3  L10513695255.14 L1054598157.5   L10617339361.9  L10811455946.5  L10973993704.6  L11104489937.10 L11734016751.7  L12420425442.16 L12611791309.16 L12666001579.2  L12720060011.7  L13681847583.7  L13775514455.10 L13799509222.9  L13999696941.3  L14003737881.6  L14508660423.6  L14540139333.2  L14630591911.13 L14736408896.1  L15068280145.6  L15468931428.3  L15538925788.2  L15546923538.6  L15687735978.2  L15689833139.2  L15815630454.4  L16328963136.9  L1638377853.0   L16400143469.7  L16672986975.6  L17009279662.14 L17120848823.0  L17285243853.4  L17336395824.7  L17621900146.7  L17784320769.13 L17798788128.11 L17829640060.18 L18223442391.6  L18236259630.7  L1857971725.6   L18926727031.2  L18928855014.4  L18930958230.3  L19122686691.7  L19325012089.6  L19325012729.6  L19325060736.6  L19325175423.3  L19325240960.6  L19927190819.15 L19976692553.4  L20066615052.14 L20386160296.14 L20398691481.13 L20525867626.5  L21312925604.7  L22313481905.11 L22868230123.4  L22885885912.15 L23131855153.2  L23236596020.9  L23251332266.8  L2325139203.14  L23251438437.10 L23251438437.5  L23538798032.9  L23765008255.6  L239050803.6    L24215315612.2  L2424857170.2   L24313402471.16 L24360966460.3  L24361222476.1  L2462299999.2   L2465711691.19  L24892949366.10 L24922284613.2  L25007717463.2  L25009814606.2  L2514918327.3   L25158569804.199L25211381463.7  L25619381187.16 L25916286205.0  L2631458591.5   L26336433588.11 L26547404252.3  L26663314677.10 L26831009109.6  L26889736996.5  L26984023146.3  L27542503627.6  L27608114289.7  L27697017043.2  L27705381220.6  L27963306124.6  L2824854936.6   L28557922057.3  L28772126126.6  L2882426241.5   L28865258673.11 L28984171752.8  L29086588489.5  L2978961816.0   L30809564980.4  L30908427776.3  L3129335810.3   L31313323145.3  L31440474728.6  L31700401835.4  L31853502798.7  L31889444643.9  L31919089093.2  L32598498269.1  L33081245254.6  L33235818719.3  L34301741628.13 L34301741628.14 L34301742015.15 L34301742015.16 L34301897727.10 L34301897727.13 L34301897727.8  L34307931039.11 L34307931039.14 L34307931039.8  L34705063038.7  L35264433605.4  L35269483449.1  L3540772118.13  L35431284852.4  L35527826779.6  L3555205172.17  L36107553247.2  L36107562391.15 L36107621412.6  L36109652399.3  L36225639796.9  L36382893066.3  L36426039819.2  L36432482090.6  L36644267936.2  L36811283190.3  L37415665760.6  L37438245544.3  L37637199976.0  L3765518222.7   L37802068022.9  L38093479687.8  L38099722297.6  L38099722297.7  L38099722297.8  L38099986473.6  L3819404470.4   L38246038461.6  L38646644277.7  L38688208282.6  L38692635477.0  L39042635707.6  L39061958544.6  L39093820477.6  L39188636933.0  L39220637093.0  L39288613011.14 L39332637397.0  L39716638549.0  L39910504545.9  L40110954359.15 L40171304529.12 L40228640085.0  L40401253682.0  L40410541975.5  L40553178201.5  L41004724830.6  L41357445052.3  L41540465941.4  L42730054363.6  L42764035438.4  L43059164842.6  L43720258116.12 L43764714725.14 L43871513222.1  L44010951469.3  L441850132.6    L44345217449.14 L44530526816.6  L44720341934.2  L44729727553.13 L4496489150.13  L45592546392.133L45592546392.5  L45711341755.3  L45717584446.9  L45717619843.18 L45717627083.2  L45751307029.6  L47268122930.6  L47821726715.7  L47862729053.5  L48098984137.3  L48792094175.3  L49179260091.4  L49949432263.134L5004869780.5   L50466637393.6  L50659591546.3  L50850525385.0  L51143378400.6  L51322266494.2  L51356925108.3  L51440081528.8  L51454961638.5  L52085800731.13 L52182764891.6  L5221355588.6   L52877453090.17 L52877453090.2  L52967442551.3  L53051764561.0  L53060451552.7  L53089742486.12 L53098296376.16 L53723044368.10 L53807381540.9  L53844214391.6  L5429770831.7   L54329746417.3  L54791753240.4  L54822598889.15 L54822598889.16 L54822598889.18 L54824429705.18 L54889726663.6  L54976314723.3  L55342555388.9  L55588686165.0  L55686442750.451L55784958067.6  L56542261992.2  L56543519691.6  L5675128892.6   L56777700252.8  L57051746208.7  L57388862637.6  L57722551259.5  L57743850048.6  L57792782281.2  L5808119834.21  L58679987322.13 L58697296220.429L58838112733.20 L58852426124.10 L58852426124.15 L58852844742.13 L59114927140.6  L59308579027.7  L59308585216.8  L59308661072.21 L59308661201.4  L59321559543.131L59355849605.0  L59671783292.13 L59671783292.14 L60165102203.6  L60359437735.5  L60542124968.5  L60546574954.14 L60729584128.7  L60785358792.0  L61020372049.151L61030986973.308L61035084364.105L61091856317.6  L61382612458.2  L61384707224.3  L61885460821.3  L62551465488.8  L62576670552.3  L62601765528.6  L62693759124.4  L62935399390.6  L63179267359.2  L63318374456.20 L63332992295.21 L63333409385.17 L63333409385.18 L63333409385.21 L63368316718.106L63368316718.327L63370329133.2  L63374621462.152L63374621462.309L63521577081.4  L63714504754.10 L63892018588.8  L64180530379.2  L6434843067.17  L64612082378.0  L65271643703.0  L65514784813.3  L65514894601.16 L65739535828.1  L6585193638.7   L6644549738.3   L6644560475.2   L6652949373.2   L6656757144.3   L6699626258.16  L6753787830.14  L6761898097.3   L67645412041.5  L67782583095.0  L67792869265.6  L67831404525.6  L777962750.0    L8118647786.0   L8753987091.4   L8895713299.5   L8903559039.5   L8997412646.2   L9251602773.16  00000300<00D00d01301H01R01[02302E02l03L03T03c04104N04^04c04h05;05A05]05a05n06706>06G06Q06Z06a07507607E07R08;08<08L08c09109V0:20:j0;60;M0;Y0;Z0;[0;_0;o0<80<A0<J0<S0<\0=J0=V0>?0>d0?I0?X0?m0@I0@Y0AC0AI0Ab0B80B`0C80CI0Ca0D90DJ0DM0DS0E=0E@0EC0EJ0F70FD0FG0FP0FZ0Fa0GV0Gj0HS0HT0Hb0IH0IM0Ie0J50J<0JF0JO0Jm0K40KC0KL0KU0K_0Km0Kn0LI0L[0M00M10M;0MG0MN0MV0M_0Mj0N80NT0NX0N[0Nj0O10OR0P20P^0QS0R;0Re0S:0S\0T>0TO0Tc0Tm0U10UU0U_0V70V[0Va0WG0WX0Wa0X60X@0XI0XQ0XW0X`0Y50Y>0Y?0YT0Yd0Z:0ZI0Z[0[00[?0[K0[\0\20\?0\@0\P0\`0\n0\o0]00]U0]V0]W0]g0^L0^l0^m0^n0_<0_J0_a0_k0`70`C0`O0`b0aB0ag0aj0ao0b=0b`0c50c>0cZ0d;0dg0e30e<0e[0fM0fS0fi0g70gF0gT0g\0gc0gm0hO0hd0hm0i60i70iC0iK0iT0id0j80jU0j^0jl0kK0kR0kY0kZ0kn0lK0m80mP0m`0mm0n?0nI0nR0o70oc10R11>11G11O11`11a13V13c13k14>14G14[15115?15L15Y15\16c17K19J1:L1;01;Y1<?1<Q1<b1=81>41>@1>b1>c1?E1?l1@71@81@E1@i1A<1A=1An1CG1C_1Cl1D21D;1DF1D^1De1Dn1E81EA1EH1FC1G=1Gi1H^1IX1J01KP1KQ1LB1M[1Mg1NA1NU1N_1OF1OG1OH1OM1Oh1Ol1P<1PG1PN1PY1Pc1QI1Qh1R21R:1R;1R@1RN1RO1RP1R]1Rl1S;1SB1SfS1LS1L1T3TB'S1h1i2HiS1n1L1c1p2SB3cnt1q2pw2AB1x1X3NF8S1L2SB3B6A4B6LOS1n1L1c3CSR1k2RB2k'1HS1L1T1A2A1S1n1L1c1TS1n1L1c1p2SB3cnt1q2pw2ABS1t1b1a2k02A21X2A1S1n1L1c1p2SB1r3cnt1q2pw2AB2RB4ABMU4UBLES1n1L1c1p2SB3cnt1q2pw2AB2RB4ABLOS2sh3BIGS1L3CTX2nb2k01XS3tf'3TFX1H2H0S2sp2lo2SP1L5SPTOP3TOP6HTOPHIS1n1L1c1T2c'3Hc'S1n1cS1n1cS2sp2SP1L3TOP5TOPHIS1h2qnS1n1L1c1p2SB3cnt1q2pw2AB1x1XS2k'S1L1T2bl2j01XS1n1c3CSRS2k'2S3S1n1L1c1TS2k'5WC30'S2k'4WC30S1n1c1pS1n1L1c1r2RB1A2k02H3SS1L3CTX2bl2j01XS1L1T2nb2k01XS1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB5SHRNG3NF8SS2k'2S12S25RZk16S1h1d2D02N'3tf'3NB'3POTS1n1L1c1k2i'1HS1n1L1c1p2SB3cnt1q2pw2AB2RB4ABLO4RBLOS1n1L1c1p2SB3cnt1q2pw2AB3AB0S1n1L2NB1c1p2SB3cnt1q2pw2AB3RZB6NEEDCS4UBLE3NF12k'2AP2USS1L2kk2ii2FRS1L2SB4SB163B6A4B6LO2DQS1n1L1c2RB1ASSS2N'S1L2c'1x1j2DJ2MJS1n1c3CSRS1n1c3CSRS1n1c3CSRS1n1c3CSRS1n1c3CSRS1n1L1c1p2SB1r3cnt4AUMU1q2pw2AB6NEEDCS2RB4ABHIS1n1c4CS161HS1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB5SHRNG3NF8S1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB5SHRNGS1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB5SHRNGS1h1L1i5AUMU'1HS1L3CTX5CXLEN2bl2j01XS1n1L1c1p2SB3cnt1q2pw2AB3AB0S3hAR2k'2S34CEILS1n1L2NB1c1p2SB3cnt1q2pw2AB3RZB4UBLE3NF11XS1A2H1S1L2c'1A2k02A11x2Hx5RBLO'S1t1A2k02A12A21x2Hx2W5S1n1L1c1p2SB3cnt1q2pw2AB4RZ164AB162D12D2S1L1T2TI1A2k02A12A21x2HxS1A2k02H21x2Hx2A1S1n1L1c1T4GC312c'3Hc'2NES3hAR2sp2lo2SP3SPL5LOIMGS1L1T3CTX5CXLEN1XS1LS1n2NBS1n1L1c1p2SB1r3cnt1q2pw2AB3RZB3N2B2RB4ABMUS1xS1xS1n3NF1S3hAR1n1L1c1p2SB3cnt1q2pw2AB3RZB3AB03AB14UBLES1n1c1p3cnt1qS1LS2k'4WC30S2k'5WC30'S1L3CTXS3hAR2sp1n2SP1L1c1p1T3CTX2SB3TOP1r3cnt1q2pw2UB3CHB2RBS1h1n2NB3BUD2v01B2AFS1n1L1c1p2SB3cnt1q2pw2AB2k'1A2k02A12A22S4SS2bl2sb2jj3HjjS3hAR1h1L2SB4B6HI4SEHI2c'6MULIM'5RBHI'S1L1TS1n1L1c1p2SB3cnt1q2pw2ABS2k'3RZ'2RU1H2H0S1n1c1pS3hAR1a2SAS1n1L1c1TS2sp2SP1L5SPTOP6HTOPHI7STKHI47S1n3NDBS1n3FP'1H2H02H1S1n1L1c1TS1n1L1c1TS3hAR1b2SAS1n1L1c1T4GC31SS1n1L1c1p2SB3cnt1q2pw2AB2UBS1n1L1c1r1k3KCS2RBS1L3TOP5TOPHI7STKHI47SS1L2c'3Hc'S1h2c'5AUMU'S1L3CTXS1A2k01HS1n1L1c1TS1L3CTX3CB'S1n1L1c1k2i'1HS1L2SB4SB162c'2k'2DM4C16'2DCS2k'S1AS1L2k'1A2A13SL1S1L3CTXS1n1L1c1p2SB3cnt1q2pw2AB3NF81x2Q9S1n1L1c1p2SB3cnt1q2pw2AB2UB1x2Q9S1n1L1c1p2SB3cnt1q2pw2AB3RZB6NEEDCS3N2B1x2Q8S1n1L1c1p2SB3CSR3cnt1q2pw2AB3RZB1x2Q86NEEDCS4UBLE3NF1S1L1T2TI1A2k02H02H11x2Hx1n1c2W12TB2A12A2S1n1L1c1T4GC312TI1A2k02H02H11x2Hx2TB2A12A2S1L1T1A2k02W21x2Hx2W3S1L1T1t1A2k02A21x2Hx1X2A11n1c4GC31S1n1L1c1T4GC311t1A2k02A21x2Hx1X2A1S1L1T1A2k01x2Hx1XS3hAR1L2SB4B6HI4SEHIS1L2ii3HiiS2k'S1n1L1c1p2SB3cnt1q2pw2AB3RZB2RB4ABLOS1L2c'3Hc'S3hAR2sp2lo2SP3SPL5LOIMGS1n1L1c1p2SB3cnt1q2pw2AB3RZB2RB4ABLOS1x2HxS1n1L1c1p2SB3cnt1q2pw2AB3AB01x2Hx1H2H0S1A2k02A11x2Hx2DAS1x3OUT1HS1L1T1A2k02A12A21x2HxS2k'2S22S3S2k'4CSR'S1h2k'1HS1n2NBS1A2k02H3S1h2N'2id3IDB3NB'3DNBS3hAR1b1XSS1L3CTX5CXLEN2nb2k01XS1n1L1c1T2c'3Hc'S1A2k02A12A21x2Hx1b2W6S1A2k01x2Hx1b1HS1A2k02H11x2Hx1b1HS1A2k02A12A21x2Hx1b1HS1A2k01x2Hx1b1XS1h1n2NB3BUDS2sp2SP1L3TOP3LEtS2sp2lo2SP1L5STKLO3SPLS1L1T2nb2k01XSS2k'3RZ'2NC1H2H0S2k'2RU1H2H03RZ'S1n1c1k2i'3ILTSSS1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB5SHRNGSSS1n1L1c1T2c'3Hc'S3hAR1n1L1c1p2SB3cnt1q2pw2AB3AB14UBLES1n1L1c1p2SB3cnt1q2pw2AB3RZB3AB0SSS1L2SB4SB162DMS2nb2sn2k03Hk0S3hAR2lo1L5STKLO6STKLOCS1n1c4GC31S2N'2N11H2H0S2k'2NC1H2H0S1L3TOP4TOP1S1h1L2k'2i'5AUMU'1HS1n1L1c1p2SB3cnt1q2pw2AB3RZB3AB0S1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB5SHRNGS1tS1n1cS1n1c1k2k'3GTkS1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB3NF8S1h2N'2id3IDB3NB'3DNBS2c'4CSR'S1n1L1c1p2SB3cnt1q2pw2AB1x1XS1n1L1c1p2SB3cnt1q2pw2AB3RZB4UBLES3hAR2sp1n2SP1L1c1p1T3CTX2SB3MCR1r4PMAX4HCNTS1n1c1p4HCNTS1x3OUT1HS1A2k03ALO1x2Hx2DA2DK2MK3hAR2A2S3hAR1n1L1c1p2SB3cnt1q2pw2AB3RZB3N2B3AB11x2Hx1H2H0S1x2HxS3hAR1L3CTX4CXHI5CXLENS1n1L1c1T4GC31S1n1L1c2RB1A2H1S2lo1L5STKLO1HS1n1c2CRS1L3CTXS1h1L1x2HxS3hAR2sp1n2SP1L1c1p1z1l1T3CTX2SB1rS1L3TOP5TOPHI7STKHI47S1n1L1c1TS2v04CB20SS1L2kk2ii2FRS2c'3Hc'S2v04CB23S2k'2F12F32F42F5S1h1L2c'5AUMU'5RBLO'S1n1L1c1p2SB3cnt1q2pw2AB1H2H0S1n1L1c1TS1n1c1k2k'3LTkS1n1L1c1p2SB3cnt1q2pw2AB2RB3NF1S1n3NF1S1L3CTXSS1h1L2k'1A2k02A23SL2S1n1L1c1p2SB3cnt1q2pw2AB2k'1XS1n1L1c1p2SB3cnt1q2pw2AB2k'2S12S22S32S45RZk16S1n1L1c1p2SB3cnt1q1k3HK2S1n1L1c1T2c'3Hc'S1L1T1A2k02A2S2sp2SP1L3TOP4TOP2S1h2j03Hj0S2sp2SP1LS1n1L1c1p2SB3cnt1q2pw2AB1A2k02AP1x2HxS1n1L1c1p2SB3cnt1q2pw2AB3AB01A2k02H11x2Hx2A2S1n1L1c1p1T2SB3cnt1q2pw2AB4ABTS1A2k02A12A21x2HxS1n1L1c1p2SB3cnt1q2pw2AB1t1A2k02A12A21x2Hx1XS1n1L1c1TS1L4FSLOS1n1L1c1k2RB2k'1HSS3hAR2sp1h1n2SP1L1c1p1T3CTX2SB3TOP1r3cnt1q2pw2AB2UB3CHB2RB2ds2x02x12x22x32x43xs52bs3LXS2HL3LWS2KF3SUB3PGS3tf'3bs'3HL'S1L1x1j2DJ2MJS2kk3HkkS2sp2SP1L3TOP5TOPHIS1n1L1c1TS1n1c1p3cnt1q2Q03Q32S2sp2lo2SP1L5STKLO3SPLS1n1L1c1T4GC31S1h1L2c'1x2HxS1L1T2bl2j01XS1LS3hAR1n1L1c1p2SB4B6HI4SEHI1r3cnt4AUMU5MULIM1q2pw2AB6NEEDCS2RB4ABHI4RBHIS1n1c1p3CSR1r3cnt4AUMU5MULIM1q1k3HK23KCSS3hAR2sp1h1n2SP1L1c1p1T3CTX2SB3TOP1r3cnt1q2pw2AB2UB3CHB2RB2ds2x02x12x22x32x43xs52bs3LXS2HL3LWS2KF3SUB3PGS3tf'3bs'3HL'2l11z2l21ES3hAR2sp1h2lo2SP1L2SB4B6HI4SEHI5LOIMG2c'1A2k02A21x2Hx6MULIM'5RBHI'S3hAR2sp2lo2SP5LOIMG1A2k02H11x2Hx2A2S3hAR2sp2lo2SP1L1T3THI5LOIMG1A2k02A21x2HxS3hAR2sp2lo2SP5LOIMG1t1A2k02A21x2Hx2W2S1A2k03A631x2Hx2DAS1L1T2k'3BIG1H2shS2sp2SP1L3TOP3GTt1a2HaS1h1n1L1c2SB1r5MULIM2c'5MFAB'1x1j2DF2HJ2j'3Hj'2DU3MU'3MF'2E1S1L5CXLEN2E2S3hAR2sp1n2SP1L1c1l1T3CTX2SB1r3WCNSS1n1L1c1p2SB1r3cnt1q2pw2AB2RB4ABHIS1n1L1c1p2SB1r3cnt4AUMU1q2pw2AB2RB4ABHIS1L1T3CTX1XSS1h1L1x2qn2HxS1n1L1c1p2SB3cnt1q2pw2AB2UB3PGS1x2HxS1t1A2k02A12A21x2HxSS3hAR2sp1n2SP1L1c1p1T3CTX2SB1r3cnt1q2pw2AB2UB3CHBS3hAR2sp1n2SP1L1c1p1T3CTX2SB3TOP1r3cnt1q2pw2AB3CHB2RB2ds2x02x12x22x32x43xs52bs3LXS2HL3LWSS3hAR2sp1n2SP1L1T3CTX2SBS1L1x1j2DJ2MJS1x2HzS1x3OUT1HS3hAR1b3SB'S2sp2lo2SP1L5STKLO3SPL1HS1L3CTXS1n1L1c1TS1h1L1i2HiS1n1L1c1TS2k'2WNS1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB5SHRNG2c'1A2k02A11x2Hx5RBLO'S1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB5SHRNG1t1A2k02A12A21x2Hx2W6S1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB1A2k02AP1x2HxS1n1L1c1p2SB3cnt1q2pw2AB2UB3SUB5SHRNG1A2k02H11x2Hx2A2S1n1L1c1p1T2SB3cnt1q2pw2AB2UB2TB3SUB5SHRNG1A2k02A12A21x2HxS3hAR2sp1n2SP1L1T3CTX2SBS3hAR2sp1n2SP1L1c1p1T3CTX2SB3TOP1r3cnt1q2pw2AB3CHB2RB2ds2x02x12x22x32x43xs52bs3LXS2HL3LWS2KF3PGSSS3hAR2sp1n2SP1L1c1p1T3CTX2SB1r3cnt1q2pw2AB2UB3CHBS3hAR2sp1n2SP1L1c1p1T3CTX2SB3TOP1r3cnt1q2pw2AB3CHB2RB2ds2x02x12x22x32x43xs52bs3LXS2HL3LWSS1h1d3HFR2D0S1n1L1c1p2SB4SB163cnt1q2DMS1n1c1p3cnt1q2Q03Q32S2k'5RZk16S1n1L1c1p2SB1r3cnt1q2pw2AB2RB4ABMU4UBLESSS1n1cS1n1L1c1p2SB3cnt1q2pw2AB2RBS2shS1L2c'1x1j2DJ2MJS1n3RZB3N2BS1n3NF1S1n7NEEDPOSS1n1c4GC31S1n1L1c1p2SB1r3cnt1q2pw2AB3N2B2RB4ABMUS1n1L1c1p2SB3cnt1q2pw2AB2UB3SUBS1h2k03Hk0S1n1H2H0SS3tf'S1n1c1k2i'3IGTSSS1h1d3tf'3TFBS1L3CTX5CXLEN1bS1L1T3CTX5CXLENS2k02K0S1n1L1c1p2SB3cnt1q2pw2AB3RZB2RB4ABLO". (* [comment removed for export] *)
  #[using="IMG ALWF ASB"] Theorem hit_field : ltac2:(CDefT.buildp (gd_tbl_AHit ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(4;.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(16.(0.&8.))Pmo,$19.Ph,$1:.PLB,(1;.(2:.$1.$1.))PLF,(1;.(2:.$1.$1.))Pn,$1.Plo,$1.Pd,$1.P,(28.VhAR,R6.R5.R4.R8.)P,(2<.VhAR,VAL,R7.R8.)P,(2=.R:.R9.)P,(25.$22.R;.R5.(2.&40.R2;.))P,(5.(74.(2?.R:.))R6.)P,(5.R7.(10.(2.&40.R2=.)+1000.))P,(5.(2.&40.R2>.)(75.(2?.R<.)))P,(15.$1.(39.(2.&40.R2?.)+10.)=)P,(24.$22.R10.)P,(15.(0.&40.)R2?.(23.&40.$76.))P,(15.(0.&40.)R2:.(23.&40.R=.))P,(4.(5.=R>.)(6.R>.(=.+2.+1<.)))P,(5.(<.(30.R12.)(?.+2.R?.))$77.)P,(78.$22.R15.(74.(2?.R13.))(79.(2?.R13.))(2.&40.R2?.)(2.&40.R35.)R>.)P,(5.(<.(31.R14.)(<.R?.+3.))$7:.)P,P,(15.$52.(7;.R12.)$58.)(6.(7<.R15.)$7=.)P,(15.$52.(7>.R13.)$58.)P,(3.(15.(1;.$1.)(7?.(80.R17.(36.R14.)))(42.$1.)))(81.$22.(82.R3;.R3:.R39.R38.R34.R33.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1<.R1;.R18.R17.R16.R15.R14.R13.R1:.R19.)(1<.(1=.(1>.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R1<.(23.&40.$50.)R1;.(20.(0.&40.))R1:.(21.$22.))R19.))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n lo d
      HM0 HK0 HJ0 ST STKLO SPL SPTOP SPA MI TP A0 NB BUD CH0 HFR XC FP HIT.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ CH0) as D0.
    (* [comment removed for export] *)
    dpose HM0 as ((AWF & HLB) & GM & (GRO & GRW) & GT & GD & GC & GR & GQ & GS & GF & GI & GE).
    assert (XC' : win24 n = true -> cnt24 (AModel.blocks h) < C24MAX) by (rewrite <- HLB; exact XC).
    dpose AWF as ([WL WLS] & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    set (L := h_L h) in *. set (T := l_T L) in *. set (CTX := l_ctx L) in *. set (SB := l_sb L) in *.
    set (SP := bv_unsigned sp) in *.
    assert (ESP : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. pose proof ALWF as ALWF'. unfold al_wf in ALWF'.
    pose proof WL as WL'. unfold wf_L in WL'. fold L in WL'.
    aceilb. 
    (* [comment removed for export] *)
    pose proof FP as FP'. unfold from_primary, kMaxSize in FP'. apply Z.leb_le in FP'.
    assert (N2E : needed2 n = needed n) by (unfold needed2; rewrite FP; reflexivity).
    assert (NDB : 24 <= needed n <= 0x10000).
    { unfold needed, rounded, round_up in FP' |- *. pose proof (rz_size_bound n). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 H1 NB FP'. lia. }
    set (c := class_of (needed2 n)).
    assert (EC : pclass n = c) by (unfold pclass; subst c; rewrite N2E; reflexivity). rewrite EC in HIT.
    pose proof (class_of_range (needed2 n) ltac:(rewrite N2E; clear - NDB; lia)) as CR. fold c in CR.
    assert (GC31 : 1 <= c <= 31) by (clear - CR; lia).
    pose proof (class_size_range c GC31) as CSR. pose proof (max_count_range c GC31) as MCR. pose proof (class_size_mod16 c GC31) as CS16.
    set (p := h_cache h c) in *. set (r := h_reg h c) in *.
    pose proof (WC c ltac:(unfold kNumClasses; clear - GC31; lia)) as WCc. cbn zeta in WCc. fold p in WCc.
    ddestruct WCc as (WCI & _ & WCN & WC16 & WCQ).
    pose proof (WR c ltac:(unfold kNumClasses; clear - GC31; lia)) as WRc. cbn zeta in WRc. fold r in WRc.
    ddestruct WRc as (_ & AUMU & AUCS & MUAL & MULIM & MUAU & MFAL & MFAB & NF4 & FAQ & OWN & PART).
    assert (CINIT : h_cinit h = true).
    { destruct (h_cinit h); [reflexivity|]. exfalso. destruct WCI as [MX0 _]. unfold pc_count in WCN. rewrite MX0 in WCN.
      destruct (pc_chunks p); [exact (HIT eq_refl)| cbn in WCN; lia]. }
    rewrite CINIT in WCI. destruct (WCI ltac:(clear - GC31; lia)) as [PMAX PCSZ].
    set (cnt := pc_count p) in *.
    assert (HCNT : 1 <= cnt <= 16).
    { unfold pc_count in *. subst cnt. split; [| exact WC16]. destruct (pc_chunks p); [exact (False_ind _ (HIT eq_refl))| cbn; lia]. }
    set (q := nth (Z.to_nat (cnt - 1)) (pc_chunks p) 0).
    assert (HQ : In q (pc_chunks p)) by (subst q; apply nth_In; unfold pc_count in *; subst cnt; lia).
    pose proof (proj1 (Forall_forall _ _) WCQ q HQ) as (Q0 & k & HK1 & HK2).
    assert (KCS : k * class_size c + class_size c <= r_alloc_user r) by (rewrite AUCS; clear - HK1 CSR; nia).
    assert (Q32 : 16 * q < 2^32) by (unfold kUserLimit in MULIM; clear - KCS HK2 AUMU MULIM CSR; lia).
    set (pw := Z_to_bv 64 q).
    assert (PWQ : bv_unsigned pw mod 2^32 = q) by (subst pw; rewrite u64_lit by (clear - Q0 Q32; lia); apply Z.mod_small; clear - Q0 Q32; lia).
    set (AB := SB + c * 2^32 + 16 * (bv_unsigned pw mod 2^32)).
    assert (EAB : AB = chunk_at L c k) by (subst AB; rewrite PWQ; unfold chunk_at, region_beg, kRegionSize; fold SB; clear - HK2; lia).
    set (UB := AB + rz_size n). set (CHB := AB + rz_size n + -16).
    pose proof (rz_size_bound n) as RZB. pose proof (rz_size_mod16 n) as RZ16.
    assert (NEEDCS : needed2 n <= class_size c) by (rewrite N2E, <- EC; apply needed_le_class; [clear - NB; lia| exact FP]).
    assert (N2B : rz_size n + 8 <= needed2 n).
    { rewrite N2E. unfold needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 NB RZB. lia. }
    (* [comment removed for export] *)
    ddestruct WL' as (SB16 & B6A & B6B & B6AL & B6LO & B6HI & SEHI & TOPAL & TOP23 & TOPHI & STKLOE & S0TOP & HTOPLO & HTOPHI & HTOPAL & STKLO16 & STKLOC & STKHI47 & STKHIAL
                      & FSAL & FSLO & FSHI & TAL & TLO & THI & CXLO & CXHI & CXLEN & CXAL & PAAL & PALO & PAHI & NB0AL & SS0AL & EXTRA).
    fold SB T CTX in SB16, TAL, TLO, THI, CXLO, CXHI, CXAL. unfold kHighMemBeg in *. unfold space_end, kSpaceSize in SEHI. fold SB in SEHI.
    (* [comment removed for export] *)
    pose proof (lowhigh_Pimg _ _ TLO) as TI. pose proof (lowhigh_Pband _ _ TLO) as TB. pose proof (lowhigh_Pband _ _ CXLO) as CB. pose proof (lowhigh_big _ _ CXLO ltac:(clear; lia)) as CX63.
    set (TOP := l_top L) in *. set (RB := region_beg L c). assert (ERB : RB = SB + c * 2^32) by (subst RB; unfold region_beg, kRegionSize; fold SB; reflexivity).
    assert (ABLO : RB <= AB) by (rewrite EAB; unfold chunk_at; fold RB; clear - HK1 CSR; nia).
    assert (ABHI : AB + class_size c <= RB + r_alloc_user r) by (rewrite EAB; unfold chunk_at; fold RB; clear - KCS; lia).
    assert (SBLO : 0x10007fff8000 + 0x8000 <= SB) by (pose proof (Z.div_mod SB (2^16) ltac:(clear; lia)) as DQ; clear - B6A B6LO SB16 DQ; lia).   (* [comment removed for export] *)
    assert (RBLO : 0x10007fff8000 + 4096 + 2^32 <= RB) by (rewrite ERB; clear - SBLO GC31; nia).
    assert (RBHI : RB + 2^32 <= SB + 2^37) by (rewrite ERB; clear - GC31; nia).
    unfold kUserLimit in MULIM.
    assert (AB0 : 0x10007fff8000 <= AB) by (clear - ABLO RBLO; lia).
    assert (AB1 : AB + needed2 n <= ACEIL) by (clear - ABHI NEEDCS AUMU MULIM RBHI SEHI B6B B6HI; lia).
    assert (AB16 : AB mod 16 = 0).
    { subst AB. rewrite PWQ. pose proof (Z.div_mod SB (2^16) ltac:(lia)) as DM.
      replace (SB + c * 2^32 + 16 * q) with ((SB / 2^16 * 2^12 + c * 2^28 + q) * 16) by (clear - DM SB16; lia). apply Z_mod_mult. }
    (* [comment removed for export] *)
    assert (LOIMG : ACEIL <= lo) by (clear - STKLO STKLOC; lia).
    assert (TOP0 : 2^23 <= TOP) by exact TOP23.
    assert (TOP1 : TOP <= 2^47) by (clear - TOPHI STKHI47; lia).
    assert (TOP2 : SP + 16 <= 2^47) by (clear - SPTOP HTOPHI STKHI47; lia).
    assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia).
    (* [comment removed for export] *)
    assert (TC : T + 4096 <= CTX \/ CTX + 0x10000 <= T).
    { destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (tr_of_ctx h)) as [E|[X|X]].
      - exfalso. injection E as E1 E2. change (h_L h) with L in E2. clear - E2 CXLEN. lia.
      - left. unfold t_hi in X. cbn [t_lo t_len] in X. change (h_L h) with L in X. fold T CTX in X. clear - X CXLEN. lia.
      - right. unfold t_hi in X. cbn [t_lo t_len] in X. change (h_L h) with L in X. fold T CTX in X. clear - X CXLEN. lia. }
    assert (NUT : forall j, 0 <= j < r_mapped_user (h_reg h c) / kUserMapSize -> TR T 4096 KEager true true <> uunit_tr L c j) by (intros j _ E; discriminate E).
    assert (NUC : forall j, 0 <= j < r_mapped_user (h_reg h c) / kUserMapSize -> TR CTX (l_ctxlen L) KEager true true <> uunit_tr L c j) by (intros j _ E; discriminate E).
    assert (NEEDPOS : 0 < needed2 n) by (clear - N2B RZB; lia).
    assert (ABMU : AB + needed2 n <= RB + r_mapped_user r) by (clear - ABHI NEEDCS AUMU; lia).
    assert (CS0 : 0 < class_size c) by (clear - CSR; lia).
    assert (ABMU2 : AB + class_size c <= region_beg (h_L h) c + r_mapped_user (h_reg h c)) by (change (h_L h) with L; fold RB r; clear - ABHI AUMU; lia).
    assert (ABTS : AB + class_size c <= T \/ T + 4096 <= AB).
    { pose proof (tr_apart_user AL h mo _ c AB (class_size c) HK0 (tr_of_T h) GC31 MUAL NUT ABLO CS0 ABMU2) as X. unfold t_hi in X. cbn [t_lo t_len] in X. exact X. }
    assert (ABT : AB + needed2 n <= T \/ T + 4096 <= AB).
    { pose proof (tr_apart_user AL h mo _ c AB (needed2 n) HK0 (tr_of_T h) GC31 MUAL NUT ABLO NEEDPOS ABMU) as X. unfold t_hi in X. cbn [t_lo t_len] in X. exact X. }
    assert (ABC : AB + needed2 n <= CTX \/ CTX + 0x10000 <= AB).
    { pose proof (tr_apart_user AL h mo _ c AB (needed2 n) HK0 (tr_of_ctx h) GC31 MUAL NUC ABLO NEEDPOS ABMU) as X. unfold t_hi in X. cbn [t_lo t_len] in X. fold L in X. rewrite CXLEN in X. exact X. }
    set (nb := d_nb (h_dep h)). set (bl := d_bl (h_dep h)).
    assert (BLKn : forall k0, 0 <= k0 < Z.of_nat (length nb) -> In (node_tr (dblk nb k0)) (tr_of h)) by (intros k0 Hk0; apply tr_of_node; unfold dblk; apply nth_In; clear - Hk0; subst nb; lia).
    assert (BLKs : forall j0, 0 <= j0 < Z.of_nat (length bl) -> In (store_tr (sblk bl j0)) (tr_of h)) by (intros j0 Hj0; apply tr_of_store; unfold sblk; apply nth_In; clear - Hj0; subst bl; lia).
    assert (APTn : forall k0, 0 <= k0 < Z.of_nat (length nb) -> T + 4096 <= dblk nb k0 \/ dblk nb k0 + 2^20 <= T).
    { intros k0 Hk0. destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (BLKn k0 Hk0)) as [E|[X|X]]; [discriminate E| left| right]; unfold t_hi in X; cbn [t_lo t_len node_tr store_tr] in X; change (h_L h) with L in X; fold T in X; clear - X; lia. }
    assert (APTs : forall j0, 0 <= j0 < Z.of_nat (length bl) -> T + 4096 <= sblk bl j0 \/ sblk bl j0 + 2^23 <= T).
    { intros j0 Hj0. destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (BLKs j0 Hj0)) as [E|[X|X]]; [discriminate E| left| right]; unfold t_hi in X; cbn [t_lo t_len node_tr store_tr] in X; change (h_L h) with L in X; fold T in X; clear - X; lia. }
    assert (APCn : forall k0, 0 <= k0 < Z.of_nat (length nb) -> CTX + 0x10000 <= dblk nb k0 \/ dblk nb k0 + 2^20 <= CTX).
    { intros k0 Hk0. destruct (tr_apart AL h mo _ _ HK0 (tr_of_ctx h) (BLKn k0 Hk0)) as [E|[X|X]]; [exfalso; injection E as E1 E2; change (h_L h) with L in E2; clear - E2 CXLEN; lia| left| right];
        unfold t_hi in X; cbn [t_lo t_len node_tr store_tr] in X; change (h_L h) with L in X; fold CTX in X; clear - X CXLEN; lia. }
    assert (APCs : forall j0, 0 <= j0 < Z.of_nat (length bl) -> CTX + 0x10000 <= sblk bl j0 \/ sblk bl j0 + 2^23 <= CTX).
    { intros j0 Hj0. destruct (tr_apart AL h mo _ _ HK0 (tr_of_ctx h) (BLKs j0 Hj0)) as [E|[X|X]]; [discriminate E| left| right];
        unfold t_hi in X; cbn [t_lo t_len node_tr store_tr] in X; change (h_L h) with L in X; fold CTX in X; clear - X CXLEN; lia. }
    assert (APAn : forall k0, 0 <= k0 < Z.of_nat (length nb) -> AB + needed2 n <= dblk nb k0 \/ dblk nb k0 + 2^20 <= AB).
    { intros k0 Hk0. pose proof (tr_apart_user AL h mo _ c AB (needed2 n) HK0 (BLKn k0 Hk0) GC31 MUAL ltac:(intros j _ E; discriminate E) ABLO NEEDPOS ABMU) as X.
      unfold t_hi in X. cbn [t_lo t_len node_tr] in X. exact X. }
    assert (APAs : forall j0, 0 <= j0 < Z.of_nat (length bl) -> AB + needed2 n <= sblk bl j0 \/ sblk bl j0 + 2^23 <= AB).
    { intros j0 Hj0. pose proof (tr_apart_user AL h mo _ c AB (needed2 n) HK0 (BLKs j0 Hj0) GC31 MUAL ltac:(intros j _ E; discriminate E) ABLO NEEDPOS ABMU) as X.
      unfold t_hi in X. cbn [t_lo t_len store_tr] in X. exact X. }
    (* [comment removed for export] *)
    dpose GRO as (MS8 & AS & PS & FS & DST & THRS & LGS & GPG & PGSZ & GCF & DEC & LIM & I40 & I56 & SBC & RIC & PPART & MH8 & QMX & MRN & TIDC & TH & THR & TSW & TFS & F88 & UARG & UARC & RSMR & SMS & F5W & T48 & MICF & MICR & B12S).
    fold L T CTX SB TOP in MS8, AS, SBC, TIDC, TH, THR, TSW, TFS.
    dpose FS as (_ & _ & _ & _ & GOTFL & _).
    dpose GT as (UNW & (ds & PCL) & _ & (xs & bs & STX & LXS & STB & HL)). fold L T in UNW, PCL, STX, STB.
    (* [comment removed for export] *)
    destruct xs as [|x0 xs]; [cbn in LXS; discriminate|]. destruct xs as [|x1 xs]; [cbn in LXS; discriminate|]. destruct xs as [|x2 xs]; [cbn in LXS; discriminate|].
    destruct xs as [|x3 xs]; [cbn in LXS; discriminate|]. destruct xs as [|x4 xs5]; [cbn in LXS; discriminate|].
    pose proof (u64arr_cells m _ _ STX) as STX'. cbn [map] in STX'.
    change (C8 x0 :: C8 x1 :: C8 x2 :: C8 x3 :: C8 x4 :: map C8 xs5) with ([C8 x0] ++ [C8 x1] ++ [C8 x2; C8 x3; C8 x4] ++ map C8 xs5) in STX'.
    apply rw_cells_app in STX' as [STC STX']. apply rw_cells_app in STX' as [_ STX']. apply rw_cells_app in STX' as [STH _].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length map app] in STC, STH.
    match type of STH with rw_cells _ _ ?a _ => replace a with (T + 2800) in STH by (clear; lia) end.
    set (stw := x0) in STC. set (j0 := x2) in STH. set (j1 := x3) in STH. set (j2 := x4) in STH.
    ddestruct (PCL c GC31) as (PC & ARR & LWS & FIRSTN & _). fold p in PC, FIRSTN. rewrite PMAX, PCSZ in PC. fold cnt in PC.
    assert (NTH : nth_error (ds c) (Z.to_nat (cnt - 1)) = Some pw).
    { subst pw q. apply nth_error_firstn_map; [exact FIRSTN| unfold pc_count in *; subst cnt; clear - HCNT; lia]. }
    pose proof (GR c GC31) as GRc. unfold hm_region in GRc. cbn zeta in GRc. fold L r in GRc.
    ddestruct GRc as (RMX & RNF & RMFA & RAU & R40 & RMU & R56 & (exb0 & R68) & R72 & R80 & RFA & RJS & WRU & SHT & SHF).
    dpose GM as (SHLO & SHHI & STKW & TW & CTXW & FSW). fold L in SHLO, SHHI, STKW, TW, CTXW, FSW.
    (* [comment removed for export] *)
    assert (UBLE : UB + nfix n <= AB + needed2 n).
    { subst UB. rewrite N2E. unfold needed, rounded, round_up, nfix. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 NB. lia. }
    assert (NF1 : 1 <= nfix n <= needed2 n) by (unfold nfix in *; clear - UBLE NB RZB; subst UB; lia).
    assert (WSUB : forall A k0, RB <= A -> 0 <= k0 -> A + k0 <= RB + r_mapped_user r -> wr_at asegs m A k0).
    { intros A k0 H1 H2 H3. pose proof (wr_at_sub m RB _ (A - RB) k0 WRU ltac:(clear - H1; lia) H2 ltac:(clear - H3; lia)) as W.
      replace (RB + (A - RB)) with A in W by (clear; lia). exact W. }
    ddestruct (wr_at_high_hdr m CHB ltac:(apply WSUB; subst CHB UB; clear - ABLO ABMU RZB N2B; lia) ltac:(subst CHB; clear - AB0 RZB; lia)) as (b0 & b1 & w2 & w4 & w8 & HDR).
    ddestruct (wr_at_high_C8C8 m AB ltac:(apply WSUB; clear - ABLO ABMU N2B RZB; lia) ltac:(clear - AB0; lia)) as (mg0 & mg1 & MG).
    set (KF := Z.min (nfix n) 4096).
    destruct (wr_at_high_CB m UB KF ltac:(apply WSUB; subst KF UB; clear - ABLO ABMU RZB UBLE NF1; lia) ltac:(subst UB; clear - AB0 RZB; lia) ltac:(subst KF; clear - NF1; lia)) as (uj & UC).
    pose proof (SHF k ltac:(clear - HK1; unfold carved in HK1; fold r in HK1; exact HK1)) as SHC. rewrite <- EAB in SHC.
    set (SUB := 0x7fff8000 + UB / 8). set (PGS := 0x7fff8000 + Z.shiftr (UB + nfix n / 8 * 8) 3).
    assert (SHRNG : 0x2008fff7000 <= SUB /\ SUB + nfix n / 8 + 1 <= 0x2008fff7000 + 0xdfff0001000).
    { subst SUB UB. pose proof (Z.div_mod (AB + rz_size n) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (AB + rz_size n) 8 ltac:(clear; lia)).
      pose proof (Z.div_le_mono (nfix n) (needed2 n) 8 ltac:(lia) ltac:(clear - NF1; lia)). clear - H H0 H1 AB0 AB1 RZB UBLE NF1. lia. }
    assert (NF8 : 0 <= nfix n / 8) by (apply Z.div_pos; clear - NF1; lia).
    assert (SSUB : forall A k0, 0x2008fff7000 <= A -> 0 <= k0 -> A + k0 <= 0x2008fff7000 + 0xdfff0001000 -> wr_at asegs m A k0).
    { intros A k0 H1 H2 H3. pose proof (wr_at_sub m 0x2008fff7000 _ (A - 0x2008fff7000) k0 SHHI ltac:(clear - H1; lia) H2 ltac:(clear - H3; lia)) as W.
      replace (0x2008fff7000 + (A - 0x2008fff7000)) with A in W by (clear; lia). exact W. }
    destruct (wr_at_high_CB m SUB (nfix n / 8) ltac:(apply SSUB; clear - SHRNG NF8; lia) ltac:(clear - SHRNG; lia) NF8) as (sj & SH).
    assert (UB16 : UB mod 16 = 0).
    { subst UB. pose proof (Z.div_mod AB 16 ltac:(clear; lia)) as D1. pose proof (Z.div_mod (rz_size n) 16 ltac:(clear; lia)) as D2.
      replace (AB + rz_size n) with ((AB / 16 + rz_size n / 16) * 16) by (clear - D1 D2 AB16 RZ16; lia). apply Z_mod_mult. }
    assert (EPGS : PGS = SUB + nfix n / 8).
    { subst PGS SUB. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. rewrite Z_div_plus by (clear; lia). clear; lia. }
    assert (PW : wr_at asegs m PGS 1) by (rewrite EPGS; apply SSUB; clear - SHRNG NF8; lia).
    assert (P68 : 0x65f000 <= PGS) by (rewrite EPGS; clear - SHRNG NF8; lia).
    destruct (wr_at_high_C1 m PGS PW P68) as (pgb & PGC). clear PW P68.
    (* [comment removed for export] *)
    assert (STT : stk asegs m SP TOP).
    { destruct (Z.le_gt_cases SP TOP) as [LEt|GTt].
      - apply wr_at_high_stk; [| clear - LOIMG SPL; lia| exact LEt].
        pose proof (wr_at_sub m (l_stk_lo L) _ (SP - l_stk_lo L) (TOP - SP) STKW ltac:(clear - STKLO SPL; lia) ltac:(clear - LEt; lia) ltac:(clear - TOPHI; lia)) as W.
        replace (l_stk_lo L + (SP - l_stk_lo L)) with SP in W by (clear; lia). exact W.
      - (* [comment removed for export] *)
        split; [clear - LOIMG SPL; lia|]. split; [clear - TOP1; lia|]. intros a Ha. exfalso. clear - Ha GTt. lia. }
    pose proof HK0 as [HKV VR0]. set (v0 := vst_of h) in *.
    pose proof (HK_vwf AL h mo HK0) as VWF0. fold v0 in VWF0.
    assert (SLACK : v_eb v0 + 4096 * vnb v0 + RES_DEPOT <= VLIMIT).
    { pose proof (vst_budget h AWF) as B. fold v0 in B. pose proof abs_fits as AF. unfold RES_DEPOT, VLIMIT. unfold AVOL_MAX in *. clear - B AF BUD NB. lia. }
    assert (HVM : h_havol h <= AVOL_MAX) by (clear - BUD NB; lia).
    pose proof (vst_cb20 h AWF HVM) as CB20. pose proof (vst_cb23 h AWF HVM) as CB23. fold v0 in CB20, CB23.
    assert (CB20' : v_cb20 v0 < J20) by (clear - CB20; lia).
    assert (CB23' : v_cb23 v0 + (2^20 / 2^23 + 2) < J23) by (change (2^20 / 2^23 + 2) with 2; clear - CB23; lia).
    assert (CSI : forall x, vcs AL v0 x -> CSd AL v0 nb bl nb bl x) by (intros x Hx; apply (proj2 (CSd_v0 AL v0 nb bl x)); exact Hx).
    assert (CRI : forall a k0, crange (vcs AL v0) a k0 -> crange (CSd AL v0 nb bl nb bl) a k0) by (intros a k0 H x Hx; apply CSI, H, Hx).
    pose proof (D_CSOK AL ALWF ASB IML IMH GOT64 GSB64 v0 nb bl VWF0 nb bl) as CSOK0.
    (* [comment removed for export] *)
    subst a0. rewrite ESP. rewrite TP.
    eapply (evtA_aevtS_KJ AL (CSd AL v0 nb bl nb bl) (KdF v0 nb bl mo nb bl)).
    { exact (F_KL v0 nb bl mo VR0 nb bl). }
    { split; [left; split; [reflexivity| split; [reflexivity| exact HKV]]| apply mo_frame_refl]. }
    { exact HJ0. }
    { apply wrap_step. exact CSOK0. }
    cbn beta. intros ms1 mo1 -> K1 MM1 HJ1. cbn [ms_mem MS MSsvc] in HJ1.
    assert (CH1 : uwc asegs m (l_stk_lo L) (l_stk_hi L) (bv_unsigned s0) SP d) by (change (h_L h) with L in CH0; fold SP in CH0; exact CH0).
    eapply aevtS_mono.
    { eapply (malloc_hit_F v0 nb bl mo VR0 VWF0 SLACK CB20' CB23' SP n lo T CTX TOP 0 SB cnt (class_size c) pw) with (LO := l_stk_lo L) (TOPU := l_stk_hi L) (d := d).
      { clear - NB; lia. } { exact FP. } { exact LOIMG. } { exact SPL. } { exact SPA. } { exact TOP0. } { exact TOP1. } { exact TOP2. }
      { exact (lowhigh_Pimg _ _ TLO). } { exact THI. } { exact TAL. } { exact (lowhigh_big _ _ CXLO ltac:(clear; lia)). } { clear - CXHI CXLEN; lia. } { exact TC. } { clear; lia. }
      { clear - B6A B6LO; lia. } { clear - SEHI B6B B6HI; lia. }
      { pose proof (Z.div_mod SB (2^16) ltac:(clear; lia)) as DM. replace SB with ((SB / 2^16 * 16) * 4096) by (clear - DM SB16; lia). apply Z_mod_mult. }
      { exact HCNT. } { clear - CSR; lia. } { clear - AB0; lia. } { exact AB1. } { exact ABT. } { exact ABC. } { right; exact AB0. } { pose proof (lowhigh_Pband _ _ TLO) as TB'; clear - TB'; lia. } { pose proof (lowhigh_Pband _ _ CXLO) as CB'; clear - CB'; lia. }
      { clear - STKLO SPL; lia. } { clear - TOPHI STKHI47; lia. }
      { exact CH1. }
      { exact MS8. } { exact AS. } { exact PS. } { exact FS. } { exact GOTFL. } { exact PPART. } { exact SBC. } { exact THR. } { exact TSW. } { exact UNW. } { exact TH. } { exact TIDC. }
      { apply CRI. apply crange_T. } { apply CRI. rewrite <- CXLEN. apply crange_ctx. }
      { exact LWS. } { exact NTH. } { exact PC. } { exact ARR. } { exact STC. } { exact STH. } { exact STB. } { exact HL. }
      { apply CRI. apply (crange_user AL h c); [exact GC31| exact MUAL| exact ABLO| clear - NEEDPOS; lia| exact ABMU]. }
      { exact HDR. } { intros _. exact MG. } { exact UC. }
      { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. destruct SHC as [RO _]. exact RO. } { clear. vm_compute. lia. }
      { exact SH. } { exact PGC. }
      { exact APTn. } { exact APTs. } { exact APCn. } { exact APCs. } { exact APAn. } { exact APAs. }
      { exact GD. }
      { split; [intros k0 Hk0; apply CRI; apply crange_node; exact Hk0| intros jj Hjj; apply CRI; apply crange_store; exact Hjj]. }
      { exact DST. }
      { apply (proj2 (wf_depot'_bounds h WD ltac:(clear - HFR D0; lia))). }
      { apply (proj1 (wf_depot'_bounds h WD ltac:(clear - HFR D0; lia))). }
      { exact STT. }
      { apply CRI. apply crange_stack; change (h_L h) with L; [| clear - TOPHI; lia]. unfold stk64. pose proof (Z.mod_pos_bound (l_stk_lo L) 64 ltac:(clear; lia)). clear - H STKLO SPL; lia. }
      { exact ST. }
      { apply CRI. apply crange_stack; change (h_L h) with L; [| clear - TOPHI SPTOP HTOPHI SPL; lia]. unfold stk64. pose proof (Z.mod_pos_bound (l_stk_lo L) 64 ltac:(clear; lia)). clear - H STKLO; lia. }
      { exact MI. } { exact K1. } { exact HJ1. }
      { split; reflexivity. } { split; [reflexivity| left; reflexivity]. } { intros x. split; [reflexivity| right; exists x; reflexivity]. } }
    (* [comment removed for export] *)
    cbn beta. intros cf PO.
    ddestruct PO as (ms' & mo' & nb' & bl' & N' & tf' & id & y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & b1' & stw' & j0' & j1' & j2' & bs' & m'
                    & -> & -> & [KD FRM] & HJ' & DI' & DCS' & DST' & IDB & NB' & TFB & POT & CSM & (sn & sb & -> & -> & APn & APs) & KEEP & WM' & MI' & ST'
                    & HDR' & B13 & B1R & MG' & SUB' & PGS' & UBF & PC' & ARR' & STC' & STH' & STB' & HL' & UNW').
    fold KF SUB PGS UB CHB in KEEP, HDR', MG', SUB', PGS', UBF. fold UB in SUB, PGS, CHB.
    (* [comment removed for export] *)
    set (newk := CK AB n true c CHUNK_ALLOCATED).
    set (h' := pop_h h c n AB N' tf' (nb ++ sn) (bl ++ sb)).
    assert (DG : dgrow h sn sb h') by (repeat split; reflexivity).
    (* [comment removed for export] *)
    dpose WK as (WKF & WKND & WKSEC).
    assert (QIN : In q (cache_set h c)) by (unfold cache_set; fold p; exact HQ).
    assert (CSD : class_size c / 16 * 16 = class_size c) by (pose proof (Z.div_mod (class_size c) 16 ltac:(clear; lia)); clear - H CS16; lia).
    assert (OLDAP : Forall (fun k' => ck_end k' <= AB \/ AB + class_size c <= (if ck_prim k' then ck_ab k' else ck_map_beg k')) (h_chunks h)).
    { apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (WN & WST & WP & WCX). unfold ck_end.
      destruct (ck_prim k') eqn:PR.
      - ddestruct WCX as (WCLS & WC30 & i' & Hi' & EAB'). rewrite EAB'.
        destruct (Z.eq_dec (ck_cls k') c) as [EQC|NEC].
        + (* [comment removed for export] *)
          rewrite EQC in *. assert (NEI : i' <> k).
          { intros ->. apply (owned_cache_not_chunk h c q OWN QIN). rewrite <- (compact_chunk_at L c k CS16) in |- * || idtac.
            replace q with (compact L c (ck_ab k')); [apply in_chunk_set; [exact Hk'| exact PR| exact EQC]|].
            rewrite EAB', compact_chunk_at by exact CS16. clear - HK2 CSD CSR. nia. }
          rewrite EAB. unfold chunk_at. destruct (proj1 (Z.lt_gt_cases i' k) NEI) as [ILT|IGT].
          * left. assert ((i' + 1) * class_size c <= k * class_size c) by (apply Z.mul_le_mono_nonneg_r; clear - ILT CSR; lia). change (h_L h) with L. clear - H. lia.
          * right. assert ((k + 1) * class_size c <= i' * class_size c) by (apply Z.mul_le_mono_nonneg_r; clear - IGT CSR; lia). change (h_L h) with L. clear - H. lia.
        + (* [comment removed for export] *)
          pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear - WC30; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & AUCS' & _ & MULIM' & _).
          unfold carved in Hi'. unfold kUserLimit in MULIM'.
          assert ((i' + 1) * class_size (ck_cls k') <= r_alloc_user (h_reg h (ck_cls k'))).
          { rewrite AUCS'. pose proof (class_size_range (ck_cls k') ltac:(clear - WC30; lia)). clear - Hi' H AUCS'. rewrite AUCS' in Hi'. rewrite Z.mul_comm in Hi'. rewrite Z.div_mul in Hi' by lia. nia. }
          rewrite EAB. unfold chunk_at, region_beg, kRegionSize. change (h_L h) with L. fold SB.
          pose proof (class_size_range (ck_cls k') ltac:(clear - WC30; lia)). clear - NEC H H0 AUMU' MULIM' Hi' HK1 KCS AUMU MULIM CSR GC31 WC30. nia.
      - (* [comment removed for export] *)
        ddestruct WCX as (i' & NTH' & _). assert (HIN : In (AModel.SH (ck_map_beg k') (ck_map_size k') (needed2 (ck_n k'))) (s_chunks (h_sec h))) by (eapply nth_error_In; exact NTH').
        assert (NEU : forall j, 0 <= j < r_mapped_user (h_reg h c) / kUserMapSize -> sec_tr (AModel.SH (ck_map_beg k') (ck_map_size k') (needed2 (ck_n k'))) <> uunit_tr (h_L h) c j) by (intros j _ E; discriminate E).
        pose proof (tr_apart_user AL h mo _ c AB (class_size c) HK0 (tr_of_sec h _ HIN) GC31 MUAL NEU ABLO CS0 ABMU2) as X.
        unfold t_hi, sec_tr in X. cbn [t_lo t_len s_map_beg s_map_size] in X. clear - X. lia. }
    assert (EUB : ck_user newk = UB) by reflexivity.
    unfold hit_fpost. assert (USP : bv_unsigned (Z_to_bv 64 SP) = SP) by (subst SP; rewrite Z_to_bv_bv_unsigned; reflexivity). rewrite !USP.
    dexists y0, y1, y2, (Z_to_bv 64 UB), ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m', mo', h', UB.
    (* [comment removed for export] *)
    assert (WRU' : wr_at asegs m' UB n).
    { eapply wr_at_transport; [| exact WM']. apply WSUB; subst UB; [clear - ABLO RZB; lia| clear - NB; lia| clear - ABMU UBLE NF1 NB; unfold nfix in *; lia]. }
    destruct (wr_at_high_CB m' UB n WRU' ltac:(subst UB; clear - AB0 RZB; lia) ltac:(clear - NB; lia)) as (junk & JUNK).
    exists junk.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FRM|]. split; [exact WM'|].
    (* [comment removed for export] *)
    assert (SNB : forall (l1 l2 : list Z), l1 ++ l2 = l1 -> l2 = []) by (intros l1 l2 E; apply (f_equal (@length Z)) in E; rewrite length_app in E; destruct l2; [reflexivity| cbn in E; lia]).
    assert (SNC : forall (l1 l2 : list Z) x, l1 ++ l2 = l1 ++ [x] -> l2 = [x]) by (intros l1 l2 x E; apply app_inv_head in E; exact E).
    assert (SANE : Forall (sane (2^20)) sn /\ Forall (sane (2^23)) sb).
    { ddestruct (Kd_cases AL v0 nb bl (nb ++ sn) (bl ++ sb) mo' KD) as (v & _ & _ & CASE).
      destruct CASE as [(E1 & E2 & _)|[(a & E1 & E2 & SA & _)|[(b & E1 & E2 & SB' & _)|(a & b & E1 & E2 & SA & SB' & _)]]];
        first [apply SNB in E1 | apply SNC in E1]; first [apply SNB in E2 | apply SNC in E2]; subst sn sb; (split; [try apply Forall_nil; try (constructor; [assumption| apply Forall_nil]) | try apply Forall_nil; try (constructor; [assumption| apply Forall_nil])]). }
    destruct SANE as [SANEn SANEs].
    dpose DI' as (_ & _ & (_ & NBWF & _) & _ & _ & _ & _ & (_ & BLWF & _) & _).
    assert (NBLO : forall b, In b (nb ++ sn) -> 0x65f000 <= b) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) NBWF b Hb) as X; cbn beta in X; clear - X; lia).
    assert (BLLO : forall b, In b (bl ++ sb) -> 0x65f000 <= b) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) BLWF b Hb) as X; cbn beta in X; clear - X; lia).
    (* [comment removed for export] *)
    assert (OBn : forall t b a k0, In t (tr_of h) -> In b nb -> t <> node_tr b -> t_lo t <= a -> a + k0 <= t_hi t -> a + k0 <= b \/ b + 2^20 <= a).
    { intros t b a k0 Ht Hb NE A1 A2. destruct (tr_apart AL h mo t (node_tr b) HK0 Ht (tr_of_node h b Hb)) as [E|[X|X]]; [exact (False_ind _ (NE E))| |];
        unfold t_hi, node_tr in *; cbn [t_lo t_len] in X; clear - X A1 A2; lia. }
    assert (OBs : forall t b a k0, In t (tr_of h) -> In b bl -> t <> store_tr b -> t_lo t <= a -> a + k0 <= t_hi t -> a + k0 <= b \/ b + 2^23 <= a).
    { intros t b a k0 Ht Hb NE A1 A2. destruct (tr_apart AL h mo t (store_tr b) HK0 Ht (tr_of_store h b Hb)) as [E|[X|X]]; [exact (False_ind _ (NE E))| |];
        unfold t_hi, store_tr in *; cbn [t_lo t_len] in X; clear - X A1 A2; lia. }
    assert (NBn : forall b x, In b sn -> vcs AL v0 x -> ~ (b <= x < b + 2^20)) by (intros b x Hb Hx; pose proof (proj1 (Forall_forall _ _) APn b Hb) as X; cbn beta in X; apply X; apply CSI; exact Hx).
    assert (NBs : forall b x, In b sb -> vcs AL v0 x -> ~ (b <= x < b + 2^23)) by (intros b x Hb Hx; pose proof (proj1 (Forall_forall _ _) APs b Hb) as X; cbn beta in X; apply X; apply CSI; exact Hx).
    assert (SHn : forall b, In b sn -> 0x10007fff8000 <= b \/ b + 2^20 <= 0x7fff7000) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) SANEn b Hb) as SA; cbn beta in SA; unfold sane in SA; clear - SA; lia).
    assert (SHs : forall b, In b sb -> 0x10007fff8000 <= b \/ b + 2^23 <= 0x7fff7000) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) SANEs b Hb) as SA; cbn beta in SA; unfold sane in SA; clear - SA; lia).
    (* [comment removed for export] *)
    assert (KEEPI : forall x : word, let a := bv_unsigned x in
              ~ (lo <= a < SP) -> ~ (A_SS <= a < A_DEP_END) ->
              (forall b, In b (nb ++ sn) -> ~ (b <= a < b + 2^20)) -> (forall b, In b (bl ++ sb) -> ~ (b <= a < b + 2^23)) ->
              ~ (T + 208 + 80 * c <= a < T + 208 + 80 * c + 4) -> ~ (T + 2784 <= a < T + 2792) -> ~ (T + 2800 <= a < T + 3169) ->
              ~ (AB <= a < AB + class_size c) -> ~ (SUB <= a < SUB + nfix n / 8 + 1) -> m' x = m x).
    { intros x. cbn zeta. intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9. apply KEEP; try assumption.
      - intros k0 Hk0. apply Q3. unfold dblk. apply nth_In. clear - Hk0. lia.
      - intros jj Hjj. apply Q4. unfold sblk. apply nth_In. clear - Hjj. lia.
      - subst CHB UB. clear - Q8 RZB N2B NEEDCS. lia.
      - clear - Q8 CSR RZB N2B NEEDCS. lia.
      - subst SUB. clear - Q9 NF8. lia.
      - subst PGS SUB UB. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. rewrite Z_div_plus by (clear; lia). clear - Q9 NF8. lia.
      - subst KF UB. clear - Q8 RZB NF1 UBLE NEEDCS. lia. }
    (* [comment removed for export] *)
    assert (KI : forall A k0, 0x10000 <= A -> A + k0 <= 0x65f000 -> (A + k0 <= A_SS \/ A_DEP_END <= A) -> kept m m' A k0).   (* [comment removed for export] *)
    { intros A k0 H0 H1 H2 x Hx. apply KEEPI; unfold A_SS, A_DEP_END in *.
      - clear - Hx H1 LOIMG. lia. - clear - Hx H2. lia.
      - intros b Hb. pose proof (NBLO b Hb). clear - H Hx H1. lia. - intros b Hb. pose proof (BLLO b Hb). clear - H Hx H1. lia.
      - clear - Hx H0 H1 TI GC31; lia. - clear - Hx H0 H1 TI; lia. - clear - Hx H0 H1 TI; lia. - clear - Hx H1 AB0; lia. - clear - Hx H1 SHRNG; lia. }
    (* [comment removed for export] *)
    assert (KT : forall t A k0, In t (tr_of h) -> t_cs t = true -> t <> TR T 4096 KEager true true ->
              (forall j, 0 <= j < r_mapped_user (h_reg h c) / kUserMapSize -> t <> uunit_tr L c j) ->
              (forall b, In b nb -> t <> node_tr b) -> (forall b, In b bl -> t <> store_tr b) ->
              t_lo t <= A -> A + k0 <= t_hi t -> 0 < k0 -> kept m m' A k0).
    { intros t A k0 Ht TCS NT NU NN NS A1 A2 K0 x Hx. dpose (tr_wf AL h mo t HK0 Ht) as (W0 & W1 & W2 & W3 & W4 & W5 & W6). specialize (W6 TCS). rewrite IMH, IMLO in W5. 
      assert (XCS : vcs AL v0 (bv_unsigned x)) by (subst v0; eapply vcs_of_tr; [exact Ht| exact TCS| unfold t_hi in *; clear - Hx A1 A2; lia]).
      apply KEEPI.
      - unfold t_hi in *. clear - Hx A1 A2 W2 LOIMG. lia. - unfold A_SS, A_DEP_END, t_hi in *. clear - Hx A1 A2 W5. lia.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (NBn b _ Hb XCS)]. pose proof (OBn t b A k0 Ht Hb (NN b Hb) A1 A2). clear - H Hx. lia.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (NBs b _ Hb XCS)]. pose proof (OBs t b A k0 Ht Hb (NS b Hb) A1 A2). clear - H Hx. lia.
      - destruct (tr_apart AL h mo t _ HK0 Ht (tr_of_T h)) as [E|[X|X]]; [exact (False_ind _ (NT E))| |]; unfold t_hi in *; cbn [t_lo t_len] in X; change (h_L h) with L in X; fold T in X; clear - X Hx A1 A2 GC31; lia.
      - destruct (tr_apart AL h mo t _ HK0 Ht (tr_of_T h)) as [E|[X|X]]; [exact (False_ind _ (NT E))| |]; unfold t_hi in *; cbn [t_lo t_len] in X; change (h_L h) with L in X; fold T in X; clear - X Hx A1 A2; lia.
      - destruct (tr_apart AL h mo t _ HK0 Ht (tr_of_T h)) as [E|[X|X]]; [exact (False_ind _ (NT E))| |]; unfold t_hi in *; cbn [t_lo t_len] in X; change (h_L h) with L in X; fold T in X; clear - X Hx A1 A2; lia.
      - pose proof (tr_apart_user AL h mo t c AB (class_size c) HK0 Ht GC31 MUAL NU ABLO CS0 ABMU2) as X. unfold t_hi in *. clear - X Hx A1 A2. lia.
      - unfold t_hi in *. clear - Hx A1 A2 W6 SHRNG. lia. }
    (* [comment removed for export] *)
    assert (KTP : forall A k0, T <= A -> A + k0 <= T + 4096 -> 0 < k0 ->
              (A + k0 <= T + 208 + 80 * c \/ T + 208 + 80 * c + 4 <= A) -> (A + k0 <= T + 2784 \/ T + 2792 <= A) -> (A + k0 <= T + 2800 \/ T + 3169 <= A) -> kept m m' A k0).
    { intros A k0 A1 A2 K0 W1 W2 W3 x Hx.
      assert (XCS : vcs AL v0 (bv_unsigned x)) by (subst v0; eapply vcs_of_tr; [exact (tr_of_T h)| reflexivity| unfold t_hi; cbn [t_lo t_len]; change (h_L h) with L; fold T; clear - Hx A1 A2; lia]).
      apply KEEPI.
      - clear - Hx A1 A2 THI LOIMG. lia. - unfold A_SS, A_DEP_END. clear - Hx A1 A2 TI. lia.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (NBn b _ Hb XCS)].
        pose proof (OBn _ b A k0 (tr_of_T h) Hb ltac:(intros E; discriminate E) ltac:(cbn [t_lo]; change (h_L h) with L; fold T; clear - A1; lia) ltac:(unfold t_hi; cbn [t_lo t_len]; change (h_L h) with L; fold T; clear - A2; lia)). clear - H Hx. lia.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (NBs b _ Hb XCS)].
        pose proof (OBs _ b A k0 (tr_of_T h) Hb ltac:(intros E; discriminate E) ltac:(cbn [t_lo]; change (h_L h) with L; fold T; clear - A1; lia) ltac:(unfold t_hi; cbn [t_lo t_len]; change (h_L h) with L; fold T; clear - A2; lia)). clear - H Hx. lia.
      - clear - Hx W1. lia. - clear - Hx W2. lia. - clear - Hx W3. lia.
      - clear - Hx A1 A2 ABTS. lia. - clear - Hx A1 A2 TB SHRNG. lia. }
    (* [comment removed for export] *)
    assert (KU : forall c' A k0, 1 <= c' <= 31 -> region_beg L c' <= A -> A + k0 <= region_beg L c' + r_mapped_user (h_reg h c') -> 0 < k0 ->
              (A + k0 <= AB \/ AB + class_size c <= A) -> kept m m' A k0).
    { intros c' A k0 Hc' A1 A2 K0 AP x Hx.
      pose proof (WR c' ltac:(unfold kNumClasses; clear - Hc'; lia)) as WRc'. cbn zeta in WRc'. ddestruct WRc' as (_ & AUMU' & _ & MUAL' & MULIM' & _).
      assert (XCS : vcs AL v0 (bv_unsigned x)) by (subst v0; eapply (crange_user AL h c' A k0); [exact Hc'| exact MUAL'| exact A1| clear - K0; lia| exact A2| exact Hx]).
      assert (RBLO' : 0x10007fff8000 + 4096 + 2^32 <= region_beg L c') by (unfold region_beg, kRegionSize; fold SB; clear - SBLO Hc'; nia).
      assert (RBHI' : region_beg L c' + 2^32 <= SB + 2^37) by (unfold region_beg, kRegionSize; fold SB; clear - Hc'; nia).
      unfold kUserLimit in MULIM'.
      assert (NUT' : forall j, 0 <= j < r_mapped_user (h_reg h c') / kUserMapSize -> TR T 4096 KEager true true <> uunit_tr L c' j) by (intros j _ E; discriminate E).
      apply KEEPI.
      - clear - Hx A1 A2 RBHI' MULIM' SEHI B6B B6HI LOIMG. lia. - unfold A_SS, A_DEP_END. clear - Hx A1 RBLO'. lia.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (NBn b _ Hb XCS)].
        pose proof (tr_apart_user AL h mo _ c' A k0 HK0 (tr_of_node h b Hb) Hc' MUAL' ltac:(intros j _ E; discriminate E) A1 K0 A2) as X. unfold t_hi, node_tr in X. cbn [t_lo t_len] in X. clear - X Hx. lia.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (NBs b _ Hb XCS)].
        pose proof (tr_apart_user AL h mo _ c' A k0 HK0 (tr_of_store h b Hb) Hc' MUAL' ltac:(intros j _ E; discriminate E) A1 K0 A2) as X. unfold t_hi, store_tr in X. cbn [t_lo t_len] in X. clear - X Hx. lia.
      - pose proof (tr_apart_user AL h mo _ c' A k0 HK0 (tr_of_T h) Hc' MUAL' NUT' A1 K0 A2) as X. unfold t_hi in X. cbn [t_lo t_len] in X. change (h_L h) with L in X. fold T in X. clear - X Hx GC31. lia.
      - pose proof (tr_apart_user AL h mo _ c' A k0 HK0 (tr_of_T h) Hc' MUAL' NUT' A1 K0 A2) as X. unfold t_hi in X. cbn [t_lo t_len] in X. change (h_L h) with L in X. fold T in X. clear - X Hx. lia.
      - pose proof (tr_apart_user AL h mo _ c' A k0 HK0 (tr_of_T h) Hc' MUAL' NUT' A1 K0 A2) as X. unfold t_hi in X. cbn [t_lo t_len] in X. change (h_L h) with L in X. fold T in X. clear - X Hx. lia.
      - clear - Hx AP. lia. - clear - Hx A1 RBLO' SHRNG. lia. }
    (* [comment removed for export] *)
    assert (KSH : forall A k0, 0x2008fff7000 <= A -> A + k0 <= 0x10007fff8000 -> (A + k0 <= SUB \/ SUB + nfix n / 8 + 1 <= A) -> kept m m' A k0).
    { intros A k0 A1 A2 AP x Hx. apply KEEPI.
      - clear - Hx A2 LOIMG. lia. - unfold A_SS, A_DEP_END. clear - Hx A1. lia.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
        + pose proof (tr_wf AL h mo _ HK0 (tr_of_node h b Hb)) as (_ & _ & _ & _ & _ & _ & W6). specialize (W6 eq_refl). unfold t_hi, node_tr in W6. cbn [t_lo t_len] in W6. clear - Hx A1 A2 W6. lia.
        + pose proof (SHn b Hb). clear - H Hx A1 A2. lia.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
        + pose proof (tr_wf AL h mo _ HK0 (tr_of_store h b Hb)) as (_ & _ & _ & _ & _ & _ & W6). specialize (W6 eq_refl). unfold t_hi, store_tr in W6. cbn [t_lo t_len] in W6. clear - Hx A1 A2 W6. lia.
        + pose proof (SHs b Hb). clear - H Hx A1 A2. lia.
      - clear - Hx A1 A2 TB GC31. lia. - clear - Hx A1 A2 TB. lia. - clear - Hx A1 A2 TB. lia. - clear - Hx A2 AB0. lia. - clear - Hx AP. lia. }
    (* [comment removed for export] *)
    assert (KSHL : forall A k0, 0x800c3e00 <= A -> A + k0 <= 0x8fff7000 -> kept m m' A k0).
    { intros A k0 A1 A2 x Hx. apply KEEPI.
      - clear - Hx A2 LOIMG. lia. - unfold A_SS, A_DEP_END. clear - Hx A1. lia.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
        + pose proof (tr_wf AL h mo _ HK0 (tr_of_node h b Hb)) as (_ & _ & _ & _ & _ & _ & W6). specialize (W6 eq_refl). unfold t_hi, node_tr in W6. cbn [t_lo t_len] in W6. clear - Hx A1 A2 W6. lia.
        + pose proof (SHn b Hb). clear - H Hx A1 A2. lia.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
        + pose proof (tr_wf AL h mo _ HK0 (tr_of_store h b Hb)) as (_ & _ & _ & _ & _ & _ & W6). specialize (W6 eq_refl). unfold t_hi, store_tr in W6. cbn [t_lo t_len] in W6. clear - Hx A1 A2 W6. lia.
        + pose proof (SHs b Hb). clear - H Hx A1 A2. lia.
      - clear - Hx A1 A2 TB GC31. lia. - clear - Hx A1 A2 TB. lia. - clear - Hx A1 A2 TB. lia. - clear - Hx A2 AB0. lia. - clear - Hx A2 SHRNG. lia. }
    assert (KPG : forall v8, nfix n mod 8 = 0 -> rw_cells asegs m PGS [C1 v8] -> kept m m' PGS 1).
    { intros v8 M0 C x Hx. pose proof (rw_C1_inj m PGS pgb v8 PGC C) as ->.
      assert (PV : pgv n v8 = v8) by (unfold pgv; rewrite (proj2 (Z.eqb_eq _ _) M0); reflexivity). rewrite PV in PGS'.
      assert (EX : x = wa PGS) by (unfold wa; apply bv_eq; rewrite u64_lit by (rewrite EPGS; clear - SHRNG NF8; lia); clear - Hx; lia).
      assert (P2 : rw_cells asegs m' PGS [C1 v8]) by exact PGS'.
      subst x. ddestruct P2 as [[_ (_ & _ & B')] _]. ddestruct C as [[_ (_ & _ & B)] _].
      specialize (B 0%nat ltac:(cbn; lia)). specialize (B' 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in B, B'. rewrite Z.add_0_r in B, B'.
      unfold mrd in B, B'. rewrite (seg_rom_high (wa PGS)) in B, B' by (unfold wa; rewrite u64_lit by (rewrite EPGS; clear - SHRNG NF8; lia); rewrite EPGS; clear - SHRNG NF8; lia).
      destruct (m' (wa PGS)); [| discriminate]. destruct (m (wa PGS)); [| discriminate]. congruence. }
    (* [comment removed for export] *)
    assert (MUI : munch [(0, 0x10000); (A_SS, A_DEP_END); (0x65f000, 2^64)] m m').   (* [comment removed for export] *)
    { intros x OUT. cbn [outside] in OUT. pose proof (u64_range x). apply (KI (bv_unsigned x) 1); unfold A_SS, A_DEP_END in *; clear - OUT H; lia. }
    assert (LOWD : forall A k0, (0x10000 <= A /\ A + k0 <= A_SS) \/ (A_DEP_END <= A /\ A + k0 <= 0x65f000) -> disjoint_from [(0, 0x10000); (A_SS, A_DEP_END); (0x65f000, 2^64)] A k0)
      by (intros A k0 H; unfold A_SS, A_DEP_END in *; cbn [disjoint_from]; clear - H; lia).
    assert (KCTX : kept m m' CTX 0x10000).
    { apply (KT (TR CTX (l_ctxlen L) KEager true true)); try solve [intros; discriminate].
      - exact (tr_of_ctx h). - reflexivity. - intros E. injection E. clear - CXLEN. lia. - intros b _ E. injection E. clear - CXLEN. lia.
      - cbn [t_lo]. clear. lia. - unfold t_hi. cbn [t_lo t_len]. rewrite CXLEN. clear. lia. - clear. lia. }
    Ltac kimg H KI := eapply keep_ro; [exact H| apply KI; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul];
      unfold A_ASAN_INITED, A_MCS_CELL, A_GOT_CFLAGS, A_CFLAGS, A_CF_FASTUNW, A_GOT_PAGESZ, A_PAGESZ_CELL, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_RSS_CELL, A_DEBRUIJN,
             A_LOGTBL1, A_LOGTBL2, A_MINRZ, A_MAXUSER, A_INSTANCE, A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND,
             A_GOT_RMEMSET, A_RMEMSET, A_CF_CSMT, A_GOT_LSANTLS, A_LSAN_CNT, A_MAGIC_CELL, A_MHOOKS, A_GOT_FLAGS, A_FL_MAXFILL, A_FL_FILLB, A_FLAGS, A_GOT_LNAME, A_LNAME_CELL,
             A_DECORATE, A_MMAP_LIMIT, A_FL_PPART, A_Q_MAX, A_MRN, A_SS, A_DEP_END; clear; lia].
    (* [comment removed for export] *)
    assert (SLOTS : forall k', In k' (h_chunks h) ->
              let slo := (if ck_prim k' then ck_ab k' else ck_map_beg k') in
              slo <= ck_ab k' /\ ck_ab k' + ck_rz k' = ck_user k' /\ ck_user k' + Z.max (ck_n k') 8 <= ck_end k'
              /\ (ck_end k' <= AB \/ AB + class_size c <= slo)).
    { intros k' Hk'. cbn zeta. pose proof (proj1 (Forall_forall _ _) OLDAP k' Hk') as AP. pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (WN & WST & WP & WCX).
      split; [| split; [reflexivity| split; [| exact AP]]].
      - destruct (ck_prim k'); [clear; lia| unfold ck_map_beg; clear; lia].
      - unfold ck_user, ck_rz, ck_end, ck_map_beg. pose proof (rz_size_bound (ck_n k')) as RZ'. destruct (ck_prim k') eqn:PR.
        + ddestruct WCX as (WCLS & WC30 & _). rewrite WCLS. pose proof (needed_le_class (ck_n k') ltac:(clear - WN; lia) ltac:(rewrite <- WP; reflexivity)) as NC.
          unfold needed, rounded, round_up in NC. pose proof (Z.div_mod (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)).
          clear - RZ' NC H H0 WN. lia.
        + unfold ck_map_size, sec_map_size. pose proof (round_up_spec (needed2 (ck_n k')) 4096 ltac:(clear; lia)) as [RU _].
          unfold needed2, needed, rounded, round_up in RU |- *. pose proof (Z.div_mod (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)).
          destruct (from_primary (ck_n k')); clear - RZ' RU H H0 WN; lia. }
    (* [comment removed for export] *)
    assert (KSL : forall k' A k0, In k' (h_chunks h) -> (if ck_prim k' then ck_ab k' else ck_map_beg k') <= A -> A + k0 <= ck_end k' -> 0 < k0 -> kept m m' A k0).
    { intros k' A k0 Hk' A1 A2 K0. dpose (SLOTS k' Hk') as (S1 & S2 & S3 & S4). pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (WN & WST & WP & WCX).
      unfold ck_end in *. destruct (ck_prim k') eqn:PR.
      - ddestruct WCX as (WCLS & WC30 & i' & Hi' & EAB'). unfold carved in Hi'.
        pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear - WC30; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & AUCS' & _).
        pose proof (class_size_range (ck_cls k') ltac:(clear - WC30; lia)) as CSR'.
        assert (SL1 : region_beg L (ck_cls k') <= ck_ab k') by (rewrite EAB'; unfold chunk_at; change (h_L h) with L; clear - Hi' CSR'; nia).
        assert (SL2 : ck_ab k' + class_size (ck_cls k') <= region_beg L (ck_cls k') + r_mapped_user (h_reg h (ck_cls k'))).
        { rewrite EAB'. unfold chunk_at. change (h_L h) with L.
          assert ((i' + 1) * class_size (ck_cls k') <= r_alloc_user (h_reg h (ck_cls k'))).
          { rewrite AUCS'. rewrite AUCS' in Hi'. rewrite Z.mul_comm in Hi'. rewrite Z.div_mul in Hi' by (clear - CSR'; lia). clear - Hi' CSR'. nia. }
          clear - H AUMU'. lia. }
        apply (KU (ck_cls k') A k0); [clear - WC30; lia| clear - A1 SL1; lia| clear - A2 SL2; lia| exact K0| clear - A1 A2 S4; lia].
      - ddestruct WCX as (i' & NTH' & _). assert (HIN : In (AModel.SH (ck_map_beg k') (ck_map_size k') (needed2 (ck_n k'))) (s_chunks (h_sec h))) by (eapply nth_error_In; exact NTH').
        ddestruct WS as (_ & _ & _ & _ & _ & _ & _ & SF). pose proof (proj1 (Forall_forall _ _) SF _ HIN) as (_ & BIG & _). cbn [s_map_size] in BIG.
        apply (KT (sec_tr (AModel.SH (ck_map_beg k') (ck_map_size k') (needed2 (ck_n k')))) A k0); try solve [intros; discriminate].
        + apply tr_of_sec. exact HIN. + reflexivity.
        + intros E. injection E. clear - BIG. intros. lia.
        + intros b Hb. exact (sec_not_node AL h mo _ b HK0 HIN Hb).
        + unfold sec_tr. cbn [t_lo s_map_beg]. exact A1. + unfold t_hi, sec_tr. cbn [t_lo t_len s_map_beg s_map_size]. exact A2. + exact K0. }
    (* [comment removed for export] *)
    assert (SHAD8 : forall A, A mod 8 = 0 -> shad A = 0x7fff8000 + A / 8) by (intros; reflexivity).
    assert (KPG0 : nfix n mod 8 = 0 -> kept m m' PGS 1) by (intros M0; exact (KPG pgb M0 PGC)).
    (* [comment removed for export] *)
    assert (KSHS : forall A k0, (0x65f000 <= A /\ (A + k0 <= 0x7fff7000 \/ 0x10007fff8000 <= A)) -> A + k0 <= ACEIL -> 0 <= k0 -> A mod 8 = 0 ->
              (A + k0 <= AB \/ AB + class_size c <= A) -> kept m m' (shad A) ((k0 + 7) / 8)).
    { intros A k0 [A63 [ALO|A1]] A2 K0 A8 AP x Hx.
      { unfold shad in Hx. pose proof (Z.div_mod A 8 ltac:(clear; lia)) as DA. rewrite A8, Z.add_0_r in DA.
        pose proof (Z.div_mod (k0 + 7) 8 ltac:(clear; lia)) as DK. pose proof (Z.mod_pos_bound (k0 + 7) 8 ltac:(clear; lia)) as MK.
        apply (KSHL (bv_unsigned x) 1); [clear - Hx A63 DA; lia| clear - Hx ALO DA DK MK K0; lia| clear; lia]. }
      unfold shad in Hx.
      pose proof (Z.div_mod A 8 ltac:(clear; lia)) as DA. rewrite A8, Z.add_0_r in DA.
      pose proof (Z.div_mod (k0 + 7) 8 ltac:(clear; lia)) as DK. pose proof (Z.mod_pos_bound (k0 + 7) 8 ltac:(clear; lia)) as MK.
      pose proof (Z.div_mod AB 16 ltac:(clear; lia)) as DAB. rewrite AB16, Z.add_0_r in DAB.
      pose proof (Z.div_mod (rz_size n) 16 ltac:(clear; lia)) as DRZ. rewrite RZ16, Z.add_0_r in DRZ.
      pose proof (Z.div_mod (class_size c) 16 ltac:(clear; lia)) as DCS. rewrite CS16, Z.add_0_r in DCS.
      pose proof (Z.div_mod (nfix n) 8 ltac:(clear; lia)) as DN. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(clear; lia)) as MN.
      assert (ESUB : SUB = 0x7fff8000 + (AB / 16) * 2 + (rz_size n / 16) * 2).
      { subst SUB UB. rewrite DAB at 1. rewrite DRZ at 1. replace (16 * (AB / 16) + 16 * (rz_size n / 16)) with ((AB / 16 * 2 + rz_size n / 16 * 2) * 8) by (clear; lia). rewrite Z_div_mult by (clear; lia). clear; lia. }
      assert (EPGS2 : PGS = SUB + nfix n / 8) by exact EPGS.
      destruct AP as [AP|AP].
      - (* [comment removed for export] *)
        apply (KSH (bv_unsigned x) 1); [clear - Hx A1 DA; lia| clear - Hx A2 DA DK MK; lia| | clear; lia]. left.
        clear - Hx AP DA DK MK ESUB DAB DRZ RZB. nia.
      - (* [comment removed for export] *)
        destruct (Z.eq_dec (bv_unsigned x) PGS) as [EX|NX].
        + assert (M0 : nfix n mod 8 = 0).
          { rewrite EPGS2, ESUB in EX. clear - Hx EX AP DA DK MK DCS DN MN UBLE NEEDCS NF1 CSR RZB DAB DRZ. subst UB. nia. }
          apply (KPG0 M0). rewrite <- EX. clear; lia.
        + apply (KSH (bv_unsigned x) 1); [clear - Hx A1 DA; lia| clear - Hx A2 DA DK MK; lia| | clear; lia]. right.
          rewrite EPGS2, ESUB in NX. rewrite ESUB. clear - Hx NX AP DA DK MK DCS DN MN UBLE NEEDCS NF1 CSR RZB DAB DRZ. subst UB. nia. }
    (* [comment removed for export] *)
    assert (KIMG : forall x : word, 0x10000 <= bv_unsigned x < 0x65f000 -> ~ in_rangesZ dep_zone (bv_unsigned x) -> m' x = m x).
    { intros x Hx Hz. cbn [in_rangesZ dep_zone] in Hz. unfold A_SS, A_DEP_END in *. apply (KI (bv_unsigned x) 1); [clear - Hx; lia| clear - Hx; lia| clear - Hz; lia| clear; lia]. }
    split. { (* [comment removed for export] *)
      split. { (* [comment removed for export] *)
        split; [| subst h'; rewrite blocks_pop, HLB; reflexivity].
        dpose DI' as (_ & _ & (_ & NBWF2 & NBL2) & _ & DWF2 & _ & _ & (_ & BLWF2 & BLL2) & _ & _ & BL2 & _).
        apply (awf'_pop h c q k n AB N' tf' (nb ++ sn) (bl ++ sb) AWF); try assumption.
        - subst q. fold p. f_equal. unfold pc_count in *. subst cnt. clear - HCNT. lia.
        - split; [exact HK1| exact HK2].
        - clear - TFB. lia.
        - destruct DWF2 as [_ E]. rewrite E. reflexivity.
        - destruct DWF2 as [N1 E]. rewrite E. clear - N1. pose proof (Z.div_mod N' 65536 ltac:(lia)). pose proof (Z.mod_pos_bound N' 65536 ltac:(lia)). lia.
        - rewrite BL2. pose proof (tf_after_put h d tf' HFR D0 (proj1 (proj2 (proj2 (proj2 WD)))) TFB POT) as TFX.
          clear - TFB TFX. pose proof (Z.div_mod (tf' + 2^20 - 1) (2^20) ltac:(lia)). pose proof (Z.mod_pos_bound (tf' + 2^20 - 1) (2^20) ltac:(lia)). lia. }
      split. { (* [comment removed for export] *) change (h_L h') with L. eapply hm_maps_frame; [exact GM| exact WM']. }
      split. { (* [comment removed for export] *) change (h_L h') with L. eapply (hm_statics_frame m m' WM' L (conj GRO GRW)).
        - eapply (iagree_of_windows2 _ dep_zone 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMG].
        - eapply (iagree_of_windows2 _ dep_zone 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMG].
        - apply KTP; clear - GC31; lia.
        - eapply kept_sub; [exact KCTX| clear; lia| clear; lia].
        - eapply kept_sub; [exact KCTX| clear; lia| clear; lia].
        - (* [comment removed for export] *)
          pose proof WLS as [_ (DT1 & DT2 & DT3)]. change (h_L h) with L in DT1, DT2, DT3.
          apply (KT (TR (l_dtls L) 4096 KEager true true)); try solve [intros; discriminate].
          + apply tr_of_dtls.
          + reflexivity.
          + intros E. apply (T_ne_dtls h VWF0). change (h_L h) with L. fold T. symmetry. exact E.
          + cbn [t_lo]. clear; lia.
          + unfold t_hi. cbn [t_lo t_len]. clear; lia.
          + clear; lia. }
      split. { (* [comment removed for export] *)
        eapply (hm_thread_frame_but m m' WM' h c (AModel.PC (pc_max p) (pc_csize p) (removelast (pc_chunks p))) (ds c) GT GC31).
        - exact UNW'.
        - intros c' Hc' NE. change (l_T (h_L h)) with T. apply KTP; clear - Hc' NE GC31; lia.
        - change (l_T (h_L h)) with T. apply KTP; clear - GC31; lia.
        - exact TW. - change (l_T (h_L h)) with T; exact TI.
        - (* [comment removed for export] *)
          split; [| split; [exact ARR'| split; [exact LWS| split]]].
          + unfold pc_count. cbn [pc_max pc_csize pc_chunks]. rewrite PMAX, PCSZ.
            replace (Z.of_nat (length (removelast (pc_chunks p)))) with (cnt - 1); [exact PC'|].
            rewrite (length_removelast_Z (pc_chunks p) HIT). unfold pc_count in *. subst cnt. clear; lia.
          + cbn [pc_chunks]. apply firstn_removelast_map; [exact HIT| exact FIRSTN].
          + cbn [pc_max pc_csize pc_chunks]. rewrite CINIT. split; [exact PMAX| exact PCSZ].
        - intros c' _ _. reflexivity.
        - reflexivity. - reflexivity.
        - intros c'. cbv delta [h']. unfold pop_h, pop_cache. cbn [h_cache]. fold p. destruct (c' =? c); reflexivity. }
      split. { (* [comment removed for export] *) exact DI'. }
      split. { (* [comment removed for export] *)
        unfold hm_chunks. cbv delta [h']. unfold pop_h. cbn [h_chunks]. constructor.
        - (* [comment removed for export] *)
          change (APop.newk c n AB) with newk.
          assert (EHDR : ck_hdr newk = CHB) by (subst CHB; reflexivity). assert (EUSR : ck_user newk = UB) by reflexivity.
          cbn [ck_st ck_n ck_ab newk]. unfold hm_chunk. cbn [ck_st ck_n ck_ab newk].
          split; [| split].
          + pose proof (proj1 (wf_depot'_bounds h WD ltac:(clear - HFR D0; lia))) as DNB.
            unfold hm_hdr. dexists b1', id. rewrite EHDR. cbn [ck_st ck_n newk]. split; [| split; [exact B13| split; [exact B1R| clear - IDB NB' DNB; lia]]].
            eapply (rw_cells_reshape asegs m' CHB); [exact HDR'| cbn; first [clear; tauto | tauto] |]. (* [comment removed for export] *)
            cbn [cells_bytes cbytes app]. rewrite ?Z.mul_0_l, ?Z.lor_0_l. rewrite ?(le8_split4 (Z_to_bv 64 id)).
            rewrite unsigned_lit by (clear - IDB NB' DNB; lia). rewrite (Z.div_small id) by (clear - IDB NB' DNB; lia). rewrite <- ?app_assoc. reflexivity.
          + unfold hm_magic. intros HRZ. rewrite EHDR. cbn [ck_ab newk]. exact (MG' HRZ).
          + cbn [CHUNK_ALLOCATED Z.eqb Pos.eqb]. unfold hm_ushadow. rewrite EUSR. cbn [ck_n newk]. split.
            * exact SUB'.
            * intros M8. replace (shad (UB + nfix n / 8 * 8)) with PGS; [| subst PGS; unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity].
              unfold pgv in PGS'. destruct (Z.eqb_spec (nfix n mod 8) 0) as [E0|NE0]; [exact (False_ind _ (M8 E0))| exact PGS'].
        - fold newk. change (Forall (hm_chunk m') (h_chunks h)). 
          apply (hm_chunks_frame m m' WM' h GC AWF). intros k' Hk'. dpose (SLOTS k' Hk') as (S1 & S2 & S3 & S4).
          pose proof (proj1 (chunk_geom h k' AWF Hk')) as RZk16. unfold ck_rz in RZk16.
          split; [| split].
          + apply (KSL k'); [exact Hk'| exact S1| unfold ck_rz in *; clear - S2 S3; unfold nfix in *; lia| unfold ck_rz in *; clear - RZk16; lia].
          + intros ALLOC. apply KSHS; [| | clear - S3; unfold nfix in *; lia| exact (proj2 (proj2 (chunk_geom h k' AWF Hk')))| unfold ck_rz, nfix in *; clear - S1 S2 S3 S4 RZk16; lia].
            * (* [comment removed for export] *)
              ddestruct (chunk_ext h k' AWF Hk') as (_ & F1 & F2 & F3 & F4 & F5 & F6 & _). unfold kHighMemBeg in F5.
              unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize, nfix in *. clear - F1 F2 F3 F4 F5 S2 RZk16. lia.
            * pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (WN' & _ & WP' & WX'). unfold ck_end in S3. destruct (ck_prim k') eqn:PR.
              -- ddestruct WX' as (_ & WC30' & i' & Hi' & EAB').
                 pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear - WC30'; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & AUCS' & _ & MULIM' & _). unfold kUserLimit in MULIM'.
                 unfold carved in Hi'. pose proof (class_size_range (ck_cls k') ltac:(clear - WC30'; lia)) as CSR'.
                 assert ((i' + 1) * class_size (ck_cls k') <= r_alloc_user (h_reg h (ck_cls k'))).
                 { rewrite AUCS'. rewrite AUCS' in Hi'. rewrite Z.mul_comm in Hi'. rewrite Z.div_mul in Hi' by (clear - CSR'; lia). clear - Hi' CSR'. nia. }
                 rewrite EAB' in S3. unfold chunk_at, region_beg, kRegionSize in S3. change (h_L h) with L in S3. fold SB in S3.
                 clear - S3 H AUMU' MULIM' WC30' SEHI B6B B6HI. unfold nfix in *. nia.
              -- ddestruct WX' as (i' & _ & _ & _ & CEIL & _). clear - S3 CEIL. unfold nfix in *. lia.
          + intros NALLOC. apply (KSL k'); [exact Hk'| unfold ck_rz in *; clear - S1 S2 RZk16; lia| clear - S3; unfold nfix in *; lia| clear; lia]. }
      split. { (* [comment removed for export] *)
        apply (hm_regions_frame m m' WM' h GR WR). intros c' Hc'. change (h_L h) with L.
        pose proof (WR c' ltac:(unfold kNumClasses; clear - Hc'; lia)) as WRc'. cbn zeta in WRc'. ddestruct WRc' as (_ & AUMU' & AUCS' & MUAL' & MULIM' & _ & MFAL' & MFAB' & _).
        unfold kUserLimit in MULIM'. unfold kFreeArrayMapSize, kFreeArraySize in MFAL', MFAB'.
        assert (RBLO' : 0x10007fff8000 + 4096 + 2^32 <= region_beg L c') by (unfold region_beg, kRegionSize; fold SB; clear - SBLO Hc'; nia).
        assert (RBHI' : region_beg L c' + 2^32 <= SB + 2^37) by (unfold region_beg, kRegionSize; fold SB; clear - Hc'; nia).
        pose proof (class_size_range c' Hc') as CSR'.
        split; [| split; [| split]].
        - (* [comment removed for export] *)
          apply (KT (ri_tr L)); try solve [intros; discriminate].
          + unfold tr_of. rewrite !in_app_iff. do 4 right. left. left. reflexivity.
          + reflexivity.
          + unfold ri_tr, ri_addr. cbn [t_lo]. clear - Hc'. lia.
          + unfold ri_tr, ri_addr, t_hi. cbn [t_lo t_len]. clear - Hc'. lia.
          + clear; lia.
        - (* [comment removed for export] *)
          intros x Hx. set (j := (bv_unsigned x - fa_beg L c') / kUserMapSize).
          pose proof (Z.div_mod (bv_unsigned x - fa_beg L c') kUserMapSize ltac:(unfold kUserMapSize; clear; lia)) as DJ. pose proof (Z.mod_pos_bound (bv_unsigned x - fa_beg L c') kUserMapSize ltac:(unfold kUserMapSize; clear; lia)) as MJ. fold j in DJ.
          pose proof (Z.div_mod (r_mapped_fa (h_reg h c')) (2^18) ltac:(clear; lia)) as DF. change kUserMapSize with (2^18) in *.
          assert (HJ : 0 <= j < r_mapped_fa (h_reg h c') / 2^18) by (subst j; split; [apply Z.div_pos; clear - Hx; lia| apply Z.div_lt_upper_bound; [clear; lia|]; clear - Hx DF MFAL'; nia]).
          apply (KT (funit_tr L c' j) (bv_unsigned x) 1); try solve [intros; discriminate].
          + apply tr_of_funit; [exact Hc'| exact HJ].
          + reflexivity.
          + intros j' Hj' E. injection E. unfold fa_beg, region_beg, kFreeArrayOffset, kRegionSize. change (h_L h) with L. fold SB.
            pose proof (Z.div_mod (r_mapped_user r) (2^18) ltac:(clear; lia)) as DU. pose proof (Z.mod_pos_bound (r_mapped_user r) (2^18) ltac:(clear; lia)) as MU'.
            pose proof (Z.mod_pos_bound (r_mapped_fa (h_reg h c')) (2^18) ltac:(clear; lia)) as MF'.
            fold r in Hj'. clear - HJ Hj' MFAB' MULIM DF DU MU' MF' Hc' GC31. unfold kUserMapSize. intros E1. lia.
          + unfold funit_tr. cbn [t_lo]. unfold kUserMapSize. clear - DJ MJ. lia.
          + unfold funit_tr, t_hi. cbn [t_lo t_len]. unfold kUserMapSize. clear - DJ MJ. lia.
          + clear; lia. + clear; lia.
        - (* [comment removed for export] *)
          pose proof (class_size_mod16 c' Hc') as C16'. pose proof (Z.div_mod (class_size c') 16 ltac:(clear; lia)) as DC'. rewrite C16', Z.add_0_r in DC'.
          pose proof (Z.div_mod (r_mapped_user (h_reg h c')) (2^18) ltac:(clear; lia)) as DMU. change kUserMapSize with (2^18) in MUAL'. rewrite MUAL', Z.add_0_r in DMU.
          assert (T8 : exists t, r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c') = t * 8).
          { exists (2^15 * (r_mapped_user (h_reg h c') / 2^18) - 2 * (class_size c' / 16) * carved h c'). clear - DC' DMU AUCS'. nia. }
          destruct T8 as [t ET].
          replace ((r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) / 8) with ((r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c') + 7) / 8)
            by (rewrite ET, Z_div_mult, Z.div_add_l by (clear; lia); clear; cbn; lia).
          apply KSHS; [clear - RBLO' AUMU'; lia| clear - AUMU' MULIM' RBHI' SEHI B6B B6HI; lia| clear - AUMU'; lia| |].
          + unfold region_beg, kRegionSize. fold SB. pose proof (Z.div_mod SB (2^16) ltac:(clear; lia)) as DM.
            replace (SB + c' * 2^32 + r_alloc_user (h_reg h c')) with (8 * (SB / 2^16 * 2^13 + c' * 2^29 + (class_size c' / 16) * carved h c' * 2)) by (clear - DM SB16 DC' AUCS'; nia).
            rewrite Z.mul_comm. apply Z_mod_mult.
          + destruct (Z.eq_dec c' c) as [->|NE]; [right; fold RB r; clear - ABHI; lia|].
            unfold region_beg, kRegionSize. fold SB. rewrite EAB. unfold chunk_at, region_beg, kRegionSize. change (h_L h) with L. fold SB.
            clear - NE Hc' GC31 AUMU' MULIM' KCS HK1 AUMU MULIM CSR CSR'. nia.
        - (* [comment removed for export] *)
          intros k' Hk'.
          assert (AL8 : chunk_at L c' k' mod 8 = 0).
          { unfold chunk_at, region_beg, kRegionSize. fold SB. pose proof (Z.div_mod SB (2^16) ltac:(clear; lia)) as DM. pose proof (class_size_mod16 c' Hc') as C16'. pose proof (Z.div_mod (class_size c') 16 ltac:(clear; lia)) as DC.
            replace (SB + c' * 2^32 + k' * class_size c') with (8 * (SB / 2^16 * 2^13 + c' * 2^29 + k' * (class_size c' / 16) * 2)) by (clear - DM SB16 DC C16'; lia). rewrite Z.mul_comm. apply Z_mod_mult. }
          assert (KHI : (k' + 1) * class_size c' <= r_alloc_user (h_reg h c')) by (rewrite AUCS'; rewrite AUCS' in Hk'; rewrite Z.mul_comm in Hk'; rewrite Z.div_mul in Hk' by (clear - CSR'; lia); clear - Hk' CSR'; nia).
          destruct (Z.eq_dec c' c) as [EC2|NE].
          + subst c'. destruct (Z.eq_dec k' k) as [->|NK].
            * (* [comment removed for export] *)
              change (h_L h) with L in EAB. rewrite <- EAB. intros x Hx. apply (KSH (bv_unsigned x) 1); unfold shad in Hx; subst SUB UB.
              -- pose proof (Z.div_mod AB 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound AB 8 ltac:(clear; lia)). clear - Hx AB0 H H0. lia.
              -- pose proof (Z.div_mod AB 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound AB 8 ltac:(clear; lia)). clear - Hx AB1 H H0 N2B RZB. lia.
              -- left. pose proof (Z.div_mod AB 16 ltac:(clear; lia)) as DAB. rewrite AB16, Z.add_0_r in DAB. pose proof (Z.div_mod (rz_size n) 16 ltac:(clear; lia)) as DRZ. rewrite RZ16, Z.add_0_r in DRZ.
                 clear - Hx DAB DRZ RZB. nia.
              -- clear; lia.
            * replace 1 with ((1 + 7) / 8) by reflexivity. apply KSHS; [ | | clear; lia| exact AL8|].
              -- unfold chunk_at. clear - RBLO' Hk' CSR'. nia.
              -- unfold chunk_at. clear - KHI AUMU' MULIM' RBHI' SEHI B6B B6HI CSR'. nia.
              -- fold RB. rewrite EAB. unfold chunk_at. change (h_L h) with L. fold RB. destruct (Z.lt_trichotomy k' k) as [LTk|[EQk|GTk]]; [| exact (False_ind _ (NK EQk))|].
                 ++ left. assert ((k' + 1) * class_size c <= k * class_size c) by (apply Z.mul_le_mono_nonneg_r; clear - LTk CSR; lia). clear - H CSR. lia.
                 ++ right. assert ((k + 1) * class_size c <= k' * class_size c) by (apply Z.mul_le_mono_nonneg_r; clear - GTk CSR; lia). clear - H CSR. lia.
          + replace 1 with ((1 + 7) / 8) by reflexivity. apply KSHS; [ | | clear; lia| exact AL8|].
            * unfold chunk_at. clear - RBLO' Hk' CSR'. nia.
            * unfold chunk_at. clear - KHI AUMU' MULIM' RBHI' SEHI B6B B6HI CSR'. nia.
            * unfold region_beg, kRegionSize. fold SB. rewrite EAB. unfold chunk_at, region_beg, kRegionSize. change (h_L h) with L. fold SB.
              clear - NE Hc' GC31 KHI Hk' AUMU' MULIM' KCS HK1 AUMU MULIM CSR CSR'. nia. }
      split. { (* [comment removed for export] *)
        apply (hm_quar_frame m m' WM' h GQ).
        - eapply (iagree_of_windows2 _ dep_zone 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMG].
        - change (h_L h) with L. apply KTP; clear - GC31; lia.
        - intros b Hb. ddestruct WQ as ((T1q & _) & (G1q & _) & NDq & _).
          assert (WBA : wf_batch h b) by (apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) T1q b Hb)| exact (proj1 (Forall_forall _ _) G1q b Hb)]).
          ddestruct WBA as (_ & _ & _ & i & Hi & EB). rewrite EB. unfold kBatchClass in *. change (h_L h) with L in Hi |- *.
          pose proof (WR 24 ltac:(unfold kNumClasses; clear; lia)) as WR24. cbn zeta in WR24. ddestruct WR24 as (_ & AUMU' & AUCS' & MUAL' & MULIM' & _).
          change (class_size 24) with 8192 in *. unfold kUserLimit in MULIM'.
          apply (KU 24); [clear; lia| unfold chunk_at; change (class_size 24) with 8192; clear - Hi; lia| | clear; lia|].
          + unfold chunk_at. change (class_size 24) with 8192.
            assert ((i + 1) * 8192 <= r_alloc_user (h_reg h 24)) by (rewrite AUCS'; clear - Hi; lia).
            clear - H AUMU'. lia.
          + unfold chunk_at. change (class_size 24) with 8192.
            assert (KHI : (i + 1) * 8192 <= r_alloc_user (h_reg h 24)) by (rewrite AUCS'; clear - Hi; lia).
            destruct (Z.eq_dec c 24) as [EC24|NC24].
            * (* [comment removed for export] *)
              assert (CS24 : class_size c = 8192) by (rewrite EC24; reflexivity).
              assert (NEI : i <> k).
              { intros ->. apply (NoDup_app_l_r (cache_set h c) (chunk_set h c ++ batch_set h c) q).
                - unfold owned in OWN. apply NoDup_app_remove_l in OWN. exact OWN.
                - exact QIN.
                - apply in_app_iff. right. unfold batch_set. rewrite EC24. cbn [Z.eqb Pos.eqb kBatchClass].
                  replace q with (compact (h_L h) 24 (b_addr b)); [apply in_map_iff; exists b; split; [reflexivity| exact Hb]|].
                  rewrite EB. change (h_L h) with L. rewrite <- EC24. rewrite compact_chunk_at by exact CS16. clear - HK2 CS16 CSR. pose proof (Z.div_mod (class_size c) 16 ltac:(lia)). nia. }
              rewrite EAB. rewrite <- EC24. unfold chunk_at. change (h_L h) with L. rewrite CS24.
              clear - NEI. destruct (Z.lt_ge_cases i k); [left| right]; nia.
            * rewrite EAB. unfold chunk_at, region_beg, kRegionSize. change (h_L h) with L. fold SB.
              clear - NC24 GC31 KHI Hi AUMU' MULIM' KCS HK1 AUMU MULIM CSR. nia. }
      split. { (* [comment removed for export] *)
        apply (hm_sec_frame m m' WM' h GS WS).
        - eapply (iagree_of_windows2 _ dep_zone 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMG].
        - change (h_L h) with L. ddestruct WS as (_ & NRM & NR0 & NR8 & PAE & _). intros x Hx.
          set (j := (bv_unsigned x - l_pa L) / kPaSlice).
          pose proof (Z.div_mod (bv_unsigned x - l_pa L) kPaSlice ltac:(unfold kPaSlice; clear; lia)) as DJ. pose proof (Z.mod_pos_bound (bv_unsigned x - l_pa L) kPaSlice ltac:(unfold kPaSlice; clear; lia)) as MJ. fold j in DJ.
          unfold kPaSlice in *. unfold kPtrArrayChunks in *.
          assert (HJ : 0 <= j < h_pa_committed h / 131072).
          { subst j. split; [apply Z.div_pos; clear - Hx; lia| apply Z.div_lt_upper_bound; [clear; lia|]].
            rewrite PAE. unfold kPtrArrayChunks in NRM. pose proof (Z.div_mod (s_nres (h_sec h)) 16384 ltac:(clear; lia)) as DQ. rewrite NRM, Z.add_0_r in DQ.
            set (qn := s_nres (h_sec h) / 16384) in DQ. rewrite DQ. replace (8 * (16384 * qn)) with (qn * 131072) by (clear; lia).
            rewrite Z_div_mult by (clear; lia). rewrite PAE, DQ in Hx. clear - Hx. lia. }
          apply (KT (pa_tr L j) (bv_unsigned x) 1); try solve [intros; discriminate].
          + unfold tr_of. rewrite !in_app_iff. do 5 right. left. apply in_map. apply in_zseq. exact HJ.
          + reflexivity.
          + unfold pa_tr. cbn [t_lo]. unfold kPaSlice. clear - DJ MJ. lia.
          + unfold pa_tr, t_hi. cbn [t_lo t_len]. unfold kPaSlice. clear - DJ MJ. lia.
          + clear; lia. + clear; lia.
        - intros sh Hsh. ddestruct WS as (_ & _ & _ & _ & _ & _ & _ & SF). pose proof (proj1 (Forall_forall _ _) SF sh Hsh) as (_ & BIG & _).
          apply (KT (sec_tr sh) (s_map_beg sh) 32); try solve [intros; discriminate].
          + apply tr_of_sec. exact Hsh. + reflexivity.
          + intros E. injection E. clear - BIG. intros. lia.
          + intros b Hb. exact (sec_not_node AL h mo sh b HK0 Hsh Hb).
          + unfold sec_tr. cbn [t_lo]. clear; lia.
          + unfold sec_tr, t_hi. cbn [t_lo t_len]. clear - BIG. lia.
          + clear; lia. }
      split. { (* [comment removed for export] *)
        assert (NFS : forall t, In t (tr_of h) -> t_len t <> kFakeBytes -> t <> TR (l_fs L) kFakeBytes KEager true true) by (intros t _ NE E; subst t; exact (NE eq_refl)).
        apply (hm_fake_frame m m' WM' h LF GF); change (h_L h) with L.
        - unfold lowhigh in FSLO. clear - FSLO; lia.
        - apply (KT (TR (l_fs L) kFakeBytes KEager true true)); try solve [intros; discriminate].
          + exact (tr_of_fs h). + reflexivity.
          + cbn [t_lo]. clear; lia. + unfold t_hi, kFakeBytes. cbn [t_lo t_len]. clear; lia. + clear; lia.
        - intros FB nn IN. ddestruct GF as (_ & _ & _ & WFL & _). destruct (WFL _ IN) as (kk & ii & Hkk & Hii & E). injection E as EN EFB.
          pose proof (fsk_geom (l_fs L) kk Hkk) as SZ.
          assert (FR : l_fs L + 36864 <= fsk_frame (l_fs L) kk ii /\ fsk_frame (l_fs L) kk ii + fsk_bytes kk <= l_fs L + 36864 + 11 * 2^20 /\ 64 <= fsk_bytes kk).
          { unfold fsk_frame, fsk_bytes. unfold fsk_n in Hii, SZ.
            assert (KC : kk = 0 \/ kk = 1 \/ kk = 2 \/ kk = 3 \/ kk = 4 \/ kk = 5 \/ kk = 6 \/ kk = 7 \/ kk = 8 \/ kk = 9 \/ kk = 10) by (clear - Hkk; lia).
            clear - KC Hii. destruct KC as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]; cbn in Hii |- *; lia. }
          apply (KT (TR (l_fs L) kFakeBytes KEager true true)); try solve [intros; discriminate].
          + exact (tr_of_fs h). + reflexivity.
          + cbn [t_lo]. rewrite EFB, EN. change (h_L h) with L. clear - FR SZ. lia.
          + unfold t_hi, kFakeBytes. cbn [t_lo t_len]. rewrite EFB, EN. change (h_L h) with L. clear - FR SZ. lia.
          + clear; lia. }
      (* [comment removed for export] *)
      split. { apply (hm_ia_frame m m' WM' h GI). eapply (iagree_of_windows2 _ dep_zone 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMG]. }
      (* [comment removed for export] *)
      apply (hm_emb_frame_i m m' WM' h _ GE); [reflexivity| reflexivity|]. eapply (iagree_of_windows2 _ dep_zone 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMG]. }
    split. { (* [comment removed for export] *)
      ddestruct (Kd_cases AL v0 nb bl (nb ++ sn) (bl ++ sb) mo' KD) as (v & HKv' & _ & CASE).
      pose proof (vst_of_grow h h' sn sb DG) as VP.
      assert (GOAL : vperm v (vst_of h') /\ vranges_ok AL v).
      { destruct CASE as [(E1 & E2 & ->)|[(a & E1 & E2 & SA & ->)|[(b & E1 & E2 & SB' & ->)|(a & b & E1 & E2 & SA & SB' & ->)]]];
          unfold sane in *;
          first [apply SNB in E1 | apply SNC in E1]; first [apply SNB in E2 | apply SNC in E2]; subst sn sb; cbn [fold_right] in VP.
        - split; [exact VP| exact VR0].
        - split; [exact VP| apply vranges_ok_add_eager; [exact VR0| clear - SA; lia| clear; lia]].
        - split; [exact VP| apply vranges_ok_add_lazy; [exact VR0| clear - SB'; lia| clear; lia]].
        - split; [exact VP| apply vranges_ok_add_lazy; [apply vranges_ok_add_eager; [exact VR0| clear - SA; lia| clear; lia]| clear - SB'; lia| clear; lia]]. }
      destruct GOAL as [VP' VRv]. split; [exact (HKv_perm AL v _ mo' VP' HKv')| exact (vranges_ok_perm AL v _ VP' VRv)]. }
    split; [exact HJ'|].
    split; [reflexivity|]. split; [reflexivity|].
    split. { (* [comment removed for export] *) unfold hfr. cbv delta [h']. unfold pop_h. cbn [h_dep d_n s_total]. unfold sframes in *. clear - POT NB' D0. lia. }
    split. { (* [comment removed for export] *) intros x Hx. exact (vcs_grow AL h h' sn sb x DG Hx). }
    split. { (* [comment removed for export] *)
      intros x. cbn zeta. intros NLO NDEP NNB NBL NPC NSTW NST NCHB NAB NSH NUB. cbn [h_dep d_nb d_bl] in NNB, NBL.
      apply KEEP.
      - exact NLO. - exact NDEP.
      - intros k0 Hk0. apply NNB. change (d_nb (h_dep h')) with (nb ++ sn). unfold dblk. apply nth_In. clear - Hk0. lia.
      - intros jj Hjj. apply NBL. change (d_bl (h_dep h')) with (bl ++ sb). unfold sblk. apply nth_In. clear - Hjj. lia.
      - rewrite EC in NPC. exact NPC. - exact NSTW. - exact NST.
      - subst CHB UB. clear - NCHB. intros X. apply NCHB. lia.
      - subst UB. clear - NAB. intros X. apply NAB. lia.
      - subst SUB UB. unfold shad in NSH. clear - NSH NF8. intros X. apply NSH. lia.
      - match goal with |- ~ ?P => idtac P end. subst PGS SUB UB. unfold shad in NSH. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. rewrite Z_div_plus by (clear; lia). clear - NSH NF8. intros X. apply NSH. lia.
      - exact NUB. }
    split; [intros b Hb; apply in_app_iff; left; exact Hb|]. split; [intros b Hb; apply in_app_iff; left; exact Hb|].
    split; [exact UB16|]. split; [subst UB; clear - AB0 RZB; lia|]. split; [clear - AB1 UBLE NF1 NB; unfold nfix in *; subst UB; lia|].
    split. { (* [comment removed for export] *)
      intros B j HB. rewrite HLB in HB. unfold blocks, live in HB. apply in_map_iff in HB. ddestruct HB as (k' & E & Hk'). apply filter_In in Hk'. destruct Hk' as [Hk' LV].
      injection E as EJ EB. subst B j. pose proof (proj1 (Forall_forall _ _) OLDAP k' Hk') as AP. pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (WN & WST & WP & WCX).
      (* [comment removed for export] *)
      assert (US : (if ck_prim k' then ck_ab k' else ck_map_beg k') <= ck_user k' /\ ck_user k' + ck_n k' <= ck_end k').
      { unfold ck_user, ck_rz, ck_end, ck_map_beg. pose proof (rz_size_bound (ck_n k')) as RZ'. destruct (ck_prim k') eqn:PR.
        - ddestruct WCX as (WCLS & WC30 & _). rewrite WCLS. pose proof (needed_le_class (ck_n k') ltac:(clear - WN; lia) ltac:(rewrite <- WP; reflexivity)) as NC.
          unfold needed, rounded, round_up in NC. pose proof (Z.div_mod (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)).
          clear - RZ' NC H H0 WN. lia.
        - unfold ck_map_size, sec_map_size. pose proof (round_up_spec (needed2 (ck_n k')) 4096 ltac:(clear; lia)) as [RU _].
          unfold needed2, needed, rounded, round_up in RU |- *. pose proof (Z.div_mod (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)).
          destruct (from_primary (ck_n k')); clear - RZ' RU H H0 WN; lia. }
      subst UB. clear - AP US UBLE NF1 NB NEEDCS RZB. unfold nfix in *. lia. }
    split. { (* [comment removed for export] *)
      pose proof (tr_apart_user AL h mo _ c AB (needed2 n) HK0 (tr_of_fs h) GC31 MUAL ltac:(intros j _ E; discriminate E) ABLO NEEDPOS ABMU) as X.
      unfold t_hi in X. cbn [t_lo t_len] in X. change (h_L h) with L in X |- *. unfold kFakeBytes in *. subst UB. clear - X UBLE NF1 NB RZB. unfold nfix in *. lia. }
    exact JUNK.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Hit.

End ARUN_1.
