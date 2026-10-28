(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_ecp_point_free () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "pt_free_LB"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_point_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_init"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_X"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Y"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Z"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_pt"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_freeable"; "mpds_distinct"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_POINT_SIZE"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "ecp_point_free_post"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"].


Definition U_ECP_POINT_FREE : Z := 0x384c8.
(* [comment removed for export] *)
Notation ECP_POINT_FREE_STACK := 48 (only parsing).

Definition pt_free_LB (p : ecp_pt) (LB : list blk) : list blk := lb_free_mpds (pt_mpds p) LB.
(* [comment removed for export] *)
Definition mpds_distinct (ds : list mpd) : Prop := List.NoDup (map fst (flat_map mpd_blk ds)).

Definition ecp_point_free_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (A : Z) (p : ecp_pt) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_free ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1<.O1;.O1:.)Lh',(5.O1<.O1;.O1:.)(6.(7.$0.R13.(8.(9.(:.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(;.O19.)O8.(<.(2.&40.))R3.(=.O1<.))R2.))(6.(>.O1<.R3.)(6.(?.O1<.R3.O3.(10.&40.O18.))(6.(11.O1.R2.)(6.(7.$12.(13.O1<.O1;.O1:.R1.)(13.O1<.O1;.O1:.O7.))(6.(14.O1<.O1;.O1:.R1.(15.O4.O6.)R3.R2.)(6.(16.O1<.R3.(15.O4.O6.)O5.(17.O5.(18.(19.O4.))(18.(1:.O4.))(18.(1;.O4.))))(6.(1<.O1<.O1;.(15.O4.O6.)(10.&40.O18.)(1=.O4.)O2.R3.)(1>.O1<.O1;.R3.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_point_free_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_free ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1?.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O5.O4.O3.)PLB,(20.$21.)PA,$12.Pp,$22.Plo,$12.P,(14.O5.O4.O3.R5.R4.R7.R6.)P,(16.O5.R8.R5.R4.R3.)P,(23.R4.)P,(24.(25.R5.))P,(26.O4.(15.R6.R8.)(10.&40.R2;.)(13.O5.O4.O3.R9.)R7.$27.)P,Pa,$12.P,(6.(28.R9.R1.)(29.R1.(2:.R9.$27.)))P,(6.(28.(2;.O4.)R2.)(29.R2.(2<.O4.)))(2=.O4.R3.)P,(?.O5.R=.R7.(10.&40.R2=.))P,(28.R8.(2>.(2>.(10.&40.R2>.)+30.)(2?.O4.)))P,(28.(30.O4.)R9.)P,(28.(10.&40.R30.)(13.O5.O4.O3.R>.))P,(7.$12.(31.(10.&40.R31.)+10.)=)P,(28.(2<.O4.)(30.O4.))P,(7.(2.&40.)R31.(32.&40.(33.O4.)))P,(>.O5.R14.)P,(1>.O5.O4.R15.)P,(34.O4.O1.+8.)P,(7.$12.(31.(10.&40.R38.)+2.)=)P,(7.(2.&40.)R30.(32.&40.R14.))(35.O5.R18.(36.O5.O4.O3.R3:.R39.R38.R37.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R17.R16.R15.R14.R13.R19.R18.)(9.(:.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(32.&40.O2.)R1:.(<.(2.&40.))R19.(=.O5.)))")
(* [comment removed for export] *).

Section PF.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L12185607278.42L22538148649.42L39298410377.45L39461344833.42L50503687337.46L5246294680.45 L8895070966.46 00000600700>00?00H00O00YS1d2I2SS2d22J2FS2d12d21QS2d12I2S2d12d22NE". (* [comment removed for export] *)
  #[using="DIMG HND"] Lemma pt_sep_facts : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_free ()) "Pm,P,(2.&40.)(3.(2.&8.))Ph,(5.$37.VL,VHI,)PLB,(20.$21.)Pmo,$4.PA,$12.Pp,$22.PSP,$12.PTOP,$12.P,(14.$37.VL,VHI,R7.R6.R8.R5.)P,(16.$37.R9.R7.R5.R4.)P,(23.R5.)P,(24.(25.R6.))P,(26.VL,(15.R7.R:.)R6.R5.R8.$27.)P,(28.(2<.VL,)(30.VL,))P,(28.(30.VL,)R8.)ZX,$38.(19.R:.)ZY,$38.(1:.R;.)ZZ,$38.(1;.R<.)(6.P,(7.$39.(3:.R3.)$3;.)(6.(3<.(3=.$12.$12.)(3>.$12.$12.(3?.R4.)(40.+4.(41.R4.)))R11.)(6.(28.+1.(41.R4.))(6.(29.=(3?.R4.))(6.(28.(2:.(3?.R4.)(40.+4.(41.R4.)))(30.VL,))(42.(28.(2:.R?.+30.)(3?.R4.))(28.(2:.(3?.R4.)(40.+4.(41.R4.)))R?.))))))(6.P,(7.$39.(3:.R2.)$3;.)(6.(3<.(3=.$12.$12.)(3>.$12.$12.(3?.R3.)(40.+4.(41.R3.)))R11.)(6.(28.+1.(41.R3.))(6.(29.=(3?.R3.))(6.(28.(2:.(3?.R3.)(40.+4.(41.R3.)))(30.VL,))(42.(28.(2:.R?.+30.)(3?.R3.))(28.(2:.(3?.R3.)(40.+4.(41.R3.)))R?.))))))(6.P,(7.$39.(3:.R1.)$3;.)(6.(3<.(3=.$12.$12.)(3>.$12.$12.(3?.R2.)(40.+4.(41.R2.)))R11.)(6.(28.+1.(41.R2.))(6.(29.=(3?.R2.))(6.(28.(2:.(3?.R2.)(40.+4.(41.R2.)))(30.VL,))(42.(28.(2:.R?.+30.)(3?.R2.))(28.(2:.(3?.R2.)(40.+4.(41.R2.)))R?.))))))(6.P,(7.$39.(3:.R3.)$3;.)P,(7.$39.(3:.R3.)$3;.)(6.(43.(7.$12.(3?.R5.)(3?.R4.)))(42.(28.(2:.(3?.R5.)(40.+4.(41.R5.)))(3?.R4.))(28.(2:.(3?.R4.)(40.+4.(41.R4.)))(3?.R5.))))(6.P,(7.$39.(3:.R3.)$3;.)P,(7.$39.(3:.R2.)$3;.)(6.(43.(7.$12.(3?.R5.)(3?.R3.)))(42.(28.(2:.(3?.R5.)(40.+4.(41.R5.)))(3?.R3.))(28.(2:.(3?.R3.)(40.+4.(41.R3.)))(3?.R5.))))P,(7.$39.(3:.R2.)$3;.)P,(7.$39.(3:.R2.)$3;.)(6.(43.(7.$12.(3?.R4.)(3?.R3.)))(42.(28.(2:.(3?.R4.)(40.+4.(41.R4.)))(3?.R3.))(28.(2:.(3?.R3.)(40.+4.(41.R3.)))(3?.R4.)))))))))")
(* [comment removed for export] *).
  Proof.
    (intros m h LB mo A p SP TOP HH dd_H; ddestruct dd_H as (EX & EY & EZ & MX & MY & MZ); intros FRB DIS CW DHI ACL). cbv zeta.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof (HND _ _ _ _ HH) as ND. pose proof DIMG as [DI1 DI2].
    unfold mpds_distinct, pt_mpds in DIS. cbn [flat_map] in DIS. rewrite app_nil_r in DIS.
    assert (SUB : forall b, In b (pt_free_LB p LB) -> In b LB) by (intros b Hb; eapply lb_free_mpds_sub; exact Hb).
    assert (APART : forall d, In d (pt_mpds p) -> mpdr_at usegs m LB d -> md_own d = LHeap ->
              In (md_p d, 4 * md_n d) LB /\ 1 <= md_n d /\ 0 < md_p d /\ md_p d + 4 * md_n d <= alloc_ceiling /\ (A + 48 <= md_p d \/ md_p d + 4 * md_n d <= A)).
    { intros d Hd Md HO. destruct (mpdr_blk_facts _ L _ _ _ Md HO HBR) as (I1 & I2 & I3 & I4 & I5).
      refine (conj I1 (conj I2 (conj I3 (conj I4 _)))).
      eapply (client_apart_block L (pt_free_LB p LB) LB); try eassumption; try lia.
      unfold pt_free_LB. apply (lb_free_mpds_notin (pt_mpds p) LB d (4 * md_n d) ND Hd HO). }
    assert (PAIR : forall d1 d2, mpdr_at usegs m LB d1 -> mpdr_at usegs m LB d2 -> md_own d1 = LHeap -> md_own d2 = LHeap -> md_p d1 <> md_p d2 ->
              md_p d1 + 4 * md_n d1 <= md_p d2 \/ md_p d2 + 4 * md_n d2 <= md_p d1).
    { intros d1 d2 M1 M2 O1 O2 NE.
      destruct (mpdr_blk_facts _ L _ _ _ M1 O1 HBR) as (I1 & I2 & _). destruct (mpdr_blk_facts _ L _ _ _ M2 O2 HBR) as (J1 & J2 & _).
      destruct (blocks_apart_neq _ _ _ HAP I1 J1 ltac:(intros E; injection E; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia. }
    (* [comment removed for export] *)
    unfold mpd_blk in DIS.
    assert (NXY : md_own (pt_X p) = LHeap -> md_own (pt_Y p) = LHeap -> md_p (pt_X p) <> md_p (pt_Y p)).
    { intros O1 O2. rewrite O1, O2 in DIS. cbn [map app fst] in DIS.
      eapply (nodup_app_neq [md_p (pt_X p)]); [exact DIS| left; reflexivity| left; reflexivity]. }
    assert (NXZ : md_own (pt_X p) = LHeap -> md_own (pt_Z p) = LHeap -> md_p (pt_X p) <> md_p (pt_Z p)).
    { intros O1 O2. rewrite O1, O2 in DIS. rewrite map_app in DIS.
      eapply (nodup_app_neq [md_p (pt_X p)]); [exact DIS| left; reflexivity|]. rewrite map_app. apply in_app_iff. right. left. reflexivity. }
    assert (NYZ : md_own (pt_Y p) = LHeap -> md_own (pt_Z p) = LHeap -> md_p (pt_Y p) <> md_p (pt_Z p)).
    { intros O1 O2. rewrite O1, O2 in DIS. rewrite app_assoc, map_app in DIS.
      eapply (nodup_app_neq (map fst (match md_own (pt_X p) with LHeap => [(md_p (pt_X p), 4 * md_n (pt_X p))] | _ => [] end ++ [(md_p (pt_Y p), 4 * md_n (pt_Y p))])));
        [exact DIS| rewrite map_app; apply in_app_iff; right; left; reflexivity| left; reflexivity]. }
    split; [intros O; apply APART; [cbn; auto| exact MX| exact O]|].
    split; [intros O; apply APART; [cbn; auto| exact MY| exact O]|].
    split; [intros O; apply APART; [cbn; auto 6| exact MZ| exact O]|].
    split. { intros O1 O2. pose proof (NXY O1 O2) as NE. split; [exact NE| exact (PAIR _ _ MX MY O1 O2 NE)]. }
    split. { intros O1 O2. pose proof (NXZ O1 O2) as NE. split; [exact NE| exact (PAIR _ _ MX MZ O1 O2 NE)]. }
    intros O1 O2. pose proof (NYZ O1 O2) as NE. split; [exact NE| exact (PAIR _ _ MY MZ O1 O2 NE)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01f0@L11774327555.103L11803324323.134L11803470627.135L11805777061.106L11805777061.134L11805777061.136L11805777061.137L11805777061.158L11807744665.136L11807744665.137L11807744665.142L11807744665.143L11807744665.161L11807744665.167L11807744665.182L13294724630.106L17054295792.165L19028896459.71 L20433961190.102L21547146570.140L21547146570.141L22372402949.133L22542330283.89 L22706399685.190L22706555648.186L24944148252.186L25928528389.156L26879305446.180L26879568456.182L26879568840.181L26879597909.154L2696076359.154 L2696077255.131 L27107914355.106L27995947512.89 L28814043710.96 L31401241657.153L32049487064.102L32049487064.154L33950173099.131L3523383040.106 L3525463959.125 L3525463959.149 L3538239023.131 L37264779017.135L37275100814.159L37275258898.154L37703838106.180L37710127238.106L37710438837.158L3832275365.154 L39365853718.131L39367848461.134L40147640349.109L40147640349.134L40147640349.157L4080398682.133 L41523673725.154L41524258103.134L43059266230.100L43212011611.157L44208477419.106L44222670276.131L44277898736.159L44277898736.181L44282093003.104L44622288685.105L44622288685.106L45907855535.105L46470821627.180L46748113268.102L49298803087.181L49299045522.131L49300982921.134L49527944330.135L49528090634.134L49528090637.158L49528435006.106L49542610961.131L49542853772.182L49542853901.159L49698585326.105L49698585326.106L50056717204.106L50619921840.132L51042627268.106L51045145707.154L51045146603.131L53441994167.156L54391891673.106L54469099118.159L55777424165.108L56552377779.103L56552377779.154L56882896299.106L57449021840.154L59229011437.106L59235454146.131L59235454786.154L59308628179.97 L59454668182.181L5977185590.109 L5977185590.134 L5977185590.157 L61157862953.181L62916011878.131L63255844535.135L63748808489.135L63748808489.159L63976857485.135L63983151254.154L63983246858.159L67198666633.106L67432241517.131L67438241858.106L67669209322.158L67671128261.180L8276962772.158 00000<00g01R02802^03D03j04P04`05005@05P05`06006@06^06o07K07W07h08908I08U09A09m0:Q0:a0:m0;90;E0;Q0;R0;S0;T0<10<=0<I0<U0<a0<b0=G0=l0>Q0?60?B0?N0?Z0?f0@20@>0@[0@g0A30AF0AY0Al0BW0BX0Bd0CA0Cl0DD0D\0Dl0E<0Eg0F[0GR0Gm0H90HE0HQ0H]0Hi0I50IA0IM0IY0Ie0J10J=0J\0K>0KJ0KV0KW0KX0KY0Ke0LT0L`0M00M<0MH0MI0Ma0N60NK0N`0O=0OI0OZ0Ok0P<0PH0PI0PU0Pf0Q70QC0QO0Q[0Q\0RE0Rn0S:0SF0SRS2ra2sp1A2XBS1L3HLS2ra2sp1A2lo3SLO3SPA3SPB3ALX2XB2WH2K0S1L3HLS2ra2sp1A2lo3SLO3SPA3SPB3ALX2XB2WH2K0S1L3HLS2ra2sp1A1p2lo3SLO3ACL3SPB2XB2P4S1L3HLS2ra2sp1A1p2lo3SLO3ACL3SPB2XB2P4S1L3HLS2ra2sp1A1p2lo3SLO3ACL3SPB2XB2P4S1L3HLS2ra2sp1A1p2lo3SLO3ACL3SPB2XB2P4S1L3HLS2ra2sp1A1p2lo3SLO3ACL3SPB2XB2P4S2ra2sp1A1p2XB1HS2ra2sp1A1p2XB1HS2ra2sp1A1p2XB1HS2ra2sp1A1p2XB1HS2ra2sp1A1p2XB1HS2ra2sp1A1p2XB1HS2ra2sp1A1p2XB1HS2ra2sp2s01A2XB2HB5Ha_st5Hl_stS2ra2sp1A1p2XB2I5S1L3HLS2ra2sp2lo3SLO3ACL3SPBS2ra2sp1A2XBS2ra2sp1A1p2XB2I5S2ra2sp1A1p2XB2I5S2ra2sp1A1p2XB1HS2ra2sp1A2XBS1L3HLS2ra2sp1A2lo3SLO3ACL3SPB2XB1a1B1k1C2B4S2ra2sp1A2XB1a1C1L3HLS2lo3SLO3ACL3DHI3SPB2K0S2ra2sp1A1p2EX3SPB4XPOS2XB4ZPOS4YPOSS2ra2sp1A1p2XB1HS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBFFFS1L3HLS2ra2sp1A2lo3SLO3SPB2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBFS1L3HLS2ra2sp1A2lo3SLO3ACL3ACP3SPB2XBS1L3HLS2ra2sp1A2lo3SLO3ACL3ACP3SPB2XBS1L3HLS2ra2sp1A2lo3SLO3ACL3ACP3SPB2XBS1L3HLS2ra2sp1A2lo3SLO3ACL3ACP3SPB2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS1L3HLS2ra2sp1A2lo3SLO3SPB2XBS2ra2sp1A2XBS2ra2sp1A2XBS1L2ra2sp1A2XB1a2HdS1L2ra2sp1A2XB1a2HdS1L2ra2sp1A2XB1a2HdS1L3HLS2ra2sp1A2lo3SLO3SPA3SPB3ALX2XB2WH2K0FS2ra2sp1A2XBS1L3HLS2ra2sp1A2lo3SLO3SPB2XBS1L3HLS2ra2sp1A2lo3SLO3SPA3SPB3ALX2XB2WH2K0S1L2HI2ra2sp1h1A4HTOP2XBS1L2HI2ra2sp1h1A4HTOP2XBS2ra2sp1A1p2XB1HS2ra2sp1A1p2XB1HS1L3HLS2ra2sp1A2lo3SLO3SPA3SPB3ALX2XB2WH2K0S1L3HLS2ra2sp1A2lo3SLO3ACL3DHI3SPB2XB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s01A2lo3SLO3ACL3DHI3SPB2XB2HB5Ha_st5Hl_stS2ra2sp1A2XB2HB5Ha_st5Hl_stS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A3SPB2XB2HB5Ha_st5Hl_stS2ra2sp2s01A3SPB2XB2HB5Ha_st5Hl_stS2ra2sp1A2XBS2ra2sp1A2XBFFFS2ra2sp1A2XBS1L2HI3HLS2ra2sp1h1A2lo3SLO4HTOP3SPB2XB2K01a2NOS2ra2sp1A2XBS2ra2sp1A1p2XB1HS2ra2sp1A2XBS2ra2sp1A2XBFS1L2HI2ra2sp1h1A4HTOP2XBS1L2ra2sp1A2lo3SLO2XBS1L2ra2sp1A2lo3SLO2XBS1L2ra2sp1A2lo3SLO2XBS2ra2sp1A1p2EX3SPB4XPOS2XB2K0S2ra2sp1A2XBS2ra2sp1A2XB1a2HaS2ra2sp1A2XB1a2HaS2ra2sp1A2XB1a2HaS2ra2sp1A2XBFS2ra2sp1A2XBS2ra2sp1A2XB1a2HaS2ra2sp1A2XB1a2HaS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XBFS1L3HLS2ra2sp1A2lo3SLO3ACL3SPA3ACP3SPB2XBS1L3HLS2ra2sp1A2lo3SLO3ACL3SPA3ACP3SPB2XBS2ra2sp1A2XBS2ra2sp1A2XBS2ra2sp1A2XB". (* [comment removed for export] *)
  #[using="HFREE HLS SW DIMG HND"] Lemma U_ecp_point_free_spec : ecp_point_free_stmt usegs L HI U_ECP_POINT_FREE U_MEMSET_FUNC.
  Proof.
    unfold ecp_point_free_stmt, U_ECP_POINT_FREE. intros until lo.
    intros HH PT FRB DIS CW WD ST SLO ACL HTOP SPA DHI TP MI SOK CA RA ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof (HND _ _ _ _ HH) as ND. pose proof DIMG as [DI1 DI2].
    pose proof (pt_sep_facts _ _ _ _ _ _ _ _ HH PT FRB DIS CW DHI ltac:(lia)) as (FX & FY & FZ & FXY & FXZ & FYZ). cbv zeta in FX, FY, FZ, FXY, FXZ, FYZ.
    ddestruct PT as (EX & EY & EZ & MX & MY & MZ).
    assert (OX : md_own (pt_X p) <> LStatic) by (apply (proj1 (Forall_forall _ _) FRB); cbn; auto).
    assert (OY : md_own (pt_Y p) <> LStatic) by (apply (proj1 (Forall_forall _ _) FRB); cbn; auto).
    assert (OZ : md_own (pt_Z p) <> LStatic) by (apply (proj1 (Forall_forall _ _) FRB); cbn; auto 6).
    dpose MX as (CHX & ALX & XPOS & _). rewrite EX in CHX, ALX. pose proof (rw_cells_bound _ _ _ _ CHX) as XB. cbn [cells_size csize Nat.add mpi_cells] in XB. clear CHX.
    assert (HBR3 : Forall (fun b => block_range L (fst b) (snd b)) (pt_free_LB p LB))
      by (eapply block_range_forall_sub; [exact HBR| intros b Hb; eapply lb_free_mpds_sub; exact Hb]).
    pose proof (client_wrange_where' L _ _ _ A ECP_POINT_SIZE lo CW ltac:(unfold ECP_POINT_SIZE; lia) HBR3 DHI ACL ltac:(unfold ECP_POINT_SIZE; lia)) as WH.
    unfold ECP_POINT_SIZE in CW, WD, WH.
    (* [comment removed for export] *)
    set (LB1 := lb_free_mpd (pt_X p) LB). set (LB2 := lb_free_mpd (pt_Y p) LB1). 
    assert (E3 : pt_free_LB p LB = lb_free_mpd (pt_Z p) LB2) by reflexivity.
    assert (S10 : forall b, In b LB1 -> In b LB) by (intros b; subst LB1; apply lb_free_mpd_sub).
    assert (S21 : forall b, In b LB2 -> In b LB1) by (intros b; subst LB2; apply lb_free_mpd_sub).
    assert (S32 : forall b, In b (pt_free_LB p LB) -> In b LB2) by (intros b; rewrite E3; apply lb_free_mpd_sub).
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; rewrite ?land_7_mod in K1; lia|].
    pose proof (conj HH I) as HH0. clear HH. pose proof (lock MI) as MI00.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    destruct HH0 as [HH _].
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact MU| exact WM| exact ACL|]. intros a Ha NO. cbn in NO. left. lia. }
    assert (MX1 : mpdr_at usegs m1 LB (pt_X p)).
    { eapply (mpdr_at_munch usegs m m1); [exact MX| exact MU| exact WM| exact (unlock _ MI00)| assumption| rewrite EX; cbn; lia|].
      intros O. ddestruct (FX O) as (_ & _ & _ & P4 & _). cbn. lia. }
    pose proof (U_mpi_free_spec L HI HFREE HLS SW DIMG) as SPF. unfold mpi_free_stmt, U_MPI_FREE in SPF.
    eapply aevtM_cut.
    { unfold mpdr_at in MX1. rewrite EX in MX1.
      eapply SPF with (lo := lo) (h := h) (LB := LB); try eassumption; try reflexivity; rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by lia; try lia.
      - change (mpi_free_LB _ _ _ LB) with LB1. eapply (client_wrange_weak L); [exact CW| intros b Hb; apply S21, S32, Hb| lia| lia| lia].
      - intros O. ddestruct (FX O) as (_ & _ & _ & _ & ?). lia.
      - intros a Ha Hd. apply WD; lia.
      - exact ST. }
    cbv beta. intros ms' mo' PO. unfold mpi_free_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & CHX2 & PX2 & SOK2).
    change (mpi_free_LB _ _ _ LB) with LB1 in HH2, PX2.
    replace (ret_pc (Z_to_bv 64 0x384e8)) with (Z_to_bv 64 0x384e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (SUBX : sub_fp ((A, A + 16) :: mpi_free_X (md_own (pt_X p)) (md_p (pt_X p)) (md_n (pt_X p))) (pt_ivs p)).
    { intros a Ho. unfold pt_ivs, pt_mpds in Ho. cbn [flat_map] in Ho. rewrite !outside_app in Ho. ddestruct Ho as (Ho & _ & _ & _).
      unfold mpd_ivs in Ho. rewrite EX in Ho. unfold mpi_free_X. destruct (md_own (pt_X p)); cbn [outside app] in Ho |- *; tauto. }
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 FR ltac:(cbn; intros a Ha; left; lia)
                  ltac:(cbn; split; [lia|]; unfold mpi_free_X; destruct (md_own (pt_X p)); cbn; [exact I| | exact I];
                        ddestruct (FX eq_refl) as (_ & _ & _ & P4 & _); lia)) as FR2.
    assert (MY2 : mpdr_at usegs m2 LB1 (pt_Y p)).
    { eapply (mpdr_at_presx usegs L m1 m2); [| exact PX2| exact MI| exact MI2| | |].
      - eapply (mpdr_at_munch usegs m m1); [exact MY| exact MU| exact WM| exact (unlock _ MI00)| exact MI| rewrite EY; cbn; lia|].
        intros O. ddestruct (FY O) as (_ & _ & _ & P4 & _). cbn. lia.
      - rewrite EY. eapply (client_range_of_wrange L); [exact CW| intros b Hb; apply S21, S32, Hb| lia| lia| lia].
      - rewrite EY. cbn. split; [lia|]. unfold mpi_free_X. destruct (md_own (pt_X p)) eqn:OXE; cbn; [exact I| | exact I].
        ddestruct (FX eq_refl) as (_ & _ & _ & _ & ?). lia.
      - intros O. ddestruct (FY O) as (I1 & I2 & I3 & I4 & I5). split.
        + subst LB1. apply lb_free_mpd_keep; [exact I1|]. intros OX1. apply not_eq_sym. exact (proj1 (FXY OX1 O)).
        + cbn. split; [lia|]. unfold mpi_free_X. destruct (md_own (pt_X p)) eqn:OXE; cbn; [exact I| | exact I].
          destruct (FXY eq_refl O) as [_ ?]. lia. }
    assert (MZ2 : mpdr_at usegs m2 LB1 (pt_Z p)).
    { eapply (mpdr_at_presx usegs L m1 m2); [| exact PX2| exact MI| exact MI2| | |].
      - eapply (mpdr_at_munch usegs m m1); [exact MZ| exact MU| exact WM| exact (unlock _ MI00)| exact MI| rewrite EZ; cbn; lia|].
        intros O. ddestruct (FZ O) as (_ & _ & _ & P4 & _). cbn. lia.
      - rewrite EZ. eapply (client_range_of_wrange L); [exact CW| intros b Hb; apply S21, S32, Hb| lia| lia| lia].
      - rewrite EZ. cbn. split; [lia|]. unfold mpi_free_X. destruct (md_own (pt_X p)) eqn:OXE; cbn; [exact I| | exact I].
        ddestruct (FX eq_refl) as (_ & _ & _ & _ & ?). lia.
      - intros O. ddestruct (FZ O) as (I1 & I2 & I3 & I4 & I5). split.
        + subst LB1. apply lb_free_mpd_keep; [exact I1|]. intros OX1. apply not_eq_sym. exact (proj1 (FXZ OX1 O)).
        + cbn. split; [lia|]. unfold mpi_free_X. destruct (md_own (pt_X p)) eqn:OXE; cbn; [exact I| | exact I].
          destruct (FXZ eq_refl O) as [_ ?]. lia. }
    clear MX MY MZ MX1 FR ST MI HH HH1.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    zstep. zstep.
    (* [comment removed for export] *)
    eapply aevtM_cut.
    { pose proof MY2 as MY2'. unfold mpdr_at in MY2'. rewrite EY in MY2'.
      eapply SPF with (lo := lo) (h := h2) (LB := LB1); try eassumption; try reflexivity; rewrite ?(unsigned_lit (bv_unsigned sp + -16)), ?HT2 by lia; try lia.
      - change (mpi_free_LB _ _ _ LB1) with LB2. eapply (client_wrange_weak L); [exact CW| intros b Hb; apply S32, Hb| lia| lia| lia].
      - intros O. ddestruct (FY O) as (_ & _ & _ & _ & ?). lia.
      - intros a Ha Hd. apply WD; lia.
      - exact ST2. }
    cbv beta. intros ms' mo' PO. unfold mpi_free_post in PO.
    ddestruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & mo3 & h3 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by lia.
    ddestruct PO as (MI3 & ST3 & MF3 & HT3 & HH3 & CHY3 & PX3 & SOK3).
    change (mpi_free_LB _ _ _ LB1) with LB2 in HH3, PX3.
    replace (ret_pc (Z_to_bv 64 0x384f0)) with (Z_to_bv 64 0x384f0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (SUBY : sub_fp ((A + 16, A + 16 + 16) :: mpi_free_X (md_own (pt_Y p)) (md_p (pt_Y p)) (md_n (pt_Y p))) (pt_ivs p)).
    { intros a Ho. unfold pt_ivs, pt_mpds in Ho. cbn [flat_map] in Ho. rewrite !outside_app in Ho. ddestruct Ho as (_ & Ho & _ & _).
      unfold mpd_ivs in Ho. rewrite EY in Ho. unfold mpi_free_X. destruct (md_own (pt_Y p)); cbn [outside app] in Ho |- *; tauto. }
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX3 FR2 ltac:(cbn; intros a Ha; left; lia)
                  ltac:(cbn; split; [lia|]; unfold mpi_free_X; destruct (md_own (pt_Y p)); cbn; [exact I| | exact I];
                        ddestruct (FY eq_refl) as (_ & _ & _ & P4 & _); lia)) as FR3.
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX3 CHX2
                  ltac:(cbn; eapply (client_range_of_wrange L); [exact CW| intros b Hb; apply S32, Hb| lia| lia| lia])
                  ltac:(cbn; split; [lia|]; unfold mpi_free_X; destruct (md_own (pt_Y p)); cbn; [exact I| | exact I];
                        ddestruct (FY eq_refl) as (_ & _ & _ & _ & ?); lia)) as CHX3.
    assert (MZ3 : mpdr_at usegs m3 LB2 (pt_Z p)).
    { eapply (mpdr_at_presx usegs L m2 m3); [exact MZ2| exact PX3| exact MI2| exact MI3| | |].
      - rewrite EZ. eapply (client_range_of_wrange L); [exact CW| intros b Hb; apply S32, Hb| lia| lia| lia].
      - rewrite EZ. cbn. split; [lia|]. unfold mpi_free_X. destruct (md_own (pt_Y p)) eqn:OYE; cbn; [exact I| | exact I].
        ddestruct (FY eq_refl) as (_ & _ & _ & _ & ?). lia.
      - intros O. ddestruct (FZ O) as (I1 & I2 & I3 & I4 & I5). split.
        + subst LB2. apply lb_free_mpd_keep; [| intros OY1; apply not_eq_sym; exact (proj1 (FYZ OY1 O))].
          subst LB1. apply lb_free_mpd_keep; [exact I1| intros OX1; apply not_eq_sym; exact (proj1 (FXZ OX1 O))].
        + cbn. split; [lia|]. unfold mpi_free_X. destruct (md_own (pt_Y p)) eqn:OYE; cbn; [exact I| | exact I].
          destruct (FYZ eq_refl O) as [_ ?]. lia. }
    pose proof MY2 as MY2'. unfold mpdr_at in MY2'. rewrite EY in MY2'.
    clear MY2 MZ2 FR2 CHX2 ST2 MI2 HH2 MK2 MU2 WM2.
    pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    pose proof (munch_refl ([] : list ivl) m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
    zstep. zstep. zstep. zstep. release_frame FR3 ST3 (bv_unsigned sp). zstep.
    (* [comment removed for export] *)
    eapply aevtM_mono.
    { pose proof MZ3 as MZ3'. unfold mpdr_at in MZ3'. rewrite EZ in MZ3'.
      eapply SPF with (lo := lo) (h := h3) (LB := LB2); try eassumption; try reflexivity; rewrite ?HT3, ?HT2 by lia; try lia.
      - change (mpi_free_LB _ _ _ LB2) with (pt_free_LB p LB). eapply (client_wrange_weak L); [exact CW| intros b Hb; exact Hb| lia| lia| lia].
      - intros O. ddestruct (FZ O) as (_ & _ & _ & _ & ?). lia.
      - intros a Ha Hd. apply WD; lia. }
    cbv beta. intros c PO. unfold mpi_free_post in PO. unfold ecp_point_free_post.
    ddestruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & mo4 & h4 & -> & PO).
    ddestruct PO as (MI4 & ST4 & MF4 & HT4 & HH4 & CHZ4 & PX4 & SOK4).
    change (mpi_free_LB _ _ _ LB2) with (pt_free_LB p LB) in HH4, PX4.
    assert (SUBZ : sub_fp ((A + 32, A + 32 + 16) :: mpi_free_X (md_own (pt_Z p)) (md_p (pt_Z p)) (md_n (pt_Z p))) (pt_ivs p)).
    { intros a Ho. unfold pt_ivs, pt_mpds in Ho. cbn [flat_map] in Ho. rewrite !outside_app in Ho. ddestruct Ho as (_ & _ & Ho & _).
      unfold mpd_ivs in Ho. rewrite EZ in Ho. unfold mpi_free_X. destruct (md_own (pt_Z p)); cbn [outside app] in Ho |- *; tauto. }
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX4 CHX3
                  ltac:(cbn; eapply (client_range_of_wrange L); [exact CW| intros b Hb; exact Hb| lia| lia| lia])
                  ltac:(cbn; split; [lia|]; unfold mpi_free_X; destruct (md_own (pt_Z p)); cbn; [exact I| | exact I];
                        ddestruct (FZ eq_refl) as (_ & _ & _ & _ & ?); lia)) as CHX4.
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX4 CHY3
                  ltac:(cbn; eapply (client_range_of_wrange L); [exact CW| intros b Hb; exact Hb| lia| lia| lia])
                  ltac:(cbn; split; [lia|]; unfold mpi_free_X; destruct (md_own (pt_Z p)); cbn; [exact I| | exact I];
                        ddestruct (FZ eq_refl) as (_ & _ & _ & _ & ?); lia)) as CHY4.
    deexists 17. exists h4. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|].
    split. { eapply mo_frame_trans; [exact MF2|]. eapply mo_frame_trans; [exact MF3| exact MF4]. }
    split. { rewrite HT4, HT3, HT2. reflexivity. }
    split; [exact HH4|].
    split. { (* [comment removed for export] *)
      unfold ecp_point_at, pt_init. cbn [pt_X pt_Y pt_Z md_addr mpd_init].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      dpose MZ3 as (_ & ALZ & ZPOS & _). rewrite EZ in ALZ, ZPOS. dpose MY2' as (_ & ALY & YPOS & _).
      split; [| split]; apply mpdr_at_init; try assumption; lia. }
    split; [| exact SOK4].
    (* [comment removed for export] *)
    eapply heap_presx_trans.
    { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn.
      destruct Hc as [C|[C|([B k] & Hb & C)]]; [lia| lia|]. pose proof (proj1 (Forall_forall _ _) HBR3 _ Hb) as (_ & _ & _ & B4 & _). cbn in C, B4. lia. }
    eapply heap_presx_trans. { eapply (heap_presx_weak usegs L); [exact PX2| intros b Hb; apply S21, S32, Hb| lia| exact SUBX]. }
    eapply heap_presx_trans. { eapply (heap_presx_weak usegs L); [exact PX3| intros b Hb; apply S32, Hb| lia| exact SUBY]. }
    eapply (heap_presx_weak usegs L); [exact PX4| intros b Hb; exact Hb| lia| exact SUBZ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PF.
