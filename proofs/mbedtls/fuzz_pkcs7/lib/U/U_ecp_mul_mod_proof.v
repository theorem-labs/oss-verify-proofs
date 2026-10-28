(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts CrtFacts RepEcp EcpFacts EcpLoad. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_mul_stmt U_mpi_divmod_stmt U_mpi_grow U_mpi_cmp U_mpi_cmp_int U_mpi_bitlen U_mpi_core_sub U_mpi_core_add_if U_ecp_red U_ecp_mul_mod.
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
Ltac2 gd_tbl_P_ecp_mul_mod_proof () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.mm_base"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.mm_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.ecp_mul_mod_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.ECP_MUL_MOD_STACK"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_modp"].


Definition U_ECP_MUL_MOD : Z := 0x3a8f4.
Notation U_MUL_COUNT := 380840 (only parsing).   (* [comment removed for export] *)

Section MM.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Variable MT : list modp_ent.
  Hypothesis HMT : modp_table_ok usegs L HI MT U_MEMSET_FUNC.
  Hypothesis HMUL : mpi_mul_mpi_stmt usegs L HI U_MPI_MUL_MPI U_MEMSET_FUNC.
  (* [comment removed for export] *)
  Hypothesis HMOD : mpi_mod_mpi_stmt usegs L HI 0x21610 U_MEMSET_FUNC.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L1449694767.105 L23245287702.101L25810984855.104L4324751549.104 L50759778118.104L59397960598.101L67442728982.10100000=00B00G00L00Q00V00[S3spv2lo4LOSPS3spvS3spvS3spvS3spvS3spvS3spv". (* [comment removed for export] *)
  #[using="Type"] Lemma mm_exit : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod_proof ()) "Prae,(0.&40.)Pspv,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0e,(0.&40.)Ps1e,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pra0,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0c,(0.&40.)Ps1c,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$5.VL,VHI,)PLB,(6.$7.)PdX,$8.PG,$9.Pg,$:.Plo,$9.Ph1,(4.$5.VL,VHI,)PLB1,(6.$7.)PdX1,$8.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.Pr,$9.Pj8,(6.(0.&8.))P,(;.VL,R<.R;.R:.+5<?:8.(<.&40.R31.)+20.R8.(=.$5.VL,VHI,R=.)R9.)P,(>.$5.R10.R=.R<.)P,(?.$5.VL,VHI,VMT,R?.R>.R=.R<.R;.+5<?:8.(<.&40.R33.)+20.R:.R11.R10.R9.R8.R7.R6.R5.)P,(10.$5.R7.(11.(<.&40.R34.)-20.)(12.$13.(14.#8.R4.)(12.$13.(15.R30.)(12.$13.(15.R31.)(12.$13.(15.R35.)(16.$13.))))))P,(17.(18.(19.(1:.+2.+1?.))R6.)(1;.R6.=))(1<.$5.R8.(1=.$5.VL,VHI,VMT,R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R16.R15.R12.R11.R10.R?.R>.+5<?:8.R=.R14.R13.)(1>.(1?.R27.(20.&40.(11.(<.&40.R36.)-20.))R35.R34.R26.R25.R24.R23.R22.(20.&40.R7.)R21.R20.R1?.R1>.R1=.R1<.R1;.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R1:.R19.R18.R17.)R16.(20.&40.+3:920.)R15.(21.(0.&40.))R9.(22.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until j8. intros BASE MA INV FR Hr.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    ddestruct INV as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1).
    replace (bv_unsigned spv - 32) with (bv_unsigned spv + -32) in ST1 by lia. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    zstep. zstep. zstep. release_frame FR ST1 (bv_unsigned spv). zstep.
    try (replace (bv_unsigned spv + -32 + 32) with (bv_unsigned spv) by lia; rewrite (Z_to_bv_bv_unsigned spv)). zstep.
    apply aevtM_done. unfold ecp_mul_mod_post.
    deexists 14. dexists m1, mo1, h1, LB1, dX1, r, cnt1.
    split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact MF1|]. split; [exact HT1|].
    split; [exact HH1|]. split; [exact MA1|]. split; [exact OUT1|]. split; [exact PX1|]. split; [exact SOK1|].
    split; [exact GR1|]. split; [exact CNT1|].
    unfold mul_mod_R, binop_keep. destruct OUT1 as (EA1 & _). exact (conj Hr (conj EA1 (conj PAD1 (conj FR1 NLE1)))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L25810984371.105L33827146007.115L3616170738.7   L37156581414.15 L56093819244.114L61287023215.109L62723200766.15 00000500<00W00h00o01001;S3spvS3dX11lS1L3spv2lo3MC23ACL4LOSP3DHIS1L3dX13MC13MC21nS3dX11lSS3dX12N12n0". (* [comment removed for export] *)
  #[using="DIMG"] Lemma mm_fin : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod_proof ()) "Prae,(0.&40.)Pspv,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0e,(0.&40.)Ps1e,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pra0,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0c,(0.&40.)Ps1c,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$5.VL,VHI,)PLB,(6.$7.)PdX,$8.PG,$9.Pg,$:.Plo,$9.Ph1,(4.$5.VL,VHI,)PLB1,(6.$7.)PdX1,$8.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.Pj8,(6.(0.&8.))P,(;.VL,R;.R:.R9.+5<?:8.(<.&40.R31.)+20.R7.(=.$5.VL,VHI,R<.)R8.)P,(>.$5.R?.R<.R;.)P,(23.(1;.(11.(24.R<.)+10.)R9.)(1;.(<.&40.R33.)(24.R<.)))P,(?.$5.VL,VHI,VMT,R?.R>.R=.R<.R;.+5<?:8.(<.&40.R34.)+20.R:.R11.R10.R9.R8.R7.R6.R5.)P,(10.$5.R7.(11.(<.&40.R35.)-20.)(12.$13.(14.#8.R5.)(12.$13.(15.R31.)(12.$13.(15.R32.)(12.$13.(15.R36.)(16.$13.))))))(1<.$5.R7.(1=.$5.VL,VHI,VMT,R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R15.R14.R11.R10.R?.R>.R=.+5<?:8.R<.R13.R12.)(1>.(1?.R27.(20.&40.(11.(<.&40.R36.)-20.))R35.R34.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R19.R18.R17.R16.)R15.(20.&40.+3:9<4.)R14.(21.(0.&40.))R8.(22.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until j8. intros BASE MA SX0 INV FR. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU). clear SX. rename SX0 into SX.
    dpose INV as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1).
    replace (bv_unsigned spv - 32) with (bv_unsigned spv + -32) in ST1 by lia. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    pose proof (munch_refl [(U_MUL_COUNT, U_MUL_COUNT + 8)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    pose proof (lock FR) as FRL. pose proof (lock MA1) as MAL. clear FR HH1 SOK1 GR1 PX1.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    pose proof (rw_cells_transport usegs _ _ _ _ _ (unlock _ FRL) MU WM ltac:(cbn; clear - MC2 DHI ACL LOSP; lia)) as FR.
    assert (INV2 : mm_inv usegs L HI MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 32 lo m mo h1 LB1 dX1 m2 mo1).
    { rewrite <- (relimb_self dX1).
      eapply mm_inv_munch; [exact DIMG| exact BASE| exact MA| exact INV| | exact WM| assumption| | intros; reflexivity| exact CNT1 |].
      - eapply munch_weaken; [| exact MU]. unfold sub_fp, mm_fp. intros xx Hxx. rewrite outside_app in Hxx. destruct Hxx as [_ Hxx]. cbn in Hxx |- *. tauto.
      - intros O. pose proof (unlock _ MAL) as [(_ & _ & _ & HL & _ & HO) _]. rewrite O in HO. ddestruct HO as (N1 & IN & _ & U).
        split; [| exact HL]. eapply u32arr_transport; [exact U| exact MU| exact WM|]. cbn. split; [| exact I]. rewrite HL.
        destruct (Z_le_dec (380840 + 8) (md_p dX1)); [right; lia|]. destruct (Z_le_dec (md_p dX1 + 4 * md_n dX1) 380840); [left; lia|]. exfalso.
        pose proof INV as (HH1 & _). clear - n n0 HH1 IN N1 MC1 MC2 DIMG.
        apply (blk_off_data usegs L HI DIMG _ _ _ _ _ _ (Z.max (md_p dX1) 380840) HH1 IN); lia.
      - first [assumption| eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM| cbn; clear - MC2 DHI ACL; lia]]. }
    zstep. eapply mm_exit; [exact BASE| exact MA| exact INV2| exact FR| lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01P0@L10313711087.156L1040543275.193 L11899552194.36 L13400090657.192L13449400078.32 L13449527305.36 L1386329633.172 L14434235674.136L14438741258.155L16697148853.262L17702764939.22 L1889625374.32  L19628483746.137L19630209780.2  L20259420115.36 L2288039837.32  L2288171162.36  L23258591603.137L24101795768.206L24101795768.231L25069776940.17 L25069776940.18 L25810984371.108L25810984371.131L25810984372.237L25810984375.262L25812997173.189L25964389401.36 L28002796601.36 L28002929470.32 L30618038634.212L30857223105.8  L32080887660.155L32555299566.193L32557369198.194L3532165547.36  L3532299948.32  L35651110259.206L35651110259.231L37155097637.22 L38053132975.192L3820915402.156 L38920017927.36 L38920148736.32 L39333773652.36 L39333908051.32 L40380495452.156L4125635279.36  L4125769160.32  L42097324645.194L45290897527.32 L45291030007.156L45291032432.36 L47115702453.155L47501761478.36 L48164758032.185L48736977073.211L49964388807.36 L49964523200.32 L50264906177.8  L51163419001.211L52149425536.155L52772328477.142L53444088118.239L54379423251.206L54379423251.231L54412312985.156L55808010801.133L56470958949.240L57626602888.18 L57705804489.36 L57705938382.32 L58382421656.32 L58382549407.36 L59308628304.178L59355459711.116L59427867934.137L59543554885.238L59543554885.263L6034832555.32  L6034961324.36  L61647693725.36 L64793413023.188L65054675075.191L66565574423.32 L6885061525.186 L7143015064.137 L7190686615.176 L7192832305.262 L7192832306.239 L7192832773.239 L7192832787.214 L7192915893.156 L7202971817.239 L7202971817.264 L8927509794.212 00000B00T01802^03803Z03[04104C04n05M06<06=06D07=08509509<09W0::0;60;g0;l0<10<T0=?0=K0>B0?00?a0@S0A10A=0Ao0Ba0Bb0Bc0C>0Ca0D:0DK0D`0EA0EZ0FH0Fn0GE0GF0GG0GY0H^0I]0Jj0KV0La0Lm0Mh0NV0O<0OZ0PL0Pl0Q80Q[0R90R_0SL0SQ0TP0U@0Ua0V:0Vm0Wh0XL0X]0X^0YC0Z00Z10Z20Z30ZT0\00]30]C0]J0^D0_a0a60bK0cX0dR0e70ed0f_S1L3spv1G1g3DHI2wsS3spv1G1g3dX12ws1KS3spv1g3dX11K3dX33PB11c3xs44Hc013XL4S1L3HLS4DIMG4IMGC3spv2dX1G1g2lo3LB13dX12SX3SLO3GNZ3SPB2GX3MC13MC23MCX3MCG3ACL3DHI2GS4GPOS5Bmodp2ws1K1HS3spv1g3dX11K3dX34PPOS3PB1S3spv1g3dX11K3dX34PPOS3PB13xs43XL4FS2MT3spv1G1g3GNZ5GRESTS3spv1G1g5Bmodp2wsS3spv1G1g3dX11K3dX33PB03PB13xs43XL43xs53XL5S1g3dX11K3KGE3dX32N33PHL3PN12n0S1L3HLS3spv1g2lo3dX13SLO3SPB1K3dX33XI34PPOS3PB1FS1g3PHNS3spv1g3dX13SPB1K3KGE3dX32N33XI33XHL3PHL4PPOS3PB13xs43XL4S1L4IMGC3spv1g2lo3dX13SPB3ACL1K3dX33XI33PHL4PPOS3PB13PR1S1L4IMGC3spv1g2lo3dX13SPB3ACL1K3dX33XI33PHL4PPOS3PB13PR13xs43XL4S3spv1GS3spv1G1g3dX11K3dX33PB03PB1S3spv1G1g3dX11K3dX33PB03PB13xs43XL4S1L3HLS3spv1G1g2lo3dX13SLO2GS1K3KGE3dX32N33GX33PHL2dX2SX3XP3S1L3HLS3spv1g2lo3dX13SLO3ACL1K3KGE3dX32N33XI43PHLS3spvS3spvS3spv1G1g3dX11K3dX33PB03PB13xs43XL4S3spv1G1g3dX11K3dX33PB03PB13xs43XL43xs53XL5S3spv1G1g2wsS1L3HLS3spv1g2lo3dX13SLO3SPB1K3dX33XI34PPOS3PB13xs43XL4S3spv1g3dX13SPB1K3dX33XI33PHL4PPOS3PB13xs43XL4S3spv1g3dX13SPB1K3KGE3dX32N33XI33XHL3PHL4PPOS3PB1S3spv1G1g3dX13SPB4GPOS5Bmodp1K3dX33XI33PN13PB03PB1S1L3HLS3spv2lo3SLO3MC23ACL3DHIS3spv1G1g2wsS1L3HLS3spv1G1g2lo3dX13SLO3SPB3ACL4GPOS5Bmodp2ws1KS1L3HLS3spv1G1g2lo3dX13SLO3SPB3ACL4GPOS5Bmodp2ws1KFFS3spv1G1g3dX11K3dX33PB03PB1S3spv1G1g3dX11K3dX33PB03PB13xs43XL4S1L1g3dX13MC13MC21K3dX31nS3spv1G1g2ws1a2HaS1L3spv1G1g2lo3ACL2wsS3spv1g3dX11K3dX33PHN3PB13xs43XL4S3spv1g3dX11K3dX33PHN3PB1S3spv1g3dX13SPB1K3dX33XI33XAL4PPOS3PB13xs43XL4S3spv1g3dX13SPB1K3dX33XI33XAL4PPOS3PB1S1L2HI3spv1h1G1g3SPT2wsFFS3spv1G1g3dX12ws1KS1L3HLS4IMGC3spv1g2lo3dX13SLO4SPA03SPB3ACL1K3dX33XI33PAL4PPOS3PB13PR0S1L3HLS4DIMG4IMGC3spv1G1g2lo3SLO4SPA03SPB3MC23ACL4GPOS5Bmodp2wsS1L3HLS4IMGC3spv1g2lo3dX13SLO4SPA03SPB3ACL1K3dX33XI33PAL4PPOS3PB13PR03xs43XL4S1L3HLS3spv1G1g2lo3SLO3SPB3ACL4GPOS5Bmodp2wsS1L3spv1g3dX13SPB1K3dX32N33XI33XI53XHL3XAL3PHL3PAL4PPOS3PB13PR03PR13xs43XL4S3spv1G1g2wsS3spv1G1g3dX13SPB4GPOS5Bmodp1K3dX33XI33PHL3PN14PPOS3PB03PB1S3spv1g3dX13SPB1K3dX33XI33PAL4PPOS3PB13xs43XL4S3spv1g3dX13SPB1K3dX33XI33PAL4PPOS3PB1S1L3HLS3spv2lo3SLO3MC23ACL3DHIS3spv1G1g3dX13SPB4GPOS5Bmodp1K3dX33XI33PN13PB03PB1S3spv1G1g3SPB4GPOS5Bmodp2ws4EVENS3spv1G1g2r1S3spv1G1g3dX11K3dX33PB03PB13xs43XL4S3spv2dX1G1g3dX11K3dX33PB03PB1S3spv2dX1G1g3dX11K3dX33PB03PB13xs43XL4S1L3spv1G1g2lo3SLO3SPB4GPOS5Bmodp2ws3STK4STKBS3spvS3spv1G1g3dX13SPB4GPOS5Bmodp1K3dX33XI33PHL3PB03PB13xs43XL41i2HiS1L3HLS3spv1g2lo3dX13SLO1K3KGE3dX32N33PHL2xx3HxxS3spv1g3dX11K3dX33XI33PB13xs43XL4S3spv1g3dX11K3dX33XI33PB1S1L3spv1g2lo3dX13SPB3ACL1K3dX33XI33XI43XHL4PPOS3PB1S1L3spv1g2lo3dX13SPB3ACL1K3dX33XI33XI43XHL4PPOS3PB13xs43XL4S3spv1G1g3SPB4GPOS5Bmodp2ws2r22Er2K1S1L3spv3LB13dX11HFS3spv1G1g3dX11K3dX33PB03PB13xs43XL41lS3spv1G1g3dX11K3dX33PB03PB13xs43XL43xs53XL51lFFFS3spv1G1g3dX13SPB4GPOS5Bmodp2ws1KS1L3HLS4DIMG4IMGC3spv2dX1G1g2lo3dX12SX3SLO3GNZ3SPB2GX3MC23MCX3MCG3ACL3DHI2GS4GPOS5Bmodp2ws1KS1L3spv1g3dX13SPB1K3dX32N33XI33XI53XHL3XAL3PHL3PAL4PPOS3PB13PR03PR1S3spv1G1g3dX12wsS3spv1GS1L3HLS4DIMG4IMGC3spv1G1g2lo3SLO3SPB3MC23ACL4GPOS5Bmodp2wsS1L3HLS4DIMG4IMGC3spv1G1g2lo3dX13SLO3SPB3MC23ACL4GPOS5Bmodp1K3dX33XI33PB03PB13xs43XL43xs53XL5S1L3HLS4DIMG4IMGC3spv1G1g2lo3dX13SLO3SPB3MC23ACL4GPOS5Bmodp1K3dX33XI33PB03PB13xs43XL4S1L3HLS4DIMG4IMGC3spv1G1g2lo3dX13SLO3SPB3MC23ACL4GPOS5Bmodp1K3dX33XI33PB03PB13xs43XL4S1L3HLS4DIMG4IMGC3spv1G1g2lo3dX13SLO3SPB3MC23ACL4GPOS5Bmodp1K3dX33XI33PB03PB1S1L3HLS4DIMG4IMGC3spv1G1g2lo3SLO3SPB3MC23ACL4GPOS5Bmodp2wsS3spv1G1g3dX11K3dX33PB03PB13xs43XL41lS3spv1G1g3dX11K3dX33PB03PB13xs43XL43xs53XL51lS3spv1G1g3dX13SPB4GPOS5Bmodp1K3dX33XI33PHL3PN14PPOS3PB03PB1". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HMT"] Lemma mm_tail : ltac2:(CDefT.buildp (gd_tbl_P_ecp_mul_mod_proof ()) "Prae,(0.&40.)Pspv,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0e,(0.&40.)Ps1e,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pra0,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$5.VL,VHI,)PLB,(6.$7.)PdX,$8.PG,$9.Pg,$:.Plo,$9.Ph1,(4.$5.VL,VHI,)PLB1,(6.$7.)PdX1,$8.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.Pj8,(6.(0.&8.))P,(;.VL,R;.R:.R9.+5<?:8.(<.&40.R2?.)+20.R7.(=.$5.VL,VHI,R<.)R8.)P,(>.$5.R?.R<.R;.)P,(23.(1;.(11.(24.R<.)+10.)R9.)(1;.(<.&40.R31.)(24.R<.)))P,(?.$5.VL,VHI,VMT,R?.R>.R=.R<.R;.+5<?:8.(<.&40.R32.)+20.R:.R11.R10.R9.R8.R7.R6.R5.)P,(10.$5.R7.(11.(<.&40.R33.)-20.)(12.$13.(14.#8.R5.)(12.$13.(15.R2?.)(12.$13.(15.R30.)(12.$13.(15.R34.)(16.$13.))))))P,(25.(0.&40.)R32.(20.&40.(26.VL,)))P,(27.VL,$28.+8.)P,(1;.R>.(29.(29.(<.&40.R36.)$2:.)(2;.VL,)))P,(25.$9.(2<.(<.&40.R37.)+10.)=)P,(2=.(25.$9.(2>.R11.)=))(1<.$5.R<.(1=.$5.VL,VHI,VMT,R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R1:.R19.R16.R15.R14.R13.R12.+5<?:8.R11.R18.R17.)(1>.(1?.R2:.(20.&40.(11.(<.&40.R39.)-20.))R38.R37.R29.R28.R27.(20.&40.(24.R14.))(20.&40.R13.)R26.R25.R24.R23.R22.R21.R20.R1?.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R1>.R1=.R1<.R1;.)R1:.(20.&40.+3:958.)R19.(21.(0.&40.))R=.(22.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until j8. intros BASE MA SX0 INV FR TP CA SLO SPA0 GNZ. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB. unfold ECP_MUL_MOD_STACK in SLO.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU). clear SX. rename SX0 into SX.
    dpose INV as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1).
    replace (bv_unsigned spv - 32) with (bv_unsigned spv + -32) in ST1 by lia. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    dpose OUT1 as (EA1 & NS1 & _). destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    assert (XL1 : md_own dX1 = LHeap -> 0 < md_p dX1 /\ md_p dX1 + 4 * md_n dX1 <= alloc_ceiling /\ In (md_p dX1, 4 * md_n dX1) LB1 /\ 1 <= md_n dX1
                                     /\ (md_p dX1 + 4 * md_n dX1 <= hl_img_lo L \/ hl_img_hi L <= md_p dX1)).
    { intros O. ddestruct (mpdr_blk_facts usegs L m1 LB1 dX1 (proj1 MA1) O HBR1) as (I1 & I2 & I3 & I4 & I5). auto 10. }
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof U_mpi_bitlen_spec as SB. unfold mpi_bitlen_stmt, U_MPI_BITLEN in SB.
    eapply aevtM_cut_evt; [exact MK| eapply SB with (LB := LB1) (dX := dX1); [exact MA1| intros O; pose proof (XL1 O); lia| exact MI1| rewrite EA1; reflexivity] |].
    clear SB. cbv beta. intros ms' PO. unfold mpi_query_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & r1 & -> & MUb & WMb & MIb & Hr1).
    replace (ret_pc (Z_to_bv 64 0x3a960)) with (Z_to_bv 64 0x3a960) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (INV2 : mm_inv usegs L HI MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 32 lo m mo h1 LB1 dX1 m2 mo1).
    { eapply mm_inv_callee; [exact DIMG| exact BASE| exact MA| exact INV| exact MUb| exact WMb| exact MIb| unfold sub_fp; cbn; intros; exact I|].
      eapply stk_transport_disjoint; [exact ST1| exact MUb| exact WMb| cbn; exact I]. }
    eapply rw_cells_transport in FR; [| exact MUb| exact WMb| cbn; exact I].
    clear INV HH1 MA1 PX1 SOK1 MI1 GR1 CNT1 ST1 MUb WMb cnt1.
    dpose INV2 as (HH1 & MA1 & _ & _ & _ & _ & PX1 & SOK1 & MI1 & _ & _ & GR1 & [cnt1 CNT1] & ST1).
    replace (bv_unsigned spv - 32) with (bv_unsigned spv + -32) in ST1 by lia.
    dpose GR1 as (GHD & GAL & GPOS & EP & EGA & EGB & EGN & MP & _ & _ & _ & _ & GTL & GREST). unfold grp_tail_cells in GTL.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply mm_exit; [exact BASE| exact MA| exact INV2| exact FR| lia].
    - clear K0. zstep. zstep. zstep.
      (* [comment removed for export] *)
      ddestruct GREST as (_ & Bpb & _ & _ & Bmodp & _ & _ & _ & _ & _ & _ & _ & GMO).
      destruct GMO as [Z0 | (lp & ws & INMT & ELP & EWS & OWNP & SGP)]; [exfalso; exact (GNZ Z0)|].
      destruct (HMT _ _ _ INMT) as (EVEN & K & STK & KGE & STKB & RED). unfold ECP_RED_STACK in STKB.
      rewrite (ret_pc_even (g_modp g)) by lia.
      pose proof (mpd_writable_out usegs L HI DIMG h1 LB LB1 m m2 mo1 (bv_unsigned spv) (bv_unsigned spv + -32) _ dX dX1 XW MA HH1 MA1 OUT1 FR1 ltac:(lia) ltac:(lia)) as XW1.
      rewrite <- HT1 in XW1.
      unfold ecp_reducer_stmt in RED.
      eapply aevtM_cut.
      { eapply RED with (lo := lo) (h := h1) (LB := LB1) (dX := dX1); rewrite ?(unsigned_lit (bv_unsigned spv + -32)) by lia;
          first [ exact HH1 | exact MA1 | exact NS1 | exact XW1 | exact TP | exact SOK1 | exact CA | exact MI1
                | rewrite EA1; reflexivity
                | match goal with |- stk _ _ _ _ => exact ST1 end
                | rewrite HT1; lia
                | lia
                | match goal with |- ?gg => idtac "REDCALLLEFT" gg end ]. }
      clear RED. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & mo3 & h3 & LB3 & dX3 & r2 & E & PO). injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned spv + -32)) in PO by lia.
      ddestruct PO as (MI3 & ST3 & MF3 & HT3 & HH3 & MA3 & OUT3 & PX3 & SOK3 & RR).
      replace (ret_pc (Z_to_bv 64 0x3a978)) with (Z_to_bv 64 0x3a978) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      ddestruct RR as (RR3 & FR3 & Hr3).
      assert (PAD3 : md_pad dX3 = md_pad dX1) by (destruct RR3 as [(_ & _ & _ & P3 & _)|[_ ->]]; [exact P3| reflexivity]).
      assert (NLE3 : md_n dX1 <= md_n dX3) by (destruct RR3 as [(_ & _ & N3 & _)|[_ ->]]; [rewrite N3|]; lia).
      assert (INV3 : mm_inv usegs L HI MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 32 lo m mo h3 LB3 dX3 m3 mo3).
      { eapply mm_inv_binop; [exact DIMG| exact BASE| exact MA| exact INV2| exact HH3| exact MA3| exact OUT3| exact FR3| exact PAD3| exact NLE3| | exact SOK3| exact MI3| exact MF3| exact HT3|].
        - replace (bv_unsigned spv - 32) with (bv_unsigned spv + -32) by lia. exact PX3.
        - replace (bv_unsigned spv - 32) with (bv_unsigned spv + -32) by lia. exact ST3. }
      eapply (heap_presx_rw_cells usegs L) in FR; [| exact PX3| cbn; intros a Ha; left; lia|].
      2:{ unfold mpd_ivs. rewrite EA1. destruct (md_own dX1) eqn:O1; cbn; (split; [lia|]); [exact I| | exfalso; congruence].
          split; [| exact I]. pose proof (XL1 eq_refl). lia. }
      clear HH1 MA1 PX1 SOK1 MI1 GR1 CNT1 ST1 GHD MP GTL XW1 MK cnt1.
      pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
      zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        eapply mm_exit; [exact BASE| exact MA| exact INV3| exact FR| exact Hr3].
      + (* [comment removed for export] *)
        destruct RR3 as [(_ & SG3 & N3 & P3 & O3)|[Er _]]; [| exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Er; lia]. clear K1.
        dpose INV3 as (_ & _ & _ & _ & _ & _ & PX3' & _ & _ & _ & _ & GR3 & [cnt3 CNT3] & _).
        pose proof OUT3 as (EA3 & _).
        destruct (heap_blocks _ _ HI _ _ _ _ HH3) as [HBR3 _].
        ddestruct (mpdr_blk_facts usegs L m3 LB3 dX3 (proj1 MA3) O3 HBR3) as (XI1 & XI2 & XI3 & XI4 & XI5).
        dpose INV3 as (_ & _ & OUT13 & FR13 & _).
        assert (GX3 : G + 192 <= md_p dX3 \/ md_p dX3 + 4 * md_n dX3 <= G).
        { eapply (new_limbs_apart_range usegs L HI) with (SP := bv_unsigned spv); [exact HH3| exact MA3| exact OUT13| exact FR13| lia| apply (proj1 DIMG)| apply (proj2 DIMG)| exact GCR| lia| exact GXL| exact O3]. }
        destruct (mpd_writable_out usegs L HI DIMG h3 LB LB3 m m3 mo3 (bv_unsigned spv) (bv_unsigned spv) _ dX dX3 XW MA HH3 MA3 OUT13 FR13 ltac:(lia) ltac:(lia)) as (_ & _ & XP3).
        specialize (XP3 O3). rewrite EA1 in EA3. rewrite EA3 in XP3.
        pose proof MA3 as [(CH3 & _ & _ & XHL & XHN & XHO) _]. rewrite O3 in XHO. ddestruct XHO as (_ & _ & XAL & XU). rewrite EA3 in CH3. unfold mpi_cells in CH3.
        unfold MPI_MAX_LIMBS in XHN.
        dpose GR3 as (_ & _ & _ & EP3 & _ & _ & _ & MP3 & _). unfold mpdr_at, mpi_at in MP3. rewrite OWNP, SGP, EP3 in MP3.
        ddestruct MP3 as (CHP & _ & _ & PHL & PHN & (PN1 & PAL & PPOS & PB & PRO)). unfold MPI_MAX_LIMBS in PHN. unfold mpi_cells in CHP.
        rewrite <- EWS in KGE.
        dpose PB as (PB0 & PB1 & _). rewrite u32s_length in PB1.
        pose proof (ROIMG _ (PRO 0 ltac:(lia)) ltac:(lia)) as PR0. rewrite Z.add_0_r in PR0.
        pose proof (ROIMG _ (PRO (4 * md_n (g_P g) - 1) ltac:(lia)) ltac:(lia)) as PR1.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        pose proof U_mpi_core_sub_spec as SPS. unfold mpi_core_sub_stmt, U_MPI_CORE_SUB in SPS.
        eapply aevtM_cut_evt; [exact MK| eapply SPS with (X := md_p dX3) (A := md_p dX3) (B := md_p (g_P g)) (n := md_n (g_P g)) (xs := md_limbs dX3) (ys := md_limbs dX3) (zs := md_limbs (g_P g)) (lo := lo);
          rewrite ?(unsigned_lit (bv_unsigned spv + -32)) by lia;
          first [ exact XU | apply u32arr_ro; exact XU | exact PB | left; split; reflexivity | exact MI3
                | match goal with |- stk _ _ _ _ => exact ST3 end
                | clear - XHL XHN PHL PHN PN1 KGE N3 XI2 XI3 XI4 XI5 XAL PAL PPOS PB1 PR0 PR1 IMGC ACL LOSP SLO SPA0 SPB HLS DIMG; unfold MPI_CORE_SUB_STACK; lia
                | reflexivity
                | rewrite zx16_small by (clear - PHN; lia); reflexivity
                | apply f_equal; lia
                | match goal with |- ?gg => idtac "SUBLEFT" gg end ] |].
        clear SPS. cbv beta. intros ms' PO. unfold mpi_core_sub_post in PO.
        ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & c & xs4 & -> & MU4 & WM4 & MI4 & Hc & Hc01 & XU4 & XL4 & _ & _ & ST4).
        rewrite ?(unsigned_lit (bv_unsigned spv + -32)) in MU4, ST4 by lia. unfold MPI_CORE_SUB_STACK in MU4.
        replace (ret_pc (Z_to_bv 64 0x3a990)) with (Z_to_bv 64 0x3a990) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        lazymatch type of Hc with ?v = _ => subst v end.
        assert (INV4 : mm_inv usegs L HI MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 32 lo m mo h3 LB3 (relimb dX3 xs4) m4 mo3).
        { eapply mm_inv_munch; [exact DIMG| exact BASE| exact MA| exact INV3| | exact WM4| exact MI4| intros _; split; [exact XU4| rewrite XL4; exact XHL]| rewrite O3; intros NO; exfalso; apply NO; reflexivity| |].
          - eapply munch_weaken; [| exact MU4]. unfold sub_fp, mm_fp. rewrite O3. cbn. intros xx Hxx. clear - Hxx KGE N3 PHL XHL XHN PHN SLO HLS LOSP. lia.
          - eapply rw_cells_transport; [exact CNT3| exact MU4| exact WM4| cbn].
            split; [| split; [clear - MC2 DHI ACL SLO HLS; lia| exact I]].
            destruct (Z_le_dec (380840 + 8) (md_p dX3)); [left; lia|]. destruct (Z_le_dec (md_p dX3 + 4 * md_n (g_P g)) 380840); [right; lia|]. exfalso.
            clear - n n0 HH3 XI1 MC1 MC2 KGE N3 PHL XHL PN1 DIMG.
            exact (blk_off_data usegs L HI DIMG _ _ _ _ _ _ (Z.max (md_p dX3) 380840) HH3 XI1 ltac:(lia) ltac:(lia)).
          - replace (bv_unsigned spv - 32) with (bv_unsigned spv + -32) by lia. exact ST4. }
        eapply rw_cells_transport in FR; [| exact MU4| exact WM4| cbn; clear - XI4 ACL SLO HLS LOSP KGE N3 PHL XHL PN1 SPB; lia].
        eapply rw_cells_transport in CHP; [| exact MU4| exact WM4| cbn; clear - GX3 GS KGE N3 PHL XHL PN1 SLO HLS; lia].
        eapply rw_cells_transport in CH3; [| exact MU4| exact WM4| cbn; clear - XP3 SX KGE N3 PHL XHL PN1 SLO HLS; lia].
        pose proof (bytes_at_static usegs m3 m4 _ _ MI3 MI4 PB ltac:(rewrite u32s_length; intros i Hi; apply PRO; lia)) as PB4.
        clear CNT3 PX3' GR3 MI3 ST3 PB.
        dpose INV4 as (HH4 & MA4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & GR4 & [cnt4 CNT4] & _).
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        pose proof U_mpi_core_add_if_spec as SPA. unfold mpi_core_add_if_stmt, U_MPI_CORE_ADD_IF in SPA.
        eapply aevtM_cut_evt; [exact MK| eapply SPA with (X := md_p dX3) (A := md_p (g_P g)) (n := md_n (g_P g)) (cond := c) (xs := xs4) (ys := md_limbs (g_P g)) (lo := lo);
          rewrite ?(unsigned_lit (bv_unsigned spv + -32)) by lia;
          first [ exact XU4 | exact PB4 | exact MI4
                | match goal with |- stk _ _ _ _ => exact ST4 end
                | clear - XHL XL4 XHN PHL PHN PN1 KGE N3 XI2 XI3 XI4 XI5 XAL PAL PPOS PB1 PR0 PR1 IMGC ACL LOSP SLO SPA0 SPB HLS DIMG Hc01; unfold MPI_CORE_ADD_IF_STACK; lia
                | reflexivity
                | rewrite zx16_small by (clear - PHN; lia); reflexivity
                | apply f_equal; lia
                | match goal with |- ?gg => idtac "ADDIFLEFT" gg end ] |].
        clear SPA. cbv beta. intros ms' PO. unfold mpi_core_add_if_post in PO.
        ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & c5 & xs5 & -> & MU5 & WM5 & MI5 & _ & _ & XU5 & XL5 & _ & _ & ST5).
        rewrite ?(unsigned_lit (bv_unsigned spv + -32)) in MU5, ST5 by lia. unfold MPI_CORE_ADD_IF_STACK in MU5.
        replace (ret_pc (Z_to_bv 64 0x3a9ac)) with (Z_to_bv 64 0x3a9ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (INV5 : mm_inv usegs L HI MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 32 lo m mo h3 LB3 (relimb (relimb dX3 xs4) xs5) m5 mo3).
        { eapply mm_inv_munch; [exact DIMG| exact BASE| exact MA| exact INV4| | exact WM5| exact MI5| intros _; split; [exact XU5| cbn; rewrite XL5, XL4; exact XHL]| cbn; rewrite O3; intros NO; exfalso; apply NO; reflexivity| |].
          - eapply munch_weaken; [| exact MU5]. unfold sub_fp, mm_fp. cbn. rewrite O3. cbn. intros xx Hxx. clear - Hxx KGE N3 PHL XHL XHN PHN SLO HLS LOSP. lia.
          - eapply rw_cells_transport; [exact CNT4| exact MU5| exact WM5| cbn].
            split; [| split; [clear - MC2 DHI ACL SLO HLS; lia| exact I]].
            destruct (Z_le_dec (380840 + 8) (md_p dX3)); [left; lia|]. destruct (Z_le_dec (md_p dX3 + 4 * md_n (g_P g)) 380840); [right; lia|]. exfalso.
            clear - n n0 HH3 XI1 MC1 MC2 KGE N3 PHL XHL PN1 DIMG.
            exact (blk_off_data usegs L HI DIMG _ _ _ _ _ _ (Z.max (md_p dX3) 380840) HH3 XI1 ltac:(lia) ltac:(lia)).
          - replace (bv_unsigned spv - 32) with (bv_unsigned spv + -32) by lia. exact ST5. }
        eapply rw_cells_transport in FR; [| exact MU5| exact WM5| cbn; clear - XI4 ACL SLO HLS LOSP KGE N3 PHL XHL PN1 SPB; lia].
        clear CNT4 GR4 MI4 ST4 PB4 XU4 INV4 HH4 MA4 CH3 CHP.
        dpose INV5 as (HH5 & MA5 & _ & _ & _ & _ & _ & SOK5 & _ & _ & _ & GR5 & [cnt5 CNT5] & _).
        (* [comment removed for export] *)
        zstep. eapply mm_fin; [exact BASE| exact MA| exact SX| exact INV5| exact FR].
  all: match goal with |- ?g => idtac "TAILLEFT" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01o0@L10311464659.117L10313448302.14 L10472341889.202L1055055788.162 L10598529703.150L11572453888.175L11803550370.116L11803635347.2  L11805728038.124L11807744665.118L11807744665.126L12679583119.175L12836565580.120L12838354676.158L1434441065.4   L14431684672.178L15320268189.149L16075583823.171L17309539751.150L19028698955.162L19427582228.114L19427582228.115L20708902209.174L21586389085.3  L21765854580.111L21887662552.110L22704459657.7  L2285897501.8   L23587552326.153L26688075343.152L27159012312.211L27775132660.111L28689727684.173L28692136132.102L29010565666.142L29638086697.153L29638086697.211L29644522319.153L30615961706.179L33510041944.111L33670901889.176L34007367317.119L34277666369.208L34277666374.150L34277741789.153L34277741789.155L34290115814.113L34292426641.176L35679229279.105L35754698159.117L35754698159.118L37155097637.15 L38076497014.158L38165030244.117L3818668534.117 L3820653643.14  L3820768891.8   L38443780194.117L38644968030.3  L39939241236.175L40147641242.152L41644202024.105L41930219402.150L41942636979.158L41942719415.117L43061838089.111L43590541400.150L43590542174.178L43781838460.105L44017249036.105L44144683615.151L44187194279.180L44622288685.117L44622288685.118L45290767222.14 L45290914118.8  L45293014731.117L45507176624.150L45775211520.105L47742574041.14 L48172539062.176L48736977073.178L48815712669.175L49698585326.117L49698585326.118L50249502089.14 L51050055863.208L51163419001.178L52616107219.107L52772329112.178L53134134743.157L53468504638.154L54391891673.118L54526711530.155L54856524135.176L58307207885.151L58573232431.8  L59308628433.1  L59314873579.178L59690697844.7  L61486692934.8  L62920051336.9  L62920558344.9  L62981818017.177L62981818017.178L63559401084.109L63672583894.15 L63887036889.152L65054675075.210L65054675076.152L65302243777.178L6549057253.159 L65502165646.102L65689164180.160L66083662040.111L68013097686.119L7143015064.143 L7190686615.137 L7190686615.195 L7190733058.175 L7190733187.158 L7190733961.117 L7192832355.176 L8929561634.179 L9302287983.163 L9716869748.110 L9868963787.178 00000:00D00E00K00Q00[01\01`02f03i04n05=05V06106=07T07e07f07l08G09<0:40:F0:O0:S0:W0:o0;F0;d0;o0=B0=F0=_0>40>50>>0>K0>S0>f0>j0?20@30@;0@?0@E0@K0@O0@U0@j0A@0AY0Ai0B;0BH0BU0Bb0Bo0C?0CH0Ca0D80D90D=0DC0DG0D\0Dk0E>0EF0EJ0EV0Eg0F\0GT0Ga0Gn0HZ0H^0Hk0I80IG0Ia0J00JJ0Jg0KB0KJ0K]0Le0Lk0M80MA0NQ0NZ0N`0Nk0O@0OD0OE0OR0OV0OW0Ol0P:0PH0PW0Pa0Pj0Qo0S00TF0T_0Tc0U10U50UA0UI0V00V[0WF0Wo0XV0Y?0YY0Yd0Yh0Z9S1L2sp3DHIS1L2sp3DHIFS2sp1rS2sp1rS2sp1G1g1rS1L3HLS4DIMG4IMGC2sp2dX1G2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB2SXS2spS1L3HLS4DIMG4IMGC2sp2dX1G2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB2SX1d2S4S1L3HLS4DIMG4IMGC2sp2dX1G2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB2SX1HS1L3HLS4DIMG4IMGC2sp2dX1G2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB2SX1d1HS2sp2dX1G1g1r1HS1L3HLS2sp2lo3SLO3ACL3SPBS1L3HLS2sp2lo3SLO3ACL3SPB1rS2sp1G2lo2GSS1L3HLS4DIMG4IMGC2sp2dX1G1g2lo2GS2GX3MC13MC23MCX3MCG3SLO3ACL3DHI3SPB2SX3LB23dX21r3GX21HS2sp3SPB1r3Hr22K0FS2sp1rS1L3HLS2sp2lo3SLO3ACL3SPB1rS1L3HLS4DIMG4IMGC2ra2sp2lo3MC23SLO3ACL2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2sp2s02lo3MC23SLO3ACL2HB5Ha_st5Hl_st2s1S2sp1G1g3dX21r3GX2S2dX1G2GXS2spS2spS1L3HLS2sp2lo3SLO2xx3HxxS1L4IMGC2sp1g2lo3ACL2R1S1L3HLS2sp2dX2lo3SLO3ACL3SPB1HS2sp2dX1G1HS1L3HLS4DIMG4IMGC2sp2dX1G1g2lo2GS2GX3MC13MC23MCX3MCG3SLO3ACL3DHI3SPB2SX3LB23dX21r1HS2spS1L3HLS2sp1g2lo3SLO3SPB1rS1L3HLS2sp2lo3SLO3SPBFS2sp1a2HaS2sp1g1r1a2HaS2sp1a1CS2sp1g3SPB1r2N13PB1S2spS2sp1g1rS1L3HLS4DIMG4IMGC2sp2dX1G2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB2SXS2sp1g1rS2spS2sp1rS2sp1rS2spS2sp1rS1L3HLS2sp2lo3SLO3SPBS2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_st2s1S1L2dX3MC13MC21nS1L2sp3dX21r2I32I4S1L2sp2lo3SLOS1L2sp2lo3ACLS1L2sp2lo3ACLS1L2sp2lo3ACLS1L2HI2sp1h4HTOPS2dX1G2GXS1L3HLS2sp1g2lo3SLO3SPB1rS1L2sp3MC13MC23SPB1a2HaFS2spS2sp1rS2spS1L3HLS2sp2lo3SLO3SPBS1L2sp2lo3SLO1rS1L2sp2lo3SLO3dX21rS2sp3SPBS2spS2sp2dX1G2GXS1L2sp1g1r3PB12R1S1L3HLS4DIMG4IMGC2ra2sp2lo3SLO3ACL3SPB2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2sp2s02lo3SLO3ACL3SPB2HB5Ha_st5Hl_st2s1S2sp4SPA03SPBS2sp4SPA03SPBS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL4SPA03SPBS2spS2sp2dX2lo2SXS1L2sp2lo3SLOS2sp1g3SPB1r2N1S2sp1g3SPB1r3PHL2N12P03PB1S2sp1G1g1r1a2HaS2ra2sp3SPB2HB5Ha_st5Hl_stS2sp2s03SPB2HB5Ha_st5Hl_st2s1S1L2HI2sp1h4HTOP3SPB2h23HT2S2sp1g1rS2sp1g3SPB1r2N13PB1S1L3HLS4DIMG4IMGC2sp2dX1G2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB2SX1a2Ha1CS2sp1rS2sp2lo3LO01rS2sp2dX1lS1L2HI3HLS4DIMG4IMGC2sp1h2dX1G2lo2GS2GX3MC23MCX3MCG3SLO3ACL4HTOP3DHI3SPB2SX1a2NOS2sp2dX1lS2sp1rS2sp2dX3MCXS1L3HLS2sp2lo3SLO3SPBS2K2FS2sp2dX2lo2SXS2spFS2sp2dX2lo2SX3dX23EA2S2sp1g3dX21r1HS2sp1g3dX21r1HS1L2sp2dX2I32I4S2dX2N12n0S2sp1a2HaS1L3HLS4DIMG4IMGC2sp2dX1G1g2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB2SX1rS1L3HLS4DIMG4IMGC2sp2dX1G2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB2SXS1L3HLS4IMGC2sp2dX1G1g2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB2SX2m23dX21r3PHO2R02R12I51HS1L2sp2lo3ACL3SPB3dX21r1HS2spS1L2sp3dX21r1HS2spS2sp2dX2lo1HS2sp1G1rS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPBS1L3HLS4DIMG4IMGC2sp1g2lo3MC23SLO3ACL3SPB1rS1L3HLS4DIMG4IMGC2sp1g2lo3MC23SLO3ACL3SPB1rS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB1rS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPBS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB1rS2sp1g3SPB1r3PHL2N12P03PB1S2sp1G1r2GPS2spS2sp1g3dX21r1a2Ha". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HMT HMUL HMOD"] Theorem U_ecp_mul_mod_spec : ecp_mul_mod_stmt usegs L HI MT U_ECP_MUL_MOD U_MEMSET_FUNC U_MUL_COUNT ECP_MUL_MOD_STACK.
  Proof.
    unfold ecp_mul_mod_stmt, U_ECP_MUL_MOD. intros until lo.
    intros HH GR H1 GPS GCR0 GS GX GXL MA MAA MAB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XSL CNT MC1 MC2 MCS MCX MCG ST SLO ACL HTOP SPA0 DHI TP MI SOK CA -> -> -> ->.
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    unfold ECP_MUL_MOD_STACK in SLO.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    dpose XW as (XCW & XD & XP).
    pose proof (client_wrange_where2 L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as SX.
    assert (XIN : forall b, In b (mpd_blk dX) -> In b LB).
    { intros b Hb. unfold mpd_blk in Hb. pose proof MA as [(_ & _ & _ & _ & _ & HO) _]. destruct (md_own dX); try (destruct Hb; fail).
      destruct Hb as [<-|[]]. ddestruct HO as (_ & IN & _). exact IN. }
    assert (GCR : client_range L LB (bv_unsigned sp) G 192).
    { intros a Ha. destruct (GCR0 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
    assert (BASE : mm_base L LB dX G U_MUL_COUNT (bv_unsigned sp) 32 lo (heap_top usegs L HI h) g).
    { unfold mm_base. repeat match goal with |- _ /\ _ => split end; try assumption; try lia. eapply (grp_X_ok_h1 usegs); [exact GR| exact H1]. }
    assert (XL : md_own dX = LHeap -> 0 < md_p dX /\ md_p dX + 4 * md_n dX <= alloc_ceiling).
    { intros O. ddestruct (mpdr_blk_facts usegs L m LB dX (proj1 MA) O HBR) as (_ & _ & I3 & I4 & _). lia. }
    (* [comment removed for export] *)
    pose proof (lock MI) as MI00. pose proof (lock SOK) as SOK00.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HH0. clear HH.
    carve_frame 32%nat ST. set (JJ := junk) in FR. clearbody JJ.
    do 9 zstep.
    destruct HH0 as [HH _].
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia. }
    assert (MA1 : mpd_at usegs m1 LB dX).
    { eapply mpd_at_munch; [exact MA| exact NST| exact MU| exact WM| cbn; lia| intros O; pose proof (XSL ltac:(rewrite O; discriminate)); cbn; lia]. }
    assert (OPA : forall d, mpd_at usegs m LB d -> opnd_sep dX d lo (bv_unsigned sp) -> mpd_at usegs m1 LB d).
    { (intros d Md dd_H; ddestruct dd_H as (S1 & S2 & S3 & S4 & S5)). eapply mpd_at_munch_any; [exact Md| exact MU| exact WM| cbn; lia| intros O; pose proof (S5 O); cbn; lia]. }
    pose proof (OPA _ MAA OA) as MAA1. pose proof (OPA _ MAB OB) as MAB1. clear OPA.
    assert (GR1 : ecp_group_at usegs MT m1 LB G g).
    { eapply ecp_group_at_munch; [exact GR| exact MU| exact WM| exact (unlock _ MI00)| assumption| cbn; lia| intros d Hd HO; exfalso; exact (grp_static_own usegs MT m LB G g d GR H1 Hd HO)]. }
    lazymatch type of CNT with rw_cells _ m1 _ _ => idtac | _ => eapply rw_cells_transport in CNT; [| exact MU| exact WM| cbn; lia] end.
    lazymatch goal with H : statics_ok usegs L m1 |- _ => rename H into SOK1
      | |- _ => pose proof (statics_ok_munch usegs L _ _ _ (unlock _ SOK00) MU ltac:(intros aa Ha _; cbn; lia)) as SOK1 end.
    assert (PX1 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX ++ [(U_MUL_COUNT, U_MUL_COUNT + 8)]) m m1) by (eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia]).
    clear MAA MAB GR MU WM MK. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    (* [comment removed for export] *)
    zstep.
    pose proof HMUL as SM. unfold mpi_mul_mpi_stmt, mpi_binop_stmt, U_MPI_MUL_MPI in SM.
    eapply aevtM_cut.
    { eapply SM with (lo := lo) (h := h) (LB := LB) (dX := dX) (dA := dA) (dB := dB); rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia;
        first [ exact HH1 | exact MA1 | exact MAA1 | exact MAB1 | exact SXA | exact SXB | exact SAB | exact NST | exact CRA | exact CRAL | exact CRB | exact CRBL
              | exact TP | exact SOK1 | exact CA | reflexivity
              | eapply opnd_sep_sp_mono; [eassumption| lia]
              | eapply mpd_writable_sp_mono'; [exact XW| lia]
              | intros O; pose proof (XSL O); lia
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia
              | match goal with |- ?gg => idtac "MULCALLLEFT" gg end ]. }
    clear SM. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & mo2 & h2 & LB2 & dX2 & r & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MA2 & OUT2 & PX2 & SOK2 & [Hr2 (EA2 & PAD2 & FR2 & NLE2)]).
    replace (ret_pc (Z_to_bv 64 0x3a91c)) with (Z_to_bv 64 0x3a91c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (INV2 : mm_inv usegs L HI MT h LB dX G g U_MUL_COUNT (bv_unsigned sp) 32 lo m mo h2 LB2 dX2 m2 mo2).
    { unfold mm_inv. refine (conj HH2 (conj MA2 (conj OUT2 (conj FR2 (conj PAD2 (conj NLE2 (conj _ (conj SOK2 (conj MI2 (conj MF2 (conj HT2 (conj _ (conj _ _))))))))))))).
      - eapply heap_presx_trans; [exact PX1|]. eapply heap_presx_weaken; [exact PX2| lia| intros a Ha; rewrite outside_app in Ha; exact (proj1 Ha)].
      - eapply (ecp_group_at_presx usegs L); [exact GR1| exact PX2| exact MI| exact MI2| intros a Ha; destruct (GCR a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C] | |].
        + unfold mpd_ivs. destruct (md_own dX) eqn:O; cbn; (split; [lia|]); [exact I| | exfalso; exact (NST eq_refl)]. split; [| exact I]. pose proof (GXL eq_refl). lia.
        + intros d Hd O. exfalso. exact (grp_static_own usegs MT m1 LB G g d GR1 H1 Hd O).
      - exists cnt. eapply heap_presx_rw_cells; [exact PX2| exact CNT| |]; cbn.
        + intros a Ha. right; left. split; [lia|]. apply (proj1 (MCS a ltac:(lia))).
        + unfold mpd_ivs. destruct (md_own dX) eqn:O; cbn; (split; [lia|]); [exact I| | exfalso; exact (NST eq_refl)]. split; [| exact I].
          pose proof MA1 as [(_ & _ & _ & _ & _ & HO) _]. rewrite O in HO. ddestruct HO as (N1 & IN & _).
          destruct (Z_le_dec (380840 + 8) (md_p dX)); [left; lia|]. destruct (Z_le_dec (md_p dX + 4 * md_n dX) 380840); [right; lia|]. exfalso.
          clear - n n0 HH1 IN N1 MC1 MC2 DIMG.
          apply (blk_off_data usegs L HI DIMG _ _ _ _ _ _ (Z.max (md_p dX) 380840) HH1 IN); lia.
      - replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia. exact ST2. }
    eapply (heap_presx_rw_cells usegs L) in FR; [| exact PX2| cbn; intros a Ha; left; lia|].
    2:{ unfold mpd_ivs. destruct (md_own dX) eqn:O; cbn; (split; [lia|]); [exact I| | exfalso; exact (NST eq_refl)]. split; [| exact I]. pose proof (XL eq_refl). lia. }
    clear HH1 MA1 MAA1 MAB1 GR1 CNT SOK1 PX1 MK. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    dpose INV2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GR2 & _).
    dpose GR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GTL2 & GREST2). unfold grp_tail_cells in GTL2.
    ddestruct GREST2 as (_ & _ & _ & _ & Bmodp & _).
    pose proof MA2 as [(CH2 & _) SG2]. rewrite EA2 in CH2. unfold mpi_cells in CH2.
    pose proof GR2 as (GHD2 & GAL2 & GPOS2 & _). pose proof MA2 as [(_ & XAL2 & _) _]. rewrite ?EA2 in XAL2.
    pose proof (rw_cells_bound _ _ _ _ GHD2) as GB2. pose proof (rw_cells_bound _ _ _ _ CH2) as XB2. unfold grp_head_cells in GB2. cbn [cells_size csize Nat.add] in GB2, XB2.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. if_cases KG0; zify_cond KG0; [exfalso; rewrite ?unsigned_lit in KG0 by lia; lia|].
      zstep. zstep. if_cases KG1; zify_cond KG1; [exfalso; rewrite ?unsigned_lit in KG1 by lia; rewrite ?land_7_mod in KG1; lia|].
      zstep. zstep. if_cases K1; zify_cond K1; rewrite ?Z.mod_small in K1 by lia.
      { (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        dpose INV2 as (_ & MA2' & _ & FR2' & _ & _ & _ & SOK2' & MI2' & _ & _ & _ & _ & ST2'). replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in ST2' by lia.
        dpose OUT2 as (_ & NS2 & _).
        destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 _].
        assert (XI : md_own dX2 = LHeap -> In (md_p dX2, 4 * md_n dX2) LB2 /\ 1 <= md_n dX2 /\ 0 < md_p dX2 /\ md_p dX2 + 4 * md_n dX2 <= alloc_ceiling
                                        /\ (md_p dX2 + 4 * md_n dX2 <= hl_img_lo L \/ hl_img_hi L <= md_p dX2)).
        { intros O. exact (mpdr_blk_facts usegs L m2 LB2 dX2 (proj1 MA2') O HBR2). }
        pose proof (mpd_writable_out usegs L HI DIMG h2 LB LB2 m m2 mo2 (bv_unsigned sp) (bv_unsigned sp + -32) _ dX dX2 XW MA HH2 MA2' OUT2 FR2' ltac:(lia) ltac:(lia)) as XW2.
        dpose XW2 as (XCW2 & _ & XP2).
        assert (GX2 : G + 192 <= md_p dX2 \/ md_p dX2 + 4 * md_n dX2 <= G).
        { destruct (md_own dX2) eqn:O2.
          - pose proof MA2' as [(_ & _ & _ & _ & _ & HO) _]. rewrite O2 in HO. destruct HO as [-> ->]. dpose GR2 as (_ & _ & GP & _). lia.
          - eapply (new_limbs_apart_range usegs L HI) with (SP := bv_unsigned sp); [exact HH2| exact MA2'| exact OUT2| exact FR2'| lia| apply (proj1 DIMG)| apply (proj2 DIMG)| exact GCR| lia| exact GXL| exact O2].
          - exfalso; congruence. }
        (* [comment removed for export] *)
        dpose GR2 as (_ & _ & GPOS' & EP2 & _ & _ & _ & MP2 & _).
        assert (POWN : md_own (g_P g) <> LHeap) by (apply (grp_static_own usegs MT m2 LB2 G g _ GR2 H1); cbn; auto).
        assert (MPB : mpd_at usegs m2 LB2 (g_P g)) by (split; [exact MP2| left; exact GPS]).
        dpose MP2 as (CHP & _ & _ & PHL & PHN & PHO). unfold MPI_MAX_LIMBS in PHN.
        assert (PST : md_own (g_P g) <> LNull -> 1 <= md_n (g_P g) /\ 0 < md_p (g_P g) /\ (forall i, 0 <= i < 4 * md_n (g_P g) -> ro_addr usegs (wa (md_p (g_P g) + i)) = true)
                                               /\ hl_img_lo L <= md_p (g_P g) /\ md_p (g_P g) + 4 * md_n (g_P g) <= hl_img_hi L).
        { intros NN. destruct (md_own (g_P g)) eqn:OP; [exfalso; congruence| exfalso; congruence|].
          ddestruct PHO as (N1 & _ & P0 & PB & PRO). dpose PB as (PB0 & PB1 & _). rewrite u32s_length in PB1.
          pose proof (ROIMG _ (PRO 0 ltac:(lia)) ltac:(lia)) as R0. rewrite Z.add_0_r in R0.
          pose proof (ROIMG _ (PRO (4 * md_n (g_P g) - 1) ltac:(lia)) ltac:(lia)) as R1.
          refine (conj N1 (conj P0 (conj PRO (conj (proj1 R0) _)))). lia. }
        assert (OPP : opnd_sep dX2 (g_P g) lo (bv_unsigned sp + -32)).
        { split; [| split; [| split; [| split]]].
          - intros NN; ddestruct (PST NN) as (N1 & P0 & PRO & _); rewrite EA2.
            exact (rw_ro_apart usegs _ _ _ (md_p (g_P g)) (4 * md_n (g_P g)) MI2' CH2 ltac:(cbn; lia) ltac:(lia) PRO).
          - intros O2; rewrite EP2; pose proof GX2; lia.
          - destruct (md_own dX2) eqn:O2; [right; left; congruence| | exfalso; congruence].
            destruct (md_own (g_P g)) eqn:OP; [right; right; left; reflexivity| exfalso; congruence|].
            right; right; right. ddestruct (PST ltac:(first [discriminate| congruence])) as (_ & _ & _ & R0 & R1). dpose (XI eq_refl) as (_ & _ & _ & _ & I5). pose proof DIMG. lia.
          - rewrite EP2; clear - GS; lia.
          - intros NN; ddestruct (PST NN) as (_ & _ & _ & R0 & R1); clear - R0 R1 IMGC ACL; lia. }
        assert (CRPS : client_range L LB2 lo (md_addr (g_P g)) 16).
        { rewrite EP2; eapply (client_range_out L); [intros a Ha; apply GCR; lia| exact OUT2| intros O; pose proof (GXL O); lia| lia]. }
        pose proof HMOD as SD. unfold mpi_mod_mpi_stmt, mpi_binop_stmt_nb in SD.
        eapply aevtM_cut.
        { eapply SD with (lo := lo) (h := h2) (LB := LB2) (dX := dX2) (dA := dX2) (dB := g_P g); rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia;
            first [ exact HH2 | exact MA2' | exact MPB | exact OPP | exact CRPS | left; reflexivity | exact NS2 | exact TP | exact SOK2' | exact CA | exact MI2'
                  | match goal with |- stk _ _ _ _ => exact ST2' end
                  | rewrite EA2; reflexivity | rewrite EP2; apply f_equal; lia
                  | (* [comment removed for export] *) right; rewrite EA2, EP2; clear - GX; lia
                  | (* [comment removed for export] *) rewrite EA2, EP2; clear - GX; lia
                  | (* [comment removed for export] *) split; [| split; [| split; [left; reflexivity| split]]];
                      [ intros NN; destruct (md_own dX2) eqn:O2; [exfalso; congruence| pose proof (XP2 eq_refl); lia| exfalso; congruence]
                      | intros O2; pose proof (XP2 O2); lia
                      | pose proof SX; pose proof EA2; clear - SX EA2 SLO HLS; lia
                      | intros NN; destruct (md_own dX2) eqn:O2; [exfalso; congruence| pose proof (XI eq_refl); lia| exfalso; congruence] ]
                  | (* [comment removed for export] *) split; [| split; [| split; [| split]]];
                      [ intros NN; ddestruct (PST NN) as (N1 & P0 & PRO & _); rewrite EA2;
                          exact (rw_ro_apart usegs _ _ _ _ _ MI2' CH2 ltac:(cbn; lia) ltac:(lia) PRO)
                      | intros O2; rewrite EP2; pose proof GX2; lia
                      | destruct (md_own dX2) eqn:O2; [right; left; congruence| | exfalso; congruence];
                        destruct (md_own (g_P g)) eqn:OP; [right; right; left; reflexivity| exfalso; congruence|];
                        right; right; right; ddestruct (PST ltac:(first [discriminate| congruence])) as (_ & _ & _ & R0 & R1); dpose (XI eq_refl) as (_ & _ & _ & _ & I5); pose proof DIMG; lia
                      | rewrite EP2; clear - GS; lia
                      | intros NN; ddestruct (PST NN) as (_ & _ & _ & R0 & R1); clear - R0 R1 IMGC ACL; lia ]
                  | (* [comment removed for export] *) rewrite EA2; eapply client_range_of_wrange; [rewrite <- EA2; exact XCW2| lia]
                  | (* [comment removed for export] *) intros O2 a Ha; right; right; exists (md_p dX2, 4 * md_n dX2); split; [exact (proj1 (XI O2))| cbn; lia]
                  | (* [comment removed for export] *) rewrite EP2; eapply (client_range_out usegs L HI DIMG); [intros a Ha; apply GCR; lia| exact OUT2| intros O; pose proof (GXL O); lia| lia]
                  | (* [comment removed for export] *) intros OP; exfalso; exact (POWN OP)
                  | (* [comment removed for export] *) rewrite <- HT2 in XW2; exact XW2
                  | intros NN; destruct (md_own dX2) eqn:O2; [exfalso; congruence| pose proof (XI eq_refl); lia| exfalso; congruence]
                  | clear - SLO HLS ACL SPA0 SPB HTOP HT2 DHI; lia
                  | match goal with |- ?gg => idtac "MODCALLLEFT" gg end ]. }
        clear SD. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
        ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & mo3 & h3 & LB3 & dX3 & r3 & E & PO). injection E as -> ->.
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
        ddestruct PO as (MI3 & ST3 & MF3 & HT3 & HH3 & MA3 & OUT3 & PX3 & SOK3 & [[_ Hr3] (EA3 & PAD3 & FR3 & NLE3)]).
        replace (ret_pc (Z_to_bv 64 0x3a9c0)) with (Z_to_bv 64 0x3a9c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (INV3 : mm_inv usegs L HI MT h LB dX G g U_MUL_COUNT (bv_unsigned sp) 32 lo m mo h3 LB3 dX3 m3 mo3).
        { eapply mm_inv_binop; [exact DIMG| exact BASE| exact MA| exact INV2| exact HH3| exact MA3| exact OUT3| exact FR3| exact PAD3| exact NLE3| | exact SOK3| exact MI3| exact MF3| exact HT3|].
          - replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia. exact PX3.
          - replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia. exact ST3. }
        eapply (heap_presx_rw_cells usegs L) in FR; [| exact PX3| cbn; intros a Ha; left; lia|].
        2:{ unfold mpd_ivs. rewrite EA2. destruct (md_own dX2) eqn:O2; cbn; (split; [lia|]); [exact I| | exfalso; congruence]. split; [| exact I]. pose proof (XI eq_refl). lia. }
        clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
        zstep. if_cases K5; zify_cond K5.
        - eapply mm_exit; [exact BASE| exact MA| exact INV3| exact FR| exact Hr3].
        - eapply mm_fin; [exact BASE| exact MA| exact SX| exact INV3| exact FR]. }
      zstep. zstep. if_cases KX; zify_cond KX; [exfalso; rewrite ?unsigned_lit in KX by lia; rewrite ?land_7_mod in KX; lia|].
      destruct SG2 as [E|E]; rewrite E in CH2.
      + (* [comment removed for export] *)
        zstep. rewrite (sx16_small 1) by lia. zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|]. clear K2.
        eapply mm_tail; [exact BASE| exact MA| exact SX| exact INV2| exact FR| exact TP| exact CA| unfold ECP_MUL_MOD_STACK; lia| exact SPA0| exact K1].
      + (* [comment removed for export] *)
        zstep. rewrite (sx16_small (-1)) by lia. zstep. if_cases K2; zify_cond K2; [| exfalso; clear - K2; lia]. clear K2.
        zstep. zstep. zstep.
        dpose INV2 as (_ & MA2' & _ & _ & _ & _ & _ & _ & MI2' & _ & _ & _ & _ & ST2'). replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) in ST2' by lia.
        dpose OUT2 as (_ & NS2 & _).
        destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 _].
        assert (XL2 : md_own dX2 = LHeap -> 0 < md_p dX2 /\ md_p dX2 + 4 * md_n dX2 <= alloc_ceiling).
        { intros O. ddestruct (mpdr_blk_facts usegs L m2 LB2 dX2 (proj1 MA2') O HBR2) as (_ & _ & I3 & I4 & _). lia. }
        assert (XS2 : md_p dX2 + 4 * md_n dX2 <= lo \/ bv_unsigned sp + -32 <= md_p dX2).
        { pose proof MA2' as [(_ & _ & _ & _ & _ & HO2) _]. destruct (md_own dX2) eqn:O2';
            [destruct HO2 as [-> ->]; left; lia| left; pose proof (XL2 eq_refl); lia| exfalso; congruence]. }
        pose proof U_mpi_cmp_int_spec as SC. unfold mpi_cmp_int_stmt, U_MPI_CMP_INT in SC.
        eapply aevtM_cut_evt; [exact MK| eapply SC with (LB := LB2) (dX := dX2) (z := 0) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia;
          first [ exact MA2' | exact MI2' | exact XS2
                | match goal with |- stk _ _ _ _ => exact ST2' end
                | rewrite EA2; reflexivity | reflexivity
                | intros O; pose proof (XL2 O); lia
                | clear - SLO HLS ACL SPA0 SPB; lia
                | rewrite EA2; clear - SX SLO HLS; lia
                | match goal with |- ?gg => idtac "CMPLEFT" gg end ] |].
        clear SC. cbv beta. intros ms' PO. unfold mpi_cmp_int_post in PO.
        ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MUc & WMc & MIc & STc).
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MUc, STc by lia.
        replace (ret_pc (Z_to_bv 64 0x3a9e8)) with (Z_to_bv 64 0x3a9e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (INV3 : mm_inv usegs L HI MT h LB dX G g U_MUL_COUNT (bv_unsigned sp) 32 lo m mo h2 LB2 dX2 m3 mo2).
        { eapply mm_inv_callee; [exact DIMG| exact BASE| exact MA| exact INV2| exact MUc| exact WMc| exact MIc| unfold sub_fp; cbn; intros xx Hxx; clear - Hxx SLO HLS; lia|].
          replace (bv_unsigned sp - 32) with (bv_unsigned sp + -32) by lia. exact STc. }
        eapply rw_cells_transport in FR; [| exact MUc| exact WMc| cbn; clear - SPB; lia].
        clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
        zstep. if_cases K3; zify_cond K3.
        * (* [comment removed for export] *)
          eapply mm_tail; [exact BASE| exact MA| exact SX| exact INV3| exact FR| exact TP| exact CA| unfold ECP_MUL_MOD_STACK; lia| exact SPA0| exact K1].
        * (* [comment removed for export] *)
          zstep. zstep. zstep.
          eapply mm_exit; [exact BASE| exact MA| exact INV3| exact FR| lia].
    - (* [comment removed for export] *)
      eapply mm_exit; [exact BASE| exact MA| exact INV2| exact FR| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr2; lia].
  all: match goal with |- ?g => idtac "MAINLEFT" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MM.
