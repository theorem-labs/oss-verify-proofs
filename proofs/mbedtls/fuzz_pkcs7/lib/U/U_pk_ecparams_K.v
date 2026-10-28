(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB Arr MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_ecp_grp_id_list U_ecp_point_free U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type U_pk_ecc_set_group U_ecp_sinv U_string U_oid U_oidv U_oid_ec_grp U_oid_ec_grp_v U_ecp_group_init U_mpi_cmp U_mpi_bitlen U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_C U_pk_ecparams_D U_pk_ecparams_E U_pk_ecparams_F U_pk_ecparams_G U_asn1_get_tag U_asn1_get_int U_asn1_get_mpi U_mpi_read_binary U_mpi_read_binary_proof U_mpi_lset U_pk_ecparams_H U_pk_ecparams_I U_pk_ecparams_J U_asn1_empty.
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
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac pnull K :=
  exfalso;
  repeat match type of K with context [?a <? ?b] =>
    first [ let E := fresh "E" in assert (E : (a <? b) = true) by (apply Z.ltb_lt; lia); rewrite E in K; clear E
          | let E := fresh "E" in assert (E : (a <? b) = false) by (apply Z.ltb_ge; lia); rewrite E in K; clear E ] end;
  vm_compute in K; first [ discriminate K | lia ].
Ltac2 gd_tbl_P_pk_ecparams_K () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_init"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_ok"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_H.SPINV"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.pk_use_ecparams_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_B.ctx_now"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].



(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0190?L10206227957.27L12765785589.27L13160509429.27L15049803981.24L15179708033.29L18735809977.29L19287471093.27L19924485877.27L22921368053.27L23486893045.27L23677733325.24L25201108725.27L26477994741.27L27367777525.27L27965486666.29L28368529909.27L28757224437.27L3091388405.27 L31925172981.27L34480536309.27L3486108149.27 L34875522293.27L36900485561.29L37460525045.27L38431621621.27L38517204298.29L39311286602.29L39467766858.29L40457111681.29L41643169781.27L41988264693.27L44013230977.29L44562781685.27L44648689397.27L4762998261.27 L48205329397.27L48758009333.27L50083530485.27L50478266613.27L50544853578.29L51509868493.24L52651214581.27L54034894325.27L54567107904.31L55522969147.24L56209951733.27L5646751733.27 L56992571210.29L58615223425.29L59181550837.27L59308579027.26L59308579027.29L59308579027.31L59308579281.27L59310679309.25L59314873579.26L59314873579.29L60073639629.24L60158959349.27L62173944761.29L62737666549.27L63135739341.24L63244367946.29L63372584181.27L63717680117.27L6450328635.24 L65098157005.24L66294293237.27L66363441141.27L6649600245.27 L66929224181.27L7042751221.27 L8231416525.24 00000300600900<00E00M00P00S00V00Y00\00_00b00e00m01001301601901<01?01B01J01M01P01X01`01h02102402702@02C02F02I02L02O02R02U02]02`02c02f03403703:03=03E03N03Q03W03]03e03j04104604;04>04A04I04L04O04W04Z04]04`04c04f04i04l04o052055S1GS1GS1GS1GS1G2d22H0S1G2d21HS1GS1GS1GS1GS1GS1GS1GS1GS1G2d11HS1GS1GS1GS1GS1GS1GS1GS1G2d21HS1GS1GS1G2d11HS1G2d11HS1G2d11HS1G2d22H0S1GS1GS1G2d22H0S1GS1GS1GS1GS1GS1GS1GS1G2d11HS1GS1GS1GS1G2d12d21H2H0S1GS1GS1GS1G2d11HS1G2d22H0S1GS1G2H0S1G2H0S1G1H2H0S1G1ES1G3HInS1G1HS1G1HS1GS1GS1G2d21HS1GS1GS1G2d11HS1GS1GS1GS1GS1GS1GS1GS1GS1GS1G". (* [comment removed for export] *)
Lemma tmp_ok_init7 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_K ()) "Pm,P,(0.&40.)(1.(0.&8.))PLBi,(2.$3.)PG,$4.Pidpad,(0.&40.)PpP,(0.&40.)PpA,(0.&40.)PpB,(0.&40.)PpX,(0.&40.)PpY,(0.&40.)PpZ,(0.&40.)PpN,(0.&40.)Phpad,(0.&40.)P,(5.$6.$7.R<.R;.R:.(8.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.))(9.(:.$6.R=.R<.R;.+<0.(;.$<.(=.(>.R;.+68.)R3.)(;.$<.(=.(>.R;.+8.)R9.)(;.$<.(=.(>.R;.+18.)R8.)(;.$<.(=.(>.R;.+28.)R7.)(;.$<.(=.(>.R;.+38.)R6.)(;.$<.(=.(>.R;.+48.)R5.)(;.$<.(=.(>.R;.+58.)R4.)(?.$<.)))))))))(9.(10.$6.R=.R;.(;.$11.(12.#8.(13.(0.&8.)(14.(15.&40.=))(14.R:.)))(?.$11.)))(10.$6.R=.(>.R;.+78.)(;.$11.(16.(15.&40.=))(;.$11.(16.(15.&40.=))(;.$11.(12.#38.(13.(0.&8.)(14.(15.&40.=))(13.(0.&8.)(14.R2.)(13.(0.&8.)(17.(15.&40.=))(13.(0.&8.)(17.(15.&40.=))(13.(0.&8.)(17.(15.&40.=))(13.(0.&8.)(17.(15.&40.=))(13.(0.&8.)(17.(15.&40.=))(17.(15.&40.=))))))))))(?.$11.)))))))")
(* [comment removed for export] *).
Proof.
  intros until hpad. intros HG.
  dpose HG as (HD & AL & POS & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & TL & _).
  cbn [grp_init g_P g_A g_B g_G g_N pt_init pt_X pt_Y pt_Z grp_head_cells grp_tail_cells g_id g_idpad g_pbits g_nbits g_h g_hpad g_modp g_tpre g_tpost g_tdata g_T g_Tsize] in HD, MP, MA, MB, MX, MY, MZ, MN, TL.
  replace (G + 56 + 16) with (G + 72) in MY by lia. replace (G + 56 + 32) with (G + 88) in MZ by lia.
  split; [| split].
  - split. { repeat apply Forall_cons; try apply Forall_nil; (split; [assumption| cbn; left; reflexivity]). }
    split. { repeat apply Forall_cons; try apply Forall_nil; cbn; (split; [discriminate| lia]). }
    split. { intros d1 d2 H1 H2 E. cbn in H1, H2. decompose [or] H1; decompose [or] H2; subst; try reflexivity; cbn in E; exfalso; lia. }
    split. { intros d1 d2 H1 H2 NE. cbn in H1, H2. decompose [or] H1; decompose [or] H2; subst; try (exfalso; apply NE; reflexivity); cbn; lia. }
    split. { intros d1 d2 H1 H2 _ O1 _. exfalso. cbn in H1. decompose [or] H1; subst; cbn in O1; first [discriminate O1| contradiction]. }
    cbn [map md_addr mpd_init]. repeat (constructor; [cbn; intros HIn; decompose [or] HIn; lia|]). constructor.
  - eapply rw_cells_reshape; [exact HD| cbn; repeat split; rewrite ?app_length, ?length_le4, ?length_le8; reflexivity| cbn; rewrite ?app_nil_r, <- ?app_assoc; reflexivity].
  - eapply rw_cells_reshape; [exact TL| cbn; repeat split; rewrite ?app_length, ?length_le4, ?length_le8; reflexivity| cbn; rewrite ?app_nil_r, <- ?app_assoc; reflexivity].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section EP.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis CA_RSA0 : const_at L U_RSA_INFO 4.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (mo0 : Model) (h0 : HST usegs L HI) (LB : list blk)
            (PKA info C lo PAR LEN P BUF : Z) (tg pd : word) (bs : list byte)
            (idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ : word).
  Notation K := (kp_init C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ).
  Hypothesis HH0 : HEAP usegs L HI h0 LB m0 mo0.
  Hypothesis HPKA0 : rw_cells usegs m0 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)].
  Hypothesis ALP : PKA mod 8 = 0.
  Hypothesis NZP : 0 < PKA.
  Hypothesis EI : In info U_EC_INFOS.
  Hypothesis DSP : PKA + 16 <= lo \/ bv_unsigned sp <= PKA.
  Hypothesis CWP : client_wrange L LB lo (heap_top usegs L HI h0) PKA 16.
  Hypothesis DPC : PKA + 16 <= C \/ C + 256 <= PKA.
  Hypothesis PKD : PKA + 16 <= hl_data_lo L \/ hl_data_hi L <= PKA.
  Hypothesis KP0 : ecp_keypair_at usegs U_MT m0 LB C K.
  Hypothesis INC : In (C, 256) LB.
  Hypothesis CD : C + 256 <= hl_data_lo L \/ hl_data_hi L <= C.
  Hypothesis HPAR0 : rw_cells usegs m0 PAR (buf_cells tg pd LEN P).
  Hypothesis ALR : PAR mod 8 = 0.
  Hypothesis NZR : 0 < PAR.
  Hypothesis DSR : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis RD : PAR + 24 <= hl_data_lo L \/ hl_data_hi L <= PAR.
  Hypothesis RC : PAR + 24 <= C \/ C + 256 <= PAR.
  Hypothesis HBS0 : bytes_at usegs m0 BUF bs.
  Hypothesis INB : In (BUF, Z.of_nat (length bs)) LB.
  Hypothesis BP : BUF <= P.
  Hypothesis LEN0 : 0 <= LEN.
  Hypothesis PL : P + LEN <= BUF + Z.of_nat (length bs).
  Hypothesis B63 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis IDS0 : ecp_ids_state usegs U_ECP_IDS_DONE U_ECP_IDS m0.
  Hypothesis SOK0 : statics_ok usegs L m0.
  Hypothesis CA : const_at L U_MEMSET_FUNC 8.
  Hypothesis CAT : const_at L U_OID_EC_GRP_TBL 440.
  Hypothesis CA_EC0 : forall e, In e U_EC_INFOS -> const_at L e 4.
  Hypothesis SLO : lo <= bv_unsigned sp - 688 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h0.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv usegs m0.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis SPR : bv_unsigned sp < 2^64.
  Hypothesis IDL : ecp_ids_lok L U_ECP_IDS_DONE U_ECP_IDS.
  (* [comment removed for export] *)
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis CAC : C + 256 <= alloc_ceiling.
  Hypothesis C0 : 0 < C.
  Hypothesis C16 : C mod 16 = 0.
  Hypothesis CIM : C + 256 <= hl_img_lo L \/ hl_img_hi L <= C.
  Hypothesis BAC : BUF + Z.of_nat (length bs) <= alloc_ceiling.
  Hypothesis BIM : BUF + Z.of_nat (length bs) <= hl_img_lo L \/ hl_img_hi L <= BUF.

  Notation XS := [(U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)].
  Notation X0 := [(C, C + ECP_GROUP_SIZE); (U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)].
  Notation POST := (pk_use_ecparams_post usegs L HI U_MT U_CA U_ONE U_ECP_IDS_DONE U_ECP_IDS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PKA info C K lo m0 mo0).
  Notation FRS mm := (rw_cells usegs mm (bv_unsigned sp + -104)
                        [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  #[using="HI m0 mo0 h0 LB HH0 INC INB ACP"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_K ()) "(9.(18.+1000.(19.VL,))(9.(18.=VC,)(9.(1:.$4.(1;.VC,+10.)=)(9.(1<.(>.VC,+100.)(19.VL,))(9.(1=.(1<.(>.VC,+100.)(1>.VL,))(1<.(1?.VL,)VC,))(9.(1<.(>.VBUF,(20.(21.(0.&8.)Vbs,)))(19.VL,))(1=.(1<.(>.VBUF,(20.(21.(0.&8.)Vbs,)))(1>.VL,))(1<.(1?.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0' & C16' & _ & CAC' & CIM'). cbn in C0', C16', CAC', CIM'.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC' & BIM'). cbn in BAC', BIM'. auto 10.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2647750340.6  L2726914452.6  L52616404933.1000000D00X016S1L3PKA3PKD2I12I22I3S1L3PKA3PKD2I12I22I3S1L2HI2sp2h03PKA2lo3DSP1a2Ha1Q". (* [comment removed for export] *)
  #[using="HI h0 lo HPKA0 DSP CWP PKD IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_K ()) "Pm,P,(0.&40.)(1.(0.&8.))P,(22.$6.VL,VLB,(23.&40.Vsp,)(;.(24.$4.$4.)(25.$4.$4.$26.(>.$26.+1.))(;.(24.$4.$4.)(25.$4.$4.$27.(>.$27.+38.))(?.(24.$4.$4.))))Vm0,R1.)(10.$6.R2.VPKA,(;.$11.(16.(15.&40.Vinfo,))(;.$11.(16.(15.&40.VC,))(?.$11.))))")
(* [comment removed for export] *).
  Proof.
    intros m PX. eapply heap_presx_rw_cells; [exact PX| exact HPKA0| |]; cbn [cells_size csize Nat.add disjoint_from].
    - intros a Ha. destruct (CWP a Ha) as [Q|[Q|Q]]; [left; clear -Q DSP Ha; lia| right; left; exact Q| right; right; exact Q].
    - ddestruct IDL as (I1 & I2 & I3 & _). clear -PKD I1 I2 I3. split; [lia| split; [lia| exact I]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  #[using="IDL"] Lemma IL1 : hl_data_lo L <= U_ECP_IDS_DONE. Proof. exact (proj1 IDL). Qed.
  #[using="L IDL"] Lemma IL2 : U_ECP_IDS_DONE + 1 <= U_ECP_IDS. Proof. exact (proj1 (proj2 IDL)). Qed.
  #[using="IDL"] Lemma IL3 : U_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 IDL))). Qed.
  #[using="IDL"] Lemma IL4 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_K ()) "Pa,$4.P,(1=.(9.(1<.$26.R1.)(18.R1.(>.$26.+1.)))(9.(1<.$27.R1.)(18.R1.(>.$27.+38.))))(9.(28.VL,R2.)(29.(2:.VL,R2.)))")
(* [comment removed for export] *).
  Proof. exact (proj2 (proj2 (proj2 IDL))). Qed.
  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.

  Notation G := (bv_unsigned sp + -504).
  Notation REF := (bv_unsigned sp + -296).
  Notation CTX := (ctx_now L HI mo0 h0 LB).
  Notation DS7 dN dP dA dB dX dY dZ := ([dN; dP; dA; dB; dX; dY; dZ] : list mpd) (only parsing).


  Notation LSTATE := (LSTATE sp gp tp F fc PKA).
  Notation LINV := (LINV L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB lo).
  Notation ctx_munch' := (ctx_munch L HI ra sp m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP DHI IDL).
  Notation tail_from_linv' := (tail_from_linv L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation iter_head' := (iter_head L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation cmp_chain' := (cmp_chain L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation idloop_walk' := (idloop_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation cleanup_walk' := (cleanup_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation linv_frame' := (linv_frame L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP SPA DHI IDL).



  Notation PEND := (P + LEN).
  Ltac inlist := cbn; repeat (first [ left; reflexivity | right ]).
  (* [comment removed for export] *)
  Ltac dj7 EN EP EA EB EX EY EZ :=
    let d := fresh "d" in let Hd := fresh "Hd" in
    intros d Hd; cbn in Hd; decompose [or] Hd; try contradiction; subst d; rewrite ?EN, ?EP, ?EA, ?EB, ?EX, ?EY, ?EZ; cbn;
    generalize SLO HLS ACL; clear; intros; repeat split; lia.

  Notation SPINV' := (SPINV L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB lo LEN P).
  Notation spinv_munch' := (spinv_munch L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB PKA C lo PAR LEN P bs ACL HTOP DHI IDL).
  Notation spinv_update' := (spinv_update L HI HLS DIMG HND sp m0 mo0 h0 LB lo SLO ACL DHI IDL).
  Notation ctx_bytes' := (ctx_bytes L DIMG sp m0 LB BUF bs HBS0 INB IDL BIM).
  Notation tmp_apart_LB' := (tmp_apart_LB L HI HLS ra sp LB PKA C lo PAR bs NZP DSP DPC NZR DSR RC SLO ACL ACP CAC C0).
  Notation tmp_upd7' := (tmp_upd7 sp).
  Notation tmp_writable' := (tmp_writable L HI sp h0 lo ACL HTOP DHI).
  Notation specC2_walk' := (specC2_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM).
  Notation spec_err' := (spec_err L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation spec_erradd' := (spec_erradd L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).

(* [comment removed for export] *)
  Ltac tmp_post m1 m2 d Ed CX1 PX1 TOK1 HH1 HH2 HT2 MF2 MI2 SOK2 MD2 OUT NEW PX2 CXo PXo TOKo :=
    let EAD := fresh "EAD" in let HBR1 := fresh "HBR1" in let MDd := fresh "MDd" in let NSd := fresh "NSd" in
    pose proof (proj1 OUT) as EAD;
    destruct (spinv_update' _ _ m1 _ _ _ m2 _ _ d _ _ CX1 PX1 TOK1 ltac:(inlist) HH2 HT2 MF2 MI2 SOK2 MD2 OUT NEW PX2
                ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as (CXo & PXo & TOKo);
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _];
    pose proof (proj1 (tmp_ok_in usegs _ _ _ _ _ d TOK1 ltac:(inlist))) as MDd;
    pose proof (proj1 (proj1 (Forall_forall _ _) (proj1 (proj2 TOK1)) d ltac:(inlist))) as NSd;
    rewrite (mpd_ivs_fp d NSd) in PX2;
    repeat match goal with
    | Hc : rw_cells usegs m1 ?a ?cs |- _ =>
        first [ apply (heap_presx_rw_cells usegs L _ _ _ m1 m2 a cs PX2) in Hc;
                [ | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; let a' := fresh "a'" in let Ha' := fresh "Ha'" in intros a' Ha'; left; clear -Ha'; lia
                  | first [ (* [comment removed for export] *) eapply (fp_disjoint_stack usegs L d m1); [exact MDd| exact HBR1| clear -ACL SLO HLS; lia
                              | rewrite Ed; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; clear; lia]
                          | split; [cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia
                                   | eapply (fp_disjoint_stack usegs L d m1); [exact MDd| exact HBR1| clear -ACL SLO HLS; lia
                                     | rewrite Ed; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; clear; lia] ] ] ]
              | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
    end;
    clear HBR1 MDd NSd.

  Notation specB_walk' := (specB_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM).

  Ltac gt_call SGT FRP FRL HBS MI p ed tg KEEP :=
    acallx (eapply SGT with (PP := REF) (LENP := bv_unsigned sp + -304) (P := p) (END := ed) (BUF := BUF) (bs := bs) (tag := tg);
            first [ exact FRP | exact FRL | exact HBS | exact MI | reflexivity
                  | KEEP
                  | clear -BAC ACL SLO HLS; lia
                  | clear -SPA SPR; lia | clear -ACL ACP SLO HLS; lia | clear -BUF0; lia
                  | clear; lia
                  | f_equal; clear; lia
                  | match goal with |- ?g => idtac "GTLEFT" g end ]).

  Ltac ro_const A n RO :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
      let cbs := eval vm_compute in (match image_bytes sg A n with Some cbs => cbs | None => [] end) in
      match goal with MI : mem_inv sg mx |- _ =>
        pose proof (ro_image_bytes_at sg mx A cbs MI ltac:(vm_compute; reflexivity) ltac:(clear; lia) ltac:(clear; cbn; lia)) as RO end
    end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03h0@D10463954377.249D11805467289.247D11805467289.294D13897687993.216D13897687993.236D16025640726.296D16035941354.294D18360801976.216D18360801976.236D2090238905.249 D22518009273.216D22518009273.236D24006757689.216D24006757689.236D27373842873.216D27373842873.236D28976707569.218D30581627241.238D34020630390.216D34020630390.236D36953774137.216D36953774137.236D3986801849.216 D3986801849.236 D4371694009.216 D4371694009.236 D44622288685.249D44622288685.296D46200682742.216D46200682742.236D47763733816.216D47763733816.236D49698585326.249D49698585326.296D49705053714.247D49705053714.294D52101704109.219D52101704109.239D53269563319.216D53269563319.236D55610685700.249D58526514487.216D58526514487.236D59953809465.216D59953809465.236D68578355769.216D68578355769.236D9383801913.216 D9383801913.236 D9919893866.247 D9926296982.249 L10259629737.0  L1110396576.17  L11328196705.15 L11339382392.2  L12258919114.2  L12455422775.1  L12632560433.6  L13302926971.6  L1386329760.227 L14351168243.6  L14368737793.5  L14411982930.15 L14948329268.184L15217048541.1  L15814045879.1  L16093294955.6  L16269778262.3  L16270054593.9  L16270152278.16 L16271922246.11 L16272271869.34 L16272395572.1  L16720171459.287L16859315579.6  L17681342172.34 L18430670468.0  L18933043916.4  L19238831410.293L19349569929.0  L19513237663.2  L19649668203.6  L19730642225.6  L19827685782.238L20032160929.16 L20033448259.18 L20034454193.11 L20361976947.6  L20380073089.5  L20729265243.5  L20731298185.35 L21961750162.34 L21962134107.2  L22311835755.6  L22530056029.1  L22576991770.3  L22577441362.34 L24850858691.6  L24984755888.17 L25583011654.10 L25870307179.6  L26087481949.1  L26387515891.6  L2661346595.1   L26913259113.6  L2691914327.35  L2692263678.2   L27105925383.1  L27197623219.285L27241983747.285L27298187553.34 L27299717803.4  L27300246154.15 L28379935446.3  L28380020182.16 L28380183361.9  L28382051270.11 L28456411139.238L28502328607.3  L28877807824.16 L28897400179.6  L29015421609.5  L29283251478.249L29426680427.6  L29558833075.204L29558833075.227L29558833075.238L29558833075.285L29742945110.264L30392002547.6  L30944687130.6  L31471788297.3  L32394139473.1  L33734336981.10 L33918586536.1  L34347336241.6  L35501726675.11 L36650009439.3  L36949002973.1  L37533028279.1  L37808070763.6  L37905822001.6  L38237953557.5  L38574091387.6  L38732773782.8  L39304206405.34 L39304625673.3  L3983087197.1   L39935534662.5  L40703418902.218L40987796497.9  L40988025478.16 L40990038317.34 L40990188694.11 L40990424929.3  L41251706944.35 L41364395883.6  L4136721515.6   L41462195249.6  L41615955691.3  L4210777681.2   L43068201034.4  L43068429000.8  L43068477917.9  L43068643146.15 L43070280026.10 L43083158376.2  L43459632897.5  L4367979357.1   L44026612587.6  L44243979607.18 L44922866283.6  L45044737469.34 L45045400561.4  L46130367529.5  L46350850038.11 L46369226564.0  L475311137.3    L47585099371.6  L477972395.34   L48062193029.4  L48395073079.1  L488979946.6    L49664744988.1  L49675928472.184L50600009991.1  L51352513313.0  L51390623401.0  L51854572294.16 L51854605713.9  L51856473366.11 L51860674949.0  L52329349271.18 L52715614025.7  L52715629660.9  L52715793099.16 L52715906507.3  L52717483433.1  L52717867360.34 L52717956315.11 L54973495411.6  L55314927287.1  L55979346332.0  L56732428411.6  L57498838785.5  L57933460272.236L580331883.6    L58531213267.1  L58742968907.3  L58743151947.16 L58743199945.7  L58743249884.9  L58745051995.11 L58972630378.15 L58974923642.10 L59427867805.207L59538824041.1  L59539575659.6  L59620532273.6  L59654577821.13 L60068700977.14 L60290916219.6  L60830077373.6  L61120265865.3  L61434210102.3  L61434516383.35 L61900301956.0  L62438632883.204L62438632883.225L62627930679.1  L62829711785.5  L63098046059.6  L63176922929.6  L63216279672.10 L63847289467.6  L6430512105.6   L65042672357.287L65113750064.17 L66572612610.3  L68574673117.1  L7056998543.2   L7057933572.34  L7524955863.3   L8322245898.4   L8325611891.6   L9744456571.6   L9786641405.34  L9787043636.1   00001801S01n02B02V03A03\04304J05L05`06406H06\07007D08A09>0::0;60;J0;^0<20<F0<Z0<n0>80?C0@?0A;0AR0Ai0BW0CF0Ce0DD0E@0F<0FP0Fd0H20HF0HZ0Hn0IB0IV0Ij0J>0JR0Jm0KW0KX0LP0Lm0M40M<0M@0MD0MK0ML0Ma0N20NA0NB0NF0NJ0NN0NV0NW0NX0NY0O90O:0Q30Q:0QN0QO0QY0R10R20R:0R>0RB0RV0R]0SG0SN0Sc0T40T50T60TV0TW0T[0T_0T`0U00UC0UG0U]0Ua0Ub0V70V;0V<0V=0V>0VB0VZ0W20Wf0Wg0XC0XK0XL0XM0XN0Xf0Y10YZ0Yo0Z30ZK0ZO0Zc0[70[O0[g0[h0\=0\R0\]0\a0]00]10]50]V0]a0]e0]i0]m0^10^50^<0^Y0_=0_>0_B0_F0_Z0`:0`;0`_0``0`a0`b0`f0`j0`n0`o0a90a:0a;0a<0a=0a>0aH0aY0a]0aa0bI0bM0c10c20c60cX0cY0cZ0c^0dO0dP0dT0dU0dY0dm0e10e20e30e40eT0eU0eV0eZ0f30f40f50f60f70fS0fT0fi0fm0fn0g50gF0gG0gK0gO0gP0gQ0gj0gk0gl0h80hD0hE0hI0hM0hQ0hR0i?0iF0iG0iR0iS0iT0iU0ii0j=0jA0jE0jI0jM0j^0je0ji0l^0lb0lm0m10m20n20n30nN0nc0nj0oJ0oKS1L2HI2ra2sp2h03PKA1C3PAR2bs3NZP3NZR4HTOP2C01h2p23HT23obs2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3obs2HBS2ra2sp3PKA1C3PAR2bs3obs2HBS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3x863obs2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3obs2HBS2ra2sp3PKA1C2lo3PAR2bsS2ra2sp3PKA1C2lo3PAR2bsS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO2C02p23obs2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C2lo3PAR3LEN1P2bs1p3x402x33x413x423x434POST3x441HS2ra2sp3PKA1C2lo3PAR2bs3x542p13ln13x423x553x563x574POST3x581HS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BACS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BACS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C02p23obs2HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C03x863obs2HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BACS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BACS2ra2sp3PKA1C2lo3PAR2bsS2ra2sp3PKA1C2lo3PAR2bsS2ra2sp3PKA1C3PAR2bs3SPR2p23obs2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3SPR3x863obs2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3SPR3obs2HBS2ra2sp3PKA1C3PAR2bs3SPR3obs2HBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI3ACP2C01a1HS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI3ACP2C01a1HS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL2C03BAC2p23obs2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3obs2HBS2ra2sp3PKA1C3PAR2bs2p23obs2HB5Ha_st5Hl_stSS3LEN1P3BUF2bs2BP2PL3B634BUF01p2PB2p13ln13PB13LN12p23PB2S3LEN1P3BUF2bs2BP1p2PB2p13PB1S2sp2loS2r13RR1S2spS2spS2sp2loFS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOS2bs2p13ln13LNRFS2spS2spS2spS2sp3SPAFFFS1L3HLS2sp2lo2bs3SLO3ACL3SPA3ACPFS1L3HLS2ra2sp3PKA1C2lo3PAR3LEN1P3BUF2bs3NZP3NZR2BP2PL3B634BUF03SLO3ACL3ACP2C03BAC1p2PB2p22p13ln12P23LN13ln22P33LN22K73obsS2sp2loS1L2HI2sp2h02bs4HTOPSS2r12r22r4S2ra2sp3PKA1C3PAR2bs3obsSS2r23RR2S2spS2spS2ra2sp3PKA1C3PAR2bsS2sp2bsS3LEN1P3BUF2bs2PL2p13ln13LN12p23ln23LN22K7S2sp2bsS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOFFS1L3HLS2sp2lo2bs3SLO3ACL3DHI3ACPFS2spS2spFS1L2sp2lo2bs3SLOS3LEN1P1p2PB2p13PB1S2bsS3LEN1P3BUF2bs2BP1p2PBS2spFS1L3HLS2sp2lo3SLO3ACLS2spFFFS2spS2ra2sp3PKA1C3PAR2bs3obsS2ra2sp3PKA1C3PAR2bs3obsS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3SLO3ACL3ACP2p13ln13LN1FS3LEN1P3BUF2bs2PL2p13ln13LN1S2sp3SPAFFFS2ra2sp3PKA1C3PAR2bs3obsS2r43RR42NZS3LEN1P1p2PB2p22p13ln13PB13LN13PB22p43PB4S1L3HLS2sp2lo3SLO3ACLS2spS2ra2sp3PKA1C3PAR2bs3obsS2spS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3obsS2ra2sp3PKA1C3PAR2bs3obsFS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLO3ACLS2r23RR22HqS2spS3LEN1P2bs1p2PBFS2spS1L2HI3HLS2sp2h02lo3SLO4HTOP1a2HaS2r43RR42HqS2spS2spS2spS2spS2loS2sp2loS1L3HLS2sp2lo3SLO3ACL3SPR3ACPS1L3HLS2sp2lo3BUF2bs3SLO3ACL3ACP3BACFS2spS2spS2ra2sp3PKA1C3PAR2bsS1L3HLS2sp2lo3BUF2bs3SLO3ACL3BACFS1L3HLS2sp2lo3BUF2bs3SLO3ACL3ACP3BACFFFS2spS2spS2spFS3obs4LENOFFFFFS3BUF4BUF0S1L3HLS2sp2lo3SLOS2spS2spS3LEN1P3BUF2bs2BP1p2PB2p13ln13PB12p23PB2S2spS1L3HLS2sp2lo3BUF2bs3SLO3ACL3ACP3BACFS2spS3LEN1P1p2PB2p13ln13PB13LN12p23PB2SFS2spS1L3HLS2sp2lo2bs3SLO3ACL3ACP2p22p13ln13ln23LN22K7FS2spFS2spS2ra2sp3PKA1C3PAR2bsS2spSSFS1L3HLS2sp2lo3BUF2bs3SLO3ACL3BACFSS2bsS1L3HLS2sp2lo3SLO3ACL3ACPFFFFS1L3HLS2sp2lo2bs3SLO3ACL3ACPFS1L3HLS2sp2lo3SLO3ACLS2spSS2sp2loS1L3HLS2sp2lo3SLOFS2spS2spFFS1L3HLS2sp2lo3SLO3ACL3ACPFFS3BUF2bs3B63S3BUF2bs3B63FS2spS2spS2spFS3LEN1P1p2PB2p22p13ln13PB13LN13ln23PB23LN22K7S2sp2loFS2sp2a'3Ha'FFSS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2spS2spS2spS2spS3LEN1P3BUF2bs2PLS2sp2loS2spS1L3HLS2ra2sp3PKA1C2lo3PAR3LEN1P3BUF2bs3NZP3NZR2BP2PL3B634BUF03SLO3ACL3ACP2C03BAC1p2PB2p22p13ln12P23LN12P33obs2p43PB4S2bsS2r13RR12HqS2spFS1L3HLS2sp2lo3LEN1P3BUF2bs2BP3SLO3ACL3ACP1p2PB2p22p13ln13PB13PB2FS2r13RR11q2Hq2r23RR22r43RR4S1L3HLS2sp2lo3SLO3ACLS2sp2loS1L3HLS2sp2lo2bs3SLO3ACL3SPA3ACPF". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM"] Lemma specA_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_K ()) "Ph,(2;.$6.VL,VHI,)PLBi,(2.$3.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$2<.PdN,$<.PdP,$<.PdA,$<.PdB,$<.PdX,$<.PdY,$<.PdZ,$<.Pp,$4.Plnw,(0.&40.)Pvw,(0.&40.)Ppb,(0.&40.)Pnb,(0.&40.)Pscj,(2.(0.&8.))Phj,(2.(0.&8.))Ptj,(2.(0.&8.))Ppj,(2.(0.&8.))Prj,(2.(0.&8.))PpP,(0.&40.)PpA,(0.&40.)PpB,(0.&40.)PpX,(0.&40.)PpY,(0.&40.)PpZ,(0.&40.)Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px10,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px18,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Px25,(0.&40.)Px26,(0.&40.)Px27,(0.&40.)Px28,(0.&40.)Px29,(0.&40.)Px30,(0.&40.)Px31,(0.&40.)P,(2=.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,VLEN,VP,R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)P,(1:.$<.R31.(=.(>.(>.(23.&40.Vsp,)-1?8.)+8.)R21.))P,(1:.$<.R31.(=.(>.(>.(23.&40.Vsp,)-1?8.)+18.)R21.))P,(1:.$<.R31.(=.(>.(>.(23.&40.Vsp,)-1?8.)+28.)R21.))P,(1:.$<.R31.(=.(>.(>.(23.&40.Vsp,)-1?8.)+38.)R21.))P,(1:.$<.R31.(=.(>.(>.(23.&40.Vsp,)-1?8.)+48.)R21.))P,(1:.$<.R31.(=.(>.(>.(23.&40.Vsp,)-1?8.)+58.)R21.))(2>.$6.R39.(2?.$6.VL,VHI,$7.$30.$31.$26.$27.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(32.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(33.(34.R21.(15.&40.(>.(23.&40.Vsp,)-200.))Vgp,Vtp,R20.R1?.R1>.(15.&40.VPKA,)(15.&40.(>.VP,VLEN,))R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)VF,(15.&40.+29718.)Vfc,(35.(0.&40.))R3:.(36.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros SI DPI DAI DBI DXI DYI DZI.
    dpose SI as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & FRP & PB & FRR & FRL & FRM & FR0 & FRH & FRT & FR & ST).
    ddestruct CX as (HH & HT & MF & MI & SOK & EXT & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    pose proof (ctx_bytes' m PX) as HBS.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases KV; zify_cond KV.
    2:{ (* [comment removed for export] *) zstep. zstep. zstep. zstep. zstep. eapply spec_err'; [exact SI| clear; lia| clear; lia]. }
    clear KV.
    (* [comment removed for export] *)
    pose proof U_asn1_get_tag_spec as SGT. unfold asn1_get_tag_stmt, asn1_get_tag_post, U_ASN1_GET_TAG in SGT.
    pose proof (munch_refl [(lo, bv_unsigned sp + -512); (REF, REF + 8); (bv_unsigned sp + -304, bv_unsigned sp + -296)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep. zstep. zstep.
    gt_call SGT FRP FRL HBS MI p (P + LEN) 0x30 ltac:(clear -PB BP LEN0 PL B63; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : rw_cells usegs m1 REF [C8 (Z_to_bv 64 ?q)] |- _ => rename H into FRP1; rename q into p1 end.
    match goal with H : rw_cells usegs m1 (bv_unsigned sp + -304) [C8 ?l] |- _ => rename H into FRL1; rename l into ln1 end.
    match goal with H : - (127) < ?r <= 0 |- _ => rename H into RR1; rename r into r1 end || match goal with H : _ < ?r <= 0 |- _ => rename H into RR1; rename r into r1 end.
    match goal with H : p <= p1 <= _ |- _ => rename H into PB1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into RZ1 end.
    match goal with M : mem_inv usegs m1 |- _ => rename M into MI1 end.
    match goal with W : wmono usegs m m1 |- _ => rename W into WM1 end. rename MU into MU1.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI MU1 WM1 MI1
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB EX EY EZ)
                  FRP1 ltac:(clear -PB PB1; lia) FRR FRL1 FRM FR0 FRH FRT FR ST) as SI1.
    clear MU1 WM1. match goal with H : ?x = Z_to_bv 64 r1 |- _ => subst x end.
    zstep. if_cases K1; zify_cond K1.
    { assert (NZ : r1 <> 0) by (intros ->; apply K1; reflexivity).
      zstep. zstep. eapply spec_err'; [exact SI1| clear -RR1; lia| exact NZ]. }
    assert (Z1 : r1 = 0).
    { clear -K1 RR1. apply Z.mod_divide in K1; [| lia]. destruct K1 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    destruct (RZ1 Z1) as [P2 LN1]. subst r1. clear K1 RZ1 RR1.
    dpose SI1 as (CX1 & PX1 & TOK1 & _). dpose CX1 as (HH1 & HT1 & MF1 & _ & SOK1 & EXT1 & IDS1).
    clear SI PX TOK HH HT MF SOK EXT IDS MK HBS HBR HAP. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    pose proof (bv_unsigned_in_range 64 ln1) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN; [pnull KN|].
    (* [comment removed for export] *)
    pose proof (ctx_bytes' m1 PX1) as HBS1.
    pose proof (munch_refl [(lo, bv_unsigned sp + -512); (REF, REF + 8); (bv_unsigned sp + -304, bv_unsigned sp + -296)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep. zstep. zstep.
    gt_call SGT FRP1 FRL1 HBS1 MI1 p1 (p1 + bv_unsigned ln1) 6 ltac:(clear -PB PB1 LN1 LNR BP LEN0 PL B63; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : rw_cells usegs m2 REF [C8 (Z_to_bv 64 ?q)] |- _ => rename H into FRP2; rename q into p2 end.
    match goal with H : rw_cells usegs m2 (bv_unsigned sp + -304) [C8 ?l] |- _ => rename H into FRL2; rename l into ln2 end.
    match goal with H : - (127) < ?r <= 0 |- _ => rename H into RR2; rename r into r2 end || match goal with H : _ < ?r <= 0 |- _ => rename H into RR2; rename r into r2 end.
    match goal with H : p1 <= p2 <= _ |- _ => rename H into PB2 end.
    match goal with H : r2 = 0 -> _ |- _ => rename H into RZ2 end.
    match goal with M : mem_inv usegs m2 |- _ => rename M into MI2 end.
    match goal with W : wmono usegs m1 m2 |- _ => rename W into WM2 end. rename MU into MU2.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI1 MU2 WM2 MI2
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB EX EY EZ)
                  FRP2 ltac:(clear -PB PB1 PB2 LN1 LNR; lia) FRR FRL2 FRM FR0 FRH FRT FR ST) as SI2.
    clear MU2 WM2. match goal with H : ?x = Z_to_bv 64 r2 |- _ => subst x end.
    zstep. if_cases K2; zify_cond K2.
    { assert (NZ : r2 <> 0) by (intros ->; apply K2; reflexivity).
      zstep. zstep. eapply spec_err'; [exact SI2| clear -RR2; lia| exact NZ]. }
    assert (Z2 : r2 = 0).
    { clear -K2 RR2. apply Z.mod_divide in K2; [| lia]. destruct K2 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    destruct (RZ2 Z2) as [P3 LN2]. subst r2. clear K2 RZ2 RR2.
    dpose SI2 as (CX2 & PX2 & TOK2 & _). dpose CX2 as (HH2 & HT2 & MF2 & _ & SOK2 & EXT2 & IDS2).
    clear SI1 CX1 PX1 TOK1 HH1 HT1 MF1 SOK1 EXT1 IDS1 MK1 HBS1. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    pose proof (bv_unsigned_in_range 64 ln2) as LNR2. change (bv_modulus 64) with (2^64) in LNR2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases K7; zify_cond K7.
    { (* [comment removed for export] *) zstep. zstep. eapply spec_err'; [exact SI2| clear; lia| clear; lia]. }
    rewrite ?unsigned_lit in K7 by (clear; lia).
    (* [comment removed for export] *)
    pose proof (ctx_bytes' m2 PX2) as HBS2.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    ro_const 0x1077b 7%nat RO.
    set (obs := firstn (Z.to_nat 7) (skipn (Z.to_nat (p2 - BUF)) bs)).
    assert (LENO : Z.of_nat (length obs) = 7) by (subst obs; apply bytes_at_sub_length; clear -PB PB1 PB2 LN1 LN2 K7 LNR BP PL; lia).
    assert (HOB : bytes_at usegs m2 p2 obs) by (subst obs; eapply bytes_at_sub; [exact HBS2| | |]; clear -PB PB1 PB2 LN1 LN2 K7 LNR BP PL; lia).
    clearbody obs.
    pose proof U_bcmp_spec as SPB. unfold memcmp_stmt, memcmp_post in SPB.
    acallp (eapply SPB; rewrite ?unsigned_lit by (clear -PB PB1 PB2 LN1 BP PL B63 BUF0 LEN0; lia);
            [ exact HOB | exact RO | clear -LENO; cbn; lia | reflexivity ]).
    clear SPB RO HOB.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rb end.
    zstep. zstep. zstep. if_cases KB; zify_cond KB.
    2:{ (* [comment removed for export] *) zstep. zstep. eapply spec_err'; [exact SI2| clear; lia| clear; lia]. }
    clear KB.
    (* [comment removed for export] *)
    pose proof (munch_refl [(REF, REF + 8)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; lia|].
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with M : mem_inv usegs m3 |- _ => rename M into MI3 end. match goal with W : wmono usegs m2 m3 |- _ => rename W into WM3 end.
    match goal with H : rw_cells usegs m3 REF [C8 _] |- _ => rename H into FRP3 end.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI2 MU WM3 MI3
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB EX EY EZ)
                  FRP3 ltac:(clear -PB PB1 PB2 LN1 LN2 K7 LNR; lia) FRR FRL2 FRM FR0 FRH FRT FR ltac:(assumption)) as SI3.
    dpose SI3 as (CX3 & PX3 & TOK3 & _). dpose CX3 as (HH3 & HT3 & MF3 & _ & SOK3 & EXT3 & IDS3).
    clear MU WM3 SI2 CX2 PX2 TOK2 HH2 HT2 MF2 SOK2 EXT2 IDS2 MK2 HBS2. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    pose proof (ctx_bytes' m3 PX3) as HBS3.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    pose proof (U_asn1_get_mpi_spec L HI U_MEMSET_FUNC HLS (U_mpi_read_binary_spec L HI HFREE HCALLOC HLS SW DIMG HND _ eq_refl)) as SGM.
    unfold asn1_get_mpi_stmt, asn1_get_mpi_post, U_ASN1_GET_MPI in SGM.
    eapply aevtM_cut.
    { eapply SGM with (lo := lo) (h := h) (LB := LBi) (PP := REF) (P := p2 + 7) (END := p1 + bv_unsigned ln1) (BUF := BUF) (bs := bs) (dX := dP);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
        first [ exact HH3 | exact FRP3 | exact HBS3 | exact TP | exact MI3 | exact SOK3 | exact CA | exact DI1 | exact DI2 | eassumption
              | reflexivity | rewrite EP; f_equal; clear; lia | f_equal; clear; lia
              | exact (tmp_ok_in usegs _ _ _ _ _ dP TOK3 ltac:(inlist))
              | exact (proj1 (proj1 (Forall_forall _ _) (proj1 (proj2 TOK3)) dP ltac:(inlist)))
              | rewrite HT3; eapply tmp_writable'; [exact HH3| exact TOK3| inlist| clear -SLO HLS; lia| clear; lia]
              | rewrite ?EP; rewrite ?HT3; clear -PB PB1 PB2 LN1 LN2 K7 LNR BP PL B63 BUF0 BAC ACL ACP SLO HLS HTOP SPA SPR DHI; lia
              | subst dP; cbn; intros O; discriminate O
              | (* [comment removed for export] *) intros a Ha; left; rewrite ?HT3; clear -Ha SLO HLS ACL HTOP; lia
              | (* [comment removed for export] *) intros a Ha; right; right; exists (BUF, Z.of_nat (length bs)); split; [eapply lb_ext_sub; [exact EXT3| exact INB]| exact Ha]
              | match goal with |- ?g => idtac "GMLEFT" g end ]. }
    clear SGM.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI4 & ST4 & MF4 & HT4 & HH4 & MD4 & OUT & PX4 & SOK4 & FRP4 & PB4 & RR4 & RZ4 & NEW).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m4; rename mox into mo4 end.
    match type of HT4 with heap_top _ _ _ ?hh = _ => rename hh into h4 end.
    match type of HH4 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB4 end.
    match type of MD4 with mpd_at _ _ _ ?dd => rename dd into dP' end.
    ddestruct OUT as (EAD & NSD & O3 & O4 & O5). pose proof (conj EAD (conj NSD (conj O3 (conj O4 O5)))) as OUT.
    destruct (spinv_update' h LBi m3 mo h4 LB4 m4 mo4 _ dP dP' [(REF, REF + 8)] CX3 PX3 TOK3 ltac:(inlist) HH4 HT4 MF4 MI4 SOK4 MD4 OUT NEW PX4
                ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as (CX4 & PXn4 & TOK4).
    rewrite (proj1 (proj2 (tmp_upd7' dP' dN dP dA dB dX dY dZ EN EP EA EB EX EY EZ)) ltac:(rewrite EAD; exact EP)) in CX4, TOK4.
    destruct (heap_blocks _ _ HI _ _ _ _ HH3) as [HBR3 _].
    pose proof (proj1 (tmp_ok_in usegs _ _ _ _ _ dP TOK3 ltac:(inlist))) as MDP.
    pose proof (proj1 (proj1 (Forall_forall _ _) (proj1 (proj2 TOK3)) dP ltac:(inlist))) as NSP.
    rewrite (mpd_ivs_fp dP NSP) in PX4.
    repeat match goal with
    | Hc : rw_cells usegs m3 ?a ?cs |- _ =>
        first [ apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 a cs PX4) in Hc;
                [ | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; intros a' Ha'; left; clear -Ha'; lia
                  | split; [cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia
                           | eapply (fp_disjoint_stack usegs L dP m3 LBi); [exact MDP| exact HBR3| clear -ACL SLO HLS; lia
                             | rewrite EP; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; clear; lia] ] ]
              | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
    end.
    lazymatch type of FRP4 with rw_cells _ _ _ [C8 (Z_to_bv 64 ?q)] => rename q into p4 end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into r4 end.
    pose proof (eq_trans EAD EP) as EP'.
    assert (SI4 : SPINV' h4 LB4 m4 mo4 dN dP' dA dB dX dY dZ p4 ln2 vw pb nb scj hj tj pj rj).
    { split; [exact CX4|]. split; [exact PXn4|]. split; [exact TOK4|].
      split; [exact EN|]. split; [exact EP'|]. split; [exact EA|]. split; [exact EB|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [exact FRP4|]. split; [clear -PB PB1 PB2 PB4 LN1 LN2 K7 LNR; lia|]. split; [exact FRR|]. split; [exact FRL2|]. split; [exact FRM|].
      split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FR| exact ST4]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    clear CX3 PX3 TOK3 HH3 HT3 MF3 SOK3 EXT3 IDS3 MI3 HBS3 MK3 PX4 HBR3 MDP NEW OUT O3 O4 O5 NSD.
    zstep. if_cases K4; zify_cond K4.
    { (* [comment removed for export] *) assert (NZ : r4 <> 0) by (intros ->; apply K4; reflexivity).
      eapply spec_erradd'; [exact SI4| clear -RR4 NZ; lia| exact MK4]. }
    assert (Z4 : r4 = 0).
    { clear -K4 RR4. apply Z.mod_divide in K4; [| lia]. destruct K4 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    subst r4. clear K4.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SBL. unfold mpi_bitlen_stmt, mpi_query_post, U_MPI_BITLEN in SBL.
    destruct (heap_blocks _ _ HI _ _ _ _ HH4) as [HBR4 _].
    pose proof (tmp_ok_in usegs _ _ _ _ _ dP' TOK4 ltac:(inlist)) as MDP4.
    pose proof (munch_refl [(bv_unsigned sp + -384, bv_unsigned sp + -376)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    replace (G + 120) with (bv_unsigned sp + -384) in FRT by (clear; lia).
    zstep. zstep.
    acallx (eapply SBL with (dX := dP');
            [ exact MDP4 | intros O; destruct (mpdr_blk_facts usegs L _ _ _ (proj1 MDP4) O HBR4) as (_ & _ & P0 & _); exact P0 | exact MI4
            | rewrite EAD, EP; f_equal; clear; lia ]).
    try clear PC.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with M : mem_inv usegs m5 |- _ => rename M into MI5 end. match goal with W : wmono usegs m4 m5 |- _ => rename W into WM5 end.
    match goal with U : munch _ m4 m5 |- _ => rename U into MU5 end.
    replace (bv_unsigned sp + -384) with (G + 120) in FRT by (clear; lia).
    lazymatch type of FRT with rw_cells _ _ _ [C8 ?pb5; C8 _; _] =>
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI4 MU5 WM5 MI5
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP' EA EB EX EY EZ)
                  FRP4 ltac:(clear -PB PB1 PB2 PB4 LN1 LN2 K7 LNR; lia) FRR FRL2 FRM FR0 FRH FRT FR ltac:(assumption)) as SI5 end.
    pose proof (heap_mok _ _ HI _ _ _ _ (proj1 (proj1 SI5))) as MK5.
    (* [comment removed for export] *)
    zstep. if_cases KE; zify_cond KE.
    2:{ zstep. zstep. zstep. eapply spec_err'; [exact SI5| clear; lia| clear; lia]. }
    eapply specB_walk'; [exact SI5| exact DAI| exact DBI| exact DXI| exact DYI| exact DZI].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02O0@D10306510801.219D10463954377.197D10510144824.219D11805467289.195D12428150072.189D12428150072.219D14547516600.189D14693844793.219D15230134585.219D16561214479.219D16859744849.219D18410054609.189D19555549836.197D204268854.189  D2090238905.197 D22518009273.219D26291562981.219D27813732409.189D28711162041.219D34020630390.219D36953774137.219D3986801849.219 D40146277073.189D4023172665.219 D41475213646.219D42194919990.219D4371694009.219 D44484923210.189D44484923210.219D44622288685.197D46060066897.219D47057380676.219D47763733816.219D48249610601.220D48848304718.219D49698585326.197D49705053714.195D50134113102.189D52101704109.191D52101704109.221D54386062265.219D54519121.189   D55618337860.189D5693649977.189 D58508532342.219D58526514487.219D58579621559.219D6074347833.189 D62233333457.189D63951661497.189D64332360377.189D64434472657.219D65167897550.219D65230314297.219D65901190169.190D67780578129.219D68578355769.219D7373464249.219 D7564728401.189 D9919893866.195 D9922138833.219 D9926296982.197 L10472341635.207L11337899452.10 L12415176104.181L12415176104.211L12630690253.1  L12632560433.6  L1322278273.5   L13302926971.6  L1392622547.3   L14437061931.6  L16269778262.3  L16270054593.9  L16270061169.9  L16604274249.7  L16766402918.210L16859315579.6  L17995532331.6  L19553456252.189L19730642225.6  L19732443085.1  L20361976947.6  L20380073089.5  L21551922987.6  L216722854.181  L25656252822.186L26304536949.211L2688456790.3   L27395166364.9  L27395172908.9  L27395216265.7  L27395447051.3  L27750126273.9  L27750131825.9  L27750374230.3  L27837460028.5  L28456411139.186L29558833075.186L29574716713.5  L34347336241.6  L34350192845.1  L36168614955.6  L37905822001.6  L37907098573.1  L3820537077.6   L38237953557.5  L38574091387.6  L38732773782.8  L39873495720.9  L39873509400.10 L39935534662.5  L40987795105.9  L40987796497.9  L41462195249.6  L41464528589.1  L41487663582.211L42207636134.211L4284441030.5   L43283476011.6  L44480858074.181L44480858074.211L45042784385.9  L45042786865.10 L45697054771.6  L46130367529.5  L47044406740.211L47290142471.1  L49401863356.10 L49664744988.1  L50147087326.181L51726009793.5  L52715614025.7  L52715624172.9  L52715629660.9  L52715906507.3  L54805739926.221L54928118530.8  L55630787796.181L56732428411.6  L57453287201.9  L57453292945.9  L59618212557.1  L59620532273.6  L60290916219.6  L60342676230.9  L61441813035.6  L63175642573.1  L63176922929.6  L63847289467.6  L64998201643.6  L65171700574.211L66248902535.1  L9744456571.6   L9788620630.3   L9788853361.9   L9788864193.9   R38730382473.161R38730382473.19800000H01N01i02D02E02F02a03903Q03i04A04Y04Z04[05\06406506M06e07e08=08U08m09E09F09G09_09`09a0:j0;B0;C0;^0=?0>?0>l0?K0?L0@L0AL0Ad0B<0B=0BU0CU0Cm0DE0D]0E50EM0Ee0F=0F>0FV0GX0H00HH0H`0I80IS0Ik0JT0JU0J_0J`0Ja0Je0Ji0K:0KA0KL0KP0KX0KY0KZ0L30LK0LR0LV0MZ0M^0Mb0N70NH0NL0OG0O_0O`0Oh0Oi0Oj0PC0PD0PE0PF0PN0P_0Q70QO0QS0QW0Q[0Q_0Qc0Qg0R10R50R<0RY0Rm0Rn0S20S30SS0SW0S[0TV0UQ0UU0UY0UZ0U[0V30V40VI0VM0VN0VR0V\0V`0W[0Wl0XE0XF0XG0XH0X`0Xo0Y00Y70Y80YX0Y\0Y`0Yg0Yn0Z20Z60Z:0ZA0ZE0[@0[D0[K0[S0[T0[U0\Q0]MS2ra2sp3PKA1C3PAR2bs3PRBS1L2HI2ra2sp2h03PKA1C3PAR1P2bs3NZP3NZR4HTOP2C01h3PRB2HT2HB5Ha_st5Hl_stS2ra2sp3PKA1C2lo3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRB2HBFFS2ra2sp3PKA1C2lo3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBFFS1L3HLS2ra2sp3PKA1C2lo3PAR1P2bs3NZP3NZR3SLO2C03PRB2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3PRBFS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BAC3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBFFS2ra2sp3PKA1C3PAR2bs3PRBFFS1L3HLS2ra2sp3PKA1C2lo3PAR1P2bs3NZP3NZR3SLO3ACL3DHI2C03PRB2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3PRBFS2ra2sp3PKA1C2lo3PAR2bs3PRBS2ra2sp3PKA1C2lo3PAR3LEN1P2bs3x643PRB3x523x653x663x674POST3x681H1L3HLS3NZP3NZR3SLO3ACL3SPA3ACP2C0S1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BAC3PRBS2ra2sp3PKA1C3PAR1P2bs3SPR3PRB2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3SPR3PRB2HBFS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI3ACP2C03PRB1a1HS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI3ACP2C03PRB1a1HS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBFS2ra2sp3PKA1C3PAR2bs3PRBS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BAC3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBFS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C2lo3PAR2bs3PRB3x501H1L3HLS3NZP3NZR3SLO3ACL3SPA3ACP2C0S2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRB2HBS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR1P2bs3PRB2HB5Ha_st5Hl_stFS2sp2lo2bsFFS2spS2spS1L3HLS2sp2lo3SLOS2sp2loS2r33RR32NZS2spS2sp3SPAFFS1L3HLS2sp2lo3SLO3ACL3ACPS2ra2sp3PKA1C3PAR2bs3PRBS2sp2loS2spS1L3HLS2ra2sp3PKA1C2lo3PAR1P2bs3NZP3NZR3SLO2C03PRB2HB5Ha_st5Hl_st2HDS2spS2spS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOS2spS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3ACP2C03PRB2HDS2ra2sp3PKA1C3PAR2bs3PRBFS2sp3SPAFFS1L3HLS2sp2lo3SLO3ACL3ACPFFFS2sp3SPAS1L3HLS2sp2lo3SLOS2ra2sp3PKA1C3PAR2bs3PRBS2ra2sp3PKA1C3PAR2bs3PRBS2spS2spS2spS2spS2spS2spS1L2lo3ACLS2loS2sp2loS1L3HLS2sp2lo3SLO3ACL3SPR3ACPS1L3HLS2sp2lo2bs3SLOFS2spFS1L3HLS2sp2lo3BUF2bs3SLO3ACL3BACS2spS2spS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3ACP2C03PRB2HDS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3ACP2C03PRB2HDS2spS2spFFS1L2sp2lo3BUF2bs3ACL3BACFS1L3HLS2sp2lo3SLO3ACLS2spFS2spS2sp2lo2bsS2spS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3ACP2C03PRB2HDS1L3HLS2sp2lo3SLOS1L3HLS2sp2lo3SLO3ACL3ACPFFFS2ra2sp3PKA1C3PAR2bs3PRBS3LEN1P2bs4LEN0FS2sp2loFS1L3HLS2sp2lo3BUF2bs3SLO3ACL3BACS2spS2spS2sp2loS2sp2bsS2spS2spS2spS2sp2loS2spS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3ACP2C03PRB2HDS2spS2sp2loS2sp3SPAFFS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3SPR3ACP2C03PRBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3SPR3ACP2C03PRB". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP LEN0 PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM"] Lemma spec0_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_K ()) "Ph,(2;.$6.VL,VHI,)PLBi,(2.$3.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$2<.Plnw,(0.&40.)Pvw,(0.&40.)Pscj,(2.(0.&8.))Ppj,(2.(0.&8.))Pgj,(2.(0.&8.))Prj,(2.(0.&8.))Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px9,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px18,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Px25,(0.&40.)Px26,(0.&40.)Px27,(0.&40.)Px28,(0.&40.)Px29,(0.&40.)Px30,(0.&40.)Px31,(0.&40.)P,(37.VL,VHI,Vmo0,Vh0,VLB,R24.R23.(?.$3.)R22.R21.)P,(22.$6.VL,VLB,(23.&40.Vsp,)(;.(24.$4.$4.)(25.$4.$4.$26.(>.$26.+1.))(;.(24.$4.$4.)(25.$4.$4.$27.(>.$27.+38.))(?.(24.$4.$4.))))Vm0,R23.)P,(10.$6.R24.VPAR,(38.Vtg,Vpd,VLEN,VP,))P,(10.$6.R25.(>.(23.&40.Vsp,)-200.)(;.$11.(12.#8.R21.)(?.$11.)))P,(10.$6.R26.(>.(23.&40.Vsp,)-1?8.)(;.$11.(12.#<0.R20.)(?.$11.)))P,(10.$6.R27.(>.(23.&40.Vsp,)-138.)(;.$11.(12.#4.R22.)(;.$11.(39.R24.)(?.$11.))))P,(10.$6.R28.(>.(23.&40.Vsp,)-130.)(;.$11.(16.R26.)(?.$11.)))P,(10.$6.R29.(>.(23.&40.Vsp,)-128.)(;.$11.(12.#<0.R22.)(?.$11.)))P,(10.$6.R2:.(>.(23.&40.Vsp,)-68.)(;.$11.(16.Vs11,)(;.$11.(16.Vs10,)(;.$11.(16.Vs9,)(;.$11.(16.Vs8,)(;.$11.(16.Vs7,)(;.$11.(16.Vs6,)(;.$11.(16.Vs5,)(;.$11.(16.Vs4,)(;.$11.(16.Vs3,)(;.$11.(16.Vs2,)(;.$11.(16.Vs1,)(;.$11.(16.Vs0,)(;.$11.(16.Vra,)(?.$11.)))))))))))))))P,(3:.$6.R2;.Vlo,(>.(23.&40.Vsp,)-200.))(2>.$6.R2;.(2?.$6.VL,VHI,$7.$30.$31.$26.$27.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(32.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(33.(34.R24.(15.&40.(>.(23.&40.Vsp,)-200.))Vgp,Vtp,R23.R22.R21.(15.&40.VPKA,)R20.(15.&40.VPAR,)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)VF,(15.&40.+296;4.)Vfc,(35.(0.&40.))R2<.(36.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros CX PX HPAR FR0 FRG FRM FRL FRR FR ST.
    dpose CX as (HH & HT & MF & MI & SOK & EXT & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    pose proof (rw_cells_bound _ _ _ _ HPAR) as PRB. cbn [cells_size csize Nat.add buf_cells] in PRB.
    (* [comment removed for export] *)
    pose proof (U_ecp_group_init_spec U_MT) as SGI. unfold ecp_group_init_stmt, ecp_group_init_post, U_ECP_GROUP_INIT, ECP_GROUP_SIZE in SGI.
    pose proof (munch_refl [(G, G + 192); (lo, bv_unsigned sp + -512)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep.
    acallx_sp (bv_unsigned sp + -512) (eapply SGI with (A := G) (LB := LBi) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
            [ exact FRG | clear -SPA SPR; lia | clear -SLO HLS ACL ACP; lia | exact ST | clear -SLO HLS; lia | clear -SPA SPR; lia
            | right; clear; lia | exact MI | reflexivity | reflexivity ]).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with W : wmono usegs m m1 |- _ => rename W into WM1 end. rename MU into MU1.
    match goal with M : mem_inv usegs m1 |- _ => rename M into MI1 end.
    match goal with Hg : ecp_group_at usegs U_MT m1 LBi _ _ |- _ => rename Hg into HG1 end.
    match goal with S : stk usegs m1 lo _ |- _ => rename S into ST1 end.
    destruct (ctx_munch' _ _ _ _ _ _ _ CX PX MU1 WM1 MI1 ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CX1 PX1].
    lazymatch type of HG1 with ecp_group_at _ _ _ _ _ (grp_init _ ?idpad' ?pP' ?pA' ?pB' ?pX' ?pY' ?pZ' ?pN' ?hpad') =>
      ddestruct (tmp_ok_init7 m1 LBi G idpad' pP' pA' pB' pX' pY' pZ' pN' hpad' HG1) as (TOK1 & FRH & FRT);
      set (dN := mpd_init (G + 104) pN') in TOK1; set (dP := mpd_init (G + 8) pP') in TOK1; set (dA := mpd_init (G + 24) pA') in TOK1;
      set (dB := mpd_init (G + 40) pB') in TOK1; set (dX := mpd_init (G + 56) pX') in TOK1; set (dY := mpd_init (G + 72) pY') in TOK1;
      set (dZ := mpd_init (G + 88) pZ') in TOK1
    end.
    clear MU1 WM1 CX PX MK HH HT MF SOK IDS SGI HG1 HBR. try clear MI. try clear ST.
    dpose CX1 as (HH & HT & MF & _ & SOK & _ & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    change ([] : list blk) with (tmp_blocks [dN; dP; dA; dB; dX; dY; dZ]) in CX1.
    (* [comment removed for export] *)
    unfold buf_cells in HPAR.
    zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of FRR with rw_cells ?sg ?mx ?A [CB 192 ?j] =>
      change (rw_cells sg mx A [CB 192 j]) with (rw_cells sg mx A ([] ++ CB 192 j :: [])) in FRR;
      apply (rw_cells_split_CB sg mx A [] 192 j [] [8; 184]%nat) in FRR; [| reflexivity]; cbn [mk_CB_cells app] in FRR
    end.
    cb8_to_c8 FRR ([] : list cell).
    chunk_split FRR 1%nat FRP FRR'. rename FRR' into FRR.
    replace (REF + 8) with (bv_unsigned sp + -288) in FRR by (clear; lia).
    pose proof (munch_refl [(REF, REF + 8)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with W : wmono usegs m1 m2 |- _ => rename W into WM2 end. rename MU into MU2.
    match goal with M : mem_inv usegs m2 |- _ => rename M into MI2 end.
    destruct (ctx_munch' _ _ _ _ _ _ _ CX1 PX1 MU2 WM2 MI2 ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CX2 PX2].
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR1 _].
    pose proof (tmp_ok_munch_fine usegs L _ _ _ _ _ _ _ TOK1 MU2 WM2 (proj1 (proj2 (proj2 (proj2 CX1)))) MI2
                  ltac:(subst dN dP dA dB dX dY dZ; intros d Hd; cbn in Hd; decompose [or] Hd; try contradiction; subst d; cbn; clear; repeat split; lia)
                  ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) HBR1) as TOK2.
    clear MU2 WM2 CX1 PX1 TOK1 MK HH HT MF SOK IDS HBR1. try clear MI1.
    dpose CX2 as (HH & HT & MF & _ & SOK & _ & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    (* [comment removed for export] *)
    zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN; [pnull KN|].
    (* [comment removed for export] *)
    pose proof (ctx_bytes' m2 PX2) as HBS2.
    chunk_split FRM 1%nat FMa FMb.
    replace (bv_unsigned sp + -312 + 4) with (bv_unsigned sp + -308) in FMb by (clear; lia).
    pose proof U_asn1_get_int_spec as SGN. unfold asn1_get_int_stmt, asn1_get_int_post, U_ASN1_GET_INT in SGN.
    pose proof (munch_refl [(lo, bv_unsigned sp + -512); (REF, REF + 8); (bv_unsigned sp + -308, bv_unsigned sp + -304)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep. zstep. zstep.
    acallx_sp (bv_unsigned sp + -512)
      (eapply SGN with (PP := REF) (VALP := bv_unsigned sp + -308) (P := P) (END := PEND) (BUF := BUF) (bs := bs) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
       first [ exact FRP | exact FMb | exact HBS2 | exact MI2 | eassumption | reflexivity
             | clear -BP LEN0 PL B63; lia
             | clear -BAC ACL SLO HLS; lia
             | clear -SPA SPR; lia | clear -ACL ACP SLO HLS; lia | clear -BUF0; lia
             | clear; lia | clear -SLO HLS; lia | right; clear; lia
             | f_equal; clear; lia
             | match goal with |- ?g => idtac "GILEFT" g end ]).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : rw_cells usegs m3 REF [C8 (Z_to_bv 64 ?q)] |- _ => rename H into FRP3; rename q into p3 end.
    match goal with H : rw_cells usegs m3 (bv_unsigned sp + -308) [C4 ?v] |- _ => rename H into FMb3; rename v into vw3 end.
    match goal with H : - (127) < ?r <= 0 |- _ => rename H into RR3; rename r into r3 end || match goal with H : _ < ?r <= 0 |- _ => rename H into RR3; rename r into r3 end.
    match goal with H : P <= p3 <= _ |- _ => rename H into PB3 end.
    match goal with M : mem_inv usegs m3 |- _ => rename M into MI3 end.
    match goal with W : wmono usegs m2 m3 |- _ => rename W into WM3 end. rename MU into MU3.
    match goal with S : stk usegs m3 lo _ |- _ => rename S into ST3 end.
    destruct (ctx_munch' _ _ _ _ _ _ _ CX2 PX2 MU3 WM3 MI3 ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CX3 PX3].
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR2 _].
    pose proof (tmp_ok_munch_fine usegs L _ _ _ _ _ _ _ TOK2 MU3 WM3 (proj1 (proj2 (proj2 (proj2 CX2)))) MI3
                  ltac:(subst dN dP dA dB dX dY dZ; intros d Hd; cbn in Hd; decompose [or] Hd; try contradiction; subst d; cbn; generalize SLO HLS ACL; clear; intros; repeat split; lia)
                  ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) HBR2) as TOK3.
    clear MU3 WM3 CX2 PX2 TOK2 MK HH HT MF SOK IDS HBR2 HBS2 SGN.
    match goal with H : ?x = Z_to_bv 64 r3 |- _ => subst x end.
    lazymatch type of FRR with rw_cells _ _ _ [CB 184 ?j] => set (rj2 := j) in FRR; clearbody rj2 end.
    chunk_join FMa FMb3 FRM.
    lazymatch type of FRH with rw_cells _ _ _ [CB 8 ?j] => set (hj := j) in FRH; clearbody hj end.
    lazymatch type of FRT with rw_cells _ _ _ [C8 ?a; C8 ?b; CB 56 ?j] => set (tj := j) in FRT; clearbody tj; set (pb := a) in FRT; clearbody pb end.
    assert (SI3 : SPINV' h LBi m3 mo dN dP dA dB dX dY dZ p3 lnw vw3 pb pb scj hj tj pj rj2).
    { split; [exact CX3|]. split; [exact PX3|]. split; [exact TOK3|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact FRP3|]. split; [exact PB3|]. split; [exact FRR|]. split; [exact FRL|]. split; [exact FRM|].
      split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FR| exact ST3]. }
    pose proof CX3 as (HH3 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    zstep. if_cases K3; zify_cond K3.
    - (* [comment removed for export] *)
      eapply specA_walk; [exact SI3| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
    - assert (NZ : r3 <> 0) by (intros ->; apply K3; reflexivity).
      eapply spec_erradd'; [exact SI3| clear -RR3 NZ; lia| exact MK3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End EP.
