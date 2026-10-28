(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_ecp_grp_id_list U_ecp_point_free U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type U_pk_ecc_set_group U_ecp_sinv U_string U_oid U_oidv U_oid_ec_grp U_oid_ec_grp_v U_pk_ecparams_A U_pk_ecparams_B.
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
Ltac2 gd_tbl_P_pk_ecparams_C () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpd_fp"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_B.ctx_now"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_ok"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.pk_use_ecparams_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


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
  #[using="HI m0 mo0 h0 LB HH0 INC INB ACP"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_C ()) "(0.(1.+1000.(2.VL,))(0.(1.=VC,)(0.(3.$4.(5.VC,+10.)=)(0.(6.(7.VC,+100.)(2.VL,))(0.(8.(6.(7.VC,+100.)(9.VL,))(6.(:.VL,)VC,))(0.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(2.VL,))(8.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(9.VL,))(6.(:.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0' & C16' & _ & CAC' & CIM'). cbn in C0', C16', CAC', CIM'.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC' & BIM'). cbn in BAC', BIM'. auto 10.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2647750340.6  L2726914452.6  L52616404933.1000000D00X016S1L3PKA3PKD2I12I22I3S1L3PKA3PKD2I12I22I3S1L2HI2sp2h03PKA2lo3DSP1a2Ha1Q". (* [comment removed for export] *)
  #[using="HI h0 lo HPKA0 DSP CWP PKD IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_C ()) "Pm,P,(=.&40.)(>.(=.&8.))P,(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,R1.)(18.$10.R2.VPKA,(12.$19.(1:.(1;.&40.Vinfo,))(12.$19.(1:.(1;.&40.VC,))(17.$19.))))")
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
  #[using="IDL"] Lemma IL4 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_C ()) "Pa,$4.P,(8.(0.(6.$15.R1.)(1.R1.(7.$15.+1.)))(0.(6.$16.R1.)(1.R1.(7.$16.+38.))))(0.(1<.VL,R2.)(1=.(1>.VL,R2.)))")
(* [comment removed for export] *).
  Proof. exact (proj2 (proj2 (proj2 IDL))). Qed.
  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.
  Notation G := (bv_unsigned sp + -504).
  Notation CTX := (ctx_now L HI mo0 h0 LB).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L2118719492.112 L58374850732.11200001C01`S1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3DSP3DPC3NZR3DSR2RC3SLO3ACL3ACP3CAC2C01d1a1k2H12P4S2ra2sp3PKA1C3PAR2bs1d1a1k2H2". (* [comment removed for export] *)
  #[using="HLS ra sp PKA C lo PAR bs NZP DSP DPC NZR DSR RC SLO ACL ACP CAC C0"] Lemma fp_disjoint_struct : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_C ()) "Pd,$1?.Pm,P,(=.&40.)(>.(=.&8.))PLBi,(20.$21.)Pa,$4.Pk,$4.P,(22.$10.R4.R3.R5.)P,(23.(13.$4.$4.)Lb,(13.$4.$4.)(24.VL,(25.$4.$4.R1.)(26.$4.$4.R1.))R4.)P,(6.(2.VL,)R4.)P,(8.(6.(7.R5.R4.)(27.R8.))(6.(7.(27.R8.)+10.)R5.))(28.(29.R9.)R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros d m LBi a k MD HBR H1 H2.
    assert (P4 : md_own d = LHeap -> md_p d + 4 * md_n d <= alloc_ceiling)
      by (intros O; ddestruct (mpdr_blk_facts usegs L m LBi d MD O HBR) as (_ & _ & _ & P4 & _); exact P4).
    unfold mpd_fp. destruct (md_own d); cbn; (split; [lia|]); [exact I| | exact I]. specialize (P4 eq_refl). split; [lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02I0?L10372898842.6 L10644870316.8 L10837299463.1 L10970720863.22L12384472927.29L12455422775.1 L12857244009.1 L1322275239.33 L1386317440.283L14429712647.1 L1559264055.1  L15936470021.4 L15946219575.1 L162905823.33  L16605722549.1 L16975954714.7 L1717687351.1  L1792247221.1  L18891495706.6 L18933043916.4 L18967883615.28L19370141991.31L2027587433.1  L20361976947.6 L20380070055.23L21704771767.6 L22409264922.6 L22480661269.6 L2281494464.8  L23270378039.1 L24748498046.3 L24748498429.4 L24750596166.2 L24875869801.1 L26068803996.8 L26684090167.1 L26892418956.1 L2692260320.2  L2692261741.2  L2692261868.2  L2692263678.2  L27105925383.1 L27303991657.1 L27320578911.31L27586806161.7 L27588789143.3 L27588791700.4 L27901888243.12L28465617323.2 L28467717136.4 L28897400179.6 L294917907.6   L297281212.7   L30352486965.7 L30352998933.6 L30392002547.6 L30718654727.1 L30944687130.6 L31422690343.26L31471788297.3 L31986007145.1 L33903858527.30L34447776282.6 L34493188407.1 L35419500961.0 L37810932841.1 L38224815777.0 L38732773782.8 L38738169695.25L39861333983.32L4048567135.26 L41122489291.6 L42492165892.1 L42983133978.6 L4305547029.6  L43459629863.25L44195387925.6 L44569460897.0 L45374645815.1 L45681558685.1 L45855348509.8 L4612254027.6  L46132990536.1 L46549747940.7 L46552119491.6 L46603236713.1 L46685274549.1 L46774934276.1 L47753857301.6 L48062193029.6 L48063759353.7 L48395073079.1 L48717661495.1 L48834180257.0 L49014974569.1 L49664744988.1 L49687448620.8 L49885414436.8 L50600009991.1 L51041058482.2 L51425573045.1 L51600178763.6 L51978278951.30L52104085303.1 L53717961577.1 L54006843703.1 L54973495411.6 L55019548186.6 L55156550987.6 L55314927287.1 L55497621031.28L56608396471.1 L57498839298.34L57563749431.1 L57841656325.4 L5856141729.0  L58629368110.7 L58631724931.6 L59194810551.1 L59229008890.4 L59263549952.4 L59263550339.3 L59308585607.10L59538824041.1 L60495735557.4 L61120265865.3 L61136161994.8 L61431508330.9 L61953854621.1 L62627930679.1 L6332228533.1  L64016262951.29L65827785291.6 L66184239967.27L66867980551.1 L66872757087.23L6699898106.4  L67055961370.6 L67534554407.27L67677319607.1 L6791302325.1  L68239705399.1 L7018928183.1  L7333724711.32 L749172757.6   L8322245898.4  L8325611891.6  L8328458975.24 L8343131559.24 L9263949493.1  L9786670416.7  L9788617045.4  L9788620630.3  00000E00\00`00d00h00l01001A01B01F01J01U01Y01]01a01b01f01j02?02C02G02X02\03103B03C03X03\04704;04C04K04P04T04k04o05305405505605705;05?05C05D05E05F05\05a05g06<06=06U06l06m07B07F07[07l08608:08>08S08W08X08\08]09:09>09B09F09J09N09c09g0:80:<0:=0:A0:E0:`0:d0:h0;@0;A0;E0;I0;M0;Q0;R0;h0;l0<00<10<50<90<T0<U0<Y0<Z0<^0<b0=30=70=;0=?0=T0=i0=m0>10>B0>F0>W0>[0>f0>g0??0?@0?D0?Q0?Z0?b0@C0@G0@R0@]0A80A90A=0AA0AE0AV0AZ0A^0Ab0Af0B30BH0BY0B]0Ba0Be0Bi0C:0C>0CJ0C_0Cc0D40D80D90D:0DBS1L3HLS2sp2lo3SLO3ACLS1L1C1H2H02H13CIM2H22H3S2spS2spS2spS2spS2spS1L2sp2lo3SLO3HLSFS2spS2spS2sp1a1k2H2S2spS2spS2spFS2spS2spS1L3HLS2sp2lo3SLO3ACLS2r2S2spS1L2sp2lo3SLO3HLSS2spS1L3HLS2sp2lo3SLO3ACLS1L2sp2lo3SLO3HLSFS1L3HLS2sp2lo3SLO3ACLS2spS1L3HLS2sp2lo3SLO3ACL2dN2P4S2spS1L1H2H0S1L1H2H0S1L1HS2spS1L1C1H2H02H13CIM2H22H3S2spS2spFFFFS2spS2spS2spFFFS1L2HI2sp2h04HTOP1a2HaS1L1HS1L2H1S1L3HLS2sp2lo3SLO3ACLFS1L2HI2sp2h04HTOP3x592HTS1L2HI2sp2h04HTOP2h42HTFS1L3HLS2sp2lo3SLO3ACLS2spS1L3HLS2sp2lo3SLO3ACLS1L2sp2lo3SLO3HLSS2r22RR2HqS2spS2spS1L3HLS2sp2lo3SLO3ACLS2spSS2spSS1L3HLS2sp2lo3SLO3ACL3SPR3ACPS2spS2spS2spS2spS2spS1L3HLS2sp2lo3SLO3ACLS2spS1L2sp2lo3SLO3HLSS2spSS2spS2spS1L3HLS2sp2lo3SLO3ACL2dA2P4S2spS2spS1L2HI2sp2h04HTOP3x412HTFS2spS2spS2spS2spFS1L2HI2sp2h04HTOP1h2HTS2spS2spSS2spS2spS1L3HLS2sp2lo3SLO3ACL2dB2P4FS2spFS2spS2spS1L2sp2lo3SLO3HLSS2spS2spS2spS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLO3ACLS2spS2spS1L2sp2lo3SLO3HLSS2spS1L2sp2lo3SLO3HLSS2spS2sp1a1k2H2SS1L2HI2sp2h04HTOP3x772HTFS2spS1L2sp2lo3SLOS1L2H02H1S1L1H2H0S1L3HLS2sp2lo3SLO3ACL3DHI1a2Ha2HdS2spS2sp1a1k2H2S2sp2a'3Ha'S1L3HLS2sp2lo3SLO3ACL2dP2P4FS2spS2spS2spS1L2sp2lo3SLO3HLSS2spS2spS2spS2spS1L2sp2lo3SLOS1L3HLS2sp2lo3SLO3ACLS1L2sp2lo3SLO3HLSS2spS2spS2spS2spS1L2sp2lo3SLO3HLSS2spS2r22RR1q2HqS1L3HLS2sp2lo3SLO3ACLS2spS1L2sp2lo3SLO3HLSS2spFFS2sp3SPA". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma cleanup_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_C ()) "Ph,(2:.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$2;.Pr2,$4.Ps1w,(=.&40.)PdN,$1?.PdP,$1?.PdA,$1?.PdB,$1?.PdX,$1?.PdY,$1?.PdZ,$1?.Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Pmj,(20.(=.&8.))Prj,(20.(=.&8.))Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px19,(=.&40.)Px20,(=.&40.)Px21,(=.&40.)Px22,(=.&40.)Px23,(=.&40.)Px24,(=.&40.)Px25,(=.&40.)Px26,(=.&40.)Px27,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(2<.VL,VHI,Vmo0,Vh0,VLB,R2;.R2:.(2=.(12.$1?.R25.(12.$1?.R24.(12.$1?.R23.(12.$1?.R22.(12.$1?.R21.(12.$1?.R20.(12.$1?.R1?.(17.$1?.)))))))))R29.R28.)P,(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,R2:.)P,(2>.$10.R2;.R2<.(7.(11.&40.Vsp,)-1?8.)+<0.(12.$1?.R27.(12.$1?.R26.(12.$1?.R25.(12.$1?.R24.(12.$1?.R23.(12.$1?.R22.(12.$1?.R21.(17.$1?.)))))))))P,(3.$4.(27.R28.)(7.(7.(11.&40.Vsp,)-1?8.)+68.))P,(3.$4.(27.R28.)(7.(7.(11.&40.Vsp,)-1?8.)+8.))P,(3.$4.(27.R28.)(7.(7.(11.&40.Vsp,)-1?8.)+18.))P,(3.$4.(27.R28.)(7.(7.(11.&40.Vsp,)-1?8.)+28.))P,(3.$4.(27.R28.)(7.(7.(11.&40.Vsp,)-1?8.)+38.))P,(3.$4.(27.R28.)(7.(7.(11.&40.Vsp,)-1?8.)+48.))P,(3.$4.(27.R28.)(7.(7.(11.&40.Vsp,)-1?8.)+58.))P,(0.(1.(2?.(30.+2.+1?.))R31.)(6.R31.=))P,P,(3.$4.R32.=)(31.$4.Lid,$4.(0.(3.(=.&40.)R33.(1;.&40.R1.))(0.(6.=R1.)(1.R1.(30.+2.+1?.)))))P,(18.$10.R35.(7.(11.&40.Vsp,)-200.)(12.$19.(32.#8.R2:.)(17.$19.)))P,(18.$10.R36.(7.(11.&40.Vsp,)-1?8.)(12.$19.(32.#8.R2:.)(17.$19.)))P,(18.$10.R37.(7.(7.(11.&40.Vsp,)-1?8.)+78.)(12.$19.(32.#48.R2:.)(17.$19.)))P,(18.$10.R38.(7.(11.&40.Vsp,)-138.)(12.$19.(32.#10.R2:.)(17.$19.)))P,(18.$10.R39.(7.(11.&40.Vsp,)-128.)(12.$19.(32.#<0.R2:.)(17.$19.)))P,(18.$10.R3:.(7.(11.&40.Vsp,)-68.)(12.$19.(1:.Vs11,)(12.$19.(1:.Vs10,)(12.$19.(1:.Vs9,)(12.$19.(1:.Vs8,)(12.$19.(1:.Vs7,)(12.$19.(1:.Vs6,)(12.$19.(1:.Vs5,)(12.$19.(1:.Vs4,)(12.$19.(1:.Vs3,)(12.$19.(1:.Vs2,)(12.$19.(1:.Vs1,)(12.$19.(1:.Vs0,)(12.$19.(1:.Vra,)(17.$19.)))))))))))))))P,(33.$10.R3;.Vlo,(7.(11.&40.Vsp,)-200.))(34.$10.R3;.(35.$10.VL,VHI,$36.$37.$38.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(39.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(3:.(3;.R2<.(1;.&40.(7.(11.&40.Vsp,)-200.))Vgp,Vtp,R2;.R2:.R29.(1;.&40.VPKA,)R39.R28.R27.R26.R25.R24.R23.R22.R21.(1;.&40.R3:.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)VF,(1;.&40.+29;:4.)Vfc,(3<.(=.&40.))R3<.(3=.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. (intros dd_H; ddestruct dd_H as (HH & HT & MF & MI & SOK & EXT & IDS); intros PX TOK EN EP EA EB EX EY EZ RR IDW FR0 FRH FRT FRM FRR FR ST).
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (U_mpi_free_spec L HI HFREE HLS SW DIMG) as SF. unfold mpi_free_stmt, mpi_free_post, U_MPI_FREE in SF.
    (* [comment removed for export] *)
    Ltac free_one SF d ED :=
      lazymatch goal with
      | HH : HEAP usegs L HI ?hc ?LBc ?mc ?moc, TOK : tmp_ok usegs ?mc ?LBc _ _ (d :: ?rest), MI : mem_inv usegs ?mc,
        HT : heap_top usegs L HI ?hc = _, MF : mo_frame mo0 ?moc, PX : heap_presx usegs L LB (bv_unsigned sp) _ m0 ?mc,
        IDS : ecp_ids_state usegs _ _ ?mc, EXT : lb_ext LB _ ?LBc, ST : stk usegs ?mc lo _, SOK : statics_ok usegs L ?mc, MK : MOK ?moc
        |- aevtM _ _ _ (MS _ _ _ _ _ ?mc _) =>
        let HBRc := fresh "HBRc" in let HAPc := fresh "HAPc" in let NDc := fresh "NDc" in
        let MDr := fresh "MDr" in let SGd := fresh "SGd" in let BDd := fresh "BDd" in
        destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBRc HAPc];
        pose proof (HND _ _ _ _ HH) as NDc;
        pose proof (proj1 (Forall_forall _ _) (proj1 TOK) _ (or_introl eq_refl)) as MDr;
        pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 TOK)) _ (or_introl eq_refl)) as BDd; cbn beta in BDd;
        destruct MDr as [MDr SGd];
        eapply aevtM_cut;
        [ eapply SF with (lo := lo) (h := hc) (LB := LBc) (X := md_addr d) (sw := Z_to_bv 64 (md_sg d)) (n := md_n d) (P := md_p d)
                           (limbs := md_limbs d) (pad := md_pad d) (own := md_own d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
          first [ exact HH | exact MDr | exact (proj1 BDd) | exact TP | exact CA | eassumption
                | rewrite ED; reflexivity
                | rewrite ED; f_equal; clear; lia
                | (* [comment removed for export] *) rewrite ED, HT; intros a Ha; left; clear -Ha SLO HLS HTOP ACL ACP; lia
                | (* [comment removed for export] *)
                  let O := fresh "O" in let P4 := fresh "P4" in
                  intros O; destruct (mpdr_blk_facts usegs L _ _ _ MDr O HBRc) as (_ & _ & _ & P4 & _); rewrite ED; clear -P4 ACL SLO HLS; lia
                | (* [comment removed for export] *) rewrite ED; let a := fresh "a" in let Ha := fresh "Ha" in let Hd := fresh "Hd" in
                  intros a Ha Hd; exfalso; clear -Ha Hd DHI ACL SLO HLS; lia
                | clear -SLO; lia | clear -HTOP HT; lia | clear -SPA SPR; lia
                | match goal with |- ?g => idtac "FREELEFT" g end ]
        | let PO := fresh "PO" in let ms' := fresh "ms'" in let mo' := fresh "mo'" in let E := fresh "E" in
          let MI2 := fresh "MI2" in let ST2 := fresh "ST2" in let MF2 := fresh "MF2" in let HT2 := fresh "HT2" in
          let HH2 := fresh "HH2" in let CH2 := fresh "CH" in let PX2 := fresh "PX2" in let SOK2 := fresh "SOK2" in
          let TOK2 := fresh "TOK2" in let EXT2 := fresh "EXT2" in let IDS2 := fresh "IDS2" in let PXn := fresh "PXn" in
          let HT3 := fresh "HT3" in let MF3 := fresh "MF3" in
          intros ms' mo' PO; destruct_exs PO;
          let E1 := fresh "E1" in let E2 := fresh "E2" in destruct PO as [E PO]; injection E as E1 E2; subst ms' mo';
          rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia);
          destruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & CH2 & PX2 & SOK2);
          rewrite ED in CH2;
          change (mpi_free_LB (md_own d) (md_p d) (md_n d) LBc) with (lb_free_mpd d LBc) in HH2, PX2;
          change ((md_addr d, md_addr d + 16) :: mpi_free_X (md_own d) (md_p d) (md_n d)) with (mpd_fp d) in PX2;
          lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end;
          lazymatch type of HH2 with HEAP _ _ _ ?h2 _ ?m2 ?mo2 =>
          (* [comment removed for export] *)
          pose proof (tmp_ok_free usegs L mc m2 LBc (lb_free_mpd d LBc) _ _ d rest (bv_unsigned sp + -512) [] TOK PX2 MI MI2 HBRc HAPc
                        (tmp_ok_keep_free usegs L _ _ _ _ _ _ TOK HBRc) (Forall_nil _) ltac:(clear; lia) ltac:(clear -ACL SLO HLS; lia)) as TOK2;
          pose proof (lb_ext_free LB (tmp_blocks rest) LBc d EXT NDc (tmp_ok_head_fresh usegs _ _ _ _ _ _ TOK)) as EXT2;
          (* [comment removed for export] *)
          pose proof (ecp_ids_state_presx usegs L _ _ _ _ _ _ _ IDS PX2 IDL
                        ltac:(eapply (fp_disjoint_data usegs L); [exact MDr| exact HBRc| generalize IL1; clear; intros; lia| generalize IL2 IL3; clear; intros; lia| exact DHI| rewrite ED; clear -ACL SLO HLS; lia| exact DI1| exact DI2])
                        ltac:(eapply (fp_disjoint_data usegs L); [exact MDr| exact HBRc| generalize IL1 IL2; clear; intros; lia| generalize IL3; clear; intros; lia| exact DHI| rewrite ED; clear -ACL SLO HLS; lia| exact DI1| exact DI2])) as IDS2;
          pose proof (heap_presx_trans usegs L _ _ _ _ _ _ PX
                        (presx_caller usegs L LB (lb_free_mpd d LBc) LBc (bv_unsigned sp) (bv_unsigned sp + -512) _ (mpd_fp d) mc m2 PX2
                           (fun b Hb => lb_ext_sub _ _ _ _ EXT2 Hb) ltac:(clear; lia) ltac:(clear -ACL SLO HLS; lia) HBRc HAPc NDc
                           (fun b Hb => lb_ext_sub _ _ _ _ EXT Hb)
                           (fp_items_mpd usegs L mc LB LBc _ (bv_unsigned sp) _ d MDr HBRc EXT
                              ltac:(intros b Hb; unfold tmp_blocks; cbn [flat_map]; apply in_app_iff; left; exact Hb)
                              ltac:(rewrite ED; clear -ACL SLO HLS; lia) ltac:(rewrite ED; clear; lia))
                           DHI DI1 DI2)) as PXn;
          (* [comment removed for export] *)
          repeat match goal with
          | Hc : rw_cells usegs mc ?a ?cs |- _ =>
              first [ apply (heap_presx_rw_cells usegs L _ _ _ mc m2 a cs PX2) in Hc;
                      [ | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length];
                          let a' := fresh "a'" in let Ha' := fresh "Ha'" in intros a' Ha'; left; clear -Ha'; lia
                        | eapply (fp_disjoint_struct d mc LBc); [exact MDr| exact HBRc| clear -ACL SLO HLS; lia
                          | rewrite ED; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; clear; lia] ]
                    | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
          end;
          clear HH MI ST TOK EXT IDS PX HBRc HAPc NDc MDr SGd BDd MK SOK;
          pose proof (eq_trans HT2 HT) as HT3; clear HT HT2; rename HT3 into HT;
          pose proof (mo_frame_trans _ _ _ MF MF2) as MF3; clear MF MF2; rename MF3 into MF;
          rename HH2 into HH; rename MI2 into MI; rename ST2 into ST; rename SOK2 into SOK; rename TOK2 into TOK; rename EXT2 into EXT;
          rename IDS2 into IDS; rename PXn into PX; clear PX2;
          pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK
          end ]
      end.
    zstep. zstep. free_one SF dN EN.
    zstep. zstep. free_one SF dP EP.
    zstep. zstep. free_one SF dA EA.
    zstep. zstep. free_one SF dB EB.
    (* [comment removed for export] *)
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBRc HAPc]. pose proof (HND _ _ _ _ HH) as NDc.
    pose proof TOK as TOKc. ddestruct TOKc as (T1 & T2 & T3 & T4 & T5 & T6).
    pose proof (Forall_inv T1) as [MXr SGX]. pose proof (Forall_inv (Forall_inv_tail T1)) as [MYr SGY].
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail T1))) as [MZr SGZ].
    pose proof (Forall_inv T2) as [NSX _]. pose proof (Forall_inv (Forall_inv_tail T2)) as [NSY _].
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail T2))) as [NSZ _].
    clear T1 T2 T3 T4.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    lazymatch type of HH with HEAP _ _ _ ?hc ?LBc _ ?moc => rename hc into h4; set (LB4 := LBc) in *; clearbody LB4; rename moc into mo4 end.
    zstep. zstep.
    pose proof (U_ecp_point_free_spec L HI HFREE HLS SW DIMG HND) as SPF. unfold ecp_point_free_stmt, ecp_point_free_post, U_ECP_POINT_FREE in SPF.
    eapply aevtM_cut.
    { eapply SPF with (lo := lo) (h := h4) (LB := LB4) (A := G + 56) (p := mkPT dX dY dZ);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
        first [ exact HH | exact TP | exact CA | eassumption
              | (* [comment removed for export] *) unfold ecp_point_at; cbn [pt_X pt_Y pt_Z]; rewrite EX, EY, EZ; split; [reflexivity| split; [clear; lia| split; [clear; lia| exact (conj MXr (conj MYr MZr))]]]
              | (* [comment removed for export] *) repeat constructor; assumption
              | (* [comment removed for export] *) unfold mpds_distinct; exact (tmp_ok_blocks_nodup usegs _ _ _ _ _ TOK)
              | (* [comment removed for export] *) rewrite HT; intros a Ha; left; clear -Ha SLO HLS HTOP ACL ACP; unfold ECP_POINT_SIZE in Ha; lia
              | (* [comment removed for export] *) intros a Ha Hd; exfalso; clear -Ha Hd DHI ACL SLO HLS; lia
              | clear -SLO; lia | clear -HTOP HT; lia | clear -SPA SPR; lia
              | reflexivity | f_equal; clear; lia
              | match goal with |- ?g => idtac "PFLEFT" g end ]. }
    clear SPF SF.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI5 & ST5 & MF5 & HT5 & HH5 & PT5 & PX5 & SOK5).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m5; rename mox into mo5 end.
    match type of HT5 with heap_top _ _ _ ?hh = _ => rename hh into h5 end.
    (* [comment removed for export] *)
    unfold pt_ivs in PX5. cbn [pt_mpds pt_X pt_Y pt_Z flat_map] in PX5. rewrite app_nil_r in PX5.
    rewrite (mpd_ivs_fp dX NSX), (mpd_ivs_fp dY NSY), (mpd_ivs_fp dZ NSZ) in PX5.
    change (pt_free_LB {| pt_X := dX; pt_Y := dY; pt_Z := dZ |} LB4) with (lb_free_mpd dZ (lb_free_mpd dY (lb_free_mpd dX LB4))) in HH5, PX5, PT5.
    set (LB5 := lb_free_mpd dZ (lb_free_mpd dY (lb_free_mpd dX LB4))) in *.
    (* [comment removed for export] *)
    pose proof (lb_ext_free LB (tmp_blocks [dY; dZ]) LB4 dX EXT NDc (tmp_ok_head_fresh usegs _ _ _ _ _ _ TOK)) as EXT1.
    pose proof (tmp_ok_tail usegs _ _ _ _ _ _ TOK) as TOKy.
    pose proof (lb_ext_free LB (tmp_blocks [dZ]) _ dY EXT1 (lb_free_mpd_nodup _ _ NDc) (tmp_ok_head_fresh usegs _ _ _ _ _ _ TOKy)) as EXT2.
    pose proof (tmp_ok_tail usegs _ _ _ _ _ _ TOKy) as TOKz.
    pose proof (lb_ext_free LB (tmp_blocks []) _ dZ EXT2 (lb_free_mpd_nodup _ _ (lb_free_mpd_nodup _ _ NDc)) (tmp_ok_head_fresh usegs _ _ _ _ _ _ TOKz)) as EXT3.
    change (tmp_blocks []) with (@nil blk) in EXT3. fold LB5 in EXT3.
    (* [comment removed for export] *)
    assert (ITEMS : forall iv, In iv (mpd_fp dX ++ mpd_fp dY ++ mpd_fp dZ) -> fp_item_ok L LB LB4 (bv_unsigned sp) XS iv).
    { intros iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv]; [| apply in_app_iff in Hiv; destruct Hiv as [Hiv|Hiv]].
      - eapply (fp_items_mpd usegs L m4 LB LB4 _ _ _ dX MXr HBRc EXT); [| rewrite EX; clear -ACL SLO HLS; lia| rewrite EX; clear; lia| exact Hiv].
        intros b Hb. unfold tmp_blocks; cbn [flat_map]. apply in_app_iff. left. exact Hb.
      - eapply (fp_items_mpd usegs L m4 LB LB4 _ _ _ dY MYr HBRc EXT); [| rewrite EY; clear -ACL SLO HLS; lia| rewrite EY; clear; lia| exact Hiv].
        intros b Hb. unfold tmp_blocks; cbn [flat_map]. apply in_app_iff. right. apply in_app_iff. left. exact Hb.
      - eapply (fp_items_mpd usegs L m4 LB LB4 _ _ _ dZ MZr HBRc EXT); [| rewrite EZ; clear -ACL SLO HLS; lia| rewrite EZ; clear; lia| exact Hiv].
        intros b Hb. unfold tmp_blocks; cbn [flat_map]. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. exact Hb. }
    pose proof (heap_presx_trans usegs L _ _ _ _ _ _ PX
                  (presx_caller usegs L LB LB5 LB4 (bv_unsigned sp) (bv_unsigned sp + -512) _ _ m4 m5 PX5
                     (fun b Hb => lb_ext_sub _ _ _ _ EXT3 Hb) ltac:(clear; lia) ltac:(clear -ACL SLO HLS; lia) HBRc HAPc NDc
                     (fun b Hb => lb_ext_sub _ _ _ _ EXT Hb) ITEMS DHI DI1 DI2)) as PXn.
    (* [comment removed for export] *)
    assert (DJS : forall a k, hl_data_lo L <= a -> a + k <= hl_data_hi L -> disjoint_from (mpd_fp dX ++ mpd_fp dY ++ mpd_fp dZ) a k).
    { intros a k H1 H2.
      apply PkTmp.disjoint_from_app; [| apply PkTmp.disjoint_from_app];
        (eapply (fp_disjoint_data usegs L); [eassumption| exact HBRc| exact H1| exact H2| exact DHI| | exact DI1| exact DI2]);
        [rewrite EX| rewrite EY| rewrite EZ]; clear -ACL SLO HLS; lia. }
    pose proof (ecp_ids_state_presx usegs L _ _ _ _ _ _ _ IDS PX5 IDL
                  ltac:(apply DJS; generalize IL1 IL2 IL3; clear; intros; lia) ltac:(apply DJS; generalize IL1 IL2 IL3; clear; intros; lia)) as IDSn.
    (* [comment removed for export] *)
    assert (DJC : forall a k, alloc_ceiling <= a -> (a + k <= G + 56 \/ G + 104 <= a) -> disjoint_from (mpd_fp dX ++ mpd_fp dY ++ mpd_fp dZ) a k).
    { intros a k H1 H2.
      apply PkTmp.disjoint_from_app; [| apply PkTmp.disjoint_from_app];
        (eapply fp_disjoint_struct; [eassumption| exact HBRc| exact H1|]); [rewrite EX| rewrite EY| rewrite EZ]; clear -H2; lia. }
    repeat match goal with
    | Hc : rw_cells usegs m4 ?a ?cs |- _ =>
        first [ apply (heap_presx_rw_cells usegs L _ _ _ m4 m5 a cs PX5) in Hc;
                [ | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; intros a' Ha'; left; clear -Ha'; lia
                  | apply DJC; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; clear -ACL SLO HLS; lia ]
              | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
    end.
    (* [comment removed for export] *)
    ddestruct PT5 as (_ & _ & _ & QX & QY & QZ). cbn [pt_X pt_Y pt_Z pt_init] in QX, QY, QZ.
    pose proof (proj1 QX) as CX. pose proof (proj1 QY) as CY. pose proof (proj1 QZ) as CZ. cbn [md_addr mpd_init md_sg md_n md_p md_pad] in CX, CY, CZ.
    clear QX QY QZ HH MI ST SOK PX IDS HBRc HAPc MK.
    pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5.
    replace (G + 56 + 16) with (bv_unsigned sp + -432) in CY by (clear; lia). replace (G + 56 + 32) with (bv_unsigned sp + -416) in CZ by (clear; lia).
    replace (G + 8) with (bv_unsigned sp + -496) in CH0 by (clear; lia). replace (G + 24) with (bv_unsigned sp + -480) in CH1 by (clear; lia).
    replace (G + 40) with (bv_unsigned sp + -464) in CH2 by (clear; lia). replace (G + 56) with (bv_unsigned sp + -448) in CX by (clear; lia).
    replace (G + 104) with (bv_unsigned sp + -400) in CH by (clear; lia). replace (G + 120) with (bv_unsigned sp + -384) in FRT by (clear; lia).
    assert (CTX5 : CTX h5 LB5 [] m5 mo5).
    { split; [exact HH5|]. split; [rewrite HT5; exact HT|]. split; [eapply mo_frame_trans; [exact MF| exact MF5]|].
      split; [exact MI5|]. split; [exact SOK5|]. split; [exact EXT3| exact IDSn]. }
    (* [comment removed for export] *)
    zstep. zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      assert (NZ : r2 <> 0) by (intros ->; apply KR; reflexivity).
      assert (STX : stk usegs m5 lo (bv_unsigned sp + -104)).
      { generalize FR0 FRH CH0 CH1 CH2 CX CY CZ CH FRT FRM FRR ST5 SLO ACL ACP HLS SPR. clear. intros. unfold mpi_cells in *.
        release_frame FR0 ST5 (bv_unsigned sp + -504). release_frame FRH ST5 (bv_unsigned sp + -496).
        release_frame CH0 ST5 (bv_unsigned sp + -480). release_frame CH1 ST5 (bv_unsigned sp + -464). release_frame CH2 ST5 (bv_unsigned sp + -448).
        release_frame CX ST5 (bv_unsigned sp + -432). release_frame CY ST5 (bv_unsigned sp + -416). release_frame CZ ST5 (bv_unsigned sp + -400).
        release_frame CH ST5 (bv_unsigned sp + -384). release_frame FRT ST5 (bv_unsigned sp + -312).
        release_frame FRM ST5 (bv_unsigned sp + -296).
        release_frame FRR ST5 (bv_unsigned sp + -104). exact ST5. }
      clear FR0 FRH CH0 CH1 CH2 CX CY CZ CH FRT FRM FRR ST5.
      eapply exit_walk with (PKA := PKA) (info := info) (C := C) (lo := lo) (PAR := PAR) (bs := bs)
                            (r := r2) (g' := kp_grp K) (NB := []);
        try eassumption; try reflexivity.
      + (* [comment removed for export] *) eapply kp_init_presx; [exact DIMG| exact KP0| exact PXn| exact MI0| exact MI5| exact INC|].
        cbn. generalize IL1 IL2 IL3 CIM DI1 DI2. clear. intros. repeat split; lia.
      + (* [comment removed for export] *)
        intros d1 d2 H1 H2 NE O1 O2. exfalso. revert H1 O1. unfold grp_mpds, kp_init, kp_grp, grp_init.
        cbn [g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In]. unfold mpd_init.
        intros H1 O1; decompose [or] H1; subst; cbn in O1; try discriminate; contradiction.
      + right. split; [exact NZ| split; reflexivity].
      + apply ctx_pka. exact PXn.
      + eapply heap_presx_weak; [exact PXn| intros b Hb; exact Hb| clear; lia| intros a Ha; exact (proj2 Ha)].
    - (* [comment removed for export] *)
      assert (Z0 : r2 = 0).
      { clear -KR RR. apply Z.mod_divide in KR; [| lia]. destruct KR as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
      ddestruct (IDW Z0) as (id & -> & IDB).
      assert (STX : stk usegs m5 lo (bv_unsigned sp + -104)).
      { generalize FR0 FRH CH0 CH1 CH2 CX CY CZ CH FRT FRM FRR ST5 SLO ACL ACP HLS SPR. clear. intros. unfold mpi_cells in *.
        release_frame FR0 ST5 (bv_unsigned sp + -504). release_frame FRH ST5 (bv_unsigned sp + -496).
        release_frame CH0 ST5 (bv_unsigned sp + -480). release_frame CH1 ST5 (bv_unsigned sp + -464). release_frame CH2 ST5 (bv_unsigned sp + -448).
        release_frame CX ST5 (bv_unsigned sp + -432). release_frame CY ST5 (bv_unsigned sp + -416). release_frame CZ ST5 (bv_unsigned sp + -400).
        release_frame CH ST5 (bv_unsigned sp + -384). release_frame FRT ST5 (bv_unsigned sp + -312).
        release_frame FRM ST5 (bv_unsigned sp + -296).
        release_frame FRR ST5 (bv_unsigned sp + -104). exact ST5. }
      clear FR0 FRH CH0 CH1 CH2 CX CY CZ CH FRT FRM FRR ST5.
      eapply setgrp_walk with (PKA := PKA) (info := info) (C := C) (lo := lo) (PAR := PAR) (bs := bs) (id := id);
        try eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End EP.
