(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB Arr MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_ecp_grp_id_list U_ecp_point_free U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type U_pk_ecc_set_group U_ecp_sinv U_string U_oid U_oidv U_oid_ec_grp U_oid_ec_grp_v U_ecp_group_init U_mpi_cmp U_mpi_bitlen U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_C U_pk_ecparams_D U_pk_ecparams_E U_pk_ecparams_F U_pk_ecparams_G U_asn1_get_tag U_asn1_get_int U_asn1_get_mpi U_mpi_read_binary U_mpi_read_binary_proof U_mpi_lset.
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
Ltac2 gd_tbl_P_pk_ecparams_H () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "prb_none_ret"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "U_ECP_POINT_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_B.ctx_now"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.lb_ext"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.fp_off"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_upd"; "EP.SPINV"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.pk_use_ecparams_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.MOK"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"].



(* [comment removed for export] *)
Definition U_ECP_POINT_READ_BINARY : Z := 0x38764.
Definition prb_none_ret (len : Z) : Z := if len =? 0 then -0x4F80 else -0x4E80.

Local Ltac2 Set LiaOrc.tbl := fun () => "0100?D11805467289.62D11805467289.63D15457446739.62D15457446739.63D19887709521.84D43070029892.84D43928033258.63D44484923210.84D49705053714.62D49705053714.63D62900777713.85L11801586693.80L11805597853.63L11807744665.65L12283411672.62L12283411672.63L12283411672.82L12860309875.81L13301871092.62L14106684376.61L14106684376.63L14106684376.82L17646078182.61L30431290393.81L30985072156.65L34994544387.62L36425798428.63L36425799944.82L39026998878.65L39843426615.65L39887139444.62L41288976216.62L41288976216.63L41288976216.82L43057599553.59L43070029892.84L44484923210.84L44866992728.62L44866992728.63L44866992728.82L45898055924.62L48429268312.62L48429268312.63L48429268312.82L49345641752.62L49358208408.81L5145216728.62 L5145216728.63 L5145216728.82 L51925114228.62L52303750330.62L53136558823.54L57933933556.62L61845709206.80L63962036340.61L67158371251.62L67158371251.63L67158371251.82L7274816372.62 L8617004262.65 L8722184664.62 L8722184664.63 L8722184664.82 R30985072156.6500000:00D00N00X00_00`00j00k01901G01_01l02902P02W02^02e02n03503<03C03J03Q03c04904@04N04\05605D05K05R05Y05`05n05o06006706>06E06L06S06Z06a06h06o07607=07D07K07]07k08208908@08G08N08U08\08l09309:09A09WS2ra2sp2HBS2ra2sp2HBS2ra2sp2HBS2ra2sp2HBS2ra2spFS2ra2sp2HBFS2ra2sp3SPR2HBS2ra2sp3SPR2HBS2ra2sp4lenw2LB2KL3x141HS2ra2sp1G3SPGS2ra2sp1G3SPGS2ra2sp2dP2lo3SLO3SPR1HS2ra2spS2ra2spS2ra2spS2ra2sp1GS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2sp4lenw2LB2KLS2ra2sp2lo3SLO3LO43SPRS2ra2spS2ra2sp2lo3SLOS2ra2sp2lo3SLOS2ra2sp2lo3SLO3LO43SPA3SPRS2ra2sp2lo3SLOS2ra2spS2ra2spS2ra2spS2ra2spS2ra2sp2lo3SLOFFS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2sp4lenw2LB2KLS2ra2sp2lo3LO4S2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2sp1G2lo3SPGS2ra2spS2ra2spS2ra2spS2ra2sp2lo3SLO3LO43SPR". (* [comment removed for export] *)
Lemma U_prb_none : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PLBx,(3.$4.)PdP,$5.PdX,$5.PG,$6.Plo,$6.Plenw,(0.&40.)P,(7.$8.R7.R6.R5.)P,(9.$6.(:.R6.)(;.R4.+8.))P,P,(9.$<.(=.R7.)$>.)(?.(10.=(11.R8.))(12.(;.(11.R8.)(13.+4.(14.R8.)))R5.))P,(15.(9.$<.(=.R8.)$16.))P,(7.$8.R;.R:.R8.)P,(9.$6.(:.R9.)(;.R8.+38.))P,(9.$<.(=.R:.)$17.)P,(18.$8.R>.R9.(19.&40.R2<.))P,(12.R:.(1:.(19.&40.R2=.)+50.))P,(12.+1000.R;.)P,(9.$6.(1;.(19.&40.R2?.)+10.)=)P,(12.(19.&40.R30.)R>.)P,(12.(;.R?.+<0.)(1<.+2.+40.))P,(1=.$8.R14.)P,(9.$6.(1;.(19.&40.R34.)+2.)=)(1>.$8.Lms',$1?.(20.(0.&40.)Lx5,(0.&40.)(20.(0.&40.)Lx6,(0.&40.)(20.(0.&40.)Lx7,(0.&40.)(20.(0.&40.)Lx11,(0.&40.)(20.(0.&40.)Lx12,(0.&40.)(20.(0.&40.)Lx13,(0.&40.)(20.(0.&40.)Lx14,(0.&40.)(20.(0.&40.)Lx15,(0.&40.)(20.(0.&40.)Lx16,(0.&40.)(20.(0.&40.)Lx17,(0.&40.)(20.(0.&40.)Lx28,(0.&40.)(20.(0.&40.)Lx29,(0.&40.)(20.(0.&40.)Lx30,(0.&40.)(20.(0.&40.)Lx31,(0.&40.)(20.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(?.(9.$1?.R10.(21.(22.R45.R44.R43.R42.R?.R>.R=.R3>.R3=.(23.&40.(24.(19.&40.R20.)))R<.R;.R:.R9.R8.R7.R6.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R5.R4.R3.R2.)R28.(25.R45.)R27.(26.(0.&40.))R1.(27.$8.)))(?.(28.(29.(2:.$6.$6.)(2;.$6.$6.(1:.(19.&40.R44.)+50.)(19.&40.R44.))(2<.(2:.$6.$6.)))R26.R1.)(?.(2=.$8.R26.R1.)(?.(1=.$8.R1.)(18.$8.R1.R21.(19.&40.R44.)))))))))))))))))))))(21.(22.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.(23.&40.R12.)R2<.R2;.R10.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(23.&40.$2>.)R17.(26.(0.&40.))R16.(27.$8.)))")
(* [comment removed for export] *).
Proof.
  intros until lenw. intros MP EP HPP NSP MX EX OX ST SLO LO4 SPA SPG GB MI RA. unfold U_ECP_POINT_READ_BINARY.
  pose proof (bv_unsigned_in_range 64 lenw) as LB. change (bv_modulus 64) with (2^64) in LB.
  assert (LIMB : md_p dP + 4 * md_n dP <= lo \/ bv_unsigned sp + -64 <= md_p dP).
  { destruct MP as [(_ & _ & _ & _ & _ & OWN) _]. destruct (md_own dP) eqn:OP; [destruct OWN as [-> ->]; left; lia| left; exact (proj2 (HPP eq_refl))| exfalso; exact (NSP eq_refl)]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (conj MI I) as MIbox.
  carve_frame 64%nat ST.
  do 9 zstep.
  zstep. if_cases KL; zify_cond KL.
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in KL by lia.
    zstep. zstep.
    do 9 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    eapply evt_done. deexists 15. split; [| split; [exact MU| split; [exact WM| split; [assumption| exact ST]]]].
    unfold prb_none_ret. replace (bv_unsigned lenw =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - rewrite ?unsigned_lit in KL by lia.
    pose proof MP as [[_ [ALG _]] _]. rewrite EP in ALG.
    zstep. zstep. if_cases KG; zify_cond KG; [exfalso; rewrite ?unsigned_lit in KG by lia; lia|].
    zstep. zstep. if_cases KG2; zify_cond KG2; [exfalso; rewrite ?unsigned_lit in KG2 by lia; change 7 with (Z.ones 3) in KG2; rewrite Z.land_ones in KG2 by lia; change (2 ^ 3) with 8 in KG2; lia|].
    do 4 zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with M : mem_inv usegs m1 |- _ => rename M into MI1 end.
    assert (MP1 : mpd_at usegs m1 LBx dP).
    { split; [| exact (proj2 MP)]. eapply mpdr_at_munch; [exact (proj1 MP)| exact MU| exact WM| exact (proj1 MIbox)| exact MI1| rewrite EP; cbn; lia|].
      intros O. pose proof (proj2 (HPP O)). cbn. lia. }
    pose proof U_mpi_size_spec as SZ. unfold mpi_size_stmt, mpi_size_post, U_MPI_SIZE in SZ.
    callx_sp (bv_unsigned sp + -64) (eapply SZ with (dX := dP) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
       first [ exact MP1 | exact MI1 | exact ST | exact LIMB | rewrite EP; f_equal; lia | rewrite EP; right; lia
             | intros O; exact (proj1 (HPP O)) | lia
             | match goal with |- ?g => idtac "SZLEFT" g end ]).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with M : mem_inv usegs m2 |- _ => rename M into MI2 end.
    match goal with U : munch _ m m2 |- _ => rename U into MU2 end. match goal with W : wmono usegs m m2 |- _ => rename W into WM2 end.
    assert (CX : rw_cells usegs m2 (G + 56) (mpi_cells (md_p dX) (Z_to_bv 64 (md_sg dX)) (md_n dX) (md_pad dX))).
    { pose proof (mpdr_at_munch usegs m m2 LBx dX _ (proj1 MX) MU2 WM2 (proj1 MIbox) MI2 ltac:(rewrite EX; cbn; lia) ltac:(intros O; rewrite OX in O; discriminate)) as [R _].
      rewrite EX in R. exact R. }
    destruct MX as [(_ & _ & _ & _ & _ & OWNX) _]. rewrite OX in OWNX. destruct OWNX as [PX0 _]. rewrite PX0 in CX. unfold mpi_cells in CX.
    zstep. zstep. if_cases KX; zify_cond KX. 2:{ exfalso. apply KX. reflexivity. }
    zstep. zstep. zstep.
    do 9 zstep. match goal with S : stk usegs _ lo _ |- _ => release_frame FR S (bv_unsigned sp); rename S into STf end. zstep.
    eapply evt_done. deexists 15. split; [| split; [exact MU2| split; [exact WM2| split; [assumption| exact STf]]]].
    unfold prb_none_ret. replace (bv_unsigned lenw =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
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
  #[using="HI m0 mo0 h0 LB HH0 INC INB ACP"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "(?.(10.+1000.(2?.VL,))(?.(10.=VC,)(?.(9.$6.(1;.VC,+10.)=)(?.(12.(;.VC,+100.)(2?.VL,))(?.(30.(12.(;.VC,+100.)(31.VL,))(12.(32.VL,)VC,))(?.(12.(;.VBUF,(33.(34.(0.&8.)Vbs,)))(2?.VL,))(30.(12.(;.VBUF,(33.(34.(0.&8.)Vbs,)))(31.VL,))(12.(32.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0' & C16' & _ & CAC' & CIM'). cbn in C0', C16', CAC', CIM'.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC' & BIM'). cbn in BAC', BIM'. auto 10.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2647750340.6  L2726914452.6  L52616404933.1000000D00X016S1L3PKA3PKD2I12I22I3S1L3PKA3PKD2I12I22I3S1L2HI2sp2h03PKA2lo3DSP1a2Ha1Q". (* [comment removed for export] *)
  #[using="HI h0 lo HPKA0 DSP CWP PKD IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Pm,P,(0.&40.)(2.(0.&8.))P,(35.$8.VL,VLB,(19.&40.Vsp,)(29.(2:.$6.$6.)(2;.$6.$6.$36.(;.$36.+1.))(29.(2:.$6.$6.)(2;.$6.$6.$37.(;.$37.+38.))(2<.(2:.$6.$6.))))Vm0,R1.)(38.$8.R2.VPKA,(29.$39.(3:.(23.&40.Vinfo,))(29.$39.(3:.(23.&40.VC,))(2<.$39.))))")
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
  #[using="IDL"] Lemma IL4 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Pa,$6.P,(30.(?.(12.$36.R1.)(10.R1.(;.$36.+1.)))(?.(12.$37.R1.)(10.R1.(;.$37.+38.))))(?.(3;.VL,R2.)(15.(3<.VL,R2.)))")
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

  (* [comment removed for export] *)
  Definition SPINV (h : HST usegs L HI) (LBi : list blk) (m : mem) (mo : Model)
      (dN dP dA dB dX dY dZ : mpd) (p : Z) (lnw vw pb nb : word) (scj hj tj pj rj : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "(?.(3=.VL,VHI,Vmo0,Vh0,VLB,O15.O14.(3>.(29.$5.O11.(29.$5.O10.(29.$5.O?.(29.$5.O>.(29.$5.O=.(29.$5.O<.(29.$5.O;.(2<.$5.)))))))))O13.O12.)(?.(35.$8.VL,VLB,(19.&40.Vsp,)(29.(2:.$6.$6.)(2;.$6.$6.$36.(;.$36.+1.))(29.(2:.$6.$6.)(2;.$6.$6.$37.(;.$37.+38.))(2<.(2:.$6.$6.))))Vm0,O13.)(?.(3?.$8.O13.O14.(;.(19.&40.Vsp,)-1?8.)+<0.(29.$5.O11.(29.$5.O10.(29.$5.O?.(29.$5.O>.(29.$5.O=.(29.$5.O<.(29.$5.O;.(2<.$5.)))))))))(?.(9.$6.(:.O11.)(;.(;.(19.&40.Vsp,)-1?8.)+68.))(?.(9.$6.(:.O10.)(;.(;.(19.&40.Vsp,)-1?8.)+8.))(?.(9.$6.(:.O?.)(;.(;.(19.&40.Vsp,)-1?8.)+18.))(?.(9.$6.(:.O>.)(;.(;.(19.&40.Vsp,)-1?8.)+28.))(?.(9.$6.(:.O=.)(;.(;.(19.&40.Vsp,)-1?8.)+38.))(?.(9.$6.(:.O<.)(;.(;.(19.&40.Vsp,)-1?8.)+48.))(?.(9.$6.(:.O;.)(;.(;.(19.&40.Vsp,)-1?8.)+58.))(?.(38.$8.O13.(;.(19.&40.Vsp,)-128.)(29.$39.(3:.(23.&40.O:.))(2<.$39.)))(?.(?.(12.VP,O:.)(12.O:.(;.VP,VLEN,)))(?.(38.$8.O13.(;.(19.&40.Vsp,)-120.)(29.$39.(40.#;8.O1.)(2<.$39.)))(?.(38.$8.O13.(;.(19.&40.Vsp,)-130.)(29.$39.(3:.O9.)(2<.$39.)))(?.(38.$8.O13.(;.(19.&40.Vsp,)-138.)(29.$39.(40.#4.O2.)(29.$39.(41.O8.)(2<.$39.))))(?.(38.$8.O13.(;.(19.&40.Vsp,)-200.)(29.$39.(40.#8.O5.)(2<.$39.)))(?.(38.$8.O13.(;.(19.&40.Vsp,)-1?8.)(29.$39.(40.#8.O4.)(2<.$39.)))(?.(38.$8.O13.(;.(;.(19.&40.Vsp,)-1?8.)+78.)(29.$39.(3:.O7.)(29.$39.(3:.O6.)(29.$39.(40.#38.O3.)(2<.$39.)))))(?.(38.$8.O13.(;.(19.&40.Vsp,)-68.)(29.$39.(3:.Vs11,)(29.$39.(3:.Vs10,)(29.$39.(3:.Vs9,)(29.$39.(3:.Vs8,)(29.$39.(3:.Vs7,)(29.$39.(3:.Vs6,)(29.$39.(3:.Vs5,)(29.$39.(3:.Vs4,)(29.$39.(3:.Vs3,)(29.$39.(3:.Vs2,)(29.$39.(3:.Vs1,)(29.$39.(3:.Vs0,)(29.$39.(3:.Vra,)(2<.$39.)))))))))))))))(18.$8.O13.Vlo,(;.(19.&40.Vsp,)-200.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L48308921574.9L60663718710.900000L00hS1L3BUF2bs1H2H02H13BIM2H22H3S1L3BUF2bs1H2H02H13BIM2H22H3". (* [comment removed for export] *)
  #[using="DIMG HBS0 INB IDL BIM"] Lemma ctx_bytes : forall m, heap_presx usegs L LB (bv_unsigned sp) XS m0 m -> bytes_at usegs m BUF bs.
  Proof.
    intros m PX. eapply heap_presx_bytes_at; [exact PX| exact HBS0| |].
    - intros a Ha. right; right. exists (BUF, Z.of_nat (length bs)). split; [exact INB| cbn; exact Ha].
    - cbn. generalize IL1 IL2 IL3 BIM DI1 DI2. clear. intros. repeat split; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L12185527390.125L30669250827.126L37304276603.126L51794627208.12500001<01V02202KS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3DSP3DPC3NZR3DSR2RC3SLO3ACL3ACP3CAC2C01d2NdS2ra2sp3PKA1C3PAR2bs1d1B1QS2ra2sp3PKA1C3PAR2bs1d1B1k1QS2ra2sp3PKA1C3PAR2bs1k2Hk". (* [comment removed for export] *)
  #[using="HLS ra PKA C lo PAR bs NZP DSP DPC NZR DSR RC SLO ACL ACP CAC C0"] Lemma tmp_apart_LB : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Ph,(42.$8.VL,VHI,)PLBi,(3.$4.)PT,(3.$4.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$43.Pds,(3.$5.)Pd,$5.PB,$6.Pk,$6.P,(44.$8.VL,VHI,R9.R8.R6.R5.)P,(45.VLB,R8.R9.)P,(3?.$8.R8.R:.(;.(19.&40.Vsp,)-1?8.)+<0.R6.)P,Pb,$4.P,(46.$4.R1.(3>.R8.))(46.$4.R2.R<.)P,(46.$5.R7.R8.)P,(9.$<.(=.R8.)$>.)P,(46.(2:.$6.$6.)(2;.$6.$6.R8.R7.)VLB,)P,(10.=R8.)(30.(12.(;.R:.R9.)(11.R;.))(12.(;.(11.R;.)(13.+4.(14.R;.)))R:.))")
(* [comment removed for export] *).
  Proof.
    intros h LBi T m mo ds d B k HH EXT TOK SUBT Hd Od HB Hk.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    pose proof (tmp_ok_in usegs _ _ _ _ _ _ TOK Hd) as [MD _]. destruct (mpdr_blk_facts usegs L _ _ _ MD Od HBR) as (Id & Nd & _).
    assert (NE : (B, k) <> (md_p d, 4 * md_n d)).
    { intros E. apply (proj2 EXT (md_p d, 4 * md_n d)); [| rewrite <- E; exact HB]. apply SUBT. apply in_tmp_blocks. exists d. split; [exact Hd|]. rewrite (mpd_blk_heap _ Od). left; reflexivity. }
    destruct (blocks_apart_neq LBi _ _ HAP (lb_ext_sub _ _ _ _ EXT HB) Id NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; [left| right]; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L31934148554.10L32778717676.16L59310682826.1300000N01201ZS1L2sp2lo3ACL1d2SP2S12S22B12P4S1L2HI2sp2h04HTOP1d2SP2S22B12B21a2HaS1L2sp2lo3ACL3DHI1d2SP2S12S22B11a2Ha3Hd'". (* [comment removed for export] *)
  #[using="ACL HTOP DHI"] Lemma tmp_writable : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Ph,(42.$8.VL,VHI,)PLBi,(3.$4.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$43.Pds,(3.$5.)Pd,$5.PSP,$6.P,(44.$8.VL,VHI,R7.R6.R5.R4.)P,(3?.$8.R6.R7.(;.(19.&40.Vsp,)-1?8.)+<0.R4.)P,(46.$5.R4.R5.)P,(12.Vlo,R4.)P,(12.R5.(;.(19.&40.Vsp,)-1?8.))(47.VL,R;.R6.(48.$8.VL,VHI,Vh0,)R7.)")
(* [comment removed for export] *).
  Proof.
    intros h LBi m mo ds d SP HH TOK Hd S1 S2. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    pose proof (tmp_ok_in usegs _ _ _ _ _ _ TOK Hd) as [MD _]. pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 TOK)) _ Hd) as (_ & B1 & B2).
    split; [| split].
    - intros a Ha. left. clear -Ha B1 B2 S1 S2 SLO HLS HTOP. lia.
    - intros a Ha Hd'. exfalso. clear -Ha Hd' B1 S2 S1 DHI ACL. lia.
    - intros O. destruct (mpdr_blk_facts usegs L _ _ _ MD O HBR) as (_ & _ & _ & P4 & _). right. clear -P4 B1 S1 S2 ACL. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0>L15439079543.8L24748498429.4L28467717136.4L28469746088.5L30392002547.6L46132990536.1L49664744988.1L4991549528.7 L59261403064.5L59263549952.400000J00R00X00b01701;01?01H01U01^S1L3HLS2sp2lo3SLO3ACL1d2B1S1L1H2H0S1L2H1S1L2H13DHIS1L3HLS2sp2lo3SLO3ACLS2spS2spS2sp1d2B2S1L2H02H13DHIS1L2H02H1". (* [comment removed for export] *)
  #[using="HLS DIMG HND lo SLO ACL DHI IDL"] Lemma spinv_update : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Ph,(42.$8.VL,VHI,)PLBi,(3.$4.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$43.Ph2,(42.$8.VL,VHI,)PLB2,(3.$4.)Pm2,P,(0.&40.)(2.(0.&8.))Pmo2,$43.Pds,(3.$5.)Pd,$5.Pd',$5.PW,(3.(2:.$6.$6.))P,(3=.VL,VHI,Vmo0,Vh0,VLB,R<.R;.(3>.R4.)R:.R9.)P,(35.$8.VL,VLB,(19.&40.Vsp,)(29.(2:.$6.$6.)(2;.$6.$6.$36.(;.$36.+1.))(29.(2:.$6.$6.)(2;.$6.$6.$37.(;.$37.+38.))(2<.(2:.$6.$6.))))Vm0,R;.)P,(3?.$8.R<.R=.(;.(19.&40.Vsp,)-1?8.)+<0.R6.)P,(46.$5.R6.R7.)P,(44.$8.VL,VHI,R<.R;.R:.R9.)P,(9.$6.(48.$8.VL,VHI,R=.)(48.$8.VL,VHI,R11.))P,(49.R?.R;.)P,(1=.$8.R=.)P,(4:.$8.VL,R>.)P,(7.$8.R?.R10.R;.)P,(4;.R15.R=.R11.R<.)P,Pb,$4.P,(46.$4.R1.(4<.R>.))(30.(46.$4.R2.(4<.R10.))(15.(46.$4.R2.R18.)))P,(35.$8.VL,R17.(;.(19.&40.Vsp,)-200.)(4=.(2:.$6.$6.)R=.(4>.R?.))R16.R12.)P,(4?.VL,(;.(19.&40.Vsp,)-1?8.)+<0.R>.)P,(50.(2:.$6.$6.)Liv,(2:.$6.$6.)(12.(51.$6.$6.R1.)(19.&40.Vsp,))R?.)(?.(3=.VL,VHI,Vmo0,Vh0,VLB,R17.R16.(3>.(52.R11.R13.))R15.R14.)(?.(35.$8.VL,VLB,(19.&40.Vsp,)(29.(2:.$6.$6.)(2;.$6.$6.$36.(;.$36.+1.))(29.(2:.$6.$6.)(2;.$6.$6.$37.(;.$37.+38.))(2<.(2:.$6.$6.))))Vm0,R15.)(3?.$8.R15.R16.(;.(19.&40.Vsp,)-1?8.)+<0.(52.R11.R13.))))")
(* [comment removed for export] *).
  Proof.
    (intros h LBi m mo h2 LB2 m2 mo2 ds d d' W dd_H; ddestruct dd_H as (HH & HT & MF & MI & SOK & EXT & IDS); intros PX TOK Hd HH2 HT2 MF2 MI2 SOK2 MD2 OUT NEW PX2 HW HW2).
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof (HND _ _ _ _ HH2) as ND2. pose proof (HND _ _ _ _ HH) as ND.
    pose proof (tmp_ok_in usegs _ _ _ _ _ _ TOK Hd) as [MDr _]. pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 TOK)) _ Hd) as (DNS & B1 & B2).
    ddestruct (tmp_update usegs L HI h2 m m2 mo2 LB [] LBi LB2 G 192 ds d d' (bv_unsigned sp + -512) W HH2 ND2 HBR HAP TOK
                ltac:(rewrite app_nil_r; exact EXT) ltac:(intros b [])
                Hd MD2 OUT NEW PX2 HW ltac:(clear; lia) ltac:(clear -ACL SLO HLS; lia) MI MI2) as (TOK2 & EXT2 & _).
    rewrite app_nil_r in EXT2. rewrite (mpd_ivs_fp d DNS) in PX2.
    split; [| split; [| exact TOK2]].
    - split; [exact HH2|]. split; [rewrite HT2; exact HT|]. split; [eapply mo_frame_trans; [exact MF| exact MF2]|]. split; [exact MI2|]. split; [exact SOK2|]. split; [exact EXT2|].
      eapply ecp_ids_state_presx; [exact IDS| exact PX2| exact IDL| |];
        (apply PkTmp.disjoint_from_app; [eapply disjoint_from_low; [exact HW|]; generalize IL1 IL2 IL3 DHI; clear; intros; lia
                                       | eapply (fp_disjoint_data usegs L); [exact MDr| exact HBR| | | exact DHI| clear -B1 ACL SLO HLS; lia| exact DI1| exact DI2];
                                         generalize IL1 IL2 IL3; clear; intros; lia]).
    - eapply heap_presx_trans; [exact PX|].
      eapply (presx_caller usegs L LB LBi LBi); [exact PX2| intros b Hb; eapply lb_ext_sub; [exact EXT| exact Hb]| clear; lia| clear -ACL SLO HLS; lia
        | exact HBR| exact HAP| exact ND| intros b Hb; eapply lb_ext_sub; [exact EXT| exact Hb]| | exact DHI| exact DI1| exact DI2].
      intros iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
      + left. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Q1 Q2]. pose proof (proj1 (Forall_forall _ _) HW2 _ Hiv) as Q3. split; [exact Q2| exact Q3].
      + eapply (fp_items_mpd usegs L m LB LBi); [exact MDr| exact HBR| exact EXT| | clear -B1 ACL SLO HLS; lia| clear -B2 SLO HLS; lia| exact Hiv].
        intros b Hb. apply in_tmp_blocks. exists d. auto.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00h0>L10592998386.1L12194878962.1L13755730418.1L14150428402.1L15706954482.1L16917811186.1L17312636146.1L1917942258.1 L19264384498.1L20475237106.1L22426592242.1L2312640242.1 L23637444850.1L24032142834.1L25983497970.1L27194350578.1L28751405042.1L28801550466.1L30356951538.1L30751780594.1L32410609794.1L33913857266.1L35470907634.1L35861542386.1L36607334018.1L37434845682.1L40199091842.1L40597057522.1L40991751410.1L42190021106.1L42581049074.1L44154483442.1L45352626162.1L47711258098.1L48909527794.1L5080154098.1 L52072259826.1L52201067138.1L54036197874.1L5475372274.1 L55624971250.1L57198278642.1L57593496818.1L59150153970.1L60755704562.1L62711254002.1L63917912306.1L64312610290.1L64968177794.1L65873854962.1L66268684018.1L67475211250.1L68564129922.1L7036092658.1 L711283954.1  L8637448946.1 00000400800900=00A00E00I00J00N00R00V00Z00^00b00f00j00n01201301701;01?01C01G01K01L01P01T01X01Y01]01a01e01i01m02102502902:02>02B02F02J02N02R02V02Z02^02b02c02g02k02o03303703;S2spS2spFS2spS2spS2spS2spFS2spS2spS2spS2spS2spS2spS2spS2spS2spS2spFS2spS2spS2spS2spS2spS2spFS2spS2spS2spFS2spS2spS2spS2spS2spS2spS2spS2spFS2spS2spS2spS2spS2spS2spS2spS2spS2spS2spFS2spS2spS2spS2spS2spS2sp". (* [comment removed for export] *)
  #[using="Type"] Lemma tmp_upd7 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Pd',$5.PdN,$5.PdP,$5.PdA,$5.PdB,$5.PdX,$5.PdY,$5.PdZ,$5.P,(9.$6.(:.R7.)(;.(;.(19.&40.Vsp,)-1?8.)+68.))P,(9.$6.(:.R7.)(;.(;.(19.&40.Vsp,)-1?8.)+8.))P,(9.$6.(:.R7.)(;.(;.(19.&40.Vsp,)-1?8.)+18.))P,(9.$6.(:.R7.)(;.(;.(19.&40.Vsp,)-1?8.)+28.))P,(9.$6.(:.R7.)(;.(;.(19.&40.Vsp,)-1?8.)+38.))P,(9.$6.(:.R7.)(;.(;.(19.&40.Vsp,)-1?8.)+48.))P,(9.$6.(:.R7.)(;.(;.(19.&40.Vsp,)-1?8.)+58.))(?.P,(9.$6.(:.R?.)(;.(;.(19.&40.Vsp,)-1?8.)+68.))(9.(3.$5.)(52.R10.(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(29.$5.R10.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(?.P,(9.$6.(:.R?.)(;.(;.(19.&40.Vsp,)-1?8.)+8.))(9.(3.$5.)(52.R10.(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(29.$5.R?.(29.$5.R10.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(?.P,(9.$6.(:.R?.)(;.(;.(19.&40.Vsp,)-1?8.)+18.))(9.(3.$5.)(52.R10.(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(29.$5.R?.(29.$5.R>.(29.$5.R10.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(?.P,(9.$6.(:.R?.)(;.(;.(19.&40.Vsp,)-1?8.)+28.))(9.(3.$5.)(52.R10.(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R10.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(?.P,(9.$6.(:.R?.)(;.(;.(19.&40.Vsp,)-1?8.)+38.))(9.(3.$5.)(52.R10.(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R10.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(?.P,(9.$6.(:.R?.)(;.(;.(19.&40.Vsp,)-1?8.)+48.))(9.(3.$5.)(52.R10.(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R10.(29.$5.R9.(2<.$5.)))))))))P,(9.$6.(:.R?.)(;.(;.(19.&40.Vsp,)-1?8.)+58.))(9.(3.$5.)(52.R10.(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R9.(2<.$5.)))))))))(29.$5.R?.(29.$5.R>.(29.$5.R=.(29.$5.R<.(29.$5.R;.(29.$5.R:.(29.$5.R10.(2<.$5.)))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros d' dN dP dA dB dX dY dZ EN EP EA EB EX EY EZ. unfold tmp_upd. cbn [map]. rewrite EN, EP, EA, EB, EX, EY, EZ.
    repeat split; intros E; rewrite E;
      repeat match goal with |- context [?u =? ?v] =>
        first [ rewrite (proj2 (Z.eqb_neq u v)) by (clear; lia) | replace (u =? v) with true by (symmetry; apply Z.eqb_eq; clear; lia) ] end; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L49425788764.174L49428161872.172L55163532373.173L58131691093.175L9605508784.174 00001=02J02d03>04KS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3DSP3DPC3NZR3DSR2RC3SLO3ACL3ACP3CAC2C02tj2WFS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3DSP3DPC3NZR3DSR2RC3SLO3ACL3ACP3CAC2C02rj2WFS2ra2sp3PKA1C3PAR2bs2rj2WFS2ra2sp3PKA1C3PAR2bs2pj2WFS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3DSP3DPC3NZR3DSR2RC3SLO3ACL3ACP3CAC2C02pj2WF". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma spec_err : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Ph,(42.$8.VL,VHI,)PLBi,(3.$4.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$43.PdN,$5.PdP,$5.PdA,$5.PdB,$5.PdX,$5.PdY,$5.PdZ,$5.Pp,$6.Plnw,(0.&40.)Pvw,(0.&40.)Ppb,(0.&40.)Pnb,(0.&40.)Pscj,(3.(0.&8.))Phj,(3.(0.&8.))Ptj,(3.(0.&8.))Ppj,(3.(0.&8.))Prj,(3.(0.&8.))Pr2,$6.Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px9,(0.&40.)Px10,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Px25,(0.&40.)Px26,(0.&40.)Px27,(0.&40.)Px28,(0.&40.)Px29,(0.&40.)Px30,(0.&40.)Px31,(0.&40.)P,(53.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(?.(10.(54.(1<.+2.+1?.))R1<.)(12.R1<.=))P,(15.(9.$6.R1=.=))(55.$8.R30.(56.$8.VL,VHI,$57.$58.$59.$36.$37.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(5:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(21.(22.R1=.(23.&40.(;.(19.&40.Vsp,)-200.))Vgp,Vtp,R1<.R1;.R1:.(23.&40.VPKA,)R19.R18.R17.R16.R15.R14.R13.R12.R11.(23.&40.R1>.)R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)VF,(23.&40.+29;:4.)Vfc,(26.(0.&40.))R31.(27.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. (intros dd_H; ddestruct dd_H as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & FRP & PB & FRR & FRL & FRM & FR0 & FRH & FRT & FR & ST); intros RR NZ).
    assert (FRR' : rw_cells usegs m REF [CB 192 (le8 (Z_to_bv 64 p) ++ rj)]).
    { pose proof FRR as [[WF _] _]. cbn in WF. chunk_join FRP FRR FRJ.
      eapply rw_cells_reshape; [exact FRJ| cbn; rewrite ?app_length, ?length_le8; cbn; split; [lia| exact I]| cbn; rewrite ?app_nil_r; reflexivity]. }
    assert (FRT' : rw_cells usegs m (G + 120) [CB 72 (le8 pb ++ le8 nb ++ tj)]).
    { pose proof FRT as [[WF _] _]. cbn in WF. eapply rw_cells_reshape; [exact FRT| cbn; rewrite ?app_length, ?length_le8; cbn; split; [lia| exact I]| cbn; rewrite ?app_nil_r, <- ?app_assoc; reflexivity]. }
    assert (FRM' : rw_cells usegs m (bv_unsigned sp + -312) [CB 16 (pj ++ le4 vw ++ le8 lnw)]).
    { pose proof FRM as [[WF _] _]. cbn in WF. chunk_join FRM FRL FMJ.
      eapply rw_cells_reshape; [exact FMJ| cbn; rewrite ?app_length, ?length_le8, ?length_le4; cbn; split; [lia| exact I]| cbn; rewrite ?app_nil_r, <- ?app_assoc; reflexivity]. }
    eapply cleanup_walk' with (r2 := r2) (dN := dN) (dP := dP) (dA := dA) (dB := dB) (dX := dX) (dY := dY) (dZ := dZ); try eassumption.
    intros Z0. exfalso. exact (NZ Z0).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090@L18933043916.4  L19246787633.2  L29010666655.144L43090215975.2  L45544150004.145L56190307013.2  L59308587280.3  L62165716363.2  L8322245898.4   00000300400500;00<00B00K00Q00\S1rSFS1r2RRFS1r2RRS1r2RR2HqS1r2RRS1r2RR1q2Hq". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma spec_erradd : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Ph,(42.$8.VL,VHI,)PLBi,(3.$4.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$43.PdN,$5.PdP,$5.PdA,$5.PdB,$5.PdX,$5.PdY,$5.PdZ,$5.Pp,$6.Plnw,(0.&40.)Pvw,(0.&40.)Ppb,(0.&40.)Pnb,(0.&40.)Pscj,(3.(0.&8.))Phj,(3.(0.&8.))Ptj,(3.(0.&8.))Ppj,(3.(0.&8.))Prj,(3.(0.&8.))Pr,$6.Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px9,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px18,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Px25,(0.&40.)Px26,(0.&40.)Px27,(0.&40.)Px28,(0.&40.)Px29,(0.&40.)Px30,(0.&40.)Px31,(0.&40.)P,(53.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(?.(10.-1000.R1<.)(10.R1<.=))P,(5;.R2?.)(55.$8.R30.(56.$8.VL,VHI,$57.$58.$59.$36.$37.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(5:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(21.(22.R1=.(23.&40.(;.(19.&40.Vsp,)-200.))Vgp,Vtp,R1<.R1;.R1:.(23.&40.VPKA,)R19.(23.&40.R1>.)R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)VF,(23.&40.+296?8.)Vfc,(26.(0.&40.))R31.(27.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros SI RR MK.
    zstep. zstep. zstep.
    rewrite swrap32_errsum by (clear -RR; lia).
    zstep. if_cases KC; zify_cond KC.
    { exfalso. clear -KC RR. rewrite ?signed_lit64 in KC by lia. lia. }
    zstep. if_cases KZ; zify_cond KZ.
    - exfalso. clear -KZ RR.
      apply Z.mod_divide in KZ; [| lia]. destruct KZ as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia.
    - zstep. eapply spec_err; [exact SI| clear -RR; lia| clear -RR; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L8765730602.1200000?S1L2lo3ACL1u2Q1". (* [comment removed for export] *)
  #[using="PKA C PAR bs ACL HTOP DHI IDL"] Lemma spinv_munch : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Ph,(42.$8.VL,VHI,)PLBi,(3.$4.)Pm,P,(0.&40.)(2.(0.&8.))Pm',P,(0.&40.)(2.(0.&8.))Pmo,$43.PdN,$5.PdP,$5.PdA,$5.PdB,$5.PdX,$5.PdY,$5.PdZ,$5.Pp,$6.Pp',$6.Plnw,(0.&40.)Plnw',(0.&40.)Pvw,(0.&40.)Pvw',(0.&40.)Ppb,(0.&40.)Ppb',(0.&40.)Pnb,(0.&40.)Pnb',(0.&40.)Pscj,(3.(0.&8.))Pscj',(3.(0.&8.))Phj,(3.(0.&8.))Phj',(3.(0.&8.))Ptj,(3.(0.&8.))Ptj',(3.(0.&8.))Ppj,(3.(0.&8.))Ppj',(3.(0.&8.))Prj,(3.(0.&8.))Prj',(3.(0.&8.))PW,(3.$5<.)P,(53.R21.R20.R1?.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R13.R11.R?.R=.R;.R9.R7.R5.R3.)P,(28.R2.R20.R1?.)P,(2=.$8.R21.R20.)P,(1=.$8.R21.)P,(50.(2:.$6.$6.)Liv,(2:.$6.$6.)(?.(12.Vlo,(5=.$6.$6.R1.))(12.(51.$6.$6.R1.)(19.&40.Vsp,)))R5.)P,Pd,$5.P,(46.$5.R1.(29.$5.R22.(29.$5.R21.(29.$5.R20.(29.$5.R1?.(29.$5.R1>.(29.$5.R1=.(29.$5.R1<.(2<.$5.)))))))))(5>.R8.(:.R2.)+10.)P,(38.$8.R24.(;.(19.&40.Vsp,)-128.)(29.$39.(3:.(23.&40.R1:.))(2<.$39.)))P,(?.(12.VP,R1;.)(12.R1;.(;.VP,VLEN,)))P,(38.$8.R26.(;.(19.&40.Vsp,)-120.)(29.$39.(40.#;8.R:.)(2<.$39.)))P,(38.$8.R27.(;.(19.&40.Vsp,)-130.)(29.$39.(3:.R1;.)(2<.$39.)))P,(38.$8.R28.(;.(19.&40.Vsp,)-138.)(29.$39.(40.#4.R>.)(29.$39.(41.R1:.)(2<.$39.))))P,(38.$8.R29.(;.(19.&40.Vsp,)-200.)(29.$39.(40.#8.R15.)(2<.$39.)))P,(38.$8.R2:.(;.(19.&40.Vsp,)-1?8.)(29.$39.(40.#8.R14.)(2<.$39.)))P,(38.$8.R2;.(;.(;.(19.&40.Vsp,)-1?8.)+78.)(29.$39.(3:.R1;.)(29.$39.(3:.R19.)(29.$39.(40.#38.R13.)(2<.$39.)))))P,(38.$8.R2<.(;.(19.&40.Vsp,)-68.)(29.$39.(3:.Vs11,)(29.$39.(3:.Vs10,)(29.$39.(3:.Vs9,)(29.$39.(3:.Vs8,)(29.$39.(3:.Vs7,)(29.$39.(3:.Vs6,)(29.$39.(3:.Vs5,)(29.$39.(3:.Vs4,)(29.$39.(3:.Vs3,)(29.$39.(3:.Vs2,)(29.$39.(3:.Vs1,)(29.$39.(3:.Vs0,)(29.$39.(3:.Vra,)(2<.$39.)))))))))))))))P,(18.$8.R2=.Vlo,(;.(19.&40.Vsp,)-200.))(53.R31.R30.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R24.R22.R20.R1>.R1<.R1:.R18.R16.R14.R12.)")
(* [comment removed for export] *).
  Proof.
    intros until W. (intros dd_H; ddestruct dd_H as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & _ & _ & _); intros MU WM MI' HW HW2 FRP PB FRR FRL FRM FR0 FRH FRT FR ST).
    destruct (ctx_munch' _ _ _ _ _ _ _ CX PX MU WM MI' HW) as [CX' PX'].
    dpose CX as (HH & _ & _ & MI & _). destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    pose proof (tmp_ok_munch_fine usegs L _ _ _ _ _ _ _ TOK MU WM MI MI' HW2
                  ltac:(clear -HW ACL; induction W as [|[u v] W IH]; [constructor|]; inversion HW as [|? ? [Q1 Q2] Q3]; subst; cbn in Q1; constructor; [cbn; lia| apply IH; exact Q3]) HBR) as TOK'.
    split; [exact CX'|]. split; [exact PX'|]. split; [exact TOK'|].
    split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
    split; [exact FRP|]. split; [exact PB|]. split; [exact FRR|]. split; [exact FRL|]. split; [exact FRM|].
    split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FR| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01W0@D10463954377.187D11805467289.185D11805467289.239D2090238905.187 D43542295471.241D43548436307.239D44622288685.187D44622288685.241D49698585326.187D49698585326.241D49705053714.185D49705053714.239D9919893866.185 D9926296982.187 L10355845457.1  L10837299463.1  L11337802139.27 L12632560433.6  L12857244009.1  L1386329760.209 L14351168243.6  L15217048541.1  L15413099.6     L15946219575.1  L15953569441.0  L16270152278.27 L1717687351.1   L17679132023.27 L18173815659.6  L18933043916.4  L19730642225.6  L20361976947.6  L20380073089.5  L20729264674.28 L21730139755.6  L21963754809.27 L22530056029.1  L22575419897.27 L23380989714.7  L25286511979.6  L25644925211.8  L26087481949.1  L26387515891.6  L2661346595.1   L2689769980.28  L26913259113.6  L27105925383.1  L28456411139.176L28684289806.9  L28897400179.6  L28915496321.5  L29558833075.176L30392002547.6  L30944687130.6  L31471788297.3  L34347336241.6  L34493188407.1  L35501726675.11 L3571786347.6   L36949002973.1  L37856140983.1  L37905822001.6  L38732773782.8  L3983087197.1   L39935534662.5  L40988025478.27 L41253790699.28 L41462195249.6  L43444914539.6  L4367979357.1   L43875673135.3  L45042753046.27 L46350850038.9  L47003401323.6  L47740243316.230L49428161872.245L49664744988.1  L52715793099.27 L54973495411.6  L55163532373.246L57498838785.5  L58131691093.247L58531213267.1  L58919282697.3  L58921022958.27 L59194810551.1  L59571318199.1  L59620532273.6  L59654577821.13 L61120265865.3  L61436700724.28 L61966242198.238L62255212841.5  L62438632883.176L63176922929.6  L6430512105.6   L66272636120.230L68574673117.1  L7330518636.27  L8322245898.4   L8325611891.6   L9605508784.246 L9788829782.27  00001601M01d02e03L03c04l06306`07K07f08A08X09A09E09I09S09W09[09\0:10:50:90:=0:>0:^0:b0;60;:0;>0;B0;W0;h0;i0;m0<M0<Q0<a0=90==0=X0=Y0=n0>20>30>40>80>L0>M0>b0?30?G0?\0@10@<0@@0@D0@e0@i0@m0A10A50AR0AV0AZ0B>0B?0BC0BG0BK0BV0C:0CU0CY0Cm0E:0E>0EZ0Eo0FI0FZ0G40G80G90G]0Ga0Ge0Gi0Gj0H50H60HJ0HN0Hb0Hf0Hj0I>0IB0J80JE0JZ0Kg0LGS1L2HI2ra2sp2h03PKA1C3PAR2bs3NZP3NZR4HTOP2C01h1p3lnw2HT2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs2HBS2ra2sp3PKA1C3PAR2bs2HBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO2C01p3lnw2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3x542HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs2HBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C01p3lnw2HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C03x542HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3SPR1p3lnw2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3SPR3x542HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3SPR2HBS2ra2sp3PKA1C3PAR2bs3SPR2HBS2ra2sp3PKA1C3PAR2bs2HBS2ra2sp3PKA1C3PAR2bs1p3lnw2HB5Ha_st5Hl_stS2spS2spS2sp2lo2bsS2spS2spFS1L3HLS2sp2lo3SLO3ACLS2spS2spS2spSS1L3HLS2sp2lo2bs3SLO3ACL3SPA3ACPS2spS1L2HI2sp2h02bs4HTOPS2spS2r2S2spS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOFS2spS1L3HLS2sp2lo2bs3SLO3ACL3DHI3ACPS2spS1L2sp2lo2bs3SLOS3LEN1P1p3lnw3PLB2PB3LNRS2spS1L3HLS2sp2lo3SLO3ACL2dN2P4FS1L3HLS2sp2lo3SLO3ACLS2spFFS2spS2ra2sp3PKA1C3PAR2bsFS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOS2ra2sp3PKA1C3PAR2bsS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLO3ACLS2r23RR22HqS2spS2spS1L2HI3HLS2sp2h02lo3SLO4HTOP1a2HaS2spS2spS2spS2spS1L3HLS2sp2lo3SLO3ACL3SPR3ACPS2spS2spS1L3HLS2sp2lo3BUF2bs3SLO3ACL3ACP3BACFS2spS2spS2spS2r23RR22NZS1L3HLS2sp2lo3BUF2bs3SLO3ACL3ACP3BACS3LEN1P1p3lnw2PB3LNR2p23PB2S2spS2ra2sp3PKA1C3PAR2bsS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3DSP3DPC3NZR3DSR2RC3SLO3ACL3ACP3CAC2C02rj2WFS2spS1L3HLS2sp2lo2bs3SLO3ACL3ACPS1L3HLS2sp2lo3SLO3ACLS2ra2sp3PKA1C3PAR2bs2rj2WFS1L3HLS2sp2lo3SLOS2ra2sp3PKA1C3PAR2bs2pj2WFS2spFS1L3HLS2sp2lo3BUF2bs3SLO3ACL3ACP3BACS2spS2spS2spFS2sp2a'3Ha'FS2ra2sp3PKA1C3PAR2bsS2spS2ra2sp3PKA1C3PAR2bsS2spS2spS2ra2sp3PKA1C3PAR2bsS2spS1L3HLS2sp2lo3LEN1P3BUF2bs2BP3SLO3ACL3ACP1p3lnw2PB3LNRS2r23RR21q2HqS1L3HLS2sp2lo3SLO3ACLS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3DSP3DPC3NZR3DSR2RC3SLO3ACL3ACP3CAC2C02pj2WFS1L3HLS2sp2lo2bs3SLO3ACL3SPA3ACP". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM"] Lemma specC2_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_H ()) "Ph,(42.$8.VL,VHI,)PLBi,(3.$4.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$43.PdN,$5.PdP,$5.PdA,$5.PdB,$5.PdX,$5.PdY,$5.PdZ,$5.Pp,$6.Plnw,(0.&40.)Pvw,(0.&40.)Ppb,(0.&40.)Pnb,(0.&40.)Pscj,(3.(0.&8.))Phj,(3.(0.&8.))Ptj,(3.(0.&8.))Ppj,(3.(0.&8.))Prj,(3.(0.&8.))Px1,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px10,(0.&40.)Px11,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)Px18,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Px25,(0.&40.)Px26,(0.&40.)Px27,(0.&40.)Px28,(0.&40.)Px29,(0.&40.)Px30,(0.&40.)Px31,(0.&40.)P,(53.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)P,(12.(;.R25.(19.&40.R24.))(;.VP,VLEN,))P,(10.=(33.(34.(0.&8.)Vbs,)))(55.$8.R2?.(56.$8.VL,VHI,$57.$58.$59.$36.$37.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(5:.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(21.(22.R1=.(23.&40.(;.(19.&40.Vsp,)-200.))Vgp,Vtp,R1<.R1;.R1:.(23.&40.VPKA,)(23.&40.(;.VP,VLEN,))R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)VF,(23.&40.+29:08.)Vfc,(26.(0.&40.))R30.(27.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros SI PLB BL.
    dpose SI as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & FRP & PB & FRR & FRL & FRM & FR0 & FRH & FRT & FR & ST).
    ddestruct CX as (HH & HT & MF & MI & SOK & EXT & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    pose proof (bv_unsigned_in_range 64 lnw) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    (* [comment removed for export] *)
    pose proof (munch_refl [(REF, REF + 8)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep. zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN; [pnull KN|].
    zstep. replace (bv_unsigned lnw + p) with (p + bv_unsigned lnw) in * by lia.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with M : mem_inv usegs m1 |- _ => rename M into MI1 end. match goal with W : wmono usegs m m1 |- _ => rename W into WM1 end.
    pose proof (spinv_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI MU WM1 MI1
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB EX EY EZ)
                  FRP ltac:(clear -PB PLB LNR; lia) FRR FRL FRM FR0 FRH FRT FR ST) as SI1.
    dpose SI1 as (CX1 & PX1 & TOK1 & _). dpose CX1 as (HH1 & HT1 & MF1 & _ & SOK1 & EXT1 & IDS1).
    clear MU WM1 SI PX TOK HH HT MF SOK EXT IDS MK. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    pose proof (ctx_bytes m1 PX1) as HBS1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    pose proof (U_asn1_get_mpi_spec L HI U_MEMSET_FUNC HLS (U_mpi_read_binary_spec L HI HFREE HCALLOC HLS SW DIMG HND _ eq_refl)) as SGM.
    unfold asn1_get_mpi_stmt, asn1_get_mpi_post, U_ASN1_GET_MPI in SGM.
    eapply aevtM_cut.
    { eapply SGM with (lo := lo) (h := h) (LB := LBi) (PP := REF) (P := p + bv_unsigned lnw) (END := PEND) (BUF := BUF) (bs := bs) (dX := dN);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
        first [ exact HH1 | exact FRP | exact HBS1 | exact TP | exact MI1 | exact SOK1 | exact CA | exact DI1 | exact DI2 | eassumption
              | reflexivity | rewrite EN; f_equal; clear; lia
              | exact (tmp_ok_in usegs _ _ _ _ _ _ TOK1 ltac:(inlist))
              | exact (proj1 (proj1 (Forall_forall _ _) (proj1 (proj2 TOK1)) _ ltac:(inlist)))
              | rewrite HT1; eapply tmp_writable; [exact HH1| exact TOK1| inlist| clear -SLO HLS; lia| clear; lia]
              | rewrite ?EN; rewrite ?HT1; clear -PB PLB LNR BP PL B63 BUF0 BAC ACL ACP SLO HLS HTOP SPA SPR DHI; lia
              | (* [comment removed for export] *)
                intros O; first [ destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _];
                                  destruct (mpdr_blk_facts usegs L _ _ _ (proj1 (tmp_ok_in usegs _ _ _ _ _ _ TOK1 ltac:(inlist))) O HBR1) as (_ & _ & _ & P4 & _);
                                  right; clear -P4 ACL SLO HLS; lia
                                | eapply (tmp_apart_LB h LBi _ m1 mo); [exact HH1| exact EXT1| exact TOK1| intros b Hb; exact Hb| inlist| exact O| exact INB| exact BL] ]
              | (* [comment removed for export] *) intros a Ha; left; rewrite ?HT1; clear -Ha SLO HLS ACL HTOP; lia
              | (* [comment removed for export] *) intros a Ha; right; right; exists (BUF, Z.of_nat (length bs)); split; [eapply lb_ext_sub; [exact EXT1| exact INB]| exact Ha]
              | match goal with |- ?g => idtac "GMLEFT" g end ]. }
    clear SGM.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MD2 & OUT & PX2 & SOK2 & FRP2 & PB2 & RR2 & RZ2 & NEW).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match type of HT2 with heap_top _ _ _ ?hh = _ => rename hh into h2 end.
    match type of HH2 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB2 end.
    match type of MD2 with mpd_at _ _ _ ?dd => rename dd into dN' end.
    ddestruct OUT as (EAD & NSD & O3 & O4 & O5). pose proof (conj EAD (conj NSD (conj O3 (conj O4 O5)))) as OUT.
    destruct (spinv_update h LBi m1 mo h2 LB2 m2 mo2 _ dN dN' [(REF, REF + 8)] CX1 PX1 TOK1 ltac:(inlist) HH2 HT2 MF2 MI2 SOK2 MD2 OUT NEW PX2
                ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as (CX2 & PXn2 & TOK2).
    rewrite (proj1 (tmp_upd7 dN' dN dP dA dB dX dY dZ EN EP EA EB EX EY EZ) ltac:(rewrite EAD; exact EN)) in CX2, TOK2.
    (* [comment removed for export] *)
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _].
    pose proof (proj1 (tmp_ok_in usegs _ _ _ _ _ _ TOK1 ltac:(inlist)) : mpdr_at usegs m1 LBi dN) as MDN.
    pose proof (proj1 (proj1 (Forall_forall _ _) (proj1 (proj2 TOK1)) dN ltac:(inlist))) as NSN.
    rewrite (mpd_ivs_fp dN NSN) in PX2.
    repeat match goal with
    | Hc : rw_cells usegs m1 ?a ?cs |- _ =>
        first [ apply (heap_presx_rw_cells usegs L _ _ _ m1 m2 a cs PX2) in Hc;
                [ | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; intros a' Ha'; left; clear -Ha'; lia
                  | split; [cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia
                           | eapply (fp_disjoint_stack usegs L dN m1 LBi); [exact MDN| exact HBR1| clear -ACL SLO HLS; lia
                             | rewrite EN; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; clear; lia] ] ]
              | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
    end.
    lazymatch type of FRP2 with rw_cells _ _ _ [C8 (Z_to_bv 64 ?q)] => rename q into p2 end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into r2 end.
    assert (SI2 : SPINV h2 LB2 m2 mo2 dN' dP dA dB dX dY dZ p2 lnw vw pb nb scj hj tj pj rj).
    { split; [exact CX2|]. split; [exact PXn2|]. split; [exact TOK2|].
      split; [rewrite EAD; exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [exact FRP2|]. split; [clear -PB PB2 PLB LNR; lia|]. split; [exact FRR|]. split; [exact FRL|]. split; [exact FRM|].
      split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FR| exact ST2]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    clear CX1 PX1 TOK1 HH1 HT1 MF1 SOK1 EXT1 IDS1 MI1 HBS1 MK1 PX2 HBR1 MDN.
    zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *) assert (NZ : r2 <> 0) by (intros ->; apply K2; reflexivity).
      eapply spec_erradd; [exact SI2| clear -RR2 NZ; lia| exact MK2]. }
    assert (Z2 : r2 = 0).
    { clear -K2 RR2. apply Z.mod_divide in K2; [| lia]. destruct K2 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    subst r2. clear K2.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SBL. unfold mpi_bitlen_stmt, mpi_query_post, U_MPI_BITLEN in SBL.
    destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 _].
    pose proof (tmp_ok_in usegs _ _ _ _ _ _ TOK2 ltac:(inlist) : mpd_at usegs m2 LB2 dN') as MDN2.
    pose proof (munch_refl [(bv_unsigned sp + -376, bv_unsigned sp + -368)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    replace (G + 120) with (bv_unsigned sp + -384) in FRT by (clear; lia).
    zstep. zstep.
    acallx (eapply SBL with (dX := dN');
            [ exact MDN2 | intros O; destruct (mpdr_blk_facts usegs L _ _ _ (proj1 MDN2) O HBR2) as (_ & _ & P0 & _); exact P0 | exact MI2
            | rewrite EAD, EN; f_equal; clear; lia ]).
    try clear PC.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with M : mem_inv usegs m3 |- _ => rename M into MI3 end. match goal with W : wmono usegs m2 m3 |- _ => rename W into WM3 end.
    match goal with U : munch _ m2 m3 |- _ => rename U into MU3 end.
    replace (bv_unsigned sp + -384) with (G + 120) in FRT by (clear; lia).
    pose proof (eq_trans EAD EN) as EN'.
    lazymatch type of FRT with rw_cells _ _ _ [C8 _; C8 ?nb3; _] =>
    pose proof (spinv_munch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI2 MU3 WM3 MI3
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN' EP EA EB EX EY EZ)
                  FRP2 ltac:(clear -PB PB2 PLB LNR; lia) FRR FRL FRM FR0 FRH FRT FR ltac:(assumption)) as SI3 end.
    dpose SI3 as (CX3 & PX3 & TOK3 & EN3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ST3).
    (* [comment removed for export] *)
    assert (FRR' : rw_cells usegs m3 REF [CB 192 (le8 (Z_to_bv 64 p2) ++ rj)]).
    { pose proof FRR as [[WF _] _]. cbn in WF. chunk_join FRP2 FRR FRJ.
      eapply rw_cells_reshape; [exact FRJ| cbn; rewrite ?app_length, ?length_le8; cbn; split; [lia| exact I]| cbn; rewrite ?app_nil_r; reflexivity]. }
    assert (FRM' : rw_cells usegs m3 (bv_unsigned sp + -312) [CB 8 (pj ++ le4 vw); CB 4 (firstn 4 (le8 lnw)); CB 4 (skipn 4 (le8 lnw))]).
    { pose proof FRM as [[WF _] _]. cbn in WF. chunk_join FRM FRL FMJ.
      eapply rw_cells_reshape; [exact FMJ| | cbn -[le8 le4]; rewrite ?app_nil_r; rewrite (firstn_skipn 4 (le8 lnw)); rewrite <- ?app_assoc; reflexivity].
      cbn -[le8 le4]. rewrite ?app_length, ?length_le4, ?firstn_length, ?skipn_length, ?length_le8. cbn. repeat split; lia. }
    eapply idloop_walk' with (dN := dN') (dP := dP) (dA := dA) (dB := dB) (dX := dX) (dY := dY) (dZ := dZ); try eassumption.
    all: match goal with |- ?g => idtac "LEFT:" g end.
    all: fail.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End EP.
