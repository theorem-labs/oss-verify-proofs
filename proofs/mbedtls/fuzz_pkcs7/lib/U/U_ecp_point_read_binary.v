(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts CrtFacts RepEcp EcpFacts EcpLoad. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney EcpJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_cmp U_mpi_bitlen U_mpi_init U_mpi_lset U_mpi_set_bit U_mpi_read_binary U_mpi_read_binary_le U_mpi_shift_r U_mpi_divmod_stmt U_ecp_red U_ecp_mul_mod U_ecp_sw_rhs U_ecp_derive_y U_ecp_point_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
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
Ltac2 gd_tbl_P_ecp_point_read_binary () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_X"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Y"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Z"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_pt"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_point_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_freeable"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_mpds"; "pt_dis"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_blocks"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.cons"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_G"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_derive_y.ECP_FEATURE_UNAVAILABLE"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_h"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_A"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_B"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "ecp_point_read_post"; "RocqVerifyHarness.AgentSubmission.USpec.EcpJourney.jtmp"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "PR.dis"; "PR.tri"; "ECP_POINT_READ_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.USpec.EcpJourney.jst"; "PR.pr_XO"; "PR.slots"; "PR.pr_state"; "PR.pr_ctx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkPT"; "PR.pr_regs"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_lset.lset_R"; "ecp_point_read_binary_stmt"; "U_ECP_POINT_READ_BINARY"].


Definition ECP_POINT_READ_STACK : Z := 800.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pt_dis (p : ecp_pt) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "(0.P,(1.$2.(3.(4.O1.))$5.)P,(1.$2.(3.(6.O1.))$5.)(7.(1.(8.$9.$9.)(:.$9.$9.(;.(4.O1.))(<.+4.(=.(4.O1.))))(:.$9.$9.(;.(6.O1.))(<.+4.(=.(6.O1.))))))(0.P,(1.$2.(3.(4.O1.))$5.)P,(1.$2.(3.(>.O1.))$5.)(7.(1.(8.$9.$9.)(:.$9.$9.(;.(4.O1.))(<.+4.(=.(4.O1.))))(:.$9.$9.(;.(>.O1.))(<.+4.(=.(>.O1.))))))P,(1.$2.(3.(6.O1.))$5.)P,(1.$2.(3.(>.O1.))$5.)(7.(1.(8.$9.$9.)(:.$9.$9.(;.(6.O1.))(<.+4.(=.(6.O1.))))(:.$9.$9.(;.(>.O1.))(<.+4.(=.(>.O1.))))))))")
(* [comment removed for export] *).

Definition ecp_point_read_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (G : Z) (g : ecp_grp) (Q : Z) (p : ecp_pt) (bs : list byte) (MC lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Lc,$?.(10.(11.&40.)Lt0,(11.&40.)(10.(11.&40.)Lt1,(11.&40.)(10.(11.&40.)Lt2,(11.&40.)(10.(11.&40.)La1,(11.&40.)(10.(11.&40.)La2,(11.&40.)(10.(11.&40.)La3,(11.&40.)(10.(11.&40.)La4,(11.&40.)(10.(11.&40.)La5,(11.&40.)(10.(11.&40.)La6,(11.&40.)(10.(11.&40.)La7,(11.&40.)(10.(11.&40.)Lt3,(11.&40.)(10.(11.&40.)Lt4,(11.&40.)(10.(11.&40.)Lt5,(11.&40.)(10.(11.&40.)Lt6,(11.&40.)(10.P,(11.&40.)(12.(11.&8.))Lm',P,(11.&40.)(12.(11.&8.))(10.$13.Lmo',$13.(10.(14.O21.O20.O1?.)Lh',(14.O21.O20.O1?.)(10.(15.$16.)LLB',(15.$16.)(10.$17.Lp',$17.(10.$9.Lr,$9.(10.(11.&40.)Lcnt',(11.&40.)(0.(1.$?.R16.(18.(19.(1:.O1=.O1<.O1;.O1:.R15.R14.R13.O19.O18.(1;.&40.R2.)R12.R11.R10.R?.R>.R=.R<.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.R;.R:.R9.R8.)O=.(1<.O1=.)O<.(1=.(11.&40.))R7.(1>.O21.))R6.))(0.(1?.O21.R7.)(0.(20.O21.R7.O3.(21.&40.O1<.))(0.(22.O1.R6.)(0.(1.$9.(23.O21.O20.O1?.R5.)(23.O21.O20.O1?.O;.))(0.(24.O21.O20.O1?.R5.R4.R7.R6.)(0.(25.O21.R7.R4.O7.R3.)(0.(26.R3.)(0.(27.$28.Ld,$28.(29.(1.$9.(2:.R1.)+1.)(1.$9.(2:.R1.)-1.))(2;.R3.))(0.(2<.R3.)(0.Pb,$16.P,(2=.$16.R1.O:.)(2=.$16.R2.R6.)(0.Pb,$16.P,(2=.$16.R1.R5.)(29.(2=.$16.R2.O:.)(2=.$16.R2.(2>.R5.)))(0.Pb,$16.P,(2=.$16.R1.(2>.R4.))(7.(2=.$16.R2.O:.))(0.(2?.O21.O20.O:.(21.&40.O1<.)(30.(8.$9.$9.)(:.$9.$9.O7.(31.O7.+30.))(30.(8.$9.$9.)(:.$9.$9.O4.(31.O4.+8.))(32.(8.$9.$9.))))O2.R7.)(0.(33.O21.O20.R7.)(0.(34.O21.O1>.R7.R4.O9.O8.)(0.(35.O21.R7.O4.(30.$36.(37.R1.)(32.$36.)))(0.P,(1.$9.(;.(4.(38.O8.)))=)(0.(1.$17.R4.O6.)(0.(1.(15.$16.)R5.O:.)P,(1.(11.&40.)(1;.&40.R3.)(1;.&40.$39.))(3:.+1.(3;.(3<.(11.&8.)O5.)))))(0.(3=.(3>.(3?.+2.+1?.))R2.)(3:.R2.=)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_point_read_binary_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ENTRY MSF MC STACK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Pra,(11.&40.)Psp,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps0,(11.&40.)Ps1,(11.&40.)Pa0,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Ps2,(11.&40.)Ps3,(11.&40.)Ps4,(11.&40.)Ps5,(11.&40.)Ps6,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)PF,(40.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Ph,(14.O8.O7.O6.)PLB,(15.$16.)PG,$9.PQ,$9.PB,$9.Pg,$41.Pp,$17.Pbs,(15.(11.&8.))Pcnt,(11.&40.)Plo,$9.P,(24.O8.O7.O6.R:.R9.R<.R;.)P,(34.O8.O5.R=.R:.R9.R6.)P,(29.(1.$9.(2:.(42.R7.))+1.)(1.$9.(2:.(42.R7.))-1.))P,P,(7.(1.$9.(;.(4.(38.R8.)))=))P,(7.(1.$9.(;.(6.(38.R9.)))=))(0.(1.$9.(43.R:.)+1.)(0.(1.$9.(2:.(42.R:.))+1.)(0.(1.$9.(2:.(44.R:.))+1.)(0.(1.$9.(2:.(45.R:.))+1.)(0.(3:.+1.(46.(42.R:.)))(3:.(=.(42.R:.))+1387.))))))P,(47.O7.R=.R5.R<.+<0.)P,(29.(3:.(31.R=.+<0.)R6.)(3:.(21.&40.R31.)R=.))P,(29.(3:.(31.O2.+8.)R>.)(3:.(31.R>.+<0.)O2.))P,(25.O8.R13.R10.R>.R;.)P,(27.$28.Ld,$28.(1.$2.(3.R1.)$48.)(2;.R<.))P,(27.$28.Ld,$28.(29.(1.$9.(2:.R1.)+1.)(1.$9.(2:.R1.)-1.))(2;.R=.))P,(49.O7.R13.(21.&40.R36.)(23.O8.O7.O6.R14.)R11.+30.)P,Pa,$9.P,(0.(3:.R13.R1.)(3=.R1.(31.R13.+30.)))P,(0.(3:.(4:.O7.)R2.)(3=.R2.(4;.O7.)))(4<.O7.R3.)P,(29.(3:.(31.R13.+30.)R=.)(3:.(21.&40.R38.)R13.))P,(29.(3:.(31.O2.+8.)R14.)(3:.(31.R14.+30.)O2.))P,P,(7.(1.$9.(;.(4.(38.R13.)))=))(29.(3:.(31.R16.+30.)R17.)(3:.(31.R17.+<0.)R16.))P,P,(7.(1.$9.(;.(4.(38.R14.)))=))Pd,$28.P,(2=.$28.R1.(4=.R16.))P,(1.$2.(3.R2.)$5.)(29.(3:.(31.R1:.+30.)(;.R3.))(3:.(31.(;.R3.)(<.+4.(=.R3.)))R1:.))P,(4>.O8.R1<.R16.R13.)P,(3=.=R17.)P,(3=.(31.R18.(3;.(3<.(11.&8.)R15.)))(3?.+2.+3?.))P,(47.O7.R1<.R14.R19.(3;.(3<.(11.&8.)R16.)))P,(29.(3:.(31.R1:.(3;.(3<.(11.&8.)R17.)))R15.)(3:.(21.&40.R40.)R1:.))P,(29.(3:.(31.R1;.(3;.(3<.(11.&8.)R18.)))R1<.)(3:.(31.R1<.+30.)R1;.))P,(29.(3:.(31.O2.+8.)R1<.)(3:.(31.R1<.(3;.(3<.(11.&8.)R19.)))O2.))P,(35.O8.R23.O2.(30.$36.(37.R19.)(32.$36.)))P,(3:.(4:.O7.)O2.)P,(3:.(31.O2.+8.)(4;.O7.))P,Pa,$9.P,(0.(3:.O2.R1.)(3=.R1.(31.O2.+8.)))(0.(7.(4?.O7.R2.))(4<.O7.R2.))P,(20.O8.R27.R1<.(21.&40.R47.))P,(3:.R1=.(50.(50.(21.&40.R48.)O1.)(51.O7.)))P,(3:.(52.O7.)R1>.)P,(3:.(21.&40.R4:.)(23.O8.O7.O6.R28.))P,(1.$9.(53.(21.&40.R4;.)+10.)=)P,(3:.(4;.O7.)(52.O7.))P,(1.(11.&40.)R4;.(1;.&40.(54.O7.)))P,(1?.O8.R2>.)P,(1.$9.(53.(21.&40.R50.)+2.)=)P,(33.O8.O7.R30.)P,(55.O7.O3.+8.)P,(1.(11.&40.)R4:.(1;.&40.R2>.))P,(1.(11.&40.)R4:.(1;.&40.R2>.))P,(1.(11.&40.)R4:.(1;.&40.R2>.))P,(1.(11.&40.)R4:.(1;.&40.(3;.(3<.(11.&8.)R2<.))))(56.O8.R35.(57.O8.O7.O6.O5.R57.R56.R55.R54.R50.R4?.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R38.R37.R34.R33.R32.R2?.R31.R2>.R2=.O2.R2;.R36.R35.)(19.(1:.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.)R38.(1;.&40.O4.)R37.(1=.(11.&40.))R36.(1>.O8.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L41691758847.10L41698164036.9 L53519157932.6 00000?00J00MS1d2HL2N12P02B1S1d2HL2N11HS1d". (* [comment removed for export] *)
Lemma mpdr_p_range' : forall segs m LB d, mpdr_at segs m LB d -> 0 <= md_p d < 2^64.
Proof.
  intros segs m LB d (_ & _ & _ & HL & HN & HO). destruct (md_own d).
  - flat constr:(HO) 2%nat. flclear HO. intros -> _. lia.
  - flat constr:(HO) 4%nat. flclear HO. intros N1 _ _ U. pose proof (u32arr_bound _ _ _ _ U). lia.
  - flat constr:(HO) 5%nat. flclear HO. intros N1 _ P0 (B0 & B1 & _) _. rewrite u32s_length in B1. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition U_ECP_POINT_READ_BINARY : Z := 0x38764.
Notation U_MUL_COUNT := 380840 (only parsing).

Section PR.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Variable MT : list modp_ent.
  Hypothesis HDY : ecp_derive_y_stmt usegs L HI MT 0x389dc U_MEMSET_FUNC U_MUL_COUNT ECP_DERIVE_Y_STACK.
  Hypothesis HSIZE : mpi_size_stmt usegs 0x1fb84.
  Hypothesis HRB : mpi_read_binary_stmt usegs L HI 0x1ff64 U_MEMSET_FUNC.
  Hypothesis HRBLE : mpi_read_binary_le_stmt usegs L HI 0x1fdac U_MEMSET_FUNC.
  Hypothesis HLSET : mpi_lset_stmt usegs L HI 0x1f808 U_MEMSET_FUNC.
  Hypothesis HSETB : mpi_set_bit0_stmt usegs 0x1f958.
  Hypothesis HFREEM : mpi_free_stmt usegs L HI 0x1f4a8 U_MEMSET_FUNC.

  Definition pr_regs (s6e s5e s4e s3e s2e s1e s0e rae : word) : list cell := [C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae].
  Definition pr_XO (Q : Z) : list ivl := [(Q, Q + 48); (U_MUL_COUNT, U_MUL_COUNT + 8)].
  Definition dis (d1 d2 : mpd) : Prop := md_own d1 = LHeap -> md_own d2 = LHeap -> (md_p d1, 4 * md_n d1) <> (md_p d2, 4 * md_n d2).

  (* [comment removed for export] *)
  Definition tri (LB LBk : list blk) (mk : mem) (A1 : Z) (d1 : mpd) (A2 : Z) (d2 : mpd) (A3 : Z) (d3 : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "(0.(58.$59.O9.O8.O7.O6.O5.)(0.(58.$59.O9.O8.O7.O4.O3.)(0.(58.$59.O9.O8.O7.O2.O1.)(0.Pb,$16.P,(2=.$16.R1.O8.)(29.(2=.$16.R2.O9.)(29.(2=.$16.R2.(5:.O5.))(29.(2=.$16.R2.(5:.O3.))(2=.$16.R2.(5:.O1.)))))(0.(5;.O5.O3.)(0.(5;.O5.O1.)(5;.O3.O1.)))))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Definition slots (Q A1 A2 A3 : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "(0.(3:.O4.O3.)(0.(3:.(31.O3.+10.)(31.O4.+30.))(0.(3:.O4.O2.)(0.(3:.(31.O2.+10.)(31.O4.+30.))(0.(3:.O4.O1.)(0.(3:.(31.O1.+10.)(31.O4.+30.))(0.(29.(3:.(31.O3.+10.)O2.)(3:.(31.O2.+10.)O3.))(0.(29.(3:.(31.O3.+10.)O1.)(3:.(31.O1.+10.)O3.))(29.(3:.(31.O2.+10.)O1.)(3:.(31.O1.+10.)O2.))))))))))")
(* [comment removed for export] *).

  Lemma dis_sym : forall d1 d2, dis d1 d2 -> dis d2 d1.
  Proof. intros d1 d2 H O2 O1 E. exact (H O1 O2 (eq_sym E)). Qed.
  Lemma tri_swap12 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "PLB,(15.$16.)PLBk,(15.$16.)Pmk,P,(11.&40.)(12.(11.&8.))PA1,$9.Pd1,$28.PA2,$9.Pd2,$28.PA3,$9.Pd3,$28.P,(5<.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(5<.R:.R9.R8.R5.R4.R7.R6.R3.R2.)")
(* [comment removed for export] *).
  Proof. intros until d3. intros (T1 & T2 & T3 & COV & D12 & D13 & D23). refine (conj T2 (conj T1 (conj T3 (conj _ (conj (dis_sym _ _ D12) (conj D23 D13)))))). intros b Hb. destruct (COV b Hb) as [X|[X|[X|X]]]; tauto. Qed.
  Lemma tri_swap13 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "PLB,(15.$16.)PLBk,(15.$16.)Pmk,P,(11.&40.)(12.(11.&8.))PA1,$9.Pd1,$28.PA2,$9.Pd2,$28.PA3,$9.Pd3,$28.P,(5<.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(5<.R:.R9.R8.R3.R2.R5.R4.R7.R6.)")
(* [comment removed for export] *).
  Proof. intros until d3. intros (T1 & T2 & T3 & COV & D12 & D13 & D23). refine (conj T3 (conj T2 (conj T1 (conj _ (conj (dis_sym _ _ D23) (conj (dis_sym _ _ D13) (dis_sym _ _ D12))))))). intros b Hb. destruct (COV b Hb) as [X|[X|[X|X]]]; tauto. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L49682036451.2000000>S1Q2A12A22A31H". (* [comment removed for export] *)
  Lemma slots_swap12 : forall Q A1 A2 A3, slots Q A1 A2 A3 -> slots Q A2 A1 A3. Proof. unfold slots. intros. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55475969356.2000000>S1Q2A12A22A31H". (* [comment removed for export] *)
  Lemma slots_swap13 : forall Q A1 A2 A3, slots Q A1 A2 A3 -> slots Q A3 A2 A1. Proof. unfold slots. intros. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition pr_ctx (h : HST usegs L HI) (LB : list blk) (G Q : Z) (g : ecp_grp) (cnt : word) (SP lo : Z) (m : mem) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "(0.(24.$59.VL,VHI,O:.O9.O2.O1.)(0.(34.$59.VMT,O2.O9.O8.O6.)(0.(7.(1.$9.(;.(4.(38.O6.)))=))(0.(47.VL,O9.O3.O8.+<0.)(0.(29.(3:.(31.O8.+<0.)O3.)(3:.O4.O8.))(0.(29.(3:.(31.+5<?:8.+8.)O8.)(3:.(31.O8.+<0.)+5<?:8.))(0.(49.VL,O9.O4.(23.$59.VL,VHI,O:.)O7.+30.)(0.Pa,$9.P,(0.(3:.O7.R1.)(3=.R1.(31.O7.+30.)))P,(0.(3:.(4:.VL,)R2.)(3=.R2.(4;.VL,)))(4<.VL,R3.)(0.(29.(3:.(31.O7.+30.)O3.)(3:.O4.O7.))(0.(29.(3:.(31.O7.+30.)O8.)(3:.(31.O8.+<0.)O7.))(0.(29.(3:.(31.+5<?:8.+8.)O7.)(3:.(31.O7.+30.)+5<?:8.))(0.Pd,$28.P,(2=.$28.R1.(4=.O6.))P,(1.$2.(3.R2.)$5.)(29.(3:.(31.O7.+30.)(;.R3.))(3:.(31.(;.R3.)(<.+4.(=.R3.)))O7.))(0.(35.$59.O2.+5<?:8.(30.$36.(37.O5.)(32.$36.)))(0.(3:.(4:.VL,)+5<?:8.)(0.(3:.(31.+5<?:8.+8.)(4;.VL,))(0.Pa,$9.P,(0.(3:.+5<?:8.R1.)(3=.R1.(31.+5<?:8.+8.)))(0.(7.(4?.VL,R2.))(4<.VL,R2.))(0.(3:.O3.(50.(50.O4.$5=.)(51.VL,)))(0.(3:.(52.VL,)O3.)(0.(3:.O4.(23.$59.VL,VHI,O:.))(0.(1.$9.(53.O4.+10.)=)(0.(3:.(4;.VL,)(52.VL,))(0.(1?.$59.O2.)(0.(33.$59.VL,O2.)(0.(55.VL,$5>.+8.)(3=.O4.(3?.+2.+40.))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Ltac prctx CTX := pose proof CTX as (HH & GR & GXN & GCR & GS & MCG & QW & QD & QS & QG & MCQ & GQL & CNT & MC1 & MC2 & MCS & SLO & ACL & HTOP & SPA & DHI & MI & SOK & CA & SPU).
  Ltac pr_qfacts STATE :=
    let J := fresh "J" in let T := fresh "T" in let S := fresh "S" in
    pose proof STATE as (J & T & S); clear J;
    let M1 := fresh "M" in let M2 := fresh "M" in let M3 := fresh "M" in
    let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
    destruct T as ((M1 & E1 & _) & (M2 & E2 & _) & (M3 & E3 & _) & _);
    let C1 := fresh "C" in let C2 := fresh "C" in let C3 := fresh "C" in
    let L1 := fresh "AL" in let L2 := fresh "AL" in let L3 := fresh "AL" in
    let P1 := fresh "P" in let P2 := fresh "P" in let P3 := fresh "P" in
    destruct M1 as [(C1 & L1 & P1 & _) _]; destruct M2 as [(C2 & L2 & P2 & _) _]; destruct M3 as [(C3 & L3 & P3 & _) _];
    rewrite E1 in C1, L1, P1; rewrite E2 in C2, L2, P2; rewrite E3 in C3, L3, P3; clear E1 E2 E3;
    unfold mpi_cells in C1, C2, C3;
    let B1 := fresh "B" in let B2 := fresh "B" in let B3 := fresh "B" in
    pose proof (rw_cells_bound _ _ _ _ C1) as B1; pose proof (rw_cells_bound _ _ _ _ C2) as B2; pose proof (rw_cells_bound _ _ _ _ C3) as B3;
    cbn [cells_size csize Nat.add] in B1, B2, B3; clear C1 C2 C3;
    lazymatch type of S with slots ?Q _ _ _ =>
      unfold slots in S;
      assert (QAL : Q mod 8 = 0) by lia; assert (QPOS : 0 < Q) by lia; assert (QLT : Q + 48 <= 2 ^ 64) by lia
    end;
    clear S B1 B2 B3 L1 L2 L3 P1 P2 P3.
  Ltac pr_qchk :=
    let K := fresh "KQ" in let K' := fresh "KQ" in
    zstep; if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|];
    zstep; zstep; if_cases K'; zify_cond K'; [exfalso; rewrite ?unsigned_lit in K' by lia; rewrite ?land_7_mod in K'; lia|].

  Definition pr_state (h : HST usegs L HI) (LB : list blk) (Q SP lo : Z) (m : mem) (mo : Model)
      (hk : HST usegs L HI) (LBk : list blk) (A1 : Z) (d1 : mpd) (A2 : Z) (d2 : mpd) (A3 : Z) (d3 : mpd) (mk : mem) (mok : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "(0.(5?.$59.VL,VHI,O11.O10.O>.+40.(60.O?.)+5<?:8.O=.O<.O;.O:.O9.O2.O1.)(0.(5<.O10.O9.O2.O8.O7.O6.O5.O4.O3.)(61.O?.O8.O6.O4.)))")
(* [comment removed for export] *).

  Lemma pr_state_swap12 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PQ,$9.PSP,$9.Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PA1,$9.Pd1,$28.PA2,$9.Pd2,$28.PA3,$9.Pd3,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.P,(62.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(62.R12.R11.R10.R?.R>.R=.R<.R;.R:.R7.R6.R9.R8.R5.R4.R3.R2.)")
(* [comment removed for export] *).
  Proof. intros until mok. intros (J & T & S). exact (conj J (conj (tri_swap12 _ _ _ _ _ _ _ _ _ T) (slots_swap12 _ _ _ _ S))). Qed.
  Lemma pr_state_swap13 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PQ,$9.PSP,$9.Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PA1,$9.Pd1,$28.PA2,$9.Pd2,$28.PA3,$9.Pd3,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.P,(62.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(62.R12.R11.R10.R?.R>.R=.R<.R;.R:.R5.R4.R7.R6.R9.R8.R3.R2.)")
(* [comment removed for export] *).
  Proof. intros until mok. intros (J & T & S). exact (conj J (conj (tri_swap13 _ _ _ _ _ _ _ _ _ T) (slots_swap13 _ _ _ _ S))). Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L37273016624.54L59656785403.5400000?00kS1L2HI1h2SP1a1CS1L2HI3HLS4DIMG4IMGC1h2SP2lo3MC23SLO3ACL1a1C". (* [comment removed for export] *)
  Lemma pr_Q_cr : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)PSP,$9.Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.P,(63.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(0.(47.VL,R:.R4.R8.+30.)(47.VL,R:.R5.R8.+30.))")
(* [comment removed for export] *).
  Proof.
    intros until mo. intros CTX. prctx CTX. unfold ECP_POINT_READ_STACK in SLO. split.
    - intros a Ha. destruct (QW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
    - intros a Ha. destruct (QW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L12185525866.74L29071909408.4 L29881113007.75L32979881071.75L37273016624.1000000X00d00l01601IS1L3HLS4DIMG4IMGC2SP2lo3MC23SLO3ACL1d2N1S1G1Q3MCG2QGS2SP1d1HS1Q2SP1d1HS1G2SP2lo2GS1a2Ha1C". (* [comment removed for export] *)
  Lemma pr_GR : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)PSP,$9.Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PA1,$9.Pd1,$28.PA2,$9.Pd2,$28.PA3,$9.Pd3,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.P,(63.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)P,(62.R15.R14.R12.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(34.$59.VMT,R4.R;.R14.R12.)")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX (STk & _). prctx CTX. unfold ECP_POINT_READ_STACK in SLO. flat constr:(STk) 6%nat. intros HHk SUBk PXk SOKk MIk _.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR _.
    eapply (ecp_group_at_presx usegs L); [exact GR| exact PXk| exact MI| exact MIk| | unfold pr_XO; cbn; clear - QG MCG; lia|].
    - intros a Ha. destruct (GCR a Ha) as [C|[C|(b & Hb & R)]]; [left; clear - C GS Ha SLO HLS; lia| right; left; exact C| right; right; exists b; split; [exact Hb| exact R]].
    - intros d Hd O. pose proof (grp_blocks_in usegs MT m LB G g d GR Hd O) as IN. split; [exact (SUBk _ IN)|].
      flat constr:((proj1 (Forall_forall _ _) HBR _ IN)) 4%nat. intros _ _ B3 _. cbn in B3.
      destruct (mpdr_blk_facts usegs L m LB d ltac:((let flt10 := fresh "FLt" in flat constr:(GR) 13%nat; flclear GR; intros _ _ _ _ _ _ _ MP MA MB flt10 MN _; flat constr:(flt10) 6%nat; flclear flt10; intros _ _ _ MX MY MZ); unfold grp_mpds, pt_mpds in Hd; cbn in Hd; destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption) O HBR) as (_ & N1 & _).
      unfold pr_XO. cbn. split; [pose proof (GQL d Hd O); lia|]. split; [| exact I].
      pose proof (j_blk_MC usegs L HI DIMG h LB m mo _ _ U_MUL_COUNT HH IN ltac:(lia) MC1 MC2). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac prstate STATE := pose proof STATE as (STk & (T1 & T2 & T3 & COVk & D12 & D13 & D23) & SL);
    pose proof STk as (HHk & SUBk & PXk & SOKk & MIk & MFk & HTk & CNTk & STk');
    pose proof T1 as (M1 & E1 & NS1 & FR1); pose proof T2 as (M2 & E2 & NS2 & FR2); pose proof T3 as (M3 & E3 & NS3 & FR3).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L1055347216.103 L10633144206.102L17641677310.104L19865140063.13 L20754570198.104L22286003249.101L22286004150.102L22536070416.103L30921035882.102L39298475913.106L40147640349.102L40402727242.101L43547071954.107L46284147761.107L5244266020.103 L5246359839.106 L5246360216.106 L55383275238.101L8102165997.106 00000400@00K00l01702H03\03`04U05>05I06206>06J07307\08E09W0:@S2SPS2SP2d11a2HaS1Q2SP2d11HS1Q2SP2lo2A12A22A33SPX4HSPX2QS2SLS1G2SP2d11HS1L3HLS4DIMG4IMGC1G1Q2SP2lo2A12A22A32GS3MCG2QS2QG3MCQ3MC23SLO3ACL3SPA3DHI2SL1a2HaS1L3HLS4DIMG4IMGC1G1Q2SP2lo2A12A22A32GS3MCG2QS2QG3MCQ3MC23SLO3ACL3SPA3DHI2SL1a2Ha2HdS2SPS1L2HI3HLS4DIMG4IMGC1h2SP2lo3SPX4HSPX3MC23SLO3ACL1a1CS1L3HLS4DIMG4IMGC2SP2lo2d23MC23SLO3ACL2N2S1L2SP1a2HdS1L3HLS4DIMG4IMGC2SP2lo2d13MC23SLO3ACL2B4S2SP2d12d21HS2SP2d12d31HS1L3HLS4DIMG4IMGC2SP2lo2d13MC23SLO3ACL2N1S1L3HLS4DIMG4IMGC2SP2lo2d13MC23SLO3ACL2N1S1L3HLS4DIMG4IMGC2SP2lo2d13MC23SLO3ACL2N1S1L3HLS4DIMG4IMGC1G1Q2SP2lo2A12d12A22A32GS3MCG2QS2QG3MCQ3MC23SLO3ACL3SPA3DHI2SL2APS1L3HLS4DIMG4IMGC2SP2lo2d33MC23SLO3ACL2N3". (* [comment removed for export] *)
  Lemma pr_d1_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)PSP,$9.Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PA1,$9.Pd1,$28.PA2,$9.Pd2,$28.PA3,$9.Pd3,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.PSPX,$9.P,(63.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)P,(62.R16.R15.R13.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(0.(3:.(50.R11.+40.)R3.)(3:.R3.R11.))(0.(64.$59.R6.R=.R;.)(0.(7.(1.$2.(3.R;.)$65.))(0.(1.$9.(66.R;.)R<.)(0.(67.VL,R=.R4.(23.$59.VL,VHI,R18.)R;.)(0.P,(7.(1.$2.(3.R;.)$48.))(29.(3:.(31.(;.R<.)(<.+4.(=.R<.)))R12.)(3:.R5.(;.R<.)))(0.P,(1.$2.(3.R;.)$5.)(0.(2=.(8.$9.$9.)(:.$9.$9.(;.R<.)(<.+4.(=.R<.)))R>.)(0.(3:.+1.(=.R<.))(0.(3=.=(;.R<.))(0.(3:.(31.(;.R<.)(<.+4.(=.R<.)))(52.VL,))(0.(7.(2=.(8.$9.$9.)(:.$9.$9.(;.R<.)(<.+4.(=.R<.)))R18.))(0.(29.(3:.(31.R16.+30.)(;.R<.))(3:.(31.(;.R<.)(<.+4.(=.R<.)))R16.))(0.(29.(3:.(31.R17.+<0.)(;.R<.))(3:.(31.(;.R<.)(<.+4.(=.R<.)))R17.))(0.P,(1.$2.(3.R:.)$5.)(29.(3:.(31.(;.R;.)(<.+4.(=.R;.)))(;.R=.))(3:.(31.(;.R=.)(<.+4.(=.R=.)))(;.R;.)))P,(1.$2.(3.R8.)$5.)(29.(3:.(31.(;.R9.)(<.+4.(=.R9.)))(;.R=.))(3:.(31.(;.R=.)(<.+4.(=.R=.)))(;.R9.)))))))))))(0.(47.VL,R=.R11.R<.+10.)(0.P,(1.$2.(3.R;.)$5.)(47.VL,R>.R12.(;.R<.)(<.+4.(=.R<.)))(29.(3:.(31.R<.+10.)R11.)(3:.R4.R<.))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until SPX. intros CTX STATE HSPX. prctx CTX. unfold ECP_POINT_READ_STACK in SLO. prstate STATE. pose proof alloc_ceiling_pos as ACP.
    flat constr:((pr_Q_cr _ _ _ _ _ _ _ _ _ _ CTX)) 2%nat. intros QCRlo QCR. unfold slots in SL.
    assert (BL1 : md_own d1 = LHeap -> In (md_p d1, 4 * md_n d1) LBk /\ 1 <= md_n d1 /\ 0 < md_p d1 /\ md_p d1 + 4 * md_n d1 <= alloc_ceiling /\ ~ In (md_p d1, 4 * md_n d1) LB
                           /\ (Q + 48 <= md_p d1 \/ md_p d1 + 4 * md_n d1 <= Q) /\ (G + 192 <= md_p d1 \/ md_p d1 + 4 * md_n d1 <= G)
                           /\ (md_own d2 = LHeap -> md_p d2 + 4 * md_n d2 <= md_p d1 \/ md_p d1 + 4 * md_n d1 <= md_p d2)
                           /\ (md_own d3 = LHeap -> md_p d3 + 4 * md_n d3 <= md_p d1 \/ md_p d1 + 4 * md_n d1 <= md_p d3)).
    { intros O. flat constr:((jtmp_blk usegs L HI hk LB LBk mk mok _ d1 HHk T1 O)) 5%nat. intros IN N1 P0 B4 NIN.
      refine (conj IN (conj N1 (conj P0 (conj B4 (conj NIN (conj _ (conj _ (conj _ _)))))))).
      - pose proof (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo _ _ Q 48 HHk IN NIN SUBk ltac:(lia) QCRlo ltac:(lia) ACL). lia.
      - pose proof (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo _ _ G 192 HHk IN NIN SUBk ltac:(lia) GCR ltac:(lia) ACL). lia.
      - intros O2. flat constr:((jtmp_blk usegs L HI hk LB LBk mk mok _ d2 HHk T2 O2)) 3%nat. intros IN2 N2 _. pose proof (j_blk_apart usegs L HI hk LBk mk mok _ _ _ _ HHk IN IN2 (D12 O O2) ltac:(lia) ltac:(lia)). lia.
      - intros O3. flat constr:((jtmp_blk usegs L HI hk LB LBk mk mok _ d3 HHk T3 O3)) 3%nat. intros IN3 N3 _. pose proof (j_blk_apart usegs L HI hk LBk mk mok _ _ _ _ HHk IN IN3 (D13 O O3) ltac:(lia) ltac:(lia)). lia. }
    assert (XSL : md_own d1 <> LNull -> md_p d1 + 4 * md_n d1 <= lo \/ SPX <= md_p d1).
    { intros NN. destruct (md_own d1) eqn:O; [exfalso; exact (NN eq_refl)| (flat constr:((BL1 eq_refl)) 5%nat; intros _ _ _ B4 _); left; lia| exfalso; exact (NS1 eq_refl)]. }
    refine (conj M1 (conj NS1 (conj E1 (conj _ (conj XSL (conj BL1 (conj _ (conj _ _)))))))).
    - unfold mpd_writable. rewrite E1. split; [| split; [intros a Ha Hd; apply QD; lia| intros O; (flat constr:((BL1 O)) 7%nat; intros _ _ _ _ _ AP _); lia]].
      intros a Ha. destruct (QW a ltac:(lia)) as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists b; split; [exact (SUBk _ Hb)| exact R]].
    - intros a Ha. destruct (QCRlo a ltac:(lia)) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [exact (SUBk _ Hb)| exact R]].
    - intros O a Ha. right; right. exists (md_p d1, 4 * md_n d1). split; [exact (proj1 (BL1 O))| cbn; lia].
    - clear - QS SL HSPX SLO HLS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L10095434675.127L14295038840.131L16167974640.127L16766199384.137L19013042947.127L22286003249.136L22371122749.10 L22541875066.132L22542362521.140L33554556276.127L39931152727.136L41724861450.127L43684974195.127L47185264661.129L5244266020.136 L54983669071.127L55877722379.125L57051693602.136L64908788771.5  L66543342039.143L67015967536.141L9220456473.140 00000B00O00\01L01^02R02g04;04?04Q06106C06U06c07L07^07h08E08V08a08i09RS1Q2SP2A12A22A32SLS2SP2d11A1n1HS2SP3SPX4HSPXS1L3HLS4DIMG4IMGC2SP2lo3SPX4HSPX3MC23SLO3ACL1a1CS1Q2SP2A12A22A32SLS1L3HLS4DIMG4IMGC1Q2SP2lo3MC23SLO3ACL1A3HA13HA21a2HaS1Q2A12A22A32SL1e3AQES1L3HLS4DIMG4IMGC1G1Q2SP2lo2A12A22A32GS3MCG2QS2QG3MCQ3MC23SLO3ACL3SPA3DHI2SL1a2O12O2S2SPS1Q2SP2A12A22A32SLS1L3HLS4DIMG4IMGC1G1Q2SP2lo2A12d12A22A32GS3MCG2QS2QG3MCQ3MC23SLO3ACL3SPA3DHI2SL1A3HA13HA23HA32AQS1Q2SP2A12A22A32SLS1Q2SP2A12A22A32SLS2SP2A11A1n2DaS1L3HLS4DIMG4IMGC2SP2lo2d13MC23SLO3ACL2N1S1Q2SP2A12A22A32SLS2SP1A1n1DS1L3HLS2SP2lo3MC23SLO3ACL3DHIS1Q3MCQ1A3HA13HA2S2SP2d11e1HS2SP1e1HS1L3HLS4DIMG4IMGC2SP2lo3MC23SLO3ACL1e3NE1". (* [comment removed for export] *)
  Lemma pr_step1 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)PSP,$9.Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PA1,$9.Pd1,$28.PA2,$9.Pd2,$28.PA3,$9.Pd3,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.Ph',(14.$59.VL,VHI,)PLB',(15.$16.)Pd1',$28.Pm',P,(11.&40.)(12.(11.&8.))Pmo',$13.PXC,(15.$68.)PSPX,$9.P,(63.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(62.R1<.R1;.R19.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)P,(29.(1.(15.$68.)R4.(32.$68.))(1.(15.$68.)R4.(30.(8.$9.$9.)(:.$9.$9.+5<?:8.(31.+5<?:8.+8.))(32.(8.$9.$9.)))))P,(0.(3:.(50.R18.+40.)R4.)(3:.R4.R18.))P,(24.$59.VL,VHI,R;.R:.R8.R7.)P,(64.$59.R9.R;.R:.)P,(69.R16.R14.R<.R;.)P,Pb,$16.P,(2=.$16.R1.(5:.R=.))(29.(2=.$16.R2.(5:.R17.))(7.(2=.$16.R2.R19.)))P,(2?.$59.VL,R18.R9.(6:.(8.$9.$9.)(6;.R16.)R:.)R11.R<.)P,(33.$59.VL,R=.)P,(1?.$59.R>.)P,(22.R13.R>.)P,(1.$9.(23.$59.VL,VHI,R13.)(23.$59.VL,VHI,R1=.))P,(10.(11.&40.)Lc,(11.&40.)(35.$59.R12.+5<?:8.(30.$36.(37.R1.)(32.$36.))))P,(20.$59.R12.R22.(50.R23.+40.))(62.R2:.R29.R27.R24.R23.R22.R21.R16.R15.R1>.R14.R1<.R1;.R1:.R19.R13.R12.)")
(* [comment removed for export] *).
  Proof.
    intros until SPX. intros CTX STATE HXC HSPX HH' MA' OUT' FRB' PX' SOK' MI' MF' HT' CNT' ST'. prctx CTX. unfold ECP_POINT_READ_STACK in SLO. prstate STATE.
    pose proof alloc_ceiling_pos as ACP. flat constr:(OUT') 5%nat. intros EA' NS' K1 K2 K3. pose proof SL as SL0. unfold slots in SL.
    flat constr:((pr_Q_cr _ _ _ _ _ _ _ _ _ _ CTX)) 2%nat. intros QCRlo QCR.
    flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SPX CTX STATE HSPX)) 7%nat. intros _ _ _ _ XSL BL1 _.
    assert (SUB' : forall b, In b LB -> In b LB').
    { intros b Hb. apply K2; [exact (SUBk _ Hb)|]. intros HX. exact (FR1 _ HX Hb). }
    assert (DXC : forall A n, (U_MUL_COUNT + 8 <= A \/ A + n <= U_MUL_COUNT) -> disjoint_from XC A n).
    { intros A n D. destruct HXC as [-> | ->]; cbn; [exact I| split; [lia| exact I]]. }
    assert (D1 : forall A n, (A1 + 16 <= A \/ A + n <= A1) -> (md_own d1 = LHeap -> md_p d1 + 4 * md_n d1 <= A \/ A + n <= md_p d1) -> disjoint_from (mpd_ivs d1) A n).
    { intros A n Da Db. unfold mpd_ivs. rewrite E1. cbn. split; [lia|]. destruct (md_own d1) eqn:O; cbn; [exact I| | exfalso; exact (NS1 eq_refl)]. split; [| exact I]. pose proof (Db eq_refl). lia. }
    (* [comment removed for export] *)
    assert (OTHER : forall A e, jtmp usegs LB LBk mk A e -> Q <= A -> A + 16 <= Q + 48 -> (A1 + 16 <= A \/ A + 16 <= A1) -> dis d1 e ->
              (md_own d1 = LHeap -> md_own e = LHeap -> md_p e + 4 * md_n e <= md_p d1 \/ md_p d1 + 4 * md_n d1 <= md_p e) ->
              jtmp usegs LB LB' m' A e).
    { intros A e TE HA1 HA2 HA3 DE APE. eapply (jtmp_presx usegs L); [exact TE| exact PX'| exact MIk| exact MI'| | |].
      - intros a Ha. destruct (QCR a ltac:(lia)) as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists b; split; [exact (SUBk _ Hb)| exact R]].
      - rewrite (disjoint_from_app L DIMG). split; [| apply DXC; clear - MCQ HA1 HA2; lia]. apply D1; [exact HA3|].
        intros O. flat constr:((BL1 O)) 7%nat. intros _ _ _ _ _ AQ _. lia.
      - intros OE. flat constr:((jtmp_blk usegs L HI hk LB LBk mk mok _ e HHk TE OE)) 5%nat. intros INE NE1 PE0 BE4 NINE. split; [exact INE|]. split.
        + apply K2; [exact INE|]. intros HX. flat constr:((mpd_blk_single d1 _ HX)) 3%nat. intros _ O1 E. exact (DE O1 OE (eq_sym E)).
        + rewrite (disjoint_from_app L DIMG). split; [| apply DXC; pose proof (j_blk_MC usegs L HI DIMG hk LBk mk mok _ _ U_MUL_COUNT HHk INE ltac:(lia) MC1 MC2); lia].
          pose proof (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo _ _ Q 48 HHk INE NINE SUBk ltac:(lia) QCRlo ltac:(lia) ACL) as AQE.
          apply D1; [clear - AQE HA1 HA2 SL; lia|]. intros O1. pose proof (APE O1 OE). lia. }
    unfold pr_state, tri. refine (conj _ (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ D23)))))) SL0)).
    - eapply (jst_step usegs L HI) with (SPX := SPX) (LBX := LBk); [exact STk| lia| exact HH'| exact SUB'| exact PX'| exact SUBk| | exact SOK'| exact MI'| exact MF'| exact HT'| exact CNT'| exact ST'].
      intros a Ha HC HO. unfold pr_XO in HO. cbn in HO. flat constr:(HO) 3%nat. flclear HO. intros O1 O2 _. rewrite outside_app. split.
      + unfold mpd_ivs. rewrite E1. cbn. split; [lia|]. destruct (md_own d1) eqn:OY; cbn; [exact I| | exfalso; exact (NS1 eq_refl)]. split; [| exact I].
        flat constr:((BL1 eq_refl)) 6%nat. intros IN N1 _ _ NIN _. eapply (j_out_blk usegs L HI DIMG hk LBk mk mok LB SP a); [exact HHk| exact IN| exact NIN| exact SUBk| lia| lia| exact HC].
      + destruct HXC as [-> | ->]; cbn; [exact I| exact (conj O2 I)].
    - refine (conj MA' (conj (eq_trans EA' E1) (conj NS' _))). intros b Hb HbL. destruct (FRB' b Hb) as [X|X]; [exact (FR1 _ X HbL)| exact (X (SUBk _ HbL))].
    - apply (OTHER A2 d2 T2); [lia| lia| lia| exact D12| intros O1 O2; (flat constr:((BL1 O1)) 9%nat; intros _ _ _ _ _ _ _ AP _); exact (AP O2)].
    - apply (OTHER A3 d3 T3); [lia| lia| lia| exact D13| intros O1 O3; (flat constr:((BL1 O1)) 9%nat; intros _ _ _ _ _ _ _ _ AP); exact (AP O3)].
    - intros b Hb. destruct (K1 b Hb) as [X|X]; [| right; left; exact X]. destruct (COVk b X) as [C|[C|C]]; [left; exact C| | right; right; exact C].
      right; left. rewrite (K3 b C Hb). exact C.
    - intros O1' O2 E. destruct (FRB' (md_p d1', 4 * md_n d1') ltac:(unfold mpd_blk; rewrite O1'; left; reflexivity)) as [X|X].
      + flat constr:((mpd_blk_single d1 _ X)) 3%nat. intros _ O1 EB. apply (D12 O1 O2). rewrite <- EB. exact E.
      + apply X. rewrite E. exact (proj1 (jtmp_blk usegs L HI hk LB LBk mk mok _ d2 HHk T2 O2)).
    - intros O1' O3 E. destruct (FRB' (md_p d1', 4 * md_n d1') ltac:(unfold mpd_blk; rewrite O1'; left; reflexivity)) as [X|X].
      + flat constr:((mpd_blk_single d1 _ X)) 3%nat. intros _ O1 EB. apply (D13 O1 O3). rewrite <- EB. exact E.
      + apply X. rewrite E. exact (proj1 (jtmp_blk usegs L HI hk LB LBk mk mok _ d3 HHk T3 O3)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L22019834206.110L33569284833.112L35497548825.112L41710099359.112L43674274278.112L47063237017.112L54990172890.11200000400F00J00\00n01Q01cS2SPS1Q2SP2A12A22A32SLS2SPS1Q2SP2A12A22A32SLS1Q2SP2A12A22A32SLS1L3HLS4DIMG4IMGC2SP2lo3MC23SLO3ACLS1Q2SP2A12A22A32SL". (* [comment removed for export] *)
  Lemma pr_munch1 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)PSP,$9.Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PA1,$9.Pd1,$28.PA2,$9.Pd2,$28.PA3,$9.Pd3,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.Pm',P,(11.&40.)(12.(11.&8.))Pd1',$28.PW,(15.$68.)P,(63.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)P,(62.R18.R17.R15.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(6<.R3.R7.R5.)P,(6=.$59.R8.R6.)P,(1?.$59.R7.)P,(20.$59.R8.R15.(50.R16.+40.))P,Pa,$9.P,(7.(6>.R8.R1.))(29.(0.(3:.R18.R2.)(3=.R2.(50.R19.+40.)))(0.(1.$2.(3.R12.)$5.)(0.(3:.(;.R12.)R2.)(3=.R2.(31.(;.R12.)(<.+4.(=.R12.)))))))P,(6?.R8.+5<?:8.+8.)P,(6?.R9.R1<.+30.)P,P,(1.$2.(3.R11.)$5.)(6?.R;.(;.R12.)(<.+4.(=.R12.)))P,P,(1.$2.(3.R10.)$5.)(6?.R<.(;.R11.)(<.+4.(=.R11.)))P,(64.$59.R>.R17.R=.)P,(1.$9.(66.R>.)(66.R16.))P,(1.$2.(3.R?.)(3.R17.))P,(1.$9.(;.R10.)(;.R18.))P,(1.$9.(=.R11.)(=.R19.))(62.R27.R26.R24.R21.R20.R1?.R1>.R1=.R1<.R1;.R12.R19.R18.R17.R16.R13.R14.)")
(* [comment removed for export] *).
  Proof.
    intros until W. intros CTX STATE MU WM MI' ST' HW DMC DQ DL2 DL3 MA' EA' EO' EP' EN'. prctx CTX. unfold ECP_POINT_READ_STACK in SLO. prstate STATE.
    pose proof alloc_ceiling_pos as ACP. unfold slots in SL.
    flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP - 64) CTX STATE ltac:(lia))) 7%nat. intros _ _ _ _ _ BL1 _.
    assert (BE : mpd_blk d1' = mpd_blk d1) by (unfold mpd_blk; rewrite EO', EP', EN'; reflexivity).
    unfold pr_state, tri. refine (conj _ (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ D23)))))) SL)).
    - eapply (jst_munch usegs L HI DIMG); [exact STk| exact HH| lia| exact MU| exact WM| exact MI'| exact ST'| | exact DMC| exact ACL| lia| exact DHI| exact HTOP| exact MC2].
      intros a NO. destruct (HW a NO) as [X|[O1 X]]; [left; exact X| right]. flat constr:((BL1 O1)) 6%nat. intros IN _ _ _ NIN _.
      exists (md_p d1), (4 * md_n d1). exact (conj IN (conj NIN X)).
    - refine (conj MA' (conj (eq_trans EA' E1) (conj _ _))); [rewrite EO'; exact NS1| rewrite BE; exact FR1].
    - refine (conj _ (conj E2 (conj NS2 FR2))). eapply mpd_at_munch_any; [exact M2| exact MU| exact WM| rewrite E2; eapply disjoint_from_sub; [exact DQ| lia| lia]|].
      intros NN. destruct (md_own d2) eqn:O2; [exfalso; exact (NN eq_refl)| exact (DL2 eq_refl)| exfalso; exact (NS2 eq_refl)].
    - refine (conj _ (conj E3 (conj NS3 FR3))). eapply mpd_at_munch_any; [exact M3| exact MU| exact WM| rewrite E3; eapply disjoint_from_sub; [exact DQ| lia| lia]|].
      intros NN. destruct (md_own d3) eqn:O3; [exfalso; exact (NN eq_refl)| exact (DL3 eq_refl)| exfalso; exact (NS3 eq_refl)].
    - rewrite BE. exact COVk.
    - unfold dis. rewrite EO', EP', EN'. exact D12.
    - unfold dis. rewrite EO', EP', EN'. exact D13.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma pr_post : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)PSP,$9.Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PdX,$28.PdY,$28.PdZ,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.P,(63.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(62.R12.R11.R?.R<.R;.R:.R9.R8.R7.R?.R6.(31.R?.+10.)R5.(31.R?.+20.)R4.R3.R2.)Zp',$17.(70.R7.R6.R5.)(0.(1?.$59.R5.)(0.(22.R;.R4.)(0.(1.$9.(23.$59.VL,VHI,R:.)(23.$59.VL,VHI,R14.))(0.(24.$59.VL,VHI,R:.R9.R5.R4.)(0.(25.$59.R5.R9.R11.R1.)(0.(26.R1.)(0.(27.$28.Ld,$28.(29.(1.$9.(2:.R1.)+1.)(1.$9.(2:.R1.)-1.))(2;.R1.))(0.(2<.R1.)(0.Pb,$16.P,(2=.$16.R1.R14.)(2=.$16.R2.R;.)(0.Pb,$16.P,(2=.$16.R1.R:.)(29.(2=.$16.R2.R15.)(2=.$16.R2.(2>.R3.)))(0.Pb,$16.P,(2=.$16.R1.(2>.R2.))(7.(2=.$16.R2.R15.))(0.(2?.$59.VL,R13.R>.(30.(8.$9.$9.)(:.$9.$9.R11.(31.R11.+30.))(30.(8.$9.$9.)(:.$9.$9.+5<?:8.(31.+5<?:8.+8.))(32.(8.$9.$9.))))R<.R5.)(0.(33.$59.VL,R5.)(0.(34.$59.VMT,R5.R9.R12.R10.)(0.(10.(11.&40.)Lc,(11.&40.)(35.$59.R6.+5<?:8.(30.$36.(37.R1.)(32.$36.))))(7.(1.$9.(;.(4.(38.R10.)))=)))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX STATE. pose proof (pr_GR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE) as GRk. prstate STATE. cbv zeta.
    refine (conj MIk (conj MFk (conj HTk (conj HHk _)))).
    split. { unfold ecp_point_at. cbn [pt_X pt_Y pt_Z]. exact (conj E1 (conj E2 (conj E3 (conj (proj1 M1) (conj (proj1 M2) (proj1 M3)))))). }
    split. { unfold pt_freeable, pt_mpds. cbn [pt_X pt_Y pt_Z]. constructor; [exact NS1| constructor; [exact NS2| constructor; [exact NS3| constructor]]]. }
    split. { unfold pt_mpds. cbn [pt_X pt_Y pt_Z]. constructor; [exact (proj2 M1)| constructor; [exact (proj2 M2)| constructor; [exact (proj2 M3)| constructor]]]. }
    split; [exact (conj D12 (conj D13 D23))|].
    split; [exact SUBk|].
    split. { intros b Hb. unfold pt_blocks, pt_mpds. cbn [pt_X pt_Y pt_Z flat_map]. rewrite app_nil_r, !in_app_iff. destruct (COVk b Hb) as [C|[C|[C|C]]]; tauto. }
    split. { intros b Hb. unfold pt_blocks, pt_mpds in Hb. cbn [pt_X pt_Y pt_Z flat_map] in Hb. rewrite app_nil_r, !in_app_iff in Hb.
             destruct Hb as [C|[C|C]]; [exact (FR1 _ C)| exact (FR2 _ C)| exact (FR3 _ C)]. }
    prctx CTX. exact (conj PXk (conj SOKk (conj GRk (conj CNTk GXN)))).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac prr := first
    [ match goal with H : - 2 ^ 31 < ?x <= 0 |- - 2 ^ 31 < ?x <= 0 => exact H end
    | plia
    | match goal with H : lset_R _ _ _ ?x _ |- _ < ?x <= _ => destruct H as [[(Er & _)|(Er & _)] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia end
    | match goal with H : (?x = 0 \/ ?x = MBEDTLS_ERR_MPI_ALLOC_FAILED) |- _ < ?x <= _ => destruct H as [Er|Er]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia end
    | match goal with H : _ /\ (?x = 0 \/ ?x = MBEDTLS_ERR_MPI_ALLOC_FAILED) /\ _ |- _ < ?x <= _ => destruct (proj1 (proj2 H)) as [Er|Er]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia end
    | match goal with H : context [?x = 0 \/ ?x = MBEDTLS_ERR_MPI_ALLOC_FAILED] |- _ < ?x <= _ => decompose [and] H; match goal with H' : x = 0 \/ x = MBEDTLS_ERR_MPI_ALLOC_FAILED |- _ => destruct H' as [Er|Er]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia end end
    | lia
    | match goal with |- ?g => idtac "PRRFAIL" g; fail end ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L10081841430.120L10312886093.120L11379704105.123L12103661095.123L13642019862.120L15466341142.120L46225601430.120L49786828438.120L51601712534.120L6503841302.120 L66651531311.124L68285471708.12300000500:00?00D00I00N00S00X00]00b01801=S3spvS3spvS3spvS3spvS3spvS3spvS3spvS3spvS3spvS3spvS1L3HLS3spv2lo3SLO3SPBS3spv". (* [comment removed for export] *)
  Lemma pr_exit : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Prae,(11.&40.)Pspv,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Ps0e,(11.&40.)Ps1e,(11.&40.)Ps2e,(11.&40.)Ps3e,(11.&40.)Ps4e,(11.&40.)Ps5e,(11.&40.)Ps6e,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pra0,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps0c,(11.&40.)Ps1c,(11.&40.)Ps2c,(11.&40.)Ps3c,(11.&40.)Ps4c,(11.&40.)Ps5c,(11.&40.)Ps6c,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)PF,(40.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)Plo,$9.Pp0,$17.Pbs,(15.(11.&8.))Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PdX,$28.PdY,$28.PdZ,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.Pr,$9.P,(63.R11.R10.R?.R>.R=.R<.(21.&40.R3:.)R;.R13.R12.)P,(62.R12.R11.R?.(21.&40.R3;.)R<.R14.R13.R9.R8.R?.R7.(31.R?.+10.)R6.(31.R?.+20.)R5.R4.R3.)P,(35.$59.R5.(31.(21.&40.R3<.)-40.)(71.R33.R34.R35.R36.R37.R38.R39.R3=.))P,(0.(3=.(3>.(3?.+2.+1?.))R4.)(3:.R4.=))(56.$59.R6.(57.$59.VL,VHI,VMT,R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R19.R18.R15.R14.R13.R11.R12.R>.R=.+5<?:8.R?.R17.R16.)(19.(1:.R2?.(1;.&40.(31.(21.&40.R3>.)-40.))R3=.R3<.R2>.R2=.R2<.R2;.R2:.(1;.&40.R5.)R24.R23.R22.R21.R20.R1?.R1>.R29.R28.R27.R26.R25.R34.R33.R32.R31.R30.R1=.R1<.R1;.R1:.)R19.(1;.&40.+389;0.)R18.(1=.(11.&40.))R7.(1>.$59.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros CTX STATE FR Hr. prctx CTX. unfold ECP_POINT_READ_STACK in SLO. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (pr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE) as PO. cbv zeta in PO.
    flat constr:(PO) 16%nat. flclear PO. intros MIk MFk HTk HHk PT' PF' PS' PD' SUB' COV' FRS' PX' SOK' GR' (ck & CNTk) GXN'.
    flat constr:(STATE) 2%nat. intros FLt1 _. flat constr:(FLt1) 9%nat. flclear FLt1. intros _ _ _ _ _ _ _ _ STk'. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in STk' by lia.
    pose proof (heap_mok _ _ HI _ _ _ _ HHk) as MK.
    unfold pr_regs in FR.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR STk' (bv_unsigned spv). zstep.
    try (replace (bv_unsigned spv + -64 + 64) with (bv_unsigned spv) by lia; rewrite (Z_to_bv_bv_unsigned spv)). zstep.
    apply aevtM_done. unfold ecp_point_read_post.
    flexi 14%nat. exists mk, mok, hk, LBk, (mkPT dX dY dZ), r, ck.
    split; [reflexivity|]. split; [exact MIk|]. split; [exact STk'|]. split; [exact MFk|]. split; [exact HTk|]. split; [exact HHk|].
    split; [exact PT'|]. split; [exact PF'|]. split; [exact PS'|]. split; [exact PD'|]. split; [exact SUB'|]. split; [exact COV'|]. split; [exact FRS'|].
    split; [exact PX'|]. split; [exact SOK'|]. split; [exact GR'|]. split; [exact CNTk|]. split; [intros E0; exfalso; exact (GXN' E0)| exact Hr].
  all: match goal with |- ?gg => idtac "EXITLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L36178624341.24L36955947269.2400000D00SS1A2bs1i1k2Hi2Hk3HikS2bs1i1k2Hi3Hik". (* [comment removed for export] *)
  Lemma bytes_at_sub : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Pm,P,(11.&40.)(12.(11.&8.))PA,$9.Pbs,(15.(11.&8.))Pi,$9.Pk,$9.P,(4>.$59.R5.R4.R3.)P,(3:.=R3.)P,(3:.=R3.)P,(3:.(31.R5.R4.)(3;.(3<.(11.&8.)R6.)))(0.(4>.$59.R9.(31.R8.R6.)(72.(11.&8.)(73.R5.)(74.(11.&8.)(73.R6.)R7.)))(1.$75.(3<.(11.&8.)(72.(11.&8.)(73.R5.)(74.(11.&8.)(73.R6.)R7.)))(73.R5.)))")
(* [comment removed for export] *).
  Proof.
    intros m A bs i k H Hi Hk Hik. split; [| rewrite firstn_length, skipn_length; lia].
    rewrite <- (firstn_skipn (Z.to_nat i) bs) in H. apply bytes_at_app in H. flat constr:(H) 2%nat. flclear H. intros _ H. rewrite firstn_length in H.
    replace (A + Z.of_nat (Nat.min (Z.to_nat i) (length bs))) with (A + i) in H by lia.
    rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) bs)) in H. apply bytes_at_app in H. exact (proj1 H).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L13270750757.10L22772968623.69L24093040976.69L26487227051.69L31240222562.69L47061501326.69L52255202498.69L58720335279.69L59097396139.6900000F00L00R00X00^01A01G01M01SS1Q2SP2lo2QS1A3HA13HA2S1Q2SPS1Q2SPS1Q2SPS1Q2SPS1L3HLS4DIMG4IMGC2SP2lo3MC23SLO3ACLS1Q2SPS1Q2SPS1Q2SP". (* [comment removed for export] *)
  Lemma pr_start : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)PSP,$9.Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Pm1,P,(11.&40.)(12.(11.&8.))Pp,$17.P,(63.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(25.$59.R5.R<.R:.R2.)P,(27.$28.Ld,$28.(1.$2.(3.R1.)$48.)(2;.R3.))P,(27.$28.Ld,$28.(29.(1.$9.(2:.R1.)+1.)(1.$9.(2:.R1.)-1.))(2;.R4.))P,(6<.(30.(8.$9.$9.)(:.$9.$9.R9.R:.)(32.(8.$9.$9.)))R8.R6.)P,(6=.$59.R9.R7.)P,(1?.$59.R8.)P,(20.$59.R9.R<.(50.R=.+40.))(62.R14.R13.R11.R>.R=.R<.R;.R14.R13.R11.(4.R9.)(31.R11.+10.)(6.R9.)(31.R11.+20.)(>.R9.)R:.R;.)")
(* [comment removed for export] *).
  Proof.
    intros until p. intros CTX PT PN PS MU WM MI1 ST1. prctx CTX. unfold ECP_POINT_READ_STACK in SLO. pose proof alloc_ceiling_pos as ACP.
    flat constr:(PT) 6%nat. flclear PT. intros EX EY EZ MX MY MZ.
    assert (ON : forall d, In d (pt_mpds p) -> md_own d = LNull) by (intros d Hd; exact (proj1 (Forall_forall _ _) PN _ Hd)).
    assert (SG : forall d, In d (pt_mpds p) -> md_sg d = 1 \/ md_sg d = -1) by (intros d Hd; exact (proj1 (Forall_forall _ _) PS _ Hd)).
    assert (TMP : forall d A, In d (pt_mpds p) -> mpdr_at usegs m LB d -> md_addr d = A -> Q <= A -> A + 16 <= Q + 48 -> jtmp usegs LB LB m1 A d).
    { intros d A Hd MD EA HA1 HA2. pose proof (ON d Hd) as O. split; [| split; [exact EA| split; [rewrite O; discriminate| unfold mpd_blk; rewrite O; intros b []]]].
      eapply mpd_at_munch_any; [exact (conj MD (SG d Hd))| exact MU| exact WM| rewrite EA; cbn; clear - QS HA1 HA2 SLO HLS; lia| intros NN; exfalso; exact (NN O)]. }
    split; [| split; [| unfold slots; lia]].
    - eapply (jst_prefix usegs L HI); [exact HH| exact MU| exact WM| exact MI1| exact SOK| exact CNT| exact MC2| exact DHI| exact ACL| lia| exact HTOP| exact ST1].
    - split; [apply (TMP (pt_X p) Q ltac:(cbn; auto) MX EX); lia|]. split; [apply (TMP (pt_Y p) (Q + 16) ltac:(cbn; auto) MY EY); lia|]. split; [apply (TMP (pt_Z p) (Q + 32) ltac:(cbn; auto 6) MZ EZ); lia|].
      split; [intros b Hb; left; exact Hb|].
      unfold dis. rewrite (ON _ ltac:(cbn; auto)), (ON (pt_Y p) ltac:(cbn; auto)). (flsplit; repeat split); intros; discriminate.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L10081841430.97 L10312886093.97 L12105755325.97 L13642019862.97 L15466341142.97 L22706553362.99 L25375923494.6  L26281077033.97 L3820768330.97  L41598391688.102L46225601430.97 L49786828438.97 L51189831868.6  L51601712534.97 L54391891673.98 L6503841302.97  L66651498924.98 L68295952198.97 00000500:00?00D00I00f01301O01Y01l02102602C02H02d02i03;03@S3spvS3spvS3spvS3spvS3spvS1L4DIMG4IMGC3spv2lo3ACL1a2HaS3spv1Q2lo2QSS1L4DIMG4IMGC3spv2lo3MC23ACLS1L2lo3ACLS1L3spv2lo3ACL1d2B4S3spvS3spvS3spv1G2lo2GSS3spvS1L2HI3spv1h2lo2bs4HTOP1a2NOS3spvS1L3HLS3spv2lo3SLOS3spv". (* [comment removed for export] *)
  Lemma pr_exit_prefix : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Prae,(11.&40.)Pspv,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Ps0e,(11.&40.)Ps1e,(11.&40.)Ps2e,(11.&40.)Ps3e,(11.&40.)Ps4e,(11.&40.)Ps5e,(11.&40.)Ps6e,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pra0,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps0c,(11.&40.)Ps1c,(11.&40.)Ps2c,(11.&40.)Ps3c,(11.&40.)Ps4c,(11.&40.)Ps5c,(11.&40.)Ps6c,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)PF,(40.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pp,$17.Pcnt,(11.&40.)Plo,$9.Pm1,P,(11.&40.)(12.(11.&8.))Pbs,(15.(11.&8.))Pr,$9.P,P,(1.(11.&40.)(1;.&40.R1.)(1;.&40.$39.))(3:.+1.(3;.(3<.(11.&8.)R3.)))P,(0.(3=.(3>.(3?.+2.+1?.))R2.)(3:.R2.=))P,(24.$59.VL,VHI,R=.R<.R?.R>.)P,(34.$59.VMT,R10.R=.R<.R:.)P,(47.VL,R>.R8.R=.+<0.)P,(29.(3:.(31.R>.+<0.)R9.)(3:.(21.&40.R39.)R>.))P,(25.$59.R13.R10.R>.R<.)P,(27.$28.Ld,$28.(1.$2.(3.R1.)$48.)(2;.R=.))P,(27.$28.Ld,$28.(29.(1.$9.(2:.R1.)+1.)(1.$9.(2:.R1.)-1.))(2;.R>.))P,(29.(3:.(31.R11.+30.)R=.)(3:.(21.&40.R3=.)R11.))P,(35.$59.R17.+5<?:8.(30.$36.(37.R?.)(32.$36.)))P,(3:.(31.+5<?:8.+8.)(4;.VL,))P,(3:.R10.(50.(50.(21.&40.R40.)$5=.)(51.VL,)))P,(3:.(52.VL,)R11.)P,(3:.(21.&40.R42.)(23.$59.VL,VHI,R19.))P,(3:.(4;.VL,)(52.VL,))P,(1?.$59.R1=.)P,(33.$59.VL,R1>.)P,(6<.(30.(8.$9.$9.)(:.$9.$9.R16.(21.&40.R46.))(32.(8.$9.$9.)))R1?.R15.)P,(6=.$59.R20.R16.)P,(1?.$59.R17.)P,(20.$59.R18.R19.(31.(21.&40.R49.)-40.))P,(35.$59.R19.(31.(21.&40.R4:.)-40.)(71.R41.R42.R43.R44.R45.R46.R47.R4;.))(56.$59.R23.(57.$59.VL,VHI,VMT,R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R26.R25.R22.R21.R20.R1>.R1?.R1=.R19.+5<?:8.R1;.R24.R23.)(19.(1:.R3<.(1;.&40.(31.(21.&40.R4;.)-40.))R4:.R49.R3;.R3:.R39.R38.R37.(1;.&40.R18.)R31.R30.R2?.R2>.R2=.R2<.R2;.R36.R35.R34.R33.R32.R41.R40.R3?.R3>.R3=.R2:.R29.R28.R27.)R26.(1;.&40.+389;0.)R25.(1=.(11.&40.))R1:.(1>.$59.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros HRF Hr HH GR GCR GS PT PN PS QS CNT MC2 SLO ACL HTOP DHI MI SOK MU WM MI1 ST1 FR. unfold ECP_POINT_READ_STACK in SLO. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    assert (ON : forall d, In d (pt_mpds p) -> md_own d = LNull) by (intros d Hd; exact (proj1 (Forall_forall _ _) PN _ Hd)).
    unfold pr_regs in FR.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST1 (bv_unsigned spv). zstep.
    try (replace (bv_unsigned spv + -64 + 64) with (bv_unsigned spv) by lia; rewrite (Z_to_bv_bv_unsigned spv)). zstep.
    apply aevtM_done. unfold ecp_point_read_post.
    flexi 14%nat. exists m1, mo, h, LB, p, r, cnt.
    split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [apply mo_frame_refl|]. split; [reflexivity|]. split; [exact HH1|].
    split. { eapply ecp_point_at_munch; [exact PT| exact MU| exact WM| exact MI| exact MI1| cbn; clear - QS SLO; lia| intros d Hd O; exfalso; pose proof (ON d Hd); congruence]. }
    split. { unfold pt_freeable. apply Forall_forall. intros d Hd. unfold mpd_freeable. rewrite (ON d Hd). discriminate. }
    split; [exact PS|].
    split. { flat constr:(PT) 4%nat. flclear PT. intros EX EY EZ _. unfold pt_dis. rewrite (ON (pt_X p) ltac:(cbn; auto)), (ON (pt_Y p) ltac:(cbn; auto)). (flsplit; repeat split); intros; discriminate. }
    split; [intros b Hb; exact Hb|]. split; [intros b Hb; left; exact Hb|].
    split. { intros b Hb. unfold pt_blocks in Hb. apply in_flat_map in Hb. flat constr:(Hb) 3%nat. flclear Hb. intros d Hd Hb. unfold mpd_blk in Hb. rewrite (ON d Hd) in Hb. destruct Hb. }
    split; [eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia]|].
    split; [eapply statics_ok_munch; [exact SOK| exact MU| intros a Ha _; cbn; lia]|].
    split. { eapply ecp_group_at_munch; [exact GR| exact MU| exact WM| exact MI| exact MI1| cbn; clear - GS SLO; lia|].
      intros d Hd O. pose proof (grp_blocks_in usegs MT m LB G g d GR Hd O) as IN. flat constr:((proj1 (Forall_forall _ _) HBR _ IN)) 5%nat. intros _ _ _ B4 _. cbn in B4. cbn. lia. }
    split; [eapply rw_cells_transport; [exact CNT| exact MU| exact WM| cbn; lia]|].
    split; [intros _; exact (conj eq_refl (conj eq_refl HRF))| exact Hr].
  all: match goal with |- ?gg => idtac "PEXLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L14929719110.117L40147641242.115L5246360089.116 L63887036889.115L7194065543.6   00000900L00V00_012S2SP2d11HS1L2SP3MC13MC21a2HaS2SP2d12N1S2SP1a2HaS1Q2A12A22A33MCQ2SL". (* [comment removed for export] *)
  Lemma pr_step0 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)PSP,$9.Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PA1,$9.Pd1,$28.PA2,$9.Pd2,$28.PA3,$9.Pd3,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.Ph',(14.$59.VL,VHI,)PLB',(15.$16.)Pd1',$28.Pm',P,(11.&40.)(12.(11.&8.))Pmo',$13.PSPX,$9.P,(63.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)P,(62.R1;.R1:.R18.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(0.(3:.(50.R16.+40.)R3.)(3:.R3.R16.))P,(24.$59.VL,VHI,R9.R8.R6.R5.)P,(64.$59.R7.R9.R8.)P,(69.R14.R12.R:.R9.)P,Pb,$16.P,(2=.$16.R1.(5:.R;.))(29.(2=.$16.R2.(5:.R15.))(7.(2=.$16.R2.R17.)))P,(2?.$59.VL,R16.R8.(6;.R14.)R?.R:.)P,(33.$59.VL,R;.)P,(1?.$59.R<.)P,(22.R11.R<.)P,(1.$9.(23.$59.VL,VHI,R11.)(23.$59.VL,VHI,R1;.))P,(20.$59.R?.R1?.(50.R20.+40.))(62.R27.R26.R24.R21.R20.R1?.R1>.R13.R12.R1;.R11.R19.R18.R17.R16.R10.R?.)")
(* [comment removed for export] *).
  Proof.
    intros until SPX. intros CTX STATE HSPX HH' MA' OUT' FRB' PX' SOK' MI' MF' HT' ST'. pose proof CTX as CTX0. prctx CTX. prstate STATE. unfold slots in SL.
    flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SPX CTX STATE HSPX)) 7%nat. intros _ _ _ _ _ BL1 _.
    flat constr:(CNTk) 2%nat. intros ck CNTk0.
    assert (CNT' : exists c, rw_cells usegs m' U_MUL_COUNT [C8 c]).
    { exists ck. eapply heap_presx_rw_cells; [exact PX'| exact CNTk0| cbn; intros a Ha; right; left; split; [lia| apply MCS; lia]|].
      cbn [cells_size csize Nat.add]. unfold mpd_ivs. rewrite E1. cbn. split; [clear - MCQ SL; lia|].
      destruct (md_own d1) eqn:O; cbn; [exact I| | exfalso; exact (NS1 eq_refl)]. split; [| exact I].
      flat constr:((BL1 eq_refl)) 3%nat. intros IN N1 _. pose proof (j_blk_MC usegs L HI DIMG hk LBk mk mok _ _ U_MUL_COUNT HHk IN ltac:(lia) MC1 MC2). lia. }
    eapply pr_step1 with (XC := []); [exact CTX0| exact STATE| left; reflexivity| exact HSPX| exact HH'| exact MA'| exact OUT'| exact FRB'| rewrite app_nil_r; exact PX'| exact SOK'| exact MI'| exact MF'| exact HT'| exact CNT'| exact ST'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L11380053673.177L3058247556.141 L3064753839.177 L30985055127.166L30987166995.146L36568972463.179L39024900934.7  L41707990985.146L46510687994.146L46510688493.9  L51060400285.179L56754567950.11 L6699899625.7   00000900B00K01>02102?02L02U02j02k03R04504CS3RET3spvS3RET3spvS3RET3spvS1L3HLS4DIMG4IMGC2lo3RET3spv2HR3MC23SLO3ACL3SPU3SPBS1L3HLS4DIMG4IMGC2lo3RET3spv2HR3MC23SLO3ACL3SPU3SPBS3RET3spv1a2HaS3spv3SPA3SPBS3RET3spvS1L2HI1h3RET3spv4HTOPFS1L3HLS2lo2d13RET3spv2HR3SLO3ACL3SPB2B4S1L3HLS1Q2lo2A12A22A33spv2QS3SLO2SLS1L2lo3spv3SLO". (* [comment removed for export] *)
  Lemma pr_call_lset : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)Plo,$9.Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PA1,$9.Pd1,$28.PA2,$9.Pd2,$28.PA3,$9.Pd3,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.Pz,$9.PRET,$9.Pspv,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps0,(11.&40.)Ps1,(11.&40.)Pa0,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Ps2,(11.&40.)Ps3,(11.&40.)Ps4,(11.&40.)Ps5,(11.&40.)Ps6,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)Ps6e,(11.&40.)Ps5e,(11.&40.)Ps4e,(11.&40.)Ps3e,(11.&40.)Ps2e,(11.&40.)Ps1e,(11.&40.)Ps0e,(11.&40.)Prae,(11.&40.)PF,(40.&5.(11.&40.))Pfc,(11.&20.)PQ',P,$?.SpP,(63.R3>.R3=.R3<.R3;.R3:.R39.(21.&40.R29.)R38.R37.R36.)P,(62.R3?.R3>.R3<.(21.&40.R2:.)R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.)P,(35.$59.R2?.(31.(21.&40.R2;.)-40.)(71.R=.R<.R;.R:.R9.R8.R7.R6.))P,(0.(3:.(3>.(3?.+2.+1?.))R2>.)(3=.R2>.(3?.+2.+1?.)))P,(0.(3:.=R2>.)(3=.R2>.(3?.+2.+40.)))P,(1.$9.(53.R2?.+2.)=)P,(1.(11.&40.)R2=.(1;.&40.(54.VL,)))P,(1.(11.&40.)R28.(1;.&40.R3:.))P,(1.(11.&40.)R28.(1;.&40.R33.))P,Pm',P,(11.&40.)(12.(11.&8.))Pmo',$13.Ph',(14.$59.VL,VHI,)PLB',(15.$16.)Pd1',$28.Pr,$9.Pt0',(11.&40.)Pt1',(11.&40.)Pt2',(11.&40.)Pa1',(11.&40.)Pa2',(11.&40.)Pa3',(11.&40.)Pa4',(11.&40.)Pa5',(11.&40.)Pa6',(11.&40.)Pa7',(11.&40.)Pt3',(11.&40.)Pt4',(11.&40.)Pt5',(11.&40.)Pt6',(11.&40.)P,(62.R5;.R5:.R58.(21.&40.R46.)R55.R54.R53.R12.R11.R50.R10.R4>.R4=.R4<.R4;.R14.R13.)P,(35.$59.R15.(31.(21.&40.R47.)-40.)(71.R29.R28.R27.R26.R25.R24.R23.R22.))P,(76.R4:.R51.R53.R11.R12.)(56.$59.R16.R21.(19.(1:.(1;.&40.R4:.)(1;.&40.(31.(21.&40.R49.)-40.))R48.R47.R11.R10.R?.R43.R42.(1;.&40.R12.)R>.R=.R<.R;.R:.R9.R8.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R7.R6.R5.R4.)R23.(1;.&40.R4:.)R22.(1=.(11.&40.))R17.(1>.$59.)))(56.$59.R36.R;.(19.(1:.(1;.&40.R34.)(1;.&40.(31.(21.&40.R33.)-40.))R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R=.(1;.&40.+1?808.)R<.(1=.(11.&40.))R37.(1>.$59.)))")
(* [comment removed for export] *).
  Proof.
    intros until Q'. intros CTX STATE FR HZ HR HRE TP -> -> K. pose proof CTX as CTX0. prctx CTX. unfold ECP_POINT_READ_STACK in SLO. prstate STATE. unfold slots in SL.
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned spv - 64) CTX STATE ltac:(lia))) 7%nat. intros _ _ _ XW1 XSL1 BL1 _.
    pose proof (heap_mok _ _ HI _ _ _ _ HHk) as MK.
    pose proof HLSET as SLS. unfold mpi_lset_stmt in SLS.
    eapply aevtM_cut.
    { eapply SLS with (lo := lo) (h := hk) (LB := LBk) (dX := d1) (z := z); rewrite ?(unsigned_lit (bv_unsigned spv + -64)), ?HTk by lia;
        first [ exact HHk | exact M1 | exact NS1 | exact HZ | exact TP | exact MIk | exact SOKk | exact CA | exact ACL | exact DHI | reflexivity | rewrite E1; reflexivity
              | match goal with |- mpd_writable _ _ _ _ _ => replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) by lia; exact XW1 end
              | match goal with |- stk _ _ _ _ => replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) by lia; exact STk' end
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SLS. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' mo2 h' LB' d1' r E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned spv + -64)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI' ST' MF' HT' HH' MA' OUT' PX' SOK' RR'.
    rewrite (ret_pc_even RET HR HRE). flat constr:(RR') 3%nat. intros _ EA' FRB'.
    eapply K; [| | exact RR'].
    - eapply pr_step0 with (SPX := bv_unsigned spv - 64); [exact CTX0| exact STATE| lia| exact HH'| exact MA'| exact OUT'| exact FRB'| replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) by lia; exact PX'| exact SOK'| exact MI'| exact MF'| exact HT'| replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) by lia; exact ST'].
    - eapply heap_presx_rw_cells; [exact PX'| exact FR| cbn; intros a Ha; left; lia|]. unfold mpd_ivs. rewrite E1. cbn. split; [clear - QS SL SLO HLS; lia|].
      destruct (md_own d1) eqn:O; cbn; [exact I| | exfalso; exact (NS1 eq_refl)]. split; [| exact I]. flat constr:((BL1 eq_refl)) 5%nat. intros _ _ _ B4 _. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac post_binop PO m' mo' h' LB' d' r :=
    let E := fresh "E" in
    (flat constr:(PO) 22%nat; flclear PO; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' mo' h' LB' d' r E PO); injection E as -> ->.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0@L10081841430.163L10312886093.163L11386002866.163L12105755324.166L13642019862.163L1386329760.151 L13942841079.132L15466341142.163L16075584458.103L242566168.213  L246904607.156  L246904734.132  L25343914833.167L26126801138.163L26132747253.199L29430653417.201L42638750385.132L46225601430.163L48191452659.203L49786828438.163L51601712534.163L53093827378.108L59427867805.127L61274419311.156L61274419438.132L61287121768.213L61486691409.167L64313969831.132L64313969956.108L6503841302.163 L66649088528.167L6699898110.167 L67725092320.201L68295952199.166R12257210954.132R19515183263.156R37506282132.213R52772328477.10800000B00T00f01801J01K01\01n01o02A02P02\03003B03T03l04;04M04g05905K05W05X05g06306E06W06f07207D07g08B08X08j08k08l08m096S3rae3spv2bs2r12r2S3rae3spv2bs2r12r2S3rae3spv2bs2r12r2S3rae3spv2bs2r12r2S3rae3spv2bs2r12r2FS3rae3spv1Q2bs2r1S3rae3spv2bs2r12r2FS3rae3spv2bs2r12r2S3rae3spv2bs2r1S3rae3spv2bsS3rae3spv1Q2bs2r12r2S3rae3spv2bs2r12r2S3rae3spv2bs2r12r2S3rae3spv2lo2bs2r12r22S0S3rae3spv2bs2r1S3rae3spv2bs2r12r2S3rae3spv2lo2bs2r12r21a2HaS3rae3spv2bs2r12r2S3rae3spv2bs2r12r2S3rae3spv2bsFS3rae3spv2bs2r1S3rae3spv2bsS3rae3spv2bs2r12r2S3rae3spv2bs2r12r2S3rae3spv2bs2r1S3rae3spv2bsS3rae3spv2bs2r12r2S1L3HLS3rae3spv2lo2bs3SLO3SPB2r12r2S1L3rae3spv2lo2bs3SLO2r12r2S3rae3spv2bs3SPU2r12r2S3rae3spv2bs2r12r2FFFS3rae3spv". (* [comment removed for export] *)
  Lemma pr_zero : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Prae,(11.&40.)Pspv,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Ps0e,(11.&40.)Ps1e,(11.&40.)Ps2e,(11.&40.)Ps3e,(11.&40.)Ps4e,(11.&40.)Ps5e,(11.&40.)Ps6e,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pra0,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps2c,(11.&40.)Ps3c,(11.&40.)Ps4c,(11.&40.)Ps5c,(11.&40.)Ps6c,(11.&40.)Pa0,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)PF,(40.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.Pg,$41.Pcnt,(11.&40.)Plo,$9.Pbs,(15.(11.&8.))Pp0,$17.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PdX,$28.PdY,$28.PdZ,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.P,(63.R10.R?.R>.R=.R<.R;.(21.&40.R38.)R:.R12.R11.)P,(62.R11.R10.R>.(21.&40.R39.)R;.R13.R12.R8.R7.R>.R6.(31.R>.+10.)R5.(31.R>.+20.)R4.R3.R2.)P,(35.$59.R4.(31.(21.&40.R3:.)-40.)(71.R31.R32.R33.R34.R35.R36.R37.R3;.))P,(1.(11.&40.)R39.(1;.&40.(54.VL,)))P,(1.$9.(53.(21.&40.R3=.)+2.)=)(56.$59.R6.(57.$59.VL,VHI,VMT,R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R19.R18.R15.R14.R13.R11.R12.R=.R>.+5<?:8.R?.R17.R16.)(19.(1:.R2>.(1;.&40.(31.(21.&40.R3=.)-40.))R3<.R3;.R2=.R2<.R2;.(1;.&40.R12.)(1;.&40.(3;.(3<.(11.&8.)R>.)))R25.R24.R23.R22.R21.R20.R1?.R1>.R2:.R29.R28.R27.R26.R33.R32.R31.R30.R2?.R1=.R1<.R1;.R1:.)R19.(1;.&40.+388?4.)R18.(1=.(11.&40.))R7.(1>.$59.)))")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX STATE FR TP RAE. pose proof CTX as CTX0. prctx CTX. unfold ECP_POINT_READ_STACK in SLO.
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(STATE) 2%nat. intros (HHk & _) _. pose proof (heap_mok _ _ HI _ _ _ _ HHk) as MK.
    unfold pr_regs in FR.
    zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) zstep. zstep. eapply pr_exit; [exact CTX0| exact STATE| exact FR| prr]. }
    (* [comment removed for export] *)
    pr_qfacts STATE. pr_qchk.
    zstep. zstep. zstep.
    eapply pr_call_lset with (z := 1); [exact CTX0| exact STATE| exact FR| lia| lia| reflexivity| exact TP| reflexivity| reflexivity|].
    clear MK FR. intros m1 mo1 h1 LB1 dX1 r1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? STATE1 FR RR1. flat constr:(STATE1) 2%nat. intros (HH1 & _) _. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    unfold pr_regs in FR.
    zstep. if_cases K1; zify_cond K1.
    { eapply pr_exit; [exact CTX0| exact STATE1| exact FR| prr]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply pr_call_lset with (z := 1); [exact CTX0| exact (pr_state_swap12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE1)| exact FR| lia| lia| reflexivity| exact TP| apply f_equal; lia| reflexivity|].
    clear MK FR. intros m2 mo2 h2 LB2 dY2 r2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? STATE2' FR RR2. pose proof (pr_state_swap12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE2') as STATE2. clear STATE2'.
    flat constr:(STATE2) 2%nat. intros (HH2 & _) _. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    unfold pr_regs in FR.
    zstep. if_cases K2; zify_cond K2.
    { eapply pr_exit; [exact CTX0| exact STATE2| exact FR| prr]. }
    (* [comment removed for export] *)
    pose proof (pr_state_swap13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE2) as STATE2z.
    flat constr:(STATE2z) 2%nat. intros FLt2 _. flat constr:(FLt2) 9%nat. flclear FLt2. intros _ _ _ SOK2 MI2 MF2 HT2 CNT2 ST2. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST2 by lia.
    flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned spv) CTX0 STATE2z ltac:(lia))) 5%nat. intros MZ2 NSZ2 EZ2 ZW2 _.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST2 (bv_unsigned spv). zstep.
    try (replace (bv_unsigned spv + -64 + 64) with (bv_unsigned spv) by lia; rewrite (Z_to_bv_bv_unsigned spv)). zstep.
    pose proof HLSET as SLS. unfold mpi_lset_stmt in SLS.
    eapply aevtM_mono.
    { eapply SLS with (lo := lo) (h := h2) (LB := LB2) (dX := dZ) (z := 0); rewrite ?HT2 by lia;
        first [ exact HH2 | exact MZ2 | exact NSZ2 | exact ZW2 | exact TP | exact MI2 | exact SOK2 | exact CA | exact ACL | exact DHI | exact ST2 | exact HTOP | exact SPA | reflexivity | rewrite EZ2; apply f_equal; lia
              | lia ]. }
    cbv beta. intros c PO. unfold mpi_binop_post in PO. unfold ecp_point_read_post.
    flat constr:(PO) 22%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 mo3 h3 LB3 dZ3 r3 -> PO.
    flat constr:(PO) 10%nat. flclear PO. intros MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR3. flat constr:(RR3) 3%nat. intros _ EA3 FRB3.
    assert (STATE3z : pr_state h LB Q (bv_unsigned spv) lo m mo h3 LB3 (Q + 32) dZ3 (Q + 16) dY2 Q dX1 m3 mo3).
    { eapply pr_step0 with (SPX := bv_unsigned spv); [exact CTX0| exact STATE2z| lia| exact HH3| exact MA3| exact OUT3| exact FRB3| exact PX3| exact SOK3| exact MI3| exact MF3| exact HT3|].
      flat constr:(ST3) 3%nat. flclear ST3. intros S0 S1 S2. split; [lia|]. split; [lia|]. intros a Ha. apply S2. lia. }
    pose proof (pr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX0 (pr_state_swap13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE3z)) as P3. cbv zeta in P3.
    flat constr:(P3) 16%nat. flclear P3. intros _ MF3' HT3' _ PT' PF' PS' PD' SUB' COV' FRS' PX' _ GR' (c3 & CNT3) _.
    flexi 14%nat. exists m3, mo3, h3, LB3, (mkPT dX1 dY2 dZ3), r3, c3.
    split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact MF3'|]. split; [exact HT3'|]. split; [exact HH3|].
    split; [exact PT'|]. split; [exact PF'|]. split; [exact PS'|]. split; [exact PD'|]. split; [exact SUB'|]. split; [exact COV'|]. split; [exact FRS'|].
    split; [exact PX'|]. split; [exact SOK3|]. split; [exact GR'|]. split; [exact CNT3|]. split; [intros E0; exfalso; exact (GXN E0)| prr].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01M0@L11007094131.273L11380053683.159L11385788978.201L11386051250.252L11603836925.223L11803631744.7  L12860309875.272L16075583823.214L16075584458.121L16313514883.248L1709193367.254 L18087015699.7  L19088111567.279L19272228911.7  L19572020754.252L20806791928.252L2192029413.225 L22286003249.176L22286004150.177L22479860437.256L23986821811.135L246903833.279  L246904734.168  L25343751095.244L29742945110.271L29786640492.223L3057967668.201 L3060705547.121 L3064543540.214 L3064753845.159 L30694155386.162L30972666931.244L30985055127.149L30985055127.191L30987168132.223L30987168260.129L30987333253.174L31774956081.159L31940391408.255L33538680625.250L34467299957.8  L3594996389.255 L36568972463.162L36568972463.204L37007107625.250L37009154827.252L39024899413.8  L39024900934.7  L40147640349.177L41707824223.174L41707987166.129L41707987806.223L42161606373.7  L42676618829.226L4457028023.244 L46510687998.10 L46510688493.9  L46510688749.129L46511115628.174L47765649904.253L50608704489.6  L5329183112.226 L54330343321.255L55526851756.276L59229011433.7  L59308546259.257L59308546259.258L59308629082.1  L59427867805.160L5960732812.4   L59682303706.258L59775227692.252L60276648437.7  L61216375001.257L61216375001.258L61274419438.168L61274420073.279L61302936314.8  L6180625946.255 L64011901837.135L64085033602.253L64311849959.244L66141014641.244L8927460368.8   L9261971504.198 L9445252013.177 L9468713420.256 L9999373409.214 R12257210954.168R30197734409.279R34708312074.280R52772328477.128R61274419819.28100000B00J00W01101>01U01g02J02c03=03Z04104204H05F05f06:06L06^07U07g08408<08I08J08W08d08l09909A09d0:j0;Y0<K0=D0>30>e0>m0?N0?o0@?0A60AC0AU0B20BO0BP0B]0Bo0C:0CB0CO0C\0C]0D70D80D90DM0Dd0E>0EJ0F30FY0Fh0G60GX0H:0H>0H?0HJ0Hi0IC0IZ0J<0J^0Jf0K30KA0L<0LI0MK0MX0Me0N10N<0NR0Nn0O=0O>0O?0OY0Oa0P1S3spv1G1Q2bs2r12r4S3spv2bsS3spv1Q2bs2r1S3spv1Q2bs3dX12r13xs34LEN3S3spv1Q2bs2r1S1L3HLS3spv1Q2lo2QS3SLOS3spv1G1Q2bs2r12r4S3spv1Q1B2bs2B02BL4LEN13SPB2r14YPOSS3spv1B2bs2B02BL4LEN13SPBS3spv1Q2bs3dX12r13xs34LEN3S3spv1Q2bs3dX12r13xs34LEN32AQS1L3HLS3spv1Q2lo2QS3SLOFS1L3HLS3spv2lo3SLO3SPBS1L3HLS4DIMG4IMGC3spv1Q2lo2bs3MC23SLO3ACL3dX12r14YPOS3xs34LEN3S3spv1Q2bs3dX12r13xs34LEN31A1n1HS3spv1Q2bs3dX12r12AQS3spv1Q2bs2r11a2HaS3spv1Q2bs2r11a2HaS1L3HLS3spv1Q2lo2bs3SLO3SPB3dX12r14YPOS3xs34LEN31a2LT1lS3spv2bs2dX3SPB2N1S3spv1Q2bs2r1S3spv2bsS3spv1Q2bs2r1FS3spv1Q2bs2r1S3spv1Q2bs2r1S3spv2bsS3spv1Q2bs2r1S3spv2bsS1L3HLS3spv2lo2bs2dX3SLO3ACL3SPB2B4S1L3HLS4DIMG4IMGC3spv1Q2lo2bs3MC23SLO3ACL3SPU3SPB3dX12r14YPOS3xs34LEN3S1L3HLS4DIMG4IMGC3spv2lo2bs3MC23SLO3ACL3SPU3SPBS1L3HLS4DIMG4IMGC3spv2lo2bs3MC23SLO3ACL3SPU3SPB2r1S1L3HLS4DIMG4IMGC3spv1Q2lo2bs3MC23SLO3ACL3SPU3SPB2r14YPOSS1L3HLS4DIMG4IMGC3spv2lo2bs3MC23SLO3ACL3SPU3SPBS1L3HLS4DIMG4IMGC3spv2lo2bs3MC23SLO3ACL3SPU3SPB2r1S3spv2bsS3spv1Q2bs2dZ3dX12r13xs34LEN33PZ0S3spv1Q2bs3dX12r13xs34LEN31A1n2HAS3spv1B2lo2bs2BSS1L3HLS3spv1Q2lo2bs3SLO3ACL3SPB3dX12r14YPOS3xs34LEN32B4S3spv2bs1a2HaS3spv1Q2bs2r11a2HaS3spv1Q2bs3dX12r13xs34LEN32QPS3spv1Q2bs3dX12r13xs34LEN32Q0FS3spv3SPA3SPBS1L3spv2bs2r11a2HdS3spv2bs2r1S3spv2bsS3spv1Q2bs2r1S3spv1Q2lo2QSFS3spv1Q2bs3dX12r13xs34LEN3FFS1L2HI3spv1h2bs4HTOPS1L2HI3spv1h2bs4HTOP2r1S3spv1Q2bs3dX12r13xs34LEN3S1B2bs2dX2JFS1L3spv1Q2lo2bs3ACL3SPB3dX12r14YPOS2P02B4S3spv1Q2bs3SPB3dX12r14YPOS3xs34LEN32N1S3spv1G1Q2bs2r1S1L3spv2lo3SLOS3spv1Q2bs3dX12r13xs34LEN31a2NO2GES3spv1Q2bs3dX12r13xs34LEN31a2NO2g0S2K7FS1Q1B2bs2BQS3spv1Q2bs2dZ3dX12r13xs34LEN31HS3spv1Q2bs3dX12r13xs34LEN3S1L3HLS3spv1Q2lo2QS3SLOS3spv1Q2bs3dX12r13xs34LEN31a2NO2GES3spv1Q2bs3dX12r13xs34LEN31a2NO2g0S3spv2bsS3spv1Q2bs2r1S1L3spv2lo3SLOS1L3HLS3spv1Q2lo2bs2dZ3SLO3ACL3SPB3dX12r14YPOS3xs34LEN33BZ4S3spv2bs4LEN1S1L3HLS4DIMG4IMGC3spv1Q2lo2bs3MC23SLO3ACL3SPB3dX12r14YPOS3xs34LEN3S3spv1Q2bs2r1S3spv1Q2bs2r1S3spv2bs3SPBS3spv2bs2r1S1L2HI3spv1h2bs2r11a1CS3spv1Q2bs3dX12r13xs34LEN31HS3spv1G1Q2bs2r1FFS3spv1Q1g2bs2r12r44GXR42K5S3spv2bsS3spv1Q2bs2r12r4". (* [comment removed for export] *)
  Lemma pr_mx : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Prae,(11.&40.)Pspv,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Ps0e,(11.&40.)Ps1e,(11.&40.)Ps2e,(11.&40.)Ps3e,(11.&40.)Ps4e,(11.&40.)Ps5e,(11.&40.)Ps6e,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pra0,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps4c,(11.&40.)Ps5c,(11.&40.)Ps6c,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)PF,(40.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.PB,$9.Pg,$41.Pcnt,(11.&40.)Plo,$9.Pbs,(15.(11.&8.))Pplen,$9.Pp0,$17.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PdX,$28.PdY,$28.PdZ,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.P,(63.R12.R11.R10.R?.R=.R<.(21.&40.R37.)R;.R14.R13.)P,(62.R13.R12.R10.(21.&40.R38.)R<.R15.R14.R8.R7.R10.R6.(31.R10.+10.)R5.(31.R10.+20.)R4.R3.R2.)P,(35.$59.R4.(31.(21.&40.R39.)-40.)(71.R30.R31.R32.R33.R34.R35.R36.R3:.))P,(1.(11.&40.)R38.(1;.&40.(54.VL,)))P,(1.$9.(;.(6.(38.R11.)))=)P,(1.$2.(3.R9.)$48.)P,(0.(3:.=R?.)(3=.R?.(3?.+2.+40.)))P,(4>.$59.R9.R15.R11.)P,(3=.=R16.)P,(3=.(31.R17.(3;.(3<.(11.&8.)R13.)))(3?.+2.+3?.))P,(3:.+1.(3;.(3<.(11.&8.)R14.)))P,(47.VL,R1<.R16.R19.(3;.(3<.(11.&8.)R15.)))P,(29.(3:.(31.R1:.(3;.(3<.(11.&8.)R16.)))R17.)(3:.(21.&40.R43.)R1:.))P,(29.(3:.(31.R1;.(3;.(3<.(11.&8.)R17.)))R1<.)(3:.(31.R1<.+30.)R1;.))(56.$59.R?.(57.$59.VL,VHI,VMT,R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R24.R23.R20.R1?.R1>.R1;.R1=.R16.R18.+5<?:8.R19.R22.R21.)(19.(1:.R36.(1;.&40.(31.(21.&40.R45.)-40.))R44.R43.R35.R34.R33.(1;.&40.R1=.)(1;.&40.(3;.(3<.(11.&8.)R18.)))(1;.&40.R17.)R2?.R2>.R2=.R2<.R2;.R2:.R29.(1;.&40.R1>.)(1;.&40.R1<.)R32.R31.R30.R3;.R3:.R39.R38.R37.R28.R27.R26.R25.)R24.(1;.&40.+38874.)R23.(1=.(11.&40.))R10.(1>.$59.)))")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX STATE FR TP GY0 YN PLB BAk B0 BL LEN1 BCR BS BQ. pose proof CTX as CTX0. prctx CTX. unfold ECP_POINT_READ_STACK in SLO.
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(STATE) 2%nat. intros STj _. flat constr:(STj) 9%nat. intros HHk SUBk _ SOKk MIk _ HTk _ STk'. pose proof (heap_mok _ _ HI _ _ _ _ HHk) as MK.
    flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned spv - 64) CTX0 STATE ltac:(lia))) 7%nat. intros MX0 NSX EX XW XSL BLX _.
    unfold pr_regs in FR.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) zstep. zstep. eapply pr_exit; [exact CTX0| exact STATE| exact FR| prr]. }
    (* [comment removed for export] *)
    pr_qfacts STATE. pr_qchk.
    zstep. zstep. zstep. zstep. zstep.
    pose proof HRBLE as SRB. unfold mpi_read_binary_le_stmt in SRB.
    eapply aevtM_cut.
    { eapply SRB with (lo := lo) (h := hk) (LB := LBk) (dX := dX) (B := B) (ibs := bs); rewrite ?(unsigned_lit (bv_unsigned spv + -64)), ?HTk by lia;
        first [ exact HHk | exact MX0 | exact NSX | exact BAk | exact B0 | exact BL | exact TP | exact MIk | exact SOKk | exact CA | exact ACL | exact DHI | reflexivity | rewrite EX; reflexivity
              | match goal with |- mpd_writable _ _ _ _ _ => replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) by lia; exact XW end
              | match goal with |- stk _ _ _ _ => replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) by lia; exact STk' end
              | match goal with |- client_range _ _ _ B _ => intros a Ha; destruct (BCR a Ha) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [exact (SUBk _ Hb)| exact R]] end
              | rewrite EX; clear - BQ; lia
              | intros O; (flat constr:((BLX O)) 6%nat; intros IN N1 P0 B4 NIN _); pose proof (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo _ _ B (Z.of_nat (length bs)) HHk IN NIN SUBk ltac:(lia) BCR ltac:(lia) ACL) as JF; first [clear - JF LENP2 PLB| clear - JF LENP PLB| clear - JF PLB]; lia
              | clear - BS SLO HLS; lia
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SRB. cbv beta. intros ms' mo' PO. unfold mpi_read_binary_post in PO. post_binop PO m1 mo1 h1 LB1 dX1 r1.
    rewrite ?(unsigned_lit (bv_unsigned spv + -64)) in PO by lia.
    flat constr:(PO) 12%nat. flclear PO. intros MI1 ST1 MF1 HT1 HH1 MA1 OUT1 PX1 SOK1 HRBFRB1 _ FRB1.
    replace (ret_pc (Z_to_bv 64 0x38898)) with (Z_to_bv 64 0x38898) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (STATE1 : pr_state h LB Q (bv_unsigned spv) lo m mo h1 LB1 Q dX1 (Q + 16) dY (Q + 32) dZ m1 mo1).
    { eapply pr_step0 with (SPX := bv_unsigned spv - 64); [exact CTX0| exact STATE| lia| exact HH1| exact MA1| exact OUT1| exact FRB1| replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) by lia; exact PX1| exact SOK1| exact MI1| exact MF1| exact HT1| replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) by lia; exact ST1]. }
    assert (FR1 : rw_cells usegs m1 (bv_unsigned spv + -64) (pr_regs s6e s5e s4e s3e s2e s1e s0e rae)).
    { eapply heap_presx_rw_cells; [exact PX1| exact FR| cbn; intros a Ha; left; lia|]. unfold mpd_ivs. rewrite EX. cbn. split; [clear - QS SLO HLS; lia|].
      destruct (md_own dX) eqn:O; cbn; [exact I| | exfalso; exact (NSX eq_refl)]. split; [| exact I]. flat constr:((BLX eq_refl)) 5%nat. intros _ _ _ B4 _. lia. }
    clear MK FR PX1. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK. flat constr:(STATE1) 3%nat. intros STj1 FLt3 _. flat constr:(FLt3) 4%nat. flclear FLt3. intros TX1 TY1 TZ1 _. flat constr:(STj1) 9%nat. intros _ SUB1 _ SOK1' _ _ HT1' _ STk1.
    unfold pr_regs in FR1.
    zstep. if_cases K1; zify_cond K1.
    { eapply pr_exit; [exact CTX0| exact STATE1| exact FR1| prr]. }
    (* [comment removed for export] *)
    flat constr:(TY1) 4%nat. intros MY1 EY NSY FRY.
    zstep. zstep.
    pose proof HFREEM as SF. unfold mpi_free_stmt in SF.
    eapply aevtM_cut.
    { flat constr:(MY1) 2%nat. intros MYA _. unfold mpdr_at in MYA. rewrite EY, YN in MYA.
      eapply SF with (lo := lo) (h := h1) (LB := LB1); rewrite ?(unsigned_lit (bv_unsigned spv + -64)), ?HT1' by lia;
        first [ exact HH1 | exact MYA | discriminate | exact TP | exact MI1 | exact SOK1' | exact CA | exact ACL | exact DHI | reflexivity | apply f_equal; lia
              | match goal with |- client_wrange _ _ _ _ _ _ => cbn [mpi_free_LB]; intros a Ha; destruct (QW a ltac:(lia)) as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists b; split; [exact (SUB1 _ Hb)| exact R]] end
              | match goal with |- stk _ _ _ _ => replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) by lia; exact STk1 end
              | intros a Ha Hd; apply QD; lia
              | intros; discriminate
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SF. cbv beta. intros ms' mo' PO. unfold mpi_free_post in PO.
    flat constr:(PO) 20%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned spv + -64)) in PO by lia.
    flat constr:(PO) 8%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 CHY2 PX2 SOK2. cbn [mpi_free_LB mpi_free_X] in HH2, PX2.
    replace (ret_pc (Z_to_bv 64 0x388a4)) with (Z_to_bv 64 0x388a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:((proj1 MY1)) 4%nat. intros _ YAL YPOS _. rewrite EY in YAL, YPOS.
    set (dY2 := mpd_init (Q + 16) (md_pad dY)).
    assert (STATE2 : pr_state h LB Q (bv_unsigned spv) lo m mo h2 LB1 Q dX1 (Q + 16) dY2 (Q + 32) dZ m2 mo2).
    { apply pr_state_swap12. eapply pr_step0 with (SPX := bv_unsigned spv - 64); [exact CTX0| exact (pr_state_swap12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE1)| lia| exact HH2| | | | | exact SOK2| exact MI2| exact MF2| exact HT2| replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) by lia; exact ST2].
      - split; [apply mpdr_at_init; [exact CHY2| exact YAL| exact YPOS]| left; reflexivity].
      - unfold mpd_out. split; [rewrite EY; reflexivity|]. split; [cbn; discriminate|]. split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|].
        intros b Hb. exfalso. unfold mpd_blk in Hb. rewrite YN in Hb. exact Hb.
      - intros b Hb. exfalso. exact Hb.
      - unfold mpd_ivs. rewrite EY, YN. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) by lia. exact PX2. }
    assert (FR2 : rw_cells usegs m2 (bv_unsigned spv + -64) (pr_regs s6e s5e s4e s3e s2e s1e s0e rae)).
    { eapply heap_presx_rw_cells; [exact PX2| exact FR1| cbn; intros a Ha; left; lia|]. cbn. clear - QS SLO HLS. lia. }
    clear MK FR1 PX2. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    pose proof (pr_GR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX0 STATE2) as GR2.
    flat constr:(GR2) 14%nat. intros HD2 _ _ _ _ _ _ _ _ _ FLt4 _ GRNG _. flat constr:(FLt4) 6%nat. flclear FLt4. intros EGX EGY _ MGX2 MGY2 _. unfold grp_head_cells in HD2.
    flat constr:(STATE2) 3%nat. intros STj2 (TX2 & _) _. flat constr:(STj2) 9%nat. intros _ SUB2 _ SOK2' _ _ HT2' _ STk2.
    flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned spv - 64) CTX0 STATE2 ltac:(lia))) 7%nat. intros MX2 NSX2 EX2 XW2 XSL2 BLX2 _.
    unfold pr_regs in FR2.
    (* [comment removed for export] *)
    assert (LSETZ : forall mq moq (hq : HST usegs L HI) dXq (raq t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      pr_state h LB Q (bv_unsigned spv) lo m mo hq LB1 Q dXq (Q + 16) dY2 (Q + 32) dZ mq moq ->
      rw_cells usegs mq (bv_unsigned spv + -64) [C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
      aevtM usegs moq (ecp_point_read_post usegs L HI MT rae spv gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 F fc h LB G g Q p0 bs U_MUL_COUNT lo m mo)
        (MS (mkR raq (Z_to_bv 64 (bv_unsigned spv + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Q) (Z_to_bv 64 (Z.of_nat (length bs))) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 G) (Z_to_bv 64 B) (Z_to_bv 64 plen) s5c s6c s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x388c8) fc None mq (seg_rom usegs))).
    { intros mq moq hq dXq raq t0q t1q t2q a0q a1q a2q a3q a4q a5q a6q a7q t3q t4q t5q t6q STATEq FRq.
      flat constr:(STATEq) 2%nat. intros (HHq & _) _. pose proof (heap_mok _ _ HI _ _ _ _ HHq) as MKq.
      zstep. zstep. zstep.
      eapply pr_call_lset with (z := 1); [exact CTX0| exact (pr_state_swap13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATEq)| exact FRq| lia| lia| reflexivity| exact TP| apply f_equal; lia| reflexivity|].
      intros m4 mo4 h4 LB4 dZ4 r4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? STATE4' FR4 RR4. pose proof (pr_state_swap13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE4') as STATE4. clear STATE4'.
      flat constr:(STATE4) 2%nat. intros (HH4 & _) _. pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
      pose proof (pr_GR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX0 STATE4) as GR4.
      flat constr:(GR4) 12%nat. intros _ _ _ _ _ _ _ _ _ _ FLt5 _. flat constr:(FLt5) 6%nat. flclear FLt5. intros EGX4 EGY4 _ MGX4 MGY4 _.
      flat constr:(MGX4) 2%nat. intros CHGX _. rewrite EGX4 in CHGX. unfold mpi_cells in CHGX.
      flat constr:(MGY4) 2%nat. intros CHGY _. rewrite EGY4 in CHGY. unfold mpi_cells in CHGY. replace (G + 56 + 16) with (G + 72) in CHGY by lia.
      unfold pr_regs in FR4.
      pose proof (mpdr_p_range' _ _ _ _ MGX4) as GXR4. pose proof (mpdr_p_range' _ _ _ _ MGY4) as GYR4.
      zstep. if_cases K4; zify_cond K4.
      { rewrite ?Z.mod_small in K4 by lia. rewrite ?unsigned_lit in K4 by lia. eapply pr_exit; [exact CTX0| exact STATE4| exact FR4| prr]. }
      zstep. zstep. if_cases K5; zify_cond K5.
      { eapply pr_exit; [exact CTX0| exact STATE4| exact FR4| prr]. }
      zstep. zstep. zstep. if_cases K6; zify_cond K6.
      { exfalso. rewrite GY0 in K6. apply K6. reflexivity. }
      zstep. zstep. eapply pr_exit; [exact CTX0| exact STATE4| exact FR4| prr]. }
    zstep. zstep. zstep. if_cases K3; zify_cond K3.
    { (* [comment removed for export] *) eapply LSETZ; [exact STATE2| exact FR2]. }
    zstep. zstep. zstep. zstep. zstep.
    pose proof HSETB as SSB. unfold mpi_set_bit0_stmt in SSB.
    eapply aevtM_cut_evt; [exact MK| eapply SSB with (LB := LB1) (dX := dX1) (pos := (Z.of_nat (length bs) * 8 - 1) mod 2^64) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned spv + -64)) by lia;
      first [ exact MX2 | exact NSX2 | exact MI2 | reflexivity | rewrite EX2; reflexivity
            | match goal with |- stk _ _ _ _ => replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) by lia; exact STk2 end
            | intros O; (flat constr:((BLX2 O)) 5%nat; intros _ _ P0 B4 _); lia
            | intros O; (flat constr:((BLX2 O)) 7%nat; intros _ _ _ _ _ AQ _); rewrite EX2; lia
            | rewrite EX2; clear - QS SLO HLS; lia
            | apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2, Z.mod_mod by lia; f_equal; lia
            | clear - SPA SPB SLO HLS; lia
            | apply Z.mod_pos_bound; lia
            | lia ] |]. cbv beta.
    clear SSB. intros ms' PO. unfold mpi_set_bit0_post in PO.
    flat constr:(PO) 23%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 xs3 -> MU3 WM3 MI3 ST3 MA3 LEN3.
    rewrite ?(unsigned_lit (bv_unsigned spv + -64)) in MU3, ST3 by lia.
    replace (ret_pc (Z_to_bv 64 0x388c4)) with (Z_to_bv 64 0x388c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    set (dX3 := mkMPD (md_addr dX1) (md_sg dX1) (md_n dX1) (md_p dX1) xs3 (md_pad dX1) (md_own dX1)) in MA3.
    flat constr:((proj1 MX2)) 6%nat. intros _ _ _ _ _ HOX2.
    assert (EIV : forall A n, 0 <= A -> (md_own dX1 = LHeap -> md_p dX1 + 4 * md_n dX1 <= A \/ A + n <= md_p dX1) -> A + n <= md_p dX1 \/ md_p dX1 + 4 * md_n dX1 <= A).
    { intros A n HA D. destruct (md_own dX1) eqn:O; [(flat constr:(HOX2) 2%nat; flclear HOX2; intros -> ->); lia| pose proof (D eq_refl); lia| exfalso; exact (NSX2 eq_refl)]. }
    flat constr:((pr_Q_cr _ _ _ _ _ _ _ _ _ _ CTX0)) 2%nat. intros QCRlo _. pose proof (QCRlo Q ltac:(lia)) as QC0.
    assert (Q0 : 0 <= Q) by (pose proof (proj1 MX2) as (_ & _ & QP & _); rewrite EX2 in QP; lia).
    flat constr:(STATE2) 3%nat. intros _ FLt6 _. flat constr:(FLt6) 4%nat. flclear FLt6. intros _ TY2 TZ2 _.
    assert (STATE3 : pr_state h LB Q (bv_unsigned spv) lo m mo h2 LB1 Q dX3 (Q + 16) dY2 (Q + 32) dZ m3 mo2).
    { eapply pr_munch1; [exact CTX0| exact STATE2| exact MU3| exact WM3| exact MI3| replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) by lia; exact ST3| | | | | | exact MA3| reflexivity| reflexivity| reflexivity| reflexivity].
      - intros a NO. cbn in NO. destruct (Z_lt_le_dec a (bv_unsigned spv + -64)) as [LT|GE]; [destruct (Z_le_gt_dec (bv_unsigned spv + -64 - 80) a); [left; lia|]|];
          (destruct (md_own dX1) eqn:O; [(flat constr:(HOX2) 2%nat; flclear HOX2; intros P0 N0); rewrite P0, N0 in NO; exfalso; lia| right; split; [reflexivity|]; (flat constr:((BLX2 eq_refl)) 5%nat; intros _ _ _ B4 _); lia| exfalso; exact (NSX2 eq_refl)]).
      - cbn. split; [lia|]. split; [| exact I]. apply EIV; [lia|]. intros O. flat constr:((BLX2 O)) 3%nat. intros IN N1 _. pose proof (j_blk_MC usegs L HI DIMG h2 LB1 m2 mo2 _ _ U_MUL_COUNT HH2 IN ltac:(lia) MC1 MC2). lia.
      - cbn. split; [clear - QS SLO HLS; lia|]. split; [| exact I]. apply EIV; [lia|]. intros O. flat constr:((BLX2 O)) 7%nat. intros _ _ _ _ _ AQ _. lia.
      - intros OY. exfalso. revert OY. cbn. discriminate.
      - intros OZ. cbn. flat constr:((jtmp_blk usegs L HI h2 LB LB1 m2 mo2 _ dZ HH2 TZ2 OZ)) 5%nat. intros _ _ PZ0 BZ4 _. split; [lia|]. split; [| exact I]. apply EIV; [lia|].
        intros O. flat constr:((BLX2 O)) 9%nat. intros _ _ _ _ _ _ _ _ AP. pose proof (AP OZ). lia. }
    eapply rw_cells_transport in FR2; [| exact MU3| exact WM3| cbn; split; [lia|]; split; [| exact I]; apply EIV; [lia|]; intros O; (flat constr:((BLX2 O)) 5%nat; intros _ _ _ B4 _); lia].
    flat constr:(STATE3) 2%nat. intros (HH3 & _) _. clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
    zstep. if_cases K7; zify_cond K7; [exfalso; clear - K7; cbn in K7; lia|].
    eapply LSETZ; [exact STATE3| exact FR2].
  all: match goal with |- ?gg => idtac "MXLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0240@L10081841430.218L10081841430.223L10312886093.218L10312886093.223L11379989042.226L11380039346.231L11380053683.176L12103661116.225L12103661116.230L13642019862.218L13642019862.223L1386329383.203 L13944546655.231L13944548934.226L15043131708.140L15043131708.214L15466341142.218L15466341142.223L15846433054.3  L15848335108.2  L16075583565.205L16075583692.207L16075584073.133L18087015699.7  L19628484516.207L22687731572.8  L23550810961.11 L23986821811.152L242566168.271  L246903960.212  L246904607.177  L25154152108.232L25345848265.176L26132747253.257L26132747253.266L26132815730.220L26135189691.214L26135189691.220L26270055528.7  L27970009891.8  L29430653417.259L29430653417.268L2973154867.8   L2985390083.226 L30341542220.7  L3060705547.131 L3064753845.176 L30694155386.179L30985055127.166L30987168260.146L36568972463.179L37263163719.11 L37276306146.214L37278403264.140L39024900934.7  L39040021588.11 L39108606513.176L41295834032.5  L41707987166.146L41877766190.226L41890336286.8  L41991527233.142L41991527233.216L45324867394.7  L45345719448.143L45345719448.217L45627207055.176L46225601430.218L46225601430.223L46510688493.9  L46510688749.146L46517389311.13 L48191452659.261L48191452659.270L48543849545.214L48810093443.232L492446834.205  L49464320621.8  L49464320877.146L49470401919.11 L49786828438.218L49786828438.223L50836578996.226L51601712534.218L51601712534.223L51755280368.231L52259700125.7  L53302591708.140L53341217028.4  L54356895797.133L54356896305.205L56270129873.5  L57425804565.206L59314841581.139L59314841581.213L59427867676.168L6052986114.2   L6113046471.229 L61274419311.177L61274420200.212L61287121768.271L61288698875.11 L61290795993.9  L61302939113.226L61953102669.7  L63678637488.7  L64011901837.152L64011901837.232L64313947033.176L65031864584.3  L6503841302.218 L6503841302.223 L66647384848.226L66647435152.231L6751656862.140 L6755968952.216 L67725092320.259L67725092320.268L68285471687.225L68285471687.230L7037304017.9   L7039434965.214 L8178090929.11  L8180206755.9   L8180207011.146 R12257211083.177R19515183896.212R37506282132.271R52772328862.141R52772329243.216R52772329370.214R52772329370.21500000V01101W02202X03303N04404O05505P05Q05n06V06b07=07c08>08?08F09209a0:>0:U0:V0;50;L0<10<W0=20=M0>=0>Z0?@0?[0@60@Q0A70AL0AX0BD0Be0Bf0Cf0D@0DL0Dg0E]0F_0Ga0HA0H[0I:0IO0I\0I]0J80J90JT0KI0KJ0KX0L50LK0Ln0M]0N80N^0O90O:0Oa0Ob0PP0Q30QR0R60R70R80RX0RY0S?0SZ0TB0Th0UC0Ug0VB0VX0Ve0W:0WY0Wh0XJ0Xa0YL0YM0YT0Z10ZL0Zg0[M0[^0[_0\N0\i0]60]V0^A0^\0^d0_J0_e0`\0aH0aT0b20b\0c;0ca0d<0dV0e70e80e90el0em0en0eo0f;0fY0g40gRS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bFS3rae3spv1Q2bs4plen3ibs5LEN1bS3rae3spv1Q2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bsS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bFS1Q3MCQS3rae3spv1B2bs4plen2B02BL4LEN13SPB3ibs5LEN1bS3rae3spv1B2bs4plen2B02BL4LEN13SPB3ibs5LEN1b2b0S3rae3spv1B2bs2B02BL4LEN13SPBS1L3HLS3spv1Q2lo2QS3SLOFS3spv1B2lo2bs4plen3PLB2BS5LENP2S3spv1B2lo2bs2BS1a2Ha1CS3rae3spv2bs4plen2dX3SPB3ibs5LEN1b2N1S3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen2dY3SPB3ibs5LEN1b4ibs25LEN3b2N1S3rae3spv1Q2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS1Q1B2bs4plen2BQ4LENPS2bs4plen2K1S3rae3spv2lo2bs4plen3ibs5LEN1b4ibs25LEN3b2S0S3rae3spv2lo2bs4plen3ibs5LEN1b2S0FS3rae3spv1B2bs4plen2BL4LEN13SPB3ibs5LEN1b5LENP24ibs25LEN3b5LENi2S1Q1B2bs4plen3PLB2BQ5LENP2S3rae3spv2bsS3rae3spv2bs4plen3ibs5LEN1bS1L3HLS3rae3spv2lo2bs4plen2dX3SLO3ACL3SPB3ibs5LEN1b2B4S1L3HLS4DIMG4IMGC3rae3spv2lo2bs4plen3MC23SLO3ACL3SPU3SPB3ibs5LEN1bS1L3HLS4DIMG4IMGC3rae3spv2lo2bs4plen3MC23SLO3ACL3SPU3SPB3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b1a2HaS3spv1B2lo2bs4plen2BS4LENPS3rae3spv2bs4plen3PLB3ibs5LEN1bS3rae3spv2bs4plen3PLBS3spv3SPA3SPBFS3rae3spv2bs4plen3ibs5LEN1bFS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv1B2bs4plen2B03SPB3ibs5LEN1b4ibs25LEN3b5LENi2FS3rae3spv1B2bsS3rae3spv1B2bs4plen3ibs5LEN1bS1B2bs4plen2dX4LENP2JFS3rae3spv2bs4plen3PLB3SPB3ibs5LEN1bS3rae3spv2bs4plen3SPB3ibs5LEN1b4LENi4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bFS1L2HI3rae3spv1h2bs4plen4HTOP3ibs5LEN1bFS3rae3spv2lo2bs4plen3ibs5LEN1b4ibs25LEN3b1a2HaS3rae3spv2lo2bs4plen3ibs5LEN1b1a2HaS3rae3spv2bs4plen3PLB3ibs5LEN1bS3rae3spv1Q2bs4plen3ibs5LEN1b3dX12AQFFS3rae3spv1B2bs4plen2B03ibs5LEN1bFS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv1B2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS1L3rae3spv2lo2bs4plen3SLO3ibs5LEN1bS1B2bs4plen2dY3PLB5LENP22JFS3rae3spv2bs4plen4LENPS3spv1G2lo2GSS3rae3spv2bs4plen3PLBS3rae3spv2bs4plen3PLB3ibs5LEN1bS1Q1B2bs2BQ3BMCS3rae3spv2bs4plen3PLB3ibs5LEN1b2b0S3rae3spv2bs4LEN13SPB1NS3rae3spv2bs4plen4LEN13SPB4LENP3ibs5LEN1b1NFS1Q3MCQS3rae3spv1Q2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS1L3spv2lo2bs3SLOFS1L3rae3spv2lo2bs4plen3SLO3ibs5LEN1b4ibs25LEN3bS1B2bs4plen4LENP1a2Ha5LENP2S3spv1Q2lo2QSS3rae3spv2bs4plen4LEN13ibs5LEN1bS3rae3spv2bs4plen4LEN13ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS1G1Q2QGS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS1L3HLS3rae3spv2lo2bs4plen3SLO3SPB3ibs5LEN1b4ibs25LEN3bS1L3HLS3rae3spv2lo2bs4plen3SLO3SPB3ibs5LEN1bS3rae3spv2bsS3rae3spv2bs4plen3ibs5LEN1b2b0S3rae3spv2bs4plen3SPU3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3SPU3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b4ibs25LEN3bS3rae3spv2bs4plen3ibs5LEN1bS2bs4plen3PLB4LEN14LENP2K6S3rae3spv2bs4plen3ibs5LEN1b5LENP2FFS3rae3spv1B2bs4plen2BL4LEN13SPB4LENP3ibs5LEN1b4LENiFFFS3rae3spv2bsS3rae3spv2bs4plen3ibs5LEN1b2b0S3rae3spv2bs4plen3ibs5LEN1bS3rae3spv2bs4plen3ibs5LEN1b2b0". (* [comment removed for export] *)
  Lemma pr_sw : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "Prae,(11.&40.)Pspv,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Ps0e,(11.&40.)Ps1e,(11.&40.)Ps2e,(11.&40.)Ps3e,(11.&40.)Ps4e,(11.&40.)Ps5e,(11.&40.)Ps6e,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pra0,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps4c,(11.&40.)Ps5c,(11.&40.)Ps6c,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)PF,(40.&5.(11.&40.))Pfc,(11.&20.)Pm,P,(11.&40.)(12.(11.&8.))Pmo,$13.Ph,(14.$59.VL,VHI,)PLB,(15.$16.)PG,$9.PQ,$9.PB,$9.Pg,$41.Pcnt,(11.&40.)Plo,$9.Pbs,(15.(11.&8.))Pplen,$9.Pp0,$17.Phk,(14.$59.VL,VHI,)PLBk,(15.$16.)PdX,$28.PdY,$28.PdZ,$28.Pmk,P,(11.&40.)(12.(11.&8.))Pmok,$13.P,(63.R12.R11.R10.R?.R=.R<.(21.&40.R37.)R;.R14.R13.)P,(62.R13.R12.R10.(21.&40.R38.)R<.R15.R14.R8.R7.R10.R6.(31.R10.+10.)R5.(31.R10.+20.)R4.R3.R2.)P,(35.$59.R4.(31.(21.&40.R39.)-40.)(71.R30.R31.R32.R33.R34.R35.R36.R3:.))P,(1.(11.&40.)R38.(1;.&40.(54.VL,)))P,(1.$9.(53.(21.&40.R3<.)+2.)=)P,(1.$9.(43.R12.)+1.)P,(1.$9.(2:.(42.R13.))+1.)P,(1.$9.(2:.(44.R14.))+1.)P,(1.$9.(2:.(45.R15.))+1.)P,(3:.+1.(46.(42.R16.)))P,(3:.(=.(42.R17.))+1387.)P,(1.$2.(3.R?.)$48.)P,(0.(3:.=R15.)(3=.R15.(3?.+2.+3=.)))P,(4>.$59.R21.R1;.R17.)P,(3=.=R1<.)P,(3=.(31.R1=.(3;.(3<.(11.&8.)R19.)))(3?.+2.+3?.))P,(3:.+1.(3;.(3<.(11.&8.)R1:.)))P,(47.VL,R22.R1<.R1?.(3;.(3<.(11.&8.)R1;.)))P,(29.(3:.(31.R20.(3;.(3<.(11.&8.)R1<.)))R1=.)(3:.(21.&40.R49.)R20.))P,(29.(3:.(31.R21.(3;.(3<.(11.&8.)R1=.)))R22.)(3:.(31.R22.+30.)R21.))P,(29.(3:.(31.+5<?:8.+8.)R22.)(3:.(31.R22.(3;.(3<.(11.&8.)R1>.)))+5<?:8.))(56.$59.R16.(57.$59.VL,VHI,VMT,R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R2;.R2:.R27.R26.R25.R22.R24.R1=.R1?.+5<?:8.R20.R29.R28.)(19.(1:.R3=.(1;.&40.(31.(21.&40.R4<.)-40.))R4;.R4:.R3<.R3;.R3:.(1;.&40.R24.)(1;.&40.(3;.(3<.(11.&8.)R1?.)))(1;.&40.R1>.)R36.R35.R34.R33.R32.R31.R30.(1;.&40.R25.)(1;.&40.R23.)R39.R38.R37.R42.R41.R40.R3?.R3>.R2?.R2>.R2=.R2<.)R2;.(1;.&40.+387<0.)R2:.(1=.(11.&40.))R17.(1>.$59.)))")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX STATE FR TP RAE H1 GPS GAS GBS PV PN49 YN PLB BA B0 BL LEN1 BCR BS BQ BMC. pose proof CTX as CTX0. prctx CTX. unfold ECP_POINT_READ_STACK in SLO.
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((pr_Q_cr _ _ _ _ _ _ _ _ _ _ CTX0)) 2%nat. intros QCRlo QCR.
    (* [comment removed for export] *)
    assert (BAT : forall (hq : HST usegs L HI) LBq mq moq, jst usegs L HI h LB (bv_unsigned spv) 64 (pr_XO Q) U_MUL_COUNT lo m mo hq LBq mq moq -> bytes_at usegs mq B bs).
    { intros hq LBq mq moq (_ & _ & PXq & _). eapply heap_presx_bytes_at; [exact PXq| exact BA| | unfold pr_XO; cbn; clear - BQ BMC; lia].
      intros a Ha. destruct (BCR a Ha) as [C|[C|C]]; [left; clear - C BS Ha SLO HLS; lia| right; left; exact C| right; right; exact C]. }
    flat constr:(STATE) 2%nat. intros STj _. flat constr:(STj) 9%nat. intros HHk SUBk _ SOKk MIk _ HTk _ STk'. pose proof (heap_mok _ _ HI _ _ _ _ HHk) as MK.
    flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned spv - 64) CTX0 STATE ltac:(lia))) 7%nat. intros MX0 NSX EX XW XSL BLX _.
    pose proof (BAT _ _ _ _ STj) as BAk.
    unfold pr_regs in FR.
    (* [comment removed for export] *)
    zstep. if_cases KB0; zify_cond KB0; [exfalso; rewrite ?unsigned_lit in KB0 by lia; lia|].
    rd8 BAk 0.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) eapply pr_zero; [exact CTX0| exact STATE| exact FR| exact TP| exact RAE]. }
    zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *) zstep. zstep. eapply pr_exit; [exact CTX0| exact STATE| exact FR| prr]. }
    (* [comment removed for export] *)
    assert (LENP : plen + 1 <= Z.of_nat (length bs)) by (clear - K1 PLB BL LEN1 B0; lia). clear K0 K1.
    flat constr:((bytes_at_sub _ _ _ 1 plen BAk ltac:(lia) ltac:(lia) ltac:(lia))) 2%nat. intros BA1 LEN1b.
    set (ibs := firstn (Z.to_nat plen) (skipn (Z.to_nat 1) bs)) in BA1, LEN1b.
    assert (LENi : Z.of_nat (length ibs) = plen) by (rewrite LEN1b; lia).
    assert (BCR1 : client_range L LBk lo (B + 1) plen).
    { intros a Ha. destruct (BCR a ltac:(clear - Ha LENP PLB; lia)) as [C|[C|(bb & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists bb; split; [exact (SUBk _ Hb)| exact R]]. }
    pr_qfacts STATE. pr_qchk.
    zstep. zstep. if_cases KB1; zify_cond KB1; [exfalso; rewrite ?unsigned_lit in KB1 by lia; first [lia | vm_compute in KB1; lia]|].
    zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof HRB as SRB. unfold mpi_read_binary_stmt in SRB.
    eapply aevtM_cut.
    { eapply SRB with (lo := lo) (h := hk) (LB := LBk) (dX := dX) (B := B + 1) (ibs := ibs); rewrite ?(unsigned_lit (bv_unsigned spv + -64)), ?HTk, ?LENi by lia;
        first [ exact HHk | exact MX0 | exact NSX | exact BA1 | exact BCR1 | exact TP | exact MIk | exact SOKk | exact CA | exact ACL | exact DHI | reflexivity | rewrite EX; reflexivity | apply f_equal; lia
              | match goal with |- mpd_writable _ _ _ _ _ => replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) by lia; exact XW end
              | match goal with |- stk _ _ _ _ => replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) by lia; exact STk' end
              | rewrite EX; clear - BQ LENP PLB; lia
              | intros O; (flat constr:((BLX O)) 6%nat; intros IN N1 P0 B4 NIN _); pose proof (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo _ _ B (Z.of_nat (length bs)) HHk IN NIN SUBk ltac:(lia) BCR ltac:(lia) ACL) as JF; first [clear - JF LENP2 PLB| clear - JF LENP PLB| clear - JF PLB]; lia
              | clear - BS SLO HLS LENP PLB; lia
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SRB. cbv beta. intros ms' mo' PO. unfold mpi_read_binary_post in PO. post_binop PO m1 mo1 h1 LB1 dX1 r1.
    rewrite ?(unsigned_lit (bv_unsigned spv + -64)) in PO by lia.
    flat constr:(PO) 12%nat. flclear PO. intros MI1 ST1 MF1 HT1 HH1 MA1 OUT1 PX1 SOK1 HRBFRB1 _ FRB1.
    replace (ret_pc (Z_to_bv 64 0x38800)) with (Z_to_bv 64 0x38800) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (STATE1 : pr_state h LB Q (bv_unsigned spv) lo m mo h1 LB1 Q dX1 (Q + 16) dY (Q + 32) dZ m1 mo1).
    { eapply pr_step0 with (SPX := bv_unsigned spv - 64); [exact CTX0| exact STATE| lia| exact HH1| exact MA1| exact OUT1| exact FRB1| replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) by lia; exact PX1| exact SOK1| exact MI1| exact MF1| exact HT1| replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) by lia; exact ST1]. }
    assert (FR1 : rw_cells usegs m1 (bv_unsigned spv + -64) (pr_regs s6e s5e s4e s3e s2e s1e s0e rae)).
    { eapply heap_presx_rw_cells; [exact PX1| exact FR| cbn; intros a Ha; left; lia|]. unfold mpd_ivs. rewrite EX. cbn. split; [clear - QS SLO HLS; lia|].
      destruct (md_own dX) eqn:O; cbn; [exact I| | exfalso; exact (NSX eq_refl)]. split; [| exact I]. flat constr:((BLX eq_refl)) 5%nat. intros _ _ _ B4 _. lia. }
    clear MK FR PX1. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK. flat constr:(STATE1) 2%nat. intros (_ & _) _.
    unfold pr_regs in FR1.
    zstep. if_cases K2; zify_cond K2.
    { eapply pr_exit; [exact CTX0| exact STATE1| exact FR1| prr]. }
    clear K2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply pr_call_lset with (z := 1); [exact CTX0| exact (pr_state_swap13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE1)| exact FR1| lia| lia| reflexivity| exact TP| apply f_equal; lia| reflexivity|].
    clear MK FR1. intros m2 mo2 h2 LB2 dZ2 r2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? STATE2' FR RR2. pose proof (pr_state_swap13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE2') as STATE2. clear STATE2'.
    flat constr:(STATE2) 3%nat. intros STj2 FLt7 _. flat constr:(FLt7) 4%nat. flclear FLt7. intros TX2 TY2 TZ2 _. flat constr:(STj2) 9%nat. intros HH2 SUB2 _ SOK2 MI2 MF2 HT2 (c2 & CNT2) STk2. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    unfold pr_regs in FR.
    zstep. if_cases K3; zify_cond K3.
    { eapply pr_exit; [exact CTX0| exact STATE2| exact FR| prr]. }
    clear K3.
    (* [comment removed for export] *)
    pose proof (BAT _ _ _ _ STj2) as BA2.
    rd8 BA2 0.
    zstep. zstep. zstep. zstep. zstep. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K5; zify_cond K5.
      { eapply pr_exit; [exact CTX0| exact STATE2| exact FR| prr]. }
      zstep. zstep. zstep. if_cases K6; zify_cond K6.
      { zstep. zstep. eapply pr_exit; [exact CTX0| exact STATE2| exact FR| prr]. }
      (* [comment removed for export] *)
      assert (LENP2 : 1 + plen + plen <= Z.of_nat (length bs)) by (rewrite ?Z.shiftl_mul_pow2 in K6 by lia; clear - K6 PLB BL LEN1 B0 LENP; lia). clear K4 K5 K6.
      flat constr:((bytes_at_sub _ _ _ (1 + plen) plen BA2 ltac:(lia) ltac:(lia) ltac:(lia))) 2%nat. intros BA3 LEN3b.
      set (ibs2 := firstn (Z.to_nat plen) (skipn (Z.to_nat (1 + plen)) bs)) in BA3, LEN3b.
      assert (LENi2 : Z.of_nat (length ibs2) = plen) by (rewrite LEN3b; lia).
      assert (BCR2 : client_range L LB2 lo (B + (1 + plen)) plen).
      { intros a Ha. destruct (BCR a ltac:(clear - Ha LENP2 PLB; lia)) as [C|[C|(bb & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists bb; split; [exact (SUB2 _ Hb)| exact R]]. }
      pose proof (pr_state_swap12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE2) as STATE2y.
      flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned spv) CTX0 STATE2y ltac:(lia))) 7%nat. intros MY2 NSY2 EY2 YW2 YSL2 BLY2 _.
      replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in STk2 by lia.
      zstep. zstep. if_cases KW; zify_cond KW; [exfalso; rewrite ?unsigned_lit in KW by lia; rewrite lxor_allones64 in KW by lia; lia|].
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      release_frame FR STk2 (bv_unsigned spv). zstep.
      try (replace (bv_unsigned spv + -64 + 64) with (bv_unsigned spv) by lia; rewrite (Z_to_bv_bv_unsigned spv)). zstep.
      pose proof HRB as SRB. unfold mpi_read_binary_stmt in SRB.
      eapply aevtM_mono.
      { eapply SRB with (lo := lo) (h := h2) (LB := LB2) (dX := dY) (B := B + (1 + plen)) (ibs := ibs2); rewrite ?HT2, ?LENi2 by lia;
          first [ exact HH2 | exact MY2 | exact NSY2 | exact YW2 | exact BA3 | exact BCR2 | exact TP | exact MI2 | exact SOK2 | exact CA | exact ACL | exact DHI | exact STk2 | exact HTOP | exact SPA | exact RAE
                | reflexivity | rewrite EY2; apply f_equal; lia | apply f_equal; lia
                | rewrite EY2; clear - BQ LENP2 PLB; lia
                | intros O; (flat constr:((BLY2 O)) 6%nat; intros IN N1 P0 B4 NIN _); pose proof (j_fresh_apart usegs L HI DIMG h2 LB2 m2 mo2 LB lo _ _ B (Z.of_nat (length bs)) HH2 IN NIN SUB2 ltac:(lia) BCR ltac:(lia) ACL) as JF; first [clear - JF LENP2 PLB| clear - JF LENP PLB| clear - JF PLB]; lia
                | clear - BS LENP2 PLB; lia
                | lia ]. }
      cbv beta. intros c PO. unfold mpi_read_binary_post in PO. unfold ecp_point_read_post.
      flat constr:(PO) 22%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 mo3 h3 LB3 dY3 r3 -> PO.
      flat constr:(PO) 12%nat. flclear PO. intros MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 HRBFRB3 _ FRB3.
      assert (STATE3y : pr_state h LB Q (bv_unsigned spv) lo m mo h3 LB3 (Q + 16) dY3 Q dX1 (Q + 32) dZ2 m3 mo3).
      { eapply pr_step0 with (SPX := bv_unsigned spv); [exact CTX0| exact STATE2y| lia| exact HH3| exact MA3| exact OUT3| exact FRB3| exact PX3| exact SOK3| exact MI3| exact MF3| exact HT3|].
        flat constr:(ST3) 3%nat. flclear ST3. intros S0 S1 S2. split; [lia|]. split; [lia|]. intros a Ha. apply S2. lia. }
      pose proof (pr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX0 (pr_state_swap12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE3y)) as P3. cbv zeta in P3.
      flat constr:(P3) 16%nat. flclear P3. intros _ MF3' HT3' _ PT' PF' PS' PD' SUB' COV' FRS' PX' _ GR' (c3 & CNT3) _.
      flexi 14%nat. exists m3, mo3, h3, LB3, (mkPT dX1 dY3 dZ2), r3, c3.
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact MF3'|]. split; [exact HT3'|]. split; [exact HH3|].
      split; [exact PT'|]. split; [exact PF'|]. split; [exact PS'|]. split; [exact PD'|]. split; [exact SUB'|]. split; [exact COV'|]. split; [exact FRS'|].
      split; [exact PX'|]. split; [exact SOK3|]. split; [exact GR'|]. split; [exact CNT3|]. split; [intros E0; exfalso; exact (GXN E0)| prr].
    - (* [comment removed for export] *)
      clear K4.
      zstep. if_cases K5; zify_cond K5.
      { eapply pr_exit; [exact CTX0| exact STATE2| exact FR| prr]. }
      clear K5.
      (* [comment removed for export] *)
      pose proof (pr_state_swap12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE2) as STATE2y.
      flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned spv) CTX0 STATE2y ltac:(lia))) 7%nat. intros MY2 NSY2 EY2 YW2 YSL2 BLY2 _.
      flat constr:((pr_d1_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned spv) CTX0 STATE2 ltac:(lia))) 9%nat. intros MX2 NSX2 EX2 _ XSL2 BLX2 CRX2 CRXL2 _.
      pose proof (pr_GR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX0 STATE2) as GR2.
      flat constr:(TY2) 4%nat. intros _ _ _ FRY2.
      assert (EXT2 : ext_opnd L LB2 dY dX1 U_MUL_COUNT (bv_unsigned spv) lo).
      { unfold ext_opnd, opnd_sep. rewrite EY2, EX2. split; [lia|].
        split. { split; [intros NN; destruct (md_own dX1) eqn:O; [exfalso; exact (NN eq_refl)| (flat constr:((BLX2 eq_refl)) 7%nat; intros _ _ _ _ _ AQ _); lia| exfalso; exact (NSX2 eq_refl)]|].
                 split; [rewrite YN; intros; discriminate|]. split; [right; left; rewrite YN; discriminate|]. split; [clear - QS SLO HLS; lia| exact XSL2]. }
        split; [exact CRX2|]. split; [exact CRXL2|]. clear - MCQ; lia. }
      assert (GCR2 : client_range L LB2 lo G 192).
      { intros a Ha. destruct (GCR a Ha) as [C|[C|(bb & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists bb; split; [exact (SUB2 _ Hb)| exact R]]. }
      replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in STk2 by lia.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      release_frame FR STk2 (bv_unsigned spv). zstep.
      try (replace (bv_unsigned spv + -64 + 64) with (bv_unsigned spv) by lia; rewrite (Z_to_bv_bv_unsigned spv)). zstep.
      pose proof HDY as SDY. unfold ecp_derive_y_stmt in SDY.
      eapply aevtM_mono.
      { eapply SDY with (lo := lo) (h := h2) (LB := LB2) (dX := dY) (dA := dX1) (G := G) (g := g) (cnt := c2); rewrite ?HT2 by lia;
          first [ exact HH2 | exact GR2 | exact H1 | exact GPS | exact GAS | exact GBS | exact PV | exact PN49 | exact GCR2 | exact MY2 | exact YN | exact YW2 | exact MX2 | exact EXT2
                | exact CNT2 | exact MC1 | exact MC2 | exact MCS | exact MCG | exact TP | exact MI2 | exact SOK2 | exact CA | exact ACL | exact DHI | exact STk2 | exact HTOP | exact SPA
                | reflexivity | rewrite EX2; reflexivity | rewrite EY2; apply f_equal; lia
                | rewrite EY2; clear - QG; lia
                | rewrite EY2; clear - MCQ; lia
                | clear - GS; lia
                | unfold ECP_DERIVE_Y_STACK; lia
                | lia ]. }
      cbv beta. intros c PO. unfold ecp_mul_mod_post in PO. unfold ecp_point_read_post.
      flat constr:(PO) 23%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 mo3 h3 LB3 dY3 r3 cnt3 -> PO.
      flat constr:(PO) 12%nat. flclear PO. intros MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 GR3 CNT3 RR3. flat constr:(RR3) 2%nat. intros HrM3 FLt8. flat constr:(FLt8) 4%nat. flclear FLt8. intros _ _ FRB3 _.
      assert (STATE3y : pr_state h LB Q (bv_unsigned spv) lo m mo h3 LB3 (Q + 16) dY3 Q dX1 (Q + 32) dZ2 m3 mo3).
      { eapply pr_step1 with (SPX := bv_unsigned spv) (XC := [(U_MUL_COUNT, U_MUL_COUNT + 8)]); [exact CTX0| exact STATE2y| right; reflexivity| lia| exact HH3| exact MA3| exact OUT3| exact FRB3| exact PX3| exact SOK3| exact MI3| exact MF3| exact HT3| exists cnt3; exact CNT3|].
        flat constr:(ST3) 3%nat. flclear ST3. intros S0 S1 S2. split; [lia|]. split; [lia|]. intros a Ha. apply S2. lia. }
      pose proof (pr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX0 (pr_state_swap12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STATE3y)) as P3. cbv zeta in P3.
      flat constr:(P3) 16%nat. flclear P3. intros _ MF3' HT3' _ PT' PF' PS' PD' SUB' COV' FRS' PX' _ GR' (c3 & CNT3') _.
      flexi 14%nat. exists m3, mo3, h3, LB3, (mkPT dX1 dY3 dZ2), r3, c3.
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact MF3'|]. split; [exact HT3'|]. split; [exact HH3|].
      split; [exact PT'|]. split; [exact PF'|]. split; [exact PS'|]. split; [exact PD'|]. split; [exact SUB'|]. split; [exact COV'|]. split; [exact FRS'|].
      split; [exact PX'|]. split; [exact SOK3|]. split; [exact GR'|]. split; [exact CNT3'|]. split; [intros E0; exfalso; exact (GXN E0)| prr].
  all: match goal with |- ?gg => idtac "SWLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0110@L11007094131.144L11572456734.123L11803634930.141L12283411672.113L12860309875.140L13301871092.113L13443634643.106L13447020430.111L14106684376.112L15463825327.122L15463825327.123L16075584458.113L17646078182.118L17648094188.149L19427582228.117L19427582228.118L22700267513.7  L27008441484.119L27008441484.120L30618040681.113L30985072156.123L30987168101.141L34994544387.113L39024900934.7  L39845524527.7  L39887139444.113L41288976216.113L41596053933.7  L41596069168.4  L41598391688.143L43059266230.116L43374875207.5  L43934434070.123L4438557961.114 L4444764981.110 L44622288685.122L44622288685.123L44866992728.113L45898055924.113L48429268312.113L49596482252.106L49698585326.122L49698585326.123L51189831868.7  L5145216728.113 L51925114228.113L53134003687.108L55526851756.145L57428035345.153L57933933556.113L60557018246.106L61851984225.141L63370247692.106L63663075009.5  L63962036340.112L67158371251.113L67541566890.115L67541566890.116L7274816372.113 L8619100141.7   L8722184664.113 L8927507745.113 R30830417310.148R43784007005.148R52772328477.12100000C00V00g01801K01\02102E02V03603h04@04Q04b05e07=07R08k0:Y0;90<10<i0=:0=F0=[0=l0>=0>I0>V0?=0?c0?j0@M0A:0A_0Bb0D:0DK0D\0Dm0EE0Ei0Fb0Fn0G?0GP0H@0HS0Hh0I90II0IZ0If0J50JF0JW0K@0Ki0L:0LF0LW0M>0MO0Md0N5S2ra2sp1G1g2bs4plenS2ra2sp1G1g2bs4plenS2ra2sp1g2bs4plenS2ra2sp1g2bs4plenS2ra2sp1G1g2bs4plenS2ra2sp1g2bs4plenS2ra2sp1g2bs3PHN4plenS2ra2sp1g2bs4plen2B1S2ra2sp1g2bs4plenS2ra2sp1g2bs4plen2HB5Ha_st5Hl_stS2ra2sp2s01g2bs4plen2HB5Ha_st5Hl_st2s12s22s32s42s5S2ra2sp1B1g2bs2B02BL3SPBS2ra2sp1g2bs4plenS2ra2sp1g2bs4plenS1L3HLS4DIMG4IMGC2ra2sp1g2bs2lo3MC23SLO3ACL4plen3CBR2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2ra2sp2s01g2bs2lo3MC23SLO3ACL4plen3CBR2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1L3HLS2sp2lo3SLO1x1HS1L3HLS4DIMG4IMGC2ra2sp1G1Q1B1g2bs2lo2GS2QS2BS2BQ3MC23SLO3ACL3SPB4plen3CBR2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2ra2sp2s01G1Q1B1g2bs2lo2GS2QS2BS2BQ3MC23SLO3ACL3SPB4plen3CBR2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2ra2sp1g2bs3SPB4plen3CBR2N13PB1S1L3HLS4DIMG4IMGC2ra2sp1g2bs2lo3MC23SLO3ACL3SPB4plen3CBRS1L3HLS4DIMG4IMGC2ra2sp1g2bs2lo3MC23SLO3ACL3SPB4plen3CBRS2ra2sp1g2bs4plenS2sp3SPA3SPBS1L3HLS2sp2lo3SLO3SPBS2ra2sp1g2bs4plenS2ra2sp1g2bs4plenS2sp1G2lo2GSS2sp1g2lo3PSLS1L2ra2sp1g2bs2lo3ACL3SPB4plen3CBR1d2B4S1L3HLS2ra2sp1g2bs2lo3SLO3SPB4plen3CBRS2bs2K0S2ra2sp2s61g2bs4plen2HB5Ha_st5Hl_stS1L4IMGC2ra2sp1g2bs2lo3ACL3SPB4plen3CBR3PB11HS1L2ra2sp1g2bs2lo3ACL3SPB4plen3CBR2B4S1L3HLS4DIMG4IMGC2ra2sp1g2bs2lo3SLO3ACL3SPB4plen3CBR2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2ra2sp2s01g2bs2lo3SLO3ACL3SPB4plen3CBR2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2ra2sp1g2bs4plenS2ra2sp1g2bs4plenS2ra2sp1g2bs4plenS2ra2sp1g2bs3SPB3PHN3CBRS2ra2sp1g2bs3SPB4plen2HB5Ha_st5Hl_stS2ra2sp2s01g2bs3SPB4plen2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp1G2lo2GSS2ra2sp1g2bs4plenS2ra2sp1g2bs4plenS1L4DIMG4IMGC2ra2sp1g2bs2lo3MC23ACL3SPB4plen3CBRS2ra2sp1G1g2bs4plenS2ra2sp1g2bs4plen3PLBS2ra2sp1g2bs4plenS2ra2sp1g2bs3CBRS2ra2sp1g2bs4plenS2ra2sp1g2bsS2sp1B2bs2lo2BSS2ra2sp1g2bs4plenS2ra2sp1g2bs4plenS1L3HLS2ra2sp1g2bs2lo3SLO3SPB4plen3CBR2HBS1L3HLS2ra2sp1g2bs2lo3SLO3SPB4plen3CBR2HBS2ra2sp1g2bs4plenS2sp1G2lo2GSS2ra2sp1g2bs4plenS2ra2sp1g2bs3SPB3PHL4plen3CBR2N12P03PB1S2ra2sp1g2bs4plenS2ra2sp1g2bs3SPB4plenS2ra2sp1g2bs4plen". (* [comment removed for export] *)
  Theorem U_ecp_point_read_binary_spec : ltac2:(CDefT.buildp (gd_tbl_P_ecp_point_read_binary ()) "(77.$59.VL,VHI,VMT,$78.$5>.+5<?:8.$5=.)")
(* [comment removed for export] *).
  Proof.
    unfold ecp_point_read_binary_stmt, U_ECP_POINT_READ_BINARY. intros until lo.
    intros HH GR PSG GSW GCR GS MCG PT PN PS QW QD QS MCQ QG GQL BA B0 BL BCR BS BQ BMC CNT MC1 MC2 MCS ST SLO ACL HTOP SPA DHI TP MI RAE SOK CA -> -> -> ->.
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    pose proof SLO as SLO0. unfold ECP_POINT_READ_STACK in SLO.
    (* [comment removed for export] *)
    flat constr:(GR) 9%nat. intros _ _ _ EP _ _ _ MP _.
    flat constr:(MP) 6%nat. intros _ _ _ PHL PHN PHO. unfold MPI_MAX_LIMBS in PHN.
    set (plen := (core_bitlen (md_limbs (g_P g)) (md_n (g_P g)) + 7) / 8).
    pose proof (core_bitlen_range (md_limbs (g_P g)) (md_n (g_P g)) ltac:(lia)) as CBR.
    assert (PLB : 0 <= plen < 2^61) by (subst plen; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    assert (PSL : md_p (g_P g) + 4 * md_n (g_P g) <= lo).
    { destruct (md_own (g_P g)) eqn:OP; [(flat constr:(PHO) 2%nat; flclear PHO; intros -> ->); lia| |].
      - flat constr:(PHO) 3%nat. flclear PHO. intros _ IN _. flat constr:((proj1 (Forall_forall _ _) HBR _ IN)) 5%nat. intros _ _ _ B4 _. cbn in B4. lia.
      - flat constr:(PHO) 5%nat. flclear PHO. intros N1 _ P0 PB PRO. flat constr:(PB) 3%nat. intros _ PB1 _. rewrite u32s_length in PB1.
        pose proof (ROIMG _ (PRO (4 * md_n (g_P g) - 1) ltac:(lia)) ltac:(lia)). lia. }
    assert (PP0 : md_own (g_P g) = LHeap -> 0 < md_p (g_P g)).
    { intros OP. rewrite OP in PHO. flat constr:(PHO) 3%nat. flclear PHO. intros _ IN _. flat constr:((proj1 (Forall_forall _ _) HBR _ IN)) 2%nat. intros B1 _. cbn in B1. lia. }
    (* [comment removed for export] *)
    pose proof (lock MI) as MI00. pose proof (lock HH) as HH00. pose proof (lock SOK) as SOK00. pose proof (lock CNT) as CNT00. pose proof (lock BA) as BA00.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM. clear HH.
    carve_frame 64%nat ST. set (JJ := junk) in FR. clearbody JJ.
    do 9 zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    change (rw_cells usegs m1 (bv_unsigned sp + -64) (pr_regs s6 s5 s4 s3 s2 s1 s0 ra)) in FR.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) zstep. zstep.
      eapply pr_exit_prefix; [| prr| exact (unlock _ HH00)| exact GR| exact GCR| exact GS| exact PT| exact PN| exact PS| exact QS| exact (unlock _ CNT00)| exact MC2| exact SLO0| exact ACL| exact HTOP| exact DHI| exact (unlock _ MI00)| exact (unlock _ SOK00)| exact MU| exact WM| assumption| assumption| exact FR].
      intros E. exfalso. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate E. }
    assert (LEN1 : 1 <= Z.of_nat (length bs)) by (clear - K0 BL B0; lia). clear K0.
    (* [comment removed for export] *)
    assert (MP1 : mpd_at usegs m1 LB (g_P g)).
    { eapply mpd_at_munch_any; [exact (conj MP PSG)| exact MU| exact WM| rewrite EP; cbn; clear - GS SLO HLS; lia| intros _; cbn; clear - PSL; lia]. }
    pose proof GR as (GHD0 & GAL0 & GPOS0 & _). pose proof (rw_cells_bound _ _ _ _ GHD0) as GB0. unfold grp_head_cells in GB0. cbn [cells_size csize Nat.add] in GB0. clear GHD0.
    zstep. zstep. if_cases KG0; zify_cond KG0; [exfalso; rewrite ?unsigned_lit in KG0 by lia; lia|].
    zstep. zstep. if_cases KG1; zify_cond KG1; [exfalso; rewrite ?unsigned_lit in KG1 by lia; rewrite ?land_7_mod in KG1; lia|].
    zstep. zstep. zstep. zstep. zstep.
    pose proof HSIZE as SZ. unfold mpi_size_stmt in SZ.
    eapply aevtM_cut_evt; [exact MK| eapply SZ with (LB := LB) (dX := g_P g) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
      first [ exact MP1 | exact PP0 | assumption | left; exact PSL | rewrite EP; apply f_equal; lia
            | rewrite EP; clear - GS SLO HLS; lia
            | clear - SPA SPB SLO HLS; lia
            | lia ] |].
    clear SZ. cbv beta. intros ms' PO. unfold mpi_size_post in PO.
    flat constr:(PO) 20%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m1a -> MUa WMa MIa STa.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in MUa, STa by lia.
    replace (ret_pc (Z_to_bv 64 0x387b0)) with (Z_to_bv 64 0x387b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    change ((core_bitlen (md_limbs (g_P g)) (md_n (g_P g)) + 7) / 8) with plen.
    eapply rw_cells_transport in FR; [| exact MUa| exact WMa| cbn; lia].
    assert (MU' : munch [(lo, bv_unsigned sp)] m m1a) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUa]; unfold sub_fp; cbn; clear - SLO HLS; intros; lia]).
    pose proof (wmono_trans _ _ _ _ WM WMa) as WM'. clear MU WM MUa WMa MP1. rename MU' into MU. rename WM' into WM.
    (* [comment removed for export] *)
    assert (GRa : ecp_group_at usegs MT m1a LB G g).
    { eapply ecp_group_at_munch; [exact GR| exact MU| exact WM| exact (unlock _ MI00)| exact MIa| cbn; clear - GS SLO HLS; lia|].
      intros d Hd O. pose proof (grp_blocks_in usegs MT m LB G g d GR Hd O) as IN. flat constr:((proj1 (Forall_forall _ _) HBR _ IN)) 5%nat. intros _ _ _ B4 _. cbn in B4. cbn. lia. }
    flat constr:(GRa) 12%nat. intros _ _ _ _ _ _ _ _ _ _ FLt9 _. flat constr:(FLt9) 6%nat. flclear FLt9. intros EGX EGY _ MGX MGY _.
    flat constr:(MGX) 2%nat. intros CHGX _. rewrite EGX in CHGX. unfold mpi_cells in CHGX.
    flat constr:(MGY) 2%nat. intros CHGY _. rewrite EGY in CHGY. unfold mpi_cells in CHGY. replace (G + 56 + 16) with (G + 72) in CHGY by lia.
    pose proof (mpdr_p_range' _ _ _ _ MGX) as GXR. pose proof (mpdr_p_range' _ _ _ _ MGY) as GYR.
    zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *) zstep. zstep. zstep.
      eapply pr_exit_prefix; [intros _; exact LEN1| prr| exact (unlock _ HH00)| exact GR| exact GCR| exact GS| exact PT| exact PN| exact PS| exact QS| exact (unlock _ CNT00)| exact MC2| exact SLO0| exact ACL| exact HTOP| exact DHI| exact (unlock _ MI00)| exact (unlock _ SOK00)| exact MU| exact WM| exact MIa| exact STa| exact FR]. }
    rewrite ?Z.mod_small in K1 by lia.
    assert (CTX : pr_ctx h LB G Q g cnt (bv_unsigned sp) lo m mo).
    { unfold pr_ctx. (flsplit; repeat match goal with |- _ /\ _ => split end); first [assumption| exact (unlock _ HH00)| exact K1| exact (QG K1)| exact (GQL K1)| exact (unlock _ CNT00)| exact (unlock _ MI00)| exact (unlock _ SOK00)| plia| lia]. }
    assert (STATE0 : pr_state h LB Q (bv_unsigned sp) lo m mo h LB Q (pt_X p) (Q + 16) (pt_Y p) (Q + 32) (pt_Z p) m1a mo).
    { eapply pr_start; [exact CTX| exact PT| exact PN| exact PS| exact MU| exact WM| exact MIa| replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; exact STa]. }
    assert (YN : md_own (pt_Y p) = LNull) by (apply (proj1 (Forall_forall _ _) PN); cbn; auto).
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      assert (BA1 : bytes_at usegs m1a B bs) by (eapply bytes_at_transport; [exact (unlock _ BA00)| exact MU| cbn; clear - BS; lia]).
      eapply pr_mx; [exact CTX| exact STATE0| exact FR| exact TP| rewrite ?Z.mod_small in K2 by lia; exact K2| exact YN| lia| exact BA1| exact B0| exact BL| exact LEN1| exact BCR| exact BS| exact BQ].
    - (* [comment removed for export] *)
      rewrite ?Z.mod_small in K2 by lia. flat constr:((GSW K1 K2)) 6%nat. intros H1 GPS GAS GBS PV PN49.
      eapply pr_sw; [exact CTX| exact STATE0| exact FR| exact TP| exact RAE| exact H1| exact GPS| exact GAS| exact GBS| exact PV| exact PN49| exact YN| exact PLB| exact (unlock _ BA00)| exact B0| exact BL| exact LEN1| exact BCR| exact BS| exact BQ| exact BMC].
  all: match goal with |- ?gg => idtac "MAINLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PR.
