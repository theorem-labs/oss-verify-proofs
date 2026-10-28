(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts CrtFacts RepEcp EcpFacts EcpLoad. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_cmp U_mpi_bitlen U_mpi_copy U_mpi_init U_ecp_red U_ecp_mul_mod U_ecp_sw_rhs.
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
Ltac2 gd_tbl_P_ecp_check_pubkey () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Logic.iff"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_point_at"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.le"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_pt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_h"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_X"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_G"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Y"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_A"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_B"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_freeable"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "bad_point_ok"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "ecp_check_post"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "CK.ck_fin"; "CK.ck_frame"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "U_BAD_POINTS"; "ECP_CHECK_PUBKEY_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "CK.ck_ctx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "CK.ck_st"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "CK.ck_tmp"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.lb_free_mpd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_free.mpi_free_X"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "ECP_INVALID_KEY"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.mm_base"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.mm_inv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.BinInt.Z.to_nat"; "ecp_check_pubkey_stmt"; "U_ECP_CHECK_PUBKEY"].


Definition ECP_CHECK_PUBKEY_STACK : Z := 736.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bad_point_ok (segs : list Segment) (m : mem) (LB : list blk) (BP : Z) (d : mpd) : Prop :=
  mpd_at segs m LB d /\ md_addr d = BP /\ md_own d = LStatic /\ md_sg d = 1.

Definition ecp_check_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (G : Z) (g : ecp_grp) (Q : Z) (p : ecp_pt) (MC lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O20.O1?.O1>.)Lh',(5.O20.O1?.O1>.)(1.(6.$7.)LLB',(6.$7.)(1.$8.Lr,$8.(1.(2.&40.)Lcnt',(2.&40.)(9.(:.$0.R15.(;.(<.(=.O1<.O1;.O1:.O19.R14.R13.R12.O18.O17.(>.&40.R2.)R11.R10.R?.R>.R=.R<.R;.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R:.R9.R8.R7.)O<.(?.O1<.)O;.(10.(2.&40.))R6.(11.O20.))R5.))(9.(12.O20.R6.)(9.(13.O20.R6.O3.(14.&40.O1;.))(9.(15.O1.R5.)(9.(:.$8.(16.O20.O1?.O1>.R4.)(16.O20.O1?.O1>.O:.))(9.(17.O20.O1?.O1>.R4.R3.R6.R5.)(9.Pb,$7.(18.(19.$7.R1.R4.)(19.$7.R1.O9.))(9.(1:.O20.O1?.O9.(14.&40.O1;.)(1;.(1<.$8.$8.)(1=.$8.$8.O4.(1>.O4.+8.))(1?.(1<.$8.$8.)))O2.R6.)(9.(20.O20.O1?.R6.)(9.(21.O20.O1=.R6.R3.O8.O7.)(9.(22.O20.R6.R3.O6.O5.)(9.(23.O20.R6.O4.(1;.$24.(25.R1.)(1?.$24.)))(9.(26.(27.(28.+2.+1?.))R2.)(29.R2.=))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_check_pubkey_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ENTRY MSF MC BP STACK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O9.O8.O7.)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.P,(17.O9.O8.O7.R:.R9.R<.R;.)P,(21.O9.O6.R=.R:.R9.R7.)P,(2>.(9.(:.$8.(2?.R8.)+1.)(9.(30.(:.$8.(31.(32.(33.R8.)))=))(30.(:.$8.(31.(34.(33.R8.)))=))))(9.(:.$8.(2?.R8.)+2.)(:.$8.(31.(34.(33.R8.)))=)))P,(:.$8.(35.(36.R9.))+1.)P,(:.$8.(35.(37.R:.))+1.)P,(:.$8.(35.(38.R;.))+1.)P,(29.+1.(39.(36.R<.)))P,(3:.O8.R10.R8.R?.+<0.)P,(2>.(29.(1>.R10.+<0.)R9.)(29.(14.&40.R34.)R10.))P,(2>.(29.(1>.O3.+8.)R11.)(29.(1>.R11.+<0.)O3.))P,(22.O9.R16.R13.R11.R?.)P,(3;.R10.)P,(3<.$2=.Ld,$2=.(2>.(:.$8.(35.R1.)+1.)(:.$8.(35.R1.)-1.))(3=.R11.))P,(3:.O8.R16.R>.R14.+30.)P,(2>.(29.(1>.R15.+30.)R?.)(29.(14.&40.R3:.)R15.))P,(2>.(29.(1>.O3.+8.)R16.)(29.(1>.R16.+30.)O3.))P,(23.O9.R1<.O3.(1;.$24.(25.R14.)(1?.$24.)))P,(29.(3>.O8.)O3.)P,(29.(1>.O3.+8.)(3?.O8.))P,Pa,$8.P,(9.(29.O3.R1.)(26.R1.(1>.O3.+8.)))(9.(30.(40.O8.R2.))(41.O8.R2.))P,(42.O9.R20.R1=.O2.R17.)P,(42.O9.R21.R1>.(1>.O2.+10.)R17.)P,(29.(3>.O8.)O2.)P,(29.(1>.O2.+20.)(3?.O8.))P,Pa,$8.P,(9.(29.O2.R1.)(26.R1.(1>.O2.+20.)))(30.(40.O8.R2.))P,(2>.(29.(1>.O3.+8.)O2.)(29.(1>.O2.+20.)O3.))P,(13.O9.R26.R1;.(14.&40.R46.))P,(29.R1<.(43.(43.(14.&40.R47.)O1.)(44.O8.)))P,(29.(45.O8.)R1=.)P,(29.(14.&40.R49.)(16.O9.O8.O7.R27.))P,(:.$8.(46.(14.&40.R4:.)+10.)=)P,(29.(3?.O8.)(45.O8.))P,(:.(2.&40.)R4:.(>.&40.(47.O8.)))P,(12.O9.R2=.)P,(20.O9.O8.R2>.)P,(48.O8.O4.+8.)P,(:.(2.&40.)R48.(>.&40.R2<.))P,(:.(2.&40.)R48.(>.&40.R2<.))(49.O9.R31.(4:.O9.O8.O7.O6.R53.R52.R51.R50.R4<.R4;.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R34.R33.R30.R2?.R2>.R2<.R2=.R2;.O3.R27.R32.R31.)(<.(=.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.)R34.(>.&40.O5.)R33.(10.(2.&40.))R32.(11.O9.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Section PtFacts.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L11566628249.23L11823099573.29L15045276710.23L22286000554.31L23449151355.23L31818516631.23L44015346570.23L65502017674.23L65703598181.29L67634573947.2300000300>00?00S00T00U00V00W00b00cS1QS1Q3off3Ho2SS1Q3off3Ho13Ho21a2HxSSSSS1Q3off3Ho1S". (* [comment removed for export] *)
  #[using="Type"] Lemma ecp_point_at_presx : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(6.$7.)PLB',(6.(1<.$8.$8.))PSP,$8.PX,(6.$4;.)PQ,$8.Pp,$2<.P,(22.Vsegs,R8.R6.R2.R1.)P,(1:.Vsegs,VL,R7.R5.R4.R9.R8.)P,(12.Vsegs,R:.)P,(12.Vsegs,R:.)P,(3:.VL,R:.R8.R6.+30.)P,(4<.R8.R7.+30.)P,Pd,$2=.P,(19.$2=.R1.(3=.R8.))P,(:.$4=.(4>.R2.)$4?.)(9.(19.(1<.$8.$8.)(1=.$8.$8.(31.R3.)(50.+4.(51.R3.)))R>.)(4<.R<.(31.R3.)(50.+4.(51.R3.))))(22.Vsegs,R>.R<.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    (intros m m' LB LB' SP X Q p dd_H; ddestruct dd_H as (EX & EY & EZ & MX & MY & MZ); intros PX MI MI' CR DX HP).
    assert (ST : forall d off, In d (pt_mpds p) -> md_addr d = Q + off -> 0 <= off -> off + 16 <= 48 -> mpdr_at segs m LB d -> mpdr_at segs m' LB' d).
    { intros d off Hd Ha Ho1 Ho2 HDd. apply (mpdr_at_LB_one segs) with (LB := LB); [| intros O; exact (proj1 (HP d Hd O))].
      eapply (mpdr_at_presx segs L); [exact HDd| exact PX| exact MI| exact MI'| | |].
      - rewrite Ha. intros a Hx; apply CR; lia.
      - rewrite Ha. eapply disjoint_from_sub; [exact DX| lia| lia].
      - intros O. split; [| exact (proj2 (HP d Hd O))]. ddestruct HDd as (_ & _ & _ & _ & _ & HO). rewrite O in HO. exact (proj1 (proj2 HO)). }
    refine (conj EX (conj EY (conj EZ _))).
    split; [apply (ST _ 0); [cbn; auto| rewrite EX; lia| lia| lia| exact MX]|].
    split; [apply (ST _ 16); [cbn; auto| exact EY| lia| lia| exact MY]|].
    apply (ST _ 32); [cbn; auto| exact EZ| lia| lia| exact MZ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PtFacts.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L41691758847.10L41698164036.9 L53519157932.6 00000?00J00MS1d2HL2N12P02B1S1d2HL2N11HS1d". (* [comment removed for export] *)
Lemma mpdr_p_range : forall segs m LB d, mpdr_at segs m LB d -> 0 <= md_p d < 2^64.
Proof.
  (intros segs m LB d dd_H; ddestruct dd_H as (_ & _ & _ & HL & HN & HO)). destruct (md_own d).
  - destruct HO as [-> _]. lia.
  - ddestruct HO as (N1 & _ & _ & U). pose proof (u32arr_bound _ _ _ _ U). lia.
  - ddestruct HO as (N1 & _ & P0 & (B0 & B1 & _) & _). rewrite u32s_length in B1. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition U_ECP_CHECK_PUBKEY : Z := 0x3a120.
Notation U_MUL_COUNT := 380840 (only parsing).
Definition U_BAD_POINTS : Z := 0x48f20.
Definition ECP_INVALID_KEY : Z := -0x4C80.

Section CK.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Variable MT : list modp_ent.
  Hypothesis HMM : ecp_mul_mod_stmt usegs L HI MT 0x3a8f4 U_MEMSET_FUNC U_MUL_COUNT ECP_MUL_MOD_STACK.
  Hypothesis HSR : ecp_sw_rhs_stmt usegs L HI MT 0x3a7a4 U_MEMSET_FUNC U_MUL_COUNT ECP_SW_RHS_STACK.
  Hypothesis HINIT : mpi_init_stmt usegs 0x1f488.
  Hypothesis HFREEM : mpi_free_stmt usegs L HI 0x1f4a8 U_MEMSET_FUNC.
  Hypothesis HCOPY : mpi_copy_stmt usegs L HI 0x1f638 U_MEMSET_FUNC.
  Hypothesis HSUBM : mpi_sub_mpi_stmt usegs L HI 0x20b04 U_MEMSET_FUNC.
  Hypothesis HADDI : mpi_add_int_stmt usegs L HI 0x1fd60 U_MEMSET_FUNC.
  Hypothesis HCMP : mpi_cmp_mpi_stmt usegs 0x202a4.
  Hypothesis HCMPI : mpi_cmp_int_stmt usegs 0x2044c.
  Hypothesis HSIZE : mpi_size_stmt usegs 0x1fb84.

  Definition ck_frame (s4e s3e s2e s1e s0e rae : word) : list cell := [C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae].

  (* [comment removed for export] *)
  Definition ck_fin (h : HST usegs L HI) (LB : list blk) (G : Z) (g : ecp_grp) (Q : Z) (p : ecp_pt) (SP lo : Z) (m : mem) (mo : Model)
      (h' : HST usegs L HI) (LB' : list blk) (m' : mem) (mo' : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "(9.(12.$52.O2.)(9.(13.$52.O2.O7.(43.O8.+50.))(9.(15.O5.O1.)(9.(:.$8.(16.$52.VL,VHI,O4.)(16.$52.VL,VHI,O>.))(9.(17.$52.VL,VHI,O4.O3.O2.O1.)(9.Pb,$7.(18.(19.$7.R1.O3.)(19.$7.R1.O=.))(9.(1:.$52.VL,O=.O8.(1;.(1<.$8.$8.)(1=.$8.$8.+5<?:8.(1>.+5<?:8.+8.))(1?.(1<.$8.$8.)))O6.O2.)(9.(20.$52.VL,O2.)(9.(21.$52.VMT,O2.O3.O<.O;.)(9.(22.$52.O2.O3.O:.O9.)(1.(2.&40.)Lc,(2.&40.)(23.$52.O2.+5<?:8.(1;.$24.(25.R1.)(1?.$24.))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac norm_ret :=
    match goal with |- context [Z_to_bv 64 (Z.land ?a ?b)] =>
      let v := eval vm_compute in (Z.land a b) in
      let w := eval vm_compute in (if v <? 2^63 then v else v - 2^64) in
      replace (Z_to_bv 64 (Z.land a b)) with (Z_to_bv 64 w) by (apply bv_eq; vm_compute; reflexivity)
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L11542269846.91L12642320717.91L13100768790.91L14471356349.88L3209619816.89 L35628693890.89L39032623430.88L44109073686.91L49236136086.91L54613153071.90L58130694033.89L8869413654.91 00000900B00K00T00b00k01401=01F01W01h021S3spv3LOCS3spv3LOCS3spv3LOCS3spv3LOCS3spv3LOC4LOCLS3spv3LOCS3spv3LOCS3spv3LOCS3spv3LOCS3spv2lo3LOC4LOSPS3spv2lo3LOC4LOSPS3spv3LOC". (* [comment removed for export] *)
  #[using="Type"] Lemma ck_exit : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Prae,(2.&40.)Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0e,(2.&40.)Ps1e,(2.&40.)Ps2e,(2.&40.)Ps3e,(2.&40.)Ps4e,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pra0,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0c,(2.&40.)Ps1c,(2.&40.)Ps2c,(2.&40.)Ps3c,(2.&40.)Ps4c,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.Pg,$2;.PQ,$8.Pp,$2<.Plo,$8.Ph1,(5.$52.VL,VHI,)PLB1,(6.$7.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$4.Pr,$8.PLOC,(6.$24.)P,(53.R=.R<.R;.R:.R9.R8.(14.&40.R34.)R7.R?.R>.R6.R5.R4.R3.)P,(23.$52.R5.(1>.(14.&40.R35.)-30.)(54.R2>.R2?.R30.R31.R32.R36.))P,(23.$52.R6.(1>.(14.&40.R36.)-50.)R3.)P,(:.$8.(55.(56.R4.))+20.)P,(29.(1>.R;.+50.)(14.&40.R38.))P,(9.(26.(27.(28.+2.+1?.))R7.)(29.R7.=))(49.$52.R9.(4:.$52.VL,VHI,VMT,R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R17.R16.R13.R12.R11.R10.R?.R>.+5<?:8.R=.R15.R14.)(<.(=.R2;.(>.&40.(1>.(14.&40.R3:.)-50.))R39.R38.R2:.R29.R28.R27.R26.(>.&40.R8.)R22.R21.R20.R1?.R1>.R1=.R1<.R25.R24.R23.R32.R31.R30.R2?.R2>.R2=.R2<.R1;.R1:.R19.R18.)R17.(>.&40.+3:168.)R16.(10.(2.&40.))R:.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until LOC. intros FIN FR LOCC LOCL LOSP Hr.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    ddestruct FIN as (MI1 & ST1 & MF1 & HT1 & HH1 & EQB & PX1 & SOK1 & GR1 & PT1 & [cnt1 CNT1]).
    replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) in ST1 by lia. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    unfold ck_frame in FR.
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame LOCC ST1 (bv_unsigned spv + -48). release_frame FR ST1 (bv_unsigned spv). zstep.
    try (replace (bv_unsigned spv + -80 + 80) with (bv_unsigned spv) by lia; rewrite (Z_to_bv_bv_unsigned spv)). zstep.
    apply aevtM_done. unfold ecp_check_post.
    deexists 14. dexists m1, mo1, h1, LB1, r, cnt1.
    split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact MF1|]. split; [exact HT1|].
    split; [exact HH1|]. split; [exact EQB|]. split; [exact PX1|]. split; [exact SOK1|]. split; [exact GR1|]. split; [exact PT1|]. split; [exact CNT1| exact Hr].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L11326368644.61L11332490680.56L22706553362.53L35561850065.51L3818389621.51 L54282829003.51L54391891673.54L8113800070.51 00000A00S00o01;01E01Q01i02DS1L2SP2lo3ACL1d1HS1L2SP2lo3ACL1d2B4S1L4DIMG4IMGC2SP2lo3ACL1a2HaS1G2SP2lo2GSS1L2lo3ACLS1Q2SP2lo2QSS1L2HI1h2SP2lo4HTOP1a2NOS1L4DIMG4IMGC2SP2lo3MC23ACL". (* [comment removed for export] *)
  #[using="DIMG IMGC"] Lemma ck_fin_prefix : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.Pg,$2;.PQ,$8.Pp,$2<.PSP,$8.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pm1,P,(2.&40.)(3.(2.&8.))Pcnt,(2.&40.)P,(17.$52.VL,VHI,R<.R;.R4.R3.)P,(21.$52.VMT,R5.R<.R;.R:.)P,(22.$52.R6.R=.R:.R9.)P,(23.$52.R7.+5<?:8.(1;.$24.(25.R4.)(1?.$24.)))P,(20.$52.VL,R8.)P,(12.$52.R9.)P,(12.$52.R8.)P,(3:.VL,R12.R<.R11.+<0.)P,(2>.(29.(1>.R12.+<0.)R=.)(29.R>.R12.))P,(3:.VL,R14.R>.R11.+30.)P,(2>.(29.(1>.R12.+30.)R?.)(29.R10.R12.))P,(29.(1>.+5<?:8.+8.)(3?.VL,))P,(29.(3?.VL,)(45.VL,))P,(29.(45.VL,)R12.)P,(29.R13.(43.R14.+50.))P,(29.R15.(16.$52.VL,VHI,R1;.))P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.R15.R16.)(1?.(1<.$8.$8.)))R14.R12.)P,(58.$52.R15.R13.)P,(13.$52.R14.R17.(43.R18.+50.))(53.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R1?.R1>.R15.R16.)")
(* [comment removed for export] *).
  Proof.
    intros h LB G g Q p SP lo m mo m1 cnt HH GR PT CNT SOK MI MI1 GCR GS QCR QS MC2 DHI ACL SLO HTOP MU WM ST1.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    assert (BL : forall d (mm : mem) LBx, mpdr_at usegs mm LBx d -> LBx = LB -> md_own d = LHeap -> md_p d + 4 * md_n d <= alloc_ceiling).
    { intros d mm LBx HD -> O. ddestruct HD as (_ & _ & _ & _ & _ & HO). rewrite O in HO. ddestruct HO as (_ & IN & _).
      pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (_ & _ & _ & B4 & _). exact B4. }
    unfold ck_fin. refine (conj MI1 (conj ST1 (conj (mo_frame_refl mo) (conj eq_refl (conj _ (conj (fun b => iff_refl _) (conj _ (conj _ (conj _ (conj _ _)))))))))).
    - apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia.
    - eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia].
    - eapply statics_ok_munch; [exact SOK| exact MU| intros a Ha _; cbn; lia].
    - eapply ecp_group_at_munch; [exact GR| exact MU| exact WM| exact MI| exact MI1| cbn; lia|].
      intros d Hd O. pose proof (grp_blocks_in usegs MT m LB G g d GR Hd O) as IN. pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (_ & _ & _ & B4 & _). cbn in B4. cbn. lia.
    - eapply ecp_point_at_munch; [exact PT| exact MU| exact WM| exact MI| exact MI1| cbn; lia|].
      intros d Hd O. ddestruct PT as (EX & EY & EZ & MX & MY & MZ).
      assert (HD : mpdr_at usegs m LB d) by (cbn in Hd; destruct Hd as [<-|[<-|[<-|[]]]]; assumption).
      pose proof (BL d m LB HD eq_refl O). cbn. lia.
    - exists cnt. eapply rw_cells_transport; [exact CNT| exact MU| exact WM| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ck_ctx (h : HST usegs L HI) (LB : list blk) (G Q : Z) (g : ecp_grp) (p : ecp_pt) (cnt : word) (bp1 bp2 : mpd) (SP lo : Z) (m : mem) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "(9.(17.$52.VL,VHI,O=.O<.O2.O1.)(9.(21.$52.VMT,O2.O<.O;.O9.)(9.(2>.(9.(:.$8.(2?.O9.)+1.)(9.(30.(:.$8.(31.(32.(33.O9.)))=))(30.(:.$8.(31.(34.(33.O9.)))=))))(9.(:.$8.(2?.O9.)+2.)(:.$8.(31.(34.(33.O9.)))=)))(9.(:.$8.(35.(36.O9.))+1.)(9.(:.$8.(35.(37.O9.))+1.)(9.(:.$8.(35.(38.O9.))+1.)(9.(29.+1.(39.(36.O9.)))(9.(3:.VL,O<.O3.O;.+<0.)(9.(2>.(29.(1>.O;.+<0.)O3.)(29.O4.O;.))(9.(2>.(29.(1>.+5<?:8.+8.)O;.)(29.(1>.O;.+<0.)+5<?:8.))(9.(22.$52.O2.O<.O:.O8.)(9.(3;.O8.)(9.(3<.$2=.Ld,$2=.(2>.(:.$8.(35.R1.)+1.)(:.$8.(35.R1.)-1.))(3=.O8.))(9.(3:.VL,O<.O3.O:.+30.)(9.(2>.(29.(1>.O:.+30.)O3.)(29.O4.O:.))(9.(2>.(29.(1>.+5<?:8.+8.)O:.)(29.(1>.O:.+30.)+5<?:8.))(9.(23.$52.O2.+5<?:8.(1;.$24.(25.O7.)(1?.$24.)))(9.(29.(3>.VL,)+5<?:8.)(9.(29.(1>.+5<?:8.+8.)(3?.VL,))(9.Pa,$8.P,(9.(29.+5<?:8.R1.)(26.R1.(1>.+5<?:8.+8.)))(9.(30.(40.VL,R2.))(41.VL,R2.))(9.(42.$52.O2.O<.$59.O6.)(9.(42.$52.O2.O<.(1>.$59.+10.)O5.)(9.(29.(3>.VL,)$59.)(9.(29.(1>.$59.+20.)(3?.VL,))(9.Pa,$8.P,(9.(29.$59.R1.)(26.R1.(1>.$59.+20.)))(30.(40.VL,R2.))(9.(2>.(29.(1>.+5<?:8.+8.)$59.)(29.(1>.$59.+20.)+5<?:8.))(9.(29.O3.(43.(43.O4.$5:.)(44.VL,)))(9.(29.(45.VL,)O3.)(9.(29.O4.(16.$52.VL,VHI,O=.))(9.(:.$8.(46.O4.+10.)=)(9.(29.(3?.VL,)(45.VL,))(9.(12.$52.O2.)(9.(20.$52.VL,O2.)(9.(48.VL,$5;.+8.)(26.O4.(28.+2.+40.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L11326368644.47L11332774272.45L25500434712.46L30618040681.53L31366167927.47L31366167927.54L8927507745.53 00000;00G00R00\00j01A01QS2SP2lo1d1HS2SP2lo1d2SDS1L1d2I32I4S1d2N13PB1S1L2lo1d3ACL1HS1L4IMGC2lo1d3ACL3PB11HS1d2HL2N12P03PB1". (* [comment removed for export] *)
  #[using="ROIMG IMGC"] Lemma ck_now : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.PSP,$8.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pm1,P,(2.&40.)(3.(2.&8.))Pd,$2=.P,(5<.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.R6.R7.)(1?.(1<.$8.$8.)))R5.R3.)P,(58.$52.R6.R4.)P,(12.$52.R5.)P,(5=.$52.R8.R12.R5.)P,(2>.(29.(1>.(5>.R6.)+10.)R:.)(29.R;.(5>.R6.)))(9.(5=.$52.R8.R14.R7.)(9.P,(:.$4=.(4>.R7.)$4?.)(9.(26.=(31.R8.))(29.(1>.(31.R8.)(50.+4.(51.R8.)))(45.VL,)))P,(30.(:.$4=.(4>.R7.)$5?.))(2>.(29.(1>.(31.R8.)(50.+4.(51.R8.)))R<.)(29.R=.(31.R8.)))))")
(* [comment removed for export] *).
  Proof.
    intros h LB G Q g p cnt bp1 bp2 SP lo m mo m1 d CTX MU WM MI1 MD SD.
    ddestruct CTX as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ACL & _ & _ & DHI & MI & _).
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    assert (BL : md_own d = LHeap -> 0 < md_p d /\ md_p d + 4 * md_n d <= alloc_ceiling).
    { intros O. ddestruct (mpdr_blk_facts usegs L m LB d (proj1 MD) O HBR) as (_ & _ & I3 & I4 & _). lia. }
    assert (SL : md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ SP <= md_p d).
    { intros NN. destruct (md_own d) eqn:O; [exfalso; congruence| left; pose proof (BL eq_refl); lia|].
      pose proof MD as [(_ & _ & _ & HL & HN & HO) _]. rewrite O in HO. ddestruct HO as (N1 & _ & P0 & PB & PRO). dpose PB as (_ & PB1 & _). rewrite u32s_length in PB1.
      pose proof (ROIMG _ (PRO (4 * md_n d - 1) ltac:(lia)) ltac:(lia)). left. lia. }
    split; [| exact (conj BL SL)].
    eapply mpd_at_munch_any; [exact MD| exact MU| exact WM| cbn; lia| intros NN; pose proof (SL NN); cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L11332490680.57L11332490680.62L35559588815.52L54284827605.52L54391891673.55L8115733656.52 00000B00T00`00l01D01_S1L2SP2lo3ACL1d2B4S1L2SP2lo3ACL1d2B4S1G2SP2lo2GSS1Q2SP2lo2QSS1L2HI1h2SP2lo4HTOP1a2NOS1L4DIMG4IMGC2SP2lo3MC23ACL". (* [comment removed for export] *)
  #[using="DIMG IMGC"] Lemma ck_now_env : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.PSP,$8.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pm1,P,(2.&40.)(3.(2.&8.))P,(5<.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.R5.R6.)(1?.(1<.$8.$8.)))R4.R2.)P,(58.$52.R5.R3.)P,(12.$52.R4.)(9.(21.$52.VMT,R5.R11.R10.R>.)(9.(22.$52.R5.R11.R?.R=.)(9.(23.$52.R5.+5<?:8.(1;.$24.(25.R<.)(1?.$24.)))(17.$52.VL,VHI,R12.R11.R5.R6.))))")
(* [comment removed for export] *).
  Proof.
    intros h LB G Q g p cnt bp1 bp2 SP lo m mo m1 CTX MU WM MI1.
    dpose CTX as (HH & GR & _ & _ & _ & _ & _ & GCR & GS & _ & PT & _ & _ & QCR & QS & _ & CNT & _ & MC2 & _ & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & _ & DHI & MI & SOK & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    split; [| split; [| split]].
    - eapply ecp_group_at_munch; [exact GR| exact MU| exact WM| exact MI| exact MI1| cbn; lia|].
      intros d Hd O. pose proof (grp_blocks_in usegs MT m LB G g d GR Hd O) as IN. pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (_ & _ & _ & B4 & _). cbn in B4. cbn. lia.
    - eapply ecp_point_at_munch; [exact PT| exact MU| exact WM| exact MI| exact MI1| cbn; lia|].
      intros d Hd O. ddestruct PT as (EX & EY & EZ & MX & MY & MZ).
      assert (HD : mpdr_at usegs m LB d) by (cbn in Hd; destruct Hd as [<-|[<-|[<-|[]]]]; assumption).
      ddestruct HD as (_ & _ & _ & _ & _ & HO). rewrite O in HO. ddestruct HO as (_ & IN & _).
      pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (_ & _ & _ & B4 & _). cbn in B4. cbn. lia.
    - eapply rw_cells_transport; [exact CNT| exact MU| exact WM| cbn; lia].
    - apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L10580084904.99 L22700267513.119L26056220003.117L26058315139.99 L3622085641.7   L3818669308.99  L46730941986.101L53136083296.100L63259770561.99 L67487075099.7  L67491449090.10200000M01001_02N02[02m03<03c04V04W04gS1L3HLS2lo3RET3spv2HR3SPB3SLOS1L3HLS2lo3RET3spv2HR3SPB3SLO3x131HS1L3HLS4DIMG4IMGC2lo3RET3spv2HR3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC2lo3RET3spv2HR3SPB3MC23SLO3ACLS2lo1d3spv2SDS1L2lo3RET3spv3ACLS1L1d3RET3spv1HS1L4DIMG4IMGC2lo3RET3spv2HR3SPB3MC23ACLS1L3HLS4DIMG4IMGC2lo3RET3spv2HR3SPB3MC23SLO3ACL3SPAFS2lo1d3RET3spv1H". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HCMPI"] Lemma ck_pre_cmpint : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pm1,P,(2.&40.)(3.(2.&8.))Pd,$2=.Pz,$8.PRET,$8.Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)PQ',P,$0.SpP,(5<.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.(14.&40.R21.)R28.R27.R26.)P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.R29.(14.&40.R22.))(1?.(1<.$8.$8.)))R28.R26.)P,(58.$52.R29.R27.)P,(12.$52.R28.)P,(13.$52.R29.R2<.(1>.(14.&40.R25.)-50.))P,(5=.$52.R2<.R35.R29.)P,(2>.(29.(1>.(5>.R2:.)+10.)R2>.)(29.(14.&40.R27.)(5>.R2:.)))P,(9.(29.(27.(28.+2.+1?.))R2:.)(26.R2:.(28.+2.+1?.)))P,(9.(29.=R2:.)(26.R2:.(28.+2.+40.)))P,(:.$8.(46.R2;.+2.)=)P,(:.(2.&40.)R23.(>.&40.(5>.R2>.)))P,(:.(2.&40.)R23.(>.&40.R2>.))P,Pm2,P,(2.&40.)(3.(2.&8.))Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.R43.(14.&40.R3<.))(1?.(1<.$8.$8.)))R42.R?.)P,(58.$52.R43.R10.)P,(12.$52.R11.)P,(13.$52.R12.R46.(1>.(14.&40.R3?.)-50.))P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.(43.(1>.(14.&40.R40.)-50.)+20.)(1>.(14.&40.R40.)-50.))(1?.(1<.$8.$8.)))R44.R13.)P,(58.$52.R45.R14.)(49.$52.R47.R22.(<.(=.(>.&40.R43.)(>.&40.(1>.(14.&40.R42.)-50.))R41.R40.R14.R13.R12.R3<.R3;.(>.&40.(60.(43.(39.R45.)R44.)))R11.R10.R?.R>.R=.R<.R;.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R:.R9.R8.R7.)R24.(>.&40.R43.)R23.(10.(2.&40.))R15.(11.$52.)))(49.$52.R33.R>.(<.(=.(>.&40.R2?.)(>.&40.(1>.(14.&40.R2>.)-50.))R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(>.&40.+2044<.)R?.(10.(2.&40.))R32.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until Q'. intros CTX MU WM MI1 ST1 MD SD HZ HR HRE -> -> K. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose CTX as (HH & GR & _ & _ & _ & _ & _ & GCR & GS & _ & PT & _ & _ & QCR & QS & _ & CNT & _ & MC2 & _ & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & SPA & DHI & MI & SOK & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    destruct (ck_now _ _ _ _ _ _ _ _ _ _ _ _ _ m1 d CTX MU WM MI1 MD SD) as (MD1 & BL & SL).
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof HCMPI as SC. unfold mpi_cmp_int_stmt in SC.
    eapply aevtM_cut_evt; [exact MK| eapply SC with (LB := LB) (dX := d) (z := z) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned spv + -80)) by lia;
      first [ exact MD1 | exact MI1 | exact ST1 | exact HZ | reflexivity
            | intros O; pose proof (BL O); lia
            | match goal with |- _ \/ _ => first [ clear - SD SLO HLS; lia
                                                 | pose proof MD as [(_ & _ & _ & _ & _ & HO) _]; destruct (md_own d) eqn:O;
                                                   [destruct HO as [-> ->]; left; lia| pose proof (SL ltac:(congruence)); lia| pose proof (SL ltac:(congruence)); lia] ] end
            | lia ] |].
    clear SC. cbv beta. intros ms' PO. unfold mpi_cmp_int_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc).
    rewrite ?(unsigned_lit (bv_unsigned spv + -80)) in MUc, STc by lia.
    rewrite (ret_pc_even RET HR HRE).
    eapply K; [| | exact MIc| exact STc| exact MUc| exact WMc].
    - eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn; intros; lia].
    - eapply wmono_trans; [exact WM| exact WMc].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L25365203235.85L46730941986.8500000;00FS1L1e3RET1HS1L1d3RET1H". (* [comment removed for export] *)
  #[using="ROIMG IMGC HCMP"] Lemma ck_pre_cmp : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pm1,P,(2.&40.)(3.(2.&8.))Pd,$2=.Pe,$2=.PRET,$8.Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)PQ',P,$0.SpP,(5<.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.(14.&40.R21.)R28.R27.R26.)P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.R29.(14.&40.R22.))(1?.(1<.$8.$8.)))R28.R26.)P,(58.$52.R29.R27.)P,(12.$52.R28.)P,(5=.$52.R2;.R34.R28.)P,(2>.(29.(1>.(5>.R29.)+10.)R2=.)(29.(14.&40.R26.)(5>.R29.)))P,(5=.$52.R2=.R36.R29.)P,(2>.(29.(1>.(5>.R2:.)+10.)R2?.)(29.(14.&40.R28.)(5>.R2:.)))P,(9.(29.=R2:.)(26.R2:.(28.+2.+40.)))P,(:.$8.(46.R2;.+2.)=)P,(:.(2.&40.)R23.(>.&40.(5>.R2>.)))P,(:.(2.&40.)R23.(>.&40.(5>.R2>.)))P,Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)(49.$52.R40.R1;.(<.(=.(>.&40.R3<.)(>.&40.(1>.(14.&40.R3;.)-50.))R3:.R39.R>.R=.R<.R35.R34.(>.&40.(60.(43.(39.R3>.)(39.R3=.))))R;.R:.R9.R8.R7.R6.R5.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R4.R3.R2.R1.)R1=.(>.&40.R3<.)R1<.(10.(2.&40.))R3?.(11.$52.)))(49.$52.R33.R>.(<.(=.(>.&40.R2?.)(>.&40.(1>.(14.&40.R2>.)-50.))R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(>.&40.+202:4.)R?.(10.(2.&40.))R32.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until Q'. intros CTX MU WM MI1 MD SD ME SE HR HRE -> -> K.
    pose proof CTX as (HH & _).
    destruct (ck_now _ _ _ _ _ _ _ _ _ _ _ _ _ m1 d CTX MU WM MI1 MD SD) as (MD1 & BLd & _).
    destruct (ck_now _ _ _ _ _ _ _ _ _ _ _ _ _ m1 e CTX MU WM MI1 ME SE) as (ME1 & BLe & _).
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof HCMP as SC. unfold mpi_cmp_mpi_stmt in SC.
    eapply aevtM_cut_evt; [exact MK| eapply SC with (LB := LB) (dX := d) (dY := e); [exact MD1| exact ME1| intros O; pose proof (BLd O); lia| intros O; pose proof (BLe O); lia| exact MI1| reflexivity| reflexivity] |].
    clear SC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & _).
    rewrite (ret_pc_even RET HR HRE). apply K.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L35628693773.95L52992180477.95L58193879266.9500000900O00eS3spv3LOCS1L3HLS3spv2lo3LOC3SLOS1L3HLS3spv2lo3LOC3SLO". (* [comment removed for export] *)
  #[using="HLS DIMG IMGC"] Lemma ck_exit_prefix : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Prae,(2.&40.)Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0e,(2.&40.)Ps1e,(2.&40.)Ps2e,(2.&40.)Ps3e,(2.&40.)Ps4e,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pra0,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0c,(2.&40.)Ps1c,(2.&40.)Ps2c,(2.&40.)Ps3c,(2.&40.)Ps4c,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Pm1,P,(2.&40.)(3.(2.&8.))Pr,$8.PLOC,(6.$24.)P,(5<.R=.R<.R;.R:.R9.R8.R7.R6.R5.(14.&40.R34.)R4.R?.R>.)P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.R5.(14.&40.R35.))(1?.(1<.$8.$8.)))R10.R4.)P,(58.$52.R11.R5.)P,(12.$52.R6.)P,(13.$52.R7.R8.(1>.(14.&40.R38.)-50.))P,(23.$52.R8.(1>.(14.&40.R39.)-30.)(54.R32.R33.R34.R35.R36.R3:.))P,(23.$52.R9.(1>.(14.&40.R3:.)-50.)R7.)P,(:.$8.(55.(56.R8.))+20.)P,(9.(26.(27.(28.+2.+1?.))R:.)(29.R:.=))(49.$52.R17.(4:.$52.VL,VHI,VMT,R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R1:.R19.R16.R15.R14.R12.R13.R11.+5<?:8.R=.R18.R17.)(<.(=.R2>.(>.&40.(1>.(14.&40.R3=.)-50.))R3<.R3;.R2=.R2<.R2;.R2:.R29.(>.&40.R;.)R25.R24.R23.R22.R21.R20.R1?.R28.R27.R26.R35.R34.R33.R32.R31.R30.R2?.R1>.R1=.R1<.R1;.)R1:.(>.&40.+3:168.)R19.(10.(2.&40.))R<.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until LOC. intros CTX MU WM MI1 ST1 FR LOCC LOCL Hr.
    dpose CTX as (HH & GR & _ & _ & _ & _ & _ & GCR & GS & _ & PT & _ & _ & QCR & QS & _ & CNT & _ & MC2 & _ & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & _ & DHI & MI & SOK & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    eapply ck_exit; [| exact FR| exact LOCC| exact LOCL| lia| exact Hr].
    eapply ck_fin_prefix; [exact HH| exact GR| exact PT| exact CNT| exact SOK| exact MI| exact MI1| exact GCR| exact GS| exact QCR| exact QS| exact MC2| exact DHI| exact ACL| lia| exact HTOP| exact MU| exact WM|].
    replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia. exact ST1.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ck_st (h : HST usegs L HI) (LB : list blk) (SP lo : Z) (m : mem) (mo : Model)
      (hk : HST usegs L HI) (LBk : list blk) (mk : mem) (mok : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "(9.(17.$52.VL,VHI,O4.O3.O2.O1.)(9.Pb,$7.P,(19.$7.R1.O9.)(19.$7.R2.O3.)(9.(1:.$52.VL,O9.O8.(1;.(1<.$8.$8.)(1=.$8.$8.+5<?:8.(1>.+5<?:8.+8.))(1?.(1<.$8.$8.)))O6.O2.)(9.(20.$52.VL,O2.)(9.(12.$52.O2.)(9.(15.O5.O1.)(9.(:.$8.(16.$52.VL,VHI,O4.)(16.$52.VL,VHI,O:.))(9.(1.(2.&40.)Lc,(2.&40.)(23.$52.O2.+5<?:8.(1;.$24.(25.R1.)(1?.$24.))))(13.$52.O2.O7.(43.O8.+50.))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition ck_tmp (LB LBk : list blk) (mk : mem) (A : Z) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "(9.(5=.$52.O3.O4.O1.)(9.(:.$8.(5>.O1.)O2.)(9.(30.(:.$4=.(4>.O1.)$61.))Pb,$7.P,(19.$7.R1.(62.O1.))(30.(19.$7.R2.O5.)))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L22706553362.55L3820652395.53 L54391891673.56L8115733656.53 00000L00V00n01IS1L4DIMG4IMGC2SP2lo3ACL1a2HaS1L2lo3ACLS1L2HI1h2SP2lo4HTOP1a2NOS1L4DIMG4IMGC2SP2lo3MC23ACL". (* [comment removed for export] *)
  #[using="DIMG IMGC"] Lemma ck_st_prefix : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.PSP,$8.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pm1,P,(2.&40.)(3.(2.&8.))P,(5<.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.R5.R6.)(1?.(1<.$8.$8.)))R4.R2.)P,(58.$52.R5.R3.)P,(12.$52.R4.)P,(13.$52.R5.R8.(43.R9.+50.))(63.R13.R12.R:.R9.R8.R7.R13.R12.R6.R7.)")
(* [comment removed for export] *).
  Proof.
    intros h LB G Q g p cnt bp1 bp2 SP lo m mo m1 CTX MU WM MI1 ST1.
    dpose CTX as (HH & GR & _ & _ & _ & _ & _ & GCR & GS & _ & PT & _ & _ & QCR & QS & _ & CNT & _ & MC2 & _ & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & _ & DHI & MI & SOK & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    unfold ck_st. refine (conj _ (conj (fun b Hb => Hb) (conj _ (conj _ (conj MI1 (conj (mo_frame_refl mo) (conj eq_refl (conj _ ST1)))))))).
    - apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia.
    - eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia].
    - eapply statics_ok_munch; [exact SOK| exact MU| intros a Ha _; cbn; lia].
    - exists cnt. eapply rw_cells_transport; [exact CNT| exact MU| exact WM| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L59308743383.39L59310678513.3500000R01=S1L2lo1a3lo'3hi'3ACL1B1j1X2H11C2B4S2SP1a3lo'3hi'1X2H21C1L4DIMG4IMGC2lo3ACL2H1". (* [comment removed for export] *)
  #[using="DIMG IMGC"] Lemma ck_out_stack : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PSP,$8.Plo,$8.Pa,$8.Plo',$8.Phi',$8.P,(17.$52.VL,VHI,R9.R8.R7.R6.)P,(29.(45.VL,)R5.)P,(29.(3?.VL,)(45.VL,))P,(64.VL,R;.R8.R6.)P,(29.R8.R6.)P,(29.R6.R:.)(30.(9.(29.R8.R9.)(26.R9.R7.)))")
(* [comment removed for export] *).
  Proof.
    intros h LB m mo SP lo a lo' hi' HH ACL DHI HC H1 H2 C. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    destruct HC as [X|[X|([B j] & Hb & X)]]; [lia| lia|].
    pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (_ & _ & _ & B4 & _). cbn in X, B4. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L45272724435.41L51794627208.41L59308743383.38L59314938599.4200000900?00V00gS1a1B1j1XS1k2HkS1L2SP1a1P1k3ACL1X1C2B4S1a1P1k1B1j1X1C1D". (* [comment removed for export] *)
  #[using="DIMG"] Lemma ck_out_blk : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Phh,(5.$52.VL,VHI,)PLBB,(6.$7.)Pmm,P,(2.&40.)(3.(2.&8.))Pmmo,$4.PLB,(6.(1<.$8.$8.))PSP,$8.Pa,$8.PP,$8.Pk,$8.P,(17.$52.VL,VHI,R9.R8.R7.R6.)P,(19.(1<.$8.$8.)(1=.$8.$8.R3.R2.)R9.)P,(30.(19.(1<.$8.$8.)(1=.$8.$8.R4.R3.)R7.))P,Pb,(1<.$8.$8.)P,(19.(1<.$8.$8.)R1.R9.)(19.(1<.$8.$8.)R2.R=.)P,(26.=R5.)P,(29.(45.VL,)R9.)P,(64.VL,R;.R:.R9.)(30.(9.(29.R9.R:.)(26.R:.(1>.R9.R8.))))")
(* [comment removed for export] *).
  Proof.
    intros hh LBB mm mmo LB SP a P k HH IN NIN SUB Hk ACL HC C. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    destruct HC as [X|[X|([B j] & Hb & X)]].
    - pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (_ & _ & _ & B4 & _). cbn in B4. lia.
    - exact (blk_off_data usegs L HI DIMG _ _ _ _ _ _ a HH IN (proj1 X) C).
    - cbn in X. assert (NE : (B, j) <> (P, k)) by (intros E; rewrite E in Hb; exact (NIN Hb)).
      destruct (blocks_apart_neq _ _ _ HAP (SUB _ Hb) IN NE ltac:(cbn; lia) ltac:(cbn; lia)) as [D|D]; cbn in D; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L1911187518.30 L59306953143.31L64517175531.31L971379721.31  00000700A00F00VS1p1k1lS1p1k2Hk1nS1p1lS1L1p3MC13MC22n0". (* [comment removed for export] *)
  #[using="DIMG"] Lemma ck_blk_MC : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pp,$8.Pk,$8.P,(17.$52.VL,VHI,R6.R5.R4.R3.)P,(19.(1<.$8.$8.)(1=.$8.$8.R3.R2.)R6.)P,(26.=R3.)P,(29.(3>.VL,)+5<?:8.)P,(29.(1>.+5<?:8.+8.)(3?.VL,))(2>.(29.(1>.R7.R6.)+5<?:8.)(29.(1>.+5<?:8.+8.)R7.))")
(* [comment removed for export] *).
  Proof.
    intros h LB m mo p k HH IN Hk MC1 MC2. destruct (Z_le_dec (p + k) U_MUL_COUNT); [left; lia|]. destruct (Z_le_dec (U_MUL_COUNT + 8) p); [right; lia|]. exfalso.
    apply (blk_off_data usegs L HI DIMG _ _ _ _ _ _ (Z.max p U_MUL_COUNT) HH IN); lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma grp_mpds_at : forall m LB G g d, ecp_group_at usegs MT m LB G g -> In d (grp_mpds g) -> mpdr_at usegs m LB d.
  Proof.
    intros m LB G g d HG Hd. ddestruct HG as (HD & AL & POS & EP & EA & EB & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & HT & REST).
    unfold grp_mpds in Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L65267193017.58000008S2SP1a1X". (* [comment removed for export] *)
  #[using="Type"] Lemma ck_st_step : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PSP,$8.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Phk,(5.$52.VL,VHI,)PLBk,(6.$7.)Pmk,P,(2.&40.)(3.(2.&8.))Pmok,$4.Phk',(5.$52.VL,VHI,)PLBk',(6.$7.)Pmk',P,(2.&40.)(3.(2.&8.))Pmok',$4.PLBX,(6.$7.)PXs,(6.$4;.)P,(63.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(17.$52.VL,VHI,R7.R6.R5.R4.)P,Pb,$7.P,(19.$7.R1.R12.)(19.$7.R2.R9.)P,(1:.$52.VL,R5.(43.R11.+50.)R4.R;.R7.)P,Pb,$7.P,(19.$7.R1.R14.)(19.$7.R2.R8.)P,Pa,$8.P,(9.(29.=R1.)(26.R1.(28.+2.+40.)))P,(64.VL,R16.R15.R2.)P,(65.(1;.(1<.$8.$8.)(1=.$8.$8.+5<?:8.(1>.+5<?:8.+8.))(1?.(1<.$8.$8.)))R3.)(65.R:.R4.)P,(20.$52.VL,R:.)P,(12.$52.R;.)P,(15.R?.R;.)P,(:.$8.(16.$52.VL,VHI,R?.)(16.$52.VL,VHI,R13.))P,(1.(2.&40.)Lc,(2.&40.)(23.$52.R?.+5<?:8.(1;.$24.(25.R1.)(1?.$24.))))P,(13.$52.R?.R18.(43.R19.+50.))(63.R1<.R1;.R1:.R19.R18.R17.R12.R11.R10.R?.)")
(* [comment removed for export] *).
  Proof.
    intros until Xs. (intros dd_H; ddestruct dd_H as (HHk & SUBk & PXk & SOKk & MIk & MFk & HTk & CNTk & STk); intros HH' SUB' PX SUBX OUT SOK' MI' MF' HT' CNT' ST').
    unfold ck_st. refine (conj HH' (conj SUB' (conj _ (conj SOK' (conj MI' (conj _ (conj _ (conj CNT' ST')))))))).
    - eapply heap_presx_trans; [exact PXk|]. intros a Ha HC HO. apply PX; [exact Ha| | exact (OUT a Ha HC HO)].
      destruct HC as [X|[X|(b & Hb & X)]]; [left; lia| right; left; exact X| right; right; exists b; split; [exact (SUBX _ Hb)| exact X]].
    - eapply mo_frame_trans; [exact MFk| exact MF'].
    - rewrite HT'. exact HTk.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12185525866.58L37273016624.55L57108244262.5200000600e00lS1d2N1S1L3HLS4DIMG4IMGC1G2SP2lo2GS3MC23SLO3ACL1a2Ha1CS1G3MCG". (* [comment removed for export] *)
  #[using="HLS DIMG IMGC"] Lemma ck_st_grp : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.PSP,$8.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Phk,(5.$52.VL,VHI,)PLBk,(6.$7.)Pmk,P,(2.&40.)(3.(2.&8.))Pmok,$4.P,(5<.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(63.R12.R11.R9.R8.R7.R6.R5.R4.R3.R2.)(21.$52.VMT,R4.R5.R11.R?.)")
(* [comment removed for export] *).
  Proof.
    intros until mok. (intros CTX dd_H; ddestruct dd_H as (HHk & SUBk & PXk & SOKk & MIk & _)).
    dpose CTX as (HH & GR & _ & _ & _ & _ & _ & GCR & GS & MCG & _ & _ & _ & _ & _ & _ & _ & MC1 & MC2 & _ & _ & _ & _ & _ & _ & _ & SLO & ACL & _ & _ & DHI & MI & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    eapply (ecp_group_at_presx usegs L); [exact GR| exact PXk| exact MI| exact MIk| | cbn; split; [lia| exact I]|].
    - intros a Ha. destruct (GCR a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
    - intros d Hd O. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
      ddestruct (mpdr_blk_facts usegs L m LB d (grp_mpds_at m LB G g d GR Hd) O HBR) as (IN & N1 & _). split; [exact (SUBk _ IN)|].
      cbn. split; [| exact I]. eapply ck_blk_MC; [exact HH| exact IN| lia| exact MC1| exact MC2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12185525866.68L37273016624.59L50894532054.5600000601601=S1d2N1S1L3HLS4DIMG4IMGC1G1Q2SP2lo2GS3MCG2QS3MCQ3MC23SLO3ACL3DHI1a2Ha1CS1Q3MCQ". (* [comment removed for export] *)
  #[using="HLS DIMG IMGC"] Lemma ck_st_pt : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.PSP,$8.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Phk,(5.$52.VL,VHI,)PLBk,(6.$7.)Pmk,P,(2.&40.)(3.(2.&8.))Pmok,$4.P,(5<.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(63.R12.R11.R9.R8.R7.R6.R5.R4.R3.R2.)(22.$52.R4.R5.R10.R>.)")
(* [comment removed for export] *).
  Proof.
    intros until mok. (intros CTX dd_H; ddestruct dd_H as (HHk & SUBk & PXk & SOKk & MIk & _)).
    dpose CTX as (HH & GR & _ & _ & _ & _ & _ & GCR & GS & MCG & PT & _ & _ & QCR & QS & MCQ & _ & MC1 & MC2 & _ & _ & _ & _ & _ & _ & _ & SLO & ACL & _ & _ & DHI & MI & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    eapply (ecp_point_at_presx usegs L); [exact PT| exact PXk| exact MI| exact MIk| | cbn; split; [lia| exact I]|].
    - intros a Ha. destruct (QCR a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
    - intros d Hd O. ddestruct PT as (EX & EY & EZ & MX & MY & MZ).
      assert (HD : mpdr_at usegs m LB d) by (cbn in Hd; destruct Hd as [<-|[<-|[<-|[]]]]; assumption).
      destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
      ddestruct (mpdr_blk_facts usegs L m LB d HD O HBR) as (IN & N1 & _). split; [exact (SUBk _ IN)|].
      cbn. split; [| exact I]. eapply ck_blk_MC; [exact HH| exact IN| lia| exact MC1| exact MC2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L12185525866.59L30618040681.64L31366167927.58L31366167927.65L37273016624.59L53610275413.56L8927507745.64 00000600@00j01A02002702GS1d2N1S1d2N13PB1S1L3HLS4DIMG4IMGC2LB2SP2lo1d3MC23SLO3ACL1HS1L4IMGC2lo1d3ACL3PB11HS1L3HLS4DIMG4IMGC2SP2lo1d2SD3MC23SLO3ACL1a2Ha1CS1d3DMCS1d2HL2N12P03PB1". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC"] Lemma ck_st_mpd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.PSP,$8.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Phk,(5.$52.VL,VHI,)PLBk,(6.$7.)Pmk,P,(2.&40.)(3.(2.&8.))Pmok,$4.Pd,$2=.P,(5<.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(63.R13.R12.R:.R9.R8.R7.R6.R5.R4.R3.)P,(5=.$52.R9.R13.R3.)P,(2>.(29.(1>.(5>.R4.)+10.)R;.)(29.R<.(5>.R4.)))P,(3:.VL,R15.R<.(5>.R5.)+10.)P,(2>.(29.(1>.+5<?:8.+8.)(5>.R6.))(29.(1>.(5>.R6.)+10.)+5<?:8.))(9.(5=.$52.R9.R:.R7.)(9.P,(:.$4=.(4>.R7.)$4?.)(9.(19.(1<.$8.$8.)(1=.$8.$8.(31.R8.)(50.+4.(51.R8.)))R18.)(9.(26.=(31.R8.))(9.(29.(1>.(31.R8.)(50.+4.(51.R8.)))(45.VL,))(29.+1.(51.R8.)))))P,(30.(:.$4=.(4>.R7.)$5?.))(2>.(29.(1>.(31.R8.)(50.+4.(51.R8.)))R?.)(29.R10.(31.R8.)))))")
(* [comment removed for export] *).
  Proof.
    intros until d. (intros CTX dd_H; ddestruct dd_H as (HHk & SUBk & PXk & SOKk & MIk & _); intros MD SD CR DMC).
    dpose CTX as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MC1 & MC2 & _ & _ & _ & _ & _ & _ & _ & SLO & ACL & _ & _ & DHI & MI & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    assert (BL : md_own d = LHeap -> In (md_p d, 4 * md_n d) LB /\ 0 < md_p d /\ md_p d + 4 * md_n d <= alloc_ceiling /\ 1 <= md_n d).
    { intros O. ddestruct (mpdr_blk_facts usegs L m LB d (proj1 MD) O HBR) as (I1 & I2 & I3 & I4 & _). auto. }
    assert (SL : md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ SP <= md_p d).
    { intros NN. destruct (md_own d) eqn:O; [exfalso; congruence| left; pose proof (BL eq_refl); lia|].
      pose proof MD as [(_ & _ & _ & HL & HN & HO) _]. rewrite O in HO. ddestruct HO as (N1 & _ & P0 & PB & PRO). dpose PB as (_ & PB1 & _). rewrite u32s_length in PB1.
      pose proof (ROIMG _ (PRO (4 * md_n d - 1) ltac:(lia)) ltac:(lia)). left. lia. }
    split; [| exact (conj BL SL)].
    split; [| exact (proj2 MD)]. apply (mpdr_at_LB_one usegs) with (LB := LB); [| intros O; exact (SUBk _ (proj1 (BL O)))].
    eapply (mpdr_at_presx usegs L); [exact (proj1 MD)| exact PXk| exact MI| exact MIk| | cbn; split; [lia| exact I]|].
    - intros a Ha. destruct (CR a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
    - intros O. ddestruct (BL O) as (IN & _ & _ & N1). split; [exact IN|]. cbn. split; [| exact I].
      eapply ck_blk_MC; [exact HH| exact IN| lia| exact MC1| exact MC2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="HLS DIMG IMGC"] Lemma ck_st_fin : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.PSP,$8.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Phk,(5.$52.VL,VHI,)PLBk,(6.$7.)Pmk,P,(2.&40.)(3.(2.&8.))Pmok,$4.P,(5<.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(63.R12.R11.R9.R8.R7.R6.R5.R4.R3.R2.)P,Pb,$7.P,(19.$7.R1.R6.)(19.$7.R2.R14.)(53.R14.R13.R12.R10.R11.R?.R;.R:.R9.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX STK SUB'. dpose STK as (HHk & SUBk & PXk & SOKk & MIk & MFk & HTk & CNTk & STk).
    unfold ck_fin. refine (conj MIk (conj STk (conj MFk (conj HTk (conj HHk (conj (fun b => conj (SUB' b) (SUBk b)) (conj PXk (conj SOKk (conj _ (conj _ CNTk)))))))))).
    - eapply ck_st_grp; [exact CTX| exact STK].
    - eapply ck_st_pt; [exact CTX| exact STK].
  Qed.

  #[using="Type"] Lemma nodup_fst_neq : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "PLB,(6.$7.)PB,$8.Pk,$8.PP,$8.Pj,$8.P,(66.$8.(67.(1<.$8.$8.)$8.(68.$8.$8.)R5.))P,(19.(1<.$8.$8.)(1=.$8.$8.R5.R4.)R6.)P,(19.(1<.$8.$8.)(1=.$8.$8.R4.R3.)R7.)P,(30.(:.(1<.$8.$8.)(1=.$8.$8.R7.R6.)(1=.$8.$8.R5.R4.)))(30.(:.$8.R8.R6.))")
(* [comment removed for export] *).
  Proof.
    induction LB as [|x r IH]; cbn; intros B k P j ND H1 H2 NE; [destruct H1|].
    apply List.NoDup_cons_iff in ND as [NI ND].
    destruct H1 as [->|H1]; destruct H2 as [E|H2].
    - congruence.
    - cbn in NI. intros ->. apply NI. apply in_map_iff. exists (P, j). auto.
    - subst x. cbn in NI. intros ->. apply NI. apply in_map_iff. exists (P, k). auto.
    - exact (IH _ _ _ _ ND H1 H2 NE).
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L17614601653.4000000?S3SP'1A2LE1a2Ha". (* [comment removed for export] *)
  #[using="Type"] Lemma ck_tmp_presx : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "PLB,(6.$7.)PLBk,(6.$7.)PLBX,(6.$7.)PLBk',(6.(1<.$8.$8.))Pmk,P,(2.&40.)(3.(2.&8.))Pmk',P,(2.&40.)(3.(2.&8.))PSP',$8.PXs,(6.$4;.)PA,$8.Pe,$2=.P,(69.R:.R9.R6.R2.R1.)P,(1:.$52.VL,R9.R5.R4.R7.R6.)P,(12.$52.R8.)P,(12.$52.R8.)P,(29.R8.R6.)P,(4<.R8.R7.+10.)P,P,(:.$4=.(4>.R7.)$4?.)(9.(19.(1<.$8.$8.)(1=.$8.$8.(31.R8.)(50.+4.(51.R8.)))R?.)(9.(19.(1<.$8.$8.)(1=.$8.$8.(31.R8.)(50.+4.(51.R8.)))R>.)(4<.R:.(31.R8.)(50.+4.(51.R8.)))))(69.R11.R>.R<.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    (intros LB LBk LBX LBk' mk mk' SP' Xs A e dd_H; ddestruct dd_H as (ME & EA & NS & FRS); intros PX MI MI' LE DX HL).
    refine (conj _ (conj EA (conj NS FRS))). split; [| exact (proj2 ME)].
    apply (mpdr_at_LB_one usegs) with (LB := LBX); [| intros O; exact (proj1 (proj2 (HL O)))].
    eapply (mpdr_at_presx usegs L); [exact (proj1 ME)| exact PX| exact MI| exact MI'| rewrite EA; intros a Ha; left; lia| rewrite EA; exact DX| intros O; ddestruct (HL O) as (X1 & _ & X3); exact (conj X1 X3)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L11866356319.109L12185525866.137L12185525866.140L24535525674.137L26058334103.126L26058544773.109L31828522092.109L32559362792.140L35622400169.134L3818637306.109 L39400550619.138L40147641242.136L47059776337.137L49587729867.111L56528008730.134L59231269992.109L59308585607.112L63259868615.109L63887036889.136L66605303805.11100000900N00c01E02402c03803Y03b04404A04`04n05W06K06]07U08H08V09BS3RET3spvS1d3RET3spv2HR3SPB2N1S1d3RET3spv2HR3SPB2N1S1L3HLS2lo1d3RET3spv2A12HR3SPB3SLOS1L3HLS4DIMG4IMGC2lo3RET3spv2HR3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC2lo3RET3spv2HR3SPB3MC23SLO3ACLS1L2HI1h3RET3spv4HTOPS1L3HLS2lo3RET3spv2HR3SPB3SLO3ACLS3RET3spvS1L2lo3RET3spv3ACLS1d3RET3spv1HS1L3RET3spv2HR3SPB3MC13MC21a2HaS1d3RET3spv2A2S1L2HI1h1d3RET3spv2A12A22HR3SPB4HTOP1a2HaS1L3HLS4DIMG4IMGC2lo1d3RET3spv2A12HR3SPB3MC23SLO3ACLS1L2lo3RET3spv3SLOS1L3HLS4DIMG4IMGC2lo1d3RET3spv2A12HR3SPB3SLO3ACL1a2Ha2HdS1L3HLS4DIMG4IMGC2lo3RET3spv2HR3SPB3MC23SLO3ACL3SPAS3RET3spv1a2HaS1L3HLS2lo3LBk1d3RET3spv2A12HR3SPB3SLO3ACL1H". (* [comment removed for export] *)
  #[using="HLS DIMG IMGC HND HFREEM"] Lemma ck_free : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Phk,(5.$52.VL,VHI,)PLBk,(6.$7.)Pmk,P,(2.&40.)(3.(2.&8.))Pmok,$4.Pd,$2=.PRET,$8.Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)PQ',P,$0.SpP,(5<.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.(14.&40.R21.)R2:.R29.R28.)P,(63.R34.R33.(14.&40.R22.)R2;.R2:.R29.R28.R27.R26.R25.)P,(69.R34.R28.R27.(5>.R25.)R25.)P,(29.(1>.(14.&40.R24.)-50.)(5>.R26.))P,(29.(1>.(5>.R27.)+10.)(14.&40.R25.))P,(9.(29.=R27.)(26.R27.(28.+2.+40.)))P,(:.$8.(46.R28.+2.)=)P,(:.(2.&40.)R26.(>.&40.(47.VL,)))P,(:.(2.&40.)R21.(>.&40.(5>.R2;.)))P,Pmk',P,(2.&40.)(3.(2.&8.))Pmok',$4.Phk',(5.$52.VL,VHI,)Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa0',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)P,(63.R4>.R4=.(14.&40.R3<.)R45.R44.R43.R10.(6:.R3>.R41.)R12.R11.)P,(23.$52.R13.(5>.R3?.)(6;.=(>.&40.+1.)=(6<.R3?.)))P,(1:.$52.VL,(6:.R40.R43.)(1>.(14.&40.R3>.)-50.)(1;.(1<.$8.$8.)(1=.$8.$8.(5>.R40.)(1>.(5>.R40.)+10.))(6=.(4>.R40.)(31.R40.)(51.R40.)))R42.R14.)P,P,(:.$4=.(4>.R41.)$4?.)(9.(19.(1<.$8.$8.)(1=.$8.$8.(31.R42.)(50.+4.(51.R42.)))R45.)(9.(29.+1.(51.R42.))(9.(26.=(31.R42.))(29.(1>.(31.R42.)(50.+4.(51.R42.)))(45.VL,)))))P,(12.$52.R44.)(49.$52.R16.R21.(<.(=.(>.&40.R42.)(>.&40.(1>.(14.&40.R41.)-50.))R40.R3?.R14.R13.R12.R3;.R3:.R11.R10.R?.R>.R=.R<.R;.R:.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R9.R8.R7.R6.)R23.(>.&40.R42.)R22.(10.(2.&40.))R17.(11.$52.)))(49.$52.R2>.R;.(<.(=.(>.&40.R2<.)(>.&40.(1>.(14.&40.R2;.)-50.))R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(>.&40.+1?4:8.)R<.(10.(2.&40.))R2?.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until Q'. intros CTX STK TMP A1 A2 HR HRE TP -> K. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose CTX as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MC1 & MC2 & MCS & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & SPA & DHI & MI & _ & CA & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    dpose STK as (HHk & SUBk & PXk & SOKk & MIk & MFk & HTk & [ck CNTk] & STk). dpose TMP as (MD & _ & NS & FRS).
    destruct (heap_blocks _ _ HI _ _ _ _ HHk) as [HBRk HAPk]. pose proof (HND _ _ _ _ HHk) as NDk.
    assert (BL : md_own d = LHeap -> In (md_p d, 4 * md_n d) LBk /\ 1 <= md_n d /\ 0 < md_p d /\ md_p d + 4 * md_n d <= alloc_ceiling).
    { intros O. ddestruct (mpdr_blk_facts usegs L mk LBk d (proj1 MD) O HBRk) as (I1 & I2 & I3 & I4 & _). auto. }
    pose proof HFREEM as SF. unfold mpi_free_stmt in SF.
    eapply aevtM_cut.
    { pose proof MD as [MA _]. unfold mpdr_at in MA.
      eapply SF with (lo := lo) (h := hk) (LB := LBk); rewrite ?(unsigned_lit (bv_unsigned spv + -80)), ?HTk by lia;
        first [ exact HHk | exact MA | exact NS | exact STk' | exact TP | exact MIk | exact SOKk | exact CA | exact DHI | reflexivity
              | match goal with |- stk _ _ _ _ => replace (bv_unsigned spv + -80) with (bv_unsigned spv - 80) by lia; exact STk end
              | intros a Ha; left; lia
              | intros O; pose proof (BL O); lia
              | intros a Ha Hd; exfalso; lia
              | lia ]. }
    clear SF. cbv beta. intros ms' mo' PO. unfold mpi_free_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mk' & mok' & hk' & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned spv + -80)) in PO by lia.
    ddestruct PO as (MI' & ST' & MF' & HT' & HH' & CH' & PX' & SOK').
    change (mpi_free_LB _ _ _ LBk) with (lb_free_mpd d LBk) in HH', PX'.
    rewrite (ret_pc_even RET HR HRE).
    assert (SUB' : forall b, In b LB -> In b (lb_free_mpd d LBk)).
    { intros [B k] Hb. apply lb_free_mpd_keep; [exact (SUBk _ Hb)|]. intros O.
      eapply (nodup_fst_neq LBk); [exact NDk| exact (SUBk _ Hb)| exact (proj1 (BL O))|].
      intros E. apply (FRS (B, k)); [| exact Hb]. unfold mpd_blk. rewrite O, E. left; reflexivity. }
    eapply K; [| exact CH'| exact PX'| exact BL| exact MIk].
    eapply ck_st_step; [exact STK| exact HH'| exact SUB'| exact PX'| exact SUB'| | exact SOK'| exact MI'| exact MF'| exact HT'| | replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia; exact ST'].
    - intros a Ha HC _. cbn. split.
      + eapply (ck_out_stack h LB m mo); [exact HH| exact ACL| exact DHI| exact HC| lia| lia].
      + unfold mpi_free_X. destruct (md_own d) eqn:O; cbn; [exact I| | exact I]. split; [| exact I].
        ddestruct (BL eq_refl) as (IN & N1 & _). 
        eapply (ck_out_blk hk LBk mk mok LB (bv_unsigned spv) a); [exact HHk| exact IN| apply FRS; unfold mpd_blk; rewrite O; left; reflexivity| exact SUBk| lia| lia| exact HC].
    - exists ck. eapply heap_presx_rw_cells; [exact PX'| exact CNTk| cbn; intros a Ha; right; left; split; [lia| apply MCS; lia]|].
      cbn. split; [lia|]. unfold mpi_free_X. destruct (md_own d) eqn:O; cbn; [exact I| | exact I]. split; [| exact I].
      ddestruct (BL eq_refl) as (IN & N1 & _). pose proof (ck_blk_MC hk LBk mk mok _ _ HHk IN ltac:(lia) MC1 MC2). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0@L12189361846.140L13129188448.113L13847661174.147L15324000921.141L2068654858.140 L2068688428.140 L24248805921.140L24935127466.144L25156247717.146L28236442263.168L32066564618.167L32073329084.169L3226783026.169 L33679264657.168L35451068657.140L41198376924.146L4585058315.142 L51523620783.143L51523620783.170L51523620783.171L58194387178.169L58751683082.113L59075789527.113L63286769808.113L64342627957.143L66285452340.169L9925028081.168 00000500:00G00L00Q00V00[01;01K01P01U02502:02?02D02T03403>03H03R03h03m04204704W04\04aS3spvS3spvS3spv2dY2dR1DS3spvS3spvS3spvS3spvS1L3HLS3spv2lo2dR3SPB3SLO3ACL2B4S3spv2dY3SPB3NY1S3spvS3spvS1L3HLS3spv2lo2dR3SPB3SLO3ACL2B4S3spvS3spvS3spvS3spv2dR3SPB3NR1S1L3HLS3spv2lo2dY3SPB3SLO3ACL2B4S3spv1a2HaS3spv1a2HaS3spv1a2HaS1L3HLS3spv2lo3SPB3SLOS3spvS3spvS3spvS1L3HLS3spv2lo2dY3SPB3SLO3ACL2B4S3spvS3spv". (* [comment removed for export] *)
  #[using="HLS DIMG IMGC HND HFREEM"] Lemma ck_cleanup : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Prae,(2.&40.)Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0e,(2.&40.)Ps1e,(2.&40.)Ps2e,(2.&40.)Ps3e,(2.&40.)Ps4e,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pra0,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1c,(2.&40.)Ps2c,(2.&40.)Ps3c,(2.&40.)Ps4c,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Phk,(5.$52.VL,VHI,)PLBk,(6.$7.)Pmk,P,(2.&40.)(3.(2.&8.))Pmok,$4.PdY,$2=.PdR,$2=.Pr,$8.P,(5<.R11.R10.R?.R>.R=.R<.R;.R:.R9.(14.&40.R38.)R8.R13.R12.)P,(63.R12.R11.(14.&40.R39.)R9.R14.R13.R8.R7.R6.R5.)P,(69.R12.R8.R7.(1>.(14.&40.R3:.)-40.)R5.)P,(69.R13.R9.R8.(1>.(14.&40.R3;.)-50.)R5.)P,P,(:.$4=.(4>.R7.)$4?.)P,(:.$4=.(4>.R7.)$4?.)(30.(:.(1<.$8.$8.)(1=.$8.$8.(31.R9.)(50.+4.(51.R9.)))(1=.$8.$8.(31.R8.)(50.+4.(51.R8.)))))P,Pb,$7.P,(19.$7.R1.R<.)(2>.(19.$7.R2.R17.)(2>.(19.$7.R2.(62.R:.))(19.$7.R2.(62.R9.))))P,(23.$52.R;.(1>.(14.&40.R3>.)-30.)(54.R37.R38.R39.R3:.R3;.R3?.))P,(:.(2.&40.)R3=.(>.&40.(47.VL,)))P,(9.(26.(27.(28.+2.+1?.))R9.)(29.R9.=))(49.$52.R=.(4:.$52.VL,VHI,VMT,R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R1>.R1=.R1:.R19.R18.R16.R17.R15.+5<?:8.R11.R1<.R1;.)(<.(=.R32.(>.&40.(1>.(14.&40.R41.)-50.))R40.R3?.R31.R30.R2?.(>.&40.R:.)R2>.R2:.R29.R28.R27.R26.R25.R24.R23.R2=.R2<.R2;.R39.R38.R37.R36.R35.R34.R33.R22.R21.R20.R1?.)R1>.(>.&40.+3:25<.)R1=.(10.(2.&40.))R>.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros CTX STK TY TR DIS COV FR TP HRr. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose CTX as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MC1 & MC2 & MCS & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & SPA & DHI & MI & _ & CA & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    dpose STK as (HHk & SUBk & _ & _ & MIk & _). pose proof (heap_mok _ _ HI _ _ _ _ HHk) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HHk) as [HBRk HAPk]. pose proof (HND _ _ _ _ HHk) as NDk.
    dpose TY as (MY & EY & NSY & FRY). dpose TR as (MR & ER & NSR & FRR).
    assert (BLR : md_own dR = LHeap -> In (md_p dR, 4 * md_n dR) LBk /\ 1 <= md_n dR /\ 0 < md_p dR /\ md_p dR + 4 * md_n dR <= alloc_ceiling).
    { intros O. ddestruct (mpdr_blk_facts usegs L mk LBk dR (proj1 MR) O HBRk) as (I1 & I2 & I3 & I4 & _). auto. }
    unfold ck_frame in FR.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply ck_free with (d := dY); [exact CTX| exact STK| rewrite EY; exact TY| rewrite EY; lia| rewrite EY; lia| lia| reflexivity| exact TP| rewrite EY; apply f_equal; lia|].
    intros m4 mo4 h4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ST4 CHY4 PX4 BLY _. rewrite EY in CHY4, PX4.
    dpose ST4 as (HH4 & SUB4 & _ & _ & MI4 & _). clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK. pose proof (HND _ _ _ _ HH4) as ND4.
    assert (DXR : md_own dR = LHeap -> disjoint_from (mpi_free_X (md_own dY) (md_p dY) (md_n dY)) (md_p dR) (4 * md_n dR) /\ (md_own dY = LHeap -> md_p dR <> md_p dY)).
    { intros OR. ddestruct (BLR OR) as (INR & NR1 & _). unfold mpi_free_X. destruct (md_own dY) eqn:OY; cbn; [split; [exact I| intros E; discriminate E]| | split; [exact I| intros E; discriminate E]].
      ddestruct (BLY eq_refl) as (INY & NY1 & _). pose proof (DIS eq_refl OR) as NE.
      split; [split; [| exact I]| intros _; apply not_eq_sym; exact (nodup_fst_neq LBk _ _ _ _ NDk INY INR NE)].
      destruct (blocks_apart_neq _ _ _ HAPk INY INR NE ltac:(cbn; lia) ltac:(cbn; lia)) as [D|D]; cbn in D; lia. }
    assert (TR4 : ck_tmp LB (lb_free_mpd dY LBk) m4 (bv_unsigned spv + -80) dR).
    { eapply ck_tmp_presx; [exact TR| exact PX4| exact MIk| exact MI4| lia| |].
      - cbn. split; [lia|]. unfold mpi_free_X. destruct (md_own dY) eqn:OY; cbn; [exact I| | exact I]. split; [| exact I]. ddestruct (BLY eq_refl) as (_ & _ & _ & B4). lia.
      - intros OR. destruct (DXR OR) as [D NE]. split; [| split]; [| | cbn; split; [ddestruct (BLR OR) as (_ & _ & _ & B4); lia| exact D]].
        + apply lb_free_mpd_keep; [exact (proj1 (BLR OR))| exact NE].
        + apply lb_free_mpd_keep; [exact (proj1 (BLR OR))| exact NE]. }
    assert (FR4 : rw_cells usegs m4 (bv_unsigned spv + -48) (ck_frame s4e s3e s2e s1e s0e rae)).
    { eapply heap_presx_rw_cells; [exact PX4| exact FR| cbn; intros a Ha; left; lia|]. cbn. split; [lia|].
      unfold mpi_free_X. destruct (md_own dY) eqn:OY; cbn; [exact I| | exact I]. split; [| exact I]. ddestruct (BLY eq_refl) as (_ & _ & _ & B4). lia. }
    clear FR PX4. unfold ck_frame in FR4.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply ck_free with (d := dR); [exact CTX| exact ST4| rewrite ER; exact TR4| rewrite ER; lia| rewrite ER; lia| lia| reflexivity| exact TP| rewrite ER; reflexivity|].
    intros m5 mo5 h5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ST5 CHR5 PX5 BLR4 _. rewrite ER in CHR5, PX5.
    dpose ST5 as (HH5 & SUB5 & _ & _ & MI5 & _ & _ & _ & STK5). clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK. pose proof (HND _ _ _ _ HH5) as ND5.
    assert (DR : disjoint_from ((bv_unsigned spv + -80, bv_unsigned spv + -80 + 16) :: mpi_free_X (md_own dR) (md_p dR) (md_n dR)) (bv_unsigned spv + -80 + 16) 64).
    { cbn. split; [lia|]. unfold mpi_free_X. destruct (md_own dR) eqn:OR; cbn; [exact I| | exact I]. split; [| exact I]. ddestruct (BLR eq_refl) as (_ & _ & _ & B4). lia. }
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX5 CHY4 ltac:(cbn; intros a Ha; left; lia) ltac:(eapply disjoint_from_sub; [exact DR| lia| cbn; lia])) as CHY5.
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX5 FR4 ltac:(cbn; intros a Ha; left; lia) ltac:(eapply disjoint_from_sub; [exact DR| lia| cbn; lia])) as FR5.
    clear FR4 PX5.
    zstep. zstep.
    replace (bv_unsigned spv + -64) with (bv_unsigned spv + -80 + Z.of_nat (cells_size (mpi_cells 0 (Z_to_bv 64 1) 0 (md_pad dR)))) in CHY5 by (cbn; lia).
    pose proof (proj2 (rw_cells_app usegs m5 (bv_unsigned spv + -80) (mpi_cells 0 (Z_to_bv 64 1) 0 (md_pad dR)) (mpi_cells 0 (Z_to_bv 64 1) 0 (md_pad dY))) (conj CHR5 CHY5)) as LOC.
    eapply ck_exit; [| exact FR5| exact LOC| reflexivity| lia| exact HRr].
    eapply ck_st_fin; [exact CTX| exact ST5|].
    intros b Hb. pose proof (lb_free_mpd_sub _ _ _ Hb) as Hb4. pose proof (lb_free_mpd_sub _ _ _ Hb4) as Hbk.
    destruct (COV b Hbk) as [Hl|[Hy|Hr]]; [exact Hl| exfalso| exfalso].
    - unfold mpd_blk in Hy. destruct (md_own dY) eqn:OY; try (destruct Hy; fail). destruct Hy as [<-|[]].
      unfold lb_free_mpd in Hb4 at 1. rewrite OY in Hb4. exact (lb_remove_notin _ _ _ NDk Hb4).
    - unfold mpd_blk in Hr. destruct (md_own dR) eqn:OR; try (destruct Hr; fail). destruct Hr as [<-|[]].
      unfold lb_free_mpd in Hb at 1. rewrite OR in Hb. exact (lb_remove_notin _ _ _ ND4 Hb).
  all: match goal with |- ?g => idtac "CLEANLEFT" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01H0@L10472342405.238L10882941462.118L11803372322.136L11803373474.139L11805421443.136L11805421443.139L11868680526.197L12439250342.148L12439250342.199L12538338809.7  L1386330018.187 L14478075398.197L14478076699.146L15848238236.141L18549761402.197L19142102195.254L19654146831.245L22286003249.143L22286003249.148L22286003249.195L22286003249.199L22409197233.139L22700267513.138L22700267513.141L25069534765.191L25069845162.241L25069846058.240L25075841709.190L25108611573.247L26056216713.146L26056220052.197L26058334103.167L26058334103.218L2733944746.259 L29960585849.197L31826850400.146L31826853757.197L32817724416.141L3449942576.178 L35453395284.242L35622400178.187L35624497330.238L35626661391.134L38329374128.258L43588574820.146L44483135597.139L44483136750.136L45212570417.136L45482601112.199L46710810478.197L4846772663.229 L49587729867.148L49587729867.199L51040468651.7  L51523620783.192L51523620783.193L51523620783.243L51982644583.146L52039837756.134L52042245253.192L52067409697.254L52514112645.254L53519240741.254L5409152199.7   L54613236531.242L58751321389.240L59073858644.191L59308585607.149L59308585607.200L59672292116.247L6042846904.193 L6052986114.2   L61274507994.259L63149377930.245L63261865686.197L63261866955.146L63676537480.193L64076647740.131L64078745260.144L6443869639.7   L65896456361.149L65896456361.200L66651481651.191L67165823973.7  L67197327768.148L67865320205.246L68441856883.146L8803359311.7   00000100600;00@00E00J00R00^00m01D01E01U01b01m02T02U02h03403@03O03^03c04f05i06M07407[08?08V09>09i0:Q0;<0;O0;`0<10<E0<R0<W0<_0<d0<l0=10=<0=J0=R0=Z0=_0>d0?e0?m0@G0@d0A10A;0AE0AR0B60B^0CF0CG0CZ0Cm0D:0DS0D[0D`0EL0F;0FR0F`0Fg0G:0G^0HM0I90II0J10JY0Jf0K20KA0KW0Kd0Lf0M40N20NIFS3spvS3spvS3spvS3spvS3spvS3spv2r2S3spv1p2lo1HS3spv1p2lo2r21HS1L3HLS3spv1Q2lo2QS3SLOFS3spv1G2lo2GS2r2S3spv1G2lo2GSS3spv1Q3MCQS1L3HLS4DIMG4IMGC3spv2lo3MC23SLO3ACL2r2FS3spv3SPB3dY22r22N1S3spv1Q1a2HaS3spv1Q1a2HaS3spv1Q2r21a2HaS3spv1Q2r21a2HaS3spvS1L3HLS4DIMG4IMGC3spv1G1Q2lo3SPB2GS3MCG2QS3MCQ3MC23SLO3ACL3DHI2x01HS1L3HLS4DIMG4IMGC3spv1G1Q2lo3SPB2GS3MCG2QS3MCQ3MC23SLO3ACL3DHI2x11HS1L3HLS4DIMG4IMGC3spv2lo3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv2lo3MC23SLO3ACL2r2S1L3HLS4DIMG4IMGC3spv2lo3MC23SLO3ACL2r2S1L3HLS4DIMG4IMGC3spv2lo3MC23SLO3ACLS1L3spv2r23LB33dR32r31HS1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACL2r2S1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACL2r2S3spv3dY22r23dR32r3S1L3spv2lo3SLO2r2S1L2HI3spv1h4HTOPS1L2HI3spv1h4HTOP2r2S3spv1Q2lo2QSS3spvS3spv2r2S3spvS3spv2r2S3spvS3spv2r22r3S1L3spv2lo3SLOS3spv2loS3spv2loS3spvS1L3HLS4DIMG4IMGC3spv1G1Q1p2lo3SPB2GS3MCG2QS3MCQ3MC23SLO3ACL3DHI2r21HS1L3HLS4DIMG4IMGC3spv1G1Q2lo3SPB2GS3MCG2QS3MCQ3MC23SLO3ACL3DHI2r2S3spv2r2S1L2HI3spv1h3SPB4HTOP1a2HaS1L2HI3spv1h3SPB4HTOP2r21a2HaS3spv1Q2lo2QSS3spv1a2HaS3spv1a2HaS3spv2r21a2HaS1L3HLS4DIMG4IMGC3spv2lo3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACLFS3spv3dY22r23dR32r3S3spv3dY22r23dR32r3S3spv3SPB3SPAS1L3HLS3spv2lo3SPB3SLO2r2S3spv2r2S3spvS1L3HLS4DIMG4IMGC3spv2lo3SPB3SLO3ACL1a2Ha2HdS1L3HLS4DIMG4IMGC3spv2lo3SPB3SLO3ACL2r21a2Ha2HdS1L3spv3LB23dY22r22r31HS3spv1Q3MCQ2r2S1Q3MCQS3spv3dY22r23dR32r3S1L3HLS3spv2lo3SPB3SLO3ACL3dY22r22B4S1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACL3SPA2r2S1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACL3SPAS3spv1Q2lo2QS2r2S1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACLS3spv3SPB3SPAS3spv1p1a2HaS3spv1p2r21a2HaS1L3HLS3spv2lo3SPB3SLOS3spv1Q2lo2QSS1L3HLS4DIMG4IMGC3spv1G1Q1p2lo3SPB2GS3MCG2QS3MCQ3MC23SLO3ACL3DHI1HS3spv3dY22r21HS1L3HLS4DIMG4IMGC3spv1G1Q2lo3SPB2GS3MCG2QS3MCQ3MC23SLO3ACL3DHIS1L3HLS3spv1Q2lo2QS3SLO". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HND HMM HSR HINIT HFREEM HCMP"] Lemma ck_sw : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Prae,(2.&40.)Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0e,(2.&40.)Ps1e,(2.&40.)Ps2e,(2.&40.)Ps3e,(2.&40.)Ps4e,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pra0,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Pm1,P,(2.&40.)(3.(2.&8.))Pj32,(6.(2.&8.))P,(5<.R<.R;.R:.R9.R8.R7.R6.R5.R4.(14.&40.R2?.)R3.R>.R=.)P,(:.$8.(2?.R9.)+1.)P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.R5.(14.&40.R31.))(1?.(1<.$8.$8.)))R10.R4.)P,(58.$52.R11.R5.)P,(12.$52.R6.)P,(13.$52.R7.R8.(1>.(14.&40.R34.)-50.))P,(23.$52.R8.(1>.(14.&40.R35.)-30.)(54.R2>.R2?.R30.R31.R32.R36.))P,(23.$52.R9.(1>.(14.&40.R36.)-50.)(1;.$24.(6>.#20.R8.)(1?.$24.)))P,(:.(2.&40.)R35.(>.&40.(47.VL,)))(49.$52.R16.(4:.$52.VL,VHI,VMT,R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R19.R18.R15.R14.R13.R11.R12.R10.+5<?:8.R<.R17.R16.)(<.(=.R29.(>.&40.(1>.(14.&40.R38.)-50.))R37.R36.R28.R27.R26.(>.&40.R13.)(>.&40.R12.)R25.R24.R23.R22.R21.R20.R1?.R1>.(>.&40.(1>.R12.+10.))(>.&40.(1>.R13.+8.))(>.&40.$6?.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R1=.R1<.R1;.R1:.)R19.(>.&40.+3:21<.)R18.(10.(2.&40.))R;.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until j32. intros CTX H1 MU WM MI1 ST1 FR LOC TP. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose CTX as (HH & GR & GKIND & GPS & GAS & GBS & PV & GCR & GS & MCG & PT & PF & PS & QCR & QS & MCQ & CNT & MC1 & MC2 & MCS & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & SPA & DHI & MI & SOK & CA & _).
    pose proof SLO as SLO0. unfold ECP_CHECK_PUBKEY_STACK in SLO. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    dpose PT as (EX & EY & EZ & MX & MY & MZ).
    assert (PSG : forall d, In d (pt_mpds p) -> md_sg d = 1 \/ md_sg d = -1) by (intros d Hd; exact (proj1 (Forall_forall _ _) PS _ Hd)).
    assert (MDX : mpd_at usegs m LB (pt_X p)) by (split; [exact MX| apply PSG; cbn; auto]).
    assert (MDY : mpd_at usegs m LB (pt_Y p)) by (split; [exact MY| apply PSG; cbn; auto]).
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB usegs m1 _ [] 32 j32 [] [16;16]%nat LOC eq_refl) as LOC2. cbn [mk_CB_cells app] in LOC2. clear LOC.
    pose proof (proj1 (rw_cells_app usegs _ _ [CB 16 _] _) LOC2) as [CR0 CY0]. clear LOC2. cbn [cells_size csize Nat.add] in CY0.
    replace (bv_unsigned spv + -80 + Z.of_nat 16) with (bv_unsigned spv + -64) in CY0 by lia.
    set (jr := firstn 16 j32) in CR0. clearbody jr. set (jy := firstn 16 _) in CY0. clearbody jy.
    apply mpi_cells_of_bytes in CR0. apply mpi_cells_of_bytes in CY0.
    set (pr0 := bv_unsigned (wof (firstn 8 jr))) in CR0. set (sr0 := wof (firstn 2 (skipn 8 jr))) in CR0. set (nr0 := bv_unsigned (wof _)) in CR0. set (padR := wof (skipn 12 jr)) in CR0.
    set (py0 := bv_unsigned (wof (firstn 8 jy))) in CY0. set (sy0 := wof (firstn 2 (skipn 8 jy))) in CY0. set (ny0 := bv_unsigned (wof _)) in CY0. set (padY := wof (skipn 12 jy)) in CY0.
    clearbody pr0 sr0 nr0 padR py0 sy0 ny0 padY.
    pose proof HH as HH0. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    unfold ck_frame in FR.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof HINIT as SI. unfold mpi_init_stmt in SI.
    eapply aevtM_cut_evt; [exact MK| eapply SI with (X := bv_unsigned spv + -64); [exact CY0| clear - SPA SPB SLO HLS; lia| lia| exact MI1| reflexivity] |].
    clear SI. cbv beta. intros ms' PO. unfold mpi_init_post in PO. ddestruct PO as (? & mI1 & -> & MUa & WMa & MIa & CY1).
    replace (ret_pc (Z_to_bv 64 0x3a224)) with (Z_to_bv 64 0x3a224) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rw_cells_transport in FR; [| exact MUa| exact WMa| cbn; lia]. eapply rw_cells_transport in CR0; [| exact MUa| exact WMa| cbn; lia].
    eapply (stk_transport_disjoint usegs) in ST1; [| exact MUa| exact WMa| cbn; lia].
    assert (MU' : munch [(lo, bv_unsigned spv)] m mI1) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUa]; unfold sub_fp; cbn; intros; lia]).
    pose proof (wmono_trans _ _ _ _ WM WMa) as WM'. clear MU WM MUa WMa MI1. rename MU' into MU. rename WM' into WM.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof HINIT as SI. unfold mpi_init_stmt in SI.
    eapply aevtM_cut_evt; [exact MK| eapply SI with (X := bv_unsigned spv + -80); [exact CR0| clear - SPA SPB SLO HLS; lia| lia| exact MIa| reflexivity] |].
    clear SI. cbv beta. intros ms' PO. unfold mpi_init_post in PO. ddestruct PO as (? & mI & -> & MUa & WMa & MII & CR1).
    replace (ret_pc (Z_to_bv 64 0x3a22c)) with (Z_to_bv 64 0x3a22c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rw_cells_transport in FR; [| exact MUa| exact WMa| cbn; lia]. eapply rw_cells_transport in CY1; [| exact MUa| exact WMa| cbn; lia].
    eapply (stk_transport_disjoint usegs) in ST1; [| exact MUa| exact WMa| cbn; lia].
    assert (MU' : munch [(lo, bv_unsigned spv)] m mI) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUa]; unfold sub_fp; cbn; intros; lia]).
    pose proof (wmono_trans _ _ _ _ WM WMa) as WM'. clear MU WM MUa WMa MIa CR0 CY0. rename MU' into MU. rename WM' into WM.
    (* [comment removed for export] *)
    assert (STI : ck_st h LB (bv_unsigned spv) lo m mo h LB mI mo).
    { eapply ck_st_prefix; [exact CTX| exact MU| exact WM| exact MII| replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia; exact ST1]. }
    dpose STI as (HHI & _ & _ & SOKI & _ & _ & _ & [cI CNTI] & STI').
    pose proof (ck_st_grp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STI) as GRI.
    destruct (ck_st_mpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pt_Y p) CTX STI MDY ltac:(rewrite EY; lia) ltac:(rewrite EY; intros a Ha; apply QCR; lia) ltac:(rewrite EY; lia)) as (MEY & BLY & SLY).
    assert (MDYY : mpd_at usegs mI LB (mpd_init (bv_unsigned spv + -64) padY)).
    { split; [apply mpdr_at_init; [exact CY1| clear - SPA SPB SLO HLS; lia| lia]| left; reflexivity]. }
    clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HHI) as MK.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    pose proof HMM as SMM. unfold ecp_mul_mod_stmt in SMM.
    eapply aevtM_cut.
    { eapply SMM with (lo := lo) (h := h) (LB := LB) (dX := mpd_init (bv_unsigned spv + -64) padY) (dA := pt_Y p) (dB := pt_Y p) (G := G) (g := g) (cnt := cI);
        rewrite ?(unsigned_lit (bv_unsigned spv + -80)) by lia; cbn [md_addr md_own md_p md_n mpd_init];
        first [ exact HHI | exact GRI | exact H1 | exact GPS | exact GCR | exact MDYY | exact MEY | exact CNTI | exact MCS | exact TP | exact SOKI | exact CA | exact MII | exact STI' | exact MCG | exact ACL | exact DHI | exact MC1 | exact MC2
              | reflexivity | rewrite EY; reflexivity | rewrite EY; apply f_equal; lia
              | discriminate
              | match goal with |- mpd_sep _ _ => unfold mpd_sep; cbn [md_addr mpd_init]; first [left; reflexivity| right; rewrite EY; clear - QS SLO HLS; lia] end
              | match goal with |- opnd_sep _ _ _ _ => unfold opnd_sep; cbn [md_addr md_own md_p md_n mpd_init]; rewrite EY;
                  split; [intros NN; pose proof (SLY NN); lia|]; split; [intros; discriminate|]; split; [right; left; discriminate|]; split; [clear - QS SLO HLS; lia| intros NN; pose proof (SLY NN); lia] end
              | match goal with |- mpd_writable _ _ _ _ _ => unfold mpd_writable; cbn [md_addr md_own md_p md_n mpd_init];
                  split; [intros a Ha; left; lia|]; split; [intros a Ha Hd; exfalso; lia| intros; discriminate] end
              | match goal with |- client_range _ _ _ _ 16 => rewrite EY; intros a Ha; apply QCR; lia end
              | match goal with |- _ = LHeap -> client_range _ _ _ _ _ => intros O a Ha; right; right; exists (md_p (pt_Y p), 4 * md_n (pt_Y p)); split; [exact (proj1 (BLY O))| cbn; lia] end
              | match goal with |- _ -> _ => intros; first [discriminate| exfalso; congruence| lia] end
              | unfold ECP_MUL_MOD_STACK; lia
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SMM. cbv beta. intros ms' mo' PO. unfold ecp_mul_mod_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & mo2 & h2 & LB2 & dY2 & r2 & cnt2 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned spv + -80)) in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MA2 & OUT2 & PX2 & SOK2 & GR2 & CNT2 & RR2).
    replace (ret_pc (Z_to_bv 64 0x3a240)) with (Z_to_bv 64 0x3a240) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    dpose OUT2 as (EA2 & NS2 & K21 & K22 & K23). cbn [md_addr mpd_init] in EA2. pose proof RR2 as [_ (_ & _ & FRB2 & _)].
    destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 HAP2].
    assert (SUB2 : forall b, In b LB -> In b LB2) by (intros b Hb; apply (K22 b Hb); cbn; tauto).
    assert (STK2 : ck_st h LB (bv_unsigned spv) lo m mo h2 LB2 m2 mo2).
    { eapply (ck_st_step h LB (bv_unsigned spv) lo m mo h LB mI mo h2 LB2 m2 mo2 LB); [exact STI| exact HH2| exact SUB2| exact PX2| intros b Hb; exact Hb| | exact SOK2| exact MI2| exact MF2| exact HT2| exists cnt2; exact CNT2| replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia; exact ST2].
      intros a Ha HC HO. cbn. split; [| exact HO]. eapply (ck_out_stack h LB m mo); [exact HH| exact ACL| exact DHI| exact HC| lia| lia]. }
    assert (TY2 : ck_tmp LB LB2 m2 (bv_unsigned spv + -64) dY2).
    { refine (conj MA2 (conj EA2 (conj NS2 _))). intros b Hb. destruct (FRB2 b Hb) as [C|C]; [destruct C| exact C]. }
    assert (BLY2 : md_own dY2 = LHeap -> In (md_p dY2, 4 * md_n dY2) LB2 /\ 1 <= md_n dY2 /\ 0 < md_p dY2 /\ md_p dY2 + 4 * md_n dY2 <= alloc_ceiling).
    { intros O. ddestruct (mpdr_blk_facts usegs L m2 LB2 dY2 (proj1 MA2) O HBR2) as (I1 & I2 & I3 & I4 & _). auto. }
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 CR1 ltac:(cbn; intros a Ha; left; lia) ltac:(cbn; lia)) as CR2.
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 FR ltac:(cbn; intros a Ha; left; lia) ltac:(cbn; lia)) as FR2.
    assert (TR2 : ck_tmp LB LB2 m2 (bv_unsigned spv + -80) (mpd_init (bv_unsigned spv + -80) padR)).
    { split; [split; [apply mpdr_at_init; [exact CR2| clear - SPA SPB SLO HLS; lia| lia]| left; reflexivity]|]. split; [reflexivity|]. split; [cbn; discriminate|]. cbn. tauto. }
    assert (COV2 : forall b, In b LB2 -> In b LB \/ In b (mpd_blk dY2) \/ In b (mpd_blk (mpd_init (bv_unsigned spv + -80) padR))).
    { intros b Hb. destruct (K21 b Hb) as [C|C]; [left; exact C| right; left; exact C]. }
    clear MK FR CR1 CY1. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) zstep. eapply ck_cleanup; [exact CTX| exact STK2| exact TY2| exact TR2| cbn; intros _ E; discriminate E| exact COV2| exact FR2| exact TP| exact (proj1 RR2)]. }
    (* [comment removed for export] *)
    dpose STK2 as (_ & _ & _ & _ & _ & _ & _ & _ & ST2').
    destruct (ck_st_mpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pt_X p) CTX STK2 MDX ltac:(rewrite EX; lia) ltac:(rewrite EX; intros a Ha; apply QCR; lia) ltac:(rewrite EX; lia)) as (MEX & BLX & SLX).
    zstep. zstep. zstep. zstep.
    pose proof HSR as SSR. unfold ecp_sw_rhs_stmt in SSR.
    eapply aevtM_cut.
    { eapply SSR with (lo := lo) (h := h2) (LB := LB2) (dX := mpd_init (bv_unsigned spv + -80) padR) (dA := pt_X p) (G := G) (g := g) (cnt := cnt2);
        rewrite ?(unsigned_lit (bv_unsigned spv + -80)), ?HT2 by lia; cbn [md_addr md_own md_p md_n mpd_init];
        first [ exact HH2 | exact GR2 | exact H1 | exact GPS | exact GAS | exact GBS | exact PV | exact (proj1 TR2) | exact MEX | exact CNT2 | exact MCS | exact TP | exact SOK2 | exact CA | exact MI2 | exact MCG | exact ACL | exact DHI | exact MC1 | exact MC2
              | reflexivity | rewrite EX; reflexivity
              | discriminate
              | match goal with |- stk _ _ _ _ => replace (bv_unsigned spv + -80) with (bv_unsigned spv - 80) by lia; exact ST2' end
              | match goal with |- client_range _ _ _ G 192 => intros a Ha; destruct (GCR a Ha) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [exact (SUB2 _ Hb)| exact R]] end
              | match goal with |- ext_opnd _ _ _ _ _ _ _ => unfold ext_opnd, opnd_sep; cbn [md_addr md_own md_p md_n mpd_init]; rewrite EX;
                  split; [clear - QS SLO HLS; lia|];
                  split; [split; [intros NN; pose proof (SLX NN); lia|]; split; [intros; discriminate|]; split; [right; left; discriminate|]; split; [clear - QS SLO HLS; lia| intros NN; pose proof (SLX NN); lia]|];
                  split; [intros a Ha; destruct (QCR a ltac:(lia)) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [exact (SUB2 _ Hb)| exact R]]|];
                  split; [intros O a Ha; right; right; exists (md_p (pt_X p), 4 * md_n (pt_X p)); split; [exact (SUB2 _ (proj1 (BLX O)))| cbn; lia]|];
                  clear - MCQ; lia end
              | match goal with |- mpd_writable _ _ _ _ _ => unfold mpd_writable; cbn [md_addr md_own md_p md_n mpd_init];
                  split; [intros a Ha; left; lia|]; split; [intros a Ha Hd; exfalso; lia| intros; discriminate] end
              | match goal with |- _ -> _ => intros; first [discriminate| exfalso; congruence| lia] end
              | unfold ECP_SW_RHS_STACK; lia
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SSR. cbv beta. intros ms' mo' PO. unfold ecp_mul_mod_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & mo3 & h3 & LB3 & dR3 & r3 & cnt3 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned spv + -80)) in PO by lia.
    ddestruct PO as (MI3 & ST3 & MF3 & HT3 & HH3 & MA3 & OUT3 & PX3 & SOK3 & GR3 & CNT3 & RR3).
    replace (ret_pc (Z_to_bv 64 0x3a254)) with (Z_to_bv 64 0x3a254) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    dpose OUT3 as (EA3 & NS3 & K31 & K32 & K33). cbn [md_addr mpd_init] in EA3. pose proof RR3 as [_ (_ & _ & FRB3 & _)].
    destruct (heap_blocks _ _ HI _ _ _ _ HH3) as [HBR3 HAP3].
    assert (SUB32 : forall b, In b LB2 -> In b LB3) by (intros b Hb; apply (K32 b Hb); cbn; tauto).
    assert (STK3 : ck_st h LB (bv_unsigned spv) lo m mo h3 LB3 m3 mo3).
    { eapply (ck_st_step h LB (bv_unsigned spv) lo m mo h2 LB2 m2 mo2 h3 LB3 m3 mo3 LB2); [exact STK2| exact HH3| intros b Hb; exact (SUB32 _ (SUB2 _ Hb))| exact PX3| exact SUB2| | exact SOK3| exact MI3| exact MF3| exact HT3| exists cnt3; exact CNT3| replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia; exact ST3].
      intros a Ha HC HO. cbn. split; [| exact HO]. eapply (ck_out_stack h LB m mo); [exact HH| exact ACL| exact DHI| exact HC| lia| lia]. }
    assert (TR3 : ck_tmp LB LB3 m3 (bv_unsigned spv + -80) dR3).
    { refine (conj MA3 (conj EA3 (conj NS3 _))). intros b Hb C. destruct (FRB3 b Hb) as [C'|C']; [destruct C'| exact (C' (SUB2 _ C))]. }
    assert (TY3 : ck_tmp LB LB3 m3 (bv_unsigned spv + -64) dY2).
    { eapply ck_tmp_presx; [exact TY2| exact PX3| exact MI2| exact MI3| lia| cbn; lia|].
      intros O. ddestruct (BLY2 O) as (IN & N1 & P0 & B4). split; [exact IN|]. split; [apply SUB32; exact IN|]. cbn. split; [lia|]. split; [| exact I].
      pose proof (ck_blk_MC h2 LB2 m2 mo2 _ _ HH2 IN ltac:(lia) MC1 MC2). lia. }
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX3 FR2 ltac:(cbn; intros a Ha; left; lia) ltac:(cbn; lia)) as FR3.
    assert (COV3 : forall b, In b LB3 -> In b LB \/ In b (mpd_blk dY2) \/ In b (mpd_blk dR3)).
    { intros b Hb. destruct (K31 b Hb) as [C|C]; [| right; right; exact C]. destruct (COV2 b C) as [D|[D|D]]; [left; exact D| right; left; exact D| destruct D]. }
    assert (DIS3 : md_own dY2 = LHeap -> md_own dR3 = LHeap -> (md_p dY2, 4 * md_n dY2) <> (md_p dR3, 4 * md_n dR3)).
    { intros OY OR E. destruct (BLY2 OY) as (IN & _). destruct (FRB3 (md_p dR3, 4 * md_n dR3) ltac:(unfold mpd_blk; rewrite OR; left; reflexivity)) as [C|C]; [destruct C|].
      apply C. rewrite <- E. exact IN. }
    clear MK FR2 CR2. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
    zstep. if_cases K1; zify_cond K1.
    2:{ (* [comment removed for export] *) zstep. eapply ck_cleanup; [exact CTX| exact STK3| exact TY3| exact TR3| exact DIS3| exact COV3| exact FR3| exact TP| exact (proj1 RR3)]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof HCMP as SC. unfold mpi_cmp_mpi_stmt in SC.
    assert (BLR3 : md_own dR3 = LHeap -> In (md_p dR3, 4 * md_n dR3) LB3 /\ 1 <= md_n dR3 /\ 0 < md_p dR3 /\ md_p dR3 + 4 * md_n dR3 <= alloc_ceiling).
    { intros O. ddestruct (mpdr_blk_facts usegs L m3 LB3 dR3 (proj1 MA3) O HBR3) as (I1 & I2 & I3 & I4 & _). auto. }
    eapply aevtM_cut_evt; [exact MK| eapply SC with (LB := LB3) (dX := dY2) (dY := dR3); [exact (proj1 TY3)| exact MA3| intros O; pose proof (BLY2 O); lia| intros O; pose proof (BLR3 O); lia| exact MI3| rewrite EA2; reflexivity| rewrite EA3; reflexivity] |].
    clear SC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & _).
    replace (ret_pc (Z_to_bv 64 0x3a390)) with (Z_to_bv 64 0x3a390) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lazymatch goal with |- context [Z.sgn ?v] => destruct (Z.sgn_spec v) as [[_ EE]|[[_ EE]|[_ EE]]]; rewrite EE end.
    all: zstep; zstep; zstep; zstep; zstep; zstep.
    all: try norm_ret.
    all: eapply ck_cleanup; [exact CTX| exact STK3| exact TY3| exact TR3| exact DIS3| exact COV3| exact FR3| exact TP| lia].
  all: match goal with |- ?gg => idtac "SWLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma grp_P_own : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Pm,P,(2.&40.)(3.(2.&8.))PLB,(6.$7.)PG,$8.Pg,$2;.P,(21.$52.VMT,R4.R3.R2.R1.)P,(2>.(:.$8.(2?.R2.)+1.)(:.$8.(2?.R2.)+2.))(30.(:.$4=.(4>.(36.R3.))$4?.))")
(* [comment removed for export] *).
  Proof.
    intros m LB G g HG H12. ddestruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REST).
    ddestruct REST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KEPT & _).
    unfold grp_kept_mpds in KEPT. destruct H12 as [E|E]; rewrite E in KEPT; cbn [Z.eqb Pos.eqb] in KEPT; apply (proj1 (Forall_forall _ _) KEPT); cbn; auto.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L47801051489.41L63381042064.41000001002SS". (* [comment removed for export] *)
  #[using="DIMG ROIMG IMGC"] Lemma mx_P_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PdX,$2=.PG,$8.Pg,$2;.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph1,(5.$52.VL,VHI,)PLB1,(6.$7.)PdX1,$2=.Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$4.PSP,$8.P,(70.VL,R=.R<.R;.+5<?:8.R1.=R9.(16.$52.VL,VHI,R>.)R:.)P,(5=.$52.R9.R>.R=.)P,(2>.(:.$8.(2?.R<.)+1.)(:.$8.(2?.R<.)+2.))P,(:.$8.(35.(36.R=.))+1.)P,(71.$52.VL,VHI,VMT,R12.R11.R10.R?.R>.+5<?:8.R5.=R=.R<.R;.R:.R9.R8.R7.R6.)(9.(5=.$52.R8.R:.(36.R?.))(9.(72.R9.(36.R?.))(9.(73.R9.(36.R?.)R>.R6.)(9.(3:.VL,R:.R>.(5>.(36.R?.))+10.)(9.P,(:.$4=.(4>.(36.R?.))$4?.)(3:.VL,R;.R?.(31.(36.R10.))(50.+4.(51.(36.R10.))))(9.(:.$8.(5>.(36.R?.))(1>.R10.+8.))(30.(:.$4=.(4>.(36.R?.))$4?.))))))))")
(* [comment removed for export] *).
  Proof.
    intros h LB dX G g lo m mo h1 LB1 dX1 m1 mo1 SP BASE MA H12 GPS INV.
    dpose INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GR1 & _).
    dpose GR1 as (_ & _ & _ & EP & _ & _ & _ & MP & _).
    pose proof (grp_P_own m1 LB1 G g GR1 H12) as POWN.
    pose proof (mm_grp_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT SP 0 lo m mo h1 LB1 dX1 m1 mo1 (g_P g) 8 ROIMG IMGC BASE MA INV MP POWN (or_introl GPS) EP ltac:(lia) ltac:(lia)) as B.
    rewrite Z.sub_0_r in B. ddestruct B as (B1 & B2 & B3 & B4 & B5). exact (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj EP POWN)))))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L36549784906.7300000HS1L3HLS2SP2lo3dX02A13SLO". (* [comment removed for export] *)
  #[using="HLS DIMG IMGC"] Lemma ck_st_of_mm : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.PSP,$8.Plo,$8.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Pm0,P,(2.&40.)(3.(2.&8.))PdX0,$2=.Ph1,(5.$52.VL,VHI,)PLB1,(6.$7.)PdX1,$2=.Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$4.P,(5<.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(63.R15.R14.R<.R;.R:.R9.R15.R14.R8.R9.)P,(71.$52.VL,VHI,VMT,R16.R15.R8.R14.R12.+5<?:8.(43.R=.+50.)=R<.R9.R:.R7.R6.R5.R4.R3.)P,(:.$4=.(4>.R9.)$5?.)P,(29.(43.R?.+50.)(5>.R:.))P,(29.(1>.(5>.R;.)+10.)R10.)(9.(63.R1:.R19.R11.R10.R?.R>.R;.R:.R8.R7.)(9.(69.R19.R:.R8.(5>.R<.)R9.)Pb,$7.P,(19.$7.R1.R;.)(2>.(19.$7.R2.R1;.)(19.$7.R2.(62.R;.)))))")
(* [comment removed for export] *).
  Proof.
    intros until mo1. intros CTX ST0 INV O0 A1 A2.
    dpose CTX as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SLO & ACL & _ & _ & DHI & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    dpose INV as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & CNT1 & ST1).
    dpose OUT1 as (EA1 & NS1 & K11 & K12 & K13). rewrite Z.sub_0_r in ST1.
    assert (B0 : mpd_blk dX0 = []) by (unfold mpd_blk; rewrite O0; reflexivity).
    assert (SUB1 : forall b, In b LB -> In b LB1) by (intros b Hb; apply (K12 b Hb); rewrite B0; intros []).
    split; [| split].
    - eapply (ck_st_step h LB SP lo m mo h LB m0 mo h1 LB1 m1 mo1 LB); [exact ST0| exact HH1| exact SUB1| exact PX1| intros b Hb; exact Hb| | exact SOK1| exact MI1| exact MF1| exact HT1| exact CNT1| exact ST1].
      intros a Ha HC HO. unfold mpd_ivs. rewrite O0. cbn. split; [| exact HO]. eapply (ck_out_stack h LB m mo); [exact HH| exact ACL| exact DHI| exact HC| lia| exact A2].
    - refine (conj MA1 (conj EA1 (conj NS1 _))). intros b Hb. destruct (FR1 b Hb) as [C|C]; [rewrite B0 in C; destruct C| exact C].
    - exact K11.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L10883024532.136L24250753214.136L24250866695.137L25992107667.137L35626856451.97 L43154656689.109L44336101011.137L5067590663.137 L5067681982.136 L51523620783.139L51523620783.140L58194387178.137L58751487531.109L59073709382.97 L59075856118.109L66827405845.97 00000500:00?00`00e00j01K01P01U01_01i02?02D02I02N02SS3spvS3spvS3spvS1L3HLS3spv2lo3dX13SPB3SLO3ACL2B4S3spvS3spvS1L3HLS3spv2lo3dX13SPB3SLO3ACL2B4S3spvS3spvS3spv1a2HaS3spv1a2HaS1L3HLS3spv2lo3SPB3SLOS3spvS3spvS3spvS3spv". (* [comment removed for export] *)
  #[using="HLS DIMG IMGC HND HFREEM"] Lemma ck_mx_fin : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Prae,(2.&40.)Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0e,(2.&40.)Ps1e,(2.&40.)Ps2e,(2.&40.)Ps3e,(2.&40.)Ps4e,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pra0,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0c,(2.&40.)Ps2c,(2.&40.)Ps3c,(2.&40.)Ps4c,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Pm0,P,(2.&40.)(3.(2.&8.))PpadX,(2.&40.)Ph1,(5.$52.VL,VHI,)PLB1,(6.$7.)PdX1,$2=.Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$4.Pjr,(6.(2.&8.))Pr,$8.P,(5<.R13.R12.R11.R10.R?.R>.R=.R<.R;.(14.&40.R3:.)R:.R15.R14.)P,(63.R14.R13.(14.&40.R3;.)R;.R16.R15.R14.R13.R:.R15.)P,(71.$52.VL,VHI,VMT,R15.R14.(74.(1>.(14.&40.R3<.)-40.)R:.)R13.R11.+5<?:8.(1>.(14.&40.R3<.)-50.)=R<.R;.R16.R9.R8.R7.R6.R5.)P,(23.$52.R7.(1>.(14.&40.R3=.)-30.)(54.R36.R37.R38.R39.R3:.R3>.))P,(23.$52.R8.(1>.(14.&40.R3>.)-50.)(1;.$24.(6>.#10.R6.)(1?.$24.)))P,(:.(2.&40.)R3=.(>.&40.(47.VL,)))P,(9.(26.(27.(28.+2.+1?.))R7.)(29.R7.=))(49.$52.R:.(4:.$52.VL,VHI,VMT,R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R1>.R1=.R1:.R19.R18.R16.R17.R15.+5<?:8.R11.R1<.R1;.)(<.(=.R32.(>.&40.(1>.(14.&40.R41.)-50.))R40.R3?.R31.R30.R2?.R2>.(>.&40.R8.)R2:.R29.R28.R27.R26.R25.R24.R23.R2=.R2<.R2;.R39.R38.R37.R36.R35.R34.R33.R22.R21.R20.R1?.)R1>.(>.&40.+3:368.)R1=.(10.(2.&40.))R;.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros CTX ST0 INV FR J1 TP Hr. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose CTX as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MC1 & MC2 & MCS & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & SPA & DHI & MI & _ & CA & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    destruct (ck_st_of_mm h LB G Q g p cnt bp1 bp2 (bv_unsigned spv) lo m mo m0 _ h1 LB1 dX1 m1 mo1 CTX ST0 ltac:(replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia; exact INV) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as (ST1 & TX1 & COV1).
    cbn [md_addr mpd_init] in TX1. dpose TX1 as (MA1 & EA1 & NS1 & FRB1).
    dpose ST1 as (HH1 & SUB1 & _ & _ & MI1 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK. pose proof (HND _ _ _ _ HH1) as ND1.
    unfold ck_frame in FR.
    zstep. zstep.
    eapply ck_free with (d := dX1); [exact CTX| exact ST1| rewrite EA1; exact TX1| rewrite EA1; lia| rewrite EA1; lia| lia| reflexivity| exact TP| rewrite EA1; reflexivity|].
    intros m2 mo2 h2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ST2 CH2 PX2 BL1 _. rewrite EA1 in CH2, PX2.
    dpose ST2 as (HH2 & SUB2 & _ & _ & MI2 & _ & _ & _ & STK2). clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    assert (DR : disjoint_from ((bv_unsigned spv + -64, bv_unsigned spv + -64 + 16) :: mpi_free_X (md_own dX1) (md_p dX1) (md_n dX1)) (bv_unsigned spv + -80) 16
              /\ disjoint_from ((bv_unsigned spv + -64, bv_unsigned spv + -64 + 16) :: mpi_free_X (md_own dX1) (md_p dX1) (md_n dX1)) (bv_unsigned spv + -48) 48).
    { cbn. unfold mpi_free_X. destruct (md_own dX1) eqn:O; cbn; [split; (split; [lia| exact I])| | split; (split; [lia| exact I])].
      ddestruct (BL1 eq_refl) as (_ & _ & _ & B4). split; (split; [lia|]); (split; [lia| exact I]). }
    destruct DR as [DRJ DRF].
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 J1 ltac:(cbn; intros a Ha; left; lia) DRJ) as J2.
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 FR ltac:(cbn; intros a Ha; left; lia) DRF) as FR2.
    clear FR J1 PX2.
    zstep. zstep.
    assert (LOC : rw_cells usegs m2 (bv_unsigned spv + -80) ([CB 16 jr] ++ mpi_cells 0 (Z_to_bv 64 1) 0 (md_pad dX1))).
    { apply (proj2 (rw_cells_app usegs _ _ _ _)). split; [exact J2|]. cbn [cells_size csize Nat.add].
      replace (bv_unsigned spv + -80 + Z.of_nat 16) with (bv_unsigned spv + -64) by lia. exact CH2. }
    eapply ck_exit; [| exact FR2| exact LOC| reflexivity| lia| exact Hr].
    eapply ck_st_fin; [exact CTX| exact ST2|].
    intros b Hb. pose proof (lb_free_mpd_sub _ _ _ Hb) as Hb1.
    destruct (COV1 b Hb1) as [Hl|Hx]; [exact Hl| exfalso].
    unfold mpd_blk in Hx. destruct (md_own dX1) eqn:OX; try (destruct Hx; fail). destruct Hx as [<-|[]].
    unfold lb_free_mpd in Hb. rewrite OX in Hb. exact (lb_remove_notin _ _ _ ND1 Hb).
  all: match goal with |- ?gg => idtac "MXFINLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L10355920871.113L12403419465.113L19142102195.159L23770485751.137L246904349.143  L26151833876.113L2733944746.161 L28008468253.139L29010565666.141L40597656024.138L42006458290.160L51523620783.139L52067409697.159L52514112645.159L53519240741.159L60874069005.113L61274419565.143L61274507994.161L63261865031.7  L64318306584.11300000>00C00D00I00N00S00`01A01B01G01N01X01Y01f02302802=02J02W02\S1L3spv2lo3SLOS3spvFS3spvS3spvS3spvS3spv1g3dX21rS1L3HLS3spv2lo3dX13SPB3SLO3ACL2B4FS3spvS3spv1rS3spv1a2HaFS3spv1g3dX21rS3spv1g3dX21rS3spvS3spvS3spv1g3dX21rS3spv3SPB3SPAS3spv". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HND HFREEM HADDI HCMP"] Lemma ck_mx_addint : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Prae,(2.&40.)Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0e,(2.&40.)Ps1e,(2.&40.)Ps2e,(2.&40.)Ps3e,(2.&40.)Ps4e,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pra0,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1c,(2.&40.)Ps2c,(2.&40.)Ps3c,(2.&40.)Ps4c,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Pm0,P,(2.&40.)(3.(2.&8.))PpadX,(2.&40.)Ph1,(5.$52.VL,VHI,)PLB1,(6.$7.)PdX1,$2=.Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$4.Pjr,(6.(2.&8.))P,(5<.R12.R11.R10.R?.R>.R=.R<.R;.R:.(14.&40.R39.)R9.R14.R13.)P,(63.R13.R12.(14.&40.R3:.)R:.R15.R14.R13.R12.R9.R14.)P,(70.VL,R13.(74.(1>.(14.&40.R3;.)-40.)R9.)R12.+5<?:8.(1>.(14.&40.R3;.)-50.)=R;.(16.$52.VL,VHI,R14.)R10.)P,(5=.$52.R;.R14.(74.(1>.(14.&40.R3<.)-40.)R:.))P,(71.$52.VL,VHI,VMT,R16.R15.(74.(1>.(14.&40.R3=.)-40.)R;.)R14.R12.+5<?:8.(1>.(14.&40.R3=.)-50.)=R=.R<.R17.R:.R9.R8.R7.R6.)P,(23.$52.R8.(1>.(14.&40.R3>.)-30.)(54.R37.R38.R39.R3:.R3;.R3?.))P,(23.$52.R9.(1>.(14.&40.R3?.)-50.)(1;.$24.(6>.#10.R7.)(1?.$24.)))P,(:.(2.&40.)R3>.(>.&40.(47.VL,)))(49.$52.R:.(4:.$52.VL,VHI,VMT,R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R1>.R1=.R1:.R19.R18.R16.R17.R15.+5<?:8.R11.R1<.R1;.)(<.(=.R32.(>.&40.(1>.(14.&40.R41.)-50.))R40.R3?.R31.R30.R2?.(>.&40.(1>.R18.+8.))R2>.R2:.R29.R28.R27.R26.R25.R24.R23.R2=.R2<.R2;.R39.R38.R37.R36.R35.R34.R33.R22.R21.R20.R1?.)R1>.(>.&40.+3:350.)R1=.(10.(2.&40.))R;.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until jr. intros CTX ST0 BASE MA0 INV FR J1 TP. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose CTX as (HH & GR & GKIND & GPS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MC1 & MC2 & MCS & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & SPA & DHI & MI & _ & CA & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    assert (H12 : g_h g = 1 \/ g_h g = 2) by (destruct GKIND as [(E & _)|(E & _)]; [left| right]; exact E).
    dpose INV as (HH1 & MA1 & OUT1 & _). dpose OUT1 as (EA1 & NS1 & _). cbn [md_addr mpd_init] in EA1.
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _]. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    assert (BL1 : md_own dX1 = LHeap -> In (md_p dX1, 4 * md_n dX1) LB1 /\ 1 <= md_n dX1 /\ 0 < md_p dX1 /\ md_p dX1 + 4 * md_n dX1 <= alloc_ceiling).
    { intros O. ddestruct (mpdr_blk_facts usegs L m1 LB1 dX1 (proj1 MA1) O HBR1) as (I1 & I2 & I3 & I4 & _). auto. }
    unfold ck_frame in FR.
    zstep. zstep. zstep. zstep.
    destruct (mm_self_opnd usegs L HI DIMG MT h LB _ G g U_MUL_COUNT (bv_unsigned spv + -80) 0 lo m0 mo h1 LB1 dX1 m1 mo1 BASE MA0 INV) as (SXX & OXX & CRX & CRXL).
    rewrite Z.sub_0_r in OXX.
    eapply (mm_call_intop usegs L HI DIMG) with (FRA := bv_unsigned spv + -48) (FRC := ck_frame s4e s3e s2e s1e s0e rae) (b := 1);
      [exact HADDI| intros ? ? ? ? ? ? [_ KP]; exact KP| exact BASE| exact MA0| exact INV| lia| exact FR| lia| cbn; lia
      | exact MA1| exact SXX| exact OXX| exact CRX| exact CRXL| lia
      | lia| exact HLS| clear - SPA SPB SLO HLS; lia| exact TP| exact CA| first [reflexivity| rewrite EA1; reflexivity]| first [reflexivity| rewrite EA1; reflexivity]| reflexivity|].
    intros m2 mo2 h2 LB2 dX2 r ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 FR2 RR2 PXs.
    replace (ret_pc (Z_to_bv 64 0x3a360)) with (Z_to_bv 64 0x3a360) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (J2 : rw_cells usegs m2 (bv_unsigned spv + -80) [CB 16 jr]).
    { eapply heap_presx_rw_cells; [exact PXs| exact J1| cbn; intros a Ha; left; lia|]. unfold mpd_ivs. rewrite EA1.
      destruct (md_own dX1) eqn:O; cbn; [split; [lia| exact I]| | exfalso; congruence].
      split; [lia|]. split; [| exact I]. ddestruct (BL1 eq_refl) as (_ & _ & _ & B4). lia. }
    dpose INV2 as (HH2 & MA2 & OUT2 & _). pose proof OUT2 as (EA2 & _). cbn [md_addr mpd_init] in EA2. clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    unfold ck_frame in FR2.
    zstep. if_cases K0; zify_cond K0.
    2:{ zstep. eapply ck_mx_fin; [exact CTX| exact ST0| exact INV2| exact FR2| exact J2| exact TP| ddestruct RR2 as [[(Er & _)|Er] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    destruct (mx_P_opnd h LB _ G g lo m0 mo h2 LB2 dX2 m2 mo2 _ BASE MA0 H12 GPS INV2) as (MP2 & _ & _ & _ & _ & EP & POWN).
    eapply (mm_call_cmp usegs L HI); [exact HCMP| exact INV2| exact MP2| intros O; exfalso; exact (POWN O)| first [reflexivity| rewrite EA2; reflexivity]| rewrite EP; reflexivity|].
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?. replace (ret_pc (Z_to_bv 64 0x3a3b4)) with (Z_to_bv 64 0x3a3b4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lazymatch goal with |- context [Z.sgn ?v] => destruct (Z.sgn_spec v) as [[_ EE]|[[_ EE]|[_ EE]]]; rewrite EE end.
    all: zstep; zstep; zstep; zstep; zstep; zstep.
    all: try norm_ret.
    all: eapply ck_mx_fin; [exact CTX| exact ST0| exact INV2| exact FR2| exact J2| exact TP| lia].
  all: match goal with |- ?gg => idtac "ADDLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0@L10582180398.7  L11801439651.137L11805421443.137L16075573631.156L16075573758.171L16075584458.130L22704459657.138L23026407728.136L26056219956.136L26058315139.118L2734101533.133 L2734108201.174 L2734108328.159 L3399871065.144 L3399871065.145 L35626725506.135L36396844203.158L3818669308.118 L3820768890.7   L40147641242.144L40147641242.145L40682824487.143L47945240939.142L53134233046.117L53938477558.119L54221100978.173L59073840583.135L59355459711.120L60976021004.118L61489748167.143L61757190933.142L63261865031.7  L64312278295.7  L66827537044.13500000F00K00P00Q00R00S01001501]02E02N02[02h03603D03M03V03d03e04A04]05=05F05f06B06K06T06e06m07607V07c07h081S1L3HLS3spv2lo3SPB3SLOS3spvS3spvFFFS1L3HLS3spv2lo3SPB3SLO2xx3HxxS3spvS1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACLS3spv3dX1S3spv3bp23dX1S3spv3bp13dX1S3spv3dX11a2HaS3spv3dX11a2HaS3spv3dX1S3spv3dX1S1L3spv2lo3ACLFS1L3spv3dX13SPB3MC23BPL1a2HaS1L3spv3dX13SPB3MC23BPL1a2HaS1L4DIMG4IMGC3spv2lo3dX13MC23ACLS3spv3dX1S1L4DIMG4IMGC3spv2lo3SPB3MC23ACLS1L3spv2lo3LB13dX13SPB3ACL1HS3spv3dX1S3spv3dX1S1L3spv3LB13dX11HS3spv2loS3spv3dX1S1L4DIMG4IMGC3spv2lo3dX13MC23ACLS3spv3SPB3SPAS3spvS3spv3dX1". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HND HFREEM HADDI HCMP HCMPI"] Lemma ck_mx_tail : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Prae,(2.&40.)Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0e,(2.&40.)Ps1e,(2.&40.)Ps2e,(2.&40.)Ps3e,(2.&40.)Ps4e,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pra0,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1c,(2.&40.)Ps2c,(2.&40.)Ps3c,(2.&40.)Ps4c,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Pm0,P,(2.&40.)(3.(2.&8.))PpadX,(2.&40.)Ph1,(5.$52.VL,VHI,)PLB1,(6.$7.)PdX1,$2=.Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$4.Pjr,(6.(2.&8.))P,(5<.R12.R11.R10.R?.R>.R=.R<.R;.R:.(14.&40.R39.)R9.R14.R13.)P,(63.R13.R12.(14.&40.R3:.)R:.R15.R14.R13.R12.R9.R14.)P,(70.VL,R13.(74.(1>.(14.&40.R3;.)-40.)R9.)R12.+5<?:8.(1>.(14.&40.R3;.)-50.)=R;.(16.$52.VL,VHI,R14.)R10.)P,(5=.$52.R;.R14.(74.(1>.(14.&40.R3<.)-40.)R:.))P,(71.$52.VL,VHI,VMT,R16.R15.(74.(1>.(14.&40.R3=.)-40.)R;.)R14.R12.+5<?:8.(1>.(14.&40.R3=.)-50.)=R=.R<.R17.R:.R9.R8.R7.R6.)P,(23.$52.R8.(1>.(14.&40.R3>.)-30.)(54.R37.R38.R39.R3:.R3;.R3?.))P,(23.$52.R9.(1>.(14.&40.R3?.)-50.)(1;.$24.(6>.#10.R7.)(1?.$24.)))P,(:.(2.&40.)R3>.(>.&40.(47.VL,)))(49.$52.R:.(4:.$52.VL,VHI,VMT,R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R1>.R1=.R1:.R19.R18.R16.R17.R15.+5<?:8.R11.R1<.R1;.)(<.(=.R32.(>.&40.(1>.(14.&40.R41.)-50.))R40.R3?.R31.R30.R2?.(>.&40.(1>.R18.+8.))R2>.R2:.R29.R28.R27.R26.R25.R24.R23.R2=.R2<.R2;.R39.R38.R37.R36.R35.R34.R33.R22.R21.R20.R1?.)R1>.(>.&40.+3:308.)R1=.(10.(2.&40.))R;.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until jr. intros CTX ST0 BASE MA0 INV FR J1 TP. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose CTX as (HH & GR & GKIND & GPS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MC1 & MC2 & MCS & BP1 & BP2 & BPL & BPH & BPS & MCB & SLO & ACL & HTOP & SPA & DHI & MI & _ & CA & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    dpose INV as (HH1 & MA1 & OUT1 & _ & _ & _ & _ & _ & MI1 & _ & _ & _ & _ & ST1). dpose OUT1 as (EA1 & NS1 & _). cbn [md_addr mpd_init] in EA1.
    rewrite Z.sub_0_r in ST1.
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _]. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    assert (BL1 : md_own dX1 = LHeap -> In (md_p dX1, 4 * md_n dX1) LB1 /\ 1 <= md_n dX1 /\ 0 < md_p dX1 /\ md_p dX1 + 4 * md_n dX1 <= alloc_ceiling).
    { intros O. ddestruct (mpdr_blk_facts usegs L m1 LB1 dX1 (proj1 MA1) O HBR1) as (I1 & I2 & I3 & I4 & _). auto. }
    assert (XS1 : md_p dX1 + 4 * md_n dX1 <= lo \/ bv_unsigned spv + -80 <= md_p dX1).
    { pose proof MA1 as [(_ & _ & _ & _ & _ & HO) _]. destruct (md_own dX1) eqn:O; [destruct HO as [-> ->]; left; lia| pose proof (BL1 eq_refl); left; lia| exfalso; congruence]. }
    unfold ck_frame in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof HCMPI as SC. unfold mpi_cmp_int_stmt in SC.
    eapply aevtM_cut_evt; [exact MK| eapply SC with (LB := LB1) (dX := dX1) (z := 1) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned spv + -80)) by lia;
      first [ exact MA1 | exact MI1 | exact XS1 | exact ST1
            | rewrite EA1; reflexivity | reflexivity
            | intros O; pose proof (BL1 O); lia
            | rewrite EA1; lia
            | clear - SPA SPB SLO HLS; lia
            | lia ] |].
    clear SC. cbv beta. intros ms' PO. unfold mpi_cmp_int_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU & WM & MI2 & ST2).
    rewrite ?(unsigned_lit (bv_unsigned spv + -80)) in MU, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x3a314)) with (Z_to_bv 64 0x3a314) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (INV2 : mm_inv usegs L HI MT h LB (mpd_init (bv_unsigned spv + -64) padX) G g U_MUL_COUNT (bv_unsigned spv + -80) 0 lo m0 mo h1 LB1 dX1 m2 mo1).
    { eapply (mm_inv_callee usegs L HI DIMG); [exact BASE| exact MA0| exact INV| exact MU| exact WM| exact MI2| unfold sub_fp; cbn; intros xx Hxx; lia| rewrite Z.sub_0_r; exact ST2]. }
    eapply rw_cells_transport in FR; [| exact MU| exact WM| cbn; lia]. eapply rw_cells_transport in J1; [| exact MU| exact WM| cbn; lia].
    clear MU WM INV MI1 ST1.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) zstep. zstep. zstep. eapply ck_mx_fin; [exact CTX| exact ST0| exact INV2| exact FR| exact J1| exact TP| lia]. }
    zstep. zstep. if_cases KB; zify_cond KB.
    { (* [comment removed for export] *) eapply ck_mx_addint; [exact CTX| exact ST0| exact BASE| exact MA0| exact INV2| exact FR| exact J1| exact TP]. }
    (* [comment removed for export] *)
    destruct (ck_st_of_mm h LB G Q g p cnt bp1 bp2 (bv_unsigned spv) lo m mo m0 _ h1 LB1 dX1 m2 mo1 CTX ST0 ltac:(replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia; exact INV2) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as (STm & _ & _).
    dpose BP1 as (MB1 & EB1 & OB1 & _). dpose BP2 as (MB2 & EB2 & OB2 & _). unfold U_BAD_POINTS in EB1, EB2, BPL, BPH, BPS, MCB.
    destruct (ck_st_mpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bp1 CTX STm MB1 ltac:(rewrite EB1; lia) ltac:(rewrite EB1; intros a Ha; right; left; split; [lia| apply BPS; lia]) ltac:(rewrite EB1; lia)) as (MB1' & _ & _).
    destruct (ck_st_mpd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bp2 CTX STm MB2 ltac:(rewrite EB2; lia) ltac:(rewrite EB2; intros a Ha; right; left; split; [lia| apply BPS; lia]) ltac:(rewrite EB2; lia)) as (MB2' & _ & _).
    zstep. zstep. zstep. zstep.
    eapply (mm_call_cmp usegs L HI); [exact HCMP| exact INV2| exact MB1'| rewrite OB1; intros; discriminate| first [reflexivity| rewrite EA1; reflexivity]| rewrite EB1; reflexivity|].
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?. replace (ret_pc (Z_to_bv 64 0x3a330)) with (Z_to_bv 64 0x3a330) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep. zstep. if_cases KC; zify_cond KC.
    { eapply ck_mx_fin; [exact CTX| exact ST0| exact INV2| exact FR| exact J1| exact TP| lia]. }
    zstep. zstep. zstep. zstep.
    eapply (mm_call_cmp usegs L HI); [exact HCMP| exact INV2| exact MB2'| rewrite OB2; intros; discriminate| first [reflexivity| rewrite EA1; reflexivity]| rewrite EB2; reflexivity|].
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?. replace (ret_pc (Z_to_bv 64 0x3a34c)) with (Z_to_bv 64 0x3a34c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. if_cases KD; zify_cond KD.
    { eapply ck_mx_fin; [exact CTX| exact ST0| exact INV2| exact FR| exact J1| exact TP| lia]. }
    eapply ck_mx_addint; [exact CTX| exact ST0| exact BASE| exact MA0| exact INV2| exact FR| exact J1| exact TP].
  all: match goal with |- ?gg => idtac "TAILLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L12403419465.140L16075584458.134L246894383.167  L26151833876.140L28008468253.166L28245028907.135L29010567952.165L36242951655.140L38800589815.164L40597656024.165L45914717502.9  L51523620783.166L59308630497.165L60874069005.140L61274409055.167L63219124928.137L63261865031.7  L63846984433.86 L65683236014.7  00000@00A00Q00a01I01Y01Z02302C02S02n03C03V03f04604O04\07I07ZS1n3spv3dX14MEASFS1n3spv3dX14MEASS1n3spv3dX14MEASS1L3HLS1n3spv2lo3dX14MEAS3SPB3SLO3ACL2B4S1n3spv3dX14MEASFS1L1n3spv2lo3dX14MEAS3SLOS1n3spv3dX14MEASS1n3spv3dX14MEASS1n1g3dX14MEAS2PV2GE3dX22V2S1n3spv3dX14MEAS1a2HaS1n3spv3dX14MEAS2KBS1n3spv3dX14MEASS1n3spv3dX14MEASS1n3spv1g3dX14MEAS3SPB2K0S3spv3SPB3SPAS1L2HI2MT3rae3spv2gp2tp3s0e3s1e3s2e3s3e3s4e2s52s62s72s82s93s103s113ra02t02t12t23s1c3s2c3s3c3s4c2a02a12a22a32a42a52a62a72t32t42t52t61F2fc1m2mo1h2LB1G1Q1g1p2lo3dX12m13mo14MEASS1g3dX12GE3dX22V2". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HND HFREEM HSUBM HADDI HCMP HCMPI"] Lemma ck_mx_loop : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Pn,$75.Prae,(2.&40.)Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0e,(2.&40.)Ps1e,(2.&40.)Ps2e,(2.&40.)Ps3e,(2.&40.)Ps4e,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pra0,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1c,(2.&40.)Ps2c,(2.&40.)Ps3c,(2.&40.)Ps4c,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Pm0,P,(2.&40.)(3.(2.&8.))PpadX,(2.&40.)Ph1,(5.$52.VL,VHI,)PLB1,(6.$7.)PdX1,$2=.Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$4.Pjr,(6.(2.&8.))P,(76.(77.(39.R4.))R3;.)P,(29.=(39.R5.))P,(5<.R14.R13.R12.R11.R10.R?.R>.R=.R<.(14.&40.R3;.)R;.R16.R15.)P,(63.R15.R14.(14.&40.R3<.)R<.R17.R16.R15.R14.R;.R16.)P,(70.VL,R15.(74.(1>.(14.&40.R3=.)-40.)R;.)R14.+5<?:8.(1>.(14.&40.R3=.)-50.)=R=.(16.$52.VL,VHI,R16.)R12.)P,(5=.$52.R=.R16.(74.(1>.(14.&40.R3>.)-40.)R<.))P,(71.$52.VL,VHI,VMT,R18.R17.(74.(1>.(14.&40.R3?.)-40.)R=.)R16.R14.+5<?:8.(1>.(14.&40.R3?.)-50.)=R?.R>.R19.R<.R;.R:.R9.R8.)P,(23.$52.R:.(1>.(14.&40.R40.)-30.)(54.R39.R3:.R3;.R3<.R3=.R41.))P,(23.$52.R;.(1>.(14.&40.R41.)-50.)(1;.$24.(6>.#10.R9.)(1?.$24.)))P,(:.(2.&40.)R40.(>.&40.(47.VL,)))(49.$52.R<.(4:.$52.VL,VHI,VMT,R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R20.R1?.R1<.R1;.R1:.R18.R19.R17.+5<?:8.R13.R1>.R1=.)(<.(=.R34.(>.&40.(1>.(14.&40.R43.)-50.))R42.R41.R33.R32.R31.(>.&40.(1>.R1:.+8.))R30.R2<.R2;.R2:.R29.R28.R27.R26.R25.R2?.R2>.R2=.R3;.R3:.R39.R38.R37.R36.R35.R24.R23.R22.R21.)R20.(>.&40.+3:2>0.)R1?.(10.(2.&40.))R=.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until jr; intros MEAS VX CTX ST0 BASE MA0 INV FR J1 TP; [lia|]. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose CTX as (HH & GR & GKIND & GPS & _ & _ & PV & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MC1 & MC2 & MCS & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & SPA & DHI & MI & _ & CA & _).
    unfold ECP_CHECK_PUBKEY_STACK in SLO.
    assert (H12 : g_h g = 1 \/ g_h g = 2) by (destruct GKIND as [(E & _)|(E & _)]; [left| right]; exact E).
    dpose INV as (HH1 & MA1 & OUT1 & _). dpose OUT1 as (EA1 & NS1 & _). cbn [md_addr mpd_init] in EA1.
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _]. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    assert (BL1 : md_own dX1 = LHeap -> In (md_p dX1, 4 * md_n dX1) LB1 /\ 1 <= md_n dX1 /\ 0 < md_p dX1 /\ md_p dX1 + 4 * md_n dX1 <= alloc_ceiling).
    { intros O. ddestruct (mpdr_blk_facts usegs L m1 LB1 dX1 (proj1 MA1) O HBR1) as (I1 & I2 & I3 & I4 & _). auto. }
    destruct (mx_P_opnd h LB _ G g lo m0 mo h1 LB1 dX1 m1 mo1 _ BASE MA0 H12 GPS INV) as (MP1 & SXP & OXP & CRP & CRPL & EP & POWN).
    unfold ck_frame in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply (mm_call_cmp usegs L HI); [exact HCMP| exact INV| exact MP1| intros O; exfalso; exact (POWN O)| first [reflexivity| rewrite EA1; reflexivity]| rewrite EP; reflexivity|].
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?. replace (ret_pc (Z_to_bv 64 0x3a2ec)) with (Z_to_bv 64 0x3a2ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) eapply ck_mx_tail; [exact CTX| exact ST0| exact BASE| exact MA0| exact INV| exact FR| exact J1| exact TP]. }
    assert (GE : mpd_val (g_P g) <= mpd_val dX1) by (pose proof (Z.sgn_spec (mpd_val dX1 - mpd_val (g_P g))); lia). clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    destruct (mm_self_opnd usegs L HI DIMG MT h LB _ G g U_MUL_COUNT (bv_unsigned spv + -80) 0 lo m0 mo h1 LB1 dX1 m1 mo1 BASE MA0 INV) as (SXX & OXX & CRX & CRXL).
    rewrite Z.sub_0_r in OXX.
    eapply (mm_call_binop usegs L HI DIMG) with (FRA := bv_unsigned spv + -48) (FRC := ck_frame s4e s3e s2e s1e s0e rae);
      [exact HSUBM| intros ? ? ? ? ? ? [_ KP]; exact KP| exact BASE| exact MA0| exact INV| lia| exact FR| lia| cbn; lia
      | exact MA1| exact MP1| exact SXX| exact SXP| exact SXP| exact OXX| exact OXP| exact CRX| exact CRXL| exact CRP| exact CRPL
      | lia| exact HLS| clear - SPA SPB SLO HLS; lia| exact TP| exact CA| first [reflexivity| rewrite EA1; reflexivity]| first [reflexivity| rewrite EA1; reflexivity]| rewrite EP; reflexivity|].
    intros m2 mo2 h2 LB2 dX2 r ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 FR2 RR2 PXs.
    replace (ret_pc (Z_to_bv 64 0x3a300)) with (Z_to_bv 64 0x3a300) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (J2 : rw_cells usegs m2 (bv_unsigned spv + -80) [CB 16 jr]).
    { eapply heap_presx_rw_cells; [exact PXs| exact J1| cbn; intros a Ha; left; lia|]. unfold mpd_ivs. rewrite EA1.
      destruct (md_own dX1) eqn:O; cbn; [split; [lia| exact I]| | exfalso; congruence].
      split; [lia|]. split; [| exact I]. ddestruct (BL1 eq_refl) as (_ & _ & _ & B4). lia. }
    pose proof INV2 as (HH2 & _). clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. unfold ck_frame in FR2.
    zstep. if_cases KB; zify_cond KB.
    - ddestruct RR2 as [[(-> & V2)|Er] _]; [| exfalso; subst r; cbv in KB; lia].
      eapply IH with (dX1 := dX2) (h1 := h2) (LB1 := LB2); [clear - MEAS V2 GE PV VX; lia| clear - V2 GE PV VX; lia| exact CTX| exact ST0| exact BASE| exact MA0| exact INV2| exact FR2| exact J2| exact TP].
    - zstep. zstep. eapply ck_mx_fin; [exact CTX| exact ST0| exact INV2| exact FR2| exact J2| exact TP| ddestruct RR2 as [[(Er & _)|Er] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia].
  all: match goal with |- ?gg => idtac "LOOPLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01C0@L10882941846.166L11801439651.220L11803324323.221L11803372194.178L11803566452.162L11803634930.145L11805421443.145L11805421443.162L11805421443.178L11870599278.219L12439250342.130L12439250342.187L13004851176.189L1386319127.213 L14477847844.182L15047278466.182L16075574008.157L21276529889.145L22286003249.187L22700267513.147L22700267513.180L23700427484.129L23700427484.164L246893736.220  L26056218006.185L26056220005.145L26058316316.127L26058334103.205L26983617546.187L2734107951.163 L2734108078.144 L28456398641.178L29784415085.138L30102489409.182L31826424927.182L31826851711.185L31826853356.9  L33827021232.214L34254556409.7  L35003997617.182L35626661391.173L36736477095.182L37247662168.182L3938951772.182 L43168283127.182L43189924142.7  L44483136750.178L49569627772.182L49587729867.184L49587729867.187L50076655012.182L51462948123.137L51467076497.138L51523620783.222L51523620783.223L51530095817.10 L51983135576.182L53133840792.138L53136082687.128L53313391509.182L59308585607.185L59308585607.188L59308630630.218L59576985857.138L60979967502.183L61274409944.220L61302938856.7  L61484463047.143L61970782849.143L63261865031.7  L63678966417.180L63680864802.143L63680898348.123L64076647740.173L64080807047.181L6443869639.7   L65684970158.219L65896456361.188L67165823973.7  L67197327768.187L68441890124.182L907814492.219  L9999373409.160 00000900B00K00T00]00b00g01001901B01T01f02I02J02_02h02i02n03>04H05T05_05o06806d07L08408`09909B09K09T09]09^0:30:H0:I0:R0:i0;C0;L0;X0;Y0;Z0;[0<10<=0<>0<\0=:0=G0=H0=I0=W0=e0>90>a0>h0?H0?I0@90@i0A50A>0AJ0AS0Aa0Aj0B30B@0BU0Bj0C=0Ci0DU0Db0E30EA0EN0FV0G\0Gi0H4S3spv1g1pS3spv1g1pS3spv1g1pS3spv1g1pS3spv1g1pS3spvS3spvS3spv1g1pS3spv1g1pS3spv1g1pS3spv1g1p2lo3GY01HS3spv1g1p2lo3GY01HS1L3HLS3spv1g1p2lo3SPB3SLO3ACL1d2B4FS3spv1G1g1p2lo3GY02GSS3spv1g1pFS3spvS3spv1Q1g1p1a2HaS1L3HLS4DIMG4IMGC3spv1G1Q1g2lo3GY03SPB2GS3MCG2QS3MCQ3MC23SLO3ACL3DHI3x131HS1L3HLS4DIMG4IMGC3spv1G1Q1g1p2lo3GY03SPB2GS3MCG2QS3MCQ3MC23SLO3ACL3DHI3x141HS1L3spv1p1HS3spv1g1p3SPB2KBS3spv1g1pS1L3HLS4DIMG4IMGC3spv1g1p2lo3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv2lo3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv1g1p2lo3SPB3MC23SLO3ACLS3spv1Q1g1p3SPB4QPOS1a2HaS3spv1g1pS3spv1g1pS3spv1g1pS3spv1g1pFS1L2HI3spv1h1g1p4HTOPS1L2HI3spv1h1g1p4HTOPFS3spv1g1pS1L3HLS3spv1Q2lo2QS3SLOS1L3HLS3spv1g1p2lo3SPB3SLOS3spv1g1pS3spv1g1p2loFFFS1L3HLS3spv2lo3SPB3SLOS3spv1g1p2loFS1L2HI3spv1h1g1p3SPB4HTOP1a2HaS1L2HI3spv1h1g1p3SPB4HTOP1a2HaS3spv1g1p3SPBFFS3spv1g1p1a2HaS3spv1g1p1a2HaS3spv1G2lo2GS1a2Ha1CS1L3HLS4DIMG4IMGC3spv1g1p2lo3MC23SLO3ACLS3spv1GS1L4DIMG4IMGC3spv2lo3SPB3MC23ACLFS1L3HLS4DIMG4IMGC3spv1g1p2lo3SPB3SLO3ACL1a2Ha2HdS1L3HLS4DIMG4IMGC3spv1g1p2lo3SPB3SLO3ACL1a2Ha2HdS3spv1g1p2KCS3spv1g1pS3spv1g1p2loS3spv1g1pS1L3spv2lo3SLOS3spv1g1pS3spv1g1pS3spv3SPB3SPAS3spv1Q1g1p2lo3GY02QSS3spv1Q1g1p2lo3GY02QSS3spv1Q1g2lo3GY02QSS1L3HLS4DIMG4IMGC3spv1g1p2lo3SPB3MC23SLO3ACLS1L3HLS4DIMG4IMGC3spv1g1p2lo3SPB3MC23SLO3ACLS3spv3SPB3SPAS3spv1g1p3dX23HN2S3spv1g1p1a2HaS3spv1Q2lo2QSS1L3HLS4DIMG4IMGC3spv1G1Q1g1p2lo3GY03SPB2GS3MCG2QS3MCQ3MC23SLO3ACL3DHI1HS1L3HLS4DIMG4IMGC3spv1G1Q1g1p2lo3GY03SPB2GS3MCG2QS3MCQ3MC23SLO3ACL3DHIS3spv1g1p3dX2S3spv1G1g1p". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HND HINIT HFREEM HCOPY HSUBM HADDI HCMP HCMPI HSIZE"] Lemma ck_mx : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "Prae,(2.&40.)Pspv,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0e,(2.&40.)Ps1e,(2.&40.)Ps2e,(2.&40.)Ps3e,(2.&40.)Ps4e,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pra0,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps2c,(2.&40.)Ps3c,(2.&40.)Ps4c,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.$52.VL,VHI,)PLB,(6.$7.)PG,$8.PQ,$8.Pg,$2;.Pp,$2<.Pcnt,(2.&40.)Pbp1,$2=.Pbp2,$2=.Plo,$8.Pm1,P,(2.&40.)(3.(2.&8.))Pj32,(6.(2.&8.))P,(5<.R<.R;.R:.R9.R8.R7.R6.R5.R4.(14.&40.R32.)R3.R>.R=.)P,(:.$8.(31.(34.(33.R9.)))=)P,(57.(1;.(1<.$8.$8.)(1=.$8.$8.R5.(14.&40.R34.))(1?.(1<.$8.$8.)))R10.R4.)P,(58.$52.R11.R5.)P,(12.$52.R6.)P,(13.$52.R7.R8.(1>.(14.&40.R37.)-50.))P,(23.$52.R8.(1>.(14.&40.R38.)-30.)(54.R31.R32.R33.R34.R35.R39.))P,(23.$52.R9.(1>.(14.&40.R39.)-50.)(1;.$24.(6>.#20.R8.)(1?.$24.)))P,(:.(2.&40.)R38.(>.&40.(47.VL,)))(49.$52.R16.(4:.$52.VL,VHI,VMT,R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R19.R18.R15.R14.R13.R11.R12.R10.+5<?:8.R<.R17.R16.)(<.(=.R2<.(>.&40.(1>.(14.&40.R3;.)-50.))R3:.R39.R2;.R2:.R29.(>.&40.R13.)(>.&40.R12.)R25.R24.R23.R22.R21.R20.R1?.R1>.R28.R27.R26.R33.R32.R31.R30.R2?.R2>.R2=.R1=.R1<.R1;.R1:.)R19.(>.&40.+3:280.)R18.(10.(2.&40.))R;.(11.$52.)))")
(* [comment removed for export] *).
  Proof.
    intros until j32. intros CTX GY0 MU WM MI1 ST1 FR LOC TP. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose CTX as (HH & GR & GKIND & GPS & GAS & GBS & PV & GCR & GS & MCG & PT & PF & PS & QCR & QS & MCQ & CNT & MC1 & MC2 & MCS & _ & _ & _ & _ & _ & _ & SLO & ACL & HTOP & SPA & DHI & MI & SOK & CA & _).
    pose proof SLO as SLO0. unfold ECP_CHECK_PUBKEY_STACK in SLO. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    dpose PT as (EX & EY & EZ & MX & MY & MZ).
    assert (PSG : forall d, In d (pt_mpds p) -> md_sg d = 1 \/ md_sg d = -1) by (intros d Hd; exact (proj1 (Forall_forall _ _) PS _ Hd)).
    assert (MDX : mpd_at usegs m LB (pt_X p)) by (split; [exact MX| apply PSG; cbn; auto]).
    dpose MX as (_ & _ & QPOS & _). rewrite EX in QPOS.
    assert (INX : md_own (pt_X p) = LHeap -> In (md_p (pt_X p), 4 * md_n (pt_X p)) LB) by (intros O; exact (proj1 (mpdr_blk_facts usegs L m LB _ MX O HBR))).
    assert (H12 : g_h g = 1 \/ g_h g = 2) by (destruct GKIND as [(E & _)|(E & _)]; [left| right]; exact E).
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    unfold ck_frame in FR.
    Ltac carry2 FR LOC MUc WMc := eapply rw_cells_transport in FR; [| exact MUc| exact WMc| cbn; lia]; eapply rw_cells_transport in LOC; [| exact MUc| exact WMc| cbn; lia].
    (* [comment removed for export] *)
    destruct (ck_now _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (pt_X p) CTX MU WM MI1 MDX ltac:(rewrite EX; lia)) as (MX1 & BLX & SLX).
    zstep. zstep.
    pose proof HSIZE as SZ. unfold mpi_size_stmt in SZ.
    eapply aevtM_cut_evt; [exact MK| eapply SZ with (LB := LB) (dX := pt_X p) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned spv + -80)) by lia;
      first [ exact MX1 | exact MI1 | exact ST1 | rewrite EX; reflexivity
            | intros O; pose proof (BLX O); lia
            | match goal with |- md_p _ + _ <= _ \/ _ => pose proof MDX as [(_ & _ & _ & _ & _ & HO) _]; destruct (md_own (pt_X p)) eqn:O;
                [destruct HO as [-> ->]; left; lia| pose proof (SLX ltac:(congruence)); lia| pose proof (SLX ltac:(congruence)); lia] end
            | rewrite EX; clear - QS SLO HLS; lia
            | clear - SPA SPB SLO HLS; lia
            | lia ] |].
    clear SZ. cbv beta. intros ms' PO. unfold mpi_size_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1a & -> & MUa & WMa & MIa & STa).
    rewrite ?(unsigned_lit (bv_unsigned spv + -80)) in MUa, STa by lia.
    replace (ret_pc (Z_to_bv 64 0x3a288)) with (Z_to_bv 64 0x3a288) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    carry2 FR LOC MUa WMa.
    assert (MU' : munch [(lo, bv_unsigned spv)] m m1a) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUa]; unfold sub_fp; cbn; intros; lia]).
    pose proof (wmono_trans _ _ _ _ WM WMa) as WM'. clear MU WM MUa WMa MI1 ST1 MX1. rename MU' into MU. rename WM' into WM.
    (* [comment removed for export] *)
    destruct (ck_now_env _ _ _ _ _ _ _ _ _ _ _ _ _ m1a CTX MU WM MIa) as (GRa & _ & _ & _).
    dpose GRa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTa & GRNG & _). unfold grp_tail_cells in HTa.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_cases KA; zify_cond KA.
    { (* [comment removed for export] *)
      eapply ck_exit_prefix; [exact CTX| exact MU| exact WM| exact MIa| exact STa| exact FR| exact LOC| reflexivity| lia]. }
    clear HTa.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    eapply ck_pre_cmpint with (z := 0); [exact CTX| exact MU| exact WM| exact MIa| exact STa| exact MDX| rewrite EX; lia| lia| lia| reflexivity| rewrite EX; reflexivity| reflexivity|].
    clear MU WM. intros m1b ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU WM MIb STb MUc WMc. carry2 FR LOC MUc WMc.
    zstep. zstep. zstep. if_cases KB; zify_cond KB.
    { eapply ck_exit_prefix; [exact CTX| exact MU| exact WM| exact MIb| exact STb| exact FR| exact LOC| reflexivity| lia]. }
    assert (VX0 : 0 <= mpd_val (pt_X p)) by (pose proof (Z.sgn_spec (mpd_val (pt_X p) - 0)); lia). clear KB.
    (* [comment removed for export] *)
    destruct (ck_now_env _ _ _ _ _ _ _ _ _ _ _ _ _ m1b CTX MU WM MIb) as (GRb & _ & _ & _).
    pose proof GRb as (HDb & _). unfold grp_head_cells in HDb.
    zstep.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB usegs m1b _ [] 32 j32 [] [16;16]%nat LOC eq_refl) as LOC2. cbn [mk_CB_cells app] in LOC2. clear LOC.
    pose proof (proj1 (rw_cells_app usegs _ _ [CB 16 _] _) LOC2) as [CR0 CX0]. clear LOC2. cbn [cells_size csize Nat.add] in CX0.
    replace (bv_unsigned spv + -80 + Z.of_nat 16) with (bv_unsigned spv + -64) in CX0 by lia.
    set (jr := firstn 16 j32) in CR0. clearbody jr. set (jx := firstn 16 _) in CX0. clearbody jx.
    apply mpi_cells_of_bytes in CX0.
    set (px0 := bv_unsigned (wof (firstn 8 jx))) in CX0. set (sx0 := wof (firstn 2 (skipn 8 jx))) in CX0. set (nx0 := bv_unsigned (wof _)) in CX0. set (padX := wof (skipn 12 jx)) in CX0.
    clearbody px0 sx0 nx0 padX.
    zstep. zstep.
    pose proof HINIT as SI. unfold mpi_init_stmt in SI.
    eapply aevtM_cut_evt; [exact MK| eapply SI with (X := bv_unsigned spv + -64); [exact CX0| clear - SPA SPB SLO HLS; lia| lia| exact MIb| reflexivity] |].
    clear SI. cbv beta. intros ms' PO. unfold mpi_init_post in PO. ddestruct PO as (? & m0 & -> & MUa & WMa & MI0 & CX1).
    replace (ret_pc (Z_to_bv 64 0x3a2cc)) with (Z_to_bv 64 0x3a2cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rw_cells_transport in FR; [| exact MUa| exact WMa| cbn; lia]. eapply rw_cells_transport in CR0; [| exact MUa| exact WMa| cbn; lia].
    eapply (stk_transport_disjoint usegs) in STb; [| exact MUa| exact WMa| cbn; lia].
    assert (MU' : munch [(lo, bv_unsigned spv)] m m0) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUa]; unfold sub_fp; cbn; intros; lia]).
    pose proof (wmono_trans _ _ _ _ WM WMa) as WM'. clear MU WM MUa WMa MIb HDb CX0. rename MU' into MU. rename WM' into WM.
    (* [comment removed for export] *)
    assert (ST0 : ck_st h LB (bv_unsigned spv) lo m mo h LB m0 mo).
    { eapply ck_st_prefix; [exact CTX| exact MU| exact WM| exact MI0| replace (bv_unsigned spv - 80) with (bv_unsigned spv + -80) by lia; exact STb]. }
    dpose ST0 as (HH0 & _ & _ & SOK0 & _ & _ & _ & [c0 CNT0] & ST0').
    pose proof (ck_st_grp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ST0) as GR0.
    destruct (ck_now _ _ _ _ _ _ _ _ _ _ _ _ _ m0 (pt_X p) CTX MU WM MI0 MDX ltac:(rewrite EX; lia)) as (MEX0 & _ & _).
    assert (MA0 : mpd_at usegs m0 LB (mpd_init (bv_unsigned spv + -64) padX)).
    { split; [apply mpdr_at_init; [exact CX1| clear - SPA SPB SLO HLS; lia| lia]| left; reflexivity]. }
    assert (BASE : mm_base L LB (mpd_init (bv_unsigned spv + -64) padX) G U_MUL_COUNT (bv_unsigned spv + -80) 0 lo (heap_top usegs L HI h) g).
    { unfold mm_base. cbn [md_addr md_own md_p md_n mpd_init mpd_blk]. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      - unfold mpd_writable. cbn [md_addr md_own md_p md_n mpd_init]. split; [intros a Ha; left; lia|]. split; [intros a Ha Hd; exfalso; lia| intros; discriminate].
      - discriminate.
      - intros b [].
      - intros a Ha. destruct (GCR a Ha) as [C|[C|C]]; [left; clear - C GS Ha SLO HLS; lia| right; left; exact C| right; right; exact C].
      - intros; discriminate.
      - intros d Hd O. ddestruct (mpdr_blk_facts usegs L m LB d (grp_mpds_at m LB G g d GR Hd) O HBR) as (IN & N1 & P0 & B4 & _).
        split; [exact IN|]. split; [intros []| cbn [md_addr mpd_init]; lia]. }
    assert (INV0 : mm_inv usegs L HI MT h LB (mpd_init (bv_unsigned spv + -64) padX) G g U_MUL_COUNT (bv_unsigned spv + -80) 0 lo m0 mo h LB (mpd_init (bv_unsigned spv + -64) padX) m0 mo).
    { eapply (sr_inv0 L HI DIMG IMGC MT); [exact BASE| exact MA0| exact HH0| exact GR0| exact CNT0| exact SOK0| exact MI0| exact MI0| apply munch_refl| apply wmono_refl| rewrite Z.sub_0_r; exact ST0'| cbn; intros NN; exfalso; exact (NN eq_refl)| cbn; lia]. }
    clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof HCOPY as SCP. unfold mpi_copy_stmt in SCP.
    eapply aevtM_cut.
    { eapply SCP with (lo := lo) (h := h) (LB := LB) (dX := mpd_init (bv_unsigned spv + -64) padX) (dY := pt_X p);
        rewrite ?(unsigned_lit (bv_unsigned spv + -80)) by lia; cbn [md_addr md_own md_p md_n mpd_init];
        first [ exact HH0 | exact MA0 | exact MEX0 | exact TP | exact SOK0 | exact CA | exact MI0 | exact ST0' | exact ACL | exact DHI
              | reflexivity | rewrite EX; reflexivity
              | discriminate
              | match goal with |- mpd_sep _ _ => unfold mpd_sep; cbn [md_addr mpd_init]; right; rewrite EX; clear - QS SLO HLS; lia end
              | match goal with |- copy_sep _ _ _ _ => unfold copy_sep; cbn [md_addr md_own md_p md_n mpd_init]; rewrite EX;
                  split; [intros NN; pose proof (SLX NN); lia|]; split; [intros; discriminate|]; split; [right; left; discriminate|];
                  split; [clear - QS SLO HLS; lia|]; split; [intros NN; pose proof (SLX NN); lia| intros a Ha; lia] end
              | match goal with |- mpd_writable _ _ _ _ _ => unfold mpd_writable; cbn [md_addr md_own md_p md_n mpd_init];
                  split; [intros a Ha; left; lia|]; split; [intros a Ha Hd; exfalso; lia| intros; discriminate] end
              | match goal with |- client_range _ _ _ _ 16 => rewrite EX; intros a Ha; apply QCR; lia end
              | match goal with |- _ = LHeap -> client_range _ _ _ _ _ => intros O a Ha; right; right; exists (md_p (pt_X p), 4 * md_n (pt_X p)); split; [exact (INX O)| cbn; lia] end
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SCP. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    ddestruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & mo2 & h2 & LB2 & dX2 & r2 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned spv + -80)) in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MA2 & OUT2 & PX2 & SOK2 & RR2).
    replace (ret_pc (Z_to_bv 64 0x3a2d8)) with (Z_to_bv 64 0x3a2d8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    dpose RR2 as (RV2 & EA2 & PAD2 & FRB2). cbn [md_addr mpd_init] in EA2.
    assert (NLE2 : md_n (mpd_init (bv_unsigned spv + -64) padX) <= md_n dX2) by (pose proof MA2 as [(_ & _ & _ & _ & HN2 & _) _]; cbn; lia).
    assert (INV2 : mm_inv usegs L HI MT h LB (mpd_init (bv_unsigned spv + -64) padX) G g U_MUL_COUNT (bv_unsigned spv + -80) 0 lo m0 mo h2 LB2 dX2 m2 mo2).
    { eapply (mm_inv_binop usegs L HI DIMG); [exact BASE| exact MA0| exact INV0| exact HH2| exact MA2| exact OUT2| exact FRB2| exact PAD2| exact NLE2| rewrite Z.sub_0_r; exact PX2| exact SOK2| exact MI2| exact MF2| exact HT2| rewrite Z.sub_0_r; replace (bv_unsigned spv + -80) with (bv_unsigned spv - 80) by lia; exact ST2]. }
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 FR ltac:(cbn; intros a Ha; left; lia) ltac:(cbn; lia)) as FR2.
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 CR0 ltac:(cbn; intros a Ha; left; lia) ltac:(cbn; lia)) as J2.
    clear MK FR CR0 CX1. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    zstep. if_cases KC; zify_cond KC.
    { (* [comment removed for export] *) zstep. eapply ck_mx_fin; [exact CTX| exact ST0| exact INV2| exact FR2| exact J2| exact TP| destruct RV2 as [(Er & _)|(Er & _)]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia]. }
    destruct RV2 as [(-> & V2 & _)|(Er & _)]; [| exfalso; subst r2; cbv in KC; lia].
    zstep.
    eapply (ck_mx_loop (S (Z.to_nat (mpd_val dX2)))) with (dX1 := dX2) (h1 := h2) (LB1 := LB2); [lia| rewrite V2; exact VX0| exact CTX| exact ST0| exact BASE| exact MA0| exact INV2| exact FR2| exact J2| exact TP].
  all: match goal with |- ?gg => idtac "MXLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0130@L11007094131.153L11150815760.132L11803566452.151L11803566452.180L11803566452.198L11805421443.151L11805421443.180L11805421443.198L12860309875.152L13942840817.179L13954520054.211L15302269400.106L16075583823.173L16075583950.191L16075584073.152L16075584200.153L16075584458.144L19427582228.109L19427582228.110L19841421879.179L23663373947.197L23668302077.211L24893396178.132L25214214772.106L25345670230.132L2721634456.225 L2721634463.211 L2734101533.150 L2734102041.197 L2734102168.179 L31225147636.106L32860062831.132L34067802422.197L34229602291.197L34229617780.161L34705680216.106L37246946676.105L3949578456.105 L40374333670.109L43059266230.107L43779939422.103L44622288685.113L44622288685.114L47996134065.161L49698585326.113L49698585326.114L51454941784.106L52772328862.158L5285469359.113 L5285469359.114 L54578955976.179L54591424719.211L55310518004.106L55526851756.156L58591023192.106L58592928065.131L59962443696.211L61321319284.106L61484452081.179L61484469239.161L64314031110.132L67280348888.106L67351568884.106L67503306555.160L67507420833.160L67541566890.107L67541566890.10800000800<00@00F00L00P00V00\00d00l01401801901:01;01<01=02203303903I03Y03]03a03g03m04304704=04C04G04S04Y04i05905=05A05E05I05^05f06[07\07b08<08b08f08n09D09f0:60:F0:J0:R0:V0:Z0:`0:d0:j0;00;40;80;<0;F0;R0;j0<BS2sp1G1pS2spS2spS2sp1pS2sp1pS2spS2sp1pS2sp1pS2sp1G1pS2sp1Q1pS2sp1Q1pS2spFFFFFS1L3HLS4DIMG4IMGC2ra2sp2lo3MC23SLO3ACL2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2sp2s02lo3MC23SLO3ACL2HB5Ha_st5Hl_st2s12s22s32s4S2sp1pS2sp1G1g1p2lo2GSS2sp1G1g1p2lo2GSS2spS2spS2sp1QS2sp1pS2sp1pS2spS2sp1pS2sp1pS2spS2sp1Q2lo2QSS2sp1pS2sp1Q1g1p2lo2QSS2sp1Q1g1p2lo2QSS2spS2spS2spS2spS1L3HLS2sp2lo3SLO3SPBS2sp3SPBS1L3HLS4DIMG4IMGC2ra2sp2lo3SLO3ACL3SPB2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2sp2s02lo3SLO3ACL3SPB2HB5Ha_st5Hl_st2s12s22s32s4S2sp1pS2ra2sp3SPB2HB5Ha_st5Hl_stS2sp2s03SPB2HB5Ha_st5Hl_st2s12s22s32s4S2spS2sp1g1pS2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_st2s12s22s32s4S2sp1Q1g1p2lo2QSS2sp1Q1g1p2lo2QSS2spS2sp1G1pS2spS2spS2sp1pS2spS2sp1pS2sp1pS2spS2spS2spS2sp1g1p1HS2sp1g1p3GYRS1L3HLS2sp2lo3SLO3SPB2HBS1L3HLS2sp2lo3SLO3SPB2HB". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HND HMM HSR HINIT HFREEM HCOPY HSUBM HADDI HCMP HCMPI HSIZE"] Theorem U_ecp_check_pubkey_spec : ltac2:(CDefT.buildp (gd_tbl_P_ecp_check_pubkey ()) "(78.$52.VL,VHI,VMT,$79.$5;.+5<?:8.$59.$5:.)")
(* [comment removed for export] *).
  Proof.
    unfold ecp_check_pubkey_stmt, U_ECP_CHECK_PUBKEY. intros until lo.
    intros HH GR GKIND GPS GAS GBS PV GCR GS MCG PT PF PS QCR QS MCQ CNT MC1 MC2 MCS BP1 BP2 BPL BPH BPS MCB ST SLO ACL HTOP SPA0 DHI TP MI SOK CA -> ->.
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    pose proof SLO as SLO0. unfold ECP_CHECK_PUBKEY_STACK in SLO.
    assert (CTX : ck_ctx h LB G Q g p cnt bp1 bp2 (bv_unsigned sp) lo m mo).
    { unfold ck_ctx. repeat match goal with |- _ /\ _ => split end; try assumption; try lia. }
    (* [comment removed for export] *)
    pose proof (lock MI) as MI00. pose proof (lock HH) as HH00.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM. clear HH.
    carve_frame 80%nat ST. set (JJ := junk) in FR. clearbody JJ.
    pose proof PT as (EQ0 & _ & _ & MQ0 & _). pose proof MQ0 as (QCH & QAL & QPOS & _). rewrite EQ0 in QCH, QAL, QPOS.
    unfold mpi_cells in QCH. pose proof (rw_cells_bound _ _ _ _ QCH) as QB. cbn [cells_size csize Nat.add] in QB. clear QCH MQ0.
    pose proof GR as (GHD0 & GAL0 & GPOS0 & _). pose proof (rw_cells_bound _ _ _ _ GHD0) as GB0. unfold grp_head_cells in GB0. cbn [cells_size csize Nat.add] in GB0. clear GHD0.
    do 7 zstep. zstep. if_cases KQ0; zify_cond KQ0; [exfalso; rewrite ?unsigned_lit in KQ0 by lia; lia|].
    zstep. zstep. zstep. zstep. if_cases KQ1; zify_cond KQ1; [exfalso; rewrite ?unsigned_lit in KQ1 by lia; rewrite ?land_7_mod in KQ1; lia|].
    zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    dpose PT as (EX & EY & EZ & MX & MY & MZ).
    assert (PSG : forall d, In d (pt_mpds p) -> md_sg d = 1 \/ md_sg d = -1) by (intros d Hd; exact (proj1 (Forall_forall _ _) PS _ Hd)).
    assert (MDX : mpd_at usegs m LB (pt_X p)) by (split; [exact MX| apply PSG; cbn; auto]).
    assert (MDY : mpd_at usegs m LB (pt_Y p)) by (split; [exact MY| apply PSG; cbn; auto]).
    assert (MDZ : mpd_at usegs m LB (pt_Z p)) by (split; [exact MZ| apply PSG; cbn; auto]).
    dpose GR as (_ & _ & _ & EP & _ & _ & _ & MP & _ & _ & (EGX & EGY & EGZ & MGX & MGY & MGZ) & _).
    assert (MDP : mpd_at usegs m LB (g_P g)) by (split; [exact MP| left; exact GPS]).
    pose proof (proj1 (rw_cells_app usegs _ _ [CB 32 _] _) FR) as [LOC FR']. clear FR. cbn [cells_size csize Nat.add] in FR'.
    match type of FR' with rw_cells _ _ ?aa _ => replace aa with (bv_unsigned sp + -48) in FR' by lia end.
    change (rw_cells usegs m1 (bv_unsigned sp + -48) (ck_frame s4 s3 s2 s1 s0 ra)) in FR'. rename FR' into FR.
    set (j32 := firstn 32 _) in LOC. clearbody j32.
    Ltac carry FR LOC MUc WMc := eapply rw_cells_transport in FR; [| exact MUc| exact WMc| cbn; lia]; eapply rw_cells_transport in LOC; [| exact MUc| exact WMc| cbn; lia]; clear MUc WMc.
    zstep.
    eapply ck_pre_cmpint with (z := 1); [exact CTX| exact MU| exact WM| assumption| replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; assumption| exact MDZ| rewrite EZ; lia| lia| lia| reflexivity| rewrite EZ; apply f_equal; lia| reflexivity|].
    clear MU WM. intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU WM MI2 ST2 MUc WMc. carry FR LOC MUc WMc.
    zstep. if_cases K0; zify_cond K0.
    2:{ (* [comment removed for export] *) zstep. zstep. eapply ck_exit_prefix; [exact CTX| exact MU| exact WM| exact MI2| exact ST2| exact FR| exact LOC| reflexivity| lia]. }
    (* [comment removed for export] *)
    destruct (ck_now_env _ _ _ _ _ _ _ _ _ _ _ _ _ m2 CTX MU WM MI2) as (GR2 & _ & _ & HH2).
    dpose GR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & MGX2 & MGY2 & _) & _).
    pose proof MGX2 as (CHGX & _). rewrite EGX in CHGX. unfold mpi_cells in CHGX.
    pose proof MGY2 as (CHGY & _). rewrite EGY in CHGY. unfold mpi_cells in CHGY. replace (G + 56 + 16) with (G + 72) in CHGY by lia.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    zstep. if_cases KG0; zify_cond KG0; [exfalso; rewrite ?unsigned_lit in KG0 by lia; lia|].
    zstep. zstep. if_cases KG1; zify_cond KG1; [exfalso; rewrite ?unsigned_lit in KG1 by lia; rewrite ?land_7_mod in KG1; lia|].
    zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *) zstep. zstep. zstep. eapply ck_exit_prefix; [exact CTX| exact MU| exact WM| exact MI2| exact ST2| exact FR| exact LOC| reflexivity| lia]. }
    zstep. zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *) eapply ck_mx; [exact CTX| | exact MU| exact WM| exact MI2| exact ST2| exact FR| exact LOC| exact TP].
      pose proof (mpdr_p_range _ _ _ _ MGY2). rewrite ?Z.mod_small in K2 by lia. exact K2. }
    pose proof (mpdr_p_range _ _ _ _ MGY2) as GYR. rewrite ?Z.mod_small in K2 by lia.
    assert (H1 : g_h g = 1) by (destruct GKIND as [(H1 & _)|(_ & GY0)]; [exact H1| exfalso; exact (K2 GY0)]).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply ck_pre_cmpint with (z := 0); [exact CTX| exact MU| exact WM| exact MI2| exact ST2| exact MDX| rewrite EX; lia| lia| lia| reflexivity| rewrite EX; reflexivity| reflexivity|].
    clear MU WM. intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU WM MI3 ST3 MUc WMc. carry FR LOC MUc WMc.
    zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3.
    { eapply ck_exit_prefix; [exact CTX| exact MU| exact WM| exact MI3| exact ST3| exact FR| exact LOC| reflexivity| lia]. }
    zstep. zstep. zstep. zstep. zstep.
    eapply ck_pre_cmpint with (z := 0); [exact CTX| exact MU| exact WM| exact MI3| exact ST3| exact MDY| rewrite EY; lia| lia| lia| reflexivity| rewrite EY; apply f_equal; lia| reflexivity|].
    clear MU WM. intros m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU WM MI4 ST4 MUc WMc. carry FR LOC MUc WMc.
    zstep. zstep. zstep. if_cases K4; zify_cond K4.
    { eapply ck_exit_prefix; [exact CTX| exact MU| exact WM| exact MI4| exact ST4| exact FR| exact LOC| reflexivity| lia]. }
    zstep. zstep. zstep. zstep.
    eapply ck_pre_cmp; [exact CTX| exact MU| exact WM| exact MI4| exact MDX| rewrite EX; lia| exact MDP| rewrite EP; lia| lia| reflexivity| rewrite EX; reflexivity| rewrite EP; reflexivity|].
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
    zstep. zstep. zstep. zstep. if_cases K5; clear K5.
    { eapply ck_exit_prefix; [exact CTX| exact MU| exact WM| exact MI4| exact ST4| exact FR| exact LOC| reflexivity| lia]. }
    zstep. zstep. zstep. zstep.
    eapply ck_pre_cmp; [exact CTX| exact MU| exact WM| exact MI4| exact MDY| rewrite EY; lia| exact MDP| rewrite EP; lia| lia| reflexivity| rewrite EY; apply f_equal; lia| rewrite EP; reflexivity|].
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
    zstep. zstep. zstep. if_cases K6; clear K6.
    { eapply ck_exit_prefix; [exact CTX| exact MU| exact WM| exact MI4| exact ST4| exact FR| exact LOC| reflexivity| lia]. }
    eapply ck_sw; [exact CTX| exact H1| exact MU| exact WM| exact MI4| exact ST4| exact FR| exact LOC| exact TP].
  all: match goal with |- ?g => idtac "MAINLEFT" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CK.
