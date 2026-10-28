(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts CrtFacts RepEcp EcpFacts EcpLoad. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney EcpJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_cmp U_mpi_bitlen U_mpi_init U_mpi_shift_r U_mpi_divmod_stmt U_mpi_exp_mod_stmt U_ecp_red U_ecp_mul_mod U_ecp_sw_rhs.
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
Ltac2 gd_tbl_P_ecp_derive_y () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_h"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_A"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_B"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.ext_opnd"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.ecp_mul_mod_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_free.mpi_free_X"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "ECP_DERIVE_Y_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.USpec.EcpJourney.jst"; "DY.dy_XO"; "RocqVerifyHarness.AgentSubmission.USpec.EcpJourney.jtmp"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "DY.dy_ctx"; "DY.dy_state"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "DY.dy_regs"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"].


Definition ECP_DERIVE_Y_STACK : Z := 800.   (* [comment removed for export] *)
Definition ECP_FEATURE_UNAVAILABLE : Z := -0x4E80.

Definition ecp_derive_y_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ENTRY MSF MC STACK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.O8.O7.O6.)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)Plo,$8.P,(:.O8.O7.O6.R8.R7.R:.R9.)P,(;.O8.O5.R;.R8.R5.R4.)P,(<.$8.(=.R5.)+1.)P,(<.$8.(>.(?.R6.))+1.)P,(<.$8.(>.(10.R7.))+1.)P,(<.$8.(>.(11.R8.))+1.)P,(12.+1.(13.(?.R9.)))P,(12.(14.(?.R:.))+1387.)P,(15.O7.R?.R9.R<.+<0.)P,(16.(12.(17.R=.+<0.)R:.)(12.(18.&40.R33.)R=.))P,(16.(12.(17.(19.R10.)+10.)R>.)(12.(17.R>.+<0.)(19.R10.)))P,(1:.O8.R15.R12.R11.)P,(<.$1;.(1<.R12.)$1=.)P,(1>.O7.R14.(18.&40.R37.)(1?.O8.O7.O6.R15.)R13.)P,(1:.O8.R18.R15.R13.)P,(20.O7.R16.R15.R14.O2.(18.&40.R39.)R10.)P,(21.O8.R1:.O2.(22.$23.(24.R12.)(25.$23.)))P,(12.(26.O7.)O2.)P,(12.(17.O2.+8.)(27.O7.))P,Pa,$8.P,(28.(12.O2.R1.)(29.R1.(17.O2.+8.)))(28.(2:.(2;.O7.R2.))(2<.O7.R2.))P,(16.(12.(17.O2.+8.)(19.R1:.))(12.(17.(19.R1:.)+10.)O2.))P,(16.(12.(17.O2.+8.)R19.)(12.(17.R19.+<0.)O2.))P,(2=.O8.R20.R17.(18.&40.R40.))P,(12.R18.(2>.(2>.(18.&40.R41.)O1.)(2?.O7.)))P,(12.(30.O7.)R19.)P,(12.(18.&40.R43.)(1?.O8.O7.O6.R21.))P,(<.$8.(31.(18.&40.R44.)+10.)=)P,(12.(27.O7.)(30.O7.))P,(<.(0.&40.)R44.(32.&40.(33.O7.)))P,(34.O8.R27.)P,(35.O8.O7.R28.)P,(36.O7.O3.+8.)P,(<.(0.&40.)R42.(32.&40.R24.))P,(<.(0.&40.)R42.(32.&40.(19.R26.)))P,(<.(0.&40.)R42.(32.&40.(19.R28.)))(37.O8.R2<.(38.O8.O7.O6.O5.R4>.R4=.R4<.R4;.R47.R46.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R2?.R2>.R2;.R2:.R29.R27.R26.O2.R24.R2=.R2<.)(39.(3:.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.)R2?.(32.&40.O4.)R2>.(3;.(0.&40.))R2=.(3<.O8.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L47380863409.5000009S1d1A1n1H". (* [comment removed for export] *)
Lemma free_X_disjoint : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Pd,$7.PA,$8.Pn,$8.P,P,(<.$1;.(1<.R3.)$3=.)(16.(12.(17.(3>.R4.)(3?.+4.(14.R4.)))R3.)(12.(17.R3.R2.)(3>.R4.)))(40.(41.(1<.R4.)(3>.R4.)(14.R4.))R3.R2.)")
(* [comment removed for export] *).
Proof. intros d A n D. unfold mpi_free_X. destruct (md_own d); cbn; [exact I| | exact I]. split; [| exact I]. pose proof (D eq_refl). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition U_ECP_DERIVE_Y : Z := 0x389dc.
Notation U_MUL_COUNT := 380840 (only parsing).

Section DY.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Variable MT : list modp_ent.
  Hypothesis HSR : ecp_sw_rhs_stmt usegs L HI MT 0x3a7a4 U_MEMSET_FUNC U_MUL_COUNT ECP_SW_RHS_STACK.
  Hypothesis HGETBIT : mpi_get_bit_stmt usegs 0x1f8f4.
  Hypothesis HINIT : mpi_init_stmt usegs 0x1f488.
  Hypothesis HFREEM : mpi_free_stmt usegs L HI 0x1f4a8 U_MEMSET_FUNC.
  Hypothesis HADDI : mpi_add_int_stmt usegs L HI 0x1fd60 U_MEMSET_FUNC.
  Hypothesis HSHR : mpi_shift_r_stmt usegs 0x2010c.
  Hypothesis HEXP : mpi_exp_mod_stmt_n usegs L HI 0x21708 U_MEMSET_FUNC.
  Hypothesis HSUBM : mpi_sub_mpi_stmt usegs L HI 0x20b04 U_MEMSET_FUNC.

  Definition dy_regs (s6e s5e s4e s3e s2e s1e s0e rae : word) : list cell := [C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae].
  Definition dy_XO (dX : mpd) : list ivl := [(md_addr dX, md_addr dX + 16); (U_MUL_COUNT, U_MUL_COUNT + 8)].

  (* [comment removed for export] *)
  Definition dy_ctx (h : HST usegs L HI) (LB : list blk) (dX dA : mpd) (G : Z) (g : ecp_grp) (cnt : word) (SP lo : Z) (m : mem) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "(28.(:.$42.VL,VHI,O;.O:.O2.O1.)(28.(;.$42.VMT,O2.O:.O7.O6.)(28.(<.$8.(=.O6.)+1.)(28.(<.$8.(>.(?.O6.))+1.)(28.(<.$8.(>.(10.O6.))+1.)(28.(<.$8.(>.(11.O6.))+1.)(28.(12.+1.(13.(?.O6.)))(28.(15.VL,O:.O3.O7.+<0.)(28.(16.(12.(17.O7.+<0.)O3.)(12.O4.O7.))(28.(16.(12.(17.(19.O9.)+10.)O7.)(12.(17.O7.+<0.)(19.O9.)))(28.(1:.$42.O2.O:.O9.)(28.(<.$1;.(1<.O9.)$1=.)(28.(1>.VL,O:.O4.(1?.$42.VL,VHI,O;.)O9.)(28.(16.(12.(17.(19.O9.)+10.)O3.)(12.O4.(19.O9.)))(28.(1:.$42.O2.O:.O8.)(28.(20.VL,O:.O9.O8.+5<?:8.O4.O3.)(28.(21.$42.O2.+5<?:8.(22.$23.(24.O5.)(25.$23.)))(28.(12.(26.VL,)+5<?:8.)(28.(12.(17.+5<?:8.+8.)(27.VL,))(28.Pa,$8.P,(28.(12.+5<?:8.R1.)(29.R1.(17.+5<?:8.+8.)))(28.(2:.(2;.VL,R2.))(2<.VL,R2.))(28.(16.(12.(17.+5<?:8.+8.)(19.O9.))(12.(17.(19.O9.)+10.)+5<?:8.))(28.(16.(12.(17.+5<?:8.+8.)O7.)(12.(17.O7.+<0.)+5<?:8.))(28.(12.O3.(2>.(2>.O4.$43.)(2?.VL,)))(28.(12.(30.VL,)O3.)(28.(12.O4.(1?.$42.VL,VHI,O;.))(28.(<.$8.(31.O4.+10.)=)(28.(12.(27.VL,)(30.VL,))(28.(34.$42.O2.)(28.(35.$42.VL,O2.)(28.(36.VL,$44.+8.)(29.O4.(45.+2.+40.))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition dy_state (h : HST usegs L HI) (LB : list blk) (dX : mpd) (G : Z) (g : ecp_grp) (SP lo : Z) (m : mem) (mo : Model)
      (hk : HST usegs L HI) (LBk : list blk) (dYk dEk : mpd) (mk : mem) (mok : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "(28.(46.$42.VL,VHI,O?.O>.O:.+50.(47.O=.)+5<?:8.O9.O8.O7.O6.O5.O2.O1.)(28.(48.$42.O>.O5.O2.(19.O=.)O4.)(28.(<.(0.&40.)(49.O4.)(49.O=.))(28.(48.$42.O>.O5.O2.(2>.O:.+50.)O3.)(28.Pb,$6.P,(4:.$6.R1.O5.)(16.(4:.$6.R2.O>.)(16.(4:.$6.R2.(4;.O4.))(4:.$6.R2.(4;.O3.))))P,(<.$1;.(1<.O4.)$3=.)P,(<.$1;.(1<.O3.)$3=.)(2:.(<.(4<.$8.$8.)(4=.$8.$8.(3>.O4.)(3?.+4.(14.O4.)))(4=.$8.$8.(3>.O3.)(3?.+4.(14.O3.))))))))))")
(* [comment removed for export] *).

  Ltac dyctx CTX := pose proof CTX as (HH & GR & H1 & GPS & GAS & GBS & PV & GCR & GS & GX & MX0 & YNULL & XW & SXS & MXA & EXT & CNT & MC1 & MC2 & MCS & MCX & MCG & SLO & ACL & HTOP & SPA & DHI & MI & SOK & CA & SPU).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L22031843797.26000008S1G1a2Ha". (* [comment removed for export] *)
  Lemma grp_relist : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Pm,P,(0.&40.)(2.(0.&8.))PLB,(5.$6.)PLB',(5.$6.)PG,$8.Pg,$9.P,(;.$42.VMT,R5.R4.R2.R1.)P,(<.$8.(=.R2.)+1.)P,(34.$42.R7.)(;.$42.VMT,R8.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros m LB LB' G g HG H1 MI. eapply (ecp_group_at_presx usegs L) with (X := []) (SP := G); [exact HG| apply heap_presx_refl| exact MI| exact MI| intros a Ha; left; lia| cbn; exact I|].
    intros d Hd O. exfalso. exact (grp_static_own usegs MT m LB G g d HG H1 Hd O).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L34519171005.4 L37273016624.1000000=00PS2dX1G2GX3MCGS1G2SP2lo2GS1a2Ha1C". (* [comment removed for export] *)
  Lemma dy_GR : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)PSP,$8.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Phk,(4.$42.VL,VHI,)PLBk,(5.$6.)PdYk,$7.PdEk,$7.Pmk,P,(0.&40.)(2.(0.&8.))Pmok,$3.P,(4>.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(4?.R12.R11.R10.R>.R=.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(;.$42.VMT,R4.R7.R?.R>.)")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX (STk & _). dyctx CTX. unfold ECP_DERIVE_Y_STACK in SLO. flat constr:(STk) 6%nat. intros HHk SUBk PXk SOKk MIk _.
    eapply (ecp_group_at_presx usegs L); [exact GR| exact PXk| exact MI| exact MIk| | unfold dy_XO; cbn; clear - GX MCG; lia|].
    - intros a Ha. destruct (GCR a Ha) as [C|[C|(b & Hb & R)]]; [left; clear - C GS Ha SLO HLS; lia| right; left; exact C| right; right; exists b; split; [exact Hb| exact R]].
    - intros d Hd O. exfalso. exact (grp_static_own usegs MT m LB G g d GR H1 Hd O).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L30615961706.89L44187194279.90L48736977073.88L48815712669.93L51163419001.88L59308546259.82L59308546259.84L8929561634.89 00000\00k01X01i02U02^02i03cS1L3HLS4DIMG4IMGC1g2SP2lo3MC23SLO3ACL2N13PB1S1L1g2SP3PB12R1S1L3HLS1g2SP2lo3MC23SLO3ACL3DHI3PHL2N12P03PB1S1G1g2SP3PB11a2HaS1L3HLS4DIMG4IMGC1g2SP2lo3MC23SLO3ACL2N13PB1S1g2SP2PVS2SP1b1l2N0S1L3HLS4DIMG4IMGC1g2SP2lo3MC23SLO3ACL3PHL3PHN2N12P03PB12R0". (* [comment removed for export] *)
  Lemma dy_P_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)PSP,$8.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Phk,(4.$42.VL,VHI,)PLBk,(5.$6.)PdYk,$7.PdEk,$7.Pmk,P,(0.&40.)(2.(0.&8.))Pmok,$3.P,(4>.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(4?.R12.R11.R10.R>.R=.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(28.(1:.$42.R4.R7.(?.R>.))(28.(<.$8.(19.(?.R>.))(17.R?.+8.))(28.(<.$1;.(1<.(?.R>.))$50.)(28.(12.+1.(14.(?.R>.)))(28.(29.=(3>.(?.R>.)))(28.Pi,$8.P,(28.(12.=R1.)(29.R1.(3?.+4.(14.(?.R?.)))))(<.$51.(52.$42.(53.(17.(3>.(?.R10.))R2.)))$54.)(28.(12.(55.VL,)(3>.(?.R>.)))(28.(12.(17.(3>.(?.R>.))(3?.+4.(14.(?.R>.))))(56.VL,))(15.VL,R7.R;.(19.(?.R>.))+10.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX STATE. pose proof (dy_GR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE) as GRk.
    flat constr:(STATE) 6%nat. intros STk TYk PADk TEk COVk DISk. dyctx CTX. unfold ECP_DERIVE_Y_STACK in SLO.
    flat constr:(STk) 3%nat. intros HHk SUBk _.
    flat constr:(GRk) 9%nat. intros _ _ _ EP _ _ _ MP _.
    assert (POWN : md_own (g_P g) <> LHeap) by (apply (grp_static_own usegs MT mk LBk G g _ GRk H1); cbn; auto).
    flat constr:(MP) 6%nat. intros _ _ _ PHL PHN PHO. unfold MPI_MAX_LIMBS in PHN.
    assert (PNN : md_own (g_P g) <> LNull).
    { intros O. rewrite O in PHO. flat constr:(PHO) 2%nat. flclear PHO. intros _ N0. unfold mpd_val in PV. rewrite <- PHL in N0.
      destruct (md_limbs (g_P g)); [cbn in PV; lia| cbn in N0; lia]. }
    destruct (md_own (g_P g)) eqn:OP; [exfalso; exact (PNN eq_refl)| exfalso; exact (POWN eq_refl)|].
    flat constr:(PHO) 5%nat. flclear PHO. intros N1 _ P0 PB PRO. flat constr:(PB) 3%nat. intros PB0 PB1 _. rewrite u32s_length in PB1.
    pose proof (ROIMG _ (PRO 0 ltac:(lia)) ltac:(lia)) as R0. rewrite Z.add_0_r in R0.
    pose proof (ROIMG _ (PRO (4 * md_n (g_P g) - 1) ltac:(lia)) ltac:(lia)) as R1.
    assert (R1' : md_p (g_P g) + 4 * md_n (g_P g) <= hl_img_hi L) by lia.
    split; [split; [exact MP| left; exact GPS]|]. refine (conj EP (conj eq_refl (conj N1 (conj P0 (conj PRO (conj (proj1 R0) (conj R1' _))))))).
    rewrite EP. intros a Ha. destruct (GCR a ltac:(lia)) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [exact (SUBk _ Hb)| exact R]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L37273016624.62L59656785403.6200000?00kS1L2HI1h2SP1a1CS1L2HI3HLS4DIMG4IMGC1h2SP2lo3MC23SLO3ACL1a1C". (* [comment removed for export] *)
  Lemma dy_Y_cr : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)PSP,$8.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.P,(4>.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(28.(15.VL,R;.R4.(19.R:.)+10.)(15.VL,R;.R5.(19.R:.)+10.))")
(* [comment removed for export] *).
  Proof.
    intros until mo. intros CTX. dyctx CTX. unfold ECP_DERIVE_Y_STACK in SLO. flat constr:(XW) 3%nat. flclear XW. intros XCW _ _. split.
    - intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
    - intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00W0@L10081841430.170L10312886093.170L1055347216.179 L12103657014.172L13642019862.170L14001836165.141L15466341142.170L17420577239.141L19478245459.184L19478247022.178L19478247022.179L25579915514.181L29228048679.10 L29228048679.177L29230264897.175L29524232988.7  L29531738636.174L35628971931.141L43340057709.141L46225601430.170L48679929427.184L49786828438.170L51601712534.170L52991983944.174L52994132725.144L54914212946.144L55456638573.178L59229254640.141L59308585607.144L59308743383.149L63681460426.173L64515111501.143L6503841302.170 L65500231440.178L66362976704.173L66647107610.173L6767896743.7   L6963277465.141 L7940585743.175 00000500:00?00D00I00N00S00\00m01=01M01o02C02L02V02c03f03k04O04T04e04j04o05E05[05`06606D07007X07]08708<08A08F08\09309809YS3spvS3spvS3spvS3spvS3spvS3spvS3spvS3spv3SPUS3spv3dEk3SPB3NE1S3spv3dEk3SPB2N1S3spv3dEk3SPB2N1S1L3HLS3spv2lo3dYk3SLO3ACL3SPB3BY4S3spv1G2lo2GS1a2Ha1CS3spv1a1CS3spv1a2HaS3spv3SPA3SPBS1L3HLS4DIMG4IMGC3spv2dX1G2lo2GS2GX3SXS3MC23MCX3MCG3SLO3ACL3DHI3SPBS3spvS1L3HLS4DIMG4IMGC3spv2lo3MC23SLO3ACLS3spvS3spv3dYk3SPB3NY1S3spvS3spvS1L3HLS3spv2lo3SLO3SPBS1L3HLS3spv2lo3SLO3SPBS3spvS3spv2dX3dYk3SPB2N02HNS1L3spv2lo3SLOS1L3HLS4DIMG4IMGC3spv2lo3SLO3ACL3SPB1a2Ha2HdS1L3HLS3spv2lo3SLO3ACL3SPB1B1k1a2Ha1R2B4S3spvS1L2HI3spv1h4HTOP3SPB1a2HaS3spvS3spvS3spvS1L3HLS3spv2lo3SLO3SPBS1L3HLS3spv1G2lo2GS3SLOS3spvS1L3HLS3spv2lo3dEk3SLO3ACL3SPB2B4". (* [comment removed for export] *)
  Lemma dy_fin : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Prae,(0.&40.)Pspv,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0e,(0.&40.)Ps1e,(0.&40.)Ps2e,(0.&40.)Ps3e,(0.&40.)Ps4e,(0.&40.)Ps5e,(0.&40.)Ps6e,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pra0,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0c,(0.&40.)Ps1c,(0.&40.)Ps2c,(0.&40.)Ps4c,(0.&40.)Ps5c,(0.&40.)Ps6c,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)Plo,$8.Phk,(4.$42.VL,VHI,)PLBk,(5.$6.)PdYk,$7.PdEk,$7.Pmk,P,(0.&40.)(2.(0.&8.))Pmok,$3.Pr,$8.P,(4>.R?.R>.R=.R<.R;.R:.R9.(18.&40.R38.)R8.R11.R10.)P,(4?.R10.R?.R>.R<.R;.(18.&40.R39.)R9.R12.R11.R8.R7.R6.R5.R4.R3.)P,(21.$42.R5.(17.(18.&40.R3:.)-40.)(57.R31.R32.R33.R34.R35.R36.R37.R3;.))P,(<.(0.&40.)R39.(32.&40.(33.VL,)))P,(28.(29.(58.(45.+2.+1?.))R5.)(12.R5.=))(37.$42.R7.(38.$42.VL,VHI,VMT,R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R18.R17.R14.R13.R12.R10.R?.+5<?:8.R=.R16.R15.)(39.(3:.R2>.(32.&40.(17.(18.&40.R3=.)-50.))R3<.R3;.R2=.R2<.R2;.R2:.R29.R24.R23.R22.R21.R20.R1?.R1>.R1=.R28.(32.&40.R6.)R27.R26.R25.R33.R32.R31.R30.R2?.R1<.R1;.R1:.R19.)R18.(32.&40.+38:<<.)R17.(3;.(0.&40.))R8.(3<.$42.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros CTX STATE FR TP Hr. dyctx CTX. pose proof SLO as SLO0. unfold ECP_DERIVE_Y_STACK in SLO. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (dy_GR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE) as GRk. flat constr:(STATE) 6%nat. intros STk TYk PADk TEk COVk DISk.
    flat constr:(STk) 9%nat. intros HHk SUBk PXk SOKk MIk MFk HTk CNTk STk'. pose proof (heap_mok _ _ HI _ _ _ _ HHk) as MK. pose proof (HND _ _ _ _ HHk) as NDk.
    flat constr:(TEk) 4%nat. intros ME EE NSE FRE. flat constr:(TYk) 4%nat. intros MY EY NSY FRY.
    flat constr:((dy_Y_cr _ _ _ _ _ _ _ _ _ _ _ CTX)) 2%nat. intros YCRlo YCR.
    assert (BLY : md_own dYk = LHeap -> In (md_p dYk, 4 * md_n dYk) LBk /\ 1 <= md_n dYk /\ 0 < md_p dYk /\ md_p dYk + 4 * md_n dYk <= alloc_ceiling /\ ~ In (md_p dYk, 4 * md_n dYk) LB)
      by (intros O; exact (jtmp_blk usegs L HI hk LB LBk mk mok _ dYk HHk TYk O)).
    unfold dy_regs in FR.
    zstep. zstep.
    eapply (jst_free usegs L HI DIMG HND) with (d := dEk) (FR := 80) (SP := bv_unsigned spv) (lo := lo) (h := h) (LB := LB) (m := m) (mo := mo);
      [exact HFREEM| lia| exact STk| lia| exact HH| rewrite EE; exact TEk| rewrite EE; intros a Ha; left; lia
      | rewrite EE; intros [B k] a Hb Ha R; exfalso; cbn in R; (flat constr:((heap_blocks _ _ HI _ _ _ _ HHk)) 2%nat; intros HBRk _); pose proof (proj1 (Forall_forall _ _) HBRk _ Hb) as (_ & _ & _ & B4 & _); cbn in B4; lia
      | rewrite EE; intros a Ha Hd; exfalso; lia
      | rewrite EE; lia| exact MC1| exact MC2| exact MCS
      | rewrite EE; intros a Ha HC _; eapply (j_out_stack usegs L HI h LB m mo); [exact HH| exact ACL| exact DHI| exact HC| lia| lia]
      | lia| exact HLS| exact ACL| exact HTOP| clear - SPA SPB SLO HLS; lia| exact DHI| exact TP| exact CA| lia| lia| reflexivity| rewrite EE; apply f_equal; lia|].
    intros m8 mo8 h8 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ST8 CH8 PX8 BLE _. rewrite EE in CH8, PX8.
    flat constr:(ST8) 9%nat. intros HH8 SUB8 PX8o SOK8 MI8 MF8 HT8 (c8 & CNT8) STK8. clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH8) as MK.
    (* [comment removed for export] *)
    assert (FR8 : rw_cells usegs m8 (bv_unsigned spv + -64) (dy_regs s6e s5e s4e s3e s2e s1e s0e rae)).
    { eapply heap_presx_rw_cells; [exact PX8| exact FR| cbn; intros a Ha; left; lia|]. cbn [disjoint_from]. split; [cbn; lia|].
      apply free_X_disjoint. intros O. flat constr:((BLE O)) 5%nat. intros _ _ _ B4 _. cbn. lia. }
    assert (TY8 : jtmp usegs LB (lb_free_mpd dEk LBk) m8 (md_addr dX) dYk).
    { eapply (jtmp_presx usegs L); [exact TYk| exact PX8| exact MIk| exact MI8| | |].
      - intros a Ha. destruct (YCR a Ha) as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists b; split; [exact (SUB8 _ Hb)| exact R]].
      - cbn [disjoint_from]. split; [lia|]. apply free_X_disjoint. intros O. flat constr:((BLE O)) 5%nat. intros IN N1 _ _ NIN.
        eapply (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo); [exact HHk| exact IN| exact NIN| exact SUBk| lia| exact YCRlo| lia| exact ACL].
      - intros OY. flat constr:((BLY OY)) 5%nat. intros INY NY1 PY0 BY4 NINY.
        assert (INY' : In (md_p dYk, 4 * md_n dYk) (lb_free_mpd dEk LBk)).
        { apply lb_free_mpd_keep; [exact INY|]. intros OE. flat constr:((BLE OE)) 2%nat. intros INE _. apply not_eq_sym. eapply (j_nodup_fst_neq LBk); [exact NDk| exact INE| exact INY| apply not_eq_sym; exact (DISk OY OE)]. }
        split; [exact INY'|]. split; [exact INY'|].
        cbn [disjoint_from]. split; [lia|]. apply free_X_disjoint. intros OE. flat constr:((BLE OE)) 3%nat. intros INE NE1 _.
          eapply (j_blk_apart usegs L HI hk LBk mk mok); [exact HHk| exact INE| exact INY| apply not_eq_sym; exact (DISk OY OE)| lia| lia]. }
    assert (GR8 : ecp_group_at usegs MT m8 (lb_free_mpd dEk LBk) G g).
    { eapply (ecp_group_at_presx usegs L); [exact (grp_relist _ _ _ _ _ GRk H1 MIk)| exact PX8| exact MIk| exact MI8| | |].
      - intros a Ha. destruct (GCR a Ha) as [C|[C|(b & Hb & R)]]; [left; clear - C GS Ha SLO HLS; lia| right; left; exact C| right; right; exists b; split; [exact (SUB8 _ Hb)| exact R]].
      - cbn [disjoint_from]. split; [clear - GS SLO HLS; lia|]. apply free_X_disjoint. intros O. flat constr:((BLE O)) 5%nat. intros IN N1 _ _ NIN.
        eapply (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo); [exact HHk| exact IN| exact NIN| exact SUBk| lia| exact GCR| lia| exact ACL].
      - intros d Hd O. exfalso. exact (grp_static_own usegs MT mk LBk G g d GRk H1 Hd O). }
    clear FR PX8.
    (* [comment removed for export] *)
    unfold dy_regs in FR8.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    unfold mpi_cells in CH8. release_frame CH8 STK8 (bv_unsigned spv + -64). release_frame FR8 STK8 (bv_unsigned spv). zstep.
    apply aevtM_done. unfold ecp_mul_mod_post.
    flat constr:(TY8) 4%nat. intros MY8 EY8 NSY8 FRY8.
    flexi 14%nat. exists m8, mo8, h8, (lb_free_mpd dEk LBk), dYk, r, c8.
    split; [reflexivity|]. split; [exact MI8|]. split; [exact STK8|]. split; [exact MF8|]. split; [exact HT8|].
    split; [exact HH8|]. split; [exact MY8|].
    split. { (* [comment removed for export] *)
      split; [exact EY8|]. split; [exact NSY8|]. split; [| split; [intros b Hb _; exact (SUB8 _ Hb)| intros b Hb; unfold mpd_blk in Hb; rewrite YNULL in Hb; destruct Hb]].
      intros b Hb. pose proof (lb_free_mpd_sub _ _ _ Hb) as Hbk. destruct (COVk b Hbk) as [C|[C|C]]; [left; exact C| right; exact C| exfalso].
      flat constr:((mpd_blk_single dEk b C)) 3%nat. intros _ OE ->. unfold lb_free_mpd in Hb. rewrite OE in Hb. exact (lb_remove_notin _ _ _ NDk Hb). }
    split. { unfold mpd_ivs. rewrite YNULL. exact PX8o. }
    split; [exact SOK8|]. split; [exact GR8|]. split; [exact CNT8|].
    unfold mul_mod_R, binop_keep. refine (conj Hr (conj EY8 (conj PADk (conj _ _)))).
    - intros b Hb. right. exact (FRY8 b Hb).
    - flat constr:(MX0) 2%nat. intros FLt1 _. flat constr:(FLt1) 6%nat. flclear FLt1. intros _ _ _ _ _ HO. rewrite YNULL in HO. flat constr:(HO) 2%nat. flclear HO. intros _ N0. flat constr:(MY8) 2%nat. intros FLt2 _. flat constr:(FLt2) 6%nat. flclear FLt2. intros _ _ _ _ HN _. lia.
  all: match goal with |- ?gg => idtac "FINLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac dystate STATE := pose proof STATE as (STk & TYk & PADk & TEk & COVk & DISk);
    pose proof STk as (HHk & SUBk & PXk & SOKk & MIk & MFk & HTk & CNTk & STk');
    pose proof TYk as (MY & EY & NSY & FRY); pose proof TEk as (ME & EE & NSE & FRE).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090@L10010478707.98 L1055347216.99  L15361929392.100L16819077072.100L17814609708.97 L18727065235.7  L48679927918.99 L55797547584.98 L65500231440.99 00000?00C00O00\01F01T02>02K02OS1L2HI1h2SP1a1CS2SPS1G2SP3dYk1HS2dX2SP3dYk1HS1L3HLS4DIMG4IMGC2SP2lo3dYk3MC23SLO3ACL2B4S2dX2SP2lo3SXSS1L3HLS4DIMG4IMGC2SP2lo3dYk3MC23SLO3ACL2N1S2SP3dYk1a2HaS2SP". (* [comment removed for export] *)
  Lemma dy_Y_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)PSP,$8.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Phk,(4.$42.VL,VHI,)PLBk,(5.$6.)PdYk,$7.PdEk,$7.Pmk,P,(0.&40.)(2.(0.&8.))Pmok,$3.P,(4>.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(4?.R12.R11.R10.R>.R=.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(28.(1:.$42.R4.R7.R6.)(28.(2:.(<.$1;.(1<.R6.)$50.))(28.(<.$8.(19.R6.)(19.R11.))(28.(1>.VL,R7.(2>.R<.+50.)(1?.$42.VL,VHI,R13.)R6.)(28.P,(2:.(<.$1;.(1<.R6.)$1=.))(16.(12.(17.(3>.R7.)(3?.+4.(14.R7.)))R<.)(12.(2>.R=.+50.)(3>.R7.)))(28.P,(<.$1;.(1<.R6.)$3=.)(28.(4:.(4<.$8.$8.)(4=.$8.$8.(3>.R7.)(3?.+4.(14.R7.)))R8.)(28.(12.+1.(14.R7.))(28.(29.=(3>.R7.))(28.(12.(17.(3>.R7.)(3?.+4.(14.R7.)))(30.VL,))(28.(2:.(4:.(4<.$8.$8.)(4=.$8.$8.(3>.R7.)(3?.+4.(14.R7.)))R13.))(28.(16.(12.(17.(19.R12.)+10.)(3>.R7.))(12.(17.(3>.R7.)(3?.+4.(14.R7.)))(19.R12.)))(16.(12.(17.R10.+<0.)(3>.R7.))(12.(17.(3>.R7.)(3?.+4.(14.R7.)))R10.))))))))(28.(59.R6.R6.)(28.(5:.R6.R6.R;.(2>.R<.+50.))(28.(15.VL,R7.R;.(19.R6.)+10.)P,(<.$1;.(1<.R6.)$3=.)(15.VL,R8.R<.(3>.R7.)(3?.+4.(14.R7.))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX STATE. dyctx CTX. unfold ECP_DERIVE_Y_STACK in SLO. dystate STATE. pose proof alloc_ceiling_pos as ACP.
    flat constr:((dy_Y_cr _ _ _ _ _ _ _ _ _ _ _ CTX)) 2%nat. intros YCRlo YCR. flat constr:(XW) 3%nat. flclear XW. intros XCW XD _.
    assert (BLY : md_own dYk = LHeap -> In (md_p dYk, 4 * md_n dYk) LBk /\ 1 <= md_n dYk /\ 0 < md_p dYk /\ md_p dYk + 4 * md_n dYk <= alloc_ceiling /\ ~ In (md_p dYk, 4 * md_n dYk) LB
                             /\ (md_addr dX + 16 <= md_p dYk \/ md_p dYk + 4 * md_n dYk <= md_addr dX) /\ (G + 192 <= md_p dYk \/ md_p dYk + 4 * md_n dYk <= G)).
    { intros O. flat constr:((jtmp_blk usegs L HI hk LB LBk mk mok _ dYk HHk TYk O)) 5%nat. intros IN N1 P0 B4 NIN.
      refine (conj IN (conj N1 (conj P0 (conj B4 (conj NIN (conj _ _)))))).
      - pose proof (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo _ _ (md_addr dX) 16 HHk IN NIN SUBk ltac:(lia) YCRlo ltac:(lia) ACL). lia.
      - pose proof (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo _ _ G 192 HHk IN NIN SUBk ltac:(lia) GCR ltac:(lia) ACL). lia. }
    assert (XSL : md_own dYk <> LNull -> md_p dYk + 4 * md_n dYk <= lo \/ SP - 80 <= md_p dYk).
    { intros NN. destruct (md_own dYk) eqn:O; [exfalso; exact (NN eq_refl)| (flat constr:((BLY eq_refl)) 5%nat; intros _ _ _ B4 _); left; lia| exfalso; exact (NSY eq_refl)]. }
    refine (conj MY (conj NSY (conj EY (conj _ (conj XSL (conj BLY (conj (or_introl eq_refl) (conj _ (conj _ _))))))))).
    - unfold mpd_writable. rewrite EY. split; [| split; [exact XD| intros O; (flat constr:((BLY O)) 7%nat; intros _ _ _ _ _ AP _); exact AP]].
      intros a Ha. destruct (XCW a Ha) as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists b; split; [exact (SUBk _ Hb)| exact R]].
    - unfold opnd_sep. rewrite EY. split; [intros NN; destruct (md_own dYk) eqn:O; [exfalso; exact (NN eq_refl)| (flat constr:((BLY eq_refl)) 7%nat; intros _ _ _ _ _ AP _); exact AP| exfalso; exact (NSY eq_refl)]|].
      split; [intros O; (flat constr:((BLY O)) 7%nat; intros _ _ _ _ _ AP _); exact AP|]. split; [left; reflexivity|]. split; [clear - SXS SLO HLS; lia| exact XSL].
    - rewrite EY. intros a Ha. destruct (YCRlo a Ha) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [exact (SUBk _ Hb)| exact R]].
    - intros O a Ha. right; right. exists (md_p dYk, 4 * md_n dYk). split; [exact (proj1 (BLY O))| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L10012400405.98 L1055347216.100 L11030662608.101L19478247022.100L19478249043.103L19586120406.98 L19586120406.99 L33057279148.96 L34144031552.7  L48679929939.103L48814886101.7  L58095932716.98 L59308585607.99 L59654577821.98 L64665708758.98 L65500231440.100L9052848816.101 L9936500800.99  00000b00f01301]02G03103[03_04704b05:05d06O07707a07e08108>S1L2HI3HLS4DIMG4IMGC1h2SP2lo3MC23SLO3ACL4HTOP1a2HaS2SPS2dX2SP3dEk1HS1L3HLS4DIMG4IMGC2SP2lo3dEk3MC23SLO3ACL2N1S1L3HLS4DIMG4IMGC2SP2lo3dEk3MC23SLO3ACL2N1S1L3HLS4DIMG4IMGC2SP2lo3dEk3MC23SLO3ACL2B4S1L3HLS4DIMG4IMGC2SP2lo3dEk3MC23SLO3ACL2B4S2SPS1L3HLS2dX2SP2lo3SXS3SLOS1L3HLS4DIMG4IMGC2SP2lo3dYk3MC23SLO3ACL3NY1S1L3HLS2dX2SP2lo3SXS3SLOS1L3HLS4DIMG4IMGC2SP2lo3dEk3MC23SLO3ACL2B4S1L3HLS4DIMG4IMGC2SP2lo3MC23SLO3ACL1a2Ha2HdS1L3HLS4DIMG4IMGC2SP2lo3MC23SLO3ACL1a2HaS1L3HLS4DIMG4IMGC2SP2lo3dYk3MC23SLO3ACL2B4S2SPS1G2SP3dEk1HS2SP3dEk1a2Ha". (* [comment removed for export] *)
  Lemma dy_E_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)PSP,$8.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Phk,(4.$42.VL,VHI,)PLBk,(5.$6.)PdYk,$7.PdEk,$7.Pmk,P,(0.&40.)(2.(0.&8.))Pmok,$3.P,(4>.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(4?.R12.R11.R10.R>.R=.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(28.(1:.$42.R4.R7.R5.)(28.(<.$8.(19.R5.)(2>.R<.+50.))(28.(2:.(<.$1;.(1<.R5.)$50.))(28.P,(<.$1;.(1<.R5.)$3=.)(28.(4:.(4<.$8.$8.)(4=.$8.$8.(3>.R6.)(3?.+4.(14.R6.)))R8.)(28.(12.+1.(14.R6.))(28.(29.=(3>.R6.))(28.(12.(17.(3>.R6.)(3?.+4.(14.R6.)))(30.VL,))(28.(2:.(4:.(4<.$8.$8.)(4=.$8.$8.(3>.R6.)(3?.+4.(14.R6.)))R13.))(28.(16.(12.(17.(19.R12.)+10.)(3>.R6.))(12.(17.(3>.R6.)(3?.+4.(14.R6.)))(19.R12.)))(28.(16.(12.(17.R10.+<0.)(3>.R6.))(12.(17.(3>.R6.)(3?.+4.(14.R6.)))R10.))P,(<.$1;.(1<.R7.)$3=.)(16.(12.(17.(3>.R8.)(3?.+4.(14.R8.)))(3>.R7.))(12.(17.(3>.R7.)(3?.+4.(14.R7.)))(3>.R8.))))))))))(28.(59.R6.R5.)(28.(2:.(<.$8.(19.R6.)(19.R5.)))(28.(5:.R6.R5.R;.(2>.R<.+50.))(28.(15.VL,R7.R;.(19.R5.)+10.)(28.P,(<.$1;.(1<.R5.)$3=.)(15.VL,R8.R<.(3>.R6.)(3?.+4.(14.R6.)))(28.(1>.VL,R7.(2>.R<.+50.)(1?.$42.VL,VHI,R13.)R5.)(28.P,(2:.(<.$1;.(1<.R5.)$1=.))(16.(12.(17.(3>.R6.)(3?.+4.(14.R6.)))R<.)(12.(2>.R=.+50.)(3>.R6.)))(28.(59.R5.R5.)(5:.R5.R5.R;.(2>.R<.+50.))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX STATE. dyctx CTX. unfold ECP_DERIVE_Y_STACK in SLO. dystate STATE. pose proof alloc_ceiling_pos as ACP.
    flat constr:((dy_Y_cr _ _ _ _ _ _ _ _ _ _ _ CTX)) 2%nat. intros YCRlo YCR.
    flat constr:((dy_Y_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE)) 7%nat. intros _ _ _ _ XSL BLY _.
    assert (BLE : md_own dEk = LHeap -> In (md_p dEk, 4 * md_n dEk) LBk /\ 1 <= md_n dEk /\ 0 < md_p dEk /\ md_p dEk + 4 * md_n dEk <= alloc_ceiling /\ ~ In (md_p dEk, 4 * md_n dEk) LB
                             /\ (md_addr dX + 16 <= md_p dEk \/ md_p dEk + 4 * md_n dEk <= md_addr dX) /\ (G + 192 <= md_p dEk \/ md_p dEk + 4 * md_n dEk <= G)
                             /\ (md_own dYk = LHeap -> md_p dYk + 4 * md_n dYk <= md_p dEk \/ md_p dEk + 4 * md_n dEk <= md_p dYk)).
    { intros O. flat constr:((jtmp_blk usegs L HI hk LB LBk mk mok _ dEk HHk TEk O)) 5%nat. intros IN N1 P0 B4 NIN.
      refine (conj IN (conj N1 (conj P0 (conj B4 (conj NIN (conj _ (conj _ _))))))).
      - pose proof (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo _ _ (md_addr dX) 16 HHk IN NIN SUBk ltac:(lia) YCRlo ltac:(lia) ACL). lia.
      - pose proof (j_fresh_apart usegs L HI DIMG hk LBk mk mok LB lo _ _ G 192 HHk IN NIN SUBk ltac:(lia) GCR ltac:(lia) ACL). lia.
      - intros OY. flat constr:((BLY OY)) 3%nat. intros INY NY1 _. exact (j_blk_apart usegs L HI hk LBk mk mok _ _ _ _ HHk INY IN (DISk OY O) ltac:(lia) ltac:(lia)). }
    assert (ESL : md_own dEk <> LNull -> md_p dEk + 4 * md_n dEk <= lo \/ SP - 80 <= md_p dEk).
    { intros NN. destruct (md_own dEk) eqn:O; [exfalso; exact (NN eq_refl)| (flat constr:((BLE eq_refl)) 5%nat; intros _ _ _ B4 _); left; lia| exfalso; exact (NSE eq_refl)]. }
    refine (conj ME (conj EE (conj NSE (conj BLE _)))).
    split; [right; rewrite EY, EE; clear - SXS SLO HLS; lia|]. split; [rewrite EY, EE; clear - SXS SLO HLS; lia|].
    split. { unfold opnd_sep. rewrite EY, EE. split; [intros NN; destruct (md_own dEk) eqn:O; [exfalso; exact (NN eq_refl)| (flat constr:((BLE eq_refl)) 7%nat; intros _ _ _ _ _ AP _); exact AP| exfalso; exact (NSE eq_refl)]|].
      split; [intros O; (flat constr:((BLY O)) 5%nat; intros _ _ _ B4 _); right; lia|].
      split; [| split; [right; lia| exact ESL]].
      destruct (md_own dYk) eqn:OY; [right; left; discriminate| | right; left; discriminate].
      destruct (md_own dEk) eqn:OE; [right; right; left; reflexivity| | exfalso; exact (NSE eq_refl)].
      right; right; right. flat constr:((BLE eq_refl)) 8%nat. intros _ _ _ _ _ _ _ AP. exact (AP eq_refl). }
    split; [rewrite EE; intros a Ha; left; lia|].
    split; [intros O a Ha; right; right; exists (md_p dEk, 4 * md_n dEk); split; [exact (proj1 (BLE O))| cbn; lia]|].
    split. { unfold mpd_writable. rewrite EE. split; [intros a Ha; left; lia|]. split; [intros a Ha Hd; exfalso; lia|].
      intros O. flat constr:((BLE O)) 5%nat. intros _ _ _ B4 _. right. lia. }
    split; [exact ESL|]. split; [left; reflexivity|].
    unfold opnd_sep. rewrite EE. split; [intros NN; destruct (md_own dEk) eqn:O; [exfalso; exact (NN eq_refl)| (flat constr:((BLE eq_refl)) 5%nat; intros _ _ _ B4 _); right; lia| exfalso; exact (NSE eq_refl)]|]. split; [intros O; (flat constr:((BLE O)) 5%nat; intros _ _ _ B4 _); right; lia|].
    split; [left; reflexivity|]. split; [right; lia| exact ESL].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L19682225709.7  L21586389085.3  L25086372389.109L26648542550.106L31450671680.108L32201215013.109L33671216523.105L37162820355.7  L38644968030.3  L40494084160.108L4442638618.106 L48172257724.105L67729409135.10600000F00O01l02902O03l04004<04E04[05C05l06TS1L3HLS1G2SP2lo2GS3SLOS2dX1G2GXS1L3HLS4DIMG4IMGC2dX1G1g2SP2lo3dEk2GS2GX3SXS3MC13MC23MCX3MCG3SLO3ACL3SPA3DHI3PN12R02R13APY2B5S2dX1g2SP3APYS2dX1G1g2SP3dYk3APY2APS1L3HLS4DIMG4IMGC2dX1G1g2SP2lo3dYk2GS2GX3SXS3MC13MC23MCX3MCG3SLO3ACL3SPA3DHI3PN12R02R13APY2B5S2SPS1G2SP2lo2GSS2dX1G2GXS2dX1G1g2SP3dEk3APY2APS1L3HLS4DIMG4IMGC1g2SP2lo3MC23SLO3ACL2R1S1L3HLS4DIMG4IMGC1g2SP2lo3MC23SLO3ACL3PN1S1L3HLS4DIMG4IMGC1g2SP2lo3MC23SLO3ACL2R1". (* [comment removed for export] *)
  Lemma dy_P_sep : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)PSP,$8.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Phk,(4.$42.VL,VHI,)PLBk,(5.$6.)PdYk,$7.PdEk,$7.Pmk,P,(0.&40.)(2.(0.&8.))Pmok,$3.P,(4>.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(4?.R12.R11.R10.R>.R=.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(28.(59.R6.(?.R>.))(28.(2:.(<.$8.(19.R6.)(19.(?.R>.))))(28.(5:.R6.(?.R>.)R;.(2>.R<.+50.))(28.(59.R5.(?.R>.))(28.(5:.R5.(?.R>.)R;.(2>.R<.+50.))(28.P,(<.$1;.(1<.(?.R>.))$3=.)(15.VL,R8.R<.(3>.(?.R?.))(3?.+4.(14.(?.R?.))))P,(<.$1;.(1<.(?.R>.))$3=.)(29.=(3>.(?.R?.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros until mok. intros CTX STATE. dyctx CTX. unfold ECP_DERIVE_Y_STACK in SLO. dystate STATE. pose proof alloc_ceiling_pos as ACP.
    flat constr:((dy_P_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE)) 9%nat. intros MP EP OP PN1 PP0 PRO R0 R1 CRP.
    flat constr:((dy_Y_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE)) 7%nat. intros _ _ _ _ XSL BLY _.
    flat constr:((dy_E_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE)) 12%nat. intros _ _ _ BLE _ _ _ _ _ _ ESL _.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HHk)) 2%nat. intros HBRk _.
    flat constr:(MY) 2%nat. intros (CHY & _) _. rewrite EY in CHY.
    pose proof (rw_ro_apart usegs mk _ _ (md_p (g_P g)) (4 * md_n (g_P g)) MIk CHY ltac:(cbn; lia) ltac:(lia) PRO) as APY. cbn [cells_size csize Nat.add length mpi_cells] in APY.
    split; [right; rewrite EY, EP; clear - GX; lia|]. split; [rewrite EY, EP; clear - GX; lia|].
    split. { unfold opnd_sep. rewrite EY, EP, OP. split; [intros _; lia|]. split; [intros O; (flat constr:((BLY O)) 7%nat; intros _ _ _ _ _ _ AP); lia|].
      split. { destruct (md_own dYk) eqn:OY; [right; left; discriminate| | right; left; discriminate]. right; right; right.
        flat constr:((BLY eq_refl)) 2%nat. intros IN _. flat constr:((proj1 (Forall_forall _ _) HBRk _ IN)) 5%nat. intros _ _ _ _ B5. cbn in B5. lia. }
      split; [clear - GS SLO HLS; lia| intros _; left; lia]. }
    split; [right; rewrite EE, EP; clear - GS SLO HLS; lia|].
    split. { unfold opnd_sep. rewrite EE, EP, OP. split; [intros _; lia|]. split; [intros O; (flat constr:((BLE O)) 8%nat; intros _ _ _ _ _ _ AP _); lia|].
      split. { destruct (md_own dEk) eqn:OE; [right; left; discriminate| | right; left; discriminate]. right; right; right.
        flat constr:((BLE eq_refl)) 2%nat. intros IN _. flat constr:((proj1 (Forall_forall _ _) HBRk _ IN)) 5%nat. intros _ _ _ _ B5. cbn in B5. lia. }
      split; [clear - GS SLO HLS; lia| intros _; left; lia]. }
    rewrite OP. split; intros; discriminate.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L19365251703.132L19478199291.130L28248021213.7  L4003770393.130 L44435711919.123L4478335651.121 L48161800634.131L48679927918.130L50201711274.121L55877722379.121L57051693602.130L65267191243.12300000>00i01A01P02:02]02g03Q03U03_04<04ES2SP3dYk3dEk1HS1L3HLS4DIMG4IMGC2SP2lo3dEk3MC23SLO3ACL3NE1S1L3HLS2dX2SP2lo3SXS3SLOS2dX2SP3dEk3APXS1L3HLS4DIMG4IMGC2SP2lo3dYk3MC23SLO3ACL2B4S1L3HLS4DIMG4IMGC2SP2lo3MC23SLO3ACLS2SP3dEk1HS1L3HLS4DIMG4IMGC2SP2lo3dYk3MC23SLO3ACL2N1S2SPS2SP1A1n1DS1L3HLS2SP2lo3MC23SLO3ACL3DHIS2SP1a2Ha". (* [comment removed for export] *)
  Lemma dy_Ystep : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)PSP,$8.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Phk,(4.$42.VL,VHI,)PLBk,(5.$6.)PdYk,$7.PdEk,$7.Pmk,P,(0.&40.)(2.(0.&8.))Pmok,$3.Ph',(4.$42.VL,VHI,)PLB',(5.$6.)PdY',$7.Pm',P,(0.&40.)(2.(0.&8.))Pmo',$3.PXC,(5.$5;.)P,(4>.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)P,(4?.R18.R17.R16.R14.R13.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(16.(<.(5.$5;.)R3.(25.$5;.))(<.(5.$5;.)R3.(22.(4<.$8.$8.)(4=.$8.$8.+5<?:8.(17.+5<?:8.+8.))(25.(4<.$8.$8.)))))P,(:.$42.VL,VHI,R9.R8.R6.R5.)P,(1:.$42.R7.R9.R8.)P,(5<.R10.R?.R:.R9.)P,Pb,$6.P,(4:.$6.R1.(4;.R;.))(16.(4:.$6.R2.(4;.R12.))(2:.(4:.$6.R2.R13.)))P,(<.(0.&40.)(49.R;.)(49.R11.))P,(5=.$42.VL,R13.(2>.R18.+50.)(5>.(4<.$8.$8.)(5?.R12.)R9.)R10.R;.)P,(35.$42.VL,R<.)P,(34.$42.R=.)P,(60.R12.R=.)P,(<.$8.(1?.$42.VL,VHI,R12.)(1?.$42.VL,VHI,R18.))P,(61.(0.&40.)Lc,(0.&40.)(21.$42.R11.+5<?:8.(22.$23.(24.R1.)(25.$23.))))P,(2=.$42.R11.R1=.(2>.R1>.+50.))(4?.R26.R25.R24.R22.R21.R1?.R1>.R1=.R1<.R15.R14.R13.R18.R12.R11.)")
(* [comment removed for export] *).
  Proof.
    intros until XC. intros CTX STATE HXC HH' MA' OUT' FRB' PAD' PX' SOK' MI' MF' HT' CNT' ST'. dyctx CTX. unfold ECP_DERIVE_Y_STACK in SLO. dystate STATE.
    pose proof alloc_ceiling_pos as ACP. flat constr:(OUT') 5%nat. intros EA' NS' K1 K2 K3.
    flat constr:((dy_Y_cr _ _ _ _ _ _ _ _ _ _ _ CTX)) 2%nat. intros YCRlo YCR.
    flat constr:((dy_Y_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE)) 7%nat. intros _ _ _ _ XSL BLY _.
    flat constr:((dy_E_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE)) 5%nat. intros _ _ _ BLE _.
    assert (SUB' : forall b, In b LB -> In b LB').
    { intros b Hb. apply K2; [exact (SUBk _ Hb)|]. intros HX. exact (FRY _ HX Hb). }
    assert (DXC : forall A n, (U_MUL_COUNT + 8 <= A \/ A + n <= U_MUL_COUNT) -> disjoint_from XC A n).
    { intros A n D. destruct HXC as [-> | ->]; cbn; [exact I| split; [lia| exact I]]. }
    unfold dy_state. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    - eapply (jst_step usegs L HI) with (SPX := SP - 80) (LBX := LBk); [exact STk| lia| exact HH'| exact SUB'| exact PX'| exact SUBk| | exact SOK'| exact MI'| exact MF'| exact HT'| exact CNT'| exact ST'].
      intros a Ha HC HO. unfold dy_XO in HO. cbn in HO. flat constr:(HO) 3%nat. flclear HO. intros O1 O2 _. rewrite outside_app. split.
      + unfold mpd_ivs. rewrite EY. cbn. split; [exact O1|]. destruct (md_own dYk) eqn:OY; cbn; [exact I| | exfalso; exact (NSY eq_refl)]. split; [| exact I].
        flat constr:((BLY eq_refl)) 6%nat. intros IN N1 _ _ NIN _. eapply (j_out_blk usegs L HI DIMG hk LBk mk mok LB SP a); [exact HHk| exact IN| exact NIN| exact SUBk| lia| lia| exact HC].
      + destruct HXC as [-> | ->]; cbn; [exact I| exact (conj O2 I)].
    - refine (conj MA' (conj (eq_trans EA' EY) (conj NS' _))). intros b Hb HbL. destruct (FRB' b Hb) as [X|X]; [exact (FRY _ X HbL)| exact (X (SUBk _ HbL))].
    - rewrite PAD'. exact PADk.
    - eapply (jtmp_presx usegs L); [exact TEk| exact PX'| exact MIk| exact MI'| intros a Ha; left; lia| |].
      + rewrite (disjoint_from_app L DIMG). split; [| apply DXC; lia]. unfold mpd_ivs. rewrite EY. cbn. split; [clear - SXS SLO HLS; lia|].
        destruct (md_own dYk) eqn:OY; cbn; [exact I| | exfalso; exact (NSY eq_refl)]. split; [| exact I]. flat constr:((BLY eq_refl)) 5%nat. intros _ _ _ B4 _. lia.
      + intros OE. flat constr:((BLE OE)) 8%nat. intros INE NE1 PE0 BE4 NINE APX APG APY. split; [exact INE|]. split.
        * apply K2; [exact INE|]. intros HX. flat constr:((mpd_blk_single dYk _ HX)) 3%nat. intros _ OY E. exact (DISk OY OE (eq_sym E)).
        * rewrite (disjoint_from_app L DIMG). split; [| apply DXC; pose proof (j_blk_MC usegs L HI DIMG hk LBk mk mok _ _ U_MUL_COUNT HHk INE ltac:(lia) MC1 MC2); lia].
          unfold mpd_ivs. rewrite EY. cbn. split; [lia|]. destruct (md_own dYk) eqn:OY; cbn; [exact I| | exfalso; exact (NSY eq_refl)]. split; [| exact I]. pose proof (APY eq_refl). lia.
    - intros b Hb. destruct (K1 b Hb) as [X|X]; [| right; left; exact X]. destruct (COVk b X) as [C|[C|C]]; [left; exact C| | right; right; exact C].
      right; left. rewrite (K3 b C Hb). exact C.
    - intros OY' OE E. destruct (FRB' (md_p dY', 4 * md_n dY') ltac:(unfold mpd_blk; rewrite OY'; left; reflexivity)) as [X|X].
      + flat constr:((mpd_blk_single dYk _ X)) 3%nat. intros _ OY E2. apply (DISk OY OE). rewrite <- E2. exact E.
      + apply X. rewrite E. exact (proj1 (BLE OE)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L12656821694.124L14749714598.123L19365251703.127L19476138579.122L19478247022.127L28248021213.7  L3992011248.122 L4001673234.121 L40147641242.121L44437803055.124L49389445539.119L50203811112.119L55541460255.123L57051693602.127L59101894031.123L63887036889.121L65269178029.12200000>00H00V01@01j02B02M02[03K04604Y04]04a05>05a05j062S2SP3dEk1A1n1HS2SP3dEk1HS2SP3dYk3dEk1HS1L3HLS4DIMG4IMGC2SP2lo3dEk3MC23SLO3ACL2N1S1L3HLS4DIMG4IMGC2SP2lo3dEk3MC23SLO3ACL2N1S1L3HLS2dX2SP2lo3SXS3SLOS2SP1A1n2D1S2dX2SP3dEk2APS1L3HLS4DIMG4IMGC2SP2lo3MC13MC23SLO3ACL3DHI1a2HaS1L3HLS4DIMG4IMGC2SP2lo3dYk3MC23SLO3ACL3BY4S1L3HLS4DIMG4IMGC2SP2lo3MC23SLO3ACLS2SPS2SPS1L3HLS2SP2lo3MC23SLO3ACL3DHIS1L3HLS4DIMG4IMGC2SP2lo3MC23SLO3ACLS2SP1a2HaS2SP1a1C". (* [comment removed for export] *)
  Lemma dy_Estep : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)PSP,$8.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Phk,(4.$42.VL,VHI,)PLBk,(5.$6.)PdYk,$7.PdEk,$7.Pmk,P,(0.&40.)(2.(0.&8.))Pmok,$3.Ph',(4.$42.VL,VHI,)PLB',(5.$6.)PdE',$7.Pm',P,(0.&40.)(2.(0.&8.))Pmo',$3.P,(4>.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)P,(4?.R17.R16.R15.R13.R12.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(:.$42.VL,VHI,R7.R6.R4.R3.)P,(1:.$42.R5.R7.R6.)P,(5<.R>.R<.R8.R7.)P,Pb,$6.P,(4:.$6.R1.(4;.R9.))(16.(4:.$6.R2.(4;.R?.))(2:.(4:.$6.R2.R11.)))P,(5=.$42.VL,R10.(2>.R15.+50.)(5?.R>.)R=.R8.)P,(35.$42.VL,R9.)P,(34.$42.R:.)P,(60.R?.R:.)P,(<.$8.(1?.$42.VL,VHI,R?.)(1?.$42.VL,VHI,R15.))P,(2=.$42.R=.R19.(2>.R1:.+50.))(4?.R22.R21.R20.R1>.R1=.R1;.R1:.R19.R18.R11.R10.R15.R?.R>.R=.)")
(* [comment removed for export] *).
  Proof.
    intros until mo'. intros CTX STATE HH' MA' OUT' FRB' PX' SOK' MI' MF' HT' ST'. dyctx CTX. unfold ECP_DERIVE_Y_STACK in SLO. dystate STATE.
    pose proof alloc_ceiling_pos as ACP. flat constr:(OUT') 5%nat. intros EA' NS' K1 K2 K3. flat constr:(STk) 9%nat. intros _ _ _ _ _ _ _ (ck & CNTk0) _.
    flat constr:((dy_Y_cr _ _ _ _ _ _ _ _ _ _ _ CTX)) 2%nat. intros YCRlo YCR.
    flat constr:((dy_Y_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE)) 7%nat. intros _ _ _ _ XSL BLY _.
    flat constr:((dy_E_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE)) 5%nat. intros _ _ _ BLE _.
    assert (SUB' : forall b, In b LB -> In b LB').
    { intros b Hb. apply K2; [exact (SUBk _ Hb)|]. intros HX. exact (FRE _ HX Hb). }
    assert (DE : forall A n, SP - 80 + 16 <= A \/ A + n <= SP - 80 -> (md_own dEk = LHeap -> md_p dEk + 4 * md_n dEk <= A \/ A + n <= md_p dEk) -> disjoint_from (mpd_ivs dEk) A n).
    { intros A n D1 D2. unfold mpd_ivs. rewrite EE. cbn. split; [lia|]. destruct (md_own dEk) eqn:O; cbn; [exact I| | exfalso; exact (NSE eq_refl)]. split; [| exact I]. pose proof (D2 eq_refl). lia. }
    unfold dy_state. refine (conj _ (conj _ (conj PADk (conj _ (conj _ _))))).
    - eapply (jst_step usegs L HI) with (SPX := SP - 80) (LBX := LBk); [exact STk| lia| exact HH'| exact SUB'| exact PX'| exact SUBk| | exact SOK'| exact MI'| exact MF'| exact HT'| | exact ST'].
      + intros a Ha HC HO. unfold mpd_ivs. rewrite EE. cbn. split; [eapply (j_out_stack usegs L HI h LB m mo); [exact HH| exact ACL| exact DHI| exact HC| lia| lia]|].
        destruct (md_own dEk) eqn:OE; cbn; [exact I| | exfalso; exact (NSE eq_refl)]. split; [| exact I].
        flat constr:((BLE eq_refl)) 6%nat. intros IN N1 _ _ NIN _. eapply (j_out_blk usegs L HI DIMG hk LBk mk mok LB SP a); [exact HHk| exact IN| exact NIN| exact SUBk| lia| lia| exact HC].
      + exists ck. eapply heap_presx_rw_cells; [exact PX'| exact CNTk0| cbn; intros a Ha; right; left; split; [lia| apply MCS; lia]|].
        cbn [cells_size csize Nat.add]. apply DE; [lia|]. intros O. flat constr:((BLE O)) 3%nat. intros IN N1 _. pose proof (j_blk_MC usegs L HI DIMG hk LBk mk mok _ _ U_MUL_COUNT HHk IN ltac:(lia) MC1 MC2). lia.
    - eapply (jtmp_presx usegs L); [exact TYk| exact PX'| exact MIk| exact MI'| | |].
      + intros a Ha. destruct (YCR a Ha) as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists b; split; [exact (SUBk _ Hb)| exact R]].
      + apply DE; [clear - SXS SLO HLS; lia|]. intros O. flat constr:((BLE O)) 7%nat. intros _ _ _ _ _ AP _. lia.
      + intros OY. flat constr:((BLY OY)) 5%nat. intros INY NY1 PY0 BY4 _. split; [exact INY|]. split.
        * apply K2; [exact INY|]. intros HX. flat constr:((mpd_blk_single dEk _ HX)) 3%nat. intros _ OE E. exact (DISk OY OE E).
        * apply DE; [lia|]. intros OE. flat constr:((BLE OE)) 8%nat. intros _ _ _ _ _ _ _ AP. pose proof (AP OY). lia.
    - refine (conj MA' (conj (eq_trans EA' EE) (conj NS' _))). intros b Hb HbL. destruct (FRB' b Hb) as [X|X]; [exact (FRE _ X HbL)| exact (X (SUBk _ HbL))].
    - intros b Hb. destruct (K1 b Hb) as [X|X]; [| right; right; exact X]. destruct (COVk b X) as [C|[C|C]]; [left; exact C| right; left; exact C|].
      right; right. rewrite (K3 b C Hb). exact C.
    - intros OY OE' E. destruct (FRB' (md_p dE', 4 * md_n dE') ltac:(unfold mpd_blk; rewrite OE'; left; reflexivity)) as [X|X].
      + flat constr:((mpd_blk_single dEk _ X)) 3%nat. intros _ OE E2. apply (DISk OY OE). rewrite E, <- E2. reflexivity.
      + apply X. rewrite <- E. exact (proj1 (BLY OY)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L14003934489.108L59101798041.10800000400WS2SPS1L3HLS4DIMG4IMGC2SP2lo3MC23SLO3ACL". (* [comment removed for export] *)
  Lemma dy_munch : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)PSP,$8.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Phk,(4.$42.VL,VHI,)PLBk,(5.$6.)PdYk,$7.PdEk,$7.Pmk,P,(0.&40.)(2.(0.&8.))Pmok,$3.Pm',P,(0.&40.)(2.(0.&8.))PdE',$7.PW,(5.$5;.)P,(4>.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)P,(4?.R15.R14.R13.R11.R10.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(62.R3.R7.R5.)P,(63.$42.R8.R6.)P,(34.$42.R7.)P,(2=.$42.R8.R11.(2>.R12.+50.))P,Pa,$8.P,(2:.(64.R8.R1.))(16.(28.(12.R14.R2.)(29.R2.(2>.R15.+50.)))(28.(<.$1;.(1<.R>.)$3=.)(28.(12.(3>.R>.)R2.)(29.R2.(17.(3>.R>.)(3?.+4.(14.R>.)))))))P,(40.R8.+5<?:8.+8.)P,(40.R9.(19.R1:.)+10.)P,P,(<.$1;.(1<.R10.)$3=.)(40.R;.(3>.R11.)(3?.+4.(14.R11.)))P,(1:.$42.R=.R12.R<.)P,(<.$8.(19.R=.)(19.R11.))P,(<.$1;.(1<.R>.)(1<.R12.))P,(<.$8.(3>.R?.)(3>.R13.))P,(<.$8.(14.R10.)(14.R14.))(4?.R23.R22.R21.R1?.R1>.R1<.R1;.R1:.R19.R18.R17.R16.R11.R12.R13.)")
(* [comment removed for export] *).
  Proof.
    intros until W. intros CTX STATE MU WM MI' ST' HW DMC DY DYL MAE' EA' EO' EP' EN'. dyctx CTX. unfold ECP_DERIVE_Y_STACK in SLO. dystate STATE.
    pose proof alloc_ceiling_pos as ACP.
    flat constr:((dy_E_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE)) 5%nat. intros _ _ _ BLE _.
    assert (BE : mpd_blk dE' = mpd_blk dEk) by (unfold mpd_blk; rewrite EO', EP', EN'; reflexivity).
    unfold dy_state. refine (conj _ (conj _ (conj PADk (conj _ (conj _ _))))).
    - eapply (jst_munch usegs L HI DIMG); [exact STk| exact HH| lia| exact MU| exact WM| exact MI'| exact ST'| | exact DMC| exact ACL| lia| exact DHI| exact HTOP| exact MC2].
      intros a NO. destruct (HW a NO) as [X|[OE X]]; [left; exact X| right]. flat constr:((BLE OE)) 6%nat. intros IN _ _ _ NIN _.
      exists (md_p dEk), (4 * md_n dEk). exact (conj IN (conj NIN X)).
    - refine (conj _ (conj EY (conj NSY FRY))). eapply mpd_at_munch_any; [exact MY| exact MU| exact WM| rewrite EY; exact DY|].
      intros NN. destruct (md_own dYk) eqn:OY; [exfalso; exact (NN eq_refl)| exact (DYL eq_refl)| exfalso; exact (NSY eq_refl)].
    - refine (conj MAE' (conj (eq_trans EA' EE) (conj _ _))); [rewrite EO'; exact NSE| rewrite BE; exact FRE].
    - rewrite BE. exact COVk.
    - rewrite EO', EP', EN'. exact DISk.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L30615961706.73L44187194279.74L48736977073.72L51163419001.72L59308546259.66L59308546259.68L8929561634.73 00000=00L00`00m01601A01US1g2SP2N13PB1S1L1g2SP3PB12R1S1g2SP3PHL2N12P03PB1S1g2SP2N13PB1S1g2SP2PVS2SP1b1l2N0S1g2SP3PHL2N12P03PB1". (* [comment removed for export] *)
  Lemma dy_P_static : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)PSP,$8.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.P,(4>.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(28.(65.$42.R3.R;.(?.R7.))(28.(<.$8.(19.(?.R7.))(17.R8.+8.))(28.(<.$1;.(1<.(?.R7.))$50.)(28.(12.+1.(14.(?.R7.)))(28.(29.=(3>.(?.R7.)))(28.(12.(55.VL,)(3>.(?.R7.)))(12.(17.(3>.(?.R7.))(3?.+4.(14.(?.R7.))))(56.VL,))))))))")
(* [comment removed for export] *).
  Proof.
    intros until mo. intros CTX. dyctx CTX.
    flat constr:(GR) 9%nat. intros _ _ _ EP _ _ _ MP _.
    assert (POWN : md_own (g_P g) <> LHeap) by (apply (grp_static_own usegs MT m LB G g _ GR H1); cbn; auto).
    flat constr:(MP) 6%nat. intros _ _ _ PHL PHN PHO. unfold MPI_MAX_LIMBS in PHN.
    assert (PNN : md_own (g_P g) <> LNull).
    { intros O. rewrite O in PHO. flat constr:(PHO) 2%nat. flclear PHO. intros _ N0. unfold mpd_val in PV. rewrite <- PHL in N0.
      destruct (md_limbs (g_P g)); [cbn in PV; lia| cbn in N0; lia]. }
    destruct (md_own (g_P g)) eqn:OP; [exfalso; exact (PNN eq_refl)| exfalso; exact (POWN eq_refl)|].
    flat constr:(PHO) 5%nat. flclear PHO. intros N1 _ P0 PB PRO. flat constr:(PB) 3%nat. intros PB0 PB1 _. rewrite u32s_length in PB1.
    pose proof (ROIMG _ (PRO 0 ltac:(lia)) ltac:(lia)) as R0. rewrite Z.add_0_r in R0.
    pose proof (ROIMG _ (PRO (4 * md_n (g_P g) - 1) ltac:(lia)) ltac:(lia)) as R1.
    refine (conj MP (conj EP (conj eq_refl (conj N1 (conj P0 (conj (proj1 R0) _)))))). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L10081841430.110L10312886093.110L10882680213.113L12105755325.112L13642019862.110L15466341142.110L22706553362.114L26281077033.112L3820768330.112 L41596053933.7  L46225601430.110L49786828438.110L51189831868.7  L51601712534.110L54391891673.115L54613153071.114L6503841302.110 L66649203857.11300000500:00?00D00I00N00o01K01Y01h01m02202?02D03V03l04104GS3spvS3spvS3spvS3spvS3spvS3spvS1L4DIMG4IMGC3spv2lo3ACL3SPB1a2HaS1L4DIMG4IMGC3spv2lo3MC23ACLS1L3spv2lo3ACLS3spv2dX2lo3SXSS3spvS3spvS3spv1G2lo2GSS3spvS1L2HI3HLS4DIMG4IMGC3spv1h2dX1G2lo2GS2GX3SXS3MC23MCX3MCG3SLO3ACL4HTOP3DHI3SPB1a2NOS1L3HLS3spv2lo3SLO3SPBS3spvS1L3HLS3spv2lo3SLO3SPB". (* [comment removed for export] *)
  Lemma dy_exit_prefix : ltac2:(CDefT.buildp (gd_tbl_P_ecp_derive_y ()) "Prae,(0.&40.)Pspv,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0e,(0.&40.)Ps1e,(0.&40.)Ps2e,(0.&40.)Ps3e,(0.&40.)Ps4e,(0.&40.)Ps5e,(0.&40.)Ps6e,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pra0,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0c,(0.&40.)Ps1c,(0.&40.)Ps2c,(0.&40.)Ps4c,(0.&40.)Ps5c,(0.&40.)Ps6c,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$42.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)Plo,$8.Pm1,P,(0.&40.)(2.(0.&8.))Pj16,(5.(0.&8.))Pr,$8.P,(4>.R;.R:.R9.R8.R7.R6.R5.(18.&40.R34.)R4.R=.R<.)P,(62.(22.(4<.$8.$8.)(4=.$8.$8.R5.(18.&40.R35.))(25.(4<.$8.$8.)))R>.R4.)P,(63.$42.R?.R5.)P,(34.$42.R6.)P,(2=.$42.R7.R8.(17.(18.&40.R38.)-50.))P,(21.$42.R8.(17.(18.&40.R39.)-40.)(57.R30.R31.R32.R33.R34.R35.R36.R3:.))P,(21.$42.R9.(17.(18.&40.R3:.)-50.)(22.$23.(66.#10.R8.)(25.$23.)))P,(28.(29.(58.(45.+2.+1?.))R8.)(12.R8.=))(37.$42.R14.(38.$42.VL,VHI,VMT,R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R17.R16.R13.R12.R11.R?.R>.+5<?:8.R<.R15.R14.)(39.(3:.R2=.(32.&40.(17.(18.&40.R3<.)-50.))R3;.R3:.R2<.R2;.R2:.R29.R28.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R27.(32.&40.R9.)R26.R25.R24.R32.R31.R30.R2?.R2>.R1;.R1:.R19.R18.)R17.(32.&40.+38:=4.)R16.(3;.(0.&40.))R;.(3<.$42.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros CTX MU WM MI1 ST1 FR CE Hr. dyctx CTX. unfold ECP_DERIVE_Y_STACK in SLO. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    unfold dy_regs in FR.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame CE ST1 (bv_unsigned spv + -64). release_frame FR ST1 (bv_unsigned spv). zstep.
    apply aevtM_done. unfold ecp_mul_mod_post.
    flexi 14%nat. exists m1, mo, h, LB, dX, r, cnt.
    split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [apply mo_frame_refl|]. split; [reflexivity|].
    split; [exact HH1|].
    split. { eapply mpd_at_munch_any; [exact MX0| exact MU| exact WM| cbn; clear - SXS SLO HLS; lia| intros NN; exfalso; exact (NN YNULL)]. }
    split; [apply mpd_out_refl; rewrite YNULL; discriminate|].
    split; [eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia]|].
    split; [eapply statics_ok_munch; [exact SOK| exact MU| intros a Ha _; cbn; lia]|].
    split. { eapply ecp_group_at_munch; [exact GR| exact MU| exact WM| exact MI| exact MI1| cbn; clear - GS SLO HLS; lia| intros d Hd O; exfalso; exact (grp_static_own usegs MT m LB G g d GR H1 Hd O)]. }
    split; [eapply rw_cells_transport; [exact CNT| exact MU| exact WM| cbn; lia]|].
    unfold mul_mod_R, binop_keep. refine (conj Hr (conj eq_refl (conj eq_refl (conj (fun b Hb => or_introl Hb) (Z.le_refl _))))).
  all: match goal with |- ?gg => idtac "EXITLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "02P0@L10362473449.7  L10472341635.258L11151000370.139L11157354021.7  L11797343396.265L11803370785.166L13850755390.307L1386329760.208 L14478075398.176L14494349489.367L15302269400.112L15649522357.303L18168128297.217L18168128297.267L18168128297.376L18168128297.479L19120302066.133L19427582228.115L19427582228.116L19654080648.375L21234244481.281L22446743512.112L22700267513.168L23186948667.468L246859936.479  L246903960.264  L24893608408.337L24893611075.229L24893611202.439L24895706952.278L24895706962.176L25069796106.10 L25214214772.112L25927109588.376L26008470477.162L26056220046.278L26056220052.176L26058315268.439L26058315397.229L26058316574.337L26058334103.197L26058334103.249L26058334103.357L26058334103.459L26071109682.299L27918425841.304L28334457422.281L28692136132.98 L29960585849.176L30830416925.138L30830417310.156L31225147636.112L33538680625.305L34068178996.412L34222387378.166L34705680216.112L36253174249.7  L36665072493.304L37246946676.111L38239027073.479L38368416584.479L38815271403.306L39135598946.306L3949578456.111 L40097111318.307L40147641242.374L40147641242.477L40371893116.278L40371893188.163L40372270147.474L40372270150.371L40373990892.337L40373994178.412L40374058619.162L40374333670.114L40378085729.303L40378220765.214L40378221405.264L40378399297.263L40378399302.213L40378446787.373L40378446797.476L41035589536.309L41592269748.177L41595988036.121L41596052393.7  L41596053933.7  L41598145928.7  L41843875160.112L41845779521.117L43024876844.479L43059266230.112L43782035707.99 L44481088716.166L44622288685.118L44622288685.119L45364820406.299L45401647669.366L48706202066.161L48708298345.163L48967152873.7  L49283344500.112L49698585326.118L49698585326.119L50576412459.303L51454941784.112L52037457335.258L52494493908.414L52513751947.139L5285469359.118 L5285469359.119 L52874768535.306L53094286011.376L53519010091.120L53519010091.393L5409152198.7   L54993126469.2  L55310518004.112L58162192221.374L58162192221.477L58228918065.158L58591023192.112L59115904765.478L59308546259.308L59308546259.309L59308628695.1  L59427867805.151L59676320424.306L59760628363.303L60383089909.337L60383091054.229L60383091183.439L60385186031.9  L60385186431.176L61274378192.479L61274419819.420L61274420200.264L61321319284.112L62556561968.208L62873783018.305L63261865030.7  L63261865686.176L63829069812.112L63887036889.374L63887036889.477L64312278294.7  L65502165646.98 L66239780239.7  L67264718639.7  L67280348888.112L67351568884.112L67541566890.113L67541566890.114L68410171293.376L6936295055.178 L756327381.307  L7860843775.278 L8469177472.7   L8548517535.308 L8548517535.309 00000=00>00B00Z00a00e01>01?01K01L01P02F02O02[03703V03`04U05\06>06h06l08208L08f08m09D09K09e09o0:30:W0:[0;N0;c0<P0=70>40>^0?X0@?0@i0Ac0B`0CZ0D10DR0Dg0E40E80E<0E@0E^0F80F<0F@0FM0GG0GK0HA0Ha0I?0J30J70JT0K>0Kk0L50L90LS0Lj0MA0M[0M_0Mc0N:0N>0NE0NL0NP0Ng0OA0O^0Oj0PF0PT0P`0Pm0Q10Q50QY0Qn0R60R=0S20T90TP0Tg0UN0V50VB0VF0V`0WL0Wk0Wo0X60XV0XZ0Y00YX0ZG0Zh0Zl0[F0[R0[Z0[^0\?0\c0\g0\k0]P0]o0^N0^R0^\0_;0_R0`50`H0`n0`o0a?0aY0b30b:0b>0bB0b_0bk0cV0cZ0d60dU0dY0d]0e50eJ0eN0eR0ej0fB0f_0fc0gR0g_0gc0hB0haS1L2sp2lo3SLOFS2spS1L3HLS2sp2dX2lo3SLO3SXSS2sp2r2S2spS2sp2r23dE32r33xs44LEN41HFS2sp1G2lo2GSFS2spS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL2r23dE32r33xs44LEN4S2sp1a2HaS2sp2r21a2HaS2sp2r23dE32r33xs44LEN41a2HaS2sp2r23dE32r33xs44LEN42r51a2HaS2sp2r02R0S1L3HLS4DIMG4IMGC2ra2sp2lo3MC23SLO3ACL2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2sp2s02lo3MC23SLO3ACL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp3SPB3dY22r23dE32r33xs44LEN42N1S1L3HLS2sp2lo3SLO3ACL3SPB2r23dE32r33EE32B4S2spS1L3HLS4DIMG4IMGC2sp2dX1G2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB3SXS1x1HS2sp2r23dE32r33xs44LEN42r5S2sp2r23dE32r33xs44LEN42r5S2sp2r2S2sp2r23dE32r33xs44LEN4S2sp2r2S2sp2r23dE32r33xs44LEN42r5S2sp2r22r3S2spS1L3HLS2sp2dX2lo3MC23SLO3ACL3DHI3SXSS2spS1L3HLS2sp2lo3SLO3ACL3SPB3dY22r23dE32r33xs44LEN42B4S1L3HLS2sp2lo3SLO3SPBS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB2r22r3S1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPBS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB2r23dE32r33xs44LEN42r5S1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB2r2S1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB2r23dE32r33xs44LEN4S1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPBS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB2r2S1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB2r23dE32r33xs44LEN4S1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB2r23dE32r33xs44LEN42r5S1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB2r23dE32r33xs44LEN4S2sp2r23dE32r33xs44LEN4S1L2sp2lo3ACL3SPB2r23dE32r32P02B4S1L3HLS2sp2lo3SLO3SPBS1L2sp2lo3SLOS2spS2spS2spS2sp2r23dE32r33xs44LEN41A1n2HAS2sp2r23dE32r33xs44LEN42r5S2spS2spS1L2sp2lo3SLOS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPB2r23dE32r33xs44LEN4S2spS1L3HLS2sp2lo3SLO3ACL3SPB2r23dE32r33xs44LEN43dY52r52B4S2sp2r23dE32r33xs44LEN43dY52r51HS2sp3SPB2r23dE32r33xs44LEN42N1S1L3HLS2sp2lo3SLO3ACL3SPB3dY22r23dE32r33xs44LEN43BY4S2spS2sp2r23dE32r33xs44LEN41A1n1HS1L2sp3MC13MC23SPB2r23dE32r33xs44LEN41a2HaS1L2sp3MC13MC23SPB2r23dE32r33xs44LEN42r51a2HaS2sp2r22r3S2spS2sp2r23dE32r33xs44LEN42r5S2sp2r23dE32r33xs44LEN4S2sp2r23dE32r33xs44LEN4S2sp2r23dE32r33xs44LEN42r5S2spS2spS2sp2r23dE32r33xs44LEN4S2spS2sp2r2S2sp2r2S2spS2sp2r23dE32r33xs44LEN4S2sp2r23dE32r33xs44LEN42r5S2sp3dY22r23dE32r33xs44LEN41HS2sp2dA2lo1HS1L4IMGC2sp1g2lo3ACL3SPB3PR1S2sp2dX2lo3SXSS2sp1G2lo2GSS2sp2dA2lo2S4S2spS2spS2sp2r23dE32r33xs44LEN43dY52r51A1n1HS1L3HLS2sp2lo3SLO3SPBS2sp3SPBS2sp2loS1L3HLS4DIMG4IMGC2ra2sp2lo3SLO3ACL3SPB2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2sp2s02lo3SLO3ACL3SPB2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp2r23dE32r33xs44LEN4S2sp2r23dE32r33xs44LEN4S1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPBS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPBS1L2sp2lo3SLOS2spS2ra2sp3SPB2HB5Ha_st5Hl_stS2sp2s03SPB2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp2dX2r23dE32r33xs44LEN44YPOSS2spS2sp2r2S2sp2r23dE32r33xs44LEN42r52r62R6S2spS2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_st2s12s22s32s42s52s6S1L3HLS2sp2lo3SLO3ACL3SPB2r23dE32r33xs44LEN42B4S2sp3dY22r23dE32r33xs44LEN41A1n1HS2spS2sp2r23dE32r33xs44LEN42r5S2sp3SPA3SPBS2dX3MCXS2spS2sp2dX2r23dE32r33xs44LEN41A1n2D1S2sp2dX2r23dE32r33xs44LEN42r51A1n2D1S2spS2spS2sp3SPB2r23dE32r33xs44LEN43dY52r52N1S2sp2r23dE32r33xs44LEN41a2NO2GES2sp2r23dE32r33xs44LEN41a2NO2g0S2K4S2sp2r12R1S2sp3dY22r23dE32r33xs44LEN43PY0S2sp2r23dE32r33xs44LEN4S1L2HI2sp1h4HTOP2r23dE32r33xs44LEN4S1L2HI2sp1h4HTOP2r2S1L2HI2sp1h4HTOP2r23dE32r33xs44LEN42r5FS1L2HI2sp1h4HTOPS2sp2r23dE32r33xs44LEN42r5S2sp2r23dE32r33xs44LEN42r5S2sp2r2S2spS2spS2sp2dX2r23dE32r33xs44LEN42APS2sp3SPA3SPBS1L3HLS4DIMG4IMGC2sp2lo3MC23SLO3ACL3SPA3SPBS2spS2sp2r23dE32r33xs44LEN41a2HaS2sp2r23dE32r33xs44LEN42r51a2HaS2spS2spS1L3HLS2sp2dX2lo3SLO3SXSS1L3HLS2sp2lo3SLO3SPBS2spS2spS1L3HLS2sp2lo3SLO3SPB2HBS1L3HLS2sp2lo3SLO3SPB2HBS2sp3dY22r23dE32r33xs44LEN41HS2spS1L3HLS2sp2lo3SLO3SPB2r23dE32r33xs44LEN41a2LT1lS2sp2lo2r22r3S2spS2sp2r23dE32r33xs44LEN41a2NO2GES2sp2r23dE32r33xs44LEN41a2NO2g0". (* [comment removed for export] *)
  Theorem U_ecp_derive_y_spec : ecp_derive_y_stmt usegs L HI MT U_ECP_DERIVE_Y U_MEMSET_FUNC U_MUL_COUNT ECP_DERIVE_Y_STACK.
  Proof.
    unfold ecp_derive_y_stmt, U_ECP_DERIVE_Y. intros until lo.
    intros HH GR H1 GPS GAS GBS PV PN49 GCR GS GX MX0 YNULL XW MXA EXT CNT MC1 MC2 MCS MCX MCG ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    pose proof SLO as SLO0. unfold ECP_DERIVE_Y_STACK in SLO.
    assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
    flat constr:(XW) 3%nat. intros XCW XD XP.
    pose proof (client_wrange_where2 L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as SXS.
    assert (CTX : dy_ctx h LB dX dA G g cnt (bv_unsigned sp) lo m mo).
    { unfold dy_ctx. (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption; try lia. }
    flat constr:((dy_P_static _ _ _ _ _ _ _ _ _ _ _ CTX)) 7%nat. intros MP EP OP PN1 PP0 PR0 PR1.
    (* [comment removed for export] *)
    pose proof (lock MI) as MI00. pose proof (lock HH) as HH00. pose proof (lock SOK) as SOK00. pose proof (lock CNT) as CNT00.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM. clear HH.
    carve_frame 80%nat ST. set (JJ := junk) in FR. clearbody JJ.
    pose proof GR as (GHD0 & GAL0 & _). pose proof (rw_cells_bound _ _ _ _ GHD0) as GB0. unfold grp_head_cells in GB0. cbn [cells_size csize Nat.add] in GB0. clear GHD0.
    do 10 zstep. zstep. zstep. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; rewrite ?land_7_mod in KA; lia|].
    do 4 zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    flat constr:((proj1 (rw_cells_app usegs _ _ [CB 16 _] _) FR)) 2%nat. intros CE FR'. clear FR. cbn [cells_size csize Nat.add] in FR'.
    match type of FR' with rw_cells _ _ ?aa _ => replace aa with (bv_unsigned sp + -64) in FR' by lia end.
    change (rw_cells usegs m1 (bv_unsigned sp + -64) (dy_regs s6 s5 s4 s3 s2 s1 s0 ra)) in FR'. rename FR' into FR.
    lazymatch type of CE with rw_cells _ _ _ [CB 16 ?j] => set (j16 := j) in CE end. clearbody j16.
    Ltac carryP FR CE MUc WMc := eapply rw_cells_transport in FR; [| exact MUc| exact WMc| cbn; try exact I; lia]; eapply rw_cells_transport in CE; [| exact MUc| exact WMc| cbn; try exact I; lia].
    (* [comment removed for export] *)
    assert (MP1 : forall mx, munch [(lo, bv_unsigned sp)] m mx -> wmono usegs m mx -> mpd_at usegs mx LB (g_P g)).
    { intros mx MUx WMx. eapply mpd_at_munch_any; [exact (conj MP (or_introl GPS))| exact MUx| exact WMx| rewrite EP; cbn; clear - GS SLO HLS; lia| intros _; cbn; lia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof HGETBIT as SG. unfold mpi_get_bit_stmt in SG.
    eapply aevtM_cut_evt; [exact MK| eapply SG with (LB := LB) (dX := g_P g) (pos := 0); [exact (MP1 _ MU WM)| rewrite OP; intros; discriminate| assumption| lia| rewrite EP; reflexivity| reflexivity] |].
    clear SG. cbv beta. intros ms' PO. unfold mpi_query_post in PO. flat constr:(PO) 21%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m1a r0 -> MUa WMa MIa R0.
    replace (ret_pc (Z_to_bv 64 0x38a28)) with (Z_to_bv 64 0x38a28) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    carryP FR CE MUa WMa. eapply (stk_transport_disjoint usegs) in ST; [| exact MUa| exact WMa| cbn; exact I].
    assert (MU' : munch [(lo, bv_unsigned sp)] m m1a) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUa]; unfold sub_fp; cbn; intros; exact I]).
    pose proof (wmono_trans _ _ _ _ WM WMa) as WM'. clear MU WM MUa WMa. rename MU' into MU. rename WM' into WM.
    zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0.
    { eapply dy_exit_prefix; [exact CTX| exact MU| exact WM| exact MIa| exact ST| exact FR| exact CE| lia]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof HGETBIT as SG. unfold mpi_get_bit_stmt in SG.
    eapply aevtM_cut_evt; [exact MK| eapply SG with (LB := LB) (dX := g_P g) (pos := 1); [exact (MP1 _ MU WM)| rewrite OP; intros; discriminate| exact MIa| lia| rewrite EP; reflexivity| reflexivity] |].
    clear SG. cbv beta. intros ms' PO. unfold mpi_query_post in PO. flat constr:(PO) 21%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m1b r1 -> MUa WMa MIb R1.
    replace (ret_pc (Z_to_bv 64 0x38a44)) with (Z_to_bv 64 0x38a44) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    carryP FR CE MUa WMa. eapply (stk_transport_disjoint usegs) in ST; [| exact MUa| exact WMa| cbn; exact I].
    assert (MU' : munch [(lo, bv_unsigned sp)] m m1b) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUa]; unfold sub_fp; cbn; intros; exact I]).
    pose proof (wmono_trans _ _ _ _ WM WMa) as WM'. clear MU WM MUa WMa MIa. rename MU' into MU. rename WM' into WM.
    zstep. if_cases K1; zify_cond K1.
    { eapply dy_exit_prefix; [exact CTX| exact MU| exact WM| exact MIb| exact ST| exact FR| exact CE| lia]. }
    (* [comment removed for export] *)
    apply mpi_cells_of_bytes in CE.
    set (pe0 := bv_unsigned (wof (firstn 8 j16))) in CE. set (se0 := wof (firstn 2 (skipn 8 j16))) in CE. set (ne0 := bv_unsigned (wof _)) in CE. set (padE := wof (skipn 12 j16)) in CE.
    clearbody pe0 se0 ne0 padE.
    zstep. zstep.
    pose proof HINIT as SI. unfold mpi_init_stmt in SI.
    eapply aevtM_cut_evt; [exact MK| eapply SI with (X := bv_unsigned sp + -80); [exact CE| clear - SPA SPB SLO HLS; lia| lia| exact MIb| reflexivity] |].
    clear SI. cbv beta. intros ms' PO. unfold mpi_init_post in PO. flat constr:(PO) 7%nat. flclear PO. intros ? m0 -> MUa WMa MI0 CE0.
    replace (ret_pc (Z_to_bv 64 0x38a50)) with (Z_to_bv 64 0x38a50) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rw_cells_transport in FR; [| exact MUa| exact WMa| cbn; lia]. eapply (stk_transport_disjoint usegs) in ST; [| exact MUa| exact WMa| cbn; lia].
    assert (MU' : munch [(lo, bv_unsigned sp)] m m0) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUa]; unfold sub_fp; cbn; intros; lia]).
    pose proof (wmono_trans _ _ _ _ WM WMa) as WM'. clear MU WM MUa WMa MIb CE. rename MU' into MU. rename WM' into WM.
    (* [comment removed for export] *)
    assert (ST0 : jst usegs L HI h LB (bv_unsigned sp) 80 (dy_XO dX) U_MUL_COUNT lo m mo h LB m0 mo).
    { eapply (jst_prefix usegs L HI); [exact (unlock _ HH00)| exact MU| exact WM| exact MI0| exact (unlock _ SOK00)| exact (unlock _ CNT00)| exact MC2| exact DHI| exact ACL| lia| exact HTOP| replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; exact ST]. }
    assert (STATE0 : dy_state h LB dX G g (bv_unsigned sp) lo m mo h LB dX (mpd_init (bv_unsigned sp + -80) padE) m0 mo).
    { unfold dy_state. refine (conj ST0 (conj _ (conj eq_refl (conj _ (conj (fun b Hb => or_introl Hb) _))))).
      - split; [| split; [reflexivity| split; [rewrite YNULL; discriminate| unfold mpd_blk; rewrite YNULL; intros b []]]].
        eapply mpd_at_munch_any; [exact MX0| exact MU| exact WM| cbn; clear - SXS SLO HLS; lia| intros NN; exfalso; exact (NN YNULL)].
      - split; [split; [apply mpdr_at_init; [exact CE0| clear - SPA SPB SLO HLS; lia| lia]| left; reflexivity]|]. split; [cbn; lia|]. split; [cbn; discriminate|]. cbn. tauto.
      - rewrite YNULL. intros; discriminate. }
    flat constr:(ST0) 9%nat. intros HH0 _ _ SOK0 _ _ _ (c0 & CNT0) ST0'.
    flat constr:((dy_Y_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE0)) 6%nat. intros MY0 NSY0 _ YW0 XSL0 _.
    assert (MEX0 : mpd_at usegs m0 LB dA).
    { flat constr:(EXT) 3%nat. intros _ FLt3 _. flat constr:(FLt3) 5%nat. flclear FLt3. intros _ _ _ S4 S5. eapply mpd_at_munch_any; [exact MXA| exact MU| exact WM| cbn; clear - S4 SLO HLS; lia| intros NN; pose proof (S5 NN); cbn; lia]. }
    assert (EXT0 : ext_opnd L LB dX dA U_MUL_COUNT (bv_unsigned sp + -80) lo).
    { flat constr:(EXT) 5%nat. flclear EXT. intros E1 E2 E3 E4 E5. refine (conj E1 (conj _ (conj E3 (conj E4 E5)))). eapply opnd_sep_sp_mono; [exact E2| lia]. }
    clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    pose proof HSR as SSR. unfold ecp_sw_rhs_stmt in SSR.
    eapply aevtM_cut.
    { eapply SSR with (lo := lo) (h := h) (LB := LB) (dX := dX) (dA := dA) (G := G) (g := g) (cnt := c0);
        rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by lia;
        first [ exact HH0 | exact H1 | exact GPS | exact GAS | exact GBS | exact PV | exact GCR | exact MY0 | exact NSY0 | exact YW0 | exact XSL0 | exact MEX0 | exact EXT0
              | exact CNT0 | exact MC1 | exact MC2 | exact MCS | exact MCX | exact MCG | exact TP | exact SOK0 | exact CA | exact MI0 | exact ACL | exact DHI | exact GX
              | reflexivity
              | match goal with |- ecp_group_at _ _ _ _ _ _ => exact (dy_GR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE0) end
              | match goal with |- stk _ _ _ _ => replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; exact ST0' end
              | rewrite YNULL; intros; discriminate
              | unfold ECP_SW_RHS_STACK; lia
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SSR. cbv beta. intros ms' mo' PO. unfold ecp_mul_mod_post in PO.
    flat constr:(PO) 23%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 LB2 dY2 r2 cnt2 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by lia.
    flat constr:(PO) 12%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 GR2 CNT2 RR2.
    replace (ret_pc (Z_to_bv 64 0x38a60)) with (Z_to_bv 64 0x38a60) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR2) 2%nat. intros Hr2 FLt4. flat constr:(FLt4) 4%nat. flclear FLt4. intros EA2 PAD2 FRB2 NLE2.
    assert (PX2' : heap_presx usegs L LB (bv_unsigned sp - 80) (mpd_ivs dX ++ [(U_MUL_COUNT, U_MUL_COUNT + 8)]) m0 m2).
    { replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia. exact PX2. }
    assert (STATE2 : dy_state h LB dX G g (bv_unsigned sp) lo m mo h2 LB2 dY2 (mpd_init (bv_unsigned sp + -80) padE) m2 mo2).
    { eapply dy_Ystep; [exact CTX| exact STATE0| right; reflexivity| exact HH2| exact MA2| exact OUT2| exact FRB2| exact PAD2| exact PX2'| exact SOK2| exact MI2| exact MF2| exact HT2| exists cnt2; exact CNT2| replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; exact ST2]. }
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (dy_regs s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply heap_presx_rw_cells; [exact PX2| exact FR| cbn; intros a Ha; left; lia|]. unfold mpd_ivs. rewrite YNULL. cbn. clear - SXS SLO HLS MC2 DHI ACL. lia. }
    clear MK FR PX2 PX2' ST. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    zstep. if_cases K2; zify_cond K2.
    { zstep. eapply dy_fin; [exact CTX| exact STATE2| exact FR2| exact TP| exact Hr2]. }
    (* [comment removed for export] *)
    flat constr:(STATE2) 2%nat. intros STj2 _. flat constr:(STj2) 9%nat. intros _ _ _ _ _ _ HTj2 _ STk2.
    flat constr:((dy_E_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE2)) 12%nat. intros ME2 EE2 NSE2 BLE2 _ _ _ _ _ EW2 ESL2 _.
    flat constr:((dy_P_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE2)) 9%nat. intros MP2 _ _ _ _ _ _ _ CRP2.
    flat constr:((dy_P_sep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE2)) 7%nat. intros _ _ _ SEP2 OEP2 CRPL2 PP2.
    zstep. zstep. zstep. zstep.
    pose proof HADDI as SA. unfold mpi_add_int_stmt, mpi_intop_stmt in SA.
    eapply aevtM_cut.
    { eapply SA with (lo := lo) (h := h2) (LB := LB2) (dX := mpd_init (bv_unsigned sp + -80) padE) (dA := g_P g) (b := 1);
        rewrite ?(unsigned_lit (bv_unsigned sp + -80)), ?HTj2 by lia;
        first [ exact HH2 | exact ME2 | exact MP2 | exact SEP2 | exact NSE2 | exact OEP2 | exact CRP2 | exact CRPL2 | exact EW2 | exact ESL2 | exact TP | exact SOK2 | exact CA | exact MI2 | exact ACL | exact DHI
              | reflexivity | rewrite EP; reflexivity
              | match goal with |- stk _ _ _ _ => replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; exact STk2 end
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SA. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 mo3 h3 LB3 dE3 r3 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR3.
    replace (ret_pc (Z_to_bv 64 0x38a74)) with (Z_to_bv 64 0x38a74) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR3) 2%nat. intros RV3 FLt5. flat constr:(FLt5) 4%nat. flclear FLt5. intros EA3 PAD3 FRB3 NLE3.
    assert (PX3' : heap_presx usegs L LB2 (bv_unsigned sp - 80) (mpd_ivs (mpd_init (bv_unsigned sp + -80) padE)) m2 m3).
    { replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia. exact PX3. }
    assert (STATE3 : dy_state h LB dX G g (bv_unsigned sp) lo m mo h3 LB3 dY2 dE3 m3 mo3).
    { eapply dy_Estep; [exact CTX| exact STATE2| exact HH3| exact MA3| exact OUT3| exact FRB3| exact PX3'| exact SOK3| exact MI3| exact MF3| exact HT3| replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; exact ST3]. }
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (dy_regs s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply heap_presx_rw_cells; [exact PX3| exact FR2| cbn; intros a Ha; left; lia|]. unfold mpd_ivs. cbn. lia. }
    clear MK FR2 PX3 PX3'. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
    zstep. if_cases K3; zify_cond K3.
    { zstep. eapply dy_fin; [exact CTX| exact STATE3| exact FR3| exact TP| destruct RV3 as [(Er & _)|Er]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia]. }
    (* [comment removed for export] *)
    flat constr:(STATE3) 2%nat. intros STj3 _. flat constr:(STj3) 9%nat. intros _ SUBk3 _ _ _ _ HTj3 _ STk3.
    flat constr:((dy_E_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE3)) 5%nat. intros ME3 EE3 NSE3 BLE3 _.
    flat constr:((dy_Y_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE3)) 7%nat. intros MY3 NSY3 EY3 _ XSL3 BLY3 _.
    zstep. zstep. zstep.
    pose proof HSHR as SSH. unfold mpi_shift_r_stmt in SSH.
    eapply aevtM_cut_evt; [exact MK| eapply SSH with (LB := LB3) (dX := dE3) (count := 2) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by lia;
      first [ exact ME3 | exact NSE3 | exact MI3 | reflexivity
            | match goal with |- stk _ _ _ _ => replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; exact STk3 end
            | rewrite EE3; apply f_equal; lia
            | intros O; (flat constr:((BLE3 O)) 5%nat; intros _ _ P0 B4 _); lia
            | rewrite EE3; lia
            | clear - SPA SPB SLO HLS; lia
            | lia ] |].
    clear SSH. cbv beta. intros ms' PO. unfold mpi_shift_r_post in PO.
    flat constr:(PO) 24%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m4 xs4 -> MU4 WM4 MI4 ST4 MA4 LEN4 _.
    rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in MU4, ST4 by lia.
    replace (ret_pc (Z_to_bv 64 0x38a84)) with (Z_to_bv 64 0x38a84) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    set (dE4 := mkMPD (md_addr dE3) (md_sg dE3) (md_n dE3) (md_p dE3) xs4 (md_pad dE3) (md_own dE3)) in MA4.
    flat constr:((proj1 ME3)) 6%nat. intros _ _ _ _ _ HOE3.
    assert (EIV : forall A n, 0 <= A -> (md_own dE3 = LHeap -> md_p dE3 + 4 * md_n dE3 <= A \/ A + n <= md_p dE3) -> A + n <= md_p dE3 \/ md_p dE3 + 4 * md_n dE3 <= A).
    { intros A n HA D. destruct (md_own dE3) eqn:O; [(flat constr:(HOE3) 2%nat; flclear HOE3; intros -> ->); lia| pose proof (D eq_refl); lia| exfalso; exact (NSE3 eq_refl)]. }
    flat constr:((proj1 MY3)) 4%nat. intros _ _ YPOS _. rewrite EY3 in YPOS.
    assert (STATE4 : dy_state h LB dX G g (bv_unsigned sp) lo m mo h3 LB3 dY2 dE4 m4 mo3).
    { eapply dy_munch; [exact CTX| exact STATE3| exact MU4| exact WM4| exact MI4| replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; exact ST4| | | | | exact MA4| reflexivity| reflexivity| reflexivity| reflexivity].
      - intros a NO. cbn in NO. destruct (Z_lt_le_dec a (bv_unsigned sp + -80)) as [LT|GE]; [destruct (Z_le_gt_dec (bv_unsigned sp + -80 - 48) a); [left; lia|]|];
          (destruct (md_own dE3) eqn:O; [(flat constr:(HOE3) 2%nat; flclear HOE3; intros P0 N0); rewrite P0, N0 in NO; exfalso; lia| right; split; [reflexivity|]; (flat constr:((BLE3 eq_refl)) 5%nat; intros _ _ _ B4 _); lia| exfalso; exact (NSE3 eq_refl)]).
      - cbn. split; [lia|]. split; [| exact I]. apply EIV; [lia|]. intros O. flat constr:((BLE3 O)) 3%nat. intros IN N1 _. pose proof (j_blk_MC usegs L HI DIMG h3 LB3 m3 mo3 _ _ U_MUL_COUNT HH3 IN ltac:(lia) MC1 MC2). lia.
      - cbn. split; [clear - SXS SLO HLS; lia|]. split; [| exact I]. apply EIV; [lia|]. intros O. flat constr:((BLE3 O)) 7%nat. intros _ _ _ _ _ AP _. lia.
      - intros OY. cbn. flat constr:((BLY3 OY)) 5%nat. intros _ _ PY0 BY4 _. split; [lia|]. split; [| exact I]. apply EIV; [lia|]. intros O. flat constr:((BLE3 O)) 8%nat. intros _ _ _ _ _ _ _ AP. pose proof (AP OY). lia. }
    eapply rw_cells_transport in FR3; [| exact MU4| exact WM4| cbn; split; [lia|]; split; [| exact I]; apply EIV; [lia|]; intros O; (flat constr:((BLE3 O)) 5%nat; intros _ _ _ B4 _); lia].
    rename FR3 into FR4. clear MU4 WM4 ST4.
    zstep. if_cases K4; zify_cond K4; [exfalso; clear - K4; cbn in K4; lia|].
    (* [comment removed for export] *)
    flat constr:(STATE4) 2%nat. intros STj4 _. flat constr:(STj4) 9%nat. intros HHj4 SUBk4 _ SOK4 _ _ HTj4 (c4 & CNT4) STk4.
    flat constr:((dy_Y_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE4)) 10%nat. intros MY4 NSY4 EY4 YW4 XSL4 BLY4 SXX4 OXX4 CRY4 CRYL4.
    flat constr:((dy_E_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE4)) 10%nat. intros ME4 EE4 NSE4 BLE4 SYE4 NYE4 OYE4 CRE4 CREL4 _.
    flat constr:((dy_P_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE4)) 9%nat. intros MP4 _ _ _ _ _ _ _ CRP4.
    flat constr:((dy_P_sep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE4)) 7%nat. intros SYP4 NYP4 OYP4 _ _ CRPL4 PP4.
    zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof HEXP as SX. unfold mpi_exp_mod_stmt_n in SX.
    eapply aevtM_cut.
    { eapply SX with (lo := lo) (h := h3) (LB := LB3) (dX := dY2) (dA := dY2) (dE := dE4) (dN := g_P g);
        rewrite ?(unsigned_lit (bv_unsigned sp + -80)), ?HTj4 by lia;
        first [ exact HHj4 | exact MY4 | exact ME4 | exact MP4 | exact PN49 | exact SXX4 | exact SYE4 | exact SYP4 | exact NYE4 | exact NYP4 | exact NSY4 | exact OXX4 | exact OYE4 | exact OYP4
              | exact CRY4 | exact CRYL4 | exact CRE4 | exact CREL4 | exact CRP4 | exact CRPL4 | exact YW4 | exact XSL4 | exact TP | exact SOK4 | exact CA | exact MI4 | exact ACL | exact DHI
              | reflexivity | rewrite EY4; reflexivity | rewrite EE4; apply f_equal; lia | rewrite EP; reflexivity
              | match goal with |- stk _ _ _ _ => replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; exact STk4 end
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SX. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m5 mo5 h5 LB5 dY5 r5 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI5 ST5 MF5 HT5 HH5 MA5 OUT5 PX5 SOK5 RR5.
    replace (ret_pc (Z_to_bv 64 0x38aa0)) with (Z_to_bv 64 0x38aa0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold exp_mod_R in RR5. flat constr:(RR5) 2%nat. flclear RR5. intros Hr5 KP5. unfold binop_keep in KP5. flat constr:(KP5) 2%nat. flclear KP5. intros EA5 (PAD5 & (FRB5 & NLE5)).
    assert (DY2 : forall A n, (md_addr dX + 16 <= A \/ A + n <= md_addr dX) -> (md_own dY2 = LHeap -> md_p dY2 + 4 * md_n dY2 <= A \/ A + n <= md_p dY2) -> disjoint_from (mpd_ivs dY2) A n).
    { intros A n D1 D2. unfold mpd_ivs. rewrite EY4. cbn. split; [lia|]. destruct (md_own dY2) eqn:O; cbn; [exact I| | exfalso; exact (NSY4 eq_refl)]. split; [| exact I]. pose proof (D2 eq_refl). lia. }
    assert (PX5' : heap_presx usegs L LB3 (bv_unsigned sp - 80) (mpd_ivs dY2 ++ []) m4 m5).
    { rewrite app_nil_r. replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia. exact PX5. }
    assert (CNT5 : exists c, rw_cells usegs m5 U_MUL_COUNT [C8 c]).
    { exists c4. eapply heap_presx_rw_cells; [exact PX5| exact CNT4| cbn; intros a Ha; right; left; split; [lia| apply MCS; lia]|].
      cbn [cells_size csize Nat.add]. apply DY2; [clear - MCX; lia|]. intros O. flat constr:((BLY4 O)) 3%nat. intros IN N1 _. pose proof (j_blk_MC usegs L HI DIMG h3 LB3 m4 mo3 _ _ U_MUL_COUNT HHj4 IN ltac:(lia) MC1 MC2). lia. }
    assert (STATE5 : dy_state h LB dX G g (bv_unsigned sp) lo m mo h5 LB5 dY5 dE4 m5 mo5).
    { eapply dy_Ystep; [exact CTX| exact STATE4| left; reflexivity| exact HH5| exact MA5| exact OUT5| exact FRB5| exact PAD5| exact PX5'| exact SOK5| exact MI5| exact MF5| exact HT5| exact CNT5| replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; exact ST5]. }
    assert (FR5 : rw_cells usegs m5 (bv_unsigned sp + -64) (dy_regs s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply heap_presx_rw_cells; [exact PX5| exact FR4| cbn; intros a Ha; left; lia|]. cbn [cells_size csize Nat.add dy_regs]. apply DY2; [clear - SXS SLO HLS; lia|].
      intros O. flat constr:((BLY4 O)) 5%nat. intros _ _ _ B4 _. lia. }
    clear MK FR4 PX5 PX5'. pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK.
    zstep. if_cases K5; zify_cond K5.
    { zstep. eapply dy_fin; [exact CTX| exact STATE5| exact FR5| exact TP| exact Hr5]. }
    (* [comment removed for export] *)
    flat constr:(STATE5) 2%nat. intros STj5 _. flat constr:(STj5) 9%nat. intros HHj5 SUBk5 _ SOK5' _ _ HTj5 (c5 & CNT5') STk5.
    flat constr:((dy_Y_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE5)) 10%nat. intros MY5 NSY5 EY5 YW5 XSL5 BLY5 SXX5 OXX5 CRY5 CRYL5.
    flat constr:((dy_E_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE5)) 2%nat. intros ME5 _.
    zstep. zstep. zstep.
    pose proof HGETBIT as SG. unfold mpi_get_bit_stmt in SG.
    eapply aevtM_cut_evt; [exact MK| eapply SG with (LB := LB5) (dX := dY5) (pos := 0); [exact MY5| intros O; (flat constr:((BLY5 O)) 4%nat; intros _ _ P0 _); exact P0| exact MI5| lia| rewrite EY5; reflexivity| reflexivity] |].
    clear SG. cbv beta. intros ms' PO. unfold mpi_query_post in PO. flat constr:(PO) 21%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m6 r6 -> MU6 WM6 MI6 R6.
    replace (ret_pc (Z_to_bv 64 0x38ab0)) with (Z_to_bv 64 0x38ab0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (STATE6 : dy_state h LB dX G g (bv_unsigned sp) lo m mo h5 LB5 dY5 dE4 m6 mo5).
    { eapply dy_munch; [exact CTX| exact STATE5| exact MU6| exact WM6| exact MI6| | intros a NO; exfalso; exact (NO I)| cbn; exact I| cbn; exact I| intros; cbn; exact I| | reflexivity| reflexivity| reflexivity| reflexivity].
      - eapply (stk_transport_disjoint usegs); [replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; exact STk5| exact MU6| exact WM6| cbn; exact I].
      - eapply mpd_at_munch_any; [exact ME5| exact MU6| exact WM6| cbn; exact I| intros; cbn; exact I]. }
    eapply rw_cells_transport in FR5; [| exact MU6| exact WM6| cbn; exact I]. rename FR5 into FR6.
    flat constr:(STATE6) 2%nat. intros STj6 _. flat constr:(STj6) 9%nat. intros HHj6 SUBk6 _ SOK6 _ _ HTj6 (c6 & CNT6) STk6.
    clear MU6 WM6.
    zstep. zstep. if_cases K6; zify_cond K6.
    { (* [comment removed for export] *) eapply dy_fin; [exact CTX| exact STATE6| exact FR6| exact TP| lia]. }
    (* [comment removed for export] *)
    flat constr:((dy_Y_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE6)) 10%nat. intros MY6 NSY6 EY6 YW6 XSL6 BLY6 SXX6 OXX6 CRY6 CRYL6.
    flat constr:((dy_P_opnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE6)) 9%nat. intros MP6 _ _ _ _ _ _ _ CRP6.
    flat constr:((dy_P_sep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX STATE6)) 7%nat. intros SYP6 NYP6 OYP6 _ _ CRPL6 PP6.
    assert (SPY6 : mpd_sep (g_P g) dY5) by (destruct SYP6 as [E|[E|E]]; [left; symmetry; exact E| right; right; exact E| right; left; exact E]).
    zstep. zstep. zstep. zstep.
    pose proof HSUBM as SB. unfold mpi_sub_mpi_stmt, mpi_binop_stmt in SB.
    eapply aevtM_cut.
    { eapply SB with (lo := lo) (h := h5) (LB := LB5) (dX := dY5) (dA := g_P g) (dB := dY5);
        rewrite ?(unsigned_lit (bv_unsigned sp + -80)), ?HTj6 by lia;
        first [ exact HHj6 | exact MY6 | exact MP6 | exact SYP6 | exact SXX6 | exact SPY6 | exact NSY6 | exact OYP6 | exact OXX6
              | exact CRP6 | exact CRPL6 | exact CRY6 | exact CRYL6 | exact YW6 | exact XSL6 | exact TP | exact SOK6 | exact CA | exact MI6 | exact ACL | exact DHI
              | reflexivity | rewrite EY6; reflexivity | rewrite EP; reflexivity
              | match goal with |- stk _ _ _ _ => replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; exact STk6 end
              | clear - SPA SPB SLO HLS; lia
              | lia ]. }
    clear SB. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m7 mo7 h7 LB7 dY7 r7 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI7 ST7 MF7 HT7 HH7 MA7 OUT7 PX7 SOK7 RR7.
    replace (ret_pc (Z_to_bv 64 0x38ac8)) with (Z_to_bv 64 0x38ac8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR7) 2%nat. intros RV7 FLt6. flat constr:(FLt6) 4%nat. flclear FLt6. intros EA7 PAD7 FRB7 NLE7.
    assert (DY5 : forall A n, (md_addr dX + 16 <= A \/ A + n <= md_addr dX) -> (md_own dY5 = LHeap -> md_p dY5 + 4 * md_n dY5 <= A \/ A + n <= md_p dY5) -> disjoint_from (mpd_ivs dY5) A n).
    { intros A n D1 D2. unfold mpd_ivs. rewrite EY6. cbn. split; [lia|]. destruct (md_own dY5) eqn:O; cbn; [exact I| | exfalso; exact (NSY6 eq_refl)]. split; [| exact I]. pose proof (D2 eq_refl). lia. }
    assert (PX7' : heap_presx usegs L LB5 (bv_unsigned sp - 80) (mpd_ivs dY5 ++ []) m6 m7).
    { rewrite app_nil_r. replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia. exact PX7. }
    assert (CNT7 : exists c, rw_cells usegs m7 U_MUL_COUNT [C8 c]).
    { exists c6. eapply heap_presx_rw_cells; [exact PX7| exact CNT6| cbn; intros a Ha; right; left; split; [lia| apply MCS; lia]|].
      cbn [cells_size csize Nat.add]. apply DY5; [clear - MCX; lia|]. intros O. flat constr:((BLY6 O)) 3%nat. intros IN N1 _. pose proof (j_blk_MC usegs L HI DIMG h5 LB5 m6 mo5 _ _ U_MUL_COUNT HHj6 IN ltac:(lia) MC1 MC2). lia. }
    assert (STATE7 : dy_state h LB dX G g (bv_unsigned sp) lo m mo h7 LB7 dY7 dE4 m7 mo7).
    { eapply dy_Ystep; [exact CTX| exact STATE6| left; reflexivity| exact HH7| exact MA7| exact OUT7| exact FRB7| exact PAD7| exact PX7'| exact SOK7| exact MI7| exact MF7| exact HT7| exact CNT7| replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; exact ST7]. }
    assert (FR7 : rw_cells usegs m7 (bv_unsigned sp + -64) (dy_regs s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply heap_presx_rw_cells; [exact PX7| exact FR6| cbn; intros a Ha; left; lia|]. cbn [cells_size csize Nat.add dy_regs]. apply DY5; [clear - SXS SLO HLS; lia|].
      intros O. flat constr:((BLY6 O)) 5%nat. intros _ _ _ B4 _. lia. }
    flat constr:(STATE7) 2%nat. intros (HHj7 & _) _. clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HHj7) as MK.
    zstep. eapply dy_fin; [exact CTX| exact STATE7| exact FR7| exact TP| destruct RV7 as [(Er & _)|Er]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia].
  all: match goal with |- ?gg => idtac "MAINLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End DY.
