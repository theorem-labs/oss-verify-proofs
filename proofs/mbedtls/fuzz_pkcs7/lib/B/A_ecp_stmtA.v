(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_ecp_group_free P_ecp_red P_ecp_mul_mod P_ecp_derive_y P_ecp_point_read_binary P_ecp_check_pubkey P_ecp_group_load.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_ecp_stmtA () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.mul"; "mm_PHIn"; "ecp_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.addsub_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.intop_PHIn"; "sw_rhs_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.exp_mod_PHIn"; "ecp_dy_sz"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "sw_rhs_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.intop_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.exp_mod_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.addsub_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.calls_FR"; "mm_FRn"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "red_FRn"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "C24_ECP_RED"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_red.reducer_R"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.of_nat"; "ecp_reducer_stmtA"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_mul_mod.mul_mod_R"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_h"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "grp_imgA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "ecp_grp_preA"; "ecp_out_sepA"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "mc_okA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "C24_ECP_MUL_MOD"; "ecp_mul_mod_postA"; "mm_nz"; "check_pubkey_PHIn"; "check_pubkey_FRn"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_point_at"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_pt"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_X"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_G"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Y"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_A"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_B"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "grp_nle"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_freeable"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_mpds"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_check_pubkey.bad_point_ok"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "C24_ECP_CHECK_PUBKEY"; "ecp_check_postA"; "point_read_PHIn"; "point_read_FRn"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_point_read_binary.pt_dis"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_blocks"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_derive_y.ECP_FEATURE_UNAVAILABLE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "C24_ECP_POINT_READ"; "ecp_point_read_postA"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_group_free.grp_free_LB"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_GROUP_SIZE"; "group_load_PHI"; "group_load_FRn"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_group_load.gl_result"; "C24_ECP_GROUP_LOAD"; "ecp_group_load_postA"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_ECP_SET_ZERO : Z := 0xcb34c.              (* [comment removed for export] *)
Definition A_ECP_POINT_READ_BINARY : Z := 0xcb3e4.     (* [comment removed for export] *)
Definition A_ECP_SW_DERIVE_Y : Z := 0xcb778.           (* [comment removed for export] *)
Definition A_ECP_CHECK_PUBKEY : Z := 0xce068.          (* [comment removed for export] *)
Definition A_ECP_SW_RHS : Z := 0xcede4.                (* [comment removed for export] *)
Definition A_ECP_MUL_MOD : Z := 0xcef9c.               (* [comment removed for export] *)
Definition A_ECP_GROUP_LOAD_E : Z := 0xd0988.          (* [comment removed for export] *)
Definition A_MUL_COUNT : Z := 0x63c120.                 (* [comment removed for export] *)  (* [comment removed for export] *)

Notation ECP_RED_STACK_A := 576 (only parsing).          (* [comment removed for export] *)
Notation ECP_MUL_MOD_STACK_A := 1040 (only parsing).      (* [comment removed for export] *)
Notation ECP_SW_RHS_STACK_A := 1104 (only parsing).       (* [comment removed for export] *)
Notation ECP_DERIVE_Y_STACK_A := 1504 (only parsing).    (* [comment removed for export] *)
Notation ECP_CHECK_PUBKEY_STACK_A := 1232 (only parsing). (* [comment removed for export] *)
Notation ECP_POINT_READ_STACK_A := 1504 (only parsing).  (* [comment removed for export] *)
Notation ECP_GROUP_LOAD_STACK_A := 192 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Notation ECP_RED_NF := 1%nat (only parsing).
Notation ECP_MUL_MOD_NF := 2%nat (only parsing).         (* [comment removed for export] *)
Notation ECP_SW_RHS_NF := 2%nat (only parsing).
Notation ECP_DERIVE_Y_NF := 4%nat (only parsing).        (* [comment removed for export] *)
Notation ECP_CHECK_PUBKEY_NF := 3%nat (only parsing).    (* [comment removed for export] *)
Notation ECP_POINT_READ_NF := 4%nat (only parsing).

(* [comment removed for export] *)
Definition C24_ECP_RED : Z := 2.
Definition C24_ECP_MUL_MOD : Z := 18.      (* [comment removed for export] *)
Definition C24_ECP_SW_RHS : Z := 20.
Definition C24_ECP_DERIVE_Y : Z := 36.      (* [comment removed for export] *)
Definition C24_ECP_CHECK_PUBKEY : Z := 24.
Definition C24_ECP_POINT_READ : Z := 40.
Definition C24_ECP_GROUP_LOAD : Z := 8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mc_okA (R : art_layout) (MC : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "(0.(1.(2.(3.O2.))O1.)(0.(1.(4.O1.+8.)(5.(3.O2.)))(0.Pa,$6.P,(0.(1.O1.R1.)(7.R1.(4.O1.+8.)))(8.(9.(3.O2.)R2.))(0.(1.(:.(;.O2.))O1.)(0.(1.(4.O1.+8.)(<.(;.O2.)))(=.$6.(>.O1.+8.)=))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition grp_imgA (g : ecp_grp) : Prop := Forall mpd_imgA (grp_mpds g).

(* [comment removed for export] *)
Definition grp_nle (g : ecp_grp) (N : Z) : Prop := md_n (g_P g) <= N /\ md_n (g_A g) <= N /\ md_n (g_B g) <= N.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition red_PHIn (nP : Z) : Z := grow_PHI (2 * nP).
Definition red_FRn (d : Z) : Z := calls_FR 2 (d + 1).
(* [comment removed for export] *)
Definition mm_nz (nX nA nB nP : Z) : Z := Z.max (mul_mpi_nz nX nA nB + 2) (2 * nP + 2).
Definition mm_PHIn (nX nA nB nP : Z) : Z := mul_mpi_PHIn nA nB + red_PHIn nP + mod_mpi_PHIn (mul_mpi_nz nX nA nB) nP.
Definition mm_FRn (nX nA nB nP d : Z) : Z := mul_mpi_FRn d + red_FRn d + mod_mpi_FRn (mul_mpi_nz nX nA nB) nP d.
(* [comment removed for export] *)
Definition ecp_sz (N : Z) : Z := 3 * N + 9.
(* [comment removed for export] *)
Definition sw_rhs_PHIn (N : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "(4.(4.(?.+2.(10.(11.O1.)(11.O1.)(11.O1.)O1.))(?.+3.(12.(11.O1.)(11.O1.))))(13.(11.O1.)))")
(* [comment removed for export] *).
Definition sw_rhs_FRn (N d : Z) : Z := 2 * mm_FRn (ecp_sz N) (ecp_sz N) (ecp_sz N) N d + 3 * addsub_FRn d + intop_FRn d.
(* [comment removed for export] *)
Definition ecp_dy_sz (N : Z) : Z := ecp_sz N + 4.
(* [comment removed for export] *)
Definition derive_y_PHIn (N : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "(4.(4.(4.(4.(14.O1.)(13.O1.))(15.(11.O1.)(4.O1.+1.)O1.))(12.(16.O1.)(16.O1.)))$17.)")
(* [comment removed for export] *).
Definition derive_y_FRn (N d : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "(4.(4.(4.(4.(18.O2.(4.O1.+1.))(19.(4.O1.+1.)))(1:.(11.O2.)(4.O2.+1.)O2.(4.O1.+1.)))(1;.(4.O1.+1.)))(1<.+1.(4.O1.+1.)))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition check_pubkey_PHIn (N : Z) : Z :=
  mm_PHIn 0 N N N + sw_rhs_PHIn N + grow_PHI N + intop_PHIn N + 3 * AVOL_CALL.
Definition check_pubkey_FRn (N d : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "(4.(4.(4.(4.(1=.=O2.O2.O2.(4.O1.+1.))(18.O2.(4.O1.+1.)))(1<.+2.(4.O1.+1.)))(19.(4.O1.+1.)))(1<.+3.(4.O1.+1.)))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition point_read_PHIn (N len : Z) : Z := 3 * MPI_RB_PHI len + 2 * grow_PHI 1 + 2 * AVOL_CALL + derive_y_PHIn N.
Definition point_read_FRn (N d : Z) : Z := calls_FR 12 d + derive_y_FRn N d.
(* [comment removed for export] *)
Definition group_load_PHI : Z := 2 * (7 * AVOL_CALL) + 3 * grow_PHI 1.
Definition group_load_FRn (d : Z) : Z := calls_FR 20 d.

Lemma mm_PHIn_mono : ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Px,$6.Pa,$6.Pb,$6.Pp,$6.Px',$6.Pa',$6.Pb',$6.Pp',$6.P,(1.R8.R4.)P,(1.R8.R4.)P,(1.R8.R4.)P,(1.R8.R4.)(1.(10.R<.R;.R:.R9.)(10.R8.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros. unfold mm_PHIn, red_PHIn.
  pose proof (mul_mpi_PHIn_mono a b a' b' ltac:(lia) ltac:(lia)).
  pose proof (mod_mpi_PHIn_mono (mul_mpi_nz x a b) p (mul_mpi_nz x' a' b') p' ltac:(unfold mul_mpi_nz; lia) ltac:(lia)).
  pose proof (grow_PHI_mono (2 * p) (2 * p') ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ecp_reducer_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY K STK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Ph,(1>.O6.O5.O4.)PLB,(1?.$20.)PLF,(1?.$20.)Pra,(21.&40.)Psp,(21.&40.)Pgp,(21.&40.)Ptp,(21.&40.)Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Ps0,(21.&40.)Ps1,(21.&40.)Pa0,(21.&40.)Pa1,(21.&40.)Pa2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Ps2,(21.&40.)Ps3,(21.&40.)Ps4,(21.&40.)Ps5,(21.&40.)Ps6,(21.&40.)Ps7,(21.&40.)Ps8,(21.&40.)Ps9,(21.&40.)Ps10,(21.&40.)Ps11,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)PF,(22.&5.(21.&40.))Pfc,(21.&20.)Pm,P,(21.&40.)(23.(21.&8.))Pmo,$24.PdX,$25.Plo,$6.Pd,$6.P,(26.O6.O5.O4.R29.R28.R27.R5.)P,(27.O6.O5.O4.R2:.R5.)P,(28.(29.(2:.$20.R29.)#1.)#200.)P,(2;.O6.R8.R2;.R6.)P,(8.(=.$2<.(2=.R7.)$2>.))P,(2?.O5.R2=.R2<.(30.&40.R2:.)(31.O6.O5.O4.R2>.)R8.)P,P,(8.(=.$2<.(2=.R9.)$32.))(33.(1.(4.(34.R:.)(?.+4.(35.R:.)))R9.)(1.(30.&40.R2<.)(34.R:.)))P,(36.O6.R<.R9.(30.&40.R2<.))P,(1.(37.O5.)R:.)P,(1.R;.(38.(38.(30.&40.R2>.)O1.)(39.O5.)))P,(1.(30.&40.R2?.)(31.O6.O5.O4.R33.))P,(=.$6.(>.(30.&40.R30.)+10.)=)P,(=.(21.&40.)R2?.(3:.&40.(3;.O5.)))P,(3<.O6.R12.)P,(=.$6.(>.(30.&40.R34.)+2.)=)P,(3=.O6.(;.O5.)(3>.O6.O5.O4.R38.)R14.R12.)P,(1.(4.(3?.O6.O5.O4.R39.)(40.O2.))$41.)P,(42.O6.R16.(37.O5.)(43.O6.O5.O4.R3:.)(30.&40.R30.)(30.&40.R36.)R12.)P,(44.O5.(45.R15.)+10.R13.)P,(1.(4.(46.O6.O5.O4.R3<.)(47.R14.))$48.)P,(1.(4.(49.R3<.)$4:.)$4;.)P,(=.(21.&40.)R32.(3:.&40.(45.R18.)))(4<.O6.(4=.O6.O5.O4.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R3?.R3>.R3=.R19.(4>.O2.R19.R3>.)(40.O2.)(47.R17.)R18.R1;.R1:.)(4?.(50.(51.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(3:.&40.O3.)R1<.(52.(21.&40.))R1;.(53.O6.))R1:.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition modp_table_okA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Pe,$6.Plp,$6.Pws,(1?.(21.&40.))P,(54.(55.$6.(55.$6.(1?.(21.&40.))))(56.$6.(55.$6.(1?.(21.&40.)))R3.(56.$6.(1?.(21.&40.))R2.R1.))O1.)(0.(=.$6.(>.R4.+2.)=)(57.$6.LK,$6.(57.$6.LSTK,$6.(0.(0.(1.(58.(2:.(21.&40.)R4.))R2.)(1.R2.(?.+2.(58.(2:.(21.&40.)R4.)))))(0.(0.(1.=R1.)(1.R1.+240.))(59.O4.O3.O2.R6.R2.R1.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ecp_mul_mod_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs R HIA) (LB LF : list blk) (dX : mpd) (G : Z) (g : ecp_grp) (MC : Z) (PHI FR SZ : Z) (lo : Z) (m : mem) (mo : Model)
    : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Lc,$5:.(57.(21.&40.)Lt0,(21.&40.)(57.(21.&40.)Lt1,(21.&40.)(57.(21.&40.)Lt2,(21.&40.)(57.(21.&40.)La1,(21.&40.)(57.(21.&40.)La2,(21.&40.)(57.(21.&40.)La3,(21.&40.)(57.(21.&40.)La4,(21.&40.)(57.(21.&40.)La5,(21.&40.)(57.(21.&40.)La6,(21.&40.)(57.(21.&40.)La7,(21.&40.)(57.(21.&40.)Lt3,(21.&40.)(57.(21.&40.)Lt4,(21.&40.)(57.(21.&40.)Lt5,(21.&40.)(57.(21.&40.)Lt6,(21.&40.)(57.P,(21.&40.)(23.(21.&8.))Lm',P,(21.&40.)(23.(21.&8.))(57.$24.Lmo',$24.(57.(1>.O23.O22.O21.)Lh',(1>.O23.O22.O21.)(57.(1?.$20.)LLB',(1?.$20.)(57.$25.LdX',$25.(57.$6.Lr,$6.(57.(21.&40.)Lcnt',(21.&40.)(0.(=.$5:.R16.(4?.(50.(51.O1?.O1>.O1=.O1<.R15.R14.R13.O1;.O1:.(3:.&40.R2.)R12.R11.R10.R?.R>.R=.R<.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.R;.R:.R9.R8.)O?.(5;.O1?.)O>.(52.(21.&40.))R7.(53.O23.))R6.))(0.(3<.O23.R7.)(0.(36.O23.R7.O3.(30.&40.O1>.))(0.(5<.O1.R6.)(0.(5=.O23.O22.(5>.O<.O:.)O;.(30.&40.O1>.)(37.O22.)(43.O23.O22.O21.O=.)(5?.(55.$6.$6.)(56.$6.$6.(45.O:.)(4.(45.O:.)+10.))(5?.(55.$6.$6.)(56.$6.$6.O7.(4.O7.+8.))(60.(55.$6.$6.))))O2.R7.)(0.(=.$6.(31.O23.O22.O21.R5.)(31.O23.O22.O21.O=.))(0.(=.$6.(43.O23.O22.O21.R5.)(43.O23.O22.O21.O=.))(0.(=.$6.(61.O23.O22.O21.R5.)(61.O23.O22.O21.O=.))(0.(27.O23.O22.O21.R5.R6.)(0.Px,$6.P,(3>.O23.O22.O21.O=.R1.)(3>.O23.O22.O21.R7.R2.)(0.(1.(3?.O23.O22.O21.R5.)(4.(3?.O23.O22.O21.O=.)O6.))(0.(1.(46.O23.O22.O21.R5.)(4.(46.O23.O22.O21.O=.)O5.))(0.(26.O23.O22.O21.R5.R4.O;.R7.)(0.(2;.O23.R7.R4.R3.)(0.(62.O<.O:.R4.R3.)(0.Pb,$20.P,(54.$20.R1.(63.R4.))(33.(54.$20.R2.(63.O:.))(64.O22.(5>.O<.O:.)O;.(65.$6.$6.R2.)(66.$6.$6.R2.)))(0.(67.O23.O20.R7.R4.O9.O8.)(0.(68.O23.R7.O7.(5?.$69.(6:.R1.)(60.$69.)))(0.(6;.O<.O:.R2.R3.)(1.(35.R3.)O4.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ecp_grp_preA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (h : HST segs R HIA) (LB LF : list blk) (m : mem) (G : Z) (g : ecp_grp) (MC lo SP d : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "(0.(67.O>.O;.O7.O9.O6.O5.)(0.(=.$6.(6<.O5.)+1.)(0.(=.$6.(6=.(6>.O5.))+1.)(0.(6?.O5.)(0.(70.(3.O=.)(71.$20.O9.(72.O8.))O3.O6.+<0.)(0.(33.(1.(4.O6.+<0.)O3.)(1.O2.O6.))(0.(33.(1.(4.O4.+8.)O6.)(1.(4.O6.+<0.)O4.))(0.(73.O>.(;.O=.)(3>.O>.O=.O<.O:.)O7.O6.+<0.)(44.O=.O6.+<0.O1.)))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ecp_out_sepA (dX : mpd) (G MC : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "(0.(33.(1.(4.(45.O3.)+10.)O2.)(1.(4.O2.+<0.)(45.O3.)))(0.P,(=.$2<.(2=.O3.)$74.)(33.(1.(4.O2.+<0.)(34.O3.))(1.(4.(34.O3.)(?.+4.(35.O3.)))O2.))(33.(1.(4.O1.+8.)(45.O3.))(1.(4.(45.O3.)+10.)O1.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ext_opndA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk) (m : mem) (dX e : mpd) (MC SP lo d : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "(0.(2;.O=.O7.O9.O5.)(0.(33.(1.(4.(45.O6.)+10.)(45.O5.))(1.(4.(45.O5.)+10.)(45.O6.)))(0.(75.O6.O5.O2.O3.)(0.(70.(3.O<.)(71.$20.O9.(72.O8.))O2.(45.O5.)+10.)(0.P,(=.$2<.(2=.O5.)$74.)(70.(3.O<.)(71.$20.O9.(72.O8.))O2.(34.O5.)(?.+4.(35.O5.)))(0.(33.(1.(4.O4.+8.)(45.O5.))(1.(4.(45.O5.)+10.)O4.))(0.(3=.O=.(;.O<.)(3>.O=.O<.O;.O:.)O7.O5.)(0.(76.O5.)(44.O<.(45.O5.)+10.O1.)))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ecp_mul_mod_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent) (ENTRY MC : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Ph,(1>.O6.O5.O4.)PLB,(1?.$20.)PLF,(1?.$20.)Pra,(21.&40.)Psp,(21.&40.)Pgp,(21.&40.)Ptp,(21.&40.)Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Ps0,(21.&40.)Ps1,(21.&40.)Pa0,(21.&40.)Pa1,(21.&40.)Pa2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Ps2,(21.&40.)Ps3,(21.&40.)Ps4,(21.&40.)Ps5,(21.&40.)Ps6,(21.&40.)Ps7,(21.&40.)Ps8,(21.&40.)Ps9,(21.&40.)Ps10,(21.&40.)Ps11,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)PF,(22.&5.(21.&40.))Pfc,(21.&20.)Pm,P,(21.&40.)(23.(21.&8.))Pmo,$24.PdX,$25.PdA,$25.PdB,$25.PG,$6.Pg,$77.Pcnt,(21.&40.)Plo,$6.Pd,$6.Pslo,$6.P,(26.O6.O5.O4.R2?.R2>.R2=.R;.)P,(27.O6.O5.O4.R30.R;.)P,(28.(29.(2:.$20.R2?.)#2.)#200.)P,(78.O6.O5.O4.O3.R32.R31.R30.R>.R9.R8.O1.R6.(30.&40.R2>.)R5.)P,(79.R=.R:.O1.)P,(2;.O6.R10.R33.R>.)P,(2;.O6.R11.R34.R>.)P,(2;.O6.R12.R35.R>.)P,(7:.R11.R10.)P,(7:.R12.R10.)P,(7:.R12.R11.)P,(8.(=.$2<.(2=.R14.)$2>.))P,(75.R15.R14.R?.(30.&40.R37.))P,(75.R16.R14.R10.(30.&40.R38.))P,(70.(3.O5.)(71.$20.R3<.(72.R3;.))R11.(45.R16.)+10.)P,P,(=.$2<.(2=.R17.)$74.)(70.(3.O5.)(71.$20.R3>.(72.R3=.))R13.(34.R18.)(?.+4.(35.R18.)))P,(70.(3.O5.)(71.$20.R3>.(72.R3=.))R13.(45.R17.)+10.)P,P,(=.$2<.(2=.R18.)$74.)(70.(3.O5.)(71.$20.R40.(72.R3?.))R15.(34.R19.)(?.+4.(35.R19.)))P,(33.(1.(4.O1.+8.)(45.R1:.))(1.(4.(45.R1:.)+10.)O1.))P,(33.(1.(4.O1.+8.)(45.R1:.))(1.(4.(45.R1:.)+10.)O1.))P,(2?.O5.R42.R41.(30.&40.R3?.)(31.O6.O5.O4.R43.)R1=.)P,P,(8.(=.$2<.(2=.R1>.)$32.))(33.(1.(4.(34.R1?.)(?.+4.(35.R1?.)))R19.)(1.(30.&40.R41.)(34.R1?.)))P,(68.O6.R21.O1.(5?.$69.(6:.R1:.)(60.$69.)))P,(7;.O5.O1.)P,(36.O6.R23.R1;.(30.&40.R43.))P,(1.(37.O5.)R1<.)P,(1.R1=.(38.(38.(30.&40.R45.)+410.)(39.O5.)))P,(7<.O6.(;.O5.)R26.R1<.(30.&40.R46.))P,(1.(37.O5.)R1=.)P,(1.R1>.R20.)P,(1.(30.&40.R49.)(31.O6.O5.O4.R4=.))P,(=.$6.(>.(30.&40.R4:.)+10.)=)P,(=.(21.&40.)R49.(3:.&40.(3;.O5.)))P,(3<.O6.R2<.)P,(=.$6.(>.(30.&40.R4>.)+2.)=)P,(3=.O6.(;.O5.)(3>.O6.O5.O4.R52.)R2>.R2<.)P,(3=.O6.(;.O5.)(3>.O6.O5.O4.R53.)R2?.R2<.)P,(3=.O6.(;.O5.)(3>.O6.O5.O4.R54.)R30.R2<.)P,(76.R2>.)P,(76.R2>.)P,(1.(4.(3?.O6.O5.O4.R57.)(10.(35.R31.)(35.R30.)(35.R2?.)(35.(6>.R2=.))))$41.)P,(42.O6.R34.(37.O5.)(43.O6.O5.O4.R58.)(30.&40.R4>.)(30.&40.R54.)R2;.)P,(44.O5.(45.R33.)+10.R2<.)P,(44.O5.(45.R33.)+10.R2=.)P,(44.O5.(45.R33.)+10.R2>.)P,(1.(4.(46.O6.O5.O4.R5<.)(1=.(35.R36.)(35.R35.)(35.R34.)(35.(6>.R32.))R2?.))$48.)P,(1.(4.(49.R5<.)$7=.)$4;.)P,(=.(21.&40.)R52.(3:.&40.R35.))P,(=.(21.&40.)R52.(3:.&40.(45.R39.)))P,(=.(21.&40.)R52.(3:.&40.(45.R39.)))P,(=.(21.&40.)R52.(3:.&40.(45.R39.)))(4<.O6.(7>.O6.O5.O4.O3.R5?.R5>.R5=.R5<.R58.R57.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R40.R3?.R62.R61.R60.R3<.R39.R38.O1.(10.(35.R3<.)(35.R3;.)(35.R3:.)(35.(6>.R38.)))(1=.(35.R3<.)(35.R3;.)(35.R3:.)(35.(6>.R38.))R35.)(7?.(35.R3<.)(35.R3;.)(35.R3:.)(35.(6>.R38.)))R36.R3>.R3=.)(4?.(50.(51.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.)R40.(3:.&40.O2.)R3?.(52.(21.&40.))R3>.(53.O6.))R3=.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ecp_rhs_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent) (ENTRY MC : Z) (DY : bool) : Prop :=
  forall (h : HST segs R HIA) (LB LF : list blk)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
         (dX dA : mpd) (G : Z) (g : ecp_grp) (cnt : word) (N lo d slo : Z),
  HM segs R HIA h LB LF m -> HK segs R HIA h mo ->
  (length LF + (if DY then ECP_DERIVE_Y_NF else ECP_SW_RHS_NF) <= 512)%nat ->
  ecp_grp_preA segs R HIA MT h LB LF m G g MC lo (bv_unsigned sp) d -> ecp_out_sepA dX G MC ->
  md_sg (g_A g) = 1 -> md_sg (g_B g) = 1 -> 1 <= mpd_val (g_P g) -> (DY = true -> md_n (g_P g) <= 4999) ->
  grp_nle g N -> md_n dA <= N ->
  mpd_at segs m LB dX -> md_own dX = LNull ->
  mpd_writableA R LB LF (bv_unsigned sp) (htop segs R HIA h) dX ->
  ext_opndA segs R HIA h LB LF m dX dA MC (bv_unsigned sp) lo d ->
  rw_cells segs m MC [C8 cnt] -> mc_okA R MC ->
  stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo ->
  lo <= bv_unsigned sp - (if DY then ECP_DERIVE_Y_STACK_A else ECP_SW_RHS_STACK_A) - arl_need_ecp R ->
  sshad segs (arl_AL R) m slo (bv_unsigned sp) -> arl_stklo R <= slo -> slo <= lo ->   (* [comment removed for export] *)
  bv_unsigned sp <= htop segs R HIA h -> bv_unsigned sp mod 16 = 0 ->
  tp = Z_to_bv 64 (arl_tp R) -> mem_inv segs m -> bv_unsigned ra mod 2 = 0 ->
  mpd_aobjA segs (arl_AL R) (hcs segs R HIA h) m dX ->
  havol segs R HIA h + (if DY then derive_y_PHIn N else sw_rhs_PHIn N) <= AVOL_MAX ->
  uwc segs m (arl_stklo R) (hstkhi segs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
  uw_obj R (md_addr dX) 16 d ->
  hfr segs R HIA h + (if DY then derive_y_FRn N d else sw_rhs_FRn N d) <= FR_MAX ->
  cnt24 LB + (if DY then C24_ECP_DERIVE_Y else C24_ECP_SW_RHS) <= C24MAX ->
  a0 = Z_to_bv 64 G ->
  (if DY then a1 = Z_to_bv 64 (md_addr dA) /\ a2 = Z_to_bv 64 (md_addr dX)
         else a1 = Z_to_bv 64 (md_addr dX) /\ a2 = Z_to_bv 64 (md_addr dA)) ->
  aevtS segs (ecp_mul_mod_postA segs R HIA MT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX G g MC
                (if DY then derive_y_PHIn N else sw_rhs_PHIn N) (if DY then derive_y_FRn N d else sw_rhs_FRn N d)
                (if DY then ecp_dy_sz N else ecp_sz N) lo m mo)   (* [comment removed for export] *)
       (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)) mo).

Definition ecp_sw_rhs_stmtA segs R HIA MT ENTRY MC := ecp_rhs_stmtA segs R HIA MT ENTRY MC false.
Definition ecp_derive_y_stmtA segs R HIA MT ENTRY MC := ecp_rhs_stmtA segs R HIA MT ENTRY MC true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ecp_check_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs R HIA) (LB LF : list blk) (G : Z) (g : ecp_grp) (Q : Z) (p : ecp_pt) (MC N lo d : Z) (m : mem) (mo : Model)
    : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Lc,$5:.(57.(21.&40.)Lt0,(21.&40.)(57.(21.&40.)Lt1,(21.&40.)(57.(21.&40.)Lt2,(21.&40.)(57.(21.&40.)La1,(21.&40.)(57.(21.&40.)La2,(21.&40.)(57.(21.&40.)La3,(21.&40.)(57.(21.&40.)La4,(21.&40.)(57.(21.&40.)La5,(21.&40.)(57.(21.&40.)La6,(21.&40.)(57.(21.&40.)La7,(21.&40.)(57.(21.&40.)Lt3,(21.&40.)(57.(21.&40.)Lt4,(21.&40.)(57.(21.&40.)Lt5,(21.&40.)(57.(21.&40.)Lt6,(21.&40.)(57.P,(21.&40.)(23.(21.&8.))Lm',P,(21.&40.)(23.(21.&8.))(57.$24.Lmo',$24.(57.(1>.O23.O22.O21.)Lh',(1>.O23.O22.O21.)(57.(1?.$20.)LLB',(1?.$20.)(57.$6.Lr,$6.(57.(21.&40.)Lcnt',(21.&40.)(0.(=.$5:.R15.(4?.(50.(51.O1?.O1>.O1=.O1<.R14.R13.R12.O1;.O1:.(3:.&40.R2.)R11.R10.R?.R>.R=.R<.R;.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.R:.R9.R8.R7.)O?.(5;.O1?.)O>.(52.(21.&40.))R6.(53.O23.))R5.))(0.(3<.O23.R6.)(0.(36.O23.R6.O4.(30.&40.O1>.))(0.(5<.O1.R5.)(0.(5=.O23.O22.O<.O;.(30.&40.O1>.)(37.O22.)(43.O23.O22.O21.O=.)(5?.(55.$6.$6.)(56.$6.$6.O6.(4.O6.+8.))(60.(55.$6.$6.)))O2.R6.)(0.(=.$6.(31.O23.O22.O21.R4.)(31.O23.O22.O21.O=.))(0.(=.$6.(43.O23.O22.O21.R4.)(43.O23.O22.O21.O=.))(0.(=.$6.(61.O23.O22.O21.R4.)(61.O23.O22.O21.O=.))(0.(27.O23.O22.O21.R4.R5.)(0.Px,$6.P,(3>.O23.O22.O21.O=.R1.)(3>.O23.O22.O21.R6.R2.)(0.(1.(3?.O23.O22.O21.R4.)(4.(3?.O23.O22.O21.O=.)(80.O5.)))(0.(1.(46.O23.O22.O21.R4.)(4.(46.O23.O22.O21.O=.)(81.O5.O3.)))(0.(26.O23.O22.O21.R4.R3.O;.R6.)(0.Pb,$20.(82.(54.$20.R1.R4.)(54.$20.R1.O<.))(0.(67.O23.O20.R6.R3.O:.O9.)(0.(83.O23.R6.R3.O8.O7.)(0.(68.O23.R6.O6.(5?.$69.(6:.R1.)(60.$69.)))(0.(7.(84.(85.+2.+1?.))R2.)(1.R2.=)))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_check_pubkey_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent) (ENTRY MC BP : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Ph,(1>.O7.O6.O5.)PLB,(1?.$20.)PLF,(1?.$20.)Pra,(21.&40.)Psp,(21.&40.)Pgp,(21.&40.)Ptp,(21.&40.)Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Ps0,(21.&40.)Ps1,(21.&40.)Pa0,(21.&40.)Pa1,(21.&40.)Pa2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Ps2,(21.&40.)Ps3,(21.&40.)Ps4,(21.&40.)Ps5,(21.&40.)Ps6,(21.&40.)Ps7,(21.&40.)Ps8,(21.&40.)Ps9,(21.&40.)Ps10,(21.&40.)Ps11,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)PF,(22.&5.(21.&40.))Pfc,(21.&20.)Pm,P,(21.&40.)(23.(21.&8.))Pmo,$24.PG,$6.PQ,$6.Pg,$77.Pp,$86.Pcnt,(21.&40.)Pbp1,$25.Pbp2,$25.PN,$6.Plo,$6.Pd,$6.Pslo,$6.P,(26.O7.O6.O5.R31.R30.R2?.R=.)P,(27.O7.O6.O5.R32.R=.)P,(28.(29.(2:.$20.R31.)#3.)#200.)P,(67.O7.O4.R10.R33.R>.R<.)P,(33.(0.(=.$6.(6<.R=.)+1.)(0.(8.(=.$6.(34.(87.(88.R=.)))=))(8.(=.$6.(34.(89.(88.R=.)))=))))(0.(=.$6.(6<.R=.)+2.)(=.$6.(34.(89.(88.R=.)))=)))P,(=.$6.(6=.(6>.R>.))+1.)P,(=.$6.(6=.(8:.R?.))+1.)P,(=.$6.(6=.(8;.R10.))+1.)P,(1.+1.(8<.(6>.R11.)))P,(6?.R12.)P,(8=.R13.R>.)P,(70.(3.O6.)(71.$20.R3;.(72.R3:.))R>.R16.+<0.)P,(33.(1.(4.R17.+<0.)R?.)(1.(30.&40.R39.)R17.))P,(33.(1.(4.O2.+8.)R18.)(1.(4.R18.+<0.)O2.))P,(73.O7.(;.O6.)(3>.O7.O6.O5.R3?.)R1;.R19.+<0.)P,(44.O6.R1:.+<0.R11.)P,(83.O7.R1=.R40.R1:.R18.)P,(8>.R19.)P,(8?.$25.Le,$25.(33.(=.$6.(6=.R1.)+1.)(=.$6.(6=.R1.)-1.))(90.R1:.))P,(8?.$25.Le,$25.(1.(35.R1.)R18.)(90.R1;.))P,(70.(3.O6.)(71.$20.R44.(72.R43.))R17.R1>.+30.)P,(33.(1.(4.R1?.+30.)R18.)(1.(30.&40.R42.)R1?.))P,(33.(1.(4.O2.+8.)R20.)(1.(4.R20.+30.)O2.))P,(73.O7.(;.O6.)(3>.O7.O6.O5.R48.)R24.R21.+30.)P,(44.O6.R22.+30.R1:.)P,(68.O7.R26.O2.(5?.$69.(6:.R20.)(60.$69.)))P,(7;.O6.O2.)P,(91.O7.R28.R4;.O1.R21.)P,(91.O7.R29.R4<.(4.O1.+20.)R21.)P,(76.R23.)P,(76.R23.)P,(=.$92.(93.O1.+10.)$94.)P,(=.$92.(93.(4.O1.+20.)+10.)$94.)P,(33.(1.(4.O2.+8.)O1.)(1.(4.O1.+30.)O2.))P,(36.O7.R2?.R25.(30.&40.R4?.))P,(1.(37.O6.)R26.)P,(1.R27.(38.(38.(30.&40.R51.)+4=0.)(39.O6.)))P,(7<.O7.(;.O6.)R32.R26.(30.&40.R52.))P,(1.(37.O6.)R27.)P,(1.R28.R2:.)P,(1.(30.&40.R55.)(31.O7.O6.O5.R59.))P,(=.$6.(>.(30.&40.R56.)+10.)=)P,(=.(21.&40.)R55.(3:.&40.(3;.O6.)))P,(3<.O7.R38.)P,(=.$6.(>.(30.&40.R5:.)+2.)=)P,(1.(4.(3?.O7.O6.O5.R5>.)(80.R31.))$41.)P,(42.O7.R3;.(37.O6.)(43.O7.O6.O5.R5?.)(30.&40.R55.)(30.&40.R5;.)R30.)P,(1.(4.(46.O7.O6.O5.R60.)(81.R33.R31.))$48.)P,(1.(4.(49.R60.)$95.)$4;.)P,(=.(21.&40.)R56.(3:.&40.R3<.))P,(=.(21.&40.)R56.(3:.&40.R3<.))(4<.O7.(96.O7.O6.O5.O4.R61.R60.R5?.R5>.R5:.R59.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R42.R41.R64.R63.R62.R3>.R3<.R3=.R3;.O2.R37.R36.R35.R40.R3?.)(4?.(50.(51.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.)R42.(3:.&40.O3.)R41.(52.(21.&40.))R40.(53.O7.))R3?.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ecp_point_read_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs R HIA) (LB LF : list blk) (G : Z) (g : ecp_grp) (Q : Z) (p : ecp_pt) (bs : list byte) (MC N lo d : Z) (m : mem) (mo : Model)
    : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Lc,$5:.(57.(21.&40.)Lt0,(21.&40.)(57.(21.&40.)Lt1,(21.&40.)(57.(21.&40.)Lt2,(21.&40.)(57.(21.&40.)La1,(21.&40.)(57.(21.&40.)La2,(21.&40.)(57.(21.&40.)La3,(21.&40.)(57.(21.&40.)La4,(21.&40.)(57.(21.&40.)La5,(21.&40.)(57.(21.&40.)La6,(21.&40.)(57.(21.&40.)La7,(21.&40.)(57.(21.&40.)Lt3,(21.&40.)(57.(21.&40.)Lt4,(21.&40.)(57.(21.&40.)Lt5,(21.&40.)(57.(21.&40.)Lt6,(21.&40.)(57.P,(21.&40.)(23.(21.&8.))Lm',P,(21.&40.)(23.(21.&8.))(57.$24.Lmo',$24.(57.(1>.O24.O23.O22.)Lh',(1>.O24.O23.O22.)(57.(1?.$20.)LLB',(1?.$20.)(57.$86.Lp',$86.(57.$6.Lr,$6.(57.(21.&40.)Lcnt',(21.&40.)(0.(=.$5:.R16.(4?.(50.(51.O20.O1?.O1>.O1=.R15.R14.R13.O1<.O1;.(3:.&40.R2.)R12.R11.R10.R?.R>.R=.R<.O1:.O19.O18.O17.O16.O15.O14.O13.O12.O11.R;.R:.R9.R8.)O10.(5;.O20.)O?.(52.(21.&40.))R7.(53.O24.))R6.))(0.(3<.O24.R7.)(0.(36.O24.R7.O4.(30.&40.O1?.))(0.(5<.O1.R6.)(0.(5=.O24.O23.O=.O<.(30.&40.O1?.)(37.O23.)(43.O24.O23.O22.O>.)(5?.(55.$6.$6.)(56.$6.$6.O9.(4.O9.+30.))(5?.(55.$6.$6.)(56.$6.$6.O6.(4.O6.+8.))(60.(55.$6.$6.))))O2.R7.)(0.(=.$6.(31.O24.O23.O22.R5.)(31.O24.O23.O22.O>.))(0.(=.$6.(43.O24.O23.O22.R5.)(43.O24.O23.O22.O>.))(0.(=.$6.(61.O24.O23.O22.R5.)(61.O24.O23.O22.O>.))(0.(27.O24.O23.O22.R5.R6.)(0.Px,$6.P,(3>.O24.O23.O22.O>.R1.)(3>.O24.O23.O22.R7.R2.)(0.(1.(3?.O24.O23.O22.R5.)(4.(3?.O24.O23.O22.O>.)(97.O5.(58.(2:.(21.&8.)O7.)))))(0.(1.(46.O24.O23.O22.R5.)(4.(46.O24.O23.O22.O>.)(98.O5.O3.)))(0.(26.O24.O23.O22.R5.R4.O<.R7.)(0.(83.O24.R7.R4.O9.R3.)(0.(8>.R3.)(0.(8?.$25.Le,$25.(33.(=.$6.(6=.R1.)+1.)(=.$6.(6=.R1.)-1.))(90.R3.))(0.(99.R3.)(0.P,(=.$6.R2.=)(8?.$25.Le,$25.(1.(35.R1.)(16.O5.))(90.R4.))(0.Pb,$20.P,(54.$20.R1.O=.)(54.$20.R2.R6.)(0.Pb,$20.P,(54.$20.R1.R5.)(33.(54.$20.R2.O=.)(54.$20.R2.(9:.R5.)))(0.Pb,$20.P,(54.$20.R1.(9:.R4.))(0.(8.(54.$20.R2.O=.))(64.O23.O=.O<.(65.$6.$6.R2.)(66.$6.$6.R2.)))(0.(67.O24.O21.R7.R4.O;.O:.)(0.(68.O24.R7.O6.(5?.$69.(6:.R1.)(60.$69.)))(0.P,(=.$6.(34.(87.(88.O:.)))=)(0.(=.$86.R4.O8.)(0.(=.(1?.$20.)R5.O=.)P,(=.(21.&40.)(3:.&40.R3.)(3:.&40.$9;.))(1.+1.(58.(2:.(21.&8.)O7.)))))(0.(7.(84.(85.+2.+1?.))R2.)(1.R2.=)))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_point_read_binary_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent) (ENTRY MC : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Ph,(1>.O6.O5.O4.)PLB,(1?.$20.)PLF,(1?.$20.)Pra,(21.&40.)Psp,(21.&40.)Pgp,(21.&40.)Ptp,(21.&40.)Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Ps0,(21.&40.)Ps1,(21.&40.)Pa0,(21.&40.)Pa1,(21.&40.)Pa2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Ps2,(21.&40.)Ps3,(21.&40.)Ps4,(21.&40.)Ps5,(21.&40.)Ps6,(21.&40.)Ps7,(21.&40.)Ps8,(21.&40.)Ps9,(21.&40.)Ps10,(21.&40.)Ps11,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)PF,(22.&5.(21.&40.))Pfc,(21.&20.)Pm,P,(21.&40.)(23.(21.&8.))Pmo,$24.PG,$6.PQ,$6.PB,$6.Pg,$77.Pp,$86.Pbs,(1?.(21.&8.))Pcnt,(21.&40.)PN,$6.Plo,$6.Pd,$6.Pslo,$6.P,(26.O6.O5.O4.R31.R30.R2?.R=.)P,(27.O6.O5.O4.R32.R=.)P,(28.(29.(2:.$20.R31.)#4.)#200.)P,(67.O6.O3.R10.R33.R>.R;.)P,(33.(=.$6.(6=.(6>.R<.))+1.)(=.$6.(6=.(6>.R<.))-1.))P,(6?.R=.)P,(1.(35.(6>.R>.))R:.)P,P,(8.(=.$6.(34.(87.(88.R?.)))=))P,(8.(=.$6.(34.(89.(88.R10.)))=))(0.(=.$6.(6<.R11.)+1.)(0.(=.$6.(6=.(6>.R11.))+1.)(0.(=.$6.(6=.(8:.R11.))+1.)(0.(=.$6.(6=.(8;.R11.))+1.)(0.(1.+1.(8<.(6>.R11.)))(0.(1.(35.(6>.R11.))+1387.)(8=.R11.R=.)))))))P,(70.(3.O5.)(71.$20.R38.(72.R37.))R;.R13.+<0.)P,(33.(1.(4.R14.+<0.)R<.)(1.(30.&40.R36.)R14.))P,(33.(1.(4.O1.+8.)R15.)(1.(4.R15.+<0.)O1.))P,(73.O6.(;.O5.)(3>.O6.O5.O4.R3<.)R18.R16.+<0.)P,(44.O5.R17.+<0.R>.)P,(83.O6.R1:.R3=.R17.R14.)P,(8?.$25.Le,$25.(=.$2<.(2=.R1.)$32.)(90.R15.))P,(8?.$25.Le,$25.(33.(=.$6.(6=.R1.)+1.)(=.$6.(6=.R1.)-1.))(90.R16.))P,(9<.(3.O5.)(71.$20.R40.(72.R3?.))(30.&40.R3=.)(31.O6.O5.O4.R41.)R1:.+30.)P,(33.(1.(4.R1;.+30.)R14.)(1.(30.&40.R3>.)R1;.))P,(33.(1.(4.O1.+8.)R1<.)(1.(4.R1<.+30.)O1.))P,(73.O6.(;.O5.)(3>.O6.O5.O4.R44.)R20.R1=.+30.)P,(44.O5.R1>.+30.R16.)P,P,(8.(=.$6.(34.(87.(88.R1=.)))=))(33.(1.(4.R20.+30.)R21.)(1.(4.R21.+<0.)R20.))P,P,(8.(=.$6.(34.(87.(88.R1>.)))=))Pe,$25.P,(54.$25.R1.(9=.R20.))P,(=.$2<.(2=.R2.)$74.)(33.(1.(4.R24.+30.)(34.R3.))(1.(4.(34.R3.)(?.+4.(35.R3.)))R24.))P,(9>.O6.R24.R20.R1=.)P,(7.=R21.)P,(7.(4.R22.(58.(2:.(21.&8.)R1?.)))(85.+2.+3?.))P,(70.(3.O5.)(71.$20.R4:.(72.R49.))R1=.R23.(58.(2:.(21.&8.)R20.)))P,(33.(1.(4.R24.(58.(2:.(21.&8.)R21.)))R1>.)(1.(30.&40.R48.)R24.))P,(33.(1.(4.R25.(58.(2:.(21.&8.)R22.)))R26.)(1.(4.R26.+30.)R25.))P,(33.(1.(4.O1.+8.)R26.)(1.(4.R26.(58.(2:.(21.&8.)R23.)))O1.))P,(33.(=.$6.(58.(2:.(21.&8.)R24.))=)(73.O6.(;.O5.)(3>.O6.O5.O4.R4?.)R2;.R27.(58.(2:.(21.&8.)R24.))))P,(33.(=.$6.(58.(2:.(21.&8.)R25.))=)(1.(4.(4.R28.(58.(2:.(21.&8.)R25.)))+8.)(85.+2.+2?.)))P,(68.O6.R2=.O1.(5?.$69.(6:.R25.)(60.$69.)))P,(7;.O5.O1.)P,(36.O6.R2?.R25.(30.&40.R4?.))P,(1.(37.O5.)R26.)P,(1.R27.(38.(38.(30.&40.R51.)+5>0.)(39.O5.)))P,(7<.O6.(;.O5.)R32.R26.(30.&40.R52.))P,(1.(37.O5.)R27.)P,(1.R28.R2:.)P,(1.(30.&40.R55.)(31.O6.O5.O4.R59.))P,(=.$6.(>.(30.&40.R56.)+10.)=)P,(=.(21.&40.)R55.(3:.&40.(3;.O5.)))P,(3<.O6.R38.)P,(=.$6.(>.(30.&40.R5:.)+2.)=)P,(1.(4.(3?.O6.O5.O4.R5>.)(97.R31.(58.(2:.(21.&8.)R33.))))$41.)P,(42.O6.R3;.(37.O5.)(43.O6.O5.O4.R5?.)(30.&40.R55.)(30.&40.R5;.)R30.)P,(1.(4.(46.O6.O5.O4.R60.)(98.R33.R31.))$48.)P,(1.(4.(49.R60.)$9?.)$4;.)P,(=.(21.&40.)R56.(3:.&40.R3<.))P,(=.(21.&40.)R56.(3:.&40.R3<.))P,(=.(21.&40.)R56.(3:.&40.R3<.))P,(=.(21.&40.)R56.(3:.&40.(58.(2:.(21.&8.)R3:.))))(4<.O6.(:0.O6.O5.O4.O3.R63.R62.R61.R60.R5<.R5;.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R44.R43.R66.R65.R64.R40.R3=.R3?.R3<.R3;.O1.R39.R38.R37.R42.R41.)(4?.(50.(51.R63.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.)R44.(3:.&40.O2.)R43.(52.(21.&40.))R42.(53.O6.))R41.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ecp_group_load_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs R HIA) (LB LF : list blk) (A : Z) (g : ecp_grp) (id lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Lc,$5:.(57.(21.&40.)Lt0,(21.&40.)(57.(21.&40.)Lt1,(21.&40.)(57.(21.&40.)Lt2,(21.&40.)(57.(21.&40.)La1,(21.&40.)(57.(21.&40.)La2,(21.&40.)(57.(21.&40.)La3,(21.&40.)(57.(21.&40.)La4,(21.&40.)(57.(21.&40.)La5,(21.&40.)(57.(21.&40.)La6,(21.&40.)(57.(21.&40.)La7,(21.&40.)(57.(21.&40.)Lt3,(21.&40.)(57.(21.&40.)Lt4,(21.&40.)(57.(21.&40.)Lt5,(21.&40.)(57.(21.&40.)Lt6,(21.&40.)(57.P,(21.&40.)(23.(21.&8.))Lm',P,(21.&40.)(23.(21.&8.))(57.$24.Lmo',$24.(57.(1>.O22.O21.O20.)Lh',(1>.O22.O21.O20.)(57.$6.Lr,$6.(57.$77.Lg',$77.(57.(1?.$20.)LNB,(1?.$20.)(57.(1?.$20.)LLB',(1?.$20.)(0.(=.$5:.R16.(4?.(50.(51.O1<.O1;.O1:.O19.R15.R14.R13.O18.O17.(3:.&40.R4.)R12.R11.R10.R?.R>.R=.R<.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R;.R:.R9.R8.)O<.(5;.O1<.)O;.(52.(21.&40.))R7.(53.O22.))R6.))(0.(3<.O22.R7.)(0.(36.O22.R7.O4.(30.&40.O1;.))(0.(5<.O1.R6.)(0.(5=.O22.O21.(:1.O6.O9.)O8.(30.&40.O1;.)(37.O21.)(43.O22.O21.O20.O:.)(5?.(55.$6.$6.)(56.$6.$6.O7.(4.O7.$:2.))(60.(55.$6.$6.)))O2.R7.)(0.(=.$6.(31.O22.O21.O20.R5.)(31.O22.O21.O20.O:.))(0.(=.$6.(43.O22.O21.O20.R5.)(43.O22.O21.O20.O:.))(0.(=.$6.(61.O22.O21.O20.R5.)(61.O22.O21.O20.O:.))(0.(27.O22.O21.O20.R5.R6.)(0.Px,$6.P,(3>.O22.O21.O20.O:.R1.)(3>.O22.O21.O20.R7.R2.)(0.(1.(3?.O22.O21.O20.R5.)(4.(3?.O22.O21.O20.O:.)$:3.))(0.(1.(46.O22.O21.O20.R5.)(4.(46.O22.O21.O20.O:.)(:4.O3.)))(0.(26.O22.O21.O20.R5.R1.O8.R7.)(0.Pb,$20.(82.(54.$20.R1.R2.)(33.(54.$20.R1.R3.)(54.$20.R1.(:1.O6.O9.))))(0.Pb,$20.P,(54.$20.R1.R3.)(0.(8.(54.$20.R2.(:1.O6.O9.)))(64.O21.(:1.O6.O9.)O8.(65.$6.$6.R2.)(66.$6.$6.R2.)))(0.(67.O22.O1?.R7.R1.O7.R3.)(0.(:5.(9=.R3.))(0.(=.(1?.$20.)(:6.R3.)R2.)(0.(:7.O1>.O1=.O5.O7.R4.R3.R2.)(73.O22.(;.O21.)(3>.O22.O21.O20.R5.)R7.O7.$:2.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_group_load_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_stmtA ()) "Ph,(1>.O7.O6.O5.)PLB,(1?.$20.)PLF,(1?.$20.)Pra,(21.&40.)Psp,(21.&40.)Pgp,(21.&40.)Ptp,(21.&40.)Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Ps0,(21.&40.)Ps1,(21.&40.)Pa0,(21.&40.)Pa1,(21.&40.)Pa2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Ps2,(21.&40.)Ps3,(21.&40.)Ps4,(21.&40.)Ps5,(21.&40.)Ps6,(21.&40.)Ps7,(21.&40.)Ps8,(21.&40.)Ps9,(21.&40.)Ps10,(21.&40.)Ps11,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)PF,(22.&5.(21.&40.))Pfc,(21.&20.)Pm,P,(21.&40.)(23.(21.&8.))Pmo,$24.PA,$6.Pg,$77.Pid,$6.Plo,$6.Pd,$6.P,(26.O7.O6.O5.R2;.R2:.R29.R7.)P,(27.O7.O6.O5.R2<.R7.)P,(67.O7.O4.R9.R2<.R7.R6.)P,(:5.(9=.R7.))P,(9<.(3.O6.)(71.$20.(:1.R8.R2>.)(72.R2=.))(30.&40.R2;.)(31.O7.O6.O5.R2?.)R9.$:2.)P,(33.(1.(4.R:.$:2.)R7.)(1.(30.&40.R2<.)R:.))P,(73.O7.(;.O6.)(3>.O7.O6.O5.R31.)R=.R;.$:2.)P,(0.(1.=R:.)(7.R:.(85.+2.+1?.)))P,(36.O7.R?.R:.(30.&40.R2?.))P,(1.(37.O6.)R;.)P,(1.R<.(38.(38.(30.&40.R31.)+<0.)(39.O6.)))P,(1.(30.&40.R32.)(31.O7.O6.O5.R36.))P,(=.$6.(>.(30.&40.R33.)+10.)=)P,(=.(21.&40.)R32.(3:.&40.(3;.O6.)))P,(3<.O7.R15.)P,(=.$6.(>.(30.&40.R37.)+2.)=)P,(1.(4.(3?.O7.O6.O5.R3;.)$:3.)$41.)P,(44.O6.R16.$:2.R12.)P,(1.(4.(46.O7.O6.O5.R3=.)(:4.R13.))$48.)P,(1.(4.(49.R3=.)$:8.)$4;.)P,(=.(21.&40.)R33.(3:.&40.R19.))P,(=.(21.&40.)R33.(3:.&40.R18.))(4<.O7.(:9.O7.O6.O5.O4.O3.O2.R3>.R3=.R3<.R3;.R37.R36.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R41.R40.R3?.R1;.R1:.R19.R18.R17.R1=.R1<.)(4?.(50.(51.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R1?.(3:.&40.O1.)R1>.(52.(21.&40.))R1=.(53.O7.))R1<.))")
(* [comment removed for export] *).
