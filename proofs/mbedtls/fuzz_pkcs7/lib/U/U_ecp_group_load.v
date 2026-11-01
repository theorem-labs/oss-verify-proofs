(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_platform_zeroize_proof U_mpi_free U_mpi_init U_mpi_addsub U_mpi_lset U_mpi_grow U_mpi_core_bitlen U_mpi_bitlen U_ecp_group_init U_ecp_group_free U_ecp_defs U_ecp_statics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ecp_group_load () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.is_sw"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.grp_sw"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.grp_mx"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_init"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_zero"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Logic.iff"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_free.grp_free_LB"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "gl_result"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_GROUP_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "ecp_group_load_post"].


(* [comment removed for export] *)
Notation ECP_GROUP_LOAD_STACK := 112 (only parsing).
Definition MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE : Z := -0x4E80.

(* [comment removed for export] *)
Definition gl_result (ca : Z -> curve_addrs) (ONE : Z) (id A : Z) (r : Z) (g' : ecp_grp) (NB : list blk) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load ()) "(0.(1.(2.$3.O3.=)(1.(2.$4.(5.O5.)$6.)(1.(1.(7.+1.O5.)(7.O5.+=.))(1.(2.(8.$9.)O1.(:.$9.))(;.(<.&40.)Lidpad,(<.&40.)(;.(<.&40.)LpP,(<.&40.)(;.(<.&40.)LpA,(<.&40.)(;.(<.&40.)LpB,(<.&40.)(;.(<.&40.)LpX,(<.&40.)(;.(<.&40.)LpY,(<.&40.)(;.(<.&40.)LpZ,(<.&40.)(;.(<.&40.)LpN,(<.&40.)(;.(<.&40.)Lhpad,(<.&40.)(2.$=.O2.(>.O5.A1.O7.O5.O6.O4.R9.R8.R7.R6.R5.R4.R3.R2.R1.)))))))))))))))(0.(1.(2.$3.O3.=)(1.(0.(2.$3.O5.+9.)(2.$3.O5.+=.))(;.(<.&40.)Lidpad,(<.&40.)(;.(<.&40.)LpP,(<.&40.)(;.(<.&40.)LpA,(<.&40.)(;.(<.&40.)LpB,(<.&40.)(;.(<.&40.)LpX,(<.&40.)(;.(<.&40.)LpY,(<.&40.)(;.(<.&40.)LpZ,(<.&40.)(;.(<.&40.)LpN,(<.&40.)(;.(<.&40.)Lhpad,(<.&40.)(;.$3.LPA,$3.(;.$3.LPX,$3.(;.$3.LPZ,$3.(;.(<.&40.)LwA,(<.&40.)(;.(<.&40.)LwX,(<.&40.)(;.(<.&40.)LwZ,(<.&40.)(1.(2.$=.O2.(?.O5.A1.O7.O5.O4.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.))(2.(8.$9.)O1.(10.(11.$3.$3.)(12.$3.$3.R6.+4.)(10.(11.$3.$3.)(12.$3.$3.R5.+4.)(10.(11.$3.$3.)(12.$3.$3.R4.+4.)(:.(11.$3.$3.))))))))))))))))))))))))(0.(1.(2.$3.O3.$13.)(1.(14.(1.(7.+1.O5.)(7.O5.+=.)))(1.(2.(8.$9.)O1.(:.$9.))(;.(<.&40.)Lidpad,(<.&40.)(;.(<.&40.)LpP,(<.&40.)(;.(<.&40.)LpA,(<.&40.)(;.(<.&40.)LpB,(<.&40.)(;.(<.&40.)LpX,(<.&40.)(;.(<.&40.)LpY,(<.&40.)(;.(<.&40.)LpZ,(<.&40.)(;.(<.&40.)LpN,(<.&40.)(;.(<.&40.)Lhpad,(<.&40.)(1.(2.$=.O2.(15.O4.R9.R8.R7.R6.R5.R4.R3.R2.R1.))$16.)))))))))))))(1.(2.$3.O3.$17.)(1.(0.(2.$3.O5.+9.)(2.$3.O5.+=.))(1.(2.(8.$9.)O1.(:.$9.))(2.$=.O2.(18.O4.))))))))")
(* [comment removed for export] *).

Definition ecp_group_load_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (A : Z) (g : ecp_grp) (id lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load ()) "Lc,$19.(;.(<.&40.)Lt0,(<.&40.)(;.(<.&40.)Lt1,(<.&40.)(;.(<.&40.)Lt2,(<.&40.)(;.(<.&40.)La1,(<.&40.)(;.(<.&40.)La2,(<.&40.)(;.(<.&40.)La3,(<.&40.)(;.(<.&40.)La4,(<.&40.)(;.(<.&40.)La5,(<.&40.)(;.(<.&40.)La6,(<.&40.)(;.(<.&40.)La7,(<.&40.)(;.(<.&40.)Lt3,(<.&40.)(;.(<.&40.)Lt4,(<.&40.)(;.(<.&40.)Lt5,(<.&40.)(;.(<.&40.)Lt6,(<.&40.)(;.P,(<.&40.)(1:.(<.&8.))Lm',P,(<.&40.)(1:.(<.&8.))(;.$1;.Lmo',$1;.(;.(1<.O20.O1?.O1>.)Lh',(1<.O20.O1?.O1>.)(;.$3.Lr,$3.(;.$=.Lg',$=.(;.(8.$9.)LNB,(8.$9.)(;.(8.$9.)LLB',(8.$9.)(1.(2.$19.R16.(1=.(1>.(1?.O1:.O19.O18.O17.R15.R14.R13.O16.O15.(20.&40.R4.)R12.R11.R10.R?.R>.R=.R<.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R;.R:.R9.R8.)O:.(21.O1:.)O9.(22.(<.&40.))R7.(23.O20.))R6.))(1.(24.O20.R7.)(1.(25.O20.R7.O3.(26.&40.O19.))(1.(27.O1.R6.)(1.(2.$3.(28.O20.O1?.O1>.R5.)(28.O20.O1?.O1>.O8.))(1.(29.O20.O1?.O1>.R5.R1.R7.R6.)(1.Pb,$9.(2:.(2;.$9.R1.R2.)(0.(2;.$9.R1.R3.)(2;.$9.R1.(2<.O5.O7.))))(1.Pb,$9.P,(2;.$9.R1.R3.)(14.(2;.$9.R2.(2<.O5.O7.)))(1.(2=.O20.O1=.R7.R1.O6.R3.)(1.(2>.(2?.R3.))(1.(2.(8.$9.)(30.R3.)R2.)(1.(31.O1<.O1;.O4.O6.R4.R3.R2.)(1.(32.O20.O1?.(2<.O5.O7.)(26.&40.O19.)(10.(11.$3.$3.)(12.$3.$3.O6.(33.O6.$34.))(:.(11.$3.$3.)))O2.R7.)(35.O20.O1?.R7.)))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_group_load_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load ()) "Pra,(<.&40.)Psp,(<.&40.)Pgp,(<.&40.)Ptp,(<.&40.)Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Ps0,(<.&40.)Ps1,(<.&40.)Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Ps2,(<.&40.)Ps3,(<.&40.)Ps4,(<.&40.)Ps5,(<.&40.)Ps6,(<.&40.)Ps7,(<.&40.)Ps8,(<.&40.)Ps9,(<.&40.)Ps10,(<.&40.)Ps11,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)PF,(36.&5.(<.&40.))Pfc,(<.&20.)Pm,P,(<.&40.)(1:.(<.&8.))Pmo,$1;.Ph,(1<.O8.O7.O6.)PLB,(8.$9.)PA,$3.Pg,$=.Pid,$3.Plo,$3.P,(29.O8.O7.O6.R6.R5.R8.R7.)P,(2=.O8.O5.R9.R6.R5.R4.)P,(2>.(2?.R5.))P,(37.O7.(2<.R6.R8.)(26.&40.R2;.)(28.O8.O7.O6.R9.)R7.$34.)P,(0.(7.(33.R8.$34.)(38.O7.))(7.(39.O7.)R8.))P,(1.(7.=R7.)(3:.R7.(3;.+2.+1?.)))P,(25.O8.R>.R7.(26.&40.R2>.))P,(7.R8.(3<.(3<.(26.&40.R2?.)+70.)(3=.O7.)))P,(7.(3>.O7.)R9.)P,(7.(26.&40.R31.)(28.O8.O7.O6.R?.))P,(2.$3.(3?.(26.&40.R32.)+10.)=)P,(7.(39.O7.)(3>.O7.))P,(2.(<.&40.)R32.(20.&40.(40.O7.)))P,(24.O8.R15.)P,(35.O8.O7.R16.)P,(41.O7.O1.+8.)P,(2.$3.(3?.(26.&40.R39.)+2.)=)P,(2.(<.&40.)R31.(20.&40.R15.))P,(2.(<.&40.)R31.(20.&40.R14.))(42.O8.R1:.(43.O8.O7.O6.O5.O4.O3.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R19.R18.R17.R16.R15.R14.R1;.R1:.)(1>.(1?.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(20.&40.O2.)R1<.(22.(<.&40.))R1;.(23.O8.)))")
(* [comment removed for export] *).

Section GL.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  (* [comment removed for export] *)
  #[using="HLS DIMG"] Lemma sw_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (mo0 mo : Model) (h0 h : HST usegs L HI)
      (LB : list blk) (A : Z) (g : ecp_grp) (id lo : Z) (idpad pP pA pB pX pY pZ pN hpad xra xs1 : word) (fj : list byte),
    let LBf := grp_free_LB g LB in let ca := U_CA id in
    is_sw id = true -> 1 <= id <= 13 ->
    HEAP usegs L HI h LBf m mo -> heap_top usegs L HI h = heap_top usegs L HI h0 -> mo_frame mo0 mo ->
    heap_presx usegs L LBf (bv_unsigned sp) [(A, A + 192)] m0 m ->
    rw_cells usegs m A [C4 (Z_to_bv 64 id); C4 idpad] -> A mod 8 = 0 -> 0 < A ->
    rw_cells usegs m (A + 8) (mpi_cells (ca_P ca) (Z_to_bv 64 1) (Z.of_nat (length (cP id))) pP) ->
    rw_cells usegs m (A + 24) (mpi_cells (if has_A id then ca_A ca else 0) (Z_to_bv 64 1) (if has_A id then Z.of_nat (length (cA id)) else 0) pA) ->
    rw_cells usegs m (A + 40) (mpi_cells (ca_B ca) (Z_to_bv 64 1) (Z.of_nat (length (cB id))) pB) ->
    rw_cells usegs m (A + 56) (mpi_cells (ca_GX ca) (Z_to_bv 64 1) (Z.of_nat (length (cGX id))) pX) ->
    rw_cells usegs m (A + 72) (mpi_cells (ca_GY ca) (Z_to_bv 64 1) (Z.of_nat (length (cGY id))) pY) ->
    rw_cells usegs m (A + 88) (mpi_cells U_ONE (Z_to_bv 64 1) 1 pZ) ->
    rw_cells usegs m (A + 104) (mpi_cells (ca_N ca) (Z_to_bv 64 1) (Z.of_nat (length (cN id))) pN) ->
    rw_cells usegs m (A + 120) [C8 (Z_to_bv 64 (core_bitlen (cP id) (Z.of_nat (length (cP id))))); C8 (Z_to_bv 64 0);
                               C4 (Z_to_bv 64 0); C4 hpad; C8 (Z_to_bv 64 (ca_modp ca)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                               C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    rw_cells usegs m (bv_unsigned sp - 32) [CB 8 fj; C8 s1; C8 s0; C8 ra] ->
    stk usegs m lo (bv_unsigned sp - 32) -> 0 <= lo -> lo <= bv_unsigned sp - 112 - hl_stack L -> (A + 192 <= lo \/ bv_unsigned sp <= A) ->
    client_wrange L LBf (bv_unsigned sp) (heap_top usegs L HI h0) A 192 -> (A + 192 <= hl_data_lo L \/ hl_data_hi L <= A) ->
    alloc_ceiling <= lo -> bv_unsigned sp <= heap_top usegs L HI h0 -> hl_data_hi L <= alloc_ceiling ->
    mem_inv usegs m -> statics_ok usegs L m -> bv_unsigned ra mod 2 = 0 ->
    aevtM usegs mo (ecp_group_load_post usegs L HI U_MT U_CA U_ONE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB A g id lo m0 mo0)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 A) xs1
               (Z_to_bv 64 0) (Z_to_bv 64 (core_bitlen (cN id) (Z.of_nat (length (cN id))))) (Z_to_bv 64 1) (Z_to_bv 64 (ca_T ca)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3c3a8) fc None m (seg_rom usegs)).
  Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m mo0 mo h0 h LB A g id lo
    idpad pP pA pB pX pY pZ pN hpad xra xs1 fj LBf ca
    sw_id id_rng heap_now top_eq mo_fr presx0 c_id a_al a_pos c_P c_A c_B c_GX c_GY c_Z c_N c_tail c_save
    stk_in lo_nn lo_room obj_stk obj_cw obj_data ceil_lo sp_top data_ceil inv_m stat_m ra_even.
  (* Facts about the curve table that hold for every id: read them off U_CA by walking its match. *)
  assert (tbl : (ca_modp (U_CA id) = 0 \/ In (ca_modp (U_CA id), (ca_P (U_CA id), cP id)) U_MT)
                /\ 0 <= ca_modp (U_CA id) < 2 ^ 64 /\ 0 <= ca_T (U_CA id) < 2 ^ 64).
  { clear - id.
    destruct id as [|bits|bits]; [split; [left; reflexivity| cbn; lia]| |split; [left; reflexivity| cbn; lia]].
    repeat (destruct bits as [bits|bits|];
            try solve [ cbv [U_CA cP ca_modp ca_P ca_T];
                        split; [ first [ left; reflexivity
                                       | right; repeat (apply in_eq || apply in_cons) ]
                               | lia ] ]). }
  destruct tbl as [modp_known [modp_rng T_rng]].
  pose proof (heap_mok _ _ _ _ _ _ _ heap_now) as mok.
  pose proof (munch_refl [(A, A + 192)] m) as fp.
  pose proof (wmono_refl usegs m) as wm.
  pose proof (conj I heap_now) as heap_entry. clear heap_now.
  (* The four stores into the group tail: nbits, h, T, T_size. *)
  do 4 step.
  (* Restore ra, s0, s1, pop the frame, return. *)
  fsteps 5%nat.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => rename mm into m_out end.
  destruct heap_entry as [_ heap_entry].
  eapply stk_release in stk_in; [| exact c_save | lia].
  change (Z.of_nat (cells_size [CB 8 fj; C8 s1; C8 s0; C8 ra])) with 32 in stk_in.
  rewrite Z.sub_add in stk_in.
  assert (ceil_sp : alloc_ceiling <= bv_unsigned sp) by lia.
  assert (covered : forall a, 0 <= a < 2 ^ 64 -> ~ outside [(A, A + 192)] a ->
                     client_waddr L LBf (bv_unsigned sp) (heap_top usegs L HI h) a).
  { intros a _ not_out. rewrite top_eq. apply obj_cw. cbn in not_out. lia. }
  pose proof (HEAP_munch _ _ _ _ _ _ _ _ _ _ heap_entry fp wm ceil_sp covered) as heap_out.
  pose proof (heap_presx_of_munch usegs L LBf (bv_unsigned sp) [(A, A + ECP_GROUP_SIZE)] _ _ _ fp wm
                (fun a _ _ out => out)) as presx_run.
  pose proof (heap_presx_trans _ _ _ _ _ _ _ _ presx0 presx_run) as presx_out.
  pose proof (U_curve_statics m_out id inv_m id_rng) as statics_out.
  pose proof (grp_sw_at usegs U_MT m_out LBf ca U_ONE id A idpad pP pA pB pX pY pZ pN hpad sw_id ltac:(lia)
                statics_out modp_known modp_rng T_rng c_id a_al a_pos c_P c_A c_B c_GX c_GY c_Z c_N c_tail)
    as grp_out.
  set (g' := grp_sw id ca U_ONE A idpad pP pA pB pX pY pZ pN hpad) in grp_out.
  assert (no_heap : Forall (fun d => md_own d <> LHeap) (grp_mpds g')).
  { unfold g', grp_mpds, grp_sw, pt_mpds. case (has_A id); repeat constructor; cbn; discriminate. }
  assert (apart_out : mpds_apart (grp_mpds g')).
  { intros d1 d2 in1 _ _ own1 _. destruct (proj1 (Forall_forall _ _) no_heap d1 in1 own1). }
  assert (blocks_out : grp_blocks g' = []).
  { unfold grp_blocks. revert no_heap. generalize (grp_mpds g') as ds.
    induction ds as [|d ds rest]; intros all_nh; [reflexivity|].
    pose proof (Forall_inv all_nh) as own_d. pose proof (Forall_inv_tail all_nh) as tail_nh.
    cbn [flat_map]. rewrite (rest tail_nh), app_nil_r. cbn beta in own_d.
    unfold mpd_blk. destruct (md_own d) eqn:own_eq; try reflexivity. contradiction. }
  assert (res_out : gl_result U_CA U_ONE id A 0 g' []).
  { left. refine (conj eq_refl (conj sw_id (conj id_rng (conj eq_refl _)))). do 9 eexists. reflexivity. }
  assert (same_blocks : forall b, In b LBf <-> In b [] \/ In b (grp_free_LB g LB)).
  { intros b. cbn [In]. tauto. }
  assert (none_new : forall b : blk, In b [] -> ~ In b (grp_free_LB g LB)) by (intros b []).
  rewrite Z.sub_add, Z_to_bv_bv_unsigned.
  finish.
  all: eassumption.
  Qed.
End GL.
