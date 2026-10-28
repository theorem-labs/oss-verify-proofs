(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_core_bitlen U_mpi_bitlen U_mpi_core_shift_l U_mpi_add_abs_W.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_shift_l () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "shift_l_n"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.binop_keep"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "shift_l_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.XJ"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "sl_frame"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen"].


Definition U_MPI_SHIFT_L : Z := 0x20018.

(* [comment removed for export] *)
Notation MPI_SHIFT_L_STACK := 112 (only parsing).

(* [comment removed for export] *)
Definition limbs_of_bits (i : Z) : Z := i / 32 + (if i mod 32 =? 0 then 0 else 1).
Definition shift_l_n (count : Z) (dX : mpd) : Z :=
  if md_n dX * 32 <? core_bitlen (md_limbs dX) (md_n dX) + count
  then limbs_of_bits (core_bitlen (md_limbs dX) (md_n dX) + count) else md_n dX.

Definition shift_l_R (count : Z) (dX : mpd) (LB : list blk) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_shift_l ()) "(0.(1.(0.(2.$3.O2.=)(0.(2.$3.(4.O1.)(5.(4.O4.)(6.+2.O5.)))(0.(2.$3.(7.O1.)(7.O4.))(2.$3.(8.O1.)(9.O5.O4.)))))(2.$3.O2.$:.))(;.O3.O4.O1.))")
(* [comment removed for export] *).

Definition mpi_shift_l_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_shift_l ()) "Pra,(<.&40.)Psp,(<.&40.)Pgp,(<.&40.)Ptp,(<.&40.)Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Ps0,(<.&40.)Ps1,(<.&40.)Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Ps2,(<.&40.)Ps3,(<.&40.)Ps4,(<.&40.)Ps5,(<.&40.)Ps6,(<.&40.)Ps7,(<.&40.)Ps8,(<.&40.)Ps9,(<.&40.)Ps10,(<.&40.)Ps11,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)PF,(=.&5.(<.&40.))Pfc,(<.&20.)Pm,P,(<.&40.)(>.(<.&8.))Pmo,$?.Ph,(10.O5.O4.O3.)PLB,(11.$12.)PdX,$13.Pcount,$3.Plo,$3.P,(14.O5.O4.O3.R5.R4.R7.R6.)P,(15.O5.R8.R5.R4.)P,(16.(2.$17.(18.R5.)$19.))P,(1:.O4.R7.(1;.&40.R2:.)(1<.O5.O4.O3.R8.)R6.)P,(0.(1=.=R6.)(1=.R6.(6.+2.+20.)))P,P,(16.(2.$17.(18.R8.)$1>.))(1.(1=.(1?.(20.R9.)(5.+4.(8.R9.)))R7.)(1=.(1;.&40.R2=.)(20.R9.)))P,(21.O5.R=.R7.(1;.&40.R2=.))P,(1=.R8.(22.(22.(1;.&40.R2>.)+70.)(23.O4.)))P,(1=.(24.O4.)R9.)P,(1=.(1;.&40.R30.)(1<.O5.O4.O3.R>.))P,(2.$3.(25.(1;.&40.R31.)+10.)=)P,(1=.(26.O4.)(24.O4.))P,(2.(<.&40.)R31.(27.&40.(28.O4.)))P,(29.O5.R14.)P,(2:.O5.O4.R15.)P,(2;.O4.O1.+8.)P,(2.$3.(25.(1;.&40.R38.)+2.)=)P,(2.(<.&40.)R30.(27.&40.(2<.R14.)))P,(2.(<.&40.)R30.(27.&40.R14.))(2=.O5.R19.(2>.O5.O4.O3.R3;.R3:.R39.R38.R34.R33.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1<.R1;.R18.R17.R16.(2?.R15.R16.R17.)R14.R1:.R19.)(30.(31.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R1<.(27.&40.O2.)R1;.(32.(<.&40.))R1:.(33.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition sl_frame (j0 : list byte) (ra s0 s1 s2 s3 : word) : list cell :=
  [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma u32arr_nil : forall segs m, u32arr segs m 0 [].
Proof. intros. split; [split; [lia| split; [cbn; lia| intros i Hi; cbn in Hi; exfalso; lia]]| split; [lia| split; [cbn; lia| intros i Hi; exfalso; cbn in Hi; lia]]]. Qed.

(* [comment removed for export] *)
Lemma bits_to_limbs_ge : forall i, 0 <= i -> i <= 32 * (i ≫ 5 + (if Z.land i 31 =? 0 then 0 else 1)).
Proof.
  intros i Hi. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  destruct (Z.eqb_spec (i mod 32) 0); lia.
Qed.

Lemma lor_land3_0 : forall a b, a mod 4 = 0 -> b mod 4 = 0 -> Z.land (Z.lor a b) 3 = 0.
Proof.
  intros a b Ha Hb. rewrite Z.land_lor_distr_l. change 3 with (Z.ones 2).
  rewrite !Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Ha, Hb. reflexivity.
Qed.
Local Ltac lor_land_zero :=
  lazymatch goal with
  | |- context [Z.land (Z.lor ?a ?b) 3] => rewrite (lor_land3_0 a b) by (Z.div_mod_to_equations; lia)
  end.
Local Ltac if_false_x :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      let E := fresh "E" in
      assert (E : c = false) by (unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; rewrite ?unsigned_lit by lia; first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia | reflexivity]);
      rewrite E; cbv_concl_iota; clear E
  end.
Local Ltac land7_zero :=
  lazymatch goal with
  | |- context [Z.land ?p 7] => let E := fresh "E" in
      assert (E : Z.land p 7 = 0) by (change (Z.land p 7) with (Z.land p (Z.ones 3)); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia);
      rewrite E; clear E
  end.

(* [comment removed for export] *)
Section S.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  Section Body.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (lo : Z) (MSF : Z) (j0 : list byte) (count : Z)
              (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own).
    Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
    Hypothesis MSFE : MSF = U_MEMSET_FUNC.
    Hypothesis CA : const_at L MSF 8.
    Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
    Hypothesis SPA : bv_unsigned sp mod 16 = 0.
    Hypothesis SLO2 : lo <= bv_unsigned sp - 112 - hl_stack L.
    Hypothesis RAE : bv_unsigned ra mod 2 = 0.
    Hypothesis CNT : 0 <= count <= 2^32.
    Local Notation FRAME := (sl_frame j0 ra s0 s1 s2 s3).
    Local Notation POST := (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (shift_l_R count dX LB) lo m mo).
    Hypothesis JCX : JC usegs L HI h LB m mo dX sp lo 48 FRAME.

    Local Ltac jc_open := pose proof JCX as [HLS' SW' DIMG' HND' ROIMG' DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
    Local Notation XJ0 := (XJ usegs L HI h LB m mo dX sp lo 48 FRAME []).
    Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1 NM1]; cbn [app] in HH1.

    (* [comment removed for export] *)
    #[using="JCX"] Lemma sl_ret : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shift_l ()) "Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Praj,(<.&40.)Px8,(<.&40.)Px9,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Px18,(<.&40.)Px19,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Phc,(10.$34.VL,VHI,)PLBc,(11.$12.)Pmc,P,(<.&40.)(>.(<.&8.))Pmoc,$?.PdXc,$13.Pr,$3.P,(35.$34.VL,VHI,Vh,VLB,Vm,Vmo,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+30.(37.Vj0,Vra,Vs0,Vs1,Vs2,Vs3,)(38.$12.)R6.R5.R4.R3.R2.)P,(1.(0.(2.$3.R2.=)(0.(2.$3.(4.R3.)(5.(4.(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))(6.+2.Vcount,)))(0.(2.$3.(7.R3.)VsX,)(2.$3.(8.R3.)(9.Vcount,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))))))(2.$3.R2.$:.))(2=.$34.R5.(2>.$34.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(2?.Vcount,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,)Vlo,Vm,Vmo,)(30.(31.R18.(27.&40.(22.(1;.&40.Vsp,)+30.))Vgp,Vtp,R1;.R1:.R19.R17.R16.(27.&40.R3.)R15.R14.R13.R12.R11.R10.R?.R>.R=.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(27.&40.+200><.)Vfc,(32.(<.&40.))R6.(33.$34.)))")
(* [comment removed for export] *).
    Proof.
      intros until r. intros J HR. jc_open. xj_open J.
      pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (_ & _ & _ & MK & _).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      unfold sl_frame in FR1.
      pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
      do 6 zstep.
      replace (Z_to_bv 64 (bv_unsigned sp - 48 + 48)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia). rewrite Z_to_bv_bv_unsigned.
      zstep. apply aevtM_done. eapply xj_post; [exact JCX| exact J|].
      split; [exact HR|]. split; [exact AD1|]. split; [exact PD1|]. split; [exact FRS1| exact NM1].
    Qed.

    (* [comment removed for export] *)
    #[using="HLS SPA SLO2 CNT JCX"] Lemma sl_tail : forall (t0 t1 t2 raj a0 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word) hc LBc mc moc xs p (n : Z),
      XJ0 hc LBc mc moc (mkMPD X sX n p xs padX (if n =? 0 then ownX else LHeap)) -> (n = 0 -> p = 0 /\ xs = []) ->
      lval xs n * 2 ^ count < 2 ^ (32 * n) \/ n = 0 -> limbs_val xs = limbs_val xs0 -> n = shift_l_n count dX ->
      aevtM usegs moc POST
        (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 count) (Z_to_bv 64 X) a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x200dc) fc None mc (seg_rom usegs)).
    Proof.
      intros until n. intros J Z0 FIT HV HN. jc_open.
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof alloc_ceiling_bounds as ACV.
      pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof MX1 as [(CX1 & _) SGX]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
      pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
      zstep. zstep. zstep.
      pose proof U_mpi_core_shift_l_spec as SPc. unfold mpi_core_shift_l_stmt, U_MPI_CORE_SHIFT_L in SPc.
      destruct (Z.eqb_spec n 0) as [N0|NZ].
      - (* [comment removed for export] *)
        destruct (Z0 N0) as [-> ->]. apply eq_sym in HN. rewrite N0 in HN. subst n.
        eapply aevtM_cut_evt; [exact MK1| eapply SPc with (xs := []) (lo := lo) (n := 0) (X := 0) (cnt := count);
          rewrite ?(unsigned_lit (bv_unsigned sp - 48)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; try (clear - CNT SLO2 SPA SPB HLS ACL ACP; unfold MPI_CORE_SHIFT_L_STACK; lia)|].
        + apply u32arr_nil.
        + exact ST1.
        + left. cbn. clear - ACL ACP SLO2 HLS. lia.
        + exact MI1.
        + cbv beta. intros ms' PO. unfold mpi_core_shift_l_post in PO.
          ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m2 & xs' & -> & MU2 & WM2 & MI2 & ARR2 & LEN2 & _ & _ & ST2).
          rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in MU2, ST2 by (clear - SPB SLO HLS ACL ACP; lia). unfold MPI_CORE_SHIFT_L_STACK in MU2.
          lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
          destruct xs'; [| exfalso; cbn in LEN2; clear - LEN2; lia].
          assert (J2 : XJ0 hc LBc m2 moc (mkMPD X sX 0 0 [] padX ownX)).
          { constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption.
            - eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. unfold sl_frame. cbn. clear - SLO2 HLS ACL ACP; lia.
            - eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH1| exact MU2| exact WM2| exact ACL|].
              intros a Ha NO. cbn in NO. left. rewrite HT1. clear - NO HTOP SLO2 HLS. lia.
            - eapply statics_ok_munch; [exact SOK1| exact MU2|]. intros a Hd NW. cbn. clear - Hd DHI ACL SLO2 HLS. lia.
            - eapply mpd_at_munch_any; [exact MX1| exact MU2| exact WM2| cbn; clear - XS SLO2 HLS X0; lia| cbn [md_own md_p md_n]; intros _; cbn; clear - SLO2 HLS ACL ACP; lia].
            - eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc Ho. cbn. split; [clear; lia|]. split; [| exact I].
              pose proof (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _].
              destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]]; [clear - C SLO2 HLS; lia| clear - C1 DHI ACL SLO2 HLS; lia|].
              pose proof (proj1 (Forall_forall _ _) HBR0 _ Hq) as (_ & _ & _ & R3 & _). cbn in R3, R. clear - R R3 ACL SLO2 HLS. lia. }
          pose proof (munch_refl ([] : list ivl) m2) as MU'. pose proof (wmono_refl usegs m2) as WM'.
          zstep. eapply sl_ret; [exact J2|]. left. split; [reflexivity|]. split; [| split; [reflexivity| symmetry; exact HN]].
          unfold mpd_val. cbn [md_sg md_limbs]. rewrite <- HV. cbn [limbs_val]. rewrite !Z.mul_0_r, Z.mul_0_l. reflexivity.
      - ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & ARR1 & P0 & PC & PI).
        eapply aevtM_cut_evt; [exact MK1| eapply SPc with (xs := xs) (lo := lo) (n := n) (X := p) (cnt := count);
          rewrite ?(unsigned_lit (bv_unsigned sp - 48)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; try (clear - CNT SLO2 SPA SPB HLS ACL ACP NR1 LEN1; unfold MPI_CORE_SHIFT_L_STACK; lia)|].
        + exact ARR1.
        + clear - XPAL. Z.div_mod_to_equations. lia.
        + right; exact P0.
        + clear - PC ACV N1. lia.
        + exact ST1.
        + left. rewrite LEN1. clear - PC ACL. lia.
        + exact MI1.
        + cbv beta. intros ms' PO. unfold mpi_core_shift_l_post in PO.
          ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m2 & xs' & -> & MU2 & WM2 & MI2 & ARR2 & LEN2 & SK2 & LV2 & ST2).
          rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in MU2, ST2 by (clear - SPB SLO HLS ACL ACP; lia). unfold MPI_CORE_SHIFT_L_STACK in MU2.
          lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
          pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J MU2 WM2 MI2 ST2
                        ltac:(intros a NO; destruct (outside_dec [(p, p + 4 * n); (bv_unsigned sp - 48 - 48, bv_unsigned sp - 48)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O SLO2 HLS; lia])
                        ltac:(cbn; clear - PC ACL SLO HLS; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H XS SLO2 HLS; lia) ARR2 LEN2) as J2.
          pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK2.
          pose proof (munch_refl ([] : list ivl) m2) as MU'. pose proof (wmono_refl usegs m2) as WM'.
          zstep. eapply sl_ret; [exact J2|]. left. split; [reflexivity|]. split; [| split; [reflexivity| exact HN]].
          unfold mpd_val. cbn [md_sg md_limbs]. rewrite <- HV.
          destruct FIT as [FIT|FIT]; [| exfalso; exact (NZ FIT)].
          rewrite (limbs_val_split xs n), (limbs_val_split xs' n) by (rewrite <- ?LEN2 in *; clear - NR1 LEN1 LEN2; lia). rewrite SK2, LV2.
          rewrite Z.mod_small by (pose proof (lval_range xs n ltac:(clear - NR1; lia)); clear - FIT H CNT; nia).
          assert (TL : limbs_val (skipn (Z.to_nat n) xs) = 0).
          { rewrite skipn_all2; [reflexivity|]. clear - LEN1; lia. }
          rewrite TL. clear; lia.
    Qed.
    (* [comment removed for export] *)
    #[using="HFREE HCALLOC HLS SW DIMG MSF MSFE CA TP SPA SLO2 CNT JCX"] Lemma sl_after_bitlen : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shift_l ()) "Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Praj,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Pm1,P,(<.&40.)(>.(<.&8.))P,(35.$34.VL,VHI,Vh,VLB,Vm,Vmo,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+30.(37.Vj0,Vra,Vs0,Vs1,Vs2,Vs3,)(38.$12.)Vh,VLB,R1.Vmo,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))(2=.$34.Vmo,(2>.$34.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(2?.Vcount,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,)Vlo,Vm,Vmo,)(30.(31.R>.(27.&40.(22.(1;.&40.Vsp,)+30.))Vgp,Vtp,R11.R10.R?.(27.&40.Vcount,)(27.&40.VX,)(27.&40.(39.Vxs0,VnX,))R=.R<.R;.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(27.&40.+20050.)Vfc,(32.(<.&40.))R2.(33.$34.)))")
(* [comment removed for export] *).
    Proof.
      intros until m1. intros J0. jc_open.
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof alloc_ceiling_bounds as ACV.
      pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof J0 as JX; xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof MX1 as [(CX1 & _) SGX]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
      pose proof (core_bitlen_range xs0 nX ltac:(clear - NR1; lia)) as BR.
      pose proof (core_bitlen_val xs0 nX ltac:(clear - NR1; lia)) as BV.
      set (bits := core_bitlen xs0 nX) in *.
      pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl usegs m1) as WM.
      zstep. rewrite zx16_small by (clear - NR1; lia). zstep. zstep. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 5) with 32.
      zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        rewrite ?Z.mod_small in K0 by (clear - BR NR1 CNT; lia).
        eapply sl_tail; [| | | reflexivity| unfold shift_l_n; cbn [md_n md_limbs]; fold bits; destruct (Z.ltb_spec (nX * 32) (bits + count)) as [LT|GE]; [exfalso; clear - LT K0; lia| reflexivity]].
        - destruct (Z.eqb_spec nX 0) as [E|NE]; [exact J0|]. destruct ownX; [destruct (OWN0 eq_refl); exfalso; clear - NE H0; lia| exact J0| exfalso; exact (NST eq_refl)].
        - intros E. destruct ownX; [destruct (OWN0 eq_refl) as [P0 _]; split; [exact P0| destruct xs0; [reflexivity| exfalso; cbn [length] in LEN1; clear - LEN1 E; lia]]| | exfalso; exact (NST eq_refl)].
          ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & _). exfalso. clear - N1 E. lia.
        - destruct (Z.eq_dec nX 0) as [E|NE]; [right; exact E| left].
          destruct BV as [[B0 L0]|[B1 [L1 L2]]]; [rewrite L0; clear - NE NR1; apply Z.pow_pos_nonneg; lia|].
          apply (Z.lt_le_trans _ (2 ^ bits * 2 ^ count)); [clear - L2 CNT; apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; lia| exact L2]|].
          rewrite <- Z.pow_add_r by (clear - BR CNT; lia). apply Z.pow_le_mono_r; clear - K0 BR CNT; lia. }
      (* [comment removed for export] *)
      rewrite ?Z.mod_small in K0 by (clear - BR NR1 CNT; lia).
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      pose proof (bits_to_limbs_ge (bits + count) ltac:(clear - BR CNT; lia)) as LGE.
      replace (Z.b2z (0 <? Z.land (bits + count) 31)) with (if Z.land (bits + count) 31 =? 0 then 0 else 1)
        by (pose proof (Z.land_nonneg (bits + count) 31) as LN; destruct (Z.land (bits + count) 31); [reflexivity| reflexivity| exfalso; clear - LN; lia]).
      set (limbs := (bits + count) ≫ 5 + (if Z.land (bits + count) 31 =? 0 then 0 else 1)) in *.
      assert (LD : limbs = limbs_of_bits (bits + count)).
      { subst limbs. unfold limbs_of_bits. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 5) with 32. change 31 with (Z.ones 5). rewrite Z.land_ones by (clear; lia). reflexivity. }
      assert (LR : nX < limbs /\ 1 <= limbs <= (bits + count) / 32 + 1).
      { rewrite LD in *. unfold limbs_of_bits in *.
        destruct ((bits + count) mod 32 =? 0); clear - K0 LGE BR CNT NR1; Z.div_mod_to_equations; nia. }
      assert (HN : limbs = shift_l_n count dX).
      { unfold shift_l_n; cbn [md_n md_limbs]; fold bits. destruct (Z.ltb_spec (nX * 32) (bits + count)) as [LT|GE]; [exact LD| exfalso; clear - GE K0; lia]. }
      clearbody limbs. clear LD.
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *)
        rewrite ?Z.mod_small in K1 by (clear - LR BR CNT NR1; Z.div_mod_to_equations; lia).
        eapply sl_ret; [exact J0| right; reflexivity]. }
      rewrite ?Z.mod_small in K1 by (clear - LR BR CNT NR1; Z.div_mod_to_equations; lia).
      zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?Z.mod_small in K2 by (clear - LR K1 NR1; lia); clear - K2 LR; lia|].
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
      eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := limbs) (sz := 4) (lo := lo);
        rewrite ?(unsigned_lit (bv_unsigned sp - 48)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity;
        clear - SLO HLS ACL ACP HTOP HT1 K1 LR NR1 SPB; try lia | ].
      intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      ddestruct PO as (MI2 & ST2 & MF2 & HPc & h2 & HT2 & RES2).
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
      clear MU WM.
      destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
      { (* [comment removed for export] *)
        pose proof (xj_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J0 MI2 ST2 MF2 HPc HT2 HH2) as J2.
        pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
        pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
        zstep. zstep. zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
        eapply sl_ret; [exact J2| right; reflexivity]. }
      (* [comment removed for export] *)
      replace (limbs * 4) with (4 * limbs) in * by (clear; lia).
      destruct (xj_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J0 MI2 ST2 MF2 HPc HT2 HH2 HBA HNEW ltac:(cbn [md_n]; clear - K1 LR; lia)) as [J2 F2].
      dpose HBA as (An0 & An16 & _ & AnC & AnI). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      clear HPc JX MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 CX1 AD1 PD1 NM1.
      pose proof J2 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof MX1 as [(CX2 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      zstep. zstep. zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ An0 AnC ACV K1 LR; lia|].
      zstep. zstep. if_cases KP; zify_cond KP.
      { (* [comment removed for export] *)
        assert (EO : ownX = LNull).
        { destruct ownX; [reflexivity| | exfalso; exact (NST eq_refl)]. exfalso. ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & _ & _ & _ & P0 & PC & _). rewrite Z.mod_small in KP by (clear - N1 P0 PC ACV; lia). clear - KP P0. lia. }
        pose proof (xg_null _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 EO) as D2.
        destruct (OWN0 EO) as [EP EN].
        clear MU WM. pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
        clear HH2 HNEW SOK1 ST2 FR1 HPX1 MI1.
        zstep. zstep. zstep.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D2 MU WM MI2 CX2) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
        eapply sl_tail with (xs := repeat (Z_to_bv 64 0) (Z.to_nat limbs)) (p := An) (n := limbs);
          [replace (limbs =? 0) with false by (symmetry; apply Z.eqb_neq; clear - LR; lia); exact J5| intros E; exfalso; clear - E LR; lia| | | exact HN].
        - left. unfold lval. rewrite firstn_all2 by (rewrite repeat_length; clear; lia). rewrite limbs_val_repeat0, Z.mul_0_l. apply Z.pow_pos_nonneg; clear - LR; lia.
        - rewrite limbs_val_repeat0. destruct xs0; [reflexivity| exfalso; cbn [length] in LEN1; clear - LEN1 EN; lia]. }
      (* [comment removed for export] *)
      assert (EO : ownX = LHeap).
      { destruct ownX; [| reflexivity| exfalso; exact (NST eq_refl)]. exfalso. destruct (OWN0 eq_refl) as [EP _]. apply KP. rewrite EP. reflexivity. }
      ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & _ & P0 & PC & PI).
      destruct (xg_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 EO) as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP.
      clear HH1 HH2 HNEW SOK1 FR1 HPX1.
      zstep. zstep. lor_land_zero. zstep. if_false.
      zstep. rewrite zx16_small by (clear - NR1; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
      pose proof U_memcpy_spec as SPm. unfold memcpy_stmt in SPm.
      assert (U1 : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; clear - An0 AnC ACV K1 LR; lia).
      assert (U2 : bv_unsigned (Z_to_bv 64 pX) = pX) by (apply unsigned_lit; clear - P0 PC ACV N1; lia).
      assert (U3 : bv_unsigned (Z_to_bv 64 (nX * 4)) = nX * 4) by (apply unsigned_lit; clear - N1 LR K1; lia).
      eapply aevtM_cut_evt; [ exact MK2 | eapply SPm with (src := u32s xs0); rewrite ?U1, ?U2, ?U3;
        [ exact SBY | rewrite SLEN; clear; lia | replace (Z.to_nat (nX * 4)) with (4 * length (firstn (Z.to_nat nX) (repeat (Z_to_bv 64 0) (Z.to_nat limbs))))%nat by (rewrite DLEN; clear; lia); exact DST
        | clear - SEP; lia | exact MI2 ] | ].
      clear SPm. unfold memcpy_post. cbv beta. intros ms' PO.
      ddestruct PO as (z0 & z1 & z2 & za1 & za2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & m3 & E & MUd & WMd & MI3 & PA3 & _). subst ms'.
      rewrite ?U1, ?U2, ?U3 in MUd. rewrite ?U1, ?U2, ?U3 in PA3.
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      replace (An + nX * 4) with (An + 4 * nX) in MUd by (clear; lia). replace (Z.to_nat (nX * 4)) with (Z.to_nat (4 * nX)) in PA3 by (clear; lia).
      destruct (xg_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ J2 F2 EO MUd WMd MI3 PA3) as [J3 F3]. cbn [md_limbs md_n] in F3.
      clear J2 F2 MU WM DST SBY CX2 ST2 MI2 MK2 MI1 ST1 HT1 MF1 MX1 NS1 OUT1 FRS1 XP1 AD1 PD1 NM1 JX.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      pose proof J3 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK3.
      destruct (xg_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J3 F3 EO) as (ZIN & ZCH & ZLEN & ZB). cbn [md_p md_n md_limbs] in ZIN, ZCH, ZLEN, ZB.
      (* [comment removed for export] *)
      pose proof MX1 as [(CX3 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
      zstep. rewrite zx16_small by (clear - N1 NR1 LR K1; lia). zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
      eapply aevtM_cut.
      { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pX) (len := 4 * nX) (lo := lo) (junk := u32s xs0);
          rewrite ?(unsigned_lit (bv_unsigned sp - 48)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity.
        all: try (right; split; [exact ZIN|]; rewrite <- ZLEN; exact ZCH).
        all: try exact ZB.
        all: try (rewrite HT1; clear - HTOP; lia).
        all: try (rewrite <- MSFE; exact CA).
        all: try (f_equal; clear; lia).
        all: clear - SLO SPA SPB HLS ACL ACP; lia. }
      cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & mo4 & h4 & E & PO). injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      ddestruct PO as (MI4 & ST4 & MF4 & HT4 & HH4 & PX4 & SOK4).
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
      pose proof (xg_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ J3 F3 EO MI4 ST4 MF4 HT4 HH4 PX4 SOK4) as D4.
      pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
      clear J3 F3 MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 AD1 PD1 NM1 MU WM MK3 HH4 PX4 ZCH PA3 MUd WMd MI3 SOK4 JX.
      pose proof (xd_struct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D4) as CX4. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX4. unfold mpi_cells in CX4.
      pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
      zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D4 MU WM MI4 CX4) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
      eapply sl_tail with (xs := xs0 ++ skipn (Z.to_nat nX) (repeat (Z_to_bv 64 0) (Z.to_nat limbs))) (p := An) (n := limbs);
        [replace (limbs =? 0) with false by (symmetry; apply Z.eqb_neq; clear - LR; lia); exact J5| intros E; exfalso; clear - E LR; lia| | | exact HN].
      - left. rewrite skipn_repeat. unfold lval. rewrite firstn_all2 by (rewrite length_app, repeat_length; clear - LEN1 LR; lia). rewrite limbs_val_app_zeros.
        unfold lval in BV. rewrite firstn_all2 in BV by (clear - LEN1; lia).
        destruct BV as [[B0 L0]|[B1 [L1 L2]]]; [rewrite L0, Z.mul_0_l; apply Z.pow_pos_nonneg; clear - LR; lia|].
        apply (Z.lt_le_trans _ (2 ^ bits * 2 ^ count)); [clear - L2 CNT; apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; lia| exact L2]|].
        rewrite <- Z.pow_add_r by (clear - BR CNT N1; lia). apply Z.pow_le_mono_r; clear - LGE BR CNT; lia.
      - rewrite skipn_repeat, limbs_val_app_zeros. reflexivity.
    Qed.

    (* [comment removed for export] *)
    #[using="HFREE HCALLOC HLS SW DIMG MSF MSFE CA TP SPA SLO2 CNT JCX"] Lemma sl_body : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shift_l ()) "Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Pm1,P,(<.&40.)(>.(<.&8.))P,(35.$34.VL,VHI,Vh,VLB,Vm,Vmo,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+30.(37.Vj0,Vra,Vs0,Vs1,Vs2,Vs3,)(38.$12.)Vh,VLB,R1.Vmo,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))(2=.$34.Vmo,(2>.$34.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(2?.Vcount,(36.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,)Vlo,Vm,Vmo,)(30.(31.Vra,(27.&40.(22.(1;.&40.Vsp,)+30.))Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(27.&40.VX,)(27.&40.Vcount,)R<.R;.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(27.&40.+20034.)Vfc,(32.(<.&40.))R2.(33.$34.)))")
(* [comment removed for export] *).
    Proof.
      intros until m1. intros J0. jc_open.
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof alloc_ceiling_bounds as ACV.
      pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof J0 as JX; xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof MX1 as [(CX1 & _) SGX]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
      pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl usegs m1) as WM.
      zstep. zstep. land7_zero. zstep. if_false.
      zstep. zstep. zstep. rewrite zx16_small by (clear - NR1; lia). zstep.
      (* [comment removed for export] *)
      destruct (Z.eq_dec nX 0) as [N0|NZ].
      - eapply aevtM_cut_evt; [exact MK1| rewrite N0; eapply U_core_bitlen_null with (A := pX); [exact MI1| | reflexivity| reflexivity]|].
        { destruct ownX; [destruct OWN0 as [-> _]; [reflexivity| clear; lia]| | exfalso; exact (NST eq_refl)].
          ddestruct (OWN1 ltac:(discriminate)) as (_ & _ & _ & _ & _ & P0 & PC & _). clear - P0 PC ACV NR1. lia. }
        cbv beta. intros ms' PB. unfold mpi_core_bitlen_post in PB.
        ddestruct PB as (b0 & b1 & b2 & ba0 & ba1 & ba2 & ba3 & ba4 & ba5 & ba6 & ba7 & b3 & b4 & b5 & b6 & -> & _ & _ & _ & ->).
        lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
        replace (core_bitlen [] nX) with (core_bitlen xs0 nX) by (rewrite N0; reflexivity).
        eapply sl_after_bitlen. exact J0.
      - ddestruct (OWN1 ltac:(destruct ownX; [destruct (OWN0 eq_refl); exfalso; clear - NZ H0; lia| discriminate| discriminate])) as (EO & N1 & XIN & XPAL & ARR1 & P0 & PC & PI).
        pose proof U_mpi_core_bitlen_spec as SPb. unfold mpi_core_bitlen_stmt, U_MPI_CORE_BITLEN in SPb.
        eapply aevtM_cut_evt; [exact MK1| eapply (SPb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pX nX xs0);
            [apply u32arr_ro; exact ARR1| clear - NR1; lia| clear - LEN1; lia| clear - XPAL; Z.div_mod_to_equations; lia| exact P0| exact MI1| reflexivity| reflexivity]|].
        cbv beta. intros ms' PB. unfold mpi_core_bitlen_post in PB.
        ddestruct PB as (b0 & b1 & b2 & ba0 & ba1 & ba2 & ba3 & ba4 & ba5 & ba6 & ba7 & b3 & b4 & b5 & b6 & -> & _ & _ & _ & ->).
        lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
            replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
        eapply sl_after_bitlen. exact J0.
    Qed.
  End Body.
End S.

(* [comment removed for export] *)
Section Spec.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem U_mpi_shift_l_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_shift_l_stmt usegs L HI U_MPI_SHIFT_L MSF.
  Proof.
    intros MSF MSFE. unfold mpi_shift_l_stmt, U_MPI_SHIFT_L. intros until lo.
    intros HH MX NST XW CNT XLS ST SLO2 ACL HTOP SPA DHI TP MI SOK CA RAE -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    destruct dX as [X sX nX pX xs0 padX ownX]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof MX as [(CX0 & XAL & X0 & LENX & NRX & OWNX) SGX]. unfold mpi_cells in CX0. unfold MPI_MAX_LIMBS in NRX.
    pose proof (rw_cells_bound _ _ _ _ CX0) as XBD. cbn [cells_size csize Nat.add] in XBD.
    dpose XW as (XCW & XDW & XP). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO2 HLS; lia)) as XS.
    (* [comment removed for export] *)
    carve_frame 48%nat ST.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HHc. clear HH. pose proof (conj SOK I) as SOKc. clear SOK.
    do 6 zstep. zstep; if_false_x.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by (clear; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    match type of FR with rw_cells _ _ _ (CB _ ?jk :: _) => set (j0 := jk) in FR end.
    change (rw_cells usegs m0 (bv_unsigned sp - 48) (sl_frame j0 ra s0 s1 s2 s3)) in FR.
    destruct HHc as [HH _]. destruct SOKc as [SOK _].
    assert (JCX : JC usegs L HI h LB m mo (mkMPD X sX nX pX xs0 padX ownX) sp lo 48 (sl_frame j0 ra s0 s1 s2 s3)).
    { constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption; try reflexivity; try (clear; lia). clear - SLO2. lia. }
    assert (J0 : XJ usegs L HI h LB m mo (mkMPD X sX nX pX xs0 padX ownX) sp lo 48 (sl_frame j0 ra s0 s1 s2 s3) [] h LB m0 mo (mkMPD X sX nX pX xs0 padX ownX)).
    { constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption; try reflexivity.
      - eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact MU| exact WM| exact ACL|].
        intros a Ha NO. cbn in NO. left. clear - NO HTOP SLO2 HLS. lia.
      - apply mo_frame_refl.
      - eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Hd NW. cbn. split; [clear - Hd DHI ACL SLO2 HLS; lia| exact I].
      - eapply mpd_at_munch_any; [exact MX| exact MU| exact WM| cbn; split; [clear - XS SLO2 HLS; lia| exact I]|].
        cbn [md_own md_p md_n]. intros ON. cbn. split; [| exact I]. destruct (XLS ON); clear - H SLO2 HLS; lia.
      - apply mpd_out_refl. exact NST.
      - intros b Hb. left. exact Hb.
      - eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| clear - ACL SLO2 HLS; lia]. }
    eapply (sl_body L HI HFREE HCALLOC HLS SW DIMG) with (MSF := MSF); try eassumption.
  Qed.
End Spec.
