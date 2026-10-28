(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_core_add U_mpi_add_abs_W U_mpi_add_abs_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_add_abs_B () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.XJ"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_add_abs_W.AA_FRAME"; "Corelib.Init.Datatypes.nil"; "B.opnd2"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_add_abs_W.AA_VAL"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_add_abs_W.AA_POST"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Lemma limbs_val_core_add : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_B ()) "Pxs,(0.(1.&40.))Pxs',(0.(1.&40.))Pzs,(0.(1.&40.))Pj,$2.Pc,$2.P,(3.=R2.)P,(3.R3.(4.(5.(1.&40.)R6.)))P,(6.$7.(5.(1.&40.)R6.)(5.(1.&40.)R7.))P,(6.(0.(1.&40.))(8.(1.&40.)(9.R5.)R7.)(8.(1.&40.)(9.R5.)R8.))P,(6.$2.(:.(;.R8.R6.)(<.R5.(=.+2.(<.+20.R6.))))(:.(;.R9.R6.)(;.R7.R6.)))(6.$2.(:.(>.R9.)(<.R6.(=.+2.(<.+20.R7.))))(:.(>.R:.)(;.R8.R7.)))")
(* [comment removed for export] *).
Proof.
  intros xs xs' zs j c Hj Hl Hlen Hs Hv.
  rewrite (limbs_val_split xs j), (limbs_val_split xs' j) by lia. rewrite Hs. lia.
Qed.

(* [comment removed for export] *)
Section B.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (dA dB : mpd) (lo : Z) (MSF : Z)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Hypothesis MSFE : MSF = U_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 176 - hl_stack L.
  Local Notation FRAME := (AA_FRAME ra s0 s1 s2 s3 s4 s5 s6).
  Local Notation POST := (AA_POST L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dA dB lo X sX nX pX xs0 padX ownX).
  Local Notation VAL := (AA_VAL dA dB).
  Hypothesis JCX : JC usegs L HI h LB m mo dX sp lo 64 FRAME.

  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ usegs L HI h LB m mo dX sp lo 64 FRAME []).
  Local Notation JBE dE := (JB usegs L LB m dX sp lo dE).
  Local Notation BJE dE := (BJ usegs sp dE).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1]; cbn [app] in HH1.
  (* [comment removed for export] *)
  Local Ltac wctx := try exact HFREE; try exact HCALLOC; try exact MSFE; try exact CA; try exact TP; try exact SPA; try exact SLO2; try exact JCX.

  (* [comment removed for export] *)
  Definition opnd2 (dE : mpd) (LBc : list blk) (mc : mem) (dXc : mpd) : Prop :=
    (JBE dE /\ BJE dE LBc mc dXc) \/ dE = dXc.

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC MSF MSFE CA TP SPA SLO2 JCX"] Lemma add_CALL :
    forall (dE : mpd) (j : Z) (t0 t1 t2 raj a0 a1 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word) (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd),
    XJ usegs L HI h LB m mo dX sp lo 64 FRAME [] hc LBc mc moc dXc -> opnd2 dE LBc mc dXc -> md_own dXc = LHeap ->
    1 <= j <= md_n dXc -> j <= md_n dE -> j <= 10000 -> md_sg dXc = 1 -> limbs_val (md_limbs dXc) + lval (md_limbs dE) j = VAL ->
    aevtM usegs moc POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 j) a0 a1 (Z_to_bv 64 (md_p dE)) a3 a4 a5 a6 a7
      (Z_to_bv 64 (j + 1)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_p dXc)) (Z_to_bv 64 (4 * j + 4)) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x205d4) fc None mc (seg_rom usegs)).
  Proof.
    intros until dXc; intros J0 OP EO HJ HJE J10 SG1 HV.
    jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    (* [comment removed for export] *)
    assert (EF : exists zs, md_limbs dE = zs /\ bytes_at usegs mc (md_p dE) (u32s zs) /\ Z.of_nat (length zs) = md_n dE
                 /\ ((md_p dE = md_p dXc /\ zs = md_limbs dXc) \/ md_p dE + 4 * Z.of_nat (length zs) <= md_p dXc \/ md_p dXc + 4 * Z.of_nat (length (md_limbs dXc)) <= md_p dE)
                 /\ md_p dE mod 4 = 0 /\ 0 < md_p dE /\ (md_p dE + 4 * Z.of_nat (length zs) <= lo \/ bv_unsigned sp - 64 <= md_p dE)).
    { ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & ARR1 & P0 & PC & PI).
      destruct OP as [[DBJ B]| ->].
      - pose proof (bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
        assert (EN : md_own dE <> LNull) by (intros C; destruct (OWNE0 C); lia).
        ddestruct (OWNE1 EN) as (_ & EP0 & EPAL & EBY & ESK & _).
        exists (md_limbs dE). split; [reflexivity|]. split; [exact EBY|]. split; [exact LENE|]. split; [| split; [exact EPAL| split; [exact EP0| rewrite LENE; clear - ESK; lia]]].
        right. rewrite LENE, LEN1. pose proof (bj_sepL _ _ _ _ _ _ B EO EN). lia.
      - exists (md_limbs dXc). split; [reflexivity|]. split; [apply u32arr_ro; exact ARR1|]. split; [exact LEN1|].
        split; [left; split; reflexivity|]. split; [clear - XPAL; Z.div_mod_to_equations; lia|]. split; [exact P0|]. left. rewrite LEN1. clear - PC ACL; lia. }
    ddestruct EF as (zs & EZ & EBY & LENZ & SEPZ & EPAL & EP0 & ESK). rewrite EZ in HV.
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' sg own.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & ARR1 & P0 & PC & PI).
    clear MX1 HH1 SOK1 HPX1 FR1 OP.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl usegs mc) as WM.
    zstep. zstep. zstep. zstep.
    pose proof U_mpi_core_add_spec as SPc. unfold mpi_core_add_stmt, U_MPI_CORE_ADD in SPc.
    eapply aevtM_cut_evt; [ exact MK1 | eapply (SPc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pXc pXc (md_p dE) j lo xs xs zs);
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity | ].
    all: try exact ARR1. all: try (apply u32arr_ro; exact ARR1). all: try exact EBY.
    all: try (left; split; reflexivity). all: try exact SEPZ.
    all: try (clear - HJ J10 HJE LEN1 LENZ N1; lia).
    all: try (clear - XPAL; Z.div_mod_to_equations; lia). all: try exact EPAL. all: try exact P0. all: try exact EP0.
    all: try exact ST1. all: try (unfold MPI_CORE_ADD_STACK; clear - SLO2 HLS; lia). all: try (clear - SPA SPB SLO HLS ACL ACP; lia).
    all: try (left; rewrite LEN1; clear - PC ACL; lia). all: try exact ESK. all: try exact MI1.
    cbv beta. intros ms' PO. unfold mpi_core_add_post in PO.
    ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m2 & c & xs' & -> & MU2 & WM2 & MI2 & -> & HC & ARR2 & LEN2 & SK2 & LV2 & ST2).
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in MU2 by (clear - SPB SLO HLS ACL ACP; lia).
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in ST2 by (clear - SPB SLO HLS ACL ACP; lia). unfold MPI_CORE_ADD_STACK in MU2.
    replace (ret_pc (Z_to_bv 64 0x205e4)) with (Z_to_bv 64 0x205e4) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J0 MU2 WM2 MI2 ST2
                  ltac:(intros a NO; destruct (outside_dec [(pXc, pXc + 4 * j); (bv_unsigned sp - 64 - 48, bv_unsigned sp - 64)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O HJ SLO2 HLS; lia])
                  ltac:(cbn; clear - PC ACL SLO HLS HJ; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H HJ XS SLO2 HLS; lia) ARR2 LEN2) as J2.
    eapply add_FIRST; wctx; [exact J2| clear - HJ; lia| exact HC|].
    pose proof (limbs_val_core_add xs xs' zs j c ltac:(clear - HJ; lia) ltac:(clear - HJ LEN1; lia) LEN2 SK2 LV2). clear - H HV. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC MSF MSFE CA TP SPA SLO2 JCX"] Lemma add_J1 :
    forall (dE : mpd) (j : Z) (t0 t1 t2 raj a0 a1 a3 a4 a5 a6 a7 x20 x22 t3 t4 t5 t6 r1 r2 r5 : word) (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd),
    XJ usegs L HI h LB m mo dX sp lo 64 FRAME [] hc LBc mc moc dXc -> opnd2 dE LBc mc dXc ->
    1 <= j <= md_n dE -> j <= 10000 -> md_sg dXc = 1 -> limbs_val (md_limbs dXc) + lval (md_limbs dE) j = VAL ->
    r1 = Z_to_bv 64 j -> r2 = Z_to_bv 64 (j + 1) -> r5 = Z_to_bv 64 (4 * j + 4) ->
    aevtM usegs moc POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) r1 a0 a1 (Z_to_bv 64 (md_p dE)) a3 a4 a5 a6 a7
      r2 (Z_to_bv 64 (md_addr dE)) x20 r5 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x20570) fc None mc (seg_rom usegs)).
  Proof.
    intros until dXc; intros J0 OP HJ J10 SG1 HV -> -> ->.
    jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    pose proof J0 as JX; xj_open JX.
    pose proof MX1 as [(CX1 & _) _]. rewrite AD1, PD1 in CX1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1. unfold mpi_cells in CX1.
    clear HH1 SOK1 HPX1 FR1.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl usegs mc) as WM.
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      assert (EO : md_own dXc = LHeap).
      { destruct (md_own dXc) eqn:E; [| reflexivity| exfalso; exact (NS1 eq_refl)]. exfalso. destruct (OWN0 eq_refl) as [_ N0]. clear - N0 K0 HJ. lia. }
      zstep. eapply add_CALL; try eassumption. clear - HJ K0; lia. clear - HJ; lia.
    - (* [comment removed for export] *)
      destruct OP as [[DBJ B]| EQ]; [| exfalso; subst dE; clear - K0 HJ; lia].
      eapply add_G1; wctx; [exact DBJ| | exact J0| exact B| clear - K0 J10; lia| exact SG1| reflexivity].
      unfold K1_stmt. intros. eapply add_CALL; try eassumption; [left; split; assumption| | clear - HJ; lia|].
      + split; [clear - HJ; lia| assumption].
      + rewrite H4. exact HV.
  Qed.
End B.
