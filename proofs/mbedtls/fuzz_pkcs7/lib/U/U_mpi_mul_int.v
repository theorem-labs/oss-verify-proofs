(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney MpiJourney2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_copy U_mpi_core_mla U_mpi_add_abs_W U_mpi_add_abs_C U_mpi_add_abs U_mpi_mul_int_W U_mpi_lset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
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
Ltac2 gd_tbl_P_mpi_mul_int () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "copy_self_post"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_int_W.U_MPI_COPY"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.XJ"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_int_W.MI_FRAME"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_int_W.MI_POST"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.JB"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.BJ"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_copy.mpi_copy_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_int_W.mpi_mul_int_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_int_W.U_MPI_MUL_INT"].


(* [comment removed for export] *)
Definition copy_self_post (segs : list Segment) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Lms',$0.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R2.(6.(7.O22.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.(8.&40.=)O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)O4.(9.O22.)O3.(:.(2.&40.))R1.(;.O23.)))(4.(<.(=.(>.$?.$?.)(10.$?.$?.(11.(12.&40.O21.)+30.)(12.&40.O21.))(13.(>.$?.$?.)))O1.R1.)(4.(14.O23.O1.R1.)(4.(15.O23.R1.)(16.O23.R1.O2.(12.&40.O21.)))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma U_copy_self : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Plo,$?.P,(15.$18.R2.)P,(16.$18.R3.R2.(12.&40.R23.))P,(19.R3.(11.(12.&40.R24.)+30.))P,(5.$?.(1:.(12.&40.R25.)+10.)=)P,(5.(2.&40.)R1>.R1=.)(1;.$18.(1<.$18.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R6.R7.)(6.(7.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(8.&40.$1=.)R8.(:.(2.&40.))R7.(;.$18.)))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros MI ST SLO SPA ->. unfold U_MPI_COPY.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. flat constr:(ST) 3%nat. intros L0 _ _.
  carve_frame 48%nat ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] mx) as MU; pose proof (wmono_refl usegs mx) as WM end.
  do 7 zstep. replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by (clear; lia).
  zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
  do 9 zstep. release_frame FR ST (bv_unsigned sp).
  replace (Z_to_bv 64 (bv_unsigned sp - 48 + 48)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia). rewrite Z_to_bv_bv_unsigned.
  zstep. apply evt_done. unfold copy_self_post. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L13312809852.8L19524031615.8L23672843407.8L33371808075.8L41415985178.8L42470663613.8L44015172602.8L54240452684.800000800D00J00R00U00X00[00cS1v1n2HvS1n2dl2Hn2HdS1n2HnS1b1n2HbS1nS1nS1nS1v1n2Hv". (* [comment removed for export] *)
Lemma mul_fits : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Pv,$?.Pb,$?.Pn,$?.Pdl,$?.P,(4.(19.=R4.)(1>.R4.(1?.+2.(20.+20.R2.))))P,(4.(19.=R4.)(1>.R4.(1?.+2.+20.)))P,(19.=R4.)P,(19.(21.R5.+1.)R4.)(1>.(20.R8.R7.)(1?.+2.(20.+20.R5.)))")
(* [comment removed for export] *).
Proof.
  intros v b n dl Hv Hb Hn Hd.
  apply (Z.lt_le_trans _ (2 ^ (32 * n) * 2 ^ 32)).
  - apply (Z.le_lt_trans _ (v * 2 ^ 32)); [apply Z.mul_le_mono_nonneg_l; lia|]. apply Z.mul_lt_mono_pos_r; lia.
  - rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac zb_split K := repeat match type of K with
  | context [Z.b2z (?x <? ?y)] => revert K; destruct (Z.ltb_spec x y); cbn [Z.b2z]; intro K
  | context [Z.b2z (?x <=? ?y)] => revert K; destruct (Z.leb_spec x y); cbn [Z.b2z]; intro K
  | context [Z.b2z (?x =? ?y)] => revert K; destruct (Z.eqb_spec x y); cbn [Z.b2z]; intro K
  end.
Local Ltac chk := let K := fresh "K" in if_cases K;
  [ zify_cond K; rewrite ?unsigned_lit, ?signed_lit_small in K by lia;
    rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2, ?land_3_mod', ?land_7_mod' in K by lia; zb_split K;
    rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in K;
    exfalso; lia | clear K ].

(* [comment removed for export] *)
Section Body.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HCOPY : forall MSF, MSF = U_MEMSET_FUNC -> mpi_copy_stmt usegs L HI U_MPI_COPY MSF.
  Hypothesis HMLA : mpi_core_mla_vstmt usegs U_MPI_CORE_MLA.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (b lo : Z) (MSF : Z)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own)
            (Aa sA nA pA : Z) (ys : list word) (padA : word) (ownA : limb_own).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Local Notation dA := (mkMPD Aa sA nA pA ys padA ownA).
  Hypothesis MSFE : MSF = U_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 160 - hl_stack L.
  Hypothesis BB : 0 <= b < 2^32.
  Variable wb : word.
  Hypothesis WB1 : bv_unsigned wb mod 2^32 = b.
  Hypothesis WB0 : bv_unsigned wb = 0 <-> b = 0.
  Local Notation FRAME := (MI_FRAME ra s0 s1 s2 s3 s4 s5 s6).
  Local Notation POST := (MI_POST L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dA b lo X sX nX pX xs0 padX ownX).
  Hypothesis JCX : JC usegs L HI h LB m mo dX sp lo 64 FRAME.
  Hypothesis MAG : mpd_at usegs m LB dA.       (* [comment removed for export] *)
  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ usegs L HI h LB m mo dX sp lo 64 FRAME []).
  Local Notation JBE dE := (JB usegs L LB m dX sp lo dE).
  Local Notation BJE dE := (BJ usegs sp dE).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1 NM1]; cbn [app] in HH1.
  Local Ltac wctx := try exact MSFE; try exact CA; try exact TP; try exact SPA; try exact SLO2; try exact BB; try exact WB1; try exact WB0; try exact JCX.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mi_MLA : forall (n : Z) (t0 t1 t2 raj a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 t3 t4 t5 t6 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (sg nXc pXc : Z) (xs : list word)
      (S : Z) (ss : list word) (Sa sgS nS : Z) (padS : word),
    XJ0 hc LBc mc moc (mkMPD X sg nXc pXc xs padX LHeap) ->
    rw_cells usegs mc Sa [C8 (Z_to_bv 64 S); C2 (Z_to_bv 64 sgS); C2 (Z_to_bv 64 nS); C4 padS] ->
    bytes_at usegs mc S (u32s ss) -> 1 <= n -> n <= Z.of_nat (length ss) -> Z.of_nat (length ss) <= 10000 ->
    n + 1 <= nXc ->
    (S = pXc /\ ss = xs) \/ (S + 4 * Z.of_nat (length ss) <= pXc \/ pXc + 4 * nXc <= S) ->
    S mod 4 = 0 -> 0 < S ->
    (S + 4 * Z.of_nat (length ss) <= @alloc_ceiling L \/ (forall i, 0 <= i < 4 * Z.of_nat (length ss) -> ro_addr usegs (wa (S + i)) = true)) ->
    (S + 4 * Z.of_nat (length ss) <= lo \/ bv_unsigned sp <= S) ->
    lval ss n = limbs_val xs -> limbs_val xs < 2 ^ (32 * n) -> 1 <= b -> nXc <= Z.max nX (nA + 1) ->
    sg * limbs_val xs * b = mpd_val dA * b ->
    aevtM usegs moc POST
      (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 Sa) a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 wb (Z_to_bv 64 X) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1fce8) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until padS. intros J CS SBY N1 NLE SL10 NX1 SEP S4 S0 SHI SLS HV VB B1 NXB VAL. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ _ XIN XPAL ARR1 P0 PC PI.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof (rw_cells_bound _ _ _ _ CS) as SaB. cbn [cells_size csize Nat.add] in SaB.
    assert (SB : S + 4 * Z.of_nat (length ss) <= alloc_ceiling).
    { destruct SHI as [C|RO]; [exact C|]. pose proof (RO (4 * Z.of_nat (length ss) - 1) ltac:(clear - NLE N1; lia)) as R1.
      pose proof (bytes_at_bound _ _ _ _ SBY) as K. rewrite u32s_length in K.
      pose proof (ROIMG _ R1 ltac:(clear - K S0 NLE N1; lia)). clear - H IMGC NLE N1. lia. }
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    zstep. zstep. rewrite zx16_small by (clear - NR1; lia). zstep. zstep. zstep. zstep.
    assert (HB4 : b - 1 = bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned wb + -1))) mod 2 ^ 32).
    { change (b - 1 = w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned wb + -1)))). rewrite Z_to_bv64_swrap32_mod32.
      replace (bv_unsigned wb + -1) with (bv_unsigned wb - 1) by (clear; lia). rewrite <- Zminus_mod_idemp_l. rewrite WB1. rewrite Z.mod_small; clear - BB B1; lia. }
    unfold mpi_core_mla_vstmt in HMLA.
    eapply aevtM_cut_evt; [exact MK1| eapply HMLA with (ds := xs) (ss := ss) (dl := nXc) (sl := n) (D := pXc) (S := S) (lo := lo) (b := b - 1);
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); unfold MPI_CORE_MLA_STACK; try reflexivity; try eassumption|].
    - clear - N1 NLE SL10; lia.
    - clear - LEN1; lia.
    - clear - NX1; lia.
    - rewrite LEN1. exact SEP.
    - clear - XPAL. Z.div_mod_to_equations. lia.
    - right. exact S0.
    - rewrite LEN1. clear - PC ACV. lia.
    - clear - SB ACV. lia.
    - clear - SLO2 HLS; lia.
    - clear - SPA. Z.div_mod_to_equations. lia.
    - left. rewrite LEN1. clear - PC ACL SLO HLS. lia.
    - destruct SLS as [C|C]; [left; exact C| right; clear - C; lia].
    - cbv beta. intros ms' PO. unfold mpi_core_mla_vpost in PO.
      flat constr:(PO) 28%nat. flclear PO. intros z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 m2 xs' c -> MU2 WM2 MI2 ARR2 LEN2 SK2 CB LV2 ST2.
      unfold MPI_CORE_MLA_STACK in MU2. rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in MU2, ST2 by (clear - SPB SLO HLS ACL ACP; lia).
      replace (ret_pc (Z_to_bv 64 130304)) with (Z_to_bv 64 130304) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      (* [comment removed for export] *)
      rewrite HV in LV2. unfold lval in LV2 at 2. rewrite firstn_all2 in LV2 by (clear - LEN1; lia).
      replace (limbs_val xs + limbs_val xs * (b - 1)) with (limbs_val xs * b) in LV2 by (clear; lia).
      pose proof (mul_fits (limbs_val xs) b n nXc (conj (limbs_val_nonneg xs) VB) BB ltac:(clear - N1; lia) NX1) as FIT.
      pose proof (lval_range xs' nXc ltac:(clear - NX1 N1; lia)) as LR.
      assert (C0 : c = 0).
      { destruct (Z.eq_dec c 0) as [E|NE]; [exact E| exfalso].
        assert (K : 2 ^ (32 * nXc) * 1 <= 2 ^ (32 * nXc) * c) by (apply Z.mul_le_mono_nonneg_l; clear - CB NE; lia). clear - K LV2 FIT LR. lia. }
      subst c. rewrite Z.mul_0_r, Z.add_0_r in LV2. unfold lval in LV2. rewrite firstn_all2 in LV2 by (rewrite LEN2; clear - LEN1; lia).
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J MU2 WM2 MI2 ST2
                    ltac:(intros a NO; destruct (outside_dec [(pXc, pXc + 4 * nXc); (bv_unsigned sp - 64 - 48, bv_unsigned sp - 64)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O SLO2 HLS; lia])
                    ltac:(cbn; clear - PC ACL SLO HLS; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H XS SLO2 HLS; lia) ARR2 LEN2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU'. pose proof (wmono_refl usegs m2) as WM'.
      zstep. eapply mi_ret; wctx; [exact J2|]. left. split; [reflexivity|]. cbn [md_n]. split; [| exact NXB].
      unfold mpd_val at 1. cbn [md_sg md_limbs]. rewrite LV2. rewrite <- VAL. clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mi_T : forall (n : Z) (t0 t1 t2 raj x9 a2 a3 a4 a5 a6 a7 x18 x19 x22 t3 t4 t5 t6 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd),
    XJ0 hc LBc mc moc dXc -> (Aa <> X -> JBE dA /\ BJE dA LBc mc dXc) -> (Aa = X -> dA = dX) ->
    md_own dXc = LHeap -> n + 1 <= md_n dXc -> md_n dXc <= Z.max nX (n + 1) -> md_sg dXc = sX ->
    limbs_val (md_limbs dXc) = limbs_val xs0 -> (Aa = X -> lval (md_limbs dXc) n = limbs_val xs0) ->
    1 <= n <= nA -> lval ys n = limbs_val ys -> limbs_val ys < 2 ^ (32 * n) -> 1 <= b ->
    aevtM usegs moc POST
      (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 n) x9 (Z_to_bv 64 X) (Z_to_bv 64 Aa)
             a2 a3 a4 a5 a6 a7 x18 x19 wb (Z_to_bv 64 X) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1fcd8) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J AJ AX OWNc NX1 NXB SGc LVc LVn NR HYS YB B1. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *. subst own sg.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ _ XIN XPAL ARR1 P0 PC PI.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    zstep. zstep.
    destruct (Z.eq_dec Aa X) as [EA|NEA].
    - (* [comment removed for export] *)
      specialize (LVn EA).
      assert (VB : limbs_val xs < 2 ^ (32 * n)).
      { rewrite LVc, <- LVn. apply lval_range. clear - NR; lia. }
      pose proof (AX EA) as E. injection E as E1 E2 E3 E4 E5 E6 E7.
      eapply aevtM_cut_evt; [exact MK1| eapply U_copy_self with (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia);
        [exact MI1| exact ST1| clear - SLO2 HLS; lia| clear - SPA; Z.div_mod_to_equations; lia| rewrite EA; reflexivity]|].
      cbv beta. intros ms' (m2 & -> & MU2 & WM2 & MI2 & ST2).
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in MU2, ST2 by (clear - SPB SLO HLS ACL ACP; lia).
      replace (ret_pc (Z_to_bv 64 130272)) with (Z_to_bv 64 130272) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (ARR2 : u32arr usegs m2 pXc xs).
      { eapply u32arr_transport; [exact ARR1| exact MU2| exact WM2|]. cbn. clear - PC ACL SLO2 HLS LEN1. lia. }
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J MU2 WM2 MI2 ST2
                    ltac:(intros a NO; destruct (outside_dec [(bv_unsigned sp - 64 - 48, bv_unsigned sp - 64)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O SLO2 HLS; lia])
                    ltac:(cbn; clear - SLO HLS; lia) ltac:(cbn; clear - XS SLO2 HLS; lia) ARR2 eq_refl) as J2.
      pose proof J2 as JY. destruct JY as [MI2' _ _ _ _ _ _ MX2 _ _ _ _ _ _ _ _].
      flat constr:(MX2) 2%nat. intros (CX2 & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
      pose proof (munch_refl ([] : list ivl) m2) as MU'. pose proof (wmono_refl usegs m2) as WM'.
      assert (LVn' : lval xs n = limbs_val xs) by (rewrite LVn, LVc; reflexivity).
      zstep. zstep. rewrite EA.
      eapply mi_MLA with (ss := xs); [exact J2| exact CX2| apply u32arr_ro; exact ARR2| clear - NR; lia| rewrite LEN1; clear - NX1; lia| rewrite LEN1; clear - NR1; lia| exact NX1
        | left; split; reflexivity| clear - XPAL; Z.div_mod_to_equations; lia| exact P0| left; rewrite LEN1; exact PC| left; rewrite LEN1; clear - PC ACL SLO HLS; lia
        | exact LVn'| exact VB| exact B1| clear - NXB NR; lia|].
      unfold mpd_val. cbn [md_sg md_limbs]. rewrite LVc, <- E2, <- E5. reflexivity.
    - (* [comment removed for export] *)
      flat constr:((AJ NEA)) 2%nat. intros DBJ B. pose proof DBJ as [MA0 OA CRA CRAL SXA]. flat constr:(OA) 5%nat. intros OA1 OA2 OA3 OA4 OA5.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ B)) 8%nat. intros A0 A16 AAL LENA NRA AS OWNA0 OWNA1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof B as [BA BSS BSL]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BSS, BSL.
      pose proof (opnd_at_mpd_back _ _ _ _ _ _ _ MAG BA) as BAm.
      destruct (bj_client _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ [] hc LBc mc moc _ LBc lo J B ltac:(intros bb Hb _; exact Hb) ltac:(clear - SLO HLS; lia)) as [C1 C2].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in C1, C2.
      pose proof (HCOPY MSF MSFE) as SPc. unfold mpi_copy_stmt, U_MPI_COPY in SPc.
      eapply aevtM_cut.
      { eapply SPc with (dX := mkMPD X sX nXc pXc xs padX LHeap) (dY := dA) (lo := lo); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
          rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; try eassumption.
        - right. cbn [md_addr]. exact SXA.
        - unfold copy_sep. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
          split; [exact OA1|]. split; [exact BSS|]. split; [| split; [clear - OA4; lia| split; [intros AN; destruct (OA5 AN); clear - H; lia| intros a Ha; clear - Ha A0; lia]]].
          destruct ownA; [right; right; left; reflexivity| |]; right; right; right; apply BSL; [reflexivity| discriminate| reflexivity| discriminate].
        - split; [| split; [exact (proj1 (proj2 XW))| cbn [md_own md_addr md_p md_n]; exact XP1]]. cbn [md_addr].
          intros a Ha. destruct (xj_cwX _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J a Ha) as [C|[C|C]]; [left; rewrite HT1; clear - C; lia| right; left; exact C| right; right; exact C].
        - clear - SLO2; lia.
        - rewrite HT1. clear - HTOP; lia.
        - clear - SPA. Z.div_mod_to_equations. lia. }
      cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m1 mo1 h1 LB1 dX1 r E PO. injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 CR.
      replace (ret_pc (Z_to_bv 64 130272)) with (Z_to_bv 64 130272) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      flat constr:(CR) 2%nat. flclear CR. intros CR1 BK. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CR1, BK.
      assert (BK' : binop_keep LBc (mkMPD X sX nXc pXc xs padX LHeap) dX1).
      { flat constr:(BK) 3%nat. flclear BK. intros K1 K2 K3. split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. cbn [md_n].
        destruct CR1 as [(_ & _ & K4 & _)|(_ & K4 & _)]; [exact K4| rewrite K4; apply Z.le_refl]. }
      pose proof (xj_call _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 BK') as J2.
      pose proof (bj_call _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ DBJ J B MI2 HH2 MX2 OUT2 HPX2 BK') as B2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      destruct dX1 as [X1 sg1 n1 p1 xs1 pad1 own1]. flat constr:(BK') 4%nat. flclear BK'. intros E1 E2 FR2 NM2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X1 pad1.
      clear MU WM JX MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 NM1 CX1.
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      zstep. zstep. if_cases KR; zify_cond KR.
      { (* [comment removed for export] *) destruct CR1 as [(-> & _)|(-> & _)]; [exfalso; apply KR; reflexivity|].
        eapply mi_ret; wctx; [exact J2| right; reflexivity]. }
      destruct CR1 as [(-> & CV & CN)|(-> & _)]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
      assert (EO1 : own1 = LHeap).
      { pose proof J2 as JY. destruct JY as [_ _ _ _ _ _ _ MX3 _ _ NS3 _ _ _ _ _]. cbn [md_own] in NS3.
        destruct own1; [| reflexivity| exfalso; exact (NS3 eq_refl)]. exfalso.
        flat constr:(MX3) 2%nat. intros FLt1 _. flat constr:(FLt1) 6%nat. flclear FLt1. intros _ _ _ _ _ OW. cbn [md_own md_p md_n] in OW. flat constr:(OW) 2%nat. flclear OW. intros _ N0. clear - N0 CN NX1 NR. lia. }
      subst own1.
      pose proof J2 as JY. xj_open JY. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ B2))) 2%nat. intros FLt2 SGA. flat constr:(FLt2) 6%nat. flclear FLt2. intros CA2 _ _ _ _ OWA2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CA2, OWA2, SGA. unfold mpi_cells in CA2.
      pose proof B2 as [_ BSS2 BSL2]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BSS2, BSL2.
      flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ B2)) 8%nat. intros _ _ _ _ _ _ _ OWNA2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OWNA2.
      destruct (OWNA2 ltac:(destruct ownA; [destruct (OWNA0 eq_refl); exfalso; clear - H0 NR; lia| discriminate| discriminate])) as (NA1 & PA0 & PA4 & ABY & ALS & AIN).
      (* [comment removed for export] *)
      assert (AV : limbs_val xs1 = limbs_val ys).
      { unfold mpd_val in CV. cbn [md_sg md_limbs] in CV. pose proof (limbs_val_nonneg xs1). pose proof (limbs_val_nonneg ys).
        flat constr:(MX1) 2%nat. intros _ SG1. cbn [md_sg] in SG1. destruct SG1 as [-> | ->]; destruct SGA as [-> | ->]; clear - CV H H0; lia. }
      eapply mi_MLA with (ss := ys) (S := pA); [exact J2| exact CA2| exact ABY| clear - NR; lia| rewrite LENA; clear - NR; lia| rewrite LENA; clear - NRA; lia| clear - CN NX1; lia
        | | exact PA4| exact PA0| | rewrite LENA; exact ALS| rewrite AV; exact HYS| rewrite AV; exact YB| exact B1| clear - CN NXB NR; lia|].
      + right. rewrite LENA. destruct (BSL2 eq_refl ltac:(destruct ownA; [destruct (OWNA0 eq_refl); exfalso; clear - H0 NR; lia| discriminate| discriminate])) as [D|D]; [right; exact D| left; exact D].
      + rewrite LENA. destruct ownA; [destruct (OWNA0 eq_refl); exfalso; clear - H0 NR; lia| |].
        * left. flat constr:((AIN eq_refl)) 2%nat. intros AIN0 _. flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _.
          flat constr:((proj1 (Forall_forall _ _) HBR0 _ AIN0)) 5%nat. intros _ _ _ R3 _. exact R3.
        * right. flat constr:(MAG) 2%nat. intros FLt3 _. flat constr:(FLt3) 6%nat. flclear FLt3. intros _ _ _ _ _ OWS. cbn [md_own md_p md_n md_limbs] in OWS. flat constr:(OWS) 5%nat. flclear OWS. intros _ _ _ _ RO. exact RO.
      + unfold mpd_val. cbn [md_sg md_limbs]. unfold mpd_val in CV. cbn [md_sg md_limbs] in CV. rewrite CV. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mi_FIN : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model),
    XJ0 hc LBc mc moc dX -> mpd_val dA * b = 0 -> 0 <= nA ->
    aevtM usegs moc POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 U_MPI_LSET) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until moc. intros J HV NA0. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (stk_release usegs mc lo (bv_unsigned sp - 64) FRAME ST1 FR1 ltac:(clear - SLO HLS; lia)) as STs.
    rewrite FSZ in STs. replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) in STs by (clear; lia).
    pose proof (U_mpi_lset_spec_v L HI HCALLOC HLS SW DIMG HND) as SL. unfold mpi_lset_stmt_v, U_MPI_LSET in SL.
    eapply aevtM_mono; [eapply SL with (dX := dX) (z := 0) (lo := lo) (h := hc) (LB := LBc); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
      try reflexivity; try eassumption|].
    - split; [| split; [exact (proj1 (proj2 XW))| cbn [md_own md_addr md_p md_n]; exact XP1]]. cbn [md_addr].
      intros a Ha. destruct (xj_cwX _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J a Ha) as [C|[C|C]]; [left; rewrite HT1; clear - C; lia| right; left; exact C| right; right; exact C].
    - clear; lia.
    - clear - SLO2; lia.
    - rewrite HT1. clear - HTOP; lia.
    - rewrite <- MSFE. exact CA.
    - intros c PO. unfold mpi_binop_post in PO.
      destruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m1 & mo1 & h1 & LB1 & dX1 & r
                      & E & MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & CR).
      unfold MI_POST, mpi_binop_post.
      exists y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m1, mo1, h1, LB1, dX1, r.
      split; [exact E|]. split; [exact MI2|]. split; [exact ST2|]. split; [eapply mo_frame_trans; [exact MF1| exact MF2]|].
      split; [rewrite HT2; exact HT1|]. split; [exact HH2|]. split; [exact MX2|].
      assert (BLX : forall bb, In bb (mpd_blk dX) -> In bb LB).
      { intros bb Hb. unfold mpd_blk in Hb. cbn [md_own md_p md_n] in Hb.
        destruct ownX; cbn in Hb; [contradiction| |contradiction]. destruct Hb as [<-|[]].
        flat constr:(MX) 2%nat. intros FLm _. flat constr:(FLm) 6%nat. flclear FLm. intros _ _ _ _ _ OW. cbn [md_own md_p md_n] in OW.
        flat constr:(OW) 4%nat. flclear OW. intros _ PIN _ _. exact PIN. }
      split; [eapply mpd_out_trans; [exact OUT1| exact OUT2| exact FRS1| exact BLX]|].
      split; [eapply (xj_presx_stepx _ _ _ _ _ _ _ _ _ _ _ _ JCX); [exact J| exact HPX2| intros bb Hb; exact Hb| clear; lia| intros a O _; exact O]|].
      split; [exact SOK2|].
      destruct CR as [CR CV]. unfold lset_R in CR. destruct CR as [CR (CA1 & CB1)].
      unfold mul_int_R. split.
      + destruct CR as [(-> & CN & _ & _ & _ & _)|(-> & _)]; [left| right; reflexivity].
        split; [reflexivity|]. split; [rewrite (CV eq_refl); clear - HV; lia|]. rewrite CN. cbn [md_n]. clear - NA0; lia.
      + unfold binop_keep. split; [exact CA1|].
        split; [destruct CR as [(_ & _ & _ & _ & _ & P)|(_ & ->)]; [exact P| reflexivity]|].
        split.
        * intros bb Hb. destruct (CB1 bb Hb) as [B|B]; [left; exact B|].
          destruct (in_dec blk_eq_dec bb LB) as [I|I]; [| right; exact I].
          destruct (xj_blocks_orig _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ bb J I) as [I'|I']; [exfalso; exact (B I')| left; exact I'].
        * destruct CR as [(_ & CN & _)|(_ & ->)]; [rewrite CN; cbn [md_n]; clear; lia| clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mi_LSET : forall (t0 t1 t2 raj x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model),
    XJ0 hc LBc mc moc dX -> mpd_val dA * b = 0 -> 0 <= nA ->
    aevtM usegs moc POST
      (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1fd30) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until moc. intros J HV NA0. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (_ & _ & _ & MK & _).
    pose proof (xj_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as FR. pose proof (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI.
    unfold MI_FRAME, mi_frame in FR.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    do 10 zstep.
    replace (Z_to_bv 64 (bv_unsigned sp - 64 + 64)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia). rewrite Z_to_bv_bv_unsigned.
    zstep.
    eapply mi_FIN; [exact J| exact HV| exact NA0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mi_FOUND : forall (n : Z) (t0 t1 t2 raj x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 r0 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model),
    XJ0 hc LBc mc moc dX -> (Aa <> X -> JBE dA /\ BJE dA LBc mc dX) -> (Aa = X -> dA = dX) ->
    1 <= n <= nA -> lval ys n = limbs_val ys -> nA <= 10000 -> r0 = Z_to_bv 64 n ->
    aevtM usegs moc POST
      (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 r0 x9 (Z_to_bv 64 X) (Z_to_bv 64 Aa) wb
             a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1fc44) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until moc. intros J AJ AX NR HYS NA10 ->. jc_open. assert (NA0 : 0 <= nA) by (clear - NR; lia).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    assert (YB : limbs_val ys < 2 ^ (32 * n)) by (rewrite <- HYS; apply lval_range; clear - NR; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    zstep. if_cases KB; zify_cond KB.
    { (* [comment removed for export] *) apply (proj1 WB0) in KB. eapply mi_LSET; wctx; [exact J| rewrite KB; clear; lia| exact NA0]. }
    assert (KB' : b <> 0) by (intros E; exact (KB (proj2 WB0 E))). clear KB. rename KB' into KB.
    zstep. zstep. zstep. zstep. if_cases KL; zify_cond KL.
    { (* [comment removed for export] *) eapply mi_ret; wctx; [exact J| right; reflexivity]. }
    rewrite Z.shiftr_div_pow2 in KL by (clear; lia). change (2 ^ 4) with 16 in KL. rewrite ?Z.mod_small in KL by (clear - NR NA10; lia).
    assert (N10 : n < 10000) by (clear - KL NR; Z.div_mod_to_equations; lia).
    zstep. chk.
    zstep. zstep. zstep. chk.
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. zstep. if_cases KG; zify_cond KG; rewrite ?Z.mod_small in KG by (clear - NR NR1 N10; lia).
    - (* [comment removed for export] *)
      assert (EO : ownX = LHeap).
      { destruct ownX; [(flat constr:((OWN0 eq_refl)) 2%nat; intros _ N0); exfalso; clear - N0 KG NR; lia| reflexivity| exfalso; exact (NST eq_refl)]. }
      eapply (mi_T n) with (dXc := dX); wctx; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        [exact J| exact AJ| exact AX| exact EO| clear - KG; lia| clear - KG; lia| reflexivity| reflexivity| | exact NR| exact HYS| exact YB| clear - KB BB; lia].
      intros EA. pose proof (AX EA) as E. injection E as E1 E2 E3 E4 E5 E6 E7. rewrite <- E5. exact HYS.
    - (* [comment removed for export] *)
      eapply (mi_G L HI HFREE HCALLOC) with (dXc := dX); wctx; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try reflexivity.
      + (* [comment removed for export] *) unfold KC_stmt. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. intros until dXc. intros KJ KA KO KN KM KS KV KW.
        eapply (mi_T n); wctx; [exact KJ| intros NE; split; [exact (proj1 (AJ NE))| exact (KA NE)]| exact AX| exact KO| exact KN| exact KM| exact KS| exact KV
          | intros _; exact KW| exact NR| exact HYS| exact YB| clear - KB BB; lia].
      + exact J.
      + exact AJ.
      + clear - KG N10; lia.
      + clear - NR; lia.
      + unfold lval. rewrite firstn_all2 by (clear - KG LEN1; lia). reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mi_SCANLOOP : forall (k : nat) (t0 t1 t2 raj x9 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 r1 r3 r4 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (r : Z),
    r <= Z.of_nat k -> XJ0 hc LBc mc moc dX -> (Aa <> X -> JBE dA /\ BJE dA LBc mc dX) -> (Aa = X -> dA = dX) ->
    bytes_at usegs mc pA (u32s ys) -> Z.of_nat (length ys) = nA -> nA <= 10000 -> 0 < pA -> pA mod 4 = 0 ->
    rw_cells usegs mc Aa [C8 (Z_to_bv 64 pA); C2 (Z_to_bv 64 sA); C2 (Z_to_bv 64 nA); C4 padA] ->
    0 <= r <= nA -> lval ys r = limbs_val ys ->
    r1 = Z_to_bv 64 (r + 1) -> r3 = Z_to_bv 64 (4 * r - 4) -> r4 = Z_to_bv 64 (-4) ->
    aevtM usegs moc POST
      (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 r1 x9 (Z_to_bv 64 X) (Z_to_bv 64 Aa) wb r3 r4 a5 a6 a7
             x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1fc04) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until r; intros Hk J AJ AX EBY LENY NY10 PA0 PAL CAa HR YA -> -> ->;
      (jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP;
       pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1;
       pose proof (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI1;
       pose proof (bytes_at_bound _ _ _ _ EBY) as EB; rewrite u32s_length in EB;
       pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl usegs mc) as WM;
       zstep; if_cases K0; zify_cond K0;
       [ assert (Er : r = 0) by (revert K0; rewrite ?unsigned_lit_wrap; intros K0; Z.div_mod_to_equations; lia); subst r;
         eapply mi_LSET; wctx; [exact J| | clear - HR; lia];
         unfold mpd_val; cbn [md_sg md_limbs]; change (lval ys 0) with 0 in YA; rewrite <- YA; clear; lia
       | ]).
    1: exfalso; revert K0; rewrite ?unsigned_lit_wrap; intros K0; Z.div_mod_to_equations; lia.
    assert (R1 : 1 <= r) by (revert K0; rewrite ?unsigned_lit_wrap; intros K0; Z.div_mod_to_equations; lia).
    zstep. zstep. zstep. chk.
    zstep. zstep. zstep. zstep. chk.
    zstep. chk.
    zstep. zstep. zstep. chk.
    destruct (nth_error ys (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENY HR R1; lia].
    pose proof (u32ro_read usegs mc pA ys (r - 1) w _ EBY NTH ltac:(clear - R1; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (limb32_w32_nth ys (Z.to_nat (r - 1)) w NTH) as LW. pose proof (w32_range w) as WR.
    zstep. zstep. zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1; fold (w32 w) in K1.
    2: { (* [comment removed for export] *)
      eapply (mi_FOUND r); wctx; [exact J| exact AJ| exact AX| clear - HR R1; lia| exact YA| exact NY10| f_equal; clear; lia]. }
    (* [comment removed for export] *)
    apply (proj1 (sxz_zero_iff _ WR)) in K1.
    assert (YA' : lval ys (r - 1) = limbs_val ys).
    { rewrite <- YA. replace r with (r - 1 + 1) at 2 by (clear; lia). rewrite (lval_succ ys (r - 1)) by (clear - R1; lia). rewrite LW, K1. clear; lia. }
    eapply IH with (r := r - 1); try eassumption; [clear - Hk; lia| clear - HR R1; lia| f_equal; clear; lia| f_equal; clear; lia| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Body.

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
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Hypothesis HMLA : mpi_core_mla_vstmt usegs U_MPI_CORE_MLA.

  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Theorem U_mpi_mul_int_spec' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "PMSF,$?.P,(5.$?.R1.$49.)P,(4:.$18.VL,VHI,$1=.R2.)(4;.$18.VL,VHI,$4<.R3.)")
(* [comment removed for export] *).
  Proof.
    intros MSF MSFE HCOPY0. unfold mpi_mul_int_stmt, U_MPI_MUL_INT. intros until lo.
    assert (HCOPY : forall MSF', MSF' = U_MEMSET_FUNC -> mpi_copy_stmt usegs L HI U_MPI_COPY MSF') by (intros MSF' ->; rewrite <- MSFE; exact HCOPY0).
    intros HH MX MA0 SXA NST OA CRA CRAL XW XLS ST SLO2 ACL HTOP SPA DHI TP MI SOK CA BB WB1 WB0 -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    destruct dX as [X sX nX pX xs0 padX ownX]. destruct dA as [Aa sA nA pA ys padA ownA].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX) 2%nat. intros FLt6 SGX. flat constr:(FLt6) 6%nat. flclear FLt6. intros CX0 XAL X0 LENX NRX OWNX. unfold mpi_cells in CX0. unfold MPI_MAX_LIMBS in NRX.
    flat constr:(MA0) 2%nat. intros FLt7 SGA. flat constr:(FLt7) 6%nat. flclear FLt7. intros CA0 AAL A0 LENA NRA OWNA. unfold MPI_MAX_LIMBS in NRA.
    pose proof (rw_cells_bound _ _ _ _ CX0) as XBD. pose proof (rw_cells_bound _ _ _ _ CA0) as ABD.
    unfold mpi_cells in ABD. cbn [cells_size csize Nat.add] in XBD, ABD.
    flat constr:(OA) 5%nat. intros OA1 OA2 OA3 OA4 OA5. flat constr:(XW) 3%nat. intros XCW XDW XP.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO2 HLS; lia)) as XS.
    unfold mpd_sep in SXA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SXA.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HHc. clear HH. pose proof (conj SOK I) as SOKc. clear SOK.
    do 9 zstep.
    replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by (clear; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    change (rw_cells usegs m0 (bv_unsigned sp - 64) (MI_FRAME ra s0 s1 s2 s3 s4 s5 s6)) in FR.
    flat constr:(HHc) 2%nat. flclear HHc. intros HH _. flat constr:(SOKc) 2%nat. flclear SOKc. intros SOK _.
    assert (JCX : JC usegs L HI h LB m mo (mkMPD X sX nX pX xs0 padX ownX) sp lo 64 (MI_FRAME ra s0 s1 s2 s3 s4 s5 s6)).
    { constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption; try reflexivity; try (clear; lia). clear - SLO2. lia. }
    assert (J0 : XJ usegs L HI h LB m mo (mkMPD X sX nX pX xs0 padX ownX) sp lo 64 (MI_FRAME ra s0 s1 s2 s3 s4 s5 s6) [] h LB m0 mo (mkMPD X sX nX pX xs0 padX ownX)).
    { constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption; try reflexivity.
      - eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact MU| exact WM| exact ACL|].
        intros a Ha NO. cbn in NO. left. clear - NO HTOP SLO2 HLS. lia.
      - apply mo_frame_refl.
      - eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Hd NW. cbn. split; [clear - Hd DHI ACL SLO2 HLS; lia| exact I].
      - eapply mpd_at_munch_any; [exact MX| exact MU| exact WM| cbn; split; [clear - XS SLO2 HLS; lia| exact I]|].
        cbn [md_own md_p md_n]. intros ON. cbn. split; [| exact I]. destruct (XLS ON); clear - H SLO2 HLS; lia.
      - apply mpd_out_refl. exact NST.
      - intros bb Hb. left. exact Hb.
      - eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| clear - ACL SLO2 HLS; lia]. }
    assert (MA : mpd_at usegs m0 LB (mkMPD Aa sA nA pA ys padA ownA)).
    { eapply mpd_at_munch_any; [exact MA0| exact MU| exact WM| cbn; split; [clear - OA4 SLO2 HLS; lia| exact I]|].
      intros ON. cbn. split; [destruct (OA5 ON); clear - H SLO2 HLS; lia| exact I]. }
    pose proof J0 as JX. destruct JX as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1 NM1]. cbn [app md_addr md_p md_n md_own] in HH1, XP1.
    clear MU WM ST FR MI.
    rename m0 into mc.
    assert (AX : Aa = X -> mkMPD Aa sA nA pA ys padA ownA = mkMPD X sX nX pX xs0 padX ownX) by (intros E; destruct SXA as [E'|D]; [symmetry; exact E'| exfalso; clear - D E; lia]).
    assert (AJ : Aa <> X -> JB usegs L LB m (mkMPD X sX nX pX xs0 padX ownX) sp lo (mkMPD Aa sA nA pA ys padA ownA)
                            /\ BJ usegs sp (mkMPD Aa sA nA pA ys padA ownA) LB mc (mkMPD X sX nX pX xs0 padX ownX)).
    { intros NE. assert (D : X + 16 <= Aa \/ Aa + 16 <= X) by (destruct SXA as [E|D]; [exfalso; apply NE; injection E; auto| exact D]).
      split; [constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption; apply opnd_at_mpd; exact MA0|].
      constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; [apply opnd_at_mpd; exact MA| exact OA2|].
      intros EO AN. destruct OA3 as [C|[C|[C|C]]]; [exfalso; apply NE; injection C; auto| exfalso; exact (C EO)| exfalso; exact (AN C)| exact C]. }
    flat constr:(MA) 2%nat. intros FLt8 _. flat constr:(FLt8) 6%nat. flclear FLt8. intros CA1 _ _ _ _ OWNA1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CA1, OWNA1. unfold mpi_cells in CA1.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl usegs mc) as WM.
    zstep. chk.
    zstep. zstep. chk.
    zstep. rewrite zx16_small by (clear - NRA; lia). zstep. zstep. zstep. zstep.
    rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    destruct (Z.eq_dec nA 0) as [KA0|KA0].
    { (* [comment removed for export] *)
      zstep. if_cases KZ; [| exfalso; zify_cond KZ; rewrite ?unsigned_lit_wrap in KZ; rewrite KA0 in KZ; apply KZ; reflexivity].
      eapply (mi_LSET L HI HCALLOC); try exact JCX; try eassumption.
      - unfold mpd_val. cbn [md_sg md_limbs]. destruct ys; [cbn [limbs_val]; clear; lia| exfalso; cbn [length] in LENA; clear - LENA KA0; lia].
      - clear - NRA; lia. }
    assert (AN : ownA <> LNull) by (intros C; rewrite C in OWNA; (flat constr:(OWNA) 2%nat; flclear OWNA; intros _ N0); exact (KA0 N0)).
    assert (AF : 1 <= nA /\ 0 < pA /\ pA mod 4 = 0 /\ bytes_at usegs mc pA (u32s ys)).
    { destruct ownA; [exfalso; exact (AN eq_refl)| |].
      - flat constr:(OWNA1) 4%nat. flclear OWNA1. intros N1 _ PAL16 ARR. split; [exact N1|]. flat constr:(OWNA) 4%nat. intros _ AIN _ _.
        flat constr:((proj1 (Forall_forall _ _) HBR _ AIN)) 2%nat. intros R0 _. split; [exact R0|].
        split; [clear - PAL16; Z.div_mod_to_equations; lia| apply u32arr_ro; exact ARR].
      - flat constr:(OWNA1) 5%nat. flclear OWNA1. intros N1 PAL4 P0 BY _. split; [exact N1|]. split; [exact P0|]. split; [exact PAL4| exact BY]. }
    flat constr:(AF) 4%nat. flclear AF. intros NA1 PA0 PAL ABY.
    eapply (mi_SCANLOOP L HI HFREE HCALLOC HCOPY HMLA IMGC) with (MSF := MSF) (k := Z.to_nat nA) (r := nA); try exact JCX; try eassumption;
      [clear - NA1; lia| clear - NRA; lia| clear - NA1; lia| apply lval_full; exact LENA| f_equal; clear; lia| f_equal; clear; lia| f_equal; clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Theorem U_mpi_mul_int_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_mul_int_stmt usegs L HI U_MPI_MUL_INT MSF.
  Proof.
    intros MSF ->. apply U_mpi_mul_int_spec'; [reflexivity|].
    change U_MPI_COPY with U_mpi_copy.U_MPI_COPY. apply U_mpi_copy_spec; try assumption. intros a H1 H2. exact (ROIMG a H2 H1).
  Qed.
End Spec.
