(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_copy U_mpi_shift_l U_mpi_cmp U_mpi_lset U_mpi_mul_int_W U_mpi_core_bitlen U_mpi_core_shift_r U_mpi_divmod_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_div_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiOpnd.
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
Ltac2 gd_tbl_P_mpi_mod_mpi () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.bool"; "ModP.Walk.ALIAS"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "ModP.Walk.es"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.USpec.MpiClient.cstate"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.MOK"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_abs"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_divmod_stmt.mod_mpi_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"].


Definition U_MPI_MOD_MPI' : Z := 0x21610.

Lemma mpd_val_T0 : forall a p pd own, mpd_val (mkMPD a 1 1 p [Z_to_bv 64 0] pd own) = 0.
Proof. intros. unfold mpd_val. cbn [md_sg md_limbs]. vm_compute. reflexivity. Qed.

Lemma T_opnd : forall (m : mem) (A P Q SPx : Z) (j4 j20 : list (bv 8)) (rest : list cell),
  rw_cells usegs m A ([CB 4 j4; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 P); C4 (Z_to_bv 64 65537); CB 4 j20] ++ rest) ->
  P = A + 4 -> Q = A + 8 -> 0 < A -> A mod 8 = 0 -> SPx <= A -> A + 24 <= 2^64 ->
  stack_opnd usegs m SPx (mkMPD Q 1 1 P [Z_to_bv 64 0] (le_bytes_to_word j20) LStatic).
Proof.
  intros m A P Q SPx j4 j20 rest H EP EQ A0 A8 HS HB. subst P Q.
  destruct (rw_cells_split3 usegs m A [CB 4 j4; C4 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 (A + 4)); C4 (Z_to_bv 64 65537); CB 4 j20] rest H) as (FA & FT & _).
  destruct (rw_cells_split3 usegs m A [CB 4 j4] [C4 (Z_to_bv 64 0)] [] FA) as (_ & FL & _).
  cbn [cells_size csize Nat.add] in FT, FL. change (Z.of_nat 8) with 8 in FT. change (Z.of_nat 4) with 4 in FL.
  pose proof FT as [[WT _] _]. cbn [cells_wf cell_wf] in WT. destruct WT as (_ & _ & L20 & _).
  pose proof FL as [[_ BL] _].
  unfold stack_opnd. cbn [md_own md_addr md_sg md_n md_p md_limbs md_pad].
  split; [reflexivity|]. split.
  { unfold mpi_cells. eapply rw_cells_reshape; [exact FT| cbn; tauto|].
    cbn [cells_bytes cbytes]. rewrite le4_le_bytes_to_word by exact L20.
    f_equal. rewrite app_assoc. f_equal. unfold le2, le4. rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
    refine (f_equal2 (@cons (bv 8)) _ (f_equal2 (@cons (bv 8)) _ (f_equal2 (@cons (bv 8)) _ (f_equal2 (@cons (bv 8)) _ eq_refl))));
      apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity. }
  split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BL|]. split; [lia|]. split; [lia|].
  left; reflexivity.
Qed.

Section ModP.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr usegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Variable MSF : Z.
  Hypothesis MSFE : MSF = U_MEMSET_FUNC.
  (* [comment removed for export] *)
  Hypothesis HDIV : mpi_div_mpi_stmt usegs L HI U_MPI_DIV_MPI MSF.
  Hypothesis HCMP : mpi_cmp_mpi_stmt usegs U_MPI_CMP_MPI.
  Hypothesis HAS : add_sub_mpi_stmt usegs L HI U_ADD_SUB_MPI MSF.

  Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (dR dA dB : mpd) (lo : Z).
  Hypothesis HH0 : HEAP usegs L HI h LB m mo.
  Hypothesis MR0 : mpd_at usegs m LB dR.
  Hypothesis MA0 : mpd_at usegs m LB dA.
  Hypothesis MB0 : mpd_at usegs m LB dB.
  Hypothesis SRA : mpd_sep dR dA.
  Hypothesis SRB : mpd_sep dR dB.
  Hypothesis SAB : mpd_sep dA dB.
  Hypothesis NSR : md_own dR <> LStatic.
  Hypothesis NEB : md_addr dR <> md_addr dB.
  Hypothesis OPA : opnd_sep dR dA lo (bv_unsigned sp).
  Hypothesis OPB : opnd_sep dR dB lo (bv_unsigned sp).
  Hypothesis CRA : client_range L LB lo (md_addr dA) 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L LB lo (md_p dA) (4 * md_n dA).
  Hypothesis CRB : client_range L LB lo (md_addr dB) 16.
  Hypothesis CRBL : md_own dB = LHeap -> client_range L LB lo (md_p dB) (4 * md_n dB).
  Hypothesis WRR : mpd_writable L LB (bv_unsigned sp) (heap_top usegs L HI h) dR.
  Hypothesis RLO : md_own dR <> LNull -> md_p dR + 4 * md_n dR <= lo \/ bv_unsigned sp <= md_p dR.
  Hypothesis ST0 : stk usegs m lo (bv_unsigned sp).
  Hypothesis SLO : lo <= bv_unsigned sp - 576 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv usegs m.
  Hypothesis SOK0 : statics_ok usegs L m.
  Hypothesis CA : const_at L MSF 8.

  Notation SP := (bv_unsigned sp).
  Notation SPc := (bv_unsigned sp + -64).
  Notation POST := (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (mod_mpi_R LB dR dA dB) lo m mo).

  (* [comment removed for export] *)
  Definition ALIAS : bool := Z.eqb (md_addr dR) (md_addr dA).
  Definition es : list mpd := if ALIAS then [dB] else [dA; dB].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L43782101083.80L54965713378.2 L59314955108.82L65499856427.80L774698616.80  00000;00B00Z00a01>S2sp2dR3SPBS1L3ACPS2sp2dR2dA4HPOS3SPB2AL1ES2sp2dRS1L3HLS2sp2dR2lo3SLO4HPOS3SPB". (* [comment removed for export] *)
  Lemma facts0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "(0.(1.=(2.VdR,))(0.(3.$4.(5.(2.VdR,)+8.)=)(0.(6.(7.(8.(2.VdR,)+10.)Vlo,)(7.(9.&40.Vsp,)(2.VdR,)))(0.P,(3.$:.(;.VdR,)$<.)(0.(=.(>.$4.$4.)(?.$4.$4.(10.VdR,)(11.+4.(12.VdR,)))VLB,)(7.+1.(12.VdR,)))(0.(13.(>.$4.$4.)Lb,(>.$4.$4.)(14.VL,(15.$4.$4.R1.)(16.$4.$4.R1.))VLB,)(0.(1.=(17.VL,))(0.(1.(9.&40.Vsp,)(18.+2.+40.))P,(3.$19.$1:.$1;.)(3.$1<.VdA,VdR,))))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(MR0) 2%nat. intros FLt1 SG. flat constr:(FLt1) 6%nat. flclear FLt1. intros HR HAL HPOS HL HN HO.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros BR _. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(WRR) 3%nat. flclear WRR. intros WW1 WW2 WW3.
    split; [exact HPOS|]. split; [exact HAL|].
    split; [exact (client_wrange_where L _ _ _ _ 16 lo WW1 ltac:(lia) BR DHI ACL ltac:(lia))|].
    split. { intros O. rewrite O in HO. flat constr:(HO) 3%nat. flclear HO. intros N1 IN _. auto. }
    split; [exact BR|]. split; [clear -ACP; lia|]. split; [lia|].
    intros AL. unfold ALIAS in AL. apply Z.eqb_eq in AL. destruct SRA as [E|E]; [symmetry; exact E| exfalso; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma ESF_ok : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "(13.$1<.Le,$1<.(0.(1=.VL,VLB,Vlo,(2.R1.)+10.)(0.P,(3.$:.(;.R1.)$<.)(=.(>.$4.$4.)(?.$4.$4.(10.R2.)(11.+4.(12.R2.)))VLB,)(0.(6.(7.(8.(2.R1.)+10.)Vlo,)(7.(9.&40.Vsp,)(2.R1.)))(0.P,(3.$:.(;.VdR,)$<.)(6.(7.(8.(2.R2.)+10.)(10.VdR,))(7.(8.(10.VdR,)(11.+4.(12.VdR,)))(2.R2.)))(0.(6.(1>.(3.$:.(;.VdR,)$<.))(6.(3.$:.(;.R1.)$1?.)(6.(7.(8.(10.VdR,)(11.+4.(12.VdR,)))(10.R1.))(7.(8.(10.R1.)(11.+4.(12.R1.)))(10.VdR,)))))(0.(6.(7.(8.(2.VdR,)+10.)(2.R1.))(7.(8.(2.R1.)+10.)(2.VdR,)))P,(1>.(3.$:.(;.R1.)$1?.))(6.(7.(8.(2.VdR,)+10.)(10.R2.))(7.(8.(10.R2.)(11.+4.(12.R2.)))(2.VdR,)))))))))$20.)")
(* [comment removed for export] *).
  Proof.
    assert (FB : client_range L LB lo (md_addr dB) 16 /\ (md_own dB = LHeap -> In (md_p dB, 4 * md_n dB) LB)
                 /\ (md_addr dB + 16 <= lo \/ SP <= md_addr dB)
                 /\ (md_own dR = LHeap -> md_addr dB + 16 <= md_p dR \/ md_p dR + 4 * md_n dR <= md_addr dB)
                 /\ (md_own dR <> LHeap \/ md_own dB = LNull \/ md_p dR + 4 * md_n dR <= md_p dB \/ md_p dB + 4 * md_n dB <= md_p dR)
                 /\ (md_addr dR + 16 <= md_addr dB \/ md_addr dB + 16 <= md_addr dR)
                 /\ (md_own dB <> LNull -> md_addr dR + 16 <= md_p dB \/ md_p dB + 4 * md_n dB <= md_addr dR)).
    { flat constr:(OPB) 5%nat. flclear OPB. intros O1 O2 O3 O4 O5. flat constr:(MB0) 2%nat. intros FLt2 _. flat constr:(FLt2) 6%nat. flclear FLt2. intros _ _ _ _ _ HOB.
      split; [exact CRB|]. split; [intros O; rewrite O in HOB; exact (proj1 (proj2 HOB))|]. split; [exact O4|]. split; [exact O2|].
      split. { destruct O3 as [E|X]; [exfalso; apply NEB; rewrite E; reflexivity| exact X]. }
      split. { destruct SRB as [E|X]; [exfalso; apply NEB; rewrite E; reflexivity| exact X]. }
      exact O1. }
    unfold es, ALIAS. destruct (Z.eqb_spec (md_addr dR) (md_addr dA)) as [AL|NAL]; [constructor; [exact FB| constructor]|].
    constructor; [| constructor; [exact FB| constructor]].
    flat constr:(OPA) 5%nat. flclear OPA. intros O1 O2 O3 O4 O5. flat constr:(MA0) 2%nat. intros FLt3 _. flat constr:(FLt3) 6%nat. flclear FLt3. intros _ _ _ _ _ HOA.
    split; [exact CRA|]. split; [intros O; rewrite O in HOA; exact (proj1 (proj2 HOA))|]. split; [exact O4|]. split; [exact O2|].
    split. { destruct O3 as [E|X]; [exfalso; apply NAL; rewrite E; reflexivity| exact X]. }
    split. { destruct SRA as [E|X]; [exfalso; apply NAL; rewrite E; reflexivity| exact X]. }
    exact O1.
  Qed.

  Lemma opndA : In dA es \/ dA = dR.
  Proof.
    unfold es. destruct ALIAS eqn:AL; [right; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0)))))) AL)| left; left; reflexivity].
  Qed.
  Lemma opndB : In dB es.
  Proof. unfold es. destruct ALIAS; [left; reflexivity| right; left; reflexivity]. Qed.

  (* [comment removed for export] *)
  Notation CST := (cstate usegs L HI h LB mo m SP lo SPc dR es).
  Local Ltac mc_inst H :=
    exact (H usegs L HI HLS DIMG HND IMGC SW ROIMG h LB mo m SP lo SPc dR es
             ACL ltac:(lia) ltac:(lia) HTOP (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0)))))) ) DHI NSR WRR
             (proj1 (proj2 (proj2 facts0))) (proj1 (proj2 facts0)) (proj1 (proj2 (proj2 (proj2 facts0)))) ESF_ok).
  Definition mc_init := ltac:(mc_inst @cs_init).
  Definition mc_final := ltac:(mc_inst @cs_final).
  Definition mc_binop_l := ltac:(mc_inst @cs_binop_l).
  Definition mc_binop_w := ltac:(mc_inst @cs_binop_w).
  Definition mc_munch := ltac:(mc_inst @cs_munch).
  Definition mc_hi_write := ltac:(mc_inst @cs_hi_write).
  Definition mc_sign_w := ltac:(mc_inst @cs_sign_w).
  Definition mc_calloc_attach := ltac:(mc_inst @cs_calloc_attach).
  Definition mc_release := ltac:(mc_inst @cs_release).
  Definition mc_heap_nop := ltac:(mc_inst @cs_heap_nop).
  Definition mc_local_facts := ltac:(mc_inst @cs_local_facts).
  Definition mc_w_facts := ltac:(mc_inst @cs_w_facts).
  Definition mc_ext_facts := ltac:(mc_inst @cs_ext_facts).
  Definition mc_opnd_sep_ll := ltac:(mc_inst @cs_opnd_sep_ll).
  Definition mc_opnd_sep_le := ltac:(mc_inst @cs_opnd_sep_le).
  Definition mc_opnd_sep_lw := ltac:(mc_inst @cs_opnd_sep_lw).
  Definition mc_opnd_sep_wl := ltac:(mc_inst @cs_opnd_sep_wl).
  Definition mc_opnd_sep_we := ltac:(mc_inst @cs_opnd_sep_we).
  Definition mc_opnd_sep_ww := ltac:(mc_inst @cs_opnd_sep_ww).
  Definition mc_ivs_local := ltac:(mc_inst @cs_ivs_local).
  Definition mc_ivs_w := ltac:(mc_inst @cs_ivs_w).

  Notation SPF' := (Z_to_bv 64 (bv_unsigned sp + -64)).

  Notation FRM j4 w4 w8 w16 j20 := ([(SPc, [CB 4 j4; C4 w4; C8 w8; C4 w16; CB 4 j20; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])] : list (Z * list cell)).

  Lemma cs_parts : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dW : mpd) (CS : list (Z * list cell)),
    CST mq moq hq LBq [] dW [] CS [] ->
    HEAP usegs L HI hq LBq mq moq /\ heap_top usegs L HI hq = heap_top usegs L HI h /\ mo_frame mo moq /\ statics_ok usegs L mq /\
    mem_inv usegs mq /\ stk usegs mq lo SPc /\ Forall (fun ac : Z * list cell => rw_cells usegs mq (fst ac) (snd ac)) CS /\ MOK moq
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq dW CS CS_.
    flat constr:(CS_) 21%nat. flclear CS_. intros HH HTc MF LOK SA LA MW WOK EXOK SUB COV FRS EXT PX SOK MI ST CH CHS CXH CXS.
    split; [exact HH|]. split; [exact HTc|]. split; [exact MF|]. split; [exact SOK|]. split; [exact MI|]. split; [exact ST|].
    split; [exact CH|]. exact (heap_mok _ _ HI _ _ _ _ HH).
  Qed.

  Lemma ext_facts : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dW : mpd) (CS : list (Z * list cell)) (d : mpd),
    CST mq moq hq LBq [] dW [] CS [] -> In d es ->
    mpd_at usegs mq LBq d /\ client_range L LBq lo (md_addr d) 16 /\ (md_own d = LHeap -> client_range L LBq lo (md_p d) (4 * md_n d)) /\
    (md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ SPc <= md_p d) /\ (md_own d = LHeap -> 0 < md_p d /\ 1 <= md_n d) /\
    (md_addr d + 16 <= lo \/ SP <= md_addr d)
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq dW CS d CS_ IN.
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ _ CS_ IN)) 6%nat. intros ME CRE CREL LE HFE ASE.
    split; [exact ME|]. split; [exact CRE|]. split; [exact CREL|]. split; [exact LE|]. split; [| exact ASE]. intros O. flat constr:((HFE O)) 4%nat. intros P0 _ _ N1. auto.
  Qed.
  Lemma es_at : Forall (fun e => mpd_at usegs m LB e) es.
  Proof. unfold es. destruct ALIAS; [constructor; [exact MB0| constructor]| constructor; [exact MA0| constructor; [exact MB0| constructor]]]. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma L_epi : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dW : mpd) (j4 j20 : list (bv 8)) (w4 w8 w16 : word) (r : Z)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x8 x9 x18 x19 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dW [] (FRM j4 w4 w8 w16 j20) [] ->
    -2^31 < r <= 0 -> (r = 0 -> 0 <= mpd_val dW < mpd_abs dB) ->
    aevtM usegs moq POST (MS (mkR xra SPF' gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x216ec) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ Hr HV.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((mc_final _ _ _ _ _ _ _ _ CS_ ltac:(constructor))) 11%nat. intros HH HT MF MW OUT BK PX SOK MI ST CH.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CHR. cbn [fst snd] in CHR. clear CH.
    zstep. zstep. zstep. zstep. zstep.
    release_frame CHR ST (bv_unsigned sp).
    zstep. zstep.
    apply aevtM_done. unfold mpi_binop_post. do 14 eexists. exists mq, moq, hq, LBq, dW, r.
    split; [rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HT|]. split; [exact HH|]. split; [exact MW|]. split; [exact OUT|].
    split; [exact PX|]. split; [exact SOK|]. split; [split; [exact HV| exact Hr]| exact BK].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma L_loopB : forall (vb : Z) (D : nat) (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dW : mpd) (j4 j20 : list (bv 8)) (w4 w8 w16 : word)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dW [] (FRM j4 w4 w8 w16 j20) [] ->
    mpd_val dB = vb -> 0 < vb -> vb = mpd_abs dB -> 0 <= mpd_val dW < Z.of_nat D * vb ->
    aevtM usegs moq POST (MS (mkR xra SPF' gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (md_addr dR)) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x216d0) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros vb D. induction D as [|D IH]; intros until t6; intros CS_ VBE VB0 VBA VR; [exfalso; clear - VR; lia|].
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_parts _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW NSW EA WR LW CRW CRWL HFW ASW WA8.
    flat constr:((ext_facts _ _ _ _ _ _ dB CS_ opndB)) 6%nat. intros MB CRB_ CRBL_ LOB HFB ASB.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof HCMP as SPC. unfold mpi_cmp_mpi_stmt, U_MPI_CMP_MPI in SPC.
    eapply aevtM_cut_evt; [exact MK| eapply SPC with (dX := dW) (dY := dB) (LB := LBq); try eassumption; try reflexivity|].
    all: try (rewrite ?EA; reflexivity).
    1:{ intros O. flat constr:((HFW O)) 2%nat. intros P0 _. exact P0. }
    1:{ intros O. flat constr:((HFB O)) 2%nat. intros P0 _. exact P0. }
    clear SPC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO. destruct_exs PO.
    flat constr:(PO) 4%nat. flclear PO. intros -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x216dc)) with (Z_to_bv 64 0x216dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (Z.sgn_spec (mpd_val dW - mpd_val dB)) as SG.
    zstep; if_cases K0; zify_cond K0; rewrite ?signed_lit_small in K0 by (clear - SG; lia).
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      flat constr:((mc_opnd_sep_we _ _ _ _ _ _ _ _ _ dB CS_ opndB)) 2%nat. intros SEPWB OPSWB.
      flat constr:((mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros SEPWW OPSWW.
      pose proof (HAS (-1) (or_intror eq_refl)) as SPA_.
      eapply aevtM_cut.
      { eapply SPA_ with (dX := dW) (dA := dW) (dB := dB) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
        all: try (rewrite ?EA; reflexivity). }
      clear SPA_. cbv beta. intros ms2 mo' PO. unfold mpi_binop_post in PO.
      flat constr:(PO) 31%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR.
      injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
      replace (ret_pc (Z_to_bv 64 0x216cc)) with (Z_to_bv 64 0x216cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      flat constr:(RR) 2%nat. flclear RR. intros R1 FLt4. flat constr:(FLt4) 4%nat. flclear FLt4. intros KA KP KF KN.
      assert (CS2 : CST m2 mo2 h2 LB2 [] dW2 [] (FRM j4 w4 w8 w16 j20) []).
      { eapply mc_binop_w; [exact CS_| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact KF| exact KP| exact KN]. }
      assert (Hr : (r = 0 /\ mpd_val dW2 = mpd_val dW - mpd_val dB) \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED).
      { destruct R1 as [[Hr0 HV]|HrF]; [left; split; [exact Hr0| rewrite HV; clear; lia]| right; exact HrF]. }
      clear MW NSW WR LW CRW CRWL HFW MB CRB_ CRBL_ LOB HFB SEPWB OPSWB SEPWW OPSWW R1 KF KP MA2 OUT2 PX2 CS_ HH HTc MF SOK MI ST CH MK.
      flat constr:((cs_parts _ _ _ _ _ _ CS2)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
      zstep; if_cases K1; zify_cond K1.
      + eapply L_epi; [exact CS2| destruct Hr as [[Hr _]|Hr]; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia|].
        intros ->. exfalso. destruct Hr as [[_ _]|Hr]; [apply K1; reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia].
      + destruct Hr as [[_ HV]|Hr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K1; clear - K1; lia].
        eapply IH; [exact CS2| exact VBE| exact VB0| exact VBA| clear - HV VR K0 SG VBE VB0; nia].
    - (* [comment removed for export] *)
      zstep. zstep. eapply L_epi; [exact CS_| clear; lia|]. intros _. clear - K0 SG VR VBE VBA. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma L_loopA_step : forall (vb : Z) (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dW : mpd) (j4 j20 : list (bv 8)) (w4 w8 w16 : word)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dW [] (FRM j4 w4 w8 w16 j20) [] ->
    mpd_val dB = vb -> 0 < vb -> vb = mpd_abs dB ->
    (forall (m2 : mem) (mo2 : Model) (h2 : HST usegs L HI) (LB2 : list blk) (dW2 : mpd) (v4 v8 v16 : word)
        (yra y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
       CST m2 mo2 h2 LB2 [] dW2 [] (FRM j4 v4 v8 v16 j20) [] -> mpd_val dW < 0 -> mpd_val dW2 = mpd_val dW + vb ->
       aevtM usegs mo2 POST (MS (mkR yra SPF' gp tp y0 y1 y2 (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (md_addr dR)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 65537) (Z_to_bv 64 (SP + -60)) s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6) F (Z_to_bv 64 0x21680) fc None m2 (seg_rom usegs))) ->
    aevtM usegs moq POST (MS (mkR xra SPF' gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (md_addr dR)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 65537) (Z_to_bv 64 (SP + -60)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x21680) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6; intros CS_ VBE VB0 VBA K.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_parts _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    pose proof (Forall_inv CH) as FR. cbn [fst snd] in FR. clear CH HH HTc MF SOK.
    pose proof (munch_refl [(SP + -64, SP)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    set (mQ := mq) in CS_.
    zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    unfold mQ in CS_.
    assert (CS1 : CST m1 moq hq LBq [] dW [] (FRM j4 (Z_to_bv 64 0) (Z_to_bv 64 (SP + -60)) (Z_to_bv 64 65537) j20) []).
    { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (SP + -64) SP []); [exact CS_| exact MU| exact WM| exact MI| exact ST| lia| lia| constructor| reflexivity| | |].
      - intros j d d' Hj. destruct j; discriminate Hj.
      - constructor; [exact FR| constructor].
      - constructor; [| constructor]. cbn [fst snd cells_size csize Nat.add]. split; [clear; lia|]. split; [clear; lia| intros d []]. }
    clear FR MU WM MI ST MK CS_.
    flat constr:((cs_parts _ _ _ _ _ _ CS1)) 8%nat. intros HH HTc MF SOK MI ST CH MK1.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS1)) 10%nat. intros MW NSW EA WR LW CRW CRWL HFW ASW WA8.
    pose proof (proj2 MW) as SGW.
    pose proof (Forall_inv CH) as FR1. cbn [fst snd] in FR1. clear CH.
    zstep. zstep. zstep.
    pose proof U_mpi_cmp_mpi_spec_o as SPC. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in SPC.
    eapply aevtM_cut_evt; [exact MK1| eapply SPC with (LB := LBq) (dX := dW) (dY := mkMPD (SP + -56) 1 1 (SP + -60) [Z_to_bv 64 0] (le_bytes_to_word j20) LStatic);
      [ apply opnd_at_mpd; exact MW
      | right; rewrite unsigned_lit by lia; eapply T_opnd; [exact FR1| lia ..]
      | intros O; exact (proj1 (HFW O))
      | cbn; intros O; discriminate O
      | exact MI
      | rewrite EA; reflexivity
      | reflexivity ]|].
    clear SPC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO. destruct_exs PO.
    flat constr:(PO) 4%nat. flclear PO. intros -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x21698)) with (Z_to_bv 64 0x21698) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite mpd_val_T0, Z.sub_0_r.
    pose proof (Z.sgn_spec (mpd_val dW)) as SG.
    zstep; if_cases K0; zify_cond K0; rewrite ?signed_lit_small in K0 by (clear - SG; lia).
    - pose proof (mpd_val_abs dW SGW) as WA.
      eapply (L_loopB vb (Z.to_nat (mpd_abs dW + 1))); [exact CS1| exact VBE| exact VB0| exact VBA|].
      rewrite Z2Nat.id by (pose proof (mpd_abs_nonneg dW) as AN; clear - AN; lia). clear - WA K0 SG VB0. nia.
    - assert (NEG : mpd_val dW < 0) by (clear - K0 SG; lia).
      zstep. zstep. zstep. zstep. zstep.
      flat constr:((ext_facts _ _ _ _ _ _ dB CS1 opndB)) 6%nat. intros MB CRB_ CRBL_ LOB HFB ASB.
      flat constr:((mc_opnd_sep_we _ _ _ _ _ _ _ _ _ dB CS1 opndB)) 2%nat. intros SEPWB OPSWB.
      flat constr:((mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS1)) 2%nat. intros SEPWW OPSWW.
      pose proof (HAS 1 (or_introl eq_refl)) as SPA_.
      eapply aevtM_cut.
      { eapply SPA_ with (dX := dW) (dA := dW) (dB := dB) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
        all: try (rewrite ?EA; reflexivity). }
      clear SPA_. cbv beta. intros ms2 mo' PO. unfold mpi_binop_post in PO.
      flat constr:(PO) 31%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 LB2 dW2 r2 E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR.
      injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
      replace (ret_pc (Z_to_bv 64 0x216b0)) with (Z_to_bv 64 0x216b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      flat constr:(RR) 2%nat. flclear RR. intros R1 FLt7. flat constr:(FLt7) 4%nat. flclear FLt7. intros KA KP KF KN.
      assert (CS2 : CST m2 mo2 h2 LB2 [] dW2 [] (FRM j4 (Z_to_bv 64 0) (Z_to_bv 64 (SP + -60)) (Z_to_bv 64 65537) j20) []).
      { eapply mc_binop_w; [exact CS1| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact KF| exact KP| exact KN]. }
      assert (Hr2 : (r2 = 0 /\ mpd_val dW2 = mpd_val dW + mpd_val dB) \/ r2 = MBEDTLS_ERR_MPI_ALLOC_FAILED).
      { destruct R1 as [[Hr0 HV]|HrF]; [left; split; [exact Hr0| rewrite HV; clear; lia]| right; exact HrF]. }
      clear MW MB CRB_ CRBL_ LOB HFB SEPWB OPSWB SEPWW OPSWW R1 KF KP MA2 OUT2 PX2 HH HTc MF SOK MI ST MK1 FR1.
      flat constr:((cs_parts _ _ _ _ _ _ CS2)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
      zstep; if_cases K3; zify_cond K3.
      + destruct Hr2 as [[-> HV]|Hx]; [| exfalso; subst r2; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K3; clear - K3; lia].
        eapply K; [exact CS2| exact NEG| rewrite HV, VBE; reflexivity].
      + zstep. eapply L_epi; [exact CS2| destruct Hr2 as [[Hx _]|Hx]; subst r2; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia|].
        intros ->. exfalso. destruct Hr2 as [[_ _]|Hx]; [apply K3; reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hx; clear - Hx; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma L_loopA : forall (vb : Z) (D : nat) (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dW : mpd) (j4 j20 : list (bv 8)) (w4 w8 w16 : word)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dW [] (FRM j4 w4 w8 w16 j20) [] ->
    mpd_val dB = vb -> 0 < vb -> vb = mpd_abs dB -> - mpd_val dW < Z.of_nat D * vb ->
    aevtM usegs moq POST (MS (mkR xra SPF' gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (md_addr dR)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 65537) (Z_to_bv 64 (SP + -60)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x21680) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros vb D. induction D as [|D IH]; intros until t6; intros CS_ VBE VB0 VBA VR.
    - eapply L_loopA_step; [exact CS_| exact VBE| exact VB0| exact VBA|]. intros. exfalso. clear - VR H0. lia.
    - eapply L_loopA_step; [exact CS_| exact VBE| exact VB0| exact VBA|]. intros until y6. intros CS2 NEG HV.
      eapply IH; [exact CS2| exact VBE| exact VB0| exact VBA| rewrite HV; clear - VR NEG VB0; nia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma opnd_facts0 : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (CS : list (Z * list cell)) (d : mpd),
    CST mq moq hq LBq [] dR [] CS [] -> In d es \/ d = dR ->
    mpd_at usegs mq LBq d /\ client_range L LBq lo (md_addr d) 16 /\ (md_own d = LHeap -> client_range L LBq lo (md_p d) (4 * md_n d)) /\
    (md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ SPc <= md_p d) /\ (md_own d = LHeap -> 0 < md_p d /\ 1 <= md_n d) /\
    (md_addr d + 16 <= lo \/ SP <= md_addr d)
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq CS d CS_ [IN|E]; [exact (ext_facts _ _ _ _ _ _ d CS_ IN)|].
    rewrite E. flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW _ _ _ LW CRW CRWL HFW ASW _.
    split; [exact MW|]. split; [exact CRW|]. split; [exact CRWL|]. split; [exact LW|]. split; [| exact ASW]. intros O. flat constr:((HFW O)) 4%nat. intros P0 _ _ N1. auto.
  Qed.
  Lemma opnd_sep_w0 : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (CS : list (Z * list cell)) (d : mpd),
    CST mq moq hq LBq [] dR [] CS [] -> In d es \/ d = dR -> mpd_sep dR d /\ opnd_sep dR d lo SPc
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq CS d CS_ [IN|E]; [exact (mc_opnd_sep_we _ _ _ _ _ _ _ _ _ d CS_ IN)|].
    rewrite E. exact (mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS_).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma L_call : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (j4 j20 : list (bv 8)) (w4 w8 w16 : word)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dR [] (FRM j4 w4 w8 w16 j20) [] ->
    mpd_abs dB = 0 \/ md_sg dB = 1 ->
    aevtM usegs moq POST (MS (mkR xra SPF' gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (md_addr dR)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (md_addr dA)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2165c) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ SGN.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_parts _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW NSW EA WR LW CRW CRWL HFW ASW WA8.
    flat constr:((opnd_facts0 _ _ _ _ _ dA CS_ opndA)) 6%nat. intros MA CRA_ CRAL_ LOA HFA ASA.
    flat constr:((opnd_facts0 _ _ _ _ _ dB CS_ (or_introl opndB))) 6%nat. intros MB CRB_ CRBL_ LOB HFB ASB.
    flat constr:((opnd_sep_w0 _ _ _ _ _ dA CS_ opndA)) 2%nat. intros SEPWA OPSWA.
    flat constr:((opnd_sep_w0 _ _ _ _ _ dB CS_ (or_introl opndB))) 2%nat. intros SEPWB OPSWB.
    zstep. zstep. zstep. zstep. zstep.
    pose proof HDIV as SPD. unfold mpi_div_mpi_stmt, U_MPI_DIV_MPI in SPD.
    eapply aevtM_cut.
    { eapply SPD with (dX := dR) (dA := dA) (dB := dB) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia). }
    clear SPD. cbv beta. intros ms2 mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 31%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR.
    injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
    replace (ret_pc (Z_to_bv 64 0x21670)) with (Z_to_bv 64 0x21670) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 2%nat. flclear RR. intros (Hr & HBP) FLt8. flat constr:(FLt8) 4%nat. flclear FLt8. intros KA KP KF KN.
    assert (CS2 : CST m2 mo2 h2 LB2 [] dW2 [] (FRM j4 w4 w8 w16 j20) []).
    { eapply mc_binop_w; [exact CS_| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact KF| exact KP| exact KN]. }
    pose proof (proj2 MA2) as SGW2.
    clear MW NSW WR LW CRW CRWL HFW MA CRA_ CRAL_ LOA HFA ASA MB CRB_ CRBL_ LOB HFB ASB SEPWA OPSWA SEPWB OPSWB KF KP MA2 OUT2 PX2 CS_ HH HTc MF SOK MI ST CH MK.
    flat constr:((cs_parts _ _ _ _ _ _ CS2)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    zstep; if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      eapply L_epi; [exact CS2| exact Hr|]. intros ->. exfalso. apply K0. reflexivity.
    - assert (r = 0) as -> by (clear - K0 Hr; lia). specialize (HBP eq_refl).
      assert (SG1 : md_sg dB = 1) by (destruct SGN as [Z0|S1]; [exfalso; clear - Z0 HBP; lia| exact S1]).
      assert (VBE : mpd_val dB = mpd_abs dB) by (unfold mpd_val, mpd_abs; rewrite SG1; clear; lia).
      zstep. zstep. zstep.
      pose proof (mpd_val_abs dW2 SGW2) as WA.
      eapply (L_loopA (mpd_abs dB) (Z.to_nat (mpd_abs dW2 + 1))); [exact CS2| exact VBE| exact HBP| reflexivity|].
      rewrite Z2Nat.id by (clear - WA; lia). clear - WA HBP. nia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma L_mod : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)(3:.$25.Vmo,(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.Vra,Vsp,Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(3?.&40.(2.VdR,))(3?.&40.(2.VdA,))(3?.&40.(2.VdB,))R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(3?.&40.+21610.)Vfc,(40.(21.&40.))Vm,(41.$25.)))")
(* [comment removed for export] *).
  Proof.
    intros.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK.
    pose proof ST0 as ST. pose proof MI0 as MI. pose proof es_at as ESA.
    carve_frame 64%nat ST.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    set (mI := m) in HH0, MR0, MA0, MB0, MI0, SOK0, ST0, ESA.
    do 18 zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 4 ?ja :: _ :: _ :: _ :: CB 4 ?jb :: _) => set (j4 := ja) in FR; set (j20 := jb) in FR end.
    assert (MU1 : munch [(lo, SP)] m m1).
    { eapply munch_weaken; [| exact MU]. intros x Hx. cbn in Hx |- *. clear - Hx SLO HLS. lia. }
    pose proof HH0 as HH0'. pose proof SOK0 as SOK0'. pose proof MI0 as MI0'. pose proof MR0 as MR0'. unfold mI in HH0', SOK0', MI0', MR0', ESA.
    assert (CS1 : CST m1 mo h LB [] dR [] (FRM j4 (Z_to_bv 64 0) (Z_to_bv 64 (SP + -60)) (Z_to_bv 64 65537) j20) []).
    { eapply mc_init; [exact HH0'| exact SOK0'| exact MI0'| exact MR0'| exact ESA| exact MU1| exact WM| exact MI| exact ST| constructor| | |].
      - intros i j di dj Hi. destruct i; discriminate Hi.
      - constructor; [exact FR| constructor].
      - constructor; [| constructor]. cbn [fst snd cells_size csize Nat.add]. split; [clear; lia|]. split; [clear; lia| intros d []]. }
    clear FR MU WM MU1 HH0' SOK0' MI0' MR0' ESA.
    flat constr:((cs_parts _ _ _ _ _ _ CS1)) 8%nat. intros HH1 HT1 MF1 SOK1 MI1 ST1 CH1 MK1.
    flat constr:((opnd_facts0 _ _ _ _ _ dB CS1 (or_introl opndB))) 6%nat. intros MB _ _ _ HFB _.
    pose proof (proj2 MB) as SGB.
    pose proof (Forall_inv CH1) as FR1. cbn [fst snd] in FR1. clear CH1.
    pose proof U_mpi_cmp_mpi_spec_o as SPC. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in SPC.
    eapply aevtM_cut_evt; [exact MK1| eapply SPC with (LB := LB) (dX := dB) (dY := mkMPD (SP + -56) 1 1 (SP + -60) [Z_to_bv 64 0] (le_bytes_to_word j20) LStatic);
      [ apply opnd_at_mpd; exact MB
      | right; rewrite unsigned_lit by lia; eapply T_opnd; [exact FR1| lia ..]
      | intros O; exact (proj1 (HFB O))
      | cbn; intros O; discriminate O
      | exact MI1
      | reflexivity
      | reflexivity ]|].
    clear SPC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO. destruct_exs PO.
    flat constr:(PO) 4%nat. flclear PO. intros -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x21658)) with (Z_to_bv 64 0x21658) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite mpd_val_T0, Z.sub_0_r.
    pose proof (Z.sgn_spec (mpd_val dB)) as SG.
    zstep; if_cases K0; zify_cond K0; rewrite ?signed_lit_small in K0 by (clear - SG; lia).
    - zstep. eapply L_epi; [exact CS1| clear; lia| intros E; exfalso; clear - E; lia].
    - eapply L_call; [exact CS1|]. assert (V0 : 0 <= mpd_val dB) by (clear - K0 SG; lia).
      destruct SGB as [S|S]; [right; exact S| left]. pose proof (mpd_abs_nonneg dB) as A0.
      unfold mpd_val in V0. unfold mpd_abs in A0 |- *. rewrite S in V0. clear - V0 A0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Walk.

  Theorem U_mpi_mod_mpi_ok : mpi_mod_mpi_stmt usegs L HI U_MPI_MOD_MPI' MSF.
  Proof using DIMG HAS HCMP HDIV HLS HND IMGC ROIMG SW.
    unfold mpi_mod_mpi_stmt, mpi_binop_stmt_nb, U_MPI_MOD_MPI'. intros until lo.
    intros HH MX MA MB SXA SXB SAB NSX NEB OPA OPB CRA CRAL CRB CRBL WRX XLO ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    eapply L_mod; eassumption.
  Qed.
End ModP.

